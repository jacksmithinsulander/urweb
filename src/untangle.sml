(* Copyright (c) 2008, Adam Chlipala
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

structure Untangle :> UNTANGLE = struct

open Mono

structure U = MonoUtil
structure E = MonoEnv

structure IS = IntBinarySet
structure IM = IntBinaryMap

fun typ (k, s) = s

fun exp (e, s) =
    case e of
        ENamed n => IS.add (s, n)

      | _ => s

fun untangle (file : file) =
    let
        fun decl (dAll as (d, loc)) =
            case d of
                DValRec vis =>
                let
                    val thisGroup = foldl (fn ((_, n, _, _, _), thisGroup) =>
                                              IS.add (thisGroup, n)) IS.empty vis

                    val used = foldl (fn ((_, n, _, e, _), used) =>
                                       let
                                           val usedHere = U.Exp.fold {typ = typ,
                                                                      exp = exp} IS.empty e
                                       in
                                           IM.insert (used, n, IS.intersection (usedHere, thisGroup))
                                       end)
                               IM.empty vis

                    (* Tarjan's SCC: same fix as Core untangle to avoid infinite iterate and correct order. *)
                    val allRefsLocal = IM.foldli (fn (_, usedHere, acc) =>
                        acc andalso IS.isEmpty (IS.difference (usedHere, thisGroup))) true used

                    val sccs = if not allRefsLocal then [thisGroup] else
                    let
                    val indexCounter = ref 0
                    val index = ref IM.empty
                    val lowlink = ref IM.empty
                    val onStack = ref IS.empty
                    val stack = ref []
                    val sccsAcc = ref []

                    fun getIndex n = Option.getOpt (IM.find (!index, n), ~1)
                    fun setIndex n i = index := IM.insert (!index, n, i)
                    fun getLowlink n = Option.getOpt (IM.find (!lowlink, n), ~1)
                    fun setLowlink n i = lowlink := IM.insert (!lowlink, n, i)

                    fun strongConnect n =
                        let
                            val i = !indexCounter
                            val () = indexCounter := i + 1
                            val () = setIndex n i
                            val () = setLowlink n i
                            val () = onStack := IS.add (!onStack, n)
                            val () = stack := n :: (!stack)
                            val succs = Option.getOpt (IM.find (used, n), IS.empty)
                            val () = IS.app (fn w =>
                                if getIndex w = ~1 then
                                    (strongConnect w;
                                     setLowlink n (Int.min (getLowlink n, getLowlink w)))
                                else if IS.member (!onStack, w) then
                                    setLowlink n (Int.min (getLowlink n, getIndex w))
                                else ()) succs
                        in
                            if getLowlink n = getIndex n then
                                let
                                    fun popToScc acc =
                                        case !stack of
                                            [] => (sccsAcc := acc :: (!sccsAcc); ())
                                          | w :: rest =>
                                                let val () = stack := rest
                                                    val () = onStack := IS.delete (!onStack, w)
                                                    val acc = IS.add (acc, w)
                                                in if w = n then (sccsAcc := acc :: (!sccsAcc); ()) else popToScc acc end
                                in popToScc IS.empty end
                            else ()
                        end

                    val () = IS.app (fn n => if getIndex n = ~1 then strongConnect n else ()) thisGroup
                    val sccs = List.rev (!sccsAcc)
                    val _ = let val union = List.foldl (fn (scc, acc) => IS.union (acc, scc)) IS.empty sccs
                            in if not (IS.equal (union, thisGroup)) then
                                  raise Fail "Untangle: SCC union != thisGroup"
                               else () end
                    in sccs end
                    (*val () = app (fn nodes => (print "SCC':";
                                               IS.app (fn i => (print " ";
                                                                print (Int.toString i))) nodes;
                                               print "\n")) sccs*)

                    fun isNonrec nodes =
                        case IS.find (fn _ => true) nodes of
                            NONE => NONE
                          | SOME node =>
                            let
                                val nodes = IS.delete (nodes, node)
                                val usedHere = Option.getOpt (IM.find (used, node), IS.empty)
                            in
                                if IS.isEmpty nodes then
                                    if IS.member (usedHere, node) then
                                        NONE
                                    else
                                        SOME node
                                else
                                    NONE
                            end

                    val ds = map (fn nodes =>
                                     case isNonrec nodes of
                                         SOME node =>
                                         let
                                             val vi = valOf (List.find (fn (_, n, _, _, _) => n = node) vis)
                                         in
                                             (DVal vi, loc)
                                         end
                                       | NONE =>
                                         (DValRec (List.filter (fn (_, n, _, _, _) => IS.member (nodes, n)) vis), loc))
                                 sccs
                in
                    ds
                end
              | _ => [dAll]
    in
        (ListUtil.mapConcat decl (#1 file), #2 file)
    end

end
