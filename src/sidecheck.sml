(* Copyright (c) 2011, Adam Chlipala
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

structure SideCheck :> SIDE_CHECK = struct

open Mono

structure E = ErrorMsg

structure SK = struct
type ord_key = string
val compare = String.compare
end

structure SS = BinarySetFn(SK)
structure IS = IntBinarySet

val envVars = ref SS.empty

fun check ds =
    let
        val alreadyWarned = ref false
        val currentDecl = ref "?"

        fun reportClientOnly loc (k1, k2) =
            let val k2' = case k1 of
                              "Basis" => (case k2 of "get_client_source" => "get" | _ => k2)
                            | _ => k2
            in
                E.errorAt loc ("Server-side code uses client-side-only identifier \"" ^ k1 ^ "." ^ k2' ^ "\"")
            end

        (* Walk expression, stopping at EJavaScript boundaries.
           Code inside EJavaScript is client-side and may use client-only FFI. *)
        fun checkExp (e : exp) =
            let val (e', loc) = e in
                case e' of
                    EJavaScript _ => ()
                  | EFfi k =>
                    (if Settings.isClientOnly k then reportClientOnly loc k else ())
                  | EFfiApp (k1, k2, args) =>
                    ((if k1 = "Basis" andalso k2 = "getenv" then
                          (case args of
                               [(e2, _)] =>
                               (case e2 of
                                    (EPrim (Prim.String (_, s)), _) =>
                                    envVars := SS.add (!envVars, s)
                                  | _ => if !alreadyWarned then ()
                                         else (alreadyWarned := true;
                                               TextIO.output (TextIO.stdErr, "WARNING: " ^ ErrorMsg.spanToString loc ^ ": reading from an environment variable not determined at compile time, which can confuse CSRF protection")))
                             | _ => ())
                      else if Settings.isClientOnly (k1, k2) then
                          reportClientOnly loc (k1, k2)
                      else ());
                     List.app (checkExp o #1) args)
                  | EPrim _ => ()
                  | ERel _ => ()
                  | ENamed _ => ()
                  | ECon (_, _, eo) => Option.app checkExp eo
                  | ENone _ => ()
                  | ESome (_, e1) => checkExp e1
                  | EApp (e1, e2) => (checkExp e1; checkExp e2)
                  | EAbs (_, _, _, e1) => checkExp e1
                  | EUnop (_, e1) => checkExp e1
                  | EBinop (_, _, e1, e2) => (checkExp e1; checkExp e2)
                  | ERecord xets => List.app (checkExp o #2) xets
                  | EField (e1, _) => checkExp e1
                  | ECase (e1, pes, _) => (checkExp e1; List.app (checkExp o #2) pes)
                  | EStrcat (e1, e2) => (checkExp e1; checkExp e2)
                  | EError (e1, _) => checkExp e1
                  | EReturnBlob {blob, mimeType, ...} =>
                    (Option.app checkExp blob; checkExp mimeType)
                  | ERedirect (e1, _) => checkExp e1
                  | EWrite e1 => checkExp e1
                  | ESeq (e1, e2) => (checkExp e1; checkExp e2)
                  | ELet (_, _, e1, e2) => (checkExp e1; checkExp e2)
                  | EClosure (_, es) => List.app checkExp es
                  | EQuery {query, body, initial, ...} =>
                    (checkExp query; checkExp body; checkExp initial)
                  | EDml (e1, _) => checkExp e1
                  | ENextval e1 => checkExp e1
                  | ESetval (e1, e2) => (checkExp e1; checkExp e2)
                  | EUnurlify (e1, _, _) => checkExp e1
                  | ESignalReturn e1 => checkExp e1
                  | ESignalBind (e1, e2) => (checkExp e1; checkExp e2)
                  | ESignalSource e1 => checkExp e1
                  | EServerCall (e1, _, _, _) => checkExp e1
                  | ERecv (e1, _) => checkExp e1
                  | ESleep e1 => checkExp e1
                  | ESpawn e1 => checkExp e1
            end

        val (decls, ps) = ds

        (* Build a set of declaration IDs marked as having client-side execution
           by scriptcheck (ServerAndPull or ServerAndPullAndPush). *)
        val clientIds = foldl (fn ((n, side, _), acc) =>
                                   case side of
                                       ServerOnly => acc
                                     | _ => IS.add (acc, n))
                               IS.empty ps

        fun checkDecl (d : decl) =
            case d of
                (DVal (_, n, _, e, _), _) =>
                if IS.member (clientIds, n) then ()
                else checkExp e
              | (DValRec vis, _) =>
                (* Skip the entire group if any member is client-side.
                   The fuse pass creates new variants (with fresh IDs) alongside
                   the original client-side declarations in the same DValRec.
                   These variants contain the same raw client code and are also
                   client-side, but their fresh IDs are not in clientIds. *)
                if List.exists (fn (_, n, _, _, _) => IS.member (clientIds, n)) vis then ()
                else List.app (fn (x, n, _, e, _) =>
                                   (currentDecl := x ^ "/" ^ Int.toString n;
                                    checkExp e)) vis
              | _ => ()
    in
        envVars := SS.empty;
        List.app checkDecl decls;
        ds
    end

fun readEnvVars () = SS.listItems (!envVars)

end
