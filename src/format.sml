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

structure Format :> FORMAT = struct

type comment = int * int * string

(* Extract nested (* ... *) comments. Returns (start, endExcl, text) for each. *)
fun extractComments s =
  let
    val n = size s
    fun scan i level start acc =
      if i >= n then
        if level > 0 then raise Fail "Unterminated comment" else List.rev acc
      else if i + 2 <= n then
        case (level, String.substring (s, i, 2)) of
          (0, "(*") => scan (i + 2) 1 i acc
        | (l, "(*") => scan (i + 2) (l + 1) start acc
        | (1, "*)") =>
            let
              val text = String.substring (s, start, i - start + 2)
            in
              scan (i + 2) 0 0 ((start, i + 2, text) :: acc)
            end
        | (l, "*)") => scan (i + 2) (l - 1) start acc
        | (l, _) => scan (i + 1) l start acc
      else
        scan (i + 1) level start acc
  in
    scan 0 0 0 []
  end

fun replaceCommentsWithSpaces s comments =
  CharVector.tabulate (size s, fn i =>
    if List.exists (fn (lo, hi, _) => i >= lo andalso i < hi) comments
    then #" "
    else String.sub (s, i))

(* Convert char offset to (line, char) for ordering *)
fun charOffsetToPos s offset =
  let
    val n = size s
    fun scan i line col =
      if i >= offset orelse i >= n then (line, col)
      else if String.sub (s, i) = #"\n" then scan (i + 1) (line + 1) 0
      else scan (i + 1) line (col + 1)
  in
    scan 0 1 0
  end

fun posLt (l1, c1) (l2, c2) = l1 < l2 orelse (l1 = l2 andalso c1 < c2)

structure C = Compiler
structure P = Print
structure SP = SourcePrint

fun readAll path =
  let
    val inf = FileIO.txtOpenIn path
    val content = TextIO.inputAll inf
    val () = TextIO.closeIn inf
  in
    content
  end

(* Parse from a string (written to temp file). filename is for error reporting. *)
fun parseUrFromString filename content =
  let
    val tmp = OS.FileSys.tmpName ()
    val outf = TextIO.openOut tmp
    val () = TextIO.output (outf, content)
    val () = TextIO.closeOut outf
    val result = C.run (C.transform C.parseUr "parseUr") tmp
    val () = OS.FileSys.remove tmp handle OS.SysErr _ => ()
  in
    result
  end

fun parseUrWithComments filename =
  let
    val content = readAll filename
    val comments = extractComments content
    val replaced = replaceCommentsWithSpaces content comments
  in
    case parseUrFromString filename replaced of
      NONE => NONE
    | SOME absyn =>
        case absyn of
          [(Source.DSgn ("?", _), _)] => NONE
        | decls => SOME (decls, comments)
  end
  handle LrParser.ParseError => NONE

(* For .urs: wrap with "sig\n", extract comments from wrapped, replace, parse *)
fun parseUrsWithComments filename =
  let
    val content = readAll filename
    val wrapped = "sig\n" ^ content
    val comments = extractComments wrapped
    val replaced = replaceCommentsWithSpaces wrapped comments
  in
    case C.parseUrsFromContent (filename, replaced) of
      NONE => NONE
    | SOME sgis => SOME (sgis, comments)
  end

(* Interleave decls with comments by source position *)
fun p_file_with_comments_simple decls comments s =
  let
    open Print.PD
    open Print

    fun spanToOrder span = (#line (#first span), #char (#first span))
    fun spanEndOrder span = (#line (#last span), #char (#last span))

    fun getSpan (d : Source.decl) = #2 d

    val sortedComments = ListMergeSort.sort
      (fn ((a, _, _), (b, _, _)) => posLt (charOffsetToPos s a) (charOffsetToPos s b))
      comments

    fun interleave prevEndOrder acc decls' =
      case decls' of
        [] =>
          let
            val trailing = List.filter (fn (lo, _, _) =>
              posLt prevEndOrder (charOffsetToPos s lo)) sortedComments
          in
            acc @ List.map (fn (_, _, t) => box [string t, newline]) trailing
          end
      | d :: rest =>
          let
            val span = getSpan d
            val currStart = spanToOrder span
            val currEnd = spanEndOrder span
            val between = List.filter (fn (lo, _, _) =>
              let val cpos = charOffsetToPos s lo in
                posLt prevEndOrder cpos andalso posLt cpos currStart
              end) sortedComments
            val commentParts = List.map (fn (_, _, t) => box [string t, newline]) between
            val declPart = SP.p_decl d
            val newAcc = acc @ commentParts @ [declPart]
          in
            interleave currEnd newAcc rest
          end

  in
    case decls of
      [] => vbox (List.map (fn (_, _, t) => box [string t, newline]) sortedComments)
    | d :: rest =>
        let
          val span = getSpan d
          val firstStart = spanToOrder span
          val leading = List.filter (fn (lo, _, _) =>
            posLt (charOffsetToPos s lo) firstStart) sortedComments
          val firstEnd = spanEndOrder span
          val leadingParts = List.map (fn (_, _, t) => box [string t, newline]) leading
          val mainParts = interleave firstEnd [SP.p_decl d] rest
        in
          vbox (ListUtil.join [newline] (leadingParts @ mainParts))
        end
  end

fun p_sgn_items_with_comments sgn_items comments s =
  let
    open Print.PD
    open Print

    fun getSpan (si : Source.sgn_item) = #2 si
    val itemsWithSpans = List.map (fn si => (si, getSpan si)) sgn_items

    (* For .urs, only comments with start >= 4 (past "sig\n") *)
    val relevantComments = List.filter (fn (lo, _, _) => lo >= 4) comments

    val sortedComments = ListMergeSort.sort
      (fn ((a, _, _), (b, _, _)) => posLt (charOffsetToPos s a) (charOffsetToPos s b))
      relevantComments

    fun spanToOrder span = (#line (#first span), #char (#first span))
    fun spanEndOrder span = (#line (#last span), #char (#last span))

    fun interleave prevEndOrder acc items =
      case items of
        [] =>
          let
            val trailing = List.filter (fn (lo, _, _) =>
              posLt prevEndOrder (charOffsetToPos s lo)) sortedComments
          in
            acc @ List.map (fn (_, _, t) => box [string t, newline]) trailing
          end
      | (si, span) :: rest =>
          let
            val currStart = spanToOrder span
            val currEnd = spanEndOrder span
            val between = List.filter (fn (lo, _, _) =>
              let val cpos = charOffsetToPos s lo in
                posLt prevEndOrder cpos andalso posLt cpos currStart
              end) sortedComments
            val commentParts = List.map (fn (_, _, t) => box [string t, newline]) between
            val itemPart = SP.p_sgn_item si
            val newAcc = acc @ commentParts @ [itemPart]
          in
            interleave currEnd newAcc rest
          end

  in
    case itemsWithSpans of
      [] => vbox (List.map (fn (_, _, t) => box [string t, newline]) sortedComments)
    | (si, span) :: rest =>
        let
          val firstStart = spanToOrder span
          val leading = List.filter (fn (lo, _, _) =>
            posLt (charOffsetToPos s lo) firstStart) sortedComments
          val firstEnd = spanEndOrder span
          val leadingParts = List.map (fn (_, _, t) => box [string t, newline]) leading
          val mainParts = interleave firstEnd [SP.p_sgn_item si] rest
        in
          vbox (ListUtil.join [newline] (leadingParts @ mainParts))
        end
  end

fun formatUrToString filename wid =
  case parseUrWithComments filename of
    NONE => NONE
  | SOME (decls, comments) =>
      let
        val content = readAll filename
        val pd = p_file_with_comments_simple decls comments content
        val tmp = OS.FileSys.tmpName ()
        val outf = TextIO.openOut tmp
        val str = Print.openOut {dst = outf, wid = wid}
        val () = Print.fprint str pd
        val () = Print.PD.PPS.closeStream str
        val () = TextIO.closeOut outf
        val inf = TextIO.openIn tmp
        val result = TextIO.inputAll inf
        val () = TextIO.closeIn inf
        val () = OS.FileSys.remove tmp handle OS.SysErr _ => ()
      in
        SOME result
      end

fun formatUrsToString filename wid =
  case parseUrsWithComments filename of
    NONE => NONE
  | SOME (sgn_items, comments) =>
      let
        val content = readAll filename
        val wrapped = "sig\n" ^ content
        val pd = p_sgn_items_with_comments sgn_items comments wrapped
        val tmp = OS.FileSys.tmpName ()
        val outf = TextIO.openOut tmp
        val str = Print.openOut {dst = outf, wid = wid}
        val () = Print.fprint str pd
        val () = Print.PD.PPS.closeStream str
        val () = TextIO.closeOut outf
        val inf = TextIO.openIn tmp
        val result = TextIO.inputAll inf
        val () = TextIO.closeIn inf
        val () = OS.FileSys.remove tmp handle OS.SysErr _ => ()
      in
        SOME result
      end

fun formatUrFile filename wid =
  case formatUrToString filename wid of
    NONE => false
  | SOME out =>
      let
        val outf = TextIO.openOut filename
        val () = TextIO.output (outf, out)
        val () = TextIO.closeOut outf
      in
        true
      end

fun formatUrsFile filename wid =
  case formatUrsToString filename wid of
    NONE => false
  | SOME out =>
      let
        val outf = TextIO.openOut filename
        val () = TextIO.output (outf, out)
        val () = TextIO.closeOut outf
      in
        true
      end

end
