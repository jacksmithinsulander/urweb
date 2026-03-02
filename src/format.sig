(* Copyright (c) 2008, Adam Chlipala
 * All rights reserved.
 *)

signature FORMAT = sig
    (* Comment: (startChar, endCharExcl, text) *)
    type comment = int * int * string

    val extractComments : string -> comment list
    val replaceCommentsWithSpaces : string -> comment list -> string

    (* Parse .ur file with comment preservation. Returns (decls, comments) or NONE on parse error. *)
    val parseUrWithComments : string -> (Source.decl list * comment list) option

    (* Parse .urs file with comment preservation. Returns (sgn_items, comments) or NONE on parse error. *)
    val parseUrsWithComments : string -> (Source.sgn_item list * comment list) option

    (* Format .ur file; writes to file. Returns false on parse error. *)
    val formatUrFile : string -> int -> bool

    (* Format .urs file; writes to file. Returns false on parse error. *)
    val formatUrsFile : string -> int -> bool

    (* Format to string. Returns NONE on parse error. *)
    val formatUrToString : string -> int -> string option
    val formatUrsToString : string -> int -> string option
end
