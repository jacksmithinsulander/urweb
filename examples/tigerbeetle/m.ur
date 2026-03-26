(* Ledger: `urweb_tb_transfer debit credit amount xfer_id`
   (Basis.int; lower 64 bits become TigerBeetle 128-bit fields; ids must be >= 1).
   `urweb_put` / `urweb_get` are not supported on this backend. *)

fun main () : transaction page =
    urweb_tb_transfer 1 2 100 42;
    return <xml><body>ok</body></xml>

(* Curried style:

fun main () : transaction page =
    let
        val t = urweb_tb_transfer 1 2
    in
        t 100 42;
        return <xml><body>ok</body></xml>
    end
*)
