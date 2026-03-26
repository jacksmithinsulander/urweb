(* Native KV (`urweb_put` / `urweb_get`) with `dbms ndb` and the in-repo urweb_ndb staticlib.
   Same patterns work for `dbms persy` or `dbms rocksdb` (RocksDB needs system librocksdb). *)

fun main () : transaction page =
    urweb_put "greet" "hello";
    s <- urweb_get "greet";
    return <xml><body>{txt s}</body></xml>

(* Partial application (Ur `let` / `in` / `end`):

fun main () : transaction page =
    let
        val putGreet = urweb_put "greet"
    in
        putGreet "hi";
        s <- urweb_get "greet";
        return <xml><body>{txt s}</body></xml>
    end
*)
