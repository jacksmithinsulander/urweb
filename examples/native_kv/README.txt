Native KV example (urweb_ndb)
==============================

Requires compiling from a full Ur/Web tree with `lib/ur` so Basis and the injected
`UrwebNative` module resolve (`boot_linking` / `-boot` in your usual workflow).

Build native bridge libraries once:

  cargo build --workspace

Then compile this example with `ur-compile` (or your wrapper) from the checkout so
include/lib fallbacks for `urweb_ndb` / `urweb_persy` apply, or set URWEB_NATIVE_LIB_DIR.

Swap `dbms ndb` for `dbms persy` to use Persy with the same Ur source.
