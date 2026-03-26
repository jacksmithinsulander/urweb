TigerBeetle example (urweb_tb_transfer)
=======================================

Link against the TigerBeetle C client (`tb_client.h`, `-ltb_client`). The `database`
line is the cluster address string passed to `tb_client_init`.

Generated C blocks until the async `tb_client_submit` completes (pthread condvar).
You must have accounts/ledger/code consistent with the emitted defaults (`ledger` 1,
`code` 1) or adjust the server side to match.

The compiler currently uses an all-zero 16-byte cluster id in `tb_client_init`;
use a real cluster id for production (future compiler support may add this to `.urp`).
