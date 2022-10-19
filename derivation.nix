{ stdenv, lib, fetchFromGitHub, file, openssl, mlton
, libmysqlclient, postgresql, sqlite, gcc
, automake, autoconf, libtool, icu67
}:

stdenv.mkDerivation rec {
  name = "urweb-${version}";
  version = "2018-06-22";
  
  src = ./.;

  buildInputs = [ openssl mlton libmysqlclient postgresql sqlite automake autoconf libtool icu67.dev openssl.dev];

  configureFlags = "--with-openssl=${openssl.dev}";

  preConfigure = ''
    ./autogen.sh
    export PGHEADER="${postgresql}/include/libpq-fe.h";
    export MSHEADER="${libmysqlclient.dev}/include/mysql/mysql.h";
    export SQHEADER="${sqlite.dev}/include/sqlite3.h";
    export ICU_LIBS="-L${icu67.out}/lib";
    export ICU_INCLUDES="-I${icu67.dev}/include";
    export CC="${gcc}/bin/gcc";
    export CCARGS="-I$out/include \
                   -I${icu67.dev}/include \
                   -pthread \
                   -L${openssl.out}/lib \
                   -L${libmysqlclient}/lib \
                   -L${postgresql.lib}/lib \
                   -L${sqlite.out}/lib \
                   -L${icu67.out}/lib";
  '';

  # Be sure to keep the statically linked libraries
  dontDisableStatic = true;

  meta = {
    description = "Advanced purely-functional web programming language";
    homepage    = "http://www.impredicative.com/ur/";
    license     = lib.licenses.bsd3;
    platforms   = lib.platforms.linux ++ lib.platforms.darwin;
    maintainers = [];
  };
}
