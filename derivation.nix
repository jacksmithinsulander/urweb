{ stdenv, lib, mlton
, libmysqlclient, postgresql, sqlite, gcc
, libunistring, samurai
}:

stdenv.mkDerivation rec {
  name = "urweb-${version}";
  version = "20200209";

  src = ./.;

  buildInputs = [ mlton libmysqlclient postgresql sqlite libunistring samurai ];

  preConfigure = ''
    export PGHEADER="${postgresql}/include/libpq-fe.h";
    export MSHEADER="${libmysqlclient.dev}/include/mysql/mysql.h";
    export SQHEADER="${sqlite.dev}/include/sqlite3.h";
    export LIBUNISTRING_INCLUDES="-I${libunistring.dev}/include";
    export LIBUNISTRING_LIBS="-L${libunistring.out}/lib -lunistring";
    export CC="${gcc}/bin/gcc";
  '';

  configureFlags = [ "--prefix=$out" ];

  buildPhase = "samurai";
  installPhase = "samurai install";
  checkPhase = "samurai test";

  # BearSSL is vendored in vendor/BearSSL
  dontDisableStatic = true;

  meta = {
    description = "Advanced purely-functional web programming language";
    homepage    = "http://www.impredicative.com/ur/";
    license     = lib.licenses.bsd3;
    platforms   = lib.platforms.linux ++ lib.platforms.darwin;
    maintainers = [];
  };
}
