signature CONFIG = sig
    val builddir : string
    val srcdir : string
    val isDarwin : int

    val bin : string
    val srclib : string
    val lib : string
    val includ : string
    val sitelisp : string

    val ccompiler : string
    val ccArgs : string
    val bearssl : string

    val pgheader : string
    val msheader : string
    val sqheader : string

    val versionNumber : string
    val versionString : string

    val pthreadCflags : string
    val pthreadLibs : string

    val libunistringIncludes : string
    val libunistringLibs : string
    (* Empty on non-macOS or when static lib unavailable; otherwise full path to libunistring.a *)
    val libunistringStatic : string
end
