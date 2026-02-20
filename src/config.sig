signature CONFIG = sig
    val builddir : string

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
end
