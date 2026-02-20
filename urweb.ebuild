# Distributed under the terms of the BSD3 license

# This file needs to be renamed to something like "urweb-20200209.ebuild", to reflect the Ur/Web version to use.

inherit eutils

EAPI=8

DESCRIPTION="A domain-specific functional programming language for modern web applications"
HOMEPAGE="http://www.impredicative.com/ur/"
SRC_URI="http://www.impredicative.com/ur/${P}.tgz"

LICENSE="BSD"
SLOT="0"
KEYWORDS="~amd64 ~x86"
IUSE=""

DEPEND="dev-lang/mlton
	dev-libs/libunistring
	dev-build/samurai"
RDEPEND="${DEPEND}"

# BearSSL is vendored; no OpenSSL or ICU dependency

S="${WORKDIR}/urweb"

src_unpack() {
	unpack ${A}
}

src_configure() {
	./configure --prefix=/usr
}

src_compile() {
	samurai
}

src_install() {
	samurai install DESTDIR=${D}
	dodoc CHANGELOG
}
