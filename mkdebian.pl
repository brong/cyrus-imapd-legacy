#!/usr/bin/perl -w

use strict;
use warnings;

my $tag = shift;
die "NO TAG GIVEN" unless $tag;

my $num = `git log --pretty=oneline | wc -l`;
chomp($num);

my $date = `date -R`;

my $CYRUSLIBS = "cyruslibs-fastmail-v44";

my $basename = "cyrus-$tag";
my $basedir = "usr/$basename";

my $LEXFIX = "echo";
if ($ENV{CYRUS_LEXFIX}) {
  $LEXFIX = "make lex-fix";
}

unless (`dpkg --get-selections | grep $CYRUSLIBS`) {
    system("apt-get", "update");
    system("apt-get", "-y", "install", $CYRUSLIBS);
}

mkdir("debian");

# https://www.debian.org/doc/manuals/maint-guide/dother.en.html#compat
# 2020-05-08:
# * The compat file defines the debhelper compatibility level. Currently, you should set it to the debhelper v10.
# * You may use compat level v9 in certain circumstances for compatibility with older systems. However, using
# * any level below v9 is not recommended and should be avoided for new packages.
open(FH, ">debian/compat");
print FH "10\n";
close(FH);

open(FH, ">debian/changelog");
print FH <<EOF;
cyrus-$tag ($num-1) experimental; urgency=low

  * basic package set up

 -- Bron Gondwana <brong\@fastmail.fm>  $date
EOF
close(FH);

open(FH, ">debian/control");
print FH <<EOF;
Source: $basename
Section: mail
Priority: extra
Maintainer: Bron Gondwana <brong\@fastmail.fm>
Build-Depends: libssl-dev, zlib1g-dev, comerr-dev, libsasl2-dev,
 libzephyr-dev, libpcre3-dev, autoconf, liblmdb-dev,
 libxml2-dev, libsqlite3-dev, $CYRUSLIBS,
 flex, bison, debhelper, libsnmp-dev, libglib2.0-dev

Package: $basename
Architecture: all
Depends: \${shlibs:Depends}, $CYRUSLIBS, liblmdb0
Description: Cyrus package for tag $tag at FastMail.FM

Package: $basename-build
Architecture: all
Depends: \${shlibs:Depends}
Description: Cyrus package for tag $tag at FastMail.FM - build files
EOF
close(FH);

open(FH, ">debian/copyright");
print FH "See the upstream files at CMU\n";
close(FH);

open(FH, ">debian/rules");
print FH <<EOF;
#!/usr/bin/make -f
# debian/rules for alien

# Uncomment this to turn on verbose mode.
#export DH_VERBOSE=1
export LDFLAGS=-L/usr/local/$CYRUSLIBS/lib/x86_64-linux-gnu -L/usr/local/$CYRUSLIBS/lib -Wl,-rpath,/usr/local/$CYRUSLIBS/lib/x86_64-linux-gnu -Wl,-rpath,/usr/local/$CYRUSLIBS/lib
export PKG_CONFIG_PATH=/usr/local/$CYRUSLIBS/lib/x86_64-linux-gnu/pkgconfig:/usr/local/$CYRUSLIBS/lib/pkgconfig:$ENV{PKG_CONFIG_PATH}
export PATH=/usr/local/$CYRUSLIBS/bin:$ENV{PATH}

PACKAGE=\$(shell dh_listpackages)

build:
	dh_testdir
	autoreconf -v -i
	./configure --without-krb --with-perl=/usr/bin/perl --enable-silent-rules --enable-http --enable-calalarmd --enable-idled --with-extraident=$tag --prefix=/$basedir --with-lmdb --with-zlib --without-snmp --enable-replication --enable-xapian --enable-jmap --enable-backup XAPIAN_CONFIG=/usr/local/$CYRUSLIBS/bin/xapian-config-1.5
	$LEXFIX
	make -j 8 all CFLAGS="-g -Og -fPIC -W -Wall -Wextra -Werror -fstack-protector-all -fno-semantic-interposition -Bsymbolic -fno-omit-frame-pointer"
	make sieve/test
	touch build

clean:
	dh_testdir
	dh_testroot
	dh_clean -d
	rm -f build

binary-indep: build

binary-arch: build
	dh_testdir
	dh_testroot
	dh_clean -k -d
	dh_installdirs

	dh_installdocs
	dh_installchangelogs

	make install DESTDIR=\$(CURDIR)/debian/$basename
	make install-binsymlinks DESTDIR=\$(CURDIR)/debian/$basename
	/bin/bash ./libtool --mode=install install -o root -m 755 sieve/test \$(PWD)/debian/$basename/$basedir/bin/sieve-test
	install -o root -m 755 tools/rehash debian/$basename/$basedir/bin/rehash
	install -o root -m 755 tools/mkimap debian/$basename/$basedir/bin/mkimap

	# set up source package
	# no need to actually install the built object files!  It's just the source we want
	mkdir -p debian/$basename-build/usr/src/$basename-build/cyrus
	# and skip the git data too since there's far too much of it
	find . -maxdepth 1 -mindepth 1 -not -name debian -not -name .git -print0 | \\
		xargs -0 -r -i cp -a {} debian/$basename-build/usr/src/$basename-build/cyrus/

	dh_compress
	dh_makeshlibs
	dh_installdeb
	#-dh_shlibdeps
	dh_gencontrol
	dh_md5sums
	dh_builddeb -- -z3

binary: binary-arch
EOF
close(FH);

chmod(0755, "debian/rules");

print "Debian build environment for tag \"$tag\" set up

  - run dpkg-buildpackage to build\n";
