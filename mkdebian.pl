#!/usr/bin/perl -w

use strict;
use warnings;

my $num = `git log --pretty=oneline | wc -l`;
chomp($num);

my $branch = `git branch | grep \\\* | cut -c 3-`;
chomp($branch);

my $date = `date -R`;

my $CYRUSLIBS = "cyruslibs-fastmail-v11";

my $basename = "cyrus-$branch";
my $basedir = $branch eq 'fastmail' ? 'usr/cyrus' : "usr/$basename";

my $LEXFIX = "echo";
if ($ENV{CYRUS_LEXFIX}) {
  $LEXFIX = "make lex-fix";
}

unless (`dpkg --get-selections | grep $CYRUSLIBS`) {
    system("apt-get", "update");
    system("apt-get", "-y", "install", $CYRUSLIBS);
}

mkdir("debian");
open(FH, ">debian/changelog");
print FH <<EOF;
cyrus-$branch ($num-1) experimental; urgency=low

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
Description: Cyrus package for branch $branch at FastMail.FM

Package: $basename-build
Architecture: all
Depends: \${shlibs:Depends}
Description: Cyrus package for branch $branch at FastMail.FM - build files
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

# Use v4 compatability mode, so ldconfig gets added to maint scripts.
export DH_COMPAT=4

PACKAGE=\$(shell dh_listpackages)

build:
	dh_testdir
	autoreconf -v -i
	./configure --without-krb --with-perl=/usr/bin/perl --enable-silent-rules --enable-http --enable-calalarmd --enable-idled --with-extraident=git-$branch-$num --prefix=/$basedir --with-lmdb --with-zlib --without-snmp --enable-replication --enable-xapian --enable-jmap --enable-backup XAPIAN_CONFIG=/usr/local/$CYRUSLIBS/bin/xapian-config-1.5
	$LEXFIX
	make -j 8 all CFLAGS="-g -fPIC -W -Wall -Werror -fstack-protector-all"
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
	install -o root -m 755 tools/translatesieve debian/$basename/$basedir/bin/translatesieve
	install -o root -m 755 tools/upgradesieve debian/$basename/$basedir/bin/upgradesieve

	# set up source package
	# no need to actually install the built object files!  It's just the source we want
	mkdir -p debian/$basename-build/usr/src/$basename-build/cyrus
	# but keep the git data so we can build again!
	find . -maxdepth 1 -mindepth 1 -not -name debian -print0 | \\
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

print "Debian build environment for branch \"$branch\" set up

  - run dpkg-buildpackage to build\n";
