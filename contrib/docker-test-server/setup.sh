#!/bin/bash

export CFLAGS="-g -W -Wall -Wextra -Werror"
export CONFIGOPTS=" --enable-autocreate --enable-backup --enable-calalarmd --enable-gssapi --enable-http --enable-idled --enable-murder --enable-nntp --enable-replication --enable-shared --enable-silent-rules --enable-unit-tests --enable-xapian --enable-jmap --with-ldap=/usr"

# build cyrus
/srv/cyrus-imapd.git/tools/build-with-cyruslibs.sh

# set up paths
install -o cyrus -d /var/run/cyrus
install -o cyrus -d /etc/cyrus
install -o cyrus -d /var/imap
install -o cyrus -d /var/imap/config
install -o cyrus -d /var/imap/search
install -o cyrus -d /var/imap/spool

# install config

install -m 644 /srv/cyrus-imapd.git/contrib/docker-test-server/imapd.conf /etc/cyrus/imapd.conf
install -m 644 /srv/cyrus-imapd.git/contrib/docker-test-server/cyrus.conf /etc/cyrus/cyrus.conf

