#!/bin/bash

service rsyslog start
/usr/cyrus/bin/master -p /var/run/cyrus/master.pid -d -L /var/run/cyrus/log
/srv/cyrus-imapd.git/contrib/docker-test-server/webserver.pl prefork -l http://*:80
