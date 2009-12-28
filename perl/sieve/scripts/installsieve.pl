#! /bin/sh
exec perl -x -S $0 ${1+"$@"} # -*-perl-*-
#!perl -w
#
# Copyright (c) 1994-2008 Carnegie Mellon University.  All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
#
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
#
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in
#    the documentation and/or other materials provided with the
#    distribution.
#
# 3. The name "Carnegie Mellon University" must not be used to
#    endorse or promote products derived from this software without
#    prior written permission. For permission or any legal
#    details, please contact
#      Carnegie Mellon University
#      Center for Technology Transfer and Enterprise Creation
#      4615 Forbes Avenue
#      Suite 302
#      Pittsburgh, PA  15213
#      (412) 268-7393, fax: (412) 268-7395
#      innovation@andrew.cmu.edu
#
# 4. Redistributions of any form whatsoever must retain the following
#    acknowledgment:
#    "This product includes software developed by Computing Services
#     at Carnegie Mellon University (http://www.cmu.edu/computing/)."
#
# CARNEGIE MELLON UNIVERSITY DISCLAIMS ALL WARRANTIES WITH REGARD TO
# THIS SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS, IN NO EVENT SHALL CARNEGIE MELLON UNIVERSITY BE LIABLE
# FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN
# AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING
# OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#
# $Id: installsieve.pl,v 1.7.12.1 2009/12/28 21:51:53 murch Exp $
#
use Cyrus::SIEVE::managesieve;
use Getopt::Long;

$username = "";

print "NOTE: This program is deprecated. Please use sieveshell\n";
print "\n";

$ret = GetOptions("v|views:s" => \$views,
		  "l|list" => \$list,
#		  "p|port:i" => \$port,
		  "i|installs:s" => \$installs,
		  "a|activates:s" => \$activates,
		  "d|deletes:s" => \$deletes,
#		  "m|mechanism:s" => \$mech,
		  "g|gets:s" => \$gets,
                  "u|username:s" => \$username,
#		  "w|password:s" => \$pass
                  );
if (!$ret || $#ARGV != 0) { 
    show_help();
    exit;
}

$acapserver = $ARGV[0];

sub list_cb {

  my($name, $isactive) = @_ ;
  
  print "$name ";
  if ($isactive == 1) {
    print " <- active script\n";
  } else {
    print "\n";
  }

}

sub prompt {

  my($type, $prompt) = @_ ;

  if (($type eq "username") && (defined $username)) {
      return $username;
  } elsif (($type eq "authname") && (defined $username)) {
      return $username;
  } elsif (($type eq "realm") && (defined $realm)) {
      return $realm;
  }

  print "$prompt: ";

  $b = <STDIN>;
  chop($b);
  
  $b;
}

sub show_help {
  print "Usage:\n";
  print "  installsieve [options] <server>\n";
  print "\n";
  print "  -v <name>    view script\n";
  print "  -l           list available scripts\n";
#  print "  -p <port>    port to connect to\n";
  print "  -i <file>    filename of script to install\n";
  print "  -a <name>    Set <name> as the active script\n";
  print "  -d <name>    Delete <name> script from server\n";
#  print "  -m <mech>    Mechanism to use for authentication\n";
  print "  -g <name>    Get script <name> and save to disk\n";
  print "  -u <user>    Userid/Authname to use\n";
#  print "  -w <passwd>  Specify password (Should only be used for automated scripts)\n";
  print "\n";
}

#main code
my $obj = sieve_get_handle($acapserver,"prompt","prompt","prompt","prompt");

if (!defined $obj) {
  die "Unable to connect to server";
}

if (defined $installs) {
  $ret = sieve_put_file($obj, $installs);
  if ($ret != 0) { print "upload failed\n"; }
}

if (defined $deletes) {
  $ret = sieve_delete($obj, $deletes);
  if ($ret != 0) { print "delete failed\n"; }
}

if (defined $activates) {
  $ret = sieve_activate($obj, $activates);
  if ($ret != 0) { print "activate failed\n"; }
}

if (defined $gets) {
    $str = "";
    $ret = sieve_get($obj, $gets, $str);
    if ($ret != 0) { 
	print "get failed\n"; 
    } else {
	open (OUTPUT,">$gets") || die "Unable to open $gets";
	print OUTPUT $str;
	close(OUTPUT);    
    }
}
if (defined $views) {
    $str = "";
    $ret = sieve_get($obj, $views, $str);
    if ($ret != 0) { 
	print "get failed\n"; 
    } else {
	# view
	print $str;
    }
}

if (defined $list) {
  $ret = sieve_list($obj, "list_cb");  
  if ($ret != 0) { print "List command failed\n"; }
}
