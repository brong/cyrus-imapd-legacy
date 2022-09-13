#!/usr/bin/perl -w

use lib '/srv/cyrus-imapd.git/perl/imap';
use Mojolicious::Lite;
use Mail::IMAPTalk;
use Cyrus::SyncProto;
use Cyrus::AccountSync;

get '/' => sub => {
  my $c = shift;
  $c->render(text => "Basic test server - read JSON for existing users or put JSON users");
};

get '/:userid' => sub {
  my $c   = shift;
  my $userid = $c->param('userid');
  my $as = _connect();
  my $data = $as->dump_user(username => $userid);
  if ($data) {
    $c->render(json => $data);
  }
  else {
    $c->render(text => 'Not found.', status => 404);
  }
};

put '/:userid' => sub {
  my $c   = shift;
  my $userid = $c->param('userid');
  my $json = $c->req->json;
  my $as = _connect();
  $as->delete_user(username => $userid);
  $as->undump_user(username => $userid, data => $json);
  $c->render(text => 'Created.', status => 201);
};

sub _connect {
  my $it = Mail::IMAPTalk->new(
    Server => 'localhost',
    Port => 143,
    Username => 'admin',
    Password => 'admin',
    AuthzUser => 'admin',
    UseSSL => 0,
    UseBlocking => 1,
    UseCompress => 0,
  );
  my $sp = Cyrus::SyncProto->new($it);
  return Cyrus::AccountSync->new($sp);
}
