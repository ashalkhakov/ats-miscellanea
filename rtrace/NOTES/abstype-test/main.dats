staload "foo.sats"

implement main () = let
  val x = make_foo ()
in
  print "hello"
end