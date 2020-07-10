module Crawler {
  //datatype Constants = Constants()
  datatype Variables = Variables(x:int, y:int)

  predicate Init(s:Variables) {
    && s.x == 0
    && s.y == 5
  }

  predicate MoveNorth(s:Variables, s':Variables) {
    && s'.x == s.x
    && s'.y == s.y + 1
  }

  predicate MoveSouthEast(s:Variables, s':Variables) {
    && s'.x == s.x + 1
    && s'.y == s.y - 1
  }

  predicate Next(s:Variables, s':Variables) {
    || MoveNorth(s, s')
    || MoveSouthEast(s, s')
  }

  predicate InManhole(s:Variables) {
    s.x*s.x + s.y*s.y <= 3*3
  }

  predicate Safety(s:Variables) {
    !InManhole(s)
  }

  predicate Inv(s:Variables) {
    true  // probably not strong enough. :v)
  }

  // Here's your obligation. Probably easiest to break this up into three
  // lemmas, each P==>Q becomes requires P ensures Q.
  lemma SafetyTheorem(s:Variables, s':Variables)
    ensures Init(s) ==> Inv(s)
    ensures Inv(s) && Next(s, s') ==> Inv(s')
    ensures Inv(s) ==> Safety(s)
  {
  }
}
