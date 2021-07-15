module Crawler {
  //datatype Constants = Constants()
  datatype Variables = Variables(x:int, y:int)

  predicate Init(v:Variables) {
    && v.x == 0
    && v.y == 5
  }

  predicate MoveNorth(v:Variables, v':Variables) {
    && v'.x == v.x
    && v'.y == v.y + 1
  }

  predicate MoveSouthEast(v:Variables, v':Variables) {
    && v'.x == v.x + 1
    && v'.y == v.y - 1
  }

  predicate Next(v:Variables, v':Variables) {
    || MoveNorth(v, v')
    || MoveSouthEast(v, v')
  }

  predicate InManhole(v:Variables) {
    v.x*v.x + v.y*v.y <= 3*3
  }

  predicate Safety(v:Variables) {
    !InManhole(v)
  }

  predicate Inv(v:Variables) {
    v.x + v.y >= 5
  }

  // Here's your obligation. Probably easiest to break this up into three
  // lemmas, each P==>Q becomes requires P ensures Q.
  lemma SafetyTheorem(v:Variables, v':Variables)
    ensures Init(v) ==> Inv(v)
    ensures Inv(v) && Next(v, v') ==> Inv(v')
    ensures Inv(v) ==> Safety(v)
  {
  }
}
