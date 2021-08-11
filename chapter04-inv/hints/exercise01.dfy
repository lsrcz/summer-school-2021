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

  // ...but the invariant doesn't need to be this strong!
  predicate ReachabilityProperty(v:Variables) {
    v.x >= 0 && v.y >= 5-v.x
  }

  predicate Safety(v:Variables) {
    !InManhole(v)
  }
}
