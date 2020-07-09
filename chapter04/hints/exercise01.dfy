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
    || MoveSouthEast s')
  }

  predicate InManhole(s:Variables) {
    s.x*s.x + s.y*s.y <= 3*3
  }

  predicate ReachabilityProperty(s:Variables) {
    s.x >= 0 && s.y >= 5-s.x
  }

  predicate Safety(s:Variables) {
    !InManhole(s)
  }
}
