//#title include directive and Union (sum) datatypes

// You can include code from another file. includes must all appear at the
// beginning of a file, before any other definitions.
include "lib_directions.dfy"
// Open and read lib_directions.dfy.

lemma TwoWrongsDontMakeARight(dir:Direction)
{
//#exercise  assert TurnLeft(TurnLeft(TurnLeft(dir))) == TurnRight(TurnRight(dir));
//#start-elide
  assert TurnLeft(TurnLeft(dir)) == TurnRight(TurnRight(dir));
//#end-elide
}

