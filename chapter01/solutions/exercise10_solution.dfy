// include directive. Union (sum) datatypes

// You can include code from another file. includes must all appear at the
// beginning of a file, before any other definitions.
include "lib_directions.dfy"
// Open and read lib_directions.dfy.

lemma TwoWrongsDontMakeARight(d:Direction)
{
  assert TurnLeft(TurnLeft(d)) == TurnRight(TurnRight(d));
}

