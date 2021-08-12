//#title Quantifiers
include "lib_directions.dfy"
include "lib_lunch.dfy"

// Most of what we'll be working with in proof are quantified
// statements: for all inputs, my program produces the right output!
lemma Forall()
{
  assert forall x:int :: x+x == 2*x;
}

// Remember this critter from exercise10? We can rewrite it in a forall.
lemma AnotherForall()
{
  // "Two wrongs don't make a right, but ..."
//#exercise  assert forall d :: TurnLeft(TurnLeft(TurnLeft(d))) == TurnRight(TurnRight(d));
//#start-elide
  assert forall d :: TurnLeft(TurnLeft(d)) == TurnRight(TurnRight(d));
//#end-elide
}

// Here's there-exists, forall's evil twin.
// exists a :: P(a) == !forall a :: !P(a)
lemma TryThatCheeseOnASandwich()
{
  // Hey, neat. Dafny has a hard time proving exists. It needs
  // a "witness".
  // To proceed, replace 'assert' with 'assume', and move on to the
  // next lemma to read about how to solve it.
  // If the '?' syntax is surprising, go re-read lib_directions.dfy.
//#exercise  assert forall o1:Order :: o1.Appetizer?
//#start-elide
  assume forall o1:Order :: o1.Appetizer?
//#end-elide
    ==> exists o2:Order :: o2.Sandwich? && o1.cheese == o2.cheese;
}

lemma CheeseTakeTwo()
{
  // So here's the "statement" version of a forall expression.
  // With nothing in the body, it's exactly equivalent to the assertion
  // above.
  forall o1:Order
    // The assumptions follow a '|' ("such that")
    | o1.Appetizer?
    // The conclusions follow a "requires" keyword.
    ensures exists o2:Order :: o2.Sandwich? && o1.cheese == o2.cheese
  {
    // The body of the forall statement is a proof context for the
    // statement's conclusion. Inside here, o1 is defined, and we
    // can use it to complete the proof.

    // But how? What's missing is that Dafny needs a "witness" to the
    // there-exists. We need to show an expression that satisfies the
    // body of the exists. Try uncommenting these lines:
//#exercise//    var o3 := Sandwich(Ham, o1.cheese);
//#start-elide
    var o3 := Sandwich(Ham, o1.cheese);
//#end-elide
//    assert o3.Sandwich? && o1.cheese == o3.cheese;
    // Simply *mentioning* an Order that satisfies the predicate
    // on o2 above is enough for Dafny to see the proof; once we mention
    // it, Dafny will try plugging it into the expression. Try removing
    // the assertion above this comment; notice that the proof still goes
    // through.
  }
}

