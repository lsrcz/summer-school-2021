//#title More with algebraic datatypes.

// Begin by reading lunch.dfy! I extracted it to a separate file because
// we'll use it again later.
include "lib_lunch.dfy"

lemma AlgebraicLunch()
{
  var meal:set<Order> := {
    Pizza(Ham, Olive),
    Sandwich(Ham, Provolone),
    Pizza(Ham, Olive)
    };
  // Fix this assertion. Hint: The two pizzas are the same element of the datatype.
  assert |meal| == 3;
}

