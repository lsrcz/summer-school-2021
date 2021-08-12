//#title Functions

// A `function` is a mathematical function.
// This one has a domain of the integers and the range is (within) the
// integers. Again, `int` is the entire set of mathematical integers.

// Run dafny on this file. See where it fails. Fix it.

function Double(a:int) : int
{
  // The body of a function is an expression context. No semicolon
  // at the end.
  2 * a
}

// A lemma is like a C++ method or C function (hence the statement context).
// The proof it contains is like a program: a sequence of statements.
// As in C, statements terminate with semicolons and can be grouped into blocks
// with braces.
lemma DoubleIsLikePlus()
{
  assert Double(6) == 6 + 6;
  {
//#exercise    assert Double(-2) == 4;
//#start-elide
    assert Double(-2) == -4;
//#end-elide
  }
}

// A lemma can take arguments. This is one way to prove a statement about
// *any* x, not just a particular literal.
lemma foo4(x:int)
{
//#exercise  assert Double(x) == x + x + x;
//#start-elide
  assert Double(x) == x + x;
//#end-elide
}
