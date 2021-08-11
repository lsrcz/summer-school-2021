// Struct (product) datatypes.

// Okay, but I know you won't settle for merely renaming some fancy type
// expression.  You actually want to define something new.

// Dafny has "algebraic" datatypes which capture both "struct"
// and (tagged) "union".
// First, structs:
datatype Point = PointCtor(x:int, y:int)
// NB the thing on the left (Point) is the name of the datatype,
// as used in formal parameters. The thing on the right (PointCtor)
// is the "constructor", used in literals. For a 'struct' like this,
// they'll often just be the same string, since which one we mean
// is always unambiguous from context.
// datatype Point = Point(x:int, y:int)

function subtractPoints(tip:Point, tail:Point) : Point
{
  PointCtor(tip.x - tail.x, tip.y - tail.x)
}

lemma PointArithmetic()
{
  var a := PointCtor(1,13);
  var b := PointCtor(2,7);

  // NB Points (and every other `datatype`) are mathematical, immutable
  // objects, so the one we get back from the function must be equal
  // (identical) to the one we construct manually. There's no implicit
  // user-overridable Equals() method; these are platonic mathematical objects.

  // This exercise is a little harder than the previous ones; take a moment
  // to investigate it carefully!
  assert subtractPoints(a, b) == PointCtor(-1, 6);
}

