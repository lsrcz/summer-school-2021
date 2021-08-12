datatype Card = Shelf | Patron(name: string)
datatype Book = Book(title: string)
type Library = map<Book, Card>

predicate Init(v: Library) {
  forall book | book in v :: v[book] == Shelf
}

predicate CheckOut(v:Library, v':Library, book:Book, patron:string) {
  && book in v
  && v[book] == Shelf
  && (forall book | book in v :: v[book] != Patron(patron))
  && v' == v[book := Patron(patron)]
}

predicate CheckIn(v:Library, v':Library, book:Book, patron:string) {
  && book in v
  && v[book] == Patron(patron)
  && v' == v[book := Shelf]
}

predicate Next(v:Library, v':Library) {
  || (exists book, patron :: CheckOut(v, v', book, patron))
  || (exists book, patron :: CheckIn(v, v', book, patron))
}

predicate CheckedOutTo(v:Library, book:Book, name: string) {
  && book in v
  && v[book] == Patron(name)
}

function BooksOutstanding(v:Library, name: string) : set<Book> {
  set book: Book | book in v && CheckedOutTo(v, book, name)
}

// This alternate variant uses set-cardinality as the definition
// of the safety property.
predicate Safety(v:Library) {
  forall name :: |BooksOutstanding(v, name)| <= 1
}

predicate Inv(v: Library) {
  Safety(v)
}

lemma SafetyProof()
  ensures forall v :: Init(v) ==> Inv(v)
  ensures forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
  ensures forall v :: Inv(v) ==> Safety(v)
{
  forall v, v' | Inv(v) && Next(v, v') ensures Inv(v') {
    InductiveStep(v, v');
  }
}

predicate HasAtMostOneBook(v: Library, name: string) {
  forall book1, book2 ::
    ( CheckedOutTo(v, book1, name) && CheckedOutTo(v, book2, name)
      ==> book1 == book2 )
}

// ...But reasoning about set cardinality is a bit more annoying in
// Dafny. Dafny's pretty darn good with quantifiers, but has a harder
// time with set cardinality rules (details on why on Friday, at the
// end of the course). So the way I chose to prove this version was
// to show that the two definitions are equivalent...
lemma SafetySynonyms(v: Library, name: string)
  ensures (|BooksOutstanding(v, name)| <= 1) <==> HasAtMostOneBook(v, name)
{
  if |BooksOutstanding(v, name)| <= 1 {
    if book1, book2 :|
      CheckedOutTo(v, book1, name) && CheckedOutTo(v, book2, name)
      && book1 != book2 {
//      assert book1 in BooksOutstanding(v, name);
//      assert book2 in BooksOutstanding(v, name);
//      assert {book1, book2} <= BooksOutstanding(v, name);
      subsetCardinality({book1, book2}, BooksOutstanding(v, name));
//      assert |{book1, book2}| <= |BooksOutstanding(v, name)|;
      assert false;
    }
  }
  if HasAtMostOneBook(v, name) && |BooksOutstanding(v, name)| > 1 {
    var uniqueBook :| CheckedOutTo(v, uniqueBook, name);
    var remainingBooks := BooksOutstanding(v, name) - {uniqueBook};
    assert |remainingBooks| > 0;  // tickle set cardinality relation.
//    var otherBook :| otherBook in remainingBooks;
//    assert false;
  }
}

// ...and then invoke that lemma in the same basic proof structure as
// in the first case. Perhaps you could write a proof that worked just
// on the set definition?
lemma InductiveStep(v: Library, v': Library)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{
  forall name ensures |BooksOutstanding(v', name)| <= 1
  {
    SafetySynonyms(v, name);
    assert HasAtMostOneBook(v, name);
    if book, patron :| CheckOut(v, v', book, patron) {
      forall book1, book2
        | CheckedOutTo(v', book1, name) && CheckedOutTo(v', book2, name)
        ensures book1 == book2
      {
        if !CheckedOutTo(v, book1, name) {
          assert book1 == book;
        }
        if !CheckedOutTo(v, book2, name) {
          assert book2 == book;
        }
      }
      assert HasAtMostOneBook(v', name);
    } else {
      var book, patron :| CheckIn(v, v', book, patron);
      forall book1, book2
        | CheckedOutTo(v', book1, name) && CheckedOutTo(v', book2, name)
        ensures book1 == book2
      {
        assert CheckedOutTo(v, book1, name);
        assert CheckedOutTo(v, book2, name);
      }
      assert HasAtMostOneBook(v', name);
    }
    SafetySynonyms(v', name);
  }
}

// Dafny seems to be missing a heuristic to trigger this cardinality relation!
// So I proved it. This should get fixed in dafny, or at least tucked into a
// library! How embarrassing.
lemma subsetCardinality<T>(seta:set<T>, setb:set<T>)
  requires seta <= setb
  ensures |seta| <= |setb|
{
  if seta == {} {
    assert |seta| <= |setb|;
  } else {
    var element :| element in seta;
    if element in setb {
      subsetCardinality(seta - {element}, setb - {element});
      assert |seta| <= |setb|;
    } else {
      subsetCardinality(seta - {element}, setb);
      assert |seta| <= |setb|;
    }
  }
}
