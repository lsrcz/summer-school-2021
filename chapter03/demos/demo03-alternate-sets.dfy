datatype Card = Shelf | Patron(name: string)
datatype Book = Book(title: string)
type Library = map<Book, Card>

predicate Init(s: Library) {
  forall book | book in s :: s[book] == Shelf
}

predicate CheckOut(s:Library, s':Library, book:Book, patron:string) {
  && book in s
  && s[book] == Shelf
  && (forall book | book in s :: s[book] != Patron(patron))
  && s' == s[book := Patron(patron)]
}

predicate CheckIn(s:Library, s':Library, book:Book, patron:string) {
  && book in s
  && s[book] == Patron(patron)
  && s' == s[book := Shelf]
}

predicate Next(s:Library, s':Library) {
  || (exists book, patron :: CheckOut(s, s', book, patron))
  || (exists book, patron :: CheckIn(s, s', book, patron))
}

predicate CheckedOutTo(s:Library, book:Book, name: string) {
  && book in s
  && s[book] == Patron(name)
}

function BooksOutstanding(s:Library, name: string) : set<Book> {
  set book: Book | book in s && CheckedOutTo(s, book, name)
}

// This alternate variant uses set-cardinality as the definition
// of the safety property.
predicate Safety(s:Library) {
  forall name :: |BooksOutstanding(s, name)| <= 1
}

predicate Inv(s: Library) {
  Safety(s)
}

lemma SafetyProof()
  ensures forall s :: Init(s) ==> Inv(s)
  ensures forall s, s' :: Inv(s) && Next(s, s') ==> Inv(s')
  ensures forall s :: Inv(s) ==> Safety(s)
{
  forall s, s' | Inv(s) && Next(s, s') ensures Inv(s') {
    InductiveStep(s, s');
  }
}

predicate HasAtMostOneBook(s: Library, name: string) {
  forall book1, book2 ::
    ( CheckedOutTo(s, book1, name) && CheckedOutTo(s, book2, name)
      ==> book1 == book2 )
}

// ...But reasoning about set cardinality is a bit more annoying in
// Dafny. Dafny's pretty darn good with quantifiers, but has a harder
// time with set cardinality rules (details on why on Friday, at the
// end of the course). So the way I chose to prove this version was
// to show that the two definitions are equivalent...
lemma SafetySynonyms(s: Library, name: string)
  ensures (|BooksOutstanding(s, name)| <= 1) <==> HasAtMostOneBook(s, name)
{
  if |BooksOutstanding(s, name)| <= 1 {
    if book1, book2 :|
      CheckedOutTo(s, book1, name) && CheckedOutTo(s, book2, name)
      && book1 != book2 {
//      assert book1 in BooksOutstanding(s, name);
//      assert book2 in BooksOutstanding(s, name);
//      assert {book1, book2} <= BooksOutstanding(s, name);
      subsetCardinality({book1, book2}, BooksOutstanding(s, name));
//      assert |{book1, book2}| <= |BooksOutstanding(s, name)|;
      assert false;
    }
  }
  if HasAtMostOneBook(s, name) && |BooksOutstanding(s, name)| > 1 {
    var uniqueBook :| CheckedOutTo(s, uniqueBook, name);
    var remainingBooks := BooksOutstanding(s, name) - {uniqueBook};
    assert |remainingBooks| > 0;  // tickle set cardinality relation.
//    var otherBook :| otherBook in remainingBooks;
//    assert false;
  }
}

// ...and then invoke that lemma in the same basic proof structure as
// in the first case. Perhaps you could write a proof that worked just
// on the set definition?
lemma InductiveStep(s: Library, s': Library)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
{
  forall name ensures |BooksOutstanding(s', name)| <= 1
  {
    SafetySynonyms(s, name);
    assert HasAtMostOneBook(s, name);
    if book, patron :| CheckOut(s, s', book, patron) {
      forall book1, book2
        | CheckedOutTo(s', book1, name) && CheckedOutTo(s', book2, name)
        ensures book1 == book2
      {
        if !CheckedOutTo(s, book1, name) {
          assert book1 == book;
        }
        if !CheckedOutTo(s, book2, name) {
          assert book2 == book;
        }
      }
      assert HasAtMostOneBook(s', name);
    } else {
      var book, patron :| CheckIn(s, s', book, patron);
      forall book1, book2
        | CheckedOutTo(s', book1, name) && CheckedOutTo(s', book2, name)
        ensures book1 == book2
      {
        assert CheckedOutTo(s, book1, name);
        assert CheckedOutTo(s, book2, name);
      }
      assert HasAtMostOneBook(s', name);
    }
    SafetySynonyms(s', name);
  }
}

// Dafny seems to be missing a heuristic to trigger this cardinality relation!
// So I proved it. This should get fixed in dafny, or at least tucked into a
// library! How embarrassing.
lemma subsetCardinality<T>(a:set<T>, b:set<T>)
  requires a <= b
  ensures |a| <= |b|
{
  if a == {} {
    assert |a| <= |b|;
  } else {
    var e :| e in a;
    if e in b {
      subsetCardinality(a - {e}, b - {e});
      assert |a| <= |b|;
    } else {
      subsetCardinality(a - {e}, b);
      assert |a| <= |b|;
    }
  }
}
