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

datatype Step = 
    | CheckOutStep(book:Book, patron:string) 
    | CheckInStep(book:Book, patron:string)
    
predicate NextStep(v:Library, v':Library, step:Step) {
  match step
    case CheckOutStep(book,patron) => CheckOut(v, v', book, patron)
    case CheckInStep(book,patron) => CheckIn(v, v', book, patron)
}

predicate Next(v:Library, v':Library) {
    exists step:Step :: NextStep(v, v', step)
}



// name has at most book checked out.
//
// If you're coming from TLA+ background, you might have written
// this using set cardinality:
//   |BooksOutstanding(v, name)| <= 1
// For a solution like that, see demo00_alternate.dfy.
predicate CheckedOutTo(v:Library, book:Book, name: string) {
  && book in v
  && v[book] == Patron(name)
}

predicate HasAtMostOneBook(v: Library, name: string) {
  forall book1, book2 ::
    ( CheckedOutTo(v, book1, name) && CheckedOutTo(v, book2, name)
      ==> book1 == book2 )
}

predicate Safety(v:Library) {
  forall name :: HasAtMostOneBook(v, name)
}

predicate Inv(v: Library) {
  Safety(v)
}

lemma SafetyProof()
  ensures forall v | Init(v) :: Inv(v)
  ensures forall v, v' | Inv(v) && Next(v, v') :: Inv(v')
  ensures forall v | Inv(v) :: Safety(v)
{
  forall v, v' | Inv(v) && Next(v, v') ensures Inv(v') {
    InductiveStep(v, v');
  }
}


lemma InductiveStep(v: Library, v': Library)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{
  var step :| NextStep(v, v', step);
  forall name ensures HasAtMostOneBook(v', name) {
    assert HasAtMostOneBook(v, name);
    match step
      case CheckOutStep(book, patron) => {
        assert forall book, name | name != patron
          :: CheckedOutTo(v, book, name) == CheckedOutTo(v', book, name);
      }
      case CheckInStep(book, patron) => {
        forall book1, book2 |
          CheckedOutTo(v', book1, name) && CheckedOutTo(v', book2, name)
          ensures book1 == book2 {
          assert CheckedOutTo(v, book1, name);
          assert CheckedOutTo(v, book2, name);
        }
      }
  }
}
