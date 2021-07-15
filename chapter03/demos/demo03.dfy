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


predicate Safety(v:Library) {
  false  // placeholder
}

predicate Inv(v: Library) {
  Safety(v)
}

lemma SafetyProof()
  ensures forall v | Init(v) :: Inv(v)
  ensures forall v, v' | Inv(v) && Next(v, v') :: Inv(v')
  ensures forall v | Inv(v) :: Safety(v)
{
}
