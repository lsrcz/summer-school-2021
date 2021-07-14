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


predicate Safety(s:Library) {
}

predicate Inv(s: Library) {
  Safety(s)
}

lemma SafetyProof()
  ensures forall s | Init(s) :: Inv(s)
  ensures forall s, s' | Inv(s) && Next(s, s') :: Inv(s')
  ensures forall s | Inv(s) :: Safety(s)
{
}
