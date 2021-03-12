//#instructor This example demonstrates the need and use of Jay Normal Form (JNF)

datatype Burger = Single | Double

datatype State = State(patties:nat, buns:nat)

predicate Init(s:State) {
    && s.patties == 0
    && s.buns == 0
}

// Action with parameters
predicate RestockPatties(s:State, s':State, pattyBoxSize:nat) {
    && s'.patties == s.patties + pattyBoxSize
    && s'.buns == s.buns    // UNCHANGED
}

predicate RestockBuns(s:State, s':State, bunBagSize:nat) {
    && s'.buns == s.buns + bunBagSize
    && s'.patties == s.patties  // UNCHANGED
}

function PattiesFor(burger:Burger) : nat {
    match burger {
        case Single => 1
        case Double => 2
    }
}

predicate SellBurger(s:State, s':State, burger:Burger) {
    && PattiesFor(burger) <= s.patties
    && 1 <= s.buns
    && s'.patties == s.patties - PattiesFor(burger)
    && s'.buns == s.buns - 1
}

predicate Next(s:State, s':State) {
    || exists pattyBoxSize :: RestockPatties(s, s', pattyBoxSize)
    || exists bunBagSize :: RestockBuns(s, s', bunBagSize)
    || exists burger :: SellBurger(s, s', burger)
}

///////////////////////////////////////////////////////////////////////////////
//
// Invariant proof example
//

predicate BunsInStockInv(s:State) {
    0 <= s.buns
}

// Base case
lemma BunsInStockInvInit(s:State)
    requires Init(s)
    ensures BunsInStockInv(s)
{
}

// Inductive step
lemma BunsInStockInvNext(s:State, s':State)
    requires Next(s, s')
    requires BunsInStockInv(s)
    ensures BunsInStockInv(s')
{
}
