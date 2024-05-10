module Footprint {
  type pos = x: int | x > 0 witness 1

  trait {:termination false} footprintable<M> {
    ghost opaque const ReprDepth: pos

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      ensures n > 0 ==>
        ReprFamily(n) >= ReprFamily(n-1)
      reads this, if n == 0 then {} else ReprFamily(n-1)
    ghost function Repr(): set<object>
      reads this, ReprFamily(ReprDepth-1)
    {
      ReprFamily(ReprDepth)
    }

    lemma ReprLemma()
      ensures Repr() == ReprFamily(ReprDepth)
    {}

    ghost predicate Valid()
      reads this, Repr()

    ghost function Model(): M
      reads this, Repr()
      requires Valid()
  }
}
