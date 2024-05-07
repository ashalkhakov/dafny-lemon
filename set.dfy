// source: lemon, set.c
class LSet {
    var size: int

    /* All sets will be of size N */
    constructor(s: int)
        requires s > 0
        ensures Valid()
    {
        size := s;
    }

    predicate Valid()
        reads this
    {
        size > 0
    }

    /* A new set for element 0..N */
    method SetNew()
        returns (x: array<bool>)
        requires Valid()
        ensures x.Length == size
        ensures forall k :: 0 <= k < size ==> x[k] == false
    {
        x := new bool[size];
        var i := 0;
        while i < size
            invariant 0 <= i <= size
            invariant forall k :: 0 <= k < i ==> x[k] == false
        {
            x[i] := false;
            i := i + 1;
        }
    }

    /* Deallocate a set */
    method SetFree(x: array<bool>) {
        // nop
    }

    /* Add a new element to the set.  Return TRUE if the element was added
    ** and FALSE if it was already there. */
    method SetAdd(s: array<bool>, e: int)
        returns (rv: bool)
        requires Valid()
        modifies (s)
        requires s.Length == size
        requires 0 <= e < size
        ensures rv == old(s[e]) && s[e] == true
    {
        rv := s[e];
        s[e] := true;
    }

    /* Add every element of s2 to s1.  Return TRUE if s1 changes. */
    method SetUnion(s1: array<bool>, s2: array<bool>)
        returns (progress: bool)
        requires Valid()
        modifies (s1)
        requires s1.Length == s2.Length == size
        ensures forall k :: 0 <= k < size ==> s1[k] == (old(s1[k]) || s2[k])
        ensures forall k :: 0 <= k < size ==> s1[k] != old(s1[k]) ==> progress
    {
        var i := 0;
        progress := false;
        while (i < size)
            modifies (s1)
            invariant 0 <= i <= size
            invariant forall k :: 0 <= k < i ==> s1[k] == (old(s1[k]) || s2[k])
            invariant forall k :: 0 <= k < i ==> s1[k] != old(s1[k]) ==> progress
            invariant forall k :: i <= k < size ==> s1[k] == old(s1[k])
        {
            if (s2[i]==false) {

            } else {
                if (s1[i]==false) {
                    progress := true;
                    s1[i] := true;
                }
            }
            i := i + 1;
        }
    }

    /* True if Y is in set X */
    method SetFind(s: array<bool>, i: int)
        returns (x: bool)
        requires s.Length == size
        requires 0 <= i < size
        ensures x == s[i]
    {
        x := s[i];
    }
}
