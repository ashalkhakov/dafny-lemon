module HashMap {
  /* There is one instance of this structure for every data element
  ** in an associative array of type "x1".
  */
  class hashtablenode<K,T> {
    var key: K                     /* The key */
    var data: T                    /* The data */
    var next: hashtablenode?<K, T>    /* Next entry with the same hash */
    //var prev: hashtablenode?<T>    /* Previous link */

    constructor(key: K, data: T)
      ensures Valid()
      ensures this.data == data && elements == map[key:=data] && list == [(key,data)] && nodes == {this} && next == null
    {
      this.key := key;
      this.data := data;
      this.next := null;
      //this.prev := null;
      list := [(key,data)];
      elements := map[key:=data];
      nodes := {this};
    }

    // abstract variable storing (in the same order) the list of elements 
    // in the sequence headed by 'this'
    ghost var list: seq<(K,T)>

    ghost var elements: map<K,T>

    // Heap frame, 
    // Consists of the set of nodes in the list headed by 'this'
    ghost var nodes: set<hashtablenode<K,T>>

    ghost function Repr(): set<object>
      reads this
    {
      nodes
    }

    ghost function length(): int
      reads this, nodes
      requires Valid()
      ensures length() == |nodes|
    {
      if this.next == null then 1
      else 1 + next.length()
    }

    /*ghost predicate Free()
      reads this
    {
      && data == null
      && next == null
      && nodes == {}
      && list == []
    }*/

    // The invariant predicate provides a definition of 'list' and 'nodes'
    // by induction of the length of the list
    ghost predicate Valid()
      decreases nodes
      reads this, nodes
    {
      // this in nodes &&      
      //&& data != null
      && (next == null ==> nodes == {this} 
                            && list == [(key,data)]
                            && elements == map[key:=data]
          )
      && (next != null ==> next in nodes 
                            && nodes == {this} + next.nodes
                            && this !in next.nodes // acyclity condition
                            && key !in next.elements // uniqueness condition
                            && list == [(key,data)] + next.list
                            && elements == map[key:=data] + next.elements
                            && next.Valid()
          )
    }

    ghost function Model(): map<K,T>
      reads this, Repr()
      requires Valid()
    {
      elements
    }

    /*constructor empty()
      ensures Free()
    {
      this.data := null;
      this.next := null;
      this.nodes := {};
      this.list := [];
    }*/

    // Makes 'this' the head of a sigleton list containg element 'e'
    constructor singleton(k: K, e: T)
      ensures Valid()
      ensures list == [(k,e)]
      ensures elements == map[k:=e]
      ensures nodes == {this}
    {
      key := k;
      data := e;
      next := null;

      list := [(k,e)];
      nodes := {this};
      elements := map[k:=e];
    }

    // Makes 'this' the head of a non-sigleton list containg element 'e' 
    // and continuing with the list headed by 'n'
    method insert_before(k: K, e: T, n: hashtablenode<K,T>)
      modifies this
      requires n.Valid()
      requires this !in n.nodes
      requires k !in n.elements.Keys
      ensures Valid()
      ensures this.key == k
      ensures this.data == e
      ensures list == [(k,e)] + n.list
      ensures elements == map[k:=e] + n.elements
      ensures nodes == {this} + n.nodes
    {
      key := k;
      data := e;
      next := n;

      list := [(k,e)] + n.list;
      elements := map[k:=e] + n.elements;
      nodes := {this} + n.nodes;
    }

    // Returns the (possibly empty) tail of the list headed by 'this'
    method tail() returns (t: hashtablenode?<K,T>)
      requires Valid()
      ensures Valid()
      ensures t != null ==> t.Valid()
                            && t.nodes == nodes - {this}
                            && t.list == list[1..]
                            && t.elements == elements - {key}
    {
      t := next;
    }
  }

  // Function type for hash functions 
  type hashfunction<!K(==)> = (K) -> nat

  /* There is one instance of the following structure for each
  ** associative array of type "x1".
  */
  class hashtable<K(==),T(==)> {
    var size: nat                 /* The number of available slots. */
                                  /*   Must be a power of 2 greater than or */
                                  /*   equal to 1 */
    var count: int                 /* Number of currently slots filled */
    // TODO: keep an array of objects? the objects of type T would be stored here
    // 0 <= i < count
    var ht: array<hashtablenode?<K,T>>  /* The data stored here */
    //var ht: array<hashtablenode?<T>>   /* Hash table for lookups */
    var hash: hashfunction<K>

    ghost var repr: set<object>
    ghost var elements: map<K,T>

    ghost function Repr0(): set<object>
      reads this
    {
      {this} + repr + {ht}
    }
    ghost function Repr1(): set<object>
      reads this, Repr0()
    {
      Repr0() + (set x | x in ht[..] && x != null)
    }
    ghost function Repr2(): set<object>
      reads this, Repr0(), Repr1()
    {
      Repr1() + (set x,y | x in ht[..] && x != null && y in x.Repr() :: y)
    }

    ghost function Repr(): set<object>
        reads Repr0(), Repr1()
    {
        Repr0() + Repr1() + Repr2()
    }
    ghost function InsertRepr(): set<object>
        reads this, ht, ht[..]
    {
        {this} + repr + {ht} + set x | x in ht[..]
    }

    ghost function Model(): map<K,T>
      reads this, Repr()
      requires Valid()
      ensures Valid()
    {
      //(set x,y | x in ht[..] && x != null && y in x.Model() :: y)
      reveal Valid();
      elements
    }

    ghost function sum_set(xs: set<int>): int
    {
      if xs == {} then 0
      else
          var x :| x in xs;
          x + sum_set(xs - {x})
    }

    ghost function pick(s: set<map<K,T>>): map<K,T>
    requires s != {}
    {
        var x :| x in s; x
    }
    ghost function flatten<K>(nested: set<set<K>>): set<K>
    {
      set x, y | y in nested && x in y :: x
    }
    predicate disjoint(nested: set<set<K>>)
    {
      forall i, j :: i in nested && j in nested && i != j ==> i * j == {}
    }

    opaque ghost predicate Valid()
      reads this, Repr()
    {
      && this !in repr
      //&& ht in repr
      && size > 0
      && ht.Length == size
      && (forall i :: 0 <= i < size ==> listValid(ht[i]))
      // what is repr?
      && (forall i, j, k :: 0 <= i < size && ht[i] != null && j == ht[i] && k in ht[i].nodes ==> k in repr)
      // disjointness causes issues
      //&& (forall i, j :: (0 <= i < size) && (0 <= j < size) && (i != j) && (tbl[i] != null) && (tbl[j] != null) ==>
      //          tbl[i] != tbl[j] && tbl[i].nodes !! tbl[j].nodes && tbl[i].elements !! tbl[j].elements)
      //&& disjoint(set i | 0 <= i < tbl.Length :: valueSetOfList(tbl[i]))
      && elements.Keys == keySet(ht)
      //&& elements.Values == valueSet(ht)
      // FIXME: adding this makes [insert] verification to time out.. but we need this for resizing
      // perhaps keep a ghost variable at every list? we'd then just need to read them
      //&& count == |valueSet(ht)|
      //&& count == valueSetLength(tbl)
      //&& count == |elements|
      && (forall e :: e in elements.Keys ==> ht[hash(e) % size] != null && e in ht[hash(e) % size].elements.Keys)
    }

    ghost predicate listValid(x: hashtablenode?<K,T>)
      reads {x}, if x != null then (set y | y in x.Repr()) else {}
    {
      (x == null) || x.Valid()
    }

    ghost function nodesOfList(x: hashtablenode?<K,T>): set<hashtablenode<K,T>>
      reads {x}, if x != null then (set y | y in x.nodes) else {}
    {
      if x == null then {} else x.nodes
    }

    opaque ghost function keySetOfList(x: hashtablenode?<K,T>): set<K>
      reads {x}, if x != null then x.nodes else {}
    {
      if x == null then {}
      else x.elements.Keys
    }
    opaque ghost function keySet(t: array<hashtablenode?<K,T>>): set<K>
      reads t, set x | x in t[..], set x, y | x in t[..] && x != null && y in x.nodes :: y
    {
      flatten(set i | 0 <= i < t.Length :: keySetOfList(t[i]))
    }

    opaque ghost function valueSetOfList(x: hashtablenode?<K,T>): set<T>
      reads {x}, if x != null then x.nodes else {}
    {
      if x == null then {}
      else x.elements.Values
    }
    opaque ghost function valueSet(t: array<hashtablenode?<K,T>>): set<T>
      reads t, set x | x in t[..], set x, y | x in t[..] && x != null && y in x.nodes :: y
    {
      flatten(set i | 0 <= i < t.Length :: valueSetOfList(t[i]))
    }

    constructor(h: hashfunction<K>, s: nat)
      requires s > 0
      ensures size == s && count == 0 && ht.Length == size && hash == h
      ensures fresh(ht)
      ensures Valid()
      ensures elements.Keys == {} && elements.Values == {}
      ensures repr == {}
    {
      reveal Valid();
      size := s;
      count := 0;
      hash := h;

      new;

      ht := new hashtablenode?<K,T>[size as int](i => null);

      repr := {};
      elements := map[];
      assert elements.Keys == {};
      assert elements.Values == {};
      reveal keySet();
      reveal keySetOfList();
      reveal valueSet();
      reveal valueSetOfList();
    }

  /*
    method resize()
      requires Valid()
      requires count > 0 && size > 0 && count == size
      ensures Valid()
      ensures count < size && size == old(size) * 2
      modifies ht[..], this`size, Repr
      ensures elements == old(elements)
      //ensures ht != old(ht)
      //ensures fresh(Repr - old(Repr))
      ensures Repr == old(Repr) - {old(ht)} + {ht}
    {
      var old_size := size;
      var old_ht := ht;
      ghost var old_elements := elements;

      size := size + size;
      assert size > 0 && count < size;
      ht := new hashtablenode?<T>[size as int](i => null);
      elements := {};
      Repr := Repr - {old_ht} + {ht};
      ghost var newRepr := Repr;

      assert this in Repr;
      assert ht in Repr;

      assert elements == valueSet(ht);

      var i := 0;
      while (i < old_ht.Length)
        //invariant Repr == newRepr
        invariant Valid()
      /*
        invariant this in Repr
        invariant ht in Repr
        invariant ht.Length == size
        invariant forall k :: 0 <= k < ht.Length ==> listValid(ht[k])
        invariant elements == valueSet(ht)
        //invariant Valid()
        invariant Repr == newRepr
        invariant count < size && size == old(size) * 2
        // the old hash table is still valid
        invariant old_ht.Length == old_size
        invariant (forall i :: 0 <= i < old_size ==> listValid(old_ht[i]))
        invariant old_elements == valueSet(old_ht)
        //invariant (forall e :: e in old_elements ==> old_ht[hash(e) % old_size] != null && e in old_ht[hash(e) % old_size].elements)
        // changes between elements
        invariant old_elements + elements == old(elements)
      */
        decreases old_ht.Length - i
      {
        /*
        //ghost var seenValues : set<T> := {};
        //ghost var values := valueSetOfList(old_ht[i]);
        //ghost var prevElements := elements;
        var np := old_ht[i];
        while (np != null)
          /*invariant count < size && size == old(size) * 2
          invariant seenValues + valueSetOfList(np) == values
          invariant elements == prevElements + seenValues
          invariant np == null || (np != null && np.Valid())
          invariant forall e :: e in seenValues ==> ht[hash(e) % size] != null && e in ht[hash(e) % size].elements
          */
          decreases if np == null then {} else np.nodes
        {
          //seenValues := seenValues + {np.data};
          var next := np.next;
          assert np.data !in elements;
          /*
          var data := np.data;
          var ph := hash(data);
          assert size > 0;
          var h := ph % size;
          if (ht[h] == null) {
            np.next := null;
            ht[h] := np;
          } else {
            np.next := ht[h];
            ht[h] := np;
          }*/
          insert_aux(np);

          //old_elements := old_elements - {np.data};
          //elements := elements + {np.data};

          np := next;
        }
        assert np == null;
        //assert seenValues == values;
        //assert elements == prevElements + values;
        */
        i := i + 1;
      }
    }
  */
  /*
    method resize_aux(chain: hashtablenode?<T>)
      requires Valid()
      requires chain != null ==> chain.Valid() && Repr !! chain.nodes
      requires valueSetOfList(chain) !! elements
      requires count + |valueSetOfList(chain)| < size
      ensures elements - old(valueSetOfList(chain)) == old(elements)
      //ensures chain != null ==> Repr - old(chain.nodes) == old(Repr)
      //ensures chain == null ==> Repr == old(Repr)
      //ensures count == old(count) + |elements| - |old(elements)|
      modifies Repr, if chain != null then chain.nodes else {}
    {
      var np := chain;
      ghost var seenValues : set<T> := {};
      ghost var seenNodes : set<hashtablenode<T>> := {};
      ghost var values : set<T> := valueSetOfList(chain);
      ghost var nodes : set<hashtablenode<T>> := if chain != null then chain.nodes else {};
      assert count + |values| < size;
      while (np != null)
        invariant Valid()
        invariant np != null ==> np.Valid() && Repr !! np.nodes && np in nodes && nodes <= old(chain.nodes)
        invariant valueSetOfList(np) !! elements
        invariant old(count) + |seenValues| < size && count == old(count) + |seenValues|
        //invariant count == old(count) + |seenValues| //count + |seenValues| < size
        invariant seenValues + valueSetOfList(np) == values
        invariant seenNodes + (if np != null then np.nodes else {}) == nodes
        invariant elements == old(elements) + seenValues
        invariant count == old(count) + |seenValues|
        decreases if np == null then {} else np.nodes
        invariant Repr == old(Repr) + seenNodes
      {
        seenValues := seenValues + {np.data};
        seenNodes := seenNodes + {np};

        var next := np.tail();
        assert np.data !in elements;
        np.next := null;
        insert_aux(np);

        np := next;
        assert np.Valid();
        assert seenValues + valueSetOfList(np) == values;
        assert count == old(count) + |seenValues|;
      }
      assume false;
      assert seenValues == values;
      assert seenNodes == nodes;
      assert elements == old(elements) + seenValues;
      //assert count == old(count) + |seenValues|;
      //assert Repr == old(Repr) + seenNodes;
      assert old(count) + |seenValues| < size && count == old(count) + |seenValues|;
    }
  */
    /* Insert a new record into the array.  Return TRUE if successful.
    ** Prior data with the same key is NOT overwritten */
    method insert(data: T, key: K)
      returns (success: bool)
      requires Valid()
      ensures Valid()
      ensures success ==> key !in old(elements.Keys) && elements == map[key:=data] + old(elements)
      ensures !success ==> key in old(elements.Keys) && elements == old(elements)
      ensures success ==> count == old(count) + 1
      ensures !success ==> count == old(count)
      ensures key in elements.Keys
      modifies this`repr, ht, ht[..], this`count, this`elements
      ensures ht == old(ht)
      ensures fresh(Repr() - old(Repr()))
      ensures old(Repr()) <= Repr()
    {
      var np := find(key);
      reveal Valid();
      if (np != null) {
        assert key in elements.Keys;
        return false;
      }
      not_found(key);
      assert key !in elements.Keys;

      /*
      if (count==size) {
          /* Need to make the hash table bigger */
          var arrSize := size * 2;
          var arr := new hashtablenode?<T>[arrSize];
          var i := 0;
          while (i < size)
              invariant 0 <= i <= size
              invariant forall k :: 0 <= k < i ==> arr[k] == ht[k]
          {
              arr[i] := ht[i];
              i := i + 1;
          }
      }*/

      /* Insert the new data */
      var node := new hashtablenode<K,T>(key, data);
      insert_aux(node);
      success := true;
    }

    method insert_aux(node: hashtablenode<K,T>)
      requires Valid()
      //requires count < size
      requires node.Valid()
      requires node !in repr
      requires node.key !in elements.Keys
      requires node.next == null
      ensures Valid()
      ensures node.data == old(node.data)
      ensures node.key == old(node.key)
      ensures elements == old(elements) + map[node.key:=node.data]
      modifies this`repr, ht, ht[..], this`count, node, this`elements
      ensures ht == old(ht)
      ensures repr == old(repr) + {node}
      ensures count == old(count) + 1
    {
      reveal keySet();
      reveal keySetOfList();
      reveal valueSetOfList();
      reveal Valid();
      /* Insert the new data */
      var ph := hash(node.key);
      var h := ph % size;

      ghost var oldKeySetOfList := keySet(ht) - keySetOfList(ht[h]);
      if (ht[h] == null) {
        ht[h] := node;
        assert keySetOfList(ht[h]) == {node.key};
        assert valueSetOfList(ht[h]) == {node.data};
        // to help proving that elements == valueSet()
        assert forall k :: 0 <= k < ht.Length && k != h ==> ht[k] == old(ht[k]);
      } else {
        ghost var t := keySetOfList(ht[h]);
        assert node !in ht[h].nodes;
        assert node.key !in t;
        node.insert_before(node.key, node.data, ht[h]);
        assert keySetOfList(node) - {node.key} == t;
        ht[h] := node;
        // to help proving that elements == valueSet()
        assert forall k :: 0 <= k < ht.Length && k != h ==> ht[k] == old(ht[k]);
      }
      assert listValid(ht[h]);

      repr := repr + {node};
      elements := elements + map[node.key:=node.data];
      count := count + 1;
      //assert |elements|==count;
      //assert this in Repr;
      assert node.key in elements.Keys;
      assert node.data in elements.Values;
      assert repr == old(repr) + {node};
    }

    lemma lf(i: int, j: int)
      requires i >= 0 && j > 0
      ensures 0 <= (i % j) < j
    {

    }

    lemma not_found(key: K)
      requires Valid()
      requires size > 0
      requires ht.Length == size
      requires key !in elements.Keys
      ensures key !in keySetOfList(ht[hash(key) % size])
    {
      reveal Valid();
      reveal keySet();
      reveal keySetOfList();
      reveal valueSet();
      reveal valueSetOfList();
      lf(hash(key), size);
      assert 0 <= hash(key) % size < ht.Length;
      assert key !in keySetOfList(ht[hash(key) % size]);
    }

    /* Return a pointer to data assigned to the given key.  Return NULL
    ** if no such key. */
    method find(key: K)
      returns (np: hashtablenode?<K,T>)
      requires Valid()
      ensures key in Model() <==> np != null && np.Valid() && np.key == key
      ensures key !in Model() <==> np == null
    {
      reveal Valid();
      reveal keySet();
      reveal keySetOfList();
      reveal valueSetOfList();
      var h := hash(key) % size;
      np := ht[h];
      ghost var seenKeys : set<K> := {};
      ghost var keys := keySetOfList(ht[h]);
      assert key !in seenKeys;
      assert forall v :: v in keys ==> v in elements.Keys;
      while (np != null)
        invariant seenKeys + keySetOfList(np) == keys
        invariant np == null || (np != null && np.Valid())
        decreases if np == null then {} else np.nodes
        invariant key !in seenKeys
      {
          if (np.key == key) {
            assert np != null;
            assert np.key in elements.Keys;
            return;
          }
          seenKeys := seenKeys + {np.key};
          np := np.next;
      }
      assert np == null;
      assert seenKeys == keys;
      assert key !in seenKeys;
      assert key !in elements.Keys;
    }
  }
}

module HashMapTest {
  import HashMap

  function strhash_loop(x: string, i: int, acc: nat): nat
    requires 0 <= i <= |x|
    decreases |x| - i
  {
    if (i < |x|) then strhash_loop(x, i+1, acc * 13 + x[i] as int)
    else acc
  }
  function strhash(x: string): nat
  {
    strhash_loop(x, 0, 0)
  }

  method {:test} test() {
      var s := new HashMap.hashtable<string,int>(i => strhash(i), 1024);
      reveal s.Valid();
      assert s.elements == map[] && s.repr == {};
      var r := s.insert(0, "x");
      assert r == true;
      assert s.Valid();
      r := s.insert(1, "x");
      assert r == false;
      assert s.elements == map["x":=0];
      r := s.insert(1, "y");
      assert r == true;
      assert s.elements == map["x":=0,"y":=1];
  }
}
