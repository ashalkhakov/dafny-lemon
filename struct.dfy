/*
** Principal data structures for the LEMON parser generator.
*/

include "footprint.dfy"
include "hashset.dfy"
include "hashmap.dfy"

datatype option<T> = None | Some(T)

/* Symbols (terminals and nonterminals) of the grammar are stored
** in the following: */
datatype symbol_type =
| TERMINAL()
| NONTERMINAL()
| MULTITERMINAL()

datatype e_assoc =
| LEFT()
| RIGHT()
| NONE()
| UNK()

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

class LTable {

  var strings: HashSet.hashtable<string>
  var symbols: HashMap.hashtable<string, symbol>

  constructor()
    ensures Valid()
  {
    reveal Valid();
    strings := new HashSet.hashtable<string>(i => strhash(i), 1024);
    symbols := new HashMap.hashtable<string,symbol>(i => strhash(i), 64);
  }

  opaque ghost predicate Valid()
    reads this, Repr()
    ensures Valid() ==> strings.Valid() && symbols.Valid()
  {
    && assert strings.Repr() <= Repr();true
    && assert symbols.Repr() <= Repr();true
    && symbols.Repr() !! strings.Repr()
    && strings.Valid()
    && symbols.Valid()
    // TODO: how to ensure this?
    //&& forall s, v :: s in symbols.Model() && v == symbols.Model()[s] ==> v.Valid()
  }

  ghost function Repr(): set<object>
    reads this, strings, strings.Repr(), symbols, symbols.Repr()
  {
    {strings} + strings.Repr() + {symbols} + symbols.Repr() + symbols.elements.Values
  }

  ghost function Model(): int
    reads this, Repr()
    requires Valid()
  {
    0
  }

  /* Routines for handling a strings */

  /* Insert a new record into the array.  Return TRUE if successful.
  ** Prior data with the same key is NOT overwritten */
  method {:rlimit 100000000} Strsafe_insert(s: string)
    returns (success: bool)
    requires Valid()
    modifies strings, Repr(), strings.InsertRepr()
    ensures Valid()
  {
    reveal Valid();
    success := strings.insert(s);
    assert fresh(strings.Repr() - old(strings.Repr()));
    assert unchanged(symbols);
    assert Valid();
  }

  /* Return a pointer to data assigned to the given key.  Return NULL
  ** if no such key. */
  method Strsafe_find(s: string)
    returns (r: option<string>)
    requires Valid()
    ensures Valid()
  {
    var np := strings.find(s);
    if (np != null) {
      r := Some(np.data);
    } else {
      r := None;
    }
  }

  /* Routines for handling symbols of the grammar */

  /* Compare two symbols for sorting purposes.  Return negative,
  ** zero, or positive if a is less then, equal to, or greater
  ** than b.
  **
  ** Symbols that begin with upper case letters (terminals or tokens)
  ** must sort before symbols that begin with lower case letters
  ** (non-terminals).  And MULTITERMINAL symbols (created using the
  ** %token_class directive) must sort at the very end. Other than
  ** that, the order does not matter.
  **
  ** We find experimentally that leaving the symbols in their original
  ** order (the order they appeared in the grammar file) gives the
  ** smallest parser tables in SQLite.
  */
  static function Symbolcmpp(a: symbol, b: symbol): int
    reads a, b
    requires a.Valid() && b.Valid()
  {
    reveal a.Valid();
    reveal b.Valid();
    var i1 := if a.symtype.MULTITERMINAL? then 3 else if a.name[0]>'Z' then 2 else 1;
    var i2 := if b.symtype.MULTITERMINAL? then 3 else if b.name[0]>'Z' then 2 else 1;

    if i1==i2 then a.index - b.index else i1 - i2
  }

  method {:rlimit 100000000} Symbol_insert(data: symbol, key: string)
    returns (success: bool)
    requires data.Valid()
    requires Valid()
    modifies symbols, Repr(), symbols.InsertRepr()
    ensures Valid()
  {
    reveal Valid();
    success := symbols.insert(data, key);
    assert fresh(symbols.Repr() - old(symbols.Repr()));
    assert unchanged(strings);
    assert Valid();
  }

  /* Return a pointer to data assigned to the given key.  Return NULL
  ** if no such key. */
  method Symbol_find(key: string)
    returns (r: symbol?)
    requires Valid()
    ensures Valid()
    ensures key in symbols.Model() ==> r != null /*&& r.Valid() && r.name == key*/
    ensures key !in symbols.Model() ==> r == null
  {
    reveal Valid();
    var np := symbols.find(key);
    if (np != null) {
      assert np.key in symbols.Model();
      //assert np.data != null && np.data.Valid();
      //assert np.data.Valid();
      r := np.data;
    } else {
      r := null;
    }
  }

  /* Return the n-th data.  Return NULL if n is out of range. */
  /*method Symbol_Nth(n: int): symbol
  {
    struct symbol *data;
    if( x2a && n>0 && n<=x2a->count ){
      data = x2a->tbl[n-1].data;
    }else{
      data = 0;
    }
    return data;
  }*/

  /* Return the size of the array */
  /*function Symbol_count(): int
  {
    symbols.count
  }*/


/*
struct symbol *Symbol_new(const char *);
struct symbol *Symbol_Nth(int);
int Symbol_count(void);
struct symbol **Symbol_arrayof(void);

/* Routines to manage the state table */

int Configcmp(const char *, const char *);
struct state *State_new(void);
void State_init(void);
int State_insert(struct state *, struct config *);
struct state *State_find(struct config *);
struct state **State_arrayof(void);

/* Routines used for efficiency in Configlist_add */

void Configtable_init(void);
int Configtable_insert(struct config *);
struct config *Configtable_find(struct config *);
void Configtable_clear(int(*)(struct config *));
*/
}


class symbol {
  var name: string        /* Name of the symbol */
  var index: int               /* Index number for this symbol */
  var symtype: symbol_type   /* Symbols are all either TERMINALS or NTs */
/*
  var rule: rule       /* Linked list of rules of this (if an NT) */
  var fallback: symbol /* fallback token in case this token doesn't parse */
  var prec: int                /* Precedence if defined (-1 otherwise) */
  var associ: e_assoc      /* Associativity if precedence is defined */
  var firstset: string          /* First-set for all rules of this symbol */
  var lambda: bool          /* True if NT and can generate an empty string */
  var useCnt: int              /* Number of times used */
  var destructor: string        /* Code which executes whenever this symbol is
                           ** popped from the stack during error processing */
  var destLineno: int          /* Line number for start of destructor.  Set to
                           ** -1 for duplicate destructors. */
  var dataType: string          /* The data type of information held by this
                           ** object. Only used if type==NONTERMINAL */
  var dtnum: int               /* The data type number.  In the parser, the value
                           ** stack is a union.  The .yy%d element of this
                           ** union is the correct data type for this object */
  var bContent: bool            /* True if this symbol ever carries content - if
                           ** it is ever more than just syntax */
  /* The following fields are used by MULTITERMINALs only */
  var nsubsym: int             /* Number of constituent symbols in the MULTI */
  var subsym: array<symbol>  /* Array of constituent symbols */
*/

  constructor(n: string, i: int)
    requires |n|>0 && i>=0
    ensures Valid()
    ensures this.name == n && this.index == i
  {
    reveal Valid();
    this.name := n;
    this.index := i;
  }

  opaque ghost predicate Valid()
    reads this
  {
    |name| > 0 && index >= 0
  }
}
/*
/* Each production rule in the grammar is stored in the following
** structure.  */
class rule {
  var lhs: symbol      /* Left-hand side of the rule */
  var lhsalias: string    /* Alias for the LHS (NULL if none) */
  var lhsStart: bool            /* True if left-hand side is the start symbol */
  var ruleline: int            /* Line number for the rule */
  var nrhs: int                /* Number of RHS symbols */
  var rhs: array<symbol>     /* The RHS symbols */
  var rhsalias: array<string>   /* An alias for each RHS symbol (NULL if none) */
  var line: int                /* Line number at which code begins */
  var code: string        /* The code executed when this rule is reduced */
  var codePrefix: string  /* Setup code before code[] above */
  var codeSuffix: string  /* Breakdown code after code[] above */
  var precsym: symbol  /* Precedence symbol for this rule */
  var index: int               /* An index number for this rule */
  var iRule: int               /* Rule number as used in the generated tables */
  var noCode: bool          /* True if this rule has no associated C code */
  var codeEmitted: bool     /* True if the code has been emitted already */
  var canReduce: bool       /* True if this rule is ever reduced */
  var doesReduce: bool      /* Reduce actions occur after optimization */
  var neverReduce: bool     /* Reduce is theoretically possible, but prevented
                           ** by actions or other outside implementation */
  var nextlhs: rule    /* Next rule with the same LHS */
  var next: rule       /* Next rule in the global list */
}
*/
/* A configuration is a production rule of the grammar together with
** a mark (dot) showing how much of that rule has been processed so far.
** Configurations also contain a follow-set which is a list of terminal
** symbols which are allowed to immediately follow the end of the rule.
** Every configuration is recorded as an instance of the following: */
datatype cfgstatus =
| COMPLETE()
| INCOMPLETE()

class config {
  /*
  var rp: rule         /* The rule upon which the configuration is based */
  var dot: int                 /* The parse point */
  var fws: string               /* Follow-set for this configuration only */
  var fplp: plink      /* Follow-set forward propagation links */
  var bplp: plink      /* Follow-set backwards propagation links */
  var stp: state       /* Pointer to state which contains this */
  */
  var status: cfgstatus   /* used during followset and shift computations */
  /*
  var next: config     /* Next configuration in the state */
  var bp: config       /* The next basis configuration */
  */
}

/*

datatype e_action =
| SHIFT()
| ACCEPT()
| REDUCE()
| ERROR()
| SSCONFLICT()              /* A shift/shift conflict */
| SRCONFLICT()              /* Was a reduce, but part of a conflict */
| RRCONFLICT()              /* Was a reduce, but part of a conflict */
| SH_RESOLVED()             /* Was a shift.  Precedence resolved conflict */
| RD_RESOLVED()             /* Was reduce.  Precedence resolved conflict */
| NOT_USED()                /* Deleted by compression */
| SHIFTREDUCE()              /* Shift first, then reduce */

/* Every shift or reduce operation is stored as one of the following */
class action {
  var sp: symbol       /* The look-ahead symbol */
  var atype: e_action
  
  var stp: state     /* The new state, if a shift */
  var rp: rule       /* The rule, if a reduce */
  
  var spOpt: symbol    /* SHIFTREDUCE optimization to this symbol */
  var next: action     /* Next action for this state */
  var collide: action  /* Next action with the same hash */
}

/* Each state of the generated parser's finite state machine
** is encoded as an instance of the following structure. */
class state {
  var bp: config       /* The basis configurations for this state */
  var cfgp: config      /* All configurations in this set */
  var statenum: int            /* Sequential number for this state */
  var ap: action       /* List of actions for this state */
  var nTknAct: int
  var nNtAct: int     /* Number of actions on terminals and nonterminals */
  var iTknOfst: int
  var iNtOfst: int   /* yy_action[] offset for terminals and nonterms */
  var iDfltReduce: int         /* Default action is to REDUCE by this rule */
  var pDfltReduce: rule /* The default REDUCE rule. */
  var autoReduce: bool          /* True if this is an auto-reduce state */
}
const NO_OFFSET := -2147483647

*/

class LPlink {
  var freelist: plink?

  ghost var spine: seq<plink>
  ghost function Repr(): set<object>
    reads this
  {
    set x | x in spine
  }

  ghost predicate Valid()
    reads this, Repr()
  {
    && (forall i | 0 <= i < |spine| :: spine[i].cfp == null)
    && (forall i | 0 <= i < |spine|-1 :: spine[i].next == spine[i+1])
    && (if freelist == null
          then spine == []
          else  spine != [] && spine[0] == freelist && spine[|spine|-1].next == null)
    && (forall i: nat, j:nat :: i < |spine| && j < |spine| && i != j ==> spine[i] != spine[j])
  }

  ghost function Model(): seq<plink>
    reads this, Repr()
    requires Valid()
  {
    spine
  }

  constructor()
    ensures Valid()
    ensures Model() == []
  {
    freelist := null;
    spine := [];
  }

  lemma LastHasLastIndex(last: plink)
    requires last.next == null && last in Repr() && Valid()
    ensures spine[|spine|-1] == last
  {
    var i :| 0 <= i < |spine| && spine[i] == last;
    assert i != |spine|-1 ==> last.next == spine[i].next == spine[i+1] != null;
  }

  /* Allocate and add a plink to a plink list */
  method Plink_add(plpp: plink, cfp: config)
    returns (plpp1: plink)
    requires plpp.Valid()
    requires plpp.Repr() !! Repr()
    requires Valid()
    ensures Valid()
    ensures plpp1.Valid()
    modifies this, Repr()
  {
    if (freelist == null) {
      var i: int;
      var amt := 100;

      i := 0;
      freelist := new plink.empty();
      spine := [freelist];
      while (i < amt-1)
        invariant |spine|==i+1
        invariant 0 <= i <= amt-1
        invariant forall k :: 0 <= k <= i ==> spine[k].cfp == null
        invariant freelist == spine[0]
        invariant spine[|spine|-1].next == null
        invariant forall k :: 0 <= k < i ==> spine[k].next == spine[k+1]
        invariant fresh(Repr() - old(Repr()))
        invariant (forall i: nat, j:nat :: i < |spine| && j < |spine| && i != j ==> spine[i] != spine[j])
      {
        var list1 := new plink.empty();
        list1.next := freelist;
        spine := [list1] + spine;
        freelist := list1;
        i := i + 1;
      }
      assert fresh(Repr() - old(Repr()));
      assert Valid();
    }

    var newlink := freelist;
    freelist := freelist.next;
    if (freelist == null) {
      spine := [];
    } else {
      spine := spine[1..];
    }
    assert newlink !in plpp.Repr();
    newlink.insert_before(cfp, plpp);
    plpp1 := newlink;
  }

  lemma head_disjoint(from: plink, nt: plink)
    requires nt.Repr() !! from.Repr()
    requires nt.Valid() && from.Valid()
    decreases nt.nodes
    ensures forall n :: n in from.Repr() ==> n !in nt.Repr()
  {
    if (nt.next != null) {
      head_disjoint(from, nt.next);
    }
  }

  /* Transfer every plink on the list "from" to the list "to" */
  method Plink_copy(t: plink, from: plink)
    returns (nt : plink)
    modifies from, from.Repr(), from.list
    requires t.Valid() && from.Valid()
    requires t.Repr() !! from.Repr()
  {
    nt := t;
    var fr := from;

    while (fr != null)
      decreases if fr != null then fr.nodes else {}
      invariant fr == null || (fr != null && fr.Valid() && fr.nodes <= old(from.nodes))
      invariant fr != null ==> fr.Repr() !! nt.Repr()
      invariant unchanged(this)
      invariant unchanged(t.Repr())
      invariant nt.Valid()
    {
      var nextpl := fr.tail();
      fr.insert_before(fr.cfp, nt);
      nt := fr;
      fr := nextpl;
    }
  }

  /* Delete every plink on the list */
  method Plink_delete(plp: plink)
    modifies plp, plp.Repr(), plp.list, this, freelist, spine
    requires plp.Valid()
    requires Valid()
    ensures Valid()
  {
    var nextpl: plink?;
    var p := plp;

    assert Valid();
    while (p != null)
      decreases if p == null then {} else p.nodes
      invariant p != null ==> p.Valid()
      invariant Valid()
    {
      nextpl := p.tail();
      p.cfp := null;
      p.next := freelist;
      freelist := p;
      spine := [p] + spine;
      p := nextpl;
    }
  }
}

/* A followset propagation link indicates that the contents of one
** configuration followset should be propagated to another whenever
** the first changes. */
class plink {
  var cfp: config?      /* The configuration to which linked */
  var next: plink?      /* The next propagate link */

  // abstract variable storing (in the same order) the list of elements 
  // in the sequence headed by 'this'
  ghost var list: seq<config>

  // Heap frame, 
  // Consists of the set of nodes in the list headed by 'this'
  ghost var nodes: set<plink>

  ghost function Repr(): set<object>
    reads this
  {
    nodes
  }

  ghost predicate Free()
    reads this
  {
    && cfp == null
    && next == null
    && nodes == {}
    && list == []
  }

  // The invariant predicate provides a definition of 'list' and 'nodes'
  // by induction of the length of the list
  ghost predicate Valid()
    decreases nodes
    reads this, nodes
  {
     // this in nodes &&      
     && cfp != null
     && (next == null ==> nodes == {this} 
                          && list == [cfp]
        )
     && (next != null ==> next in nodes 
                          && nodes == {this} + next.nodes
                          && this !in next.nodes // acyclity condition
                          && list == [cfp] + next.list
                          && next.Valid()
        )
  }

  ghost function Model(): set<config>
    reads this, Repr()
    requires Valid()
  {
    set x | x in list
  }

  constructor empty()
    ensures Free()
  {
    this.cfp := null;
    this.next := null;
    this.nodes := {};
    this.list := [];
  }

  // Makes 'this' the head of a sigleton list containg element 'e'
  constructor singleton(e: config)
    ensures Valid()
    ensures list == [e]
  {
    cfp := e;
    next := null;

    list := [e];
    nodes := {this};
  }

  // Makes 'this' the head of a non-sigleton list containg element 'e' 
  // and continuing with the list headed by 'n'
  method insert_before(e: config, n: plink)
    modifies this
    requires n.Valid()
    requires this !in n.nodes
    ensures Valid()
    ensures list == [e] + n.list
    ensures nodes == {this} + n.nodes
  {
    cfp := e;
    next := n;

    list := [e] + n.list;
    nodes := {this} + n.nodes;
  }

  // Returns the (possibly empty) tail of the list headed by 'this'
  method tail() returns (t: plink?)
    requires Valid()
    ensures Valid()
    ensures t != null ==> t.Valid()
                          && t.nodes == nodes - {this}
                          && t.list == list[1..]
  {
    t := next;
  }
}

/*

/* The state vector for the entire parser generator is recorded as
** follows.  (LEMON uses no global variables and makes little use of
** static variables.  Fields in the following structure can be thought
** of as begin global variables in the program.) */
class lemon {
  var sorted: array<state>   /* Table of states sorted by state number */
  var rule: rule       /* List of all rules */
  var startRule: rule  /* First rule */
  var nstate: int              /* Number of states */
  var nxstate: int             /* nstate with tail degenerate states removed */
  var nrule: int               /* Number of rules */
  var nruleWithAction: int     /* Number of rules with actions */
  var nsymbol: int             /* Number of terminal and nonterminal symbols */
  var nterminal: int           /* Number of terminal symbols */
  var minShiftReduce: int      /* Minimum shift-reduce action value */
  var errAction: int           /* Error action value */
  var accAction: int           /* Accept action value */
  var noAction: int            /* No-op action value */
  var minReduce: int           /* Minimum reduce action */
  var maxAction: int           /* Maximum action value of any kind */
  var symbols: array<symbol> /* Sorted array of pointers to symbols */
  var errorcnt: int            /* Number of errors */
  var errsym: symbol   /* The error symbol */
  var wildcard: symbol /* Token that matches anything */
  var name: string              /* Name of the generated parser */
  var arg: string               /* Declaration of the 3rd argument to parser */
  var ctx: string               /* Declaration of 2nd argument to constructor */
  var tokentype: string         /* Type of terminal symbols in the parser stack */
  var vartype: string           /* The default type of non-terminal symbols */
  var start: string             /* Name of the start symbol for the grammar */
  var stacksize: string         /* Size of the parser stack */
  var includeCode: string           /* Code to put at the start of the C file */
  var error: string             /* Code to execute when an error is seen */
  var overflow: string          /* Code to execute on a stack overflow */
  var failure: string           /* Code to execute on parser failure */
  var accept: string            /* Code to execute when the parser excepts */
  var extracode: string         /* Code appended to the generated file */
  var tokendest: string         /* Code to execute to destroy token data */
  var vardest: string           /* Code for the default non-terminal destructor */
  var filename: string          /* Name of the input file */
  var outname: string           /* Name of the current output file */
  var tokenprefix: string       /* A prefix added to token names in the .h file */
  var nconflict: int           /* Number of parsing conflicts */
  var nactiontab: int          /* Number of entries in the yy_action[] table */
  var nlookaheadtab: int       /* Number of entries in yy_lookahead[] */
  var tablesize: int           /* Total table size of all tables in bytes */
  var basisflag: int           /* Print only basis configurations */
  var printPreprocessed: int   /* Show preprocessor output on stdout */
  var has_fallback: int        /* True if any %fallback is seen in the grammar */
  var nolinenosflag: int       /* True if #line statements should not be printed */
  var argv0: string             /* Name of the program */
}
*/