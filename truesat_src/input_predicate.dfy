include "int32.dfy"

module InputPredicate {
  import SYInt32

  function countLiterals(clauses : seq<seq<SYInt32.t>>) : int
  {
    if |clauses| == 0 then 0
    else |clauses[|clauses|-1]| + countLiterals(clauses[..|clauses|-1])
  }

  predicate checkClauses(variablesCount: SYInt32.t, clauses : seq<seq<SYInt32.t>>) {
    countLiterals(clauses) < SYInt32.max as int &&
    forall clause :: (clause in clauses) ==>
      0 < |clause| < SYInt32.max as int &&
      forall literal :: (literal in clause) ==> (
        (literal < 0 && 0 < -literal <= variablesCount) ||
        (literal > 0 && 0 < literal <= variablesCount))
  }
  
  predicate sortedClauses(clauses : seq<seq<SYInt32.t>>) {
    forall clause :: (clause in clauses) ==>
      forall x, y :: 0 <= x < y < |clause| ==>
        clause[x] < clause[y]
  }

  predicate valid(input : (SYInt32.t, seq<seq<SYInt32.t>>)) {
    (0 < input.0 < SYInt32.max as SYInt32.t) &&

    (0 < |input.1| <= SYInt32.max as int) &&

    checkClauses(input.0, input.1) &&

    sortedClauses(input.1)
  }
}
