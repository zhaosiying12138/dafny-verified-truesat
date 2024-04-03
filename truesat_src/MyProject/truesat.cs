// Dafny program truesat.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.6.0.0
// Command Line Options: /compileTarget:cs /compileVerbose:1 /spillTargetCode:1 /compile:2 /unicodeChar:0 truesat.dfy file_input.cs
// truesat.dfy

method Main(_noArgsParameter: seq<seq<char>>)
{
  var starttime := Input.getTimestamp();
  var input := Input.getInput();
  var totalTime: real := (Input.getTimestamp() - starttime) as real / 1000.0;
  print ""c Time to read: "", totalTime, ""s\n"";
  match input {
    case {:split false} Error(m) =>
      print ""c Error: "", m, ""\n"";
    case {:split false} Just(z) =>
      var (variablesCount, clauses) := z;
      starttime := Input.getTimestamp();
      var formula := new Formula(variablesCount, clauses);
      var solver := new SATSolver(formula);
      totalTime := (Input.getTimestamp() - starttime) as real / 1000.0;
      print ""c Time to initialize: "", totalTime, ""s\n"";
      starttime := Input.getTimestamp();
      var solution := solver.start();
      totalTime := (Input.getTimestamp() - starttime) as real / 1000.0;
      print ""c Time to solve: "", totalTime, ""s\n"";
      match solution {
        case {:split false} SAT(x) =>
          print ""s SATISFIABLE\n"";
        case {:split false} UNSAT() =>
          print ""s UNSATISFIABLE\n"";
      }
  }
}

module InputPredicate {
  function countLiterals(clauses: seq<seq<SYInt32.t>>): int
    decreases clauses
  {
    if |clauses| == 0 then
      0
    else
      |clauses[|clauses| - 1]| + countLiterals(clauses[..|clauses| - 1])
  }

  predicate checkClauses(variablesCount: SYInt32.t, clauses: seq<seq<SYInt32.t>>)
    decreases variablesCount, clauses
  {
    countLiterals(clauses) < SYInt32.max as int &&
    forall clause: seq<SYInt32.t> {:trigger |clause|} {:trigger clause in clauses} :: 
      (clause in clauses ==>
        0 < |clause|) &&
      (clause in clauses ==>
        |clause| < SYInt32.max as int) &&
      (clause in clauses ==>
        forall literal: SYInt32.t {:trigger literal in clause} :: 
          literal in clause ==>
            (literal < 0 && 0 < -literal <= variablesCount) || (literal > 0 && 0 < literal <= variablesCount))
  }

  predicate sortedClauses(clauses: seq<seq<SYInt32.t>>)
    decreases clauses
  {
    forall clause: seq<SYInt32.t> {:trigger |clause|} {:trigger clause in clauses} :: 
      clause in clauses ==>
        forall x: int, y: int {:trigger clause[y], clause[x]} :: 
          0 <= x < y < |clause| ==>
            clause[x] < clause[y]
  }

  predicate valid(input: (SYInt32.t, seq<seq<SYInt32.t>>))
    decreases input
  {
    0 < input.0 < SYInt32.max as SYInt32.t &&
    0 < |input.1| <= SYInt32.max as int &&
    checkClauses(input.0, input.1) &&
    sortedClauses(input.1)
  }

  import SYInt32
}

module SYInt32 {
  const max: int := 2000000
  const min: int := -2000000

  ghost method test(x: t)
    decreases x
  {
    ghost var m1: t := -x;
  }

  newtype {:nativeType ""int""} t = x: int
    | -2000000 <= x < 2000001
}

module MyDatatypes {
  datatype Maybe<T> = Error(string) | Just(value: T)
}

module Input {
  method getInput() returns (result: Maybe<(SYInt32.t, seq<seq<SYInt32.t>>)>)
    ensures result.Just? ==> InputPredicate.valid(result.value)
  {
    var input := FileInput.Reader.getContent();
    if 0 < |input| < SYInt32.max as int {
      var parser := new Parser(input);
      var x := parser.parse();
      return x;
    } else {
      return Error(""the file contains more data than SYInt32.max"");
    }
  }

  function getTimestamp(): int
  {
    FileInput.Reader.getTimestamp()
  }

  import SYInt32

  import opened Useless

  import FileInput

  import opened MyDatatypes

  import InputPredicate
}

module {:extern ""FileInput""} FileInput {
  class {:extern ""Reader""} Reader {
    static function {:extern ""getContent""} getContent(): seq<char>

    static function {:extern ""getTimestamp""} getTimestamp(): int
  }
}

module Useless {
  predicate valid'(c: seq<char>)
    decreases c
  {
    0 < |c| < SYInt32.max as int
  }

  import opened MyDatatypes

  import SYInt32

  import InputPredicate

  class Parser {
    var content: seq<char>
    var contentLength: SYInt32.t
    var cursor: SYInt32.t

    constructor (c: seq<char>)
      requires valid'(c)
      ensures valid()
      decreases c
    {
      content := c;
      contentLength := |c| as SYInt32.t;
      cursor := 0;
    }

    predicate valid()
      reads `content, `contentLength, `cursor
      decreases {this, this, this}
    {
      valid'(content) &&
      contentLength as int == |content| &&
      0 <= cursor <= contentLength
    }

    method skipLine()
      requires valid()
      modifies `cursor
      ensures valid()
      ensures old(cursor) <= cursor
    {
      while cursor < contentLength && content[cursor] != '\n'
        invariant 0 <= cursor <= contentLength
        decreases contentLength as int - cursor as int, if cursor < contentLength then if content[cursor] <= '\n' then '\n' as int - content[cursor] as int else content[cursor] as int - '\n' as int else 0 - 1
      {
        cursor := cursor + 1;
      }
      if cursor < contentLength {
        cursor := cursor + 1;
      }
    }

    method toNextNumber()
      requires valid()
      modifies `cursor
      ensures valid()
      ensures old(cursor) <= cursor
      ensures cursor < contentLength ==> content[cursor] == '-' || '0' <= content[cursor] <= '9'
    {
      while cursor < contentLength && !('0' <= content[cursor] <= '9' || content[cursor] == '-')
        invariant 0 <= cursor <= contentLength
        decreases contentLength as int - cursor as int, if cursor < contentLength && !('0' <= content[cursor] <= '9') then if content[cursor] <= '-' then '-' as int - content[cursor] as int else content[cursor] as int - '-' as int else 0 - 1
      {
        cursor := cursor + 1;
      }
    }

    method extractNumber() returns (res: Maybe<SYInt32.t>)
      requires valid()
      requires cursor < contentLength ==> content[cursor] == '-' || '0' <= content[cursor] <= '9'
      modifies `cursor
      ensures valid()
      ensures old(cursor) <= cursor
      ensures res.Just? ==> old(cursor) < cursor
    {
      var number: SYInt32.t := 0;
      var isNegative: bool := false;
      if cursor < contentLength && content[cursor] == '-' {
        isNegative := true;
        cursor := cursor + 1;
      }
      if cursor == contentLength {
        return Error(""There is no number around here."");
      }
      while cursor < contentLength && '0' <= content[cursor] <= '9'
        invariant 0 <= cursor <= contentLength
        invariant 0 <= number <= SYInt32.max as SYInt32.t
        decreases contentLength as int - cursor as int
      {
        var digit: SYInt32.t := content[cursor] as SYInt32.t - '0' as SYInt32.t;
        if number <= (SYInt32.max as SYInt32.t - digit) / 10 {
          assert 0 <= (SYInt32.max as SYInt32.t - digit) / 10 - number;
          number := number * 10 + digit;
        } else {
          return Error(""There is a number bigger than SYInt32.max"");
        }
        cursor := cursor + 1;
      }
      if isNegative {
        number := -number;
      }
      return Just(number);
    }

    method parse() returns (result: Maybe<(SYInt32.t, seq<seq<SYInt32.t>>)>)
      requires valid()
      modifies `cursor
      ensures result.Just? ==> InputPredicate.valid(result.value)
    {
      var variablesCount: SYInt32.t := 0;
      var clausesCount: SYInt32.t := 0;
      var clauses: seq<seq<SYInt32.t>> := [];
      var clause: array<SYInt32.t> := new SYInt32.t[1000];
      var clauseLength: SYInt32.t := 0;
      var ok := false;
      var literalsCount: SYInt32.t := 0;
      var contentLength: SYInt32.t := |content| as SYInt32.t;
      while cursor < contentLength
        invariant 0 <= cursor <= contentLength
        invariant InputPredicate.checkClauses(variablesCount, clauses)
        invariant InputPredicate.sortedClauses(clauses)
        invariant clause.Length <= SYInt32.max as int
        invariant forall z: SYInt32.t {:trigger clause[z]} :: 0 <= z < clauseLength ==> (clause[z] < 0 && 0 < -clause[z] <= variablesCount) || (clause[z] > 0 && 0 < clause[z] <= variablesCount)
        invariant forall x: SYInt32.t, y: SYInt32.t {:trigger clause[y], clause[x]} :: 0 <= x < y < clauseLength ==> clause[x] < clause[y]
        invariant ok ==> 0 < variablesCount < SYInt32.max as SYInt32.t
        invariant InputPredicate.countLiterals(clauses) == literalsCount as int
        decreases contentLength - cursor
        modifies `cursor, clause
      {
        var oldCursor := cursor;
        if content[cursor] == 'c' {
          skipLine();
        } else if content[cursor] == 'p' && variablesCount == 0 {
          toNextNumber();
          var x := extractNumber();
          match x {
            case {:split false} Error(t) =>
              {
                return Error(t);
              }
            case {:split false} Just(number) =>
              {
                if 0 < number < SYInt32.max as SYInt32.t {
                  variablesCount := number;
                  ok := true;
                } else {
                  return Error(""Variables count is bigger than SYInt32.max"");
                }
              }
          }
          toNextNumber();
          x := extractNumber();
          match x {
            case {:split false} Error(t) =>
              {
                return Error(t);
              }
            case {:split false} Just(number) =>
              {
                clausesCount := number;
              }
          }
          skipLine();
        } else if content[cursor] == 'p' {
          return Error(""Twice p? what are you doing?"");
        } else if ok {
          toNextNumber();
          if clauseLength == 0 && cursor == contentLength {
            break;
          }
          var x := extractNumber();
          match x {
            case {:split false} Error(t) =>
              {
                return Error(t);
              }
            case {:split false} Just(number) =>
              {
                if number == 0 && clauseLength > 0 {
                  clauses := clauses + [clause[..clauseLength]];
                  if SYInt32.max as SYInt32.t - clauseLength > literalsCount {
                    literalsCount := literalsCount + clauseLength;
                  } else {
                    return Error(""The number of literals is to big"");
                  }
                  clauseLength := 0;
                } else if number != 0 {
                  if clauseLength < 1000 {
                    if (number < 0 && 0 < -number <= variablesCount) || (number > 0 && 0 < number <= variablesCount) {
                      clause[clauseLength] := number;
                      clauseLength := clauseLength + 1;
                      var k: SYInt32.t := clauseLength - 1;
                      while 0 < k && clause[k - 1] > clause[k]
                        invariant 0 <= k <= clauseLength
                        invariant forall z: SYInt32.t {:trigger clause[z]} :: 0 <= z < clauseLength ==> (clause[z] < 0 && 0 < -clause[z] <= variablesCount) || (clause[z] > 0 && 0 < clause[z] <= variablesCount)
                        invariant forall x: SYInt32.t, y: SYInt32.t {:trigger clause[y], clause[x]} :: 0 <= x < y < clauseLength && x != k && y != k ==> clause[x] < clause[y]
                        invariant forall x: SYInt32.t, y: SYInt32.t {:trigger clause[y], clause[x]} :: k <= x < y < clauseLength ==> clause[x] < clause[y]
                        decreases k
                        modifies clause
                      {
                        var aux := clause[k];
                        clause[k] := clause[k - 1];
                        clause[k - 1] := aux;
                        k := k - 1;
                      }
                      if k > 0 && clause[k - 1] == clause[k] {
                        return Error(""duplice literal in clause"");
                      }
                    } else {
                      return Error(""literal bigger than variablesCount"");
                    }
                  } else {
                    return Error(""clause longer than 1000"");
                  }
                }
              }
          }
        }
        if cursor < contentLength && oldCursor == cursor {
          cursor := cursor + 1;
        }
      }
      if !(0 < |clauses| < SYInt32.max as int) {
        return Error(""number of clauses incorrect"");
      }
      if |clauses| != clausesCount as int {
        return Error(""different number of clauses"");
      }
      if ok {
        return Just((variablesCount, clauses));
      } else {
        return Error(""p not found"");
      }
    }
  }
}

datatype SAT_UNSAT = SAT(tau: seq<SYInt32.t>) | UNSAT

class SATSolver {
  var formula: Formula

  constructor (f': Formula)
    requires f'.valid()
    ensures formula == f'
    ensures formula.valid()
    decreases f'
  {
    formula := f';
  }

  method step(literal: SYInt32.t, value: bool) returns (result: SAT_UNSAT)
    requires formula.valid()
    requires formula.decisionLevel < formula.variablesCount - 1
    requires formula.decisionLevel > -1 ==> formula.traceDLStart[formula.decisionLevel] < formula.traceDLEnd[formula.decisionLevel]
    requires !formula.hasEmptyClause()
    requires !formula.isEmpty()
    requires formula.validLiteral(literal)
    requires formula.getLiteralValue(formula.truthAssignment[..], literal) == -1
    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue, formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel, formula`assignmentsTrace, formula.trueLiteralsCount, formula.falseLiteralsCount
    ensures formula.valid()
    ensures !formula.hasEmptyClause()
    ensures old(formula.decisionLevel) == formula.decisionLevel
    ensures old(formula.assignmentsTrace) == formula.assignmentsTrace
    ensures forall i: SYInt32.t {:trigger formula.getDecisionLevel(i)} {:trigger old(formula.getDecisionLevel(i))} :: 0 <= i <= formula.decisionLevel ==> old(formula.getDecisionLevel(i)) == formula.getDecisionLevel(i)
    ensures formula.decisionLevel > -1 ==> formula.traceDLStart[formula.decisionLevel] < formula.traceDLEnd[formula.decisionLevel]
    ensures !formula.isEmpty()
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau)
    ensures result.SAT? ==> var (variable: SYInt32.t, val: SYInt32.t) := formula.convertLVtoVI(literal, value); formula.isSatisfiableExtend(formula.truthAssignment[..][variable as int := val])
    ensures result.SAT? ==> formula.isSatisfiableTruthAssignment(old(formula.truthAssignment[..]), result.tau)
    ensures result.UNSAT? ==> var (variable: SYInt32.t, val: SYInt32.t) := formula.convertLVtoVI(literal, value); !formula.isSatisfiableExtend(formula.truthAssignment[..][variable as int := val])
    ensures formula.countUnsetVariables(formula.truthAssignment[..]) == formula.countUnsetVariables(old(formula.truthAssignment[..]))
    decreases formula.countUnsetVariables(formula.truthAssignment[..]), 0
  {
    formula.increaseDecisionLevel();
    formula.setLiteral(literal, value);
    result := solve();
    formula.revertLastDecisionLevel();
    if formula.truthAssignment[..] != old(formula.truthAssignment[..]) {
      ghost var i: SYInt32.t :| 0 <= i as int < formula.truthAssignment.Length && formula.truthAssignment[i] != old(formula.truthAssignment[i]);
      ghost var y: (SYInt32.t, bool) := (i, formula.convertIntToBool(old(formula.truthAssignment[i])));
      assert false;
    }
    return result;
  }

  method solve() returns (result: SAT_UNSAT)
    requires formula.valid()
    requires formula.decisionLevel > -1 ==> formula.traceDLStart[formula.decisionLevel] < formula.traceDLEnd[formula.decisionLevel]
    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue, formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel, formula`assignmentsTrace, formula.trueLiteralsCount, formula.falseLiteralsCount
    ensures formula.valid()
    ensures old(formula.decisionLevel) == formula.decisionLevel
    ensures old(formula.assignmentsTrace) == formula.assignmentsTrace
    ensures forall i: SYInt32.t {:trigger formula.getDecisionLevel(i)} {:trigger old(formula.getDecisionLevel(i))} :: 0 <= i <= formula.decisionLevel ==> old(formula.getDecisionLevel(i)) == formula.getDecisionLevel(i)
    ensures formula.decisionLevel > -1 ==> formula.traceDLStart[formula.decisionLevel] < formula.traceDLEnd[formula.decisionLevel]
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau)
    ensures result.SAT? ==> formula.isSatisfiableExtend(formula.truthAssignment[..])
    ensures result.SAT? ==> formula.isSatisfiableTruthAssignment(old(formula.truthAssignment[..]), result.tau)
    ensures result.UNSAT? ==> !formula.isSatisfiableExtend(formula.truthAssignment[..])
    ensures formula.countUnsetVariables(formula.truthAssignment[..]) == formula.countUnsetVariables(old(formula.truthAssignment[..]))
    decreases formula.countUnsetVariables(formula.truthAssignment[..]), 1
  {
    var hasEmptyClause: bool := formula.getHasEmptyClause();
    if hasEmptyClause {
      formula.hasEmptyClause_notSatisfiable();
      return UNSAT;
    }
    var isEmpty: bool := formula.getIsEmpty();
    if isEmpty {
      formula.isEmpty_sastisfied();
      result := SAT(formula.truthAssignment[..]);
      assert formula.validValuesTruthAssignment(result.tau);
      return result;
    }
    var literal := formula.chooseLiteral();
    formula.notEmptyNoEmptyClauses_traceNotFull();
    result := step(literal, true);
    if result.SAT? {
      return result;
    }
    result := step(literal, false);
    if result.UNSAT? {
      ghost var variable := formula.getVariableFromLiteral(literal);
      formula.forVariableNotSatisfiableExtend_notSatisfiableExtend(formula.truthAssignment[..], variable);
    }
    return result;
  }

  method start() returns (result: SAT_UNSAT)
    requires formula.valid()
    requires formula.decisionLevel == -1
    modifies formula.truthAssignment, formula.traceVariable, formula.traceValue, formula.traceDLStart, formula.traceDLEnd, formula`decisionLevel, formula`assignmentsTrace, formula.trueLiteralsCount, formula.falseLiteralsCount
    ensures formula.valid()
    ensures result.SAT? ==> formula.validValuesTruthAssignment(result.tau)
    ensures result.SAT? ==> formula.isSatisfiableExtend(old(formula.truthAssignment[..]))
    ensures result.SAT? ==> formula.isSatisfiableTruthAssignment(old(formula.truthAssignment[..]), result.tau)
    ensures result.UNSAT? ==> !formula.isSatisfiableExtend(old(formula.truthAssignment[..]))
  {
    formula.level0UnitPropagation();
    result := solve();
  }
}

class Formula extends DataStructures {
  constructor (variablesCount: SYInt32.t, clauses: seq<seq<SYInt32.t>>)
    requires InputPredicate.valid((variablesCount, clauses))
    ensures valid()
    ensures this.variablesCount == variablesCount
    ensures this.clauses == clauses
    ensures fresh(this.traceVariable) && fresh(this.traceValue) && fresh(this.traceDLStart) && fresh(this.traceDLEnd) && fresh(this.clauseLength) && fresh(this.trueLiteralsCount) && fresh(this.falseLiteralsCount) && fresh(this.positiveLiteralsToClauses) && fresh(this.negativeLiteralsToClauses) && fresh(this.truthAssignment)
    ensures this.decisionLevel == -1
    decreases variablesCount, clauses
  {
    assert 0 < variablesCount < SYInt32.max as SYInt32.t;
    assert 0 < |clauses| <= SYInt32.max as int;
    assert forall clause: seq<SYInt32.t> {:trigger clause in clauses} :: clause in clauses ==> forall literal: SYInt32.t {:trigger literal in clause} :: literal in clause ==> (literal < 0 && 0 < -literal <= variablesCount) || (literal > 0 && 0 < literal <= variablesCount);
    this.variablesCount := variablesCount;
    this.clauses := clauses;
    this.decisionLevel := -1;
    this.traceVariable := new SYInt32.t[variablesCount];
    this.traceValue := new bool[variablesCount];
    this.traceDLStart := new SYInt32.t[variablesCount];
    this.traceDLEnd := new SYInt32.t[variablesCount];
    this.assignmentsTrace := {};
    var clsLength := |clauses| as SYInt32.t;
    this.clausesCount := clsLength;
    this.clauseLength := new SYInt32.t[clsLength];
    this.trueLiteralsCount := new SYInt32.t[clsLength];
    this.falseLiteralsCount := new SYInt32.t[clsLength];
    this.positiveLiteralsToClauses := new seq<SYInt32.t>[variablesCount];
    this.negativeLiteralsToClauses := new seq<SYInt32.t>[variablesCount];
    this.truthAssignment := new SYInt32.t[variablesCount];
    new;
    var k: SYInt32.t := 0;
    while k < this.clausesCount
      invariant this.clauseLength.Length == this.clausesCount as int
      invariant forall i: SYInt32.t {:trigger clauses[i]} {:trigger this.clauseLength[i]} :: 0 <= i < k <= this.clausesCount ==> this.clauseLength[i] as int == |clauses[i]|
      invariant 0 <= k <= this.clausesCount
      decreases this.clausesCount as int - k as int
      modifies this.clauseLength
    {
      this.clauseLength[k] := |this.clauses[k]| as SYInt32.t;
      k := k + 1;
    }
    var index: SYInt32.t := 0;
    while index < variablesCount
      invariant 0 <= index <= variablesCount
      invariant forall j: SYInt32.t {:trigger truthAssignment[j]} :: 0 <= j < index ==> truthAssignment[j] == -1
      invariant forall j: SYInt32.t {:trigger (j, true)} {:trigger (j, false)} {:trigger truthAssignment[j]} :: (0 <= j < index && truthAssignment[j] == -1 ==> (j, false) !in assignmentsTrace) && (0 <= j < index && truthAssignment[j] == -1 ==> (j, true) !in assignmentsTrace)
      decreases variablesCount as int - index as int
      modifies truthAssignment
    {
      truthAssignment[index] := -1;
      assert (index, true) !in assignmentsTrace;
      assert (index, false) !in assignmentsTrace;
      index := index + 1;
    }
    this.createTFLArrays();
    this.createPositiveLiteralsToClauses();
    this.createNegativeLiteralsToClauses();
    inputPredicate_countLiterals(clausesCount);
    assert clauses == clauses[..clausesCount];
    assert countLiterals(clausesCount) == InputPredicate.countLiterals(clauses);
  }

  lemma /*{:_induction this, cI}*/ inputPredicate_countLiterals(cI: SYInt32.t)
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= cI <= clausesCount
    ensures countLiterals(cI) == InputPredicate.countLiterals(clauses[..cI])
    decreases cI
  {
    if cI == 0 {
    } else {
      inputPredicate_countLiterals(cI - 1);
      ghost var cl := clauses[..cI];
      assert clauses[..cI - 1] == cl[..cI - 1];
      assert countLiterals(cI - 1) == InputPredicate.countLiterals(cl[..cI - 1]);
      assert countLiterals(cI) == countLiterals(cI - 1) + |clauses[cI - 1]|;
      assert cI as int == |clauses[..cI]|;
      assert InputPredicate.countLiterals(cl) == InputPredicate.countLiterals(cl[..cI - 1]) + |cl[cI - 1]|;
    }
  }

  method createTFLArrays()
    requires validReferences()
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires validTruthAssignment()
    requires validClauses()
    requires trueLiteralsCount.Length == |clauses|
    requires falseLiteralsCount.Length == |clauses|
    requires forall value: int {:trigger truthAssignment[value]} :: 0 <= value < truthAssignment.Length ==> truthAssignment[value] == -1
    modifies trueLiteralsCount, falseLiteralsCount
    ensures validTrueLiteralsCount(truthAssignment[..])
    ensures validFalseLiteralsCount(truthAssignment[..])
  {
    var i: SYInt32.t := 0;
    while i < clausesCount
      invariant 0 <= i <= clausesCount
      invariant forall j: SYInt32.t {:trigger clauses[j]} {:trigger trueLiteralsCount[j]} :: 0 <= j < i ==> trueLiteralsCount[j] == countTrueLiterals(truthAssignment[..], clauses[j])
      invariant forall j: SYInt32.t {:trigger clauses[j]} {:trigger falseLiteralsCount[j]} :: 0 <= j < i ==> falseLiteralsCount[j] == countFalseLiterals(truthAssignment[..], clauses[j])
      decreases clausesCount - i
    {
      prop_countTrueLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      trueLiteralsCount[i] := 0;
      prop_countFalseLiterals_initialTruthAssignment(truthAssignment[..], clauses[i]);
      falseLiteralsCount[i] := 0;
      i := i + 1;
    }
  }

  method createPositiveLiteralsToClauses()
    requires validReferences()
    requires validVariablesCount()
    requires validClauses()
    requires positiveLiteralsToClauses.Length == variablesCount as int
    modifies positiveLiteralsToClauses
    ensures validPositiveLiteralsToClauses()
  {
    var variable := 0;
    while variable < variablesCount
      invariant 0 <= variable <= variablesCount
      invariant forall v: SYInt32.t {:trigger positiveLiteralsToClauses[v]} :: 0 <= v < variable ==> validPositiveLiteralToClause(v, positiveLiteralsToClauses[v])
      invariant forall v: SYInt32.t {:trigger positiveLiteralsToClauses[v]} :: 0 <= v < variable ==> |positiveLiteralsToClauses[v]| <= clausesCount as int
      decreases variablesCount - variable
    {
      positiveLiteralsToClauses[variable] := [];
      var clauseIndex: SYInt32.t := 0;
      while clauseIndex < clausesCount
        invariant 0 <= clauseIndex <= clausesCount
        invariant forall v: SYInt32.t {:trigger positiveLiteralsToClauses[v]} :: 0 <= v < variable ==> validPositiveLiteralToClause(v, positiveLiteralsToClauses[v])
        invariant forall v: SYInt32.t {:trigger positiveLiteralsToClauses[v]} :: 0 <= v < variable ==> |positiveLiteralsToClauses[v]| <= clausesCount as int
        invariant |positiveLiteralsToClauses[variable]| <= clauseIndex as int
        invariant Utils.valuesBoundedBy(positiveLiteralsToClauses[variable], 0, |clauses|)
        invariant |positiveLiteralsToClauses[variable]| > 0 ==> positiveLiteralsToClauses[variable][|positiveLiteralsToClauses[variable]| - 1] < clauseIndex
        invariant Utils.orderedAsc(positiveLiteralsToClauses[variable])
        invariant forall cI: SYInt32.t {:trigger clauses[cI]} {:trigger cI in positiveLiteralsToClauses[variable]} :: cI in positiveLiteralsToClauses[variable] ==> variable + 1 in clauses[cI]
        invariant forall cI: SYInt32.t {:trigger clauses[cI]} {:trigger cI in positiveLiteralsToClauses[variable]} :: 0 <= cI < clauseIndex ==> cI !in positiveLiteralsToClauses[variable] ==> variable + 1 !in clauses[cI]
        decreases clausesCount - clauseIndex
      {
        if variable + 1 in clauses[clauseIndex] {
          positiveLiteralsToClauses[variable] := positiveLiteralsToClauses[variable] + [clauseIndex];
        }
        clauseIndex := clauseIndex + 1;
      }
      variable := variable + 1;
    }
  }

  method createNegativeLiteralsToClauses()
    requires validReferences()
    requires validVariablesCount()
    requires validClauses()
    requires negativeLiteralsToClauses.Length == variablesCount as int
    modifies negativeLiteralsToClauses
    ensures validNegativeLiteralsToClauses()
  {
    var variable: SYInt32.t := 0;
    while variable < variablesCount
      invariant 0 <= variable <= variablesCount
      invariant forall v: SYInt32.t {:trigger negativeLiteralsToClauses[v]} :: 0 <= v < variable ==> validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])
      invariant forall v: SYInt32.t {:trigger negativeLiteralsToClauses[v]} :: 0 <= v < variable ==> |negativeLiteralsToClauses[v]| <= clausesCount as int
      decreases variablesCount - variable
    {
      negativeLiteralsToClauses[variable] := [];
      var clauseIndex: SYInt32.t := 0;
      while clauseIndex < clausesCount
        invariant 0 <= clauseIndex <= clausesCount
        invariant forall v: SYInt32.t {:trigger negativeLiteralsToClauses[v]} :: 0 <= v < variable ==> validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])
        invariant forall v: SYInt32.t {:trigger negativeLiteralsToClauses[v]} :: 0 <= v < variable ==> |negativeLiteralsToClauses[v]| <= clausesCount as int
        invariant |negativeLiteralsToClauses[variable]| <= clauseIndex as int
        invariant Utils.valuesBoundedBy(negativeLiteralsToClauses[variable], 0, |clauses|)
        invariant |negativeLiteralsToClauses[variable]| > 0 ==> negativeLiteralsToClauses[variable][|negativeLiteralsToClauses[variable]| - 1] < clauseIndex
        invariant Utils.orderedAsc(negativeLiteralsToClauses[variable])
        invariant forall cI: SYInt32.t {:trigger clauses[cI]} {:trigger cI in negativeLiteralsToClauses[variable]} :: cI in negativeLiteralsToClauses[variable] ==> -variable - 1 in clauses[cI]
        invariant forall cI: SYInt32.t {:trigger clauses[cI]} {:trigger cI in negativeLiteralsToClauses[variable]} :: 0 <= cI < clauseIndex ==> cI !in negativeLiteralsToClauses[variable] ==> -variable - 1 !in clauses[cI]
        decreases |clauses| - clauseIndex as int
      {
        if -variable - 1 in clauses[clauseIndex] {
          negativeLiteralsToClauses[variable] := negativeLiteralsToClauses[variable] + [clauseIndex];
        }
        clauseIndex := clauseIndex + 1;
      }
      variable := variable + 1;
    }
  }

  method revertLastDecisionLevel()
    requires valid()
    requires 0 <= decisionLevel
    modifies `assignmentsTrace, `decisionLevel, truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLEnd
    ensures decisionLevel == old(decisionLevel) - 1
    ensures assignmentsTrace == old(assignmentsTrace) - old(getDecisionLevel(decisionLevel))
    ensures valid()
    ensures forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i <= decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures decisionLevel > -1 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
  {
    ghost var k: SYInt32.t := traceDLEnd[decisionLevel] - 1;
    while traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
      invariant traceDLStart[decisionLevel] - 1 <= k < traceDLEnd[decisionLevel]
      invariant k == traceDLEnd[decisionLevel] - 1
      invariant valid()
      invariant forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
      decreases traceDLEnd[decisionLevel] as int - traceDLStart[decisionLevel] as int
      modifies `assignmentsTrace, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount
    {
      removeLastVariable();
      k := k - 1;
    }
    decisionLevel := decisionLevel - 1;
    assert old(traceVariable[..]) == traceVariable[..];
  }

  method removeLastVariable()
    requires valid()
    requires 0 <= decisionLevel < variablesCount
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    modifies `assignmentsTrace, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount
    ensures traceDLEnd[decisionLevel] == old(traceDLEnd[decisionLevel]) - 1
    ensures valid()
    ensures forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
  {
    forall_validAssignmentTrace_traceDLEndStrictlyOrdered();
    var k: SYInt32.t := traceDLEnd[decisionLevel] - 1;
    var variable := traceVariable[k];
    var value := traceValue[k];
    assignmentsTrace := assignmentsTrace - {(variable, value)};
    traceDLEnd[decisionLevel] := k;
    ghost var previousTau := truthAssignment[..];
    truthAssignment[variable] := -1;
    ghost var newTau := truthAssignment[..];
    assert forall i: SYInt32.t {:trigger old(traceDLStart[i])} {:trigger traceDLStart[i]} {:trigger old(traceDLEnd[i])} {:trigger traceDLEnd[i]} :: (0 <= i < decisionLevel ==> traceDLEnd[i] == old(traceDLEnd[i])) && (0 <= i < decisionLevel ==> traceDLStart[i] == old(traceDLStart[i]));
    assert traceVariable[..traceDLEnd[decisionLevel]] == old(traceVariable[..traceDLEnd[decisionLevel] - 1]);
    assert forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i);
    var positivelyImpactedClauses: seq<SYInt32.t> := positiveLiteralsToClauses[variable];
    var negativelyImpactedClauses: seq<SYInt32.t> := negativeLiteralsToClauses[variable];
    if !value {
      negativelyImpactedClauses := positiveLiteralsToClauses[variable];
      positivelyImpactedClauses := negativeLiteralsToClauses[variable];
    }
    assert Utils.valuesBoundedBy(positivelyImpactedClauses, 0, |clauses|);
    assert Utils.valuesBoundedBy(negativelyImpactedClauses, 0, |clauses|);
    undoImpactedClauses_TFSArraysModified(previousTau, newTau, variable, positivelyImpactedClauses, negativelyImpactedClauses);
    var i: SYInt32.t := 0;
    var len := |positivelyImpactedClauses| as SYInt32.t;
    while i < len
      invariant len as int == |positivelyImpactedClauses|
      invariant 0 <= i <= len
      invariant forall i': SYInt32.t {:trigger clauses[i']} {:trigger trueLiteralsCount[i']} {:trigger i' in positivelyImpactedClauses} :: 0 <= i' < clausesCount && i' !in positivelyImpactedClauses ==> trueLiteralsCount[i'] == countTrueLiterals(newTau, clauses[i'])
      invariant forall i': SYInt32.t {:trigger positivelyImpactedClauses[i']} :: 0 <= i' < i ==> trueLiteralsCount[positivelyImpactedClauses[i']] == countTrueLiterals(newTau, clauses[positivelyImpactedClauses[i']])
      invariant forall i': SYInt32.t {:trigger positivelyImpactedClauses[i']} :: i <= i' < len ==> trueLiteralsCount[positivelyImpactedClauses[i']] == countTrueLiterals(previousTau, clauses[positivelyImpactedClauses[i']])
      decreases len as int - i as int
      modifies trueLiteralsCount
    {
      var clauseIndex := positivelyImpactedClauses[i];
      ghost var clause := clauses[clauseIndex];
      assert validClause(clause);
      unsetVariable_countTrueLiteralsLessThanLength(newTau, variable, clauses[clauseIndex]);
      unsetVariable_countTrueLiteralsDecreasesWithOne(previousTau, newTau, variable, clause);
      trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] - 1;
      i := i + 1;
    }
    assert trueLiteralsCount.Length == |clauses|;
    forall i: SYInt32.t | 0 <= i as int < |clauses|
      ensures trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i])
    {
      if i !in positivelyImpactedClauses {
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      } else {
        ghost var j: SYInt32.t :| 0 <= j as int < |positivelyImpactedClauses| && positivelyImpactedClauses[j] == i;
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    i := 0;
    len := |negativelyImpactedClauses| as SYInt32.t;
    modify falseLiteralsCount {
      while i < len
        invariant 0 <= i <= len
        invariant forall i': SYInt32.t {:trigger negativelyImpactedClauses[i']} :: 0 <= i' < i ==> falseLiteralsCount[negativelyImpactedClauses[i']] == countFalseLiterals(newTau, clauses[negativelyImpactedClauses[i']])
        invariant forall i': SYInt32.t {:trigger negativelyImpactedClauses[i']} :: i <= i' < len ==> falseLiteralsCount[negativelyImpactedClauses[i']] == countFalseLiterals(previousTau, clauses[negativelyImpactedClauses[i']])
        invariant forall i': SYInt32.t {:trigger clauses[i']} {:trigger falseLiteralsCount[i']} {:trigger i' in negativelyImpactedClauses} :: 0 <= i' < clausesCount && i' !in negativelyImpactedClauses ==> falseLiteralsCount[i'] == countFalseLiterals(newTau, clauses[i'])
        invariant forall i': SYInt32.t {:trigger clauses[i']} {:trigger trueLiteralsCount[i']} {:trigger i' in positivelyImpactedClauses} :: 0 <= i' < clausesCount && i' !in positivelyImpactedClauses ==> trueLiteralsCount[i'] == countTrueLiterals(newTau, clauses[i'])
        invariant forall i': int {:trigger positivelyImpactedClauses[i']} :: 0 <= i' < |positivelyImpactedClauses| ==> trueLiteralsCount[positivelyImpactedClauses[i']] == countTrueLiterals(newTau, clauses[positivelyImpactedClauses[i']])
        invariant validTrueLiteralsCount(truthAssignment[..])
        decreases len - i
        modifies falseLiteralsCount
      {
        var clauseIndex := negativelyImpactedClauses[i];
        unsetVariable_countFalseLiteralsLessThanLength(newTau, variable, clauses[clauseIndex]);
        unsetVariable_countFalseLiteralsDecreasesWithOne(previousTau, newTau, variable, clauses[clauseIndex]);
        falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] - 1;
        i := i + 1;
      }
    }
    assert falseLiteralsCount.Length == |clauses|;
    forall i: SYInt32.t | 0 <= i as int < |clauses|
      ensures falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i])
    {
      if i !in negativelyImpactedClauses {
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      } else {
        ghost var j: SYInt32.t :| 0 <= j as int < |negativelyImpactedClauses| && negativelyImpactedClauses[j] == i;
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    assert old(traceVariable[..]) == traceVariable[..];
  }

  method setVariable(variable: SYInt32.t, value: bool)
    requires valid()
    requires validVariable(variable)
    requires truthAssignment[variable] == -1
    requires 0 <= decisionLevel
    modifies truthAssignment, traceVariable, traceValue, traceDLEnd, `assignmentsTrace, trueLiteralsCount, falseLiteralsCount
    ensures valid()
    ensures value == false ==> old(truthAssignment[..])[variable as int := 0] == truthAssignment[..]
    ensures value == true ==> old(truthAssignment[..])[variable as int := 1] == truthAssignment[..]
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures traceVariable[traceDLEnd[decisionLevel] - 1] == variable
    ensures traceValue[traceDLEnd[decisionLevel] - 1] == value
    ensures forall i: SYInt32.t {:trigger old(traceDLEnd[i])} {:trigger traceDLEnd[i]} :: 0 <= i < variablesCount && i != decisionLevel ==> traceDLEnd[i] == old(traceDLEnd[i])
    ensures forall i: SYInt32.t {:trigger old(traceValue[i])} {:trigger traceValue[i]} {:trigger old(traceVariable[i])} {:trigger traceVariable[i]} :: (0 <= i < variablesCount && i != old(traceDLEnd[decisionLevel]) ==> traceVariable[i] == old(traceVariable[i])) && (0 <= i < variablesCount && i != old(traceDLEnd[decisionLevel]) ==> traceValue[i] == old(traceValue[i]))
    ensures forall x: SYInt32.t {:trigger old(traceVariable[x])} {:trigger traceVariable[x]} :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
    ensures forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures assignmentsTrace == old(assignmentsTrace) + {(variable, value)}
    ensures countUnsetVariables(truthAssignment[..]) + 1 == old(countUnsetVariables(truthAssignment[..]))
    decreases variable, value
  {
    ghost var oldTau: seq<SYInt32.t> := truthAssignment[..];
    existsUnsetLiteral_traceNotFull(variable);
    addAssignment(variable, value);
    if value {
      truthAssignment[variable] := 1;
    } else {
      truthAssignment[variable] := 0;
    }
    assert validTruthAssignment();
    ghost var newTau := truthAssignment[..];
    ghost var trueLiteral := variable + 1;
    ghost var falseLiteral := -variable - 1;
    if !value {
      trueLiteral := -variable - 1;
      falseLiteral := variable + 1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    var i: SYInt32.t := 0;
    var impactedClauses := positiveLiteralsToClauses[variable];
    var impactedClauses' := negativeLiteralsToClauses[variable];
    if !value {
      impactedClauses := negativeLiteralsToClauses[variable];
      impactedClauses' := positiveLiteralsToClauses[variable];
    }
    clausesNotImpacted_TFArraysSame(oldTau, newTau, variable, impactedClauses, impactedClauses');
    var impactedClausesLen: SYInt32.t := |impactedClauses| as SYInt32.t;
    while i < impactedClausesLen
      invariant 0 <= i <= impactedClausesLen
      invariant forall j: SYInt32.t {:trigger clauses[j]} {:trigger trueLiteralsCount[j]} {:trigger j in impactedClauses} :: 0 <= j < clausesCount && j !in impactedClauses ==> trueLiteralsCount[j] == countTrueLiterals(newTau, clauses[j])
      invariant forall j: SYInt32.t {:trigger impactedClauses[j]} :: 0 <= j < i ==> trueLiteralsCount[impactedClauses[j]] == countTrueLiterals(newTau, clauses[impactedClauses[j]])
      invariant forall j: SYInt32.t {:trigger impactedClauses[j]} :: i <= j < impactedClausesLen ==> trueLiteralsCount[impactedClauses[j]] == countTrueLiterals(oldTau, clauses[impactedClauses[j]])
      decreases impactedClausesLen - i
      modifies trueLiteralsCount
    {
      var clauseIndex := impactedClauses[i];
      unsetVariable_countTrueLiteralsLessThanLength(oldTau, variable, clauses[clauseIndex]);
      setVariable_countTrueLiteralsIncreasesWithOne(oldTau, newTau, variable, clauses[clauseIndex]);
      trueLiteralsCount[clauseIndex] := trueLiteralsCount[clauseIndex] + 1;
      assert trueLiteral in clauses[clauseIndex] && getLiteralValue(newTau, trueLiteral) == 1;
      assert isClauseSatisfied(newTau, clauseIndex);
      i := i + 1;
    }
    assert trueLiteralsCount.Length == |clauses|;
    forall i: SYInt32.t | 0 <= i as int < |clauses|
      ensures trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i])
    {
      if i !in impactedClauses {
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      } else {
        ghost var j: SYInt32.t :| 0 <= j as int < |impactedClauses| && impactedClauses[j] == i;
        assert trueLiteralsCount[i] == countTrueLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    assert validTrueLiteralsCount(truthAssignment[..]);
    var i': SYInt32.t := 0;
    var impactedClausesLen': SYInt32.t := |impactedClauses'| as SYInt32.t;
    while i' < impactedClausesLen'
      invariant 0 <= i' <= impactedClausesLen'
      invariant forall j: SYInt32.t {:trigger clauses[j]} {:trigger falseLiteralsCount[j]} {:trigger j in impactedClauses'} :: 0 <= j < clausesCount && j !in impactedClauses' ==> falseLiteralsCount[j] == countFalseLiterals(newTau, clauses[j])
      invariant forall j: SYInt32.t {:trigger impactedClauses'[j]} :: 0 <= j < i' ==> falseLiteralsCount[impactedClauses'[j]] == countFalseLiterals(newTau, clauses[impactedClauses'[j]])
      invariant forall j: SYInt32.t {:trigger impactedClauses'[j]} :: i' <= j < impactedClausesLen' ==> falseLiteralsCount[impactedClauses'[j]] == countFalseLiterals(oldTau, clauses[impactedClauses'[j]])
      decreases impactedClausesLen' - i'
      modifies falseLiteralsCount
    {
      var clauseIndex := impactedClauses'[i'];
      unsetVariable_countFalseLiteralsLessThanLength(oldTau, variable, clauses[clauseIndex]);
      setVariable_countFalseLiteralsIncreasesWithOne(oldTau, newTau, variable, clauses[clauseIndex]);
      falseLiteralsCount[clauseIndex] := falseLiteralsCount[clauseIndex] + 1;
      i' := i' + 1;
    }
    assert falseLiteralsCount.Length == |clauses|;
    forall i: SYInt32.t | 0 <= i as int < |clauses|
      ensures falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i])
    {
      if i !in impactedClauses {
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      } else {
        ghost var j: SYInt32.t :| 0 <= j as int < |impactedClauses| && impactedClauses[j] == i;
        assert falseLiteralsCount[i] == countFalseLiterals(newTau, clauses[i]);
      }
    }
    assert newTau == truthAssignment[..];
    assert validFalseLiteralsCount(truthAssignment[..]);
    variableSet_countUnsetVariablesLessThanLength(newTau, variable);
    setVariable_unsetVariablesDecreasesWithOne(oldTau, newTau, variable);
  }

  lemma /*{:_induction this}*/ traceFull_variableInTrace(variable: SYInt32.t)
    requires valid()
    requires validVariable(variable)
    requires 0 <= decisionLevel
    requires traceDLEnd[decisionLevel] == variablesCount
    ensures exists i: SYInt32.t {:trigger traceVariable[i]} :: 0 <= i < traceDLEnd[decisionLevel] && traceVariable[i] == variable
    decreases variable
  {
    ghost var L: set<SYInt32.t>, R: set<SYInt32.t> := {}, Utils.RangeSet(0, variablesCount);
    ghost var i: SYInt32.t := 0;
    Utils.CardinalityRangeSet(0, variablesCount);
    while i < variablesCount
      invariant 0 <= i <= variablesCount
      invariant L == set j: SYInt32.t {:trigger traceVariable[j]} | 0 <= j < i :: traceVariable[j]
      invariant forall v: SYInt32.t {:trigger v in R} {:trigger v in L} :: 0 <= v < variablesCount ==> v in L || v in R
      invariant |R| == (variablesCount - i) as int
      decreases variablesCount - i
    {
      L, R := L + {traceVariable[i]}, R - {traceVariable[i]};
      i := i + 1;
    }
    assert variable in L;
  }

  lemma /*{:_induction this}*/ existsUnsetLiteral_traceNotFull(variable: SYInt32.t)
    requires valid()
    requires validVariable(variable)
    requires truthAssignment[variable] == -1
    requires 0 <= decisionLevel
    ensures traceDLEnd[decisionLevel] < variablesCount
    ensures forall x: (SYInt32.t, bool) {:trigger x.0} {:trigger x in assignmentsTrace} :: x in assignmentsTrace ==> x.0 != variable
    decreases variable
  {
    if traceDLEnd[decisionLevel] == variablesCount {
      traceFull_variableInTrace(variable);
      ghost var i :| 0 <= i < traceDLEnd[decisionLevel] && traceVariable[i] == variable;
      assert (traceVariable[i], traceValue[i]) in assignmentsTrace;
      assert traceVariable[i] == variable;
      assert traceValue[i] == false || traceValue[i] || true;
      assert (variable, true) in assignmentsTrace || (variable, false) in assignmentsTrace;
      assert truthAssignment[variable] == -1 ==> (variable, false) !in assignmentsTrace && (variable, true) !in assignmentsTrace;
      assert false;
    }
    if exists x: (SYInt32.t, bool) {:trigger x.0} {:trigger x in assignmentsTrace} :: x in assignmentsTrace && x.0 == variable {
      ghost var x :| x in assignmentsTrace && x.0 == variable;
      var (a, b) := x;
      assert a == variable;
      assert b == true || b == false;
      assert (variable, false) !in assignmentsTrace && (variable, true) !in assignmentsTrace;
      assert false;
    }
  }

  method addAssignment(variable: SYInt32.t, value: bool)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires 0 <= decisionLevel
    requires 0 <= variable < variablesCount
    requires forall x: (SYInt32.t, bool) {:trigger x.0} {:trigger x in assignmentsTrace} :: x in assignmentsTrace ==> x.0 != variable
    requires traceDLEnd[decisionLevel] < variablesCount
    modifies `assignmentsTrace, traceDLEnd, traceVariable, traceValue
    ensures traceDLEnd[decisionLevel] == old(traceDLEnd[decisionLevel]) + 1
    ensures traceVariable[traceDLEnd[decisionLevel] - 1] == variable
    ensures traceValue[traceDLEnd[decisionLevel] - 1] == value
    ensures forall i: SYInt32.t {:trigger old(traceDLEnd[i])} {:trigger traceDLEnd[i]} :: 0 <= i < variablesCount && i != decisionLevel ==> traceDLEnd[i] == old(traceDLEnd[i])
    ensures forall i: SYInt32.t {:trigger old(traceValue[i])} {:trigger traceValue[i]} {:trigger old(traceVariable[i])} {:trigger traceVariable[i]} :: (0 <= i < variablesCount && i != old(traceDLEnd[decisionLevel]) ==> traceVariable[i] == old(traceVariable[i])) && (0 <= i < variablesCount && i != old(traceDLEnd[decisionLevel]) ==> traceValue[i] == old(traceValue[i]))
    ensures assignmentsTrace == old(assignmentsTrace) + {(variable, value)}
    ensures validAssignmentTrace()
    ensures forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    decreases variable, value
  {
    traceVariable[traceDLEnd[decisionLevel]] := variable;
    traceValue[traceDLEnd[decisionLevel]] := value;
    assignmentsTrace := assignmentsTrace + {(variable, value)};
    traceDLEnd[decisionLevel] := traceDLEnd[decisionLevel] + 1;
    forall_validAssignmentTrace_traceDLEndStrictlyOrdered();
  }

  lemma /*{:_induction this}*/ forall_validAssignmentTrace_traceDLStartStrictlyOrdered()
    requires 0 <= decisionLevel
    requires decisionLevel as int < traceDLStart.Length
    requires decisionLevel as int < traceDLEnd.Length
    ensures validVariablesCount() && validAssignmentTrace() ==> forall i: SYInt32.t, j: SYInt32.t {:trigger traceDLStart[j], traceDLStart[i]} :: 0 <= i < j <= decisionLevel ==> traceDLStart[i] < traceDLStart[j]
  {
    if validVariablesCount() && validAssignmentTrace() {
      forall i: SYInt32.t, j: SYInt32.t | 0 <= i < j <= decisionLevel
        ensures traceDLStart[i] < traceDLStart[j]
      {
        validAssignmentTrace_traceDLStartStrictlyOrdered(i, j);
      }
    }
  }

  lemma /*{:_induction this}*/ validAssignmentTrace_traceDLStartStrictlyOrdered(i: SYInt32.t, j: SYInt32.t)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires 0 <= i < j <= decisionLevel
    ensures traceDLStart[i] < traceDLStart[j]
    decreases decisionLevel - i
  {
    if i == j - 1 {
    } else if i < j - 1 {
      validAssignmentTrace_traceDLStartStrictlyOrdered(i + 1, j);
    }
  }

  lemma /*{:_induction this}*/ forall_validAssignmentTrace_traceDLEndStrictlyOrdered()
    requires 0 <= decisionLevel
    requires decisionLevel as int < traceDLStart.Length
    requires decisionLevel as int < traceDLEnd.Length
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures validVariablesCount() && validAssignmentTrace() ==> forall i: SYInt32.t {:trigger traceDLEnd[i]} :: 0 <= i < decisionLevel ==> traceDLEnd[i] < traceDLEnd[decisionLevel]
  {
    if validVariablesCount() && validAssignmentTrace() {
      forall i: SYInt32.t | 0 <= i < decisionLevel
        ensures traceDLEnd[i] < traceDLEnd[decisionLevel]
      {
        validAssignmentTrace_traceDLEndStrictlyOrdered(i);
      }
    }
  }

  lemma /*{:_induction this}*/ validAssignmentTrace_traceDLEndStrictlyOrdered(i: SYInt32.t)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires 0 <= i < decisionLevel
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures traceDLEnd[i] < traceDLEnd[decisionLevel]
    decreases decisionLevel - i
  {
    if i == decisionLevel - 1 {
    } else if i < decisionLevel - 1 {
      validAssignmentTrace_traceDLEndStrictlyOrdered(i + 1);
    }
  }

  method increaseDecisionLevel()
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires decisionLevel < variablesCount - 1
    requires decisionLevel >= 0 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    modifies `decisionLevel, traceDLStart, traceDLEnd
    ensures decisionLevel == old(decisionLevel) + 1
    ensures validAssignmentTrace()
    ensures traceDLStart[decisionLevel] == traceDLEnd[decisionLevel]
    ensures getDecisionLevel(decisionLevel) == {}
    ensures forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
  {
    decisionLevel := decisionLevel + 1;
    var previous: SYInt32.t := 0;
    if decisionLevel == 0 {
      previous := 0;
    } else {
      previous := traceDLEnd[decisionLevel - 1];
    }
    traceDLStart[decisionLevel] := previous;
    traceDLEnd[decisionLevel] := previous;
    assert old(traceVariable[..]) == traceVariable[..];
  }

  ghost function getDecisionLevel(dL: SYInt32.t): set<(SYInt32.t, bool)>
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires -1 <= dL <= decisionLevel
    requires traceVariable.Length == variablesCount as int
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue, `assignmentsTrace
    ensures getDecisionLevel(dL) <= assignmentsTrace
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue, this}, dL
  {
    if dL == -1 then
      {}
    else
      set j: (SYInt32.t, bool) {:trigger j.0} {:trigger j in assignmentsTrace} | j in assignmentsTrace && j.0 in traceVariable[traceDLStart[dL] .. traceDLEnd[dL]]
  }

  method extractUnsetLiteralFromClause(clauseIndex: SYInt32.t) returns (literal: SYInt32.t)
    requires valid()
    requires 0 <= clauseIndex < clausesCount
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex]
    requires trueLiteralsCount[clauseIndex] == 0 && falseLiteralsCount[clauseIndex] + 1 == clauseLength[clauseIndex]
    ensures validLiteral(literal)
    ensures literal in clauses[clauseIndex]
    ensures truthAssignment[getVariableFromLiteral(literal)] == -1
    decreases clauseIndex
  {
    unitClause_existsUnsetLiteral(clauseIndex);
    var i: SYInt32.t := 0;
    var clause := clauses[clauseIndex];
    while i < clauseLength[clauseIndex]
      invariant 0 <= i < clauseLength[clauseIndex]
      invariant exists literal: SYInt32.t {:trigger getVariableFromLiteral(literal)} {:trigger literal in clause[i..]} :: literal in clause[i..] && truthAssignment[getVariableFromLiteral(literal)] == -1
      decreases clauseLength[clauseIndex] - i
    {
      if truthAssignment[getVariableFromLiteral(clause[i])] == -1 {
        return clause[i];
      }
      i := i + 1;
    }
    assert false;
  }

  method propagate(clauseIndex: SYInt32.t)
    requires valid()
    requires 0 <= decisionLevel
    requires 0 <= clauseIndex < clausesCount
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex]
    requires trueLiteralsCount[clauseIndex] == 0 && falseLiteralsCount[clauseIndex] + 1 == clauseLength[clauseIndex]
    modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLEnd, traceValue, traceVariable, `assignmentsTrace
    ensures valid()
    ensures forall x: SYInt32.t {:trigger old(traceVariable[x])} {:trigger traceVariable[x]} :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures assignmentsTrace == old(assignmentsTrace) + getDecisionLevel(decisionLevel)
    ensures countUnsetVariables(truthAssignment[..]) < old(countUnsetVariables(truthAssignment[..]))
    ensures old(assignmentsTrace) <= assignmentsTrace
    ensures forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures ghost var tau: seq<SYInt32.t> := old(truthAssignment[..]); isSatisfiableExtend(tau) <==> isSatisfiableExtend(truthAssignment[..])
    decreases countUnsetVariables(truthAssignment[..]), 1
  {
    ghost var tau'' := truthAssignment[..];
    var literal := extractUnsetLiteralFromClause(clauseIndex);
    var clause := clauses[clauseIndex];
    ghost var (v', val') := convertLVtoVI(literal, true);
    unitClauseLiteralFalse_tauNotSatisfiable(tau'', clauseIndex, literal);
    setLiteral(literal, true);
    assert isSatisfiableExtend(tau''[v' as int := val']) <==> isSatisfiableExtend(truthAssignment[..]);
    if isSatisfiableExtend(truthAssignment[..]) {
      extensionSatisfiable_baseSatisfiable(tau'', v', val');
    } else {
      forVariableNotSatisfiableExtend_notSatisfiableExtend(tau'', v');
    }
    assert !isSatisfiableExtend(tau'') <==> !isSatisfiableExtend(truthAssignment[..]);
    assert countUnsetVariables(truthAssignment[..]) < old(countUnsetVariables(truthAssignment[..]));
  }

  method unitPropagation(variable: SYInt32.t, value: bool)
    requires valid()
    requires validVariable(variable)
    requires 0 <= decisionLevel
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLEnd, traceValue, traceVariable, `assignmentsTrace
    ensures valid()
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures old(assignmentsTrace) <= assignmentsTrace
    ensures assignmentsTrace == old(assignmentsTrace) + getDecisionLevel(decisionLevel)
    ensures forall x: SYInt32.t {:trigger old(traceVariable[x])} {:trigger traceVariable[x]} :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
    ensures forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures countUnsetVariables(truthAssignment[..]) <= old(countUnsetVariables(truthAssignment[..]))
    ensures ghost var tau: seq<SYInt32.t> := old(truthAssignment[..]); isSatisfiableExtend(tau) <==> isSatisfiableExtend(truthAssignment[..])
    decreases countUnsetVariables(truthAssignment[..]), 2
  {
    var negativelyImpactedClauses := negativeLiteralsToClauses[variable];
    if !value {
      negativelyImpactedClauses := positiveLiteralsToClauses[variable];
    }
    var k: SYInt32.t := 0;
    var negativelyImpactedClausesLen: SYInt32.t := |negativelyImpactedClauses| as SYInt32.t;
    while k < negativelyImpactedClausesLen
      invariant 0 <= k <= negativelyImpactedClausesLen
      invariant valid()
      invariant decisionLevel == old(decisionLevel)
      invariant traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
      invariant assignmentsTrace == old(assignmentsTrace) + getDecisionLevel(decisionLevel)
      invariant countUnsetVariables(truthAssignment[..]) <= old(countUnsetVariables(truthAssignment[..]))
      invariant isSatisfiableExtend(old(truthAssignment[..])) <==> isSatisfiableExtend(truthAssignment[..])
      invariant forall x: SYInt32.t {:trigger old(traceVariable[x])} {:trigger traceVariable[x]} :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
      invariant forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
      decreases |negativelyImpactedClauses| - k as int
    {
      var clauseIndex := negativelyImpactedClauses[k];
      if falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex] {
        if trueLiteralsCount[clauseIndex] == 0 && falseLiteralsCount[clauseIndex] + 1 == clauseLength[clauseIndex] {
          propagate(clauseIndex);
        }
      }
      k := k + 1;
    }
  }

  method setLiteral(literal: SYInt32.t, value: bool)
    requires valid()
    requires validLiteral(literal)
    requires getLiteralValue(truthAssignment[..], literal) == -1
    requires 0 <= decisionLevel
    modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLEnd, traceValue, traceVariable, `assignmentsTrace
    ensures valid()
    ensures traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures forall x: SYInt32.t {:trigger old(traceVariable[x])} {:trigger traceVariable[x]} :: 0 <= x < old(traceDLEnd[decisionLevel]) ==> traceVariable[x] == old(traceVariable[x])
    ensures assignmentsTrace == old(assignmentsTrace) + getDecisionLevel(decisionLevel)
    ensures forall i: SYInt32.t {:trigger getDecisionLevel(i)} {:trigger old(getDecisionLevel(i))} :: 0 <= i < decisionLevel ==> old(getDecisionLevel(i)) == getDecisionLevel(i)
    ensures countUnsetVariables(truthAssignment[..]) < old(countUnsetVariables(truthAssignment[..]))
    ensures var (variable: SYInt32.t, val: SYInt32.t) := convertLVtoVI(literal, value); isSatisfiableExtend(old(truthAssignment[..])[variable as int := val]) <==> isSatisfiableExtend(truthAssignment[..])
    decreases countUnsetVariables(truthAssignment[..]), 0
  {
    ghost var (vari, val) := convertLVtoVI(literal, value);
    ghost var tau' := truthAssignment[..][vari as int := val];
    var variable := getVariableFromLiteral(literal);
    var value' := if literal > 0 then value else !value;
    setVariable(variable, value');
    unitPropagation(variable, value');
  }

  method chooseLiteral() returns (x: SYInt32.t)
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    ensures valid()
    ensures validLiteral(x)
    ensures truthAssignment[getVariableFromLiteral(x)] == -1
    ensures getLiteralValue(truthAssignment[..], x) == -1
  {
    notEmptyNoEmptyClauses_existUnsetLiteralInClauses();
    var minim: SYInt32.t := SYInt32.max as SYInt32.t;
    var counter: SYInt32.t := 0;
    var result: SYInt32.t := -1;
    var ok := false;
    var cI: SYInt32.t := 0;
    while cI < clausesCount
      invariant 0 <= cI <= clausesCount
      invariant !ok ==> counter == 0 && minim == SYInt32.max as SYInt32.t && exists i': SYInt32.t, k': int {:trigger clauses[i'][k']} :: cI <= i' < clausesCount && 0 <= k' < |clauses[i']| && trueLiteralsCount[i'] == 0 && validLiteral(clauses[i'][k']) && truthAssignment[getVariableFromLiteral(clauses[i'][k'])] == -1 && getLiteralValue(truthAssignment[..], clauses[i'][k']) == -1
      invariant (exists i': SYInt32.t, k': int {:trigger clauses[i'][k']} :: 0 <= i' < cI && 0 <= k' < |clauses[i']| && trueLiteralsCount[i'] == 0 && validLiteral(clauses[i'][k']) && truthAssignment[getVariableFromLiteral(clauses[i'][k'])] == -1 && getLiteralValue(truthAssignment[..], clauses[i'][k']) == -1) ==> ok
      invariant ok ==> validLiteral(result) && truthAssignment[getVariableFromLiteral(result)] == -1 && getLiteralValue(truthAssignment[..], result) == -1
      invariant 0 <= counter as int <= countLiterals(cI)
      decreases clausesCount as int - cI as int
    {
      var diff := clauseLength[cI] - falseLiteralsCount[cI];
      if trueLiteralsCount[cI] == 0 && diff < minim {
        minim := diff;
      }
      if trueLiteralsCount[cI] == 0 && diff == minim {
        assert validClause(clauses[cI]);
        var lI: SYInt32.t := 0;
        while lI < clauseLength[cI]
          invariant 0 <= lI <= clauseLength[cI]
          invariant !ok ==> counter == 0 && exists k': int {:trigger clauses[cI][k']} :: lI as int <= k' < |clauses[cI]| && trueLiteralsCount[cI] == 0 && validLiteral(clauses[cI][k']) && truthAssignment[getVariableFromLiteral(clauses[cI][k'])] == -1 && getLiteralValue(truthAssignment[..], clauses[cI][k']) == -1
          invariant (exists k': SYInt32.t {:trigger clauses[cI][k']} :: 0 <= k' < lI && trueLiteralsCount[cI] == 0 && validLiteral(clauses[cI][k']) && truthAssignment[getVariableFromLiteral(clauses[cI][k'])] == -1 && getLiteralValue(truthAssignment[..], clauses[cI][k']) == -1) ==> ok
          invariant ok ==> validLiteral(result) && truthAssignment[getVariableFromLiteral(result)] == -1 && getLiteralValue(truthAssignment[..], result) == -1
          invariant 0 <= counter as int <= countLiterals(cI) + lI as int
          decreases clauseLength[cI] as int - lI as int
        {
          countLiterals_monotone(cI);
          assert validLiteral(clauses[cI][lI]);
          var variable := getVariableFromLiteral(clauses[cI][lI]);
          if truthAssignment[variable] == -1 {
            ok := true;
            if counter == 0 {
              result := variable + 1;
              counter := counter + 1;
            } else if result == variable + 1 {
              counter := counter + 1;
            } else {
              counter := counter - 1;
            }
          }
          lI := lI + 1;
        }
      }
      cI := cI + 1;
    }
    return -result;
  }

  lemma /*{:_induction this}*/ maybeClause_existUnsetLiteralInClause(clauseIndex: SYInt32.t)
    requires valid()
    requires 0 <= clauseIndex < clausesCount
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] < clauseLength[clauseIndex]
    ensures exists j': SYInt32.t {:trigger clauses[clauseIndex][j']} :: 0 <= j' < clauseLength[clauseIndex] && validLiteral(clauses[clauseIndex][j']) && truthAssignment[getVariableFromLiteral(clauses[clauseIndex][j'])] == -1
    decreases clauseIndex
  {
    ghost var tau := truthAssignment[..];
    ghost var clause := clauses[clauseIndex];
    countTrueLiterals0_noLiteralsTrue(tau, clause);
    ghost var clauseLen := clauseLength[clauseIndex];
    ghost var k := clauseLen - 1;
    ghost var flc := 0;
    ghost var ok := false;
    ghost var index: SYInt32.t := 0;
    assert clauseLen > 0;
    while k >= 0
      invariant -1 <= k < clauseLen
      invariant forall k': SYInt32.t {:trigger clause[k']} :: k < k' < clauseLen ==> getLiteralValue(tau, clause[k']) != 1
      invariant countTrueLiterals(tau, clause[k + 1..]) == 0
      invariant countFalseLiterals(tau, clause[k + 1..]) == flc
      invariant flc == clauseLen - 1 - k ==> ok == false
      invariant flc < clauseLen - 1 - k ==> ok == true
      invariant ok ==> 0 <= index < clauseLen
      invariant ok ==> getLiteralValue(tau, clause[index]) == -1
      decreases k
    {
      if getLiteralValue(tau, clause[k]) == 0 {
        flc := flc + 1;
      }
      if getLiteralValue(tau, clause[k]) == -1 {
        ok := true;
        index := k;
      }
      k := k - 1;
    }
    assert ok;
    assert clause[index] in clauses[clauseIndex];
    assert 0 <= index < clauseLen;
    assert validLiteral(clauses[clauseIndex][index]);
    assert truthAssignment[getVariableFromLiteral(clauses[clauseIndex][index])] == -1;
  }

  lemma /*{:_induction this}*/ notEmptyNoEmptyClauses_existUnsetLiteralInClauses()
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    ensures forall i: int {:trigger clauses[i]} {:trigger clauseLength[i]} {:trigger falseLiteralsCount[i]} {:trigger trueLiteralsCount[i]} :: 0 <= i < |clauses| && trueLiteralsCount[i] == 0 && falseLiteralsCount[i] < clauseLength[i] ==> exists j': SYInt32.t {:trigger clauses[i][j']} :: 0 <= j' < clauseLength[i] && validLiteral(clauses[i][j']) && truthAssignment[getVariableFromLiteral(clauses[i][j'])] == -1
  {
    forall i: SYInt32.t | 0 <= i < clausesCount && trueLiteralsCount[i] == 0 && falseLiteralsCount[i] < clauseLength[i]
      ensures exists j': SYInt32.t {:trigger clauses[i][j']} :: 0 <= j' < clauseLength[i] && validLiteral(clauses[i][j']) && truthAssignment[getVariableFromLiteral(clauses[i][j'])] == -1
    {
      maybeClause_existUnsetLiteralInClause(i);
    }
  }

  function hasEmptyClause(): bool
    requires valid()
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    ensures hasEmptyClause() == true ==> exists i: int {:trigger clauses[i]} {:trigger falseLiteralsCount[i]} :: 0 <= i < |clauses| && falseLiteralsCount[i] as int == |clauses[i]|
    ensures hasEmptyClause() == false ==> forall i: int {:trigger clauses[i]} {:trigger falseLiteralsCount[i]} :: 0 <= i < |clauses| ==> falseLiteralsCount[i] as int < |clauses[i]|
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    if exists i: SYInt32.t {:trigger clauseLength[i]} {:trigger falseLiteralsCount[i]} :: 0 <= i < clausesCount && falseLiteralsCount[i] == clauseLength[i] then
      var i: SYInt32.t :| 0 <= i < clausesCount && falseLiteralsCount[i] == clauseLength[i];
      true
    else
      false
  }

  method getHasEmptyClause() returns (ok: bool)
    requires valid()
    ensures ok <==> hasEmptyClause()
    ensures ok ==> exists i: SYInt32.t {:trigger clauseLength[i]} {:trigger falseLiteralsCount[i]} :: 0 <= i < clausesCount && falseLiteralsCount[i] == clauseLength[i]
    ensures !ok ==> forall i: SYInt32.t {:trigger clauseLength[i]} {:trigger falseLiteralsCount[i]} :: 0 <= i < clausesCount ==> falseLiteralsCount[i] < clauseLength[i]
  {
    var k: SYInt32.t := 0;
    while k < clausesCount
      invariant 0 <= k <= clausesCount
      invariant forall k': SYInt32.t {:trigger clauseLength[k']} {:trigger falseLiteralsCount[k']} :: 0 <= k' < k ==> falseLiteralsCount[k'] < clauseLength[k']
      decreases clausesCount as int - k as int
    {
      if falseLiteralsCount[k] == clauseLength[k] {
        return true;
      }
      k := k + 1;
    }
    return false;
  }

  function isEmpty(): bool
    requires valid()
    requires !hasEmptyClause()
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    ensures isEmpty() == true ==> forall i: int {:trigger trueLiteralsCount[i]} :: 0 <= i < |clauses| ==> trueLiteralsCount[i] > 0
    ensures isEmpty() == false ==> exists i: int {:trigger trueLiteralsCount[i]} :: 0 <= i < |clauses| && trueLiteralsCount[i] == 0
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    if exists i: SYInt32.t {:trigger trueLiteralsCount[i]} :: 0 <= i < clausesCount && trueLiteralsCount[i] == 0 then
      var i: SYInt32.t :| 0 <= i < clausesCount && trueLiteralsCount[i] == 0;
      false
    else
      true
  }

  method getIsEmpty() returns (ok: bool)
    requires valid()
    requires !hasEmptyClause()
    ensures ok <==> isEmpty()
    ensures ok ==> forall i: SYInt32.t {:trigger trueLiteralsCount[i]} :: 0 <= i < clausesCount ==> trueLiteralsCount[i] > 0
    ensures !ok ==> exists i: SYInt32.t {:trigger trueLiteralsCount[i]} :: 0 <= i < clausesCount && trueLiteralsCount[i] == 0
  {
    var k: SYInt32.t := 0;
    while k < clausesCount
      invariant 0 <= k <= clausesCount
      invariant forall k': SYInt32.t {:trigger trueLiteralsCount[k']} :: 0 <= k' < k ==> trueLiteralsCount[k'] > 0
      decreases clausesCount as int - k as int
    {
      if trueLiteralsCount[k] == 0 {
        return false;
      }
      k := k + 1;
    }
    return true;
  }

  method level0UnitPropagation()
    requires valid()
    requires decisionLevel == -1
    modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLStart, traceDLEnd, traceValue, traceVariable, `assignmentsTrace, `decisionLevel
    ensures valid()
    ensures decisionLevel > -1 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures isSatisfiableExtend(old(truthAssignment[..])) <==> isSatisfiableExtend(truthAssignment[..])
  {
    var i := 0;
    increaseDecisionLevel();
    while i < clausesCount
      invariant 0 <= i <= clausesCount
      invariant valid()
      invariant isSatisfiableExtend(old(truthAssignment[..])) <==> isSatisfiableExtend(truthAssignment[..])
      decreases clausesCount as int - i as int
      modifies truthAssignment, trueLiteralsCount, falseLiteralsCount, traceDLStart, traceDLEnd, traceValue, traceVariable, `assignmentsTrace
    {
      if trueLiteralsCount[i] == 0 && falseLiteralsCount[i] + 1 == clauseLength[i] {
        propagate(i);
      }
      i := i + 1;
    }
    if traceDLStart[decisionLevel] == traceDLEnd[decisionLevel] {
      revertLastDecisionLevel();
    }
  }

  lemma /*{:_induction this}*/ notEmptyNoEmptyClauses_traceNotFull()
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    requires decisionLevel > -1 ==> traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures decisionLevel < variablesCount - 1
  {
    if decisionLevel == variablesCount - 1 {
      ifFull_containsAllVariables();
      forall v: SYInt32.t | 0 <= v < variablesCount
        ensures truthAssignment[v] != -1
      {
        if truthAssignment[v] == -1 {
          assert (v, true) !in assignmentsTrace;
          assert (v, false) !in assignmentsTrace;
          assert occursInAssignmentsTrace(v);
          ghost var x :| x in assignmentsTrace && x.0 == v;
          var (i, b) := x;
          assert x == (v, true) || x == (v, false);
          assert false;
        }
      }
      allVariablesSet_done();
      assert false;
    }
  }

  predicate occursInTrace(variable: SYInt32.t)
    requires valid()
    requires validVariable(variable)
    requires decisionLevel > -1
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}, variable
  {
    exists j: SYInt32.t {:trigger traceVariable[j]} :: 
      0 <= j < traceDLEnd[decisionLevel] &&
      traceVariable[j] == variable
  }

  ghost predicate occursInAssignmentsTrace(variable: SYInt32.t)
    requires valid()
    requires validVariable(variable)
    requires decisionLevel > -1
    requires decisionLevel == variablesCount - 1
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}, variable
  {
    exists x: (SYInt32.t, bool) {:trigger x.0} {:trigger x in assignmentsTrace} :: 
      x in assignmentsTrace &&
      x.0 == variable
  }

  lemma /*{:_induction this}*/ ifFull_containsAllVariables()
    requires valid()
    requires !hasEmptyClause()
    requires !isEmpty()
    requires decisionLevel == variablesCount - 1
    requires traceDLStart[decisionLevel] < traceDLEnd[decisionLevel]
    ensures forall v: SYInt32.t {:trigger occursInTrace(v)} :: 0 <= v < variablesCount ==> occursInTrace(v)
    ensures forall v: SYInt32.t {:trigger occursInAssignmentsTrace(v)} :: 0 <= v < variablesCount ==> occursInAssignmentsTrace(v)
  {
    ghost var L: set<SYInt32.t>, R: set<SYInt32.t> := {}, Utils.RangeSet(0, variablesCount);
    ghost var i: SYInt32.t := 0;
    Utils.CardinalityRangeSet(0, variablesCount);
    forall_validAssignmentTrace_traceDLStartStrictlyOrdered();
    while i < variablesCount
      invariant 0 <= i <= variablesCount
      invariant L == set j: SYInt32.t {:trigger traceDLStart[j]} | 0 <= j < i :: traceVariable[traceDLStart[j]]
      invariant forall v: SYInt32.t {:trigger validVariable(v)} {:trigger v in L} :: v in L ==> validVariable(v)
      invariant forall v: SYInt32.t {:trigger occursInTrace(v)} {:trigger v in L} :: v in L ==> occursInTrace(v)
      invariant forall v: SYInt32.t {:trigger v in R} {:trigger v in L} :: 0 <= v < variablesCount ==> v in L || v in R
      invariant |R| == (variablesCount - i) as int
      decreases variablesCount - i
    {
      L, R := L + {traceVariable[traceDLStart[i]]}, R - {traceVariable[traceDLStart[i]]};
      i := i + 1;
    }
    assert forall v: SYInt32.t {:trigger occursInTrace(v)} {:trigger v in L} :: (0 <= v < variablesCount ==> v in L) && (0 <= v < variablesCount ==> occursInTrace(v));
    forall v: SYInt32.t | 0 <= v < variablesCount
      ensures occursInAssignmentsTrace(v)
    {
      assert occursInTrace(v);
      ghost var j :| 0 <= j < variablesCount && traceVariable[traceDLStart[j]] == v;
      if j < decisionLevel {
        validAssignmentTrace_traceDLStartStrictlyOrdered(j, decisionLevel);
      }
      assert traceDLStart[j] < traceDLEnd[decisionLevel];
      assert (traceVariable[traceDLStart[j]], traceValue[traceDLStart[j]]) in assignmentsTrace;
      assert occursInAssignmentsTrace(v);
    }
    assert forall v: SYInt32.t {:trigger occursInAssignmentsTrace(v)} :: 0 <= v < variablesCount ==> occursInAssignmentsTrace(v);
  }

  lemma /*{:_induction this}*/ allVariablesSet_done()
    requires valid()
    requires forall v: SYInt32.t {:trigger isVariableSet(truthAssignment[..], v)} {:trigger validVariable(v)} :: validVariable(v) ==> isVariableSet(truthAssignment[..], v)
    ensures hasEmptyClause() || isEmpty()
  {
    if !hasEmptyClause() {
      if !isEmpty() {
        ghost var k := 0;
        assert forall k: int {:trigger clauses[k]} {:trigger falseLiteralsCount[k]} :: 0 <= k < |clauses| ==> falseLiteralsCount[k] as int < |clauses[k]|;
        while k < |clauses|
          invariant 0 <= k <= |clauses|
          invariant forall k': int {:trigger trueLiteralsCount[k']} :: 0 <= k' < k ==> trueLiteralsCount[k'] > 0
          decreases |clauses| - k
        {
          assert validClause(clauses[k]);
          assert falseLiteralsCount[k] as int < |clauses[k]|;
          assert forall x: SYInt32.t {:trigger getVariableFromLiteral(x)} {:trigger x in clauses[k]} :: x in clauses[k] ==> isVariableSet(truthAssignment[..], getVariableFromLiteral(x));
          tauFullClauseNotEmpty_clauseIsSatisfied(k);
          k := k + 1;
        }
      } else {
      }
    } else {
    }
  }

  lemma /*{:_induction this}*/ tauFullClauseNotEmpty_clauseIsSatisfied(cI: int)
    requires valid()
    requires 0 <= cI < |clauses|
    requires validClause(clauses[cI])
    requires forall x: SYInt32.t {:trigger getVariableFromLiteral(x)} {:trigger x in clauses[cI]} :: x in clauses[cI] ==> isVariableSet(truthAssignment[..], getVariableFromLiteral(x))
    requires falseLiteralsCount[cI] as int < |clauses[cI]|
    ensures trueLiteralsCount[cI] > 0
    decreases cI
  {
    ghost var tau := truthAssignment[..];
    ghost var clause := clauses[cI];
    assert forall x: SYInt32.t {:trigger getLiteralValue(tau, x)} {:trigger x in clause} :: x in clause ==> getLiteralValue(tau, x) in [0, 1];
    if forall x: SYInt32.t {:trigger getLiteralValue(tau, x)} {:trigger x in clause} :: x in clause ==> getLiteralValue(tau, x) == 0 {
      ghost var k := |clause| - 1;
      while k > 0
        invariant 0 <= k <= |clause|
        invariant countFalseLiterals(tau, clause[k..]) as int == |clause| - k
        decreases k
      {
        k := k - 1;
      }
      assert countFalseLiterals(tau, clause) as int == |clause| == |clauses[cI]|;
    } else {
      assert exists x: SYInt32.t {:trigger getLiteralValue(tau, x)} {:trigger x in clause} :: x in clause && getLiteralValue(tau, x) == 1;
      existsTrueLiteral_countTrueLiteralsPositive(clause, tau);
    }
  }

  lemma /*{:_induction this, clause, truthAssignment}*/ existsTrueLiteral_countTrueLiteralsPositive(clause: seq<SYInt32.t>, truthAssignment: seq<SYInt32.t>)
    requires valid()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires exists x: SYInt32.t {:trigger getLiteralValue(truthAssignment, x)} {:trigger x in clause} :: x in clause && getLiteralValue(truthAssignment, x) == 1
    ensures countTrueLiterals(truthAssignment, clause) > 0
    decreases clause, truthAssignment
  {
    if |clause| == 0 {
    } else if getLiteralValue(truthAssignment, clause[0]) == 1 {
    } else {
      existsTrueLiteral_countTrueLiteralsPositive(clause[1..], truthAssignment);
    }
  }

  lemma /*{:_induction this}*/ unitClause_existsUnsetLiteral(clauseIndex: SYInt32.t)
    requires valid()
    requires 0 <= clauseIndex as int < |clauses|
    requires validClause(clauses[clauseIndex])
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|
    ensures exists literal: SYInt32.t {:trigger getVariableFromLiteral(literal)} {:trigger literal in clauses[clauseIndex]} :: literal in clauses[clauseIndex] && truthAssignment[getVariableFromLiteral(literal)] == -1
    decreases clauseIndex
  {
    maybeClause_existUnsetLiteralInClause(clauseIndex);
  }

  lemma /*{:_induction this}*/ hasEmptyClause_notSatisfiable()
    requires valid()
    requires hasEmptyClause()
    ensures !isSatisfiableExtend(truthAssignment[..])
  {
    ghost var tau := truthAssignment[..];
    ghost var clauseIndex: SYInt32.t :| 0 <= clauseIndex as int < |clauses| && falseLiteralsCount[clauseIndex] as int == |clauses[clauseIndex]|;
    ghost var clause := clauses[clauseIndex];
    assert validClause(clause);
    allLiteralsSetToFalse_clauseUnsatisfied(clauseIndex);
    if tau': seq<SYInt32.t> {:trigger isSatisfied(tau')} {:trigger isExtendingTau(tau, tau')} {:trigger isTauComplete(tau')} {:trigger validValuesTruthAssignment(tau')} :| validValuesTruthAssignment(tau') && isTauComplete(tau') && isExtendingTau(tau, tau') && isSatisfied(tau') {
      assert forall l: SYInt32.t {:trigger getLiteralValue(tau', l)} {:trigger getLiteralValue(tau, l)} {:trigger l in clause} :: (l in clause ==> getLiteralValue(tau, l) == getLiteralValue(tau', l)) && (l in clause ==> getLiteralValue(tau', l) == 0);
      assert !isClauseSatisfied(tau', clauseIndex);
      assert false;
    }
  }

  lemma /*{:_induction this}*/ allLiteralsSetToFalse_clauseUnsatisfied(clauseIndex: SYInt32.t)
    requires valid()
    requires 0 <= clauseIndex as int < |clauses|
    requires falseLiteralsCount[clauseIndex] as int == |clauses[clauseIndex]|
    requires validClause(clauses[clauseIndex])
    ensures forall literal: SYInt32.t {:trigger getLiteralValue(truthAssignment[..], literal)} {:trigger literal in clauses[clauseIndex]} :: literal in clauses[clauseIndex] ==> getLiteralValue(truthAssignment[..], literal) == 0
    decreases clauseIndex
  {
    ghost var clause := clauses[clauseIndex];
    ghost var k: SYInt32.t := 0;
    ghost var flc := 0;
    ghost var tau := truthAssignment[..];
    while k as int < |clause|
      invariant 0 <= k as int <= |clause|
      invariant countFalseLiterals(tau, clause[k..]) == falseLiteralsCount[clauseIndex] - k
      invariant forall k': SYInt32.t {:trigger clause[k']} :: 0 <= k' < k ==> getLiteralValue(tau, clause[k']) == 0
      decreases |clause| - k as int
    {
      k := k + 1;
    }
  }

  lemma /*{:_induction this}*/ isEmpty_sastisfied()
    requires valid()
    requires !hasEmptyClause()
    requires isEmpty()
    ensures isSatisfiableExtend(truthAssignment[..])
    ensures isSatisfiableTruthAssignment(truthAssignment[..], truthAssignment[..])
  {
    assert forall i: int {:trigger trueLiteralsCount[i]} :: 0 <= i < |clauses| ==> trueLiteralsCount[i] > 0;
    forall i: SYInt32.t | 0 <= i as int < |clauses|
      ensures isClauseSatisfied(truthAssignment[..], i)
    {
      countTrueLiteralsX_existsTrueLiteral(truthAssignment[..], clauses[i]);
    }
    assert isSatisfied(truthAssignment[..]);
    assert variablesCount > 0;
    partialTauSatisfied_isSatisfiableExtend(truthAssignment[..]);
  }

  lemma /*{:_induction this}*/ partialTauSatisfied_isSatisfiableExtend(tau: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validClauses()
    requires isSatisfied(tau)
    ensures isSatisfiableExtend(tau)
    decreases countUnsetVariables(tau)
  {
    if isTauComplete(tau) {
    } else {
      ghost var x :| 0 <= x < |tau| && tau[x] == -1;
      ghost var tau' := tau[x := 0];
      forall i: SYInt32.t | 0 <= i as int < |clauses|
        ensures isClauseSatisfied(tau', i)
      {
        assert isClauseSatisfied(tau, i);
      }
      assert isSatisfied(tau');
      ghost var k := |tau'| - 1;
      while k > 0
        invariant 0 <= k < |tau'|
        invariant x < k < |tau'| ==> countUnsetVariables(tau'[k..]) == countUnsetVariables(tau[k..])
        invariant 0 <= k <= x ==> countUnsetVariables(tau'[k..]) + 1 == countUnsetVariables(tau[k..])
        decreases k - 0
      {
        k := k - 1;
      }
      assert countUnsetVariables(tau) - 1 == countUnsetVariables(tau');
      partialTauSatisfied_isSatisfiableExtend(tau');
    }
  }

  lemma /*{:_induction this}*/ unitClause_allFalseExceptLiteral(truthAssignment: seq<SYInt32.t>, clauseIndex: SYInt32.t, literal: SYInt32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    requires validTrueLiteralsCount(truthAssignment)
    requires validFalseLiteralsCount(truthAssignment)
    requires 0 <= clauseIndex as int < |clauses|
    requires validClause(clauses[clauseIndex])
    requires validLiteral(literal)
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|
    requires literal in clauses[clauseIndex]
    requires getLiteralValue(truthAssignment, literal) == -1
    requires forall literal: SYInt32.t {:trigger getLiteralValue(truthAssignment, literal)} {:trigger literal in clauses[clauseIndex]} :: literal in clauses[clauseIndex] ==> getLiteralValue(truthAssignment, literal) != 1
    ensures forall literal': SYInt32.t {:trigger getLiteralValue(truthAssignment, literal')} {:trigger literal' in clauses[clauseIndex]} :: literal' in clauses[clauseIndex] && literal' != literal ==> getLiteralValue(truthAssignment, literal') != -1
    decreases truthAssignment, clauseIndex, literal
  {
    ghost var clause := clauses[clauseIndex];
    ghost var literalIndex :| 0 <= literalIndex < |clause| && clause[literalIndex] == literal;
    if i: int {:trigger clause[i]} :| 0 <= i < |clause| && i != literalIndex && getLiteralValue(truthAssignment, clause[i]) == -1 {
      ghost var a := i;
      ghost var b := literalIndex;
      if b < a {
        a := literalIndex;
        b := i;
      }
      assert a < b;
      assert getLiteralValue(truthAssignment, clause[a]) == -1;
      assert getLiteralValue(truthAssignment, clause[b]) == -1;
      ghost var k := |clause| - 1;
      while k >= 0
        invariant -1 <= k < |clause|
        invariant 0 <= a < b < |clause|
        invariant b <= k ==> countFalseLiterals(truthAssignment, clause[k + 1..]) as int <= |clause| - (k + 1)
        invariant a <= k < b ==> countFalseLiterals(truthAssignment, clause[k + 1..]) as int <= |clause| - (k + 1) - 1
        invariant k < a ==> countFalseLiterals(truthAssignment, clause[k + 1..]) as int <= |clause| - (k + 1) - 2
        decreases k
      {
        k := k - 1;
      }
      assert false;
    }
  }

  lemma /*{:_induction this}*/ unitClauseLiteralFalse_tauNotSatisfiable(truthAssignment: seq<SYInt32.t>, clauseIndex: SYInt32.t, literal: SYInt32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    requires validTrueLiteralsCount(truthAssignment)
    requires validFalseLiteralsCount(truthAssignment)
    requires 0 <= clauseIndex as int < |clauses|
    requires validClause(clauses[clauseIndex])
    requires validLiteral(literal)
    requires trueLiteralsCount[clauseIndex] == 0
    requires falseLiteralsCount[clauseIndex] as int + 1 == |clauses[clauseIndex]|
    requires truthAssignment[getVariableFromLiteral(literal)] == -1
    requires literal in clauses[clauseIndex]
    ensures var (variable: SYInt32.t, value: SYInt32.t) := convertLVtoVI(literal, false); !isSatisfiableExtend(truthAssignment[variable as int := value])
    decreases truthAssignment, clauseIndex, literal
  {
    ghost var clause := clauses[clauseIndex];
    var (variable, value) := convertLVtoVI(literal, false);
    countTrueLiterals0_noLiteralsTrue(truthAssignment, clause);
    unitClause_allFalseExceptLiteral(truthAssignment, clauseIndex, literal);
    ghost var tau := truthAssignment[variable as int := value];
    ghost var k := |clause| - 1;
    while k >= 0
      invariant -1 <= k < |clause|
      invariant forall k': int {:trigger clause[k']} :: k < k' < |clause| ==> getLiteralValue(tau, clause[k']) == 0
      decreases k
    {
      if getLiteralValue(tau, clause[k]) == 1 {
        assert literal in clause;
        assert clause[k] in clause;
        if literal == clause[k] {
          assert getLiteralValue(truthAssignment, literal) == -1;
          assert getLiteralValue(tau, literal) == 0;
          assert false;
        } else if -literal == clause[k] {
          assert false;
        } else {
          assert getLiteralValue(truthAssignment, clause[k]) != 1;
          assert getVariableFromLiteral(clause[k]) != variable;
          assert tau[getVariableFromLiteral(clause[k])] == truthAssignment[getVariableFromLiteral(clause[k])];
          assert getLiteralValue(tau, clause[k]) != 1;
          assert false;
        }
        assert false;
      }
      if getLiteralValue(tau, clause[k]) == -1 {
        assert false;
      }
      k := k - 1;
    }
    if tau': seq<SYInt32.t> {:trigger isSatisfied(tau')} {:trigger isExtendingTau(tau, tau')} {:trigger isTauComplete(tau')} {:trigger validValuesTruthAssignment(tau')} :| validValuesTruthAssignment(tau') && isTauComplete(tau') && isExtendingTau(tau, tau') && isSatisfied(tau') {
      assert forall l: SYInt32.t {:trigger getLiteralValue(tau', l)} {:trigger getLiteralValue(tau, l)} {:trigger l in clause} :: (l in clause ==> getLiteralValue(tau, l) == getLiteralValue(tau', l)) && (l in clause ==> getLiteralValue(tau', l) == 0);
      assert !isClauseSatisfied(tau', clauseIndex);
      assert false;
    }
  }

  lemma /*{:_induction this, tau}*/ variableSet_countUnsetVariablesLessThanLength(tau: seq<SYInt32.t>, variable: SYInt32.t)
    requires |tau| <= SYInt32.max as int
    requires 0 <= variable as int < |tau|
    requires tau[variable] in [0, 1]
    ensures countUnsetVariables(tau) as int < |tau|
    decreases tau, variable
  {
    ghost var k := |tau| - 1;
    while k >= 0
      invariant -1 <= k < |tau|
      invariant forall j: int {:trigger tau[j..]} :: k < j < |tau| && j > variable as int ==> countUnsetVariables(tau[j..]) as int <= |tau[j..]|
      invariant forall j: int {:trigger tau[j..]} :: k < j < |tau| && j <= variable as int ==> countUnsetVariables(tau[j..]) as int < |tau[j..]|
      decreases k
    {
      if k == variable as int {
        assert tau[variable] != -1;
      }
      k := k - 1;
    }
  }

  lemma /*{:_induction this, tau, clause}*/ unsetVariable_countTrueLiteralsLessThanLength(tau: seq<SYInt32.t>, variable: SYInt32.t, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validClause(clause)
    requires validVariable(variable)
    requires tau[variable] == -1
    requires variable + 1 in clause || -variable - 1 in clause
    ensures countTrueLiterals(tau, clause) as int < |clause|
    decreases tau, variable, clause
  {
    ghost var literal: SYInt32.t := variable + 1;
    if variable + 1 !in clause {
      literal := -variable - 1;
    }
    ghost var k := |clause| - 1;
    while k >= 0 && clause[k] != literal
      invariant -1 <= k < |clause|
      invariant countTrueLiterals(tau, clause[k + 1..]) as int <= |clause[k + 1..]|
      invariant forall j: int {:trigger clause[j]} :: k < j < |clause| ==> clause[j] != literal
      decreases k
    {
      k := k - 1;
    }
    if k < 0 {
      assert false;
    } else {
      assert clause[k] == literal;
      assert getLiteralValue(tau, clause[k]) == -1;
      assert countTrueLiterals(tau, clause[k..]) as int < |clause[k..]|;
      k := k - 1;
      while k >= 0
        invariant -1 <= k < |clause|
        invariant countTrueLiterals(tau, clause[k + 1..]) as int < |clause[k + 1..]|
        decreases k
      {
        k := k - 1;
      }
    }
  }

  lemma /*{:_induction this, tau, clause}*/ unsetVariable_countFalseLiteralsLessThanLength(tau: seq<SYInt32.t>, variable: SYInt32.t, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validClause(clause)
    requires validVariable(variable)
    requires tau[variable] == -1
    requires variable + 1 in clause || -variable - 1 in clause
    ensures countFalseLiterals(tau, clause) as int < |clause|
    decreases tau, variable, clause
  {
    ghost var literal: SYInt32.t := variable + 1;
    if variable + 1 !in clause {
      literal := -variable - 1;
    }
    ghost var k := |clause| - 1;
    while k >= 0 && clause[k] != literal
      invariant -1 <= k < |clause|
      invariant countFalseLiterals(tau, clause[k + 1..]) as int <= |clause[k + 1..]|
      invariant forall j: int {:trigger clause[j]} :: k < j < |clause| ==> clause[j] != literal
      decreases k
    {
      k := k - 1;
    }
    if k < 0 {
      assert false;
    } else {
      assert clause[k] == literal;
      assert getLiteralValue(tau, clause[k]) == -1;
      assert countFalseLiterals(tau, clause[k..]) as int < |clause[k..]|;
      k := k - 1;
      while k >= 0
        invariant -1 <= k < |clause|
        invariant countFalseLiterals(tau, clause[k + 1..]) as int < |clause[k + 1..]|
        decreases k
      {
        k := k - 1;
      }
    }
  }

  lemma /*{:_induction this}*/ forVariableNotSatisfiableExtend_notSatisfiableExtend(tau: seq<SYInt32.t>, variable: SYInt32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    requires validVariable(variable)
    requires !isSatisfiableExtend(tau[variable as int := 0])
    requires !isSatisfiableExtend(tau[variable as int := 1])
    ensures !isSatisfiableExtend(tau)
    decreases tau, variable
  {
  }

  lemma /*{:_induction this}*/ extensionSatisfiable_baseSatisfiable(tau: seq<SYInt32.t>, variable: SYInt32.t, value: SYInt32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    requires validVariable(variable)
    requires value in [0, 1]
    requires tau[variable] == -1
    requires isSatisfiableExtend(tau[variable as int := value])
    ensures isSatisfiableExtend(tau)
    decreases tau, variable, value
  {
    ghost var tau' := tau[variable as int := value];
    assert isSatisfiableExtend(tau');
  }
}

module Utils {
  method newInitializedSeq(n: SYInt32.t, d: SYInt32.t) returns (r: array<SYInt32.t>)
    requires 0 < n
    ensures r.Length == n as int
    ensures forall j: int {:trigger r[j]} :: 0 <= j < r.Length ==> r[j] == d
    ensures fresh(r)
    decreases n, d
  {
    r := new SYInt32.t[n];
    var index: SYInt32.t := 0;
    while index < n
      invariant 0 <= index as int <= r.Length == n as int
      invariant forall j: SYInt32.t {:trigger r[j]} :: 0 <= j < index ==> r[j] == d
      decreases n - index
    {
      r[index] := d;
      index := index + 1;
    }
  }

  function abs(literal: SYInt32.t): SYInt32.t
    decreases literal
  {
    if literal < 0 then
      -literal
    else
      literal
  }

  lemma prop_seq_predicate(q: int, abc: seq<SYInt32.t>)
    requires forall j: SYInt32.t {:trigger j in abc} :: (j in abc ==> 0 <= j as int) && (j in abc ==> j as int < q)
    ensures forall j: int {:trigger abc[j]} :: (0 <= j < |abc| ==> 0 <= abc[j] as int) && (0 <= j < |abc| ==> abc[j] as int < q)
    decreases q, abc
  {
    assert forall j: int {:trigger abc[j]} :: 0 <= j < |abc| ==> abc[j] in abc ==> 0 <= abc[j] as int < q;
  }

  predicate valueBoundedBy(value: SYInt32.t, min: int, max: int)
    decreases value, min, max
  {
    min <= value as int < max
  }

  predicate valuesBoundedBy(s: seq<SYInt32.t>, min: int, max: int)
    decreases s, min, max
  {
    (forall el: SYInt32.t {:trigger valueBoundedBy(el, min, max)} {:trigger el in s} :: 
      el in s ==>
        valueBoundedBy(el, min, max)) &&
    forall i: int {:trigger s[i]} :: 
      0 <= i < |s| ==>
        valueBoundedBy(s[i], min, max)
  }

  predicate orderedAsc(s: seq<SYInt32.t>)
    decreases s
  {
    forall x: int, y: int {:trigger s[y], s[x]} :: 
      0 <= x < y < |s| ==>
        s[x] < s[y]
  }

  predicate InRange(lo: SYInt32.t, hi: SYInt32.t, i: SYInt32.t)
    decreases lo, hi, i
  {
    lo <= i < hi
  }

  function RangeSet(lo: SYInt32.t, hi: SYInt32.t): set<SYInt32.t>
    decreases lo, hi
  {
    set i: SYInt32.t {:trigger InRange(lo, hi, i)} | lo <= i < hi && InRange(lo, hi, i)
  }

  lemma CardinalityRangeSet(lo: SYInt32.t, hi: SYInt32.t)
    requires 0 <= lo <= hi
    ensures |RangeSet(lo, hi)| == if lo >= hi then 0 else (hi - lo) as int
    decreases hi - lo
  {
    if lo < hi {
      assert RangeSet(lo, hi) == {lo} + RangeSet(lo + 1, hi);
      CardinalityRangeSet(lo + 1, hi);
    }
  }

  import SYInt32
}

trait DataStructures {
  var variablesCount: SYInt32.t
  var clauses: seq<seq<SYInt32.t>>
  var clausesCount: SYInt32.t
  var clauseLength: array<SYInt32.t>
  var truthAssignment: array<SYInt32.t>
  var trueLiteralsCount: array<SYInt32.t>
  var falseLiteralsCount: array<SYInt32.t>
  var positiveLiteralsToClauses: array<seq<SYInt32.t>>
  var negativeLiteralsToClauses: array<seq<SYInt32.t>>
  var decisionLevel: SYInt32.t
  var traceVariable: array<SYInt32.t>
  var traceValue: array<bool>
  var traceDLStart: array<SYInt32.t>
  var traceDLEnd: array<SYInt32.t>
  ghost var assignmentsTrace: set<(SYInt32.t, bool)>

  predicate validVariablesCount()
    reads `variablesCount
    decreases {this}
  {
    0 < variablesCount < SYInt32.max as SYInt32.t
  }

  predicate validLiteral(literal: SYInt32.t)
    requires validVariablesCount()
    reads `variablesCount
    decreases {this}, literal
  {
    if literal == 0 then
      false
    else if -variablesCount <= literal && literal <= variablesCount then
      true
    else
      false
  }

  predicate validClause(clause: seq<SYInt32.t>)
    requires validVariablesCount()
    reads `variablesCount
    decreases {this}, clause
  {
    |clause| < SYInt32.max as int &&
    (forall x: int, y: int {:trigger clause[y], clause[x]} :: 
      0 <= x < y < |clause| ==>
        clause[x] != clause[y]) &&
    forall literal: SYInt32.t {:trigger validLiteral(literal)} {:trigger literal in clause} :: 
      literal in clause ==>
        validLiteral(literal)
  }

  predicate validClauses()
    requires validVariablesCount()
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}
  {
    0 < |clauses| == clausesCount as int <= SYInt32.max as int &&
    clauseLength.Length == clausesCount as int &&
    (forall i: SYInt32.t {:trigger clauses[i]} {:trigger clauseLength[i]} :: 
      (0 <= i < clausesCount ==>
        0 < clauseLength[i] as int) &&
      (0 <= i < clausesCount ==>
        clauseLength[i] as int == |clauses[i]|) &&
      (0 <= i < clausesCount ==>
        |clauses[i]| < SYInt32.max as int)) &&
    forall clause: seq<SYInt32.t> {:trigger validClause(clause)} {:trigger clause in clauses} :: 
      clause in clauses ==>
        validClause(clause)
  }

  predicate validVariable(variable: SYInt32.t)
    requires validVariablesCount()
    reads `variablesCount
    decreases {this}, variable
  {
    0 <= variable < variablesCount
  }

  ghost predicate validAssignmentTrace()
    requires validVariablesCount()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue, `assignmentsTrace
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue, this}
  {
    validAssignmentTraceBasic() &&
    validTraceDL() &&
    validTraceVariable() &&
    validAssignmentTraceGhost()
  }

  predicate validAssignmentTraceBasic()
    requires validVariablesCount()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue}
  {
    0 < variablesCount < SYInt32.max as SYInt32.t &&
    -1 <= decisionLevel < variablesCount &&
    traceVariable.Length == variablesCount as int &&
    traceValue.Length == variablesCount as int &&
    traceDLStart.Length == variablesCount as int &&
    traceDLEnd.Length == variablesCount as int &&
    traceVariable != traceDLStart &&
    traceVariable != traceDLEnd &&
    traceDLStart != traceDLEnd
  }

  predicate validTraceDL()
    requires validVariablesCount()
    requires validAssignmentTraceBasic()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue}
  {
    (forall dl: SYInt32.t {:trigger traceDLEnd[dl]} {:trigger traceDLStart[dl]} :: 
      (0 <= dl < decisionLevel ==>
        0 <= traceDLStart[dl]) &&
      (0 <= dl < decisionLevel ==>
        traceDLStart[dl] < traceDLEnd[dl]) &&
      (0 <= dl < decisionLevel ==>
        traceDLEnd[dl] <= variablesCount)) &&
    (decisionLevel >= 0 ==>
      traceDLStart[0] == 0 &&
      0 <= traceDLStart[decisionLevel] <= traceDLEnd[decisionLevel] <= variablesCount) &&
    forall dl: SYInt32.t {:trigger traceDLStart[dl]} :: 
      0 < dl <= decisionLevel ==>
        traceDLStart[dl] == traceDLEnd[dl - 1]
  }

  predicate validTraceVariable()
    requires validVariablesCount()
    requires validAssignmentTraceBasic()
    requires validTraceDL()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue}
  {
    decisionLevel >= 0 ==>
      (forall i: SYInt32.t {:trigger traceVariable[i]} :: 
        0 <= i < traceDLEnd[decisionLevel] ==>
          validVariable(traceVariable[i])) &&
      forall i: SYInt32.t {:trigger traceVariable[i]} :: 
        0 <= i < traceDLEnd[decisionLevel] ==>
          forall j: SYInt32.t {:trigger traceVariable[j]} :: 
            0 <= j < traceDLEnd[decisionLevel] &&
            i != j ==>
              traceVariable[i] != traceVariable[j]
  }

  ghost predicate validAssignmentTraceGhost()
    requires validVariablesCount()
    requires validAssignmentTraceBasic()
    requires validTraceDL()
    requires validTraceVariable()
    reads `variablesCount, `decisionLevel, `traceDLStart, `traceDLEnd, `traceVariable, `traceValue, traceDLStart, traceDLEnd, traceVariable, traceValue, `assignmentsTrace
    decreases {this, this, this, this, this, this, traceDLStart, traceDLEnd, traceVariable, traceValue, this}
  {
    (decisionLevel == -1 ==>
      assignmentsTrace == {}) &&
    (decisionLevel >= 0 ==>
      (forall i: SYInt32.t {:trigger traceValue[i]} {:trigger traceVariable[i]} :: 
        0 <= i < traceDLEnd[decisionLevel] ==>
          (traceVariable[i], traceValue[i]) in assignmentsTrace) &&
      forall x: (SYInt32.t, bool) {:trigger x in assignmentsTrace} :: 
        x in assignmentsTrace ==>
          exists i: SYInt32.t {:trigger traceValue[i]} {:trigger traceVariable[i]} :: 
            0 <= i < traceDLEnd[decisionLevel] &&
            (traceVariable[i], traceValue[i]) == x)
  }

  function convertIntToBool(x: SYInt32.t): bool
    decreases x
  {
    if x == 0 then
      false
    else
      true
  }

  predicate validValuesTruthAssignment(truthAssignment: seq<SYInt32.t>)
    requires validVariablesCount()
    reads `variablesCount
    decreases {this}, truthAssignment
  {
    |truthAssignment| == variablesCount as int &&
    |truthAssignment| <= SYInt32.max as int &&
    forall i: int {:trigger truthAssignment[i]} :: 
      (0 <= i < |truthAssignment| ==>
        -1 <= truthAssignment[i]) &&
      (0 <= i < |truthAssignment| ==>
        truthAssignment[i] <= 1)
  }

  ghost predicate validTruthAssignment()
    requires validVariablesCount()
    requires validAssignmentTrace()
    reads this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment
    decreases {this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment}
  {
    validValuesTruthAssignment(truthAssignment[..]) &&
    (forall i: SYInt32.t {:trigger truthAssignment[i]} :: 
      0 <= i < variablesCount &&
      truthAssignment[i] != -1 ==>
        (i, convertIntToBool(truthAssignment[i])) in assignmentsTrace) &&
    forall i: SYInt32.t {:trigger (i, true)} {:trigger (i, false)} {:trigger truthAssignment[i]} :: 
      (0 <= i < variablesCount &&
      truthAssignment[i] == -1 ==>
        (i, false) !in assignmentsTrace) &&
      (0 <= i < variablesCount &&
      truthAssignment[i] == -1 ==>
        (i, true) !in assignmentsTrace)
  }

  function getLiteralValue(truthAssignment: seq<SYInt32.t>, literal: SYInt32.t): SYInt32.t
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validLiteral(literal)
    reads `variablesCount
    decreases {this}, truthAssignment, literal
  {
    var variable: SYInt32.t := Utils.abs(literal) - 1;
    if truthAssignment[variable] == -1 then
      -1
    else if literal < 0 then
      1 - truthAssignment[variable]
    else
      truthAssignment[variable]
  }

  predicate isClauseSatisfied(truthAssignment: seq<SYInt32.t>, clauseIndex: SYInt32.t)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    requires 0 <= clauseIndex as int < |clauses|
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}, truthAssignment, clauseIndex
  {
    assert validClause(clauses[clauseIndex]);
    exists literal: SYInt32.t {:trigger getLiteralValue(truthAssignment, literal)} {:trigger literal in clauses[clauseIndex]} :: 
      literal in clauses[clauseIndex] &&
      getLiteralValue(truthAssignment, literal) == 1
  }

  function getVariableFromLiteral(literal: SYInt32.t): SYInt32.t
    requires validVariablesCount()
    requires validLiteral(literal)
    reads this
    ensures validVariable(getVariableFromLiteral(literal))
    decreases {this}, literal
  {
    Utils.abs(literal) - 1
  }

  function convertLVtoVI(literal: SYInt32.t, value: bool): (SYInt32.t, SYInt32.t)
    requires validVariablesCount()
    requires validLiteral(literal)
    reads this
    ensures validVariable(convertLVtoVI(literal, value).0)
    ensures convertLVtoVI(literal, value).0 == getVariableFromLiteral(literal)
    ensures convertLVtoVI(literal, value).1 in [0, 1]
    decreases {this}, literal, value
  {
    var variable: SYInt32.t := getVariableFromLiteral(literal);
    var v: SYInt32.t := if value then 1 else 0;
    var val: SYInt32.t := if literal < 0 then 1 - v else v;
    (variable, val)
  }

  predicate validTrueLiteralsCount(truthAssignment: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads `variablesCount, `clauses, `trueLiteralsCount, `clauseLength, `clausesCount, trueLiteralsCount, clauseLength
    decreases {this, this, this, this, this, trueLiteralsCount, clauseLength}, truthAssignment
  {
    trueLiteralsCount.Length == |clauses| &&
    forall i: int {:trigger clauses[i]} {:trigger trueLiteralsCount[i]} :: 
      (0 <= i < |clauses| ==>
        0 <= trueLiteralsCount[i]) &&
      (0 <= i < |clauses| ==>
        trueLiteralsCount[i] == countTrueLiterals(truthAssignment, clauses[i]))
  }

  function countUnsetVariables(truthAssignment: seq<SYInt32.t>): SYInt32.t
    requires |truthAssignment| <= SYInt32.max as int
    ensures 0 <= countUnsetVariables(truthAssignment) as int <= |truthAssignment| <= SYInt32.max as int
    decreases truthAssignment
  {
    if |truthAssignment| == 0 then
      0
    else
      var ok: SYInt32.t := if truthAssignment[0] == -1 then 1 else 0; ok + countUnsetVariables(truthAssignment[1..])
  }

  function countTrueLiterals(truthAssignment: seq<SYInt32.t>, clause: seq<SYInt32.t>): SYInt32.t
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    reads `variablesCount, `clauseLength, clauseLength
    ensures 0 <= countTrueLiterals(truthAssignment, clause) as int <= |clause|
    decreases {this, this, clauseLength}, truthAssignment, clause
  {
    if |clause| == 0 then
      0
    else
      var ok: SYInt32.t := if getLiteralValue(truthAssignment, clause[0]) == 1 then 1 else 0; ok + countTrueLiterals(truthAssignment, clause[1..])
  }

  lemma /*{:_induction this, truthAssignment, clause}*/ prop_countTrueLiterals_initialTruthAssignment(truthAssignment: seq<SYInt32.t>, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires forall j: int {:trigger truthAssignment[j]} :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1
    ensures countTrueLiterals(truthAssignment, clause) == 0
    decreases truthAssignment, clause
  {
    assert forall literal: SYInt32.t {:trigger getLiteralValue(truthAssignment, literal)} {:trigger literal in clause} :: literal in clause ==> getLiteralValue(truthAssignment, literal) == -1;
    if |clause| > 0 {
      assert clause[0] in clause;
      assert getLiteralValue(truthAssignment, clause[0]) == -1;
      prop_countTrueLiterals_initialTruthAssignment(truthAssignment, clause[1..]);
    }
  }

  lemma /*{:_induction this, truthAssignment, clause}*/ countTrueLiterals0_noLiteralsTrue(truthAssignment: seq<SYInt32.t>, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validClause(clause)
    requires validValuesTruthAssignment(truthAssignment)
    requires countTrueLiterals(truthAssignment, clause) == 0
    ensures forall literal: SYInt32.t {:trigger getLiteralValue(truthAssignment, literal)} {:trigger literal in clause} :: literal in clause ==> getLiteralValue(truthAssignment, literal) != 1
    decreases truthAssignment, clause
  {
    ghost var k := 0;
    while k < |clause|
      invariant -1 <= k <= |clause|
      invariant forall k': int {:trigger clause[k']} :: 0 <= k' < k ==> getLiteralValue(truthAssignment, clause[k']) != 1
      invariant countTrueLiterals(truthAssignment, clause[k..]) == 0
      decreases |clause| - k
    {
      k := k + 1;
    }
  }

  lemma /*{:_induction this, truthAssignment, clause}*/ countTrueLiteralsX_existsTrueLiteral(truthAssignment: seq<SYInt32.t>, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validClause(clause)
    requires validValuesTruthAssignment(truthAssignment)
    requires countTrueLiterals(truthAssignment, clause) > 0
    ensures exists literal: SYInt32.t {:trigger getLiteralValue(truthAssignment, literal)} {:trigger literal in clause} :: literal in clause && getLiteralValue(truthAssignment, literal) == 1
    decreases truthAssignment, clause
  {
    if countTrueLiterals(truthAssignment, clause) == 0 {
      countTrueLiterals0_noLiteralsTrue(truthAssignment, clause);
      assert forall literal: SYInt32.t {:trigger getLiteralValue(truthAssignment, literal)} {:trigger literal in clause} :: literal in clause ==> getLiteralValue(truthAssignment, literal) != 1;
    } else {
      if getLiteralValue(truthAssignment, clause[0]) != 1 {
        countTrueLiteralsX_existsTrueLiteral(truthAssignment, clause[1..]);
      } else {
      }
    }
  }

  predicate validFalseLiteralsCount(truthAssignment: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads `variablesCount, `clauses, `falseLiteralsCount, `clauseLength, `clausesCount, falseLiteralsCount, clauseLength
    decreases {this, this, this, this, this, falseLiteralsCount, clauseLength}, truthAssignment
  {
    falseLiteralsCount.Length == |clauses| &&
    forall i: int {:trigger clauses[i]} {:trigger falseLiteralsCount[i]} :: 
      (0 <= i < |clauses| ==>
        0 <= falseLiteralsCount[i]) &&
      (0 <= i < |clauses| ==>
        falseLiteralsCount[i] == countFalseLiterals(truthAssignment, clauses[i]))
  }

  function countFalseLiterals(truthAssignment: seq<SYInt32.t>, clause: seq<SYInt32.t>): SYInt32.t
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    reads `variablesCount, `clauseLength, clauseLength
    ensures 0 <= countFalseLiterals(truthAssignment, clause) as int <= |clause|
    decreases {this, this, clauseLength}, truthAssignment, clause
  {
    if |clause| == 0 then
      0
    else
      var ok: SYInt32.t := if getLiteralValue(truthAssignment, clause[0]) == 0 then 1 else 0; ok + countFalseLiterals(truthAssignment, clause[1..])
  }

  lemma /*{:_induction this, truthAssignment, clause}*/ prop_countFalseLiterals_initialTruthAssignment(truthAssignment: seq<SYInt32.t>, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validClause(clause)
    requires forall j: int {:trigger truthAssignment[j]} :: 0 <= j < |truthAssignment| ==> truthAssignment[j] == -1
    ensures countFalseLiterals(truthAssignment, clause) == 0
    decreases truthAssignment, clause
  {
    assert forall literal: SYInt32.t {:trigger getLiteralValue(truthAssignment, literal)} {:trigger literal in clause} :: literal in clause ==> getLiteralValue(truthAssignment, literal) == -1;
    if |clause| > 0 {
      assert clause[0] in clause;
      assert getLiteralValue(truthAssignment, clause[0]) == -1;
      prop_countFalseLiterals_initialTruthAssignment(truthAssignment, clause[1..]);
    }
  }

  predicate validPositiveLiteralsToClauses()
    requires validVariablesCount()
    requires validClauses()
    reads this, positiveLiteralsToClauses, clauseLength
    decreases {this, positiveLiteralsToClauses, clauseLength}
  {
    positiveLiteralsToClauses.Length == variablesCount as int &&
    (forall variable: SYInt32.t {:trigger positiveLiteralsToClauses[variable]} :: 
      0 <= variable as int < positiveLiteralsToClauses.Length ==>
        validPositiveLiteralToClause(variable, positiveLiteralsToClauses[variable])) &&
    forall variable: SYInt32.t {:trigger positiveLiteralsToClauses[variable]} :: 
      0 <= variable as int < positiveLiteralsToClauses.Length ==>
        |positiveLiteralsToClauses[variable]| <= clausesCount as int
  }

  predicate validPositiveLiteralToClause(variable: SYInt32.t, s: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= variable < variablesCount
    reads this, clauseLength
    decreases {this, clauseLength}, variable, s
  {
    Utils.valuesBoundedBy(s, 0, |clauses|) &&
    Utils.orderedAsc(s) &&
    (forall clauseIndex: SYInt32.t {:trigger clauses[clauseIndex]} {:trigger clauseIndex in s} :: 
      clauseIndex in s ==>
        variable + 1 in clauses[clauseIndex]) &&
    forall clauseIndex: SYInt32.t {:trigger clauses[clauseIndex]} {:trigger clauseIndex in s} :: 
      0 <= clauseIndex as int < |clauses| &&
      clauseIndex !in s ==>
        variable + 1 !in clauses[clauseIndex]
  }

  predicate validNegativeLiteralsToClauses()
    requires validVariablesCount()
    requires validClauses()
    reads this, negativeLiteralsToClauses, clauseLength
    decreases {this, negativeLiteralsToClauses, clauseLength}
  {
    negativeLiteralsToClauses.Length == variablesCount as int &&
    forall v: SYInt32.t {:trigger negativeLiteralsToClauses[v]} :: 
      (0 <= v as int < negativeLiteralsToClauses.Length ==>
        validNegativeLiteralsToClause(v, negativeLiteralsToClauses[v])) &&
      (0 <= v as int < negativeLiteralsToClauses.Length ==>
        forall variable: SYInt32.t {:trigger negativeLiteralsToClauses[variable]} :: 
          0 <= variable as int < negativeLiteralsToClauses.Length ==>
            |negativeLiteralsToClauses[variable]| <= clausesCount as int)
  }

  predicate validNegativeLiteralsToClause(variable: SYInt32.t, s: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= variable < variablesCount
    reads this, clauseLength
    decreases {this, clauseLength}, variable, s
  {
    Utils.valuesBoundedBy(s, 0, |clauses|) &&
    Utils.orderedAsc(s) &&
    (forall clauseIndex: SYInt32.t {:trigger clauses[clauseIndex]} {:trigger clauseIndex in s} :: 
      clauseIndex in s ==>
        -variable - 1 in clauses[clauseIndex]) &&
    forall clauseIndex: SYInt32.t {:trigger clauses[clauseIndex]} {:trigger clauseIndex in s} :: 
      0 <= clauseIndex as int < |clauses| &&
      clauseIndex !in s ==>
        -variable - 1 !in clauses[clauseIndex]
  }

  predicate validReferences()
    reads this, truthAssignment, trueLiteralsCount, falseLiteralsCount, positiveLiteralsToClauses, negativeLiteralsToClauses, clauseLength
    decreases {this, truthAssignment, trueLiteralsCount, falseLiteralsCount, positiveLiteralsToClauses, negativeLiteralsToClauses, clauseLength}
  {
    truthAssignment != trueLiteralsCount &&
    truthAssignment != falseLiteralsCount &&
    truthAssignment != clauseLength &&
    truthAssignment != traceVariable &&
    truthAssignment != traceDLStart &&
    truthAssignment != traceDLEnd &&
    trueLiteralsCount != falseLiteralsCount &&
    trueLiteralsCount != clauseLength &&
    trueLiteralsCount != traceVariable &&
    trueLiteralsCount != traceDLStart &&
    trueLiteralsCount != traceDLEnd &&
    falseLiteralsCount != clauseLength &&
    falseLiteralsCount != traceVariable &&
    falseLiteralsCount != traceDLStart &&
    falseLiteralsCount != traceDLEnd &&
    clauseLength != traceVariable &&
    clauseLength != traceDLStart &&
    clauseLength != traceDLEnd &&
    positiveLiteralsToClauses != negativeLiteralsToClauses
  }

  ghost predicate valid()
    reads this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses
    decreases {this, traceDLStart, traceDLEnd, traceVariable, traceValue, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength, positiveLiteralsToClauses, negativeLiteralsToClauses}
  {
    validReferences() &&
    validVariablesCount() &&
    validClauses() &&
    countLiterals(clausesCount) < SYInt32.max as int &&
    validAssignmentTrace() &&
    validTruthAssignment() &&
    validTrueLiteralsCount(truthAssignment[..]) &&
    validFalseLiteralsCount(truthAssignment[..]) &&
    validPositiveLiteralsToClauses() &&
    validNegativeLiteralsToClauses()
  }

  function countLiterals(clauseIndex: SYInt32.t): int
    requires validVariablesCount()
    requires validClauses()
    requires 0 <= clauseIndex <= clausesCount
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}, clauseIndex
  {
    if clauseIndex == 0 then
      0
    else
      |clauses[clauseIndex - 1]| + countLiterals(clauseIndex - 1)
  }

  lemma /*{:_induction this, cI}*/ countLiterals_monotone(cI: SYInt32.t)
    requires validVariablesCount()
    requires validClauses()
    requires countLiterals(clausesCount) < SYInt32.max as int
    requires 0 <= cI <= clausesCount
    ensures 0 <= cI < clausesCount ==> countLiterals(cI) < countLiterals(cI + 1) < SYInt32.max as int
    decreases clausesCount - cI
  {
    if cI == clausesCount {
    } else {
      calc < {
        countLiterals(cI);
        {
          assert countLiterals(cI + 1) == countLiterals(cI) + clauseLength[cI] as int;
          assert clauseLength[cI] > 0;
        }
        countLiterals(cI + 1);
        {
          countLiterals_monotone(cI + 1);
        }
      }
    }
  }

  lemma /*{:_induction this, oldTau, newTau}*/ clausesNotImpacted_TFArraysSame(oldTau: seq<SYInt32.t>, newTau: seq<SYInt32.t>, variable: SYInt32.t, impactedClauses: seq<SYInt32.t>, impactedClauses': seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validClauses()
    requires validTrueLiteralsCount(oldTau)
    requires validFalseLiteralsCount(oldTau)
    requires forall clauseIndex: int {:trigger clauses[clauseIndex]} :: 0 <= clauseIndex < |clauses| ==> validClause(clauses[clauseIndex])
    requires validVariable(variable)
    requires newTau[variable] == 1 ==> validPositiveLiteralToClause(variable, impactedClauses)
    requires newTau[variable] == 1 ==> validNegativeLiteralsToClause(variable, impactedClauses')
    requires newTau[variable] == 0 ==> validPositiveLiteralToClause(variable, impactedClauses')
    requires newTau[variable] == 0 ==> validNegativeLiteralsToClause(variable, impactedClauses)
    requires forall x: SYInt32.t {:trigger newTau[x]} {:trigger oldTau[x]} :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    ensures forall clauseIndex: SYInt32.t {:trigger clauses[clauseIndex]} {:trigger clauseIndex in impactedClauses} :: 0 <= clauseIndex as int < |clauses| && clauseIndex !in impactedClauses ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == countTrueLiterals(newTau, clauses[clauseIndex])
    ensures forall clauseIndex: SYInt32.t {:trigger clauses[clauseIndex]} {:trigger clauseIndex in impactedClauses'} :: 0 <= clauseIndex as int < |clauses| && clauseIndex !in impactedClauses' ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == countFalseLiterals(newTau, clauses[clauseIndex])
    decreases oldTau, newTau, variable, impactedClauses, impactedClauses'
  {
    ghost var trueLiteral := variable + 1;
    ghost var falseLiteral := -variable - 1;
    if newTau[variable] == 0 {
      trueLiteral := -variable - 1;
      falseLiteral := variable + 1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    forall clauseIndex: SYInt32.t | 0 <= clauseIndex as int < |clauses|
      ensures clauseIndex !in impactedClauses ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == countTrueLiterals(newTau, clauses[clauseIndex])
      ensures clauseIndex !in impactedClauses' ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == countFalseLiterals(newTau, clauses[clauseIndex])
    {
      ghost var clause := clauses[clauseIndex];
      ghost var k := |clause| - 1;
      while k >= 0
        invariant -1 <= k < |clause|
        invariant clauseIndex !in impactedClauses ==> forall j: int {:trigger clause[j]} :: k < j < |clause| ==> (getLiteralValue(newTau, clause[j]) == 1 <==> getLiteralValue(oldTau, clause[j]) == 1)
        invariant clauseIndex !in impactedClauses ==> forall j: int {:trigger clause[j..]} :: k < j <= |clause| ==> countTrueLiterals(oldTau, clause[j..]) == countTrueLiterals(newTau, clause[j..])
        invariant clauseIndex !in impactedClauses' ==> forall j: int {:trigger clause[j]} :: k < j < |clause| ==> (getLiteralValue(newTau, clause[j]) == 0 <==> getLiteralValue(oldTau, clause[j]) == 0)
        invariant clauseIndex !in impactedClauses' ==> forall j: int {:trigger clause[j..]} :: k < j <= |clause| ==> countFalseLiterals(oldTau, clause[j..]) == countFalseLiterals(newTau, clause[j..])
        decreases k
      {
        if clauseIndex !in impactedClauses {
          assert clause[k] != trueLiteral;
          if clause[k] == falseLiteral {
            assert getLiteralValue(newTau, clause[k]) == 0;
          } else {
            ghost var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(newTau, clause[k]) == 1 <==> getLiteralValue(oldTau, clause[k]) == 1;
          }
        } else if clauseIndex !in impactedClauses' {
          assert clause[k] != falseLiteral;
          if clause[k] == trueLiteral {
            assert getLiteralValue(newTau, clause[k]) == 1;
          } else {
            ghost var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(newTau, clause[k]) == 0 <==> getLiteralValue(oldTau, clause[k]) == 0;
          }
        }
        k := k - 1;
      }
    }
  }

  lemma /*{:_induction this, oldTau, newTau, clause}*/ setVariable_countTrueLiteralsIncreasesWithOne(oldTau: seq<SYInt32.t>, newTau: seq<SYInt32.t>, variable: SYInt32.t, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires newTau[variable] == 1 ==> variable + 1 in clause
    requires newTau[variable] == 0 ==> -variable - 1 in clause
    requires forall x: SYInt32.t {:trigger newTau[x]} {:trigger oldTau[x]} :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    requires countTrueLiterals(oldTau, clause) as int < |clause|
    requires countTrueLiterals(newTau, clause) as int <= |clause|
    ensures countTrueLiterals(newTau, clause) == countTrueLiterals(oldTau, clause) + 1
    decreases oldTau, newTau, variable, clause
  {
    ghost var k := |clause| - 1;
    ghost var trueLiteral := variable + 1;
    ghost var falseLiteral := -variable - 1;
    if newTau[variable] == 0 {
      trueLiteral := -variable - 1;
      falseLiteral := variable + 1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    while k >= 0 && clause[k] != trueLiteral
      invariant -1 <= k < |clause|
      invariant trueLiteral in clause[0 .. k + 1]
      invariant countTrueLiterals(oldTau, clause[k + 1..]) == countTrueLiterals(newTau, clause[k + 1..])
      decreases k
    {
      if clause[k] != falseLiteral {
        assert oldTau[getVariableFromLiteral(clause[k])] == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
    assert clause[k] == trueLiteral;
    k := k - 1;
    while k >= 0
      invariant -1 <= k < |clause|
      invariant countTrueLiterals(oldTau, clause[k + 1..]) + 1 == countTrueLiterals(newTau, clause[k + 1..])
      decreases k
    {
      if clause[k] != falseLiteral {
        assert oldTau[getVariableFromLiteral(clause[k])] == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }

  lemma /*{:_induction this, oldTau, newTau, clause}*/ setVariable_countFalseLiteralsIncreasesWithOne(oldTau: seq<SYInt32.t>, newTau: seq<SYInt32.t>, variable: SYInt32.t, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires newTau[variable] == 1 ==> -variable - 1 in clause
    requires newTau[variable] == 0 ==> variable + 1 in clause
    requires forall x: SYInt32.t {:trigger newTau[x]} {:trigger oldTau[x]} :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    requires countFalseLiterals(oldTau, clause) as int < |clause|
    requires countFalseLiterals(newTau, clause) as int <= |clause|
    ensures countFalseLiterals(newTau, clause) == countFalseLiterals(oldTau, clause) + 1
    decreases oldTau, newTau, variable, clause
  {
    ghost var k := |clause| - 1;
    ghost var trueLiteral := variable + 1;
    ghost var falseLiteral := -variable - 1;
    if newTau[variable] == 0 {
      trueLiteral := -variable - 1;
      falseLiteral := variable + 1;
    }
    assert getLiteralValue(newTau, trueLiteral) == 1;
    assert getLiteralValue(newTau, falseLiteral) == 0;
    assert falseLiteral in clause;
    assert falseLiteral in clause[0 .. k + 1];
    while k >= 0 && clause[k] != falseLiteral
      invariant -1 <= k < |clause|
      invariant falseLiteral in clause[0 .. k + 1]
      invariant countFalseLiterals(oldTau, clause[k + 1..]) == countFalseLiterals(newTau, clause[k + 1..])
      decreases k
    {
      if clause[k] != trueLiteral {
        assert oldTau[getVariableFromLiteral(clause[k])] == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
    k := k - 1;
    while k >= 0
      invariant -1 <= k < |clause|
      invariant countFalseLiterals(oldTau, clause[k + 1..]) + 1 == countFalseLiterals(newTau, clause[k + 1..])
      decreases k
    {
      if clause[k] != trueLiteral {
        assert oldTau[getVariableFromLiteral(clause[k])] == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }

  lemma /*{:_induction this, oldTau, clause}*/ literalTrue_countTrueLiteralsAtLeastOne(oldTau: seq<SYInt32.t>, variable: SYInt32.t, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires oldTau[variable] == 1 ==> variable + 1 in clause
    requires oldTau[variable] == 0 ==> -variable - 1 in clause
    requires oldTau[variable] in [0, 1]
    ensures 0 < countTrueLiterals(oldTau, clause)
    decreases oldTau, variable, clause
  {
    ghost var literal: SYInt32.t := variable + 1;
    if oldTau[variable] == 0 {
      literal := -variable - 1;
    }
    ghost var k := |clause| - 1;
    while k >= 0 && clause[k] != literal
      invariant -1 <= k < |clause|
      invariant literal in clause[..k + 1]
      invariant countTrueLiterals(oldTau, clause[k + 1..]) >= 0
      decreases k
    {
      k := k - 1;
    }
    assert clause[k] == literal;
    assert getLiteralValue(oldTau, clause[k]) == 1;
    assert countTrueLiterals(oldTau, clause[k..]) > 0;
    k := k - 1;
    while k >= 0
      invariant -1 <= k < |clause|
      invariant countTrueLiterals(oldTau, clause[k + 1..]) > 0
      decreases k
    {
      k := k - 1;
    }
  }

  lemma /*{:_induction this, oldTau, newTau, clause}*/ unsetVariable_countTrueLiteralsDecreasesWithOne(oldTau: seq<SYInt32.t>, newTau: seq<SYInt32.t>, variable: SYInt32.t, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires oldTau[variable] == 1 ==> variable + 1 in clause
    requires oldTau[variable] == 0 ==> -variable - 1 in clause
    requires forall x: SYInt32.t {:trigger newTau[x]} {:trigger oldTau[x]} :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] in [0, 1]
    requires newTau[variable] == -1
    requires countTrueLiterals(oldTau, clause) as int <= |clause|
    requires countTrueLiterals(newTau, clause) as int < |clause|
    ensures countTrueLiterals(newTau, clause) == countTrueLiterals(oldTau, clause) - 1
    decreases oldTau, newTau, variable, clause
  {
    literalTrue_countTrueLiteralsAtLeastOne(oldTau, variable, clause);
    ghost var k := |clause| - 1;
    ghost var trueLiteral := variable + 1;
    ghost var falseLiteral := -variable - 1;
    if oldTau[variable] == 0 {
      trueLiteral := -variable - 1;
      falseLiteral := variable + 1;
    }
    assert getLiteralValue(oldTau, trueLiteral) == 1;
    assert getLiteralValue(oldTau, falseLiteral) == 0;
    while k >= 0 && clause[k] != trueLiteral
      invariant -1 <= k < |clause|
      invariant trueLiteral in clause[0 .. k + 1]
      invariant countTrueLiterals(oldTau, clause[k + 1..]) == countTrueLiterals(newTau, clause[k + 1..])
      decreases k
    {
      if clause[k] != falseLiteral {
        assert oldTau[getVariableFromLiteral(clause[k])] == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
    assert clause[k] == trueLiteral;
    assert countTrueLiterals(oldTau, clause[k..]) - 1 == countTrueLiterals(newTau, clause[k..]);
    k := k - 1;
    while k >= 0
      invariant -1 <= k < |clause|
      invariant countTrueLiterals(oldTau, clause[k + 1..]) - 1 == countTrueLiterals(newTau, clause[k + 1..])
      decreases k
    {
      if clause[k] != falseLiteral {
        assert oldTau[getVariableFromLiteral(clause[k])] == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }

  lemma /*{:_induction this, oldTau, newTau, clause}*/ unsetVariable_countFalseLiteralsDecreasesWithOne(oldTau: seq<SYInt32.t>, newTau: seq<SYInt32.t>, variable: SYInt32.t, clause: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validVariable(variable)
    requires validClause(clause)
    requires oldTau[variable] == 1 ==> -variable - 1 in clause
    requires oldTau[variable] == 0 ==> variable + 1 in clause
    requires forall x: SYInt32.t {:trigger newTau[x]} {:trigger oldTau[x]} :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires oldTau[variable] in [0, 1]
    requires newTau[variable] == -1
    requires countFalseLiterals(oldTau, clause) as int <= |clause|
    requires countFalseLiterals(newTau, clause) as int < |clause|
    ensures countFalseLiterals(newTau, clause) == countFalseLiterals(oldTau, clause) - 1
    decreases oldTau, newTau, variable, clause
  {
    ghost var k := |clause| - 1;
    ghost var trueLiteral := variable + 1;
    ghost var falseLiteral := -variable - 1;
    if oldTau[variable] == 0 {
      trueLiteral := -variable - 1;
      falseLiteral := variable + 1;
    }
    assert getLiteralValue(oldTau, trueLiteral) == 1;
    assert getLiteralValue(oldTau, falseLiteral) == 0;
    while k >= 0 && clause[k] != falseLiteral
      invariant -1 <= k < |clause|
      invariant falseLiteral in clause[0 .. k + 1]
      invariant countFalseLiterals(oldTau, clause[k + 1..]) == countFalseLiterals(newTau, clause[k + 1..])
      decreases k
    {
      if clause[k] != trueLiteral {
        assert oldTau[getVariableFromLiteral(clause[k])] == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
    assert clause[k] == falseLiteral;
    assert countFalseLiterals(oldTau, clause[k..]) - 1 == countFalseLiterals(newTau, clause[k..]);
    k := k - 1;
    while k >= 0
      invariant -1 <= k < |clause|
      invariant countFalseLiterals(oldTau, clause[k + 1..]) - 1 == countFalseLiterals(newTau, clause[k + 1..])
      decreases k
    {
      if clause[k] != trueLiteral {
        assert oldTau[getVariableFromLiteral(clause[k])] == newTau[getVariableFromLiteral(clause[k])];
      }
      k := k - 1;
    }
  }

  lemma /*{:_induction this, oldTau, newTau}*/ undoImpactedClauses_TFSArraysModified(oldTau: seq<SYInt32.t>, newTau: seq<SYInt32.t>, variable: SYInt32.t, impactedClauses: seq<SYInt32.t>, impactedClauses': seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires validClauses()
    requires validTrueLiteralsCount(oldTau)
    requires validFalseLiteralsCount(oldTau)
    requires forall clauseIndex: int {:trigger clauses[clauseIndex]} :: 0 <= clauseIndex < |clauses| ==> validClause(clauses[clauseIndex])
    requires validVariable(variable)
    requires oldTau[variable] == 1 ==> validPositiveLiteralToClause(variable, impactedClauses)
    requires oldTau[variable] == 1 ==> validNegativeLiteralsToClause(variable, impactedClauses')
    requires oldTau[variable] == 0 ==> validPositiveLiteralToClause(variable, impactedClauses')
    requires oldTau[variable] == 0 ==> validNegativeLiteralsToClause(variable, impactedClauses)
    requires forall x: SYInt32.t {:trigger newTau[x]} {:trigger oldTau[x]} :: 0 <= x as int < |oldTau| && x != variable ==> oldTau[x] == newTau[x]
    requires forall clauseIndex: int {:trigger trueLiteralsCount[clauseIndex]} {:trigger clauses[clauseIndex]} :: 0 <= clauseIndex < |clauses| ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == trueLiteralsCount[clauseIndex]
    requires forall clauseIndex: int {:trigger falseLiteralsCount[clauseIndex]} {:trigger clauses[clauseIndex]} :: 0 <= clauseIndex < |clauses| ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == falseLiteralsCount[clauseIndex]
    requires oldTau[variable] in [0, 1]
    requires newTau[variable] == -1
    ensures forall clauseIndex: SYInt32.t {:trigger clauses[clauseIndex]} {:trigger clauseIndex in impactedClauses} :: 0 <= clauseIndex as int < |clauses| && clauseIndex !in impactedClauses ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == countTrueLiterals(newTau, clauses[clauseIndex])
    ensures forall clauseIndex: SYInt32.t {:trigger clauses[clauseIndex]} {:trigger clauseIndex in impactedClauses'} :: 0 <= clauseIndex as int < |clauses| && clauseIndex !in impactedClauses' ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == countFalseLiterals(newTau, clauses[clauseIndex])
    decreases oldTau, newTau, variable, impactedClauses, impactedClauses'
  {
    ghost var trueLiteral := variable + 1;
    ghost var falseLiteral := -variable - 1;
    if oldTau[variable] == 0 {
      trueLiteral := -variable - 1;
      falseLiteral := variable + 1;
    }
    assert getLiteralValue(oldTau, trueLiteral) == 1;
    assert getLiteralValue(oldTau, falseLiteral) == 0;
    forall clauseIndex: SYInt32.t | 0 <= clauseIndex as int < |clauses|
      ensures clauseIndex !in impactedClauses ==> countTrueLiterals(oldTau, clauses[clauseIndex]) == countTrueLiterals(newTau, clauses[clauseIndex])
      ensures clauseIndex !in impactedClauses' ==> countFalseLiterals(oldTau, clauses[clauseIndex]) == countFalseLiterals(newTau, clauses[clauseIndex])
    {
      ghost var clause := clauses[clauseIndex];
      ghost var k := |clause| - 1;
      while k >= 0
        invariant -1 <= k < |clause|
        invariant clauseIndex !in impactedClauses ==> forall j: int {:trigger clause[j]} :: k < j < |clause| ==> (getLiteralValue(newTau, clause[j]) == 1 <==> getLiteralValue(oldTau, clause[j]) == 1)
        invariant clauseIndex !in impactedClauses ==> forall j: int {:trigger clause[j..]} :: k < j <= |clause| ==> countTrueLiterals(oldTau, clause[j..]) == countTrueLiterals(newTau, clause[j..])
        invariant clauseIndex !in impactedClauses' ==> forall j: int {:trigger clause[j]} :: k < j < |clause| ==> (getLiteralValue(newTau, clause[j]) == 0 <==> getLiteralValue(oldTau, clause[j]) == 0)
        invariant clauseIndex !in impactedClauses' ==> forall j: int {:trigger clause[j..]} :: k < j <= |clause| ==> countFalseLiterals(oldTau, clause[j..]) == countFalseLiterals(newTau, clause[j..])
        decreases k
      {
        if clauseIndex !in impactedClauses {
          assert clause[k] != trueLiteral;
          if clause[k] == falseLiteral {
            assert getLiteralValue(oldTau, clause[k]) == 0;
          } else {
            ghost var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(oldTau, clause[k]) == 1 <==> getLiteralValue(newTau, clause[k]) == 1;
          }
        } else if clauseIndex !in impactedClauses' {
          assert clause[k] != falseLiteral;
          if clause[k] == trueLiteral {
            assert getLiteralValue(oldTau, clause[k]) == 1;
          } else {
            ghost var v := getVariableFromLiteral(clause[k]);
            assert v != variable;
            assert getLiteralValue(oldTau, clause[k]) == 0 <==> getLiteralValue(newTau, clause[k]) == 0;
          }
        }
        k := k - 1;
      }
    }
  }

  lemma /*{:_induction this}*/ notDone_literalsToSet(i: SYInt32.t)
    requires valid()
    requires 0 <= i as int < |clauses|
    requires falseLiteralsCount[i] as int < |clauses[i]|
    requires trueLiteralsCount[i] == 0
    requires validClause(clauses[i])
    requires forall literal: SYInt32.t {:trigger validLiteral(literal)} {:trigger literal in clauses[i]} :: literal in clauses[i] ==> validLiteral(literal)
    ensures exists literal: SYInt32.t {:trigger getVariableFromLiteral(literal)} {:trigger literal in clauses[i]} :: literal in clauses[i] && truthAssignment[getVariableFromLiteral(literal)] == -1
    decreases i
  {
    assert forall literal: SYInt32.t {:trigger getLiteralValue(truthAssignment[..], literal)} {:trigger validLiteral(literal)} :: (validLiteral(literal) ==> -1 <= getLiteralValue(truthAssignment[..], literal)) && (validLiteral(literal) ==> getLiteralValue(truthAssignment[..], literal) <= 1);
    ghost var clause := clauses[i];
    countTrueLiterals0_noLiteralsTrue(truthAssignment[..], clause);
    if forall literal: SYInt32.t {:trigger getLiteralValue(truthAssignment[..], literal)} {:trigger literal in clause} :: literal in clause ==> getLiteralValue(truthAssignment[..], literal) == 0 {
      ghost var k := |clause| - 1;
      while k > 0
        invariant 0 <= k < |clause| == |clauses[i]|
        invariant countFalseLiterals(truthAssignment[..], clause[k..]) as int == |clause| - k
        decreases k
      {
        assert getLiteralValue(truthAssignment[..], clause[k]) == 0;
        k := k - 1;
      }
      assert countFalseLiterals(truthAssignment[..], clause) as int == |clauses[i]|;
      assert false;
    }
  }

  lemma /*{:_induction this, oldTau, newTau}*/ setVariable_unsetVariablesDecreasesWithOne(oldTau: seq<SYInt32.t>, newTau: seq<SYInt32.t>, variable: SYInt32.t)
    requires validVariablesCount()
    requires validVariable(variable)
    requires validValuesTruthAssignment(oldTau)
    requires validValuesTruthAssignment(newTau)
    requires |oldTau| == |newTau|
    requires forall i: SYInt32.t {:trigger newTau[i]} {:trigger oldTau[i]} :: 0 <= i as int < |oldTau| && i != variable ==> oldTau[i] == newTau[i]
    requires oldTau[variable] == -1
    requires newTau[variable] in [0, 1]
    requires countUnsetVariables(newTau) as int < |newTau|
    ensures countUnsetVariables(newTau) + 1 == countUnsetVariables(oldTau)
    decreases oldTau, newTau, variable
  {
    ghost var k := |newTau| - 1;
    while k > 0
      invariant 0 <= k < |newTau|
      invariant variable as int < k < |newTau| ==> countUnsetVariables(newTau[k..]) == countUnsetVariables(oldTau[k..])
      invariant 0 <= k <= variable as int ==> countUnsetVariables(newTau[k..]) + 1 == countUnsetVariables(oldTau[k..])
      decreases k - 0
    {
      k := k - 1;
    }
  }

  predicate isVariableSet(truthAssignment: seq<SYInt32.t>, variable: SYInt32.t)
    requires validVariablesCount()
    requires validValuesTruthAssignment(truthAssignment)
    requires validVariable(variable)
    reads this
    decreases {this}, truthAssignment, variable
  {
    truthAssignment[variable] != -1
  }

  predicate isSatisfied(truthAssignment: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(truthAssignment)
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}, truthAssignment
  {
    forall cI: SYInt32.t {:trigger isClauseSatisfied(truthAssignment, cI)} :: 
      0 <= cI as int < |clauses| ==>
        isClauseSatisfied(truthAssignment, cI)
  }

  predicate isExtendingTau(tau: seq<SYInt32.t>, tau': seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    requires validValuesTruthAssignment(tau')
    reads `variablesCount
    decreases {this}, tau, tau'
  {
    forall i: int {:trigger tau'[i]} {:trigger tau[i]} :: 
      0 <= i < |tau| &&
      tau[i] != -1 ==>
        tau[i] == tau'[i]
  }

  predicate isTauComplete(tau: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validValuesTruthAssignment(tau)
    reads `variablesCount
    decreases {this}, tau
  {
    forall i: int {:trigger tau[i]} :: 
      0 <= i < |tau| ==>
        tau[i] != -1
  }

  ghost predicate isSatisfiableExtend(tau: seq<SYInt32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}, tau
  {
    exists tau': seq<SYInt32.t> {:trigger isSatisfied(tau')} {:trigger isExtendingTau(tau, tau')} {:trigger isTauComplete(tau')} {:trigger validValuesTruthAssignment(tau')} :: 
      validValuesTruthAssignment(tau') &&
      isTauComplete(tau') &&
      isExtendingTau(tau, tau') &&
      isSatisfied(tau')
  }

  predicate isSatisfiableTruthAssignment(tau: seq<SYInt32.t>, tau': seq<SYInt32.t>)
    requires validVariablesCount()
    requires validClauses()
    requires validValuesTruthAssignment(tau)
    reads `variablesCount, `clauses, `clausesCount, `clauseLength, clauseLength
    decreases {this, this, this, this, clauseLength}, tau, tau'
  {
    validValuesTruthAssignment(tau') &&
    isExtendingTau(tau, tau') &&
    isSatisfied(tau')
  }

  function isUnitClause(index: SYInt32.t): bool
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires validTruthAssignment()
    requires validClauses()
    requires validTrueLiteralsCount(truthAssignment[..])
    requires validFalseLiteralsCount(truthAssignment[..])
    requires 0 <= index < clausesCount
    reads this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength
    decreases {this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength}, index
  {
    trueLiteralsCount[index] == 0 &&
    clauseLength[index] - falseLiteralsCount[index] == 1
  }

  function isEmptyClause(index: SYInt32.t): bool
    requires validVariablesCount()
    requires validAssignmentTrace()
    requires validTruthAssignment()
    requires validClauses()
    requires validTrueLiteralsCount(truthAssignment[..])
    requires validFalseLiteralsCount(truthAssignment[..])
    requires 0 <= index < clausesCount
    reads this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength
    decreases {this, traceVariable, traceValue, traceDLStart, traceDLEnd, truthAssignment, trueLiteralsCount, falseLiteralsCount, clauseLength}, index
  {
    clauseLength[index] == falseLiteralsCount[index]
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

// When --include-runtime is true, this file is directly prepended
// to the output program. We have to avoid these using directives in that case
// since they can only appear before any other declarations.
// The DafnyRuntime.csproj file is the only place that ISDAFNYRUNTIMELIB is defined,
// so these are only active when building the C# DafnyRuntime.dll library.
#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public static bool IsRune(BigInteger i) {
      return (0 <= i && i < 0xD800) || (0xE000 <= i && i < 0x11_0000);
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    BigInteger ElementCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t, out var i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }

      if (t is T && dict.TryGetValue((T)(object)t, out var m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount; }
    }
    public long LongCount {
      get { return (long)ElementCount; }
    }

    public BigInteger ElementCount {
      get {
        // This is inefficient
        var c = occurrencesOfNull;
        foreach (var item in dict) {
          c += item.Value;
        }
        return c;
      }
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }

    public static uint Bv32ShiftLeft(uint a, int amount) {
      return 32 <= amount ? 0 : a << amount;
    }
    public static ulong Bv64ShiftLeft(ulong a, int amount) {
      return 64 <= amount ? 0 : a << amount;
    }

    public static uint Bv32ShiftRight(uint a, int amount) {
      return 32 <= amount ? 0 : a >> amount;
    }
    public static ulong Bv64ShiftRight(ulong a, int amount) {
      return 64 <= amount ? 0 : a >> amount;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (DividesAPowerOf10(den, out var factor, out var log10)) {
        var n = num * factor;
        string sign;
        string digits;
        if (n.Sign < 0) {
          sign = "-"; digits = (-n).ToString();
        } else {
          sign = ""; digits = n.ToString();
        }
        if (log10 < digits.Length) {
          var digitCount = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, digitCount), digits.Substring(digitCount));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public static bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    /// <summary>
    /// If this method return true, then
    ///     10^log10 == factor * i
    /// Otherwise, factor and log10 should not be used.
    /// </summary>
    public static bool DividesAPowerOf10(BigInteger i, out BigInteger factor, out int log10) {
      factor = BigInteger.One;
      log10 = 0;
      if (i <= 0) {
        return false;
      }

      BigInteger ten = 10;
      BigInteger five = 5;
      BigInteger two = 2;

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i % ten == 0) {
        i /= ten;
        log10++;
      }

      while (i % five == 0) {
        i /= five;
        factor *= two;
        log10++;
      }
      while (i % two == 0) {
        i /= two;
        factor *= five;
        log10++;
      }

      return i == BigInteger.One;
    }

    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }

    public bool IsInteger() {
      var floored = new BigRational(this.ToBigInteger(), BigInteger.One);
      return this == floored;
    }

    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }

      Normalize(this, that, out var aa, out var bb, out var dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}
// Dafny program systemModulePopulator.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif
#if ISDAFNYRUNTIMELIB
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,] InitNewArray5<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      T[,,,,] a = new T[s0,s1,s2,s3,s4];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                a[i0,i1,i2,i3,i4] = z;
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,] InitNewArray6<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      T[,,,,,] a = new T[s0,s1,s2,s3,s4,s5];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  a[i0,i1,i2,i3,i4,i5] = z;
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,] InitNewArray7<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      T[,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    a[i0,i1,i2,i3,i4,i5,i6] = z;
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,] InitNewArray8<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      T[,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      a[i0,i1,i2,i3,i4,i5,i6,i7] = z;
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,] InitNewArray9<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      T[,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        a[i0,i1,i2,i3,i4,i5,i6,i7,i8] = z;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,] InitNewArray10<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      T[,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = z;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,] InitNewArray11<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      T[,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10] = z;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,] InitNewArray12<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      T[,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11] = z;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,] InitNewArray13<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      T[,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12] = z;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,] InitNewArray14<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      T[,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13] = z;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,] InitNewArray15<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      T[,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14] = z;
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,,] InitNewArray16<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14, BigInteger size15) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      int s15 = (int)size15;
      T[,,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    for (int i15 = 0; i15 < s15; i15++) {
                                      a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15] = z;
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, TResult, U1, U2, U3, U4, U5, U6, U7, U8, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<U16, T16> ArgConv16, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15), ArgConv16(arg16)));
  }
}
#endif
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(BigInteger __source) {
      BigInteger _0_x = __source;
      return (_0_x).Sign != -1;
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1);
  }
  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 __0;
    public readonly T1 __1;
    public Tuple2(T0 _0, T1 _1) {
      this.__0 = _0;
      this.__1 = _1;
    }
    public _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1) {
      if (this is _ITuple2<__T0, __T1> dt) { return dt; }
      return new Tuple2<__T0, __T1>(converter0(__0), converter1(__1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ")";
      return s;
    }
    public static _System._ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public static _ITuple2<T0, T1> create____hMake2(T0 _0, T1 _1) {
      return create(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _System._ITuple0 theDefault = create();
    public static _System._ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static _ITuple0 create____hMake0() {
      return create();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public interface _ITuple1<out T0> {
    T0 dtor__0 { get; }
    _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0);
  }
  public class Tuple1<T0> : _ITuple1<T0> {
    public readonly T0 __0;
    public Tuple1(T0 _0) {
      this.__0 = _0;
    }
    public _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0) {
      if (this is _ITuple1<__T0> dt) { return dt; }
      return new Tuple1<__T0>(converter0(__0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T0>;
      return oth != null && object.Equals(this.__0, oth.__0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ")";
      return s;
    }
    public static _System._ITuple1<T0> Default(T0 _default_T0) {
      return create(_default_T0);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T0>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T0>>(_System.Tuple1<T0>.Default(_td_T0.Default()));
    }
    public static _ITuple1<T0> create(T0 _0) {
      return new Tuple1<T0>(_0);
    }
    public static _ITuple1<T0> create____hMake1(T0 _0) {
      return create(_0);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(__0), converter1(__1), converter2(__2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ")";
      return s;
    }
    public static _System._ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public static _ITuple3<T0, T1, T2> create____hMake3(T0 _0, T1 _1, T2 _2) {
      return create(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(__0), converter1(__1), converter2(__2), converter3(__3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ")";
      return s;
    }
    public static _System._ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public static _ITuple4<T0, T1, T2, T3> create____hMake4(T0 _0, T1 _1, T2 _2, T3 _3) {
      return create(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ")";
      return s;
    }
    public static _System._ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create____hMake5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return create(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ")";
      return s;
    }
    public static _System._ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create____hMake6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return create(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ")";
      return s;
    }
    public static _System._ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create____hMake7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return create(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ")";
      return s;
    }
    public static _System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create____hMake8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ")";
      return s;
    }
    public static _System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create____hMake9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ")";
      return s;
    }
    public static _System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create____hMake10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ")";
      return s;
    }
    public static _System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create____hMake11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ")";
      return s;
    }
    public static _System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create____hMake12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ")";
      return s;
    }
    public static _System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create____hMake13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ")";
      return s;
    }
    public static _System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create____hMake14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ")";
      return s;
    }
    public static _System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create____hMake15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ")";
      return s;
    }
    public static _System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create____hMake16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ")";
      return s;
    }
    public static _System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create____hMake17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ")";
      return s;
    }
    public static _System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create____hMake18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ")";
      return s;
    }
    public static _System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create____hMake19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public readonly T19 __19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
      this.__19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18), converter19(__19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18) && object.Equals(this.__19, oth.__19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__19));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__19);
      s += ")";
      return s;
    }
    public static _System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create____hMake20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
    public T19 dtor__19 {
      get {
        return this.__19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
}
namespace SYInt32 {

  public partial class __default {
    public static BigInteger max { get {
      return new BigInteger(2000000);
    } }
    public static BigInteger min { get {
      return new BigInteger(-2000000);
    } }
  }

  public partial class t {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(int __source) {
      BigInteger _0_x = new BigInteger(__source);
      return ((new BigInteger(-2000000)) <= (_0_x)) && ((_0_x) < (new BigInteger(2000001)));
    }
  }
} // end of namespace SYInt32
namespace InputPredicate {

  public partial class __default {
    public static BigInteger countLiterals(Dafny.ISequence<Dafny.ISequence<int>> clauses) {
      BigInteger _1___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((clauses).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_1___accumulator);
      } else {
        _1___accumulator = (_1___accumulator) + (new BigInteger(((clauses).Select((new BigInteger((clauses).Count)) - (BigInteger.One))).Count));
        Dafny.ISequence<Dafny.ISequence<int>> _in0 = (clauses).Take((new BigInteger((clauses).Count)) - (BigInteger.One));
        clauses = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static bool checkClauses(int variablesCount, Dafny.ISequence<Dafny.ISequence<int>> clauses)
    {
      return ((InputPredicate.__default.countLiterals(clauses)) < (SYInt32.__default.max)) && (Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<int>>, int, bool>>((_2_clauses, _3_variablesCount) => Dafny.Helpers.Quantifier<Dafny.ISequence<int>>((_2_clauses).UniqueElements, true, (((_forall_var_0) => {
        Dafny.ISequence<int> _4_clause = (Dafny.ISequence<int>)_forall_var_0;
        return !((_2_clauses).Contains(_4_clause)) || ((((new BigInteger((_4_clause).Count)).Sign == 1) && ((new BigInteger((_4_clause).Count)) < (SYInt32.__default.max))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, int, bool>>((_5_clause, _6_variablesCount) => Dafny.Helpers.Quantifier<int>((_5_clause).UniqueElements, true, (((_forall_var_1) => {
          int _7_literal = (int)_forall_var_1;
          if (SYInt32.t._Is(_7_literal)) {
            return !((_5_clause).Contains(_7_literal)) || ((((_7_literal) < (0)) && (((0) < ((0) - (_7_literal))) && (((0) - (_7_literal)) <= (_6_variablesCount)))) || (((_7_literal) > (0)) && (((0) < (_7_literal)) && ((_7_literal) <= (_6_variablesCount)))));
          } else {
            return true;
          }
        }))))(_4_clause, _3_variablesCount)));
      }))))(clauses, variablesCount));
    }
    public static bool sortedClauses(Dafny.ISequence<Dafny.ISequence<int>> clauses) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<int>>, bool>>((_8_clauses) => Dafny.Helpers.Quantifier<Dafny.ISequence<int>>((_8_clauses).UniqueElements, true, (((_forall_var_2) => {
        Dafny.ISequence<int> _9_clause = (Dafny.ISequence<int>)_forall_var_2;
        return !((_8_clauses).Contains(_9_clause)) || (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, bool>>((_10_clause) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_10_clause).Count)), true, (((_forall_var_3) => {
          BigInteger _11_x = (BigInteger)_forall_var_3;
          return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange((_11_x) + (BigInteger.One), new BigInteger((_10_clause).Count)), true, (((_forall_var_4) => {
            BigInteger _12_y = (BigInteger)_forall_var_4;
            return !((((_11_x).Sign != -1) && ((_11_x) < (_12_y))) && ((_12_y) < (new BigInteger((_10_clause).Count)))) || (((_10_clause).Select(_11_x)) < ((_10_clause).Select(_12_y)));
          })));
        }))))(_9_clause));
      }))))(clauses);
    }
    public static bool valid(_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>> input) {
      return (((((0) < ((input).dtor__0)) && (((input).dtor__0) < ((int)(SYInt32.__default.max)))) && (((new BigInteger(((input).dtor__1).Count)).Sign == 1) && ((new BigInteger(((input).dtor__1).Count)) <= (SYInt32.__default.max)))) && (InputPredicate.__default.checkClauses((input).dtor__0, (input).dtor__1))) && (InputPredicate.__default.sortedClauses((input).dtor__1));
    }
  }
} // end of namespace InputPredicate
namespace MyDatatypes {


  public interface _IMaybe<T> {
    bool is_Error { get; }
    bool is_Just { get; }
    Dafny.ISequence<char> dtor_Error_a0 { get; }
    T dtor_value { get; }
    _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class Maybe<T> : _IMaybe<T> {
    public Maybe() {
    }
    public static MyDatatypes._IMaybe<T> Default() {
      return create_Error(Dafny.Sequence<char>.Empty);
    }
    public static Dafny.TypeDescriptor<MyDatatypes._IMaybe<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<MyDatatypes._IMaybe<T>>(MyDatatypes.Maybe<T>.Default());
    }
    public static _IMaybe<T> create_Error(Dafny.ISequence<char> _a0) {
      return new Maybe_Error<T>(_a0);
    }
    public static _IMaybe<T> create_Just(T @value) {
      return new Maybe_Just<T>(@value);
    }
    public bool is_Error { get { return this is Maybe_Error<T>; } }
    public bool is_Just { get { return this is Maybe_Just<T>; } }
    public Dafny.ISequence<char> dtor_Error_a0 {
      get {
        var d = this;
        return ((Maybe_Error<T>)d)._a0;
      }
    }
    public T dtor_value {
      get {
        var d = this;
        return ((Maybe_Just<T>)d)._value;
      }
    }
    public abstract _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Maybe_Error<T> : Maybe<T> {
    public readonly Dafny.ISequence<char> _a0;
    public Maybe_Error(Dafny.ISequence<char> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_Error<__T>(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as MyDatatypes.Maybe_Error<T>;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MyDatatypes.Maybe.Error";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Maybe_Just<T> : Maybe<T> {
    public readonly T _value;
    public Maybe_Just(T @value) : base() {
      this._value = @value;
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_Just<__T>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as MyDatatypes.Maybe_Just<T>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "MyDatatypes.Maybe.Just";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
} // end of namespace MyDatatypes
namespace Useless {

  public partial class __default {
    public static bool valid_k(Dafny.ISequence<char> c) {
      return ((new BigInteger((c).Count)).Sign == 1) && ((new BigInteger((c).Count)) < (SYInt32.__default.max));
    }
  }

  public partial class Parser {
    public Parser() {
      this.content = Dafny.Sequence<char>.Empty;
      this.contentLength = 0;
      this.cursor = 0;
    }
    public Dafny.ISequence<char> content {get; set;}
    public int contentLength {get; set;}
    public int cursor {get; set;}
    public void __ctor(Dafny.ISequence<char> c)
    {
      (this).content = c;
      (this).contentLength = (int)(c).Count;
      (this).cursor = 0;
    }
    public bool valid() {
      return ((Useless.__default.valid_k(this.content)) && ((new BigInteger(this.contentLength)) == (new BigInteger((this.content).Count)))) && (((0) <= (this.cursor)) && ((this.cursor) <= (this.contentLength)));
    }
    public void skipLine()
    {
      while (((this.cursor) < (this.contentLength)) && (((this.content).Select(this.cursor)) != ('\n'))) {
        (this).cursor = (this.cursor) + (1);
      }
      if ((this.cursor) < (this.contentLength)) {
        (this).cursor = (this.cursor) + (1);
      }
    }
    public void toNextNumber()
    {
      while (((this.cursor) < (this.contentLength)) && (!(((('0') <= ((this.content).Select(this.cursor))) && (((this.content).Select(this.cursor)) <= ('9'))) || (((this.content).Select(this.cursor)) == ('-'))))) {
        (this).cursor = (this.cursor) + (1);
      }
    }
    public MyDatatypes._IMaybe<int> extractNumber()
    {
      MyDatatypes._IMaybe<int> res = MyDatatypes.Maybe<int>.Default();
      int _13_number;
      _13_number = 0;
      bool _14_isNegative;
      _14_isNegative = false;
      if (((this.cursor) < (this.contentLength)) && (((this.content).Select(this.cursor)) == ('-'))) {
        _14_isNegative = true;
        (this).cursor = (this.cursor) + (1);
      }
      if ((this.cursor) == (this.contentLength)) {
        res = MyDatatypes.Maybe<int>.create_Error(Dafny.Sequence<char>.FromString("There is no number around here."));
        return res;
      }
      while (((this.cursor) < (this.contentLength)) && ((('0') <= ((this.content).Select(this.cursor))) && (((this.content).Select(this.cursor)) <= ('9')))) {
        int _15_digit;
        _15_digit = ((int)((this.content).Select(this.cursor))) - ((int)('0'));
        if ((_13_number) <= (Dafny.Helpers.EuclideanDivision_int(((int)(SYInt32.__default.max)) - (_15_digit), 10))) {
          _13_number = ((_13_number) * (10)) + (_15_digit);
        } else {
          res = MyDatatypes.Maybe<int>.create_Error(Dafny.Sequence<char>.FromString("There is a number bigger than SYInt32.max"));
          return res;
        }
        (this).cursor = (this.cursor) + (1);
      }
      if (_14_isNegative) {
        _13_number = (0) - (_13_number);
      }
      res = MyDatatypes.Maybe<int>.create_Just(_13_number);
      return res;
      return res;
    }
    public MyDatatypes._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> parse()
    {
      MyDatatypes._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.Default();
      int _16_variablesCount;
      _16_variablesCount = 0;
      int _17_clausesCount;
      _17_clausesCount = 0;
      Dafny.ISequence<Dafny.ISequence<int>> _18_clauses;
      _18_clauses = Dafny.Sequence<Dafny.ISequence<int>>.FromElements();
      int[] _19_clause;
      int[] _nw0 = new int[Dafny.Helpers.ToIntChecked(new BigInteger(1000), "array size exceeds memory limit")];
      _19_clause = _nw0;
      int _20_clauseLength;
      _20_clauseLength = 0;
      bool _21_ok;
      _21_ok = false;
      int _22_literalsCount;
      _22_literalsCount = 0;
      int _23_contentLength;
      _23_contentLength = (int)(this.content).Count;
      while ((this.cursor) < (_23_contentLength)) {
        int _24_oldCursor;
        _24_oldCursor = this.cursor;
        if (((this.content).Select(this.cursor)) == ('c')) {
          (this).skipLine();
        } else if ((((this.content).Select(this.cursor)) == ('p')) && ((_16_variablesCount) == (0))) {
          (this).toNextNumber();
          MyDatatypes._IMaybe<int> _25_x;
          MyDatatypes._IMaybe<int> _out0;
          _out0 = (this).extractNumber();
          _25_x = _out0;
          MyDatatypes._IMaybe<int> _source0 = _25_x;
          if (_source0.is_Error) {
            Dafny.ISequence<char> _26___mcc_h0 = _source0.dtor_Error_a0;
            Dafny.ISequence<char> _27_t = _26___mcc_h0;
            {
              result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(_27_t);
              return result;
            }
          } else {
            int _28___mcc_h1 = _source0.dtor_value;
            int _29_number = _28___mcc_h1;
            {
              if (((0) < (_29_number)) && ((_29_number) < ((int)(SYInt32.__default.max)))) {
                _16_variablesCount = _29_number;
                _21_ok = true;
              } else {
                result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("Variables count is bigger than SYInt32.max"));
                return result;
              }
            }
          }
          (this).toNextNumber();
          MyDatatypes._IMaybe<int> _out1;
          _out1 = (this).extractNumber();
          _25_x = _out1;
          MyDatatypes._IMaybe<int> _source1 = _25_x;
          if (_source1.is_Error) {
            Dafny.ISequence<char> _30___mcc_h2 = _source1.dtor_Error_a0;
            Dafny.ISequence<char> _31_t = _30___mcc_h2;
            {
              result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(_31_t);
              return result;
            }
          } else {
            int _32___mcc_h3 = _source1.dtor_value;
            int _33_number = _32___mcc_h3;
            {
              _17_clausesCount = _33_number;
            }
          }
          (this).skipLine();
        } else if (((this.content).Select(this.cursor)) == ('p')) {
          result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("Twice p? what are you doing?"));
          return result;
        } else if (_21_ok) {
          (this).toNextNumber();
          if (((_20_clauseLength) == (0)) && ((this.cursor) == (_23_contentLength))) {
            goto after_0;
          }
          MyDatatypes._IMaybe<int> _34_x;
          MyDatatypes._IMaybe<int> _out2;
          _out2 = (this).extractNumber();
          _34_x = _out2;
          MyDatatypes._IMaybe<int> _source2 = _34_x;
          if (_source2.is_Error) {
            Dafny.ISequence<char> _35___mcc_h4 = _source2.dtor_Error_a0;
            Dafny.ISequence<char> _36_t = _35___mcc_h4;
            {
              result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(_36_t);
              return result;
            }
          } else {
            int _37___mcc_h5 = _source2.dtor_value;
            int _38_number = _37___mcc_h5;
            {
              if (((_38_number) == (0)) && ((_20_clauseLength) > (0))) {
                _18_clauses = Dafny.Sequence<Dafny.ISequence<int>>.Concat(_18_clauses, Dafny.Sequence<Dafny.ISequence<int>>.FromElements(Dafny.Helpers.SeqFromArray(_19_clause).Take(_20_clauseLength)));
                if ((((int)(SYInt32.__default.max)) - (_20_clauseLength)) > (_22_literalsCount)) {
                  _22_literalsCount = (_22_literalsCount) + (_20_clauseLength);
                } else {
                  result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("The number of literals is to big"));
                  return result;
                }
                _20_clauseLength = 0;
              } else if ((_38_number) != (0)) {
                if ((_20_clauseLength) < (1000)) {
                  if ((((_38_number) < (0)) && (((0) < ((0) - (_38_number))) && (((0) - (_38_number)) <= (_16_variablesCount)))) || (((_38_number) > (0)) && (((0) < (_38_number)) && ((_38_number) <= (_16_variablesCount))))) {
                    (_19_clause)[(int)((_20_clauseLength))] = _38_number;
                    _20_clauseLength = (_20_clauseLength) + (1);
                    int _39_k;
                    _39_k = (_20_clauseLength) - (1);
                    while (((0) < (_39_k)) && (((_19_clause)[(int)((_39_k) - (1))]) > ((_19_clause)[(int)(_39_k)]))) {
                      int _40_aux;
                      _40_aux = (_19_clause)[(int)(_39_k)];
                      (_19_clause)[(int)((_39_k))] = (_19_clause)[(int)((_39_k) - (1))];
                      int _index0 = (_39_k) - (1);
                      (_19_clause)[(int)(_index0)] = _40_aux;
                      _39_k = (_39_k) - (1);
                    }
                    if (((_39_k) > (0)) && (((_19_clause)[(int)((_39_k) - (1))]) == ((_19_clause)[(int)(_39_k)]))) {
                      result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("duplice literal in clause"));
                      return result;
                    }
                  } else {
                    result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("literal bigger than variablesCount"));
                    return result;
                  }
                } else {
                  result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("clause longer than 1000"));
                  return result;
                }
              }
            }
          }
        }
        if (((this.cursor) < (_23_contentLength)) && ((_24_oldCursor) == (this.cursor))) {
          (this).cursor = (this.cursor) + (1);
        }
      continue_0: ;
      }
    after_0: ;
      if (!(((new BigInteger((_18_clauses).Count)).Sign == 1) && ((new BigInteger((_18_clauses).Count)) < (SYInt32.__default.max)))) {
        result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("number of clauses incorrect"));
        return result;
      }
      if ((new BigInteger((_18_clauses).Count)) != (new BigInteger(_17_clausesCount))) {
        result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("different number of clauses"));
        return result;
      }
      if (_21_ok) {
        result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Just(_System.Tuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>.create(_16_variablesCount, _18_clauses));
        return result;
      } else {
        result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("p not found"));
        return result;
      }
      return result;
    }
  }
} // end of namespace Useless
namespace FileInput {


} // end of namespace FileInput
namespace Input {

  public partial class __default {
    public static MyDatatypes._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> getInput()
    {
      MyDatatypes._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.Default();
      Dafny.ISequence<char> _41_input;
      _41_input = FileInput.Reader.getContent();
      if (((new BigInteger((_41_input).Count)).Sign == 1) && ((new BigInteger((_41_input).Count)) < (SYInt32.__default.max))) {
        Useless.Parser _42_parser;
        Useless.Parser _nw1 = new Useless.Parser();
        _nw1.__ctor(_41_input);
        _42_parser = _nw1;
        MyDatatypes._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _43_x;
        MyDatatypes._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _out3;
        _out3 = (_42_parser).parse();
        _43_x = _out3;
        result = _43_x;
        return result;
      } else {
        result = MyDatatypes.Maybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>>.create_Error(Dafny.Sequence<char>.FromString("the file contains more data than SYInt32.max"));
        return result;
      }
      return result;
    }
    public static BigInteger getTimestamp() {
      return FileInput.Reader.getTimestamp();
    }
  }
} // end of namespace Input
namespace Utils {

  public partial class __default {
    public static int[] newInitializedSeq(int n, int d)
    {
      int[] r = new int[0];
      int[] _nw2 = new int[Dafny.Helpers.ToIntChecked(n, "array size exceeds memory limit")];
      r = _nw2;
      int _44_index;
      _44_index = 0;
      while ((_44_index) < (n)) {
        (r)[(int)((_44_index))] = d;
        _44_index = (_44_index) + (1);
      }
      return r;
    }
    public static int abs(int literal) {
      if ((literal) < (0)) {
        return (0) - (literal);
      } else {
        return literal;
      }
    }
    public static bool valueBoundedBy(int @value, BigInteger min, BigInteger max)
    {
      return ((min) <= (new BigInteger(@value))) && ((new BigInteger(@value)) < (max));
    }
    public static bool valuesBoundedBy(Dafny.ISequence<int> s, BigInteger min, BigInteger max)
    {
      return (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, BigInteger, BigInteger, bool>>((_45_s, _46_min, _47_max) => Dafny.Helpers.Quantifier<int>((_45_s).UniqueElements, true, (((_forall_var_5) => {
        int _48_el = (int)_forall_var_5;
        if (SYInt32.t._Is(_48_el)) {
          return !((_45_s).Contains(_48_el)) || (Utils.__default.valueBoundedBy(_48_el, _46_min, _47_max));
        } else {
          return true;
        }
      }))))(s, min, max)) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, BigInteger, BigInteger, bool>>((_49_s, _50_min, _51_max) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_49_s).Count)), true, (((_forall_var_6) => {
        BigInteger _52_i = (BigInteger)_forall_var_6;
        return !(((_52_i).Sign != -1) && ((_52_i) < (new BigInteger((_49_s).Count)))) || (Utils.__default.valueBoundedBy((_49_s).Select(_52_i), _50_min, _51_max));
      }))))(s, min, max));
    }
    public static bool orderedAsc(Dafny.ISequence<int> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<int>, bool>>((_53_s) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_53_s).Count)), true, (((_forall_var_7) => {
        BigInteger _54_x = (BigInteger)_forall_var_7;
        return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange((_54_x) + (BigInteger.One), new BigInteger((_53_s).Count)), true, (((_forall_var_8) => {
          BigInteger _55_y = (BigInteger)_forall_var_8;
          return !((((_54_x).Sign != -1) && ((_54_x) < (_55_y))) && ((_55_y) < (new BigInteger((_53_s).Count)))) || (((_53_s).Select(_54_x)) < ((_53_s).Select(_55_y)));
        })));
      }))))(s);
    }
    public static bool InRange(int lo, int hi, int i)
    {
      return ((lo) <= (i)) && ((i) < (hi));
    }
    public static Dafny.ISet<int> RangeSet(int lo, int hi)
    {
      return Dafny.Helpers.Id<Func<int, int, Dafny.ISet<int>>>((_56_lo, _57_hi) => ((System.Func<Dafny.ISet<int>>)(() => {
        var _coll0 = new System.Collections.Generic.List<int>();
        foreach (int _compr_0 in SYInt32.t.IntegerRange(new BigInteger(-2000000), new BigInteger(2000001))) {
          int _58_i = (int)_compr_0;
          if (SYInt32.t._Is(_58_i)) {
            if ((((_56_lo) <= (_58_i)) && ((_58_i) < (_57_hi))) && (Utils.__default.InRange(_56_lo, _57_hi, _58_i))) {
              _coll0.Add(_58_i);
            }
          }
        }
        return Dafny.Set<int>.FromCollection(_coll0);
      }))())(lo, hi);
    }
  }
} // end of namespace Utils
namespace _module {

  public partial class __default {
    public static void _Main(Dafny.ISequence<Dafny.ISequence<char>> __noArgsParameter)
    {
      BigInteger _59_starttime;
      _59_starttime = Input.__default.getTimestamp();
      MyDatatypes._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _60_input;
      MyDatatypes._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _out4;
      _out4 = Input.__default.getInput();
      _60_input = _out4;
      Dafny.BigRational _61_totalTime;
      _61_totalTime = (new Dafny.BigRational(((Input.__default.getTimestamp()) - (_59_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("c Time to read: ")));
      Dafny.Helpers.Print((_61_totalTime));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("s\n")));
      MyDatatypes._IMaybe<_System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>>> _source3 = _60_input;
      if (_source3.is_Error) {
        Dafny.ISequence<char> _62___mcc_h0 = _source3.dtor_Error_a0;
        Dafny.ISequence<char> _63_m = _62___mcc_h0;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("c Error: ")));
        Dafny.Helpers.Print((_63_m));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      } else {
        _System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>> _64___mcc_h1 = _source3.dtor_value;
        _System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>> _65_z = _64___mcc_h1;
        _System._ITuple2<int, Dafny.ISequence<Dafny.ISequence<int>>> _let_tmp_rhs0 = _65_z;
        int _66_variablesCount = _let_tmp_rhs0.dtor__0;
        Dafny.ISequence<Dafny.ISequence<int>> _67_clauses = _let_tmp_rhs0.dtor__1;
        _59_starttime = Input.__default.getTimestamp();
        Formula _68_formula;
        Formula _nw3 = new Formula();
        _nw3.__ctor(_66_variablesCount, _67_clauses);
        _68_formula = _nw3;
        SATSolver _69_solver;
        SATSolver _nw4 = new SATSolver();
        _nw4.__ctor(_68_formula);
        _69_solver = _nw4;
        _61_totalTime = (new Dafny.BigRational(((Input.__default.getTimestamp()) - (_59_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("c Time to initialize: ")));
        Dafny.Helpers.Print((_61_totalTime));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("s\n")));
        _59_starttime = Input.__default.getTimestamp();
        _ISAT__UNSAT _70_solution;
        _ISAT__UNSAT _out5;
        _out5 = (_69_solver).start();
        _70_solution = _out5;
        _61_totalTime = (new Dafny.BigRational(((Input.__default.getTimestamp()) - (_59_starttime)), BigInteger.One)) / (new Dafny.BigRational(BigInteger.Parse("1000"), BigInteger.One));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("c Time to solve: ")));
        Dafny.Helpers.Print((_61_totalTime));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("s\n")));
        _ISAT__UNSAT _source4 = _70_solution;
        if (_source4.is_SAT) {
          Dafny.ISequence<int> _71___mcc_h2 = _source4.dtor_tau;
          Dafny.ISequence<int> _72_x = _71___mcc_h2;
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("s SATISFIABLE\n")));
        } else {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("s UNSATISFIABLE\n")));
        }
      }
    }
  }

  public interface _ISAT__UNSAT {
    bool is_SAT { get; }
    bool is_UNSAT { get; }
    Dafny.ISequence<int> dtor_tau { get; }
    _ISAT__UNSAT DowncastClone();
  }
  public abstract class SAT__UNSAT : _ISAT__UNSAT {
    public SAT__UNSAT() {
    }
    private static readonly _ISAT__UNSAT theDefault = create_SAT(Dafny.Sequence<int>.Empty);
    public static _ISAT__UNSAT Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_ISAT__UNSAT> _TYPE = new Dafny.TypeDescriptor<_ISAT__UNSAT>(SAT__UNSAT.Default());
    public static Dafny.TypeDescriptor<_ISAT__UNSAT> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISAT__UNSAT create_SAT(Dafny.ISequence<int> tau) {
      return new SAT__UNSAT_SAT(tau);
    }
    public static _ISAT__UNSAT create_UNSAT() {
      return new SAT__UNSAT_UNSAT();
    }
    public bool is_SAT { get { return this is SAT__UNSAT_SAT; } }
    public bool is_UNSAT { get { return this is SAT__UNSAT_UNSAT; } }
    public Dafny.ISequence<int> dtor_tau {
      get {
        var d = this;
        return ((SAT__UNSAT_SAT)d)._tau;
      }
    }
    public abstract _ISAT__UNSAT DowncastClone();
  }
  public class SAT__UNSAT_SAT : SAT__UNSAT {
    public readonly Dafny.ISequence<int> _tau;
    public SAT__UNSAT_SAT(Dafny.ISequence<int> tau) : base() {
      this._tau = tau;
    }
    public override _ISAT__UNSAT DowncastClone() {
      if (this is _ISAT__UNSAT dt) { return dt; }
      return new SAT__UNSAT_SAT(_tau);
    }
    public override bool Equals(object other) {
      var oth = other as SAT__UNSAT_SAT;
      return oth != null && object.Equals(this._tau, oth._tau);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tau));
      return (int) hash;
    }
    public override string ToString() {
      string s = "SAT_UNSAT.SAT";
      s += "(";
      s += Dafny.Helpers.ToString(this._tau);
      s += ")";
      return s;
    }
  }
  public class SAT__UNSAT_UNSAT : SAT__UNSAT {
    public SAT__UNSAT_UNSAT() : base() {
    }
    public override _ISAT__UNSAT DowncastClone() {
      if (this is _ISAT__UNSAT dt) { return dt; }
      return new SAT__UNSAT_UNSAT();
    }
    public override bool Equals(object other) {
      var oth = other as SAT__UNSAT_UNSAT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "SAT_UNSAT.UNSAT";
      return s;
    }
  }

  public partial class SATSolver {
    public SATSolver() {
      this.formula = default(Formula);
    }
    public Formula formula {get; set;}
    public void __ctor(Formula f_k)
    {
      (this).formula = f_k;
    }
    public _ISAT__UNSAT step(int literal, bool @value)
    {
      _ISAT__UNSAT result = SAT__UNSAT.Default();
      (this.formula).increaseDecisionLevel();
      (this.formula).setLiteral(literal, @value);
      _ISAT__UNSAT _out6;
      _out6 = (this).solve();
      result = _out6;
      (this.formula).revertLastDecisionLevel();
      result = result;
      return result;
      return result;
    }
    public _ISAT__UNSAT solve()
    {
      _ISAT__UNSAT result = SAT__UNSAT.Default();
      bool _73_hasEmptyClause;
      bool _out7;
      _out7 = (this.formula).getHasEmptyClause();
      _73_hasEmptyClause = _out7;
      if (_73_hasEmptyClause) {
        result = _module.SAT__UNSAT.create_UNSAT();
        return result;
      }
      bool _74_isEmpty;
      bool _out8;
      _out8 = (this.formula).getIsEmpty();
      _74_isEmpty = _out8;
      if (_74_isEmpty) {
        result = _module.SAT__UNSAT.create_SAT(Dafny.Helpers.SeqFromArray(this.formula.truthAssignment));
        result = result;
        return result;
      }
      int _75_literal;
      int _out9;
      _out9 = (this.formula).chooseLiteral();
      _75_literal = _out9;
      _ISAT__UNSAT _out10;
      _out10 = (this).step(_75_literal, true);
      result = _out10;
      if ((result).is_SAT) {
        result = result;
        return result;
      }
      _ISAT__UNSAT _out11;
      _out11 = (this).step(_75_literal, false);
      result = _out11;
      result = result;
      return result;
      return result;
    }
    public _ISAT__UNSAT start()
    {
      _ISAT__UNSAT result = SAT__UNSAT.Default();
      (this.formula).level0UnitPropagation();
      _ISAT__UNSAT _out12;
      _out12 = (this).solve();
      result = _out12;
      return result;
    }
  }

  public partial class Formula : DataStructures {
    public Formula() {
      this._variablesCount = 0;
      this._clauses = Dafny.Sequence<Dafny.ISequence<int>>.Empty;
      this._clausesCount = 0;
      this._clauseLength = new int[0];
      this._truthAssignment = new int[0];
      this._trueLiteralsCount = new int[0];
      this._falseLiteralsCount = new int[0];
      this._positiveLiteralsToClauses = new Dafny.ISequence<int>[0];
      this._negativeLiteralsToClauses = new Dafny.ISequence<int>[0];
      this._decisionLevel = 0;
      this._traceVariable = new int[0];
      this._traceValue = new bool[0];
      this._traceDLStart = new int[0];
      this._traceDLEnd = new int[0];
    }
    public int _variablesCount {get; set;}
    public int variablesCount {
      get {
        return this._variablesCount;
      }
      set {
        this._variablesCount = value;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<int>> _clauses {get; set;}
    public Dafny.ISequence<Dafny.ISequence<int>> clauses {
      get {
        return this._clauses;
      }
      set {
        this._clauses = value;
      }
    }
    public int _clausesCount {get; set;}
    public int clausesCount {
      get {
        return this._clausesCount;
      }
      set {
        this._clausesCount = value;
      }
    }
    public int[] _clauseLength {get; set;}
    public int[] clauseLength {
      get {
        return this._clauseLength;
      }
      set {
        this._clauseLength = value;
      }
    }
    public int[] _truthAssignment {get; set;}
    public int[] truthAssignment {
      get {
        return this._truthAssignment;
      }
      set {
        this._truthAssignment = value;
      }
    }
    public int[] _trueLiteralsCount {get; set;}
    public int[] trueLiteralsCount {
      get {
        return this._trueLiteralsCount;
      }
      set {
        this._trueLiteralsCount = value;
      }
    }
    public int[] _falseLiteralsCount {get; set;}
    public int[] falseLiteralsCount {
      get {
        return this._falseLiteralsCount;
      }
      set {
        this._falseLiteralsCount = value;
      }
    }
    public Dafny.ISequence<int>[] _positiveLiteralsToClauses {get; set;}
    public Dafny.ISequence<int>[] positiveLiteralsToClauses {
      get {
        return this._positiveLiteralsToClauses;
      }
      set {
        this._positiveLiteralsToClauses = value;
      }
    }
    public Dafny.ISequence<int>[] _negativeLiteralsToClauses {get; set;}
    public Dafny.ISequence<int>[] negativeLiteralsToClauses {
      get {
        return this._negativeLiteralsToClauses;
      }
      set {
        this._negativeLiteralsToClauses = value;
      }
    }
    public int _decisionLevel {get; set;}
    public int decisionLevel {
      get {
        return this._decisionLevel;
      }
      set {
        this._decisionLevel = value;
      }
    }
    public int[] _traceVariable {get; set;}
    public int[] traceVariable {
      get {
        return this._traceVariable;
      }
      set {
        this._traceVariable = value;
      }
    }
    public bool[] _traceValue {get; set;}
    public bool[] traceValue {
      get {
        return this._traceValue;
      }
      set {
        this._traceValue = value;
      }
    }
    public int[] _traceDLStart {get; set;}
    public int[] traceDLStart {
      get {
        return this._traceDLStart;
      }
      set {
        this._traceDLStart = value;
      }
    }
    public int[] _traceDLEnd {get; set;}
    public int[] traceDLEnd {
      get {
        return this._traceDLEnd;
      }
      set {
        this._traceDLEnd = value;
      }
    }
    public bool validVariablesCount() {
      return _Companion_DataStructures.validVariablesCount(this);
    }
    public bool validLiteral(int literal) {
      return _Companion_DataStructures.validLiteral(this, literal);
    }
    public bool validClause(Dafny.ISequence<int> clause) {
      return _Companion_DataStructures.validClause(this, clause);
    }
    public bool validClauses() {
      return _Companion_DataStructures.validClauses(this);
    }
    public bool validVariable(int variable) {
      return _Companion_DataStructures.validVariable(this, variable);
    }
    public bool validAssignmentTraceBasic() {
      return _Companion_DataStructures.validAssignmentTraceBasic(this);
    }
    public bool validTraceDL() {
      return _Companion_DataStructures.validTraceDL(this);
    }
    public bool validTraceVariable() {
      return _Companion_DataStructures.validTraceVariable(this);
    }
    public bool convertIntToBool(int x) {
      return _Companion_DataStructures.convertIntToBool(this, x);
    }
    public bool validValuesTruthAssignment(Dafny.ISequence<int> truthAssignment) {
      return _Companion_DataStructures.validValuesTruthAssignment(this, truthAssignment);
    }
    public int getLiteralValue(Dafny.ISequence<int> truthAssignment, int literal)
    {
      return _Companion_DataStructures.getLiteralValue(this, truthAssignment, literal);
    }
    public bool isClauseSatisfied(Dafny.ISequence<int> truthAssignment, int clauseIndex)
    {
      return _Companion_DataStructures.isClauseSatisfied(this, truthAssignment, clauseIndex);
    }
    public int getVariableFromLiteral(int literal) {
      return _Companion_DataStructures.getVariableFromLiteral(this, literal);
    }
    public _System._ITuple2<int, int> convertLVtoVI(int literal, bool @value)
    {
      return _Companion_DataStructures.convertLVtoVI(this, literal, @value);
    }
    public bool validTrueLiteralsCount(Dafny.ISequence<int> truthAssignment) {
      return _Companion_DataStructures.validTrueLiteralsCount(this, truthAssignment);
    }
    public int countUnsetVariables(Dafny.ISequence<int> truthAssignment) {
      return _Companion_DataStructures.countUnsetVariables(this, truthAssignment);
    }
    public int countTrueLiterals(Dafny.ISequence<int> truthAssignment, Dafny.ISequence<int> clause)
    {
      return _Companion_DataStructures.countTrueLiterals(this, truthAssignment, clause);
    }
    public bool validFalseLiteralsCount(Dafny.ISequence<int> truthAssignment) {
      return _Companion_DataStructures.validFalseLiteralsCount(this, truthAssignment);
    }
    public int countFalseLiterals(Dafny.ISequence<int> truthAssignment, Dafny.ISequence<int> clause)
    {
      return _Companion_DataStructures.countFalseLiterals(this, truthAssignment, clause);
    }
    public bool validPositiveLiteralsToClauses() {
      return _Companion_DataStructures.validPositiveLiteralsToClauses(this);
    }
    public bool validPositiveLiteralToClause(int variable, Dafny.ISequence<int> s)
    {
      return _Companion_DataStructures.validPositiveLiteralToClause(this, variable, s);
    }
    public bool validNegativeLiteralsToClauses() {
      return _Companion_DataStructures.validNegativeLiteralsToClauses(this);
    }
    public bool validNegativeLiteralsToClause(int variable, Dafny.ISequence<int> s)
    {
      return _Companion_DataStructures.validNegativeLiteralsToClause(this, variable, s);
    }
    public bool validReferences() {
      return _Companion_DataStructures.validReferences(this);
    }
    public BigInteger countLiterals(int clauseIndex) {
      return _Companion_DataStructures.countLiterals(this, clauseIndex);
    }
    public bool isVariableSet(Dafny.ISequence<int> truthAssignment, int variable)
    {
      return _Companion_DataStructures.isVariableSet(this, truthAssignment, variable);
    }
    public bool isSatisfied(Dafny.ISequence<int> truthAssignment) {
      return _Companion_DataStructures.isSatisfied(this, truthAssignment);
    }
    public bool isExtendingTau(Dafny.ISequence<int> tau, Dafny.ISequence<int> tau_k)
    {
      return _Companion_DataStructures.isExtendingTau(this, tau, tau_k);
    }
    public bool isTauComplete(Dafny.ISequence<int> tau) {
      return _Companion_DataStructures.isTauComplete(this, tau);
    }
    public bool isSatisfiableTruthAssignment(Dafny.ISequence<int> tau, Dafny.ISequence<int> tau_k)
    {
      return _Companion_DataStructures.isSatisfiableTruthAssignment(this, tau, tau_k);
    }
    public bool isUnitClause(int index) {
      return _Companion_DataStructures.isUnitClause(this, index);
    }
    public bool isEmptyClause(int index) {
      return _Companion_DataStructures.isEmptyClause(this, index);
    }
    public void __ctor(int variablesCount, Dafny.ISequence<Dafny.ISequence<int>> clauses)
    {
      (this)._variablesCount = variablesCount;
      (this)._clauses = clauses;
      (this)._decisionLevel = -1;
      int[] _nw5 = new int[Dafny.Helpers.ToIntChecked(variablesCount, "array size exceeds memory limit")];
      (this)._traceVariable = _nw5;
      bool[] _nw6 = new bool[Dafny.Helpers.ToIntChecked(variablesCount, "array size exceeds memory limit")];
      (this)._traceValue = _nw6;
      int[] _nw7 = new int[Dafny.Helpers.ToIntChecked(variablesCount, "array size exceeds memory limit")];
      (this)._traceDLStart = _nw7;
      int[] _nw8 = new int[Dafny.Helpers.ToIntChecked(variablesCount, "array size exceeds memory limit")];
      (this)._traceDLEnd = _nw8;
      int _76_clsLength;
      _76_clsLength = (int)(clauses).Count;
      (this)._clausesCount = _76_clsLength;
      int[] _nw9 = new int[Dafny.Helpers.ToIntChecked(_76_clsLength, "array size exceeds memory limit")];
      (this)._clauseLength = _nw9;
      int[] _nw10 = new int[Dafny.Helpers.ToIntChecked(_76_clsLength, "array size exceeds memory limit")];
      (this)._trueLiteralsCount = _nw10;
      int[] _nw11 = new int[Dafny.Helpers.ToIntChecked(_76_clsLength, "array size exceeds memory limit")];
      (this)._falseLiteralsCount = _nw11;
      Dafny.ISequence<int>[] _nw12 = Dafny.ArrayHelpers.InitNewArray1<Dafny.ISequence<int>>(Dafny.Sequence<int>.Empty, Dafny.Helpers.ToIntChecked(variablesCount, "array size exceeds memory limit"));
      (this)._positiveLiteralsToClauses = _nw12;
      Dafny.ISequence<int>[] _nw13 = Dafny.ArrayHelpers.InitNewArray1<Dafny.ISequence<int>>(Dafny.Sequence<int>.Empty, Dafny.Helpers.ToIntChecked(variablesCount, "array size exceeds memory limit"));
      (this)._negativeLiteralsToClauses = _nw13;
      int[] _nw14 = new int[Dafny.Helpers.ToIntChecked(variablesCount, "array size exceeds memory limit")];
      (this)._truthAssignment = _nw14;
      int _77_k;
      _77_k = 0;
      while ((_77_k) < (this.clausesCount)) {
        int[] _arr0 = this.clauseLength;
        _arr0[(int)((_77_k))] = (int)((this.clauses).Select(_77_k)).Count;
        _77_k = (_77_k) + (1);
      }
      int _78_index;
      _78_index = 0;
      while ((_78_index) < (variablesCount)) {
        int[] _arr1 = this.truthAssignment;
        _arr1[(int)((_78_index))] = -1;
        _78_index = (_78_index) + (1);
      }
      (this).createTFLArrays();
      (this).createPositiveLiteralsToClauses();
      (this).createNegativeLiteralsToClauses();
    }
    public void createTFLArrays()
    {
      int _79_i;
      _79_i = 0;
      while ((_79_i) < (this.clausesCount)) {
        int[] _arr2 = this.trueLiteralsCount;
        _arr2[(int)((_79_i))] = 0;
        int[] _arr3 = this.falseLiteralsCount;
        _arr3[(int)((_79_i))] = 0;
        _79_i = (_79_i) + (1);
      }
    }
    public void createPositiveLiteralsToClauses()
    {
      int _80_variable;
      _80_variable = 0;
      while ((_80_variable) < (this.variablesCount)) {
        Dafny.ISequence<int>[] _arr4 = this.positiveLiteralsToClauses;
        _arr4[(int)((_80_variable))] = Dafny.Sequence<int>.FromElements();
        int _81_clauseIndex;
        _81_clauseIndex = 0;
        while ((_81_clauseIndex) < (this.clausesCount)) {
          if (((this.clauses).Select(_81_clauseIndex)).Contains((_80_variable) + (1))) {
            Dafny.ISequence<int>[] _arr5 = this.positiveLiteralsToClauses;
            _arr5[(int)((_80_variable))] = Dafny.Sequence<int>.Concat((this.positiveLiteralsToClauses)[(int)(_80_variable)], Dafny.Sequence<int>.FromElements(_81_clauseIndex));
          }
          _81_clauseIndex = (_81_clauseIndex) + (1);
        }
        _80_variable = (_80_variable) + (1);
      }
    }
    public void createNegativeLiteralsToClauses()
    {
      int _82_variable;
      _82_variable = 0;
      while ((_82_variable) < (this.variablesCount)) {
        Dafny.ISequence<int>[] _arr6 = this.negativeLiteralsToClauses;
        _arr6[(int)((_82_variable))] = Dafny.Sequence<int>.FromElements();
        int _83_clauseIndex;
        _83_clauseIndex = 0;
        while ((_83_clauseIndex) < (this.clausesCount)) {
          if (((this.clauses).Select(_83_clauseIndex)).Contains(((0) - (_82_variable)) - (1))) {
            Dafny.ISequence<int>[] _arr7 = this.negativeLiteralsToClauses;
            _arr7[(int)((_82_variable))] = Dafny.Sequence<int>.Concat((this.negativeLiteralsToClauses)[(int)(_82_variable)], Dafny.Sequence<int>.FromElements(_83_clauseIndex));
          }
          _83_clauseIndex = (_83_clauseIndex) + (1);
        }
        _82_variable = (_82_variable) + (1);
      }
    }
    public void revertLastDecisionLevel()
    {
      while (((this.traceDLStart)[(int)(this.decisionLevel)]) < ((this.traceDLEnd)[(int)(this.decisionLevel)])) {
        (this).removeLastVariable();
      }
      (this).decisionLevel = (this.decisionLevel) - (1);
    }
    public void removeLastVariable()
    {
      int _84_k;
      _84_k = ((this.traceDLEnd)[(int)(this.decisionLevel)]) - (1);
      int _85_variable;
      _85_variable = (this.traceVariable)[(int)(_84_k)];
      bool _86_value;
      _86_value = (this.traceValue)[(int)(_84_k)];
      int[] _arr8 = this.traceDLEnd;
      int _index1 = this.decisionLevel;
      _arr8[(int)(_index1)] = _84_k;
      int[] _arr9 = this.truthAssignment;
      _arr9[(int)((_85_variable))] = -1;
      Dafny.ISequence<int> _87_positivelyImpactedClauses;
      _87_positivelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(_85_variable)];
      Dafny.ISequence<int> _88_negativelyImpactedClauses;
      _88_negativelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(_85_variable)];
      if (!(_86_value)) {
        _88_negativelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(_85_variable)];
        _87_positivelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(_85_variable)];
      }
      int _89_i;
      _89_i = 0;
      int _90_len;
      _90_len = (int)(_87_positivelyImpactedClauses).Count;
      while ((_89_i) < (_90_len)) {
        int _91_clauseIndex;
        _91_clauseIndex = (_87_positivelyImpactedClauses).Select(_89_i);
        int[] _arr10 = this.trueLiteralsCount;
        _arr10[(int)((_91_clauseIndex))] = ((this.trueLiteralsCount)[(int)(_91_clauseIndex)]) - (1);
        _89_i = (_89_i) + (1);
      }
      _89_i = 0;
      _90_len = (int)(_88_negativelyImpactedClauses).Count;
      {
        while ((_89_i) < (_90_len)) {
          int _92_clauseIndex;
          _92_clauseIndex = (_88_negativelyImpactedClauses).Select(_89_i);
          int[] _arr11 = this.falseLiteralsCount;
          _arr11[(int)((_92_clauseIndex))] = ((this.falseLiteralsCount)[(int)(_92_clauseIndex)]) - (1);
          _89_i = (_89_i) + (1);
        }
      }
    }
    public void setVariable(int variable, bool @value)
    {
      (this).addAssignment(variable, @value);
      if (@value) {
        int[] _arr12 = this.truthAssignment;
        _arr12[(int)((variable))] = 1;
      } else {
        int[] _arr13 = this.truthAssignment;
        _arr13[(int)((variable))] = 0;
      }
      int _93_i;
      _93_i = 0;
      Dafny.ISequence<int> _94_impactedClauses;
      _94_impactedClauses = (this.positiveLiteralsToClauses)[(int)(variable)];
      Dafny.ISequence<int> _95_impactedClauses_k;
      _95_impactedClauses_k = (this.negativeLiteralsToClauses)[(int)(variable)];
      if (!(@value)) {
        _94_impactedClauses = (this.negativeLiteralsToClauses)[(int)(variable)];
        _95_impactedClauses_k = (this.positiveLiteralsToClauses)[(int)(variable)];
      }
      int _96_impactedClausesLen;
      _96_impactedClausesLen = (int)(_94_impactedClauses).Count;
      while ((_93_i) < (_96_impactedClausesLen)) {
        int _97_clauseIndex;
        _97_clauseIndex = (_94_impactedClauses).Select(_93_i);
        int[] _arr14 = this.trueLiteralsCount;
        _arr14[(int)((_97_clauseIndex))] = ((this.trueLiteralsCount)[(int)(_97_clauseIndex)]) + (1);
        _93_i = (_93_i) + (1);
      }
      int _98_i_k;
      _98_i_k = 0;
      int _99_impactedClausesLen_k;
      _99_impactedClausesLen_k = (int)(_95_impactedClauses_k).Count;
      while ((_98_i_k) < (_99_impactedClausesLen_k)) {
        int _100_clauseIndex;
        _100_clauseIndex = (_95_impactedClauses_k).Select(_98_i_k);
        int[] _arr15 = this.falseLiteralsCount;
        _arr15[(int)((_100_clauseIndex))] = ((this.falseLiteralsCount)[(int)(_100_clauseIndex)]) + (1);
        _98_i_k = (_98_i_k) + (1);
      }
    }
    public void addAssignment(int variable, bool @value)
    {
      int[] _arr16 = this.traceVariable;
      int _index2 = (this.traceDLEnd)[(int)(this.decisionLevel)];
      _arr16[(int)(_index2)] = variable;
      bool[] _arr17 = this.traceValue;
      int _index3 = (this.traceDLEnd)[(int)(this.decisionLevel)];
      _arr17[(int)(_index3)] = @value;
      int[] _arr18 = this.traceDLEnd;
      int _index4 = this.decisionLevel;
      _arr18[(int)(_index4)] = ((this.traceDLEnd)[(int)(this.decisionLevel)]) + (1);
    }
    public void increaseDecisionLevel()
    {
      (this).decisionLevel = (this.decisionLevel) + (1);
      int _101_previous;
      _101_previous = 0;
      if ((this.decisionLevel) == (0)) {
        _101_previous = 0;
      } else {
        _101_previous = (this.traceDLEnd)[(int)((this.decisionLevel) - (1))];
      }
      int[] _arr19 = this.traceDLStart;
      int _index5 = this.decisionLevel;
      _arr19[(int)(_index5)] = _101_previous;
      int[] _arr20 = this.traceDLEnd;
      int _index6 = this.decisionLevel;
      _arr20[(int)(_index6)] = _101_previous;
    }
    public int extractUnsetLiteralFromClause(int clauseIndex)
    {
      int literal = 0;
      int _102_i;
      _102_i = 0;
      Dafny.ISequence<int> _103_clause;
      _103_clause = (this.clauses).Select(clauseIndex);
      while ((_102_i) < ((this.clauseLength)[(int)(clauseIndex)])) {
        if (((this.truthAssignment)[(int)((this).getVariableFromLiteral((_103_clause).Select(_102_i)))]) == (-1)) {
          literal = (_103_clause).Select(_102_i);
          return literal;
        }
        _102_i = (_102_i) + (1);
      }
      return literal;
    }
    public void propagate(int clauseIndex)
    {
      int _104_literal;
      int _out13;
      _out13 = (this).extractUnsetLiteralFromClause(clauseIndex);
      _104_literal = _out13;
      Dafny.ISequence<int> _105_clause;
      _105_clause = (this.clauses).Select(clauseIndex);
      (this).setLiteral(_104_literal, true);
    }
    public void unitPropagation(int variable, bool @value)
    {
      Dafny.ISequence<int> _106_negativelyImpactedClauses;
      _106_negativelyImpactedClauses = (this.negativeLiteralsToClauses)[(int)(variable)];
      if (!(@value)) {
        _106_negativelyImpactedClauses = (this.positiveLiteralsToClauses)[(int)(variable)];
      }
      int _107_k;
      _107_k = 0;
      int _108_negativelyImpactedClausesLen;
      _108_negativelyImpactedClausesLen = (int)(_106_negativelyImpactedClauses).Count;
      while ((_107_k) < (_108_negativelyImpactedClausesLen)) {
        int _109_clauseIndex;
        _109_clauseIndex = (_106_negativelyImpactedClauses).Select(_107_k);
        if (((this.falseLiteralsCount)[(int)(_109_clauseIndex)]) < ((this.clauseLength)[(int)(_109_clauseIndex)])) {
          if ((((this.trueLiteralsCount)[(int)(_109_clauseIndex)]) == (0)) && ((((this.falseLiteralsCount)[(int)(_109_clauseIndex)]) + (1)) == ((this.clauseLength)[(int)(_109_clauseIndex)]))) {
            (this).propagate(_109_clauseIndex);
          }
        }
        _107_k = (_107_k) + (1);
      }
    }
    public void setLiteral(int literal, bool @value)
    {
      int _110_variable;
      _110_variable = (this).getVariableFromLiteral(literal);
      bool _111_value_k;
      _111_value_k = (((literal) > (0)) ? (@value) : (!(@value)));
      (this).setVariable(_110_variable, _111_value_k);
      (this).unitPropagation(_110_variable, _111_value_k);
    }
    public int chooseLiteral()
    {
      int x = 0;
      int _112_minim;
      _112_minim = (int)(SYInt32.__default.max);
      int _113_counter;
      _113_counter = 0;
      int _114_result;
      _114_result = -1;
      bool _115_ok;
      _115_ok = false;
      int _116_cI;
      _116_cI = 0;
      while ((_116_cI) < (this.clausesCount)) {
        int _117_diff;
        _117_diff = ((this.clauseLength)[(int)(_116_cI)]) - ((this.falseLiteralsCount)[(int)(_116_cI)]);
        if ((((this.trueLiteralsCount)[(int)(_116_cI)]) == (0)) && ((_117_diff) < (_112_minim))) {
          _112_minim = _117_diff;
        }
        if ((((this.trueLiteralsCount)[(int)(_116_cI)]) == (0)) && ((_117_diff) == (_112_minim))) {
          int _118_lI;
          _118_lI = 0;
          while ((_118_lI) < ((this.clauseLength)[(int)(_116_cI)])) {
            int _119_variable;
            _119_variable = (this).getVariableFromLiteral(((this.clauses).Select(_116_cI)).Select(_118_lI));
            if (((this.truthAssignment)[(int)(_119_variable)]) == (-1)) {
              _115_ok = true;
              if ((_113_counter) == (0)) {
                _114_result = (_119_variable) + (1);
                _113_counter = (_113_counter) + (1);
              } else if ((_114_result) == ((_119_variable) + (1))) {
                _113_counter = (_113_counter) + (1);
              } else {
                _113_counter = (_113_counter) - (1);
              }
            }
            _118_lI = (_118_lI) + (1);
          }
        }
        _116_cI = (_116_cI) + (1);
      }
      x = (0) - (_114_result);
      return x;
      return x;
    }
    public bool hasEmptyClause() {
      if (Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001)), false, (((_exists_var_0) => {
        int _120_i = (int)_exists_var_0;
        if (SYInt32.t._Is(_120_i)) {
          return (((0) <= (_120_i)) && ((_120_i) < (this.clausesCount))) && (((this.falseLiteralsCount)[(int)(_120_i)]) == ((this.clauseLength)[(int)(_120_i)]));
        } else {
          return false;
        }
      })))) {
        return Dafny.Helpers.Let<int, bool>(0, _let_dummy_0 =>  {
          int _120_i = default(int);
          foreach (int _assign_such_that_0 in SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001))) {
            _120_i = (int)_assign_such_that_0;
            if (SYInt32.t._Is(_120_i)) {
              if ((((0) <= (_120_i)) && ((_120_i) < (this.clausesCount))) && (((this.falseLiteralsCount)[(int)(_120_i)]) == ((this.clauseLength)[(int)(_120_i)]))) {
                goto after__ASSIGN_SUCH_THAT_0;
              }
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 1241)");
        after__ASSIGN_SUCH_THAT_0: ;
          return true;
        }
        );
      } else {
        return false;
      }
    }
    public bool getHasEmptyClause()
    {
      bool ok = false;
      int _121_k;
      _121_k = 0;
      while ((_121_k) < (this.clausesCount)) {
        if (((this.falseLiteralsCount)[(int)(_121_k)]) == ((this.clauseLength)[(int)(_121_k)])) {
          ok = true;
          return ok;
        }
        _121_k = (_121_k) + (1);
      }
      ok = false;
      return ok;
      return ok;
    }
    public bool isEmpty() {
      if (Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001)), false, (((_exists_var_1) => {
        int _122_i = (int)_exists_var_1;
        if (SYInt32.t._Is(_122_i)) {
          return (((0) <= (_122_i)) && ((_122_i) < (this.clausesCount))) && (((this.trueLiteralsCount)[(int)(_122_i)]) == (0));
        } else {
          return false;
        }
      })))) {
        return Dafny.Helpers.Let<int, bool>(0, _let_dummy_1 =>  {
          int _122_i = default(int);
          foreach (int _assign_such_that_1 in SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001))) {
            _122_i = (int)_assign_such_that_1;
            if (SYInt32.t._Is(_122_i)) {
              if ((((0) <= (_122_i)) && ((_122_i) < (this.clausesCount))) && (((this.trueLiteralsCount)[(int)(_122_i)]) == (0))) {
                goto after__ASSIGN_SUCH_THAT_1;
              }
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 1287)");
        after__ASSIGN_SUCH_THAT_1: ;
          return false;
        }
        );
      } else {
        return true;
      }
    }
    public bool getIsEmpty()
    {
      bool ok = false;
      int _123_k;
      _123_k = 0;
      while ((_123_k) < (this.clausesCount)) {
        if (((this.trueLiteralsCount)[(int)(_123_k)]) == (0)) {
          ok = false;
          return ok;
        }
        _123_k = (_123_k) + (1);
      }
      ok = true;
      return ok;
      return ok;
    }
    public void level0UnitPropagation()
    {
      int _124_i;
      _124_i = 0;
      (this).increaseDecisionLevel();
      while ((_124_i) < (this.clausesCount)) {
        if ((((this.trueLiteralsCount)[(int)(_124_i)]) == (0)) && ((((this.falseLiteralsCount)[(int)(_124_i)]) + (1)) == ((this.clauseLength)[(int)(_124_i)]))) {
          (this).propagate(_124_i);
        }
        _124_i = (_124_i) + (1);
      }
      if (((this.traceDLStart)[(int)(this.decisionLevel)]) == ((this.traceDLEnd)[(int)(this.decisionLevel)])) {
        (this).revertLastDecisionLevel();
      }
    }
    public bool occursInTrace(int variable) {
      return Dafny.Helpers.Id<Func<int, bool>>((_125_variable) => Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001)), false, (((_exists_var_2) => {
        int _126_j = (int)_exists_var_2;
        if (SYInt32.t._Is(_126_j)) {
          return (((0) <= (_126_j)) && ((_126_j) < ((this.traceDLEnd)[(int)(this.decisionLevel)]))) && (((this.traceVariable)[(int)(_126_j)]) == (_125_variable));
        } else {
          return false;
        }
      }))))(variable);
    }
  }

  public interface DataStructures {
    int variablesCount { get; set; }
    Dafny.ISequence<Dafny.ISequence<int>> clauses { get; set; }
    int clausesCount { get; set; }
    int[] clauseLength { get; set; }
    int[] truthAssignment { get; set; }
    int[] trueLiteralsCount { get; set; }
    int[] falseLiteralsCount { get; set; }
    Dafny.ISequence<int>[] positiveLiteralsToClauses { get; set; }
    Dafny.ISequence<int>[] negativeLiteralsToClauses { get; set; }
    int decisionLevel { get; set; }
    int[] traceVariable { get; set; }
    bool[] traceValue { get; set; }
    int[] traceDLStart { get; set; }
    int[] traceDLEnd { get; set; }
    bool validVariablesCount();
    bool validLiteral(int literal);
    bool validClause(Dafny.ISequence<int> clause);
    bool validClauses();
    bool validVariable(int variable);
    bool validAssignmentTraceBasic();
    bool validTraceDL();
    bool validTraceVariable();
    bool convertIntToBool(int x);
    bool validValuesTruthAssignment(Dafny.ISequence<int> truthAssignment);
    int getLiteralValue(Dafny.ISequence<int> truthAssignment, int literal);
    bool isClauseSatisfied(Dafny.ISequence<int> truthAssignment, int clauseIndex);
    int getVariableFromLiteral(int literal);
    _System._ITuple2<int, int> convertLVtoVI(int literal, bool @value);
    bool validTrueLiteralsCount(Dafny.ISequence<int> truthAssignment);
    int countUnsetVariables(Dafny.ISequence<int> truthAssignment);
    int countTrueLiterals(Dafny.ISequence<int> truthAssignment, Dafny.ISequence<int> clause);
    bool validFalseLiteralsCount(Dafny.ISequence<int> truthAssignment);
    int countFalseLiterals(Dafny.ISequence<int> truthAssignment, Dafny.ISequence<int> clause);
    bool validPositiveLiteralsToClauses();
    bool validPositiveLiteralToClause(int variable, Dafny.ISequence<int> s);
    bool validNegativeLiteralsToClauses();
    bool validNegativeLiteralsToClause(int variable, Dafny.ISequence<int> s);
    bool validReferences();
    BigInteger countLiterals(int clauseIndex);
    bool isVariableSet(Dafny.ISequence<int> truthAssignment, int variable);
    bool isSatisfied(Dafny.ISequence<int> truthAssignment);
    bool isExtendingTau(Dafny.ISequence<int> tau, Dafny.ISequence<int> tau_k);
    bool isTauComplete(Dafny.ISequence<int> tau);
    bool isSatisfiableTruthAssignment(Dafny.ISequence<int> tau, Dafny.ISequence<int> tau_k);
    bool isUnitClause(int index);
    bool isEmptyClause(int index);
  }
  public class _Companion_DataStructures {
    public static bool validVariablesCount(DataStructures _this) {
      return ((0) < (_this.variablesCount)) && ((_this.variablesCount) < ((int)(SYInt32.__default.max)));
    }
    public static bool validLiteral(DataStructures _this, int literal) {
      if ((literal) == (0)) {
        return false;
      } else if ((((0) - (_this.variablesCount)) <= (literal)) && ((literal) <= (_this.variablesCount))) {
        return true;
      } else {
        return false;
      }
    }
    public static bool validClause(DataStructures _this, Dafny.ISequence<int> clause) {
      return (((new BigInteger((clause).Count)) < (SYInt32.__default.max)) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, bool>>((_127_clause) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_127_clause).Count)), true, (((_forall_var_9) => {
        BigInteger _128_x = (BigInteger)_forall_var_9;
        return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange((_128_x) + (BigInteger.One), new BigInteger((_127_clause).Count)), true, (((_forall_var_10) => {
          BigInteger _129_y = (BigInteger)_forall_var_10;
          return !((((_128_x).Sign != -1) && ((_128_x) < (_129_y))) && ((_129_y) < (new BigInteger((_127_clause).Count)))) || (((_127_clause).Select(_128_x)) != ((_127_clause).Select(_129_y)));
        })));
      }))))(clause))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, bool>>((_130_clause) => Dafny.Helpers.Quantifier<int>((_130_clause).UniqueElements, true, (((_forall_var_11) => {
        int _131_literal = (int)_forall_var_11;
        if (SYInt32.t._Is(_131_literal)) {
          return !((_130_clause).Contains(_131_literal)) || ((_this).validLiteral(_131_literal));
        } else {
          return true;
        }
      }))))(clause));
    }
    public static bool validClauses(DataStructures _this) {
      return ((((((new BigInteger((_this.clauses).Count)).Sign == 1) && ((new BigInteger((_this.clauses).Count)) == (new BigInteger(_this.clausesCount)))) && ((new BigInteger(_this.clausesCount)) <= (SYInt32.__default.max))) && ((new BigInteger((_this.clauseLength).Length)) == (new BigInteger(_this.clausesCount)))) && (Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001)), true, (((_forall_var_12) => {
        int _132_i = (int)_forall_var_12;
        if (SYInt32.t._Is(_132_i)) {
          return !(((0) <= (_132_i)) && ((_132_i) < (_this.clausesCount))) || ((((new BigInteger((_this.clauseLength)[(int)(_132_i)])).Sign == 1) && ((new BigInteger((_this.clauseLength)[(int)(_132_i)])) == (new BigInteger(((_this.clauses).Select(_132_i)).Count)))) && ((new BigInteger(((_this.clauses).Select(_132_i)).Count)) < (SYInt32.__default.max)));
        } else {
          return true;
        }
      }))))) && (Dafny.Helpers.Quantifier<Dafny.ISequence<int>>((_this.clauses).UniqueElements, true, (((_forall_var_13) => {
        Dafny.ISequence<int> _133_clause = (Dafny.ISequence<int>)_forall_var_13;
        return !((_this.clauses).Contains(_133_clause)) || ((_this).validClause(_133_clause));
      }))));
    }
    public static bool validVariable(DataStructures _this, int variable) {
      return ((0) <= (variable)) && ((variable) < (_this.variablesCount));
    }
    public static bool validAssignmentTraceBasic(DataStructures _this) {
      return ((((((((((0) < (_this.variablesCount)) && ((_this.variablesCount) < ((int)(SYInt32.__default.max)))) && (((-1) <= (_this.decisionLevel)) && ((_this.decisionLevel) < (_this.variablesCount)))) && ((new BigInteger((_this.traceVariable).Length)) == (new BigInteger(_this.variablesCount)))) && ((new BigInteger((_this.traceValue).Length)) == (new BigInteger(_this.variablesCount)))) && ((new BigInteger((_this.traceDLStart).Length)) == (new BigInteger(_this.variablesCount)))) && ((new BigInteger((_this.traceDLEnd).Length)) == (new BigInteger(_this.variablesCount)))) && ((_this.traceVariable) != (object) (_this.traceDLStart))) && ((_this.traceVariable) != (object) (_this.traceDLEnd))) && ((_this.traceDLStart) != (object) (_this.traceDLEnd));
    }
    public static bool validTraceDL(DataStructures _this) {
      return ((Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001)), true, (((_forall_var_14) => {
        int _134_dl = (int)_forall_var_14;
        if (SYInt32.t._Is(_134_dl)) {
          return !(((0) <= (_134_dl)) && ((_134_dl) < (_this.decisionLevel))) || ((((0) <= ((_this.traceDLStart)[(int)(_134_dl)])) && (((_this.traceDLStart)[(int)(_134_dl)]) < ((_this.traceDLEnd)[(int)(_134_dl)]))) && (((_this.traceDLEnd)[(int)(_134_dl)]) <= (_this.variablesCount)));
        } else {
          return true;
        }
      })))) && (!((_this.decisionLevel) >= (0)) || ((((_this.traceDLStart)[(int)(BigInteger.Zero)]) == (0)) && ((((0) <= ((_this.traceDLStart)[(int)(_this.decisionLevel)])) && (((_this.traceDLStart)[(int)(_this.decisionLevel)]) <= ((_this.traceDLEnd)[(int)(_this.decisionLevel)]))) && (((_this.traceDLEnd)[(int)(_this.decisionLevel)]) <= (_this.variablesCount)))))) && (Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(new BigInteger(-2000000), new BigInteger(2000001)), true, (((_forall_var_15) => {
        int _135_dl = (int)_forall_var_15;
        if (SYInt32.t._Is(_135_dl)) {
          return !(((0) < (_135_dl)) && ((_135_dl) <= (_this.decisionLevel))) || (((_this.traceDLStart)[(int)(_135_dl)]) == ((_this.traceDLEnd)[(int)((_135_dl) - (1))]));
        } else {
          return true;
        }
      }))));
    }
    public static bool validTraceVariable(DataStructures _this) {
      return !((_this.decisionLevel) >= (0)) || ((Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001)), true, (((_forall_var_16) => {
        int _136_i = (int)_forall_var_16;
        if (SYInt32.t._Is(_136_i)) {
          return !(((0) <= (_136_i)) && ((_136_i) < ((_this.traceDLEnd)[(int)(_this.decisionLevel)]))) || ((_this).validVariable((_this.traceVariable)[(int)(_136_i)]));
        } else {
          return true;
        }
      })))) && (Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001)), true, (((_forall_var_17) => {
        int _137_i = (int)_forall_var_17;
        if (SYInt32.t._Is(_137_i)) {
          return !(((0) <= (_137_i)) && ((_137_i) < ((_this.traceDLEnd)[(int)(_this.decisionLevel)]))) || (Dafny.Helpers.Id<Func<int, bool>>((_138_i) => Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(BigInteger.Zero, new BigInteger(2000001)), true, (((_forall_var_18) => {
            int _139_j = (int)_forall_var_18;
            if (SYInt32.t._Is(_139_j)) {
              return !((((0) <= (_139_j)) && ((_139_j) < ((_this.traceDLEnd)[(int)(_this.decisionLevel)]))) && ((_138_i) != (_139_j))) || (((_this.traceVariable)[(int)(_138_i)]) != ((_this.traceVariable)[(int)(_139_j)]));
            } else {
              return true;
            }
          }))))(_137_i));
        } else {
          return true;
        }
      })))));
    }
    public static bool convertIntToBool(DataStructures _this, int x) {
      if ((x) == (0)) {
        return false;
      } else {
        return true;
      }
    }
    public static bool validValuesTruthAssignment(DataStructures _this, Dafny.ISequence<int> truthAssignment) {
      return (((new BigInteger((truthAssignment).Count)) == (new BigInteger(_this.variablesCount))) && ((new BigInteger((truthAssignment).Count)) <= (SYInt32.__default.max))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, bool>>((_140_truthAssignment) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_140_truthAssignment).Count)), true, (((_forall_var_19) => {
        BigInteger _141_i = (BigInteger)_forall_var_19;
        return !(((_141_i).Sign != -1) && ((_141_i) < (new BigInteger((_140_truthAssignment).Count)))) || (((-1) <= ((_140_truthAssignment).Select(_141_i))) && (((_140_truthAssignment).Select(_141_i)) <= (1)));
      }))))(truthAssignment));
    }
    public static int getLiteralValue(DataStructures _this, Dafny.ISequence<int> truthAssignment, int literal)
    {
      int _142_variable = (Utils.__default.abs(literal)) - (1);
      if (((truthAssignment).Select(_142_variable)) == (-1)) {
        return -1;
      } else if ((literal) < (0)) {
        return (1) - ((truthAssignment).Select(_142_variable));
      } else {
        return (truthAssignment).Select(_142_variable);
      }
    }
    public static bool isClauseSatisfied(DataStructures _this, Dafny.ISequence<int> truthAssignment, int clauseIndex)
    {
      return Dafny.Helpers.Id<Func<int, Dafny.ISequence<int>, bool>>((_143_clauseIndex, _144_truthAssignment) => Dafny.Helpers.Quantifier<int>(((_this.clauses).Select(_143_clauseIndex)).UniqueElements, false, (((_exists_var_3) => {
        int _145_literal = (int)_exists_var_3;
        if (SYInt32.t._Is(_145_literal)) {
          return (((_this.clauses).Select(_143_clauseIndex)).Contains(_145_literal)) && (((_this).getLiteralValue(_144_truthAssignment, _145_literal)) == (1));
        } else {
          return false;
        }
      }))))(clauseIndex, truthAssignment);
    }
    public static int getVariableFromLiteral(DataStructures _this, int literal) {
      return (Utils.__default.abs(literal)) - (1);
    }
    public static _System._ITuple2<int, int> convertLVtoVI(DataStructures _this, int literal, bool @value)
    {
      int _146_variable = (_this).getVariableFromLiteral(literal);
      int _147_v = ((@value) ? (1) : (0));
      int _148_val = (((literal) < (0)) ? ((1) - (_147_v)) : (_147_v));
      return _System.Tuple2<int, int>.create(_146_variable, _148_val);
    }
    public static bool validTrueLiteralsCount(DataStructures _this, Dafny.ISequence<int> truthAssignment) {
      return ((new BigInteger((_this.trueLiteralsCount).Length)) == (new BigInteger((_this.clauses).Count))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, bool>>((_149_truthAssignment) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_this.clauses).Count)), true, (((_forall_var_20) => {
        BigInteger _150_i = (BigInteger)_forall_var_20;
        return !(((_150_i).Sign != -1) && ((_150_i) < (new BigInteger((_this.clauses).Count)))) || (((0) <= ((_this.trueLiteralsCount)[(int)(_150_i)])) && (((_this.trueLiteralsCount)[(int)(_150_i)]) == ((_this).countTrueLiterals(_149_truthAssignment, (_this.clauses).Select(_150_i)))));
      }))))(truthAssignment));
    }
    public static int countUnsetVariables(DataStructures _this, Dafny.ISequence<int> truthAssignment) {
      int _151___accumulator = 0;
    TAIL_CALL_START: ;
      if ((new BigInteger((truthAssignment).Count)).Sign == 0) {
        return (0) + (_151___accumulator);
      } else {
        int _152_ok = ((((truthAssignment).Select(BigInteger.Zero)) == (-1)) ? (1) : (0));
        _151___accumulator = (_151___accumulator) + (_152_ok);
        DataStructures _in1 = _this;
        Dafny.ISequence<int> _in2 = (truthAssignment).Drop(BigInteger.One);
        _this = _in1;
        ;
        truthAssignment = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static int countTrueLiterals(DataStructures _this, Dafny.ISequence<int> truthAssignment, Dafny.ISequence<int> clause)
    {
      int _153___accumulator = 0;
    TAIL_CALL_START: ;
      if ((new BigInteger((clause).Count)).Sign == 0) {
        return (0) + (_153___accumulator);
      } else {
        int _154_ok = ((((_this).getLiteralValue(truthAssignment, (clause).Select(BigInteger.Zero))) == (1)) ? (1) : (0));
        _153___accumulator = (_153___accumulator) + (_154_ok);
        DataStructures _in3 = _this;
        Dafny.ISequence<int> _in4 = truthAssignment;
        Dafny.ISequence<int> _in5 = (clause).Drop(BigInteger.One);
        _this = _in3;
        ;
        truthAssignment = _in4;
        clause = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static bool validFalseLiteralsCount(DataStructures _this, Dafny.ISequence<int> truthAssignment) {
      return ((new BigInteger((_this.falseLiteralsCount).Length)) == (new BigInteger((_this.clauses).Count))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, bool>>((_155_truthAssignment) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_this.clauses).Count)), true, (((_forall_var_21) => {
        BigInteger _156_i = (BigInteger)_forall_var_21;
        return !(((_156_i).Sign != -1) && ((_156_i) < (new BigInteger((_this.clauses).Count)))) || (((0) <= ((_this.falseLiteralsCount)[(int)(_156_i)])) && (((_this.falseLiteralsCount)[(int)(_156_i)]) == ((_this).countFalseLiterals(_155_truthAssignment, (_this.clauses).Select(_156_i)))));
      }))))(truthAssignment));
    }
    public static int countFalseLiterals(DataStructures _this, Dafny.ISequence<int> truthAssignment, Dafny.ISequence<int> clause)
    {
      int _157___accumulator = 0;
    TAIL_CALL_START: ;
      if ((new BigInteger((clause).Count)).Sign == 0) {
        return (0) + (_157___accumulator);
      } else {
        int _158_ok = ((((_this).getLiteralValue(truthAssignment, (clause).Select(BigInteger.Zero))) == (0)) ? (1) : (0));
        _157___accumulator = (_157___accumulator) + (_158_ok);
        DataStructures _in6 = _this;
        Dafny.ISequence<int> _in7 = truthAssignment;
        Dafny.ISequence<int> _in8 = (clause).Drop(BigInteger.One);
        _this = _in6;
        ;
        truthAssignment = _in7;
        clause = _in8;
        goto TAIL_CALL_START;
      }
    }
    public static bool validPositiveLiteralsToClauses(DataStructures _this) {
      return (((new BigInteger((_this.positiveLiteralsToClauses).Length)) == (new BigInteger(_this.variablesCount))) && (Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(new BigInteger(-2000000), new BigInteger(2000001)), true, (((_forall_var_22) => {
        int _159_variable = (int)_forall_var_22;
        if (SYInt32.t._Is(_159_variable)) {
          return !(((new BigInteger(_159_variable)).Sign != -1) && ((new BigInteger(_159_variable)) < (new BigInteger((_this.positiveLiteralsToClauses).Length)))) || ((_this).validPositiveLiteralToClause(_159_variable, (_this.positiveLiteralsToClauses)[(int)(_159_variable)]));
        } else {
          return true;
        }
      }))))) && (Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(new BigInteger(-2000000), new BigInteger(2000001)), true, (((_forall_var_23) => {
        int _160_variable = (int)_forall_var_23;
        if (SYInt32.t._Is(_160_variable)) {
          return !(((new BigInteger(_160_variable)).Sign != -1) && ((new BigInteger(_160_variable)) < (new BigInteger((_this.positiveLiteralsToClauses).Length)))) || ((new BigInteger(((_this.positiveLiteralsToClauses)[(int)(_160_variable)]).Count)) <= (new BigInteger(_this.clausesCount)));
        } else {
          return true;
        }
      }))));
    }
    public static bool validPositiveLiteralToClause(DataStructures _this, int variable, Dafny.ISequence<int> s)
    {
      return (((Utils.__default.valuesBoundedBy(s, BigInteger.Zero, new BigInteger((_this.clauses).Count))) && (Utils.__default.orderedAsc(s))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, int, bool>>((_161_s, _162_variable) => Dafny.Helpers.Quantifier<int>((_161_s).UniqueElements, true, (((_forall_var_24) => {
        int _163_clauseIndex = (int)_forall_var_24;
        if (SYInt32.t._Is(_163_clauseIndex)) {
          return !((_161_s).Contains(_163_clauseIndex)) || (((_this.clauses).Select(_163_clauseIndex)).Contains((_162_variable) + (1)));
        } else {
          return true;
        }
      }))))(s, variable))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, int, bool>>((_164_s, _165_variable) => Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(new BigInteger(-2000000), new BigInteger(2000001)), true, (((_forall_var_25) => {
        int _166_clauseIndex = (int)_forall_var_25;
        if (SYInt32.t._Is(_166_clauseIndex)) {
          return !((((new BigInteger(_166_clauseIndex)).Sign != -1) && ((new BigInteger(_166_clauseIndex)) < (new BigInteger((_this.clauses).Count)))) && (!(_164_s).Contains(_166_clauseIndex))) || (!((_this.clauses).Select(_166_clauseIndex)).Contains((_165_variable) + (1)));
        } else {
          return true;
        }
      }))))(s, variable));
    }
    public static bool validNegativeLiteralsToClauses(DataStructures _this) {
      return ((new BigInteger((_this.negativeLiteralsToClauses).Length)) == (new BigInteger(_this.variablesCount))) && (Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(new BigInteger(-2000000), new BigInteger(2000001)), true, (((_forall_var_26) => {
        int _167_v = (int)_forall_var_26;
        if (SYInt32.t._Is(_167_v)) {
          return !(((new BigInteger(_167_v)).Sign != -1) && ((new BigInteger(_167_v)) < (new BigInteger((_this.negativeLiteralsToClauses).Length)))) || (((_this).validNegativeLiteralsToClause(_167_v, (_this.negativeLiteralsToClauses)[(int)(_167_v)])) && (Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(new BigInteger(-2000000), new BigInteger(2000001)), true, (((_forall_var_27) => {
            int _168_variable = (int)_forall_var_27;
            if (SYInt32.t._Is(_168_variable)) {
              return !(((new BigInteger(_168_variable)).Sign != -1) && ((new BigInteger(_168_variable)) < (new BigInteger((_this.negativeLiteralsToClauses).Length)))) || ((new BigInteger(((_this.negativeLiteralsToClauses)[(int)(_168_variable)]).Count)) <= (new BigInteger(_this.clausesCount)));
            } else {
              return true;
            }
          })))));
        } else {
          return true;
        }
      }))));
    }
    public static bool validNegativeLiteralsToClause(DataStructures _this, int variable, Dafny.ISequence<int> s)
    {
      return (((Utils.__default.valuesBoundedBy(s, BigInteger.Zero, new BigInteger((_this.clauses).Count))) && (Utils.__default.orderedAsc(s))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, int, bool>>((_169_s, _170_variable) => Dafny.Helpers.Quantifier<int>((_169_s).UniqueElements, true, (((_forall_var_28) => {
        int _171_clauseIndex = (int)_forall_var_28;
        if (SYInt32.t._Is(_171_clauseIndex)) {
          return !((_169_s).Contains(_171_clauseIndex)) || (((_this.clauses).Select(_171_clauseIndex)).Contains(((0) - (_170_variable)) - (1)));
        } else {
          return true;
        }
      }))))(s, variable))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<int>, int, bool>>((_172_s, _173_variable) => Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(new BigInteger(-2000000), new BigInteger(2000001)), true, (((_forall_var_29) => {
        int _174_clauseIndex = (int)_forall_var_29;
        if (SYInt32.t._Is(_174_clauseIndex)) {
          return !((((new BigInteger(_174_clauseIndex)).Sign != -1) && ((new BigInteger(_174_clauseIndex)) < (new BigInteger((_this.clauses).Count)))) && (!(_172_s).Contains(_174_clauseIndex))) || (!((_this.clauses).Select(_174_clauseIndex)).Contains(((0) - (_173_variable)) - (1)));
        } else {
          return true;
        }
      }))))(s, variable));
    }
    public static bool validReferences(DataStructures _this) {
      return (((((((((((((((((((_this.truthAssignment) != (object) (_this.trueLiteralsCount)) && ((_this.truthAssignment) != (object) (_this.falseLiteralsCount))) && ((_this.truthAssignment) != (object) (_this.clauseLength))) && ((_this.truthAssignment) != (object) (_this.traceVariable))) && ((_this.truthAssignment) != (object) (_this.traceDLStart))) && ((_this.truthAssignment) != (object) (_this.traceDLEnd))) && ((_this.trueLiteralsCount) != (object) (_this.falseLiteralsCount))) && ((_this.trueLiteralsCount) != (object) (_this.clauseLength))) && ((_this.trueLiteralsCount) != (object) (_this.traceVariable))) && ((_this.trueLiteralsCount) != (object) (_this.traceDLStart))) && ((_this.trueLiteralsCount) != (object) (_this.traceDLEnd))) && ((_this.falseLiteralsCount) != (object) (_this.clauseLength))) && ((_this.falseLiteralsCount) != (object) (_this.traceVariable))) && ((_this.falseLiteralsCount) != (object) (_this.traceDLStart))) && ((_this.falseLiteralsCount) != (object) (_this.traceDLEnd))) && ((_this.clauseLength) != (object) (_this.traceVariable))) && ((_this.clauseLength) != (object) (_this.traceDLStart))) && ((_this.clauseLength) != (object) (_this.traceDLEnd))) && ((_this.positiveLiteralsToClauses) != (object) (_this.negativeLiteralsToClauses));
    }
    public static BigInteger countLiterals(DataStructures _this, int clauseIndex) {
      BigInteger _175___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((clauseIndex) == (0)) {
        return (BigInteger.Zero) + (_175___accumulator);
      } else {
        _175___accumulator = (_175___accumulator) + (new BigInteger(((_this.clauses).Select((clauseIndex) - (1))).Count));
        DataStructures _in9 = _this;
        int _in10 = (clauseIndex) - (1);
        _this = _in9;
        ;
        clauseIndex = _in10;
        goto TAIL_CALL_START;
      }
    }
    public static bool isVariableSet(DataStructures _this, Dafny.ISequence<int> truthAssignment, int variable)
    {
      return ((truthAssignment).Select(variable)) != (-1);
    }
    public static bool isSatisfied(DataStructures _this, Dafny.ISequence<int> truthAssignment) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<int>, bool>>((_176_truthAssignment) => Dafny.Helpers.Quantifier<int>(SYInt32.t.IntegerRange(new BigInteger(-2000000), new BigInteger(2000001)), true, (((_forall_var_30) => {
        int _177_cI = (int)_forall_var_30;
        if (SYInt32.t._Is(_177_cI)) {
          return !(((new BigInteger(_177_cI)).Sign != -1) && ((new BigInteger(_177_cI)) < (new BigInteger((_this.clauses).Count)))) || ((_this).isClauseSatisfied(_176_truthAssignment, _177_cI));
        } else {
          return true;
        }
      }))))(truthAssignment);
    }
    public static bool isExtendingTau(DataStructures _this, Dafny.ISequence<int> tau, Dafny.ISequence<int> tau_k)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<int>, Dafny.ISequence<int>, bool>>((_178_tau, _179_tau_k) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_178_tau).Count)), true, (((_forall_var_31) => {
        BigInteger _180_i = (BigInteger)_forall_var_31;
        return !((((_180_i).Sign != -1) && ((_180_i) < (new BigInteger((_178_tau).Count)))) && (((_178_tau).Select(_180_i)) != (-1))) || (((_178_tau).Select(_180_i)) == ((_179_tau_k).Select(_180_i)));
      }))))(tau, tau_k);
    }
    public static bool isTauComplete(DataStructures _this, Dafny.ISequence<int> tau) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<int>, bool>>((_181_tau) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_181_tau).Count)), true, (((_forall_var_32) => {
        BigInteger _182_i = (BigInteger)_forall_var_32;
        return !(((_182_i).Sign != -1) && ((_182_i) < (new BigInteger((_181_tau).Count)))) || (((_181_tau).Select(_182_i)) != (-1));
      }))))(tau);
    }
    public static bool isSatisfiableTruthAssignment(DataStructures _this, Dafny.ISequence<int> tau, Dafny.ISequence<int> tau_k)
    {
      return (((_this).validValuesTruthAssignment(tau_k)) && ((_this).isExtendingTau(tau, tau_k))) && ((_this).isSatisfied(tau_k));
    }
    public static bool isUnitClause(DataStructures _this, int index) {
      return (((_this.trueLiteralsCount)[(int)(index)]) == (0)) && ((((_this.clauseLength)[(int)(index)]) - ((_this.falseLiteralsCount)[(int)(index)])) == (1));
    }
    public static bool isEmptyClause(DataStructures _this, int index) {
      return ((_this.clauseLength)[(int)(index)]) == ((_this.falseLiteralsCount)[(int)(index)]);
    }
  }
} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => _module.__default._Main(Dafny.Sequence<Dafny.ISequence<char>>.FromMainArguments(args)));
  }
}
