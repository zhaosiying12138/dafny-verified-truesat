include "int32.dfy"
include "my_datatypes.dfy"
include "input_predicate.dfy"

module Useless {
  import opened MyDatatypes
  import SYInt32
  import InputPredicate

  predicate valid'(c : seq<char>) {
    0 < |c| < SYInt32.max as int
  }

  class Parser {
    var content : seq<char>;
    var contentLength : SYInt32.t;
    var cursor : SYInt32.t;

    constructor(c : seq<char>) 
      requires valid'(c);
      ensures valid();
    {
      content := c; 
      contentLength := |c| as SYInt32.t;
      cursor := 0;
    }

    predicate valid() 
      reads `content, `contentLength, `cursor;
    {
      valid'(content) && 
      contentLength as int == |content| &&
      0 <= cursor <= contentLength
    }

    method skipLine()
      requires valid();
      modifies `cursor;
      ensures valid();
      ensures old(cursor) <= cursor;
    {
      while (cursor < contentLength && content[cursor] != '\n')
        invariant 0 <= cursor <= contentLength;
      {
        cursor := cursor + 1;
      }

      if (cursor < contentLength) {
        cursor := cursor + 1;
      }
    }

    method toNextNumber()
      requires valid();
      modifies `cursor;
      ensures valid();
      ensures old(cursor) <= cursor;
      ensures cursor < contentLength ==>
        (content[cursor] == '-' || ('0' <= content[cursor] <= '9'));
    {
      while (cursor < contentLength && !('0' <= content[cursor] <= '9' || content[cursor] == '-'))
        invariant 0 <= cursor <= contentLength;
      {
        cursor := cursor + 1;
      }
    }

    method extractNumber() returns (res : Maybe<SYInt32.t>)
      requires valid();
      requires cursor < contentLength ==>
        (content[cursor] == '-' || ('0' <= content[cursor] <= '9'));
      modifies `cursor;
      ensures valid();
      ensures old(cursor) <= cursor;
      ensures res.Just? ==> old(cursor) < cursor;
    {
      var number : SYInt32.t := 0;
      var isNegative : bool := false;

      if (cursor < contentLength && content[cursor] == '-') {
        isNegative := true;
        cursor := cursor + 1;
      }

      if (cursor == contentLength) {
        return Error("There is no number around here.");
      }

      while (cursor < contentLength && ('0' <= content[cursor] <= '9'))
        invariant 0 <= cursor <= contentLength;
        invariant 0 <= number <= SYInt32.max as SYInt32.t;
      {
        var digit : SYInt32.t := content[cursor] as SYInt32.t - '0' as SYInt32.t;
        if (number <= (SYInt32.max as SYInt32.t - digit) / 10) {
          assert 0 <= (SYInt32.max as SYInt32.t - digit) / 10 - number;
          number := number * 10 + digit;
        } else {
          return Error("There is a number bigger than SYInt32.max");
        }
        cursor := cursor + 1;
      }

      if (isNegative) {
        number := -number;
      }

      /* print number, " ";*/
      return Just(number);
    }

    method parse() returns (result: Maybe<(SYInt32.t, seq<seq<SYInt32.t>>)>)
      requires valid();
      modifies `cursor;

      ensures result.Just? ==>
        InputPredicate.valid(result.value);
    {
      var variablesCount : SYInt32.t := 0;
      var clausesCount : SYInt32.t := 0;
      var clauses : seq<seq<SYInt32.t>> := [];
      var clause : array<SYInt32.t> := new SYInt32.t[1000];
      var clauseLength : SYInt32.t := 0;
      var ok := false; 
      var literalsCount : SYInt32.t := 0;

      var contentLength : SYInt32.t := |content| as SYInt32.t;
      while (cursor < contentLength) 
        modifies `cursor, clause;

        invariant 0 <= cursor <= contentLength;
        invariant InputPredicate.checkClauses(variablesCount, clauses);
        invariant InputPredicate.sortedClauses(clauses);
        invariant clause.Length <= SYInt32.max as int;
        invariant forall z :: 0 <= z < clauseLength ==> (
            (clause[z] < 0 && 0 < -clause[z] <= variablesCount) ||
            (clause[z] > 0 && 0 < clause[z] <= variablesCount));
        invariant forall x, y :: 0 <= x < y < clauseLength ==>
            clause[x] < clause[y]
        invariant ok ==>  0 < variablesCount < SYInt32.max as SYInt32.t;
        invariant InputPredicate.countLiterals(clauses) == literalsCount as int;

        decreases contentLength - cursor;
      {
        var oldCursor := cursor;
        if (content[cursor] == 'c') {
          skipLine();
        } else if (content[cursor] == 'p' && variablesCount == 0) {
          toNextNumber();
          var x := extractNumber();
          match x {
            case Error(t) => {
              return Error(t);
            } 
            case Just(number) => {
              if (0 < number < SYInt32.max as SYInt32.t) {
                variablesCount := number;
                ok := true;
              } else {
                return Error("Variables count is bigger than SYInt32.max");
              }
            }
          }
          toNextNumber();
          x := extractNumber();
          match x {
            case Error(t) => {
              return Error(t);
            }
            case Just(number) => {
              clausesCount := number;
              /* print "clausesCount: ", clausesCount, "\n";*/
            }
          }
          skipLine();
        } else if (content[cursor] == 'p') {
          return Error ("Twice p? what are you doing?");
        } else if (ok) {
          toNextNumber();
          /* print clause, "\n";*/
          if (clauseLength == 0 && cursor == contentLength) {
            break;
          }
          var x := extractNumber();
          match x {
            case Error(t) => {
              return Error(t);
            } 
            case Just(number) => {
              if (number == 0 && clauseLength > 0) {
                clauses := clauses + [clause[..clauseLength]];
                if (SYInt32.max as SYInt32.t - clauseLength > literalsCount) {
                  literalsCount := literalsCount + clauseLength;
                } else {
                  return Error("The number of literals is to big");
                }
                clauseLength := 0;
                /* print "\n";*/
              } else if (number != 0) {
                if (clauseLength < 1000) {
                  if ((number < 0 && 0 < -number <= variablesCount) ||
                      (number > 0 && 0 < number <= variablesCount)) {
                    clause[clauseLength] := number;
                    clauseLength := clauseLength + 1;
                    var k : SYInt32.t := clauseLength-1;
                    while (0 < k && clause[k-1] > clause[k]) 
                      modifies clause;
                      invariant 0 <= k <= clauseLength; 
                      invariant forall z :: 0 <= z < clauseLength ==> (
                          (clause[z] < 0 && 0 < -clause[z] <= variablesCount) ||
                          (clause[z] > 0 && 0 < clause[z] <= variablesCount));
                      invariant forall x, y :: 0 <= x < y < clauseLength && x != k && y != k ==>
                          clause[x] < clause[y];
                      invariant forall x, y :: k <= x < y < clauseLength ==>
                          clause[x] < clause[y];
                      decreases k;
                    {
                      var aux := clause[k];
                      clause[k] := clause[k-1];
                      clause[k-1] := aux;
                      k := k - 1;
                    }
                    if (k > 0 && clause[k-1] == clause[k]) {
                      return Error("duplice literal in clause");
                    }
                  } else {
                    return Error("literal bigger than variablesCount");
                  }
                } else {
                  return Error("clause longer than 1000");
                }
              }
            }
          }
        }

        if (cursor < contentLength && oldCursor == cursor) {
          cursor := cursor + 1;
        }
      }

      if (!(0 < |clauses| < SYInt32.max as int)) {
        return Error("number of clauses incorrect");
      }

      if (|clauses| != clausesCount as int) {
        return Error("different number of clauses");
      }
      
      if (ok) {
        return Just((variablesCount, clauses));
      } else {
        return Error("p not found");
      }
    }
  }
}
