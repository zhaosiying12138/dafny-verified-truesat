include "int32.dfy"
include "parser.dfy"
include "file_input.dfy"
include "my_datatypes.dfy"
include "input_predicate.dfy"

module Input {
    import SYInt32
    import opened Useless
    import FileInput
    import opened MyDatatypes
    import InputPredicate

    method getInput() returns (result : Maybe<(SYInt32.t, seq<seq<SYInt32.t>>)>)
      ensures result.Just? ==>
        InputPredicate.valid(result.value);
    {
      var input := FileInput.Reader.getContent();
      if (0 < |input| < SYInt32.max as int) {
        var parser := new Parser(input);
        var x := parser.parse();
        return x;
      } else {
        return Error("the file contains more data than SYInt32.max");
      }
    }

    function getTimestamp() : int
    {
      FileInput.Reader.getTimestamp()
    }
}
