using System;
using System.Collections;
using System.Text;
using System.IO;
using System.Linq;

using Dafny;

namespace @FileInput {

    public partial class @Reader
    {
        public static Dafny.ISequence<char> CharArrayToDafnySequence(char[] charArray) {
            // Convert each char in the array to Dafny's char
            // var dafnyCharArray = charArray.Select(c => (char)c).ToArray();
            // Create a Dafny sequence from the array
            return Dafny.Sequence<char>.FromArray(charArray);
        }

        public static Dafny.ISequence<char> getContent() {
            string[] argList = Environment.GetCommandLineArgs();

            if (argList.Length > 1) {
              if (File.Exists(argList[1])) {

                return CharArrayToDafnySequence(System.IO.File.ReadAllText(argList[1], Encoding.UTF8).ToCharArray());
              } else {
                return CharArrayToDafnySequence("".ToCharArray());
              }
            }

            return CharArrayToDafnySequence("".ToCharArray());
        }

        public static long getTimestamp() {
          return DateTimeOffset.UtcNow.ToUnixTimeMilliseconds();
        }
    }
}
