module {:extern "FileInput"} FileInput {
    class {:extern "Reader"} Reader {
        static function {:extern "getContent"} getContent() : seq<char>
        static function {:extern "getTimestamp"} getTimestamp() : int
    }
}
