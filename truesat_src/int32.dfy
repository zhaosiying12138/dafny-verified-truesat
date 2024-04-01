module SYInt32 {
  newtype {:nativeType "int"} t = x | -2000000 <= x < 2000001
  const max : int := 2000000;
  const min : int := -2000000;
  
  ghost method test(x : t) {
    var m1 : t := -x;
  }
}
