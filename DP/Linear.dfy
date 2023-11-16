method LinearSearch(a: array<int>, lo: int, hi: int, v: int ) returns (r: bool)
  requires 0 <= lo <= hi < a.Length
  ensures r <==> exists i :: lo <= i <= hi && a[i] == v
{
  var i := lo;
  while i != hi + 1
    invariant lo <= i <= hi + 1
    invariant forall k :: lo <= k < i ==> a[k] != v
    decreases hi+1 -i 
  {
    if (a[i] == v) {
      r := true;
      return;
    }
    i := i + 1;
  }
  assert(i == hi+1);
  r := false;
}