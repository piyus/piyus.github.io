method BinarySearch(a: array<int>, v: int, lo: int, hi: int) returns (r: bool)
  requires 0 <= lo && hi < a.Length
  requires forall i :: lo <= i < hi ==> a[i] <= a[i+1] 
  decreases hi - lo 
  ensures r <==> exists i :: lo <= i <= hi && a[i] == v
{
  if (lo > hi) {
    r := false;
    return;
  }
  assert(forall i :: lo <= i < hi ==> a[i] <= a[i+1]);
  assert((forall i :: lo <= i < hi ==> a[i] <= a[i+1]) ==> (forall i, j :: lo <= i < j <= hi ==> a[i] <= a[j]));
  var mid := (hi + lo)/2;
  if (a[mid] == v) {
    r := true;
    return;
  }
  else if (a[mid] > v)
  {
    r := BinarySearch(a, v, lo, mid - 1);
  }
  else {
    r := BinarySearch(a, v, mid + 1, hi);
  }
}