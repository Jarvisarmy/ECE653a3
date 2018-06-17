method findMax (a : array?<int>, n : int) returns (r:int)
  requires a != null && a.Length > 0;
  //n couldn't be 0
  requires 0 < n <= a.Length;
  ensures 0 <= r < n;
  ensures forall l :: 0<= l < n ==> a[l] <= a[r]
{
  
  var mi;
  var i;
  mi := 0;
  i := 0;
  while (i < n)
  invariant 0<= i <= n;
  invariant 0<= mi < n;
  decreases n-i;
  invariant forall k :: 0<= k < i ==> a[k] <= a[mi]
  {
    if (a[i] > a[mi])
    { mi := i; }
    i := i + 1;
  }
  return mi;
}
