// flips (i.e., reverses) array elements in the range [0..num]
method flip (a: array?<int>, num: int)
requires a != null && a.Length > 0;
requires 0<= num <a.Length;
modifies a;
ensures multiset(old(a[..])) == multiset(a[..]);
ensures forall n:: 0 <= n <= num  ==> a[n] == old(a[num-n]);
ensures forall n:: num < n < a.Length ==> a[n] == old(a[n]);
{
  var tmp:int;
  var i := 0;
  var j := num;
  while (i < j)
    decreases num - i;
    invariant i + j ==num;
    invariant 0 <= i <= num/2 + 1;
    invariant num/2-1 <= j <=num;
    invariant multiset(old(a[..])) == multiset(a[..]);
    invariant forall n :: 0<= n <i ==> a[n] == old(a[num-n]);
    invariant forall n:: num < n < a.Length ==> a[n] == old(a[n]);
    invariant forall n :: 0<= n <i ==> a[num-n] == old(a[n]);
    invariant forall n :: i<= n <= j ==> a[n] == old(a[n]); 
  {
    tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := j - 1;
  }
}