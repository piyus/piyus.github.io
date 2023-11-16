method BubbleSort(a: array<int>)
	modifies a
	//ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] 
	ensures forall i :: 0 <= i < a.Length-1 ==> a[i] <= a[i+1] 
	ensures multiset(a[..]) == old(multiset(a[..]))
{
	if a.Length == 0 {
		return;
	}
	var i := a.Length - 1;
	while i > 0
		invariant 0 <= i < a.Length
		invariant forall k, l :: 0 <= k <= i && i+1 <= l <= a.Length - 1 ==> a[l] >= a[k]
		//invariant forall k, l :: i+1 <= k < l <= a.Length - 1 ==> a[k] <= a[l] 
		invariant forall k :: i+1 <= k < a.Length - 1 ==> a[k] <= a[k+1]
		invariant multiset(a[..]) == old(multiset(a[..])) 
	{
		var j := 0;
		while j < i
			invariant 0 <= j <= i
			invariant forall k :: 0 <= k < j ==> a[j] >= a[k] 
			invariant forall k, l :: 0 <= k <= i && i+1 <= l <= a.Length - 1 ==> a[l] >= a[k] 
			//invariant forall k, l :: i+1 <= k < l <= a.Length - 1 ==> a[k] <= a[l]
			invariant forall k :: i+1 <= k < a.Length - 1 ==> a[k] <= a[k+1]
			invariant multiset(a[..]) == old(multiset(a[..])) 
		{
			if a[j] > a[j+1] 
			{
				var t := a[j];
				a[j] := a[j+1];
				a[j+1] := t;
			}
			j := j + 1;
		}
		i := i - 1;
	}
}
