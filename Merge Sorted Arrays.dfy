method Main() {
	var a, b := new int[3] [3,5,8], new int[2] [4,7];
	print "Before merging the following two sorted arrays:\n";
	print a[..];
	print "\n";
	print b[..];
	ghost var AB := multiset(a[..]+b[..]);
	assert Sorted(a[..]) && Sorted(b[..]);
	MergeSortedArraysInPlace(a, b, AB);
	assert multiset(a[..]+b[..]) == AB;
	assert Sorted(a[..]+b[..]);
	print "\nAfter merging:\n";
	print a[..]; // [3,4,5]
	print "\n";
	print b[..]; // [7,8]
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

/*
	Goal: Implement iteratively, correctly, efficiently, clearly. No need to document the proof obligations.

	Restriction: Merge the arrays in place, using constant additional space only.
*/
method MergeSortedArraysInPlace(a: array<int>, b: array<int>, ghost AB: multiset<int>)
	requires Sorted(a[..]) && Sorted(b[..])
	requires multiset(a[..]+b[..]) == AB
	requires a != b
	ensures Sorted(a[..]+b[..])
	ensures multiset(a[..]+b[..]) == AB
	modifies a,b
{
    if a.Length == 0 || b.Length == 0           // no need to merge
    {
        assert AB == multiset(a[..]+b[..]);
        assert Sorted(a[..]+b[..]);
        assert forall i,j :: 0 <= i <= j < |a[..]+b[..]| ==> (a[..]+b[..])[i] <= (a[..]+b[..])[j];
        return;
    }
    else                                        // need to merge
    {   // insertion sort a -> b
        var i:int:=0;
        while i < a.Length
            invariant multiset(a[..]+b[..]) == AB
            invariant Sorted(a[..])
            invariant Sorted(b[..])
            invariant i <= a.Length
            // invariant forall j :: 0 <= j < b.Length ==> b[0] <= b[j]
            invariant forall j :: 0 <= j < i ==> a[j] <= b[0]   // upto i has been inserted
        {
            if a[i] > b[0]      // insert and sort a[i]
            {
                var temp:int:= a[i];
                a[i] := b[0];
                b[0] := temp;
                var j:int:= 0;

                // assert Sorted(a[..]);
                // assert forall j :: 0 <= j < i ==> a[j] <= b[0];
                // ghost var b_ := b[..];
                // assert forall j :: 0 <= j < i ==> a[j] <= b_[0];
                
                while j < b.Length-1 
                    invariant Sorted(a[..])
                    invariant multiset(a[..]+b[..]) == AB
                    invariant j <= b.Length-1
                    // invariant Sorted(b[j+1..])
                    invariant SortedExceptAt(b[..], j)
                    // invariant forall j :: 0 <= j < i ==> a[j] <= b_[0]
                    // invariant multiset(b[..]) == multiset(b_[..])
                    invariant forall k:: 0<= k < j ==> b[k] <= b[j]   // upto j is sorted
                    invariant forall k:: 0<= k < b.Length ==> a[i] <= b[k]
                    // invariant forall k :: 0 <= k < j ==> a[k] <= b[j]
                {
                    if b[j] > b[j+1]
                    {
                        temp := b[j];
                        b[j] := b[j+1];
                        b[j+1] := temp;
                    }
                    else
                    {
                        break;
                    }
                    j:=j+1;
                }
                
                // assert Sorted(a[..]);
                // assert Sorted(b[..]);
            }
            i:=i+1;
        }
        
    }
}

predicate SortedExceptAt(q: seq<int>, k: nat) {
	forall i,j :: 0 <= i <= j < |q| && i != k && j != k ==> q[i] <= q[j]
}
