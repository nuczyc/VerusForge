
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, N: i32, m: i32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] <= N,
{
	let mut i: usize = 0;

	while (i < N as usize)
	invariant
		0 <= i <= N,
		a.len() == N,
		// Invariant about elements set to 'm' so far:
		forall |k:int| 0 <= k < i ==> a[k] == m,
		decreases(N as int - i as int),
	{
		a.set(i, m);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	invariant
		0 <= i <= N,
		a.len() == N,
		// Establishing invariant for the elements' bounds:
		forall |k:int| 0 <= k < i ==> a[k] <= N,
		decreases(N as int - i as int),
	{
		if (a[i] < N) {
			a.set(i, a[i]);
		} else {
			a.set(i, N);
		}
		i = i + 1;
	}
}
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True