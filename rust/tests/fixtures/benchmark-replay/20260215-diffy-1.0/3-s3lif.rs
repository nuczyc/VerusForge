
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 4 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
	invariant
		i <= N as usize,
		a.len() == N,
		sum.len() == 1,
		N > 0,
		N < 1000,
		forall |k: int| 0 <= k < i ==> a[k] == 1,
		decreases(N - i as int),
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	invariant
		i <= N as usize,
		a.len() == N,
		sum.len() == 1,
		N > 0,
		N < 1000,
		forall |k: int| 0 <= k < i ==> a[k] == 4,
		forall |k: int| i <= k < N as usize ==> a[k] == 1,
		decreases(N - i as int),
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 3);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	invariant
		i <= N as usize,
		a.len() == N,
		sum.len() == 1,
		N > 0,
		N < 1000,
		sum[0] == 4 * i as i32,
		forall |k: int| 0 <= k < N as usize ==> a[k] == 4,
		decreases(N - i as int),
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}

// Score: Compilation Error: False, Verified: 4, Errors: 0, Verus Errors: 0
// Safe: True