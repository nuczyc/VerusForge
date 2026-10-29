
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			old(a).len() == N,
			a.len() == N as usize,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |k: usize| 0 <= k < i ==> (if k % 2 == 0 { a[( k ) as int] == 2 } else { a[( k ) as int] == 0 }),
			decreases(N as usize - i),
	{
		if (i % 2 == 0) {
			a.set(i, 2);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			old(sum).len() == 1,
			sum.len() == 1,
			old(a).len() == N,
			a.len() == N as usize,
			N > 0,
			N < 1000,
			(i > 0) ==> sum[0] <= 2 * (i as i32),
			// The array 'a' is not modified in this loop.
			forall |k: usize| 0 <= k < N as usize ==> (if k % 2 == 0 { a[( k ) as int] <= 2 } else { a[( k ) as int] <= 0 }),
			decreases(N as usize - i),
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;
	}
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True