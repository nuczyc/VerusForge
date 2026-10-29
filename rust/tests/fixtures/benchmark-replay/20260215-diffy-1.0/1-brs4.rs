
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
		sum[0] <= 4 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			old(a).len() == N,
			a.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |k: int| 0 <= k < i as int ==> (if k % 4 == 0 { a[k as int] == 4 } else { a[k as int] == 0 }),
			decreases(N as isize - i as isize)
	{
		if (i % 4 == 0) {
			a.set(i, 4);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			0 <= i <= N,
			old(a).len() == N,
			a.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			(i > 0) ==> (sum[0] <= 4 * i as i32),
			// sum is being modified in the loop.
			decreases(N as isize - i as isize)
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