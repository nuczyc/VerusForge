
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
			a.len() == N,
			sum.len() == 1,
			forall |k: int| 0 <= k < i ==> a[k as int] == (k % 3) as i32,
			forall |k: int| i <= k < N as usize ==> old(a)[k] == a[k],
			decreases(N as usize - i),
	{
		a.set(i, (i % 3) as i32);
		i = i + 1;
	}

	i = 0;

	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |k: int| 0 <= k < N as usize ==> a[k] == (k % 3) as i32,
			i > 0 ==> sum[0] <= 2 * i as i32,
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