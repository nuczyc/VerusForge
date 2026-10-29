
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] <= 3 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			sum.len() == 1,
			a.len() == N,
			b.len() == N,
			c.len() == N,
			forall |k: int| 0 <= k < i ==> a[k as int] == 1,
			N > 0,
			N < 1000,
		decreases(N as isize - i as isize)
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			sum.len() == 1,
			a.len() == N,
			sum[0] <= i,
			forall |k: int| 0 <= k < a.len() ==> a[k] == 1, // a is not changed within the loop
			N > 0,
			N < 1000,
		decreases(N as isize - i as isize)
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			sum.len() == 1,
			b.len() == N,
			c.len() == N,
			forall |k: int| 0 <= k < i ==> b[k as int] == 1,
			N > 0,
			N < 1000,
		decreases(N as isize - i as isize)
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			sum.len() == 1,
			b.len() == N,
			sum[0] <= N + i,
			forall |k: int| 0 <= k < b.len() ==> b[k] == 1, // b is not changed within the loop
			N > 0,
			N < 1000,
		decreases(N as isize - i as isize)
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			sum.len() == 1,
			c.len() == N,
			forall |k: int| 0 <= k < i ==> c[k as int] == 1,
			N > 0,
			N < 1000,
		decreases(N as isize - i as isize)
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			sum.len() == 1,
			c.len() == N,
			sum[0] <= 2 * N + i,
			forall |k: int| 0 <= k < c.len() ==> c[k] == 1, // c is not changed within the loop
			N > 0,
			N < 1000,
		decreases(N as isize - i as isize)
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}


// Score: Compilation Error: False, Verified: 7, Errors: 0, Verus Errors: 0
// Safe: True