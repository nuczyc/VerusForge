
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
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
	while (i < N)
		invariant
			// Invariance about the length of `a` and `sum`
			a.len() == N,
			sum.len() == 1,
			// Invariance about the current state of `a`
			forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 1,
			// Tracking the loop variable
			0 <= i <= N,
			// Loop should progress and eventually terminate
			decreases(N - i),
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			// Invariance about the length of `a` and `sum`
			a.len() == N,
			sum.len() == 1,
			// Invariance about the current state of `a`
			forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 4,
			forall |k: usize| i <= k < N ==> a[( k ) as int] == 1,
			// Tracking the loop variable
			0 <= i <= N,
			// Loop should progress and eventually terminate
			decreases(N - i),
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 3);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

    i = 0;
    while (i < N)
        invariant
            // Invariance about the length of `a` and `sum`
            a.len() == N,
            sum.len() == 1,
            // Invariance about the current state of `a`
            forall |k: usize| 0 <= k < N ==> a[( k ) as int] == 4, // No a.set() in this loop, so a[] is never modified
            // Sum calculation
            sum[0] == 4 * i,
            // Tracking the loop variable
            0 <= i <= N,
            // Loop should progress and eventually terminate
            decreases(N - i),
    {
        if (a[i] == 4) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}
}
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True