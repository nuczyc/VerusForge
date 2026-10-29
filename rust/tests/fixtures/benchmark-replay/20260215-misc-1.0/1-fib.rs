#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
spec fn fibo(n: int) -> nat
    decreases n
{
    if n <= 0 { 0 } else if n == 1 { 1 }
    else { fibo(n - 2) + fibo(n - 1) }
}

spec fn fibo_fits_i32(n: int) -> bool {
    fibo(n) < 0x8000_0000
}

proof fn lemma_monotonic_fibo(i: int, j: int)
    requires
        i <= j,
    ensures
        fibo(i) <= fibo(j)
    decreases j
{
    if i < j {
        lemma_monotonic_fibo(i, j - 1);
        lemma_monotonic_fibo(j - 1, j);
    }
}

fn fibonacci(n: usize) -> (ret: Vec<i32>)
requires
    fibo_fits_i32(n as int),
    n >= 2,
ensures
    forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] == fibo(i), 
    ret@.len() == n,
{
    let mut fib = Vec::new();
    fib.push(0);
    fib.push(1);
    let mut i = 2;

    while i < n
    invariant fibo_fits_i32(n as int),
              n >= 2,
              fib@.len() == i,
              forall |k: int| 0 <= k < fib@.len() ==> #[trigger] fib@[k] == if k == 0 { 0 } else if k == 1 { 1 } else { fib@[k - 1] + fib@[k - 2] }, 
              fibo_fits_i32(i as int), // Added invariant for i instead of asserting inside the loop
    decreases n - i
    {
        let next_fib = fib[i - 1] + fib[i - 2];
        fib.push(next_fib);
        i += 1;
    }

    fib
}
}
// Score: Compilation Error: False, Verified: 1, Errors: 6, Verus Errors: 6
// Safe: True