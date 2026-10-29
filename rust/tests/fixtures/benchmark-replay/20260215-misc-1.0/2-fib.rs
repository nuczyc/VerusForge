
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

proof fn lemma_fibo_monotonicity(i: int, j: int)
    requires
        0 <= i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases j
{
    if i < j {
        lemma_fibo_monotonicity(i, j - 1);
        assert(fibo(i) <= fibo(j - 1));
    }
}

fn fibonacci(n: usize) -> (ret: Vec<i32>)
requires
    fibo_fits_i32(n as int),
    n >= 2,
ensures
    forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] ==  fibo(i), 
    ret@.len() == n,
{
    let mut fib = Vec::new();
    fib.push(0);
    fib.push(1);
    let mut i = 2;

    while i < n
    invariant
        n >= 2,
        fib.len() == i,
        forall |k: int| 0 <= k < fib.len() ==> (k < 2 || fib@[k] == fibo(k as int)),
    decreases n - i,
    {
        // Assertions to ensure safe access and prevent overflow
        assert(i >= 2);
        assert(fib[i - 1] + fib[i - 2] == fibo(i as int));
        assert(fibo(i as int) < 0x8000_0000);

        let next_fib = fib[i - 1] + fib[i - 2];
        fib.push(next_fib);
        
        i += 1;
    }

    fib
}
}

// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3
// Safe: True