
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

proof fn lemma_fib_monotonic(n: int)
    ensures
        forall |i: int| 0 <= i <= n ==> #[trigger] fibo(i) <= fibo(n)
    decreases n
{
    if n > 0 {
        lemma_fib_monotonic(n-1);
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
    invariant
        fib.len() == i,
        fibo_fits_i32(n as int),
        forall |j: int| 2 <= j < i ==> fib[j] == fibo(j as int),
    decreases (n - i)
    {
        // Assert to ensure no overflow when calculating next_fib
        assert(fib[i - 1] as int + fib[i - 2] as int <= i32::MAX as int) by {
            lemma_fib_monotonic(i as int - 1);
        }

        let next_fib = fib[i - 1] + fib[i - 2];

        fib.push(next_fib);
        
        i += 1;
    }

    fib
}
}

// Score: Compilation Error: False, Verified: 2, Errors: 4, Verus Errors: 4
// Safe: True