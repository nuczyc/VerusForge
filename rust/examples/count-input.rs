use vstd::prelude::*;
fn main() {}
verus! {
fn count(n: u64) -> (r: u64)
    requires n < 100,
    ensures r == n,
{
    let mut i = 0;
    while i < n
        decreases n - i,
    {
        i = i + 1;
    }
    i
}
}
