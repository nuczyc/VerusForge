
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
    
pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires 
        old(a).len() == N,
        N <= 0x7FFF_FFFF,
    ensures
        sum <= 2 * N,
{
    let mut i: usize = 0;
    // Loop to modify array elements
    while (i < N as usize)
    // Start Loop Invariant Block
    invariant
        a.len() == N, // Ensure array length remains consistent
        forall |k: int| 0 <= k < i ==> a[k] <= 2, // All processed indices have values <= 2
        decreases(N as int - i as int), // Ensuring loop termination
    // End Loop Invariant Block
    {
        if a[i] > 2 
        {
            a.set(i, 2);
        } 
        i = i + 1;
    }

    i = 0;
    let mut sum: u32 = 0;
    // Loop to calculate the sum
    while (i < N as usize)
    // Start Loop Invariant Block
    invariant
        a.len() == N, // Ensure array length remains consistent
        sum <= 2 * i as u32, // Sum does not exceed twice the number of processed elements
        forall |k: int| 0 <= k < a.len() ==> old(a)[k] == a[k], // Ensure none of these values have changed because the array is not modified in this loop
        decreases(N as int - i as int), // Ensuring loop termination
    // End Loop Invariant Block
    {
        sum = sum + a[i];
        i = i + 1;
    }

    sum
}
}
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True