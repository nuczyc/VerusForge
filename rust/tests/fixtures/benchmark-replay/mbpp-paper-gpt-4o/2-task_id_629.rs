
use vstd::prelude::*;

fn main() {}

verus! {
/*
 This lemma is often useful to put right after a loop that has a loop invariant involving Seq::subrange(0, i), with i being the loop index.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(0, k as int)...,
          ...
    {
       ...
       k = k + 1;
    }
    proof{
     	lemma_seq_subrange_all(s@);
    }
 */

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn lemma_seq_filter_all<T>(v: Seq<T>, predicate: FnSpec(T) -> bool)
    ensures
        v.filter(predicate) == v.subrange(0, v.len() as int).filter(predicate),
{
    assert(v.filter(predicate) =~= v.subrange(0, v.len() as int).filter(predicate));
}

proof fn lemma_seq_filter_ext<T>(v: Seq<T>, seq: Seq<T>, predicate: FnSpec(T) -> bool)
    requires
        forall |i: int| 0 <= i < seq.len() ==> seq[i] == v[i],
    ensures
        seq.filter(predicate) == v.filter(predicate),
{
    lemma_seq_filter_all(seq, predicate);
    lemma_seq_filter_all(v, predicate);
    assert(seq.subrange(0, seq.len() as int).filter(predicate) =~= v.subrange(0, v.len() as int).filter(predicate));
}

#[verifier::loop_isolation(false)]
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    reveal(Seq::filter); // Reveal the filter function

    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
        invariant 
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], 
            even_numbers@ == arr@.subrange(0, ( index ) as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - index,
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
    }
    
    proof {
       lemma_seq_subrange_all(arr@);
       lemma_seq_filter_ext(arr@, arr@, |x: u32| x % 2 == 0);
       assert(arr@.subrange(0, arr.len() as int).filter(|x: u32| x % 2 == 0) =~= arr@.filter(|x: u32| x % 2 == 0));
       assert(even_numbers@ == arr@.subrange(0, arr.len() as int).filter(|x: u32| x % 2 == 0));
       assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0));
    }
    
    even_numbers
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 4, Verus Errors: 4
// Safe: True