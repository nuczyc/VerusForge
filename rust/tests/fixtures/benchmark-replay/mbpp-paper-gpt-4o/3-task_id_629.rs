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

#[verifier::loop_isolation(false)]

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    // Reveal Seq::filter so that Verus can use its specification
    reveal(Seq::filter);

    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant 
            arr.len() >= index, 
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr@[k],
        decreases arr.len() - index
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
        proof {
            assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)); // Added by AI
        }
    }
    proof {
        lemma_seq_subrange_all(arr@);
    }
    even_numbers
}

}

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True