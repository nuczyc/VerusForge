
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

/*
 This lemma is often useful to put near the end of a loop body that has a loop invariant involving Seq::subrange(j, k), with k being the loop index. It will help prove the property of range j..k+1 of a Sequence based on the property held for range j..k of a Sequence.

 Example usage:
    while ( k < s.len() )
      invariant
          ...
          k <= s.len(),
          ...s@.subrange(j, k as int)...,
          ...
    {
       ...
       proof{
       	  lemma_seq_subrange_ascend(s@, j, k+1);
       }
       k = k + 1;
    }

 */

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0<= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j-1 ),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j-1));
}

#[verifier::loop_isolation(false)]
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    requires
        first.len() > 0,
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
{
    let mut replaced_list = Vec::new();
    let first_end = first.len() - 1;
    let mut index = 0;

    while index < first_end
        invariant
            first.len() > 0,
            first.len() == first.len(),
            replaced_list@ == first@.subrange(0, ( index ) as int),
            forall |k: int| 0 <= k < first.len() ==> first@.index(k) == first[k],
        decreases first_end - index,
    {
        replaced_list.push(first[index]);
        index += 1;
        proof{
            lemma_seq_subrange_ascend(first@, 0, ( index ) as int);
        }
    }
    index = 0;
    while index < second.len()
        invariant
            first.len() > 0,
            second.len() == second.len(),
            replaced_list@ == first@.subrange(0, ( first_end ) as int).add(second@.subrange(0, ( index ) as int)),
            forall |k: int| 0 <= k < second.len() ==> second@.index(k) == second[k],
        decreases second.len() - index,
    {
        replaced_list.push(second[index]);
        index += 1;
        proof{
            lemma_seq_subrange_ascend(second@, 0, ( index ) as int);
        }
    }
    proof {
        lemma_seq_subrange_all(first@);
        lemma_seq_subrange_all(second@);
    }
    replaced_list
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True