
use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_index_invariant(index: nat)
    ensures
        2 * index == index + index,
{
    assert(index + index == 2 * index);
}

proof fn lemma_final_index_equals_len(total_len: nat, current_index: nat)
    requires
        current_index == total_len,
    ensures
        2 * current_index == 2 * total_len,
{
    assert(current_index == total_len);
    assert(2 * current_index == 2 * total_len);
}

proof fn lemma_invariant_holds(result: Seq<i32>, elem: i32, arr: Seq<i32>, index: nat)
    requires
        result.len() == 2 * index,
        forall |k: int| 0 <= k < result.len() ==> 
            (k % 2 == 0 ==> result[k] == elem) && 
            (k % 2 == 1 ==> result[k] == arr[k / 2]),
{
    assert(forall |k: int| 0 <= k < 2 * index ==> 
           (k % 2 == 0 ==> result[k] == elem) && 
           (k % 2 == 1 ==> result[k] == arr[k / 2]));
}

#[verifier::loop_isolation(false)]
fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()),
        forall |k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall |k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len() 
        invariant
            arr.len() == arr.len(), 
            result.len() == 2 * index,
            forall |k: int| 0 <= k < result.len() ==> 
                (k % 2 == 0 ==> result[k] == elem) && 
                (k % 2 == 1 ==> result[k] == arr[k / 2]),
        decreases arr.len() - index 
    {
        result.push(elem);
        result.push(arr[index]);
        index += 1;

        proof {
            lemma_invariant_holds(result@, elem, arr@, index as nat);
        }
    }
    proof {
        assert(index == arr.len());
        lemma_index_invariant((arr.len()) as nat);
        lemma_final_index_equals_len((arr.len()) as nat, (index) as nat);
        assert(result@.len() == 2 * arr.len()); 
    }
    result
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: True