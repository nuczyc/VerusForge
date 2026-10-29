
use vstd::prelude::*;

fn main() {}

verus! {

proof fn maintain_length_equality(arr: Seq<u64>, copied_array: Seq<u64>, index: int)
    requires
        index <= arr.len(),
        copied_array.len() == index,
    ensures
        arr.len() == copied_array.len() + index
{
    assert(copied_array.len() == index);
    assert(arr.len() == arr.len());
    assert(arr.len() == copied_array.len() + index);
}

proof fn lemma_copied_array_length(copied_array: Seq<u64>, index: int)
    ensures
        copied_array.len() == index
{
    assert(copied_array.len() == index);
}

fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    let mut copied_array = Vec::with_capacity(arr.len());
    let mut index = 0;
    
    proof {
        lemma_copied_array_length(copied_array@, index as int);
        maintain_length_equality(arr@, copied_array@, index as int);
    }
    
    while index < arr.len() 
        invariant
            arr.len() >= 0,
            arr@.len() == copied_array@.len() + index,
            forall|i: int| (0 <= i < copied_array@.len()) ==> arr[i] == copied_array[i],
        decreases arr.len() - index,
    {
        copied_array.push(arr[index]);
        index += 1;
        
        proof {
            lemma_copied_array_length(copied_array@, index as int);
            maintain_length_equality(arr@, copied_array@, index as int);
        }
    }

    proof {
        assert(forall|i: int| (0 <= i < arr@.len()) ==> arr[i] == copied_array[i]);
    } 
    copied_array
}

}

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True