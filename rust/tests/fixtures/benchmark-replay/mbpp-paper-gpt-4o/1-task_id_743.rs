
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn rotation_split(len: usize, n: usize) -> int {
    len - (n % len)
}

fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
    requires
        list.len() > 0,
    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
{
    let rotation = n % list.len();
    let split_index = list.len() - rotation;
    let mut new_list = Vec::with_capacity(list.len());
    let mut index = split_index;

    while index < list.len()
    invariant
        list.len() > 0,
        new_list.len() <= list.len(),
        forall |k: int| 0 <= k && k < new_list.len() ==> new_list[k] == list[(k + split_index) % ( list.len() ) as int] // Fixed by AI
    decreases list.len() - index // Added by AI
    {
        new_list.push(list[index]);
        index += 1;
    }
    index = 0;
    while index < split_index
    invariant
        list.len() > 0,
        new_list.len() <= list.len(),
        forall |k: int| 0 <= k && k < new_list.len() ==> new_list[k] == list[(k + split_index) % ( list.len() ) as int] // Fixed by AI
    decreases split_index - index // Added by AI
    {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!



// Score: Compilation Error: False, Verified: 0, Errors: 7, Verus Errors: 7
// Safe: True