
use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
    ensures
        v == v.subrange(0, v.len() as int),
{
    assert(v =~= v.subrange(0, v.len() as int));
}

proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i:int, j: int)
    requires
        0 <= i < j <= v.len(),
    ensures
        v.subrange(i, j as int).drop_last() == v.subrange(i, j - 1),
{
    assert(v.subrange(i, j as int).drop_last() =~= v.subrange(i, j - 1));
}

fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
{
    let mut part1: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < l
        invariant 0 <= index <= l,
        decreases l - index,
    {
        part1.push(list[index]);
        index += 1;
    }
    let mut part2: Vec<i32> = Vec::new();
    index = l;
    while index < list.len()
        invariant l <= index <= list.len(),
        decreases list.len() - index,
    {
        part2.push(list[index]);
        index += 1;
    }
    proof {
        assert(part1@ == list@.subrange(0, l as int));
        lemma_seq_subrange_ascend(list@, l as int, list.len() as int);
        lemma_seq_subrange_all(list@);
        assert(part2@ == list@.subrange(l as int, list.len() as int));
    }
    (part1, part2)
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 3, Verus Errors: 3
// Safe: True