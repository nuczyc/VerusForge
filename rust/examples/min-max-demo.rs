fn min_max_pair(a: u64, b: u64) -> (u64, u64) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

fn main() {
    let (lo, hi) = min_max_pair(5, 3);
    println!("{} {}", lo, hi);
    let (lo2, hi2) = min_max_pair(3, 5);
    println!("{} {}", lo2, hi2);
    let (lo3, hi3) = min_max_pair(0, u64::MAX);
    println!("{} {}", lo3, hi3);
}