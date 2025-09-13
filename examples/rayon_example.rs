//! Example showing rayon parallel iteration with HashTrieMapSync
//!
//! Run with: cargo run --features rayon --example rayon_example

#[cfg(feature = "rayon")]
fn main() {
    use rayon::iter::{IntoParallelIterator, ParallelIterator};
    use rpds::HashTrieMapSync;
    use std::time::Instant;

    // Create a large map for demonstration
    let mut map = HashTrieMapSync::new_sync();
    for i in 0..1_000_000 {
        map.insert_mut(i, i * 2);
    }

    println!("Created map with {} entries", map.size());

    // Sequential iteration
    let start = Instant::now();
    let sequential_sum: i64 = (&map).iter().map(|(_, v)| *v as i64).sum();
    let sequential_time = start.elapsed();

    // Parallel iteration
    let start = Instant::now();
    let parallel_sum: i64 = (&map).into_par_iter().map(|(_, v)| *v as i64).sum();
    let parallel_time = start.elapsed();

    println!("Sequential sum: {} (took {:?})", sequential_sum, sequential_time);
    println!("Parallel sum:   {} (took {:?})", parallel_sum, parallel_time);
    println!("Results match: {}", sequential_sum == parallel_sum);
}

#[cfg(not(feature = "rayon"))]
fn main() {
    println!("This example requires the 'rayon' feature to be enabled.");
    println!("Run with: cargo run --features rayon --example rayon_example");
}
