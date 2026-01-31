use std::sync::{Arc, Mutex};
use std::thread;
use rand::Rng;

fn think_randomly(philosopher_id: usize) {
    let mut rng = rand::thread_rng();
    let think_time = rng.gen_range(1..=10);
    println!("Philosopher {} is thinking", philosopher_id);
    thread::sleep(std::time::Duration::from_secs(think_time));
}

fn eat_randomly(philosopher_id: usize) {
    let mut rng = rand::thread_rng();
    let eat_time = rng.gen_range(1..=10);
    println!("Philosopher {} is eating", philosopher_id);
    thread::sleep(std::time::Duration::from_secs(eat_time));
    println!("Philosopher {} is done eating", philosopher_id);
}

fn main() {
    let fork0 = Arc::new(Mutex::new(()));
    let fork1 = Arc::new(Mutex::new(()));
    let fork2 = Arc::new(Mutex::new(()));
    let fork3 = Arc::new(Mutex::new(()));
    let fork4 = Arc::new(Mutex::new(()));

    // Philosopher 0: picks up fork0 then fork1
    let fork0_p0 = Arc::clone(&fork0);
    let fork1_p0 = Arc::clone(&fork1);
    let handle0 = thread::spawn(move || {
        loop {
            think_randomly(0);
            let _guard1 = fork0_p0.lock().unwrap();
            let _guard2 = fork1_p0.lock().unwrap();
            eat_randomly(0);
        }
    });

    // Philosopher 1: picks up fork1 then fork2
    let fork1_p1 = Arc::clone(&fork1);
    let fork2_p1 = Arc::clone(&fork2);
    let handle1 = thread::spawn(move || {
        loop {
            think_randomly(1);
            let _guard1 = fork1_p1.lock().unwrap();
            let _guard2 = fork2_p1.lock().unwrap();
            eat_randomly(1);
        }
    });

    // Philosopher 2: picks up fork2 then fork3
    let fork2_p2 = Arc::clone(&fork2);
    let fork3_p2 = Arc::clone(&fork3);
    let handle2 = thread::spawn(move || {
        loop {
            think_randomly(2);
            let _guard1 = fork2_p2.lock().unwrap();
            let _guard2 = fork3_p2.lock().unwrap();
            eat_randomly(2);
        }
    });

    // Philosopher 3: picks up fork3 then fork4
    let fork3_p3 = Arc::clone(&fork3);
    let fork4_p3 = Arc::clone(&fork4);
    let handle3 = thread::spawn(move || {
        loop {
            think_randomly(3);
            let _guard1 = fork3_p3.lock().unwrap();
            let _guard2 = fork4_p3.lock().unwrap();
            eat_randomly(3);
        }
    });

    // Philosopher 4: picks up fork4 then fork0 (reversed order to prevent deadlock)
    let fork0_p4 = Arc::clone(&fork0);
    let fork4_p4 = Arc::clone(&fork4);
    let handle4 = thread::spawn(move || {
        loop {
            think_randomly(4);
            let _guard1 = fork4_p4.lock().unwrap();
            let _guard2 = fork0_p4.lock().unwrap();
            eat_randomly(4);
        }
    });

    handle0.join().unwrap();
    handle1.join().unwrap();
    handle2.join().unwrap();
    handle3.join().unwrap();
    handle4.join().unwrap();
}
