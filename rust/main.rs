use std::sync::{Arc, Mutex};
use std::thread;
use rand::Rng;

fn eat(philosopher: usize) {
    let duration = rand::thread_rng().gen_range(50..150);
    println!("Philosopher {} is eating", philosopher);
    thread::sleep(std::time::Duration::from_millis(duration));
    println!("Philosopher {} is done eating", philosopher);
}

fn think(philosopher: usize) {
    let duration = rand::thread_rng().gen_range(50..150);
    println!("Philosopher {} is thinking", philosopher);
    thread::sleep(std::time::Duration::from_millis(duration));
    println!("Philosopher {} is done thinking", philosopher);
}

fn main() {
    let fork0 = Arc::new(Mutex::new(()));
    let fork1 = Arc::new(Mutex::new(()));
    let fork2 = Arc::new(Mutex::new(()));
    let fork3 = Arc::new(Mutex::new(()));
    let fork4 = Arc::new(Mutex::new(()));

    let mut handles = vec![];

    // Philosopher 0
    {
        let fork0_clone = Arc::clone(&fork0);
        let fork1_clone = Arc::clone(&fork1);
        let handle = thread::spawn(move || {
            let _guard0 = fork0_clone.lock().unwrap();
            let _guard1 = fork1_clone.lock().unwrap();
            eat(0);
        });
        handles.push(handle);
    }

    // Philosopher 1
    {
        let fork1_clone = Arc::clone(&fork1);
        let fork2_clone = Arc::clone(&fork2);
        let handle = thread::spawn(move || {
            let _guard1 = fork1_clone.lock().unwrap();
            let _guard2 = fork2_clone.lock().unwrap();
            eat(1);
        });
        handles.push(handle);
    }

    // Philosopher 2
    {
        let fork2_clone = Arc::clone(&fork2);
        let fork3_clone = Arc::clone(&fork3);
        let handle = thread::spawn(move || {
            let _guard2 = fork2_clone.lock().unwrap();
            let _guard3 = fork3_clone.lock().unwrap();
            eat(2);
        });
        handles.push(handle);
    }

    // Philosopher 3
    {
        let fork3_clone = Arc::clone(&fork3);
        let fork4_clone = Arc::clone(&fork4);
        let handle = thread::spawn(move || {
            let _guard3 = fork3_clone.lock().unwrap();
            let _guard4 = fork4_clone.lock().unwrap();
            eat(3);
        });
        handles.push(handle);
    }

    // Philosopher 4 (reversed order to prevent deadlock)
    {
        let fork0_clone = Arc::clone(&fork0);
        let fork4_clone = Arc::clone(&fork4);
        let handle = thread::spawn(move || {
            let _guard4 = fork4_clone.lock().unwrap();
            let _guard0 = fork0_clone.lock().unwrap();
            eat(4);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
