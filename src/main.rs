use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let fork0 = Arc::new(Mutex::new(()));
    let fork1 = Arc::new(Mutex::new(()));
    let fork2 = Arc::new(Mutex::new(()));
    let fork3 = Arc::new(Mutex::new(()));
    let fork4 = Arc::new(Mutex::new(()));

    let mut handles = vec![];

    for i in 0..5 {
        let (fork_left, fork_right) = match i {
            0 => (Arc::clone(&fork0), Arc::clone(&fork1)),
            1 => (Arc::clone(&fork1), Arc::clone(&fork2)),
            2 => (Arc::clone(&fork2), Arc::clone(&fork3)),
            3 => (Arc::clone(&fork3), Arc::clone(&fork4)),
            4 => (Arc::clone(&fork0), Arc::clone(&fork4)),
            _ => unreachable!(),
        };

        let handle = thread::spawn(move || {
            let (first_fork, second_fork) = if i == 4 {
                (fork_right, fork_left)
            } else {
                (fork_left, fork_right)
            };

            let _guard1 = first_fork.lock().unwrap();
            let _guard2 = second_fork.lock().unwrap();

            println!("Philosopher {} is eating", i);
            thread::sleep(std::time::Duration::from_millis(100));
            println!("Philosopher {} is done eating", i);
        });

        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
