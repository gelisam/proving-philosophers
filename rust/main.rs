use std::sync::Mutex;
use std::thread;
use rand::Rng;

static FORK0: Mutex<()> = Mutex::new(());
static FORK1: Mutex<()> = Mutex::new(());
static FORK2: Mutex<()> = Mutex::new(());
static FORK3: Mutex<()> = Mutex::new(());
static FORK4: Mutex<()> = Mutex::new(());

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
    // Philosopher 0: picks up fork0 then fork1
    let handle0 = thread::spawn(|| {
        loop {
            think_randomly(0);
            let _guard1 = FORK0.lock().unwrap();
            let _guard2 = FORK1.lock().unwrap();
            eat_randomly(0);
        }
    });

    // Philosopher 1: picks up fork1 then fork2
    let handle1 = thread::spawn(|| {
        loop {
            think_randomly(1);
            let _guard1 = FORK1.lock().unwrap();
            let _guard2 = FORK2.lock().unwrap();
            eat_randomly(1);
        }
    });

    // Philosopher 2: picks up fork2 then fork3
    let handle2 = thread::spawn(|| {
        loop {
            think_randomly(2);
            let _guard1 = FORK2.lock().unwrap();
            let _guard2 = FORK3.lock().unwrap();
            eat_randomly(2);
        }
    });

    // Philosopher 3: picks up fork3 then fork4
    let handle3 = thread::spawn(|| {
        loop {
            think_randomly(3);
            let _guard1 = FORK3.lock().unwrap();
            let _guard2 = FORK4.lock().unwrap();
            eat_randomly(3);
        }
    });

    // Philosopher 4: picks up fork4 then fork0 (reversed order to prevent deadlock)
    let handle4 = thread::spawn(|| {
        loop {
            think_randomly(4);
            let _guard1 = FORK4.lock().unwrap();
            let _guard2 = FORK0.lock().unwrap();
            eat_randomly(4);
        }
    });

    handle0.join().unwrap();
    handle1.join().unwrap();
    handle2.join().unwrap();
    handle3.join().unwrap();
    handle4.join().unwrap();
}
