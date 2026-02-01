use std::sync::Mutex;
use std::thread;
use rand::Rng;

fn think_randomly(philosopher_id: usize) {
    let mut rng = rand::thread_rng();
    let think_time = rng.gen_range(1..=10);
    println!("Philosopher {} is thinking for {} seconds...", philosopher_id, think_time);
    thread::sleep(std::time::Duration::from_secs(think_time));
    println!("Philosopher {} is done thinking.", philosopher_id);
}

fn eat_randomly(philosopher_id: usize) {
    let mut rng = rand::thread_rng();
    let eat_time = rng.gen_range(1..=10);
    println!("Philosopher {} is eating for {} seconds...", philosopher_id, eat_time);
    thread::sleep(std::time::Duration::from_secs(eat_time));
    println!("Philosopher {} is done eating.", philosopher_id);
}

static FORK_1_2: Mutex<()> = Mutex::new(());
static FORK_2_3: Mutex<()> = Mutex::new(());
static FORK_3_4: Mutex<()> = Mutex::new(());
static FORK_4_5: Mutex<()> = Mutex::new(());
static FORK_5_1: Mutex<()> = Mutex::new(());

fn main() {
    let handle1 = thread::spawn(|| {
        loop {
            think_randomly(1);
            let _guard1 = FORK_1_2.lock().unwrap();
            let _guard2 = FORK_5_1.lock().unwrap();
            eat_randomly(1);
        }
    });
    let handle2 = thread::spawn(|| {
        loop {
            think_randomly(2);
            let _guard1 = FORK_1_2.lock().unwrap();
            let _guard2 = FORK_2_3.lock().unwrap();
            eat_randomly(2);
        }
    });
    let handle3 = thread::spawn(|| {
        loop {
            think_randomly(3);
            let _guard1 = FORK_2_3.lock().unwrap();
            let _guard2 = FORK_3_4.lock().unwrap();
            eat_randomly(3);
        }
    });
    let handle4 = thread::spawn(|| {
        loop {
            think_randomly(4);
            let _guard1 = FORK_3_4.lock().unwrap();
            let _guard2 = FORK_4_5.lock().unwrap();
            eat_randomly(4);
        }
    });
    let handle5 = thread::spawn(|| {
        loop {
            think_randomly(5);
            let _guard1 = FORK_4_5.lock().unwrap();
            let _guard2 = FORK_5_1.lock().unwrap();
            eat_randomly(5);
        }
    });
    handle1.join().unwrap();
    handle2.join().unwrap();
    handle3.join().unwrap();
    handle4.join().unwrap();
    handle5.join().unwrap();
}
