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
