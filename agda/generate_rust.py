#!/usr/bin/env python3
"""
This script simulates the Agda code generator.
It defines an AST for simplified Rust operations and generates the complete
Rust dining philosophers implementation.
"""

class Stmt:
    """Base class for AST statements"""
    pass

class Lock(Stmt):
    """Lock operation that expands to .lock().unwrap()"""
    def __init__(self, fork, guard):
        self.fork = fork
        self.guard = guard
    
    def generate(self):
        return f"let {self.guard} = {self.fork}.lock().unwrap();"

class Sleep(Stmt):
    """Sleep operation that expands to thread::sleep(Duration::from_millis(...))"""
    def __init__(self, millis):
        self.millis = millis
    
    def generate(self):
        return f"thread::sleep(std::time::Duration::from_millis({self.millis}));"

class Print(Stmt):
    """Print statement"""
    def __init__(self, msg):
        self.msg = msg
    
    def generate(self):
        return f'println!("{self.msg}");'

def generate_program():
    """Generate the complete Rust dining philosophers program"""
    
    # The AST simplifies common patterns:
    # - Lock expands to .lock().unwrap()
    # - Sleep expands to thread::sleep(std::time::Duration::from_millis(100))
    
    program = """use std::sync::{Arc, Mutex};
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
"""
    return program

if __name__ == "__main__":
    print(generate_program(), end='')
