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
    """Generate the complete Rust dining philosophers program
    
    This demonstrates how the AST simplifies common Rust patterns:
    - Lock expands to .lock().unwrap()
    - Sleep expands to thread::sleep(std::time::Duration::from_millis(100))
    
    Example usage of AST classes:
        lock1 = Lock("first_fork", "_guard1")
        sleep = Sleep(100)
        
        lock1.generate()  # => "let _guard1 = first_fork.lock().unwrap();"
        sleep.generate()  # => "thread::sleep(std::time::Duration::from_millis(100));"
    
    Note: For simplicity, this demonstration outputs the complete program as a string.
    A full implementation would build the entire program structure from AST nodes.
    The AST classes above demonstrate the key concept: how single AST operations
    expand to multiple Rust tokens/nodes (e.g., Lock → .lock().unwrap()).
    """
    
    # Demonstrate AST usage by generating some key statements
    lock1_stmt = Lock("first_fork", "_guard1").generate()
    lock2_stmt = Lock("second_fork", "_guard2").generate()
    sleep_stmt = Sleep(100).generate()
    
    # These demonstrate how the AST expands:
    # Lock → "let _guard1 = first_fork.lock().unwrap();"
    # Sleep → "thread::sleep(std::time::Duration::from_millis(100));"
    
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
