#![no_std]
extern crate alloc;
use alloc::{string::{String, ToString}, vec::Vec,vec};
use ulib::{
    sys,
    env, eprint, eprintln,
     fs::OpenOptions, print,
      println, 
      process::{Child, Command, Stdio},
       stdio::stdin,
};

fn main() {
    // Ensure that three file descriptors are open
    while let Ok(fd) = OpenOptions::new().read(true).write(true).open("console") {
        if fd.get_fd() > 2 {
            drop(fd);
            break;
        }
    }

    let mut idx = 0;
    let mut children: Vec<Option<Child>> = vec![];
    println!("Launching benchmark");

    let startUptime = sys::uptime().unwrap();
    // read and run input commands.
    'mainL: loop {
        let mut args = env::args().skip(1).peekable();
        if args.peek().is_none() {
            panic!("Usage: benchmark number_of_groups");
        }
    
        let n = args.next().unwrap();
        let nInt = n.parse::<usize>().unwrap();

        idx += 1;
        if idx > nInt {
            break 'mainL;
        }
        let mut input = "sendData|recvData".to_string();

        let mut commands = input.trim().split('|').enumerate().peekable();
        let mut previous_command: Option<Child> = None;

        while let Some((num, command)) = commands.next() {
            let mut parts = command.split_whitespace();
            match command {

                command => {
                    let stdin = previous_command
                        .map_or(Stdio::Inherit, |pc| Stdio::from(pc.stdout.unwrap()));
                    let mut stdout = if commands.peek().is_some() {
                        Stdio::MakePipe
                    } else {
                        Stdio::Inherit
                    };



                    let timeDiff = sys::uptime().unwrap() - startUptime;
                    let sleepTime = (nInt*5) - timeDiff;
                    match Command::new(command)
                    .args(vec![&idx.to_string(),&sleepTime.to_string()])
                        .stdin(stdin)
                        .stdout(stdout)
                        .spawn()
                    {
                        Ok(child) => previous_command = Some(child),
                        Err(e) => {
                            previous_command = None;
                            eprintln!("{}", e);
                        }
                    }
                }
            }
        }

        children.push(previous_command);
        
    }

    println!("All processes launched!");
    for child in children {
        if let Some(mut unwrappedChild) = child {
            unwrappedChild.wait();
        }
        else {

        }
}


}
