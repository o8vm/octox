#![no_std]
extern crate alloc;
use alloc::{
    string::{String, ToString},
    vec::Vec,
};
use ulib::{
    env, eprint, eprintln,
    fs::{File, OpenOptions},
    io::{BufRead, BufReader},
    path::Path,
    print, println,
    process::{Child, Command, Stdio},
    stdio::stdin,
    sys,
};

fn main() {
    // Ensure that three file descriptors are open
    while let Ok(fd) = OpenOptions::new()
        .read(true)
        .write(true)
        .open("/dev/console")
    {
        if fd.get_fd() > 2 {
            drop(fd);
            break;
        }
    }
    set_path_fron_etc_paths().unwrap();

    // read and run input commands.
    'main: loop {
        print!("$ ");

        let mut input = String::new();
        stdin().read_line(&mut input).unwrap();

        let mut commands = input.trim().split('|').enumerate().peekable();
        let mut previous_command: Option<Child> = None;

        while let Some((num, command)) = commands.next() {
            let mut parts = command.split_whitespace();
            let Some(command) = parts.next() else {
                continue 'main;
            };
            let mut args = parts.peekable();

            match command {
                "cd" => {
                    if num == 0 {
                        // chdir must be called by the parent. if in child do nothing any more.
                        let new_dir = args.peek().map_or("/", |x| *x);
                        if let Err(e) = env::set_current_dir(new_dir) {
                            eprintln!("{}", e);
                        }
                    }
                    continue 'main;
                }
                "export" => {
                    if args.peek().map_or(true, |x| *x == "-p") {
                        for (key, value) in env::vars() {
                            println!("{}: {}", key, value);
                        }
                    } else {
                        for arg in args {
                            if let Some((key, value)) = arg.split_once('=') {
                                if let Err(e) = env::set_var(key, value) {
                                    eprintln!("{}", e);
                                }
                            } else {
                                eprintln!("export: invalid argument: {}", arg);
                            }
                        }
                    }
                    continue 'main;
                }
                "exit" => return,
                command => {
                    let stdin = previous_command
                        .map_or(Stdio::Inherit, |pc| Stdio::from(pc.stdout.unwrap()));
                    let mut stdout = if commands.peek().is_some() {
                        Stdio::MakePipe
                    } else {
                        Stdio::Inherit
                    };

                    let rawstring;
                    let mut file_name = "";
                    let mut overwrite = true;
                    let mut append = false;
                    let mut arg_vec = Vec::new();
                    while let Some(arg) = args.next_if(|s| !s.contains('>')) {
                        arg_vec.push(arg);
                    }
                    if let Some(redir) = args.peek() {
                        if redir.contains(">>") {
                            overwrite = false;
                            append = true;
                        }
                        rawstring = args.collect::<Vec<&str>>().concat();
                        let splited = rawstring.split('>');
                        for (i, e) in splited.enumerate() {
                            if e.is_empty() {
                                continue;
                            }
                            if i == 0 {
                                arg_vec.push(e);
                            } else {
                                file_name = e;
                            }
                        }
                        assert!(!file_name.is_empty(), "redirect");
                        stdout = Stdio::Fd(
                            OpenOptions::new()
                                .create(true)
                                .write(true)
                                .truncate(overwrite)
                                .append(append)
                                .open(file_name)
                                .unwrap(),
                        );
                    }

                    match Command::new(command)
                        .args(arg_vec)
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

        if let Some(mut final_command) = previous_command {
            final_command.wait().unwrap();
        }
    }
}

fn set_path_fron_etc_paths() -> sys::Result<()> {
    let path_file = "/etc/paths";
    if Path::new(path_file).exists() {
        let file = BufReader::new(File::open(path_file)?);
        let mut paths: Vec<String> = env::var("PATH")
            .unwrap_or_default()
            .split(':')
            .filter(|s| !s.is_empty())
            .map(String::from)
            .collect();
        for line in file.lines() {
            if let Ok(path) = line {
                paths.push(path);
            }
        }
        let new_path = paths.join(":");
        env::set_var("PATH", &new_path);
    }
    Ok(())
}
