#![no_std]

extern crate alloc;

use core::cell::RefCell;
use core::fmt::Display;
use core::iter::zip;

use alloc::vec;

use alloc::{
    collections::VecDeque,
    fmt, format,
    rc::Rc,
    string::{String, ToString},
    vec::Vec,
};

use ulib::fs::File;
use ulib::io::Read;
use ulib::stdio::stdin;
use ulib::{env, eprint, eprintln, print, println};

#[derive(Debug, Clone)]
enum Expr {
    Symbol(String),
    Keyword(String),
    String(String),
    Int(isize),
    Float(f64),
    Bool(bool),
    Lambda(Vec<String>, Vec<Expr>, Rc<RefCell<Environment>>),
    Nil,

    List(Rc<Vec<Expr>>),
    Vector(Rc<Vec<Expr>>),
    Set(Rc<Vec<Expr>>),
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, &other) {
            (Expr::Symbol(a), Expr::Symbol(b)) => a == b,
            (Expr::Keyword(a), Expr::Keyword(b)) => a == b,
            (Expr::String(a), Expr::String(b)) => a == b,
            (Expr::Int(a), Expr::Int(b)) => a == b,
            (Expr::Float(a), Expr::Float(b)) => a == b,
            (Expr::Bool(a), Expr::Bool(b)) => a == b,
            (Expr::Nil, Expr::Nil) => true,
            (Expr::List(a), Expr::List(b)) => a == b,
            (Expr::Vector(a), Expr::Vector(b)) => a == b,
            (Expr::Set(a), Expr::Set(b)) => a == b,
            _ => false,
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let value = self.clone();
        let s: String = match value {
            Expr::Symbol(symbol) => symbol,
            Expr::Keyword(keyword) => format!(":{}", keyword),
            Expr::String(string) => string,
            Expr::Int(i) => i.to_string(),
            Expr::Float(f) => f.to_string(),
            Expr::Bool(b) => match b {
                true => "true",
                false => "false",
            }
            .to_string(),
            Expr::Nil => "nil".to_string(),
            Expr::List(elems) => {
                format!(
                    "({})",
                    elems
                        .iter()
                        .map(|e| format!("{}", e))
                        .collect::<Vec<String>>()
                        .join(" ")
                )
            }
            Expr::Vector(elems) => {
                format!(
                    "[{}]",
                    elems
                        .iter()
                        .map(|e| format!("{}", e))
                        .collect::<Vec<String>>()
                        .join(" ")
                )
            }
            Expr::Set(elems) => {
                format!(
                    "#{{{}}}",
                    elems
                        .iter()
                        .map(|e| format!("{}", e))
                        .collect::<Vec<String>>()
                        .join(" ")
                )
            }
            Expr::Lambda(_, _, _) => "<lambda>".into(),
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug)]
enum Error {
    SyntaxError(String),
    LexicalError(String),
    RuntimeError(String),
}

#[derive(Debug, PartialEq, Clone)]
enum Token {
    Nil,             // nil
    Bool(bool),      // true, false
    Symbol(String),  // a10, abc, abc-def, ...
    Int(isize),      // 0, 1, ...
    Float(f64),      // 0.0, 0.1, ...
    String(String),  // "abc def", "abc \"def\"", ...
    Keyword(String), // :a10, :abc, ...

    LParen,      // "("
    RParen,      // ")"
    LBrace,      // "{"
    RBrace,      // "}"
    LBracket,    // "["
    RBracket,    // "]"
    LSharpBrace, // "#{"

    SingleQuote, // "'"

    EOF,
}

struct Lexer {
    input: Vec<char>,
    pos: usize,
    read_pos: usize,
    ch: char,
}

type LexerState = (usize, usize, char);

impl Lexer {
    fn new(input: &str) -> Self {
        let inp = input.chars().collect();
        let mut lexer = Lexer {
            input: inp,
            pos: 0,
            read_pos: 0,
            ch: '\0',
        };
        lexer.read_char();
        lexer
    }

    fn state(&self) -> LexerState {
        (self.pos, self.read_pos, self.ch)
    }

    fn set_state(&mut self, state: LexerState) {
        self.pos = state.0;
        self.read_pos = state.1;
        self.ch = state.2;
    }

    fn read_char(&mut self) -> Option<char> {
        if self.read_pos >= self.input.len() {
            self.ch = '\0';
        } else {
            self.ch = self.input[self.read_pos]
        }
        self.pos = self.read_pos;
        self.read_pos += 1;
        if self.ch == '\0' {
            return None;
        } else {
            return Some(self.ch);
        }
    }

    fn next(&mut self) -> Result<Token, Error> {
        self.skip_whitespaces();

        let result = match self.ch {
            '(' => Ok(Token::LParen),
            ')' => Ok(Token::RParen),
            '{' => Ok(Token::LBrace),
            '}' => Ok(Token::RBrace),
            '[' => Ok(Token::LBracket),
            ']' => Ok(Token::RBracket),
            '#' => {
                self.read_char();
                if self.ch == '{' {
                    self.read_char();
                    return Ok(Token::LSharpBrace);
                }
                return Err(Error::LexicalError(
                    "failed to tokenize left sharp brace".into(),
                ));
            }
            ':' => {
                self.read_char();
                let sym = self.read_symbol()?;
                return Ok(Token::Keyword(sym));
            }
            '"' => {
                self.read_char();
                let s = self.read_string()?;
                return Ok(Token::String(s));
            }
            '\'' => {
                self.read_char();
                return Ok(Token::SingleQuote);
            }

            '\0' => Ok(Token::EOF),

            c => {
                if self.ch == '-' {
                    let s = self.state();
                    match self.read_numeral() {
                        Ok(token) => return Ok(token),
                        Err(_) => self.set_state(s),
                    }
                }
                if is_alpha(c) || is_special_symbol(c) {
                    let sym = self.read_symbol()?;
                    return Ok(match sym.as_str() {
                        "true" => Token::Bool(true),
                        "false" => Token::Bool(false),
                        "nil" => Token::Nil,
                        _ => Token::Symbol(sym),
                    });
                } else if is_num(c) {
                    return self.read_numeral();
                }
                Err(Error::LexicalError(format!("{}", c)))
            }
        };
        self.read_char();
        result
    }

    fn tokenize(&mut self) -> Result<Vec<Token>, Error> {
        let mut tokens: Vec<Token> = vec![];
        loop {
            let token = self.next()?;
            if token == Token::EOF {
                break;
            }
            tokens.push(token.clone());
        }
        Ok(tokens)
    }

    fn read_symbol(&mut self) -> Result<String, Error> {
        if !is_alpha(self.ch) && !is_special_symbol(self.ch) {
            return Err(Error::LexicalError("not a symbol".into()));
        }
        let pos = self.pos;
        while is_alpha_num(self.ch) || is_special_symbol(self.ch) {
            self.read_char();
        }
        let x = &self.input[pos..self.pos];
        Ok(x.iter().collect())
    }

    fn read_numeral(&mut self) -> Result<Token, Error> {
        let pos = self.pos;
        let mut has_decimal = false;
        while is_num(self.ch) || self.ch == '.' || self.ch == '-' {
            if self.ch == '.' {
                has_decimal = true;
            }
            self.read_char();
        }
        let x = &self.input[pos..self.pos];
        let numeral = x.iter().collect::<String>();
        numeral.parse::<isize>();
        if has_decimal {
            let f = numeral
                .parse::<f64>()
                .or_else(|_| Err(Error::LexicalError("failed to parse float".into())))?;
            Ok(Token::Float(f))
        } else {
            let i = numeral
                .parse::<isize>()
                .or_else(|_| Err(Error::LexicalError("failed to parse int".into())))?;
            Ok(Token::Int(i))
        }
    }

    fn read_string(&mut self) -> Result<String, Error> {
        let pos = self.pos;
        while self.ch != '"' {
            if self.ch == '\0' {
                return Err(Error::LexicalError("unclosed string literal".into()));
            }
            self.read_char();
        }
        self.read_char();
        let x = &self.input[pos..self.pos - 1];
        match x.iter().collect::<String>().parse::<String>() {
            Ok(f) => Ok(unescape(f.as_str())),
            Err(_) => Err(Error::LexicalError("failed to read string".into())),
        }
    }

    fn skip_whitespaces(&mut self) {
        while is_whitespace(self.ch) {
            self.read_char();
        }
    }
}

struct Parser {
    tokens: VecDeque<Token>,
}

impl Parser {
    fn new(input: Vec<Token>) -> Self {
        let tokens = VecDeque::from(input);
        Parser { tokens }
    }

    fn parse_program(&mut self) -> Result<Vec<Expr>, Error> {
        let mut exprs: Vec<Expr> = vec![];
        while self.tokens.len() > 0 {
            let expr = self.parse()?;
            exprs.push(expr);
        }
        Ok(exprs)
    }

    fn parse(&mut self) -> Result<Expr, Error> {
        let token = self.tokens.pop_front().unwrap();
        let expr = match token {
            Token::Symbol(sym) => Expr::Symbol(sym),
            Token::Bool(b) => Expr::Bool(b),
            Token::Int(i) => Expr::Int(i),
            Token::Float(f) => Expr::Float(f),
            Token::String(s) => Expr::String(s),
            Token::Keyword(k) => Expr::Keyword(k),
            Token::LParen => {
                self.tokens.push_front(Token::LParen);
                self.parse_list()?
            }
            Token::LBrace => todo!(),
            Token::LBracket => {
                self.tokens.push_front(Token::LBracket);
                self.parse_vector()?
            }
            Token::LSharpBrace => {
                self.tokens.push_front(Token::LSharpBrace);
                self.parse_set()?
            }
            Token::SingleQuote => {
                let elem = self.parse()?;
                Expr::List(Rc::new(vec![Expr::Symbol("quote".into()), elem]))
            }
            t => panic!("unsupported token: {:?}", t),
        };
        Ok(expr)
    }

    fn parse_list(&mut self) -> Result<Expr, Error> {
        let mut elems = vec![];

        if self.tokens.front().unwrap().clone() != Token::LParen {
            return Err(Error::SyntaxError("expected LParen".into()));
        }
        self.tokens.pop_front().unwrap();

        while !self.tokens.is_empty() && self.tokens.front().unwrap().clone() != Token::RParen {
            let elem = self.parse().unwrap();
            elems.push(elem);
        }
        self.tokens.pop_front().unwrap();

        Ok(Expr::List(Rc::new(elems)))
    }

    fn parse_vector(&mut self) -> Result<Expr, Error> {
        let mut elems = vec![];

        if self.tokens.front().unwrap().clone() != Token::LBracket {
            return Err(Error::SyntaxError("expected LBracket".into()));
        }
        self.tokens.pop_front().unwrap();

        while !self.tokens.is_empty() && self.tokens.front().unwrap().clone() != Token::RBracket {
            let elem = self.parse().unwrap();
            elems.push(elem);
        }
        self.tokens.pop_front().unwrap();

        Ok(Expr::Vector(Rc::new(elems)))
    }

    fn parse_set(&mut self) -> Result<Expr, Error> {
        let mut elems = vec![];

        if self.tokens.front().unwrap().clone() != Token::LSharpBrace {
            return Err(Error::SyntaxError("expected LSharpBrace".into()));
        }
        self.tokens.pop_front().unwrap();

        while !self.tokens.is_empty() && self.tokens.front().unwrap().clone() != Token::RBrace {
            let elem = self.parse().unwrap();
            elems.push(elem);
        }
        self.tokens.pop_front().unwrap();

        Ok(Expr::Set(Rc::new(elems)))
    }
}

fn is_lower_alpha(c: char) -> bool {
    'a' <= c && c <= 'z'
}

fn is_upper_alpha(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

fn is_alpha(c: char) -> bool {
    is_lower_alpha(c) || is_upper_alpha(c)
}

fn is_num(c: char) -> bool {
    '0' <= c && c <= '9'
}

fn is_alpha_num(c: char) -> bool {
    is_alpha(c) || is_num(c)
}

fn is_whitespace(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

fn is_special_symbol(c: char) -> bool {
    c == '!'
        || c == '%'
        || c == '&'
        || c == '-'
        || c == '@'
        || c == '+'
        || c == '*'
        || c == '/'
        || c == '='
        || c == '<'
        || c == '>'
        || c == '?'
}

fn repl() {
    let mut line = String::new();
    let mut input = String::new();
    let mut env = Environment::new();
    let mut paren_stack: Vec<Token> = vec![];
    let mut tokens: Vec<Token> = vec![];
    let mut evaluator = Evaluator::new();
    loop {
        print!("user=> ");
        for _ in 0..paren_stack.len() {
            print!("  ");
        }
        if stdin().read_line(&mut line).is_err() {
            break;
        }

        let mut lexer = Lexer::new(line.as_str());
        line = "".to_string();

        let toks = lexer.tokenize().unwrap();
        for tok in toks.iter() {
            match tok.clone() {
                Token::LBrace => paren_stack.push(Token::LBrace),
                Token::LBracket => paren_stack.push(Token::LBracket),
                Token::LParen => paren_stack.push(Token::LParen),
                Token::LSharpBrace => paren_stack.push(Token::LSharpBrace),
                Token::RBrace => match paren_stack.last() {
                    Some(&Token::LBrace) => {
                        paren_stack.pop();
                    }
                    Some(&Token::LSharpBrace) => {
                        paren_stack.pop();
                    }
                    _ => panic!(),
                },
                Token::RBracket => match paren_stack.last() {
                    Some(&Token::LBracket) => {
                        paren_stack.pop();
                    }
                    _ => panic!(),
                },
                Token::RParen => match paren_stack.last() {
                    Some(&Token::LParen) => {
                        paren_stack.pop();
                    }
                    _ => panic!(),
                },
                _ => {}
            }
        }

        tokens.append(&mut toks.clone());

        if paren_stack.len() == 0 {
            input = "".to_string();
            if tokens.len() > 0 {
                let mut parser = Parser::new(tokens);
                match parser.parse() {
                    Ok(expr) => match evaluator.evaluate(expr, &mut env) {
                        Ok(expr) => println!("{}", expr),
                        Err(err) => eprintln!("error: {:?}", err),
                    },
                    Err(err) => panic!(),
                }
                tokens = vec![];
                println!("")
            }
        }
    }
}

fn exec_file(file: &str) -> Result<Expr, Error> {
    let mut file = File::open(file).unwrap();
    let mut program = "".to_string();
    file.read_to_string(&mut program);

    let mut lexer = Lexer::new(program.as_str());
    let tokens = lexer.tokenize()?;
    let mut parser = Parser::new(tokens);
    let exprs = parser.parse_program()?;
    let evaluator = Evaluator::new();
    let mut env = Environment::new();
    for expr in exprs.iter() {
        evaluator.evaluate(expr.clone(), &mut env)?;
    }
    println!("");
    Ok(Expr::Nil)
}

fn run(input: &str, evaluator: &mut Evaluator, env: &mut Environment) -> Result<Expr, Error> {
    let mut lexer = Lexer::new(input);
    let tokens = lexer.tokenize()?;
    let mut parser = Parser::new(tokens);
    let expr = parser.parse()?;
    evaluator.evaluate(expr, env)
}

fn main() {
    // jell_test();
    let args: Vec<&str> = env::args().skip(1).collect();
    if args.len() == 0 {
        repl()
    } else {
        exec_file(args[0]);
    }
}

fn jell_test() {
    lexer_test();
    parser_test();
    environment_test();
    evaluator_test();
}

#[derive(Debug, Clone, PartialEq)]
struct Environment {
    variables: VecDeque<(String, Expr)>,
}

impl Environment {
    fn new() -> Self {
        Environment {
            variables: VecDeque::new(),
        }
    }

    fn extend(&mut self, other: Environment) {
        for (sym, val) in other.variables.iter() {
            self.variables.push_back((sym.clone(), val.clone()))
        }
    }

    fn set(&mut self, name: &str, val: &Expr) {
        self.variables.push_front((name.into(), val.clone()))
    }

    fn get(&self, name: &str) -> Option<Expr> {
        for (sym, val) in self.variables.iter() {
            if sym.as_str() == name {
                return Some(val.clone());
            }
        }
        None
    }
}

struct Evaluator {
    global: Rc<RefCell<Environment>>,
}

impl Evaluator {
    fn new() -> Self {
        Evaluator {
            global: Rc::new(RefCell::new(Environment::new())),
        }
    }

    fn evaluate(&self, val: Expr, env: &mut Environment) -> Result<Expr, Error> {
        match val {
            Expr::Symbol(name) => env
                .get(name.as_str())
                .or(self.global.borrow().get(name.as_str()))
                .ok_or(Error::RuntimeError(
                    format!("symbol {} not found in environment", name).into(),
                )),
            Expr::List(elems) => self.evaluate_list(elems.to_vec(), env),
            Expr::Vector(elems) => self.evaluate_vector(elems.to_vec(), env),
            Expr::Set(_) => todo!(),

            Expr::Bool(_) => Ok(val),
            Expr::Keyword(_) => Ok(val),
            Expr::String(_) => Ok(val),
            Expr::Int(_) => Ok(val),
            Expr::Float(_) => Ok(val),
            Expr::Lambda(_, _, _) => Ok(val),
            Expr::Nil => Ok(val),
        }
    }

    fn evaluate_vector(&self, elems: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        let mut values = vec![];
        for elem in elems.iter() {
            let val = self
                .evaluate(elem.clone(), env)
                .expect("failed to evaluate vector element");
            values.push(val);
        }
        Ok(Expr::Vector(Rc::new(values)))
    }

    fn evaluate_list(&self, elems: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if elems.len() == 0 {
            Ok(Expr::List(elems.into()))
        } else {
            let head = elems[0].clone();
            let rest = &elems[1..];
            match head {
                Expr::Symbol(ref sym) => match sym.as_str() {
                    // special forms
                    "defmacro" => todo!(),
                    "eval" => self.evaluate_eval(rest.to_vec(), env),
                    "def" => self.evaluate_def(rest.to_vec(), env),
                    "if" => self.evaluate_if(rest.to_vec(), env),
                    "do" => self.evaluate_do(rest.to_vec(), env),
                    "let" => self.evaluate_let(rest.to_vec(), env),
                    "quote" => self.evaluate_quote(rest.to_vec(), env),
                    "fn" => self.evaluate_fn(rest.to_vec(), env),
                    "loop" => todo!(),
                    "recur" => todo!(),

                    "string?" => self.evaluate_stringp(rest.to_vec(), env),
                    "int?" => self.evaluate_intp(rest.to_vec(), env),
                    "float?" => self.evaluate_floatp(rest.to_vec(), env),
                    "keyword?" => self.evaluate_keywordp(rest.to_vec(), env),
                    "symbol?" => self.evaluate_symbolp(rest.to_vec(), env),
                    "list?" => self.evaluate_listp(rest.to_vec(), env),
                    "vector?" => self.evaluate_vectorp(rest.to_vec(), env),

                    "list" => self.evaluate_list_fn(rest.to_vec(), env),
                    "vector" => self.evaluate_vector_fn(rest.to_vec(), env),

                    "and" => self.evaluate_and(rest.to_vec(), env),
                    "or" => self.evaluate_or(rest.to_vec(), env),
                    "not" => self.evaluate_not(rest.to_vec(), env),

                    // functions
                    "+" => self.evaluate_add(rest.to_vec(), env),
                    "-" => self.evaluate_sub(rest.to_vec(), env),
                    "*" => self.evaluate_mult(rest.to_vec(), env),
                    "/" => self.evaluate_div(rest.to_vec(), env),
                    "=" => self.evaluate_eq(rest.to_vec(), env),
                    "<" => self.evaluate_less_than(rest.to_vec(), env),
                    "<=" => self.evaluate_less_than_or_eq(rest.to_vec(), env),
                    ">" => self.evaluate_greater_than(rest.to_vec(), env),
                    ">=" => self.evaluate_greater_than_or_eq(rest.to_vec(), env),

                    "first" => self.evaluate_first(rest.to_vec(), env),
                    "rest" => self.evaluate_rest(rest.to_vec(), env),
                    "conj" => self.evaluate_conj(rest.to_vec(), env),

                    "nth" => self.evaluate_nth(rest.to_vec(), env),
                    "count" => self.evaluate_count(rest.to_vec(), env),

                    "print" => self.evaluate_print(rest.to_vec(), env),

                    _ => {
                        // function call
                        let func = self.evaluate(head.clone(), env)?;
                        let mut lst = vec![func];
                        lst.append(&mut rest.to_vec());
                        self.evaluate(Expr::List(Rc::new(lst)), env)
                    }
                },
                Expr::Keyword(_) => todo!(),
                Expr::Lambda(vars, body, inner_env) => {
                    let mut let_args: Vec<Expr> = vec![];
                    if vars.len() != rest.len() {
                        return Err(Error::RuntimeError(format!(
                            "function takes {} arguments but got {} arguments",
                            vars.len(),
                            rest.len()
                        )));
                    }
                    for (name, val) in zip(vars, rest) {
                        let_args.push(Expr::Symbol(name));
                        let_args.push(Expr::List(Rc::new(vec![
                            Expr::Symbol("quote".into()),
                            self.evaluate(val.clone(), env)?,
                        ])));
                    }
                    let mut args = vec![Expr::Vector(Rc::new(let_args.clone()))];
                    args.append(&mut body.clone());
                    self.evaluate_let(args, &mut inner_env.borrow().clone())
                }
                Expr::List(elems) => {
                    let f = self.evaluate_list(elems.to_vec(), env)?;
                    let mut lst = vec![f];
                    lst.append(&mut rest.to_vec());
                    self.evaluate(Expr::List(Rc::new(lst)), env)
                }
                _ => Err(Error::RuntimeError(format!(
                    "{:?} can not be applied",
                    head.clone()
                ))),
            }
        }
    }

    fn evaluate_eval(&self, args: Vec<Expr>, _: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            return self.evaluate(args[0].clone(), &mut Environment::new());
        } else {
            return Err(Error::RuntimeError("eval takes 1 argument".into()));
        }
    }

    fn evaluate_def(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 2 {
            let mut e = env.clone();
            let first = args[0].clone();
            match first {
                Expr::Symbol(name) => {
                    let v = self.evaluate(args[1].clone(), &mut e)?;
                    match v {
                        Expr::Lambda(_, _, ref inner_env) => {
                            inner_env.borrow_mut().set(name.as_str(), &v);
                        }
                        _ => (),
                    };
                    e.set(name.as_str(), &v);
                    self.global.borrow_mut().set(name.as_str(), &v);
                    Ok(Expr::Nil)
                }
                _ => Err(Error::RuntimeError("def takes symbol and value".into())),
            }
        } else {
            Err(Error::RuntimeError("def takes symbol and value".into()))
        }
    }

    fn evaluate_if(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 3 {
            let test = args[0].clone();
            let test_result = self.evaluate(test, env)?;
            match test_result {
                Expr::Bool(b) => {
                    if b {
                        self.evaluate(args[1].clone(), env)
                    } else {
                        self.evaluate(args[2].clone(), env)
                    }
                }
                _ => Err(Error::RuntimeError(
                    "test must be evaluated to boolean".into(),
                )),
            }
        } else {
            Err(Error::RuntimeError("required 3 arguments for if".into()))
        }
    }

    fn evaluate_do(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        let mut v = Expr::Nil;
        for arg in args.iter() {
            v = self.evaluate(arg.clone(), env)?;
        }
        Ok(v)
    }

    fn evaluate_let(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() >= 1 {
            let binding = &args[0];

            let mut e = env.clone();

            match binding {
                Expr::Vector(elems) => {
                    if elems.len() % 2 == 0 {
                        for pair in elems.chunks(2) {
                            let sym = &pair[0];
                            let val = &pair[1];
                            match sym {
                                Expr::Symbol(name) => {
                                    let v = self.evaluate(val.clone(), &mut e)?;
                                    match v {
                                        Expr::Lambda(_, _, ref inner_env) => {
                                            inner_env.borrow_mut().set(name.as_str(), &v);
                                        }
                                        _ => (),
                                    };
                                    e.set(name.as_str(), &v);
                                }
                                _ => {
                                    return Err(Error::RuntimeError(
                                        "let binding only takes pairs of symbol and value".into(),
                                    ))
                                }
                            }
                        }
                    } else {
                        return Err(Error::RuntimeError(
                            "binding elements must be even number".into(),
                        ));
                    }
                }
                _ => return Err(Error::RuntimeError("binding must be vector".into())),
            }

            let mut v = Expr::Nil;
            for arg in args[1..].iter() {
                v = self.evaluate(arg.clone(), &mut e)?;
            }
            Ok(v)
        } else {
            Err(Error::RuntimeError(
                "required at least binding for let".into(),
            ))
        }
    }

    fn evaluate_quote(&self, args: Vec<Expr>, _env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            Ok(args[0].clone())
        } else {
            Err(Error::RuntimeError("required 1 argument for quote".into()))
        }
    }

    fn evaluate_fn(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() > 0 {
            let var_vector = &args[0];
            match var_vector {
                Expr::Vector(vars) => {
                    let mut names: Vec<String> = vec![];
                    for var in vars.iter() {
                        match var {
                            Expr::Symbol(name) => names.push(name.clone()),
                            _ => {
                                return Err(Error::RuntimeError(
                                    "fn takes vector of symbols".into(),
                                ))
                            }
                        }
                    }

                    return Ok(Expr::Lambda(
                        names,
                        args[1..].to_vec(),
                        Rc::new(RefCell::new(env.clone())),
                    ));
                }
                _ => return Err(Error::RuntimeError("fn takes vector as variable".into())),
            }
        } else {
            return Err(Error::RuntimeError("fn requires binding".into()));
        }
    }

    fn evaluate_less_than(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() >= 1 {
            let mut current = self.evaluate(args[0].clone(), env)?;
            for arg in args[1..].iter() {
                let value = self.evaluate(arg.clone(), env)?;
                let ok = match (current, value.clone()) {
                    (Expr::String(a), Expr::String(b)) => a < b,
                    (Expr::Int(a), Expr::Int(b)) => a < b,
                    (Expr::Int(a), Expr::Float(b)) => (a as f64) < b,
                    (Expr::Float(a), Expr::Int(b)) => a < (b as f64),
                    (Expr::Float(a), Expr::Float(b)) => a < b,
                    _ => {
                        return Err(Error::RuntimeError(
                            "types not supported for comparison".into(),
                        ))
                    }
                };
                if !ok {
                    return Ok(Expr::Bool(false));
                } else {
                    current = value;
                }
            }
            Ok(Expr::Bool(true))
        } else {
            Err(Error::RuntimeError("< takes at least 1 argument".into()))
        }
    }

    fn evaluate_greater_than(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() >= 1 {
            let mut current = self.evaluate(args[0].clone(), env)?;
            for arg in args[1..].iter() {
                let value = self.evaluate(arg.clone(), env)?;
                let ok = match (current, value.clone()) {
                    (Expr::String(a), Expr::String(b)) => a > b,
                    (Expr::Int(a), Expr::Int(b)) => a > b,
                    (Expr::Int(a), Expr::Float(b)) => (a as f64) > b,
                    (Expr::Float(a), Expr::Int(b)) => a > (b as f64),
                    (Expr::Float(a), Expr::Float(b)) => a > b,
                    _ => {
                        return Err(Error::RuntimeError(
                            "types not supported for comparison".into(),
                        ))
                    }
                };
                if !ok {
                    return Ok(Expr::Bool(false));
                } else {
                    current = value;
                }
            }
            Ok(Expr::Bool(true))
        } else {
            Err(Error::RuntimeError("> takes at least 1 argument".into()))
        }
    }

    fn evaluate_greater_than_or_eq(
        &self,
        args: Vec<Expr>,
        env: &mut Environment,
    ) -> Result<Expr, Error> {
        if args.len() >= 1 {
            let mut current = self.evaluate(args[0].clone(), env)?;
            for arg in args[1..].iter() {
                let value = self.evaluate(arg.clone(), env)?;
                let ok = match (current, value.clone()) {
                    (Expr::String(a), Expr::String(b)) => a >= b,
                    (Expr::Int(a), Expr::Int(b)) => a >= b,
                    (Expr::Int(a), Expr::Float(b)) => (a as f64) >= b,
                    (Expr::Float(a), Expr::Int(b)) => a >= (b as f64),
                    (Expr::Float(a), Expr::Float(b)) => a >= b,
                    _ => {
                        return Err(Error::RuntimeError(
                            "types not supported for comparison".into(),
                        ))
                    }
                };
                if !ok {
                    return Ok(Expr::Bool(false));
                } else {
                    current = value;
                }
            }
            Ok(Expr::Bool(true))
        } else {
            Err(Error::RuntimeError(">= takes at least 1 argument".into()))
        }
    }

    fn evaluate_less_than_or_eq(
        &self,
        args: Vec<Expr>,
        env: &mut Environment,
    ) -> Result<Expr, Error> {
        if args.len() >= 1 {
            let mut current = self.evaluate(args[0].clone(), env)?;
            for arg in args[1..].iter() {
                let value = self.evaluate(arg.clone(), env)?;
                let ok = match (current, value.clone()) {
                    (Expr::String(a), Expr::String(b)) => a <= b,
                    (Expr::Int(a), Expr::Int(b)) => a <= b,
                    (Expr::Int(a), Expr::Float(b)) => a as f64 <= b,
                    (Expr::Float(a), Expr::Int(b)) => a <= b as f64,
                    (Expr::Float(a), Expr::Float(b)) => a <= b,
                    _ => {
                        return Err(Error::RuntimeError(
                            "types not supported for comparison".into(),
                        ))
                    }
                };
                if !ok {
                    return Ok(Expr::Bool(false));
                } else {
                    current = value;
                }
            }
            Ok(Expr::Bool(true))
        } else {
            Err(Error::RuntimeError("<= takes at least 1 argument".into()))
        }
    }

    fn evaluate_add(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        let mut s = Expr::Int(0);
        for arg in args.iter() {
            let v = self.evaluate(arg.clone(), env)?;
            s = self.evaluate_add_aux(s, v)?;
        }
        Ok(s)
    }

    fn evaluate_add_aux(&self, a: Expr, b: Expr) -> Result<Expr, Error> {
        match (a.clone(), b.clone()) {
            (Expr::Int(i), Expr::Int(j)) => Ok(Expr::Int(i + j)),
            (Expr::Int(i), Expr::Float(j)) => Ok(Expr::Float(i as f64 + j)),
            (Expr::Float(i), Expr::Int(j)) => Ok(Expr::Float(i + j as f64)),
            (Expr::Float(i), Expr::Float(j)) => Ok(Expr::Float(i + j)),
            _ => Err(Error::RuntimeError(format!(
                "unsupported addition: {:?} + {:?}",
                a, b
            ))),
        }
    }

    fn evaluate_sub(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() >= 1 {
            let mut s = self.evaluate(args[0].clone(), env)?;
            for arg in args[1..].iter() {
                let v = self.evaluate(arg.clone(), env)?;
                s = self.evaluate_sub_aux(s, v)?;
            }
            Ok(s)
        } else {
            Err(Error::RuntimeError("- requires at least 1 argument".into()))
        }
    }

    fn evaluate_sub_aux(&self, a: Expr, b: Expr) -> Result<Expr, Error> {
        match (a.clone(), b.clone()) {
            (Expr::Int(i), Expr::Int(j)) => Ok(Expr::Int(i - j)),
            (Expr::Int(i), Expr::Float(j)) => Ok(Expr::Float(i as f64 - j)),
            (Expr::Float(i), Expr::Int(j)) => Ok(Expr::Float(i - j as f64)),
            (Expr::Float(i), Expr::Float(j)) => Ok(Expr::Float(i - j)),
            _ => Err(Error::RuntimeError(format!(
                "unsupported sub: {:?} - {:?}",
                a, b
            ))),
        }
    }

    fn evaluate_mult(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        let mut s = Expr::Int(1);
        for arg in args.iter() {
            let v = self.evaluate(arg.clone(), env)?;
            s = self.evaluate_mult_aux(s, v)?;
        }
        Ok(s)
    }

    fn evaluate_mult_aux(&self, a: Expr, b: Expr) -> Result<Expr, Error> {
        match (a.clone(), b.clone()) {
            (Expr::Int(i), Expr::Int(j)) => Ok(Expr::Int(i * j)),
            (Expr::Int(i), Expr::Float(j)) => Ok(Expr::Float(i as f64 * j)),
            (Expr::Float(i), Expr::Int(j)) => Ok(Expr::Float(i * j as f64)),
            (Expr::Float(i), Expr::Float(j)) => Ok(Expr::Float(i * j)),
            _ => Err(Error::RuntimeError(format!(
                "unsupported mult: {:?} * {:?}",
                a, b
            ))),
        }
    }

    fn evaluate_div(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() >= 1 {
            let mut s = self.evaluate(args[0].clone(), env)?;
            for arg in args[1..].iter() {
                let v = self.evaluate(arg.clone(), env)?;
                s = self.evaluate_div_aux(s, v)?;
            }
            Ok(s)
        } else {
            Err(Error::RuntimeError("- requires at least 1 argument".into()))
        }
    }

    fn evaluate_div_aux(&self, a: Expr, b: Expr) -> Result<Expr, Error> {
        match (a.clone(), b.clone()) {
            (Expr::Int(i), Expr::Int(j)) => Ok(Expr::Int(i / j)),
            (Expr::Int(i), Expr::Float(j)) => Ok(Expr::Float(i as f64 / j)),
            (Expr::Float(i), Expr::Int(j)) => Ok(Expr::Float(i / j as f64)),
            (Expr::Float(i), Expr::Float(j)) => Ok(Expr::Float(i / j)),
            _ => Err(Error::RuntimeError(format!(
                "unsupported div: {:?} / {:?}",
                a, b
            ))),
        }
    }

    fn evaluate_eq(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() >= 2 {
            let first = self.evaluate(args[0].clone(), env)?;
            for arg in args[1..].iter() {
                if first != self.evaluate(arg.clone(), env)? {
                    return Ok(Expr::Bool(false));
                }
            }
            Ok(Expr::Bool(true))
        } else {
            Err(Error::RuntimeError("= requires at least 2 argument".into()))
        }
    }

    fn evaluate_and(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        for arg in args.iter() {
            let value = self.evaluate(arg.clone(), env)?;
            match value {
                Expr::Bool(b) => {
                    if !b {
                        return Ok(Expr::Bool(false));
                    }
                }
                _ => return Err(Error::RuntimeError("and only takes booleans".into())),
            }
        }
        Ok(Expr::Bool(true))
    }

    fn evaluate_or(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        for arg in args.iter() {
            let value = self.evaluate(arg.clone(), env)?;
            match value {
                Expr::Bool(b) => {
                    if b {
                        return Ok(Expr::Bool(true));
                    }
                }
                _ => return Err(Error::RuntimeError("and only takes booleans".into())),
            }
        }
        Ok(Expr::Bool(false))
    }

    fn evaluate_not(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let value = self.evaluate(args[0].clone(), env)?;
            match value {
                Expr::Bool(b) => Ok(Expr::Bool(!b)),
                _ => Err(Error::RuntimeError("not only takes boolean value".into())),
            }
        } else {
            Err(Error::RuntimeError("not only takes 1 argument".into()))
        }
    }

    fn evaluate_first(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let head = args[0].clone();
            let arg = self.evaluate(head, env)?;
            match arg {
                Expr::Vector(elems) => {
                    if elems.len() > 0 {
                        return Ok(elems[0].clone());
                    }
                    return Ok(Expr::Nil);
                }
                Expr::List(elems) => {
                    if elems.len() > 0 {
                        return Ok(elems[0].clone());
                    }
                    return Ok(Expr::Nil);
                }
                _ => Err(Error::RuntimeError(format!(
                    "first can not be applied to {}",
                    arg
                ))),
            }
        } else {
            Err(Error::RuntimeError("required 1 argument for first".into()))
        }
    }

    fn evaluate_rest(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let head = args[0].clone();
            let arg = self.evaluate(head, env)?;
            match arg {
                Expr::Vector(elems) => {
                    let mut vec: Vec<Expr> = vec![];
                    if elems.len() > 0 {
                        vec = elems[1..].to_vec();
                    }
                    Ok(Expr::Vector(Rc::new(vec)))
                }
                Expr::List(elems) => {
                    let mut vec: Vec<Expr> = vec![];
                    if elems.len() > 0 {
                        vec = elems[1..].to_vec();
                    }
                    Ok(Expr::List(Rc::new(vec)))
                }
                _ => Err(Error::RuntimeError(format!(
                    "rest can not be applied to {}",
                    arg
                ))),
            }
        } else {
            Err(Error::RuntimeError("required 1 argument for rest".into()))
        }
    }

    fn evaluate_conj(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 0 {
            return Ok(Expr::List(Rc::new(vec![])));
        }
        let coll = self.evaluate(args[0].clone(), env)?;
        match coll {
            Expr::Vector(elems) => {
                let mut joined = elems.as_ref().clone();
                for arg in args[1..].iter() {
                    let value = self.evaluate(arg.clone(), env)?;
                    joined.push(value);
                }
                Ok(Expr::Vector(Rc::new(joined)))
            }
            Expr::List(elems) => {
                let mut joined = VecDeque::from(elems.as_ref().clone());
                for arg in args[1..].iter() {
                    let value = self.evaluate(arg.clone(), env)?;
                    joined.push_front(value);
                }
                Ok(Expr::List(Rc::new(Vec::from(joined))))
            }
            _ => Err(Error::RuntimeError(
                "conj only supports vectors and lists".into(),
            )),
        }
    }

    fn evaluate_print(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        let mut s = "".to_string();
        for arg in args.iter() {
            let value = self.evaluate(arg.clone(), env)?;
            s += value.to_string().as_str();
        }
        print!("{}", s);
        Ok(Expr::Nil)
    }

    fn evaluate_nth(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 2 {
            let coll = self.evaluate(args[0].clone(), env)?;
            let index = self.evaluate(args[1].clone(), env)?;
            match (coll, index) {
                (Expr::Vector(elems), Expr::Int(i)) => {
                    match elems.get(i as usize) {
                        Some(v) => return Ok(v.clone()),
                        None => panic!(),
                    };
                }
                (Expr::List(elems), Expr::Int(i)) => {
                    match elems.get(i as usize) {
                        Some(v) => return Ok(v.clone()),
                        None => panic!(),
                    };
                }
                _ => Err(Error::RuntimeError(
                    "nth does not support those types".into(),
                )),
            }
        } else if args.len() == 3 {
            let coll = self.evaluate(args[0].clone(), env)?;
            let index = self.evaluate(args[1].clone(), env)?;
            match (coll, index) {
                (Expr::Vector(elems), Expr::Int(i)) => match elems.get(i as usize) {
                    Some(v) => Ok(v.clone()),
                    None => Ok(self.evaluate(args[2].clone(), env)?),
                },
                (Expr::List(elems), Expr::Int(i)) => match elems.get(i as usize) {
                    Some(v) => Ok(v.clone()),
                    None => Ok(self.evaluate(args[2].clone(), env)?),
                },
                _ => Err(Error::RuntimeError(
                    "nth does not support those types".into(),
                )),
            }
        } else {
            Err(Error::RuntimeError(
                "required 2 or 3 argument for nth".into(),
            ))
        }
    }

    fn evaluate_count(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let value = self.evaluate(args[0].clone(), env)?;
            match value {
                Expr::Vector(elems) => Ok(Expr::Int(elems.len().try_into().unwrap())),
                Expr::Set(elems) => Ok(Expr::Int(elems.len().try_into().unwrap())),
                Expr::List(elems) => Ok(Expr::Int(elems.len().try_into().unwrap())),
                _ => Err(Error::RuntimeError("count only takes a sequence".into())),
            }
        } else {
            Err(Error::RuntimeError("required 1 argument for count".into()))
        }
    }

    fn evaluate_stringp(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let value = self.evaluate(args[0].clone(), env)?;
            Ok(match value {
                Expr::String(_) => Expr::Bool(true),
                _ => Expr::Bool(false),
            })
        } else {
            return Err(Error::RuntimeError(
                "required 1 argument for string?".into(),
            ));
        }
    }

    fn evaluate_intp(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let value = self.evaluate(args[0].clone(), env)?;
            Ok(match value {
                Expr::Int(_) => Expr::Bool(true),
                _ => Expr::Bool(false),
            })
        } else {
            return Err(Error::RuntimeError("required 1 argument for int?".into()));
        }
    }

    fn evaluate_floatp(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let value = self.evaluate(args[0].clone(), env)?;
            Ok(match value {
                Expr::Float(_) => Expr::Bool(true),
                _ => Expr::Bool(false),
            })
        } else {
            return Err(Error::RuntimeError("required 1 argument for float?".into()));
        }
    }

    fn evaluate_keywordp(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let value = self.evaluate(args[0].clone(), env)?;
            Ok(match value {
                Expr::Keyword(_) => Expr::Bool(true),
                _ => Expr::Bool(false),
            })
        } else {
            return Err(Error::RuntimeError(
                "required 1 argument for keyword?".into(),
            ));
        }
    }

    fn evaluate_symbolp(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let value = self.evaluate(args[0].clone(), env)?;
            Ok(match value {
                Expr::Symbol(_) => Expr::Bool(true),
                _ => Expr::Bool(false),
            })
        } else {
            return Err(Error::RuntimeError(
                "required 1 argument for symbol?".into(),
            ));
        }
    }

    fn evaluate_listp(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let value = self.evaluate(args[0].clone(), env)?;
            Ok(match value {
                Expr::List(_) => Expr::Bool(true),
                _ => Expr::Bool(false),
            })
        } else {
            return Err(Error::RuntimeError("required 1 argument for list?".into()));
        }
    }

    fn evaluate_vectorp(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        if args.len() == 1 {
            let value = self.evaluate(args[0].clone(), env)?;
            Ok(match value {
                Expr::Vector(_) => Expr::Bool(true),
                _ => Expr::Bool(false),
            })
        } else {
            return Err(Error::RuntimeError(
                "required 1 argument for vector?".into(),
            ));
        }
    }

    fn evaluate_list_fn(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        let mut elems: Vec<Expr> = vec![];
        for arg in args.iter() {
            elems.push(self.evaluate(arg.clone(), env)?);
        }
        Ok(Expr::List(Rc::new(elems)))
    }

    fn evaluate_vector_fn(&self, args: Vec<Expr>, env: &mut Environment) -> Result<Expr, Error> {
        let mut elems: Vec<Expr> = vec![];
        for arg in args.iter() {
            elems.push(self.evaluate(arg.clone(), env)?);
        }
        Ok(Expr::Vector(Rc::new(elems)))
    }
}

struct LexerTestCase {
    input: String,
    expected: Vec<Token>,
    want_err: bool,
}

impl LexerTestCase {
    fn new(input: &str, expected: Vec<Token>, want_err: bool) -> Self {
        LexerTestCase {
            input: input.into(),
            expected,
            want_err,
        }
    }

    fn run(&self) -> Result<Vec<Token>, String> {
        let mut got: Vec<Token> = vec![];
        let mut lexer = Lexer::new(self.input.as_str());
        loop {
            let result = lexer.next();
            if result.is_err() {
                if self.want_err {
                    return Ok(got);
                }
                return Err(format!("{:?}", result.err()));
            }
            if self.want_err && result.is_ok() {
                return Err(format!("{:?}", result.ok()));
            }
            let token = result.unwrap();
            got.push(token.clone());
            if token == Token::EOF {
                break;
            }
        }

        if self.expected.len() != got.len() {
            panic!(
                "length mismatch: {:?} != {:?}, got: {:?}, expected: {:?}, input: {:?}",
                got.len(),
                self.expected.len(),
                got,
                self.expected,
                self.input,
            );
        }

        for (_, (t, g)) in self.expected.iter().zip(got.iter()).enumerate() {
            if t != g {
                panic!("{:?} != {:?}", g, t);
            }
        }
        Ok(got)
    }
}

struct ParserTestCase {
    input: Vec<Token>,
    expected: Expr,
    want_err: bool,
}

impl ParserTestCase {
    fn new(input: &str, expected: Expr, want_err: bool) -> Self {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().unwrap();
        ParserTestCase {
            input: tokens,
            expected,
            want_err,
        }
    }

    fn run(&self) -> Result<Expr, String> {
        let mut parser = Parser::new(self.input.clone());
        let result = parser.parse();
        if result.is_err() {
            if self.want_err {
                return Ok(Expr::Nil);
            }
            return Err(format!("{:?}", result.err()));
        }
        if self.want_err && result.is_ok() {
            return Err(format!("{:?}", result.ok()));
        }
        let got = result.unwrap();

        if got != self.expected {
            panic!("{:?} != {:?}", got, self.expected);
        }
        Ok(got)
    }
}

fn lexer_test() {
    let testcases: Vec<LexerTestCase> = vec![
        LexerTestCase::new(
            "(abc def ghi 0 123 45.6 :abc)",
            vec![
                Token::LParen,
                Token::Symbol("abc".into()),
                Token::Symbol("def".into()),
                Token::Symbol("ghi".into()),
                Token::Int(0),
                Token::Int(123),
                Token::Float(45.6),
                Token::Keyword("abc".into()),
                Token::RParen,
                Token::EOF,
            ],
            false,
        ),
        LexerTestCase::new("", vec![Token::EOF], false),
        LexerTestCase::new("abc", vec![Token::Symbol("abc".into()), Token::EOF], false),
        LexerTestCase::new("123", vec![Token::Int(123), Token::EOF], false),
        LexerTestCase::new("-123", vec![Token::Int(-123), Token::EOF], false),
        LexerTestCase::new(
            "-abc",
            vec![Token::Symbol("-abc".into()), Token::EOF],
            false,
        ),
        LexerTestCase::new(
            "[-abc -a1]",
            vec![
                Token::LBracket,
                Token::Symbol("-abc".into()),
                Token::Symbol("-a1".into()),
                Token::RBracket,
                Token::EOF,
            ],
            false,
        ),
        LexerTestCase::new(":0", vec![], true),
        LexerTestCase::new("*", vec![Token::Symbol("*".into()), Token::EOF], false),
        LexerTestCase::new(
            "*abc*",
            vec![Token::Symbol("*abc*".into()), Token::EOF],
            false,
        ),
        LexerTestCase::new(
            "abc123",
            vec![Token::Symbol("abc123".into()), Token::EOF],
            false,
        ),
        LexerTestCase::new(
            "(#{})",
            vec![
                Token::LParen,
                Token::LSharpBrace,
                Token::RBrace,
                Token::RParen,
                Token::EOF,
            ],
            false,
        ),
        LexerTestCase::new(
            "(fn [x] (+ x 1))",
            vec![
                Token::LParen,
                Token::Symbol("fn".into()),
                Token::LBracket,
                Token::Symbol("x".into()),
                Token::RBracket,
                Token::LParen,
                Token::Symbol("+".into()),
                Token::Symbol("x".into()),
                Token::Int(1),
                Token::RParen,
                Token::RParen,
                Token::EOF,
            ],
            false,
        ),
        LexerTestCase::new(
            r###""hello, world""###,
            vec![Token::String("hello, world".into()), Token::EOF],
            false,
        ),
        LexerTestCase::new(r###""hello, world"###, vec![], true),
    ];

    for testcase in testcases {
        let result = testcase.run();
        if result.is_err() {
            println!("{:?}", result)
        }
    }
}

fn parser_test() {
    let testcases: Vec<ParserTestCase> = vec![
        ParserTestCase::new("-12", Expr::Int(-12), false),
        ParserTestCase::new(
            "(abc def ghi 0 123 45.6 :abc)",
            Expr::List(Rc::new(vec![
                Expr::Symbol("abc".into()),
                Expr::Symbol("def".into()),
                Expr::Symbol("ghi".into()),
                Expr::Int(0),
                Expr::Int(123),
                Expr::Float(45.6),
                Expr::Keyword("abc".into()),
            ])),
            false,
        ),
        ParserTestCase::new(
            "(())",
            Expr::List(Rc::new(vec![Expr::List(Rc::new(vec![]))])),
            false,
        ),
        ParserTestCase::new("abc", Expr::Symbol("abc".into()), false),
        ParserTestCase::new("123", Expr::Int(123), false),
        ParserTestCase::new("*", Expr::Symbol("*".into()), false),
        ParserTestCase::new("*abc*", Expr::Symbol("*abc*".into()), false),
        ParserTestCase::new(
            "(a)",
            Expr::List(Rc::new(vec![Expr::Symbol("a".into())])),
            false,
        ),
        ParserTestCase::new(
            "(fn [x] (+ x 1))",
            Expr::List(Rc::new(vec![
                Expr::Symbol("fn".into()),
                Expr::Vector(Rc::new(vec![Expr::Symbol("x".into())])),
                Expr::List(Rc::new(vec![
                    Expr::Symbol("+".into()),
                    Expr::Symbol("x".into()),
                    Expr::Int(1),
                ])),
            ])),
            false,
        ),
        ParserTestCase::new("#{}", Expr::Set(Rc::new(vec![])), false),
        ParserTestCase::new(
            "#{a}",
            Expr::Set(Rc::new(vec![Expr::Symbol("a".into())])),
            false,
        ),
        ParserTestCase::new(
            "(#{})",
            Expr::List(Rc::new(vec![Expr::Set(Rc::new(vec![]))])),
            false,
        ),
        ParserTestCase::new(
            "'a",
            Expr::List(Rc::new(vec![
                Expr::Symbol("quote".into()),
                Expr::Symbol("a".into()),
            ])),
            false,
        ),
        ParserTestCase::new(
            "'(1 2)",
            Expr::List(Rc::new(vec![
                Expr::Symbol("quote".into()),
                Expr::List(Rc::new(vec![Expr::Int(1), Expr::Int(2)])),
            ])),
            false,
        ),
    ];

    for testcase in testcases {
        let result = testcase.run();
        if result.is_err() {
            println!("{:?}", result)
        }
    }
}

fn environment_test() {
    let mut a = Environment::new();
    a.set("abc", &Expr::Float(1.0));
    let got = a.get("abc").expect("failed to get abc");
    if got != Expr::Float(1.0) {
        println!("got: {:?}, expected: {:?}", got, Expr::Float(1.0))
    }

    let mut p = Environment::new();
    p.set("xyz", &Expr::Float(2.0));
    a.extend(p);
    let got = a.get("xyz").expect("failed to get parent");
    if got != Expr::Float(2.0) {
        println!("got: {:?}, expected: {:?}", got, Expr::Float(2.0));
    }

    a.set("xyz", &Expr::Bool(true));
    let got = a.get("xyz").expect("failed to get xyz");
    if got != Expr::Bool(true) {
        println!("got: {:?}, expected: {:?}", got, Expr::Bool(true));
    }
    a.set("xyz", &Expr::Bool(false));
    let got = a.get("xyz").expect("failed to get xyz");
    if got != Expr::Bool(false) {
        println!("got: {:?}, expected: {:?}", got, Expr::Bool(false));
    }
}

struct EvaluatorTestCase {
    raw_input: String,
    input: Expr,
    environment: Environment,
    expected: Expr,
    want_err: bool,
}

impl EvaluatorTestCase {
    fn new(input: &str, environment: Environment, expected: Expr, want_err: bool) -> Self {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().unwrap();
        let mut parser = Parser::new(tokens);
        let val = parser.parse().unwrap();

        EvaluatorTestCase {
            raw_input: input.to_string(),
            input: val,
            environment: environment,
            expected,
            want_err,
        }
    }

    fn run(&self) -> Result<Expr, String> {
        let evaluator = Evaluator::new();
        let result = evaluator.evaluate(self.input.clone(), &mut self.environment.clone());
        if result.is_err() {
            if self.want_err {
                return Ok(Expr::Nil);
            }
            return Err(format!("{:?}", result.err().unwrap()));
        }
        if self.want_err && result.is_ok() {
            return Err(format!("{:?}", result.ok()));
        }
        let got = result.unwrap();

        if got != self.expected {
            panic!(
                "input: {} => got: {:?}, expected: {:?}",
                self.raw_input, got, self.expected
            );
        }
        Ok(got)
    }
}

fn evaluator_test() {
    let mut env = Environment::new();
    env.set("hello", &Expr::Float(2.0));

    let testcases: Vec<EvaluatorTestCase> = vec![
        EvaluatorTestCase::new("1", Environment::new(), Expr::Int(1), false),
        EvaluatorTestCase::new("1.0", Environment::new(), Expr::Float(1.0), false),
        EvaluatorTestCase::new("-1.0", Environment::new(), Expr::Float(-1.0), false),
        EvaluatorTestCase::new("-123", Environment::new(), Expr::Int(-123), false),
        EvaluatorTestCase::new("hello", env, Expr::Float(2.0), false),
        EvaluatorTestCase::new(
            "[]",
            Environment::new(),
            Expr::Vector(Rc::new(vec![])),
            false,
        ),
        EvaluatorTestCase::new(
            "[32 48]",
            Environment::new(),
            Expr::Vector(Rc::new(vec![Expr::Int(32), Expr::Int(48)])),
            false,
        ),
        EvaluatorTestCase::new("(first [32 48])", Environment::new(), Expr::Int(32), false),
        EvaluatorTestCase::new(
            "(rest [])",
            Environment::new(),
            Expr::Vector(Rc::new(vec![])),
            false,
        ),
        EvaluatorTestCase::new(
            "(rest [1])",
            Environment::new(),
            Expr::Vector(Rc::new(vec![])),
            false,
        ),
        EvaluatorTestCase::new(
            "(rest [32 48 59])",
            Environment::new(),
            Expr::Vector(Rc::new(vec![Expr::Int(48), Expr::Int(59)])),
            false,
        ),
        EvaluatorTestCase::new("(if true 32 48)", Environment::new(), Expr::Int(32), false),
        EvaluatorTestCase::new("(if false 32 48)", Environment::new(), Expr::Int(48), false),
        EvaluatorTestCase::new("(do false 32 48)", Environment::new(), Expr::Int(48), false),
        EvaluatorTestCase::new("(+ 0 32 48)", Environment::new(), Expr::Int(80), false),
        EvaluatorTestCase::new("(* 2 32 48)", Environment::new(), Expr::Int(3072), false),
        EvaluatorTestCase::new("(/ 1 2)", Environment::new(), Expr::Int(0), false),
        EvaluatorTestCase::new("(/ 1.0 2)", Environment::new(), Expr::Float(0.5), false),
        // EvaluatorTestCase::new("(print 1 2 3)", Environment::new(), Expr::Nil, false),
        // EvaluatorTestCase::new("(print \"hello\")", Environment::new(), Expr::Nil, false),
        EvaluatorTestCase::new("(quote 3)", Environment::new(), Expr::Int(3), false),
        EvaluatorTestCase::new(
            "(quote [1 2 3 x])",
            Environment::new(),
            Expr::Vector(Rc::new(vec![
                Expr::Int(1),
                Expr::Int(2),
                Expr::Int(3),
                Expr::Symbol("x".into()),
            ])),
            false,
        ),
        EvaluatorTestCase::new("(string? 3)", Environment::new(), Expr::Bool(false), false),
        EvaluatorTestCase::new("(float? 3)", Environment::new(), Expr::Bool(false), false),
        EvaluatorTestCase::new("(int? 3)", Environment::new(), Expr::Bool(true), false),
        EvaluatorTestCase::new("(float? 3.0)", Environment::new(), Expr::Bool(true), false),
        EvaluatorTestCase::new(
            "(float? (quote x))",
            Environment::new(),
            Expr::Bool(false),
            false,
        ),
        EvaluatorTestCase::new("(count [1 2 3])", Environment::new(), Expr::Int(3), false),
        EvaluatorTestCase::new("(let [x 3] x)", Environment::new(), Expr::Int(3), false),
        EvaluatorTestCase::new("(do (let [x 3] x) x)", Environment::new(), Expr::Nil, true),
        EvaluatorTestCase::new(
            "(do (let [x 1] (let [x 2] x)))",
            Environment::new(),
            Expr::Int(2),
            false,
        ),
        EvaluatorTestCase::new(
            "(let [add (fn [x] (+ x 1))] (add 3))",
            Environment::new(),
            Expr::Int(4),
            false,
        ),
        EvaluatorTestCase::new(
            "(let [x 1] ((fn [n] (+ n x)) 3))",
            Environment::new(),
            Expr::Int(4),
            false,
        ),
        EvaluatorTestCase::new(
            "(let [x 1]
               (let [add (fn [n] (+ n x))]
                 (let [x 10]
                   (add 5))))",
            Environment::new(),
            Expr::Int(6),
            false,
        ),
        EvaluatorTestCase::new(
            "(and true false)",
            Environment::new(),
            Expr::Bool(false),
            false,
        ),
        EvaluatorTestCase::new(
            "(and true true)",
            Environment::new(),
            Expr::Bool(true),
            false,
        ),
        EvaluatorTestCase::new(
            "(or true true)",
            Environment::new(),
            Expr::Bool(true),
            false,
        ),
        EvaluatorTestCase::new("(not true)", Environment::new(), Expr::Bool(false), false),
        EvaluatorTestCase::new("(not false)", Environment::new(), Expr::Bool(true), false),
        EvaluatorTestCase::new(
            "(let [add (fn [x] (+ x 1))]
               (add (add 4)))",
            Environment::new(),
            Expr::Int(6),
            false,
        ),
        EvaluatorTestCase::new(
            "(let [fib
               (fn [n]
                 (if (<= n 2)
                     1
                     (+ (fib (- n 1))
                        (fib (- n 2)))))]
               (fib 10))",
            Environment::new(),
            Expr::Int(55),
            false,
        ),
        EvaluatorTestCase::new("'a", Environment::new(), Expr::Symbol("a".into()), false),
        EvaluatorTestCase::new(
            "'(1 2)",
            Environment::new(),
            Expr::List(Rc::new(vec![Expr::Int(1), Expr::Int(2)])),
            false,
        ),
        EvaluatorTestCase::new("(= 1 2)", Environment::new(), Expr::Bool(false), false),
        EvaluatorTestCase::new("(= 2 2)", Environment::new(), Expr::Bool(true), false),
        EvaluatorTestCase::new(
            "(conj)",
            Environment::new(),
            Expr::List(Rc::new(vec![])),
            false,
        ),
        EvaluatorTestCase::new(
            "(conj [1 2] 3)",
            Environment::new(),
            Expr::Vector(Rc::new(vec![Expr::Int(1), Expr::Int(2), Expr::Int(3)])),
            false,
        ),
        EvaluatorTestCase::new(
            "(let [x 4] (conj [1 2] 3 x))",
            Environment::new(),
            Expr::Vector(Rc::new(vec![
                Expr::Int(1),
                Expr::Int(2),
                Expr::Int(3),
                Expr::Int(4),
            ])),
            false,
        ),
        EvaluatorTestCase::new(
            "(let [x 4] (conj '(1 2) 3 x))",
            Environment::new(),
            Expr::List(Rc::new(vec![
                Expr::Int(4),
                Expr::Int(3),
                Expr::Int(1),
                Expr::Int(2),
            ])),
            false,
        ),
        EvaluatorTestCase::new("(< 1 3 2 x)", Environment::new(), Expr::Bool(false), false),
        EvaluatorTestCase::new("(nth [1 2] 0)", Environment::new(), Expr::Int(1), false),
        EvaluatorTestCase::new(
            "(list)",
            Environment::new(),
            Expr::List(Rc::new(vec![])),
            false,
        ),
        EvaluatorTestCase::new(
            "(list 1 2)",
            Environment::new(),
            Expr::List(Rc::new(vec![Expr::Int(1), Expr::Int(2)])),
            false,
        ),
        EvaluatorTestCase::new(
            "(let [x (fn [] 3)] (x))",
            Environment::new(),
            Expr::Int(3),
            false,
        ),
        EvaluatorTestCase::new(
            "(do
               (def x 1)
               x)",
            Environment::new(),
            Expr::Int(1),
            false,
        ),
        EvaluatorTestCase::new(
            "(do
               (def x 1)
               (let [x 3] x))",
            Environment::new(),
            Expr::Int(3),
            false,
        ),
        EvaluatorTestCase::new(
            "(do
               (def x 1)
               (let [x 3] x)
               x)",
            Environment::new(),
            Expr::Int(1),
            false,
        ),
        EvaluatorTestCase::new(
            "(do
              (def fib
                (fn [n]
                  (if (<= n 2)
                      1
                      (+ (fib (- n 1))
                         (fib (- n 2))))))
              (fib 10))",
            Environment::new(),
            Expr::Int(55),
            false,
        ),
        EvaluatorTestCase::new(
            "(= '(1 2 3) '(1 2))",
            Environment::new(),
            Expr::Bool(false),
            false,
        ),
        EvaluatorTestCase::new(
            "(= '(abc :def 1) '(abc :def 1))",
            Environment::new(),
            Expr::Bool(true),
            false,
        ),
    ];

    for testcase in testcases {
        let result = testcase.run();
        if result.is_err() {
            println!("{:?}", result)
        }
    }
}

fn unescape(s: &str) -> String {
    s.replace("\\n", "\n")
        .replace("\\r", "\r")
        .replace("\\t", "\t")
        .replace("\\\\", "\\")
        .replace("\\'", "\'")
}
