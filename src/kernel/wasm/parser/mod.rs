pub mod error;
pub mod primitives;
pub mod types;
pub mod instructions;
pub mod modules;

/// Parser configuration
/// 
/// Contains configuration options for the WebAssembly parser
#[derive(Debug, Clone)]
pub struct ParserConfig {
    /// Whether to enable debug logging during parsing
    pub debug: bool,
}

impl Default for ParserConfig {
    fn default() -> Self {
        Self {
            debug: false,
        }
    }
}

impl ParserConfig {
    /// Creates a new parser config with debug logging enabled
    pub fn debug() -> Self {
        Self {
            debug: true,
        }
    }

    /// Creates a new parser config with debug logging disabled
    pub fn release() -> Self {
        Self {
            debug: false,
        }
    }
}

/// Debug logging helper function for parser
/// 
/// Only prints debug messages when the debug flag is enabled in the parser config
pub fn debug_log(config: &ParserConfig, message: &str) {
    if config.debug {
        println!("[PARSER DEBUG] {}", message);
    }
}

/// Debug logging macro for parser
/// 
/// Only prints debug messages when the debug flag is enabled in the parser config
#[macro_export]
macro_rules! parser_debug_log {
    ($config:expr, $($arg:tt)*) => {
        if $config.debug {
            println!("[PARSER DEBUG] {}", format!($($arg)*));
        }
    };
}

#[derive(Debug)]
pub struct Parser<'a> {
    /// The input byte slice
    pub input: &'a [u8],
    /// The current position in the input
    pub cursor: usize,
    /// Parser configuration
    pub config: ParserConfig,
}

impl<'a> Parser<'a> {
    /// Creates a new parser for the given input with default configuration
    pub const fn new(input: &'a [u8]) -> Self {
        Self {
            input,
            cursor: 0,
            config: ParserConfig { debug: false },
        }
    }

    /// Creates a new parser for the given input with custom configuration
    pub const fn with_config(input: &'a [u8], config: ParserConfig) -> Self {
        Self {
            input,
            cursor: 0,
            config,
        }
    }

    /// Creates a new parser for the given input with debug logging enabled
    pub const fn debug(input: &'a [u8]) -> Self {
        Self {
            input,
            cursor: 0,
            config: ParserConfig { debug: true },
        }
    }
} 