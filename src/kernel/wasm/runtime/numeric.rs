use core::fmt;
use core::convert::TryFrom;
use alloc::vec::Vec;

/// Bit width for numeric operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitWidth {
    /// 32-bit operations
    W32,
    /// 64-bit operations
    W64,
}

impl BitWidth {
    /// Returns the number of bits
    pub const fn bits(&self) -> u32 {
        match self {
            Self::W32 => 32,
            Self::W64 => 64,
        }
    }

    /// Returns the maximum unsigned value
    pub const fn max_unsigned(&self) -> u64 {
        match self {
            Self::W32 => u32::MAX as u64,
            Self::W64 => u64::MAX,
        }
    }

    /// Returns the maximum signed value
    pub const fn max_signed(&self) -> i64 {
        match self {
            Self::W32 => i32::MAX as i64,
            Self::W64 => i64::MAX,
        }
    }

    /// Returns the minimum signed value
    pub const fn min_signed(&self) -> i64 {
        match self {
            Self::W32 => i32::MIN as i64,
            Self::W64 => i64::MIN,
        }
    }

    /// Returns the type name as a string
    pub fn type_name(&self) -> &'static str {
        match self {
            Self::W32 => "i32",
            Self::W64 => "i64",
        }
    }
}

/// Errors that can occur during numeric operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericError {
    /// Division by zero
    DivisionByZero,
    /// Integer overflow
    Overflow,
    /// Integer underflow
    Underflow,
    /// Invalid operation (e.g., -2^N-1 / -1 for signed division)
    InvalidOperation,
}

/// Result type for numeric operations
pub enum NumericResult<T> {
    /// Successful operation with a value
    Ok(T),
    /// Operation failed with an error
    Err(NumericError),
}

impl<T> NumericResult<T> {
    /// Returns true if the result is Ok
    pub const fn is_ok(&self) -> bool {
        matches!(self, Self::Ok(_))
    }

    /// Returns true if the result is Err
    pub const fn is_err(&self) -> bool {
        matches!(self, Self::Err(_))
    }

    /// Unwraps the result, panicking if it is Err
    pub fn unwrap(self) -> T {
        match self {
            Self::Ok(value) => value,
            Self::Err(err) => panic!("called `NumericResult::unwrap()` on an `Err` value: {:?}", err),
        }
    }

    /// Unwraps the result, returning the default value if it is Err
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Self::Ok(value) => value,
            Self::Err(_) => default,
        }
    }
}

/// Trait for numeric operations that can return multiple values
pub trait NumericOps<T> {
    /// Square root operation
    fn sqrt(self) -> NumericResult<T>;
    /// Division operation
    fn div(self, other: T) -> NumericResult<T>;
    /// Remainder operation
    fn rem(self, other: T) -> NumericResult<T>;
    /// Truncate operation
    fn trunc(self) -> NumericResult<T>;
}

/// Trait for floating point operations
pub trait FloatOps: Sized {
    /// The bit width of the type
    const WIDTH: BitWidth;

    /// Addition
    fn add(self, other: Self) -> Self;

    /// Subtraction
    fn sub(self, other: Self) -> Self;

    /// Multiplication
    fn mul(self, other: Self) -> NumericResult<Self>;

    /// Division
    fn div(self, other: Self) -> NumericResult<Self>;

    /// Square root
    fn sqrt(self) -> Self;

    /// Minimum
    fn min(self, other: Self) -> Self;

    /// Maximum
    fn max(self, other: Self) -> Self;

    /// Ceiling
    fn ceil(self) -> Self;

    /// Floor
    fn floor(self) -> Self;

    /// Truncate
    fn trunc(self) -> Self;

    /// Round to nearest
    fn nearest(self) -> Self;

    /// Absolute value
    fn abs(self) -> Self;

    /// Negation
    fn neg(self) -> Self;

    /// Copy sign
    fn copysign(self, other: Self) -> Self;

    /// Equal
    fn eq(self, other: Self) -> bool;

    /// Not equal
    fn ne(self, other: Self) -> bool;

    /// Less than
    fn lt(self, other: Self) -> bool;

    /// Less than or equal
    fn le(self, other: Self) -> bool;

    /// Greater than
    fn gt(self, other: Self) -> bool;

    /// Greater than or equal
    fn ge(self, other: Self) -> bool;

    /// Remainder
    fn rem(self, other: Self) -> Self;

    /// Unsigned truncation
    /// 
    /// Truncates a floating-point value to an unsigned integer.
    /// Returns None if:
    /// - The input is NaN
    /// - The input is infinity
    /// - The truncated value is out of range (negative or >= 2^N)
    /// truncu_M,N(z) = trunc(z) if -1 < trunc(z) < 2^N, undefined otherwise
    fn trunc_u<M: IntOps + From<u64>>(self) -> Option<M>;

    /// Signed truncation
    /// 
    /// Truncates a floating-point value to a signed integer.
    /// Returns None if:
    /// - The input is NaN
    /// - The input is infinity
    /// - The truncated value is out of range (-2^(N-1) - 1 < trunc(z) < 2^(N-1))
    /// truncs_M,N(z) = trunc(z) if -2^(N-1) - 1 < trunc(z) < 2^(N-1), undefined otherwise
    fn trunc_s<M: IntOps + From<i64>>(self) -> Option<M>;

    /// Unsigned saturating truncation
    /// 
    /// Truncates a floating-point value to an unsigned integer with saturation.
    /// - Returns 0 for NaN or negative infinity
    /// - Returns 2^N - 1 for positive infinity
    /// - Otherwise returns sat_u_N(trunc(z))
    /// trunc_sat_u_M,N(z) = sat_u_N(trunc(z)) with special cases for NaN and infinity
    fn trunc_sat_u<M: IntOps + From<u64>>(self) -> M;

    /// Signed saturating truncation
    /// 
    /// Truncates a floating-point value to a signed integer with saturation.
    /// - Returns 0 for NaN
    /// - Returns -2^(N-1) for negative infinity
    /// - Returns 2^(N-1) - 1 for positive infinity
    /// - Otherwise returns sat_s_N(trunc(z))
    /// trunc_sat_s_M,N(z) = sat_s_N(trunc(z)) with special cases for NaN and infinity
    fn trunc_sat_s<M: IntOps + From<i64>>(self) -> M;

    /// Promotes a floating-point value from size M to size N
    /// 
    /// - If z is a canonical NaN, returns a canonical NaN of size N
    /// - If z is a NaN, returns an arithmetic NaN of size N
    /// - Otherwise, returns z
    /// promote_M,N(z) = nans_N{} if z is canonical NaN
    /// promote_M,N(z) = nans_N{+nan(1)} if z is NaN
    /// promote_M,N(z) = z otherwise
    fn promote<M: FloatOps + From<f32> + From<f64>>(self) -> M;

    /// Demotes a floating-point value from size M to size N
    /// 
    /// - If z is a canonical NaN, returns a canonical NaN of size N
    /// - If z is a NaN, returns an arithmetic NaN of size N
    /// - If z is an infinity, returns that infinity
    /// - If z is a zero, returns that zero
    /// - Otherwise, returns float_N(z)
    /// demote_M,N(z) = nans_N{} if z is canonical NaN
    /// demote_M,N(z) = nans_N{+nan(1)} if z is NaN
    /// demote_M,N(±∞) = ±∞
    /// demote_M,N(±0) = ±0
    /// demote_M,N(±q) = float_N(±q)
    fn demote<M: FloatOps + From<f32> + From<f64>>(self) -> M;

    /// Reinterprets the bits of a value as another type
    /// 
    /// Takes the bit sequence of the input value and reinterprets it as the target type.
    /// reinterpret_t1,t2(c) = bits^-1_t2(bits_t1(c))
    fn reinterpret<M: FloatOps + From<f32> + From<f64>>(self) -> M;
}

/// Unsigned integer operations
pub trait UnsignedOps {
    /// The bit width of the type
    const WIDTH: BitWidth;

    /// Unsigned addition
    fn uadd(self, other: Self) -> Self;

    /// Unsigned subtraction
    fn usub(self, other: Self) -> NumericResult<Self>
    where
        Self: Sized;

    /// Unsigned multiplication
    fn umul(self, other: Self) -> Self;

    /// Unsigned division
    fn udiv(self, other: Self) -> NumericResult<Self>
    where
        Self: Sized;

    /// Unsigned remainder
    fn urem(self, other: Self) -> NumericResult<Self>
    where
        Self: Sized;

    /// Unsigned less than
    fn ult(self, other: Self) -> bool;

    /// Unsigned less than or equal
    fn ule(self, other: Self) -> bool;

    /// Unsigned greater than
    fn ugt(self, other: Self) -> bool;

    /// Unsigned greater than or equal
    fn uge(self, other: Self) -> bool;

    /// Unsigned minimum
    fn umin(self, other: Self) -> Self;

    /// Unsigned maximum
    fn umax(self, other: Self) -> Self;

    /// Unsigned saturation
    fn saturate(self) -> Self;
}

/// Signed integer operations
pub trait SignedOps {
    /// The bit width of the type
    const WIDTH: BitWidth;

    /// Signed addition
    fn sadd(self, other: Self) -> Self;

    /// Signed subtraction
    fn ssub(self, other: Self) -> Self;

    /// Signed multiplication
    fn smul(self, other: Self) -> Self;

    /// Signed division
    fn sdiv(self, other: Self) -> NumericResult<Self>
    where
        Self: Sized;

    /// Signed remainder
    fn srem(self, other: Self) -> NumericResult<Self>
    where
        Self: Sized;

    /// Signed less than
    fn slt(self, other: Self) -> bool;

    /// Signed less than or equal
    fn sle(self, other: Self) -> bool;

    /// Signed greater than
    fn sgt(self, other: Self) -> bool;

    /// Signed greater than or equal
    fn sge(self, other: Self) -> bool;

    /// Signed minimum
    fn smin(self, other: Self) -> Self;

    /// Signed maximum
    fn smax(self, other: Self) -> Self;

    /// Signed saturation
    fn saturate(self) -> Self;

    /// Absolute value
    fn abs(self) -> Self;

    /// Negation
    fn neg(self) -> Self;
}

/// Integer operations
pub trait IntOps: Sized + TryFrom<i32> + TryFrom<i64> {
    /// The bit width of the type
    const WIDTH: BitWidth;

    /// Count leading zeros
    /// 
    /// Returns the count of leading zero bits in the value.
    /// All bits are considered leading zeros if the value is 0.
    fn clz(self) -> Self;

    /// Count trailing zeros
    /// 
    /// Returns the count of trailing zero bits in the value.
    /// All bits are considered trailing zeros if the value is 0.
    fn ctz(self) -> Self;

    /// Population count
    /// 
    /// Returns the count of non-zero bits in the value.
    fn popcnt(self) -> Self;

    /// Equal to zero
    /// 
    /// Returns 1 if the value is zero, 0 otherwise.
    fn eqz(self) -> Self;

    /// Equal
    /// 
    /// Returns 1 if the values are equal, 0 otherwise.
    fn eq(self, other: Self) -> Self;

    /// Not equal
    /// 
    /// Returns 1 if the values are not equal, 0 otherwise.
    fn ne(self, other: Self) -> Self;

    /// Unsigned less than
    /// 
    /// Returns 1 if the first value is less than the second value,
    /// interpreted as unsigned integers, 0 otherwise.
    fn lt_u(self, other: Self) -> Self;

    /// Signed less than
    /// 
    /// Returns 1 if the first value is less than the second value,
    /// interpreted as signed integers, 0 otherwise.
    fn lt_s(self, other: Self) -> Self;

    /// Signed extension
    /// 
    /// Extends the value from N bits to M bits, interpreting the value as signed.
    /// First interprets the value as signed of size M, then converts it to two's complement of size N.
    /// extends_M,N(i) = signed^-1_N(signed_M(i))
    fn extend_s<M: IntOps + TryFrom<i64>>(self) -> M 
    where
        <M as TryFrom<i64>>::Error: fmt::Debug;

    /// Bit select
    /// 
    /// Selects bits from i1 and i2 based on the bits in i3.
    /// For each bit position, if the bit in i3 is 1, the bit from i1 is selected,
    /// otherwise the bit from i2 is selected.
    fn bitselect(self, other: Self, mask: Self) -> Self;

    /// Absolute value
    /// 
    /// Returns the absolute value of the signed interpretation of the value.
    /// If the value is non-negative, returns the value itself.
    /// Otherwise, returns the negation of the value modulo 2^N.
    fn abs(self) -> Self;

    /// Negation
    /// 
    /// Returns the negation of the value modulo 2^N.
    fn neg(self) -> Self;

    /// Unsigned minimum
    /// 
    /// Returns the smaller of two values, interpreted as unsigned integers.
    fn min_u(self, other: Self) -> Self;

    /// Signed minimum
    /// 
    /// Returns the smaller of two values, interpreted as signed integers.
    fn min_s(self, other: Self) -> Self;

    /// Saturating addition (unsigned)
    /// 
    /// Returns the result of adding two values with unsigned saturation.
    /// If the result overflows, returns the maximum unsigned value.
    fn add_sat_u(self, other: Self) -> Self;

    /// Saturating addition (signed)
    /// 
    /// Returns the result of adding two values with signed saturation.
    /// If the result overflows, returns the maximum signed value.
    /// If the result underflows, returns the minimum signed value.
    fn add_sat_s(self, other: Self) -> Self;

    /// Saturating subtraction (unsigned)
    /// 
    /// Returns the result of subtracting two values with unsigned saturation.
    /// If the result underflows, returns 0.
    fn sub_sat_u(self, other: Self) -> Self;

    /// Saturating subtraction (signed)
    /// 
    /// Returns the result of subtracting two values with signed saturation.
    /// If the result overflows, returns the maximum signed value.
    /// If the result underflows, returns the minimum signed value.
    fn sub_sat_s(self, other: Self) -> Self;

    /// Average rounding (unsigned)
    /// 
    /// Returns the average of two values, rounded to the nearest integer.
    /// The result is computed as (i1 + i2 + 1) / 2, truncated toward zero.
    fn avgr_u(self, other: Self) -> Self;

    /// Q15 multiplication with rounding and saturation
    /// 
    /// Returns the result of saturating the signed value of (i1 * i2 + 2^14) >> 15.
    /// This is used for fixed-point multiplication in Q15 format.
    fn q15mulrsat_s(self, other: Self) -> Self;

    /// Unsigned extension
    /// 
    /// Extends the value from N bits to M bits, interpreting the value as unsigned.
    /// First wraps the value to N bits, then extends it to M bits.
    /// In the abstract syntax, unsigned extension just reinterprets the same value.
    fn extend_u<M: IntOps + TryFrom<u64>>(self) -> M 
    where
        <M as TryFrom<u64>>::Error: fmt::Debug;

    /// Wrap operation
    /// 
    /// Wraps the value to N bits by taking modulo 2^N.
    /// wrap_M,N(i) = i mod 2^N
    fn wrap<M: IntOps + From<u64>>(self) -> M;

    /// Converts an unsigned integer to a floating-point value
    /// 
    /// Converts the unsigned integer value to a floating-point value of the target type.
    /// convertu_M,N(i) = float_N(i)
    fn convert_u<M: FloatOps + From<f32> + From<f64>>(self) -> M;

    /// Converts a signed integer to a floating-point value
    /// 
    /// First interprets the value as signed, then converts it to a floating-point value.
    /// converts_M,N(i) = float_N(signed_M(i))
    fn convert_s<M: FloatOps + From<f32> + From<f64>>(self) -> M;

    /// Narrows a signed integer from size M to size N with saturation
    /// 
    /// First interprets the value as signed of size M, then applies signed saturation to size N.
    /// narrows_M,N(i) = sat_s_N(signed_M(i))
    fn narrow_s<M: IntOps + From<i64>>(self) -> M;

    /// Narrows an integer from size M to size N with unsigned saturation
    /// 
    /// First interprets the value as signed of size M, then applies unsigned saturation to size N.
    /// narrowu_M,N(i) = sat_u_N(signed_M(i))
    fn narrow_u<M: IntOps + From<u64>>(self) -> M;
}

/// Round a floating point number to the nearest integer
/// 
/// This implements the "round to nearest, ties to even" rounding mode
/// as specified in IEEE 754 and WebAssembly.
fn round_to_nearest_f32(x: f32) -> f32 {
    if x.is_nan() {
        return x;
    }
    if x.is_infinite() {
        return x;
    }
    if x == 0.0 {
        return x;
    }

    // Get the integer part and fractional part
    let int_part = x.trunc();
    let fract_part = x - int_part;

    // Handle ties to even
    if fract_part.abs() == 0.5 {
        // If the integer part is even, round down
        if int_part as i32 % 2 == 0 {
            int_part
        } else {
            // If the integer part is odd, round up
            if x > 0.0 {
                int_part + 1.0
            } else {
                int_part - 1.0
            }
        }
    } else if fract_part.abs() > 0.5 {
        // Round up
        if x > 0.0 {
            int_part + 1.0
        } else {
            int_part - 1.0
        }
    } else {
        // Round down
        int_part
    }
}

fn round_to_nearest_f64(x: f64) -> f64 {
    if x.is_nan() {
        return x;
    }
    if x.is_infinite() {
        return x;
    }
    if x == 0.0 {
        return x;
    }

    // Get the integer part and fractional part
    let int_part = x.trunc();
    let fract_part = x - int_part;

    // Handle ties to even
    if fract_part.abs() == 0.5 {
        // If the integer part is even, round down
        if int_part as i64 % 2 == 0 {
            int_part
        } else {
            // If the integer part is odd, round up
            if x > 0.0 {
                int_part + 1.0
            } else {
                int_part - 1.0
            }
        }
    } else if fract_part.abs() > 0.5 {
        // Round up
        if x > 0.0 {
            int_part + 1.0
        } else {
            int_part - 1.0
        }
    } else {
        // Round down
        int_part
    }
}

/// Get the fractional part of a floating point number
fn fract_f32(x: f32) -> f32 {
    x - (x as i32 as f32)
}

fn fract_f64(x: f64) -> f64 {
    x - (x as i64 as f64)
}

/// Custom implementation of square root using Newton's method
fn sqrt_f32(x: f32) -> f32 {
    if x < 0.0 {
        return f32::NAN;
    }
    if x == 0.0 {
        return 0.0;
    }
    if x == 1.0 {
        return 1.0;
    }

    let mut guess = x / 2.0;
    let mut prev_guess = 0.0;
    let epsilon = f32::EPSILON * 10.0;

    // Newton's method: x_{n+1} = (x_n + a/x_n) / 2
    while (guess - prev_guess).abs() > epsilon {
        prev_guess = guess;
        guess = (guess + x / guess) / 2.0;
    }

    guess
}

/// Custom implementation of square root using Newton's method
fn sqrt_f64(x: f64) -> f64 {
    if x < 0.0 {
        return f64::NAN;
    }
    if x == 0.0 {
        return 0.0;
    }
    if x == 1.0 {
        return 1.0;
    }

    let mut guess = x / 2.0;
    let mut prev_guess = 0.0;
    let epsilon = f64::EPSILON * 10.0;

    // Newton's method: x_{n+1} = (x_n + a/x_n) / 2
    while (guess - prev_guess).abs() > epsilon {
        prev_guess = guess;
        guess = (guess + x / guess) / 2.0;
    }

    guess
}

/// Helper function to determine if a NaN payload is canonical
fn is_canonical_nan(x: f32) -> bool {
    x.is_nan() && (x.to_bits() & 0x7FFFFF) == 0x400000
}

fn is_canonical_nan_f64(x: f64) -> bool {
    x.is_nan() && (x.to_bits() & 0xFFFFFFFFFFFFF) == 0x8000000000000
}

/// Helper function to get a canonical NaN
fn canonical_nan_f32() -> f32 {
    f32::from_bits(0x7FC00000)  // positive canonical NaN
}

fn canonical_nan_f64() -> f64 {
    f64::from_bits(0x7FF8000000000000)  // positive canonical NaN
}

/// Helper function to get an arithmetic NaN
fn arithmetic_nan_f32() -> f32 {
    f32::from_bits(0x7FC00001)  // positive arithmetic NaN
}

fn arithmetic_nan_f64() -> f64 {
    f64::from_bits(0x7FF8000000000001)  // positive arithmetic NaN
}

/// Helper function to implement nans_N{...} from the spec
fn nans_f32(inputs: &[f32]) -> f32 {
    let has_canonical = inputs.iter().all(|&x| !x.is_nan() || is_canonical_nan(x));
    if has_canonical {
        canonical_nan_f32()
    } else {
        arithmetic_nan_f32()
    }
}

fn nans_f64(inputs: &[f64]) -> f64 {
    let has_canonical = inputs.iter().all(|&x| !x.is_nan() || is_canonical_nan_f64(x));
    if has_canonical {
        canonical_nan_f64()
    } else {
        arithmetic_nan_f64()
    }
}

// Implementation for u32
impl UnsignedOps for u32 {
    const WIDTH: BitWidth = BitWidth::W32;

    fn uadd(self, other: Self) -> Self {
        self.wrapping_add(other)
    }

    fn usub(self, other: Self) -> NumericResult<Self> {
        if self < other {
            NumericResult::Err(NumericError::Underflow)
        } else {
            NumericResult::Ok(self - other)
        }
    }

    fn umul(self, other: Self) -> Self {
        self.wrapping_mul(other)
    }

    fn udiv(self, other: Self) -> NumericResult<Self> {
        if other == 0 {
            NumericResult::Err(NumericError::DivisionByZero)
        } else {
            NumericResult::Ok(self / other)
        }
    }

    fn urem(self, other: Self) -> NumericResult<Self> {
        if other == 0 {
            NumericResult::Err(NumericError::DivisionByZero)
        } else {
            NumericResult::Ok(self % other)
        }
    }

    fn ult(self, other: Self) -> bool {
        self < other
    }

    fn ule(self, other: Self) -> bool {
        self <= other
    }

    fn ugt(self, other: Self) -> bool {
        self > other
    }

    fn uge(self, other: Self) -> bool {
        self >= other
    }

    fn umin(self, other: Self) -> Self {
        self.min(other)
    }

    fn umax(self, other: Self) -> Self {
        self.max(other)
    }

    fn saturate(self) -> Self {
        self
    }
}

// Implementation for u64
impl UnsignedOps for u64 {
    const WIDTH: BitWidth = BitWidth::W64;

    fn uadd(self, other: Self) -> Self {
        self.wrapping_add(other)
    }

    fn usub(self, other: Self) -> NumericResult<Self> {
        if self < other {
            NumericResult::Err(NumericError::Underflow)
        } else {
            NumericResult::Ok(self - other)
        }
    }

    fn umul(self, other: Self) -> Self {
        self.wrapping_mul(other)
    }

    fn udiv(self, other: Self) -> NumericResult<Self> {
        if other == 0 {
            NumericResult::Err(NumericError::DivisionByZero)
        } else {
            NumericResult::Ok(self / other)
        }
    }

    fn urem(self, other: Self) -> NumericResult<Self> {
        if other == 0 {
            NumericResult::Err(NumericError::DivisionByZero)
        } else {
            NumericResult::Ok(self % other)
        }
    }

    fn ult(self, other: Self) -> bool {
        self < other
    }

    fn ule(self, other: Self) -> bool {
        self <= other
    }

    fn ugt(self, other: Self) -> bool {
        self > other
    }

    fn uge(self, other: Self) -> bool {
        self >= other
    }

    fn umin(self, other: Self) -> Self {
        self.min(other)
    }

    fn umax(self, other: Self) -> Self {
        self.max(other)
    }

    fn saturate(self) -> Self {
        self
    }
}

// Implementation for i32
impl SignedOps for i32 {
    const WIDTH: BitWidth = BitWidth::W32;

    fn sadd(self, other: Self) -> Self {
        self.wrapping_add(other)
    }

    fn ssub(self, other: Self) -> Self {
        self.wrapping_sub(other)
    }

    fn smul(self, other: Self) -> Self {
        self.wrapping_mul(other)
    }

    fn sdiv(self, other: Self) -> NumericResult<Self> {
        if other == 0 {
            NumericResult::Err(NumericError::DivisionByZero)
        } else if self == i32::MIN && other == -1 {
            NumericResult::Err(NumericError::InvalidOperation)
        } else {
            NumericResult::Ok(self.wrapping_div(other))
        }
    }

    fn srem(self, other: Self) -> NumericResult<Self> {
        if other == 0 {
            NumericResult::Err(NumericError::DivisionByZero)
        } else {
            NumericResult::Ok(self.rem_euclid(other))
        }
    }

    fn slt(self, other: Self) -> bool {
        self < other
    }

    fn sle(self, other: Self) -> bool {
        self <= other
    }

    fn sgt(self, other: Self) -> bool {
        self > other
    }

    fn sge(self, other: Self) -> bool {
        self >= other
    }

    fn smin(self, other: Self) -> Self {
        self.min(other)
    }

    fn smax(self, other: Self) -> Self {
        self.max(other)
    }

    fn saturate(self) -> Self {
        if self > Self::MAX {
            Self::MAX
        } else if self < Self::MIN {
            Self::MIN
        } else {
            self
        }
    }

    fn abs(self) -> Self {
        self.abs()
    }

    fn neg(self) -> Self {
        self.wrapping_neg()
    }
}

// Implementation for i64
impl SignedOps for i64 {
    const WIDTH: BitWidth = BitWidth::W64;

    fn sadd(self, other: Self) -> Self {
        self.wrapping_add(other)
    }

    fn ssub(self, other: Self) -> Self {
        self.wrapping_sub(other)
    }

    fn smul(self, other: Self) -> Self {
        self.wrapping_mul(other)
    }

    fn sdiv(self, other: Self) -> NumericResult<Self> {
        if other == 0 || (self == Self::MIN && other == -1) {
            NumericResult::Ok(0)
        } else {
            NumericResult::Ok(self.wrapping_div(other))
        }
    }

    fn srem(self, other: Self) -> NumericResult<Self> {
        if other == 0 {
            NumericResult::Ok(0)
        } else {
            NumericResult::Ok(self.wrapping_rem(other))
        }
    }

    fn slt(self, other: Self) -> bool {
        self < other
    }

    fn sle(self, other: Self) -> bool {
        self <= other
    }

    fn sgt(self, other: Self) -> bool {
        self > other
    }

    fn sge(self, other: Self) -> bool {
        self >= other
    }

    fn smin(self, other: Self) -> Self {
        self.min(other)
    }

    fn smax(self, other: Self) -> Self {
        self.max(other)
    }

    fn saturate(self) -> Self {
        if self > Self::MAX {
            Self::MAX
        } else if self < Self::MIN {
            Self::MIN
        } else {
            self
        }
    }

    fn abs(self) -> Self {
        self.abs()
    }

    fn neg(self) -> Self {
        self.wrapping_neg()
    }
}

// Implementation for f32
impl FloatOps for f32 {
    const WIDTH: BitWidth = BitWidth::W32;

    fn add(self, other: Self) -> Self {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            return nans_f32(&[self, other]);
        }

        // Handle infinity cases
        if self.is_infinite() && other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return self;  // Same sign infinity
            } else {
                return nans_f32(&[]);  // Opposite sign infinity
            }
        }
        if self.is_infinite() {
            return self;
        }
        if other.is_infinite() {
            return other;
        }

        // Handle zero cases
        if self == 0.0 && other == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return self;  // Same sign zero
            } else {
                return 0.0;  // Positive zero for opposite signs
            }
        }
        if self == 0.0 {
            return other;
        }
        if other == 0.0 {
            return self;
        }

        // Handle same magnitude, opposite signs
        if self.abs() == other.abs() && (self > 0.0) != (other > 0.0) {
            return 0.0;  // Positive zero
        }

        // Normal addition
        self + other
    }

    fn sub(self, other: Self) -> Self {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            return nans_f32(&[self, other]);
        }

        // Handle infinity cases
        if self.is_infinite() && other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return nans_f32(&[]);  // Same sign infinity
            } else {
                return self;  // Opposite sign infinity
            }
        }
        if self.is_infinite() {
            return self;
        }
        if other.is_infinite() {
            return -other;  // Negated infinity
        }

        // Handle zero cases
        if self == 0.0 && other == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return 0.0;  // Positive zero for same signs
            } else {
                return self;  // Keep first zero's sign
            }
        }
        if other == 0.0 {
            return self;
        }
        if self == 0.0 {
            return -other;  // Negated second operand
        }

        // Handle same value
        if self == other {
            return 0.0;  // Positive zero
        }

        // Normal subtraction
        self - other
    }

    fn mul(self, other: Self) -> NumericResult<Self> {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            return NumericResult::Ok(nans_f32(&[self, other]));
        }

        // Handle zero and infinity cases
        if (self == 0.0 && other.is_infinite()) || (self.is_infinite() && other == 0.0) {
            return NumericResult::Ok(nans_f32(&[]));
        }

        // Handle infinity cases
        if self.is_infinite() && other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f32::INFINITY);  // Same sign infinity
            } else {
                return NumericResult::Ok(f32::NEG_INFINITY);  // Opposite sign infinity
            }
        }

        // Handle infinity with finite value
        if self.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f32::INFINITY);
            } else {
                return NumericResult::Ok(f32::NEG_INFINITY);
            }
        }
        if other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f32::INFINITY);
            } else {
                return NumericResult::Ok(f32::NEG_INFINITY);
            }
        }

        // Handle zero cases
        if self == 0.0 && other == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(0.0);  // Positive zero for same signs
            } else {
                return NumericResult::Ok(-0.0);  // Negative zero for opposite signs
            }
        }

        // Normal multiplication
        NumericResult::Ok(self * other)
    }

    fn div(self, other: Self) -> NumericResult<Self> {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            return NumericResult::Ok(nans_f32(&[self, other]));
        }

        // Handle infinity and infinity cases
        if self.is_infinite() && other.is_infinite() {
            return NumericResult::Ok(nans_f32(&[]));
        }

        // Handle zero and zero cases
        if self == 0.0 && other == 0.0 {
            return NumericResult::Ok(nans_f32(&[self, other]));
        }

        // Handle infinity with finite value
        if self.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f32::INFINITY);  // Same sign
            } else {
                return NumericResult::Ok(f32::NEG_INFINITY);  // Opposite sign
            }
        }

        // Handle finite value with infinity
        if other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(0.0);  // Positive zero for same sign
            } else {
                return NumericResult::Ok(-0.0);  // Negative zero for opposite sign
            }
        }

        // Handle zero with finite value
        if self == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(0.0);  // Positive zero for same sign
            } else {
                return NumericResult::Ok(-0.0);  // Negative zero for opposite sign
            }
        }

        // Handle finite value with zero
        if other == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f32::INFINITY);  // Positive infinity for same sign
            } else {
                return NumericResult::Ok(f32::NEG_INFINITY);  // Negative infinity for opposite sign
            }
        }

        // Normal division
        NumericResult::Ok(self / other)
    }

    fn sqrt(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f32(&[self])
        }
        // Handle negative infinity
        else if self == f32::NEG_INFINITY {
            nans_f32(&[])
        }
        // Handle positive infinity
        else if self == f32::INFINITY {
            f32::INFINITY
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle negative value
        else if self < 0.0 {
            nans_f32(&[])
        }
        // Handle positive value
        else {
            sqrt_f32(self)
        }
    }

    fn min(self, other: Self) -> Self {
        // If other is less than self, return other
        // Otherwise return self
        if other.lt(self) {
            other
        } else {
            self
        }
    }

    fn max(self, other: Self) -> Self {
        // If self is less than other, return other
        // Otherwise return self
        if self.lt(other) {
            other
        } else {
            self
        }
    }

    fn ceil(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f32(&[self])
        }
        // Handle infinity case
        else if self.is_infinite() {
            self  // Preserve sign of infinity
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle negative value between -1 and 0
        else if self < 0.0 && self > -1.0 {
            -0.0
        }
        // Handle other values
        else {
            let fract = fract_f32(self);
            if fract > 0.0 {
                FloatOps::trunc(self) + 1.0
            } else {
                FloatOps::trunc(self)
            }
        }
    }

    fn floor(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f32(&[self])
        }
        // Handle infinity case
        else if self.is_infinite() {
            self  // Preserve sign of infinity
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle positive value between 0 and 1
        else if self > 0.0 && self < 1.0 {
            0.0
        }
        // Handle negative value between -1 and 0
        else if self < 0.0 && self > -1.0 {
            -0.0
        }
        // Handle other values
        else {
            // Get the integer part with the same sign as the input
            let int_part = self as i32 as f32;
            if self > 0.0 {
                int_part
            } else {
                -int_part.abs()
            }
        }
    }

    fn trunc(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f32(&[self])
        }
        // Handle infinity case
        else if self.is_infinite() {
            self  // Preserve sign of infinity
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle positive value between 0 and 1
        else if self > 0.0 && self < 1.0 {
            0.0
        }
        // Handle negative value between -1 and 0
        else if self < 0.0 && self > -1.0 {
            -0.0
        }
        // Handle other values
        else {
            // Get the integer part with the same sign as the input
            let int_part = self as i32 as f32;
            if self > 0.0 {
                int_part
            } else {
                -int_part.abs()
            }
        }
    }

    fn nearest(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f32(&[self])
        }
        // Handle infinity case
        else if self.is_infinite() {
            self  // Preserve sign of infinity
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle positive value between 0 and 0.5 (inclusive)
        else if self > 0.0 && self <= 0.5 {
            0.0
        }
        // Handle negative value between -0.5 (inclusive) and 0
        else if self < 0.0 && self >= -0.5 {
            -0.0
        }
        // Handle other values
        else {
            // Get the integer part and fractional part
            let int_part = self.trunc();
            let fract_part = self - int_part;

            // Handle ties to even
            if fract_part.abs() == 0.5 {
                // If the integer part is even, round down
                if int_part as i32 % 2 == 0 {
                    int_part
                } else {
                    // If the integer part is odd, round up
                    if self > 0.0 {
                        int_part + 1.0
                    } else {
                        int_part - 1.0
                    }
                }
            } else if fract_part.abs() > 0.5 {
                // Round up
                if self > 0.0 {
                    int_part + 1.0
                } else {
                    int_part - 1.0
                }
            } else {
                // Round down
                int_part
            }
        }
    }

    fn abs(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            // Return NaN with positive sign
            f32::from_bits(self.to_bits() & 0x7FFFFFFF)
        }
        // Handle infinity case
        else if self.is_infinite() {
            f32::INFINITY
        }
        // Handle zero case
        else if self == 0.0 {
            0.0  // Return positive zero
        }
        // Handle positive value
        else if self > 0.0 {
            self
        }
        // Handle negative value
        else {
            -self
        }
    }

    fn neg(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            // Return NaN with negated sign
            f32::from_bits(self.to_bits() ^ 0x80000000)
        }
        // Handle infinity case
        else if self.is_infinite() {
            if self > 0.0 {
                f32::NEG_INFINITY
            } else {
                f32::INFINITY
            }
        }
        // Handle zero case
        else if self == 0.0 {
            if self > 0.0 {
                -0.0
            } else {
                0.0
            }
        }
        // Handle other values
        else {
            -self
        }
    }

    fn copysign(self, other: Self) -> Self {
        // If z1 and z2 have the same sign, return z1
        if (self > 0.0) == (other > 0.0) {
            self
        }
        // Else return z1 with negated sign
        else {
            -self
        }
    }

    fn eq(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            true
        }
        // Handle other values
        else {
            self == other
        }
    }

    fn ne(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            true
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            false
        }
        // Handle other values
        else {
            self != other
        }
    }

    fn lt(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle same value case
        else if self == other {
            false
        }
        // Handle infinity cases
        else if self == f32::INFINITY {
            false
        }
        else if self == f32::NEG_INFINITY {
            true
        }
        else if other == f32::INFINITY {
            true
        }
        else if other == f32::NEG_INFINITY {
            false
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            false
        }
        // Handle other values
        else {
            self < other
        }
    }

    fn le(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle same value case
        else if self == other {
            true
        }
        // Handle infinity cases
        else if self == f32::INFINITY {
            false
        }
        else if self == f32::NEG_INFINITY {
            true
        }
        else if other == f32::INFINITY {
            true
        }
        else if other == f32::NEG_INFINITY {
            false
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            true
        }
        // Handle other values
        else {
            self <= other
        }
    }

    fn gt(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle same value case
        else if self == other {
            false
        }
        // Handle infinity cases
        else if self == f32::INFINITY {
            true
        }
        else if self == f32::NEG_INFINITY {
            false
        }
        else if other == f32::INFINITY {
            false
        }
        else if other == f32::NEG_INFINITY {
            true
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            false
        }
        // Handle other values
        else {
            self > other
        }
    }

    fn ge(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle same value case
        else if self == other {
            true
        }
        // Handle infinity cases
        else if self == f32::INFINITY {
            true
        }
        else if self == f32::NEG_INFINITY {
            false
        }
        else if other == f32::INFINITY {
            false
        }
        else if other == f32::NEG_INFINITY {
            true
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            true
        }
        // Handle other values
        else {
            self >= other
        }
    }

    fn rem(self, other: Self) -> Self {
        if other == 0.0 {
            f32::NAN
        } else {
            self % other
        }
    }

    fn trunc_u<M: IntOps + From<u64>>(self) -> Option<M> {
        // Check for NaN or infinity
        if self.is_nan() || self.is_infinite() {
            return None;
        }

        // Truncate the value
        let truncated = self.trunc();
        
        // Check if the truncated value is in range (0 <= x < 2^N)
        if truncated < 0.0 || truncated >= M::WIDTH.max_unsigned() as f32 {
            return None;
        }

        // Convert to unsigned integer
        Some(M::from(truncated as u64))
    }

    fn trunc_s<M: IntOps + From<i64>>(self) -> Option<M> {
        // Check for NaN or infinity
        if self.is_nan() || self.is_infinite() {
            return None;
        }

        // Truncate the value
        let truncated = self.trunc();
        
        // Check if the truncated value is in range (-2^(N-1) - 1 < x < 2^(N-1))
        let min_value = M::WIDTH.min_signed() as f32;
        let max_value = M::WIDTH.max_signed() as f32;
        if truncated <= min_value || truncated >= max_value {
            return None;
        }

        // Convert to signed integer
        Some(M::from(truncated as i64))
    }

    fn trunc_sat_u<M: IntOps + From<u64>>(self) -> M {
        // Handle special cases
        if self.is_nan() || (self.is_infinite() && self.is_sign_negative()) {
            return M::from(0u64);
        }
        if self.is_infinite() && self.is_sign_positive() {
            return M::from(M::WIDTH.max_unsigned());
        }

        // Truncate the value
        let truncated = self.trunc();
        
        // Apply saturation
        if truncated < 0.0 {
            // Negative values saturate to 0
            M::from(0u64)
        } else if truncated >= M::WIDTH.max_unsigned() as f32 {
            // Values >= 2^N saturate to 2^N - 1
            M::from(M::WIDTH.max_unsigned())
        } else {
            // In-range values are converted directly
            M::from(truncated as u64)
        }
    }

    fn trunc_sat_s<M: IntOps + From<i64>>(self) -> M {
        // Handle special cases
        if self.is_nan() {
            return M::from(0i64);
        }
        if self.is_infinite() {
            if self.is_sign_negative() {
                // Negative infinity saturates to -2^(N-1)
                return M::from(M::WIDTH.min_signed());
            } else {
                // Positive infinity saturates to 2^(N-1) - 1
                return M::from(M::WIDTH.max_signed());
            }
        }

        // Truncate the value
        let truncated = self.trunc();
        
        // Apply saturation
        if truncated <= M::WIDTH.min_signed() as f32 {
            // Values <= -2^(N-1) saturate to -2^(N-1)
            M::from(M::WIDTH.min_signed())
        } else if truncated >= M::WIDTH.max_signed() as f32 {
            // Values >= 2^(N-1) saturate to 2^(N-1) - 1
            M::from(M::WIDTH.max_signed())
        } else {
            // In-range values are converted directly
            M::from(truncated as i64)
        }
    }

    fn promote<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Handle NaN cases
        if self.is_nan() {
            // Check if it's a canonical NaN
            if is_canonical_nan(self) {
                // Return canonical NaN of target size
                if M::WIDTH == BitWidth::W32 {
                    M::from(canonical_nan_f32())
                } else {
                    M::from(canonical_nan_f64())
                }
            } else {
                // Return arithmetic NaN of target size
                if M::WIDTH == BitWidth::W32 {
                    M::from(arithmetic_nan_f32())
                } else {
                    M::from(arithmetic_nan_f64())
                }
            }
        } else {
            // For non-NaN values, convert based on target type
            if M::WIDTH == BitWidth::W32 {
                M::from(self)
            } else {
                M::from(self as f64)
            }
        }
    }

    fn demote<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Handle NaN cases
        if self.is_nan() {
            // Check if it's a canonical NaN
            if is_canonical_nan(self) {
                // Return canonical NaN of target size
                if M::WIDTH == BitWidth::W32 {
                    M::from(canonical_nan_f32())
                } else {
                    M::from(canonical_nan_f64())
                }
            } else {
                // Return arithmetic NaN of target size
                if M::WIDTH == BitWidth::W32 {
                    M::from(arithmetic_nan_f32())
                } else {
                    M::from(arithmetic_nan_f64())
                }
            }
        }
        // Handle infinity cases
        else if self.is_infinite() {
            // Preserve the sign of infinity
            if M::WIDTH == BitWidth::W32 {
                M::from(self)  // ±∞ as f32
            } else {
                M::from(self as f64)  // ±∞ as f64
            }
        }
        // Handle zero cases
        else if self == 0.0 {
            // Preserve the sign of zero
            if M::WIDTH == BitWidth::W32 {
                M::from(self)  // ±0 as f32
            } else {
                M::from(self as f64)  // ±0 as f64
            }
        }
        // Handle other values
        else {
            // Convert to target type
            if M::WIDTH == BitWidth::W32 {
                M::from(self)  // float_32(z)
            } else {
                M::from(self as f64)  // float_64(z)
            }
        }
    }

    fn reinterpret<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Use core::mem::transmute to reinterpret bits
        // This is safe because we're just reinterpreting the bits
        // and the target type M is constrained to be FloatOps
        if M::WIDTH == BitWidth::W32 {
            // For 32-bit target (i32)
            let bits: u32 = unsafe { core::mem::transmute(self) };
            M::from(bits as i32 as f32)
        } else {
            // For 64-bit target (i64)
            let bits: u32 = unsafe { core::mem::transmute(self) };
            M::from(bits as i64 as f64)
        }
    }
}

impl FloatOps for f64 {
    const WIDTH: BitWidth = BitWidth::W64;

    fn add(self, other: Self) -> Self {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            return nans_f64(&[self, other]);
        }

        // Handle infinity cases
        if self.is_infinite() && other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return self;  // Same sign infinity
            } else {
                return nans_f64(&[]);  // Opposite sign infinity
            }
        }
        if self.is_infinite() {
            return self;
        }
        if other.is_infinite() {
            return other;
        }

        // Handle zero cases
        if self == 0.0 && other == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return self;  // Same sign zero
            } else {
                return 0.0;  // Positive zero for opposite signs
            }
        }
        if self == 0.0 {
            return other;
        }
        if other == 0.0 {
            return self;
        }

        // Handle same magnitude, opposite signs
        if self.abs() == other.abs() && (self > 0.0) != (other > 0.0) {
            return 0.0;  // Positive zero
        }

        // Normal addition
        self + other
    }

    fn sub(self, other: Self) -> Self {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            return nans_f64(&[self, other]);
        }

        // Handle infinity cases
        if self.is_infinite() && other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return nans_f64(&[]);  // Same sign infinity
            } else {
                return self;  // Opposite sign infinity
            }
        }
        if self.is_infinite() {
            return self;
        }
        if other.is_infinite() {
            return -other;  // Negated infinity
        }

        // Handle zero cases
        if self == 0.0 && other == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return 0.0;  // Positive zero for same signs
            } else {
                return self;  // Keep first zero's sign
            }
        }
        if other == 0.0 {
            return self;
        }
        if self == 0.0 {
            return -other;  // Negated second operand
        }

        // Handle same value
        if self == other {
            return 0.0;  // Positive zero
        }

        // Normal subtraction
        self - other
    }

    fn mul(self, other: Self) -> NumericResult<Self> {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            return NumericResult::Ok(nans_f64(&[self, other]));
        }

        // Handle zero and infinity cases
        if (self == 0.0 && other.is_infinite()) || (self.is_infinite() && other == 0.0) {
            return NumericResult::Ok(nans_f64(&[]));
        }

        // Handle infinity cases
        if self.is_infinite() && other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f64::INFINITY);  // Same sign infinity
            } else {
                return NumericResult::Ok(f64::NEG_INFINITY);  // Opposite sign infinity
            }
        }

        // Handle infinity with finite value
        if self.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f64::INFINITY);
            } else {
                return NumericResult::Ok(f64::NEG_INFINITY);
            }
        }
        if other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f64::INFINITY);
            } else {
                return NumericResult::Ok(f64::NEG_INFINITY);
            }
        }

        // Handle zero cases
        if self == 0.0 && other == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(0.0);  // Positive zero for same signs
            } else {
                return NumericResult::Ok(-0.0);  // Negative zero for opposite signs
            }
        }

        // Normal multiplication
        NumericResult::Ok(self * other)
    }

    fn div(self, other: Self) -> NumericResult<Self> {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            return NumericResult::Ok(nans_f64(&[self, other]));
        }

        // Handle infinity and infinity cases
        if self.is_infinite() && other.is_infinite() {
            return NumericResult::Ok(nans_f64(&[]));
        }

        // Handle zero and zero cases
        if self == 0.0 && other == 0.0 {
            return NumericResult::Ok(nans_f64(&[self, other]));
        }

        // Handle infinity with finite value
        if self.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f64::INFINITY);  // Same sign
            } else {
                return NumericResult::Ok(f64::NEG_INFINITY);  // Opposite sign
            }
        }

        // Handle finite value with infinity
        if other.is_infinite() {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(0.0);  // Positive zero for same sign
            } else {
                return NumericResult::Ok(-0.0);  // Negative zero for opposite sign
            }
        }

        // Handle zero with finite value
        if self == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(0.0);  // Positive zero for same sign
            } else {
                return NumericResult::Ok(-0.0);  // Negative zero for opposite sign
            }
        }

        // Handle finite value with zero
        if other == 0.0 {
            if (self > 0.0) == (other > 0.0) {
                return NumericResult::Ok(f64::INFINITY);  // Positive infinity for same sign
            } else {
                return NumericResult::Ok(f64::NEG_INFINITY);  // Negative infinity for opposite sign
            }
        }

        // Normal division
        NumericResult::Ok(self / other)
    }

    fn sqrt(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f64(&[self])
        }
        // Handle negative infinity
        else if self == f64::NEG_INFINITY {
            nans_f64(&[])
        }
        // Handle positive infinity
        else if self == f64::INFINITY {
            f64::INFINITY
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle negative value
        else if self < 0.0 {
            nans_f64(&[])
        }
        // Handle positive value
        else {
            sqrt_f64(self)
        }
    }

    fn min(self, other: Self) -> Self {
        // If other is less than self, return other
        // Otherwise return self
        if other.lt(self) {
            other
        } else {
            self
        }
    }

    fn max(self, other: Self) -> Self {
        // If self is less than other, return other
        // Otherwise return self
        if self.lt(other) {
            other
        } else {
            self
        }
    }

    fn ceil(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f64(&[self])
        }
        // Handle infinity case
        else if self.is_infinite() {
            self  // Preserve sign of infinity
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle negative value between -1 and 0
        else if self < 0.0 && self > -1.0 {
            -0.0
        }
        // Handle other values
        else {
            let fract = fract_f64(self);
            if fract > 0.0 {
                FloatOps::trunc(self) + 1.0
            } else {
                FloatOps::trunc(self)
            }
        }
    }

    fn floor(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f64(&[self])
        }
        // Handle infinity case
        else if self.is_infinite() {
            self  // Preserve sign of infinity
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle positive value between 0 and 1
        else if self > 0.0 && self < 1.0 {
            0.0
        }
        // Handle negative value between -1 and 0
        else if self < 0.0 && self > -1.0 {
            -0.0
        }
        // Handle other values
        else {
            // Get the integer part with the same sign as the input
            let int_part = self as i64 as f64;
            if self > 0.0 {
                int_part
            } else {
                -int_part.abs()
            }
        }
    }

    fn trunc(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f64(&[self])
        }
        // Handle infinity case
        else if self.is_infinite() {
            self  // Preserve sign of infinity
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle positive value between 0 and 1
        else if self > 0.0 && self < 1.0 {
            0.0
        }
        // Handle negative value between -1 and 0
        else if self < 0.0 && self > -1.0 {
            -0.0
        }
        // Handle other values
        else {
            // Get the integer part with the same sign as the input
            let int_part = self as i64 as f64;
            if self > 0.0 {
                int_part
            } else {
                -int_part.abs()
            }
        }
    }

    fn nearest(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            nans_f64(&[self])
        }
        // Handle infinity case
        else if self.is_infinite() {
            self  // Preserve sign of infinity
        }
        // Handle zero case
        else if self == 0.0 {
            self  // Preserve sign of zero
        }
        // Handle positive value between 0 and 0.5 (inclusive)
        else if self > 0.0 && self <= 0.5 {
            0.0
        }
        // Handle negative value between -0.5 (inclusive) and 0
        else if self < 0.0 && self >= -0.5 {
            -0.0
        }
        // Handle other values
        else {
            // Get the integer part and fractional part
            let int_part = self.trunc();
            let fract_part = self - int_part;

            // Handle ties to even
            if fract_part.abs() == 0.5 {
                // If the integer part is even, round down
                if int_part as i64 % 2 == 0 {
                    int_part
                } else {
                    // If the integer part is odd, round up
                    if self > 0.0 {
                        int_part + 1.0
                    } else {
                        int_part - 1.0
                    }
                }
            } else if fract_part.abs() > 0.5 {
                // Round up
                if self > 0.0 {
                    int_part + 1.0
                } else {
                    int_part - 1.0
                }
            } else {
                // Round down
                int_part
            }
        }
    }

    fn abs(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            // Return NaN with positive sign
            f64::from_bits(self.to_bits() & 0x7FFFFFFFFFFFFFFF)
        }
        // Handle infinity case
        else if self.is_infinite() {
            f64::INFINITY
        }
        // Handle zero case
        else if self == 0.0 {
            0.0  // Return positive zero
        }
        // Handle positive value
        else if self > 0.0 {
            self
        }
        // Handle negative value
        else {
            -self
        }
    }

    fn neg(self) -> Self {
        // Handle NaN case
        if self.is_nan() {
            // Return NaN with negated sign
            f64::from_bits(self.to_bits() ^ 0x8000000000000000)
        }
        // Handle infinity case
        else if self.is_infinite() {
            if self > 0.0 {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            }
        }
        // Handle zero case
        else if self == 0.0 {
            if self > 0.0 {
                -0.0
            } else {
                0.0
            }
        }
        // Handle other values
        else {
            -self
        }
    }

    fn copysign(self, other: Self) -> Self {
        // If z1 and z2 have the same sign, return z1
        if (self > 0.0) == (other > 0.0) {
            self
        }
        // Else return z1 with negated sign
        else {
            -self
        }
    }

    fn eq(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            true
        }
        // Handle other values
        else {
            self == other
        }
    }

    fn ne(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            true
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            false
        }
        // Handle other values
        else {
            self != other
        }
    }

    fn lt(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle same value case
        else if self == other {
            false
        }
        // Handle infinity cases
        else if self == f64::INFINITY {
            false
        }
        else if self == f64::NEG_INFINITY {
            true
        }
        else if other == f64::INFINITY {
            true
        }
        else if other == f64::NEG_INFINITY {
            false
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            false
        }
        // Handle other values
        else {
            self < other
        }
    }

    fn le(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle same value case
        else if self == other {
            true
        }
        // Handle infinity cases
        else if self == f64::INFINITY {
            false
        }
        else if self == f64::NEG_INFINITY {
            true
        }
        else if other == f64::INFINITY {
            true
        }
        else if other == f64::NEG_INFINITY {
            false
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            true
        }
        // Handle other values
        else {
            self <= other
        }
    }

    fn gt(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle same value case
        else if self == other {
            false
        }
        // Handle infinity cases
        else if self == f64::INFINITY {
            true
        }
        else if self == f64::NEG_INFINITY {
            false
        }
        else if other == f64::INFINITY {
            false
        }
        else if other == f64::NEG_INFINITY {
            true
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            false
        }
        // Handle other values
        else {
            self > other
        }
    }

    fn ge(self, other: Self) -> bool {
        // Handle NaN cases
        if self.is_nan() || other.is_nan() {
            false
        }
        // Handle same value case
        else if self == other {
            true
        }
        // Handle infinity cases
        else if self == f64::INFINITY {
            true
        }
        else if self == f64::NEG_INFINITY {
            false
        }
        else if other == f64::INFINITY {
            false
        }
        else if other == f64::NEG_INFINITY {
            true
        }
        // Handle zero cases (including opposite signs)
        else if self == 0.0 && other == 0.0 {
            true
        }
        // Handle other values
        else {
            self >= other
        }
    }

    fn rem(self, other: Self) -> Self {
        if other == 0.0 {
            f64::NAN
        } else {
            self % other
        }
    }

    fn trunc_u<M: IntOps + From<u64>>(self) -> Option<M> {
        // Check for NaN or infinity
        if self.is_nan() || self.is_infinite() {
            return None;
        }

        // Truncate the value
        let truncated = self.trunc();
        
        // Check if the truncated value is in range (0 <= x < 2^N)
        if truncated < 0.0 || truncated >= M::WIDTH.max_unsigned() as f64 {
            return None;
        }

        // Convert to unsigned integer
        Some(M::from(truncated as u64))
    }

    fn trunc_s<M: IntOps + From<i64>>(self) -> Option<M> {
        // Check for NaN or infinity
        if self.is_nan() || self.is_infinite() {
            return None;
        }

        // Truncate the value
        let truncated = self.trunc();
        
        // Check if the truncated value is in range (-2^(N-1) - 1 < x < 2^(N-1))
        let min_value = M::WIDTH.min_signed() as f64;
        let max_value = M::WIDTH.max_signed() as f64;
        if truncated <= min_value || truncated >= max_value {
            return None;
        }

        // Convert to signed integer
        Some(M::from(truncated as i64))
    }

    fn trunc_sat_u<M: IntOps + From<u64>>(self) -> M {
        // Handle special cases
        if self.is_nan() || (self.is_infinite() && self.is_sign_negative()) {
            return M::from(0u64);
        }
        if self.is_infinite() && self.is_sign_positive() {
            return M::from(M::WIDTH.max_unsigned());
        }

        // Truncate the value
        let truncated = self.trunc();
        
        // Apply saturation
        if truncated < 0.0 {
            // Negative values saturate to 0
            M::from(0u64)
        } else if truncated >= M::WIDTH.max_unsigned() as f64 {
            // Values >= 2^N saturate to 2^N - 1
            M::from(M::WIDTH.max_unsigned())
        } else {
            // In-range values are converted directly
            M::from(truncated as u64)
        }
    }

    fn trunc_sat_s<M: IntOps + From<i64>>(self) -> M {
        // Handle special cases
        if self.is_nan() {
            return M::from(0i64);
        }
        if self.is_infinite() {
            if self.is_sign_negative() {
                // Negative infinity saturates to -2^(N-1)
                return M::from(M::WIDTH.min_signed());
            } else {
                // Positive infinity saturates to 2^(N-1) - 1
                return M::from(M::WIDTH.max_signed());
            }
        }

        // Truncate the value
        let truncated = self.trunc();
        
        // Apply saturation
        if truncated <= M::WIDTH.min_signed() as f64 {
            // Values <= -2^(N-1) saturate to -2^(N-1)
            M::from(M::WIDTH.min_signed())
        } else if truncated >= M::WIDTH.max_signed() as f64 {
            // Values >= 2^(N-1) saturate to 2^(N-1) - 1
            M::from(M::WIDTH.max_signed())
        } else {
            // In-range values are converted directly
            M::from(truncated as i64)
        }
    }

    fn promote<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Handle NaN cases
        if self.is_nan() {
            // Check if it's a canonical NaN
            if is_canonical_nan_f64(self) {
                // Return canonical NaN of target size
                if M::WIDTH == BitWidth::W32 {
                    M::from(canonical_nan_f32())
                } else {
                    M::from(canonical_nan_f64())
                }
            } else {
                // Return arithmetic NaN of target size
                if M::WIDTH == BitWidth::W32 {
                    M::from(arithmetic_nan_f32())
                } else {
                    M::from(arithmetic_nan_f64())
                }
            }
        } else {
            // For non-NaN values, convert based on target type
            if M::WIDTH == BitWidth::W32 {
                M::from(self as f32)
            } else {
                M::from(self)
            }
        }
    }

    fn demote<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Handle NaN cases
        if self.is_nan() {
            // Check if it's a canonical NaN
            if is_canonical_nan_f64(self) {
                // Return canonical NaN of target size
                if M::WIDTH == BitWidth::W32 {
                    M::from(canonical_nan_f32())
                } else {
                    M::from(canonical_nan_f64())
                }
            } else {
                // Return arithmetic NaN of target size
                if M::WIDTH == BitWidth::W32 {
                    M::from(arithmetic_nan_f32())
                } else {
                    M::from(arithmetic_nan_f64())
                }
            }
        }
        // Handle infinity cases
        else if self.is_infinite() {
            // Preserve the sign of infinity
            if M::WIDTH == BitWidth::W32 {
                M::from(self as f32)  // ±∞ as f32
            } else {
                M::from(self)  // ±∞ as f64
            }
        }
        // Handle zero cases
        else if self == 0.0 {
            // Preserve the sign of zero
            if M::WIDTH == BitWidth::W32 {
                M::from(self as f32)  // ±0 as f32
            } else {
                M::from(self)  // ±0 as f64
            }
        }
        // Handle other values
        else {
            // Convert to target type
            if M::WIDTH == BitWidth::W32 {
                M::from(self as f32)  // float_32(z)
            } else {
                M::from(self)  // float_64(z)
            }
        }
    }

    fn reinterpret<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Use core::mem::transmute to reinterpret bits
        // This is safe because we're just reinterpreting the bits
        // and the target type M is constrained to be FloatOps
        if M::WIDTH == BitWidth::W32 {
            // For 32-bit target (i32)
            let bits: u64 = unsafe { core::mem::transmute(self) };
            M::from((bits as i32) as f32)
        } else {
            // For 64-bit target (i64)
            let bits: u64 = unsafe { core::mem::transmute(self) };
            M::from(bits as i64 as f64)
        }
    }
}

/// Vector operations for numeric types
pub trait VectorOps<T> {
    /// Applies a unary operation to each element of the vector
    fn unary_op<F>(self, f: F) -> Self
    where
        F: Fn(T) -> T;

    /// Applies a binary operation to each element of the vector
    fn binary_op<F>(self, other: Self, f: F) -> Self
    where
        F: Fn(T, T) -> T;

    /// Applies a binary operation to each element of the vector, returning a vector of results
    fn binary_op_result<F>(self, other: Self, f: F) -> Vec<NumericResult<T>>
    where
        F: Fn(T, T) -> NumericResult<T>;

    /// Applies a comparison operation to each element of the vector
    fn compare_op<F>(self, other: Self, f: F) -> Vec<bool>
    where
        F: Fn(T, T) -> bool;
}

// Implementation for Vec<T> where T: Copy
impl<T: Copy> VectorOps<T> for Vec<T> {
    fn unary_op<F>(self, f: F) -> Self
    where
        F: Fn(T) -> T,
    {
        self.into_iter().map(f).collect()
    }

    fn binary_op<F>(self, other: Self, f: F) -> Self
    where
        F: Fn(T, T) -> T,
    {
        self.into_iter()
            .zip(other.into_iter())
            .map(|(a, b)| f(a, b))
            .collect()
    }

    fn binary_op_result<F>(self, other: Self, f: F) -> Vec<NumericResult<T>>
    where
        F: Fn(T, T) -> NumericResult<T>,
    {
        self.into_iter()
            .zip(other.into_iter())
            .map(|(a, b)| f(a, b))
            .collect()
    }

    fn compare_op<F>(self, other: Self, f: F) -> Vec<bool>
    where
        F: Fn(T, T) -> bool,
    {
        self.into_iter()
            .zip(other.into_iter())
            .map(|(a, b)| f(a, b))
            .collect()
    }
}

impl<T: FloatOps + From<f32> + From<f64> + Into<f32> + Into<f64> + PartialEq + 
    core::ops::Div<Output = T> + core::ops::Rem<Output = T> + 
    core::cmp::PartialOrd> NumericOps<T> for T {
    fn sqrt(self) -> NumericResult<T> {
        if self < T::from(0.0) {
            NumericResult::Err(NumericError::InvalidOperation)
        } else {
            // Convert to f64 for better precision, then back to T
            let x: f64 = self.into();
            let sqrt_x = sqrt_f64(x);
            NumericResult::Ok(T::from(sqrt_x))
        }
    }

    fn div(self, other: T) -> NumericResult<T> {
        if other == T::from(0.0) {
            NumericResult::Err(NumericError::DivisionByZero)
        } else {
            NumericResult::Ok(self / other)
        }
    }

    fn rem(self, other: T) -> NumericResult<T> {
        if other == T::from(0.0) {
            NumericResult::Err(NumericError::DivisionByZero)
        } else {
            NumericResult::Ok(self % other)
        }
    }

    fn trunc(self) -> NumericResult<T> {
        // Convert to f64 for better precision, then back to T
        let x: f64 = self.into();
        let trunc_x = x.trunc();
        NumericResult::Ok(T::from(trunc_x))
    }
}

// Implementation for i32
impl IntOps for i32 {
    const WIDTH: BitWidth = BitWidth::W32;

    fn clz(self) -> Self {
        if self == 0 {
            32
        } else {
            self.leading_zeros() as i32
        }
    }

    fn ctz(self) -> Self {
        if self == 0 {
            32
        } else {
            self.trailing_zeros() as i32
        }
    }

    fn popcnt(self) -> Self {
        self.count_ones() as i32
    }

    fn eqz(self) -> Self {
        if self == 0 { 1 } else { 0 }
    }

    fn eq(self, other: Self) -> Self {
        if self == other { 1 } else { 0 }
    }

    fn ne(self, other: Self) -> Self {
        if self != other { 1 } else { 0 }
    }

    fn lt_u(self, other: Self) -> Self {
        if (self as u32) < (other as u32) { 1 } else { 0 }
    }

    fn lt_s(self, other: Self) -> Self {
        if self < other { 1 } else { 0 }
    }

    fn extend_s<M: IntOps + TryFrom<i64>>(self) -> M 
    where
        <M as TryFrom<i64>>::Error: fmt::Debug
    {
        // Already signed, just convert to target type's two's complement
        M::try_from(self as i64).unwrap_or_else(|_| {
            // If the conversion fails, wrap the value to the target type's bit width
            let min = M::WIDTH.min_signed();
            let max = M::WIDTH.max_signed();
            let mask = max - min + 1;
            M::try_from((self as i64 & mask) + min).unwrap()
        })
    }

    fn bitselect(self, other: Self, mask: Self) -> Self {
        // j1 = i1 & i3
        let j1 = self & mask;
        // j3' = !i3
        let j3_not = !mask;
        // j2 = i2 & j3'
        let j2 = other & j3_not;
        // j1 | j2
        j1 | j2
    }

    fn abs(self) -> Self {
        if self >= 0 {
            self
        } else {
            // -self mod 2^32
            self.wrapping_neg()
        }
    }

    fn neg(self) -> Self {
        // (2^32 - i) mod 2^32
        self.wrapping_neg()
    }

    fn min_u(self, other: Self) -> Self {
        if (self as u32) < (other as u32) {
            self
        } else {
            other
        }
    }

    fn min_s(self, other: Self) -> Self {
        if self < other {
            self
        } else {
            other
        }
    }

    fn add_sat_u(self, other: Self) -> Self {
        let result = (self as u32).wrapping_add(other as u32);
        if result > u32::MAX as u32 {
            u32::MAX as i32
        } else {
            result as i32
        }
    }

    fn add_sat_s(self, other: Self) -> Self {
        self.saturating_add(other)
    }

    fn sub_sat_u(self, other: Self) -> Self {
        let result = (self as u32).wrapping_sub(other as u32);
        if result > self as u32 {
            0
        } else {
            result as i32
        }
    }

    fn sub_sat_s(self, other: Self) -> Self {
        self.saturating_sub(other)
    }

    fn avgr_u(self, other: Self) -> Self {
        // (i1 + i2 + 1) / 2, truncated toward zero
        ((self as u32).wrapping_add(other as u32).wrapping_add(1) / 2) as i32
    }

    fn q15mulrsat_s(self, other: Self) -> Self {
        // sat_s((i1 * i2 + 2^14) >> 15)
        let product = (self as i64).wrapping_mul(other as i64);
        let rounded = product.wrapping_add(1 << 14);
        let shifted = rounded >> 15;
        if shifted > i32::MAX as i64 {
            i32::MAX
        } else if shifted < i32::MIN as i64 {
            i32::MIN
        } else {
            shifted as i32
        }
    }

    fn extend_u<M: IntOps + TryFrom<u64>>(self) -> M 
    where
        <M as TryFrom<u64>>::Error: fmt::Debug
    {
        // For unsigned extension, we just reinterpret the same value
        // Convert to unsigned first, then extend
        M::try_from(self as u32 as u64).unwrap_or_else(|_| {
            // If the conversion fails, wrap the value to the target type's bit width
            let max = M::WIDTH.max_unsigned();
            M::try_from((self as u32 as u64) & max).unwrap()
        })
    }

    fn wrap<M: IntOps + From<u64>>(self) -> M {
        // For signed types, first convert to unsigned, then wrap
        let mask = M::WIDTH.max_unsigned();
        let unsigned = self as u32 as u64;
        M::from(unsigned & mask)
    }

    fn convert_u<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Convert to target type
        if M::WIDTH == BitWidth::W32 {
            M::from(self as f32)  // float_32(i)
        } else {
            M::from(self as f64)  // float_64(i)
        }
    }

    fn convert_s<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // For signed types, directly convert to float
        M::from(self as f32)
    }

    fn narrow_s<M: IntOps + From<i64>>(self) -> M {
        // For signed types, directly apply saturation
        let saturated = if self > i32::MAX as i32 {
            i32::MAX
        } else if self < i32::MIN as i32 {
            i32::MIN
        } else {
            self
        };
        M::from(saturated as i64)
    }

    fn narrow_u<M: IntOps + From<u64>>(self) -> M {
        // For signed types, interpret as signed, then apply unsigned saturation
        let saturated = if self < 0 {
            0u32
        } else if self > u32::MAX as i32 {
            u32::MAX
        } else {
            self as u32
        };
        M::from(saturated as u64)
    }
}

// Implementation for i64
impl IntOps for i64 {
    const WIDTH: BitWidth = BitWidth::W64;

    fn clz(self) -> Self {
        if self == 0 {
            64
        } else {
            self.leading_zeros() as i64
        }
    }

    fn ctz(self) -> Self {
        if self == 0 {
            64
        } else {
            self.trailing_zeros() as i64
        }
    }

    fn popcnt(self) -> Self {
        self.count_ones() as i64
    }

    fn eqz(self) -> Self {
        if self == 0 { 1 } else { 0 }
    }

    fn eq(self, other: Self) -> Self {
        if self == other { 1 } else { 0 }
    }

    fn ne(self, other: Self) -> Self {
        if self != other { 1 } else { 0 }
    }

    fn lt_u(self, other: Self) -> Self {
        if (self as u64) < (other as u64) { 1 } else { 0 }
    }

    fn lt_s(self, other: Self) -> Self {
        if self < other { 1 } else { 0 }
    }

    fn extend_s<M: IntOps + TryFrom<i64>>(self) -> M 
    where
        <M as TryFrom<i64>>::Error: fmt::Debug
    {
        // Already signed, just convert to target type's two's complement
        M::try_from(self).unwrap_or_else(|_| {
            // If the conversion fails, wrap the value to the target type's bit width
            let min = M::WIDTH.min_signed();
            let max = M::WIDTH.max_signed();
            let mask = max - min + 1;
            M::try_from((self & mask) + min).unwrap()
        })
    }

    fn bitselect(self, other: Self, mask: Self) -> Self {
        // j1 = i1 & i3
        let j1 = self & mask;
        // j3' = !i3
        let j3_not = !mask;
        // j2 = i2 & j3'
        let j2 = other & j3_not;
        // j1 | j2
        j1 | j2
    }

    fn abs(self) -> Self {
        if self >= 0 {
            self
        } else {
            // -self mod 2^64
            self.wrapping_neg()
        }
    }

    fn neg(self) -> Self {
        // (2^64 - i) mod 2^64
        self.wrapping_neg()
    }

    fn min_u(self, other: Self) -> Self {
        if (self as u64) < (other as u64) {
            self
        } else {
            other
        }
    }

    fn min_s(self, other: Self) -> Self {
        if self < other {
            self
        } else {
            other
        }
    }

    fn add_sat_u(self, other: Self) -> Self {
        let result = (self as u64).wrapping_add(other as u64);
        if result > u64::MAX as u64 {
            u64::MAX as i64
        } else {
            result as i64
        }
    }

    fn add_sat_s(self, other: Self) -> Self {
        self.saturating_add(other)
    }

    fn sub_sat_u(self, other: Self) -> Self {
        let result = (self as u64).wrapping_sub(other as u64);
        if result > self as u64 {
            0
        } else {
            result as i64
        }
    }

    fn sub_sat_s(self, other: Self) -> Self {
        self.saturating_sub(other)
    }

    fn avgr_u(self, other: Self) -> Self {
        // (i1 + i2 + 1) / 2, truncated toward zero
        ((self as u64).wrapping_add(other as u64).wrapping_add(1) / 2) as i64
    }

    fn q15mulrsat_s(self, other: Self) -> Self {
        // For i64, we need to handle the intermediate calculation carefully
        // to avoid overflow in the multiplication
        let half = (other >> 1) as i64;  // Divide by 2 to avoid overflow
        let product = self.wrapping_mul(half);
        let rounded = product.wrapping_add(1 << 13);  // 2^14/2
        let shifted = rounded >> 14;  // 15-1
        if shifted > i64::MAX {
            i64::MAX
        } else if shifted < i64::MIN {
            i64::MIN
        } else {
            shifted
        }
    }

    fn extend_u<M: IntOps + TryFrom<u64>>(self) -> M 
    where
        <M as TryFrom<u64>>::Error: fmt::Debug
    {
        // For unsigned extension, we just reinterpret the same value
        // Convert to unsigned first, then extend
        M::try_from(self as u64).unwrap_or_else(|_| {
            // If the conversion fails, wrap the value to the target type's bit width
            let max = M::WIDTH.max_unsigned();
            M::try_from((self as u64) & max).unwrap()
        })
    }

    fn wrap<M: IntOps + From<u64>>(self) -> M {
        // For signed types, first convert to unsigned, then wrap
        let mask = M::WIDTH.max_unsigned();
        let unsigned = self as u64;  // This preserves the bit pattern
        M::from(unsigned & mask)
    }

    fn convert_u<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Convert to target type
        if M::WIDTH == BitWidth::W32 {
            // For f32, we need to handle potential precision loss
            if self > (u32::MAX as u64).try_into().unwrap() {
                // If the value is too large for f32, return infinity
                M::from(f32::INFINITY)
            } else {
                M::from(self as f32)  // float_32(i)
            }
        } else {
            M::from(self as f64)  // float_64(i)
        }
    }

    fn convert_s<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // For signed types, directly convert to float
        M::from(self as f64)
    }

    fn narrow_s<M: IntOps + From<i64>>(self) -> M {
        // For signed types, directly apply saturation
        let saturated = if self > i64::MAX as i64 {
            i64::MAX
        } else if self < i64::MIN as i64 {
            i64::MIN
        } else {
            self
        };
        M::from(saturated)
    }

    fn narrow_u<M: IntOps + From<u64>>(self) -> M {
        // For signed types, interpret as signed, then apply unsigned saturation
        let saturated = if self < 0 {
            0u64
        } else if self > u64::MAX as i64 {
            u64::MAX
        } else {
            self as u64
        };
        M::from(saturated)
    }
}

// Implementation for u32
impl IntOps for u32 {
    const WIDTH: BitWidth = BitWidth::W32;

    fn clz(self) -> Self {
        if self == 0 {
            32
        } else {
            self.leading_zeros()
        }
    }

    fn ctz(self) -> Self {
        if self == 0 {
            32
        } else {
            self.trailing_zeros()
        }
    }

    fn popcnt(self) -> Self {
        self.count_ones()
    }

    fn eqz(self) -> Self {
        if self == 0 { 1 } else { 0 }
    }

    fn eq(self, other: Self) -> Self {
        if self == other { 1 } else { 0 }
    }

    fn ne(self, other: Self) -> Self {
        if self != other { 1 } else { 0 }
    }

    fn lt_u(self, other: Self) -> Self {
        if self < other { 1 } else { 0 }
    }

    fn lt_s(self, other: Self) -> Self {
        if (self as i32) < (other as i32) { 1 } else { 0 }
    }

    fn extend_s<M: IntOps + TryFrom<i64>>(self) -> M 
    where
        <M as TryFrom<i64>>::Error: fmt::Debug
    {
        // First interpret as signed i32
        let signed = self as i32;
        // Then convert to target type's two's complement
        M::try_from(signed as i64).unwrap_or_else(|_| {
            // If the conversion fails, wrap the value to the target type's bit width
            let min = M::WIDTH.min_signed();
            let max = M::WIDTH.max_signed();
            let mask = max - min + 1;
            M::try_from((signed as i64 & mask) + min).unwrap()
        })
    }

    fn bitselect(self, other: Self, mask: Self) -> Self {
        // j1 = i1 & i3
        let j1 = self & mask;
        // j3' = !i3
        let j3_not = !mask;
        // j2 = i2 & j3'
        let j2 = other & j3_not;
        // j1 | j2
        j1 | j2
    }

    fn abs(self) -> Self {
        // For unsigned types, abs is the identity function
        self
    }

    fn neg(self) -> Self {
        // (2^32 - i) mod 2^32
        self.wrapping_neg()
    }

    fn min_u(self, other: Self) -> Self {
        if self < other {
            self
        } else {
            other
        }
    }

    fn min_s(self, other: Self) -> Self {
        if (self as i32) < (other as i32) {
            self
        } else {
            other
        }
    }

    fn add_sat_u(self, other: Self) -> Self {
        self.saturating_add(other)
    }

    fn add_sat_s(self, other: Self) -> Self {
        let result = (self as i32).saturating_add(other as i32);
        if result > i32::MAX {
            i32::MAX as u32
        } else if result < i32::MIN {
            i32::MIN as u32
        } else {
            result as u32
        }
    }

    fn sub_sat_u(self, other: Self) -> Self {
        self.saturating_sub(other)
    }

    fn sub_sat_s(self, other: Self) -> Self {
        let result = (self as i32).saturating_sub(other as i32);
        if result > i32::MAX {
            i32::MAX as u32
        } else if result < i32::MIN {
            i32::MIN as u32
        } else {
            result as u32
        }
    }

    fn avgr_u(self, other: Self) -> Self {
        // (i1 + i2 + 1) / 2, truncated toward zero
        self.wrapping_add(other).wrapping_add(1) / 2
    }

    fn q15mulrsat_s(self, other: Self) -> Self {
        // Convert to signed, perform operation, then convert back
        let signed_result = (self as i32).q15mulrsat_s(other as i32);
        if signed_result > (i32::MAX as u32).try_into().unwrap() {
            i32::MAX as u32
        } else if signed_result < (i32::MIN as u32).try_into().unwrap() {
            i32::MIN as u32
        } else {
            signed_result as u32
        }
    }

    fn extend_u<M: IntOps + TryFrom<u64>>(self) -> M 
    where
        <M as TryFrom<u64>>::Error: fmt::Debug
    {
        // For unsigned extension, we just reinterpret the same value
        // This is a no-op for unsigned types
        M::try_from(self as u64).unwrap_or_else(|_| {
            // If the conversion fails, wrap the value to the target type's bit width
            let max = M::WIDTH.max_unsigned();
            M::try_from(self as u64 & max).unwrap()
        })
    }

    fn wrap<M: IntOps + From<u64>>(self) -> M {
        // Calculate modulo 2^N where N is the bit width of M
        let mask = M::WIDTH.max_unsigned();
        M::from(self as u64 & mask)
    }

    fn convert_u<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Convert to target type
        if M::WIDTH == BitWidth::W32 {
            M::from(self as f32)  // float_32(i)
        } else {
            M::from(self as f64)  // float_64(i)
        }
    }

    fn convert_s<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // For unsigned types, first interpret as signed, then convert to float
        M::from(self as i32 as f32)
    }

    fn narrow_s<M: IntOps + From<i64>>(self) -> M {
        // For unsigned types, first interpret as signed, then apply saturation
        let signed = self as i32;
        let saturated = if signed > i32::MAX as i32 {
            i32::MAX
        } else if signed < i32::MIN as i32 {
            i32::MIN
        } else {
            signed
        };
        M::from(saturated as i64)
    }

    fn narrow_u<M: IntOps + From<u64>>(self) -> M {
        // For unsigned types, first interpret as signed, then apply unsigned saturation
        let signed = self as i32;
        let saturated = if signed < 0 {
            0u32
        } else if signed > u32::MAX as i32 {
            u32::MAX
        } else {
            signed as u32
        };
        M::from(saturated as u64)
    }
}

// Implementation for u64
impl IntOps for u64 {
    const WIDTH: BitWidth = BitWidth::W64;

    fn clz(self) -> Self {
        if self == 0 {
            64
        } else {
            self.leading_zeros().into()
        }
    }

    fn ctz(self) -> Self {
        if self == 0 {
            64
        } else {
            self.trailing_zeros().into()
        }
    }

    fn popcnt(self) -> Self {
        self.count_ones().into()
    }

    fn eqz(self) -> Self {
        if self == 0 { 1 } else { 0 }
    }

    fn eq(self, other: Self) -> Self {
        if self == other { 1 } else { 0 }
    }

    fn ne(self, other: Self) -> Self {
        if self != other { 1 } else { 0 }
    }

    fn lt_u(self, other: Self) -> Self {
        if self < other { 1 } else { 0 }
    }

    fn lt_s(self, other: Self) -> Self {
        if (self as i64) < (other as i64) { 1 } else { 0 }
    }

    fn extend_s<M: IntOps + TryFrom<i64>>(self) -> M 
    where
        <M as TryFrom<i64>>::Error: fmt::Debug
    {
        // First interpret as signed i64
        let signed = self as i64;
        // Then convert to target type's two's complement
        M::try_from(signed).unwrap_or_else(|_| {
            // If the conversion fails, wrap the value to the target type's bit width
            let min = M::WIDTH.min_signed();
            let max = M::WIDTH.max_signed();
            let mask = max - min + 1;
            M::try_from((signed & mask) + min).unwrap()
        })
    }

    fn bitselect(self, other: Self, mask: Self) -> Self {
        // j1 = i1 & i3
        let j1 = self & mask;
        // j3' = !i3
        let j3_not = !mask;
        // j2 = i2 & j3'
        let j2 = other & j3_not;
        // j1 | j2
        j1 | j2
    }

    fn abs(self) -> Self {
        // For unsigned types, abs is the identity function
        self
    }

    fn neg(self) -> Self {
        // (2^64 - i) mod 2^64
        self.wrapping_neg()
    }

    fn min_u(self, other: Self) -> Self {
        if self < other {
            self
        } else {
            other
        }
    }

    fn min_s(self, other: Self) -> Self {
        if (self as i64) < (other as i64) {
            self
        } else {
            other
        }
    }

    fn add_sat_u(self, other: Self) -> Self {
        self.saturating_add(other)
    }

    fn add_sat_s(self, other: Self) -> Self {
        let result = (self as i64).saturating_add(other as i64);
        if result > i64::MAX {
            i64::MAX as u64
        } else if result < i64::MIN {
            i64::MIN as u64
        } else {
            result as u64
        }
    }

    fn sub_sat_u(self, other: Self) -> Self {
        self.saturating_sub(other)
    }

    fn sub_sat_s(self, other: Self) -> Self {
        let result = (self as i64).saturating_sub(other as i64);
        if result > i64::MAX {
            i64::MAX as u64
        } else if result < i64::MIN {
            i64::MIN as u64
        } else {
            result as u64
        }
    }

    fn avgr_u(self, other: Self) -> Self {
        // (i1 + i2 + 1) / 2, truncated toward zero
        self.wrapping_add(other).wrapping_add(1) / 2
    }

    fn q15mulrsat_s(self, other: Self) -> Self {
        // Convert to signed, perform operation, then convert back
        let signed_result = (self as i64).q15mulrsat_s(other as i64);
        if signed_result > (i64::MAX as u64).try_into().unwrap() {
            i64::MAX as u64
        } else if signed_result < (i64::MIN as u64).try_into().unwrap() {
            i64::MIN as u64
        } else {
            signed_result as u64
        }
    }

    fn extend_u<M: IntOps + TryFrom<u64>>(self) -> M 
    where
        <M as TryFrom<u64>>::Error: fmt::Debug
    {
        // For unsigned extension, we just reinterpret the same value
        // This is a no-op for unsigned types
        M::try_from(self).unwrap_or_else(|_| {
            // If the conversion fails, wrap the value to the target type's bit width
            let max = M::WIDTH.max_unsigned();
            M::try_from(self & max).unwrap()
        })
    }

    fn wrap<M: IntOps + From<u64>>(self) -> M {
        // Calculate modulo 2^N where N is the bit width of M
        let mask = M::WIDTH.max_unsigned();
        M::from(self & mask)
    }

    fn convert_u<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // Convert to target type
        if M::WIDTH == BitWidth::W32 {
            // For f32, we need to handle potential precision loss
            if self > u32::MAX as u64 {
                // If the value is too large for f32, return infinity
                M::from(f32::INFINITY)
            } else {
                M::from(self as f32)  // float_32(i)
            }
        } else {
            M::from(self as f64)  // float_64(i)
        }
    }

    fn convert_s<M: FloatOps + From<f32> + From<f64>>(self) -> M {
        // For unsigned types, first interpret as signed, then convert to float
        M::from(self as i64 as f64)
    }

    fn narrow_s<M: IntOps + From<i64>>(self) -> M {
        // For unsigned types, first interpret as signed, then apply saturation
        let signed = self as i64;
        let saturated = if signed > i64::MAX as i64 {
            i64::MAX
        } else if signed < i64::MIN as i64 {
            i64::MIN
        } else {
            signed
        };
        M::from(saturated)
    }

    fn narrow_u<M: IntOps + From<u64>>(self) -> M {
        // For unsigned types, first interpret as signed, then apply unsigned saturation
        let signed = self as i64;
        let saturated = if signed < 0 {
            0u64
        } else if signed > u64::MAX as i64 {
            u64::MAX
        } else {
            signed as u64
        };
        M::from(saturated)
    }
} 