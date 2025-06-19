use alloc::vec::Vec;
use alloc::string::String;
use alloc::format;
use core::fmt;

/// Data instance represents a runtime data segment
/// 
/// # Specification
/// A data instance is the runtime representation of a data segment.
/// It holds a vector of bytes.
/// 
/// datainst ::= {data vec(byte)}
#[derive(Debug, Clone)]
pub struct DataInstance {
    /// The vector of bytes
    data: Vec<u8>,
}

impl DataInstance {
    /// Creates a new empty data instance
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
        }
    }

    /// Creates a new data instance with initial data
    /// 
    /// # Arguments
    /// * `data` - The initial vector of bytes
    pub fn with_data(data: Vec<u8>) -> Self {
        Self { data }
    }

    /// Returns the number of bytes in this instance
    pub fn size(&self) -> usize {
        self.data.len()
    }

    /// Returns true if this data instance is empty
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Returns a reference to the byte at the given index
    /// 
    /// # Arguments
    /// * `index` - The index of the byte to get
    /// 
    /// # Returns
    /// Some reference to the byte if the index is valid, None otherwise
    pub fn get(&self, index: usize) -> Option<&u8> {
        self.data.get(index)
    }

    /// Returns a mutable reference to the byte at the given index
    /// 
    /// # Arguments
    /// * `index` - The index of the byte to get
    /// 
    /// # Returns
    /// Some mutable reference to the byte if the index is valid, None otherwise
    pub fn get_mut(&mut self, index: usize) -> Option<&mut u8> {
        self.data.get_mut(index)
    }

    /// Sets the byte at the given index
    /// 
    /// # Arguments
    /// * `index` - The index of the byte to set
    /// * `value` - The new value for the byte
    /// 
    /// # Returns
    /// Ok(()) if successful, Err if the index is invalid
    pub fn set(&mut self, index: usize, value: u8) -> Result<(), String> {
        if index >= self.data.len() {
            return Err(format!("Data index {} out of bounds", index));
        }

        self.data[index] = value;
        Ok(())
    }

    /// Appends a byte to this instance
    /// 
    /// # Arguments
    /// * `value` - The byte to append
    pub fn push(&mut self, value: u8) {
        self.data.push(value);
    }

    /// Appends a slice of bytes to this instance
    /// 
    /// # Arguments
    /// * `values` - The bytes to append
    pub fn extend_from_slice(&mut self, values: &[u8]) {
        self.data.extend_from_slice(values);
    }

    /// Returns a slice of the data
    /// 
    /// # Arguments
    /// * `start` - The start index (inclusive)
    /// * `end` - The end index (exclusive)
    /// 
    /// # Returns
    /// Some slice of the data if the indices are valid, None otherwise
    pub fn slice(&self, start: usize, end: usize) -> Option<&[u8]> {
        if start > end || end > self.data.len() {
            return None;
        }
        Some(&self.data[start..end])
    }

    /// Returns a mutable slice of the data
    /// 
    /// # Arguments
    /// * `start` - The start index (inclusive)
    /// * `end` - The end index (exclusive)
    /// 
    /// # Returns
    /// Some mutable slice of the data if the indices are valid, None otherwise
    pub fn slice_mut(&mut self, start: usize, end: usize) -> Option<&mut [u8]> {
        if start > end || end > self.data.len() {
            return None;
        }
        Some(&mut self.data[start..end])
    }

    /// Returns an iterator over the bytes
    pub fn bytes(&self) -> impl Iterator<Item = &u8> {
        self.data.iter()
    }

    /// Returns a mutable iterator over the bytes
    pub fn bytes_mut(&mut self) -> impl Iterator<Item = &mut u8> {
        self.data.iter_mut()
    }

    /// Returns a reference to the underlying byte vector
    pub fn as_bytes(&self) -> &[u8] {
        &self.data
    }

    /// Returns a mutable reference to the underlying byte vector
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }

    /// Clears all bytes from this instance
    pub fn clear(&mut self) {
        self.data.clear();
    }
}

impl fmt::Display for DataInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{data: [")?;
        for (i, byte) in self.data.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:02x}", byte)?;
        }
        write!(f, "]}}")
    }
}
