#![cfg_attr(not(feature = "std"), no_std)]
#![doc = include_str!("../README.md")]
#![warn(missing_docs, missing_debug_implementations)]

extern crate alloc;
use alloc::{borrow::Cow, boxed::Box, string::*, vec::Vec};
mod string;
use core::fmt::{Debug, Display};

use hashbrown::HashMap;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
pub use string::*;

#[derive(Debug, Clone)]
/// A map of string keys to dynamically typed values.
///
/// `Map` is a wrapper around a `HashMap<String, Value>` that provides a
/// convenient way to store and access heterogeneous data with string keys.
///
/// # Examples
///
/// ```
/// use anyval::Map;
///
/// let mut m = Map::new();
/// m["key"] = (10.0).into();
/// m["key2"] = "string value".into();
///
/// // or using map! macro
/// use anyval::map;
/// let m2 = map! {
///    "key" => 10.0,
///   "key2" => "string value",
/// };
/// ```
pub struct Map {
    inner: Box<HashMap<String, Value>>,
}

impl Map {
    /// Creates an empty `Map`.
    ///
    /// The map is initially created with a capacity of 0, so it will not
    /// allocate until it is first inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Map;
    ///
    /// let mut map = Map::new();
    /// ```
    pub fn new() -> Self {
        Self {
            inner: Box::new(HashMap::default()),
        }
    }
    /// Creates an empty `Map` with at least the specified capacity.
    ///
    /// The map will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is 0, the map will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Map;
    ///
    /// let mut map = Map::with_capacity(10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        let mut inner = HashMap::default();
        inner.reserve(capacity);
        Self {
            inner: Box::new(inner),
        }
    }

    #[cfg(all(feature = "json"))]
    /// Deserialises a JSON string into a `Map`.
    ///
    /// Returns a `serde_json::Error` if the JSON cannot be parsed or does not
    /// represent a valid map structure.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Map;
    ///
    /// let json = r#"{"key":"value","num":42}"#;
    /// let map = Map::from_json(json).unwrap();
    /// assert_eq!(map["key"].as_str(), "value");
    /// assert_eq!(map["num"].as_int(), 42);
    /// ```
    pub fn from_json(s: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(s)
    }

    /// Serialises the map to a JSON string.
    ///
    /// Returns a `serde_json::Error` if the map cannot be serialised.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Map;
    ///
    /// let mut map = Map::new();
    /// map["key"] = "value".into();
    /// let json = map.to_json().unwrap();
    /// assert_eq!(json, r#"{"key":"value"}"#);
    /// ```
    ///
    /// # Nested example
    ///
    /// ```
    /// use anyval::{Map, Value};
    ///
    /// let mut map = Map::new();
    /// let mut nested = Map::new();
    /// nested["inner"] = "value".into();
    /// map["outer"] = Value::Map(nested);
    /// let json = map.to_json().unwrap();
    /// assert!(json.contains("outer"));
    /// assert!(json.contains("inner"));
    /// ```
    #[cfg(all(feature = "json"))]
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(&self)
    }

    /// Serialises the map to a JSON writer.
    ///
    /// Returns a `serde_json::Error` if the map cannot be serialised.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Map;
    ///
    /// let mut map = Map::new();
    /// map["key"] = "value".into();
    /// let mut buffer = Vec::new();
    /// map.to_json_writer(&mut buffer).unwrap();
    /// assert_eq!(String::from_utf8(buffer).unwrap(), r#"{"key":"value"}"#);
    /// ```
    #[cfg(all(feature = "json"))]
    pub fn to_json_writer<W: std::io::Write>(&self, writer: W) -> Result<(), serde_json::Error> {
        serde_json::to_writer(writer, &self)
    }
}

impl core::ops::Index<&str> for Map {
    type Output = Value;

    fn index(&self, index: &str) -> &Self::Output {
        &self.inner[index]
    }
}

impl core::ops::IndexMut<&str> for Map {
    fn index_mut(&mut self, index: &str) -> &mut Self::Output {
        self.inner
            .entry(index.to_string())
            .or_insert(Value::from(""))
    }
}

impl core::ops::Deref for Map {
    type Target = HashMap<String, Value>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl core::ops::DerefMut for Map {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl Default for Map {
    fn default() -> Self {
        Self::new()
    }
}
/// A dynamically‑sized array that stores [`Value`] instances.
///
/// This type is a thin wrapper around `Vec<Value>` that provides a stable
/// API for the rest of the crate. It implements `Debug` and `Clone` by
/// delegating to the inner `Vec`.
///
/// # Examples
///
/// ```
/// use anyval::{Array, Value};
///
/// let mut arr = Array::new();
/// assert!(arr.is_empty());
///
/// arr.push(("something").into());
/// assert!(!arr.is_empty());
///
/// // or using array macro
/// use anyval::array;
/// let arr2 = array!["value", 42, true];
/// assert!(arr2[0].is_string());
/// ```
#[derive(Debug, Clone)]
pub struct Array {
    inner: Box<Vec<Value>>,
}

impl Array {
    /// Creates a new, empty `Array`.
    ///
    /// The returned array does not allocate any memory until elements are
    /// pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Array;
    ///
    /// let mut arr = Array::new();
    /// assert!(arr.is_empty());
    /// arr.push((10).into());
    /// assert_eq!(arr.len(), 1);
    /// ```
    pub fn new() -> Self {
        Self {
            inner: Box::new(Vec::new()),
        }
    }

    /// Creates an empty `Array` with at least the specified capacity.
    ///
    /// The array will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, no allocation occurs.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Array;
    ///
    /// let mut arr = Array::with_capacity(10);
    /// assert_eq!(arr.capacity(), 10);
    /// assert!(arr.is_empty());
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Box::new(Vec::with_capacity(capacity)),
        }
    }

    #[cfg(all(feature = "json"))]
    /// Deserialises a JSON string into an `Array`.
    ///
    /// Returns a `serde_json::Error` if the JSON cannot be parsed or does not
    /// represent a valid array structure.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Array;
    ///
    /// let json = r#"["value",42,true]"#;
    /// let arr = Array::from_json(json).unwrap();
    /// assert_eq!(arr[0].as_str(), "value");
    /// assert_eq!(arr[1].as_int(), 42);
    /// assert_eq!(arr[2].as_bool(), true);
    /// ```
    ///
    /// # Nested example
    ///
    /// ```
    /// use anyval::{Array, Value, Map};
    ///
    /// let json = r#"[{"key":"value"},42]"#;
    /// let arr = Array::from_json(json).unwrap();
    /// assert_eq!(arr[0].as_map().unwrap()["key"].as_str(), "value");
    /// assert_eq!(arr[1].as_int(), 42);
    /// ```
    pub fn from_json(s: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(s)
    }

    /// Serialises the array to a JSON string.
    ///
    /// Returns a `serde_json::Error` if the array cannot be serialised.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Array;
    ///
    /// let mut arr = Array::new();
    /// arr.push("value".into());
    /// arr.push(42.into());
    /// let json = arr.to_json().unwrap();
    /// assert_eq!(json, r#"["value",42]"#);
    /// ```
    #[cfg(all(feature = "json"))]
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(&self)
    }

    /// Serialises the array to a JSON writer.
    ///
    /// Returns a `serde_json::Error` if the array cannot be serialised.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Array;
    ///
    /// let mut arr = Array::new();
    /// arr.push("value".into());
    /// arr.push(42.into());
    /// let mut buffer = Vec::new();
    /// arr.to_json_writer(&mut buffer).unwrap();
    /// assert_eq!(String::from_utf8(buffer).unwrap(), r#"["value",42]"#);
    /// ```
    #[cfg(all(feature = "json", feature = "std"))]
    pub fn to_json_writer<W: std::io::Write>(&self, writer: W) -> Result<(), serde_json::Error> {
        serde_json::to_writer(writer, &self)
    }
}

impl core::ops::Deref for Array {
    type Target = Vec<Value>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl core::ops::DerefMut for Array {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl Default for Array {
    fn default() -> Self {
        Self::new()
    }
}

/// A dynamically‑typed value used throughout the library.
///
/// This enum can represent the primitive scalar types supported by the
/// library as well as compound collection types. It is deliberately
/// exhaustive so that a `Value` can be stored in heterogeneous containers
/// (e.g., maps or arrays) without losing type information.
///
/// # Variants
///
/// * **`Float(f64)`** – A 64‑bit floating‑point number. Mirrors the behaviour
///   of `f64` in the Rust standard library, including `NaN` and `Infinity`
///   handling.
///
/// * **`Int(i64)`** – A signed 64‑bit integer. Provides the full range of `i64`
///   values.
///
/// * **`Bool(bool)`** – A boolean value, either `true` or `false`.
///
/// * **`String(Str)`** – A string value that may be a static slice, an
///   `Arc<String>`, or an owned `String`. See [`Str`] for details.
///
/// * **`Map(Map)`** – An associative container mapping string keys to `Value`s.
///   See [`Map`] for the underlying implementation.
///
/// * **`Array(Array)`** – An ordered list of `Value`s. See [`Array`] for the
///   underlying implementation.
///
/// # Examples
///
/// ```rust
/// # use anyval::Value;
///
/// let v = Value::from(3.14);
/// assert!(matches!(v, Value::Float(_)));
///
/// let s = Value::from("hello");
/// assert_eq!(s.as_str(), "hello");
/// assert_eq!(v.as_str(), "3.14");
/// ```
pub enum Value {
    /// 64‑bit floating‑point number.
    Float(f64),

    /// 64‑bit signed integer.
    Int(i64),

    /// Boolean value.
    Bool(bool),

    /// String value, using the library's flexible `Str` type.
    String(Str),

    /// Map (dictionary) of string keys to `Value`s.
    Map(Map),

    /// Array (list) of `Value`s.
    Array(Array),

    /// None value
    None,
}

/// A borrowed reference to a `Value`.
///
/// This enum provides read‑only access to the data stored inside a `Value`
/// without taking ownership. It mirrors the variants of `Value` but holds
/// references (`&'a …`) to the underlying data, allowing inspection while
/// preserving the original lifetime.
///
/// # Variants
///
/// * **`Float(&'a f64)`** – Reference to a 64‑bit floating‑point number.
/// * **`Int(&'a i64)`** – Reference to a signed 64‑bit integer.
/// * **`Bool(&'a bool)`** – Reference to a boolean value.
/// * **`String(&'a Str)`** – Reference to a string (`Str`) value.
/// * **`Map(&'a Map)`** – Reference to a map container.
/// * **`Array(&'a Array)`** – Reference to an array container.
/// * **`None`** – Represents the absence of a value.
#[derive(Debug)]
pub enum ValueRef<'a> {
    /// Reference to a floating‑point number.
    Float(&'a f64),
    /// Reference to an integer.
    Int(&'a i64),
    /// Reference to a boolean.
    Bool(&'a bool),
    /// Reference to a string.
    String(&'a Str),
    /// Reference to a map.
    Map(&'a Map),
    /// Reference to an array.
    Array(&'a Array),
    /// No value.
    None,
}

/// A mutable borrowed reference to a `Value`.
///
/// This enum provides write‑access to the data stored inside a `Value`
/// via mutable references (`&'a mut …`). It mirrors the variants of
/// `Value` but allows the underlying data to be modified in place.
///
/// # Variants
///
/// * **`Float(&'a mut f64)`** – Mutable reference to a floating‑point number.
/// * **`Int(&'a mut i64)`** – Mutable reference to an integer.
/// * **`Bool(&'a mut bool)`** – Mutable reference to a boolean.
/// * **`String(&'a mut Str)`** – Mutable reference to a string.
/// * **`Map(&'a mut Map)`** – Mutable reference to a map container.
/// * **`Array(&'a mut Array)`** – Mutable reference to an array container.
/// * **`None`** – Represents the absence of a value.
#[derive(Debug)]
pub enum ValueRefMut<'a> {
    /// Mutable reference to a floating‑point number.
    Float(&'a mut f64),
    /// Mutable reference to an integer.
    Int(&'a mut i64),
    /// Mutable reference to a boolean.
    Bool(&'a mut bool),
    /// Mutable reference to a string.
    String(&'a mut Str),
    /// Mutable reference to a map.
    Map(&'a mut Map),
    /// Mutable reference to an array.
    Array(&'a mut Array),
    /// No value.
    None,
}

impl Display for Value {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Value::String(s) => write!(f, "{}", s),
            Value::Float(fl) => write!(f, "{}", fl),
            Value::Int(i) => write!(f, "{}", i),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Map(_) => write!(f, "[object Map]"),
            Value::Array(_) => write!(f, "[object Array]"),
            Value::None => write!(f, "null"),
        }
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Value::String(s) => write!(f, "{:?}", s),
            Value::Float(fl) => write!(f, "Value::Float({:?})", fl),
            Value::Int(i) => write!(f, "Value::Int({:?})", i),
            Value::Bool(b) => write!(f, "Value::Bool({:?})", b),
            Value::Map(m) => write!(f, "Value::Map({:?})", m),
            Value::Array(a) => write!(f, "Value::Array({:?})", a),
            Value::None => write!(f, "Value::None"),
        }
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        match self {
            Value::String(s) => Value::String(s.clone()),
            Value::Float(fl) => Value::Float(*fl),
            Value::Int(i) => Value::Int(*i),
            Value::Bool(b) => Value::Bool(*b),
            Value::Map(m) => Value::Map(m.clone()),
            Value::Array(a) => Value::Array(a.clone()),
            Value::None => Value::None,
        }
    }
}
impl Value {
    /// Creates a `Value` from any type that implements `Into<Value>`.
    /// ///
    /// This is a convenience method that allows for easy conversion of
    /// common types into `Value` instances.
    ///
    /// # Examples
    ///
    /// ```
    /// # use anyval::Value;
    /// let v_float = Value::from(3.14);
    /// let v_int = Value::from(42);
    /// let v_bool = Value::from(true);
    /// let v_string = Value::from("hello");
    /// assert!(matches!(v_float, Value::Float(_)));
    /// assert!(matches!(v_int, Value::Int(_)));
    /// assert!(matches!(v_bool, Value::Bool(_)));
    /// assert!(matches!(v_string, Value::String(_)));
    /// ```
    pub fn from<T: Into<Value>>(value: T) -> Self {
        value.into()
    }

    /// Returns a string representation of the value.
    ///
    /// If the value is a `String`, a borrowed `&str` is returned.
    /// Otherwise the value is formatted with `to_string()` and an owned
    /// `String` is returned inside a `Cow::Owned`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use anyval::{Value, Str};
    /// let v = Value::String(Str::from_static("hello"));
    /// assert_eq!(v.as_str(), "hello");
    ///
    /// let v = Value::Int(42);
    /// assert_eq!(v.as_str(), "42");
    /// ```
    pub fn as_str(&self) -> Cow<'_, str> {
        match self {
            Value::String(s) => Cow::Borrowed(s.as_str()),
            _ => Cow::Owned(self.to_string()),
        }
    }

    /// Attempts to interpret the value as a 64‑bit floating‑point number.
    ///
    /// The conversion rules are:
    ///
    /// * `Float` – returns the contained `f64`.
    /// * `Int` – casts the integer to `f64`.
    /// * `String` – parses the string as `f64`; on parse failure `0.0` is
    ///   returned.
    /// * `Bool` – `true` becomes `1.0`, `false` becomes `0.0`.
    /// * Any other variant – returns `0.0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use anyval::Value;
    /// assert_eq!(Value::Float(3.14).as_float(), 3.14);
    /// assert_eq!(Value::Int(2).as_float(), 2.0);
    /// assert_eq!(Value::Bool(true).as_float(), 1.0);
    /// assert_eq!(Value::String("2.5".into()).as_float(), 2.5);
    /// ```
    pub fn as_float(&self) -> f64 {
        match self {
            Value::Float(f) => *f,
            Value::Int(i) => *i as f64,
            Value::String(str) => str.as_str().parse::<f64>().unwrap_or(0.0),
            Value::Bool(b) => {
                if *b {
                    1.0
                } else {
                    0.0
                }
            }
            _ => 0.0,
        }
    }

    /// Attempts to interpret the value as a signed 64‑bit integer.
    ///
    /// The conversion rules are:
    ///
    /// * `Int` – returns the contained integer.
    /// * `Float` – truncates the floating‑point value.
    /// * `String` – parses the string as `i64`; on parse failure `0` is
    ///   returned.
    /// * `Bool` – `true` becomes `1`, `false` becomes `0`.
    /// * Any other variant – returns `0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use anyval::Value;
    /// assert_eq!(Value::Int(7).as_int(), 7);
    /// assert_eq!(Value::Float(3.9).as_int(), 3);
    /// assert_eq!(Value::Bool(false).as_int(), 0);
    /// assert_eq!(Value::String("42".into()).as_int(), 42);
    /// ```
    pub fn as_int(&self) -> i64 {
        match self {
            Value::Int(i) => *i,
            Value::Float(f) => *f as i64,
            Value::String(str) => str.as_str().parse::<i64>().unwrap_or(0),
            Value::Bool(b) => {
                if *b {
                    1
                } else {
                    0
                }
            }
            _ => 0,
        }
    }

    /// Returns the boolean representation of the value.
    ///
    /// Conversion rules:
    ///
    /// * `Bool` – returns the contained boolean.
    /// * `Int` – `0` is `false`, any other integer is `true`.
    /// * `Float` – `0.0` is `false`, any other number is `true`.
    /// * `String` – empty string is `false`, otherwise `true`.
    /// * `Map` / `Array` – empty collections are `false`, otherwise `true`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use anyval::{Value, Map, Array};
    /// assert!(Value::Bool(true).as_bool());
    /// assert!(!Value::Int(0).as_bool());
    /// assert!(Value::String("text".into()).as_bool());
    /// ```
    pub fn as_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            Value::Float(f) => *f != 0.0,
            Value::String(s) => !s.as_str().is_empty(),
            Value::Map(m) => !m.is_empty(),
            Value::Array(a) => !a.is_empty(),
            Value::None => false,
        }
    }

    /// Returns a reference to the underlying map if the value is a `Map`.
    ///
    /// # Returns
    ///
    /// * `Some(&Map)` – when the variant is `Value::Map`.
    /// * `None` – for all other variants.
    ///
    /// # Examples
    ///
    /// ```
    /// # use anyval::{Value, Map};
    /// let map = Map::new();
    /// let v = Value::Map(map);
    /// assert!(v.as_map().is_some());
    /// ```
    pub fn as_map(&self) -> Option<&Map> {
        match self {
            Value::Map(m) => Some(m),
            _ => None,
        }
    }

    /// Returns a reference to the underlying array if the value is an `Array`.
    ///
    /// # Returns
    ///
    /// * `Some(&Array)` – when the variant is `Value::Array`.
    /// * `None` – for all other variants.
    ///
    /// # Examples
    ///
    /// ```
    /// # use anyval::{Value, Array};
    /// let arr = Array::new();
    /// let v = Value::Array(arr);
    /// assert!(v.as_array().is_some());
    /// ```
    pub fn as_array(&self) -> Option<&Array> {
        match self {
            Value::Array(a) => Some(a),
            _ => None,
        }
    }

    /// Returns `true` if the value is a `Float`.
    pub fn is_float(&self) -> bool {
        matches!(self, Value::Float(_))
    }

    /// Returns `true` if the value is an `Int`.
    pub fn is_int(&self) -> bool {
        matches!(self, Value::Int(_))
    }

    /// Returns `true` if the value is a `Bool`.
    pub fn is_bool(&self) -> bool {
        matches!(self, Value::Bool(_))
    }

    /// Returns `true` if the value is a `String`.
    pub fn is_string(&self) -> bool {
        matches!(self, Value::String(_))
    }

    /// Returns `true` if the value is a `Map`.
    pub fn is_map(&self) -> bool {
        matches!(self, Value::Map(_))
    }

    /// Returns `true` if the value is an `Array`.
    pub fn is_array(&self) -> bool {
        matches!(self, Value::Array(_))
    }

    /// Creates a new empty `Value::Map`.
    pub fn new_map() -> Self {
        Value::Map(Map::new())
    }

    /// Creates a new empty `Value::Array`.
    pub fn new_array() -> Self {
        Value::Array(Array::new())
    }

    /// Safely gets a value from a map by key, returning None if not a map or
    /// key doesn't exist
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.as_map()?.get(key)
    }

    /// Safely gets a value from an array by index
    pub fn get_index(&self, index: usize) -> Option<&Value> {
        self.as_array()?.get(index)
    }

    #[cfg(all(feature = "json"))]
    /// Deserialises a JSON string into a `Value`.
    ///
    /// Returns a `serde_json::Error` if the JSON cannot be parsed.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Value;
    ///
    /// let json = r#"{"key":"value","num":42}"#;
    /// let val = Value::from_json(json).unwrap();
    /// assert_eq!(val["key"].as_str(), "value");
    /// assert_eq!(val["num"].as_int(), 42);
    /// ```
    ///
    /// # Array example
    ///
    /// ```
    /// use anyval::Value;
    ///
    /// let json = r#"["value",42,true]"#;
    /// let val = Value::from_json(json).unwrap();
    /// assert_eq!(val[0].as_str(), "value");
    /// assert_eq!(val[1].as_int(), 42);
    /// assert_eq!(val[2].as_bool(), true);
    /// ```
    pub fn from_json(s: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(s)
    }

    /// Serialises the value to a JSON string.
    ///
    /// Returns a `serde_json::Error` if the value cannot be serialised.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Value;
    ///
    /// let val = Value::from("hello");
    /// let json = val.to_json().unwrap();
    /// assert_eq!(json, r#""hello""#);
    /// ```
    ///
    /// # Map example
    ///
    /// ```
    /// use anyval::{Value, Map};
    ///
    /// let mut map = Map::new();
    /// map["key"] = "value".into();
    /// let val = Value::Map(map);
    /// let json = val.to_json().unwrap();
    /// assert_eq!(json, r#"{"key":"value"}"#);
    /// ```
    #[cfg(all(feature = "json"))]
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(&self)
    }

    /// Serialises the value to a JSON writer.
    ///
    /// Returns a `serde_json::Error` if the value cannot be serialised.
    ///
    /// # Examples
    ///
    /// ```
    /// use anyval::Value;
    ///
    /// let val = Value::from(42);
    /// let mut buffer = Vec::new();
    /// val.to_json_writer(&mut buffer).unwrap();
    /// assert_eq!(String::from_utf8(buffer).unwrap(), "42");
    /// ```
    #[cfg(all(feature = "json", feature = "std"))]
    pub fn to_json_writer<W: std::io::Write>(&self, writer: W) -> Result<(), serde_json::Error> {
        serde_json::to_writer(writer, &self)
    }
}

#[cfg(feature = "serde")]
impl Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Value::Float(f) => serializer.serialize_f64(*f),
            Value::Int(i) => serializer.serialize_i64(*i),
            Value::Bool(b) => serializer.serialize_bool(*b),
            Value::String(s) => serializer.serialize_str(s.as_str()),
            Value::Map(m) => m.inner.serialize(serializer),
            Value::Array(a) => a.inner.serialize(serializer),
            Value::None => serializer.serialize_none(),
        }
    }
}

impl core::ops::Index<&str> for Value {
    type Output = Value;

    fn index(&self, index: &str) -> &Self::Output {
        match self {
            Value::Map(m) => &m[index],
            _ => &Value::None,
        }
    }
}

impl core::ops::IndexMut<&str> for Value {
    fn index_mut(&mut self, index: &str) -> &mut Self::Output {
        match self {
            Value::Map(m) => &mut m[index],
            _ => {
                *self = Value::None;
                self
            }
        }
    }
}

impl core::ops::Index<usize> for Value {
    type Output = Value;

    fn index(&self, index: usize) -> &Self::Output {
        match self {
            Value::Array(a) => &a[index],
            _ => &Value::None,
        }
    }
}

impl core::ops::IndexMut<usize> for Value {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        match self {
            Value::Array(a) => &mut a[index],
            _ => {
                *self = Value::None;
                self
            }
        }
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Value {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct ValueVisitor;

        impl<'de> serde::de::Visitor<'de> for ValueVisitor {
            type Value = Value;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a valid Value")
            }

            fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Value::Float(v))
            }

            fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Value::Int(v))
            }

            fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Value::Bool(v))
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Value::String(Str::from_owned(v.to_string())))
            }

            fn visit_i8<E>(self, v: i8) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_i64(v as i64)
            }

            fn visit_i16<E>(self, v: i16) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_i64(v as i64)
            }

            fn visit_i32<E>(self, v: i32) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_i64(v as i64)
            }

            fn visit_i128<E>(self, v: i128) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                let mut writer = String::new();
                core::fmt::Write::write_fmt(&mut writer, format_args!("integer `{}` as i128", v))
                    .unwrap();
                Err(serde::de::Error::invalid_type(
                    serde::de::Unexpected::Other(writer.as_str()),
                    &self,
                ))
            }

            fn visit_u8<E>(self, v: u8) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_i64(v as i64)
            }

            fn visit_u16<E>(self, v: u16) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_i64(v as i64)
            }

            fn visit_u32<E>(self, v: u32) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_i64(v as i64)
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                if v <= i64::MAX as u64 {
                    Ok(Value::Int(v as i64))
                } else {
                    Ok(Value::Float(v as f64))
                }
            }

            fn visit_u128<E>(self, v: u128) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                // If the value fits into an i64, store it as an integer.
                if v <= i64::MAX as u128 {
                    Ok(Value::Int(v as i64))
                } else {
                    // Otherwise fall back to a floating‑point representation.
                    Ok(Value::Float(v as f64))
                }
            }
            fn visit_f32<E>(self, v: f32) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_f64(v as f64)
            }

            fn visit_char<E>(self, v: char) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_str(v.encode_utf8(&mut [0u8; 4]))
            }

            fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_str(v)
            }

            fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_str(&v)
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Err(serde::de::Error::invalid_type(
                    serde::de::Unexpected::Bytes(v),
                    &self,
                ))
            }

            fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_bytes(v)
            }

            fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_bytes(&v)
            }

            fn visit_none<E>(self) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(Value::None)
            }

            fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                let _ = deserializer;
                Err(serde::de::Error::invalid_type(
                    serde::de::Unexpected::Option,
                    &self,
                ))
            }

            fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                let inner = Map::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;
                Ok(Value::Map(inner))
            }

            fn visit_seq<A>(self, seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let inner = Array::deserialize(serde::de::value::SeqAccessDeserializer::new(seq))?;
                Ok(Value::Array(inner))
            }
        }

        deserializer.deserialize_any(ValueVisitor)
    }
}

#[cfg(feature = "serde")]
impl Serialize for Map {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.inner.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Map {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let inner = Box::new(HashMap::deserialize(deserializer)?);
        Ok(Map { inner })
    }
}

#[cfg(feature = "serde")]
impl Serialize for Array {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.inner.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Array {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let inner = Box::new(Vec::<Value>::deserialize(deserializer)?);
        Ok(Array { inner })
    }
}

// From implementations for Value
impl From<f64> for Value {
    fn from(f: f64) -> Self {
        Value::Float(f)
    }
}

impl From<i64> for Value {
    fn from(i: i64) -> Self {
        Value::Int(i)
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl From<Map> for Value {
    fn from(m: Map) -> Self {
        Value::Map(m)
    }
}

impl From<Array> for Value {
    fn from(a: Array) -> Self {
        Value::Array(a)
    }
}

impl From<i32> for Value {
    fn from(i: i32) -> Self {
        Value::Int(i as i64)
    }
}

impl From<i128> for Value {
    fn from(i: i128) -> Self {
        if i <= i64::MAX as i128 && i >= i64::MIN as i128 {
            Value::Int(i as i64)
        } else {
            Value::Float(i as f64)
        }
    }
}

impl From<u64> for Value {
    fn from(u: u64) -> Self {
        if u <= i64::MAX as u64 {
            Value::Int(u as i64)
        } else {
            Value::Float(u as f64)
        }
    }
}

impl From<u128> for Value {
    fn from(u: u128) -> Self {
        if u <= i64::MAX as u128 {
            Value::Int(u as i64)
        } else {
            Value::Float(u as f64)
        }
    }
}

impl From<f32> for Value {
    fn from(f: f32) -> Self {
        Value::Float(f as f64)
    }
}

impl Into<f64> for Value {
    fn into(self) -> f64 {
        self.as_float()
    }
}

impl Into<i8> for Value {
    fn into(self) -> i8 {
        self.as_int() as i8
    }
}

impl Into<i16> for Value {
    fn into(self) -> i16 {
        self.as_int() as i16
    }
}

impl Into<i32> for Value {
    fn into(self) -> i32 {
        self.as_int() as i32
    }
}

impl Into<i64> for Value {
    fn into(self) -> i64 {
        self.as_int()
    }
}

impl Into<i128> for Value {
    fn into(self) -> i128 {
        self.as_int() as i128
    }
}

impl Into<isize> for Value {
    fn into(self) -> isize {
        self.as_int() as isize
    }
}

impl Into<usize> for Value {
    fn into(self) -> usize {
        self.as_int() as usize
    }
}

impl Into<bool> for Value {
    fn into(self) -> bool {
        self.as_bool()
    }
}

impl From<&String> for Value {
    fn from(s: &String) -> Self {
        Value::String(Str::from_owned(s.clone()))
    }
}

impl TryFrom<Value> for String {
    type Error = &'static str;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::String(s) => Ok(s.to_string()),
            _ => Err("Value is not a string"),
        }
    }
}

// Add PartialEq for Value comparison
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::String(a), Value::String(b)) => a.as_str() == b.as_str(),
            (Value::None, Value::None) => true,
            // Cross-type numeric comparisons
            (Value::Float(f), Value::Int(i)) | (Value::Int(i), Value::Float(f)) => *f == *i as f64,
            _ => false,
        }
    }
}

// Add IntoIterator for Array
impl IntoIterator for Array {
    type Item = Value;
    type IntoIter = alloc::vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a> IntoIterator for &'a Array {
    type Item = &'a Value;
    type IntoIter = alloc::slice::Iter<'a, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

// Add helper methods to Value
impl Value {
    /// Returns a mutable reference to the underlying map if the value is a
    /// `Map`.
    pub fn as_map_mut(&mut self) -> Option<&mut Map> {
        match self {
            Value::Map(m) => Some(m),
            _ => None,
        }
    }

    /// Returns a mutable reference to the underlying array if the value is an
    /// `Array`.
    pub fn as_array_mut(&mut self) -> Option<&mut Array> {
        match self {
            Value::Array(a) => Some(a),
            _ => None,
        }
    }

    /// Returns `true` if the value is `None`.
    pub fn is_none(&self) -> bool {
        matches!(self, Value::None)
    }

    /// Takes the value out, leaving `Value::None` in its place.
    pub fn take(&mut self) -> Value {
        core::mem::replace(self, Value::None)
    }
}

// Add FromIterator for Array
impl FromIterator<Value> for Array {
    fn from_iter<T: IntoIterator<Item = Value>>(iter: T) -> Self {
        Array {
            inner: Box::new(iter.into_iter().collect()),
        }
    }
}

// Add FromIterator for Map
impl FromIterator<(String, Value)> for Map {
    fn from_iter<T: IntoIterator<Item = (String, Value)>>(iter: T) -> Self {
        Map {
            inner: Box::new(iter.into_iter().collect()),
        }
    }
}

/// Creates a [`Map`] containing the given key-value pairs.
///
/// This macro provides a convenient way to initialize a `Map` with known
/// entries. It comes in two forms:
///
/// # Forms
///
/// - `map!()` - Creates an empty map
/// - `map!(key => value, ...)` - Creates a map with the specified key-value
///   pairs
///
/// # Examples
///
/// ```
/// # use anyval::map;
/// // Create an empty map
/// let empty = map!();
///
/// // Create a map with initial values
/// let m = map! {
///     "name" => "Alice",
///     "age" => 30,
///     "active" => true,
/// };
/// ```
///
/// # Notes
///
/// - Keys are used directly without conversion
/// - Values are converted using `.into()` to support flexible value types
/// - The map is pre-allocated with the exact capacity needed
/// - Trailing commas are allowed
#[macro_export]
macro_rules! map {
    () => {
        $crate::Map::new()
    };
    ($($key:expr => $val:expr),* $(,)?) => {{
        let mut m = $crate::Map::with_capacity(count_tts::count_tts!($($key)*));
        $(
            m[$key] = $val.into();
        )*
        m
    }};
}

/// Creates an [`Array`] containing the given values.
///
/// This macro provides a convenient way to create an `Array` with initial
/// values, similar to the `vec!` macro for `Vec`.
///
/// # Examples
///
/// ```
/// # use anyval::array;
/// // Create an empty array
/// let empty = array![];
///
/// // Create an array with values
/// let numbers = array![1, 2, 3, 4, 5];
///
/// // Trailing commas are allowed
/// let mixed = array![
///     "hello",
///     42,
///     true,
/// ];
/// ```
///
/// # Notes
///
/// - Values are automatically converted using `.into()`, so they must implement
///   the appropriate `Into` trait for the array's element type.
/// - The capacity is pre-allocated to match the number of elements when known
///   at compile time.
#[macro_export]
macro_rules! array {
    () => {
        $crate::Array::new()
    };
    ($($val:expr),* $(,)?) => {{
        let mut a = $crate::Array::with_capacity(count_tts::count_tts!($($val)*));
        $(
            a.push($val.into());
        )*
        a
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map_macro_empty() {
        let m = map! {};
        assert_eq!(m.len(), 0);
    }

    #[test]
    fn test_map_macro_single_entry() {
        let m = map! {
            "key" => "value"
        };
        assert_eq!(m.len(), 1);
        assert_eq!(m["key"].as_str(), "value");
    }

    #[test]
    fn test_map_macro_multiple_entries() {
        let m = map! {
            "name" => "Alice",
            "age" => 30,
            "active" => true,
        };
        assert_eq!(m.len(), 3);
        assert_eq!(m["name"].as_str(), "Alice");
        assert_eq!(m["age"].as_int(), 30);
        assert_eq!(m["active"].as_bool(), true);
    }

    #[test]
    fn test_map_macro_mixed_types() {
        let m = map! {
            "float" => 3.14,
            "int" => 42,
            "bool" => false,
            "string" => "hello",
        };
        assert_eq!(m["float"].as_float(), 3.14);
        assert_eq!(m["int"].as_int(), 42);
        assert_eq!(m["bool"].as_bool(), false);
        assert_eq!(m["string"].as_str(), "hello");
    }

    #[test]
    fn test_map_macro_nested() {
        let inner = map! {
            "inner_key" => "inner_value"
        };
        let m = map! {
            "outer" => Value::Map(inner)
        };
        assert_eq!(m["outer"]["inner_key"].as_str(), "inner_value");
    }

    #[test]
    fn test_array_macro_empty() {
        let a = array![];
        assert_eq!(a.len(), 0);
    }

    #[test]
    fn test_array_macro_single_element() {
        let a = array![42];
        assert_eq!(a.len(), 1);
        assert_eq!(a[0].as_int(), 42);
    }

    #[test]
    fn test_array_macro_multiple_elements() {
        let a = array![1, 2, 3, 4, 5];
        assert_eq!(a.len(), 5);
        assert_eq!(a[0].as_int(), 1);
        assert_eq!(a[4].as_int(), 5);
    }

    #[test]
    fn test_array_macro_mixed_types() {
        let a = array!["hello", 42, true, 3.14];
        assert_eq!(a.len(), 4);
        assert_eq!(a[0].as_str(), "hello");
        assert_eq!(a[1].as_int(), 42);
        assert_eq!(a[2].as_bool(), true);
        assert_eq!(a[3].as_float(), 3.14);
    }

    #[test]
    fn test_array_macro_trailing_comma() {
        let a = array![1, 2, 3,];
        assert_eq!(a.len(), 3);
    }

    #[test]
    fn test_array_macro_nested() {
        let inner = array![1, 2, 3];
        let a = array![Value::Array(inner), 42];
        assert_eq!(a.len(), 2);
        assert_eq!(a[0][0].as_int(), 1);
        assert_eq!(a[1].as_int(), 42);
    }

    #[test]
    fn test_map_macro_with_array_values() {
        let arr = array![1, 2, 3];
        let m = map! {
            "numbers" => Value::Array(arr)
        };
        assert_eq!(m["numbers"][0].as_int(), 1);
    }

    #[test]
    fn test_array_macro_with_map_values() {
        let m = map! {
            "key" => "value"
        };
        let a = array![Value::Map(m), "other"];
        assert_eq!(a[0]["key"].as_str(), "value");
        assert_eq!(a[1].as_str(), "other");
    }

    #[test]
    fn test_complex_nested_structure() {
        let m = map! {
            "users" => array! [
                map! {
                    "name" => "Alice",
                    "age" => 30
                },
                map! {
                    "name" => "Bob",
                    "age" => 25
                }
            ],
            "count" => 2
        };
        assert_eq!(m["users"][0]["name"].as_str(), "Alice");
        assert_eq!(m["users"][1]["age"].as_int(), 25);
        assert_eq!(m["count"].as_int(), 2);
    }
}
