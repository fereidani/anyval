use crate::*;
use std::{
    fmt::{Debug, Display},
    sync::Arc,
};

/// A string type that can hold either a `'static` string slice, an
/// `Arc<String>` for cheap cloning, or an owned `String`.
///
/// This enum is useful when you need to store string data that may be
/// static, shared, or owned without incurring unnecessary allocations.
///
/// # Variants
///
/// * `Static(&'static str)` – A reference to a compile‑time constant string.
/// * `Rc(Arc<String>)` – A reference‑counted pointer to a `String`, allowing cheap
///   cloning of the underlying data.
/// * `Owned(String)` – An owned heap‑allocated `String`.
pub enum Str {
    /// A reference to a compile‑time constant string.
    Static(&'static str),

    /// A reference‑counted pointer to a `String`.
    Rc(Arc<String>),

    /// An owned heap‑allocated `String`.
    Owned(String),
}

impl Display for Str {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Str::Static(s) => write!(f, "{}", s),
            Str::Rc(s) => write!(f, "{}", s),
            Str::Owned(s) => write!(f, "{}", s),
        }
    }
}

impl Clone for Str {
    fn clone(&self) -> Self {
        match self {
            Str::Static(s) => Str::Static(s),
            Str::Rc(s) => Str::Rc(Arc::clone(s)),
            Str::Owned(s) => Str::Owned(s.clone()),
        }
    }
}

impl Debug for Str {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Str::Static(s) => write!(f, "Str::Static({:?})", s),
            Str::Rc(s) => write!(f, "Str::Rc({:?})", s),
            Str::Owned(s) => write!(f, "Str::Owned({:?})", s),
        }
    }
}

impl Str {
    /// Returns a string slice (`&str`) that references the data inside the
    /// `Str`, regardless of which variant it holds.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use anyval::Str;
    /// let s = Str::from_static("hello");
    /// assert_eq!(s.as_str(), "hello");
    /// ```
    pub fn as_str(&self) -> &str {
        match self {
            Str::Static(s) => s,
            Str::Rc(s) => s.as_str(),
            Str::Owned(s) => s.as_str(),
        }
    }

    /// Constructs a `Str` from a `'static` string slice.
    ///
    /// This does not allocate; the variant stored is `Str::Static`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use anyval::Str;
    /// let s = Str::from_static("static");
    /// assert!(s.is_static());
    /// ```
    pub fn from_static(s: &'static str) -> Self {
        Str::Static(s)
    }

    /// Constructs a `Str` from an owned `String`.
    ///
    /// The `String` is moved into the `Str::Owned` variant.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use anyval::Str;
    /// let original = String::from("owned");
    /// let s = Str::from_owned(original);
    /// // `original` can no longer be used here
    /// ```
    pub fn from_owned(s: String) -> Self {
        Str::Owned(s)
    }

    /// Constructs a `Str` from an `Arc<String>`.
    ///
    /// The `Arc` is moved into the `Str::Rc` variant, allowing cheap cloning.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::sync::Arc;
    /// use anyval::Str;
    /// let arc = Arc::new(String::from("shared"));
    /// let s = Str::from_rc(arc.clone());
    /// assert!(s.is_rc());
    /// ```
    pub fn from_rc(s: Arc<String>) -> Self {
        Str::Rc(s)
    }

    /// Consumes the `Str` and returns an owned `String`.
    ///
    /// - For `Str::Static`, the static slice is cloned into a new `String`.
    /// - For `Str::Rc`, the underlying `String` is cloned.
    /// - For `Str::Owned`, the inner `String` is returned without allocation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use anyval::Str;
    /// let s = Str::from_owned(String::from("owned"));
    /// let owned = s.take(); // `s` is moved
    /// assert_eq!(owned, "owned");
    /// ```
    pub fn take(self) -> String {
        match self {
            Str::Static(s) => s.to_string(),
            Str::Rc(s) => s.as_ref().clone(),
            Str::Owned(s) => s,
        }
    }

    /// Alias for [`take`]; consumes the `Str` and returns an owned `String`.
    ///
    /// This method exists for API symmetry with other types that provide an
    /// `into_*` conversion.
    pub fn into_string(self) -> String {
        self.take()
    }

    /// Returns `true` if the `Str` is the `Static` variant.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use anyval::Str;
    /// let s = Str::from_static("static");
    /// assert!(s.is_static());
    /// ```
    pub fn is_static(&self) -> bool {
        matches!(self, Str::Static(_))
    }

    /// Returns `true` if the `Str` is the `Owned` variant.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use anyval::Str;
    /// let s = Str::from_owned(String::from("owned"));
    /// assert!(s.is_owned());
    /// ```
    pub fn is_owned(&self) -> bool {
        matches!(self, Str::Owned(_))
    }

    /// Returns `true` if the `Str` is the `Rc` variant.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use anyval::Str;
    /// use std::sync::Arc;
    /// let s = Str::from_rc(Arc::new(String::from("shared")));
    /// assert!(s.is_rc());
    /// ```
    pub fn is_rc(&self) -> bool {
        matches!(self, Str::Rc(_))
    }
}

impl From<Str> for Value {
    fn from(s: Str) -> Self {
        Value::String(s)
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::String(Str::Owned(s))
    }
}

impl From<&'static str> for Value {
    fn from(s: &'static str) -> Self {
        Value::String(Str::Static(s))
    }
}

impl From<Arc<String>> for Value {
    fn from(s: Arc<String>) -> Self {
        Value::String(Str::Rc(s))
    }
}

// From implementations for Str
impl From<&'static str> for Str {
    fn from(s: &'static str) -> Self {
        Str::Static(s)
    }
}

impl From<String> for Str {
    fn from(s: String) -> Self {
        Str::Owned(s)
    }
}

impl From<Arc<String>> for Str {
    fn from(s: Arc<String>) -> Self {
        Str::Rc(s)
    }
}

impl From<Str> for String {
    fn from(s: Str) -> Self {
        s.take()
    }
}
