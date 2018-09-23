//! Utilities.

/// Returns "Yes" or "No".
#[snippet = "yn"]
pub fn yn(result: bool) -> &'static str {
    if result { "Yes" } else { "No" }
}
