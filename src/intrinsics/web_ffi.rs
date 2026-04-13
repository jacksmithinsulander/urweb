//! Canonical Basis FFI names used by web-specific compiler passes (RPC, marshalling, …).
//!
//! Centralizing these strings is the first step toward an intrinsic registry keyed by resolved
//! symbol identifiers instead of scattered `Basis.*` comparisons.

/// Module name for the standard Basis FFI bundle in typical Ur/Web projects.
pub const BASIS_MODULE: &str = "Basis";

/// [`BASIS_MODULE`] binding rewritten by [`crate::core::rpc_elaboration::rpcify`].
pub const BASIS_RPC_FUNCTION: &str = "rpc";

/// [`BASIS_MODULE`] binding rewritten alongside [`BASIS_RPC_FUNCTION`].
pub const BASIS_TRY_RPC_FUNCTION: &str = "tryRpc";

/// Returns true when `(module_name, function_name)` is the RPC FFI pair elaborated by `rpcify`.
pub fn is_basis_rpc_ffi(module_name: &str, function_name: &str) -> bool {
    module_name == BASIS_MODULE && function_name == BASIS_RPC_FUNCTION
}

/// Returns true when `(module_name, function_name)` is the tryRpc FFI pair elaborated by `rpcify`.
pub fn is_basis_try_rpc_ffi(module_name: &str, function_name: &str) -> bool {
    module_name == BASIS_MODULE && function_name == BASIS_TRY_RPC_FUNCTION
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basis_rpc_predicate_matches_canonical_spelling() -> anyhow::Result<()> {
        assert!(is_basis_rpc_ffi(BASIS_MODULE, BASIS_RPC_FUNCTION));
        assert!(!is_basis_rpc_ffi("Other", BASIS_RPC_FUNCTION));
        assert!(!is_basis_rpc_ffi(BASIS_MODULE, "other"));
        Ok(())
    }

    #[test]
    fn basis_try_rpc_predicate_matches_canonical_spelling() -> anyhow::Result<()> {
        assert!(is_basis_try_rpc_ffi(BASIS_MODULE, BASIS_TRY_RPC_FUNCTION));
        assert!(!is_basis_try_rpc_ffi(BASIS_MODULE, BASIS_RPC_FUNCTION));
        Ok(())
    }
}
