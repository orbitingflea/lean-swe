//! Single-threaded `#![no_std]` container init helper for `LeanSwe.ProcessSandbox`.
#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

pub mod cli;
pub mod ops;
pub mod plan;
pub mod init_sys;
