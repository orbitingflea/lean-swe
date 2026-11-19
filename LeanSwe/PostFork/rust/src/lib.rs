//! Allocation-free, lock-free post-`fork` child-setup core for `LeanSwe.PostFork`.
#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

pub mod child;
pub mod fd_ops;
#[cfg(feature = "standalone")]
pub mod ffi;
pub mod sys;
