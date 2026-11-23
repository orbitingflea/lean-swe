//! Entrypoint binary wrapper delegating to `psandbox_init::ops::run_init`.
#![no_std]
#![no_main]

use core::ffi::c_char;

/// C-ABI process entrypoint invoked by `crt1.o`.
///
/// # Safety
/// Must be invoked by the platform C runtime startup with a valid `(argc, argv)` vector.
#[no_mangle]
pub unsafe extern "C" fn main(argc: i32, argv: *const *const c_char) -> i32 {
    let mut s = unsafe { psandbox_init::init_sys::Sys::from_main_args(argc, argv) };
    let count = if argc > 0 { argc as usize } else { 0 };
    psandbox_init::ops::run_init(&mut s, count)
}
