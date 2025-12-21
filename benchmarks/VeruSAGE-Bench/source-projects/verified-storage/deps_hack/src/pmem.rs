use crate::pmem_memcpy_nodrain;
use core::ffi::c_void;

pub unsafe fn pmem_memcpy_nodrain_helper(
    pm_ptr: *mut c_void,
    bytes_ptr: *const c_void,
    len: usize,
) {
    unsafe {
        pmem_memcpy_nodrain(pm_ptr, bytes_ptr, len);
    }
}
