use llvm_sys::*;
pub fn from_bc_path(path: &str) {
    
    use std::ffi::{CStr, CString};
    use std::mem;
    let memory_buffer = unsafe {
        let mut memory_buffer = std::ptr::null_mut();
        let mut err_string = std::mem::zeroed();
        let return_code = LLVMCreateMemoryBufferWithContentsOfFile(
            path.as_ptr() as *const _,
            &mut memory_buffer,
            &mut err_string,
        );
        if return_code != 0 {
            return Err(CStr::from_ptr(err_string)
                .to_str()
                .expect("Failed to convert CStr")
                .to_owned());
        }
        memory_buffer
    };
    debug!("Created a MemoryBuffer");
    let context = from_llvm::Context::new();
    use llvm_sys::bit_reader::LLVMParseBitcodeInContext2;
    let module = unsafe {
        let mut module: mem::MaybeUninit<LLVMModuleRef> = mem::MaybeUninit::uninit();
        let return_code =
            LLVMParseBitcodeInContext2(context.ctx, memory_buffer, module.as_mut_ptr());
        LLVMDisposeMemoryBuffer(memory_buffer);
        if return_code != 0 {
            return Err("Failed to parse bitcode".to_string());
        }
        module.assume_init()
    };
    debug!("Parsed bitcode to llvm_sys module");
}
fn main() {
    from_bc_path("/Experiments/FlashMQ/CFGPass/complete.bc")
}
format!("{}\0", &"/tmp/main.bc".to_owned()).as_ptr() as *const i8;
