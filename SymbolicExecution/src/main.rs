use boolector::BV;
use haybale::backend::Backend;
use haybale::backend::DefaultBackend;
use haybale::callbacks::Callbacks;
use haybale::config::NullPointerChecking;
use haybale::function_hooks::generic_stub_hook;
use haybale::function_hooks::FunctionHooks;
use haybale::function_hooks::IsCall;
use haybale::watchpoints::Watchpoint;
use haybale::*;
use llvm_ir::types::NamedStructDef;
use llvm_ir::types::Type;
use std::env;
use std::fs::File;
use std::num::Wrapping;
use std::time::Duration;
fn get_project(dir: String) -> Project {
    let mut modname = String::from(&dir);
    modname += &String::from("/complete.bc");
    
    Project::from_bc_path(&modname)
        .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e))
}
pub fn test_hook<B: Backend>(
    state: &mut State<B>,
    call: &dyn IsCall,
) -> Result<ReturnValue<B::BV>> {
    let ret_size = state.size_in_bits(&state.type_of(call)).ok_or_else(|| {
        Error::OtherError("simple_callee shouldn't return opaque struct type".into())
    })?;
    Ok(ReturnValue::Return(state.bv_from_u32(1, ret_size)))
}
pub fn test_hook_2<B: Backend>(
    state: &mut State<B>,
    call: &dyn IsCall,
) -> Result<ReturnValue<B::BV>> {
    Ok(ReturnValue::ReturnVoid)
}
pub fn get_struct_size_bit<B: Backend>(
    mutProject: &Project,
    mutState: &mut State<B>,
    structName: &str,
) -> u32 {
    match mutProject.get_named_struct_def(&structName).unwrap().0 {
        NamedStructDef::Opaque => {
            return 0 as u32;
        }
        NamedStructDef::Defined(ty) => {
            let structType = ty.as_ref();
            let mut struct_mosquitto_size = {
                let element_size_bits = mutState
                    .size_in_bits(structType)
                    .ok_or_else(|| {
                        Error::MalformedInstruction("Alloca with opaque struct type".into())
                    })
                    .unwrap();
                element_size_bits as u32
            };
            return struct_mosquitto_size;
        }
    }
    return 0 as u32;
}
fn main() {
    let config_f: Config<DefaultBackend> = {
        let mut config = Config::default();
        let mut fh = FunctionHooks::default();
        FunctionHooks::add_default_hook(&mut fh, &generic_stub_hook);
        FunctionHooks::add_inline_asm_hook(&mut fh, &generic_stub_hook);
        
        config.null_pointer_checking = NullPointerChecking::None; 
        config.max_callstack_depth = Some(5);
        config.max_memcpy_length = Some(0x10);
        config.function_hooks = fh;
        config.loop_bound = 2;
        config.solver_query_timeout = Some(Duration::new(800, 0));
        config
    };
    let args: Vec<String> = env::args().collect();
    let mut handlerName = String::from(&args[1]);
    let mut funcName = String::from(&args[2]);
    let file = String::from(&args[3]);
    let dir = String::from(&args[4]);
    
    
    let mut fileName = String::from(funcName);
    fileName += &String::from(":");
    fileName += &dir.clone();
    fileName += &String::from("/OUTPUT/PATHS/");
    fileName += &String::from(handlerName);
    fileName += &String::from("/Type-");
    fileName += &file;
    let mut f = fileName;
    let mutProject = get_project(dir.clone());
    
    let project = get_project(dir.clone());
    let mut x: ExecutionManager<haybale::backend::DefaultBackend> =
        symex_function2(f, &project, config_f, None).unwrap();
    
    let mut mutState = x.mut_state();
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    while (true) {
        let result = x.next();
        match result {
            Some(Ok(ReturnValue::Return(_))) => {}
            Some(Ok(ReturnValue::ReturnVoid)) => {}
            Some(Ok(ReturnValue::Throw(_))) => {}
            Some(Ok(ReturnValue::Abort)) => {}
            Some(Err(Error::PathComplete)) => {
                let mut state = x.state();
                let mut instrs = state.pretty_path_llvm();
                println!("{}", state.pretty_path_source());
                println!("{}", instrs);
                println!("OK\n");
                break;
            }
            Some(Err(Error::OtherError(e))) => {
                if e == String::from("No Paths anymore!") {
                    println!("NO PATHS!");
                } else {
                    let mut state = x.state();
                    let mut instrs = state.pretty_path_llvm();
                    println!("{}", instrs);
                    println!("{}", e);
                }
                break;
            }
            
            Some(Err(e)) => {
                let mut state = x.state();
                let mut instrs = state.pretty_path_llvm();
                println!("{}", instrs);
                println!("{}", e);
                continue;
            }
            None => {}
        };
    }
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
}
