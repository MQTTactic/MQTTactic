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
    // modname += &String::from("/complete.bc");
    //let modname = "/home/szx/Documents/SourceCode/clangTest/test.bc";
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
        // FunctionHooks::add(&mut fh, "__assert_fail", &test_hook_2);

        config.null_pointer_checking = NullPointerChecking::None; // otherwise this test fails, as ptr[10] could be NULL for the correct value of ptr
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
    let bcDir = String::from(&args[5]);

    // handle__publish:/home/szx/Documents/Experiments/llvm-pass/HelloWorld/OUTPUT/PATHS/handle__publish/Type-6
    // keyBBs，keyFuncs
    let mut fileName = String::from(funcName);
    fileName += &String::from(":");
    fileName += &dir.clone();
    fileName += &String::from("/OUTPUT/PATHS/");
    fileName += &String::from(handlerName);
    fileName += &String::from("/Type-");
    fileName += &file;

    let mut f = fileName;
    let mutProject = get_project(bcDir.clone());

    // ExecutionManager
    let project = get_project(bcDir.clone());
    let mut x: ExecutionManager<haybale::backend::DefaultBackend> =
        symex_function2(f, &project, config_f, None).unwrap();
    // mut state
    let mut mutState = x.mut_state();

    // // struct size
    // let mut struct_mosquitto_size = get_struct_size_bit(&mutProject, mutState, "struct.mosquitto");
    // let mut struct_mosquitto__packet_size =
    //     get_struct_size_bit(&mutProject, mutState, "struct.mosquitto__packet");
    // let mut struct_mosquitto__listener_size =
    //     get_struct_size_bit(&mutProject, mutState, "struct.mosquitto__listener");
    // let mut struct_mosquitto__config_size =
    //     get_struct_size_bit(&mutProject, mutState, "struct.mosquitto__config");

    // let mut dbPtr = &mutState.bv_from_u64(0, 64 as u32);
    // let globalVars = mutProject.all_global_vars();
    // for g in globalVars {
    //     if g.0.name.to_string() == "%db" {
    //         dbPtr = mutState.get_pointer_to_global(&g.0.name).unwrap();
    //         // println!("{:?}", dbPtr);
    //     }
    // }

    // let p = dbPtr.clone();
    // // db.contexts_by_id
    // let contextsByIdAddr = p.add((&mutState.bv_from_u64(24, 64 as u32)));
    // let contextsByIdPtr = mutState.allocate(struct_mosquitto_size as u64);
    // mutState.write(&contextsByIdAddr, contextsByIdPtr);

    // let configAddr = p.add((&mutState.bv_from_u64(108, 64 as u32)));
    // let configPtr = mutState.allocate(struct_mosquitto__config_size as u64);
    // mutState.write(&configAddr, configPtr);

    // let contextPtr = mutState.allocate(struct_mosquitto_size as u64);
    // let context = mutState.read(&contextPtr, struct_mosquitto_size).unwrap();

    // // context.msgs_in.queued
    // //let queuedPtr = context.slice(1775, 1712);
    // let queued = mutState.allocate(424 as u64);
    // //queuedPtr._eq(&queued).assert();
    // let queuedAddr = contextPtr.add((&mutState.bv_from_u64(214, 64 as u32)));
    // mutState.write(&queuedAddr, queued);

    // // context.msgs_in.inflight
    // //let queuedPtr = context.slice(1775, 1712);
    // let inflight = mutState.allocate(424 as u64);
    // //queuedPtr._eq(&queued).assert();
    // let inflightAddr = contextPtr.add((&mutState.bv_from_u64(206, 64 as u32)));
    // mutState.write(&inflightAddr, inflight);

    // // context.listener
    // let listener = mutState.allocate(struct_mosquitto__listener_size as u64);
    // //queuedPtr._eq(&queued).assert();
    // let listenerAddr = contextPtr.add((&mutState.bv_from_u64(306, 64 as u32)));
    // mutState.write(&listenerAddr, listener);

    // // context.in_packet.pos
    // let posAddr = contextPtr.add((&mutState.bv_from_u64(112, 64 as u32)));
    // mutState.write(&posAddr, mutState.bv_from_u64(0, 32));

    // // context.in_packet.payload
    // // 60bytes
    // // mqtt5.0
    // // >>> int.from_bytes(bytes.fromhex('00044d51545405'), byteorder = 'little')
    // // >>> 1500096001541120
    // let payloadAddr = contextPtr.add((&mutState.bv_from_u64(80, 64 as u32)));
    // let payload = mutState.allocate(60 * 8 as u64);
    // mutState.write(&payloadAddr, payload);

    // // context.in_packet.command
    // //let mqttHeader = context.slice(951, 944);
    // //  int('01100010',2)
    // //mqttHeader._eq(&mutState.bv_from_u64(48, 8)).assert();
    // let mqttHeaderAddr = contextPtr.add((&mutState.bv_from_u64(118, 64 as u32)));
    // mutState.write(&mqttHeaderAddr, mutState.bv_from_u64(224, 8));

    // //println!("{}", x.state().solver.print_constraints());

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
            // Err(_e) => state.bv_from_i32(2, 32),
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
    // retval = match result {
    //     Ok(ReturnValue::Return(r)) => r,
    //     Ok(ReturnValue::ReturnVoid) => state.bv_from_i32(0, 32),
    //     Ok(ReturnValue::Throw(_)) => state.bv_from_i32(102, 32),
    //     Ok(ReturnValue::Abort) => state.bv_from_i32(103, 32),
    //     Err(Error::SolverError(_)) => state.bv_from_i32(104, 32),
    //     Err(Error::LoopBoundExceeded(_)) => state.bv_from_i32(105, 32),
    //     Err(Error::UnreachableInstruction) => state.bv_from_i32(106, 32),
    //     Err(Error::PathComplete) => state.bv_from_i32(666, 32),
    //     // Err(_e) => state.bv_from_i32(2, 32),
    //     Err(e) => panic!("{}", em.state().full_error_message_with_context(e)),
    // };

    // cmp = state.bvs_can_be_equal(&retval, &state.bv_from_i32(666, 32));
    // cmpResult = match cmp {
    //     Ok(true) => true,
    //     Ok(false) => false,
    //     Err(e) => false,
    // };
    // if cmpResult {
    //     i = i + 1;
    //     println!("{}", i);
    //     println!("{}", len);
    //     println!("{}", instrs);
    //     println!("return {:?}", retval);
    //     println!("retval can be 0!");
    // }
}
