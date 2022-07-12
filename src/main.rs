#[allow(unused_imports)]

use absal_impl::{parse, SeqReducer, Reducer, compile, decompile};
use absal_impl::par_reducer::ParReducer;
use absal_impl::top;
#[cfg(feature = "gpu")] use absal_impl::vk_reducer::VkReducer;

fn main() {
	// match parse("((λ2f.((λ2x.(f (x x))) (λ2a.(f (a a))))) (λ0l.(λ1z.z)))") {
	// 	Ok(e) => {
	// 		let (net, _, _) = compile(&e);
	//
	// 		// let _net2 = ParReducer::reduce(net.clone());
	// 		// let _net = VkReducer::reduce(net.clone());
	// 		// println!("{}", decompile(&net).unwrap());
	//
	// 		let net = SeqReducer::reduce(net);
	// 		println!("{}", decompile(&net).unwrap());
	// 	},
	// 	Err(err) => eprintln!("{}", err)
	// }
	// absal_impl::break_me_with_overflow();
	// let expr = parse("((λ2x.(x x)) (λ0a.(λ2b.(b b))))").unwrap();
	let expr = parse("((λ2f.((λ2x.(f (x x))) (λ2a.(f (a a))))) (λ2x.(x x)))").unwrap(); // infinite loop y-combinator
	let res = SeqReducer::reduce(top(&expr));
	println!("{}", decompile(&res).unwrap());
}