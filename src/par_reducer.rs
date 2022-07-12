use std::cell::Cell;
use crate::{NK, Node, P, Reducer, Y};

pub struct ParReducer {}
impl Reducer for ParReducer {
	fn reduce(net: Vec<Node>) -> Vec<Node> {
		let mut buf = NetBuf::from(&net[1..]);

		let foo = Cell::as_slice_of_cells(Cell::from_mut(&mut buf.inner));

		buf.get_net()
	}
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
struct NetBuf {
	inner: Vec<u32>,
	root: Vec<u32>
}
impl NetBuf {
	fn get_net(&self) -> Vec<Node<'static>> {
		let mut res = vec![get_node(&*self.root).unwrap()];
		self.inner.chunks(4)
			.filter_map(get_node)
			.for_each(|n| res.push(n));
		res
	}
}
impl<'a> From<&[Node<'a>]> for NetBuf {
	fn from(net: &[Node]) -> Self {
		let buf: Vec<u32> = net[1..].iter()
			.map(node_to_buf)
			.flatten()
			.collect();

		NetBuf { inner: buf, root: node_to_buf(&net[0]) }
	}
}

fn node_to_buf(n: &Node) -> Vec<u32> {
	let mut buf = Vec::<u32>::with_capacity(4);
	let kind: u32 = match n.kind {
		NK::Root => unreachable!(),
		NK::Lam => 1,
		NK::Dup(_) => 2
	};
	for p in n.inner {
		match p.get_wire() {
			None => buf.push(0),
			Some(z) => buf.push((z as u32) + 1)
		}
	}
	buf.push(kind);
	buf
}

fn get_node(raw_node: &[u32]) -> Option<Node<'static>> {
	if raw_node.len() != 4 { return None }
	if let [p1, p2, p3, kind] = raw_node {
		let kind = match kind {
			1 => NK::Lam,
			2 => NK::Dup(0),
			_ => unreachable!()
		};

		Some(Node {
			kind,
			inner: [wire_to_p(*p1), wire_to_p(*p2), wire_to_p(*p3)]
		})
	} else {
		None
	}
}

fn wire_to_p(w: u32) -> P<'static> {
	if w == 0 { P::Empty } else { P::Y(Y::Z((w - 1) as usize)) }
}
