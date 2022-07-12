#![allow(dead_code)]

#[cfg(feature = "gpu")] pub mod vk_reducer;
pub mod par_reducer;

use std::borrow::Cow;
use std::cmp;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicUsize, Ordering};
use anyhow::{Context, Result};
use pest::iterators::Pair;
use pest::Parser;
use rayon::prelude::*;

pub trait Reducer {
    fn reduce(net: Vec<Node>) -> Vec<Node>;
}

pub struct SeqReducer;
impl Reducer for SeqReducer {
    fn reduce(net: Vec<Node>) -> Vec<Node> {
        let net = make_node_map(&net);
        reduce(&net);
        let g = net.guard();
        let mut res: Vec<_> = net.iter(&g)
            .map(|(_,v)| *v)
            .collect();

        res.sort_unstable_by(|a, b|
            if a.kind == NK::Root {
                cmp::Ordering::Less
            } else if b.kind == NK::Root {
                cmp::Ordering::Greater
            } else {
                cmp::Ordering::Equal
            }
        );

        res
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Abs(String, Box<Term>),
    App(Box<Term>, Box<Term>)
}
impl Term {
    fn var(x: Ident) -> Term {
        Term::Var(x.to_string())
    }
}
impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(x) => write!(f, "{}", x),
            Term::App(t1, t2) => write!(f, "({} {})", t1, t2),
            Term::Abs(x, t) => write!(f, "(λ{}.{})", x, t)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    Abs(usize, String, Box<Expr>),
    App(Box<Expr>, Box<Expr>)
}

type Gamma<'a> = HashSet<Y<'a>>;

#[derive(Clone, Debug, Copy, Eq)]
pub enum Y<'a> {
    Z(usize),
    XZ(Ident<'a>, usize)
}
impl Y<'_> {
    fn get_wire(&self) -> usize {
        match self {
            Y::Z(w) => *w,
            Y::XZ(_, w) => *w
        }
    }
}
impl Hash for Y<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Y::Z(z) => z.hash(state),
            Y::XZ(_, z) => z.hash(state)
        }
    }
}
impl PartialEq for Y<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.get_wire() == other.get_wire()
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum P<'a> {
    Y(Y<'a>),
    Empty
}
impl P<'_> {
    fn get_wire(&self) -> Option<usize> {
        match self {
            P::Y(y) => Some(y.get_wire()),
            P::Empty => None
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum NK { Lam, Dup(usize), Root }

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Node<'a> {
    pub kind: NK,
    pub inner: [P<'a>; 3]
}
impl Display for Node<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fn wire_ident<'a>(p: &P<'a>) -> Cow<'static, str> {
            match p {
                P::Empty => "#".into(),
                P::Y(Y::Z(z)) => z.to_string().into(),
                P::Y(Y::XZ(x, z)) => format!("{}!{}", x, z).into()
            }
        }
        let nk = match self.kind { NK::Lam => "-", NK::Dup(_) => "*", NK::Root => "-" };
        write!(f, "{} {} {} {}", nk, wire_ident(&self.inner[0]), wire_ident(&self.inner[1]), wire_ident(&self.inner[2]))
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum D { Snd, Trd }

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
struct NP<'a> {
    node: Node<'a>,
    port: u8
}

type Ident<'a> = &'a str;
type Net<'a> = flurry::HashMap<usize, Node<'a>>;

fn fresh_z() -> usize {
    static NEXT_Z: AtomicUsize = AtomicUsize::new(0);
    NEXT_Z.fetch_add(1, Ordering::Relaxed)
}

fn fresh_node_idx() -> usize {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    NEXT.fetch_add(1, Ordering::Relaxed)
}

fn fresh_constructor_id() -> usize {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    NEXT.fetch_add(1, Ordering::Relaxed)
}

fn fresh_name() -> String {
    static NEXT_N: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT_N.fetch_add(1, Ordering::Relaxed);
    format!("t{}", n)
}

pub fn top(e: &Expr) -> Vec<Node> {
    let z = fresh_z();
    let (mut ns, _, y) = compile(e);
    let mut net = vec![Node { kind: NK::Root, inner: [P::Y(Y::Z(z)), P::Y(y), P::Y(Y::Z(z))] }];
    net.append(&mut ns);
    net
}

pub fn compile(e: &Expr) -> (Vec<Node>, Gamma, Y) {
    match e {
        Expr::Var(x) => {
            let wire = Y::XZ(x, fresh_z());
            (vec![], HashSet::from([wire]), wire)
        }
        Expr::App(e1, e2) => {
            let z = Y::Z(fresh_z());
            let (mut ns1, mut g1, y1) = compile(e1);
            let (mut ns2, g2, y2) = compile(e2);

            let mut net = vec![Node { kind: NK::Lam, inner: [P::Y(y1), P::Y(y2), P::Y(z)] }];
            net.append(&mut ns1);
            net.append(&mut ns2);
            g1.extend(g2);

            (net, g1, z)
        }
        Expr::Abs(n, x, f) if *n == 0 => {
            let xz = Y::XZ(x, fresh_z());
            let (mut ns0, g, y0) = compile(f);
            let mut net = vec![Node { kind: NK::Lam, inner: [P::Y(xz), P::Empty, P::Y(y0)] }];
            net.append(&mut ns0);
            (net, g, xz)
        }
        Expr::Abs(n, x, e) if *n == 1 => {
            let xz = Y::XZ(x, fresh_z());
            let (mut ns0, mut g, y0) = compile(e);
            let xz_p = *g.iter().find(|y| matches!(y, Y::XZ(inner_x, _) if inner_x == x)).unwrap();
            g.remove(&xz_p);

            let mut net = vec![Node { kind: NK::Lam, inner: [P::Y(xz), P::Y(xz_p), P::Y(y0)] }];
            net.append(&mut ns0);
            (net, g, xz)
        },
        Expr::Abs(_, x, e) => {
            let xz = Y::XZ(x, fresh_z());
            let (mut ns1, mut g, y1) = compile(e);
            let xzs = g.iter().filter(|y| matches!(y, Y::XZ(inner_x, _) if inner_x == x)).copied().collect::<VecDeque<_>>();
            for xz in &xzs { g.remove(xz); }

            let (mut ns2, y2) = dup(xzs);

            let mut net = vec![Node { kind: NK::Lam, inner: [P::Y(xz), P::Y(y2), P::Y(y1)] }];
            net.append(&mut ns1);
            net.append(&mut ns2);
            (net, g, xz)
        }
    }
}

fn dup(mut gamma: VecDeque<Y>) -> (Vec<Node>, Y) {
    match gamma.len() {
        2 => {
            let x = match gamma[0] { Y::XZ(x, _) => x, _ => unreachable!() };
            let z = Y::XZ(x, fresh_z());
            (vec![Node { kind: NK::Dup(fresh_constructor_id()), inner: [P::Y(z), P::Y(gamma[0]), P::Y(gamma[1])] }], z)
        },
        n if n > 2 => {
            let y = gamma.pop_front().unwrap();
            let y0 = gamma.pop_front().unwrap();
            let (mut net, y_prime) = dup(VecDeque::from([y, y0]));
            gamma.push_front(y_prime);
            let (mut net2, y_cont) = dup(gamma);
            net.append(&mut net2);
            (net, y_cont)
        },
        _ => unreachable!()
    }
}

fn make_node_map<'a>(net: &[Node<'a>]) -> Net<'a> {
    net.iter().map(|n| (fresh_node_idx(), *n)).collect()
}

fn get_active_pairs(net: &Net) -> Vec<(usize, usize)> {
    let mut seen = HashSet::new();
    let mut active_pairs = Vec::new();

    let guard = net.guard();
    net.iter(&guard)
        .filter_map(|(i, node)|
            node.inner[0].get_wire()
                .and_then(|wire|
                    net.iter(&guard)
                        .find(|(_, n)| n != &node && n.inner[0].get_wire().map(|w| w == wire).unwrap_or(false))
                        .map(|(other_idx, _)| if i < other_idx { (*i, *other_idx) } else { (*other_idx, *i) })
                )
        )
        .for_each(|pair| {
            if seen.contains(&pair) {
                active_pairs.push(pair);
            } else {
                seen.insert(pair);
            }
        });

    active_pairs
}

fn reduce(net: &Net) {
    let mut active_pairs = get_active_pairs(net);

    while !active_pairs.is_empty() {
        active_pairs.into_iter().for_each(|active_pair| {
            rewrite(net, active_pair);
            print_net_map(net);
        });
        active_pairs = get_active_pairs(net);
    }

    print_net_map(net);
}

pub fn rewrite(net: &Net, active_pair: (usize, usize)) {
    let guard = net.guard();
    let n1 = net.get(&active_pair.0, &guard); let n2 = net.get(&active_pair.1, &guard);
    if let Some(n1) = n1 {
        if let Some(n2) = n2 {
            let n1 = *n1; let n2 = *n2;
            let active_port = n1.inner[0].get_wire().unwrap();

            if n1.kind == n2.kind {
                // annihilate
                if let P::Y(y0) = n1.inner[1] {
                    if let P::Y(y1) = n1.inner[2] {
                        println!("applying (annihilate on {})", active_port);
                        let p0 = n2.inner[1];
                        let p1 = n2.inner[2];

                        net.remove(&active_pair.0, &guard); net.remove(&active_pair.1, &guard);

                        // Relink
                        for (k,n) in net.iter(&guard) {
                            for (i, p) in n.inner.iter().enumerate() {
                                if p.get_wire() == Some(y0.get_wire()) {
                                    let mut inner = n.inner;
                                    inner[i] = p0;
                                    net.insert(*k, Node { inner, ..*n }, &guard);
                                }
                                if p.get_wire() == Some(y1.get_wire()) {
                                    // Re-fetch the node in case we changed it in the previous if-block
                                    let n = net.get(k, &guard).unwrap();

                                    let mut inner = n.inner;
                                    inner[i] = p1;
                                    net.insert(*k, Node { inner, ..*n }, &guard);
                                }
                            }
                        }
                    }
                }
            } else {
                // Commute
                println!("applying (commute on {})", active_port);
                let p0 = n1.inner[1]; let p1 = n1.inner[2];
                let p0_p = n2.inner[1]; let p1_p = n2.inner[2];

                // new connections
                let p2 = P::Y(Y::Z(fresh_z()));
                let p3 = P::Y(Y::Z(fresh_z()));
                let p4 = P::Y(Y::Z(fresh_z()));
                let p5 = P::Y(Y::Z(fresh_z()));

                net.insert(fresh_node_idx(), Node { kind: n2.kind, inner: [p0, p2, p3] }, &guard);
                net.insert(fresh_node_idx(), Node { kind: n2.kind, inner: [p1, p4, p5] }, &guard);

                net.insert(fresh_node_idx(), Node { kind: n1.kind, inner: [p0_p, p2, p4] }, &guard);
                net.insert(fresh_node_idx(), Node { kind: n1.kind, inner: [p1_p, p3, p5] }, &guard);

                net.remove(&active_pair.0, &guard); net.remove(&active_pair.1, &guard);
            }
        }
    }
}

pub fn decompile(net: &[Node]) -> Result<Term> {
    let root = net[0];
    let net = &net[1..];
    let name_c = AtomicUsize::new(0);

    let res = build_term(net, Default::default(), Default::default(), enter(net, &root.inner[1], &NP { node: root, port: 1 }), &|| {
        let n = name_c.fetch_add(1, Ordering::Relaxed);
        format!("t{}", n)
    }, 0)?;

    Ok(res)
}

fn enter<'a, 'b>(net: &'b [Node<'a>], p: &P<'a>, ignore: &NP<'a>) -> NP<'a> {
    let from = p.get_wire().unwrap();

    println!("following {:?}", p);
    net.iter()
        .flat_map(|n|
            n.inner.iter().map(|p| p.get_wire()).filter_map(|w| {
                match w {
                    Some(w) => {
                        if w == from {
                            Some(NP {
                                node: *n,
                                port: n.inner.iter().position(|p| p.get_wire() == Some(w)).unwrap() as u8
                            })
                        } else {
                            None
                        }
                    },
                    None => None
                }
            })
        )
        .find(|np| np != ignore)
        .unwrap()
}

fn build_term<'a, 'b, FN>(net: &'b [Node<'a>], ds: VecDeque<D>, vars: HashMap<usize, String>, np: NP<'a>, fresh_name: &FN, depth: u32) -> Result<Term> where
    FN: Fn() -> String
{
    const MAX_TERM_DEPTH: u32 = 1000;
    if depth > MAX_TERM_DEPTH {
        // bail!("Stack overflow");
    }

    let p = np.node.inner[np.port as usize];
    Ok(match np.node.kind {
        NK::Lam => {
            match np.port {
                0 => {
                    let mut vars = vars;
                    let x = fresh_name();
                    let p2 = np.node.inner[1]; let p3 = np.node.inner[2];
                    if let Some(z) = p2.get_wire() {
                        vars.insert(z, x.clone());
                    }

                    Term::Abs(x, Box::new(build_term(net, ds, vars, enter(net, &p3, &NP { node: np.node, port: 2 }), fresh_name, depth+1)?))
                }
                1 => {
                    Term::var(vars.get(&p.get_wire().unwrap()).context("No var!")?)
                },
                2 => {
                    let p1 = np.node.inner[0]; let p2 = np.node.inner[1];

                    let t1 = Box::new(build_term(net, ds.clone(), vars.clone(), enter(net, &p1, &NP { node: np.node, port: 0 }), fresh_name, depth+1)?);
                    let t2 = Box::new(build_term(net, ds, vars, enter(net, &p2, &NP { node: np.node, port: 1 }), fresh_name, depth+1)?);
                    Term::App(t1, t2)
                }
                _ => unreachable!()
            }
        },
        NK::Dup(_) => {
            match np.port {
                0 => {
                    let mut ds = ds;
                    let d = ds.pop_back().unwrap();
                    let p2 = np.node.inner[1]; let p3 = np.node.inner[2];

                    match d {
                        D::Snd => {
                            build_term(net, ds, vars, enter(net, &p2, &NP { node: np.node, port: 1 }), fresh_name, depth+1)?
                        }
                        D::Trd => {
                            build_term(net, ds, vars, enter(net, &p3, &NP { node: np.node, port: 2 }), fresh_name, depth+1)?
                        }
                    }
                }
                1 => {
                    let mut ds = ds;
                    ds.push_back(D::Snd);
                    build_term(net, ds, vars, enter(net, &np.node.inner[0], &NP { node: np.node, port: 0 }), fresh_name, depth+1)?
                },
                2 => {
                    let mut ds = ds;
                    ds.push_back(D::Trd);
                    build_term(net, ds, vars, enter(net, &np.node.inner[0], &NP { node: np.node, port: 0 }), fresh_name, depth+1)?
                }
                _ => unreachable!()
            }
        },
        NK::Root => unreachable!()
    })
}

fn print_net(net: &[Node]) {
    println!("--------------n={}---------------", net.len());
    for node in net {
        println!("{}", node);
    }
    println!("-----------------------------");
}

fn print_net_map(net: &Net) {
    let guard = net.guard();
    println!("--------------n={}---------------", net.len());

    let root = net.values(&guard).find(|n| n.kind == NK::Root).unwrap();
    println!("{}", root);

    for node in net.values(&net.guard()).filter(|n| n.kind != NK::Root) {
        println!("{}", node);
    }
    println!("-----------------------------");
}

#[derive(pest_derive::Parser)]
#[grammar = "absal.pest"]
struct AbsalParser;

pub fn parse(expr: &str) -> Result<Expr> {
    let pairs = AbsalParser::parse(Rule::e, expr)?;

    fn parse_expr(pair: Pair<Rule>) -> Result<Expr> {
        Ok(match pair.as_rule() {
            Rule::x => Expr::Var(pair.as_str().to_string()),
            Rule::eApp => {
                let mut inner = pair.into_inner();
                Expr::App(
                    Box::new(parse_expr(inner.next().unwrap())?),
                    Box::new(parse_expr(inner.next().unwrap())?)
                )
            },
            Rule::eAbs => {
                let mut inner = pair.into_inner();
                Expr::Abs(
                    inner.next().unwrap().as_str().parse::<usize>()?,
                    inner.next().unwrap().as_str().to_string(),
                    Box::new(parse_expr(inner.next().unwrap())?)
                )
            },
            _ => {
                println!("wtf {:?}", pair);
                unreachable!()
            }
        })
    }

    let pair = pairs.into_iter().next().context("Invalid syntax tree")?;
    parse_expr(pair)
}

pub fn break_me_with_overflow() {
    // omega two -> four
    // ((λx.(x x)) (λf.(λx.(f (f x))))) -> four
    // let func = parse("((λ2x.(x x)) (λ2f.(λ1x.(f (f x)))))").unwrap();
    let func = parse("((λ1x.(x (λ2f.(λ1x.(f (f x)))))) (λ2f.(λ1x.(f (f x)))))").unwrap();

    let net = top(&func);
    print_net(&net);
    let net = SeqReducer::reduce(net);
    println!("Fully reduced!");
    print_net(&net);
    let res = decompile(&net).unwrap();

    assert_eq!(format!("{}", res), "(λt0.(λt1.(t0 (t0 (t0 (t0 t1))))))".to_string());
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn works_simple() {
        // λy.λx.x λx.x -> λx.x
        let func = parse("((λ0y.(λ1x.x)) (λ1a.a))").unwrap();

        let net = top(&func);
        print_net(&net);
        let net = SeqReducer::reduce(net);
        let res = decompile(&net).unwrap();
        println!("{}", res);

        assert_eq!(res, Term::Abs("t0".to_string(), Box::new(Term::var("t0"))));
    }

    #[test]
    fn works_complex() {
        // λy.λx.(y x) λa.a -> λx.x
        let func = parse("((λ1y.(λ1x.(y x))) (λ1a.a))").unwrap();

        let net = top(&func);
        print_net(&net);
        let net = SeqReducer::reduce(net);
        let res = decompile(&net).unwrap();

        assert_eq!(format!("{}", res), "(λt0.t0)".to_string());
    }

    #[test]
    fn works_dup1() {
        // ((λa.λb.a) (λc.c)) (λx.(x x)) -> λc.c
        let func = parse("(((λ1a.(λ0b.a)) (λ1c.c)) (λ2x.(x x)))").unwrap();

        let net = top(&func);
        print_net(&net);
        let net = SeqReducer::reduce(net);
        let res = decompile(&net).unwrap();

        assert_eq!(format!("{}", res), "(λt0.t0)".to_string());
    }

    #[test]
    fn works_dup2() {
        // (λa.(λb.b) (λc.c) λx.(x x)) -> λx.(x x)
        let func = parse("(((λ0a.(λ1b.b)) (λ1c.c)) (λ2x.(x x)))").unwrap();

        let net = top(&func);
        print_net(&net);
        let net = SeqReducer::reduce(net);
        let res = decompile(&net).unwrap();

        assert_eq!(format!("{}", res), "(λt0.(t0 t0))".to_string());
    }

    #[test]
    fn works_dup3() {
        // (λa.(λb.b) (λc.c) λx.(x (x x))) -> λx.(x (x x))
        let func = parse("(((λ0a.(λ1b.b)) (λ1c.c)) (λ3x.(x (x x))))").unwrap();

        let net = top(&func);
        print_net(&net);
        let net = SeqReducer::reduce(net);
        let res = decompile(&net).unwrap();

        assert_eq!(format!("{}", res), "(λt0.(t0 (t0 t0)))".to_string());
    }

    #[test]
    fn y_comb() {
        // (λf.(λx.f (x x)) (λa.f (a a))) (λl.λz.z)
        // a.k.a Y (λl.λz.z)
        // let _y = parse("(λ2f.((λ2x.(f (x x))) (λ2a.(f (a a)))))").unwrap();
        let func = parse("((λ2f.((λ2x.(f (x x))) (λ2a.(f (a a))))) (λ0l.(λ1z.z)))").unwrap();

        let net = top(&func);
        print_net(&net);
        let net = SeqReducer::reduce(net);
        let res = decompile(&net).unwrap();

        assert_eq!(format!("{}", res), "(λt0.t0)".to_string());
    }

    #[test]
    #[ignore]
    fn omega_two() {
        let func = parse("((λ2x.(x x)) (λ2f.(λ1x.(f (f x)))))").unwrap();

        let net = top(&func);
        print_net(&net);
        let net = SeqReducer::reduce(net);
        println!("Fully reduced!");
        let res = decompile(&net).unwrap();

        assert_eq!(format!("{}", res), "(λt0.(λt1.(t0 (t0 (t0 (t0 t1))))))".to_string());
    }

    #[test]
    fn omega_two_works() {
        // omega two -> four
        // but the omega two is manually cloned here
        // ((λx.(x x)) (λf.(λx.(f (f x))))) -> four
        let func = parse("((λ1x.(x (λ2f.(λ1x.(f (f x)))))) (λ2f.(λ1x.(f (f x)))))").unwrap();

        let net = top(&func);
        print_net(&net);
        let net = SeqReducer::reduce(net);
        println!("Fully reduced!");
        let res = decompile(&net).unwrap();

        assert_eq!(format!("{}", res), "(λt0.(λt1.(t0 (t0 (t0 (t0 t1))))))".to_string());
    }
}
