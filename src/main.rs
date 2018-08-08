// This crate is inspired by
// http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html
//
// Minor implementation details suggested by:
// https://gist.github.com/AndyShiue/55198c5a0137b62eb3d5

use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sym(String);

type Type = Expr;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(Sym),
    App(Box<Expr>, Box<Expr>),
    Lam(Sym, Box<Expr>, Box<Expr>),
    Pi(Sym, Box<Expr>, Box<Expr>),
    Kind(Kinds),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Kinds {
    Star,
    Bawx,
}

impl Sym {
    fn alphaRename(&self, set: &HashSet<&Sym>) -> Self {
        let Sym(var) = *self;
        let mut var = var;
        while set.contains(&Sym(var)) {
            var += "'";
        }
        Sym(var)
    }
}

impl Expr {
    // y u no nice and concise, rust?
    fn free_vars(&self) -> HashSet<&Sym> {
        use Expr::*;
        match *self {
            Var(s) => [s].iter().collect(),
            App(f, a) => f.free_vars().union(&a.free_vars()).cloned().collect(),
            Lam(i, t, e) => t
                .free_vars()
                .union(
                    &e.free_vars()
                        .difference(&[i].iter().collect())
                        .cloned()
                        .collect(),
                )
                .cloned()
                .collect(),
            Pi(i, k, t) => k
                .free_vars()
                .union(
                    &t.free_vars()
                        .difference(&[i].iter().collect())
                        .cloned()
                        .collect(),
                )
                .cloned()
                .collect(),
            Kind(_) => HashSet::new(),
        }
    }
