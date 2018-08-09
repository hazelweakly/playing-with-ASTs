// This crate is inspired by
// http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html
//
// Minor implementation details suggested by:
// https://gist.github.com/AndyShiue/55198c5a0137b62eb3d5

use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sym(String);

// type Type = Expr;

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
    fn alpha_rename(&self, set: &HashSet<&Sym>) -> Self {
        if set.contains(self) {
            Sym(format!("{}'", self.0)).alpha_rename(set)
        } else {
            self.clone()
        }
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

    fn subst(&self, v: Sym, x: Self) -> Self {
        use Expr::*;
        match *self {
            Var(i) => if i == v {
                x
            } else {
                Var(i)
            },
            App(f, a) => App(Box::new(f.subst(v, x)), Box::new(a.subst(v, x))),
            Lam(i, t, e) => if v == i {
                Lam(i, Box::new(t.subst(v, x)), e)
            } else {
                if x.free_vars().contains(&i) {
                    let u: HashSet<_> = x.free_vars().union(&e.free_vars()).cloned().collect();
                    let ii = i.alphaRename(&u);
                    // TODO: Fix this thing. Needs to be an environment with a substituted variable
                    // let ee = e.subst(i, Var(ii), e);
                    Lam(ii, t.subst(v, x), Box::new(ee))
                }
            },
        }
    }
}

//substVar :: Sym -> Sym -> Expr -> Expr
// substVar s s' e = subst s (Var s') e
