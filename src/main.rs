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
    pub fn free_vars(&self) -> HashSet<&Sym> {
        use Expr::*;
        match *self {
            Var(ref s) => [s].iter().map(|&s| s).collect(),
            App(ref f, ref a) => f.free_vars().union(&a.free_vars()).cloned().collect(),
            Lam(ref i, ref t, ref e) => t
                .free_vars()
                .union(
                    &e.free_vars()
                        .difference(&[i].iter().map(|&i| i).collect())
                        .cloned()
                        .collect(),
                )
                .cloned()
                .collect(),
            Pi(ref i, ref k, ref t) => k
                .free_vars()
                .union(
                    &t.free_vars()
                        .difference(&[i].iter().map(|&i| i).collect())
                        .cloned()
                        .collect(),
                )
                .cloned()
                .collect(),
            Kind(_) => HashSet::new(),
        }
    }

    pub fn subst(self, v: &Sym, x: &Self) -> Self {
        use Expr::*;
        match self {
            Var(i) => if i == *v {
                x.clone()
            } else {
                Var(i)
            },
            App(f, a) => App(Box::new(f.subst(v, x)), Box::new(a.subst(v, x))),
            Lam(i, t, e) => if i == *v {
                Lam(i, Box::new(t.subst(v, x)), e)
            } else {
                if x.free_vars().contains(&i) {
                    let i = i.alpha_rename(&x.free_vars().union(&e.free_vars()).cloned().collect());
                    Lam(
                        i.clone(),
                        Box::new(t.subst(v, x)),
                        Box::new(e.subst(&i.clone(), &Var(i))),
                    )
                } else {
                    Lam(i.clone(), Box::new(t.subst(v, x)), Box::new(e.subst(v, x)))
                }
            },
            Pi(i, t, e) => if i == *v {
                Pi(i, Box::new(t.subst(v, x)), e)
            } else {
                if x.free_vars().contains(&i) {
                    let i = i.alpha_rename(&x.free_vars().union(&e.free_vars()).cloned().collect());
                    Pi(
                        i.clone(),
                        Box::new(t.subst(v, x)),
                        Box::new(e.subst(&i.clone(), &Var(i))),
                    )
                } else {
                    Pi(i.clone(), Box::new(t.subst(v, x)), Box::new(e.subst(v, x)))
                }
            },
            Kind(k) => Kind(k),
        }
    }
}

//substVar :: Sym -> Sym -> Expr -> Expr
// substVar s s' e = subst s (Var s') e
