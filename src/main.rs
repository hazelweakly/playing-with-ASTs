// This crate is inspired by
// http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html
//
// Minor implementation details suggested by:
// https://gist.github.com/AndyShiue/55198c5a0137b62eb3d5
#[macro_use]
extern crate lazy_static;

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sym(String);

type Type = Expr;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Env(HashMap<Sym, Type>);

impl Env {
    fn find_var(self, s: Sym) -> Result<Type, String> {
        match self.0.get(&s) {
            Some(t) => Ok(t.clone()),
            None => Err(format!("Cannot find variable {}", s.0)),
        }
    }

    fn extend(mut self, s: Sym, t: Type) -> Self {
        self.0.insert(s, t);
        self
    }

    // normalizes results + type checks
    // tCheckRed r e = liftM whnf (tCheck r e)
    fn t_check_red(self, e: Expr) -> Result<Type, String> {
        Ok(self.t_check(e)?.whnf())
    }

    fn t_check(self, e: Expr) -> Result<Type, String> {
        use Expr::*;
        match e {
            Var(s) => self.find_var(s),
            App(f, a) => {
                let tf = self.clone().t_check_red(*f)?;
                if let Pi(x, at, rt) = tf {
                    let ta = self.t_check(*a.clone())?;
                    if !ta.beta_eq(*at) {
                        return Err("Bad function argument type".to_string());
                    }
                    return Ok(a.subst(&x, &*rt));
                }
                return Err("Non-function in application".to_string());
            }
            Lam(s, t, e) => {
                if self.clone().t_check(*t.clone()).is_ok() {
                    let r = self.extend(s.clone(), *t.clone());
                    let te = r.clone().t_check(*e)?;
                    let lt = Pi(s, t, Box::new(te));
                    if r.t_check(lt.clone()).is_ok() {
                        Ok(lt)
                    } else {
                        Err("extended environment is not well typed".to_string())
                    }
                } else {
                    Err("Lambda is not well typed".to_string())
                }
            }
            Pi(x, a, b) => {
                if self.clone().t_check_red(*a.clone()).is_ok() {
                    let r = self.clone().extend(x, *a.clone());
                    let t = r.t_check_red(*b)?;
                    if let Some(tt) = allowedKinds.get(&self.t_check_red(*a)?) {
                        if *tt != t {
                            return Err("Bad Abstraction".to_string());
                        }
                    };
                    Ok(t)
                } else {
                    Err("self did not type check".to_string())
                }
            }
            // If this is changed to return Kinds::Star and Bawx is removed, the type system will
            // have one level with Type in Type. This an inconsistent logic, but in it is
            // inconsistent in a meaningless way if your language is already turing complete.
            // (eg you're not losing anything you already gave up)
            Kind(Kinds::Star) => Ok(Kind(Kinds::Bawx)),
            // Change Bawx match to Kinds::Bawx to have kind in kind
            Kind(Kinds::Bawx) => Err("Found a box".to_string()),
        }
    }
}

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

lazy_static! {
    static ref allowedKinds: HashMap<Type, Type> = [
        (Expr::Kind(Kinds::Star), Expr::Kind(Kinds::Star)),
        (Expr::Kind(Kinds::Star), Expr::Kind(Kinds::Bawx)),
        (Expr::Kind(Kinds::Bawx), Expr::Kind(Kinds::Star)),
        (Expr::Kind(Kinds::Bawx), Expr::Kind(Kinds::Bawx)),
    ]
        .iter()
        .cloned()
        .collect();
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
                ).cloned()
                .collect(),
            Pi(ref i, ref k, ref t) => k
                .free_vars()
                .union(
                    &t.free_vars()
                        .difference(&[i].iter().map(|&i| i).collect())
                        .cloned()
                        .collect(),
                ).cloned()
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

    pub fn nf(self) -> Self {
        use Expr::*;
        fn spine(ee: Expr, es: &[Expr]) -> Expr {
            match (ee, es) {
                (App(f, a), _) => spine(*f, &[&[*a], es].concat()),
                (Lam(s, t, e), []) => Lam(s, Box::new(t.nf()), Box::new(e.nf())),
                (Lam(s, _, e), es) => spine(es[0].clone().subst(&s, &e), &es[1..]),
                (f, es) => es
                    .iter()
                    .map(|e| e.clone().nf())
                    .fold(f, |f, a| App(Box::new(f), Box::new(a.clone()))),
            }
        }

        spine(self, &[])
    }

    pub fn whnf(self) -> Self {
        use Expr::*;
        fn spine(ee: Expr, es: &[Expr]) -> Expr {
            match (ee, es) {
                (App(f, a), _) => spine(*f, &[&[*a], es].concat()),
                (Lam(s, _, e), _) => spine(es[0].clone().subst(&s, &e), &es[1..]),
                (f, es) => es
                    .iter()
                    .fold(f, |f, a| App(Box::new(f), Box::new(a.clone()))),
            }
        }

        spine(self, &[])
    }

    pub fn alpha_eq(self, v: Self) -> bool {
        use Expr::*;
        match (self, v) {
            (Var(f), Var(ff)) => f == ff,
            (App(f, a), App(ff, aa)) => f.alpha_eq(*ff) && a.alpha_eq(*aa),
            (Lam(s, _, e), Lam(ss, _, ee)) => e.alpha_eq(Var(s).subst(&ss, &*ee)),
            (Pi(s, _, e), Pi(ss, _, ee)) => e.alpha_eq(Var(s).subst(&ss, &*ee)),
            (Kind(k), Kind(kk)) => k == kk,
            (_, _) => false,
        }
    }

    pub fn beta_eq(self, v: Self) -> bool {
        self.nf().alpha_eq(v.nf())
    }
}

// Test functions shamelessly stolen from the gist and adapted to work with the more advanced type
// system implemented here.
//
// Here just to have something to quickly give a sanity check that I didn't screw up too badly
fn i_comb() -> Expr {
    use Expr::*;
    use Kinds::*;
    Lam(
        Sym("a".to_string()),
        Box::new(Kind(Star)),
        Box::new(
            Lam(
                Sym("x".to_string()),
                Box::new(Kind(Bawx)),
                Box::new(Var(Sym("x".to_string())))
            )
            )
    )
}

fn simple_subst() -> bool {
    use Expr::*;
    let input = App(
        Box::new(i_comb()),
        Box::new(Var(Sym("y".to_string())))
    );
    let output = Var(Sym("y".to_string()));

    input.whnf() == output
}

fn main() {
    println!("{}", i_comb().alpha_eq(i_comb()));
    println!("{}", simple_subst());
}
