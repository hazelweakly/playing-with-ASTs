// This crate is inspired by
// http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html
//
// Minor implementation details suggested by:
// https://gist.github.com/AndyShiue/55198c5a0137b62eb3d5
#[macro_use]
extern crate lazy_static;

use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;

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
        use Kinds::*;
        match e {
            Var(s) => self.find_var(s),
            App(f, a) => {
                let tf = self.clone().t_check_red(*f.clone())?;
                println!("tf: {:?}", tf.clone());
                match tf {
                    Pi(ref x, ref at, ref rt) => {
                        let ta = self.t_check(*a.clone())?;
                        println!(
                            "\nx: {:?}\nta: {:?}\nat: {:?}\nrt: {:?}",
                            x,
                            ta.clone(),
                            at.clone(),
                            rt.clone()
                        );
                        if !ta.beta_eq(*at.clone()) {
                            Err("Bad function argument type".to_string())
                        } else {
                            println!("subst: {:?}", a.clone().subst(&x.clone(), &*rt.clone()));
                            Ok(a.subst(&x, &*rt))
                        }
                    }
                    _ => {
                        // app needs a function
                        // functions are Pi types
                        println!("{:?} {:?}", f, a);
                        Err("Non-function in application".to_string())
                    }
                }
            }
            Lam(s, t, e) => {
                self.clone().t_check(*t.clone())?;
                let r = self.extend(s.clone(), *t.clone());
                let te = r.clone().t_check(*e)?;
                r.t_check(Pi(s, t, Box::new(te)))
            }
            Pi(x, a, b) => {
                let s = self.clone().t_check_red(*a.clone())?;
                let r = self.clone().extend(x, *a.clone());
                let t = r.clone().t_check_red(*b)?;
                if allowedKinds.contains(&(t.clone(), s.clone())) {
                    Ok(t)
                } else {
                    Err("Bad Abstraction".to_string())
                }
            }
            // If this is changed to return Kinds::Star and Bawx is removed, the type system will
            // have one level with Type in Type. This an inconsistent logic, but in it is
            // inconsistent in a meaningless way if your language is already turing complete.
            // (eg you're not losing anything you already gave up)
            Kind(Star) => Ok(Kind(Bawx)),
            // Change Bawx match to Kinds::Bawx to have kind in kind
            Kind(Bawx) => Ok(Kind(Bawx)),
            // Kind(Kinds::Bawx) => Err("Found a box".to_string()),
        }
    }

    pub fn type_check(e: Expr) -> Result<Type, String> {
        Env(HashMap::new()).t_check(e)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(Sym),
    App(Box<Expr>, Box<Expr>),
    Lam(Sym, Box<Type>, Box<Expr>),
    Pi(Sym, Box<Type>, Box<Type>),
    Kind(Kinds),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Kinds {
    Star,
    Bawx,
}

lazy_static! {
    static ref allowedKinds: Vec<(Type, Type)> = [
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

impl<'a> From<&'a str> for Expr {
    fn from(s: &str) -> Self {
        var(s)
    }
}

impl<'a> From<&'a str> for Sym {
    fn from(s: &str) -> Self {
        Sym(s.to_string())
    }
}

impl From<String> for Sym {
    fn from(s: String) -> Self {
        Sym(s)
    }
}

impl From<Sym> for String {
    fn from(s: Sym) -> Self {
        s.0
    }
}

impl fmt::Display for Sym {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
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
            Lam(s, t, e) => if s == *v {
                Lam(s, Box::new(t.subst(v, x)), e)
            } else {
                if x.free_vars().contains(&s) {
                    let i = s.alpha_rename(&x.free_vars().union(&e.free_vars()).cloned().collect());
                    Lam(
                        i.clone(),
                        Box::new(t.subst(v, x)),
                        Box::new(e.subst(&i.clone(), &Var(i))),
                    )
                } else {
                    Lam(s.clone(), Box::new(t.subst(v, x)), Box::new(e.subst(v, x)))
                }
            },
            Pi(s, k, t) => if s == *v {
                Pi(s, Box::new(k.subst(v, x)), t)
            } else {
                if x.free_vars().contains(&s) {
                    let i = s.alpha_rename(&x.free_vars().union(&t.free_vars()).cloned().collect());
                    Pi(
                        i.clone(),
                        Box::new(k.subst(v, x)),
                        Box::new(t.subst(&i.clone(), &Var(i))),
                    )
                } else {
                    Pi(s.clone(), Box::new(k.subst(v, x)), Box::new(t.subst(v, x)))
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
                (Lam(s, t, e), []) => lam(s, t.nf(), e.nf()),
                (Lam(s, _, e), _) => spine(es[0].clone().subst(&s, &e), &es[1..]),
                (Pi(s, k, t), _) => es
                    .iter()
                    .map(|t| t.clone().nf())
                    .fold(pi(s.clone(), k.clone().nf(), t.clone().nf()), |f, a| {
                        app(f, a.clone())
                    }),
                (f, _) => es
                    .iter()
                    .map(|e| e.clone().nf())
                    .fold(f, |f, a| app(f, a.clone())),
            }
        }

        spine(self, &[])
    }

    pub fn whnf(self) -> Self {
        use Expr::*;
        fn spine(ee: Expr, es: &[Expr]) -> Expr {
            match (ee, es) {
                (App(f, a), _) => spine(*f, &[&[*a], es].concat()),
                (Lam(ref s, _, ref e), _) if !es.is_empty() => {
                    spine(e.clone().subst(&s, &es[0]), &es[1..])
                }
                (Pi(ref s, _, ref t), _) if !es.is_empty() => {
                    spine(t.clone().subst(&s, &es[0]), &es[1..])
                }
                // (Pi(ref s, ref k, ref t), _) if !es.is_empty() => es
                //     .iter()
                //     .fold(pi(s.clone(), k.clone().whnf(), t.clone().whnf()), |f, a| {
                //         app(f, a.clone())
                //     }),
                (f, es) => es.iter().fold(f, |f, a| app(f, a.clone())),
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
            (Pi(s, _, t), Pi(ss, _, ee)) => t.alpha_eq(Var(s).subst(&ss, &*ee)),
            (Kind(k), Kind(kk)) => k == kk,
            (_, _) => false,
        }
    }

    pub fn beta_eq(self, v: Self) -> bool {
        self.nf().alpha_eq(v.nf())
    }
}

// Convenience functions for HOAS representation of the LC.
pub fn app(e: Expr, a: Expr) -> Expr {
    Expr::App(Box::new(e), Box::new(a))
}

// Specalization of pi to A -> B
pub fn arr(a: Expr, b: Expr) -> Expr {
    pi([a.to_string(), "₀".to_string()].concat(), a, b)
}

pub fn pi<S: Into<Sym>>(s: S, k: Expr, t: Expr) -> Expr {
    Expr::Pi(s.into(), Box::new(k), Box::new(t))
}

pub fn lam<S: Into<Sym>>(s: S, t: Expr, e: Expr) -> Expr {
    Expr::Lam(s.into(), Box::new(t), Box::new(e))
}

pub fn var<S: Into<String>>(s: S) -> Expr {
    Expr::Var(Sym(s.into()))
}

pub fn star() -> Expr {
    Expr::Kind(Kinds::Star)
}

pub fn bawx() -> Expr {
    Expr::Kind(Kinds::Bawx)
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Expr::*;
        use Kinds::*;
        fn pprint(e: &Expr) -> String {
            match e {
                Var(v) => v.to_string(),
                App(f, a) => format!("({} {})", pprint(&*f), pprint(&*a)),
                Lam(s, t, e) => format!("λ{}:{} {}", s, pprint(&*t), pprint(&*e)),
                Pi(s, k, t) => format!("Π({}:{} → {})", s, pprint(&*k), pprint(&*t)),
                Kind(k) => match k {
                    Star => "★".to_string(),
                    Bawx => "□".to_string(),
                },
            }
        };
        write!(f, "{}", pprint(self))
    }
}

// Test functions shamelessly stolen from the gist and adapted to work with the more advanced type
// system implemented here.
//
// Here just to have something to quickly give a sanity check that I didn't screw up too badly
// id : forall a.a -> a        <-- polymorphic version
// id = \(a:*) -> \(x:a) -> x  <-- dependently typed version

fn id() -> Expr {
    lam("a", star(), lam("x", var("a"), var("x")))
}

// The type of the identity function
fn id_t() -> Expr {
    pi("a", star(), pi("x", var("a"), var("a")))
}

// \a:* -> \b:* -> \x:a -> \y:b -> y
fn konst() -> Expr {
    lam(
        "a",
        star(),
        lam(
            "b",
            star(),
            lam("x", var("a"), lam("y", var("b"), var("y"))),
        ),
    )
}

fn id_coc() -> Expr {
    lam("a", star(), lam("p", pi("p", var("a"), star()), var("p")))
}

// (.) :: (b -> c) -> (a -> b) -> a -> c
// \ b:* -> \c:* ->
// \x -> \y -> \z xz yz
// \ x : (b -> c) -> \ y : (a -> b) -> \z:* -> app x (app z y)
// \f : B->C. \g: A->B. \x: A.f (g x)
// forall a:*, forall b:* forall c:*. (b-c) -> (a-b) -> a -> c
fn composition() -> Expr {
    // lam( "a", star(),
    //     lam( "b", star(),
    //         lam( "c", star(),
    //             lam( "f", arr(var("b"), var("c")),
    //                 lam( "g", arr(var("a"), var("b")),
    //                     lam("x", var("a"), app(var("f"), app(var("g"), var("x")))),
    //                 ),
    //             ),
    //         ),
    //     ),
    // )
    lam(
        "a",
        star(),
        lam(
            "b",
            star(),
            lam(
                "c",
                star(),
                lam(
                    "f",
                    arr(var("b"), var("c")),
                    lam(
                        "g",
                        arr(var("a"), var("b")),
                        lam("y", var("a"), app(var("f"), app(var("g"), var("y")))),
                    ),
                ),
            ),
        ),
    )
}

fn simple_subst() -> bool {
    let input = app(id(), var("y"));
    let output = var("y");

    (input.clone().whnf() == output) != (input == output)
}

fn should_rename() -> Expr {
    app(lam("x", star(), lam("z", star(), var("z"))), var("z"))
}

fn zero() -> Expr {
    lam("s", star(), lam("z", star(), var("z")))
}

fn one() -> Expr {
    lam("s", star(), lam("z", star(), app(var("s"), var("z"))))
}

fn two() -> Expr {
    lam(
        "s",
        star(),
        lam("z", star(), app(var("s"), app(var("s"), var("z")))),
    )
}

fn three() -> Expr {
    lam(
        "s",
        star(),
        lam(
            "z",
            star(),
            app(var("s"), app(var("s"), app(var("s"), var("z")))),
        ),
    )
}

fn plus() -> Expr {
    lam(
        "m",
        star(),
        lam(
            "n",
            star(),
            lam(
                "s",
                star(),
                lam(
                    "z",
                    star(),
                    app(
                        var("m"),
                        app(
                            app(var("m"), var("s")),
                            app(app(var("n"), var("s")), var("z")),
                        ),
                    ),
                ),
            ),
        ),
    )
}

fn main() {
    println!("{}", id().alpha_eq(id()));
    println!("{}", simple_subst());

    println!("{}\n{}\n{}\n{}", id(), konst(), id_coc(), composition());

    let s = Sym("this".to_string());
    let eq: Sym = "this".into();
    println!("{}", var(s).beta_eq(var(eq)));

    println!("id: {:?}", Env::type_check(id()));
    println!("{:?}", Env::type_check(konst()));
    println!("id_coc: {:?}", Env::type_check(id_coc()));

    println!("{}", should_rename().whnf());
    println!(
        "{}",
        app(lam("x", star(), lam("z", star(), var("z"))), var("z")).whnf()
    );
    println!("{}", lam("z'", star(), var("z")));

    println!("comp: {:?}", Env::type_check(composition()));
    println!("id_t: {:?}", Env::type_check(id_t()));
    println!("id_t: {}", id_t());

    println!("{}", arr(var("a"), var("b")));

    println!("0: {}\n1: {}\n2: {}\n3: {}", zero(), one(), two(), three());
    println!("2+2: {}", app(three(), app(plus(), two())).nf());
}
