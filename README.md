# Playing with ASTs

This repository will detail the adventures of attempting to recreate the lambda cube in Rust.
Hopefully, in a way that allows for much more generic and useful traversal of the AST.
We'll see what happens when Rust's borrow checker starts to make things interesting.

(This is my final project for PSU's CS410P Rust elctive class)

## Project Report

It was fairly smooth to get some basic code translation from Haskell to Rust
done and I had some decently handy references with which to get started.
However, some interesting difficulties that I encountered were that, as I chose
to do things in a slightly richer language and it happened to be just rich
enough that I ended up with a lambda calculus system written up with no damn
idea how to actually write anything in it or test it... So that was
interesting. (That would be why my speed of commits dropped drastically as
I started having to read a lot of papers to figure out what I should be writing
to begin to test it rather than being able to add new features or keep plowing
forward)

There's also a weird bug hidden somewhere in the code, which is preventing
addition from working in the language. It's either in the type checker, or the
whnf/nf functions, or whatever; but probably the type checker. Unfortunately,
it's driving me nuts--partially because I'm only mostly certain that it's
actually a bug and not my inability to write out the correct functions in
lambda-cube.

Overall, 5/7, a perfect score, would Rusty my language again.

Next up in the feature-set would be switching to a Trait based system to
implement only specific subsets of the lambda cube (which is a fantastic idea
I saw done well [here](https://github.com/AndyShiue/pts)), and using HOAS with
closures to make the lambda/pi bit easier.
