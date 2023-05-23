# Ordinal Numbers in Coq

This project contains a definition of ordinal numbers, and useful operators and theorms for them.
The basic definition was already in the literature.
The datatype for ordinals is identical to aczel trees, and the chapter 10 in the HOTT book contains same definitions and properties of ordering on ordinals.

# Code Structure
- [Ordinal.v](https://github.com/minkiminki/Ordinal/blob/main/src/Ordinal.v): basic defintions
- [Arithmetic.v](https://github.com/minkiminki/Ordinal/blob/main/src/Arithmetic.v): ordinal arithmetic
- [ClassicOrdinal.v](https://github.com/minkiminki/Ordinal/blob/main/src/ClassicOrdinal.v) and [Totalness.v](https://github.com/minkiminki/Ordinal/blob/main/src/Totalness.v): classical facts about ordinals
- [Cardinal.v](https://github.com/minkiminki/Ordinal/blob/main/src/Cardinal.v): cardinals
- [WellOrdering.v](https://github.com/minkiminki/Ordinal/blob/main/src/WellOrdering.v), [Zorn.v](https://github.com/minkiminki/Ordinal/blob/main/src/Zorn.v) and [Fixedpoint.v](https://github.com/minkiminki/Ordinal/blob/main/src/Fixedpoint.v): corollary

If you are finding a general well-founded ordered structure, definitions in `Ordinal.v` and `Arithmetic.v` (sometimes, `ClassicalOrdinal`) will be a good choice.
If you are looking for more set-theoretical things, other files will be interesting, too.

Note that files other than `Ordinal.v`, `Arithmetic.v` and `ClassicOrdinal.v` are experimental and not maintained well.

## Basic definitions - [Ordinal.v](https://github.com/minkiminki/Ordinal/blob/main/src/Ordinal.v) (axiom-free)
Below is the mathematical representation of the ordinal used in this project.
```
Inductive Ord.t :=
| Ord.build: forall (A: Type), (A -> Ord.t) -> Ord.t
.
```
Intuitively, an ordinal in `Ord.t` is a tree with possibly infinite branches,
and its maximum "depth" corresponds to an ordinal in the set theory.

There is ordering (`Ord.le`, `Ord.lt`, and `Ord.eq`) with desired properties (including well-foundness of `Ord.lt`). The ordering compares maximum depths between two ordinals.
```
Inductive Ord.le: t -> t -> Prop :=
| Ord.le_intro
    A0 A1 os0 os1
    (LE: forall (a0: A0), exists (a1: A1), Ord.le (os0 a0) (os1 a1))
  :
    Ord.le (build os0) (build os1)
.

Variant Ord.lt: t -> t -> Prop :=
| Ord.lt_intro
    o A os (a: A)
    (LE: Ord.le o (os a))
  :
    Ord.lt o (build os)
.

Definition Ord.eq (o0 o1: Ord.t): Prop := Ord.le o0 o1 /\ Ord.le o1 o0.
```
Totalness of this ordering is [equivalent](https://github.com/minkiminki/Ordinal/blob/main/src/Totalness.v) to excluded_middle,
and thus it is not included in `Ordinal.v`.

The following and basic combinators:
- Zero `Ord.O: Ord.t`,
- Successor `Ord.S: Ord.t -> Ord.t`
- A join of an indexed family of ordinals. Note that a limit ordinal is a special case of a join where a family of ordinals are unbounded.
`join: forall (A: Type), (A -> Ord.t) -> Ord.t // = ∨_{\forall a \in A}(os a)`

There is an embedding `Ord.from_nat: nat -> Ord.t` from natural numbers to `Ord.v`.
Furthermore, any well-founded type can be embedded into `Ord.v` using `Ord.from_wf`.
```
Ord.from_wf: forall (A: Type) (R: A -> A -> Prop) (WF: well_founded R), A -> Ord.t
```

There is no unique representation for a mathematical ordinal.
For example, `o0 := @Ord.join bool (fun _ => Ord.O)` and `o1 := @Ord.join unit (fun _ => Ord.O)` are corresponding to the same mathematical ordinal 0 and
`Ord.eq o0 o1` holds, but `o0 = o1` is not true.


## Transfinite Recursion and Arithmetic - [Ordinal.v](https://github.com/minkiminki/Ordinal/blob/main/src/Ordinal.v) and [Arithmetic.v](https://github.com/minkiminki/Ordinal/blob/main/src/Arithmetic.v) (axiom-free)
Transfinite recursive function:
```
Ord.rec: forall (D: Type) (base: D) (next: D -> D) (join: forall (A: Type), (A -> D) -> D), Ord.t -> D
```
and its special case, a generator for recursive functions on ordinals:
```
Ord.orec: forall (base: Ord.t) (next: Ord.t -> Ord.t), Ord.t -> Ord.t
```
`Ord.orec` is very useful for defining other ordinal functions.
`OrdArith.add`, `OrdArith.mult`, and `OrdArith.expn` in `Arithmetic.v` are defined using `Ord.orec`, and even aleph numbers can be defined using `Ord.orec` (`aleph` in `Cardinal.v`).

## Ordinal + axiom - [ClassicOrdinal.v](https://github.com/minkiminki/Ordinal/blob/main/src/ClassicOrdinal.v) and others (axiom used)
The law of excluded middle is imported in [ClassicOrdinal.v](https://github.com/minkiminki/Ordinal/blob/main/src/ClassicOrdinal.v),
and we get classical facts about ordinals. 
- totalness of ordering (`Lemma ClassicOrd.total`)
- case analysis (`Lemma limit_or_S`)
- more "standard" transfinite induction (`Lemma ClassicOrd.ind`)

More axioms are used in other files (excluded middle, axiom of choice, axiom K, proof irrelevance, propositional extensionality and functional extensionality).
With axioms, we can define [cardinals](https://github.com/minkiminki/Ordinal/blob/main/src/Cardinal.v) as special ordinals
and prove the existence of an [inaccessible cardinal](https://github.com/minkiminki/Ordinal/blob/main/src/Inaccessible.v).

## Interesting Results (axiom used)
Furthermore, many useful theorems *not about ordinals* can be proved.
- [The well ordering theorem](https://github.com/minkiminki/Ordinal/blob/main/src/WellOrdering.v)
- [Zorn's lemma](https://github.com/minkiminki/Ordinal/blob/main/src/Zorn.v)
- [The Bourbaki–Witt fixed point theorem](https://github.com/minkiminki/Ordinal/blob/main/src/Fixedpoint.v) and its application for an initial algebra / final coalgebra

# Installation
```
# from opam
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-ordinal
```
or you can build manually
```
# from source
git clone git@github.com:minkiminki/Ordinal.git
cd Ordinal
opam pin .
```
