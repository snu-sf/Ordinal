# Ordinal Numbers in Coq

We define ordinal numbers as follows.
```
  Inductive t: Type :=
  | build (A: Type) (os: A -> t)
  .

  Inductive le: t -> t -> Prop :=
  | le_intro
      A0 A1 os0 os1
      (LE: forall (a0: A0), exists (a1: A1), le (os0 a0) (os1 a1))
    :
      le (build os0) (build os1)
  .

  Variant lt: t -> t -> Prop :=
  | lt_intro
      o A os (a: A)
      (LE: le o (os a))
    :
      lt o (build os)
  .
```
This definition enjoys a lot of properties of ordinal numbers in set theory.
`< (=lt)` is [well-founded](https://github.com/minkiminki/Ordinal/blob/main/src/Ordinal.v#L158), and [successor ordinals](https://github.com/minkiminki/Ordinal/blob/main/src/Ordinal.v#L377) and [limit ordinals](https://github.com/minkiminki/Ordinal/blob/main/src/Ordinal.v#L453-L456) exist.
Also, we can define
[embedding from any well-ordered type](https://github.com/minkiminki/Ordinal/blob/main/src/Ordinal.v#L677-L678), [ordinal arithmetic](https://github.com/minkiminki/Ordinal/blob/main/src/Arithmetic.v) and [recursive functions](https://github.com/minkiminki/Ordinal/blob/main/src/Ordinal.v#L742-L746) whose domains are ordinal numbers.

Up to this point (`Ordinal.v`, `Arithmetic.v`), every proof can be done costructively. (without any axiom)
However, some facts about ordinals in classical mathematics cannot be proven constructively.
Actually, totalness of `<` is [equivalent](https://github.com/minkiminki/Ordinal/blob/main/src/Totalness.v) to LEM.

For that reason, classical axioms (excluded middle, axiom of choice, axiom K, proof irrelevance, propositional extensionality and functional extensionality) are used in some files.
With axioms, we can define [cardinals](https://github.com/minkiminki/Ordinal/blob/main/src/Cardinal.v) as special ordinals
and prove the existence of an [inaccessible cardinal](https://github.com/minkiminki/Ordinal/blob/main/src/Inaccessible.v)

Furthermore, many useful theorems *not about ordinals* can be proved.
- [The well ordering theorem](https://github.com/minkiminki/Ordinal/blob/main/src/WellOrdering.v)
- [Zorn's lemma](https://github.com/minkiminki/Ordinal/blob/main/src/WellOrdering.v)
- [The Bourbaki–Witt fixed point theorem](https://github.com/minkiminki/Ordinal/blob/main/src/WellOrdering.v) and its application for an initial algebra / final coalgebra
