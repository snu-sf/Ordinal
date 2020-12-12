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
`< (=lt)` is [well-founded](https://github.com/minkiminki/Ordinal/blob/main/src/Constructive.v#L133), and [successor ordinals](https://github.com/minkiminki/Ordinal/blob/main/src/Constructive.v#L431) and [limit ordinals](https://github.com/minkiminki/Ordinal/blob/main/src/Constructive.v#L531) exist.

There are two versions of developments, one with classical axioms and one without.
## [With classical axioms](https://github.com/minkiminki/Ordinal/blob/main/src/Classical.v)
Many classical axioms are used here. (excluded middle, axiom of choice, axiom K, proof irrelevance, propositional extensionality and functional extensionality)
[Totalness of `<`](https://github.com/minkiminki/Ordinal/blob/main/src/Classical.v#L228), the existence of an [inaccessible cardinal](https://github.com/minkiminki/Ordinal/blob/main/src/Classical.v#L3509) and a lot of interesting things can be proved in this version.

Furthermore, many useful theorems *not about ordinals* can be proved.
- [The well ordering theorem](https://github.com/minkiminki/Ordinal/blob/main/src/Classical.v#L3999-L4003)
- [Zorn's lemma](https://github.com/minkiminki/Ordinal/blob/main/src/Classical.v#L4048-L4049)
- [The Bourbaki–Witt fixed point theorem](https://github.com/minkiminki/Ordinal/blob/main/src/Classical.v#L4602-L4603)
- and its application for an [initial algebra](https://github.com/minkiminki/Ordinal/blob/main/src/Classical.v#L4635-L4636) / [final coalgebra](https://github.com/minkiminki/Ordinal/blob/main/src/Classical.v#L4635-L4636)

## [Without classical axioms](https://github.com/minkiminki/Ordinal/blob/main/src/Constructive.v)
No axiom is used here. We can not prove totalness of `<` without AOC or LEM. (Actually, totalness of `<` may imply LEM and a weaker form of AOC)
However, we can still do many things. We can define
[embedding from any well-ordered type](https://github.com/minkiminki/Ordinal/blob/main/src/Constructive.v#L273-L274), [ordinal arithmetic](https://github.com/minkiminki/Ordinal/blob/main/src/Constructive.v#L1187) and [recursive functions](https://github.com/minkiminki/Ordinal/blob/main/src/Constructive.v#L666) whose domains are ordinal numbers.
