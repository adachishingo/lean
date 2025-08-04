# Lean入門

`Lean`のコードを読んだり書いたりしても\
いまいち分かったような分からないような感じでした。

ですが、次のことを知った時は一番いろんなものがしっくりきました。

----

## term と type

Leanが採用している型理論では、すべてがtermである。

また、すべてのtermは、typeを持つ。

  

例えば、

```lean
π : ℝ
```

は、`π`がtype `ℝ`のtermであることを表す。

このことは、集合を使った数学の
\\[ \pi \in \mathbb{R} \\]
に対応し、
`π`が実数であることを表す。

----

## 2つのuniverse

### universe Type

すべてのtermはtypeを持つ。

`ℝ`のtypeは`Type`というuniverse typeである。

- universe: `Type`
- type: 例えば群\\(G\\)
- term: 例えば群\\(G\\)の要素\\(g\\)

のような3層の階層があると考えることができる。

### universe Prop

この universe `Type` の他に、
universe `Prop` がある。

 この universe `Prop`では、

- universe: `Prop`
- type: 命題
- term: 証明

となる。

----

## 参考になったサイト

- [Mathematics in type theory.](https://xenaproject.wordpress.com/2020/06/20/mathematics-in-type-theory/)
- [Formalising Mathematics (Types and terms 他)](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2022/Part_B/typesandterms.html)
