Typeのことが何となく分かったところで、\
`Lean`で数学のあれこれを書いてみると…。

## 集合

```lean
-- 集合A
variable (A : Type)
```
`A`があって、その`A`のtypeが`Type`。\
つまり「集合\\(A\\)」みたいなもの

```lean
-- Aの要素a
variable (a : A)
```
`a`の`type`は`A : Type`ということを表している、\
つまり\\( a \in A \\)に対応している

### 写像

```lean
variable (B : Type)

-- AからBへの写像f
variable (f : A → B)
```
`f`のtypeは`A → B`、つまり集合\\(A\\)から集合\\(B\\)への写像みたいなもの

```lean
-- 一気に書くと
def g {C : Type} {D : Type} : C → D := sorry
```
`{ ... }`は、その定義の前提みたいなもの。\
集合\\(C\\)、集合\\(D\\)があるとき、…みたいなもの

`C`とか`D`とかを、`variable`で別に定義しなくても、\
`{C : Type}`などと書くと、その定義内で`C : Type`として扱われる。



```lean
-- もっと省略すると
def h : E → F := sorry
```

## 集合関連続き

### 族

```lean
-- 族

variable (Λ : Type)

-- Aの元の族
variable (A : Λ → Type)
```
添字集合\\(Λ\\)から別の集合への写像の集合\\(A\\)

```lean
-- 直積
def dependent_product := ∀ x : Λ, A x

-- ∀が分かりにくければ、
def dependent_product__ := (x : Λ) → A x
-- ∀ x, ... はxを受け取って...を返す関数と考えられる

-- 一気に書くと
def dependent_product_ {Λ : Type} {A : Λ → Type} := ∀ x : Λ, A x

-- 選択公理
axiom axiomOfChoice {r : ∀ x, A x → Prop} (h : ∀ x, ∃ y, r x y) : ∃ (f : ∀ x, A x), ∀ x, r x (f x)

-- 一気に書くと
axiom axiomOfChoice_ {α : Type} {β : α → Type} {r : ∀ x, β x → Prop} (h : ∀ x, ∃ y, r x y) : ∃ (f : ∀ x, β x), ∀ x, r x (f x)
```
