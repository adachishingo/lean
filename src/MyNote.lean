import Mathlib.Data.Set.Defs -- Set, 𝒫
import Mathlib.Order.SetNotation -- ⋃, ⋂
-- import Mathlib.Tactic.FinCases -- sᶜ, f⁻¹', g ∘' f
import Mathlib.Data.Nat.Basic -- ℕ
import Mathlib.Data.Set.Basic  -- Disjoint

namespace MyNote

open Set

-- 1 集合と写像


-- 1-1 集合の概念


-- 1-1-A) 集合と元

-- 集合 A'
variable {A' : Type}

-- 集合 A' の元 a'
-- a' ∈ A'
variable {a' : Set A'}


-- 1-1-B) 集合の記法
-- { x | P x}
def set1 {A : Type} {P : A → Prop} : Set A := { x | P x }


-- 1-1-C) 集合の相等
def set_eq {A : Type} (a b : Set A) : Prop := a = b


-- 1-1-D) 部分集合
-- s ⊆ t
def subset {A : Type} (s t : Set A) : Prop := ∀ ⦃x⦄, x ∈ s → x ∈ t

notation s " ⊆' " t => subset s t

def subset1 {A : Type} (s t : Set A) : s ⊆' t := sorry

-- ⊆ が Lean で定義済み
def subset2 {A : Type} (s t : Set A) : s ⊆ t := sorry


-- 1-2 集合の間の演算

-- 1-2-A) 和集合
-- s ∪ t
def union {A : Type} (s t : Set A) : Set A := { x | x ∈ s ∨ x ∈ t }

notation s " ∪' " t => union s t

def union1 {A : Type} (s t : Set A) : Set A := s ∪' t

-- ∪ が Lean で定義済み
def union2 {A : Type} (s t : Set A) : Set A := s ∪ t


-- 1-2-B) 共通部分
-- s ∩ t
def inter {A : Type} (s t : Set A) : Set A := { x | x ∈ s ∧ x ∈ t }

notation s " ∩' " t => inter s t

def inter1 {A : Type} (s t : Set A) : Set A := s ∩' t

-- ∩ が Lean で定義済み
def inter2 {A : Type} (s t : Set A) : Set A := s ∩ t


-- 1-2-C) 差
-- s \ t
def diff {A : Type} (s t : Set A) : Set A := { x | x ∈ s ∧ x ∉ t }

notation s " \\' " t => diff s t

def diff1 {A : Type} (s t : Set A) : Set A := s \' t

-- \ が Lean で定義済み
def diff2 {A : Type} (s t : Set A) : Set A := s \ t


-- 1-2-D) 普遍集合
variable {X : Type}

-- 補集合
-- sᶜ
def compl {A : Type} (s : Set A) : Set A := {a | a ∉ s}

postfix:max "ᶜ'" => compl

def compl1 {A : Type} (s : Set A) : Set A := sᶜ'

-- import Mathlib.Tactic.FinCases などで使用可能
-- FIXME sᶜをどこで定義しているのか不明
-- def compl2 {A : Type} (s : Set A) : Set A := sᶜ


-- 1-2-E) 集合系、べき集合

-- 集合系 集合の元が集合となっている集合
def set_family (A : Type) : Type := Set (Set A)

-- X のすべての部分集合の集合
def power_set {A : Type} (s : Set A) : Set (Set A) := { t | t ⊆ s }

notation " 𝒫' " s => power_set s  -- 𝒫: script capital P

-- 𝒫 は定義済み
def power_set1 {A : Type} (x : Set A) : Set (Set A) := 𝒫 x


-- 1-2-F) 集合系の和集合、共通部分

-- 集合系の和集合
def Union_family {A : Type} (F : Set (Set A)) : Set A :=
  { x | ∃ s ∈ F, x ∈ s }

notation " ⋃ " F => Union_family F

def unionfamily1 {A : Type} (F : Set (Set A)) : Set A := ⋃ F

-- 集合系の共通部分
def Inter_family {A : Type} (F : Set (Set A)) : Set A :=
  { x | ∀ s ∈ F, x ∈ s }

notation " ⋂ " F => Inter_family F

def interfamily1 {A : Type} (F : Set (Set A)) : Set A := ⋂ F

-- ⋃, ⋂は別の意味で Mathlib.Order.SetNotation に定義済み
-- def u1 {α I : Type} {A : I → Set α} : Set α := ⋃ i, A i
-- def i1 {α I : Type} {A : I → Set α} : Set α := ⋂ i, A i


-- 1-3 対応、写像


-- 1-3-A) 2つの集合の直積
def prod_set {A B : Type} (s : Set A) (t : Set B) : Set (A × B) :=
  { p | p.1 ∈ s ∧ p.2 ∈ t }

-- A x B は Lean で定義済み
def prod1 {A B : Type} (s : Set A) (t : Set B) : Set (A × B) := prod_set s t


-- 1-3-B) 対応の概念
def correspondence (A : Type) (B : Type) : Type :=
  Set (A × B)


-- 1-3-C) 対応のグラフ
def graph_of_function {A B : Type} (f : A → B) : Set (A × B) :=
  { (a, f a) | a ∈ Set.univ }


-- 1-3-D) 逆対応
def inverse_correspondence {A B : Type} (R : Set (A × B)) : Set (B × A) :=
  { (b, a) | (a, b) ∈ R }


-- 1-3-E) 写像

-- 集合Aから集合Bへの写像f
def f1 {A B : Type} : A → B := sorry


-- 1-4 写像に関する諸概念


-- 1-4-A) 写像による像および現像
-- 像
def image {A B : Type} (f : A → B) (s : Set A) : Set B :=
  { b | ∃ a ∈ s, f a = b }

-- 現像（逆像）
def preimage {A B : Type} (f : A → B) (t : Set B) : Set A :=
  { a | f a ∈ t }

notation f " ⁻¹'' " t => preimage f t

def preimage1 {A B : Type} (f : A → B) (t : Set B) : Set A := f⁻¹'' t

-- ⁻¹'は定義済み
-- def preimage2 {A B : Type} (f : A → B) (t : Set B) : Set A := f⁻¹' t


-- 1-4-B) 全射、単射、全単射
-- 単射
def injective {A B : Type} (f : A → B) : Prop :=
  ∀ ⦃x y : A⦄, f x = f y → x = y

-- 全射
def surjective {A B : Type} (f : A → B) : Prop :=
  ∀ y : B, ∃ x : A, f x = y

-- 全単射
def bijective {A B : Type} (f : A → B) : Prop :=
  injective f ∧ surjective f


-- 1-4-C) 写像の合成
def compose {A B C : Type} (g : B → C) (f : A → B) : A → C :=
  fun x => g (f x)

infixr:80 " ∘'' " => compose

def compose1 {A B C : Type} (f : A → B) (g : B → C) : A → C := g ∘'' f

-- ∘'は定義済み
-- def compose2 {A B C : Type} (f : A → B) (g : B → C) : A → C := g ∘' f


-- 1-4-D) 写像の縮小、拡大
def restrict {A B : Type} (f : A → B) (s : Set A) : { a // a ∈ s } → B :=
  fun a_sub => f a_sub.val

def extend {A B : Type} (s : Set A) [DecidablePred (· ∈ s)] (f : { a // a ∈ s } → B) (b0 : B) : A → B :=
  fun a => if h : a ∈ s then f ⟨a, h⟩ else b0

-- 1-4-E) 写像の終集合に関する注意
def restrict_codomain {A B : Type} {B' : Set B} (f : A → B)
  (h : ∀ a : A, f a ∈ B') : A → { b // b ∈ B' } :=
fun a => ⟨f a, h a⟩

-- 1-4-F) 写像の集合
def map_set (A B : Type) : Set (A → B) := Set.univ  -- 全写像の集合

def map_set_condition (A B : Type) (P : (A → B) → Prop) : Set (A → B) :=
  { f | P f }

def char_func {A : Type} (S : Set A) [DecidablePred (· ∈ S)] : A → Bool :=
  fun a => if a ∈ S then true else false

-- 1-5 添数づけられた族、一般の直積

-- 1-5-A) 元の無限列、有限列
def sequence (A : Type) := ℕ → A

def map_fin_to_A {A : Type} (n : Nat) := Fin n → A

-- 1-5-B) 元の族
def family (Λ A : Type) := Λ → A

-- 1-5-C) 集合族とその和集合、共通部分
def family_of_sets (Λ : Type) := Λ → Type

def union_family {Λ : Type} (a : family_of_sets Λ) : Type :=
  Σ (i : Λ), a i

-- FIXME
-- def inter_family {Λ A : Type} (F : family_of_sets Λ A) : Set A :=
--   { x | ∀ i : Λ, x ∈ F i }


-- 1-5-D) 一般の直積、選出公理
def general_product {Λ : Type} (A : Λ → Type) : Type :=
  ∀ i : Λ, A i

def axiom_of_choice :=
  ∀ {ι : Type} {A : ι → Type}, (∀ i, Nonempty (A i)) → Nonempty (∀ i, A i)

-- 1-5-E) 写像に関する一定理

-- a) fが全射である ⇔ ある写像s : B → Aが存在し f ∘ s = id_B
def exists_right_inverse {A B : Type} (f : A → B) : Prop :=
  ∃ s : B → A, (∀ b : B, f (s b) = b)

theorem surjective_iff_right_inverse :
  surjective f → exists_right_inverse f :=
sorry  -- 証明省略

-- b) fが単射である ⇔ ある写像r : B → Aが存在し r ∘ f = id_A
def exists_left_inverse {A B : Type} (f : A → B)  : Prop :=
  ∃ r : B → A, (∀ a : A, r (f a) = a)

theorem injective_iff_left_inverse  {A B : Type} (f : A → B) :
  injective f → exists_left_inverse f :=
sorry  -- 証明省略

def exists_injective (A B : Type) : Prop :=
  ∃ f : A → B, Function.Injective f

def exists_surjective (A B : Type)  : Prop :=
  ∃ g : B → A, Function.Surjective g

theorem inj_iff_surj  (A B : Type) :
  exists_injective A B ↔ exists_surjective A B :=
sorry -- 証明省略

-- 1-5-F) 多変数の写像
-- 演算
def operation {M : Type} : M → M → M := sorry


-- 1-6 同値関係


-- 1-6-A) 関係の概念
def Rel (α : Type) := α → α → Prop

-- 1-6-B) 同値関係
-- 反射性 (Reflexive)
variable (R : Rel α)
def Reflexive := ∀ a, R a a

-- 対称性 (Symmetric)
def Symmetric := ∀ a b, R a b → R b a

-- 反対称性 (Antisymmetric)
def Antisymmetric := ∀ a b, R a b → R b a → a = b

-- 推移性 (Transitive)
def Transitive := ∀ a b c, R a b → R b c → R a c

-- 同値関係
def Equivalence (R : Rel α) :=
  Reflexive R ∧ Symmetric R ∧ Transitive R

-- f による像が一致するとき、Rel a b として関係を定義
def inducedEquiv {α β : Type} (f : α → β) : Rel α :=
  fun a b => f a = f b

-- 付随する同値関係
theorem inducedEquiv_is_equivalence {α β : Type} (f : α → β) :
  Equivalence (inducedEquiv f) := by
  unfold Equivalence Reflexive Symmetric Transitive inducedEquiv
  exact ⟨
    fun a => rfl,                          -- Reflexive: f a = f a
    fun a b h => h.symm,                  -- Symmetric: f a = f b → f b = f a
    fun a b c hab hbc => hab.trans hbc    -- Transitive: f a = f b ∧ f b = f c → f a = f c
  ⟩

-- 直和分割の定義
def isDisjointUnion {α ι : Type _} (parts : ι → Set α) (A : Set α) : Prop :=
  (⋃ i, parts i) = A ∧                  -- 1. 被覆
  (∀ i j, i ≠ j → Disjoint (parts i) (parts j))  -- 2. 互いに素

-- 直和分割に付随する同値関係
def relOfPartition {α ι : Type _} (parts : ι → Set α) : Rel α :=
  fun x y => ∃ i, x ∈ parts i ∧ y ∈ parts i


-- 1-6-C) 同値類、商集合
-- 同値類1
def equivClass {α : Type _} (R : α → α → Prop) (a : α) : Set α :=
  { x | R x a }

-- 同値類2
def classOf (R : Rel α) (a : α) : Set α := fun x => R x a

-- 商集合
def quotientSet (R : α → α → Prop) : Set (Set α) :=
  { C | ∃ a, C = classOf R a }

-- 自然な写像、あるいは標準的な写像1
def canonicalMap (R : α → α → Prop) (a : α) : Set α :=
  classOf R a

-- 自然な写像、あるいは標準的な写像2 (Quot を使用)
def canonicalMap' {α : Type _} (R : α → α → Prop) : α → Quot R :=
  Quot.mk R


-- 1-6-D) 写像の分解
-- f に付随する同値関係
-- def R' {A B : Type} (f : A → B) (a1 a2 : A) : A → B := f a1 = f a2

-- -- 商集合への射影
-- def π : A → Quot R := Quot.mk R'

-- -- overline_f : Quot R → V(f)
-- def overline_f : Quot R → Set.range f := Quot.lift f (λ a b h, h)

-- -- 像の包含写像
-- def i : Set.range f → B := id

def π {A : Type} (R : A → A → Prop) (a : A) : Set A :=
  classOf R a

noncomputable def overline_f {A B : Type} (f : A → B) (R : A → A → Prop)
  (C : Set A)
  (exists_rep : ∃ a, C = classOf R a) : B :=
  let a := Classical.choose exists_rep
  f a
