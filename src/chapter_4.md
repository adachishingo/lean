```lean
-- 慣れてきたので、mathlibにあわせて`Type`の代わりに`Type u`を使う

-- 実数ℝⁿの距離空間
class MetricSpace (α : Type u) where
  dist : α → α → ℝ
  dist_nonneg : ∀ x y, dist x y ≥ 0
  dist_eq_zero : ∀ x y, dist x y = 0 ↔ x = y
  dist_comm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z
  IsOpen : Set α → Prop

-- Xを距離空間とする
variable {X : Type u}
variable [MetricSpace X]

-- 開集合
def IsOpen : Set X → Prop := MetricSpace.IsOpen

-- 内点全部の集合（内部、開核）
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
```

```lean
-- 位相空間

-- 位相構造
class TopologicalStructure (X : Type u) where
  𝒪 : Set (Set X) -- 位相
  univ_mem : Set.univ ∈ 𝒪
  empty_mem : ∅ ∈ 𝒪
  sUnion_mem : ∀ S : Set (Set X), (∀ U ∈ S, U ∈ 𝒪) → ⋃₀ S ∈ 𝒪

-- 𝒪に属するSの部分集合を開集合という
def isOpen {X : Type u} [T : TopologicalStructure X] (U : Set X) : Prop :=
  U ∈ T.𝒪

-- 開核作用子 (interior operator) の定義
def interior_  {X : Type u} [TopologicalStructure X] (M : Set X) : Set X :=
  ⋃₀ { U : Set X | isOpen U ∧ U ⊆ M }

-- 閉集合
def isClosed {X : Type u} [TopologicalStructure X] (A : Set X) : Prop :=
  isOpen (Aᶜ)

-- 閉包作用子
def closure {X : Type u} [TopologicalStructure X] (M : Set X) : Set X :=
  ⋂₀ { U : Set X | isClosed U ∧ U ⊆ M }

-- 近傍
def isNeighborhood {X : Type u} [TopologicalStructure X] (x : X) (V : Set X) : Prop :=
  ∃ U : Set X, isOpen U ∧ x ∈ U ∧ U ⊆ V

-- 位相の強弱
def isStrongerThan {X : Type u} (T₁ T₂ : TopologicalStructure X) : Prop :=
  T₂.𝒪 ⊆ T₁.𝒪

def isWeakerThan {X : Type u} (T₁ T₂ : TopologicalStructure X) : Prop :=
  T₁.𝒪 ⊆ T₂.𝒪

-- 位相の生成
def generatedTopology {X : Type u} (ℳ : Set (Set X)) : Set (Set X) :=
  ⋂₀ { 𝒯 : Set (Set X) | 
        Set.univ ∈ 𝒯 ∧
        ∅ ∈ 𝒯 ∧
        (∀ U V, U ∈ 𝒯 → V ∈ 𝒯 → U ∩ V ∈ 𝒯) ∧
        (∀ S : Set (Set X), S ⊆ 𝒯 → ⋃₀ S ∈ 𝒯) ∧
        ℳ ⊆ 𝒯 }

-- 準基底
structure Prebasis (X : Type u) where
  sets : Set (Set X)
  covers : ⋃₀ sets = Set.univ

-- 基底
structure Basis (X : Type u) where
  sets : Set (Set X)
  covers : ⋃₀ sets = Set.univ
  inter_basis : ∀ (B₁ B₂ : Set X), B₁ ∈ sets → B₂ ∈ sets → 
                ∀ (x : X), x ∈ B₁ ∩ B₂ → ∃ (B₃ : Set X), B₃ ∈ sets ∧ x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂

def is_countable (S : Set (Set X)) : Prop :=
  ∃ f : ℕ → Set X, S = Set.range f

-- 第二可算公理
structure SecondCountableSpace (X : Type u) extends Basis X where
  countable_basis : is_countable sets

-- 基本近傍系
structure BasicNeighborhoodSystem (X : Type u) [T : TopologicalStructure X] where
  neighborhood_base : X → Set (Set X)  -- 各点の基本近傍系
  mem_nh : ∀ x, ∀ B ∈ neighborhood_base x, x ∈ B
  base_is_filter : ∀ x, ∀ U, isNeighborhood x U →
    ∃ B ∈ neighborhood_base x, B ⊆ U

-- 第一可算公理
structure FirstCountableSpace (X : Type u) [T : TopologicalStructure X] where
  basic_nh : BasicNeighborhoodSystem X
  countable_nh : ∀ x : X, is_countable (basic_nh.neighborhood_base x)

-- 密、稠密(Dense)
def isDense {X : Type u} [TopologicalStructure X] (A : Set X) : Prop :=
  closure A = Set.univ

-- 位相空間
structure TopologicalSpace (X : Type u) where
  toTopologicalStructure : TopologicalStructure X

-- この位相空間を使って、開集合の定義すると…
def isOpen_ {X : Type u} (T : TopologicalSpace X) (U : Set X) : Prop :=
  U ∈ T.toTopologicalStructure.𝒪
  -- T.toTopologicalStructure. がいちいち余計になる…
```
