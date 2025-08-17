-- import Mathlib.Data.Set.Defs -- { x | P x }
-- import Mathlib.Order.Notation -- Aᶜ
import Mathlib.Order.SetNotation -- ⋃, ⋂

namespace MyNote

open Set


--
-- 1 集合と写像


-- 1-1 集合の概念

-- 1-1-A) 集合と元

-- 集合A
variable {A : Type}

variable {A : Type}
variable {s t : Set A}

-- 集合Aの元a
-- a ∈ A
def a : A := sorry

-- 1-1-B) 集合の記法
def set1 {A : Type} {P : A → Prop} : Set A := { x | P x }
def set2 {P : A → Prop} : Set A := { x | P x }

-- 1-1-C) 集合の相等
def set_eq {A : Type} (a b : Set A) : Prop := a = b

-- 1-1-D) 部分集合
def ss1 {A : Type} (s t : Set A) : s ⊆ t := sorry
def ss2 : s ⊆ t := sorry


-- 1-2 集合の間の演算

-- 1-2-A) 和集合
def su1 {A : Type} (s t : Set A) : Set A := s ∪ t

-- 1-2-B) 共通部分
def sc1 {A : Type} (s t : Set A) : Set A := s ∩ t

-- 1-2-C) 差
def sd1 {A : Type} (s t : Set A) : Set A := s \ t

-- 1-2-D) 普遍集合
variable {X : Type}

-- def ac (a : A) : A := aᶜ -- エラーになる
def compl (s : Set A) : Set A := {a | a ∉ s}

-- 1-2-E) 集合系、べき集合

-- 1-2-F) 集合系の和集合、共通部分
def u1 {α I : Type} {A : I → Set α} : Set α := ⋃ i, A i
def i1 {α I : Type} {A : I → Set α} : Set α := ⋂ i, A i


-- 1-3 対応、写像

-- 1-3-A) 2つの集合の直積
-- 1-3-B) 対応の概念
-- 1-3-C) 対応のグラフ
-- 1-3-D) 逆対応

-- 1-3-E) 写像

-- 集合Aから集合Bへの写像f
def f : A → B := sorry


-- 1-4 写像に関する諸概念

-- 1-4-A) 写像による像および現像
-- 1-4-B) 全射、単射、全単射
-- 1-4-C) 写像の合成
-- 1-4-D) 写像の縮小、拡大
-- 1-4-E) 写像の終集合に関する注意
-- 1-4-F) 写像の集合


-- 1-5 添数づけられた族、一般の直積

-- 1-5-A) 元の無限列、有限列
-- 1-5-B) 元の族
-- 1-5-C) 集合族とその和集合、共通部分
-- 1-5-D) 一般の直積、選出公理
-- 1-5-E) 写像に関する一定理
-- 1-5-F) 多変数の写像
