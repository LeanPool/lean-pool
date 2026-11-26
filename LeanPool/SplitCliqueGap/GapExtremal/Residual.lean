/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
Ported (Lean 4.28 → 4.35, module system) from the B16 isolation development
(`C:/gap-cordal/verificacion/b16_aislamiento_20261004/source/RequestProject/Basic.lean`,
2026-10-04).
-/

@[expose] public section

/-!
# Pesos de columnas (`w`, `φ`, `w⁺`)

Definiciones básicas del modelo: para un grafo simple concreto `B : SimpleGraph V`
sobre un tipo finito `V` y una "columna" `S : Finset V`,

* `D B X Y` es el número de pares **ordenados** `(u,v) ∈ X × Y` adyacentes en `B`;
* `e B S` es el número de aristas de `B` con ambos extremos en `S`;
* `w B S = 2 * e B S - (S.card).choose 2 - 1` y `phi B S = 2 * e B S - (S.card).choose 2`;
* `wpos B S = max (w B S) 0`.

Todo está *definido* mediante fórmulas explícitas (nada postulado).
-/

namespace GapExtremal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Subgrafo de `B` inducido en `S`, visto como grafo sobre el mismo tipo de vértices. -/
def inducedOn (B : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := B.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance inducedOn.instDecidableRel (B : SimpleGraph V) [DecidableRel B.Adj] (S : Finset V) :
    DecidableRel (inducedOn B S).Adj := fun u v =>
  inferInstanceAs (Decidable (B.Adj u v ∧ u ∈ S ∧ v ∈ S))

/-- Número de pares **ordenados** `(u,v) ∈ X × Y` con `u` adyacente a `v` en `B`. -/
def D (B : SimpleGraph V) [DecidableRel B.Adj] (X Y : Finset V) : ℕ :=
  ∑ u ∈ X, ∑ v ∈ Y, if B.Adj u v then 1 else 0

/-- Número de aristas de `B` con ambos extremos en `S`. -/
def e (B : SimpleGraph V) [DecidableRel B.Adj] (S : Finset V) : ℕ :=
  (inducedOn B S).edgeFinset.card

/-- Peso de una columna: `w B S = 2 * e B S - C(|S|,2) - 1`. -/
def w (B : SimpleGraph V) [DecidableRel B.Adj] (S : Finset V) : ℤ :=
  2 * (e B S : ℤ) - ((S.card).choose 2 : ℤ) - 1

/-- `phi B S = 2 * e B S - C(|S|,2) = w B S + 1`. -/
def phi (B : SimpleGraph V) [DecidableRel B.Adj] (S : Finset V) : ℤ :=
  2 * (e B S : ℤ) - ((S.card).choose 2 : ℤ)

/-- Parte positiva del peso, `w⁺`. -/
def wpos (B : SimpleGraph V) [DecidableRel B.Adj] (S : Finset V) : ℤ := max (w B S) 0

variable (B : SimpleGraph V) [DecidableRel B.Adj]

lemma phi_eq_w_add_one (S : Finset V) : phi B S = w B S + 1 := by
  simp [phi, w]

lemma w_le_wpos (S : Finset V) : w B S ≤ wpos B S := le_max_left _ _

lemma wpos_nonneg (S : Finset V) : 0 ≤ wpos B S := le_max_right _ _

/-! ### `D` -/

omit [Fintype V] [DecidableEq V] in
lemma D_comm (X Y : Finset V) : D B X Y = D B Y X := by
  unfold D
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
    simp [SimpleGraph.adj_comm]

omit [Fintype V] in
lemma D_union_left {X X' Y : Finset V} (h : Disjoint X X') :
    D B (X ∪ X') Y = D B X Y + D B X' Y := by
  unfold D
  rw [Finset.sum_union h]

omit [Fintype V] in
lemma D_union_right {X Y Y' : Finset V} (h : Disjoint Y Y') :
    D B X (Y ∪ Y') = D B X Y + D B X Y' := by
  rw [D_comm, D_union_left B h, D_comm B Y X, D_comm B Y' X]

omit [Fintype V] [DecidableEq V] in
lemma D_empty_left (Y : Finset V) : D B ∅ Y = 0 := by simp [D]

omit [Fintype V] [DecidableEq V] in
lemma D_empty_right (X : Finset V) : D B X ∅ = 0 := by simp [D]

omit [Fintype V] [DecidableEq V] in
/-- Si no hay aristas entre `X` e `Y`, `D B X Y = 0`. -/
lemma D_eq_zero_of_no_edges {X Y : Finset V} (h : ∀ u ∈ X, ∀ v ∈ Y, ¬ B.Adj u v) :
    D B X Y = 0 := by
  unfold D
  refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => ?_
  simp [h u hu v hv]

omit [Fintype V] [DecidableEq V] in
lemma D_eq_sum_singleton_left (X Y : Finset V) : D B X Y = ∑ u ∈ X, D B {u} Y := by
  unfold D
  exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_singleton]

omit [Fintype V] [DecidableEq V] in
lemma D_self_singleton (a : V) : D B {a} {a} = 0 := by
  simp [D, SimpleGraph.irrefl]

omit [Fintype V] in
lemma D_biUnion_left {ι : Type*} (A : Finset ι) (f : ι → Finset V) (Y : Finset V)
    (hdisj : (A : Set ι).PairwiseDisjoint f) :
    D B (A.biUnion f) Y = ∑ a ∈ A, D B (f a) Y := by
  unfold D
  rw [Finset.sum_biUnion hdisj]

omit [Fintype V] in
lemma D_biUnion_right {ι : Type*} (A : Finset ι) (f : ι → Finset V) (X : Finset V)
    (hdisj : (A : Set ι).PairwiseDisjoint f) :
    D B X (A.biUnion f) = ∑ a ∈ A, D B X (f a) := by
  rw [D_comm, D_biUnion_left B A f X hdisj]
  exact Finset.sum_congr rfl fun a _ => D_comm B (f a) X

/-- `2 * e B S = D B S S`: cada arista interior se cuenta dos veces como par ordenado. -/
lemma two_mul_e_eq_D (S : Finset V) : 2 * e B S = D B S S := by
  classical
  rw [e, (inducedOn B S).two_mul_card_edgeFinset, D, Finset.card_filter,
    ← Finset.univ_product_univ, Finset.sum_product]
  rw [← Finset.sum_subset (Finset.subset_univ S) (by
    intro u _ hu
    refine Finset.sum_eq_zero ?_
    intro v _
    simp only [inducedOn]
    simp [hu])]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [← Finset.sum_subset (Finset.subset_univ S) (by
    intro v _ hv
    simp only [inducedOn]
    simp [hv])]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp only [inducedOn]
  simp [hu, hv]

/-- El peso escrito con pares ordenados. -/
lemma w_eq_D (S : Finset V) : w B S = (D B S S : ℤ) - ((S.card).choose 2 : ℤ) - 1 := by
  rw [w, ← two_mul_e_eq_D]
  push_cast
  ring

lemma phi_eq_D (S : Finset V) : phi B S = (D B S S : ℤ) - ((S.card).choose 2 : ℤ) := by
  rw [phi, ← two_mul_e_eq_D]
  push_cast
  ring

omit [Fintype V] [DecidableEq V] in
lemma D_self_eq_zero_of_card_le_one {S : Finset V} (h : S.card ≤ 1) : D B S S = 0 := by
  rcases Nat.lt_or_ge S.card 1 with h0 | h1
  · have hS : S = ∅ := Finset.card_eq_zero.mp (show S.card = 0 by omega)
    subst hS
    simp [D]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
    simp [D, SimpleGraph.irrefl]

/-- `phi` se anula en conjuntos de a lo sumo un elemento. -/
lemma phi_eq_zero_of_card_le_one {S : Finset V} (h : S.card ≤ 1) : phi B S = 0 := by
  rw [phi_eq_D, D_self_eq_zero_of_card_le_one B h]
  rcases Nat.lt_or_ge S.card 1 with h0 | h1
  · rw [show S.card = 0 by omega]
    simp
  · rw [show S.card = 1 by omega]
    simp

/-- Un conjunto con menos de tres elementos tiene peso `≤ 0`. -/
lemma w_nonpos_of_card_lt_three {S : Finset V} (h : S.card < 3) : w B S ≤ 0 := by
  rw [w_eq_D]
  have h012 : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases h012 with hc | hc | hc
  · rw [Finset.card_eq_zero] at hc
    subst hc
    simp [D]
  · have hD : D B S S = 0 := by
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      simp [D, SimpleGraph.irrefl]
    rw [hD, hc]
    norm_num
  · have hD : D B S S ≤ 2 := by
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
      unfold D
      rw [Finset.sum_pair hab, Finset.sum_pair hab, Finset.sum_pair hab]
      simp only [SimpleGraph.irrefl, ite_false]
      split <;> split <;> simp
    rw [hc]
    have : (D B S S : ℤ) ≤ 2 := by exact_mod_cast hD
    norm_num
    linarith

/-- `w⁺` se anula en conjuntos de menos de tres elementos. -/
lemma wpos_eq_zero_of_card_lt_three {S : Finset V} (h : S.card < 3) : wpos B S = 0 :=
  max_eq_right (w_nonpos_of_card_lt_three B h)

/-- Si `w⁺ B S ≠ 0` entonces `S` es una columna (tiene al menos tres elementos). -/
lemma three_le_card_of_wpos_ne_zero {S : Finset V} (h : wpos B S ≠ 0) : 3 ≤ S.card := by
  by_contra hc
  exact h (wpos_eq_zero_of_card_lt_three B (by omega))

/-- Si `w B S > 0` entonces `S` es una columna. -/
lemma three_le_card_of_w_pos {S : Finset V} (h : 0 < w B S) : 3 ≤ S.card := by
  by_contra hc
  exact absurd h (not_lt.mpr (w_nonpos_of_card_lt_three B (by omega)))

end GapExtremal
