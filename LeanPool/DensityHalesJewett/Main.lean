/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.Varnavides
public import Mathlib.Computability.Ackermann
public import Mathlib.Order.Lattice.Nat
import LeanPool.DensityHalesJewett.Ackermann
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt

/-!
# The density theorems

The density Hales--Jewett theorem, Szemerédi's theorem and Varnavides' theorem, each with the
Ackermann function as the bound.

* `Combinatorics.Line.exists_of_density`: over `k` letters, in every dimension
  `n ≥ ack (4 * k) (k + ⌈1 / δ⌉₊)`, every set of words of density `δ` contains a combinatorial
  line.
* `Combinatorics.ArithmeticProgression.exists_of_density_nat`: for
  `n ≥ ack (4 * k + 1) (k + ⌈1 / δ⌉₊)`, every subset of `range n` of density `δ` contains an
  arithmetic progression of length `k`.
* `Combinatorics.ArithmeticProgression.exists_many_of_density_nat`: for the same `n`, it contains
  at least `n ^ 2 / ack (4 * k + 1) (k + ⌈1 / δ⌉₊)` of them.

The least threshold for the first theorem is the density Hales--Jewett number
`Combinatorics.Line.dhjNumber k δ`, so it is at most `ack (4 * k) (k + ⌈1 / δ⌉₊)`.
-/

@[expose] public section

open Finset
open Combinatorics

namespace Combinatorics.Line

/-- The density theorem for alphabets with at most one letter. -/
lemma exists_of_density_card_le_one {α : Type*} [Fintype α]
    (hα : Fintype.card α ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 1 ≤ n) {A : Finset (Fin n → α)}
    (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  let : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hα
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  use Line.diagonal α (Fin n)
  intro x
  have hcard : Fintype.card α = 1 :=
    Fintype.card_eq_one_of_forall_eq fun y ↦ Subsingleton.elim y x
  rw [hcard] at hAδ
  norm_num at hAδ
  obtain ⟨w, hw⟩ : A.Nonempty := card_pos.mp <| by
    exact_mod_cast hδ.trans_le hAδ
  simpa [Subsingleton.elim (Line.diagonal α (Fin n) x) w] using hw

/-- Transport the finite-alphabet density theorem across the canonical alphabet equivalence. -/
lemma exists_of_density_card_ge_two {α : Type*} [Fintype α]
    (hα : 2 ≤ Fintype.card α) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : ack (4 * Fintype.card α) (Fintype.card α + ⌈1 / δ⌉₊) ≤ n)
    {A : Finset (Fin n → α)} (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  let e := Fintype.equivFin α
  let wordEquiv : (Fin n → α) ≃ (Fin n → Fin (Fintype.card α)) :=
    (Equiv.refl (Fin n)).arrowCongr e
  let B := A.map wordEquiv.toEmbedding
  obtain ⟨l, hl⟩ := DensityHalesJewett.isDHJBound_ack hα δ hδ n hn B (by grind)
  use l.map e.symm
  intro x
  specialize hl (e x)
  rw [mem_map_equiv] at hl
  change (e.symm ∘ l (e x)) ∈ A at hl
  rwa [← e.symm_apply_apply x, Combinatorics.Line.map_apply]

/-- The **density Hales--Jewett theorem**: over a finite alphabet `α` of `k` letters, in every
dimension `n ≥ ack (4 * k) (k + ⌈1 / δ⌉₊)`, every set of at least a `δ` fraction of the words
contains a combinatorial line. -/
theorem exists_of_density {α : Type*} [Fintype α] {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : ack (4 * Fintype.card α) (Fintype.card α + ⌈1 / δ⌉₊) ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  by_cases hα : 2 ≤ Fintype.card α
  · exact exists_of_density_card_ge_two hα hδ hn hAδ
  · exact exists_of_density_card_le_one (by grind) hδ ((ack_pos _ _).trans_le hn) hAδ

/-- The **density Hales--Jewett number** of `k` letters and density `δ`: the least `N` such that
density Hales--Jewett holds for `k` letters and density `δ` in every dimension `n ≥ N`. If there is
no such `N`, it is `0`, the value of `sInf ∅`; by `dhjNumber_le_ack` this can only happen for
`δ ≤ 0`. -/
noncomputable def dhjNumber (k : ℕ) (δ : ℝ) : ℕ :=
  sInf {N | ∀ n, N ≤ n → DensityHalesJewett.IsDHJDimension k δ n}

private lemma ack_mem (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ack (4 * k) (k + ⌈1 / δ⌉₊) ∈ {N | ∀ n, N ≤ n → DensityHalesJewett.IsDHJDimension k δ n} :=
  fun n hn A hA ↦ exists_of_density hδ (by simpa using hn) A (by simpa using hA)

/-- The density Hales--Jewett number is below the Ackermann function at level `4 * k`. -/
theorem dhjNumber_le_ack (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    dhjNumber k δ ≤ ack (4 * k) (k + ⌈1 / δ⌉₊) :=
  Nat.sInf_le (ack_mem k hδ)

/-- In every dimension `n ≥ dhjNumber k δ`, every set of at least `δ * k ^ n` words of length `n`
over `k` letters contains a combinatorial line. -/
theorem exists_of_dhjNumber_le {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : dhjNumber k δ ≤ n) (A : Finset (Fin n → Fin k)) (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ l : Line (Fin k) (Fin n), ∀ x, l x ∈ A :=
  Nat.sInf_mem ⟨_, ack_mem k hδ⟩ n hn A hA

end Combinatorics.Line

namespace Combinatorics.ArithmeticProgression

open DensityHalesJewett AckBounded

/-- A threshold for Szemerédi's theorem for progressions of length `k + 2`, a fixed number of
applications of `ack (4 * k + 5)` above a bound `N` for `1 / δ`. -/
private lemma exists_threshold (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {s c N : ℕ} (hs : k + 4 ≤ s)
    (hN : AckBounded (4 * k + 5) s c N) (hδN : 1 / δ ≤ N) :
    ∃ m, AckBounded (4 * k + 5) s (max 1 c + 5) m ∧
      ∀ n, m ≤ n → ∀ A : Finset ℕ, A ⊆ range n → δ * n ≤ #A →
        ∃ P : ArithmeticProgression ℕ (k + 2), P.IsSubset A := by
  have hM : 5 ≤ 4 * k + 5 := by omega
  obtain ⟨d, hd, hdb⟩ := exists_isDHJDimension_ackBounded k (half_pos hδ) le_rfl hs
    ((num hM 2).mul hM hN) (one_div_half_le hδN)
  refine ⟨2 * (k + 2) ^ d * N, ?_, ?_⟩
  · exact (((num hM 2).mul hM ((of_le (by omega : k + 2 ≤ s)).pow hM hdb)).mul hM hN).mono
      (by omega)
  · intro n hn A hAn hA
    refine exists_of_isDHJDimension (by omega) hδ hd ?_ A hAn hA
    calc 2 * ((k + 2 : ℕ) : ℝ) ^ d / δ = 2 * ((k + 2 : ℕ) : ℝ) ^ d * (1 / δ) := by ring
      _ ≤ 2 * ((k + 2 : ℕ) : ℝ) ^ d * N := by gcongr
      _ ≤ n := by exact_mod_cast hn

/-- **Szemerédi's theorem**: for `k ≥ 3` and `n ≥ ack (4 * k + 1) (k + ⌈1 / δ⌉₊)`, every subset of
`range n` with at least `δ * n` elements contains an arithmetic progression of length `k`. -/
theorem exists_of_density_nat {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : ack (4 * k + 1) (k + ⌈1 / δ⌉₊) ≤ n) (A : Finset ℕ) (hAn : A ⊆ range n)
    (hAδ : δ * n ≤ #A) : ∃ P : ArithmeticProgression ℕ k, P.IsSubset A := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 2 ≤ k)
  obtain ⟨m, hm, h⟩ := exists_threshold k hδ (le_max_left _ ⌈1 / δ⌉₊) (of_le (le_max_right _ _))
    (Nat.le_ceil _)
  refine h n (le_trans ?_ hn) A hAn hAδ
  exact (hm.le_ack (by omega) (by norm_num) (by omega)).trans
    (ack_max_le (Nat.ceil_pos.2 (by positivity)))

/-- **Varnavides' theorem**: for `k ≥ 3` and `n ≥ ack (4 * k + 1) (k + ⌈1 / δ⌉₊)`, every subset of
`range n` with at least `δ * n` elements contains at least
`n ^ 2 / ack (4 * k + 1) (k + ⌈1 / δ⌉₊)` arithmetic progressions of length `k`. -/
theorem exists_many_of_density_nat {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : ack (4 * k + 1) (k + ⌈1 / δ⌉₊) ≤ n) (A : Finset ℕ) (hAn : A ⊆ range n)
    (hA : δ * n ≤ #A) :
    (n : ℝ) ^ 2 / ack (4 * k + 1) (k + ⌈1 / δ⌉₊) ≤ #(containedProgressions k n A) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (by grind : 2 ≤ k)
  set N := ⌈1 / δ⌉₊
  have hM : 5 ≤ 4 * k + 5 := by grind
  have hs := of_le (M := 4 * k + 5) (le_max_right (k + 4) N)
  obtain ⟨m, hm, hS⟩ := exists_threshold k (half_pos hδ) (le_max_left _ N)
    ((num hM 2).mul hM hs) (one_div_half_le (Nat.le_ceil _))
  have hm' : AckBounded (4 * k + 5) (max (k + 4) N) 8 (m + 1) :=
    (hm.add hM (num hM 1)).mono (by grind)
  refine sq_div_le_card_containedProgressions (by grind) hδ m.succ_pos
    (fun B ↦ hS _ m.le_succ B) (Nat.le_ceil _) ?_ hn A hAn hA
  exact ((((num hM 128).mul hM (hm'.pow hM (num hM 3))).mul hM (hs.pow hM (num hM 2))).le_ack
    (by grind) (by grind) (by grind)).trans (ack_max_le (Nat.ceil_pos.2 (by positivity)))

end Combinatorics.ArithmeticProgression
