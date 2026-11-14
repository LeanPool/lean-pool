/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Degree

/-!
# Filtered (affine) Hilbert functions with block degrees

Roy (DALAG Ch. 5, 8) works in a polynomial ring whose variables are split into blocks, and bounds
the
total degree in each block. Here `β : σ → ι` assigns each variable to a block, and
* `bdeg β m i` is the degree of the monomial `m` in block `i`;
* `S β D` is the set of monomials with `bdeg β m i ≤ D i` for every `i`;
* `FLE β D = restrictSupport K (S β D)` is the space of polynomials of block degree `≤ D`. It is
  finite-dimensional.

Main facts:
* `S_add_le`: `S D + S D' ⊆ S (D + D')`;
* `S_succ`: `S ((t+1) • D) = S (t • D) + S D`. This is the splitting lemma, proved by adding one
  variable at a time with a pigeonhole step;
* `FLE_mul_le` and `FLE_succ`: the corresponding statements for the spaces.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq ι]

/-- The degree of a monomial in block `i`. -/
def bdeg (β : σ → ι) (m : σ →₀ ℕ) (i : ι) : ℕ := ∑ s, if β s = i then m s else 0

omit [DecidableEq σ] in
theorem bdeg_add (β : σ → ι) (m n : σ →₀ ℕ) (i : ι) :
    bdeg β (m + n) i = bdeg β m i + bdeg β n i := by
  simp only [bdeg, Finsupp.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp

omit [DecidableEq σ] in
@[simp] theorem bdeg_zero (β : σ → ι) (i : ι) : bdeg β 0 i = 0 := by simp [bdeg]

omit [DecidableEq σ] in
theorem bdeg_single (β : σ → ι) (s : σ) (i : ι) :
    bdeg β (Finsupp.single s 1) i = if β s = i then 1 else 0 := by
  classical
  simp only [bdeg, Finsupp.single_apply]
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

omit [DecidableEq σ] in
theorem le_bdeg (β : σ → ι) (m : σ →₀ ℕ) (s : σ) : m s ≤ bdeg β m (β s) := by
  unfold bdeg
  rw [← Finset.sum_filter]
  exact Finset.single_le_sum (f := fun s => m s) (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- Monomials of block degree `≤ D`. -/
def S (β : σ → ι) (D : ι → ℕ) : Set (σ →₀ ℕ) := {m | ∀ i, bdeg β m i ≤ D i}

omit [DecidableEq σ] in
theorem S_mono (β : σ → ι) {D D' : ι → ℕ} (h : D ≤ D') : S β D ⊆ S β D' :=
  fun _ hm i => (hm i).trans (h i)

open scoped Pointwise in
omit [DecidableEq σ] in
theorem S_add_le (β : σ → ι) (D D' : ι → ℕ) : S β D + S β D' ⊆ S β (D + D') := by
  classical
  rintro _ ⟨m, hm, n, hn, rfl⟩ i
  rw [bdeg_add]
  exact add_le_add (hm i) (hn i)

omit [DecidableEq σ] in
/-- **Splitting, one step.** A monomial of block degree `≤ D' + D` is a sum of one of block degree
`≤ D'` and one of block degree `≤ D`. -/
theorem exists_split (β : σ → ι) (D D' : ι → ℕ) :
    ∀ m : σ →₀ ℕ, m ∈ S β (D' + D) → ∃ a ∈ S β D', ∃ b ∈ S β D, a + b = m := by
  classical
  intro m
  induction h : m.degree using Nat.strong_induction_on generalizing m with
  | _ k ih =>
  intro hm
  by_cases hm0 : m = 0
  · exact ⟨0, fun i => by simp, 0, fun i => by simp, by simp [hm0]⟩
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hm0 (Finsupp.ext hcon)
  have hle : Finsupp.single s 1 ≤ m := by
    intro x
    rw [Finsupp.single_apply]
    split_ifs with hx
    · subst hx; omega
    · exact Nat.zero_le _
  set m' := m - Finsupp.single s 1 with hm'
  have hmm : m' + Finsupp.single s 1 = m := tsub_add_cancel_of_le hle
  have hdeg : m'.degree < k := by
    rw [← h, ← hmm, map_add]; simp
  have hm'S : m' ∈ S β (D' + D) := fun i => by
    have := hm i; rw [← hmm, bdeg_add] at this; omega
  obtain ⟨a, ha, b, hb, hab⟩ := ih _ hdeg m' rfl hm'S
  by_cases hbs : bdeg β b (β s) < D (β s)
  · refine ⟨a, ha, b + Finsupp.single s 1, fun i => ?_, by rw [← add_assoc, hab, hmm]⟩
    rw [bdeg_add, bdeg_single]
    split_ifs with hi
    · subst hi; omega
    · simpa using hb i
  · refine ⟨a + Finsupp.single s 1, fun i => ?_, b, hb, by
      rw [add_right_comm, hab, hmm]⟩
    rw [bdeg_add, bdeg_single]
    split_ifs with hi
    · subst hi
      have h1 := hm (β s)
      rw [← hmm, ← hab, bdeg_add, bdeg_add, bdeg_single, ite_eq_left rfl] at h1
      have h2 := hb (β s)
      simp only [Pi.add_apply] at h1
      omega
    · simpa using ha i

open scoped Pointwise in
omit [DecidableEq σ] in
theorem S_add (β : σ → ι) (D D' : ι → ℕ) : S β (D' + D) = S β D' + S β D := by
  classical
  apply le_antisymm
  · intro m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_split β D D' m hm
    exact Set.add_mem_add ha hb
  · exact S_add_le β D' D

open scoped Pointwise in
omit [DecidableEq σ] in
theorem S_succ (β : σ → ι) (D : ι → ℕ) (t : ℕ) : S β ((t + 1) • D) = S β (t • D) + S β D := by
  classical
  rw [succ_nsmul, S_add]

omit [DecidableEq σ] in
theorem S_finite (β : σ → ι) (D : ι → ℕ) [Finite ι] : (S β D).Finite := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let N := ∑ i, D i
  have hsub : S β D ⊆ (Finsupp.equivFunOnFinite.symm) '' (Set.pi Set.univ fun _ : σ => Set.Iic
    N) := by
    intro m hm
    refine ⟨m, fun s _ => ?_, by simp⟩
    exact (le_bdeg β m s).trans ((hm (β s)).trans
      (Finset.single_le_sum (f := D) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)))
  exact ((Set.Finite.pi fun _ => Set.finite_Iic N).image _).subset hsub

variable (K : Type*) [Field K]

/-- Polynomials of block degree `≤ D`. -/
noncomputable abbrev FLE (β : σ → ι) (D : ι → ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K (S β D)

omit [DecidableEq σ] in
instance [Finite ι] (β : σ → ι) (D : ι → ℕ) : FiniteDimensional K (FLE K β D) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have : Finite (S β D) := (S_finite β D).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K (S β D))

omit [DecidableEq σ] in
theorem FLE_mono (β : σ → ι) {D D' : ι → ℕ} (h : D ≤ D') : FLE K β D ≤ FLE K β D' := by
  classical
  exact
    restrictSupport_mono K (S_mono β h)

omit [DecidableEq σ] in
theorem FLE_mul_le (β : σ → ι) (D D' : ι → ℕ) : FLE K β D * FLE K β D' ≤ FLE K β (D + D') := by
  classical
  rw [← restrictSupport_add]
  exact restrictSupport_mono K (S_add_le β D D')

omit [DecidableEq σ] in
theorem FLE_succ (β : σ → ι) (D : ι → ℕ) (t : ℕ) :
    FLE K β ((t + 1) • D) = FLE K β (t • D) * FLE K β D := by
  classical
  rw [FLE, S_succ, restrictSupport_add]

omit [DecidableEq σ] in
theorem mul_mem_FLE {β : σ → ι} {D D' : ι → ℕ} {P Q : MvPolynomial σ K} (hP : P ∈ FLE K β D)
    (hQ : Q ∈ FLE K β D') : P * Q ∈ FLE K β (D + D') := by
  classical
  exact
    FLE_mul_le K β D D' (Submodule.mul_mem_mul hP hQ)

end StrongSix.M2

end LeanPool
