/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/IndependentFamily.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ConservativeExtension
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Independent Family
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IndependentFamily

noncomputable def fresh (b : Degree) : Degree :=
  Classical.choose (ConservativeExtension.exists_conservative_degree b)

theorem fresh_spec (b : Degree) : ¬ fresh b ≤ b ∧
    ∀ a y : Degree, a ≤ b → y ≤ b → y ≤ a ⊔ fresh b → y ≤ a :=
  Classical.choose_spec (ConservativeExtension.exists_conservative_degree b)

noncomputable def tower (b : Degree) : ℕ → Degree
  | 0 => b
  | n+1 => tower b n ⊔ fresh (tower b n)

noncomputable def column (b : Degree) (n : ℕ) : Degree := fresh (tower b n)

theorem tower_mono (b : Degree) : Monotone (tower b) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_sup_left

theorem base_le (b : Degree) (n : ℕ) : b ≤ tower b n := tower_mono b (Nat.zero_le n)

theorem column_le {b : Degree} {i n : ℕ} (hi : i < n) : column b i ≤ tower b n :=
  le_trans (show column b i ≤ tower b (i+1) from le_sup_right) (tower_mono b hi)

theorem finite_le {b : Degree} {F : Finset ℕ} {n : ℕ}
    (hF : ∀ i ∈ F, i < n) : F.sup (column b) ≤ tower b n := by
  apply Finset.sup_le
  intro i hi
  exact column_le (hF i hi)

theorem finite_conservative (b : Degree) (n : ℕ) (F : Finset ℕ)
    (hF : ∀ i ∈ F, i < n) (a y : Degree) (ha : a ≤ b) (hy : y ≤ b)
    (h : y ≤ a ⊔ F.sup (column b)) : y ≤ a := by
  classical
  induction n generalizing F with
  | zero =>
    have he : F = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => by
      have := hF i hi; omega)
    simpa [he] using h
  | succ n ih =>
    by_cases hn : n ∈ F
    · have he : F = insert n (F.erase n) := (Finset.insert_erase hn).symm
      have hsmall : ∀ i ∈ F.erase n, i < n := by
        intro i hi
        have hh := Finset.mem_erase.mp hi
        have := hF i hh.2
        omega
      have hh : y ≤ (a ⊔ (F.erase n).sup (column b)) ⊔ column b n := by
        rw [he, Finset.sup_insert] at h
        simpa only [sup_assoc, sup_comm, sup_left_comm] using h
      have hd := (fresh_spec (tower b n)).2 _ _
        (sup_le (ha.trans (base_le b n)) (finite_le hsmall))
        (hy.trans (base_le b n)) hh
      exact ih (F.erase n) hsmall hd
    · apply ih F (fun i hi => ?_) h
      have := hF i hi
      have : i ≠ n := fun he => hn (he ▸ hi)
      omega

theorem column_membership (b : Degree) (n : ℕ) (F : Finset ℕ)
    (hF : ∀ j ∈ F, j < n) (i : ℕ) (hi : i < n)
    (h : column b i ≤ b ⊔ F.sup (column b)) : i ∈ F := by
  classical
  induction n generalizing F i with
  | zero => omega
  | succ n ih =>
    by_cases hin : i = n
    · subst i
      by_contra hn
      have hsmall : ∀ j ∈ F, j < n := by
        intro j hj
        have := hF j hj
        have : j ≠ n := fun he => hn (he ▸ hj)
        omega
      exact (fresh_spec (tower b n)).1
        (h.trans (sup_le (base_le b n) (finite_le hsmall)))
    · have hi' : i < n := by omega
      by_cases hn : n ∈ F
      · have he : F = insert n (F.erase n) := (Finset.insert_erase hn).symm
        have hsmall : ∀ j ∈ F.erase n, j < n := by
          intro j hj
          have hh := Finset.mem_erase.mp hj
          have := hF j hh.2
          omega
        have hh : column b i ≤ (b ⊔ (F.erase n).sup (column b)) ⊔ column b n := by
          rw [he, Finset.sup_insert] at h
          simpa only [sup_assoc, sup_comm, sup_left_comm] using h
        have hd := (fresh_spec (tower b n)).2 _ _
          (sup_le (base_le b n) (finite_le hsmall)) (column_le hi') hh
        exact Finset.mem_of_mem_erase (ih _ hsmall _ hi' hd)
      · apply ih F (fun j hj => ?_) i hi' h
        have := hF j hj
        have : j ≠ n := fun he => hn (he ▸ hj)
        omega

theorem independence (b : Degree) (a₀ a₁ : Degree) (h₀ : a₀ ≤ b) (h₁ : a₁ ≤ b)
    (i : ℕ) (F : Finset ℕ) :
    a₀ ⊔ column b i ≤ a₁ ⊔ F.sup (column b) ↔ a₀ ≤ a₁ ∧ i ∈ F := by
  classical
  let n := max (i+1) (F.sup id + 1)
  have hi : i < n := lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)
  have hF : ∀ j ∈ F, j < n := by
    intro j hj
    have hj' : j ≤ F.sup id := Finset.le_sup (f := id) hj
    exact lt_of_lt_of_le (Nat.lt_succ_of_le hj') (le_max_right _ _)
  constructor
  · intro h
    refine ⟨finite_conservative b n F hF a₁ a₀ h₁ h₀ (le_sup_left.trans h), ?_⟩
    exact column_membership b n F hF i hi
      (le_sup_right.trans (h.trans (sup_le_sup_right h₁ _)))
  · rintro ⟨ha, hi⟩
    exact sup_le_sup ha (Finset.le_sup hi)

theorem column_injective (b : Degree) : Function.Injective (column b) := by
  intro i j hij
  have h := (independence b ⊥ ⊥ bot_le bot_le i {j}).mp (by simp [hij])
  simpa using h.2

end TuringRigidity.IndependentFamily

end OAI
