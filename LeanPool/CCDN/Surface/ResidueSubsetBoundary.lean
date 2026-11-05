/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith

/-! Finite subset selection for the residue cover. A minimal modulus
crosses its target by at most one prime factor. A change of containment
then occurs across a single deletion edge. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

/-- If a finite set `P` of positive integers bounded by `U` has product at least `X > 1`, then
it contains a nonempty subset `R` with product at least `X` and less than `U X`, all of whose
proper subsets have product less than `X`. -/
theorem exists_minimal_product_subset (P : Finset ℕ) {X U : ℝ}
    (hX : 1 < X) (hP : ∀ p ∈ P, (0 : ℝ) < p)
    (hU : ∀ p ∈ P, (p : ℝ) ≤ U)
    (hprod : X ≤ ∏ p ∈ P, (p : ℝ)) :
    ∃ R : Finset ℕ, R ⊆ P ∧ R.Nonempty ∧ X ≤ ∏ p ∈ R, (p : ℝ) ∧
      (∀ T ⊂ R, (∏ p ∈ T, (p : ℝ)) < X) ∧
      (∏ p ∈ R, (p : ℝ)) < U * X := by
  classical
  let S := P.powerset.filter (fun R : Finset ℕ => X ≤ ∏ p ∈ R, (p : ℝ))
  have hS : S.Nonempty := ⟨P, mem_filter.mpr ⟨mem_powerset.mpr (Subset.refl _), hprod⟩⟩
  obtain ⟨R, hRS, hmin⟩ := S.exists_min_image Finset.card hS
  obtain ⟨hRP, hRX⟩ := mem_filter.mp hRS
  have hRP' : R ⊆ P := mem_powerset.mp hRP
  have hRne : R.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, prod_empty] at hRX
    linarith
  have hproper : ∀ T ⊂ R, (∏ p ∈ T, (p : ℝ)) < X := by
    intro T hTR
    by_contra hn
    have hTS : T ∈ S := mem_filter.mpr
      ⟨mem_powerset.mpr (hTR.subset.trans hRP'), le_of_not_gt hn⟩
    exact (not_le_of_gt (card_lt_card hTR)) (hmin T hTS)
  refine ⟨R, hRP', hRne, hRX, hproper, ?_⟩
  obtain ⟨p, hp⟩ := hRne
  have hsmall := hproper (R.erase p) (erase_ssubset hp)
  have hmul := mul_lt_mul_of_pos_left hsmall (hP p (hRP' hp))
  rw [mul_prod_erase R _ hp] at hmul
  exact hmul.trans_le (mul_le_mul_of_nonneg_right (hU p (hRP' hp)) (by linarith))

/-- Any property false at the empty node and true at a terminal node
changes across a one-element subset edge. -/
theorem exists_subset_erase_boundary {α : Type*} [DecidableEq α] (R : Finset α)
    (W : Finset α → Prop) (hempty : ¬ W ∅) (hR : W R) :
    ∃ T : Finset α, T ⊆ R ∧ ∃ p ∈ T, W T ∧ ¬ W (T.erase p) := by
  classical
  let S := R.powerset.filter W
  have hS : S.Nonempty := ⟨R, mem_filter.mpr ⟨mem_powerset.mpr (Subset.refl _), hR⟩⟩
  obtain ⟨T, hTS, hmin⟩ := S.exists_min_image Finset.card hS
  obtain ⟨hTR, hWT⟩ := mem_filter.mp hTS
  have hTne : T.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    rintro rfl
    exact hempty hWT
  obtain ⟨p, hp⟩ := hTne
  refine ⟨T, mem_powerset.mp hTR, p, hp, hWT, ?_⟩
  intro he
  have herase : T.erase p ∈ S := mem_filter.mpr
    ⟨mem_powerset.mpr (Subset.trans (erase_subset p T) (mem_powerset.mp hTR)), he⟩
  exact (not_le_of_gt (card_lt_card (erase_ssubset hp))) (hmin _ herase)

end
end CCDN
