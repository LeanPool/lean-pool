/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.SimplexTransfer
public import Mathlib.Tactic.Module

/-! # Distinct-index products of the concrete simplex matrices -/

@[expose] public section

namespace NoncommutativeAMGM
open Matrix
open scoped BigOperators

/-- Coefficients on the simplex vectors, together with the axis coefficient. -/
noncomputable def simplexStateVector (n : ℕ) (c : ℝ) (g : Fin n → ℝ) : Fin n → ℝ :=
  c • simplexAxis n + ∑ j, g j • simplexVector n j

/-- Applying a fresh matrix updates the axis and the simplex coefficients explicitly. -/
theorem simplexStateVector_fresh {n : ℕ} (hn : 1 < n) (α β c : ℝ)
    (g : Fin n → ℝ) (i : Fin n) (hgi : g i = 0) :
    simplexMatrix n α β i *ᵥ simplexStateVector n c g =
      simplexStateVector n (c - β / ((n : ℝ) - 1) * ∑ j, g j)
        (fun j ↦ α * g j + if j = i then
          β * c - (β ^ 2 - α) / ((n : ℝ) - 1) * ∑ j, g j else 0) := by
  classical
  have hact (j : Fin n) :
      g j • (simplexMatrix n α β i *ᵥ simplexVector n j) =
        g j • (α • simplexVector n j - (β / ((n : ℝ) - 1)) • simplexAxis n -
          ((β ^ 2 - α) / ((n : ℝ) - 1)) • simplexVector n i) := by
    by_cases h : i = j
    · subst j
      simp only [hgi, zero_smul]
    · rw [simplexMatrix_mulVec_other hn α β i j h]
  have hsum : simplexMatrix n α β i *ᵥ (∑ j, g j • simplexVector n j) =
      ∑ j, g j • (simplexMatrix n α β i *ᵥ simplexVector n j) := by
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_smul] using
      map_sum (simplexMatrix n α β i).mulVecLin (fun j ↦ g j • simplexVector n j)
        Finset.univ
  simp only [simplexStateVector, Matrix.mulVec_add, Matrix.mulVec_smul,
    simplexMatrix_mulVec_axis hn, hsum, hact, smul_add, smul_sub,
    Finset.sum_sub_distrib, smul_smul]
  simp_rw [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have ha : (∑ j, (g j * α) • simplexVector n j) =
      ∑ j, (α * g j) • simplexVector n j := by
    congr 1
    funext j
    rw [mul_comm]
  rw [ha, ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_mul, ← Finset.sum_mul]
  module

/-- Every distinct-index product admits the transfer-state decomposition. -/
theorem simplexWord_state {n : ℕ} (hn : 1 < n) (α β : ℝ)
    (l : List (Fin n)) (hl : l.Nodup) :
    ∃ g : Fin n → ℝ,
      (∀ i, i ∉ l → g i = 0) ∧
      (∑ i, g i) = (simplexTransfer ((n : ℝ) - 1) α β l.length).2 ∧
      (l.map (simplexMatrix n α β)).prod *ᵥ simplexAxis n =
        simplexStateVector n (simplexTransfer ((n : ℝ) - 1) α β l.length).1 g := by
  classical
  induction l with
  | nil =>
    refine ⟨0, by simp, ?_, ?_⟩
    · simp [simplexTransfer]
    · simp [simplexStateVector, simplexTransfer]
  | cons i l ih =>
    obtain ⟨hi, hln⟩ := List.nodup_cons.mp hl
    obtain ⟨g, hg, hsum, hstate⟩ := ih hln
    let δ := β * (simplexTransfer ((n : ℝ) - 1) α β l.length).1 -
      (β ^ 2 - α) / ((n : ℝ) - 1) * ∑ j, g j
    refine ⟨fun j ↦ α * g j + if j = i then δ else 0, ?_, ?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := by intro h; subst j; simp at hj
      have hjl : j ∉ l := by simpa [List.mem_cons, hji] using hj
      simp [hg j hjl, hji]
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, List.length_cons, simplexTransfer]
      dsimp [δ]
      rw [hsum]
      ring
    · simp only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, hstate,
        simplexStateVector_fresh hn α β _ g i (hg i hi), List.length_cons,
        simplexTransfer]
      dsimp [δ]
      rw [hsum]

/-- The scalar coefficient of a distinct word is independent of the index choices. -/
theorem simplexWord_axis_coefficient {n : ℕ} (hn : 1 < n) (α β : ℝ)
    (hαβ : ((n : ℝ) - 2) * α + β ^ 2 = (n : ℝ) - 1)
    (l : List (Fin n)) (hl : l.Nodup) :
    simplexAxis n ⬝ᵥ ((l.map (simplexMatrix n α β)).prod *ᵥ simplexAxis n) =
      simplexRecurrence (2 * α) (α * (n : ℝ) / ((n : ℝ) - 1)) l.length := by
  obtain ⟨g, _, _, hg⟩ := simplexWord_state hn α β l hl
  rw [hg, simplexStateVector, dotProduct_add, dotProduct_smul,
    simplexAxis_dot_self (by omega)]
  have hz : simplexAxis n ⬝ᵥ (∑ j, g j • simplexVector n j) = 0 := by
    rw [dotProduct_sum]
    simp only [dotProduct_smul, simplexAxis_dot_vector (show 0 < n by omega),
      smul_zero, Finset.sum_const_zero]
  rw [hz, add_zero, smul_eq_mul, mul_one, simplexTransfer_fst hn α β hαβ]

/-- The actual without-replacement matrix average has the predicted axis coefficient. -/
theorem simplexMean_axis_coefficient {n m : ℕ} (hn : 1 < n) (hmn : m ≤ n) (α β : ℝ)
    (hαβ : ((n : ℝ) - 2) * α + β ^ 2 = (n : ℝ) - 1) :
    simplexAxis n ⬝ᵥ (withoutReplacementMean n m (simplexMatrix n α β) *ᵥ simplexAxis n) =
      simplexRecurrence (2 * α) (α * (n : ℝ) / ((n : ℝ) - 1)) m := by
  classical
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M ↦ simplexAxis n ⬝ᵥ (M *ᵥ simplexAxis n)
      map_add' := by intros; simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intros; simp [Matrix.smul_mulVec, dotProduct_smul] }
  change L (withoutReplacementMean n m (simplexMatrix n α β)) = _
  rw [withoutReplacementMean, map_smul, distinctProductSum, map_sum]
  have hword (f : Fin m ↪ Fin n) :
      L (List.ofFn (fun j ↦ simplexMatrix n α β (f j))).prod =
        simplexRecurrence (2 * α) (α * (n : ℝ) / ((n : ℝ) - 1)) m := by
    have h := simplexWord_axis_coefficient hn α β hαβ (List.ofFn f)
      (List.nodup_ofFn.mpr f.injective)
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, List.map_ofFn,
      List.length_ofFn, Function.comp_def] using h
  simp_rw [hword]
  rw [normalization_eq_inv_card hmn]
  have hc : (Fintype.card (Fin m ↪ Fin n) : ℝ) ≠ 0 := by
    rw [card_distinct_tuples]
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hmn))
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end NoncommutativeAMGM
