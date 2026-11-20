/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.CoefficientSpace

/-!
# The triangular basis for the high-order vanishing subspace

The powers are listed in descending degree so that the operator matrix is upper triangular.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial Module
open scoped RealInnerProductSpace

/-- The shifted power of degree `L - 1 - i` in the bounded-degree space. -/
noncomputable def descendingPowerVector (L j : ℕ) (i : Fin (L - j)) : CoefficientSpace L :=
  ⟨(X - 1) ^ (L - 1 - i.val), by
    change shiftedPowerSequence (L - 1 - i.val) ∈ Polynomial.degreeLT ℝ L
    rw [mem_degreeLT, shiftedPowerSequence.degree_eq, Nat.cast_lt]
    omega⟩

theorem descendingPowerVector_independent (L j : ℕ) :
    LinearIndependent ℝ (descendingPowerVector L j) := by
  apply LinearIndependent.of_comp (coefficientSpaceVal L)
  change LinearIndependent ℝ (fun i : Fin (L - j) ↦ shiftedPowerSequence (L - 1 - i.val))
  apply shiftedPowerSequence.linearIndependent.comp
  intro a b hab
  change L - 1 - a.val = L - 1 - b.val at hab
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

/-- The span of the shifted powers with degrees from `j` to `L - 1`. -/
noncomputable def coefficientTail (L j : ℕ) : Submodule ℝ (CoefficientSpace L) :=
  Submodule.span ℝ (Set.range (descendingPowerVector L j))

/-- The shifted-power basis of the tail, ordered by descending degree. -/
noncomputable def coefficientTailBasis (L j : ℕ) :
    Basis (Fin (L - j)) ℝ (coefficientTail L j) :=
  Basis.span (descendingPowerVector_independent L j)

theorem coefficientTailBasis_val (L j : ℕ) (i : Fin (L - j)) :
    (coefficientTailBasis L j i : CoefficientSpace L) = descendingPowerVector L j i := by
  exact Basis.coe_span_apply (descendingPowerVector_independent L j) i

/-- The diagonal entry of the restricted operator in the shifted-power basis. -/
noncomputable def tailEigenvalue (L : ℕ) (i : ℕ) : ℝ :=
  ((L - 1 - i : ℕ) : ℝ) * (((L - 1 - i : ℕ) : ℝ) + 1)

/-- The magnitude of the coefficient of the preceding basis vector. -/
noncomputable def tailOffDiagonal (L : ℕ) (i : ℕ) : ℝ :=
  (((L - 1 - i : ℕ) : ℝ) + 1) * ((L : ℝ) - (L - 1 - i : ℕ) - 1)

theorem descendingPower_action_zero (L j : ℕ) (i : Fin (L - j)) (hi : i.val = 0) :
    boundedCoefficientOperator L (descendingPowerVector L j i) =
      tailEigenvalue L i.val • descendingPowerVector L j i := by
  apply Subtype.ext
  change coefficientOperator L ((X - 1 : Polynomial ℝ) ^ (L - 1 - i.val)) = _
  rw [coefficientOperator_power]
  have hL : 0 < L := by have := i.isLt; omega
  have hcast : ((L - 1 - i.val : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [hi, Nat.sub_zero, Nat.cast_sub hL, Nat.cast_one]
  have hz : (L : ℝ) - (L - 1 - i.val : ℕ) - 1 = 0 := by linarith
  simp [hz, tailEigenvalue, descendingPowerVector]

theorem descendingPower_action_pred (L j : ℕ) (i : Fin (L - j)) (hi : 0 < i.val) :
    boundedCoefficientOperator L (descendingPowerVector L j i) =
      tailEigenvalue L i.val • descendingPowerVector L j i -
        tailOffDiagonal L i.val • descendingPowerVector L j ⟨i.val - 1, by omega⟩ := by
  apply Subtype.ext
  change coefficientOperator L ((X - 1 : Polynomial ℝ) ^ (L - 1 - i.val)) = _
  rw [coefficientOperator_power]
  have he : L - 1 - (i.val - 1) = (L - 1 - i.val) + 1 := by
    have := i.isLt
    omega
  simp only [tailEigenvalue, tailOffDiagonal, descendingPowerVector,
    Submodule.coe_sub, Submodule.coe_smul, he]

theorem boundedCoefficientOperator_preserves_tail (L j : ℕ) (p : CoefficientSpace L)
    (hp : p ∈ coefficientTail L j) : boundedCoefficientOperator L p ∈ coefficientTail L j := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    by_cases hi : i.val = 0
    · rw [descendingPower_action_zero L j i hi]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    · rw [descendingPower_action_pred L j i (by omega)]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))
  | zero => simp
  | add p q _ _ hp hq => simpa using (coefficientTail L j).add_mem hp hq
  | smul r p _ hp => simpa using (coefficientTail L j).smul_mem r hp

/-- The bounded coefficient operator restricted to the invariant tail subspace. -/
noncomputable def coefficientTailOperator (L j : ℕ) :
    coefficientTail L j →ₗ[ℝ] coefficientTail L j :=
  (boundedCoefficientOperator L).restrict (boundedCoefficientOperator_preserves_tail L j)

theorem coefficientTailOperator_symmetric {L j : ℕ} (hL : 0 < L) :
    (coefficientTailOperator L j).IsSymmetric := by
  intro p q
  exact boundedCoefficientOperator_symmetric hL p.val q.val

theorem coefficientTailOperator_basis_zero (L j : ℕ) (i : Fin (L - j)) (hi : i.val = 0) :
    coefficientTailOperator L j (coefficientTailBasis L j i) =
      tailEigenvalue L i.val • coefficientTailBasis L j i := by
  apply Subtype.ext
  simpa only [coefficientTailOperator, LinearMap.restrict_apply, coefficientTailBasis_val,
    Submodule.coe_smul] using descendingPower_action_zero L j i hi

theorem coefficientTailOperator_basis_pred (L j : ℕ) (i : Fin (L - j)) (hi : 0 < i.val) :
    coefficientTailOperator L j (coefficientTailBasis L j i) =
      tailEigenvalue L i.val • coefficientTailBasis L j i -
        tailOffDiagonal L i.val • coefficientTailBasis L j ⟨i.val - 1, by omega⟩ := by
  apply Subtype.ext
  simpa only [coefficientTailOperator, LinearMap.restrict_apply, coefficientTailBasis_val,
    Submodule.coe_smul, Submodule.coe_sub] using
      descendingPower_action_pred L j i hi

theorem coefficientTailMatrix_upper (L j : ℕ) :
    (LinearMap.toMatrix (coefficientTailBasis L j) (coefficientTailBasis L j)
      (coefficientTailOperator L j)).IsUpperTriangular := by
  intro r c hrc
  change c.val < r.val at hrc
  rw [LinearMap.toMatrix_apply]
  have hcr : c ≠ r := by omega
  by_cases hc : c.val = 0
  · rw [coefficientTailOperator_basis_zero L j c hc]
    simp [map_smul, hcr]
  · have hcpos : 0 < c.val := by omega
    rw [coefficientTailOperator_basis_pred L j c hcpos]
    have hpr : (⟨c.val - 1, by omega⟩ : Fin (L - j)) ≠ r := by
      intro he
      have heval : c.val - 1 = r.val := congrArg Fin.val he
      omega
    simp [map_sub, map_smul, hcr, hpr]

theorem coefficientTailMatrix_diagonal (L j : ℕ) (i : Fin (L - j)) :
    LinearMap.toMatrix (coefficientTailBasis L j) (coefficientTailBasis L j)
      (coefficientTailOperator L j) i i = tailEigenvalue L i.val := by
  rw [LinearMap.toMatrix_apply]
  by_cases hi : i.val = 0
  · rw [coefficientTailOperator_basis_zero L j i hi]
    simp [map_smul]
  · have hipos : 0 < i.val := by omega
    rw [coefficientTailOperator_basis_pred L j i hipos]
    have hpi : (⟨i.val - 1, by omega⟩ : Fin (L - j)) ≠ i := by
      intro he
      have heval : i.val - 1 = i.val := congrArg Fin.val he
      omega
    simp [map_sub, map_smul, hpi]

/-- The spectral lower bound for the concrete coefficient operator on its vanishing subspace. -/
theorem coefficientTail_inner_lower {L j : ℕ} (hjL : j < L) (x : coefficientTail L j) :
    ((j : ℝ) * ((j : ℝ) + 1)) * ‖x‖ ^ 2 ≤ ⟪coefficientTailOperator L j x, x⟫ := by
  apply symmetric_triangular_inner_lower (coefficientTailOperator L j)
    (coefficientTailOperator_symmetric (by omega)) (coefficientTailBasis L j)
    (coefficientTailMatrix_upper L j)
  intro i
  rw [coefficientTailMatrix_diagonal, tailEigenvalue]
  have hji : j ≤ L - 1 - i.val := by have := i.isLt; omega
  have hjiR : (j : ℝ) ≤ (L - 1 - i.val : ℕ) := by exact_mod_cast hji
  exact mul_le_mul hjiR (by linarith) (by positivity) (by positivity)

theorem coefficientTail_map_val (L j : ℕ) :
    (coefficientTail L j).map (coefficientSpaceVal L) = powerTail L j := by
  rw [coefficientTail, Submodule.map_span, ← Set.range_comp]
  change Submodule.span ℝ (Set.range (fun i : Fin (L - j) ↦
    (X - 1 : Polynomial ℝ) ^ (L - 1 - i.val))) = powerTail L j
  rw [powerTail]
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    have := i.isLt
    exact ⟨L - 1 - i.val, by omega, by omega, rfl⟩
  · rintro ⟨l, hjl, hlL, rfl⟩
    refine ⟨⟨L - 1 - l, by omega⟩, ?_⟩
    change (X - 1 : Polynomial ℝ) ^ (L - 1 - (L - 1 - l)) = (X - 1) ^ l
    congr 1
    omega

/-- The concrete spectral lower bound, now expressed entirely in polynomial coefficients. -/
theorem coefficientOperator_inner_lower {L j : ℕ} (hjL : j < L) (p : Polynomial ℝ)
    (hp : p ∈ powerTail L j) :
    ((j : ℝ) * ((j : ℝ) + 1)) * realCoefficientInner p p ≤
      realCoefficientInner p (coefficientOperator L p) := by
  rw [← coefficientTail_map_val] at hp
  obtain ⟨x, hx, hxp⟩ := Submodule.mem_map.mp hp
  let y : coefficientTail L j := ⟨x, hx⟩
  have h := coefficientTail_inner_lower hjL y
  have hL : 0 < L := by omega
  have hnorm : ‖y‖ ^ 2 = realCoefficientInner p p := by
    change ‖x‖ ^ 2 = _
    rw [← real_inner_self_eq_norm_sq, coefficientSpace_inner hL, hxp]
  have hinner : ⟪coefficientTailOperator L j y, y⟫ =
      realCoefficientInner (coefficientOperator L p) p := by
    change ⟪boundedCoefficientOperator L x, x⟫ = _
    rw [coefficientSpace_inner hL]
    change realCoefficientInner (coefficientOperator L (coefficientSpaceVal L x))
      (coefficientSpaceVal L x) = _
    rw [hxp]
  rw [hnorm, hinner, realCoefficientInner_comm (coefficientOperator L p) p] at h
  exact h

/-- Lemma 3.10 with coefficients padded to the fixed ambient degree `L` before
removing the first and last coefficients. -/
theorem coefficient_norm_step_padded {L j : ℕ} (hjL : j < L) (p : Polynomial ℝ)
    (hp : p ∈ powerTail L j) :
    ((j : ℝ) * ((j : ℝ) + 1)) * realCoefficientInner p p ≤
      ((L : ℝ) ^ 2 / 4) * interiorCoefficientNormSq L ((X - 1) * p) := by
  have hp0 : p ∈ powerTail L 0 := by
    apply Submodule.span_mono (s := {q : Polynomial ℝ |
      ∃ l : ℕ, j ≤ l ∧ l < L ∧ q = (X - 1) ^ l}) (t := {q : Polynomial ℝ |
      ∃ l : ℕ, 0 ≤ l ∧ l < L ∧ q = (X - 1) ^ l}) ?_ hp
    rintro q ⟨l, _, hlL, rfl⟩
    exact ⟨l, by omega, hlL, rfl⟩
  rw [powerTail_zero_eq_degreeLT] at hp0
  have hdeg : p.natDegree < L := by
    by_cases hpz : p = 0
    · simpa [hpz] using (show 0 < L by omega)
    · exact (natDegree_lt_iff_degree_lt hpz).mpr (mem_degreeLT.mp hp0)
  exact (coefficientOperator_inner_lower hjL p hp).trans (coefficientOperator_energy_le L p hdeg)

end NoncommutativeAMGM
