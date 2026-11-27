/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalParallel
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalIdentity

/-!
# Functional calculus for the parallel thermal formula

The mean and parallel-family operations are identified with their scalar
functions on a single self-adjoint operator. Strict positivity of the
scalar functions is an explicit domain requirement for every inverse.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

variable {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Scalar normalization in the defining geometric-mean formula. -/
theorem scalar_weightedGeometricMean (p : ℝ) {a b : ℝ} (ha : 0 < a) :
    a ^ (1 / 2 : ℝ) * (a ^ (-(1 / 2) : ℝ) * b * a ^ (-(1 / 2) : ℝ)) ^ p *
      a ^ (1 / 2 : ℝ) = a * (b / a) ^ p := by
  have hhalf : a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := by
    rw [← Real.rpow_add ha]
    norm_num
  have hneg : a ^ (-(1 / 2) : ℝ) * a ^ (-(1 / 2) : ℝ) = a⁻¹ := by
    rw [← Real.rpow_add ha]
    norm_num [Real.rpow_neg_one]
  have hinner : a ^ (-(1 / 2) : ℝ) * b * a ^ (-(1 / 2) : ℝ) = b / a := by
    calc
      _ = b * (a ^ (-(1 / 2) : ℝ) * a ^ (-(1 / 2) : ℝ)) := by ring
      _ = _ := by rw [hneg, div_eq_mul_inv]
  rw [hinner]
  calc
    _ = (a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ)) * (b / a) ^ p := by ring
    _ = _ := by rw [hhalf]

/-- Weighted geometric means of two positive functions of the same
self-adjoint operator are given by the scalar weighted-mean formula. -/
theorem weightedGeometricMean_cfc (T : F →L[ℂ] F) (hT : IsSelfAdjoint T)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ T))
    (hg : ContinuousOn g (spectrum ℝ T))
    (hfpos : ∀ x ∈ spectrum ℝ T, 0 < f x)
    (hgpos : ∀ x ∈ spectrum ℝ T, 0 < g x) (p : ℝ) :
    weightedGeometricMean p (cfc f T) (cfc g T) =
      cfc (fun x => f x * (g x / f x) ^ p) T := by
  let u : ℝ → ℝ := fun x => f x ^ (1 / 2 : ℝ)
  let v : ℝ → ℝ := fun x => f x ^ (-(1 / 2) : ℝ)
  have hu : ContinuousOn u (spectrum ℝ T) :=
    hf.rpow_const (fun x hx => Or.inl (hfpos x hx).ne')
  have hv : ContinuousOn v (spectrum ℝ T) :=
    hf.rpow_const (fun x hx => Or.inl (hfpos x hx).ne')
  have hX : ContinuousOn (fun x => v x * g x * v x) (spectrum ℝ T) :=
    (hv.mul hg).mul hv
  have hXpos : ∀ x ∈ spectrum ℝ T, 0 < v x * g x * v x := by
    intro x hx
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos (hfpos x hx) _) (hgpos x hx))
      (Real.rpow_pos_of_pos (hfpos x hx) _)
  have hXp : ContinuousOn (fun x => (v x * g x * v x) ^ p) (spectrum ℝ T) :=
    hX.rpow_const (fun x hx => Or.inl (hXpos x hx).ne')
  unfold weightedGeometricMean
  simp_rw [CFC.cfc_rpow hfpos hf hT]
  change cfc u T * (cfc v T * cfc g T * cfc v T) ^ p * cfc u T = _
  rw [← cfc_mul v g T hv hg, ← cfc_mul (fun x => v x * g x) v T (hv.mul hg) hv,
    CFC.cfc_rpow hXpos hX hT,
    ← cfc_mul u (fun x => (v x * g x * v x) ^ p) T hu hXp,
    ← cfc_mul (fun x => u x * (v x * g x * v x) ^ p) u T (hu.mul hXp) hu]
  apply cfc_congr
  intro x hx
  exact scalar_weightedGeometricMean p (hfpos x hx)

/-- Finite parallel sums of strictly positive scalar functions commute
with the functional calculus. -/
theorem parallelFamily_cfc (T : F →L[ℂ] F) (hT : IsSelfAdjoint T)
    {n : ℕ} (f : Fin (n + 1) → ℝ → ℝ)
    (hf : ∀ j, ContinuousOn (f j) (spectrum ℝ T))
    (hpos : ∀ j x, x ∈ spectrum ℝ T → 0 < f j x) :
    parallelFamily (fun j => cfc (f j) T) =
      cfc (fun x => (∑ j, (f j x)⁻¹)⁻¹) T := by
  have hInv : ∀ j, ContinuousOn (fun x => (f j x)⁻¹) (spectrum ℝ T) :=
    fun j => (hf j).inv₀ (fun x hx => (hpos j x hx).ne')
  have hsum : ContinuousOn (fun x => ∑ j, (f j x)⁻¹) (spectrum ℝ T) :=
    continuousOn_finsetSum _ (fun j _ => hInv j)
  have hsumpos : ∀ x ∈ spectrum ℝ T, 0 < ∑ j, (f j x)⁻¹ := by
    intro x hx
    exact Finset.sum_pos (fun j _ => inv_pos.mpr (hpos j x hx)) Finset.univ_nonempty
  have hi : ∀ j, Ring.inverse (cfc (f j) T) = cfc (fun x => (f j x)⁻¹) T :=
    fun j => (cfc_inv (f j) T (fun x hx => (hpos j x hx).ne') (hf j) hT).symm
  unfold parallelFamily
  simp_rw [hi]
  rw [← cfc_sum_univ (fun j x => (f j x)⁻¹) T hInv]
  have heq : (∑ j : Fin (n + 1), fun x : ℝ => (f j x)⁻¹) =
      (fun x => ∑ j, (f j x)⁻¹) := by ext x; simp
  rw [heq]
  exact (cfc_inv _ T (fun x hx => (hsumpos x hx).ne') hsum hT).symm

/-- Every real spectral value of an operator of norm below one lies in
the open interval needed for the strict thermal identity. -/
theorem spectrum_mem_Ioo_of_norm_lt_one {T : F →L[ℂ] F} (hT : ‖T‖ < 1)
    {x : ℝ} (hx : x ∈ spectrum ℝ T) : x ∈ Set.Ioo (-1 : ℝ) 1 := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · let := hF
    simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hx
  · let := hF
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using
      (spectrum.norm_le_norm_of_mem hx).trans_lt hT)

/-- Scalar member of the thermal geometric-mean family. -/
noncomputable def thermalMeanFunction {n : ℕ} (j : Fin (n + 1)) (x : ℝ) : ℝ :=
  (1 + x) * ((1 - x) / (1 + x)) ^ thermalMeanWeight j

theorem thermalMeanFunction_pos {n : ℕ} (j : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : 0 < thermalMeanFunction j x := by
  unfold thermalMeanFunction
  exact mul_pos (by linarith [hx.1])
    (Real.rpow_pos_of_pos (div_pos (by linarith [hx.2]) (by linarith [hx.1])) _)

theorem continuousOn_thermalMeanFunction {n : ℕ} (j : Fin (n + 1)) :
    ContinuousOn (thermalMeanFunction j) (Set.Ioo (-1 : ℝ) 1) := by
  have hplus : ContinuousOn (fun x : ℝ => 1 + x) (Set.Ioo (-1 : ℝ) 1) := by fun_prop
  have hminus : ContinuousOn (fun x : ℝ => 1 - x) (Set.Ioo (-1 : ℝ) 1) := by fun_prop
  apply hplus.mul
  apply (hminus.div hplus (fun x hx => ne_of_gt (by linarith [hx.1]))).rpow_const
  intro x hx
  exact Or.inr (thermalMeanWeight_pos j).le

theorem cfc_one_add_id (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    cfc (fun x : ℝ => 1 + x) T = 1 + T := by
  rw [cfc_const_add (1 : ℝ) (fun x : ℝ => x) T (by fun_prop) hT,
    cfc_id' ℝ T hT, map_one]

theorem cfc_one_sub_id (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    cfc (fun x : ℝ => 1 - x) T = 1 - T := by
  rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) T,
    cfc_const_one ℝ T hT, cfc_id' ℝ T hT]

theorem weightedGeometricMean_one_add_sub (T : F →L[ℂ] F) (hT : IsSelfAdjoint T)
    (hnorm : ‖T‖ < 1) {n : ℕ} (j : Fin (n + 1)) :
    weightedGeometricMean (thermalMeanWeight j) (1 + T) (1 - T) =
      cfc (thermalMeanFunction j) T := by
  rw [← cfc_one_add_id T hT, ← cfc_one_sub_id T hT]
  apply weightedGeometricMean_cfc T hT _ _ (by fun_prop) (by fun_prop)
  · intro x hx
    have h := spectrum_mem_Ioo_of_norm_lt_one hnorm hx
    linarith [h.1]
  · intro x hx
    have h := spectrum_mem_Ioo_of_norm_lt_one hnorm hx
    linarith [h.2]

/-- The actual parallel thermal identity for a strictly contractive
self-adjoint commutation operator. All inverses are genuine here. -/
theorem geometricParallel_eq_thermal_cfc (T : F →L[ℂ] F) (hT : IsSelfAdjoint T)
    (hnorm : ‖T‖ < 1) (n : ℕ) :
    geometricParallel n (1 + T) (1 - T) =
      cfc (fun x : ℝ => thermalIncrement
        (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) |x|) T := by
  have hspec : spectrum ℝ T ⊆ Set.Ioo (-1 : ℝ) 1 :=
    fun _ hx => spectrum_mem_Ioo_of_norm_lt_one hnorm hx
  unfold geometricParallel
  simp_rw [weightedGeometricMean_one_add_sub T hT hnorm]
  rw [parallelFamily_cfc T hT _
    (fun j => (continuousOn_thermalMeanFunction j).mono hspec)
    (fun j x hx => thermalMeanFunction_pos j (hspec hx))]
  apply cfc_congr
  intro x hx
  dsimp only
  rw [thermalIncrement_abs_eq_scalarGeometricParallel n (hspec hx).1 (hspec hx).2]
  unfold scalarGeometricParallel
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold thermalMeanFunction
  congr 1
  have ht : 0 ≤ (1 - x) / (1 + x) :=
    (div_pos (by linarith [(hspec hx).2]) (by linarith [(hspec hx).1])).le
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  congr 1
  unfold thermalMeanWeight
  ring

theorem one_add_isStrictlyPositive_of_norm_lt_one {T : F →L[ℂ] F}
    (hT : IsSelfAdjoint T) (hnorm : ‖T‖ < 1) : IsStrictlyPositive (1 + T) := by
  rw [← cfc_one_add_id T hT]
  apply (cfc_isStrictlyPositive_iff _ T (by fun_prop) hT).mpr
  intro x hx
  have h := spectrum_mem_Ioo_of_norm_lt_one hnorm hx
  linarith [h.1]

theorem one_sub_isStrictlyPositive_of_norm_lt_one {T : F →L[ℂ] F}
    (hT : IsSelfAdjoint T) (hnorm : ‖T‖ < 1) : IsStrictlyPositive (1 - T) := by
  rw [← cfc_one_sub_id T hT]
  apply (cfc_isStrictlyPositive_iff _ T (by fun_prop) hT).mpr
  intro x hx
  have h := spectrum_mem_Ioo_of_norm_lt_one hnorm hx
  linarith [h.2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_compression_le (ι : E →ₗᵢ[ℂ] F) (T : F →L[ℂ] F) :
    ‖compression ι T‖ ≤ ‖T‖ := by
  unfold compression
  grw [ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.opNorm_comp_le]
  simp only [LinearIsometryEquiv.norm_map]
  grw [ι.norm_toContinuousLinearMap_le]
  simp only [one_mul]
  exact (mul_le_mul_of_nonneg_left ι.norm_toContinuousLinearMap_le (norm_nonneg T)).trans_eq
    (mul_one _)

/-- First high-compression inequality of Lemma 4.4 in the strictly
contractive case, now stated directly for the actual thermal function.
The closed contraction case still requires its continuous endpoint limit. -/
theorem high_compression_of_norm_lt_one (ι : E →ₗᵢ[ℂ] F)
    {T : F →L[ℂ] F} (hT : IsSelfAdjoint T) (hnorm : ‖T‖ < 1) (n : ℕ) :
    compression ι (cfc (fun x : ℝ => thermalIncrement
      (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) |x|) T) ≤
      cfc (fun x : ℝ => thermalIncrement
        (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) |x|) (compression ι T) := by
  rw [← geometricParallel_eq_thermal_cfc T hT hnorm,
    ← geometricParallel_eq_thermal_cfc (compression ι T) (compression_isSelfAdjoint ι hT)
      ((norm_compression_le ι T).trans_lt hnorm)]
  have h := compression_geometricParallel_le ι n
    (one_add_isStrictlyPositive_of_norm_lt_one hT hnorm)
    (one_sub_isStrictlyPositive_of_norm_lt_one hT hnorm)
  simpa only [compression_add, compression_sub, compression_one] using h

end VacuumBellSeparation.Gaussian
