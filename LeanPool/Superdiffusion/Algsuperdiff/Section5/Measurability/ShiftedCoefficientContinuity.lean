/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.FieldSolutionMap
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionCoefficientContinuity
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionMeasurable
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.AlphaShiftedWeakSolution
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationInterior
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.EllipticityWitness

@[expose] public section

/-!
# Stability of shifted weak solutions under coefficient perturbations

This file isolates the Hilbert-space estimate used to prove continuity of a
shifted divergence-form solution with respect to its coefficient.  The
coefficient-specific work is reduced to bounding the difference of the two
shifted bilinear forms at one of the solutions.
-/

namespace Algsuperdiff.Section5.Measurability.ShiftedCoefficientContinuity

open DivergenceFormProcess.Form HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support Algsuperdiff.Section5.Support
open scoped ENNReal Matrix.Norms.Elementwise Topology

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

private theorem sqrt_integral_norm_sq_eq_norm_vectorL2 (F : VectorL2 U) :
    Real.sqrt (∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume) = ‖F‖ := by
  have hnorm := (MeasureTheory.Lp.memLp F).eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  have hnonneg : 0 ≤ ∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume :=
    integral_nonneg fun x => sq_nonneg ‖F x‖
  have hsq : ‖F‖ ^ (2 : ℕ) = ∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume := by
    rw [MeasureTheory.Lp.norm_def, hnorm (by norm_num)]
    norm_num
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _),
      ← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg F)]

private theorem sqrt_integral_sq_eq_norm_scalarL2 (F : ScalarL2 U) :
    Real.sqrt (∫ x in U, F x ^ (2 : ℕ) ∂volume) = ‖F‖ := by
  have hnorm := (MeasureTheory.Lp.memLp F).eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  have hnonneg : 0 ≤ ∫ x in U, F x ^ (2 : ℕ) ∂volume :=
    integral_nonneg fun x => sq_nonneg (F x)
  have hsq : ‖F‖ ^ (2 : ℕ) = ∫ x in U, F x ^ (2 : ℕ) ∂volume := by
    rw [MeasureTheory.Lp.norm_def, hnorm (by norm_num)]
    norm_num
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _),
      ← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg F)]

/-- Difference of shifted bilinear forms controlled by an entrywise coefficient
bound.  The mass terms cancel, leaving only the coefficient pairing. -/
theorem abs_shiftedBilin_sub_le_of_entry_bound
    {a b : CoeffField d} {alpha lamA LamA lamB LamB delta : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA U a)
    (hEllB : IsEllipticFieldOn lamB LamB U b)
    (hdelta : 0 ≤ delta)
    (hab : ∀ x ∈ U, ∀ i j, |a x i j - b x i j| ≤ delta)
    (v w : ZeroTraceSobolev U) :
    |shiftedBilin hEllA alpha v w - shiftedBilin hEllB alpha v w| ≤
      (d : ℝ) * ((d : ℝ) * delta) * ‖ZeroTraceSobolev.gradient v‖ *
        ‖ZeroTraceSobolev.gradient w‖ := by
  let V : VectorL2 U :=
    hilbertVectorL2ToVectorL2 (U := U) (ZeroTraceSobolev.gradient v)
  let W : VectorL2 U :=
    hilbertVectorL2ToVectorL2 (U := U) (ZeroTraceSobolev.gradient w)
  have hVL2 : MemVectorL2 U (fun x => V x) := MeasureTheory.Lp.memLp V
  have hWL2 : MemVectorL2 U (fun x => W x) := MeasureTheory.Lp.memLp W
  have hAVL2 : MemVectorL2 U (fun x => matVecMul (a x) (V x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllA hVL2
  have hBVL2 : MemVectorL2 U (fun x => matVecMul (b x) (V x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllB hVL2
  have hIntA : IntegrableOn (fun x => vecDot (matVecMul (a x) (V x)) (W x)) U :=
    integrableOn_vecDot_of_memVectorL2 hAVL2 hWL2
  have hIntB : IntegrableOn (fun x => vecDot (matVecMul (b x) (V x)) (W x)) U :=
    integrableOn_vecDot_of_memVectorL2 hBVL2 hWL2
  have hpair : coefficientPairing a U (ZeroTraceSobolev.gradient v)
        (ZeroTraceSobolev.gradient w) -
      coefficientPairing b U (ZeroTraceSobolev.gradient v)
        (ZeroTraceSobolev.gradient w) =
      ∫ x in U, vecDot (matVecMul (a x - b x) (V x)) (W x) ∂volume := by
    unfold coefficientPairing
    change (∫ x in U, vecDot (matVecMul (a x) (V x)) (W x) ∂volume) -
        (∫ x in U, vecDot (matVecMul (b x) (V x)) (W x) ∂volume) = _
    rw [← integral_sub hIntA hIntB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hmv : matVecMul (a x - b x) (V x) =
        matVecMul (a x) (V x) - matVecMul (b x) (V x) := by
      funext i
      simp only [matVecMul, Pi.sub_apply, Matrix.sub_apply, sub_mul,
        Finset.sum_sub_distrib]
    change vecDot (matVecMul (a x) (V x)) (W x) -
        vecDot (matVecMul (b x) (V x)) (W x) =
      vecDot (matVecMul (a x - b x) (V x)) (W x)
    rw [hmv]
    unfold vecDot
    rw [← Finset.sum_sub_distrib]
    congr 1
    funext i
    rw [Pi.sub_apply, sub_mul]
  have hpert : ∀ x ∈ U,
      ‖matVecMul (a x - b x) (V x)‖ ≤ ((d : ℝ) * delta) * ‖V x‖ := by
    intro x hx
    exact Algsuperdiff.Section5.Support.norm_matVecMul_le_of_entry_bound hdelta
      (fun i j => by simpa only [Matrix.sub_apply] using hab x hx i j) (V x)
  have hbound := Algsuperdiff.Section5.Support.abs_setIntegral_vecDot_le_of_norm_le
    U (measurableSet_of_isEllipticFieldOn hEllA)
    (by positivity : (0 : ℝ) ≤ (d : ℝ) * delta) hVL2 hWL2 hpert
  rw [shiftedBilin_apply, shiftedBilin_apply]
  have hmass : alpha * inner ℝ (ZeroTraceSobolev.toL2 v) (ZeroTraceSobolev.toL2 w) +
        coefficientPairing a U (ZeroTraceSobolev.gradient v) (ZeroTraceSobolev.gradient w) -
      (alpha * inner ℝ (ZeroTraceSobolev.toL2 v) (ZeroTraceSobolev.toL2 w) +
        coefficientPairing b U (ZeroTraceSobolev.gradient v) (ZeroTraceSobolev.gradient w)) =
      coefficientPairing a U (ZeroTraceSobolev.gradient v) (ZeroTraceSobolev.gradient w) -
        coefficientPairing b U (ZeroTraceSobolev.gradient v) (ZeroTraceSobolev.gradient w) := by
    ring
  rw [hmass, hpair]
  rw [sqrt_integral_norm_sq_eq_norm_vectorL2,
    sqrt_integral_norm_sq_eq_norm_vectorL2] at hbound
  have hVnorm : ‖V‖ ≤ ‖ZeroTraceSobolev.gradient v‖ := by
    calc
      ‖V‖ ≤ ‖hilbertVectorL2ToVectorL2 (d := d) (U := U)‖ *
          ‖ZeroTraceSobolev.gradient v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖ZeroTraceSobolev.gradient v‖ :=
        mul_le_mul_of_nonneg_right norm_hilbertVectorL2ToVectorL2_le (norm_nonneg _)
      _ = ‖ZeroTraceSobolev.gradient v‖ := one_mul _
  have hWnorm : ‖W‖ ≤ ‖ZeroTraceSobolev.gradient w‖ := by
    calc
      ‖W‖ ≤ ‖hilbertVectorL2ToVectorL2 (d := d) (U := U)‖ *
          ‖ZeroTraceSobolev.gradient w‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖ZeroTraceSobolev.gradient w‖ :=
        mul_le_mul_of_nonneg_right norm_hilbertVectorL2ToVectorL2_le (norm_nonneg _)
      _ = ‖ZeroTraceSobolev.gradient w‖ := one_mul _
  refine hbound.trans ?_
  have hc : 0 ≤ (d : ℝ) * ((d : ℝ) * delta) := by positivity
  calc
    (d : ℝ) * ((d : ℝ) * delta) * (‖V‖ * ‖W‖) ≤
        (d : ℝ) * ((d : ℝ) * delta) *
          (‖ZeroTraceSobolev.gradient v‖ * ‖ZeroTraceSobolev.gradient w‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hVnorm hWnorm (norm_nonneg _) (norm_nonneg _)) hc
    _ = (d : ℝ) * ((d : ℝ) * delta) * ‖ZeroTraceSobolev.gradient v‖ *
        ‖ZeroTraceSobolev.gradient w‖ := by ring

/-- Stability of the canonical shifted weak solution under a perturbation of
the shifted bilinear form.  The coercivity constant is that of the first
coefficient. -/
theorem norm_alphaShiftedSolution_sub_le_of_bilin_diff
    {a b : CoeffField d} {alpha lamA LamA lamB LamB eps : ℝ}
    (halpha : 0 < alpha) (hlamA : 0 < lamA) (hlamB : 0 < lamB)
    (hEllA : IsEllipticFieldOn lamA LamA U a)
    (hEllB : IsEllipticFieldOn lamB LamB U b)
    (f : ScalarL2 U)
    (hpert : ∀ w : ZeroTraceSobolev U,
      |shiftedBilin hEllA alpha
          (alphaShiftedSolution b halpha hlamB hEllB f) w -
        shiftedBilin hEllB alpha
          (alphaShiftedSolution b halpha hlamB hEllB f) w| ≤ eps * ‖w‖)
    (heps : 0 ≤ eps) :
    ‖alphaShiftedSolution a halpha hlamA hEllA f -
        alphaShiftedSolution b halpha hlamB hEllB f‖ ≤
      (min alpha lamA)⁻¹ * eps := by
  let u := alphaShiftedSolution a halpha hlamA hEllA f
  let v := alphaShiftedSolution b halpha hlamB hEllB f
  let w := u - v
  have hc : 0 < min alpha lamA := lt_min halpha hlamA
  have hu := alphaShiftedSolution_isAlphaShiftedWeakSolution
    a halpha hlamA hEllA f
  have hv := alphaShiftedSolution_isAlphaShiftedWeakSolution
    b halpha hlamB hEllB f
  have hu' : shiftedBilin hEllA alpha u w =
      inner ℝ f (ZeroTraceSobolev.toL2 w) := by
    rw [shiftedBilin_apply]
    exact hu w
  have hv' : shiftedBilin hEllB alpha v w =
      inner ℝ f (ZeroTraceSobolev.toL2 w) := by
    rw [shiftedBilin_apply]
    exact hv w
  have hlin : shiftedBilin hEllA alpha w w =
      shiftedBilin hEllA alpha u w - shiftedBilin hEllA alpha v w := by
    have h := congrArg (fun L : ZeroTraceSobolev U →L[ℝ] ℝ => L w)
      (map_sub (shiftedBilin hEllA alpha) u v)
    simpa only [sub_apply] using h
  have hform : shiftedBilin hEllA alpha w w =
      shiftedBilin hEllB alpha v w - shiftedBilin hEllA alpha v w := by
    calc
      shiftedBilin hEllA alpha w w =
          shiftedBilin hEllA alpha u w - shiftedBilin hEllA alpha v w := hlin
      _ = inner ℝ f (ZeroTraceSobolev.toL2 w) -
          shiftedBilin hEllA alpha v w := by
        rw [hu']
      _ = shiftedBilin hEllB alpha v w - shiftedBilin hEllA alpha v w := by
        rw [hv']
  have hlower : min alpha lamA * ‖w‖ * ‖w‖ ≤
      shiftedBilin hEllA alpha w w :=
    shiftedBilin_lower_bound hEllA w
  have hupper : shiftedBilin hEllA alpha w w ≤ eps * ‖w‖ := by
    rw [hform]
    refine (le_abs_self _).trans ?_
    rw [abs_sub_comm]
    simpa only [v] using hpert w
  have hchain : min alpha lamA * ‖w‖ * ‖w‖ ≤ eps * ‖w‖ :=
    hlower.trans hupper
  by_cases hw : ‖w‖ = 0
  · rw [hw]
    positivity
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    have hcancel : min alpha lamA * ‖w‖ ≤ eps := by
      exact le_of_mul_le_mul_right (by simpa [mul_assoc] using hchain) hwpos
    change ‖w‖ ≤ (min alpha lamA)⁻¹ * eps
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    simpa [mul_comm] using hcancel

/-- The corresponding stability estimate for the `L²` resolvent values. -/
theorem norm_alphaShiftedResolvent_sub_le_of_bilin_diff
    {a b : CoeffField d} {alpha lamA LamA lamB LamB eps : ℝ}
    (halpha : 0 < alpha) (hlamA : 0 < lamA) (hlamB : 0 < lamB)
    (hEllA : IsEllipticFieldOn lamA LamA U a)
    (hEllB : IsEllipticFieldOn lamB LamB U b)
    (f : ScalarL2 U)
    (hpert : ∀ w : ZeroTraceSobolev U,
      |shiftedBilin hEllA alpha
          (alphaShiftedSolution b halpha hlamB hEllB f) w -
        shiftedBilin hEllB alpha
          (alphaShiftedSolution b halpha hlamB hEllB f) w| ≤ eps * ‖w‖)
    (heps : 0 ≤ eps) :
    ‖alphaShiftedResolvent a halpha hlamA hEllA f -
        alphaShiftedResolvent b halpha hlamB hEllB f‖ ≤
      (min alpha lamA)⁻¹ * eps := by
  rw [alphaShiftedResolvent_apply, alphaShiftedResolvent_apply, ← map_sub]
  exact (ZeroTraceSobolev.norm_toL2_le _).trans
    (norm_alphaShiftedSolution_sub_le_of_bilin_diff halpha hlamA hlamB
      hEllA hEllB f hpert heps)

/-- Quantitative stability under a uniform entrywise coefficient perturbation.
The solution on the right is fixed, so this estimate is directly suited to a
continuity proof at a specified coefficient. -/
theorem norm_alphaShiftedSolution_sub_le_of_entry_bound
    {a b : CoeffField d} {alpha nu LamA LamB delta : ℝ}
    (halpha : 0 < alpha) (hnu : 0 < nu)
    (hEllA : IsEllipticFieldOn nu LamA U a)
    (hEllB : IsEllipticFieldOn nu LamB U b)
    (hdelta : 0 ≤ delta)
    (hab : ∀ x ∈ U, ∀ i j, |a x i j - b x i j| ≤ delta)
    (f : ScalarL2 U) :
    ‖alphaShiftedSolution a halpha hnu hEllA f -
        alphaShiftedSolution b halpha hnu hEllB f‖ ≤
      (min alpha nu)⁻¹ *
        ((d : ℝ) * ((d : ℝ) * delta) *
          ‖ZeroTraceSobolev.gradient
            (alphaShiftedSolution b halpha hnu hEllB f)‖) := by
  apply norm_alphaShiftedSolution_sub_le_of_bilin_diff halpha hnu hnu
    hEllA hEllB f
  · intro w
    have h := abs_shiftedBilin_sub_le_of_entry_bound (alpha := alpha)
      hEllA hEllB hdelta hab
      (alphaShiftedSolution b halpha hnu hEllB f) w
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left (ZeroTraceSobolev.norm_gradient_le w)
      (by positivity)
  · positivity

/-- The `L²` resolvent version of the entrywise perturbation estimate. -/
theorem norm_alphaShiftedResolvent_sub_le_of_entry_bound
    {a b : CoeffField d} {alpha nu LamA LamB delta : ℝ}
    (halpha : 0 < alpha) (hnu : 0 < nu)
    (hEllA : IsEllipticFieldOn nu LamA U a)
    (hEllB : IsEllipticFieldOn nu LamB U b)
    (hdelta : 0 ≤ delta)
    (hab : ∀ x ∈ U, ∀ i j, |a x i j - b x i j| ≤ delta)
    (f : ScalarL2 U) :
    ‖alphaShiftedResolvent a halpha hnu hEllA f -
        alphaShiftedResolvent b halpha hnu hEllB f‖ ≤
      (min alpha nu)⁻¹ *
        ((d : ℝ) * ((d : ℝ) * delta) *
          ‖ZeroTraceSobolev.gradient
            (alphaShiftedSolution b halpha hnu hEllB f)‖) := by
  rw [alphaShiftedResolvent_apply, alphaShiftedResolvent_apply, ← map_sub]
  exact (ZeroTraceSobolev.norm_toL2_le _).trans
    (norm_alphaShiftedSolution_sub_le_of_entry_bound halpha hnu hEllA hEllB
      hdelta hab f)

/-! ## Canonical shifted solutions over an interior domain -/

variable {n : ℤ} {nu alpha : ℝ}

/-- An upper ellipticity constant selected for the extension of a compact-cube
coefficient, restricted to an interior domain. -/
def shiftedFieldUpper (hnu : 0 < nu) (A : ellipticCube nu (0 : Vec d) n) : ℝ :=
  (exists_isEllipticFieldOn_extendCoeff hnu (0 : Vec d) n A.2).choose

/-- The selected ellipticity certificate on an arbitrary measurable subset of
the open cube. -/
theorem shiftedFieldEllipticity (hnu : 0 < nu) (hU : MeasurableSet U)
    (hUsub : U ⊆ cubeSetAt (0 : Vec d) n) (A : ellipticCube nu (0 : Vec d) n) :
    IsEllipticFieldOn nu (shiftedFieldUpper hnu A) U (extendCoeff (0 : Vec d) n A.1) :=
  (exists_isEllipticFieldOn_extendCoeff hnu (0 : Vec d) n A.2).choose_spec.mono hU hUsub

/-- Canonical shifted weak solution for a compact-cube coefficient, on an
interior measurable domain. -/
def shiftedFieldSolution (hnu : 0 < nu) (halpha : 0 < alpha)
    (hU : MeasurableSet U) (hUsub : U ⊆ cubeSetAt (0 : Vec d) n)
    (f : ScalarL2 U) (A : ellipticCube nu (0 : Vec d) n) : ZeroTraceSobolev U :=
  alphaShiftedSolution (extendCoeff (0 : Vec d) n A.1) halpha hnu
    (shiftedFieldEllipticity hnu hU hUsub A) f

/-- The associated `L²` resolvent. -/
def shiftedFieldResolvent (hnu : 0 < nu) (halpha : 0 < alpha)
    (hU : MeasurableSet U) (hUsub : U ⊆ cubeSetAt (0 : Vec d) n)
    (f : ScalarL2 U) (A : ellipticCube nu (0 : Vec d) n) : ScalarL2 U :=
  ZeroTraceSobolev.toL2 (shiftedFieldSolution hnu halpha hU hUsub f A)

/-- The compact parameter-to-resolvent map is continuous in `L²`. -/
theorem continuous_shiftedFieldResolvent (hnu : 0 < nu) (halpha : 0 < alpha)
    (hU : MeasurableSet U) (hUsub : U ⊆ cubeSetAt (0 : Vec d) n)
    (f : ScalarL2 U) :
    Continuous (shiftedFieldResolvent hnu halpha hU hUsub f) := by
  rw [Metric.continuous_iff]
  intro A0 eps heps
  let C : ℝ := (min alpha nu)⁻¹ *
    ((d : ℝ) * (d : ℝ) *
      ‖ZeroTraceSobolev.gradient (shiftedFieldSolution hnu halpha hU hUsub f A0)‖)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨eps / (C + 1), by positivity, fun A hA => ?_⟩
  have hentry : ∀ x ∈ U, ∀ i j,
      |extendCoeff (0 : Vec d) n A.1 x i j - extendCoeff (0 : Vec d) n A0.1 x i j| ≤ dist A.1 A0.1 := by
    intro x hx i j
    have hxK : x ∈ closedCubeAt (0 : Vec d) n :=
      cubeSetAt_subset_closedCubeAt (0 : Vec d) n (hUsub hx)
    rw [extendCoeff_apply_of_mem A.1 hxK, extendCoeff_apply_of_mem A0.1 hxK]
    let _ : Norm C(closedCubeAt (0 : Vec d) n, Mat d) := ContinuousMap.instNorm
    let _ : SeminormedAddCommGroup C(closedCubeAt (0 : Vec d) n, Mat d) :=
      ContinuousMap.instSeminormedAddCommGroup
    calc
      |A.1 ⟨x, hxK⟩ i j - A0.1 ⟨x, hxK⟩ i j| =
          |(A.1 ⟨x, hxK⟩ - A0.1 ⟨x, hxK⟩) i j| := by rw [Matrix.sub_apply]
      _ ≤ ‖A.1 ⟨x, hxK⟩ - A0.1 ⟨x, hxK⟩‖ := by
        simpa [Real.norm_eq_abs] using
          Matrix.norm_entry_le_entrywise_sup_norm
            (A := A.1 ⟨x, hxK⟩ - A0.1 ⟨x, hxK⟩) (i := i) (j := j)
      _ = ‖(A.1 - A0.1) ⟨x, hxK⟩‖ := by rfl
      _ ≤ ‖A.1 - A0.1‖ := (A.1 - A0.1).norm_coe_le_norm _
      _ = dist A.1 A0.1 := (dist_eq_norm A.1 A0.1).symm
  have hstab := norm_alphaShiftedResolvent_sub_le_of_entry_bound
    halpha hnu
    (shiftedFieldEllipticity hnu hU hUsub A)
    (shiftedFieldEllipticity hnu hU hUsub A0)
    (dist_nonneg : 0 ≤ dist A.1 A0.1) hentry f
  change dist (shiftedFieldResolvent hnu halpha hU hUsub f A)
      (shiftedFieldResolvent hnu halpha hU hUsub f A0) < eps
  rw [dist_eq_norm]
  have hbound : ‖shiftedFieldResolvent hnu halpha hU hUsub f A -
      shiftedFieldResolvent hnu halpha hU hUsub f A0‖ ≤ C * dist A.1 A0.1 := by
    simpa only [shiftedFieldResolvent, shiftedFieldSolution,
      alphaShiftedResolvent_apply] using
      hstab.trans_eq (by simp only [C, shiftedFieldSolution]; ring)
  have hdist : dist A.1 A0.1 < eps / (C + 1) := by
    simpa [Subtype.dist_eq] using hA
  have hfrac : C * (eps / (C + 1)) < eps := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  exact lt_of_le_of_lt hbound
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hdist.le hC) hfrac)

/-- Identifying the compact-parameter resolvent with any elliptic coefficient
that agrees with its extension on the solution domain. -/
theorem alphaShiftedResolvent_eq_shiftedFieldResolvent_of_eqOn
    {a : CoeffField d} {Lam : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha)
    (hU : MeasurableSet U) (hUsub : U ⊆ cubeSetAt (0 : Vec d) n)
    (A : ellipticCube nu (0 : Vec d) n)
    (hEll : IsEllipticFieldOn nu Lam U a)
    (ha : ∀ x ∈ U, a x = extendCoeff (0 : Vec d) n A.1 x)
    (f : ScalarL2 U) :
    alphaShiftedResolvent a halpha hnu hEll f =
      shiftedFieldResolvent hnu halpha hU hUsub f A := by
  have hab : ∀ x ∈ U, ∀ i j,
      |a x i j - extendCoeff (0 : Vec d) n A.1 x i j| ≤ (0 : ℝ) := by
    intro x hx i j
    rw [ha x hx]
    simp
  have hzero := norm_alphaShiftedResolvent_sub_le_of_entry_bound
    halpha hnu hEll (shiftedFieldEllipticity hnu hU hUsub A)
      (show (0 : ℝ) ≤ 0 by rfl) hab f
  have heq : alphaShiftedResolvent a halpha hnu hEll f =
      alphaShiftedResolvent (extendCoeff (0 : Vec d) n A.1) halpha hnu
        (shiftedFieldEllipticity hnu hU hUsub A) f := by
    apply sub_eq_zero.mp
    exact norm_eq_zero.mp (le_antisymm (hzero.trans (by simp)) (norm_nonneg _))
  simpa [shiftedFieldResolvent, shiftedFieldSolution] using heq

/-- Integral of the canonical shifted resolvent over a measurable subset. -/
def shiftedFieldSetIntegral (hnu : 0 < nu) (halpha : 0 < alpha)
    (hU : MeasurableSet U) (hUsub : U ⊆ cubeSetAt (0 : Vec d) n)
    (f : ScalarL2 U) (B : Set (Vec d)) (A : ellipticCube nu (0 : Vec d) n) : ℝ :=
  ∫ z in B, shiftedFieldResolvent hnu halpha hU hUsub f A z ∂volume

/-- Set integrals of the shifted resolvent vary continuously with the compact
coefficient. -/
theorem continuous_shiftedFieldSetIntegral (hnu : 0 < nu) (halpha : 0 < alpha)
    (hU : MeasurableSet U) (hUfin : volume U ≠ ⊤)
    (hUsub : U ⊆ cubeSetAt (0 : Vec d) n)
    (f : ScalarL2 U) {B : Set (Vec d)} (hBsub : B ⊆ U) :
    Continuous (shiftedFieldSetIntegral hnu halpha hU hUsub f B) := by
  have hBfin : volume B ≠ ⊤ :=
    ((measure_mono hBsub).trans_lt (lt_top_iff_ne_top.2 hUfin)).ne
  rw [Metric.continuous_iff]
  intro A0 eps heps
  let S : ℝ := Real.sqrt (volume.real B)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  obtain ⟨delta, hdelta, hclose⟩ :=
    (Metric.continuous_iff.1
      (continuous_shiftedFieldResolvent hnu halpha hU hUsub f))
      A0 (eps / (S + 1)) (by positivity)
  refine ⟨delta, hdelta, fun A hA => ?_⟩
  let F : ScalarL2 U := shiftedFieldResolvent hnu halpha hU hUsub f A -
    shiftedFieldResolvent hnu halpha hU hUsub f A0
  have hFB : MemLp (fun z => F z) 2 (volume.restrict B) :=
    (MeasureTheory.Lp.memLp F).mono_measure (Measure.restrict_mono hBsub le_rfl)
  have hFU : IntegrableOn (fun z => F z ^ (2 : ℕ)) U volume :=
    (MeasureTheory.Lp.memLp F).integrable_sq
  have hsqrt : Real.sqrt (∫ z in B, F z ^ (2 : ℕ) ∂volume) ≤ ‖F‖ := by
    rw [← sqrt_integral_sq_eq_norm_scalarL2 F]
    refine Real.sqrt_le_sqrt ?_
    exact setIntegral_mono_set hFU (Filter.Eventually.of_forall fun z => sq_nonneg (F z))
      (LE.le.eventuallyLE hBsub)
  have hsplit : shiftedFieldSetIntegral hnu halpha hU hUsub f B A -
      shiftedFieldSetIntegral hnu halpha hU hUsub f B A0 = ∫ z in B, F z ∂volume := by
    let _ : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hBfin⟩
    have hIA : IntegrableOn (fun z => shiftedFieldResolvent hnu halpha hU hUsub f A z)
        B volume := ((MeasureTheory.Lp.memLp
          (shiftedFieldResolvent hnu halpha hU hUsub f A)).mono_measure
            (Measure.restrict_mono hBsub le_rfl)).integrable one_le_two
    have hI0 : IntegrableOn (fun z => shiftedFieldResolvent hnu halpha hU hUsub f A0 z)
        B volume := ((MeasureTheory.Lp.memLp
          (shiftedFieldResolvent hnu halpha hU hUsub f A0)).mono_measure
            (Measure.restrict_mono hBsub le_rfl)).integrable one_le_two
    rw [shiftedFieldSetIntegral, shiftedFieldSetIntegral, ← integral_sub hIA hI0]
    have hs := (MeasureTheory.Lp.coeFn_sub
      (shiftedFieldResolvent hnu halpha hU hUsub f A)
      (shiftedFieldResolvent hnu halpha hU hUsub f A0)).filter_mono
        (ae_mono (Measure.restrict_mono hBsub le_rfl))
    apply integral_congr_ae
    filter_upwards [hs] with z hz
    change shiftedFieldResolvent hnu halpha hU hUsub f A z -
      shiftedFieldResolvent hnu halpha hU hUsub f A0 z = F z
    exact hz.symm
  rw [Real.dist_eq, hsplit]
  have hint := Algsuperdiff.Section5.Support.abs_setIntegral_le_sqrt hBfin hFB
  have hnorm : ‖F‖ < eps / (S + 1) := by
    simpa [F, dist_eq_norm] using hclose A hA
  have hmain : |∫ z in B, F z ∂volume| ≤ S * ‖F‖ :=
    hint.trans (mul_le_mul_of_nonneg_left hsqrt hS)
  have hfrac : S * (eps / (S + 1)) < eps := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  exact lt_of_le_of_lt hmain
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hnorm.le hS) hfrac)

end

end Algsuperdiff.Section5.Measurability.ShiftedCoefficientContinuity
