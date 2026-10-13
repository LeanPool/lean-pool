/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Carrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionGlue
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.MeanFinalCore

/-!
# BoundaryReflectedCoeff

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Coefficients under one coordinate face reflection

Reflecting a divergence-form coefficient in the hyperplane `{y i = c}`
conjugates the matrix by the coordinate sign flip in direction `i`.  The
conjugation fixes the identity and is an isometry for the operator norm, so it
preserves exactly the distance-to-identity quantity that the small-contrast
estimates consume.  The one-face reflected field keeps the original coefficient
on the retained half, installs the conjugated pullback on the reflected half,
and is the identity on the null interface.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-! ## 1. Conjugation by a coordinate sign flip -/

/-- The coordinate sign flip attached to the hyperplane with normal `i`. -/
def faceReflectSign (i j : Fin d) : ℝ := if j = i then -1 else 1

theorem faceReflectSign_mul_self (i j : Fin d) :
    faceReflectSign i j * faceReflectSign i j = 1 := by
  unfold faceReflectSign
  by_cases h : j = i <;> simp [h]

/-- Conjugation of a matrix by the coordinate sign flip in direction `i`. -/
def faceReflectMat (i : Fin d) (A : Mat d) : Mat d :=
  fun j k => faceReflectSign i j * (faceReflectSign i k * A j k)

theorem faceReflectMat_apply (i : Fin d) (A : Mat d) (j k : Fin d) :
    faceReflectMat i A j k = faceReflectSign i j * (faceReflectSign i k * A j k) :=
  rfl

theorem faceReflectMat_one (i : Fin d) :
    faceReflectMat i (1 : Mat d) = (1 : Mat d) := by
  ext j k
  rw [faceReflectMat_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [Matrix.one_apply_eq]
    have h := faceReflectSign_mul_self i j
    calc
      faceReflectSign i j * (faceReflectSign i j * 1) =
          faceReflectSign i j * faceReflectSign i j := by ring
      _ = 1 := h
  · rw [Matrix.one_apply_ne hjk, mul_zero, mul_zero]

theorem faceReflectMat_sub (i : Fin d) (A B : Mat d) :
    faceReflectMat i (A - B) = faceReflectMat i A - faceReflectMat i B := by
  ext j k
  simp only [faceReflectMat_apply, Matrix.sub_apply]
  ring

theorem coordReflectionLinear_involutive_local (i : Fin d) (v : Vec d) :
    coordReflectionLinear i (coordReflectionLinear i v) = v := by
  funext k
  rw [coordReflectionLinear_apply_coord, coordReflectionLinear_apply_coord]
  by_cases hk : k = i <;> simp [hk]

theorem vecDot_coordReflectionLinear_both (i : Fin d) (v w : Vec d) :
    vecDot (coordReflectionLinear i v) (coordReflectionLinear i w) = vecDot v w := by
  simp only [vecDot]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coordReflectionLinear_apply_coord, coordReflectionLinear_apply_coord]
  by_cases hk : k = i <;> simp [hk]

/-- The conjugated matrix acts on the reflected vector by reflecting the
original action. -/
theorem matVecMul_faceReflectMat (i : Fin d) (A : Mat d) (v : Vec d) :
    matVecMul (faceReflectMat i A) v =
      coordReflectionLinear i (matVecMul A (coordReflectionLinear i v)) := by
  funext j
  rw [coordReflectionLinear_apply_coord]
  simp only [matVecMul, faceReflectMat_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coordReflectionLinear_apply_coord]
  simp only [faceReflectSign]
  split_ifs <;> ring

theorem matVecMul_faceReflectMat_coordReflectionLinear
    (i : Fin d) (A : Mat d) (v : Vec d) :
    matVecMul (faceReflectMat i A) (coordReflectionLinear i v) =
      coordReflectionLinear i (matVecMul A v) := by
  rw [matVecMul_faceReflectMat, coordReflectionLinear_involutive_local]

theorem norm_ofVec_coordReflectionLinear (i : Fin d) (v : Vec d) :
    ‖HilbertVec.ofVec (coordReflectionLinear i v)‖ = ‖HilbertVec.ofVec v‖ := by
  have hsq : ‖HilbertVec.ofVec (coordReflectionLinear i v)‖ ^ 2 =
      ‖HilbertVec.ofVec v‖ ^ 2 := by
    rw [HilbertVec.norm_sq_ofVec, HilbertVec.norm_sq_ofVec]
    exact vecDot_coordReflectionLinear_both i v v
  calc
    ‖HilbertVec.ofVec (coordReflectionLinear i v)‖ =
        Real.sqrt (‖HilbertVec.ofVec (coordReflectionLinear i v)‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖HilbertVec.ofVec v‖ ^ 2) := by rw [hsq]
    _ = ‖HilbertVec.ofVec v‖ := Real.sqrt_sq (norm_nonneg _)

private theorem norm_applyMat_faceReflectMat_le (i : Fin d) (A : Mat d) :
    ‖HilbertVec.applyMat (faceReflectMat i A)‖ ≤ ‖HilbertVec.applyMat A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro x
  have hval : HilbertVec.applyMat (faceReflectMat i A) x =
      HilbertVec.ofVec (coordReflectionLinear i
        (matVecMul A (coordReflectionLinear i x.toVec))) := by
    rw [HilbertVec.applyMat_apply, matVecMul_faceReflectMat]
  rw [hval, norm_ofVec_coordReflectionLinear]
  have hstep : ‖HilbertVec.ofVec (matVecMul A (coordReflectionLinear i x.toVec))‖ =
      ‖HilbertVec.applyMat A (HilbertVec.ofVec (coordReflectionLinear i x.toVec))‖ := by
    rw [HilbertVec.applyMat_apply, HilbertVec.toVec_ofVec]
  rw [hstep]
  refine le_trans ((HilbertVec.applyMat A).le_opNorm _) ?_
  rw [norm_ofVec_coordReflectionLinear, HilbertVec.ofVec_toVec]

/-- Conjugation by a coordinate sign flip is an isometry of the operator
norm. -/
theorem norm_applyMat_faceReflectMat (i : Fin d) (A : Mat d) :
    ‖HilbertVec.applyMat (faceReflectMat i A)‖ = ‖HilbertVec.applyMat A‖ := by
  refine le_antisymm (norm_applyMat_faceReflectMat_le i A) ?_
  have hback : faceReflectMat i (faceReflectMat i A) = A := by
    ext j k
    simp only [faceReflectMat_apply]
    have hj := faceReflectSign_mul_self i j
    have hk := faceReflectSign_mul_self i k
    calc
      faceReflectSign i j * (faceReflectSign i k *
          (faceReflectSign i j * (faceReflectSign i k * A j k))) =
          (faceReflectSign i j * faceReflectSign i j) *
            ((faceReflectSign i k * faceReflectSign i k) * A j k) := by ring
      _ = A j k := by rw [hj, hk]; ring
  calc
    ‖HilbertVec.applyMat A‖ =
        ‖HilbertVec.applyMat (faceReflectMat i (faceReflectMat i A))‖ := by rw [hback]
    _ ≤ ‖HilbertVec.applyMat (faceReflectMat i A)‖ :=
      norm_applyMat_faceReflectMat_le i (faceReflectMat i A)

/-- Conjugation preserves the distance to the identity. -/
theorem norm_applyMat_faceReflectMat_sub_one (i : Fin d) (A : Mat d) :
    ‖HilbertVec.applyMat (faceReflectMat i A - (1 : Mat d))‖ =
      ‖HilbertVec.applyMat (A - (1 : Mat d))‖ := by
  have hrewrite : faceReflectMat i A - (1 : Mat d) =
      faceReflectMat i (A - (1 : Mat d)) := by
    rw [faceReflectMat_sub, faceReflectMat_one]
  rw [hrewrite, norm_applyMat_faceReflectMat]

/-! ## 2. The one-face reflected coefficient field -/

/-- The one-face reflected coefficient in the hyperplane `{y i = c}`: the
original field on the `sigma`-side, the conjugated pullback on the other side,
and the identity on the interface. -/
def faceReflectedCoeff (c : ℝ) (i : Fin d) (sigma : ℝ) (a : CoeffField d) :
    CoeffField d :=
  fun y =>
    if 0 < sigma * (c - y i) then a y
    else if 0 < sigma * (y i - c) then
      faceReflectMat i (a (coordFaceReflection c i y))
    else (1 : Mat d)

theorem faceReflectedCoeff_of_pos {c : ℝ} {i : Fin d} {sigma : ℝ}
    (a : CoeffField d) {y : Vec d} (hy : 0 < sigma * (c - y i)) :
    faceReflectedCoeff c i sigma a y = a y := by
  rw [faceReflectedCoeff, ite_eq_left hy]

theorem faceReflectedCoeff_of_neg {c : ℝ} {i : Fin d} {sigma : ℝ}
    (a : CoeffField d) {y : Vec d} (hy : 0 < sigma * (y i - c)) :
    faceReflectedCoeff c i sigma a y =
      faceReflectMat i (a (coordFaceReflection c i y)) := by
  have hnot : ¬ (0 < sigma * (c - y i)) := by
    have hneg : sigma * (c - y i) = -(sigma * (y i - c)) := by ring
    rw [hneg]
    exact not_lt.2 (neg_nonpos.2 hy.le)
  rw [faceReflectedCoeff, ite_eq_right hnot, ite_eq_left hy]

theorem coordFaceReflection_coord (c : ℝ) (i : Fin d) (y : Vec d) :
    coordFaceReflection c i y i = 2 * c - y i := by
  have h1 : coordFaceReflection c i y i =
      coordReflectionLinear i y i + coordFaceReflectionOffset c i i := rfl
  have h2 : coordReflectionLinear i y i = -(y i) := by
    simp [coordReflectionLinear]
  have h3 : coordFaceReflectionOffset c i i = 2 * c := by
    simp [coordFaceReflectionOffset]
  rw [h1, h2, h3]
  ring

/-- Off the interface hyperplane, membership in the retained half is decided by
the sign condition. -/
theorem faceReflectedCoeff_eq_on_faceHalf {c : ℝ} {i : Fin d} {sigma : ℝ}
    {U : Set (Vec d)} (a : CoeffField d) {y : Vec d}
    (hy : y ∈ faceHalf U i c sigma) :
    faceReflectedCoeff c i sigma a y = a y :=
  faceReflectedCoeff_of_pos a hy.2

theorem faceReflectedCoeff_eq_reflected {c : ℝ} {i : Fin d} {sigma : ℝ}
    {U : Set (Vec d)} (a : CoeffField d) {y : Vec d}
    (hy : y ∈ U) (hynot : y ∉ faceHalf U i c sigma) (hne : y i ≠ c)
    (hsigma : sigma ≠ 0) :
    faceReflectedCoeff c i sigma a y =
      faceReflectMat i (a (coordFaceReflection c i y)) := by
  have hle : ¬ (0 < sigma * (c - y i)) := fun hpos => hynot ⟨hy, hpos⟩
  have hnezero : sigma * (c - y i) ≠ 0 := by
    intro hzero
    rcases mul_eq_zero.1 hzero with h | h
    · exact hsigma h
    · exact hne (by linarith only [h])
  have hneg : sigma * (c - y i) < 0 := lt_of_le_of_ne (not_lt.1 hle) hnezero
  have hpos : 0 < sigma * (y i - c) := by
    have hid : sigma * (y i - c) = -(sigma * (c - y i)) := by ring
    rw [hid]
    exact neg_pos.2 hneg
  exact faceReflectedCoeff_of_neg a hpos

theorem measurable_faceReflectedCoeff {c : ℝ} {i : Fin d} {sigma : ℝ}
    {a : CoeffField d} (ha : Measurable a) :
    Measurable (faceReflectedCoeff c i sigma a) := by
  classical
  refine (measurable_pi_iff).2 fun j => (measurable_pi_iff).2 fun k => ?_
  have hcoord : Measurable fun y : Vec d => y i := measurable_pi_apply i
  have hset1 : MeasurableSet {y : Vec d | 0 < sigma * (c - y i)} :=
    measurableSet_lt measurable_const ((measurable_const.sub hcoord).const_mul sigma)
  have hset2 : MeasurableSet {y : Vec d | 0 < sigma * (y i - c)} :=
    measurableSet_lt measurable_const ((hcoord.sub measurable_const).const_mul sigma)
  have hentry : Measurable fun y : Vec d => a y j k :=
    ((measurable_pi_iff).1 ((measurable_pi_iff).1 ha j)) k
  have hrefl : Measurable fun y : Vec d =>
      faceReflectMat i (a (coordFaceReflection c i y)) j k := by
    have hcomp : Measurable fun y : Vec d => a (coordFaceReflection c i y) j k :=
      hentry.comp (continuous_coordFaceReflection c i).measurable
    simpa only [faceReflectMat_apply] using
      (hcomp.const_mul (faceReflectSign i k)).const_mul (faceReflectSign i j)
  have hmain : Measurable fun y : Vec d =>
      if 0 < sigma * (y i - c) then
        faceReflectMat i (a (coordFaceReflection c i y)) j k
      else (1 : Mat d) j k :=
    Measurable.ite hset2 hrefl measurable_const
  have hunfold : (fun y : Vec d => faceReflectedCoeff c i sigma a y j k) =
      fun y : Vec d =>
        if 0 < sigma * (c - y i) then a y j k
        else if 0 < sigma * (y i - c) then
          faceReflectMat i (a (coordFaceReflection c i y)) j k
        else (1 : Mat d) j k := by
    funext y
    rw [faceReflectedCoeff]
    split_ifs <;> rfl
  rw [hunfold]
  exact Measurable.ite hset1 hentry hmain

/-- The reflected field inherits the small-contrast bound of the original
field on the retained half. -/
theorem coefficientIdentityDistanceLE_faceReflectedCoeff
    {c : ℝ} {i : Fin d} {sigma : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    {delta : ℝ} (hsigma : sigma ≠ 0)
    (hUopen : IsOpen U)
    (hUsymm : ∀ y : Vec d, coordFaceReflection c i y ∈ U ↔ y ∈ U)
    (ha : CoefficientIdentityDistanceLE (faceHalf U i c sigma) a delta) :
    CoefficientIdentityDistanceLE U (faceReflectedCoeff c i sigma a) delta := by
  classical
  set H : Set (Vec d) := faceHalf U i c sigma with hH
  have hHmeas : MeasurableSet H := (isOpen_faceHalf hUopen i c sigma).measurableSet
  have hnull : volume {y : Vec d | y i = c} = 0 :=
    Algsuperdiff.Section4.Provider.ExcessDecay.Schauder.volume_coordHyperplane_eq_zero i c
  have haGlobal : ∀ᵐ y ∂(volume : Measure (Vec d)),
      y ∈ H → ‖HilbertVec.applyMat (a y - (1 : Mat d))‖ ≤ delta :=
    (ae_restrict_iff' hHmeas).1 ha
  have hreflAE : ∀ᵐ y ∂(volume : Measure (Vec d)),
      coordFaceReflection c i y ∈ H →
        ‖HilbertVec.applyMat (a (coordFaceReflection c i y) - (1 : Mat d))‖ ≤ delta :=
    (measurePreserving_coordFaceReflection c i).quasiMeasurePreserving.ae haGlobal
  have hplane : ∀ᵐ y ∂(volume : Measure (Vec d)), y i ≠ c := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  refine (ae_restrict_iff' hUopen.measurableSet).2 ?_
  filter_upwards [haGlobal, hreflAE, hplane] with y hy hry hplaney hyU
  by_cases hyH : y ∈ H
  · rw [faceReflectedCoeff_eq_on_faceHalf (U := U) a hyH]
    exact hy hyH
  · have hrmem : coordFaceReflection c i y ∈ H := by
      refine ⟨(hUsymm y).2 hyU, ?_⟩
      have hle : ¬ (0 < sigma * (c - y i)) := fun hpos => hyH ⟨hyU, hpos⟩
      have hnezero : sigma * (c - y i) ≠ 0 := by
        intro hzero
        rcases mul_eq_zero.1 hzero with h | h
        · exact hsigma h
        · exact hplaney (by linarith only [h])
      have hneg : sigma * (c - y i) < 0 := lt_of_le_of_ne (not_lt.1 hle) hnezero
      show (0 : ℝ) < sigma * (c - coordFaceReflection c i y i)
      rw [coordFaceReflection_coord]
      have hid : sigma * (c - (2 * c - y i)) = -(sigma * (c - y i)) := by ring
      rw [hid]
      exact neg_pos.2 hneg
    rw [faceReflectedCoeff_eq_reflected (U := U) a hyU hyH hplaney hsigma,
      norm_applyMat_faceReflectMat_sub_one]
    exact hry hrmem

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
