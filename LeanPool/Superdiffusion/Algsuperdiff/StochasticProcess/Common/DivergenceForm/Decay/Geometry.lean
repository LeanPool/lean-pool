/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.ExponentialWeight
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.QuantitativeCutoff

/-!
# Geometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Geometry for the exponentially weighted estimates

The weighted estimates need two explicit smooth objects: a localization with a
quantitative coordinate-gradient bound, and a phase with unit coordinate
gradient comparable to the distance from a point.

The localization is the smooth ball cutoff of the cutoff layer, whose
operator-norm gradient bound is converted here into the coordinate form the
weighted estimate consumes.

Two phases are supplied.  The outward phase is the regularized radius
`radialPhase z delta x = sqrt (|x - z| ^ 2 + delta ^ 2) - delta`, which is
smooth everywhere, has coordinate gradient of length at most one, and differs
from `|x - z|` by at most `delta`; it increases away from `z`, so it measures
decay away from a ball or cube around `z`.  The inward phase is its negative,
`inwardPhase z delta = -radialPhase z delta`, which increases towards `z`, so
it measures decay from the inscribed radius of a cube centred at `z`.

Each phase comes with the two comparisons the pointwise estimate consumes.
For the outward phase, a transition layer inside `{y : |y - z| <= s}` admits
`tA := s`, and a point `x` with a ball of radius `rho` around it admits
`tx := |x - z| - rho - delta`, so `tx - tA` is the distance from `x` to the
layer up to `rho + delta`.  For the inward phase, a transition layer inside
`{y : R <= |y - z|}` admits `tA := -R + delta` and the same point admits
`tx := -(|x - z| + rho)`, so `tx - tA` is `R - |x - z|` up to `rho + delta`.

## Main results

- `DivergenceFormProcess.Decay.vecNormSq_fderiv_le_of_norm_fderiv_le`
- `DivergenceFormProcess.Decay.vecNormSq_fderiv_ballCutoff_le`
- `DivergenceFormProcess.Decay.contDiff_radialPhase`
- `DivergenceFormProcess.Decay.vecNormSq_fderiv_radialPhase_le_one`
- `DivergenceFormProcess.Decay.radialPhase_bounds`
- `DivergenceFormProcess.Decay.le_euclideanNorm_sub_of_notMem_euclideanBall`
- `DivergenceFormProcess.Decay.contDiff_inwardPhase`
- `DivergenceFormProcess.Decay.vecNormSq_fderiv_inwardPhase_le_one`
- `DivergenceFormProcess.Decay.inwardPhase_le_of_le_euclideanNorm`
- `DivergenceFormProcess.Decay.le_inwardPhase_of_mem_euclideanBall`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory

variable {d : ℕ}

/-- An operator-norm bound on the derivative gives the coordinate bound the
weighted estimates consume. -/
theorem vecNormSq_fderiv_le_of_norm_fderiv_le {f : Vec d → ℝ} {C : ℝ}
    (hC : 0 ≤ C) {x : Vec d} (h : ‖fderiv ℝ f x‖ ≤ C) :
    vecNormSq (fun i => (fderiv ℝ f x) (basisVec i)) ≤ (d : ℝ) * C ^ 2 := by
  have hbasis : ∀ i : Fin d, ‖basisVec (d := d) i‖ ≤ 1 := by
    intro i
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro j
    rw [basisVec_apply]
    by_cases hji : j = i <;> simp [hji]
  have hcoord : ∀ i : Fin d,
      ((fderiv ℝ f x) (basisVec i)) ^ 2 ≤ C ^ 2 := by
    intro i
    have happ : ‖(fderiv ℝ f x) (basisVec i)‖ ≤ ‖fderiv ℝ f x‖ := by
      calc
        ‖(fderiv ℝ f x) (basisVec i)‖ ≤
            ‖fderiv ℝ f x‖ * ‖basisVec (d := d) i‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ f x‖ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hbasis i) (norm_nonneg _)
    have habs : |(fderiv ℝ f x) (basisVec i)| ≤ C := by
      rw [← Real.norm_eq_abs]
      exact happ.trans h
    have hsq := (sq_le_sq₀ (abs_nonneg _) hC).2 habs
    rwa [sq_abs] at hsq
  calc
    vecNormSq (fun i => (fderiv ℝ f x) (basisVec i)) =
        ∑ i : Fin d, ((fderiv ℝ f x) (basisVec i)) ^ 2 := by
      simp only [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ _i : Fin d, C ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * C ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-- Coordinate gradient bound for the smooth ball cutoff. -/
theorem vecNormSq_fderiv_ballCutoff_le (x₀ : Vec d) {r s : ℝ} (hr : 0 < r)
    (hrs : r < s) (x : Vec d) :
    vecNormSq (fun i =>
        (fderiv ℝ (QuantitativeBallCutoff.canonicalFun x₀ r s) x) (basisVec i)) ≤
      (d : ℝ) *
        (smoothTransitionProfile.derivBound * (2 * (d : ℝ) / (s - r))) ^ 2 := by
  have hgrad := QuantitativeBallCutoff.canonicalFun_gradient_bound x₀ hr hrs x
  exact vecNormSq_fderiv_le_of_norm_fderiv_le ((norm_nonneg _).trans hgrad) hgrad

section RadialPhase

variable (z : Vec d) (delta : ℝ)

/-- The regularized radius about a point. -/
def radialSq (z : Vec d) (delta : ℝ) (x : Vec d) : ℝ :=
  vecNormSq (x - z) + delta ^ 2

/-- The smooth phase used by the exponential weight: the regularized radius,
normalized to vanish at the centre. -/
def radialPhase (z : Vec d) (delta : ℝ) (x : Vec d) : ℝ :=
  Real.sqrt (radialSq z delta x) - delta

variable {z delta}

/-- The regularized squared radius is bounded below by the regularization. -/
theorem radialSq_pos (hdelta : 0 < delta) (x : Vec d) :
    0 < radialSq z delta x := by
  have := vecNormSq_nonneg (x - z)
  have hd : (0 : ℝ) < delta ^ 2 := by positivity
  simp only [radialSq]
  linarith only [this, hd]

/-- The regularized squared radius has the expected derivative. -/
theorem hasFDerivAt_radialSq (x : Vec d) :
    HasFDerivAt (radialSq z delta)
      (∑ i : Fin d, (2 * (x i - z i)) •
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) x := by
  have hcoord : ∀ i : Fin d,
      HasFDerivAt (fun y : Vec d => (y i - z i) ^ 2)
        ((2 * (x i - z i)) •
          (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) x := by
    intro i
    have hproj : HasFDerivAt (fun y : Vec d => y i)
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) x :=
      (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).hasFDerivAt
    have hsub : HasFDerivAt (fun y : Vec d => y i - z i)
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) x := by
      simpa using hproj.sub_const (z i)
    have hp := hsub.pow 2
    simpa using hp
  have hsum : HasFDerivAt (fun y : Vec d => ∑ i : Fin d, (y i - z i) ^ 2)
      (∑ i : Fin d, (2 * (x i - z i)) •
        (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) x :=
    HasFDerivAt.fun_sum fun i _ => hcoord i
  have hshape : (fun y : Vec d => ∑ i : Fin d, (y i - z i) ^ 2) =
      fun y => radialSq z delta y - delta ^ 2 := by
    funext y
    simp only [radialSq, vecNormSq, vecDot, Pi.sub_apply, pow_two]
    ring_nf
  rw [hshape] at hsum
  simpa using hsum.add_const (delta ^ 2)

/-- The regularized radius is smooth. -/
theorem contDiff_radialPhase (hdelta : 0 < delta) :
    ContDiff ℝ (⊤ : ℕ∞) (radialPhase z delta) := by
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (radialSq z delta) := by
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec d => ∑ i : Fin d, (y i - z i) ^ 2) := by
      exact ContDiff.sum fun i _ =>
        (((contDiff_apply ℝ ℝ i).sub contDiff_const).pow 2)
    have hshape : (fun y : Vec d => ∑ i : Fin d, (y i - z i) ^ 2) =
        fun y => radialSq z delta y - delta ^ 2 := by
      funext y
      simp only [radialSq, vecNormSq, vecDot, Pi.sub_apply, pow_two]
      ring_nf
    rw [hshape] at hcoord
    have hadd := hcoord.add (contDiff_const (c := delta ^ 2) (n := (⊤ : ℕ∞)))
    have hshape2 :
        (fun y : Vec d => radialSq z delta y - delta ^ 2 + delta ^ 2) =
          radialSq z delta := by
      funext y
      ring
    rwa [hshape2] at hadd
  refine ContDiff.sub ?_ contDiff_const
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (hsq.contDiffAt).sqrt (radialSq_pos hdelta x).ne'

/-- The coordinate gradient of the regularized radius has length at most one. -/
theorem vecNormSq_fderiv_radialPhase_le_one (hdelta : 0 < delta) (x : Vec d) :
    vecNormSq (fun i => (fderiv ℝ (radialPhase z delta) x) (basisVec i)) ≤ 1 := by
  have hpos := radialSq_pos (z := z) hdelta x
  have hsqrtPos : 0 < Real.sqrt (radialSq z delta x) := Real.sqrt_pos.2 hpos
  have hsq := hasFDerivAt_radialSq (z := z) (delta := delta) x
  have hzero : Real.sqrt (radialSq z delta x) ≠ 0 := hsqrtPos.ne'
  have hphase : HasFDerivAt (radialPhase z delta)
      ((1 / (2 * Real.sqrt (radialSq z delta x))) •
        (∑ i : Fin d, (2 * (x i - z i)) •
          (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))) x :=
    (hsq.sqrt hpos.ne').sub_const delta
  have hcoord : ∀ i : Fin d,
      (fderiv ℝ (radialPhase z delta) x) (basisVec i) =
        (x i - z i) / Real.sqrt (radialSq z delta x) := by
    intro i
    rw [hphase.fderiv]
    simp only [smul_apply, FunLike.coe_sum,
      Finset.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      basisVec_apply]
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl, mul_one]
      field_simp
    · intro j _ hji
      rw [ite_eq_right (by simpa using hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hval : vecNormSq (fun i =>
      (fderiv ℝ (radialPhase z delta) x) (basisVec i)) =
      vecNormSq (x - z) / radialSq z delta x := by
    simp only [vecNormSq, vecDot, hcoord, Pi.sub_apply]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_mul_div_comm, Real.mul_self_sqrt hpos.le]
  rw [hval, div_le_one hpos]
  simp only [radialSq]
  have hd : (0 : ℝ) ≤ delta ^ 2 := sq_nonneg _
  linarith only [hd]

/-- The regularized radius is nonnegative and brackets the Euclidean
distance. -/
theorem radialPhase_bounds (hdelta : 0 < delta) (x : Vec d) :
    0 ≤ radialPhase z delta x ∧
      euclideanNorm (x - z) - delta ≤ radialPhase z delta x ∧
      radialPhase z delta x ≤ euclideanNorm (x - z) := by
  have hpos := radialSq_pos (z := z) hdelta x
  have hnn : (0 : ℝ) ≤ vecNormSq (x - z) := vecNormSq_nonneg _
  have hlow : delta ≤ Real.sqrt (radialSq z delta x) := by
    have hdd : delta ^ 2 ≤ radialSq z delta x := by
      simp only [radialSq]
      linarith only [hnn]
    have := Real.sqrt_le_sqrt hdd
    rwa [Real.sqrt_sq hdelta.le] at this
  have hnorm : euclideanNorm (x - z) ≤ Real.sqrt (radialSq z delta x) := by
    refine Real.sqrt_le_sqrt ?_
    simp only [radialSq]
    have hd : (0 : ℝ) ≤ delta ^ 2 := sq_nonneg _
    linarith only [hd]
  have hupper : Real.sqrt (radialSq z delta x) ≤
      euclideanNorm (x - z) + delta := by
    have hsq : radialSq z delta x ≤ (euclideanNorm (x - z) + delta) ^ 2 := by
      have hsqn : euclideanNorm (x - z) ^ 2 = vecNormSq (x - z) :=
        euclideanNorm_sq _
      have hcross : 0 ≤ 2 * euclideanNorm (x - z) * delta :=
        mul_nonneg (mul_nonneg (by norm_num) (euclideanNorm_nonneg _)) hdelta.le
      simp only [radialSq]
      nlinarith only [hsqn, hcross]
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (add_nonneg (euclideanNorm_nonneg _) hdelta.le)] at this
  refine ⟨by simp only [radialPhase]; linarith only [hlow], ?_, ?_⟩
  · simp only [radialPhase]
    linarith only [hnorm]
  · simp only [radialPhase]
    linarith only [hupper]

/-- The Euclidean magnitude obeys the triangle inequality, through the
continuous linear promotion to the Hilbert carrier. -/
private theorem euclideanNorm_add_le (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  have hnorm : ∀ w : Vec d, euclideanNorm w = ‖HilbertVec.ofVecL d w‖ := by
    intro w
    rw [HilbertVec.ofVecL_apply, euclideanNorm_eq_norm_ofVec]
  rw [hnorm, hnorm x, hnorm y, map_add]
  exact norm_add_le _ _

/-- A point of a Euclidean ball is within the radius of the centre. -/
theorem euclideanNorm_sub_lt_of_mem_euclideanBall {x y : Vec d} {rho : ℝ}
    (hrho : 0 ≤ rho) (hy : y ∈ euclideanBall x rho) :
    euclideanNorm (y - x) < rho := by
  have hy' : euclideanSqDist y x < rho ^ 2 := hy
  have hsq : euclideanNorm (y - x) ^ 2 < rho ^ 2 := by
    rw [euclideanNorm_sq]
    exact hy'
  exact lt_of_pow_lt_pow_left₀ 2 hrho hsq

/-- A point outside a Euclidean ball is at least the radius from the centre.
This is the form the transition-layer hypothesis consumes when the layer is
read off as the complement of an inner ball. -/
theorem le_euclideanNorm_sub_of_notMem_euclideanBall {x y : Vec d} {rho : ℝ}
    (hy : y ∉ euclideanBall x rho) :
    rho ≤ euclideanNorm (y - x) := by
  by_contra hcon
  push Not at hcon
  refine hy ?_
  show euclideanSqDist y x < rho ^ 2
  rw [euclideanSqDist, ← euclideanNorm_sq]
  exact pow_lt_pow_left₀ hcon (euclideanNorm_nonneg _) (by norm_num)

/-- The inward phase about a centre: the negative of the regularized radius.
It increases towards the centre, so it measures decay from the inscribed
radius of a region centred there. -/
def inwardPhase (z : Vec d) (delta : ℝ) (x : Vec d) : ℝ :=
  -radialPhase z delta x

/-- The inward phase is smooth. -/
theorem contDiff_inwardPhase (hdelta : 0 < delta) :
    ContDiff ℝ (⊤ : ℕ∞) (inwardPhase z delta) :=
  (contDiff_radialPhase hdelta).neg

/-- The coordinate gradient of the inward phase has length at most one. -/
theorem vecNormSq_fderiv_inwardPhase_le_one (hdelta : 0 < delta) (x : Vec d) :
    vecNormSq (fun i =>
        (fderiv ℝ (inwardPhase z delta) x) (basisVec i)) ≤ 1 := by
  have hfd : fderiv ℝ (inwardPhase z delta) x =
      -fderiv ℝ (radialPhase z delta) x := by
    simpa only [inwardPhase] using!
      fderiv_neg (f := radialPhase z delta) (x := x)
  have hval : vecNormSq (fun i =>
        (fderiv ℝ (inwardPhase z delta) x) (basisVec i)) =
      vecNormSq (fun i =>
        (fderiv ℝ (radialPhase z delta) x) (basisVec i)) := by
    rw [hfd]
    simp only [vecNormSq, vecDot, neg_apply, neg_mul_neg]
  rw [hval]
  exact vecNormSq_fderiv_radialPhase_le_one hdelta x

/-- Beyond radius `R` the inward phase is at most `-R + delta`, which is the
form the transition-layer hypothesis consumes. -/
theorem inwardPhase_le_of_le_euclideanNorm (hdelta : 0 < delta) {R : ℝ}
    {y : Vec d} (hy : R ≤ euclideanNorm (y - z)) :
    inwardPhase z delta y ≤ -R + delta := by
  have hlow := (radialPhase_bounds (z := z) hdelta y).2.1
  simp only [inwardPhase]
  linarith only [hlow, hy]

/-- On a ball of radius `rho` about `x` the inward phase is at least
`-(euclideanNorm (x - z) + rho)`, which is the form the near-point hypothesis
consumes. -/
theorem le_inwardPhase_of_mem_euclideanBall (hdelta : 0 < delta) {x y : Vec d}
    {rho : ℝ} (hrho : 0 ≤ rho) (hy : y ∈ euclideanBall x rho) :
    -(euclideanNorm (x - z) + rho) ≤ inwardPhase z delta y := by
  have hup := (radialPhase_bounds (z := z) hdelta y).2.2
  have hyx : euclideanNorm (y - x) < rho :=
    euclideanNorm_sub_lt_of_mem_euclideanBall hrho hy
  have htri : euclideanNorm (y - z) ≤
      euclideanNorm (y - x) + euclideanNorm (x - z) := by
    rw [← sub_add_sub_cancel y x z]
    exact euclideanNorm_add_le _ _
  simp only [inwardPhase]
  linarith only [hup, hyx, htri]

end RadialPhase

end DivergenceFormProcess.Decay
