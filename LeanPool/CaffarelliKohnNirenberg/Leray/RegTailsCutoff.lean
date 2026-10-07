/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsWeakIdentity
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTransportCutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Commutator.SphereTransport

/-!
# Exterior cutoffs for the regularized velocity tail

The compact cutoffs approximate a smooth exterior weight whose gradient is
bounded by the inverse width of its transition annulus.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A smooth weight that vanishes on the inner ball and equals one outside the
outer ball. -/
@[expose]
def regTailsExteriorWeight (R1 R2 : ℝ) : Vec3 → ℝ :=
  fun x => 1 - CKN.canonicalBallCutoff 0 ((R1 + R2) / 2) R2 x

/-- The exterior weight is smooth. -/
theorem regTailsExteriorWeight_smooth {R1 R2 : ℝ}
    (hR1 : 0 < R1) (hR12 : R1 < R2) :
    ContDiff ℝ (⊤ : ℕ∞) (regTailsExteriorWeight R1 R2) := by
  unfold regTailsExteriorWeight
  have hR2 : 0 < R2 := lt_trans hR1 hR12
  have hmid : 0 ≤ (R1 + R2) / 2 := by positivity
  have hmidR : (R1 + R2) / 2 < R2 := by linarith only [hR12]
  exact contDiff_const.sub (CKN.canonicalBallCutoff_smooth 0 hmid hmidR)

/-- The exterior weight lies in the unit interval. -/
theorem regTailsExteriorWeight_unit {R1 R2 : ℝ}
    (x : Vec3) : 0 ≤ regTailsExteriorWeight R1 R2 x ∧
      regTailsExteriorWeight R1 R2 x ≤ 1 := by
  constructor
  · unfold regTailsExteriorWeight
    exact sub_nonneg.mpr
      (CKN.canonicalBallCutoff_le_one 0 ((R1 + R2) / 2) R2 x)
  · unfold regTailsExteriorWeight
    have h := CKN.canonicalBallCutoff_nonneg 0 ((R1 + R2) / 2) R2 x
    linarith only [h]

/-- The exterior weight vanishes through the inner ball. -/
theorem regTailsExteriorWeight_zero_inner {R1 R2 : ℝ}
    (hR1 : 0 < R1) (hR12 : R1 < R2) {x : Vec3}
    (hx : vec3EuclideanNorm x ≤ R1) :
    regTailsExteriorWeight R1 R2 x = 0 := by
  unfold regTailsExteriorWeight
  have hmid : R1 < (R1 + R2) / 2 := by linarith only [hR12]
  have hR2pos : 0 < R2 := lt_trans hR1 hR12
  have hmidpos : 0 < (R1 + R2) / 2 := by
    exact div_pos (add_pos hR1 hR2pos) (by norm_num)
  have hmidR : (R1 + R2) / 2 < R2 := by linarith only [hR12]
  have hnormEq : vec3EuclideanNorm x = CKN.vecEuclideanNorm (x - 0) := by
    rw [sub_zero, vec3EuclideanNorm_eq_l2,
      CKN.Foundation.Harmonic.Commutator.vecEuclideanNorm_eq_l2]
  have hxball : x ∈ CKN.euclideanBall 0 ((R1 + R2) / 2) := by
    apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hmidpos).2
    rw [← hnormEq]
    exact lt_of_le_of_lt hx hmid
  have hone := CKN.canonicalBallCutoff_eq_one_on_inner
    (x₀ := (0 : Vec3)) (r := (R1 + R2) / 2) (R := R2)
    hmidpos.le hmidR hxball
  rw [hone]
  norm_num

/-- The exterior weight equals one outside the outer ball. -/
theorem regTailsExteriorWeight_one_outer {R1 R2 : ℝ}
    (hR1 : 0 ≤ R1) (hR12 : R1 < R2) {x : Vec3}
    (hx : R2 ≤ vec3EuclideanNorm x) :
    regTailsExteriorWeight R1 R2 x = 1 := by
  unfold regTailsExteriorWeight
  have hzero : CKN.canonicalBallCutoff 0 ((R1 + R2) / 2) R2 x = 0 := by
    have hR2 : 0 < R2 := lt_of_le_of_lt hR1 hR12
    have hcut : CKN.canonicalBallCutoff 0 ((R1 + R2) / 2) R2 x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hmidpos : 0 ≤ (R1 + R2) / 2 := by positivity
      have hmidR : (R1 + R2) / 2 < R2 := by linarith only [hR12]
      have hsub := CKN.canonicalBallCutoff_tsupport_subset_outer
        (x₀ := (0 : Vec3)) hmidpos hmidR hmem
      have hnormEq : vec3EuclideanNorm x = CKN.vecEuclideanNorm (x - 0) := by
        rw [sub_zero, vec3EuclideanNorm_eq_l2,
          CKN.Foundation.Harmonic.Commutator.vecEuclideanNorm_eq_l2]
      have hnorm := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hR2).1 hsub
      rw [← hnormEq] at hnorm
      exact (not_lt_of_ge hx) hnorm
    exact hcut
  simp [hzero]

/-- Each coordinate derivative of the exterior weight is controlled by the
inverse width of its transition annulus. -/
theorem regTailsExteriorWeight_derivative_bound {R1 R2 : ℝ}
    (hR1 : 0 ≤ R1) (hR12 : R1 < R2) (i : Fin 3) (x : Vec3) :
    |spatialDeriv (regTailsExteriorWeight R1 R2) i x| ≤ 64 / (R2 - R1) := by
  let r : ℝ := (R1 + R2) / 2
  have hr : 0 ≤ r := by dsimp [r]; linarith only [hR1, hR12]
  have hrR : r < R2 := by dsimp [r]; linarith only [hR12]
  have hgap : R2 - r = (R2 - R1) / 2 := by dsimp [r]; ring
  have hgrad := CKN.canonicalBallCutoff_gradient_bound
    (x₀ := (0 : Vec3)) hr hrR x
  have hcoord := CKN.abs_apply_le_vecEuclideanNorm
    (CKN.classicalGradient (CKN.canonicalBallCutoff 0 r R2) x) i
  have hcanonical : |spatialDeriv (CKN.canonicalBallCutoff 0 r R2) i x| ≤
      64 / (R2 - R1) := by
    calc
      |spatialDeriv (CKN.canonicalBallCutoff 0 r R2) i x| ≤
          CKN.vecEuclideanNorm
            (CKN.classicalGradient (CKN.canonicalBallCutoff 0 r R2) x) := by
        simpa [spatialDeriv, CKN.classicalGradient_apply, CKN.basisVec_apply] using hcoord
      _ ≤ 32 / (R2 - r) := hgrad
      _ = 64 / (R2 - R1) := by
        rw [hgap]
        field_simp [ne_of_gt (sub_pos.mpr hR12)]
        ring
  have hdiff : spatialDeriv (regTailsExteriorWeight R1 R2) i x =
      -spatialDeriv (CKN.canonicalBallCutoff 0 r R2) i x := by
    unfold regTailsExteriorWeight spatialDeriv
    rw [fderiv_const_sub]
    rfl
  rw [hdiff, abs_neg]
  exact hcanonical

/-- Compact cutoffs of the exterior weight. Their extra derivative is the
vanishing outer-boundary error used when the compact support expands. -/
theorem regTails_compact_exterior_cutoffs {R1 R2 : ℝ}
    (hR1 : 0 < R1) (hR12 : R1 < R2) :
    ∃ f : Vec3 → ℝ,
      f = regTailsExteriorWeight R1 R2 ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x, vec3EuclideanNorm x ≤ R1 → f x = 0) ∧
      (∀ x, R2 ≤ vec3EuclideanNorm x → f x = 1) ∧
      (∀ x i, |spatialDeriv f i x| ≤ 64 / (R2 - R1)) ∧
      ∀ N : ℝ, R2 ≤ N →
        ∃ q : Vec3 → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) q ∧ HasCompactSupport q ∧
          (∀ x, 0 ≤ q x ∧ q x ≤ 1) ∧
          (∀ x, vec3EuclideanNorm x < N → q x = f x) ∧
          (∀ x i, spatialDeriv q i x =
            spatialDeriv f i x * regularisedEnergyCutoff N x +
              f x * spatialDeriv (regularisedEnergyCutoff N) i x) ∧
          (∀ x i, |spatialDeriv (regularisedEnergyCutoff N) i x| ≤ 32 / N) := by
  let f : Vec3 → ℝ := regTailsExteriorWeight R1 R2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := regTailsExteriorWeight_smooth hR1 hR12
  refine ⟨f, rfl, fun x => regTailsExteriorWeight_unit x,
    fun x hx => regTailsExteriorWeight_zero_inner hR1 hR12 hx,
    fun x hx => regTailsExteriorWeight_one_outer hR1.le hR12 hx,
    fun x i => regTailsExteriorWeight_derivative_bound hR1.le hR12 i x,
    fun N hN => ?_⟩
  let χ : Vec3 → ℝ := regularisedEnergyCutoff N
  let q : Vec3 → ℝ := fun x => f x * χ x
  have hNpos : 0 < N := hR1.trans hR12 |>.trans_le hN
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ :=
    regularisedEnergyCutoff_smooth N hNpos
  have hχcompact : HasCompactSupport χ := regularisedEnergyCutoff_compact N hNpos
  have hχunit (x : Vec3) : 0 ≤ χ x ∧ χ x ≤ 1 :=
    regularisedEnergyCutoff_mem_unitInterval N x
  have hχone {x : Vec3} (hx : vec3EuclideanNorm x < N) : χ x = 1 := by
    have hnormEq : vec3EuclideanNorm x = CKN.vecEuclideanNorm (x - 0) := by
      rw [sub_zero, vec3EuclideanNorm_eq_l2,
        CKN.Foundation.Harmonic.Commutator.vecEuclideanNorm_eq_l2]
    apply regularisedEnergyCutoff_eq_one_of_mem_ball N hNpos
    exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hNpos).2
      (by rw [← hnormEq]; exact hx)
  refine ⟨q, hf.mul hχsmooth, hχcompact.mul_left, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · exact mul_nonneg (regTailsExteriorWeight_unit x).1 (hχunit x).1
    · calc
        f x * χ x ≤ 1 * χ x :=
          mul_le_mul_of_nonneg_right (regTailsExteriorWeight_unit x).2 (hχunit x).1
        _ = χ x := one_mul _
        _ ≤ 1 := (hχunit x).2
  · intro x hx
    simp [q, χ, hχone hx]
  · intro x i
    change spatialDeriv (fun y => f y * χ y) i x = _
    rw [spatialDeriv_mul (hf.differentiable (by simp) x)
      (hχsmooth.differentiable (by simp) x)]
  · intro x i
    exact regularisedEnergyCutoff_derivative_bound N hNpos i x

end CKN.Leray

end
