/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityPotential
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-!
# Compact cutoffs for decaying Riesz potential tests

The cutoffs are taken from CKN's smooth ball cutoff API and are used to pass
from compact to decaying tests in `lem:riesz-duality`.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The spatial radius used by the compact approximations of a potential test. -/
@[expose]
def rieszPressurePotentialCutoffScale (n : ℕ) : ℝ := (n : ℝ) + 1

/-- The CKN cutoff radius whose inner ball has radius
`rieszPressurePotentialCutoffScale n`. -/
@[expose]
def rieszPressurePotentialCutoffRadius (n : ℕ) : ℝ :=
  20 * rieszPressurePotentialCutoffScale n / 13

/-- The spatial cutoff in the compact approximation of a potential test. -/
@[expose]
def rieszPressurePotentialCutoff (n : ℕ) : Vec3 → ℝ :=
  CKN.mollifiedBallCutoff 0 (ρ := rieszPressurePotentialCutoffRadius n) (by
    unfold rieszPressurePotentialCutoffRadius rieszPressurePotentialCutoffScale
    positivity)

/-- The compactly supported approximation of a potential test. -/
@[expose]
def rieszPressurePotentialCutoffTest (ψ : Vec3 × ℝ → ℝ) (n : ℕ) :
    Vec3 × ℝ → ℝ := fun z => rieszPressurePotentialCutoff n z.1 * ψ z

/-- The cutoff scales are uniformly bounded below by one, used by the
noncompact-potential estimates. -/
theorem rieszPressurePotentialCutoffScale_ge_one (n : ℕ) :
    1 ≤ rieszPressurePotentialCutoffScale n := by
  simp [rieszPressurePotentialCutoffScale]

/-- Every cutoff scale is positive, used by the noncompact-potential
estimates. -/
theorem rieszPressurePotentialCutoffScale_pos (n : ℕ) :
    0 < rieszPressurePotentialCutoffScale n :=
  lt_of_lt_of_le zero_lt_one (rieszPressurePotentialCutoffScale_ge_one n)

/-- Every CKN cutoff radius is positive, used by the cutoff construction. -/
theorem rieszPressurePotentialCutoffRadius_pos (n : ℕ) :
    0 < rieszPressurePotentialCutoffRadius n := by
  unfold rieszPressurePotentialCutoffRadius
  exact div_pos (mul_pos (by norm_num) (rieszPressurePotentialCutoffScale_pos n))
    (by norm_num)

private theorem rieszPressurePotentialCutoff_inner (n : ℕ) :
    13 * rieszPressurePotentialCutoffRadius n / 20 =
      rieszPressurePotentialCutoffScale n := by
  dsimp [rieszPressurePotentialCutoffRadius]
  ring

/-- The outer support radius of the cutoff is a fixed multiple of its scale,
used by the noncompact-potential estimates. -/
theorem rieszPressurePotentialCutoff_outer (n : ℕ) :
    3 * rieszPressurePotentialCutoffRadius n / 4 =
      15 * rieszPressurePotentialCutoffScale n / 13 := by
  dsimp [rieszPressurePotentialCutoffRadius]
  ring

/-- The CKN spatial cutoff equals one on its growing inner ball. -/
theorem rieszPressurePotentialCutoff_eq_one
    (n : ℕ) {x : Vec3}
    (hx : x ∈ CKN.euclideanBall 0 (rieszPressurePotentialCutoffScale n)) :
    rieszPressurePotentialCutoff n x = 1 := by
  unfold rieszPressurePotentialCutoff
  rw [← rieszPressurePotentialCutoff_inner n] at hx
  exact CKN.mollifiedBallCutoff_eq_one_on_inner 0
    (rieszPressurePotentialCutoffRadius_pos n) hx

/-- The CKN cutoff is between zero and one. -/
theorem rieszPressurePotentialCutoff_bounds (n : ℕ) (x : Vec3) :
    0 ≤ rieszPressurePotentialCutoff n x ∧ rieszPressurePotentialCutoff n x ≤ 1 := by
  constructor
  · simpa [rieszPressurePotentialCutoff] using
      CKN.mollifiedBallCutoff_nonneg 0 (rieszPressurePotentialCutoffRadius_pos n) x
  · simpa [rieszPressurePotentialCutoff] using
      CKN.mollifiedBallCutoff_le_one 0 (rieszPressurePotentialCutoffRadius_pos n) x

/-- The first coordinate derivatives of the cutoff have the scale bound needed
for the noncompact-potential passage. -/
theorem rieszPressurePotentialCutoff_gradient_bound
    (n : ℕ) (i : Fin 3) (x : Vec3) :
    |CKN.spatialDeriv (rieszPressurePotentialCutoff n) i x| ≤
      CKN.cutoffGradientConstant / rieszPressurePotentialCutoffScale n := by
  have hcoord := CKN.abs_apply_le_vecEuclideanNorm
    (CKN.classicalGradient (rieszPressurePotentialCutoff n) x) i
  have hbound := CKN.mollifiedBallCutoff_gradient_bound 0
    (rieszPressurePotentialCutoffRadius_pos n) x
  change CKN.vecEuclideanNorm (CKN.classicalGradient
    (rieszPressurePotentialCutoff n) x) ≤
      CKN.cutoffGradientConstant / rieszPressurePotentialCutoffRadius n at hbound
  have hsp : CKN.spatialDeriv (rieszPressurePotentialCutoff n) i x =
      CKN.classicalGradient (rieszPressurePotentialCutoff n) x i := rfl
  rw [hsp]
  calc
    |CKN.classicalGradient (rieszPressurePotentialCutoff n) x i| ≤
        CKN.vecEuclideanNorm (CKN.classicalGradient (rieszPressurePotentialCutoff n) x) := hcoord
    _ ≤ CKN.cutoffGradientConstant / rieszPressurePotentialCutoffRadius n := hbound
    _ = CKN.cutoffGradientConstant * (13 / 20) /
        rieszPressurePotentialCutoffScale n := by
      rw [rieszPressurePotentialCutoffRadius]
      have hscale : rieszPressurePotentialCutoffScale n ≠ 0 :=
        (rieszPressurePotentialCutoffScale_pos n).ne'
      field_simp [hscale]
    _ ≤ CKN.cutoffGradientConstant / rieszPressurePotentialCutoffScale n := by
      have hC : 0 ≤ CKN.cutoffGradientConstant := by
        have h := CKN.mollifiedBallCutoff_gradient_bound 0
          (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
        exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
      have hs := rieszPressurePotentialCutoffScale_pos n
      apply (div_le_div_iff_of_pos_right hs).2
      calc
        CKN.cutoffGradientConstant * (13 / 20) ≤
            CKN.cutoffGradientConstant * 1 := by gcongr; norm_num
        _ = CKN.cutoffGradientConstant := by ring

/-- Every coordinate second derivative of the cutoff has the inverse-square
scale bound needed by `lem:riesz-duality`. -/
theorem rieszPressurePotentialCutoff_hessian_component_bound
    (n : ℕ) (i j : Fin 3) (x : Vec3) :
    |CKN.mixedSecond (rieszPressurePotentialCutoff n) i j x| ≤
      CKN.cutoffSecondDerivativeConstant /
        rieszPressurePotentialCutoffScale n ^ 2 := by
  have hbound := CKN.mollifiedBallCutoff_second_derivative_bound 0
    (rieszPressurePotentialCutoffRadius_pos n) x
  change ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x‖ ≤
      CKN.cutoffSecondDerivativeConstant / rieszPressurePotentialCutoffRadius n ^ 2 at hbound
  have hcoord : |CKN.mixedSecond (rieszPressurePotentialCutoff n) i j x| ≤
      ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x‖ := by
    have hcomp : CKN.mixedSecond (rieszPressurePotentialCutoff n) i j x =
        (fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x
          (CKN.basisVec i)) j := by
      have hη : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoff n) :=
        CKN.mollifiedBallCutoff_smooth 0 (rieszPressurePotentialCutoffRadius_pos n)
      have hgrad : ContDiff ℝ (⊤ : ℕ∞)
          (CKN.classicalGradient (rieszPressurePotentialCutoff n)) := by
        rw [contDiff_pi]
        intro k
        change ContDiff ℝ (⊤ : ℕ∞)
          (CKN.spatialDeriv (rieszPressurePotentialCutoff n) k)
        exact CKN.contDiff_spatialDeriv_smooth hη k
      change (fderiv ℝ
        (fun y : Vec3 => CKN.classicalGradient (rieszPressurePotentialCutoff n) y j)
        x) (CKN.basisVec i) = _
      rw [fderiv_apply (hgrad.differentiable (by norm_num) x) j]
      rfl
    rw [hcomp]
    calc
      |(fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x
          (CKN.basisVec i)) j| ≤
        ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x
          (CKN.basisVec i)‖ := by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm _ j
      _ ≤ ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x‖ := by
        calc
          _ ≤ ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x‖ *
                ‖CKN.basisVec i‖ := ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x‖ := by
            rw [CKN.basisVec, Pi.norm_single]
            norm_num
  calc
    |CKN.mixedSecond (rieszPressurePotentialCutoff n) i j x| ≤
        ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x‖ := hcoord
    _ ≤ CKN.cutoffSecondDerivativeConstant /
        rieszPressurePotentialCutoffRadius n ^ 2 := hbound
    _ = CKN.cutoffSecondDerivativeConstant * (13 / 20) ^ 2 /
        rieszPressurePotentialCutoffScale n ^ 2 := by
      rw [rieszPressurePotentialCutoffRadius]
      have hscale : rieszPressurePotentialCutoffScale n ≠ 0 :=
        (rieszPressurePotentialCutoffScale_pos n).ne'
      field_simp [hscale]
    _ ≤ CKN.cutoffSecondDerivativeConstant /
        rieszPressurePotentialCutoffScale n ^ 2 := by
      have hC : 0 ≤ CKN.cutoffSecondDerivativeConstant := by
        have h := CKN.mollifiedBallCutoff_second_derivative_bound 0
          (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
        exact le_trans (norm_nonneg _) (by simpa using h)
      have hs : 0 < rieszPressurePotentialCutoffScale n ^ 2 :=
        pow_pos (rieszPressurePotentialCutoffScale_pos n) _
      apply (div_le_div_iff_of_pos_right hs).2
      calc
            CKN.cutoffSecondDerivativeConstant * (13 / 20) ^ 2 ≤
            CKN.cutoffSecondDerivativeConstant * 1 := by
              gcongr; norm_num
        _ = CKN.cutoffSecondDerivativeConstant := by ring

/-- The first and second cutoff derivatives vanish on its inner ball. -/
theorem rieszPressurePotentialCutoff_derivatives_zero_on_inner
    (n : ℕ) {x : Vec3}
    (hx : x ∈ CKN.euclideanClosedBall 0
      (rieszPressurePotentialCutoffScale n)) :
    CKN.classicalGradient (rieszPressurePotentialCutoff n) x = 0 ∧
      fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoff n)) x = 0 := by
  have hnotAnnulus : x ∉ CKN.euclideanBall 0
      (3 * rieszPressurePotentialCutoffRadius n / 4) \
        CKN.euclideanClosedBall 0
          (13 * rieszPressurePotentialCutoffRadius n / 20) := by
    intro hxAnn
    apply hxAnn.2
    rw [rieszPressurePotentialCutoff_inner n]
    exact hx
  exact CKN.mollifiedBallCutoff_derivatives_vanish_outside_annulus 0
    (rieszPressurePotentialCutoffRadius_pos n) hnotAnnulus

/-- The compact cutoff approximants are smooth whenever the potential test is
smooth. -/
theorem rieszPressurePotentialCutoffTest_contDiff
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoffTest ψ n) := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoff n) :=
    CKN.mollifiedBallCutoff_smooth 0 (rieszPressurePotentialCutoffRadius_pos n)
  have hη' : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => rieszPressurePotentialCutoff n z.1) := by
    exact hη.comp contDiff_fst
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun z : Vec3 × ℝ => rieszPressurePotentialCutoff n z.1 * ψ z)
  exact hη'.mul hψ

/-- The compact cutoff approximants have compact support when the test has
compact time support. -/
theorem rieszPressurePotentialCutoffTest_hasCompactSupport
    {ψ : Vec3 × ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hzero : ∀ t ∉ K, ∀ x, ψ (x, t) = 0) (n : ℕ) :
    HasCompactSupport (rieszPressurePotentialCutoffTest ψ n) := by
  let R := 3 * rieszPressurePotentialCutoffRadius n / 4
  let B : Set Vec3 := CKN.euclideanClosedBall 0 R
  have hRpos : 0 < R := by
    dsimp [R]
    exact div_pos (mul_pos (by norm_num) (rieszPressurePotentialCutoffRadius_pos n))
      (by norm_num)
  have hR : 0 ≤ R := hRpos.le
  have hB : IsCompact B := by
    dsimp [B, R]
    exact CKN.isCompact_euclideanClosedBall 0 hR
  let S : Set (Vec3 × ℝ) := B ×ˢ K
  have hS : IsCompact S := hB.prod hK
  refine HasCompactSupport.intro hS ?_
  intro z hz
  by_cases htime : z.2 ∈ K
  · have hspace : z.1 ∉ B := by
      intro hx
      exact hz ⟨hx, htime⟩
    have houter : z.1 ∉ CKN.euclideanBall 0 R := by
      intro hx
      apply hspace
      apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR).2
      exact ((CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos).1 hx).le
    have hnot : z.1 ∉ tsupport (rieszPressurePotentialCutoff n) := by
      intro hs
      have houter' : z.1 ∈ CKN.euclideanBall 0 R := by
        have hsub := CKN.mollifiedBallCutoff_tsupport_subset_outer 0
          (rieszPressurePotentialCutoffRadius_pos n) hs
        simpa [R] using hsub
      exact houter houter'
    have hcut : rieszPressurePotentialCutoff n z.1 = 0 :=
      image_eq_zero_of_notMem_tsupport hnot
    simp [rieszPressurePotentialCutoffTest, hcut]
  · simp [rieszPressurePotentialCutoffTest, hzero z.2 htime z.1]

end CKN.Leray

end
