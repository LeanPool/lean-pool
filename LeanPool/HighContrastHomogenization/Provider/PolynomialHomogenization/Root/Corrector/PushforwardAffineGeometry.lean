/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.AffineSandwichDepth
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardAffineGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Geometry and locality for the affine pushforward

Two facts the pushforward construction needs and the tree does not have.

* the **reverse sandwich**: every centered exhaustion cube is contained in the
  matrix image of a fixed coarser one, so the affine pullback of a carrier can
  be read on the exhaustion in either direction;
* **locality of the global weak gradient**: a weak-gradient pair on every
  centered exhaustion cube is a weak-gradient pair on all of `Vec d`.  The
  available affine-pullback transports of `HasWeakGradientOn` demand `L²` or
  integrability on the *source domain*, which no corrector satisfies globally;
  locality is what lets them be applied cube by cube and assembled.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## Test functions live in a centered cube -/

/-- A compactly supported test function is supported in some centered
exhaustion cube. -/
theorem exists_tsupport_subset_localGradientCube {phi : Vec d → ℝ}
    (hphi : HasCompactSupport phi) :
    ∃ n : ℕ, tsupport phi ⊆ localGradientCube d n := by
  obtain ⟨R, hR⟩ :=
    (hphi.isCompact.isBounded).subset_closedBall (0 : Vec d) |>.imp
      fun _R h ↦ h
  obtain ⟨n, hn⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).eventually_gt_atTop
      (2 * R)).exists
  refine ⟨n, fun x hx ↦ ?_⟩
  have hxball : x ∈ Metric.closedBall (0 : Vec d) R := hR hx
  have hxnorm : ‖x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hxball
  rw [localGradientCube, mem_openCubeSet_originCube_iff]
  intro i
  have hcoord : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  rw [zpow_natCast]
  constructor <;>
    linarith only [neg_abs_le (x i), le_abs_self (x i), hcoord, hxnorm, hn]

/-! ## Locality of the global weak gradient -/

/-- Two set integrals of a function vanishing off both sets agree. -/
theorem setIntegral_eq_of_vanishing {f : Vec d → ℝ} {U V : Set (Vec d)}
    (hU : ∀ x ∉ U, f x = 0) (hV : ∀ x ∉ V, f x = 0) :
    ∫ x in U, f x ∂volume = ∫ x in V, f x ∂volume :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hU).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero hV).symm

/-- The weak-gradient identity on a centered cube containing the support of the
test is the identity on all of `Vec d`. -/
theorem hasWeakGradientOn_univ_of_localGradientCube {u : Vec d → ℝ}
    {Du : Vec d → Vec d}
    (h : ∀ n : ℕ, HasWeakGradientOn (localGradientCube d n) u Du) :
    HasWeakGradientOn Set.univ u Du := by
  intro i phi hsmooth hcompact _hsub
  obtain ⟨n, hn⟩ := exists_tsupport_subset_localGradientCube hcompact
  have hleft : ∀ x ∉ localGradientCube d n,
      u x * (fderiv ℝ phi x) (basisVec i) = 0 := by
    intro x hx
    have hxsupp : x ∉ tsupport phi := fun hmem ↦ hx (hn hmem)
    have hzero : fderiv ℝ phi x = 0 := by
      by_contra hne
      exact hxsupp (support_fderiv_subset ℝ (f := phi)
        (by simpa only [Function.mem_support] using hne))
    rw [hzero]
    simp
  have hright : ∀ x ∉ localGradientCube d n, Du x i * phi x = 0 := by
    intro x hx
    have hxsupp : x ∉ tsupport phi := fun hmem ↦ hx (hn hmem)
    have hzero : phi x = 0 := image_eq_zero_of_notMem_tsupport hxsupp
    rw [hzero, mul_zero]
  have hcube := h n i phi hsmooth hcompact hn
  rw [setIntegral_eq_of_vanishing (fun x hx ↦ absurd (Set.mem_univ x) hx) hleft,
    setIntegral_eq_of_vanishing (fun x hx ↦ absurd (Set.mem_univ x) hx) hright]
  exact hcube

/-- A weak-gradient pair on a set restricts to every subset, because the test
is supported in the subset. -/
theorem hasWeakGradientOn_subset {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {U V : Set (Vec d)} (hVU : V ⊆ U) (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du := by
  intro i phi hsmooth hcompact hsub
  have hleft : ∀ x ∉ V, u x * (fderiv ℝ phi x) (basisVec i) = 0 := by
    intro x hx
    have hxsupp : x ∉ tsupport phi := fun hmem ↦ hx (hsub hmem)
    have hzero : fderiv ℝ phi x = 0 := by
      by_contra hne
      exact hxsupp (support_fderiv_subset ℝ (f := phi)
        (by simpa only [Function.mem_support] using hne))
    rw [hzero]
    simp
  have hright : ∀ x ∉ V, Du x i * phi x = 0 := by
    intro x hx
    have hxsupp : x ∉ tsupport phi := fun hmem ↦ hx (hsub hmem)
    have hzero : phi x = 0 := image_eq_zero_of_notMem_tsupport hxsupp
    rw [hzero, mul_zero]
  have hleftU : ∀ x ∉ U, u x * (fderiv ℝ phi x) (basisVec i) = 0 :=
    fun x hx ↦ hleft x fun hmem ↦ hx (hVU hmem)
  have hrightU : ∀ x ∉ U, Du x i * phi x = 0 :=
    fun x hx ↦ hright x fun hmem ↦ hx (hVU hmem)
  have hbig := h i phi hsmooth hcompact (hsub.trans hVU)
  rw [setIntegral_eq_of_vanishing hleft hleftU,
    setIntegral_eq_of_vanishing hright hrightU]
  exact hbig

/-! ## The reverse sandwich -/

/-- Every centered exhaustion cube sits inside the matrix image of a fixed
coarser one.  This is the direction the pushforward needs; the
inclusion into the affine pullback gives the other one. -/
theorem exists_localGradientCube_subset_matImage (L : Mat d) (hL : IsUnit L.det) :
    ∃ k : ℕ, ∀ n : ℕ,
      localGradientCube d n ⊆ matImage L (localGradientCube d (n + k)) := by
  obtain ⟨k, hk⟩ := exists_matImage_localGradientCube_subset L⁻¹
  refine ⟨k, fun n x hx ↦ ?_⟩
  refine ⟨matVecMul L⁻¹ x, hk n ⟨x, hx, rfl⟩, ?_⟩
  rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL]
  exact matVecMul_one x

end

end Root
end HighContrast
end HCPolySupport
