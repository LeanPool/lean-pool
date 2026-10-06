/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyKernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial

/-!
# Separated space-time tests

The test `(y, s) ↦ k(x - y) θ(s)`, built from a smooth compact spatial kernel
`k` and a smooth compact time test `θ`, is an admissible space-time test on
`ℝ³ × (a, τ)`. Its time derivative, spatial derivatives and spatial second
derivatives are again separated. Testing the weak equation with it gives the
time derivative of the spatial convolution in `lem:localized-vorticity-energy`
of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory Set

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

/-- The separated test `(y, s) ↦ k(x - y) θ(s)`. -/
@[expose]
def vlTest (k : Vec3 → ℝ) (x : Vec3) (θ : ℝ → ℝ) : Vec3 × ℝ → ℝ :=
  fun p => k (x - p.1) * θ p.2

theorem vlTest_contDiff {k : Vec3 → ℝ} (hk : IsVlKernel k) (x : Vec3) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) : ContDiff ℝ (⊤ : ℕ∞) (vlTest k x θ) :=
  (hk.1.comp (contDiff_const.sub contDiff_fst)).mul (hθ.comp contDiff_snd)

theorem vlTest_mem {k : Vec3 → ℝ} (hk : IsVlKernel k) (x : Vec3) {a τ : ℝ}
    {θ : ℝ → ℝ} (hθ : IsIntervalTest (Ioo a τ) θ) :
    vlTest k x θ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ) := by
  refine ⟨vlTest_contDiff hk x hθ.1, ?_, ?_⟩
  · have hK : IsCompact (((fun y : Vec3 => x - y) '' tsupport k) ×ˢ tsupport θ) :=
      ((hk.2.isCompact.image (continuous_const.sub continuous_id)).prod hθ.2.1.isCompact)
    refine HasCompactSupport.intro hK ?_
    intro p hp
    by_cases hkx : x - p.1 ∈ tsupport k
    · have hθp : p.2 ∉ tsupport θ := by
        intro hθp
        apply hp
        refine ⟨⟨x - p.1, hkx, ?_⟩, hθp⟩
        simp
      simp [vlTest, image_eq_zero_of_notMem_tsupport hθp]
    · simp [vlTest, image_eq_zero_of_notMem_tsupport hkx]
  · have hsupp : Function.support (vlTest k x θ) ⊆ (univ : Set Vec3) ×ˢ tsupport θ := by
      intro p hp
      refine ⟨mem_univ _, ?_⟩
      by_contra hθp
      apply hp
      simp [vlTest, image_eq_zero_of_notMem_tsupport hθp]
    have hclosed : IsClosed ((univ : Set Vec3) ×ˢ tsupport θ) :=
      isClosed_univ.prod (isClosed_tsupport θ)
    exact (closure_minimal hsupp hclosed).trans (prod_mono subset_rfl hθ.2.2)

theorem vlTest_timePartial {k : Vec3 → ℝ} (x : Vec3) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (p : Vec3 × ℝ) :
    CKN.timePartial (vlTest k x θ) p = k (x - p.1) * deriv θ p.2 := by
  unfold CKN.timePartial
  rw [fderiv_apply_one_eq_deriv]
  change deriv (fun s : ℝ => k (x - p.1) * θ s) p.2 = _
  rw [deriv_const_mul _ ((hθ.differentiable (by simp)).differentiableAt)]

theorem vlTest_spatialPartial {k : Vec3 → ℝ} (hk : IsVlKernel k) (x : Vec3)
    (θ : ℝ → ℝ) (j : Fin 3) (p : Vec3 × ℝ) :
    CKN.spatialPartial (vlTest k x θ) j p = -(vlDeriv k j (x - p.1) * θ p.2) := by
  unfold CKN.spatialPartial
  have hkd : HasFDerivAt k (fderiv ℝ k (x - p.1)) (x - p.1) :=
    ((hk.1.differentiable (by simp)) (x - p.1)).hasFDerivAt
  have hin : HasFDerivAt (fun y : Vec3 => x - y) (-ContinuousLinearMap.id ℝ Vec3) p.1 :=
    (hasFDerivAt_id (𝕜 := ℝ) p.1).const_sub x
  have hcomp := (hkd.comp p.1 hin).mul_const (θ p.2)
  have hfd := hcomp.fderiv
  simp only [Function.comp_def] at hfd
  change fderiv ℝ (fun y : Vec3 => k (x - y) * θ p.2) p.1 (CKN.basisVec j) = _
  rw [hfd]
  simp [vlDeriv]
  ring

theorem vlTest_spatialSecondPartial {k : Vec3 → ℝ} (hk : IsVlKernel k) (x : Vec3)
    (θ : ℝ → ℝ) (j : Fin 3) (p : Vec3 × ℝ) :
    CKN.spatialSecondPartial (vlTest k x θ) j j p =
      vlDeriv (vlDeriv k j) j (x - p.1) * θ p.2 := by
  unfold CKN.spatialSecondPartial
  have hinner : (fun w : ParabolicPoint => CKN.spatialPartial (vlTest k x θ) j w) =
      fun w : ParabolicPoint => -(vlTest (vlDeriv k j) x θ w) := by
    funext w
    rw [vlTest_spatialPartial hk x θ j w]
    rfl
  rw [hinner]
  have hneg : CKN.spatialPartial (fun w : ParabolicPoint => -(vlTest (vlDeriv k j) x θ w)) j p =
      -CKN.spatialPartial (vlTest (vlDeriv k j) x θ) j p := by
    unfold CKN.spatialPartial
    change fderiv ℝ (fun y : Vec3 => -(vlTest (vlDeriv k j) x θ (y, p.2))) p.1
      (CKN.basisVec j) = _
    rw [fderiv_fun_neg]
    rfl
  rw [hneg, vlTest_spatialPartial (hk.deriv j) x θ j p]
  ring

end CKN

end
