/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUZeroExtendIntegral
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevSupport

/-!
# Global weak identities restricted to the half-space cylinder

Product-coordinate integration by parts for fields supported in a target
cylinder gives the corresponding spatial and time weak identities there.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A global product-coordinate spatial identity restricts to any cylinder
containing the supports of its two fields. -/
theorem bu_spatial_weak_identity_of_global
    {Ω : Set Vec3} {I : Set ℝ} {K : Set ParabolicPoint}
    (hKsub : K ⊆ spaceTimeSet Ω I)
    (f g : ParabolicPoint → ℝ)
    (hfzero : ∀ z ∉ K, f z = 0)
    (hgzero : ∀ z ∉ K, g z = 0)
    (j : Fin 3)
    (hglobal : ∀ ψ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ q, f (parabolicHomeomorph.symm q) *
        (fderiv ℝ ψ q) (basisVec j, 0)
          ∂(volume : Measure (Vec3 × ℝ))) =
      -∫ q, g (parabolicHomeomorph.symm q) * ψ q
          ∂(volume : Measure (Vec3 × ℝ)))
    (φ : ParabolicPoint → ℝ)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    (∫ z in spaceTimeSet Ω I, f z * spatialPartial φ j z) =
      -∫ z in spaceTimeSet Ω I, g z * φ z := by
  let ψ : Vec3 × ℝ → ℝ := fun q => φ q
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.1
  have hψcompact : HasCompactSupport ψ := hφ.2.1
  have hfactor (q : Vec3 × ℝ) :
      spatialPartial φ j (parabolicHomeomorph.symm q) =
        (fderiv ℝ ψ q) (basisVec j, 0) := by
    simpa [ψ] using spatialPartial_eq_joint_fderiv hψsmooth q j
  have hleftZero (z : ParabolicPoint) (hz : z ∉ K) :
      f z * spatialPartial φ j z = 0 := by rw [hfzero z hz, zero_mul]
  have hrightZero (z : ParabolicPoint) (hz : z ∉ K) :
      g z * φ z = 0 := by rw [hgzero z hz, zero_mul]
  have hleft := bu_target_setIntegral_eq_product_integral hKsub
    (fun z => f z * spatialPartial φ j z) hleftZero
  have hright := bu_target_setIntegral_eq_product_integral hKsub
    (fun z => g z * φ z) hrightZero
  calc
    (∫ z in spaceTimeSet Ω I, f z * spatialPartial φ j z) =
        ∫ q, f (parabolicHomeomorph.symm q) *
          (fderiv ℝ ψ q) (basisVec j, 0)
            ∂(volume : Measure (Vec3 × ℝ)) := by
      rw [hleft]
      apply integral_congr_ae
      filter_upwards [] with q
      rw [hfactor]
    _ = -∫ q, g (parabolicHomeomorph.symm q) * ψ q
          ∂(volume : Measure (Vec3 × ℝ)) := hglobal ψ hψsmooth hψcompact
    _ = -∫ z in spaceTimeSet Ω I, g z * φ z := by
      rw [hright]
      congr 2

/-- A global product-coordinate time identity restricts to any cylinder
containing the supports of its two fields. -/
theorem bu_time_weak_identity_of_global
    {Ω : Set Vec3} {I : Set ℝ} {K : Set ParabolicPoint}
    (hKsub : K ⊆ spaceTimeSet Ω I)
    (f g : ParabolicPoint → ℝ)
    (hfzero : ∀ z ∉ K, f z = 0)
    (hgzero : ∀ z ∉ K, g z = 0)
    (hglobal : ∀ ψ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ q, f (parabolicHomeomorph.symm q) *
        (fderiv ℝ ψ q) (0, 1)
          ∂(volume : Measure (Vec3 × ℝ))) =
      -∫ q, g (parabolicHomeomorph.symm q) * ψ q
          ∂(volume : Measure (Vec3 × ℝ)))
    (φ : ParabolicPoint → ℝ)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    (∫ z in spaceTimeSet Ω I, f z * timePartial φ z) =
      -∫ z in spaceTimeSet Ω I, g z * φ z := by
  let ψ : Vec3 × ℝ → ℝ := fun q => φ q
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.1
  have hψcompact : HasCompactSupport ψ := hφ.2.1
  have hfactor (q : Vec3 × ℝ) :
      timePartial φ (parabolicHomeomorph.symm q) =
        (fderiv ℝ ψ q) (0, 1) := by
    simpa [ψ] using timePartial_eq_joint_fderiv hψsmooth q
  have hleftZero (z : ParabolicPoint) (hz : z ∉ K) :
      f z * timePartial φ z = 0 := by rw [hfzero z hz, zero_mul]
  have hrightZero (z : ParabolicPoint) (hz : z ∉ K) :
      g z * φ z = 0 := by rw [hgzero z hz, zero_mul]
  have hleft := bu_target_setIntegral_eq_product_integral hKsub
    (fun z => f z * timePartial φ z) hleftZero
  have hright := bu_target_setIntegral_eq_product_integral hKsub
    (fun z => g z * φ z) hrightZero
  calc
    (∫ z in spaceTimeSet Ω I, f z * timePartial φ z) =
        ∫ q, f (parabolicHomeomorph.symm q) *
          (fderiv ℝ ψ q) (0, 1)
            ∂(volume : Measure (Vec3 × ℝ)) := by
      rw [hleft]
      apply integral_congr_ae
      filter_upwards [] with q
      rw [hfactor]
    _ = -∫ q, g (parabolicHomeomorph.symm q) * ψ q
          ∂(volume : Measure (Vec3 × ℝ)) := hglobal ψ hψsmooth hψcompact
    _ = -∫ z in spaceTimeSet Ω I, g z * φ z := by
      rw [hright]
      congr 2

end ESS
