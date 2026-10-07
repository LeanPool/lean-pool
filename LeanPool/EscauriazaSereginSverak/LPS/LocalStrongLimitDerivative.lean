/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitCurve
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Weak derivatives of kernel convolutions of slab fields

A space-time weak spatial derivative is, for every kernel and at every point,
an almost-everywhere-in-time identity between convolutions. These identities
are the input of the energy identities for the specified first gradient of a
strong solution (`prop:lps-local-strong`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- A weak spatial derivative of a slab field is, for every kernel and at every
point, an almost-everywhere-in-time identity between convolutions. -/
theorem lps_conv_deriv_ae {a b : ℝ} {u v : Vec3 × ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (vlSlab a b)))
    (hv : MemLp v 2 (volume.restrict (vlSlab a b))) (j : Fin 3)
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, u p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, v p * φ p)
    {κ : Vec3 → ℝ} (hκ : IsVlKernel κ) (x : Vec3) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      vlConvT (vlDeriv κ j) u x s = vlConvT κ v x s := by
  set F : ℝ → ℝ := fun s => vlConvT (vlDeriv κ j) u x s - vlConvT κ v x s with hF
  have hFint : IntegrableOn F (Ioo a b) volume :=
    (vlConvT_integrableOn hu (hκ.deriv j) x).sub (vlConvT_integrableOn hv hκ x)
  have hfull : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo a b → ∫ s, θ s • F s ∂(volume : Measure ℝ) = 0 := by
    intro θ hθ hθc hθI
    have hθt : IsIntervalTest (Ioo a b) θ := ⟨hθ, hθc, hθI⟩
    have hθcont : Continuous θ := hθ.continuous
    have hθb := hθcont.bounded_above_of_compact_support hθc
    have hθb' : ∃ C, ∀ s, |θ s| ≤ C := by
      obtain ⟨C, hC⟩ := hθb
      exact ⟨C, fun s => by simpa [Real.norm_eq_abs] using hC s⟩
    have h := hweak (vlTest κ x θ) (vlTest_mem hκ x hθt)
    have hA := vlSlab_integral_sep hu (hκ.deriv j) x hθcont hθb'
    have hB := vlSlab_integral_sep hv hκ x hθcont hθb'
    have hL : ∫ p in vlSlab a b, u p * CKN.spatialPartial (vlTest κ x θ) j p =
        -∫ s in Ioo a b, θ s * vlConvT (vlDeriv κ j) u x s := by
      rw [← hA.2, ← integral_neg]
      refine setIntegral_congr_fun (measurableSet_prod.2 (Or.inl ⟨MeasurableSet.univ,
        measurableSet_Ioo⟩)) fun p _ => ?_
      rw [vlTest_spatialPartial hκ x θ j p]
      ring
    have hR : ∫ p in vlSlab a b, v p * vlTest κ x θ p =
        ∫ s in Ioo a b, θ s * vlConvT κ v x s := by
      rw [← hB.2]
      rfl
    rw [hL, hR] at h
    have hint1 : IntegrableOn (fun s => θ s * vlConvT (vlDeriv κ j) u x s) (Ioo a b) volume := by
      obtain ⟨C, hC⟩ := hθb'
      exact (vlConvT_integrableOn hu (hκ.deriv j) x).bdd_mul (c := C)
        hθcont.aestronglyMeasurable
        (Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hC s)
    have hint2 : IntegrableOn (fun s => θ s * vlConvT κ v x s) (Ioo a b) volume := by
      obtain ⟨C, hC⟩ := hθb'
      exact (vlConvT_integrableOn hv hκ x).bdd_mul (c := C) hθcont.aestronglyMeasurable
        (Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hC s)
    have hzero : ∫ s in Ioo a b, θ s • F s = 0 := by
      have : ∫ s in Ioo a b, θ s • F s =
          (∫ s in Ioo a b, θ s * vlConvT (vlDeriv κ j) u x s) -
            ∫ s in Ioo a b, θ s * vlConvT κ v x s := by
        rw [← integral_sub hint1 hint2]
        refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
        simp only [hF, smul_eq_mul]
        ring
      rw [this]
      linarith only [h]
    have hcompl : ∀ s ∉ Ioo a b, θ s • F s = 0 := by
      intro s hs
      have : θ s = 0 := by
        by_contra hne
        exact hs (hθI ((subset_tsupport θ) (Function.mem_support.mpr hne)))
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
    exact hzero
  have hzero := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hFint.locallyIntegrableOn hfull
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hzero] with s hs hsI
  have := hs hsI
  simp only [hF] at this
  linarith only [this]

/-- From an identity for every point and almost every time to an identity for
almost every time and almost every point. -/
theorem lps_ae_slice_of_ae_time {a b : ℝ} {F G : Vec3 × ℝ → ℝ}
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (h : ∀ x : Vec3, ∀ᵐ s ∂(volume.restrict (Ioo a b)), F (x, s) = G (x, s)) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3),
      F (x, s) = G (x, s) := by
  have hmeas : MeasurableSet {p : Vec3 × ℝ | F p = G p} :=
    measurableSet_eq_fun hF.measurable hG.measurable
  exact (Measure.ae_ae_comm hmeas).1 (Eventually.of_forall h)

end ESS.LPS

end
