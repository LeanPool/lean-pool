/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszProductTest
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingKernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionCore

/-!
# Blowup Riesz Slice Core

Pressure reconstruction and convergence bounds for the rescaled sequence.
-/

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
noncomputable section
namespace ESS

/-- Testing the spatial Laplacian on a countable family of mollifier bumps
determines distributional harmonicity on the entire open set. -/
theorem blowup_harmonic_of_mollifier_bump_pairings
    {U : Set Vec3} (hU : IsOpen U) {Q : Set Vec3} (hQ : Dense Q)
    {p : Vec3 → ℝ} (hp : LocallyIntegrableOn p U volume)
    (hzero : ∀ y ∈ Q, ∀ n : ℕ, Metric.closedBall y (CKN.sliceRadius n) ⊆ U →
      ∫ x in U, p x * CKN.spatialLaplacian
        (fun z : Vec3 => CKN.mollifier (d := 3) (CKN.sliceRadius n)
          (CKN.sliceRadius_pos n) (z - y)) x = 0) :
    CKN.Foundation.Heat.WeaklyHarmonicOn U p := by
  intro ψ hψ hψc hψU
  have hmain := CKN.slice_pairing_zero_of_mollifier_family
    (Ω := U) (Q := Q) (g := fun x (i : Fin 3) => p x)
    (κ := fun n i => CKN.mixedSecond
      (CKN.mollifier (d := 3) (CKN.sliceRadius n) (CKN.sliceRadius_pos n)) i i)
    hU hQ (fun _ => hp)
    (fun n i => CKN.continuous_mixedSecond_mollifier (CKN.sliceRadius_pos n) i i)
    (fun n i z hz => CKN.mixedSecond_mollifier_eq_zero (CKN.sliceRadius_pos n)
      i i hz)
    hψ.continuous hψc hψU
    (T := fun i => CKN.mixedSecond ψ i i)
    (fun i => (CKN.contDiff_mixedSecond_smooth hψ i i).continuous)
    (fun i x hx => by
      have hsub : tsupport (CKN.mixedSecond ψ i i) ⊆ tsupport ψ := by
        exact (tsupport_fderiv_apply_subset ℝ (CKN.basisVec i)).trans
          (tsupport_fderiv_apply_subset ℝ (CKN.basisVec i))
      exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)))
    (fun n i x => CKN.integral_mul_mixedSecond_mollifier_sub hψ i i
      (CKN.sliceRadius_pos n) x)
    (fun y hy n hn => by
      rw [← hzero y hy n hn]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [CKN.spatialLaplacian, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (congrArg (fun v : ℝ => p x * v)
        (CKN.mixedSecond_sub_const
          (CKN.mollifier_contDiff (d := 3) (n := ⊤) (CKN.sliceRadius_pos n))
          y x i i)).symm)
  calc
    ∫ x in U, p x * CKN.spatialLaplacian ψ x =
      ∫ x in U, ∑ i : Fin 3, p x * CKN.mixedSecond ψ i i x := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [CKN.spatialLaplacian, Finset.mul_sum]
        rfl
    _ = 0 := hmain

end ESS
