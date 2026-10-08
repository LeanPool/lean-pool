/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityWeakLimit
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.SmoothIBP
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport

/-!
# Weak spatial derivatives on individual time slices

Spatial weak-derivative identities pass to limits of smooth approximations on a fixed ball.
-/

public section

open Filter Function MeasureTheory Set Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- If smooth functions and their spatial derivatives converge in `L²` on a ball,
the derivative limit is the weak spatial derivative of the function limit. -/
theorem vorticity_sliceWeakPartial_of_tendsto
    {B : Set Vec3} {j : Fin 3} (hBmeas : MeasurableSet B)
    {f g : ℕ → Vec3 → ℝ} {F G : Vec3 → ℝ}
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hg : ∀ n, MemLp (f n) 2 (volume.restrict B))
    (hDg : ∀ n, MemLp (g n) 2 (volume.restrict B))
    (hF : MemLp F 2 (volume.restrict B))
    (hG : MemLp G 2 (volume.restrict B))
    (hFconv : Tendsto (fun n => eLpNorm (f n - F) 2 (volume.restrict B)) atTop (𝓝 0))
    (hGconv : Tendsto (fun n => eLpNorm (g n - G) 2 (volume.restrict B)) atTop (𝓝 0))
    (hderiv : ∀ n x, x ∈ B → spatialDeriv (f n) j x = g n x) :
    HasWeakPartialDerivOn B j F G := by
  intro ψ hψ hψc hψB
  have hψLp : MemLp ψ 2 (volume.restrict B) :=
    (hψ.continuous.memLp_of_hasCompactSupport hψc).restrict B
  have hdψLp : MemLp (fun x : Vec3 => spatialDeriv ψ j x) 2 (volume.restrict B) :=
    ((contDiff_spatialDeriv_smooth hψ j).continuous.memLp_of_hasCompactSupport
      (CKN.hasCompactSupport_spatialDeriv hψc j)).restrict B
  have hleft := vorticity_tendsto_integral_mul hg hF hdψLp hFconv
  have hright := vorticity_tendsto_integral_mul hDg hG hψLp hGconv
  have hseq (n : ℕ) :
      (∫ x in B, f n x * spatialDeriv ψ j x) =
        -∫ x in B, g n x * ψ x := by
    have hleftGlobal :
        ∫ x in B, f n x * spatialDeriv ψ j x ∂volume =
          ∫ x, f n x * spatialDeriv ψ j x ∂volume := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hψ0 : spatialDeriv ψ j x = 0 := by
        have hnot : x ∉ tsupport (spatialDeriv ψ j) := by
          intro hderiv
          exact hx (hψB (CKN.tsupport_spatialDeriv_subset j hderiv))
        exact image_eq_zero_of_notMem_tsupport hnot
      rw [hψ0, mul_zero]
    have hderivGlobal :
        ∫ x in B, spatialDeriv (f n) j x * ψ x ∂volume =
          ∫ x, spatialDeriv (f n) j x * ψ x ∂volume := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hψ0 : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψB h))
      rw [hψ0, mul_zero]
    calc
      ∫ x in B, f n x * spatialDeriv ψ j x ∂volume =
          ∫ x, f n x * spatialDeriv ψ j x ∂volume := hleftGlobal
      _ = -∫ x, spatialDeriv (f n) j x * ψ x ∂volume :=
        CKN.integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
          (hf n) hψ hψc j
      _ = -∫ x in B, spatialDeriv (f n) j x * ψ x ∂volume := by rw [← hderivGlobal]
      _ = -∫ x in B, g n x * ψ x ∂volume := by
        congr 1
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hBmeas] with x hx
        rw [hderiv n x hx]
  have hright' := hright.neg.congr fun n => (hseq n).symm
  exact tendsto_nhds_unique hleft hright'

end ESS

end
