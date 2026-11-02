/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicityTransferTests

/-!
# BoundaryWeakTests

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Smooth tests for the divergence-form equation with a scalar source

The zeroth-order weak equation is stated against the bundled `H¹₀` carrier.
Two conversions are used repeatedly by the reflection argument: smooth
compactly supported tests already determine the equation, and a smooth
competitor which happens to lie in `H¹₀` may be tested with its classical
gradient.  Both are the coefficient-carrying analogues of the corresponding
harmonicity conversions.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport Filter
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-- The tested pairing splits into its `d` coordinate products. -/
theorem integral_vecDot_split_coords {W : Set (Vec d)} (F G : Vec d → Vec d)
    (hF : ∀ j, MemLp (fun y => F y j) 2 (volume.restrict W))
    (hG : ∀ j, MemLp (fun y => G y j) 2 (volume.restrict W)) :
    ∫ y in W, vecDot (F y) (G y) ∂volume =
      ∑ j : Fin d, ∫ y in W, G y j * F y j ∂volume := by
  have hint : ∀ j : Fin d,
      Integrable (fun y => G y j * F y j) (volume.restrict W) := fun j =>
    (hG j).integrable_mul (hF j)
  rw [← integral_finsetSum _ fun j _ => hint j]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  change vecDot (F y) (G y) = ∑ j : Fin d, G y j * F y j
  rw [vecDot]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- A smooth compactly supported function is square integrable on every
window. -/
theorem memLp_two_of_contDiff_restrict {W : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    MemLp f 2 (volume.restrict W) :=
  (hf.continuous.memLp_of_hasCompactSupport hfc).restrict W

/-- **Smooth tests suffice for the divergence-form equation with a bounded
scalar source.**  The proof tests against the `H¹₀` package's own smooth
approximants and passes to the limit coordinatewise, using the `L²`
convergence of both values and gradients. -/
theorem isMatrixDivFormWeakSolutionZerothOrderOn_of_contDiff_tests
    {W : Set (Vec d)} {a : CoeffField d} {u : H1Function W} {g : Vec d → ℝ}
    (hflux : ∀ j, MemLp (fun y => matVecMul (a y) (u.grad y) j) 2 (volume.restrict W))
    (hg : MemLp g 2 (volume.restrict W))
    (htest : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W →
      ∫ y in W, vecDot (matVecMul (a y) (u.grad y)) (euclideanGradient φ y) ∂volume =
        ∫ y in W, g y * φ y ∂volume) :
    IsMatrixDivFormWeakSolutionZerothOrderOn a W u g 0 := by
  intro phi
  set F : Vec d → Vec d := fun y => matVecMul (a y) (u.grad y) with hFdef
  have hgradL2 : ∀ (n : ℕ) (j : Fin d),
      MemLp (fun y => euclideanGradient (phi.approx n) y j) 2 (volume.restrict W) :=
    fun n j => memLp_two_fderiv_apply_restrict (phi.approx_smooth n)
      (phi.approx_hasCompactSupport n) j
  have hvalL2 : ∀ n : ℕ, MemLp (phi.approx n) 2 (volume.restrict W) := fun n =>
    memLp_two_of_contDiff_restrict (phi.approx_smooth n) (phi.approx_hasCompactSupport n)
  have hstep : ∀ n : ℕ,
      (∑ j : Fin d, ∫ y in W, euclideanGradient (phi.approx n) y j * F y j ∂volume) =
        ∫ y in W, phi.approx n y * g y ∂volume := by
    intro n
    rw [← integral_vecDot_split_coords F (euclideanGradient (phi.approx n)) hflux
      (hgradL2 n)]
    rw [htest (phi.approx n) (phi.approx_smooth n) (phi.approx_hasCompactSupport n)
      (phi.approx_support_subset n)]
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  have hgradConv : ∀ j : Fin d, Tendsto
      (fun n => ∫ y in W, euclideanGradient (phi.approx n) y j * F y j ∂volume)
      atTop (nhds (∫ y in W, phi.toH1Function.grad y j * F y j ∂volume)) := fun j =>
    tendsto_setIntegral_mul_of_tendsto_eLpNormTwo (hflux j) (fun n => hgradL2 n j)
      (phi.toH1Function.gradMemL2 j) (phi.tendsto_approx_grad j)
  have hsumConv : Tendsto
      (fun n => ∑ j : Fin d,
        ∫ y in W, euclideanGradient (phi.approx n) y j * F y j ∂volume) atTop
      (nhds (∑ j : Fin d, ∫ y in W, phi.toH1Function.grad y j * F y j ∂volume)) :=
    tendsto_finsetSum _ fun j _ => hgradConv j
  have hvalConv : Tendsto (fun n => ∫ y in W, phi.approx n y * g y ∂volume) atTop
      (nhds (∫ y in W, phi.toH1Function.toFun y * g y ∂volume)) :=
    tendsto_setIntegral_mul_of_tendsto_eLpNormTwo hg hvalL2 phi.toH1Function.memL2
      phi.tendsto_approx
  have hlimit : (∑ j : Fin d, ∫ y in W, phi.toH1Function.grad y j * F y j ∂volume) =
      ∫ y in W, phi.toH1Function.toFun y * g y ∂volume :=
    tendsto_nhds_unique (hsumConv.congr fun n => hstep n) hvalConv
  have hleft : ∫ y in W, vecDot (F y) (phi.toH1Function.grad y) ∂volume =
      ∫ y in W, phi.toH1Function.toFun y * g y ∂volume := by
    rw [integral_vecDot_split_coords F phi.toH1Function.grad hflux
      phi.toH1Function.gradMemL2]
    exact hlimit
  have hright : ∫ y in W, g y * phi.toH1Function.toFun y ∂volume =
      ∫ y in W, phi.toH1Function.toFun y * g y ∂volume :=
    integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  simp only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero]
  rw [hleft, hright]

/-- **A smooth `H¹₀` competitor may be tested with its classical gradient.**
The `H10Function` witness carries some weak gradient of the competitor; on the
open window it agrees almost everywhere with the classical one. -/
theorem integral_pairing_eq_of_memH10
    {W : Set (Vec d)} (hWopen : IsOpen W) [IsFiniteMeasure (volume.restrict W)]
    {a : CoeffField d} {u : H1Function W} {g : Vec d → ℝ}
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a W u g 0)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hmem : MemH10 W ψ) :
    ∫ y in W, vecDot (matVecMul (a y) (u.grad y)) (euclideanGradient ψ y) ∂volume =
      ∫ y in W, g y * ψ y ∂volume := by
  obtain ⟨w, hw⟩ := hmem
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hcont : ∀ j : Fin d, Continuous fun y => euclideanGradient ψ y j := fun j =>
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hae : ∀ j : Fin d, (fun y => w.toH1Function.grad y j)
      =ᵐ[volume.restrict W] fun y => euclideanGradient ψ y j := by
    intro j
    refine HasWeakPartialDerivOn.ae_eq (u := ψ) (i := j) hWopen ?_ ?_ ?_ ?_
    · have hI : IntegrableOn (fun y => w.toH1Function.grad y j) W volume :=
        (w.toH1Function.gradMemL2 j).integrable (by norm_num)
      exact hI.locallyIntegrableOn
    · exact (hcont j).locallyIntegrable.locallyIntegrableOn W
    · rw [← hw]
      exact w.toH1Function.hasWeakGradient j
    · exact HasWeakPartialDerivOn.of_contDiff hψ1
  have haeAll : ∀ᵐ y ∂(volume.restrict W),
      ∀ j : Fin d, w.toH1Function.grad y j = euclideanGradient ψ y j :=
    ae_all_iff.2 hae
  have hEq : ∫ y in W, vecDot (matVecMul (a y) (u.grad y))
        (euclideanGradient ψ y) ∂volume =
      ∫ y in W, vecDot (matVecMul (a y) (u.grad y))
        (w.toH1Function.grad y) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [haeAll] with y hy
    have hvec : euclideanGradient ψ y = w.toH1Function.grad y := by
      funext j
      exact (hy j).symm
    rw [hvec]
  have hmain := hu w
  simp only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero] at hmain
  rw [hEq, hmain, hw]

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
