/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.SpatialSecondDerivatives

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CanonicalEnvelopeL2

/-! Spatial diffusion calculus below the public AMNR facade. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem amnr_energy_gradient_smooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad f) := by
  have hjoint : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Vec 2 × Vec 2 => fderiv ℝ f p.1 p.2) :=
    hf.contDiff_fderiv_apply (by simp)
  apply contDiff_pi.2
  intro i
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (x, basisVec i)) := by
    fun_prop
  have hcomp := hjoint.comp hmap
  simpa only [Function.comp_def, Prod.fst, Prod.snd, AVenhance.spaceGrad] using hcomp

theorem amnr_energy_coordinate_derivatives_commute {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x j =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y j) x i := by
  exact AVenhance.Infra.SpatialSecondDerivatives.coordinate_derivatives_commute hf i j x

/-- The gradient of the Laplacian is the componentwise Laplacian of the
gradient. This justifies moving current diffusion derivatives to the preceding
increment in the oscillatory material pairing. -/
theorem amnr_energy_gradient_laplacian_commute {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (i : Fin 2) :
    spaceGrad (spaceLap f) x i = spaceLap (fun y => spaceGrad f y i) x := by
  have hg (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => spaceGrad f y j) :=
    contDiff_pi.mp (amnr_energy_gradient_smooth hf) j
  have hgg (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => spaceGrad (fun z => spaceGrad f z j) y j) :=
    contDiff_pi.mp (amnr_energy_gradient_smooth (hg j)) j
  change fderiv ℝ (fun y => ∑ j : Fin 2,
    spaceGrad (fun z => spaceGrad f z j) y j) x (basisVec i) = _
  rw [fderiv_fun_sum (fun j _ => (hgg j).differentiable (by simp) |>.differentiableAt)]
  simp only [sum_apply]
  unfold spaceLap
  apply Finset.sum_congr rfl
  intro j _
  change spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z j) y j) x i = _
  rw [amnr_energy_coordinate_derivatives_commute (hg j) j i x]
  have hswap : (fun y => spaceGrad (fun z => spaceGrad f z j) y i) =
      (fun y => spaceGrad (fun z => spaceGrad f z i) y j) := by
    funext y
    exact amnr_energy_coordinate_derivatives_commute hf j i y
  rw [hswap]

theorem amnr_energy_laplacian_smooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (spaceLap f) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_pi.mp (amnr_energy_gradient_smooth
    (contDiff_pi.mp (amnr_energy_gradient_smooth hf) j)) j

end AVenhance.Infra.Section4
