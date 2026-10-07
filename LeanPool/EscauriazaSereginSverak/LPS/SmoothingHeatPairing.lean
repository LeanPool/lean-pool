/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Whole-space heat pairing for high-order smoothing

For a smooth scalar derivative of the regularized velocity, integration
by parts converts the Laplacian pairing into its coordinate-gradient
energy. This is the dissipative term of `eq:lps-regularized-Hm-identity`.
-/

public section

open MeasureTheory
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A scalar whole-space heat pairing dissipates the square of one
coordinate derivative (eq:lps-regularized-Hm-identity). -/
theorem lps_heat_pairing_direction
    {h : Vec3 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (j : Fin 3)
    (h0 : MemLp h 2 volume)
    (h1 : MemLp (spatialDeriv h j) 2 volume)
    (h2 : MemLp (spatialDeriv (spatialDeriv h j) j) 2 volume) :
    (∫ x : Vec3, h x * spatialDeriv (spatialDeriv h j) j x) =
      -(∫ x : Vec3, (spatialDeriv h j x) ^ 2) := by
  have hfirst :
      Integrable (fun x : Vec3 => spatialDeriv h j x * spatialDeriv h j x)
        volume := h1.integrable_mul h1
  have hsecond :
      Integrable (fun x : Vec3 => h x *
        spatialDeriv (spatialDeriv h j) j x) volume :=
    h0.integrable_mul h2
  have hcross :
      Integrable (fun x : Vec3 => h x * spatialDeriv h j x) volume :=
    h0.integrable_mul h1
  have hhsmooth : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv h j) := by
    simpa [wordDeriv] using contDiff_wordDeriv hh [j]
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := h) (g := spatialDeriv h j)
    (v := basisVec j)
    hfirst hsecond hcross
    (fun x _ => hh.differentiable (by simp) x)
    (fun x _ => hhsmooth.differentiable (by simp) x)
  simpa only [spatialDeriv, pow_two] using h

/-- Summing the coordinate heat pairings yields the full
spatial-gradient dissipation (eq:lps-regularized-Hm-identity). -/
theorem lps_heat_pairing_laplacian
    {h : Vec3 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (h0 : MemLp h 2 volume)
    (h1 : ∀ j : Fin 3, MemLp (spatialDeriv h j) 2 volume)
    (h2 : ∀ j : Fin 3,
      MemLp (spatialDeriv (spatialDeriv h j) j) 2 volume) :
    (∫ x : Vec3, h x *
      (∑ j : Fin 3, spatialDeriv (spatialDeriv h j) j x)) =
      -(∑ j : Fin 3,
        ∫ x : Vec3, (spatialDeriv h j x) ^ 2) := by
  calc
    (∫ x : Vec3, h x *
      (∑ j : Fin 3, spatialDeriv (spatialDeriv h j) j x)) =
        ∫ x : Vec3, ∑ j : Fin 3,
          h x * spatialDeriv (spatialDeriv h j) j x := by
            congr 1
            funext x
            rw [Finset.mul_sum]
    _ = ∑ j : Fin 3,
          ∫ x : Vec3, h x * spatialDeriv (spatialDeriv h j) j x := by
            exact integral_finsetSum _ (fun j _ => h0.integrable_mul (h2 j))
    _ = ∑ j : Fin 3,
          -(∫ x : Vec3, (spatialDeriv h j x) ^ 2) := by
            apply Finset.sum_congr rfl
            intro j _
            exact lps_heat_pairing_direction hh j h0 (h1 j) (h2 j)
    _ = -(∑ j : Fin 3,
          ∫ x : Vec3, (spatialDeriv h j x) ^ 2) :=
            by rw [Finset.sum_neg_distrib]

/-- A smooth whole-space divergence term transfers one derivative
to the energy test field (eq:lps-regularized-Hm-identity). -/
theorem lps_divergence_pairing_direction
    {h F : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (j : Fin 3)
    (hh0 : MemLp h 2 volume)
    (hh1 : MemLp (spatialDeriv h j) 2 volume)
    (hF0 : MemLp F 2 volume)
    (hF1 : MemLp (spatialDeriv F j) 2 volume) :
    (∫ x : Vec3, h x * spatialDeriv F j x) =
      -(∫ x : Vec3, spatialDeriv h j x * F x) := by
  have hleft : Integrable
      (fun x : Vec3 => spatialDeriv h j x * F x) volume :=
    hh1.integrable_mul hF0
  have hright : Integrable
      (fun x : Vec3 => h x * spatialDeriv F j x) volume :=
    hh0.integrable_mul hF1
  have hcross : Integrable (fun x : Vec3 => h x * F x) volume :=
    hh0.integrable_mul hF0
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := h) (g := F) (v := basisVec j)
    hleft hright hcross
    (fun x _ => hh.differentiable (by simp) x)
    (fun x _ => hF.differentiable (by simp) x)
  simpa only [spatialDeriv] using h

end ESS
