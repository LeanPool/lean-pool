/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientCompatibility
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientProjection

/-!
# Compactness Gradient Global

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Topology
open CKN CKN.Foundation.Parabolic

namespace CKN.Leray

/-- Compatible local weak spatial gradients on a nested exhaustion have a
jointly measurable representative that agrees with each local gradient
almost everywhere on its full open rectangle. -/
theorem exists_measurable_gradient_of_local_weak_partials
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hKmono : ∀ j, K j ⊆ K (j + 1))
    (hJmono : ∀ j, J j ⊆ J (j + 1))
    (hJ : ∀ j, IsCompact (J j))
    (u : Vec3 × ℝ → Vec3)
    (gLocal : ℕ → Vec3 × ℝ → CompactnessGradientFiber)
    (hgMeas : ∀ j, Measurable (gLocal j))
    (hlocal : ∀ j (i m : Fin 3), ∀ᵐ t ∂(volume.restrict (J j)),
      LocallyIntegrableOn
        (fun x => gLocal j (x,t) i m) (interior (K j)) volume ∧
      HasWeakPartialDerivOn (interior (K j)) m
        (fun x => u (x,t) i)
        (fun x => gLocal j (x,t) i m)) :
    ∃ g : Vec3 × ℝ → CompactnessGradientFiber,
      Measurable g ∧ ∀ j,
        g =ᵐ[((volume.restrict (interior (K j))).prod
          (volume.restrict (J j)))] gLocal j := by
  classical
  let R : ℕ → Set (Vec3 × ℝ) :=
    fun j => interior (K j) ×ˢ J j
  have hRmeas (j : ℕ) : MeasurableSet (R j) :=
    isOpen_interior.measurableSet.prod (hJ j).measurableSet
  have hρ (j : ℕ) : (volume : Measure (Vec3 × ℝ)).restrict (R j) =
      (volume.restrict (interior (K j))).prod
        (volume.restrict (J j)) := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (interior (K j) ×ˢ J j) =
      (volume.restrict (interior (K j))).prod
        (volume.restrict (J j))
    rw [Measure.prod_restrict]
  have hcompat (a b : ℕ) (hab : a ≤ b) :
      gLocal a =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict (R a)]
        gLocal b := by
    rw [hρ]
    have hcoord (i m : Fin 3) :
        (fun z => gLocal a z i m) =ᵐ[
          (volume.restrict (interior (K a))).prod
            (volume.restrict (J a))]
          (fun z => gLocal b z i m) := by
      exact weak_partial_representatives_agree_on_nested_rectangles
        K J hKmono hJmono (fun z => u z i)
        (fun k z => gLocal k z i m)
        (fun k => ((gradientCoordinateCLM i m).continuous.measurable).comp
          (hgMeas k))
        m (fun k => hlocal k i m) hab
    have hAll : ∀ᵐ z ∂((volume.restrict (interior (K a))).prod
        (volume.restrict (J a))), ∀ i m : Fin 3,
        gLocal a z i m = gLocal b z i m :=
      (ae_all_iff).mpr (fun i => (ae_all_iff).mpr (fun m => hcoord i m))
    filter_upwards [hAll] with z hz
    ext i m
    exact hz i m
  obtain ⟨g, hg, hpiece⟩ :=
    exists_measurable_disjointed_gradient_representative
      K J hJ gLocal hgMeas
  refine ⟨g, hg, fun j => ?_⟩
  have h := ae_eq_on_nested_sets_of_disjointed_representative
    R hRmeas gLocal g hpiece hcompat j
  rwa [hρ] at h

end CKN.Leray
