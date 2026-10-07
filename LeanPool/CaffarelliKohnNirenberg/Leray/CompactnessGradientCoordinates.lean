/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientProjection
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientExtract
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Compactness Gradient Coordinates

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- A weak `L²` limit of the matrix gradient gives weak convergence of
each scalar gradient coordinate against all `L²` tests. -/
theorem weak_gradient_coordinate_integrals
    {μ : Measure (Vec3 × ℝ)}
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (D : Lp CompactnessGradientFiber 2 μ)
    (hmem : ∀ k, MemLp
      (fun z => toCompactnessGradientFiber (Du k z)) 2 μ)
    (hweak : ∀ w, Tendsto
      (fun k => inner ℝ ((hmem k).toLp
        (fun z => toCompactnessGradientFiber (Du k z))) w) atTop
      (nhds (inner ℝ D w)))
    (i j : Fin 3) (w : Vec3 × ℝ → ℝ) (hw : MemLp w 2 μ) :
    Tendsto (fun k => ∫ z, Du k z i j * w z ∂μ) atTop
      (nhds (∫ z, gradientCoordinateCLM i j (D z) * w z ∂μ)) := by
  have h := weak_l2_scalar_integral_of_fiber_weak
    (gradientCoordinateCLM i j)
    (fun k z => toCompactnessGradientFiber (Du k z))
    D hmem hweak w hw
  simpa only [gradientCoordinateCLM_toCompactnessGradientFiber] using h

/-- The coordinate pairings restrict from a compact rectangle to an open
spatial subrectangle by extending each test by zero. -/
theorem weak_gradient_coordinate_integrals_on_subrectangle
    {K Ω : Set Vec3} {J : Set ℝ}
    (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) (hJ : MeasurableSet J)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (D : Lp CompactnessGradientFiber 2
      ((volume.restrict K).prod (volume.restrict J)))
    (hmem : ∀ k, MemLp
      (fun z => toCompactnessGradientFiber (Du k z)) 2
        ((volume.restrict K).prod (volume.restrict J)))
    (hweak : ∀ v, Tendsto
      (fun k => inner ℝ ((hmem k).toLp
        (fun z => toCompactnessGradientFiber (Du k z))) v) atTop
      (nhds (inner ℝ D v)))
    (i j : Fin 3) (w : Vec3 × ℝ → ℝ)
    (hw : MemLp w 2
      ((volume.restrict Ω).prod (volume.restrict J))) :
    Tendsto (fun k => ∫ z, Du k z i j * w z
      ∂((volume.restrict Ω).prod (volume.restrict J))) atTop
      (nhds (∫ z, gradientCoordinateCLM i j (D z) * w z
        ∂((volume.restrict Ω).prod (volume.restrict J)))) := by
  classical
  let ρK : Measure (Vec3 × ℝ) :=
    (volume.restrict K).prod (volume.restrict J)
  let ρΩ : Measure (Vec3 × ℝ) :=
    (volume.restrict Ω).prod (volume.restrict J)
  let S : Set (Vec3 × ℝ) := Ω ×ˢ J
  have hS : MeasurableSet S := hΩ.measurableSet.prod hJ
  have hSK : S ⊆ K ×ˢ J := by
    intro z hz
    exact ⟨hΩK hz.1, hz.2⟩
  have hρK : ρK =
      (volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ J) := by
    change (volume.restrict K).prod (volume.restrict J) =
      ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (K ×ˢ J)
    rw [Measure.prod_restrict]
  have hρΩ : ρΩ =
      (volume : Measure (Vec3 × ℝ)).restrict S := by
    change (volume.restrict Ω).prod (volume.restrict J) =
      ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Ω ×ˢ J)
    rw [Measure.prod_restrict]
  have hρrestrict : ρK.restrict S = ρΩ := by
    rw [hρK, Measure.restrict_restrict_of_subset hSK, hρΩ]
  have htest : MemLp (S.indicator w) 2 ρK := by
    rw [memLp_indicator_iff_restrict hS]
    rwa [hρrestrict]
  have hInt (H : Vec3 × ℝ → ℝ) :
      (∫ z, H z * S.indicator w z ∂ρK) =
        ∫ z, H z * w z ∂ρΩ := by
    have heq : (fun z => H z * S.indicator w z) =
        S.indicator (fun z => H z * w z) := by
      funext z
      by_cases hz : z ∈ S <;> simp [Set.indicator, hz]
    rw [heq, integral_indicator hS]
    change (∫ z, H z * w z ∂ρK.restrict S) =
      (∫ z, H z * w z ∂ρΩ)
    rw [hρrestrict]
  have h := weak_gradient_coordinate_integrals Du D hmem hweak
    i j (S.indicator w) htest
  simpa only [ρK, ρΩ, hInt] using h

end CKN.Leray
