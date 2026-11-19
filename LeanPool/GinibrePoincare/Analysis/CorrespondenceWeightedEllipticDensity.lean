/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticDensity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRestrictedData
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
/-!
# Correspondence weighted elliptic density

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_locallyIntegrable`,
`correspondenceWeightedElliptic_integral_density`,
`correspondenceWeightedElliptic_compact_value_memLp`.
-/

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The measure with density `ρ` (through `ENNReal.ofReal`) with respect to `volume`. -/
def correspondenceWeightedEllipticMeasure (ρ : E → ℝ) : Measure E :=
  volume.withDensity (fun x=>ENNReal.ofReal (ρ x))

theorem correspondenceWeightedElliptic_volume_ac (ρ : E → ℝ)
    (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    (volume : Measure E) ≪ correspondenceWeightedEllipticMeasure ρ := by
  apply withDensity_absolutelyContinuous' (hρ.measurable.ennreal_ofReal.aemeasurable)
  exact ae_of_all volume (fun x=>ne_of_gt (ENNReal.ofReal_pos.mpr (hp x)))

theorem correspondenceWeightedElliptic_integrable_density (ρ f : E → ℝ)
    (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    Integrable f (correspondenceWeightedEllipticMeasure ρ) ↔
      Integrable (fun x=>ρ x*f x) volume := by
  unfold correspondenceWeightedEllipticMeasure
  rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
    (ae_of_all volume (fun _=>ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_of_lt (hp _)), smul_eq_mul]

theorem correspondenceWeightedElliptic_memLp_compact {V : Type*} [NormedAddCommGroup V]
    (ρ : E → ℝ) (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x) (f : E → V)
    (hf : MemLp f 2 (correspondenceWeightedEllipticMeasure ρ))
    (K : Set E) (hK : IsCompact K) : MemLp f 2 (volume.restrict K) := by
  have hm := hf.aestronglyMeasurable.mono_ac (correspondenceWeightedElliptic_volume_ac ρ hρ hp)
  apply (memLp_two_iff_integrable_sq_norm hm.restrict).mpr
  have hi := (correspondenceWeightedElliptic_integrable_density ρ (fun x=>‖f x‖^2) hρ hp).mp
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
  have hInv : Continuous (fun x=>(ρ x)⁻¹) := hρ.inv₀ (fun x=>(hp x).ne')
  have hl := hi.locallyIntegrable.mul_continuous hInv
  have he : (fun x=>(ρ x*‖f x‖^2)*(ρ x)⁻¹)=(fun x=>‖f x‖^2) := by
    funext x
    field_simp [(hp x).ne']
  rw [he] at hl
  exact hl.integrableOn_isCompact hK

theorem correspondenceWeightedElliptic_compact_multiplier_memLp
    (ρ : E → ℝ) (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x) (u q : E → ℝ)
    (hu : MemLp u 2 (correspondenceWeightedEllipticMeasure ρ)) (hq : Continuous q)
    (K : Set E) (hK : IsCompact K) : MemLp (fun x=>q x*u x) 2 (volume.restrict K) := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := ginibreLocalRegularity_exists_compact_cutoff K hK
  have htop : MemLp (χ*q) ⊤ ((volume : Measure E).restrict K) :=
    (hχ.continuous.mul hq).memLp_top_of_hasCompactSupport (hχc.mul_right) _
  have hm := htop.fun_mul (r:=2) (correspondenceWeightedElliptic_memLp_compact ρ hρ hp u hu K hK)
  apply hm.ae_eq
  apply ae_restrict_of_forall_mem hK.measurableSet
  intro x hx
  dsimp only [Pi.mul_apply]
  rw [(hχone x hx).eq_of_nhds]
  simp

theorem correspondenceWeightedElliptic_locallyIntegrable
    (ρ : E → ℝ) (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x) (u : E → ℝ)
    [IsFiniteMeasure (correspondenceWeightedEllipticMeasure ρ)]
    (hu : MemLp u 2 (correspondenceWeightedEllipticMeasure ρ)) : LocallyIntegrable u volume := by
  have hi := (correspondenceWeightedElliptic_integrable_density ρ u hρ hp).mp
    (hu.integrable (by norm_num))
  have hInv : Continuous (fun x=>(ρ x)⁻¹) := hρ.inv₀ (fun x=>(hp x).ne')
  have hl := hi.locallyIntegrable.mul_continuous hInv
  have he : (fun x=>(ρ x*u x)*(ρ x)⁻¹)=u := by
    funext x
    field_simp [(hp x).ne']
  rwa [he] at hl

theorem correspondenceWeightedElliptic_integral_density (ρ f : E → ℝ)
    (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    (∫x, f x∂correspondenceWeightedEllipticMeasure ρ)=∫x, ρ x*f x := by
  unfold correspondenceWeightedEllipticMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
    (ae_of_all volume (fun _=>ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_of_lt (hp _)), smul_eq_mul]

theorem correspondenceWeightedElliptic_compact_value_memLp
    (ρ : E → ℝ) (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x) (f η : E → ℝ)
    (hf : MemLp f 2 (correspondenceWeightedEllipticMeasure ρ))
    (hη : Continuous η) (hc : HasCompactSupport η) :
    MemLp (fun x=>η x*f x) 2 (volume : Measure E) := by
  have hK := correspondenceWeightedElliptic_compact_multiplier_memLp ρ hρ hp f η hf hη (tsupport η)
      hc
  have hI := (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr hK
  apply hI.ae_eq
  exact ae_of_all volume fun x=>by
    by_cases hx : x∈tsupport η
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
end
end GinibrePoincare
