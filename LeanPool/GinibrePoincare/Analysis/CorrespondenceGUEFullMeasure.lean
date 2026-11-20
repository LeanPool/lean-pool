/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEFullMeasure.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEChamberIntegrals
/-!
# Correspondence GUE full measure

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueFullMeasure_probability`, `gueFullMeasure_symmetric_integral`.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

theorem gueRawDensity_integrable {n : ℕ} (hn : 0 < n) : Integrable (gueRawDensity n) volume := by
  have hσ (σ : Equiv.Perm (Fin n)) : Integrable (fun x => gueOrderedRawDensity n (guePermute n σ x))
      volume :=
    (guePermute_volume_preserving n σ).integrable_comp_of_integrable
        (gueOrderedRawDensity_integrable hn)
  simpa only [gueChamber_density_partition] using integrable_finsetSum Finset.univ (fun σ _ => hσ σ)

theorem gueRawDensity_partition_pos {n : ℕ} (hn : 0 < n) : 0<∫x, gueRawDensity n x := by
  have h := gueChamber_weighted_integral hn (fun _ => 1) continuous_const
    (by intros; rfl) 1 (by intros; norm_num)
  simp only [mul_one] at h
  rw [h]
  exact mul_pos (by exact_mod_cast Fintype.card_pos) (gueOrderedRawDensity_partition_pos hn)

/-- The GUE eigenvalue measure on `EuclideanSpace ℝ (Fin n)`: the density `gueRawDensity n` with
respect to Lebesgue measure, normalized by its total integral. -/
def gueFullMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (ENNReal.ofReal (∫x, gueRawDensity n x))⁻¹ • volume.withDensity (fun x => ENNReal.ofReal
      (gueRawDensity n x))

theorem gueRawDensity_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : 0≤gueRawDensity n x := by
  unfold gueRawDensity
  positivity

theorem gueRawDensity_continuous (n : ℕ) : Continuous (gueRawDensity n) := by
  unfold gueRawDensity
  fun_prop

theorem gueFullMeasure_probability {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (gueFullMeasure n) :=
    by
  constructor
  unfold gueFullMeasure
  rw [_root_.smul_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gueRawDensity_integrable hn)
      (Eventually.of_forall (gueRawDensity_nonneg n))]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (gueRawDensity_partition_pos hn))
      ENNReal.ofReal_ne_top

theorem gueFullMeasure_integral (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫x, f x ∂gueFullMeasure n)=(∫x, gueRawDensity n x*f x)/(∫x, gueRawDensity n x) := by
  unfold gueFullMeasure
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul (μ := volume)
    (f := fun x => ENNReal.ofReal (gueRawDensity n x))
    ((gueRawDensity_continuous n).measurable.ennreal_ofReal)
    (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (gueRawDensity_nonneg n _), smul_eq_mul]
  rw [ENNReal.toReal_ofReal (integral_nonneg (gueRawDensity_nonneg n))]
  ring

theorem gueFullMeasure_symmetric_integral {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (hs : ∀ σ x, f (guePermute n σ x) = f x) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫x, f x ∂gueFullMeasure n)=(∫x, f x ∂gueOrderedMeasure n) := by
  rw [gueFullMeasure_integral, gueOrderedMeasure_integral,
    gueChamber_weighted_integral hn f hf hs C hb]
  have hp := gueChamber_weighted_integral hn (fun _ => 1) continuous_const
    (by intros; rfl) 1 (by intros; norm_num)
  simp only [mul_one] at hp
  rw [hp]
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ)≠0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hc]

end
end GinibrePoincare
