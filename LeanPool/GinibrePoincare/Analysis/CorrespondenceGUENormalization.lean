/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUENormalization.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEDensityConvergence
/-!
# Correspondence GUE normalization

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueDoubledOrderedMeasure_probability`, `gueDoubledOrderedMeasure_integral`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- The explicit point with real coordinates `x (i, 0) = i` and auxiliary coordinates `0`. -/
def gueOrderedWitness (n : ℕ) : EuclideanSpace ℝ (Fin n×Fin 2) :=
  WithLp.toLp 2 (fun p => if p.2=0 then (p.1.val : ℝ) else 0)

theorem gueDoubledOrderedDensity_witness_pos (n : ℕ) :
    0 < gueDoubledOrderedDensity n (gueOrderedWitness n) := by
  unfold gueDoubledOrderedDensity
  apply mul_pos (Real.exp_pos _)
  apply Finset.prod_pos
  intro p hp
  have hij : p.1<p.2 := (Finset.mem_filter.mp hp).2
  have h : (0 : ℝ)<(p.2.val : ℝ)-(p.1.val : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hij)
  change 0 < gueOrderedPairWeight ((p.2.val : ℝ)-(p.1.val : ℝ))
  rw [gueOrderedPairWeight, ite_eq_left h]
  exact sq_pos_of_pos h

theorem gueDoubledOrdered_partition_pos {n : ℕ} (hn : 0 < n) :
    0 < ∫ x, gueDoubledOrderedDensity n x := by
  exact integral_pos_of_integrable_nonneg_nonzero
    (gueDoubledOrderedDensity_continuous n) (gueDoubledOrderedDensity_integrable hn)
    (gueDoubledOrderedDensity_nonneg n)
    (ne_of_gt (gueDoubledOrderedDensity_witness_pos n))

/-- The doubled ordered measure: the density `gueDoubledOrderedDensity n` with respect to
Lebesgue measure, normalized by its total integral. -/
def gueDoubledOrderedMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n×Fin 2)) :=
  (ENNReal.ofReal (∫ x, gueDoubledOrderedDensity n x))⁻¹ •
    volume.withDensity (fun x => ENNReal.ofReal (gueDoubledOrderedDensity n x))

theorem gueDoubledOrderedMeasure_probability {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (gueDoubledOrderedMeasure n) := by
  constructor
  unfold gueDoubledOrderedMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gueDoubledOrderedDensity_integrable hn)
      (Eventually.of_forall (gueDoubledOrderedDensity_nonneg n))]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (gueDoubledOrdered_partition_pos hn)) ENNReal.ofReal_ne_top

theorem gueDoubledOrderedMeasure_integral (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ) :
    (∫ x, f x ∂gueDoubledOrderedMeasure n) =
      (∫ x, gueDoubledOrderedDensity n x*f x)/(∫ x, gueDoubledOrderedDensity n x) := by
  unfold gueDoubledOrderedMeasure
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul
    (μ := volume) (f := fun x => ENNReal.ofReal (gueDoubledOrderedDensity n x))
    ((gueDoubledOrderedDensity_continuous n).measurable.ennreal_ofReal)
    (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (gueDoubledOrderedDensity_nonneg n _),
      smul_eq_mul]
  rw [ENNReal.toReal_ofReal (integral_nonneg (gueDoubledOrderedDensity_nonneg n))]
  ring

end
end GinibrePoincare
