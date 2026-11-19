/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungMultiplier.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungInverse

/-!
# Correspondence Dolbeault Young multiplier

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultBoundedMultiplier_memLp`, `dolbeaultBoundedMultiplier_ae`,
`dolbeaultBoundedMultiplier_norm`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem dolbeaultBoundedMultiplier_memLp {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖ ≤ C) (u : dolbeaultOrdinaryL2 n) :
    MemLp (fun z => b z*u z) 2 volume := by
  apply ((Lp.memLp u).norm.const_mul C).mono' (hb.mul (Lp.aestronglyMeasurable u))
  filter_upwards [hC] with z hz
  change ‖b z*u z‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

/-- The ordinary `L²` class of `z ↦ b z * u z` for an essentially bounded multiplier `b`. -/
def dolbeaultBoundedMultiplierValue {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖ ≤ C) (u : dolbeaultOrdinaryL2 n) :
    dolbeaultOrdinaryL2 n := (dolbeaultBoundedMultiplier_memLp b hb C hC u).toLp (fun z => b z*u z)

theorem dolbeaultBoundedMultiplier_ae {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖ ≤ C) (u : dolbeaultOrdinaryL2 n) :
    (dolbeaultBoundedMultiplierValue b hb C hC u : Configuration n → ℂ) =ᵐ[volume]
      fun z => b z*u z := (dolbeaultBoundedMultiplier_memLp b hb C hC u).coeFn_toLp

theorem dolbeaultBoundedMultiplier_norm {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖ ≤ C) (u : dolbeaultOrdinaryL2 n) :
    ‖dolbeaultBoundedMultiplierValue b hb C hC u‖ ≤ C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [dolbeaultBoundedMultiplier_ae b hb C hC u, hC] with z hz hc
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

/-- Multiplication by an essentially bounded function `b`, as a linear map on ordinary `L²`. -/
def dolbeaultBoundedMultiplierLinear {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖ ≤ C) :
    dolbeaultOrdinaryL2 n →ₗ[ℂ] dolbeaultOrdinaryL2 n where
  toFun := dolbeaultBoundedMultiplierValue b hb C hC
  map_add' u v := by
    apply Lp.ext
    filter_upwards [dolbeaultBoundedMultiplier_ae b hb C hC (u+v),
      dolbeaultBoundedMultiplier_ae b hb C hC u, dolbeaultBoundedMultiplier_ae b hb C hC v,
      Lp.coeFn_add u v, Lp.coeFn_add (dolbeaultBoundedMultiplierValue b hb C hC u)
        (dolbeaultBoundedMultiplierValue b hb C hC v)] with z h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1, h5, h2, h3, h4]
    ring
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [dolbeaultBoundedMultiplier_ae b hb C hC (c •u),
      dolbeaultBoundedMultiplier_ae b hb C hC u, Lp.coeFn_smul c u,
      Lp.coeFn_smul c (dolbeaultBoundedMultiplierValue b hb C hC u)] with z h1 h2 h3 h4
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
    rw [h1, h4, h2, h3]
    ring

/-- Actual bounded multiplication, ready to compose with coordinate Cauchy–Green homotopies. -/
def dolbeaultBoundedMultiplier {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖ ≤ C) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  (dolbeaultBoundedMultiplierLinear b hb C hC).mkContinuous C (dolbeaultBoundedMultiplier_norm b hb
      C hC)

end
end GinibrePoincare
