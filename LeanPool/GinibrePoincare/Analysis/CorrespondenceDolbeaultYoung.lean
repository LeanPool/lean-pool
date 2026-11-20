/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoung.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungTranslation

/-!
# Correspondence Dolbeault Young

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultCoordinateConvolution_pairing`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Convolution of `u` with the kernel `k` in the `j`-th coordinate, as the Bochner integral
`∫ y, k y • dolbeaultTranslateL2 j y u` of translates. -/
def dolbeaultCoordinateConvolution {n : ℕ} (j : Fin n) (k : ℂ → ℂ)
    (u : dolbeaultOrdinaryL2 n) : dolbeaultOrdinaryL2 n :=
  ∫ y : ℂ, k y • dolbeaultTranslateL2 j y u

theorem dolbeaultCoordinateConvolution_integrable {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) (u : dolbeaultOrdinaryL2 n) :
    Integrable (fun y : ℂ => k y • dolbeaultTranslateL2 j y u) volume := by
  have hm := hk.aestronglyMeasurable.smul (dolbeaultTranslateL2_continuous j u).aestronglyMeasurable
  apply (hk.norm.mul_const ‖u‖).mono' hm
  exact ae_of_all _ (fun y => by
    change ‖k y • dolbeaultTranslateL2 j y u‖ ≤ _
    rw [norm_smul, dolbeaultTranslateL2_norm])

/-- Genuine coordinate Young bound on ordinary Lebesgue L² in arbitrary dimension. -/
theorem dolbeaultCoordinateConvolution_norm {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (u : dolbeaultOrdinaryL2 n) :
    ‖dolbeaultCoordinateConvolution j k u‖ ≤ (∫ y : ℂ, ‖k y‖)*‖u‖ := by
  unfold dolbeaultCoordinateConvolution
  calc
    _ ≤ ∫ y : ℂ, ‖k y • dolbeaultTranslateL2 j y u‖ := norm_integral_le_integral_norm _
    _ = _ := by simp_rw [norm_smul, dolbeaultTranslateL2_norm]; rw [integral_mul_const]

/-- `dolbeaultCoordinateConvolution j k` as a linear map, for an integrable kernel `k`. -/
def dolbeaultCoordinateConvolutionLinear {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) :
    dolbeaultOrdinaryL2 n →ₗ[ℂ] dolbeaultOrdinaryL2 n where
  toFun := dolbeaultCoordinateConvolution j k
  map_add' u v := by
    unfold dolbeaultCoordinateConvolution
    simp only [map_add, smul_add]
    exact integral_add (dolbeaultCoordinateConvolution_integrable j k hk u)
      (dolbeaultCoordinateConvolution_integrable j k hk v)
  map_smul' c u := by
    unfold dolbeaultCoordinateConvolution
    simp only [map_smul, smul_smul]
    simp_rw [mul_comm (k _) c]
    simp_rw [← smul_smul]
    rw [integral_smul]
    rfl

/-- Coordinate convolution with an integrable kernel `k` as a bounded operator on ordinary `L²`,
with norm at most `∫ ‖k‖`. -/
def dolbeaultCoordinateConvolutionCLM {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  (dolbeaultCoordinateConvolutionLinear j k hk).mkContinuous (∫ y : ℂ, ‖k y‖)
    (dolbeaultCoordinateConvolution_norm j k)

/-- Every bounded ordinary-L² test functional commutes with the actual convolution. -/
theorem dolbeaultCoordinateConvolution_pairing {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) (u : dolbeaultOrdinaryL2 n)
    (T : dolbeaultOrdinaryL2 n →L[ℂ] ℂ) :
    T (dolbeaultCoordinateConvolution j k u) =
      ∫ y : ℂ, k y*T (dolbeaultTranslateL2 j y u) := by
  rw [dolbeaultCoordinateConvolution,← T.integral_comp_comm
    (dolbeaultCoordinateConvolution_integrable j k hk u)]
  simp only [map_smul, smul_eq_mul]

end
end GinibrePoincare
