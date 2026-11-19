/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupRegularity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupDynamics

/-! # Unconditional positive-time generator regularization -/

@[expose] public section
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous divided-difference spectral preimage at positive time. -/
def resolventCfcSmoothingPreimage (R : H →L[ℂ] H) (t : ℝ≥0) : H →L[ℂ] H :=
  cfc (dslope (resolventEvolutionMultiplier (t : ℝ)) 0) R

/-- Positive-time evolution maps the entire Hilbert space into the resolvent range. -/
theorem resolventCfcEvolution_smoothing_preimage (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (t : ℝ≥0) (ht : 0 < t) :
    R * resolventCfcSmoothingPreimage R t = resolventCfcEvolution R t := by
  let f := resolventEvolutionMultiplier (t : ℝ)
  have hc : Continuous f := resolventEvolutionMultiplier_continuous _
  have hd : DifferentiableAt ℝ f 0 :=
    (resolventEvolutionMultiplier_contDiff _).differentiable (by simp) |>.differentiableAt
  have hg : Continuous (dslope f 0) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope (s := Set.univ) (by simp)).mpr ⟨hc.continuousOn, hd⟩
  have hf0 : f 0 = 0 := resolventEvolutionMultiplier_nonpositive (by exact_mod_cast ht) le_rfl
  have he : (fun r : ℝ => r * dslope f 0 r) = f := by
    funext r
    simpa only [sub_zero, hf0, smul_eq_mul] using sub_smul_dslope f 0 r
  change R * cfc (dslope f 0) R = cfc f R
  calc
    _ = cfc (fun r : ℝ => r) R * cfc (dslope f 0) R := by rw [cfc_id' ℝ R hR]
    _ = cfc (fun r : ℝ => r * dslope f 0 r) R :=
      (cfc_mul (fun r : ℝ => r) (dslope f 0) R continuousOn_id hg.continuousOn).symm
    _ = _ := by rw [he]

/-- Every positive-time output belongs to the exact maximal generator domain. -/
theorem resolventCfcEvolution_smoothing_graph (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R) (t : ℝ≥0) (ht : 0 < t) (x : H) :
    (resolventCfcEvolution R t x,
      resolventCfcEvolution R t x - resolventCfcSmoothingPreimage R t x) ∈
      (resolventGenerator R hInj).graph := by
  rw [resolventGenerator_graph R hInj]
  change R (resolventCfcEvolution R t x -
    (resolventCfcEvolution R t x - resolventCfcSmoothingPreimage R t x)) = _
  rw [sub_sub_cancel]
  exact congrArg (fun A : H →L[ℂ] H => A x) (resolventCfcEvolution_smoothing_preimage R hR t ht)

/-- The actual full diffusion regularizes every symmetric weighted L² datum. -/
theorem ginibreFullEvolution_smoothing_graph (n : ℕ) (hn : 0 < n)
    (t : ℝ≥0) (ht : 0 < t) (x : ginibreSymmetricL2 n) :
    (ginibreFullEvolution n hn t x,
      ginibreFullEvolution n hn t x - resolventCfcSmoothingPreimage
        (ginibreFullComplexResolvent n hn) t x) ∈ (ginibreFullGenerator n hn).graph :=
  resolventCfcEvolution_smoothing_graph _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) t ht x

end
end GinibrePoincare
