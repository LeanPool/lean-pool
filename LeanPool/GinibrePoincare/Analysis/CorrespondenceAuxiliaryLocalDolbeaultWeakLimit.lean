/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultWeakLimit.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultLpIteration

/-!
# Correspondence auxiliary local Dolbeault weak limit

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeault_weak_identity_of_strong_limit`,
`dolbeault_weak_identity_of_eventual_strong_limit`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

theorem dbarComponent_compact_support {n : ℕ} (θ : Configuration n → ℂ)
    (hc : HasCompactSupport θ) (j : Fin n) :
    HasCompactSupport (fun p => dbarComponent θ j p) := by
  exact ((hc.fderiv_apply ℝ (realCoordinateDirection j)).add
    ((hc.fderiv_apply ℝ (imaginaryCoordinateDirection j)).mul_left
      (f := fun _ => Complex.I))).mul_left (f := fun _ => (1/2 : ℂ))

/-- Ordinary strong L² limits preserve the literal local distributional
solution identities against every ordinary compact smooth test. -/
theorem dolbeault_weak_identity_of_strong_limit {n : ℕ} {ι : Type*}
    {f : Filter ι} [f.NeBot] (u a : ι → dolbeaultOrdinaryL2 n)
    (U A : dolbeaultOrdinaryL2 n) (hu : Tendsto u f (𝓝 U)) (ha : Tendsto a f (𝓝 A))
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (j : Fin n)
    (he : ∀ i, (∫ p, θ p * a i p) = -∫ p, dbarComponent θ j p * u i p) :
    (∫ p, θ p*A p) = -∫ p, dbarComponent θ j p*U p := by
  have hd := (smooth_dbarComponent_contDiff θ hθ j).continuous
  have hdc := dbarComponent_compact_support θ hc j
  have ha' := ((dolbeaultCompactPairing θ hθ.continuous hc).continuous.tendsto _).comp ha
  have hu' := ((dolbeaultCompactPairing (fun p => dbarComponent θ j p) hd hdc).continuous.tendsto
      _).comp hu
  simp only [Function.comp_def, dolbeaultCompactPairing_eq_integral] at ha' hu'
  have heq : (fun i => ∫ p, θ p*a i p) =
      (fun i => -∫ p, dbarComponent θ j p*u i p) := funext he
  rw [heq] at ha'
  exact tendsto_nhds_unique ha' hu'.neg

theorem dolbeault_weak_identity_of_eventual_strong_limit {n : ℕ} {ι : Type*}
    {f : Filter ι} [f.NeBot] (u a : ι → dolbeaultOrdinaryL2 n)
    (U A : dolbeaultOrdinaryL2 n) (hu : Tendsto u f (𝓝 U)) (ha : Tendsto a f (𝓝 A))
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (j : Fin n)
    (he : ∀ᶠ i in f, (∫ p, θ p * a i p) = -∫ p, dbarComponent θ j p * u i p) :
    (∫ p, θ p*A p) = -∫ p, dbarComponent θ j p*U p := by
  have hd := (smooth_dbarComponent_contDiff θ hθ j).continuous
  have hdc := dbarComponent_compact_support θ hc j
  have ha' := ((dolbeaultCompactPairing θ hθ.continuous hc).continuous.tendsto _).comp ha
  have hu' := ((dolbeaultCompactPairing (fun p => dbarComponent θ j p) hd hdc).continuous.tendsto
      _).comp hu
  simp only [Function.comp_def, dolbeaultCompactPairing_eq_integral] at ha' hu'
  have he' : (fun i => ∫ p, θ p*a i p) =ᶠ[f]
      (fun i => -∫ p, dbarComponent θ j p*u i p) := he
  exact tendsto_nhds_unique ha' (hu'.neg.congr' he'.symm)

end
end GinibrePoincare
