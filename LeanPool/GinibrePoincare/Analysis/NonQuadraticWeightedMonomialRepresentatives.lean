/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticWeightedMonomialRepresentatives.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticAlternatingMonomialClosure
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiTensorConvolution

/-!
# Non quadratic weighted monomial representatives

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarPiWeightedMonomialVector_coeFn`, `piPotentialHalfWeight_permute`,
`complexLp_finset_sum_coeFn`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

theorem planarPiWeightedMonomialVector_coeFn {d : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (F : PlanarPiLebesgueL2 d) (hF : F ∈ planarPiWeightedMonomialVectors d n V) :
    ∃ p : Fin d → ℕ, ∃ c : ℂ,
      (F : Configuration d → ℂ) =ᵐ[volume]
        (fun x => c * (∏ i, x i ^ p i) * piPotentialHalfWeight d n V x) := by
  obtain ⟨u, hu, rfl⟩ := hF
  choose p c hm he using hu
  have hscalar (i : Fin d) : (u i : ℂ → ℂ) =ᵐ[volume]
      (fun z => c i * z ^ p i * planarPotentialHalfWeight n V z) := by
    rw [← he i]
    exact (hm i).coeFn_toLp
  have hall : ∀ᵐ x ∂Measure.pi (fun _ : Fin d => (volume : Measure ℂ)), ∀ i,
      u i (x i) = c i * x i ^ p i * planarPotentialHalfWeight n V (x i) :=
    ae_all_iff.mpr (fun i => (quasiMeasurePreserving_eval (fun _ => (volume : Measure ℂ))
        i).ae_eq_comp (hscalar i))
  refine ⟨p, ∏ i, c i, ?_⟩
  rw [volume_pi]
  filter_upwards [l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ)) u, hall] with x hx hh
  rw [hx]
  simp only [hh, Finset.prod_mul_distrib, piPotentialHalfWeight]

theorem piPotentialHalfWeight_permute {d : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (σ : ParticlePermutation d) (x : Configuration d) :
    piPotentialHalfWeight d n V (permute σ x) = piPotentialHalfWeight d n V x := by
  unfold piPotentialHalfWeight
  exact Equiv.prod_comp σ (fun i => planarPotentialHalfWeight n V (x i))

theorem complexLp_finset_sum_coeFn {A I : Type*} [MeasurableSpace A]
    (μ : Measure A) (s : Finset I) (U : I → Lp ℂ 2 μ) :
    ((∑ i ∈ s, U i : Lp ℂ 2 μ) : A → ℂ) =ᵐ[μ] (fun x => ∑ i ∈ s, U i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    simpa using hx
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    filter_upwards [Lp.coeFn_add (U i) (∑ j ∈ s, U j), ih] with x hx hh
    rw [hx]
    change U i x + (∑ j ∈ s, U j) x = _
    rw [hh]
end
end GinibrePoincare
