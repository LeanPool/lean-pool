/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreLiteralProjectionGeometry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreConjugationGeometry
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! # Projection residual identities on the concrete smooth Ginibre core

These are the projection-norm formulas in arXiv:2608.19358v2,
Lemma 2.7(3), on the smooth core and the proved closed holomorphic
polynomial subspace. They do not identify the representative-level
infimum over all entire functions defined in `HolomorphicDistance`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem ginibre_core_holomorphic_projection_residual_identity {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    let u := centeredObservableL2 hn f hf
    let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection u
    let r := u - h - star h
    ‖u - h‖ ^ 2 = smoothGinibreVariance n f / 2 + ‖r‖ ^ 2 / 2 := by
  dsimp
  let u := centeredObservableL2 hn f hf
  let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection u
  have hh : h ∈ (ginibreHolomorphicAmbientClosedSpan n hn).toSubmodule :=
    Submodule.starProjection_apply_mem _ u
  have ho : inner ℂ h (u - h) = 0 := by
    rw [← inner_conj_symm h (u - h), Submodule.starProjection_inner_eq_zero u h hh,
      map_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero h (u - h) ho
  have he : h + (u - h) = u := by abel
  rw [he] at hp
  have hnrm : ‖u‖ ^ 2 = smoothGinibreVariance n f := norm_sq_centeredObservableL2 hn f hf
  have hg := (centeredHolomorphicRemainderGeometry hn f hf).2.2.2
  change smoothGinibreVariance n f = 2 * ‖h‖ ^ 2 + ‖u - h - star h‖ ^ 2 at hg
  change ‖u - h‖ ^ 2 = smoothGinibreVariance n f / 2 + ‖u - h - star h‖ ^ 2 / 2
  nlinarith

theorem ginibre_core_holomorphic_projection_half_distance {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    smoothGinibreVariance n f / 2 ≤
      ‖centeredObservableL2 hn f hf -
        (ginibreHolomorphicAmbientClosedSpan n hn).starProjection (centeredObservableL2 hn f hf)‖ ^
            2 := by
  rw [ginibre_core_holomorphic_projection_residual_identity hn f hf]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by norm_num))

end
end GinibrePoincare
