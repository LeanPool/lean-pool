/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiMultilinear.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2PiProducts
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Non quadratic pi multilinear

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `l2PiProductVector_update_add`, `l2PiProductVector_update_smul`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
variable {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin (m + 1) → Measure X) [∀ i, SigmaFinite (μ i)]

theorem l2PiProductVector_update_add [DecidableEq (Fin (m + 1))] (u : ∀ i, Lp ℂ 2 (μ i)) (i : Fin
    (m + 1))
    (a b : Lp ℂ 2 (μ i)) :
    l2PiProductVector μ (Function.update u i (a+b)) =
      l2PiProductVector μ (Function.update u i a) + l2PiProductVector μ (Function.update u i b) :=
          by
  apply (l2PiCoordinateEquiv μ i).injective
  rw [map_add, l2PiProductVector_split, l2PiProductVector_split, l2PiProductVector_split]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne i _)]
  change l2ProductBilinear (a+b) _ = _
  rw [map_add, LinearMap.add_apply]
  rfl

theorem l2PiProductVector_update_smul [DecidableEq (Fin (m + 1))] (u : ∀ i, Lp ℂ 2 (μ i)) (i : Fin
    (m + 1))
    (c : ℂ) (a : Lp ℂ 2 (μ i)) :
    l2PiProductVector μ (Function.update u i (c • a)) =
      c • l2PiProductVector μ (Function.update u i a) := by
  apply (l2PiCoordinateEquiv μ i).injective
  rw [map_smul, l2PiProductVector_split, l2PiProductVector_split]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne i _)]
  change l2ProductBilinear (c • a) _ = _
  rw [map_smul, LinearMap.smul_apply]
  rfl

/-- The tensor product `l2PiProductVector` of `L²` vectors, as a multilinear map. -/
def l2PiProductMultilinear : MultilinearMap ℂ (fun i => Lp ℂ 2 (μ i)) (Lp ℂ 2 (Measure.pi μ)) where
  toFun := l2PiProductVector μ
  map_update_add' u i a b := l2PiProductVector_update_add μ u i a b
  map_update_smul' u i c a := l2PiProductVector_update_smul μ u i c a

/-- The tensor product `l2PiProductVector` of `L²` vectors, as a continuous multilinear map of
norm at most `1`. -/
def l2PiProductContinuousMultilinear :
    ContinuousMultilinearMap ℂ (fun i => Lp ℂ 2 (μ i)) (Lp ℂ 2 (Measure.pi μ)) :=
  (l2PiProductMultilinear μ).mkContinuous 1 (fun u => by
    change ‖l2PiProductVector μ u‖ ≤ _
    rw [l2PiProductVector_norm]
    simp)
end
end GinibrePoincare
