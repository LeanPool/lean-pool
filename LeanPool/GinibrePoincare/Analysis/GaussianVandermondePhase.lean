/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianVandermondePhase.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianHermitePhase
public import LeanPool.GinibrePoincare.Analysis.VandermondeL2

/-! # Exact phase intertwining of the actual Vandermonde isometry -/


@[expose] public section


open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The Vandermonde isometry shifts every actual phase character by its
holomorphic degree. -/
theorem gaussianGlobalPhaseL2_normalizedVandermonde {n : ℕ} (hn : 0 < n)
    (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (ginibreMeasure n)) :
    gaussianGlobalPhaseL2 hn u hu (normalizedVandermondeL2 n hn x) =
      u ^ vandermondeDegree n •
        normalizedVandermondeL2 n hn (ginibreGlobalPhaseL2 hn u hu x) := by
  apply Lp.ext
  have hsrc := (measurePreserving_globalPhase_complexGaussianMeasure hn u
    hu).quasiMeasurePreserving.ae_eq_comp (normalizedVandermondeL2_coeFn_public n hn x)
  have hcomp := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq
      (Lp.coeFn_compMeasurePreserving x (measurePreserving_globalPhase_ginibreMeasure hn u hu))
  filter_upwards [Lp.coeFn_compMeasurePreserving (normalizedVandermondeL2 n hn x)
      (measurePreserving_globalPhase_complexGaussianMeasure hn u hu), hsrc,
    Lp.coeFn_smul (u ^ vandermondeDegree n)
      (normalizedVandermondeL2 n hn (ginibreGlobalPhaseL2 hn u hu x)),
    normalizedVandermondeL2_coeFn_public n hn (ginibreGlobalPhaseL2 hn u hu x),
    hcomp] with z hleft hsource hright htarget hx
  change (gaussianGlobalPhaseL2 hn u hu (normalizedVandermondeL2 n hn x)) z =
    (normalizedVandermondeL2 n hn x) (globalPhase u z) at hleft
  rw [hleft, hright]
  change (normalizedVandermondeL2 n hn x) (globalPhase u z) =
    (u ^ vandermondeDegree n) * (normalizedVandermondeL2 n hn (ginibreGlobalPhaseL2 hn u hu x)) z
  change (normalizedVandermondeL2 n hn x) (globalPhase u z) =
    normalizedVandermondeMultiplier n (globalPhase u z) * x (globalPhase u z) at hsource
  change (ginibreGlobalPhaseL2 hn u hu x) z = x (globalPhase u z) at hx
  rw [hsource, htarget, hx]
  unfold normalizedVandermondeMultiplier
  rw [vandermonde_globalPhase, ← vandermondeDegree_eq_sum_Ioi_card]
  ring

/-- Exact transformed character of an arbitrary actual Ginibre phase eigenvector. -/
theorem gaussianGlobalPhaseL2_normalizedVandermonde_character {n r s : ℕ} (hn : 0 < n)
    (x : Lp ℂ 2 (ginibreMeasure n))
    (hx : ∀ (u : ℂ) (hu : ‖u‖ = 1), ginibreGlobalPhaseL2 hn u hu x =
      (u ^ r * (conj u) ^ s) • x) :
    ∀ (u : ℂ) (hu : ‖u‖ = 1),
      gaussianGlobalPhaseL2 hn u hu (normalizedVandermondeL2 n hn x) =
        (u ^ (vandermondeDegree n + r) * (conj u) ^ s) •
          normalizedVandermondeL2 n hn x := by
  intro u hu
  rw [gaussianGlobalPhaseL2_normalizedVandermonde, hx u hu, map_smul, smul_smul]
  rw [pow_add, mul_assoc]

end
end GinibrePoincare
