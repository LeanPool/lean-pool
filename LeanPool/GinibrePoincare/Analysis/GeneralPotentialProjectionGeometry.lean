/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialProjectionGeometry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialProjectionPermutation
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondeCentered
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialLpConjugation

/-!
# General potential projection geometry

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialVandermondeCentered_alternating`, `potentialCenteredL2_star`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem potentialCenteredL2_permutation (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V))
    (hs : IsSymmetric f) (e : ParticlePermutation n) :
    potentialPermutationL2 n hV e (potentialCenteredL2 n hn hV hfin f hf) =
      potentialCenteredL2 n hn hV hfin f hf := by
  unfold potentialPermutationL2
  change Lp.compMeasurePreserving (permute e)
    (measurePreserving_permute_potentialMeasure n hV e) _ = _
  apply Lp.ext
  have hc := potentialCenteredL2_coeFn n hn hV hfin f hf
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (potentialCenteredL2 n hn hV hfin f hf)
    (measurePreserving_permute_potentialMeasure n hV e), hc,
    (measurePreserving_permute_potentialMeasure n hV e).quasiMeasurePreserving.ae_eq_comp hc]
    with z hp hz hq
  rw [hp, hq, hz]
  simp only [Function.comp_apply]
  rw [hs e z]

theorem potentialVandermondeCentered_alternating (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V))
    (hs : IsSymmetric f) (e : ParticlePermutation n) :
    volumePermutationL2 e
      (potentialVandermondeL2 n hn hV hfin (potentialCenteredL2 n hn hV hfin f hf)) =
      permutationSign e •
        potentialVandermondeL2 n hn hV hfin (potentialCenteredL2 n hn hV hfin f hf) := by
  rw [potentialVandermondeL2_intertwines hn hV hfin,
    potentialCenteredL2_permutation n hn hV hfin f hf hs e]

theorem potentialCenteredL2_star (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    star (potentialCenteredL2 n hn hV hfin f hf) = potentialCenteredL2 n hn hV hfin f hf := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (potentialCenteredL2 n hn hV hfin f hf),
    potentialCenteredL2_coeFn n hn hV hfin f hf] with z hs hz
  rw [hs]
  simp only [Pi.star_apply, hz]
  exact Complex.conj_ofReal _

end
end GinibrePoincare
