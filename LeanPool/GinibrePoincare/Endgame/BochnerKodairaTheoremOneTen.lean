/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/BochnerKodairaTheoremOneTen.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaInverseRoot
public import LeanPool.GinibrePoincare.Analysis.GinibreGeneratorDeficitAlgebra
public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneTen

/-! # Independent integrated Bochner–Kodaira proof of Theorem 1.10

The second derivative energy is obtained from the Gaussian commutator and
integration by parts, extended through finite polynomial jet approximation.
Neither the first Hermite deficit nor Theorem 1.9 is invoked. The weak-domain
first identity and generator-domain second identity have their actual domains.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The first differential deficit, independently obtained from the integrated
Bochner–Kodaira identity, for every genuine real symmetric weak pair. -/
theorem bochnerKodaira_ginibre_weak_first_deficit {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreWeakEnergy n g - 2*ginibreL2Variance n hn u =
      2*‖ginibreFullHolomorphicRemainder n hn u‖^2 +
        (4/(n : ℝ))*ginibreDifferentialSecondEnergy n hn g := by
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u g hu hs
  have hc := ginibreFullTransformedDbar_weak_coefficient hn
    (ginibreFullCenter n hn u) g huc hsc
  have hBK := bkInverseSquareRoot_total_energy hn (ginibreFullCenteredTransform n hn u)
    (ginibreFullTransformedDbar n hn · g) hc
  have hw : ‖ginibreFullCenteredTransform n hn u‖^2 = ginibreL2Variance n hn u := by
    unfold ginibreFullCenteredTransform
    rw [(normalizedVandermondeL2 n hn).norm_map, ginibreFullCenteredValue_norm_sq]
  rw [ginibreFullTransformedDbar_norm_sum hn g, hw,
    ginibreFullWeak_zero_mode_norm hn u g hu hs] at hBK
  change ginibreDifferentialSecondEnergy n hn g = _ at hBK
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hE : (4/(n : ℝ))*ginibreDifferentialSecondEnergy n hn g =
      ginibreWeakEnergy n g - 4*ginibreL2Variance n hn u +
        4*‖ginibreFullHolomorphicPart n hn u‖^2 := by
    rw [hBK]
    unfold ginibreWeakEnergy
    field_simp
    ring
  have hgeom := ginibreFullWeak_holomorphic_geometry hn u g hu hs
  rw [hE]
  nlinarith

/-- Both exact differential identities, with ordinary Schwartz first and second
Wirtinger derivatives and the actual projected inverse square root, on the full
real symmetric generator graph. This is the independent Section 6 route. -/
theorem bochnerKodairaTheoremOneTen {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      (∀ j, IsGaussianSchwartzDbar n (ginibreDifferentialDeficitVector n hn u.val)
        (ginibreDifferentialFirstDerivative n hn g j) j) ∧
      (∀ j k, IsGaussianSchwartzDbar n (ginibreDifferentialFirstDerivative n hn g j)
        (ginibreDifferentialSecondDerivative n hn g j k) k) ∧
      ginibreWeakEnergy n g - 2*ginibreL2Variance n hn u.val =
        2*‖ginibreFullHolomorphicRemainder n hn u.val‖^2 +
          (4/(n : ℝ))*ginibreDifferentialSecondEnergy n hn g ∧
      ‖v.val‖^2 - 2*ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖^2 +
          4*‖ginibreFullHolomorphicRemainder n hn u.val‖^2 +
          (8/(n : ℝ))*ginibreDifferentialSecondEnergy n hn g := by
  obtain ⟨g, hu, hs, hsecond⟩ := ginibreGenerator_second_deficit_algebra hn u v hgraph
  have hfirst := bochnerKodaira_ginibre_weak_first_deficit hn u.val g hu hs
  obtain ⟨hd, hdd⟩ := ginibreDifferentialDeficit_weak_derivatives hn u.val g hu hs
  refine ⟨g, hu, hs, fun j => (gaussianSchwartzDbar_iff_weak hn _ _ j).mpr (hd j),
    fun j k => (gaussianSchwartzDbar_iff_weak hn _ _ k).mpr (hdd j k), hfirst,?_⟩
  rw [hsecond, hfirst]
  ring

end
end GinibrePoincare
