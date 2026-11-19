/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSlaterPoincare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterLowering
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakDeficit

/-!
# Alternative Slater Poincare

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `slater_ginibre_symmetric_weak_poincare`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory ComplexHermite
open scoped BigOperators

/-- Every full-domain symmetric real weak pair has an alternating centered
Vandermonde transform. -/
theorem slater_centered_transform_alternating {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreFullCenteredTransform n hn u ∈ gaussianAlternatingL2 n := by
  obtain ⟨hc, hsc⟩ := ginibreFullCenter_weak_pair hn u g hu hs
  let r : ginibreFullSymmetricValues n :=
    ⟨ginibreFullCenter n hn u, fun σ => (hsc σ).1⟩
  let c : ginibreSymmetricL2 n := ginibreFullSymmetricOfReal n r
  exact (vandermondeSymmetricAlternatingEquiv n hn c).property

/-- Exact derivative energy (4.4) in the determinant expansion, on the full
ordinary weak-H¹ domain. The summation groups Slater orbitals by their total
antiholomorphic degree. -/
theorem slater_ginibre_weak_energy {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    HasSum (fun k : ℕ => (k + 1) *
      slaterDegreeMass hn (ginibreFullCenteredTransform n hn u) (k + 1))
      (ginibreWeakEnergy n g / 4) := by
  have hw := slater_centered_transform_alternating hn u g hu hs
  simp_rw [slaterDegreeMass_eq_mode_norm hn _ hw]
  exact ginibreFullWeak_weighted_hermite_energy hn u g hu hs

/-- Parseval (4.3), grouped by antiholomorphic Slater degree, for the actual
centered weak-domain transform. -/
theorem slater_ginibre_weak_parseval {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    HasSum (fun d => slaterDegreeMass hn (ginibreFullCenteredTransform n hn u) d)
      (ginibreL2Variance n hn u) := by
  have hw := slater_centered_transform_alternating hn u g hu hs
  simp_rw [slaterDegreeMass_eq_mode_norm hn _ hw]
  have he := hasSum_norm_sq_gaussianHermiteMode hn (ginibreFullCenteredTransform n hn u)
  unfold ginibreFullCenteredTransform at he
  rw [(normalizedVandermondeL2 n hn).norm_map, ginibreFullCenteredValue_norm_sq] at he
  exact he

/-- The all-holomorphic Slater determinant component has at most half the
centered real mass, including at the ordinary weak-domain limit. -/
theorem slater_ginibre_zero_degree_half_mass {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    2 * slaterDegreeMass hn (ginibreFullCenteredTransform n hn u) 0 ≤
      ginibreL2Variance n hn u := by
  rw [slaterDegreeMass_eq_mode_norm hn _ (slater_centered_transform_alternating hn u g hu hs),
    ginibreFullWeak_zero_mode_norm hn u g hu hs, ginibreFullWeak_holomorphic_geometry hn u g hu hs]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Section 4's independent determinant-expansion proof of Theorem 1.1.
It uses only Slater Parseval, the exact derivative energy, the integer bound
`q ≥ 1` on positive Slater degrees, and the holomorphic mass estimate. -/
theorem slater_ginibre_symmetric_weak_poincare {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreL2Variance n hn u ≤ ginibreWeakEnergy n g / 2 := by
  let m : ℕ → ℝ := slaterDegreeMass hn (ginibreFullCenteredTransform n hn u)
  have hm (d : ℕ) : 0 ≤ m d := by
    change 0 ≤ slaterDegreeMass hn (ginibreFullCenteredTransform n hn u) d
    unfold slaterDegreeMass
    exact tsum_nonneg (fun _ => div_nonneg (sq_nonneg _) (le_of_lt (slaterMultiplicity_pos n)))
  have he := slater_ginibre_weak_energy hn u g hu hs
  have hp := slater_ginibre_weak_parseval hn u g hu hs
  have htail : HasSum (fun k => m (k + 1)) (ginibreL2Variance n hn u - m 0) := by
    simpa [m] using (hasSum_nat_add_iff' 1).2 hp
  have hbound : (∑' k, m (k + 1)) ≤ ∑' k : ℕ, (k + 1) * m (k + 1) := by
    apply Summable.tsum_le_tsum _ htail.summable he.summable
    intro k
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    nlinarith [hm (k + 1)]
  rw [htail.tsum_eq, he.tsum_eq] at hbound
  have hzero := slater_ginibre_zero_degree_half_mass hn u g hu hs
  change 2 * m 0 ≤ ginibreL2Variance n hn u at hzero
  linarith

end
end GinibrePoincare

