/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorVariational
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Ginibre full generator energy

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreFullGenerator_complex_dissipative`, `ginibreFullGenerator_complex_poincare`.
-/

@[expose] public section

noncomputable section
namespace GinibrePoincare

/-- Every actual full complex graph element has real and imaginary ordinary
weak gradients, and its quadratic form is their exact summed energy. -/
theorem ginibreFullGenerator_complex_energy_identity {n : ℕ} (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hgraph : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    ∃ gr gi : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n (ginibreFullSymmetricRe n u).val gr ∧
      IsGinibreSymmetricWeakPair ((ginibreFullSymmetricRe n u).val, gr) ∧
      IsGinibreDistributionalGradient n (ginibreFullSymmetricIm n u).val gi ∧
      IsGinibreSymmetricWeakPair ((ginibreFullSymmetricIm n u).val, gi) ∧
      ginibreWeakEnergy n gr + ginibreWeakEnergy n gi = -(inner ℂ v u).re := by
  obtain ⟨hr, hi⟩ := (ginibreFullGenerator_graph_iff_real_imag hn u v).mp hgraph
  have hrg : (ginibreFullSymmetricOfReal n (ginibreFullSymmetricRe n u),
      ginibreFullSymmetricOfReal n (ginibreFullSymmetricRe n v)) ∈
      (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff, ← map_sub, ginibreFullComplexResolvent_ofReal, hr]
  have hig : (ginibreFullSymmetricOfReal n (ginibreFullSymmetricIm n u),
      ginibreFullSymmetricOfReal n (ginibreFullSymmetricIm n v)) ∈
      (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff, ← map_sub, ginibreFullComplexResolvent_ofReal, hi]
  obtain ⟨gr, hgr, hsr, her⟩ := ginibreFullGenerator_real_energy_identity hn _ _ hrg
  obtain ⟨gi, hgi, hsi, hei⟩ := ginibreFullGenerator_real_energy_identity hn _ _ hig
  refine ⟨gr, gi, hgr, hsr, hgi, hsi, ?_⟩
  have hinner := ginibreFullComplex_inner_re n v.val u.val
  rw [her, hei]
  change -(inner ℝ (ginibreFullComplexRe n v.val) (ginibreFullComplexRe n u.val)) +
    -(inner ℝ (ginibreFullComplexIm n v.val) (ginibreFullComplexIm n u.val)) =
      -(inner ℂ v.val u.val).re
  rw [hinner]
  ring

/-- Dissipativity on the entire actual symmetric generator domain. -/
theorem ginibreFullGenerator_complex_dissipative {n : ℕ} (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hgraph : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    (inner ℂ v u).re ≤ 0 := by
  obtain ⟨gr, gi, _, _, _, _, he⟩ := ginibreFullGenerator_complex_energy_identity hn u v hgraph
  have hr : 0 ≤ ginibreWeakEnergy n gr := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have hi : 0 ≤ ginibreWeakEnergy n gi := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-- The full complex generator quadratic form dominates twice the sum of the
real and imaginary centered variances throughout its exact graph domain. -/
theorem ginibreFullGenerator_complex_poincare {n : ℕ} (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hgraph : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    2 * (ginibreL2Variance n hn (ginibreFullSymmetricRe n u).val +
      ginibreL2Variance n hn (ginibreFullSymmetricIm n u).val) ≤ -(inner ℂ v u).re := by
  obtain ⟨gr, gi, hgr, hsr, hgi, hsi, he⟩ :=
    ginibreFullGenerator_complex_energy_identity hn u v hgraph
  have hr := ginibre_symmetric_weak_poincare hn _ gr hgr hsr
  have hi := ginibre_symmetric_weak_poincare hn _ gi hgi hsi
  linarith

end GinibrePoincare
