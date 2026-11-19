/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianSublevelPathExhaustion.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUReferenceSublevelStopped
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCompactPathWeight

/-!
# Ginibre Hamiltonian sublevel path exhaustion

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreHamiltonian_compact_sublevel_survival_reverse`,
`ginibreHamiltonian_compact_path_survival_exhaustion_iff`.
-/

@[expose] public section

open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Every continuous collision-free path on a compact horizon survives some
Hamiltonian sublevel. The bound is derived from the actual path. -/
theorem ginibreHamiltonian_compact_path_sublevel_exhaustion
    {n : ℕ} (T : ℝ) (x : C(Icc (0 : ℝ) T, Configuration n))
    (hCF : ∀ t, CollisionFree (x t)) :
    ∃ R : ℝ, ∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n R := by
  have hH : Continuous (fun t => ginibreHamiltonian n (x t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (ginibreHamiltonian_contDiffAt n (x t) (hCF t)).continuousAt.comp
        x.continuous.continuousAt
  have hK := isCompact_range hH
  obtain ⟨R, hR, hBound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R+1, fun t => ?_⟩
  change Real.exp (-(R+1)) < ginibreWeight n (x t)
  rw [← ginibreHamiltonian_exp_neg (x t) (hCF t)]
  apply Real.exp_lt_exp.mpr
  have hb := hBound (ginibreHamiltonian n (x t)) (mem_range_self t)
  have hh := le_trans (le_abs_self (ginibreHamiltonian n (x t))) hb
  linarith

/-- Hamiltonian survival depends only on the range of the path and is
unchanged by compact-horizon time reversal. -/
theorem ginibreHamiltonian_compact_sublevel_survival_reverse
    {n : ℕ} (T : ℝ) (hT : 0 ≤ T) (R : ℝ)
    (x : C(Icc (0 : ℝ) T, Configuration n)) :
    (∀ t, (x.comp (ginibreHamiltonianCompactReverseTime T hT)) t ∈
      ginibreHamiltonianOUSublevelDomain n R) ↔
    (∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n R) := by
  constructor
  · intro h t
    have hh := h ((ginibreHamiltonianCompactReverseTime T hT) t)
    have he : (ginibreHamiltonianCompactReverseTime T hT)
        ((ginibreHamiltonianCompactReverseTime T hT) t) = t := by
      apply Subtype.ext
      change T - (T - t.val) = t.val
      ring
    simpa only [ContinuousMap.comp_apply, he] using hh
  · intro h t
    exact h ((ginibreHamiltonianCompactReverseTime T hT) t)

theorem ginibreHamiltonian_compact_path_natural_sublevel_exhaustion
    {n : ℕ} (T : ℝ) (x : C(Icc (0 : ℝ) T, Configuration n))
    (hCF : ∀ t, CollisionFree (x t)) :
    ∃ k : ℕ, ∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n (k : ℝ) := by
  obtain ⟨R, hR⟩ := ginibreHamiltonian_compact_path_sublevel_exhaustion T x hCF
  obtain ⟨k, hk⟩ := exists_nat_gt R
  refine ⟨k, fun t => ?_⟩
  have hh := hR t
  change Real.exp (-R) < ginibreWeight n (x t) at hh
  change Real.exp (-(k : ℝ)) < ginibreWeight n (x t)
  exact lt_trans (Real.exp_lt_exp.mpr (neg_lt_neg hk)) hh

theorem ginibreHamiltonian_compact_path_survival_exhaustion_iff
    {n : ℕ} (T : ℝ) (x : C(Icc (0 : ℝ) T, Configuration n)) :
    (∃ k : ℕ, ∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n (k : ℝ)) ↔
      (∀ t, CollisionFree (x t)) := by
  constructor
  · rintro ⟨k, hk⟩ t
    have hh := hk t
    have hMem : x t ∈ ginibreHamiltonianSublevel n k := by
      rw [ginibreHamiltonianSublevel_eq_weight_superlevel]
      exact (show Real.exp (-(k : ℝ)) < ginibreWeight n (x t) from hh).le
    exact hMem.1
  · exact ginibreHamiltonian_compact_path_natural_sublevel_exhaustion T x

end
end GinibrePoincare
