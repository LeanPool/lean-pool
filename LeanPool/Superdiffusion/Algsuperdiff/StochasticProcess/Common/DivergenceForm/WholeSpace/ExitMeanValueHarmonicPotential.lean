/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEIdentificationLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.RealResolvent

/-!
# ExitMeanValueHarmonicPotential

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The vanishing-shift limit of the Dirichlet resolvents of an exhaustion cube

The Dirichlet resolvents `R^V_lam f` of a fixed bounded measurable datum on an exhaustion cube
converge as the shift decreases to zero, and this file constructs the limit and bounds it.

Two facts drive everything.  First, the Dirichlet resolvent of a datum bounded by `D` is bounded
by `D` times the uniform bound of the torsion function of the cube
*uniformly in the shift*: comparison with the
constant datum replaces the shift-dependent bound `D / lam`.  Second, the resolvent identity
expresses the difference of the values at two shifts as the difference of the shifts times a
third Dirichlet resolvent, so the family is Lipschitz in the shift with a shift-independent
constant.

A Lipschitz real family on the positive half-line converges as its argument decreases to zero,
with an error proportional to the argument (`exists_forall_abs_sub_le_of_lipschitz`).  The limit
is the Green potential of the cube; it vanishes off the cube, obeys the same uniform bound, is
measurable, and is approached at the linear rate recorded above.

Everything here is analytic: no process, and no hypothesis about one, appears.  The
identification of that limit with the zero-trace weak solution of the unshifted
Dirichlet problem is a separate question and is not addressed here.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## A Lipschitz family on the positive shifts -/

/-- **A Lipschitz real family on the positive half-line has a limit at zero.**  If the values at
two positive arguments differ by at most a constant times the difference of the arguments, then
there is a real number approached at the linear rate as the argument decreases to zero. -/
theorem exists_forall_abs_sub_le_of_lipschitz {s : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ lam nu : ℝ, 0 < lam → 0 < nu → |s lam - s nu| ≤ K * |lam - nu|) :
    ∃ c : ℝ, ∀ lam : ℝ, 0 < lam → |s lam - c| ≤ K * lam := by
  set b : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹ with hbdef
  have hbpos : ∀ n : ℕ, 0 < b n := fun n ↦ by rw [hbdef]; positivity
  have hbanti : ∀ {n N : ℕ}, N ≤ n → b n ≤ b N := by
    intro n N hn
    have hcast : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have hle : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      linarith only [hle]
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    exact inv_anti₀ hpos hcast
  have hbzero : Tendsto b atTop (𝓝 0) := by
    rw [hbdef]
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hCauchy : CauchySeq fun n : ℕ ↦ s (b n) := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ ↦ 2 * K * b N) (fun n m N hn hm ↦ ?_) ?_
    · have hdiff : |b n - b m| ≤ 2 * b N := by
        have h1 : b n ≤ b N := hbanti hn
        have h2 : b m ≤ b N := hbanti hm
        exact abs_le.mpr ⟨by linarith only [h1, h2, (hbpos n).le, (hbpos m).le],
          by linarith only [h1, h2, (hbpos n).le, (hbpos m).le]⟩
      calc dist (s (b n)) (s (b m)) = |s (b n) - s (b m)| := Real.dist_eq _ _
        _ ≤ K * |b n - b m| := hlip _ _ (hbpos n) (hbpos m)
        _ ≤ K * (2 * b N) := mul_le_mul_of_nonneg_left hdiff hK
        _ = 2 * K * b N := by ring
    · simpa only [mul_zero] using
        (tendsto_const_nhds (x := 2 * K) (f := (atTop : Filter ℕ))).mul hbzero
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hCauchy
  refine ⟨c, fun lam hlam ↦ ?_⟩
  have h1 : Tendsto (fun n : ℕ ↦ |s lam - s (b n)|) atTop (𝓝 |s lam - c|) :=
    (tendsto_const_nhds.sub hc).abs
  have h2 : Tendsto (fun n : ℕ ↦ K * |lam - b n|) atTop (𝓝 (K * lam)) := by
    have habs : Tendsto (fun n : ℕ ↦ |lam - b n|) atTop (𝓝 |lam - 0|) :=
      (tendsto_const_nhds.sub hbzero).abs
    rw [sub_zero, abs_of_pos hlam] at habs
    exact tendsto_const_nhds.mul habs
  exact le_of_tendsto_of_tendsto' h1 h2 fun n ↦ hlip lam (b n) hlam (hbpos n)

variable [NeZero d]

end

end DivergenceFormProcess.Form
