/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Defs

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for scale arrays — definitions and constants

This module formalizes the setup of Proposition `p.concentration.for.scales`
(ABK26, Appendix D): a concentration inequality for exceedance counts in a
triangular array `{X_{k,j}}` with geometric weights within rows and column-wise
`r`-dependence.

We work over an abstract probability space `(Ω, P)` with a nonnegative array
`X : ℤ → ℤ → Ω → ℝ`.  This file collects:

* the geometric weights `wt s k j = 3^{-s|k-j|}` and the weighted row sums
  `Yk` (the paper's `Y_k`, `e.Yk.def.twosided`);
* the exceedance thresholds `thr` and the column exceedance counts `Zcount`
  (the paper's `Z_j`, `e.Zj.def.twosided`);
* the universal constants `C₂`, `C₃`, and the exponential-moment rate `mgfRate`
  (`a = ⅛ (log 3) s p`);
* the positivity facts `one_sub_rpow_pos`, `C₂_pos`, `C₃_pos` and
  `mgfRate_pos` those constants need.  The geometric row-sum bound that Step 1
  uses is `Reduction.sum_wt_half_le`, one module on.

## Design of the independence hypothesis

The paper assumes `r`-dependence across columns
(`e.independent.columns.twosided`): for `I, J ⊆ ℤ` with `dist(I,J) ≥ r`, the
families `{X_{·,j} : j ∈ I}` and `{X_{·,j} : j ∈ J}` are independent.  What the
proof actually uses (Step 4) is the mutual independence, *within each residue
class* `b` modulo `r`, of the columns `{X_{·, jr+b} : j ∈ ℤ}` — these columns
are pairwise at distance `≥ r`, and `{i}` is at distance `≥ r` from
`{i', i'', …}` for any earlier members, so the paper's two-set hypothesis
yields mutual independence by induction.  We therefore take as the hypothesis
the mutual independence of each residue class, phrased with mathlib's
`iIndepFun` over the whole columns viewed as `(ℤ → ℝ)`-valued random variables:
  `∀ b : ℤ, iIndepFun (fun j : ℤ => fun ω k => X k (j * r + b) ω) P`.

This is the weakest faithful hypothesis mathlib's independence A supports
cleanly; it is implied by `e.independent.columns.twosided`.  Since `Zcount j`
is a measurable function of column `j` alone, `iIndepFun.comp` transports this
to independence of the `Z`'s within each residue class.
-/

namespace Algsuperdiff.Section4.Probability.ScalesConcentration

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

/-- Real distance between integer indices, `|k - j|`. -/
noncomputable def idist (k j : ℤ) : ℝ := |(k : ℝ) - (j : ℝ)|

/-- Geometric row weight `3^{-s|k-j|}` (`e.Yk.def.twosided`). -/
noncomputable def wt (s : ℝ) (k j : ℤ) : ℝ := (3 : ℝ) ^ (-(s * idist k j))

lemma wt_pos (s : ℝ) (k j : ℤ) : 0 < wt s k j :=
  Real.rpow_pos_of_pos (by norm_num) _

lemma wt_nonneg (s : ℝ) (k j : ℤ) : 0 ≤ wt s k j := (wt_pos s k j).le

/-- The weighted row sum `Y_k = ∑_j 3^{-s|k-j|} X_{k,j}` (`e.Yk.def.twosided`). -/
noncomputable def Yk {Ω : Type*} (X : ℤ → ℤ → Ω → ℝ) (s : ℝ) (k : ℤ) (ω : Ω) : ℝ :=
  ∑' j : ℤ, wt s k j * X k j ω

/-- The Step-1/Step-2 exceedance threshold `½ λ 3^{(s/2)|k-j|}`. -/
noncomputable def thr (s lam : ℝ) (k j : ℤ) : ℝ :=
  (lam / 2) * (3 : ℝ) ^ ((s / 2) * idist k j)

open Classical in
/-- The column exceedance count
`Z_j = ∑_{k=0}^{m} 𝟙{X_{k,j} > ½ λ 3^{(s/2)|k-j|}}` (`e.Zj.def.twosided`),
as a natural number. -/
noncomputable def Zcount {Ω : Type*} (X : ℤ → ℤ → Ω → ℝ) (s lam : ℝ) (m : ℕ)
    (j : ℤ) (ω : Ω) : ℕ :=
  ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), if thr s lam k j < X k j ω then 1 else 0

/-! ### Universal constants -/

/-- `C₂ = 4 / (1 - 3^{-1/2})` from Step 2 (`e.Zj.tail.twosided`). -/
noncomputable def C₂ : ℝ := 4 / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))

/-- `C₃ = 2 (1 - 3^{-1/8})⁻¹ C₂` from Step 3 (`e.Zj.mgf.twosided`). -/
noncomputable def C₃ : ℝ := 2 * (1 - (3 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹ * C₂

/-- The exponential-moment rate `a = ⅛ (log 3) s p` from Step 3. -/
noncomputable def mgfRate (s p : ℝ) : ℝ := (1 / 8) * Real.log 3 * s * p

lemma one_sub_rpow_pos {c : ℝ} (hc : 0 < c) : 0 < 1 - (3 : ℝ) ^ (-c) := by
  have h1 : (3 : ℝ) ^ (-c) < 1 := by
    rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith)
  linarith

lemma C₂_pos : 0 < C₂ := by
  unfold C₂
  exact div_pos (by norm_num) (one_sub_rpow_pos (by norm_num))

lemma C₃_pos : 0 < C₃ := by
  unfold C₃
  refine mul_pos (mul_pos (by norm_num) (inv_pos.2 (one_sub_rpow_pos (by norm_num)))) C₂_pos

lemma mgfRate_pos {s p : ℝ} (hs : 0 < s) (hp : 0 < p) : 0 < mgfRate s p := by
  unfold mgfRate
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  positivity

end Algsuperdiff.Section4.Probability.ScalesConcentration
