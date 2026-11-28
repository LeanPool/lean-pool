/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The bisection method

The **bisection method** looks for a solution of `f x = C` on a bracket
`[lo, hi]`: evaluate `f` at the midpoint, keep the half whose endpoints still
straddle `C`, repeat.

## Why bisection converges

Bisection only ever asks whether `f m < C`. So the hypothesis it needs is that
`σ` is the **threshold** of `f` against `C` on the bracket: `f x < C ↔ x < σ`
for `x ∈ [lo, hi]`. The estimates converge to that threshold. A strictly
increasing `f` with `f σ = C` has this property (`StrictMonoOn.lt_iff_lt`), and
then the limit is the solution. The property itself asks for neither continuity
nor strictness, and in general `σ` need not solve `f σ = C`.
At a threshold, a step maps the *trap* `[lo, σ] × [σ, hi]` (left
endpoint below `σ`, right endpoint above) into itself: the two branches of the
step are the two directions of the threshold equivalence. `Set.MapsTo.iterate`
then traps `σ` in every bracket. Separately, and whatever `f` is, each step
halves the width. A bracket of width `(hi − lo) / 2ⁿ` that contains `σ` puts
its midpoint within `(hi − lo) / 2ⁿ⁺¹` of it.

The iteration is a noncomputable definition over `ℝ`. Floating-point rounding
and stopping rules are out of scope.

## Main definitions

* `bisectStep`: one bisection step toward `f x = C` on a bracket: evaluate `f` at the midpoint and
  keep the half whose endpoints still straddle `C`.
* `bisect`: the `n`-th bisection bracket from `(a, b)`.
* `bisectMid`: the `n`-th bisection estimate, the midpoint of the `n`-th bracket.

## Main results

* `bisectStep`, `bisect`, `bisectMid`: one step, the `n`-th bracket, and the
  `n`-th estimate (the midpoint of the `n`-th bracket, counted from `n = 0`);
  `bisect_zero` and `bisect_succ` unfold the iteration.
* `bisectStep_snd_sub_fst`, `bisect_snd_sub_fst`: a step halves the bracket, so
  from any starting bracket `(a, b)` the `n`-th one has width `(b − a) / 2ⁿ`.
* `mapsTo_bisectStep`, `bisect_mem`: at a threshold `σ` the trap is invariant,
  so every bracket contains `σ`.
* `bisectMid_mem_Icc`: at a threshold `σ ∈ [lo, hi]`, every estimate lies in `[lo, hi]`.
* `abs_bisectMid_sub_le`, `tendsto_bisectMid`: the `n`-th estimate is within
  `(hi − lo) / 2ⁿ⁺¹` of `σ`, and the estimates converge to `σ`.

## Tags

bisection method, root finding, implied volatility solver, threshold, interval halving, JEL C63,
MSC 65M06
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- One **bisection step** toward `f x = C` on the bracket `I = (a, b)`: evaluate
`f` at the midpoint `m`, keep `(m, b)` if `f m < C` and `(a, m)` otherwise. -/
noncomputable def bisectStep (f : ℝ → ℝ) (C : ℝ) (I : ℝ × ℝ) : ℝ × ℝ :=
  let m := (I.1 + I.2) / 2
  if f m < C then (m, I.2) else (I.1, m)

/-- The `n`-th **bisection bracket** for `f x = C`, starting from `(a, b)`. -/
noncomputable def bisect (f : ℝ → ℝ) (C a b : ℝ) (n : ℕ) : ℝ × ℝ :=
  (bisectStep f C)^[n] (a, b)

/-- The **bisection estimate** after `n` steps: the midpoint of the `n`-th
bracket. At `n = 0` it is the midpoint of the starting bracket. -/
noncomputable def bisectMid (f : ℝ → ℝ) (C a b : ℝ) (n : ℕ) : ℝ :=
  ((bisect f C a b n).1 + (bisect f C a b n).2) / 2

@[simp] lemma bisect_zero (f : ℝ → ℝ) (C a b : ℝ) : bisect f C a b 0 = (a, b) := rfl

lemma bisect_succ (f : ℝ → ℝ) (C a b : ℝ) (n : ℕ) :
    bisect f C a b (n + 1) = bisectStep f C (bisect f C a b n) :=
  Function.iterate_succ_apply' _ _ _

/-- A bisection step halves the bracket, whatever `f` and `C` are. -/
lemma bisectStep_snd_sub_fst (f : ℝ → ℝ) (C : ℝ) (I : ℝ × ℝ) :
    (bisectStep f C I).2 - (bisectStep f C I).1 = (I.2 - I.1) / 2 := by
  simp only [bisectStep]
  split_ifs <;> ring

/-- **Halving**: the `n`-th bracket has width `(b − a) / 2ⁿ`, whatever `f` and
`C` are. -/
theorem bisect_snd_sub_fst (f : ℝ → ℝ) (C a b : ℝ) (n : ℕ) :
    (bisect f C a b n).2 - (bisect f C a b n).1 = (b - a) / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [bisect_succ, bisectStep_snd_sub_fst, ih, pow_succ, div_div]

variable {f : ℝ → ℝ} {C lo hi σ : ℝ}

/-- **The trap is invariant.** If `σ` is the threshold of `f` against `C` on
`[lo, hi]`, a bisection step keeps the left endpoint in `[lo, σ]` and the right
endpoint in `[σ, hi]`: at the midpoint `m`, `f m < C` means `m < σ`, and
otherwise `σ ≤ m`. -/
theorem mapsTo_bisectStep (hC : ∀ x ∈ Set.Icc lo hi, f x < C ↔ x < σ) :
    Set.MapsTo (bisectStep f C) (Set.Icc lo σ ×ˢ Set.Icc σ hi)
      (Set.Icc lo σ ×ˢ Set.Icc σ hi) := by
  rintro ⟨a, b⟩ ⟨⟨hla, haσ⟩, hσb, hbh⟩
  have hm : (a + b) / 2 ∈ Set.Icc lo hi := ⟨by linarith, by linarith⟩
  simp only [bisectStep]
  split_ifs with h
  · exact ⟨⟨hm.1, ((hC _ hm).1 h).le⟩, hσb, hbh⟩
  · exact ⟨⟨hla, haσ⟩, not_lt.1 ((hC _ hm).not.1 h), hm.2⟩

/-- **Every bisection bracket traps the threshold**: the `n`-th bracket
`(aₙ, bₙ)` from `(lo, hi)` has `aₙ ∈ [lo, σ]` and `bₙ ∈ [σ, hi]`. -/
theorem bisect_mem (hC : ∀ x ∈ Set.Icc lo hi, f x < C ↔ x < σ) (hσ : σ ∈ Set.Icc lo hi)
    (n : ℕ) : bisect f C lo hi n ∈ Set.Icc lo σ ×ˢ Set.Icc σ hi :=
  (mapsTo_bisectStep hC).iterate n ⟨⟨le_rfl, hσ.1⟩, hσ.2, le_rfl⟩

/-- **Error bound**: the `n`-th estimate is within `(hi − lo) / 2ⁿ⁺¹` of the
threshold, half the width of a bracket that contains both. -/
theorem abs_bisectMid_sub_le (hC : ∀ x ∈ Set.Icc lo hi, f x < C ↔ x < σ)
    (hσ : σ ∈ Set.Icc lo hi) (n : ℕ) :
    |bisectMid f C lo hi n - σ| ≤ (hi - lo) / 2 ^ (n + 1) := by
  obtain ⟨⟨-, ha⟩, hb, -⟩ := bisect_mem hC hσ n
  rw [pow_succ, ← div_div, ← bisect_snd_sub_fst f C, bisectMid, abs_sub_le_iff]
  constructor <;> linarith

/-- **The estimate stays in the bracket**: the `n`-th bisection estimate lies
in `[lo, hi]`, since it is the midpoint of a sub-bracket of `[lo, hi]`. -/
theorem bisectMid_mem_Icc (hC : ∀ x ∈ Set.Icc lo hi, f x < C ↔ x < σ) (hσ : σ ∈ Set.Icc lo hi)
    (n : ℕ) : bisectMid f C lo hi n ∈ Set.Icc lo hi := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := bisect_mem hC hσ n
  constructor <;> simp only [bisectMid] <;> linarith

/-- **Convergence**: the bisection estimates converge to the threshold. -/
theorem tendsto_bisectMid (hC : ∀ x ∈ Set.Icc lo hi, f x < C ↔ x < σ)
    (hσ : σ ∈ Set.Icc lo hi) : Tendsto (bisectMid f C lo hi) atTop (𝓝 σ) :=
  tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun _ ↦ dist_nonneg)
    (abs_bisectMid_sub_le hC hσ) <| tendsto_const_nhds.div_atTop <|
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1)

end MathFin
