/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.BaseCase
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionStep
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Induction.StateCalculus

/-!
# InductionState

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The all-scales induction state `𝒮(m, C c⋆⁻¹)`

Section 4 consumes the Section 3 induction state `𝒮(m₀, E)` as a *premise* at
half a dozen call sites: `p.cg.ellipticity.bounds` and `e.shom.m.vs.shom.n`
both carry `𝒮(m₀−1, E)` together with a budget gate `E ≥ C c⋆⁻¹` and a regime
`γ ≤ E⁻¹¹⁰`, and §4.1 applies them at arbitrary scales without ever exhibiting
the state.  The manuscript's discharge is the last two lines of the proof of
`p.induction.bounds`:

> According to Proposition `p.base.case`, there exists `C(d) < ∞` such that
> `𝒮(m**, C c⋆^{−1/2})` is valid.  By induction, we deduce the existence of
> `C(d) < ∞` such that `𝒮(m, C c⋆⁻¹)` is valid for every `m ∈ ℤ`.

This module renders those two lines over the Section 3 surface.

## The `c⋆^{−1/2}` to `c⋆⁻¹` reconciliation

Both halves are proved in this repository, so **the gap is closed here, not
assumed**:

* `Algsuperdiff.Section3.Provider.Induction.inductionState_mono_E` — the frozen
  state is monotone in `E` (both `E`-occurrences of the frozen definition are
  increasing in `E`); and

Together they give `Cstart c⋆^{−1/2} ≤ C c⋆⁻¹` as soon as `C ≥ Cstart √(3/2)` —
the proved `Algsuperdiff.Section3.Provider.Induction.startBudget_le_of_sqrt`.

## What is consumed

* the proved state calculus of `Section3/Provider/Induction/StateCalculus.lean`
  (`inductionState_mono_E`, `inductionState_of_base_of_step_of_E_le`,
  `startBudget_le_of_sqrt`) and `cstar_le_three_halves`.

`Algsuperdiff.Frozen.Section3.induction_bounds` is *not* consumed: its proof
builds exactly this state internally (`InductionBoundsAssembly.lean`) but does
not export it, and its own conclusion does not carry the state.  The assembly
here therefore repeats the constant bookkeeping rather than importing a
`private` helper or editing Section 3.

## References

* ABK26, `d.mathcalS.def`; `p.base.case`; `p.induction.bounds` proof, the
  terminal budget.
-/

namespace Algsuperdiff.Section4.Provider.GoodEvents

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant bookkeeping

`K` is fixed before every model datum: above `6`, above the caller's threshold,
above the base case's `Cstart √(3/2)`, and above the induction step's own
constant. -/

/-- A single real above `6`, above a requested threshold, and above two further
given reals. -/
private theorem exists_budgetConst (a b c : ℝ) :
    ∃ K : ℝ, 6 ≤ K ∧ a ≤ K ∧ b ≤ K ∧ c ≤ K :=
  ⟨max (max 6 a) (max b c),
    le_trans (le_max_left 6 a) (le_max_left _ _),
    le_trans (le_max_right 6 a) (le_max_left _ _),
    le_trans (le_max_left b c) (le_max_right _ _),
    le_trans (le_max_right b c) (le_max_right _ _)⟩

/-- **The terminal budget is admissible.**  `1 ≤ K c⋆⁻¹` from `6 ≤ K` and the
proved `c⋆ ≤ 3/2`: the budget is at least `6 · (3/2)⁻¹ = 4`. -/
private theorem one_le_budget {K cst : ℝ} (hK : 6 ≤ K) (hcs0 : 0 < cst)
    (hcs : cst ≤ 3 / 2) : (1 : ℝ) ≤ K * cst⁻¹ := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK
  have ha : (6 : ℝ) * (3 / 2 : ℝ)⁻¹ ≤ K * (3 / 2 : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hK (by norm_num)
  have hb : K * (3 / 2 : ℝ)⁻¹ ≤ K * cst⁻¹ :=
    mul_le_mul_of_nonneg_left (inv_anti₀ hcs0 hcs) hK0.le
  have hnum : (4 : ℝ) = 6 * (3 / 2 : ℝ)⁻¹ := by norm_num
  linarith only [ha, hb, hnum]

/-- The regime `γ ≤ C⁻¹¹⁰ c⋆¹⁰` is exactly `γ ≤ (E⁻¹)¹⁰` at the terminal budget
`E = C c⋆⁻¹`.  No tenth power is ever expanded. -/
private theorem inv_budget_pow_ten {K cst : ℝ} :
    ((K * cst⁻¹)⁻¹) ^ 10 = (K⁻¹) ^ 10 * cst ^ 10 := by
  rw [mul_inv, inv_inv, mul_pow]

/-! ## 2. The all-scales state -/

/-- **The all-scales induction state, with a caller-prescribed constant floor.**

For every requested threshold `C₀` there is a `C ≥ max 6 C₀`, depending only on
the dimension and on `C₀`, such that every model in the printed regime
`γ ≤ C⁻¹¹⁰ c⋆¹⁰` admits the budget `E = C c⋆⁻¹`, and `𝒮(m, E)` holds at
*every* integer scale.  The returned bundle also carries the three `E`-side
facts the Section 4 call sites need (see §3).

The `C₀` slot is what makes the result usable: a downstream node with its own
constant `C'` gets `C' c⋆⁻¹ ≤ E` from `mul_cstarInv_le_of_budget` by requesting
`C₀ := C'`. -/
theorem exists_allScalesInductionState_ge (d : ℕ) (C₀ : ℝ) :
    ∃ C : ℝ, 6 ≤ C ∧ C₀ ≤ C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E},
          (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
            M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 ∧
              ∀ m : ℤ, Algsuperdiff.Frozen.Section3.inductionState M m E := by
  obtain ⟨_C0, Cstart, _hC00, hCstart0, hbase⟩ :=
    Algsuperdiff.Frozen.Section3.base_case d
  obtain ⟨Cstep, _hCstep0, hstep⟩ := Algsuperdiff.Frozen.Section3.induction_step d
  obtain ⟨K, hK6, hK0le, hKstart, hKstep⟩ :=
    exists_budgetConst C₀ (Cstart * Real.sqrt (3 / 2)) Cstep
  refine ⟨K, hK6, hK0le, ?_⟩
  intro M hreg
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hcsinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := (inv_pos.mpr hcs0).le
  refine ⟨⟨K * (Disorder.cstar M)⁻¹, one_le_budget hK6 hcs0 hcs⟩, rfl, ?_, ?_⟩
  · change M.gamma ≤ ((K * (Disorder.cstar M)⁻¹)⁻¹) ^ 10
    rw [inv_budget_pow_ten]
    exact hreg
  · have hgammaE : M.gamma ≤ (((K * (Disorder.cstar M)⁻¹) : ℝ)⁻¹) ^ 10 := by
      rw [inv_budget_pow_ten]
      exact hreg
    have hstepGate :
        Cstep * (Disorder.cstar M)⁻¹ ≤ K * (Disorder.cstar M)⁻¹ :=
      mul_le_mul_of_nonneg_right hKstep hcsinv
    obtain ⟨-, -, -, Estart, hEstartVal, hEstartState⟩ := hbase M
    have hbridge : (Estart : ℝ) ≤ K * (Disorder.cstar M)⁻¹ := by
      rw [hEstartVal]
      exact Algsuperdiff.Section3.Provider.Induction.startBudget_le_of_sqrt hcs0 hcs
        hCstart0.le hKstart
    exact
      Algsuperdiff.Section3.Provider.Induction.inductionState_of_base_of_step_of_E_le
        hEstartState hbridge
        fun n hn => hstep M n _ hstepGate hgammaE hn

/-- **The all-scales induction state** in the shape printed: there is a `C(d)` such
that `𝒮(m, C c⋆⁻¹)` is valid for every `m ∈ ℤ`. -/
theorem exists_allScalesInductionState (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E},
          (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
            ∀ m : ℤ, Algsuperdiff.Frozen.Section3.inductionState M m E := by
  obtain ⟨C, hC6, -, hC⟩ := exists_allScalesInductionState_ge d 0
  refine ⟨C, lt_of_lt_of_le (by norm_num) hC6, ?_⟩
  intro M hreg
  obtain ⟨E, hEval, -, hall⟩ := hC M hreg
  exact ⟨E, hEval, hall⟩

/-! ## 3. The `E`-window consumption A

The Section 4 call sites do not consume `𝒮` alone: `p.cg.ellipticity.bounds`
(as `Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds`) asks for `max
(exp (Ccg/σ)) c⋆⁻¹ ≤ E` and `E ≤ γ^{−1/5}` on top of the state, and
`e.shom.m.vs.shom.n` asks for `C' c⋆⁻¹ ≤ E` and `γ ≤ E⁻¹¹⁰`.  Each of the
budget-side facts is discharged from the budget identity `(E : ℝ) = C c⋆⁻¹`. -/

/-- **Any constant below the budget constant clears the budget gate.**  This is the
premise `E ≥ C' c⋆⁻¹` of `e.shom.m.vs.shom.n` and of the `induction_step`, at a
downstream node's own constant `C'`. -/
theorem mul_cstarInv_le_of_budget (M : ABKModel d) {C C' : ℝ}
    {E : {E : ℝ // 1 ≤ E}} (hEval : (E : ℝ) = C * (Disorder.cstar M)⁻¹)
    (h : C' ≤ C) : C' * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  rw [hEval]
  exact mul_le_mul_of_nonneg_right h (inv_pos.mpr hcs0).le

/-- **`c⋆⁻¹ ≤ E`** — the second entry of the `max` in the
`coarse_ellipticity_bounds`. -/
theorem cstarInv_le_of_budget (M : ABKModel d) {C : ℝ}
    {E : {E : ℝ // 1 ≤ E}} (hEval : (E : ℝ) = C * (Disorder.cstar M)⁻¹)
    (hC : 1 ≤ C) : (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
  have h := mul_cstarInv_le_of_budget M hEval hC
  rwa [one_mul] at h

/-- The abstract-real core of the `E ≤ γ^{−1/5}` window.  The transcendental
atom `γ^{1/5}` is never seen by a numeric tactic: the chain is
`Real.rpow_le_rpow`, one exponent identity, `inv_anti₀`. -/
private theorem le_rpow_neg_fifth_core {gamma E : ℝ} (hgamma : 0 < gamma)
    (hE : 1 ≤ E) (hle : gamma ≤ (E⁻¹) ^ 10) :
    E ≤ gamma ^ (-(1 / 5 : ℝ)) := by
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hu0 : (0 : ℝ) ≤ E⁻¹ := (inv_pos.mpr hE0).le
  have hpow : ((E⁻¹) ^ 10 : ℝ) ^ (1 / 5 : ℝ) = (E⁻¹) ^ 2 := by
    rw [← Real.rpow_natCast (E⁻¹) 10, ← Real.rpow_mul hu0]
    have hexp : ((10 : ℕ) : ℝ) * (1 / 5 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_natCast]
  have h1 : gamma ^ (1 / 5 : ℝ) ≤ (E⁻¹) ^ 2 := by
    have := Real.rpow_le_rpow hgamma.le hle (by norm_num : (0 : ℝ) ≤ 1 / 5)
    rwa [hpow] at this
  have hpos : (0 : ℝ) < gamma ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hgamma _
  have h2 : ((E⁻¹) ^ 2)⁻¹ ≤ (gamma ^ (1 / 5 : ℝ))⁻¹ := inv_anti₀ hpos h1
  have h3 : ((E⁻¹) ^ 2 : ℝ)⁻¹ = E ^ 2 := by rw [inv_pow, inv_inv]
  have h4 : E ≤ E ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hE hE0.le
    calc E = E * 1 := (mul_one E).symm
      _ ≤ E * E := h
      _ = E ^ 2 := by ring
  rw [Real.rpow_neg hgamma.le]
  rw [h3] at h2
  exact h4.trans h2

/-- **`E ≤ γ^{−1/5}`** — the upper `E`-window of the `coarse_ellipticity_bounds`,
from the regime `γ ≤ E⁻¹¹⁰` alone.

The regime gives `γ^{1/5} ≤ E⁻²`, hence `γ^{−1/5} ≥ E² ≥ E`. -/
theorem le_rpow_neg_fifth_of_regime (M : ABKModel d) {E : {E : ℝ // 1 ≤ E}}
    (hreg : M.gamma ≤ (((E : ℝ))⁻¹) ^ 10) :
    (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) :=
  le_rpow_neg_fifth_core M.shellPrefix.gamma_pos E.2 hreg

/-- **The `E`-side hypotheses of the `coarse_ellipticity_bounds`.**

Given the budget identity, the regime, and the caller's own choice of `σ` and
`Ccg` (through `hexp`, which is genuinely a caller obligation: `exp (Ccg/σ)`
is unbounded as `σ ↓ 0` while the budget is fixed), the two `E`-window premises
and the state premise are all available at every scale `m`. -/
theorem coarseEllipticityBudget (M : ABKModel d) {C Ccg sigma : ℝ}
    {E : {E : ℝ // 1 ≤ E}} (hEval : (E : ℝ) = C * (Disorder.cstar M)⁻¹)
    (hC : 1 ≤ C) (hreg : M.gamma ≤ (((E : ℝ))⁻¹) ^ 10)
    (hall : ∀ m : ℤ, Algsuperdiff.Frozen.Section3.inductionState M m E)
    (hexp : Real.exp (Ccg / sigma) ≤ (E : ℝ)) (m : ℤ) :
    Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E ∧
      max (Real.exp (Ccg / sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) ∧
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) :=
  ⟨hall (m - 1), max_le hexp (cstarInv_le_of_budget M hEval hC),
    le_rpow_neg_fifth_of_regime M hreg⟩

end

end Algsuperdiff.Section4.Provider.GoodEvents
