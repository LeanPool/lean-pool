/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.TwoSidedTargets
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Scales

/-!
# NodeContract

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The closure node's contract, transcribed, and what it feeds

The closure of `l.approximate.recurrence.formula` asks, at
`e.what.do.we.have`, for the two displayed upper estimates for
`sigmaBar_(n+h)/sigmaBar_n` and its reciprocal, with `C` depending only on `d`.

`TwoSidedClosure` below is that contract, transcribed with the manuscript's own
binders: the standing hypotheses of the enclosing lemma

```
  S(m0-1, E) valid ,   E >= C cstar^{-1} ,   cgamma <= E^{-5} ,
```

and the quantifier range

```
  n in (-infty, m0] cap Z ,  h in N ,  h <= 6 cstar cgamma^{-1} ,
  mstarstar <= n <= m0 - h .
```

The manuscript's **standing dimension hypothesis** `d >= 2` is carried as the
antecedent `2 <= d` of the contract.  It is a standing assumption of the whole
paper, not a proof step, and it is what the proved principal comparison
`PrincipalResponseTerminal.exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit`
binds as `hd : 2 <= d`; a discharger of the contract obtains it by `intro hd`.

Nothing here proves the contract.  `TwoSidedClosure` is a `Prop`-valued
definition: the exact target, written down so that it can be verified against
the source *before* the two remaining endpoints are proved, and so that the
assembly skeletons of `Closure.Junctions` have a stated destination.

The second half of the module discharges the other side of the interface: the
contract's two displays deliver, verbatim, the `hupper` and `hlower` binders of
`RecurrenceIntegration.integrate_approx_recurrence` at the sequence
`s = fun m => (Annealed.sigmaBar M m : R)`.  That is proved unconditionally, and
it is the reason the displays are stated at these carriers.

## The scale gate on `m0`

The gate carried on `m0` below is `mStarStar M < m0`, **not** the printed `m0
in (mstar, infty) cap Z`.

## References

* ABK26, `l.approximate.recurrence.formula`.
* ABK26, `e.mstarstar`; `l.integrate.approx.recurrence`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

noncomputable section

/-! ## The contract -/

/-- **The closure node's exact contract.**

```
In dimension d >= 2 there exists C(d) < infinity such that, if E >= C cstar^{-1}
and cgamma <= E^{-5}, then for every n in (-infty, m0] cap Z and h in N with
h <= 6 cstar cgamma^{-1} and mstarstar <= n <= m0 - h, both lines of
e.what.do.we.have hold.
```

The standing dimension hypothesis `2 <= d` is the leading antecedent; it is the
binder the proved principal comparison carries as `hd : 2 <= d`.  The constant
is quantified outside the model, so "depends only on `d`" is rendered as
"depends only on `d`", not "depends on `M`".  The manuscript's `h in N` is
transcribed with no positivity: the degenerate shell `h = 0` is covered by
`Closure.recurrenceUpperDisplay_zero` and
`Closure.recurrenceLowerDisplay_zero`, so a proof of this contract may assume
`0 < h` at no cost. -/
def TwoSidedClosure (d : ℕ) : Prop :=
  2 ≤ d →
  ∃ C : ℝ, 0 < C ∧
    ∀ (M : ABKModel d) (m0 : ℤ) (Ec : {E : ℝ // 1 ≤ E}),
      mStarStar M < m0 →
      Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) Ec →
      C * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) →
      M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ) →
      ∀ (n : ℤ) (h : ℕ),
        (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
        mStarStar M ≤ n → n ≤ m0 - (h : ℤ) →
        RecurrenceUpperDisplay M C (Ec : ℝ) n h ∧
          RecurrenceLowerDisplay M C (Ec : ℝ) n h

/-! ## What the contract feeds -/

/-- **The two displays deliver `e.assump.upper` and `e.assump.lower.modified`.**

At one admissible pair `(n, n+h)` the two printed displays give exactly the two
binders of `RecurrenceIntegration.integrate_approx_recurrence`, at

```
  s   = fun m => (Annealed.sigmaBar M m : R) ,
  E_integration = (2 + shellIncrementCap) C E^2 |log cgamma|^2 ,
  F             = C .
```

`hcap` is produced by `Closure.shellDrift_le_cap` from the induction state and
the shell budget; `herr` is the smallness of the printed error, which
`e.cgamma.constraints` supplies.  Unconditional otherwise. -/
theorem integrationHypotheses_of_displays {d : ℕ} (M : ABKModel d) {C E : ℝ}
    {n : ℤ} {h : ℕ} (hC : 0 ≤ C)
    (hup : RecurrenceUpperDisplay M C E n h)
    (hlo : RecurrenceLowerDisplay M C E n h)
    (hcap : shellDrift M n h ≤ shellIncrementCap)
    (herr : recurrenceFlatError M C E ≤ 1) :
    (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) ≤
        (1 + C * E ^ 2 * Real.log M.gamma ^ 2 * M.gamma) *
            (Annealed.sigmaBar M n : ℝ) +
          recurrenceIncrement (Disorder.cstar M) M.gamma n (n + (h : ℤ)) *
            ((Annealed.sigmaBar M n : ℝ))⁻¹ ∧
      (1 - (2 + shellIncrementCap) * (C * E ^ 2 * Real.log M.gamma ^ 2) * M.gamma) *
            (Annealed.sigmaBar M n : ℝ) +
          recurrenceIncrement (Disorder.cstar M) M.gamma n (n + (h : ℤ)) *
            (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 *
            (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) -
          C * (((n + (h : ℤ) : ℤ) : ℝ) - (n : ℝ)) ^ 2 *
            (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
            (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) *
            (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) ≤
        (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) := by
  refine ⟨?_, sigmaBar_ge_of_displays M hC hup hlo hcap herr⟩
  have h1 := sigmaBar_le_of_upperDisplay M hup
  unfold recurrenceFlatError at h1
  exact h1

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
