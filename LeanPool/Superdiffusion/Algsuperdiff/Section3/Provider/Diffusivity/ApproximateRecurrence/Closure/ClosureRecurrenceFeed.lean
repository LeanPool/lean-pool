/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.NodeContract
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.SubLandmarkDisplays

/-!
# ClosureRecurrenceFeed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# What the closure node feeds: the two binders of `l.integrate.approx.recurrence`

ABK26, `e.what.do.we.have`, `e.assump.upper`, `e.assump.lower.modified`,
`l.integrate.approx.recurrence`.

`Closure.NodeContract.integrationHypotheses_of_displays` converts the two
printed displays at **one** admissible pair `(n, n+h)` into the two integration
hypotheses.  This module runs that conversion over the **whole** admissible
range and hands the result to the proved frozen-root splice

```
ApproximateRecurrence.SubLandmarkDisplays.sigmaBar_integrate_approx_recurrence_of_mStarStar_floored
  ,
```

whose `hupper`/`hlower` binders are exactly what comes out.  The shapes meet
with no bridge: the splice quantifies over pairs `mss <= n <= m <= m0` with
`(m : R) <= (n : R) + cstar cgamma^{-1}`, while the contract quantifies over
`(n, h)` with `mstarstar <= n`, `n <= m0 - h` and `h <= 6 cstar cgamma^{-1}`;
`h := (m - n).toNat` translates one into the other, and the splice's *narrow*
shell budget `cstar cgamma^{-1}` sits inside the contract's *wide* one.

## The two constants

The integration engine wants a single `E` with `1 <= E` and a single `F` with
`1 <= F`; they are

```
  E_integration = recurrenceIntegrationSlack M C E
                = max 1 ((2 + shellIncrementCap) (C E^2 |log cgamma|^2)) ,
  F             = max 1 C ,
```

the two `max`es being the only bookkeeping: both displays are monotone in the
constant, so enlarging is free.

## Binders

`recurrenceIntegrationBinders_of_twoSidedClosure` carries exactly

* `hclosure` --- the closure node's contract `Closure.TwoSidedClosure d`, i.e.
  the statement this lane is assembling; it is a *hypothesis* here, and nothing
  in this module proves any part of it;
* `hd : 2 <= d` --- the standing dimension hypothesis, which is the contract's
  own antecedent;
* the contract's own standing premises `mStarStar M < m0` (the gate; see
  below), the induction state, the regime `C cstar^{-1} <= E` and the gate
  `cgamma <= E^{-5}`;
* `herr : recurrenceFlatError M <= 1` --- the smallness of the printed error,
  supplied by `e.cgamma.constraints`; it is what
  `integrationHypotheses_of_displays` needs to move the error across the ratio.

No estimate is proved here and no node is claimed: this is the consumption
shape, and it is arithmetic.

## The scale gate on `m0` (-bin statement change)

Both theorems below gate `m0` at `mStarStar M < m0`, **not** at the printed `m0
in (mstar, infty) cap Z`.

## References

* ABK26, `l.approximate.recurrence.formula`.
* ABK26, `l.integrate.approx.recurrence`; `e.mstarstar`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

noncomputable section

variable {d : ℕ}

/-- The integration constant the two displays deliver. -/
def recurrenceIntegrationSlack (M : ABKModel d) (C E : ℝ) : ℝ :=
  max 1 ((2 + shellIncrementCap) * (C * E ^ 2 * Real.log M.gamma ^ 2))

theorem one_le_recurrenceIntegrationSlack (M : ABKModel d) (C E : ℝ) :
    1 ≤ recurrenceIntegrationSlack M C E := le_max_left _ _

private theorem feed_pair (M : ABKModel d) {m0 : ℤ} {Ec : {E : ℝ // 1 ≤ E}} {C : ℝ}
    (hC0 : 0 < C)
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) Ec)
    (herr : recurrenceFlatError M C (Ec : ℝ) ≤ 1)
    (hdisp : ∀ (n : ℤ) (h : ℕ),
      (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
      mStarStar M ≤ n → n ≤ m0 - (h : ℤ) →
      RecurrenceUpperDisplay M C (Ec : ℝ) n h ∧
        RecurrenceLowerDisplay M C (Ec : ℝ) n h)
    {n m : ℤ} (hn : mStarStar M ≤ n) (hm : m ≤ m0) (hnm : n ≤ m)
    (hrange : (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹) :
    (Annealed.sigmaBar M m : ℝ) ≤
        (1 + recurrenceIntegrationSlack M C (Ec : ℝ) * M.gamma) *
            (Annealed.sigmaBar M n : ℝ) +
          recurrenceIncrement (Disorder.cstar M) M.gamma n m *
            ((Annealed.sigmaBar M n : ℝ))⁻¹ ∧
      (1 - recurrenceIntegrationSlack M C (Ec : ℝ) * M.gamma) *
              (Annealed.sigmaBar M n : ℝ) +
            recurrenceIncrement (Disorder.cstar M) M.gamma n m *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 * (Annealed.sigmaBar M m : ℝ) -
          max 1 C * ((m : ℝ) - (n : ℝ)) ^ 2 *
            (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M m : ℝ) *
            (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) ≤
        (Annealed.sigmaBar M m : ℝ) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hsigm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hcap0 : (0 : ℝ) ≤ shellIncrementCap := shellIncrementCap_pos.le
  set h : ℕ := (m - n).toNat with hdef
  have hh : (h : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  have hnh : n + (h : ℤ) = m := by omega
  have hcast : ((h : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    have : ((h : ℤ) : ℝ) = ((m - n : ℤ) : ℝ) := by rw [hh]
    push_cast at this ⊢
    linarith
  have hhcap : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ := by
    have hpos : (0 : ℝ) < Disorder.cstar M * M.gamma⁻¹ := by positivity
    rw [hcast]
    linarith
  obtain ⟨hup, hlo⟩ := hdisp n h hhcap hn (by omega)
  have hcap : shellDrift M n h ≤ shellIncrementCap := by
    rcases Nat.eq_zero_or_pos h with hz | hz
    · rw [hz, shellDrift_zero]
      exact shellIncrementCap_pos.le
    · exact shellDrift_le_cap M hstate (by omega) hhcap
  obtain ⟨hupper0, hlower0⟩ :=
    integrationHypotheses_of_displays M hC0.le hup hlo hcap herr
  rw [hnh] at hupper0 hlower0
  have hbase : (0 : ℝ) ≤ C * (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 := by positivity
  have hEle1 : C * (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 ≤
      recurrenceIntegrationSlack M C (Ec : ℝ) := by
    refine le_trans ?_ (le_max_right _ _)
    exact le_mul_of_one_le_left hbase (by linarith only [hcap0])
  have hEle2 : (2 + shellIncrementCap) * (C * (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2) ≤
      recurrenceIntegrationSlack M C (Ec : ℝ) := le_max_right _ _
  have hFle : C ≤ max 1 C := le_max_right _ _
  refine ⟨?_, ?_⟩
  · have hstep : (1 + C * (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma) *
        (Annealed.sigmaBar M n : ℝ) ≤
        (1 + recurrenceIntegrationSlack M C (Ec : ℝ) * M.gamma) *
          (Annealed.sigmaBar M n : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ hsig.le
      linarith only [mul_le_mul_of_nonneg_right hEle1 hgamma0.le]
    linarith [hupper0, hstep]
  · have hstep : (1 - recurrenceIntegrationSlack M C (Ec : ℝ) * M.gamma) *
        (Annealed.sigmaBar M n : ℝ) ≤
        (1 - (2 + shellIncrementCap) *
            (C * (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2) * M.gamma) *
          (Annealed.sigmaBar M n : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ hsig.le
      linarith only [mul_le_mul_of_nonneg_right hEle2 hgamma0.le]
    have hQ : (0 : ℝ) ≤ ((m : ℝ) - (n : ℝ)) ^ 2 *
        ((((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 * ((Annealed.sigmaBar M m : ℝ) *
          (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)))) := by
      have hr := Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num)
        (4 * M.gamma * (m : ℝ))
      positivity
    have hquad : C * ((m : ℝ) - (n : ℝ)) ^ 2 *
          (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M m : ℝ) *
          (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) ≤
        max 1 C * ((m : ℝ) - (n : ℝ)) ^ 2 *
          (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M m : ℝ) *
          (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_right hFle hQ
      calc C * ((m : ℝ) - (n : ℝ)) ^ 2 *
            (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M m : ℝ) *
            (3 : ℝ) ^ (4 * M.gamma * (m : ℝ))
          = C * (((m : ℝ) - (n : ℝ)) ^ 2 *
              ((((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
                ((Annealed.sigmaBar M m : ℝ) *
                  (3 : ℝ) ^ (4 * M.gamma * (m : ℝ))))) := by ring
        _ ≤ max 1 C * (((m : ℝ) - (n : ℝ)) ^ 2 *
              ((((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
                ((Annealed.sigmaBar M m : ℝ) *
                  (3 : ℝ) ^ (4 * M.gamma * (m : ℝ))))) := hmul
        _ = max 1 C * ((m : ℝ) - (n : ℝ)) ^ 2 *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 * (Annealed.sigmaBar M m : ℝ) *
              (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) := by ring
    linarith [hlower0, hstep, hquad]

theorem recurrenceIntegrationBinders_of_twoSidedClosure (hd : 2 ≤ d)
    (hclosure : TwoSidedClosure d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ec : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) Ec →
        C * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) →
        M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ) →
        recurrenceFlatError M C (Ec : ℝ) ≤ 1 →
        (∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
            (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
            (Annealed.sigmaBar M m : ℝ) ≤
              (1 + recurrenceIntegrationSlack M C (Ec : ℝ) * M.gamma) *
                  (Annealed.sigmaBar M n : ℝ) +
                recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                  ((Annealed.sigmaBar M n : ℝ))⁻¹) ∧
          (∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
            (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
            (1 - recurrenceIntegrationSlack M C (Ec : ℝ) * M.gamma) *
                    (Annealed.sigmaBar M n : ℝ) +
                  recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                    (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 *
                    (Annealed.sigmaBar M m : ℝ) -
                max 1 C * ((m : ℝ) - (n : ℝ)) ^ 2 *
                  (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
                  (Annealed.sigmaBar M m : ℝ) *
                  (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) ≤
              (Annealed.sigmaBar M m : ℝ)) := by
  obtain ⟨C, hC0, hmain⟩ := hclosure hd
  refine ⟨C, hC0, ?_⟩
  intro M m0 Ec hm0 hstate hCE hgammaE herr
  have hdisp : ∀ (n : ℤ) (h : ℕ),
      (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
      mStarStar M ≤ n → n ≤ m0 - (h : ℤ) →
      RecurrenceUpperDisplay M C (Ec : ℝ) n h ∧
        RecurrenceLowerDisplay M C (Ec : ℝ) n h :=
    fun n h hhcap hn hle => hmain M m0 Ec hm0 hstate hCE hgammaE n h hhcap hn hle
  exact ⟨fun n m hn hm hnm hrange =>
      (feed_pair M hC0 hstate herr hdisp hn hm hnm hrange).1,
    fun n m hn hm hnm hrange =>
      (feed_pair M hC0 hstate herr hdisp hn hm hnm hrange).2⟩

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
