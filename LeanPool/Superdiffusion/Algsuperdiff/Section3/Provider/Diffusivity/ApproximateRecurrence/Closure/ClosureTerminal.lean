/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureRecurrenceFeed
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.AsymptoticsAssembly

/-!
# ClosureTerminal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The closure contract, wired to the diffusivity-asymptotics conclusion

ABK26, `e.what.do.we.have`, `l.integrate.approx.recurrence`.

## What this module composes

Two proved conditional A were left unconnected:

* `Closure.NodeContract.TwoSidedClosure d` --- the closure node's contract, whose
  conclusion is the pair of printed displays
  `Closure.TwoSidedTargets.RecurrenceUpperDisplay` /
  `Closure.TwoSidedTargets.RecurrenceLowerDisplay` at the **wide** shell window
  `h <= 6 cstar cgamma^{-1}`, written with `Closure.ShellIncrementCap.shellDrift`
  and `Closure.TwoSidedTargets.recurrenceFlatError`;
* `Provider.Diffusivity.diffusivity_asymptotics_of_recurrence_displays` --- the
  deterministic flow spine, whose two disclosed binders `hforward`/`hreverse` are
  the same two displays at the **narrow** window
  `(m : R) <= (n : R) + cstar cgamma^{-1}`, written with
  `RecurrenceIntegration.recurrenceIncrement` and `|log cgamma|^2`, and floored
  at `mStarStar M <= n`.

`displays_window_pair` performs the conversion at one admissible pair, exactly
as `Closure.ClosureRecurrenceFeed.feed_pair` does for the integration engine's
own binders: `h := (m - n).toNat` turns the narrow window into an admissible
`(n, h)`, `Closure.TwoSidedTargets.shellDrift_eq` turns `shellDrift` into
`recurrenceIncrement` gauged by `shom_n^{-2}`, and `sq_abs` turns `(log
cgamma)^2` into `|log cgamma|^2`.  The display constant is enlarged to `Crec:=
max 1 C`, which both displays tolerate because every coefficient they carry is
nonnegative.

## What is proved

* `displays_window_pair` --- the window conversion at one pair `(n, m)`.
* `diffusivity_asymptotics_of_twoSidedClosure` --- **the composite**: from
  `Closure.NodeContract.TwoSidedClosure d` and the standing `2 <= d`, the three
  conclusions carried by `Algsuperdiff.Frozen.Section3.diffusivity_asymptotics`
  on that statement's own premise list with the landmark gate weakened to the
  `mStarStar M < m0`.

## How the premises meet

The premise list here is `mStarStar M < m0`, `inductionState M (m0 - 1) E`,
`Cflow cstar^{-1} <= E` and `cgamma <= (E^{-1})^{10}`.  The contract asks for the
same landmark gate and induction state and for `C cstar^{-1} <= E` and
`cgamma <= E^{-5}`; the
offered flow constant is `max Cflow (max 1 C)`, so the regime premise
delivers both the spine's and the contract's, and `(E^{-1})^{10} <= E^{-5}` for
`E >= 1` delivers the contract's gate.  No premise is added, reordered
or dropped, and the enlarged flow constant only weakens the first conclusion.

## The scale gate on `m0` (-bin statement change)

The landmark gate above is `mStarStar M < m0`, **not** the printed `m0 in
(mstar, infty) cap Z`.

## Binders

`hd : 2 <= d` (the contract's own antecedent) and `hclosure: TwoSidedClosure
d`.  Nothing else.

## Scope

Internal Provider infrastructure: a conditional A.  There is no `sorry`, no
`admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`; `e.what.do.we.have`.
* ABK26, `l.integrate.approx.recurrence`; `e.mstarstar`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

noncomputable section

/-! ## The window conversion -/

/-- **The two printed displays, read on the narrow window.**

At one pair `n <= m <= m0` with `mStarStar M <= n` and
`(m : R) <= (n : R) + cstar cgamma^{-1}`, the contract's display pair at the
shell `h = (m - n).toNat` is exactly the pair of binders `hforward`/`hreverse`
of `Provider.Diffusivity.diffusivity_asymptotics_of_recurrence_displays`, at any
display constant `Crec >= C`.

on the display family `hdisp` and on `C <= Crec`. -/
private theorem displays_window_pair {d : ℕ} (M : ABKModel d) {m0 : ℤ}
    {Ec : {E : ℝ // 1 ≤ E}} {C Crec : ℝ} (hCCrec : C ≤ Crec)
    (hdisp : ∀ (n : ℤ) (h : ℕ),
      (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
      mStarStar M ≤ n → n ≤ m0 - (h : ℤ) →
      RecurrenceUpperDisplay M C (Ec : ℝ) n h ∧
        RecurrenceLowerDisplay M C (Ec : ℝ) n h)
    {n m : ℤ} (hn : mStarStar M ≤ n) (hm : m ≤ m0) (hnm : n ≤ m)
    (hrange : (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹) :
    ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤
        1 +
            recurrenceIncrement (Disorder.cstar M) M.gamma n m *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
          Crec * (Ec : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma) ∧
      ((Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
        1 -
              recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
            Crec * ((m : ℝ) - (n : ℝ)) ^ 2 *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
              (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) +
          Crec * (Ec : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (h : ℤ) = m - n :=
    ⟨(m - n).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hnh : n + (h : ℤ) = m := by omega
  have hcast : ((h : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    have hz : ((h : ℤ) : ℝ) = ((m - n : ℤ) : ℝ) := by rw [hh]
    push_cast at hz ⊢
    linarith
  have hhcap : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ := by
    have hpos : (0 : ℝ) < Disorder.cstar M * M.gamma⁻¹ := by positivity
    rw [hcast]
    linarith
  obtain ⟨hup, hlo⟩ := hdisp n h hhcap hn (by omega)
  -- the drift is the increment, gauged
  have hdrift : shellDrift M n h =
      recurrenceIncrement (Disorder.cstar M) M.gamma n m *
        (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 := by
    rw [shellDrift_eq, hnh, inv_pow]
  -- the flat error, at the enlarged constant
  have hfac : (0 : ℝ) ≤ (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma := by positivity
  have hmulC := mul_le_mul_of_nonneg_right hCCrec hfac
  have herr : recurrenceFlatError M C (Ec : ℝ) ≤
      Crec * (Ec : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma := by
    unfold recurrenceFlatError
    rw [sq_abs]
    linarith only [hmulC]
  constructor
  · unfold RecurrenceUpperDisplay at hup
    rw [hnh, hdrift] at hup
    linarith only [hup, herr]
  · unfold RecurrenceLowerDisplay at hlo
    rw [hnh, hcast, hdrift, ← inv_pow] at hlo
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hq0 : (0 : ℝ) ≤ ((m : ℝ) - (n : ℝ)) ^ 2 *
        (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 * (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) := by
      positivity
    have hquad := mul_le_mul_of_nonneg_right hCCrec hq0
    linarith only [hlo, herr, hquad]

/-! ## The composite -/

/-- **The diffusivity asymptotics, from the closure node's contract.**

From `Closure.NodeContract.TwoSidedClosure d` and the standing dimension
hypothesis, the three conclusions carried by
`Algsuperdiff.Frozen.Section3.diffusivity_asymptotics` hold on that statement's
own premise list, with the landmark gate weakened to the `mStarStar M < m0` (
option (i)).

exactly on `hd : 2 <= d` and on `hclosure : TwoSidedClosure d`.  The contract
is carried as a `Prop` binder and nothing below proves any part of it; this is
a conditional A, not a claim about any source node. -/
theorem diffusivity_asymptotics_of_twoSidedClosure (d : ℕ) (hd : 2 ≤ d)
    (hclosure : TwoSidedClosure d) :
    ∃ Cflow : ℝ, 0 < Cflow ∧
      ∀ (M : ABKModel d) (m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ m : ℤ, m ≤ m0 →
          |(Annealed.sigmaBar M m : ℝ) -
              Real.sqrt
                (M.nu ^ 2 +
                  Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
            ≤ Cflow * (Disorder.cstar M)⁻¹ * (E : ℝ) *
              Real.sqrt M.gamma * |Real.log M.gamma| *
                (Annealed.sigmaBar M m : ℝ)) ∧
        (1 / 4 : ℝ) *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2)
          ≤ (Annealed.sigmaBar M m0 : ℝ) ^ 2 ∧
        (Annealed.sigmaBar M m0 : ℝ) ^ 2
          ≤ 4 *
            max
              (Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m0 : ℝ)))
              (M.nu ^ 2) := by
  classical
  obtain ⟨C, hC0, hmain⟩ := hclosure hd
  have hCrec1 : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have hCCrec : C ≤ max 1 C := le_max_right _ _
  obtain ⟨Cflow, hCflow0, hasym⟩ :=
    diffusivity_asymptotics_of_recurrence_displays d (max 1 C) hCrec1
  refine ⟨max Cflow (max 1 C), lt_of_lt_of_le hCflow0 (le_max_left _ _), ?_⟩
  intro M m0 E hm0 hS hEreg hgammaE
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcinv0 : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar0
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le one_pos hE1
  -- the spine's own regime premise
  have hEflow : Cflow * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left Cflow (max 1 C)) hcinv0.le) hEreg
  -- the contract's regime premise
  have hEC : C * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right
      (le_trans hCCrec (le_max_right Cflow (max 1 C))) hcinv0.le) hEreg
  -- the contract's scale gate, from the frozen one
  have hgamma5 : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) := by
    have hinv0 : (0 : ℝ) ≤ (E : ℝ)⁻¹ := (inv_pos.2 hE0).le
    have hinv1 : (E : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr hE1
    have hpow : ((E : ℝ)⁻¹) ^ (10 : ℕ) ≤ ((E : ℝ)⁻¹) ^ (5 : ℕ) :=
      pow_le_pow_of_le_one hinv0 hinv1 (by norm_num)
    have hzp : (E : ℝ) ^ (-5 : ℤ) = ((E : ℝ)⁻¹) ^ (5 : ℕ) := by
      rw [inv_pow, ← zpow_natCast (E : ℝ) 5, ← zpow_neg]
      norm_num
    rw [hzp]
    exact le_trans hgammaE hpow
  have hdisp := hmain M m0 E hm0 hS hEC hgamma5
  have hforward : ∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
      (Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤
        1 +
            recurrenceIncrement (Disorder.cstar M) M.gamma n m *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
          max 1 C * (E : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma :=
    fun n m hn hmle hnm hr =>
      (displays_window_pair M hCCrec
        (fun n' h' hcap' hn' hle' => hdisp n' h' hcap' hn' hle') hn hmle hnm hr).1
  have hreverse : ∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
      (Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
        1 -
              recurrenceIncrement (Disorder.cstar M) M.gamma n m *
                (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 +
            max 1 C * ((m : ℝ) - (n : ℝ)) ^ 2 *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
              (3 : ℝ) ^ (4 * M.gamma * (m : ℝ)) +
          max 1 C * (E : ℝ) ^ 2 * |Real.log M.gamma| ^ 2 * M.gamma :=
    fun n m hn hmle hnm hr =>
      (displays_window_pair M hCCrec
        (fun n' h' hcap' hn' hle' => hdisp n' h' hcap' hn' hle') hn hmle hnm hr).2
  obtain ⟨hrel, hs1, hs2⟩ := hasym M m0 E hm0 hS hEflow hgammaE hforward hreverse
  refine ⟨?_, hs1, hs2⟩
  intro m hmle
  refine le_trans (hrel m hmle) ?_
  have hsigm : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hfac : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * (E : ℝ) * Real.sqrt M.gamma *
      |Real.log M.gamma| * (Annealed.sigmaBar M m : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcinv0.le hE0.le)
      (Real.sqrt_nonneg _)) (abs_nonneg _)) hsigm.le
  have hmul := mul_le_mul_of_nonneg_right (le_max_left Cflow (max 1 C)) hfac
  linarith only [hmul]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
