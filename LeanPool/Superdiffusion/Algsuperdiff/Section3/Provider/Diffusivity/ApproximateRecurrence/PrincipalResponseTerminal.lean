/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.GoodLocalEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationParams
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLegsBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseGoodEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalComplementEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseComposeDisplayTwo
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseComposeAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseIndepAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitch
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchPlateau
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseMomentsFourth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLoadMeas

/-!
# PrincipalResponseTerminal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The principal-response comparison and its gates

The two halves of the Step-3 switch display are stated at different
admissibility gates on the induction parameter `E`: the bad-event package asks
for `c⁻¹ (cstar M)⁻¹ ≤ E`, the coarse-ellipticity envelope for
`max (exp (2 C)) (cstar M)⁻¹ ≤ E`, and both for a fifth-root upper gate.  The
source premises available at this level are the two premises of
`l.approximate.recurrence.formula` itself: a constant fixed before the model
times `(cstar M)⁻¹` below `E`, and `gamma ≤ E⁻⁵`.  They are *not* contained in
`Algsuperdiff.Frozen.Section3.inductionState`, which binds only `1 ≤ E`, and
they are not carried by the frozen induction command; at the frozen root the
corresponding scale premise is the stronger `gamma ≤ (E⁻¹)^10`, from which the
`gamma ≤ E⁻⁵` read here is obtained in the root assembly.

This module supplies the arithmetic that turns those two source premises into
every gate the two halves ask for, so that none of them has to be carried as a
hypothesis by the comparison itself.

## The admissibility reductions

* `le_rpow_neg_fifth_of_gamma_le_zpow_neg_five'` --- the integer-power gate
  `gamma ≤ E⁻⁵` gives the real-power gate `E ≤ gamma^(-1/5)` that both packages
  consume.
* `admissibility_of_enlarged_const_mul_cstarInv_le` --- one enlarged constant,
  chosen after the two packages have fixed their own constants and depending
  only on them, dominates all the lower gates at once.  The step that makes this
  work is the repository's own upper bound `cstar M ≤ 3 / 2`
  (`Provider.Disorder.cstar_le_three_halves`), which gives `(cstar M)⁻¹ ≥ 2 / 3`
  and so lets a `3 / 2` factor inside the enlarged constant pay for the
  `(cstar M)⁻¹` that multiplies it.  No lower bound on `cstar M` is assumed;
  none is available.

## The scale gaps at the recurrence mesoscale

The two-sided exponent `(n - Q.scale)_+ - 5 (Q.scale - n)_+` of the oscillation
rate is read at the Step-3 orientation: the cube scale is the corrected buffer
`n := m - h - a ceil|log_3 gamma|` and the field index is `m - h`.
`scaleGapPos_recurrenceMesoScale_to_field` and
`scaleGapPos_field_to_recurrenceMesoScale` evaluate the two positive parts
there: the `-5` branch vanishes and the surviving branch is the corrected gap
itself.

## The two rate gates

Both tails of the bad-event package have to clear `gamma⁻¹ + log 2` before the
two-lane fold can collapse them.  The mechanism is the standard one: the
constants are fixed once, before `gamma`, and the whole gain is read off the
two source premises.

* `add_log_two_le_mul_rpow_three_recurrenceGap` --- the oscillation lane.  With
  `2 / c ≤ Cterm`, the premise `Cterm (cstar M)⁻¹ ≤ E` gives `2 ≤ c cstar E`,
  and `gamma ≤ E⁻⁵` gives `E ≤ gamma⁻¹`, so the prefactor reaches
  `2 ≤ c cstar gamma⁻¹`.  That alone is *not* the gate: the missing factor
  `gamma⁻¹` is supplied by the gap factor, through
  `3^(a ceil|log_3 gamma|) ≥ gamma⁻¹`.  Both steps are load-bearing.
* `add_log_two_le_exp_ellipticityRate` --- the ellipticity lane, a genuine
  exp-beats-power step.  The exponent `x := c E⁻² gamma⁻¹` has
  `x^2 / 4 = c^2 gamma⁻¹ gamma⁻¹ / (4 E^4)`; with `12 / c^2 ≤ Cterm` and
  `cstar M ≤ 3 / 2` the same premise gives `8 / c^2 ≤ E`, which together with
  `E^5 ≤ gamma⁻¹` puts `x^2 / 4` above `2 gamma⁻¹`, and `sq_div_four_le_exp`
  carries that to `exp x`.

## The two gates of the recombination

The assembly step that turns the two legs into the comparison itself asks for a
window gate and a rename gate.  Both are discharged here, over abstract reals:

* `inv_abs_log_mem_Icc` --- the window `|log gamma|⁻¹ ∈ [8 gamma, 1]`, on
  `gamma ≤ 1 / 1089`.
* This is what lets the comparison be displayed at the manuscript's own shape `C E^2
  |log cgamma|^2 cgamma` with `C` absolute, rather than at a `cgamma`-dependent
  factor.
* Its only real content is a threshold on `gamma` by an absolute constant.

All of the analytic statements are over abstract reals, away from any model or
envelope, so that no definitional depth reaches the unifier.

## The comparison itself

`exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit`
puts the two halves of the Step-3 switch display together at one and the same
witness and hands back the combined comparison of
`e.lower.bound.principal.one`: one pair of correctors produced existentially
with their `e.def.w` properties, one coarse-ellipticity constant, one per-cube
bad-event family, and a single inequality between the grid average of the
localized principal energy and the infinite-volume annealed form at the factor
`1 + 3 principalResponseSwitchBudget M E 64` plus `cgamma^6`.  Its two surviving
analytic premises are the two source premises above; every gate listed in this
header --- including the threshold on `cgamma` that the four sub-packages ask
for, which is *not* a binder but a consequence of the enlarged `Cterm` --- and
every measurability, integrability and `MemLp` proposition the two halves ask
for, is discharged inside its proof.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 3.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open MeasureTheory

noncomputable section

/-! ## The fifth-root upper gate -/

/-- The integer-power upper gate `gamma ≤ E⁻⁵` implies the real-power gate
`E ≤ gamma^(-1/5)` that the two packages consume.  Stated over abstract reals. -/
private theorem le_rpow_neg_fifth_of_gamma_le_zpow_neg_five' {E gamma : ℝ}
    (hE : 1 ≤ E) (hgamma : 0 < gamma) (hgammaE : gamma ≤ E ^ (-5 : ℤ)) :
    E ≤ gamma ^ (-(1 / 5 : ℝ)) := by
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hE5 : E ^ (5 : ℕ) ≤ gamma⁻¹ := by
    rw [le_inv_comm₀ (pow_pos hEpos 5) hgamma]
    have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rwa [hEpow] at hgammaE
  have hroot : E ≤ (gamma⁻¹) ^ ((5 : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos hEpos.le (inv_pos.mpr hgamma).le (by norm_num)]
    exact (Real.rpow_natCast E 5).trans_le hE5
  have hinv : (gamma⁻¹) ^ ((5 : ℝ)⁻¹) = gamma ^ (-(1 / 5 : ℝ)) := by
    rw [← Real.rpow_neg_one gamma, ← Real.rpow_mul hgamma.le]
    norm_num
  rwa [hinv] at hroot

/-! ## The lower admissibility gates, from one enlarged constant -/

/-- **All the lower gates at once.**  Let `cbad` and `Ccg` be the two constants
the bad-event and the coarse-ellipticity packages fix before the model is seen
(their positivity is not needed here), and let the enlarged constant be

```
  T := max 1 (max cbad⁻¹ ((3 / 2) * exp (2 Ccg))) ,
```

which depends only on them.  Then the single source premise
`T * cstarInv ≤ E`, at any `cstarInv` arising as the inverse of a positive
`cstar ≤ 3 / 2`, delivers both lower gates the two halves ask for.

The `3 / 2` inside `T` is exactly what `cstar ≤ 3 / 2` costs: it makes
`(3 / 2) * exp (2 Ccg) * cstarInv ≥ exp (2 Ccg)` even though `cstarInv` is only
known to be at least `2 / 3`.  No lower bound on `cstar` is hypothesised. -/
private theorem admissibility_of_enlarged_const_mul_cstarInv_le
    {cbad Ccg cstar E : ℝ} (hcstar0 : 0 < cstar) (hcstar : cstar ≤ 3 / 2)
    (hE : max 1 (max cbad⁻¹ ((3 / 2) * Real.exp (2 * Ccg))) * cstar⁻¹ ≤ E) :
    max (Real.exp (2 * Ccg)) cstar⁻¹ ≤ E ∧ cbad⁻¹ * cstar⁻¹ ≤ E := by
  have hcinv0 : 0 < cstar⁻¹ := inv_pos.2 hcstar0
  have hcinv : (2 : ℝ) / 3 ≤ cstar⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcstar0]
    linarith
  have hone : (1 : ℝ) ≤ max 1 (max cbad⁻¹ ((3 / 2) * Real.exp (2 * Ccg))) :=
    le_max_left _ _
  have hbad : cbad⁻¹ ≤ max 1 (max cbad⁻¹ ((3 / 2) * Real.exp (2 * Ccg))) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hexp : (3 / 2 : ℝ) * Real.exp (2 * Ccg) ≤
      max 1 (max cbad⁻¹ ((3 / 2) * Real.exp (2 * Ccg))) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max_le ?_ ?_, ?_⟩
  · have hstep : (3 / 2 : ℝ) * Real.exp (2 * Ccg) * cstar⁻¹ ≤ E :=
      le_trans (mul_le_mul_of_nonneg_right hexp hcinv0.le) hE
    have hlow : Real.exp (2 * Ccg) ≤ (3 / 2 : ℝ) * Real.exp (2 * Ccg) * cstar⁻¹ := by
      have hexp0 : (0 : ℝ) < Real.exp (2 * Ccg) := Real.exp_pos _
      nlinarith [hcinv, hexp0]
    linarith
  · have hstep : (1 : ℝ) * cstar⁻¹ ≤ E :=
      le_trans (mul_le_mul_of_nonneg_right hone hcinv0.le) hE
    linarith
  · exact le_trans (mul_le_mul_of_nonneg_right hbad hcinv0.le) hE

/-! ## The two scale gaps at the recurrence mesoscale -/

/-- At the Step-3 orientation the surviving positive part of the two-sided exponent
is the corrected recurrence gap itself. -/
private theorem scaleGapPos_recurrenceMesoScale_to_field (a : ℕ) (gamma : ℝ)
    (m h : ℤ) :
    Provider.BadEvents.scaleGapPos (recurrenceMesoScale a gamma m h) (m - h) =
      (recurrenceGap a gamma : ℝ) := by
  rw [Provider.BadEvents.scaleGapPos_of_le (recurrenceMesoScale_le a gamma m h)]
  simp only [recurrenceMesoScale]
  push_cast
  ring

/-- The `-5` branch of the same exponent vanishes at that orientation. -/
private theorem scaleGapPos_field_to_recurrenceMesoScale (a : ℕ) (gamma : ℝ)
    (m h : ℤ) :
    Provider.BadEvents.scaleGapPos (m - h) (recurrenceMesoScale a gamma m h) = 0 := by
  have hgap0 : (0 : ℝ) ≤ (recurrenceGap a gamma : ℝ) := by positivity
  have hnonpos : (((m - h - (recurrenceGap a gamma : ℤ) : ℤ) : ℝ) -
      ((m - h : ℤ) : ℝ)) ≤ 0 := by
    push_cast
    linarith only [hgap0]
  rw [Provider.BadEvents.scaleGapPos, recurrenceMesoScale]
  exact max_eq_right hnonpos

/-! ## The two rate gates -/

/-- Anything at least twice `gamma⁻¹` clears the fold's threshold, since
`log 2 ≤ 1 ≤ gamma⁻¹`. -/
private theorem add_log_two_le_of_two_mul_le {g r : ℝ} (hg : 1 ≤ g)
    (hr : 2 * g ≤ r) : g + Real.log 2 ≤ r := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith only [h]
  linarith only [hg, hr, hlog]

/-- The quadratic lower bound for the exponential, from `1 + x ≤ exp x` applied
at `x / 2`.  This is the whole of the exp-beats-power step. -/
private theorem sq_div_four_le_exp {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 4 ≤ Real.exp x := by
  have hbase : 1 + x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith only [h]
  have hnn : (0 : ℝ) ≤ 1 + x / 2 := by linarith only [hx]
  have hsq : (1 + x / 2) * (1 + x / 2) ≤ Real.exp (x / 2) * Real.exp (x / 2) :=
    mul_le_mul hbase hbase hnn (le_trans hnn hbase)
  have hexp : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hsq
  nlinarith only [hsq, hx]

/-- The three consequences of the source scale premise `gamma ≤ E⁻⁵` that both
lanes use: `gamma ≤ 1`, `E ≤ gamma⁻¹` and the sharp `E⁵ ≤ gamma⁻¹`. -/
private theorem fifth_power_regime {E gamma : ℝ} (hE : 1 ≤ E)
    (hgamma0 : 0 < gamma) (hgammaE : gamma ≤ E ^ (-5 : ℤ)) :
    gamma ≤ 1 ∧ E ≤ gamma⁻¹ ∧ E ^ (5 : ℕ) ≤ gamma⁻¹ := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hE5pos : 0 < E ^ (5 : ℕ) := pow_pos hE0 5
  have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hE5 : E ^ (5 : ℕ) ≤ gamma⁻¹ := by
    rw [le_inv_comm₀ hE5pos hgamma0]
    rwa [← hEpow]
  have hEto5 : E ≤ E ^ (5 : ℕ) := by
    have hE4 : 1 ≤ E ^ (4 : ℕ) := one_le_pow₀ hE
    calc E = E * 1 := (mul_one E).symm
      _ ≤ E * E ^ (4 : ℕ) := mul_le_mul_of_nonneg_left hE4 hE0.le
      _ = E ^ (5 : ℕ) := by ring
  have hgamma1 : gamma ≤ 1 := by
    have hpow1 : (1 : ℝ) ≤ E ^ (5 : ℕ) := one_le_pow₀ hE
    have hinvle : (E ^ (5 : ℕ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow1
    refine hgammaE.trans ?_
    rw [hEpow]
    exact hinvle
  exact ⟨hgamma1, hEto5.trans hE5, hE5⟩

/-- The corrected gap at the development multiplier covers one power of `gamma⁻¹`
in base `3`, because `ceil|log_3 gamma|` already does. -/
private theorem inv_le_rpow_three_recurrenceGap {gamma : ℝ} (hgamma0 : 0 < gamma)
    (hgamma1 : gamma ≤ 1) :
    gamma⁻¹ ≤ (3 : ℝ) ^ (recurrenceGap recurrenceGapMultiplier gamma : ℝ) := by
  have hinv0 : 0 < gamma⁻¹ := inv_pos.mpr hgamma0
  have hinv1 : (1 : ℝ) ≤ gamma⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hgamma0]
    simpa using hgamma1
  have hlog0 : 0 ≤ Real.logb 3 gamma⁻¹ := Real.logb_nonneg (by norm_num) hinv1
  have hceil := logb_le_logThreeCeil gamma
  have hcast : (recurrenceGap recurrenceGapMultiplier gamma : ℝ) =
      32 * (logThreeCeil gamma : ℝ) := by
    norm_num [recurrenceGap, recurrenceGapMultiplier]
  have hle : Real.logb 3 gamma⁻¹ ≤
      (recurrenceGap recurrenceGapMultiplier gamma : ℝ) := by
    rw [hcast]
    linarith only [hlog0, hceil]
  have hid : (3 : ℝ) ^ (Real.logb 3 gamma⁻¹) = gamma⁻¹ :=
    Real.rpow_logb (by norm_num) (by norm_num) hinv0
  calc gamma⁻¹ = (3 : ℝ) ^ (Real.logb 3 gamma⁻¹) := hid.symm
    _ ≤ (3 : ℝ) ^ (recurrenceGap recurrenceGapMultiplier gamma : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hle

/-- The source admissibility premise, cleared of its inverse. -/
private theorem le_cstar_mul_of_threshold {Cterm cstar E : ℝ} (hcstar0 : 0 < cstar)
    (hthreshold : Cterm * cstar⁻¹ ≤ E) : Cterm ≤ cstar * E := by
  have h := mul_le_mul_of_nonneg_left hthreshold hcstar0.le
  have hid : cstar * (Cterm * cstar⁻¹) = Cterm := by field_simp
  rwa [hid] at h

/-- The ellipticity lane's own reading of the same premise, at the enlarged
constant `12 / c^2` and the proved cap `cstar M ≤ 3 / 2`. -/
private theorem eight_div_sq_le_of_threshold {c cstar E Cterm : ℝ} (hc : 0 < c)
    (hcstar0 : 0 < cstar) (hcstar : cstar ≤ 3 / 2) (hC12 : 12 / c ^ 2 ≤ Cterm)
    (hthreshold : Cterm * cstar⁻¹ ≤ E) : 8 / c ^ 2 ≤ E := by
  have hcinv : (2 : ℝ) / 3 ≤ cstar⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcstar0]
    linarith
  have h12nonneg : (0 : ℝ) ≤ 12 / c ^ 2 := by positivity
  have hCnonneg : (0 : ℝ) ≤ Cterm := le_trans h12nonneg hC12
  have hleft : (12 / c ^ 2) * ((2 : ℝ) / 3) ≤ Cterm * cstar⁻¹ :=
    mul_le_mul hC12 hcinv (by norm_num) hCnonneg
  have hid : (12 / c ^ 2) * ((2 : ℝ) / 3) = 8 / c ^ 2 := by ring
  rw [hid] at hleft
  exact hleft.trans hthreshold

/-- **The oscillation lane of the bad-event tail.**  Stated over abstract reals at
the shape the per-cube estimate produces once the two scale gaps have been
evaluated: prefactor `c cstar gamma⁻¹` times the gap factor at the development
multiplier.  Only the two source premises and `2 / c ≤ Cterm` are used. -/
private theorem add_log_two_le_mul_rpow_three_recurrenceGap
    {c cstar gamma E Cterm : ℝ} (hc : 0 < c) (hcstar0 : 0 < cstar)
    (hgamma0 : 0 < gamma) (hE : 1 ≤ E) (hgammaE : gamma ≤ E ^ (-5 : ℤ))
    (hC2 : 2 / c ≤ Cterm) (hthreshold : Cterm * cstar⁻¹ ≤ E) :
    gamma⁻¹ + Real.log 2 ≤ c * cstar * gamma⁻¹ *
      (3 : ℝ) ^ (recurrenceGap recurrenceGapMultiplier gamma : ℝ) := by
  obtain ⟨hgamma1, hEinv, -⟩ := fifth_power_regime hE hgamma0 hgammaE
  have hinv0 : 0 < gamma⁻¹ := inv_pos.mpr hgamma0
  have hinv1 : (1 : ℝ) ≤ gamma⁻¹ := le_trans hE hEinv
  have h2c : 2 / c ≤ cstar * E := hC2.trans (le_cstar_mul_of_threshold hcstar0 hthreshold)
  have htwo : 2 ≤ c * (cstar * E) := by
    have h := mul_le_mul_of_nonneg_left h2c hc.le
    have hid : c * (2 / c) = 2 := by field_simp
    linarith only [h, hid]
  have hccs0 : 0 ≤ c * cstar := mul_nonneg hc.le hcstar0.le
  have htwoInv : 2 ≤ c * cstar * gamma⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_left hEinv hccs0
    nlinarith only [htwo, hmul]
  have hfirst : 2 * gamma⁻¹ ≤ c * cstar * gamma⁻¹ * gamma⁻¹ :=
    mul_le_mul_of_nonneg_right htwoInv hinv0.le
  have hsecond : c * cstar * gamma⁻¹ * gamma⁻¹ ≤ c * cstar * gamma⁻¹ *
      (3 : ℝ) ^ (recurrenceGap recurrenceGapMultiplier gamma : ℝ) :=
    mul_le_mul_of_nonneg_left
      (inv_le_rpow_three_recurrenceGap hgamma0 hgamma1) (by positivity)
  exact add_log_two_le_of_two_mul_le hinv1 (hfirst.trans hsecond)

/-- **The ellipticity lane of the bad-event tail.**  For the exponent
`x := c E⁻² gamma⁻¹` one has `x^2 / 4 = c^2 gamma⁻¹ gamma⁻¹ / (4 E^4)`, and
`8 / c^2 ≤ E` together with `E^5 ≤ gamma⁻¹` puts that above `2 gamma⁻¹`;
`sq_div_four_le_exp` then carries it to `exp x`.  Only the two source premises,
the proved cap `cstar M ≤ 3 / 2` and `12 / c^2 ≤ Cterm` are used. -/
private theorem add_log_two_le_exp_ellipticityRate {c cstar gamma E Cterm : ℝ}
    (hc : 0 < c) (hcstar0 : 0 < cstar) (hcstar : cstar ≤ 3 / 2)
    (hgamma0 : 0 < gamma) (hE : 1 ≤ E) (hgammaE : gamma ≤ E ^ (-5 : ℤ))
    (hC12 : 12 / c ^ 2 ≤ Cterm) (hthreshold : Cterm * cstar⁻¹ ≤ E) :
    gamma⁻¹ + Real.log 2 ≤ Real.exp (c * E⁻¹ ^ 2 * gamma⁻¹) := by
  obtain ⟨-, hEinv, hE5⟩ := fifth_power_regime hE hgamma0 hgammaE
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hinv0 : 0 < gamma⁻¹ := inv_pos.mpr hgamma0
  have hinv1 : (1 : ℝ) ≤ gamma⁻¹ := le_trans hE hEinv
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have h8 : 8 / c ^ 2 ≤ E := eight_div_sq_le_of_threshold hc hcstar0 hcstar hC12 hthreshold
  have h8' : 8 ≤ c ^ 2 * E := by
    have h := mul_le_mul_of_nonneg_left h8 hc2.le
    have hid : c ^ 2 * (8 / c ^ 2) = 8 := by field_simp
    linarith only [h, hid]
  have hx0 : (0 : ℝ) ≤ c * E⁻¹ ^ 2 * gamma⁻¹ := by positivity
  have hstep : 8 * (gamma⁻¹ * E ^ (4 : ℕ)) ≤ c ^ 2 * (gamma⁻¹ * gamma⁻¹) := by
    have hA : 8 * (gamma⁻¹ * E ^ (4 : ℕ)) ≤
        c ^ 2 * E * (gamma⁻¹ * E ^ (4 : ℕ)) :=
      mul_le_mul_of_nonneg_right h8' (by positivity)
    have hB : c ^ 2 * E * (gamma⁻¹ * E ^ (4 : ℕ)) =
        c ^ 2 * (gamma⁻¹ * E ^ (5 : ℕ)) := by ring
    have hC : c ^ 2 * (gamma⁻¹ * E ^ (5 : ℕ)) ≤ c ^ 2 * (gamma⁻¹ * gamma⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE5 hinv0.le) hc2.le
    linarith only [hA, hB, hC]
  have hkey : 2 * gamma⁻¹ ≤ (c * E⁻¹ ^ 2 * gamma⁻¹) ^ 2 / 4 := by
    have hx2 : (c * E⁻¹ ^ 2 * gamma⁻¹) ^ 2 / 4 =
        c ^ 2 * (gamma⁻¹ * gamma⁻¹) / (4 * E ^ (4 : ℕ)) := by
      field_simp
    rw [hx2, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * E ^ (4 : ℕ))]
    have hrw : 2 * gamma⁻¹ * (4 * E ^ (4 : ℕ)) = 8 * (gamma⁻¹ * E ^ (4 : ℕ)) := by ring
    linarith only [hstep, hrw]
  exact add_log_two_le_of_two_mul_le hinv1 (hkey.trans (sq_div_four_le_exp hx0))

/-! ## The bad-event leg inside the half budget -/

/-- **The bad-event leg of the Step-3 display, already inside `gamma^6 / 2`.**

* the two scale gaps are evaluated at the mesoscale, so the tail's first
  exponent is `c cstar gamma⁻¹ 3^(32 ceil|log_3 gamma|)`;
* the two rate gates then collapse the sum of exponentials to
  `exp (-gamma⁻¹)` through `exp_add_exp_le_exp_neg`;
* the moment envelope `3^22 . 2 C cstar⁻¹ gamma⁻¹ . Cv^2` is put inside `Cm
  gamma⁻²` at `Cm := 3^22 . 2 C . Cv^2` using `cstar⁻¹ ≤ gamma⁻¹`, and
  `badEventEnergy_budget_le` closes at the tail power `3/8`.

The bad leg's per-cube integrability is passed through from the estimate, which
produces it on its own conclusion side; it is not assumed here and does not
appear among the binders.  The recombination of the two legs needs it.

The four propositions the caller supplies beyond the estimate's own binders --
the two rate gates, `cstar⁻¹ ≤ gamma⁻¹` and the smallness of `gamma` against
`Cm` -- are all discharged from the two source premises by the terminal
comparison; none of them survives there.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
private theorem exists_const_descendantsAverage_switchCubeEnergy_badEvent_le_half
    (d : ℕ) :
    ∃ Cbase c C : ℝ, 1 ≤ Cbase ∧ (d : ℝ) ^ 6 ≤ Cbase ∧ 0 < c ∧ 0 < C ∧
      ∀ (M : ABKModel d) (E : {E : ℝ // 1 ≤ E}) (m h : ℤ) (Q : TriadicCube d)
        (j : ℕ) (P : TriadicCube d → CutoffSample d → BlockVec d) (Cv : ℝ),
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        0 < h →
        Q.scale - (j : ℤ) =
          recurrenceMesoScale recurrenceGapMultiplier M.gamma m h →
        max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        c⁻¹ * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        M.gamma / 2 + Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma →
        M.gamma ≤ 1 / 1089 →
        (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
        0 < Cv →
        (∀ R ∈ descendantsAtDepth Q j,
          AEStronglyMeasurable
            (fun omega : CutoffSample d => switchCubeEnergy M m R (P R omega) omega)
            (cutoffSampleLaw M).toMeasure) →
        (∀ R ∈ descendantsAtDepth Q j,
          AEStronglyMeasurable
            (fun omega : CutoffSample d =>
              Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P R omega)))
            (cutoffSampleLaw M).toMeasure) →
        (∀ R ∈ descendantsAtDepth Q j,
          Integrable
            (fun omega : CutoffSample d =>
              annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P R omega) ^ (2 : ℕ))
            (cutoffSampleLaw M).toMeasure) →
        descendantsAverage Q j
            (fun R => ∫ omega : CutoffSample d,
              annealedSqrtNormSq (Annealed.sigmaBar M (m - 1)) (P R omega) ^ (2 : ℕ)
              ∂(cutoffSampleLaw M).toMeasure) ≤ Cv ^ (4 : ℕ) →
        M.gamma⁻¹ + Real.log 2 ≤ c * Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ (recurrenceGap recurrenceGapMultiplier M.gamma : ℝ) →
        M.gamma⁻¹ + Real.log 2 ≤ Real.exp (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) →
        (Disorder.cstar M)⁻¹ ≤ M.gamma⁻¹ →
        M.gamma ≤
          (2 * ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cv ^ (2 : ℕ)) * 24 ^ (9 : ℕ))⁻¹ →
          (∀ R ∈ descendantsAtDepth Q j,
            Integrable
              (fun omega : CutoffSample d =>
                switchCubeEnergy M m R (P R omega) omega *
                  (principalBadEvent M (2 * Cbase) R (m - h)).indicator
                    (fun _ => (1 : ℝ)) omega)
              (cutoffSampleLaw M).toMeasure) ∧
          descendantsAverage Q j
              (fun R => ∫ omega : CutoffSample d,
                switchCubeEnergy M m R (P R omega) omega *
                  (principalBadEvent M (2 * Cbase) R (m - h)).indicator
                    (fun _ => (1 : ℝ)) omega
                ∂(cutoffSampleLaw M).toMeasure) ≤ M.gamma ^ (6 : ℕ) / 2 := by
  classical
  obtain ⟨Cbase, c, C, hCbase, hCbased, hc, hC0, hgrid⟩ :=
    exists_const_descendantsAverage_integral_switchCubeEnergy_badEvent_le d
  refine ⟨Cbase, c, C, hCbase, hCbased, hc, hC0, ?_⟩
  intro M E m h Q j P Cv hstate hh0 hscale hEexp hEadm hEgamma hwindow hgamma1089 hh
    hCv0 hXm hVm hVint havg hrate hrateEllip hcstarinv hsmall
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hinv0 : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgamma0
  obtain ⟨hbadInt, hres⟩ := hgrid M E m h recurrenceGapMultiplier Q j P Cv hstate hh0
    (by norm_num [recurrenceGapMultiplier]) hscale hEexp hEadm hEgamma hwindow
    hgamma1089 hh hCv0.le hXm hVm hVint havg
  refine ⟨hbadInt, ?_⟩
  -- the two scale gaps at the Step-3 orientation
  have hexp1 : c * Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (-5 * Provider.BadEvents.scaleGapPos (m - h)
          (recurrenceMesoScale recurrenceGapMultiplier M.gamma m h)) *
        (3 : ℝ) ^ Provider.BadEvents.scaleGapPos
          (recurrenceMesoScale recurrenceGapMultiplier M.gamma m h) (m - h) =
      c * Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (recurrenceGap recurrenceGapMultiplier M.gamma : ℝ) := by
    rw [scaleGapPos_field_to_recurrenceMesoScale,
      scaleGapPos_recurrenceMesoScale_to_field, mul_zero, Real.rpow_zero, mul_one]
  rw [hexp1] at hres
  refine le_trans hres ?_
  -- the two-lane fold of the tail
  have htail : Real.exp (-(c * Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (recurrenceGap recurrenceGapMultiplier M.gamma : ℝ))) +
      Real.exp (-Real.exp (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      Real.exp (-M.gamma⁻¹) :=
    exp_add_exp_le_exp_neg (by linarith) (by linarith)
  have htail0 : (0 : ℝ) ≤ Real.exp (-(c * Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (recurrenceGap recurrenceGapMultiplier M.gamma : ℝ))) +
      Real.exp (-Real.exp (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := by positivity
  -- the moment envelope, at the dimension-only constant the budget consumes
  have hCm0 : (0 : ℝ) < (3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cv ^ (2 : ℕ) := by positivity
  have hsq : (M.gamma ^ (2 : ℕ))⁻¹ = M.gamma⁻¹ * M.gamma⁻¹ := by
    rw [pow_two, mul_inv]
  have hEmom : (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) *
      Cv ^ (2 : ℕ) ≤
      ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cv ^ (2 : ℕ)) * (M.gamma ^ (2 : ℕ))⁻¹ := by
    have h1 : C * (Disorder.cstar M)⁻¹ ≤ C * M.gamma⁻¹ :=
      mul_le_mul_of_nonneg_left hcstarinv hC0.le
    have h2 : C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹ ≤ C * M.gamma⁻¹ * M.gamma⁻¹ :=
      mul_le_mul_of_nonneg_right h1 hinv0.le
    have h3 : (3 : ℝ) ^ (22 : ℝ) * (2 * (C * (Disorder.cstar M)⁻¹ * M.gamma⁻¹)) ≤
        (3 : ℝ) ^ (22 : ℝ) * (2 * (C * M.gamma⁻¹ * M.gamma⁻¹)) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (Real.rpow_pos_of_pos (by norm_num) (22 : ℝ)).le
    refine le_trans (mul_le_mul_of_nonneg_right h3 (by positivity)) (le_of_eq ?_)
    rw [hsq]
    ring
  exact badEventEnergy_budget_le hgamma0 hCm0 htail0 hEmom htail hsmall

/-! ## The two gates of the recombination -/

/-- **The window gate.**  On `gamma ≤ 1 / 1089` the reciprocal logarithm sits in
`[8 gamma, 1]`.  The upper end is `log 4 ≥ 1`; the lower end is `8 gamma |log
gamma| ≤ 16 sqrt gamma ≤ 16 / 33 < 1`, using `log y ≤ 2 sqrt y` at `y =
gamma⁻¹` -- the crude `log y ≤ y - 1` is far too weak here.  Stated over
abstract reals. -/
private theorem inv_abs_log_mem_Icc {gamma : ℝ} (hgamma0 : 0 < gamma)
    (hgamma : gamma ≤ 1 / 1089) :
    |Real.log gamma|⁻¹ ∈ Set.Icc (8 * gamma) 1 := by
  have hq : gamma ≤ 1 / 4 := by linarith
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mpr hexp
    linarith
  have hmono : Real.log gamma ≤ Real.log (1 / 4) := Real.log_le_log hgamma0 hq
  have hval : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hneg : Real.log gamma ≤ -1 := by
    rw [hval] at hmono
    linarith
  have hlt0 : Real.log gamma < 0 := by linarith
  have habs : |Real.log gamma| = Real.log gamma⁻¹ := by
    rw [Real.log_inv, abs_of_neg hlt0]
  have hlpos : 0 < |Real.log gamma| := by
    rw [abs_of_neg hlt0]
    linarith
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · have hsp : 0 < Real.sqrt gamma := Real.sqrt_pos.mpr hgamma0
    have hsq : Real.sqrt gamma ≤ 1 / 33 := by
      have h := Real.sqrt_le_sqrt hgamma
      rwa [show (1 / 1089 : ℝ) = (1 / 33) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 33)] at h
    have hinvpos : (0 : ℝ) < gamma⁻¹ := inv_pos.2 hgamma0
    have hlogle : Real.log gamma⁻¹ ≤ 2 * Real.sqrt gamma⁻¹ := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hinvpos)
      rw [Real.log_sqrt hinvpos.le] at h
      linarith [Real.sqrt_nonneg gamma⁻¹]
    have hsi : Real.sqrt gamma⁻¹ = (Real.sqrt gamma)⁻¹ := Real.sqrt_inv gamma
    have hgs : gamma * (Real.sqrt gamma)⁻¹ = Real.sqrt gamma := by
      have hne : Real.sqrt gamma ≠ 0 := ne_of_gt hsp
      field_simp
      exact (Real.sq_sqrt hgamma0.le).symm
    have hkey : 8 * gamma * |Real.log gamma| ≤ 1 := by
      rw [habs]
      calc 8 * gamma * Real.log gamma⁻¹ ≤ 8 * gamma * (2 * Real.sqrt gamma⁻¹) := by
            nlinarith [hlogle, hgamma0]
        _ = 16 * (gamma * (Real.sqrt gamma)⁻¹) := by rw [hsi]; ring
        _ = 16 * Real.sqrt gamma := by rw [hgs]
        _ ≤ 16 * (1 / 33) := by linarith
        _ ≤ 1 := by norm_num
    rw [← one_div]
    exact (le_div_iff₀ hlpos).mpr hkey
  · rw [abs_of_neg hlt0]
    exact inv_le_one_of_one_le₀ (by linarith)

/-- The budget of `e.use.also.for.the.upper.bound` carries the geometric factor
`3^(2 s G)` at the window `s = |log cgamma|^{-1}` and the scale gap
`G = 32 ceil|log_3 cgamma|`.  That product is bounded by an absolute constant:
`log 3 >= 1` puts `log_3 cgamma^{-1}` below `|log cgamma|`, the ceiling costs one
more, and `|log cgamma| >= 1` on `cgamma <= 1 / 4` pays for it, so
`ceil|log_3 cgamma| <= 2 |log cgamma|` and `s G <= 64`.

This is what lets the terminal display its switch budget at a constant that
does not depend on `cgamma`, i.e. at the manuscript's own shape `C E^2 |log
cgamma|^2 cgamma` with `C` absolute.  Stated over abstract reals. -/
private theorem windowExponent_recurrenceGap_le_sixtyFour {gamma : ℝ}
    (hgamma0 : 0 < gamma) (hgamma : gamma ≤ 1 / 4) :
    |Real.log gamma|⁻¹ *
        ((recurrenceGap recurrenceGapMultiplier gamma : ℕ) : ℝ) ≤ 64 := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mpr hexp
    linarith
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr hexp
    linarith
  have hmono : Real.log gamma ≤ Real.log (1 / 4) := Real.log_le_log hgamma0 hgamma
  have hval : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hneg : Real.log gamma ≤ -1 := by
    rw [hval] at hmono
    linarith
  have hlt0 : Real.log gamma < 0 := by linarith
  have habs : |Real.log gamma| = Real.log gamma⁻¹ := by
    rw [Real.log_inv, abs_of_neg hlt0]
  have hL1 : (1 : ℝ) ≤ |Real.log gamma| := by
    rw [abs_of_neg hlt0]
    linarith
  have hL0 : (0 : ℝ) < |Real.log gamma| := lt_of_lt_of_le zero_lt_one hL1
  have hLinv0 : (0 : ℝ) < |Real.log gamma|⁻¹ := inv_pos.2 hL0
  have hlogb : Real.logb 3 gamma⁻¹ ≤ |Real.log gamma| := by
    rw [← Real.log_div_log, ← habs]
    exact div_le_self (le_trans zero_le_one hL1) hlog3
  have hceil : (logThreeCeil gamma : ℝ) < Real.logb 3 gamma⁻¹ + 1 :=
    logThreeCeil_lt_logb_add_one hgamma0 (by linarith)
  have hceil2 : (logThreeCeil gamma : ℝ) ≤ 2 * |Real.log gamma| := by linarith
  have hcast : ((recurrenceGap recurrenceGapMultiplier gamma : ℕ) : ℝ) =
      32 * (logThreeCeil gamma : ℝ) := by
    norm_num [recurrenceGap, recurrenceGapMultiplier]
  calc |Real.log gamma|⁻¹ * ((recurrenceGap recurrenceGapMultiplier gamma : ℕ) : ℝ)
      = |Real.log gamma|⁻¹ * (32 * (logThreeCeil gamma : ℝ)) := by rw [hcast]
    _ ≤ |Real.log gamma|⁻¹ * (32 * (2 * |Real.log gamma|)) :=
        mul_le_mul_of_nonneg_left (by linarith) hLinv0.le
    _ = 64 * (|Real.log gamma|⁻¹ * |Real.log gamma|) := by ring
    _ = 64 := by rw [inv_mul_cancel₀ hL0.ne']; ring

/-- The only real content is the threshold `gamma ≤ Cbud`, which is a bound by an
absolute constant. -/
private theorem pow_six_le_budget_core {gamma Cbud Ecv K : ℝ} (hgamma0 : 0 < gamma)
    (hgamma : gamma ≤ 1 / 4) (hCbud : gamma ≤ Cbud) (hEc : 1 ≤ Ecv) (hK : 0 ≤ K) :
    gamma ^ (6 : ℕ) ≤
      Cbud * (3 : ℝ) ^ (2 * K) * (Ecv ^ 2 * Real.log gamma ^ 2 * gamma) := by
  have hCbud0 : 0 < Cbud := lt_of_lt_of_le hgamma0 hCbud
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mpr hexp
    linarith
  have hmono : Real.log gamma ≤ Real.log (1 / 4) := Real.log_le_log hgamma0 hgamma
  have hval : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hneg : Real.log gamma ≤ -1 := by
    rw [hval] at hmono
    linarith
  have hlogsq : (1 : ℝ) ≤ Real.log gamma ^ 2 := by nlinarith [hneg]
  have hEcsq : (1 : ℝ) ≤ Ecv ^ 2 := one_le_pow₀ hEc
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * K) := Real.one_le_rpow (by norm_num) (by linarith)
  have hprod : (1 : ℝ) ≤ Ecv ^ 2 * Real.log gamma ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Ecv ^ 2 - 1)
      (by linarith : (0 : ℝ) ≤ Real.log gamma ^ 2 - 1)]
  have hinner : gamma ≤ Ecv ^ 2 * Real.log gamma ^ 2 * gamma := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Ecv ^ 2 * Real.log gamma ^ 2 - 1)
      hgamma0.le]
  have hX0 : (0 : ℝ) ≤ Ecv ^ 2 * Real.log gamma ^ 2 * gamma := by positivity
  have hb1 : Cbud * gamma ≤ Cbud * (Ecv ^ 2 * Real.log gamma ^ 2 * gamma) :=
    mul_le_mul_of_nonneg_left hinner hCbud0.le
  have hc3 : Cbud ≤ Cbud * (3 : ℝ) ^ (2 * K) := by
    nlinarith [mul_nonneg hCbud0.le (by linarith : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * K) - 1)]
  have hb2 : Cbud * (Ecv ^ 2 * Real.log gamma ^ 2 * gamma) ≤
      Cbud * (3 : ℝ) ^ (2 * K) * (Ecv ^ 2 * Real.log gamma ^ 2 * gamma) :=
    mul_le_mul_of_nonneg_right hc3 hX0
  have hstep : ∀ n : ℕ, gamma ^ (n + 1) ≤ gamma ^ n := by
    intro n
    rw [pow_succ]
    nlinarith [mul_nonneg (pow_nonneg hgamma0.le n) (by linarith : (0 : ℝ) ≤ 1 - gamma)]
  have h62 : gamma ^ (6 : ℕ) ≤ gamma ^ (2 : ℕ) :=
    le_trans (hstep 5) (le_trans (hstep 4) (le_trans (hstep 3) (hstep 2)))
  have hsq2 : gamma ^ (2 : ℕ) ≤ Cbud * gamma := by
    have hrw : gamma ^ (2 : ℕ) = gamma * gamma := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hCbud hgamma0.le
  linarith

/-! ## The plumbing of the limit-side quadratic form -/

/-- **From the entrywise second moments of a doubled load to its scalar
block-diagonal quadratic form.**  For a block-diagonal `diag(a I, b I)` the form
`W . diag(a I, b I) W` is the finite sum `a sum_i W_i^2 + b sum_i W'_i^2` of the
very products `toFullBlockVec W alpha * toFullBlockVec W beta` at
`alpha = beta`, so integrability of those products gives integrability of the
form.  Stated over an arbitrary measure, away from any model. -/
private theorem integrable_blockVecDot_blockDiag_smul_one_of_entries {d : ℕ}
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (W : Omega → BlockVec d) (a b : ℝ)
    (hW : ∀ alpha beta : BlockCoord d,
      Integrable (fun z => toFullBlockVec (W z) alpha * toFullBlockVec (W z) beta) mu) :
    Integrable (fun z => blockVecDot (W z)
      (blockMatVecMul (Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) (W z))) mu := by
  have hEq : (fun z => blockVecDot (W z)
        (blockMatVecMul (Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) (W z))) =
      fun z => a * ∑ i : Fin d, toFullBlockVec (W z) (Sum.inl i) *
            toFullBlockVec (W z) (Sum.inl i) +
          b * ∑ i : Fin d, toFullBlockVec (W z) (Sum.inr i) *
            toFullBlockVec (W z) (Sum.inr i) := by
    funext z
    rw [blockVecDot_blockDiag_smul_one_vecDot]
    rfl
  rw [hEq]
  exact ((integrable_finsetSum _ fun i _ => hW (Sum.inl i) (Sum.inl i)).const_mul a).add
    ((integrable_finsetSum _ fun i _ => hW (Sum.inr i) (Sum.inr i)).const_mul b)

/-! ## The principal-response comparison -/

private theorem principalResponseTerminal_comparisonBounds1 :
    ∀ (d : ℕ) (Cbase c C : ℝ) (_ : (1 : ℝ) ≤ Cbase) (_ : (↑d : ℝ) ^ (6 : ℕ) ≤ Cbase)
      (_ : (0 : ℝ) < c) (_ : (0 : ℝ) < C) (Cload : ℝ) (_ : (0 : ℝ) < Cload)
      (_ : (0 : ℝ) < (3 : ℝ) ^ (22 : ℝ) * ((2 : ℝ) * C) * Cload ^ (2 : ℕ)) (_ : (0 : ℝ) < (24 : ℝ)
        ^ (9 : ℕ))
      (Cterm : ℝ) (_ : (2 : ℝ) / c ≤ Cterm) (_ : (12 : ℝ) / c ^ (2 : ℕ) ≤ Cterm)
      (_ : (12 : ℝ) * C ^ (2 : ℕ) ≤ Cterm)
      (_ : (3 : ℝ) * ((3 : ℝ) ^ (22 : ℝ) * ((2 : ℝ) * C) * Cload ^ (2 : ℕ)) * (24 : ℝ) ^ (9 : ℕ) ≤
        Cterm)
      (_ : (1 : ℝ) ≤ Cterm) (M : ABKModel d) (m _ : ℤ) (hgap : ℕ) (E : { E : ℝ // (1 : ℝ) ≤ E })
      (_ : (0 : ℕ) < hgap) (_ : Cterm * (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
      (_ : M.gamma ≤ (↑E : ℝ) ^ (-5 : ℤ)) (_ : (↑hgap : ℝ) ≤ (6 : ℝ) * Disorder.cstar M *
        M.gamma⁻¹) (_ : ℕ)
      (_ : (0 : ℝ) < M.gamma) (_ : (0 : ℝ) < M.gamma⁻¹) (_ : (0 : ℝ) < Disorder.cstar M)
      (_ : Disorder.cstar M ≤ (3 / 2 : ℝ)) (_ : (0 : ℝ) < (Disorder.cstar M)⁻¹) (_ : (1 : ℝ) ≤ (↑E
        : ℝ))
      (_ : ∀ (T : ℝ), (0 : ℝ) ≤ T → T ≤ Cterm → T * (2 / 3 : ℝ) ≤ (↑E : ℝ)) (_ : (↑E : ℝ) ≤
        M.gamma⁻¹)
      (_ : (↑E : ℝ) ^ (5 : ℕ) ≤ M.gamma⁻¹) (_ : M.gamma ≤ (1 / 1089 : ℝ)),
      (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) ∧
        (Disorder.cstar M)⁻¹ ≤ M.gamma⁻¹ ∧
          M.gamma ≤ ((2 : ℝ) * ((3 : ℝ) ^ (22 : ℝ) * ((2 : ℝ) * C) * Cload ^ (2 : ℕ)) * (24 : ℝ) ^
            (9 : ℕ))⁻¹ ∧
            M.gamma / (2 : ℝ) + Real.exp (-(C⁻¹ * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)) ≤ M.gamma ∧
              M.gamma⁻¹ + Real.log (2 : ℝ) ≤
                  c * Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (↑(recurrenceGap
                    recurrenceGapMultiplier M.gamma) : ℝ) ∧
                M.gamma⁻¹ + Real.log (2 : ℝ) ≤ Real.exp (c * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹) ∧
                  (0 : ℤ) < (↑hgap : ℤ) ∧
                    m - (↑hgap : ℤ) ≤ m - (1 : ℤ) ∧
                      (↑(↑hgap : ℤ) : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹ ∧
                        (2 : ℝ) * (↑d : ℝ) ^ (6 : ℕ) ≤ (2 : ℝ) * Cbase *
                          BadEvents.sensitivityConstMax d ^ (2 : ℕ) := by
  intro d Cbase _ C _ _ hc _ Cload _ hCm0 h24 _ hT2c hT12 hTC2 hTm hTone M m _ hgap E hhpos
    hthreshold hgammaE hh _ hgamma0 hinv0 hcstar0 hcstar32 hcinv0 hE1 hproj hEinv hE5 _
  have hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) :=
    le_rpow_neg_fifth_of_gamma_le_zpow_neg_five' hE1 hgamma0 hgammaE
  have hcstarE : (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hTone hcinv0.le
    rw [one_mul] at h
    exact le_trans h hthreshold
  have hcstarinv : (Disorder.cstar M)⁻¹ ≤ M.gamma⁻¹ := le_trans hcstarE hEinv
  have hsmall : M.gamma ≤
      (2 * ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cload ^ (2 : ℕ)) * 24 ^ (9 : ℕ))⁻¹ := by
    have hX0 : (0 : ℝ) <
        2 * ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cload ^ (2 : ℕ)) * 24 ^ (9 : ℕ) :=
      mul_pos (mul_pos (by norm_num) hCm0) h24
    rw [le_inv_comm₀ hgamma0 hX0]
    have h := hproj (3 * ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cload ^ (2 : ℕ)) * 24 ^ (9 : ℕ))
      (by positivity) hTm
    have hid : (3 * ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cload ^ (2 : ℕ)) * 24 ^ (9 : ℕ)) *
        (2 / 3) =
        2 * ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cload ^ (2 : ℕ)) * 24 ^ (9 : ℕ) := by ring
    linarith [hEinv]
  -- the window of the bad-event tail, an exp-beats-power step at the exponent `C⁻¹`
  have hwindow : M.gamma / 2 +
      Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma := by
    have hy0 : (0 : ℝ) ≤ C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by positivity
    have h8C : 8 * C ^ 2 ≤ (E : ℝ) := by
      have h := hproj (12 * C ^ 2) (by positivity) hTC2
      linarith
    have hy2 : (C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) ^ 2 =
        M.gamma⁻¹ * M.gamma⁻¹ / (C ^ 2 * (E : ℝ) ^ (4 : ℕ)) := by
      field_simp
    have hden : (0 : ℝ) < C ^ 2 * (E : ℝ) ^ (4 : ℕ) := by positivity
    have hstep : 8 * C ^ 2 * (E : ℝ) ^ (4 : ℕ) ≤ M.gamma⁻¹ := by
      have h1 : 8 * C ^ 2 * (E : ℝ) ^ (4 : ℕ) ≤ (E : ℝ) * (E : ℝ) ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_right h8C (by positivity)
      have h2 : (E : ℝ) * (E : ℝ) ^ (4 : ℕ) = (E : ℝ) ^ (5 : ℕ) := by ring
      linarith [hE5]
    have hkey : 8 * M.gamma⁻¹ ≤ (C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) ^ 2 := by
      rw [hy2, le_div_iff₀ hden]
      have h3 := mul_le_mul_of_nonneg_left hstep hinv0.le
      linarith [h3]
    have hexpy : 2 * M.gamma⁻¹ ≤ Real.exp (C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) := by
      refine le_trans ?_ (sq_div_four_le_exp hy0)
      linarith [hkey]
    have hid : M.gamma / 2 = (2 * M.gamma⁻¹)⁻¹ := by
      field_simp
    have hexpneg : Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma / 2 := by
      rw [Real.exp_neg, hid,
        le_inv_comm₀ (inv_pos.2 (Real.exp_pos _))
          (mul_pos (by norm_num : (0 : ℝ) < 2) hinv0),
        inv_inv]
      exact hexpy
    linarith [hexpneg]
  have hrate := add_log_two_le_mul_rpow_three_recurrenceGap hc hcstar0 hgamma0 hE1
    hgammaE hT2c hthreshold
  have hrateEllip := add_log_two_le_exp_ellipticityRate hc hcstar0 hcstar32 hgamma0 hE1
    hgammaE hT12 hthreshold
  -- the scale data
  have hhZ : (0 : ℤ) < (hgap : ℤ) := by exact_mod_cast hhpos
  have hm : m - (hgap : ℤ) ≤ m - 1 := by omega
  have hhcast : (((hgap : ℤ) : ℝ)) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ := by
    push_cast
    exact hh
  -- the two halves at one and the same coarse-ellipticity constant
  have hccg : 2 * (d : ℝ) ^ 6 ≤
      2 * Cbase * Provider.BadEvents.sensitivityConstMax d ^ 2 := by
    have h2 : (1 : ℝ) ≤ Provider.BadEvents.sensitivityConstMax d ^ 2 :=
      one_le_pow₀ (Provider.BadEvents.one_le_sensitivityConstMax d)
    have h3 : (0 : ℝ) ≤ 2 * Cbase := by linarith
    calc 2 * (d : ℝ) ^ 6 ≤ 2 * Cbase := by linarith
      _ = 2 * Cbase * 1 := (mul_one _).symm
      _ ≤ 2 * Cbase * Provider.BadEvents.sensitivityConstMax d ^ 2 :=
          mul_le_mul_of_nonneg_left h2 h3
  exact ⟨hEgamma, hcstarinv, hsmall, hwindow, hrate, hrateEllip, hhZ, hm, hhcast, hccg⟩

private theorem principalResponseTerminal_comparisonBounds2 :
    ∀ (d : ℕ) (_ : NeZero d) (Cload g2 : ℝ)
      (_ :
        ∀ (M : ABKModel d),
          M.gamma ≤ g2 →
            ∀ (m0 : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E }),
              Frozen.Section3.inductionState M m0 E →
                ∀ (m K : ℤ) (h : ℕ),
                  (0 : ℕ) < h →
                    m - (↑h : ℤ) ≤ m0 →
                      m - (1 : ℤ) ≤ m0 →
                        (↑h : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹ →
                          (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ) →
                            ∀ (e e' : Vec d),
                              Ch02.vecNorm e ≤ (1 : ℝ) →
                                Ch02.vecNorm e' ≤ (1 : ℝ) →
                                  ∀ (j : ℕ) (wD : CutoffSample d → H10Function (openCubeSet
                                    (originCube d K)))
                                    (wN : CutoffSample d → H1MeanZeroFunction (openCubeSet
                                      (originCube d K))),
                                    (∀ (z : CutoffSample d),
                                        IsZeroTraceDirichletRhsWeakSolution
                                          (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                            (openCubeSet (originCube d K))
                                          (wD z) fun (x : Vec d) =>
                                          -streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) :
                                            ℝ)⁻¹ (↑z : ShellSeq d)
                                              (m - (↑h : ℤ)) m e x) →
                                      (∀ (z : CutoffSample d),
                                          IsMeanZeroNeumannRhsWeakSolution
                                            (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                            (openCubeSet (originCube d K)) (wN z) fun (x : Vec d) =>
                                            -streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ)))
                                              : ℝ)⁻¹ (↑z : ShellSeq d)
                                                (m - (↑h : ℤ)) m e' x) →
                                        (∀ R ∈ descendantsAtDepth (originCube d K) j,
                                            Measurable fun (z : CutoffSample d) =>
                                              annealedSqrtNormSq (Annealed.sigmaBar M (m - (1 : ℤ)))
                                                  (principalPz (Annealed.sigmaBar M (m - (↑h :
                                                    ℤ))) (↑z : ShellSeq d)
                                                    (m - (↑h : ℤ)) m e e' R (wD z) (wN z)) ^
                                                (2 : ℕ)) →
                                          (∀ R ∈ descendantsAtDepth (originCube d K) j,
                                              Integrable
                                                (fun (z : CutoffSample d) =>
                                                  annealedSqrtNormSq (Annealed.sigmaBar M (m - (1
                                                    : ℤ)))
                                                      (principalPz (Annealed.sigmaBar M (m - (↑h :
                                                        ℤ))) (↑z : ShellSeq d)
                                                        (m - (↑h : ℤ)) m e e' R (wD z) (wN z)) ^
                                                    (2 : ℕ))
                                                (↑(cutoffSampleLaw M) : Measure (CutoffSample d))) →
                                            (descendantsAverage (originCube d K) j fun (R :
                                              TriadicCube d) =>
                                                  ∫ (z : CutoffSample d),
                                                    annealedSqrtNormSq (Annealed.sigmaBar M (m -
                                                      (1 : ℤ)))
                                                        (principalPz (Annealed.sigmaBar M (m - (↑h
                                                          : ℤ))) (↑z : ShellSeq d)
                                                          (m - (↑h : ℤ)) m e e' R (wD z) (wN z)) ^
                                                      (2 : ℕ) ∂(↑(cutoffSampleLaw M) : Measure
                                                        (CutoffSample d))) ^
                                                (1 / 4 : ℝ) ≤
                                              Cload)
      (g3 : ℝ)
      (_ :
        ∀ (M : ABKModel d),
          M.gamma ≤ g3 →
            ∀ (m0 : ℤ) (Eind : { E : ℝ // (1 : ℝ) ≤ E }),
              Frozen.Section3.inductionState M m0 Eind →
                ∀ (m K : ℤ) (hgap : ℕ),
                  (0 : ℕ) < hgap →
                    m - (↑hgap : ℤ) ≤ m0 →
                      (↑hgap : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹ →
                        (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ) →
                          ∀ (e e' : Vec d),
                            Ch02.vecNorm e ≤ (1 : ℝ) →
                              Ch02.vecNorm e' ≤ (1 : ℝ) →
                                ∀ (jd : ℕ),
                                  ∀ R ∈ descendantsAtDepth (originCube d K) jd,
                                    ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d K)))
                                      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet
                                        (originCube d K))),
                                      (∀ (omega : ShellSeq d),
                                          IsZeroTraceDirichletRhsWeakSolution
                                            (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                            (openCubeSet (originCube d K)) (wD omega) fun (x : Vec
                                              d) =>
                                            -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap :
                                              ℤ))) : ℝ)⁻¹ omega
                                                (m - (↑hgap : ℤ)) m e x) →
                                        (∀ (omega : ShellSeq d),
                                            IsMeanZeroNeumannRhsWeakSolution
                                              (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                              (openCubeSet (originCube d K)) (wN omega) fun (x :
                                                Vec d) =>
                                              -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap :
                                                ℤ))) : ℝ)⁻¹ omega
                                                  (m - (↑hgap : ℤ)) m e' x) →
                                          Integrable
                                            (fun (omega : ShellSeq d) =>
                                              switchEllipLoad (↑(Annealed.sigmaBar M (m - (↑hgap :
                                                ℤ))) : ℝ)
                                                  (principalPz (Annealed.sigmaBar M (m - (↑hgap :
                                                    ℤ))) omega
                                                    (m - (↑hgap : ℤ)) m e e' R (wD omega) (wN
                                                      omega)) ^
                                                (2 : ℕ))
                                            (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d)))
      (M : ABKModel d) (m Kc : ℤ) (hgap : ℕ) (E : { E : ℝ // (1 : ℝ) ≤ E })
      (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) (_ : (0 : ℕ) < hgap)
      (_ : (↑hgap : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹)
      (_ : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑Kc : ℝ) - (↑m : ℝ)) (e e' : Vec d) (_ :
        Ch02.vecNorm e ≤ (1 : ℝ))
      (_ : Ch02.vecNorm e' ≤ (1 : ℝ)) (j : ℕ) (_ : M.gamma ≤ g2) (_ : M.gamma ≤ g3)
      (_ : m - (↑hgap : ℤ) ≤ m - (1 : ℤ)) (wD : ShellSeq d → H10Function (openCubeSet (originCube
        d Kc)))
      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
      (_ :
        ∀ (omega : ShellSeq d),
          IsZeroTraceDirichletRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
            (openCubeSet (originCube d Kc)) (wD omega) fun (x : Vec d) =>
            -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap : ℤ))) : ℝ)⁻¹ omega (m - (↑hgap :
              ℤ)) m e x)
      (_ :
        ∀ (omega : ShellSeq d),
          IsMeanZeroNeumannRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
            (openCubeSet (originCube d Kc)) (wN omega) fun (x : Vec d) =>
            -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap : ℤ))) : ℝ)⁻¹ omega (m - (↑hgap :
              ℤ)) m e' x),
      MeasurableEmbedding (Subtype.val : CutoffSample d → ShellSeq d) ∧
        (∀ R ∈ descendantsAtDepth (originCube d Kc) j,
            Measurable fun (z : CutoffSample d) =>
              principalPz (Annealed.sigmaBar M (m - (↑hgap : ℤ))) (↑z : ShellSeq d) (m - (↑hgap :
                ℤ)) m e e' R
                (wD (↑z : ShellSeq d)) (wN (↑z : ShellSeq d))) ∧
          (∀ (s : Observable.PositiveScalar) (F : CutoffSample d → BlockVec d),
              Measurable F → Measurable fun (z : CutoffSample d) => annealedSqrtNormSq s (F z)) ∧
            (∀ R ∈ descendantsAtDepth (originCube d Kc) j,
                Integrable
                  (fun (z : CutoffSample d) =>
                    annealedSqrtNormSq (Annealed.sigmaBar M (m - (1 : ℤ)))
                        (principalPz (Annealed.sigmaBar M (m - (↑hgap : ℤ))) (↑z : ShellSeq d) (m
                          - (↑hgap : ℤ)) m e e' R
                          (wD (↑z : ShellSeq d)) (wN (↑z : ShellSeq d))) ^
                      (2 : ℕ))
                  (↑(cutoffSampleLaw M) : Measure (CutoffSample d))) ∧
              (descendantsAverage (originCube d Kc) j fun (R : TriadicCube d) =>
                  ∫ (z : CutoffSample d),
                    annealedSqrtNormSq (Annealed.sigmaBar M (m - (1 : ℤ)))
                        (principalPz (Annealed.sigmaBar M (m - (↑hgap : ℤ))) (↑z : ShellSeq d) (m
                          - (↑hgap : ℤ)) m e e' R
                          (wD (↑z : ShellSeq d)) (wN (↑z : ShellSeq d))) ^
                      (2 : ℕ) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d))) ≤
                Cload ^ (4 : ℕ) := by
  intro d _ Cload _ hdisp2 _ hSqInt M m Kc hgap E hstate hhpos hh hK e e' he he' j hg2 hg3 hm wD
    wN hwD hwN
  have hemb : MeasurableEmbedding (Subtype.val : CutoffSample d → ShellSeq d) :=
    MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)
  have hPzmeas : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Measurable (fun z : Cutoff.CutoffSample d =>
        principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val (m - (hgap : ℤ)) m
          e e' R (wD z.val) (wN z.val)) := by
    intro R hR
    exact ((measurable_shellIndexSigma_principalPz hR
      (Annealed.sigmaBar M (m - (hgap : ℤ)))
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
      (m - (hgap : ℤ)) m e e' e e' wD wN hwD hwN).mono
      (Cutoff.shellIndexSigma_le_borel _) le_rfl).comp measurable_subtype_coe
  have hvns : ∀ f : Cutoff.CutoffSample d → Vec d, Measurable f →
      Measurable fun z => vecNormSq (f z) := by
    intro f hf
    have hEq : (fun z => vecNormSq (f z)) = fun z => ∑ i, f z i * f z i := rfl
    rw [hEq]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hf)
  have hann : ∀ (s : Observable.PositiveScalar) (F : Cutoff.CutoffSample d → BlockVec d),
      Measurable F → Measurable fun z => annealedSqrtNormSq s (F z) := by
    intro s F hF
    have hEq : (fun z => annealedSqrtNormSq s (F z)) =
        fun z => (s : ℝ) * vecNormSq (F z).1 + ((s : ℝ))⁻¹ * vecNormSq (F z).2 := rfl
    rw [hEq]
    exact (measurable_const.mul (hvns _ hF.fst)).add
      (measurable_const.mul (hvns _ hF.snd))
  -- the load square at the reading gauge, through the gauge bridge
  have hVint : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Integrable (fun z : Cutoff.CutoffSample d =>
        annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) ^ (2 : ℕ))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro R hR
    have hsh := hSqInt M hg3 (m - 1) E hstate m Kc hgap hhpos hm hh hK e e' he he' j R hR
      wD wN hwD hwN
    rw [← map_cutoffSampleLaw_val M, hemb.integrable_map_iff] at hsh
    have hload : Integrable (fun z : Cutoff.CutoffSample d =>
        annealedSqrtNormSq (Annealed.sigmaBar M (m - (hgap : ℤ)))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) ^ (2 : ℕ))
        (Cutoff.cutoffSampleLaw M).toMeasure := hsh
    refine Integrable.mono'
      (hload.const_mul (gaugeRatio (Annealed.sigmaBar M (m - (hgap : ℤ)))
        (Annealed.sigmaBar M (m - 1)) ^ 2))
      ((hann _ _ (hPzmeas R hR)).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have hb := sq_annealedSqrtNormSq_le_gaugeRatio_sq_mul
      (Annealed.sigmaBar M (m - (hgap : ℤ))) (Annealed.sigmaBar M (m - 1))
      (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
        (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val))
    have h0 : (0 : ℝ) ≤ annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
          (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) ^ (2 : ℕ) := by positivity
    rw [Real.norm_of_nonneg h0]
    exact hb
  -- the fourth-moment display, in grid form
  have hmeasR : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Measurable (fun z : Cutoff.CutoffSample d =>
        annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) ^ (2 : ℕ)) :=
    fun R hR => (hann _ _ (hPzmeas R hR)).pow_const 2
  have hd2 := hdisp2 M hg2 (m - 1) E hstate m Kc hgap hhpos hm le_rfl hh hK e e' he he' j
    (fun z : Cutoff.CutoffSample d => wD z.val)
    (fun z : Cutoff.CutoffSample d => wN z.val)
    (fun z => hwD z.val) (fun z => hwN z.val) hmeasR hVint
  have havgnn : (0 : ℝ) ≤ descendantsAverage (originCube d Kc) j
      (fun R => ∫ z : Cutoff.CutoffSample d,
        annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) ^ (2 : ℕ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) :=
    descendantsAverage_nonneg (originCube d Kc) j _ fun R _ =>
      integral_nonneg fun z => pow_nonneg (annealedSqrtNormSq_nonneg _ _) 2
  have havg : descendantsAverage (originCube d Kc) j
      (fun R => ∫ z : Cutoff.CutoffSample d,
        annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) ^ (2 : ℕ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ Cload ^ (4 : ℕ) := by
    have hstep := Real.rpow_le_rpow (Real.rpow_nonneg havgnn _) hd2
      (by norm_num : (0 : ℝ) ≤ 4)
    rw [← Real.rpow_mul havgnn] at hstep
    have h4 : ((1 : ℝ) / 4) * 4 = 1 := by norm_num
    rw [h4, Real.rpow_one] at hstep
    have hc4 : Cload ^ (4 : ℝ) = Cload ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast Cload 4]
      norm_num
    rwa [hc4] at hstep
  exact ⟨hemb, hPzmeas, hann, hVint, havg⟩

private theorem principalResponseTerminal_comparisonBounds3 :
    ∀ (d : ℕ) (_ : NeZero d) (Cbase c C : ℝ)
      (_ :
        ∀ (M : ABKModel d) (E : { E : ℝ // (1 : ℝ) ≤ E }) (m h : ℤ) (Q : TriadicCube d) (j : ℕ)
          (P : TriadicCube d → CutoffSample d → BlockVec d) (Cv : ℝ),
          Frozen.Section3.inductionState M (m - (1 : ℤ)) E →
            (0 : ℤ) < h →
              Q.scale - (↑j : ℤ) = recurrenceMesoScale recurrenceGapMultiplier M.gamma m h →
                max (Real.exp ((2 : ℝ) * C)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ) →
                  c⁻¹ * (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ) →
                    (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
                      M.gamma / (2 : ℝ) + Real.exp (-(C⁻¹ * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)) ≤
                        M.gamma →
                        M.gamma ≤ (1 / 1089 : ℝ) →
                          (↑h : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹ →
                            (0 : ℝ) < Cv →
                              (∀ R ∈ descendantsAtDepth Q j,
                                  AEStronglyMeasurable
                                    (fun (omega : CutoffSample d) => switchCubeEnergy M m R (P R
                                      omega) omega)
                                    (↑(cutoffSampleLaw M) : Measure (CutoffSample d))) →
                                (∀ R ∈ descendantsAtDepth Q j,
                                    AEStronglyMeasurable
                                      (fun (omega : CutoffSample d) =>
                                        √(annealedSqrtNormSq (Annealed.sigmaBar M (m - (1 : ℤ)))
                                          (P R omega)))
                                      (↑(cutoffSampleLaw M) : Measure (CutoffSample d))) →
                                  (∀ R ∈ descendantsAtDepth Q j,
                                      Integrable
                                        (fun (omega : CutoffSample d) =>
                                          annealedSqrtNormSq (Annealed.sigmaBar M (m - (1 : ℤ)))
                                            (P R omega) ^ (2 : ℕ))
                                        (↑(cutoffSampleLaw M) : Measure (CutoffSample d))) →
                                    (descendantsAverage Q j fun (R : TriadicCube d) =>
                                          ∫ (omega : CutoffSample d),
                                            annealedSqrtNormSq (Annealed.sigmaBar M (m - (1 : ℤ)))
                                              (P R omega) ^
                                              (2 : ℕ) ∂(↑(cutoffSampleLaw M) : Measure
                                                (CutoffSample d))) ≤
                                        Cv ^ (4 : ℕ) →
                                      M.gamma⁻¹ + Real.log (2 : ℝ) ≤
                                          c * Disorder.cstar M * M.gamma⁻¹ *
                                            (3 : ℝ) ^ (↑(recurrenceGap recurrenceGapMultiplier
                                              M.gamma) : ℝ) →
                                        M.gamma⁻¹ + Real.log (2 : ℝ) ≤ Real.exp (c * (↑E : ℝ)⁻¹ ^
                                          (2 : ℕ) * M.gamma⁻¹) →
                                          (Disorder.cstar M)⁻¹ ≤ M.gamma⁻¹ →
                                            M.gamma ≤
                                                ((2 : ℝ) * ((3 : ℝ) ^ (22 : ℝ) * ((2 : ℝ) * C) *
                                                  Cv ^ (2 : ℕ)) *
                                                    (24 : ℝ) ^ (9 : ℕ))⁻¹ →
                                              (∀ R ∈ descendantsAtDepth Q j,
                                                  Integrable
                                                    (fun (omega : CutoffSample d) =>
                                                      switchCubeEnergy M m R (P R omega) omega *
                                                        (principalBadEvent M ((2 : ℝ) * Cbase) R
                                                          (m - h)).indicator
                                                          (fun (_ : CutoffSample d) => (1 : ℝ))
                                                            omega)
                                                    (↑(cutoffSampleLaw M) : Measure (CutoffSample
                                                      d))) ∧
                                                (descendantsAverage Q j fun (R : TriadicCube d) =>
                                                    ∫ (omega : CutoffSample d),
                                                      switchCubeEnergy M m R (P R omega) omega *
                                                        (principalBadEvent M ((2 : ℝ) * Cbase) R
                                                          (m - h)).indicator
                                                          (fun (_ : CutoffSample d) => (1 : ℝ))
                                                          omega ∂(↑(cutoffSampleLaw M) : Measure
                                                            (CutoffSample d))) ≤
                                                  M.gamma ^ (6 : ℕ) / (2 : ℝ))
      (Cload : ℝ) (_ : (0 : ℝ) < Cload) (g2 : ℝ)
      (_ :
        ∀ (M : ABKModel d),
          M.gamma ≤ g2 →
            ∀ (m0 : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E }),
              Frozen.Section3.inductionState M m0 E →
                ∀ (m K : ℤ) (h : ℕ),
                  (0 : ℕ) < h →
                    m - (↑h : ℤ) ≤ m0 →
                      m - (1 : ℤ) ≤ m0 →
                        (↑h : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹ →
                          (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ) →
                            ∀ (e e' : Vec d),
                              Ch02.vecNorm e ≤ (1 : ℝ) →
                                Ch02.vecNorm e' ≤ (1 : ℝ) →
                                  ∀ (j : ℕ) (wD : CutoffSample d → H10Function (openCubeSet
                                    (originCube d K)))
                                    (wN : CutoffSample d → H1MeanZeroFunction (openCubeSet
                                      (originCube d K))),
                                    (∀ (z : CutoffSample d),
                                        IsZeroTraceDirichletRhsWeakSolution
                                          (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                            (openCubeSet (originCube d K))
                                          (wD z) fun (x : Vec d) =>
                                          -streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) :
                                            ℝ)⁻¹ (↑z : ShellSeq d)
                                              (m - (↑h : ℤ)) m e x) →
                                      (∀ (z : CutoffSample d),
                                          IsMeanZeroNeumannRhsWeakSolution
                                            (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                            (openCubeSet (originCube d K)) (wN z) fun (x : Vec d) =>
                                            -streamForcing (↑(Annealed.sigmaBar M (m - (↑h : ℤ)))
                                              : ℝ)⁻¹ (↑z : ShellSeq d)
                                                (m - (↑h : ℤ)) m e' x) →
                                        (∀ R ∈ descendantsAtDepth (originCube d K) j,
                                            Measurable fun (z : CutoffSample d) =>
                                              annealedSqrtNormSq (Annealed.sigmaBar M (m - (1 : ℤ)))
                                                  (principalPz (Annealed.sigmaBar M (m - (↑h :
                                                    ℤ))) (↑z : ShellSeq d)
                                                    (m - (↑h : ℤ)) m e e' R (wD z) (wN z)) ^
                                                (2 : ℕ)) →
                                          (∀ R ∈ descendantsAtDepth (originCube d K) j,
                                              Integrable
                                                (fun (z : CutoffSample d) =>
                                                  annealedSqrtNormSq (Annealed.sigmaBar M (m - (1
                                                    : ℤ)))
                                                      (principalPz (Annealed.sigmaBar M (m - (↑h :
                                                        ℤ))) (↑z : ShellSeq d)
                                                        (m - (↑h : ℤ)) m e e' R (wD z) (wN z)) ^
                                                    (2 : ℕ))
                                                (↑(cutoffSampleLaw M) : Measure (CutoffSample d))) →
                                            (descendantsAverage (originCube d K) j fun (R :
                                              TriadicCube d) =>
                                                  ∫ (z : CutoffSample d),
                                                    annealedSqrtNormSq (Annealed.sigmaBar M (m -
                                                      (1 : ℤ)))
                                                        (principalPz (Annealed.sigmaBar M (m - (↑h
                                                          : ℤ))) (↑z : ShellSeq d)
                                                          (m - (↑h : ℤ)) m e e' R (wD z) (wN z)) ^
                                                      (2 : ℕ) ∂(↑(cutoffSampleLaw M) : Measure
                                                        (CutoffSample d))) ^
                                                (1 / 4 : ℝ) ≤
                                              Cload)
      (g3 : ℝ)
      (_ :
        ∀ (M : ABKModel d),
          M.gamma ≤ g3 →
            ∀ (m0 : ℤ) (Eind : { E : ℝ // (1 : ℝ) ≤ E }),
              Frozen.Section3.inductionState M m0 Eind →
                ∀ (m K : ℤ) (hgap : ℕ),
                  (0 : ℕ) < hgap →
                    m - (↑hgap : ℤ) ≤ m0 →
                      (↑hgap : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹ →
                        (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ) →
                          ∀ (e e' : Vec d),
                            Ch02.vecNorm e ≤ (1 : ℝ) →
                              Ch02.vecNorm e' ≤ (1 : ℝ) →
                                ∀ (jd : ℕ),
                                  ∀ R ∈ descendantsAtDepth (originCube d K) jd,
                                    ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d K)))
                                      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet
                                        (originCube d K))),
                                      (∀ (omega : ShellSeq d),
                                          IsZeroTraceDirichletRhsWeakSolution
                                            (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                            (openCubeSet (originCube d K)) (wD omega) fun (x : Vec
                                              d) =>
                                            -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap :
                                              ℤ))) : ℝ)⁻¹ omega
                                                (m - (↑hgap : ℤ)) m e x) →
                                        (∀ (omega : ShellSeq d),
                                            IsMeanZeroNeumannRhsWeakSolution
                                              (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                              (openCubeSet (originCube d K)) (wN omega) fun (x :
                                                Vec d) =>
                                              -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap :
                                                ℤ))) : ℝ)⁻¹ omega
                                                  (m - (↑hgap : ℤ)) m e' x) →
                                          Integrable
                                            (fun (omega : ShellSeq d) =>
                                              switchEllipLoad (↑(Annealed.sigmaBar M (m - (↑hgap :
                                                ℤ))) : ℝ)
                                                  (principalPz (Annealed.sigmaBar M (m - (↑hgap :
                                                    ℤ))) omega
                                                    (m - (↑hgap : ℤ)) m e e' R (wD omega) (wN
                                                      omega)) ^
                                                (2 : ℕ))
                                            (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField d)))
      (g4 : ℝ)
      (_ :
        ∀ (M : ABKModel d),
          M.gamma ≤ g4 →
            ∀ (m0 : ℤ) (Eind : { E : ℝ // (1 : ℝ) ≤ E }),
              Frozen.Section3.inductionState M m0 Eind →
                ∀ (m K : ℤ) (hgap : ℕ),
                  (0 : ℕ) < hgap →
                    m - (↑hgap : ℤ) ≤ m0 →
                      (↑hgap : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹ →
                        (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ) →
                          ∀ (e e' : Vec d),
                            Ch02.vecNorm e ≤ (1 : ℝ) →
                              Ch02.vecNorm e' ≤ (1 : ℝ) →
                                ∀ (jd : ℕ),
                                  ∀ R ∈ descendantsAtDepth (originCube d K) jd,
                                    ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d K)))
                                      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet
                                        (originCube d K))),
                                      (∀ (omega : ShellSeq d),
                                          IsZeroTraceDirichletRhsWeakSolution
                                            (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                            (openCubeSet (originCube d K)) (wD omega) fun (x : Vec
                                              d) =>
                                            -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap :
                                              ℤ))) : ℝ)⁻¹ omega
                                                (m - (↑hgap : ℤ)) m e x) →
                                        (∀ (omega : ShellSeq d),
                                            IsMeanZeroNeumannRhsWeakSolution
                                              (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
                                              (openCubeSet (originCube d K)) (wN omega) fun (x :
                                                Vec d) =>
                                              -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap :
                                                ℤ))) : ℝ)⁻¹ omega
                                                  (m - (↑hgap : ℤ)) m e' x) →
                                          ∀ (alpha beta : BlockCoord d),
                                            Integrable
                                              (fun (omega : ShellSeq d) =>
                                                toFullBlockVec
                                                    (gaugedPrincipalLoadShell (Annealed.sigmaBar M
                                                      (m - (↑hgap : ℤ))) R
                                                      (m - (↑hgap : ℤ)) m e e' wD wN omega)
                                                    alpha *
                                                  toFullBlockVec
                                                    (gaugedPrincipalLoadShell (Annealed.sigmaBar M
                                                      (m - (↑hgap : ℤ))) R
                                                      (m - (↑hgap : ℤ)) m e e' wD wN omega)
                                                    beta)
                                              (↑M.P : Measure (ℤ → Frozen.Assumptions.ShellField
                                                d)))
      (Cterm : ℝ) (_ : (3 / 2 : ℝ) * principalResponseBudgetConst⁻¹ ≤ Cterm) (M : ABKModel d) (m
        Kc : ℤ) (hgap : ℕ)
      (E : { E : ℝ // (1 : ℝ) ≤ E }) (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) (_ :
        (0 : ℕ) < hgap)
      (_ : M.gamma ≤ (↑E : ℝ) ^ (-5 : ℤ)) (_ : (↑hgap : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹)
      (_ : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑Kc : ℝ) - (↑m : ℝ)) (e e' : Vec d) (_ :
        Ch02.vecNorm e ≤ (1 : ℝ))
      (_ : Ch02.vecNorm e' ≤ (1 : ℝ)) (j : ℕ)
      (_ : (originCube d Kc).scale - (↑j : ℤ) = recurrenceMesoScale recurrenceGapMultiplier
        M.gamma m (↑hgap : ℤ))
      (_ : (0 : ℝ) < M.gamma) (_ : (1 : ℝ) ≤ (↑E : ℝ))
      (_ : ∀ (T : ℝ), (0 : ℝ) ≤ T → T ≤ Cterm → T * (2 / 3 : ℝ) ≤ (↑E : ℝ)) (_ : (↑E : ℝ) ≤
        M.gamma⁻¹)
      (_ : M.gamma ≤ g2) (_ : M.gamma ≤ g3) (_ : M.gamma ≤ g4) (_ : M.gamma ≤ (1 / 1089 : ℝ))
      (_ : max (Real.exp ((2 : ℝ) * C)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ)) (_ : c⁻¹ *
        (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
      (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (_ : (Disorder.cstar M)⁻¹ ≤ M.gamma⁻¹)
      (_ : M.gamma ≤ ((2 : ℝ) * ((3 : ℝ) ^ (22 : ℝ) * ((2 : ℝ) * C) * Cload ^ (2 : ℕ)) * (24 : ℝ)
        ^ (9 : ℕ))⁻¹)
      (_ : M.gamma / (2 : ℝ) + Real.exp (-(C⁻¹ * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)) ≤ M.gamma)
      (_ :
        M.gamma⁻¹ + Real.log (2 : ℝ) ≤
          c * Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ (↑(recurrenceGap recurrenceGapMultiplier
            M.gamma) : ℝ))
      (_ : M.gamma⁻¹ + Real.log (2 : ℝ) ≤ Real.exp (c * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))
      (_ : (0 : ℤ) < (↑hgap : ℤ)) (_ : m - (↑hgap : ℤ) ≤ m - (1 : ℤ))
      (_ : (↑(↑hgap : ℤ) : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹)
      (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
      (_ :
        ∀ (omega : ShellSeq d),
          IsZeroTraceDirichletRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
            (openCubeSet (originCube d Kc)) (wD omega) fun (x : Vec d) =>
            -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap : ℤ))) : ℝ)⁻¹ omega (m - (↑hgap :
              ℤ)) m e x)
      (_ :
        ∀ (omega : ShellSeq d),
          IsMeanZeroNeumannRhsWeakSolution (fun (_ : Vec d) => (1 : Matrix (Fin d) (Fin d) ℝ))
            (openCubeSet (originCube d Kc)) (wN omega) fun (x : Vec d) =>
            -streamForcing (↑(Annealed.sigmaBar M (m - (↑hgap : ℤ))) : ℝ)⁻¹ omega (m - (↑hgap :
              ℤ)) m e' x),
      ∃ (_ :
        ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
          Integrable
            (fun (omega : CutoffSample d) =>
              switchCubeEnergy M m R
                  (principalPz (Annealed.sigmaBar M (m - (↑hgap : ℤ))) (↑omega : ShellSeq d) (m -
                    (↑hgap : ℤ)) m e e' R
                    (wD (↑omega : ShellSeq d)) (wN (↑omega : ShellSeq d)))
                  omega *
                (principalBadEvent M ((2 : ℝ) * Cbase) R (m - (↑hgap : ℤ))).indicator (fun (_ :
                  CutoffSample d) => (1 : ℝ))
                  omega)
            (↑(cutoffSampleLaw M) : Measure (CutoffSample d)))
        (_ :
        (descendantsAverage (originCube d Kc) j fun (R : TriadicCube d) =>
            ∫ (omega : CutoffSample d),
              switchCubeEnergy M m R
                  (principalPz (Annealed.sigmaBar M (m - (↑hgap : ℤ))) (↑omega : ShellSeq d) (m -
                    (↑hgap : ℤ)) m e e' R
                    (wD (↑omega : ShellSeq d)) (wN (↑omega : ShellSeq d)))
                  omega *
                (principalBadEvent M ((2 : ℝ) * Cbase) R (m - (↑hgap : ℤ))).indicator (fun (_ :
                  CutoffSample d) => (1 : ℝ))
                  omega ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d))) ≤
          M.gamma ^ (6 : ℕ) / (2 : ℝ))
        (_ :
        ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
          Integrable
            (fun (z : CutoffSample d) =>
              blockVecDot
                (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (↑hgap : ℤ))) R (m - (↑hgap :
                  ℤ)) m e e' wD wN
                  (↑z : ShellSeq d))
                (blockMatVecMul
                  (Ch02.blockDiag ((↑(Annealed.sigmaBar M (m - (↑hgap : ℤ))) : ℝ) • (1 : Mat d))
                    ((↑(Annealed.sigmaBar M (m - (↑hgap : ℤ))) : ℝ)⁻¹ • (1 : Mat d)))
                  (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (↑hgap : ℤ))) R (m - (↑hgap
                    : ℤ)) m e e' wD wN
                    (↑z : ShellSeq d))))
            (↑(cutoffSampleLaw M) : Measure (CutoffSample d)))
        (_ :
        ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
          Integrable
            (fun (z : CutoffSample d) =>
              blockVecDot
                (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (↑hgap : ℤ))) R (m - (↑hgap :
                  ℤ)) m e e' wD wN
                  (↑z : ShellSeq d))
                (blockMatVecMul
                  (Ch04.annealedBlockMatrixAtScale (coefficientCutoffLaw M (m - (↑hgap : ℤ)))
                    ((originCube d Kc).scale - (↑j : ℤ)))
                  (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (↑hgap : ℤ))) R (m - (↑hgap
                    : ℤ)) m e e' wD wN
                    (↑z : ShellSeq d))))
            (↑(cutoffSampleLaw M) : Measure (CutoffSample d)))
        (_ : m - (↑hgap : ℤ) ≤ m - (1 : ℤ)) (_ : (originCube d Kc).scale - (↑j : ℤ) ≤ m - (↑hgap :
          ℤ)) (_ :
        M.gamma ≤ ((↑E : ℝ) ^ (5 : ℕ))⁻¹) (_ : |Real.log M.gamma|⁻¹ ∈ Set.Icc ((8 : ℝ) * M.gamma)
          (1 : ℝ)) (Ev : BlockVec d)
        (_ : blockVecDot Ev Ev = (1 : ℝ)) (_ :
        |Real.log M.gamma|⁻¹ * (↑(m - (↑hgap : ℤ) - ((originCube d Kc).scale - (↑j : ℤ))).toNat :
          ℝ) ≤ (64 : ℝ)),
        M.gamma ^ (6 : ℕ) ≤ principalResponseSwitchBudget M E (64 : ℝ) := by
  classical
  intro d this Cbase _ C hbadhalf Cload hCload0 g2 hdisp2 g3 hSqInt _ hWint Cterm hTb M m Kc hgap
    E hstate hhpos hgammaE hh hK e e' he he' j hscale hgamma0 hE1 hproj hEinv hg2 hg3 hg4
      hgamma1089 hEexp hEadm hEgamma hcstarinv hsmall hwindow hrate hrateEllip hhZ hm hhcast wD wN
        hwD hwN
  obtain ⟨hemb, hPzmeas, hann, hVint, havg⟩ :=
    (show (MeasurableEmbedding (Subtype.val : CutoffSample d → ShellSeq d)) ∧ (∀ R ∈
      descendantsAtDepth (originCube d Kc) j,
      Measurable (fun z : Cutoff.CutoffSample d =>
        principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val (m - (hgap : ℤ)) m
          e e' R (wD z.val) (wN z.val))) ∧ (∀ (s : Observable.PositiveScalar) (F :
            Cutoff.CutoffSample d → BlockVec d),
      Measurable F → Measurable fun z => annealedSqrtNormSq s (F z)) ∧ (∀ R ∈ descendantsAtDepth
        (originCube d Kc) j,
      Integrable (fun z : Cutoff.CutoffSample d =>
        annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) ^ (2 : ℕ))
        (Cutoff.cutoffSampleLaw M).toMeasure) ∧ (descendantsAverage (originCube d Kc) j
      (fun R => ∫ z : Cutoff.CutoffSample d,
        annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val)) ^ (2 : ℕ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ Cload ^ (4 : ℕ)) from
      @principalResponseTerminal_comparisonBounds2 (d) (this) (Cload) (g2) (hdisp2) (g3) (hSqInt)
        (M) (m) (Kc) (hgap) (E) (hstate) (hhpos) (hh) (hK) (e) (e') (he) (he') (j) (hg2) (hg3)
          (hm) (wD) (wN) (hwD) (hwN))
  -- the bad half, already inside the half budget
  obtain ⟨hbadInt, hbad⟩ := hbadhalf M E m (hgap : ℤ) (originCube d Kc) j
    (fun R z => principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
      (m - (hgap : ℤ)) m e e' R (wD z.val) (wN z.val))
    Cload hstate hhZ hscale hEexp hEadm hEgamma hwindow hgamma1089 hhcast hCload0
    (fun R hR => aestronglyMeasurable_switchCubeEnergy M m R (hPzmeas R hR))
    (fun R hR => (Real.continuous_sqrt.measurable.comp
      (hann _ _ (hPzmeas R hR))).aestronglyMeasurable)
    hVint havg hrate hrateEllip hcstarinv hsmall
  -- the two quadratic forms of the recombination
  have hWentry : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      ∀ alpha beta : BlockCoord d,
        Integrable (fun z : Cutoff.CutoffSample d =>
          toFullBlockVec (gaugedPrincipalLoadShell
              (Annealed.sigmaBar M (m - (hgap : ℤ))) R (m - (hgap : ℤ)) m e e' wD wN
              z.val) alpha *
            toFullBlockVec (gaugedPrincipalLoadShell
              (Annealed.sigmaBar M (m - (hgap : ℤ))) R (m - (hgap : ℤ)) m e e' wD wN
              z.val) beta)
          (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro R hR alpha beta
    have hsh := hWint M hg4 (m - 1) E hstate m Kc hgap hhpos hm hh hK e e' he he' j R hR
      wD wN hwD hwN alpha beta
    rw [← map_cutoffSampleLaw_val M, hemb.integrable_map_iff] at hsh
    exact hsh
  have hlimInt : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Integrable (fun z : Cutoff.CutoffSample d =>
        blockVecDot
          (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
            (m - (hgap : ℤ)) m e e' wD wN z.val)
          (blockMatVecMul
            (Ch02.blockDiag
              ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ) • (1 : Mat d))
              (((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ • (1 : Mat d)))
            (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
              (m - (hgap : ℤ)) m e e' wD wN z.val)))
        (Cutoff.cutoffSampleLaw M).toMeasure := fun R hR =>
    integrable_blockVecDot_blockDiag_smul_one_of_entries _ _ _ (hWentry R hR)
  obtain ⟨sUp, sLow, hst⟩ :=
    Provider.Annealed.coefficientCutoffLaw_exists_annealedBlockMatrixAtScale_eq_blockDiag_smul_one
      M (m - (hgap : ℤ)) (((originCube d Kc).scale : ℤ) - (j : ℤ))
  have hcubeInt : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Integrable (fun z : Cutoff.CutoffSample d =>
        blockVecDot
          (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
            (m - (hgap : ℤ)) m e e' wD wN z.val)
          (blockMatVecMul
            (Ch04.annealedBlockMatrixAtScale
              (Cutoff.coefficientCutoffLaw M (m - (hgap : ℤ)))
              (((originCube d Kc).scale : ℤ) - (j : ℤ)))
            (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
              (m - (hgap : ℤ)) m e e' wD wN z.val)))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro R hR
    rw [hst]
    exact integrable_blockVecDot_blockDiag_smul_one_of_entries _ sUp sLow (hWentry R hR)
  -- the gates of the recombination
  have hL : m - (hgap : ℤ) ≤ m - 1 := hm
  have hn : ((originCube d Kc).scale : ℤ) - (j : ℤ) ≤ m - (hgap : ℤ) := by
    rw [hscale]
    exact recurrenceMesoScale_le _ _ _ _
  have hgamE : M.gamma ≤ ((E : ℝ) ^ 5)⁻¹ := by
    have hEpow : (E : ℝ) ^ (-5 : ℤ) = ((E : ℝ) ^ (5 : ℕ))⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rwa [hEpow] at hgammaE
  have hsw := inv_abs_log_mem_Icc hgamma0 hgamma1089
  obtain ⟨Ev, hEv⟩ := exists_blockVecDot_self_eq_one (d := d)
  have hLn : m - (hgap : ℤ) - (((originCube d Kc).scale : ℤ) - (j : ℤ)) =
      ((recurrenceGap recurrenceGapMultiplier M.gamma : ℕ) : ℤ) := by
    rw [hscale]
    exact sub_recurrenceMesoScale _ _ _ _
  have hgapK : |Real.log M.gamma|⁻¹ *
      ((Int.toNat (m - (hgap : ℤ) - (((originCube d Kc).scale : ℤ) - (j : ℤ))) : ℕ) : ℝ) ≤
      64 := by
    rw [hLn, Int.toNat_natCast]
    exact windowExponent_recurrenceGap_le_sixtyFour hgamma0 (by linarith)
  have hCbud : M.gamma ≤ principalResponseBudgetConst := by
    have hb0 : (0 : ℝ) < principalResponseBudgetConst := principalResponseBudgetConst_pos
    have hbinv0 : (0 : ℝ) < principalResponseBudgetConst⁻¹ := inv_pos.2 hb0
    have h := hproj ((3 / 2) * principalResponseBudgetConst⁻¹) (by positivity) hTb
    have hid : ((3 / 2) * principalResponseBudgetConst⁻¹) * (2 / 3) =
        principalResponseBudgetConst⁻¹ := by ring
    have hle : principalResponseBudgetConst⁻¹ ≤ M.gamma⁻¹ := by
      linarith [hEinv]
    rw [← inv_inv principalResponseBudgetConst, le_inv_comm₀ hgamma0 hbinv0]
    exact hle
  have hrename : M.gamma ^ (6 : ℕ) ≤ principalResponseSwitchBudget M E 64 := by
    rw [principalResponseSwitchBudget]
    exact pow_six_le_budget_core hgamma0 (by linarith) hCbud hE1 (by norm_num)
  exact ⟨hbadInt, hbad, hlimInt, hcubeInt, hL, hn, hgamE, hsw, Ev, hEv, hgapK, hrename⟩

/-- **The principal-response comparison of `l.approximate.recurrence.formula`,
Step 3, at one and the same witness.**

For a single constant `Cterm` fixed before the model --- the manuscript's own
`C(d)` --- every model, every induction state `S(m - 1, E)`, and every scale
datum of `e.recurrence.params` carry one pair of solutions `wD`, `wN` of the
two problems `e.def.w` (label), produced existentially together with those
properties, for which the grid average of the localized principal energy obeys

```
  avsum_R E[ P_R . bfA_m(R) P_R ]
    <= (1 + 3 principalResponseSwitchBudget M E 64)
         avsum_R E[ W_R . bfAhom_{m-h} W_R ]
       + cgamma^6 ,
```

where `principalResponseSwitchBudget M E 64 = C 3^128 E^2 (log cgamma)^2 cgamma`
carries an absolute constant; no factor of the conclusion depends on
`cgamma` except through the printed `|log cgamma|^2 cgamma`.  There is **no**
separate smallness binder on `cgamma`: every threshold the proof needs is
forced by `Cterm (cstar M)^{-1} <= E`, `cstar M <= 3/2` and `cgamma <= E^{-5}`,
which is exactly the manuscript's "increasing `M` in `e.cgamma.constraints` if
necessary".

with `W_R = G_{-(h)_R} P_R` the gauged load and `principalResponseSwitchBudget`
the named form of the printed factor `C E^2 |log cgamma|^2 cgamma`.  This is the
target display `e.lower.bound.principal.one` (label) at the localization data
of this repository -- one combined comparison, not a pair of good/bad estimates
and not a raw two-exponential tail.

## The two surviving analytic premises

They are the two premises of `l.approximate.recurrence.formula` itself: one
constant fixed before the model times `(cstar M)^{-1}` below `E`, and
`cgamma <= E^{-5}`.  Neither is contained in
`Algsuperdiff.Frozen.Section3.inductionState`, which binds only `1 <= E`, and
neither is carried by the frozen induction command; at the frozen root the
corresponding scale premise is the stronger `cgamma <= (E^{-1})^{10}`, from
which the `cgamma <= E^{-5}` read here is obtained in the root assembly.

Everything else the two halves and the recombination ask for -- the two
admissibility gates, the fifth-root gate, the window, the two rate gates, the
tail domination, the moment envelope's smallness gate, the four sub-packages'
own `cgamma`-thresholds, the rename gate, and every measurability,
integrability and `MemLp` proposition -- is discharged inside the proof.  None
of them survives as a binder.  In particular the terminal carries no `hsmall`,
no `hEexp`/`hEadm`/`hEgamma`, no `hwindow`, no rate gate and no `cgamma <=
gamma0`.  What remains besides the two premises is standing or source-scale
data: the induction state at `m - 1`, `0 < h`, the buffer bound `h <= 6 cstar
cgamma^{-1}`, the large-cube gate `10^10 cgamma^{-1} <= K - m`, the two
directions, the localization depth `j` and its mesoscale identity.

## The parameters

* No multiplier binder and no range binder occurs; the printed buffer `16` of
  `e.recurrence.params` is not used.
* The good-event half is read at the honest switch factor `1 + (3/2) Delta`;
  the extra half of `Delta` is paid inside the `cgamma^6` budget at the
  corrected gap `a = 32`, not absorbed into the printed factor.
* The bad-event half is folded to the single tail `exp(-cgamma^{-1})` and
  finished below `cgamma^6 / 2` internally, at the tail power `3/8`.
* The coarse-ellipticity gate of the good half is met at `Ccg = 2 Cbase` from
  the dimension floor `(d : ℝ)^6 <= Cbase` carried by the bad-event package and
  `Provider.BadEvents.one_le_sensitivityConstMax`.  No event monotonicity is
  used or assumed.
* The window `|log cgamma|^{-1} in [8 cgamma, 1]` needs `cgamma <= 1 / 1089`.
  The standing `cgamma <= 1 / 4` is **insufficient** for its lower end: at
  `cgamma = 1 / 4`, `8 cgamma |log cgamma| = 2 log 4 = 2.77... > 1`.  The bound
  is obtained here from the source premises, by enlarging `Cterm` past `(3/2).
  1089`: then `1089 <= E <= cgamma^{-1}`.  The same mechanism supplies the four
  sub-packages' own thresholds, so no `cgamma <= gamma0` binder occurs.
* The reading gauge `shom_{m-1}` of the fourth-moment display and the load
  gauge `shom_{m-h}` of `e.Pz.def` are bridged inside the proof by the public
  transports of `PrincipalResponseMomentsFourth`; no gauge identity is assumed. -/
theorem exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cterm : ℝ, 0 < Cterm ∧
      ∀ (M : ABKModel d),
        ∀ (m Kc : ℤ) (hgap : ℕ) (E : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
          0 < hgap →
          Cterm * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
          M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) →
          (hgap : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
          (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (Kc : ℝ) - (m : ℝ) →
          ∀ e e' : Vec d, Ch02.vecNorm e ≤ 1 → Ch02.vecNorm e' ≤ 1 →
            ∀ j : ℕ,
              ((originCube d Kc).scale : ℤ) - (j : ℤ) =
                recurrenceMesoScale recurrenceGapMultiplier M.gamma m (hgap : ℤ) →
              ∃ (wD : Cutoff.ShellSeq d →
                  H10Function (openCubeSet (originCube d Kc)))
                (wN : Cutoff.ShellSeq d →
                  H1MeanZeroFunction (openCubeSet (originCube d Kc))),
                (∀ omega : Cutoff.ShellSeq d,
                  IsZeroTraceDirichletRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d Kc)) (wD omega)
                    (fun x => -streamForcing
                      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
                      (m - (hgap : ℤ)) m e x)) ∧
                (∀ omega : Cutoff.ShellSeq d,
                  IsMeanZeroNeumannRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d Kc)) (wN omega)
                    (fun x => -streamForcing
                      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
                      (m - (hgap : ℤ)) m e' x)) ∧
                descendantsAverage (originCube d Kc) j
                    (fun R => ∫ omega : Cutoff.CutoffSample d,
                      switchCubeEnergy M m R
                        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                          omega.val (m - (hgap : ℤ)) m e e' R
                          (wD omega.val) (wN omega.val)) omega
                      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                  (1 + 3 * principalResponseSwitchBudget M E 64) *
                      descendantsAverage (originCube d Kc) j
                        (fun R => ∫ omega : Cutoff.CutoffSample d,
                          blockVecDot
                            (gaugedPrincipalLoadShell
                              (Annealed.sigmaBar M (m - (hgap : ℤ))) R
                              (m - (hgap : ℤ)) m e e' wD wN omega.val)
                            (blockMatVecMul
                              (Ch02.blockDiag
                                ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ) •
                                  (1 : Mat d))
                                (((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ •
                                  (1 : Mat d)))
                              (gaugedPrincipalLoadShell
                                (Annealed.sigmaBar M (m - (hgap : ℤ))) R
                                (m - (hgap : ℤ)) m e e' wD wN omega.val))
                          ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
                    M.gamma ^ (6 : ℕ) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cbase, c, C, hCbase, hCbased, hc, hC0, hbadhalf⟩ :=
    exists_const_descendantsAverage_switchCubeEnergy_badEvent_le_half d
  obtain ⟨g1, hg1p, hg1q, hgoodE⟩ :=
    exists_smallCoupling_principalEnergy_bound_of_gate
      d hd
  obtain ⟨Cload, hCload0, g2, hg2p, hg2q, hdisp2⟩ :=
    exists_const_gridAverage_fourthMoment_annealedSqrtNormSq_principalPz_le d hd
  obtain ⟨g3, hg3p, hg3q, hSqInt⟩ :=
    exists_gamma0_integrable_switchEllipLoad_principalPz_sq d hd
  obtain ⟨g4, hg4p, hg4q, hWint⟩ :=
    exists_gamma0_integrable_toFullBlockVec_gaugedPrincipalLoadShell_mul d hd
  have hCm0 : (0 : ℝ) < (3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cload ^ (2 : ℕ) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith))
      (pow_pos hCload0 2)
  have h24 : (0 : ℝ) < 24 ^ (9 : ℕ) := by positivity
  -- the composite threshold on `cgamma` that the four packages ask for, and the
  -- window of the bad-event chain; it is *not* a binder below
  have hg0p : (0 : ℝ) < min (1 / 1089) (min g1 (min g2 (min g3 g4))) :=
    lt_min (by norm_num) (lt_min hg1p (lt_min hg2p (lt_min hg3p hg4p)))
  have hg0inv0 : (0 : ℝ) < (min (1 / 1089) (min g1 (min g2 (min g3 g4))))⁻¹ :=
    inv_pos.2 hg0p
  -- the enlarged constant, with the nine readings it has to cover
  obtain ⟨Cterm, hT1, hT9, hT2c, hT12, hTC2, hTm, hTb, hTg⟩ :
      ∃ T : ℝ, max 1 (max c⁻¹ ((3 / 2) * Real.exp (2 * C))) ≤ T ∧ (9 : ℝ) ≤ T ∧
        2 / c ≤ T ∧ 12 / c ^ 2 ≤ T ∧ 12 * C ^ 2 ≤ T ∧
        3 * ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cload ^ (2 : ℕ)) * 24 ^ (9 : ℕ) ≤ T ∧
        (3 / 2) * principalResponseBudgetConst⁻¹ ≤ T ∧
        (3 / 2) * (min (1 / 1089) (min g1 (min g2 (min g3 g4))))⁻¹ ≤ T := by
    refine ⟨max (max (max 1 (max c⁻¹ ((3 / 2) * Real.exp (2 * C))))
        (max 9 (max (2 / c) (max (12 / c ^ 2) (max (12 * C ^ 2)
          (max (3 * ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cload ^ (2 : ℕ)) * 24 ^ (9 : ℕ))
            ((3 / 2) * principalResponseBudgetConst⁻¹)))))))
        ((3 / 2) * (min (1 / 1089) (min g1 (min g2 (min g3 g4))))⁻¹),
      le_trans (le_max_left _ _) (le_max_left _ _), ?_, ?_, ?_, ?_, ?_, ?_,
      le_max_right _ _⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
    · exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_max_right _ _)) (le_max_left _ _)
    · exact le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_max_right _ _)) (le_max_right _ _)) (le_max_left _ _)
    · exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _)
        (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _))
        (le_max_left _ _)
    · exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _)
        (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _))
        (le_max_right _ _)) (le_max_left _ _)
    · exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
        (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _))
        (le_max_right _ _)) (le_max_left _ _)
  have hTone : (1 : ℝ) ≤ Cterm := le_trans (le_max_left _ _) hT1
  refine ⟨Cterm, lt_of_lt_of_le zero_lt_one hTone, ?_⟩
  intro M m Kc hgap E hstate hhpos hthreshold hgammaE hh hK e e' he he' j hscale
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hinv0 : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgamma0
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar32 : Disorder.cstar M ≤ 3 / 2 := Disorder.cstar_le_three_halves M
  have hcinv0 : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar0
  have hcinv23 : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcstar0]
    linarith
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one hE1
  -- one projection of the source admissibility premise, at every reading
  have hproj : ∀ T : ℝ, 0 ≤ T → T ≤ Cterm → T * (2 / 3) ≤ (E : ℝ) := by
    intro T hT0 hTC
    have h1 : T * (2 / 3) ≤ T * (Disorder.cstar M)⁻¹ :=
      mul_le_mul_of_nonneg_left hcinv23 hT0
    have h2 : T * (Disorder.cstar M)⁻¹ ≤ Cterm * (Disorder.cstar M)⁻¹ :=
      mul_le_mul_of_nonneg_right hTC hcinv0.le
    linarith [hthreshold]
  obtain ⟨-, hEinv, hE5⟩ := fifth_power_regime hE1 hgamma0 hgammaE
  -- the composite `cgamma`-threshold, from the source admissibility premise:
  -- `Cterm (cstar M)^{-1} <= E` and `cstar M <= 3/2` give `g0^{-1} <= E <= cgamma^{-1}`
  have hMgamma : M.gamma ≤ min (1 / 1089) (min g1 (min g2 (min g3 g4))) := by
    have h := hproj ((3 / 2) * (min (1 / 1089) (min g1 (min g2 (min g3 g4))))⁻¹)
      (by linarith) hTg
    have hid : ((3 / 2) * (min (1 / 1089) (min g1 (min g2 (min g3 g4))))⁻¹) * (2 / 3) =
        (min (1 / 1089) (min g1 (min g2 (min g3 g4))))⁻¹ := by ring
    have hle : (min (1 / 1089) (min g1 (min g2 (min g3 g4))))⁻¹ ≤ M.gamma⁻¹ := by
      linarith [hEinv]
    rw [← inv_inv (min (1 / 1089) (min g1 (min g2 (min g3 g4)))),
      le_inv_comm₀ hgamma0 hg0inv0]
    exact hle
  have hg1 : M.gamma ≤ g1 :=
    le_trans hMgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg2 : M.gamma ≤ g2 :=
    le_trans hMgamma
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hg3 : M.gamma ≤ g3 :=
    le_trans hMgamma (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hg4 : M.gamma ≤ g4 :=
    le_trans hMgamma (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hgamma1089 : M.gamma ≤ 1 / 1089 := le_trans hMgamma (min_le_left _ _)
  -- the gates of the two halves, from the two source premises
  have hE6 : (6 : ℝ) ≤ (E : ℝ) := by
    have h := hproj 9 (by norm_num) hT9
    linarith
  have hadmE : max 1 (max c⁻¹ ((3 / 2) * Real.exp (2 * C))) * (Disorder.cstar M)⁻¹ ≤
      (E : ℝ) := le_trans (mul_le_mul_of_nonneg_right hT1 hcinv0.le) hthreshold
  obtain ⟨hEexp, hEadm⟩ :=
    admissibility_of_enlarged_const_mul_cstarInv_le hcstar0 hcstar32 hadmE
  obtain ⟨stage_hEgamma, stage_hcstarinv, stage_hsmall, stage_hwindow, stage_hrate,
    stage_hrateEllip, stage_hhZ, stage_hm, stage_hhcast, stage_hccg⟩ :=
    @principalResponseTerminal_comparisonBounds1 (d) (Cbase) (c) (C) (hCbase) (hCbased) (hc) (hC0)
      (Cload) (hCload0) (hCm0) (h24) (Cterm) (hT2c) (hT12) (hTC2) (hTm) (hTone) (M) (m) (Kc)
        (hgap) (E) (hhpos) (hthreshold) (hgammaE) (hh) (j) (hgamma0) (hinv0) (hcstar0) (hcstar32)
          (hcinv0) (hE1) (hproj) (hEinv) (hE5) (hgamma1089)
  have hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) := stage_hEgamma
  have hcstarinv : (Disorder.cstar M)⁻¹ ≤ M.gamma⁻¹ := stage_hcstarinv
  have hsmall : M.gamma ≤
      (2 * ((3 : ℝ) ^ (22 : ℝ) * (2 * C) * Cload ^ (2 : ℕ)) * 24 ^ (9 : ℕ))⁻¹ := stage_hsmall
  have hwindow : M.gamma / 2 +
      Real.exp (-(C⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤ M.gamma := stage_hwindow
  have hrate := stage_hrate
  have hrateEllip := stage_hrateEllip
  have hhZ : (0 : ℤ) < (hgap : ℤ) := stage_hhZ
  have hm : m - (hgap : ℤ) ≤ m - 1 := stage_hm
  have hhcast : (((hgap : ℤ) : ℝ)) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ := stage_hhcast
  have hccg : 2 * (d : ℝ) ^ 6 ≤
      2 * Cbase * Provider.BadEvents.sensitivityConstMax d ^ 2 := stage_hccg
  obtain ⟨wD, wN, hwD, hwN, hgoodInt, hgood⟩ :=
    hgoodE M hg1 (m - 1) E hstate m Kc hgap hhpos hm hh hK e e' he he' j
      recurrenceGapMultiplier recurrenceGapMultiplierFloor_le_recurrenceGapMultiplier
      hscale (2 * Cbase) hccg
  refine ⟨wD, wN, hwD, hwN, ?_⟩
  -- the transport between the two carriers
  obtain ⟨stage_hbadInt, stage_hbad, stage_hlimInt, stage_hcubeInt, stage_hL, stage_hn,
    stage_hgamE, stage_hsw, stage_Ev, stage_hEv, stage_hgapK, stage_hrename⟩ :=
    @principalResponseTerminal_comparisonBounds3 (d) (by infer_instance) (Cbase) (c) (C)
      (hbadhalf) (Cload) (hCload0) (g2) (hdisp2) (g3) (hSqInt) (g4) (hWint) (Cterm) (hTb) (M) (m)
        (Kc) (hgap) (E) (hstate) (hhpos) (hgammaE) (hh) (hK) (e) (e') (he) (he') (j) (hscale)
          (hgamma0) (hE1) (hproj) (hEinv) (hg2) (hg3) (hg4) (hgamma1089) (hEexp) (hEadm) (hEgamma)
            (hcstarinv) (hsmall) (hwindow) (hrate) (hrateEllip) (hhZ) (hm) (hhcast) (wD) (wN)
              (hwD) (hwN)
  let hbadInt := stage_hbadInt
  let hbad := stage_hbad
  have hlimInt : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Integrable (fun z : Cutoff.CutoffSample d =>
        blockVecDot
          (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
            (m - (hgap : ℤ)) m e e' wD wN z.val)
          (blockMatVecMul
            (Ch02.blockDiag
              ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ) • (1 : Mat d))
              (((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ • (1 : Mat d)))
            (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
              (m - (hgap : ℤ)) m e e' wD wN z.val)))
        (Cutoff.cutoffSampleLaw M).toMeasure := stage_hlimInt
  have hcubeInt : ∀ R ∈ descendantsAtDepth (originCube d Kc) j,
      Integrable (fun z : Cutoff.CutoffSample d =>
        blockVecDot
          (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
            (m - (hgap : ℤ)) m e e' wD wN z.val)
          (blockMatVecMul
            (Ch04.annealedBlockMatrixAtScale
              (Cutoff.coefficientCutoffLaw M (m - (hgap : ℤ)))
              (((originCube d Kc).scale : ℤ) - (j : ℤ)))
            (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
              (m - (hgap : ℤ)) m e e' wD wN z.val)))
        (Cutoff.cutoffSampleLaw M).toMeasure := stage_hcubeInt
  have hL : m - (hgap : ℤ) ≤ m - 1 := stage_hL
  have hn : ((originCube d Kc).scale : ℤ) - (j : ℤ) ≤ m - (hgap : ℤ) := stage_hn
  have hgamE : M.gamma ≤ ((E : ℝ) ^ 5)⁻¹ := stage_hgamE
  let hsw := stage_hsw
  let Ev := stage_Ev
  let hEv := stage_hEv
  have hgapK : |Real.log M.gamma|⁻¹ *
      ((Int.toNat (m - (hgap : ℤ) - (((originCube d Kc).scale : ℤ) - (j : ℤ))) : ℕ) : ℝ) ≤
      64 := stage_hgapK
  have hrename : M.gamma ^ (6 : ℕ) ≤ principalResponseSwitchBudget M E 64 := stage_hrename
  exact descendantsAverage_integral_principalEnergy_le_annealedLimit
    (mu := (Cutoff.cutoffSampleLaw M).toMeasure) M
    (m0 := m - 1) (L := m - (hgap : ℤ))
    (n := ((originCube d Kc).scale : ℤ) - (j : ℤ)) (Ec := E) hstate hL hn hE6 hgamE hsw
    (Ev := Ev) hEv
    (K := 64) hgapK
    (originCube d Kc) j
    (fun R omega => switchCubeEnergy M m R
      (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) omega.val
        (m - (hgap : ℤ)) m e e' R (wD omega.val) (wN omega.val)) omega)
    (fun R omega => gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
      (m - (hgap : ℤ)) m e e' wD wN omega.val)
    (Ebad := fun R => principalBadEvent M (2 * Cbase) R (m - (hgap : ℤ)))
    hgoodInt hbadInt hcubeInt hlimInt hgood hbad hrename

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
