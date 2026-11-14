/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseMomentsCloseOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Carrier
import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz

/-!
# PrincipalResponseDisplayTwoMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the expectation and the measure transport behind display 2

Display 2 of leg (iv) of `l.approximate.recurrence.formula` takes an
expectation of a fourth power.  The pathwise input, `e.nablaw.in.L.eight`,
controls the corrector energies by a deterministic head plus a `Gamma_1`
fluctuation, so the expectation that has to be evaluated is the **second**
moment of a shifted one-lane weak-Orlicz variable.  That engine is the proved
`integral_rpow_two_le_of_shift_add_one_orlicz`; this module supplies the three
pieces of plumbing that stand between it and the display.

## 1. Two lanes into one

The fourth-power display carries *two* fluctuation lanes, not one: the
Calderon-Zygmund lane of `e.nablaw.in.L.eight` and, separately, the lane of the
forcing `shom^{-1} (k_m - k_{m-h}) e'` that the Neumann slot of `e.Pz.def`
adds to `grad w_N`.  `isBigOWith_gammaSigma_one_add` merges them: at the
manuscript's exponent `sigma = 1` the sum of two lanes is again a single lane,
at twice the sum of the amplitudes.  The doubling is exactly what pays for the
union bound, since `2 exp(-2t) <= exp(-t)` for `t >= 1`.

## 2. From the shell law to the cutoff-sample law

`e.nablaw.in.L.eight` is stated on the canonical shell-sequence law
`M.P.toMeasure`; the displays of Step 3 live on the lower-tail-good carrier
`Cutoff.CutoffSample d` with its induced law `Cutoff.cutoffSampleLaw M`.
`isBigOWith_cutoffSampleLaw_of_isBigOWith` transports a weak-Orlicz upper tail
along `Subtype.val`.  The transport is one-sided by design and needs no
measurability of the lane: the upper-tail event of the composite is the
preimage of the upper-tail event of the original, and
`MeasureTheory.Measure.le_map_apply` bounds the measure of a preimage by the
pushforward of *any* set, measurable or not, which
`Cutoff.map_cutoffSampleLaw_val` identifies with the shell law.

## 3. The expectation, with no measurability assumed of the lane

The lane witnesses produced by `e.nablaw.in.L.eight` and by `e.km.kn.Lp` are
existential and carry no measurability.  `integral_le_of_le_shift_add_kappa_sq`
is stated so that none is needed: the only measurable object is the display's
own integrand `X`, and the proof runs the moment engine on the **measurable
proxy** `sqrt(max(X - B, 0) / kappa)`, which is pointwise below the true energy
and therefore inherits its tail by `IsBigOWith.of_le`.  This is the same device
by which the proved engines handle non-negative parts, applied one level up.

## Portability

Section 1 and section 3 mention no ABK26 object and would move to
CoarseGraining unchanged; section 2 is about this repository's cutoff carrier
and stays here.

## Main results

* `isBigOWith_gammaSigma_one_add`
* `isBigOWith_cutoffSampleLaw_of_isBigOWith`
* `integral_le_of_le_shift_add_kappa_sq`
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3

noncomputable section

/-! ## Merging two `Gamma_1` lanes -/

section Lanes

variable {Omega : Type*} [MeasurableSpace Omega]

/-- **Two `Gamma_1` lanes are one `Gamma_1` lane.**  At the manuscript's
exponent `sigma = 1` the sum of two one-sided stretched-exponential variables is
again one, with amplitude twice the sum of the two amplitudes: the union bound
costs a factor `2`, and `2 exp(-2t) <= exp(-t)` for `t >= 1` pays for it. -/
theorem isBigOWith_gammaSigma_one_add {mu : Measure Omega} [IsFiniteMeasure mu]
    {Y1 Y2 : Omega → ℝ} {A1 A2 : ℝ}
    (h1 : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) Y1 A1)
    (h2 : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) Y2 A2) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1)
      (fun omega => Y1 omega + Y2 omega) (2 * (A1 + A2)) := by
  intro t ht
  have ht2 : (1 : ℝ) ≤ 2 * t := by linarith
  have hsub : IndependentSums.upperTailEvent
        (fun omega => Y1 omega + Y2 omega) (2 * (A1 + A2) * t) ⊆
      IndependentSums.upperTailEvent Y1 (A1 * (2 * t)) ∪
        IndependentSums.upperTailEvent Y2 (A2 * (2 * t)) := by
    intro omega homega
    by_contra hcon
    simp only [Set.mem_union, IndependentSums.mem_upperTailEvent, not_or, not_lt] at hcon
    have hsum := homega
    simp only [IndependentSums.mem_upperTailEvent] at hsum
    have := hcon.1
    have := hcon.2
    nlinarith [hcon.1, hcon.2, hsum]
  have hmono : mu.real (IndependentSums.upperTailEvent
      (fun omega => Y1 omega + Y2 omega) (2 * (A1 + A2) * t)) ≤
      mu.real (IndependentSums.upperTailEvent Y1 (A1 * (2 * t)) ∪
        IndependentSums.upperTailEvent Y2 (A2 * (2 * t))) := measureReal_mono hsub
  have hunion : mu.real (IndependentSums.upperTailEvent Y1 (A1 * (2 * t)) ∪
        IndependentSums.upperTailEvent Y2 (A2 * (2 * t))) ≤
      mu.real (IndependentSums.upperTailEvent Y1 (A1 * (2 * t))) +
        mu.real (IndependentSums.upperTailEvent Y2 (A2 * (2 * t))) :=
    measureReal_union_le _ _
  have hpsi : ∀ s : ℝ, (IndependentSums.gammaSigma 1 s)⁻¹ = (Real.exp s)⁻¹ := by
    intro s
    rw [IndependentSums.gammaSigma, Real.rpow_one]
  have hexp1 : (2 : ℝ) ≤ Real.exp t := by
    have hone : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hmonoexp : Real.exp 1 ≤ Real.exp t := Real.exp_le_exp.2 ht
    linarith
  have hposexp : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hkey : 2 * (Real.exp (2 * t))⁻¹ ≤ (Real.exp t)⁻¹ := by
    have hsplit : Real.exp (2 * t) = Real.exp t * Real.exp t := by
      rw [two_mul, Real.exp_add]
    rw [hsplit, mul_inv]
    have hhalf : (2 : ℝ) * (Real.exp t)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one hposexp).2 hexp1
    have hinvpos : (0 : ℝ) < (Real.exp t)⁻¹ := inv_pos.2 hposexp
    nlinarith [hhalf, hinvpos]
  have h1' := h1 ht2
  have h2' := h2 ht2
  rw [hpsi] at h1' h2'
  rw [hpsi]
  have hrw : Real.exp (2 * t) = Real.exp (2 * t) := rfl
  calc mu.real (IndependentSums.upperTailEvent
        (fun omega => Y1 omega + Y2 omega) (2 * (A1 + A2) * t))
      ≤ mu.real (IndependentSums.upperTailEvent Y1 (A1 * (2 * t))) +
          mu.real (IndependentSums.upperTailEvent Y2 (A2 * (2 * t))) :=
        hmono.trans hunion
    _ ≤ (Real.exp (2 * t))⁻¹ + (Real.exp (2 * t))⁻¹ := by
        rw [hrw]
        linarith [h1', h2']
    _ = 2 * (Real.exp (2 * t))⁻¹ := by ring
    _ ≤ (Real.exp t)⁻¹ := hkey

end Lanes

/-! ## Transport to the cutoff-sample law -/

variable {d : ℕ}

/-- **A weak-Orlicz tail transports to the cutoff-sample carrier.**  If a
variable on the canonical shell-sequence law is `O_Psi(A)`, then its restriction
to the lower-tail-good carrier is `O_Psi(A)` for the induced law.  No
measurability of the variable is used. -/
theorem isBigOWith_cutoffSampleLaw_of_isBigOWith (M : ABKModel d) {Psi : ℝ → ℝ}
    {T : Cutoff.ShellSeq d → ℝ} {A : ℝ}
    (hT : IndependentSums.IsBigOWith M.P.toMeasure Psi T A) :
    IndependentSums.IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure Psi
      (fun z : Cutoff.CutoffSample d => T z.val) A := by
  intro t ht
  have hmeas : Measurable (Subtype.val : Cutoff.CutoffSample d → Cutoff.ShellSeq d) :=
    measurable_subtype_coe
  have hpre : IndependentSums.upperTailEvent
        (fun z : Cutoff.CutoffSample d => T z.val) (A * t) =
      (Subtype.val : Cutoff.CutoffSample d → Cutoff.ShellSeq d) ⁻¹'
        IndependentSums.upperTailEvent T (A * t) := rfl
  have hle : (Cutoff.cutoffSampleLaw M).toMeasure
        (IndependentSums.upperTailEvent
          (fun z : Cutoff.CutoffSample d => T z.val) (A * t)) ≤
      M.P.toMeasure (IndependentSums.upperTailEvent T (A * t)) := by
    rw [hpre]
    calc (Cutoff.cutoffSampleLaw M).toMeasure
          ((Subtype.val : Cutoff.CutoffSample d → Cutoff.ShellSeq d) ⁻¹'
            IndependentSums.upperTailEvent T (A * t))
        ≤ Measure.map (Subtype.val : Cutoff.CutoffSample d → Cutoff.ShellSeq d)
            (Cutoff.cutoffSampleLaw M).toMeasure
            (IndependentSums.upperTailEvent T (A * t)) :=
          Measure.le_map_apply hmeas.aemeasurable _
      _ = M.P.toMeasure (IndependentSums.upperTailEvent T (A * t)) := by
          rw [Cutoff.map_cutoffSampleLaw_val]
  refine le_trans ?_ (hT ht)
  simp only [Measure.real_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-! ## The expectation of a fourth power under a shifted one-lane bound -/

section Expectation

variable {Omega : Type*} [MeasurableSpace Omega]

private theorem rpow_two_eq_pow_display (y : ℝ) : y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The expectation of display 2, from a shifted one-lane energy bound.**

Let `X` be a non-negative measurable observable dominated by a deterministic
shift `B` plus `kappa` times the square of an energy `W`, and let `W` itself be
dominated by a deterministic shift `b` plus a single one-sided
stretched-exponential lane `Y` of amplitude `A`.  Then

```
  E[X]  <=  B + kappa (2 (b + c(sigma) A))^2 ,
```

with `c = orliczSecondMomentScale` the class constant of the proved engine
`integral_rpow_two_le_of_shift_add_one_orlicz`.

Neither `W` nor `Y` is assumed measurable: the engine is run on the measurable
proxy `sqrt(max(X - B, 0)/kappa)`, which is pointwise below `W` and therefore
inherits the lane by `IsBigOWith.of_le`. -/
theorem integral_le_of_le_shift_add_kappa_sq {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X W Y : Omega → ℝ} {B kappa b A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hb : 0 ≤ b) (hkappa : 0 < kappa)
    (hXm : Measurable X) (hX0 : ∀ omega, 0 ≤ X omega)
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hXW : ∀ omega, X omega ≤ B + kappa * W omega ^ (2 : ℕ))
    (hWY : ∀ omega, W omega ≤ b + Y omega)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    ∫ omega, X omega ∂mu ≤
      B + kappa * (2 * (b + orliczSecondMomentScale sigma * A)) ^ (2 : ℕ) := by
  obtain ⟨W0, hW0m, hW0nn, _hW0leW, hXle, hYt⟩ :=
    exists_measurable_quadratic_dominator hkappa hXm hW0 hXW hWY hY
  let Yt : Omega → ℝ := fun omega => W0 omega - b
  have hYtm : Measurable Yt := hW0m.sub measurable_const
  have hW0shift : ∀ omega, W0 omega ≤ b + Yt omega := by
    intro omega
    dsimp [Yt]
    linarith
  -- the second moment of the proxy
  have hmom0 := integral_rpow_two_le_of_shift_add_one_orlicz hsigma hA hb hYtm hYt
    hW0nn hW0shift
  have hmom : ∫ omega, W0 omega ^ (2 : ℕ) ∂mu ≤
      (2 * (b + orliczSecondMomentScale sigma * A)) ^ (2 : ℕ) := by
    simpa only [rpow_two_eq_pow_display] using hmom0
  have hIW0 := integrable_sq_of_shift_add_one_orlicz hsigma hA hb
    hW0m hW0nn hW0shift hYt
  have hIg : Integrable (fun omega => B + kappa * W0 omega ^ (2 : ℕ)) mu :=
    (integrable_const B).add (hIW0.const_mul kappa)
  have hstep : ∫ omega, X omega ∂mu ≤
      ∫ omega, (B + kappa * W0 omega ^ (2 : ℕ)) ∂mu :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall hX0) hIg
      (Filter.Eventually.of_forall hXle)
  have hsplit : ∫ omega, (B + kappa * W0 omega ^ (2 : ℕ)) ∂mu =
      B + kappa * ∫ omega, W0 omega ^ (2 : ℕ) ∂mu := by
    rw [integral_add (integrable_const B) (hIW0.const_mul kappa), integral_const,
      integral_const_mul]
    simp
  rw [hsplit] at hstep
  have hscale : kappa * ∫ omega, W0 omega ^ (2 : ℕ) ∂mu ≤
      kappa * (2 * (b + orliczSecondMomentScale sigma * A)) ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hmom hkappa.le
  linarith

end Expectation

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
