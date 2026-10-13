/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.BadEventLemmaCases
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.FiniteQTransfer

/-!
# EllipticityBranchLow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The coarse-ellipticity branch of `l.bad.event.lemma` at `n < m`

`BadEventLemmaCases.lean` supplies a conditional local result for the
coarse-ellipticity branch of ABK26's
Lemma `l.bad.event.lemma` on the branch `n >= m`.  This module supplies a
conditional local result for the *other* branch, `n < m`:

```
lambda^{-1}_{1/8,2}(square_m; a_n)
  <= max_{z in 3^n Z^d cap square_m} lambda^{-1}_{1/8,2}(z + square_n; a_n) ,
```
then `p.cg.ellipticity.bounds` at each translate and `l.maximums.Gamma.s`.

## The two corrections this branch runs under

* **The printed max form is false at finite `q`.**  Definition (2.23) puts a
  sum of per-depth maxima on the left and a maximum of sums on the right, and
  the printed step fails by `3^{2(m-n)(d/q-s)}`, unbounded in the separation.
  The consuming step is routed instead through the true `q = infinity` max form
  and exponent monotonicity, reading the coarse-graining input at a fixed
  `t < s`; the canonical instantiation is `t = 1/16`.  This module consumes the
  proved gap-constant route (sharp only relative to the geometric profile)
  `ErrorComparison.lambdaSq_eighth_inv_le_two_mul_max_descendants_sixteenth`
  (`lambda^{-1}_{1/8,2}(Q) <= 2 max_{R in descendantsAtScale Q n}
  lambda^{-1}_{1/16,2}(R)`, gap constant `G(1/8,1/16,2) = 1 + 3^{-1/8} <= 2`).

  This is exactly the accounting recorded in the header of
  `FiniteQTransfer.lean`.

* **The entropy of the `3^{d(m-n)}` translates is NOT absorbed by an adjusted
  constant.**  ABK26 says "the constant `c` is adjusted to absorb the polynomial
  factor `3^{d(m-n)}` from the union bound".  A dimension-only `c` cannot do
  that: the loss grows with `m - n` while the double exponential `exp(-exp(c
  E^{-2} gamma^{-1}))` does not.  Accordingly the headline theorem here,
  `measureReal_coarseEllipticityFailure_le_of_translateCoarseBounds`, is stated
  with **no gate at all** and **carries** the loss,

  ```
  P[ lambda^{-1}_{1/8,2}(square_m; a_n) sigmabar_{n-1} > 2 . 2 Ccg ]
    <= 3^{d(m-n)} exp( - exp( (1/4) Ccg^{-1} E^{-2} gamma^{-1} ) ) ,
  ```

  and the passage to the printed shape is a separate, explicitly gated step
  (`..._of_absorb`, `..._printed_of_gap`), whose gate

  ```
  d (m - n) log 3 + T <= exp( (1/4) Ccg^{-1} E^{-2} gamma^{-1} )
  ```

  is the exact and only inequality the absorption needs.  Nothing in this
  module hides it: the loss-carrying theorem is unconditional, and every
  printed-shape statement carries the gate as a named binder.

## The size of the gate

The gate above is a genuine restriction on `m - n`, not a constant adjustment.
Two remarks fix its size.

* It is *much* weaker than the self-consistent restriction imposed on the
  oscillation branch at `n < m` (`3^{5(m-n)_+} <= c c_star gamma^{-1}`, i.e.
  `m - n <~ log_3(gamma^{-1})/5`), because here `m - n` may grow like
  `exp(c E^{-2} gamma^{-1})`, doubly exponentially larger.
* The union bound wins because the per-translate tail is *doubly* exponential
  while the loss is only exponential in `m - n`; that is the whole reason a
  gate on `m - n` suffices and no adjustment of the constant is needed.

## The two conditional binders

* `hcg` is the conclusion of `p.cg.ellipticity.bounds` **at every translate**
  `R in descendantsAtScale Q n`, at `sigma = 1/2`, `s = 1/16`, `q = 2`, in the
  exact shape of the frozen
  `Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` conclusion but with
  the centered observable `Observable.cutoffLowerEllipticityInv M n L ...`
  replaced by the general-cube observable `cubeLowerEllipticityInv M ...`.  Two
  things are carried by this single binder, both of them steps the manuscript
  itself takes:

  1. the helper keeps the frozen theorem's specialization explicit as a
     conditional A binder, exactly as in `BadEventLemmaCases.lean`; the frozen
     theorem is now proved and may discharge the centered instance in a
     downstream assembly;
  2. the manuscript applies the proposition *at each translate* `z + square_n`,
     which is its own stationarity reduction; the frozen statement is at the
     centered cube.  On the centered cube `R = originCube d n` the two
     observables agree almost everywhere
     (`cubeLowerEllipticityInv_ae_eq_cutoffLowerEllipticityInv`); note however
     that this a.e. identification does NOT by itself transport the frozen
     conclusion to this binder even at that one translate, because
     `IsLowerIntegerFamilyOrliczWithWitness.dominates` is a pointwise (`∀ ω`)
     clause, which an a.e. route cannot reach.  Both halves are resolved below.

     * *Centered.*  The exported general-cube and centered observables both
       reduce pointwise to the same literal by
       `cubeLowerEllipticityInv_eq_literal`,
       `Observable.cutoffLowerEllipticityInv_eq_literal`, and
       `cubeLowerEllipticityInvLiteral_originCube`.  Hence the family relation
       transports with the same witness and no null-set surgery.
     * Since the observable bodies are the literals clamped
       at `0`, the exported observables carry pointwise
       information, and the proved pathwise covariance
       `LambdaCovariance.lambdaSq_cutoff_translateCutoffSample` applies to them
       directly: `cubeLowerEllipticityInv M s hs q omega` equals the centered
       observable at scale `R.scale` read at the translated sample
       (`ObservableSwapPayoff.cubeLowerEllipticityInv_translateCutoffSample`).
       With the law invariance
       `Cutoff.map_translateCutoffSample_cutoffSampleLaw` this produces the
       WHOLE `∀ R ∈ descendantsAtScale Q n` binder from a SINGLE centered
       instance at scale `n` (`ObservableSwapPayoff`'s
       `isLowerIntegerFamilyOrlicz_cubeLowerEllipticityInv_forall_descendant`),
       which is precisely the manuscript's stationarity reduction.

     The binder remains as stated because this module exposes the translated
     statement rather than assembling its upstream input.  The frozen theorem
     discharges the centered instance, and the *transport* is what is proved
     here.

  The exponent is `1/16`, not the printed `1/8`, by the `q = infinity` reading
  described above.  `1/16` lies
  in the frozen `s`-window `Set.Icc (gamma/2 + exp(-Ccg^{-1} E^{-2}
  gamma^{-1})) 1` exactly when `gamma/2 + exp(-Ccg^{-1} E^{-2} gamma^{-1}) <=
  1/16`, the `t = 1/16` analogue of the proved `s = 1/8` gate; that gate is a
  *precondition of the frozen theorem*, discharged where the binder is
  discharged, and therefore appears nowhere here.

* `hgamma : gamma <= 1/16` makes the frozen deterministic profile
  `lowerEllipticityProfile Ccg gamma (1/16) 2 = Ccg (1/16) (1/8 - gamma)^{-1}`
  at most `Ccg`.  It is not an addition: `gamma_le_one_sixteenth_of_admissible`
  derives it from the manuscript's own admissibility
  `e.bad.event.admissibility` at the dimension-only constant
  `badEventOscAdmissibleConst`, exactly as the proved `n >= m` branch derives
  `gamma <= 1/8` (both come from `gamma <= E^{-5} <= 1/32`).

## Main results

* `lowerEllipticityProfile_exponentTwo_eq`,
  `lowerEllipticityProfile_exponentTwo_sixteenth_le`,
  `gamma_le_one_sixteenth_of_admissible`: the deterministic profile at
  `s = 1/16`.
* `cubeLowerEllipticityInv_le_two_mul_finsetSupReal_ae`: the transfer, at the
  observables (stated almost everywhere; the underlying fact is in fact
  pointwise --- see the structure note at that theorem).
* `measureReal_translateCoarseEllipticityTail_le`: the per-translate tail.
* `measureReal_coarseEllipticityFailure_le_of_translateCoarseBounds`: the
  branch, loss-carrying and gate-free.
* `measureReal_coarseEllipticityFailure_le_of_absorb`,
  `measureReal_coarseEllipticityFailure_le_printed_of_gap`: the printed shape,
  under the explicit entropy gate.

## References

* ABK26, `l.bad.event.lemma`; the case `n < m`; the recombined display.
* ABK26, `p.cg.ellipticity.bounds`.
* ABK26, `l.maximums.Gamma.s`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Nonzero dimension, from the paper-wide assumption `2 <= d` stored in the
model. -/
private theorem neZero_of_model_low (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-! ## The frozen deterministic profile at `q = 2` -/

/-- The frozen lower profile at `q = 2` and an arbitrary exponent:
`lowerEllipticityProfile Ccg gamma s 2 = Ccg s (2 s - gamma)^{-1}`. -/
theorem lowerEllipticityProfile_exponentTwo_eq (Ccg gamma s : ℝ) :
    Algsuperdiff.Section3.lowerEllipticityProfile Ccg gamma s exponentTwo =
      Ccg * s * (2 * s - gamma)⁻¹ := by
  simp only [Algsuperdiff.Section3.lowerEllipticityProfile, exponentTwo,
    Algsuperdiff.Section3.CoarseEllipticityExponent.finite]
  norm_num

/-- At `gamma <= 1/16` the frozen deterministic profile at the exponent `t = 1/16`
is below the frozen constant itself, which is what the manuscript's threshold
`2 C_{(e.cg.ellip.lower)}` needs.  This is the `t = 1/16` analogue of the
proved `lowerEllipticityProfile_exponentTwo_le`. -/
theorem lowerEllipticityProfile_exponentTwo_sixteenth_le {Ccg gamma : ℝ}
    (hCcg : 0 < Ccg) (hgamma : gamma ≤ 1 / 16) :
    Algsuperdiff.Section3.lowerEllipticityProfile Ccg gamma (1 / 16) exponentTwo ≤
      Ccg := by
  have hgap : (0 : ℝ) < 2 * (1 / 16 : ℝ) - gamma := by linarith
  have hsixteenth : (1 / 16 : ℝ) ≤ 2 * (1 / 16 : ℝ) - gamma := by linarith
  have hinv : (2 * (1 / 16 : ℝ) - gamma)⁻¹ ≤ (1 / 16 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hsixteenth
  rw [lowerEllipticityProfile_exponentTwo_eq]
  have h16 : ((1 : ℝ) / 16)⁻¹ = 16 := by norm_num
  rw [h16] at hinv
  nlinarith [hinv, hCcg, inv_pos.2 hgap]

/-- The manuscript's own admissibility `e.bad.event.admissibility`, at
the dimension-only constant `badEventOscAdmissibleConst`, implies `gamma
<= 1/16` (indeed `gamma <= 1/32`).  Same derivation as the proved
`gamma_le_one_eighth_of_admissible`, read at the exponent. -/
theorem gamma_le_one_sixteenth_of_admissible (M : ABKModel d) {Ccg E : ℝ}
    (hadm : badEventOscAdmissibleConst d Ccg ≤
      E * Algsuperdiff.Section3.Disorder.cstar M)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) : M.gamma ≤ 1 / 16 := by
  have hc : (0 : ℝ) < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hchalf : Algsuperdiff.Section3.Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have h3 : (3 : ℝ) ≤ E * Algsuperdiff.Section3.Disorder.cstar M :=
    le_trans (le_max_left _ _) hadm
  have hE2 : (2 : ℝ) ≤ E := by
    by_contra hlt
    push Not at hlt
    have hmul : E * Algsuperdiff.Section3.Disorder.cstar M <
        2 * Algsuperdiff.Section3.Disorder.cstar M :=
      mul_lt_mul_of_pos_right hlt hc
    linarith
  have hE5 : (0 : ℝ) < E ^ (5 : ℕ) := by positivity
  have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hsq : (4 : ℝ) ≤ E ^ 2 := by nlinarith
  have hquart : (16 : ℝ) ≤ E ^ 4 := by nlinarith
  have h32 : (32 : ℝ) ≤ E ^ (5 : ℕ) := by nlinarith
  have hle : M.gamma ≤ (E ^ (5 : ℕ))⁻¹ := by
    rw [← hEpow]
    exact hgammaE
  have hinv : (E ^ (5 : ℕ))⁻¹ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h32
  have h132 : ((32 : ℝ))⁻¹ ≤ 1 / 16 := by norm_num
  linarith

/-! ## The transfer at the observable level

`ErrorComparison.lambdaSq_eighth_inv_le_two_mul_max_descendants_sixteenth` is a
statement about the literal `Ch02.lambdaSq` of a triadic coefficient family, and
holds pointwise in the sample.

The observable bodies are the literals
clamped at `0`, so `cubeLowerEllipticityInv M Q n s hs q` **is**
`cubeLowerEllipticityInvLiteral M Q n s q` on the source range `s > 0`
(`cubeLowerEllipticityInv_eq_literal`), and the transfer descends at every
sample point.  The same applies to the a.e. route of `LambdaTransfer.lean`. -/

/-- **The transfer, at the observables.**  Almost surely (in fact at every
sample point — see the structure note above),

```
lambda^{-1}_{1/8,2}(square_m; a_n)
  <= 2 max_{R in descendantsAtScale Q n} lambda^{-1}_{1/16,2}(R; a_n) ,
``` -/
theorem cubeLowerEllipticityInv_le_two_mul_finsetSupReal_ae (M : ABKModel d)
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo omega ≤
        2 * Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
          cubeLowerEllipticityInv M R n (1 / 16) (by norm_num) exponentTwo omega := by
  let : NeZero d := neZero_of_model_low M
  have hall : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ R ∈ descendantsAtScale Q n,
        cubeLowerEllipticityInv M R n (1 / 16) (by norm_num) exponentTwo omega =
          cubeLowerEllipticityInvLiteral M R n (1 / 16) exponentTwo omega := by
    rw [Filter.eventually_all_finset]
    intro R _
    exact cubeLowerEllipticityInv_ae_eq_literal M R n (1 / 16) (by norm_num) exponentTwo
  filter_upwards [cubeLowerEllipticityInv_ae_eq_literal M Q n (1 / 8) (by norm_num)
    exponentTwo, hall] with omega hQ hR
  rw [hQ, Ch02.finsetSupReal_congr _ hR]
  set F : Ch02.TriadicCoeffFamily d :=
    coefficientCutoffTriadicCoeffFamily M n omega with hF
  have hQlit : cubeLowerEllipticityInvLiteral M Q n (1 / 8) exponentTwo omega =
      (Ch02.lambdaSq Q (1 / 8) (Ch02.MultiscaleExponent.finite 2) F)⁻¹ := by
    rw [← exponentTwo_val, hF, ← cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq,
      inv_inv]
  have hRlit : ∀ R : TriadicCube d,
      cubeLowerEllipticityInvLiteral M R n (1 / 16) exponentTwo omega =
        (Ch02.lambdaSq R (1 / 16) (Ch02.MultiscaleExponent.finite 2) F)⁻¹ := by
    intro R
    rw [← exponentTwo_val, hF, ← cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq,
      inv_inv]
  rw [hQlit, Ch02.finsetSupReal_congr _ (fun R _ => hRlit R)]
  exact ErrorComparison.lambdaSq_eighth_inv_le_two_mul_max_descendants_sixteenth
    Q hn F

/-! ## The per-translate tail

In the manuscript, `p.cg.ellipticity.bounds` at scale `n`, applied at the
translate `z + square_n`, gives the weak-Orlicz bound whose tail at the level
`Ccg` is the printed double exponential.  The argument is the proved one of
`BadEventLemmaCases.lean`, read at the translate and at the exponent.  -/

/-- **The per-translate tail** (ABK26).  At each scale-`n` translate `R`, the
coarse-graining input at the exponent `t = 1/16` gives

```
P[ lambda^{-1}_{1/16,2}(R; a_n) sigmabar_{n-1} > 2 Ccg ]
  <= exp( - exp( (1/4) Ccg^{-1} E^{-2} gamma^{-1} ) ) .
```
-/
theorem measureReal_translateCoarseEllipticityTail_le (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 1 ≤ Ccg) (R : TriadicCube d) {n : ℤ} {E : ℝ}
    (hgamma : M.gamma ≤ 1 / 16)
    (hcg : Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure
      (HCPolySupport.IndependentSums.gammaSigma ((1 - 1 / 2) / 2))
      (fun L : ℤ => fun omega =>
        cubeLowerEllipticityInv M R L (1 / 16) (by norm_num) exponentTwo omega *
          (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
      (n - 1)
      (Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 16)
        exponentTwo)
      (Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)))) :
    (cutoffSampleLaw M).toMeasure.real
        {omega : CutoffSample d | 2 * Ccg <
          cubeLowerEllipticityInv M R n (1 / 16) (by norm_num) exponentTwo omega *
            ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))} ≤
      Real.exp (-Real.exp ((1 / 4 : ℝ) * (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) := by
  obtain ⟨Y, hY⟩ := hcg
  have hCcg0 : (0 : ℝ) < Ccg := lt_of_lt_of_le zero_lt_one hCcg
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hXnn : (0 : ℝ) ≤ Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹ := by
    have h1 : (0 : ℝ) ≤ Ccg⁻¹ := (inv_pos.2 hCcg0).le
    have h3 : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.2 hg).le
    positivity
  have hApos : (0 : ℝ) < Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) :=
    Real.exp_pos _
  have hAle : Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hb : Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 16)
      exponentTwo ≤ Ccg :=
    lowerEllipticityProfile_exponentTwo_sixteenth_le hCcg0 hgamma
  have hsub : {omega : CutoffSample d | 2 * Ccg <
        cubeLowerEllipticityInv M R n (1 / 16) (by norm_num) exponentTwo omega *
          ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))} ⊆
      HCPolySupport.IndependentSums.upperTailEvent Y Ccg := by
    intro omega homega
    have hfail : 2 * Ccg <
        cubeLowerEllipticityInv M R n (1 / 16) (by norm_num) exponentTwo omega *
          ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := homega
    have hdom := hY.dominates omega n (by omega)
    show Ccg < Y omega
    linarith
  have ht1 : (1 : ℝ) ≤ Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) :=
    (one_le_div hApos).2 (le_trans hAle hCcg)
  have htail := hY.tail ht1
  have hlevel : Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) *
      (Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) = Ccg := by
    field_simp
  rw [hlevel] at htail
  refine le_trans (le_trans (measureReal_mono hsub) htail) ?_
  rw [HCPolySupport.IndependentSums.gammaSigma_inv]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have hquotient : Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) =
      Ccg * Real.exp (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹) := by
    rw [Real.exp_neg]
    field_simp
  have hge : Real.exp (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹) ≤
      Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) := by
    rw [hquotient]
    nlinarith [Real.exp_pos (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹), hCcg]
  have hquarter : ((1 : ℝ) - 1 / 2) / 2 = 1 / 4 := by norm_num
  rw [hquarter]
  have hrpow : Real.exp (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹) ^ ((1 : ℝ) / 4) ≤
      (Ccg / Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (Real.exp_pos _).le hge (by norm_num)
  have hexpid : Real.exp (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹) ^ ((1 : ℝ) / 4) =
      Real.exp ((1 / 4 : ℝ) * (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hexpid] at hrpow
  exact hrpow

/-! ## The subcube cover of the failure event -/

/-- **The subcube decomposition of the failure event** (ABK26), almost surely:
at the re-based constant `2 Ccg` the printed-cube coarse-ellipticity failure
event is covered by the scale-`n` translate events at the bare level `2 Ccg`. -/
theorem coarseEllipticityFailure_ae_subset_biUnion (M : ABKModel d) {Ccg : ℝ}
    (Q : TriadicCube d) {n : ℤ} (hnm : n < Q.scale) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ coarseEllipticityFailure M (2 * Ccg) Q n →
        omega ∈ ⋃ R ∈ descendantsAtScale Q n,
          {omega : CutoffSample d | 2 * Ccg <
            cubeLowerEllipticityInv M R n (1 / 16) (by norm_num) exponentTwo omega *
              ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))} := by
  have hs : (descendantsAtScale Q n).Nonempty :=
    descendantsAtScale_nonempty Q (le_of_lt hnm)
  have hsig : (0 : ℝ) < ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar_characterization M (n - 1)).1
  filter_upwards [cubeLowerEllipticityInv_le_two_mul_finsetSupReal_ae M Q
    (le_of_lt hnm)] with omega htrans homega
  by_contra hcon
  have hall : ∀ R ∈ descendantsAtScale Q n,
      cubeLowerEllipticityInv M R n (1 / 16) (by norm_num) exponentTwo omega ≤
        2 * Ccg / ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := by
    intro R hR
    rw [le_div_iff₀ hsig]
    by_contra hlt
    exact hcon (Set.mem_biUnion hR (not_le.1 hlt))
  have hsup : Ch02.finsetSupReal (descendantsAtScale Q n) (fun R =>
      cubeLowerEllipticityInv M R n (1 / 16) (by norm_num) exponentTwo omega) ≤
        2 * Ccg / ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) :=
    Ch02.finsetSupReal_le _ hs hall
  have hgap : scaleGapPos Q.scale n = 0 := scaleGapPos_of_lt hnm
  have hfail : 2 * (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) * (2 * Ccg) <
      cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo omega *
        ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := homega
  rw [hgap, mul_zero, Real.rpow_zero, mul_one] at hfail
  have hchain : cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo
      omega ≤ 2 * (2 * Ccg /
        ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) :=
    le_trans htrans (by linarith)
  have hprod := mul_le_mul_of_nonneg_right hchain hsig.le
  have hcancel : 2 * (2 * Ccg /
      ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))) *
      ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) = 4 * Ccg := by
    field_simp
    ring
  rw [hcancel] at hprod
  linarith

/-! ## The branch, loss-carrying and gate-free -/

/-- **The case `n < m` of the coarse-ellipticity branch** (ABK26), with the
union loss carried:

```
P[ lambda^{-1}_{1/8,2}(square_m; a_n) sigmabar_{n-1} > 2 . (2 Ccg) ]
  <= 3^{d(m-n)} exp( - exp( (1/4) Ccg^{-1} E^{-2} gamma^{-1} ) ) .
```

There is no hypothesis on `m - n`: the cardinality of the translate set appears
in the conclusion, where the manuscript puts it into an "adjusted" constant `c`,
which a dimension-only `c` cannot absorb.  The passage to the printed shape is
`measureReal_coarseEllipticityFailure_le_of_absorb`.

The constant `2 Ccg` at which the failure event is read is the `Ccg` re-basing
(gap route, `G <= 2`); `hcg` is the coarse-graining input at every translate,
at the exponent `t = 1/16`. -/
theorem measureReal_coarseEllipticityFailure_le_of_translateCoarseBounds
    (M : ABKModel d) {Ccg : ℝ} (hCcg : 1 ≤ Ccg) (Q : TriadicCube d) {n : ℤ}
    {E : ℝ} (hnm : n < Q.scale) (hgamma : M.gamma ≤ 1 / 16)
    (hcg : ∀ R ∈ descendantsAtScale Q n,
      Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - 1 / 2) / 2))
        (fun L : ℤ => fun omega =>
          cubeLowerEllipticityInv M R L (1 / 16) (by norm_num) exponentTwo omega *
            (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
        (n - 1)
        (Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 16)
          exponentTwo)
        (Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)))) :
    (cutoffSampleLaw M).toMeasure.real (coarseEllipticityFailure M (2 * Ccg) Q n) ≤
      ((descendantsAtScale Q n).card : ℝ) *
        Real.exp (-Real.exp ((1 / 4 : ℝ) *
          (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) := by
  have hCcg0 : (0 : ℝ) < Ccg := lt_of_lt_of_le zero_lt_one hCcg
  set Ev : TriadicCube d → Set (CutoffSample d) := fun R =>
    {omega : CutoffSample d | 2 * Ccg <
      cubeLowerEllipticityInv M R n (1 / 16) (by norm_num) exponentTwo omega *
        ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))} with hEv
  have hmono : (Cutoff.cutoffSampleLaw M).toMeasure
        (coarseEllipticityFailure M (2 * Ccg) Q n) ≤
      (Cutoff.cutoffSampleLaw M).toMeasure (⋃ R ∈ descendantsAtScale Q n, Ev R) :=
    measure_mono_ae (coarseEllipticityFailure_ae_subset_biUnion M Q hnm)
  have hreal : (cutoffSampleLaw M).toMeasure.real
      (coarseEllipticityFailure M (2 * Ccg) Q n) ≤
      (cutoffSampleLaw M).toMeasure.real (⋃ R ∈ descendantsAtScale Q n, Ev R) :=
    ENNReal.toReal_mono (measure_ne_top _ _) hmono
  refine le_trans hreal (le_trans (measureReal_biUnion_finset_le _ _) ?_)
  have hterm : ∀ R ∈ descendantsAtScale Q n,
      (cutoffSampleLaw M).toMeasure.real (Ev R) ≤
        Real.exp (-Real.exp ((1 / 4 : ℝ) *
          (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) := fun R hR =>
    measureReal_translateCoarseEllipticityTail_le M hCcg R hgamma (hcg R hR)
  calc ∑ R ∈ descendantsAtScale Q n,
        (cutoffSampleLaw M).toMeasure.real (Ev R)
      ≤ ∑ _R ∈ descendantsAtScale Q n,
          Real.exp (-Real.exp ((1 / 4 : ℝ) *
            (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) := Finset.sum_le_sum hterm
    _ = ((descendantsAtScale Q n).card : ℝ) *
          Real.exp (-Real.exp ((1 / 4 : ℝ) *
            (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## The absorption of the union loss -/

/-- The logarithm of the union loss is the manuscript's own `d (m - n) log 3`. -/
theorem log_card_descendantsAtScale (Q : TriadicCube d) {n : ℤ}
    (hn : n ≤ Q.scale) :
    Real.log ((descendantsAtScale Q n).card : ℝ) =
      (d : ℝ) * ((Q.scale : ℝ) - (n : ℝ)) * Real.log 3 := by
  have hcard : (descendantsAtScale Q n).card =
      (3 ^ d) ^ Int.toNat (Q.scale - n) := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hn]
    exact descendantsAtDepth_card Q (Int.toNat (Q.scale - n))
  have hnn : (0 : ℤ) ≤ Q.scale - n := by omega
  have hcast : ((Int.toNat (Q.scale - n) : ℕ) : ℝ) = (Q.scale : ℝ) - (n : ℝ) := by
    have := Int.toNat_of_nonneg hnn
    have hz : ((Int.toNat (Q.scale - n) : ℤ) : ℝ) = ((Q.scale - n : ℤ) : ℝ) := by
      rw [this]
    push_cast at hz
    exact hz
  rw [hcard]
  push_cast
  rw [Real.log_pow, Real.log_pow, hcast]
  ring

/-- **The absorption of the union loss.**  If the entropy of the `3^{d(m-n)}`
translates fits under the per-translate double exponent with room `T` to spare,
the branch is delivered at the level `exp(-T)`.

The hypothesis `hAbsorb` is *the* inequality the manuscript's needs and does not
state; by `log_card_descendantsAtScale` it reads

```
d (m - n) log 3 + T <= exp( (1/4) Ccg^{-1} E^{-2} gamma^{-1} ) .
```

It is a restriction on the scale separation `m - n`, not a constant adjustment. -/
theorem measureReal_coarseEllipticityFailure_le_of_absorb (M : ABKModel d)
    {Ccg : ℝ} (hCcg : 1 ≤ Ccg) (Q : TriadicCube d) {n : ℤ} {E T : ℝ}
    (hnm : n < Q.scale) (hgamma : M.gamma ≤ 1 / 16)
    (hcg : ∀ R ∈ descendantsAtScale Q n,
      Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - 1 / 2) / 2))
        (fun L : ℤ => fun omega =>
          cubeLowerEllipticityInv M R L (1 / 16) (by norm_num) exponentTwo omega *
            (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
        (n - 1)
        (Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 16)
          exponentTwo)
        (Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))))
    (hAbsorb : Real.log ((descendantsAtScale Q n).card : ℝ) + T ≤
      Real.exp ((1 / 4 : ℝ) * (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) :
    (cutoffSampleLaw M).toMeasure.real (coarseEllipticityFailure M (2 * Ccg) Q n) ≤
      Real.exp (-T) := by
  have hs : (descendantsAtScale Q n).Nonempty :=
    descendantsAtScale_nonempty Q (le_of_lt hnm)
  have hcardpos : (0 : ℝ) < ((descendantsAtScale Q n).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hs
  refine le_trans (measureReal_coarseEllipticityFailure_le_of_translateCoarseBounds
    M hCcg Q hnm hgamma hcg) ?_
  have hexp : ((descendantsAtScale Q n).card : ℝ) =
      Real.exp (Real.log ((descendantsAtScale Q n).card : ℝ)) :=
    (Real.exp_log hcardpos).symm
  rw [hexp, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

/-- **The printed shape of the branch**, under the explicit entropy gate.  With
`T = exp((1/8) Ccg^{-1} E^{-2} gamma^{-1})` the conclusion is the manuscript's
own display, at the dimension-only constant `c = Ccg^{-1}/8` (the proved `n >=
m` branch delivers `Ccg^{-1}/4`, which is stronger, so the two branches combine
at `Ccg^{-1}/8`).

The gate is stated in the manuscript's own variables: `m = Q.scale`, `n`, and
`d`. -/
theorem measureReal_coarseEllipticityFailure_le_printed_of_gap (M : ABKModel d)
    {Ccg : ℝ} (hCcg : 1 ≤ Ccg) (Q : TriadicCube d) {n : ℤ} {E : ℝ}
    (hnm : n < Q.scale) (hgamma : M.gamma ≤ 1 / 16)
    (hcg : ∀ R ∈ descendantsAtScale Q n,
      Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - 1 / 2) / 2))
        (fun L : ℤ => fun omega =>
          cubeLowerEllipticityInv M R L (1 / 16) (by norm_num) exponentTwo omega *
            (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
        (n - 1)
        (Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 16)
          exponentTwo)
        (Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))))
    (hgap : (d : ℝ) * ((Q.scale : ℝ) - (n : ℝ)) * Real.log 3 +
        Real.exp ((1 / 8 : ℝ) * (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      Real.exp ((1 / 4 : ℝ) * (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) :
    (cutoffSampleLaw M).toMeasure.real (coarseEllipticityFailure M (2 * Ccg) Q n) ≤
      Real.exp (-Real.exp ((1 / 8 : ℝ) *
        (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) := by
  refine measureReal_coarseEllipticityFailure_le_of_absorb M hCcg Q hnm hgamma
    hcg ?_
  rw [log_card_descendantsAtScale Q (le_of_lt hnm)]
  exact hgap

end

end Algsuperdiff.Section3.Provider.BadEvents
