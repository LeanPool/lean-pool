/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumCarrierDecorrelation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ValuePathTransport
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# ShellSumCarrierLaw

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The shell-sum law on the continuous-path carrier

ABK26, `e.def.w` and `e.perturb.assumption`.

`Algsuperdiff/Section3/Provider/Corrector/ValuePathTransport.lean` puts the
**fresh shell** on the compact-open carrier `C(Vec d, Mat d)` -- the only
carrier in this repository that supplies the joint measurability
`MeasurableVAdd₂ (Vec d) Ω` the `Ω`-level decorrelation chain needs -- as the
law `zeroShellValuePathLaw`.  The recurrence consumers force not with one shell
but with the finite shell increment `k_m - k_n = Σ_{k ∈ (n,m]} j_k`
(`Cutoff.finiteShellIncrement`, `Corrector.streamForcing`).

This module puts that increment on the *same* carrier, as
`shellSumValuePathLaw M n m`, and supplies the three carrier facts the chain
consumes.  The point of re-using `C(Vec d, Mat d)` rather than introducing a new
carrier is that **the forcing function does not change**: the shell-sum forcing
is literally `valuePathForcing e`, the same function of a continuous path that
`ValuePathTransport` uses; only the law on the carrier is new.  Every statement
of `ValuePathTransport` that is about the *function* therefore transfers
verbatim, and only the measure-dependent statements are reproved here.

## What is supplied

* `shellSumValuePath` -- the increment as a continuous matrix path, with
  `shellSumValuePath_apply` identifying its values with
  `Cutoff.finiteShellIncrement`.
* `shellSumValuePathLaw` -- its law, a probability measure on `C(Vec d, Mat d)`.
* `vaddInvariantMeasure_shellSumValuePathLaw` -- **stationarity**.  The input is
  `Cutoff.sequenceLaw_stationary`, i.e. (J1) stationarity of the zero shell
  transported to every shell by `e.diff.law.shift`
  (`ShellLawPrefix.marginal_scaling`) and lifted to the whole sequence by the
  cross-shell independence of ABK26.  No new assumption is used.
* `memLp_two_valuePathForcing_shellSum` -- the **`L²` layer** of the shell-sum
  forcing, the Minkowski step over the block of the frozen (J2) tail.
* `integral_inner_valuePathForcing_vadd_shellSum_eq_zero` -- the **covariance
  kill** at the increment's own range `√d · 3^m`, transported from
  `ShellSumCarrierDecorrelation.lean`.  This is exactly the `hcov` binder of
  `integral_normSq_mollify_le_of_helmholtz_of_covariance_support`, at the
  shell-sum carrier.
* `integral_normSq_mollify_le_of_helmholtz_shellSum` -- the **unconditional**
  decorrelation bound `E[|A_κ 𝐣|²] ≤ B · |B_{√d·3^m+1}| · E[|𝐟|²]` at this
  carrier, with no covariance, no `L²` and no instance obligation left on the
  caller.

## What is *not* supplied here

The Helmholtz splitting of the increment flux and the approximate-stream
assembly at this carrier are **not** proved in this module.
`OmegaStreamAssembly`'s `exists_freshShellStream` is stated at
`zeroShellValuePathLaw` and does *not* apply to `shellSumValuePathLaw`; its
shell-sum analogue remains open.  Nothing below claims any source-node status.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}

/-! ### The increment as a continuous matrix path -/

/-- The finite shell increment `k_m - k_n`, read as a continuous matrix path.
This is the same object as `Cutoff.finiteShellIncrement` (see
`shellSumValuePath_apply`) on the carrier that supports the joint translation
action. -/
def shellSumValuePath (n m : ℤ) (omega : ShellSeq d) : C(Vec d, Mat d) :=
  ∑ k ∈ Finset.Ioc n m, ShellField.valuePath (omega k)

@[simp]
theorem shellSumValuePath_apply (n m : ℤ) (omega : ShellSeq d) (x : Vec d) :
    shellSumValuePath n m omega x = finiteShellIncrement omega n m x := by
  rw [shellSumValuePath, ContinuousMap.sum_apply, finiteShellIncrement_apply]
  rfl

theorem measurable_shellSumValuePath (n m : ℤ) :
    Measurable (shellSumValuePath (d := d) n m) := by
  -- The two carrier facts making the compact-open path space second countable,
  -- hence its (continuous) addition jointly measurable for the Borel field.
  have : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  have : Filter.IsCountablyGenerated (uniformity (Mat d)) :=
    inferInstanceAs (Filter.IsCountablyGenerated (uniformity (Fin d → Fin d → ℝ)))
  exact Finset.measurable_sum _ fun k _ =>
    ShellField.measurable_valuePath.comp (measurable_pi_apply k)

/-- **The law of the finite shell increment on the continuous-path carrier.**
The analogue of `zeroShellValuePathLaw` with the single fresh shell replaced by
the block `(n, m]`. -/
def shellSumValuePathLaw (P : ProbabilityMeasure (ℤ → ShellField d)) (n m : ℤ) :
    ProbabilityMeasure C(Vec d, Mat d) :=
  P.map (shellSumValuePath (d := d) n m)

theorem shellSumValuePathLaw_toMeasure
    (P : ProbabilityMeasure (ℤ → ShellField d)) (n m : ℤ) :
    (shellSumValuePathLaw P n m).toMeasure =
      Measure.map (shellSumValuePath (d := d) n m) P.toMeasure :=
  rfl

/-! ### Equivariance and stationarity -/

/-- The increment path is equivariant: translating every shell of the sequence
translates the increment path. -/
theorem shellSumValuePath_translateSequence (n m : ℤ) (z : Vec d)
    (omega : ShellSeq d) :
    shellSumValuePath n m (ShellField.translateSequence z omega)
      = z +ᵥ shellSumValuePath (d := d) n m omega := by
  refine ContinuousMap.ext fun x => ?_
  rw [ShellField.vadd_apply, shellSumValuePath_apply, shellSumValuePath_apply,
    finiteShellIncrement_apply, finiteShellIncrement_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

/-- **The shell-sum law is translation invariant.**

The only input is `Cutoff.sequenceLaw_stationary`: (J1) stationarity of the zero
shell, transported to every shell marginal by `e.diff.law.shift`
(`ShellLawPrefix.marginal_scaling`), and lifted to the joint law of the sequence
by the cross-shell independence of ABK26, `ShellLawPrefix.independent`.  No
invariance is assumed on the target law. -/
theorem map_vadd_shellSumValuePathLaw (M : ABKModel d) (n m : ℤ) (z : Vec d) :
    Measure.map (fun f : C(Vec d, Mat d) => z +ᵥ f)
        (shellSumValuePathLaw M.P n m).toMeasure =
      (shellSumValuePathLaw M.P n m).toMeasure := by
  rw [shellSumValuePathLaw_toMeasure]
  calc
    Measure.map (fun f : C(Vec d, Mat d) => z +ᵥ f)
          (Measure.map (shellSumValuePath (d := d) n m) M.P.toMeasure)
        = Measure.map ((fun f : C(Vec d, Mat d) => z +ᵥ f) ∘
            shellSumValuePath (d := d) n m) M.P.toMeasure :=
      Measure.map_map (measurable_const_vadd z) (measurable_shellSumValuePath n m)
    _ = Measure.map (shellSumValuePath (d := d) n m ∘
          ShellField.translateSequence z) M.P.toMeasure := by
        refine congrArg
          (fun g : ShellSeq d → C(Vec d, Mat d) => Measure.map g M.P.toMeasure) ?_
        funext omega
        exact (shellSumValuePath_translateSequence n m z omega).symm
    _ = Measure.map (shellSumValuePath (d := d) n m)
          (Measure.map (ShellField.translateSequence z) M.P.toMeasure) :=
      (Measure.map_map (measurable_shellSumValuePath n m)
        (ShellField.measurable_translateSequence z)).symm
    _ = Measure.map (shellSumValuePath (d := d) n m) M.P.toMeasure := by
        rw [sequenceLaw_stationary M z]

instance vaddInvariantMeasure_shellSumValuePathLaw (M : ABKModel d) (n m : ℤ) :
    VAddInvariantMeasure (Vec d) C(Vec d, Mat d)
      (shellSumValuePathLaw M.P n m).toMeasure where
  measure_preimage_vadd := by
    intro z s hs
    rw [← Measure.map_apply (measurable_const_vadd z) hs]
    exact congrArg (fun mu : Measure C(Vec d, Mat d) => mu s)
      (map_vadd_shellSumValuePathLaw M n m z)

/-! ### The `L²` layer of the shell-sum forcing -/

/-- **The shell-sum forcing is square integrable on the continuous-path
carrier.**  Transported from `memLp_two_hilbertForcing_finiteShellIncrement`,
whose input is the Minkowski sum over the block of the frozen (J2) tail.  No
normalization of `e` is assumed. -/
theorem memLp_two_valuePathForcing_shellSum (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    MemLp (valuePathForcing e) 2 (shellSumValuePathLaw M.P n m).toMeasure := by
  rw [shellSumValuePathLaw_toMeasure,
    memLp_map_measure_iff (stronglyMeasurable_valuePathForcing e).aestronglyMeasurable
      (measurable_shellSumValuePath n m).aemeasurable]
  have hfun : (valuePathForcing e ∘ shellSumValuePath (d := d) n m)
      = fun omega : ShellSeq d =>
        HilbertVec.ofVec (matVecMul (finiteShellIncrement omega n m 0) e) := by
    funext omega
    rw [Function.comp_apply, valuePathForcing_apply, shellSumValuePath_apply]
  rw [hfun]
  exact memLp_two_hilbertForcing_finiteShellIncrement M e 0 n m

/-! ### The covariance kill at the increment's own range -/

/-- The pairing of the path forcing against its `w`-translate, evaluated at an
increment path. -/
private theorem inner_valuePathForcing_vadd_shellSumValuePath
    (e w : Vec d) (n m : ℤ) (omega : ShellSeq d) :
    (inner ℝ (valuePathForcing e (w +ᵥ shellSumValuePath n m omega))
        (valuePathForcing e (shellSumValuePath n m omega)) : ℝ)
      = vecDot (matVecMul (finiteShellIncrement omega n m w) e)
          (matVecMul (finiteShellIncrement omega n m 0) e) := by
  rw [valuePathForcing_apply, valuePathForcing_apply]
  simp only [HilbertVec.inner_def, HilbertVec.toVec_ofVec]
  rw [ShellField.vadd_apply, zero_add, shellSumValuePath_apply,
    shellSumValuePath_apply]

/-- **The shell-sum forcing has compactly supported covariance on the
continuous-path carrier.**

For every translation `w` with `√d · 3^m < ‖w‖`, the covariance of the path
forcing against its `w`-translate vanishes under the shell-sum law.  This is
literally the `hcov` binder of
`integral_normSq_mollify_le_of_helmholtz_of_covariance_support` at
`Ω := C(Vec d, Mat d)` and `μ := (shellSumValuePathLaw M.P n m).toMeasure`; the
(J1) range dependence, `e.diff.law.shift` and the cross-shell independence
argument is not repeated, it is transported from
`integral_vecDot_matVecMul_finiteShellIncrement_eq_zero_of_lt_norm`. -/
theorem integral_inner_valuePathForcing_vadd_shellSum_eq_zero_of_lt_norm
    (M : ABKModel d) (e : Vec d) (n m : ℤ) {w : Vec d}
    (hw : Real.sqrt (d : ℝ) * (3 : ℝ) ^ m < ‖w‖) :
    ∫ f, inner ℝ (valuePathForcing e (w +ᵥ f)) (valuePathForcing e f)
      ∂(shellSumValuePathLaw M.P n m).toMeasure = 0 := by
  have hpathm : StronglyMeasurable (fun f : C(Vec d, Mat d) =>
      (inner ℝ (valuePathForcing e (w +ᵥ f)) (valuePathForcing e f) : ℝ)) :=
    (((continuous_valuePathForcing e).comp
        (ShellField.continuous_const_vadd w)).stronglyMeasurable).inner
      (stronglyMeasurable_valuePathForcing e)
  rw [shellSumValuePathLaw_toMeasure,
    integral_map (measurable_shellSumValuePath n m).aemeasurable
      hpathm.aestronglyMeasurable,
    integral_congr_ae (Filter.Eventually.of_forall
      (inner_valuePathForcing_vadd_shellSumValuePath e w n m))]
  exact integral_vecDot_matVecMul_finiteShellIncrement_eq_zero_of_lt_norm M e n m hw

/-- The covariance support statement at the concrete admissible radius
`√d · 3^m + 1`. -/
theorem integral_inner_valuePathForcing_vadd_shellSum_eq_zero
    (M : ABKModel d) (e : Vec d) (n m : ℤ) (w : Vec d)
    (hw : Real.sqrt (d : ℝ) * (3 : ℝ) ^ m + 1 ≤ ‖w‖) :
    ∫ f, inner ℝ (valuePathForcing e (w +ᵥ f)) (valuePathForcing e f)
      ∂(shellSumValuePathLaw M.P n m).toMeasure = 0 :=
  integral_inner_valuePathForcing_vadd_shellSum_eq_zero_of_lt_norm M e n m
    (by linarith)

/-! ### The unconditional shell-sum decorrelation bound -/

/-- **The shell-sum decorrelation bound, with no covariance hypothesis.**

Let `𝐣 = 𝐟 + p` be a stationary Helmholtz splitting of the shell-sum forcing
`𝐟 = valuePathForcing e` under the shell-sum law: `p` lies in the stationary
potential subspace of that carrier and `𝐣` in its stationary solenoidal
subspace.  Then for every probability density `κ` bounded by `B`,

`E[|A_κ 𝐣|²] ≤ B · |B_{√d·3^m+1}| · E[|𝐟|²]`.

Compared with `integral_normSq_mollify_le_of_helmholtz_of_covariance_support`,
the covariance support hypothesis `hcov` is discharged here at the increment's
own range from (J1), `e.diff.law.shift` and the cross-shell independence, the
`L²` layer of the forcing is discharged from (J2), and all three carrier
instances are available, so no instance obligation is left on the caller.  The
remaining binders are the caller's Helmholtz data.

This is the exact shell-sum analogue of
`ValuePathTransport.integral_normSq_mollify_le_of_helmholtz_valuePath`, with the
radius `√d + 1` of the single fresh shell replaced by the increment's own range
`√d · 3^m + 1`. -/
theorem integral_normSq_mollify_le_of_helmholtz_shellSum (M : ABKModel d)
    (e : Vec d) (n m : ℤ)
    {kappa : Vec d → ℝ} (hk0 : ∀ y, 0 ≤ kappa y) (hkc : Continuous kappa)
    (hki : Integrable kappa volume) (hk1 : ∫ y, kappa y = 1) {B : ℝ}
    (hkB : ∀ y, kappa y ≤ B)
    {p j : C(Vec d, Mat d) → HilbertVec d}
    (hpm : StronglyMeasurable p)
    (hp : MemLp p 2 (shellSumValuePathLaw M.P n m).toMeasure)
    (hjm : StronglyMeasurable j)
    (hj : MemLp j 2 (shellSumValuePathLaw M.P n m).toMeasure)
    (hjdef : ∀ f, j f = valuePathForcing e f + p f)
    (hpmem : hp.toLp p ∈ Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
      (μ := (shellSumValuePathLaw M.P n m).toMeasure) (d := d))
    (hjmem : hj.toLp j ∈ Algsuperdiff.Probability.Stationary.stationarySolenoidalSubspace
      (μ := (shellSumValuePathLaw M.P n m).toMeasure) (d := d)) :
    ∫ f, ‖mollify kappa j f‖ ^ 2 ∂(shellSumValuePathLaw M.P n m).toMeasure
      ≤ B * (volume (Metric.ball (0 : Vec d)
              (Real.sqrt (d : ℝ) * (3 : ℝ) ^ m + 1))).toReal
          * ∫ f, ‖valuePathForcing e f‖ ^ 2
              ∂(shellSumValuePathLaw M.P n m).toMeasure :=
  integral_normSq_mollify_le_of_helmholtz_of_covariance_support hk0 hkc hki hk1 hkB
    (stronglyMeasurable_valuePathForcing e)
    (memLp_two_valuePathForcing_shellSum M e n m)
    hpm hp hjm hj hjdef hpmem hjmem
    (integral_inner_valuePathForcing_vadd_shellSum_eq_zero M e n m)

end

end Algsuperdiff.Section3.Provider.Corrector
