/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5DefectGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.StepProducers
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffLawTransport

/-!
# Step5Basket

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-5 analytic basket: the gate, the re-sited gauge, and the defect binder

`Closure.JunctionDischargeStepFiveDisplay.step5GaugeEndpoint_of_correctors_gauge`
reduces `Closure.Step5GaugeEndpoint` to a list of named legs, read at a
**per-cube** forcing gauge.  `Closure.StepProducers.step5GaugeEndpoint_closureFamilies_of_legs`
discharges, at the closure's own corrector families and at that per-cube gauge,
the seven legs that are statements about those families rather than displays of
the manuscript.  This module

* discharges three more legs outright --- `hgate`, `hmemGauge` and `hdefect` ---
  at the gauge
  `fun R omega => 3^nmesh * shellDerivNormSum n (n+h) (triadicCubeShift R) omega`;
* assembles all ten into `step5GaugeEndpoint_closureFamilies_of_gaugeLegs`,
  which is `Closure.Step5GaugeEndpoint` at the closure families with exactly the
  residual analytic basket left as binders;
* assembles those into `step5GaugeEndpoint_closureFamilies_of_momentLegs`, in
  which `hshell` and `hgradM` are read at the two **explicit** grid fourth
  moments the Hoelder step produces.

## What is proved

| leg | content | route |
|---|---|---|
| `hCdef` | `0 <= Cdef` at `Cdef = step5CrossDefectConst d` |
`Step5DefectGauge.step5CrossDefectConst_nonneg` |
| `hgate` | `step5CrossDefectConst d * cgamma^15 <= 2` |
`step5CrossDefectConst_mul_gamma_pow_fifteen_le_two_of_regime`: the regime's own `C c⋆^{-1} <= E`
and `cgamma <= E^{-5}`, at the *d*-dependent threshold `step5GateConst d = 1 + d^3`, exactly the
enlargement device of `Closure.ClosureFinalArithmetic` |
| `hgauge0` | the gauge is nonnegative | discharged inline by `Closure.StepProducers`; also
available here as `step5Gauge_nonneg` |
| `hmemGauge` | the per-cube gauge is `L^4` in the sample | `memLp_four_step5Gauge`:
`LocalizationOscillationDisplay.integrable_shellDerivNormSum_rpow_four` on `M.P`, transported to
`(cutoffSampleLaw M)` along the measurable embedding
`Provider.Stream.measurableEmbedding_cutoffSample_val` and `Cutoff.map_cutoffSampleLaw_val` |
| `hdefect` | the per-cube step at the closure's grid | `step5CrossDefect_le_step5Gauge`:
`Step5DefectGauge.step5CrossDefect_le_meshOscillationCell` at `R.scale = K - j = nmesh <= n` |
| `hD`, `hN` | `e.def.w` at the two closure families | `Closure.ClosureAssembly` |
| `hmemD`, `hintD`, `hsampN`, `hsampG` | the four Dirichlet spatial/sample routes |
`Closure.StepProducers` |
| `hprod`, `hgrad0` | the Hoelder split on the grid |
`descendantsAverage_integral_vecNormSq_matVecMul_le`: `|A_R v_R|^2 <= ||A_R||^2 |v_R|^2`,
Cauchy--Schwarz in the sample at the second moment, then Cauchy--Schwarz on the finite grid |
| `hsampX`, `hsampS` | the two remaining per-cube sample integrabilities |
`integrable_vecDot_matVecMul_of_memLp_four`, `integrable_vecNormSq_matVecMul_of_memLp_four`, from
the same two fourth-moment legs plus measurability |

The gate is the same device `Closure.ClosureFinalArithmetic` already uses for
the two regime facts: `step5CrossDefectConst d` is dimensional and absolute, `E
>= 2C/3` and `cgamma <= E^{-1}` give `cgamma^15 <= (2C/3)^{-1}`, and `C >= 1 +
d^3 >= 2 step5CrossDefectConst d` closes it.  No smallness of the manuscript is
assumed: the threshold is *produced*, and it is consumed only inside
`Closure.ClosureRegime`.

## The residual basket

`step5GaugeEndpoint_closureFamilies_of_momentLegs` still carries, as binders,
exactly the legs that this lane did **not** reach:

* `hintP`, `hsampDef` --- two integrability side conditions on the cube and on
  the sample;
* `hmeasX`, `hmeasS` --- the sample measurability of the two per-cube pairings.
  Both legs are now proved at the full sigma-algebra, at the closure's own
  families, as
  `Closure.Step5InputSideConditions.aestronglyMeasurable_step5PairingX` and
  `...aestronglyMeasurable_step5PairingS`, and it is those that the downstream
  assembly consumes.  They remain *binders* of this module only because this
  module sits below `Closure.Step5InputSideConditions` in the import order;
* `hAmem`, `hvmem` --- the `L^4` sample membership of the per-cube shell and
  gradient averages;
* `hmemOsc` --- the `L^4` sample membership of the mesh oscillation cell;
* `hosc` --- `e.lower.bound.oscillations`, whose re-sited shape is exactly
`exists_gamma0_freshShellDirichlet_step5MeshOscillationResited_le_gamma_pow_fifteen`
  and whose own binders (`hmem8`, the octic grid envelope `E`, the recurrence
  gates) are not discharged here;
* `hshell`, `hgradM` --- the two moment inputs `e.km.kn.Lp` and
  `e.nablaw.in.L.eight`, read at the two explicit grid fourth moments.

Nothing below papers over any of them.  In particular **no**
`Closure.ClosureStep5Input` is produced by this module: the residual basket
above is still carried as binders here.

The *second* reason previously given --- that `Closure.ClosureStep5Input` "is
quantified over every `d` with `NeZero d`, whereas the re-sited oscillation
endpoint. is available only for `2 <= d`" --- is **obsolete and was never an
obstruction**: `Closure.ClosureFinal.ClosureStep5Input d` is *defined* as `2 <=
d ->.`, so the `2 <= d` restriction of the Step-5 inputs is exactly the
hypothesis that statement supplies.  The residual basket, not the dimension
quantifier, is the whole reason this module stops short; and that basket is
itself discharged downstream, in `Closure.Step5Input` (nine legs) and
`Closure.Step5SampDef` (the tenth), which together produce
`Closure.ClosureStep5Input d` for every `d` with `NeZero d`.

## References

* ABK26, `e.lower.bound.pre2`; the Step-5 estimate; `e.nablaw.oscillations`;
  `e.lower.bound.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The gate `Cdef cgamma^15 <= 2` -/

/-- The absolute, dimension-dependent threshold at which the manuscript's
standing hypotheses `C c⋆^{-1} <= E` and `cgamma <= E^{-5}` already deliver the
Step-5 defect gate.  It is the Step-5 analogue of
`Closure.closureRegimeConst`. -/
def step5GateConst (d : ℕ) : ℝ := 1 + (d : ℝ) ^ 3

theorem step5GateConst_pos (d : ℕ) : 0 < step5GateConst d := by
  unfold step5GateConst
  positivity

theorem one_le_step5GateConst (d : ℕ) : 1 ≤ step5GateConst d := by
  unfold step5GateConst
  have hcube : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
  linarith

theorem sqrt_natCast_le_self (d : ℕ) : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
  have hle : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    have h : (d : ℕ) ≤ d ^ 2 := Nat.le_self_pow (by norm_num) d
    have hc := (Nat.cast_le (α := ℝ)).2 h
    calc (d : ℝ) ≤ ((d ^ 2 : ℕ) : ℝ) := hc
      _ = (d : ℝ) ^ 2 := by push_cast; ring
  have h2 := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (Nat.cast_nonneg d)] at h2

/-- The geometric constant of the per-cube defect step is at most half the
threshold. -/
theorem two_mul_step5CrossDefectConst_le (d : ℕ) :
    2 * step5CrossDefectConst d ≤ step5GateConst d := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsq := sqrt_natCast_le_self d
  have hstep : (d : ℝ) ^ 2 * Real.sqrt (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2)
    nlinarith [hmul]
  unfold step5CrossDefectConst step5GateConst
  nlinarith [hstep]

/-- **`hgate`, from the regime's own antecedents.**

`Closure.ClosureRegime` carries `C c⋆^{-1} <= E` and `cgamma <= E^{-5}`.  At
the absolute threshold `step5GateConst d` these already force `Cdef cgamma^15
<= 2` for the geometric constant `Cdef = step5CrossDefectConst d` of the
per-cube step.  This is the same enlargement device
`Closure.gamma_le_exp_neg_one_of_regime` and
`Closure.three_mul_switchBudget_le_one_of_regime` use, with a `d`-dependent
threshold in place of an absolute one. -/
theorem step5CrossDefectConst_mul_gamma_pow_fifteen_le_two_of_regime
    (M : ABKModel d) {C : ℝ} (hCbig : step5GateConst d ≤ C)
    {Ec : {E : ℝ // 1 ≤ E}}
    (hCE : C * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ))
    (hgammaE : M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ)) :
    step5CrossDefectConst d * M.gamma ^ (15 : ℕ) ≤ 2 := by
  have hgate := two_mul_step5CrossDefectConst_le d
  have hC1 : (1 : ℝ) ≤ C := le_trans (one_le_step5GateConst d) hCbig
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hEbig := two_thirds_mul_le_of_regime M hC0 hCE
  have hE1 : (1 : ℝ) ≤ (Ec : ℝ) := Ec.2
  have hgi := gamma_le_inv_of_regime M hgammaE
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgamma1 : M.gamma ≤ 1 := by
    have hinv1 : ((Ec : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right; exact hE1
    linarith
  have hpow : M.gamma ^ (15 : ℕ) ≤ M.gamma :=
    pow_le_of_le_one hgamma0.le hgamma1 (by norm_num)
  have hCpos : (0 : ℝ) < 2 / 3 * C := by linarith
  have hinvle : ((Ec : ℝ))⁻¹ ≤ (2 / 3 * C)⁻¹ := by
    have hone := one_div_le_one_div_of_le hCpos hEbig
    rwa [one_div, one_div] at hone
  have hconst0 : (0 : ℝ) ≤ step5CrossDefectConst d := step5CrossDefectConst_nonneg d
  have hchain : M.gamma ^ (15 : ℕ) ≤ (2 / 3 * C)⁻¹ := le_trans hpow (le_trans hgi hinvle)
  have hmul : step5CrossDefectConst d * M.gamma ^ (15 : ℕ) ≤
      step5CrossDefectConst d * (2 / 3 * C)⁻¹ :=
    mul_le_mul_of_nonneg_left hchain hconst0
  have hle2 : step5CrossDefectConst d * (2 / 3 * C)⁻¹ ≤ 2 := by
    rw [mul_inv_le_iff₀ hCpos]
    nlinarith [hgate, hCbig, hC0]
  linarith

/-! ## `hmemGauge`: the re-sited forcing gauge is `L^4` in the sample -/

/-- **Unconditional.**  `L^p` membership transports from the shell-sequence law
to the cutoff sample law along the sample inclusion, which is a measurable
embedding pushing the sample law forward onto `M.P`. -/
theorem memLp_comp_val_cutoffSampleLaw (M : ABKModel d) {p : ℝ≥0∞} {G : ShellSeq d → ℝ}
    (hG : MemLp G p M.P.toMeasure) :
    MemLp (fun omega : CutoffSample d => G omega.val) p (cutoffSampleLaw M).toMeasure := by
  have hiff :=
    (Provider.Stream.measurableEmbedding_cutoffSample_val (d := d)).memLp_map_measure_iff
      (μ := (cutoffSampleLaw M).toMeasure) (g := G) (p := p)
  rw [map_cutoffSampleLaw_val] at hiff
  exact hiff.1 hG

/-- The forcing gauge of `e.nablaw.oscillations` is `L^4` on the shell-sequence
law: its fourth power is integrable by the weak-Orlicz tail
`e.nabla.km.kn.infty`. -/
theorem memLp_four_shellDerivNormSum (M : ABKModel d) {lowScale highScale : ℤ}
    (hlt : lowScale < highScale) (z : Vec d) :
    MemLp (fun omega : ShellSeq d => shellDerivNormSum lowScale highScale z omega) 4
      M.P.toMeasure := by
  refine (integrable_norm_rpow_iff
    (measurable_shellDerivNormSum lowScale highScale z).aestronglyMeasurable
    (by norm_num) (by norm_num)).1 ?_
  have hfun : (fun x : ShellSeq d =>
      ‖shellDerivNormSum lowScale highScale z x‖ ^ ((4 : ℝ≥0∞).toReal)) =
      fun x : ShellSeq d => shellDerivNormSum lowScale highScale z x ^ (4 : ℝ) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (shellDerivNormSum_nonneg lowScale highScale z x)]
    norm_num
  rw [hfun]
  exact integrable_shellDerivNormSum_rpow_four M hlt z

/-- **`hmemGauge` at the re-sited gauge**, on the closure's own sample
carrier. -/
theorem memLp_four_step5Gauge (M : ABKModel d) {lowScale highScale : ℤ}
    (hlt : lowScale < highScale) (nmesh : ℤ) (R : TriadicCube d) :
    MemLp (fun omega : CutoffSample d =>
        (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
          shellDerivNormSum lowScale highScale (triadicCubeShift R) omega.val) 4
      (cutoffSampleLaw M).toMeasure :=
  (memLp_comp_val_cutoffSampleLaw M
    (memLp_four_shellDerivNormSum M hlt (triadicCubeShift R))).const_mul _

/-! ## `hdefect` at the closure's grid -/

theorem scale_of_mem_descendantsAtDepth_originCube {K : ℤ} {j : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d K) j) : R.scale = K - (j : ℤ) := by
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
  have hQ : (originCube d K).scale = K := by simp [originCube]
  rw [hscale, hQ]

/-- **`hdefect` at the mesh grid `descendantsAtDepth cu_K j`.**

Every cube of that grid has scale `K - j`; at `nmesh = K - j <= n` the per-cube
step, proved in `Closure.Step5DefectGauge`, is literally the binder, the
forcing gauge being read at each cube's own base point. -/
theorem step5CrossDefect_le_step5Gauge {K : ℤ} {j : ℕ} {nmesh n m : ℤ}
    (hmesh : K - (j : ℤ) = nmesh) (hsc : nmesh ≤ n) {e : Vec d} (he : vecNorm e ≤ 1)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d K) j)
    (omega : ShellSeq d) (u : Vec d → Vec d)
    (hu : MemLp u 2 (normalizedCubeMeasure R)) :
    step5CrossDefect R omega n m e u ≤
      step5CrossDefectConst d *
        (meshOscillationCell nmesh u R *
          ((3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
            shellDerivNormSum n m (triadicCubeShift R) omega)) := by
  have hRscale : R.scale = nmesh := by
    rw [scale_of_mem_descendantsAtDepth_originCube hR, hmesh]
  have hbase := step5CrossDefect_le_meshOscillationCell R omega n m
    (by rw [hRscale]; exact hsc) he u hu
  rwa [hRscale] at hbase

/-! ## The Step-5 endpoint at the closure families, at the re-sited gauge -/

/-- **`Closure.Step5GaugeEndpoint` at the closure's own corrector families and
at the per-cube forcing gauge, with nine legs discharged.**

This adds, to the seven family legs already discharged by
`Closure.StepProducers.step5GaugeEndpoint_closureFamilies_of_legs`, the three
legs `hCdef`, `hdefect` and `hmemGauge`, all *proved*: the gauge is sited at
each cube's own base point, which is exactly what makes `hdefect`
dischargeable.

What remains are exactly the residual analytic legs listed in the module
docstring.  No smallness, no normalization and no bound of ABK26 is assumed
here: `hgate` is supplied by the caller from
`step5CrossDefectConst_mul_gamma_pow_fifteen_le_two_of_regime`, i.e. from
`Closure.ClosureRegime` itself. -/
theorem step5GaugeEndpoint_closureFamilies_of_gaugeLegs [NeZero d] (M : ABKModel d)
    (n : ℤ) (h : ℕ) (K j : ℕ) {e : Vec d} (he : vecNormSq e = 1) {nmesh : ℤ}
    (hmesh : (K : ℤ) - (j : ℤ) = nmesh) (hsc : nmesh ≤ n) (hh : 0 < h)
    {C1 C2 shellMoment gradMoment : ℝ}
    (hgate : step5CrossDefectConst d * M.gamma ^ (15 : ℕ) ≤ 2)
    (hintP : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n (n + (h : ℤ)) x)
        ((alongIncrementPath n h
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
            omega).toH1Function.grad x)))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hsampX : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampS : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampDef : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x))
          (cutoffSampleLaw M).toMeasure)
    (hmemOsc : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp
          (fun omega : CutoffSample d =>
            meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
            omega.val).toH1Function.grad x) R) 4
          (cutoffSampleLaw M).toMeasure)
    (hosc : (gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (descendantsAtDepth (originCube d (K : ℤ)) j)
      (fun R omega => meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
            omega.val).toH1Function.grad x) R)) +
      ((Annealed.sigmaBar M n : ℝ))⁻¹ *
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (descendantsAtDepth (originCube d (K : ℤ)) j)
        (fun (R : TriadicCube d) (omega : CutoffSample d) =>
          (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
            shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R) omega.val) ≤
      M.gamma ^ (15 : ℕ))
    (hC1 : 0 ≤ C1) (hgrad0 : 0 ≤ gradMoment)
    (hprod : descendantsAverage (originCube d (K : ℤ)) j
          (fun R => ∫ omega : CutoffSample d,
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x)))
            ∂(cutoffSampleLaw M).toMeasure)
      ≤ shellMoment * gradMoment)
    (hshell : shellMoment ≤
      C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
    (hgradM : gradMoment ≤
      C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :
    Step5GaugeEndpoint M n h K j e (C1 * C2)
      (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
      (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K) := by
  have hlt : n < n + (h : ℤ) := by
    have hpos : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh
    omega
  have hnorm : vecNorm e ≤ 1 := le_of_eq (vecNorm_eq_one_of_vecNormSq_eq_one he)
  exact step5GaugeEndpoint_closureFamilies_of_legs M n h K j he nmesh
    (step5CrossDefectConst_nonneg d) hgate hintP hsampX hsampS hsampDef
    (fun R hR omega => step5CrossDefect_le_step5Gauge hmesh hsc hnorm hR omega.val _
      (memLp_two_grad_normalizedCubeMeasure_descendant hR
        (alongIncrementPath n h
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
            omega.val).toH1Function))
    hmemOsc
    (fun R _hR => memLp_four_step5Gauge M hlt nmesh R)
    hosc hC1 hgrad0 hprod hshell hgradM

/-! ## `hprod`: the grid/sample Hoelder split

`Closure.ShellProductControl` does the scale bookkeeping once `hprod` is granted
at *some* pair `(shellMoment, gradMoment)`.  The manuscript's own choice is
Hoelder, which fixes the pair to the two grid fourth moments below; the three
lemmas of this section carry that split out, so that `hprod` and `hgrad0` are
proved and the two moment binders that remain are literally `e.km.kn.Lp` and
`e.nablaw.in.L.eight` read on the closure's grid. -/

private theorem holderConjTwoTwo : (2 : ℝ).HolderConjugate 2 := by
  rw [Real.holderConjugate_iff]
  constructor <;> norm_num

private theorem ofRealTwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
  simp [ENNReal.ofReal_ofNat]

/-- The square of a nonnegative `L^4` function is `L^2`. -/
theorem memLp_two_rpow_two_of_memLp_four {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ} (hf : ∀ omega, 0 ≤ f omega)
    (hfm : MemLp f 4 mu) : MemLp (fun omega => f omega ^ (2 : ℝ)) 2 mu := by
  have hbase := hfm.norm_rpow_div (2 : ℝ≥0∞)
  have hdiv : (4 : ℝ≥0∞) / (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  rw [hdiv] at hbase
  refine hbase.ae_eq ?_
  filter_upwards with omega
  simp [Real.norm_of_nonneg (hf omega)]

theorem integrable_rpow_two_of_memLp_four {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {f : Omega → ℝ} (hf : ∀ omega, 0 ≤ f omega)
    (hfm : MemLp f 4 mu) : Integrable (fun omega => f omega ^ (2 : ℝ)) mu :=
  (memLp_two_rpow_two_of_memLp_four hf hfm).integrable (by norm_num)

/-- **Cauchy--Schwarz in the sample at the second moment**, in the fourth-moment
spelling. -/
theorem integral_rpow_two_mul_rpow_two_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {a b : Omega → ℝ}
    (ha : ∀ omega, 0 ≤ a omega) (hb : ∀ omega, 0 ≤ b omega)
    (ham : MemLp a 4 mu) (hbm : MemLp b 4 mu) :
    ∫ omega, a omega ^ (2 : ℝ) * b omega ^ (2 : ℝ) ∂mu ≤
      (∫ omega, a omega ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) *
        (∫ omega, b omega ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) := by
  have hA2 : MemLp (fun omega => a omega ^ (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) mu := by
    rw [ofRealTwo]
    exact memLp_two_rpow_two_of_memLp_four ha ham
  have hB2 : MemLp (fun omega => b omega ^ (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) mu := by
    rw [ofRealTwo]
    exact memLp_two_rpow_two_of_memLp_four hb hbm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg holderConjTwoTwo
    (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (ha omega) _)
    (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hb omega) _) hA2 hB2
  have hsqA : ∀ omega : Omega, (a omega ^ (2 : ℝ)) ^ (2 : ℝ) = a omega ^ (4 : ℝ) := by
    intro omega
    rw [← Real.rpow_mul (ha omega)]
    norm_num
  have hsqB : ∀ omega : Omega, (b omega ^ (2 : ℝ)) ^ (2 : ℝ) = b omega ^ (4 : ℝ) := by
    intro omega
    rw [← Real.rpow_mul (hb omega)]
    norm_num
  simp only [hsqA, hsqB] at hh
  rwa [show (1 : ℝ) / (2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] at hh

/-- Hoelder on the grid at a pair of square roots. -/
theorem cubeFamilyAverage_sqrt_mul_le (I : Finset (TriadicCube d))
    (a b : TriadicCube d → ℝ) (ha : ∀ R ∈ I, 0 ≤ a R) (hb : ∀ R ∈ I, 0 ≤ b R) :
    cubeFamilyAverage I (fun R => a R ^ ((2 : ℝ)⁻¹) * b R ^ ((2 : ℝ)⁻¹)) ≤
      (cubeFamilyAverage I a) ^ ((2 : ℝ)⁻¹) * (cubeFamilyAverage I b) ^ ((2 : ℝ)⁻¹) := by
  classical
  have hAnn : (0 : ℝ) ≤ cubeFamilyAverage I a := cubeFamilyAverage_nonneg ha
  have hBnn : (0 : ℝ) ≤ cubeFamilyAverage I b := cubeFamilyAverage_nonneg hb
  have hLnn : (0 : ℝ) ≤
      cubeFamilyAverage I (fun R => a R ^ ((2 : ℝ)⁻¹) * b R ^ ((2 : ℝ)⁻¹)) :=
    cubeFamilyAverage_nonneg fun R hR =>
      mul_nonneg (Real.rpow_nonneg (ha R hR) _) (Real.rpow_nonneg (hb R hR) _)
  have hcs := sq_cubeFamilyAverage_mul_le I (fun R => a R ^ ((2 : ℝ)⁻¹))
    (fun R => b R ^ ((2 : ℝ)⁻¹))
  have hptA : ∀ R ∈ I, (a R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) = a R := by
    intro R hR
    rw [← Real.rpow_natCast (a R ^ ((2 : ℝ)⁻¹)) 2, ← Real.rpow_mul (ha R hR)]
    norm_num
  have hptB : ∀ R ∈ I, (b R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) = b R := by
    intro R hR
    rw [← Real.rpow_natCast (b R ^ ((2 : ℝ)⁻¹)) 2, ← Real.rpow_mul (hb R hR)]
    norm_num
  have hrwA : cubeFamilyAverage I (fun R => (a R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ))
      = cubeFamilyAverage I a := by
    unfold cubeFamilyAverage
    exact congrArg _ (Finset.sum_congr rfl hptA)
  have hrwB : cubeFamilyAverage I (fun R => (b R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ))
      = cubeFamilyAverage I b := by
    unfold cubeFamilyAverage
    exact congrArg _ (Finset.sum_congr rfl hptB)
  rw [hrwA, hrwB] at hcs
  have hroot := Real.rpow_le_rpow (by positivity) hcs
    (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  rw [← Real.rpow_natCast
      (cubeFamilyAverage I (fun R => a R ^ ((2 : ℝ)⁻¹) * b R ^ ((2 : ℝ)⁻¹))) 2,
    ← Real.rpow_mul hLnn, show (((2 : ℕ) : ℝ) * (2 : ℝ)⁻¹) = 1 by norm_num,
    Real.rpow_one, Real.mul_rpow hAnn hBnn] at hroot
  exact hroot

/-- **`hprod`, proved**: the grid average of the sample mean of `|A_R v_R|^2` is at
most the product of the square roots of the two grid fourth moments, of the
operator norms and of the vector norms.  This is the Hoelder step, at the
closure's grid carrier. -/
theorem descendantsAverage_integral_vecNormSq_matVecMul_le {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega)
    (Q : TriadicCube d) (j : ℕ)
    (A : TriadicCube d → Omega → Mat d) (v : TriadicCube d → Omega → Vec d)
    (hA : ∀ R ∈ descendantsAtDepth Q j,
      MemLp (fun omega => matrixOperatorNorm (A R omega)) 4 mu)
    (hv : ∀ R ∈ descendantsAtDepth Q j,
      MemLp (fun omega => vecNorm (v R omega)) 4 mu) :
    descendantsAverage Q j
        (fun R => ∫ omega, vecNormSq (matVecMul (A R omega) (v R omega)) ∂mu) ≤
      (gridFourthMoment mu (descendantsAtDepth Q j)
            (fun R omega => matrixOperatorNorm (A R omega))) ^ ((2 : ℝ)⁻¹) *
        (gridFourthMoment mu (descendantsAtDepth Q j)
            (fun R omega => vecNorm (v R omega))) ^ ((2 : ℝ)⁻¹) := by
  classical
  set I : Finset (TriadicCube d) := descendantsAtDepth Q j with hI
  have hper : ∀ R ∈ I, ∫ omega, vecNormSq (matVecMul (A R omega) (v R omega)) ∂mu ≤
      (∫ omega, matrixOperatorNorm (A R omega) ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) *
        (∫ omega, vecNorm (v R omega) ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) := by
    intro R hR
    have hAnn : ∀ omega : Omega, (0 : ℝ) ≤ matrixOperatorNorm (A R omega) := fun omega =>
      matrixOperatorNorm_nonneg _
    have hvnn : ∀ omega : Omega, (0 : ℝ) ≤ vecNorm (v R omega) := fun omega =>
      vecNorm_nonneg _
    have hprodInt : Integrable (fun omega => matrixOperatorNorm (A R omega) ^ (2 : ℝ) *
        vecNorm (v R omega) ^ (2 : ℝ)) mu :=
      (memLp_two_rpow_two_of_memLp_four hAnn (hA R hR)).integrable_mul
        (memLp_two_rpow_two_of_memLp_four hvnn (hv R hR))
    have hptwise : ∀ omega : Omega,
        vecNormSq (matVecMul (A R omega) (v R omega)) ≤
          matrixOperatorNorm (A R omega) ^ (2 : ℝ) * vecNorm (v R omega) ^ (2 : ℝ) := by
      intro omega
      have hbase := vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
        (A R omega) (v R omega)
      have hA2 : matrixOperatorNorm (A R omega) ^ (2 : ℕ) =
          matrixOperatorNorm (A R omega) ^ (2 : ℝ) := by
        rw [← Real.rpow_natCast (matrixOperatorNorm (A R omega)) 2]
        norm_num
      have hv2 : vecNormSq (v R omega) = vecNorm (v R omega) ^ (2 : ℝ) := by
        rw [← vecNorm_sq_eq_vecNormSq, ← Real.rpow_natCast (vecNorm (v R omega)) 2]
        norm_num
      rw [← hA2, ← hv2]
      exact hbase
    have hmono : ∫ omega, vecNormSq (matVecMul (A R omega) (v R omega)) ∂mu ≤
        ∫ omega, matrixOperatorNorm (A R omega) ^ (2 : ℝ) *
          vecNorm (v R omega) ^ (2 : ℝ) ∂mu :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun omega => vecNormSq_nonneg _) hprodInt
        (Filter.Eventually.of_forall hptwise)
    exact hmono.trans (integral_rpow_two_mul_rpow_two_le mu hAnn hvnn (hA R hR) (hv R hR))
  have hgrid : cubeFamilyAverage I
      (fun R => ∫ omega, vecNormSq (matVecMul (A R omega) (v R omega)) ∂mu) ≤
      cubeFamilyAverage I (fun R =>
        (∫ omega, matrixOperatorNorm (A R omega) ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) *
          (∫ omega, vecNorm (v R omega) ^ (4 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹)) :=
    cubeFamilyAverage_mono hper
  have hfold := cubeFamilyAverage_sqrt_mul_le I
    (fun R => ∫ omega, matrixOperatorNorm (A R omega) ^ (4 : ℝ) ∂mu)
    (fun R => ∫ omega, vecNorm (v R omega) ^ (4 : ℝ) ∂mu)
    (fun R _ => integral_nonneg fun omega =>
      Real.rpow_nonneg (matrixOperatorNorm_nonneg _) _)
    (fun R _ => integral_nonneg fun omega => Real.rpow_nonneg (vecNorm_nonneg _) _)
  exact le_trans hgrid hfold

/-! ## `hsampS` and `hsampX` from the same two fourth-moment legs -/

/-- **`hsampS`**, from the two fourth-moment legs and the measurability of the
quantity itself. -/
theorem integrable_vecNormSq_matVecMul_of_memLp_four {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega)
    {A : Omega → Mat d} {v : Omega → Vec d}
    (hA : MemLp (fun omega => matrixOperatorNorm (A omega)) 4 mu)
    (hv : MemLp (fun omega => vecNorm (v omega)) 4 mu)
    (hmeas : AEStronglyMeasurable
      (fun omega => vecNormSq (matVecMul (A omega) (v omega))) mu) :
    Integrable (fun omega => vecNormSq (matVecMul (A omega) (v omega))) mu := by
  have hAnn : ∀ omega : Omega, (0 : ℝ) ≤ matrixOperatorNorm (A omega) := fun omega =>
    matrixOperatorNorm_nonneg _
  have hvnn : ∀ omega : Omega, (0 : ℝ) ≤ vecNorm (v omega) := fun omega => vecNorm_nonneg _
  have hprodInt : Integrable (fun omega => matrixOperatorNorm (A omega) ^ (2 : ℝ) *
      vecNorm (v omega) ^ (2 : ℝ)) mu :=
    (memLp_two_rpow_two_of_memLp_four hAnn hA).integrable_mul
      (memLp_two_rpow_two_of_memLp_four hvnn hv)
  refine hprodInt.mono' hmeas ?_
  filter_upwards with omega
  have hbase := vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
    (A omega) (v omega)
  have hA2 : matrixOperatorNorm (A omega) ^ (2 : ℕ) =
      matrixOperatorNorm (A omega) ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast (matrixOperatorNorm (A omega)) 2]
    norm_num
  have hv2 : vecNormSq (v omega) = vecNorm (v omega) ^ (2 : ℝ) := by
    rw [← vecNorm_sq_eq_vecNormSq, ← Real.rpow_natCast (vecNorm (v omega)) 2]
    norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg _), ← hA2, ← hv2]
  exact hbase

/-- **`hsampX`**, from the two fourth-moment legs and the measurability of the
quantity itself. -/
theorem integrable_vecDot_matVecMul_of_memLp_four {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    {e : Vec d} (he : vecNorm e ≤ 1) {A : Omega → Mat d} {v : Omega → Vec d}
    (hA : MemLp (fun omega => matrixOperatorNorm (A omega)) 4 mu)
    (hv : MemLp (fun omega => vecNorm (v omega)) 4 mu)
    (hmeas : AEStronglyMeasurable
      (fun omega => vecDot e (matVecMul (A omega) (v omega))) mu) :
    Integrable (fun omega => vecDot e (matVecMul (A omega) (v omega))) mu := by
  have hAnn : ∀ omega : Omega, (0 : ℝ) ≤ matrixOperatorNorm (A omega) := fun omega =>
    matrixOperatorNorm_nonneg _
  have hvnn : ∀ omega : Omega, (0 : ℝ) ≤ vecNorm (v omega) := fun omega => vecNorm_nonneg _
  have hbdd : Integrable (fun omega =>
      (matrixOperatorNorm (A omega) ^ (2 : ℝ) + vecNorm (v omega) ^ (2 : ℝ)) / 2) mu :=
    ((integrable_rpow_two_of_memLp_four hAnn hA).add
      (integrable_rpow_two_of_memLp_four hvnn hv)).div_const 2
  refine hbdd.mono' hmeas ?_
  filter_upwards with omega
  have h1 : |vecDot e (matVecMul (A omega) (v omega))| ≤
      vecNorm e * vecNorm (matVecMul (A omega) (v omega)) :=
    abs_vecDot_le_vecNorm_mul_vecNorm _ _
  have h2 : vecNorm (matVecMul (A omega) (v omega)) ≤
      matrixOperatorNorm (A omega) * vecNorm (v omega) :=
    vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _
  have h3 : vecNorm e * vecNorm (matVecMul (A omega) (v omega)) ≤
      matrixOperatorNorm (A omega) * vecNorm (v omega) := by
    calc vecNorm e * vecNorm (matVecMul (A omega) (v omega))
        ≤ 1 * vecNorm (matVecMul (A omega) (v omega)) :=
          mul_le_mul_of_nonneg_right he (vecNorm_nonneg _)
      _ = vecNorm (matVecMul (A omega) (v omega)) := one_mul _
      _ ≤ matrixOperatorNorm (A omega) * vecNorm (v omega) := h2
  have hAM : matrixOperatorNorm (A omega) ^ (2 : ℝ) =
      matrixOperatorNorm (A omega) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (matrixOperatorNorm (A omega)) 2]
    norm_num
  have hvM : vecNorm (v omega) ^ (2 : ℝ) = vecNorm (v omega) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (vecNorm (v omega)) 2]
    norm_num
  rw [Real.norm_eq_abs, hAM, hvM]
  nlinarith [h1, h3, sq_nonneg (matrixOperatorNorm (A omega) - vecNorm (v omega))]

/-! ## The endpoint at the two grid fourth moments -/

/-- **`Closure.Step5GaugeEndpoint` at the closure families, with the Hoelder split
carried out.**

Relative to `step5GaugeEndpoint_closureFamilies_of_gaugeLegs` this discharges
four more legs --- `hprod`, `hgrad0`, `hsampX` and `hsampS` --- from the two
grid fourth-moment memberships `hAmem`, `hvmem` and two measurability side
conditions, and restates `hshell` and `hgradM` at the *explicit* grid fourth
moments the manuscript's Hoelder step produces:

* `hshell` is `e.km.kn.Lp` read as `(avsum_ ||(k_{n+h} - k_n)_R||^4)^{1/2} <= h
  3^{2 cgamma (n+h)}`;
* `hgradM` is `e.nablaw.in.L.eight` read as `(avsum_ |(grad w_D)_R|^4)^{1/2} <=
  shom_n^{-2} h 3^{2 cgamma (n+h)}`.

The residual basket is therefore `hintP`, `hsampDef`, `hmeasX`, `hmeasS`,
`hAmem`, `hvmem`, `hmemOsc`, `hosc`, `hshell`, `hgradM`. -/
theorem step5GaugeEndpoint_closureFamilies_of_momentLegs [NeZero d] (M : ABKModel d)
    (n : ℤ) (h : ℕ) (K j : ℕ) {e : Vec d} (he : vecNormSq e = 1) {nmesh : ℤ}
    (hmesh : (K : ℤ) - (j : ℤ) = nmesh) (hsc : nmesh ≤ n) (hh : 0 < h) {C1 C2 : ℝ}
    (hgate : step5CrossDefectConst d * M.gamma ^ (15 : ℕ) ≤ 2)
    (hintP : ∀ omega : ShellSeq d, IntegrableOn
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n (n + (h : ℤ)) x)
        ((alongIncrementPath n h
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
            omega).toH1Function.grad x)))
      (cubeSet (originCube d (K : ℤ))) volume)
    (hmeasX : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      AEStronglyMeasurable
          (fun omega : CutoffSample d =>
            vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hmeasS : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      AEStronglyMeasurable
          (fun omega : CutoffSample d =>
            vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
        (cubeAverageVec R
          (fun x => (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x))))
          (cutoffSampleLaw M).toMeasure)
    (hsampDef : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      Integrable
          (fun omega : CutoffSample d =>
            step5CrossDefect R omega.val n (n + (h : ℤ)) e
          (fun x => (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x))
          (cutoffSampleLaw M).toMeasure)
    (hAmem : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp (fun omega : CutoffSample d =>
        matrixOperatorNorm (freshShellCubeAverage R omega.val n (n + (h : ℤ)))) 4
        (cutoffSampleLaw M).toMeasure)
    (hvmem : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp (fun omega : CutoffSample d =>
        vecNorm (cubeAverageVec R
          (fun x => (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
              omega.val).toH1Function.grad x))) 4 (cutoffSampleLaw M).toMeasure)
    (hmemOsc : ∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
      MemLp
          (fun omega : CutoffSample d =>
            meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
            omega.val).toH1Function.grad x) R) 4
          (cutoffSampleLaw M).toMeasure)
    (hosc : (gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (descendantsAtDepth (originCube d (K : ℤ)) j)
      (fun R omega => meshOscillationCell nmesh
        (fun x => (alongIncrementPath n h
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
            omega.val).toH1Function.grad x) R)) +
      ((Annealed.sigmaBar M n : ℝ))⁻¹ *
      gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
        (descendantsAtDepth (originCube d (K : ℤ)) j)
        (fun (R : TriadicCube d) (omega : CutoffSample d) =>
          (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
            shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R) omega.val) ≤
      M.gamma ^ (15 : ℕ))
    (hC1 : 0 ≤ C1)
    (hshell : (gridFourthMoment (cutoffSampleLaw M).toMeasure
          (descendantsAtDepth (originCube d (K : ℤ)) j)
          (fun (R : TriadicCube d) (omega : CutoffSample d) =>
            matrixOperatorNorm (freshShellCubeAverage R omega.val n (n + (h : ℤ)))))
        ^ ((2 : ℝ)⁻¹) ≤
      C1 * (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
    (hgradM : (gridFourthMoment (cutoffSampleLaw M).toMeasure
          (descendantsAtDepth (originCube d (K : ℤ)) j)
          (fun (R : TriadicCube d) (omega : CutoffSample d) =>
            vecNorm (cubeAverageVec R
              (fun x => (alongIncrementPath n h
                (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
                  omega.val).toH1Function.grad x))))
        ^ ((2 : ℝ)⁻¹) ≤
      C2 * (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ * (h : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :
    Step5GaugeEndpoint M n h K j e (C1 * C2)
      (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
      (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K) := by
  have hnorm : vecNorm e ≤ 1 := le_of_eq (vecNorm_eq_one_of_vecNormSq_eq_one he)
  exact step5GaugeEndpoint_closureFamilies_of_gaugeLegs M n h K j he hmesh hsc hh hgate
    hintP
    (fun R hR => integrable_vecDot_matVecMul_of_memLp_four
      (cutoffSampleLaw M).toMeasure hnorm (hAmem R hR) (hvmem R hR) (hmeasX R hR))
    (fun R hR => integrable_vecNormSq_matVecMul_of_memLp_four
      (cutoffSampleLaw M).toMeasure (hAmem R hR) (hvmem R hR) (hmeasS R hR))
    hsampDef hmemOsc hosc hC1
    (Real.rpow_nonneg (gridFourthMoment_nonneg _ _ _) _)
    (descendantsAverage_integral_vecNormSq_matVecMul_le (cutoffSampleLaw M).toMeasure
      (originCube d (K : ℤ)) j _ _ hAmem hvmem)
    hshell hgradM

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
