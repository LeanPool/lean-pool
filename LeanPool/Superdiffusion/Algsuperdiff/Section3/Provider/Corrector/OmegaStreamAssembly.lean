/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.OmegaStream
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ValuePathTransport
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# OmegaStreamAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: assembling the `Ω`-level approximate stream at the fresh shell

`Algsuperdiff/Section3/Provider/Corrector/OmegaStream.lean` builds the kernel
stream `S_{im} = A_{g_m}X_i − A_{g_i}X_m` and proves that its row divergence is,
at every point of space, the realization of the `Ω`-level field
`kernelStreamDiv`, which for a stationary solenoidal `X` equals `A_{κ₁}X − A_{κ₂}X`
almost surely.  This file supplies the carrier-general `ε`-form of that
construction, its two-scale instantiation, the small-scale error leg and the
carrier instances the legs need.

## What is assembled

* `exists_kernelStream_integral_normSq_le` — the carrier-general `ε`-form: with
  `∫‖A_{κ₁}X − X‖² ≤ e₁` and `∫‖A_{κ₂}X‖² ≤ e₂` the stream reproduces `X` up to
  `2e₁ + 2e₂` in squared `L²(Ω)` norm.

* `exists_twoScaleStream_integral_normSq_le` — the same at the two product
  densities of `Algsuperdiff/Section3/Provider/Corrector/MollifierScaling.lean`,
  whose divergence kernel is the explicit telescoping field of
  `Algsuperdiff/Section3/Provider/Corrector/DivergenceKernel.lean`.

* `exists_radius_integral_normSq_mollify_productDensity_sub_le` — the small-scale
  leg, the approximate-identity estimate of
  `Algsuperdiff/Section3/Provider/Corrector/MollifierConvergence.lean` transported
  from `Mollifier.ofRadius` to `Mollifier.ofProduct`.

The matching large-scale leg and the shell instantiation are not here.  They
are downstream, in
`Algsuperdiff/Section3/Provider/Corrector/ShellSumCorrectorLimit.lean`:
`exists_scale_integral_normSq_mollify_productDensity_shellSumFlux_le` is the
decorrelation bound at the product density, built on
`Algsuperdiff/Section3/Provider/Corrector/ValuePathTransport.lean`, and
`exists_shellSumStream` puts the two legs together --- for every tolerance
`ε > 0` an antisymmetric stationary square-integrable stream with smooth
realizations whose row divergence reproduces the shell-sum flux `shellSumFlux`
to within `ε` in squared `L²(Ω)` norm.

## The carrier instances

The approximate-identity leg needs the strong continuity of the Koopman orbit
(`Algsuperdiff.Probability.Stationary.continuous_koopman_orbit`), which is
stated under `[ Ω] [BorelSpace Ω] [ContinuousVAdd (Vec d) Ω]
[IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]`.  On the
continuous-path carrier `C(Vec d, Mat d)` all of these are available once `Mat
d` is known to be second countable with a countably generated uniformity; those
two facts are recorded below as `secondCountableTopology_mat` and
`isCountablyGenerated_uniformity_mat`, each a transport of the corresponding
`Pi` instance through the type synonym `Matrix (Fin d) (Fin d) ℝ = Fin d → Fin
d → ℝ`.  They upgrade `C(Vec d, Mat d)` to a Polish space, and Mathlib's
`MeasureTheory.Measure.InnerRegularCompactLTTop_of_polishSpace` then supplies
the last instance for *every* measure on that carrier.

## What is *not* proved

The divergence identity delivered is the **approximate** one.  The consumer
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_stationaryStream`
(`Algsuperdiff/Section3/Provider/Corrector/SolenoidalApproximation.lean`) asks for
the *exact* hypothesis

`hstreamDiv : ∀ᵐ ω, ∀ x, streamDivergence (streamRealization S ω) x = (realize j ω x).toVec`,

and the output below satisfies that equality with an auxiliary field `D` in place
of `j`, together with `∫‖D − j‖² ≤ ε`.  The output therefore does **not** plug
into that theorem verbatim; see the note on
`exists_kernelStream_integral_normSq_le` for the exact restatement the consumer
would need.

**Disclosure.**  Nothing in this file realizes any source node.  It discharges the
two error legs of the approximate representation and instantiates it at the fresh
shell; it does not prove part (ii) of `l.approximation.stationary.by.local`, and
it claims no node status.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}


/-! ### The approximate stream -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **The `Ω`-level antisymmetric stream, in the approximate form.**

For a stationary square-integrable field `X` in the stationary solenoidal
subspace and any family `g` of smooth compactly supported scalar fields whose
divergence is `κ₁ − κ₂`, the kernel stream `S_{im} = A_{g_m}X_i − A_{g_i}X_m` is a
stationary square-integrable antisymmetric field with smooth realizations whose
row divergence is, at every point of space, the realization of the `Ω`-level
field `D`, and `D = A_{κ₁}X − A_{κ₂}X` almost surely.

The first five conclusions are exactly the hypotheses `hSm`, `hS`,
`hstreamSmooth`, `hstreamAnti` of
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_stationaryStream`; the sixth
is its `hstreamDiv` **with `D` in place of `X`**. -/
theorem exists_kernelStream {g : Fin d → (Vec d → ℝ)}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m)) (hgc : ∀ m, HasCompactSupport (g m))
    {κ₁ κ₂ : Vec d → ℝ} (hκ₁c : Continuous κ₁) (hκ₁i : Integrable κ₁ volume)
    (hκ₂c : Continuous κ₂) (hκ₂i : Integrable κ₂ volume)
    (hdiv : ∀ y, ∑ m : Fin d, kernelDeriv (g m) m y = κ₁ y - κ₂ y)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hmem : hX.toLp X ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    ∃ S : Ω → (Fin d → HilbertVec d), ∃ D : Ω → HilbertVec d,
      StronglyMeasurable S ∧ MemLp S 2 μ ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d, ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i m)) ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d,
          streamRealization S ω m i = -streamRealization S ω i m) ∧
        (∀ᵐ ω ∂μ, ∀ x : Vec d,
          streamDivergence (streamRealization S ω) x = (realize D ω x).toVec) ∧
        StronglyMeasurable D ∧ MemLp D 2 μ ∧
        (∀ᵐ ω ∂μ, D ω = mollify κ₁ X ω - mollify κ₂ X ω) := by
  classical
  set ν : Vec d → ℝ := fun y => κ₁ y - κ₂ y with hνdef
  have hνc : Continuous ν := hκ₁c.sub hκ₂c
  have hνi : Integrable ν volume := hκ₁i.sub hκ₂i
  have hν : ∀ y : Vec d, ν y = ∑ m : Fin d, kernelDeriv (g m) m y := fun y => (hdiv y).symm
  have hgcont : ∀ m : Fin d, Continuous (g m) := fun m => (hgs m).continuous
  have hgint : ∀ m : Fin d, Integrable (g m) volume := fun m =>
    (hgs m).continuous.integrable_of_hasCompactSupport (hgc m)
  have hloc : ∀ᵐ ω ∂μ, ∀ i : Fin d,
      LocallyIntegrable (realize (d := d) (coordField X i) ω) volume :=
    ae_all_iff.2 fun i => ae_locallyIntegrable_realize (μ := μ)
      (stronglyMeasurable_coordField hXm i) (memLp_coordField hXm hX i)
  refine ⟨kernelStream g X, kernelStreamDiv g ν X,
    stronglyMeasurable_kernelStream hgcont hXm,
    memLp_two_kernelStream hgcont hgint hXm hX, ?_, ?_, ?_,
    stronglyMeasurable_kernelStreamDiv hgs hνc hXm,
    memLp_two_kernelStreamDiv hgs hgc hνc hνi hXm hX, ?_⟩
  · filter_upwards [hloc] with ω hω i m
    exact contDiff_streamRealization_kernelStream hgs hgc hω i m
  · filter_upwards with ω i m
    exact streamRealization_kernelStream_neg g X ω i m
  · filter_upwards [hloc] with ω hω x
    exact streamDivergence_kernelStream hgs hgc hν hω x
  · exact kernelStreamDiv_ae_eq hgs hgc hκ₁c hκ₁i hκ₂c hκ₂i (fun _ => rfl) hXm hX hmem

/-- **The `Ω`-level `ε`-approximate antisymmetric stream.**

Same construction, with the two error legs entered numerically: if the smoothing
by `κ₁` moves `X` by at most `e₁` and the smoothing by `κ₂` has energy at most
`e₂`, both in squared `L²(Ω)` norm, then the row divergence of the stream
reproduces `X` up to `2e₁ + 2e₂` in squared `L²(Ω)` norm.

**This is the approximate form, not the exact one.**  What
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_stationaryStream` consumes is
`hstreamDiv : ∀ᵐ ω, ∀ x, streamDivergence (streamRealization S ω) x = (realize j ω x).toVec`,
an *equality*.  The conclusion below gives that equality with `D` in place of
`j`, together with `∫ ‖D − j‖² ≤ 2e₁ + 2e₂`.  To accept this output the consumer
would have to be restated with `hstreamDiv` replaced by the pair

`(∀ᵐ ω, ∀ x, streamDivergence (streamRealization S ω) x = (realize D ω x).toVec)`
and `(∫ ω, ‖D ω − j ω‖² ∂μ ≤ e)`,

and its conclusion weakened by the resulting `L²(cu_K)` error, which is
`(cubeVolume Q)⁻¹ ∫_{cu_K} ‖realize (D − j) ω‖²` and integrates in `ω` to exactly
`e` by translation invariance.  Nothing else in that proof uses `hstreamDiv`. -/
theorem exists_kernelStream_integral_normSq_le {g : Fin d → (Vec d → ℝ)}
    (hgs : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m)) (hgc : ∀ m, HasCompactSupport (g m))
    {κ₁ κ₂ : Vec d → ℝ} (hκ₁c : Continuous κ₁) (hκ₁i : Integrable κ₁ volume)
    (hκ₂c : Continuous κ₂) (hκ₂i : Integrable κ₂ volume)
    (hdiv : ∀ y, ∑ m : Fin d, kernelDeriv (g m) m y = κ₁ y - κ₂ y)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hmem : hX.toLp X ∈ stationarySolenoidalSubspace (μ := μ) (d := d))
    {e₁ e₂ : ℝ} (h₁ : ∫ ω, ‖mollify κ₁ X ω - X ω‖ ^ 2 ∂μ ≤ e₁)
    (h₂ : ∫ ω, ‖mollify κ₂ X ω‖ ^ 2 ∂μ ≤ e₂) :
    ∃ S : Ω → (Fin d → HilbertVec d), ∃ D : Ω → HilbertVec d,
      StronglyMeasurable S ∧ MemLp S 2 μ ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d, ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i m)) ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d,
          streamRealization S ω m i = -streamRealization S ω i m) ∧
        (∀ᵐ ω ∂μ, ∀ x : Vec d,
          streamDivergence (streamRealization S ω) x = (realize D ω x).toVec) ∧
        StronglyMeasurable D ∧ MemLp D 2 μ ∧
        ∫ ω, ‖D ω - X ω‖ ^ 2 ∂μ ≤ 2 * e₁ + 2 * e₂ := by
  classical
  obtain ⟨S, D, hSm, hS, hsmooth, hanti, hdivS, hDm, hD, hDeq⟩ :=
    exists_kernelStream hgs hgc hκ₁c hκ₁i hκ₂c hκ₂i hdiv hXm hX hmem
  refine ⟨S, D, hSm, hS, hsmooth, hanti, hdivS, hDm, hD, ?_⟩
  have hA₁ : MemLp (mollify (Ω := Ω) κ₁ X) 2 μ := memLp_two_mollify hκ₁c hκ₁i hXm hX
  have hA₂ : MemLp (mollify (Ω := Ω) κ₂ X) 2 μ := memLp_two_mollify hκ₂c hκ₂i hXm hX
  have hint₁ : Integrable (fun ω => ‖mollify (Ω := Ω) κ₁ X ω - X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hA₁.sub hX).aestronglyMeasurable).1 (hA₁.sub hX)
  have hint₂ : Integrable (fun ω => ‖mollify (Ω := Ω) κ₂ X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hA₂.aestronglyMeasurable).1 hA₂
  have hintD : Integrable (fun ω => ‖D ω - X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hD.sub hX).aestronglyMeasurable).1 (hD.sub hX)
  have hdom : Integrable (fun ω => 2 * ‖mollify (Ω := Ω) κ₁ X ω - X ω‖ ^ 2
      + 2 * ‖mollify (Ω := Ω) κ₂ X ω‖ ^ 2) μ :=
    (hint₁.const_mul 2).add (hint₂.const_mul 2)
  have hpt : ∀ᵐ ω ∂μ, ‖D ω - X ω‖ ^ 2
      ≤ 2 * ‖mollify (Ω := Ω) κ₁ X ω - X ω‖ ^ 2 + 2 * ‖mollify (Ω := Ω) κ₂ X ω‖ ^ 2 := by
    filter_upwards [hDeq] with ω hω
    have hsplit : D ω - X ω = (mollify κ₁ X ω - X ω) - mollify κ₂ X ω := by
      rw [hω]
      abel
    have htri : ‖D ω - X ω‖ ≤ ‖mollify κ₁ X ω - X ω‖ + ‖mollify κ₂ X ω‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    nlinarith [htri, norm_nonneg (D ω - X ω), norm_nonneg (mollify κ₁ X ω - X ω),
      norm_nonneg (mollify (Ω := Ω) κ₂ X ω),
      sq_nonneg (‖mollify (Ω := Ω) κ₁ X ω - X ω‖ - ‖mollify (Ω := Ω) κ₂ X ω‖)]
  have hmono : ∫ ω, ‖D ω - X ω‖ ^ 2 ∂μ
      ≤ ∫ ω, (2 * ‖mollify (Ω := Ω) κ₁ X ω - X ω‖ ^ 2
        + 2 * ‖mollify (Ω := Ω) κ₂ X ω‖ ^ 2) ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hdom hpt
  have hval : ∫ ω, (2 * ‖mollify (Ω := Ω) κ₁ X ω - X ω‖ ^ 2
      + 2 * ‖mollify (Ω := Ω) κ₂ X ω‖ ^ 2) ∂μ
      = 2 * (∫ ω, ‖mollify (Ω := Ω) κ₁ X ω - X ω‖ ^ 2 ∂μ)
        + 2 * ∫ ω, ‖mollify (Ω := Ω) κ₂ X ω‖ ^ 2 ∂μ := by
    rw [integral_add (hint₁.const_mul 2) (hint₂.const_mul 2), integral_const_mul,
      integral_const_mul]
  rw [hval] at hmono
  linarith [hmono, h₁, h₂]

end Main

/-! ### The two-scale instance -/

section TwoScale

variable {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- The two-scale kernel family of
`Algsuperdiff/Section3/Provider/Corrector/DivergenceKernel.lean`, whose
divergence is the difference of the two product densities. -/
def twoScaleKernelFamily {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Fin d → (Vec d → ℝ) :=
  fun m => fun x => divKernel (scaledBump hr) (scaledBump hs) (r + s) x m

theorem contDiff_twoScaleKernelFamily {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (m : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (twoScaleKernelFamily (d := d) hr hs m) :=
  contDiff_divKernel_scaledBump_apply hr hs m

theorem hasCompactSupport_twoScaleKernelFamily {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (m : Fin d) : HasCompactSupport (twoScaleKernelFamily (d := d) hr hs m) :=
  hasCompactSupport_divKernel_scaledBump_apply hr hs m

/-- **The divergence of the two-scale kernel family.** -/
theorem kernelDeriv_sum_twoScaleKernelFamily {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (y : Vec d) :
    ∑ m : Fin d, kernelDeriv (twoScaleKernelFamily (d := d) hr hs m) m y
      = productDensity d hr y - productDensity d hs y :=
  coordDeriv_sum_divKernel_scaledBump hr hs y

/-- **The two-scale `ε`-approximate antisymmetric stream.**

The concrete instance of `exists_kernelStream_integral_normSq_le` at the two
product densities of scales `r` and `s`: the smoothing at the small scale `r` is
the approximate identity, the smoothing at the large scale `s` is the term killed
by decorrelation. -/
theorem exists_twoScaleStream_integral_normSq_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hmem : hX.toLp X ∈ stationarySolenoidalSubspace (μ := μ) (d := d))
    {e₁ e₂ : ℝ}
    (h₁ : ∫ ω, ‖mollify (productDensity d hr) X ω - X ω‖ ^ 2 ∂μ ≤ e₁)
    (h₂ : ∫ ω, ‖mollify (productDensity d hs) X ω‖ ^ 2 ∂μ ≤ e₂) :
    ∃ S : Ω → (Fin d → HilbertVec d), ∃ D : Ω → HilbertVec d,
      StronglyMeasurable S ∧ MemLp S 2 μ ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d, ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i m)) ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d,
          streamRealization S ω m i = -streamRealization S ω i m) ∧
        (∀ᵐ ω ∂μ, ∀ x : Vec d,
          streamDivergence (streamRealization S ω) x = (realize D ω x).toVec) ∧
        StronglyMeasurable D ∧ MemLp D 2 μ ∧
        ∫ ω, ‖D ω - X ω‖ ^ 2 ∂μ ≤ 2 * e₁ + 2 * e₂ :=
  exists_kernelStream_integral_normSq_le (contDiff_twoScaleKernelFamily hr hs)
    (hasCompactSupport_twoScaleKernelFamily hr hs)
    (continuous_productDensity d hr) (integrable_productDensity d hr)
    (continuous_productDensity d hs) (integrable_productDensity d hs)
    (kernelDeriv_sum_twoScaleKernelFamily hr hs) hXm hX hmem h₁ h₂

end TwoScale

/-! ### The small-scale leg -/

section ApproximateIdentity

variable {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable [TopologicalSpace Ω] [R1Space Ω] [BorelSpace Ω] [ContinuousVAdd (Vec d) Ω]
variable [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- **The approximate-identity leg at the product density.**  This is
`exists_radius_integral_normSq_mollify_sub_le` of
`Algsuperdiff/Section3/Provider/Corrector/MollifierConvergence.lean` with
`Mollifier.ofRadius` replaced by `Mollifier.ofProduct`, whose density is the
tensor product used by the two-scale divergence kernel. -/
theorem exists_radius_integral_normSq_mollify_productDensity_sub_le
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    {t : ℝ} (ht : 0 < t) :
    ∃ r : ℝ, ∃ hr : 0 < r,
      ∫ ω, ‖mollify (productDensity d hr) X ω - X ω‖ ^ 2 ∂μ ≤ t := by
  have hcont : ContinuousAt (fun y : Vec d => ∫ ω, ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 ∂μ) 0 :=
    (continuous_integral_normSq_translate (μ := μ) hX).continuousAt
  have hzero : (∫ ω, ‖X ((-(0 : Vec d)) +ᵥ ω) - X ω‖ ^ 2 ∂μ) = 0 := by simp
  rw [Metric.continuousAt_iff] at hcont
  rw [hzero] at hcont
  obtain ⟨r, hr, hball⟩ := hcont t ht
  refine ⟨r, hr, ?_⟩
  refine integral_normSq_mollify_sub_le (μ := μ) (Mollifier.ofProduct d hr) hXm hX ?_
  intro y hy
  have hy' : dist y (0 : Vec d) < r := by
    rw [dist_eq_norm, sub_zero]
    exact hy
  have h := hball hy'
  rw [Real.dist_eq, sub_zero] at h
  exact (le_abs_self _).trans h.le

end ApproximateIdentity

/-! ### The carrier instances of the continuous-path space -/

/-- `Mat d` is second countable: the type synonym `Matrix (Fin d) (Fin d) ℝ`
carries the `Pi` topology. -/
instance secondCountableTopology_mat (d : ℕ) : SecondCountableTopology (Mat d) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))

/-- The uniformity of `Mat d` is countably generated. -/
instance isCountablyGenerated_uniformity_mat (d : ℕ) :
    Filter.IsCountablyGenerated (uniformity (Mat d)) :=
  inferInstanceAs (Filter.IsCountablyGenerated (uniformity (Fin d → Fin d → ℝ)))

section FreshShell

end FreshShell

end

end Algsuperdiff.Section3.Provider.Corrector
