/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.NeumannUpperBound

/-!
# SolenoidalApproximationEps

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: part (ii) of the local-approximation lemma for an approximate stream

The cutoff core of part (ii) of `l.approximation.stationary.by.local` is proved
in `Algsuperdiff/Section3/Provider/Corrector/SolenoidalApproximation.lean` for a
field whose *exact* row divergence is the stream divergence.  The Ω-level
streams that the repository can actually build represent the flux only up to an
`L²(Ω)` error: they come with an auxiliary stationary square-integrable field
`D` whose realization is the stream divergence at every point, together with a
tolerance `E[|D − j|²] ≤ ε`.

This file restates the cutoff core in that approximate form.  Nothing of
`SolenoidalApproximation.lean` is re-proved: the competitor family is the same
`localStreamApprox`, instantiated at `D` — where the divergence identity holds
exactly, so its admissibility `IsSolenoidalZeroNormalTraceOn` is literally
`isSolenoidalZeroNormalTraceOn_localStreamApprox` — and the only new content is
the absorption of the `L²(Ω)` gap between `D` and the true flux `j`.

## Why the gap is `K`-independent

The error against the true flux splits as

`j_{K,L} − j = (j_{K,L} − D) + (D − j)`,

and by the stationary transfer
(`Algsuperdiff/Section3/Provider/Corrector/RealizationTransfer.lean`,
`integral_cubeAverage_normSq_realize`)

`E[ ‖realize (D − j)‖²_{L²(cu_K)} ] = E[ |D − j|² ]`

for **every** cube `K`: the second term is a constant of `K` and therefore
passes through the `limsup` untouched.  The resulting estimate is

`limsup_K E[ ‖j_{K,L} − j‖²_{L²(cu_K)} ] ≤ 2 d 3^{−L} E[|D|²] + 2 E[|D − j|²]`.

## The concrete-witness discipline

CoarseGraining's `IsSolenoidalZeroNormalTraceOn U g` is orthogonality to
`∇H¹(U)` and carries no square integrability, so an existential witness of it
gives no per-sample `L²` control and `∫|·|²` can silently be the Bochner junk
value `0`.  Exactly as in
`Algsuperdiff/Section3/Provider/Corrector/NeumannUpperBound.lean`, the consumer
below therefore uses the *concrete* family `localStreamApprox Q L S D` and the
per-sample membership `ae_memLp_localStreamApprox_sub_of_approximateStream`,
not the existential
`exists_isSolenoidalZeroNormalTraceOn_limsup_le_of_approximateStream`; the
existential is recorded because it is the printed form of part (ii), not
because anything downstream consumes it.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### An elementary two-term split -/

section Elementary

/-- The crude triangle split `‖a − c‖² ≤ 2‖a − b‖² + 2‖b − c‖²`. -/
theorem normSq_sub_le_two_mul_add_two_mul {F : Type*} [NormedAddCommGroup F] (a b c : F) :
    ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have h : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    simpa [dist_eq_norm] using dist_triangle a b c
  nlinarith [norm_nonneg (a - c), norm_nonneg (a - b), norm_nonneg (b - c),
    sq_nonneg (‖a - b‖ - ‖b - c‖)]

end Elementary

/-! ### The competitor of an approximate stream -/

section Measurability

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable [MeasurableVAdd₂ (Vec d) Ω]

/-- The error of the competitor built from `D` against the true flux `j` is
jointly strongly measurable. -/
theorem stronglyMeasurable_uncurry_localStreamApprox_sub_of_approximateStream
    (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {D j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hDm : StronglyMeasurable D)
    (hjm : StronglyMeasurable j) :
    StronglyMeasurable fun z : Ω × Vec d =>
      HilbertVec.ofVec (localStreamApprox Q L S D z.1 z.2) - realize j z.1 z.2 := by
  have hrw : (fun z : Ω × Vec d =>
      HilbertVec.ofVec (localStreamApprox Q L S D z.1 z.2) - realize j z.1 z.2)
      = fun z : Ω × Vec d =>
        (HilbertVec.ofVec (localStreamApprox Q L S D z.1 z.2) - realize D z.1 z.2)
          + (realize D z.1 z.2 - realize j z.1 z.2) := by
    funext z
    abel
  rw [hrw]
  exact (stronglyMeasurable_uncurry_localStreamApprox_sub Q L hSm hDm).add
    ((stronglyMeasurable_uncurry_realize hDm).sub (stronglyMeasurable_uncurry_realize hjm))

end Measurability

section Sample

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

/-- **The two-term split of the approximate error at a fixed sample.**  On the
cube, the error of the competitor built from `D` against the true flux `j` costs
at most twice the exact error plus twice the realized `D − j` energy. -/
theorem setIntegral_normSq_localStreamApprox_sub_le_of_approximateStream
    (Q : TriadicCube d) (L : ℕ) (S : Ω → (Fin d → HilbertVec d)) (D j : Ω → HilbertVec d)
    (ω : Ω)
    (hexact : MemLp (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x)
      - realize D ω x) 2 (volume.restrict (cubeSet Q)))
    (hgap : MemLp (fun x => realize D ω x - realize j ω x) 2
      (volume.restrict (cubeSet Q))) :
    (∫ x in cubeSet Q, ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x)
        - realize j ω x‖ ^ 2)
      ≤ 2 * (∫ x in cubeSet Q, ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x)
            - realize D ω x‖ ^ 2)
        + 2 * ∫ x in cubeSet Q, ‖realize D ω x - realize j ω x‖ ^ 2 := by
  have hexact' : IntegrableOn (fun x => ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x)
      - realize D ω x‖ ^ 2) (cubeSet Q) :=
    (memLp_two_iff_integrable_sq_norm hexact.aestronglyMeasurable).1 hexact
  have hgap' : IntegrableOn (fun x => ‖realize D ω x - realize j ω x‖ ^ 2) (cubeSet Q) :=
    (memLp_two_iff_integrable_sq_norm hgap.aestronglyMeasurable).1 hgap
  have hmono : (∫ x in cubeSet Q, ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x)
        - realize j ω x‖ ^ 2)
      ≤ ∫ x in cubeSet Q, (2 * ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x)
          - realize D ω x‖ ^ 2 + 2 * ‖realize D ω x - realize j ω x‖ ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      ((hexact'.const_mul 2).add (hgap'.const_mul 2)) ?_
    filter_upwards with x
    exact normSq_sub_le_two_mul_add_two_mul
      (HilbertVec.ofVec (localStreamApprox Q L S D ω x)) (realize D ω x) (realize j ω x)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add (hexact'.const_mul 2) (hgap'.const_mul 2), integral_const_mul,
    integral_const_mul]

end Sample

/-! ### The expected error of the approximate competitor -/

section Estimate

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- For almost every sample the error of the approximate competitor against the
true flux is square integrable on the cube.  This is the per-sample `L²`
control that CoarseGraining's `IsSolenoidalZeroNormalTraceOn` does not carry. -/
theorem ae_memLp_localStreamApprox_sub_of_approximateStream (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {D j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 μ)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ) :
    ∀ᵐ ω ∂μ, MemLp (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x)
      - realize j ω x) 2 (volume.restrict (cubeSet Q)) := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  filter_upwards [ae_memLp_localStreamApprox_sub (μ := μ) Q L hSm hS hDm hD,
    ae_memLp_two_realize (μ := μ) hQfin (hDm.sub hjm) (hD.sub hj)] with ω h1 h2
  have h2' : MemLp (fun x => realize D ω x - realize j ω x) 2
      (volume.restrict (cubeSet Q)) := h2
  have hrw : (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize j ω x)
      = fun x => (HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize D ω x)
        + (realize D ω x - realize j ω x) := by
    funext x
    abel
  rw [hrw]
  exact h1.add h2'

/-- Almost-sure square integrability of the realized gap `D − j` on the cube. -/
theorem ae_memLp_realize_sub (Q : TriadicCube d) {D j : Ω → HilbertVec d}
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ) :
    ∀ᵐ ω ∂μ, MemLp (fun x => realize D ω x - realize j ω x) 2
      (volume.restrict (cubeSet Q)) := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  filter_upwards [ae_memLp_two_realize (μ := μ) hQfin (hDm.sub hjm) (hD.sub hj)] with ω h
  exact h

/-- The unnormalized exact error is integrable in the sample.  This is the
internal companion of `integrable_cubeLpNorm_localStreamApprox_sub`, recovered
from it by the normalization identity. -/
theorem integrable_setIntegral_normSq_localStreamApprox_sub (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {D : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 μ)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 μ) :
    Integrable (fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize D ω x‖ ^ 2) μ := by
  refine ((integrable_cubeLpNorm_localStreamApprox_sub (μ := μ) Q L hSm hS hDm hD).const_mul
    (cubeVolume Q)).congr ?_
  filter_upwards [ae_memLp_localStreamApprox_sub (μ := μ) Q L hSm hS hDm hD] with ω hω
  have hne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  rw [cubeLpNorm_two_rpow_eq_cubeAverage_norm_sq hω, cubeAverage]
  field_simp

/-- The squared normalized error of the approximate competitor is integrable in
the sample. -/
theorem integrable_cubeLpNorm_localStreamApprox_sub_of_approximateStream
    (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {D j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 μ)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ) :
    Integrable (fun ω => cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x)
        - realize j ω x) ^ (2 : ℝ)) μ := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hmeas : StronglyMeasurable fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize j ω x‖ ^ 2 :=
    ((stronglyMeasurable_uncurry_localStreamApprox_sub_of_approximateStream Q L
      hSm hDm hjm).norm.pow 2).integral_prod_right'
  have hdom : Integrable (fun ω =>
      2 * (∫ x in cubeSet Q, ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x)
          - realize D ω x‖ ^ 2)
        + 2 * ∫ x in cubeSet Q, ‖realize D ω x - realize j ω x‖ ^ 2) μ := by
    refine ((integrable_setIntegral_normSq_localStreamApprox_sub (μ := μ) Q L
      hSm hS hDm hD).const_mul 2).add ?_
    exact ((integrable_setIntegral_normSq_realize (μ := μ) hQfin (hDm.sub hjm)
      (hD.sub hj)).const_mul 2)
  have hI : Integrable (fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize j ω x‖ ^ 2) μ := by
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_memLp_localStreamApprox_sub (μ := μ) Q L hSm hS hDm hD,
      ae_memLp_realize_sub (μ := μ) Q hDm hD hjm hj] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => by positivity)]
    exact setIntegral_normSq_localStreamApprox_sub_le_of_approximateStream Q L S D j ω h1 h2
  refine ((hI.const_mul (cubeVolume Q)⁻¹).congr ?_)
  filter_upwards [ae_memLp_localStreamApprox_sub_of_approximateStream (μ := μ) Q L
    hSm hS hDm hD hjm hj] with ω hω
  rw [cubeLpNorm_two_rpow_eq_cubeAverage_norm_sq hω, cubeAverage]

/-- **The expected normalized error of the approximate competitor at a fixed
cube.**  The exact estimate of `integral_cubeLpNorm_localStreamApprox_sub_le`
at `D` plus the `K`-independent `L²(Ω)` gap `E[|D − j|²]`, the latter by the
stationary transfer. -/
theorem integral_cubeLpNorm_localStreamApprox_sub_le_of_approximateStream
    (Q : TriadicCube d) (L : ℕ)
    {S : Ω → (Fin d → HilbertVec d)} {D j : Ω → HilbertVec d}
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 μ)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ) :
    ∫ ω, cubeLpNorm Q 2
        (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x)
          - realize j ω x) ^ (2 : ℝ) ∂μ
      ≤ 2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (∫ ω, ‖D ω‖ ^ 2 ∂μ)
            + 2 * ((d : ℝ) * gradBound Q L) ^ 2 * ∫ ω, ‖S ω‖ ^ 2 ∂μ)
        + 2 * ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hvolpos := cubeVolume_pos Q
  have hinv : (0 : ℝ) < (cubeVolume Q)⁻¹ := inv_pos.2 hvolpos
  -- The exact half, in the unnormalized form.
  have hexactInt : Integrable (fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize D ω x‖ ^ 2) μ :=
    integrable_setIntegral_normSq_localStreamApprox_sub (μ := μ) Q L hSm hS hDm hD
  have hgapInt : Integrable (fun ω => ∫ x in cubeSet Q,
      ‖realize D ω x - realize j ω x‖ ^ 2) μ :=
    integrable_setIntegral_normSq_realize (μ := μ) hQfin (hDm.sub hjm) (hD.sub hj)
  -- The `K`-independent gap, by the stationary transfer.
  have hgapVal : (∫ ω, (∫ x in cubeSet Q, ‖realize D ω x - realize j ω x‖ ^ 2) ∂μ)
      = cubeVolume Q * ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ := by
    have h := integral_setIntegral_normSq_realize (μ := μ) (S := cubeSet Q) hQfin
      (hDm.sub hjm) (hD.sub hj)
    rw [volume_cubeSet_toReal] at h
    exact h
  -- The unnormalized comparison.
  have hmono : (∫ ω, (∫ x in cubeSet Q, ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x)
        - realize j ω x‖ ^ 2) ∂μ)
      ≤ ∫ ω, (2 * (∫ x in cubeSet Q, ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x)
          - realize D ω x‖ ^ 2)
        + 2 * ∫ x in cubeSet Q, ‖realize D ω x - realize j ω x‖ ^ 2) ∂μ := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω => integral_nonneg fun x => by positivity)
      ((hexactInt.const_mul 2).add (hgapInt.const_mul 2)) ?_
    filter_upwards [ae_memLp_localStreamApprox_sub (μ := μ) Q L hSm hS hDm hD,
      ae_memLp_realize_sub (μ := μ) Q hDm hD hjm hj] with ω h1 h2
    exact setIntegral_normSq_localStreamApprox_sub_le_of_approximateStream Q L S D j ω h1 h2
  rw [integral_add (hexactInt.const_mul 2) (hgapInt.const_mul 2), integral_const_mul,
    integral_const_mul, hgapVal] at hmono
  -- Renormalize and insert the exact estimate.
  have hrepr : ∀ᵐ ω ∂μ, cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize j ω x) ^ (2 : ℝ)
      = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q,
          ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize j ω x‖ ^ 2 := by
    filter_upwards [ae_memLp_localStreamApprox_sub_of_approximateStream (μ := μ) Q L
      hSm hS hDm hD hjm hj] with ω hω
    rw [cubeLpNorm_two_rpow_eq_cubeAverage_norm_sq hω, cubeAverage]
  rw [integral_congr_ae hrepr, integral_const_mul]
  have hexactVal : (cubeVolume Q)⁻¹ * ∫ ω, (∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize D ω x‖ ^ 2) ∂μ
      ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (∫ ω, ‖D ω‖ ^ 2 ∂μ)
        + 2 * ((d : ℝ) * gradBound Q L) ^ 2 * ∫ ω, ‖S ω‖ ^ 2 ∂μ := by
    have hbase := integral_cubeLpNorm_localStreamApprox_sub_le (μ := μ) Q L hSm hS hDm hD
    have heq : (∫ ω, cubeLpNorm Q 2 (fun x =>
          HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize D ω x) ^ (2 : ℝ) ∂μ)
        = (cubeVolume Q)⁻¹ * ∫ ω, (∫ x in cubeSet Q,
            ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize D ω x‖ ^ 2) ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_memLp_localStreamApprox_sub (μ := μ) Q L hSm hS hDm hD] with ω hω
      rw [cubeLpNorm_two_rpow_eq_cubeAverage_norm_sq hω, cubeAverage]
    rwa [heq] at hbase
  have hscaled := mul_le_mul_of_nonneg_left hmono hinv.le
  have hdist : (cubeVolume Q)⁻¹ * (2 * (∫ ω, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize D ω x‖ ^ 2) ∂μ)
      + 2 * (cubeVolume Q * ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ))
      = 2 * ((cubeVolume Q)⁻¹ * ∫ ω, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize D ω x‖ ^ 2) ∂μ)
        + 2 * ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ := by
    have hne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
    field_simp
  rw [hdist] at hscaled
  linarith [hscaled, hexactVal]

end Estimate

section Main

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

end Main

/-! ### The Neumann upper bound for a field with approximate streams -/

section Neumann

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **`e.upper.bound.neumann.corrector.limit`** in the `ε`-form, for a flux
possessing approximate streams at every tolerance.

`hstream` is the only stream input, and it is an *approximate* representation:
for every tolerance `η > 0` there is a stationary square-integrable
antisymmetric stream `S` with smooth realizations whose row divergence is the
realization of a stationary square-integrable `D` with `E[|D − j|²] ≤ η`.  Its
shape is copied verbatim from
`Algsuperdiff/Section3/Provider/Corrector/OmegaStreamAssembly.lean`
(`exists_freshShellStream`).

`hNint` is the sample-integrability of the Neumann cube energies; it makes the
left-hand side the expectation of the display rather than a junk value.

The tolerance is chosen after the Young parameter and before the localization
scale, so nothing is circular: `η` depends only on `ε` and `E[|∇w|²]`, `L`
depends on `η` and `E[|j|²]`, and the cutoff-gradient term is killed by taking
`K` large at the fixed `L`. -/
theorem eventually_integral_cubeAverage_neumann_le_integral_normSq_of_approximateStream
    {f p j : Ω → HilbertVec d}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ)
    (hjdef : ∀ ω : Ω, j ω = p ω + f ω)
    (hstream : ∀ η : ℝ, 0 < η →
      ∃ S : Ω → (Fin d → HilbertVec d), ∃ D : Ω → HilbertVec d,
        StronglyMeasurable S ∧ MemLp S 2 μ ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d, ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i m)) ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d,
          streamRealization S ω m i = -streamRealization S ω i m) ∧
        (∀ᵐ ω ∂μ, ∀ x : Vec d,
          streamDivergence (streamRealization S ω) x = (realize D ω x).toVec) ∧
        StronglyMeasurable D ∧ MemLp D 2 μ ∧
        ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ ≤ η)
    {Nfam : ℕ → Ω → (Vec d → Vec d)}
    (hNpot : ∀ K : ℕ, ∀ᵐ ω ∂μ,
      IsPotentialOn (openCubeSet (originCube d (K : ℤ))) (Nfam K ω))
    (hNsol : ∀ K : ℕ, ∀ᵐ ω ∂μ,
      IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d (K : ℤ)))
        fun x => Nfam K ω x + (realize f ω x).toVec)
    (hNint : ∀ K : ℕ, Integrable (fun ω => cubeAverage (originCube d (K : ℤ))
      fun x => vecDot (Nfam K ω x) (Nfam K ω x)) μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in Filter.atTop,
      (∫ ω, cubeAverage (originCube d (K : ℤ))
          (fun x => vecDot (Nfam K ω x) (Nfam K ω x)) ∂μ)
        ≤ (∫ ω, ‖p ω‖ ^ 2 ∂μ) + ε := by
  classical
  set M : ℝ := ∫ ω, ‖p ω‖ ^ 2 ∂μ with hMdef
  set Jm : ℝ := ∫ ω, ‖j ω‖ ^ 2 ∂μ with hJmdef
  have hM0 : 0 ≤ M := integral_nonneg fun ω => by positivity
  have hJ0 : 0 ≤ Jm := integral_nonneg fun ω => by positivity
  -- The Young parameter, small enough that `δ E[|∇w|²] ≤ ε/2`.
  set δ : ℝ := min 1 (ε / (2 * (M + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδM : δ * M ≤ ε / 2 := by
    have hδle : δ ≤ ε / (2 * (M + 1)) := min_le_right _ _
    have hstep : δ * M ≤ ε / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hδle hM0
    have hfin : ε / (2 * (M + 1)) * M ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      nlinarith [hε.le, hM0]
    linarith
  have hcoef : (0 : ℝ) < 1 + δ⁻¹ := by positivity
  -- The stream tolerance, chosen from `ε` and `δ` alone.
  set η : ℝ := min 1 (ε / (8 * (1 + δ⁻¹))) with hηdef
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : (1 + δ⁻¹) * (2 * η) ≤ ε / 4 := by
    have hle : η ≤ ε / (8 * (1 + δ⁻¹)) := min_le_right _ _
    have hstep : (1 + δ⁻¹) * (2 * η) ≤ (1 + δ⁻¹) * (2 * (ε / (8 * (1 + δ⁻¹)))) := by
      have := mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 2)
      exact mul_le_mul_of_nonneg_left this hcoef.le
    have hval : (1 + δ⁻¹) * (2 * (ε / (8 * (1 + δ⁻¹)))) = ε / 4 := by
      field_simp
      ring
    linarith
  obtain ⟨S, D, hSm, hS, hsmooth, hanti, hdiv, hDm, hD, hgap⟩ := hstream η hη0
  -- The auxiliary field has energy bounded by a quantity independent of `L`.
  have hDsq : Integrable (fun ω => ‖D ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).1 hD
  have hgapsq : Integrable (fun ω => ‖D ω - j ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hD.sub hj).aestronglyMeasurable).1 (hD.sub hj)
  have hjsq : Integrable (fun ω => ‖j ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hj.aestronglyMeasurable).1 hj
  have hDbd : (∫ ω, ‖D ω‖ ^ 2 ∂μ) ≤ 2 + 2 * Jm := by
    have hmono : (∫ ω, ‖D ω‖ ^ 2 ∂μ)
        ≤ ∫ ω, (2 * ‖D ω - j ω‖ ^ 2 + 2 * ‖j ω‖ ^ 2) ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
        ((hgapsq.const_mul 2).add (hjsq.const_mul 2)) ?_
      filter_upwards with ω
      have h := normSq_sub_le_two_mul_add_two_mul (D ω) (j ω) (0 : HilbertVec d)
      simpa using h
    rw [integral_add (hgapsq.const_mul 2) (hjsq.const_mul 2), integral_const_mul,
      integral_const_mul] at hmono
    have h2 : (2 : ℝ) * ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ ≤ 2 := by linarith
    linarith [hmono, h2]
  have hDbd0 : (0 : ℝ) ≤ 2 + 2 * Jm := by linarith
  -- The localization scale.
  obtain ⟨L, hL⟩ := exists_three_zpow_neg_mul_le (d : ℝ) (2 + 2 * Jm)
    (ε / (16 * (1 + δ⁻¹))) (Nat.cast_nonneg d) hDbd0 (by positivity)
  have hcoefpow : (0 : ℝ) ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) :=
    mul_nonneg (Nat.cast_nonneg d) (zpow_nonneg (by norm_num) _)
  have hstrip : (1 + δ⁻¹) * (2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ))
      * ∫ ω, ‖D ω‖ ^ 2 ∂μ)) ≤ ε / 8 := by
    have hin : (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * ∫ ω, ‖D ω‖ ^ 2 ∂μ
        ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (2 + 2 * Jm) :=
      mul_le_mul_of_nonneg_left hDbd hcoefpow
    have hstep : (1 + δ⁻¹) * (2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ))
        * ∫ ω, ‖D ω‖ ^ 2 ∂μ))
        ≤ (1 + δ⁻¹) * (2 * (ε / (16 * (1 + δ⁻¹)))) := by
      have h1 : (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * ∫ ω, ‖D ω‖ ^ 2 ∂μ
          ≤ ε / (16 * (1 + δ⁻¹)) := hin.trans hL
      have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2)
      exact mul_le_mul_of_nonneg_left h2 hcoef.le
    have hval : (1 + δ⁻¹) * (2 * (ε / (16 * (1 + δ⁻¹)))) = ε / 8 := by
      field_simp
      ring
    linarith
  -- The cutoff-gradient term vanishes as the cube grows, at the fixed scale `L`.
  have hinv : Filter.Tendsto (fun K : ℕ => ((3 : ℝ) ^ K)⁻¹) Filter.atTop (nhds 0) := by
    simpa [inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
        (by norm_num : (3 : ℝ)⁻¹ < 1)
  have hgrad0 : Filter.Tendsto (fun K : ℕ => gradBound (originCube d (K : ℤ)) L)
      Filter.atTop (nhds 0) := by
    simp only [gradBound_originCube]
    simpa using hinv.const_mul
      ((d : ℝ) * quantitativeCubeCutoffGradientConst d * 8 * (3 : ℝ) ^ L)
  set G : ℕ → ℝ := fun K => (1 + δ⁻¹) * (2 * (2 * ((d : ℝ)
      * gradBound (originCube d (K : ℤ)) L) ^ 2 * ∫ ω, ‖S ω‖ ^ 2 ∂μ)) with hGdef
  have hG0 : Filter.Tendsto G Filter.atTop (nhds 0) := by
    have := ((((((hgrad0.const_mul (d : ℝ)).pow 2).const_mul (2 : ℝ)).mul_const
      (∫ ω, ‖S ω‖ ^ 2 ∂μ)).const_mul (2 : ℝ)).const_mul (1 + δ⁻¹))
    simpa [hGdef] using this
  filter_upwards [Filter.Tendsto.eventually_lt_const
    (show (0 : ℝ) < ε / 8 by linarith) hG0] with K hK
  -- The competitor family of part (ii) at the cube `cu_K` and the scale `L`.
  have hJsolK : ∀ᵐ ω ∂μ,
      IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d (K : ℤ)))
        (localStreamApprox (originCube d (K : ℤ)) L S D ω) := by
    filter_upwards [hsmooth, hanti, hdiv] with ω h1 h2 h3
    exact isSolenoidalZeroNormalTraceOn_localStreamApprox _ L h1 h2 h3
  have hmain := integral_cubeAverage_vecDot_self_le (μ := μ) (originCube d (K : ℤ)) hδ0
    hfm hf hpm hp hjdef (hNpot K) (hNsol K) hJsolK
    (ae_memLp_localStreamApprox_sub_of_approximateStream (μ := μ)
      (originCube d (K : ℤ)) L hSm hS hDm hD hjm hj)
    (hNint K)
    (integrable_cubeLpNorm_localStreamApprox_sub_of_approximateStream (μ := μ)
      (originCube d (K : ℤ)) L hSm hS hDm hD hjm hj)
  have hbound := integral_cubeLpNorm_localStreamApprox_sub_le_of_approximateStream (μ := μ)
    (originCube d (K : ℤ)) L hSm hS hDm hD hjm hj
  have hgapscaled : (1 + δ⁻¹) * (2 * ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ) ≤ ε / 4 := by
    have h1 : (2 : ℝ) * ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ ≤ 2 * η :=
      mul_le_mul_of_nonneg_left hgap (by norm_num)
    exact (mul_le_mul_of_nonneg_left h1 hcoef.le).trans hηε
  have hscaled := mul_le_mul_of_nonneg_left hbound hcoef.le
  have hexpand : (1 + δ⁻¹) * (2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (∫ ω, ‖D ω‖ ^ 2 ∂μ)
        + 2 * ((d : ℝ) * gradBound (originCube d (K : ℤ)) L) ^ 2 * ∫ ω, ‖S ω‖ ^ 2 ∂μ)
      + 2 * ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ)
      = (1 + δ⁻¹) * (2 * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * ∫ ω, ‖D ω‖ ^ 2 ∂μ))
        + G K + (1 + δ⁻¹) * (2 * ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ) := by
    simp only [hGdef]
    ring
  rw [hexpand] at hscaled
  linarith [hmain, hscaled, hstrip, hgapscaled, hδM, hK]

end Neumann

end

end Algsuperdiff.Section3.Provider.Corrector
