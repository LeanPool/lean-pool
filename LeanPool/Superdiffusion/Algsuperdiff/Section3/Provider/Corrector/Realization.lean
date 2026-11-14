/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.StationaryProjection
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure
public import LeanPool.HighContrastHomogenization.Support.Sobolev.L2Ambient
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Realization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the measurable spatial realization of a stationary random field

`Algsuperdiff/Probability/StationaryProjection.lean` builds the stationary
Hilbert layer over an abstract carrier `Ω` carrying an `AddAction (Vec d) Ω`
and a translation-invariant measure `μ`.  That layer is purely abstract: the
docstring of `Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd`
records that only *fixed-shift* measurability is available there, "not joint
measurability of the translation parameter and the field".

Every displayed quantity of `l.approximation.stationary.by.local` and
`l.corrector.limit` lives instead on the *space* side: `‖·‖_{L²(cu_K)}`,
`⨍_{cu_K}`, `H¹₀(cu_K)`.  Passing between the two sides requires the
realization map

`realize X ω : x ↦ X (x +ᵥ ω)`,

which is what this file provides, together with the measurability facts that
make it usable under Fubini.  This is item of the corrector-limit design.

Joint measurability of `(x, ω) ↦ x +ᵥ ω` is genuinely extra data over the
abstract layer; it is taken here as Mathlib's existing class
`MeasurableVAdd₂ (Vec d) Ω`, so that no new class and no new global instance is
introduced.  For `L²`-classes the realization is representative dependent
(changing `X` on a `μ`-null set can change `realize X ω` at every point), so
every statement below is made for an honest `StronglyMeasurable` representative
and transported to `Lp` along a.e. equality at the point of use.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary (measurePreserving_const_vadd)

noncomputable section

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

/-- The spatial realization of an abstract random field `X` at the sample `ω`:
the field `x ↦ X (x +ᵥ ω)` on `ℝᵈ`.  This is the map denoted `X(x + ω)` in the
ergodic-theory literature and implicitly used throughout Section 3 whenever a
stationary field is integrated over a cube. -/
def realize {E : Type*} (X : Ω → E) (ω : Ω) (x : Vec d) : E := X (x +ᵥ ω)

theorem realize_apply {E : Type*} (X : Ω → E) (ω : Ω) (x : Vec d) :
    realize X ω x = X (x +ᵥ ω) := rfl

/-- The restricted Lebesgue measure of a triadic cube is finite. -/
theorem isFiniteMeasure_volume_restrict_cubeSet (Q : TriadicCube d) :
    IsFiniteMeasure (volume.restrict (cubeSet Q)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact volume_cubeSet_lt_top Q

section Measurability

variable [MeasurableSpace Ω] [MeasurableVAdd₂ (Vec d) Ω]

/-- Joint measurability of the translation action, in the order `(space, sample)`. -/
theorem measurable_vadd_pair :
    Measurable fun p : Vec d × Ω => p.1 +ᵥ p.2 :=
  measurable_vadd

/-- Joint measurability of the translation action, in the order `(sample, space)`.
This is the order in which the product measure `μ.prod (volume.restrict …)` is
formed below. -/
theorem measurable_vadd_pair_swap :
    Measurable fun p : Ω × Vec d => p.2 +ᵥ p.1 :=
  measurable_vadd_pair.comp measurable_swap

/-- The spatial translation at a fixed sample is measurable. -/
theorem measurable_vadd_const_sample (ω : Ω) :
    Measurable fun x : Vec d => x +ᵥ ω :=
  measurable_vadd_pair.comp (measurable_id.prodMk measurable_const)

/-- **, per-sample form.**  For a measurable representative the spatial realization
is measurable in the space variable, for *every* sample. -/
theorem stronglyMeasurable_realize {E : Type*} [TopologicalSpace E]
    {X : Ω → E} (hX : StronglyMeasurable X) (ω : Ω) :
    StronglyMeasurable (realize (d := d) X ω) :=
  hX.comp_measurable (measurable_vadd_const_sample ω)

/-- **, joint form.**  For a measurable representative the spatial realization is
jointly measurable in the sample and the space variable.  This is the fact the
abstract stationary layer does not supply, and the one that makes the Fubini
argument of `RealizationTransfer.lean` legitimate. -/
theorem stronglyMeasurable_uncurry_realize {E : Type*} [TopologicalSpace E]
    {X : Ω → E} (hX : StronglyMeasurable X) :
    StronglyMeasurable fun p : Ω × Vec d => realize X p.1 p.2 :=
  hX.comp_measurable measurable_vadd_pair_swap

/-- **, Fubini-ready form.**  The pointwise pairing of two realizations is jointly
measurable. -/
theorem stronglyMeasurable_uncurry_vecDot_realize
    {X Y : Ω → HilbertVec d} (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y) :
    StronglyMeasurable fun p : Ω × Vec d =>
      vecDot (realize X p.1 p.2).toVec (realize Y p.1 p.2).toVec := by
  have h : StronglyMeasurable fun p : Ω × Vec d =>
      inner ℝ (realize X p.1 p.2) (realize Y p.1 p.2) :=
    (stronglyMeasurable_uncurry_realize hX).inner (stronglyMeasurable_uncurry_realize hY)
  simpa using h

end Measurability

section Transfer

variable [MeasurableSpace Ω] {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

/-- Real-shift Koopman transfer of expectations: a stationary expectation is
unchanged by translating the sample.  This is the real-parameter analogue of
CoarseGraining's integer-shift
`Homogenization.IsStationaryR.integral_comp_translateReg`, obtained from
`Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd`. -/
theorem integral_comp_const_vadd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Ω → E) (x : Vec d) :
    ∫ ω, g (x +ᵥ ω) ∂μ = ∫ ω, g ω ∂μ :=
  (measurePreserving_const_vadd (μ := μ) x).integral_comp
    (measurableEmbedding_const_vadd x) g

/-- Stationary translation preserves integrability. -/
theorem integrable_comp_const_vadd {E : Type*} [NormedAddCommGroup E]
    {g : Ω → E} (hg : Integrable g μ) (x : Vec d) :
    Integrable (fun ω => g (x +ᵥ ω)) μ :=
  ((measurePreserving_const_vadd (μ := μ) x).integrable_comp_emb
    (measurableEmbedding_const_vadd x)).2 hg

end Transfer

section Pairing

variable [MeasurableSpace Ω] {μ : Measure Ω}

omit [AddAction (Vec d) Ω] in
/-- The pointwise pairing of two square-integrable stationary fields is
integrable on the sample space. -/
theorem integrable_vecDot {X Y : Ω → HilbertVec d}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => vecDot (X ω).toVec (Y ω).toVec) μ := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hX.toLp X) (hY.toLp Y)).congr ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hx hy
  rw [hx, hy, HilbertVec.inner_def]

end Pairing

section Product

variable [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **, product integrability.**  The pointwise pairing of two realizations is
integrable on the product of the sample space with a triadic cube.  This is the
hypothesis of the Fubini exchange used, and it also produces the per-sample
square integrability of a realization on a cube. -/
theorem integrable_prod_vecDot_realize (Q : TriadicCube d)
    {X Y : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hYm : StronglyMeasurable Y)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable
      (fun p : Ω × Vec d => vecDot (realize X p.1 p.2).toVec (realize Y p.1 p.2).toVec)
      (μ.prod (volume.restrict (cubeSet Q))) := by
  have := isFiniteMeasure_volume_restrict_cubeSet (d := d) Q
  have hpair : Integrable (fun ω => vecDot (X ω).toVec (Y ω).toVec) μ :=
    integrable_vecDot hX hY
  refine (integrable_prod_iff'
    (stronglyMeasurable_uncurry_vecDot_realize hXm hYm).aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x => ?_
    exact integrable_comp_const_vadd hpair x
  · have hconst : ∀ x : Vec d,
        (∫ ω, ‖vecDot (realize X ω x).toVec (realize Y ω x).toVec‖ ∂μ)
          = ∫ ω, ‖vecDot (X ω).toVec (Y ω).toVec‖ ∂μ := fun x =>
      integral_comp_const_vadd (fun ω => ‖vecDot (X ω).toVec (Y ω).toVec‖) x
    refine (integrable_congr ?_).2
      (integrable_const (∫ ω, ‖vecDot (X ω).toVec (Y ω).toVec‖ ∂μ))
    filter_upwards with x
    exact hconst x

/-- **, per-sample square integrability.**  For almost every sample the spatial
realization of a stationary `L²` field is square integrable on any triadic
cube, i.e. it is an honest element of CoarseGraining's `L²(Q; ℝᵈ)` scale. -/
theorem ae_memHilbertVectorL2_realize (Q : TriadicCube d)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ, MemHilbertVectorL2 (cubeSet Q) (realize (d := d) X ω) := by
  have := isFiniteMeasure_volume_restrict_cubeSet (d := d) Q
  filter_upwards [(integrable_prod_vecDot_realize Q hXm hXm hX hX).prod_right_ae] with ω hω
  refine (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_realize hXm ω).aestronglyMeasurable).2 (hω.congr ?_)
  filter_upwards with x
  exact (HilbertVec.inner_def _ _).symm.trans (real_inner_self_eq_norm_sq _)

end Product

end

end Algsuperdiff.Section3.Provider.Corrector
