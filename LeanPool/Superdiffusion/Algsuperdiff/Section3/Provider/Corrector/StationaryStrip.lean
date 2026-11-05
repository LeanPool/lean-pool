/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.BoundaryStrip
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.Realization
public import LeanPool.HighContrastHomogenization.Support.Geometry.BoundaryLayer
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.Cube

/-!
# StationaryStrip

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: stationary transfer on arbitrary sets and the boundary-strip fraction

The proof of part (i) of `l.approximation.stationary.by.local` needs two
ingredients beyond the cube-average transfer of
`Algsuperdiff/Section3/Provider/Corrector/RealizationTransfer.lean`:

* the stationary transfer over an *arbitrary* measurable set of finite volume,
  `E[∫_S g(x + ω) dx] = |S| E[g]`, which is what turns the first error term
  `E[‖(η_{K,L} - 1) p‖²_{L²(cu_K)}]` into `(|Σ_{K,L}|/|cu_K|) E[|p|²]`; and
* the geometric half of `e.boundary.strip.volume`: the set where
  CoarseGraining's cutoff `Homogenization.QuantitativeCubeCutoff Q ρ₁ ρ₂` is
  allowed to differ from `1` has volume fraction at most `1 - ρ₁ ^ d ≤ d (1 -
  ρ₁)`.

The scalar Bernoulli core of the second item is
`Algsuperdiff/Section3/Provider/Corrector/BoundaryStrip.lean`; here it is
combined with CoarseGraining's exact boundary-layer volume
`Homogenization.volume_cubeBoundaryLayer_toReal_of_nonneg_le_half`.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

section Transfer

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- Joint integrability of `(ω, x) ↦ g (x +ᵥ ω)` over the product of the sample
space with a set of finite volume.  This is the Fubini hypothesis behind the
set-indexed stationary transfer. -/
theorem integrable_prod_comp_vadd {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {g : Ω → ℝ} (hgm : StronglyMeasurable g) (hg : Integrable g μ) :
    Integrable (fun q : Ω × Vec d => g (q.2 +ᵥ q.1)) (μ.prod (volume.restrict S)) := by
  have : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hSfin
  have hjm : StronglyMeasurable fun q : Ω × Vec d => g (q.2 +ᵥ q.1) :=
    hgm.comp_measurable measurable_vadd_pair_swap
  refine (integrable_prod_iff' hjm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => integrable_comp_const_vadd hg x
  · refine (integrable_congr ?_).2 (integrable_const (∫ ω, ‖g ω‖ ∂μ))
    filter_upwards with x
    exact integral_comp_const_vadd (fun ω => ‖g ω‖) x

/-- **Set-indexed stationary transfer.**  For a stationary integrable observable
`g` and a measurable set `S` of finite volume, `E[∫_S g(x + ω) dx] = |S| ·
E[g]`.  Taking `S` a triadic cube recovers; taking `S` the boundary strip of
the paper's cutoff is what produces `e.boundary.strip.volume`. -/
theorem integral_setIntegral_comp_vadd {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {g : Ω → ℝ} (hgm : StronglyMeasurable g) (hg : Integrable g μ) :
    ∫ ω, (∫ x in S, g (x +ᵥ ω)) ∂μ = (volume S).toReal * ∫ ω, g ω ∂μ := by
  have : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hSfin
  calc
    ∫ ω, (∫ x in S, g (x +ᵥ ω)) ∂μ
        = ∫ x, (∫ ω, g (x +ᵥ ω) ∂μ) ∂volume.restrict S :=
          integral_integral_swap (integrable_prod_comp_vadd hSfin hgm hg)
    _ = ∫ _x, (∫ ω, g ω ∂μ) ∂volume.restrict S := by
          simp only [integral_comp_const_vadd]
    _ = (volume S).toReal * ∫ ω, g ω ∂μ := by
          rw [integral_const, Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul]

/-- Integrability in the sample of the set integral of a stationary
observable. -/
theorem integrable_setIntegral_comp_vadd {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {g : Ω → ℝ} (hgm : StronglyMeasurable g) (hg : Integrable g μ) :
    Integrable (fun ω => ∫ x in S, g (x +ᵥ ω)) μ :=
  (integrable_prod_comp_vadd hSfin hgm hg).integral_prod_left

/-- The set-indexed transfer for the squared norm of the realization of a
square-integrable stationary field:
`E[∫_S |(realize X) (x)|² dx] = |S| E[|X|²]`. -/
theorem integral_setIntegral_normSq_realize {E : Type*} [NormedAddCommGroup E]
    {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∫ ω, (∫ x in S, ‖realize X ω x‖ ^ 2) ∂μ = (volume S).toReal * ∫ ω, ‖X ω‖ ^ 2 ∂μ :=
  integral_setIntegral_comp_vadd (μ := μ) hSfin (hXm.norm.pow 2)
    ((memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX)

/-- Integrability in the sample of the set integral of the squared norm of a
realization. -/
theorem integrable_setIntegral_normSq_realize {E : Type*} [NormedAddCommGroup E]
    {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    Integrable (fun ω => ∫ x in S, ‖realize X ω x‖ ^ 2) μ :=
  integrable_setIntegral_comp_vadd (μ := μ) hSfin (hXm.norm.pow 2)
    ((memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX)

/-- **Per-sample square integrability on an arbitrary set.**  For almost every
sample the spatial realization of a stationary `L²` field is square integrable
on any measurable set of finite volume.  This is the general-set companion of
`Algsuperdiff.Section3.Provider.Corrector.ae_memHilbertVectorL2_realize`. -/
theorem ae_memLp_two_realize {E : Type*} [NormedAddCommGroup E]
    {S : Set (Vec d)} (hSfin : volume S ≠ ⊤)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ, MemLp (realize (d := d) X ω) 2 (volume.restrict S) := by
  have hprod := integrable_prod_comp_vadd (μ := μ) hSfin (hXm.norm.pow 2)
    ((memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX)
  filter_upwards [hprod.prod_right_ae] with ω hω
  exact (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_realize hXm ω).aestronglyMeasurable).2 hω

end Transfer

section Geometry

variable {d : ℕ}

/-- A concentric closed subcube of ratio `ρ` contains the inward shrinking of
the half-open cube by the absolute amount `(1 - ρ) / 2`. -/
theorem cubeShrunkSet_subset_scaledClosedCubeSet (Q : TriadicCube d) (ρ : ℝ) :
    cubeShrunkSet Q ((1 - ρ) / 2) ⊆ scaledClosedCubeSet Q ρ := by
  intro x hx i
  have hxi := hx i
  have hs : (0 : ℝ) < cubeScaleFactor Q :=
    zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  rw [abs_le]
  constructor
  · have := hxi.1
    have hrad : cubeRadius Q = (1 / 2 : ℝ) * cubeScaleFactor Q := rfl
    have hc : cubeCenter Q i = (Q.index i : ℝ) * cubeScaleFactor Q := rfl
    rw [hrad, hc]
    nlinarith [this]
  · have := hxi.2
    have hrad : cubeRadius Q = (1 / 2 : ℝ) * cubeScaleFactor Q := rfl
    have hc : cubeCenter Q i = (Q.index i : ℝ) * cubeScaleFactor Q := rfl
    rw [hrad, hc]
    nlinarith [this]

/-- The set on which a concentric cutoff of inner ratio `ρ` may differ from `1`
inside a triadic cube is contained in the boundary layer of thickness
`(1 - ρ) / 2`. -/
theorem cubeSet_diff_scaledClosedCubeSet_subset (Q : TriadicCube d) (ρ : ℝ) :
    cubeSet Q \ scaledClosedCubeSet Q ρ ⊆ cubeBoundaryLayer Q ((1 - ρ) / 2) :=
  fun _ hx =>
    ⟨hx.1, fun hmem => hx.2 (cubeShrunkSet_subset_scaledClosedCubeSet Q ρ hmem)⟩

/-- A concentric closed subcube of ratio `ρ < 1` sits inside the open cube;
this is what makes the cutoff product compactly supported in `cu_K`. -/
theorem scaledClosedCubeSet_subset_openCubeSet (Q : TriadicCube d) {ρ : ℝ}
    (hρ1 : ρ < 1) :
    scaledClosedCubeSet Q ρ ⊆ openCubeSet Q := by
  intro x hx i
  have hs : (0 : ℝ) < cubeScaleFactor Q :=
    zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hxi := abs_le.1 (hx i)
  have hrad : cubeRadius Q = (1 / 2 : ℝ) * cubeScaleFactor Q := rfl
  have hc : cubeCenter Q i = (Q.index i : ℝ) * cubeScaleFactor Q := rfl
  rw [hrad, hc] at hxi
  constructor
  · nlinarith [hxi.1]
  · nlinarith [hxi.2]

/-- **`e.boundary.strip.volume`, geometric half.**  The volume of the set where a
concentric cutoff of inner ratio `ρ ∈ [0, 1]` may differ from `1` inside a
triadic cube is at most `(1 - ρ ^ d)` times the volume of the cube. -/
theorem volume_cubeSet_diff_scaledClosedCubeSet_toReal_le (Q : TriadicCube d) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (volume (cubeSet Q \ scaledClosedCubeSet Q ρ)).toReal ≤ (1 - ρ ^ d) * cubeVolume Q := by
  have ht0 : (0 : ℝ) ≤ (1 - ρ) / 2 := by linarith
  have hthalf : (1 - ρ) / 2 ≤ (1 / 2 : ℝ) := by linarith
  have hlayer := volume_cubeBoundaryLayer_toReal_of_nonneg_le_half Q ht0 hthalf
  have hsub : volume (cubeSet Q \ scaledClosedCubeSet Q ρ)
      ≤ volume (cubeBoundaryLayer Q ((1 - ρ) / 2)) :=
    measure_mono (cubeSet_diff_scaledClosedCubeSet_subset Q ρ)
  have hfin : volume (cubeBoundaryLayer Q ((1 - ρ) / 2)) ≠ ⊤ :=
    measure_ne_top_of_subset (cubeBoundaryLayer_subset_cubeSet Q _) (volume_cubeSet_lt_top Q).ne
  have hmono := ENNReal.toReal_mono hfin hsub
  refine hmono.trans ?_
  rw [hlayer]
  have hrw : (1 - 2 * ((1 - ρ) / 2)) = ρ := by ring
  rw [hrw]
  have hvol : cubeVolume Q = cubeScaleFactor Q ^ d := rfl
  rw [hvol, mul_pow]
  ring_nf
  exact le_of_eq rfl

end Geometry

end

end Algsuperdiff.Section3.Provider.Corrector
