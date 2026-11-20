/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalModeWeakIdentity
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitDiskFibreDerivativeSource
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Unit-circle surface sources for two-component whole-plane fields

The interface step of the proof of `lem:jump-horizontal-mode` is the cancellation of the
interface distributions: the singular parts of the generator are

`(Δ_⊥b)_sing = [∂_r b] δ_{r=1}`,  `((b·∇_⊥)V⁰_⊥)_sing = -Ω b_r e_θ δ_{r=1}`,

and the transmission conditions `eq:transmission-horizontal` make their sum vanish.

The surface value `unitCircleSurfaceValue` and the derivative semantics
`HasUnitCircleSourceDerivative` are the fibre-generic ones of
`Analysis/WholePlaneUnitCircleSurface.lean` and
`Analysis/WholePlaneUnitDiskFibreDerivativeSource.lean`, read at the fibre `ℂ²`.  What this
module adds is

* the `ℂ²` packaging of the surface term as a continuous Schwartz functional and as a tempered
  distribution, with the two cancellation conventions;
* the equivalence of the weak coordinate derivative with a unit-circle source with the
  corresponding tempered-distribution identity;
* the assembly theorem that turns two coordinate-source identities, one bulk identity and one
  density cancellation into `HorizontalModeDistributionalEquation`, i.e. into the weak
  eigenvalue identity of the horizontal mode.

No local Gauss-Green or slice computation is carried out here: this is the semantic layer that
such a computation feeds.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open MeasureTheory
open WholePlaneFibreSource
open scoped LineDeriv SchwartzMap

/-! ## The two-component unit-circle surface functional -/

/-- For an integrable circle density the integrand `y ↦ φ(y)·density(y)` is integrable against
the unit-circle surface measure, the Schwartz factor being uniformly bounded. -/
theorem wholePlaneC2UnitCircleSurfaceIntegrand_integrable
    {density : WholePlaneUnitCircle → C2}
    (hDensity : Integrable density wholePlaneUnitCircleMeasure)
    (φ : SchwartzMap WholePlane ℂ) :
    Integrable (fun y : WholePlaneUnitCircle ↦ φ y.1 • density y)
      wholePlaneUnitCircleMeasure := by
  have hMeas : AEStronglyMeasurable (fun y : WholePlaneUnitCircle ↦ φ y.1)
      wholePlaneUnitCircleMeasure :=
    (φ.continuous.comp continuous_subtype_val).aestronglyMeasurable
  have hBound : ∀ᵐ y : WholePlaneUnitCircle ∂wholePlaneUnitCircleMeasure,
      ‖φ y.1‖ ≤ SchwartzMap.seminorm ℂ 0 0 φ := by
    filter_upwards [] with y
    exact SchwartzMap.norm_le_seminorm ℂ φ y.1
  refine Integrable.of_eval_piLp (fun i ↦ ?_)
  change Integrable
    ((fun y : WholePlaneUnitCircle ↦ φ y.1) •
      (fun y : WholePlaneUnitCircle ↦ density y i))
    wholePlaneUnitCircleMeasure
  exact (hDensity.eval_piLp i).bdd_smul
    (SchwartzMap.seminorm ℂ 0 0 φ) hMeas hBound

/-- The surface value is controlled by the zeroth Schwartz seminorm and the `L¹` norm of the
density. -/
theorem norm_unitCircleSurfaceValue_le
    {density : WholePlaneUnitCircle → C2}
    (hDensity : Integrable density wholePlaneUnitCircleMeasure)
    (φ : SchwartzMap WholePlane ℂ) :
    ‖unitCircleSurfaceValue density φ‖ ≤
      SchwartzMap.seminorm ℂ 0 0 φ *
        ∫ y : WholePlaneUnitCircle, ‖density y‖ ∂wholePlaneUnitCircleMeasure := by
  unfold unitCircleSurfaceValue
  calc
    ‖∫ y : WholePlaneUnitCircle,
        φ y.1 • density y ∂wholePlaneUnitCircleMeasure‖
        ≤ ∫ y : WholePlaneUnitCircle,
            SchwartzMap.seminorm ℂ 0 0 φ * ‖density y‖
            ∂wholePlaneUnitCircleMeasure := by
          apply norm_integral_le_of_norm_le (hDensity.norm.const_mul _)
          filter_upwards [] with y
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right
            (SchwartzMap.norm_le_seminorm ℂ φ y.1) (norm_nonneg _)
    _ = SchwartzMap.seminorm ℂ 0 0 φ *
          ∫ y : WholePlaneUnitCircle, ‖density y‖
            ∂wholePlaneUnitCircleMeasure := integral_const_mul _ _

/-- Integration against an integrable `ℂ²`-valued unit-circle density, bundled as a continuous
complex-linear functional on whole-plane Schwartz space. -/
def wholePlaneC2UnitCircleSurfaceFunctional
    (density : WholePlaneUnitCircle → C2)
    (hDensity : Integrable density wholePlaneUnitCircleMeasure) :
    SchwartzMap WholePlane ℂ →L[ℂ] C2 := by
  refine SchwartzMap.mkCLMtoNormedSpace
    (unitCircleSurfaceValue density) ?_ ?_ ?_
  · intro φ ψ
    unfold unitCircleSurfaceValue
    rw [← integral_add
      (wholePlaneC2UnitCircleSurfaceIntegrand_integrable hDensity φ)
      (wholePlaneC2UnitCircleSurfaceIntegrand_integrable hDensity ψ)]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [add_smul]
  · intro c φ
    unfold unitCircleSurfaceValue
    calc
      (∫ y : WholePlaneUnitCircle,
          (c • φ) y.1 • density y ∂wholePlaneUnitCircleMeasure) =
          ∫ y : WholePlaneUnitCircle,
            c • (φ y.1 • density y) ∂wholePlaneUnitCircleMeasure := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp [smul_smul]
      _ = c • ∫ y : WholePlaneUnitCircle,
          φ y.1 • density y ∂wholePlaneUnitCircleMeasure :=
        integral_smul c _
  · refine ⟨{(0, 0)},
      ∫ y : WholePlaneUnitCircle, ‖density y‖ ∂wholePlaneUnitCircleMeasure,
      integral_nonneg (fun y ↦ norm_nonneg (density y)), ?_⟩
    intro φ
    simpa only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply,
      mul_comm] using
      norm_unitCircleSurfaceValue_le hDensity φ

/-- The bundled continuous functional evaluates to the surface integral. -/
@[simp] theorem wholePlaneC2UnitCircleSurfaceFunctional_apply
    (density : WholePlaneUnitCircle → C2)
    (hDensity : Integrable density wholePlaneUnitCircleMeasure)
    (φ : SchwartzMap WholePlane ℂ) :
    wholePlaneC2UnitCircleSurfaceFunctional density hDensity φ =
      unitCircleSurfaceValue density φ :=
  rfl

/-- The same continuous test functional, regarded as a `ℂ²`-valued tempered distribution. -/
def wholePlaneC2UnitCircleSurfaceTempered
    (density : WholePlaneUnitCircle → C2)
    (hDensity : Integrable density wholePlaneUnitCircleMeasure) :
    TemperedDistribution WholePlane C2 :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _
    (wholePlaneC2UnitCircleSurfaceFunctional density hDensity)

/-- The tempered distribution attached to a circle density evaluates to the surface
integral. -/
@[simp] theorem wholePlaneC2UnitCircleSurfaceTempered_apply
    (density : WholePlaneUnitCircle → C2)
    (hDensity : Integrable density wholePlaneUnitCircleMeasure)
    (φ : SchwartzMap WholePlane ℂ) :
    wholePlaneC2UnitCircleSurfaceTempered density hDensity φ =
      unitCircleSurfaceValue density φ :=
  rfl

/-- Pointwise opposite interface densities cancel when the two tempered surface terms are
added.  This is the shape in which `eq:transmission-horizontal` is used. -/
theorem wholePlaneC2UnitCircleSurfaceTempered_add_eq_zero_of_pointwise_opposite
    {density₁ density₂ : WholePlaneUnitCircle → C2}
    (hDensity₁ : Integrable density₁ wholePlaneUnitCircleMeasure)
    (hDensity₂ : Integrable density₂ wholePlaneUnitCircleMeasure)
    (h : ∀ y, density₁ y = -density₂ y) :
    wholePlaneC2UnitCircleSurfaceTempered density₁ hDensity₁ +
      wholePlaneC2UnitCircleSurfaceTempered density₂ hDensity₂ = 0 := by
  apply ContinuousLinearMap.ext
  intro φ
  change unitCircleSurfaceValue density₁ φ +
    unitCircleSurfaceValue density₂ φ = 0
  have hv : unitCircleSurfaceValue density₁ φ =
      -unitCircleSurfaceValue density₂ φ := by
    unfold unitCircleSurfaceValue
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [h y, smul_neg]
  rw [hv, neg_add_cancel]

/-! ## Weak derivatives with a unit-circle source -/

/-- The explicit integral identity with a unit-circle source is exactly the equality between
the tempered derivative and the sum of the `L²` bulk distribution and the surface
distribution. -/
theorem wholePlaneC2_distributionDerivative_eq_bulk_add_unitCircleSurface
    {f bulk : WholePlaneC2L2}
    {density : WholePlaneUnitCircle → C2}
    (hDensity : Integrable density wholePlaneUnitCircleMeasure)
    {j : Fin 2}
    (h : HasUnitCircleSourceDerivative f bulk density j) :
    ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered C2 f) =
      wholePlaneL2ToTempered C2 bulk +
        wholePlaneC2UnitCircleSurfaceTempered density hDensity := by
  ext φ i
  simpa only [TemperedDistribution.lineDerivOp_apply_apply,
    wholePlaneL2ToTempered_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply, add_apply,
    wholePlaneC2UnitCircleSurfaceTempered_apply] using
    congrArg (fun z : C2 ↦ z i) (h φ)

/-! ## Assembling the distributional eigenvalue equation -/

/-- The remaining interface step of `lem:jump-horizontal-mode`, in the exact shape the
two-component weak identity needs.

Given, for each coordinate direction `j`, a decomposition of the distributional derivative of
the pivot field `∂_jb + w_⊥b_j` into an `L²` bulk part and a unit-circle source, the weak
eigenvalue identity `𝔩_w(b,φ) = -λ⟨b,φ⟩` follows from exactly two further facts:

* the **bulk identity** `bulk₀ + bulk₁ = N²b + w_⊥·∇_⊥b + iNw₃b + w_⊥(Div_⊥b) + λb`, which off
  the unit circle is the radial Bessel system of `eq:bessel-solutions`;
* the **interface cancellation** `density₀ = -density₁`, which is
  `eq:transmission-horizontal`. -/
theorem horizontalModeDistributionalEquation_of_coordinate_sources
    (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) (lam : ℂ)
    (bulk : Fin 2 → WholePlaneC2L2)
    (density : Fin 2 → WholePlaneUnitCircle → C2)
    (hDensity : ∀ j : Fin 2, Integrable (density j) wholePlaneUnitCircleMeasure)
    (hsource : ∀ j : Fin 2,
      HasUnitCircleSourceDerivative
        (horizontalWeakFormDerivativePivot w b j) (bulk j) (density j) j)
    (hbulk : bulk 0 + bulk 1 =
      horizontalWeakFormMassPivot N w b + lam • wholePlaneH1Embedding C2 b)
    (hcancel : ∀ y : WholePlaneUnitCircle, density 0 y = -density 1 y) :
    HorizontalModeDistributionalEquation N w b lam := by
  have hzero := wholePlaneC2_distributionDerivative_eq_bulk_add_unitCircleSurface
    (hDensity 0) (hsource 0)
  have hone := wholePlaneC2_distributionDerivative_eq_bulk_add_unitCircleSurface
    (hDensity 1) (hsource 1)
  have hsurf := wholePlaneC2UnitCircleSurfaceTempered_add_eq_zero_of_pointwise_opposite
    (hDensity 0) (hDensity 1) hcancel
  unfold HorizontalModeDistributionalEquation
  rw [Fin.sum_univ_two, hzero, hone, ← hbulk, map_add]
  calc
    wholePlaneL2ToTempered C2 (bulk 0) +
          wholePlaneC2UnitCircleSurfaceTempered (density 0) (hDensity 0) +
        (wholePlaneL2ToTempered C2 (bulk 1) +
          wholePlaneC2UnitCircleSurfaceTempered (density 1) (hDensity 1)) =
        wholePlaneL2ToTempered C2 (bulk 0) + wholePlaneL2ToTempered C2 (bulk 1) +
          (wholePlaneC2UnitCircleSurfaceTempered (density 0) (hDensity 0) +
            wholePlaneC2UnitCircleSurfaceTempered (density 1) (hDensity 1)) := by
      abel
    _ = wholePlaneL2ToTempered C2 (bulk 0) + wholePlaneL2ToTempered C2 (bulk 1) := by
      rw [hsurf, add_zero]

/-- The same assembly, stated directly for the weak eigenvalue identity. -/
theorem horizontalModeWeakEquation_of_coordinate_sources
    (N : ℝ) (w : WholePlaneC3LInf) (b : WholePlaneC2H1) (lam : ℂ)
    (bulk : Fin 2 → WholePlaneC2L2)
    (density : Fin 2 → WholePlaneUnitCircle → C2)
    (hDensity : ∀ j : Fin 2, Integrable (density j) wholePlaneUnitCircleMeasure)
    (hsource : ∀ j : Fin 2,
      HasUnitCircleSourceDerivative
        (horizontalWeakFormDerivativePivot w b j) (bulk j) (density j) j)
    (hbulk : bulk 0 + bulk 1 =
      horizontalWeakFormMassPivot N w b + lam • wholePlaneH1Embedding C2 b)
    (hcancel : ∀ y : WholePlaneUnitCircle, density 0 y = -density 1 y) :
    HorizontalModeWeakEquation N w b lam :=
  (horizontalModeWeakEquation_iff_distributional N w b lam).2
    (horizontalModeDistributionalEquation_of_coordinate_sources N w b lam bulk density
      hDensity hsource hbulk hcancel)

end HorizontalMode
end FastDynamo
