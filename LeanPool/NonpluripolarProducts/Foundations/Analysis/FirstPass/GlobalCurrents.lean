/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GeometricForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CurrentPairing
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Global currents from compatible overlap pairings

A current of real degree `k` pairs with tests of degree `dim ℝ E - k`.
The chart transition is `e.symm.trans f`, from `e`- to `f`-coordinates.
Overlap tests are genuine smooth compactly supported forms on its source and
target. Compatibility is the explicit tensor equation, not a postulated
pullback operator. The compatible families form a real submodule.

Restrictions use test-space inclusions with explicit domain inclusions, which
exclude `monoCLM`'s zero fallback. No global test space is invented here.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.LocalCurrents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U V Ω : Opens E} {q : ℕ}

/-- The inclusion keeps the same globally extended test, including its support. -/
theorem testForm_inclusion_apply (hUΩ : U ≤ Ω) (η : TestForm U q) (x : E) :
    (TestFunction.monoCLM ℝ η : TestForm Ω q) x = η x := by
  have h := TestFunction.monoCLM_apply (𝕜 := ℝ) (n₂ := ⊤) (Ω₂ := Ω) η
  simpa only [le_refl, hUΩ, and_self, ↓reduceIte] using congrFun h x

section Restriction

variable [FiniteDimensional ℝ E] {k : Fin (Module.finrank ℝ E + 1)}

/-- Restriction of a local current, by extension of the smaller-domain tests. -/
def restrictLocalCurrent (_hUΩ : U ≤ Ω) (T : LocalCurrent Ω k) : LocalCurrent U k :=
  T.comp (TestFunction.monoCLM ℝ)

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrictLocalCurrent_apply (hUΩ : U ≤ Ω) (T : LocalCurrent Ω k)
    (η : TestForm U (Module.finrank ℝ E - k.val)) :
    restrictLocalCurrent hUΩ T η = T (TestFunction.monoCLM ℝ η) := rfl

/-- Local restriction is real linear. -/
def restrictLocalCurrentLM (hUΩ : U ≤ Ω) : LocalCurrent Ω k →ₗ[ℝ] LocalCurrent U k where
  toFun := restrictLocalCurrent hUΩ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrictLocalCurrent_refl (T : LocalCurrent Ω k) :
    restrictLocalCurrent le_rfl T = T := by
  ext η
  change T (TestFunction.monoCLM ℝ η) = T η
  congr 1
  apply TestFunction.ext
  intro x
  exact testForm_inclusion_apply le_rfl η x

omit [FiniteDimensional ℝ E] in
theorem restrictLocalCurrent_trans (hUV : U ≤ V) (hVΩ : V ≤ Ω)
    (T : LocalCurrent Ω k) :
    restrictLocalCurrent hUV (restrictLocalCurrent hVΩ T) =
      restrictLocalCurrent (hUV.trans hVΩ) T := by
  ext η
  change T (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm V _)) =
    T (TestFunction.monoCLM ℝ η)
  congr 1
  ext x
  simp only [testForm_inclusion_apply hVΩ, testForm_inclusion_apply hUV,
    testForm_inclusion_apply (hUV.trans hVΩ)]

end Restriction

section Density

variable [MeasurableSpace E] [OpensMeasurableSpace E] {r : ℕ}

/-- A locally integrable field of alternating forms yields actual distribution
coefficients. The local-integrability argument excludes the integral API's
zero fallback. Evaluation of the vector integral preserves alternation. -/
def regularFormDistribution (μ : Measure E) (a : E → E [⋀^Fin r]→L[ℝ] ℝ)
    (_ha : LocallyIntegrableOn a Ω μ) : DistributionForm Ω r := by
  let D : 𝓓'(Ω, E [⋀^Fin r]→L[ℝ] ℝ) :=
    TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ a
  exact
    { toFun := fun v => (formEvaluationCLM v).comp D
      map_update_add' v i x y := by
        ext φ
        exact (D φ).map_update_add v i x y
      map_update_smul' v i c x := by
        ext φ
        exact (D φ).map_update_smul v i c x
      map_eq_zero_of_eq' v i j hv hij := by
        ext φ
        exact (D φ).map_eq_zero_of_eq v hv hij }

theorem regularFormDistribution_apply (μ : Measure E) (a : E → E [⋀^Fin r]→L[ℝ] ℝ)
    (ha : LocallyIntegrableOn a Ω μ) (v : Fin r → E) (φ : 𝓓(Ω, ℝ)) :
    regularFormDistribution μ a ha v φ = (∫ x, φ x • a x ∂μ) v := by
  change (TestFunction.integralAgainstBilinCLM
    (ContinuousLinearMap.lsmul ℝ ℝ) μ a φ) v = _
  rw [TestFunction.integralAgainstBilinCLM_eq_integral ha]
  rfl

end Density

end SGPT.Foundations.Analysis.LocalCurrents

namespace SGPT.Foundations.Analysis.FirstPass

open LocalCurrents

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- Real current degree, bounded by the real (not complex) dimension. -/
abbrev CurrentDegree (n : ℕ) := Fin (Module.finrank ℝ (ComplexModel n) + 1)

theorem complexModel_real_finrank (n : ℕ) : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [finrank_real_of_complex]
  simp [ComplexModel]

/-- The open coordinate domain of an actual atlas chart. -/
def chartTarget (e : ComplexChart n M) : Opens (ComplexModel n) :=
  ⟨e.val.target, e.val.open_target⟩

/-- Overlap in the first chart's coordinates. -/
def overlapSource (e f : ComplexChart n M) : Opens (ComplexModel n) :=
  ⟨(chartTransition e f).source, (chartTransition e f).open_source⟩

/-- The same overlap in the second chart's coordinates. -/
def overlapTarget (e f : ComplexChart n M) : Opens (ComplexModel n) :=
  ⟨(chartTransition e f).target, (chartTransition e f).open_target⟩

theorem overlapSource_le (e f : ComplexChart n M) : overlapSource e f ≤ chartTarget e :=
  fun _ hz => hz.1

theorem overlapTarget_le (e f : ComplexChart n M) : overlapTarget e f ≤ chartTarget f :=
  fun _ hz => hz.1

/-- On an overlap, `φ ∘ e⁻¹ = (φ ∘ f⁻¹) ∘ (f ∘ e⁻¹)`. -/
theorem chart_comp_transition {α : Type*} (φ : M → α) (e f : ComplexChart n M) :
    ∀ x ∈ overlapSource e f, φ (e.val.symm x) = φ (f.val.symm (chartTransition e f x)) := by
  intro x hx
  have hx' : x ∈ (chartTransition e f).source := hx
  have hxf : e.val.symm x ∈ f.val.source := by
    simp only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hx'
    exact hx'.2
  simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    f.val.left_inv hxf]

/-- The complete pullback equation for a pair of actual overlap test forms.
Their bundled domains already require compact support in the source and target. -/
def OverlapTestRelated (e f : ComplexChart n M) {q : ℕ}
    (η : TestForm (overlapSource e f) q) (θ : TestForm (overlapTarget e f) q) : Prop :=
  ∀ z, z ∈ (chartTransition e f).source → ∀ v : Fin q → ComplexModel n,
    η z v = θ (chartTransition e f z) (fun i => chartTransitionDerivative e f z (v i))

/-- A family of genuine local continuous test-form functionals, before gluing. -/
abbrev ChartCurrentFamily (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (k : CurrentDegree n) :=
  (e : ComplexChart n M) → LocalCurrent (chartTarget e) k

/-- Agreement of pairings after the explicit tensor transformation of tests. -/
def CurrentFamilyCompatible {k : CurrentDegree n} (T : ChartCurrentFamily n M k) : Prop :=
  ∀ (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (θ : TestForm (overlapTarget e f) (Module.finrank ℝ (ComplexModel n) - k.val)),
    OverlapTestRelated e f η θ →
      restrictLocalCurrent (overlapSource_le e f) (T e) η =
        restrictLocalCurrent (overlapTarget_le e f) (T f) θ

variable [IsComplexManifold n M]

/-- Compatible families are closed under the ordinary linear operations. -/
def compatibleCurrentSubmodule (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (k : CurrentDegree n) :
    Submodule ℝ (ChartCurrentFamily n M k) where
  carrier := {T | CurrentFamilyCompatible T}
  zero_mem' := by intro e f η θ h; rfl
  add_mem' := by
    intro S T hS hT e f η θ h
    exact congrArg₂ (· + ·) (hS e f η θ h) (hT e f η θ h)
  smul_mem' := by
    intro c T hT e f η θ h
    exact congrArg (c • ·) (hT e f η θ h)

/-- A geometric global current, as a compatible family of local currents.
This type inherits the real module operations from its concrete submodule. -/
abbrev GlobalCurrent (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (k : CurrentDegree n) :=
  ↥(compatibleCurrentSubmodule n M k)

namespace GlobalCurrent

variable {k : CurrentDegree n}

/-- The actual continuous local functional in a specified chart. -/
def inChart (T : GlobalCurrent n M k) (e : ComplexChart n M) :
    LocalCurrent (chartTarget e) k := T.val e

omit [IsComplexManifold n M] in
@[ext] theorem ext {S T : GlobalCurrent n M k}
    (h : ∀ e η, S.inChart e η = T.inChart e η) : S = T := by
  apply Subtype.ext
  funext e
  exact ContinuousLinearMap.ext (h e)

omit [IsComplexManifold n M] in
@[simp] theorem inChart_zero (e : ComplexChart n M) :
    (0 : GlobalCurrent n M k).inChart e = 0 := rfl

omit [IsComplexManifold n M] in
@[simp] theorem inChart_add (S T : GlobalCurrent n M k) (e : ComplexChart n M) :
    (S + T).inChart e = S.inChart e + T.inChart e := rfl

omit [IsComplexManifold n M] in
@[simp] theorem inChart_smul (c : ℝ) (T : GlobalCurrent n M k) (e : ComplexChart n M) :
    (c • T).inChart e = c • T.inChart e := rfl

omit [IsComplexManifold n M] in
@[simp] theorem inChart_neg (T : GlobalCurrent n M k) (e : ComplexChart n M) :
    (-T).inChart e = -T.inChart e := rfl

/-- Restrict to any open subdomain of a chart. -/
def restrictChart (T : GlobalCurrent n M k) (e : ComplexChart n M)
    {U : Opens (ComplexModel n)} (hU : U ≤ chartTarget e) : LocalCurrent U k :=
  restrictLocalCurrent hU (T.inChart e)

/-- This chart restriction is a real linear map on global currents. -/
def restrictChartLM (e : ComplexChart n M) {U : Opens (ComplexModel n)}
    (hU : U ≤ chartTarget e) : GlobalCurrent n M k →ₗ[ℝ] LocalCurrent U k where
  toFun T := T.restrictChart e hU
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsComplexManifold n M] in
@[simp] theorem restrictChart_refl (T : GlobalCurrent n M k) (e : ComplexChart n M) :
    T.restrictChart e le_rfl = T.inChart e := restrictLocalCurrent_refl _

omit [IsComplexManifold n M] in
theorem restrictChart_trans (T : GlobalCurrent n M k) (e : ComplexChart n M)
    {U V : Opens (ComplexModel n)} (hUV : U ≤ V) (hV : V ≤ chartTarget e) :
    restrictLocalCurrent hUV (T.restrictChart e hV) = T.restrictChart e (hUV.trans hV) :=
  restrictLocalCurrent_trans hUV hV _

omit [IsComplexManifold n M] in
/-- The geometric overlap equation holds for every related pair of tests. -/
theorem overlap (T : GlobalCurrent n M k) (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (θ : TestForm (overlapTarget e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (h : OverlapTestRelated e f η θ) :
    T.restrictChart e (overlapSource_le e f) η =
      T.restrictChart f (overlapTarget_le e f) θ := T.property e f η θ h

end GlobalCurrent

section SmoothDensities

variable [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

/-- Smooth chart coefficients are locally integrable for the basis-normalized
Haar measure. Neither global integrability nor off-target smoothness is needed. -/
theorem smoothForm_coeff_locallyIntegrable
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {r : ℕ} (a : SmoothRealForm n M r) (e : ComplexChart n M) :
    LocallyIntegrableOn (a.coeff e) (chartTarget e) b.addHaar :=
  (a.smooth e).continuousOn.locallyIntegrableOn e.val.open_target.measurableSet

/-- The distribution coefficients of a smooth form, with density measure
normalized to give the ordered basis parallelepiped mass one. -/
def smoothFormDistribution
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {r : ℕ} (a : SmoothRealForm n M r) (e : ComplexChart n M) :
    DistributionForm (chartTarget e) r :=
  regularFormDistribution b.addHaar (a.coeff e) (smoothForm_coeff_locallyIntegrable b a e)

theorem smoothFormDistribution_apply
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {r : ℕ} (a : SmoothRealForm n M r) (e : ComplexChart n M)
    (v : Fin r → ComplexModel n) (φ : 𝓓(chartTarget e, ℝ)) :
    smoothFormDistribution b a e v φ = (∫ x, φ x • a.coeff e x ∂b.addHaar) v :=
  regularFormDistribution_apply _ _ _ _ _

/-- The actual chart family of a smooth form, using the normalized shuffle
pairing and the Haar measure belonging to the same ordered basis. Compatibility
is a Pending theorem, not an additional input to this construction. An arbitrary
`b` fixes an orientation; use a complex-positive `b` for the manuscript's oriented
integration convention. No positivity or global `ddᶜ` claim is made here. -/
def smoothCurrentFamily
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) : ChartCurrentFamily n M k :=
  fun e => toLocalCurrent b k (smoothFormDistribution b a e)

theorem smoothCurrentFamily_apply
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)) :
    smoothCurrentFamily b a e η = distributionTestPairing
      (((smoothFormDistribution b a e).domCoprod (testFormAlternating η))
        (currentPairingBasis b k)) := toLocalCurrent_eq_domCoprod b k _ η

end SmoothDensities

end SGPT.Foundations.Analysis.FirstPass
