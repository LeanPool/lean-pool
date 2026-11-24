/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicMaps
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Change of coordinates for smooth currents

This file proves the overlap pairing equality for the smooth density family.
The proof separates the normalized shuffle-wedge determinant identity from
Mathlib's change-of-variables theorem and the zero extension of overlap tests.
The global constructor therefore requires no compatibility hypothesis from its
caller.

The model is the concrete finite-dimensional complex space `ComplexModel n`,
with its compatible real scalar action and real dimension `2*n`. The manifold,
measurable and Borel structures are explicit. The density measure is specifically
`b.addHaar`, whose Haar and local-finiteness properties are mathlib instances,
not an unspecified measure or an extra change-of-variables assumption. The same
ordered basis fixes the volume in `toLocalCurrent`; changing its orientation
changes the sign of the associated integration current. Choose a complex-positive
basis for the manuscript convention. Global positivity and the normalized global
`ddᶜ = i ∂∂bar/(2π)` correspondence are not asserted here.
-/

@[expose] public section

noncomputable section

open TopologicalSpace MeasureTheory
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.GlobalCurrents

open FirstPass LocalCurrents
open FirstPass.HolomorphicMaps

theorem chartTransitionDerivative_det_nonneg
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (e f : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source) :
    0 ≤ (chartTransitionDerivative e f z).det := by
  rw [chartTransitionDerivative,
    ((chartTransition_contDiffAt e f hz).differentiableAt
      (by simp)).fderiv_restrictScalars ℝ]
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_nonneg _

/-- The scalar density obtained by taking the normalized shuffle wedge of a
smooth form coefficient with a complementary-degree test form. -/
def smoothWedgeDensity
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val))
    (x : ComplexModel n) : ℝ :=
  ∑ s : Equiv.Perm.ModSumCongr (Fin k.val)
      (Fin (Module.finrank ℝ (ComplexModel n) - k.val)),
    ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
      (a.coeff e x (fun i => currentPairingBasis b k (s.out (Sum.inl i))) *
        η x (fun j => currentPairingBasis b k (s.out (Sum.inr j))))

/-- A smooth local current is the ordinary Haar integral of its scalar
top-degree shuffle density. This removes the distribution and tensor-product
wrappers before applying change of variables. -/
theorem smoothCurrentFamily_apply_eq_integral_smoothWedgeDensity
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)) :
    smoothCurrentFamily b a e η = ∫ x, smoothWedgeDensity b a e η x ∂b.addHaar := by
  change wedgePairing (currentPairingBasis b k) (smoothFormDistribution b a e) η = _
  rw [wedgePairing_apply]
  simp only [Units.smul_def, zsmul_eq_mul]
  have hvec (s : Equiv.Perm.ModSumCongr (Fin k.val)
      (Fin (Module.finrank ℝ (ComplexModel n) - k.val))) :
      Integrable (fun x =>
        (testCoefficientCLM
            (fun j => currentPairingBasis b k (s.out (Sum.inr j))) η x) •
          a.coeff e x) b.addHaar :=
    TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b a e)
      (testCoefficientCLM (fun j => currentPairingBasis b k (s.out (Sum.inr j))) η)
  have hterm (s : Equiv.Perm.ModSumCongr (Fin k.val)
      (Fin (Module.finrank ℝ (ComplexModel n) - k.val))) :
      ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (smoothFormDistribution b a e)
            (fun i => currentPairingBasis b k (s.out (Sum.inl i)))
            (testCoefficientCLM
              (fun j => currentPairingBasis b k (s.out (Sum.inr j))) η) =
        ∫ x, ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (a.coeff e x (fun i => currentPairingBasis b k (s.out (Sum.inl i))) *
            η x (fun j => currentPairingBasis b k (s.out (Sum.inr j)))) ∂b.addHaar := by
    rw [smoothFormDistribution_apply]
    change ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
        formEvaluationCLM
          (fun i => currentPairingBasis b k (s.out (Sum.inl i)))
          (∫ x, (testCoefficientCLM
              (fun j => currentPairingBasis b k (s.out (Sum.inr j))) η x) •
                a.coeff e x ∂b.addHaar) = _
    rw [← (formEvaluationCLM
      (fun i => currentPairingBasis b k (s.out (Sum.inl i)))).integral_comp_comm (hvec s)]
    rw [← integral_const_mul]
    congr 1
    funext x
    simp [mul_comm]
  simp_rw [hterm]
  rw [← integral_finsetSum Finset.univ]
  · simp only [smoothWedgeDensity]
  · intro s _
    have hs := (formEvaluationCLM
      (fun i => currentPairingBasis b k (s.out (Sum.inl i)))).integrable_comp (hvec s)
    exact (hs.const_mul ((Equiv.Perm.sign s.out : ℤ) : ℝ)).congr
      (Filter.Eventually.of_forall fun x => by simp [mul_comm])

/-- The scalar exterior product used by the smooth current density. -/
def scalarWedge {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {r q : ℕ} (α : E [⋀^Fin r]→L[ℝ] ℝ) (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    E [⋀^(Fin r ⊕ Fin q)]→ₗ[ℝ] ℝ :=
  (LinearMap.mul' ℝ ℝ).compAlternatingMap
    (α.toAlternatingMap.domCoprod β.toAlternatingMap)

/-- Evaluation of the scalar exterior product is the normalized shuffle sum,
including the endpoint degrees. -/
theorem scalarWedge_apply {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E]
    {r q : ℕ} (α : E [⋀^Fin r]→L[ℝ] ℝ) (β : E [⋀^Fin q]→L[ℝ] ℝ)
    (v : Fin r ⊕ Fin q → E) :
    scalarWedge α β v =
      ∑ s : Equiv.Perm.ModSumCongr (Fin r) (Fin q),
        ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (α (fun i ↦ v (s.out (Sum.inl i))) *
            β (fun j ↦ v (s.out (Sum.inr j)))) := by
  rw [scalarWedge, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  conv_lhs => rw [← Quotient.out_eq s, AlternatingMap.domCoprod.summand_mk'']
  rcases Int.units_eq_one_or (Equiv.Perm.sign s.out) with hs | hs
  · rw [hs]
    simp [LinearMap.mul'_apply]
  · rw [hs]
    simp [LinearMap.mul'_apply]

/-- Pulling both factors of a top-degree scalar wedge back by the same linear
map multiplies its value on the basis by the determinant. -/
theorem scalarWedge_comp_basis {n r q : ℕ}
    (B : Module.Basis (Fin r ⊕ Fin q) ℝ (ComplexModel n))
    (D : ComplexModel n →L[ℝ] ComplexModel n)
    (α : ComplexModel n [⋀^Fin r]→L[ℝ] ℝ) (β : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :
    scalarWedge (α.compContinuousLinearMap D) (β.compContinuousLinearMap D) B =
      D.det * scalarWedge α β B := by
  let W := scalarWedge α β
  have hpull : scalarWedge (α.compContinuousLinearMap D) (β.compContinuousLinearMap D) B =
      W (D ∘ B) := by
    rw [scalarWedge_apply, scalarWedge_apply]
    rfl
  rw [hpull]
  have htop := congrArg
    (fun A : ComplexModel n [⋀^(Fin r ⊕ Fin q)]→ₗ[ℝ] ℝ ↦ A (D ∘ B)) (W.eq_smul_basis_det B)
  have hdet : B.det (D ∘ B) = LinearMap.det D.toLinearMap := by
    change B.det (D.toLinearMap ∘ B) = LinearMap.det D.toLinearMap
    rw [B.det_comp, B.det_self, mul_one]
  calc
    W (D ∘ B) = ((W B) • B.det) (D ∘ B) := htop
    _ = W B * B.det (D ∘ B) := by simp
    _ = LinearMap.det D.toLinearMap * W B := by rw [hdet, mul_comm]

/-- The concrete density is evaluation of the scalar exterior product on the
ordered current-pairing basis. -/
private theorem smoothWedgeDensity_eq_scalarWedge
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val))
    (x : ComplexModel n) :
    smoothWedgeDensity b a e η x =
      scalarWedge (a.coeff e x) (η x) (currentPairingBasis b k) := by
  rw [scalarWedge_apply]
  rfl

/-- On an overlap the source density is the target density multiplied by the
real Jacobian determinant of the holomorphic chart transition. -/
theorem smoothWedgeDensity_overlap_pointwise
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f)
      (Module.finrank ℝ (ComplexModel n) - k.val))
    (θ : TestForm (overlapTarget e f)
      (Module.finrank ℝ (ComplexModel n) - k.val))
    (h : OverlapTestRelated e f η θ) (x : ComplexModel n)
    (hx : x ∈ (chartTransition e f).source) :
    smoothWedgeDensity b a e (TestFunction.monoCLM ℝ η) x =
      (chartTransitionDerivative e f x).det *
        smoothWedgeDensity b a f (TestFunction.monoCLM ℝ θ)
          (chartTransition e f x) := by
  rw [smoothWedgeDensity_eq_scalarWedge, smoothWedgeDensity_eq_scalarWedge,
    LocalCurrents.testForm_inclusion_apply (overlapSource_le e f),
    LocalCurrents.testForm_inclusion_apply (overlapTarget_le e f)]
  let D := chartTransitionDerivative e f x
  have ha : a.coeff e x = (a.coeff f (chartTransition e f x)).compContinuousLinearMap D :=
    ContinuousAlternatingMap.ext (a.compatible e f x hx)
  have hη : η x = (θ (chartTransition e f x)).compContinuousLinearMap D :=
    ContinuousAlternatingMap.ext (h x hx)
  rw [ha, hη]
  exact scalarWedge_comp_basis (currentPairingBasis b k) (chartTransitionDerivative e f x) _ _

/-- A test form vanishes away from its declared open domain. -/
private theorem testForm_eq_zero_of_not_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} {q : ℕ} (η : TestForm Ω q) {x : E} (hx : x ∉ Ω) :
    η x = 0 := by
  by_contra hη
  exact hx (η.tsupport_subset (subset_closure hη))

/-- The shuffle density vanishes wherever its test-form factor vanishes. -/
private theorem smoothWedgeDensity_eq_zero_of_test_eq_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val))
    (x : ComplexModel n) (hη : η x = 0) :
    smoothWedgeDensity b a e η x = 0 := by
  simp [smoothWedgeDensity, hη]

/-- The remaining scalar change-of-variables identity. All distribution and
tensor-product wrappers have been removed: the two integrands are the genuine
shuffle wedges, extended by zero from the overlap test domains. Its proof is the
pointwise determinant identity followed by
`integral_target_eq_integral_abs_det_fderiv_smul`; nonnegativity of the
holomorphic real Jacobian is `chartTransitionDerivative_det_nonneg`. -/
theorem integral_smoothWedgeDensity_overlap
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (θ : TestForm (overlapTarget e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (h : OverlapTestRelated e f η θ) :
    (∫ x, smoothWedgeDensity b a e (TestFunction.monoCLM ℝ η) x ∂b.addHaar) =
      ∫ x, smoothWedgeDensity b a f (TestFunction.monoCLM ℝ θ) x ∂b.addHaar := by
  let F := chartTransition e f
  let D := chartTransitionDerivative e f
  let gS := fun x ↦ smoothWedgeDensity b a e (TestFunction.monoCLM ℝ η) x
  let gT := fun x ↦ smoothWedgeDensity b a f (TestFunction.monoCLM ℝ θ) x
  have hzeroS {x : ComplexModel n} (hx : x ∉ F.source) : gS x = 0 := by
    apply smoothWedgeDensity_eq_zero_of_test_eq_zero
    rw [LocalCurrents.testForm_inclusion_apply (overlapSource_le e f)]
    exact testForm_eq_zero_of_not_mem η hx
  have hzeroT {x : ComplexModel n} (hx : x ∉ F.target) : gT x = 0 := by
    apply smoothWedgeDensity_eq_zero_of_test_eq_zero
    rw [LocalCurrents.testForm_inclusion_apply (overlapTarget_le e f)]
    exact testForm_eq_zero_of_not_mem θ hx
  have hfullS : (∫ x, gS x ∂b.addHaar) =
      ∫ x in F.source, gS x ∂b.addHaar := by
    rw [← MeasureTheory.integral_indicator F.open_source.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ F.source
    · simp [hx]
    · simp [hx, hzeroS hx]
  have hfullT : (∫ x, gT x ∂b.addHaar) =
      ∫ x in F.target, gT x ∂b.addHaar := by
    rw [← MeasureTheory.integral_indicator F.open_target.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ F.target
    · simp [hx]
    · simp [hx, hzeroT hx]
  have hderiv (x : ComplexModel n) (hx : x ∈ F.source) :
      HasFDerivAt F (D x) x := by
    exact ((chartTransition_contDiffAt_real e f hx).differentiableAt
      (by simp)).hasFDerivAt
  have hchange := integral_target_eq_integral_abs_det_fderiv_smul
    b.addHaar hderiv gT
  have hsource : (∫ x in F.source, gS x ∂b.addHaar) =
      ∫ x in F.source, |(D x).det| • gT (F x) ∂b.addHaar := by
    apply MeasureTheory.setIntegral_congr_fun F.open_source.measurableSet
    intro x hx
    change gS x = |(D x).det| * gT (F x)
    rw [abs_of_nonneg (chartTransitionDerivative_det_nonneg e f hx)]
    exact smoothWedgeDensity_overlap_pointwise b a e f η θ h x hx
  calc
    (∫ x, gS x ∂b.addHaar) = ∫ x in F.source, gS x ∂b.addHaar := hfullS
    _ = ∫ x in F.source, |(D x).det| • gT (F x) ∂b.addHaar := hsource
    _ = ∫ x in F.target, gT x ∂b.addHaar := hchange.symm
    _ = ∫ x, gT x ∂b.addHaar := hfullT.symm

/-- Holomorphic change of variables for the normalized smooth current family.
Source and target tests obey the full covariant tensor equation; the conclusion
compares their actual continuous local pairings. -/
theorem smoothCurrentFamily_overlap
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (θ : TestForm (overlapTarget e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (h : OverlapTestRelated e f η θ) :
    restrictLocalCurrent (overlapSource_le e f) (smoothCurrentFamily b a e) η =
      restrictLocalCurrent (overlapTarget_le e f) (smoothCurrentFamily b a f) θ := by
  change smoothCurrentFamily b a e (TestFunction.monoCLM ℝ η) =
    smoothCurrentFamily b a f (TestFunction.monoCLM ℝ θ)
  rw [smoothCurrentFamily_apply_eq_integral_smoothWedgeDensity,
    smoothCurrentFamily_apply_eq_integral_smoothWedgeDensity]
  exact integral_smoothWedgeDensity_overlap b a e f η θ h

/-- The actual global smooth current. There is no compatibility proof argument. -/
def smoothGlobalCurrent
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) : GlobalCurrent n M k :=
  ⟨smoothCurrentFamily b a, fun e f η θ h => smoothCurrentFamily_overlap b a e f η θ h⟩

@[simp] theorem smoothGlobalCurrent_inChart
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (a : SmoothRealForm n M k.val) (e : ComplexChart n M) :
    (smoothGlobalCurrent b a).inChart e = smoothCurrentFamily b a e := rfl

end SGPT.Foundations.Analysis.Pending.GlobalCurrents
