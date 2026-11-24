/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalCurrentPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicDDC
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothDistribution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Holomorphic covariance of `ddᶜ` of a locally integrable potential

The pairing of `ddᶜ T` with a complementary-degree test form is `T` applied to
an explicit second-order test function built from the test form. For a smooth
potential this test function integrates to the smooth shuffle density of
`ddᶜ`, which is covariant under holomorphic chart transitions. Testing against
all smooth compactly supported functions identifies the source test function
with the Jacobian-weighted pullback of the target one; change of variables then
gives covariance for every locally integrable potential.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.DDCOverlap

open FirstPass LocalCurrents FirstPass.HolomorphicMaps FirstPass.HolomorphicDDC

variable {n : ℕ}

section Transpose

variable {Ω : Opens (ComplexModel n)} {q : ℕ}

/-- The second directional derivative `∂_v ∂_w` on test functions. -/
def testSecondDeriv (v w : ComplexModel n) : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v ∘L
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w

/-- Applying a distribution to a second derivative of a test function is the
second distributional derivative, taken in the opposite order. -/
theorem lineDerivCLM_lineDerivCLM_apply (T : 𝓓'(Ω, ℝ)) (v w : ComplexModel n)
    (φ : 𝓓(Ω, ℝ)) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) w T) φ =
      T (testSecondDeriv w v φ) := by
  simp [Distribution.lineDerivCLM_apply, testSecondDeriv]

/-- The adjoint of `ddᶜ` in one pair of directions. -/
def ddcAdjointCoeff (v w : ComplexModel n) : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  (-1 / (4 * Real.pi) : ℝ) •
    (testSecondDeriv (Complex.I • w) v - testSecondDeriv (Complex.I • v) w)

theorem ddC_apply_eq (T : 𝓓'(Ω, ℝ)) (v w : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    ddC T ![v, w] φ = T (ddcAdjointCoeff v w φ) := by
  rw [ddC_apply]
  simp [ddcAdjointCoeff, lineDerivCLM_lineDerivCLM_apply, map_sub, map_smul]

/-- The test function to which a distribution is applied when `ddᶜ` of it is
paired with a test form along a shuffle frame. -/
def ddcAdjoint (B : Fin 2 ⊕ Fin q → ComplexModel n) : TestForm Ω q →L[ℝ] 𝓓(Ω, ℝ) :=
  ∑ s : Equiv.Perm.ModSumCongr (Fin 2) (Fin q),
    ((Equiv.Perm.sign s.out : ℤ) : ℝ) •
      (ddcAdjointCoeff (B (s.out (Sum.inl 0))) (B (s.out (Sum.inl 1)))).comp
        (testCoefficientCLM (fun j => B (s.out (Sum.inr j))))

theorem wedgePairing_ddC (B : Fin 2 ⊕ Fin q → ComplexModel n) (T : 𝓓'(Ω, ℝ))
    (η : TestForm Ω q) :
    wedgePairing B (ddC T) η = T (ddcAdjoint B η) := by
  rw [wedgePairing_apply]
  simp only [ddcAdjoint, sum_apply, map_sum,
    smul_apply, ContinuousLinearMap.comp_apply, map_smul]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hfun : (fun i : Fin 2 => B (s.out (Sum.inl i))) =
      ![B (s.out (Sum.inl 0)), B (s.out (Sum.inl 1))] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun, ddC_apply_eq, Units.smul_def, zsmul_eq_mul, smul_eq_mul]

end Transpose

/-- The adjoint test function only depends on the underlying test form, not on
the open set on which it is regarded as a test form. -/
theorem ddcAdjoint_monoCLM_apply {U Ω : Opens (ComplexModel n)} {q : ℕ} (hUΩ : U ≤ Ω)
    (B : Fin 2 ⊕ Fin q → ComplexModel n) (η : TestForm U q) (x : ComplexModel n) :
    ddcAdjoint B (TestFunction.monoCLM ℝ η : TestForm Ω q) x = ddcAdjoint B η x := by
  have hcoef (v : Fin q → ComplexModel n) :
      ((testCoefficientCLM v (TestFunction.monoCLM ℝ η : TestForm Ω q) : 𝓓(Ω, ℝ)) :
        ComplexModel n → ℝ) = testCoefficientCLM v η := by
    funext y
    simp [testForm_inclusion_apply hUΩ]
  have hder (w : ComplexModel n) (v : Fin q → ComplexModel n) :
      ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w
          (testCoefficientCLM v (TestFunction.monoCLM ℝ η : TestForm Ω q)) : 𝓓(Ω, ℝ)) :
        ComplexModel n → ℝ) =
      TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w (testCoefficientCLM v η) := by
    funext y
    simp [hcoef]
  simp [ddcAdjoint, ddcAdjointCoeff, testSecondDeriv, hder]

section Smooth

variable {Ω : Opens (ComplexModel n)} {q : ℕ}
variable [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
  {μ : Measure (ComplexModel n)} [μ.IsAddHaarMeasure]

/-- The coefficient of `ddᶜ` of a `C²` regular distribution is the regular
distribution of the classical `ddᶜ` coefficient. -/
theorem ddC_regularDistribution_apply {h : ComplexModel n → ℝ} (hh : ContDiff ℝ 2 h)
    (v w : ComplexModel n) (φ : 𝓓(Ω, ℝ)) :
    ddC (regularDistribution μ h (hh.continuous.locallyIntegrable.locallyIntegrableOn Ω))
        ![v, w] φ =
      ∫ x, φ x * smoothDDC h x ![v, w] ∂μ := by
  rw [ddC_apply]
  simp only [smul_apply, sub_apply,
    lineDerivCLM_lineDerivCLM_regularDistribution hh, regularDistribution_apply]
  have hint (a b : ComplexModel n) : Integrable (fun x => φ x * realHessian h x a b) μ :=
    TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      ((continuous_realHessian hh a b).locallyIntegrable.locallyIntegrableOn Ω) φ
  rw [← integral_sub (hint _ _) (hint _ _), smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smoothDDC_apply_eq_realHessian (hh.contDiffAt)]
  ring

/-- The classical shuffle density of `ddᶜh` against a test form. -/
def ddcDensity (B : Fin 2 ⊕ Fin q → ComplexModel n) (h : ComplexModel n → ℝ)
    (η : TestForm Ω q) (x : ComplexModel n) : ℝ :=
  ∑ s : Equiv.Perm.ModSumCongr (Fin 2) (Fin q),
    ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
      (smoothDDC h x (fun i => B (s.out (Sum.inl i))) *
        η x (fun j => B (s.out (Sum.inr j))))

/-- For a smooth potential, the adjoint test function integrates to the
classical shuffle density of `ddᶜ`. -/
theorem integral_ddcAdjoint_mul {h : ComplexModel n → ℝ} (hh : ContDiff ℝ ∞ h)
    (B : Fin 2 ⊕ Fin q → ComplexModel n) (η : TestForm Ω q) :
    ∫ x, ddcAdjoint B η x * h x ∂μ = ∫ x, ddcDensity B h η x ∂μ := by
  have hh2 : ContDiff ℝ 2 h := hh.of_le (by norm_cast)
  have hloc : LocallyIntegrableOn h Ω μ := hh.continuous.locallyIntegrable.locallyIntegrableOn Ω
  rw [← regularDistribution_apply μ h hloc, ← wedgePairing_ddC, wedgePairing_apply]
  have hsmooth (v : Fin 2 → ComplexModel n) : Continuous (fun x => smoothDDC h x v) := by
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    simp only [smoothDDC_apply_eq_realHessian hh2.contDiffAt]
    exact ((continuous_realHessian hh2 _ _).sub (continuous_realHessian hh2 _ _)).div_const _
  have hterm (s : Equiv.Perm.ModSumCongr (Fin 2) (Fin q)) :
      Equiv.Perm.sign s.out •
          ddC (regularDistribution μ h hloc) (fun i => B (s.out (Sum.inl i)))
            (testCoefficientCLM (fun j => B (s.out (Sum.inr j))) η) =
        ∫ x, ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (smoothDDC h x (fun i => B (s.out (Sum.inl i))) *
            η x (fun j => B (s.out (Sum.inr j)))) ∂μ := by
    have hfun : (fun i : Fin 2 => B (s.out (Sum.inl i))) =
        ![B (s.out (Sum.inl 0)), B (s.out (Sum.inl 1))] := by
      funext i
      fin_cases i <;> rfl
    rw [Units.smul_def, zsmul_eq_mul, hfun, ddC_regularDistribution_apply hh2,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [testCoefficientCLM_apply]
    ring
  simp_rw [hterm]
  rw [← integral_finsetSum Finset.univ]
  · rfl
  · intro s _
    have hi := TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      (((hsmooth (fun i => B (s.out (Sum.inl i)))).locallyIntegrable (μ := μ)).locallyIntegrableOn
        (Ω : Set (ComplexModel n)))
      (testCoefficientCLM (fun j => B (s.out (Sum.inr j))) η)
    exact (hi.const_mul ((Equiv.Perm.sign s.out : ℤ) : ℝ)).congr
      (Eventually.of_forall fun x => by simp [mul_comm])

end Smooth

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Transport of a function along the inverse of a partial homeomorphism,
extended by zero off the target. -/
def transportSymm (F : OpenPartialHomeomorph E E) (φ : E → ℝ) (y : E) : ℝ :=
  open Classical in if y ∈ F.target then φ (F.symm y) else 0

omit [NormedSpace ℝ E] in
theorem transportSymm_comp_eventuallyEq (F : OpenPartialHomeomorph E E) (φ : E → ℝ)
    {x : E} (hx : x ∈ F.source) : φ =ᶠ[𝓝 x] fun y => transportSymm F φ (F y) := by
  filter_upwards [F.open_source.mem_nhds hx] with y hy
  simp [transportSymm, F.map_source hy, F.left_inv hy]

/-- A smooth function with compact support inside the source transports to a
globally smooth function when the inverse is smooth. -/
theorem contDiff_transportSymm (F : OpenPartialHomeomorph E E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ F.source)
    (hsymm : ∀ y ∈ F.target, ContDiffAt ℝ ∞ F.symm y) :
    ContDiff ℝ ∞ (transportSymm F φ) := by
  have hK : IsCompact (F '' tsupport φ) :=
    hc.isCompact.image_of_continuousOn (F.continuousOn.mono hs)
  have hKt : F '' tsupport φ ⊆ F.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact F.map_source (hs hx)
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ F.target
  · have hev : transportSymm F φ =ᶠ[𝓝 y] fun z => φ (F.symm z) := by
      filter_upwards [F.open_target.mem_nhds hy] with z hz
      simp [transportSymm, hz]
    exact (hφ.contDiffAt.comp y (hsymm y hy)).congr_of_eventuallyEq hev
  · have hyK : y ∉ F '' tsupport φ := fun h => hy (hKt h)
    have hev : transportSymm F φ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hyK] with z hz
      by_cases hzt : z ∈ F.target
      · have hz' : F.symm z ∉ tsupport φ := fun h =>
          hz ⟨F.symm z, h, F.right_inv hzt⟩
        simp [transportSymm, hzt, image_eq_zero_of_notMem_tsupport hz']
      · simp [transportSymm, hzt]
    exact contDiffAt_const.congr_of_eventuallyEq hev

end Transport

section Pointwise

/-- The scalar exterior product of two real alternating forms. -/
private def scalarWedge {r q : ℕ} (α : ComplexModel n [⋀^Fin r]→L[ℝ] ℝ)
    (β : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :
    ComplexModel n [⋀^(Fin r ⊕ Fin q)]→ₗ[ℝ] ℝ :=
  (LinearMap.mul' ℝ ℝ).compAlternatingMap (α.toAlternatingMap.domCoprod β.toAlternatingMap)

private theorem scalarWedge_apply {r q : ℕ} (α : ComplexModel n [⋀^Fin r]→L[ℝ] ℝ)
    (β : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) (v : Fin r ⊕ Fin q → ComplexModel n) :
    scalarWedge α β v =
      ∑ s : Equiv.Perm.ModSumCongr (Fin r) (Fin q),
        ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (α (fun i ↦ v (s.out (Sum.inl i))) * β (fun j ↦ v (s.out (Sum.inr j)))) := by
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {q : ℕ}

/-- On an overlap, the classical `ddᶜ` shuffle density of a potential that is
locally the pullback of a target potential is the target density times the
real Jacobian determinant of the holomorphic transition. -/
theorem ddcDensity_overlap_pointwise (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n))
    (e f : ComplexChart n M) (η : TestForm (overlapSource e f) q)
    (θ : TestForm (overlapTarget e f) q) (hηθ : OverlapTestRelated e f η θ)
    {g h : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g (chartTransition e f).target)
    {x : ComplexModel n} (hx : x ∈ (chartTransition e f).source)
    (hhg : h =ᶠ[𝓝 x] fun y => g (chartTransition e f y)) :
    ddcDensity B h η x =
      (chartTransitionDerivative e f x).det * ddcDensity B g θ (chartTransition e f x) := by
  let F := chartTransition e f
  let D := chartTransitionDerivative e f x
  have hF : ContDiffOn ℂ ∞ F F.source := fun y hy =>
    (chartTransition_contDiffAt e f hy).contDiffWithinAt
  have hddc : smoothDDC h x = (smoothDDC g (F x)).compContinuousLinearMap D :=
    (smoothDDC_congr hhg).trans
      (smoothDDC_comp F.open_source F.open_target hF hg F.mapsTo hx)
  have hdens (k : ComplexModel n → ℝ) (Ω : Opens (ComplexModel n)) (ζ : TestForm Ω q)
      (y : ComplexModel n) :
      ddcDensity B k ζ y = scalarWedge (smoothDDC k y) (ζ y) B := by
    rw [scalarWedge_apply]
    rfl
  rw [hdens, hdens]
  let W := scalarWedge (smoothDDC g (F x)) (θ (F x))
  have hpull : scalarWedge (smoothDDC h x) (η x) B = W (D ∘ B) := by
    rw [scalarWedge_apply, scalarWedge_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hddc, hηθ x hx]
    rfl
  rw [hpull]
  have htop := congrArg
    (fun A : ComplexModel n [⋀^(Fin 2 ⊕ Fin q)]→ₗ[ℝ] ℝ ↦ A (D ∘ B)) (W.eq_smul_basis_det B)
  have hdet : B.det (D ∘ B) = LinearMap.det D.toLinearMap := by
    change B.det (D.toLinearMap ∘ B) = LinearMap.det D.toLinearMap
    rw [B.det_comp, B.det_self, mul_one]
  calc
    W (D ∘ B) = ((W B) • B.det) (D ∘ B) := htop
    _ = W B * B.det (D ∘ B) := by simp
    _ = LinearMap.det D.toLinearMap * W B := by rw [hdet, mul_comm]

end Pointwise

section Assembly

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
  {q : ℕ}

omit [IsComplexManifold n M] [MeasurableSpace (ComplexModel n)]
  [BorelSpace (ComplexModel n)] in
theorem chartTransition_symm_apply (e f : ComplexChart n M) (y : ComplexModel n) :
    (chartTransition e f).symm y = chartTransition f e y := by
  simp [chartTransition]

omit [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
theorem contDiffAt_chartTransition_symm (e f : ComplexChart n M) {y : ComplexModel n}
    (hy : y ∈ (chartTransition e f).target) :
    ContDiffAt ℝ ∞ (chartTransition e f).symm y := by
  have hfun : ((chartTransition e f).symm : ComplexModel n → ComplexModel n) =
      chartTransition f e := funext (chartTransition_symm_apply e f)
  rw [hfun]
  apply chartTransition_contDiffAt_real f e
  simpa [chartTransition] using hy

omit [IsComplexManifold n M] [MeasurableSpace (ComplexModel n)]
  [BorelSpace (ComplexModel n)] in
theorem testForm_eq_zero_of_notMem {Ω : Opens (ComplexModel n)} (η : TestForm Ω q)
    {x : ComplexModel n} (hx : x ∉ Ω) : η x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (η.tsupport_subset h)

omit [IsComplexManifold n M] [MeasurableSpace (ComplexModel n)]
  [BorelSpace (ComplexModel n)] in
theorem ddcDensity_eq_zero_of_notMem {Ω : Opens (ComplexModel n)}
    (B : Fin 2 ⊕ Fin q → ComplexModel n) (h : ComplexModel n → ℝ) (η : TestForm Ω q)
    {x : ComplexModel n} (hx : x ∉ Ω) : ddcDensity B h η x = 0 := by
  simp [ddcDensity, testForm_eq_zero_of_notMem η hx]

/-- The smooth test identity: pairing the source adjoint test function with a
smooth function compactly supported in the overlap equals pairing the target
adjoint test function with its transport, rewritten on the source. -/
theorem integral_ddcAdjoint_mul_overlap
    (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n)) (μ : Measure (ComplexModel n))
    [μ.IsAddHaarMeasure] (e f : ComplexChart n M) (η : TestForm (overlapSource e f) q)
    (θ : TestForm (overlapTarget e f) q) (hηθ : OverlapTestRelated e f η θ)
    {φ : ComplexModel n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (chartTransition e f).source) :
    ∫ x, ddcAdjoint B η x * φ x ∂μ =
      ∫ x in (chartTransition e f).source,
        |(chartTransitionDerivative e f x).det| • (ddcAdjoint B θ (chartTransition e f x) *
          φ x) ∂μ := by
  let F := chartTransition e f
  let D := chartTransitionDerivative e f
  let g := transportSymm F φ
  have hg : ContDiff ℝ ∞ g :=
    contDiff_transportSymm F hφ hc hs fun y hy => contDiffAt_chartTransition_symm e f hy
  have hderiv (x : ComplexModel n) (hx : x ∈ F.source) : HasFDerivAt F (D x) x :=
    ((chartTransition_contDiffAt_real e f hx).differentiableAt (by simp)).hasFDerivAt
  have hfullS (k : ComplexModel n → ℝ) (hk : ∀ x ∉ F.source, k x = 0) :
      ∫ x, k x ∂μ = ∫ x in F.source, k x ∂μ := by
    rw [← integral_indicator F.open_source.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ F.source
    · simp [hx]
    · simp [hx, hk x hx]
  have hfullT (k : ComplexModel n → ℝ) (hk : ∀ x ∉ F.target, k x = 0) :
      ∫ x, k x ∂μ = ∫ x in F.target, k x ∂μ := by
    rw [← integral_indicator F.open_target.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ F.target
    · simp [hx]
    · simp [hx, hk x hx]
  calc
    ∫ x, ddcAdjoint (⇑B) η x * φ x ∂μ = ∫ x, ddcDensity B φ η x ∂μ :=
      integral_ddcAdjoint_mul hφ B η
    _ = ∫ x in F.source, ddcDensity B φ η x ∂μ :=
      hfullS _ fun x hx => ddcDensity_eq_zero_of_notMem B φ η hx
    _ = ∫ x in F.source, |(D x).det| • ddcDensity B g θ (F x) ∂μ := by
      refine setIntegral_congr_fun F.open_source.measurableSet fun x hx => ?_
      rw [abs_of_nonneg (GlobalCurrents.chartTransitionDerivative_det_nonneg e f hx),
        smul_eq_mul]
      exact ddcDensity_overlap_pointwise B e f η θ hηθ hg.contDiffOn hx
        (transportSymm_comp_eventuallyEq F φ hx)
    _ = ∫ y in F.target, ddcDensity B g θ y ∂μ :=
      (integral_target_eq_integral_abs_det_fderiv_smul μ hderiv _).symm
    _ = ∫ y, ddcDensity B g θ y ∂μ :=
      (hfullT _ fun y hy => ddcDensity_eq_zero_of_notMem B g θ hy).symm
    _ = ∫ y, ddcAdjoint (⇑B) θ y * g y ∂μ := (integral_ddcAdjoint_mul hg B θ).symm
    _ = ∫ y in F.target, ddcAdjoint (⇑B) θ y * g y ∂μ :=
      hfullT _ fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hy ((ddcAdjoint (⇑B) θ).tsupport_subset h),
          zero_mul]
    _ = ∫ x in F.source, |(D x).det| • (ddcAdjoint (⇑B) θ (F x) * g (F x)) ∂μ :=
      integral_target_eq_integral_abs_det_fderiv_smul μ hderiv _
    _ = _ := by
      refine setIntegral_congr_fun F.open_source.measurableSet fun x hx => ?_
      simp only [g, transportSymm, F.map_source hx, ite_true, F.left_inv hx]
      rfl

/-- The source adjoint test function is almost everywhere on the overlap the
Jacobian-weighted pullback of the target adjoint test function. -/
theorem ddcAdjoint_overlap_ae
    (B : Module.Basis (Fin 2 ⊕ Fin q) ℝ (ComplexModel n)) (μ : Measure (ComplexModel n))
    [μ.IsAddHaarMeasure] (e f : ComplexChart n M) (η : TestForm (overlapSource e f) q)
    (θ : TestForm (overlapTarget e f) q) (hηθ : OverlapTestRelated e f η θ) :
    ∀ᵐ x ∂μ, x ∈ (chartTransition e f).source →
      ddcAdjoint B η x - |(chartTransitionDerivative e f x).det| *
        ddcAdjoint B θ (chartTransition e f x) = 0 := by
  let F := chartTransition e f
  let D := chartTransitionDerivative e f
  let PS : ComplexModel n → ℝ := ddcAdjoint (⇑B) η
  let PR : ComplexModel n → ℝ := ddcAdjoint (⇑B) θ
  have hFsmooth : ContDiffOn ℝ ∞ F F.source := fun y hy =>
    (chartTransition_contDiffAt_real e f hy).contDiffWithinAt
  have hDcont : ContinuousOn (fun x => |(D x).det|) F.source :=
    (continuous_abs.comp ContinuousLinearMap.continuous_det).comp_continuousOn
      (hFsmooth.continuousOn_fderiv_of_isOpen F.open_source (by simp))
  have hJcont : ContinuousOn (fun x => |(D x).det| * PR (F x)) F.source :=
    hDcont.mul ((ddcAdjoint (⇑B) θ).continuous.comp_continuousOn F.continuousOn)
  have hcont : ContinuousOn (fun x => PS x - |(D x).det| * PR (F x)) F.source :=
    (ddcAdjoint (⇑B) η).continuous.continuousOn.sub hJcont
  refine F.open_source.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn F.open_source.measurableSet) fun φ hφ hc hs => ?_
  have hint1 : Integrable (fun x => PS x * φ x) μ :=
    ((ddcAdjoint (⇑B) η).continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hJφcont : Continuous (fun x => (|(D x).det| * PR (F x)) * φ x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ F.source
    · exact ((hJcont x hx).continuousAt (F.open_source.mem_nhds hx)).mul
        hφ.continuous.continuousAt
    · have hxt : x ∉ tsupport φ := fun h => hx (hs h)
      have hev : (fun x => (|(D x).det| * PR (F x)) * φ x) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxt] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
      exact continuousAt_const.congr hev.symm
  have hint2 : Integrable (fun x => (|(D x).det| * PR (F x)) * φ x) μ :=
    hJφcont.integrable_of_hasCompactSupport hc.mul_left
  have hstep := integral_ddcAdjoint_mul_overlap B μ e f η θ hηθ hφ hc hs
  have hfull : ∫ x in F.source, |(D x).det| • (PR (F x) * φ x) ∂μ =
      ∫ x, (|(D x).det| * PR (F x)) * φ x ∂μ := by
    rw [← integral_indicator F.open_source.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ F.source
    · simp [hx, smul_eq_mul, mul_assoc]
    · have hxt : x ∉ tsupport φ := fun h => hx (hs h)
      simp [hx, image_eq_zero_of_notMem_tsupport hxt]
  calc
    ∫ x, φ x • (PS x - |(D x).det| * PR (F x)) ∂μ =
        ∫ x, PS x * φ x ∂μ - ∫ x, (|(D x).det| * PR (F x)) * φ x ∂μ := by
      rw [← integral_sub hint1 hint2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring
    _ = 0 := by
      change ∫ x, ddcAdjoint (⇑B) η x * φ x ∂μ - _ = 0
      rw [hstep, hfull, sub_self]

/-- **Holomorphic overlap compatibility of `ddᶜ` of a chartwise locally
integrable potential.** -/
theorem ddCCurrentFamily_overlap
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (hn : 0 < n) (u : M → EReal) (hu : ChartLocallyIntegrable b u)
    (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) (Module.finrank ℝ (ComplexModel n) - 2))
    (θ : TestForm (overlapTarget e f) (Module.finrank ℝ (ComplexModel n) - 2))
    (h : OverlapTestRelated e f η θ) :
    restrictLocalCurrent (overlapSource_le e f) (ddCCurrentFamily b hn u hu e) η =
      restrictLocalCurrent (overlapTarget_le e f) (ddCCurrentFamily b hn u hu f) θ := by
  let F := chartTransition e f
  let D := chartTransitionDerivative e f
  let B := currentPairingBasis b (degreeTwo hn)
  let ue : ComplexModel n → ℝ := fun z => (chartFunction u e z).toReal
  let uf : ComplexModel n → ℝ := fun z => (chartFunction u f z).toReal
  have hpair (g : ComplexChart n M) (Ω : Opens (ComplexModel n)) (hΩ : Ω ≤ chartTarget g)
      (ζ : TestForm Ω (Module.finrank ℝ (ComplexModel n) - 2)) :
      restrictLocalCurrent hΩ (ddCCurrentFamily b hn u hu g) ζ =
        ∫ x, ddcAdjoint (⇑B) ζ x * (chartFunction u g x).toReal ∂b.addHaar := by
    change wedgePairing B (chartDDC b u g (hu g)) (TestFunction.monoCLM ℝ ζ) = _
    rw [chartDDC, wedgePairing_ddC, regularDistribution_apply]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ddcAdjoint_monoCLM_apply hΩ]
  rw [hpair e _ (overlapSource_le e f), hpair f _ (overlapTarget_le e f)]
  have hderiv (x : ComplexModel n) (hx : x ∈ F.source) : HasFDerivAt F (D x) x :=
    ((chartTransition_contDiffAt_real e f hx).differentiableAt (by simp)).hasFDerivAt
  have hae := ddcAdjoint_overlap_ae B b.addHaar e f η θ h
  have hue (x : ComplexModel n) (hx : x ∈ F.source) : ue x = uf (F x) := by
    have hx' : x ∈ e.val.target ∧ e.val.symm x ∈ f.val.source := by
      simpa [F, chartTransition] using hx
    simp [ue, uf, F, chartFunction, chartTransition, f.val.left_inv hx'.2]
  calc
    ∫ x, ddcAdjoint (⇑B) η x * ue x ∂b.addHaar =
        ∫ x in F.source, ddcAdjoint (⇑B) η x * ue x ∂b.addHaar := by
      rw [← integral_indicator F.open_source.measurableSet]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ F.source
      · simp [hx]
      · have hxt : x ∉ tsupport (ddcAdjoint (⇑B) η) := fun h' =>
          hx ((ddcAdjoint (⇑B) η).tsupport_subset h')
        simp [hx, image_eq_zero_of_notMem_tsupport hxt]
    _ = ∫ x in F.source, |(D x).det| • (ddcAdjoint (⇑B) θ (F x) * uf (F x)) ∂b.addHaar := by
      refine setIntegral_congr_ae F.open_source.measurableSet ?_
      filter_upwards [hae] with x hx hxS
      rw [sub_eq_zero.mp (hx hxS), hue x hxS, smul_eq_mul, mul_assoc]
    _ = ∫ y in F.target, ddcAdjoint (⇑B) θ y * uf y ∂b.addHaar :=
      (integral_target_eq_integral_abs_det_fderiv_smul b.addHaar hderiv
        (fun y => ddcAdjoint (⇑B) θ y * uf y)).symm
    _ = ∫ y, ddcAdjoint (⇑B) θ y * uf y ∂b.addHaar := by
      rw [← integral_indicator F.open_target.measurableSet]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ F.target
      · simp [hy]
      · have hyt : y ∉ tsupport (ddcAdjoint (⇑B) θ) := fun h' =>
          hy ((ddcAdjoint (⇑B) θ).tsupport_subset h')
        simp [hy, image_eq_zero_of_notMem_tsupport hyt]

end Assembly

end SGPT.Foundations.Analysis.Pending.DDCOverlap
