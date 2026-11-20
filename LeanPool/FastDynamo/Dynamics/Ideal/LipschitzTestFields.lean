/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Ideal.VelocityGradient
public import LeanPool.FastDynamo.Dynamics.Ideal.GradientOrthogonality

/-!
# Lipschitz test fields for the weak form of the ideal induction equation

The uniqueness step of the proof of `cor:ideal-growth` (Corollary 4.2) tests a weak solution
against fields `ψ ∘ Φ₋ₛ` that are only Lipschitz, while the weak form `IsIdealWeakSolution`
(`FastDynamo/Dynamics/IdealWeakForm.lean`) is stated against smooth periodic test fields.  This
module extends the weak identity from smooth test fields to fields whose periodic lift is
Lipschitz and differentiable at every point, and proves that the smooth test fields are dense in
`L²(T³; ℂ³)`.

The extension uses Fourier partial sums, not mollification:

* the trigonometric fields `literalTrigField F c = ∑ᵢ ∑_{m ∈ F} c m i e_m eᵢ` are smooth test
  fields (`isIdealTestField_literalTrigField`) with advection
  `(v·∇)(∑ c e_m eᵢ) = ∑ⱼ vⱼ ∑ 2πi mⱼ c e_m eᵢ` at every point
  (`literalAdvection_literalTrigField`);
* their classes, built from the Fourier coefficients of `Φ ∈ L²`, tend to `Φ`
  (`tendsto_toLp_literalTrigField`), whence `dense_idealTestFieldL2`;
* for a Lipschitz, everywhere differentiable lift, integration by parts against characters
  (`integral_conj_mFourier_mul_torusGradient_of_increment`) gives `⟪e_m, (∂ⱼφ)ᵢ⟫ =
  2πi mⱼ ⟪e_m, φᵢ⟫` (`literalFourierCoeff_fderiv`), so the advections of the partial sums of `φ`
  are `∑ⱼ uⱼ` times the partial sums of `∂ⱼφ`, and tend to `(u·∇)φ = ∑ⱼ uⱼ ∂ⱼφ` in `L²`;
* the weak identity with an `L²` test pair passes to limits (`IdealWeakIdentity.of_tendsto`),
  and for a smooth test field it is the integral form of `IsIdealWeakSolution`
  (`idealWeakIdentity_of_isIdealTestField`).

The paper extends the divergence identity to `H¹` test functions "by density" (proof of
`cor:ideal-growth`) and obtains uniqueness of distributional solutions from Ambrosio–Crippa
(Proposition 2.3 there).  The formalised uniqueness argument instead tests a weak solution
against the Lipschitz fields `ψ ∘ Φ₋ₛ`, and uses the extension proved here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-! ## Trigonometric vector fields -/

/-- The phase `a ↦ 2πi m·a` of the character of frequency `m`, as a real-linear form on `ℝ³`. -/
def literalCharPhase (m : Fin 3 → ℤ) : R3 →L[ℝ] ℂ :=
  ∑ j : Fin 3, (2 * Real.pi * Complex.I * (m j : ℂ)) •
    (Complex.ofRealCLM.comp (EuclideanSpace.proj j : R3 →L[ℝ] ℝ))

/-- The value of the phase: `2πi ∑ⱼ mⱼ aⱼ`. -/
theorem literalCharPhase_apply (m : Fin 3 → ℤ) (a : R3) :
    literalCharPhase m a = 2 * Real.pi * Complex.I * ∑ j, (m j : ℂ) * (a j : ℂ) := by
  simp [literalCharPhase, Finset.mul_sum, mul_assoc]

/-- The character of frequency `m` at the class of `a` is the exponential of the phase. -/
theorem mFourier_literalTorusPoint_eq_exp (m : Fin 3 → ℤ) (a : R3) :
    UnitAddTorus.mFourier m (literalTorusPoint a) = Complex.exp (literalCharPhase m a) := by
  rw [mFourier_literalTorusPoint, literalCharPhase_apply]

/-- The vector character `x ↦ e_m(x) e_i` of frequency `m` and direction `i`. -/
def literalCharField (m : Fin 3 → ℤ) (i : Fin 3) : C(Torus 3, C3) :=
  ⟨fun x ↦ UnitAddTorus.mFourier m x • EuclideanSpace.single i (1 : ℂ),
    (UnitAddTorus.mFourier m).continuous.smul continuous_const⟩

/-- The trigonometric vector field `∑_{i} ∑_{m ∈ F} c m i e_m e_i`. -/
def literalTrigField (F : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Fin 3 → ℂ) : C(Torus 3, C3) :=
  ∑ i : Fin 3, ∑ m ∈ F, c m i • literalCharField m i

/-- The lift of a trigonometric field, as an explicit sum of exponentials. -/
theorem literalTrigField_literalTorusPoint (F : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → Fin 3 → ℂ) (a : R3) :
    literalTrigField F c (literalTorusPoint a) =
      ∑ i : Fin 3, ∑ m ∈ F, c m i •
        (Complex.exp (literalCharPhase m a) • EuclideanSpace.single i (1 : ℂ)) := by
  simp [literalTrigField, literalCharField, mFourier_literalTorusPoint_eq_exp]

/-- The derivative of the lift of a trigonometric field. -/
theorem hasFDerivAt_literalTrigField_lift (F : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → Fin 3 → ℂ) (a : R3) :
    HasFDerivAt (fun b : R3 ↦ literalTrigField F c (literalTorusPoint b))
      (∑ i : Fin 3, ∑ m ∈ F, c m i •
        ((Complex.exp (literalCharPhase m a) • literalCharPhase m).smulRight
          (EuclideanSpace.single i (1 : ℂ)))) a := by
  simp_rw [literalTrigField_literalTorusPoint]
  refine HasFDerivAt.fun_sum fun i _ ↦ HasFDerivAt.fun_sum fun m _ ↦ ?_
  exact (((literalCharPhase m).hasFDerivAt.cexp).smul_const
    (EuclideanSpace.single i (1 : ℂ))).const_smul (c m i)

/-- Trigonometric fields are smooth test fields. -/
theorem isIdealTestField_literalTrigField (F : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → Fin 3 → ℂ) : IsIdealTestField (literalTrigField F c) := by
  unfold IsIdealTestField
  simp_rw [literalTrigField_literalTorusPoint]
  refine ContDiff.sum fun i _ ↦ ContDiff.sum fun m _ ↦ ?_
  exact ((Complex.contDiff_exp.comp (literalCharPhase m).contDiff).smul
    (contDiff_const (c := EuclideanSpace.single i (1 : ℂ)))).const_smul (c m i)

/-- **The advection of a trigonometric field** is, at every point, `∑ⱼ vⱼ` times the
trigonometric field with coefficients `2πi mⱼ c m i`. -/
theorem literalAdvection_literalTrigField (v : Torus 3 → R3) (F : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → Fin 3 → ℂ) (x : Torus 3) :
    literalAdvection v (literalTrigField F c) x =
      ∑ j : Fin 3, ((v x j : ℝ) : ℂ) •
        literalTrigField F (fun m i ↦ 2 * Real.pi * Complex.I * (m j : ℂ) * c m i) x := by
  rw [literalAdvection, (hasFDerivAt_literalTrigField_lift F c _).fderiv]
  set a := literalIocRepresentative x
  have hx : x = literalTorusPoint a := (literalTorusPoint_literalIocRepresentative x).symm
  set w := v x
  rw [hx]
  simp_rw [literalTrigField_literalTorusPoint, Finset.smul_sum]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp only [smul_smul, ← Finset.sum_smul, literalCharPhase_apply]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-! ## Fourier partial sums of vector fields -/

/-- The `(m, i)` Fourier coefficient `⟪e_m, Φᵢ⟫` of a vector field `Φ ∈ L²(T³; ℂ³)`. -/
def literalFourierCoeff (Φ : LiteralC3L2) (m : Fin 3 → ℤ) (i : Fin 3) : ℂ :=
  inner ℂ (flatTorus3FourierBasis m) (literalCoordL2 i Φ)

/-- The embedding `f ↦ f eᵢ` of scalar `L²` classes as the `i`-th component. -/
def literalSingleL2 (i : Fin 3) : FlatTorus3ScalarL2 →L[ℂ] LiteralC3L2 :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single i (1 : ℂ))).compLpL 2 volume

/-- The `i`-th component embedding is represented by `x ↦ f(x) eᵢ`. -/
theorem literalSingleL2_coe_ae (i : Fin 3) (f : FlatTorus3ScalarL2) :
    (literalSingleL2 i f : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ (f : Torus 3 → ℂ) x • EuclideanSpace.single i (1 : ℂ) :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single i (1 : ℂ))).coeFn_compLpL f

/-- A sum of three classes is represented by the sum of representatives. -/
theorem literalC3L2_coeFn_sum (f : Fin 3 → LiteralC3L2) :
    (⇑(∑ j : Fin 3, f j) : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ ∑ j : Fin 3, (f j : Torus 3 → C3) x := by
  rw [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (f 0 + f 1) (f 2), Lp.coeFn_add (f 0) (f 1)] with x h h'
  rw [h, Pi.add_apply, h', Pi.add_apply, Fin.sum_univ_three]

/-- A vector field is the sum of its components, each embedded in its direction. -/
theorem sum_literalSingleL2_literalCoordL2 (Φ : LiteralC3L2) :
    ∑ i : Fin 3, literalSingleL2 i (literalCoordL2 i Φ) = Φ := by
  refine Lp.ext ?_
  filter_upwards [literalC3L2_coeFn_sum fun i ↦ literalSingleL2 i (literalCoordL2 i Φ),
    ae_all_iff.2 fun i ↦ literalSingleL2_coe_ae i (literalCoordL2 i Φ),
    ae_all_iff.2 fun i ↦ literalCoordL2_coe_ae i Φ] with x h h1 h2
  rw [h]
  simp_rw [h1, h2]
  ext j
  simp [Pi.single_apply]

/-- The class of the vector character `e_m eᵢ` is the embedded basis vector `e_m`. -/
theorem toLp_literalCharField (m : Fin 3 → ℤ) (i : Fin 3) :
    ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ (literalCharField m i) =
      literalSingleL2 i (flatTorus3FourierBasis m) := by
  refine Lp.ext ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure (Torus 3))
      (literalCharField m i), literalSingleL2_coe_ae i (flatTorus3FourierBasis m),
    flatTorus3FourierBasis_coe_ae m] with x h1 h2 h3
  rw [h1, h2, h3]
  rfl

/-- The class of a trigonometric field, in terms of the scalar Fourier basis. -/
theorem toLp_literalTrigField (F : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Fin 3 → ℂ) :
    ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ (literalTrigField F c) =
      ∑ i : Fin 3, literalSingleL2 i (∑ m ∈ F, c m i • flatTorus3FourierBasis m) := by
  simp only [literalTrigField, map_sum, map_smul, toLp_literalCharField]

/-- **Fourier partial sums converge**: the classes of the trigonometric fields built from the
Fourier coefficients of `Φ` over the finite sets of frequencies tend to `Φ`. -/
theorem tendsto_toLp_literalTrigField (Φ : LiteralC3L2) :
    Tendsto (fun F : Finset (Fin 3 → ℤ) ↦ ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ
      (literalTrigField F (literalFourierCoeff Φ))) atTop (𝓝 Φ) := by
  simp_rw [toLp_literalTrigField]
  conv => arg 3; rw [← sum_literalSingleL2_literalCoordL2 Φ]
  refine tendsto_finsetSum _ fun i _ ↦ ((literalSingleL2 i).continuous.tendsto _).comp ?_
  have h := flatTorus3FourierBasis.hasSum_repr (literalCoordL2 i Φ)
  simp only [HilbertBasis.repr_apply_apply] at h
  exact h

/-- The class of a trigonometric field is its class as a continuous map. -/
theorem memLp_toLp_literalTrigField (F : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Fin 3 → ℂ)
    (hφ : MemLp (literalTrigField F c) 2 (volume : Measure (Torus 3))) :
    hφ.toLp _ = ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ (literalTrigField F c) :=
  Lp.ext ((MemLp.coeFn_toLp _).trans (ContinuousMap.coeFn_toLp _ _).symm)

/-- **Smooth test fields are dense in `L²(T³; ℂ³)`.** -/
theorem dense_idealTestFieldL2 :
    Dense {f : LiteralC3L2 | ∃ φ : Torus 3 → C3, IsIdealTestField φ ∧
      ∃ hφ : MemLp φ 2 (volume : Measure (Torus 3)), f = hφ.toLp φ} := by
  intro Φ
  refine mem_closure_of_tendsto (tendsto_toLp_literalTrigField Φ) (Eventually.of_forall fun F ↦ ?_)
  have hmem := (Lp.memLp (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ
    (literalTrigField F (literalFourierCoeff Φ)))).ae_eq (ContinuousMap.coeFn_toLp _ _)
  exact ⟨_, isIdealTestField_literalTrigField _ _, hmem,
    (memLp_toLp_literalTrigField _ _ hmem).symm⟩

/-! ## Fields with a Lipschitz, everywhere differentiable lift -/

/-- The `i`-th component of a field `φ` whose lift is Lipschitz has axis increments bounded by
the Lipschitz constant. -/
theorem exists_axis_increment_bound_of_lipschitz {φ : Torus 3 → C3} {K : ℝ≥0}
    (hlip : LipschitzWith K fun a : R3 ↦ φ (literalTorusPoint a)) (i : Fin 3) :
    ∃ C : ℝ, ∀ (x : Torus 3) (j : Fin 3) (t : ℝ), |t| ≤ 1 →
      ‖φ (x + torusAxisShift j t) i - φ x i‖ ≤ C * |t| := by
  refine ⟨K, fun x j t _ ↦ ?_⟩
  set a := literalIocRepresentative x
  have hx : x = literalTorusPoint a := (literalTorusPoint_literalIocRepresentative x).symm
  rw [hx, ← literalTorusPoint_add_single, ← PiLp.sub_apply]
  refine (PiLp.norm_apply_le _ i).trans ?_
  have := hlip.norm_sub_le (a + EuclideanSpace.single j t) a
  have hn : ‖(EuclideanSpace.single j t : R3)‖ = |t| := by simp
  rwa [add_sub_cancel_left, hn] at this

/-- **Fourier coefficients of a partial derivative of a Lipschitz field**: if the lift of `φ`
is Lipschitz and differentiable everywhere, the `(m, i)` coefficient of `∂ⱼφ` is `2πi mⱼ` times
that of `φ`. -/
theorem literalFourierCoeff_fderiv {φ : Torus 3 → C3}
    (hdiff : Differentiable ℝ fun a : R3 ↦ φ (literalTorusPoint a)) {K : ℝ≥0}
    (hlip : LipschitzWith K fun a : R3 ↦ φ (literalTorusPoint a))
    (hφ : MemLp φ 2 (volume : Measure (Torus 3))) (j : Fin 3)
    (hD : MemLp (fun x ↦ fderiv ℝ (fun a : R3 ↦ φ (literalTorusPoint a))
      (literalIocRepresentative x) (EuclideanSpace.single j 1)) 2 (volume : Measure (Torus 3)))
    (m : Fin 3 → ℤ) (i : Fin 3) :
    literalFourierCoeff (hD.toLp _) m i =
      2 * Real.pi * Complex.I * (m j : ℂ) * literalFourierCoeff (hφ.toLp φ) m i := by
  set pr : C3 →L[ℝ] ℂ := (EuclideanSpace.proj i : C3 →L[ℂ] ℂ).restrictScalars ℝ
  have hlift : torusLift (fun x ↦ φ x i) = fun a ↦ pr (φ (literalTorusPoint a)) := rfl
  have hwd : Differentiable ℝ (torusLift fun x ↦ φ x i) := by
    rw [hlift]
    exact pr.differentiable.comp hdiff
  have hgrad : ∀ x, torusGradient (fun x ↦ φ x i) x j =
      fderiv ℝ (fun a : R3 ↦ φ (literalTorusPoint a)) (literalIocRepresentative x)
        (EuclideanSpace.single j 1) i := by
    intro x
    have hd : HasFDerivAt (fun a ↦ pr (φ (literalTorusPoint a)))
        (pr.comp (fderiv ℝ (fun a : R3 ↦ φ (literalTorusPoint a)) (literalIocRepresentative x)))
        (literalIocRepresentative x) := pr.hasFDerivAt.comp _ (hdiff _).hasFDerivAt
    rw [torusGradient, hlift, hd.fderiv]
    rfl
  have hibp := integral_conj_mFourier_mul_torusGradient_of_increment hwd
    (exists_axis_increment_bound_of_lipschitz hlip i) m j
  rw [literalFourierCoeff, literalFourierCoeff, inner_flatTorus3FourierBasis,
    inner_flatTorus3FourierBasis]
  have h1 : (∫ x, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
      (literalCoordL2 i (hD.toLp _) : Torus 3 → ℂ) x) =
      ∫ x, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * torusGradient (fun x ↦ φ x i) x j := by
    refine integral_congr_ae ?_
    filter_upwards [literalCoordL2_coe_ae i (hD.toLp _), hD.coeFn_toLp] with x h1 h2
    rw [h1, h2, hgrad]
  have h2 : (∫ x, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) *
      (literalCoordL2 i (hφ.toLp φ) : Torus 3 → ℂ) x) =
      ∫ x, (starRingEnd ℂ) (UnitAddTorus.mFourier m x) * φ x i := by
    refine integral_congr_ae ?_
    filter_upwards [literalCoordL2_coe_ae i (hφ.toLp φ), hφ.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  rw [h1, h2, hibp]

/-! ## The weak identity with `L²` test pairs is closed -/

/-- With `W` continuous on `[s, t]`, the time integral of the weak identity is a pairing with the
time integrals of `W` and of its stretching. -/
theorem idealWeakIdentity_iff {v : Torus 3 → R3} {W : ℝ → LiteralC3L2} {s t : ℝ}
    (hW : ContinuousOn W (Set.uIcc s t)) (φ ψ : LiteralC3L2) :
    IdealWeakIdentity v W s t φ ψ ↔
      inner ℂ φ (W t) - inner ℂ φ (W s) =
        inner ℂ φ (∫ τ in s..t, literalStretchL2 v (W τ)) + inner ℂ ψ (∫ τ in s..t, W τ) := by
  have hA : IntervalIntegrable (fun τ ↦ literalStretchL2 v (W τ)) volume s t :=
    ((literalStretchL2 v).continuous.comp_continuousOn hW).intervalIntegrable
  have hW' : IntervalIntegrable W volume s t := hW.intervalIntegrable
  have h1 : IntervalIntegrable (fun τ ↦ inner ℂ φ (literalStretchL2 v (W τ))) volume s t :=
    ((innerSL ℂ φ).continuous.comp_continuousOn
      ((literalStretchL2 v).continuous.comp_continuousOn hW)).intervalIntegrable
  have h2 : IntervalIntegrable (fun τ ↦ inner ℂ ψ (W τ)) volume s t :=
    ((innerSL ℂ ψ).continuous.comp_continuousOn hW).intervalIntegrable
  have e1 := (innerSL ℂ φ).intervalIntegral_comp_comm hA
  have e2 := (innerSL ℂ ψ).intervalIntegral_comp_comm hW'
  simp only [innerSL_apply_apply] at e1 e2
  rw [IdealWeakIdentity, intervalIntegral.integral_add h1 h2, e1, e2]

/-- **The weak identity passes to limits of test pairs** in `L² × L²`. -/
theorem IdealWeakIdentity.of_tendsto {v : Torus 3 → R3} {W : ℝ → LiteralC3L2} {s t : ℝ}
    (hW : ContinuousOn W (Set.uIcc s t)) {ι : Type*} {l : Filter ι} [l.NeBot]
    {φ ψ : ι → LiteralC3L2} {φ₀ ψ₀ : LiteralC3L2} (hφ : Tendsto φ l (𝓝 φ₀))
    (hψ : Tendsto ψ l (𝓝 ψ₀)) (h : ∀ᶠ k in l, IdealWeakIdentity v W s t (φ k) (ψ k)) :
    IdealWeakIdentity v W s t φ₀ ψ₀ := by
  rw [idealWeakIdentity_iff hW]
  refine tendsto_nhds_unique_of_eventuallyEq
    ((hφ.inner tendsto_const_nhds).sub (hφ.inner tendsto_const_nhds))
    ((hφ.inner tendsto_const_nhds).add (hψ.inner tendsto_const_nhds)) ?_
  filter_upwards [h] with k hk
  exact (idealWeakIdentity_iff hW _ _).1 hk

/-! ## The weak identity at the velocity of the paper -/

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- For a smooth test field the integral form of the weak identity is the weak identity with
the `L²` test pair `(φ, (u·∇)φ)`. -/
theorem idealWeakIdentity_of_isIdealTestField (htau : 0 ≤ tau) {T : ℝ}
    {W : ℝ → LiteralC3L2} (hW : IsIdealWeakSolution (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) T W)
    {φ : Torus 3 → C3} (hφt : IsIdealTestField φ) (hφ : MemLp φ 2 volume)
    (hadv : MemLp (literalAdvection (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) φ) 2 volume)
    {s t : ℝ} (hs : s ∈ Set.Icc (-T) T) (ht : t ∈ Set.Icc (-T) T) :
    IdealWeakIdentity (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) W s t
      (hφ.toLp φ) (hadv.toLp _) := by
  have hpair : ∀ X : LiteralC3L2,
      inner ℂ (hφ.toLp φ) X = ∫ x, inner ℂ (φ x) ((X : Torus 3 → C3) x) := fun X ↦ by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hφ.coeFn_toLp] with x hx
    rw [hx]
  have hτ : ∀ τ : ℝ, (∫ x, (inner ℂ (φ x) (literalStretch (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
        (W τ : Torus 3 → C3) x) +
      inner ℂ (literalAdvection (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) φ x)
        ((W τ : Torus 3 → C3) x))) =
      inner ℂ (hφ.toLp φ) (literalStretchL2 (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) (W τ)) +
        inner ℂ (hadv.toLp _) (W τ) := by
    intro τ
    rw [L2.inner_def, L2.inner_def, ← integral_add (L2.integrable_inner _ _)
      (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [hφ.coeFn_toLp, hadv.coeFn_toLp,
      literalStretchL2_coe_ae h P angularSpeed axialSpeed tau htau (W τ)] with x h1 h2 h3
    rw [h1, h2, h3]
  have hweak := hW.weak φ hφt s hs t ht
  simp_rw [hτ] at hweak
  rw [IdealWeakIdentity, hpair, hpair, hweak]

/-- **The weak identity for Lipschitz test fields.**  If `W` is a weak solution on `[−T, T]` and
the lift of `φ` is Lipschitz and differentiable everywhere, then `W` satisfies the weak identity
with the `L²` test pair `(φ, (u·∇)φ)`.  The trigonometric partial sums of `φ` are smooth test
fields; their classes tend to `φ`, and (by integration by parts against characters) their
advections tend to `(u·∇)φ = ∑ⱼ uⱼ ∂ⱼφ`. -/
theorem IsIdealWeakSolution.weakIdentity_of_lipschitz (htau : 0 ≤ tau) {T : ℝ}
    {W : ℝ → LiteralC3L2} (hW : IsIdealWeakSolution (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) T W)
    {φ : Torus 3 → C3} (hdiff : Differentiable ℝ fun a : R3 ↦ φ (literalTorusPoint a))
    {K : ℝ≥0} (hlip : LipschitzWith K fun a : R3 ↦ φ (literalTorusPoint a))
    (hφ : MemLp φ 2 volume) (hadv : MemLp (literalAdvection (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) φ) 2 volume)
    {s t : ℝ} (hs : s ∈ Set.Icc (-T) T) (ht : t ∈ Set.Icc (-T) T) :
    IdealWeakIdentity (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) W s t
      (hφ.toLp φ) (hadv.toLp _) := by
  set u := literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
  -- the velocity is bounded and measurable
  set U : R3 → R3 := fun b ↦ u (literalTorusPoint b)
  have hUc : Continuous U :=
    (differentiable_literalVelocity_lift h P angularSpeed axialSpeed tau htau).continuous
  have huU : ∀ x, u x = U (literalIocRepresentative x) := fun x ↦ by
    simp only [U, literalTorusPoint_literalIocRepresentative]
  have hum : Measurable u := by
    rw [funext huU]
    exact hUc.measurable.comp measurable_literalIocRepresentative
  obtain ⟨Mu, hMu⟩ := exists_bound_comp_literalIocRepresentative hUc
  -- multiplication by the components of the velocity
  have hΛ : ∀ j : Fin 3, MemLp (fun x ↦ ((u x j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ C3) ∞
      (volume : Measure (Torus 3)) := by
    intro j
    refine memLp_top_of_bound ?_ Mu (Eventually.of_forall fun x ↦ ?_)
    · have hG : Continuous fun y : R3 ↦ ((y j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ C3 := by
        fun_prop
      exact hG.comp_aestronglyMeasurable hum.aestronglyMeasurable
    · calc ‖((u x j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ C3‖
          ≤ ‖((u x j : ℝ) : ℂ)‖ * ‖ContinuousLinearMap.id ℂ C3‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ ‖u x‖ * 1 := by
          refine mul_le_mul ?_ ContinuousLinearMap.norm_id_le (norm_nonneg _) (norm_nonneg _)
          rw [Complex.norm_real]
          exact PiLp.norm_apply_le (u x) j
        _ ≤ Mu := by rw [mul_one, huU]; exact hMu x
  set M : Fin 3 → LiteralC3L2 →L[ℂ] LiteralC3L2 :=
    fun j ↦ operatorMulL2 (volume : Measure (Torus 3)) ((hΛ j).toLp _)
  have hM : ∀ (j : Fin 3) (X : LiteralC3L2), (M j X : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ ((u x j : ℝ) : ℂ) • (X : Torus 3 → C3) x := by
    intro j X
    filter_upwards [operatorMulL2_coe_ae (volume : Measure (Torus 3)) ((hΛ j).toLp _) X,
      (hΛ j).coeFn_toLp] with x h1 h2
    rw [h1, h2]
    rfl
  -- the partial derivatives of `φ`
  have hD : ∀ j : Fin 3, MemLp (fun x ↦ fderiv ℝ (fun a : R3 ↦ φ (literalTorusPoint a))
      (literalIocRepresentative x) (EuclideanSpace.single j 1)) 2 (volume : Measure (Torus 3)) := by
    intro j
    refine MemLp.of_bound ((measurable_fderiv_apply_const ℝ _ _).comp
      measurable_literalIocRepresentative).aestronglyMeasurable K
      (Eventually.of_forall fun x ↦ ?_)
    refine ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    have hn : ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ = 1 := by simp
    rw [hn, mul_one]
    exact norm_fderiv_le_of_lipschitz ℝ hlip
  set D : Fin 3 → LiteralC3L2 := fun j ↦ (hD j).toLp _
  -- the approximants and their advections
  set Φ := hφ.toLp φ
  set A : Finset (Fin 3 → ℤ) → LiteralC3L2 := fun F ↦ ∑ j : Fin 3, M j
    (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ
      (literalTrigField F (literalFourierCoeff (D j))))
  have hcoeff : ∀ j : Fin 3, (fun m i ↦ 2 * Real.pi * Complex.I * (m j : ℂ) *
      literalFourierCoeff Φ m i) = literalFourierCoeff (D j) := fun j ↦ by
    funext m i
    exact (literalFourierCoeff_fderiv hdiff hlip hφ j (hD j) m i).symm
  have hadvF : ∀ F : Finset (Fin 3 → ℤ),
      literalAdvection u (literalTrigField F (literalFourierCoeff Φ)) =ᵐ[volume]
        (A F : Torus 3 → C3) := by
    intro F
    filter_upwards [literalC3L2_coeFn_sum fun j ↦ M j (ContinuousMap.toLp 2
        (volume : Measure (Torus 3)) ℂ (literalTrigField F (literalFourierCoeff (D j)))),
      ae_all_iff.2 fun j ↦ hM j (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ
        (literalTrigField F (literalFourierCoeff (D j)))),
      ae_all_iff.2 fun j ↦ ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
        (volume : Measure (Torus 3)) (literalTrigField F (literalFourierCoeff (D j)))]
      with x h1 h2 h3
    rw [h1, literalAdvection_literalTrigField]
    simp_rw [h2, h3, hcoeff]
  have hlimit : ∑ j : Fin 3, M j (D j) = hadv.toLp _ := by
    refine Lp.ext ?_
    filter_upwards [literalC3L2_coeFn_sum fun j ↦ M j (D j), ae_all_iff.2 fun j ↦ hM j (D j),
      ae_all_iff.2 fun j ↦ (show (D j : Torus 3 → C3) =ᵐ[volume] _ from (hD j).coeFn_toLp),
      hadv.coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h4]
    simp_rw [h2, h3]
    conv_rhs => rw [literalAdvection, ← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (u x)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [← hlimit]
  refine IdealWeakIdentity.of_tendsto (hW.continuousOn.mono (Set.uIcc_subset_Icc hs ht))
    (tendsto_toLp_literalTrigField Φ)
    (tendsto_finsetSum _ fun j _ ↦ ((M j).continuous.tendsto _).comp
      (tendsto_toLp_literalTrigField (D j)))
    (Eventually.of_forall fun F ↦ ?_)
  have hmemF : MemLp (literalTrigField F (literalFourierCoeff Φ)) 2 volume :=
    (Lp.memLp _).ae_eq (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
      (volume : Measure (Torus 3)) _)
  have hmemA : MemLp (literalAdvection u (literalTrigField F (literalFourierCoeff Φ))) 2 volume :=
    (Lp.memLp (A F)).ae_eq (hadvF F).symm
  have hF := idealWeakIdentity_of_isIdealTestField h P angularSpeed axialSpeed tau htau hW
    (isIdealTestField_literalTrigField _ _) hmemF hmemA hs ht
  rw [memLp_toLp_literalTrigField, MemLp.toLp_congr hmemA (Lp.memLp _) (hadvF F),
    Lp.toLp_coeFn] at hF
  exact hF

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
