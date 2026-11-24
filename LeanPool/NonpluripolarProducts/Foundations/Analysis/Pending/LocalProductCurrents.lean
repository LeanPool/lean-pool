/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.StronglyPositiveForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ProductTestForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveDistributionMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.TopDegreeDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HermitianGeometry
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Upstream.KahlerClosed
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothCutoff

/-!
# Local currents of bidimension `(q,q)` against constant product forms

Let `U ⊆ ℂⁿ` be open.  A real current of bidimension `(q,q)` on `U` acts on the compactly
supported smooth real `(q,q)`-forms.  Every such form is a finite sum `∑ₖ φₖ γₖ` of a scalar test
function `φₖ` times a CONSTANT real `(q,q)`-form `γₖ`, so the current is the same as the linear map
`γ ↦ T(γ)` from the constant forms to the scalar distributions on `U`, `T(γ)(φ) = ⟨T, φ γ⟩`
(`LocalProductCurrent U q`).  The constant real `(q,q)`-forms are taken to be the real span
`Λ_q = span (spCone q)` of the strongly positive cone (`formSpan q`; by the basis theorem
`demailly-cadg:III.1.4` this is the space of all real `(q,q)`-forms, which is NOT formalized and
not used here: everything below is stated for `Λ_q` itself).

A current is *positive* (`IsPositive`, `demailly-cadg:III.1.13`, weak positivity) when
`∑ₖ T(γₖ)(φₖ) ≥ 0` whenever the variable test form `x ↦ ∑ₖ φₖ(x) γₖ` is strongly positive at every
point.  This is the positivity of the blueprint (`bt:recursive-product`), on variable test forms.

## Main results

* `formSpan`, `oneOne_mem_formSpan`, `wedge_mem_formSpan` — real `(1,1)`-forms lie in `Λ₁`, and the
  exterior product maps `Λ_q × (1,1)` into `Λ_{q+1}`; `wedgeLM` is the induced linear map.
* `exists_orderUnit` — the power `ω₀^q` of the standard Kähler form `ω₀(u,v) = Im⟨u,v⟩` is an order
  unit: for `γ ∈ Λ_q` there is `C ≥ 0` with `C ω₀^q ± γ` strongly positive.
* `LocalProductCurrent`, `IsPositive` (with `add`, `smul`, `zero`), `traceDistribution`
  (`T(ω₀^q)`, a positive distribution for positive `T`).
* **Order zero** — `IsPositive.exists_density`: a positive current has a regular locally finite
  trace measure `σ_T` on `U` (the Riesz measure of `T(ω₀^q)`), and every coefficient `T(γ)` is
  integration against `f_γ σ_T` for a measurable density with `|f_γ| ≤ C` (the order-unit constant
  of `γ`).  So `|T(γ)| ≤ C T(ω₀^q)`: the coefficients are signed Radon measures dominated by the
  trace measure (`demailly-cadg:III.1.14`).
* `IsPositive.traceMeasure`, `IsPositive.density`, `IsPositive.apply_eq_integral_density`
  (`T(γ)(φ) = ∫ φ f_γ dσ_T`), `IsPositive.density_add_ae`, `IsPositive.density_smul_ae`,
  `IsPositive.ae_eq_of_forall_integral_eq` (densities are determined by the distribution).
* **Multiplication by a locally bounded Borel function** — `mulBorel T u`, `mulBorel_apply`
  (`(u T)(γ) = u f_γ σ_T`), `mulBorel_const`, `mulBorel_add`, and for `u` smooth near the
  support of `φ`, `IsPositive.apply_smoothMulTest` (`(u T)(γ)(φ) = T(γ)(u φ)`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions CompactlySupported NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalProductCurrents

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms

variable {n : ℕ}

/-! ### Constant real `(q,q)`-forms -/

section Constant

variable (n) in
/-- The constant real `(q,q)`-forms: the real span of the strongly positive cone. -/
def formSpan (q : ℕ) : Submodule ℝ (RealForm n (2 * q)) :=
  Submodule.span ℝ (spCone (n := n) q : Set (RealForm n (2 * q)))

theorem mem_formSpan_of_mem_spCone {q : ℕ} {P : RealForm n (2 * q)} (hP : P ∈ spCone q) :
    P ∈ formSpan n q :=
  Submodule.subset_span hP

variable (n) in
/-- The standard Kähler form of `ℂⁿ`, `ω₀(u, v) = Im ⟨u, v⟩`, so `ω₀(v, i v) = ‖v‖²`. -/
def kahlerForm : RealForm n 2 := Kahler.fundamentalFormAlt

theorem kahlerForm_apply_I (v : ComplexModel n) :
    kahlerForm n ![v, Complex.I • v] = ‖v‖ ^ 2 := by
  simp only [kahlerForm, Kahler.fundamentalFormAlt_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact Kahler.fundamentalForm_complexStructure_self v

theorem isSemipositiveOneOne_kahlerForm : IsSemipositiveOneOne (kahlerForm n) := by
  refine ⟨flatFundamentalForm_isOneOne n, fun v => ?_⟩
  rw [kahlerForm_apply_I]
  positivity

/-- Every real `(1,1)`-form is bounded by a multiple of `ω₀`: `K ω₀ ± β` are semipositive for
`K = ‖β‖`. -/
theorem isSemipositiveOneOne_norm_smul_kahlerForm {β : RealForm n 2} (hβ : IsOneOne β) :
    IsSemipositiveOneOne (‖β‖ • kahlerForm n - β) ∧
      IsSemipositiveOneOne (‖β‖ • kahlerForm n + β) := by
  have hω := flatFundamentalForm_isOneOne n
  have hbound : ∀ v : ComplexModel n, |β ![v, Complex.I • v]| ≤ ‖β‖ * ‖v‖ ^ 2 := by
    intro v
    have h := β.le_opNorm ![v, Complex.I • v]
    rw [Fin.prod_univ_two] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_smul,
      Complex.norm_I, one_mul, Real.norm_eq_abs] at h
    nlinarith [h]
  refine ⟨⟨fun u v => ?_, fun v => ?_⟩, ⟨fun u v => ?_, fun v => ?_⟩⟩
  · simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rw [show kahlerForm n = Kahler.fundamentalFormAlt from rfl, hω u v, hβ u v]
  · simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, kahlerForm_apply_I]
    have := hbound v
    rw [abs_le] at this
    linarith [this.2]
  · simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rw [show kahlerForm n = Kahler.fundamentalFormAlt from rfl, hω u v, hβ u v]
  · simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, kahlerForm_apply_I]
    have := hbound v
    rw [abs_le] at this
    linarith [this.1]

/-- `1 ∧ β = β` for a two-form, in the degree `2 * 1` used by `spCone`. -/
theorem coordinateWedge_unit_eq (β : RealForm n 2) :
    (coordinateWedge (coordinateWedgeUnit : RealForm n 0) β : RealForm n (2 * 1)) = β := by
  ext v
  rw [TopDegreeDensity.coordinateWedge_unit_apply]
  rfl

/-- A semipositive real `(1,1)`-form is strongly positive of degree one. -/
theorem mem_spCone_one {β : RealForm n 2} (hβ : IsSemipositiveOneOne β) :
    (β : RealForm n (2 * 1)) ∈ spCone (n := n) 1 := by
  have h := wedge_mem_spCone (unit_mem_spCone (n := n)) hβ
  rwa [coordinateWedge_unit_eq] at h

/-- Every real `(1,1)`-form is a constant `(1,1)`-form in the sense of `formSpan`. -/
theorem oneOne_mem_formSpan {β : RealForm n 2} (hβ : IsOneOne β) :
    (β : RealForm n (2 * 1)) ∈ formSpan n 1 := by
  obtain ⟨h₁, h₂⟩ := isSemipositiveOneOne_norm_smul_kahlerForm hβ
  have e : β = (1 / 2 : ℝ) • ((‖β‖ • kahlerForm n + β) - (‖β‖ • kahlerForm n - β)) := by
    module
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mem_formSpan_of_mem_spCone (mem_spCone_one
    h₂))
    (mem_formSpan_of_mem_spCone (mem_spCone_one h₁)))

/-- The exterior product maps `Λ_q × (1,1)`-forms into `Λ_{q+1}`. -/
theorem wedge_mem_formSpan {q : ℕ} {γ : RealForm n (2 * q)} (hγ : γ ∈ formSpan n q)
    {β : RealForm n 2} (hβ : IsOneOne β) :
    coordinateWedge γ β ∈ formSpan n (q + 1) := by
  obtain ⟨h₁, h₂⟩ := isSemipositiveOneOne_norm_smul_kahlerForm hβ
  have hpos : ∀ P ∈ spCone (n := n) q, ∀ β' : RealForm n 2, IsSemipositiveOneOne β' →
      coordinateWedge P β' ∈ formSpan n (q + 1) := fun P hP β' hβ' =>
    mem_formSpan_of_mem_spCone (wedge_mem_spCone hP hβ')
  have hβe : β = (1 / 2 : ℝ) • ((‖β‖ • kahlerForm n + β) - (‖β‖ • kahlerForm n - β)) := by
    module
  have hgen : ∀ P ∈ spCone (n := n) q, coordinateWedge P β ∈ formSpan n (q + 1) := by
    intro P hP
    rw [hβe, ← wedgeBilin_apply, map_smul, map_sub, wedgeBilin_apply, wedgeBilin_apply]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hpos P hP _ h₂) (hpos P hP _ h₁))
  induction hγ using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero =>
    rw [← wedgeBilin_apply, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [← wedgeBilin_apply, map_add, LinearMap.add_apply, wedgeBilin_apply, wedgeBilin_apply]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← wedgeBilin_apply, map_smul, LinearMap.smul_apply, wedgeBilin_apply]
    exact Submodule.smul_mem _ _ hx

/-- The wedge with a real `(1,1)`-form, as a linear map `Λ_q → Λ_{q+1}`. -/
def wedgeLM (q : ℕ) {β : RealForm n 2} (hβ : IsOneOne β) :
    formSpan n q →ₗ[ℝ] formSpan n (q + 1) where
  toFun γ := ⟨coordinateWedge (γ : RealForm n (2 * q)) β, wedge_mem_formSpan γ.2 hβ⟩
  map_add' γ γ' := by
    ext1
    simp only [Submodule.coe_add, ← wedgeBilin_apply, map_add, LinearMap.add_apply]
  map_smul' c γ := by
    ext1
    simp only [Submodule.coe_smul, ← wedgeBilin_apply, map_smul, LinearMap.smul_apply,
      RingHom.id_apply]

@[simp] theorem coe_wedgeLM_apply (q : ℕ) {β : RealForm n 2} (hβ : IsOneOne β)
    (γ : formSpan n q) :
    (wedgeLM q hβ γ : RealForm n (2 * (q + 1))) = coordinateWedge (γ : RealForm n (2 * q)) β :=
  rfl

/-- The forms `P` with `C ω₀^q ± P` strongly positive for some `C` form a submodule. -/
def orderUnitSubmodule (q : ℕ) : Submodule ℝ (RealForm n (2 * q)) where
  carrier := {P | ∃ C : ℝ, C • formPower (kahlerForm n) q - P ∈ spCone q ∧
    C • formPower (kahlerForm n) q + P ∈ spCone q}
  add_mem' := by
    rintro P P' ⟨C, h₁, h₂⟩ ⟨C', h₁', h₂'⟩
    refine ⟨C + C', ?_, ?_⟩
    · have := (spCone (n := n) q).add_mem h₁ h₁'
      convert this using 1
      module
    · have := (spCone (n := n) q).add_mem h₂ h₂'
      convert this using 1
      module
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro c P ⟨C, h₁, h₂⟩
    rcases le_total 0 c with hc | hc
    · refine ⟨c * C, ?_, ?_⟩
      · have := smul_mem_spCone h₁ hc
        convert this using 1
        module
      · have := smul_mem_spCone h₂ hc
        convert this using 1
        module
    · have hc' : 0 ≤ -c := neg_nonneg.mpr hc
      refine ⟨-c * C, ?_, ?_⟩
      · have := smul_mem_spCone h₂ hc'
        convert this using 1
        module
      · have := smul_mem_spCone h₁ hc'
        convert this using 1
        module

theorem spCone_le_orderUnitSubmodule :
    ∀ q : ℕ, ∀ P ∈ spCone (n := n) q, P ∈ orderUnitSubmodule (n := n) q
  | 0, P, hP => by
    induction hP using Submodule.span_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨1, ?_, ?_⟩
      · simp
      · have := smul_mem_spCone (unit_mem_spCone (n := n)) (show (0 : ℝ) ≤ 2 by norm_num)
        convert this using 1
        rw [formPower_zero]
        module
    | zero => exact (orderUnitSubmodule 0).zero_mem
    | add x y _ _ hx hy => exact (orderUnitSubmodule 0).add_mem hx hy
    | smul a x _ hx => exact (orderUnitSubmodule 0).smul_mem (a : ℝ) hx
  | q + 1, P, hP => by
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Q, hQ, β, hβ, rfl⟩ := hx
      obtain ⟨C, h₁, h₂⟩ := spCone_le_orderUnitSubmodule q Q hQ
      obtain ⟨k₁, k₂⟩ := isSemipositiveOneOne_norm_smul_kahlerForm hβ.1
      exact ⟨C * ‖β‖, (orderUnit_step h₁ h₂ k₁ k₂).1, (orderUnit_step h₁ h₂ k₁ k₂).2⟩
    | zero => exact (orderUnitSubmodule (q + 1)).zero_mem
    | add x y _ _ hx hy => exact (orderUnitSubmodule (q + 1)).add_mem hx hy
    | smul a x _ hx => exact (orderUnitSubmodule (q + 1)).smul_mem (a : ℝ) hx

/-- **`ω₀^q` is an order unit of `Λ_q`.** -/
theorem exists_orderUnit {q : ℕ} {γ : RealForm n (2 * q)} (hγ : γ ∈ formSpan n q) :
    ∃ C : ℝ, 0 ≤ C ∧ C • formPower (kahlerForm n) q - γ ∈ spCone q ∧
      C • formPower (kahlerForm n) q + γ ∈ spCone q := by
  have hle : formSpan n q ≤ orderUnitSubmodule q :=
    Submodule.span_le.mpr fun P hP => spCone_le_orderUnitSubmodule q P hP
  obtain ⟨C, h₁, h₂⟩ := hle hγ
  have hω : formPower (kahlerForm n) q ∈ spCone q :=
    formPower_mem_spCone isSemipositiveOneOne_kahlerForm q
  refine ⟨max C 0, le_max_right _ _, ?_, ?_⟩
  · have := (spCone (n := n) q).add_mem h₁ (smul_mem_spCone hω (sub_nonneg.mpr (le_max_left C 0)))
    convert this using 1
    module
  · have := (spCone (n := n) q).add_mem h₂ (smul_mem_spCone hω (sub_nonneg.mpr (le_max_left C 0)))
    convert this using 1
    module

theorem formPower_mem_formSpan (q : ℕ) : formPower (kahlerForm n) q ∈ formSpan n q :=
  mem_formSpan_of_mem_spCone (formPower_mem_spCone isSemipositiveOneOne_kahlerForm q)

variable (n) in
/-- `ω₀^q` as an element of `Λ_q`. -/
def kahlerPower (q : ℕ) : formSpan n q := ⟨formPower (kahlerForm n) q, formPower_mem_formSpan q⟩

end Constant

/-! ### Currents of bidimension `(q,q)` and positivity -/

section Currents

variable (n) in
/-- A real current of bidimension `(q,q)` on `U`: the linear map `γ ↦ T(γ)` from the constant
`(q,q)`-forms to the distributions on `U`; `T(γ)(φ) = ⟨T, φ γ⟩`. -/
abbrev LocalProductCurrent (U : Opens (ComplexModel n)) (q : ℕ) :=
  formSpan n q →ₗ[ℝ] 𝓓'(U, ℝ)

variable {U : Opens (ComplexModel n)} {q : ℕ}

/-- **Positivity on variable test forms**: `∑ₖ T(γₖ)(φₖ) ≥ 0` whenever the test form
`x ↦ ∑ₖ φₖ(x) γₖ` is strongly positive at every point. -/
def IsPositive (T : LocalProductCurrent n U q) : Prop :=
  ∀ (ι : Type) [Fintype ι] (γ : ι → formSpan n q) (φ : ι → 𝓓(U, ℝ)),
    (∀ x, ∑ i, φ i x • (γ i : RealForm n (2 * q)) ∈ spCone q) → 0 ≤ ∑ i, T (γ i) (φ i)

theorem isPositive_zero : IsPositive (0 : LocalProductCurrent n U q) := by
  intro ι _ γ φ _
  simp

namespace IsPositive

variable {S T : LocalProductCurrent n U q}

theorem add (hS : IsPositive S) (hT : IsPositive T) : IsPositive (S + T) := by
  intro ι _ γ φ h
  simp only [LinearMap.add_apply, _root_.add_apply, Finset.sum_add_distrib]
  exact add_nonneg (hS ι γ φ h) (hT ι γ φ h)

theorem smul (hT : IsPositive T) {c : ℝ} (hc : 0 ≤ c) : IsPositive (c • T) := by
  intro ι _ γ φ h
  simp only [LinearMap.smul_apply, _root_.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  exact mul_nonneg hc (hT ι γ φ h)

/-- The coefficient of a positive current on a strongly positive constant form is a positive
distribution. -/
theorem positiveDistribution (hT : IsPositive T) {γ : formSpan n q}
    (hγ : (γ : RealForm n (2 * q)) ∈ spCone q) : PositiveDistribution (T γ) := by
  intro φ hφ
  have h := hT Unit (fun _ => γ) (fun _ => φ) (fun x => by
    simpa using smul_mem_spCone hγ (hφ x))
  simpa using h

/-- The trace distribution `T(ω₀^q)` of a positive current is positive. -/
theorem positiveDistribution_trace (hT : IsPositive T) :
    PositiveDistribution (T (kahlerPower n q)) :=
  hT.positiveDistribution (formPower_mem_spCone isSemipositiveOneOne_kahlerForm q)

/-- **Order zero.**  Let `σ` be a locally finite measure on `U` representing the trace
distribution `T(ω₀^q)` of a positive current.  Then every coefficient `T(γ)` is integration against
`f σ` for a measurable density `f` bounded by the order-unit constant of `γ`. -/
theorem exists_density_of_measure (hT : IsPositive T) (σ : Measure U) [IsLocallyFiniteMeasure σ]
    (hσ : ∀ φ : 𝓓(U, ℝ), ∫ x : U, φ x ∂σ = T (kahlerPower n q) φ) (γ : formSpan n q) :
    ∃ f : U → ℝ, Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ (∀ x, |f x| ≤ C) ∧
      ∀ φ : 𝓓(U, ℝ), T γ φ = ∫ x : U, φ x * f x ∂σ := by
  classical
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  obtain ⟨C, hC, h₁, h₂⟩ := exists_orderUnit γ.2
  set w₀ : formSpan n q := kahlerPower n q with hω
  set γ₁ : formSpan n q := C • w₀ + (-1 : ℝ) • γ with hγ₁def
  set γ₂ : formSpan n q := C • w₀ + γ with hγ₂def
  have hγ₁ : (γ₁ : RealForm n (2 * q)) ∈ spCone q := by
    have e : (γ₁ : RealForm n (2 * q)) = C • formPower (kahlerForm n) q - (γ : RealForm n (2 * q))
      := by
      simp only [γ₁, w₀, kahlerPower, Submodule.coe_add, Submodule.coe_smul]
      module
    rw [e]
    exact h₁
  have hγ₂ : (γ₂ : RealForm n (2 * q)) ∈ spCone q := by
    simpa [γ₂, w₀, kahlerPower] using h₂
  obtain ⟨ν₁, -, hν₁lf, hν₁⟩ := (hT.positiveDistribution hγ₁).exists_regular_measure
  obtain ⟨ν₂, -, hν₂lf, hν₂⟩ := (hT.positiveDistribution hγ₂).exists_regular_measure
  let c : NNReal := Real.toNNReal (2 * C)
  have hc : (c : ℝ) = 2 * C := Real.coe_toNNReal _ (by positivity)
  -- integrability of test functions
  have hint : ∀ (μ : Measure U) [IsLocallyFiniteMeasure μ] (φ : 𝓓(U, ℝ)),
      Integrable (fun x : U => φ x) μ := by
    intro μ _ φ
    let g : C_c(U, ℝ) := testFunctionToCompactlySupportedLM U φ
    exact (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).congr
      (Eventually.of_forall fun x => by simp [g])
  let _ : IsLocallyFiniteMeasure (ν₁ + ν₂) := Measure.isLocallyFiniteMeasure_add ν₁ ν₂
  have hsum : ν₁ + ν₂ = c • σ := by
    apply Measure.eq_of_testFunction_integral_eq
    intro φ
    rw [integral_add_measure (hint ν₁ φ) (hint ν₂ φ), hν₁, hν₂, integral_smul_nnreal_measure,
      hσ, NNReal.smul_def, smul_eq_mul, hc]
    have e₁ : T γ₁ = C • T w₀ + (-1 : ℝ) • T γ := by
      rw [hγ₁def, T.map_add, T.map_smul, T.map_smul]
    have e₂ : T γ₂ = C • T w₀ + T γ := by
      rw [hγ₂def, T.map_add, T.map_smul]
    rw [e₁, e₂]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hac₁ : ν₁ ≪ σ := by
    refine (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl :
      ν₁ ≤ ν₁ + ν₂)).trans ?_
    rw [hsum]
    exact Measure.smul_absolutelyContinuous
  have hac₂ : ν₂ ≪ σ := by
    refine (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl :
      ν₂ ≤ ν₁ + ν₂)).trans ?_
    rw [hsum]
    exact Measure.smul_absolutelyContinuous
  -- the densities add up to `c`
  have hrn : ∀ᵐ x ∂σ, ν₁.rnDeriv σ x + ν₂.rnDeriv σ x = c := by
    have e₁ := Measure.rnDeriv_add' ν₁ ν₂ σ
    have e₂ := Measure.rnDeriv_smul_left' σ σ c
    have e₃ := Measure.rnDeriv_self σ
    rw [hsum] at e₁
    filter_upwards [e₁, e₂, e₃] with x h₁ h₂ h₃
    rw [Pi.add_apply] at h₁
    rw [← h₁, h₂, Pi.smul_apply, h₃, ENNReal.smul_def, smul_eq_mul, mul_one]
  set g₁ : U → ℝ := fun x => (ν₁.rnDeriv σ x).toReal
  set g₂ : U → ℝ := fun x => (ν₂.rnDeriv σ x).toReal
  have hg : ∀ᵐ x ∂σ, 0 ≤ g₁ x ∧ g₁ x ≤ 2 * C ∧ 0 ≤ g₂ x ∧ g₂ x ≤ 2 * C := by
    filter_upwards [hrn] with x hx
    have hle₁ : ν₁.rnDeriv σ x ≤ c := hx ▸ le_self_add
    have hle₂ : ν₂.rnDeriv σ x ≤ c := hx ▸ le_add_self
    have hne₁ : ν₁.rnDeriv σ x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle₁
    have hne₂ : ν₂.rnDeriv σ x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle₂
    refine ⟨ENNReal.toReal_nonneg, ?_, ENNReal.toReal_nonneg, ?_⟩
    · rw [← hc]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (by simpa using hle₁)
    · rw [← hc]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (by simpa using hle₂)
  have hmeas₁ : Measurable g₁ := (Measure.measurable_rnDeriv ν₁ σ).ennreal_toReal
  have hmeas₂ : Measurable g₂ := (Measure.measurable_rnDeriv ν₂ σ).ennreal_toReal
  set f₀ : U → ℝ := fun x => (g₂ x - g₁ x) / 2
  let f : U → ℝ := fun x => max (-C) (min C (f₀ x))
  have hff₀ : f =ᵐ[σ] f₀ := by
    filter_upwards [hg] with x hx
    simp only [f, f₀]
    rw [min_eq_right (by linarith [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]),
      max_eq_right (by linarith [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2])]
  refine ⟨f, ?_, C, hC, fun x => ?_, fun φ => ?_⟩
  · exact measurable_const.max (measurable_const.min ((hmeas₂.sub hmeas₁).div_const 2))
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · have hγ : γ = (1 / 2 : ℝ) • γ₂ + (-1 / 2 : ℝ) • γ₁ := by
      ext1
      simp only [γ₁, γ₂, Submodule.coe_smul, Submodule.coe_add]
      module
    have hi₁ : Integrable (fun x : U => g₁ x * φ x) σ := by
      refine (hint σ φ).bdd_mul hmeas₁.aestronglyMeasurable (c := 2 * C) ?_
      filter_upwards [hg] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2.1
    have hi₂ : Integrable (fun x : U => g₂ x * φ x) σ := by
      refine (hint σ φ).bdd_mul hmeas₂.aestronglyMeasurable (c := 2 * C) ?_
      filter_upwards [hg] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.2.1]
      exact hx.2.2.2
    have e₁ : T γ₁ φ = ∫ x : U, g₁ x * φ x ∂σ := by
      rw [← hν₁]
      exact (integral_toReal_rnDeriv_mul hac₁).symm
    have e₂ : T γ₂ φ = ∫ x : U, g₂ x * φ x ∂σ := by
      rw [← hν₂]
      exact (integral_toReal_rnDeriv_mul hac₂).symm
    calc T γ φ = (1 / 2 : ℝ) * (T γ₂ φ - T γ₁ φ) := by
          have e : T γ = (1 / 2 : ℝ) • T γ₂ + (-1 / 2 : ℝ) • T γ₁ := by
            rw [hγ, T.map_add, T.map_smul, T.map_smul]
          rw [e]
          simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
          ring
      _ = ∫ x : U, φ x * f₀ x ∂σ := by
          rw [e₁, e₂, ← integral_sub hi₂ hi₁, ← integral_const_mul]
          congr 1
          funext x
          simp only [f₀]
          ring
      _ = ∫ x : U, φ x * f x ∂σ := by
          refine integral_congr_ae ?_
          filter_upwards [hff₀] with x hx
          rw [hx]

/-- The (chosen) trace measure of a positive current on the open set, as a measure on `U`. -/
def traceMeasureOn (hT : IsPositive T) : Measure U :=
  Classical.choose hT.positiveDistribution_trace.exists_regular_measure

theorem isLocallyFiniteMeasure_traceMeasureOn (hT : IsPositive T) :
    IsLocallyFiniteMeasure (traceMeasureOn hT) :=
  (Classical.choose_spec hT.positiveDistribution_trace.exists_regular_measure).2.1

theorem integral_traceMeasureOn (hT : IsPositive T) (φ : 𝓓(U, ℝ)) :
    ∫ x : U, φ x ∂(traceMeasureOn hT) = T (kahlerPower n q) φ :=
  (Classical.choose_spec hT.positiveDistribution_trace.exists_regular_measure).2.2 φ

theorem exists_densityOn (hT : IsPositive T) (γ : formSpan n q) :
    ∃ f : U → ℝ, Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ (∀ x, |f x| ≤ C) ∧
      ∀ φ : 𝓓(U, ℝ), T γ φ = ∫ x : U, φ x * f x ∂(traceMeasureOn hT) :=
  have := isLocallyFiniteMeasure_traceMeasureOn hT
  hT.exists_density_of_measure _ (integral_traceMeasureOn hT) γ

/-- **The trace measure** `σ_T` of a positive current, as a measure on `ℂⁿ` carried by `U`: the
Riesz measure of the positive distribution `T(ω₀^q)`. -/
def traceMeasure (hT : IsPositive T) : Measure (ComplexModel n) :=
  (traceMeasureOn hT).map Subtype.val

/-- **The density** `f_γ` of the coefficient `T(γ)` with respect to the trace measure (extended by
zero off `U`). -/
def density (hT : IsPositive T) (γ : formSpan n q) : ComplexModel n → ℝ :=
  Function.extend Subtype.val (Classical.choose (hT.exists_densityOn γ)) 0

theorem measurableEmbedding_val : MeasurableEmbedding (Subtype.val : U → ComplexModel n) :=
  MeasurableEmbedding.subtype_coe U.isOpen.measurableSet

theorem integral_traceMeasure_eq (hT : IsPositive T) (g : ComplexModel n → ℝ) :
    ∫ x, g x ∂(traceMeasure hT) = ∫ x : U, g x ∂(traceMeasureOn hT) :=
  measurableEmbedding_val.integral_map g

theorem traceMeasure_compl (hT : IsPositive T) :
    traceMeasure hT ((U : Set (ComplexModel n))ᶜ) = 0 := by
  rw [traceMeasure, Measure.map_apply measurable_subtype_coe U.isOpen.measurableSet.compl]
  have : (Subtype.val : U → ComplexModel n) ⁻¹' (U : Set (ComplexModel n))ᶜ = ∅ := by
    ext x
    simp
  rw [this, measure_empty]

theorem traceMeasure_lt_top (hT : IsPositive T) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKU : K ⊆ U) : traceMeasure hT K < ⊤ := by
  have := isLocallyFiniteMeasure_traceMeasureOn hT
  rw [traceMeasure, Measure.map_apply measurable_subtype_coe hK.measurableSet]
  have hK' : IsCompact ((Subtype.val : U → ComplexModel n) ⁻¹' K) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_preimage_iff (by
      rw [Subtype.range_coe]; exact hKU)]
    exact hK
  exact hK'.measure_lt_top

theorem integral_traceMeasure (hT : IsPositive T) (φ : 𝓓(U, ℝ)) :
    ∫ x, φ x ∂(traceMeasure hT) = T (kahlerPower n q) φ := by
  rw [integral_traceMeasure_eq, integral_traceMeasureOn]

theorem density_val (hT : IsPositive T) (γ : formSpan n q) (x : U) :
    density hT γ x = Classical.choose (hT.exists_densityOn γ) x :=
  Subtype.val_injective.extend_apply _ _ x

theorem measurable_density (hT : IsPositive T) (γ : formSpan n q) :
    Measurable (density hT γ) :=
  measurableEmbedding_val.measurable_extend (Classical.choose_spec (hT.exists_densityOn γ)).1
    measurable_const

/-- The density of a coefficient is bounded. -/
theorem exists_abs_density_le (hT : IsPositive T) (γ : formSpan n q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |density hT γ x| ≤ C := by
  have hs := Classical.choose_spec (hT.exists_densityOn γ)
  obtain ⟨C, hC, hbound, -⟩ := hs.2
  refine ⟨C, hC, fun x => ?_⟩
  by_cases hx : x ∈ U
  · have e := density_val hT γ ⟨x, hx⟩
    simp only at e
    rw [e]
    exact hbound _
  · have hne : ¬ ∃ y : U, (y : ComplexModel n) = x := by
      rintro ⟨y, rfl⟩
      exact hx y.2
    have : density hT γ x = 0 := by
      rw [density, Function.extend_apply' _ _ _ hne]
      rfl
    rw [this, abs_zero]
    exact hC

/-- **Coefficients are measures dominated by the trace measure**: `T(γ)(φ) = ∫ φ f_γ dσ_T`. -/
theorem apply_eq_integral_density (hT : IsPositive T) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    T γ φ = ∫ x, φ x * density hT γ x ∂(traceMeasure hT) := by
  obtain ⟨C, -, -, hrep⟩ := (Classical.choose_spec (hT.exists_densityOn γ)).2
  rw [integral_traceMeasure_eq, hrep φ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [density_val]

/-- A function bounded on the compact subsets of `U` (and measurable) times a density is locally
integrable on `U` for the trace measure. -/
theorem locallyIntegrableOn_mul_density (hT : IsPositive T) (γ : formSpan n q)
    {u : ComplexModel n → ℝ} (hu : AEStronglyMeasurable u (traceMeasure hT))
    (hb : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → ∃ M : ℝ, ∀ x ∈ K, |u x| ≤ M) :
    LocallyIntegrableOn (fun x => u x * density hT γ x) U (traceMeasure hT) := by
  intro x hx
  obtain ⟨K, hKn, hK, hKU⟩ : ∃ K ∈ 𝓝 x, IsCompact K ∧ K ⊆ U := by
    obtain ⟨K, hK, hKn, hKU⟩ := exists_compact_subset U.isOpen hx
    exact ⟨K, mem_interior_iff_mem_nhds.mp hKn, hK, hKU⟩
  refine ⟨K, nhdsWithin_le_nhds hKn, ?_⟩
  obtain ⟨M, hM⟩ := hb K hK hKU
  obtain ⟨C, -, hC⟩ := exists_abs_density_le hT γ
  have hfin : traceMeasure hT K < ⊤ := traceMeasure_lt_top hT hK hKU
  refine Measure.integrableOn_of_bounded (M := M * C) hfin.ne
    (hu.mul (measurable_density hT γ).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hM y hy) (hC y) (abs_nonneg _) ((abs_nonneg _).trans (hM y hy))

/-- A compactly supported continuous function on `U` times a function bounded on its support is
integrable for the trace measure. -/
theorem integrable_mul_of_bounded (hT : IsPositive T) {ψ w : ComplexModel n → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hw : AEStronglyMeasurable w (traceMeasure hT)) (hwb : ∃ M, ∀ x ∈ tsupport ψ, |w x| ≤ M) :
    Integrable (fun x => ψ x * w x) (traceMeasure hT) := by
  obtain ⟨M, hM⟩ := hwb
  obtain ⟨Cψ, hCψ⟩ := hψ.bounded_above_of_compact_support hψc
  have hsupp : Function.support (fun x => ψ x * w x) ⊆ tsupport ψ := fun x hx =>
    subset_tsupport ψ (left_ne_zero_of_mul hx)
  refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
  refine Measure.integrableOn_of_bounded (M := Cψ * M)
    (traceMeasure_lt_top hT hψc hψU).ne (hψ.aestronglyMeasurable.mul hw) ?_
  filter_upwards [ae_restrict_mem (isClosed_tsupport ψ).measurableSet] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (hCψ x) (hM x hx) (abs_nonneg _) ((norm_nonneg _).trans (hCψ x))

/-- Two bounded measurable densities giving the same distribution agree almost everywhere for the
trace measure. -/
theorem ae_eq_of_forall_integral_eq (hT : IsPositive T) {f g : ComplexModel n → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∃ C, ∀ x, |f x| ≤ C) (hgb : ∃ C, ∀ x, |g x| ≤ C)
    (h : ∀ φ : 𝓓(U, ℝ), ∫ x, φ x * f x ∂(traceMeasure hT) = ∫ x, φ x * g x ∂(traceMeasure hT)) :
    f =ᵐ[traceMeasure hT] g := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hloc : ∀ {w : ComplexModel n → ℝ}, Measurable w → (∀ x, |w x| ≤ Cf + Cg) →
      LocallyIntegrableOn w U (traceMeasure hT) := by
    intro w hw hwb x hx
    obtain ⟨K, hK, hKn, hKU⟩ := exists_compact_subset U.isOpen hx
    refine ⟨K, nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hKn), ?_⟩
    exact Measure.integrableOn_of_bounded (M := Cf + Cg) (traceMeasure_lt_top hT hK hKU).ne
      hw.aestronglyMeasurable (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hwb y)
  have hfg : ∀ x, |f x - g x| ≤ Cf + Cg := fun x =>
    (abs_sub _ _).trans (add_le_add (hCf x) (hCg x))
  have hzero := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hloc (hf.sub hg) hfg) (μ := traceMeasure hT) (fun ψ hψ hψc hψU => by
      let φ : 𝓓(U, ℝ) := ⟨ψ, hψ, hψc, hψU⟩
      have hi : ∀ w : ComplexModel n → ℝ, Measurable w → (∀ x, |w x| ≤ Cf + Cg) →
          Integrable (fun x => ψ x * w x) (traceMeasure hT) := fun w hw hwb =>
        integrable_mul_of_bounded hT hψ.continuous hψc hψU hw.aestronglyMeasurable
          ⟨Cf + Cg, fun x _ => hwb x⟩
      have hf' : ∀ x, |f x| ≤ Cf + Cg := fun x =>
        (hCf x).trans (le_add_of_nonneg_right ((abs_nonneg _).trans (hCg x)))
      have hg' : ∀ x, |g x| ≤ Cf + Cg := fun x =>
        (hCg x).trans (le_add_of_nonneg_left ((abs_nonneg _).trans (hCf x)))
      simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
      rw [integral_sub (hi f hf hf') (hi g hg hg'), sub_eq_zero]
      exact h φ)
  have hcompl := traceMeasure_compl hT
  filter_upwards [hzero, measure_eq_zero_iff_ae_notMem.mp hcompl] with x hx hxU
  have : x ∈ U := by simpa using hxU
  exact sub_eq_zero.mp (hx this)

theorem density_add_ae (hT : IsPositive T) (γ γ' : formSpan n q) :
    density hT (γ + γ') =ᵐ[traceMeasure hT] density hT γ + density hT γ' := by
  obtain ⟨C, -, hC⟩ := exists_abs_density_le hT γ
  obtain ⟨C', -, hC'⟩ := exists_abs_density_le hT γ'
  obtain ⟨C'', -, hC''⟩ := exists_abs_density_le hT (γ + γ')
  refine ae_eq_of_forall_integral_eq hT (measurable_density hT _)
    ((measurable_density hT γ).add (measurable_density hT γ')) ⟨C'', hC''⟩
    ⟨C + C', fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩ fun φ => ?_
  have hi : ∀ g : formSpan n q, Integrable (fun x => φ x * density hT g x) (traceMeasure hT) :=
    fun g => integrable_mul_of_bounded hT φ.continuous φ.hasCompactSupport φ.tsupport_subset
      (measurable_density hT g).aestronglyMeasurable
      (by obtain ⟨D, -, hD⟩ := exists_abs_density_le hT g; exact ⟨D, fun x _ => hD x⟩)
  rw [← apply_eq_integral_density, map_add, _root_.add_apply, apply_eq_integral_density hT γ,
    apply_eq_integral_density hT γ', ← integral_add (hi γ) (hi γ')]
  simp only [Pi.add_apply, mul_add]

theorem density_smul_ae (hT : IsPositive T) (c : ℝ) (γ : formSpan n q) :
    density hT (c • γ) =ᵐ[traceMeasure hT] c • density hT γ := by
  obtain ⟨C, -, hC⟩ := exists_abs_density_le hT γ
  obtain ⟨C', -, hC'⟩ := exists_abs_density_le hT (c • γ)
  refine ae_eq_of_forall_integral_eq hT (measurable_density hT _)
    ((measurable_density hT γ).const_smul c) ⟨C', hC'⟩
    ⟨|c| * C, fun x => by
      rw [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)⟩ fun φ => ?_
  rw [← apply_eq_integral_density, map_smul, _root_.smul_apply, smul_eq_mul,
    apply_eq_integral_density hT γ, ← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  funext x
  ring

end IsPositive

/-! ### Multiplication by locally bounded Borel functions -/

/-- A real function bounded on every compact subset of `U`. -/
def IsLocallyBoundedOn (u : ComplexModel n → ℝ) (U : Set (ComplexModel n)) : Prop :=
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → ∃ M : ℝ, ∀ x ∈ K, |u x| ≤ M

namespace IsPositive

variable {T : LocalProductCurrent n U q}

theorem integrable_mul_density (hT : IsPositive T) {u : ComplexModel n → ℝ} (hu : Measurable u)
    (hb : IsLocallyBoundedOn u U) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    Integrable (fun x => φ x * (u x * density hT γ x)) (traceMeasure hT) := by
  obtain ⟨M, hM⟩ := hb _ φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨C, -, hC⟩ := exists_abs_density_le hT γ
  exact integrable_mul_of_bounded hT φ.continuous φ.hasCompactSupport φ.tsupport_subset
    (hu.mul (measurable_density hT γ)).aestronglyMeasurable ⟨M * C, fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hM x hx) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hM x hx))⟩

/-- The current `u T` for a positive `T` and a measurable `u` bounded on compact subsets of `U`:
`(u T)(γ) = u f_γ σ_T`. -/
def mulBorelLM (hT : IsPositive T) {u : ComplexModel n → ℝ} (hu : Measurable u)
    (hb : IsLocallyBoundedOn u U) : LocalProductCurrent n U q where
  toFun γ := regularDistribution (traceMeasure hT) (fun x => u x * density hT γ x)
    (locallyIntegrableOn_mul_density hT γ hu.aestronglyMeasurable hb)
  map_add' γ γ' := by
    ext φ
    rw [_root_.add_apply, regularDistribution_apply, regularDistribution_apply,
      regularDistribution_apply, ← integral_add (integrable_mul_density hT hu hb γ φ)
        (integrable_mul_density hT hu hb γ' φ)]
    refine integral_congr_ae ?_
    filter_upwards [density_add_ae hT γ γ'] with x hx
    rw [hx, Pi.add_apply]
    ring
  map_smul' c γ := by
    ext φ
    rw [RingHom.id_apply, _root_.smul_apply, regularDistribution_apply, regularDistribution_apply,
      smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [density_smul_ae hT c γ] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    ring

theorem mulBorelLM_apply (hT : IsPositive T) {u : ComplexModel n → ℝ} (hu : Measurable u)
    (hb : IsLocallyBoundedOn u U) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    mulBorelLM hT hu hb γ φ = ∫ x, φ x * (u x * density hT γ x) ∂(traceMeasure hT) :=
  regularDistribution_apply _ _ (locallyIntegrableOn_mul_density hT γ hu.aestronglyMeasurable hb) φ

end IsPositive

open Classical in
/-- **Multiplication of a current by a function**: for a positive current `T` and a measurable
function `u` bounded on the compact subsets of `U`, `u T` multiplies the coefficient measures of
    `T`
by `u` (`IsPositive.mulBorelLM`); in every other case it is `0` (a junk value, so that the
recursive products of `bt:recursive-product` can be written without proof arguments). -/
def mulBorel (T : LocalProductCurrent n U q) (u : ComplexModel n → ℝ) :
    LocalProductCurrent n U q :=
  if h : IsPositive T ∧ Measurable u ∧ IsLocallyBoundedOn u U then
    IsPositive.mulBorelLM h.1 h.2.1 h.2.2
  else 0

theorem mulBorel_apply {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {u : ComplexModel n → ℝ} (hu : Measurable u) (hb : IsLocallyBoundedOn u U)
    (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    mulBorel T u γ φ = ∫ x, φ x * (u x * hT.density γ x) ∂hT.traceMeasure := by
  rw [mulBorel, dite_eq_left ⟨hT, hu, hb⟩, IsPositive.mulBorelLM_apply]

/-- A function smooth on an open set, multiplied by a smooth function supported in it, is
smooth everywhere. -/
theorem contDiff_mul_of_tsupport_subset {D : Set (ComplexModel n)} (hD : IsOpen D)
    {ψ ρ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψD : tsupport ψ ⊆ D)
    (hρ : ContDiffOn ℝ ∞ ρ D) : ContDiff ℝ ∞ (fun z => ψ z * ρ z) := by
  simpa only [smul_eq_mul] using SmoothCutoff.contDiff_smul_of_tsupport_subset hD hψ hψD hρ

/-- The test function `φ u` for `u` smooth on an open set `A` containing the support of `φ`. -/
def smoothMulTest {A : Set (ComplexModel n)} (hA : IsOpen A) {u : ComplexModel n → ℝ}
    (hu : ContDiffOn ℝ ∞ u A) (φ : 𝓓(U, ℝ)) (hφ : tsupport φ ⊆ A) : 𝓓(U, ℝ) where
  toFun x := φ x * u x
  contDiff' := contDiff_mul_of_tsupport_subset hA φ.contDiff hφ hu
  hasCompactSupport' := φ.hasCompactSupport.mul_right
  tsupport_subset' := (tsupport_mul_subset_left).trans φ.tsupport_subset

@[simp] theorem smoothMulTest_apply {A : Set (ComplexModel n)} (hA : IsOpen A)
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u A) (φ : 𝓓(U, ℝ)) (hφ : tsupport φ ⊆ A)
    (x : ComplexModel n) : smoothMulTest hA hu φ hφ x = φ x * u x := rfl

/-- For `u` smooth near the support of `φ`, `(u T)(γ)(φ) = T(γ)(u φ)`. -/
theorem IsPositive.apply_smoothMulTest {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {A : Set (ComplexModel n)} (hA : IsOpen A) {u : ComplexModel n → ℝ}
    (hu : ContDiffOn ℝ ∞ u A) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) (hφ : tsupport φ ⊆ A) :
    T γ (smoothMulTest hA hu φ hφ) = ∫ x, φ x * (u x * hT.density γ x) ∂hT.traceMeasure := by
  rw [hT.apply_eq_integral_density]
  simp only [smoothMulTest_apply, mul_assoc]

/-- Multiplication by a constant. -/
theorem mulBorel_const {T : LocalProductCurrent n U q} (hT : IsPositive T) (c : ℝ) :
    mulBorel T (fun _ => c) = c • T := by
  ext γ φ
  rw [mulBorel_apply hT measurable_const (fun K _ _ => ⟨|c|, fun _ _ => le_rfl⟩),
    LinearMap.smul_apply, _root_.smul_apply, hT.apply_eq_integral_density, smul_eq_mul,
    ← integral_const_mul]
  congr 1
  funext x
  ring

/-- `(u + v) T = u T + v T`. -/
theorem mulBorel_add {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {u v : ComplexModel n → ℝ} (hu : Measurable u) (hub : IsLocallyBoundedOn u U)
    (hv : Measurable v) (hvb : IsLocallyBoundedOn v U) :
    mulBorel T (u + v) = mulBorel T u + mulBorel T v := by
  have hb : IsLocallyBoundedOn (u + v) U := fun K hK hKU => by
    obtain ⟨M, hM⟩ := hub K hK hKU
    obtain ⟨N, hN⟩ := hvb K hK hKU
    exact ⟨M + N, fun x hx => (abs_add_le _ _).trans (add_le_add (hM x hx) (hN x hx))⟩
  ext γ φ
  rw [mulBorel_apply hT (hu.add hv) hb, LinearMap.add_apply, _root_.add_apply,
    mulBorel_apply hT hu hub, mulBorel_apply hT hv hvb,
    ← integral_add (hT.integrable_mul_density hu hub γ φ) (hT.integrable_mul_density hv hvb γ φ)]
  congr 1
  funext x
  simp only [Pi.add_apply]
  ring

end Currents

end SGPT.Foundations.Analysis.Pending.LocalProductCurrents
