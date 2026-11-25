/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentLebesgue
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BiholomorphicPair

/-!
# Pull-back of positive currents along biholomorphisms, and `(τ^* T)_ac = τ^*(T_ac)`

The transformation of the absolutely continuous part `(τ^* T)_ac = τ^*(T_ac)` has a
classical antecedent in [Boucksom, Lemma 4.2 (iii)](https://arxiv.org/pdf/math/0201031#page=12),
which treats positive `(1,1)`-currents under generically finite holomorphic maps of compact
Kähler manifolds. The version here uses a biholomorphism `τ : A → B` between open coordinate
domains with inverse `σ` and works for positive currents of any bidimension `(q,q)`. It
expresses the transformation through the trace measure and the corresponding coefficient density.

* **Uniqueness of the absolutely continuous density** (`ae_eq_ofReal_acDensity`): if a measure
    carried by `B`, finite on
  compacts, represents `T(γ)` for a strongly positive `γ` and is `s + f λ` with `s ⟂ λ`,
    then `f = acWeight · L(γ)` a.e.
  (through `coeffMeasure`, the measure `L(γ) σ_T`, and mathlib's `Measure.eq_rnDeriv`).
* `pullSpan S`: the pull-back `γ ↦ S^* γ` of constant forms along a complex-linear map,
    a linear map of `Λ_q` preserving the
  strongly positive cone.
* **The pull-back** `pullback h hT : LocalProductCurrent n A q`,
    `(τ^* T)(γ)(φ) = ∫ φ(x) L_{τ x}(Dσ(τ x)^* γ) d(σ_* σ_T)(x)`;
  `pullback_apply`: `⟨τ^* T, φ γ⟩ = ∫_B φ(σ y) L_y(Dσ(y)^* γ) dσ_T(y) = ⟨T, σ^*(φ γ)⟩`;
    `isPositive_pullback`.
* Measure theory along `τ`: `ae_comp_of_ae` (null sets of `B` pull back to null sets of `A`),
    `map_withDensity_restrict` (the
  change of variables `σ_*((r λ)|_B) = |det Dτ| (r ∘ τ) λ|_A`), `mutuallySingular_map` (singular
    measures stay singular),
  `pbMeasure_eq`.
* **`ae_acDensity_pullback`** (`(τ^* T)_ac = τ^*(T_ac)`): for almost every `x ∈ A` and every `γ`,
  `acWeight'(x) L'_x(γ) = |det_ℝ Dτ(x)| acWeight(τ x) L_{τ x}(Dσ(τ x)^* γ)`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal

namespace SGPT.Foundations.Analysis.Pending.LocalCurrentPullback

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms TopDegreeDensity LocalProductCurrents
    LocalCurrentLebesgue
  LocalBedfordTaylorLocality

attribute [local instance] addCommGroupFormSpan

variable {n q : ℕ}

/-! ### Uniqueness of the absolutely continuous density -/

section Unique

variable {U : Opens (ComplexModel n)} {T : LocalProductCurrent n U q}

/-- The coefficient measure `L(γ)⁺ σ_T` of a constant form (for a strongly positive `γ` it
    represents `T(γ)`). -/
def coeffMeasure (hT : IsPositive T) (γ : formSpan n q) : Measure (ComplexModel n) :=
  hT.traceMeasure.withDensity fun x => ENNReal.ofReal (densityForm hT x γ)

theorem measurable_ofReal_densityForm (hT : IsPositive T) (γ : formSpan n q) :
    Measurable fun x => ENNReal.ofReal (densityForm hT x γ) :=
  ENNReal.measurable_ofReal.comp (measurable_densityForm hT γ)

theorem coeffMeasure_compl (hT : IsPositive T) (γ : formSpan n q) :
    coeffMeasure hT γ ((U : Set (ComplexModel n))ᶜ) = 0 :=
  withDensity_absolutelyContinuous _ _ hT.traceMeasure_compl

theorem coeffMeasure_lt_top (hT : IsPositive T) (γ : formSpan n q) (K : Set (ComplexModel n))
    (hK : IsCompact K)
    (hKU : K ⊆ U) : coeffMeasure hT γ K < ⊤ := by
  obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT γ
  rw [coeffMeasure, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (densityForm hT x γ) ∂hT.traceMeasure
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂hT.traceMeasure :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC x))
    _ = ENNReal.ofReal C * hT.traceMeasure K := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hT.traceMeasure_lt_top hK hKU)

/-- For a strongly positive `γ`, `T(γ)` is integration against the coefficient measure. -/
theorem integral_coeffMeasure (hT : IsPositive T) {γ : formSpan n q} (hγ : γ ∈ posCone n q)
    (φ : 𝓓(U, ℝ)) :
    ∫ x, φ x ∂(coeffMeasure hT γ) = T γ φ := by
  rw [coeffMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_densityForm hT
    γ)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), apply_eq_integral_densityForm hT]
  refine integral_congr_ae ?_
  filter_upwards [ae_densityForm_nonneg hT] with x hx
  rw [ENNReal.toReal_ofReal (hx γ hγ), smul_eq_mul, mul_comm]

/-- The Lebesgue decomposition of the coefficient measure. -/
theorem coeffMeasure_eq (hT : IsPositive T) (γ : formSpan n q) :
    coeffMeasure hT γ = (sgMeasure hT).withDensity (fun x => ENNReal.ofReal (densityForm hT x γ)) +
      volume.withDensity (hT.traceMeasure.rnDeriv volume * fun x => ENNReal.ofReal (densityForm hT
        x γ)) := by
  rw [withDensity_mul _ (Measure.measurable_rnDeriv _ _) (measurable_ofReal_densityForm hT γ),
    coeffMeasure]
  conv_lhs => rw [← sgMeasure_add_acMeasure hT]
  rw [withDensity_add_measure, acMeasure]

/-- **Uniqueness of the absolutely continuous density.**  Let `γ` be strongly positive and let `μ`
    be a measure carried by
`U`, finite on the compact subsets of `U`, representing `T(γ)`.  If `μ = s + f λ` with `s ⟂ λ`,
    then
`f = acWeight · L(γ)` Lebesgue-almost everywhere. -/
theorem ae_eq_ofReal_acDensity (hT : IsPositive T) {γ : formSpan n q} (hγ : γ ∈ posCone n q)
    {μ s : Measure (ComplexModel n)} {f : ComplexModel n → ℝ≥0∞} (hf : Measurable f)
    (hμU : μ ((U : Set (ComplexModel n))ᶜ) = 0) (hμK : ∀ K : Set (ComplexModel n),
      IsCompact K → K ⊆ U → μ K < ⊤)
    (hTμ : ∀ φ : 𝓓(U, ℝ), ∫ x, φ x ∂μ = T γ φ) (hs : s ⟂ₘ volume) (hdec : μ = s +
      volume.withDensity f) :
    f =ᵐ[volume] fun x => ENNReal.ofReal (acWeight hT x * densityForm hT x γ) := by
  have hm : μ = coeffMeasure hT γ :=
    eq_of_forall_testFunction_integral_eq hμU (coeffMeasure_compl hT γ) hμK (coeffMeasure_lt_top
      hT γ)
      fun φ => by rw [hTμ, integral_coeffMeasure hT hγ]
  have h1 : f =ᵐ[volume] μ.rnDeriv volume := Measure.eq_rnDeriv hf hs hdec
  have hsg : (sgMeasure hT).withDensity (fun x => ENNReal.ofReal (densityForm hT x γ)) ⟂ₘ volume :=
    (sgMeasure_mutuallySingular hT).mono_ac (withDensity_absolutelyContinuous _ _)
      Measure.AbsolutelyContinuous.rfl
  have h2 := Measure.eq_rnDeriv ((Measure.measurable_rnDeriv _ _).mul
    (measurable_ofReal_densityForm hT γ)) hsg
    (coeffMeasure_eq hT γ)
  rw [← hm] at h2
  filter_upwards [h1, h2, Measure.rnDeriv_lt_top hT.traceMeasure volume] with x h1 h2 h3
  rw [h1, ← h2, Pi.mul_apply, acWeight, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal h3.ne]

end Unique

/-! ### Pull-back of constant forms along complex-linear maps -/

section Forms

/-- The pull-back of a form of `Λ_q` along a complex-linear map lies in `Λ_q`. -/
theorem compContinuousLinearMap_mem_formSpan (S : ComplexModel n →L[ℂ] ComplexModel n)
    {γ : RealForm n (2 * q)}
    (hγ : γ ∈ formSpan n q) : γ.compContinuousLinearMap (S.restrictScalars ℝ) ∈ formSpan n q := by
  have hI : ∀ v, S.restrictScalars ℝ (Complex.I • v) = Complex.I • S.restrictScalars ℝ v := fun v
    =>
    S.map_smul Complex.I v
  induction hγ using Submodule.span_induction with
  | mem x hx => exact mem_formSpan_of_mem_spCone (compContinuousLinearMap_mem_spCone _ hI q hx)
  | zero => rw [zero_compContinuousLinearMap]; exact (formSpan n q).zero_mem
  | add x y _ _ hx hy => rw [add_compContinuousLinearMap]; exact (formSpan n q).add_mem hx hy
  | smul c x _ hx => rw [smul_compContinuousLinearMap]; exact (formSpan n q).smul_mem c hx

variable (q) in
/-- **Pull-back of constant forms** along a complex-linear map `S`, `γ ↦ S^* γ`,
    as a linear map of `Λ_q`. -/
def pullSpan (S : ComplexModel n →L[ℂ] ComplexModel n) : formSpan n q →ₗ[ℝ] formSpan n q :=
  (ContinuousAlternatingMap.compContinuousLinearMapₗ (S.restrictScalars ℝ)).restrict
    fun _ hγ => compContinuousLinearMap_mem_formSpan S hγ

@[simp] theorem coe_pullSpan (S : ComplexModel n →L[ℂ] ComplexModel n) (γ : formSpan n q) :
    (pullSpan q S γ : RealForm n (2 * q)) = (γ : RealForm n (2 * q)).compContinuousLinearMap
      (S.restrictScalars ℝ) :=
  rfl

theorem pullSpan_mem_posCone (S : ComplexModel n →L[ℂ] ComplexModel n) {γ : formSpan n q}
    (hγ : γ ∈ posCone n q) : pullSpan q S γ ∈ posCone n q :=
  compContinuousLinearMap_mem_spCone _ (fun v => S.map_smul Complex.I v) q hγ

theorem pullSpan_pullSpan (S S' : ComplexModel n →L[ℂ] ComplexModel n) (γ : formSpan n q) :
    pullSpan q S (pullSpan q S' γ) = pullSpan q (S'.comp S) γ := by
  apply Subtype.ext
  ext v
  rfl

theorem pullSpan_id (γ : formSpan n q) : pullSpan q (ContinuousLinearMap.id ℂ (ComplexModel n))
    γ = γ := by
  apply Subtype.ext
  ext v
  rfl

theorem continuous_pullSpan_apply (γ : formSpan n q) :
    Continuous fun S : ComplexModel n →L[ℂ] ComplexModel n => pullSpan q S γ := by
  have h1 : Continuous fun S : ComplexModel n →L[ℂ] ComplexModel n => S.restrictScalars ℝ :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (ComplexModel n) (ComplexModel n)
      ℝ ℝ).continuous
  have h : Continuous fun S : ComplexModel n →L[ℂ] ComplexModel n =>
      (γ : RealForm n (2 * q)).compContinuousLinearMap (S.restrictScalars ℝ) :=
    ((ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM (𝕜 := ℝ) (E := ComplexModel n)
      (F := ComplexModel n) (G := ℝ) (ι := Fin (2 * q))).comp h1).clm_apply
      (continuous_const (y := (γ : RealForm n (2 * q))))
  exact h.subtype_mk _

theorem continuous_repr_pullSpan_apply (γ : formSpan n q) (i : Fin (Module.finrank ℝ (formSpan n
    q))) :
    Continuous fun S : ComplexModel n →L[ℂ] ComplexModel n => (formBasis n q).repr (pullSpan q S
      γ) i :=
  ((formBasis n q).coord i).continuous_of_finiteDimensional.comp (continuous_pullSpan_apply γ)

variable {U : Opens (ComplexModel n)} {T : LocalProductCurrent n U q}

theorem measurable_densityForm_pullSpan (hT : IsPositive T)
    {g : ComplexModel n → (ComplexModel n →L[ℂ] ComplexModel n)} (hg : Measurable g)
      (γ : formSpan n q) :
    Measurable fun y => densityForm hT y (pullSpan q (g y) γ) := by
  simp_rw [densityForm_apply]
  exact Finset.measurable_sum _ fun i _ =>
    ((continuous_repr_pullSpan_apply γ i).measurable.comp hg).mul (hT.measurable_density _)

end Forms

/-! ### The pull-back of a positive current -/

section Pullback

open BedfordTaylor

/-- A measurable function agreeing with `f` on the open set `s` (extended by `0`). -/
def onOpen (s : Opens (ComplexModel n)) (f : ComplexModel n → ComplexModel n) : ComplexModel n →
    ComplexModel n := by
  classical exact (s : Set (ComplexModel n)).piecewise f fun _ => 0

theorem onOpen_of_mem {s : Opens (ComplexModel n)} {f : ComplexModel n → ComplexModel n} {x :
    ComplexModel n}
    (hx : x ∈ s) : onOpen s f x = f x := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hx

theorem measurable_onOpen {s : Opens (ComplexModel n)} {f : ComplexModel n → ComplexModel n}
    (hf : ContinuousOn f s) : Measurable (onOpen s f) := by
  classical
  exact hf.measurable_piecewise continuous_const.continuousOn s.isOpen.measurableSet

variable {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n} {T :
    LocalProductCurrent n B q}

/-- The push-forward `σ_*(σ_T|_B)` of the trace measure, carried by `A`. -/
def pbMeasure (σ : ComplexModel n → ComplexModel n) (hT : IsPositive T) : Measure (ComplexModel n)
    :=
  (hT.traceMeasure.restrict B).map (onOpen B σ)

/-- The coefficient density of the pull-back at `x ∈ A`: `L_{τ x}(Dσ(τ x)^* γ)`. -/
def pbDensity (A : Opens (ComplexModel n)) (τ σ : ComplexModel n → ComplexModel n)
    (hT : IsPositive T)
    (γ : formSpan n q) (x : ComplexModel n) : ℝ :=
  densityForm hT (onOpen A τ x) (pullSpan q (fderiv ℂ σ (onOpen A τ x)) γ)

theorem measurable_pbDensity (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    (γ : formSpan n q) :
    Measurable (pbDensity A τ σ hT γ) :=
  (measurable_densityForm_pullSpan hT (measurable_fderiv ℂ σ) γ).comp (measurable_onOpen
    h.holo.continuousOn)

theorem pbDensity_apply_of_mem (hT : IsPositive T) (γ : formSpan n q) {x : ComplexModel n} (hx : x
    ∈ A) :
    pbDensity A τ σ hT γ x = densityForm hT (τ x) (pullSpan q (fderiv ℂ σ (τ x)) γ) := by
  rw [pbDensity, onOpen_of_mem hx]

theorem pbDensity_comp (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) (γ : formSpan n q)
    {y : ComplexModel n} (hy : y ∈ B) :
    pbDensity A τ σ hT γ (σ y) = densityForm hT y (pullSpan q (fderiv ℂ σ y) γ) := by
  rw [pbDensity_apply_of_mem hT γ (h.mapsTo_inv hy), h.right_inv y hy]

theorem pbDensity_add (hT : IsPositive T) (γ γ' : formSpan n q) (x : ComplexModel n) :
    pbDensity A τ σ hT (γ + γ') x = pbDensity A τ σ hT γ x + pbDensity A τ σ hT γ' x := by
  simp only [pbDensity, map_add]

theorem pbDensity_smul (hT : IsPositive T) (c : ℝ) (γ : formSpan n q) (x : ComplexModel n) :
    pbDensity A τ σ hT (c • γ) x = c * pbDensity A τ σ hT γ x := by
  simp only [pbDensity, map_smul, smul_eq_mul]

theorem measurable_onOpen_inv (h : IsBiholomorphicPair A B τ σ) : Measurable (onOpen B σ) :=
  measurable_onOpen h.holo_inv.continuousOn

theorem pbMeasure_apply (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) {t : Set
    (ComplexModel n)}
    (ht : MeasurableSet t) : pbMeasure σ hT t = hT.traceMeasure (onOpen B σ ⁻¹' t ∩ B) := by
  rw [pbMeasure, Measure.map_apply (measurable_onOpen_inv h) ht,
    Measure.restrict_apply (measurable_onOpen_inv h ht)]

/-- The preimage of a subset of `A` under `σ`, inside `B`, is its image under `τ`. -/
theorem preimage_onOpen_inter_subset (h : IsBiholomorphicPair A B τ σ) (t : Set (ComplexModel n)) :
    onOpen B σ ⁻¹' t ∩ B ⊆ τ '' t := by
  rintro y ⟨hyt, hyB⟩
  rw [mem_preimage, onOpen_of_mem hyB] at hyt
  exact ⟨σ y, hyt, h.right_inv y hyB⟩

theorem pbMeasure_compl (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) :
    pbMeasure σ hT ((A : Set (ComplexModel n))ᶜ) = 0 := by
  rw [pbMeasure_apply h hT A.isOpen.measurableSet.compl]
  have : onOpen B σ ⁻¹' (A : Set (ComplexModel n))ᶜ ∩ B = ∅ := by
    refine eq_empty_of_forall_notMem fun y ⟨hy, hyB⟩ => ?_
    rw [mem_preimage, onOpen_of_mem hyB] at hy
    exact hy (h.mapsTo_inv hyB)
  rw [this, measure_empty]

theorem pbMeasure_lt_top (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) {K : Set
    (ComplexModel n)}
    (hK : IsCompact K) (hKA : K ⊆ A) : pbMeasure σ hT K < ⊤ := by
  rw [pbMeasure_apply h hT hK.measurableSet]
  have hτK : IsCompact (τ '' K) := hK.image_of_continuousOn (h.holo.continuousOn.mono hKA)
  exact (measure_mono (preimage_onOpen_inter_subset h K)).trans_lt
    (hT.traceMeasure_lt_top hτK (image_subset_iff.mpr fun x hx => h.mapsTo (hKA hx)))

/-- **Integrals against the push-forward measure** are integrals over `B` against `σ_T`. -/
theorem integral_pbMeasure (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    {g : ComplexModel n → ℝ}
    (hg : AEStronglyMeasurable g (pbMeasure σ hT)) :
    ∫ x, g x ∂pbMeasure σ hT = ∫ y in B, g (σ y) ∂hT.traceMeasure := by
  rw [pbMeasure, integral_map (measurable_onOpen_inv h).aemeasurable hg]
  exact setIntegral_congr_fun B.isOpen.measurableSet fun y hy => by rw [onOpen_of_mem hy]

theorem integrable_pbMeasure_iff (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    {g : ComplexModel n → ℝ}
    (hg : AEStronglyMeasurable g (pbMeasure σ hT)) :
    Integrable g (pbMeasure σ hT) ↔ IntegrableOn (fun y => g (σ y)) B hT.traceMeasure := by
  rw [pbMeasure, integrable_map_measure hg (measurable_onOpen_inv h).aemeasurable]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem B.isOpen.measurableSet] with y hy
  simp only [Function.comp_apply, onOpen_of_mem hy]

/-- The coefficients of `Dσ(y)^* γ` are bounded on the compact subsets of `B`. -/
theorem exists_abs_repr_pullSpan_le (h : IsBiholomorphicPair A B τ σ) (γ : formSpan n q)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKB : K ⊆ B) (i : Fin (Module.finrank ℝ
      (formSpan n q))) :
    ∃ C, ∀ y ∈ K, |(formBasis n q).repr (pullSpan q (fderiv ℂ σ y) γ) i| ≤ C := by
  have hd : ContinuousOn (fderiv ℂ σ) B :=
    h.holo_inv.continuousOn_fderiv_of_isOpen B.isOpen (ENat.natCast_le_of_coe_top_le_withTop
      le_rfl 1)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (((continuous_repr_pullSpan_apply γ i).comp_continuousOn hd).mono hKB)
  exact ⟨C, fun y hy => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hC y hy⟩

/-- The density of the pull-back is bounded on the compact subsets of `A`. -/
theorem exists_abs_pbDensity_le (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    (γ : formSpan n q)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKA : K ⊆ A) :
    ∃ C, ∀ x ∈ K, |pbDensity A τ σ hT γ x| ≤ C := by
  have hτK : IsCompact (τ '' K) := hK.image_of_continuousOn (h.holo.continuousOn.mono hKA)
  have hτKB : τ '' K ⊆ B := image_subset_iff.mpr fun x hx => h.mapsTo (hKA hx)
  choose c hc using fun i => exists_abs_repr_pullSpan_le h γ hτK hτKB i
  choose D hD0 hD using fun i => hT.exists_abs_density_le (formBasis n q i)
  refine ⟨∑ i, c i * D i, fun x hx => ?_⟩
  rw [pbDensity_apply_of_mem hT γ (hKA hx), densityForm_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have h1 := hc i _ (mem_image_of_mem τ hx)
  exact mul_le_mul h1 (hD i _) (abs_nonneg _) ((abs_nonneg _).trans h1)

theorem locallyIntegrableOn_pbDensity (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    (γ : formSpan n q) :
    LocallyIntegrableOn (pbDensity A τ σ hT γ) A (pbMeasure σ hT) := by
  intro x hx
  obtain ⟨K, hK, hxK, hKA⟩ := exists_compact_subset A.isOpen hx
  obtain ⟨C, hC⟩ := exists_abs_pbDensity_le h hT γ hK hKA
  refine ⟨K, nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hxK), ?_⟩
  refine Measure.integrableOn_of_bounded (M := C) (pbMeasure_lt_top h hT hK hKA).ne
    (measurable_pbDensity h hT γ).aestronglyMeasurable ?_
  exact (ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall fun y hy => by
    rw [Real.norm_eq_abs]; exact hC y hy)

theorem integrable_mul_pbDensity (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    (γ : formSpan n q)
    (φ : 𝓓(A, ℝ)) : Integrable (fun x => φ x * pbDensity A τ σ hT γ x) (pbMeasure σ hT) := by
  obtain ⟨C, hC⟩ := exists_abs_pbDensity_le h hT γ φ.hasCompactSupport φ.tsupport_subset
  apply MeasureLocality.integrable_mul_of_ae_bounded_on_tsupport φ.continuous φ.hasCompactSupport
    (pbMeasure_lt_top h hT φ.hasCompactSupport φ.tsupport_subset)
    (measurable_pbDensity h hT γ).aestronglyMeasurable
  exact (ae_restrict_iff' φ.hasCompactSupport.measurableSet).mpr (Eventually.of_forall hC)

/-- **The pull-back `τ^* T` of a positive current** along a biholomorphism `τ : A → B` with
    inverse `σ`:
`(τ^* T)(γ)(φ) = ∫ φ(x) L_{τ x}(Dσ(τ x)^* γ) d(σ_* σ_T)(x)`, i.e. `⟨τ^* T, φ γ⟩ = ⟨T, σ^*(φ γ)⟩`.
-/
def pullback (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) : LocalProductCurrent n A q
    where
  toFun γ := regularDistribution (pbMeasure σ hT) (pbDensity A τ σ hT γ)
    (locallyIntegrableOn_pbDensity h hT γ)
  map_add' γ γ' := by
    ext φ
    rw [_root_.add_apply, regularDistribution_apply, regularDistribution_apply,
      regularDistribution_apply,
      ← integral_add (integrable_mul_pbDensity h hT γ φ) (integrable_mul_pbDensity h hT γ' φ)]
    congr 1
    funext x
    rw [pbDensity_add, mul_add]
  map_smul' c γ := by
    ext φ
    rw [RingHom.id_apply, _root_.smul_apply, regularDistribution_apply, regularDistribution_apply,
      smul_eq_mul,
      ← integral_const_mul]
    congr 1
    funext x
    rw [pbDensity_smul]
    ring

theorem pullback_congr {degree : ℕ} (h : IsBiholomorphicPair A B τ σ)
    {S S' : LocalProductCurrent n B degree}
    (hS : IsPositive S) (hS' : IsPositive S') (e : S = S') : pullback h hS = pullback h hS' := by
  subst e
  rfl

theorem pullback_apply_eq (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) (γ : formSpan n q)
    (φ : 𝓓(A, ℝ)) : pullback h hT γ φ = ∫ x, φ x * pbDensity A τ σ hT γ x ∂pbMeasure σ hT :=
  regularDistribution_apply _ _ (locallyIntegrableOn_pbDensity h hT γ) φ

/-- **`⟨τ^* T, φ γ⟩ = ⟨T, σ^*(φ γ)⟩`**: the pull-back integrated on `B`. -/
theorem pullback_apply (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) (γ : formSpan n q)
    (φ : 𝓓(A, ℝ)) : pullback h hT γ φ =
      ∫ y in B, φ (σ y) * densityForm hT y (pullSpan q (fderiv ℂ σ y) γ) ∂hT.traceMeasure := by
  rw [pullback_apply_eq, integral_pbMeasure h hT (integrable_mul_pbDensity h hT γ
    φ).aestronglyMeasurable]
  exact setIntegral_congr_fun B.isOpen.measurableSet fun y hy => by simp only [pbDensity_comp h hT
    γ hy]

theorem integrableOn_pullback_integrand (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    (γ : formSpan n q)
    (φ : 𝓓(A, ℝ)) :
    IntegrableOn (fun y => φ (σ y) * densityForm hT y (pullSpan q (fderiv ℂ σ y) γ))
      B hT.traceMeasure := by
  have hi := (integrable_pbMeasure_iff h hT (integrable_mul_pbDensity h hT γ
    φ).aestronglyMeasurable).mp
    (integrable_mul_pbDensity h hT γ φ)
  refine hi.congr_fun (fun y hy => ?_) B.isOpen.measurableSet
  simp only [pbDensity_comp h hT γ hy]

/-- **The pull-back of a positive current is positive.** -/
theorem isPositive_pullback (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    : IsPositive (pullback h hT) := by
  intro ι _ γ φ hγ
  simp only [pullback_apply h hT]
  rw [← integral_finsetSum _ fun i _ => integrableOn_pullback_integrand h hT (γ i) (φ i)]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_of_ae (ae_densityForm_nonneg hT)] with y hy
  have hmem : (∑ i, φ i (σ y) • γ i) ∈ posCone n q := by
    change ((∑ i, φ i (σ y) • γ i : formSpan n q) : RealForm n (2 * q)) ∈ spCone q
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hγ (σ y)
  have h2 := hy _ (pullSpan_mem_posCone (fderiv ℂ σ y) hmem)
  simp only [map_sum, map_smul, smul_eq_mul] at h2
  simpa only [Pi.zero_apply] using h2

end Pullback

/-! ### Null sets, the change of variables, and the singular part -/

section Measures

open BedfordTaylor

variable {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}

theorem differentiableOn_inv (h : IsBiholomorphicPair A B τ σ) : DifferentiableOn ℝ σ B :=
  (h.holo_inv.differentiableOn (by simp)).restrictScalars ℝ

theorem differentiableAt_of_mem (h : IsBiholomorphicPair A B τ σ) {x : ComplexModel n} (hx : x ∈
    A) :
    DifferentiableAt ℂ τ x :=
  (h.holo.differentiableOn (by simp) x hx).differentiableAt
    (A.isOpen.mem_nhds hx)

theorem differentiableAt_inv_of_mem (h : IsBiholomorphicPair A B τ σ) {y : ComplexModel n} (hy : y
    ∈ B) :
    DifferentiableAt ℂ σ y :=
  (h.holo_inv.differentiableOn (by simp) y hy).differentiableAt
    (B.isOpen.mem_nhds hy)

/-- **`τ` pulls Lebesgue-null subsets of `B` back to null subsets of `A`**: a property holding for
    almost every point of
`B` holds at `τ x` for almost every `x ∈ A`. -/
theorem ae_comp_of_ae (h : IsBiholomorphicPair A B τ σ) {P : ComplexModel n → Prop}
    (hP : ∀ᵐ y ∂(volume : Measure (ComplexModel n)), y ∈ B → P y) :
    ∀ᵐ x ∂(volume : Measure (ComplexModel n)), x ∈ A → P (τ x) := by
  obtain ⟨N, hsub, -, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have himg : (volume : Measure (ComplexModel n)) (σ '' (N ∩ B)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
      ((differentiableOn_inv h).mono inter_subset_right) (measure_mono_null inter_subset_left hN0)
  refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) himg)
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hx
  obtain ⟨hxA, hPx⟩ := hx
  refine ⟨τ x, ⟨hsub ?_, h.mapsTo hxA⟩, h.left_inv x hxA⟩
  simp only [Set.mem_ofPred_eq, Classical.not_imp]
  exact ⟨h.mapsTo hxA, hPx⟩

/-- `σ⁻¹(t) ∩ B = τ(t ∩ A)`. -/
theorem preimage_onOpen_inter_eq (h : IsBiholomorphicPair A B τ σ) (t : Set (ComplexModel n)) :
    onOpen B σ ⁻¹' t ∩ B = τ '' (t ∩ A) := by
  ext y
  constructor
  · rintro ⟨hyt, hyB⟩
    rw [mem_preimage, onOpen_of_mem hyB] at hyt
    exact ⟨σ y, ⟨hyt, h.mapsTo_inv hyB⟩, h.right_inv y hyB⟩
  · rintro ⟨x, ⟨hxt, hxA⟩, rfl⟩
    refine ⟨?_, h.mapsTo hxA⟩
    rw [mem_preimage, onOpen_of_mem (h.mapsTo hxA), h.left_inv x hxA]
    exact hxt

/-- **The change of variables**: `σ_*((r λ)|_B) = |det Dτ| (r ∘ τ) λ|_A`. -/
theorem map_withDensity_restrict (h : IsBiholomorphicPair A B τ σ) (r : ComplexModel n → ℝ≥0∞) :
    ((volume.withDensity r).restrict B).map (onOpen B σ) =
      (volume.restrict A).withDensity fun x => ENNReal.ofReal |(fderiv ℝ τ x).det| * r (onOpen A τ
        x) := by
  ext t ht
  have hpre : MeasurableSet (onOpen B σ ⁻¹' t) := measurable_onOpen_inv h ht
  rw [Measure.map_apply (measurable_onOpen_inv h) ht, Measure.restrict_apply hpre,
    withDensity_apply _ (hpre.inter B.isOpen.measurableSet), withDensity_apply _ ht,
    Measure.restrict_restrict ht, preimage_onOpen_inter_eq h t]
  have hderiv : ∀ x ∈ t ∩ (A : Set (ComplexModel n)),
      HasFDerivWithinAt τ (fderiv ℝ τ x) (t ∩ (A : Set (ComplexModel n))) x := fun x hx =>
    (((differentiableAt_of_mem h hx.2).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  have hinj : InjOn τ (t ∩ (A : Set (ComplexModel n))) := fun x hx x' hx' hxx' => by
    rw [← h.left_inv x hx.2, ← h.left_inv x' hx'.2, hxx']
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (ht.inter A.isOpen.measurableSet)
    hderiv hinj]
  exact setLIntegral_congr_fun (ht.inter A.isOpen.measurableSet) fun x hx => by rw [onOpen_of_mem
    hx.2]

/-- **Singular measures stay singular**: `σ_*(s|_B) ⟂ λ` when `s ⟂ λ`. -/
theorem mutuallySingular_map (h : IsBiholomorphicPair A B τ σ) {s : Measure (ComplexModel n)}
    (hs : s ⟂ₘ volume) : (s.restrict B).map (onOpen B σ) ⟂ₘ volume := by
  obtain ⟨S, hSm, hs0, hvol⟩ := hs
  set N : Set (ComplexModel n) := σ '' (Sᶜ ∩ B)
  have hN : (volume : Measure (ComplexModel n)) N = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
      ((differentiableOn_inv h).mono inter_subset_right) (measure_mono_null inter_subset_left hvol)
  refine ⟨(toMeasurable volume N)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [Measure.map_apply (measurable_onOpen_inv h) (measurableSet_toMeasurable _ _).compl,
      Measure.restrict_apply (measurable_onOpen_inv h (measurableSet_toMeasurable _ _).compl)]
    refine measure_mono_null (fun y ⟨hy, hyB⟩ => ?_) hs0
    by_contra hyS
    rw [mem_preimage, onOpen_of_mem hyB] at hy
    exact hy (subset_toMeasurable _ _ ⟨y, ⟨hyS, hyB⟩, rfl⟩)
  · rw [compl_compl, measure_toMeasurable]
    exact hN

end Measures

/-! ### The absolutely continuous part of the pull-back -/

section AbsolutelyContinuous

open BedfordTaylor

variable {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n} {T :
    LocalProductCurrent n B q}

/-- The density of the pull-back is nonnegative on strongly positive forms, `σ_* σ_T`-almost
    everywhere. -/
theorem ae_pbDensity_nonneg (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    {γ : formSpan n q}
    (hγ : γ ∈ posCone n q) : ∀ᵐ x ∂pbMeasure σ hT, 0 ≤ pbDensity A τ σ hT γ x := by
  rw [pbMeasure, ae_map_iff (measurable_onOpen_inv h).aemeasurable
    (measurableSet_le measurable_const (measurable_pbDensity h hT γ))]
  filter_upwards [ae_restrict_of_ae (ae_densityForm_nonneg hT), ae_restrict_mem
    B.isOpen.measurableSet]
    with y hy hyB
  rw [onOpen_of_mem hyB, pbDensity_comp h hT γ hyB]
  exact hy _ (pullSpan_mem_posCone _ hγ)

theorem measurable_ofReal_pbDensity (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    (γ : formSpan n q) :
    Measurable fun x => ENNReal.ofReal (pbDensity A τ σ hT γ x) :=
  ENNReal.measurable_ofReal.comp (measurable_pbDensity h hT γ)

/-- The measure `L'(γ) σ_* σ_T` representing `(τ^* T)(γ)` for a strongly positive `γ`. -/
def pbCoeffMeasure (A : Opens (ComplexModel n)) (τ σ : ComplexModel n → ComplexModel n)
    (hT : IsPositive T)
    (γ : formSpan n q) : Measure (ComplexModel n) :=
  (pbMeasure σ hT).withDensity fun x => ENNReal.ofReal (pbDensity A τ σ hT γ x)

theorem integral_pbCoeffMeasure (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    {γ : formSpan n q}
    (hγ : γ ∈ posCone n q) (φ : 𝓓(A, ℝ)) : ∫ x, φ x ∂pbCoeffMeasure A τ σ hT γ = pullback h hT γ φ
      := by
  rw [pbCoeffMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_pbDensity h
    hT γ)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), pullback_apply_eq]
  refine integral_congr_ae ?_
  filter_upwards [ae_pbDensity_nonneg h hT hγ] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

theorem pbCoeffMeasure_compl (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    (γ : formSpan n q) :
    pbCoeffMeasure A τ σ hT γ ((A : Set (ComplexModel n))ᶜ) = 0 :=
  withDensity_absolutelyContinuous _ _ (pbMeasure_compl h hT)

theorem pbCoeffMeasure_lt_top (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    (γ : formSpan n q)
    (K : Set (ComplexModel n)) (hK : IsCompact K) (hKA : K ⊆ A) : pbCoeffMeasure A τ σ hT γ K < ⊤
      := by
  obtain ⟨C, hC⟩ := exists_abs_pbDensity_le h hT γ hK hKA
  rw [pbCoeffMeasure, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (pbDensity A τ σ hT γ x) ∂pbMeasure σ hT
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂pbMeasure σ hT :=
        setLIntegral_mono' hK.measurableSet fun x hx =>
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC x hx))
    _ = ENNReal.ofReal C * pbMeasure σ hT K := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (pbMeasure_lt_top h hT hK hKA)

/-- The Jacobian factor `|det Dτ(x)| (dσ_T/dλ)(τ x)` of the absolutely continuous part of
    `σ_* σ_T`. -/
def pbJacobianWeight (A : Opens (ComplexModel n)) (τ : ComplexModel n → ComplexModel n)
    (hT : IsPositive T)
    (x : ComplexModel n) : ℝ≥0∞ :=
  ENNReal.ofReal |(fderiv ℝ τ x).det| * hT.traceMeasure.rnDeriv volume (onOpen A τ x)

theorem measurable_pbJacobianWeight (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) :
    Measurable (pbJacobianWeight A τ hT) :=
  (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ τ)))).mul
    ((Measure.measurable_rnDeriv _ _).comp (measurable_onOpen h.holo.continuousOn))

/-- **The Lebesgue decomposition of `σ_* σ_T`**: `σ_*(σ_T^sing|_B)`, singular, plus
    `|det Dτ| (dσ_T/dλ ∘ τ) λ|_A`. -/
theorem pbMeasure_eq (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) :
    pbMeasure σ hT = ((sgMeasure hT).restrict B).map (onOpen B σ) +
      (volume.restrict A).withDensity (pbJacobianWeight A τ hT) := by
  rw [pbMeasure, ← sgMeasure_add_acMeasure hT, Measure.restrict_add, Measure.map_add _ _
    (measurable_onOpen_inv h),
    acMeasure, map_withDensity_restrict h]
  rfl

/-- The Lebesgue decomposition of the coefficient measure of the pull-back. -/
theorem pbCoeffMeasure_eq (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) (γ : formSpan n q)
    :
    pbCoeffMeasure A τ σ hT γ =
      (((sgMeasure hT).restrict B).map (onOpen B σ)).withDensity
          (fun x => ENNReal.ofReal (pbDensity A τ σ hT γ x)) +
        volume.withDensity ((A : Set (ComplexModel n)).indicator
          (pbJacobianWeight A τ hT * fun x => ENNReal.ofReal (pbDensity A τ σ hT γ x))) := by
  rw [pbCoeffMeasure, pbMeasure_eq h hT, withDensity_add_measure,
    ← withDensity_mul _ (measurable_pbJacobianWeight h hT) (measurable_ofReal_pbDensity h hT γ),
    withDensity_indicator A.isOpen.measurableSet]

/-- **`(τ^* T)_ac = τ^*(T_ac)` on a strongly positive form**: for almost every `x ∈ A`,
`acWeight'(x) L'_x(γ) = |det Dτ(x)| acWeight(τ x) L_{τ x}(Dσ(τ x)^* γ)`. -/
theorem ae_acDensity_pullback_of_mem_posCone (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T)
    {γ : formSpan n q} (hγ : γ ∈ posCone n q) :
    ∀ᵐ x ∂(volume : Measure (ComplexModel n)), x ∈ A →
      acWeight (isPositive_pullback h hT) x * densityForm (isPositive_pullback h hT) x γ =
        |(fderiv ℝ τ x).det| * (acWeight hT (τ x) * densityForm hT (τ x) (pullSpan q (fderiv ℂ σ
          (τ x)) γ)) := by
  have hrep := ae_eq_ofReal_acDensity (isPositive_pullback h hT) hγ
    (((measurable_pbJacobianWeight h hT).mul (measurable_ofReal_pbDensity h hT γ)).indicator
      A.isOpen.measurableSet)
    (pbCoeffMeasure_compl h hT γ) (pbCoeffMeasure_lt_top h hT γ) (integral_pbCoeffMeasure h hT hγ)
    ((mutuallySingular_map h (sgMeasure_mutuallySingular hT)).mono_ac
      (withDensity_absolutelyContinuous _ _)
      Measure.AbsolutelyContinuous.rfl)
    (pbCoeffMeasure_eq h hT γ)
  have hfin := ae_comp_of_ae h ((Measure.rnDeriv_lt_top hT.traceMeasure volume).mono fun y hy _ =>
    hy)
  have hnn := ae_comp_of_ae h ((ae_volume_acDensity_nonneg hT).mono fun y hy _ => hy)
  filter_upwards [hrep, hfin, hnn, ae_volume_acDensity_nonneg (isPositive_pullback h hT)]
    with x h1 h2 h3 h4 hxA
  simp only [indicator_of_mem hxA, Pi.mul_apply, pbJacobianWeight, onOpen_of_mem hxA,
    pbDensity_apply_of_mem hT γ hxA] at h1
  have hL := h3 hxA _ (pullSpan_mem_posCone (fderiv ℂ σ (τ x)) hγ)
  rw [mul_assoc, ← ENNReal.ofReal_toReal (h2 hxA).ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (abs_nonneg _)] at h1
  exact (ENNReal.ofReal_eq_ofReal_iff (h4 γ hγ) (mul_nonneg (abs_nonneg _) hL)).mp h1.symm

/-- The absolutely continuous coefficients of a positive current of any bidimension `(q,q)`
transform under biholomorphisms of open coordinate domains. This is the local, degree-general
version of Boucksom's Lemma 4.2 (iii), which treats positive `(1,1)`-currents and generically
finite holomorphic maps of compact Kähler manifolds. For almost every `x ∈ A`, the coefficient
on a constant test form `γ` acquires the real Jacobian factor and is evaluated on the test
form pulled back by the derivative of the inverse map. -/
theorem ae_acDensity_pullback (h : IsBiholomorphicPair A B τ σ) (hT : IsPositive T) :
    ∀ᵐ x ∂(volume : Measure (ComplexModel n)), x ∈ A → ∀ γ : formSpan n q,
      acWeight (isPositive_pullback h hT) x * densityForm (isPositive_pullback h hT) x γ =
        |(fderiv ℝ τ x).det| * (acWeight hT (τ x) * densityForm hT (τ x) (pullSpan q (fderiv ℂ σ
          (τ x)) γ)) := by
  let left (x : ComplexModel n) : formSpan n q →ₗ[ℝ] ℝ :=
    acWeight (isPositive_pullback h hT) x • densityForm (isPositive_pullback h hT) x
  let right (x : ComplexModel n) : formSpan n q →ₗ[ℝ] ℝ :=
    (|(fderiv ℝ τ x).det| * acWeight hT (τ x)) •
      (densityForm hT (τ x)).comp (pullSpan q (fderiv ℂ σ (τ x)))
  have agree := ae_forall_eq_of_posCone left right (P := fun x => x ∈ A) (fun γ hγ => by
    filter_upwards [ae_acDensity_pullback_of_mem_posCone h hT hγ] with x hx hxA
    simpa only [left, right, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, mul_assoc]
      using hx hxA)
  filter_upwards [agree] with x hx hxA γ
  simpa only [left, right, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, mul_assoc]
    using hx hxA γ

end AbsolutelyContinuous

/-! ### Derivatives of the biholomorphism -/

section Derivatives

open BedfordTaylor

variable {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}

/-- `Dσ(τ x) ∘ Dτ(x) = id` on `A`. -/
theorem fderiv_inv_comp (h : IsBiholomorphicPair A B τ σ) {x : ComplexModel n} (hx : x ∈ A) :
    (fderiv ℂ σ (τ x)).comp (fderiv ℂ τ x) = ContinuousLinearMap.id ℂ (ComplexModel n) := by
  have hev : σ ∘ τ =ᶠ[𝓝 x] id :=
    Filter.eventually_of_mem (A.isOpen.mem_nhds hx) fun y hy => h.left_inv y hy
  rw [← fderiv_comp x (differentiableAt_inv_of_mem h (h.mapsTo hx)) (differentiableAt_of_mem h
    hx), hev.fderiv_eq,
    fderiv_id]

/-- The real derivative of `τ` is its complex derivative. -/
theorem fderiv_real_eq (h : IsBiholomorphicPair A B τ σ) {x : ComplexModel n} (hx : x ∈ A) :
    fderiv ℝ τ x = (fderiv ℂ τ x).restrictScalars ℝ :=
  (differentiableAt_of_mem h hx).fderiv_restrictScalars ℝ

/-- The real determinant of a complex-linear map is `|det_ℂ|²`. -/
theorem det_restrictScalars_eq_normSq (S : ComplexModel n →L[ℂ] ComplexModel n) :
    (S.restrictScalars ℝ).det = Complex.normSq S.det :=
  normSq_det_eq_realDet (S : ComplexModel n →ₗ[ℂ] ComplexModel n)

/-- The complex Jacobian determinant of `τ` does not vanish on `A`. -/
theorem det_fderiv_ne_zero (h : IsBiholomorphicPair A B τ σ) {x : ComplexModel n} (hx : x ∈ A) :
    (fderiv ℂ τ x).det ≠ 0 := by
  have e : LinearMap.det ((fderiv ℂ σ (τ x) : ComplexModel n →ₗ[ℂ] ComplexModel n) ∘ₗ
      (fderiv ℂ τ x : ComplexModel n →ₗ[ℂ] ComplexModel n)) =
        LinearMap.det (LinearMap.id : ComplexModel n →ₗ[ℂ] ComplexModel n) := by
    change LinearMap.det (((fderiv ℂ σ (τ x)).comp (fderiv ℂ τ x) : ComplexModel n →L[ℂ]
      ComplexModel n) :
      ComplexModel n →ₗ[ℂ] ComplexModel n) = _
    rw [fderiv_inv_comp h hx]
    rfl
  rw [LinearMap.det_comp, LinearMap.det_id] at e
  exact right_ne_zero_of_mul_eq_one e

/-- Pull-back of a `(1,1)`-form along a complex-linear map is of type `(1,1)`. -/
theorem isOneOne_comp_restrictScalars (S : ComplexModel n →L[ℂ] ComplexModel n) {α : RealForm n 2}
    (hα : IsOneOne α) : IsOneOne (α.compContinuousLinearMap (S.restrictScalars ℝ)) := by
  intro u v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have e : (⇑(S.restrictScalars ℝ) ∘ ![Complex.I • u, Complex.I • v]) = ![Complex.I • S u,
    Complex.I • S v] := by
    funext i
    fin_cases i <;> simp [S.map_smul]
  have e' : (⇑(S.restrictScalars ℝ) ∘ ![u, v]) = ![S u, S v] := by
    funext i
    fin_cases i <;> rfl
  rw [e, e', hα]

/-- The pull-back along `S` as `CoordinateDensityHermitian.compLinearMap`. -/
theorem compContinuousLinearMap_restrictScalars_eq (S : ComplexModel n →L[ℂ] ComplexModel n)
    (α : RealForm n 2) :
    α.compContinuousLinearMap (S.restrictScalars ℝ) = compLinearMap α (S : ComplexModel n →ₗ[ℂ]
      ComplexModel n) := by
  ext v
  rfl

end Derivatives

end SGPT.Foundations.Analysis.Pending.LocalCurrentPullback

end
