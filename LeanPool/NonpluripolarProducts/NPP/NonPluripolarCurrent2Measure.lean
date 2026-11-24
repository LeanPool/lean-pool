/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentManifold
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ProductTestForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.FiniteMeasureGluing

/-!
# The measures `T ∧ α^q` of positive currents against variable forms: locality and invariance

Source: `chapter_npp.tex`, `def:npp:L69` (`eq:welldefinepluri` uses the measures
`(⋀ⱼ dd^c (φⱼ ∨ (-k)))|_U ∧ ω^{dim U - p}` for smooth positive `(1,1)`-forms `ω` on open subsets
`U` of the manifold); Xia, *Foundations of pluripotential theory*, the paragraph after
`prop:nonpluripolar-local-calculus` (comparison of trace measures in two coordinate systems,
`eq:trace-measure-form-comparison`).

For a positive current `T` of bidimension `(q,q)` on an open `U ⊆ ℂⁿ` and a semipositive
`(1,1)`-form `α` on `U`, `T ∧ α^q` is `NonPluripolarCurrent.wedgePowerMeasure T α`
(`L_x(α(x)^q) σ_T`).  This file proves:

* `wedgePowerMeasure_eq_of_integral_eq` — **the measure does not depend on the representation of
  the coefficients**: if `T(γ)(φ) = ∫ φ g_x(γ) dν` for a locally finite `ν` carried by `U` and
  bounded measurable `g`, nonnegative on the strongly positive cone, then
  `T ∧ α^q = g_x(α(x)^q) ν`;
* `wedgePowerMeasure_restrict` — `(T|_V) ∧ α^q = (T ∧ α^q)|_V`;
* `wedgePowerMeasure_pullback` — **biholomorphic invariance**: for a biholomorphism
  `τ : A → B` with inverse `σ` and `β = τ^* α` on `A`, `(τ^* T) ∧ β^q = σ_*((T ∧ α^q)|_B)`.

These are the local ingredients of the measures of manifold currents over arbitrary open sets
(`SGPT.NPP.NonPluripolarCurrent2Opens`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

/-! ### Powers of pulled-back forms -/

section Forms

theorem formPower_compContinuousLinearMap (L : (ComplexModel n) →L[ℝ] (ComplexModel n))
    (β : RealForm n 2) :
    ∀ q, (formPower β q).compContinuousLinearMap L = formPower (β.compContinuousLinearMap L) q
  | 0 => by
    rw [formPower_zero, formPower_zero, coordinateWedgeUnit_compContinuousLinearMap]
  | q + 1 => by
    rw [formPower_succ, formPower_succ, MongeAmpere.coordinateWedge_compContinuousLinearMap,
      formPower_compContinuousLinearMap L β q]

/-- `S^*(β^q) = (S^* β)^q` in `Λ_q`. -/
theorem pullSpan_powerSpan (S : (ComplexModel n) →L[ℂ] (ComplexModel n)) {β : RealForm n 2} (hβ :
    IsSemipositiveOneOne β)
    (q : ℕ) :
    pullSpan q S (powerSpan q β) = powerSpan q (β.compContinuousLinearMap (S.restrictScalars ℝ))
      := by
  have hβ' := hβ.comp (S.restrictScalars ℝ) (fun v => S.map_smul Complex.I v)
  apply Subtype.ext
  rw [coe_pullSpan, coe_powerSpan hβ, coe_powerSpan hβ', formPower_compContinuousLinearMap]

theorem contDiffOn_formPower {U : Set (ComplexModel n)} {α : (ComplexModel n) → RealForm n 2} (hα
    : ContDiffOn ℝ ∞ α U) :
    ∀ q, ContDiffOn ℝ ∞ (fun x => formPower (α x) q) U
  | 0 => contDiffOn_const
  | q + 1 => ProductTestForms.contDiffOn_coordinateWedge (contDiffOn_formPower hα q) hα

end Forms

/-! ### Representations of the coefficients -/

section Rep

variable {U : Opens (ComplexModel n)} {q : ℕ}

open Classical in
/-- The coefficients of `α(x)^q` in the basis of `Λ_q`, on `U` (and `0` off `U`). -/
def powerCoeff (U : Opens (ComplexModel n)) (α : (ComplexModel n) → RealForm n 2) (q : ℕ)
    (i : Fin (Module.finrank ℝ (formSpan n q))) : (ComplexModel n) → ℝ :=
  (U : Set (ComplexModel n)).piecewise (formCoeff (fun x => formPower (α x) q) i) fun _ => 0

theorem measurable_powerCoeff {α : (ComplexModel n) → RealForm n 2} (hα : ContDiffOn ℝ ∞ α U)
    (i : Fin (Module.finrank ℝ (formSpan n q))) : Measurable (powerCoeff U α q i) := by
  classical
  exact (contDiffOn_formCoeff (contDiffOn_formPower hα q) i).continuousOn.measurable_piecewise
    continuousOn_const U.isOpen.measurableSet

theorem isLocallyBoundedOn_powerCoeff {α : (ComplexModel n) → RealForm n 2} (hα : ContDiffOn ℝ ∞ α
    U)
    (i : Fin (Module.finrank ℝ (formSpan n q))) : IsLocallyBoundedOn (powerCoeff U α q i) U := by
  classical
  intro K hK hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((contDiffOn_formCoeff (contDiffOn_formPower hα q) i).continuousOn.mono hKU)
  refine ⟨C, fun x hx => ?_⟩
  rw [powerCoeff, Set.piecewise_eq_of_mem _ _ _ (hKU hx)]
  simpa [Real.norm_eq_abs] using hC x hx

/-- On `U`, `α(x)^q = ∑ᵢ cᵢ(x) bᵢ`. -/
theorem powerSpan_eq_sum {α : (ComplexModel n) → RealForm n 2} (hαp : ∀ x ∈ U,
    IsSemipositiveOneOne (α x))
    {x : (ComplexModel n)} (hx : x ∈ U) :
    powerSpan q (α x) = ∑ i, powerCoeff U α q i x • formBasis n q i := by
  classical
  apply Subtype.ext
  rw [coe_powerSpan (hαp x hx), Submodule.coe_sum]
  have hmem : formPower (α x) q ∈ formSpan n q :=
    mem_formSpan_of_mem_spCone (formPower_mem_spCone (hαp x hx) q)
  rw [eq_sum_formCoeff (α := fun x => formPower (α x) q) hmem]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, powerCoeff, Set.piecewise_eq_of_mem _ _ _ hx]

/-- `L(α(x)^q) = ∑ᵢ cᵢ(x) L(bᵢ)` on `U`. -/
theorem apply_powerSpan_eq_sum {α : (ComplexModel n) → RealForm n 2} (hαp : ∀ x ∈ U,
    IsSemipositiveOneOne (α x))
    {x : (ComplexModel n)} (hx : x ∈ U) (L : formSpan n q →ₗ[ℝ] ℝ) :
    L (powerSpan q (α x)) = ∑ i, powerCoeff U α q i x * L (formBasis n q i) := by
  rw [powerSpan_eq_sum hαp hx, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem isLocalDensity_densityForm {T : LocalProductCurrent n U q} (hT : IsPositive T)
    (γ : formSpan n q) : IsLocalDensity (U := U) hT.traceMeasure fun x => densityForm hT x γ := by
  obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le hT γ
  exact ⟨hT.traceMeasure_compl, fun K hK hKU => hT.traceMeasure_lt_top hK hKU,
    measurable_densityForm hT γ, fun _ _ _ => ⟨C, fun x _ => hC x⟩⟩

/-- The order-unit comparison `L(α^q) ≤ c^q L(ω₀^q)` for `α ≤ c ω₀`. -/
theorem apply_powerSpan_le {L : formSpan n q →ₗ[ℝ] ℝ} (hL : ∀ γ ∈ posCone n q, 0 ≤ L γ)
    {β : RealForm n 2} (hβ : IsSemipositiveOneOne β) {c : ℝ}
    (hc : IsSemipositiveOneOne (c • kahlerForm n - β)) :
    L (powerSpan q β) ≤ c ^ q * L (kahlerPower n q) := by
  have hmem : (c ^ q • kahlerPower n q - powerSpan q β : formSpan n q) ∈ posCone n q := by
    change ((c ^ q • kahlerPower n q - powerSpan q β : formSpan n q) :
      RealForm n (2 * q)) ∈ spCone q
    rw [Submodule.coe_sub, Submodule.coe_smul, coe_powerSpan hβ]
    have h := formPower_sub_mem_spCone hβ hc q
    rwa [formPower_smul] at h
  have h := hL _ hmem
  rw [map_sub, map_smul, smul_eq_mul, sub_nonneg] at h
  exact h

/-- Nonnegativity on the strongly positive cone, almost everywhere for all forms at once (a
countable dense subset of the cone and continuity of linear forms). -/
theorem ae_forall_posCone_nonneg {ν : Measure (ComplexModel n)} {g : (ComplexModel n)
    → formSpan n q →ₗ[ℝ] ℝ}
    (hgp : ∀ γ ∈ posCone n q, ∀ᵐ x ∂ν, 0 ≤ g x γ) :
    ∀ᵐ x ∂ν, ∀ γ ∈ posCone n q, 0 ≤ g x γ := by
  obtain ⟨D, hDC, hDc, hCD⟩ :=
    (IsSeparable.of_separableSpace (posCone n q)).exists_countable_dense_subset
  have _ := hDc.to_subtype
  have h : ∀ᵐ x ∂ν, ∀ γ : D, 0 ≤ g x γ := by
    rw [ae_all_iff]
    exact fun γ => hgp γ (hDC γ.2)
  filter_upwards [h] with x hx γ hγ
  have hcont : Continuous (g x) := (g x).continuous_of_finiteDimensional
  have hclosed : IsClosed {γ : formSpan n q | 0 ≤ g x γ} := isClosed_le continuous_const hcont
  exact closure_minimal (fun γ hγD => hx ⟨γ, hγD⟩) hclosed (hCD hγ)

/-- **The measure `T ∧ α^q` does not depend on the representation of the coefficients.** -/
theorem wedgePowerMeasure_eq_of_integral_eq {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {ν : Measure (ComplexModel n)} (hνc : ν ((U : Set (ComplexModel n))ᶜ) = 0)
    (hνK : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → ν K < ⊤) (g : (ComplexModel n)
      → formSpan n q →ₗ[ℝ] ℝ)
    (hgm : ∀ γ, Measurable fun x => g x γ) (hgb : ∀ γ, IsLocallyBoundedOn (fun x => g x γ) U)
    (hgp' : ∀ γ ∈ posCone n q, ∀ᵐ x ∂ν, 0 ≤ g x γ)
    (hrep : ∀ γ (φ : 𝓓(U, ℝ)), T γ φ = ∫ x, φ x * g x γ ∂ν)
    {α : (ComplexModel n) → RealForm n 2} (hα : ContDiffOn ℝ ∞ α U)
    (hαp : ∀ x ∈ U, IsSemipositiveOneOne (α x)) :
    wedgePowerMeasure T α = ν.withDensity fun x => ENNReal.ofReal (g x (powerSpan q (α x))) := by
  have hgp := ae_forall_posCone_nonneg hgp'
  set b := formBasis n q
  set c := powerCoeff U α q
  have hcm := measurable_powerCoeff (q := q) hα
  have hcb := isLocallyBoundedOn_powerCoeff (q := q) hα
  -- the measurable densities agreeing with the given ones on `U`
  set d : (ComplexModel n) → ℝ := fun x => ∑ i, c i x * densityForm hT x (b i) with hd
  set d' : (ComplexModel n) → ℝ := fun x => ∑ i, c i x * g x (b i) with hd'
  have hdm : Measurable d := Finset.measurable_sum _ fun i _ =>
    (hcm i).mul (measurable_densityForm hT (b i))
  have hd'm : Measurable d' := Finset.measurable_sum _ fun i _ => (hcm i).mul (hgm (b i))
  have hdU : ∀ x ∈ U, densityForm hT x (powerSpan q (α x)) = d x := fun x hx =>
    apply_powerSpan_eq_sum hαp hx _
  have hd'U : ∀ x ∈ U, g x (powerSpan q (α x)) = d' x := fun x hx =>
    apply_powerSpan_eq_sum hαp hx _
  have haeU : ∀ᵐ x ∂hT.traceMeasure, x ∈ (U : Set (ComplexModel n)) :=
    measure_eq_zero_iff_ae_notMem.mp hT.traceMeasure_compl |>.mono fun x hx => by simpa using hx
  have haeU' : ∀ᵐ x ∂ν, x ∈ (U : Set (ComplexModel n)) :=
    measure_eq_zero_iff_ae_notMem.mp hνc |>.mono fun x hx => by simpa using hx
  have e1 : wedgePowerMeasure T α = hT.traceMeasure.withDensity (posDensity d) := by
    rw [wedgePowerMeasure, dite_eq_left hT]
    refine withDensity_congr_ae ?_
    filter_upwards [haeU] with x hx
    rw [hdU x hx]
    rfl
  have e2 : (ν.withDensity fun x => ENNReal.ofReal (g x (powerSpan q (α x)))) =
      ν.withDensity (posDensity d') := by
    refine withDensity_congr_ae ?_
    filter_upwards [haeU'] with x hx
    rw [hd'U x hx]
    rfl
  rw [e1, e2]
  have hdpos : ∀ᵐ x ∂hT.traceMeasure, 0 ≤ d x := by
    filter_upwards [haeU, ae_densityForm_nonneg hT] with x hx hpos
    rw [← hdU x hx]
    exact hpos _ (by
      change ((powerSpan q (α x) : formSpan n q) : RealForm n (2 * q)) ∈ spCone q
      rw [coe_powerSpan (hαp x hx)]
      exact formPower_mem_spCone (hαp x hx) q)
  have hd'pos : ∀ᵐ x ∂ν, 0 ≤ d' x := by
    filter_upwards [haeU', hgp] with x hx hpos
    rw [← hd'U x hx]
    exact hpos _ (by
      change ((powerSpan q (α x) : formSpan n q) : RealForm n (2 * q)) ∈ spCone q
      rw [coe_powerSpan (hαp x hx)]
      exact formPower_mem_spCone (hαp x hx) q)
  -- the comparison on each basis element
  have hloc : ∀ i, IsLocalDensity (U := U) hT.traceMeasure fun x => densityForm hT x (b i) :=
    fun i => isLocalDensity_densityForm hT (b i)
  have hloc' : ∀ i, IsLocalDensity (U := U) ν fun x => g x (b i) :=
    fun i => ⟨hνc, hνK, hgm (b i), hgb (b i)⟩
  have hbasis : ∀ (i) (w : (ComplexModel n) → ℝ), IsTestWeight (U := U) w →
      ∫ x, densityForm hT x (b i) * w x ∂hT.traceMeasure = ∫ x, g x (b i) * w x ∂ν := by
    intro i w hw
    refine integral_eq_of_forall_testFunction (hloc i) (hloc' i) (fun ψ => ?_) hw
    have h1 := apply_eq_integral_densityForm hT (b i) ψ
    have h2 := hrep (b i) ψ
    rw [h1] at h2
    simp only [mul_comm (ψ _)] at h2
    exact h2
  -- local finiteness
  have hfin : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ᵐ x ∂ν, x ∈ K → d' x ≤ C := by
    intro K hK hKU
    obtain ⟨c₀, hc₀0, hc₀⟩ := exists_smul_kahlerForm_sub hK (hα.continuousOn.mono hKU)
      fun x hx => (hαp x (hKU hx)).1
    obtain ⟨C, hC⟩ := hgb (kahlerPower n q) K hK hKU
    refine ⟨c₀ ^ q * C, ?_⟩
    filter_upwards [hgp] with x hx hxK
    rw [← hd'U x (hKU hxK)]
    refine (apply_powerSpan_le hx (hαp x (hKU hxK)) (hc₀ x hxK)).trans ?_
    have hc0 : 0 ≤ c₀ ^ q := pow_nonneg hc₀0 q
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hC x hxK)) hc0
  refine LocalBedfordTaylorLocality.eq_of_forall_testFunction_integral_eq (U := U)
    (withDensity_absolutelyContinuous _ _ hT.traceMeasure_compl)
    (withDensity_absolutelyContinuous _ _ hνc) ?_ ?_ fun φ => ?_
  · intro K hK hKU
    rw [← e1]
    obtain ⟨c₀, -, hc₀⟩ := exists_smul_kahlerForm_sub hK (hα.continuousOn.mono hKU)
      fun x hx => (hαp x (hKU hx)).1
    have h := wedgePowerMeasure_le hT hK.measurableSet MeasurableSet.univ
      (fun x hx => hαp x (hKU hx)) hc₀
    rw [inter_univ] at h
    exact h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hT.traceMeasure_lt_top hK hKU))
  · intro K hK hKU
    obtain ⟨C, hC⟩ := hfin K hK hKU
    rw [withDensity_apply _ hK.measurableSet]
    calc ∫⁻ x in K, posDensity d' x ∂ν ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae hC] with x hx h
          exact ENNReal.ofReal_le_ofReal (h hx)
      _ = ENNReal.ofReal C * ν K := by rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hνK K hK hKU)
  · rw [integral_withDensity_posDensity _ hdm, integral_withDensity_posDensity _ hd'm]
    have e3 : ∫ x, max (d x) 0 * φ x ∂hT.traceMeasure =
        ∑ i, ∫ x, densityForm hT x (b i) * (φ x * c i x) ∂hT.traceMeasure := by
      rw [← integral_finsetSum _ fun i _ => (hloc i).integrable (isTestWeight_mul φ (hcm i)
        (hcb i))]
      refine integral_congr_ae ?_
      filter_upwards [hdpos] with x hx
      rw [max_eq_left hx, hd, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have e4 : ∫ x, max (d' x) 0 * φ x ∂ν = ∑ i, ∫ x, g x (b i) * (φ x * c i x) ∂ν := by
      rw [← integral_finsetSum _ fun i _ => (hloc' i).integrable (isTestWeight_mul φ (hcm i)
        (hcb i))]
      refine integral_congr_ae ?_
      filter_upwards [hd'pos] with x hx
      rw [max_eq_left hx, hd', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e3, e4]
    exact Finset.sum_congr rfl fun i _ => hbasis i _ (isTestWeight_mul φ (hcm i) (hcb i))

end Rep

/-! ### Restriction and biholomorphic invariance -/

section Invariance

variable {q : ℕ}

/-- **`(T|_V) ∧ α^q = (T ∧ α^q)|_V`.** -/
theorem wedgePowerMeasure_restrict {U V : Opens (ComplexModel n)} {T : LocalProductCurrent n U q}
    (hT : IsPositive T) (hVU : V ≤ U) (α : (ComplexModel n) → RealForm n 2) :
    wedgePowerMeasure (LocalBedfordTaylorLocality.restrict hVU T) α =
      (wedgePowerMeasure T α).restrict V := by
  have hT' := LocalBedfordTaylorLocality.isPositive_restrict hT hVU
  rw [wedgePowerMeasure, dite_eq_left hT', wedgePowerMeasure, dite_eq_left hT,
    restrict_withDensity V.isOpen.measurableSet,
    ← LocalBedfordTaylorLocality.traceMeasure_restrict hT hVU]
  refine withDensity_congr_ae ?_
  filter_upwards [LocalCurrentPullbackDdc.ae_densityForm_restrict_eq hT hVU] with x hx
  rw [hx]

/-- Push-forward and densities: `(F_* μ).withDensity G = F_*(μ.withDensity (G ∘ F))`. -/
theorem map_withDensity_comp {μ : Measure (ComplexModel n)} {F : (ComplexModel n)
    → (ComplexModel n)} (hF : Measurable F) {G : (ComplexModel n) → ℝ≥0∞}
    (hG : Measurable G) : (μ.map F).withDensity G = (μ.withDensity (G ∘ F)).map F := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply hF hs, withDensity_apply _ (hF hs),
    ← lintegral_indicator hs, lintegral_map (hG.indicator hs) hF, ← lintegral_indicator (hF hs)]
  rfl

/-- **Biholomorphic invariance of `T ∧ α^q`**: for a biholomorphism `τ : A → B` with inverse
`σ`, a positive current `S` on `B` and a `(1,1)`-form `α` on `B` whose pull-back `β = τ^* α` is
smooth and semipositive on `A`, `(τ^* S) ∧ β^q = σ_*((S ∧ α^q)|_B)`. -/
theorem wedgePowerMeasure_pullback {A B : Opens (ComplexModel n)} {τ σ : (ComplexModel n)
    → (ComplexModel n)}
    (h : BedfordTaylor.IsBiholomorphicPair A B τ σ) {S : LocalProductCurrent n B q}
    (hS : IsPositive S) {α β : (ComplexModel n) → RealForm n 2} (hβ : ContDiffOn ℝ ∞ β A)
    (hβp : ∀ x ∈ A, IsSemipositiveOneOne (β x))
    (hβα : ∀ x ∈ A,
      β x = (α (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ)) :
    wedgePowerMeasure (pullback h hS) β = ((wedgePowerMeasure S α).restrict B).map (onOpen B σ)
      := by
  set g : (ComplexModel n) → formSpan n q →ₗ[ℝ] ℝ := fun x =>
    (densityForm hS (onOpen A τ x)).comp (pullSpan q (fderiv ℂ σ (onOpen A τ x))) with hg
  have hgx : ∀ γ x, g x γ = pbDensity A τ σ hS γ x := fun _ _ => rfl
  have hrep := wedgePowerMeasure_eq_of_integral_eq (isPositive_pullback h hS)
    (pbMeasure_compl h hS) (fun K hK hKA => pbMeasure_lt_top h hS hK hKA) g
    (fun γ => measurable_pbDensity h hS γ)
    (fun γ K hK hKA => exists_abs_pbDensity_le h hS γ hK hKA)
    (fun γ hγ => ae_pbDensity_nonneg h hS hγ) (fun γ φ => pullback_apply_eq h hS γ φ) hβ hβp
  set d : (ComplexModel n) → ℝ := fun x => ∑ i, powerCoeff A β q i x * g x (formBasis n q i)
    with hd
  have hdm : Measurable d := Finset.measurable_sum _ fun i _ =>
    (measurable_powerCoeff hβ i).mul (measurable_pbDensity h hS _)
  have haeA : ∀ᵐ x ∂pbMeasure σ hS, x ∈ (A : Set (ComplexModel n)) :=
    measure_eq_zero_iff_ae_notMem.mp (pbMeasure_compl h hS) |>.mono fun x hx => by simpa using hx
  have e1 : (pbMeasure σ hS).withDensity (fun x => ENNReal.ofReal (g x (powerSpan q (β x)))) =
      (pbMeasure σ hS).withDensity (posDensity d) := by
    refine withDensity_congr_ae ?_
    filter_upwards [haeA] with x hx
    rw [apply_powerSpan_eq_sum hβp hx]
    rfl
  rw [hrep, e1, pbMeasure, map_withDensity_comp (G := posDensity d) (measurable_onOpen_inv h)
      hdm.ennreal_ofReal,
    wedgePowerMeasure, dite_eq_left hS, restrict_withDensity B.isOpen.measurableSet]
  congr 1
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem B.isOpen.measurableSet] with y hy
  have hσy : σ y ∈ A := h.mapsTo_inv hy
  simp only [Function.comp_apply, onOpen_of_mem hy]
  change ENNReal.ofReal (d (σ y)) = ENNReal.ofReal (densityForm hS y (powerSpan q (α y)))
  rw [hd]
  simp only
  rw [← apply_powerSpan_eq_sum hβp hσy, hgx, pbDensity_comp h hS _ hy,
    pullSpan_powerSpan _ (hβp _ hσy), hβα _ hσy, h.right_inv y hy]
  congr 3
  have hsymm : BedfordTaylor.IsBiholomorphicPair B A σ τ :=
    ⟨h.holo_inv, h.holo, h.mapsTo_inv, h.mapsTo, h.right_inv, h.left_inv⟩
  have hid := fderiv_inv_comp hsymm hy
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  have := congrArg (fun L : (ComplexModel n) →L[ℂ] (ComplexModel n) => L (v i)) hid
  simpa using this

end Invariance

end SGPT.NPP.NonPluripolarCurrent
