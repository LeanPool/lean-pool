/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DistributionRestriction
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalProductCurrents

/-! # Restriction of local positive currents and their trace measures -/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality

open FirstPass StronglyPositiveForms LocalProductCurrents

variable {n : ℕ}

local notation "E" => ComplexModel n

variable {U V : Opens (ComplexModel n)}

/-! ### Measures carried by an open set -/

/-- **Uniqueness of measures carried by an open set.** -/
theorem eq_of_forall_testFunction_integral_eq {μ ν : Measure E}
    (hμ : μ ((U : Set E)ᶜ) = 0) (hν : ν ((U : Set E)ᶜ) = 0)
    (hμK : ∀ K : Set E, IsCompact K → K ⊆ U → μ K < ⊤)
    (hνK : ∀ K : Set E, IsCompact K → K ⊆ U → ν K < ⊤)
    (h : ∀ φ : 𝓓(U, ℝ), ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) : μ = ν := by
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have hemb := IsPositive.measurableEmbedding_val (U := U)
  have hloc : ∀ (ρ : Measure E), (∀ K : Set E, IsCompact K → K ⊆ U → ρ K < ⊤) →
      IsLocallyFiniteMeasure (ρ.comap (Subtype.val : U → E)) := by
    intro ρ hρ
    refine ⟨fun x => ?_⟩
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x
    refine ⟨K, hKn, ?_⟩
    rw [hemb.comap_apply]
    exact hρ _ (hK.image continuous_subtype_val) (image_subset_iff.mpr fun y _ => y.2)
  have hmap : ∀ (ρ : Measure E), ρ ((U : Set E)ᶜ) = 0 →
      (ρ.comap (Subtype.val : U → E)).map Subtype.val = ρ := by
    intro ρ hρ
    rw [hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.mp hρ |>.mono
      fun x hx => by simpa using hx)
  have _ := hloc μ hμK
  have _ := hloc ν hνK
  have heq : μ.comap (Subtype.val : U → E) = ν.comap (Subtype.val : U → E) := by
    apply Pending.Measure.eq_of_testFunction_integral_eq
    intro φ
    have e1 := hemb.integral_map (μ := μ.comap Subtype.val) (fun x => φ x)
    have e2 := hemb.integral_map (μ := ν.comap Subtype.val) (fun x => φ x)
    rw [hmap μ hμ] at e1
    rw [hmap ν hν] at e2
    rw [← e1, ← e2]
    exact h φ
  rw [← hmap μ hμ, ← hmap ν hν, heq]

/-! ### Restriction of currents -/

/-- Extension of test functions by zero from `V ≤ U` to `U`. -/
def extTest (_hVU : V ≤ U) : 𝓓(V, ℝ) →L[ℝ] 𝓓(U, ℝ) := TestFunction.monoCLM ℝ

@[simp] theorem extTest_apply (hVU : V ≤ U) (φ : 𝓓(V, ℝ)) (x : E) :
    extTest hVU φ x = φ x := by
  simp [extTest, hVU]

/-- Restriction of distributions to `V ≤ U`. -/
def restrictDist (hVU : V ≤ U) : 𝓓'(U, ℝ) →ₗ[ℝ] 𝓓'(V, ℝ) where
  toFun T := SGPT.Foundations.Analysis.restrictDistribution T hVU
  map_add' _ _ := ContinuousLinearMap.add_comp _ _ _
  map_smul' _ _ := ContinuousLinearMap.smul_comp _ _ _

variable {q : ℕ}

/-- **Restriction** `T|_V` of a current of bidimension `(q,q)` on `U`. -/
def restrict (hVU : V ≤ U) (T : LocalProductCurrent n U q) : LocalProductCurrent n V q :=
  restrictDist hVU ∘ₗ T

@[simp] theorem restrict_apply (hVU : V ≤ U) (T : LocalProductCurrent n U q) (γ : formSpan n q)
    (φ : 𝓓(V, ℝ)) : restrict hVU T γ φ = T γ (extTest hVU φ) := rfl

/-- Restriction to the whole domain fixes a current. -/
theorem restrict_self (hUU : U ≤ U) (T : LocalProductCurrent n U q) : restrict hUU T = T := by
  ext γ φ
  exact DFunLike.congr_fun
    (SGPT.Foundations.Analysis.restrictDistribution_self (T γ)) φ

/-- Restricting in two steps agrees with restricting directly. -/
theorem restrict_restrict {V W : Opens (ComplexModel n)} (hWV : W ≤ V) (hVU : V ≤ U)
    (T : LocalProductCurrent n U q) :
    restrict hWV (restrict hVU T) = restrict (hWV.trans hVU) T := by
  ext γ φ
  exact DFunLike.congr_fun
    (SGPT.Foundations.Analysis.restrictDistribution_trans (T γ) hWV hVU) φ

theorem isPositive_restrict {T : LocalProductCurrent n U q} (hT : IsPositive T) (hVU : V ≤ U) :
    IsPositive (restrict hVU T) := by
  intro ι _ γ φ hγ
  simp only [restrict_apply]
  exact hT ι γ (fun i => extTest hVU (φ i)) fun x => by simpa using hγ x

/-! ### Trace measure, densities and multiplication by functions -/

/-- A test function on `V` vanishes off `V`. -/
theorem testFunction_eq_zero_of_notMem (φ : 𝓓(V, ℝ)) {x : E} (hx : x ∉ (V : Set E)) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)

/-- Integrals of `φ · g` for a test function `φ` on `V` see only the restriction of the measure
to `V`. -/
theorem integral_restrict_mul (φ : 𝓓(V, ℝ)) (μ : Measure E) (g : E → ℝ) :
    ∫ x, φ x * g x ∂(μ.restrict V) = ∫ x, φ x * g x ∂μ :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [testFunction_eq_zero_of_notMem φ hx, zero_mul]

/-- **The trace measure of the restriction is the restriction of the trace measure.** -/
theorem traceMeasure_restrict {T : LocalProductCurrent n U q} (hT : IsPositive T) (hVU : V ≤ U) :
    (isPositive_restrict hT hVU).traceMeasure = hT.traceMeasure.restrict V := by
  apply eq_of_forall_testFunction_integral_eq (U := V)
  · exact (isPositive_restrict hT hVU).traceMeasure_compl
  · rw [Measure.restrict_apply' V.isOpen.measurableSet]
    simp
  · exact fun K hK hKV => (isPositive_restrict hT hVU).traceMeasure_lt_top hK hKV
  · intro K hK hKV
    rw [Measure.restrict_apply hK.measurableSet]
    exact (measure_mono inter_subset_left).trans_lt
      (hT.traceMeasure_lt_top hK (hKV.trans (SetLike.coe_subset_coe.mpr hVU)))
  · intro φ
    rw [(isPositive_restrict hT hVU).integral_traceMeasure, restrict_apply,
      ← hT.integral_traceMeasure]
    have hf : (extTest hVU φ : E → ℝ) = (φ : E → ℝ) := funext (extTest_apply hVU φ)
    rw [hf]
    have := integral_restrict_mul φ hT.traceMeasure (fun _ => 1)
    simp only [mul_one] at this
    exact this.symm

/-- **The densities of the restriction are the restrictions of the densities** (almost
everywhere). -/
theorem density_restrict_ae {T : LocalProductCurrent n U q} (hT : IsPositive T) (hVU : V ≤ U)
    (γ : formSpan n q) :
    (isPositive_restrict hT hVU).density γ
      =ᵐ[(isPositive_restrict hT hVU).traceMeasure] hT.density γ := by
  obtain ⟨C, -, hC⟩ := (isPositive_restrict hT hVU).exists_abs_density_le γ
  obtain ⟨D, -, hD⟩ := hT.exists_abs_density_le γ
  refine (isPositive_restrict hT hVU).ae_eq_of_forall_integral_eq
    ((isPositive_restrict hT hVU).measurable_density γ) (hT.measurable_density γ) ⟨C, hC⟩
    ⟨D, hD⟩ fun φ => ?_
  rw [← (isPositive_restrict hT hVU).apply_eq_integral_density, restrict_apply,
    hT.apply_eq_integral_density, traceMeasure_restrict hT hVU, integral_restrict_mul]
  have hf : (extTest hVU φ : E → ℝ) = (φ : E → ℝ) := funext (extTest_apply hVU φ)
  rw [hf]

theorem isLocallyBoundedOn_mono {u : E → ℝ} (hu : IsLocallyBoundedOn u U) (hVU : V ≤ U) :
    IsLocallyBoundedOn u V :=
  fun K hK hKV => hu K hK (hKV.trans (SetLike.coe_subset_coe.mpr hVU))

/-- **Multiplication by a locally bounded Borel function commutes with restriction.** -/
theorem mulBorel_restrict {T : LocalProductCurrent n U q} (hT : IsPositive T) (hVU : V ≤ U)
    {u : E → ℝ} (hu : Measurable u) (hb : IsLocallyBoundedOn u U) :
    mulBorel (restrict hVU T) u = restrict hVU (mulBorel T u) := by
  ext γ φ
  rw [restrict_apply, mulBorel_apply hT hu hb,
    mulBorel_apply (isPositive_restrict hT hVU) hu (isLocallyBoundedOn_mono hb hVU)]
  have hf : (extTest hVU φ : E → ℝ) = (φ : E → ℝ) := funext (extTest_apply hVU φ)
  rw [hf]
  have e : ∫ x, φ x * (u x * (isPositive_restrict hT hVU).density γ x)
        ∂(isPositive_restrict hT hVU).traceMeasure =
      ∫ x, φ x * (u x * hT.density γ x) ∂(isPositive_restrict hT hVU).traceMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [density_restrict_ae hT hVU γ] with x hx
    rw [hx]
  rw [e, traceMeasure_restrict hT hVU, integral_restrict_mul]

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
