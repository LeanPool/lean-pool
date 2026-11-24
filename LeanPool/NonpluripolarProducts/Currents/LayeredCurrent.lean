/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentPullbackDdc

/-!
# Currents defined by layered density forms

A sequence of positive currents supplies one trace measure and one density form
for each measurable layer. Their sum and the density of the first layer give
the data for a current whenever the measure is finite on compact subsets.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

/-! ### Uniform bounds of density forms -/

section Density

variable {U : Opens (ComplexModel n)} {q : ℕ} {T : LocalProductCurrent n U q}

/-- The density of the trace form `ω₀^q` with respect to the trace measure is `1`. -/
theorem density_kahlerPower_ae (hT : IsPositive T) :
    hT.density (kahlerPower n q) =ᵐ[hT.traceMeasure] fun _ => (1 : ℝ) := by
  obtain ⟨C, -, hC⟩ := hT.exists_abs_density_le (kahlerPower n q)
  refine hT.ae_eq_of_forall_integral_eq (hT.measurable_density _) measurable_const ⟨C, hC⟩
    ⟨1, fun _ => by simp⟩ fun φ => ?_
  rw [← hT.apply_eq_integral_density, ← hT.integral_traceMeasure]
  simp

/-- The pointwise density form takes the value `1` on `ω₀^q`, almost everywhere. -/
theorem densityForm_kahlerPower_ae (hT : IsPositive T) :
    ∀ᵐ x ∂hT.traceMeasure, densityForm hT x (kahlerPower n q) = 1 := by
  filter_upwards [densityForm_ae hT (kahlerPower n q), density_kahlerPower_ae hT] with x h1 h2
  rw [h1, h2]

/-- The order-unit constant of a constant form: `C ω₀^q ± γ` are strongly positive. -/
def orderUnitConst (γ : formSpan n q) : ℝ := Classical.choose (exists_orderUnit γ.2)

theorem orderUnitConst_nonneg (γ : formSpan n q) : 0 ≤ orderUnitConst γ :=
  (Classical.choose_spec (exists_orderUnit γ.2)).1

/-- **The density forms of all positive currents are bounded by the same constant** on a given
constant form, almost everywhere: `|L_x(γ)| ≤ C_γ`. -/
theorem ae_abs_densityForm_le (hT : IsPositive T) (γ : formSpan n q) :
    ∀ᵐ x ∂hT.traceMeasure, |densityForm hT x γ| ≤ orderUnitConst γ := by
  obtain ⟨-, h₁, h₂⟩ := Classical.choose_spec (exists_orderUnit γ.2)
  filter_upwards [ae_densityForm_nonneg hT, densityForm_kahlerPower_ae hT] with x hpos hone
  have e₁ : (orderUnitConst γ • kahlerPower n q - γ : formSpan n q) ∈ posCone n q := by
    change ((orderUnitConst γ • kahlerPower n q - γ : formSpan n q) : RealForm n (2 * q)) ∈
      spCone q
    simpa [kahlerPower, orderUnitConst] using h₁
  have e₂ : (orderUnitConst γ • kahlerPower n q + γ : formSpan n q) ∈ posCone n q := by
    change ((orderUnitConst γ • kahlerPower n q + γ : formSpan n q) : RealForm n (2 * q)) ∈
      spCone q
    simpa [kahlerPower, orderUnitConst] using h₂
  have a₁ := hpos _ e₁
  have a₂ := hpos _ e₂
  rw [map_sub, map_smul, hone, smul_eq_mul, mul_one] at a₁
  rw [map_add, map_smul, hone, smul_eq_mul, mul_one] at a₂
  rw [abs_le]
  constructor <;> linarith

end Density

/-! ### First-occurrence layers of a sequence of sets -/

section Layers

variable {O : ℕ → Set (ComplexModel n)}

/-- The `k`-th layer `O_k \ ⋃_{j < k} O_j`. -/
def layer (O : ℕ → Set (ComplexModel n)) (k : ℕ) : Set (ComplexModel n) := {x | x ∈ O k ∧ ∀ j < k,
    x ∉ O j}

theorem layer_subset (k : ℕ) : layer O k ⊆ O k := fun _ hx => hx.1

theorem measurableSet_layer (hO : ∀ k, MeasurableSet (O k)) (k : ℕ) :
    MeasurableSet (layer O k) := by
  have e : layer O k = O k ∩ ⋂ j, ⋂ (_ : j < k), (O j)ᶜ := by
    ext x
    simp [layer]
  rw [e]
  exact (hO k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hO j).compl)

theorem notMem_of_mem_layer {j k : ℕ} (hkj : k < j) {x : (ComplexModel n)}
    (hx : x ∈ layer O j) : x ∉ O k :=
  hx.2 k hkj

theorem disjoint_layer {j k : ℕ} (hjk : j ≠ k) : Disjoint (layer O j) (layer O k) := by
  rw [Set.disjoint_left]
  intro x hj hk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hk.2 j h hj.1
  · exact hj.2 k h hk.1

theorem exists_mem_layer {k : ℕ} {x : (ComplexModel n)} (hx : x ∈ O k) : ∃ j ≤ k,
    x ∈ layer O j := by
  classical
  have h : ∃ j, x ∈ O j := ⟨k, hx⟩
  refine ⟨Nat.find h, Nat.find_min' h hx, Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

/-- For an increasing sequence, `1_{O_k} = ∑_{j ≤ k} 1_{layer j}`. -/
theorem indicator_eq_sum_layer (hO : Monotone O) (k : ℕ) (x : (ComplexModel n)) :
    (O k).indicator (fun _ => (1 : ℝ)) x =
      ∑ j ∈ Finset.range (k + 1), (layer O j).indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : x ∈ O k
  · obtain ⟨j, hjk, hj⟩ := exists_mem_layer hx
    rw [Set.indicator_of_mem hx, Finset.sum_eq_single j]
    · rw [Set.indicator_of_mem hj]
    · intro i _ hij
      exact Set.indicator_of_notMem (fun hi => Set.disjoint_left.mp (disjoint_layer hij) hi hj) _
    · intro hj'
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hjk)) hj'
  · rw [Set.indicator_of_notMem hx]
    refine (Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (fun hj' => hx ?_) _).symm
    exact hO (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hj'.1

theorem exists_mem_of_notMem_compl {x : (ComplexModel n)} : ∃ k, x ∈ O k ∨ ∀ j, x ∉ O j := by
  by_cases h : ∃ k, x ∈ O k
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Or.inl hk⟩
  · exact ⟨0, Or.inr fun j hj => h ⟨j, hj⟩⟩

/-- The first level `k` with `x ∈ O_k` (and `0` if there is none). -/
@[irreducible] def level (O : ℕ → Set (ComplexModel n)) (x : (ComplexModel n)) : ℕ :=
  @Nat.find (fun k => x ∈ O k ∨ ∀ j, x ∉ O j) (fun _ => Classical.propDecidable _)
    exists_mem_of_notMem_compl

theorem level_eq_of_mem_layer {k : ℕ} {x : (ComplexModel n)} (hx : x ∈ layer O k)
    : level O x = k := by
  unfold level
  rw [@Nat.find_eq_iff]
  refine ⟨Or.inl hx.1, fun j hj h => ?_⟩
  rcases h with h | h
  · exact hx.2 j hj h
  · exact h k hx.1

theorem measurable_level (hO : ∀ k, MeasurableSet (O k)) : Measurable (level O) := by
  unfold level
  refine @measurable_find _ _ (fun x k => x ∈ O k ∨ ∀ j, x ∉ O j)
    (fun _ => fun _ => Classical.propDecidable _) (fun _ => exists_mem_of_notMem_compl)
    fun k => ?_
  have e : {x | x ∈ O k ∨ ∀ j, x ∉ O j} = O k ∪ ⋂ j, (O j)ᶜ := by
    ext x
    simp
  rw [e]
  exact (hO k).union (MeasurableSet.iInter fun j => (hO j).compl)

end Layers

end SGPT.NPP.NonPluripolarCurrent

namespace SGPT.Currents

open SGPT.NPP.NonPluripolarCurrent
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents

variable {n : ℕ}

namespace LayeredCurrent

variable {q : ℕ} {W : ℕ → Opens (ComplexModel n)} {T : ∀ k, LocalProductCurrent n (W k) q}
  (H : ∀ k, IsPositive (T k)) (O : ℕ → Set (ComplexModel n))

/-- Sum the trace measures restricted to their first-occurrence layers. -/
def measure : Measure (ComplexModel n) :=
  Measure.sum fun k => (H k).traceMeasure.restrict (layer O k)

/-- The density form supplied by a point and a layer index. -/
def densityAtLayer (z : ComplexModel n × ℕ) : formSpan n q →ₗ[ℝ] ℝ :=
  densityForm (H z.2) z.1

/-- Use the density form belonging to the first member that contains the point. -/
def density (x : ComplexModel n) : formSpan n q →ₗ[ℝ] ℝ :=
  densityAtLayer H (x, level O x)

theorem density_of_mem_layer {k : ℕ} {x : ComplexModel n} (hx : x ∈ layer O k) :
    density H O x = densityForm (H k) x :=
  congrArg (fun j => densityAtLayer H (x, j)) (level_eq_of_mem_layer hx)

theorem measurable_density (hO : ∀ k, MeasurableSet (O k)) (γ : formSpan n q) :
    Measurable fun x => density H O x γ := by
  have h : Measurable fun z : ComplexModel n × ℕ => densityAtLayer H z γ := by
    refine measurable_from_prod_countable_left (f := fun z => densityAtLayer H z γ) ?_
    intro k
    exact measurable_densityForm (H k) γ
  have hl : Measurable fun x : ComplexModel n => (x, level O x) :=
    measurable_id.prodMk (measurable_level hO)
  exact h.comp (f := fun x => (x, level O x)) hl

theorem measure_apply {s : Set (ComplexModel n)} (hs : MeasurableSet s) :
    measure H O s = ∑' k, (H k).traceMeasure (s ∩ layer O k) := by
  rw [measure, Measure.sum_apply _ hs]
  simp only [Measure.restrict_apply hs]

theorem ae_abs_density_le (hO : ∀ k, MeasurableSet (O k)) (γ : formSpan n q) :
    ∀ᵐ x ∂measure H O, |density H O x γ| ≤ orderUnitConst γ := by
  rw [measure, Measure.ae_sum_iff]
  intro k
  rw [ae_restrict_iff' (measurableSet_layer hO k)]
  filter_upwards [ae_abs_densityForm_le (H k) γ] with x hx hmem
  rw [density_of_mem_layer H O hmem]
  exact hx

end LayeredCurrent

/-! ### A current from a measure and a bounded density form -/

section OfMeasure

variable {q : ℕ} {U : Opens (ComplexModel n)}

/-- The data of a positive-current-like object on `U`: a measure `μ` carried by `U` and finite on
the compact subsets of `U`, and a measurable density form `g` with `|g x γ| ≤ C_γ` almost
everywhere. -/
structure IsMeasureDensity (U : Opens (ComplexModel n)) (μ : Measure (ComplexModel n))
    (g : (ComplexModel n) → formSpan n q →ₗ[ℝ] ℝ) : Prop where
  compl : μ ((U : Set (ComplexModel n))ᶜ) = 0
  lt_top : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → μ K < ⊤
  measurable : ∀ γ, Measurable fun x => g x γ
  bounded : ∀ γ, ∀ᵐ x ∂μ, |g x γ| ≤ orderUnitConst γ

variable {μ : Measure (ComplexModel n)} {g : (ComplexModel n) → formSpan n q →ₗ[ℝ] ℝ}

theorem IsMeasureDensity.integrable_test (hμ : IsMeasureDensity U μ g) (γ : formSpan n q)
    (φ : 𝓓(U, ℝ)) : Integrable (fun x => φ x * g x γ) μ := by
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hon : IntegrableOn (fun x => φ x * g x γ) (tsupport φ) μ := by
    refine Measure.integrableOn_of_bounded (M := Cφ * orderUnitConst γ)
      (hμ.lt_top _ φ.hasCompactSupport φ.tsupport_subset).ne
      (φ.continuous.measurable.mul (hμ.measurable γ)).aestronglyMeasurable
      (ae_restrict_of_ae ?_)
    filter_upwards [hμ.bounded γ] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : ‖φ x‖ ≤ Cφ := hCφ x
    rw [Real.norm_eq_abs] at h1
    exact mul_le_mul h1 hx (abs_nonneg _) ((abs_nonneg _).trans h1)
  exact hon.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem IsMeasureDensity.locallyIntegrableOn (hμ : IsMeasureDensity U μ g) (γ : formSpan n q) :
    LocallyIntegrableOn (fun x => g x γ) U μ := by
  intro x hx
  obtain ⟨K, hK, hKn, hKU⟩ := exists_compact_subset U.isOpen hx
  refine ⟨K, nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hKn), ?_⟩
  refine Measure.integrableOn_of_bounded (M := orderUnitConst γ) (hμ.lt_top K hK hKU).ne
    (hμ.measurable γ).aestronglyMeasurable (ae_restrict_of_ae ?_)
  filter_upwards [hμ.bounded γ] with x hx
  rwa [Real.norm_eq_abs]

open Classical in
/-- **The current `γ ↦ g(γ) μ`** (and `0` when the data are not admissible). -/
def ofMeasureDensity (U : Opens (ComplexModel n)) (μ : Measure (ComplexModel n))
    (g : (ComplexModel n) → formSpan n q →ₗ[ℝ] ℝ) :
    LocalProductCurrent n U q :=
  if hμ : IsMeasureDensity U μ g then
    { toFun := fun γ => regularDistribution μ (fun x => g x γ) (hμ.locallyIntegrableOn γ)
      map_add' := fun γ γ' => by
        ext φ
        rw [_root_.add_apply, regularDistribution_apply, regularDistribution_apply,
          regularDistribution_apply, ← integral_add (hμ.integrable_test γ φ)
            (hμ.integrable_test γ' φ)]
        congr 1
        funext x
        rw [map_add, mul_add]
      map_smul' := fun c γ => by
        ext φ
        rw [RingHom.id_apply, _root_.smul_apply, regularDistribution_apply,
          regularDistribution_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext x
        rw [map_smul, smul_eq_mul]
        ring }
  else 0

theorem ofMeasureDensity_apply (hμ : IsMeasureDensity U μ g) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    ofMeasureDensity U μ g γ φ = ∫ x, φ x * g x γ ∂μ := by
  rw [ofMeasureDensity, dite_eq_left hμ]
  exact regularDistribution_apply _ _ (hμ.locallyIntegrableOn γ) φ

end OfMeasure

end SGPT.Currents
