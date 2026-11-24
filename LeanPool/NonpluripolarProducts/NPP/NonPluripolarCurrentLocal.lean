/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.BedfordTaylorTopDegree
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentPullbackDdc

/-!
# The non-pluripolar product of arbitrary degree as a current: the local theory

Source: `chapter_npp.tex`, `def:npp:L69`; Xia, *Foundations of pluripotential theory*,
`lem:positive-current-restriction`, `lem:nonpluripolar-truncation-limit`,
`def:nonpluripolar-product`.

Let `U ⊆ ℂⁿ` be open, `q + p = n`, and let `φ₁, …, φ_p` be psh on `U`.  With
`O_k = {φ₁ > -k, …, φ_p > -k}` the truncated products
`T_k = 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))` (`BedfordTaylorTopDegree.truncatedProduct`) are consistent
(`1_{O_k} T_l = T_k` for `k ≤ l`) and increase.  The source defines the non-pluripolar product by
`1_{O_k} ⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩ = T_k` on `⋃ₖ O_k` and extension by zero, under the local mass
condition `sup_k ∫_{K ∩ O_k} ⋀ⱼ dd^c(φⱼ ∨ (-k)) ∧ ω^{n-p} < ∞`.

## The gluing construction

We work with an abstract *truncation family* (`IsTruncationFamily B O`): positive currents `B k`
and an increasing sequence of Borel sets `O k ⊆ U` with `1_{O_k} B_l = 1_{O_k} B_k` for `k ≤ l`.
The layers `O_k \ ⋃_{j<k} O_j` are disjoint Borel sets; on the `k`-th layer we keep the trace
measure and the pointwise density form of `B_k`.  The glued measure
`μ = ∑ₖ σ_{B_k}|_{layer k}` (`glueMeasure`) and the glued density form (`glueDensity`) define, when
`μ` is finite on the compact subsets of `U` (`HasLocallyFiniteMass`), the current
`S(γ) = L_x(γ) μ` (`glue`).  We prove:

* `glue_apply_trunc`, `weakTendsto_trunc_glue` — `1_{O_k} B_k → S` weakly (so `S` is the weak
  limit of the truncated products, FPT `lem:nonpluripolar-truncation-limit`), and `S` is positive
  (`isPositive_glue`);
* `mulBorel_glue_indicator` — `1_{O_k} S = 1_{O_k} B_k` (the defining identity `eq:npp`), and
  `mulBorel_glue_compl` — `S` vanishes off `⋃ₖ O_k` (extension by zero);
* `eq_glue_of_mulBorel` — these two properties characterize `S` among positive currents;
* `hasLocallyFiniteMass_iff` — `μ(K) < ∞` iff `sup_k σ_{B_k}(K ∩ O_k) < ∞`.

## The non-pluripolar product

`nonPluripolarProduct hqp U φ` is the glued current of the truncations
(`truncatedBT`, `strictLocus`).  The source well-definedness predicate `IsWellDefinedOn`
quantifies, as `eq:welldefinepluri`, over connected open `V ⊆ U`, smooth semipositive
`(1,1)`-forms `ω` on `V` (the book's "positive forms are not necessarily strictly positive") and
compact `K ⊆ V`, using the measures `(⋀ⱼ dd^c (φⱼ ∨ (-k)))|_V ∧ ω^{n-p}` (`wedgePowerMeasure`); it
is equivalent to the Euclidean mass condition (`isWellDefinedOn_iff`).
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

/-! ### Layers of an increasing sequence of sets -/

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

theorem notMem_of_mem_layer {j k : ℕ} (_hO : Monotone O) (hkj : k < j) {x : (ComplexModel n)}
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

/-! ### Truncation families and the glued current -/

section Glue

variable {U : Opens (ComplexModel n)} {q : ℕ}

/-- A **truncation family** on `U`: positive currents `B k` and an increasing sequence of Borel
sets `O k ⊆ U` with `1_{O_k} B_l = 1_{O_k} B_k` for `k ≤ l`. -/
structure IsTruncationFamily (B : ℕ → LocalProductCurrent n U q) (O : ℕ → Set (ComplexModel n))
    : Prop where
  isPositive : ∀ k, IsPositive (B k)
  measurableSet : ∀ k, MeasurableSet (O k)
  subset : ∀ k, O k ⊆ U
  mono : Monotone O
  consistent : ∀ {k l : ℕ}, k ≤ l →
    mulBorel (B l) ((O k).indicator fun _ => (1 : ℝ)) =
      mulBorel (B k) ((O k).indicator fun _ => (1 : ℝ))

variable {B : ℕ → LocalProductCurrent n U q} {O : ℕ → Set (ComplexModel n)}

theorem isLocallyBoundedOn_indicator_one (A : Set (ComplexModel n)) :
    IsLocallyBoundedOn (A.indicator fun _ => (1 : ℝ)) U :=
  fun _ _ _ => ⟨1, fun x _ => by by_cases hx : x ∈ A <;> simp [hx]⟩

variable (B O) in
/-- The level-`k` truncated current `1_{O_k} B_k`. -/
def truncAt (k : ℕ) : LocalProductCurrent n U q :=
  mulBorel (B k) ((O k).indicator fun _ => (1 : ℝ))

namespace IsTruncationFamily

variable (hF : IsTruncationFamily B O)
include hF

theorem isPositive_trunc (k : ℕ) : IsPositive (truncAt B O k) :=
  BedfordTaylorTopDegree.isPositive_mulBorel_of_nonneg (hF.isPositive k)
    (measurable_const.indicator (hF.measurableSet k)) (isLocallyBoundedOn_indicator_one _)
    (fun x => by by_cases hx : x ∈ O k <;> simp [hx])

theorem isLocalDensity_indicator_density (k : ℕ) (A : Set (ComplexModel n)) (hA : MeasurableSet A)
    (γ : formSpan n q) :
    IsLocalDensity (U := U) (hF.isPositive k).traceMeasure
      (fun x => A.indicator (fun _ => (1 : ℝ)) x * (hF.isPositive k).density γ x) := by
  obtain ⟨C, -, hC⟩ := (hF.isPositive k).exists_abs_density_le γ
  refine ⟨(hF.isPositive k).traceMeasure_compl,
    fun K hK hKU => (hF.isPositive k).traceMeasure_lt_top hK hKU,
    (measurable_const.indicator hA).mul ((hF.isPositive k).measurable_density γ),
    fun K _ _ => ⟨C, fun x _ => ?_⟩⟩
  rw [abs_mul]
  by_cases hx : x ∈ A
  · simpa [hx] using hC x
  · simp [hx, (abs_nonneg _).trans (hC x)]

/-- **Consistency against test weights**: for `j ≤ k` and a bounded Borel weight `w` with compact
support in `U`, `∫_{layer j} w L^{(k)}(γ) dσ_k = ∫_{layer j} w L^{(j)}(γ) dσ_j`. -/
theorem setIntegral_layer_consistent {j k : ℕ} (hjk : j ≤ k) (γ : formSpan n q)
    {w : (ComplexModel n) → ℝ}
    (hw : IsTestWeight (U := U) w) :
    ∫ x in layer O j, w x * densityForm (hF.isPositive k) x γ ∂(hF.isPositive k).traceMeasure =
      ∫ x in layer O j, w x * densityForm (hF.isPositive j) x γ ∂(hF.isPositive j).traceMeasure :=
        by
  have hLm := measurableSet_layer hF.measurableSet j
  have key := integral_eq_of_forall_testFunction
    (hF.isLocalDensity_indicator_density k (O j) (hF.measurableSet j) γ)
    (hF.isLocalDensity_indicator_density j (O j) (hF.measurableSet j) γ)
    (fun ψ => by
      have h := congrArg (fun S : LocalProductCurrent n U q => S γ ψ) (hF.consistent hjk)
      simp only at h
      rw [mulBorel_apply (hF.isPositive k) (measurable_const.indicator (hF.measurableSet j))
          (isLocallyBoundedOn_indicator_one _),
        mulBorel_apply (hF.isPositive j) (measurable_const.indicator (hF.measurableSet j))
          (isLocallyBoundedOn_indicator_one _)] at h
      calc ∫ x, (O j).indicator (fun _ => (1 : ℝ)) x * (hF.isPositive k).density γ x * ψ x
              ∂(hF.isPositive k).traceMeasure =
            ∫ x, ψ x * ((O j).indicator (fun _ => (1 : ℝ)) x * (hF.isPositive k).density γ x)
              ∂(hF.isPositive k).traceMeasure :=
            integral_congr_ae (ae_of_all _ fun x => by ring)
        _ = _ := h
        _ = _ := integral_congr_ae (ae_of_all _ fun x => by ring))
    (w := (layer O j).indicator w) ?_
  · rw [← integral_indicator hLm, ← integral_indicator hLm]
    have e : ∀ (m : ℕ), ∫ x, (layer O j).indicator
          (fun x => w x * densityForm (hF.isPositive m) x γ) x ∂(hF.isPositive m).traceMeasure =
        ∫ x, (O j).indicator (fun _ => (1 : ℝ)) x * (hF.isPositive m).density γ x *
          (layer O j).indicator w x ∂(hF.isPositive m).traceMeasure := fun m => by
      refine integral_congr_ae ?_
      filter_upwards [densityForm_ae (hF.isPositive m) γ] with x hx
      by_cases hxl : x ∈ layer O j
      · rw [Set.indicator_of_mem hxl, Set.indicator_of_mem hxl,
          Set.indicator_of_mem (layer_subset j hxl), hx]
        ring
      · rw [Set.indicator_of_notMem hxl, Set.indicator_of_notMem hxl, mul_zero]
    rw [e k, e j, key]
  · obtain ⟨hwm, ⟨M, hM⟩, K, hK, hKU, hKw⟩ := hw
    refine ⟨hwm.indicator hLm, ⟨M, fun x => ?_⟩, K, hK, hKU, fun x hx => ?_⟩
    · by_cases hx : x ∈ layer O j
      · rw [Set.indicator_of_mem hx]
        exact hM x
      · rw [Set.indicator_of_notMem hx, abs_zero]
        exact (abs_nonneg _).trans (hM x)
    · by_cases hx' : x ∈ layer O j
      · rw [Set.indicator_of_mem hx', hKw x hx]
      · rw [Set.indicator_of_notMem hx']

/-- The glued measure `μ = ∑ₖ σ_{B_k}|_{layer k}`. -/
def glueMeasure : Measure (ComplexModel n) :=
  Measure.sum fun k => ((hF.isPositive k).traceMeasure).restrict (layer O k)

/-- The density form of `B_k` at `x`, as a function of `(x, k)`. -/
def layerDensity (z : (ComplexModel n) × ℕ) : formSpan n q →ₗ[ℝ] ℝ :=
  densityForm (hF.isPositive z.2) z.1

/-- The glued density form: on the `k`-th layer, the density form of `B_k`. -/
def glueDensity (x : (ComplexModel n)) : formSpan n q →ₗ[ℝ] ℝ :=
  hF.layerDensity (x, level O x)

theorem densityForm_congr_level {k l : ℕ} (h : k = l) (x : (ComplexModel n)) :
    densityForm (hF.isPositive k) x = densityForm (hF.isPositive l) x := by
  subst h
  rfl

theorem glueDensity_of_mem_layer {k : ℕ} {x : (ComplexModel n)} (hx : x ∈ layer O k) :
    hF.glueDensity x = densityForm (hF.isPositive k) x :=
  hF.densityForm_congr_level (level_eq_of_mem_layer hx) x

theorem measurable_glueDensity (γ : formSpan n q) : Measurable fun x => hF.glueDensity x γ := by
  have h : Measurable fun z : (ComplexModel n) × ℕ => hF.layerDensity z γ := by
    apply measurable_from_prod_countable_left
    intro k
    exact measurable_densityForm (hF.isPositive k) γ
  have hl : Measurable fun x : (ComplexModel n) => (x, level O x) :=
    measurable_id.prodMk (measurable_level hF.measurableSet)
  exact h.comp hl

theorem glueMeasure_apply {s : Set (ComplexModel n)} (hs : MeasurableSet s) :
    hF.glueMeasure s = ∑' k, (hF.isPositive k).traceMeasure (s ∩ layer O k) := by
  rw [glueMeasure, Measure.sum_apply _ hs]
  simp only [Measure.restrict_apply hs]

theorem glueMeasure_compl : hF.glueMeasure ((U : Set (ComplexModel n))ᶜ) = 0 := by
  rw [hF.glueMeasure_apply U.isOpen.measurableSet.compl, tsum_eq_zero_iff]
  intro k
  exact measure_mono_null inter_subset_left (hF.isPositive k).traceMeasure_compl

theorem ae_glueMeasure_mem : ∀ᵐ x ∂hF.glueMeasure, ∃ k, x ∈ O k := by
  rw [glueMeasure, Measure.ae_sum_iff]
  intro k
  filter_upwards [ae_restrict_mem (measurableSet_layer hF.measurableSet k)] with x hx
  exact ⟨k, hx.1⟩

theorem ae_abs_glueDensity_le (γ : formSpan n q) :
    ∀ᵐ x ∂hF.glueMeasure, |hF.glueDensity x γ| ≤ orderUnitConst γ := by
  rw [glueMeasure, Measure.ae_sum_iff]
  intro k
  rw [ae_restrict_iff' (measurableSet_layer hF.measurableSet k)]
  filter_upwards [ae_abs_densityForm_le (hF.isPositive k) γ] with x hx hmem
  rw [hF.glueDensity_of_mem_layer hmem]
  exact hx

/-- **The local mass condition**: the glued measure is finite on the compact subsets of `U`. -/
def HasLocallyFiniteMass : Prop :=
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → hF.glueMeasure K < ⊤

theorem integrable_test_mul_glueDensity (hm : hF.HasLocallyFiniteMass) (γ : formSpan n q)
    {c : (ComplexModel n) → ℝ} (hc : Measurable c) (hcb : ∀ x, |c x| ≤ 1) (φ : 𝓓(U, ℝ)) :
    Integrable (fun x => φ x * (c x * hF.glueDensity x γ)) hF.glueMeasure := by
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport
  have hon : IntegrableOn (fun x => φ x * (c x * hF.glueDensity x γ)) (tsupport φ)
      hF.glueMeasure := by
    refine Measure.integrableOn_of_bounded (M := Cφ * orderUnitConst γ)
      (hm _ hK φ.tsupport_subset).ne
      (φ.continuous.measurable.mul (hc.mul (hF.measurable_glueDensity γ))).aestronglyMeasurable
      (ae_restrict_of_ae ?_)
    filter_upwards [hF.ae_abs_glueDensity_le γ] with x hx
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : ‖φ x‖ ≤ Cφ := hCφ x
    rw [Real.norm_eq_abs] at h1
    calc |φ x| * (|c x| * |hF.glueDensity x γ|) ≤ Cφ * (1 * orderUnitConst γ) :=
          mul_le_mul h1 (mul_le_mul (hcb x) hx (abs_nonneg _) zero_le_one)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ((abs_nonneg _).trans h1)
      _ = Cφ * orderUnitConst γ := by ring
  exact hon.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem locallyIntegrableOn_glueDensity (hm : hF.HasLocallyFiniteMass) (γ : formSpan n q) :
    LocallyIntegrableOn (fun x => hF.glueDensity x γ) U hF.glueMeasure := by
  intro x hx
  obtain ⟨K, hK, hKn, hKU⟩ := exists_compact_subset U.isOpen hx
  refine ⟨K, nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hKn), ?_⟩
  refine Measure.integrableOn_of_bounded (M := orderUnitConst γ) (hm K hK hKU).ne
    (hF.measurable_glueDensity γ).aestronglyMeasurable (ae_restrict_of_ae ?_)
  filter_upwards [hF.ae_abs_glueDensity_le γ] with x hx
  rwa [Real.norm_eq_abs]

open Classical in
/-- **The glued current** `S(γ) = L_x(γ) μ` (and `0` when the mass condition fails). -/
def glue : LocalProductCurrent n U q :=
  if hm : hF.HasLocallyFiniteMass then
    { toFun := fun γ => regularDistribution hF.glueMeasure (fun x => hF.glueDensity x γ)
        (hF.locallyIntegrableOn_glueDensity hm γ)
      map_add' := fun γ γ' => by
        ext φ
        have h1 := hF.integrable_test_mul_glueDensity hm γ (c := fun _ => 1) measurable_const
          (fun _ => by simp) φ
        have h2 := hF.integrable_test_mul_glueDensity hm γ' (c := fun _ => 1) measurable_const
          (fun _ => by simp) φ
        simp only [one_mul] at h1 h2
        rw [_root_.add_apply, regularDistribution_apply, regularDistribution_apply,
          regularDistribution_apply, ← integral_add h1 h2]
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

theorem glue_apply (hm : hF.HasLocallyFiniteMass) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    hF.glue γ φ = ∫ x, φ x * hF.glueDensity x γ ∂hF.glueMeasure := by
  rw [glue, dite_eq_left hm]
  exact regularDistribution_apply _ _ (hF.locallyIntegrableOn_glueDensity hm γ) φ

theorem integrable_test (hm : hF.HasLocallyFiniteMass) (φ : 𝓓(U, ℝ)) :
    Integrable (fun x => φ x) hF.glueMeasure := by
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hon : IntegrableOn (fun x => φ x) (tsupport φ) hF.glueMeasure :=
    Measure.integrableOn_of_bounded (M := Cφ) (hm _ φ.hasCompactSupport φ.tsupport_subset).ne
      φ.continuous.aestronglyMeasurable (Eventually.of_forall fun x => hCφ x)
  exact hon.integrable_of_forall_notMem_eq_zero fun x hx => image_eq_zero_of_notMem_tsupport hx

/-- **The truncated currents through the glued data**: under the mass condition,
`(1_{O_k} B_k)(γ)(φ) = ∫ φ 1_{O_k} L(γ) dμ`. -/
theorem truncAt_apply (hm : hF.HasLocallyFiniteMass) (k : ℕ) (γ : formSpan n q)
    (φ : 𝓓(U, ℝ)) :
    truncAt B O k γ φ = ∫ x, φ x * ((O k).indicator (fun _ => (1 : ℝ)) x * hF.glueDensity x γ)
      ∂hF.glueMeasure := by
  have hOk := hF.measurableSet k
  have hlay := measurableSet_layer hF.measurableSet
  have hint := hF.integrable_test_mul_glueDensity hm γ
    (c := (O k).indicator fun _ => (1 : ℝ)) (measurable_const.indicator hOk)
    (fun x => by by_cases hx : x ∈ O k <;> simp [hx]) φ
  have hterm : ∀ j, ∫ x, φ x * ((O k).indicator (fun _ => (1 : ℝ)) x * hF.glueDensity x γ)
        ∂((hF.isPositive j).traceMeasure.restrict (layer O j)) =
      if j ≤ k then ∫ x in layer O j, φ x * densityForm (hF.isPositive j) x γ
        ∂(hF.isPositive j).traceMeasure else 0 := by
    intro j
    split_ifs with hjk
    · refine setIntegral_congr_fun (hlay j) fun x hx => ?_
      rw [Set.indicator_of_mem (hF.mono hjk (layer_subset j hx)), one_mul,
        hF.glueDensity_of_mem_layer hx]
    · refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      rw [Set.indicator_of_notMem (notMem_of_mem_layer hF.mono (not_le.mp hjk) hx), zero_mul,
        mul_zero]
  have hR : ∫ x, φ x * ((O k).indicator (fun _ => (1 : ℝ)) x * hF.glueDensity x γ)
      ∂hF.glueMeasure = ∑ j ∈ Finset.range (k + 1),
        ∫ x in layer O j, φ x * densityForm (hF.isPositive j) x γ
          ∂(hF.isPositive j).traceMeasure := by
    rw [glueMeasure] at hint ⊢
    rw [integral_sum_measure hint]
    simp_rw [hterm]
    rw [tsum_eq_sum (s := Finset.range (k + 1)) fun j hj => by
      rw [Finset.mem_range, not_lt] at hj
      rw [ite_eq_right (by omega)]]
    exact Finset.sum_congr rfl fun j hj => by
      rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  rw [hR, truncAt, mulBorel_apply (hF.isPositive k) (measurable_const.indicator hOk)
    (isLocallyBoundedOn_indicator_one _)]
  have hi := integrable_densityForm (hF.isPositive k) le_rfl γ φ
  have hL : ∫ x, φ x * ((O k).indicator (fun _ => (1 : ℝ)) x * (hF.isPositive k).density γ x)
        ∂(hF.isPositive k).traceMeasure =
      ∑ j ∈ Finset.range (k + 1), ∫ x in layer O j, φ x * densityForm (hF.isPositive k) x γ
        ∂(hF.isPositive k).traceMeasure := by
    simp_rw [← integral_indicator (hlay _)]
    rw [← integral_finsetSum _ fun j _ => hi.indicator (hlay j)]
    refine integral_congr_ae ?_
    filter_upwards [densityForm_ae (hF.isPositive k) γ] with x hx
    rw [← hx, indicator_eq_sum_layer hF.mono k x, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hxj : x ∈ layer O j
    · rw [Set.indicator_of_mem hxj, Set.indicator_of_mem hxj, one_mul]
    · rw [Set.indicator_of_notMem hxj, Set.indicator_of_notMem hxj, zero_mul, mul_zero]
  rw [hL]
  exact Finset.sum_congr rfl fun j hj => hF.setIntegral_layer_consistent
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) γ (isTestWeight_testFunction φ)

/-- **The truncated products converge weakly to the glued current** (FPT
`lem:nonpluripolar-truncation-limit`). -/
theorem weakTendsto_truncAt_glue (hm : hF.HasLocallyFiniteMass) :
    LocalBedfordTaylorContinuity.WeakTendsto (truncAt B O) hF.glue := by
  intro γ φ
  simp only [hF.truncAt_apply hm, hF.glue_apply hm]
  refine tendsto_integral_of_dominated_convergence (fun x => |φ x| * orderUnitConst γ)
    (fun k => ?_) ?_ (fun k => ?_) ?_
  · exact (φ.continuous.measurable.mul ((measurable_const.indicator (hF.measurableSet k)).mul
      (hF.measurable_glueDensity γ))).aestronglyMeasurable
  · exact (hF.integrable_test hm φ).abs.mul_const _
  · filter_upwards [hF.ae_abs_glueDensity_le γ] with x hx
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |(O k).indicator (fun _ => (1 : ℝ)) x| * |hF.glueDensity x γ| ≤
          1 * orderUnitConst γ := by
          refine mul_le_mul ?_ hx (abs_nonneg _) zero_le_one
          by_cases h : x ∈ O k <;> simp [h]
      _ = orderUnitConst γ := one_mul _
  · filter_upwards [hF.ae_glueMeasure_mem] with x hx
    obtain ⟨k₀, hk₀⟩ := hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k₀] with k hk
    rw [Set.indicator_of_mem (hF.mono hk hk₀), one_mul]

/-- **The glued current is positive**, as a weak limit of positive currents. -/
theorem isPositive_glue (hm : hF.HasLocallyFiniteMass) : IsPositive hF.glue :=
  LocalBedfordTaylorContinuity.isPositive_of_weakTendsto (fun k => hF.isPositive_trunc k)
    (hF.weakTendsto_truncAt_glue hm)

/-- The glued density clipped to `[-C_γ, C_γ]` (a bounded representative). -/
def clipDensity (γ : formSpan n q) (x : (ComplexModel n)) : ℝ :=
  max (-orderUnitConst γ) (min (hF.glueDensity x γ) (orderUnitConst γ))

theorem clipDensity_ae (γ : formSpan n q) :
    (fun x => hF.clipDensity γ x) =ᵐ[hF.glueMeasure] fun x => hF.glueDensity x γ := by
  filter_upwards [hF.ae_abs_glueDensity_le γ] with x hx
  rw [abs_le] at hx
  simp only [clipDensity]
  rw [min_eq_left hx.2, max_eq_right hx.1]

theorem isLocalDensity_clipDensity (hm : hF.HasLocallyFiniteMass) (γ : formSpan n q) :
    IsLocalDensity (U := U) hF.glueMeasure (hF.clipDensity γ) := by
  refine ⟨hF.glueMeasure_compl, hm, measurable_const.max
    ((hF.measurable_glueDensity γ).min measurable_const), fun K _ _ => ⟨orderUnitConst γ,
      fun x _ => ?_⟩⟩
  have h0 := orderUnitConst_nonneg γ
  rw [abs_le]
  simp only [clipDensity]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

/-- `(c S)(γ)(φ) = ∫ φ c L(γ) dμ` for the glued current `S`. -/
theorem mulBorel_glue_apply (hm : hF.HasLocallyFiniteMass) {c : (ComplexModel n)
    → ℝ} (hc : Measurable c)
    (hcb : IsLocallyBoundedOn c U) (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
    mulBorel hF.glue c γ φ = ∫ x, φ x * (c x * hF.glueDensity x γ) ∂hF.glueMeasure := by
  rw [mulBorel_apply_of_integral_eq (hF.isPositive_glue hm) γ (hF.isLocalDensity_clipDensity hm γ)
    (fun ψ => ?_) hc hcb φ]
  · refine integral_congr_ae ?_
    filter_upwards [hF.clipDensity_ae γ] with x hx
    rw [hx]
  · rw [hF.glue_apply hm]
    refine integral_congr_ae ?_
    filter_upwards [hF.clipDensity_ae γ] with x hx
    rw [hx]

/-- **The defining identity** `1_{O_k} S = 1_{O_k} B_k` (source `eq:npp`). -/
theorem mulBorel_glue_indicator (hm : hF.HasLocallyFiniteMass) (k : ℕ) :
    mulBorel hF.glue ((O k).indicator fun _ => (1 : ℝ)) = truncAt B O k := by
  ext γ φ
  rw [hF.mulBorel_glue_apply hm (measurable_const.indicator (hF.measurableSet k))
    (isLocallyBoundedOn_indicator_one _), hF.truncAt_apply hm]

/-- **Extension by zero**: the glued current vanishes off `⋃ₖ O_k`. -/
theorem mulBorel_glue_compl (hm : hF.HasLocallyFiniteMass) :
    mulBorel hF.glue ((⋃ k, O k)ᶜ.indicator fun _ => (1 : ℝ)) = 0 := by
  have hA : MeasurableSet (⋃ k, O k)ᶜ := (MeasurableSet.iUnion hF.measurableSet).compl
  ext γ φ
  rw [hF.mulBorel_glue_apply hm (measurable_const.indicator hA)
    (isLocallyBoundedOn_indicator_one _)]
  simp only [LinearMap.zero_apply, _root_.zero_apply]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hF.ae_glueMeasure_mem] with x hx
  have : x ∉ (⋃ k, O k)ᶜ := fun h => h (mem_iUnion.mpr hx)
  rw [Set.indicator_of_notMem this, zero_mul, mul_zero, Pi.zero_apply]

/-- **Uniqueness**: a positive current `S` with `1_{O_k} S = 1_{O_k} B_k` for all `k` and
vanishing off `⋃ₖ O_k` is the glued current. -/
theorem eq_glue_of_mulBorel (hm : hF.HasLocallyFiniteMass) {S : LocalProductCurrent n U q}
    (hS : IsPositive S) (h₁ : ∀ k, mulBorel S ((O k).indicator fun _ => (1 : ℝ)) = truncAt B O k)
    (h₂ : mulBorel S ((⋃ k, O k)ᶜ.indicator fun _ => (1 : ℝ)) = 0) : S = hF.glue := by
  set A : Set (ComplexModel n) := ⋃ k, O k
  have hA : MeasurableSet A := MeasurableSet.iUnion hF.measurableSet
  have hsplit : S = mulBorel S (A.indicator fun _ => (1 : ℝ)) := by
    have e : (fun _ : (ComplexModel n) => (1 : ℝ)) = A.indicator (fun _ => (1 : ℝ)) +
        Aᶜ.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ A <;> simp [hx]
    conv_lhs => rw [← one_smul ℝ S, ← mulBorel_const hS 1, e,
      mulBorel_add hS (measurable_const.indicator hA) (isLocallyBoundedOn_indicator_one _)
        (measurable_const.indicator hA.compl) (isLocallyBoundedOn_indicator_one _), h₂, add_zero]
  ext γ φ
  have hlim : Tendsto (fun k => mulBorel S ((O k).indicator fun _ => (1 : ℝ)) γ φ) atTop
      (𝓝 (mulBorel S (A.indicator fun _ => (1 : ℝ)) γ φ)) := by
    simp only [mulBorel_apply hS (measurable_const.indicator (hF.measurableSet _))
      (isLocallyBoundedOn_indicator_one _), mulBorel_apply hS (measurable_const.indicator hA)
      (isLocallyBoundedOn_indicator_one _)]
    obtain ⟨C, -, hC⟩ := hS.exists_abs_density_le γ
    refine tendsto_integral_of_dominated_convergence (fun x => |φ x| * C) (fun k => ?_) ?_
      (fun k => ?_) ?_
    · exact (φ.continuous.measurable.mul ((measurable_const.indicator (hF.measurableSet k)).mul
        (hS.measurable_density γ))).aestronglyMeasurable
    · have := hS.integrable_mul_of_bounded (w := fun _ => C) φ.continuous φ.hasCompactSupport
        φ.tsupport_subset aestronglyMeasurable_const ⟨|C|, fun _ _ => le_rfl⟩
      refine this.norm.congr (ae_of_all _ fun x => ?_)
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg ((abs_nonneg _).trans (hC x))]
    · refine ae_of_all _ fun x => ?_
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |(O k).indicator (fun _ => (1 : ℝ)) x| * |hS.density γ x| ≤ 1 * C :=
            mul_le_mul (by by_cases h : x ∈ O k <;> simp [h]) (hC x) (abs_nonneg _) zero_le_one
        _ = C := one_mul _
    · refine ae_of_all _ fun x => ?_
      by_cases hx : x ∈ A
      · obtain ⟨k₀, hk₀⟩ := mem_iUnion.mp hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop k₀] with k hk
        rw [Set.indicator_of_mem (hF.mono hk hk₀), Set.indicator_of_mem hx]
      · have h0 : ∀ k, x ∉ O k := fun k hk => hx (mem_iUnion.mpr ⟨k, hk⟩)
        simp only [Set.indicator_of_notMem (h0 _), Set.indicator_of_notMem hx]
        exact tendsto_const_nhds
  simp_rw [h₁] at hlim
  rw [← congrArg (fun T : LocalProductCurrent n U q => T γ φ) hsplit] at hlim
  exact tendsto_nhds_unique hlim (hF.weakTendsto_truncAt_glue hm γ φ)

/-! #### The mass condition -/

theorem measure_inter_layer_eq {j k : ℕ} (hjk : j ≤ k) {K : Set (ComplexModel n)} (hK : IsCompact
    K)
    (hKU : K ⊆ U) :
    (hF.isPositive k).traceMeasure (K ∩ layer O j) =
      (hF.isPositive j).traceMeasure (K ∩ layer O j) := by
  have hlay := measurableSet_layer hF.measurableSet j
  have hw : IsTestWeight (U := U) (K.indicator fun _ => (1 : ℝ)) :=
    ⟨measurable_const.indicator hK.measurableSet, ⟨1, fun x => by
      by_cases hx : x ∈ K <;> simp [hx]⟩, K, hK, hKU, fun x hx => Set.indicator_of_notMem hx _⟩
  have key := hF.setIntegral_layer_consistent hjk (kahlerPower n q) hw
  have e : ∀ m, ∫ x in layer O j, K.indicator (fun _ => (1 : ℝ)) x *
        densityForm (hF.isPositive m) x (kahlerPower n q) ∂(hF.isPositive m).traceMeasure =
      ((hF.isPositive m).traceMeasure (K ∩ layer O j)).toReal := fun m => by
    rw [setIntegral_congr_ae hlay (by
      filter_upwards [densityForm_kahlerPower_ae (hF.isPositive m)] with x hx _
      rw [hx, mul_one])]
    rw [integral_indicator hK.measurableSet, setIntegral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.restrict_apply hK.measurableSet]
  rw [e k, e j] at key
  have hlt : ∀ m, (hF.isPositive m).traceMeasure (K ∩ layer O j) ≠ ⊤ := fun m =>
    (measure_mono inter_subset_left).trans_lt ((hF.isPositive m).traceMeasure_lt_top hK hKU) |>.ne
  exact (ENNReal.toReal_eq_toReal_iff' (hlt k) (hlt j)).mp key

theorem measure_inter_eq_sum {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U) (k : ℕ) :
    (hF.isPositive k).traceMeasure (K ∩ O k) =
      ∑ j ∈ Finset.range (k + 1), (hF.isPositive j).traceMeasure (K ∩ layer O j) := by
  have e : K ∩ O k = ⋃ j ∈ Finset.range (k + 1), K ∩ layer O j := by
    ext x
    simp only [mem_inter_iff, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨hxK, hx⟩
      obtain ⟨j, hjk, hj⟩ := exists_mem_layer hx
      exact ⟨j, Nat.lt_succ_of_le hjk, hxK, hj⟩
    · rintro ⟨j, hj, hxK, hx⟩
      exact ⟨hxK, hF.mono (Nat.le_of_lt_succ hj) hx.1⟩
  rw [e, measure_biUnion_finset (fun i _ j _ hij => (disjoint_layer hij).mono inter_subset_right
      inter_subset_right) fun j _ => hK.measurableSet.inter (measurableSet_layer hF.measurableSet
        j)]
  exact Finset.sum_congr rfl fun j hj =>
    hF.measure_inter_layer_eq (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hK hKU

/-- **The mass condition in terms of the truncations**: `μ(K) < ∞` for the compact `K ⊆ U` iff
`sup_k σ_{B_k}(K ∩ O_k) < ∞`. -/
theorem hasLocallyFiniteMass_iff : hF.HasLocallyFiniteMass ↔
    ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → ⨆ k, (hF.isPositive k).traceMeasure (K ∩ O
      k) < ⊤ := by
  have hμ : ∀ K : Set (ComplexModel n), IsCompact K → hF.glueMeasure K =
      ∑' j, (hF.isPositive j).traceMeasure (K ∩ layer O j) := fun K hK =>
    hF.glueMeasure_apply hK.measurableSet
  constructor
  · intro hm K hK hKU
    refine lt_of_le_of_lt (iSup_le fun k => ?_) (hm K hK hKU)
    rw [hF.measure_inter_eq_sum hK hKU, hμ K hK]
    exact sum_le_tsum _
  · intro h K hK hKU
    refine lt_of_le_of_lt ?_ (h K hK hKU)
    rw [hμ K hK]
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    refine le_trans ?_ (le_iSup _ N)
    rw [hF.measure_inter_eq_sum hK hKU]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ N))

end IsTruncationFamily

end Glue

/-! ### Wedge products of positive currents with powers of variable `(1,1)`-forms -/

section Wedge

/-- `formPower (c β) q = c^q β^q`. -/
theorem formPower_smul (c : ℝ) (β : RealForm n 2) :
    ∀ q, formPower (c • β) q = c ^ q • formPower β q
  | 0 => by simp [formPower_zero]
  | q + 1 => by
    simp only [formPower_succ, formPower_smul c β q, ← wedgeBilin_apply, map_smul,
      LinearMap.smul_apply, smul_smul, pow_succ']

/-- If `α` and `β - α` are semipositive `(1,1)`-forms, then `β^q - α^q` is strongly positive. -/
theorem formPower_sub_mem_spCone {α β : RealForm n 2} (hα : IsSemipositiveOneOne α)
    (hβα : IsSemipositiveOneOne (β - α)) : ∀ q, formPower β q - formPower α q ∈ spCone q
  | 0 => by simp
  | q + 1 => by
    have hβ : IsSemipositiveOneOne β := by simpa using hα.add hβα
    have h1 := wedge_mem_spCone (formPower_sub_mem_spCone hα hβα q) hβ
    have h2 := wedge_mem_spCone (formPower_mem_spCone hα q) hβα
    have e : formPower β (q + 1) - formPower α (q + 1) =
        coordinateWedge (formPower β q - formPower α q) β +
          coordinateWedge (formPower α q) (β - α) := by
      simp only [formPower_succ, ← wedgeBilin_apply, map_sub, LinearMap.sub_apply]
      abel
    rw [e]
    exact add_mem h1 h2

open Classical in
/-- The power `β^q` of a semipositive `(1,1)`-form, as a constant `(q,q)`-form of `Λ_q` (and `0`
for other two-forms). -/
def powerSpan (q : ℕ) (β : RealForm n 2) : formSpan n q :=
  if h : IsSemipositiveOneOne β then
    ⟨formPower β q, mem_formSpan_of_mem_spCone (formPower_mem_spCone h q)⟩
  else 0

theorem coe_powerSpan {q : ℕ} {β : RealForm n 2} (h : IsSemipositiveOneOne β) :
    (powerSpan q β : RealForm n (2 * q)) = formPower β q := by
  rw [powerSpan, dite_eq_left h]

theorem powerSpan_kahlerForm (q : ℕ) : powerSpan q (kahlerForm n) = kahlerPower n q := by
  rw [powerSpan, dite_eq_left isSemipositiveOneOne_kahlerForm]
  rfl

variable {U : Opens (ComplexModel n)} {q : ℕ}

open Classical in
/-- **The measure `T ∧ α^q`** of a positive current `T` of bidimension `(q,q)` and a variable
semipositive `(1,1)`-form `α`: the trace measure of `T` with density `x ↦ L_x(α(x)^q)` (and `0`
when `T` is not positive). -/
def wedgePowerMeasure (T : LocalProductCurrent n U q) (α : (ComplexModel n) → RealForm n 2)
    : Measure (ComplexModel n) :=
  if hT : IsPositive T then
    hT.traceMeasure.withDensity fun x => ENNReal.ofReal (densityForm hT x (powerSpan q (α x)))
  else 0

/-- For the Euclidean Kähler form, `T ∧ ω₀^q` is the trace measure of `T`. -/
theorem wedgePowerMeasure_kahlerForm {T : LocalProductCurrent n U q} (hT : IsPositive T) :
    wedgePowerMeasure T (fun _ => kahlerForm n) = hT.traceMeasure := by
  rw [wedgePowerMeasure, dite_eq_left hT]
  simp_rw [powerSpan_kahlerForm]
  rw [withDensity_congr_ae (g := 1) (by
    filter_upwards [densityForm_kahlerPower_ae hT] with x hx
    rw [hx, ENNReal.ofReal_one, Pi.one_apply]), withDensity_one]

/-- **Comparison of trace measures**: if `α ≤ c ω₀` on `K`, then
`(T ∧ α^q)(K ∩ A) ≤ c^q σ_T(K ∩ A)`. -/
theorem wedgePowerMeasure_le {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {α : (ComplexModel n) → RealForm n 2} {c : ℝ} {K A : Set (ComplexModel n)} (hK : MeasurableSet
      K) (hA : MeasurableSet A)
    (hα : ∀ x ∈ K, IsSemipositiveOneOne (α x))
    (hαc : ∀ x ∈ K, IsSemipositiveOneOne (c • kahlerForm n - α x)) :
    wedgePowerMeasure T α (K ∩ A) ≤ ENNReal.ofReal (c ^ q) * hT.traceMeasure (K ∩ A) := by
  rw [wedgePowerMeasure, dite_eq_left hT, withDensity_apply _ (hK.inter hA), ← setLIntegral_const]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem (hK.inter hA), ae_restrict_of_ae (ae_densityForm_nonneg hT),
    ae_restrict_of_ae (densityForm_kahlerPower_ae hT)] with x hx hpos hone
  refine ENNReal.ofReal_le_ofReal ?_
  have hmem : (c ^ q • kahlerPower n q - powerSpan q (α x) : formSpan n q) ∈ posCone n q := by
    change ((c ^ q • kahlerPower n q - powerSpan q (α x) : formSpan n q) :
      RealForm n (2 * q)) ∈ spCone q
    rw [Submodule.coe_sub, Submodule.coe_smul, coe_powerSpan (hα x hx.1)]
    have h := formPower_sub_mem_spCone (hα x hx.1) (hαc x hx.1) q
    rwa [formPower_smul] at h
  have h := hpos _ hmem
  rw [map_sub, map_smul, hone, smul_eq_mul, mul_one, sub_nonneg] at h
  exact h

/-- A continuous `(1,1)`-form is bounded by a multiple of `ω₀` on a compact set. -/
theorem exists_smul_kahlerForm_sub {α : (ComplexModel n) → RealForm n 2} {K : Set (ComplexModel
    n)} (hK : IsCompact K)
    (hαc : ContinuousOn α K) (hα : ∀ x ∈ K, IsOneOne (α x)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ K, IsSemipositiveOneOne (c • kahlerForm n - α x) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hαc
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h1 := (isSemipositiveOneOne_norm_smul_kahlerForm (hα x hx)).1
  have h2 : IsSemipositiveOneOne ((max C 0 - ‖α x‖) • kahlerForm n) :=
    isSemipositiveOneOne_kahlerForm.smul (sub_nonneg.mpr ((hC x hx).trans (le_max_left _ _)))
  have e : max C 0 • kahlerForm n - α x =
      (max C 0 - ‖α x‖) • kahlerForm n + (‖α x‖ • kahlerForm n - α x) := by
    module
  rw [e]
  exact h2.add h1

end Wedge

/-! ### The non-pluripolar product of degree `p` -/

section Product

variable {p q : ℕ} (hqp : q + p = n)

/-- The Bedford–Taylor product `⋀ⱼ dd^c (φⱼ ∨ (-k))` of the truncations at level `k`, on `U`
(a positive closed current of bidimension `(q,q)` when the `φⱼ` are psh). -/
def truncatedBT (U : Opens (ComplexModel n)) (φ : Fin p → (ComplexModel n) → EReal) (k : ℕ)
    : LocalProductCurrent n U q :=
  btProduct p q (fun i => truncationReal (φ i) k) (oneCurrentOf (U := U) hqp)

variable {U : Opens (ComplexModel n)} {φ : Fin p → (ComplexModel n) → EReal}

theorem isPositive_truncatedBT (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (k : ℕ) :
    IsPositive (truncatedBT hqp U φ k) ∧ IsClosedAny q (truncatedBT hqp U φ k) :=
  isPositive_btProduct p q _ _ (isPositive_oneCurrentOf hqp) (isClosedAny_oneCurrentOf hqp)
    fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k

/-- The truncations of psh functions form a truncation family, with the strict loci
`O_k = {φ₁ > -k, …, φ_p > -k}` (consistency:
    `BedfordTaylorTopDegree.mulBorel_btProduct_truncation_consistent`,
plurifine locality of the Bedford–Taylor products). -/
theorem isTruncationFamily (hφ : ∀ i, PlurisubharmonicOn (φ i) U) :
    IsTruncationFamily (truncatedBT hqp U φ) (BedfordTaylorTopDegree.strictLocus U φ) where
  isPositive k := (isPositive_truncatedBT hqp hφ k).1
  measurableSet := BedfordTaylorTopDegree.measurableSet_strictLocus hφ
  subset _ := fun _ hz => hz.1
  mono _ _ hkl := BedfordTaylorTopDegree.strictLocus_mono U φ hkl
  consistent hkl := BedfordTaylorTopDegree.mulBorel_btProduct_truncation_consistent hqp hφ hkl

theorem truncAt_eq_truncatedProduct (k : ℕ) :
    truncAt (truncatedBT hqp U φ) (BedfordTaylorTopDegree.strictLocus U φ) k =
      BedfordTaylorTopDegree.truncatedProduct hqp U φ k := rfl

variable (U φ) in
/-- **The source well-definedness condition** `eq:welldefinepluri` on `U`: for every connected
open `V ⊆ U`, every smooth semipositive `(1,1)`-form `α` on `V` and every compact `K ⊆ V`,
`sup_k ∫_{K ∩ O_k} (⋀ⱼ dd^c (φⱼ ∨ (-k)))|_V ∧ α^{n-p} < ∞`. -/
def IsWellDefinedOn : Prop :=
  ∀ (V : Opens (ComplexModel n)) (hVU : V ≤ U), IsConnected (V : Set (ComplexModel n)) →
    ∀ α : (ComplexModel n) → RealForm n 2, ContDiffOn ℝ ∞ α V → (∀ x ∈ V, IsSemipositiveOneOne (α
      x)) →
      ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ V →
        ⨆ k, wedgePowerMeasure (LocalBedfordTaylorLocality.restrict hVU (truncatedBT hqp U φ k)) α
          (K ∩ BedfordTaylorTopDegree.strictLocus U φ k) < ⊤

/-- **The well-definedness condition is the Euclidean local mass condition** of the
truncation family (FPT `eq:nonpluripolar-local-mass-condition`). -/
theorem isWellDefinedOn_iff (hφ : ∀ i, PlurisubharmonicOn (φ i) U) :
    IsWellDefinedOn hqp U φ ↔ (isTruncationFamily hqp hφ).HasLocallyFiniteMass := by
  set hF := isTruncationFamily hqp hφ
  set O := BedfordTaylorTopDegree.strictLocus U φ
  rw [hF.hasLocallyFiniteMass_iff]
  have hres : ∀ (V : Opens (ComplexModel n)) (hVU : V ≤ U) (k : ℕ) (A : Set (ComplexModel n)),
    MeasurableSet A → A ⊆ V →
      (LocalBedfordTaylorLocality.isPositive_restrict (hF.isPositive k) hVU).traceMeasure A =
        (hF.isPositive k).traceMeasure A := fun V hVU k A hA hAV => by
    rw [LocalBedfordTaylorLocality.traceMeasure_restrict, Measure.restrict_apply hA,
      inter_eq_left.mpr hAV]
  constructor
  · intro hW K hK hKU
    have hε : ∀ x : (ComplexModel n), ∃ ε > (0 : ℝ), x ∈ U → Metric.ball x ε ⊆ U := fun x => by
      by_cases hx : x ∈ U
      · obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.mp U.isOpen x hx
        exact ⟨ε, hε, fun _ => h⟩
      · exact ⟨1, one_pos, fun h => absurd h hx⟩
    choose ε hεpos hεU using hε
    obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x => Metric.closedBall x (ε x / 2))
      fun x _ => Metric.closedBall_mem_nhds x (half_pos (hεpos x))
    let V : (ComplexModel n) → Opens (ComplexModel n) := fun x => ⟨Metric.ball x (ε x),
      Metric.isOpen_ball⟩
    have hVU : ∀ x ∈ t, V x ≤ U := fun x hx => hεU x (hKU (htK x hx))
    have hKV : ∀ x, K ∩ Metric.closedBall x (ε x / 2) ⊆ V x := fun x y hy =>
      Metric.closedBall_subset_ball (half_lt_self (hεpos x)) hy.2
    have hKc : ∀ x, IsCompact (K ∩ Metric.closedBall x (ε x / 2)) := fun x =>
      hK.inter_right Metric.isClosed_closedBall
    have hbound : ∀ x (hx : x ∈ t), ⨆ k, (hF.isPositive k).traceMeasure
        (K ∩ Metric.closedBall x (ε x / 2) ∩ O k) < ⊤ := fun x hx => by
      have h := hW (V x) (hVU x hx) ((convex_ball x (ε x)).isConnected
        (Metric.nonempty_ball.mpr (hεpos x))) (fun _ => kahlerForm n) contDiffOn_const
        (fun _ _ => isSemipositiveOneOne_kahlerForm) _ (hKc x) (hKV x)
      simp_rw [wedgePowerMeasure_kahlerForm (LocalBedfordTaylorLocality.isPositive_restrict
        (hF.isPositive _) (hVU x hx))] at h
      refine lt_of_le_of_lt (iSup_mono fun k => ?_) h
      rw [hres (V x) (hVU x hx) k _ ((hKc x).measurableSet.inter (hF.measurableSet k))
        (inter_subset_left.trans (hKV x))]
    refine lt_of_le_of_lt (iSup_le fun k => ?_) (ENNReal.sum_lt_top.mpr fun x hx =>
      hbound x hx)
    have hsub : K ∩ O k ⊆ ⋃ x ∈ t, K ∩ Metric.closedBall x (ε x / 2) ∩ O k := by
      rintro y ⟨hyK, hyO⟩
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hKt hyK)
      exact mem_iUnion₂.mpr ⟨x, hx, ⟨hyK, hyx⟩, hyO⟩
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun x hx => le_iSup (fun k => (hF.isPositive k).traceMeasure
        (K ∩ Metric.closedBall x (ε x / 2) ∩ O k)) k))
  · intro hm V hVU _ α hαs hαp K hK hKV
    obtain ⟨c, -, hc⟩ := exists_smul_kahlerForm_sub hK (hαs.continuousOn.mono hKV)
      fun x hx => (hαp x (hKV hx)).1
    have hle : ∀ k, wedgePowerMeasure (LocalBedfordTaylorLocality.restrict hVU
        (truncatedBT hqp U φ k)) α (K ∩ O k) ≤
          ENNReal.ofReal (c ^ q) * (hF.isPositive k).traceMeasure (K ∩ O k) := fun k => by
      refine (wedgePowerMeasure_le (LocalBedfordTaylorLocality.isPositive_restrict
        (hF.isPositive k) hVU) hK.measurableSet (hF.measurableSet k)
        (fun x hx => hαp x (hKV hx)) hc).trans ?_
      rw [hres V hVU k _ (hK.measurableSet.inter (hF.measurableSet k))
        (inter_subset_left.trans hKV)]
    refine lt_of_le_of_lt (iSup_le fun k => (hle k).trans
      (mul_le_mul_of_nonneg_left (le_iSup (fun k => (hF.isPositive k).traceMeasure (K ∩ O k)) k)
        (zero_le)))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hm K hK (hKV.trans hVU)))

variable (U φ) in
open Classical in
/-- **The non-pluripolar product** `⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩` on `U` (source `def:npp:L69`),
a current of bidimension `(q,q)`, `q + p = n`: the glued current of the truncation family
`1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))` (`IsTruncationFamily.glue`), characterized by
`1_{O_k} ⟨⋯⟩ = 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))` and vanishing off `⋃ₖ O_k`
(`mulBorel_nonPluripolarProduct_strictLocus`, `mulBorel_nonPluripolarProduct_compl`,
`eq_nonPluripolarProduct_of_mulBorel`).  It is `0` when the `φⱼ` are not psh or the product is not
well defined. -/
def nonPluripolarProduct : LocalProductCurrent n U q :=
  if hφ : ∀ i, PlurisubharmonicOn (φ i) U then (isTruncationFamily hqp hφ).glue else 0

theorem nonPluripolarProduct_eq (hφ : ∀ i, PlurisubharmonicOn (φ i) U) :
    nonPluripolarProduct hqp U φ = (isTruncationFamily hqp hφ).glue := by
  rw [nonPluripolarProduct, dite_eq_left hφ]

/-- **The non-pluripolar product is the weak limit of the truncated products** (FPT
`lem:nonpluripolar-truncation-limit`). -/
theorem weakTendsto_truncatedProduct (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hW : IsWellDefinedOn hqp U φ) :
    LocalBedfordTaylorContinuity.WeakTendsto (BedfordTaylorTopDegree.truncatedProduct hqp U φ)
      (nonPluripolarProduct hqp U φ) := by
  rw [nonPluripolarProduct_eq hqp hφ]
  exact (isTruncationFamily hqp hφ).weakTendsto_truncAt_glue
    ((isWellDefinedOn_iff hqp hφ).mp hW)

/-- **The non-pluripolar product is a positive current** (`prop:npp1` (5), positivity). -/
theorem isPositive_nonPluripolarProduct (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hW : IsWellDefinedOn hqp U φ) : IsPositive (nonPluripolarProduct hqp U φ) := by
  rw [nonPluripolarProduct_eq hqp hφ]
  exact (isTruncationFamily hqp hφ).isPositive_glue ((isWellDefinedOn_iff hqp hφ).mp hW)

/-- **The defining identity** `eq:npp`:
`1_{O_k} ⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩ = 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))`. -/
theorem mulBorel_nonPluripolarProduct_strictLocus (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hW : IsWellDefinedOn hqp U φ) (k : ℕ) :
    mulBorel (nonPluripolarProduct hqp U φ)
        ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) =
      BedfordTaylorTopDegree.truncatedProduct hqp U φ k := by
  rw [nonPluripolarProduct_eq hqp hφ]
  exact (isTruncationFamily hqp hφ).mulBorel_glue_indicator ((isWellDefinedOn_iff hqp hφ).mp hW) k

/-- **Extension by zero**: the product vanishes off `⋃ₖ O_k`. -/
theorem mulBorel_nonPluripolarProduct_compl (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hW : IsWellDefinedOn hqp U φ) :
    mulBorel (nonPluripolarProduct hqp U φ)
        ((⋃ k, BedfordTaylorTopDegree.strictLocus U φ k)ᶜ.indicator fun _ => (1 : ℝ)) = 0 := by
  rw [nonPluripolarProduct_eq hqp hφ]
  exact (isTruncationFamily hqp hφ).mulBorel_glue_compl ((isWellDefinedOn_iff hqp hφ).mp hW)

/-- **The source definition determines the product**: a positive current with
`1_{O_k} S = 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))` for every `k` and vanishing off `⋃ₖ O_k` is the
non-pluripolar product. -/
theorem eq_nonPluripolarProduct_of_mulBorel (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hW : IsWellDefinedOn hqp U φ) {S : LocalProductCurrent n U q} (hS : IsPositive S)
    (h₁ : ∀ k, mulBorel S ((BedfordTaylorTopDegree.strictLocus U φ k).indicator
      fun _ => (1 : ℝ)) = BedfordTaylorTopDegree.truncatedProduct hqp U φ k)
    (h₂ : mulBorel S ((⋃ k, BedfordTaylorTopDegree.strictLocus U φ k)ᶜ.indicator
      fun _ => (1 : ℝ)) = 0) :
    S = nonPluripolarProduct hqp U φ := by
  rw [nonPluripolarProduct_eq hqp hφ]
  exact (isTruncationFamily hqp hφ).eq_glue_of_mulBorel ((isWellDefinedOn_iff hqp hφ).mp hW) hS
    h₁ h₂

end Product

end SGPT.NPP.NonPluripolarCurrent
