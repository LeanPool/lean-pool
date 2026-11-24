/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentLocality
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalPositiveCurrentGluing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

/-!
# Gluing positive currents over an open cover

Source: the sheaf property of currents used in `chapter_npp.tex`, `def:npp:L146` (the product
`T₁ ∧ ⋯ ∧ T_p` is *defined* by its restrictions `(T₁ ∧ ⋯ ∧ T_p)|_U` to the members `U` of an open
cover); Xia, *Foundations of pluripotential theory*, the paragraph after
`prop:nonpluripolar-local-calculus` ("the local products then glue to a positive current") and
`thm:positive-current-order-zero` (positive currents have measure coefficients).

Let `U ⊆ ℂⁿ` be open and let `(W i)` be open subsets of `U` covering `U`, with positive currents
`T i` of bidimension `(q,q)` on `W i` that agree on all overlaps
(`T i|_{W i ∩ W j} = T j|_{W i ∩ W j}`).  Then there is a unique current `S` on `U` with
`S|_{W i} = T i` for all `i`, and it is positive.

* Uniqueness is TN's `LocalBedfordTaylorCalculus.eq_of_local` (partition of unity).
* Existence: by Lindelöf a countable subfamily `W (f 0), W (f 1), …` covers `U`.  On the layers
  `L_k = W (f k) \ ⋃_{j<k} W (f j)` we keep the trace measure and the pointwise density form of
  `T (f k)` (`glueMeasure`, `glueDensity`); the glued measure is finite on compact subsets of `U`
  and `S(γ) = L_x(γ) μ` (`glueCurrent`).  The restriction of `μ` to `W a` is the trace measure of
  `T a`, and the glued density agrees with the density form of `T a` almost everywhere there,
  because two positive currents agreeing on an open set have the same trace measures and density
  forms on it (`traceMeasure_restrict`, `ae_densityForm_restrict_eq`).

## Main results

* `SGPT.Currents.eq_of_isEmpty` — all currents on the empty open set coincide.
* `SGPT.Currents.IsCompatibleFamily` — positive currents agreeing on overlaps.
* `SGPT.Currents.IsCompatibleFamily.exists_glue` — gluing (existence and positivity).
* `SGPT.Currents.IsCompatibleFamily.existsUnique_glue` — the glued current is unique.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal

namespace SGPT.Currents

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
open SGPT.NPP.NonPluripolarCurrent

variable {n q : ℕ}

/-! ### Elementary facts -/

/-- All currents on an empty open set coincide. -/
theorem eq_of_isEmpty {V : Opens (ComplexModel n)} (hV : (V : Set (ComplexModel n)) = ∅)
    (S S' : LocalProductCurrent n V q) :
    S = S' := by
  have h0 : ∀ φ : 𝓓(V, ℝ), φ = 0 := fun φ => by
    ext x
    have hx : x ∉ (V : Set (ComplexModel n)) := by rw [hV]; exact notMem_empty x
    simp [testFunction_eq_zero_of_notMem φ hx]
  ext γ φ
  rw [h0 φ, map_zero, map_zero]

/-- The trace measure depends only on the current. -/
theorem traceMeasure_congr {V : Opens (ComplexModel n)} {S S' : LocalProductCurrent n V q} (h : S
    = S')
    (hS : IsPositive S) (hS' : IsPositive S') : hS.traceMeasure = hS'.traceMeasure := by
  subst h
  rfl

/-- The density form depends only on the current. -/
theorem densityForm_congr {V : Opens (ComplexModel n)} {S S' : LocalProductCurrent n V q} (h : S =
    S')
    (hS : IsPositive S) (hS' : IsPositive S') : densityForm hS = densityForm hS' := by
  subst h
  rfl

/-- **Two positive currents agreeing on an open set have the same trace measure there**, and their
density forms agree almost everywhere there. -/
theorem traceMeasure_restrict_eq_and_ae_densityForm {A B V : Opens (ComplexModel n)} {S :
    LocalProductCurrent n A q}
    {S' : LocalProductCurrent n B q} (hS : IsPositive S) (hS' : IsPositive S') (hVA : V ≤ A)
    (hVB : V ≤ B) (h : restrict hVA S = restrict hVB S') :
    hS.traceMeasure.restrict V = hS'.traceMeasure.restrict V ∧
      ∀ᵐ x ∂(hS.traceMeasure.restrict V), densityForm hS x = densityForm hS' x := by
  have hR := isPositive_restrict hS hVA
  have hR' := isPositive_restrict hS' hVB
  have e1 := traceMeasure_restrict hS hVA
  have e2 := traceMeasure_restrict hS' hVB
  have e3 := traceMeasure_congr h hR hR'
  have hμ : hS.traceMeasure.restrict V = hS'.traceMeasure.restrict V := by
    rw [← e1, ← e2, e3]
  refine ⟨hμ, ?_⟩
  have a1 := ae_densityForm_restrict_eq hS hVA
  have a2 := ae_densityForm_restrict_eq hS' hVB
  rw [e1] at a1
  rw [e2, ← hμ] at a2
  have e4 := densityForm_congr h hR hR'
  filter_upwards [a1, a2] with x h1 h2
  rw [← h1, ← h2, e4]

/-! ### A current from a measure and a bounded density form -/

section OfMeasure

variable {U : Opens (ComplexModel n)}

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

/-- The restriction of `g(γ) μ` to an open `V ≤ U` is a positive current `T` on `V` as soon as
`μ|_V` is the trace measure of `T` and `g` is its density form almost everywhere. -/
theorem restrict_ofMeasureDensity (hμ : IsMeasureDensity U μ g) {V : Opens (ComplexModel n)} (hVU
    : V ≤ U)
    {T : LocalProductCurrent n V q} (hT : IsPositive T) (h1 : μ.restrict V = hT.traceMeasure)
    (h2 : ∀ᵐ x ∂hT.traceMeasure, g x = densityForm hT x) :
    restrict hVU (ofMeasureDensity U μ g) = T := by
  ext γ φ
  rw [LocalBedfordTaylorLocality.restrict_apply, ofMeasureDensity_apply hμ,
    apply_eq_integral_densityForm hT]
  have hf : (extTest hVU φ : (ComplexModel n) → ℝ) = (φ : (ComplexModel n) → ℝ)
    := funext (extTest_apply hVU φ)
  rw [hf, ← integral_restrict_mul φ μ, h1]
  refine integral_congr_ae ?_
  filter_upwards [h2] with x hx
  rw [hx]

end OfMeasure

/-! ### Compatible families and their gluing -/

section Glue

variable {U : Opens (ComplexModel n)}

/-- A **compatible family** of positive currents on the open sets `W i`: they agree on all
overlaps. -/
structure IsCompatibleFamily {ι : Type*} (W : ι → Opens (ComplexModel n)) (T : ∀ i,
    LocalProductCurrent n (W i) q) :
    Prop where
  isPositive : ∀ i, IsPositive (T i)
  agree : ∀ i j, restrict (inf_le_left : W i ⊓ W j ≤ W i) (T i) =
    restrict (inf_le_right : W i ⊓ W j ≤ W j) (T j)

namespace IsCompatibleFamily

variable {ι : Type*} {W : ι → Opens (ComplexModel n)} {T : ∀ i, LocalProductCurrent n (W i) q}

theorem comp (hF : IsCompatibleFamily W T) {κ : Type*} (f : κ → ι) :
    IsCompatibleFamily (W ∘ f) fun k => T (f k) :=
  ⟨fun k => hF.isPositive (f k), fun k l => hF.agree (f k) (f l)⟩

/-- The trace measures agree on overlaps. -/
theorem traceMeasure_restrict_inter (hF : IsCompatibleFamily W T) (i j : ι) :
    (hF.isPositive i).traceMeasure.restrict (W i ⊓ W j : Opens (ComplexModel n)) =
      (hF.isPositive j).traceMeasure.restrict (W i ⊓ W j : Opens (ComplexModel n)) :=
  (traceMeasure_restrict_eq_and_ae_densityForm (hF.isPositive i) (hF.isPositive j) _ _
    (hF.agree i j)).1

/-- The density forms agree almost everywhere on overlaps. -/
theorem ae_densityForm_inter (hF : IsCompatibleFamily W T) (i j : ι) :
    ∀ᵐ x ∂(hF.isPositive i).traceMeasure, x ∈ (W j : Set (ComplexModel n)) →
      densityForm (hF.isPositive i) x = densityForm (hF.isPositive j) x := by
  have h := (traceMeasure_restrict_eq_and_ae_densityForm (hF.isPositive i) (hF.isPositive j) _ _
    (hF.agree i j)).2
  rw [ae_restrict_iff' (W i ⊓ W j).isOpen.measurableSet] at h
  have hmem : ∀ᵐ x ∂(hF.isPositive i).traceMeasure, x ∈ (W i : Set (ComplexModel n)) :=
    (measure_eq_zero_iff_ae_notMem.mp (hF.isPositive i).traceMeasure_compl).mono
      fun x hx => by simpa using hx
  filter_upwards [h, hmem] with x hx hxi hxj
  exact hx ⟨hxi, hxj⟩

end IsCompatibleFamily

/-! #### Gluing a sequence -/

section Seq

variable {W : ℕ → Opens (ComplexModel n)} {T : ∀ k, LocalProductCurrent n (W k) q}
  (hF : IsCompatibleFamily W T)

/-- The glued measure `μ = ∑ₖ σ_{T k}|_{L_k}` on the layers `L_k = W k \ ⋃_{j<k} W j`. -/
def glueMeasure : Measure (ComplexModel n) :=
  Measure.sum fun k => ((hF.isPositive k).traceMeasure).restrict (layer (fun k => (W k : Set
    (ComplexModel n))) k)

/-- The density forms as a function of `(x, k)`. -/
def layerDensity (z : (ComplexModel n) × ℕ) : formSpan n q →ₗ[ℝ] ℝ :=
  densityForm (hF.isPositive z.2) z.1

/-- The glued density form: on the `k`-th layer, the density form of `T k`. -/
def glueDensity (x : (ComplexModel n)) : formSpan n q →ₗ[ℝ] ℝ :=
  layerDensity hF (x, level (fun k => (W k : Set (ComplexModel n))) x)

theorem densityForm_congr_index {k l : ℕ} (h : k = l) (x : (ComplexModel n)) :
    densityForm (hF.isPositive k) x = densityForm (hF.isPositive l) x := by
  subst h
  rfl

theorem glueDensity_of_mem_layer {k : ℕ} {x : (ComplexModel n)} (hx : x ∈ layer (fun k => (W k :
    Set (ComplexModel n))) k) :
    glueDensity hF x = densityForm (hF.isPositive k) x :=
  densityForm_congr_index hF (level_eq_of_mem_layer hx) x

theorem measurableSet_W (k : ℕ) : MeasurableSet ((fun k => (W k : Set (ComplexModel n))) k) :=
  (W k).isOpen.measurableSet

theorem measurable_glueDensity (γ : formSpan n q) : Measurable fun x => glueDensity hF x γ := by
  have h : Measurable fun z : (ComplexModel n) × ℕ => layerDensity hF z γ := by
    apply measurable_from_prod_countable_left
    intro k
    exact measurable_densityForm (hF.isPositive k) γ
  have hl : Measurable fun x : (ComplexModel n) => (x, level (fun k => (W k : Set (ComplexModel
    n))) x) :=
    measurable_id.prodMk (measurable_level (measurableSet_W (W := W)))
  exact h.comp hl

theorem glueMeasure_apply {s : Set (ComplexModel n)} (hs : MeasurableSet s) :
    glueMeasure hF s =
      ∑' k, (hF.isPositive k).traceMeasure (s ∩ layer (fun k => (W k : Set (ComplexModel n))) k)
        := by
  rw [glueMeasure, Measure.sum_apply _ hs]
  simp only [Measure.restrict_apply hs]

/-- **The restriction of the glued measure to `W a` is the trace measure of `T a`.** -/
theorem glueMeasure_restrict (a : ℕ) :
    (glueMeasure hF).restrict (W a) = (hF.isPositive a).traceMeasure := by
  ext s hs
  rw [Measure.restrict_apply hs, glueMeasure_apply hF (hs.inter (W a).isOpen.measurableSet)]
  set O : ℕ → Set (ComplexModel n) := fun k => (W k : Set (ComplexModel n))
  have hk : ∀ k, (hF.isPositive k).traceMeasure (s ∩ (W a : Set (ComplexModel n)) ∩ layer O k) =
      (hF.isPositive a).traceMeasure (s ∩ (W a : Set (ComplexModel n)) ∩ layer O k) := by
    intro k
    have hsub : s ∩ (W a : Set (ComplexModel n)) ∩ layer O k ⊆ ((W k ⊓ W a : Opens (ComplexModel
      n)) : Set (ComplexModel n)) :=
      fun x hx => ⟨layer_subset k hx.2, hx.1.2⟩
    have hm : MeasurableSet (s ∩ (W a : Set (ComplexModel n)) ∩ layer O k) :=
      (hs.inter (W a).isOpen.measurableSet).inter
        (measurableSet_layer (fun k => (W k).isOpen.measurableSet) k)
    have e := hF.traceMeasure_restrict_inter k a
    rw [← inter_eq_left.mpr hsub, ← Measure.restrict_apply hm, e, Measure.restrict_apply hm]
  simp_rw [hk]
  rw [← measure_iUnion (fun j k hjk => (Disjoint.mono inter_subset_right inter_subset_right
      (disjoint_layer hjk)))
    (fun k => (hs.inter (W a).isOpen.measurableSet).inter
      (measurableSet_layer (fun k => (W k).isOpen.measurableSet) k))]
  have hU : (⋃ k, s ∩ (W a : Set (ComplexModel n)) ∩ layer O k) = s ∩ (W a : Set (ComplexModel n))
    := by
    refine subset_antisymm (iUnion_subset fun k => inter_subset_left) fun x hx => ?_
    obtain ⟨j, -, hj⟩ := exists_mem_layer (O := O) (k := a) hx.2
    exact mem_iUnion.mpr ⟨j, hx, hj⟩
  rw [hU]
  have hc := (hF.isPositive a).traceMeasure_compl
  refine le_antisymm (measure_mono inter_subset_left) ?_
  calc (hF.isPositive a).traceMeasure s
      ≤ (hF.isPositive a).traceMeasure (s ∩ (W a : Set (ComplexModel n)) ∪ (W a : Set
        (ComplexModel n))ᶜ) :=
        measure_mono fun x hx => by
          by_cases h : x ∈ (W a : Set (ComplexModel n))
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr h
    _ ≤ (hF.isPositive a).traceMeasure (s ∩ (W a : Set (ComplexModel n))) +
          (hF.isPositive a).traceMeasure ((W a : Set (ComplexModel n))ᶜ) := measure_union_le _ _
    _ = _ := by rw [hc, add_zero]

/-- **The glued density form is the density form of `T a` almost everywhere for its trace
measure.** -/
theorem ae_glueDensity (a : ℕ) :
    ∀ᵐ x ∂(hF.isPositive a).traceMeasure, glueDensity hF x = densityForm (hF.isPositive a) x := by
  set O : ℕ → Set (ComplexModel n) := fun k => (W k : Set (ComplexModel n))
  have hall : ∀ᵐ x ∂(hF.isPositive a).traceMeasure, ∀ k, x ∈ O k →
      densityForm (hF.isPositive a) x = densityForm (hF.isPositive k) x :=
    ae_all_iff.mpr fun k => hF.ae_densityForm_inter a k
  have hmem : ∀ᵐ x ∂(hF.isPositive a).traceMeasure, x ∈ (W a : Set (ComplexModel n)) :=
    (measure_eq_zero_iff_ae_notMem.mp (hF.isPositive a).traceMeasure_compl).mono
      fun x hx => by simpa using hx
  filter_upwards [hall, hmem] with x hx hxa
  obtain ⟨j, -, hj⟩ := exists_mem_layer (O := O) (k := a) hxa
  rw [glueDensity_of_mem_layer hF hj, hx j (layer_subset j hj)]

theorem ae_abs_glueDensity_le (γ : formSpan n q) :
    ∀ᵐ x ∂glueMeasure hF, |glueDensity hF x γ| ≤ orderUnitConst γ := by
  rw [glueMeasure, Measure.ae_sum_iff]
  intro k
  rw [ae_restrict_iff' (measurableSet_layer (fun k => (W k).isOpen.measurableSet) k)]
  filter_upwards [ae_abs_densityForm_le (hF.isPositive k) γ] with x hx hmem
  rw [glueDensity_of_mem_layer hF hmem]
  exact hx

/-- **The glued data define a current on any open `U` covered by the `W k`.** -/
theorem isMeasureDensity_glue (hWU : ∀ k, W k ≤ U) (hcov : ∀ x ∈ U, ∃ k, x ∈ W k) :
    IsMeasureDensity U (glueMeasure hF) (glueDensity hF) where
  compl := by
    rw [glueMeasure_apply hF U.isOpen.measurableSet.compl, tsum_eq_zero_iff]
    intro k
    refine measure_mono_null (fun x hx => ?_) (hF.isPositive k).traceMeasure_compl
    exact absurd (hWU k (layer_subset k hx.2)) hx.1
  lt_top := by
    intro K hK hKU
    have hnhds : ∀ x ∈ K, ∃ k, ∃ r > 0, Metric.closedBall x r ⊆ (W k : Set (ComplexModel n)) := by
      intro x hx
      obtain ⟨k, hk⟩ := hcov x (hKU hx)
      obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (W k).isOpen x hk
      exact ⟨k, r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hb⟩
    choose! k r hr hb using hnhds
    obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x => Metric.closedBall x (r x))
      fun x hx => Metric.closedBall_mem_nhds x (hr x hx)
    refine (measure_mono hKt).trans_lt ((measure_biUnion_finset_le t _).trans_lt ?_)
    refine ENNReal.sum_lt_top.mpr fun x hx => ?_
    have hsub := hb x (htK x hx)
    have e := glueMeasure_restrict hF (k x)
    have e' : glueMeasure hF (Metric.closedBall x (r x)) =
        (hF.isPositive (k x)).traceMeasure (Metric.closedBall x (r x)) := by
      rw [← e, Measure.restrict_apply Metric.isClosed_closedBall.measurableSet,
        inter_eq_left.mpr hsub]
    rw [e']
    exact (hF.isPositive (k x)).traceMeasure_lt_top (isCompact_closedBall x (r x)) hsub
  measurable := measurable_glueDensity hF
  bounded := ae_abs_glueDensity_le hF

end Seq

namespace IsCompatibleFamily

variable {ι : Type*} {W : ι → Opens (ComplexModel n)} {T : ∀ i, LocalProductCurrent n (W i) q}

/-- **Gluing.** A compatible family of positive currents on open sets `W i ≤ U` covering `U` glues
to a positive current `S` on `U` with `S|_{W i} = T i` for every `i`. -/
theorem exists_glue (hF : IsCompatibleFamily W T) (hWU : ∀ i, W i ≤ U)
    (hcov : ∀ x ∈ U, ∃ i, x ∈ W i) :
    ∃ S : LocalProductCurrent n U q, IsPositive S ∧ ∀ i, restrict (hWU i) S = T i := by
  obtain ⟨J, hJc, hJ⟩ := TopologicalSpace.isOpen_iUnion_countable (fun i => (W i : Set
    (ComplexModel n)))
    fun i => (W i).isOpen
  rcases J.eq_empty_or_nonempty with hJe | hJne
  · -- `U` is empty
    have hUe : (U : Set (ComplexModel n)) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨i, hi⟩ := hcov x hx
      have : x ∈ ⋃ i ∈ J, (W i : Set (ComplexModel n)) := hJ ▸ mem_iUnion.mpr ⟨i, hi⟩
      simp [hJe] at this
    refine ⟨0, isPositive_zero, fun i => eq_of_isEmpty ?_ _ _⟩
    exact eq_empty_of_subset (hWU i) hUe
  · obtain ⟨f, rfl⟩ := hJc.exists_eq_range hJne
    have hG := hF.comp f
    have hcov' : ∀ x ∈ U, ∃ k, x ∈ (W ∘ f) k := by
      intro x hx
      obtain ⟨i, hi⟩ := hcov x hx
      have : x ∈ ⋃ i ∈ range f, (W i : Set (ComplexModel n)) := hJ ▸ mem_iUnion.mpr ⟨i, hi⟩
      simp only [mem_iUnion, mem_range, exists_prop] at this
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := this
      exact ⟨k, hk⟩
    have hμ := isMeasureDensity_glue hG (fun k => hWU (f k)) hcov'
    set S := ofMeasureDensity U (glueMeasure hG) (glueDensity hG)
    have hres : ∀ k, restrict (hWU (f k)) S = T (f k) := fun k =>
      restrict_ofMeasureDensity hμ (hWU (f k)) (hF.isPositive (f k)) (glueMeasure_restrict hG k)
        (ae_glueDensity hG k)
    have hpos : IsPositive S := by
      apply LocalPositiveCurrentGluing.isPositive_of_local_restrict
      intro x hx
      obtain ⟨k, hk⟩ := hcov' x hx
      exact ⟨W (f k), hWU (f k), hk, by rw [hres k]; exact hF.isPositive (f k)⟩
    refine ⟨S, hpos, fun i => ?_⟩
    apply LocalBedfordTaylorCalculus.eq_of_local
    intro x hx
    obtain ⟨k, hk⟩ := hcov' x (hWU i hx)
    refine ⟨W i ⊓ W (f k), inf_le_left, ⟨hx, hk⟩, ?_⟩
    rw [restrict_restrict, hF.agree i (f k), ← hres k, restrict_restrict]

/-- **Uniqueness of the glued current**: a current on `U` is determined by its restrictions to the
members of an open cover. -/
theorem glue_unique (hWU : ∀ i, W i ≤ U) (hcov : ∀ x ∈ U, ∃ i, x ∈ W i)
    {S S' : LocalProductCurrent n U q} (hS : ∀ i, restrict (hWU i) S = T i)
    (hS' : ∀ i, restrict (hWU i) S' = T i) : S = S' := by
  apply LocalBedfordTaylorCalculus.eq_of_local
  intro x hx
  obtain ⟨i, hi⟩ := hcov x hx
  exact ⟨W i, hWU i, hi, by rw [hS i, hS' i]⟩

/-- **The sheaf property**: a compatible family of positive currents on an open cover of `U` glues
to a unique current on `U`; it is positive. -/
theorem existsUnique_glue (hF : IsCompatibleFamily W T) (hWU : ∀ i, W i ≤ U)
    (hcov : ∀ x ∈ U, ∃ i, x ∈ W i) :
    ∃! S : LocalProductCurrent n U q, ∀ i, restrict (hWU i) S = T i := by
  obtain ⟨S, -, hS⟩ := hF.exists_glue hWU hcov
  exact ⟨S, hS, fun S' hS' => glue_unique hWU hcov hS' hS⟩

end IsCompatibleFamily

end Glue

end SGPT.Currents
