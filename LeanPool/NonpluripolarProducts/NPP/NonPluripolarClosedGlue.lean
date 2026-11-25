/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Currents.GradientCutoff
public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentLocal

/-!
# Closedness of glued truncation families with psh cutoffs

Source: Xia, *Foundations of pluripotential theory*, `thm:nonpluripolar-product-closed` (proof:
"Cutoff functions", "Gradient bound", "Conclusion").

Let `(B_k, O_k)` be a truncation family on an open `U ⊆ ℂⁿ` (`IsTruncationFamily`: positive
currents `B_k` of bidimension `(q+1,q+1)` and increasing Borel sets `O_k` with
`1_{O_k} B_l = 1_{O_k} B_k` for `k ≤ l`) whose glued current `S` (`IsTruncationFamily.glue`,
characterized by `1_{O_k} S = 1_{O_k} B_k` and `S = 0` off `⋃ O_k`) has locally finite mass.  If
every `B_k` is **closed** and the family admits **psh cutoffs** (`HasPshCutoffs`: near every
compact set, locally bounded psh `0 ≤ w_k ≤ 1` vanishing off `O_k` with `w_k → 1` on `⋃ O_k`),
then `S` is closed (`IsTruncationFamily.isClosedCurrent_glue`).  This is the FPT argument written
in TN's language of currents acting on constant forms: closedness is tested against
`d(φ ℓ ∧ γ)` (`IsClosedCurrent`), the strongly positive `γ` spanning the constant forms; with
`ζ` a smooth step function (`cutProfile`: `0` on `(-∞, 1/2]`, `1` on `[3/4, ∞)`),

* `ζ(w_k) S = ζ(w_k) B_k` (`integral_mul_glueDensity_eq`, from `1_{O_k} S = 1_{O_k} B_k`);
* the closedness defect of `ζ(w_k) B_k` is bounded by
  `(t/4) ∫ w_k² A_τ dσ_{B_k} + (1/2t) ∫ φ² ζ'(w_k)² L(Q(η,η)) dσ_{B_k}`
  (`SGPT.Currents.Gradient.abs_sum_integral_le`); the first integral is bounded by
  `C σ_{B_k}(supp τ ∩ O_k) ≤ C sup_j σ_{B_j}(supp τ ∩ O_j) < ∞` (the mass condition), the second
  equals `∫ φ² ζ'(w_k)² L(Q(η,η)) dσ_S → 0` by dominated convergence;
* `ζ(w_k) S → S` by dominated convergence, so the defect of `S` is `≤ t C` for every `t > 0`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

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
open SGPT.Currents.Gradient

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

/-! ### The smooth step function -/

section Profile

/-- The smooth step `ζ(s) = smoothTransition(4s - 2)`: `0` on `(-∞, 1/2]`, `1` on `[3/4, ∞)`. -/
def cutProfile (s : ℝ) : ℝ := Real.smoothTransition (4 * s - 2)

theorem contDiff_cutProfile : ContDiff ℝ ∞ cutProfile :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem cutProfile_nonneg (s : ℝ) : 0 ≤ cutProfile s := Real.smoothTransition.nonneg _

theorem cutProfile_le_one (s : ℝ) : cutProfile s ≤ 1 := Real.smoothTransition.le_one _

theorem cutProfile_of_le {s : ℝ} (hs : s ≤ 1 / 2) : cutProfile s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutProfile_of_ge {s : ℝ} (hs : 3 / 4 ≤ s) : cutProfile s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutProfile_zero : cutProfile 0 = 0 := cutProfile_of_le (by norm_num)

theorem cutProfile_one : cutProfile 1 = 1 := cutProfile_of_ge (by norm_num)

theorem deriv_cutProfile_of_lt {s : ℝ} (hs : s < 1 / 2) : deriv cutProfile s = 0 := by
  have h : cutProfile =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hs] with r hr
    exact cutProfile_of_le (le_of_lt hr)
  rw [h.deriv_eq, deriv_const]

theorem deriv_cutProfile_of_gt {s : ℝ} (hs : 3 / 4 < s) : deriv cutProfile s = 0 := by
  have h : cutProfile =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    exact cutProfile_of_ge (le_of_lt hr)
  rw [h.deriv_eq, deriv_const]

theorem deriv_cutProfile_zero : deriv cutProfile 0 = 0 := deriv_cutProfile_of_lt (by norm_num)

end Profile

/-! ### A nonnegative test function equal to one on a compact set -/

theorem exists_testFunction_eq_one {U V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKV : K ⊆ V) :
    ∃ τ : 𝓓(U, ℝ), (∀ x, 0 ≤ τ x) ∧ (∀ x ∈ K, τ x = 1) ∧ tsupport τ ⊆ V := by
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hK V.isOpen hKV
  obtain ⟨f, h0, h1, h01⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (I := 𝓘(ℝ,
    (ComplexModel n)))
    (n := (⊤ : ℕ∞)) hWo.isClosed_compl hK.isClosed (disjoint_compl_left_iff_subset.mpr hKW)
  have hsupp : tsupport f ⊆ W := fun x hx => by
    by_contra hxW
    exact (notMem_tsupport_iff_eventuallyEq.mpr ((eventually_nhdsSet_iff_forall.mp h0) x hxW)) hx
  have hsV : tsupport f ⊆ V := hsupp.trans (subset_closure.trans hWV)
  refine ⟨⟨f, contMDiff_iff_contDiff.mp f.contMDiff,
    IsCompact.of_isClosed_subset hWc (isClosed_tsupport _) (hsupp.trans subset_closure),
    hsV.trans hVU⟩, fun x => (h01 x).1, fun x hx => ?_, hsV⟩
  exact ((eventually_nhdsSet_iff_forall.mp h1) x hx).self_of_nhds

/-! ### Transfer from the glued current to the truncations -/

section Transfer

variable {U : Opens (ComplexModel n)} {q : ℕ} {B : ℕ → LocalProductCurrent n U q} {O : ℕ → Set
    (ComplexModel n)}

namespace IsTruncationFamily

variable (hF : IsTruncationFamily B O)
include hF

/-- **`c S = c B_k` for weights supported in `O_k`**: for a test weight `c` vanishing off `O_k`,
`∫ c L^S(β) dμ_S = ∫ c L^{B_k}(β) dσ_{B_k}` (a consequence of `1_{O_k} S = 1_{O_k} B_k`). -/
theorem integral_mul_glueDensity_eq (hm : hF.HasLocallyFiniteMass) (k : ℕ) (β : formSpan n q)
    {c : (ComplexModel n) → ℝ} (hc : IsTestWeight (U := U) c) (hcO : ∀ x, x ∉ O k → c x = 0) :
    ∫ x, c x * hF.glueDensity x β ∂hF.glueMeasure =
      ∫ x, c x * densityForm (hF.isPositive k) x β ∂(hF.isPositive k).traceMeasure := by
  set ind : (ComplexModel n) → ℝ := (O k).indicator fun _ => (1 : ℝ) with hind_def
  have hind : Measurable ind := measurable_const.indicator (hF.measurableSet k)
  have hind1 : ∀ x, |ind x| ≤ 1 := fun x => by
    by_cases hx : x ∈ O k <;> simp [hind_def, hx]
  have hf : IsLocalDensity (U := U) hF.glueMeasure (fun x => ind x * hF.clipDensity β x) := by
    have h := hF.isLocalDensity_clipDensity hm β
    refine ⟨h.compl, h.lt_top, hind.mul h.measurable, fun K hK hKU => ?_⟩
    obtain ⟨M, hM⟩ := h.bounded K hK hKU
    exact ⟨M, fun x hx => by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hind1 x)).trans (hM x hx)⟩
  have hg : IsLocalDensity (U := U) (hF.isPositive k).traceMeasure
      (fun x => ind x * densityForm (hF.isPositive k) x β) := by
    obtain ⟨C, -, hC⟩ := exists_abs_densityForm_le (hF.isPositive k) β
    exact ⟨(hF.isPositive k).traceMeasure_compl, fun K hK hKU =>
      (hF.isPositive k).traceMeasure_lt_top hK hKU,
      hind.mul (measurable_densityForm _ β), fun K _ _ => ⟨C, fun x _ => by
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hind1 x)).trans (hC x)⟩⟩
  have key := integral_eq_of_forall_testFunction hf hg (fun ψ => by
    have h1 := hF.truncAt_apply hm k β ψ
    have h2 := mulBorel_apply (hF.isPositive k) hind (isLocallyBoundedOn_indicator_one _) β ψ
    calc ∫ x, ind x * hF.clipDensity β x * ψ x ∂hF.glueMeasure =
          ∫ x, ψ x * (ind x * hF.glueDensity x β) ∂hF.glueMeasure := by
          refine integral_congr_ae ?_
          filter_upwards [hF.clipDensity_ae β] with x hx
          rw [hx]
          ring
      _ = truncAt B O k β ψ := h1.symm
      _ = ∫ x, ψ x * (ind x * (hF.isPositive k).density β x)
            ∂(hF.isPositive k).traceMeasure := h2
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [densityForm_ae (hF.isPositive k) β] with x hx
          rw [hx]
          ring) hc
  have e1 : ∫ x, c x * hF.glueDensity x β ∂hF.glueMeasure =
      ∫ x, ind x * hF.clipDensity β x * c x ∂hF.glueMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [hF.clipDensity_ae β] with x hx
    rw [hx]
    by_cases hxO : x ∈ O k
    · simp only [hind_def, Set.indicator_of_mem hxO]
      ring
    · rw [hcO x hxO]
      ring
  have e2 : ∫ x, c x * densityForm (hF.isPositive k) x β ∂(hF.isPositive k).traceMeasure =
      ∫ x, ind x * densityForm (hF.isPositive k) x β * c x ∂(hF.isPositive k).traceMeasure := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hxO : x ∈ O k
    · simp only [hind_def, Set.indicator_of_mem hxO]
      ring
    · simp only
      rw [hcO x hxO]
      ring
  rw [e1, e2, key]

end IsTruncationFamily

end Transfer

/-! ### Psh cutoffs and the closedness theorem -/

section Closed

variable {U : Opens (ComplexModel n)} {q : ℕ}

variable (U) in
/-- **Psh cutoffs** for an increasing sequence of sets `O_k` (FPT, proof of
`thm:nonpluripolar-product-closed`, "Cutoff functions"): near every compact `K ⊆ U` there are an
open `V` with `K ⊆ V ⊆ U` and measurable functions `w_k`, locally bounded psh on `V`, with
`0 ≤ w_k ≤ 1` on `V`, `w_k = 0` on `V \ O_k`, and `w_k → 1` at every point of `V ∩ ⋃ O_k`. -/
def HasPshCutoffs (O : ℕ → Set (ComplexModel n)) : Prop :=
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → ∃ V : Opens (ComplexModel n),
    V ≤ U ∧ K ⊆ V ∧ ∃ w : ℕ → (ComplexModel n) → ℝ,
    (∀ k, Measurable (w k)) ∧ (∀ k, IsLocallyBoundedPshOn V (w k)) ∧
    (∀ k, ∀ x ∈ V, 0 ≤ w k x ∧ w k x ≤ 1) ∧ (∀ k, ∀ x ∈ V, x ∉ O k → w k x = 0) ∧
    ∀ x ∈ V, (∃ k, x ∈ O k) → Tendsto (fun k => w k x) atTop (𝓝 1)

private theorem exists_hessWeight_bound (γ : formSpan n q) (τ : 𝓓(U, ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {T : LocalProductCurrent n U (q + 1)} (hT : IsPositive T)
      (x : ComplexModel n), (∀ a b, |densityForm hT x (coeffWedge γ a b)| ≤
        orderUnitConst (coeffWedge γ a b)) → hessWeight hT γ τ x ≤ D := by
  choose Mh hMh using fun ab : Fin (n * 2) × Fin (n * 2) =>
    (dTest (realBasis n ab.2) (dTest (realBasis n ab.1)
      τ)).continuous.bounded_above_of_compact_support
      (dTest (realBasis n ab.2) (dTest (realBasis n ab.1) τ)).hasCompactSupport
  set D : ℝ := ∑ a, ∑ b, Mh (a, b) * orderUnitConst (coeffWedge γ a b)
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    mul_nonneg ((norm_nonneg _).trans (hMh (a, b) 0)) (orderUnitConst_nonneg _)
  refine ⟨D, hD0, fun hT x hx => ?_⟩
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using hMh (a, b) x) (hx a b)
    (abs_nonneg _) ((norm_nonneg _).trans (hMh (a, b) 0))

namespace IsTruncationFamily

variable {B : ℕ → LocalProductCurrent n U (q + 1)} {O : ℕ → Set (ComplexModel n)}
  (hF : IsTruncationFamily B O)
include hF

/-- **The closedness defect of the glued current vanishes** on `d(φ ℓ ∧ γ)` for strongly
positive `γ` (FPT `thm:nonpluripolar-product-closed`, `dS_γ = 0`). -/
theorem sum_glue_testWedge_dTest_eq_zero (hm : hF.HasLocallyFiniteMass)
    (hBc : ∀ k, IsClosedCurrent (B k)) (hcut : HasPshCutoffs U O) {γ : formSpan n q}
    (hγ : γ ∈ posCone n q) (ℓ : (ComplexModel n) →L[ℝ] ℝ) (φ : 𝓓(U, ℝ)) :
    ∑ a, hF.glue (testWedge γ ℓ a) (dTest (realBasis n a) φ) = 0 := by
  set K := tsupport (φ : (ComplexModel n) → ℝ) with hKdef
  have hK : IsCompact K := φ.hasCompactSupport
  obtain ⟨V, hVU, hKV, w, hwm, hwpsh, hw01, hwO, hwlim⟩ := hcut K hK φ.tsupport_subset
  obtain ⟨τ, hτ0, hτ1, hτV⟩ := exists_testFunction_eq_one hVU hK hKV
  set μ := hF.glueMeasure
  set η := dualCoeff ℓ
  have hζc : Continuous cutProfile := contDiff_cutProfile.continuous
  have hζ'c : Continuous (deriv cutProfile) := contDiff_cutProfile.continuous_deriv (by simp)
  have hdφK : ∀ a, ∀ x, x ∉ K → dTest (realBasis n a) φ x = 0 := fun a x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_dTest_subset _ _ h)
  have hφK : ∀ x, x ∉ K → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hI : ∑ a, hF.glue (testWedge γ ℓ a) (dTest (realBasis n a) φ) =
      ∑ a, ∫ x, dTest (realBasis n a) φ x * hF.glueDensity x (testWedge γ ℓ a) ∂μ :=
    Finset.sum_congr rfl fun a _ => hF.glue_apply hm _ _
  set Ilim := ∑ a, ∫ x, dTest (realBasis n a) φ x * hF.glueDensity x (testWedge γ ℓ a) ∂μ
  -- (A) the cut-off defects converge to the defect of `S`
  set I : ℕ → ℝ := fun k => ∑ a, ∫ x, dTest (realBasis n a) φ x *
    (cutProfile (w k x) * hF.glueDensity x (testWedge γ ℓ a)) ∂μ with hIdef
  have hA : Tendsto I atTop (𝓝 Ilim) := by
    refine tendsto_finsetSum _ fun a _ => ?_
    set ψ := dTest (realBasis n a) φ
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖ψ x‖ * orderUnitConst (testWedge γ ℓ a)) (fun k => ?_)
      ((hF.integrable_test hm ψ).norm.mul_const _) (fun k => ?_) ?_
    · exact (ψ.continuous.measurable.mul ((hζc.measurable.comp (hwm k)).mul
        (hF.measurable_glueDensity _))).aestronglyMeasurable
    · filter_upwards [hF.ae_abs_glueDensity_le (testWedge γ ℓ a)] with x hx
      rw [norm_mul, norm_mul, Real.norm_eq_abs (hF.glueDensity x _)]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖cutProfile (w k x)‖ * |hF.glueDensity x (testWedge γ ℓ a)| ≤
            1 * orderUnitConst (testWedge γ ℓ a) := by
            refine mul_le_mul ?_ hx (abs_nonneg _) zero_le_one
            rw [Real.norm_eq_abs, abs_of_nonneg (cutProfile_nonneg _)]
            exact cutProfile_le_one _
        _ = _ := one_mul _
    · filter_upwards [hF.ae_glueMeasure_mem] with x hx
      by_cases hxK : x ∈ K
      · have h1 := (hζc.tendsto 1).comp (hwlim x (hKV hxK) hx)
        rw [cutProfile_one] at h1
        have h2 := tendsto_const_nhds (x := ψ x) |>.mul
          (h1.mul (tendsto_const_nhds (x := hF.glueDensity x (testWedge γ ℓ a))))
        simpa only [one_mul, Function.comp_def] using h2
      · simp only [ψ, hdφK a x hxK, zero_mul]
        exact tendsto_const_nhds
  -- (B) the cut-off defects through the truncations `B_k`
  have hB : ∀ k, I k = ∑ a, ∫ x, dTest (realBasis n a) φ x * (cutProfile (w k x) *
      densityForm (hF.isPositive k) x (testWedge γ ℓ a)) ∂(hF.isPositive k).traceMeasure := by
    intro k
    refine Finset.sum_congr rfl fun a _ => ?_
    have hc : IsTestWeight (U := U) (fun x => dTest (realBasis n a) φ x * cutProfile (w k x)) :=
      isTestWeight_mul _ (hζc.measurable.comp (hwm k)) fun _ _ _ => ⟨1, fun x _ => by
        rw [abs_of_nonneg (cutProfile_nonneg _)]
        exact cutProfile_le_one _⟩
    have h := hF.integral_mul_glueDensity_eq hm k (testWedge γ ℓ a) hc (fun x hx => by
      by_cases hxK : x ∈ K
      · simp only [hwO k x (hKV hxK) hx, cutProfile_zero, mul_zero]
      · simp only [hdφK a x hxK, zero_mul])
    simp only [mul_assoc] at h
    exact h
  -- (C) the cutoff estimate for each `B_k`
  have hC : ∀ k, ∀ t : ℝ, 0 < t → |I k| ≤
      t / 4 * ∫ x, w k x ^ 2 * hessWeight (hF.isPositive k) γ τ x ∂(hF.isPositive k).traceMeasure +
        1 / (2 * t) * ∫ x, φ x ^ 2 * deriv cutProfile (w k x) ^ 2 *
          densityForm (hF.isPositive k) x (quadForm q γ η η) ∂(hF.isPositive k).traceMeasure := by
    intro k t ht
    rw [hB k]
    exact abs_sum_integral_le (hF.isPositive k) (hBc k) hγ ℓ φ τ hτ0 (fun x hx => hτ1 x hx)
      contDiff_cutProfile hτV (hwpsh k) (fun x hx => (hw01 k x hx).1) ht
  -- (D) the gradient terms are bounded uniformly in `k` (the mass condition)
  set K₁ := tsupport (τ : (ComplexModel n) → ℝ) with hK₁def
  have hK₁ : IsCompact K₁ := τ.hasCompactSupport
  have hK₁U : K₁ ⊆ U := τ.tsupport_subset
  obtain ⟨D, hD0, hD⟩ := exists_hessWeight_bound γ τ
  have hmass := (hF.hasLocallyFiniteMass_iff.mp hm) K₁ hK₁ hK₁U
  set C₁ : ℝ := (⨆ k, (hF.isPositive k).traceMeasure (K₁ ∩ O k)).toReal * D with hC₁def
  have hC₁0 : 0 ≤ C₁ := mul_nonneg ENNReal.toReal_nonneg hD0
  have hE : ∀ k, ∫ x, w k x ^ 2 * hessWeight (hF.isPositive k) γ τ x
      ∂(hF.isPositive k).traceMeasure ≤ C₁ := by
    intro k
    set σk := (hF.isPositive k).traceMeasure
    have hs : MeasurableSet (K₁ ∩ O k) := (isClosed_tsupport _).measurableSet.inter
      (hF.measurableSet k)
    have hfin : σk (K₁ ∩ O k) < ⊤ :=
      (measure_mono inter_subset_left).trans_lt ((hF.isPositive k).traceMeasure_lt_top hK₁ hK₁U)
    have hall : ∀ᵐ x ∂σk, ∀ a b, |densityForm (hF.isPositive k) x (coeffWedge γ a b)| ≤
        orderUnitConst (coeffWedge γ a b) :=
      ae_all_iff.mpr fun a => ae_all_iff.mpr fun b => ae_abs_densityForm_le _ _
    have hpt : ∀ᵐ x ∂σk, w k x ^ 2 * hessWeight (hF.isPositive k) γ τ x ≤
        (K₁ ∩ O k).indicator (fun _ => D) x := by
      filter_upwards [hall] with x hx
      by_cases hx1 : x ∈ K₁
      · by_cases hx2 : x ∈ O k
        · rw [Set.indicator_of_mem (Set.mem_inter hx1 hx2)]
          have hw1 : w k x ^ 2 ≤ 1 := by
            have := hw01 k x (hτV hx1)
            nlinarith [this.1, this.2]
          have hH := hD (hF.isPositive k) x hx
          calc w k x ^ 2 * hessWeight (hF.isPositive k) γ τ x ≤ 1 * D :=
                mul_le_mul hw1 hH (hessWeight_nonneg _ _ _ _) zero_le_one
            _ = D := one_mul _
        · have hnot : x ∉ K₁ ∩ O k := fun h => hx2 h.2
          rw [hwO k x (hτV hx1) hx2, Set.indicator_of_notMem hnot]
          simp
      · rw [hessWeight_eq_zero _ γ τ hx1, mul_zero]
        exact Set.indicator_nonneg (fun _ _ => hD0) x
    calc ∫ x, w k x ^ 2 * hessWeight (hF.isPositive k) γ τ x ∂σk ≤
          ∫ x, (K₁ ∩ O k).indicator (fun _ => D) x ∂σk :=
          integral_mono_of_nonneg (Eventually.of_forall fun x =>
            mul_nonneg (sq_nonneg _) (hessWeight_nonneg _ _ _ _))
            ((integrable_indicator_iff hs).mpr (integrableOn_const hfin.ne)) hpt
      _ = (σk (K₁ ∩ O k)).toReal * D := by
          rw [integral_indicator_const _ hs, smul_eq_mul, Measure.real]
      _ ≤ C₁ := by
          refine mul_le_mul_of_nonneg_right ?_ hD0
          exact ENNReal.toReal_mono hmass.ne
            (le_iSup (fun k => (hF.isPositive k).traceMeasure (K₁ ∩ O k)) k)
  -- ((ComplexModel n)) the cutoff terms tend to zero
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hCφ' : ∀ x, |φ x| ≤ Cφ := fun x => by simpa [Real.norm_eq_abs] using hCφ x
  have hCφ0 : 0 ≤ Cφ := (abs_nonneg _).trans (hCφ' 0)
  obtain ⟨Mζ', hMζ'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hζ'c.continuousOn
  have hcK : ∀ k, ∀ x ∈ K, |deriv cutProfile (w k x)| ≤ Mζ' := fun k x hx => by
    simpa [Real.norm_eq_abs] using hMζ' _ ⟨(hw01 k x (hKV hx)).1, (hw01 k x (hKV hx)).2⟩
  have hM0 : 0 ≤ Mζ' := (abs_nonneg _).trans (hMζ' 0 ⟨le_rfl, zero_le_one⟩)
  set Y : ℕ → ℝ := fun k => ∫ x, φ x ^ 2 * deriv cutProfile (w k x) ^ 2 *
    hF.glueDensity x (quadForm q γ η η) ∂μ with hYdef
  have hYeq : ∀ k, ∫ x, φ x ^ 2 * deriv cutProfile (w k x) ^ 2 *
      densityForm (hF.isPositive k) x (quadForm q γ η η) ∂(hF.isPositive k).traceMeasure =
      Y k := by
    intro k
    have hc : IsTestWeight (U := U) (fun x => φ x ^ 2 * deriv cutProfile (w k x) ^ 2) := by
      refine ⟨(φ.continuous.measurable.pow_const 2).mul
        ((hζ'c.measurable.comp (hwm k)).pow_const 2), ⟨Cφ ^ 2 * Mζ' ^ 2, fun x => ?_⟩,
        K, hK, φ.tsupport_subset, fun x hx => by simp [hφK x hx]⟩
      by_cases hx : x ∈ K
      · rw [abs_mul, abs_pow, abs_pow]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hCφ' x) 2)
          (pow_le_pow_left₀ (abs_nonneg _) (hcK k x hx) 2) (by positivity) (by positivity)
      · simp only [hφK x hx]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, abs_zero]
        positivity
    exact (hF.integral_mul_glueDensity_eq hm k _ hc (fun x hx => by
      by_cases hxK : x ∈ K
      · simp [hwO k x (hKV hxK) hx, deriv_cutProfile_zero]
      · simp [hφK x hxK])).symm
  have hY : Tendsto Y atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun k x => φ x ^ 2 * deriv cutProfile (w k x) ^ 2 *
        hF.glueDensity x (quadForm q γ η η)) (f := fun _ => (0 : ℝ))
      (fun x => ‖φ x‖ * (Cφ * Mζ' ^ 2 * orderUnitConst (quadForm q γ η η))) (fun k => ?_)
      ((hF.integrable_test hm φ).norm.mul_const _) (fun k => ?_) ?_
    · simpa only [integral_zero] using h
    · exact ((φ.continuous.measurable.pow_const 2).mul ((hζ'c.measurable.comp (hwm k)).pow_const
        2)).mul (hF.measurable_glueDensity _) |>.aestronglyMeasurable
    · filter_upwards [hF.ae_abs_glueDensity_le (quadForm q γ η η)] with x hx
      by_cases hxK : x ∈ K
      · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
        have h1 := hCφ' x
        have h2 := hcK k x hxK
        have h3 : 0 ≤ orderUnitConst (quadForm q γ η η) := orderUnitConst_nonneg _
        calc |φ x| ^ 2 * |deriv cutProfile (w k x)| ^ 2 * |hF.glueDensity x (quadForm q γ η η)|
            ≤ |φ x| * Cφ * Mζ' ^ 2 * orderUnitConst (quadForm q γ η η) := by
              rw [sq (|φ x|)]
              gcongr
          _ = |φ x| * (Cφ * Mζ' ^ 2 * orderUnitConst (quadForm q γ η η)) := by ring
      · simp only [hφK x hxK]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, norm_zero]
        exact le_rfl
    · filter_upwards [hF.ae_glueMeasure_mem] with x hx
      by_cases hxK : x ∈ K
      · have hev : ∀ᶠ k in atTop, 3 / 4 < w k x :=
          (hwlim x (hKV hxK) hx).eventually_const_lt (by norm_num)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with k hk
        rw [deriv_cutProfile_of_gt hk]
        simp
      · simp only [hφK x hxK]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact tendsto_const_nhds
  -- (F) conclusion: the defect of `S` is at most `t C₁ / 4` for every `t > 0`
  have hkey : ∀ t : ℝ, 0 < t → |Ilim| ≤ t / 4 * C₁ := by
    intro t ht
    have hle : ∀ k, |I k| ≤ t / 4 * C₁ + 1 / (2 * t) * Y k := fun k => by
      have h := hC k t ht
      rw [hYeq k] at h
      have h4 : 0 ≤ t / 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (hE k) h4]
    have h := le_of_tendsto_of_tendsto' ((continuous_abs.tendsto _).comp hA)
      (tendsto_const_nhds.add (hY.const_mul _)) hle
    simpa only [mul_zero, add_zero] using h
  have hzero : Ilim = 0 := by
    by_contra hne
    have hpos : 0 < |Ilim| := abs_pos.mpr hne
    have h := hkey (2 * |Ilim| / (C₁ + 1)) (by positivity)
    have hlt : 2 * |Ilim| / (C₁ + 1) / 4 * C₁ < |Ilim| := by
      rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [hI]
  exact hzero

/-- **The glued current of a closed truncation family with psh cutoffs is closed** (FPT
`thm:nonpluripolar-product-closed`): `IsClosedCurrent` in TN's sense, i.e. `⟨S, d(φ ℓ ∧ γ)⟩ = 0`
for every test function `φ`, real linear form `ℓ` and constant `(q,q)`-form `γ`.  The strongly
positive `γ` span the constant forms (`formSpan` is by definition the span of the strongly
positive cone), so it suffices to treat them (`sum_glue_testWedge_dTest_eq_zero`). -/
theorem isClosedCurrent_glue (hm : hF.HasLocallyFiniteMass) (hBc : ∀ k, IsClosedCurrent (B k))
    (hcut : HasPshCutoffs U O) : IsClosedCurrent hF.glue := by
  intro ℓ γ
  ext φ
  simp only [_root_.sum_apply, dDist_apply, _root_.zero_apply, Finset.sum_neg_distrib,
    neg_eq_zero]
  change ∑ a, hF.glue (testWedge γ ℓ a) (dTest (realBasis n a) φ) = 0
  let Φ : formSpan n q →ₗ[ℝ] ℝ :=
    { toFun := fun γ => ∑ a, hF.glue (testWedge γ ℓ a) (dTest (realBasis n a) φ)
      map_add' := fun γ γ' => by
        simp only [testWedge_add, map_add, _root_.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c γ => by
        simp only [testWedge_smul, map_smul, _root_.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum] }
  have hspan : Submodule.span ℝ (posCone n q) = ⊤ := Submodule.span_span_coe_preimage
  have h0 : Φ = 0 := LinearMap.ext_on hspan fun γ hγ =>
    (hF.sum_glue_testWedge_dTest_eq_zero hm hBc hcut hγ ℓ φ).trans (LinearMap.zero_apply γ).symm
  exact LinearMap.congr_fun h0 γ

end IsTruncationFamily

end Closed

end SGPT.NPP.NonPluripolarCurrent
