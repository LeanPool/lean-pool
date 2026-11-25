/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifinePshTopology
public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentNonCharging
public import LeanPool.NonpluripolarProducts.PSH.DomainPlurifine
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BorelPlurifineCanonicalMixedLocality

/-!
# Plurifine locality of the non-pluripolar product of arbitrary degree

Source: `chapter_npp.tex`, `prop:npp1` (1), `eq:ppp1`; Xia, *Foundations of pluripotential
theory*, `thm:bt-plurifine-locality` (for bounded products) and
`prop:nonpluripolar-local-calculus` ("Symmetry and locality").

The plurifine topology of an open `U ⊆ ℂⁿ` is the verified `def:pftopologydomain`
(`SGPT.PSH.domainPlurifineTopology`, the coarsest topology on `U` making all real psh functions
continuous).

* `mulBorel_btProduct_eq_of_eqOn_plurifineOpen` — **plurifine locality of Bedford–Taylor products
  of every degree**: if `vᵢ = wᵢ` on a Borel plurifine open `F ⊆ U`, then
  `1_F ⋀ dd^c vᵢ = 1_F ⋀ dd^c wᵢ` (reduction to top degree with quadratic potentials and the
  reused top-degree plurifine locality `canonicalMixed_restrict_eq_on_borel_plurifine_open`);
* `mulBorel_nonPluripolarProduct_eq_of_eqOn_plurifineOpen` — **`eq:ppp1` for Borel plurifine
  open sets**: if `φⱼ = ψⱼ` on a Borel plurifine open `O ⊆ U` and both products are well defined,
  then `1_O ⟨⋀ dd^c φⱼ⟩ = 1_O ⟨⋀ dd^c ψⱼ⟩`.

The local statements use the convention at `NonPluripolarCurrent.nonPluripolarProduct`.
A factor may be identically `-∞` on an open component, where the product vanishes.
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
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

/-- **Plurifine locality of Bedford–Taylor products of every degree** (FPT
`thm:bt-plurifine-locality`, for Borel plurifine open sets). -/
theorem mulBorel_btProduct_eq_of_eqOn_plurifineOpen {p q : ℕ} (hqp : q + p = n)
    {U : Opens (ComplexModel n)} {v w : Fin p → (ComplexModel n) → ℝ} (hv : ∀ i,
      IsLocallyBoundedPshOn U (v i))
    (hw : ∀ i, IsLocallyBoundedPshOn U (w i)) {F : Set (ComplexModel n)} (hFU : F ⊆ U)
    (hFm : MeasurableSet F)
    (hFine : IsOpen[SGPT.PSH.domainPlurifineTopology U] (Subtype.val ⁻¹' F))
    (heq : ∀ i, EqOn (v i) (w i) F) :
    mulBorel (btProduct p q v (oneCurrentOf (U := U) hqp)) (F.indicator fun _ => (1 : ℝ)) =
      mulBorel (btProduct p q w (oneCurrentOf (U := U) hqp)) (F.indicator fun _ => (1 : ℝ)) := by
  subst hqp
  have hgm : Measurable (F.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hFm
  have hgb : IsLocallyBoundedOn (F.indicator fun _ => (1 : ℝ)) U :=
    isLocallyBoundedOn_indicator_one F
  refine BedfordTaylorTopDegree.eq_of_wedgeProd _ _ fun β hβ hP φ => ?_
  have hℓs : ∀ i, ContDiffOn ℝ ∞ (BedfordTaylorTopDegree.quadPot (β i)) U :=
    fun i => (BedfordTaylorTopDegree.contDiff_quadPot _).contDiffOn
  have hℓ : ∀ i, IsLocallyBoundedPshOn U (BedfordTaylorTopDegree.quadPot (β i)) :=
    fun i => BedfordTaylorTopDegree.isLocallyBoundedPshOn_quadPot (hβ i) U
  have hddc : ∀ i, ∀ x ∈ U, smoothDDC (BedfordTaylorTopDegree.quadPot (β i)) x = β i :=
    fun i x _ => BedfordTaylorTopDegree.smoothDDC_quadPot (hβ i).1 x
  have hav := BedfordTaylorTopDegree.isLocallyBoundedPshOn_append hℓ hv
  have haw := BedfordTaylorTopDegree.isLocallyBoundedPshOn_append hℓ hw
  have heq' : ∀ i, EqOn (Fin.append (fun i => BedfordTaylorTopDegree.quadPot (β i)) v i)
      (Fin.append (fun i => BedfordTaylorTopDegree.quadPot (β i)) w i) F := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro z _
      simp only [Fin.append_left]
    · intro z hz
      simp only [Fin.append_right]
      exact heq j hz
  have hloc : (LocalBedfordTaylorSmoothTraceMeasure.recursiveMixedTraceMeasure U _ hav).restrict F
    =
      (LocalBedfordTaylorSmoothTraceMeasure.recursiveMixedTraceMeasure U _ haw).restrict F := by
    rw [← canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hav,
      ← canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure haw]
    exact BorelPlurifineCanonicalMixedLocality.canonicalMixed_restrict_eq_on_borel_plurifine_open
      hav haw hFU hFm hFine heq'
  rw [BedfordTaylorTopDegree.mulBorel_btProduct_apply_wedgeProd_of_ddc p q v hv β _ hℓs hℓ hddc hP
      hgm hgb φ,
    BedfordTaylorTopDegree.mulBorel_btProduct_apply_wedgeProd_of_ddc p q w hw β _ hℓs hℓ hddc hP
      hgm hgb φ]
  have hind : ∀ x, φ x * F.indicator (fun _ => (1 : ℝ)) x = F.indicator (fun y => φ y) x := by
    intro x
    by_cases hx : x ∈ F <;> simp [hx]
  simp only [hind]
  rw [integral_indicator hFm, integral_indicator hFm, hloc]

section General

variable {U : Opens (ComplexModel n)} {q : ℕ}

/-- `1_B (1_A T) = 1_{A ∩ B} T`. -/
theorem mulBorel_indicator_indicator {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {A B : Set (ComplexModel n)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    mulBorel (mulBorel T (A.indicator fun _ => (1 : ℝ))) (B.indicator fun _ => (1 : ℝ)) =
      mulBorel T ((A ∩ B).indicator fun _ => (1 : ℝ)) := by
  rw [mulBorel_mulBorel hT (measurable_const.indicator hA) (isLocallyBoundedOn_indicator_one _)
    (fun x => by by_cases hx : x ∈ A <;> simp [hx]) (measurable_const.indicator hB)
    (isLocallyBoundedOn_indicator_one _)]
  congr 1
  funext x
  by_cases hx : x ∈ A <;> by_cases hy : x ∈ B <;> simp [hx, hy]

end General

section Product

variable {p q : ℕ} (hqp : q + p = n) {U : Opens (ComplexModel n)}

/-- The trace measure of the non-pluripolar product is carried by `⋃ₖ O_k`. -/
theorem ae_mem_iUnion_strictLocus {φ : Fin p → (ComplexModel n) → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (hW : IsWellDefinedOn hqp U φ) :
    ∀ᵐ x ∂(isPositive_nonPluripolarProduct hqp hφ hW).traceMeasure,
      ∃ k, x ∈ BedfordTaylorTopDegree.strictLocus U φ k := by
  have hm := (isWellDefinedOn_iff hqp hφ).mp hW
  rw [IsPositive.traceMeasure_congr _ ((isTruncationFamily hqp hφ).isPositive_glue hm)
    (nonPluripolarProduct_eq hqp hφ), (isTruncationFamily hqp hφ).traceMeasure_glue hm]
  exact (isTruncationFamily hqp hφ).ae_glueMeasure_mem

/-- The strict loci `O_k` are plurifine open (`def:pftopologydomain`). -/
theorem isOpen_plurifine_strictLocus {φ : Fin p → (ComplexModel n) → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (k : ℕ) :
    IsOpen[SGPT.PSH.domainPlurifineTopology U]
      (Subtype.val ⁻¹' BedfordTaylorTopDegree.strictLocus U φ k) := by
  have e : (Subtype.val ⁻¹' BedfordTaylorTopDegree.strictLocus U φ k : Set U) =
      ⋂ i, {z : U | (((-(k : ℝ)) : ℝ) : EReal) < φ i z.val} := by
    ext z
    simp [BedfordTaylorTopDegree.strictLocus]
  rw [e]
  exact @isOpen_iInter_of_finite _ _ (SGPT.PSH.domainPlurifineTopology U) _ _
    fun i => PlurifinePshTopology.isOpen_psh_superlevel (hφ i) _

/-- `1_{O_k ∩ O} ⟨⋯⟩ → 1_O ⟨⋯⟩` weakly. -/
theorem tendsto_mulBorel_strictLocus_inter {φ : Fin p → (ComplexModel n) → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (hW : IsWellDefinedOn hqp U φ) {O : Set (ComplexModel
      n)}
    (hOm : MeasurableSet O) (γ : formSpan n q) (χ : 𝓓(U, ℝ)) :
    Tendsto (fun k => mulBorel (nonPluripolarProduct hqp U φ)
        ((BedfordTaylorTopDegree.strictLocus U φ k ∩ O).indicator fun _ => (1 : ℝ)) γ χ) atTop
      (𝓝 (mulBorel (nonPluripolarProduct hqp U φ) (O.indicator fun _ => (1 : ℝ)) γ χ)) := by
  have hS := isPositive_nonPluripolarProduct hqp hφ hW
  have hOk := BedfordTaylorTopDegree.measurableSet_strictLocus hφ
  apply tendsto_mulBorel_indicator_one hS (fun k => (hOk k).inter hOm) hOm _ γ χ
  filter_upwards [ae_mem_iUnion_strictLocus hqp hφ hW] with x hx
  obtain ⟨k₀, hk₀⟩ := hx
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop k₀] with k hk
  have hxk := BedfordTaylorTopDegree.strictLocus_mono U φ hk hk₀
  by_cases hxO : x ∈ O
  · rw [Set.indicator_of_mem hxO, Set.indicator_of_mem
      (show x ∈ BedfordTaylorTopDegree.strictLocus U φ k ∩ O from ⟨hxk, hxO⟩)]
  · rw [Set.indicator_of_notMem hxO, Set.indicator_of_notMem
      (fun h : x ∈ BedfordTaylorTopDegree.strictLocus U φ k ∩ O => hxO h.2)]

/-- **Plurifine locality of the non-pluripolar product** (`prop:npp1` (1), `eq:ppp1`, for Borel
plurifine open sets): if `φⱼ = ψⱼ` on a Borel plurifine open `O ⊆ U` and both products are well
defined, then `1_O ⟨⋀ⱼ dd^c φⱼ⟩ = 1_O ⟨⋀ⱼ dd^c ψⱼ⟩`. -/
theorem mulBorel_nonPluripolarProduct_eq_of_eqOn_plurifineOpen {φ ψ : Fin p → (ComplexModel n)
    → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (hψ : ∀ i, PlurisubharmonicOn (ψ i) U)
    (hWφ : IsWellDefinedOn hqp U φ) (hWψ : IsWellDefinedOn hqp U ψ) {O : Set (ComplexModel n)}
    (hOU : O ⊆ U) (hOm : MeasurableSet O)
    (hOfine : IsOpen[SGPT.PSH.domainPlurifineTopology U] (Subtype.val ⁻¹' O))
    (heq : ∀ i, EqOn (φ i) (ψ i) O) :
    mulBorel (nonPluripolarProduct hqp U φ) (O.indicator fun _ => (1 : ℝ)) =
      mulBorel (nonPluripolarProduct hqp U ψ) (O.indicator fun _ => (1 : ℝ)) := by
  have hS := isPositive_nonPluripolarProduct hqp hφ hWφ
  have hS' := isPositive_nonPluripolarProduct hqp hψ hWψ
  have hstep : ∀ k, mulBorel (nonPluripolarProduct hqp U φ)
      ((BedfordTaylorTopDegree.strictLocus U φ k ∩ O).indicator fun _ => (1 : ℝ)) =
        mulBorel (nonPluripolarProduct hqp U ψ)
          ((BedfordTaylorTopDegree.strictLocus U ψ k ∩ O).indicator fun _ => (1 : ℝ)) := by
    intro k
    have hOk := BedfordTaylorTopDegree.measurableSet_strictLocus hφ k
    have hOk' := BedfordTaylorTopDegree.measurableSet_strictLocus hψ k
    have hB := (isPositive_truncatedBT hqp hφ k).1
    have hB' := (isPositive_truncatedBT hqp hψ k).1
    have hset : O ∩ BedfordTaylorTopDegree.strictLocus U φ k =
        O ∩ BedfordTaylorTopDegree.strictLocus U ψ k := by
      ext x
      constructor
      · rintro ⟨hxO, hxU, h⟩
        exact ⟨hxO, hxU, fun i => (heq i hxO) ▸ h i⟩
      · rintro ⟨hxO, hxU, h⟩
        exact ⟨hxO, hxU, fun i => (heq i hxO).symm ▸ h i⟩
    have hBloc : mulBorel (truncatedBT hqp U φ k) (O.indicator fun _ => (1 : ℝ)) =
        mulBorel (truncatedBT hqp U ψ k) (O.indicator fun _ => (1 : ℝ)) :=
      mulBorel_btProduct_eq_of_eqOn_plurifineOpen hqp
        (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k)
        (fun i => truncationReal_isLocallyBoundedPshOn (hψ i) k) hOU hOm hOfine
        fun i x hx => by simp only [truncationReal, truncation, heq i hx]
    calc mulBorel (nonPluripolarProduct hqp U φ)
          ((BedfordTaylorTopDegree.strictLocus U φ k ∩ O).indicator fun _ => (1 : ℝ)) =
        mulBorel (mulBorel (nonPluripolarProduct hqp U φ)
          ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)))
          (O.indicator fun _ => (1 : ℝ)) := (mulBorel_indicator_indicator hS hOk hOm).symm
      _ = mulBorel (mulBorel (truncatedBT hqp U φ k)
          ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)))
          (O.indicator fun _ => (1 : ℝ)) := by
          rw [mulBorel_nonPluripolarProduct_strictLocus hqp hφ hWφ k]
          rfl
      _ = mulBorel (truncatedBT hqp U φ k)
          ((O ∩ BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) := by
          rw [mulBorel_indicator_indicator hB hOk hOm, inter_comm]
      _ = mulBorel (mulBorel (truncatedBT hqp U φ k) (O.indicator fun _ => (1 : ℝ)))
          ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) :=
          (mulBorel_indicator_indicator hB hOm hOk).symm
      _ = mulBorel (mulBorel (truncatedBT hqp U ψ k) (O.indicator fun _ => (1 : ℝ)))
          ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) := by
          rw [hBloc]
      _ = mulBorel (truncatedBT hqp U ψ k)
          ((BedfordTaylorTopDegree.strictLocus U ψ k ∩ O).indicator fun _ => (1 : ℝ)) := by
          rw [mulBorel_indicator_indicator hB' hOm hOk, hset, inter_comm]
      _ = mulBorel (mulBorel (truncatedBT hqp U ψ k)
          ((BedfordTaylorTopDegree.strictLocus U ψ k).indicator fun _ => (1 : ℝ)))
          (O.indicator fun _ => (1 : ℝ)) := (mulBorel_indicator_indicator hB' hOk' hOm).symm
      _ = mulBorel (mulBorel (nonPluripolarProduct hqp U ψ)
          ((BedfordTaylorTopDegree.strictLocus U ψ k).indicator fun _ => (1 : ℝ)))
          (O.indicator fun _ => (1 : ℝ)) := by
          rw [mulBorel_nonPluripolarProduct_strictLocus hqp hψ hWψ k]
          rfl
      _ = mulBorel (nonPluripolarProduct hqp U ψ)
          ((BedfordTaylorTopDegree.strictLocus U ψ k ∩ O).indicator fun _ => (1 : ℝ)) :=
          mulBorel_indicator_indicator hS' hOk' hOm
  ext γ χ
  have h1 := tendsto_mulBorel_strictLocus_inter hqp hφ hWφ hOm γ χ
  have h2 := tendsto_mulBorel_strictLocus_inter hqp hψ hWψ hOm γ χ
  simp_rw [hstep] at h1
  exact tendsto_nhds_unique h1 h2

end Product

end SGPT.NPP.NonPluripolarCurrent
