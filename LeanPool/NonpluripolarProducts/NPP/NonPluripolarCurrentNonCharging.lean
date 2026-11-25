/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentManifold
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorNonCharging

/-!
# The non-pluripolar product puts no mass on pluripolar sets

Source: `chapter_npp.tex`, `prop:npp1` (4); Xia, *Foundations of pluripotential theory*,
`lem:nonpluripolar-truncation-limit` ("every pluripolar subset of `U` has outer measure zero for
`μ`", `μ` the trace measure of the product) and `prop:finite-locus-truncation`.

* `traceMeasure_btProduct_eq` — the trace measure `dd^c u₁ ∧ ⋯ ∧ dd^c u_p ∧ ω₀^{n-p}` of a
  Bedford–Taylor product of every degree is the top-degree mixed Bedford–Taylor measure of
  `(ℓ, …, ℓ, u₁, …, u_p)`, `ℓ` a quadratic potential of the Euclidean Kähler form `ω₀`
  (S11's reduction `BedfordTaylorTopDegree.btProduct_apply_wedgeProd`);
* `doesNotChargePluripolarOn_btProduct` — hence it does not charge locally pluripolar sets
  (TN `IsLocalMixedBedfordTaylorMeasure.doesNotChargePluripolarOn`, from the weighted
  Chern–Levine–Nirenberg estimate);
* `traceMeasure_glue` — the trace measure of the glued current is the glued measure;
* `doesNotChargePluripolarOn_nonPluripolarProduct` (local) and
  `doesNotChargePluripolarOn_nonPluripolarProduct_inChart` (on a manifold, in every chart): the
  trace measure of the non-pluripolar product, which dominates all its coefficient measures, gives
  zero (outer) mass to every locally pluripolar set.

The local statements use the convention at `NonPluripolarCurrent.nonPluripolarProduct`.
A factor may be identically `-∞` on an open component, where the product vanishes.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

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

/-- `β ∧ ⋯ ∧ β = β^q`. -/
theorem wedgeProd_const (β : RealForm n 2) :
    ∀ q, TopDegreeDensity.wedgeProd q (fun _ => β) = formPower β q
  | 0 => rfl
  | q + 1 => by
    rw [TopDegreeDensity.wedgeProd, formPower_succ, ← wedgeProd_const β q]

/-- **The trace measure of a Bedford–Taylor product of degree `p`** is the top-degree mixed
Bedford–Taylor measure `dd^c ℓ ∧ ⋯ ∧ dd^c ℓ ∧ dd^c u₁ ∧ ⋯ ∧ dd^c u_p` with `dd^c ℓ = ω₀`. -/
theorem traceMeasure_btProduct_eq {p q : ℕ} {U : Opens (ComplexModel (q + p))}
    {u : Fin p → ComplexModel (q + p) → ℝ} (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    (isPositive_btProduct p q u (oneCurrentOf (U := U) rfl) (isPositive_oneCurrentOf _)
        (isClosedAny_oneCurrentOf _) hu).1.traceMeasure =
      LocalBedfordTaylorSmoothTraceMeasure.recursiveMixedTraceMeasure U
        (Fin.append (fun _ => BedfordTaylorTopDegree.quadPot (standardHermitianTwoForm (q + p))) u)
        (BedfordTaylorTopDegree.isLocallyBoundedPshOn_append
          (fun _ => BedfordTaylorTopDegree.isLocallyBoundedPshOn_quadPot
            isSemipositiveOneOne_kahlerForm U) hu) := by
  set hB := (isPositive_btProduct p q u (oneCurrentOf (U := U) rfl) (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _) hu).1
  have hℓ := BedfordTaylorTopDegree.isLocallyBoundedPshOn_append
    (fun (_ : Fin q) => BedfordTaylorTopDegree.isLocallyBoundedPshOn_quadPot
      isSemipositiveOneOne_kahlerForm U) hu
  have hM := (isPositive_btProduct (q + p) 0 _ (oneCurrentOf (U := U) (Nat.zero_add (q + p)))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hℓ).1
  have hP :
      TopDegreeDensity.wedgeProd q (fun _ => standardHermitianTwoForm (q + p)) ∈
        formSpan (q + p) q := by
    rw [wedgeProd_const]
    exact formPower_mem_formSpan q
  have hk : (⟨TopDegreeDensity.wedgeProd q (fun _ => standardHermitianTwoForm (q + p)), hP⟩ :
      formSpan (q + p) q) = kahlerPower (q + p) q :=
    Subtype.ext (wedgeProd_const _ q)
  refine LocalBedfordTaylorLocality.eq_of_forall_testFunction_integral_eq (U := U)
    hB.traceMeasure_compl hM.traceMeasure_compl (fun K hK hKU => hB.traceMeasure_lt_top hK hKU)
    (fun K hK hKU => hM.traceMeasure_lt_top hK hKU) fun φ => ?_
  rw [hB.integral_traceMeasure, ← hk, BedfordTaylorTopDegree.btProduct_apply_wedgeProd p q u hu
    (fun _ => standardHermitianTwoForm (q + p)) (fun _ => isSemipositiveOneOne_kahlerForm) hP φ]

/-- **Bedford–Taylor products of every degree do not charge pluripolar sets**: their trace
measures give zero outer mass to every locally pluripolar subset of `U`. -/
theorem doesNotChargePluripolarOn_btProduct {p q : ℕ} (hqp : q + p = n) {U : Opens (ComplexModel
    n)}
    {u : Fin p → (ComplexModel n) → ℝ} (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    DoesNotChargePluripolarOn
      (isPositive_btProduct p q u (oneCurrentOf (U := U) hqp) (isPositive_oneCurrentOf _)
        (isClosedAny_oneCurrentOf _) hu).1.traceMeasure (U : Set (ComplexModel n)) := by
  subst hqp
  rw [traceMeasure_btProduct_eq hu]
  exact BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.doesNotChargePluripolarOn
    (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure
      _)

section Glue

variable {U : Opens (ComplexModel n)} {q : ℕ} {B : ℕ → LocalProductCurrent n U q} {O : ℕ → Set
    (ComplexModel n)}

/-- **The trace measure of the glued current is the glued measure.** -/
theorem IsTruncationFamily.traceMeasure_glue (hF : IsTruncationFamily B O)
    (hm : hF.HasLocallyFiniteMass) :
    (hF.isPositive_glue hm).traceMeasure = hF.glueMeasure := by
  have hS := hF.isPositive_glue hm
  refine LocalBedfordTaylorLocality.eq_of_forall_testFunction_integral_eq (U := U)
    hS.traceMeasure_compl hF.glueMeasure_compl (fun K hK hKU => hS.traceMeasure_lt_top hK hKU)
    hm fun φ => ?_
  rw [hS.integral_traceMeasure, hF.glue_apply hm]
  refine integral_congr_ae ?_
  have h1 : ∀ᵐ x ∂hF.glueMeasure, hF.glueDensity x (kahlerPower n q) = 1 := by
    rw [IsTruncationFamily.glueMeasure, Currents.LayeredCurrent.measure, Measure.ae_sum_iff]
    intro k
    rw [ae_restrict_iff' (measurableSet_layer hF.measurableSet k)]
    filter_upwards [densityForm_kahlerPower_ae (hF.isPositive k)] with x hx hmem
    rw [hF.glueDensity_of_mem_layer hmem, hx]
  filter_upwards [h1] with x hx
  rw [hx, mul_one]

/-- The glued measure does not charge the sets that none of the `B_k` charges. -/
theorem IsTruncationFamily.glueMeasure_eq_zero (hF : IsTruncationFamily B O) {s : Set
    (ComplexModel n)}
    (hs : ∀ k, (hF.isPositive k).traceMeasure s = 0) : hF.glueMeasure s = 0 := by
  rw [IsTruncationFamily.glueMeasure, Currents.LayeredCurrent.measure,
    Measure.sum_apply_of_countable, tsum_eq_zero_iff]
  exact fun k => le_antisymm ((Measure.le_iff'.mp Measure.restrict_le_self s).trans (hs k).le)
    zero_le

end Glue

section Product

variable {p q : ℕ} (hqp : q + p = n) {U : Opens (ComplexModel n)} {φ : Fin p → (ComplexModel n)
    → EReal}

/-- **The non-pluripolar product puts no mass on pluripolar sets** (`prop:npp1` (4)): its trace
measure gives zero outer mass to every locally pluripolar subset of `U`. -/
theorem doesNotChargePluripolarOn_nonPluripolarProduct
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (hW : IsWellDefinedOn hqp U φ) :
    DoesNotChargePluripolarOn (isPositive_nonPluripolarProduct hqp hφ hW).traceMeasure
      (U : Set (ComplexModel n)) := by
  set hF := isTruncationFamily hqp hφ
  have hm := (isWellDefinedOn_iff hqp hφ).mp hW
  intro s hs
  have e : (isPositive_nonPluripolarProduct hqp hφ hW).traceMeasure =
      (hF.isPositive_glue hm).traceMeasure :=
    IsPositive.traceMeasure_congr _ _ (nonPluripolarProduct_eq hqp hφ)
  rw [e, hF.traceMeasure_glue hm]
  exact hF.glueMeasure_eq_zero fun k =>
    doesNotChargePluripolarOn_btProduct hqp (fun i => truncationReal_isLocallyBoundedPshOn (hφ i)
      k)
      s hs

end Product

end SGPT.NPP.NonPluripolarCurrent

namespace SGPT.NPP

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

/-- **`prop:npp1` (4) on a complex manifold**: in every chart, the trace measure of the
non-pluripolar product gives zero outer mass to every locally pluripolar subset of the
coordinate domain. -/
theorem doesNotChargePluripolarOn_nonPluripolarProduct_inChart {p q : ℕ} (hqp : q + p = n)
    {φ : Fin p → M → EReal} (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hW : IsNonPluripolarWellDefined hqp φ) (e : ComplexChart n M) :
    DoesNotChargePluripolarOn ((nonPluripolarProduct hqp φ hφ hW).isPositive e).traceMeasure
      (chartTarget e : Set (ComplexModel n)) :=
  NonPluripolarCurrent.doesNotChargePluripolarOn_nonPluripolarProduct hqp
    (chartPlurisubharmonicOn hφ e) (hW e)

end SGPT.NPP
