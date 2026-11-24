/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothPlurisubharmonic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedNonPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

/-!
# Bedford–Taylor products of arbitrary degree through top-degree products

Let `U ⊆ ℂⁿ` be open, `n = q + p`, and let `u₁, …, u_p` be locally bounded psh functions on `U`.
The recursive local product `S = dd^c u₁ ∧ ⋯ ∧ dd^c u_p`
(`LocalBedfordTaylorProducts.btProduct`), a closed positive current of bidimension `(q,q)`, is
determined by top-degree Bedford–Taylor measures: for constant semipositive `(1,1)`-forms
`β₁, …, β_q`,

`⟨S, φ β₁ ∧ ⋯ ∧ β_q⟩ = ∫ φ dd^c ℓ₁ ∧ ⋯ ∧ dd^c ℓ_q ∧ dd^c u₁ ∧ ⋯ ∧ dd^c u_p`,

where `ℓⱼ(z) = π βⱼ(z, i z)` is a quadratic potential of `βⱼ` (`dd^c ℓⱼ = βⱼ`), and the products
`β₁ ∧ ⋯ ∧ β_q` span the constant `(q,q)`-forms (`spCone_le_prodCone`).  This is the standard
reduction of `(p,p)`-currents to measures (FPT `def:positive-current`: a positive current is
determined by the measures `T ∧ γ` with `γ` strongly positive).

With it, the increasing convergence theorem for top-degree mixed measures
(`BedfordTaylor.incPClaim_all`, `BedfordTaylor.incWClaim_all`, Cegrell's proof, FPT
`thm:bt-increasing-continuity`) gives the increasing convergence of the products of every degree,
unweighted and weighted (`weakTendsto_btProduct_of_monotone`,
`weakTendsto_mulBorel_btProduct_of_monotone`), the missing half of `thm:contMA`.

## Main results

* `quadPot`, `smoothDDC_quadPot`, `isLocallyBoundedPshOn_quadPot` — quadratic potentials.
* `btProduct_append` — `B(ℓ ++ u; T) = B(ℓ; B(u; T))`.
* `btProduct_apply_wedgeProd` — the reduction to top degree.
* `weakTendsto_of_wedgeProd` — weak convergence is tested on the products `β₁ ∧ ⋯ ∧ β_q`.
* `weakTendsto_btProduct_of_monotone`, `weakTendsto_mulBorel_btProduct_of_monotone`.
* `mulBorel_btProduct_max_const` — mixed plurifine locality on the common strict locus,
  and `mulBorel_btProduct_truncation_consistent`, the consistency of the truncations used to
  define the non-pluripolar product of every degree (`def:npp:L69`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.NPP.BedfordTaylorTopDegree

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure

variable {n : ℕ}

/-! ### Quadratic potentials of constant `(1,1)`-forms -/

/-- The bilinear form `(v, w) ↦ β(v, w)` of a real two-form. -/
def bilin (β : RealForm n 2) : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin1 ℝ (ComplexModel n) ℝ).toLinearIsometry.toContinuousLinearMap.comp
    β.toContinuousMultilinearMap.curryLeft

theorem bilin_apply (β : RealForm n 2) (v w : ComplexModel n) : bilin β v w = β ![v, w] := by
  simp [bilin]

/-- The bilinear form of a two-form is antisymmetric. -/
theorem bilin_swap (β : RealForm n 2) (v w : ComplexModel n) : bilin β w v = -bilin β v w := by
  rw [bilin_apply, bilin_apply]
  have h := β.map_swap ![v, w] (show (0 : Fin 2) ≠ 1 by decide)
  have e : (![v, w] ∘ Equiv.swap 0 1 : Fin 2 → ComplexModel n) = ![w, v] := by
    ext i
    fin_cases i <;> rfl
  rw [e] at h
  exact h

/-- The quadratic potential `ℓ_β(z) = π β(z, i z)` of a constant real two-form `β`. -/
def quadPot (β : RealForm n 2) (z : ComplexModel n) : ℝ := Real.pi * β ![z, Complex.I • z]

/-- The real-linear map `z ↦ (z, i z)`. -/
private def diagI : ComplexModel n →L[ℝ] ComplexModel n × ComplexModel n :=
  (ContinuousLinearMap.id ℝ (ComplexModel n)).prod
    (Complex.I • ContinuousLinearMap.id ℝ (ComplexModel n) :
      ComplexModel n →L[ℝ] ComplexModel n)

private theorem diagI_apply (z : ComplexModel n) : diagI z = (z, Complex.I • z) := by
  simp [diagI]

/-- `(x, y) ↦ π β(x, y)`. -/
private def bilinFun (β : RealForm n 2) (p : ComplexModel n × ComplexModel n) : ℝ :=
  Real.pi * bilin β p.1 p.2

private theorem contDiff_bilinFun (β : RealForm n 2) : ContDiff ℝ ∞ (bilinFun β) :=
  contDiff_const.mul ((bilin β).isBoundedBilinearMap.contDiff)

private theorem quadPot_eq (β : RealForm n 2) :
    quadPot β = fun z => bilinFun β (0 + diagI z) := by
  funext z
  simp [quadPot, bilinFun, diagI_apply, bilin_apply]

theorem contDiff_quadPot (β : RealForm n 2) : ContDiff ℝ ∞ (quadPot β) := by
  rw [quadPot_eq]
  exact (contDiff_bilinFun β).comp (contDiff_const.add diagI.contDiff)

private theorem realHessian_bilinFun (β : RealForm n 2) (p a b : ComplexModel n × ComplexModel n) :
    realHessian (bilinFun β) p a b = Real.pi * (bilin β a.1 b.2 + bilin β b.1 a.2) := by
  have hB : IsBoundedBilinearMap ℝ (fun p : ComplexModel n × ComplexModel n => bilin β p.1 p.2) :=
    (bilin β).isBoundedBilinearMap
  have hf : fderiv ℝ (bilinFun β) = fun p => Real.pi • hB.deriv p := by
    funext p
    rw [show bilinFun β = fun p => Real.pi * bilin β p.1 p.2 from rfl,
      fderiv_const_mul (hB.differentiableAt p), hB.fderiv p]
  rw [realHessian_eq_fderiv, hf, show (fun p => Real.pi • hB.deriv p) =
      Real.pi • (fun p => hB.deriv p) from rfl,
    fderiv_const_smul (hB.isBoundedLinearMap_deriv.differentiable.differentiableAt),
    hB.isBoundedLinearMap_deriv.fderiv]
  change Real.pi • hB.deriv a b = _
  rw [IsBoundedBilinearMap.deriv_apply, smul_eq_mul]

/-- The real Hessian of the quadratic potential. -/
theorem realHessian_quadPot (β : RealForm n 2) (z v w : ComplexModel n) :
    realHessian (quadPot β) z v w =
      Real.pi * (bilin β v (Complex.I • w) + bilin β w (Complex.I • v)) := by
  rw [quadPot_eq, realHessian_comp_affine ((contDiff_bilinFun β).of_le (WithTop.coe_le_coe.mpr
    le_top)) diagI 0 z v w,
    realHessian_bilinFun]
  simp [diagI_apply]

private theorem I_smul_I_smul (v : ComplexModel n) : Complex.I • Complex.I • v = -v := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-- **`dd^c ℓ_β = β`** for a real `(1,1)`-form `β`, at every point. -/
theorem smoothDDC_quadPot {β : RealForm n 2} (hβ : IsOneOne β) (z : ComplexModel n) :
    smoothDDC (quadPot β) z = β := by
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  have hβ' : ∀ a b : ComplexModel n, bilin β (Complex.I • a) (Complex.I • b) = bilin β a b := by
    intro a b
    rw [bilin_apply, bilin_apply, hβ a b]
  rw [hv, FirstPass.smoothDDC_apply_eq_realHessian ((contDiff_quadPot β).contDiffAt.of_le
    (WithTop.coe_le_coe.mpr le_top)),
    realHessian_quadPot, realHessian_quadPot, I_smul_I_smul, I_smul_I_smul, hβ', hβ',
    ← bilin_apply, map_neg, map_neg, bilin_swap β (v 0) (v 1)]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The Levi form of `ℓ_β` is `π β(v, i v)`. -/
theorem leviForm_quadPot {β : RealForm n 2} (hβ : IsOneOne β) (z v : ComplexModel n) :
    leviForm (quadPot β) z v = Real.pi * β ![v, Complex.I • v] := by
  have hβ' : ∀ a b : ComplexModel n, bilin β (Complex.I • a) (Complex.I • b) = bilin β a b := by
    intro a b
    rw [bilin_apply, bilin_apply, hβ a b]
  rw [leviForm, realHessian_quadPot, realHessian_quadPot, I_smul_I_smul, map_neg,
    bilin_swap β v (Complex.I • v), ← bilin_apply]
  ring

/-- For a semipositive `(1,1)`-form `β`, `ℓ_β` is a (smooth, hence locally bounded) psh
function on every open set. -/
theorem isLocallyBoundedPshOn_quadPot {β : RealForm n 2} (hβ : IsSemipositiveOneOne β)
    (U : Opens (ComplexModel n)) : IsLocallyBoundedPshOn U (quadPot β) := by
  refine ⟨plurisubharmonicOn_of_levi_nonneg ((contDiff_quadPot β).of_le (WithTop.coe_le_coe.mpr
    le_top)) U.isOpen
    fun x _ v => ?_, fun z hz => ?_⟩
  · rw [leviForm_quadPot hβ.1]
    exact mul_nonneg Real.pi_pos.le (hβ.2 v)
  · obtain ⟨C, hC⟩ := (isCompact_closedBall z 1).exists_bound_of_continuousOn
      (contDiff_quadPot β).continuous.continuousOn
    refine ⟨U ⊓ ⟨Metric.ball z 1, Metric.isOpen_ball⟩, ⟨hz, Metric.mem_ball_self one_pos⟩,
      inf_le_left, C, fun w hw => ?_⟩
    simpa [Real.norm_eq_abs] using hC w (Metric.ball_subset_closedBall hw.2)

/-! ### Concatenating the potentials -/

theorem init_append {α : Type*} {q p : ℕ} (ℓ : Fin q → α) (u : Fin (p + 1) → α) :
    Fin.init (n := q + p) (Fin.append ℓ u : Fin (q + (p + 1)) → α) =
      Fin.append ℓ (Fin.init u) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have e : Fin.castSucc (Fin.castAdd p j) = Fin.castAdd (p + 1) j := Fin.ext rfl
    simp only [Fin.init, e, Fin.append_left]
  · have e : Fin.castSucc (Fin.natAdd q j) = Fin.natAdd q (Fin.castSucc j) := Fin.ext rfl
    simp only [Fin.init, e, Fin.append_right]

theorem append_last {α : Type*} {q p : ℕ} (ℓ : Fin q → α) (u : Fin (p + 1) → α) :
    Fin.append ℓ u (Fin.last (q + p)) = u (Fin.last p) := by
  have e : (Fin.last (q + p) : Fin (q + (p + 1))) = Fin.natAdd q (Fin.last p) := Fin.ext rfl
  rw [e, Fin.append_right]

open LocalBedfordTaylorCollar in
/-- `B(ℓ ++ u; T) = B(ℓ; B(u; T))`. -/
theorem btProduct_append {U : Opens (ComplexModel n)} : ∀ (p q r s : ℕ) (hs : s = r + q)
    (ℓ : Fin q → ComplexModel n → ℝ) (u : Fin p → ComplexModel n → ℝ)
    (T : LocalProductCurrent n U (r + (q + p))) (T' : LocalProductCurrent n U (s + p)),
    HEq T T' →
      btProduct (q + p) r (Fin.append ℓ u) T = btProduct q r ℓ (castLPC hs (btProduct p s u T'))
  | 0, q, r, s, hs, ℓ, u, T, T', hT => by
    subst hs
    have e : T = T' := eq_of_heq hT
    subst e
    have : Fin.append ℓ u = ℓ := by
      rw [Fin.append_right_nil ℓ u rfl]
      rfl
    rw [this]
    rfl
  | p + 1, q, r, s, hs, ℓ, u, T, T', hT => by
    have h1 : btProduct (q + (p + 1)) r (Fin.append ℓ u) T =
        btProduct (q + p) r (Fin.init (n := q + p)
            (Fin.append ℓ u : Fin (q + (p + 1)) → ComplexModel n → ℝ))
          (ddcMul T (Fin.append ℓ u (Fin.last (q + p)))) := rfl
    rw [h1, init_append, append_last]
    exact btProduct_append p q r s hs ℓ (Fin.init u) _ _
      (ddcMul_heq (a := r + (q + p)) (b := s + p) (by omega) hT _)

/-- A concatenation of locally bounded psh tuples is locally bounded psh. -/
theorem isLocallyBoundedPshOn_append {U : Opens (ComplexModel n)} {q p : ℕ}
    {ℓ : Fin q → ComplexModel n → ℝ} {u : Fin p → ComplexModel n → ℝ}
    (hℓ : ∀ i, IsLocallyBoundedPshOn U (ℓ i)) (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    ∀ i, IsLocallyBoundedPshOn U (Fin.append ℓ u i) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; exact hℓ j
  · rw [Fin.append_right]; exact hu j

/-- The currents `[U]` read in two equal bidimensions agree. -/
theorem heq_oneCurrentOf {U : Opens (ComplexModel n)} {k k' : ℕ} (hk : k = n) (hk' : k' = n) :
    HEq (oneCurrentOf (U := U) hk) (oneCurrentOf (U := U) hk') := by
  subst hk
  subst hk'
  rfl

open LocalBedfordTaylorCollar LocalBedfordTaylorForms in
private theorem wedgeForm_castLPC' {U : Opens (ComplexModel n)} {a b r k : ℕ} (hab : a = b)
    (h : r + k = a) (T : LocalProductCurrent n U a) {α : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm (h.trans hab) (castLPC hab T) hα = wedgeForm h T hα := by
  subst hab
  rfl

/-! ### The reduction to top degree -/

open LocalBedfordTaylorCollar LocalBedfordTaylorForms LocalBedfordTaylorSmoothProductDensity
  LocalBedfordTaylorSmooth ConstantFormProducts in
/-- **Reduction to top degree**, for any smooth psh potentials `ℓⱼ` of the constant
semipositive `(1,1)`-forms `βⱼ` on `U`: `⟨dd^c u₁ ∧ ⋯ ∧ dd^c u_p, φ β₁ ∧ ⋯ ∧ β_q⟩` is the integral
of `φ` against the top-degree Bedford–Taylor measure
`dd^c ℓ₁ ∧ ⋯ ∧ dd^c ℓ_q ∧ dd^c u₁ ∧ ⋯ ∧ dd^c u_p`. -/
theorem btProduct_apply_wedgeProd_of_ddc (p q : ℕ) {U : Opens (ComplexModel (q + p))}
    (u : Fin p → ComplexModel (q + p) → ℝ) (hu : ∀ i, IsLocallyBoundedPshOn U (u i))
    (β : Fin q → RealForm (q + p) 2) (ℓ : Fin q → ComplexModel (q + p) → ℝ)
    (hℓs : ∀ i, ContDiffOn ℝ ∞ (ℓ i) U) (hℓ : ∀ i, IsLocallyBoundedPshOn U (ℓ i))
    (hddc : ∀ i, ∀ x ∈ U, smoothDDC (ℓ i) x = β i)
    (hP : TopDegreeDensity.wedgeProd q β ∈ formSpan (q + p) q) (φ : 𝓓(U, ℝ)) :
    btProduct p q u (oneCurrentOf (U := U) rfl) ⟨TopDegreeDensity.wedgeProd q β, hP⟩ φ =
      ∫ x, φ x ∂LocalBedfordTaylorSmoothTraceMeasure.recursiveMixedTraceMeasure U
        (Fin.append ℓ u) (isLocallyBoundedPshOn_append hℓ hu) := by
  obtain ⟨hS, hSc⟩ := isPositive_btProduct p q u (oneCurrentOf (U := U) rfl)
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu
  have hs : q = 0 + q := (Nat.zero_add q).symm
  rw [LocalBedfordTaylorSmoothTraceMeasure.recursiveMixedTraceMeasure,
    IsPositive.integral_traceMeasure,
    btProduct_append p q 0 q hs _ u _ (oneCurrentOf (U := U) rfl) (heq_oneCurrentOf _ _),
    btProduct_eq_wedgeForm q 0 ℓ hℓs (fun i => (hℓ i).1) _ (isPositive_castLPC hs hS)
      (isClosedAny_castLPC hs hSc),
    wedgeForm_castLPC' hs (Nat.zero_add q)]
  have hrep : ∀ x ∈ U, TopDegreeDensity.wedgeProd q (fun i => ddcForm (ℓ i) x) =
      ∑ j : Unit, (fun _ _ => (1 : ℝ)) j x •
        ((fun _ => (⟨TopDegreeDensity.wedgeProd q β, hP⟩ : formSpan (q + p) q)) j :
          RealForm (q + p) (2 * q)) := by
    intro x hx
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    congr 1
    funext i
    exact hddc i x hx
  rw [wedgeForm_apply_eq (Nat.zero_add q) _ _ (fun x hx => by rw [hrep x hx]; simpa using hP)
    (fun _ _ => (1 : ℝ)) (fun _ => contDiffOn_const) _ hrep]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have eφ : mulSmoothOnCLM (U := U) (contDiffOn_const (c := (1 : ℝ))) φ = φ := by
    ext x
    simp only [mulSmoothOnCLM_apply, mul_one]
  have eγ : wedgeSpan (q + p) (Nat.zero_add q) (kahlerPower (q + p) 0)
      ⟨TopDegreeDensity.wedgeProd q β, hP⟩ = ⟨TopDegreeDensity.wedgeProd q β, hP⟩ := by
    apply Subtype.ext
    rw [coe_wedgeSpan_apply (Nat.zero_add q) _ _ (by omega)]
    change wedgeTo (by omega : 0 + 2 * q = 2 * q) (coordinateWedgeUnit : RealForm (q + p) 0)
      (TopDegreeDensity.wedgeProd q β) = _
    rw [wedgeTo_unit_left _ rfl]
    rfl
  rw [eφ, eγ]

/-- **Reduction to top degree** with the quadratic potentials `ℓ_{βⱼ}`. -/
theorem btProduct_apply_wedgeProd (p q : ℕ) {U : Opens (ComplexModel (q + p))}
    (u : Fin p → ComplexModel (q + p) → ℝ) (hu : ∀ i, IsLocallyBoundedPshOn U (u i))
    (β : Fin q → RealForm (q + p) 2) (hβ : ∀ i, IsSemipositiveOneOne (β i))
    (hP : TopDegreeDensity.wedgeProd q β ∈ formSpan (q + p) q) (φ : 𝓓(U, ℝ)) :
    btProduct p q u (oneCurrentOf (U := U) rfl) ⟨TopDegreeDensity.wedgeProd q β, hP⟩ φ =
      ∫ x, φ x ∂LocalBedfordTaylorSmoothTraceMeasure.recursiveMixedTraceMeasure U
        (Fin.append (fun i => quadPot (β i)) u)
        (isLocallyBoundedPshOn_append (fun i => isLocallyBoundedPshOn_quadPot (hβ i) U) hu) :=
  btProduct_apply_wedgeProd_of_ddc p q u hu β _ (fun _ => (contDiff_quadPot _).contDiffOn)
    (fun i => isLocallyBoundedPshOn_quadPot (hβ i) U) (fun i x _ => smoothDDC_quadPot (hβ i).1 x)
    hP φ

/-- The weighted form of the reduction: `⟨g · dd^c u₁ ∧ ⋯ ∧ dd^c u_p, φ β₁ ∧ ⋯ ∧ β_q⟩` is the
integral of `φ g` against the same top-degree measure, for every measurable `g` bounded on the
compact subsets of `U`. -/
theorem mulBorel_btProduct_apply_wedgeProd_of_ddc (p q : ℕ) {U : Opens (ComplexModel (q + p))}
    (u : Fin p → ComplexModel (q + p) → ℝ) (hu : ∀ i, IsLocallyBoundedPshOn U (u i))
    (β : Fin q → RealForm (q + p) 2) (ℓ : Fin q → ComplexModel (q + p) → ℝ)
    (hℓs : ∀ i, ContDiffOn ℝ ∞ (ℓ i) U) (hℓ : ∀ i, IsLocallyBoundedPshOn U (ℓ i))
    (hddc : ∀ i, ∀ x ∈ U, smoothDDC (ℓ i) x = β i)
    (hP : TopDegreeDensity.wedgeProd q β ∈ formSpan (q + p) q) {g : ComplexModel (q + p) → ℝ}
    (hg : Measurable g) (hgb : IsLocallyBoundedOn g U) (φ : 𝓓(U, ℝ)) :
    mulBorel (btProduct p q u (oneCurrentOf (U := U) rfl)) g
        ⟨TopDegreeDensity.wedgeProd q β, hP⟩ φ =
      ∫ x, φ x * g x ∂LocalBedfordTaylorSmoothTraceMeasure.recursiveMixedTraceMeasure U
        (Fin.append ℓ u) (isLocallyBoundedPshOn_append hℓ hu) := by
  obtain ⟨hS, -⟩ := isPositive_btProduct p q u (oneCurrentOf (U := U) rfl)
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu
  have hν := (isPositive_btProduct (q + p) 0 (Fin.append ℓ u)
    (oneCurrentOf (U := U) (Nat.zero_add _)) (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _) (isLocallyBoundedPshOn_append hℓ hu)).1
  have hd : LocalBedfordTaylorForms.IsLocalDensity (U := U) hν.traceMeasure
      (fun _ => (1 : ℝ)) :=
    ⟨hν.traceMeasure_compl, fun K hK hKU => hν.traceMeasure_lt_top hK hKU, measurable_const,
      fun K _ _ => ⟨1, fun x _ => by simp⟩⟩
  have hrep : ∀ ψ : 𝓓(U, ℝ), btProduct p q u (oneCurrentOf (U := U) rfl)
      ⟨TopDegreeDensity.wedgeProd q β, hP⟩ ψ =
        ∫ x, ψ x * (fun _ => (1 : ℝ)) x ∂hν.traceMeasure := fun ψ => by
    rw [btProduct_apply_wedgeProd_of_ddc p q u hu β ℓ hℓs hℓ hddc hP ψ]
    simp only [mul_one]
    rfl
  rw [LocalBedfordTaylorForms.mulBorel_apply_of_integral_eq hS _ hd hrep hg hgb φ]
  simp only [mul_one]
  rfl

open TopDegreeDensity in
/-- Products of semipositive `(1,1)`-forms are constant `(q,q)`-forms of `formSpan`. -/
theorem prodCone_le_formSpan {q : ℕ} {P : RealForm n (2 * q)} (hP : P ∈ prodCone q) :
    P ∈ formSpan n q := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact LocalBedfordTaylorSmoothProductDensity.wedgeProd_mem_formSpan q β
      fun i => oneOne_mem_formSpan (hβ i).1
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_of_tower_mem _ a hx

open TopDegreeDensity LocalBedfordTaylorContinuity in
/-- Weak convergence of currents of bidimension `(q,q)` is tested on the products
`β₁ ∧ ⋯ ∧ β_q` of semipositive constant `(1,1)`-forms. -/
theorem weakTendsto_of_wedgeProd {U : Opens (ComplexModel n)} {q : ℕ}
    (T : ℕ → LocalProductCurrent n U q) (T₀ : LocalProductCurrent n U q)
    (h : ∀ (β : Fin q → RealForm n 2), (∀ i, IsSemipositiveOneOne (β i)) →
      ∀ (hP : wedgeProd q β ∈ formSpan n q) (φ : 𝓓(U, ℝ)),
        Tendsto (fun k => T k ⟨wedgeProd q β, hP⟩ φ) atTop (𝓝 (T₀ ⟨wedgeProd q β, hP⟩ φ))) :
    WeakTendsto T T₀ := by
  intro γ φ
  -- the product cone
  have hprod : ∀ P (hP : P ∈ prodCone q) (hP' : P ∈ formSpan n q),
      Tendsto (fun k => T k ⟨P, hP'⟩ φ) atTop (𝓝 (T₀ ⟨P, hP'⟩ φ)) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      exact fun hP' => h β hβ hP' φ
    | zero =>
      intro hP'
      have e : (⟨0, hP'⟩ : formSpan n q) = 0 := rfl
      simp only [e, map_zero, _root_.zero_apply]
      exact tendsto_const_nhds
    | add x y hx hy ihx ihy =>
      intro hP'
      have e : (⟨x + y, hP'⟩ : formSpan n q) =
          ⟨x, prodCone_le_formSpan hx⟩ + ⟨y, prodCone_le_formSpan hy⟩ := rfl
      simp only [e, map_add, _root_.add_apply]
      exact (ihx _).add (ihy _)
    | smul a x hx ihx =>
      intro hP'
      have e : (⟨a • x, hP'⟩ : formSpan n q) = (a : ℝ) • ⟨x, prodCone_le_formSpan hx⟩ := rfl
      simp only [e, map_smul, _root_.smul_apply, smul_eq_mul]
      exact (ihx _).const_mul _
  obtain ⟨P, hP⟩ := γ
  induction hP using Submodule.span_induction with
  | mem x hx => exact hprod x (spCone_le_prodCone q hx) _
  | zero =>
    have e : (⟨0, Submodule.zero_mem _⟩ : formSpan n q) = 0 := rfl
    simp only [e, map_zero, _root_.zero_apply]
    exact tendsto_const_nhds
  | add x y hx hy ihx ihy =>
    have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : formSpan n q) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    simp only [e, map_add, _root_.add_apply]
    exact ihx.add ihy
  | smul a x hx ihx =>
    have e : (⟨a • x, Submodule.smul_mem _ a hx⟩ : formSpan n q) = a • ⟨x, hx⟩ := rfl
    simp only [e, map_smul, _root_.smul_apply, smul_eq_mul]
    exact ihx.const_mul _

open TopDegreeDensity LocalBedfordTaylorContinuity in
/-- Two currents of bidimension `(q,q)` agreeing on all products `β₁ ∧ ⋯ ∧ β_q` of semipositive
constant `(1,1)`-forms are equal. -/
theorem eq_of_wedgeProd {U : Opens (ComplexModel n)} {q : ℕ} (A B : LocalProductCurrent n U q)
    (h : ∀ (β : Fin q → RealForm n 2), (∀ i, IsSemipositiveOneOne (β i)) →
      ∀ (hP : wedgeProd q β ∈ formSpan n q) (φ : 𝓓(U, ℝ)),
        A ⟨wedgeProd q β, hP⟩ φ = B ⟨wedgeProd q β, hP⟩ φ) : A = B := by
  ext γ φ
  have hw := weakTendsto_of_wedgeProd (fun _ => A) B
    (fun β hβ hP φ => by rw [h β hβ hP φ]; exact tendsto_const_nhds) γ φ
  exact tendsto_nhds_unique tendsto_const_nhds hw

open TopDegreeDensity LocalBedfordTaylorContinuity BedfordTaylor in
private theorem isIncAdmissible_append (p q : ℕ) {U : Opens (ComplexModel (q + p))}
    (β : Fin q → RealForm (q + p) 2) (hβ : ∀ i, IsSemipositiveOneOne (β i))
    (u : ℕ → Fin p → ComplexModel (q + p) → ℝ) (u₀ : Fin p → ComplexModel (q + p) → ℝ)
    (hu : ∀ k i, IsLocallyBoundedPshOn U (u k i)) (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hmono : ∀ i, ∀ z ∈ U, Monotone fun k => u k i z)
    (hae : ∀ i, ∀ᵐ z, z ∈ U → Tendsto (fun k => u k i z) atTop (𝓝 (u₀ i z))) :
    IsIncAdmissible (q + p) U (Fin.append (fun i => quadPot (β i)) u₀)
      (fun i k => Fin.append (fun i => quadPot (β i)) (u k) i) := by
  refine ⟨isLocallyBoundedPshOn_append (fun i => isLocallyBoundedPshOn_quadPot (hβ i) U) hu₀,
    fun i => ?_, fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    exact isIncApprox_const (isLocallyBoundedPshOn_quadPot (hβ j) U)
  · simp only [Fin.append_right]
    exact isIncApprox_of_monotone_ae (hu₀ j) (fun k => hu k j)
      (hmono j) (hae j)

/-! ### Increasing convergence -/

open TopDegreeDensity LocalBedfordTaylorContinuity BedfordTaylor in
/-- **Increasing convergence of Bedford–Taylor products of every degree** (unweighted;
FPT `thm:bt-increasing-continuity`): if `u_i^k ↑ u_i` almost everywhere on `U`, all functions
locally bounded psh, then `dd^c u_1^k ∧ ⋯ ∧ dd^c u_p^k → dd^c u_1 ∧ ⋯ ∧ dd^c u_p` weakly. -/
theorem weakTendsto_btProduct_of_monotone {p q : ℕ} (hqp : q + p = n)
    {U : Opens (ComplexModel n)}
    (u : ℕ → Fin p → ComplexModel n → ℝ) (u₀ : Fin p → ComplexModel n → ℝ)
    (hu : ∀ k i, IsLocallyBoundedPshOn U (u k i)) (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hmono : ∀ i, ∀ z ∈ U, Monotone fun k => u k i z)
    (hae : ∀ i, ∀ᵐ z, z ∈ U → Tendsto (fun k => u k i z) atTop (𝓝 (u₀ i z))) :
    WeakTendsto (fun k => btProduct p q (u k) (oneCurrentOf (U := U) hqp))
      (btProduct p q u₀ (oneCurrentOf (U := U) hqp)) := by
  subst hqp
  refine weakTendsto_of_wedgeProd _ _ fun β hβ hP φ => ?_
  simp only [btProduct_apply_wedgeProd p q _ (hu _) β hβ hP φ,
    btProduct_apply_wedgeProd p q _ hu₀ β hβ hP φ]
  have hv := isLocallyBoundedPshOn_append (fun i => isLocallyBoundedPshOn_quadPot (hβ i) U) hu₀
  exact incPClaim_all U _ _ _ _ (isIncAdmissible_append p q β hβ u u₀ hu hu₀ hmono hae)
    (fun k => IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure
        (isLocallyBoundedPshOn_append (fun i => isLocallyBoundedPshOn_quadPot (hβ i) U) (hu k))))
    (IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure
        hv)) φ φ.continuous φ.hasCompactSupport φ.tsupport_subset

open TopDegreeDensity LocalBedfordTaylorContinuity BedfordTaylor LocalBedfordTaylorForms in
/-- **Increasing convergence of Bedford–Taylor products of every degree**, weighted form:
`u_0^k dd^c u_1^k ∧ ⋯ ∧ dd^c u_p^k → u_0 dd^c u_1 ∧ ⋯ ∧ dd^c u_p`. -/
theorem weakTendsto_mulBorel_btProduct_of_monotone {p q : ℕ} (hqp : q + p = n)
    {U : Opens (ComplexModel n)}
    (u : ℕ → Fin (p + 1) → ComplexModel n → ℝ) (u₀ : Fin (p + 1) → ComplexModel n → ℝ)
    (hu : ∀ k i, IsLocallyBoundedPshOn U (u k i)) (hu₀ : ∀ i, IsLocallyBoundedPshOn U (u₀ i))
    (hmono : ∀ i, ∀ z ∈ U, Monotone fun k => u k i z)
    (hae : ∀ i, ∀ᵐ z, z ∈ U → Tendsto (fun k => u k i z) atTop (𝓝 (u₀ i z))) :
    WeakTendsto (fun k => mulBorel (btProduct p q (Fin.tail (u k)) (oneCurrentOf (U := U) hqp))
        ((U : Set (ComplexModel n)).indicator (u k 0)))
      (mulBorel (btProduct p q (Fin.tail u₀) (oneCurrentOf (U := U) hqp))
        ((U : Set (ComplexModel n)).indicator (u₀ 0))) := by
  subst hqp
  refine weakTendsto_of_wedgeProd _ _ fun β hβ hP φ => ?_
  have hℓ : ∀ i, IsLocallyBoundedPshOn U (quadPot (β i)) :=
    fun i => isLocallyBoundedPshOn_quadPot (hβ i) U
  have key : ∀ (w : Fin p → ComplexModel (q + p) → ℝ) (hw : ∀ i, IsLocallyBoundedPshOn U (w i))
      (g : ComplexModel (q + p) → ℝ) (hg : IsLocallyBoundedPshOn U g),
      mulBorel (btProduct p q w (oneCurrentOf (U := U) rfl))
          ((U : Set (ComplexModel (q + p))).indicator g) ⟨wedgeProd q β, hP⟩ φ =
        ∫ x, φ x * g x ∂LocalBedfordTaylorSmoothTraceMeasure.recursiveMixedTraceMeasure U
          (Fin.append (fun i => quadPot (β i)) w) (isLocallyBoundedPshOn_append hℓ hw) := by
    intro w hw g hg
    obtain ⟨hS, -⟩ := isPositive_btProduct p q w (oneCurrentOf (U := U) rfl)
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hw
    have hν := (isPositive_btProduct (q + p) 0 (Fin.append (fun i => quadPot (β i)) w)
      (oneCurrentOf (U := U) (Nat.zero_add _)) (isPositive_oneCurrentOf _)
      (isClosedAny_oneCurrentOf _) (isLocallyBoundedPshOn_append hℓ hw)).1
    have hd : IsLocalDensity (U := U) hν.traceMeasure (fun _ => (1 : ℝ)) :=
      ⟨hν.traceMeasure_compl, fun K hK hKU => hν.traceMeasure_lt_top hK hKU, measurable_const,
        fun K _ _ => ⟨1, fun x _ => by simp⟩⟩
    have hrep : ∀ ψ : 𝓓(U, ℝ), btProduct p q w (oneCurrentOf (U := U) rfl)
        ⟨wedgeProd q β, hP⟩ ψ = ∫ x, ψ x * (fun _ => (1 : ℝ)) x ∂hν.traceMeasure := fun ψ => by
      rw [btProduct_apply_wedgeProd p q w hw β hβ hP ψ]
      simp only [mul_one]
      rfl
    rw [mulBorel_apply_of_integral_eq hS _ hd hrep
      (measurable_indicator_of_isLocallyBoundedPshOn hg) (isLocallyBoundedOn_indicator hg) φ]
    change _ = ∫ x, φ x * g x ∂hν.traceMeasure
    refine integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hν.traceMeasure_compl] with x hx
    have hxU : x ∈ (U : Set (ComplexModel (q + p))) := by simpa using hx
    simp [Set.indicator_of_mem hxU]
  have e1 : ∀ k, mulBorel (btProduct p q (Fin.tail (u k)) (oneCurrentOf (U := U) rfl))
      ((U : Set (ComplexModel (q + p))).indicator (u k 0)) ⟨wedgeProd q β, hP⟩ φ =
        ∫ x, φ x * u k 0 x ∂LocalBedfordTaylorSmoothTraceMeasure.recursiveMixedTraceMeasure U
          (Fin.append (fun i => quadPot (β i)) (Fin.tail (u k)))
          (isLocallyBoundedPshOn_append hℓ (fun i => hu k i.succ)) :=
    fun k => key _ (fun i => hu k i.succ) _ (hu k 0)
  rw [funext e1, key (Fin.tail u₀) (fun i => hu₀ i.succ) _ (hu₀ 0)]
  have hv := isLocallyBoundedPshOn_append hℓ (fun i => hu₀ i.succ)
  exact incWClaim_all U _ _ _ _
    (isIncAdmissible_append p q β hβ (fun k => Fin.tail (u k)) (Fin.tail u₀)
      (fun k i => hu k i.succ) (fun i => hu₀ i.succ) (fun i => hmono i.succ) (fun i => hae i.succ))
    (fun k => IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure
        (isLocallyBoundedPshOn_append hℓ (fun i => hu k i.succ))))
    (IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure
        hv))
    (u₀ 0) (fun k => u k 0) (hu₀ 0)
    (isIncApprox_of_monotone_ae (hu₀ 0) (fun k => hu k 0) (hmono 0) (hae 0))
    φ φ.continuous φ.hasCompactSupport φ.tsupport_subset

/-! ### Locality on the plurifine open sets `{v > c}` -/

open TopDegreeDensity in
/-- **Mixed locality on the common strict locus.** This is a consequence of
[Xia's mixed plurifine locality theorem](
https://github.com/MingchenXia/foundations-of-pluripotential-theory/blob/5d7f16338ae82d4933193a0cb331365e737824db/chapters/q03-pluripolar-sets-and-the-plurifine-topology.tex#L350-L355).
Apply the theorem to the separately truncated factors. If `wᵢ = max(vᵢ, c)` on `U`, then
`1_L dd^c w₁ ∧ ⋯ ∧ dd^c w_p = 1_L dd^c v₁ ∧ ⋯ ∧ dd^c v_p` with
`L = {z ∈ U | vᵢ(z) > c for all i}`. -/
theorem mulBorel_btProduct_max_const {p q : ℕ} (hqp : q + p = n) {U : Opens (ComplexModel n)}
    {v w : Fin p → ComplexModel n → ℝ} (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (hw : ∀ i, IsLocallyBoundedPshOn U (w i)) (c : ℝ)
    (hmax : ∀ i, EqOn (w i) (fun z => max (v i z) c) U) :
    mulBorel (btProduct p q w (oneCurrentOf (U := U) hqp))
        ({z | z ∈ U ∧ ∀ i, c < v i z}.indicator fun _ => (1 : ℝ)) =
      mulBorel (btProduct p q v (oneCurrentOf (U := U) hqp))
        ({z | z ∈ U ∧ ∀ i, c < v i z}.indicator fun _ => (1 : ℝ)) := by
  subst hqp
  set L : Set (ComplexModel (q + p)) := {z | z ∈ U ∧ ∀ i, c < v i z} with hLdef
  have hLm : MeasurableSet L := by
    have e : L = (U : Set (ComplexModel (q + p))) ∩
        ⋂ i, {z | c < (U : Set (ComplexModel (q + p))).indicator (v i) z} := by
      ext z
      simp only [hLdef, mem_ofPred_eq, mem_inter_iff, mem_iInter, SetLike.mem_coe]
      constructor
      · rintro ⟨hz, h⟩
        exact ⟨hz, fun i => by rw [Set.indicator_of_mem hz]; exact h i⟩
      · rintro ⟨hz, h⟩
        exact ⟨hz, fun i => by have := h i; rwa [Set.indicator_of_mem hz] at this⟩
    rw [e]
    exact U.isOpen.measurableSet.inter (MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (measurable_indicator_of_isLocallyBoundedPshOn (hv i)))
  have hgm : Measurable (L.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hLm
  have hgb : IsLocallyBoundedOn (L.indicator fun _ => (1 : ℝ)) U := fun K _ _ =>
    ⟨1, fun x _ => by by_cases hx : x ∈ L <;> simp [hx]⟩
  refine eq_of_wedgeProd _ _ fun β hβ hP φ => ?_
  set C : ℝ := |c| + 1
  have hq0 : ∀ i z, 0 ≤ quadPot (β i) z := fun i z => mul_nonneg Real.pi_pos.le ((hβ i).2 z)
  let ℓ : Fin q → ComplexModel (q + p) → ℝ := fun i z => quadPot (β i) z + C
  have hℓs : ∀ i, ContDiffOn ℝ ∞ (ℓ i) U :=
    fun i => ((contDiff_quadPot _).add contDiff_const).contDiffOn
  have hℓ : ∀ i, IsLocallyBoundedPshOn U (ℓ i) := fun i =>
    LocalBedfordTaylorDecreasing.isLocallyBoundedPshOn_add_const
      (isLocallyBoundedPshOn_quadPot (hβ i) U) C
  have hddc : ∀ i, ∀ x ∈ U, smoothDDC (ℓ i) x = β i := by
    intro i x hx
    rw [smoothDDC_add U.isOpen (contDiff_quadPot _).contDiffOn contDiffOn_const hx,
      GlobalPotentialTransforms.smoothDDC_const, add_zero, smoothDDC_quadPot (hβ i).1 x]
  have hgt : ∀ i z, c < ℓ i z := fun i z => by
    have h1 := hq0 i z
    have h2 : c < C := by
      have := le_abs_self c
      simp only [C]
      linarith
    simp only [ℓ]
    linarith
  have hL : {z | z ∈ U ∧ ∀ i, c < Fin.append ℓ v i z} = L := by
    ext z
    simp only [hLdef, mem_ofPred_eq]
    constructor
    · rintro ⟨hz, h⟩
      exact ⟨hz, fun i => by simpa using h (Fin.natAdd q i)⟩
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun i => ?_⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact hgt j z
      · rw [Fin.append_right]
        exact h j
  have hmax' : ∀ i, EqOn (Fin.append ℓ w i) (fun z => max (Fin.append ℓ v i z) c) U := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro z _
      simp only [Fin.append_left]
      exact (max_eq_left (hgt j z).le).symm
    · intro z hz
      simp only [Fin.append_right]
      exact hmax j hz
  have hloc := MixedNonPluripolar.localMixedBedfordTaylorMeasure_max_const_locality
    (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure
      (isLocallyBoundedPshOn_append hℓ hv))
    (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure
      (isLocallyBoundedPshOn_append hℓ hw)) c hmax'
  rw [hL] at hloc
  rw [mulBorel_btProduct_apply_wedgeProd_of_ddc p q w hw β ℓ hℓs hℓ hddc hP hgm hgb φ,
    mulBorel_btProduct_apply_wedgeProd_of_ddc p q v hv β ℓ hℓs hℓ hddc hP hgm hgb φ]
  have hind : ∀ x, φ x * L.indicator (fun _ => (1 : ℝ)) x = L.indicator (fun y => φ y) x := by
    intro x
    by_cases hx : x ∈ L <;> simp [hx]
  simp only [hind]
  rw [integral_indicator hLm, integral_indicator hLm, hloc]

/-! ### Truncations: consistency of the non-pluripolar construction -/

/-- The common strict locus `O_k = {z ∈ U | φᵢ(z) > -k for all i}` of a tuple of functions
(source `def:npp:L69`). -/
def strictLocus (U : Opens (ComplexModel n)) {p : ℕ} (φ : Fin p → ComplexModel n → EReal)
    (k : ℕ) : Set (ComplexModel n) :=
  {z | z ∈ U ∧ ∀ i, ((-(k : ℝ) : ℝ) : EReal) < φ i z}

theorem strictLocus_eq {U : Opens (ComplexModel n)} {p : ℕ} {φ : Fin p → ComplexModel n → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) {k l : ℕ} (hkl : k ≤ l) :
    strictLocus U φ k = {z | z ∈ U ∧ ∀ i, -(k : ℝ) < truncationReal (φ i) l z} := by
  ext z
  have e (i : Fin p) := strictLocus_eq_truncationReal_superlevel (hφ i) hkl
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun i => ?_⟩
    have hm : z ∈ strictTruncationLocus U (φ i) k := ⟨hz, h i⟩
    rw [e i] at hm
    exact hm.2
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun i => ?_⟩
    have hm : z ∈ {z | z ∈ U ∧ -(k : ℝ) < truncationReal (φ i) l z} := ⟨hz, h i⟩
    rw [← e i] at hm
    exact hm.2

/-- **Consistency of the defining identities of the non-pluripolar product** (source
`def:npp:L69`, FPT q09): for psh `φ₁, …, φ_p` on `U` and `k ≤ l`,
`1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-l)) = 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))`, so that the identities
`1_{O_k} (dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p) = 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))` are compatible. -/
theorem mulBorel_btProduct_truncation_consistent {p q : ℕ} (hqp : q + p = n)
    {U : Opens (ComplexModel n)} {φ : Fin p → ComplexModel n → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) {k l : ℕ} (hkl : k ≤ l) :
    mulBorel (btProduct p q (fun i => truncationReal (φ i) l) (oneCurrentOf (U := U) hqp))
        ((strictLocus U φ k).indicator fun _ => (1 : ℝ)) =
      mulBorel (btProduct p q (fun i => truncationReal (φ i) k) (oneCurrentOf (U := U) hqp))
        ((strictLocus U φ k).indicator fun _ => (1 : ℝ)) := by
  rw [strictLocus_eq hφ hkl]
  exact (mulBorel_btProduct_max_const hqp
    (v := fun i => truncationReal (φ i) l) (w := fun i => truncationReal (φ i) k)
    (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) l)
    (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k) (-(k : ℝ))
    (fun i z hz => (truncationReal_nested (hφ i) hkl hz).symm)).symm

/-- Multiplication by a nonnegative measurable function bounded on the compact subsets of `U`
preserves positivity. -/
theorem isPositive_mulBorel_of_nonneg {U : Opens (ComplexModel n)} {m : ℕ}
    {S : LocalProductCurrent n U m} (hS : IsPositive S) {f : ComplexModel n → ℝ}
    (hf : Measurable f) (hfb : IsLocallyBoundedOn f U) (hf0 : ∀ x, 0 ≤ f x) :
    IsPositive (mulBorel S f) := by
  intro ι _ γ φ hγ
  rw [LocalBedfordTaylorDecreasing.sum_mulBorel_eq_integral_formMeasure hS hγ hf hfb]
  exact integral_nonneg hf0

theorem measurableSet_strictLocus {U : Opens (ComplexModel n)} {p : ℕ}
    {φ : Fin p → ComplexModel n → EReal} (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (k : ℕ) :
    MeasurableSet (strictLocus U φ k) := by
  have e : strictLocus U φ k =
      (U : Set (ComplexModel n)) ∩ ⋂ i, strictTruncationLocus U (φ i) k := by
    ext z
    simp only [strictLocus, strictTruncationLocus, mem_ofPred_eq, mem_inter_iff, mem_iInter,
      SetLike.mem_coe]
    exact ⟨fun h => ⟨h.1, fun i => ⟨h.1, h.2 i⟩⟩, fun h => ⟨h.1, fun i => (h.2 i).2⟩⟩
  rw [e]
  exact U.isOpen.measurableSet.inter
    (MeasurableSet.iInter fun i => measurableSet_strictTruncationLocus (hφ i) k)

theorem strictLocus_mono (U : Opens (ComplexModel n)) {p : ℕ}
    (φ : Fin p → ComplexModel n → EReal) {k l : ℕ} (hkl : k ≤ l) :
    strictLocus U φ k ⊆ strictLocus U φ l := by
  rintro z ⟨hz, h⟩
  refine ⟨hz, fun i => lt_of_le_of_lt ?_ (h i)⟩
  exact EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkl))

/-- The truncated products `1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))` whose increasing limit defines the
non-pluripolar product of degree `p` (source `def:npp:L69`). -/
def truncatedProduct {p q : ℕ} (hqp : q + p = n) (U : Opens (ComplexModel n))
    (φ : Fin p → ComplexModel n → EReal) (k : ℕ) : LocalProductCurrent n U q :=
  mulBorel (btProduct p q (fun i => truncationReal (φ i) k) (oneCurrentOf (U := U) hqp))
    ((strictLocus U φ k).indicator fun _ => (1 : ℝ))

theorem isPositive_truncatedProduct {p q : ℕ} (hqp : q + p = n) {U : Opens (ComplexModel n)}
    {φ : Fin p → ComplexModel n → EReal} (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (k : ℕ) :
    IsPositive (truncatedProduct hqp U φ k) :=
  isPositive_mulBorel_of_nonneg (isPositive_btProduct p q _ _ (isPositive_oneCurrentOf hqp)
      (isClosedAny_oneCurrentOf hqp) fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k).1
    (measurable_const.indicator (measurableSet_strictLocus hφ k))
    (fun K _ _ => ⟨1, fun x _ => by by_cases hx : x ∈ strictLocus U φ k <;> simp [hx]⟩)
    (fun x => by by_cases hx : x ∈ strictLocus U φ k <;> simp [hx])

/-- **The truncated products increase**: for `k ≤ l`,
`1_{O_l} ⋀ⱼ dd^c (φⱼ ∨ (-l)) - 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))` is a positive current. -/
theorem isPositive_truncatedProduct_sub {p q : ℕ} (hqp : q + p = n)
    {U : Opens (ComplexModel n)} {φ : Fin p → ComplexModel n → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) {k l : ℕ} (hkl : k ≤ l) :
    IsPositive (truncatedProduct hqp U φ l - truncatedProduct hqp U φ k) := by
  have hB := (isPositive_btProduct p q (fun i => truncationReal (φ i) l)
    (oneCurrentOf (U := U) hqp) (isPositive_oneCurrentOf hqp) (isClosedAny_oneCurrentOf hqp)
    fun i => truncationReal_isLocallyBoundedPshOn (hφ i) l).1
  have hk := measurableSet_strictLocus hφ k
  have hl := measurableSet_strictLocus hφ l
  have hbd : ∀ A : Set (ComplexModel n), IsLocallyBoundedOn (A.indicator fun _ => (1 : ℝ)) U :=
    fun A K _ _ => ⟨1, fun x _ => by by_cases hx : x ∈ A <;> simp [hx]⟩
  have hsplit : (strictLocus U φ l).indicator (fun _ => (1 : ℝ)) =
      (strictLocus U φ k).indicator (fun _ => (1 : ℝ)) +
        (strictLocus U φ l \ strictLocus U φ k).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hxk : x ∈ strictLocus U φ k
    · have hxl := strictLocus_mono U φ hkl hxk
      simp [hxk, hxl]
    · by_cases hxl : x ∈ strictLocus U φ l <;> simp [hxk, hxl]
  have e : truncatedProduct hqp U φ l - truncatedProduct hqp U φ k =
      mulBorel (btProduct p q (fun i => truncationReal (φ i) l) (oneCurrentOf (U := U) hqp))
        ((strictLocus U φ l \ strictLocus U φ k).indicator fun _ => (1 : ℝ)) := by
    unfold truncatedProduct
    rw [← mulBorel_btProduct_truncation_consistent hqp hφ hkl, hsplit,
      mulBorel_add hB (measurable_const.indicator hk) (hbd _)
        (measurable_const.indicator (hl.diff hk)) (hbd _), add_sub_cancel_left]
  rw [e]
  exact isPositive_mulBorel_of_nonneg hB (measurable_const.indicator (hl.diff hk)) (hbd _)
    (fun x => by by_cases hx : x ∈ strictLocus U φ l \ strictLocus U φ k <;> simp [hx])

end SGPT.NPP.BedfordTaylorTopDegree
