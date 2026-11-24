/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.BedfordTaylorManifold
public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentBiholomorphic

/-!
# The non-pluripolar product of arbitrary degree on a complex manifold

Source: `chapter_npp.tex`, `def:npp:L69`, `prop:npp1` (1)–(3), (5); Xia, *Foundations of
pluripotential theory*, `def:nonpluripolar-product` and the paragraphs after
`prop:nonpluripolar-local-calculus` ("We say that the non-pluripolar product … is locally finite
if this holds near every point; the local products then glue to a positive current on `X`").

`M` is a complex manifold of dimension `n` (mathlib's holomorphic atlas, as in
`SGPT.NPP.BedfordTaylorManifold`); currents on `M` are compatible chart families
(`SGPT.NPP.PositiveCurrent`).  For psh functions `φ₁, …, φ_p` on `M` (`SGPT.PSH.ManifoldPSH`,
the verified `def:pshmfd`) and `q + p = n`:

* `IsNonPluripolarWellDefined hqp φ` — the source condition `eq:welldefinepluri` in coordinates:
  in every atlas chart `e`, for every connected open set `V` of the coordinate domain, every
  smooth semipositive `(1,1)`-form `ω` on `V` and every compact `K ⊆ V`,
  `sup_k ∫_{K ∩ O_k} (⋀ⱼ dd^c (φⱼ ∨ (-k)))|_V ∧ ω^{n-p} < ∞`
  (`NonPluripolarCurrent.IsWellDefinedOn`);
  `isNonPluripolarWellDefined_of_local` shows that it suffices to check it in one chart around
  every point (the condition is local and invariant under coordinate changes);
* `nonPluripolarProduct hqp φ hφ hW` — the non-pluripolar product as a positive current of
  bidimension `(q,q)` (bidegree `(p,p)`) on `M`: in every chart, the local product of the
  coordinate expressions (`NonPluripolarCurrent.nonPluripolarProduct`, the weak limit of the
  truncated products, characterized by `1_{O_k} ⟨⋯⟩ = 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))` and extension
  by zero); the chart expressions are compatible by restriction to open sets and biholomorphic
  invariance (`NonPluripolarCurrent.pullback_nonPluripolarProduct`);
* `nonPluripolarProduct_inChart_strictLocus`, `nonPluripolarProduct_inChart_compl`,
  `weakTendsto_truncatedProduct_inChart` — the defining properties in every chart;
* `nonPluripolarProduct_comp_perm` — symmetry (`prop:npp1` (2), the ordering);
* `isNonPluripolarWellDefined_of_isLocallyBoundedPSH`, `nonPluripolarProduct_eq_bedfordTaylor` —
  for locally bounded potentials the product is well defined and is the Bedford–Taylor product
  `SGPT.NPP.bedfordTaylor` (`prop:npp1` (3), first sentence);
* `isClosed_nonPluripolarProduct_top` — in top degree (`p = n`) the product is a closed positive
  current (`prop:npp1` (5) for `p = n`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.NPP

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
open SGPT.NPP.NonPluripolarCurrent

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

variable {p q : ℕ} (hqp : q + p = n)

/-- The coordinate expressions of psh functions on `M` are psh on the chart domains. -/
theorem chartPlurisubharmonicOn {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (e : ComplexChart n M) (i : Fin p) :
    SGPT.Foundations.Analysis.PlurisubharmonicOn (fun z => φ i (e.val.symm z)) (chartTarget e) :=
  (hφ i).chartPlurisubharmonic e

/-- **Well-definedness of `dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p`** (source `def:npp:L69`,
`eq:welldefinepluri`), in coordinates: in every atlas chart `e`, the local condition
`NonPluripolarCurrent.IsWellDefinedOn` for the coordinate expressions `φᵢ ∘ e⁻¹` on the
coordinate domain (all connected open `V`, smooth semipositive `(1,1)`-forms `ω` on `V`, compact
`K ⊆ V`). -/
def IsNonPluripolarWellDefined (φ : Fin p → M → EReal) : Prop :=
  ∀ e : ComplexChart n M,
    NonPluripolarCurrent.IsWellDefinedOn hqp (chartTarget e) fun i z => φ i (e.val.symm z)

/-- On an overlap, the well-definedness and the product in the chart `e` are obtained from those in
the chart `f` by restriction and pull-back along the coordinate change. -/
theorem nonPluripolarProduct_overlap {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (e f : ComplexChart n M)
    (hWf : NonPluripolarCurrent.IsWellDefinedOn hqp (chartTarget f)
      fun i z => φ i (f.val.symm z)) :
    NonPluripolarCurrent.IsWellDefinedOn hqp (overlapSource e f)
        (fun i z => φ i (e.val.symm z)) ∧
      pullback (chartTransition_isBiholomorphicPair e f)
          (isPositive_restrict (isPositive_nonPluripolarProduct hqp
            (chartPlurisubharmonicOn hφ f) hWf) (overlapTarget_le e f)) =
        NonPluripolarCurrent.nonPluripolarProduct hqp (overlapSource e f)
          (fun i z => φ i (e.val.symm z)) := by
  have hh := chartTransition_isBiholomorphicPair e f
  have hφf := chartPlurisubharmonicOn hφ f
  have hφB : ∀ i, SGPT.Foundations.Analysis.PlurisubharmonicOn (fun z => φ i (f.val.symm z))
      (overlapTarget e f) := fun i => (hφf i).mono (overlapTarget_le e f)
  have hWB := isWellDefinedOn_restrict hqp hφf hWf (overlapTarget_le e f)
  have e1 := restrict_nonPluripolarProduct hqp hφf hWf (overlapTarget_le e f)
  have hpb := pullback_nonPluripolarProduct hqp hh hφB hWB
  have hcongr : ∀ i, ∀ x ∈ overlapSource e f,
      φ i (e.val.symm x) = φ i (f.val.symm (chartTransition e f x)) := by
    intro i x hx
    have hx' : x ∈ (chartTransition e f).source := hx
    have hxf : e.val.symm x ∈ f.val.source := by
      simp only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hx'
      exact hx'.2
    simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      f.val.left_inv hxf]
  have hc := nonPluripolarProduct_congr hqp (U := overlapSource e f) hcongr
  refine ⟨hc.1.mpr hpb.1, ?_⟩
  rw [pullback_congr_current hh _ (isPositive_nonPluripolarProduct hqp hφB hWB) e1, hpb.2,
    hc.2]

/-- **The non-pluripolar product** `⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩` of psh functions on the complex
manifold `M` (source `def:npp:L69`), when well defined: the positive current of bidimension
`(q,q)`, `q + p = n`, whose expression in every chart is the local non-pluripolar product of the
coordinate expressions. -/
def nonPluripolarProduct (φ : Fin p → M → EReal)
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (hW : IsNonPluripolarWellDefined hqp φ) :
    PositiveCurrent n M q where
  inChart e := NonPluripolarCurrent.nonPluripolarProduct hqp (chartTarget e)
    fun i z => φ i (e.val.symm z)
  isPositive e := isPositive_nonPluripolarProduct hqp (chartPlurisubharmonicOn hφ e) (hW e)
  compatible e f := by
    rw [restrict_nonPluripolarProduct hqp (chartPlurisubharmonicOn hφ e) (hW e)
      (overlapSource_le e f)]
    exact (nonPluripolarProduct_overlap hqp hφ e f (hW f)).2.symm

variable {φ : Fin p → M → EReal}

@[simp] theorem nonPluripolarProduct_inChart (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hW : IsNonPluripolarWellDefined hqp φ) (e : ComplexChart n M) :
    (nonPluripolarProduct hqp φ hφ hW).inChart e =
      NonPluripolarCurrent.nonPluripolarProduct hqp (chartTarget e)
        (fun i z => φ i (e.val.symm z)) := rfl

/-- **The defining identity** `eq:npp` in every chart:
`1_{O_k} ⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩ = 1_{O_k} ⋀ⱼ dd^c (φⱼ ∨ (-k))`. -/
theorem nonPluripolarProduct_inChart_strictLocus
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (hW : IsNonPluripolarWellDefined hqp φ)
    (e : ComplexChart n M) (k : ℕ) :
    mulBorel ((nonPluripolarProduct hqp φ hφ hW).inChart e)
        ((BedfordTaylorTopDegree.strictLocus (chartTarget e)
          (fun i z => φ i (e.val.symm z)) k).indicator fun _ => (1 : ℝ)) =
      BedfordTaylorTopDegree.truncatedProduct hqp (chartTarget e)
        (fun i z => φ i (e.val.symm z)) k :=
  mulBorel_nonPluripolarProduct_strictLocus hqp (chartPlurisubharmonicOn hφ e) (hW e) k

/-- **Extension by zero** in every chart: the product vanishes off `⋃ₖ O_k`. -/
theorem nonPluripolarProduct_inChart_compl
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (hW : IsNonPluripolarWellDefined hqp φ)
    (e : ComplexChart n M) :
    mulBorel ((nonPluripolarProduct hqp φ hφ hW).inChart e)
        ((⋃ k, BedfordTaylorTopDegree.strictLocus (chartTarget e)
          (fun i z => φ i (e.val.symm z)) k)ᶜ.indicator fun _ => (1 : ℝ)) = 0 :=
  mulBorel_nonPluripolarProduct_compl hqp (chartPlurisubharmonicOn hφ e) (hW e)

/-- In every chart the product is the weak limit of the truncated products. -/
theorem weakTendsto_truncatedProduct_inChart
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (hW : IsNonPluripolarWellDefined hqp φ)
    (e : ComplexChart n M) :
    LocalBedfordTaylorContinuity.WeakTendsto
      (BedfordTaylorTopDegree.truncatedProduct hqp (chartTarget e)
        (fun i z => φ i (e.val.symm z)))
      ((nonPluripolarProduct hqp φ hφ hW).inChart e) :=
  weakTendsto_truncatedProduct hqp (chartPlurisubharmonicOn hφ e) (hW e)

/-- **The well-definedness condition is local and coordinate independent**: it holds as soon as
every point has an atlas chart in which the local condition holds. -/
theorem isNonPluripolarWellDefined_of_local (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (h : ∀ x : M, ∃ e : ComplexChart n M, x ∈ e.val.source ∧
      NonPluripolarCurrent.IsWellDefinedOn hqp (chartTarget e) fun i z => φ i (e.val.symm z)) :
    IsNonPluripolarWellDefined hqp φ := by
  intro f
  choose e he hWe using h
  refine isWellDefinedOn_of_cover hqp (chartPlurisubharmonicOn hφ f)
    (fun z : chartTarget f => overlapSource f (e (f.val.symm z)))
    (fun z => overlapSource_le f _) (fun z hz => ?_)
    (fun z => (nonPluripolarProduct_overlap hqp hφ f _ (hWe _)).1)
  refine mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
  have hz' : z ∈ f.val.target := hz
  change z ∈ (chartTransition f (e (f.val.symm z))).source
  simp only [chartTransition, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
  exact ⟨hz', he _⟩

/-- **Symmetry** (`prop:npp1` (2), the ordering of the factors). -/
theorem nonPluripolarProduct_comp_perm (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hW : IsNonPluripolarWellDefined hqp φ) (σ : Equiv.Perm (Fin p)) :
    ∃ hW' : IsNonPluripolarWellDefined hqp (φ ∘ σ),
      nonPluripolarProduct hqp (φ ∘ σ) (fun i => hφ (σ i)) hW' =
        nonPluripolarProduct hqp φ hφ hW := by
  have h := fun e : ComplexChart n M => NonPluripolarCurrent.nonPluripolarProduct_comp_perm hqp
    (φ := fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) σ
  refine ⟨fun e => (h e).1.mpr (hW e), ?_⟩
  ext1 e
  exact (h e).2

/-- **Locally bounded potentials** (`prop:npp1` (3), first sentence): the non-pluripolar product
of locally bounded psh functions on `M` is well defined. -/
theorem isNonPluripolarWellDefined_of_isLocallyBoundedPSH {u : Fin p → M → ℝ}
    (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) :
    IsNonPluripolarWellDefined hqp (fun i x => (u i x : EReal)) := fun e =>
  isWellDefinedOn_of_isLocallyBoundedPshOn hqp (u := fun i z => u i (e.val.symm z))
    fun i => (hu i).chart e

/-- **The non-pluripolar product of locally bounded psh functions is their Bedford–Taylor
product** (`prop:npp1` (3), first sentence; `def:npp:L22`). -/
theorem nonPluripolarProduct_eq_bedfordTaylor {u : Fin p → M → ℝ}
    (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i))
    (hW : IsNonPluripolarWellDefined hqp (fun i x => (u i x : EReal))) :
    nonPluripolarProduct hqp (fun i x => (u i x : EReal)) (fun i => (hu i).1) hW =
      bedfordTaylor hqp u hu := by
  ext1 e
  exact nonPluripolarProduct_of_isLocallyBoundedPshOn hqp (u := fun i z => u i (e.val.symm z))
    fun i => (hu i).chart e

/-- **In top degree the product is a closed positive current** (`prop:npp1` (5) for `p = n`;
positivity is part of `PositiveCurrent`). -/
theorem isClosed_nonPluripolarProduct_top {φ : Fin n → M → EReal} (h0 : 0 + n = n)
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (hW : IsNonPluripolarWellDefined h0 φ) :
    (nonPluripolarProduct h0 φ hφ hW).IsClosed := fun _ => trivial

end SGPT.NPP
