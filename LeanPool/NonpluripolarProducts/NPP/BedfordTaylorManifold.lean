/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.Manifold
public import LeanPool.NonpluripolarProducts.NPP.BedfordTaylorTopDegree
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorBiholomorphicProducts
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

/-!
# Bedford–Taylor products of arbitrary degree on a complex manifold

Source: `chapter_npp.tex`, `def:npp:L22`, `prop:npp:L40`, `thm:contMA`;
Xia, *Foundations of pluripotential theory*, `def:bedford-taylor-product`,
`prop:bt-positive-recursion` (5) and its last paragraph ("products … on a complex manifold can
be computed in holomorphic charts: the products defined in two charts agree on their overlap"),
`thm:bt-decreasing-continuity`, `thm:bt-increasing-continuity`.

## Currents on a complex manifold

`M` is a complex manifold of dimension `n` (mathlib's holomorphic atlas: a charted space modelled
on `ℂⁿ` with holomorphic transition maps; no Hausdorff, countability or compactness assumption is
needed below).  A *positive current of bidimension `(q,q)`* on `M` (bidegree `(n-q,n-q)`) is
recorded by its local expressions in all atlas charts (`PositiveCurrent`):

* in a chart `e` it is a positive current of bidimension `(q,q)` on the open coordinate domain
  `chartTarget e ⊆ ℂⁿ`, in the sense of `SGPT.Foundations.Analysis.Pending.LocalProductCurrents`
  (`T(γ)(φ) = ⟨T, φ γ⟩` for constant real `(q,q)`-forms `γ` and test functions `φ`, positivity =
  weak positivity on all variable strongly positive test forms);
* the local expressions are **compatible**: on every overlap, the expression in `e` is the
  pull-back, along the holomorphic coordinate change `f ∘ e⁻¹`, of the expression in `f`
  (`LocalCurrentPullback.pullback`, `⟨τ^* T, φ γ⟩ = ⟨T, σ^*(φ γ)⟩`).

This is the usual description of a current on a manifold through its restrictions to coordinate
charts.  Closedness (`PositiveCurrent.IsClosed`) and weak convergence
(`PositiveCurrent.WeakTendsto`) are tested in every chart; since every test form is a finite sum of
test forms supported in coordinate charts (partition of unity), chartwise weak convergence is weak
convergence of currents on `M`.

## The Bedford–Taylor product

For locally bounded psh functions `u₁, …, u_p` on `M` (`IsLocallyBoundedPSH`: psh in the sense of
the verified `def:pshmfd`, `SGPT.PSH.ManifoldPSH`, real valued and bounded near every point) the
product `dd^c u₁ ∧ ⋯ ∧ dd^c u_p` is the positive current of bidimension `(q,q)`, `q + p = n`, whose
expression in a chart `e` is the recursive local product
`B(u₁ ∘ e⁻¹, …, u_p ∘ e⁻¹; [chartTarget e])` of `LocalBedfordTaylorProducts.btProduct`
(`bedfordTaylor`).  The local expressions are compatible by the biholomorphic invariance of the
local products (`LocalBedfordTaylorBiholomorphicProducts.pullback_btProduct`, FPT
`prop:bt-positive-recursion` (5)) and their locality on open sets.  The two clauses of the source
induction hold literally in every chart: the product with no factor is the current of integration
`[M]` (`bedfordTaylorInChart_zero`), and
`dd^c u₁ ∧ ⋯ ∧ dd^c u_{p+1} = dd^c (u₁ · dd^c u₂ ∧ ⋯ ∧ dd^c u_{p+1})`
(`bedfordTaylorInChart_succ`; `ddcMul S w = dd^c (w S)`, the multiplication of the coefficient
measures of the positive current `S` by the locally bounded Borel function `w`).

Normalization: `dd^c = (i/2π) ∂∂bar` (`FirstPass.MongeAmpere`, `LocalBedfordTaylorProducts.ddc`),
as in the source (`chapter_pshfunctions.tex`, `dd^c = i/(2π) ∂∂bar`).  A `(p,p)`-current with
`p > n` is zero; the products below are therefore stated for `p ≤ n`, with bidimension
`q = n - p` given by an explicit `q + p = n`.

## Main results

* `chartTransition_isBiholomorphicPair` — atlas coordinate changes are biholomorphisms between
  the two expressions of the overlap.
* `PositiveCurrent`, `PositiveCurrent.IsClosed`, `PositiveCurrent.WeakTendsto`.
* `IsLocallyBoundedPSH`, `IsLocallyBoundedPSH.chart`.
* `bedfordTaylor` (`def:npp:L22`) with `bedfordTaylorInChart_zero`, `bedfordTaylorInChart_succ`.
* `isClosed_bedfordTaylor`, `bedfordTaylor_comp_perm` (`prop:npp:L40`).
* `weakTendsto_bedfordTaylor_of_antitone`, `weakTendsto_weightedBedfordTaylorInChart_of_antitone`
  (`thm:contMA`, decreasing sequences).
* `TendstoAE`, `weakTendsto_bedfordTaylor_of_monotone`,
  `weakTendsto_weightedBedfordTaylorInChart_of_monotone` (`thm:contMA`, increasing sequences
  converging almost everywhere; through the reduction to top degree of
  `SGPT.NPP.BedfordTaylorTopDegree`).
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
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-! ### Coordinate changes -/

section Transition

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

theorem chartTransition_mem_contDiffGroupoid (e f : ComplexChart n M) :
    chartTransition e f ∈ contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel n)) :=
  StructureGroupoid.compatible _ e.property f.property

/-- The coordinate change `f ∘ e⁻¹` is holomorphic on its overlap. -/
theorem contDiffOn_chartTransition (e f : ComplexChart n M) :
    ContDiffOn ℂ ∞ (chartTransition e f) (chartTransition e f).source :=
  contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_of_mem_contDiffGroupoid (chartTransition_mem_contDiffGroupoid e f))

/-- The inverse coordinate change is holomorphic on the overlap in `f`-coordinates. -/
theorem contDiffOn_chartTransition_symm (e f : ComplexChart n M) :
    ContDiffOn ℂ ∞ (chartTransition e f).symm (chartTransition e f).target := by
  have h := (contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel n))).symm
    (chartTransition_mem_contDiffGroupoid e f)
  have h' := contMDiffOn_iff_contDiffOn.mp (contMDiffOn_of_mem_contDiffGroupoid h)
  simpa only [OpenPartialHomeomorph.symm_source] using h'

/-- **Atlas coordinate changes are biholomorphisms** between the two coordinate expressions of an
overlap (only the holomorphic atlas is used). -/
theorem chartTransition_isBiholomorphicPair (e f : ComplexChart n M) :
    IsBiholomorphicPair (overlapSource e f) (overlapTarget e f)
      (chartTransition e f) (chartTransition e f).symm where
  holo := contDiffOn_chartTransition e f
  holo_inv := contDiffOn_chartTransition_symm e f
  mapsTo := fun _ hx => (chartTransition e f).map_source hx
  mapsTo_inv := fun _ hy => (chartTransition e f).map_target hy
  left_inv := fun _ hx => (chartTransition e f).left_inv hx
  right_inv := fun _ hy => (chartTransition e f).right_inv hy

end Transition

/-! ### Positive currents on the manifold -/

section Currents

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

variable (n M) in
/-- **A positive current of bidimension `(q,q)` on `M`** (bidegree `(n-q, n-q)`), given by its
expressions in all atlas charts: positive currents on the coordinate domains which agree on every
overlap, the expression in `e` being the pull-back of the expression in `f` along the coordinate
change `f ∘ e⁻¹`. -/
structure PositiveCurrent (q : ℕ) where
  /-- The coordinate expression in the chart `e`. -/
  inChart : (e : ComplexChart n M) → LocalProductCurrent n (chartTarget e) q
  /-- Every coordinate expression is a positive current. -/
  isPositive : ∀ e, IsPositive (inChart e)
  /-- Compatibility on overlaps. -/
  compatible : ∀ e f : ComplexChart n M,
    restrict (overlapSource_le e f) (inChart e) =
      pullback (chartTransition_isBiholomorphicPair e f)
        (isPositive_restrict (isPositive f) (overlapTarget_le e f))

namespace PositiveCurrent

variable {q : ℕ}

@[ext] theorem ext {S T : PositiveCurrent n M q} (h : ∀ e, S.inChart e = T.inChart e) :
    S = T := by
  cases S
  cases T
  congr
  funext e
  exact h e

/-- A current on `M` is closed when all its coordinate expressions are closed. -/
def IsClosed (T : PositiveCurrent n M q) : Prop :=
  ∀ e, IsClosedAny q (T.inChart e)

/-- Weak convergence of currents on `M`: convergence of the coordinate expressions against every
constant form and every test function, in every chart. -/
def WeakTendsto (T : ℕ → PositiveCurrent n M q) (T₀ : PositiveCurrent n M q) : Prop :=
  ∀ e, LocalBedfordTaylorContinuity.WeakTendsto (fun k => (T k).inChart e) (T₀.inChart e)

end PositiveCurrent

end Currents

/-! ### Locally bounded psh functions -/

section Psh

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

/-- A locally bounded plurisubharmonic function on `M`: psh in the sense of `def:pshmfd`
(`SGPT.PSH.ManifoldPSH`), real valued, and bounded on a neighbourhood of every point. -/
def IsLocallyBoundedPSH (u : M → ℝ) : Prop :=
  SGPT.PSH.ManifoldPSH (n := n) (fun x => (u x : EReal)) ∧
    ∀ x : M, ∃ V ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ V, |u y| ≤ C

/-- In every chart a locally bounded psh function is locally bounded psh on the coordinate
domain. -/
theorem IsLocallyBoundedPSH.chart {u : M → ℝ} (hu : IsLocallyBoundedPSH (n := n) u)
    (e : ComplexChart n M) :
    MongeAmpere.IsLocallyBoundedPshOn (chartTarget e) (fun z => u (e.val.symm z)) := by
  refine ⟨hu.1.chartPlurisubharmonic e, fun z hz => ?_⟩
  obtain ⟨V, hV, C, hC⟩ := hu.2 (e.val.symm z)
  have hz' : z ∈ e.val.target := hz
  have hpre : e.val.symm ⁻¹' V ∩ e.val.target ∈ 𝓝 z :=
    inter_mem ((e.val.continuousAt_symm hz').preimage_mem_nhds hV)
      (e.val.open_target.mem_nhds hz')
  obtain ⟨t, hts, hto, hzt⟩ := mem_nhds_iff.mp hpre
  exact ⟨⟨t, hto⟩, hzt, fun w hw => (hts hw).2, C, fun w hw => hC _ (hts hw).1⟩

end Psh

/-! ### The Bedford–Taylor product -/

section Product

variable [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

private theorem restrict_oneCurrentOf {U V : Opens (ComplexModel n)} (hVU : V ≤ U) {k : ℕ}
    (hk : k = n) : restrict hVU (oneCurrentOf (U := U) hk) = oneCurrentOf (U := V) hk := by
  subst hk
  exact LocalCurrentPullbackDdc.restrict_oneCurrent hVU

private theorem pullback_eq_of_eq {A B : Opens (ComplexModel n)}
    {τ σ : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B τ σ) {s : ℕ}
    {T T' : LocalProductCurrent n B s} (hT : IsPositive T) (hT' : IsPositive T') (e : T = T') :
    pullback h hT = pullback h hT' := by
  subst e
  rfl

variable {q p : ℕ}

/-- The coordinate expression in the chart `e` of `dd^c u₁ ∧ ⋯ ∧ dd^c u_p`: the recursive local
Bedford–Taylor product of the coordinate expressions `uᵢ ∘ e⁻¹`, against the current of
integration `[chartTarget e]`. -/
def bedfordTaylorInChart (hqp : q + p = n) (u : Fin p → M → ℝ) (e : ComplexChart n M) :
    LocalProductCurrent n (chartTarget e) q :=
  btProduct p q (fun i z => u i (e.val.symm z)) (oneCurrentOf (U := chartTarget e) hqp)

theorem isPositive_bedfordTaylorInChart (hqp : q + p = n) {u : Fin p → M → ℝ}
    (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) (e : ComplexChart n M) :
    IsPositive (bedfordTaylorInChart hqp u e) ∧ IsClosedAny q (bedfordTaylorInChart hqp u e) :=
  isPositive_btProduct p q _ _ (isPositive_oneCurrentOf hqp) (isClosedAny_oneCurrentOf hqp)
    fun i => (hu i).chart e

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- **`def:npp:L22`, case `p = 0`**: the product with no factor is the current of integration
`[M]` (in every chart, `[chartTarget e]`, integration of top-degree forms). -/
theorem bedfordTaylorInChart_zero (hqp : q + 0 = n) (u : Fin 0 → M → ℝ) (e : ComplexChart n M) :
    bedfordTaylorInChart hqp u e = oneCurrentOf (U := chartTarget e) hqp := rfl

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- **`def:npp:L22`, the inductive step**:
`dd^c u₁ ∧ ⋯ ∧ dd^c u_{p+1} = dd^c (u₁ · (dd^c u₂ ∧ ⋯ ∧ dd^c u_{p+1}))` in every chart, where
`ddcMul S w = dd^c (w S)` multiplies the coefficient measures of the positive current `S` by the
locally bounded Borel function `w` (extended by zero off the chart) and applies `dd^c`. -/
theorem bedfordTaylorInChart_succ (hqp : q + (p + 1) = n) (u : Fin (p + 1) → M → ℝ)
    (e : ComplexChart n M) :
    bedfordTaylorInChart hqp u e =
      ddcMul (bedfordTaylorInChart (q := q + 1) (p := p) (by omega) (Fin.tail u) e)
        (fun z => u 0 (e.val.symm z)) :=
  LocalBedfordTaylorCollar.btProduct_succ_eq_ddcMul p q _ _ _
    (BedfordTaylorTopDegree.heq_oneCurrentOf _ _)

/-- On an overlap, the coordinate expression of the product in `e` is the pull-back of its
expression in `f`. -/
theorem bedfordTaylorInChart_compatible (hqp : q + p = n) {u : Fin p → M → ℝ}
    (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) (e f : ComplexChart n M) :
    restrict (overlapSource_le e f) (bedfordTaylorInChart hqp u e) =
      pullback (chartTransition_isBiholomorphicPair e f)
        (isPositive_restrict (isPositive_bedfordTaylorInChart hqp hu f).1
          (overlapTarget_le e f)) := by
  set A := overlapSource e f
  set B := overlapTarget e f
  have hAe : A ≤ chartTarget e := overlapSource_le e f
  have hBf : B ≤ chartTarget f := overlapTarget_le e f
  have hue : ∀ i, MongeAmpere.IsLocallyBoundedPshOn (chartTarget e)
      (fun z => u i (e.val.symm z)) := fun i => (hu i).chart e
  have huf : ∀ i, MongeAmpere.IsLocallyBoundedPshOn (chartTarget f)
      (fun z => u i (f.val.symm z)) := fun i => (hu i).chart f
  have huB : ∀ i, MongeAmpere.IsLocallyBoundedPshOn B (fun z => u i (f.val.symm z)) :=
    fun i => isLocallyBoundedPshOn_mono (huf i) hBf
  -- the expression in `e`, restricted to the overlap
  have eA : restrict hAe (bedfordTaylorInChart hqp u e) =
      btProduct p q (fun i z => u i (e.val.symm z)) (oneCurrentOf (U := A) hqp) := by
    rw [bedfordTaylorInChart, ← btProduct_restrict hAe p q _ _ (isPositive_oneCurrentOf hqp)
      (isClosedAny_oneCurrentOf hqp) hue, restrict_oneCurrentOf]
  -- the expression in `f`, restricted to the overlap
  have eB : restrict hBf (bedfordTaylorInChart hqp u f) =
      btProduct p q (fun i z => u i (f.val.symm z)) (oneCurrentOf (U := B) hqp) := by
    rw [bedfordTaylorInChart, ← btProduct_restrict hBf p q _ _ (isPositive_oneCurrentOf hqp)
      (isClosedAny_oneCurrentOf hqp) huf, restrict_oneCurrentOf]
  rw [eA, pullback_eq_of_eq (chartTransition_isBiholomorphicPair e f) _
      (isPositive_btProduct p q _ _ (isPositive_oneCurrentOf hqp)
        (isClosedAny_oneCurrentOf hqp) huB).1 eB,
    LocalBedfordTaylorBiholomorphicProducts.pullback_btProduct hqp
      (chartTransition_isBiholomorphicPair e f) huB]
  refine LocalBedfordTaylorDecreasing.btProduct_congr p q _ _ _ fun i x hx => ?_
  exact chart_comp_transition (u i) e f x hx

/-- **The Bedford–Taylor product** `dd^c u₁ ∧ ⋯ ∧ dd^c u_p` of locally bounded psh functions on
the complex manifold `M` (source `def:npp:L22`), a positive current of bidimension `(q,q)`, i.e.
of bidegree `(p,p)`, `q + p = n`: in every chart, the recursive local Bedford–Taylor product
(`bedfordTaylorInChart_zero`, `bedfordTaylorInChart_succ`). -/
def bedfordTaylor (hqp : q + p = n) (u : Fin p → M → ℝ)
    (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) : PositiveCurrent n M q where
  inChart := bedfordTaylorInChart hqp u
  isPositive e := (isPositive_bedfordTaylorInChart hqp hu e).1
  compatible := bedfordTaylorInChart_compatible hqp hu

@[simp] theorem bedfordTaylor_inChart (hqp : q + p = n) (u : Fin p → M → ℝ)
    (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) (e : ComplexChart n M) :
    (bedfordTaylor hqp u hu).inChart e = bedfordTaylorInChart hqp u e := rfl

/-- **`prop:npp:L40`, closedness**: the Bedford–Taylor product is a closed positive current
(positivity is part of `PositiveCurrent`). -/
theorem isClosed_bedfordTaylor (hqp : q + p = n) (u : Fin p → M → ℝ)
    (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) : (bedfordTaylor hqp u hu).IsClosed :=
  fun e => (isPositive_bedfordTaylorInChart hqp hu e).2

/-- **`prop:npp:L40`, symmetry**: the product does not depend on the order of the factors. -/
theorem bedfordTaylor_comp_perm (hqp : q + p = n) (u : Fin p → M → ℝ)
    (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) (σ : Equiv.Perm (Fin p)) :
    bedfordTaylor hqp (u ∘ σ) (fun i => hu (σ i)) = bedfordTaylor hqp u hu := by
  ext1 e
  exact LocalBedfordTaylorCalculus.btProduct_comp_perm p q _ (isPositive_oneCurrentOf hqp)
    (isClosedAny_oneCurrentOf hqp) (fun i z => u i (e.val.symm z)) (fun i => (hu i).chart e) σ

/-! ### Decreasing continuity (`thm:contMA`) -/

/-- **`thm:contMA`, decreasing sequences, unweighted form**: if `u_i^k ↓ u_i` pointwise, with all
functions locally bounded psh, then `dd^c u_1^k ∧ ⋯ ∧ dd^c u_p^k → dd^c u_1 ∧ ⋯ ∧ dd^c u_p`
weakly as currents on `M`. -/
theorem weakTendsto_bedfordTaylor_of_antitone (hqp : q + p = n) (u : ℕ → Fin p → M → ℝ)
    (u₀ : Fin p → M → ℝ) (hu : ∀ k i, IsLocallyBoundedPSH (n := n) (u k i))
    (hu₀ : ∀ i, IsLocallyBoundedPSH (n := n) (u₀ i))
    (hanti : ∀ i x, Antitone fun k => u k i x)
    (hlim : ∀ i x, Tendsto (fun k => u k i x) atTop (𝓝 (u₀ i x))) :
    PositiveCurrent.WeakTendsto (fun k => bedfordTaylor hqp (u k) (hu k))
      (bedfordTaylor hqp u₀ hu₀) := fun e =>
  LocalBedfordTaylorDecreasing.weakTendsto_btProduct_of_antitone p q _
    (isPositive_oneCurrentOf hqp) (isClosedAny_oneCurrentOf hqp)
    (fun k i z => u k i (e.val.symm z)) (fun i z => u₀ i (e.val.symm z))
    (fun k i => (hu k i).chart e) (fun i => (hu₀ i).chart e)
    (fun i z _ => hanti i (e.val.symm z)) (fun i z _ => hlim i (e.val.symm z))

/-- The coordinate expression in the chart `e` of the weighted product
`u₀ dd^c u₁ ∧ ⋯ ∧ dd^c u_p` (the coefficient measures of the positive current
`dd^c u₁ ∧ ⋯ ∧ dd^c u_p` multiplied by the locally bounded Borel function `u₀`). -/
def weightedBedfordTaylorInChart (hqp : q + p = n) (u : Fin (p + 1) → M → ℝ)
    (e : ComplexChart n M) : LocalProductCurrent n (chartTarget e) q :=
  mulBorel (bedfordTaylorInChart hqp (Fin.tail u) e)
    ((chartTarget e : Set (ComplexModel n)).indicator fun z => u 0 (e.val.symm z))

/-- **`thm:contMA`, decreasing sequences, weighted form**: if `u_i^k ↓ u_i` pointwise for
`i = 0, …, p`, with all functions locally bounded psh, then
`u_0^k dd^c u_1^k ∧ ⋯ ∧ dd^c u_p^k → u_0 dd^c u_1 ∧ ⋯ ∧ dd^c u_p` weakly, in every chart. -/
theorem weakTendsto_weightedBedfordTaylorInChart_of_antitone (hqp : q + p = n)
    (u : ℕ → Fin (p + 1) → M → ℝ) (u₀ : Fin (p + 1) → M → ℝ)
    (hu : ∀ k i, IsLocallyBoundedPSH (n := n) (u k i))
    (hu₀ : ∀ i, IsLocallyBoundedPSH (n := n) (u₀ i))
    (hanti : ∀ i x, Antitone fun k => u k i x)
    (hlim : ∀ i x, Tendsto (fun k => u k i x) atTop (𝓝 (u₀ i x))) (e : ComplexChart n M) :
    LocalBedfordTaylorContinuity.WeakTendsto
      (fun k => weightedBedfordTaylorInChart hqp (u k) e)
      (weightedBedfordTaylorInChart hqp u₀ e) :=
  LocalBedfordTaylorDecreasing.weakTendsto_mulBorel_btProduct_of_antitone p q _
    (isPositive_oneCurrentOf hqp) (isClosedAny_oneCurrentOf hqp)
    (fun k i z => u k i (e.val.symm z)) (fun i z => u₀ i (e.val.symm z))
    (fun k i => (hu k i).chart e) (fun i => (hu₀ i).chart e)
    (fun i z _ => hanti i (e.val.symm z)) (fun i z _ => hlim i (e.val.symm z))

/-! ### Increasing continuity (`thm:contMA`) -/

/-- Convergence almost everywhere on `M`: in every atlas chart, for Lebesgue-almost every point of
the coordinate domain (the null sets of a manifold are measured by the Lebesgue measures of the
charts, as in `SGPT.PSH.VariableComplexAtlas.CoordinateAELE`). -/
def TendstoAE (u : ℕ → M → ℝ) (u₀ : M → ℝ) : Prop :=
  ∀ e : ComplexChart n M, ∀ᵐ z ∂volume.restrict (chartTarget e : Set (ComplexModel n)),
    Tendsto (fun k => u k (e.val.symm z)) atTop (𝓝 (u₀ (e.val.symm z)))

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
private theorem ae_imp_of_tendstoAE {u : ℕ → M → ℝ} {u₀ : M → ℝ} (h : TendstoAE (n := n) u u₀)
    (e : ComplexChart n M) :
    ∀ᵐ z, z ∈ (chartTarget e : Set (ComplexModel n)) →
      Tendsto (fun k => u k (e.val.symm z)) atTop (𝓝 (u₀ (e.val.symm z))) :=
  (ae_restrict_iff' (chartTarget e).isOpen.measurableSet).mp (h e)

/-- **`thm:contMA`, increasing sequences, unweighted form**: if `u_i^k ↑ u_i` almost everywhere,
with all functions locally bounded psh, then
`dd^c u_1^k ∧ ⋯ ∧ dd^c u_p^k → dd^c u_1 ∧ ⋯ ∧ dd^c u_p` weakly as currents on `M`. -/
theorem weakTendsto_bedfordTaylor_of_monotone (hqp : q + p = n) (u : ℕ → Fin p → M → ℝ)
    (u₀ : Fin p → M → ℝ) (hu : ∀ k i, IsLocallyBoundedPSH (n := n) (u k i))
    (hu₀ : ∀ i, IsLocallyBoundedPSH (n := n) (u₀ i))
    (hmono : ∀ i x, Monotone fun k => u k i x)
    (hae : ∀ i, TendstoAE (n := n) (fun k => u k i) (u₀ i)) :
    PositiveCurrent.WeakTendsto (fun k => bedfordTaylor hqp (u k) (hu k))
      (bedfordTaylor hqp u₀ hu₀) := fun e =>
  BedfordTaylorTopDegree.weakTendsto_btProduct_of_monotone hqp
    (fun k i z => u k i (e.val.symm z)) (fun i z => u₀ i (e.val.symm z))
    (fun k i => (hu k i).chart e) (fun i => (hu₀ i).chart e)
    (fun i z _ => hmono i (e.val.symm z)) (fun i => ae_imp_of_tendstoAE (hae i) e)

/-- **`thm:contMA`, increasing sequences, weighted form**: if `u_i^k ↑ u_i` almost everywhere for
`i = 0, …, p`, with all functions locally bounded psh, then
`u_0^k dd^c u_1^k ∧ ⋯ ∧ dd^c u_p^k → u_0 dd^c u_1 ∧ ⋯ ∧ dd^c u_p` weakly, in every chart. -/
theorem weakTendsto_weightedBedfordTaylorInChart_of_monotone (hqp : q + p = n)
    (u : ℕ → Fin (p + 1) → M → ℝ) (u₀ : Fin (p + 1) → M → ℝ)
    (hu : ∀ k i, IsLocallyBoundedPSH (n := n) (u k i))
    (hu₀ : ∀ i, IsLocallyBoundedPSH (n := n) (u₀ i))
    (hmono : ∀ i x, Monotone fun k => u k i x)
    (hae : ∀ i, TendstoAE (n := n) (fun k => u k i) (u₀ i)) (e : ComplexChart n M) :
    LocalBedfordTaylorContinuity.WeakTendsto
      (fun k => weightedBedfordTaylorInChart hqp (u k) e)
      (weightedBedfordTaylorInChart hqp u₀ e) :=
  BedfordTaylorTopDegree.weakTendsto_mulBorel_btProduct_of_monotone hqp
    (fun k i z => u k i (e.val.symm z)) (fun i z => u₀ i (e.val.symm z))
    (fun k i => (hu k i).chart e) (fun i => (hu₀ i).chart e)
    (fun i z _ => hmono i (e.val.symm z)) (fun i => ae_imp_of_tendstoAE (hae i) e)

/-! ### Products against a closed positive current (`rmk:extensionBT`, chartwise) -/

/-- The coordinate expression in the chart `e` of `dd^c u₁ ∧ ⋯ ∧ dd^c u_p ∧ T` for a current `T`
on `M` of bidimension `(q + p, q + p)`: the recursive local product against the chart expression
of `T` (`rmk:extensionBT`). -/
def bedfordTaylorRelInChart {r : ℕ} (T : PositiveCurrent n M (r + p)) (u : Fin p → M → ℝ)
    (e : ComplexChart n M) : LocalProductCurrent n (chartTarget e) r :=
  btProduct p r (fun i z => u i (e.val.symm z)) (T.inChart e)

/-- **`rmk:extensionBT`, chartwise**: for a closed positive current `T` and locally bounded psh
functions, every step of the recursion `dd^c (u₁ · dd^c u₂ ∧ ⋯ ∧ dd^c u_p ∧ T)` is defined, and
the coordinate expression of `dd^c u₁ ∧ ⋯ ∧ dd^c u_p ∧ T` is a closed positive current in every
chart; for `T = [M]` it is the Bedford–Taylor product. -/
theorem isPositive_bedfordTaylorRelInChart {r : ℕ} (T : PositiveCurrent n M (r + p))
    (hT : T.IsClosed) {u : Fin p → M → ℝ} (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i))
    (e : ComplexChart n M) :
    IsPositive (bedfordTaylorRelInChart T u e) ∧
      IsClosedAny r (bedfordTaylorRelInChart T u e) :=
  isPositive_btProduct p r _ _ (T.isPositive e) (hT e) fun i => (hu i).chart e

/-- The recursion of `rmk:extensionBT` in every chart:
`dd^c u₁ ∧ ⋯ ∧ dd^c u_{p+1} ∧ T = dd^c (u₁ · dd^c u₂ ∧ ⋯ ∧ dd^c u_{p+1} ∧ T)`. -/
theorem bedfordTaylorRelInChart_succ {r : ℕ} (T : PositiveCurrent n M (r + (p + 1)))
    (T' : PositiveCurrent n M (r + 1 + p)) (hTT : ∀ e, HEq (T.inChart e) (T'.inChart e))
    (u : Fin (p + 1) → M → ℝ) (e : ComplexChart n M) :
    bedfordTaylorRelInChart T u e =
      ddcMul (bedfordTaylorRelInChart T' (Fin.tail u) e) (fun z => u 0 (e.val.symm z)) :=
  LocalBedfordTaylorCollar.btProduct_succ_eq_ddcMul p r _ _ _ (hTT e)

end Product

end SGPT.NPP
