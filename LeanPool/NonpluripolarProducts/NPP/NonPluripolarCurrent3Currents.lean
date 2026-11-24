/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrent3Gauge
public import LeanPool.NonpluripolarProducts.Currents.ManifoldDdc
public import LeanPool.NonpluripolarProducts.Currents.LocalCurrentGluing
public import LeanPool.NonpluripolarProducts.PSH.PlurifineManifold

/-!
# Non-pluripolar products of closed positive `(1,1)`-currents

Source: `chapter_npp.tex`, `def:npp:L146` and the sentence after it ("The product
`T₁ ∧ ⋯ ∧ T_p` is independent of the choices we made thanks to (1) and (2)"), and `prop:npp1`
(2) on the manifold; Xia, *Foundations of pluripotential theory*, the paragraphs after
`prop:nonpluripolar-local-calculus` ("local finiteness and the local non-pluripolar product do not
depend on the choice of these potentials … the local products then glue to a positive current
`⟨T₁ ∧ ⋯ ∧ T_p⟩` on `X`").

`M` is a complex manifold of dimension `m + 1`; currents are S17's chart families
`SGPT.NPP.PositiveCurrent`; `q + p = m + 1`.

## `prop:npp1` (2) on `M`

* `nonPluripolarProduct_eq_of_ddcCurrent_eq` — for psh `φᵢ, ψᵢ` on `M` (`def:pshmfd`) with
  `dd^c φᵢ = dd^c ψᵢ` (`SGPT.NPP.ddcCurrent`), `⋀ dd^c φᵢ` is well defined iff `⋀ dd^c ψᵢ` is, and
  the two non-pluripolar products coincide (chartwise from the local
  `NonPluripolarCurrent.nonPluripolarProduct_eq_of_ddcL1_eq`: Weyl's lemma and gauge invariance).

## `def:npp:L146`

For positive `(1,1)`-currents `T₁, …, T_p` on `M` (bidimension `(m,m)`):

* `IsLocalPotential T O φ` — `φᵢ ∈ PSH(O)` (`SGPT.PSH.VariableComplexAtlas.IsPSHOn`, the
  project's `def:pshmfd` on the open manifold `O`) and `dd^c φᵢ = Tᵢ` on `O` (`IsDdcOn`);
* `IsNonPluripolarWellDefinedOn hqp φ O` — `dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p` is well defined on `O`
  (`eq:welldefinepluri` in every chart, on the coordinate expressions `chartDomain e O` of `O`;
  for `O = M` this is S17's `IsNonPluripolarWellDefined`, see
  `isNonPluripolarWellDefinedOn_top_iff`);
* **`IsCurrentProductWellDefined hqp T`** — the source definition: there is an open cover `𝒰` of
  `M` such that on each `U ∈ 𝒰` there are local potentials `φ^U` of `T` whose product is well
  defined on `U`;
* **`currentProduct hqp T hT`** — the non-pluripolar product `T₁ ∧ ⋯ ∧ T_p`, a positive current
  of bidimension `(q,q)` on `M`, glued (`SGPT.Currents.IsCompatibleFamily.exists_glue`) from the
  local products `⟨dd^c φ₁^U ∧ ⋯ ∧ dd^c φ_p^U⟩` of the chosen cover;
* **`currentProduct_restrict`** — `eq:ppp5` together with the independence of all choices: for
  *every* open `O ⊆ M` and *every* tuple `ψ` of local potentials of `T` on `O`, the product
  `⋀ dd^c ψᵢ` is well defined on `O` and `(T₁ ∧ ⋯ ∧ T_p)|_O = ⟨dd^c ψ₁ ∧ ⋯ ∧ dd^c ψ_p⟩`;
* `eq_currentProduct` — uniqueness: a positive current satisfying `eq:ppp5` for the members of
  some open cover with local potentials is `T₁ ∧ ⋯ ∧ T_p`;
* `isCurrentProductWellDefined_ddcCurrent_iff`, `currentProduct_ddcCurrent` — for global
  potentials, `dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p` (`def:npp:L146`) is well defined iff the product of the
  `φᵢ` (`def:npp:L69`) is, and the two products agree.

Closedness of `T₁ ∧ ⋯ ∧ T_p` (asserted in the definition, `prop:npp1` (5)) is proved only for
`p = m + 1` (bidimension `(0,0)`, `isClosed_currentProduct_top`); for `p < m + 1` it is open.
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
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

variable {p q : ℕ} (hqp : q + p = m + 1)

/-! ### `prop:npp1` (2) on the manifold -/

/-- **`prop:npp1` (2)**: for psh `φᵢ, ψᵢ` on `M` with `dd^c φᵢ = dd^c ψᵢ` as currents, the product
`⋀ dd^c φᵢ` is well defined iff `⋀ dd^c ψᵢ` is, and then the two non-pluripolar products are
equal. -/
theorem nonPluripolarProduct_eq_of_ddcCurrent_eq {φ ψ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i))
    (hψ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (ψ i))
    (h : ∀ i, ddcCurrent m (φ i) (hφ i) = ddcCurrent m (ψ i) (hψ i)) :
    (IsNonPluripolarWellDefined hqp φ ↔ IsNonPluripolarWellDefined hqp ψ) ∧
      ∀ (hW : IsNonPluripolarWellDefined hqp φ) (hW' : IsNonPluripolarWellDefined hqp ψ),
        nonPluripolarProduct hqp φ hφ hW = nonPluripolarProduct hqp ψ hψ hW' := by
  have hloc := fun e : ComplexChart (m + 1) M =>
    nonPluripolarProduct_eq_of_ddcL1_eq hqp (fun i => isL1PshOn_chart (hφ i) e)
      (fun i => isL1PshOn_chart (hψ i) e) fun i => congrArg (fun T => T.inChart e) (h i)
  refine ⟨⟨fun hW e => (hloc e).1.mp (hW e), fun hW e => (hloc e).1.mpr (hW e)⟩,
    fun hW _ => ?_⟩
  ext1 e
  exact (hloc e).2 (hW e)

/-! ### Local potentials -/

section Potentials

variable {T : Fin p → PositiveCurrent (m + 1) M m}

/-- **Local potentials** of `T₁, …, T_p` on the open set `O`: `φᵢ ∈ PSH(O)` and `dd^c φᵢ = Tᵢ` on
`O`. -/
structure IsLocalPotential (T : Fin p → PositiveCurrent (m + 1) M m) (O : Opens M)
    (φ : Fin p → M → EReal) : Prop where
  psh : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) O
  ddc : ∀ i, IsDdcOn (T i) (φ i) O

variable {O O' : Opens M} {φ ψ : Fin p → M → EReal}

theorem IsLocalPotential.isL1PshOn (h : IsLocalPotential T O φ) (e : ComplexChart (m + 1) M)
    (i : Fin p) : IsL1PshOn (chartDomain e O) fun z => φ i (e.val.symm z) :=
  isL1PshOn_chartDomain (h.psh i) e

theorem IsLocalPotential.chartPsh (h : IsLocalPotential T O φ) (e : ComplexChart (m + 1) M) :
    ∀ i, SGPT.Foundations.Analysis.PlurisubharmonicOn (fun z => φ i (e.val.symm z))
      (chartDomain e O) :=
  fun i => (h.isL1PshOn e i).psh

/-- On an open `W` inside the coordinate expression of `O`, `dd^c (φᵢ ∘ e⁻¹)` is the restriction of
the chart expression of `Tᵢ`. -/
theorem IsLocalPotential.ddcL1_eq (h : IsLocalPotential T O φ) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartDomain e O) (i : Fin p) :
    ddcL1 W (fun z => φ i (e.val.symm z)) =
      restrict (hW.trans (chartDomain_le e O)) ((T i).inChart e) := by
  rw [← restrict_restrict hW (chartDomain_le e O), (h.ddc i) e,
    restrict_ddcL1 hW (h.isL1PshOn e i).locallyIntegrableOn]

/-- **Two tuples of local potentials of the same currents give the same local products** on the
coordinate expression of the overlap (`prop:npp1` (2), local form). -/
theorem IsLocalPotential.compare (hφ : IsLocalPotential T O φ) (hψ : IsLocalPotential T O' ψ)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartDomain e O)
    (hW' : W ≤ chartDomain e O') :
    (IsWellDefinedOn hqp W (fun i z => φ i (e.val.symm z)) ↔
        IsWellDefinedOn hqp W (fun i z => ψ i (e.val.symm z))) ∧
      (IsWellDefinedOn hqp W (fun i z => φ i (e.val.symm z)) →
        NonPluripolarCurrent.nonPluripolarProduct hqp W (fun i z => φ i (e.val.symm z)) =
          NonPluripolarCurrent.nonPluripolarProduct hqp W (fun i z => ψ i (e.val.symm z))) :=
  nonPluripolarProduct_eq_of_ddcL1_eq hqp (fun i => (hφ.isL1PshOn e i).mono hW)
    (fun i => (hψ.isL1PshOn e i).mono hW') fun i => by
      rw [hφ.ddcL1_eq e hW, hψ.ddcL1_eq e hW']

end Potentials

/-! ### Well-definedness on an open set -/

/-- **`dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p` is well defined on the open set `O`** (`eq:welldefinepluri` on
`O`, in coordinates): in every chart `e`, the local condition on the coordinate expression of
`O`. -/
def IsNonPluripolarWellDefinedOn (φ : Fin p → M → EReal) (O : Opens M) : Prop :=
  ∀ e : ComplexChart (m + 1) M,
    IsWellDefinedOn hqp (chartDomain e O) fun i z => φ i (e.val.symm z)

/-- On `O = M` this is S17's chart condition `IsNonPluripolarWellDefined`. -/
theorem isNonPluripolarWellDefinedOn_top_iff {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i)) :
    IsNonPluripolarWellDefinedOn hqp φ ⊤ ↔ IsNonPluripolarWellDefined hqp φ := by
  constructor
  · intro h e
    exact isWellDefinedOn_of_cover hqp (chartPlurisubharmonicOn hφ e)
      (fun _ : Unit => chartDomain e ⊤) (fun _ => chartDomain_le e ⊤)
      (fun z hz => mem_iUnion.mpr ⟨(), hz, trivial⟩) fun _ => h e
  · intro h e
    exact isWellDefinedOn_restrict hqp (chartPlurisubharmonicOn hφ e) (h e) (chartDomain_le e ⊤)

/-! ### `prop:npp1` (1), `eq:ppp2` and the covering criterion on open subsets of `M` -/

/-- **`eq:ppp2` on open subsets of `M`** (`prop:npp1` (1)): if `⋀ dd^c φᵢ` is well defined on `M`
and `O ⊆ M` is open, then the product of the restrictions `φᵢ|_O` is well defined on `O` and
`(⋀ dd^c φᵢ)|_O = ⋀ dd^c φᵢ|_O`, in every chart. -/
theorem nonPluripolarProduct_restrict_opens {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i)) (hW : IsNonPluripolarWellDefined hqp φ)
    (O : Opens M) :
    IsNonPluripolarWellDefinedOn hqp φ O ∧
      ∀ e : ComplexChart (m + 1) M,
        restrict (chartDomain_le e O) ((nonPluripolarProduct hqp φ hφ hW).inChart e) =
          NonPluripolarCurrent.nonPluripolarProduct hqp (chartDomain e O)
            fun i z => φ i (e.val.symm z) :=
  ⟨fun e => isWellDefinedOn_restrict hqp (chartPlurisubharmonicOn hφ e) (hW e) (chartDomain_le e
    O),
    fun e => restrict_nonPluripolarProduct hqp (chartPlurisubharmonicOn hφ e) (hW e)
      (chartDomain_le e O)⟩

/-- **The covering criterion on `M`** (`prop:npp1` (1), last sentence): for an arbitrary open
cover `𝒰` of `M`, `⋀ dd^c φᵢ` is well defined iff it is well defined on every `U ∈ 𝒰`. -/
theorem isNonPluripolarWellDefined_iff_of_cover {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i)) {𝒰 : Set (Opens M)}
    (h𝒰 : ∀ x : M, ∃ U ∈ 𝒰, x ∈ U) :
    IsNonPluripolarWellDefined hqp φ ↔ ∀ U ∈ 𝒰, IsNonPluripolarWellDefinedOn hqp φ U := by
  constructor
  · intro hW U _
    exact (nonPluripolarProduct_restrict_opens hqp hφ hW U).1
  · intro h e
    refine isWellDefinedOn_of_cover hqp (chartPlurisubharmonicOn hφ e)
      (fun U : 𝒰 => chartDomain e U.1) (fun U => chartDomain_le e U.1) (fun z hz => ?_)
      fun U => h U.1 U.2 e
    obtain ⟨U, hU, hzU⟩ := h𝒰 (e.val.symm z)
    exact mem_iUnion.mpr ⟨⟨U, hU⟩, hz, hzU⟩

omit [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M] in
/-- The coordinate expression `e.target ∩ e⁻¹⁻¹(O)` of a Borel set `O ⊆ M` is Borel. -/
theorem measurableSet_chartImage [MeasurableSpace M] [BorelSpace M] {O : Set M}
    (hO : MeasurableSet O) (e : ComplexChart (m + 1) M) :
    MeasurableSet (e.val.target ∩ e.val.symm ⁻¹' O) := by
  let g : e.val.target → M := fun z => e.val.symm z
  have hg : Continuous g := continuousOn_iff_continuous_domRestrict.mp e.val.continuousOn_symm
  have h := MeasurableSet.subtype_image e.val.open_target.measurableSet (hg.measurable hO)
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz, hzO⟩
    exact ⟨⟨z, hz⟩, hzO, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩

/-- **`eq:ppp1` for Borel plurifine open subsets of `M`** (`prop:npp1` (1); the plurifine topology
of `M` is the verified `def:pftopologygeneral`,
`SGPT.PSH.VariableComplexAtlas.plurifineTopology`): if `φᵢ = ψᵢ` on a Borel plurifine open set
`O ⊆ M` and both products are well defined, then `1_O ⟨⋀ dd^c φᵢ⟩ = 1_O ⟨⋀ dd^c ψᵢ⟩`, in every
chart (multiplication by the indicator of the coordinate expression of `O`). -/
theorem mulBorel_nonPluripolarProduct_inChart_eq_of_eqOn_plurifineOpen [MeasurableSpace M]
    [BorelSpace M] {φ ψ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i))
    (hψ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (ψ i))
    (hWφ : IsNonPluripolarWellDefined hqp φ) (hWψ : IsNonPluripolarWellDefined hqp ψ) {O : Set M}
    (hOm : MeasurableSet O)
    (hOfine : IsOpen[(SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).plurifineTopology] O)
    (heq : ∀ i, EqOn (φ i) (ψ i) O) (e : ComplexChart (m + 1) M) :
    mulBorel ((nonPluripolarProduct hqp φ hφ hWφ).inChart e)
        ((e.val.target ∩ e.val.symm ⁻¹' O).indicator fun _ => (1 : ℝ)) =
      mulBorel ((nonPluripolarProduct hqp ψ hψ hWψ).inChart e)
        ((e.val.target ∩ e.val.symm ⁻¹' O).indicator fun _ => (1 : ℝ)) := by
  have hfine := (SGPT.PSH.VariableComplexAtlas.isOpen_plurifine_iff _ O).mp hOfine e
  refine mulBorel_nonPluripolarProduct_eq_of_eqOn_plurifineOpen hqp (chartPlurisubharmonicOn hφ e)
    (chartPlurisubharmonicOn hψ e) (hWφ e) (hWψ e) inter_subset_left
    (measurableSet_chartImage hOm e) ?_ fun i z hz => heq i hz.2
  have hset : (Subtype.val ⁻¹' (e.val.target ∩ e.val.symm ⁻¹' O) : Set (chartTarget e)) =
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).chartInverse e ⁻¹' O := by
    ext z
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  rw [hset]
  exact hfine

/-! ### The definition `def:npp:L146` -/

/-- **`def:npp:L146`, well-definedness**: `T₁ ∧ ⋯ ∧ T_p` is well defined if there is an open
covering `𝒰` of `M` such that on each `U ∈ 𝒰` there are `φⱼ^U ∈ PSH(U)` with `dd^c φⱼ^U = Tⱼ` and
`dd^c φ₁^U ∧ ⋯ ∧ dd^c φ_p^U` well defined. -/
def IsCurrentProductWellDefined (T : Fin p → PositiveCurrent (m + 1) M m) : Prop :=
  ∃ 𝒰 : Set (Opens M), (∀ x : M, ∃ U ∈ 𝒰, x ∈ U) ∧
    ∀ U ∈ 𝒰, ∃ φ : Fin p → M → EReal,
      IsLocalPotential T U φ ∧ IsNonPluripolarWellDefinedOn hqp φ U

namespace IsCurrentProductWellDefined

variable {hqp} {T : Fin p → PositiveCurrent (m + 1) M m} (hT : IsCurrentProductWellDefined hqp T)

/-- The chosen open cover. -/
def cover : Set (Opens M) := hT.choose

theorem cover_spec (x : M) : ∃ U ∈ hT.cover, x ∈ U := hT.choose_spec.1 x

open Classical in
/-- The chosen local potentials on the members of the cover. -/
def pot (U : Opens M) : Fin p → M → EReal :=
  if h : U ∈ hT.cover then (hT.choose_spec.2 U h).choose else fun _ _ => 0

theorem pot_spec {U : Opens M} (hU : U ∈ hT.cover) :
    IsLocalPotential T U (hT.pot U) ∧ IsNonPluripolarWellDefinedOn hqp (hT.pot U) U := by
  rw [pot, dite_eq_left hU]
  exact (hT.choose_spec.2 U hU).choose_spec

/-- The local products of the chosen potentials, on the coordinate expressions of the members of
the cover. -/
def localProduct (e : ComplexChart (m + 1) M) (U : hT.cover) :
    LocalProductCurrent (m + 1) (chartDomain e U.1) q :=
  NonPluripolarCurrent.nonPluripolarProduct hqp (chartDomain e U.1) fun i z => hT.pot U.1 i
    (e.val.symm z)

theorem isPositive_localProduct (e : ComplexChart (m + 1) M) (U : hT.cover) :
    IsPositive (hT.localProduct e U) :=
  isPositive_nonPluripolarProduct hqp ((hT.pot_spec U.2).1.chartPsh e) ((hT.pot_spec U.2).2 e)

/-- The local products are compatible on overlaps (`prop:npp1` (1) and (2)). -/
theorem isCompatibleFamily (e : ComplexChart (m + 1) M) :
    SGPT.Currents.IsCompatibleFamily (fun U : hT.cover => chartDomain e U.1) (hT.localProduct e)
      where
  isPositive := hT.isPositive_localProduct e
  agree U V := by
    have hU := hT.pot_spec U.2
    have hV := hT.pot_spec V.2
    rw [localProduct, localProduct, restrict_nonPluripolarProduct hqp (hU.1.chartPsh e) (hU.2 e),
      restrict_nonPluripolarProduct hqp (hV.1.chartPsh e) (hV.2 e)]
    exact (hU.1.compare hqp hV.1 e inf_le_left inf_le_right).2
      (isWellDefinedOn_restrict hqp (hU.1.chartPsh e) (hU.2 e) inf_le_left)

theorem chartDomain_cover (e : ComplexChart (m + 1) M) :
    ∀ z ∈ chartTarget e, ∃ U : hT.cover, z ∈ chartDomain e U.1 := by
  intro z hz
  obtain ⟨U, hU, hzU⟩ := hT.cover_spec (e.val.symm z)
  exact ⟨⟨U, hU⟩, hz, hzU⟩

theorem exists_glue (e : ComplexChart (m + 1) M) :
    ∃ S : LocalProductCurrent (m + 1) (chartTarget e) q, IsPositive S ∧
      ∀ U : hT.cover, restrict (chartDomain_le e U.1) S = hT.localProduct e U :=
  (hT.isCompatibleFamily e).exists_glue (fun U => chartDomain_le e U.1) (hT.chartDomain_cover e)

/-- The chart expression of `T₁ ∧ ⋯ ∧ T_p` in the chart `e`: the glued local products. -/
def productInChart (e : ComplexChart (m + 1) M) : LocalProductCurrent (m + 1) (chartTarget e) q :=
  (hT.exists_glue e).choose

theorem isPositive_productInChart (e : ComplexChart (m + 1) M) :
    IsPositive (hT.productInChart e) :=
  (hT.exists_glue e).choose_spec.1

theorem restrict_productInChart (e : ComplexChart (m + 1) M) (U : hT.cover) :
    restrict (chartDomain_le e U.1) (hT.productInChart e) = hT.localProduct e U :=
  (hT.exists_glue e).choose_spec.2 U

/-- **Independence of the choices, in a chart**: for every open `O` and every tuple `ψ` of local
potentials of `T` on `O`, the product of the `ψᵢ` is well defined on the coordinate expression of
`O` and is the restriction of the glued chart expression. -/
theorem productInChart_restrict {O : Opens M} {ψ : Fin p → M → EReal}
    (hψ : IsLocalPotential T O ψ) (e : ComplexChart (m + 1) M) :
    IsWellDefinedOn hqp (chartDomain e O) (fun i z => ψ i (e.val.symm z)) ∧
      restrict (chartDomain_le e O) (hT.productInChart e) =
        NonPluripolarCurrent.nonPluripolarProduct hqp (chartDomain e O) fun i z => ψ i (e.val.symm
          z) := by
  -- well-definedness, from the overlaps with the members of the cover
  have hWloc : ∀ U : hT.cover, IsWellDefinedOn hqp (chartDomain e O ⊓ chartDomain e U.1)
      fun i z => ψ i (e.val.symm z) := by
    intro U
    have hU := hT.pot_spec U.2
    exact (hU.1.compare hqp hψ e inf_le_right inf_le_left).1.mp
      (isWellDefinedOn_restrict hqp (hU.1.chartPsh e) (hU.2 e) inf_le_right)
  have hW : IsWellDefinedOn hqp (chartDomain e O) fun i z => ψ i (e.val.symm z) := by
    refine isWellDefinedOn_of_cover hqp (hψ.chartPsh e)
      (fun U : hT.cover => chartDomain e O ⊓ chartDomain e U.1) (fun _ => inf_le_left)
      (fun z hz => ?_) hWloc
    obtain ⟨U, hzU⟩ := hT.chartDomain_cover e z hz.1
    exact mem_iUnion.mpr ⟨U, hz, hzU⟩
  refine ⟨hW, ?_⟩
  apply LocalBedfordTaylorCalculus.eq_of_local
  intro z hz
  obtain ⟨U, hzU⟩ := hT.chartDomain_cover e z hz.1
  have hU := hT.pot_spec U.2
  refine ⟨chartDomain e O ⊓ chartDomain e U.1, inf_le_left, ⟨hz, hzU⟩, ?_⟩
  rw [restrict_restrict, ← restrict_restrict (inf_le_right : chartDomain e O ⊓ chartDomain e U.1 ≤
    _)
    (chartDomain_le e U.1), hT.restrict_productInChart e U, localProduct,
    restrict_nonPluripolarProduct hqp (hU.1.chartPsh e) (hU.2 e) inf_le_right,
    restrict_nonPluripolarProduct hqp (hψ.chartPsh e) hW inf_le_left]
  exact (hU.1.compare hqp hψ e inf_le_right inf_le_left).2
    (isWellDefinedOn_restrict hqp (hU.1.chartPsh e) (hU.2 e) inf_le_right)

/-- The glued chart expressions are compatible on overlaps of charts. -/
theorem productInChart_compatible (e f : ComplexChart (m + 1) M) :
    restrict (overlapSource_le e f) (hT.productInChart e) =
      pullback (chartTransition_isBiholomorphicPair e f)
        (isPositive_restrict (hT.isPositive_productInChart f) (overlapTarget_le e f)) := by
  have hh := chartTransition_isBiholomorphicPair e f
  apply LocalBedfordTaylorCalculus.eq_of_local
  intro z hz
  obtain ⟨U, hU, hzU⟩ := hT.cover_spec (e.val.symm z)
  have hpot := hT.pot_spec hU
  set V' : Opens (ComplexModel (m + 1)) := overlapTarget e f ⊓ chartDomain f U with hV'
  have hV'B : V' ≤ overlapTarget e f := inf_le_left
  have hzf : e.val.symm z ∈ f.val.source := by
    have hz' : z ∈ (chartTransition e f).source := hz
    simp only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hz'
    exact hz'.2
  have hτ : ∀ x ∈ overlapSource e f, f.val.symm (chartTransition e f x) = e.val.symm x := by
    intro x hx
    have hx' : x ∈ (chartTransition e f).source := hx
    have hxf : e.val.symm x ∈ f.val.source := by
      simp only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hx'
      exact hx'.2
    simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      f.val.left_inv hxf]
  have hpre_le : preOpen hh V' ≤ chartDomain e U := by
    intro x hx
    refine ⟨overlapSource_le e f hx.1, ?_⟩
    have h2 : f.val.symm (chartTransition e f x) ∈ U := hx.2.2.2
    rw [hτ x hx.1] at h2
    exact h2
  refine ⟨preOpen hh V', preOpen_le hh V', ⟨hz, hh.mapsTo hz, overlapTarget_le e f (hh.mapsTo hz),
    show f.val.symm (chartTransition e f z) ∈ U by rw [hτ z hz]; exact hzU⟩, ?_⟩
  -- the left-hand side
  have hL : restrict (preOpen_le hh V') (restrict (overlapSource_le e f) (hT.productInChart e)) =
      NonPluripolarCurrent.nonPluripolarProduct hqp (preOpen hh V') fun i x => hT.pot U i
        (e.val.symm x) := by
    rw [restrict_restrict, ← restrict_restrict hpre_le (chartDomain_le e U),
      (hT.productInChart_restrict hpot.1 e).2,
      restrict_nonPluripolarProduct hqp (hpot.1.chartPsh e) (hpot.2 e) hpre_le]
  -- the right-hand side
  have hpshV' : ∀ i, SGPT.Foundations.Analysis.PlurisubharmonicOn
      (fun y => hT.pot U i (f.val.symm y)) V' := fun i => (hpot.1.chartPsh f i).mono inf_le_right
  have hWV' : IsWellDefinedOn hqp V' fun i y => hT.pot U i (f.val.symm y) :=
    isWellDefinedOn_restrict hqp (hpot.1.chartPsh f) (hpot.2 f) inf_le_right
  have hRV' : restrict hV'B (restrict (overlapTarget_le e f) (hT.productInChart f)) =
      NonPluripolarCurrent.nonPluripolarProduct hqp V' fun i y => hT.pot U i (f.val.symm y) := by
    rw [restrict_restrict, ← restrict_restrict (inf_le_right : V' ≤ chartDomain f U)
      (chartDomain_le f U), (hT.productInChart_restrict hpot.1 f).2,
      restrict_nonPluripolarProduct hqp (hpot.1.chartPsh f) (hpot.2 f) inf_le_right]
  have hh' := isBiholomorphicPair_preOpen hh hV'B
  have hpb := pullback_nonPluripolarProduct hqp hh' hpshV' hWV'
  have hR : restrict (preOpen_le hh V') (pullback hh
        (isPositive_restrict (hT.isPositive_productInChart f) (overlapTarget_le e f))) =
      NonPluripolarCurrent.nonPluripolarProduct hqp (preOpen hh V') fun i x => hT.pot U i
        (e.val.symm x) := by
    rw [← pullback_restrict hh _ hV'B,
      pullback_congr_current hh' _ (isPositive_nonPluripolarProduct hqp hpshV' hWV') hRV',
      hpb.2]
    exact (nonPluripolarProduct_congr hqp fun i x hx => by rw [hτ x hx.1]).2
  rw [hL, hR]

end IsCurrentProductWellDefined

/-- **`def:npp:L146`, the product**: the non-pluripolar product `T₁ ∧ ⋯ ∧ T_p` of positive
`(1,1)`-currents admitting local potentials with well-defined local products, a positive current
of bidimension `(q,q)` (bidegree `(p,p)`) on `M`, defined by
`(T₁ ∧ ⋯ ∧ T_p)|_U = dd^c φ₁^U ∧ ⋯ ∧ dd^c φ_p^U` on the members of the chosen cover (`eq:ppp5`);
by `currentProduct_restrict` it does not depend on the cover nor on the potentials. -/
def currentProduct (T : Fin p → PositiveCurrent (m + 1) M m)
    (hT : IsCurrentProductWellDefined hqp T) : PositiveCurrent (m + 1) M q where
  inChart := hT.productInChart
  isPositive := hT.isPositive_productInChart
  compatible := hT.productInChart_compatible

variable {T : Fin p → PositiveCurrent (m + 1) M m}

/-- **`eq:ppp5` and the independence of the choices** (the sentence after `def:npp:L146`): for
every open set `O ⊆ M` and every tuple `ψ` of local potentials of `T` on `O`
(`ψᵢ ∈ PSH(O)`, `dd^c ψᵢ = Tᵢ` on `O`), the product `dd^c ψ₁ ∧ ⋯ ∧ dd^c ψ_p` is well defined on
`O` and `(T₁ ∧ ⋯ ∧ T_p)|_O = dd^c ψ₁ ∧ ⋯ ∧ dd^c ψ_p` (in every chart). -/
theorem currentProduct_restrict (hT : IsCurrentProductWellDefined hqp T) {O : Opens M}
    {ψ : Fin p → M → EReal} (hψ : IsLocalPotential T O ψ) :
    IsNonPluripolarWellDefinedOn hqp ψ O ∧
      ∀ e : ComplexChart (m + 1) M,
        restrict (chartDomain_le e O) ((currentProduct hqp T hT).inChart e) =
          NonPluripolarCurrent.nonPluripolarProduct hqp (chartDomain e O) fun i z => ψ i
            (e.val.symm z) :=
  ⟨fun e => (hT.productInChart_restrict hψ e).1, fun e => (hT.productInChart_restrict hψ e).2⟩

/-- **Uniqueness**: a positive current satisfying `eq:ppp5` on the members of an open cover with
local potentials is `T₁ ∧ ⋯ ∧ T_p`. -/
theorem eq_currentProduct (hT : IsCurrentProductWellDefined hqp T) {S : PositiveCurrent (m + 1)
    M q}
    {𝒰 : Set (Opens M)} (h𝒰 : ∀ x : M, ∃ U ∈ 𝒰, x ∈ U) {φ : Opens M → Fin p → M → EReal}
    (hφ : ∀ U ∈ 𝒰, IsLocalPotential T U (φ U))
    (hS : ∀ U ∈ 𝒰, ∀ e : ComplexChart (m + 1) M,
      restrict (chartDomain_le e U) (S.inChart e) =
        NonPluripolarCurrent.nonPluripolarProduct hqp (chartDomain e U) fun i z => φ U i
          (e.val.symm z)) :
    S = currentProduct hqp T hT := by
  ext1 e
  apply LocalBedfordTaylorCalculus.eq_of_local
  intro z hz
  obtain ⟨U, hU, hzU⟩ := h𝒰 (e.val.symm z)
  exact ⟨chartDomain e U, chartDomain_le e U, ⟨hz, hzU⟩,
    by rw [hS U hU e, ((currentProduct_restrict hqp hT (hφ U hU)).2 e)]⟩

/-- In top degree (`p = m + 1`, bidimension `(0,0)`) `T₁ ∧ ⋯ ∧ T_p` is closed. -/
theorem isClosed_currentProduct_top {T : Fin (m + 1) → PositiveCurrent (m + 1) M m}
    (h0 : 0 + (m + 1) = m + 1) (hT : IsCurrentProductWellDefined h0 T) :
    (currentProduct h0 T hT).IsClosed := fun _ => trivial

/-! ### Compatibility with `def:npp:L69` -/

/-- Global psh potentials are local potentials on every open set. -/
theorem isLocalPotential_ddcCurrent {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i)) (O : Opens M) :
    IsLocalPotential (fun i => ddcCurrent m (φ i) (hφ i)) O φ :=
  ⟨fun i => isPSHOn_of_manifoldPSH (hφ i) O, fun i => isDdcOn_ddcCurrent (hφ i) O⟩

/-- **`dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p` in the sense of `def:npp:L146` is well defined iff the product of
the psh functions `φᵢ` (`def:npp:L69`) is.** -/
theorem isCurrentProductWellDefined_ddcCurrent_iff {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i)) :
    IsCurrentProductWellDefined hqp (fun i => ddcCurrent m (φ i) (hφ i)) ↔
      IsNonPluripolarWellDefined hqp φ := by
  constructor
  · intro hT
    exact (isNonPluripolarWellDefinedOn_top_iff hqp hφ).mp
      (currentProduct_restrict hqp hT (isLocalPotential_ddcCurrent hφ ⊤)).1
  · intro hW
    exact ⟨{⊤}, fun x => ⟨⊤, rfl, trivial⟩, fun U hU => by
      rw [mem_singleton_iff.mp hU]
      exact ⟨φ, isLocalPotential_ddcCurrent hφ ⊤,
        (isNonPluripolarWellDefinedOn_top_iff hqp hφ).mpr hW⟩⟩

/-- **The two definitions of the product agree**: `dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p` of `def:npp:L146`
(products of the currents `dd^c φᵢ`) is the non-pluripolar product of the `φᵢ` of
`def:npp:L69`. -/
theorem currentProduct_ddcCurrent {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i))
    (hT : IsCurrentProductWellDefined hqp (fun i => ddcCurrent m (φ i) (hφ i))) :
    currentProduct hqp (fun i => ddcCurrent m (φ i) (hφ i)) hT =
      nonPluripolarProduct hqp φ hφ ((isCurrentProductWellDefined_ddcCurrent_iff hqp hφ).mp hT)
        := by
  set hW := (isCurrentProductWellDefined_ddcCurrent_iff hqp hφ).mp hT
  symm
  refine eq_currentProduct hqp hT (𝒰 := {⊤}) (fun x => ⟨⊤, rfl, trivial⟩) (φ := fun _ => φ)
    (fun U _ => isLocalPotential_ddcCurrent hφ U) fun U _ e => ?_
  rw [nonPluripolarProduct_inChart]
  exact restrict_nonPluripolarProduct hqp (chartPlurisubharmonicOn hφ e) (hW e)
    (chartDomain_le e U)

end SGPT.NPP
