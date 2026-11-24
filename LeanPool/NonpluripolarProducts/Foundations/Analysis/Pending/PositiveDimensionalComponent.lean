/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RegularLocusComponent
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ClosureDifferenceAnalytic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.NonKahlerLocus

/-!
# Positive-dimensional irreducible components through non-isolated points

Blueprint `ana:irreducible-components` (Demailly, *Complex analytic and differential
geometry*, II.5.3).

* `exists_isOpen_inter_subset_singleton_of_regularAtDim_zero`: a regular point of dimension
  `0` of `A` is isolated in `A` (the flattening sends `A` near the point to `{0}`).
* `subset_singleton_of_isPreconnected`: a preconnected subset of `A` consisting of regular
  points of dimension `0` is a subsingleton.
* `exists_isIrreducibleComponent_pos_dim_of_accPt`: a non-isolated point `x` of an analytic
  subset `A` lies on a positive-dimensional irreducible component.  Take (LS) with connected
  regular parts at `x`.  If all piece dimensions vanished, each piece would meet the
  neighbourhood `Δᵢ` only in `x`, so `x` would be isolated in `A`.  Hence some piece has
  `dᵢ > 0`; for `c` in its connected regular part `Gᵢ`, the closure `V` of the connected
  component `C` of the regular locus through `c` is irreducible analytic of dimension `dᵢ`,
  contains `closure Gᵢ ∋ x`, lies in `A`, and is maximal since `A` agrees with `C` near `c`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PositiveDimensionalComponent

open FirstPass FirstPass.NonKahlerLocus AnalyticLocalStatement LocalStatementConnected
  RegularLocusComponent

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A regular point of dimension `0` is isolated. -/
theorem exists_isOpen_inter_subset_singleton_of_regularAtDim_zero {A : Set M} {y : M}
    (hy : RegularAtDim (n := n) A y 0) :
    ∃ O : Set M, IsOpen O ∧ y ∈ O ∧ A ∩ O ⊆ {y} := by
  obtain ⟨-, -, Φ, -, hzero, hflat⟩ := hy
  refine ⟨(complexChartAt (n := n) y).val.source ∩
      (complexChartAt (n := n) y).val ⁻¹' Φ.source,
    (complexChartAt (n := n) y).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) y).val.open_source Φ.isOpen_source,
    ⟨mem_complexChartAt_source y, Φ.center_mem_source⟩, ?_⟩
  rintro z ⟨hzA, hzs, hzΦ⟩
  have hz0 : Φ.toFun ((complexChartAt (n := n) y).val z) = 0 := by
    have hp := (hflat hzs hzΦ).mp hzA
    ext i
    simpa using hp i (Nat.zero_le _)
  have hez : (complexChartAt (n := n) y).val z = (complexChartAt (n := n) y).val y :=
    calc (complexChartAt (n := n) y).val z
        = Φ.invFun (Φ.toFun ((complexChartAt (n := n) y).val z)) := (Φ.left_inv _ hzΦ).symm
      _ = Φ.invFun (Φ.toFun ((complexChartAt (n := n) y).val y)) := by rw [hz0, hzero]
      _ = (complexChartAt (n := n) y).val y := Φ.left_inv _ Φ.center_mem_source
  exact (complexChartAt (n := n) y).val.injOn hzs (mem_complexChartAt_source y) hez

/-- A preconnected set of `0`-dimensional regular points is a subsingleton. -/
theorem subset_singleton_of_isPreconnected {A G : Set M} (hGA : G ⊆ A)
    (hG : IsPreconnected G) (hreg : ∀ y ∈ G, RegularAtDim (n := n) A y 0) {g : M}
    (hg : g ∈ G) : G ⊆ {g} := by
  obtain ⟨O, hO, hgO, hAO⟩ :=
    exists_isOpen_inter_subset_singleton_of_regularAtDim_zero (hreg g hg)
  have hcover : G ⊆ O ∪ {g}ᶜ := by
    intro z _
    by_cases hzg : z = g
    · exact Or.inl (hzg ▸ hgO)
    · exact Or.inr hzg
  have hdisj : G ∩ (O ∩ {g}ᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro z ⟨hzG, hzO, hzg⟩
    exact hzg (hAO ⟨hGA hzG, hzO⟩)
  have hGO : G ⊆ O := by
    rcases isPreconnected_iff_subset_of_disjoint.mp hG O {g}ᶜ hO isOpen_compl_singleton
      hcover hdisj with h | h
    · exact h
    · exact absurd (h hg) (by simp)
  exact fun z hz => hAO ⟨hGA hz, hGO hz⟩

/-- **Positive-dimensional components through non-isolated points.** A point of an
analytic subset `A` which is not isolated in `A` lies on a positive-dimensional
irreducible component of `A`. -/
theorem exists_isIrreducibleComponent_pos_dim_of_accPt {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {x : M} (hx : x ∈ A)
    (hacc : AccPt x (𝓟 A)) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety n M,
      IsIrreducibleComponent V A ∧ 0 < V.dim ∧ x ∈ V.carrier := by
  obtain ⟨D, ⟨P⟩⟩ := exists_connectedParts (p := x) hA
  have hpieceA : ∀ i, D.piece i ⊆ A := fun i y hy =>
    (D.inter_nbhd_eq.symm ▸ mem_iUnion.mpr ⟨i, hy⟩ : y ∈ A ∩ D.nbhd).1
  have hgoodA : ∀ i, P.good i ⊆ A := fun i =>
    (P.good_subset i).trans (inter_subset_left.trans (hpieceA i))
  -- some piece is positive-dimensional
  have hpos : ∃ i, 0 < D.dim i := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hsing : ∀ i, D.piece i ∩ P.core i ⊆ {x} := by
      intro i
      have hmem : x ∈ closure (P.good i) :=
        P.subset_closure_good i ⟨P.mem_piece i, P.mem_core i⟩
      obtain ⟨g, hg⟩ := mem_closure_iff_nhds.mp hmem univ univ_mem
      have hGg : P.good i ⊆ {g} := subset_singleton_of_isPreconnected (hgoodA i)
        (P.isPreconnected_good i)
        (fun y hy => Nat.le_zero.mp (hcon i) ▸ P.regularAtDim_of_mem_good i y hy) hg.2
      have hcl : closure (P.good i) ⊆ {g} := by
        simpa using closure_mono hGg
      have hxg : x = g := hcl hmem
      exact hxg ▸ (P.subset_closure_good i).trans hcl
    set N : Set M := D.nbhd ∩ ⋂ i, P.core i
    have hN : N ∈ 𝓝 x := (D.isOpen_nbhd.inter (isOpen_iInter_of_finite P.isOpen_core)).mem_nhds
      ⟨D.mem_nbhd, mem_iInter.mpr P.mem_core⟩
    obtain ⟨y, ⟨hyN, hyA⟩, hyx⟩ := accPt_iff_nhds.mp hacc N hN
    have hy : y ∈ ⋃ i, D.piece i := D.inter_nbhd_eq ▸ ⟨hyA, hyN.1⟩
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    exact hyx (hsing i ⟨hyi, mem_iInter.mp hyN.2 i⟩)
  obtain ⟨i, hi⟩ := hpos
  have hxcl : x ∈ closure (P.good i) := P.subset_closure_good i ⟨P.mem_piece i, P.mem_core i⟩
  obtain ⟨c, hc⟩ := mem_closure_iff_nhds.mp hxcl univ univ_mem
  have hcreg : RegularAtDim (n := n) A c (D.dim i) := P.regularAtDim_of_mem_good i c hc.2
  have hgoodReg : P.good i ⊆ regularPoints (n := n) A := fun y hy =>
    ⟨D.dim i, P.regularAtDim_of_mem_good i y hy⟩
  have hcC : c ∈ component (n := n) A c := mem_connectedComponentIn (hgoodReg hc.2)
  have hgoodC : P.good i ⊆ component (n := n) A c :=
    (P.isPreconnected_good i).subset_connectedComponentIn hc.2 hgoodReg
  have hCA : component (n := n) A c ⊆ A := fun y hy =>
    (connectedComponentIn_subset _ _ hy : y ∈ regularPoints (n := n) A).choose_spec.2.1
  have hVA : closure (component (n := n) A c) ⊆ A := closure_minimal hCA hA.isClosed
  let V : ClosedIrreducibleAnalyticSubvariety n M :=
    { carrier := closure (component (n := n) A c)
      isClosed_carrier := isClosed_closure
      irreducible_carrier := isComplexAnalyticallyIrreducible_closure_component hA hcreg
      dim := D.dim i
      dim_le := hcreg.1
      regularLocus_nonempty := ⟨c, regularAtDim_closure_component hcreg hcC⟩ }
  refine ⟨V, ⟨hVA, fun Z hVZ hZA => ?_⟩, hi, closure_mono hgoodC hxcl⟩
  obtain ⟨W, hW, hcW, hAW⟩ := exists_open_inter_subset_component hcC
  refine (ClosureDifferenceAnalytic.eq_of_subset_of_inter_open_subset
    (isComplexAnalyticSubset_closure_component hA) Z.irreducible_carrier hVZ hW
    ⟨c, hVZ (subset_closure hcC), hcW⟩ ?_).symm
  intro z hz
  exact subset_closure (hAW ⟨hZA hz.1, hz.2⟩)

end SGPT.Foundations.Analysis.Pending.PositiveDimensionalComponent
