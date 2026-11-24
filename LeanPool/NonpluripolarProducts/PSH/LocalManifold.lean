/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.VariableAtlas

/-!
# Actual source PSH on open manifold subsets

Use ambient representatives, testing values only on the specified subset.
Connected coordinate witnesses are contained in that actual subset. The
existing one-center positive-measure producer is reused for nondegeneracy.
-/

@[expose] public section

namespace SGPT.PSH

open Set Filter Metric
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

/-- Actual non-bottom points in every relative open neighborhood. -/
def LocallyNondegenerateOn (u : X → EReal) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ O : Set X, IsOpen O → x ∈ O → ∃ y ∈ U ∩ O, u y ≠ ⊥

namespace VariableComplexAtlas

variable (A : VariableComplexAtlas X)

/-- The source local definition on an actual open manifold subset.
Values of the ambient representative outside this subset are unrestricted. -/
def IsPSHOn (u : X → EReal) (U : Set X) : Prop :=
  ∀ x ∈ U, ∃ i : A.Index, x ∈ (A.chart i).source ∧
    ∃ V : Set (ComplexModel (A.dimension i)), IsOpen V ∧ IsConnected V ∧
      V ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ∧
        A.chart i x ∈ V ∧ PSHOn (A.coordinate u i) V

variable {A}

theorem isPSHOn_univ_iff {u : X → EReal} : A.IsPSHOn u univ ↔ A.IsPSH u := by
  constructor
  · intro hu x
    obtain ⟨i, hi, V, hV, hc, hVe, hxV, huV⟩ := hu x (mem_univ x)
    exact ⟨i, hi, V, hV, hc, fun _ hz ↦ (hVe hz).1, hxV, huV⟩
  · intro hu x _
    obtain ⟨i, hi, V, hV, hc, hVe, hxV, huV⟩ := hu x
    exact ⟨i, hi, V, hV, hc, fun _ hz ↦ ⟨hVe hz, mem_univ _⟩, hxV, huV⟩

/-- Genuine overlap transport gives coordinate germs on the actual subset. -/
theorem IsPSHOn.chartPlurisubharmonic {u : X → EReal} {U : Set X}
    (hu : A.IsPSHOn u U) (i : A.Index) :
    SGPT.Foundations.Analysis.PlurisubharmonicOn (A.coordinate u i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
  intro z hz
  obtain ⟨j, hj, V, hV, _, _, hzV, huV⟩ := hu ((A.chart i).symm z) hz.2
  have hi := (A.chart i).map_target hz.1
  have hp := (A.chart_germ_iff u j i ((A.chart i).symm z) hj hi).mp
    (huV.disc.plurisubharmonicOn hV _ hzV)
  simpa only [(A.chart i).right_inv hz.1] using hp

/-- The source's never-top codomain is derived on the actual subset. -/
theorem IsPSHOn.ne_top {u : X → EReal} {U : Set X}
    (hu : A.IsPSHOn u U) {x : X} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨i, hi⟩ := A.cover x
  have h := (hu.chartPlurisubharmonic i _
    ⟨(A.chart i).map_source hi, by simpa only [Set.mem_preimage, (A.chart i).left_inv hi]
      using hx⟩).ne_top
  simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hi] using h

/-- Reuse the single existing coordinate measure argument at each center. -/
theorem IsPSHOn.locallyNondegenerate {u : X → EReal} {U : Set X}
    (hu : A.IsPSHOn u U) (hU : IsOpen U) : LocallyNondegenerateOn u U := by
  intro x hx O hO hxO
  obtain ⟨i, hi, V, hV, hc, _, hxV, huV⟩ := hu x hx
  exact exists_ne_bot_in_open_of_coordinate_psh (A.chart i) hi hV hc hxV huV
    (hU.inter hO) ⟨hx, hxO⟩

/-- Local actual nondegeneracy supplies non-bottom points in any actual
open coordinate neighborhood contained in the original subset. -/
theorem exists_coordinate_ne_bot_of_locallyNondegenerateOn {u : X → EReal} {U : Set X}
    (hnd : LocallyNondegenerateOn u U) (i : A.Index)
    {O : Set (ComplexModel (A.dimension i))} (hO : IsOpen O)
    (hOe : O ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U)
    {z : ComplexModel (A.dimension i)} (hz : z ∈ O) :
    ∃ y ∈ O, A.coordinate u i y ≠ ⊥ := by
  let V := (A.chart i).source ∩ (A.chart i) ⁻¹' O
  have hV : IsOpen V := (A.chart i).isOpen_inter_preimage hO
  have hzT := (hOe hz).1
  have hzV : (A.chart i).symm z ∈ V := by
    refine ⟨(A.chart i).map_target hzT, ?_⟩
    change A.chart i ((A.chart i).symm z) ∈ O
    simpa only [(A.chart i).right_inv hzT] using hz
  obtain ⟨y, hy, hfin⟩ := hnd ((A.chart i).symm z) (hOe hz).2 V hV hzV
  exact ⟨A.chart i y, hy.2.2,
    by simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hy.2.1] using hfin⟩

/-- Actual local source witnesses are equivalent to genuine coordinate germs
and actual neighborhood finite points, with no analytic certificate assumed. -/
theorem isPSHOn_iff_chart_and_nondegenerate {u : X → EReal} {U : Set X} (hU : IsOpen U) :
    A.IsPSHOn u U ↔
      (∀ i, SGPT.Foundations.Analysis.PlurisubharmonicOn (A.coordinate u i)
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) ∧ LocallyNondegenerateOn u U := by
  constructor
  · intro hu
    exact ⟨hu.chartPlurisubharmonic, hu.locallyNondegenerate hU⟩
  · rintro ⟨hcharts, hnd⟩ x hx
    obtain ⟨i, hi⟩ := A.cover x
    have hzT : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
      ⟨(A.chart i).map_source hi, by simpa only [Set.mem_preimage, (A.chart i).left_inv hi]
        using hx⟩
    obtain ⟨W, hW, hzW, hd⟩ := hcharts i _ hzT
    have hT := (A.chart i).isOpen_inter_preimage_symm hU
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (hW.inter hT) (A.chart i x) ⟨hzW, hzT⟩
    have hbe : ball (A.chart i x) r ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
      fun _ hz ↦ (hb hz).2
    refine ⟨i, hi, ball (A.chart i x) r, isOpen_ball, isConnected_ball hr, hbe,
      mem_ball_self hr, hd.mono (fun _ hz ↦ (hb hz).1), ?_⟩
    exact exists_coordinate_ne_bot_of_locallyNondegenerateOn hnd i isOpen_ball hbe
      (mem_ball_self hr)

/-- Actual source coordinate PSH on each connected neighborhood inside U. -/
theorem IsPSHOn.coordinate_pshOn_of_connected {u : X → EReal} {U : Set X}
    (hu : A.IsPSHOn u U) (hU : IsOpen U) (i : A.Index)
    {V : Set (ComplexModel (A.dimension i))} (hV : IsOpen V) (hc : IsConnected V)
    (hVe : V ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U) : PSHOn (A.coordinate u i) V := by
  obtain ⟨z, hz⟩ := hc.nonempty
  exact ⟨(hu.chartPlurisubharmonic i).discPshOn.mono hVe,
    exists_coordinate_ne_bot_of_locallyNondegenerateOn (hu.locallyNondegenerate hU)
      i hV hVe hz⟩

end VariableComplexAtlas
end SGPT.PSH
