/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section2Base
public import LeanPool.GraphMinor.GM07.Section2Euler
import LeanPool.GraphMinor.GM07.CuffIncidences
import LeanPool.GraphMinor.GM11.DrawingOps
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.Section4b
import LeanPool.GraphMinor.Surface.Circle
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Gluing
import LeanPool.GraphMinor.Surface.ModelCriterion
import LeanPool.GraphMinor.Surface.SideCut
import LeanPool.GraphMinor.Surface.SurfacePull
import LeanPool.GraphMinor.Surface.WordFold

/-!
# Graph Minors VII, (2.3): Minimum Valency of the Seam Graph of a Minimal Net

This file proves `(2.3)` (`minimalNet_minValency`, pages 216–217) of N. Robertson and P. D. Seymour,
*Graph Minors. VII. Disjoint paths on a surface*, J. Combin. Theory Ser. B 45 (1988) 212–254:
if `S` is a connected surface not homeomorphic to `Σ(0, 0, 0)`, `Σ(0, 0, 1)`, or `Σ(0, 1, 0)`, and
`J` is the seam graph for a minimal net `N` with respect to a proper graph `G` in `S`, then every
vertex `v ∈ J.V` has `3 ≤ vertexValency J v`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

namespace Net

/-! ## 1. Reversing and swapping pasted pairs in a net -/

/-- Reverse a curve `c : Curve D` by precomposing with `unitInterval.symm`. -/
def revCurve {D : Type u} [TopologicalSpace D] (c : Curve D) : Curve D :=
  c.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩

@[simp]
theorem revCurve_apply {D : Type u} [TopologicalSpace D] (c : Curve D) (t : unitInterval) :
    revCurve c t = c (unitInterval.symm t) :=
  rfl

theorem revCurve_zero {D : Type u} [TopologicalSpace D] (c : Curve D) :
    revCurve c 0 = c 1 := by
  simp [revCurve]

theorem revCurve_one {D : Type u} [TopologicalSpace D] (c : Curve D) :
    revCurve c 1 = c 0 := by
  simp [revCurve]

theorem injective_revCurve {D : Type u} [TopologicalSpace D] {c : Curve D}
    (hc : Function.Injective c) : Function.Injective (revCurve c) :=
  hc.comp unitInterval.symm_bijective.injective

@[simp]
theorem range_revCurve {D : Type u} [TopologicalSpace D] (c : Curve D) :
    range (revCurve c) = range c :=
  unitInterval.symm_bijective.surjective.range_comp c

theorem mem_Ioo_symm_iff {t : unitInterval} :
    unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 ↔ t ∈ Ioo (0 : unitInterval) 1 := by
  simp only [mem_Ioo, ← Subtype.coe_lt_coe, unitInterval.coe_symm_eq, Icc.coe_zero, Icc.coe_one]
  constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

@[simp]
theorem image_Ioo_revCurve {D : Type u} [TopologicalSpace D] (c : Curve D) :
    revCurve c '' Ioo (0 : unitInterval) 1 = c '' Ioo (0 : unitInterval) 1 := by
  ext x
  simp only [mem_image, revCurve_apply]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨unitInterval.symm t, mem_Ioo_symm_iff.mpr ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨unitInterval.symm t, mem_Ioo_symm_iff.mpr ht, by simp⟩

/-- Reverse the orientation of the `i₀`-th pair `(f i₀, g i₀)` in a net `N`. -/
def revPair (N : Net S) (i₀ : Fin N.r) : Net S where
  D := N.D
  topD := N.topD
  isSurface_D := N.isSurface_D
  isClosedDisc_D := N.isClosedDisc_D
  r := N.r
  f := fun i => if i = i₀ then revCurve (N.f i) else N.f i
  g := fun i => if i = i₀ then revCurve (N.g i) else N.g i
  φ := N.φ
  injective_f := fun i => by
    split_ifs
    · exact injective_revCurve (N.injective_f i)
    · exact N.injective_f i
  range_f_subset_bd := fun i => by
    split_ifs
    · rw [range_revCurve]; exact N.range_f_subset_bd i
    · exact N.range_f_subset_bd i
  injective_g := fun i => by
    split_ifs
    · exact injective_revCurve (N.injective_g i)
    · exact N.injective_g i
  range_g_subset_bd := fun i => by
    split_ifs
    · rw [range_revCurve]; exact N.range_g_subset_bd i
    · exact N.range_g_subset_bd i
  internally_disjoint_ff := fun i j hij x hx => by
    split_ifs with hj hi hi
    · rw [range_revCurve]
      exact N.internally_disjoint_ff i j hij (unitInterval.symm x) (mem_Ioo_symm_iff.mpr hx)
    · rw [range_revCurve]
      exact N.internally_disjoint_ff i j hij x hx
    · exact N.internally_disjoint_ff i j hij (unitInterval.symm x) (mem_Ioo_symm_iff.mpr hx)
    · exact N.internally_disjoint_ff i j hij x hx
  internally_disjoint_gg := fun i j hij x hx => by
    split_ifs with hj hi hi
    · rw [range_revCurve]
      exact N.internally_disjoint_gg i j hij (unitInterval.symm x) (mem_Ioo_symm_iff.mpr hx)
    · rw [range_revCurve]
      exact N.internally_disjoint_gg i j hij x hx
    · exact N.internally_disjoint_gg i j hij (unitInterval.symm x) (mem_Ioo_symm_iff.mpr hx)
    · exact N.internally_disjoint_gg i j hij x hx
  internally_disjoint_fg := fun i j x hx => by
    split_ifs with hj hi hi
    · rw [range_revCurve]
      exact N.internally_disjoint_fg i j (unitInterval.symm x) (mem_Ioo_symm_iff.mpr hx)
    · rw [range_revCurve]
      exact N.internally_disjoint_fg i j x hx
    · exact N.internally_disjoint_fg i j (unitInterval.symm x) (mem_Ioo_symm_iff.mpr hx)
    · exact N.internally_disjoint_fg i j x hx
  internally_disjoint_gf := fun i j x hx => by
    split_ifs with hj hi hi
    · rw [range_revCurve]
      exact N.internally_disjoint_gf i j (unitInterval.symm x) (mem_Ioo_symm_iff.mpr hx)
    · rw [range_revCurve]
      exact N.internally_disjoint_gf i j x hx
    · exact N.internally_disjoint_gf i j (unitInterval.symm x) (mem_Ioo_symm_iff.mpr hx)
    · exact N.internally_disjoint_gf i j x hx
  quotientMap_φ := N.quotientMap_φ
  pasting_eq := fun i x => by
    split_ifs
    · exact N.pasting_eq i (unitInterval.symm x)
    · exact N.pasting_eq i x
  interior_inj := N.interior_inj
  bd_eq_iff := fun x y => by
    rw [N.bd_eq_iff]
    have hrel : (fun a b : N.D => ∃ (i : Fin N.r) (t : unitInterval),
        a = N.f i t ∧ b = N.g i t) =
      (fun a b : N.D => ∃ (i : Fin N.r) (t : unitInterval),
        a = (if i = i₀ then revCurve (N.f i) else N.f i) t ∧
        b = (if i = i₀ then revCurve (N.g i) else N.g i) t) := by
      ext a b
      constructor
      · rintro ⟨i, t, rfl, rfl⟩
        by_cases hi : i = i₀
        · refine ⟨i, unitInterval.symm t, ?_, ?_⟩ <;> simp [hi]
        · refine ⟨i, t, ?_, ?_⟩ <;> simp [hi]
      · rintro ⟨i, t, ha, hb⟩
        by_cases hi : i = i₀
        · subst hi
          simp only [↓reduceIte, revCurve_apply] at ha hb
          exact ⟨i, unitInterval.symm t, ha, hb⟩
        · simp only [hi, ↓reduceIte] at ha hb
          exact ⟨i, t, ha, hb⟩
    rw [hrel]

@[simp]
theorem r_revPair (N : Net S) (i₀ : Fin N.r) :
    (N.revPair i₀).r = N.r :=
  rfl

@[simp]
theorem φ_revPair (N : Net S) (i₀ : Fin N.r) :
    (N.revPair i₀).φ = N.φ :=
  rfl

@[simp]
theorem f_revPair (N : Net S) (i₀ i : Fin N.r) :
    (N.revPair i₀).f i = if i = i₀ then revCurve (N.f i) else N.f i :=
  rfl

@[simp]
theorem g_revPair (N : Net S) (i₀ i : Fin N.r) :
    (N.revPair i₀).g i = if i = i₀ then revCurve (N.g i) else N.g i :=
  rfl

@[simp]
theorem seamU_revPair (N : Net S) (i₀ : Fin N.r) :
    (N.revPair i₀).seamU = N.seamU :=
  rfl

@[simp]
theorem seamV_revPair (N : Net S) (i₀ : Fin N.r) :
    (N.revPair i₀).seamV = N.seamV := by
  ext z
  change (∃ i : Fin N.r, N.φ (((if i = i₀ then revCurve (N.f i) else N.f i) : Curve N.D) 0) = z ∨
      N.φ (((if i = i₀ then revCurve (N.f i) else N.f i) : Curve N.D) 1) = z) ↔
    (∃ i : Fin N.r, N.φ (N.f i 0) = z ∨ N.φ (N.f i 1) = z)
  refine exists_congr fun i => ?_
  split_ifs with hi
  · simp [or_comm]
  · rfl

@[simp]
theorem isSeamGraphFor_revPair (N : Net S) (i₀ : Fin N.r) (J : Drawing S) :
    (N.revPair i₀).IsSeamGraphFor J ↔ N.IsSeamGraphFor J := by
  simp [IsSeamGraphFor]

@[simp]
theorem isNormalFor_revPair (N : Net S) (i₀ : Fin N.r) (G : Drawing S) :
    (N.revPair i₀).IsNormalFor G ↔ N.IsNormalFor G := by
  simp [IsNormalFor]

@[simp]
theorem bdVertexPreimageCard_revPair (N : Net S) (i₀ : Fin N.r) (G : Drawing S) :
    (N.revPair i₀).bdVertexPreimageCard G = N.bdVertexPreimageCard G :=
  rfl

@[simp]
theorem isMinimalFor_revPair (N : Net S) (i₀ : Fin N.r) (G : Drawing S) :
    (N.revPair i₀).IsMinimalFor G ↔ N.IsMinimalFor G := by
  simp only [IsMinimalFor, isNormalFor_revPair, bdVertexPreimageCard_revPair, r_revPair]

/-- Swap `f i₀` and `g i₀` at the `i₀`-th pair in a net `N`. -/
def swapPair (N : Net S) (i₀ : Fin N.r) : Net S where
  D := N.D
  topD := N.topD
  isSurface_D := N.isSurface_D
  isClosedDisc_D := N.isClosedDisc_D
  r := N.r
  f := fun i => if i = i₀ then N.g i else N.f i
  g := fun i => if i = i₀ then N.f i else N.g i
  φ := N.φ
  injective_f := fun i => by
    split_ifs
    · exact N.injective_g i
    · exact N.injective_f i
  range_f_subset_bd := fun i => by
    split_ifs
    · exact N.range_g_subset_bd i
    · exact N.range_f_subset_bd i
  injective_g := fun i => by
    split_ifs
    · exact N.injective_f i
    · exact N.injective_g i
  range_g_subset_bd := fun i => by
    split_ifs
    · exact N.range_f_subset_bd i
    · exact N.range_g_subset_bd i
  internally_disjoint_ff := fun i j hij x hx => by
    split_ifs with hj hi hi
    · exact N.internally_disjoint_gg i j hij x hx
    · exact N.internally_disjoint_fg i j x hx
    · exact N.internally_disjoint_gf i j x hx
    · exact N.internally_disjoint_ff i j hij x hx
  internally_disjoint_gg := fun i j hij x hx => by
    split_ifs with hj hi hi
    · exact N.internally_disjoint_ff i j hij x hx
    · exact N.internally_disjoint_gf i j x hx
    · exact N.internally_disjoint_fg i j x hx
    · exact N.internally_disjoint_gg i j hij x hx
  internally_disjoint_fg := fun i j x hx => by
    split_ifs with hj hi hi
    · exact N.internally_disjoint_gf i j x hx
    · have hij : i ≠ j := by rintro rfl; exact hi hj
      exact N.internally_disjoint_ff i j hij x hx
    · have hij : i ≠ j := by rintro rfl; exact hj hi
      exact N.internally_disjoint_gg i j hij x hx
    · exact N.internally_disjoint_fg i j x hx
  internally_disjoint_gf := fun i j x hx => by
    split_ifs with hj hi hi
    · exact N.internally_disjoint_fg i j x hx
    · have hij : i ≠ j := by rintro rfl; exact hi hj
      exact N.internally_disjoint_gg i j hij x hx
    · have hij : i ≠ j := by rintro rfl; exact hj hi
      exact N.internally_disjoint_ff i j hij x hx
    · exact N.internally_disjoint_gf i j x hx
  quotientMap_φ := N.quotientMap_φ
  pasting_eq := fun i x => by
    split_ifs
    · exact (N.pasting_eq i x).symm
    · exact N.pasting_eq i x
  interior_inj := N.interior_inj
  bd_eq_iff := fun x y => by
    rw [N.bd_eq_iff]
    constructor <;> intro h <;> induction h with
    | rel a b hab =>
      rcases hab with ⟨i, t, rfl, rfl⟩
      by_cases hi : i = i₀
      · refine Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨i, t, ?_, ?_⟩) <;> simp [hi]
      · refine Relation.EqvGen.rel _ _ ⟨i, t, ?_, ?_⟩ <;> simp [hi]
    | refl _ => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

@[simp]
theorem r_swapPair (N : Net S) (i₀ : Fin N.r) :
    (N.swapPair i₀).r = N.r :=
  rfl

@[simp]
theorem φ_swapPair (N : Net S) (i₀ : Fin N.r) :
    (N.swapPair i₀).φ = N.φ :=
  rfl

@[simp]
theorem f_swapPair (N : Net S) (i₀ i : Fin N.r) :
    (N.swapPair i₀).f i = if i = i₀ then N.g i else N.f i :=
  rfl

@[simp]
theorem g_swapPair (N : Net S) (i₀ i : Fin N.r) :
    (N.swapPair i₀).g i = if i = i₀ then N.f i else N.g i :=
  rfl

@[simp]
theorem seamU_swapPair (N : Net S) (i₀ : Fin N.r) :
    (N.swapPair i₀).seamU = N.seamU :=
  rfl

@[simp]
theorem seamV_swapPair (N : Net S) (i₀ : Fin N.r) :
    (N.swapPair i₀).seamV = N.seamV := by
  ext z
  change (∃ i : Fin N.r, N.φ (((if i = i₀ then N.g i else N.f i) : Curve N.D) 0) = z ∨
      N.φ (((if i = i₀ then N.g i else N.f i) : Curve N.D) 1) = z) ↔
    (∃ i : Fin N.r, N.φ (N.f i 0) = z ∨ N.φ (N.f i 1) = z)
  refine exists_congr fun i => ?_
  split_ifs with hi
  · rw [← N.pasting_eq i 0, ← N.pasting_eq i 1]
  · rfl

@[simp]
theorem isSeamGraphFor_swapPair (N : Net S) (i₀ : Fin N.r) (J : Drawing S) :
    (N.swapPair i₀).IsSeamGraphFor J ↔ N.IsSeamGraphFor J := by
  simp [IsSeamGraphFor]

@[simp]
theorem isNormalFor_swapPair (N : Net S) (i₀ : Fin N.r) (G : Drawing S) :
    (N.swapPair i₀).IsNormalFor G ↔ N.IsNormalFor G := by
  simp [IsNormalFor]

@[simp]
theorem bdVertexPreimageCard_swapPair (N : Net S) (i₀ : Fin N.r) (G : Drawing S) :
    (N.swapPair i₀).bdVertexPreimageCard G = N.bdVertexPreimageCard G :=
  rfl

@[simp]
theorem isMinimalFor_swapPair (N : Net S) (i₀ : Fin N.r) (G : Drawing S) :
    (N.swapPair i₀).IsMinimalFor G ↔ N.IsMinimalFor G := by
  simp only [IsMinimalFor, isNormalFor_swapPair, bdVertexPreimageCard_swapPair, r_swapPair]

/-! ## 2. Explicit edge decomposition of a seam graph -/

/-- The `i`-th interior seam curve `N.φ ∘ N.f i : C(unitInterval, S)`. -/
def interiorSeamCurve (N : Net S) (i : Fin N.r) : C(unitInterval, S) :=
  ⟨N.φ ∘ N.f i, N.quotientMap_φ.continuous.comp (N.f i).continuous⟩

/-- The `i`-th interior seam edge `(N.φ ∘ N.f i) '' Ioo 0 1`. -/
def interiorSeamEdge (N : Net S) (i : Fin N.r) : Set S :=
  N.interiorSeamCurve i '' Ioo (0 : unitInterval) 1

theorem e_int_mem_E [T2Space S] (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J)
    (i : Fin N.r) : N.interiorSeamEdge i ∈ J.E := by
  refine (Drawing.eq_edge_of_injOn_Ioo J (N.interiorSeamCurve i) ?_ ?_ ?_ ?_).1
  · rw [hJ.2.2]
    exact ⟨i, Or.inl rfl⟩
  · rw [hJ.2.2]
    exact ⟨i, Or.inr rfl⟩
  · intro t ht
    rw [hJ.2.1, hJ.2.2]
    exact ⟨⟨N.f i t, N.range_f_subset_bd i ⟨t, rfl⟩, rfl⟩, N.notMem_seamV_of_mem_Ioo i ht⟩
  · intro t₁ ht₁ t₂ _ h12
    rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht₁ h12 with hff | hfg
    · exact (N.injective_f i hff).symm
    · exact False.elim (N.internally_disjoint_gf i i t₁ ht₁ ⟨t₂, hfg⟩)

theorem e_int_isLink [T2Space S] (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J)
    (i : Fin N.r) :
    J.toGraph.IsLink (N.interiorSeamEdge i) (N.φ (N.f i 0)) (N.φ (N.f i 1)) := by
  refine (Drawing.eq_edge_of_injOn_Ioo J (N.interiorSeamCurve i) ?_ ?_ ?_ ?_).2
  · rw [hJ.2.2]
    exact ⟨i, Or.inl rfl⟩
  · rw [hJ.2.2]
    exact ⟨i, Or.inr rfl⟩
  · intro t ht
    rw [hJ.2.1, hJ.2.2]
    exact ⟨⟨N.f i t, N.range_f_subset_bd i ⟨t, rfl⟩, rfl⟩, N.notMem_seamV_of_mem_Ioo i ht⟩
  · intro t₁ ht₁ t₂ _ h12
    rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht₁ h12 with hff | hfg
    · exact (N.injective_f i hff).symm
    · exact False.elim (N.internally_disjoint_gf i i t₁ ht₁ ⟨t₂, hfg⟩)

theorem tilde_e_int [T2Space S] (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J)
    (i : Fin N.r) :
    tilde (N.interiorSeamEdge i) = {N.φ (N.f i 0), N.φ (N.f i 1)} := by
  rw [tilde_eq_closure_inter_V J (N.e_int_mem_E hJ i)]
  have hlink := N.e_int_isLink hJ i
  unfold Drawing.toGraph at hlink
  exact hlink.2.2.2

theorem e_int_injective (N : Net S) : Function.Injective N.interiorSeamEdge := by
  intro i j hij
  let t₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t₀]
  have hmem : N.interiorSeamCurve i t₀ ∈ N.interiorSeamEdge j := hij ▸ ⟨t₀, ht₀, rfl⟩
  rcases hmem with ⟨s, _, hs_eq⟩
  by_contra hne
  rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht₀ hs_eq.symm with hff | hfg
  · exact N.internally_disjoint_ff i j hne t₀ ht₀ ⟨s, hff⟩
  · exact N.internally_disjoint_gf i j t₀ ht₀ ⟨s, hfg⟩

theorem disjoint_e_int_bd (hS : IsSurface S) (N : Net S) (i : Fin N.r) :
    Disjoint (N.interiorSeamEdge i) (bd S) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, ht, rfl⟩ hbd
  exact N.notMem_bd_of_mem_Ioo hS i ht hbd

theorem seamGraph_edges_eq (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) :
    J.E = range N.interiorSeamEdge ∪ arcComponentsIn (bd S \ J.V) ∧
      Disjoint (range N.interiorSeamEdge) (arcComponentsIn (bd S \ J.V)) := by
  have : T2Space S := hS.2.1
  let A : Set S := (J.U \ J.V) \ bd S
  let B : Set S := bd S \ J.V
  have hA_eq : A = ⋃ i : Fin N.r, N.interiorSeamEdge i := by
    ext p
    simp only [A, interiorSeamEdge, interiorSeamCurve, ContinuousMap.coe_mk, Function.comp_apply,
      Set.mem_sdiff,
      mem_iUnion, mem_image]
    constructor
    · rintro ⟨⟨hpU, hpV⟩, hpbd⟩
      rw [hJ.2.1] at hpU
      rw [hJ.2.2] at hpV
      obtain ⟨x, hxbd, rfl⟩ := hpU
      obtain ⟨i, w, hw, hφw, -, -⟩ :=
        N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV hxbd hpbd hpV
      exact ⟨i, w, hw, hφw⟩
    · rintro ⟨i, t, ht, rfl⟩
      rw [hJ.2.1, hJ.2.2]
      exact ⟨⟨⟨N.f i t, N.range_f_subset_bd i ⟨t, rfl⟩, rfl⟩,
        N.notMem_seamV_of_mem_Ioo i ht⟩, N.notMem_bd_of_mem_Ioo hS i ht⟩
  let U₁ : Set S := ⋃ i : Fin N.r, range (N.interiorSeamCurve i)
  have hU₁_closed : IsClosed U₁ :=
    isClosed_iUnion_of_finite fun i => (isCompact_range (N.interiorSeamCurve i).continuous).isClosed
  have hA_sub_U₁ : A ⊆ U₁ := by
    rw [hA_eq]
    exact iUnion_mono fun i => image_subset_range _ _
  have hUV_eq : J.U \ J.V = A ∪ B := by
    ext p
    simp only [A, B, Set.mem_sdiff, mem_union]
    have hbd_sub : bd S ⊆ J.U := hJ.2.1 ▸ N.bd_subset_seamU
    by_cases hpbd : p ∈ bd S
    · exact ⟨fun ⟨_, hpV⟩ => Or.inr ⟨hpbd, hpV⟩,
        by rintro (⟨⟨_, hpV⟩, _⟩ | ⟨_, hpV⟩) <;> exact ⟨hbd_sub hpbd, hpV⟩⟩
    · constructor
      · intro hp
        exact Or.inl ⟨hp, hpbd⟩
      · rintro (⟨hp, _⟩ | ⟨hpbd', _⟩)
        · exact hp
        · exact False.elim (hpbd hpbd')
  have hAB_disj : ∀ x ∈ A ∪ B, x ∈ U₁ → x ∉ bd S := by
    intro x hx hu₁ hxbd
    rw [mem_iUnion] at hu₁
    rcases hu₁ with ⟨i, t, rfl⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · rw [← hUV_eq] at hx
      exact hx.2 (hJ.2.2 ▸ ⟨i, Or.inl rfl⟩)
    · rw [← hUV_eq] at hx
      exact hx.2 (hJ.2.2 ▸ ⟨i, Or.inr rfl⟩)
    · exact N.notMem_bd_of_mem_Ioo hS i ht hxbd
  have harc_union : J.E = arcComponentsIn A ∪ arcComponentsIn B := by
    change arcComponentsIn (J.U \ J.V) = _
    rw [hUV_eq]
    exact GM11.arcComponentsIn_union hU₁_closed (isClosed_bd S) hA_sub_U₁ sdiff_subset hAB_disj
  have harc_A : arcComponentsIn A = range N.interiorSeamEdge := by
    ext E
    simp only [mem_range]
    constructor
    · intro hE
      have hEJ : E ∈ J.E := harc_union ▸ Or.inl hE
      obtain ⟨p, hpE⟩ := hE.1
      have hpA : p ∈ A := hE.2.1 hpE
      rw [hA_eq, mem_iUnion] at hpA
      obtain ⟨i, hpi⟩ := hpA
      exact ⟨i, J.edge_eq_of_mem (N.e_int_mem_E hJ i) hEJ hpi hpE⟩
    · rintro ⟨i, rfl⟩
      rcases harc_union ▸ N.e_int_mem_E hJ i with hEA | hEB
      · exact hEA
      · obtain ⟨p, hp⟩ := hEB.1
        have hpA : p ∈ A := by
          rw [hA_eq, mem_iUnion]
          exact ⟨i, hp⟩
        exact False.elim (hpA.2 (hEB.2.1 hp).1)
  have hdisj_arc : Disjoint (range N.interiorSeamEdge) (arcComponentsIn B) := by
    rw [← harc_A, Set.disjoint_left]
    intro E hEA hEB
    obtain ⟨p, hp⟩ := hEA.1
    exact (hEA.2.1 hp).2 (hEB.2.1 hp).1
  exact ⟨harc_A ▸ harc_union, hdisj_arc⟩

/-! ## 3. Boundary vertices of a seam graph have valency at least 3 -/

/-- Every boundary vertex `v ∈ J.V ∩ bd S` of a seam graph `J` for any net `N` has
`3 ≤ vertexValency J v`. -/
theorem three_le_vertexValency_of_mem_bd (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) {v : S} (hvV : v ∈ J.V) (hv_bd : v ∈ bd S) :
    3 ≤ vertexValency J v := by
  have : T2Space S := hS.2.1
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin N.r, N.φ (N.f i₀ 0) = v ∨ N.φ (N.f i₀ 1) = v := by
    have hv_seamV : v ∈ N.seamV := hJ.2.2 ▸ hvV
    exact hv_seamV
  let e₀ := N.interiorSeamEdge i₀
  have he₀_E : e₀ ∈ J.E := N.e_int_mem_E hJ i₀
  have hv_tilde_e₀ : v ∈ tilde e₀ := by
    rw [N.tilde_e_int hJ i₀]
    rcases hi₀ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hv_inc_e₀ : J.VertexIncident v e₀ :=
    (vertexIncident_iff_mem_tilde J hvV he₀_E).mpr hv_tilde_e₀
  have he₀_ne_boundary : ∀ {e}, e ⊆ bd S → e₀ ≠ e := by
    intro e he_bd heq
    obtain ⟨x, hxe₀⟩ := he₀_E.1
    exact Set.disjoint_left.mp (N.disjoint_e_int_bd hS i₀) hxe₀ (he_bd (heq ▸ hxe₀))
  have hcuffs : arcComponentsIn (bd S \ J.V) ⊆ J.E := by
    rw [(N.seamGraph_edges_eq hS hJ).1]
    exact subset_union_right
  rcases exists_cuff_incident_edges_of_edge_cover hS hcuffs hvV hv_bd with
    ⟨e₁, he₁_E, he₁_bd, hv_inc_e₁, hncard_e₁⟩ |
    ⟨e₁, he₁_E, e₂, he₂_E, he₁_ne_e₂, he₁_bd, he₂_bd, hv_inc_e₁, hv_inc_e₂⟩
  · have h1_ge : 1 ≤ {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 1}.ncard := by
      have hsub1 : ({e₁} : Set (Set S)) ⊆
          {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 1} :=
        singleton_subset_iff.mpr ⟨he₁_E, hv_inc_e₁, hncard_e₁⟩
      have hle := ncard_le_ncard hsub1 (J.finite_edges.subset fun e he => he.1)
      rwa [ncard_singleton] at hle
    rcases ncard_tilde_of_mem_E J he₀_E with h2_e₀ | h1_e₀
    · have h2_ge : 1 ≤ {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 2}.ncard := by
        have hsub2 : ({e₀} : Set (Set S)) ⊆
            {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 2} :=
          singleton_subset_iff.mpr ⟨he₀_E, hv_inc_e₀, h2_e₀⟩
        have hle := ncard_le_ncard hsub2 (J.finite_edges.subset fun e he => he.1)
        rwa [ncard_singleton] at hle
      unfold vertexValency
      omega
    · have h1_ge2 : 2 ≤ {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 1}.ncard := by
        have hsub_pair : ({e₀, e₁} : Set (Set S)) ⊆
            {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 1} := by
          rintro e (rfl | rfl)
          · exact ⟨he₀_E, hv_inc_e₀, h1_e₀⟩
          · exact ⟨he₁_E, hv_inc_e₁, hncard_e₁⟩
        have hle := ncard_le_ncard hsub_pair (J.finite_edges.subset fun e he => he.1)
        rwa [ncard_pair (he₀_ne_boundary he₁_bd)] at hle
      unfold vertexValency
      omega
  · have he₀_ne_e₁ : e₀ ≠ e₁ := he₀_ne_boundary he₁_bd
    have he₀_ne_e₂ : e₀ ≠ e₂ := he₀_ne_boundary he₂_bd
    let S₂ := {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 2}
    let S₁ := {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 1}
    have hS₂_fin : S₂.Finite := J.finite_edges.subset fun e he => he.1
    have hS₁_fin : S₁.Finite := J.finite_edges.subset fun e he => he.1
    have hdisj_S : Disjoint S₂ S₁ := by
      rw [Set.disjoint_left]
      intro e he₂ he₁
      exact absurd (he₂.2.2.symm.trans he₁.2.2) (by decide)
    have hsub_three : ({e₀, e₁, e₂} : Set (Set S)) ⊆ S₂ ∪ S₁ := by
      rintro e (rfl | rfl | rfl)
      · rcases ncard_tilde_of_mem_E J he₀_E with h2 | h1
        · exact Or.inl ⟨he₀_E, hv_inc_e₀, h2⟩
        · exact Or.inr ⟨he₀_E, hv_inc_e₀, h1⟩
      · rcases ncard_tilde_of_mem_E J he₁_E with h2 | h1
        · exact Or.inl ⟨he₁_E, hv_inc_e₁, h2⟩
        · exact Or.inr ⟨he₁_E, hv_inc_e₁, h1⟩
      · rcases ncard_tilde_of_mem_E J he₂_E with h2 | h1
        · exact Or.inl ⟨he₂_E, hv_inc_e₂, h2⟩
        · exact Or.inr ⟨he₂_E, hv_inc_e₂, h1⟩
    have h3_le : 3 ≤ (S₂ ∪ S₁).ncard := by
      have hcard3 : ({e₀, e₁, e₂} : Set (Set S)).ncard = 3 := by
        rw [ncard_insert_of_notMem, ncard_pair he₁_ne_e₂]
        simp [he₀_ne_e₁, he₀_ne_e₂]
      rw [← hcard3]
      exact ncard_le_ncard hsub_three (hS₂_fin.union hS₁_fin)
    rw [ncard_union_eq hdisj_S hS₂_fin hS₁_fin] at h3_le
    unfold vertexValency
    change S₂.ncard + 2 * S₁.ncard ≥ 3
    omega

/-! ## 4. Interior vertex valency lower bound and boundary O-arc structure -/

/-- Any point `x ∈ bd N.D` with `N.φ x ∉ bd S` lies on `range (N.f i) ∪ range (N.g i)` for some
`i : Fin N.r`. -/
theorem mem_pasted_of_mem_bd_of_notMem_bd [T2Space S] (N : Net S)
    {x : N.D} (hx_bd : x ∈ bd N.D) (hx_not_bdS : N.φ x ∉ bd S) :
    x ∈ ⋃ i : Fin N.r, (range (N.f i) ∪ range (N.g i)) := by
  by_cases hxV : N.φ x ∈ N.seamV
  · have h := N.preimage_seamV_subset_endpoints hxV
    simp only [mem_iUnion, mem_insert_iff, mem_singleton_iff] at h
    rcases h with ⟨i, rfl | rfl | rfl | rfl⟩
    · exact mem_iUnion.mpr ⟨i, Or.inl ⟨0, rfl⟩⟩
    · exact mem_iUnion.mpr ⟨i, Or.inl ⟨1, rfl⟩⟩
    · exact mem_iUnion.mpr ⟨i, Or.inr ⟨0, rfl⟩⟩
    · exact mem_iUnion.mpr ⟨i, Or.inr ⟨1, rfl⟩⟩
  · obtain ⟨i, w, _, _, hfib, _⟩ :=
      N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV hx_bd hx_not_bdS hxV
    have hx_pair : x ∈ ({N.f i w, N.g i w} : Set N.D) := hfib ▸ rfl
    rcases hx_pair with rfl | rfl
    · exact mem_iUnion.mpr ⟨i, Or.inl ⟨w, rfl⟩⟩
    · exact mem_iUnion.mpr ⟨i, Or.inr ⟨w, rfl⟩⟩

/-- Every point of `bd N.D` lies either on one of the pasted boundary arcs `range (N.f i)`,
`range (N.g i)` (`i : Fin N.r`) or in `bd N.D ∩ N.φ ⁻¹' (bd S)`. -/
theorem bd_subset_pasted_union_preimage_bd [T2Space S] (N : Net S) :
    bd N.D ⊆ (⋃ i : Fin N.r, (range (N.f i) ∪ range (N.g i))) ∪ (bd N.D ∩ N.φ ⁻¹' (bd S)) := by
  intro x hx
  by_cases hx_bdS : N.φ x ∈ bd S
  · exact Or.inr ⟨hx, hx_bdS⟩
  · exact Or.inl (N.mem_pasted_of_mem_bd_of_notMem_bd hx hx_bdS)

/-- For an injective curve `c : Curve N.D` in `bd N.D`, its open interior `c '' Ioo 0 1` is one of
the two connected components `B₁, B₂` of `bd N.D \ {c 0, c 1}`, and `range c` is the closure
`Bᵢ ∪ {c 0, c 1}` of that component. -/
theorem curve_image_Ioo_eq_component (N : Net S) {c : Curve N.D}
    (hc_inj : Function.Injective c) (hc_bd : range c ⊆ bd N.D)
    {B₁ B₂ : Set N.D}
    (hcomp : componentsIn (bd N.D \ {c 0, c 1}) = {B₁, B₂}) :
    (c '' Ioo (0 : unitInterval) 1 = B₁ ∧ range c = B₁ ∪ {c 0, c 1}) ∨
      (c '' Ioo (0 : unitInterval) 1 = B₂ ∧ range c = B₂ ∪ {c 0, c 1}) := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hc0_bd : c 0 ∈ bd N.D := hc_bd ⟨0, rfl⟩
  have hc1_bd : c 1 ∈ bd N.D := hc_bd ⟨1, rfl⟩
  have hc01_ne : c 0 ≠ c 1 := fun h => zero_ne_one (hc_inj h)
  obtain ⟨B₁', B₂', hcomp', _, _, hline₁', hline₂'⟩ :=
    oArc_components_diff_pair N.isOArc_bd_D hc0_bd hc1_bd hc01_ne
  let t₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t₀]
  have hIoo_conn : IsPreconnected (c '' Ioo (0 : unitInterval) 1) :=
    isPreconnected_Ioo.image c c.continuous.continuousOn
  have hIoo_sub : c '' Ioo (0 : unitInterval) 1 ⊆ bd N.D \ {c 0, c 1} := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨hc_bd ⟨s, rfl⟩, ?_⟩
    rintro (h0 | h1)
    · exact hs.1.ne (hc_inj h0).symm
    · exact hs.2.ne (hc_inj (mem_singleton_iff.mp h1))
  let B := connectedComponentIn (bd N.D \ {c 0, c 1}) (c t₀)
  have hB_mem : B ∈ componentsIn (bd N.D \ {c 0, c 1}) :=
    ⟨c t₀, hIoo_sub ⟨t₀, ht₀, rfl⟩, rfl⟩
  have hB_line : IsLineWithEnds (B ∪ {c 0, c 1}) (c 0) (c 1) := by
    have hB_mem' : B ∈ ({B₁', B₂'} : Set (Set N.D)) := hcomp' ▸ hB_mem
    rcases hB_mem' with rfl | rfl
    · exact hline₁'
    · exact hline₂'
  have hIoo_sub_B : c '' Ioo (0 : unitInterval) 1 ⊆ B :=
    hIoo_conn.subset_connectedComponentIn ⟨t₀, ht₀, rfl⟩ hIoo_sub
  have hrange_sub : range c ⊆ B ∪ {c 0, c 1} := by
    rintro _ ⟨s, rfl⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl (hIoo_sub_B ⟨s, hs, rfl⟩)
  have hrange_eq : range c = B ∪ {c 0, c 1} :=
    hB_line.eq_of_subset (isPreconnected_range c.continuous) hrange_sub ⟨0, rfl⟩ ⟨1, rfl⟩
  have hB_sub_Ioo : B ⊆ c '' Ioo (0 : unitInterval) 1 := by
    intro y hy
    have hy_diff : y ∈ bd N.D \ {c 0, c 1} := connectedComponentIn_subset _ _ hy
    have hy_range : y ∈ range c := hrange_eq ▸ Or.inl hy
    rcases hy_range with ⟨s, rfl⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
    · exact False.elim (hy_diff.2 (Or.inl rfl))
    · exact False.elim (hy_diff.2 (Or.inr rfl))
    · exact ⟨s, hs, rfl⟩
  have hIoo_eq : c '' Ioo (0 : unitInterval) 1 = B :=
    Subset.antisymm hIoo_sub_B hB_sub_Ioo
  rw [hcomp] at hB_mem
  rcases hB_mem with rfl | rfl
  · exact Or.inl ⟨hIoo_eq, hrange_eq⟩
  · exact Or.inr ⟨hIoo_eq, hrange_eq⟩

/-- If `IsLineWithEnds (B ∪ {s, t}) s t` in a `T2Space`, then `B ∪ {s, t}` is closed and both `s`
and `t` lie in `closure B`. -/
theorem mem_closure_of_isLineWithEnds {X : Type*} [TopologicalSpace X] [T2Space X]
    {B : Set X} {s t : X} (hline : IsLineWithEnds (B ∪ {s, t}) s t) :
    IsClosed (B ∪ {s, t}) ∧ s ∈ closure B ∧ t ∈ closure B :=
  hline.isClosed_union_and_endpoints_mem_closure

/-- A single injective curve `c₀ : Curve N.D` in `bd N.D` and a closed set `K` missing an endpoint
`x ∈ {c₀ 0, c₀ 1}` cannot together cover `bd N.D`. -/
theorem not_bd_subset_range_union_closed (N : Net S) {c₀ : Curve N.D}
    (hc₀_inj : Function.Injective c₀) (hc₀_bd : range c₀ ⊆ bd N.D)
    {K : Set N.D} (hK : IsClosed K) {x : N.D} (hx : x = c₀ 0 ∨ x = c₀ 1) (hxK : x ∉ K) :
    ¬ (bd N.D ⊆ range c₀ ∪ K) := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hc0_bd : c₀ 0 ∈ bd N.D := hc₀_bd ⟨0, rfl⟩
  have hc1_bd : c₀ 1 ∈ bd N.D := hc₀_bd ⟨1, rfl⟩
  have hc01_ne : c₀ 0 ≠ c₀ 1 := fun h => zero_ne_one (hc₀_inj h)
  obtain ⟨B₁, B₂, hcomp, hdisj, hunion, hline₁, hline₂⟩ :=
    oArc_components_diff_pair N.isOArc_bd_D hc0_bd hc1_bd hc01_ne
  obtain ⟨_, hc0_cl₁, hc1_cl₁⟩ := mem_closure_of_isLineWithEnds hline₁
  obtain ⟨_, hc0_cl₂, hc1_cl₂⟩ := mem_closure_of_isLineWithEnds hline₂
  intro hcov
  rcases N.curve_image_Ioo_eq_component hc₀_inj hc₀_bd hcomp with ⟨_, hr₁⟩ | ⟨_, hr₂⟩
  · have hB₂_sub_K : B₂ ⊆ K := by
      intro y hy
      have hy_diff : y ∈ bd N.D \ {c₀ 0, c₀ 1} := hunion ▸ Or.inr hy
      rcases hcov hy_diff.1 with hy_c | hy_K
      · rw [hr₁] at hy_c
        rcases hy_c with hy_B₁ | hy_end
        · exact False.elim (hdisj.le_bot ⟨hy_B₁, hy⟩)
        · exact False.elim (hy_diff.2 hy_end)
      · exact hy_K
    have hcl_sub : closure B₂ ⊆ K := hK.closure_subset_iff.mpr hB₂_sub_K
    rcases hx with rfl | rfl
    · exact hxK (hcl_sub hc0_cl₂)
    · exact hxK (hcl_sub hc1_cl₂)
  · have hB₁_sub_K : B₁ ⊆ K := by
      intro y hy
      have hy_diff : y ∈ bd N.D \ {c₀ 0, c₀ 1} := hunion ▸ Or.inl hy
      rcases hcov hy_diff.1 with hy_c | hy_K
      · rw [hr₂] at hy_c
        rcases hy_c with hy_B₂ | hy_end
        · exact False.elim (hdisj.le_bot ⟨hy, hy_B₂⟩)
        · exact False.elim (hy_diff.2 hy_end)
      · exact hy_K
    have hcl_sub : closure B₁ ⊆ K := hK.closure_subset_iff.mpr hB₁_sub_K
    rcases hx with rfl | rfl
    · exact hxK (hcl_sub hc0_cl₁)
    · exact hxK (hcl_sub hc1_cl₁)

/-- Two internally disjoint injective curves `c₁, c₂ : Curve N.D` in `bd N.D` with the same
endpoints `c₁ 0 = c₂ 0` and `c₁ 1 = c₂ 1` cover all of `bd N.D`. -/
theorem range_union_eq_bd_of_same_ends (N : Net S) {c₁ c₂ : Curve N.D}
    (hc₁_inj : Function.Injective c₁) (hc₁_bd : range c₁ ⊆ bd N.D)
    (hc₂_inj : Function.Injective c₂) (hc₂_bd : range c₂ ⊆ bd N.D)
    (h0 : c₁ 0 = c₂ 0) (h1 : c₁ 1 = c₂ 1)
    (hdisj_Ioo : Disjoint (c₁ '' Ioo (0 : unitInterval) 1) (c₂ '' Ioo (0 : unitInterval) 1)) :
    range c₁ ∪ range c₂ = bd N.D := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hc0_bd : c₁ 0 ∈ bd N.D := hc₁_bd ⟨0, rfl⟩
  have hc1_bd : c₁ 1 ∈ bd N.D := hc₁_bd ⟨1, rfl⟩
  have hc01_ne : c₁ 0 ≠ c₁ 1 := fun h => zero_ne_one (hc₁_inj h)
  obtain ⟨B₁, B₂, hcomp, hdisj, hunion, _, _⟩ :=
    oArc_components_diff_pair N.isOArc_bd_D hc0_bd hc1_bd hc01_ne
  have hcomp₂ : componentsIn (bd N.D \ {c₂ 0, c₂ 1}) = {B₁, B₂} := by
    rwa [← h0, ← h1]
  let t₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t₀]
  have h_nonempty : (c₁ '' Ioo (0 : unitInterval) 1).Nonempty := ⟨c₁ t₀, t₀, ht₀, rfl⟩
  rcases N.curve_image_Ioo_eq_component hc₁_inj hc₁_bd hcomp with ⟨hI₁, hr₁⟩ | ⟨hI₁, hr₁⟩ <;>
    rcases N.curve_image_Ioo_eq_component hc₂_inj hc₂_bd hcomp₂ with ⟨hI₂, hr₂⟩ | ⟨hI₂, hr₂⟩
  · exfalso
    rw [hI₁, hI₂, disjoint_self, bot_eq_empty] at hdisj_Ioo
    exact h_nonempty.ne_empty (hI₁.trans hdisj_Ioo)
  · apply Subset.antisymm (union_subset hc₁_bd hc₂_bd)
    intro x hx
    by_cases hx_end : x ∈ ({c₁ 0, c₁ 1} : Set N.D)
    · exact Or.inl (hr₁ ▸ Or.inr hx_end)
    · rcases hunion ▸ (show x ∈ bd N.D \ {c₁ 0, c₁ 1} from ⟨hx, hx_end⟩) with hx₁ | hx₂
      · exact Or.inl (hr₁ ▸ Or.inl hx₁)
      · exact Or.inr (hr₂ ▸ Or.inl hx₂)
  · apply Subset.antisymm (union_subset hc₁_bd hc₂_bd)
    intro x hx
    by_cases hx_end : x ∈ ({c₁ 0, c₁ 1} : Set N.D)
    · exact Or.inl (hr₁ ▸ Or.inr hx_end)
    · rcases hunion ▸ (show x ∈ bd N.D \ {c₁ 0, c₁ 1} from ⟨hx, hx_end⟩) with hx₁ | hx₂
      · exact Or.inr (hr₂ ▸ Or.inl hx₁)
      · exact Or.inl (hr₁ ▸ Or.inl hx₂)
  · exfalso
    rw [hI₁, hI₂, disjoint_self, bot_eq_empty] at hdisj_Ioo
    exact h_nonempty.ne_empty (hI₁.trans hdisj_Ioo)

/-- If two internally disjoint injective curves `c₁, c₂ : Curve N.D` in `bd N.D` share their start
endpoint `c₁ 0 = c₂ 0 = x` and have distinct end endpoints `c₁ 1 ≠ c₂ 1` (with `c₁ 1 ∉ range c₂`
and `c₂ 1 ∉ range c₁`), then `bd N.D \ {c₁ 1, c₂ 1}` splits into two components `B, B'` where
`B = (c₁ '' Ico 0 1) ∪ (c₂ '' Ico 0 1)` is open in `bd N.D` around `x`, and `B' ∪ {c₁ 1, c₂ 1}` is
a closed `I`-arc in `bd N.D` with ends `c₁ 1, c₂ 1`. -/
theorem two_curves_common_end_component (N : Net S) {c₁ c₂ : Curve N.D}
    (hc₁_inj : Function.Injective c₁) (hc₁_bd : range c₁ ⊆ bd N.D)
    (hc₂_inj : Function.Injective c₂) (hc₂_bd : range c₂ ⊆ bd N.D)
    (h0 : c₁ 0 = c₂ 0) (h1_ne : c₁ 1 ≠ c₂ 1)
    (hc₁1_not : c₁ 1 ∉ range c₂) (hc₂1_not : c₂ 1 ∉ range c₁) :
    ∃ B B' : Set N.D,
      Disjoint B B' ∧
      bd N.D \ {c₁ 1, c₂ 1} = B ∪ B' ∧
      B = (c₁ '' Ico (0 : unitInterval) 1) ∪ (c₂ '' Ico (0 : unitInterval) 1) ∧
      range c₁ ∪ range c₂ = B ∪ {c₁ 1, c₂ 1} ∧
      bd N.D \ ((c₁ '' Ico (0 : unitInterval) 1) ∪ (c₂ '' Ico (0 : unitInterval) 1)) =
        B' ∪ {c₁ 1, c₂ 1} ∧
      IsClosed (B' ∪ {c₁ 1, c₂ 1}) ∧
      IsLineWithEnds (B' ∪ {c₁ 1, c₂ 1}) (c₁ 1) (c₂ 1) := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hc₁1_bd : c₁ 1 ∈ bd N.D := hc₁_bd ⟨1, rfl⟩
  have hc₂1_bd : c₂ 1 ∈ bd N.D := hc₂_bd ⟨1, rfl⟩
  obtain ⟨B₁, B₂, hcomp, hdisj, hunion, hline₁, hline₂⟩ :=
    oArc_components_diff_pair N.isOArc_bd_D hc₁1_bd hc₂1_bd h1_ne
  have hIco₁_sub : c₁ '' Ico (0 : unitInterval) 1 ⊆ bd N.D \ {c₁ 1, c₂ 1} := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨hc₁_bd ⟨s, rfl⟩, ?_⟩
    rintro (h1 | h2)
    · exact hs.2.ne (hc₁_inj h1)
    · exact hc₂1_not ⟨s, mem_singleton_iff.mp h2⟩
  have hIco₂_sub : c₂ '' Ico (0 : unitInterval) 1 ⊆ bd N.D \ {c₁ 1, c₂ 1} := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨hc₂_bd ⟨s, rfl⟩, ?_⟩
    rintro (h1 | h2)
    · exact hc₁1_not ⟨s, h1⟩
    · exact hs.2.ne (hc₂_inj (mem_singleton_iff.mp h2))
  have h0_Ico : (0 : unitInterval) ∈ Ico (0 : unitInterval) 1 :=
    ⟨le_rfl, Subtype.coe_lt_coe.mp zero_lt_one⟩
  have hx_diff : c₁ 0 ∈ bd N.D \ {c₁ 1, c₂ 1} := hIco₁_sub ⟨0, h0_Ico, rfl⟩
  let B := connectedComponentIn (bd N.D \ {c₁ 1, c₂ 1}) (c₁ 0)
  have hB_mem : B ∈ ({B₁, B₂} : Set (Set N.D)) := hcomp ▸ ⟨c₁ 0, hx_diff, rfl⟩
  have hIco₁_B : c₁ '' Ico (0 : unitInterval) 1 ⊆ B :=
    (isPreconnected_Ico.image c₁ c₁.continuous.continuousOn).subset_connectedComponentIn
      ⟨0, h0_Ico, rfl⟩ hIco₁_sub
  have hIco₂_B : c₂ '' Ico (0 : unitInterval) 1 ⊆ B :=
    (isPreconnected_Ico.image c₂ c₂.continuous.continuousOn).subset_connectedComponentIn
      (h0 ▸ ⟨0, h0_Ico, rfl⟩) hIco₂_sub
  have hrange_conn : IsPreconnected (range c₁ ∪ range c₂) :=
    (isPreconnected_range c₁.continuous).union' ⟨c₁ 0, ⟨0, rfl⟩, h0 ▸ ⟨0, rfl⟩⟩
      (isPreconnected_range c₂.continuous)
  have hrange_sub : range c₁ ∪ range c₂ ⊆ B ∪ {c₁ 1, c₂ 1} := by
    rintro y (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
      · exact Or.inl (hIco₁_B ⟨0, h0_Ico, rfl⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (hIco₁_B ⟨s, ⟨hs.1.le, hs.2⟩, rfl⟩)
    · rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
      · exact Or.inl (hIco₂_B ⟨0, h0_Ico, rfl⟩)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl (hIco₂_B ⟨s, ⟨hs.1.le, hs.2⟩, rfl⟩)
  have hhelper : ∀ {Ba Bb : Set N.D},
      Disjoint Ba Bb → bd N.D \ {c₁ 1, c₂ 1} = Ba ∪ Bb → B = Ba →
      IsLineWithEnds (Ba ∪ {c₁ 1, c₂ 1}) (c₁ 1) (c₂ 1) →
      IsLineWithEnds (Bb ∪ {c₁ 1, c₂ 1}) (c₁ 1) (c₂ 1) →
      Disjoint Ba Bb ∧
      bd N.D \ {c₁ 1, c₂ 1} = Ba ∪ Bb ∧
      Ba = (c₁ '' Ico (0 : unitInterval) 1) ∪ (c₂ '' Ico (0 : unitInterval) 1) ∧
      range c₁ ∪ range c₂ = Ba ∪ {c₁ 1, c₂ 1} ∧
      bd N.D \ ((c₁ '' Ico (0 : unitInterval) 1) ∪ (c₂ '' Ico (0 : unitInterval) 1)) =
        Bb ∪ {c₁ 1, c₂ 1} ∧
      IsClosed (Bb ∪ {c₁ 1, c₂ 1}) ∧
      IsLineWithEnds (Bb ∪ {c₁ 1, c₂ 1}) (c₁ 1) (c₂ 1) := by
    intro Ba Bb hd hu hBa hline_a hline_b
    subst hBa
    have hrange_eq : range c₁ ∪ range c₂ = B ∪ {c₁ 1, c₂ 1} :=
      hline_a.eq_of_subset hrange_conn hrange_sub (Or.inl ⟨1, rfl⟩) (Or.inr ⟨1, rfl⟩)
    have hB_eq : B = (c₁ '' Ico (0 : unitInterval) 1) ∪ (c₂ '' Ico (0 : unitInterval) 1) := by
      apply Subset.antisymm
      · intro y hyB
        have hy_diff : y ∈ bd N.D \ {c₁ 1, c₂ 1} := connectedComponentIn_subset _ _ hyB
        have hy_r : y ∈ range c₁ ∪ range c₂ := hrange_eq ▸ Or.inl hyB
        rcases hy_r with ⟨s, rfl⟩ | ⟨s, rfl⟩
        · rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
          · exact Or.inl ⟨0, h0_Ico, rfl⟩
          · exact False.elim (hy_diff.2 (Or.inl rfl))
          · exact Or.inl ⟨s, ⟨hs.1.le, hs.2⟩, rfl⟩
        · rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
          · exact Or.inr ⟨0, h0_Ico, rfl⟩
          · exact False.elim (hy_diff.2 (Or.inr rfl))
          · exact Or.inr ⟨s, ⟨hs.1.le, hs.2⟩, rfl⟩
      · exact union_subset hIco₁_B hIco₂_B
    have hdiff_eq : bd N.D \ ((c₁ '' Ico (0 : unitInterval) 1) ∪ (c₂ '' Ico (0 : unitInterval) 1)) =
        Bb ∪ {c₁ 1, c₂ 1} := by
      rw [← hB_eq]
      ext y
      constructor
      · rintro ⟨hy_bd, hy_not_B⟩
        by_cases hy_end : y ∈ ({c₁ 1, c₂ 1} : Set N.D)
        · exact Or.inr hy_end
        · have hy_u : y ∈ B ∪ Bb := hu ▸ ⟨hy_bd, hy_end⟩
          exact Or.inl (hy_u.resolve_left hy_not_B)
      · rintro (hy_Bb | hy_end)
        · have hy_diff : y ∈ bd N.D \ {c₁ 1, c₂ 1} := hu ▸ Or.inr hy_Bb
          exact ⟨hy_diff.1, fun hyB => hd.le_bot ⟨hyB, hy_Bb⟩⟩
        · refine ⟨?_, fun hyB => (connectedComponentIn_subset _ _ hyB).2 hy_end⟩
          rcases hy_end with rfl | h2
          · exact hc₁1_bd
          · exact (mem_singleton_iff.mp h2) ▸ hc₂1_bd
    exact ⟨hd, hu, hB_eq, hrange_eq, hdiff_eq, (mem_closure_of_isLineWithEnds hline_b).1, hline_b⟩
  rcases hB_mem with hB1 | hB2
  · exact ⟨B₁, B₂, hhelper hdisj hunion hB1 hline₁ hline₂⟩
  · have hB2' : B = B₂ := mem_singleton_iff.mp hB2
    exact ⟨B₂, B₁, hhelper hdisj.symm (union_comm B₁ B₂ ▸ hunion) hB2' hline₂ hline₁⟩

/-- Three pairwise internally disjoint injective curves `c₁, c₂, c₃ : Curve N.D` in `bd N.D` cannot
share a common start endpoint `c₁ 0 = c₂ 0 = c₃ 0`. -/
theorem not_three_curves_common_end (N : Net S) {c₁ c₂ c₃ : Curve N.D}
    (hc₁_inj : Function.Injective c₁) (hc₁_bd : range c₁ ⊆ bd N.D)
    (hc₂_inj : Function.Injective c₂) (hc₂_bd : range c₂ ⊆ bd N.D)
    (hc₃_bd : range c₃ ⊆ bd N.D)
    (h0_12 : c₁ 0 = c₂ 0) (h0_13 : c₁ 0 = c₃ 0)
    (hdisj_12 : ∀ t ∈ Ioo (0 : unitInterval) 1, c₁ t ∉ range c₂)
    (hdisj_21 : ∀ t ∈ Ioo (0 : unitInterval) 1, c₂ t ∉ range c₁)
    (hdisj_31 : ∀ t ∈ Ioo (0 : unitInterval) 1, c₃ t ∉ range c₁)
    (hdisj_32 : ∀ t ∈ Ioo (0 : unitInterval) 1, c₃ t ∉ range c₂) :
    False := by
  let t₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t₀]
  have hd_Ioo_12 : Disjoint (c₁ '' Ioo (0 : unitInterval) 1) (c₂ '' Ioo (0 : unitInterval) 1) := by
    rw [disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ ⟨s, _, hs⟩
    exact hdisj_12 t ht ⟨s, hs⟩
  by_cases h1 : c₁ 1 = c₂ 1
  · have hcov := N.range_union_eq_bd_of_same_ends hc₁_inj hc₁_bd hc₂_inj hc₂_bd h0_12 h1 hd_Ioo_12
    have hc₃_bd_t₀ : c₃ t₀ ∈ range c₁ ∪ range c₂ := hcov ▸ hc₃_bd ⟨t₀, rfl⟩
    rcases hc₃_bd_t₀ with h1_mem | h2_mem
    · exact hdisj_31 t₀ ht₀ h1_mem
    · exact hdisj_32 t₀ ht₀ h2_mem
  · have hc₁1_not : c₁ 1 ∉ range c₂ := by
      rintro ⟨s, hs⟩
      rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs_Ioo
      · exact zero_ne_one (hc₁_inj (h0_12.trans hs))
      · exact h1 hs.symm
      · exact hdisj_21 s hs_Ioo ⟨1, hs.symm⟩
    have hc₂1_not : c₂ 1 ∉ range c₁ := by
      rintro ⟨s, hs⟩
      rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs_Ioo
      · exact zero_ne_one (hc₂_inj (h0_12.symm.trans hs))
      · exact h1 hs
      · exact hdisj_12 s hs_Ioo ⟨1, hs.symm⟩
    obtain ⟨B, B', hdisj, _, hB_eq, _, hdiff_eq, hcl_B', _⟩ :=
      N.two_curves_common_end_component hc₁_inj hc₁_bd hc₂_inj hc₂_bd h0_12 h1 hc₁1_not hc₂1_not
    have hIoo₃_sub : c₃ '' Ioo (0 : unitInterval) 1 ⊆ B' ∪ {c₁ 1, c₂ 1} := by
      rw [← hdiff_eq]
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨hc₃_bd ⟨t, rfl⟩, ?_⟩
      rintro (⟨s, _, hs⟩ | ⟨s, _, hs⟩)
      · exact hdisj_31 t ht ⟨s, hs⟩
      · exact hdisj_32 t ht ⟨s, hs⟩
    have hcl_Ioo : (0 : unitInterval) ∈ closure (Ioo (0 : unitInterval) 1) := by
      rw [closure_Ioo zero_ne_one]
      exact left_mem_Icc.mpr (Subtype.coe_le_coe.mp zero_le_one)
    have hc₃0_cl : c₃ 0 ∈ closure (c₃ '' Ioo (0 : unitInterval) 1) :=
      image_closure_subset_closure_image c₃.continuous ⟨0, hcl_Ioo, rfl⟩
    have hc₃0_B' : c₁ 0 ∈ B' ∪ {c₁ 1, c₂ 1} :=
      h0_13.symm ▸ hcl_B'.closure_subset_iff.mpr hIoo₃_sub hc₃0_cl
    have hc₁0_B : c₁ 0 ∈ B := by
      rw [hB_eq]
      exact Or.inl ⟨0, ⟨le_rfl, Subtype.coe_lt_coe.mp zero_lt_one⟩, rfl⟩
    rcases hc₃0_B' with hB' | (h1_eq | h2_eq)
    · exact hdisj.le_bot ⟨hc₁0_B, hB'⟩
    · exact zero_ne_one (hc₁_inj h1_eq)
    · exact hc₂1_not ⟨0, mem_singleton_iff.mp h2_eq⟩

/-- The set of indices `i : Fin N.r` such that `N.interiorSeamEdge i` has `v` as one of two distinct
endpoints
(`(N.φ (N.f i 0) = v ∧ N.φ (N.f i 1) ≠ v) ∨ (N.φ (N.f i 0) ≠ v ∧ N.φ (N.f i 1) = v)`). -/
noncomputable def F₁ (N : Net S) (v : S) : Finset (Fin N.r) := by
  classical
  exact Finset.univ.filter fun i =>
    (N.φ (N.f i 0) = v ∧ N.φ (N.f i 1) ≠ v) ∨ (N.φ (N.f i 0) ≠ v ∧ N.φ (N.f i 1) = v)

/-- The set of indices `i : Fin N.r` such that `N.interiorSeamEdge i` is a loop at `v`
(`N.φ (N.f i 0) = v ∧ N.φ (N.f i 1) = v`). -/
noncomputable def F₂ (N : Net S) (v : S) : Finset (Fin N.r) := by
  classical
  exact Finset.univ.filter fun i => N.φ (N.f i 0) = v ∧ N.φ (N.f i 1) = v

theorem mem_F₁_iff (N : Net S) (v : S) (i : Fin N.r) :
    i ∈ N.F₁ v ↔
      (N.φ (N.f i 0) = v ∧ N.φ (N.f i 1) ≠ v) ∨ (N.φ (N.f i 0) ≠ v ∧ N.φ (N.f i 1) = v) := by
  classical
  simp [F₁]

theorem mem_F₂_iff (N : Net S) (v : S) (i : Fin N.r) :
    i ∈ N.F₂ v ↔ N.φ (N.f i 0) = v ∧ N.φ (N.f i 1) = v := by
  classical
  simp [F₂]

theorem notMem_F₁_and_notMem_F₂_iff (N : Net S) (v : S) (i : Fin N.r) :
    (i ∉ N.F₁ v ∧ i ∉ N.F₂ v) ↔ N.φ (N.f i 0) ≠ v ∧ N.φ (N.f i 1) ≠ v := by
  rw [mem_F₁_iff, mem_F₂_iff]
  by_cases h0 : N.φ (N.f i 0) = v <;> by_cases h1 : N.φ (N.f i 1) = v <;> simp [h0, h1]

/-- For every vertex `v ∈ J.V` of a seam graph `J` for `N`, the interior seam edges alone contribute
at least `(N.F₁ v).card + 2 * (N.F₂ v).card` to `vertexValency J v`. -/
theorem card_F₁_add_two_mul_card_F₂_le_vertexValency [T2Space S] (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) (v : S) :
    (N.F₁ v).card + 2 * (N.F₂ v).card ≤ vertexValency J v := by
  let S₂ := {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 2}
  let S₁ := {e ∈ J.E | J.VertexIncident v e ∧ (tilde e).ncard = 1}
  have hS₂_fin : S₂.Finite := J.finite_edges.subset fun e he => he.1
  have hS₁_fin : S₁.Finite := J.finite_edges.subset fun e he => he.1
  have h1 : (N.F₁ v).card ≤ S₂.ncard := by
    have hsub : N.interiorSeamEdge '' (N.F₁ v : Set (Fin N.r)) ⊆ S₂ := by
      rintro _ ⟨i, hi, rfl⟩
      rw [ Finset.mem_coe, mem_F₁_iff ] at hi
      have heE : N.interiorSeamEdge i ∈ J.E := N.e_int_mem_E hJ i
      have htilde : tilde (N.interiorSeamEdge i) = {N.φ (N.f i 0), N.φ (N.f i 1)}
        := N.tilde_e_int hJ i
      rcases hi with ⟨h0, hne⟩ | ⟨hne, h1⟩
      · have hvV : v ∈ J.V := hJ.2.2 ▸ ⟨i, Or.inl h0⟩
        have hv_tilde : v ∈ tilde (N.interiorSeamEdge i) := htilde ▸ Or.inl h0.symm
        refine ⟨heE, (vertexIncident_iff_mem_tilde J hvV heE).mpr hv_tilde, ?_⟩
        rw [htilde, h0, ncard_pair hne.symm]
      · have hvV : v ∈ J.V := hJ.2.2 ▸ ⟨i, Or.inr h1⟩
        have hv_tilde : v ∈ tilde (N.interiorSeamEdge i) := htilde ▸ Or.inr h1.symm
        refine ⟨heE, (vertexIncident_iff_mem_tilde J hvV heE).mpr hv_tilde, ?_⟩
        rw [htilde, h1, ncard_pair hne]
    have hle := ncard_le_ncard hsub hS₂_fin
    rwa [ncard_image_of_injective _ N.e_int_injective, ncard_coe_finset] at hle
  have h2 : (N.F₂ v).card ≤ S₁.ncard := by
    have hsub : N.interiorSeamEdge '' (N.F₂ v : Set (Fin N.r)) ⊆ S₁ := by
      rintro _ ⟨i, hi, rfl⟩
      rw [ Finset.mem_coe, mem_F₂_iff ] at hi
      rcases hi with ⟨h0, h1⟩
      have heE : N.interiorSeamEdge i ∈ J.E := N.e_int_mem_E hJ i
      have htilde : tilde (N.interiorSeamEdge i) = {v} := by
        rw [N.tilde_e_int hJ i, h0, h1, pair_eq_singleton]
      have hvV : v ∈ J.V := hJ.2.2 ▸ ⟨i, Or.inl h0⟩
      have hv_tilde : v ∈ tilde (N.interiorSeamEdge i) := htilde ▸ rfl
      refine ⟨heE, (vertexIncident_iff_mem_tilde J hvV heE).mpr hv_tilde, ?_⟩
      rw [htilde, ncard_singleton]
    have hle := ncard_le_ncard hsub hS₁_fin
    rwa [ncard_image_of_injective _ N.e_int_injective, ncard_coe_finset] at hle
  unfold vertexValency
  change (N.F₁ v).card + 2 * (N.F₂ v).card ≤ S₂.ncard + 2 * S₁.ncard
  omega

/-- On a surface `S` not homeomorphic to `Σ(0, 0, 0)`, `Σ(0, 1, 0)`, or `Σ(0, 0, 1)`, no seam pair
`i₀ : Fin N.r` can have both endpoint images outside `bd S` and `range (N.f i₀) ∪ range (N.g i₀)`
disjoint from `range (N.f j) ∪ range (N.g j)` for all `j ≠ i₀` (otherwise connectedness of `bd N.D`
forces `N.r = 1` and `bd S = ∅`, contradicting Euler's formula (2.2)). -/
theorem not_isolated_pair_of_not_sphere_proj_disc (hS : IsSurface S)
    (h000 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 0))
    (h010 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 1 0))
    (h001 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 1))
    (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J) (i₀ : Fin N.r)
    (hf0_not_bd : N.φ (N.f i₀ 0) ∉ bd S)
    (hf1_not_bd : N.φ (N.f i₀ 1) ∉ bd S)
    (hdisj_other : ∀ j : Fin N.r, j ≠ i₀ →
      Disjoint (range (N.f i₀) ∪ range (N.g i₀)) (range (N.f j) ∪ range (N.g j))) :
    False := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  let K₀ : Set N.D := range (N.f i₀) ∪ range (N.g i₀)
  let K₁ : Set N.D :=
    (⋃ j ∈ ({i₀}ᶜ : Set (Fin N.r)), (range (N.f j) ∪ range (N.g j))) ∪ (bd N.D ∩ N.φ ⁻¹' (bd S))
  have hK₀_not_bdS : ∀ x ∈ K₀, N.φ x ∉ bd S := by
    rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
      · exact hf0_not_bd
      · exact hf1_not_bd
      · intro hbd
        have hmem_e : N.φ (N.f i₀ t) ∈ N.interiorSeamEdge i₀ := ⟨t, ht, rfl⟩
        exact (N.disjoint_e_int_bd hS i₀).le_bot ⟨hmem_e, hbd⟩
    · rw [← N.pasting_eq i₀ t]
      rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
      · exact hf0_not_bd
      · exact hf1_not_bd
      · intro hbd
        have hmem_e : N.φ (N.f i₀ t) ∈ N.interiorSeamEdge i₀ := ⟨t, ht, rfl⟩
        exact (N.disjoint_e_int_bd hS i₀).le_bot ⟨hmem_e, hbd⟩
  have hK₀_closed : IsClosed K₀ :=
    (isCompact_range (N.f i₀).continuous).isClosed.union
      (isCompact_range (N.g i₀).continuous).isClosed
  have hK₁_closed : IsClosed K₁ := by
    refine ((toFinite ({i₀}ᶜ : Set (Fin N.r))).isClosed_biUnion fun j _ => ?_).union ?_
    · exact (isCompact_range (N.f j).continuous).isClosed.union
        (isCompact_range (N.g j).continuous).isClosed
    · exact (isClosed_bd N.D).inter ((isClosed_bd S).preimage N.quotientMap_φ.continuous)
  have hcov : bd N.D ⊆ K₀ ∪ K₁ := by
    intro x hx
    rcases N.bd_subset_pasted_union_preimage_bd hx with hx_pasted | hx_bdS
    · rw [mem_iUnion] at hx_pasted
      rcases hx_pasted with ⟨j, hj⟩
      by_cases hij : j = i₀
      · subst hij
        exact Or.inl hj
      · exact Or.inr (Or.inl (mem_biUnion hij hj))
    · exact Or.inr (Or.inr hx_bdS)
  have hdisj_K : Disjoint K₀ K₁ := by
    rw [disjoint_left]
    intro x hx₀ hx₁
    rcases hx₁ with hx_other | hx_bdS
    · rw [mem_iUnion₂] at hx_other
      rcases hx_other with ⟨j, hj, hx_j⟩
      exact (hdisj_other j hj).le_bot ⟨hx₀, hx_j⟩
    · exact hK₀_not_bdS x hx₀ hx_bdS.2
  have hK₁_empty : bd N.D ∩ K₁ = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro y ⟨hy_bd, hy₁⟩
    obtain ⟨z, _, hz₀, hz₁⟩ := isPreconnected_closed_iff.mp
      N.isOArc_bd_D.isPreconnected K₀ K₁ hK₀_closed hK₁_closed hcov
      ⟨N.f i₀ 0, N.range_f_subset_bd i₀ ⟨0, rfl⟩, Or.inl ⟨0, rfl⟩⟩
      ⟨y, hy_bd, hy₁⟩
    exact hdisj_K.le_bot ⟨hz₀, hz₁⟩
  have hall_eq_i₀ : ∀ j : Fin N.r, j = i₀ := by
    intro j
    by_contra hij
    have hmem : N.f j 0 ∈ bd N.D ∩ K₁ :=
      ⟨N.range_f_subset_bd j ⟨0, rfl⟩, Or.inl (mem_biUnion hij (Or.inl ⟨0, rfl⟩))⟩
    rw [hK₁_empty] at hmem
    exact hmem
  have hbdS_empty : bd S = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨x, hx_bd, rfl⟩ := N.bd_subset_seamU hz
    have hmem : x ∈ bd N.D ∩ K₁ := ⟨hx_bd, Or.inr ⟨hx_bd, hz⟩⟩
    rw [hK₁_empty] at hmem
    exact hmem
  have hE_eq : J.E = {N.interiorSeamEdge i₀} := by
    rw [(N.seamGraph_edges_eq hS hJ).1]
    ext e
    simp only [mem_union, mem_range, mem_singleton_iff]
    constructor
    · rintro (⟨j, rfl⟩ | he_bd)
      · rw [hall_eq_i₀ j]
      · exfalso
        obtain ⟨⟨z, hze⟩, hsub, _⟩ := he_bd
        have hz_bdS : z ∈ bd S := (hsub hze).1
        rw [hbdS_empty] at hz_bdS
        exact hz_bdS
    · rintro rfl
      exact Or.inl ⟨i₀, rfl⟩
  have hE_ncard : J.E.ncard = 1 := by
    rw [hE_eq, ncard_singleton]
  have hV_eq : J.V = {N.φ (N.f i₀ 0), N.φ (N.f i₀ 1)} := by
    rw [hJ.2.2]
    ext z
    simp only [seamV, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨j, hj⟩
      rw [hall_eq_i₀ j] at hj
      exact hj.imp Eq.symm Eq.symm
    · rintro (rfl | rfl)
      · exact ⟨i₀, Or.inl rfl⟩
      · exact ⟨i₀, Or.inr rfl⟩
  have hV_pos : 1 ≤ J.V.ncard := by
    rw [hV_eq]
    by_cases heq : N.φ (N.f i₀ 0) = N.φ (N.f i₀ 1)
    · rw [heq, pair_eq_singleton, ncard_singleton]
    · rw [ncard_pair heq]; omega
  have hconn_univ_D : ConnectedSpace (univ : Set N.D) :=
    Subtype.connectedSpace N.isClosedDisc_D.isPathConnected.isConnected
  have hconn_D : ConnectedSpace N.D :=
    (Homeomorph.Set.univ N.D).surjective.connectedSpace (Homeomorph.Set.univ N.D).continuous
  have hconn_S : ConnectedSpace S :=
    N.quotientMap_φ.surjective.connectedSpace N.quotientMap_φ.continuous
  obtain ⟨a, b, c, he⟩ := classification S hS hconn_S
  have heuler := seamGraph_euler_formula S hS a b c he J ⟨N, hJ⟩
  rw [hE_ncard] at heuler
  have habc_le : 2 * a + b + c ≤ 1 := by omega
  rcases ( by omega : (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c
    = 1) ) with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h000 he
  · exact h010 he
  · exact h001 he

/-! ## 5. Excluding Case 1 (`F₂.card = 1, F₁.card = 0`) and Case 3 (`F₂.card = 0, F₁.card = 2`) -/

/-- If `v ∈ N.seamV` and `N.φ (N.f j 0) ≠ v` and `N.φ (N.f j 1) ≠ v`, then no point of
`range (N.f j) ∪ range (N.g j)` maps to `v` under `N.φ`. -/
theorem not_φ_eq_of_mem_range_fg (N : Net S) {v : S} (hv : v ∈ N.seamV) {j : Fin N.r}
    (hf0 : N.φ (N.f j 0) ≠ v) (hf1 : N.φ (N.f j 1) ≠ v)
    {x : N.D} (hx : x ∈ range (N.f j) ∪ range (N.g j)) :
    N.φ x ≠ v := by
  intro hφ
  have hφ_f : ∃ t : unitInterval, N.φ (N.f j t) = v := by
    rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact ⟨t, hφ⟩
    · exact ⟨t, (N.pasting_eq j t).trans hφ⟩
  rcases hφ_f with ⟨t, ht_eq⟩
  rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
  · exact hf0 ht_eq
  · exact hf1 ht_eq
  · exact N.notMem_seamV_of_mem_Ioo j ht (ht_eq.symm ▸ hv)

/-- Excluding Subcase B2a (`(N.F₂ v).card = 1` and `(N.F₁ v).card = 0`): a single loop seam edge at
an interior vertex `v ∉ bd S` with no other seam edges incident with `v` is impossible on a surface
not homeomorphic to `Σ(0, 0, 0)`, `Σ(0, 1, 0)`, or `Σ(0, 0, 1)`. -/
theorem not_loop_only_at_interior_vertex (hS : IsSurface S)
    (h000 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 0))
    (h010 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 1 0))
    (h001 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 1))
    (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J)
    {v : S} (hv_not_bd : v ∉ bd S) (i₀ : Fin N.r)
    (hi₀_0 : N.φ (N.f i₀ 0) = v) (hi₀_1 : N.φ (N.f i₀ 1) = v)
    (hother : ∀ j : Fin N.r, j ≠ i₀ → N.φ (N.f j 0) ≠ v ∧ N.φ (N.f j 1) ≠ v) :
    False := by
  have hv_seamV : v ∈ N.seamV := ⟨i₀, Or.inl hi₀_0⟩
  refine N.not_isolated_pair_of_not_sphere_proj_disc hS h000 h010 h001 hJ i₀
    (hi₀_0.symm ▸ hv_not_bd) (hi₀_1.symm ▸ hv_not_bd) fun j hj => ?_
  rw [disjoint_left]
  intro x hx₀ hxj
  have hnot_v : N.φ x ≠ v :=
    N.not_φ_eq_of_mem_range_fg hv_seamV (hother j hj).1 (hother j hj).2 hxj
  rcases hx₀ with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · exact hnot_v hi₀_0
    · exact hnot_v hi₀_1
    · rcases hxj with hf_j | hg_j
      · exact N.internally_disjoint_ff i₀ j hj.symm t ht hf_j
      · exact N.internally_disjoint_fg i₀ j t ht hg_j
  · rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · exact hnot_v ((N.pasting_eq i₀ 0).symm.trans hi₀_0)
    · exact hnot_v ((N.pasting_eq i₀ 1).symm.trans hi₀_1)
    · rcases hxj with hf_j | hg_j
      · exact N.internally_disjoint_gf i₀ j t ht hf_j
      · exact N.internally_disjoint_gg i₀ j hj.symm t ht hg_j

/-- Concatenate two curves `c₁, c₂ : Curve D` with `c₁ 1 = c₂ 0` via `Path.trans`. -/
noncomputable def concatCurve {D : Type u} [TopologicalSpace D] (c₁ c₂ : Curve D) (h12 : c₁ 1
  = c₂ 0) :
    Curve D :=
  ((⟨c₁, rfl, rfl⟩ : Path (c₁ 0) (c₁ 1)).trans ⟨c₂, h12.symm, rfl⟩).toContinuousMap

@[simp]
theorem concatCurve_zero {D : Type u} [TopologicalSpace D] (c₁ c₂ : Curve D) (h12 : c₁ 1 = c₂ 0) :
    concatCurve c₁ c₂ h12 0 = c₁ 0 :=
  ((⟨c₁, rfl, rfl⟩ : Path (c₁ 0) (c₁ 1)).trans ⟨c₂, h12.symm, rfl⟩).source

@[simp]
theorem concatCurve_one {D : Type u} [TopologicalSpace D] (c₁ c₂ : Curve D) (h12 : c₁ 1 = c₂ 0) :
    concatCurve c₁ c₂ h12 1 = c₂ 1 :=
  ((⟨c₁, rfl, rfl⟩ : Path (c₁ 0) (c₁ 1)).trans ⟨c₂, h12.symm, rfl⟩).target

@[simp]
theorem range_concatCurve {D : Type u} [TopologicalSpace D] (c₁ c₂ : Curve D) (h12 : c₁ 1 = c₂ 0) :
    range (concatCurve c₁ c₂ h12) = range c₁ ∪ range c₂ :=
  Path.trans_range (⟨c₁, rfl, rfl⟩ : Path (c₁ 0) (c₁ 1)) ⟨c₂, h12.symm, rfl⟩

theorem concatCurve_apply {D : Type u} [TopologicalSpace D] (c₁ c₂ : Curve D) (h12 : c₁ 1 = c₂ 0)
    (t : unitInterval) :
    concatCurve c₁ c₂ h12 t =
      if h : (t : ℝ) ≤ 1 / 2 then
        c₁ ⟨2 * (t : ℝ), ⟨by linarith [t.2.1], by linarith⟩⟩
      else
        c₂ ⟨2 * (t : ℝ) - 1, ⟨by linarith, by linarith [t.2.2]⟩⟩ :=
  Path.trans_apply (⟨c₁, rfl, rfl⟩ : Path (c₁ 0) (c₁ 1)) ⟨c₂, h12.symm, rfl⟩ t

theorem injective_concatCurve {D : Type u} [TopologicalSpace D] {c₁ c₂ : Curve D}
    (h12 : c₁ 1 = c₂ 0) (hc₁ : Function.Injective c₁) (hc₂ : Function.Injective c₂)
    (h01_ne : c₁ 0 ≠ c₂ 1)
    (hdisj₁₂ : ∀ t ∈ Ioo (0 : unitInterval) 1, c₁ t ∉ range c₂)
    (hdisj₂₁ : ∀ t ∈ Ioo (0 : unitInterval) 1, c₂ t ∉ range c₁) :
    Function.Injective (concatCurve c₁ c₂ h12) := by
  have hcross : ∀ (t₁ t₂ : unitInterval) (ht₁ : (t₁ : ℝ) ≤ 1 / 2) (ht₂ : ¬ (t₂ : ℝ) ≤ 1 / 2),
      c₁ ⟨2 * (t₁ : ℝ), ⟨by linarith [t₁.2.1], by linarith⟩⟩ =
        c₂ ⟨2 * (t₂ : ℝ) - 1, ⟨by linarith, by linarith [t₂.2.2]⟩⟩ →
      t₁ = t₂ := by
    intro t₁ t₂ ht₁ ht₂ heq
    let u₁ : unitInterval := ⟨2 * (t₁ : ℝ), ⟨by linarith [t₁.2.1], by linarith⟩⟩
    let u₂ : unitInterval := ⟨2 * (t₂ : ℝ) - 1, ⟨by linarith, by linarith [t₂.2.2]⟩⟩
    change c₁ u₁ = c₂ u₂ at heq
    have hu₂_pos : (0 : unitInterval) < u₂ := by
      rw [← Subtype.coe_lt_coe]
      change (0 : ℝ) < 2 * (t₂ : ℝ) - 1
      linarith
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo u₂ with hu₂0 | hu₂1 | hu₂_Ioo
    · exact False.elim (hu₂_pos.ne' hu₂0)
    · rcases unitInterval_eq_zero_or_one_or_mem_Ioo u₁ with hu₁0 | hu₁1 | hu₁_Ioo
      · exfalso
        have h : c₁ 0 = c₂ 1 := by simpa [hu₁0, hu₂1] using heq
        exact h01_ne h
      · exfalso
        have h : c₂ 0 = c₂ 1 := by
          rw [← h12]
          simpa [hu₁1, hu₂1] using heq
        exact zero_ne_one (hc₂ h)
      · exact False.elim (hdisj₁₂ u₁ hu₁_Ioo ⟨u₂, heq.symm⟩)
    · exact False.elim (hdisj₂₁ u₂ hu₂_Ioo ⟨u₁, heq⟩)
  intro t₁ t₂ h
  rw [concatCurve_apply, concatCurve_apply] at h
  split_ifs at h with ht₁ ht₂ ht₂
  · have hu := hc₁ h
    have hreal : 2 * (t₁ : ℝ) = 2 * (t₂ : ℝ) := congr_arg Subtype.val hu
    exact Subtype.ext (by linarith)
  · exact hcross t₁ t₂ ht₁ ht₂ h
  · exact (hcross t₂ t₁ ht₂ ht₁ h.symm).symm
  · have hu := hc₂ h
    have hreal : 2 * (t₁ : ℝ) - 1 = 2 * (t₂ : ℝ) - 1 := congr_arg Subtype.val hu
    exact Subtype.ext (by linarith)

theorem mem_Ioo_concatCurve {D : Type u} [TopologicalSpace D] {c₁ c₂ : Curve D}
    (h12 : c₁ 1 = c₂ 0) {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1) :
    concatCurve c₁ c₂ h12 t ∈
      (c₁ '' Ioo (0 : unitInterval) 1) ∪ {c₁ 1} ∪ (c₂ '' Ioo (0 : unitInterval) 1) := by
  have ht0 : (0 : ℝ) < t := Subtype.coe_lt_coe.mpr ht.1
  have ht1 : (t : ℝ) < 1 := Subtype.coe_lt_coe.mpr ht.2
  rw [concatCurve_apply]
  split_ifs with hle
  · rcases eq_or_lt_of_le hle with heq | hlt
    · left; right
      rw [mem_singleton_iff]
      congr 1
      ext
      change 2 * (t : ℝ) = 1
      linarith
    · left; left
      refine ⟨⟨2 * (t : ℝ), ⟨by linarith, by linarith⟩⟩, ?_, rfl⟩
      constructor <;> rw [← Subtype.coe_lt_coe]
      · change (0 : ℝ) < 2 * (t : ℝ); linarith
      · change 2 * (t : ℝ) < 1; linarith
  · right
    refine ⟨⟨2 * (t : ℝ) - 1, ⟨by linarith, by linarith⟩⟩, ?_, rfl⟩
    constructor <;> rw [← Subtype.coe_lt_coe]
    · change (0 : ℝ) < 2 * (t : ℝ) - 1; linarith
    · change 2 * (t : ℝ) - 1 < 1; linarith

/-- Every seam curve `N.interiorSeamCurve i` carries a drawing with underlying set `range
(N.interiorSeamCurve i)` and
vertex set `{N.φ (N.f i 0), N.φ (N.f i 1)}`. -/
theorem exists_drawing_range_c_int [T2Space S] (N : Net S) (i : Fin N.r) :
    ∃ D : Drawing S, D.U = range (N.interiorSeamCurve i) ∧ D.V = {N.φ (N.f i 0), N.φ (N.f i 1)}
      := by
  let γ : unitInterval → S := N.interiorSeamCurve i
  have hγ : Continuous γ := (N.interiorSeamCurve i).continuous
  have hinj_Ioo : ∀ {s t : unitInterval}, s ∈ Ioo (0 : unitInterval) 1 →
      γ s = γ t → s = t := by
    intro s t hs hst
    rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i hs hst with hff | hfg
    · exact (N.injective_f i hff).symm
    · exact False.elim (N.internally_disjoint_gf i i s hs ⟨t, hfg⟩)
  by_cases h01 : N.φ (N.f i 0) = N.φ (N.f i 1)
  · have hpair_eq : ({N.φ (N.f i 0), N.φ (N.f i 1)} : Set S) = {N.φ (N.f i 0)} := by
      rw [h01, pair_eq_singleton]
    rw [hpair_eq]
    have hinj : ∀ s t : unitInterval, γ s = γ t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
      intro s t h
      rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
      · rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact False.elim (ht.1.ne' (hinj_Ioo ht h.symm))
      · rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inl rfl
        · exact False.elim (ht.2.ne (hinj_Ioo ht h.symm))
      · exact Or.inl (hinj_Ioo hs h)
    let q : unitInterval → Circle := GM11.arcParam 1
    have hq : Continuous q := (GM11.arcParam 1).continuous
    have hqs : Function.Surjective q := GM11.arcParam_surjective 1
    have hqq : Topology.IsQuotientMap q := hq.isClosedMap.isQuotientMap hq hqs
    let G : Circle → S := fun z => γ (Function.surjInv hqs z)
    have hGq : G ∘ q = γ := by
      funext t
      have hsi : q (Function.surjInv hqs (q t)) = q t := Function.surjInv_eq hqs _
      change γ (Function.surjInv hqs (q t)) = γ t
      rcases GM11.arcParam_eq_iff 1 hsi with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h]
      · rw [h₁, h₂]; exact h01
      · rw [h₁, h₂]; exact h01.symm
    have hG : Continuous G := hqq.continuous_iff.mpr (hGq ▸ hγ)
    have hGi : Function.Injective G := by
      intro z w h
      rw [← Function.surjInv_eq hqs z, ← Function.surjInv_eq hqs w]
      rcases hinj _ _ h with h' | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h']
      · rw [h₁, h₂]; change GM11.arcParam 1 0 = GM11.arcParam 1 1; simp
      · rw [h₁, h₂]; change GM11.arcParam 1 1 = GM11.arcParam 1 0; simp
    have hrange : range G = range γ := by
      rw [← hGq, range_comp, hqs.range_eq, image_univ]
    have hO : IsOArc (range γ) := by
      rw [← hrange]
      exact ⟨(hG.isClosedEmbedding hGi).isEmbedding.toHomeomorph⟩
    exact GM11.exists_loop_drawing hO ⟨0, rfl⟩
  · have hinj : Function.Injective γ := by
      intro s t h
      rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
      · rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · rfl
        · exact False.elim (h01 h)
        · exact (hinj_Ioo ht h.symm).symm
      · rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · exact False.elim (h01 h.symm)
        · rfl
        · exact (hinj_Ioo ht h.symm).symm
      · exact hinj_Ioo hs h
    have hL : IsLineWithEnds (range γ) (N.φ (N.f i 0)) (N.φ (N.f i 1)) :=
      GM11.isLine_range hγ hinj
    exact ⟨GM11.lineDrawing hL h01, rfl, rfl⟩

/-- Every net `N` with `0 < N.r` on a surface `S` has a seam graph `J : Drawing S`. -/
theorem exists_isSeamGraphFor (hS : IsSurface S) (N : Net S) (hr : 0 < N.r) :
    ∃ J : Drawing S, N.IsSeamGraphFor J := by
  classical
  have : T2Space S := hS.2.1
  have hbd_step : ∀ 𝓐 : Set (Set S), 𝓐.Finite → 𝓐 ⊆ cuffs S →
      ∃ D : Drawing S, D.U = N.seamV ∪ ⋃₀ 𝓐 ∧ D.V = N.seamV := by
    intro 𝓐 h𝓐
    induction 𝓐, h𝓐 using Set.Finite.induction_on with
    | empty =>
      intro _
      exact ⟨GM11.pointsDrawing N.finite_seamV, by simp [GM11.pointsDrawing], rfl⟩
    | @insert C 𝓐 hC_not_mem h𝓐_fin ih =>
      intro hsub
      have hC : C ∈ cuffs S := hsub (mem_insert _ _)
      have h𝓐_sub : 𝓐 ⊆ cuffs S := (subset_insert _ _).trans hsub
      obtain ⟨D₁, hU₁, hV₁⟩ := ih h𝓐_sub
      have hO : IsOArc C := (cuff_statement S hS).2.2 C hC
      have hCV_fin : (C ∩ N.seamV).Finite := N.finite_seamV.inter_of_right C
      have hCV_ne : (C ∩ N.seamV).Nonempty := N.cuff_inter_seamV_nonempty hS hr hC
      obtain ⟨D₂, hU₂, hV₂⟩ := GM11.exists_drawing_on_oArc hO hCV_fin hCV_ne inter_subset_left
      have hmeet : D₁.U ∩ D₂.U ⊆ D₁.V ∩ D₂.V := by
        rw [hU₁, hV₁, hU₂, hV₂]
        rintro x ⟨hxV | ⟨C', hC', hxC'⟩, hxC⟩
        · exact ⟨hxV, hxC, hxV⟩
        · have hne : C ≠ C' := fun h => hC_not_mem (h ▸ hC')
          exact False.elim (Set.disjoint_left.mp (cuffs_disjoint hC (h𝓐_sub hC') hne) hxC hxC')
      refine ⟨D₁.glue D₂ hmeet, ?_, ?_⟩
      · change D₁.U ∪ D₂.U = _
        rw [hU₁, hU₂, sUnion_insert]
        ext x; simp only [mem_union]; tauto
      · change D₁.V ∪ D₂.V = _
        rw [hV₁, hV₂, union_eq_left.mpr inter_subset_right]
  obtain ⟨D_bd, hU_bd, hV_bd⟩ := hbd_step (cuffs S) (cuff_statement S hS).2.1 Subset.rfl
  rw [sUnion_cuffs] at hU_bd
  have hint_step : ∀ T : Finset (Fin N.r),
      ∃ D : Drawing S, D.U = N.seamV ∪ bd S ∪ (⋃ i ∈ T, range (N.interiorSeamCurve i)) ∧ D.V
        = N.seamV := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      exact ⟨D_bd, by simp [hU_bd], hV_bd⟩
    | insert i T hi_not_mem ih =>
      obtain ⟨D₁, hU₁, hV₁⟩ := ih
      obtain ⟨D₂, hU₂, hV₂⟩ := N.exists_drawing_range_c_int i
      have hV₂_sub : D₂.V ⊆ N.seamV := by
        rw [hV₂]
        rintro x (rfl | rfl)
        · exact ⟨i, Or.inl rfl⟩
        · exact ⟨i, Or.inr rfl⟩
      have hmeet : D₁.U ∩ D₂.U ⊆ D₁.V ∩ D₂.V := by
        rw [hU₁, hV₁, hU₂, hV₂]
        rintro x ⟨hx₁, t, rfl⟩
        rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · exact ⟨⟨i, Or.inl rfl⟩, Or.inl rfl⟩
        · exact ⟨⟨i, Or.inr rfl⟩, Or.inr rfl⟩
        · exfalso
          rcases hx₁ with (hxV | hxbd) | hxi
          · exact N.notMem_seamV_of_mem_Ioo i ht hxV
          · exact N.notMem_bd_of_mem_Ioo hS i ht hxbd
          · rw [mem_iUnion₂] at hxi
            rcases hxi with ⟨j, hjT, s, hs_eq⟩
            have hij : i ≠ j := fun h => hi_not_mem (h ▸ hjT)
            rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht hs_eq.symm with hff | hfg
            · exact N.internally_disjoint_ff i j hij t ht ⟨s, hff⟩
            · exact N.internally_disjoint_gf i j t ht ⟨s, hfg⟩
      refine ⟨D₁.glue D₂ hmeet, ?_, ?_⟩
      · change D₁.U ∪ D₂.U = _
        rw [hU₁, hU₂, Finset.set_biUnion_insert, union_assoc]
        congr 1
        exact union_comm _ _
      · change D₁.V ∪ D₂.V = _
        rw [hV₁, union_eq_left.mpr hV₂_sub]
  obtain ⟨J, hUJ, hVJ⟩ := hint_step Finset.univ
  refine ⟨J, hr, ?_, hVJ⟩
  rw [hUJ]
  apply Subset.antisymm
  · rintro x ((hxV | hxbd) | hxi)
    · rcases hxV with ⟨i, rfl | rfl⟩
      · exact ⟨N.f i 0, N.range_f_subset_bd i ⟨0, rfl⟩, rfl⟩
      · exact ⟨N.f i 1, N.range_f_subset_bd i ⟨1, rfl⟩, rfl⟩
    · exact N.bd_subset_seamU hxbd
    · rw [mem_iUnion₂] at hxi
      rcases hxi with ⟨i, _, t, rfl⟩
      exact ⟨N.f i t, N.range_f_subset_bd i ⟨t, rfl⟩, rfl⟩
  · rintro p ⟨x, hxbd, rfl⟩
    by_cases hpbd : N.φ x ∈ bd S
    · exact Or.inl (Or.inr hpbd)
    · by_cases hpV : N.φ x ∈ N.seamV
      · exact Or.inl (Or.inl hpV)
      · obtain ⟨i, t, _, hφt, -, -⟩ :=
          N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV hxbd hpbd hpV
        exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, t, hφt⟩)

/-- A net `N` on a surface `S` is `G`-normal if and only if `0 < N.r` and `G.IsNormal N.seamU`. -/
theorem isNormalFor_iff (hS : IsSurface S) (N : Net S) (G : Drawing S) :
    N.IsNormalFor G ↔ 0 < N.r ∧ G.IsNormal N.seamU := by
  constructor
  · rintro ⟨J, ⟨hr, hU, _⟩, hnorm⟩
    exact ⟨hr, hU ▸ hnorm⟩
  · rintro ⟨hr, hnorm⟩
    obtain ⟨J, hJ⟩ := N.exists_isSeamGraphFor hS hr
    exact ⟨J, hJ, hJ.2.1.symm ▸ hnorm⟩

open Classical in
private noncomputable abbrev join_adjacent_net_pairs
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    {v : S}
    {i₁ : Fin N.r}
    {i₂ : Fin N.r}
    (hi₁_1 : N.φ ((N.f i₁) 1) = v)
    (hother : ∀ (j : Fin N.r), j ≠ i₁ → j ≠ i₂ → N.φ ((N.f j) 0) ≠ v ∧ N.φ ((N.f j) 1) ≠ v)
    (hf12 : (N.f i₁) 1 = (N.f i₂) 0)
    (hg12 : (N.g i₁) 1 = (N.g i₂) 0)
    (hv_seamV : v ∈ N.seamV)
    (hinj_f_cat : Function.Injective ⇑(concatCurve (N.f i₁) (N.f i₂) hf12))
    (hinj_g_cat : Function.Injective ⇑(concatCurve (N.g i₁) (N.g i₂) hg12))
    (hf1_notMem_g1 : (N.f i₁) 1 ∉ range ⇑(N.g i₁))
    (hf1_notMem_g2 : (N.f i₁) 1 ∉ range ⇑(N.g i₂))
    (hg1_notMem_f1 : (N.g i₁) 1 ∉ range ⇑(N.f i₁))
    (hg1_notMem_f2 : (N.g i₁) 1 ∉ range ⇑(N.f i₂))
    (k₀ : Fin (N.r - 1))
    (idx : Fin (N.r - 1) → Fin N.r)
    (hidx_inj : Function.Injective idx)
    (hidx_ne_i₂ : ∀ (k : Fin (N.r - 1)), idx k ≠ i₂)
    (hidx_ne_i₁ : ∀ (k : Fin (N.r - 1)), k ≠ k₀ → idx k ≠ i₁)
    (hsurj_other : ∀ (j : Fin N.r), j ≠ i₁ → j ≠ i₂ → ∃ k, k ≠ k₀ ∧ idx k = j) : Net S :=
  let f_cat := concatCurve (N.f i₁) (N.f i₂) hf12
  let g_cat := concatCurve (N.g i₁) (N.g i₂) hg12
  {
    D := N.D
    isSurface_D := N.isSurface_D
    isClosedDisc_D := N.isClosedDisc_D
    φ := N.φ
    quotientMap_φ := N.quotientMap_φ
    r := N.r - 1
    f := fun k => if k = k₀ then f_cat else N.f (idx k)
    g := fun k => if k = k₀ then g_cat else N.g (idx k)
    injective_f := by
      intro k
      split_ifs with hk
      · exact hinj_f_cat
      · exact N.injective_f (idx k)
    injective_g := by
      intro k
      split_ifs with hk
      · exact hinj_g_cat
      · exact N.injective_g (idx k)
    range_f_subset_bd := by
      intro k
      split_ifs with hk
      · rw [show f_cat = concatCurve (N.f i₁) (N.f i₂) hf12 from rfl, range_concatCurve]
        exact union_subset (N.range_f_subset_bd i₁) (N.range_f_subset_bd i₂)
      · exact N.range_f_subset_bd (idx k)
    range_g_subset_bd := by
      intro k
      split_ifs with hk
      · rw [show g_cat = concatCurve (N.g i₁) (N.g i₂) hg12 from rfl, range_concatCurve]
        exact union_subset (N.range_g_subset_bd i₁) (N.range_g_subset_bd i₂)
      · exact N.range_g_subset_bd (idx k)
    internally_disjoint_ff := by
      intro k₁ k₂ hk12 t ht
      by_cases h1 : k₁ = k₀ <;> by_cases h2 : k₂ = k₀ <;>
        simp only [h1, h2, ite_true, ite_false]
      · exact False.elim (hk12 (h1.trans h2.symm))
      · have hj₁ := hidx_ne_i₁ k₂ h2
        have hj₂ := hidx_ne_i₂ k₂
        change concatCurve (N.f i₁) (N.f i₂) hf12 t ∉ range (N.f (idx k₂))
        rcases mem_Ioo_concatCurve hf12 ht with (⟨u, hu, hfu⟩ | hfu) | ⟨u, hu, hfu⟩
        · rw [← hfu]; exact N.internally_disjoint_ff i₁ (idx k₂) hj₁.symm u hu
        · rw [mem_singleton_iff.mp hfu]
          intro hmem
          exact N.not_φ_eq_of_mem_range_fg hv_seamV (hother (idx k₂) hj₁ hj₂).1
            (hother (idx k₂) hj₁ hj₂).2 (Or.inl hmem) hi₁_1
        · rw [← hfu]; exact N.internally_disjoint_ff i₂ (idx k₂) hj₂.symm u hu
      · have hj₁ := hidx_ne_i₁ k₁ h1
        have hj₂ := hidx_ne_i₂ k₁
        rw [show f_cat = concatCurve (N.f i₁) (N.f i₂) hf12 from rfl, range_concatCurve]
        rintro (hf₁ | hf₂)
        · exact N.internally_disjoint_ff (idx k₁) i₁ hj₁ t ht hf₁
        · exact N.internally_disjoint_ff (idx k₁) i₂ hj₂ t ht hf₂
      · exact N.internally_disjoint_ff (idx k₁) (idx k₂) (fun h => hk12 (hidx_inj h)) t ht
    internally_disjoint_gg := by
      intro k₁ k₂ hk12 t ht
      by_cases h1 : k₁ = k₀ <;> by_cases h2 : k₂ = k₀ <;>
        simp only [h1, h2, ite_true, ite_false]
      · exact False.elim (hk12 (h1.trans h2.symm))
      · have hj₁ := hidx_ne_i₁ k₂ h2
        have hj₂ := hidx_ne_i₂ k₂
        change concatCurve (N.g i₁) (N.g i₂) hg12 t ∉ range (N.g (idx k₂))
        rcases mem_Ioo_concatCurve hg12 ht with (⟨u, hu, hgu⟩ | hgu) | ⟨u, hu, hgu⟩
        · rw [← hgu]; exact N.internally_disjoint_gg i₁ (idx k₂) hj₁.symm u hu
        · rw [mem_singleton_iff.mp hgu]
          intro hmem
          exact N.not_φ_eq_of_mem_range_fg hv_seamV (hother (idx k₂) hj₁ hj₂).1
            (hother (idx k₂) hj₁ hj₂).2 (Or.inr hmem) ((N.pasting_eq i₁ 1).symm.trans hi₁_1)
        · rw [← hgu]; exact N.internally_disjoint_gg i₂ (idx k₂) hj₂.symm u hu
      · have hj₁ := hidx_ne_i₁ k₁ h1
        have hj₂ := hidx_ne_i₂ k₁
        rw [show g_cat = concatCurve (N.g i₁) (N.g i₂) hg12 from rfl, range_concatCurve]
        rintro (hg₁ | hg₂)
        · exact N.internally_disjoint_gg (idx k₁) i₁ hj₁ t ht hg₁
        · exact N.internally_disjoint_gg (idx k₁) i₂ hj₂ t ht hg₂
      · exact N.internally_disjoint_gg (idx k₁) (idx k₂) (fun h => hk12 (hidx_inj h)) t ht
    internally_disjoint_fg := by
      intro k₁ k₂ t ht
      by_cases h1 : k₁ = k₀ <;> by_cases h2 : k₂ = k₀ <;>
        simp only [h1, h2, ite_true, ite_false]
      · rw [show g_cat = concatCurve (N.g i₁) (N.g i₂) hg12 from rfl, range_concatCurve]
        change concatCurve (N.f i₁) (N.f i₂) hf12 t ∉ range (N.g i₁) ∪ range (N.g i₂)
        rcases mem_Ioo_concatCurve hf12 ht with (⟨u, hu, hfu⟩ | hfu) | ⟨u, hu, hfu⟩
        · rw [← hfu]
          rintro (hg₁ | hg₂)
          · exact N.internally_disjoint_fg i₁ i₁ u hu hg₁
          · exact N.internally_disjoint_fg i₁ i₂ u hu hg₂
        · rw [mem_singleton_iff.mp hfu]
          exact fun h => h.elim hf1_notMem_g1 hf1_notMem_g2
        · rw [← hfu]
          rintro (hg₁ | hg₂)
          · exact N.internally_disjoint_fg i₂ i₁ u hu hg₁
          · exact N.internally_disjoint_fg i₂ i₂ u hu hg₂
      · have hj₁ := hidx_ne_i₁ k₂ h2
        have hj₂ := hidx_ne_i₂ k₂
        change concatCurve (N.f i₁) (N.f i₂) hf12 t ∉ range (N.g (idx k₂))
        rcases mem_Ioo_concatCurve hf12 ht with (⟨u, hu, hfu⟩ | hfu) | ⟨u, hu, hfu⟩
        · rw [← hfu]; exact N.internally_disjoint_fg i₁ (idx k₂) u hu
        · rw [mem_singleton_iff.mp hfu]
          intro hmem
          exact N.not_φ_eq_of_mem_range_fg hv_seamV (hother (idx k₂) hj₁ hj₂).1
            (hother (idx k₂) hj₁ hj₂).2 (Or.inr hmem) hi₁_1
        · rw [← hfu]; exact N.internally_disjoint_fg i₂ (idx k₂) u hu
      · rw [show g_cat = concatCurve (N.g i₁) (N.g i₂) hg12 from rfl, range_concatCurve]
        rintro (hg₁ | hg₂)
        · exact N.internally_disjoint_fg (idx k₁) i₁ t ht hg₁
        · exact N.internally_disjoint_fg (idx k₁) i₂ t ht hg₂
      · exact N.internally_disjoint_fg (idx k₁) (idx k₂) t ht
    internally_disjoint_gf := by
      intro k₁ k₂ t ht
      by_cases h1 : k₁ = k₀ <;> by_cases h2 : k₂ = k₀ <;>
        simp only [h1, h2, ite_true, ite_false]
      · rw [show f_cat = concatCurve (N.f i₁) (N.f i₂) hf12 from rfl, range_concatCurve]
        change concatCurve (N.g i₁) (N.g i₂) hg12 t ∉ range (N.f i₁) ∪ range (N.f i₂)
        rcases mem_Ioo_concatCurve hg12 ht with (⟨u, hu, hgu⟩ | hgu) | ⟨u, hu, hgu⟩
        · rw [← hgu]
          rintro (hf₁ | hf₂)
          · exact N.internally_disjoint_gf i₁ i₁ u hu hf₁
          · exact N.internally_disjoint_gf i₁ i₂ u hu hf₂
        · rw [mem_singleton_iff.mp hgu]
          exact fun h => h.elim hg1_notMem_f1 hg1_notMem_f2
        · rw [← hgu]
          rintro (hf₁ | hf₂)
          · exact N.internally_disjoint_gf i₂ i₁ u hu hf₁
          · exact N.internally_disjoint_gf i₂ i₂ u hu hf₂
      · have hj₁ := hidx_ne_i₁ k₂ h2
        have hj₂ := hidx_ne_i₂ k₂
        change concatCurve (N.g i₁) (N.g i₂) hg12 t ∉ range (N.f (idx k₂))
        rcases mem_Ioo_concatCurve hg12 ht with (⟨u, hu, hgu⟩ | hgu) | ⟨u, hu, hgu⟩
        · rw [← hgu]; exact N.internally_disjoint_gf i₁ (idx k₂) u hu
        · rw [mem_singleton_iff.mp hgu]
          intro hmem
          exact N.not_φ_eq_of_mem_range_fg hv_seamV (hother (idx k₂) hj₁ hj₂).1
            (hother (idx k₂) hj₁ hj₂).2 (Or.inl hmem) ((N.pasting_eq i₁ 1).symm.trans hi₁_1)
        · rw [← hgu]; exact N.internally_disjoint_gf i₂ (idx k₂) u hu
      · rw [show f_cat = concatCurve (N.f i₁) (N.f i₂) hf12 from rfl, range_concatCurve]
        rintro (hf₁ | hf₂)
        · exact N.internally_disjoint_gf (idx k₁) i₁ t ht hf₁
        · exact N.internally_disjoint_gf (idx k₁) i₂ t ht hf₂
      · exact N.internally_disjoint_gf (idx k₁) (idx k₂) t ht
    pasting_eq := by
      intro k t
      split_ifs with hk
      · change N.φ (concatCurve (N.f i₁) (N.f i₂) hf12 t) =
            N.φ (concatCurve (N.g i₁) (N.g i₂) hg12 t)
        rw [concatCurve_apply, concatCurve_apply]
        split_ifs
        · exact N.pasting_eq i₁ _
        · exact N.pasting_eq i₂ _
      · exact N.pasting_eq (idx k) t
    interior_inj := N.interior_inj
    bd_eq_iff := by
      intro x y
      rw [N.bd_eq_iff x y]
      suffices hrel_eq :
          (fun a b : N.D => ∃ (k : Fin (N.r - 1)) (u : unitInterval),
            a = (if k = k₀ then f_cat else N.f (idx k)) u ∧
            b = (if k = k₀ then g_cat else N.g (idx k)) u) =
          (fun a b : N.D => ∃ (j : Fin N.r) (t : unitInterval),
            a = N.f j t ∧ b = N.g j t) by
        rw [hrel_eq]
      ext a b
      constructor
      · rintro ⟨k, u, hxy⟩
        split_ifs at hxy with hk
        · change a = concatCurve (N.f i₁) (N.f i₂) hf12 u ∧
              b = concatCurve (N.g i₁) (N.g i₂) hg12 u at hxy
          rw [concatCurve_apply, concatCurve_apply] at hxy
          split_ifs at hxy with hu_le
          · exact ⟨i₁, _, hxy⟩
          · exact ⟨i₂, _, hxy⟩
        · exact ⟨idx k, u, hxy⟩
      · rintro ⟨j, t, hxy⟩
        by_cases hj₁ : j = i₁
        · cases hj₁
          let u : unitInterval := ⟨(t : ℝ) / 2, ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩
          have hu_le : (u : ℝ) ≤ 1 / 2 := by
            change (t : ℝ) / 2 ≤ 1 / 2; linarith [t.2.2]
          have h2u : (⟨2 * (u : ℝ), ⟨by linarith [u.2.1], by linarith⟩⟩ : unitInterval) = t := by
            ext; change 2 * ((t : ℝ) / 2) = t; ring
          have hf_u : f_cat u = N.f i₁ t := by
            change concatCurve (N.f i₁) (N.f i₂) hf12 u = N.f i₁ t
            rw [concatCurve_apply, dite_eq_left hu_le, h2u]
          have hg_u : g_cat u = N.g i₁ t := by
            change concatCurve (N.g i₁) (N.g i₂) hg12 u = N.g i₁ t
            rw [concatCurve_apply, dite_eq_left hu_le, h2u]
          refine ⟨k₀, u, ?_⟩
          simpa [hf_u, hg_u] using hxy
        · by_cases hj₂ : j = i₂
          · cases hj₂
            rcases eq_or_lt_of_le t.2.1 with ht0 | ht_pos
            · have ht_eq0 : t = 0 := Subtype.ext ht0.symm
              subst ht_eq0
              let u : unitInterval := ⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩
              have hu_le : (u : ℝ) ≤ 1 / 2 := le_rfl
              have h2u : (⟨2 * (u : ℝ), ⟨by change 0 ≤ (2 : ℝ) * (1 / 2); norm_num,
                  by change (2 : ℝ) * (1 / 2) ≤ 1; norm_num⟩⟩ : unitInterval) = 1 := by
                ext; change (2 : ℝ) * (1 / 2) = 1; norm_num
              have hf_u : f_cat u = N.f i₂ 0 := by
                change concatCurve (N.f i₁) (N.f i₂) hf12 u = N.f i₂ 0
                rw [concatCurve_apply, dite_eq_left hu_le, h2u, hf12]
              have hg_u : g_cat u = N.g i₂ 0 := by
                change concatCurve (N.g i₁) (N.g i₂) hg12 u = N.g i₂ 0
                rw [concatCurve_apply, dite_eq_left hu_le, h2u, hg12]
              refine ⟨k₀, u, ?_⟩
              simpa [hf_u, hg_u] using hxy
            · let u : unitInterval := ⟨((t : ℝ) + 1) / 2, ⟨by linarith [t.2.1], by linarith
                [t.2.2]⟩⟩
              have hu_gt : ¬ (u : ℝ) ≤ 1 / 2 := by
                change ¬ ((t : ℝ) + 1) / 2 ≤ 1 / 2; linarith
              have h2u : (⟨2 * (u : ℝ) - 1, ⟨by linarith, by linarith [u.2.2]⟩⟩ : unitInterval) = t
                := by
                ext; change 2 * (((t : ℝ) + 1) / 2) - 1 = t; ring
              have hf_u : f_cat u = N.f i₂ t := by
                change concatCurve (N.f i₁) (N.f i₂) hf12 u = N.f i₂ t
                rw [concatCurve_apply, dite_eq_right hu_gt, h2u]
              have hg_u : g_cat u = N.g i₂ t := by
                change concatCurve (N.g i₁) (N.g i₂) hg12 u = N.g i₂ t
                rw [concatCurve_apply, dite_eq_right hu_gt, h2u]
              refine ⟨k₀, u, ?_⟩
              simpa [hf_u, hg_u] using hxy
          · obtain ⟨k, hk_ne, rfl⟩ := hsurj_other j hj₁ hj₂
            refine ⟨k, t, ?_⟩
            simpa [hk_ne] using hxy
  }

/-- Excluding two aligned pasted pairs meeting at an interior vertex `v ∉ bd S`
(`N.f i₁ 1 = N.f i₂ 0`, `N.g i₁ 1 = N.g i₂ 0`, `N.f i₁ 1 ≠ N.g i₁ 1`) with no other pasted pairs
incident with `v`: concatenating `(N.f i₁, N.f i₂)` and `(N.g i₁, N.g i₂)` yields a `G`-normal net
`N'` with `N'.r = N.r - 1 < N.r`, contradicting `N.IsMinimalFor G`. -/
theorem not_two_pairs_aligned_at_interior_vertex (hS : IsSurface S)
    {G : Drawing S} (N : Net S) (hmin : N.IsMinimalFor G)
    {v : S} (_hv_not_bd : v ∉ bd S) {i₁ i₂ : Fin N.r} (h12_ne : i₁ ≠ i₂)
    (hi₁_0 : N.φ (N.f i₁ 0) ≠ v) (hi₁_1 : N.φ (N.f i₁ 1) = v)
    (_hi₂_0 : N.φ (N.f i₂ 0) = v) (hi₂_1 : N.φ (N.f i₂ 1) ≠ v)
    (hother : ∀ j : Fin N.r, j ≠ i₁ → j ≠ i₂ → N.φ (N.f j 0) ≠ v ∧ N.φ (N.f j 1) ≠ v)
    (hf12 : N.f i₁ 1 = N.f i₂ 0) (hg12 : N.g i₁ 1 = N.g i₂ 0)
    (hfg_ne : N.f i₁ 1 ≠ N.g i₁ 1) :
    False := by
  classical
  have : T2Space S := hS.2.1
  have hv_seamV : v ∈ N.seamV := ⟨i₁, Or.inr hi₁_1⟩
  let t_half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht_half : t_half ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t_half]
  have hf_ends_ne : N.f i₁ 0 ≠ N.f i₂ 1 := by
    intro heq
    have hbd_eq : range (N.f i₁) ∪ range (revCurve (N.f i₂)) = bd N.D :=
      N.range_union_eq_bd_of_same_ends (c₁ := N.f i₁) (c₂ := revCurve (N.f i₂))
        (N.injective_f i₁) (N.range_f_subset_bd i₁)
        (injective_revCurve (N.injective_f i₂))
        (by rw [range_revCurve]; exact N.range_f_subset_bd i₂)
        (by simpa [revCurve] using heq)
        (by simpa [revCurve] using hf12)
        (by
          rw [disjoint_left]
          rintro _ ⟨t, ht, rfl⟩ ⟨s, _, hs⟩
          rw [revCurve_apply] at hs
          exact N.internally_disjoint_ff i₁ i₂ h12_ne t ht ⟨unitInterval.symm s, hs⟩)
    rw [range_revCurve] at hbd_eq
    have hmem : N.g i₁ t_half ∈ range (N.f i₁) ∪ range (N.f i₂) :=
      hbd_eq.symm ▸ N.range_g_subset_bd i₁ ⟨t_half, rfl⟩
    rcases hmem with hf₁ | hf₂
    · exact N.internally_disjoint_gf i₁ i₁ t_half ht_half hf₁
    · exact N.internally_disjoint_gf i₁ i₂ t_half ht_half hf₂
  have hg_ends_ne : N.g i₁ 0 ≠ N.g i₂ 1 := by
    intro heq
    have hbd_eq : range (N.g i₁) ∪ range (revCurve (N.g i₂)) = bd N.D :=
      N.range_union_eq_bd_of_same_ends (c₁ := N.g i₁) (c₂ := revCurve (N.g i₂))
        (N.injective_g i₁) (N.range_g_subset_bd i₁)
        (injective_revCurve (N.injective_g i₂))
        (by rw [range_revCurve]; exact N.range_g_subset_bd i₂)
        (by simpa [revCurve] using heq)
        (by simpa [revCurve] using hg12)
        (by
          rw [disjoint_left]
          rintro _ ⟨t, ht, rfl⟩ ⟨s, _, hs⟩
          rw [revCurve_apply] at hs
          exact N.internally_disjoint_gg i₁ i₂ h12_ne t ht ⟨unitInterval.symm s, hs⟩)
    rw [range_revCurve] at hbd_eq
    have hmem : N.f i₁ t_half ∈ range (N.g i₁) ∪ range (N.g i₂) :=
      hbd_eq.symm ▸ N.range_f_subset_bd i₁ ⟨t_half, rfl⟩
    rcases hmem with hg₁ | hg₂
    · exact N.internally_disjoint_fg i₁ i₁ t_half ht_half hg₁
    · exact N.internally_disjoint_fg i₁ i₂ t_half ht_half hg₂
  let f_cat : Curve N.D := concatCurve (N.f i₁) (N.f i₂) hf12
  let g_cat : Curve N.D := concatCurve (N.g i₁) (N.g i₂) hg12
  have hinj_f_cat : Function.Injective f_cat :=
    injective_concatCurve hf12 (N.injective_f i₁) (N.injective_f i₂) hf_ends_ne
      (N.internally_disjoint_ff i₁ i₂ h12_ne) (N.internally_disjoint_ff i₂ i₁ h12_ne.symm)
  have hinj_g_cat : Function.Injective g_cat :=
    injective_concatCurve hg12 (N.injective_g i₁) (N.injective_g i₂) hg_ends_ne
      (N.internally_disjoint_gg i₁ i₂ h12_ne) (N.internally_disjoint_gg i₂ i₁ h12_ne.symm)
  have hf1_notMem_g1 : N.f i₁ 1 ∉ range (N.g i₁) := by
    rintro ⟨s, hs⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs_Ioo
    · exact hi₁_0 ((N.pasting_eq i₁ 0).trans ((congr_arg N.φ hs).trans hi₁_1))
    · exact hfg_ne hs.symm
    · exact N.internally_disjoint_gf i₁ i₁ s hs_Ioo ⟨1, hs.symm⟩
  have hf1_notMem_g2 : N.f i₁ 1 ∉ range (N.g i₂) := by
    rintro ⟨s, hs⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs_Ioo
    · exact hfg_ne (hs.symm.trans hg12.symm)
    · exact hi₂_1 ((N.pasting_eq i₂ 1).trans ((congr_arg N.φ hs).trans hi₁_1))
    · exact N.internally_disjoint_gf i₂ i₁ s hs_Ioo ⟨1, hs.symm⟩
  have hg1_notMem_f1 : N.g i₁ 1 ∉ range (N.f i₁) := by
    rintro ⟨s, hs⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs_Ioo
    · exact hi₁_0 ((congr_arg N.φ hs).trans ((N.pasting_eq i₁ 1).symm.trans hi₁_1))
    · exact hfg_ne hs
    · exact N.internally_disjoint_fg i₁ i₁ s hs_Ioo ⟨1, hs.symm⟩
  have hg1_notMem_f2 : N.g i₁ 1 ∉ range (N.f i₂) := by
    rintro ⟨s, hs⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs_Ioo
    · exact hfg_ne (hf12.trans hs)
    · exact hi₂_1 ((congr_arg N.φ hs).trans ((N.pasting_eq i₁ 1).symm.trans hi₁_1))
    · exact N.internally_disjoint_fg i₂ i₁ s hs_Ioo ⟨1, hs.symm⟩
  have hr2 : 2 ≤ N.r := by
    have : i₁.1 ≠ i₂.1 := Fin.val_ne_of_ne h12_ne
    omega
  let e : Fin (N.r - 1 + 1) ≃ Fin N.r := finCongr (by omega)
  let i₁' : Fin (N.r - 1 + 1) := e.symm i₁
  let i₂' : Fin (N.r - 1 + 1) := e.symm i₂
  have h12'_ne : i₁' ≠ i₂' := fun h => h12_ne (e.symm.injective h)
  obtain ⟨k₀, hk₀⟩ := Fin.exists_succAbove_eq h12'_ne
  let idx (k : Fin (N.r - 1)) : Fin N.r := e (i₂'.succAbove k)
  have hidx_inj : Function.Injective idx := e.injective.comp (Fin.succAbove_right_injective)
  have hidx_k₀ : idx k₀ = i₁ := by simp [idx, hk₀, i₁']
  have hidx_ne_i₂ : ∀ k : Fin (N.r - 1), idx k ≠ i₂ := by
    intro k h
    have : i₂'.succAbove k = i₂' := e.injective (by simpa [idx, i₂'] using h)
    exact Fin.succAbove_ne i₂' k this
  have hidx_ne_i₁ : ∀ k : Fin (N.r - 1), k ≠ k₀ → idx k ≠ i₁ := by
    intro k hk h
    exact hk (hidx_inj (h.trans hidx_k₀.symm))
  have hsurj_other : ∀ j : Fin N.r, j ≠ i₁ → j ≠ i₂ → ∃ k : Fin (N.r - 1), k ≠ k₀ ∧ idx k = j := by
    intro j hj₁ hj₂
    have hj'_ne : e.symm j ≠ i₂' := fun h => hj₂ (e.symm.injective h)
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj'_ne
    have hidx_k : idx k = j := by simp [idx, hk]
    exact ⟨k, fun hkk₀ => hj₁ (hidx_k ▸ hkk₀ ▸ hidx_k₀), hidx_k⟩
  let N' : Net S :=
    join_adjacent_net_pairs (S := S) N (v := v) (i₁ := i₁) (i₂ := i₂) hi₁_1 hother hf12 hg12
      hv_seamV hinj_f_cat hinj_g_cat hf1_notMem_g1 hf1_notMem_g2 hg1_notMem_f1 hg1_notMem_f2 k₀
      idx hidx_inj hidx_ne_i₂ hidx_ne_i₁ hsurj_other
  have hN'_norm : N'.IsNormalFor G := by
    rw [N'.isNormalFor_iff hS]
    exact ⟨by change 0 < N.r - 1; omega, ((N.isNormalFor_iff hS G).mp hmin.1).2⟩
  have hle : N.r ≤ N'.r := hmin.2.2 N' hN'_norm le_rfl
  change N.r ≤ N.r - 1 at hle
  omega

/-- If `v ∉ bd S` and `x ∈ {N.f i₀ 0, N.f i₀ 1}` has `N.φ x = v`, then `x` belongs to the range
of some other curve among `{N.f j | j ≠ i₀} ∪ {N.g j | j}`. -/
lemma mem_other_range_of_φ_f_eq (hS : IsSurface S) (N : Net S)
    {v : S} (hv_not_bd : v ∉ bd S) {i₀ : Fin N.r} {x : N.D}
    (hx_end : x = N.f i₀ 0 ∨ x = N.f i₀ 1) (hφ : N.φ x = v) :
    (∃ j : Fin N.r, j ≠ i₀ ∧ x ∈ range (N.f j)) ∨
      ∃ j : Fin N.r, x ∈ range (N.g j) := by
  have : T2Space N.D := N.isSurface_D.2.1
  have : T2Space S := hS.2.1
  let K : Set N.D :=
    (⋃ j ∈ (Finset.univ.filter (· ≠ i₀) : Finset (Fin N.r)), range (N.f j)) ∪
      (⋃ j : Fin N.r, range (N.g j)) ∪ N.φ ⁻¹' bd S
  have hK_closed : IsClosed K := by
    refine ((IsClosed.union ?_ ?_).union ((isClosed_bd S).preimage N.quotientMap_φ.continuous))
    · exact isClosed_biUnion_finset (fun j _ => (isCompact_range (N.f j).continuous).isClosed)
    · exact isClosed_iUnion_of_finite (fun j => (isCompact_range (N.g j).continuous).isClosed)
  have hsub : bd N.D ⊆ range (N.f i₀) ∪ K := by
    intro y hy
    rcases N.bd_subset_pasted_union_preimage_bd hy with hpasted | hbdS
    · simp only [mem_iUnion, mem_union] at hpasted
      rcases hpasted with ⟨j, hfj | hgj⟩
      · by_cases hj : j = i₀
        · subst hj; exact Or.inl hfj
        · refine Or.inr (Or.inl (Or.inl (mem_iUnion₂.mpr ⟨j, ?_, hfj⟩)))
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      · exact Or.inr (Or.inl (Or.inr (mem_iUnion.mpr ⟨j, hgj⟩)))
    · exact Or.inr (Or.inr hbdS.2)
  have hmemK : x ∈ K := by
    by_contra hnotK
    exact N.not_bd_subset_range_union_closed (N.injective_f i₀) (N.range_f_subset_bd i₀)
      hK_closed hx_end hnotK hsub
  rcases hmemK with (hf | hg) | hbdS
  · simp only [mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rcases hf with ⟨j, hj, hfj⟩
    exact Or.inl ⟨j, hj, hfj⟩
  · simp only [mem_iUnion] at hg
    exact Or.inr hg
  · exact False.elim (hv_not_bd (hφ ▸ hbdS))

/-- If `v ∉ bd S` and `x ∈ {N.g i₀ 0, N.g i₀ 1}` has `N.φ x = v`, then `x` belongs to the range
of some other curve among `{N.f j | j} ∪ {N.g j | j ≠ i₀}`. -/
lemma mem_other_range_of_φ_g_eq (hS : IsSurface S) (N : Net S)
    {v : S} (hv_not_bd : v ∉ bd S) {i₀ : Fin N.r} {x : N.D}
    (hx_end : x = N.g i₀ 0 ∨ x = N.g i₀ 1) (hφ : N.φ x = v) :
    (∃ j : Fin N.r, x ∈ range (N.f j)) ∨
      ∃ j : Fin N.r, j ≠ i₀ ∧ x ∈ range (N.g j) := by
  have : T2Space N.D := N.isSurface_D.2.1
  have : T2Space S := hS.2.1
  let K : Set N.D :=
    (⋃ j : Fin N.r, range (N.f j)) ∪
      (⋃ j ∈ (Finset.univ.filter (· ≠ i₀) : Finset (Fin N.r)), range (N.g j)) ∪ N.φ ⁻¹' bd S
  have hK_closed : IsClosed K := by
    refine ((IsClosed.union ?_ ?_).union ((isClosed_bd S).preimage N.quotientMap_φ.continuous))
    · exact isClosed_iUnion_of_finite (fun j => (isCompact_range (N.f j).continuous).isClosed)
    · exact isClosed_biUnion_finset (fun j _ => (isCompact_range (N.g j).continuous).isClosed)
  have hsub : bd N.D ⊆ range (N.g i₀) ∪ K := by
    intro y hy
    rcases N.bd_subset_pasted_union_preimage_bd hy with hpasted | hbdS
    · simp only [mem_iUnion, mem_union] at hpasted
      rcases hpasted with ⟨j, hfj | hgj⟩
      · exact Or.inr (Or.inl (Or.inl (mem_iUnion.mpr ⟨j, hfj⟩)))
      · by_cases hj : j = i₀
        · subst hj; exact Or.inl hgj
        · refine Or.inr (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨j, ?_, hgj⟩)))
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    · exact Or.inr (Or.inr hbdS.2)
  have hmemK : x ∈ K := by
    by_contra hnotK
    exact N.not_bd_subset_range_union_closed (N.injective_g i₀) (N.range_g_subset_bd i₀)
      hK_closed hx_end hnotK hsub
  rcases hmemK with (hf | hg) | hbdS
  · simp only [mem_iUnion] at hf
    exact Or.inl hf
  · simp only [mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    rcases hg with ⟨j, hj, hgj⟩
    exact Or.inr ⟨j, hj, hgj⟩
  · exact False.elim (hv_not_bd (hφ ▸ hbdS))

/-- Excluding Case 3 / Subcase B2b (`(N.F₂ v).card = 0` and `(N.F₁ v).card = 2`): two distinct
non-loop seam pairs incident with an interior vertex `v ∉ bd S` and no other seam pairs incident
with `v` cannot occur in a minimal net `N` on a surface `S`. -/
theorem not_two_pairs_at_interior_vertex (hS : IsSurface S)
    {G : Drawing S} (N : Net S) (hmin : N.IsMinimalFor G)
    {v : S} (hv_not_bd : v ∉ bd S) {i₁ i₂ : Fin N.r} (h12_ne : i₁ ≠ i₂)
    (hi₁_0 : N.φ (N.f i₁ 0) ≠ v) (hi₁_1 : N.φ (N.f i₁ 1) = v)
    (hi₂_0 : N.φ (N.f i₂ 0) = v) (hi₂_1 : N.φ (N.f i₂ 1) ≠ v)
    (hother : ∀ j : Fin N.r, j ≠ i₁ → j ≠ i₂ → N.φ (N.f j 0) ≠ v ∧ N.φ (N.f j 1) ≠ v) :
    False := by
  have hv_seamV : v ∈ N.seamV := ⟨i₁, Or.inr hi₁_1⟩
  have hsymm_Ioo : ∀ {t : unitInterval}, t ∈ Ioo (0 : unitInterval) 1 →
      unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := Subtype.coe_lt_coe.mpr ht.1
    have ht1 : (t : ℝ) < 1 := Subtype.coe_lt_coe.mpr ht.2
    constructor <;> rw [← Subtype.coe_lt_coe]
    · change (0 : ℝ) < 1 - (t : ℝ); linarith
    · change 1 - (t : ℝ) < 1; linarith
  have hφ_g₁ : N.φ (N.g i₁ 1) = v := (N.pasting_eq i₁ 1).symm.trans hi₁_1
  have hφ_g₂ : N.φ (N.g i₂ 0) = v := (N.pasting_eq i₂ 0).symm.trans hi₂_0
  have hstep_v : ∀ {j : Fin N.r} {t : unitInterval}, N.φ (N.f j t) = v →
      (j = i₁ ∧ t = 1) ∨ (j = i₂ ∧ t = 0) := by
    intro j t hφft
    by_cases hj₁ : j = i₁
    · cases hj₁
      rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
      · exact False.elim (hi₁_0 hφft)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (N.notMem_seamV_of_mem_Ioo i₁ ht (hφft.symm ▸ hv_seamV))
    · by_cases hj₂ : j = i₂
      · cases hj₂
        rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · exact Or.inr ⟨rfl, rfl⟩
        · exact False.elim (hi₂_1 hφft)
        · exact False.elim (N.notMem_seamV_of_mem_Ioo i₂ ht (hφft.symm ▸ hv_seamV))
      · exact False.elim (N.not_φ_eq_of_mem_range_fg hv_seamV (hother j hj₁ hj₂).1
          (hother j hj₁ hj₂).2 (Or.inl ⟨t, rfl⟩) hφft)
  have hfg₁_ne : N.f i₁ 1 ≠ N.g i₁ 1 := by
    intro heq
    have h3_f₂ : N.f i₁ 1 ≠ N.f i₂ 0 := by
      intro h2
      refine N.not_three_curves_common_end
        (c₁ := revCurve (N.f i₁)) (c₂ := revCurve (N.g i₁)) (c₃ := N.f i₂)
        (injective_revCurve (N.injective_f i₁))
        (by rw [range_revCurve]; exact N.range_f_subset_bd i₁)
        (injective_revCurve (N.injective_g i₁))
        (by rw [range_revCurve]; exact N.range_g_subset_bd i₁)
        (N.range_f_subset_bd i₂)
        (by simpa using heq)
        (by simpa using h2)
        (by intro t ht; rw [range_revCurve]; exact N.internally_disjoint_fg i₁ i₁ _ (hsymm_Ioo ht))
        (by intro t ht; rw [range_revCurve]; exact N.internally_disjoint_gf i₁ i₁ _ (hsymm_Ioo ht))
        (by intro t ht; rw [range_revCurve]; exact N.internally_disjoint_ff i₂ i₁ h12_ne.symm t ht)
        (by intro t ht; rw [range_revCurve]; exact N.internally_disjoint_fg i₂ i₁ t ht)
    have h3_g₂ : N.f i₁ 1 ≠ N.g i₂ 0 := by
      intro h2
      refine N.not_three_curves_common_end
        (c₁ := revCurve (N.f i₁)) (c₂ := revCurve (N.g i₁)) (c₃ := N.g i₂)
        (injective_revCurve (N.injective_f i₁))
        (by rw [range_revCurve]; exact N.range_f_subset_bd i₁)
        (injective_revCurve (N.injective_g i₁))
        (by rw [range_revCurve]; exact N.range_g_subset_bd i₁)
        (N.range_g_subset_bd i₂)
        (by simpa using heq)
        (by simpa using h2)
        (by intro t ht; rw [range_revCurve]; exact N.internally_disjoint_fg i₁ i₁ _ (hsymm_Ioo ht))
        (by intro t ht; rw [range_revCurve]; exact N.internally_disjoint_gf i₁ i₁ _ (hsymm_Ioo ht))
        (by intro t ht; rw [range_revCurve]; exact N.internally_disjoint_gf i₂ i₁ t ht)
        (by intro t ht; rw [range_revCurve]; exact N.internally_disjoint_gg i₂ i₁ h12_ne.symm t ht)
    have heqv := (N.bd_eq_iff (N.f i₁ 1) (N.f i₂ 0)).mp (hi₁_1.trans hi₂_0.symm)
    have hinv : ∀ a b : N.D,
        Relation.EqvGen (fun a b => ∃ j t, a = N.f j t ∧ b = N.g j t) a b →
        (a = N.f i₁ 1 ↔ b = N.f i₁ 1) := by
      intro a b hrel
      induction hrel with
      | rel x y hxy =>
        rcases hxy with ⟨j, t, rfl, rfl⟩
        constructor
        · intro hx
          rcases hstep_v (hx.symm ▸ hi₁_1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact heq.symm
          · exact False.elim (h3_f₂ hx.symm)
        · intro hy
          have hφft : N.φ (N.f j t) = v := (N.pasting_eq j t).trans (hy.symm ▸ hi₁_1)
          rcases hstep_v hφft with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact False.elim (h3_g₂ hy.symm)
      | refl _ => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact h3_f₂ ((hinv (N.f i₁ 1) (N.f i₂ 0) heqv).mp rfl).symm
  have hfg₂_ne : N.f i₂ 0 ≠ N.g i₂ 0 := by
    intro heq
    have h3_f₁ : N.f i₂ 0 ≠ N.f i₁ 1 := by
      intro h1
      refine N.not_three_curves_common_end
        (c₁ := N.f i₂) (c₂ := N.g i₂) (c₃ := revCurve (N.f i₁))
        (N.injective_f i₂) (N.range_f_subset_bd i₂)
        (N.injective_g i₂) (N.range_g_subset_bd i₂)
        (by rw [range_revCurve]; exact N.range_f_subset_bd i₁)
        heq
        (by simpa using h1)
        (N.internally_disjoint_fg i₂ i₂)
        (N.internally_disjoint_gf i₂ i₂)
        (by intro t ht; exact N.internally_disjoint_ff i₁ i₂ h12_ne _ (hsymm_Ioo ht))
        (by intro t ht; exact N.internally_disjoint_fg i₁ i₂ _ (hsymm_Ioo ht))
    have h3_g₁ : N.f i₂ 0 ≠ N.g i₁ 1 := by
      intro h1
      refine N.not_three_curves_common_end
        (c₁ := N.f i₂) (c₂ := N.g i₂) (c₃ := revCurve (N.g i₁))
        (N.injective_f i₂) (N.range_f_subset_bd i₂)
        (N.injective_g i₂) (N.range_g_subset_bd i₂)
        (by rw [range_revCurve]; exact N.range_g_subset_bd i₁)
        heq
        (by simpa using h1)
        (N.internally_disjoint_fg i₂ i₂)
        (N.internally_disjoint_gf i₂ i₂)
        (by intro t ht; exact N.internally_disjoint_gf i₁ i₂ _ (hsymm_Ioo ht))
        (by intro t ht; exact N.internally_disjoint_gg i₁ i₂ h12_ne _ (hsymm_Ioo ht))
    have heqv := (N.bd_eq_iff (N.f i₂ 0) (N.f i₁ 1)).mp (hi₂_0.trans hi₁_1.symm)
    have hinv : ∀ a b : N.D,
        Relation.EqvGen (fun a b => ∃ j t, a = N.f j t ∧ b = N.g j t) a b →
        (a = N.f i₂ 0 ↔ b = N.f i₂ 0) := by
      intro a b hrel
      induction hrel with
      | rel x y hxy =>
        rcases hxy with ⟨j, t, rfl, rfl⟩
        constructor
        · intro hx
          rcases hstep_v (hx.symm ▸ hi₂_0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact False.elim (h3_f₁ hx.symm)
          · exact heq.symm
        · intro hy
          have hφft : N.φ (N.f j t) = v := (N.pasting_eq j t).trans (hy.symm ▸ hi₂_0)
          rcases hstep_v hφft with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact False.elim (h3_g₁ hy.symm)
          · rfl
      | refl _ => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact h3_f₁ ((hinv (N.f i₂ 0) (N.f i₁ 1) heqv).mp rfl).symm
  have hf₁_cases : N.f i₁ 1 = N.f i₂ 0 ∨ N.f i₁ 1 = N.g i₂ 0 := by
    rcases N.mem_other_range_of_φ_f_eq hS hv_not_bd (Or.inr rfl) hi₁_1 with
      ⟨j, hj, t, ht⟩ | ⟨j, t, ht⟩
    · rcases hstep_v ((congr_arg N.φ ht).trans hi₁_1) with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hj rfl)
      · exact Or.inl ht.symm
    · rcases hstep_v ((N.pasting_eq j t).trans ((congr_arg N.φ ht).trans hi₁_1)) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hfg₁_ne ht.symm)
      · exact Or.inr ht.symm
  have hg₁_cases : N.g i₁ 1 = N.f i₂ 0 ∨ N.g i₁ 1 = N.g i₂ 0 := by
    rcases N.mem_other_range_of_φ_g_eq hS hv_not_bd (Or.inr rfl) hφ_g₁ with
      ⟨j, t, ht⟩ | ⟨j, hj, t, ht⟩
    · rcases hstep_v ((congr_arg N.φ ht).trans hφ_g₁) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hfg₁_ne ht)
      · exact Or.inl ht.symm
    · rcases hstep_v ((N.pasting_eq j t).trans ((congr_arg N.φ ht).trans hφ_g₁)) with
        ⟨rfl, _⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hj rfl)
      · exact Or.inr ht.symm
  rcases hf₁_cases with hf12 | hf1_g2
  · have hg12 : N.g i₁ 1 = N.g i₂ 0 := by
      rcases hg₁_cases with hg1_f2 | hg12
      · exact False.elim (hfg₁_ne (hf12.trans hg1_f2.symm))
      · exact hg12
    exact N.not_two_pairs_aligned_at_interior_vertex hS hmin hv_not_bd h12_ne
      hi₁_0 hi₁_1 hi₂_0 hi₂_1 hother hf12 hg12 hfg₁_ne
  · have hg1_f2 : N.g i₁ 1 = N.f i₂ 0 := by
      rcases hg₁_cases with hg1_f2 | hg12
      · exact hg1_f2
      · exact False.elim (hfg₁_ne (hf1_g2.trans hg12.symm))
    refine (N.swapPair i₂).not_two_pairs_aligned_at_interior_vertex hS
      ((N.isMinimalFor_swapPair i₂ G).mpr hmin) hv_not_bd h12_ne
      (by change N.φ ((if i₁ = i₂ then N.g i₁ else N.f i₁) 0) ≠ v; rw [ite_eq_right h12_ne]; exact
        hi₁_0)
      (by change N.φ ((if i₁ = i₂ then N.g i₁ else N.f i₁) 1) = v; rw [ite_eq_right h12_ne]; exact
        hi₁_1)
      (by change N.φ ((if i₂ = i₂ then N.g i₂ else N.f i₂) 0) = v; rw [ite_eq_left rfl]; exact
        hφ_g₂)
      (by change N.φ ((if i₂ = i₂ then N.g i₂ else N.f i₂) 1) ≠ v
          rw [ite_eq_left rfl, ← N.pasting_eq i₂ 1]; exact hi₂_1)
      (by change ∀ j : Fin N.r, j ≠ i₁ → j ≠ i₂ →
            N.φ ((if j = i₂ then N.g j else N.f j) 0) ≠ v ∧
            N.φ ((if j = i₂ then N.g j else N.f j) 1) ≠ v
          intro j hj₁ hj₂
          rw [ite_eq_right hj₂]; exact hother j hj₁ hj₂)
      (by change (if i₁ = i₂ then N.g i₁ else N.f i₁) 1 = (if i₂ = i₂ then N.g i₂ else N.f i₂) 0
          rw [ite_eq_right h12_ne, ite_eq_left rfl]; exact hf1_g2)
      (by change (if i₁ = i₂ then N.f i₁ else N.g i₁) 1 = (if i₂ = i₂ then N.f i₂ else N.g i₂) 0
          rw [ite_eq_right h12_ne, ite_eq_left rfl]; exact hg1_f2)
      (by change (if i₁ = i₂ then N.g i₁ else N.f i₁) 1 ≠ (if i₁ = i₂ then N.f i₁ else N.g i₁) 1
          rw [ite_eq_right h12_ne, ite_eq_right h12_ne]; exact hfg₁_ne)

/-! ## 6. Excluding Case 2 (`F₂.card = 0, F₁.card = 1`) and proving (2.3) -/

/-- The diameter `u ↦ 2u - 1` of the upper half disc `halfD 1`. -/
private noncomputable def e_half (u : unitInterval) : ℂ := ((2 * (u : ℝ) - 1 : ℝ) : ℂ)

/-- The upper semicircle `u ↦ exp(i π (1 - u))` of the upper half disc `halfD 1`. -/
private noncomputable def a_half (u : unitInterval) : ℂ := cis' (Real.pi * (1 - (u : ℝ)))

private theorem isArcMap_e_half : IsArcMap e_half := by
  refine ⟨Complex.continuous_ofReal.comp (by fun_prop), fun u v h => ?_⟩
  have h1 : 2 * (u : ℝ) - 1 = 2 * (v : ℝ) - 1 := Complex.ofReal_injective h
  exact Subtype.ext (by linarith)

private theorem isArcMap_a_half : IsArcMap a_half := by
  have hpi := Real.pi_pos
  refine ⟨continuous_cis'.comp (by fun_prop), fun u v h => ?_⟩
  have hu : Real.pi * (1 - (u : ℝ)) ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by nlinarith [u.2.2], by nlinarith [u.2.1]⟩
  have hv : Real.pi * (1 - (v : ℝ)) ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by nlinarith [v.2.2], by nlinarith [v.2.1]⟩
  have h1 := cis'_injOn' hu hv h
  exact Subtype.ext (by nlinarith)

private theorem a_half_zero : a_half 0 = -1 := by
  change cis' (Real.pi * (1 - 0)) = -1
  rw [sub_zero, mul_one, cis'_pi]

private theorem a_half_one : a_half 1 = 1 := by
  change cis' (Real.pi * (1 - 1)) = 1
  rw [sub_self, mul_zero, cis'_zero]

private theorem e_half_zero : e_half 0 = -1 := by
  change ((2 * (0 : ℝ) - 1 : ℝ) : ℂ) = -1
  norm_num

private theorem e_half_one : e_half 1 = 1 := by
  change ((2 * (1 : ℝ) - 1 : ℝ) : ℂ) = 1
  norm_num

private theorem a_half_eq_e_half (s t : unitInterval) (h : a_half s = e_half t) :
    (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
  rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
  · rw [e_half_zero, ← a_half_zero] at h
    exact Or.inl ⟨isArcMap_a_half.2 h, rfl⟩
  · rw [e_half_one, ← a_half_one] at h
    exact Or.inr ⟨isArcMap_a_half.2 h, rfl⟩
  · exfalso
    have ht0 : (0 : ℝ) < t := Subtype.coe_lt_coe.mpr ht.1
    have ht1 : (t : ℝ) < 1 := Subtype.coe_lt_coe.mpr ht.2
    have hnorm1 : ‖a_half s‖ = 1 := norm_cis' _
    have hnorm2 : ‖e_half t‖ < 1 := by
      change ‖((2 * (t : ℝ) - 1 : ℝ) : ℂ)‖ < 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    rw [h] at hnorm1
    linarith

private theorem side_a_half_e_half : side a_half e_half = discBd (halfD 1) := by
  have hpi := Real.pi_pos
  rw [(isClosedDisc_halfD one_ne_zero).2]
  ext z
  simp only [side, mem_union, mem_range, mem_ofPred_eq, one_mul]
  constructor
  · rintro (⟨s, rfl⟩ | ⟨t, rfl⟩)
    · left
      refine ⟨norm_cis' _, ?_⟩
      change 0 ≤ (cis' (Real.pi * (1 - (s : ℝ)))).im
      rw [cis'_im]
      exact Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [s.2.2]) (by nlinarith [s.2.1])
    · right
      change ‖((2 * (t : ℝ) - 1 : ℝ) : ℂ)‖ ≤ 1 ∧ ((2 * (t : ℝ) - 1 : ℝ) : ℂ).im = 0
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨⟨by linarith [t.2.1], by linarith [t.2.2]⟩, Complex.ofReal_im _⟩
  · rintro (⟨hz1, hz2⟩ | ⟨hz1, hz2⟩)
    · left
      have harg0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr hz2
      have harg1 : Complex.arg z ≤ Real.pi := Complex.arg_le_pi z
      have hdiv0 : 0 ≤ Complex.arg z / Real.pi := div_nonneg harg0 hpi.le
      have hdiv1 : Complex.arg z / Real.pi ≤ 1 := (div_le_one hpi).mpr harg1
      refine ⟨⟨1 - Complex.arg z / Real.pi, ⟨by linarith, by linarith⟩⟩, ?_⟩
      change cis' (Real.pi * (1 - (1 - Complex.arg z / Real.pi))) = z
      rw [show Real.pi * (1 - (1 - Complex.arg z / Real.pi)) = Complex.arg z by
        field_simp; ring]
      exact cis'_arg hz1
    · right
      have hz_re : z = (z.re : ℂ) := Complex.ext rfl (by simp [hz2])
      have habs : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz1
      obtain ⟨hre0, hre1⟩ := abs_le.mp habs
      refine ⟨⟨(z.re + 1) / 2, ⟨by linarith, by linarith⟩⟩, ?_⟩
      change ((2 * ((z.re + 1) / 2) - 1 : ℝ) : ℂ) = z
      nth_rw 2 [hz_re]
      congr 1
      ring

/-- Map `N.D` homeomorphically onto `halfD 1` sending a boundary arc `ℓ` to `e_half`. -/
private lemma exists_half_disc_map (N : Net S) {ℓ : Curve N.D} (hinj : Function.Injective ℓ)
    (hr : range ℓ ⊆ bd N.D) :
    ∃ (p : N.D → ℂ) (q : ℂ → N.D), Continuous p ∧ ContinuousOn q (halfD 1) ∧
      (∀ x : N.D, p x ∈ halfD 1) ∧ (∀ x : N.D, q (p x) = x) ∧
      (∀ z ∈ halfD 1, p (q z) = z) ∧ (∀ u : unitInterval, p (ℓ u) = e_half u) ∧
      bd N.D = q '' (range a_half ∪ range e_half) := by
  obtain ⟨h, g, c⟩ := N.isClosedDisc_D.exists_isChart
  have hbd_univ : discBd (univ : Set N.D) = bd N.D :=
    image_bd_homeomorph (Homeomorph.Set.univ N.D)
  have hr' : range ℓ ⊆ discBd (univ : Set N.D) := hbd_univ.symm ▸ hr
  have hrΔ : ∀ u : unitInterval, ℓ u ∈ (univ : Set N.D) := fun _ => trivial
  let c₀ : unitInterval → ℂ := fun u => h (ℓ u)
  have hc₀ : IsArcMap c₀ := ⟨c.hc.comp_continuous ℓ.continuous hrΔ, fun u v huv =>
    hinj (c.gh.injOn (hrΔ u) (hrΔ v) huv)⟩
  have hsub : range c₀ ⊆ Metric.sphere (0 : ℂ) 1 := by
    rintro _ ⟨u, rfl⟩
    rw [← c.bd]
    exact mem_image_of_mem h (hr' ⟨u, rfl⟩)
  obtain ⟨φ₀⟩ := oArc_sphere
  obtain ⟨d, hd, d0, d1, hu, hmd⟩ := exists_other_arc φ₀ hc₀ hsub
  obtain ⟨h₀, k₀, m, -, v2⟩ := exists_bdMatch_of_arcs hd hc₀ isArcMap_a_half isArcMap_e_half
    d0.symm d1.symm (e_half_zero.trans a_half_zero.symm) (e_half_one.trans a_half_one.symm)
    (fun s t hst => (hmd t s hst.symm).imp And.symm And.symm) a_half_eq_e_half
  rw [union_comm (range d), hu] at m
  have hO : Nonempty (Circle ≃ₜ side a_half e_half) :=
    oArc_of_two_arcs isArcMap_a_half isArcMap_e_half
      (a_half_zero.trans e_half_zero.symm) (a_half_one.trans e_half_one.symm) a_half_eq_e_half
  obtain ⟨ψ, χ, m', hψ⟩ := exists_bdMatch_closedInner ⟨φ₀⟩ hO m
  have hcl_eq : closedInner (side a_half e_half) = halfD 1 :=
    (eq_closedInner_of_discBd (side_a_half_e_half ▸ hO) (isClosedDisc_halfD one_ne_zero).1
      side_a_half_e_half.symm).symm
  rw [closedInner_sphere, hcl_eq] at m'
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := id m'
  refine ⟨ψ ∘ h, g ∘ χ,
    continuousOn_univ.mp (n5.comp c.hc c.hm),
    c.gc.comp n6 n2,
    fun x => n1 (c.hm (mem_univ x)),
    fun x => by
      change g (χ (ψ (h x))) = x
      rw [n3 (c.hm (mem_univ x))]
      exact c.gh (mem_univ x),
    fun z hz => by
      change ψ (h (g (χ z))) = z
      rw [c.hg (n2 hz)]
      exact n4 hz,
    fun u => by
      change ψ (c₀ u) = e_half u
      rw [hψ (hsub ⟨u, rfl⟩), v2],
    ?_⟩
  rw [← hbd_univ]
  change discBd (univ : Set N.D) = (g ∘ χ) '' side a_half e_half
  rw [← show h₀ '' Metric.sphere (0 : ℂ) 1 = side a_half e_half from m.image_eq,
      ← hψ.image_eq, image_image, ← c.g_sphere]
  refine image_congr fun z hz => ?_
  change g z = g (χ (ψ z))
  rw [n3 (Metric.sphere_subset_closedBall hz)]

/-- Folding `(N.f i₀, N.g i₀)` when `N.f i₀ 0 = N.g i₀ 0` and `N.f i₀ 1 ≠ N.g i₀ 1`: there is a
quotient map `π : N.D → N.D` whose only non-trivial fibers are `{N.f i₀ t, N.g i₀ t}` for
`t : unitInterval` and which maps `bd N.D \ (N.f i₀ '' Ico 0 1 ∪ N.g i₀ '' Ico 0 1)` onto `bd N.D`.
-/
lemma exists_fold_quotient (N : Net S) {i₀ : Fin N.r}
    (hfg0 : N.f i₀ 0 = N.g i₀ 0) (hfg1_ne : N.f i₀ 1 ≠ N.g i₀ 1) :
    ∃ π : N.D → N.D,
      Topology.IsQuotientMap π ∧
      (∀ x y : N.D, π x = π y ↔
        x = y ∨ ∃ t : unitInterval,
          (x = N.f i₀ t ∧ y = N.g i₀ t) ∨ (x = N.g i₀ t ∧ y = N.f i₀ t)) ∧
      (∀ x : N.D, π x ∈ bd N.D ↔
        x ∈ bd N.D ∧ x ∉ N.f i₀ '' Ico (0 : unitInterval) 1 ∪ N.g i₀ '' Ico (0 : unitInterval) 1)
          := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hsymm_Ioo : ∀ {t : unitInterval}, t ∈ Ioo (0 : unitInterval) 1 →
      unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := Subtype.coe_lt_coe.mpr ht.1
    have ht1 : (t : ℝ) < 1 := Subtype.coe_lt_coe.mpr ht.2
    constructor <;> rw [← Subtype.coe_lt_coe]
    · change (0 : ℝ) < 1 - (t : ℝ); linarith
    · change 1 - (t : ℝ) < 1; linarith
  have hrev_f1 : (revCurve (N.f i₀)) 1 = N.g i₀ 0 := by simpa using hfg0
  let c_fold : Curve N.D := concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1
  have hinj_c_fold : Function.Injective c_fold :=
    injective_concatCurve hrev_f1 (injective_revCurve (N.injective_f i₀)) (N.injective_g i₀)
      (by simpa using hfg1_ne)
      (fun t ht => N.internally_disjoint_fg i₀ i₀ _ (hsymm_Ioo ht))
      (fun t ht => by rw [range_revCurve]; exact N.internally_disjoint_gf i₀ i₀ t ht)
  have hrange_c_fold : range c_fold = range (N.f i₀) ∪ range (N.g i₀) := by
    change range (concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1) = _
    rw [range_concatCurve, range_revCurve]
  have hr_c_fold : range c_fold ⊆ bd N.D :=
    hrange_c_fold ▸ union_subset (N.range_f_subset_bd i₀) (N.range_g_subset_bd i₀)
  obtain ⟨p, q, hp_cont, _, hp_mem, hqp, hpq, hp_c_fold, hbd_eq⟩ :=
    N.exists_half_disc_map hinj_c_fold hr_c_fold
  have hp_f : ∀ t : unitInterval, p (N.f i₀ t) = - ((t : ℝ) : ℂ) := by
    intro t
    let u : unitInterval := ⟨(1 - (t : ℝ)) / 2, ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩
    have hu_le : (u : ℝ) ≤ 1 / 2 := by
      change (1 - (t : ℝ)) / 2 ≤ 1 / 2; linarith [t.2.1]
    have h2u : unitInterval.symm ⟨2 * (u : ℝ), ⟨by linarith [u.2.1], by linarith⟩⟩ = t := by
      ext; change 1 - 2 * ((1 - (t : ℝ)) / 2) = t; ring
    have hc_u : c_fold u = N.f i₀ t := by
      change concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1 u = N.f i₀ t
      rw [concatCurve_apply, dite_eq_left hu_le, revCurve_apply, h2u]
    rw [← hc_u, hp_c_fold u]
    change ((2 * ((1 - (t : ℝ)) / 2) - 1 : ℝ) : ℂ) = - ((t : ℝ) : ℂ)
    push_cast
    ring
  have hp_g : ∀ t : unitInterval, p (N.g i₀ t) = ((t : ℝ) : ℂ) := by
    intro t
    rcases eq_or_lt_of_le t.2.1 with ht0 | ht_pos
    · have ht_eq0 : t = 0 := Subtype.ext ht0.symm
      subst ht_eq0
      rw [← hfg0, hp_f 0]
      simp
    · let u : unitInterval := ⟨((t : ℝ) + 1) / 2, ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩
      have hu_gt : ¬ (u : ℝ) ≤ 1 / 2 := by
        change ¬ ((t : ℝ) + 1) / 2 ≤ 1 / 2; linarith
      have h2u : (⟨2 * (u : ℝ) - 1, ⟨by linarith, by linarith [u.2.2]⟩⟩ : unitInterval) = t := by
        ext; change 2 * (((t : ℝ) + 1) / 2) - 1 = t; ring
      have hc_u : c_fold u = N.g i₀ t := by
        change concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1 u = N.g i₀ t
        rw [concatCurve_apply, dite_eq_right hu_gt, h2u]
      rw [← hc_u, hp_c_fold u]
      change ((2 * (((t : ℝ) + 1) / 2) - 1 : ℝ) : ℂ) = ((t : ℝ) : ℂ)
      push_cast
      ring
  obtain ⟨h_D, g_D, c_D⟩ := N.isClosedDisc_D.exists_isChart
  have hbd_univ : discBd (univ : Set N.D) = bd N.D :=
    image_bd_homeomorph (Homeomorph.Set.univ N.D)
  let π : N.D → N.D := fun x => g_D ((p x) ^ 2)
  have hsq_mem : ∀ x : N.D, (p x) ^ 2 ∈ Metric.closedBall (0 : ℂ) 1 := fun x => by
    rw [Metric.mem_closedBall, dist_zero_right, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hp_mem x).1
  have hπ_cont : Continuous π := c_D.gc.comp_continuous (hp_cont.pow 2) hsq_mem
  have hπ_surj : Function.Surjective π := by
    intro y
    have hy_ball : ‖h_D y‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using c_D.hm (mem_univ y)
    obtain ⟨w, hw_mem, hw_sq⟩ := exists_sqrt_half hy_ball
    refine ⟨q w, ?_⟩
    change g_D ((p (q w)) ^ 2) = y
    rw [hpq w hw_mem, hw_sq]
    exact c_D.gh (mem_univ y)
  have hπ_quot : Topology.IsQuotientMap π :=
    (hπ_cont.isClosedMap).isQuotientMap hπ_cont hπ_surj
  have hπ_eq_iff : ∀ x y : N.D, π x = π y ↔
      x = y ∨ ∃ t : unitInterval,
        (x = N.f i₀ t ∧ y = N.g i₀ t) ∨ (x = N.g i₀ t ∧ y = N.f i₀ t) := by
    intro x y
    constructor
    · intro heq
      have hsq_eq : (p x) ^ 2 = (p y) ^ 2 := c_D.injOn (hsq_mem x) (hsq_mem y) heq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq with hp_eq | hp_neg
      · exact Or.inl (by rw [← hqp x, ← hqp y, hp_eq])
      · right
        have hx_im : 0 ≤ (p x).im := by simpa using (hp_mem x).2
        have hy_im : 0 ≤ (p y).im := by simpa using (hp_mem y).2
        have hy_im0 : (p y).im = 0 := by
          rw [hp_neg, Complex.neg_im] at hx_im
          linarith
        have hpy_re : p y = (((p y).re : ℝ) : ℂ) := Complex.ext rfl (by simp [hy_im0])
        have habs : |(p y).re| ≤ 1 := (Complex.abs_re_le_norm (p y)).trans (hp_mem y).1
        obtain ⟨hre0, hre1⟩ := abs_le.mp habs
        rcases le_total 0 (p y).re with hnonneg | hnonpos
        · let t : unitInterval := ⟨(p y).re, ⟨hnonneg, hre1⟩⟩
          refine ⟨t, Or.inl ⟨?_, ?_⟩⟩
          · rw [← hqp x, hp_neg, hpy_re, ← hp_f t, hqp]
          · rw [← hqp y, hpy_re, ← hp_g t, hqp]
        · let t : unitInterval := ⟨- (p y).re, ⟨by linarith, by linarith⟩⟩
          refine ⟨t, Or.inr ⟨?_, ?_⟩⟩
          · rw [← hqp x, hp_neg, hpy_re, show - (((p y).re : ℝ) : ℂ) = ((t : ℝ) : ℂ) by
              change - (((p y).re : ℝ) : ℂ) = ((- (p y).re : ℝ) : ℂ); push_cast; ring, ← hp_g t,
                hqp]
          · rw [← hqp y, hpy_re, show (((p y).re : ℝ) : ℂ) = - ((t : ℝ) : ℂ) by
              change (((p y).re : ℝ) : ℂ) = - ((- (p y).re : ℝ) : ℂ); push_cast; ring, ← hp_f t,
                hqp]
    · rintro (rfl | ⟨t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
      · rfl
      · change g_D ((p (N.f i₀ t)) ^ 2) = g_D ((p (N.g i₀ t)) ^ 2)
        rw [hp_f t, hp_g t, neg_sq]
      · change g_D ((p (N.g i₀ t)) ^ 2) = g_D ((p (N.f i₀ t)) ^ 2)
        rw [hp_f t, hp_g t, neg_sq]
  have hπ_bd_iff : ∀ x : N.D, π x ∈ bd N.D ↔ ‖p x‖ = 1 := by
    intro x
    rw [← hbd_univ, ← c_D.g_sphere]
    constructor
    · rintro ⟨w, hw, heq⟩
      have hw_eq : w = (p x) ^ 2 := c_D.injOn (Metric.sphere_subset_closedBall hw) (hsq_mem x) heq
      have hnorm_sq : ‖p x‖ ^ 2 = 1 := by
        rw [← norm_pow, ← hw_eq]
        simpa [Metric.mem_sphere, dist_zero_right] using hw
      nlinarith [norm_nonneg (p x)]
    · intro hnorm
      refine ⟨(p x) ^ 2, ?_, rfl⟩
      simp [norm_pow, hnorm]
  have hq_e_half : q '' range e_half = range (N.f i₀) ∪ range (N.g i₀) := by
    rw [← hrange_c_fold]
    ext x
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, by rw [← hp_c_fold u, hqp]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨e_half u, ⟨u, rfl⟩, by rw [← hp_c_fold u, hqp]⟩
  refine ⟨π, hπ_quot, hπ_eq_iff, fun x => ⟨?_, ?_⟩⟩
  · intro hπ_bd
    have hnorm : ‖p x‖ = 1 := (hπ_bd_iff x).mp hπ_bd
    refine ⟨?_, ?_⟩
    · rw [hbd_eq]
      refine ⟨p x, ?_, hqp x⟩
      change p x ∈ side a_half e_half
      rw [side_a_half_e_half, (isClosedDisc_halfD one_ne_zero).2]
      exact Or.inl ⟨by simpa using hnorm, (hp_mem x).2⟩
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · rw [hp_f t, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.2.1] at hnorm
        exact (Subtype.coe_lt_coe.mpr ht.2).ne hnorm
      · rw [hp_g t, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.2.1] at hnorm
        exact (Subtype.coe_lt_coe.mpr ht.2).ne hnorm
  · rintro ⟨hx_bd, hx_notMem⟩
    rw [hπ_bd_iff]
    rw [hbd_eq, image_union, hq_e_half] at hx_bd
    rcases hx_bd with ⟨z, ⟨s, rfl⟩, rfl⟩ | (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · have ha_mem : a_half s ∈ halfD 1 :=
        discBd_subset (halfD 1) (side_a_half_e_half ▸ Or.inl ⟨s, rfl⟩)
      rw [hpq _ ha_mem]
      exact norm_cis' _
    · rcases eq_or_lt_of_le t.2.2 with ht1 | ht_lt
      · have ht_eq1 : t = 1 := Subtype.ext ht1
        subst ht_eq1; rw [hp_f 1]; simp
      · exact False.elim (hx_notMem (Or.inl ⟨t, ⟨t.2.1, ht_lt⟩, rfl⟩))
    · rcases eq_or_lt_of_le t.2.2 with ht1 | ht_lt
      · have ht_eq1 : t = 1 := Subtype.ext ht1
        subst ht_eq1; rw [hp_g 1]; simp
      · exact False.elim (hx_notMem (Or.inr ⟨t, ⟨t.2.1, ht_lt⟩, rfl⟩))

open Classical in
private noncomputable abbrev collapse_single_net_pair
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    {v : S}
    (hv_not_bd : v ∉ bd S)
    {i₀ : Fin N.r}
    (hi₀_0 : N.φ ((N.f i₀) 0) = v)
    (hi₀_1 : N.φ ((N.f i₀) 1) ≠ v)
    (hother : ∀ (j : Fin N.r), j ≠ i₀ → N.φ ((N.f j) 0) ≠ v ∧ N.φ ((N.f j) 1) ≠ v)
    [T2Space S]
    (t_half : unitInterval)
    (ht_half : t_half ∈ Ioo 0 1)
    (hstep_v : ∀ {j : Fin N.r} {t : unitInterval}, N.φ ((N.f j) t) = v → j = i₀ ∧ t = 0)
    (hfg0 : (N.f i₀) 0 = (N.g i₀) 0)
    (hfg1_ne : (N.f i₀) 1 ≠ (N.g i₀) 1)
    (π : N.D → N.D)
    (hπ_eq_iff : ∀ (x y : N.D), π x = π y ↔ x = y ∨ ∃ t, x = (N.f i₀) t ∧ y = (N.g i₀) t ∨ x =
      (N.g i₀) t ∧ y = (N.f i₀) t)
    (hπ_bd : ∀ (x : N.D), π x ∈ bd N.D ↔ x ∈ bd N.D ∧ x ∉ ⇑(N.f i₀) '' Ico 0 1 ∪ ⇑(N.g i₀) '' Ico
      0 1)
    (hπ_cont : Continuous π)
    (hπ_surj : Function.Surjective π)
    (φ' : N.D → S)
    (hφ'_π : ∀ (x : N.D), φ' (π x) = N.φ x)
    (hφ'_quot : IsQuotientMap φ')
    (hrev_f1 : (revCurve (N.f i₀)) 1 = (N.g i₀) 0)
    (hinj_c_fold : Function.Injective ⇑(concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1))
    (hrange_c_fold : range ⇑(concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1) = range ⇑(N.f i₀) ∪
      range ⇑(N.g i₀))
    (hr_c_fold : range ⇑(concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1) ⊆ bd N.D)
    (hc_fold_0 : (concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1) 0 = (N.f i₀) 1)
    (hc_fold_1 : (concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1) 1 = (N.g i₀) 1)
    (hnot_Ico_of_ne : ∀ {j : Fin N.r}, j ≠ i₀ → ∀ {x : N.D}, x ∈ range ⇑(N.f j) ∪ range ⇑(N.g j) →
      x ∉ ⇑(N.f i₀) '' Ico 0 1 ∪ ⇑(N.g i₀) '' Ico 0 1)
    (hnot_ends_of_disj : ∀ {c c' : Curve N.D}, Function.Injective ⇑c → range ⇑c ⊆ bd N.D → range
      ⇑c' ⊆ bd N.D → (∀ t ∈ Ioo 0 1, c t ∉ range ⇑(N.f i₀) ∧ c t ∉ range ⇑(N.g i₀)) → c' t_half ∉
      range ⇑c ∧ c' t_half ∉ range ⇑(N.f i₀) ∧ c' t_half ∉ range ⇑(N.g i₀) → ¬(c 0 = (N.f i₀) 1 ∧
      c 1 = (N.g i₀) 1))
    (hinj_π_curve : ∀ {c c' : Curve N.D}, Function.Injective ⇑c → range ⇑c ⊆ bd N.D → range ⇑c' ⊆
      bd N.D → (∀ (t : unitInterval), c t ∉ ⇑(N.f i₀) '' Ico 0 1 ∪ ⇑(N.g i₀) '' Ico 0 1) → (∀ t ∈
      Ioo 0 1, c t ∉ range ⇑(N.f i₀) ∧ c t ∉ range ⇑(N.g i₀)) → c' t_half ∉ range ⇑c ∧ c' t_half ∉
      range ⇑(N.f i₀) ∧ c' t_half ∉ range ⇑(N.g i₀) → Function.Injective (π ∘ ⇑c))
    (idx : Fin (N.r - 1) → Fin N.r)
    (hidx_inj : Function.Injective idx)
    (hidx_ne : ∀ (k : Fin (N.r - 1)), idx k ≠ i₀)
    (hsurj_other : ∀ (j : Fin N.r), j ≠ i₀ → ∃ k, idx k = j)
    (hπ_single_of_notMem : ∀ {x y : N.D}, x ∉ range ⇑(N.f i₀) ∧ x ∉ range ⇑(N.g i₀) → (π x = π y ↔
      x = y)) : Net S :=
  let c_fold := concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1
  {
    D := N.D
    isSurface_D := N.isSurface_D
    isClosedDisc_D := N.isClosedDisc_D
    φ := φ'
    quotientMap_φ := hφ'_quot
    r := N.r - 1
    f := fun k => ⟨π ∘ N.f (idx k), hπ_cont.comp (N.f (idx k)).continuous⟩
    g := fun k => ⟨π ∘ N.g (idx k), hπ_cont.comp (N.g (idx k)).continuous⟩
    injective_f := fun k =>
      hinj_π_curve (c := N.f (idx k)) (c' := N.g (idx k))
        (N.injective_f (idx k)) (N.range_f_subset_bd (idx k)) (N.range_g_subset_bd (idx k))
        (fun t => hnot_Ico_of_ne (hidx_ne k) (Or.inl ⟨t, rfl⟩))
        (fun t ht => ⟨N.internally_disjoint_ff (idx k) i₀ (hidx_ne k) t ht,
          N.internally_disjoint_fg (idx k) i₀ t ht⟩)
        ⟨N.internally_disjoint_gf (idx k) (idx k) t_half ht_half,
          N.internally_disjoint_gf (idx k) i₀ t_half ht_half,
          N.internally_disjoint_gg (idx k) i₀ (hidx_ne k) t_half ht_half⟩
    injective_g := fun k =>
      hinj_π_curve (c := N.g (idx k)) (c' := N.f (idx k))
        (N.injective_g (idx k)) (N.range_g_subset_bd (idx k)) (N.range_f_subset_bd (idx k))
        (fun t => hnot_Ico_of_ne (hidx_ne k) (Or.inr ⟨t, rfl⟩))
        (fun t ht => ⟨N.internally_disjoint_gf (idx k) i₀ t ht,
          N.internally_disjoint_gg (idx k) i₀ (hidx_ne k) t ht⟩)
        ⟨N.internally_disjoint_fg (idx k) (idx k) t_half ht_half,
          N.internally_disjoint_ff (idx k) i₀ (hidx_ne k) t_half ht_half,
          N.internally_disjoint_fg (idx k) i₀ t_half ht_half⟩
    range_f_subset_bd := by
      rintro k _ ⟨t, rfl⟩
      exact (hπ_bd _).mpr ⟨N.range_f_subset_bd (idx k) ⟨t, rfl⟩,
        hnot_Ico_of_ne (hidx_ne k) (Or.inl ⟨t, rfl⟩)⟩
    range_g_subset_bd := by
      rintro k _ ⟨t, rfl⟩
      exact (hπ_bd _).mpr ⟨N.range_g_subset_bd (idx k) ⟨t, rfl⟩,
        hnot_Ico_of_ne (hidx_ne k) (Or.inr ⟨t, rfl⟩)⟩
    internally_disjoint_ff := by
      rintro k₁ k₂ hk12 t ht ⟨s, hs⟩
      change π (N.f (idx k₂) s) = π (N.f (idx k₁) t) at hs
      have h_eq : N.f (idx k₁) t = N.f (idx k₂) s :=
        (hπ_single_of_notMem ⟨N.internally_disjoint_ff (idx k₁) i₀ (hidx_ne k₁) t ht,
          N.internally_disjoint_fg (idx k₁) i₀ t ht⟩).mp hs.symm
      exact N.internally_disjoint_ff (idx k₁) (idx k₂) (fun h => hk12 (hidx_inj h)) t ht ⟨s,
        h_eq.symm⟩
    internally_disjoint_gg := by
      rintro k₁ k₂ hk12 t ht ⟨s, hs⟩
      change π (N.g (idx k₂) s) = π (N.g (idx k₁) t) at hs
      have h_eq : N.g (idx k₁) t = N.g (idx k₂) s :=
        (hπ_single_of_notMem ⟨N.internally_disjoint_gf (idx k₁) i₀ t ht,
          N.internally_disjoint_gg (idx k₁) i₀ (hidx_ne k₁) t ht⟩).mp hs.symm
      exact N.internally_disjoint_gg (idx k₁) (idx k₂) (fun h => hk12 (hidx_inj h)) t ht ⟨s,
        h_eq.symm⟩
    internally_disjoint_fg := by
      rintro k₁ k₂ t ht ⟨s, hs⟩
      change π (N.g (idx k₂) s) = π (N.f (idx k₁) t) at hs
      have h_eq : N.f (idx k₁) t = N.g (idx k₂) s :=
        (hπ_single_of_notMem ⟨N.internally_disjoint_ff (idx k₁) i₀ (hidx_ne k₁) t ht,
          N.internally_disjoint_fg (idx k₁) i₀ t ht⟩).mp hs.symm
      exact N.internally_disjoint_fg (idx k₁) (idx k₂) t ht ⟨s, h_eq.symm⟩
    internally_disjoint_gf := by
      rintro k₁ k₂ t ht ⟨s, hs⟩
      change π (N.f (idx k₂) s) = π (N.g (idx k₁) t) at hs
      have h_eq : N.g (idx k₁) t = N.f (idx k₂) s :=
        (hπ_single_of_notMem ⟨N.internally_disjoint_gf (idx k₁) i₀ t ht,
          N.internally_disjoint_gg (idx k₁) i₀ (hidx_ne k₁) t ht⟩).mp hs.symm
      exact N.internally_disjoint_gf (idx k₁) (idx k₂) t ht ⟨s, h_eq.symm⟩
    pasting_eq := by
      intro k t
      change φ' (π (N.f (idx k) t)) = φ' (π (N.g (idx k) t))
      rw [hφ'_π, hφ'_π]
      exact N.pasting_eq (idx k) t
    interior_inj := by
      intro z₁ hz₁ z₂ hφ'_eq
      obtain ⟨x₁, rfl⟩ := hπ_surj z₁
      obtain ⟨x₂, rfl⟩ := hπ_surj z₂
      rw [hφ'_π, hφ'_π] at hφ'_eq
      by_cases hx₁_bd : x₁ ∈ bd N.D
      · have hx₁_Ico : x₁ ∈ N.f i₀ '' Ico (0 : unitInterval) 1 ∪ N.g i₀ '' Ico
          (0 : unitInterval) 1 := by
          by_contra hx₁_notMem
          exact hz₁ ((hπ_bd x₁).mpr ⟨hx₁_bd, hx₁_notMem⟩)
        have hIco_eq :
            ∃ t ∈ Ico (0 : unitInterval) 1, π x₁ = π (N.f i₀ t) ∧ N.φ x₁ = N.φ (N.f i₀ t) := by
          rcases hx₁_Ico with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
          · exact ⟨t, ht, rfl, rfl⟩
          · exact ⟨t, ht, (hπ_eq_iff _ _).mpr (Or.inr ⟨t, Or.inr ⟨rfl, rfl⟩⟩),
              (N.pasting_eq i₀ t).symm⟩
        obtain ⟨t₁, ht₁, hπ₁, hφ₁⟩ := hIco_eq
        rw [hπ₁]
        have hφ_x₂ : N.φ x₂ = N.φ (N.f i₀ t₁) := hφ'_eq.symm.trans hφ₁
        rcases eq_or_lt_of_le ht₁.1 with ht₁0 | ht₁_pos
        · have ht₁_eq0 : t₁ = 0 := ht₁0.symm
          subst ht₁_eq0
          have hφ_x₂_v : N.φ x₂ = v := hφ_x₂.trans hi₀_0
          have hx₂_bd : x₂ ∈ bd N.D := by
            rw [← N.preimage_seamU, mem_preimage, hφ_x₂_v, ← hi₀_0]
            exact ⟨N.f i₀ 0, N.range_f_subset_bd i₀ ⟨0, rfl⟩, rfl⟩
          have hx₂_pasted := N.mem_pasted_of_mem_bd_of_notMem_bd hx₂_bd
            (hφ_x₂_v.symm ▸ hv_not_bd)
          rw [mem_iUnion] at hx₂_pasted
          rcases hx₂_pasted with ⟨j, ⟨t₂, rfl⟩ | ⟨t₂, rfl⟩⟩
          · rcases hstep_v hφ_x₂_v with ⟨rfl, rfl⟩
            rfl
          · rcases hstep_v ((N.pasting_eq j t₂).trans hφ_x₂_v) with ⟨rfl, rfl⟩
            exact (hπ_eq_iff _ _).mpr (Or.inr ⟨0, Or.inl ⟨rfl, rfl⟩⟩)
        · have ht₁_Ioo : t₁ ∈ Ioo (0 : unitInterval) 1 := ⟨ht₁_pos, ht₁.2⟩
          rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i₀ ht₁_Ioo hφ_x₂.symm with rfl | rfl
          · rfl
          · exact (hπ_eq_iff _ _).mpr (Or.inr ⟨t₁, Or.inl ⟨rfl, rfl⟩⟩)
      · rw [N.interior_inj x₁ hx₁_bd x₂ hφ'_eq]
    bd_eq_iff := by
      intro z₁ z₂
      obtain ⟨x₁, rfl⟩ := hπ_surj z₁
      obtain ⟨x₂, rfl⟩ := hπ_surj z₂
      rw [hφ'_π, hφ'_π, N.bd_eq_iff x₁ x₂]
      let R_N (a b : N.D) : Prop := ∃ (j : Fin N.r) (t : unitInterval), a = N.f j t ∧ b = N.g j t
      let R_N' (u v : N.D) : Prop :=
        ∃ (k : Fin (N.r - 1)) (t : unitInterval), u = π (N.f (idx k) t) ∧ v = π (N.g (idx k) t)
      change Relation.EqvGen R_N x₁ x₂ ↔ Relation.EqvGen R_N' (π x₁) (π x₂)
      have hπ_rel : ∀ a b : N.D, π a = π b → Relation.EqvGen R_N a b := by
        intro a b heq
        rcases (hπ_eq_iff a b).mp heq with rfl | ⟨t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact Relation.EqvGen.refl _
        · exact Relation.EqvGen.rel _ _ ⟨i₀, t, rfl, rfl⟩
        · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨i₀, t, rfl, rfl⟩)
      constructor
      · intro hrel
        induction hrel with
        | rel a b hab =>
          rcases hab with ⟨j, t, rfl, rfl⟩
          by_cases hj : j = i₀
          · cases hj
            have hπ_fg : π (N.f i₀ t) = π (N.g i₀ t) :=
              (hπ_eq_iff _ _).mpr (Or.inr ⟨t, Or.inl ⟨rfl, rfl⟩⟩)
            rw [hπ_fg]
            exact Relation.EqvGen.refl _
          · obtain ⟨k, rfl⟩ := hsurj_other j hj
            exact Relation.EqvGen.rel _ _ ⟨k, t, rfl, rfl⟩
        | refl _ => exact Relation.EqvGen.refl _
        | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
      · intro hrel'
        have hlift : ∀ u v : N.D, Relation.EqvGen R_N' u v →
            ∀ a b : N.D, π a = u → π b = v → Relation.EqvGen R_N a b := by
          intro u v huv
          induction huv with
          | rel u v huv =>
            rcases huv with ⟨k, t, rfl, rfl⟩
            intro a b ha hb
            exact Relation.EqvGen.trans _ _ _ (hπ_rel a _ ha)
              (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨idx k, t, rfl, rfl⟩)
                (hπ_rel _ b hb.symm))
          | refl u =>
            intro a b ha hb
            exact hπ_rel a b (ha.trans hb.symm)
          | symm u v _ ih =>
            intro a b ha hb
            exact Relation.EqvGen.symm _ _ (ih b a hb ha)
          | trans u w v _ _ ih1 ih2 =>
            intro a b ha hb
            obtain ⟨c, rfl⟩ := hπ_surj w
            exact Relation.EqvGen.trans _ _ _ (ih1 a c ha rfl) (ih2 c b rfl hb)
        exact hlift (π x₁) (π x₂) hrel' x₁ x₂ rfl rfl
  }

private theorem single_pair_has_distinct_final_ends
    {S : Type u}
    [TopologicalSpace S]
    (hS : IsSurface S)
    (h000 : ¬Nonempty (S ≃ₜ SurfaceModel 0 0 0))
    (h010 : ¬Nonempty (S ≃ₜ SurfaceModel 0 1 0))
    (h001 : ¬Nonempty (S ≃ₜ SurfaceModel 0 0 1))
    {G : Drawing S}
    (N : Net S)
    (hmin : N.IsMinimalFor G)
    {v : S}
    (hv_not_bd : v ∉ bd S)
    {i₀ : Fin N.r}
    (hi₀_0 : N.φ ((N.f i₀) 0) = v)
    [T2Space S]
    (t_half : ↑unitInterval)
    (ht_half : t_half ∈ Ioo 0 1)
    (hfg0 : (N.f i₀) 0 = (N.g i₀) 0) :
    (N.f i₀) 1 ≠ (N.g i₀) 1 := by
  intro heq
  have hbd_eq : range (N.f i₀) ∪ range (N.g i₀) = bd N.D :=
    N.range_union_eq_bd_of_same_ends (N.injective_f i₀) (N.range_f_subset_bd i₀)
      (N.injective_g i₀) (N.range_g_subset_bd i₀) hfg0 heq (by
        rw [disjoint_left]
        rintro _ ⟨t, ht, rfl⟩ ⟨s, _, hs⟩
        exact N.internally_disjoint_fg i₀ i₀ t ht ⟨s, hs⟩)
  have hno_j : ∀ j : Fin N.r, j ≠ i₀ → False := by
    intro j hj
    have hmem : N.f j t_half ∈ range (N.f i₀) ∪ range (N.g i₀) :=
      hbd_eq.symm ▸ N.range_f_subset_bd j ⟨t_half, rfl⟩
    rcases hmem with hf | hg
    · exact N.internally_disjoint_ff j i₀ hj t_half ht_half hf
    · exact N.internally_disjoint_fg j i₀ t_half ht_half hg
  have hf1_not_bd : N.φ (N.f i₀ 1) ∉ bd S := by
    intro hp_bd
    let C : Set S := connectedComponentIn (bd S) (N.φ (N.f i₀ 1))
    have hC_mem : C ∈ cuffs S := ⟨N.φ (N.f i₀ 1), hp_bd, rfl⟩
    have hC_sub : C ⊆ bd S := connectedComponentIn_subset _ _
    obtain ⟨e_cuff⟩ := (cuff_statement S hS).2.2 C hC_mem
    have h1_ne_neg1 : (1 : Circle) ≠ (-1 : Circle) := by
      intro h
      have h' : (1 : ℂ) = (-1 : ℂ) := congr_arg Subtype.val h
      norm_num at h'
    have hex_ne : ∃ z ∈ C, z ≠ N.φ (N.f i₀ 1) := by
      by_cases h1 : (e_cuff 1).1 = N.φ (N.f i₀ 1)
      · refine ⟨(e_cuff (-1)).1, (e_cuff (-1)).2, ?_⟩
        intro h2
        exact h1_ne_neg1 (e_cuff.injective (Subtype.ext (h1.trans h2.symm)))
      · exact ⟨(e_cuff 1).1, (e_cuff 1).2, h1⟩
    obtain ⟨z, hzC, hz_ne⟩ := hex_ne
    have hz_bdS : z ∈ bd S := hC_sub hzC
    obtain ⟨x, hx_bd, rfl⟩ := N.bd_subset_seamU hz_bdS
    rw [← hbd_eq] at hx_bd
    have hex_t : ∃ t : unitInterval, N.φ x = N.φ (N.f i₀ t) := by
      rcases hx_bd with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨t, rfl⟩
      · exact ⟨t, (N.pasting_eq i₀ t).symm⟩
    obtain ⟨t, ht_eq⟩ := hex_t
    rw [ht_eq] at hz_bdS hz_ne
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht_Ioo
    · exact hv_not_bd (hi₀_0 ▸ hz_bdS)
    · exact hz_ne rfl
    · exact N.notMem_bd_of_mem_Ioo hS i₀ ht_Ioo hz_bdS
  obtain ⟨J, hJ, _⟩ := hmin.1
  exact N.not_isolated_pair_of_not_sphere_proj_disc hS h000 h010 h001 hJ i₀
    (hi₀_0.symm ▸ hv_not_bd) hf1_not_bd (fun j hj => False.elim (hno_j j hj))

private theorem other_pairs_avoid_fold_endpoints
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    {v : S}
    {i₀ : Fin N.r}
    (hi₀_0 : N.φ ((N.f i₀) 0) = v)
    (hother : ∀ (j : Fin N.r), j ≠ i₀ → N.φ ((N.f j) 0) ≠ v ∧ N.φ ((N.f j) 1) ≠ v)
    (hv_seamV : v ∈ N.seamV) :
    ∀ {j : Fin N.r}, j ≠ i₀ → ∀ {x : N.D}, x ∈ range ⇑(N.f j) ∪ range ⇑(N.g j) → x ∉ ⇑(N.f i₀) ''
      Ico 0 1 ∪ ⇑(N.g i₀) '' Ico 0 1 := by
  intro j hj x hx_mem hIco
  rcases hIco with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · rcases eq_or_lt_of_le hs.1 with hs0 | hs_pos
    · have hs_eq0 : s = 0 := hs0.symm
      subst hs_eq0
      exact N.not_φ_eq_of_mem_range_fg hv_seamV (hother j hj).1 (hother j hj).2 hx_mem hi₀_0
    · have hs_Ioo : s ∈ Ioo (0 : unitInterval) 1 := ⟨hs_pos, hs.2⟩
      rcases hx_mem with hfj | hgj
      · exact N.internally_disjoint_ff i₀ j hj.symm s hs_Ioo hfj
      · exact N.internally_disjoint_fg i₀ j s hs_Ioo hgj
  · rcases eq_or_lt_of_le hs.1 with hs0 | hs_pos
    · have hs_eq0 : s = 0 := hs0.symm
      subst hs_eq0
      exact N.not_φ_eq_of_mem_range_fg hv_seamV (hother j hj).1 (hother j hj).2 hx_mem
        ((N.pasting_eq i₀ 0).symm.trans hi₀_0)
    · have hs_Ioo : s ∈ Ioo (0 : unitInterval) 1 := ⟨hs_pos, hs.2⟩
      rcases hx_mem with hfj | hgj
      · exact N.internally_disjoint_gf i₀ j s hs_Ioo hfj
      · exact N.internally_disjoint_gg i₀ j hj.symm s hs_Ioo hgj

private theorem another_curve_excludes_fold_end_pair
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    {i₀ : Fin N.r}
    (t_half : ↑unitInterval)
    (c_fold : Curve N.D)
    (hinj_c_fold : Function.Injective ⇑c_fold)
    (hrange_c_fold : range ⇑c_fold = range ⇑(N.f i₀) ∪ range ⇑(N.g i₀))
    (hr_c_fold : range ⇑c_fold ⊆ bd N.D)
    (hc_fold_0 : c_fold 0 = (N.f i₀) 1)
    (hc_fold_1 : c_fold 1 = (N.g i₀) 1) :
    ∀ {c c' : Curve N.D}, Function.Injective ⇑c → range ⇑c ⊆ bd N.D → range ⇑c' ⊆ bd N.D → (∀ t ∈
      Ioo 0 1, c t ∉ range ⇑(N.f i₀) ∧ c t ∉ range ⇑(N.g i₀)) → c' t_half ∉ range ⇑c ∧ c' t_half ∉
      range ⇑(N.f i₀) ∧ c' t_half ∉ range ⇑(N.g i₀) → ¬(c 0 = (N.f i₀) 1 ∧ c 1 = (N.g i₀) 1) := by
  intro c c' hc_inj hc_bd hc'_bd hc_disj hc'_half ⟨hc0, hc1⟩
  have hbd_eq : range c ∪ range c_fold = bd N.D :=
    N.range_union_eq_bd_of_same_ends hc_inj hc_bd hinj_c_fold hr_c_fold
      (hc0.trans hc_fold_0.symm) (hc1.trans hc_fold_1.symm) (by
        rw [disjoint_left]
        rintro _ ⟨t, ht, rfl⟩ hmem
        have hmem' : c t ∈ range c_fold := image_subset_range _ _ hmem
        rw [hrange_c_fold] at hmem'
        rcases hmem' with hf | hg
        · exact (hc_disj t ht).1 hf
        · exact (hc_disj t ht).2 hg)
  rw [hrange_c_fold] at hbd_eq
  have hmem : c' t_half ∈ range c ∪ (range (N.f i₀) ∪ range (N.g i₀)) :=
    hbd_eq.symm ▸ hc'_bd ⟨t_half, rfl⟩
  rcases hmem with hc_mem | (hf_mem | hg_mem)
  · exact hc'_half.1 hc_mem
  · exact hc'_half.2.1 hf_mem
  · exact hc'_half.2.2 hg_mem

private theorem fold_injective_on_remaining_curve
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    {i₀ : Fin N.r}
    (hsymm_Ioo : ∀ {t : ↑unitInterval}, t ∈ Ioo 0 1 → unitInterval.symm t ∈ Ioo 0 1)
    (t_half : ↑unitInterval)
    (hfg1_ne : (N.f i₀) 1 ≠ (N.g i₀) 1)
    (π : N.D → N.D)
    (hπ_eq_iff : ∀ (x y : N.D), π x = π y ↔ x = y ∨ ∃ t, x = (N.f i₀) t ∧ y = (N.g i₀) t ∨ x =
      (N.g i₀) t ∧ y = (N.f i₀) t)
    (hnot_ends_of_disj : ∀ {c c' : Curve N.D}, Function.Injective ⇑c → range ⇑c ⊆ bd N.D → range
      ⇑c' ⊆ bd N.D → (∀ t ∈ Ioo 0 1, c t ∉ range ⇑(N.f i₀) ∧ c t ∉ range ⇑(N.g i₀)) → c' t_half ∉
      range ⇑c ∧ c' t_half ∉ range ⇑(N.f i₀) ∧ c' t_half ∉ range ⇑(N.g i₀) → ¬(c 0 = (N.f i₀) 1 ∧
      c 1 = (N.g i₀) 1)) :
    ∀ {c c' : Curve N.D}, Function.Injective ⇑c → range ⇑c ⊆ bd N.D → range ⇑c' ⊆ bd N.D → (∀ (t :
      ↑unitInterval), c t ∉ ⇑(N.f i₀) '' Ico 0 1 ∪ ⇑(N.g i₀) '' Ico 0 1) → (∀ t ∈ Ioo 0 1, c t ∉
      range ⇑(N.f i₀) ∧ c t ∉ range ⇑(N.g i₀)) → c' t_half ∉ range ⇑c ∧ c' t_half ∉ range ⇑(N.f
      i₀) ∧ c' t_half ∉ range ⇑(N.g i₀) → Function.Injective (π ∘ ⇑c) := by
  intro c c' hc_inj hc_bd hc'_bd hc_not_Ico hc_disj hc'_half t₁ t₂ heq
  rcases (hπ_eq_iff (c t₁) (c t₂)).mp heq with hct | ⟨s, hcs⟩
  · exact hc_inj hct
  · exfalso
    have hs1 : s = 1 := by
      rcases eq_or_lt_of_le s.2.2 with hs1 | hs_lt
      · exact Subtype.ext hs1
      · exfalso
        rcases hcs with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hc_not_Ico t₁ (Or.inl ⟨s, ⟨s.2.1, hs_lt⟩, h1.symm⟩)
        · exact hc_not_Ico t₁ (Or.inr ⟨s, ⟨s.2.1, hs_lt⟩, h1.symm⟩)
    subst hs1
    have ht₁_not_Ioo : t₁ ∉ Ioo (0 : unitInterval) 1 := by
      intro ht₁
      rcases hcs with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact (hc_disj t₁ ht₁).1 ⟨1, h1.symm⟩
      · exact (hc_disj t₁ ht₁).2 ⟨1, h1.symm⟩
    have ht₂_not_Ioo : t₂ ∉ Ioo (0 : unitInterval) 1 := by
      intro ht₂
      rcases hcs with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact (hc_disj t₂ ht₂).2 ⟨1, h2.symm⟩
      · exact (hc_disj t₂ ht₂).1 ⟨1, h2.symm⟩
    have ht12_ne : t₁ ≠ t₂ := by
      rintro rfl
      rcases hcs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hfg1_ne (h1.symm.trans h2)
      · exact hfg1_ne (h2.symm.trans h1)
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo t₁ with rfl | rfl | ht₁_Ioo <;>
      rcases unitInterval_eq_zero_or_one_or_mem_Ioo t₂ with rfl | rfl | ht₂_Ioo
    · exact ht12_ne rfl
    · rcases hcs with h01 | h01
      · exact hnot_ends_of_disj hc_inj hc_bd hc'_bd hc_disj hc'_half h01
      · exact hnot_ends_of_disj (c := revCurve c) (c' := c')
          (injective_revCurve hc_inj) (by rw [range_revCurve]; exact hc_bd) hc'_bd
          (fun t ht => hc_disj _ (hsymm_Ioo ht))
          (by rw [range_revCurve]; exact hc'_half)
          ⟨by simpa using h01.2, by simpa using h01.1⟩
    · exact ht₂_not_Ioo ht₂_Ioo
    · rcases hcs with h10 | h10
      · exact hnot_ends_of_disj (c := revCurve c) (c' := c')
          (injective_revCurve hc_inj) (by rw [range_revCurve]; exact hc_bd) hc'_bd
          (fun t ht => hc_disj _ (hsymm_Ioo ht))
          (by rw [range_revCurve]; exact hc'_half)
          ⟨by simpa using h10.1, by simpa using h10.2⟩
      · exact hnot_ends_of_disj hc_inj hc_bd hc'_bd hc_disj hc'_half ⟨h10.2, h10.1⟩
    · exact ht12_ne rfl
    · exact ht₂_not_Ioo ht₂_Ioo
    · exact ht₁_not_Ioo ht₁_Ioo
    · exact ht₁_not_Ioo ht₁_Ioo
    · exact ht₁_not_Ioo ht₁_Ioo

/-- Excluding Case 2 / Subcase B2c (`(N.F₂ v).card = 0` and `(N.F₁ v).card = 1`): a single
non-loop seam pair incident with an interior vertex `v ∉ bd S` and no other seam pairs incident
with `v` cannot occur in a minimal net `N` on a surface `S` not homeomorphic to `Σ(0, 0, 0)`,
`Σ(0, 1, 0)`, or `Σ(0, 0, 1)`. -/
theorem not_one_pair_at_interior_vertex (hS : IsSurface S)
    (h000 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 0))
    (h010 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 1 0))
    (h001 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 1))
    {G : Drawing S} (N : Net S) (hmin : N.IsMinimalFor G)
    {v : S} (hv_not_bd : v ∉ bd S) {i₀ : Fin N.r}
    (hi₀_0 : N.φ (N.f i₀ 0) = v) (hi₀_1 : N.φ (N.f i₀ 1) ≠ v)
    (hother : ∀ j : Fin N.r, j ≠ i₀ → N.φ (N.f j 0) ≠ v ∧ N.φ (N.f j 1) ≠ v) :
    False := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hv_seamV : v ∈ N.seamV := ⟨i₀, Or.inl hi₀_0⟩
  have hsymm_Ioo : ∀ {t : unitInterval}, t ∈ Ioo (0 : unitInterval) 1 →
      unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := Subtype.coe_lt_coe.mpr ht.1
    have ht1 : (t : ℝ) < 1 := Subtype.coe_lt_coe.mpr ht.2
    constructor <;> rw [← Subtype.coe_lt_coe]
    · change (0 : ℝ) < 1 - (t : ℝ); linarith
    · change 1 - (t : ℝ) < 1; linarith
  let t_half : unitInterval := ⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩
  have ht_half : t_half ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe]
    · change (0 : ℝ) < 1 / 2; norm_num
    · change (1 / 2 : ℝ) < 1; norm_num
  have hstep_v : ∀ {j : Fin N.r} {t : unitInterval}, N.φ (N.f j t) = v → j = i₀ ∧ t = 0 := by
    intro j t hφft
    by_cases hj : j = i₀
    · cases hj
      rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
      · exact ⟨rfl, rfl⟩
      · exact False.elim (hi₀_1 hφft)
      · exact False.elim (N.notMem_seamV_of_mem_Ioo i₀ ht (hφft.symm ▸ hv_seamV))
    · exact False.elim (N.not_φ_eq_of_mem_range_fg hv_seamV (hother j hj).1
        (hother j hj).2 (Or.inl ⟨t, rfl⟩) hφft)
  have hfg0 : N.f i₀ 0 = N.g i₀ 0 := by
    rcases N.mem_other_range_of_φ_f_eq hS hv_not_bd (Or.inl rfl) hi₀_0 with
      ⟨j, hj, t, ht⟩ | ⟨j, t, ht⟩
    · exact False.elim (hj (hstep_v ((congr_arg N.φ ht).trans hi₀_0)).1)
    · rcases hstep_v ((N.pasting_eq j t).trans ((congr_arg N.φ ht).trans hi₀_0)) with ⟨rfl, rfl⟩
      exact ht.symm
  have hfg1_ne : N.f i₀ 1 ≠ N.g i₀ 1 := by
    exact single_pair_has_distinct_final_ends (S := S) hS h000 h010 h001 (G := G) N hmin (v := v)
      hv_not_bd (i₀ := i₀) hi₀_0 t_half ht_half hfg0
  obtain ⟨π, hπ_quot, hπ_eq_iff, hπ_bd⟩ :=
    N.exists_fold_quotient hfg0 hfg1_ne
  have hπ_cont : Continuous π := hπ_quot.continuous
  have hπ_surj : Function.Surjective π := hπ_quot.surjective
  let φ' : N.D → S := fun z => N.φ (Function.surjInv hπ_surj z)
  have hφ'_π : ∀ x : N.D, φ' (π x) = N.φ x := by
    intro x
    change N.φ (Function.surjInv hπ_surj (π x)) = N.φ x
    have hπ_inv : π (Function.surjInv hπ_surj (π x)) = π x :=
      Function.surjInv_eq hπ_surj (π x)
    rcases (hπ_eq_iff _ _).mp hπ_inv with heq | ⟨t, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · rw [heq]
    · rw [h1, h2, N.pasting_eq i₀ t]
    · rw [h1, h2, ← N.pasting_eq i₀ t]
  have hφ'_cont : Continuous φ' := by
    rw [hπ_quot.continuous_iff]
    have : φ' ∘ π = N.φ := funext hφ'_π
    rw [this]
    exact N.quotientMap_φ.continuous
  have hφ'_surj : Function.Surjective φ' := by
    intro y
    obtain ⟨x, rfl⟩ := N.quotientMap_φ.surjective y
    exact ⟨π x, hφ'_π x⟩
  have hφ'_quot : Topology.IsQuotientMap φ' :=
    (hφ'_cont.isClosedMap).isQuotientMap hφ'_cont hφ'_surj
  by_cases hr2 : 2 ≤ N.r
  · have hrev_f1 : (revCurve (N.f i₀)) 1 = N.g i₀ 0 := by simpa using hfg0
    let c_fold : Curve N.D := concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1
    have hinj_c_fold : Function.Injective c_fold :=
      injective_concatCurve hrev_f1 (injective_revCurve (N.injective_f i₀)) (N.injective_g i₀)
        (by simpa using hfg1_ne)
        (fun t ht => N.internally_disjoint_fg i₀ i₀ _ (hsymm_Ioo ht))
        (fun t ht => by rw [range_revCurve]; exact N.internally_disjoint_gf i₀ i₀ t ht)
    have hrange_c_fold : range c_fold = range (N.f i₀) ∪ range (N.g i₀) := by
      change range (concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1) = _
      rw [range_concatCurve, range_revCurve]
    have hr_c_fold : range c_fold ⊆ bd N.D :=
      hrange_c_fold ▸ union_subset (N.range_f_subset_bd i₀) (N.range_g_subset_bd i₀)
    have hc_fold_0 : c_fold 0 = N.f i₀ 1 := by
      change concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1 0 = N.f i₀ 1
      rw [concatCurve_zero, revCurve_zero]
    have hc_fold_1 : c_fold 1 = N.g i₀ 1 := by
      change concatCurve (revCurve (N.f i₀)) (N.g i₀) hrev_f1 1 = N.g i₀ 1
      rw [concatCurve_one]
    have hnot_Ico_of_ne : ∀ {j : Fin N.r} (hj : j ≠ i₀) {x : N.D},
        x ∈ range (N.f j) ∪ range (N.g j) →
        x ∉ N.f i₀ '' Ico (0 : unitInterval) 1 ∪ N.g i₀ '' Ico (0 : unitInterval) 1 := by
      exact other_pairs_avoid_fold_endpoints (S := S) N (v := v) (i₀ := i₀) hi₀_0 hother hv_seamV
    have hnot_ends_of_disj : ∀ {c c' : Curve N.D},
        Function.Injective c → range c ⊆ bd N.D → range c' ⊆ bd N.D →
        (∀ t ∈ Ioo (0 : unitInterval) 1, c t ∉ range (N.f i₀) ∧ c t ∉ range (N.g i₀)) →
        (c' t_half ∉ range c ∧ c' t_half ∉ range (N.f i₀) ∧ c' t_half ∉ range (N.g i₀)) →
        ¬ (c 0 = N.f i₀ 1 ∧ c 1 = N.g i₀ 1) := by
      exact another_curve_excludes_fold_end_pair (S := S) N (i₀ := i₀) t_half c_fold hinj_c_fold
        hrange_c_fold hr_c_fold hc_fold_0 hc_fold_1
    have hinj_π_curve : ∀ {c c' : Curve N.D},
        Function.Injective c → range c ⊆ bd N.D → range c' ⊆ bd N.D →
        (∀ t : unitInterval, c t ∉ N.f i₀ '' Ico (0 : unitInterval) 1 ∪ N.g i₀ '' Ico
          (0 : unitInterval) 1) →
        (∀ t ∈ Ioo (0 : unitInterval) 1, c t ∉ range (N.f i₀) ∧ c t ∉ range (N.g i₀)) →
        (c' t_half ∉ range c ∧ c' t_half ∉ range (N.f i₀) ∧ c' t_half ∉ range (N.g i₀)) →
        Function.Injective (π ∘ c) := by
      exact fold_injective_on_remaining_curve (S := S) N (i₀ := i₀) hsymm_Ioo t_half hfg1_ne π
        hπ_eq_iff hnot_ends_of_disj
    let e : Fin (N.r - 1 + 1) ≃ Fin N.r := finCongr (by omega)
    let i₀' : Fin (N.r - 1 + 1) := e.symm i₀
    let idx (k : Fin (N.r - 1)) : Fin N.r := e (i₀'.succAbove k)
    have hidx_inj : Function.Injective idx := e.injective.comp Fin.succAbove_right_injective
    have hidx_ne : ∀ k : Fin (N.r - 1), idx k ≠ i₀ := by
      intro k h
      have : i₀'.succAbove k = i₀' := e.injective (by simpa [idx, i₀'] using h)
      exact Fin.succAbove_ne i₀' k this
    have hsurj_other : ∀ j : Fin N.r, j ≠ i₀ → ∃ k : Fin (N.r - 1), idx k = j := by
      intro j hj
      have hj'_ne : e.symm j ≠ i₀' := fun h => hj (e.symm.injective h)
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj'_ne
      exact ⟨k, by simp [idx, hk]⟩
    have hπ_single_of_notMem : ∀ {x y : N.D},
        x ∉ range (N.f i₀) ∧ x ∉ range (N.g i₀) → (π x = π y ↔ x = y) := by
      intro x y ⟨hxf, hxg⟩
      rw [hπ_eq_iff]
      constructor
      · rintro (rfl | ⟨s, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩)
        · rfl
        · exact False.elim (hxf ⟨s, rfl⟩)
        · exact False.elim (hxg ⟨s, rfl⟩)
      · exact Or.inl
    let N' : Net S :=
      collapse_single_net_pair (S := S) N (v := v) hv_not_bd (i₀ := i₀) hi₀_0 hi₀_1 hother t_half
        ht_half hstep_v hfg0 hfg1_ne π hπ_eq_iff hπ_bd hπ_cont hπ_surj φ' hφ'_π hφ'_quot hrev_f1
        hinj_c_fold hrange_c_fold hr_c_fold hc_fold_0 hc_fold_1 hnot_Ico_of_ne hnot_ends_of_disj
        hinj_π_curve idx hidx_inj hidx_ne hsurj_other hπ_single_of_notMem
    have hseamU_sub : N'.seamU ⊆ N.seamU := by
      rintro _ ⟨z, hz_bd, rfl⟩
      obtain ⟨x, rfl⟩ := hπ_surj z
      change φ' (π x) ∈ N.seamU
      rw [hφ'_π]
      exact ⟨x, ((hπ_bd x).mp hz_bd).1, rfl⟩
    have hN_norm := (N.isNormalFor_iff hS G).mp hmin.1
    have hN'_norm : N'.IsNormalFor G := by
      rw [N'.isNormalFor_iff hS G]
      exact ⟨by change 0 < N.r - 1; omega,
        (inter_subset_inter_left G.U hseamU_sub).trans hN_norm.2⟩
    have hcard_le : N'.bdVertexPreimageCard G ≤ N.bdVertexPreimageCard G := by
      refine Set.ncard_le_ncard_of_injOn (Function.surjInv hπ_surj)
        (fun z hz => ⟨?_, ?_⟩)
        (fun _ _ _ _ h => Function.injective_surjInv hπ_surj h)
        ((N.finite_preimage G.finite_V).subset inter_subset_left)
      · change N.φ (Function.surjInv hπ_surj z) ∈ G.V
        exact hz.1
      ·exact ((hπ_bd _).mp (by rw [Function.surjInv_eq hπ_surj]; exact hz.2)).1
    have hle : N.r ≤ N'.r := hmin.2.2 N' hN'_norm hcard_le
    change N.r ≤ N.r - 1 at hle
    omega
  · have hr1 : N.r = 1 := by
      have := i₀.2
      omega
    have hall_i₀ : ∀ j : Fin N.r, j = i₀ := by
      intro j
      ext
      omega
    have hφ'_inj : Function.Injective φ' := by
      intro z₁ z₂ heq
      obtain ⟨x₁, rfl⟩ := hπ_surj z₁
      obtain ⟨x₂, rfl⟩ := hπ_surj z₂
      rw [hφ'_π, hφ'_π, N.bd_eq_iff x₁ x₂] at heq
      induction heq with
      | rel a b hab =>
        rcases hab with ⟨j, t, rfl, rfl⟩
        rw [hall_i₀ j]
        exact (hπ_eq_iff _ _).mpr (Or.inr ⟨t, Or.inl ⟨rfl, rfl⟩⟩)
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    let e_φ' : N.D ≃ₜ S :=
      hφ'_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ' ⟨hφ'_inj, hφ'_surj⟩)
    obtain ⟨e_D⟩ := N.isClosedDisc_D
    obtain ⟨e_001⟩ := nonempty_disc_homeo
    exact h001 ⟨e_φ'.symm.trans ((Homeomorph.Set.univ N.D).symm.trans (e_D.symm.trans e_001.symm))⟩

end Net

/-- Graph Minors VII, (2.3) (pages 216–217):
"(2.3) *Let $\Sigma$ be a connected surface with $\Sigma \not\cong \Sigma(0, 0, 0)$, $\Sigma(0, 0,
1)$,
... $\Sigma(0, 1, 0)$. Let $J$ be the seam graph for some minimal net with respect to some proper
graph
$G$ in $\Sigma$. Then no vertex of $J$ has valency $\le 2$.*" -/
theorem minimalNet_minValency (S : Type u) [TopologicalSpace S]
    (hS : IsSurface S) (_hconn : ConnectedSpace S)
    (h000 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 0))
    (h001 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 1))
    (h010 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 1 0))
    (G J : Drawing S) (N : Net S)
    (_hG : G.IsProper) (hmin : N.IsMinimalFor G) (hJ : N.IsSeamGraphFor J)
    (v : S) (hv : v ∈ J.V) :
    3 ≤ vertexValency J v := by
  open Net in
  have : T2Space S := hS.2.1
  by_cases hv_bd : v ∈ bd S
  · exact N.three_le_vertexValency_of_mem_bd hS hJ hv hv_bd
  · have hle := N.card_F₁_add_two_mul_card_F₂_le_vertexValency hJ v
    have hv_seamV : v ∈ N.seamV := hJ.2.2 ▸ hv
    rcases hv_seamV with ⟨i₀, hi₀⟩
    have hpos : 1 ≤ (N.F₁ v).card + 2 * (N.F₂ v).card := by
      by_cases h1 : i₀ ∈ N.F₁ v
      · have : 1 ≤ (N.F₁ v).card := Finset.card_pos.mpr ⟨i₀, h1⟩
        omega
      · have h2 : i₀ ∈ N.F₂ v := by
          by_contra h2
          rcases (N.notMem_F₁_and_notMem_F₂_iff v i₀).mp ⟨h1, h2⟩ with ⟨hne0, hne1⟩
          exact hi₀.elim hne0 hne1
        have : 1 ≤ (N.F₂ v).card := Finset.card_pos.mpr ⟨i₀, h2⟩
        omega
    by_contra! hlt
    have hcases :
        ((N.F₂ v).card = 1 ∧ (N.F₁ v).card = 0) ∨
        ((N.F₂ v).card = 0 ∧ (N.F₁ v).card = 1) ∨
        ((N.F₂ v).card = 0 ∧ (N.F₁ v).card = 2) := by
      omega
    rcases hcases with ⟨hF₂_1, hF₁_0⟩ | ⟨hF₂_0, hF₁_1⟩ | ⟨hF₂_0, hF₁_2⟩
    · obtain ⟨i, hi_eq⟩ := Finset.card_eq_one.mp hF₂_1
      have hi_F₂ : i ∈ N.F₂ v := hi_eq ▸ Finset.mem_singleton_self i
      obtain ⟨hi_0, hi_1⟩ := (N.mem_F₂_iff v i).mp hi_F₂
      have hother : ∀ j : Fin N.r, j ≠ i → N.φ (N.f j 0) ≠ v ∧ N.φ (N.f j 1) ≠ v := by
        intro j hj
        refine (N.notMem_F₁_and_notMem_F₂_iff v j).mp ⟨?_, ?_⟩
        · rw [Finset.card_eq_zero.mp hF₁_0]; exact Finset.notMem_empty j
        · rw [hi_eq, Finset.mem_singleton]; exact hj
      exact N.not_loop_only_at_interior_vertex hS h000 h010 h001 hJ hv_bd i hi_0 hi_1 hother
    · obtain ⟨i, hi_eq⟩ := Finset.card_eq_one.mp hF₁_1
      have hi_F₁ : i ∈ N.F₁ v := hi_eq ▸ Finset.mem_singleton_self i
      have hother : ∀ j : Fin N.r, j ≠ i → N.φ (N.f j 0) ≠ v ∧ N.φ (N.f j 1) ≠ v := by
        intro j hj
        refine (N.notMem_F₁_and_notMem_F₂_iff v j).mp ⟨?_, ?_⟩
        · rw [hi_eq, Finset.mem_singleton]; exact hj
        · rw [Finset.card_eq_zero.mp hF₂_0]; exact Finset.notMem_empty j
      rcases (N.mem_F₁_iff v i).mp hi_F₁ with ⟨hi_0, hi_1⟩ | ⟨hi_0, hi_1⟩
      · exact N.not_one_pair_at_interior_vertex hS h000 h010 h001 hmin hv_bd hi_0 hi_1 hother
      · refine (N.revPair i).not_one_pair_at_interior_vertex hS h000 h010 h001
          ((N.isMinimalFor_revPair i G).mpr hmin) hv_bd (i₀ := i)
          (by change N.φ ((if i = i then revCurve (N.f i) else N.f i) 0) = v; simpa using hi_1)
          (by change N.φ ((if i = i then revCurve (N.f i) else N.f i) 1) ≠ v; simpa using hi_0)
          (by change ∀ j : Fin N.r, j ≠ i →
                N.φ ((if j = i then revCurve (N.f j) else N.f j) 0) ≠ v ∧
                N.φ ((if j = i then revCurve (N.f j) else N.f j) 1) ≠ v
              intro j hj; rw [ite_eq_right hj]; exact hother j hj)
    · obtain ⟨i₁, i₂, h12_ne, hF₁_eq⟩ := Finset.card_eq_two.mp hF₁_2
      have hi₁_F₁ : i₁ ∈ N.F₁ v := hF₁_eq ▸ Finset.mem_insert_self i₁ {i₂}
      have hi₂_F₁ : i₂ ∈ N.F₁ v :=
        hF₁_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self i₂)
      have hother : ∀ j : Fin N.r, j ≠ i₁ → j ≠ i₂ → N.φ (N.f j 0) ≠ v ∧ N.φ (N.f j 1) ≠ v := by
        intro j hj₁ hj₂
        refine (N.notMem_F₁_and_notMem_F₂_iff v j).mp ⟨?_, ?_⟩
        · rw [hF₁_eq, Finset.mem_insert, Finset.mem_singleton]
          exact not_or.mpr ⟨hj₁, hj₂⟩
        · rw [Finset.card_eq_zero.mp hF₂_0]; exact Finset.notMem_empty j
      have haux₁ : ∀ (M : Net S) (hM_min : M.IsMinimalFor G) {k₁ k₂ : Fin M.r} (hk12 : k₁ ≠ k₂),
          M.φ (M.f k₁ 0) ≠ v → M.φ (M.f k₁ 1) = v →
          ((M.φ (M.f k₂ 0) = v ∧ M.φ (M.f k₂ 1) ≠ v) ∨
            (M.φ (M.f k₂ 0) ≠ v ∧ M.φ (M.f k₂ 1) = v)) →
          (∀ j : Fin M.r, j ≠ k₁ → j ≠ k₂ → M.φ (M.f j 0) ≠ v ∧ M.φ (M.f j 1) ≠ v) →
          False := by
        intro M hM_min k₁ k₂ hk12 hk₁_0 hk₁_1 hk₂ hM_other
        rcases hk₂ with ⟨hk₂_0, hk₂_1⟩ | ⟨hk₂_0, hk₂_1⟩
        · exact M.not_two_pairs_at_interior_vertex hS hM_min hv_bd hk12
            hk₁_0 hk₁_1 hk₂_0 hk₂_1 hM_other
        · refine (M.revPair k₂).not_two_pairs_at_interior_vertex hS
            ((M.isMinimalFor_revPair k₂ G).mpr hM_min) hv_bd hk12
            (by change M.φ ((if k₁ = k₂ then revCurve (M.f k₁) else M.f k₁) 0) ≠ v
                rw [ite_eq_right hk12]; exact hk₁_0)
            (by change M.φ ((if k₁ = k₂ then revCurve (M.f k₁) else M.f k₁) 1) = v
                rw [ite_eq_right hk12]; exact hk₁_1)
            (by change M.φ ((if k₂ = k₂ then revCurve (M.f k₂) else M.f k₂) 0) = v
                simpa using hk₂_1)
            (by change M.φ ((if k₂ = k₂ then revCurve (M.f k₂) else M.f k₂) 1) ≠ v
                simpa using hk₂_0)
            (by change ∀ j : Fin M.r, j ≠ k₁ → j ≠ k₂ →
                  M.φ ((if j = k₂ then revCurve (M.f j) else M.f j) 0) ≠ v ∧
                  M.φ ((if j = k₂ then revCurve (M.f j) else M.f j) 1) ≠ v
                intro j hj₁ hj₂; rw [ite_eq_right hj₂]; exact hM_other j hj₁ hj₂)
      rcases (N.mem_F₁_iff v i₁).mp hi₁_F₁ with ⟨hi₁_0, hi₁_1⟩ | ⟨hi₁_0, hi₁_1⟩
      · refine haux₁ (N.revPair i₁) ((N.isMinimalFor_revPair i₁ G).mpr hmin) h12_ne
          (by change N.φ ((if i₁ = i₁ then revCurve (N.f i₁) else N.f i₁) 0) ≠ v; simpa using hi₁_1)
          (by change N.φ ((if i₁ = i₁ then revCurve (N.f i₁) else N.f i₁) 1) = v; simpa using hi₁_0)
          (by change (N.φ ((if i₂ = i₁ then revCurve (N.f i₂) else N.f i₂) 0) = v ∧
                N.φ ((if i₂ = i₁ then revCurve (N.f i₂) else N.f i₂) 1) ≠ v) ∨
              (N.φ ((if i₂ = i₁ then revCurve (N.f i₂) else N.f i₂) 0) ≠ v ∧
                N.φ ((if i₂ = i₁ then revCurve (N.f i₂) else N.f i₂) 1) = v)
              rw [ite_eq_right h12_ne.symm]; exact (N.mem_F₁_iff v i₂).mp hi₂_F₁)
          (by change ∀ j : Fin N.r, j ≠ i₁ → j ≠ i₂ →
                N.φ ((if j = i₁ then revCurve (N.f j) else N.f j) 0) ≠ v ∧
                N.φ ((if j = i₁ then revCurve (N.f j) else N.f j) 1) ≠ v
              intro j hj₁ hj₂; rw [ite_eq_right hj₁]; exact hother j hj₁ hj₂)
      · exact haux₁ N hmin h12_ne hi₁_0 hi₁_1 ((N.mem_F₁_iff v i₂).mp hi₂_F₁) hother

end GraphMinor.GM07
