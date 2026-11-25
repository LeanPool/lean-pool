/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Defs

/-!
# Graph Minors VI, Section 2: Dual Divisions and Theorems (2.1)–(2.3)

This file formalizes the topological transfer between an $O$-arc $C \subseteq S$ and `Circle`,
the segment and dual point set structure on `Circle`, and proves (2.1), (2.2), and (2.3) of
Robertson and Seymour, *Graph Minors. VI. Disjoint paths across a disc*, J. Combin. Theory
Ser. B **41** (1986), 115–138 (pages 117–118).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Function Topology GraphMinor.Surface

universe u

/-! ## 1. Transfer between an $O$-Arc $C \subseteq S$ and `Circle` -/

/-- The topological embedding $\text{Circle} \to S$ associated with a homeomorphism
$\phi \colon \text{Circle} \simeqₜ C$. -/
def oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C) : Circle → S :=
  Subtype.val ∘ φ

theorem isEmbedding_oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C) :
    IsEmbedding (oArcMap φ) :=
  IsEmbedding.subtypeVal.comp φ.isEmbedding

theorem injective_oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C) :
    Injective (oArcMap φ) :=
  (isEmbedding_oArcMap φ).injective

@[simp]
theorem oArcMap_mem {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C) (z : Circle) :
    oArcMap φ z ∈ C :=
  (φ z).2

@[simp]
theorem range_oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C) :
    range (oArcMap φ) = C := by
  ext x
  simp only [oArcMap, mem_range, comp_apply]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ (φ z).2, fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩⟩

theorem diff_image_oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    (s : Set Circle) : C \ (oArcMap φ '' s) = oArcMap φ '' sᶜ := by
  have hrange := range_oArcMap φ
  rw [← image_univ] at hrange
  rw [compl_eq_univ_sdiff, image_sdiff (injective_oArcMap φ), hrange]

/-- On `Circle` with $C = \text{univ}$, `CrossesOn univ` agrees with
`circleCrosses circleStdCoord`. -/
theorem crossesOn_univ_iff_circleStdCoord {a c b d : Circle} :
    CrossesOn (univ : Set Circle) a c b d ↔ circleCrosses circleStdCoord a c b d := by
  simp only [CrossesOn, Surface.PairsCrossOn, mem_univ, true_and, ← compl_eq_univ_sdiff]
  constructor
  · rintro ⟨hac, hbd, hab, had, hcb, hcd, hcc⟩
    exact (connectedComponentIn_compl_pair_ne_iff_circleCrosses hac hbd hab had hcb hcd).mp hcc
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      (connectedComponentIn_compl_pair_ne_iff_circleCrosses
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1).mpr h⟩

/-- On `Circle` with $C = \text{univ}$, `CrossesOn univ` agrees with
`circleCrosses (circleCoordFrom x)` for any basepoint $x \in \text{Circle}$. -/
theorem crossesOn_univ_iff_circleCoordFrom (x : Circle) {a c b d : Circle} :
    CrossesOn (univ : Set Circle) a c b d ↔ circleCrosses (circleCoordFrom x) a c b d := by
  rw [crossesOn_univ_iff_circleStdCoord, circleCrosses_circleCoordFrom_iff]

/-- Characterization of `CrossesOn univ` on `Circle` directly in terms of `a.angleDiff`. -/
theorem crossesOn_univ_iff_angleDiff {a c b d : Circle} :
    CrossesOn (univ : Set Circle) a c b d ↔
      a ≠ c ∧ b ≠ d ∧ a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d ∧
      (a.angleDiff b < a.angleDiff c ↔ ¬ a.angleDiff d < a.angleDiff c) := by
  rw [crossesOn_univ_iff_circleStdCoord, circleCrosses_circleStdCoord_iff_angleDiff]

/-- `CrossesOn C` is preserved and reflected by `oArcMap φ`. -/
theorem crossesOn_oArcMap_iff {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    {a c b d : Circle} :
    CrossesOn C (oArcMap φ a) (oArcMap φ c) (oArcMap φ b) (oArcMap φ d) ↔
      CrossesOn (univ : Set Circle) a c b d := by
  have hinj := injective_oArcMap φ
  have hemb := isEmbedding_oArcMap φ
  have hpair : C \ {oArcMap φ a, oArcMap φ c} = oArcMap φ '' ({a, c} : Set Circle)ᶜ := by
    rw [← diff_image_oArcMap φ]
    simp
  simp only [CrossesOn, Surface.PairsCrossOn, oArcMap_mem, mem_univ, true_and, hinj.ne_iff,
    ← compl_eq_univ_sdiff]
  refine and_congr_right fun hac => and_congr_right fun hbd =>
    and_congr_right fun hab => and_congr_right fun had =>
    and_congr_right fun hcb => and_congr_right fun hcd => ?_
  have hb_mem : b ∈ ({a, c} : Set Circle)ᶜ := by simp [hab.symm, hcb.symm]
  have hd_mem : d ∈ ({a, c} : Set Circle)ᶜ := by simp [had.symm, hcd.symm]
  rw [hpair, ← isEmbedding_image_connectedComponentIn hemb hb_mem,
    ← isEmbedding_image_connectedComponentIn hemb hd_mem, ne_eq, ne_eq, image_eq_image hinj]

theorem CrossesOn.symm_left {S : Type u} [TopologicalSpace S] {C : Set S} {a c b d : S}
    (h : CrossesOn C a c b d) : CrossesOn C c a b d := by
  rcases h with ⟨ha, hb, hc, hd, hac, hbd, hab, had, hcb, hcd, hcc⟩
  rw [pair_comm] at hcc
  exact ⟨hc, hb, ha, hd, hac.symm, hbd, hcb, hcd, hab, had, hcc⟩

theorem CrossesOn.symm_right {S : Type u} [TopologicalSpace S] {C : Set S} {a c b d : S}
    (h : CrossesOn C a c b d) : CrossesOn C a c d b := by
  rcases h with ⟨ha, hb, hc, hd, hac, hbd, hab, had, hcb, hcd, hcc⟩
  exact ⟨ha, hd, hc, hb, hac, hbd.symm, had, hab, hcd, hcb, hcc.symm⟩

theorem CrossesOn.comm {S : Type u} [TopologicalSpace S] {C : Set S} (hC : IsOArc C)
    {a c b d : S} (h : CrossesOn C a c b d) : CrossesOn C b d a c := by
  obtain ⟨φ⟩ := hC
  have ha : a ∈ C := h.1
  have hb : b ∈ C := h.2.1
  have hc : c ∈ C := h.2.2.1
  have hd : d ∈ C := h.2.2.2.1
  let a' := φ.symm ⟨a, ha⟩
  let b' := φ.symm ⟨b, hb⟩
  let c' := φ.symm ⟨c, hc⟩
  let d' := φ.symm ⟨d, hd⟩
  have ha' : oArcMap φ a' = a := by simp [oArcMap, a']
  have hb' : oArcMap φ b' = b := by simp [oArcMap, b']
  have hc' : oArcMap φ c' = c := by simp [oArcMap, c']
  have hd' : oArcMap φ d' = d := by simp [oArcMap, d']
  rw [← ha', ← hb', ← hc', ← hd'] at h ⊢
  rw [crossesOn_oArcMap_iff, crossesOn_univ_iff_circleStdCoord] at h ⊢
  exact (circleCrosses_comm circleStdCoord a' c' b' d').mp h

theorem not_crossesOn_trans {S : Type u} [TopologicalSpace S] {C : Set S} (hC : IsOArc C)
    {a c b₁ b₂ b₃ : S} (ha : a ∈ C) (hc : c ∈ C)
    (hb₁ : b₁ ∈ C) (hb₂ : b₂ ∈ C) (hb₃ : b₃ ∈ C)
    (ha₂ : a ≠ b₂) (hc₂ : c ≠ b₂)
    (h12 : ¬ CrossesOn C a c b₁ b₂) (h23 : ¬ CrossesOn C a c b₂ b₃) :
    ¬ CrossesOn C a c b₁ b₃ := by
  obtain ⟨φ⟩ := hC
  let a' := φ.symm ⟨a, ha⟩
  let c' := φ.symm ⟨c, hc⟩
  let b₁' := φ.symm ⟨b₁, hb₁⟩
  let b₂' := φ.symm ⟨b₂, hb₂⟩
  let b₃' := φ.symm ⟨b₃, hb₃⟩
  have ha' : oArcMap φ a' = a := by simp [oArcMap, a']
  have hc' : oArcMap φ c' = c := by simp [oArcMap, c']
  have hb₁' : oArcMap φ b₁' = b₁ := by simp [oArcMap, b₁']
  have hb₂' : oArcMap φ b₂' = b₂ := by simp [oArcMap, b₂']
  have hb₃' : oArcMap φ b₃' = b₃ := by simp [oArcMap, b₃']
  rw [← ha', ← hc', ← hb₁', ← hb₂'] at h12
  rw [← ha', ← hc', ← hb₂', ← hb₃'] at h23
  rw [← ha', ← hc', ← hb₁', ← hb₃']
  rw [crossesOn_oArcMap_iff, crossesOn_univ_iff_circleStdCoord] at h12 h23 ⊢
  exact not_circleCrosses_trans circleStdCoord
    (fun h => ha₂ (ha' ▸ hb₂' ▸ congrArg (oArcMap φ) h))
    (fun h => hc₂ (hc' ▸ hb₂' ▸ congrArg (oArcMap φ) h))
    h12 h23

theorem crossesOn_four_point {S : Type u} [TopologicalSpace S] {C : Set S} (hC : IsOArc C)
    {u₁ u₂ u₃ u₄ v₁ v₂ : S} (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C)
    (hv₁u₃ : v₁ ≠ u₃) (hv₂u₃ : v₂ ≠ u₃)
    (hv₁u₄ : v₁ ≠ u₄) (hv₂u₄ : v₂ ≠ u₄)
    (hu : CrossesOn C u₁ u₃ u₂ u₄) (hv : CrossesOn C v₁ v₂ u₁ u₂) :
    CrossesOn C v₁ v₂ u₁ u₃ ∨ CrossesOn C v₁ v₂ u₂ u₄ := by
  obtain ⟨φ⟩ := hC
  have hu₁ : u₁ ∈ C := hu.1
  have hu₂ : u₂ ∈ C := hu.2.1
  have hu₃ : u₃ ∈ C := hu.2.2.1
  have hu₄ : u₄ ∈ C := hu.2.2.2.1
  let u₁' := φ.symm ⟨u₁, hu₁⟩
  let u₂' := φ.symm ⟨u₂, hu₂⟩
  let u₃' := φ.symm ⟨u₃, hu₃⟩
  let u₄' := φ.symm ⟨u₄, hu₄⟩
  let v₁' := φ.symm ⟨v₁, hv₁⟩
  let v₂' := φ.symm ⟨v₂, hv₂⟩
  have hu₁' : oArcMap φ u₁' = u₁ := by simp [oArcMap, u₁']
  have hu₂' : oArcMap φ u₂' = u₂ := by simp [oArcMap, u₂']
  have hu₃' : oArcMap φ u₃' = u₃ := by simp [oArcMap, u₃']
  have hu₄' : oArcMap φ u₄' = u₄ := by simp [oArcMap, u₄']
  have hv₁' : oArcMap φ v₁' = v₁ := by simp [oArcMap, v₁']
  have hv₂' : oArcMap φ v₂' = v₂ := by simp [oArcMap, v₂']
  rw [← hu₁', ← hu₂', ← hu₃', ← hu₄', crossesOn_oArcMap_iff,
    crossesOn_univ_iff_circleStdCoord] at hu
  rw [← hv₁', ← hv₂', ← hu₁', ← hu₂', crossesOn_oArcMap_iff,
    crossesOn_univ_iff_circleStdCoord] at hv
  rw [← hv₁', ← hv₂', ← hu₁', ← hu₃', ← hu₂', ← hu₄',
    crossesOn_oArcMap_iff, crossesOn_oArcMap_iff,
    crossesOn_univ_iff_circleStdCoord, crossesOn_univ_iff_circleStdCoord]
  exact four_point_circleCrosses circleStdCoord hu hv
    (fun h => hv₁u₃ (hv₁' ▸ hu₃' ▸ congrArg (oArcMap φ) h))
    (fun h => hv₂u₃ (hv₂' ▸ hu₃' ▸ congrArg (oArcMap φ) h))
    (fun h => hv₁u₄ (hv₁' ▸ hu₄' ▸ congrArg (oArcMap φ) h))
    (fun h => hv₂u₄ (hv₂' ▸ hu₄' ▸ congrArg (oArcMap φ) h))

/-! ## 2. Equivalence Properties of `dualEquivRel` and Proof of (2.1) -/

theorem dualEquivRel_refl {S : Type u} [TopologicalSpace S] (C : Set S) (Δ : Set (Set S))
    (u : S) : dualEquivRel C Δ u u := by
  rintro ⟨δ, _, v, _, v', _, hcross⟩
  exact hcross.2.2.2.2.2.1 rfl

theorem dualEquivRel_symm {S : Type u} [TopologicalSpace S] {C : Set S} {Δ : Set (Set S)}
    {u u' : S} (h : dualEquivRel C Δ u u') : dualEquivRel C Δ u' u := by
  rintro ⟨δ, hδ, v, hv, v', hv', hcross⟩
  exact h ⟨δ, hδ, v, hv, v', hv', hcross.symm_right⟩

theorem dualEquivRel_trans {S : Type u} [TopologicalSpace S] {C U : Set S} {Δ : Set (Set S)}
    (hC : IsOArc C) (hV_sub : divisionUnion Δ ⊆ C) (hU_sub : U ⊆ C \ divisionUnion Δ)
    {u₁ u₂ u₃ : S} (hu₁ : u₁ ∈ U) (hu₂ : u₂ ∈ U) (hu₃ : u₃ ∈ U)
    (h12 : dualEquivRel C Δ u₁ u₂) (h23 : dualEquivRel C Δ u₂ u₃) :
    dualEquivRel C Δ u₁ u₃ := by
  rintro ⟨δ, hδ, v, hv, v', hv', hcross⟩
  have hv_mem : v ∈ divisionUnion Δ := ⟨δ, hδ, hv⟩
  have hv'_mem : v' ∈ divisionUnion Δ := ⟨δ, hδ, hv'⟩
  have h12' : ¬ CrossesOn C v v' u₁ u₂ := fun h => h12 ⟨δ, hδ, v, hv, v', hv', h⟩
  have h23' : ¬ CrossesOn C v v' u₂ u₃ := fun h => h23 ⟨δ, hδ, v, hv, v', hv', h⟩
  exact not_crossesOn_trans hC (hV_sub hv_mem) (hV_sub hv'_mem)
    (hU_sub hu₁).1 (hU_sub hu₂).1 (hU_sub hu₃).1
    (fun h => (hU_sub hu₂).2 (h ▸ hv_mem))
    (fun h => (hU_sub hu₂).2 (h ▸ hv'_mem))
    h12' h23' hcross

theorem isDualPointSet_subset_diff {S : Type u} [TopologicalSpace S] {C V U : Set S}
    (hU : IsDualPointSet C V U) : U ⊆ C \ V := by
  rcases V.eq_empty_or_nonempty with rfl | hne
  · rw [hU.1 rfl]
    exact empty_subset _
  · exact (hU.2 hne).1

theorem dualDivision_mem_eq_of_mem {S : Type u} [TopologicalSpace S] {C U : Set S}
    {Δ : Set (Set S)} (hC : IsOArc C) (hV_sub : divisionUnion Δ ⊆ C)
    (hU_sub : U ⊆ C \ divisionUnion Δ) {δ_star : Set S} (hδ : δ_star ∈ dualDivision C U Δ)
    {u : S} (hu : u ∈ δ_star) :
    δ_star = {u' ∈ U | dualEquivRel C Δ u u'} := by
  rcases hδ with ⟨u₀, hu₀, rfl⟩
  simp only [mem_ofPred_eq] at hu
  ext u'
  simp only [mem_ofPred_eq]
  refine and_congr_right fun hu' => ⟨?_, ?_⟩
  · intro h₀
    exact dualEquivRel_trans hC hV_sub hU_sub hu.1 hu₀ hu' (dualEquivRel_symm hu.2) h₀
  · intro h₁
    exact dualEquivRel_trans hC hV_sub hU_sub hu₀ hu.1 hu' hu.2 h₁

/-- **Graph Minors VI, (2.1)** (page 117):
"$\Delta^*$ is cross-free, for any $\Delta$." -/
theorem theorem_2_1_proof : Statement21 := by
  intro S _ C U Δ hC _hΔ hV_sub hU
  have hU_sub : U ⊆ C \ divisionUnion Δ := isDualPointSet_subset_diff hU
  rintro ⟨δ₁, hδ₁, δ₂, hδ₂, hne, u₁, hu₁, u₃, hu₃, u₂, hu₂, u₄, hu₄, hcross⟩
  have hδ₁_eq := dualDivision_mem_eq_of_mem hC hV_sub hU_sub hδ₁ hu₁
  have hδ₂_eq := dualDivision_mem_eq_of_mem hC hV_sub hU_sub hδ₂ hu₂
  have hu₁_U : u₁ ∈ U := by rw [hδ₁_eq] at hu₁; exact hu₁.1
  have hu₃_rel : dualEquivRel C Δ u₁ u₃ := by rw [hδ₁_eq] at hu₃; exact hu₃.2
  have hu₂_U : u₂ ∈ U := by rw [hδ₂_eq] at hu₂; exact hu₂.1
  have hu₄_rel : dualEquivRel C Δ u₂ u₄ := by rw [hδ₂_eq] at hu₄; exact hu₄.2
  have hu₃_U : u₃ ∈ U := by rw [hδ₁_eq] at hu₃; exact hu₃.1
  have hu₄_U : u₄ ∈ U := by rw [hδ₂_eq] at hu₄; exact hu₄.1
  have hnot_rel : ¬ dualEquivRel C Δ u₁ u₂ := by
    intro h12
    have hu₂_in_δ₁ : u₂ ∈ δ₁ := by
      rw [hδ₁_eq]
      exact ⟨hu₂_U, h12⟩
    exact hne ((dualDivision_mem_eq_of_mem hC hV_sub hU_sub hδ₁ hu₂_in_δ₁).trans hδ₂_eq.symm)
  unfold dualEquivRel at hnot_rel
  push Not at hnot_rel
  obtain ⟨δ, hδ, v₁, hv₁, v₂, hv₂, hv_cross⟩ := hnot_rel
  have hv₁_V : v₁ ∈ divisionUnion Δ := ⟨δ, hδ, hv₁⟩
  have hv₂_V : v₂ ∈ divisionUnion Δ := ⟨δ, hδ, hv₂⟩
  rcases crossesOn_four_point (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) (u₄ := u₄) (v₁ := v₁) (v₂ := v₂)
    hC (hV_sub hv₁_V) (hV_sub hv₂_V)
    (fun h => (hU_sub hu₃_U).2 (h ▸ hv₁_V))
    (fun h => (hU_sub hu₃_U).2 (h ▸ hv₂_V))
    (fun h => (hU_sub hu₄_U).2 (h ▸ hv₁_V))
    (fun h => (hU_sub hu₄_U).2 (h ▸ hv₂_V))
    hcross hv_cross with h13 | h24
  · exact hu₃_rel ⟨δ, hδ, v₁, hv₁, v₂, hv₂, h13⟩
  · exact hu₄_rel ⟨δ, hδ, v₁, hv₁, v₂, hv₂, h24⟩

/-! ## 3. Segments and Dual Point Sets on `Circle` and on $O$-Arcs -/

theorem nextSegment_mem_segmentsOf_univ {V : Set Circle} (hV : V.Finite) {v : Circle}
    (hv : v ∈ V) : nextSegment V v ∈ segmentsOf (univ : Set Circle) V := by
  obtain ⟨z, hz⟩ := nextSegment_nonempty hV hv
  have hz_compl : z ∈ (univ : Set Circle) \ V := ⟨trivial, nextSegment_subset_compl hz⟩
  refine ⟨⟨z, hz_compl, ?_⟩, nonempty_homeomorph_Ioo_nextSegment hV hv⟩
  rw [← compl_eq_univ_sdiff]
  exact connectedComponentIn_compl_eq_nextSegment hV hv hz

theorem prevSegment_mem_segmentsOf_univ {V : Set Circle} (hV : V.Finite) {v : Circle}
    (hv : v ∈ V) : prevSegment V v ∈ segmentsOf (univ : Set Circle) V := by
  obtain ⟨v_prev, hv_prev, heq⟩ := exists_nextSegment_eq_prevSegment hV hv
  rw [heq]
  exact nextSegment_mem_segmentsOf_univ hV hv_prev

theorem mem_segmentsOf_univ_iff {V : Set Circle} (hV : V.Finite) (hne : V.Nonempty)
    {seg : Set Circle} :
    seg ∈ segmentsOf (univ : Set Circle) V ↔ ∃ v ∈ V, seg = nextSegment V v := by
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, _⟩
    rw [← compl_eq_univ_sdiff] at hz ⊢
    obtain ⟨v, ⟨hv, hzv⟩, _⟩ := exists_unique_nextSegment_of_mem_compl hV hne hz
    exact ⟨v, hv, connectedComponentIn_compl_eq_nextSegment hV hv hzv⟩
  · rintro ⟨v, hv, rfl⟩
    exact nextSegment_mem_segmentsOf_univ hV hv

theorem exists_unique_mem_nextSegment_of_isDualPointSet {V U : Set Circle} (hV : V.Finite)
    (hU : IsDualPointSet (univ : Set Circle) V U) {v : Circle} (hv : v ∈ V) :
    ∃ u, U ∩ nextSegment V v = {u} := by
  have hne : V.Nonempty := ⟨v, hv⟩
  have hseg := nextSegment_mem_segmentsOf_univ hV hv
  exact ncard_eq_one.mp ((hU.2 hne).2 _ hseg)

theorem exists_unique_mem_prevSegment_of_isDualPointSet {V U : Set Circle} (hV : V.Finite)
    (hU : IsDualPointSet (univ : Set Circle) V U) {v : Circle} (hv : v ∈ V) :
    ∃ u, U ∩ prevSegment V v = {u} := by
  have hne : V.Nonempty := ⟨v, hv⟩
  have hseg := prevSegment_mem_segmentsOf_univ hV hv
  exact ncard_eq_one.mp ((hU.2 hne).2 _ hseg)

theorem finite_of_isDualPointSet_univ {V U : Set Circle} (hV : V.Finite)
    (hU : IsDualPointSet (univ : Set Circle) V U) : U.Finite := by
  rcases V.eq_empty_or_nonempty with rfl | hne
  · rw [hU.1 rfl]
    exact finite_empty
  · have hU_sub : U ⊆ ⋃ v ∈ V, (U ∩ nextSegment V v) := by
      intro u hu
      have hu_compl : u ∈ Vᶜ := ((hU.2 hne).1 hu).2
      obtain ⟨v, ⟨hv, huv⟩, _⟩ := exists_unique_nextSegment_of_mem_compl hV hne hu_compl
      exact mem_biUnion hv ⟨hu, huv⟩
    refine (hV.biUnion fun v hv => ?_).subset hU_sub
    obtain ⟨u, hu⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hV hU hv
    rw [hu]
    exact finite_singleton u

theorem nextSegment_dual_properties {V U : Set Circle}
    (hU : IsDualPointSet (univ : Set Circle) V U) {v u : Circle} (hv : v ∈ V)
    (hu : U ∩ nextSegment V v = {u}) :
    u ∈ U ∧ u ≠ v ∧
    (∀ w ∈ V \ {v}, v.angleDiff u < v.angleDiff w) ∧
    (∀ u' ∈ U \ {u}, ∃ w ∈ V \ {v}, v.angleDiff u < v.angleDiff w ∧ v.angleDiff w < v.angleDiff u')
      := by
  have hu_mem : u ∈ U ∩ nextSegment V v := by rw [hu]; exact mem_singleton u
  have huU : u ∈ U := hu_mem.1
  have hu_seg : u ∈ nextSegment V v := hu_mem.2
  have hU_compl : U ⊆ Vᶜ := fun x hx => ((hU.2 ⟨v, hv⟩).1 hx).2
  refine ⟨huU, hu_seg.1, hu_seg.2, fun u' hu' => ?_⟩
  have hu'_not : u' ∉ nextSegment V v := by
    intro h
    have hmem : u' ∈ U ∩ nextSegment V v := ⟨hu'.1, h⟩
    rw [hu, mem_singleton_iff] at hmem
    exact hu'.2 hmem
  have hu'_ne_v : u' ≠ v := fun h => hU_compl hu'.1 (h ▸ hv)
  simp only [nextSegment, mem_ofPred_eq, not_and, not_forall, not_lt] at hu'_not
  obtain ⟨w, hw, hle⟩ := hu'_not hu'_ne_v
  have hwu' : w ≠ u' := fun h => hU_compl hu'.1 (h ▸ hw.1)
  have hlt : v.angleDiff w < v.angleDiff u' :=
    lt_of_le_of_ne hle ((circleCoordFrom v).injective.ne hwu')
  exact ⟨w, hw, hu_seg.2 w hw, hlt⟩

theorem prevSegment_dual_properties {V U : Set Circle}
    (hU : IsDualPointSet (univ : Set Circle) V U) {v u : Circle} (hv : v ∈ V)
    (hu : U ∩ prevSegment V v = {u}) :
    u ∈ U ∧ u ≠ v ∧
    (∀ w ∈ V \ {v}, u.angleDiff v < w.angleDiff v) ∧
    (∀ u' ∈ U \ {u}, ∃ w ∈ V \ {v}, u.angleDiff v < w.angleDiff v ∧ w.angleDiff v < u'.angleDiff v)
      := by
  have hu_mem : u ∈ U ∩ prevSegment V v := by rw [hu]; exact mem_singleton u
  have huU : u ∈ U := hu_mem.1
  have hu_seg : u ∈ prevSegment V v := hu_mem.2
  have hU_compl : U ⊆ Vᶜ := fun x hx => ((hU.2 ⟨v, hv⟩).1 hx).2
  refine ⟨huU, hu_seg.1, hu_seg.2, fun u' hu' => ?_⟩
  have hu'_not : u' ∉ prevSegment V v := by
    intro h
    have hmem : u' ∈ U ∩ prevSegment V v := ⟨hu'.1, h⟩
    rw [hu, mem_singleton_iff] at hmem
    exact hu'.2 hmem
  have hu'_ne_v : u' ≠ v := fun h => hU_compl hu'.1 (h ▸ hv)
  simp only [prevSegment, mem_ofPred_eq, not_and, not_forall, not_lt] at hu'_not
  obtain ⟨w, hw, hle⟩ := hu'_not hu'_ne_v
  have hwu' : w ≠ u' := fun h => hU_compl hu'.1 (h ▸ hw.1)
  have hsum_w := Circle.angleDiff_add_angleDiff hw.2
  have hsum_u' := Circle.angleDiff_add_angleDiff hu'_ne_v
  have hvw_ne : v.angleDiff w ≠ v.angleDiff u' := (circleCoordFrom v).injective.ne hwu'
  have hlt : w.angleDiff v < u'.angleDiff v := by grind [-Circle.angleDiff]
  exact ⟨w, hw, hu_seg.2 w hw, hlt⟩

/-- Symmetry of `IsDualPointSet` on `Circle`: if $U$ is a dual point set for $(C, V)$ with $V$
finite, then $V$ is a dual point set for $(C, U)$. -/
theorem isDualPointSet_univ_symm {V U : Set Circle} (hV : V.Finite)
    (hU : IsDualPointSet (univ : Set Circle) V U) :
    IsDualPointSet (univ : Set Circle) U V := by
  have hU_fin : U.Finite := finite_of_isDualPointSet_univ hV hU
  refine ⟨?_, ?_⟩
  · intro hU_emp
    by_contra hV_ne
    obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.mpr hV_ne
    obtain ⟨u, hu⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hV hU hv
    rw [hU_emp, empty_inter] at hu
    exact singleton_ne_empty u hu.symm
  · intro hU_ne
    have hV_ne : V.Nonempty := by
      by_contra hV_emp
      rw [not_nonempty_iff_eq_empty] at hV_emp
      exact hU_ne.ne_empty (hU.1 hV_emp)
    have hU_sub : U ⊆ (univ : Set Circle) \ V := (hU.2 hV_ne).1
    have hV_sub : V ⊆ (univ : Set Circle) \ U := fun v hv => ⟨trivial, fun hu => (hU_sub hu).2 hv⟩
    refine ⟨hV_sub, fun seg hseg => ?_⟩
    rw [mem_segmentsOf_univ_iff hU_fin hU_ne] at hseg
    obtain ⟨u, hu, rfl⟩ := hseg
    obtain ⟨v₀, ⟨hv₀, huv₀⟩, _⟩ := exists_unique_nextSegment_of_mem_compl hV hV_ne (hU_sub hu).2
    obtain ⟨u₀, hu₀_eq⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hV hU hv₀
    have hu₀ : u = u₀ := by
      have hmem : u ∈ U ∩ nextSegment V v₀ := ⟨hu, huv₀⟩
      rwa [hu₀_eq, mem_singleton_iff] at hmem
    rw [← hu₀] at hu₀_eq
    obtain ⟨_, huv₀_ne, hvw, hu'w⟩ := nextSegment_dual_properties hU hv₀ hu₀_eq
    obtain ⟨v_next, hv_next, hmin⟩ := exists_min_on_finite hV hV_ne (Circle.angleDiff u)
    have hv_next_in : v_next ∈ V ∩ nextSegment U u := by
      refine ⟨hv_next, fun h => (hV_sub hv_next).2 (h ▸ hu), fun u' hu' => ?_⟩
      obtain ⟨w, hw, hlt1, hlt2⟩ := hu'w u' hu'
      have hmin_w : u.angleDiff v_next ≤ u.angleDiff w := hmin w hw.1
      have hv₀u_pos := Circle.angleDiff_pos huv₀_ne.symm
      have heq_w := angleDiff_eq_of_angleDiff (x := v₀) (a := u) (b := w)
      have heq_u' := angleDiff_eq_of_angleDiff (x := v₀) (a := u) (b := u')
      grind [-Circle.angleDiff]
    rw [ncard_eq_one]
    refine ⟨v_next, Subset.antisymm ?_ (singleton_subset_iff.mpr hv_next_in)⟩
    rintro v'' ⟨hv'', hv''_seg⟩
    rw [mem_singleton_iff]
    by_contra hne''
    have hmin'' : u.angleDiff v_next ≤ u.angleDiff v'' := hmin v'' hv''
    have hlt'' : u.angleDiff v_next < u.angleDiff v'' :=
      lt_of_le_of_ne hmin'' ((circleCoordFrom u).injective.ne (Ne.symm hne''))
    obtain ⟨u'', hu''_eq⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hV hU hv_next
    obtain ⟨hu''U, hu''_ne, hvw'', _⟩ := nextSegment_dual_properties hU hv_next hu''_eq
    have hlt_v'' : v_next.angleDiff u'' < v_next.angleDiff v'' := hvw'' v'' ⟨hv'', hne''⟩
    have huv_pos := Circle.angleDiff_pos (Ne.symm hv_next_in.2.1)
    have hvp_u''_pos := Circle.angleDiff_pos hu''_ne.symm
    have huv''_lt := Circle.angleDiff_lt_two_pi u v''
    have heq_v'' := angleDiff_eq_of_angleDiff (x := u) (a := v_next) (b := v'')
    have heq_u'' := angleDiff_eq_of_angleDiff (x := u) (a := v_next) (b := u'')
    have hu''_ne_u : u'' ≠ u := by
      rintro rfl
      have h0 : u''.angleDiff u'' = 0 := circleCoordFrom_self u''
      split_ifs at heq_v'' heq_u'' <;> linarith
    have hu''_lt_v'' : u.angleDiff u'' < u.angleDiff v'' := by
      split_ifs at heq_v'' heq_u'' <;> linarith
    have hcontra := hv''_seg.2 u'' ⟨hu''U, hu''_ne_u⟩
    linarith

theorem isOArc_univ_circle : IsOArc (univ : Set Circle) :=
  ⟨(Homeomorph.Set.univ Circle).symm⟩

theorem isSegmentOf_oArcMap_iff {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    {V seg : Set Circle} :
    IsSegmentOf C (oArcMap φ '' V) (oArcMap φ '' seg) ↔
      IsSegmentOf (univ : Set Circle) V seg := by
  have hinj := injective_oArcMap φ
  have hemb := isEmbedding_oArcMap φ
  simp only [IsSegmentOf, componentsIn, diff_image_oArcMap, ← compl_eq_univ_sdiff]
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, heq⟩
      dsimp only at heq
      rw [← isEmbedding_image_connectedComponentIn hemb hz, image_eq_image hinj] at heq
      exact ⟨z, hz, heq⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨oArcMap φ z, mem_image_of_mem _ hz,
        (isEmbedding_image_connectedComponentIn hemb hz).symm⟩
  · constructor
    · rintro ⟨e⟩
      exact ⟨e.trans (hemb.homeomorphImage seg).symm⟩
    · rintro ⟨e⟩
      exact ⟨e.trans (hemb.homeomorphImage seg)⟩

theorem segmentsOf_oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    (V : Set Circle) :
    segmentsOf C (oArcMap φ '' V) = (image (oArcMap φ)) '' segmentsOf (univ : Set Circle) V := by
  ext s
  simp only [segmentsOf, mem_ofPred_eq, mem_image]
  constructor
  · intro hs
    obtain ⟨x, hx, rfl⟩ := hs.1
    have hxC : x ∈ C := hx.1
    have hsub : connectedComponentIn (C \ (oArcMap φ '' V)) x ⊆ range (oArcMap φ) := by
      rw [range_oArcMap]
      exact (connectedComponentIn_subset _ _).trans sdiff_subset
    have heq := image_preimage_eq_of_subset hsub
    refine ⟨oArcMap φ ⁻¹' connectedComponentIn (C \ (oArcMap φ '' V)) x, ?_, heq⟩
    rwa [← isSegmentOf_oArcMap_iff φ, heq]
  · rintro ⟨seg, hseg, rfl⟩
    exact (isSegmentOf_oArcMap_iff φ).mpr hseg

theorem isDualPointSet_oArcMap_iff {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    {V U : Set Circle} :
    IsDualPointSet C (oArcMap φ '' V) (oArcMap φ '' U) ↔
      IsDualPointSet (univ : Set Circle) V U := by
  have hinj := injective_oArcMap φ
  simp only [IsDualPointSet, image_eq_empty, image_nonempty, diff_image_oArcMap,
    ← compl_eq_univ_sdiff, image_subset_image_iff hinj, segmentsOf_oArcMap]
  refine and_congr Iff.rfl (imp_congr_right fun _ => and_congr_right fun _ => ?_)
  constructor
  · intro h seg hseg
    have h1 := h (oArcMap φ '' seg) (mem_image_of_mem _ hseg)
    rwa [← image_inter hinj, ncard_image_of_injective _ hinj] at h1
  · rintro h _ ⟨seg, hseg, rfl⟩
    rw [← image_inter hinj, ncard_image_of_injective _ hinj]
    exact h seg hseg

theorem dualEquivRel_oArcMap_iff {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    {Δ : Set (Set Circle)} {u u' : Circle} :
    dualEquivRel C ((image (oArcMap φ)) '' Δ) (oArcMap φ u) (oArcMap φ u') ↔
      dualEquivRel (univ : Set Circle) Δ u u' := by
  simp only [dualEquivRel, mem_image, exists_exists_and_eq_and, crossesOn_oArcMap_iff]

theorem dualDivision_oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    (U : Set Circle) (Δ : Set (Set Circle)) :
    dualDivision C (oArcMap φ '' U) ((image (oArcMap φ)) '' Δ) =
      (image (oArcMap φ)) '' dualDivision (univ : Set Circle) U Δ := by
  rw [dualDivision, dualDivision, image_image, image_image]
  congr 1
  ext u x
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hrel⟩
    exact ⟨z, ⟨hz, (dualEquivRel_oArcMap_iff φ).mp hrel⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hrel⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (dualEquivRel_oArcMap_iff φ).mpr hrel⟩

theorem divisionUnion_oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    (Δ : Set (Set Circle)) :
    divisionUnion ((image (oArcMap φ)) '' Δ) = oArcMap φ '' divisionUnion Δ := by
  ext x
  simp only [divisionUnion, mem_sUnion, mem_image, exists_exists_and_eq_and]
  tauto

theorem doubleDualDivision_oArcMap {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    (U : Set Circle) (Δ : Set (Set Circle)) :
    doubleDualDivision C (oArcMap φ '' U) ((image (oArcMap φ)) '' Δ) =
      (image (oArcMap φ)) '' doubleDualDivision (univ : Set Circle) U Δ := by
  simp only [doubleDualDivision, divisionUnion_oArcMap, dualDivision_oArcMap]

theorem isCrossFree_oArcMap_iff {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    {Δ : Set (Set Circle)} :
    IsCrossFree C ((image (oArcMap φ)) '' Δ) ↔ IsCrossFree (univ : Set Circle) Δ := by
  have hinj := injective_oArcMap φ
  simp only [IsCrossFree, mem_image, exists_exists_and_eq_and, ne_eq, image_eq_image hinj,
    crossesOn_oArcMap_iff]

theorem isDivision_oArcMap_iff {S : Type u} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C)
    {Δ : Set (Set Circle)} :
    IsDivision ((image (oArcMap φ)) '' Δ) ↔ IsDivision Δ := by
  have hinj := injective_oArcMap φ
  constructor
  · rintro ⟨hfin, hne_fin, hdisj⟩
    refine ⟨hfin.of_finite_image (image_injective.mpr hinj).injOn, ?_, ?_⟩
    · intro δ hδ
      exact (hne_fin _ (mem_image_of_mem _ hδ)).of_image
    · intro δ₁ hδ₁ δ₂ hδ₂ hne
      have h := hdisj (mem_image_of_mem _ hδ₁) (mem_image_of_mem _ hδ₂)
        (fun heq => hne ((image_eq_image hinj).mp heq))
      exact (disjoint_image_iff hinj).mp h
  · rintro ⟨hfin, hne_fin, hdisj⟩
    refine ⟨hfin.image _, ?_, ?_⟩
    · rintro _ ⟨δ, hδ, rfl⟩
      exact (hne_fin δ hδ).image _
    · rintro _ ⟨δ₁, hδ₁, rfl⟩ _ ⟨δ₂, hδ₂, rfl⟩ hne
      have h := hdisj hδ₁ hδ₂ (fun heq => hne (congrArg _ heq))
      exact (disjoint_image_iff hinj).mpr h

theorem divisionUnion_dualDivision {S : Type u} [TopologicalSpace S] (C U : Set S)
    (Δ : Set (Set S)) : divisionUnion (dualDivision C U Δ) = U := by
  ext x
  simp only [divisionUnion, dualDivision, mem_sUnion, mem_image, exists_exists_and_eq_and,
    mem_ofPred_eq]
  exact ⟨fun ⟨_, _, hx, _⟩ => hx, fun hx => ⟨x, hx, hx, dualEquivRel_refl C Δ x⟩⟩

theorem isDivision_dualDivision_univ {U : Set Circle} {Δ : Set (Set Circle)}
    (hV_fin : (divisionUnion Δ).Finite)
    (hU : IsDualPointSet (univ : Set Circle) (divisionUnion Δ) U) :
    IsDivision (dualDivision (univ : Set Circle) U Δ) := by
  have hU_fin : U.Finite := finite_of_isDualPointSet_univ hV_fin hU
  have hU_sub : U ⊆ (univ : Set Circle) \ divisionUnion Δ := isDualPointSet_subset_diff hU
  refine ⟨hU_fin.image _, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hu, dualEquivRel_refl _ _ u⟩
  · intro δ₁ hδ₁ δ₂ hδ₂ hne
    change Disjoint δ₁ δ₂
    rw [disjoint_left]
    intro u hu₁ hu₂
    have h1 := dualDivision_mem_eq_of_mem isOArc_univ_circle (subset_univ _) hU_sub hδ₁ hu₁
    have h2 := dualDivision_mem_eq_of_mem isOArc_univ_circle (subset_univ _) hU_sub hδ₂ hu₂
    exact hne (h1.trans h2.symm)

/-! ## 4. Proof of (2.2) -/

theorem theorem_2_2_univ (U : Set Circle) (Δ : Set (Set Circle))
    (hΔ : IsDivision Δ) (hV_fin : (divisionUnion Δ).Finite)
    (hU : IsDualPointSet (univ : Set Circle) (divisionUnion Δ) U)
    (hCF : IsCrossFree (univ : Set Circle) Δ) :
    doubleDualDivision (univ : Set Circle) U Δ = Δ := by
  let V := divisionUnion Δ
  have hU_sub : U ⊆ (univ : Set Circle) \ V := isDualPointSet_subset_diff hU
  let Δ_star := dualDivision (univ : Set Circle) U Δ
  have hrel_iff : ∀ v ∈ V, ∀ v' ∈ V,
      dualEquivRel (univ : Set Circle) Δ_star v v' ↔ ∃ δ ∈ Δ, v ∈ δ ∧ v' ∈ δ := by
    intro v hv v' hv'
    constructor
    · intro hrel
      by_contra! hnot_same
      have ⟨δ, hδ, hvδ⟩ := hv
      have hv'_not_δ : v' ∉ δ := hnot_same δ hδ hvδ
      have hδ_fin : δ.Finite := hV_fin.subset (subset_sUnion_of_mem hδ)
      have hδ_ne : δ.Nonempty := ⟨v, hvδ⟩
      obtain ⟨v₁, hv₁δ, hmax₁⟩ := exists_max_on_finite hδ_fin hδ_ne (Circle.angleDiff v')
      obtain ⟨v₂, hv₂δ, hmin₂⟩ := exists_min_on_finite hδ_fin hδ_ne (Circle.angleDiff v')
      have hv₁V : v₁ ∈ V := ⟨δ, hδ, hv₁δ⟩
      have hv₂V : v₂ ∈ V := ⟨δ, hδ, hv₂δ⟩
      have hv'v₁ : v' ≠ v₁ := fun h => hv'_not_δ (h ▸ hv₁δ)
      have hv'v₂ : v' ≠ v₂ := fun h => hv'_not_δ (h ▸ hv₂δ)
      have hv'v : v' ≠ v := fun h => hv'_not_δ (h ▸ hvδ)
      obtain ⟨u₁, hu₁_eq⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hV_fin hU hv₁V
      obtain ⟨hu₁U, hu₁v₁, hvw₁, _⟩ := nextSegment_dual_properties hU hv₁V hu₁_eq
      obtain ⟨u₂, hu₂_eq⟩ := exists_unique_mem_prevSegment_of_isDualPointSet hV_fin hU hv₂V
      obtain ⟨hu₂U, hu₂v₂, hvw₂, _⟩ := prevSegment_dual_properties hU hv₂V hu₂_eq
      have hv₁u₁_lt_v₁v' : v₁.angleDiff u₁ < v₁.angleDiff v' := hvw₁ v' ⟨hv', hv'v₁⟩
      have hu₂v₂_lt_v'v₂ : u₂.angleDiff v₂ < v'.angleDiff v₂ := hvw₂ v' ⟨hv', hv'v₂⟩
      have hv₁u₁_pos := Circle.angleDiff_pos hu₁v₁.symm
      have hv'v₁_pos := Circle.angleDiff_pos hv'v₁
      have hv'v₂_pos := Circle.angleDiff_pos hv'v₂
      have hu₂v₂_pos := Circle.angleDiff_pos hu₂v₂
      have hv'u₁_ne : v' ≠ u₁ := fun h => (hU_sub hu₁U).2 (h ▸ hv')
      have hv'u₂_ne : v' ≠ u₂ := fun h => (hU_sub hu₂U).2 (h ▸ hv')
      have hv'u₁_pos := Circle.angleDiff_pos hv'u₁_ne
      have hv'u₂_pos := Circle.angleDiff_pos hv'u₂_ne
      have hv'u₁_lt_2pi := Circle.angleDiff_lt_two_pi v' u₁
      have hv'u₂_lt_2pi := Circle.angleDiff_lt_two_pi v' u₂
      have hv'v₁_lt_2pi := Circle.angleDiff_lt_two_pi v' v₁
      have hv'v₂_lt_2pi := Circle.angleDiff_lt_two_pi v' v₂
      have hsum_v'v₁ := Circle.angleDiff_add_angleDiff hv'v₁
      have heq_u₁ := angleDiff_eq_of_angleDiff (x := v') (a := v₁) (b := u₁)
      have hv'v₁_lt_u₁ : v'.angleDiff v₁ < v'.angleDiff u₁ := by grind [-Circle.angleDiff]
      have hsum_u₂v₂ := Circle.angleDiff_add_angleDiff hu₂v₂
      have hsum_v'v₂ := Circle.angleDiff_add_angleDiff hv'v₂
      have heq_u₂ := angleDiff_eq_of_angleDiff (x := v') (a := u₂) (b := v₂)
      have hv'u₂_lt_v₂ : v'.angleDiff u₂ < v'.angleDiff v₂ := by grind [-Circle.angleDiff]
      have hv₂_le_v : v'.angleDiff v₂ ≤ v'.angleDiff v := hmin₂ v hvδ
      have hv_le_v₁ : v'.angleDiff v ≤ v'.angleDiff v₁ := hmax₁ v hvδ
      have hno_V_1 : ∀ w ∈ V, v'.angleDiff w ≤ v'.angleDiff u₁ → v'.angleDiff w ≤ v'.angleDiff v₁
        := by
        intro w hw hle
        rcases eq_or_ne w v₁ with rfl | hwv₁
        · exact le_rfl
        · have hlt := hvw₁ w ⟨hw, hwv₁⟩
          have hv'w_lt_2pi := Circle.angleDiff_lt_two_pi v' w
          have hv₁w_pos := Circle.angleDiff_pos hwv₁.symm
          have heq_w := angleDiff_eq_of_angleDiff (x := v') (a := v₁) (b := w)
          grind [-Circle.angleDiff]
      have hno_V_2 : ∀ w ∈ V, v'.angleDiff u₂ ≤ v'.angleDiff w → v'.angleDiff v₂ ≤ v'.angleDiff w
        := by
        intro w hw hle
        rcases eq_or_ne w v₂ with rfl | hwv₂
        · exact le_rfl
        · have hlt := hvw₂ w ⟨hw, hwv₂⟩
          have hv'w_ne : v' ≠ w := by
            rintro rfl
            have : v'.angleDiff v' = 0 := circleCoordFrom_self v'
            linarith
          have hv'w_pos := Circle.angleDiff_pos hv'w_ne
          have hv'w_lt_2pi := Circle.angleDiff_lt_two_pi v' w
          have hwv₂_pos := Circle.angleDiff_pos hwv₂
          have hsum_wv₂ := Circle.angleDiff_add_angleDiff hwv₂
          have heq_w := angleDiff_eq_of_angleDiff (x := v') (a := w) (b := v₂)
          grind [-Circle.angleDiff]
      have hu₁u₂_rel : dualEquivRel (univ : Set Circle) Δ u₁ u₂ := by
        rintro ⟨δ', hδ', w₁, hw₁, w₂, hw₂, hcross⟩
        have hw₁V : w₁ ∈ V := ⟨δ', hδ', hw₁⟩
        have hw₂V : w₂ ∈ V := ⟨δ', hδ', hw₂⟩
        have hcross' := hcross.comm isOArc_univ_circle
        rw [crossesOn_univ_iff_circleCoordFrom v'] at hcross'
        rcases hcross' with ⟨hu₁u₂_ne, hw₁w₂_ne, _, _, _, _, hiff⟩
        simp only [onOpenArc, circleCoordFrom] at hiff
        have hw₁_in_iff : (min (v'.angleDiff u₁) (v'.angleDiff u₂) < v'.angleDiff w₁ ∧
            v'.angleDiff w₁ < max (v'.angleDiff u₁) (v'.angleDiff u₂)) ↔
            (v'.angleDiff v₂ ≤ v'.angleDiff w₁ ∧ v'.angleDiff w₁ ≤ v'.angleDiff v₁) := by
          have := hno_V_1 w₁ hw₁V
          have := hno_V_2 w₁ hw₁V
          grind [-Circle.angleDiff]
        have hw₂_in_iff : (min (v'.angleDiff u₁) (v'.angleDiff u₂) < v'.angleDiff w₂ ∧
            v'.angleDiff w₂ < max (v'.angleDiff u₁) (v'.angleDiff u₂)) ↔
            (v'.angleDiff v₂ ≤ v'.angleDiff w₂ ∧ v'.angleDiff w₂ ≤ v'.angleDiff v₁) := by
          have := hno_V_1 w₂ hw₂V
          have := hno_V_2 w₂ hw₂V
          grind [-Circle.angleDiff]
        rw [hw₁_in_iff, hw₂_in_iff] at hiff
        have hδ_ne_δ' : δ ≠ δ' := by
          rintro rfl
          have hw₁_b : v'.angleDiff v₂ ≤ v'.angleDiff w₁ ∧ v'.angleDiff w₁ ≤ v'.angleDiff v₁ :=
            ⟨hmin₂ w₁ hw₁, hmax₁ w₁ hw₁⟩
          have hw₂_b : v'.angleDiff v₂ ≤ v'.angleDiff w₂ ∧ v'.angleDiff w₂ ≤ v'.angleDiff v₁ :=
            ⟨hmin₂ w₂ hw₂, hmax₁ w₂ hw₂⟩
          tauto
        have hdisj : Disjoint δ δ' := hΔ.2.2 hδ hδ' hδ_ne_δ'
        have hw₁_ne_v₁ : w₁ ≠ v₁ := fun h => hdisj.ne_of_mem hv₁δ (h ▸ hw₁) rfl
        have hw₁_ne_v₂ : w₁ ≠ v₂ := fun h => hdisj.ne_of_mem hv₂δ (h ▸ hw₁) rfl
        have hw₂_ne_v₁ : w₂ ≠ v₁ := fun h => hdisj.ne_of_mem hv₁δ (h ▸ hw₂) rfl
        have hw₂_ne_v₂ : w₂ ≠ v₂ := fun h => hdisj.ne_of_mem hv₂δ (h ▸ hw₂) rfl
        have hw₁_ne_v₁_ang : v'.angleDiff w₁ ≠ v'.angleDiff v₁ :=
          (circleCoordFrom v').injective.ne hw₁_ne_v₁
        have hw₁_ne_v₂_ang : v'.angleDiff w₁ ≠ v'.angleDiff v₂ :=
          (circleCoordFrom v').injective.ne hw₁_ne_v₂
        have hw₂_ne_v₁_ang : v'.angleDiff w₂ ≠ v'.angleDiff v₁ :=
          (circleCoordFrom v').injective.ne hw₂_ne_v₁
        have hw₂_ne_v₂_ang : v'.angleDiff w₂ ≠ v'.angleDiff v₂ :=
          (circleCoordFrom v').injective.ne hw₂_ne_v₂
        have hv₁_ne_v₂ : v₁ ≠ v₂ := by
          intro h
          subst h
          grind [-Circle.angleDiff]
        have hv_cross : CrossesOn (univ : Set Circle) v₁ v₂ w₁ w₂ := by
          rw [crossesOn_univ_iff_circleCoordFrom v']
          refine ⟨hv₁_ne_v₂, hw₁w₂_ne, hw₁_ne_v₁.symm, hw₂_ne_v₁.symm,
            hw₁_ne_v₂.symm, hw₂_ne_v₂.symm, ?_⟩
          simp only [onOpenArc, circleCoordFrom]
          grind [-Circle.angleDiff]
        exact hCF ⟨δ, hδ, δ', hδ', hδ_ne_δ', v₁, hv₁δ, v₂, hv₂δ, w₁, hw₁, w₂, hw₂, hv_cross⟩
      let δ_star := {u' ∈ U | dualEquivRel (univ : Set Circle) Δ u₁ u'}
      have hδ_star_mem : δ_star ∈ Δ_star := ⟨u₁, hu₁U, rfl⟩
      have hu₁_in : u₁ ∈ δ_star := ⟨hu₁U, dualEquivRel_refl _ _ u₁⟩
      have hu₂_in : u₂ ∈ δ_star := ⟨hu₂U, hu₁u₂_rel⟩
      have hu_cross : CrossesOn (univ : Set Circle) u₁ u₂ v v' := by
        rw [crossesOn_univ_iff_circleCoordFrom v']
        have hu₁u₂_ne : u₁ ≠ u₂ := fun h => by
          have : v'.angleDiff u₁ = v'.angleDiff u₂ := congrArg (Circle.angleDiff v') h
          linarith
        have hu₁v_ne : u₁ ≠ v := fun h => (hU_sub hu₁U).2 (h ▸ hv)
        have hu₂v_ne : u₂ ≠ v := fun h => (hU_sub hu₂U).2 (h ▸ hv)
        refine ⟨hu₁u₂_ne, hv'v.symm, hu₁v_ne, hv'u₁_ne.symm, hu₂v_ne, hv'u₂_ne.symm, ?_⟩
        simp only [onOpenArc, circleCoordFrom]
        have hv'0 : v'.angleDiff v' = 0 := circleCoordFrom_self v'
        grind [-Circle.angleDiff]
      exact hrel ⟨δ_star, hδ_star_mem, u₁, hu₁_in, u₂, hu₂_in, hu_cross⟩
    · rintro ⟨δ, hδ, hvδ, hv'δ⟩ ⟨δ_star, hδ_star, u₁, hu₁, u₂, hu₂, hcross⟩
      have hδ_star_eq := dualDivision_mem_eq_of_mem isOArc_univ_circle
        (subset_univ _) hU_sub hδ_star hu₁
      rw [hδ_star_eq] at hu₂
      exact hu₂.2 ⟨δ, hδ, v, hvδ, v', hv'δ, hcross.comm isOArc_univ_circle⟩
  ext s
  simp only [doubleDualDivision, dualDivision, mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨δ, hδ, hvδ⟩ := hv
    convert hδ using 1
    ext v'
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hv', hrel⟩
      obtain ⟨δ', hδ', hvδ', hv'δ'⟩ := (hrel_iff v ⟨δ, hδ, hvδ⟩ v' hv').mp hrel
      have heq : δ = δ' := by
        by_contra hne
        exact (hΔ.2.2 hδ hδ' hne).ne_of_mem hvδ hvδ' rfl
      exact heq ▸ hv'δ'
    · intro hv'δ
      have hv' : v' ∈ V := ⟨δ, hδ, hv'δ⟩
      exact ⟨hv', (hrel_iff v ⟨δ, hδ, hvδ⟩ v' hv').mpr ⟨δ, hδ, hvδ, hv'δ⟩⟩
  · intro hδ
    obtain ⟨v, hvδ⟩ := hΔ.2.1 s hδ
    have hv : v ∈ V := ⟨s, hδ, hvδ⟩
    refine ⟨v, hv, ?_⟩
    ext v'
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hv', hrel⟩
      obtain ⟨δ', hδ', hvδ', hv'δ'⟩ := (hrel_iff v hv v' hv').mp hrel
      have heq : s = δ' := by
        by_contra hne
        exact (hΔ.2.2 hδ hδ' hne).ne_of_mem hvδ hvδ' rfl
      exact heq ▸ hv'δ'
    · intro hv's
      have hv' : v' ∈ V := ⟨s, hδ, hv's⟩
      exact ⟨hv', (hrel_iff v hv v' hv').mpr ⟨s, hδ, hvδ, hv's⟩⟩

/-- **Graph Minors VI, (2.2)** (page 117):
"If $\Delta$ is cross-free then $\Delta^{**} = \Delta$." -/
theorem theorem_2_2_proof : Statement22 := by
  intro S _ C U Δ hC hΔ hV_fin hV_sub hU hCF
  obtain ⟨φ⟩ := hC
  have hinj := injective_oArcMap φ
  have hrange := range_oArcMap φ
  let U₀ := oArcMap φ ⁻¹' U
  let Δ₀ := (preimage (oArcMap φ)) '' Δ
  have hU_eq : oArcMap φ '' U₀ = U :=
    image_preimage_eq_of_subset ((isDualPointSet_subset_diff hU).trans
      (sdiff_subset.trans hrange.symm.subset))
  have hΔ_eq : (image (oArcMap φ)) '' Δ₀ = Δ := by
    ext δ
    simp only [Δ₀, mem_image, exists_exists_and_eq_and]
    constructor
    · rintro ⟨δ', hδ', rfl⟩
      have hsub : δ' ⊆ range (oArcMap φ) := by
        rw [hrange]
        exact (subset_sUnion_of_mem hδ').trans hV_sub
      rwa [image_preimage_eq_of_subset hsub]
    · intro hδ
      have hsub : δ ⊆ range (oArcMap φ) := by
        rw [hrange]
        exact (subset_sUnion_of_mem hδ).trans hV_sub
      exact ⟨δ, hδ, image_preimage_eq_of_subset hsub⟩
  have hΔ₀ : IsDivision Δ₀ := by
    rw [← isDivision_oArcMap_iff φ, hΔ_eq]
    exact hΔ
  have hV₀_fin : (divisionUnion Δ₀).Finite := by
    refine Finite.of_finite_image ?_ hinj.injOn
    rw [← divisionUnion_oArcMap φ, hΔ_eq]
    exact hV_fin
  have hU₀ : IsDualPointSet (univ : Set Circle) (divisionUnion Δ₀) U₀ := by
    rw [← isDualPointSet_oArcMap_iff φ, ← divisionUnion_oArcMap φ, hΔ_eq, hU_eq]
    exact hU
  have hCF₀ : IsCrossFree (univ : Set Circle) Δ₀ := by
    rw [← isCrossFree_oArcMap_iff φ, hΔ_eq]
    exact hCF
  rw [← hU_eq, ← hΔ_eq, doubleDualDivision_oArcMap, theorem_2_2_univ U₀ Δ₀ hΔ₀ hV₀_fin hU₀ hCF₀]

/-! ## 5. Proof of (2.3) -/

/-- For a basepoint $c \in \text{Circle}$ and a subset $\gamma \subseteq W$, the set of points
$w \in W$ lying in the half-open interval $(a, b]$ in the linear order of `c.angleDiff` for some
$a, b \in \gamma$. -/
private def spanSet (c : Circle) (W γ : Set Circle) : Set Circle :=
  {w ∈ W | ∃ a ∈ γ, ∃ b ∈ γ, c.angleDiff a < c.angleDiff w ∧ c.angleDiff w ≤ c.angleDiff b}

private lemma spanSet_subset (c : Circle) (W γ : Set Circle) : spanSet c W γ ⊆ W :=
  fun _ hx => hx.1

private lemma spanSet_strict_mono_of_contained {c a b : Circle} {W γ γ' : Set Circle}
    (hW_fin : W.Finite) (haγ : a ∈ γ) (hbγ : b ∈ γ) (hbW : b ∈ W)
    (hab : c.angleDiff a < c.angleDiff b)
    (hγ'_sub : ∀ z ∈ γ', c.angleDiff a < c.angleDiff z ∧ c.angleDiff z < c.angleDiff b) :
    (spanSet c W γ').ncard < (spanSet c W γ).ncard := by
  refine ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩) (hW_fin.subset (spanSet_subset c W γ))
  · rintro w ⟨hwW, z₁, hz₁, z₂, hz₂, hlt₁, hle₂⟩
    have hz₁_b := (hγ'_sub z₁ hz₁).1
    have hz₂_b := (hγ'_sub z₂ hz₂).2
    exact ⟨hwW, a, haγ, b, hbγ, hz₁_b.trans hlt₁, hle₂.trans hz₂_b.le⟩
  · intro heq
    have hb_in : b ∈ spanSet c W γ := ⟨hbW, a, haγ, b, hbγ, hab, le_rfl⟩
    rw [← heq] at hb_in
    rcases hb_in with ⟨_, z₁, _, z₂, hz₂, _, hle₂⟩
    exact (not_lt_of_ge hle₂) (hγ'_sub z₂ hz₂).2

theorem theorem_2_3_univ (U : Set Circle) (Δ : Set (Set Circle))
    (hΔ : IsDivision Δ) (hV_fin : (divisionUnion Δ).Finite)
    (hU : IsDualPointSet (univ : Set Circle) (divisionUnion Δ) U)
    (hW_ne : (divisionUnion Δ ∪ U).Nonempty) :
    ∃ γ ∈ Δ ∪ dualDivision (univ : Set Circle) U Δ, γ.ncard = 1 := by
  let V := divisionUnion Δ
  let W := V ∪ U
  let Δ_star := dualDivision (univ : Set Circle) U Δ
  have hU_fin : U.Finite := finite_of_isDualPointSet_univ hV_fin hU
  have hW_fin : W.Finite := hV_fin.union hU_fin
  have hU_sub : U ⊆ (univ : Set Circle) \ V := isDualPointSet_subset_diff hU
  have hΔ_star_div : IsDivision Δ_star := isDivision_dualDivision_univ hV_fin hU
  have hV_ne : V.Nonempty := by
    rcases V.eq_empty_or_nonempty with hV_emp | hV_ne
    · have hU_emp : U = ∅ := hU.1 hV_emp
      exfalso
      rcases hW_ne with ⟨x, hxV | hxU⟩
      · exact (hV_emp ▸ hxV : x ∈ (∅ : Set Circle)).elim
      · exact (hU_emp ▸ hxU : x ∈ (∅ : Set Circle)).elim
    · exact hV_ne
  obtain ⟨v₀, hv₀⟩ := hV_ne
  obtain ⟨δ₀, hδ₀, _⟩ := hv₀
  have hAll_fin : (Δ ∪ Δ_star).Finite := hΔ.1.union hΔ_star_div.1
  have hAll_ne : (Δ ∪ Δ_star).Nonempty := ⟨δ₀, Or.inl hδ₀⟩
  obtain ⟨x₀, hx₀⟩ := hW_ne
  obtain ⟨c, hc⟩ := nextSegment_nonempty hW_fin hx₀
  have hcW : c ∉ W := nextSegment_subset_compl hc
  obtain ⟨γ, hγ_in, hγ_min_fin⟩ :=
    hAll_fin.toFinset.exists_min_image (fun γ => (spanSet c W γ).ncard)
      (hAll_fin.toFinset_nonempty.mpr hAll_ne)
  have hγ_mem : γ ∈ Δ ∪ Δ_star := hAll_fin.mem_toFinset.mp hγ_in
  have hγ_min : ∀ γ' ∈ Δ ∪ Δ_star, (spanSet c W γ).ncard ≤ (spanSet c W γ').ncard :=
    fun γ' hγ' => hγ_min_fin γ' (hAll_fin.mem_toFinset.mpr hγ')
  refine ⟨γ, hγ_mem, ?_⟩
  have hγ_ne_fin : γ.Nonempty ∧ γ.Finite ∧ γ ⊆ W := by
    rcases hγ_mem with hγΔ | hγΔ_star
    · have hsub : γ ⊆ W := (subset_sUnion_of_mem hγΔ).trans subset_union_left
      exact ⟨hΔ.2.1 γ hγΔ, hW_fin.subset hsub, hsub⟩
    · have hsub : γ ⊆ divisionUnion Δ_star := subset_sUnion_of_mem hγΔ_star
      rw [divisionUnion_dualDivision] at hsub
      have hsubW : γ ⊆ W := hsub.trans subset_union_right
      exact ⟨hΔ_star_div.2.1 γ hγΔ_star, hW_fin.subset hsubW, hsubW⟩
  obtain ⟨a, haγ, hmin_a⟩ := exists_min_on_finite hγ_ne_fin.2.1 hγ_ne_fin.1 (Circle.angleDiff c)
  obtain ⟨b, hbγ, hmax_b⟩ := exists_max_on_finite hγ_ne_fin.2.1 hγ_ne_fin.1 (Circle.angleDiff c)
  rcases eq_or_ne a b with rfl | hab_ne
  · have hγ_eq : γ = {a} := by
      ext z
      simp only [mem_singleton_iff]
      refine ⟨fun hz => ?_, fun h => h.symm ▸ haγ⟩
      have hle1 := hmin_a z hz
      have hle2 := hmax_b z hz
      exact (circleCoordFrom c).injective (le_antisymm hle2 hle1)
    rw [hγ_eq, ncard_singleton]
  · exfalso
    have hab_lt : c.angleDiff a < c.angleDiff b :=
      lt_of_le_of_ne (hmin_a b hbγ) ((circleCoordFrom c).injective.ne hab_ne)
    have haW : a ∈ W := hγ_ne_fin.2.2 haγ
    have hbW : b ∈ W := hγ_ne_fin.2.2 hbγ
    have hca_ne : c ≠ a := fun h => hcW (h ▸ haW)
    have hcb_ne : c ≠ b := fun h => hcW (h ▸ hbW)
    have hca_pos := Circle.angleDiff_pos hca_ne
    have hcb_lt_2pi := Circle.angleDiff_lt_two_pi c b
    have heq_ab := angleDiff_eq_of_angleDiff (x := c) (a := a) (b := b)
    rcases hγ_mem with hγΔ | hγΔ_star
    · have haV : a ∈ V := ⟨γ, hγΔ, haγ⟩
      have hbV : b ∈ V := ⟨γ, hγΔ, hbγ⟩
      obtain ⟨u, hu_eq⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hV_fin hU haV
      obtain ⟨huU, hua_ne, hvw, _⟩ := nextSegment_dual_properties hU haV hu_eq
      have hau_lt_ab : a.angleDiff u < a.angleDiff b := hvw b ⟨hbV, hab_ne.symm⟩
      have hau_pos := Circle.angleDiff_pos hua_ne.symm
      have huW : u ∈ W := Or.inr huU
      have hcu_ne : c ≠ u := fun h => hcW (h ▸ huW)
      have hcu_pos := Circle.angleDiff_pos hcu_ne
      have hcu_lt_2pi := Circle.angleDiff_lt_two_pi c u
      have heq_au := angleDiff_eq_of_angleDiff (x := c) (a := a) (b := u)
      have hcu_in : c.angleDiff a < c.angleDiff u ∧ c.angleDiff u < c.angleDiff b := by
        grind [-Circle.angleDiff]
      let γ' := {u' ∈ U | dualEquivRel (univ : Set Circle) Δ u u'}
      have hγ'_mem : γ' ∈ Δ ∪ Δ_star := Or.inr ⟨u, huU, rfl⟩
      have hγ'_sub : ∀ u' ∈ γ', c.angleDiff a < c.angleDiff u' ∧ c.angleDiff u' < c.angleDiff b
        := by
        intro u' ⟨hu'U, hrel⟩
        rcases eq_or_ne u' u with rfl | hu'u_ne
        · exact hcu_in
        · by_contra hnot
          have hau_ne : a ≠ u := hua_ne.symm
          have hbu_ne : b ≠ u := fun h => (hU_sub huU).2 (h ▸ hbV)
          have hau'_ne : a ≠ u' := fun h => (hU_sub hu'U).2 (h ▸ haV)
          have hbu'_ne : b ≠ u' := fun h => (hU_sub hu'U).2 (h ▸ hbV)
          have hau'_ang : c.angleDiff a ≠ c.angleDiff u' := (circleCoordFrom c).injective.ne hau'_ne
          have hbu'_ang : c.angleDiff b ≠ c.angleDiff u' := (circleCoordFrom c).injective.ne hbu'_ne
          have hcross : CrossesOn (univ : Set Circle) a b u u' := by
            rw [crossesOn_univ_iff_circleCoordFrom c]
            refine ⟨hab_ne, hu'u_ne.symm, hau_ne, hau'_ne, hbu_ne, hbu'_ne, ?_⟩
            simp only [onOpenArc, circleCoordFrom]
            grind [-Circle.angleDiff]
          exact hrel ⟨γ, hγΔ, a, haγ, b, hbγ, hcross⟩
      have hlt_card := spanSet_strict_mono_of_contained hW_fin haγ hbγ hbW hab_lt hγ'_sub
      exact (not_lt_of_ge (hγ_min γ' hγ'_mem)) hlt_card
    · have hγ_sub_U : γ ⊆ U := by
        have hsub : γ ⊆ divisionUnion Δ_star := subset_sUnion_of_mem hγΔ_star
        rwa [divisionUnion_dualDivision] at hsub
      have haU : a ∈ U := hγ_sub_U haγ
      have hbU : b ∈ U := hγ_sub_U hbγ
      have hU_symm := isDualPointSet_univ_symm hV_fin hU
      obtain ⟨v, hv_eq⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hU_fin hU_symm haU
      obtain ⟨hvV, hva_ne, hvu, _⟩ := nextSegment_dual_properties hU_symm haU hv_eq
      have hav_lt_ab : a.angleDiff v < a.angleDiff b := hvu b ⟨hbU, hab_ne.symm⟩
      have hav_pos := Circle.angleDiff_pos hva_ne.symm
      have hvW : v ∈ W := Or.inl hvV
      have hcv_ne : c ≠ v := fun h => hcW (h ▸ hvW)
      have hcv_pos := Circle.angleDiff_pos hcv_ne
      have hcv_lt_2pi := Circle.angleDiff_lt_two_pi c v
      have heq_av := angleDiff_eq_of_angleDiff (x := c) (a := a) (b := v)
      have hcv_in : c.angleDiff a < c.angleDiff v ∧ c.angleDiff v < c.angleDiff b := by
        grind [-Circle.angleDiff]
      have ⟨γ', hγ'Δ, hvγ'⟩ := hvV
      have hγ'_mem : γ' ∈ Δ ∪ Δ_star := Or.inl hγ'Δ
      have hγ_eq := dualDivision_mem_eq_of_mem isOArc_univ_circle (subset_univ _) hU_sub hγΔ_star
        haγ
      have hab_rel : dualEquivRel (univ : Set Circle) Δ a b := by
        rw [hγ_eq] at hbγ
        exact hbγ.2
      have hγ'_sub : ∀ v' ∈ γ', c.angleDiff a < c.angleDiff v' ∧ c.angleDiff v' < c.angleDiff b
        := by
        intro v' hv'γ'
        have hv'V : v' ∈ V := ⟨γ', hγ'Δ, hv'γ'⟩
        rcases eq_or_ne v' v with rfl | hv'v_ne
        · exact hcv_in
        · by_contra hnot
          have hav_ne : a ≠ v := hva_ne.symm
          have hbv_ne : b ≠ v := fun h => (hU_sub hbU).2 (h ▸ hvV)
          have hav'_ne : a ≠ v' := fun h => (hU_sub haU).2 (h ▸ hv'V)
          have hbv'_ne : b ≠ v' := fun h => (hU_sub hbU).2 (h ▸ hv'V)
          have hav'_ang : c.angleDiff a ≠ c.angleDiff v' := (circleCoordFrom c).injective.ne hav'_ne
          have hbv'_ang : c.angleDiff b ≠ c.angleDiff v' := (circleCoordFrom c).injective.ne hbv'_ne
          have hcross : CrossesOn (univ : Set Circle) a b v v' := by
            rw [crossesOn_univ_iff_circleCoordFrom c]
            refine ⟨hab_ne, hv'v_ne.symm, hav_ne, hav'_ne, hbv_ne, hbv'_ne, ?_⟩
            simp only [onOpenArc, circleCoordFrom]
            grind [-Circle.angleDiff]
          exact hab_rel ⟨γ', hγ'Δ, v, hvγ', v', hv'γ', hcross.comm isOArc_univ_circle⟩
      have hlt_card := spanSet_strict_mono_of_contained hW_fin haγ hbγ hbW hab_lt hγ'_sub
      exact (not_lt_of_ge (hγ_min γ' hγ'_mem)) hlt_card

/-- **Graph Minors VI, (2.3)** (page 118):
"If $W \ne \emptyset$, one of $\Delta, \Delta^*$ has a member with cardinality $1$." -/
theorem theorem_2_3_proof : Statement23 := by
  intro S _ C U Δ hC hΔ hV_fin hV_sub hU hW_ne
  obtain ⟨φ⟩ := hC
  have hinj := injective_oArcMap φ
  have hrange := range_oArcMap φ
  let U₀ := oArcMap φ ⁻¹' U
  let Δ₀ := (preimage (oArcMap φ)) '' Δ
  have hU_eq : oArcMap φ '' U₀ = U :=
    image_preimage_eq_of_subset ((isDualPointSet_subset_diff hU).trans
      (sdiff_subset.trans hrange.symm.subset))
  have hΔ_eq : (image (oArcMap φ)) '' Δ₀ = Δ := by
    ext δ
    simp only [Δ₀, mem_image, exists_exists_and_eq_and]
    constructor
    · rintro ⟨δ', hδ', rfl⟩
      have hsub : δ' ⊆ range (oArcMap φ) := by
        rw [hrange]
        exact (subset_sUnion_of_mem hδ').trans hV_sub
      rwa [image_preimage_eq_of_subset hsub]
    · intro hδ
      have hsub : δ ⊆ range (oArcMap φ) := by
        rw [hrange]
        exact (subset_sUnion_of_mem hδ).trans hV_sub
      exact ⟨δ, hδ, image_preimage_eq_of_subset hsub⟩
  have hΔ₀ : IsDivision Δ₀ := by
    rw [← isDivision_oArcMap_iff φ, hΔ_eq]
    exact hΔ
  have hV₀_fin : (divisionUnion Δ₀).Finite := by
    refine Finite.of_finite_image ?_ hinj.injOn
    rw [← divisionUnion_oArcMap φ, hΔ_eq]
    exact hV_fin
  have hU₀ : IsDualPointSet (univ : Set Circle) (divisionUnion Δ₀) U₀ := by
    rw [← isDualPointSet_oArcMap_iff φ, ← divisionUnion_oArcMap φ, hΔ_eq, hU_eq]
    exact hU
  have hW₀_ne : (divisionUnion Δ₀ ∪ U₀).Nonempty := by
    have heq : oArcMap φ '' (divisionUnion Δ₀ ∪ U₀) = divisionUnion Δ ∪ U := by
      rw [image_union, ← divisionUnion_oArcMap φ, hΔ_eq, hU_eq]
    exact (heq ▸ hW_ne).of_image
  obtain ⟨γ₀, hγ₀_mem, hγ₀_card⟩ := theorem_2_3_univ U₀ Δ₀ hΔ₀ hV₀_fin hU₀ hW₀_ne
  refine ⟨oArcMap φ '' γ₀, ?_, ?_⟩
  · rw [← hΔ_eq, ← hU_eq, dualDivision_oArcMap, ← image_union]
    exact mem_image_of_mem _ hγ₀_mem
  · rw [ncard_image_of_injective _ hinj]
    exact hγ₀_card

end GraphMinor.GM06
