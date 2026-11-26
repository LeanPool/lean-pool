/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section75Case2Atoms
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM12.Section74Bridge

/-!
# The end of Case 2 of XII (7.5)

The paragraph of pages 265 and 266 that claims that `Γ'`, `𝒯'`, `r'` satisfy the theorem. The
theorem takes what
the chain of Case 2 gives, and proves (ii), (iii) and (iv) of (7.5). Condition (i) is in the
conclusion
of `theorem_7_5_apply_7_4`, by `U_subset_of_deleteVertices_U_subset`.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- In Case 2 of **(7.5)** (Graph Minors XII, pages 265 and 266): `Γ'`, `𝒯'`, `r'` satisfy the
theorem. Write `Γ₂ = Γ₁ \ v`, where `v = r*` and `r₂` is the region of `Γ₂` containing `v`. From
the duals `Γ₁` and `Γ₃`, the equations `d₁(a*, b*) = d(a, b)` and `d₃(a*, b*) = d₂(a, b)` in the
form of
`exists_dual_tangleMetric_of_common_radial`, the bounds (v), (vi) of (7.3) and the conclusion of
`theorem_7_5_apply_7_4`, this proves (ii), (iii), (iv) of (7.5). -/
theorem theorem_7_5_case_2_end (hS : IsClosedSurface S)
    {Γ Γ₁ K J Γ₃ Γ' : Drawing S} {f : C(S, S)} {θ : ℕ}
    {T T₁ T₂ T₃ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d₁ d₂ d₃ d' : Set S → Set S → ℕ} {ins ins₂ : Drawing S → Set S}
    {r r₂ r' : Set S} {v : S} (hθ : 3 ≤ θ)
    (hT : IsRespectfulDrawingTangle Γ θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hd : ∀ x ∈ Γ.A, ∀ y ∈ Γ.A, d x y = tangleMetric Γ K ins θ x y)
    (hr : r ∈ Γ.R) (hvr : v ∈ r) (hvK : v ∈ K.V)
    (hK₁ : (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K) (hdual : IsLineDual Γ K Γ₁)
    (hM₁ : HasTangleMetric Γ₁ θ T₁ d₁)
    (hd₁ : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a_star ∈ Γ₁.A, ∀ b_star ∈ Γ₁.A,
      (a = b ↔ a_star = b_star) →
      (∀ x' : Set S, IsCorrespondingAtom Γ K a x' ↔ IsCorrespondingAtom Γ₁ K a_star x') →
      (∀ y' : Set S, IsCorrespondingAtom Γ K b y' ↔ IsCorrespondingAtom Γ₁ K b_star y') →
      d₁ a_star b_star = tangleMetric Γ K ins θ a b)
    (hM₂ : HasTangleMetric (deleteVertices Γ₁ {v}) (θ - 1) T₂ d₂)
    (hr₂ : r₂ ∈ (deleteVertices Γ₁ {v}).R) (hvr₂ : v ∈ r₂)
    (h_v : ∀ a ∈ Γ₁.A ∩ (deleteVertices Γ₁ {v}).A,
      ∀ b ∈ Γ₁.A ∩ (deleteVertices Γ₁ {v}).A, d₁ a b - 2 ≤ d₂ a b)
    (h_vi : ∀ a ∈ Γ₁.A ∩ (deleteVertices Γ₁ {v}).A, d₁ a {v} - 1 ≤ d₂ a r₂)
    (hJ : (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).IsRadialDrawing J)
    (hd₂ : ∀ x ∈ (deleteVertices Γ₁ {v}).A, ∀ y ∈ (deleteVertices Γ₁ {v}).A,
      d₂ x y = tangleMetric (deleteVertices Γ₁ {v}) J ins₂ (θ - 1) x y)
    (hc : IsContractedDual Γ Γ₁ K J f r v Γ₃)
    (hM₃ : HasTangleMetric Γ₃ (θ - 1) T₃ d₃)
    (hd₃ : ∀ a ∈ (deleteVertices Γ₁ {v}).A, ∀ b ∈ (deleteVertices Γ₁ {v}).A,
      ∀ a_star ∈ Γ₃.A, ∀ b_star ∈ Γ₃.A,
      (a = b ↔ a_star = b_star) →
      (∀ x' : Set S, IsCorrespondingAtom (deleteVertices Γ₁ {v}) J a x' ↔
        IsCorrespondingAtom Γ₃ J a_star x') →
      (∀ y' : Set S, IsCorrespondingAtom (deleteVertices Γ₁ {v}) J b y' ↔
        IsCorrespondingAtom Γ₃ J b_star y') →
      d₃ a_star b_star = tangleMetric (deleteVertices Γ₁ {v}) J ins₂ (θ - 1) a b)
    (hSub' : Γ'.IsSubdrawing (deleteVertices Γ {u ∈ Γ.V | u ∈ closure r}))
    (hr' : r' ∈ Γ'.R) (hrr' : r ⊆ r') (hU : Γ.U ⊆ Γ'.U ∪ r')
    (h_viii : ∀ a ∈ Γ₃.A ∩ Γ'.A, ∀ b ∈ Γ₃.A ∩ Γ'.A, d₃ a b - 2 ≤ d' a b)
    (h_ix : ∀ a ∈ Γ₃.A ∩ Γ'.A, d₃ a {v} - 1 ≤ d' a r')
    (h_x : ∀ a ∈ Γ₃.A, a ⊆ r' → d₃ a {v} ≤ 2) :
    (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 ≤ d' a r') ∧
      (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 3) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hV₁, _⟩ := hdual
  obtain ⟨-, h₀, -, hsym₁, -, hreg₁, hedge₁⟩ := GM11.gm15_theorem_9_1 Γ₁ θ T₁ d₁ hS inferInstance
    hM₁
  have hE : Γ.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hT.2.1 (by omega)
  have hE₂ : (deleteVertices Γ₁ {v}).E.Nonempty :=
    edgeSet_nonempty_of_isTangle_of_two_le hM₂.1.2.1 (by omega)
  have hE₁ : Γ₁.E.Nonempty := hE₂.mono (deleteVertices_isSubdrawing Γ₁ {v}).2
  have hE₃ : Γ₃.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hM₃.1.2.1 (by omega)
  have hvV₃ : v ∈ Γ₃.V := by
    rw [hc.V_eq]
    exact Or.inr rfl
  have hv₁ : v ∈ Γ₁.V := by
    rw [hV₁]
    exact ⟨hvK, fun h' => region_subset hr hvr (Γ.V_subset_U h')⟩
  have hvJ : v ∈ J.V := hc.radial.2.1.2.1 hvV₃
  have hvr' : v ∈ r' := hrr' hvr
  have hZ : {u ∈ Γ.V | u ∈ closure r} = Γ.V ∩ (closure r \ r) := by
    ext u
    exact ⟨fun h' => ⟨h'.1, h'.2, fun h'' => region_subset hr h'' (Γ.V_subset_U h'.1)⟩,
      fun h' => ⟨h'.1, h'.2.1⟩⟩
  have hSub₃ : Γ'.IsSubdrawing (deleteVertices Γ₃ {v}) := by
    rw [hc.delete_eq, ← hZ]
    exact hSub'
  have hSub₃' : Γ'.IsSubdrawing Γ₃ := hSub₃.trans (deleteVertices_isSubdrawing Γ₃ {v})
  have hU₃ : Γ₃.U ⊆ Γ'.U ∪ r' := by
    refine U_subset_of_delete_U_subset hr' hSub₃ hvV₃ hvr' (Subset.trans ?_ hU)
    rw [hc.delete_eq]
    exact (deleteVertices_isSubdrawing Γ _).U_subset
  have hrs : SameAtom Γ Γ₁ K r {v} := sameAtom_region hK hK₁ hv₁ hr hvK hvr
  have hrs₂ : SameAtom (deleteVertices Γ₁ {v}) Γ₃ J r₂ {v} :=
    ⟨{v}, corr_region hr₂ hvJ hvr₂, corr_vertex hc.radial hvV₃⟩
  have hd_eq : ∀ {a b a₁ b₁ : Set S}, a ∈ Γ.A → b ∈ Γ.A → SameAtom Γ Γ₁ K a a₁ →
      SameAtom Γ Γ₁ K b b₁ → d a b = d₁ a₁ b₁ := fun {a b _ _} ha hb h₁ h₂ => by
    rw [hd a ha b hb]
    exact (dual_metric_eq hS hK hK₁ hE hE₁ hd₁ h₁ h₂).symm
  have hd₃_eq : ∀ {a b a₃ b₃ : Set S}, a ∈ (deleteVertices Γ₁ {v}).A →
      b ∈ (deleteVertices Γ₁ {v}).A → SameAtom (deleteVertices Γ₁ {v}) Γ₃ J a a₃ →
      SameAtom (deleteVertices Γ₁ {v}) Γ₃ J b b₃ → d₂ a b = d₃ a₃ b₃ := fun {a b _ _} ha hb h₁ h₂
        => by
    rw [hd₂ a ha b hb]
    exact (dual_metric_eq hS hJ hc.radial hE₂ hE₃ hd₃ h₁ h₂).symm
  have hdis : ∀ a ∈ Γ.A ∩ Γ'.A, Disjoint a r' := fun a ha =>
    (theorem_7_5_disjoint_region_of_shared_atom hS (by omega) hT hr hr' hSub' hrr' ha).1
  have hSubΓ : Γ'.IsSubdrawing Γ := (isSubdrawing_deleteVertices_iff.mp hSub').1
  have hshared : ∀ a ∈ Γ.A ∩ Γ'.A, ∃ a₁, a₁ ∈ Γ₁.A ∧ a₁ ∈ (deleteVertices Γ₁ {v}).A ∧
      SameAtom Γ Γ₁ K a a₁ ∧ a ∈ Γ₃.A ∧ SameAtom (deleteVertices Γ₁ {v}) Γ₃ J a₁ a := by
    rintro a ⟨ha, ha'⟩
    have har' := hdis a ⟨ha, ha'⟩
    rcases ha' with (⟨u, hu', rfl⟩ | he') | hR'
    · have hu : u ∈ Γ.V := hSubΓ.1 hu'
      have hur : u ∉ closure r := fun h' =>
        disjoint_left.mp (isSubdrawing_deleteVertices_iff.mp hSub').2 hu' ⟨hu, h'⟩
      obtain ⟨t, ht, ht₂, hs, hu₃, hs₂⟩ := thread_vertex hc hK hK₁ hV₁ hu hur
      exact ⟨t, Or.inr ht, Or.inr ht₂, hs, Or.inl (Or.inl ⟨u, hu₃, rfl⟩), hs₂⟩
    · have he : a ∈ Γ.E := hSubΓ.2 he'
      have hd' := hSub'.2 he'
      rw [deleteVertices_E] at hd'
      have hdj : Disjoint (closure a ∩ Γ.V) (closure r \ r) :=
        disjoint_left.mpr fun u h₁ h₂ => disjoint_left.mp hd'.2 h₁ ⟨h₁.2, h₂.1⟩
      obtain ⟨g, hg, hg₂, hs, hfe, hs₂⟩ := thread_edge hc he (hc.not_sub a he hdj)
      rw [hc.fixed a he hdj] at hfe hs₂
      exact ⟨g, Or.inl (Or.inr hg), Or.inl (Or.inr hg₂), hs, Or.inl (Or.inr hfe), hs₂⟩
    · have hoffU : ∀ x ∈ a, x ∉ Γ.U := fun x hxa hxU => by
        rcases hU hxU with h | h
        · exact region_subset hR' hxa h
        · exact disjoint_left.mp har' hxa h
      obtain ⟨x₀, hx₀⟩ := region_nonempty hR'
      rcases ha with (⟨u, hu, rfl⟩ | he) | hR
      · exact absurd (Γ.V_subset_U (mem_singleton_iff.mp hx₀ ▸ hu)) (hoffU x₀ hx₀)
      · exact absurd (he.2.1 hx₀).1 (hoffU x₀ hx₀)
      · have har : a ≠ r := by
          rintro rfl
          exact disjoint_left.mp har' hvr hvr'
        obtain ⟨w, hwa, hw₁, hw₂, hs, t, ht, hwt, hs₂⟩ :=
          thread_region hc hJ hK hK₁ hV₁ hr hvr hR har
        have ha₃ : a ∈ Γ₃.R := region_of_disjoint hSub₃' hU₃ hR' har'
        obtain rfl : t = a := region_eq_of_mem ht ha₃ hwt hwa
        exact ⟨{w}, hw₁, hw₂, hs, Or.inr ha₃, hs₂⟩
  have hbound : ∀ {a a₁ a₃ : Set S}, a ∈ Γ.A → a₁ ∈ Γ₁.A → a₁ ∈ (deleteVertices Γ₁ {v}).A →
      SameAtom Γ Γ₁ K a a₁ → a₃ ∈ Γ₃.A → SameAtom (deleteVertices Γ₁ {v}) Γ₃ J a₁ a₃ → a₃ ⊆ r' →
      d a r ≤ 3 := fun {a a₁ a₃} ha ha₁ ha₂ hs ha₃ hs₂ hsub => by
    have h₁ := hd_eq ha (Or.inr hr) hs hrs
    have h₂ := hd₃_eq ha₂ (Or.inr hr₂) hs₂ hrs₂
    have h₃ := h_vi a₁ ⟨ha₁, ha₂⟩
    have h₄ := h_x a₃ ha₃ hsub
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    by_cases hab : a = b
    · obtain ⟨a₁, ha₁, -, hs, -, -⟩ := hshared a ha
      subst hab
      rw [hd_eq ha.1 ha.1 hs hs, h₀ a₁ ha₁]
      exact Nat.zero_le _
    obtain ⟨a₁, ha₁, ha₂, hs, ha₃, hs₂⟩ := hshared a ha
    obtain ⟨b₁, hb₁, hb₂, ht, hb₃, ht₂⟩ := hshared b hb
    have h₁ := hd_eq ha.1 hb.1 hs ht
    have h₂ := hd₃_eq ha₂ hb₂ hs₂ ht₂
    have h₃ := h_v a₁ ⟨ha₁, ha₂⟩ b₁ ⟨hb₁, hb₂⟩
    have h₄ := h_viii a ⟨ha₃, ha.2⟩ b ⟨hb₃, hb.2⟩
    omega
  · intro a ha
    obtain ⟨a₁, ha₁, ha₂, hs, ha₃, hs₂⟩ := hshared a ha
    have h₁ := hd_eq ha.1 (Or.inr hr) hs hrs
    have h₂ := hd₃_eq ha₂ (Or.inr hr₂) hs₂ hrs₂
    have h₃ := h_vi a₁ ⟨ha₁, ha₂⟩
    have h₄ := h_ix a ⟨ha₃, ha.2⟩
    omega
  · intro a ha har'
    have hrA : r ∈ Γ.A := Or.inr hr
    have hvA : ({v} : Set S) ∈ Γ₁.A := Or.inl (Or.inl ⟨v, hv₁, rfl⟩)
    rcases id ha with (⟨u, hu, rfl⟩ | he) | hR
    · by_cases hur : u ∈ closure r
      · obtain ⟨t, ht, hut, hs⟩ := sameAtom_vertex hK hK₁ hV₁ hu
        have h₁ := hreg₁ hE₁ v hv₁ t ht (hc.vertex_bd u hu hur t ht hut)
        rw [hd_eq ha hrA hs hrs, hsym₁ t (Or.inr ht) {v} hvA]
        omega
      · obtain ⟨t, ht, ht₂, hs, hu₃, hs₂⟩ := thread_vertex hc hK hK₁ hV₁ hu hur
        exact hbound ha (Or.inr ht) (Or.inr ht₂) hs (Or.inl (Or.inl ⟨u, hu₃, rfl⟩)) hs₂ har'
    · by_cases hn : a ⊆ closure r \ r
      · obtain ⟨g, hg, hvg, s, hs, hes, hgs⟩ := hc.edge_bd a he hn
        have hsa : SameAtom Γ Γ₁ K a g := ⟨s, corr_edge he hs hes, corr_edge hg hs hgs⟩
        have h₁ := hedge₁ v hv₁ g hg hvg
        rw [hd_eq ha hrA hsa hrs, hsym₁ g (Or.inl (Or.inr hg)) {v} hvA]
        omega
      · obtain ⟨g, hg, hg₂, hs, hfe, hs₂⟩ := thread_edge hc he hn
        have hsub : f '' a ⊆ r' := by
          by_cases hdj : Disjoint (closure a ∩ Γ.V) (closure r \ r)
          · rw [hc.fixed a he hdj]
            exact har'
          · rw [not_disjoint_iff] at hdj
            obtain ⟨u, ⟨hua, huV⟩, hur⟩ := hdj
            have hfu := hc.collapse u huV hur.1
            have hvc : v ∈ closure (f '' a) :=
              hfu ▸ image_closure_subset_closure_image f.continuous ⟨u, hua, rfl⟩
            exact incident_edge_subset_region_of_vertex_mem hr' hSub₃ hfe hvV₃ rfl hvc
              (singleton_subset_iff.mpr hvr')
        exact hbound ha (Or.inl (Or.inr hg)) (Or.inl (Or.inr hg₂)) hs (Or.inl (Or.inr hfe)) hs₂ hsub
    · by_cases har : a = r
      · subst har
        rw [hd_eq ha ha hrs hrs, h₀ {v} hvA]
        omega
      · obtain ⟨w, hwa, hw₁, hw₂, hs, t, ht, hwt, hs₂⟩ :=
          thread_region hc hJ hK hK₁ hV₁ hr hvr hR har
        have hsub : t ⊆ r' :=
          region_subset_region_of_inter_nonempty hSub₃' ht hr' ⟨w, hwt, har' hwa⟩
        exact hbound ha hw₁ hw₂ hs (Or.inr ht) hs₂ hsub

/-- All of (i) to (iv) of **(7.5)** in Case 2, with `Γ'`, `T'`, `d'`, `r'` from
`theorem_7_5_apply_7_4`. The conclusion is that of `Theorem75Statement`. -/
theorem theorem_7_5_case_2 (hS : IsClosedSurface S)
    {Γ Γ₁ K J Γ₃ : Drawing S} {f : C(S, S)} {θ : ℕ}
    {T T₁ T₂ T₃ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d₁ d₂ d₃ : Set S → Set S → ℕ} {ins ins₂ : Drawing S → Set S}
    {r r₂ : Set S} {v : S} (hθ : 3 ≤ θ)
    (hT : IsRespectfulDrawingTangle Γ θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hd : ∀ x ∈ Γ.A, ∀ y ∈ Γ.A, d x y = tangleMetric Γ K ins θ x y)
    (hr : r ∈ Γ.R) (hvr : v ∈ r) (hvK : v ∈ K.V)
    (hK₁ : (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K) (hdual : IsLineDual Γ K Γ₁)
    (hM₁ : HasTangleMetric Γ₁ θ T₁ d₁)
    (hd₁ : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a_star ∈ Γ₁.A, ∀ b_star ∈ Γ₁.A,
      (a = b ↔ a_star = b_star) →
      (∀ x' : Set S, IsCorrespondingAtom Γ K a x' ↔ IsCorrespondingAtom Γ₁ K a_star x') →
      (∀ y' : Set S, IsCorrespondingAtom Γ K b y' ↔ IsCorrespondingAtom Γ₁ K b_star y') →
      d₁ a_star b_star = tangleMetric Γ K ins θ a b)
    (hM₂ : HasTangleMetric (deleteVertices Γ₁ {v}) (θ - 1) T₂ d₂)
    (hr₂ : r₂ ∈ (deleteVertices Γ₁ {v}).R) (hvr₂ : v ∈ r₂)
    (h_v : ∀ a ∈ Γ₁.A ∩ (deleteVertices Γ₁ {v}).A,
      ∀ b ∈ Γ₁.A ∩ (deleteVertices Γ₁ {v}).A, d₁ a b - 2 ≤ d₂ a b)
    (h_vi : ∀ a ∈ Γ₁.A ∩ (deleteVertices Γ₁ {v}).A, d₁ a {v} - 1 ≤ d₂ a r₂)
    (hJ : (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).IsRadialDrawing J)
    (hd₂ : ∀ x ∈ (deleteVertices Γ₁ {v}).A, ∀ y ∈ (deleteVertices Γ₁ {v}).A,
      d₂ x y = tangleMetric (deleteVertices Γ₁ {v}) J ins₂ (θ - 1) x y)
    (hc : IsContractedDual Γ Γ₁ K J f r v Γ₃)
    (hM₃ : HasTangleMetric Γ₃ (θ - 1) T₃ d₃)
    (hd₃ : ∀ a ∈ (deleteVertices Γ₁ {v}).A, ∀ b ∈ (deleteVertices Γ₁ {v}).A,
      ∀ a_star ∈ Γ₃.A, ∀ b_star ∈ Γ₃.A,
      (a = b ↔ a_star = b_star) →
      (∀ x' : Set S, IsCorrespondingAtom (deleteVertices Γ₁ {v}) J a x' ↔
        IsCorrespondingAtom Γ₃ J a_star x') →
      (∀ y' : Set S, IsCorrespondingAtom (deleteVertices Γ₁ {v}) J b y' ↔
        IsCorrespondingAtom Γ₃ J b_star y') →
      d₃ a_star b_star = tangleMetric (deleteVertices Γ₁ {v}) J ins₂ (θ - 1) a b) :
    ∃ (Γ' : Drawing S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r' : Set S),
      Γ'.IsSubdrawing (deleteVertices Γ {u ∈ Γ.V | u ∈ closure r}) ∧
      (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
      HasTangleMetric Γ' (θ - 2) T' d' ∧
      r' ∈ Γ'.R ∧ r ⊆ r' ∧
      Γ.U ⊆ Γ'.U ∪ r' ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 ≤ d' a r') ∧
      (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 3) := by
  have hvV₃ : v ∈ Γ₃.V := by
    rw [hc.V_eq]
    exact Or.inr rfl
  have hZ : {u ∈ Γ.V | u ∈ closure r} = Γ.V ∩ (closure r \ r) := by
    ext u
    exact ⟨fun h' => ⟨h'.1, h'.2, fun h'' => region_subset hr h'' (Γ.V_subset_U h'.1)⟩,
      fun h' => ⟨h'.1, h'.2.1⟩⟩
  obtain ⟨Γ', T', d', r', hSub', htwo, hM', hr', hrr', hU, h_viii, h_ix, h_x⟩ :=
    theorem_7_5_apply_7_4 hS hθ hr hM₃ hvV₃ hvr (by rw [hc.delete_eq, hZ])
  exact ⟨Γ', T', d', r', hSub', htwo, hM', hr', hrr', hU, theorem_7_5_case_2_end hS hθ hT hK hd hr
    hvr
    hvK hK₁ hdual hM₁ hd₁ hM₂ hr₂ hvr₂ h_v h_vi hJ hd₂ hc hM₃ hd₃ hSub' hr' hrr' hU h_viii h_ix h_x⟩

end GraphMinor.GM12
