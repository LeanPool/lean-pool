/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13zb

/-!
# Graph Minors XIX, Section 13: the division on the boundary of a sector

We cut the bigon at a pair of vertices at the same position. What is left has a part towards `r` and
a part towards `u`, and each part is connected. So points of one part are not separated by the pair.
Then VI (3.6) gives that the division with these pairs as members is feasible in `sk(Γ)` inside the
disc. The chain condition of VI (3.6) comes from the fact that the bigon has no short cut.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM06

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_append_left {G : Drawing Shat} {a b c : Shat}
  (P : GraphWalk G.toGraph a b) (Q : GraphWalk G.toGraph b c) {t : ℕ} (ht : t ≤ P.length) :
    GraphWalk.vertexAt (P.append Q) t = GraphWalk.vertexAt P t := by
  have hl := GraphWalk.length_support' P
  have hl' : t ≤ (P.append Q).length := by rw [GraphWalk.length_append]; omega
  rw [GraphWalk.vertexAt_eq _ hl', GraphWalk.vertexAt_eq P ht (by omega)]
  simp only [GraphWalk.support_append]
  rw [List.getElem_append_left (by omega)]

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_append_right {G : Drawing Shat} {a b c : Shat}
  (P : GraphWalk G.toGraph a b) (Q : GraphWalk G.toGraph b c) {t : ℕ} (ht : t ≤ Q.length) :
    GraphWalk.vertexAt (P.append Q) (P.length + t) = GraphWalk.vertexAt Q t := by
  induction P with
  | nil h => simp [GraphWalk.length, GraphWalk.append]
  | cons hl' s ih =>
    rw [← ih Q ht]
    have e : (GraphWalk.cons hl' s).length + t = (s.length + t) + 1 := by
      simp only [GraphWalk.length, GraphWalk.edges_cons, List.length_cons]
      omega
    rw [e]
    simp [GraphWalk.vertexAt, GraphWalk.append]

/-- The two pieces of a split walk lie in the walk. -/
theorem walkU_left_subset {G : Drawing Shat} {a b c : Shat} (P : GraphWalk G.toGraph a b)
  (Q : GraphWalk G.toGraph b c) : (walkDrawing G P).U ⊆ (walkDrawing G (P.append Q)).U
    := fun y hy ↦ by
  rw [mem_walkDrawing_U] at hy ⊢
  rcases hy with h | ⟨e, he, hye⟩
  · exact .inl ((GraphWalk.mem_support_append P Q).mpr (.inl h))
  · exact .inr ⟨e, by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he, hye⟩

theorem walkU_right_subset {G : Drawing Shat} {a b c : Shat} (P : GraphWalk G.toGraph a b)
  (Q : GraphWalk G.toGraph b c) : (walkDrawing G Q).U ⊆ (walkDrawing G (P.append Q)).U
    := fun y hy ↦ by
  rw [mem_walkDrawing_U] at hy ⊢
  rcases hy with h | ⟨e, he, hye⟩
  · exact .inl ((GraphWalk.mem_support_append P Q).mpr (.inr h))
  · exact .inr ⟨e, by rw [GraphWalk.edges_append]; exact List.mem_append_right _ he, hye⟩

theorem walkU_diff_end {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b)
  (hs : K.IsSimple) (hab : a ≠ b) : IsPreconnected ((walkDrawing G K).U \ {b}) := by
  have h := isLine_of_isPathBetween (walkDrawing_isPathBetween G hs) hab
  refine (IsLineWithEnds.isPreconnected_diff h).subset_closure (fun x hx ↦ ⟨hx.1,
    fun h' ↦ hx.2 (.inr h')⟩) fun x hx ↦ IsLineWithEnds.subset_closure_diff h hx.1

theorem walkU_diff_start {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b)
  (hs : K.IsSimple) (hab : a ≠ b) : IsPreconnected ((walkDrawing G K).U \ {a}) := by
  have h := isLine_of_isPathBetween (walkDrawing_isPathBetween G hs) hab
  refine (IsLineWithEnds.isPreconnected_diff h).subset_closure (fun x hx ↦ ⟨hx.1,
    fun h' ↦ hx.2 (.inl h')⟩) fun x hx ↦ IsLineWithEnds.subset_closure_diff h hx.1

namespace TangleDatum

variable {D : TangleDatum cap χ} {r u : Shat} {B : Bool → GraphWalk D.rad.G.toGraph r u}

omit [T2Space S] in
/-- Cutting the bigon at position `p`, with `p ≥ 1`, leaves a connected part towards `r` and a
connected part towards `u`, and every placed point other than at `p` is in the right part. -/
theorem IsBigon.exists_parts (hB : D.IsBigon B) {p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ (B false).length) :
    ∃ X Y : Set Shat, IsPreconnected X ∧ IsPreconnected Y ∧ (∀ i, GraphWalk.vertexAt (B i) p ∉ X
      ∧ GraphWalk.vertexAt (B i) p ∉ Y) ∧ (X ∪ Y ⊆ ⋃ i, (walkDrawing D.rad.G (B i)).U) ∧
      ∀ i x q, D.IsPlaced (B i) x q → (q < p → x ∈ X) ∧ (p < q → x ∈ Y) := by
  have hn : ∀ i, (B i).length = (B false).length := fun i ↦ hB.len i false
  have hpi : ∀ i, p ≤ (B i).length := fun i ↦ by rw [hn]; exact hp
  choose P Q hsplit hlen using fun i ↦ GraphWalk.exists_split_at (B i) (hpi i)
  have hG : ∀ i, GraphWalk.vertexAt (B i) p ∈ D.rad.G.V := fun i ↦ (B
    i).mem_vertexSet_of_mem_support (GraphWalk.vertexAt_mem _ (hpi i))
  have hra : ∀ i, r ≠ GraphWalk.vertexAt (B i) p := fun i he ↦ by
    have := hB.position_unique (i := i) (i' := i) (Nat.zero_le _) (hpi i)
      ((GraphWalk.vertexAt_zero _).trans he)
    omega
  have hsP : ∀ i, (P i).IsSimple := fun i ↦ (isSimple_of_append (hsplit i ▸ hB.simple i)).1
  have hsQ : ∀ i, (Q i).IsSimple := fun i ↦ (isSimple_of_append (hsplit i ▸ hB.simple i)).2
  have hoffP : ∀ i i', GraphWalk.vertexAt (B i') p ∈ (walkDrawing D.rad.G (P i)).U
    → GraphWalk.vertexAt (B i') p = GraphWalk.vertexAt (B i) p := fun i i' hm ↦ by
    obtain ⟨t, ht, e⟩ := GraphWalk.exists_vertexAt _ (support_of_mem_U (P i) hm (hG i'))
    have e₁ : GraphWalk.vertexAt (B i) t = GraphWalk.vertexAt (P i) t := by
      conv_lhs => rw [hsplit i]
      exact GraphWalk.vertexAt_append_left _ _ ht
    have := hB.position_unique (i := i') (i' := i) (hpi i') (by
      have := hlen i
      have := hpi i
      omega) (e.trans e₁.symm)
    subst this
    rw [e, ← e₁]
  have hoffQ : ∀ i i', GraphWalk.vertexAt (B i') p ∈ (walkDrawing D.rad.G (Q i)).U
    → GraphWalk.vertexAt (B i') p = GraphWalk.vertexAt (B i) p := fun i i' hm ↦ by
    obtain ⟨t, ht, e⟩ := GraphWalk.exists_vertexAt _ (support_of_mem_U (Q i) hm (hG i'))
    have e₁ : GraphWalk.vertexAt (B i) (p + t) = GraphWalk.vertexAt (Q i) t := by
      have h₂ := GraphWalk.vertexAt_append_right (P i) (Q i) ht
      rw [hlen i, ← hsplit i] at h₂
      exact h₂
    have hlenB : (B i).length = p + (Q i).length := by
      conv_lhs => rw [hsplit i, GraphWalk.length_append, hlen i]
    have := hB.position_unique (i := i') (i' := i) (hpi i') (by omega) (e.trans e₁.symm)
    have ht0 : t = 0 := by omega
    subst ht0
    rw [e, ← e₁]
    rfl
  have hplace : ∀ i x q, D.IsPlaced (B i) x q → q ≠ p → x ≠ GraphWalk.vertexAt (B i) p
    := fun i x q hx hqp he ↦ by
    rcases hx.2.1 with h | h
    · exact hqp (hB.position_unique hx.1 (hpi i) (h.symm.trans he))
    · exact h (he ▸ hG i)
  by_cases hlt : p < (B false).length
  · have hau : ∀ i, GraphWalk.vertexAt (B i) p ≠ u := fun i he ↦ by
      have := hB.position_unique (i := i) (i' := i) (hpi i) le_rfl (he.trans
        (GraphWalk.vertexAt_length _ hB.u_mem).symm)
      have := hn i
      omega
    refine ⟨⋃ i, (walkDrawing D.rad.G (P i)).U \ {GraphWalk.vertexAt (B i) p}, ⋃ i,
      (walkDrawing D.rad.G (Q i)).U \ {GraphWalk.vertexAt (B i) p},
      isPreconnected_iUnion ⟨r, mem_iInter.mpr fun i ↦ ⟨(mem_walkDrawing_U _ _).mpr (.inl
        (P i).start_mem_support), hra i⟩⟩ fun i ↦ walkU_diff_end _ (hsP i) (hra i),
      isPreconnected_iUnion ⟨u, mem_iInter.mpr fun i ↦ ⟨(mem_walkDrawing_U _ _).mpr (.inl
        (Q i).end_mem_support), (hau i).symm⟩⟩ fun i ↦ walkU_diff_start _ (hsQ i)
          (hau i), fun i ↦ ⟨?_, ?_⟩, ?_, ?_⟩
    · rintro hm
      obtain ⟨i', hm₁, hm₂⟩ := mem_iUnion.mp hm
      exact hm₂ (hoffP i' i hm₁)
    · rintro hm
      obtain ⟨i', hm₁, hm₂⟩ := mem_iUnion.mp hm
      exact hm₂ (hoffQ i' i hm₁)
    · rintro x (hx | hx)
      · obtain ⟨i, hm, -⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i, by rw [hsplit i]; exact walkU_left_subset _ _ hm⟩
      · obtain ⟨i, hm, -⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i, by rw [hsplit i]; exact walkU_right_subset _ _ hm⟩
    · intro i x q hx
      have hs := hx.2.2 _ (P i) (Q i) (hsplit i)
      rw [hlen i] at hs
      exact ⟨fun h ↦ mem_iUnion.mpr ⟨i, hs.1 h, hplace i x q hx (by omega)⟩,
        fun h ↦ mem_iUnion.mpr ⟨i, hs.2 h, hplace i x q hx (by omega)⟩⟩
  · refine ⟨⋃ i, (walkDrawing D.rad.G (P i)).U \ {GraphWalk.vertexAt (B i) p}, ∅,
      isPreconnected_iUnion ⟨r, mem_iInter.mpr fun i ↦ ⟨(mem_walkDrawing_U _ _).mpr (.inl
        (P i).start_mem_support), hra i⟩⟩ fun i ↦ walkU_diff_end _ (hsP i) (hra i),
      isPreconnected_empty, fun i ↦ ⟨?_, by simp⟩, ?_, ?_⟩
    · rintro hm
      obtain ⟨i', hm₁, hm₂⟩ := mem_iUnion.mp hm
      exact hm₂ (hoffP i' i hm₁)
    · rintro x (hx | hx)
      · obtain ⟨i, hm, -⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i, by rw [hsplit i]; exact walkU_left_subset _ _ hm⟩
      · exact absurd hx (notMem_empty _)
    · intro i x q hx
      have hs := hx.2.2 _ (P i) (Q i) (hsplit i)
      rw [hlen i] at hs
      refine ⟨fun h ↦ mem_iUnion.mpr ⟨i, hs.1 h, hplace i x q hx (by omega)⟩, fun h ↦ ?_⟩
      have := hx.1
      have := hn i
      omega

end TangleDatum

omit [T2Space Shat] in
/-- Points of a connected set off `a, c` are not separated by `a, c`. -/
theorem not_crossesOn_of_part {Δ : Set Shat} {C : Set Δ} {X : Set Shat} (hX : IsPreconnected X)
  (hXC : X ⊆ Subtype.val '' C) {a c b d : Δ} (ha : a.1 ∉ X) (hc : c.1 ∉ X) (hb : b.1 ∈ X)
    (hd : d.1 ∈ X) :
    ¬ CrossesOn C a c b d := by
  rintro ⟨-, -, -, -, -, -, -, -, -, -, hne⟩
  have hsub : X ⊆ Δ := hXC.trans (by rintro _ ⟨z, -, rfl⟩; exact z.2)
  have hP : IsPreconnected (Subtype.val ⁻¹' X : Set Δ) := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.mpr hsub]
    exact hX
  have hin : (Subtype.val ⁻¹' X : Set Δ) ⊆ C \ {a, c} := fun z hz ↦ by
    obtain ⟨z', hz', e⟩ := hXC hz
    have : z = z' := Subtype.ext e.symm
    subst this
    refine ⟨hz', ?_⟩
    rintro (rfl | rfl)
    · exact ha hz
    · exact hc hz
  have h₁ := hP.subset_connectedComponentIn (x := b) hb hin
  exact hne (connectedComponentIn_eq (h₁ hd))

/-- A dual point set exists: choose one point on each segment. -/
theorem exists_isDualPointSet {T : Type} [TopologicalSpace T] (C V : Set T) : ∃ U, IsDualPointSet C
  V U := by
  classical
  by_cases hV : V = ∅
  · exact ⟨∅, fun _ ↦ rfl, fun h ↦ absurd hV h.ne_empty⟩
  have hne : ∀ s ∈ segmentsOf C V, s.Nonempty := fun s hs ↦ by
    obtain ⟨x, hx, rfl⟩ := hs.1
    exact ⟨x, mem_connectedComponentIn hx⟩
  have : Nonempty T := ⟨(nonempty_iff_ne_empty.mpr hV).some⟩
  choose! pt hpt using hne
  have hsub : ∀ s ∈ segmentsOf C V, s ⊆ C \ V := fun s hs ↦ by
    obtain ⟨x, hx, rfl⟩ := hs.1
    exact connectedComponentIn_subset _ _
  refine ⟨pt '' segmentsOf C V, fun h ↦ absurd h hV, fun _ ↦ ⟨?_, fun s hs ↦ ?_⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hsub s hs (hpt s hs)
  · have : pt '' segmentsOf C V ∩ s = {pt s} := by
      ext z
      constructor
      · rintro ⟨⟨s', hs', rfl⟩, hz⟩
        obtain ⟨x, hx, rfl⟩ := hs.1
        obtain ⟨x', hx', rfl⟩ := hs'.1
        have e₁ := connectedComponentIn_eq hz
        have e₂ := connectedComponentIn_eq (hpt _ hs')
        rw [mem_singleton_iff, e₁.trans e₂.symm]
      · rintro rfl
        exact ⟨mem_image_of_mem _ hs, hpt s hs⟩
    rw [this, ncard_singleton]

end GraphMinor.GM19
