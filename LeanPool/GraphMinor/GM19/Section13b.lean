/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13a

/-!
# Graph Minors XIX, Section 13: (13.2)

We work with walks. The weight `walkWeight` of a walk counts an edge as often as it is used. So a
walk of the same length as
a spoke, from the same vertex to the hub, weighs at least as much as the spoke
(`IsSpoke.walk_bound`). (13.2) follows, by the
paper's proof.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- A path of a drawing is a simple walk of the drawing. -/
theorem Drawing.IsPathOf.exists_simple_walk {T : Type} [TopologicalSpace T] {P G :
  Drawing T} {u v : T}
    (hP : Drawing.IsPathOf P G u v) : ∃ K : GraphWalk G.toGraph u v, K.IsSimple ∧
      (∀ x, x ∈ P.V ↔ x ∈ K.support) ∧
      (∀ e, e ∈ P.E ↔ e ∈ K.edges) := by
  obtain ⟨W, hW, hV, hE⟩ := hP.2
  obtain ⟨K, hs, he⟩ := hP.1.exists_walk_up W
  refine ⟨K, ?_, ?_, ?_⟩
  · unfold GraphWalk.IsSimple
    rw [hs]
    exact hW
  · intro x
    rw [hV, hs]
    rfl
  · intro e
    rw [hE, he]
    rfl

/-- The first vertex of a walk in a set. -/
theorem GraphWalk.exists_first_mem {α' β : Type*} {G : Graph α' β} {a b : α'}
  (K : GraphWalk G a b) {X : Set α'}
    (hm : ∃ x ∈ K.support, x ∈ X) : ∃ u ∈ X, ∃ (A : GraphWalk G a u) (B : GraphWalk G u b), K
      = A.append B ∧
      ∀ x ∈ A.support, x ∈ X → x = u := by
  induction K with
  | nil h =>
    obtain ⟨x, hx, hxX⟩ := hm
    simp only [GraphWalk.support_nil, List.mem_singleton] at hx
    subst hx
    refine ⟨x, hxX, .nil h, .nil h, rfl, ?_⟩
    intro y hy _
    simpa using hy
  | @cons a c b e h r ih =>
    by_cases ha : a ∈ X
    · refine ⟨a, ha, .nil h.left_mem, .cons h r, rfl, ?_⟩
      intro y hy _
      simpa using hy
    · obtain ⟨x, hx, hxX⟩ := hm
      have hr : ∃ x ∈ r.support, x ∈ X := by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd hxX ha
        · exact ⟨x, hx', hxX⟩
      obtain ⟨u, hu, A, B, rfl, hA⟩ := ih hr
      refine ⟨u, hu, .cons h A, B, rfl, ?_⟩
      intro y hy hyX
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd hyX ha
      · exact hA y hy' hyX

/-- Two simple walks from one vertex with the same edges have the same end and the same vertices. -/
theorem simple_walks_eq {T : Type} [TopologicalSpace T] {G : Drawing T} {u a b : T}
  (A : GraphWalk G.toGraph u a)
    (B : GraphWalk G.toGraph u b) (hA : A.IsSimple) (hB : B.IsSimple)
      (hE : ∀ e, e ∈ A.edges ↔ e ∈ B.edges) :
    a = b ∧ ∀ x, x ∈ A.support ↔ x ∈ B.support := by
  induction A generalizing b with
  | nil h =>
    cases B with
    | nil _ => exact ⟨rfl, fun _ ↦ Iff.rfl⟩
    | @cons _ x _ e hl r =>
      have := (hE e).mpr (by simp)
      simp at this
  | @cons u x a e hl r ih =>
    cases B with
    | nil _ =>
      have := (hE e).mp (by simp)
      simp at this
    | @cons _ x' _ e' hl' r' =>
      have hsA : (GraphWalk.cons hl r).support.Nodup := hA
      have hsB : (GraphWalk.cons hl' r').support.Nodup := hB
      simp only [GraphWalk.support_cons, List.nodup_cons] at hsA hsB
      have hee : e = e' := by
        have := (hE e).mp (by simp)
        rcases List.mem_cons.mp (by simpa using this) with h | h
        · exact h
        · exact absurd (r'.left_mem_support_of_mem_edges h hl) hsB.1
      subst hee
      obtain rfl := hl.right_unique hl'
      have hE' : ∀ f, f ∈ r.edges ↔ f ∈ r'.edges := by
        intro f
        constructor
        · intro hf
          have h₁ := (hE f).mp (by simp [hf])
          rcases List.mem_cons.mp (by simpa using h₁) with h | h
          · subst h
            exact absurd (r.left_mem_support_of_mem_edges hf hl) hsA.1
          · exact h
        · intro hf
          have h₁ := (hE f).mpr (by simp [hf])
          rcases List.mem_cons.mp (by simpa using h₁) with h | h
          · subst h
            exact absurd (r'.left_mem_support_of_mem_edges hf hl) hsB.1
          · exact h
      obtain ⟨h₁, h₂⟩ := ih r' hsA.2 hsB.2 hE'
      refine ⟨h₁, fun y ↦ ?_⟩
      simp only [GraphWalk.support_cons, List.mem_cons, h₂]

/-- The sum over the set of a list is at most the sum over the list, for nonnegative terms. -/
theorem sum_toFinset_le_sum_map {β : Type*} [DecidableEq β] (f : β → ℝ) (l : List β)
  (hf : ∀ e ∈ l, 0 ≤ f e) :
    ∑ e ∈ l.toFinset, f e ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl := ih fun e he ↦ hf e (.tail _ he)
    have ha := hf a (.head _)
    rw [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases hal : a ∈ l.toFinset
    · rw [Finset.insert_eq_of_mem hal]
      linarith
    · rw [Finset.sum_insert hal]
      linarith

namespace TieBreaker

variable {Γ : Painting S} {rad : RadialDrawing cap Γ}

/-- The weight of a walk, counting an edge as often as it is used. -/
noncomputable def walkWeight (tb : TieBreaker rad) {u v : Shat} (T : GraphWalk rad.G.toGraph u v) :
  ℝ :=
  (T.edges.map tb.wtE).sum

omit [T2Space S] [T2Space Shat] in
theorem walkWeight_append (tb : TieBreaker rad) {u v w : Shat} (A : GraphWalk rad.G.toGraph u v)
    (B : GraphWalk rad.G.toGraph v w) : tb.walkWeight (A.append B) = tb.walkWeight A +
      tb.walkWeight B := by
  simp [walkWeight, GraphWalk.edges_append]

omit [T2Space S] in
theorem mem_edges_E {u v : Shat} (T : GraphWalk rad.G.toGraph u v) {e : Set Shat}
  (he : e ∈ T.edges) : e ∈ rad.G.E := by
  have h : e ∈ (walkDrawing rad.G T).E := by
    rw [walkDrawing_E]
    exact he
  exact (walkDrawing_isSubdrawing rad.G T).2 h

omit [T2Space S] in
theorem weightSub_walkDrawing_le (tb : TieBreaker rad) {u v : Shat} (T : GraphWalk rad.G.toGraph u
  v) :
    tb.weightSub (walkDrawing rad.G T) ≤ tb.walkWeight T := by
  classical
  have hE : (walkDrawing rad.G T).E = ↑T.edges.toFinset := by
    rw [walkDrawing_E]
    ext e
    simp
  rw [weightSub, hE, finsum_mem_coe_finset]
  exact sum_toFinset_le_sum_map _ _ fun e he ↦ (tb.wtE_pos e (mem_edges_E T he)).le

omit [T2Space S] [T2Space Shat] in
theorem weightSub_eq_of_simple (tb : TieBreaker rad) {u v : Shat} {T : GraphWalk rad.G.toGraph u v}
  (hT : T.IsSimple)
    {P : Drawing Shat} (hP : ∀ e, e ∈ P.E ↔ e ∈ T.edges) : tb.weightSub P = tb.walkWeight T := by
  classical
  have hE : P.E = ↑T.edges.toFinset := by
    ext e
    simp [hP]
  rw [weightSub, hE, finsum_mem_coe_finset]
  exact List.sum_toFinset _ hT.edges_nodup

omit [T2Space S] [T2Space Shat] in
theorem weightSub_mono (tb : TieBreaker rad) {X Y : Drawing Shat} (hE : X.E ⊆ Y.E)
  (hY : Y.E ⊆ rad.G.E) :
    tb.weightSub X ≤ tb.weightSub Y := by
  classical
  simp only [weightSub]
  rw [finsum_mem_eq_finite_toFinset_sum _ (show X.E.Finite from X.finite_edges),
    finsum_mem_eq_finite_toFinset_sum _ (show Y.E.Finite from Y.finite_edges)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun e he ↦ ?_) fun e he _ ↦ ?_
  · exact (Set.Finite.mem_toFinset _).mpr (hE ((Set.Finite.mem_toFinset _).mp he))
  · exact (tb.wtE_pos e (hY ((Set.Finite.mem_toFinset _).mp he))).le

end TieBreaker

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {v h h' : Shat} {P : Drawing
  Shat}

omit [T2Space S] in
/-- A walk from the outer end of a spoke to the hub is as long as the spoke, and if it has the same
length then it weighs at
least as much. -/
theorem IsSpoke.walk_bound (hS : D.IsSpoke W H v h P) (hh' : h' ∈ H.V)
  (T : GraphWalk D.rad.G.toGraph v h') :
    P.E.ncard ≤ T.length ∧ (T.length = P.E.ncard → D.tb.weightSub P ≤ D.tb.walkWeight T) := by
  classical
  obtain ⟨T', hs, -, he⟩ := GM11.GraphWalk.exists_isSimple T
  have hsub := walkDrawing_isSubdrawing D.rad.G T'
  have hPath : Drawing.IsPathOf (walkDrawing D.rad.G T') D.rad.G v h'
    := ⟨hsub, walkDrawing_isPathBetween _ hs⟩
  have hc := ncard_walk_E D.rad.G hs
  have hl : T'.length ≤ T.length := by
    have : T'.edges.length ≤ T.edges.length := (hs.edges_nodup.subperm he).length_le
    exact this
  have hmin := hS.min_length _ h' hh' hPath
  refine ⟨by omega, fun heq ↦ ?_⟩
  have h₁ := hS.min_weight _ h' hh' hPath (by omega)
  have h₂ : D.tb.weightSub (walkDrawing D.rad.G T') ≤ D.tb.weightSub (walkDrawing D.rad.G T) :=
    D.tb.weightSub_mono (by rw [walkDrawing_E, walkDrawing_E]; exact he)
      (walkDrawing_isSubdrawing _ _).2
  have h₃ := D.tb.weightSub_walkDrawing_le T
  linarith

omit [T2Space S] in
/-- **Graph Minors XIX, (13.2)** (page 366): "**13.2.** *Let $v_1, v_2 \in V(\Gamma) \cap
bd(\Sigma)$.
If $S_{v_1}$ meets $S_{v_2}$ then they have the same inner end, and $S_{v_1} \cap S_{v_2}$ is a
path.*" The paper prints `bd(Σ)` for `bd(W)`. The path `Q` also ends at the inner end. -/
theorem theorem_13_2_proof {v₁ v₂ h₁ h₂ : Shat} {S₁ S₂ : Drawing Shat}
  (hS₁ : D.IsSpoke W H v₁ h₁ S₁) (hS₂ : D.IsSpoke W H v₂ h₂ S₂)
    (hm : (S₁.V ∩ S₂.V).Nonempty) : h₁ = h₂ ∧ ∃ u, ∃ Q : Drawing Shat, Q.IsPathOf D.rad.G u h₁ ∧
      S₁.V ∩ S₂.V = Q.V ∧ S₁.E ∩ S₂.E = Q.E := by
  classical
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨K₁, hK₁, hV₁, hE₁⟩ := Drawing.IsPathOf.exists_simple_walk hS₁.is_path
  obtain ⟨K₂, hK₂, hV₂, hE₂⟩ := Drawing.IsPathOf.exists_simple_walk hS₂.is_path
  obtain ⟨x, hx₁, hx₂⟩ := hm
  obtain ⟨u, huS, P₁, Q₁, rfl, hfirst⟩ := GraphWalk.exists_first_mem K₁ (X := {y | y ∈ K₂.support})
    ⟨x, (hV₁ x).mp hx₁, (hV₂ x).mp hx₂⟩
  obtain ⟨P₂, Q₂, rfl⟩ := K₂.exists_append_of_mem huS
  have hc₁ : S₁.E.ncard = (P₁.append Q₁).length := by
    have := ncard_walk_E D.rad.G hK₁
    rw [← this]
    congr 1
    ext e
    rw [hE₁ e, walkDrawing_E]
    rfl
  have hc₂ : S₂.E.ncard = (P₂.append Q₂).length := by
    have := ncard_walk_E D.rad.G hK₂
    rw [← this]
    congr 1
    ext e
    rw [hE₂ e, walkDrawing_E]
    rfl
  rw [GraphWalk.length_append] at hc₁ hc₂
  obtain ⟨b₁, w₁⟩ := hS₁.walk_bound hS₂.h_mem (P₁.append Q₂)
  obtain ⟨b₂, w₂⟩ := hS₂.walk_bound hS₁.h_mem (P₂.append Q₁)
  rw [GraphWalk.length_append] at b₁ b₂ w₁ w₂
  have hw₁ := D.tb.weightSub_eq_of_simple hK₁ hE₁
  have hw₂ := D.tb.weightSub_eq_of_simple hK₂ hE₂
  rw [D.tb.walkWeight_append] at hw₁ hw₂
  have hq : Q₁.length = Q₂.length := by omega
  have hl₁ := w₁ (by omega)
  have hl₂ := w₂ (by omega)
  rw [D.tb.walkWeight_append] at hl₁ hl₂
  have hweq : D.tb.walkWeight Q₁ = D.tb.walkWeight Q₂ := by linarith
  have hQ₁s : Q₁.IsSimple := (GraphMinor.GM19.GraphWalk.IsSimple.of_append hK₁).2
  have hQ₂s : Q₂.IsSimple := (GraphMinor.GM19.GraphWalk.IsSimple.of_append hK₂).2
  have hEq : ∀ e, e ∈ Q₁.edges ↔ e ∈ Q₂.edges := by
    set A := walkDrawing D.rad.G Q₁ with hA
    set B := walkDrawing D.rad.G Q₂ with hB
    have hAE : ∀ e, e ∈ A.E ↔ e ∈ Q₁.edges := fun e ↦ by rw [hA, walkDrawing_E]; rfl
    have hBE : ∀ e, e ∈ B.E ↔ e ∈ Q₂.edges := fun e ↦ by rw [hB, walkDrawing_E]; rfl
    have hwA := D.tb.weightSub_eq_of_simple hQ₁s hAE
    have hwB := D.tb.weightSub_eq_of_simple hQ₂s hBE
    have hAf : A.E.Finite := A.finite_edges
    have hBf : B.E.Finite := B.finite_edges
    have hDisjoint₁ : Disjoint (A.E ∩ B.E) (A.E \ B.E) :=
      disjoint_left.mpr fun _ he₁ he₂ ↦ he₂.2 he₁.2
    have hDisjoint₂ : Disjoint (B.E ∩ A.E) (B.E \ A.E) :=
      disjoint_left.mpr fun _ he₁ he₂ ↦ he₂.2 he₁.2
    have hs₁ : ∑ᶠ e ∈ A.E ∩ B.E, D.tb.wtE e + ∑ᶠ e ∈ A.E \ B.E, D.tb.wtE e = D.tb.weightSub A := by
      rw [← finsum_mem_union hDisjoint₁ (hAf.subset inter_subset_left)
        (hAf.subset sdiff_subset), inter_union_sdiff]
      rfl
    have hs₂ : ∑ᶠ e ∈ A.E ∩ B.E, D.tb.wtE e + ∑ᶠ e ∈ B.E \ A.E, D.tb.wtE e = D.tb.weightSub B := by
      rw [Set.inter_comm, ← finsum_mem_union hDisjoint₂ (hBf.subset inter_subset_left)
        (hBf.subset sdiff_subset), inter_union_sdiff]
      rfl
    have heq : ∑ᶠ e ∈ A.E \ B.E, D.tb.wtE e = ∑ᶠ e ∈ B.E \ A.E, D.tb.wtE e := by linarith
    have hsubA : A.E ⊆ D.rad.G.E := (walkDrawing_isSubdrawing _ _).2
    have hsubB : B.E ⊆ D.rad.G.E := (walkDrawing_isSubdrawing _ _).2
    have hdis : Disjoint (A.E \ B.E) (B.E \ A.E) := disjoint_left.mpr fun e h₁ h₂ ↦ h₂.2 h₁.1
    have hY : B.E \ A.E = ∅ := by
      by_contra hne
      exact D.tb.weight_ne (sdiff_subset.trans hsubA) (sdiff_subset.trans hsubB) hdis
        (nonempty_iff_ne_empty.mpr hne) heq
    have hX : A.E \ B.E = ∅ := by
      by_contra hne
      exact D.tb.weight_ne (sdiff_subset.trans hsubB) (sdiff_subset.trans hsubA) hdis.symm
        (nonempty_iff_ne_empty.mpr hne) heq.symm
    intro e
    rw [← hAE, ← hBE]
    constructor
    · intro h
      by_contra hn
      have : e ∈ A.E \ B.E := ⟨h, hn⟩
      rw [hX] at this
      exact this
    · intro h
      by_contra hn
      have : e ∈ B.E \ A.E := ⟨h, hn⟩
      rw [hY] at this
      exact this
  obtain ⟨he, hsup⟩ := simple_walks_eq Q₁ Q₂ hQ₁s hQ₂s hEq
  subst he
  refine ⟨rfl, u, walkDrawing D.rad.G Q₁, ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hQ₁s⟩, ?_, ?_⟩
  · ext y
    rw [walkDrawing_V]
    constructor
    · rintro ⟨h₁, h₂⟩
      have h₁' := (hV₁ y).mp h₁
      have h₂' := (hV₂ y).mp h₂
      rcases (GraphWalk.mem_support_append P₁ Q₁).mp h₁' with h' | h'
      · rw [hfirst y h' h₂']
        exact Q₁.start_mem_support
      · exact h'
    · intro h'
      have h'' : y ∈ Q₁.support := h'
      exact ⟨(hV₁ y).mpr ((GraphWalk.mem_support_append P₁ Q₁).mpr (.inr h'')),
        (hV₂ y).mpr ((GraphWalk.mem_support_append P₂ Q₂).mpr (.inr ((hsup y).mp h'')))⟩
  · ext e
    rw [walkDrawing_E]
    constructor
    · rintro ⟨h₁, h₂⟩
      have h₁' := (hE₁ e).mp h₁
      have h₂' := (hE₂ e).mp h₂
      rw [GraphWalk.edges_append, List.mem_append] at h₁'
      rcases h₁' with h' | h'
      · exfalso
        have heG : e ∈ D.rad.G.E := TieBreaker.mem_edges_E _ h'
        obtain ⟨a, ha, b, hb, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e heG
        have hl : D.rad.G.toGraph.IsLink e a b := ⟨heG, D.rad.isPreRadial.2.1 ha, hb.1, hcap⟩
        have hl' : D.rad.G.toGraph.IsLink e b a := ⟨heG, hb.1, D.rad.isPreRadial.2.1 ha, by rw
          [hcap, pair_comm]⟩
        have e₁ := hfirst a (P₁.left_mem_support_of_mem_edges h' hl) ((P₂.append
          Q₂).left_mem_support_of_mem_edges h₂' hl)
        have e₂ := hfirst b (P₁.left_mem_support_of_mem_edges h' hl')
          ((P₂.append Q₂).left_mem_support_of_mem_edges h₂' hl')
        exact hb.2 ((e₂.trans e₁.symm) ▸ ha)
      · exact h'
    · intro h'
      have h'' : e ∈ Q₁.edges := h'
      exact ⟨(hE₁ e).mpr (by rw [GraphWalk.edges_append, List.mem_append]; exact .inr h''),
        (hE₂ e).mpr (by rw [GraphWalk.edges_append, List.mem_append]; exact .inr ((hEq e).mp h''))⟩

end TangleDatum

end GraphMinor.GM19
