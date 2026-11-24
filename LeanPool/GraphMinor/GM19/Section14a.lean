/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13zf
public import LeanPool.GraphMinor.Surface.Fan

/-!
# Graph Minors XIX, Section 14: sectors exist

The two spokes at a vertex of `R* ∩ bd(W)` give the sector `Δ_v` of page 368. The paper takes this
as seen.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
theorem GraphWalk.support_of_closed {G : Drawing Shat} {a : Shat} (T : GraphWalk G.toGraph a a)
  (hs : T.IsSimple) {y : Shat} (hy : y ∈ T.support) : y = a := by
  cases T with
  | nil h => simpa using hy
  | cons hl t =>
    exfalso
    have h₁ : (GraphWalk.cons hl t).support.Nodup := hs
    rw [GraphWalk.support_cons, List.nodup_cons] at h₁
    exact h₁.1 t.end_mem_support


section Chord

variable {T : Type} [TopologicalSpace T] [T2Space T]

omit [T2Space T] in
/-- A line with ends `a, b` is more than its ends. -/
theorem IsLineWithEnds.diff_nonempty {L : Set T} {a b : T} (hl : IsLineWithEnds L a b) :
  (L \ {a, b}).Nonempty := by
  by_contra hn
  have hsub : L ⊆ {a, b} := sdiff_eq_empty.mp (not_nonempty_iff_eq_empty.mp hn)
  obtain ⟨f, hf0, hf1⟩ := hl
  have hx₀ : (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) ≠ 0 := fun h ↦ by
    have := congrArg Subtype.val h
    norm_num at this
  have hx₁ : (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) ≠ 1 := fun h ↦ by
    have := congrArg Subtype.val h
    norm_num at this
  rcases hsub (f ⟨1 / 2, by norm_num, by norm_num⟩).2 with h | h
  · exact hx₀ (f.injective (Subtype.ext (h.trans hf0.symm)))
  · exact hx₁ (f.injective (Subtype.ext ((mem_singleton_iff.mp h).trans hf1.symm)))

/-- If an `O`-arc is two lines with the same ends then a third line with those ends in the `O`-arc
is one of the two. -/
theorem line_eq_of_two_lines {P Q J : Set T} {a b : T} (hP : IsLineWithEnds P a b)
  (hQ : IsLineWithEnds Q a b) (hPQ : P ∩ Q = {a, b})
    (hJ : IsLineWithEnds J a b) (hsub : J ⊆ P ∪ Q) : J = P ∨ J = Q := by
  have hc := hJ.isPreconnected_diff
  have hcl₁ : IsClosed P := hP.isCompact.isClosed
  have hcl₂ : IsClosed Q := hQ.isCompact.isClosed
  have hcov : J \ {a, b} ⊆ P ∪ Q := sdiff_subset.trans hsub
  have hmem : ∀ {X : Set T}, IsLineWithEnds X a b → J \ {a, b} ⊆ X → J = X := fun {X} hl hs ↦ by
    refine hl.eq_of_subset (GraphMinor.GM19.IsLineWithEnds.isPreconnected' hJ)
      (fun y hy ↦ ?_) hJ.left_mem hJ.right_mem
    by_cases hy' : y ∈ ({a, b} : Set T)
    · rcases hy' with rfl | hy'
      · exact hl.left_mem
      · rw [mem_singleton_iff.mp hy']
        exact hl.right_mem
    · exact hs ⟨hy, hy'⟩
  by_cases h₁ : J \ {a, b} ⊆ P
  · exact .inl (hmem hP h₁)
  by_cases h₂ : J \ {a, b} ⊆ Q
  · exact .inr (hmem hQ h₂)
  exfalso
  obtain ⟨x, hx, hxn⟩ := not_subset.mp h₁
  obtain ⟨y, hy, hyn⟩ := not_subset.mp h₂
  obtain ⟨z, hz, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hc P Q hcl₁ hcl₂ hcov ⟨y, hy,
    (hcov hy).resolve_right hyn⟩
    ⟨x, hx, (hcov hx).resolve_left hxn⟩
  exact hz.2 (hPQ ▸ ⟨hz₁, hz₂⟩)

/-- A line on `bd(W)` and a chord of `W` with the same ends cut `W` into two discs, one of them
bounded by the line and the chord. This is `disc_iArc`, with the part of `bd(W)` named. -/
theorem exists_chord_discs_of_lines {W P Q Y Z : Set T} {a b : T} (hW : IsClosedDisc W)
  (hlP : IsLineWithEnds P a b)
    (hlQ : IsLineWithEnds Q a b) (hPQ : P ∩ Q = {a, b}) (hUU : discBd W = P ∪ Q)
      (hlY : IsLineWithEnds Y a b) (hYb : Y ⊆ discBd W)
    (hlZ : IsLineWithEnds Z a b) (hZW : Z ⊆ W) (hZb : Z ∩ discBd W = {a, b}) :
    ∃ Δ₁ Δ₂, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧ Δ₁ ∪ Δ₂ = W ∧ Δ₁ ∩ Δ₂ = Z ∧ discBd Δ₁ = Y ∪ Z
      ∧ discBd Δ₂ = (discBd W \ (Y \ {a, b})) ∪ Z := by
  have hab : a ≠ b := hlY.ne'
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hA, hc, d₁, d₂, hu, hi, b₁, b₂, -⟩ := disc_iArc W Z a b hW hZW hab hlZ hZb
  -- `Y` is one of the two arcs. Name the other `Y'`.
  obtain ⟨Y', hlY', hYY, hUY⟩ : ∃ Y', IsLineWithEnds Y' a b ∧ Y ∩ Y' = {a, b} ∧ discBd W = Y ∪ Y'
    := by
    rcases line_eq_of_two_lines hlP hlQ hPQ hlY (hUU ▸ hYb) with rfl | rfl
    · exact ⟨Q, hlQ, hPQ, hUU⟩
    · exact ⟨P, hlP, by rw [Set.inter_comm]; exact hPQ, by rw [Set.union_comm]; exact hUU⟩
  have hY : discBd W \ {a, b} = (Y \ {a, b}) ∪ (Y' \ {a, b}) := by rw [hUY, union_sdiff_distrib]
  have hdj : Disjoint (Y \ {a, b}) (Y' \ {a, b}) := disjoint_left.mpr fun y h₁ h₂ ↦ h₁.2
    (hYY ▸ ⟨h₁.1, h₂.1⟩)
  have hab_sub : ∀ {X : Set T}, IsLineWithEnds X a b → (X \ {a, b}) ∪ {a, b} = X := fun {X} hl ↦ by
    rw [sdiff_union_self, union_eq_left]
    rintro y (rfl | hy)
    · exact hl.left_mem
    · rw [mem_singleton_iff.mp hy]
      exact hl.right_mem
  have hsZ : ({a, b} : Set T) ⊆ Z := by
    rintro y (rfl | hy)
    · exact hlZ.left_mem
    · rw [mem_singleton_iff.mp hy]
      exact hlZ.right_mem
  have hadd : ∀ {X : Set T}, IsLineWithEnds X a b → (X \ {a, b}) ∪ Z = X ∪ Z := fun {X} hl ↦ by
    conv_rhs => rw [← hab_sub hl, Set.union_assoc, union_eq_right.mpr hsZ]
  have hrest : discBd W \ (Y \ {a, b}) = Y' := by
    ext y
    constructor
    · rintro ⟨hy, hn⟩
      rcases hUY ▸ hy with h | h
      · by_cases hy' : y ∈ ({a, b} : Set T)
        · exact hYY ▸ hy' |>.2
        · exact absurd ⟨h, hy'⟩ hn
      · exact h
    · intro hy
      refine ⟨hUY ▸ .inr hy, fun h ↦ h.2 (hYY ▸ ⟨h.1, hy⟩)⟩
  rcases comps_two hA hc hY hdj hlY.isPreconnected_diff hlY'.isPreconnected_diff
    (GraphMinor.GM19.IsLineWithEnds.diff_nonempty hlY)
      (GraphMinor.GM19.IsLineWithEnds.diff_nonempty hlY') with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · refine ⟨Δ₁, Δ₂, d₁, d₂, hu, hi, ?_, ?_⟩
    · rw [b₁, e₁, hadd hlY]
    · rw [b₂, e₂, hadd hlY', hrest]
  · refine ⟨Δ₂, Δ₁, d₂, d₁, by rwa [Set.union_comm],
      by rwa [Set.inter_comm], ?_, ?_⟩
    · rw [b₂, e₂, hadd hlY]
    · rw [b₁, e₁, hadd hlY', hrest]

variable [ConnectedSpace T]

omit [ConnectedSpace T] in
/-- Two paths whose union is a drawing cover it. -/
theorem paths_U_union {F P Q : Drawing T} (hPs : P.IsSubdrawing F) (hQs : Q.IsSubdrawing F)
  (hsup : F.sup P Q = F) : F.U = P.U ∪ Q.U := by
  apply subset_antisymm
  · intro y hy
    rw [← hsup, Drawing.U_eq, Drawing.sup_V hPs hQs, Drawing.sup_E hPs hQs] at hy
    rcases hy with h' | h'
    · rcases h' with h'' | h''
      · exact .inl (P.V_subset_U h'')
      · exact .inr (Q.V_subset_U h'')
    · obtain ⟨e, he, hye⟩ : ∃ e ∈ P.E ∪ Q.E, y ∈ closure e := by simpa using h'
      rcases he with h'' | h''
      · exact .inl (P.closure_subset_U h'' hye)
      · exact .inr (Q.closure_subset_U h'' hye)
  · exact union_subset hPs.U_subset hQs.U_subset

omit [ConnectedSpace T] in
/-- Two paths of a drawing with disjoint edges meet in `U` only where they meet in vertices. -/
theorem paths_U_inter {F P Q : Drawing T} {a b : T} (hPs : P.IsSubdrawing F)
  (hQs : Q.IsSubdrawing F) (hPQ : P.V ∩ Q.V = {a, b}) (hE : Disjoint P.E Q.E)
    (hlP : IsLineWithEnds P.U a b) (hlQ : IsLineWithEnds Q.U a b) : P.U ∩ Q.U = {a, b} := by
  apply subset_antisymm
  · rintro y ⟨hyP, hyQ⟩
    by_cases hV : y ∈ F.V
    · have h : y ∈ P.V ∩ Q.V := ⟨mem_V_of_mem_U hPs hyP hV, mem_V_of_mem_U hQs hyQ hV⟩
      rwa [hPQ] at h
    · exfalso
      rw [Drawing.U_eq] at hyP
      rcases hyP with h' | h'
      · exact hV (hPs.1 h')
      obtain ⟨e, he, hye⟩ : ∃ e ∈ P.E, y ∈ closure e := by simpa using h'
      have hye' : y ∈ e := (closure_edge_subset (hPs.2 he) hye).resolve_right hV
      have heQ : e ∉ Q.E := fun h'' ↦ disjoint_left.mp hE he h''
      exact disjoint_left.mp (edge_disjoint_U hQs (hPs.2 he) heQ) hye' hyQ
  · rintro y (rfl | hy)
    · exact ⟨hlP.left_mem, hlQ.left_mem⟩
    · rw [mem_singleton_iff.mp hy]
      exact ⟨hlP.right_mem, hlQ.right_mem⟩

/-- Graph form of `exists_chord_discs_of_lines`. -/
theorem exists_chord_discs {G : Drawing T} {W : Set T} (hW : IsClosedDisc W)
  (hG : discBd W ⊆ G.U) {a b : T} (hab : a ≠ b)
    {Y Z : GraphWalk G.toGraph a b} (hY : Y.IsSimple) (hZ : Z.IsSimple) (hYb :
      (walkDrawing G Y).U ⊆ discBd W)
    (hZW : (walkDrawing G Z).U ⊆ W) (hZb : (walkDrawing G Z).U ∩ discBd W = {a, b}) :
    ∃ Δ₁ Δ₂, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧ Δ₁ ∪ Δ₂ = W ∧ Δ₁ ∩ Δ₂ = (walkDrawing G Z).U ∧
      discBd Δ₁ = (walkDrawing G Y).U ∪ (walkDrawing G Z).U ∧
      discBd Δ₂ = (discBd W \ ((walkDrawing G Y).U \ {a, b})) ∪ (walkDrawing G Z).U := by
  classical
  have hlY := isLine_of_isPathBetween (walkDrawing_isPathBetween G hY) hab
  have hlZ := isLine_of_isPathBetween (walkDrawing_isPathBetween G hZ) hab
  obtain ⟨F, hFc, hFs, hFU⟩ := exists_circuit_of_oArc hW.isOArc_discBd hG
  have haV : a ∈ F.V := mem_V_of_mem_U hFs (hFU ▸ hYb hlY.left_mem) (Y.mem_vertexSet_of_mem_support
    Y.start_mem_support)
  have hbV : b ∈ F.V := mem_V_of_mem_U hFs (hFU ▸ hYb hlY.right_mem)
    (Y.mem_vertexSet_of_mem_support Y.end_mem_support)
  obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, hPQ, hE, hsup⟩ := Drawing.IsCircuit.exists_two_paths hFc
    haV hbV hab
  have hlP := isLine_of_isPathBetween hP hab
  have hlQ := isLine_of_isPathBetween hQ hab
  have hPQU : P.U ∩ Q.U = {a, b} := paths_U_inter hPs hQs hPQ hE hlP hlQ
  have hUU : discBd W = P.U ∪ Q.U := hFU ▸ paths_U_union hPs hQs hsup
  exact exists_chord_discs_of_lines hW hlP hlQ hPQU hUU hlY hYb hlZ hZW hZb

end Chord

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat}

omit [T2Space Shat] in
theorem mem_support_of_mem_closure_edge {G : Drawing Shat} {a b x : Shat}
  (t : GraphWalk G.toGraph a b) {e : Set Shat} (he : e ∈ t.edges)
    (hx : x ∈ closure e) (hV : x ∈ G.V) : x ∈ t.support := by
  induction t with
  | nil h => simp [GraphWalk.edges] at he
  | cons hl q ih =>
    rw [GraphWalk.edges_cons, List.mem_cons] at he
    rw [GraphWalk.support_cons, List.mem_cons]
    rcases he with rfl | he
    · have hm : x ∈ closure e ∩ G.V := ⟨hx, hV⟩
      rw [hl.2.2.2] at hm
      rcases hm with rfl | hm
      · exact .inl rfl
      · exact .inr (mem_singleton_iff.mp hm ▸ q.start_mem_support)
    · exact .inr (ih he)

theorem exists_first_edge {G F P : Drawing Shat} (hF : F.IsSubdrawing G)
  (hP : P.IsSubdrawing F) {a b : Shat} (h : P.IsPathBetween a b) (hpos : 0 < P.length)
    (hG : a ∈ G.V) :
    ∃ f v, G.toGraph.IsLink f a v ∧ f ∈ P.E ∧ v ∈ P.V ∧ v ≠ a ∧ (v = b → ∀ y ∈ P.V, y = a ∨ y = b)
      ∧ ∀ e ∈ P.E, a ∈ closure e → e = f := by
  obtain ⟨Z, hs, hV, hE⟩ := h
  cases Z with
  | nil h' =>
    exfalso
    rw [Drawing.length, hE] at hpos
    simp at hpos
  | @cons a v b f hl t =>
    have hfP : f ∈ P.E := by rw [hE]; simp
    have hvP : v ∈ P.V := by rw [hV]; simp [GraphWalk.support_cons, t.start_mem_support]
    have hs₁ : (GraphWalk.cons hl t).support.Nodup := hs
    rw [GraphWalk.support_cons, List.nodup_cons] at hs₁
    have hne : v ≠ a := fun e ↦ hs₁.1 (e ▸ t.start_mem_support)
    have hsub := hP.trans hF
    have hfG : f ∈ G.E := hsub.2 hfP
    have haP : a ∈ P.V := by rw [hV]; simp [GraphWalk.support_cons]
    refine ⟨f, v, ⟨hfG, hG, hsub.1 hvP, ?_⟩, hfP, hvP, hne, ?_, ?_⟩
    · rw [closure_inter_V_eq_tilde hfG, ← closure_inter_V_eq_tilde hfP]
      exact hl.2.2.2
    · rintro rfl y hy
      rw [hV] at hy
      have hy' : y ∈ (GraphWalk.cons hl t).support := hy
      rw [GraphWalk.support_cons, List.mem_cons] at hy'
      rcases hy' with rfl | hy'
      · exact .inl rfl
      · exact .inr (GraphWalk.support_of_closed t hs₁.2 hy')
    · intro e he hae
      rw [hE] at he
      have he' : e ∈ (GraphWalk.cons hl t).edges := he
      rw [GraphWalk.edges_cons, List.mem_cons] at he'
      rcases he' with rfl | he'
      · rfl
      · exact absurd (mem_support_of_mem_closure_edge t he' hae haP) hs₁.1

/-- A vertex of `R* ∩ bd(W)` has two neighbours in `Γ* ∩ bd(W)`, because `bd(W)` is a circuit of
`Γ*` with at least three vertices of `Γ`. -/
theorem IsWheelHubOfRadius.exists_two_bd_edges (h : D.IsWheelHubOfRadius W H ρ)
  (hbd : discBd W ⊆ cap.emb '' (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (hr : r ∈ D.rad.Rstar) (hrb : r ∈ discBd W) :
    ∃ f₁ f₂ v₁ v₂, v₁ ≠ v₂ ∧ D.rad.G.toGraph.IsLink f₁ r v₁ ∧ D.rad.G.toGraph.IsLink f₂ r v₂
      ∧ f₁ ⊆ discBd W ∧ f₂ ⊆ discBd W ∧
      ∀ f ∈ D.rad.G.E, f ⊆ discBd W → r ∈ closure f → f = f₁ ∨ f = f₂ := by
  classical
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨F, hFc, hFs, hFU⟩ := exists_circuit_of_oArc h.is_disc.isOArc_discBd h.bd_sub
  have h3 := three_le_ncard_bd h hbd hin
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y, x ∈ discBd W ∩ D.P.Γ.hatV cap ∧ y ∈ discBd W ∩ D.P.Γ.hatV cap
    ∧ x ≠ y := by
    have : 1 < (discBd W ∩ D.P.Γ.hatV cap).ncard := by omega
    obtain ⟨x, hx, y, hy, hne⟩ := (one_lt_ncard (D.P.Γ.finite_V.image _ |>.subset
      inter_subset_right)).mp this
    exact ⟨x, y, hx, hy, hne⟩
  have hV : ∀ {z}, z ∈ discBd W ∩ D.P.Γ.hatV cap → z ∈ F.V := fun hz ↦ mem_V_of_mem_U hFs
    (hFU ▸ hz.1) (D.rad.isPreRadial.2.1 hz.2)
  have hrF : r ∈ F.V := mem_V_of_mem_U hFs (hFU ▸ hrb) hr.1
  have hxr : r ≠ x := fun e ↦ hr.2 (e ▸ hx.2)
  have hyr : r ≠ y := fun e ↦ hr.2 (e ▸ hy.2)
  obtain ⟨P, Q, hP, hQ, hPs, hQs, hP0, hQ0, hPQ, -, hsup⟩ := Drawing.IsCircuit.exists_two_paths hFc
    hrF (hV hx) hxr
  obtain ⟨f₁, v₁, hl₁, hf₁, hv₁, hne₁, hend₁, huq₁⟩ := exists_first_edge hFs hPs hP hP0 hr.1
  obtain ⟨f₂, v₂, hl₂, hf₂, hv₂, hne₂, hend₂, huq₂⟩ := exists_first_edge hFs hQs hQ hQ0 hr.1
  have hsubU : ∀ {f}, f ∈ F.E → f ⊆ discBd W := fun hf ↦ by
    rw [← hFU]
    exact fun z hz ↦ F.closure_subset_U hf (subset_closure hz)
  refine ⟨f₁, f₂, v₁, v₂, ?_, hl₁, hl₂, hsubU (hPs.2 hf₁), hsubU (hQs.2 hf₂), ?_⟩
  swap
  · intro f hf hfb hrf
    have hfF : f ∈ F.E := by
      by_contra hn
      obtain ⟨z, hz⟩ := hf.1
      exact disjoint_left.mp (edge_disjoint_U hFs hf hn) hz (hFU ▸ hfb hz)
    have hEF : f ∈ (F.sup P Q).E := by rw [hsup]; exact hfF
    rw [Drawing.sup_E hPs hQs] at hEF
    rcases hEF with h' | h'
    · exact .inl (huq₁ f h' hrf)
    · exact .inr (huq₂ f h' hrf)
  rintro rfl
  have hv : v₁ ∈ P.V ∩ Q.V := ⟨hv₁, hv₂⟩
  rw [hPQ] at hv
  have hvx : v₁ = x := hv.resolve_left hne₁
  have hyF : y ∈ (F.sup P Q).V := by rw [hsup]; exact hV hy
  rw [Drawing.sup_V hPs hQs] at hyF
  rcases hyF with h₁ | h₁
  · rcases hend₁ hvx y h₁ with e | e
    · exact hyr e.symm
    · exact hxy e.symm
  · rcases hend₂ hvx y h₁ with e | e
    · exact hyr e.symm
    · exact hxy e.symm

end TangleDatum

end GraphMinor.GM19
