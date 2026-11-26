/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CylinderWheel
public import LeanPool.GraphMinor.GM09.PlanarNests
public import LeanPool.GraphMinor.GM11.Section6

/-!
# Trimming the paths back to the cylinder

The uncrossing gives paths between the two circles of the wheels (`CylinderWheel`). Each meets a
circle in a path, so what lies before its last vertex on the first circle and after its
next vertex on the second lies on the circles. The part between has a spoke at each end, and without
these spokes it is a path of the original drawing. It meets each circuit of the nest
exactly as the long path does (`exists_trimmed_path`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM09.PlanarNests

variable {T : Type} [TopologicalSpace T] [T2Space T]

section Walks

variable {α β : Type*} {G : Graph α β}

theorem walk_append_assoc {a b c d : α} (X : GraphWalk G a b) (Y : GraphWalk G b c)
  (Z : GraphWalk G c d) :
    (X.append Y).append Z = X.append (Y.append Z) := by
  induction X with
  | nil h => rfl
  | cons h r ih => simp [GraphWalk.append, ih]

/-- Cut a walk at its last vertex in `X`. -/
theorem exists_last_hit_split {a b : α} (W : GraphWalk G a b) {X : Set α}
  (hne : ∃ x ∈ W.support, x ∈ X) :
    ∃ v ∈ X, ∃ (W₁ : GraphWalk G a v) (W₂ : GraphWalk G v b), W = W₁.append W₂
      ∧ ∀ x ∈ W₂.support, x ∈ X → x = v := by
  induction W with
  | @nil a h =>
    obtain ⟨x, hx, hxX⟩ := hne
    have hxa : x = a := List.mem_singleton.mp hx
    exact ⟨a, hxa ▸ hxX, .nil h, .nil h, rfl, fun y hy _ => List.mem_singleton.mp hy⟩
  | @cons a y b e h r ih =>
    by_cases hr : ∃ x ∈ r.support, x ∈ X
    · obtain ⟨v, hv, W₁, W₂, rfl, h2⟩ := ih hr
      exact ⟨v, hv, .cons h W₁, W₂, rfl, h2⟩
    · obtain ⟨x, hx, hxX⟩ := hne
      rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨x, hxX, .nil h.left_mem, .cons h r, rfl, fun z hz hzX => ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · rfl
        · exact (hr ⟨z, hz, hzX⟩).elim
      · exact (hr ⟨x, hx, hxX⟩).elim

/-- The first edge of a walk. -/
theorem exists_cons_of_ne {a b : α} (W : GraphWalk G a b) (hab : a ≠ b) : ∃ (c : α) (e : β)
  (h : G.IsLink e a c) (W₀ : GraphWalk G c b), W = .cons h W₀ := by
  cases W with
  | nil _ => exact absurd rfl hab
  | cons h r => exact ⟨_, _, h, r, rfl⟩

/-- The last edge of a walk. -/
theorem exists_snoc {a b : α} (W : GraphWalk G a b) (hab : 0 < W.length) :
    ∃ (c : α) (e : β) (W₀ : GraphWalk G a c) (h : G.IsLink e c b), W = W₀.append (.cons h
      (.nil h.right_mem)) := by
  induction W with
  | nil _ => simp at hab
  | @cons a y b e h r ih =>
    by_cases hy : 0 < r.length
    · obtain ⟨c, e', W₀, h', rfl⟩ := ih hy
      exact ⟨c, e', .cons h W₀, h', rfl⟩
    · cases r with
      | nil _ => exact ⟨a, e, .nil h.left_mem, h, rfl⟩
      | cons _ _ => simp at hy

/-- All edges of a walk with vertices in `X`. -/
theorem edges_of_support {a b : α} (W : GraphWalk G a b) {X : Set α} {F : Set β}
  (hX : ∀ x ∈ W.support, x ∈ X) (h : ∀ e x y, G.IsLink e x y → x ∈ X → y ∈ X
    → e ∈ F) : ∀ e ∈ W.edges, e ∈ F := by
  induction W with
  | nil _ => simp
  | cons hl r ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h _ _ _ hl (hX _ (by simp)) (hX _ (by simp [r.start_mem_support]))
    · exact ih (fun x hx => hX x (by simp [hx])) e he

end Walks

/-- If a connected part `D` of a simple walk has a vertex on each side of `w`, it holds `w`. -/
theorem mem_of_sides {P D : Drawing T} {a w b : T} (A : GraphWalk P.toGraph a w)
  (R : GraphWalk P.toGraph w b) (hs : (A.append R).IsSimple) (hV : P.V = {x | x ∈
    (A.append R).support})
    (hE : P.E = {e | e ∈ (A.append R).edges}) (hD : D.IsSubdrawing P)
      (hc : IsPreconnected D.U) {x y : T} (hx : x ∈ A.support) (hxD : x ∈ D.U) (hy : y ∈ R.support)
        (hyD : y ∈ D.U) : w ∈ D.V := by
  let X := walkDrawing P A
  let Y := walkDrawing P R
  have hxX : x ∈ X.U := (mem_walkDrawing_U P A).mpr (.inl hx)
  have hyY : y ∈ Y.U := (mem_walkDrawing_U P R).mpr (.inl hy)
  have hcov : D.U ⊆ X.U ∪ Y.U := fun z hz => by
    have hzP := hD.U_subset hz
    rw [P.U_eq] at hzP
    rcases hzP with h | h
    · rw [hV] at h
      rcases (GraphWalk.mem_support_append A R).mp h with h | h
      · exact .inl ((mem_walkDrawing_U P A).mpr (.inl h))
      · exact .inr ((mem_walkDrawing_U P R).mpr (.inl h))
    · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp h
      rw [hE] at he
      have he' : e ∈ (A.append R).edges := he
      rw [GraphWalk.edges_append, List.mem_append] at he'
      rcases he' with h | h
      · exact .inl ((mem_walkDrawing_U P A).mpr (.inr ⟨e, h, hze⟩))
      · exact .inr ((mem_walkDrawing_U P R).mpr (.inr ⟨e, h, hze⟩))
  obtain ⟨z, hzD, hzX, hzY⟩ := isPreconnected_closed_iff.mp hc X.U Y.U X.isClosed_U Y.isClosed_U
    hcov ⟨x, hxD, hxX⟩ ⟨y, hyD, hyY⟩
  have hnd : (A.edges ++ R.edges).Nodup := by
    rw [← GraphWalk.edges_append]
    exact hs.edges_nodup
  have hdE : Disjoint X.E Y.E := by
    rw [walkDrawing_E, walkDrawing_E]
    exact disjoint_left.mpr fun e h1 h2 => (List.nodup_append.mp hnd).2.2 e h1 e h2 rfl
  have hin := U_inter_of_disjoint (walkDrawing_isSubdrawing P A) (walkDrawing_isSubdrawing P R) hdE
  have hz : z ∈ X.V ∩ Y.V := by
    rw [← hin]
    exact ⟨hzX, hzY⟩
  have hzA : z ∈ A.support := by
    have := hz.1
    rwa [walkDrawing_V] at this
  have hzR : z ∈ R.support := by
    have := hz.2
    rwa [walkDrawing_V] at this
  have hnd2 : (A.support ++ R.support.tail).Nodup := by
    rw [← GraphWalk.support_append]
    exact hs
  have hzw : z = w := by
    rw [R.support_eq_cons] at hzR
    rcases List.mem_cons.mp hzR with h | h
    · exact h
    · exact ((List.nodup_append.mp hnd2).2.2 z hzA z h rfl).elim
  subst hzw
  by_contra hn
  obtain ⟨e, he, hze⟩ := D.exists_edge_of_mem hzD hn
  have hwV : z ∈ P.V := A.mem_vertexSet_of_mem_support hzA
  exact (hD.2 he).2.1 hze |>.2 hwV

variable {Γ H C₁ C₂ : Drawing T} {D₁ D₂ E₁ E₂ : Set T} {q : T → T} {ℓ : T → Set T}

omit [T2Space T] in
theorem IsWheeled.swap (w : IsWheeled Γ H C₁ C₂ D₁ D₂ E₁ E₂ q ℓ) : IsWheeled Γ H C₂ C₁ D₂ D₁ E₂ E₁
  q ℓ where
  sub := w.sub
  sub₁ := w.sub₂
  sub₂ := w.sub₁
  circ₁ := w.circ₂
  circ₂ := w.circ₁
  disc₁ := w.disc₂
  disc₂ := w.disc₁
  in₁ := w.in₂
  in₂ := w.in₁
  bd₁ := w.bd₂
  bd₂ := w.bd₁
  V := by rw [w.V, union_right_comm]
  U := by rw [w.U, union_right_comm Γ.U, union_comm D₂ D₁]
  E := fun e he => by
    rw [union_comm D₂ D₁]
    rcases w.E e he with h | h | h | h
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr h))
  q₁ := w.q₂
  q₂ := w.q₁
  line := by
    rw [union_comm D₂ D₁]
    exact w.line
  cap₁ := w.cap₂
  cap₂ := w.cap₁
  disj := by
    rw [union_comm D₂ D₁]
    exact w.disj

theorem IsWheeled.ends (w : IsWheeled Γ H C₁ C₂ D₁ D₂ E₁ E₂ q ℓ) {x : T} (hx : x ∈ Γ.V ∩
  (D₁ ∪ D₂)) : closure (ℓ x \ {x, q x}) = ℓ x ∧ x ∈ ℓ x ∧ q x ∈ ℓ x ∧ x ∈ H.V ∧ q x ∈ C₁.V ∪ C₂.V
    ∧ q x ∈ H.V := by
  obtain ⟨hl, -, -⟩ := w.line x hx
  have hq : q x ∈ C₁.V ∪ C₂.V := by
    obtain ⟨hV, h | h⟩ := hx
    · exact .inl (w.q₁ x ⟨hV, h⟩)
    · exact .inr (w.q₂ x ⟨hV, h⟩)
  refine ⟨closure_sdiff_pair hl, hl.left_mem, hl.right_mem, w.sub.1 hx.1, hq, ?_⟩
  rcases hq with h | h
  · exact w.sub₁.1 h
  · exact w.sub₂.1 h

/-- An edge between two vertices of `Γ` is an edge of `Γ`, since the circles and the spokes have
ends on the circles. -/
theorem IsWheeled.mem_E_of_link (w : IsWheeled Γ H C₁ C₂ D₁ D₂ E₁ E₂ q ℓ) (hΓ₁ : Disjoint Γ.V C₁.V)
  (hΓ₂ : Disjoint Γ.V C₂.V) {e : Set T} {y z : T} (hl : H.toGraph.IsLink e y z) (hy : y ∈ Γ.V)
    (hz : z ∈ Γ.V) : e ∈ Γ.E := by
  have hcap := hl.2.2.2
  have hyc : y ∈ closure e ∩ H.V := by rw [hcap]; simp
  rcases w.E e hl.1 with h | h | h | ⟨x, hx, rfl⟩
  · exact h
  · have : y ∈ closure e ∩ C₁.V := by rw [w.sub₁.closure_inter_V h]; exact hyc
    exact absurd this.2 (disjoint_left.mp hΓ₁ hy)
  · have : y ∈ closure e ∩ C₂.V := by rw [w.sub₂.closure_inter_V h]; exact hyc
    exact absurd this.2 (disjoint_left.mp hΓ₂ hy)
  · obtain ⟨h1, -, h3, -, h5, h6⟩ := w.ends hx
    have h7 : q x ∈ closure (ℓ x \ {x, q x}) ∩ H.V := ⟨by rw [h1]; exact h3, h6⟩
    rw [hcap] at h7
    have h8 : q x ∈ Γ.V := by
      rcases h7 with h | h
      · exact h ▸ hy
      · exact (mem_singleton_iff.mp h) ▸ hz
    rcases h5 with h | h
    · exact absurd h (disjoint_left.mp hΓ₁ h8)
    · exact absurd h (disjoint_left.mp hΓ₂ h8)

/-- An edge that leaves the first circle is a spoke, so it goes to a vertex of `Γ` on `D₁`. -/
theorem IsWheeled.mem_of_link_off (w : IsWheeled Γ H C₁ C₂ D₁ D₂ E₁ E₂ q ℓ)
  (hΓ₁ : Disjoint Γ.V C₁.V) (h12 : Disjoint C₁.V C₂.V) {e : Set T} {y z : T}
    (hl : H.toGraph.IsLink e y z) (hy : y ∈ C₁.V) (hz : z ∉ C₁.V) : z ∈ Γ.V ∩ D₁ := by
  have hcap := hl.2.2.2
  have hyc : y ∈ closure e ∩ H.V := by rw [hcap]; simp
  have hzc : z ∈ closure e ∩ H.V := by rw [hcap]; simp
  rcases w.E e hl.1 with h | h | h | ⟨x, hx, rfl⟩
  · have : y ∈ closure e ∩ Γ.V := by rw [w.sub.closure_inter_V h]; exact hyc
    exact absurd hy (disjoint_left.mp hΓ₁ this.2)
  · have : z ∈ closure e ∩ C₁.V := by rw [w.sub₁.closure_inter_V h]; exact hzc
    exact absurd this.2 hz
  · have : y ∈ closure e ∩ C₂.V := by rw [w.sub₂.closure_inter_V h]; exact hyc
    exact absurd this.2 (disjoint_left.mp h12 hy)
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := w.ends hx
    have h7 : x ∈ closure (ℓ x \ {x, q x}) ∩ H.V := ⟨by rw [h1]; exact h2, h4⟩
    have h8 : q x ∈ closure (ℓ x \ {x, q x}) ∩ H.V := ⟨by rw [h1]; exact h3, h6⟩
    rw [hcap] at h7 h8
    have hne := (w.line x hx).2.1
    have hxz : x = z := by
      rcases h7 with h | h
      · exact absurd hy (h ▸ disjoint_left.mp hΓ₁ hx.1)
      · exact h
    subst hxz
    have hqy : q x = y := by
      rcases h8 with h | h
      · exact h
      · exact absurd (mem_singleton_iff.mp h).symm hne
    obtain ⟨hV, h | h⟩ := hx
    · exact ⟨hV, h⟩
    · exact absurd (w.q₂ x ⟨hV, h⟩) (hqy ▸ disjoint_left.mp h12 hy)

/-- **Trimming a path of `H` to a path of `Γ`.** -/
theorem exists_trimmed_path (w : IsWheeled Γ H C₁ C₂ D₁ D₂ E₁ E₂ q ℓ) (hΓ₁ : Disjoint Γ.V C₁.V)
  (hΓ₂ : Disjoint Γ.V C₂.V) (h12 : Disjoint C₁.V C₂.V) {Pl : Drawing T} {a b : T}
    (hs : Pl.IsSubdrawing H)
    (ha : a ∈ C₁.V) (hb : b ∈ C₂.V) (hP : Pl.IsPathBetween a b) (h1 : IsPreconnected
      (Drawing.inf H C₁ Pl).U) (h2 : IsPreconnected (Drawing.inf H C₂ Pl).U) :
    ∃ (P : Drawing T) (u v : T), P.IsSubdrawing Γ ∧ P.IsSubdrawing Pl ∧ u ∈ D₁ ∧ v ∈ D₂
      ∧ P.IsPathBetween u v ∧
      ∀ B : Drawing T, B.IsSubdrawing H → Disjoint B.V C₁.V → Disjoint B.V C₂.V → B.V ∩ Pl.V ⊆ P.V
        ∧ B.E ∩ Pl.E ⊆ P.E := by
  obtain ⟨W, hW, hV, hE⟩ := hP
  obtain ⟨c, hc, A, R, hWeq, hR⟩ := exists_last_hit_split W ⟨a, W.start_mem_support, ha⟩
  obtain ⟨d, hd, M, Z, hReq, hM⟩ := GM09.PlanarNests.exists_first_hit_split R ⟨b,
    R.end_mem_support, hb⟩
  subst hWeq
  subst hReq
  obtain ⟨hAs, hRs⟩ := GM09.isSimple_of_append hW
  obtain ⟨hMs, hZs⟩ := GM09.isSimple_of_append hRs
  have hcd : c ≠ d := fun h => disjoint_left.mp h12 hc (h ▸ hd)
  obtain ⟨x, e₁, h₁, M', hMeq⟩ := exists_cons_of_ne M hcd
  have hPlH : ∀ {e y z}, Pl.toGraph.IsLink e y z → H.toGraph.IsLink e y z := fun {e y z} hl =>
    (hs.isLink_iff hl.1).mp hl
  -- the first edge of `M` is a spoke
  have hcM : c ∉ M'.support := by
    have := hMs
    rw [hMeq] at this
    exact (List.nodup_cons.mp this).1
  have hxC : x ∉ C₁.V := fun h => hcM (by
    have hM : x ∈ M.support := by
      rw [hMeq]
      exact List.mem_cons_of_mem _ M'.start_mem_support
    have h3 : x = c := hR x ((GraphWalk.mem_support_append M Z).mpr (.inl hM)) h
    exact h3 ▸ M'.start_mem_support)
  have hx := w.mem_of_link_off hΓ₁ h12 (hPlH h₁) hc hxC
  have hxd : x ≠ d := fun h => disjoint_left.mp hΓ₂ hx.1 (h ▸ hd)
  have hlen : 0 < M'.length := by
    by_contra hn
    exact hxd (GraphWalk.eq_of_length_eq_zero (W := M') (by omega))
  obtain ⟨y, e₂, M₀, h₂', hM'eq⟩ := exists_snoc M' hlen
  have hM's : M'.IsSimple := by
    have := hMs
    rw [hMeq] at this
    exact GraphWalk.IsSimple.of_cons this
  have hM₀s : M₀.IsSimple := (GM09.isSimple_of_append (hM'eq ▸ hM's)).1
  have hdM₀ : d ∉ M₀.support := by
    have := hM's
    rw [hM'eq] at this
    have h3 : (M₀.support ++ [d]).Nodup := by
      have h4 := this
      unfold GraphWalk.IsSimple at h4
      rw [GraphWalk.support_append] at h4
      exact h4
    exact fun h => (List.nodup_append.mp h3).2.2 d h d (by simp) rfl
  have hM₀M : ∀ z ∈ M₀.support, z ∈ M.support := fun z hz => by
    rw [hMeq]
    refine List.mem_cons_of_mem _ ?_
    rw [hM'eq]
    exact (GraphWalk.mem_support_append _ _).mpr (.inl hz)
  have hyC : y ∉ C₂.V := fun h => hdM₀ (by
    have h3 := hM y (hM₀M y M₀.end_mem_support) h
    exact h3 ▸ M₀.end_mem_support)
  have hy := w.swap.mem_of_link_off hΓ₂ h12.symm (hPlH h₂').symm hd hyC
  have hdCc : ∀ {z}, z ∈ M₀.support → z ≠ c := fun {z} hz h => hcM (by
    rw [hM'eq]
    exact (GraphWalk.mem_support_append _ _).mpr (.inl (h ▸ hz)))
  have hM₀Γ : ∀ z ∈ M₀.support, z ∈ Γ.V := fun z hz => by
    have hzW : z ∈ (A.append (M.append Z)).support := (GraphWalk.mem_support_append _ _).mpr (.inr
      ((GraphWalk.mem_support_append _ _).mpr (.inl (hM₀M z hz))))
    have hzH : z ∈ H.V := hs.1 (hV ▸ hzW)
    rw [w.V] at hzH
    rcases hzH with (h | h) | h
    · exact h
    · exact absurd (hR z ((GraphWalk.mem_support_append M Z).mpr (.inl (hM₀M z hz))) h) (hdCc hz)
    · have := hM z (hM₀M z hz) h
      exact absurd (this ▸ hz) hdM₀
  have hM₀E : ∀ e ∈ M₀.edges, e ∈ Γ.E := edges_of_support M₀ hM₀Γ fun e y z hl hy hz
    => w.mem_E_of_link hΓ₁ hΓ₂ (hPlH hl) hy hz
  have hMsub : ∀ z ∈ M.support, z = c ∨ z ∈ M₀.support ∨ z = d := fun z hz => by
    rw [hMeq] at hz
    rcases List.mem_cons.mp hz with h | h
    · exact .inl h
    · rw [hM'eq] at h
      rcases (GraphWalk.mem_support_append _ _).mp h with h | h
      · exact .inr (.inl h)
      · rcases List.mem_cons.mp h with h | h
        · exact .inr (.inl (h ▸ M₀.end_mem_support))
        · exact .inr (.inr (by simpa using h))
  have hMed : ∀ e ∈ M.edges, e = e₁ ∨ e ∈ M₀.edges ∨ e = e₂ := fun e he => by
    rw [hMeq] at he
    rcases List.mem_cons.mp he with h | h
    · exact .inl h
    · rw [hM'eq, GraphWalk.edges_append] at h
      rcases List.mem_append.mp h with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr (by simpa using h))
  have haPl : a ∈ Pl.V := by rw [hV]; exact GraphWalk.start_mem_support _
  have hbPl : b ∈ Pl.V := by rw [hV]; exact GraphWalk.end_mem_support _
  have hcPl : c ∈ Pl.V := by
    rw [hV]
    exact (GraphWalk.mem_support_append _ _).mpr (.inr ((GraphWalk.mem_support_append _ _).mpr
      (.inl M.start_mem_support)))
  have hdPl : d ∈ Pl.V := by
    rw [hV]
    exact (GraphWalk.mem_support_append _ _).mpr (.inr ((GraphWalk.mem_support_append _ _).mpr
      (.inl M.end_mem_support)))
  have hDA := Drawing.inf_isSubdrawing_right w.sub₁ hs
  have hDZ := Drawing.inf_isSubdrawing_right w.sub₂ hs
  have hmemV : ∀ {C : Drawing T}, C.IsSubdrawing H → ∀ {z}, z ∈ C.V → z ∈ Pl.V → z ∈
    (Drawing.inf H C Pl).U := fun {C} hC {z} h3 h4 =>
    (Drawing.inf H C Pl).V_subset_U (by rw [Drawing.inf_V hC hs]; exact ⟨h3, h4⟩)
  have hAin : ∀ z ∈ A.support, z ∈ C₁.V := fun z hz => by
    obtain ⟨A₁, A₂, rfl⟩ := GraphWalk.exists_append_of_mem A hz
    have hass := walk_append_assoc A₁ A₂ (M.append Z)
    rw [hass] at hV hE hW
    have := mem_of_sides A₁ (A₂.append (M.append Z)) hW hV hE hDA h1 (x := a) (y
      := c) A₁.start_mem_support (hmemV w.sub₁ ha haPl)
      ((GraphWalk.mem_support_append _ _).mpr (.inr ((GraphWalk.mem_support_append _ _).mpr
        (.inl M.start_mem_support)))) (hmemV w.sub₁ hc hcPl)
    rw [Drawing.inf_V w.sub₁ hs] at this
    exact this.1
  have hZin : ∀ z ∈ Z.support, z ∈ C₂.V := fun z hz => by
    obtain ⟨Z₁, Z₂, rfl⟩ := GraphWalk.exists_append_of_mem Z hz
    rw [← walk_append_assoc M Z₁ Z₂, ← walk_append_assoc A (M.append Z₁) Z₂] at hV hE hW
    have := mem_of_sides (A.append (M.append Z₁)) Z₂ hW hV hE hDZ h2 (x := d) (y := b)
      ((GraphWalk.mem_support_append _ _).mpr (.inr ((GraphWalk.mem_support_append _ _).mpr
        (.inl M.end_mem_support)))) (hmemV w.sub₂ hd hdPl) Z₂.end_mem_support (hmemV w.sub₂ hb hbPl)
    rw [Drawing.inf_V w.sub₂ hs] at this
    exact this.1
  refine ⟨walkDrawing Pl M₀, x, y, ⟨?_, ?_⟩, walkDrawing_isSubdrawing Pl M₀, hx.2, hy.2,
    walkDrawing_isPathBetween Pl hM₀s, fun B hB hB₁ hB₂ => ⟨?_, ?_⟩⟩
  · rw [walkDrawing_V]
    exact hM₀Γ
  · rw [walkDrawing_E]
    exact hM₀E
  · rintro z ⟨hzB, hzP⟩
    rw [walkDrawing_V]
    rw [hV] at hzP
    rcases (GraphWalk.mem_support_append _ _).mp hzP with h | h
    · exact absurd (hAin z h) (disjoint_left.mp hB₁ hzB)
    · rcases (GraphWalk.mem_support_append _ _).mp h with h | h
      · rcases hMsub z h with rfl | h | rfl
        · exact absurd hc (disjoint_left.mp hB₁ hzB)
        · exact h
        · exact absurd hd (disjoint_left.mp hB₂ hzB)
      · exact absurd (hZin z h) (disjoint_left.mp hB₂ hzB)
  · rintro e ⟨heB, heP⟩
    have hend : ∀ z, z ∈ closure e → z ∈ H.V → z ∈ B.V := fun z h3 h4 => by
      have : z ∈ closure e ∩ B.V := by rw [hB.closure_inter_V heB]; exact ⟨h3, h4⟩
      exact this.2
    obtain ⟨l, m, hlm⟩ := (Pl.toGraph.edge_mem_iff_exists_isLink e).mp heP
    have hlc : l ∈ closure e := by
      have : l ∈ closure e ∩ Pl.V := by rw [hlm.2.2.2]; simp
      exact this.1
    have hlH : l ∈ H.V := hs.1 hlm.2.1
    rw [walkDrawing_E]
    have heW : e ∈ (A.append (M.append Z)).edges := by rw [hE] at heP; exact heP
    rw [GraphWalk.edges_append, GraphWalk.edges_append, List.mem_append, List.mem_append] at heW
    rcases heW with h | h | h
    · have := hAin l (GraphWalk.left_mem_support_of_mem_edges A h hlm)
      exact absurd this (disjoint_left.mp hB₁ (hend l hlc hlH))
    · rcases hMed e h with rfl | h | rfl
      · have h3 : c ∈ closure e ∩ Pl.V := by rw [h₁.2.2.2]; simp
        exact absurd hc (disjoint_left.mp hB₁ (hend c h3.1 (hs.1 h3.2)))
      · exact h
      · have h3 : d ∈ closure e ∩ Pl.V := by rw [h₂'.2.2.2]; simp
        exact absurd hd (disjoint_left.mp hB₂ (hend d h3.1 (hs.1 h3.2)))
    · have := hZin l (GraphWalk.left_mem_support_of_mem_edges Z h hlm)
      exact absurd this (disjoint_left.mp hB₂ (hend l hlc hlH))

end GraphMinor.GM07
