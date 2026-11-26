/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13n

/-!
# Graph Minors XIX, Section 13: step (6) of (13.6)

If `ins(H) ∩ Δ ⊆ U(C)` then `C = D_v`, and so the theorem holds. We count edges along `C`, and then
we compare weights.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat}

omit [T2Space Shat] in
/-- A vertex of `Γ*` on `U(C)` is a vertex of `C`. -/
theorem mem_V_of_mem_U {G C : Drawing Shat} (hC : C.IsSubdrawing G) {x : Shat} (hx : x ∈ C.U)
  (hxG : x ∈ G.V) : x ∈ C.V := by
  by_contra hn
  obtain ⟨g, hg, hxg⟩ := C.exists_edge_of_mem hx hn
  exact ((hC.2 hg).2.1 hxg).2 hxG

namespace IsRound

variable (hr : D.IsRound W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ)
include hr

omit [T2Space S] in
/-- A walk from `Δ` that ends at a vertex outside `Δ \ U(C)` meets `C`. -/
theorem exists_mem_C {a b : Shat} (T : GraphWalk D.rad.G.toGraph a b) (ha : a ∈ Δ) (hb : b ∈ Δ
  → b ∈ C.U) : ∃ x ∈ T.support, x ∈ C.V := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hC := hr.circuit
  have hbG : b ∈ D.rad.G.V := T.mem_vertexSet_of_mem_support T.end_mem_support
  by_contra hn
  push Not at hn
  have key : ∀ {a b : Shat} (T : GraphWalk D.rad.G.toGraph a b), (∀ x ∈ T.support, x ∉ C.V) → a ∈ Δ
    → b ∈ Δ := by
    intro a b T
    induction T with
    | nil _ => exact fun _ h ↦ h
    | @cons a y b e hl L ih =>
      intro hoff ha
      refine ih (fun x hx ↦ hoff x (by simp [hx])) ?_
      have heC : e ∉ C.E := fun he ↦ hoff a (by simp) (Drawing.IsLink.mem_V_of_sub hC.1 hl he).1
      have haU : a ∉ C.U := fun h' ↦ hoff a (by simp) (mem_V_of_mem_U hC.1 h' hl.2.1)
      have hai : a ∈ discInt Δ := ⟨ha, fun h' ↦ haU (hr.bd ▸ h')⟩
      rcases edge_inside_or_off hT hC.1 hr.disc hr.bd hl.1 heC with h₁ | h₁
      · exact closure_minimal (h₁.trans (discInt_subset _)) hr.disc.isClosed
          (IsLink.right_mem_closure hl)
      · obtain ⟨z, hzi, hze⟩ := mem_closure_iff.mp (IsLink.left_mem_closure hl) _
          (hr.disc.isOpen_discInt hman) hai
        exact absurd hzi.1 (disjoint_left.mp h₁ hze)
  have hbΔ := key T hn ha
  exact hn b T.end_mem_support (mem_V_of_mem_U hC.1 (hb hbΔ) hbG)

omit [T2Space S] in
/-- Once `D_v` is in `C`, the theorem holds. -/
theorem ins_of_E (hE : Dv.E ⊆ C.E) : D.ins F ⊆ Δv := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hC := hr.circuit
  have hDv := hr.enc.sector.Dv_circuit
  have heq := circuit_E_eq_of_subset hC.2 hDv.2 hC.1 hDv.1 hE
  obtain rfl := circuit_eq_of_E hDv.2 hC.2 hDv.1 hC.1 heq
  have hΔ : Δv = Δ := disc_eq_of_subset_disc hT hr.amb.disc hr.enc.sector.is_disc hr.disc
    (hr.v_sub.trans hr.sub) hr.sub
    (hr.enc.sector.Dv_U.symm.trans hr.bd.symm)
  rw [hΔ]
  exact hr.F_sub

end IsRound

omit [T2Space S] in
/-- If `M` has two edges and its ends are vertices of `Γ` on `bd(W)`, then its middle vertex is in
`W`. -/
theorem IsOuterPath.not_two (hW : D.IsWheelHubOfRadius W H ρ) {C : Drawing Shat} {a b : Shat} {M :
  GraphWalk D.rad.G.toGraph a b} {Q : GraphWalk D.rad.G.toGraph b a}
    (ho : D.IsOuterPath W C M Q) (hlen : M.length = 2) (ha : a ∈ D.P.Γ.hatV cap)
      (hb : b ∈ D.P.Γ.hatV cap) (hin : ∀ x ∈ M.support, x ∈ W → x = a ∨ x = b) : False := by
  have hs := ho.splits.s₁
  cases M with
  | nil _ => simp [GraphWalk.length] at hlen
  | @cons _ y _ g hl L =>
    cases L with
    | nil _ => simp [GraphWalk.length] at hlen
    | @cons _ y' _ g' hl' L' =>
      cases L' with
      | @cons _ _ _ _ _ _ => simp [GraphWalk.length] at hlen
      | nil _ =>
        have hnd : ([a, y, b] : List Shat).Nodup := hs
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true] at hnd
        have hyW : y ∈ W := hW.two_nbrs_in_W y hl.2.2.1 a ⟨ha, ho.a_bd⟩ b ⟨hb, ho.b_bd⟩ ho.ne ⟨g,
          hl.1, by
          rw [← closure_inter_V_eq_tilde hl.1, hl.2.2.2, pair_comm]⟩ ⟨g', hl'.1,
            by rw [← closure_inter_V_eq_tilde hl'.1, hl'.2.2.2]⟩
        rcases hin y (by simp) hyW with h' | h'
        · exact hnd.1.1 h'.symm
        · exact hnd.2.1 h'

omit [T2Space Shat] in
/-- A simple walk `K` between two vertices of a simple walk `Q`, with all its edges in `Q`, is a
piece of `Q`. -/
theorem GraphWalk.eq_piece {G : Drawing Shat} {a b x y : Shat} (A : GraphWalk G.toGraph a x)
  (K' : GraphWalk G.toGraph x y) (B : GraphWalk G.toGraph y b)
    (hQ : (A.append (K'.append B)).IsSimple) (K : GraphWalk G.toGraph x y) (hK : K.IsSimple)
      (hE : ∀ e ∈ K.edges, e ∈ (A.append (K'.append B)).edges) : K' = K := by
  have hs₂ := (isSimple_of_append hQ).2
  have hK's := (isSimple_of_append hs₂).1
  have hnd := hQ
  unfold GraphWalk.IsSimple at hnd
  rw [GraphWalk.support_append, List.nodup_append] at hnd
  have hnd₂ := hs₂
  unfold GraphWalk.IsSimple at hnd₂
  rw [GraphWalk.support_append, List.nodup_append] at hnd₂
  have hmem : ∀ z, z ∈ (K'.append B).support → z ∈ A.support → z = x := by
    intro z h₁ h₂
    by_contra hn
    have h₃ : z ∈ (K'.append B).support.tail := by
      obtain ⟨l, hl⟩ : ∃ l, (K'.append B).support = x :: l := by
        cases h : K' with
        | nil _ =>
          cases B with
          | nil _ => exact ⟨_, rfl⟩
          | cons _ _ => exact ⟨_, rfl⟩
        | cons _ _ => exact ⟨_, rfl⟩
      rw [hl] at h₁ ⊢
      exact (List.mem_cons.mp h₁).resolve_left hn
    exact hnd.2.2 _ h₂ _ h₃ rfl
  have hmem₂ : ∀ z, z ∈ K'.support → z ∈ B.support → z = y := by
    intro z h₁ h₂
    by_contra hn
    have h₃ : z ∈ B.support.tail := by
      obtain ⟨l, hl⟩ : ∃ l, B.support = y :: l := by
        cases B with
        | nil _ => exact ⟨_, rfl⟩
        | cons _ _ => exact ⟨_, rfl⟩
      rw [hl] at h₂ ⊢
      exact (List.mem_cons.mp h₂).resolve_left hn
    exact hnd₂.2.2 _ h₁ _ h₃ rfl
  have h₁ : ∀ e ∈ K.reverse.edges, e ∈ (K'.append B).edges := walk_stays K.reverse hK.reverse
    (K'.append B) A
    (fun e he ↦ by
      have h := hE e (by simpa [GraphWalk.edges_reverse] using he)
      rw [GraphWalk.edges_append, List.mem_append] at h
      exact h.symm)
    (fun z _ h₁ h₂ ↦ hmem z h₁ h₂) ((GraphWalk.mem_support_append _ _).mpr
      (.inl K'.end_mem_support))
    (fun {e x y} hl he _ ↦ (K'.append B).left_mem_support_of_mem_edges he (IsLink.symm' hl))
    (fun {e x y} hl he ↦ A.left_mem_support_of_mem_edges he hl)
  have h₂ : ∀ e ∈ K.edges, e ∈ K'.edges := walk_stays K hK K' B
    (fun e he ↦ by
      have h := h₁ e (by simpa [GraphWalk.edges_reverse] using he)
      rwa [GraphWalk.edges_append, List.mem_append] at h)
    (fun z _ h₁ h₂ ↦ hmem₂ z h₁ h₂) K'.start_mem_support
    (fun {e x y} hl he _ ↦ K'.left_mem_support_of_mem_edges he (IsLink.symm' hl))
    (fun {e x y} hl he ↦ B.left_mem_support_of_mem_edges he hl)
  exact simple_walk_unique K' K hK's hK h₂

/-- **Step (6) of the proof of (13.6) when the spokes meet.** -/
theorem IsRound.step_six_fan (hr : D.IsRound W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ) {v₁ v₂ u h : Shat} {f₁
  f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ u}
    {A₂ : GraphWalk D.rad.G.toGraph v₂ u} {T : GraphWalk D.rad.G.toGraph u h}
      (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hc : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv)
    (hb₁ : f₁ ⊆ discBd W) (hb₂ : f₂ ⊆ discBd W) (hh : h ∈ Δ → h ∈ C.U) : D.ins F ⊆ Δv := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hW := hr.enc.wheel
  have hbdS := hr.enc.hbdS
  have hin := hr.enc.hin
  have hCc := hr.circuit
  have h1 := hf.spoke₁
  have h2 := hf.spoke₂
  have hDvΔ : Dv.U ⊆ Δ := fun x hx ↦ hr.v_sub (by
    rw [hr.enc.sector.Dv_U] at hx
    exact Surface.discBd_subset _ hx)
  have huΔ : u ∈ Δ := hDvΔ (Dv.V_subset_U ((hc.mem_V u).mpr (.inr (.inl A₁.end_mem_support))))
  obtain ⟨c, hcX, T', L, rfl, hlast⟩ := GraphWalk.exists_last_mem T (X := C.V)
    (hr.exists_mem_C T huΔ hh)
  have hch₁ : c ∈ (A₁.append (T'.append L)).support :=
    (GraphWalk.mem_support_append _ _).mpr (.inr ((GraphWalk.mem_support_append _ _).mpr
      (.inl T'.end_mem_support)))
  have hch₂ : c ∈ (A₂.append (T'.append L)).support :=
    (GraphWalk.mem_support_append _ _).mpr (.inr ((GraphWalk.mem_support_append _ _).mpr
      (.inl T'.end_mem_support)))
  have hcW : c ∈ W \ discBd W := by
    refine ⟨h1.subset_W hW hbdS hin ((mem_walkDrawing_U _ _).mpr (.inl hch₁)), ?_⟩
    by_cases hcv : c = v₁
    · exact h2.tail_off_bd hW hbdS hin hch₂ (hcv ▸ hf.ne)
    · exact h1.tail_off_bd hW hbdS hin hch₁ hcv
  have hf₁ : f₁ ∈ Dv.E := (hc.mem_E _).mpr (.inl rfl)
  have hf₂ : f₂ ∈ Dv.E := (hc.mem_E _).mpr (.inr (.inl rfl))
  have hrep := hr.enc.hrep
  -- the count, for either form of `M`
  have hcount : ∀ {a b : Shat} {M : GraphWalk D.rad.G.toGraph a b} {Q : GraphWalk D.rad.G.toGraph b
    a}, D.IsOuterPath W C M Q → ∃ (Q₁ : GraphWalk D.rad.G.toGraph b c)
      (Q₂ : GraphWalk D.rad.G.toGraph c a), Q = Q₁.append Q₂ ∧ T'.length = 0 ∧ M.length = 2
        ∧ a ∈ D.P.Γ.hatV cap ∧ b ∈ D.P.Γ.hatV cap ∧ C.E.ncard = Dv.E.ncard ∧
      A₁.length + T'.length + L.length = Q₂.reverse.length + L.length
        ∧ A₂.length + T'.length + L.length = Q₁.length + L.length := by
    intro a b M Q ho
    have hcQ : c ∈ Q.support := ((ho.splits.V c).mp hcX).resolve_left fun h' ↦ ho.noint c h' hcW
    obtain ⟨Q₁, Q₂, rfl⟩ := Q.exists_append_of_mem hcQ
    have haG : a ∈ D.rad.G.V := Q₂.mem_vertexSet_of_mem_support Q₂.end_mem_support
    have hbG : b ∈ D.rad.G.V := Q₁.mem_vertexSet_of_mem_support Q₁.start_mem_support
    have lA := h1.le_walk_of_bd hW hbdS hin (Q₂.reverse.append L) haG ho.a_bd
    have lB := h2.le_walk_of_bd hW hbdS hin (Q₁.append L) hbG ho.b_bd
    simp only [GraphWalk.length_append] at lA lB
    have e₁ : (edgeSet M).ncard = M.length := by
      rw [← ncard_walk_E D.rad.G ho.splits.s₁, walkDrawing_E]
      rfl
    have e₂ : (edgeSet (Q₁.append Q₂)).ncard = (Q₁.append Q₂).length := by
      rw [← ncard_walk_E D.rad.G ho.splits.s₂, walkDrawing_E]
      rfl
    have e₃ := ho.splits.card_add
    have e₄ : C.length = C.E.ncard := rfl
    have e₅ := hr.card.1
    have e₆ := hc.card
    have e₇ := ho.two
    have e₈ : Q₂.reverse.length = Q₂.length := GraphWalk.length_reverse _
    rw [GraphWalk.length_append] at e₂
    have heq₁ : A₁.length + (T'.length + L.length) = Q₂.reverse.length + L.length := by omega
    have heq₂ : A₂.length + (T'.length + L.length) = Q₁.length + L.length := by omega
    exact ⟨Q₁, Q₂, rfl, by omega, by omega, lA.2 heq₁, lB.2 heq₂, by omega, by omega, by omega⟩
  have hout := hr.exists_outer hf.ne hf.link₁ hf.link₂ hb₁ hb₂ hf₁ hf₂ hf.r_mem.2 h1.2.v_mem.1
    h2.2.v_mem.1 hcX hcW
  rcases hout with ⟨a, b, M, Q, ho, hinner⟩ | ⟨hU, M, Q, ho, hMe⟩
  · obtain ⟨Q₁, Q₂, rfl, -, hl, ha, hb, -⟩ := hcount ho
    exact (ho.not_two hW hl ha hb hinner).elim
  obtain ⟨Q₁, Q₂, rfl, hT0, -, -, -, hcard, l₁, l₂⟩ := hcount ho
  obtain rfl : c = u := by
    cases T' with
    | nil _ => rfl
    | cons _ _ => simp [GraphWalk.length] at hT0
  have hT'e : T'.edges = [] := List.length_eq_zero_iff.mp hT0
  have hT'w : D.tb.walkWeight T' = 0 := by simp [TieBreaker.walkWeight, hT'e]
  have hLs : L.IsSimple := (GraphWalk.IsSimple.of_append (GraphWalk.IsSimple.of_append h1.1).2).2
  have hQs := ho.splits.s₂
  have hQ₁s := (GraphWalk.IsSimple.of_append hQs).1
  have hQ₂s := (GraphWalk.IsSimple.of_append hQs).2
  have hsupC : ∀ x ∈ (Q₁.append Q₂).support, x ∈ C.V := fun x hx ↦ (ho.splits.V x).mpr (.inr hx)
  have hs₁ : (Q₂.reverse.append L).IsSimple := isSimple_append' hQ₂s.reverse hLs fun y hy₁ hy₂ ↦
    hlast y hy₂ (hsupC y ((GraphWalk.mem_support_append _ _).mpr (.inr
      (by simpa [GraphWalk.support_reverse] using hy₁))))
  have hs₂ : (Q₁.append L).IsSimple := isSimple_append' hQ₁s hLs fun y hy₁ hy₂ ↦
    hlast y hy₂ (hsupC y ((GraphWalk.mem_support_append _ _).mpr (.inl hy₁)))
  have b₁ := (h1.bound h2.2.h_mem (Q₂.reverse.append L)).2 (by
    simp only [GraphWalk.length_append] at l₁ ⊢
    omega)
  have b₂ := (h2.bound h2.2.h_mem (Q₁.append L)).2 (by
    simp only [GraphWalk.length_append] at l₂ ⊢
    omega)
  simp only [TieBreaker.walkWeight_append, TieBreaker.walkWeight_reverse, hT'w, zero_add] at b₁ b₂
  have w₁ := hr.card.2 hcard
  have w₂ := D.tb.weightSub_eq_of_splits ho.splits
  rw [TieBreaker.walkWeight_append] at w₂
  have w₃ : D.tb.walkWeight M = D.tb.wtE f₁ + D.tb.wtE f₂ := by simp [TieBreaker.walkWeight, hMe]
  let R : GraphWalk D.rad.G.toGraph c c := A₁.reverse.append (.cons (IsLink.symm' hf.link₁)
    (.cons hf.link₂ A₂))
  have hR : ∀ e ∈ Dv.E, e ∈ R.edges := fun e he ↦ by
    simp only [R, GraphWalk.edges_append, GraphWalk.edges_cons, GraphWalk.edges_reverse,
      List.mem_append, List.mem_reverse, List.mem_cons]
    have := (hc.mem_E e).mp he
    tauto
  have w₄ := D.tb.weightSub_le_of_edges R hR
  have w₅ : D.tb.walkWeight R = D.tb.walkWeight A₁ + D.tb.wtE f₁ + D.tb.wtE f₂ + D.tb.walkWeight A₂
    := by
    simp only [R, TieBreaker.walkWeight_append, TieBreaker.walkWeight_reverse]
    simp [TieBreaker.walkWeight]
    ring
  have eq₁ : D.tb.walkWeight (A₁.append (T'.append L)) = D.tb.walkWeight (Q₂.reverse.append L) := by
    simp only [TieBreaker.walkWeight_append, TieBreaker.walkWeight_reverse, hT'w, zero_add]
    linarith
  have eq₂ : D.tb.walkWeight (A₂.append (T'.append L)) = D.tb.walkWeight (Q₁.append L) := by
    simp only [TieBreaker.walkWeight_append, hT'w, zero_add]
    linarith
  have sub₁ := D.edges_eq_of_weight_eq h1.1 hs₁ eq₁
  have sub₂ := D.edges_eq_of_weight_eq h2.1 hs₂ eq₂
  refine hr.ins_of_E fun e he ↦ ?_
  have hM : ∀ e ∈ M.edges, e ∈ C.E := fun e he ↦ (ho.splits.E e).mpr (.inl he)
  have hQ : ∀ e, e ∈ Q₁.edges ∨ e ∈ Q₂.edges → e ∈ C.E := fun e he ↦ (ho.splits.E e).mpr (.inr (by
    rw [GraphWalk.edges_append, List.mem_append]
    exact he))
  rcases (hc.mem_E e).mp he with rfl | rfl | he' | he'
  · exact hM _ (by simp [hMe])
  · exact hM _ (by simp [hMe])
  · have h₃ := (sub₁ e).mp (by
      rw [GraphWalk.edges_append]
      exact List.mem_append_left _ he')
    rw [GraphWalk.edges_append, GraphWalk.edges_reverse, List.mem_append, List.mem_reverse] at h₃
    rcases h₃ with h₃ | h₃
    · exact hQ e (.inr h₃)
    · refine absurd ?_ (hf.edges_disjoint_T e he')
      rw [GraphWalk.edges_append]
      exact List.mem_append_right _ h₃
  · have h₃ := (sub₂ e).mp (by
      rw [GraphWalk.edges_append]
      exact List.mem_append_left _ he')
    rw [GraphWalk.edges_append, List.mem_append] at h₃
    rcases h₃ with h₃ | h₃
    · exact hQ e (.inl h₃)
    · refine absurd ?_ (hf.swap.edges_disjoint_T e he')
      rw [GraphWalk.edges_append]
      exact List.mem_append_right _ h₃

private theorem sector_supported_by_closed_walk
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    [T2Space Shat]
    {α : Type w}
    {cap : IsCappedSurface S Shat}
    {χ : ColourScheme S α}
    {D : TangleDatum cap χ}
    {r : Shat}
    {Dv : Drawing Shat}
    {v₁ : Shat}
    {v₂ : Shat}
    {h₁ : Shat}
    {h₂ : Shat}
    {f₁ : Set Shat}
    {f₂ : Set Shat}
    {K₁ : GraphWalk (Drawing.toGraph D.rad.G) v₁ h₁}
    {K₂ : GraphWalk (Drawing.toGraph D.rad.G) v₂ h₂}
    {P : Drawing Shat}
    (hl₁ : (Drawing.toGraph D.rad.G).IsLink f₁ r v₁)
    (hl₂ : (Drawing.toGraph D.rad.G).IsLink f₂ r v₂)
    (hUform : (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ P.U ∪ closure f₁ ∪ closure
      f₂ = Dv.U)
    (K₀ : GraphWalk (Drawing.toGraph D.rad.G) h₁ h₂)
    (hV₀ : ∀ (x : Shat), x ∈ P.V ↔ x ∈ K₀.support)
    (hE₀ : ∀ (e : Set Shat), e ∈ Drawing.E P ↔ e ∈ K₀.edges) :
    let R : GraphWalk (Drawing.toGraph D.rad.G) h₁ h₁ := K₁.reverse.append (GraphWalk.cons
      (IsLink.symm' hl₁) (GraphWalk.cons hl₂ (K₂.append K₀.reverse)))
    Dv.U ⊆ (walkDrawing D.rad.G R).U := by
  intro R x hx
  rw [mem_walkDrawing_U]
  rw [← hUform] at hx
  have hRs : ∀ x, x ∈ K₁.support ∨ x ∈ K₂.support ∨ x ∈ K₀.support → x ∈ R.support
    := fun x hx ↦ by
    simp only [R, GraphWalk.mem_support_append, GraphWalk.support_reverse, List.mem_reverse,
      GraphWalk.support_cons, List.mem_cons]
    tauto
  have hRe : ∀ e, e = f₁ ∨ e = f₂ ∨ e ∈ K₁.edges ∨ e ∈ K₂.edges ∨ e ∈ K₀.edges → e ∈ R.edges
    := fun e he ↦ by
    simp only [R, GraphWalk.edges_append, GraphWalk.edges_reverse, GraphWalk.edges_cons,
      List.mem_append, List.mem_reverse, List.mem_cons]
    tauto
  rcases hx with (((hx | hx) | hx) | hx) | hx
  · rcases (mem_walkDrawing_U _ _).mp hx with h' | ⟨e, he, hxe⟩
    · exact .inl (hRs x (.inl h'))
    · exact .inr ⟨e, hRe e (by tauto), hxe⟩
  · rcases (mem_walkDrawing_U _ _).mp hx with h' | ⟨e, he, hxe⟩
    · exact .inl (hRs x (.inr (.inl h')))
    · exact .inr ⟨e, hRe e (by tauto), hxe⟩
  · by_cases hxV : x ∈ P.V
    · exact .inl (hRs x (.inr (.inr ((hV₀ x).mp hxV))))
    · obtain ⟨g, hg, hxg⟩ := P.exists_edge_of_mem hx hxV
      exact .inr ⟨g, hRe g (.inr (.inr (.inr (.inr ((hE₀ g).mp hg))))), subset_closure hxg⟩
  · exact .inr ⟨f₁, hRe _ (.inl rfl), hx⟩
  · exact .inr ⟨f₂, hRe _ (.inr (.inl rfl)), hx⟩

/-- **Step (6) of the proof of (13.6) when the spokes do not meet.** -/
theorem IsRound.step_six_path (hr : D.IsRound W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ) {v₁ v₂ h₁ h₂ : Shat}
  {f₁ f₂ : Set Shat} {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁}
    {K₂ : GraphWalk D.rad.G.toGraph v₂ h₂} {P : Drawing Shat} (hne : v₁ ≠ v₂)
      (hl₁ : D.rad.G.toGraph.IsLink f₁ r v₁) (hl₂ : D.rad.G.toGraph.IsLink f₂ r v₂)
    (hb₁ : f₁ ⊆ discBd W) (hb₂ : f₂ ⊆ discBd W) (h1 : D.IsSpokeWalk W H K₁)
      (h2 : D.IsSpokeWalk W H K₂) (hdis : ∀ x ∈ K₁.support, x ∉ K₂.support)
    (hP : Drawing.IsPathOf P H h₁ h₂) (hbd : discBd Δv = (walkDrawing D.rad.G K₁).U ∪
      (walkDrawing D.rad.G K₂).U ∪ P.U ∪ closure f₁ ∪ closure f₂)
    (hh : H.U ∩ Δ ⊆ C.U) : D.ins F ⊆ Δv := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hW := hr.enc.wheel
  have hbdS := hr.enc.hbdS
  have hin := hr.enc.hin
  have hCc := hr.circuit
  have hDv := hr.enc.sector.Dv_circuit
  have hrr := hr.enc.sector.rstar_mem
  have hDvΔ : Dv.U ⊆ Δ := fun x hx ↦ hr.v_sub (by
    rw [hr.enc.sector.Dv_U] at hx
    exact Surface.discBd_subset _ hx)
  have hUform : (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ P.U ∪ closure f₁ ∪
    closure f₂ = Dv.U := by
    rw [← hbd, hr.enc.sector.Dv_U]
  have hPG : Drawing.IsPathOf P D.rad.G h₁ h₂ := ⟨hP.1.trans hW.H_sub, hP.2⟩
  obtain ⟨K₀, hK₀, hV₀, hE₀⟩ := Drawing.IsPathOf.exists_simple_walk hPG
  have hPH : P.U ⊆ H.U := hP.1.U_subset
  have hPDv : P.U ⊆ Dv.U := fun x hx ↦ hUform ▸ .inl (.inl (.inr hx))
  have hPC : P.U ⊆ C.U := fun x hx ↦ hh ⟨hPH hx, hDvΔ (hPDv hx)⟩
  have hne12 : h₁ ≠ h₂ := fun h' ↦ hdis h₁ K₁.end_mem_support (h' ▸ K₂.end_mem_support)
  have hV₀P : ∀ x ∈ K₀.support, x ∈ P.U := fun x hx ↦ P.V_subset_U ((hV₀ x).mpr hx)
  have hedgeU : ∀ e ∈ K₀.edges, e ⊆ P.U := fun e he ↦ subset_closure.trans (P.closure_subset_U
    ((hE₀ e).mpr he))
  have hK₀C : ∀ e ∈ K₀.edges, e ∈ C.E := fun e he ↦ by
    by_contra hn
    have heG : e ∈ D.rad.G.E := hPG.1.2 ((hE₀ e).mpr he)
    obtain ⟨x, hx⟩ := heG.1
    exact disjoint_left.mp (edge_disjoint_U hCc.1 heG hn) hx (hPC (hedgeU e he hx))
  have hh₁C : h₁ ∈ C.V := mem_V_of_mem_U hCc.1 (hPC (hV₀P _ K₀.start_mem_support))
    (K₀.mem_vertexSet_of_mem_support K₀.start_mem_support)
  have hh₂C : h₂ ∈ C.V := mem_V_of_mem_U hCc.1 (hPC (hV₀P _ K₀.end_mem_support))
    (K₀.mem_vertexSet_of_mem_support K₀.end_mem_support)
  have hh₁W : h₁ ∈ W \ discBd W := hW.H_in_int (H.V_subset_U h1.2.h_mem)
  have hh₂W : h₂ ∈ W \ discBd W := hW.H_in_int (H.V_subset_U h2.2.h_mem)
  have hedgeDv : ∀ {e : Set Shat}, e ∈ D.rad.G.E → e ⊆ Dv.U → e ∈ Dv.E := fun {e} heG hs ↦ by
    by_contra hn
    obtain ⟨x, hx⟩ := heG.1
    exact disjoint_left.mp (edge_disjoint_U hDv.1 heG hn) hx (hs hx)
  have hf₁ : f₁ ∈ Dv.E := hedgeDv hl₁.1 (subset_closure.trans fun x hx ↦ hUform ▸ .inl (.inr hx))
  have hf₂ : f₂ ∈ Dv.E := hedgeDv hl₂.1 (subset_closure.trans fun x hx ↦ hUform ▸ .inr hx)
  let R : GraphWalk D.rad.G.toGraph h₁ h₁ := K₁.reverse.append (.cons (IsLink.symm' hl₁) (.cons hl₂
    (K₂.append K₀.reverse)))
  have hRU : Dv.U ⊆ (walkDrawing D.rad.G R).U := by
    exact sector_supported_by_closed_walk (S := S) (Shat := Shat) (α := α) (cap := cap) (χ := χ)
      (D := D) (r := r) (Dv := Dv) (v₁ := v₁) (v₂ := v₂) (h₁ := h₁) (h₂ := h₂) (f₁ := f₁) (f₂ :=
      f₂) (K₁ := K₁) (K₂ := K₂) (P := P) hl₁ hl₂ hUform K₀ hV₀ hE₀
  have hRE : ∀ e ∈ Dv.E, e ∈ R.edges := fun e he ↦ by
    by_contra hn
    have heG := hDv.1.2 he
    obtain ⟨x, hx⟩ := heG.1
    have hn' : e ∉ (walkDrawing D.rad.G R).E := fun h' ↦ hn (by rwa [walkDrawing_E] at h')
    exact disjoint_left.mp (edge_disjoint_U (walkDrawing_isSubdrawing _ _) heG hn') hx (hRU
      (Dv.closure_subset_U he (subset_closure hx)))
  have hRl : R.length = K₁.length + K₂.length + K₀.length + 2 := by
    simp only [R, GraphWalk.length_append, GraphWalk.length_reverse, GraphWalk.length_cons]
    omega
  have hcount : ∀ {a b : Shat} {M : GraphWalk D.rad.G.toGraph a b} {Q : GraphWalk D.rad.G.toGraph b
    a}, D.IsOuterPath W C M Q →
      ∃ (x₁ x₂ : Shat) (X₁ : GraphWalk D.rad.G.toGraph x₁ h₁) (X₂ : GraphWalk D.rad.G.toGraph x₂
        h₂), ((x₁ = a ∧ x₂ = b) ∨ (x₁ = b ∧ x₂ = a)) ∧ X₁.IsSimple ∧ X₂.IsSimple ∧
        (∀ e, e ∈ Q.edges ↔ e ∈ X₁.edges ∨ e ∈ X₂.edges ∨ e ∈ K₀.edges) ∧ D.tb.walkWeight Q
          = D.tb.walkWeight X₁ + D.tb.walkWeight X₂ + D.tb.walkWeight K₀ ∧
        M.length = 2 ∧ X₁.length = K₁.length ∧ X₂.length = K₂.length ∧ a ∈ D.P.Γ.hatV cap
          ∧ b ∈ D.P.Γ.hatV cap ∧ C.E.ncard = Dv.E.ncard := by
    intro a b M Q ho
    have hoffM : ∀ e ∈ K₀.edges, e ∉ M.edges := fun e he heM ↦ by
      have heG : e ∈ D.rad.G.E := hPG.1.2 ((hE₀ e).mpr he)
      obtain ⟨x, hx⟩ := heG.1
      exact disjoint_left.mp (ho.off_int e heM) hx (hW.H_in_int (hPH (hedgeU e he hx)))
    have hE₀Q : ∀ e ∈ K₀.edges, e ∈ Q.edges := fun e he ↦ ((ho.splits.E e).mp
      (hK₀C e he)).resolve_left (hoffM e he)
    have hh₁Q : h₁ ∈ Q.support := ((ho.splits.V _).mp hh₁C).resolve_left fun h' ↦ ho.noint _ h' hh₁W
    have hh₂Q : h₂ ∈ Q.support := ((ho.splits.V _).mp hh₂C).resolve_left fun h' ↦ ho.noint _ h' hh₂W
    have hform : (∃ (A : GraphWalk D.rad.G.toGraph b h₁) (B : GraphWalk D.rad.G.toGraph h₂ a), Q
      = A.append (K₀.append B)) ∨
        (∃ (A : GraphWalk D.rad.G.toGraph b h₂) (B : GraphWalk D.rad.G.toGraph h₁ a), Q = A.append
          (K₀.reverse.append B)) := by
      obtain ⟨A₀, B₀, hQ⟩ := Q.exists_append_of_mem hh₁Q
      by_cases hy : h₂ ∈ B₀.support
      · left
        obtain ⟨K', B, rfl⟩ := B₀.exists_append_of_mem hy
        subst hQ
        obtain rfl := GraphWalk.eq_piece A₀ K' B ho.splits.s₂ K₀ hK₀ hE₀Q
        exact ⟨A₀, B, rfl⟩
      · right
        subst hQ
        have hy' : h₂ ∈ A₀.support := ((GraphWalk.mem_support_append _ _).mp hh₂Q).resolve_right hy
        obtain ⟨A', K', rfl⟩ := A₀.exists_append_of_mem hy'
        have hass := GraphWalk.append_assoc' A' K' B₀
        rw [hass] at ho hE₀Q ⊢
        obtain rfl := GraphWalk.eq_piece A' K' B₀ ho.splits.s₂ K₀.reverse hK₀.reverse fun e he ↦
          hE₀Q e (by simpa [GraphWalk.edges_reverse] using he)
        exact ⟨A', B₀, rfl⟩
    have hstruct : ∃ (x₁ x₂ : Shat) (X₁ : GraphWalk D.rad.G.toGraph x₁ h₁)
      (X₂ : GraphWalk D.rad.G.toGraph x₂ h₂), ((x₁ = a ∧ x₂ = b) ∨ (x₁ = b ∧ x₂ = a)) ∧
        X₁.IsSimple ∧ X₂.IsSimple ∧
        (∀ e, e ∈ Q.edges ↔ e ∈ X₁.edges ∨ e ∈ X₂.edges ∨ e ∈ K₀.edges) ∧ D.tb.walkWeight Q
          = D.tb.walkWeight X₁ + D.tb.walkWeight X₂ + D.tb.walkWeight K₀ ∧
        Q.length = X₁.length + X₂.length + K₀.length := by
      rcases hform with ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩
      · have hs₁ := (And.intro (isSimple_of_append ho.splits.s₂).1 (isSimple_of_append
          ho.splits.s₂).2)
        have hs₂ := (And.intro (isSimple_of_append hs₁.2).1 (isSimple_of_append hs₁.2).2)
        refine ⟨b, a, A, B.reverse, .inr ⟨rfl, rfl⟩, hs₁.1, hs₂.2.reverse, fun e ↦ ?_, ?_, ?_⟩
        · simp only [GraphWalk.edges_append, GraphWalk.edges_reverse, List.mem_append,
            List.mem_reverse]
          tauto
        · simp only [TieBreaker.walkWeight_append, TieBreaker.walkWeight_reverse]
          ring
        · simp only [GraphWalk.length_append, GraphWalk.length_reverse]
          omega
      · have hs₁ := (And.intro (isSimple_of_append ho.splits.s₂).1 (isSimple_of_append
          ho.splits.s₂).2)
        have hs₂ := (And.intro (isSimple_of_append hs₁.2).1 (isSimple_of_append hs₁.2).2)
        refine ⟨a, b, B.reverse, A, .inl ⟨rfl, rfl⟩, hs₂.2.reverse, hs₁.1, fun e ↦ ?_, ?_, ?_⟩
        · simp only [GraphWalk.edges_append, GraphWalk.edges_reverse, List.mem_append,
            List.mem_reverse]
          tauto
        · simp only [TieBreaker.walkWeight_append, TieBreaker.walkWeight_reverse]
          ring
        · simp only [GraphWalk.length_append, GraphWalk.length_reverse]
          omega
    obtain ⟨x₁, x₂, X₁, X₂, hx, hX₁, hX₂, hEq, hwq, hlq⟩ := hstruct
    have hbdx : x₁ ∈ discBd W ∧ x₂ ∈ discBd W := by
      rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ho.a_bd, ho.b_bd⟩
      · exact ⟨ho.b_bd, ho.a_bd⟩
    have lA := h1.le_walk_of_bd hW hbdS hin X₁ (X₁.mem_vertexSet_of_mem_support
      X₁.start_mem_support) hbdx.1
    have lB := h2.le_walk_of_bd hW hbdS hin X₂ (X₂.mem_vertexSet_of_mem_support
      X₂.start_mem_support) hbdx.2
    have e₁ : (edgeSet M).ncard = M.length := by
      rw [← ncard_walk_E D.rad.G ho.splits.s₁, walkDrawing_E]
      rfl
    have e₂ : (edgeSet Q).ncard = Q.length := by
      rw [← ncard_walk_E D.rad.G ho.splits.s₂, walkDrawing_E]
      rfl
    have e₃ := ho.splits.card_add
    have e₄ : C.length = C.E.ncard := rfl
    have e₅ := hr.card.1
    have e₆ := ncard_le_length_of_edges (G := D.rad.G) R hRE
    have e₇ := ho.two
    have h₁e : K₁.length = X₁.length := by omega
    have h₂e : K₂.length = X₂.length := by omega
    have hat₁ := lA.2 h₁e
    have hat₂ := lB.2 h₂e
    have hab : a ∈ D.P.Γ.hatV cap ∧ b ∈ D.P.Γ.hatV cap := by
      rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hat₁, hat₂⟩
      · exact ⟨hat₂, hat₁⟩
    exact ⟨x₁, x₂, X₁, X₂, hx, hX₁, hX₂, hEq, hwq, by omega, by omega, by omega, hab.1, hab.2,
      by omega⟩
  have hout := hr.exists_outer hne hl₁ hl₂ hb₁ hb₂ hf₁ hf₂ hrr.1.2 h1.2.v_mem.1 h2.2.v_mem.1 hh₁C
    hh₁W
  rcases hout with ⟨a, b, M, Q, ho, hinner⟩ | ⟨hU, M, Q, ho, hMe⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, hl, -, -, ha, hb, -⟩ := hcount ho
    exact (ho.not_two hW hl ha hb hinner).elim
  obtain ⟨x₁, x₂, X₁, X₂, hx, hX₁, hX₂, hEq, hwq, -, hl₃, hl₄, -, -, hcard⟩ := hcount ho
  have w₁ := hr.card.2 hcard
  have w₂ := D.tb.weightSub_eq_of_splits ho.splits
  have w₃ : D.tb.walkWeight M = D.tb.wtE f₁ + D.tb.wtE f₂ := by simp [TieBreaker.walkWeight, hMe]
  have w₄ := D.tb.weightSub_le_of_edges R hRE
  have w₅ : D.tb.walkWeight R = D.tb.walkWeight K₁ + D.tb.wtE f₁ + D.tb.wtE f₂ + D.tb.walkWeight K₂
    + D.tb.walkWeight K₀ := by
    have w₀ : D.tb.walkWeight (K₂.append K₀.reverse) = D.tb.walkWeight K₂ + D.tb.walkWeight K₀ := by
      rw [TieBreaker.walkWeight_append, TieBreaker.walkWeight_reverse]
    simp only [R, TieBreaker.walkWeight_append, TieBreaker.walkWeight_reverse]
    simp only [TieBreaker.walkWeight] at w₀ ⊢
    simp only [GraphWalk.edges_cons, List.map_cons, List.sum_cons]
    rw [w₀]
    ring
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have b₁ := (h1.bound h1.2.h_mem X₁).2 hl₃
    have b₂ := (h2.bound h2.2.h_mem X₂).2 hl₄
    have sub₁ := D.edges_eq_of_weight_eq h1.1 hX₁ (by linarith)
    have sub₂ := D.edges_eq_of_weight_eq h2.1 hX₂ (by linarith)
    refine hr.ins_of_E fun e he ↦ ?_
    have h₃ := hRE e he
    simp only [R, GraphWalk.edges_append, GraphWalk.edges_reverse, GraphWalk.edges_cons,
      List.mem_append, List.mem_reverse, List.mem_cons] at h₃
    have hM : ∀ e ∈ M.edges, e ∈ C.E := fun e he ↦ (ho.splits.E e).mpr (.inl he)
    have hQ : ∀ e ∈ Q.edges, e ∈ C.E := fun e he ↦ (ho.splits.E e).mpr (.inr he)
    rcases h₃ with h₃ | rfl | rfl | h₃ | h₃
    · exact hQ e ((hEq e).mpr (.inl ((sub₁ e).mp h₃)))
    · exact hM _ (by simp [hMe])
    · exact hM _ (by simp [hMe])
    · exact hQ e ((hEq e).mpr (.inr (.inl ((sub₂ e).mp h₃))))
    · exact hK₀C e h₃
  · exfalso
    have b₁ := h2.bound h1.2.h_mem X₁
    have b₂ := h1.bound h2.2.h_mem X₂
    have heq₁ : X₁.length = K₂.length := by omega
    have heq₂ : X₂.length = K₁.length := by omega
    have w₆ := b₁.2 heq₁
    have w₇ := b₂.2 heq₂
    have sub := D.edges_eq_of_weight_eq h2.1 hX₁ (by linarith)
    exact hne12 (simple_walks_eq K₂ X₁ h2.1 hX₁ sub).1.symm

/-- **Step (6) of the proof of (13.6).** -/
theorem IsRound.step_six (hr : D.IsRound W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ)
  (hh : H.U ∩ Δ ⊆ C.U) : D.ins F ⊆ Δv := by
  have hW := hr.enc.wheel
  rcases hr.enc.sector.cases hW hr.enc.hbdS hr.enc.hin with ⟨v₁, v₂, u, h, f₁, f₂, A₁, A₂, T, hf,
    hC, hb₁, hb₂⟩ |
    ⟨v₁, v₂, h₁, h₂, f₁, f₂, K₁, K₂, P, hne, hl₁, hl₂, hb₁, hb₂, h1, h2, hdis, hP, hbd, -⟩
  · exact hr.step_six_fan hf hC hb₁ hb₂ fun hm ↦ hh ⟨H.V_subset_U hf.spoke₁.2.h_mem, hm⟩
  · exact hr.step_six_path hne hl₁ hl₂ hb₁ hb₂ h1 h2 hdis hP hbd hh

end TangleDatum

end GraphMinor.GM19
