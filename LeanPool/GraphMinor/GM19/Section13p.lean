/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13o

/-!
# Graph Minors XIX, Section 13: the point `h` and the arcs in the proof of (13.6)

From here on we suppose that `ins(H) ∩ Δ ⊄ U(C)`, and we seek a contradiction. We take the point
`h`, and we show that `F` has an inner arc and an outer arc.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
/-- If a disc in the disc of `B` is bounded by a circuit `A`, and `C ⊆ A ∪ B` bounds a disc that
holds the disc of `B`, then `C ⊆ B`. -/
theorem edges_of_nested (hT : IsClosedSurface Shat) {G A B C : Drawing Shat}
    {ΔA ΔB Δ : Set Shat} (hB : B.IsCircuitOf G) (hC : C.IsCircuitOf G) (hΔB : IsClosedDisc ΔB)
    (hbB : discBd ΔB = B.U) (hbA : discBd ΔA = A.U) (hAB : ΔA ⊆ ΔB) (hΔ : IsClosedDisc Δ)
    (hb : discBd Δ = C.U)
    (hBΔ : ΔB ⊆ Δ) (hE : ∀ e ∈ C.E, e ∈ A.E ∨ e ∈ B.E) : ∀ e ∈ C.E, e ∈ B.E := by
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  intro e he
  rcases hE e he with h₁ | h₁
  · by_contra hn
    have heG := hC.1.2 he
    obtain ⟨x, hx⟩ := heG.1
    have hxA : x ∈ ΔB := hAB (by
      have : x ∈ discBd ΔA := by
        rw [hbA]
        exact A.closure_subset_U h₁ (subset_closure hx)
      exact Surface.discBd_subset _ this)
    have hd := edge_disjoint_U hB.1 heG hn
    have hxi : x ∈ discInt ΔB := ⟨hxA, fun hb' ↦ disjoint_left.mp hd hx (hbB ▸ hb')⟩
    have hxb : x ∈ frontier Δ := by
      rw [IsClosedDisc.frontier_eq_discBd hT hΔ, hb]
      exact C.closure_subset_U he (subset_closure hx)
    exact hxb.2 (mem_interior.mpr ⟨_, (discInt_subset _).trans hBΔ, hΔB.isOpen_discInt hman, hxi⟩)
  · exact h₁

omit [T2Space Shat] in
/-- A disc in `Δ₀` whose boundary lies in a second disc in `Δ₀` lies in the second disc. -/
theorem disc_subset_of_bd [ConnectedSpace Shat] (hT : IsClosedSurface Shat) {Δ₀ Δ₁ Δ₂ : Set Shat}
  (h₀ : IsClosedDisc Δ₀) (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂)
    (s₁ : Δ₁ ⊆ Δ₀) (s₂ : Δ₂ ⊆ Δ₀) (hb : discBd Δ₁ ⊆ Δ₂) : Δ₁ ⊆ Δ₂ := by
  obtain ⟨Δ', ⟨hs₁, hd₁, hb₁, -⟩, -⟩ := disc_oArc Δ₂ (discBd Δ₁) h₂ hb h₁.isOArc_discBd
  rw [disc_eq_of_subset_disc hT h₀ h₁ hd₁ s₁ (hs₁.trans s₂) hb₁.symm]
  exact hs₁

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}

/-- The set-up after step (6): `h ∈ Δ \ U(C)`, and `h ∈ ins(H)`. If `H` is a circuit then `h ∉
U(H)`. -/
structure IsFar (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat) (ρ : ℕ) (r : Shat)
  (Δv : Set Shat) (Dv : Drawing Shat) (ord' : ℕ)
    (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (F : Drawing Shat) (Δ₀ : Set Shat)
      (C : Drawing Shat) (Δ : Set Shat) (h : Shat) : Prop
    extends D.IsRound W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ where
  mem_Δ : h ∈ Δ
  not_C : h ∉ C.U
  hub : (H.V = {h} ∧ H.V.ncard = 1) ∨ (IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4
    ∧ h ∈ discInt (D.ins H))

omit [T2Space S] in
/-- The choice of `h`, after step (6). -/
theorem IsRound.exists_far (hr : D.IsRound W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ)
  (hn : ¬ H.U ∩ Δ ⊆ C.U) : ∃ h, D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hW := hr.enc.wheel
  obtain ⟨y, ⟨hyH, hyΔ⟩, hyC⟩ := not_subset.mp hn
  have hyi : y ∈ discInt Δ := ⟨hyΔ, fun hb ↦ hyC (hr.bd ▸ hb)⟩
  rcases hW.hub_cond with ⟨hc, hE, -⟩ | ⟨hH, hle, -⟩
  · refine ⟨y, hr, hyΔ, hyC, .inl ⟨?_, hc⟩⟩
    obtain ⟨z, hz⟩ := ncard_eq_one.mp hc
    have hyV : y ∈ H.V := by
      by_contra hnV
      obtain ⟨g, hg, -⟩ := H.exists_edge_of_mem hyH hnV
      rw [hE] at hg
      exact hg
    rw [hz] at hyV ⊢
    rw [mem_singleton_iff.mp hyV]
  · obtain ⟨-, -, -, hcir, hlt, -⟩ := id hH
    have hi := D.ins_spec hcir hlt
    have hyb : y ∈ frontier (discInt (D.ins H)) := by
      have h₁ := IsClosedDisc.frontier_eq_discBd hT hi.2.2.1
      have h₂ : y ∈ frontier (D.ins H) := by
        rw [h₁, hi.2.2.2.1]
        exact hyH
      have hint : frontier (discInt (D.ins H)) = closure (discInt (D.ins H)) \ discInt (D.ins H) :=
        (hi.2.2.1.isOpen_discInt hman).frontier_eq
      rw [hint, closure_discInt hi.2.2.1]
      exact ⟨h₂.1 |> fun _ ↦ Surface.discBd_subset _ (hi.2.2.2.1.symm ▸ hyH),
        fun h' ↦ h'.2 (hi.2.2.2.1.symm ▸ hyH)⟩
    obtain ⟨z, hzΔ, hzi⟩ := mem_closure_iff.mp hyb.1 _ (hr.disc.isOpen_discInt hman) hyi
    exact ⟨z, hr, hzΔ.1, fun hb ↦ hzΔ.2 (hr.bd.symm ▸ hb), .inr ⟨hH, hle, hzi⟩⟩

omit [T2Space S] in
/-- A simple walk `P` from `a` to `b ≠ a` with edges in a circuit `F`, and a walk `J` back with
edges in `F` and no edge of `P`, use up `F`. -/
theorem circuit_cover {a b : Shat} {P : GraphWalk D.rad.G.toGraph a b} (hF : F.IsCircuitOf D.rad.G)
  (hne : a ≠ b) (hP : P.IsSimple)
    (hPF : ∀ e ∈ P.edges, e ∈ F.E) (J : GraphWalk D.rad.G.toGraph b a)
      (hJF : ∀ e ∈ J.edges, e ∈ F.E) (hd : ∀ e ∈ J.edges, e ∉ P.edges) :
    ∀ e ∈ F.E, e ∈ P.edges ∨ e ∈ J.edges := by
  classical
  have hstart : ∀ {a b : Shat} (N : GraphWalk D.rad.G.toGraph a b), a ≠ b →
    (∀ e ∈ N.edges, e ∈ F.E) → a ∈ F.V := by
    intro a b N hab hE
    cases N with
    | nil _ => exact absurd rfl hab
    | @cons _ y _ e hl r => exact (Drawing.IsLink.mem_V_of_sub hF.1 hl (hE e (by simp))).1
  have ha := hstart P hne hPF
  have hb := hstart P.reverse hne.symm fun e he ↦ hPF e (by simpa [GraphWalk.edges_reverse] using
    he)
  obtain ⟨R₁, R₂, hs⟩ := exists_splits hF.2 hF.1 ha hb hne
  obtain ⟨R, hR⟩ := exists_side_of_walk hne hP hPF hs
  obtain ⟨J', hJ's, -, hJ'e⟩ := GM11.GraphWalk.exists_isSimple J
  have hsub : ∀ e ∈ J'.edges, e ∈ R.edges := fun e he ↦ ((hR.E e).mp (hJF e
    (hJ'e e he))).resolve_left (hd e (hJ'e e he))
  obtain rfl := simple_walk_unique R J' hR.s₂ hJ's hsub
  intro e he
  rcases (hR.E e).mp he with h₁ | h₁
  · exact .inl h₁
  · exact .inr (hJ'e e h₁)

omit [T2Space S] in
/-- A vertex of a circuit is in no edge. So a walk in `G` that avoids the vertices of `Dv` and its
edges stays on one side of the disc of `Dv`. -/
theorem side_of_walk {Dv : Drawing Shat} {Δv : Set Shat} (hDv : Dv.IsSubdrawing D.rad.G)
  (hd : IsClosedDisc Δv) (hb : discBd Δv = Dv.U) {a b : Shat}
    (L : GraphWalk D.rad.G.toGraph a b) (hs : L.IsSimple) (hmid : ∀ z ∈ L.support, z ≠ b
      → z ∉ Dv.V) (hoff : ∀ e ∈ L.edges, e ∉ Dv.E) :
    (a ∈ discInt Δv → ∀ e ∈ L.edges, e ⊆ discInt Δv) ∧ (a ∉ Δv → ∀ e ∈ L.edges, Disjoint e Δv) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  induction L with
  | nil _ => simp
  | @cons a y b e hl L ih =>
    have hnd : (GraphWalk.cons hl L).support.Nodup := hs
    simp only [GraphWalk.support_cons, List.nodup_cons] at hnd
    have heoff := hoff e (by simp)
    have hIH := ih hnd.2 (fun z hz hzb ↦ hmid z (by simp [hz]) hzb) (fun f hf ↦ hoff f
      (by simp [hf]))
    have hstep : y = b ∨ y ∉ Dv.U := by
      by_cases hyb : y = b
      · exact .inl hyb
      · exact .inr fun hu ↦ hmid y (by simp [L.start_mem_support]) hyb
          (mem_V_of_mem_U hDv hu hl.2.2.1)
    have hrest : y = b → ∀ f ∈ L.edges, False := fun hyb f hf ↦ by
      subst hyb
      rw [(simple_self hnd.2).1] at hf
      cases hf
    constructor
    · intro hai f hf
      have hein : e ⊆ discInt Δv := by
        rcases edge_inside_or_off hT hDv hd hb hl.1 heoff with h₁ | h₁
        · exact h₁
        · obtain ⟨z, hzi, hze⟩ := mem_closure_iff.mp (IsLink.left_mem_closure hl) _
            (hd.isOpen_discInt hman) hai
          exact absurd hzi.1 (disjoint_left.mp h₁ hze)
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hein
      · rcases hstep with h₁ | h₁
        · exact (hrest h₁ f hf).elim
        · refine hIH.1 ⟨closure_minimal (hein.trans (discInt_subset _)) hd.isClosed
            (IsLink.right_mem_closure hl), fun hb' ↦ h₁ (hb ▸ hb')⟩ f hf
    · intro hao f hf
      have heout : Disjoint e Δv := by
        rcases edge_inside_or_off hT hDv hd hb hl.1 heoff with h₁ | h₁
        · exact absurd (closure_minimal (h₁.trans (discInt_subset _)) hd.isClosed
            (IsLink.left_mem_closure hl)) hao
        · exact h₁
      rcases List.mem_cons.mp hf with rfl | hf
      · exact heout
      · rcases hstep with h₁ | h₁
        · exact (hrest h₁ f hf).elim
        · refine hIH.2 (fun hyΔ ↦ ?_) f hf
          have hyi : y ∈ discInt Δv := ⟨hyΔ, fun hb' ↦ h₁ (hb ▸ hb')⟩
          obtain ⟨z, hzi, hze⟩ := mem_closure_iff.mp (IsLink.right_mem_closure hl) _
            (hd.isOpen_discInt hman) hyi
          exact disjoint_left.mp heout hze hzi.1

omit [T2Space S] in
/-- An arc is *inner* or *outer*: this is the sentence of the paper after the definition of arcs. -/
theorem IsArcOn.side {a b : Shat} {P : GraphWalk D.rad.G.toGraph a b} (hP : IsArcOn D.rad.G Dv F P)
  (hDv : Dv.IsSubdrawing D.rad.G) (hd : IsClosedDisc Δv)
    (hb : discBd Δv = Dv.U) : (∀ e ∈ P.edges, e ⊆ discInt Δv) ∨ (∀ e ∈ P.edges, Disjoint e Δv) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hne := hP.ne
  have hs := hP.simple
  have hinner := hP.inner
  have hoff := hP.off
  cases P with
  | nil _ => exact absurd rfl hne
  | @cons _ y _ e hl L =>
    have hnd : (GraphWalk.cons hl L).support.Nodup := hs
    simp only [GraphWalk.support_cons, List.nodup_cons] at hnd
    have heoff := hoff e (by simp)
    have hmid : ∀ z ∈ L.support, z ≠ _ → z ∉ Dv.V := fun z hz hzb hzV ↦ by
      rcases hinner z (by simp [hz]) hzV with rfl | h₁
      · exact hnd.1 hz
      · exact hzb h₁
    have hIH := side_of_walk (D := D) hDv hd hb L hnd.2 hmid fun f hf ↦ hoff f (by simp [hf])
    have hrest : y = b → ∀ f ∈ L.edges, False := fun hyb f hf ↦ by
      subst hyb
      rw [(simple_self hnd.2).1] at hf
      cases hf
    have hstep : y = b ∨ y ∉ Dv.U := by
      by_cases hyb : y = b
      · exact .inl hyb
      · exact .inr fun hu ↦ hmid y L.start_mem_support hyb (mem_V_of_mem_U hDv hu hl.2.2.1)
    rcases edge_inside_or_off hT hDv hd hb hl.1 heoff with h₁ | h₁
    · left
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact h₁
      · rcases hstep with h₂ | h₂
        · exact (hrest h₂ f hf).elim
        · exact hIH.1 ⟨closure_minimal (h₁.trans (discInt_subset _)) hd.isClosed
            (IsLink.right_mem_closure hl), fun hb' ↦ h₂ (hb ▸ hb')⟩ f hf
    · right
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact h₁
      · rcases hstep with h₂ | h₂
        · exact (hrest h₂ f hf).elim
        · refine hIH.2 (fun hyΔ ↦ ?_) f hf
          have hyi : y ∈ discInt Δv := ⟨hyΔ, fun hb' ↦ h₂ (hb ▸ hb')⟩
          have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
          obtain ⟨z, hzi, hze⟩ := mem_closure_iff.mp (IsLink.right_mem_closure hl) _
            (hd.isOpen_discInt hman) hyi
          exact disjoint_left.mp h₁ hze hzi.1

omit [T2Space Shat] in
/-- The reverse of an arc is an arc. -/
theorem IsArcOn.reverse {G Dv F : Drawing Shat} {a b : Shat} {P : GraphWalk G.toGraph a b}
  (hP : IsArcOn G Dv F P) : IsArcOn G Dv F P.reverse := by
  refine ⟨hP.ne.symm, hP.simple.reverse, hP.right, hP.left, fun x hx hxV ↦ ?_,
    fun e he ↦ hP.off e (by simpa [GraphWalk.edges_reverse] using he),
    fun e he ↦ hP.inF e (by simpa [GraphWalk.edges_reverse] using he)⟩
  exact (hP.inner x (by simpa [GraphWalk.support_reverse] using hx) hxV).symm

namespace IsFar

variable (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
include hf

/-- If `H` is a circuit then `h ∉ U(F)`, and if `h ∈ ins(F)` then `H` is the point `h`, and `h ∈
V(F)`: this is the first line of the proof of step (7). -/
theorem point_of_mem_ins (hm : h ∈ D.ins F) : H.V = {h} ∧ H.V.ncard = 1 ∧ h ∈ F.U := by
  have : ConnectedSpace Shat := cap.connected
  rcases hf.hub with ⟨h₁, h₂⟩ | ⟨hH, -, hi⟩
  · exact ⟨h₁, h₂, hf.enc.hub_point h₂ (by rw [h₁]; rfl) hm⟩
  · have := hf.enc.hub_circuit hH
    have h₃ : h ∈ D.ins F ∩ D.ins H := ⟨hm, hi.1⟩
    rw [this] at h₃
    obtain ⟨-, -, -, hcir, hlt, -⟩ := id hH
    exact absurd (D.ins_spec hcir hlt).2.2.2.1 fun hb ↦ hi.2 (hb ▸ h₃.2)

/-- If `h ∈ Δ_v` then `h ∈ U(D_v)`. -/
theorem mem_Dv_of_mem (hm : h ∈ Δv) : h ∈ Dv.U := by
  have : ConnectedSpace Shat := cap.connected
  have hbv := hf.enc.sector.Dv_U
  have hW := hf.enc.wheel
  by_contra hn
  have hi : h ∈ discInt Δv := ⟨hm, fun hb ↦ hn (hbv ▸ hb)⟩
  rcases hf.hub with ⟨h₁, h₂⟩ | ⟨hH, hle, hi'⟩
  · rcases hf.enc.sector.cases hW hf.enc.hbdS hf.enc.hin with ⟨v₁, v₂, u, h', f₁, f₂, A₁, A₂, T,
      hfan, hC, -, -⟩ | ⟨v₁, v₂, h₁', h₂', f₁, f₂, K₁, K₂, P, -, -, -, -, -, h1, h2, hdis, -, -, -⟩
    · have hmain := (hfan.main hC hf.enc.hopt hf.enc.sector.is_disc hf.enc.sector.Δv_sub hbv.symm).1
      have hu := hmain h ⟨hm, H.V_subset_U (by rw [h₁]; rfl)⟩
      subst hu
      exact hn (Dv.V_subset_U ((hC.mem_V _).mpr (.inr (.inl A₁.end_mem_support))))
    · have e₁ := h1.2.h_mem
      have e₂ := h2.2.h_mem
      rw [h₁] at e₁ e₂
      obtain rfl : h₁' = h := e₁
      obtain rfl : h₂' = h₁' := e₂
      exact hdis _ K₁.end_mem_support K₂.end_mem_support
  · exact disjoint_left.mp (hf.enc.sector.interior_off_hub hf.enc.hopt hf.enc.hbdS hf.enc.hin hH
      hle) hi' hi

theorem ne_Dv : ¬ ∀ e ∈ C.E, e ∈ Dv.E := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  intro hE
  have hC := hf.circuit
  have hDv := hf.enc.sector.Dv_circuit
  have heq := circuit_E_eq_of_subset hDv.2 hC.2 hDv.1 hC.1 hE
  obtain rfl := circuit_eq_of_E hC.2 hDv.2 hC.1 hDv.1 heq
  have hΔ : Δ = Δv := disc_eq_of_subset_disc hT hf.amb.disc hf.disc hf.enc.sector.is_disc hf.sub
    (hf.v_sub.trans hf.sub)
    (hf.bd.trans hf.enc.sector.Dv_U)
  exact hf.not_C (hf.mem_Dv_of_mem (hΔ ▸ hf.mem_Δ))

theorem ne_F : ¬ ∀ e ∈ C.E, e ∈ F.E := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  intro hE
  have hC := hf.circuit
  have hFi := hf.enc.isInsOf_F
  have heq := circuit_E_eq_of_subset hFi.1.2 hC.2 hFi.1.1 hC.1 hE
  obtain rfl := circuit_eq_of_E hC.2 hFi.1.2 hC.1 hFi.1.1 heq
  have hΔ : Δ = D.ins C := hf.ins_C.symm
  exact hf.not_C (hf.point_of_mem_ins (hΔ ▸ hf.mem_Δ)).2.2

/-- The first half of the remark after the definition of arcs: `Δ_v ⊄ ins(F)`. -/
theorem not_v_sub : ¬ Δv ⊆ D.ins F := fun hsub ↦ by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hFi := hf.enc.isInsOf_F
  exact hf.ne_F (edges_of_nested hT hFi.1 hf.circuit hFi.2.2.1 hFi.2.2.2.1
    hf.enc.sector.Dv_U.symm hsub hf.disc hf.bd hf.F_sub
    fun e he ↦ (hf.edges e he).symm)

/-- `ins(F) ⊄ Δ_v`. -/
theorem not_F_sub : ¬ D.ins F ⊆ Δv := fun hsub ↦ by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hFi := hf.enc.isInsOf_F
  exact hf.ne_Dv (edges_of_nested hT hf.enc.sector.Dv_circuit hf.circuit
    hf.enc.sector.is_disc hf.enc.sector.Dv_U.symm hFi.2.2.2.1 hsub hf.disc hf.bd hf.v_sub hf.edges)

/-- `F` has an edge outside `Δ_v`. -/
theorem exists_edge_out : ∃ e ∈ F.E, Disjoint e Δv := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hFi := hf.enc.isInsOf_F
  have hΔv := hf.enc.sector.is_disc
  by_contra hn
  push Not at hn
  have hU : F.U ⊆ Δv := U_of_edges hFi.1.2 hΔv.isClosed fun e he ↦ by
    have hG := hFi.1.1.2 he
    by_cases heD : e ∈ Dv.E
    · intro x hx
      have : x ∈ discBd Δv := by
        rw [← hf.enc.sector.Dv_U]
        exact Dv.closure_subset_U heD (subset_closure hx)
      exact Surface.discBd_subset _ this
    · rcases edge_inside_or_off hT hf.enc.sector.Dv_circuit.1 hΔv hf.enc.sector.Dv_U.symm hG heD
        with h₁ | h₁
      · exact h₁.trans (discInt_subset _)
      · exact absurd h₁ (hn e he)
  have hsF : D.ins F ⊆ Δ₀ := hf.F_sub.trans hf.sub
  exact hf.not_F_sub (disc_subset_of_bd hT hf.amb.disc hFi.2.2.1 hΔv hsF (hf.v_sub.trans hf.sub)
    (hFi.2.2.2.1 ▸ hU))

/-- `F` has an edge inside `Δ_v`. -/
theorem exists_edge_in : ∃ e ∈ F.E, e ⊆ discInt Δv := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hFi := hf.enc.isInsOf_F
  have hΔv := hf.enc.sector.is_disc
  have hbv := hf.enc.sector.Dv_U.symm
  by_contra hn
  push Not at hn
  have hUd : F.U ⊆ (discInt Δv)ᶜ := U_of_edges hFi.1.2 (hΔv.isOpen_discInt hman).isClosed_compl fun
    e he x hx hxi ↦ by
    have hG := hFi.1.1.2 he
    by_cases heD : e ∈ Dv.E
    · have : x ∈ discBd Δv := by
        rw [hbv]
        exact Dv.closure_subset_U heD (subset_closure hx)
      exact hxi.2 this
    · rcases edge_inside_or_off hT hf.enc.sector.Dv_circuit.1 hΔv hbv hG heD with h₁ | h₁
      · exact hn e he h₁
      · exact disjoint_left.mp h₁ hx hxi.1
  obtain ⟨c, hc, hc₁, hc₂⟩ := hf.enc.exists_edge
  obtain ⟨y, hy⟩ := hc.1
  have hsub : discInt Δv ⊆ discInt (D.ins F) := (isSide_int hT hFi.2.2.1 hFi.2.2.2.1).subset
    hΔv.isPreconnected_discInt
    (disjoint_left.mpr fun z hz hzU ↦ hUd hzU hz) ⟨_, hc₂ (mem_image_of_mem _ hy), hc₁
      (mem_image_of_mem _ hy)⟩
  refine hf.not_v_sub ?_
  rw [← closure_discInt hΔv]
  exact closure_minimal (hsub.trans (discInt_subset _)) hFi.2.2.1.isClosed

/-- There is an outer arc. -/
theorem exists_outer_arc : ∃ (a b : Shat) (P : GraphWalk D.rad.G.toGraph a b), IsArcOn D.rad.G Dv F
  P ∧ ∀ e ∈ P.edges, Disjoint e Δv := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hFi := hf.enc.isInsOf_F
  have hF := hFi.1
  have hDv := hf.enc.sector.Dv_circuit
  have hΔv := hf.enc.sector.is_disc
  have hbv := hf.enc.sector.Dv_U.symm
  obtain ⟨e₀, he₀, he₀d⟩ := hf.exists_edge_out
  obtain ⟨e₁, he₁, he₁i⟩ := hf.exists_edge_in
  obtain ⟨a, b, hne, hl⟩ : ∃ a b, a ≠ b ∧ D.rad.G.toGraph.IsLink e₁ a b := by
    obtain ⟨p, hp, q, hq, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e₁ (hF.1.2 he₁)
    have hpm : p ∈ closure e₁ ∩ D.rad.G.V := by
      rw [hcap]
      exact .inl rfl
    have hqm : q ∈ closure e₁ ∩ D.rad.G.V := by
      rw [hcap]
      exact .inr rfl
    exact ⟨p, q, fun h' ↦ hq.2 (h' ▸ hp), hF.1.2 he₁, hpm.2, hqm.2, hcap⟩
  have hclΔ : closure e₁ ⊆ Δv := closure_minimal (he₁i.trans (discInt_subset _)) hΔv.isClosed
  have hends := Drawing.IsLink.mem_V_of_sub hF.1 hl he₁
  obtain ⟨W₁, W₂, hs⟩ := exists_splits hF.2 hF.1 hends.1 hends.2 hne
  obtain ⟨u, v, M, hu, hv, hMs, he₀M, hME, hinner⟩ : ∃ (u v : Shat) (M : GraphWalk D.rad.G.toGraph
    u v), u ∈ Δv ∧ v ∈ Δv ∧ M.IsSimple ∧ e₀ ∈ M.edges ∧
      (∀ e ∈ M.edges, e ∈ F.E) ∧ ∀ x ∈ M.support, x ∈ Δv → x = u ∨ x = v := by
    rcases (hs.E e₀).mp he₀ with h₁ | h₁
    · obtain ⟨u, v, M, h₁', h₂, h₃, h₄, h₅, h₆⟩ := GraphWalk.exists_piece W₁ hs.s₁ (hclΔ
        (IsLink.left_mem_closure hl)) (hclΔ (IsLink.right_mem_closure hl)) h₁
      exact ⟨u, v, M, h₁', h₂, h₃, h₄, fun e he ↦ (hs.E e).mpr (.inl (h₅ e he)), h₆⟩
    · obtain ⟨u, v, M, h₁', h₂, h₃, h₄, h₅, h₆⟩ := GraphWalk.exists_piece W₂ hs.s₂ (hclΔ
        (IsLink.right_mem_closure hl)) (hclΔ (IsLink.left_mem_closure hl)) h₁
      exact ⟨u, v, M, h₁', h₂, h₃, h₄, fun e he ↦ (hs.E e).mpr (.inr (h₅ e he)), h₆⟩
  have huv : u ≠ v := by
    rintro rfl
    rw [(simple_self hMs).1] at he₀M
    cases he₀M
  have hcase : ∀ e ∈ F.E, closure e ⊆ Δv ∨ Disjoint e Δv := fun e he ↦ by
    by_cases heC : e ∈ Dv.E
    · refine .inl ((Dv.closure_subset_U heC).trans ?_)
      rw [← hbv]
      exact Surface.discBd_subset _
    · rcases edge_inside_or_off hT hDv.1 hΔv hbv (hF.1.2 he) heC with h₁ | h₁
      · exact .inl (closure_minimal (h₁.trans (discInt_subset _)) hΔv.isClosed)
      · exact .inr h₁
  have hMoff : ∀ e ∈ M.edges, Disjoint e Δv := fun e he ↦ by
    rcases GraphWalk.edge_has_middle M hMs huv he with h₁ | ⟨x, hxs, hxc, hxu, hxv⟩
    · rw [h₁] at he₀M
      obtain rfl : e₀ = e := by simpa using he₀M
      exact he₀d
    · refine (hcase e (hME e he)).resolve_left fun h' ↦ ?_
      rcases hinner x hxs (h' hxc) with h'' | h''
      · exact hxu h''
      · exact hxv h''
  have hstart : ∀ {a b : Shat} (N : GraphWalk D.rad.G.toGraph a b), a ≠ b →
    (∀ e ∈ N.edges, e ∈ F.E) → (∀ e ∈ N.edges, Disjoint e Δv) → a ∈ Δv → a ∈ Dv.V := by
    intro a b N hab hE hD haΔ
    cases N with
    | nil _ => exact absurd rfl hab
    | @cons _ y _ e hl r =>
      have hdis := hD e (by simp)
      have hac := IsLink.left_mem_closure hl
      have haf : a ∈ frontier Δv := by
        refine ⟨subset_closure haΔ, fun hi ↦ ?_⟩
        obtain ⟨y, hyi, hye⟩ := mem_closure_iff.mp hac _ isOpen_interior hi
        exact disjoint_left.mp hdis hye (interior_subset hyi)
      rw [IsClosedDisc.frontier_eq_discBd hT hΔv, hbv] at haf
      exact mem_V_of_mem_U hDv.1 haf hl.2.1
  have huD := hstart M huv hME hMoff hu
  have hvD := hstart M.reverse huv.symm (fun e he ↦ hME e (by simpa [GraphWalk.edges_reverse] using
    he))
    (fun e he ↦ hMoff e (by simpa [GraphWalk.edges_reverse] using he)) hv
  have hsubΔ : Dv.V ⊆ Δv := fun x hx ↦ by
    have : x ∈ discBd Δv := by
      rw [hbv]
      exact Dv.V_subset_U hx
    exact Surface.discBd_subset _ this
  refine ⟨u, v, M, ⟨huv, hMs, huD, hvD, fun x hx hxV ↦ hinner x hx (hsubΔ hxV),
    fun e he heD ↦ ?_, hME⟩, hMoff⟩
  obtain ⟨x, hx⟩ := (hF.1.2 (hME e he)).1
  exact disjoint_left.mp (hMoff e he) hx (hsubΔ.trans subset_rfl |> fun _ ↦ by
    have : x ∈ discBd Δv := by
      rw [hbv]
      exact Dv.closure_subset_U heD (subset_closure hx)
    exact Surface.discBd_subset _ this)

/-- Every edge of `F` off `D_v` lies on an arc. -/
theorem exists_arc_through {e : Set Shat} (he : e ∈ F.E) (heD : e ∉ Dv.E) : ∃ (a b : Shat)
  (P : GraphWalk D.rad.G.toGraph a b), IsArcOn D.rad.G Dv F P ∧ e ∈ P.edges := by
  classical
  have hF := hf.enc.isInsOf_F.1
  obtain ⟨u, v, O, hO, -⟩ := hf.exists_outer_arc
  have hstart : ∀ {a b : Shat} (N : GraphWalk D.rad.G.toGraph a b), a ≠ b →
    (∀ e ∈ N.edges, e ∈ F.E) → a ∈ F.V := by
    intro a b N hab hE
    cases N with
    | nil _ => exact absurd rfl hab
    | @cons _ y _ e hl r => exact (Drawing.IsLink.mem_V_of_sub hF.1 hl (hE e (by simp))).1
  have huF := hstart O hO.ne hO.inF
  have hvF := hstart O.reverse hO.ne.symm fun e he ↦ hO.inF e (by simpa [GraphWalk.edges_reverse]
    using he)
  obtain ⟨W₁, W₂, hs⟩ := exists_splits hF.2 hF.1 huF hvF hO.ne
  obtain ⟨a, b, M, ha, hb, hMs, heM, hME, hinner⟩ : ∃ (a b : Shat) (M : GraphWalk D.rad.G.toGraph a
    b), a ∈ Dv.V ∧ b ∈ Dv.V ∧ M.IsSimple ∧ e ∈ M.edges ∧
      (∀ f ∈ M.edges, f ∈ F.E) ∧ ∀ x ∈ M.support, x ∈ Dv.V → x = a ∨ x = b := by
    rcases (hs.E e).mp he with h₁ | h₁
    · obtain ⟨u, v, M, h₁', h₂, h₃, h₄, h₅, h₆⟩ := GraphWalk.exists_piece W₁ hs.s₁ hO.left hO.right
        h₁
      exact ⟨u, v, M, h₁', h₂, h₃, h₄, fun e he ↦ (hs.E e).mpr (.inl (h₅ e he)), h₆⟩
    · obtain ⟨u, v, M, h₁', h₂, h₃, h₄, h₅, h₆⟩ := GraphWalk.exists_piece W₂ hs.s₂ hO.right hO.left
        h₁
      exact ⟨u, v, M, h₁', h₂, h₃, h₄, fun e he ↦ (hs.E e).mpr (.inr (h₅ e he)), h₆⟩
  have hab : a ≠ b := by
    rintro rfl
    rw [(simple_self hMs).1] at heM
    cases heM
  refine ⟨a, b, M, ⟨hab, hMs, ha, hb, hinner, fun f hfM hfD ↦ ?_, hME⟩, heM⟩
  rcases GraphWalk.edge_has_middle M hMs hab hfM with h₁ | ⟨x, hxs, hxc, hxu, hxv⟩
  · rw [h₁] at heM
    obtain rfl : e = f := by simpa using heM
    exact heD hfD
  · have hxV : x ∈ Dv.V := by
      have hG := hf.enc.sector.Dv_circuit.1
      have hxG : x ∈ D.rad.G.V := M.mem_vertexSet_of_mem_support hxs
      exact mem_V_of_mem_U hG (Dv.closure_subset_U hfD hxc) hxG
    rcases hinner x hxs hxV with h₁ | h₁
    · exact hxu h₁
    · exact hxv h₁

/-- There is an inner arc. -/
theorem exists_inner_arc : ∃ (a b : Shat) (P : GraphWalk D.rad.G.toGraph a b), IsArcOn D.rad.G Dv F
  P ∧ ∀ e ∈ P.edges, e ⊆ discInt Δv := by
  have hDv := hf.enc.sector.Dv_circuit
  have hΔv := hf.enc.sector.is_disc
  have hbv := hf.enc.sector.Dv_U.symm
  obtain ⟨e, he, hei⟩ := hf.exists_edge_in
  have heD : e ∉ Dv.E := fun h' ↦ by
    obtain ⟨x, hx⟩ := (hDv.1.2 h').1
    exact (hei hx).2 (hbv ▸ Dv.closure_subset_U h' (subset_closure hx))
  obtain ⟨a, b, P, hP, heP⟩ := hf.exists_arc_through he heD
  refine ⟨a, b, P, hP, ?_⟩
  rcases IsArcOn.side (D := D) hP hDv.1 hΔv hbv with h₁ | h₁
  · exact h₁
  · obtain ⟨x, hx⟩ := (hf.enc.isInsOf_F.1.1.2 he).1
    exact absurd (hei hx).1 (disjoint_left.mp (h₁ e heP) hx)

end IsFar

end TangleDatum

end GraphMinor.GM19
