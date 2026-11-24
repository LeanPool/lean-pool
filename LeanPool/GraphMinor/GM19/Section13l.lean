/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13k

import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XIX, Section 13: step (4) of (13.6)

We find a closed disc `Δ₀` that holds `ins(F)`, `bd(W)`, the hub and the spokes, and that is closed
under taking the inside of a short
circuit. If `ins(F) ⊆ W` this is `W`. Otherwise `F` has a vertex `z*` on `bd(W)`, and all these
things are close to `z*` in the metric of
`𝒯`, so (7.1) gives `Δ₀`.
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
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}

/-- A vertex of a spoke other than its first one is not on `bd(W)`. For a vertex of `Γ` this is the
bound on the distance from `bd(W)` to
`H`, and for a region it is (13.1). -/
theorem IsSpokeWalk.tail_off_bd (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {v h y : Shat} {K : GraphWalk
      D.rad.G.toGraph v h} (hK : D.IsSpokeWalk W H K)
    (hy : y ∈ K.support) (hne : y ≠ v) : y ∉ discBd W := by
  intro hyb
  have : ConnectedSpace Shat := cap.connected
  have hl := (hW.spoke_length hK).1
  have hh := hK.2.h_mem
  obtain ⟨A, B, rfl⟩ := K.exists_append_of_mem hy
  rw [GraphWalk.length_append] at hl
  have hA : 1 ≤ A.length := by
    by_contra hn
    cases A with
    | nil _ => exact hne rfl
    | cons _ _ => simp at hn
  by_cases hyh : y ∈ D.P.Γ.hatV cap
  · have h₂ := two_le_of_hatV D A hK.2.v_mem.1 hyh hne.symm
    have h₃ := hW.walk_ge ⟨hyh, hyb⟩ hh B
    omega
  · have hyG : y ∈ D.rad.G.V := A.mem_vertexSet_of_mem_support A.end_mem_support
    obtain ⟨P, hP, hle⟩ := exists_path_of_walk B
    exact theorem_13_1_proof hW hbdS hin ⟨hyG, hyh⟩ hyb ⟨P, h, hh, hP, by omega⟩

/-- A spoke lies in `W`: we go along it from the hub, and an edge at a point inside `W` lies in `W`.
-/
theorem IsSpokeWalk.subset_W (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {v h : Shat} {K : GraphWalk
      D.rad.G.toGraph v h} (hK : D.IsSpokeWalk W H K) :
    (walkDrawing D.rad.G K).U ⊆ W := by
  have key : ∀ {a b : Shat} (L : GraphWalk D.rad.G.toGraph a b), L.IsSimple →
    (∀ y ∈ L.support, y ≠ a → y ∉ discBd W) → b ∈ W →
      (walkDrawing D.rad.G L).U ⊆ W := by
    intro a b L
    induction L with
    | nil h' =>
      intro _ _ hb x hx
      rw [mem_walkDrawing_U] at hx
      rcases hx with hx | ⟨e, he, -⟩
      · obtain rfl : x = _ := by simpa using hx
        exact hb
      · simp at he
    | @cons a y b e hl L ih =>
      intro hs hoff hb
      have hnd : (GraphWalk.cons hl L).support.Nodup := hs
      simp only [GraphWalk.support_cons, List.nodup_cons] at hnd
      have hU := ih hnd.2 (fun z hz hne ↦ hoff z (by simp [hz]) fun h' ↦ hnd.1 (h' ▸ hz)) hb
      have hyU : y ∈ (walkDrawing D.rad.G L).U := by
        rw [mem_walkDrawing_U]
        exact .inl L.start_mem_support
      have hyW := hU hyU
      have hya : y ≠ a := fun h' ↦ hnd.1 (h' ▸ L.start_mem_support)
      have hyb := hoff y (by simp [L.start_mem_support]) hya
      have hyc : y ∈ closure e := by
        have : y ∈ closure e ∩ D.rad.G.V := by
          rw [hl.2.2.2]
          exact .inr rfl
        exact this.1
      have hsub : closure e ⊆ W := by
        rcases hW.edge_side hl.1 with h₁ | h₁
        · exact closure_minimal h₁ hW.is_disc.isClosed
        · exact absurd (hW.mem_bd_of_closure h₁ hyc hyW) hyb
      intro x hx
      rw [mem_walkDrawing_U] at hx
      rcases hx with hx | ⟨f, hf, hxf⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hsub (by
            have : x ∈ closure e ∩ D.rad.G.V := by
              rw [hl.2.2.2]
              exact .inl rfl
            exact this.1)
        · exact hU ((mem_walkDrawing_U _ _).mpr (.inl hx))
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact hsub hxf
        · exact hU ((mem_walkDrawing_U _ _).mpr (.inr ⟨f, hf, hxf⟩))
  exact key K hK.1 (fun y hy hne ↦ hK.tail_off_bd hW hbdS hin hy hne) ((hW.H_in_int
    (H.V_subset_U hK.2.h_mem)).1)

/-- A walk that stays close to `z` in the metric of `𝒯` lies in the set `Λ` that holds the atoms
close to `z`. -/
theorem walk_subset_of_dist {z Λ : Set Shat} {n : ℕ} (hrep : 4 ≤ D.rep)
    (hclose : ∀ a ∈ D.P.Γ.atoms cap, D.dist z a ≤ n → a ⊆ Λ)
    {a b : Shat} (K : GraphWalk D.rad.G.toGraph a b) (ha : a ∈ D.rad.G.V) (hd : D.dist z
      (D.rad.atomOf a) + K.length ≤ n) :
    (walkDrawing D.rad.G K).U ⊆ Λ := by
  induction K with
  | nil h' =>
    intro x hx
    rw [mem_walkDrawing_U] at hx
    rcases hx with hx | ⟨e, he, -⟩
    · obtain rfl : x = _ := by simpa using hx
      exact hclose _ (D.atomOf_mem ha) (by simpa using hd) (D.mem_atomOf ha)
    · simp at he
  | @cons a y b e hl L ih =>
    rw [GraphWalk.length_cons] at hd
    have hyG : y ∈ D.rad.G.V := hl.2.2.1
    have h₁ : D.dist (D.rad.atomOf a) (D.rad.atomOf y) ≤ 1 := D.dist_atomOf_le_of_walk (.cons hl
      (.nil hyG)) (by
      rw [GraphWalk.length_cons]
      change 0 + 1 < D.rep
      omega)
    have h₂ := D.dist_triangle hrep (a := z) (c := D.rad.atomOf y) (D.atomOf_mem ha)
    have hU := ih hyG (by omega)
    have haΛ := hclose _ (D.atomOf_mem ha) (by omega) (D.mem_atomOf ha)
    have hyΛ := hclose _ (D.atomOf_mem hyG) (by omega) (D.mem_atomOf hyG)
    have hsub : closure e ⊆ Λ := by
      intro x hx
      obtain ⟨p, hp, q, hq, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e hl.1
      have hpm : p ∈ closure e ∩ D.rad.G.V := by
        rw [hcap]
        exact .inl rfl
      have hqm : q ∈ closure e ∩ D.rad.G.V := by
        rw [hcap]
        exact .inr rfl
      have hqa : q = a ∨ q = y := by
        have : q ∈ ({a, y} : Set Shat) := by
          rw [← hl.2.2.2]
          exact hqm
        exact this
      rcases closure_edge_subset hl.1 hx with hxe | hxV
      · have hsub := edge_subset_regionOf D hq hl.1 hqm.1 hxe
        rw [← atomOf_Rstar D hq] at hsub
        rcases hqa with rfl | rfl
        · exact hclose _ (D.atomOf_mem ha) (by omega) hsub
        · exact hclose _ (D.atomOf_mem hyG) (by omega) hsub
      · have : x ∈ ({a, y} : Set Shat) := by
          rw [← hl.2.2.2]
          exact ⟨hx, hxV⟩
        rcases this with rfl | rfl
        · exact haΛ
        · exact hyΛ
    intro x hx
    rw [mem_walkDrawing_U] at hx
    rcases hx with hx | ⟨f, hf, hxf⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact haΛ
      · exact hU ((mem_walkDrawing_U _ _).mpr (.inl hx))
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact hsub hxf
      · exact hU ((mem_walkDrawing_U _ _).mpr (.inr ⟨f, hf, hxf⟩))

/-- Two vertices of a circuit are joined by a walk along the circuit of at most half its length. -/
theorem exists_short_walk {G F : Drawing Shat} (hF : F.IsCircuitOf G) {a b : Shat} (ha : a ∈ F.V)
  (hb : b ∈ F.V) :
    ∃ T : GraphWalk G.toGraph a b, 2 * T.length ≤ F.E.ncard ∧ ∀ e ∈ T.edges, e ∈ F.E := by
  by_cases hab : a = b
  · subst hab
    refine ⟨.nil (hF.1.1 ha), ?_, fun e he ↦ ?_⟩
    · change 2 * 0 ≤ _
      omega
    · cases he
  · obtain ⟨W₁, W₂, hs⟩ := exists_splits hF.2 hF.1 ha hb hab
    have hc := hs.card_add
    have h₁ : (edgeSet W₁).ncard = W₁.length := by
      rw [← ncard_walk_E G hs.s₁, walkDrawing_E]
      rfl
    have h₂ : (edgeSet W₂).ncard = W₂.length := by
      rw [← ncard_walk_E G hs.s₂, walkDrawing_E]
      rfl
    have h₃ : F.length = F.E.ncard := rfl
    by_cases hle : W₁.length ≤ W₂.length
    · exact ⟨W₁, by omega, fun e he ↦ (hs.E e).mpr (.inl he)⟩
    · refine ⟨W₂.reverse, ?_, fun e he ↦ (hs.E e).mpr (.inr ?_)⟩
      · rw [GraphWalk.length_reverse]
        omega
      · rw [GraphWalk.edges_reverse, List.mem_reverse] at he
        exact he

theorem U_reverse (G : Drawing Shat) {a b : Shat} (K : GraphWalk G.toGraph a b) :
  (walkDrawing G K.reverse).U = (walkDrawing G K).U := by
  ext x
  simp only [mem_walkDrawing_U, GraphWalk.support_reverse, GraphWalk.edges_reverse,
    List.mem_reverse]

/-- `Δ₀` as in step (4) of the proof of (13.6). The paper also has `W ⊆ Δ₀`. For that it needs that
the discs `ins(D_{v'})` and `ins(H)`
fill `W`, and it uses `W ⊆ Δ₀` only to get `Δ ⊆ W` in step (6). There we use the wheel condition on
short circuits instead. -/
structure IsAmbientDisc (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat) (ρ : ℕ)
  (F : Drawing Shat) (Δ₀ : Set Shat) : Prop where
  disc : IsClosedDisc Δ₀
  ins_F : D.ins F ⊆ Δ₀
  bd_W : discBd W ⊆ Δ₀
  hub : H.U ⊆ Δ₀
  spoke : ∀ (v h : Shat) (K : GraphWalk D.rad.G.toGraph v h), D.IsSpokeWalk W H K →
    (walkDrawing D.rad.G K).U ⊆ Δ₀
  short : ∀ C : Drawing Shat, C.IsCircuitOf D.rad.G → C.E.ncard ≤ 4 * ρ + 4 → C.U ⊆ Δ₀
    → D.ins C ⊆ Δ₀

/-- The second case of the paper's proof of step (4): `F` has a vertex `z*` on `bd(W)`. -/
theorem IsAmbientDisc.of_vertex (hW : D.IsWheelHubOfRadius W H ρ) (hrep : 6 * ρ + 14 ≤ D.rep)
    (hF : F.IsCircuitOf D.rad.G) (hFc : F.E.ncard ≤ 4 * ρ + 4) (hHc : H.V.ncard = 1 ∨
      (H.IsCircuitOf D.rad.G ∧ H.E.ncard ≤ 4 * ρ + 4))
    {zs : Shat} (hzF : zs ∈ F.V) (hzb : zs ∈ discBd W) : ∃ Δ₀, D.IsAmbientDisc W H ρ F Δ₀ := by
  classical
  have hS := χ.isSurface
  have hρ := hW.pos_ρ
  have hr4 : 4 ≤ D.rep := by omega
  have hzG : zs ∈ D.rad.G.V := hF.1.1 hzF
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
  obtain ⟨C₀, Λ, -, -, -, hΛc, hsb, hdiff, -, -, -, hclose, hins⟩ :=
    theorem_7_1_proof D (D.atomOf_mem hzG) (κ := 4 * ρ + 6) (by omega) (by omega) hSk
  set z := D.rad.atomOf zs with hz
  have hclose' : ∀ a ∈ D.P.Γ.atoms cap, D.dist z a ≤ 4 * ρ + 4 → a ⊆ Λ := fun a ha hd ↦ hclose a ha
    (by omega)
  have hsubcl : Λ ⊆ closure Λ := subset_closure
  have hK := fun {a b : Shat} (K : GraphWalk D.rad.G.toGraph a b) (ha : a ∈ D.rad.G.V)
    (hd : D.dist z (D.rad.atomOf a) + K.length ≤ 4 * ρ + 4) ↦
    walk_subset_of_dist (D := D) hr4 hclose' K ha hd
  have hstep : ∀ {a b : Shat} {j : ℕ} (T : GraphWalk D.rad.G.toGraph a b), a ∈ D.rad.G.V → D.dist z
    (D.rad.atomOf a) ≤ j → T.length < D.rep →
      D.dist z (D.rad.atomOf b) ≤ j + T.length := by
    intro a b j T ha hd hlt
    have h₁ := D.dist_atomOf_le_of_walk T hlt
    have h₂ := D.dist_triangle hr4 (a := z) (c := D.rad.atomOf b) (D.atomOf_mem ha)
    omega
  -- the distance from `z` to the hub
  have hbdv : ∀ {v : Shat}, v ∈ (cap.emb '' D.Γ.V) ∩ discBd W → ∃ h₀ ∈ H.V, ∃ T : GraphWalk
    D.rad.G.toGraph v h₀, T.length ≤ ρ := by
    intro v hv
    obtain ⟨P, h₀, hh, hP, hle⟩ := (hW.bd_dist v hv).1
    obtain ⟨K, hKs, -, hE⟩ := Drawing.IsPathOf.exists_simple_walk hP
    refine ⟨h₀, hh, K, ?_⟩
    rw [← ncard_walk_E _ hKs]
    have : (walkDrawing D.rad.G K).E = P.E := by
      ext e
      rw [hE e, walkDrawing_E]
      rfl
    rwa [this]
  obtain ⟨v, hv, w, hzw, hwG, hcase⟩ := hW.exists_atom_on_bd hzb
  have hzw' : D.rad.atomOf w = z := D.atom_eq_of_mem (D.atomOf_mem hwG) (D.atomOf_mem hzG) hzw
    (D.mem_atomOf hzG)
  have hvG : v ∈ D.rad.G.V := D.rad.isPreRadial.2.1 hv.1
  have hone : ∀ {a b : Shat} {g : Set Shat}, D.rad.G.toGraph.IsLink g a b → D.dist (D.rad.atomOf a)
    (D.rad.atomOf b) ≤ 1 := fun hl ↦
    D.dist_atomOf_le_of_walk (.cons hl (.nil hl.2.2.1)) (by
      rw [GraphWalk.length_cons]
      change 0 + 1 < D.rep
      omega)
  have hd₁ : D.dist z (D.rad.atomOf v) ≤ 1 := by
    rw [← hzw']
    rcases hcase with rfl | ⟨g, hl⟩
    · rw [D.dist_self]
      omega
    · rw [D.dist_comm]
      exact hone hl
  obtain ⟨h₀, hh₀, T₀, hT₀⟩ := hbdv hv
  have hh₀G : h₀ ∈ D.rad.G.V := hW.H_sub.1 hh₀
  have hd₂ : D.dist z (D.rad.atomOf h₀) ≤ 1 + T₀.length := hstep T₀ hvG hd₁ (by omega)
  have hhub : ∀ h ∈ H.V, D.dist z (D.rad.atomOf h) ≤ 3 * ρ + 3 := by
    intro h hh
    rcases hHc with hc | ⟨hc, hle⟩
    · obtain ⟨y, hy⟩ := ncard_eq_one.mp hc
      rw [hy] at hh hh₀
      obtain rfl : h = y := hh
      obtain rfl : h₀ = h := hh₀
      omega
    · obtain ⟨T, hT, -⟩ := exists_short_walk hc hh₀ hh
      have := hstep T hh₀G hd₂ (by omega)
      omega
  have hvdist : ∀ {v' : Shat}, v' ∈ (cap.emb '' D.Γ.V) ∩ discBd W → D.dist z (D.rad.atomOf v')
    ≤ 4 * ρ + 3 := by
    intro v' hv'
    obtain ⟨h', hh', T, hT⟩ := hbdv hv'
    have := hstep T.reverse (hW.H_sub.1 hh') (hhub h' hh') (by rw [GraphWalk.length_reverse]; omega)
    rw [GraphWalk.length_reverse] at this
    omega
  have hbd : discBd W ⊆ Λ := by
    intro p hp
    obtain ⟨v', hv', w', hpw, hw'G, hc'⟩ := hW.exists_atom_on_bd hp
    have hd := hvdist hv'
    refine hclose' _ (D.atomOf_mem hw'G) ?_ hpw
    rcases hc' with rfl | ⟨g, hl⟩
    · omega
    · have h₁ := hone hl
      have h₂ := D.dist_triangle hr4 (a := z) (c := D.rad.atomOf w') (D.atomOf_mem
        (D.rad.isPreRadial.2.1 hv'.1))
      omega
  have hsubd : ∀ {F₁ : Drawing Shat} {j : ℕ}, F₁.IsSubdrawing D.rad.G → (∀ a ∈ F₁.V, D.dist z
    (D.rad.atomOf a) ≤ j) → j + 1 ≤ 4 * ρ + 4 → F₁.U ⊆ Λ := by
    intro F₁ j hs hd hj x hx
    by_cases hxV : x ∈ F₁.V
    · exact hclose' _ (D.atomOf_mem (hs.1 hxV)) ((hd x hxV).trans (by omega)) (D.mem_atomOf
        (hs.1 hxV))
    · obtain ⟨g, hg, hxg⟩ := F₁.exists_edge_of_mem hx hxV
      have hgG := hs.2 hg
      obtain ⟨a, ha, q, hq, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hgG
      have ham : a ∈ closure g ∩ D.rad.G.V := by
        rw [hcap]
        exact .inl rfl
      have hqm : q ∈ closure g ∩ D.rad.G.V := by
        rw [hcap]
        exact .inr rfl
      have haF : a ∈ F₁.V := ((hs.closure_inter_V hg).symm ▸ ham : a ∈ closure g ∩ F₁.V).2
      have hl : D.rad.G.toGraph.IsLink g a q := ⟨hgG, ham.2, hqm.2, hcap⟩
      refine hK (.cons hl (.nil hqm.2)) ham.2 ?_ ?_
      · rw [GraphWalk.length_cons]
        change _ + (0 + 1) ≤ _
        have := hd a haF
        omega
      · rw [mem_walkDrawing_U]
        exact .inr ⟨g, by simp, subset_closure hxg⟩
  have hHU : H.U ⊆ Λ := hsubd hW.H_sub hhub (by omega)
  have hFU : F.U ⊆ Λ := by
    refine hsubd (j := 2 * ρ + 2) hF.1 (fun a ha ↦ ?_) (by omega)
    obtain ⟨T, hT, -⟩ := exists_short_walk hF hzF ha
    have := hstep T hzG (j := 0) (by rw [D.dist_self]) (by omega)
    omega
  refine ⟨closure Λ, hΛc, hins F hF (hFU.trans hsubcl) (by omega), hbd.trans hsubcl,
    hHU.trans hsubcl, fun v' h' T hT ↦ ?_,
    fun C hC hle hU ↦ hins C hC hU (by omega)⟩
  have hl := (hW.spoke_length hT).1
  have hHubDist := hhub h' hT.2.h_mem
  have hReverse := hK T.reverse (hW.H_sub.1 hT.2.h_mem) (by
    rw [GraphWalk.length_reverse]
    omega)
  rw [U_reverse] at hReverse
  exact hReverse.trans hsubcl

namespace IsSectorEnclave

variable (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F)
include hx

/-- If `F` has no vertex on `bd(W)`, and `ins(F)` is not in `W`, then `F` is disjoint from `W`. -/
theorem off_W (hsub : ¬ D.ins F ⊆ W) (hnot : ∀ x ∈ F.V, x ∉ discBd W) : Disjoint F.U W := by
  have : ConnectedSpace Shat := cap.connected
  have hW := hx.wheel
  obtain ⟨-, hc, hlt, -⟩ := hx.enclave
  have hle := hx.F_card
  have hstay : ∀ {a b : Shat} (T : GraphWalk D.rad.G.toGraph a b), (∀ e ∈ T.edges, e ∈ F.E)
    → a ∈ F.V → a ∉ W → b ∉ W := by
    intro a b T
    induction T with
    | nil _ => exact fun _ _ h ↦ h
    | @cons a y b e hl L ih =>
      intro hE ha hn
      have heF : e ∈ F.E := hE e (by simp)
      have hac : a ∈ closure e := by
        have : a ∈ closure e ∩ D.rad.G.V := by
          rw [hl.2.2.2]
          exact .inl rfl
        exact this.1
      have hdis : Disjoint e W := (hW.edge_side hl.1).resolve_left fun h' ↦ hn
        (closure_minimal h' hW.is_disc.isClosed hac)
      have hyF := (Drawing.IsLink.mem_V_of_sub hc.1 hl heF).2
      refine ih (fun f hf ↦ hE f (by simp [hf])) hyF fun hy ↦ hnot y hyF
        (hW.mem_bd_of_closure hdis ?_ hy)
      have : y ∈ closure e ∩ D.rad.G.V := by
        rw [hl.2.2.2]
        exact .inr rfl
      exact this.1
  obtain ⟨y, hyF, hyW⟩ : ∃ y ∈ F.V, y ∉ W := by
    by_contra hn
    push Not at hn
    exact hsub (hW.ins_subset_of_vertices hc (hle.1.trans hle.2) fun x hx _ ↦ hn x hx)
  have hall : ∀ x ∈ F.V, x ∉ W := fun x hxF ↦ by
    obtain ⟨T, -, hT⟩ := exists_short_walk hc hyF hxF
    exact hstay T hT hyF hyW
  refine disjoint_left.mpr fun x hxU hxW ↦ ?_
  by_cases hxV : x ∈ F.V
  · exact hall x hxV hxW
  · obtain ⟨g, hg, hxg⟩ := F.exists_edge_of_mem hxU hxV
    have hgG := hc.1.2 hg
    obtain ⟨a, ha, q, hq, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hgG
    have ham : a ∈ closure g ∩ D.rad.G.V := by
      rw [hcap]
      exact .inl rfl
    have haF : a ∈ F.V := ((hc.1.closure_inter_V hg).symm ▸ ham : a ∈ closure g ∩ F.V).2
    rcases hW.edge_side hgG with h₁ | h₁
    · exact hall a haF (closure_minimal h₁ hW.is_disc.isClosed ham.1)
    · exact disjoint_left.mp h₁ hxg hxW

/-- If `ins(F)` is not in `W`, then `F` has a vertex on `bd(W)`. Otherwise `W` lies inside `F`, and
this contradicts step (3). -/
theorem exists_vertex_on_bd (hsub : ¬ D.ins F ⊆ W) : ∃ z ∈ F.V, z ∈ discBd W := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hW := hx.wheel
  by_contra hn
  push Not at hn
  have hdis := hx.off_W hsub hn
  have hFi := hx.isInsOf_F
  have hO := isSide_int hT hFi.2.2.1 hFi.2.2.2.1
  obtain ⟨c, hc, hc₁, hc₂⟩ := hx.exists_edge
  obtain ⟨y, hy⟩ := hc.1
  have hyi₁ := hc₁ (mem_image_of_mem _ hy)
  have hyi₂ := hc₂ (mem_image_of_mem _ hy)
  have hWin : W ⊆ discInt (D.ins F) := hO.subset (by
    have h₁ := hW.is_disc.isPreconnected_discInt.closure
    rwa [closure_discInt hW.is_disc] at h₁) hdis.symm ⟨_, hx.sector.Δv_sub hyi₂.1, hyi₁⟩
  rcases hW.hub_cond with ⟨hc₁', -, -⟩ | ⟨hH, -, -⟩
  · obtain ⟨z, hz⟩ := ncard_eq_one.mp hc₁'
    have hh : z ∈ H.V := by
      rw [hz]
      rfl
    have hzW := hW.H_in_int (H.V_subset_U hh)
    have := hx.hub_point hc₁' hh (hWin hzW.1).1
    exact disjoint_left.mp hdis this hzW.1
  · obtain ⟨-, -, -, hcir, hlt, -⟩ := id hH
    obtain ⟨u', W', -, -, hVe, -⟩ := hcir.2
    have hu' : u' ∈ H.V := by
      rw [hVe]
      exact W'.start_mem_support
    have huW := hW.H_in_int (H.V_subset_U hu')
    have hi := D.ins_spec hcir hlt
    have hm : u' ∈ D.ins F ∩ D.ins H := ⟨(hWin huW.1).1, by
      have : u' ∈ discBd (D.ins H) := by
        rw [hi.2.2.2.1]
        exact H.V_subset_U hu'
      exact Surface.discBd_subset _ this⟩
    rw [hx.hub_circuit hH] at hm
    exact disjoint_left.mp hdis hm.1 huW.1

/-- **Step (4) of the proof of (13.6).** -/
theorem exists_ambient : ∃ Δ₀, D.IsAmbientDisc W H ρ F Δ₀ := by
  have : ConnectedSpace Shat := cap.connected
  have hW := hx.wheel
  by_cases hsub : D.ins F ⊆ W
  · exact ⟨W, hW.is_disc, hsub, Surface.discBd_subset _, hW.H_in_int.trans sdiff_subset, fun v h K
      hK ↦ hK.subset_W hW hx.hbdS hx.hin,
      fun C hC hle hU ↦ hW.ins_sub C hC hle hU⟩
  · obtain ⟨z, hzF, hzb⟩ := hx.exists_vertex_on_bd hsub
    obtain ⟨-, hc, -⟩ := hx.enclave
    have hle := hx.F_card
    refine IsAmbientDisc.of_vertex hW hx.hrep hc (hle.1.trans hle.2) ?_ hzF hzb
    rcases hW.hub_cond with ⟨h₁, -, -⟩ | ⟨hH, h₂, -⟩
    · exact .inl h₁
    · obtain ⟨-, -, -, hcir, -⟩ := id hH
      exact .inr ⟨hcir, h₂⟩

end IsSectorEnclave

end TangleDatum

end GraphMinor.GM19
