/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section6Chain
public import LeanPool.GraphMinor.GM12.MetricRadial
public import LeanPool.GraphMinor.GM15.Cited
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM10.Section6

/-!
# Graph Minors XII, Section 6: (6.1)

We follow the proof in the paper (page 258).

* The paper chooses a radial drawing `K` with a hub in each disc `D_m` and spokes in `D_m` to the
  vertices of the paths beside it. This is `exists_special_radial`. The metric `d` is defined from
  some
  radial drawing, and the paper does not say why it may be computed in this `K`. We prove that it
  may
  (`HasTangleMetric.of_radial`).
* Claim (1) is `Setup61.ins_eq_of_disc`.
* `W` is the trace of `F`, which we write out (`exists_W`). For each path `P_i` it contains the
  circuit
  `Q_i` of the four spokes at the ends of `P_i`, and `ins(Q_i) ⊇ U(P_i)` by claim (1) and
  `exists_Q_disc`. So `ins(W)` contains `F ∩ V(Γ)` and the edges `e_1` and `e_{θ/2}`. By claim (1)
  again, `ins(W) ⊆ Δ`.
* Claim (2) is `claim_two`.
* The paper says that there is no closed walk `W*` of `K` of length `< 2θ` in `Δ` with `e_1` and
  `e_{θ/2}` in `ins(W*)`. We prove this with the levels of `lev61` (`exists_low`, `exists_high`,
  `two_points`).
* The end goes through [5, (8.13)] (`gm12_theorem_8_13`).
-/


public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- An atom of `K` that corresponds to an edge of `Γ` is a region of `K` around it. -/
theorem atom_of_edge {Γ K : Drawing S} {e x : Set S} (he : e ∈ Γ.E)
    (hx : IsCorrespondingAtom Γ K e x) : e ⊆ x := by
  obtain ⟨-, -, ⟨v, hv, rfl, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩⟩ := hx
  · exact (edge_notMem_V he (show v ∈ ({v} : Set S) from rfl) hv).elim
  · exact h
  · obtain ⟨y, hy⟩ := he.1
    exact (region_subset h hy (Γ.closure_subset_U he (subset_closure hy))).elim

private theorem hub_walk_lies_in_closed_disc
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    (Γ : Drawing S)
    (F : Set S)
    (Δ : Set S)
    (k : ℕ)
    (a : Fin k → S)
    (b : Fin k → S)
    (P : Fin k → Drawing S)
    (h : Setup61 Γ F Δ k a b P)
    (X : Fin k → Set S)
    (Y : Fin k → Set S)
    (A : Fin k → Set S)
    (B : Fin k → Set S)
    (E : Fin (k + 1) → Set S)
    (r : Fin (k + 1) → Set S)
    (hp : Pieces61 Γ F Δ a b P X Y A B E r)
    (K : Drawing S)
    (c : Fin (k + 1) → S)
    (L : Fin (k + 1) → S → Set S)
    (hcE : ∀ (m : Fin (k + 1)), c m ∈ discInt (E m))
    (hL : ∀ (m : Fin (k + 1)), ∀ x ∈ sideVerts P m, IsLineWithEnds (L m x) (c m) x ∧ L m x ⊆ E m ∧
      L m x ∩ discBd (E m) = {x} ∧ ∀ y ∈ sideVerts P m, x ≠ y → L m x ∩ L m y = {c m})
    (W : GraphWalk K.toGraph (c 0) (c 0))
    (hWE : ∀ (e : Set S), e ∈ W.edges ↔ ∃ i : Fin k,
      e = L i.castSucc (a i) \ {c i.castSucc, a i} ∨ e = L i.succ (a i) \ {c i.succ, a i} ∨
      e = L i.castSucc (b i) \ {c i.castSucc, b i} ∨ e = L i.succ (b i) \ {c i.succ, b i})
    (hWS : ∀ x ∈ W.support, (∃ j, x = c j) ∨ ∃ i, x = a i ∨ x = b i) :
    (walkDrawing K W).U ⊆ Δ := by
  intro x hx
  rcases (mem_walkDrawing_U K W).mp hx with hx | ⟨e, heW, hxe⟩
  · rcases hWS x hx with ⟨j, rfl⟩ | ⟨i, rfl | rfl⟩
    · exact hp.sub j (hcE j).1
    · exact h.U_sub i (h.line i).left_mem
    · exact h.U_sub i (h.line i).right_mem
  · obtain ⟨i, rfl | rfl | rfl | rfl⟩ := (hWE e).mp heW
    · have hx' : a i ∈ sideVerts P i.castSucc := ⟨i, .inl rfl, h.a_V i⟩
      rw [closure_sdiff_pair (hL _ _ hx').1] at hxe
      exact hp.sub _ ((hL _ _ hx').2.1 hxe)
    · have hx' : a i ∈ sideVerts P i.succ := ⟨i, .inr rfl, h.a_V i⟩
      rw [closure_sdiff_pair (hL _ _ hx').1] at hxe
      exact hp.sub _ ((hL _ _ hx').2.1 hxe)
    · have hx' : b i ∈ sideVerts P i.castSucc := ⟨i, .inl rfl, h.b_V i⟩
      rw [closure_sdiff_pair (hL _ _ hx').1] at hxe
      exact hp.sub _ ((hL _ _ hx').2.1 hxe)
    · have hx' : b i ∈ sideVerts P i.succ := ⟨i, .inr rfl, h.b_V i⟩
      rw [closure_sdiff_pair (hL _ _ hx').1] at hxe
      exact hp.sub _ ((hL _ _ hx').2.1 hxe)

private theorem spoke_circuits_are_inside_hub_walk
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    (Γ : Drawing S)
    (k : ℕ)
    (a : Fin k → S)
    (b : Fin k → S)
    (P : Fin k → Drawing S)
    (K : Drawing S)
    (c : Fin (k + 1) → S)
    (L : Fin (k + 1) → S → Set S)
    (sp : Spokes Γ K a b P c (fun i => L i.castSucc (a i) \ {c i.castSucc, a i}) (fun i => L
      i.succ (a i) \ {c i.succ, a i}) (fun i => L i.castSucc (b i) \ {c i.castSucc, b i}) fun i =>
      L i.succ (b i) \ {c i.succ, b i})
    (ins : Drawing S → Set S)
    (Q : Fin k → Drawing S)
    (hQc : ∀ (i : Fin k), (Q i).IsCircuit)
    (hQV : ∀ (i : Fin k), (Q i).V = {c i.castSucc, a i, c i.succ, b i})
    (hQE : ∀ (i : Fin k), (Q i).E =
      {L i.castSucc (a i) \ {c i.castSucc, a i}, L i.succ (a i) \ {c i.succ, a i},
        L i.succ (b i) \ {c i.succ, b i}, L i.castSucc (b i) \ {c i.castSucc, b i}})
    (W : GraphWalk K.toGraph (c 0) (c 0))
    (hWE : ∀ (e : Set S), e ∈ W.edges ↔ ∃ i : Fin k,
      e = L i.castSucc (a i) \ {c i.castSucc, a i} ∨ e = L i.succ (a i) \ {c i.succ, a i} ∨
      e = L i.castSucc (b i) \ {c i.castSucc, b i} ∨ e = L i.succ (b i) \ {c i.succ, b i}) :
    ∀ (i : Fin k), ins (Q i) ⊆ insWalk ins K W := by
  intro i x hx
  have hsub : (Q i).IsSubdrawing (walkDrawing K W) := by
    refine ⟨?_, ?_⟩
    · rw [walkDrawing_V, hQV i]
      have e₀ : _ ∈ W.edges := (hWE _).mpr ⟨i, .inl rfl⟩
      have e₁ : _ ∈ W.edges := (hWE _).mpr ⟨i, .inr (.inl rfl)⟩
      have e₂ : _ ∈ W.edges := (hWE _).mpr ⟨i, .inr (.inr (.inl rfl))⟩
      rintro x (rfl | rfl | rfl | rfl)
      · exact W.left_mem_support_of_mem_edges e₀ (spoke_link (sp.mem_α₀ i) (pair_swap
          (sp.cap_α₀ i)))
      · exact W.left_mem_support_of_mem_edges e₀ (spoke_link (sp.mem_α₀ i) (sp.cap_α₀ i))
      · exact W.left_mem_support_of_mem_edges e₁ (spoke_link (sp.mem_α₁ i) (pair_swap
          (sp.cap_α₁ i)))
      · exact W.left_mem_support_of_mem_edges e₂ (spoke_link (sp.mem_β₀ i) (sp.cap_β₀ i))
    · rw [walkDrawing_E, hQE i]
      rintro t (rfl | rfl | rfl | rfl)
      · exact (hWE _).mpr ⟨i, .inl rfl⟩
      · exact (hWE _).mpr ⟨i, .inr (.inl rfl)⟩
      · exact (hWE _).mpr ⟨i, .inr (.inr (.inr rfl))⟩
      · exact (hWE _).mpr ⟨i, .inr (.inr (.inl rfl))⟩
  exact Or.inr (mem_iUnion₂.mpr ⟨Q i, ⟨hQc i, hsub⟩, hx⟩)

/-- **(6.1)** of Graph Minors XII: `d(e₁, e_{θ/2}) ≥ θ`. -/
theorem theorem_6_1_proof : GM15.GM12Theorem61Statement.{u} := by
  intro S _ _ Γ F Δ k θ₁ T₁ d a b P e_path i₀ i_last hS hconn hk hθ h2c hF hN hΔ hb hnd hord hV hP
    hdis
    hcov he h2 hT₁ hM hfree h0 hlast
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hk0 : 0 < k := by omega
  have hθ3 : 3 ≤ θ₁ := by omega
  have heΓ : ∀ i, e_path i ∈ Γ.E := fun i => ((hP i).2.trans interSet_isSub).2 (he i)
  have hE : Γ.E.Nonempty := ⟨_, heΓ i₀⟩
  have h : Setup61 Γ F Δ k a b P := ⟨hN, hΔ, hb, hnd, hord, hV, hP, hdis, hcov⟩
  -- the discs `D_m`, and the radial drawing `K` with hubs and spokes in them
  obtain ⟨X, Y, A, B, E, r, hp, hside⟩ := h.exists_regions hS hk0 h2
  obtain ⟨K, c, L, hK, hh, hcE, hL, sp⟩ := exists_hubs_spokes h hS h2c hp hside
  -- the metric may be computed in `K`
  obtain ⟨ins, hd', hdist⟩ := HasTangleMetric.of_radial hS hM hK
  have hT := hM.1
  have hrad : PreRad (.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  have hpt : IsPretangle (PaintingOrDrawing.drawing Γ).toHypergraph θ₁ _ :=
    ⟨hT.2.1.one_le, hT.2.1.isSeparation, hT.2.1.order_lt, hT.2.1.axiom1, hT.2.1.axiom2⟩
  have hs : IsSlope K (2 * θ₁) ins := GM11.isSlope_of_derived hS hpt hrad.2.1 hd'
  have hsize := size_free h
  have hins : ∀ C : Drawing S, C.IsCircuit → C.IsSubdrawing K → C.length < 2 * θ₁ →
      IsClosedDisc (ins C) ∧ discBd (ins C) = C.U ∧
      ((PaintingOrDrawing.drawing Γ).inter (ins C),
        (PaintingOrDrawing.drawing Γ).interOutside (ins C)) ∈
        GM12.inducedBySubgraph Γ.toHypergraph (Γ.interSet (closure (univ \ Δ))).toHypergraph θ₁ T₁
          :=
    fun C hC hCK hl => by
      obtain ⟨h1, h2, h3⟩ := hd' C hC hCK hl
      exact ⟨h1, by rw [← GM14.IsClosedDisc.subBd_eq_discBd hS h1]; exact h2, h3⟩
  -- the circuits `Q i`, and `U(P i) ⊆ ins(Q i)`
  choose Q hQc hQs hQl hQV hQE using exists_Q h hh sp
  have hQlen : ∀ i, (Q i).length < 2 * θ₁ := fun i => by
    have := hQl i
    omega
  have hRQ : ∀ i, (P i).U ⊆ ins (Q i) := by
    intro i
    have ha₀ : a i ∈ sideVerts P i.castSucc := ⟨i, .inl rfl, h.a_V i⟩
    have hb₀ : b i ∈ sideVerts P i.castSucc := ⟨i, .inl rfl, h.b_V i⟩
    have ha₁ : a i ∈ sideVerts P i.succ := ⟨i, .inr rfl, h.a_V i⟩
    have hb₁ : b i ∈ sideVerts P i.succ := ⟨i, .inr rfl, h.b_V i⟩
    have l1 := (hL _ _ ha₀).1
    have l2 := (hL _ _ ha₁).1
    have l3 := (hL _ _ hb₀).1
    have l4 := (hL _ _ hb₁).1
    have hQU : (Q i).U = (L i.castSucc (a i) ∪ L i.castSucc (b i)) ∪
        (L i.succ (a i) ∪ L i.succ (b i)) := by
      ext x
      rw [(Q i).U_eq, mem_union, mem_iUnion₂, hQV i]
      simp only [hQE i, mem_insert_iff, mem_singleton_iff, exists_prop, exists_eq_or_imp,
        exists_eq_left, closure_sdiff_pair l1, closure_sdiff_pair l2, closure_sdiff_pair l3,
        closure_sdiff_pair l4, mem_union]
      constructor
      · rintro ((rfl | rfl | rfl | rfl) | (h1 | h1 | h1 | h1))
        · exact .inl (.inl l1.left_mem)
        · exact .inl (.inl l1.right_mem)
        · exact .inr (.inl l2.left_mem)
        · exact .inl (.inr l3.right_mem)
        · exact .inl (.inl h1)
        · exact .inr (.inl h1)
        · exact .inr (.inr h1)
        · exact .inl (.inr h1)
      · rintro ((h1 | h1) | (h1 | h1))
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inr (.inr h1)))
        · exact .inr (.inr (.inl h1))
        · exact .inr (.inr (.inr (.inl h1)))
    obtain ⟨G, hG, hGΔ, hRG, hGb⟩ := hp.exists_Q_disc h hL i
    obtain ⟨h1, h2, h3⟩ := hins (Q i) (hQc i) (hQs i) (hQlen i)
    rw [h.ins_eq_of_disc hS hT.2.1 hθ3 h1 h3 hG hGΔ (by rw [h2, hGb, hQU])]
    exact hRG
  -- the walk `W`, and `ins(W) ⊆ Δ`
  obtain ⟨W, hWl, hWE, hWS⟩ := exists_W sp (hh.c_V 0)
  have hWk : W.length < 2 * θ₁ := by omega
  obtain ⟨hXr, hXl⟩ := theorem_8_5_proof hS hs W hWk
  have hWΔ : (walkDrawing K W).U ⊆ Δ := by
    exact hub_walk_lies_in_closed_disc (S := S) Γ F Δ k a b P h X Y A B E r hp K c L hcE hL W hWE
      hWS
  have hXΔ : insWalk ins K W ⊆ Δ := by
    rintro x (hx | hx)
    · exact hWΔ hx
    · obtain ⟨C, ⟨hC, hCW⟩, hxC⟩ := mem_iUnion₂.mp hx
      have hCK := hCW.trans (walkDrawing_isSubdrawing K W)
      obtain ⟨h1, h2, h3⟩ := hins C hC hCK (isConfined_walk W hWk C hC hCW)
      exact h.sub_of_bd_sub hS hT.2.1 hθ3 h1 h3 hΔ subset_rfl (h2 ▸ hCW.U_subset.trans hWΔ) hxC
  have hQW : ∀ i, ins (Q i) ⊆ insWalk ins K W := by
    exact spoke_circuits_are_inside_hub_walk (S := S) Γ k a b P K c L sp ins Q hQc hQV hQE W hWE
  have hFX : F ∩ Γ.V ⊆ insWalk ins K W := by
    intro x hx
    rw [← hV] at hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hQW i (hRQ i (h.line i).left_mem)
    · exact hQW i (hRQ i (h.line i).right_mem)
  -- claim (2) for `ins(W)`
  have hclaim2 : ∀ Y : Set S, IsRestraint K ins (2 * θ₁) Y → insWalk ins K W ⊆ Y →
      ¬ perimeterWalkLength K Y < perimeterWalkLength K (insWalk ins K W) := by
    intro Y hY hXY hlt
    exact claim_two hS hE hk hθ hT hK hd' hs hfree hsize hY (hFX.trans hXY) (by omega)
  have hne : e_path i₀ ≠ e_path i_last := by
    intro heq
    have hii : i₀ ≠ i_last := fun hi => by
      have := congrArg Fin.val hi
      omega
    obtain ⟨y, hy⟩ := (heΓ i₀).1
    have h1 := (P i₀).closure_subset_U (he i₀) (subset_closure hy)
    have h2 := (P i_last).closure_subset_U (he i_last) (subset_closure (heq ▸ hy))
    exact hii (same_path h h1 h2)
  rw [hdist _ (.inl (.inr (heΓ i₀))) _ (.inl (.inr (heΓ i_last)))]
  unfold tangleMetric
  rw [ite_eq_right hne]
  split_ifs with hex
  swap
  · omega
  by_contra hlt
  push Not at hlt
  have hne' : {m : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom Γ K (e_path i₀) x' ∧ IsCorrespondingAtom Γ K (e_path i_last) y' ∧
      W.length < 2 * θ₁ ∧ W.length = 2 * m ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W}.Nonempty
        := by
    obtain ⟨u, W'', x', y', h1, h2, h3, h4, h5⟩ := hex
    exact ⟨_, u, W'', x', y', h1, h2, h3, closed_walk_length_eq_two_mul hrad.2 W'', h4, h5⟩
  obtain ⟨u, W'', x', y', hx, hy, hl, hl2, hxW, hyW⟩ := Nat.sInf_mem hne'
  -- two points of the edges
  obtain ⟨pa, hpa⟩ := (heΓ i₀).1
  obtain ⟨pb, hpb⟩ := (heΓ i_last).1
  have hpaR : pa ∈ (P i₀).U := (P i₀).closure_subset_U (he i₀) (subset_closure hpa)
  have hpbR : pb ∈ (P i_last).U := (P i_last).closure_subset_U (he i_last) (subset_closure hpb)
  have hpaX : pa ∈ insWalk ins K W := hQW i₀ (hRQ i₀ hpaR)
  have hpbX : pb ∈ insWalk ins K W := hQW i_last (hRQ i_last hpbR)
  have hpaU : pa ∉ K.U := Set.disjoint_left.mp (edge_disjoint hrad (heΓ i₀)) hpa
  have hpbU : pb ∉ K.U := Set.disjoint_left.mp (edge_disjoint hrad (heΓ i_last)) hpb
  have hoff : ({pa, pb} : Set S) ∩ K.U ⊆ K.V := by
    rintro x ⟨rfl | rfl, hxU⟩
    · exact (hpaU hxU).elim
    · exact (hpbU hxU).elim
  obtain ⟨Y₀, hY₀X, hopt⟩ := gm12_theorem_8_13 S hS hconn K (2 * θ₁) ins hs pa pb
    (insWalk ins K W) hoff hXr hpaX hpbX hclaim2
  obtain ⟨hY₀, hpaY, hpbY, hmin⟩ := hopt
  -- `W*`
  obtain ⟨hZr, hZl⟩ := theorem_8_5_proof hS hs W'' hl
  have hle := hmin _ hZr (hxW (atom_of_edge (heΓ _) hx hpa)) (hyW (atom_of_edge (heΓ _) hy hpb))
  obtain ⟨v, Wst, -, hlen, -, -, hwd⟩ := hY₀.exists_walk hS
  have hfrΔ : frontier Y₀ ⊆ Δ := (hY₀.isClosed.frontier_subset.trans hY₀X).trans hXΔ
  -- a circuit of the boundary of `Y₀` around a point of `Y₀` off `K`
  have hcirc : ∀ {p : S}, p ∈ Y₀ → p ∉ K.U → ∃ C : Drawing S, C.IsCircuit ∧
      C.IsSubdrawing (K.interSet (frontier Y₀)) ∧ C.length < 2 * θ₁ ∧ p ∈ ins C := by
    intro p hpY hpU
    have : p ∈ insOf ins (K.interSet (frontier Y₀)) := by
      rw [insOf_frontier hS hs hY₀]
      exact hpY
    rcases this with hpU' | hpU'
    · exact (hpU (interSet_isSub.U_subset hpU')).elim
    · obtain ⟨C, ⟨hC, hCs⟩, hpC⟩ := mem_iUnion₂.mp hpU'
      exact ⟨C, hC, hCs, hY₀.isConfined hS C hC hCs, hpC⟩
  have hsupp : ∀ {C : Drawing S}, C.IsSubdrawing (K.interSet (frontier Y₀)) →
      ∀ x ∈ C.V, x ∈ Wst.support := by
    intro C hCs x hx
    have : x ∈ (K.interSet (frontier Y₀)).V := hCs.1 hx
    rw [← hwd, walkDrawing_V] at this
    exact this
  have hCU : ∀ {C : Drawing S}, C.IsSubdrawing (K.interSet (frontier Y₀)) → C.U ⊆ Δ ∧ C.U ⊆ K.U :=
    fun hCs => ⟨(hCs.U_subset.trans (interSet_U_subset isClosed_frontier)).trans hfrΔ,
      hCs.U_subset.trans interSet_isSub.U_subset⟩
  obtain ⟨C₀, hC₀, hC₀s, hC₀l, hpaC₀⟩ := hcirc hpaY hpaU
  obtain ⟨C₁, hC₁, hC₁s, hC₁l, hpbC₁⟩ := hcirc hpbY hpbU
  have hC₀K := hC₀s.trans interSet_isSub
  have hC₁K := hC₁s.trans interSet_isSub
  obtain ⟨i₀1, i₀2, i₀3⟩ := hins C₀ hC₀ hC₀K hC₀l
  obtain ⟨i₁1, i₁2, i₁3⟩ := hins C₁ hC₁ hC₁K hC₁l
  obtain ⟨x₀, hx₀C, hx₀⟩ := hp.exists_low h hS hK.2.1 hT.2.1 hθ3 hC₀ hC₀K (hCU hC₀s).1 i₀1 i₀2 i₀3
    h0 hpaC₀ (fun hm => hpaU ((hCU hC₀s).2 hm)) hpaR
  obtain ⟨x₁, hx₁C, hx₁⟩ := hp.exists_high h hS hK.2.1 hT.2.1 hθ3 hC₁ hC₁K (hCU hC₁s).1 i₁1 i₁2 i₁3
    (by omega) hpbC₁ (fun hm => hpbU ((hCU hC₁s).2 hm)) hpbR
  -- each edge of `W*` changes the level by one
  have hstep : ∀ e ∈ Wst.edges, ∀ x y, closure e ∩ K.V = {x, y} →
      lev61 X Y x ≤ lev61 X Y y + 1 ∧ lev61 X Y y ≤ lev61 X Y x + 1 := by
    intro e he x y hxy
    have heK : e ∈ (K.interSet (frontier Y₀)).E := by
      rw [← hwd, walkDrawing_E]
      exact he
    obtain ⟨h1, h2⟩ := mem_interSet_E_iff.mp heK
    have hcl : closure e ⊆ Δ := (closure_minimal h2 isClosed_frontier).trans hfrΔ
    obtain ⟨v', hv', w', hw', hc'⟩ := hK.2.1.2.2.2.2.1 e h1
    have hlev := hp.lev_step h hS hK.2.1 h1 hcl hv' hw' hc'
    rw [hc'] at hxy
    rcases Set.pair_eq_pair_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hlev
    · exact ⟨hlev.2, hlev.1⟩
  have hlong := two_points Wst hstep (hsupp hC₀s x₀ hx₀C) (hsupp hC₁s x₁ hx₁C)
    (n := 2 * k) (by rw [hx₀, hx₁]; omega)
  omega

end GraphMinor.GM12
