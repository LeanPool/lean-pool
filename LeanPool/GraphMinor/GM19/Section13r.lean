/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13q

/-!
# Graph Minors XIX, Section 13: step (7) of (13.6)

We show that the point `h` is not in `ins(F)`. If it were, then `F` would run along the two spokes
up to `h`, every arc would have `r*` as an end, and there would be one outer
and one inner arc. The outer arc leaves `W` at `r*`, so it is long. Then the inner arc cuts `Δ_v`
into two discs with shorter boundaries than `F`, and one of them points to the
tangle `𝒯'`, against the choice of `F`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
/-- A list of distinct edges of `F` is no longer than `F`. -/
theorem length_le_of_nodup (F : Drawing Shat) {l : List (Set Shat)} (hn : l.Nodup)
  (hE : ∀ e ∈ l, e ∈ F.E) : l.length ≤ F.E.ncard := by
  classical
  rw [← List.toFinset_card_of_nodup hn, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun e he ↦ hE e (by simpa using he)) F.finite_edges

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}

omit [T2Space S] in
/-- A walk from outside `W` to a vertex of `W`, with no other vertex in `W`, enters at a point of
`bd(W)`. -/
theorem IsWheelHubOfRadius.mem_bd_of_walk (hW : D.IsWheelHubOfRadius W H ρ) {a b : Shat}
  (L : GraphWalk D.rad.G.toGraph a b) (ha : a ∉ W) (hb : b ∈ W)
    (hL : ∀ x ∈ L.support, x ≠ b → x ∉ W) : b ∈ discBd W := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  induction L with
  | nil _ => exact absurd hb ha
  | @cons x y z e hl t ih =>
    by_cases hyz : y = z
    · subst hyz
      rcases hW.edge_side hl.1 with hs | hd
      · have hcl : closure e ⊆ W := closure_minimal hs hW.is_disc.isClosed
        exact absurd (hcl (IsLink.left_mem_closure hl)) ha
      · exact hW.mem_bd_of_closure hd (IsLink.right_mem_closure hl) hb
    · exact ih (hL y (by simp [t.start_mem_support]) hyz) hb fun z' hz' hne ↦ hL z'
        (by simp [hz']) hne

variable {v₁ v₂ u : Shat} {f₁ f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ u} {A₂ : GraphWalk
  D.rad.G.toGraph v₂ u} {T : GraphWalk D.rad.G.toGraph u h}

/-- By (13.3), if `F` has the vertices `x` of the spoke and `h`, then it includes the spoke from `x`
to `h`. -/
theorem IsFan.tail_in_enclave (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hF : IsEnclave D.tb D.ord D.𝒯
  F) {x : Shat} {X : GraphWalk D.rad.G.toGraph v₁ x}
    {Y : GraphWalk D.rad.G.toGraph x u} (hA : A₁ = X.append Y) (hx : x ∈ F.V)
      (hh : h ∈ F.V) : ∀ e ∈ (Y.append T).edges, e ∈ F.E := by
  subst hA
  have hend : h ∈ D.rad.G.toGraph.vertexSet := T.mem_vertexSet_of_mem_support T.end_mem_support
  have hnil := GraphWalk.append_nil' (Y.append T) hend
  have heq : (X.append Y).append T = X.append ((Y.append T).append (.nil hend)) := by
    rw [hnil, GraphWalk.append_assoc']
  refine hf.spoke₁.2.subwalk_in_enclave hF (A := X) (Y.append T) (B := .nil hend)
    (heq ▸ hf.spoke₁.1) (fun e ↦ ?_) hx hh
  rw [walkDrawing_E, ← heq]
  rfl

/-- Two walks from `r*` to the same spoke, off `D_v` and in `F`, with no shared edge, cannot end
before `u`, if the later end comes after the earlier one. -/
theorem IsFan.no_two_ends_ordered (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hF : F.IsCircuitOf D.rad.G)
  (hE : IsEnclave D.tb D.ord D.𝒯 F)
    (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv) (hh : h ∈ F.V) {p q : Shat} {X : GraphWalk
      D.rad.G.toGraph v₁ p} {Y : GraphWalk D.rad.G.toGraph p q}
    {Z : GraphWalk D.rad.G.toGraph q u} (hA : A₁ = X.append (Y.append Z)) (hq : q ≠ u)
      (hp : p ∈ F.V) {P : GraphWalk D.rad.G.toGraph r p}
    {P' : GraphWalk D.rad.G.toGraph r q} (hPs : P.IsSimple) (hPF : ∀ e ∈ P.edges, e ∈ F.E)
      (hP'F : ∀ e ∈ P'.edges, e ∈ F.E) (hPo : ∀ e ∈ P.edges, e ∉ Dv.E)
    (hP'o : ∀ e ∈ P'.edges, e ∉ Dv.E) (hdis : ∀ e ∈ P'.edges, e ∉ P.edges) : False := by
  have hsp : ∀ e ∈ ((Y.append Z).append T).edges, e ∈ F.E := hf.tail_in_enclave hE hA hp hh
  have hYZ : ∀ e, e ∈ (Y.append Z).edges → e ∈ F.E := fun e he ↦ hsp e
    (by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he)
  have hinD : ∀ e, e ∈ (Y.append Z).edges → e ∈ Dv.E := fun e he ↦ (hC.mem_E e).mpr (.inr (.inr
    (.inl (by
    rw [hA, GraphWalk.edges_append]; exact List.mem_append_right _ he))))
  have hne : r ≠ p := fun h' ↦ hf.r_notMem_spoke hf.spoke₁ (by
    rw [h', GraphWalk.mem_support_append]
    exact .inl (by rw [hA, GraphWalk.mem_support_append]; exact .inl X.end_mem_support))
  have hcov := circuit_cover hF hne hPs hPF (Y.append P'.reverse) (fun e he ↦ by
    rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse] at he
    rcases he with he | he
    · exact hYZ e (by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he)
    · exact hP'F e he) (fun e he hp' ↦ by
    rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse] at he
    rcases he with he | he
    · exact hPo e hp' (hinD e (by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he))
    · exact hdis e he hp')
  cases Z with
  | nil _ => exact hq rfl
  | @cons _ y _ g hg t =>
    have hgm : g ∈ (Y.append (GraphWalk.cons hg t)).edges := by
      rw [GraphWalk.edges_append]
      exact List.mem_append_right _ List.mem_cons_self
    have hsimple : (Y.append (GraphWalk.cons hg t)).IsSimple := by
      have hs := isSimple_of_append hf.spoke₁.1
      rw [hA] at hs
      exact (isSimple_of_append hs.1).2
    rcases hcov g (hYZ g hgm) with h₁ | h₁
    · exact hPo g h₁ (hinD g hgm)
    · rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse] at h₁
      rcases h₁ with h₁ | h₁
      · exact Splits.append_edge hsimple h₁ List.mem_cons_self
      · exact hP'o g h₁ (hinD g hgm)

/-- Two such walks to the same spoke: one of them ends at `u`. -/
theorem IsFan.no_two_ends (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hF : F.IsCircuitOf D.rad.G)
  (hE : IsEnclave D.tb D.ord D.𝒯 F)
    (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv) (hh : h ∈ F.V) {p q : Shat} (hp : p ∈ A₁.support)
      (hq : q ∈ A₁.support) (hpu : p ≠ u) (hqu : q ≠ u) (hpF : p ∈ F.V) (hqF : q ∈ F.V)
    {P : GraphWalk D.rad.G.toGraph r p} {P' : GraphWalk D.rad.G.toGraph r q} (hPs : P.IsSimple)
      (hP's : P'.IsSimple) (hPF : ∀ e ∈ P.edges, e ∈ F.E) (hP'F : ∀ e ∈ P'.edges, e ∈ F.E)
    (hPo : ∀ e ∈ P.edges, e ∉ Dv.E) (hP'o : ∀ e ∈ P'.edges, e ∉ Dv.E)
      (hdis : ∀ e ∈ P'.edges, e ∉ P.edges) : False := by
  obtain ⟨X, Y, rfl⟩ := A₁.exists_append_of_mem hp
  rcases (GraphWalk.mem_support_append _ _).mp hq with hq' | hq'
  · obtain ⟨X', Y', rfl⟩ := X.exists_append_of_mem hq'
    exact hf.no_two_ends_ordered hF hE hC hh (X := X') (Y := Y') (Z := Y)
      (by rw [GraphWalk.append_assoc']) hpu hqF hP's hP'F hPF hP'o hPo
      fun e he he' ↦ hdis e he' he
  · obtain ⟨X', Y', rfl⟩ := Y.exists_append_of_mem hq'
    exact hf.no_two_ends_ordered hF hE hC hh rfl hqu hpF hPs hPF hP'F hPo hP'o hdis

end TangleDatum

omit [T2Space Shat] in
/-- The ends of an arc are vertices of `F`. -/
theorem IsArcOn.mem_F {G Dv F : Drawing Shat} {a b : Shat} {P : GraphWalk G.toGraph a b}
  (hP : IsArcOn G Dv F P) (hF : F.IsSubdrawing G) : ∀ x ∈ P.support, x ∈ F.V := by
  have ha : a ∈ F.V := by
    cases hc : P with
    | nil _ => exact absurd rfl hP.ne
    | @cons _ y _ e hl t =>
      exact (Drawing.IsLink.mem_V_of_sub hF hl (hP.inF e (by
        rw [hc]
        exact List.mem_cons_self))).1
  exact support_subset_of_edges hF P ha hP.inF

namespace TangleDatum.IsFar

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}
  {v₁ v₂ u : Shat} {f₁ f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ u} {A₂ : GraphWalk
    D.rad.G.toGraph v₂ u} {T : GraphWalk D.rad.G.toGraph u h}

omit [T2Space S] [T2Space Shat] in
/-- An edge of the drawing has a point. -/
theorem edge_nonempty {e : Set Shat} (he : e ∈ D.rad.G.E) : e.Nonempty := by
  obtain ⟨x, -, y, -, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e he
  have hx : x ∈ closure e ∩ D.rad.G.V := by rw [hcap]; exact .inl rfl
  exact closure_nonempty_iff.mp ⟨x, hx.1⟩

/-- The heart of step (7): the outer arc is long and the inner arc is a short chord of `D_v`. -/
theorem false_of_ends (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
  (hfan : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv)
    (hb₁ : f₁ ⊆ discBd W) (hb₂ : f₂ ⊆ discBd W) (hh : h ∈ F.V) {a₁ a₂ : Shat} {O : GraphWalk
      D.rad.G.toGraph r a₁} {I : GraphWalk D.rad.G.toGraph r a₂}
    (hO : IsArcOn D.rad.G Dv F O) (hI : IsArcOn D.rad.G Dv F I) (hOo : ∀ e ∈ O.edges, Disjoint e
      Δv) (hIi : ∀ e ∈ I.edges, e ⊆ discInt Δv)
    (ha₁ : a₁ ∈ A₁.support) (ha₂ : a₂ ∈ A₂.support) : False := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hx := hf.enc
  have hW := hfan.hub
  have hbdS := hfan.bd_off
  have hinn := hfan.inner
  have hFi := hx.isInsOf_F
  have hE := hx.isEnclave
  have hFsub := hFi.1.1
  have hΔv := hx.sector.is_disc
  have hbv := hx.sector.Dv_U.symm
  have hΔW := hx.sector.Δv_sub
  have hmain := (hfan.main hC hx.hopt hΔv hΔW hbv).2
  have hK₁ := hfan.spoke₁
  have hK₂ := hfan.spoke₂
  obtain ⟨X₁, Y₁, hA₁⟩ := A₁.exists_append_of_mem ha₁
  obtain ⟨X₂, Y₂, hA₂⟩ := A₂.exists_append_of_mem ha₂
  have hF₁ : ∀ e ∈ (Y₁.append T).edges, e ∈ F.E := hfan.tail_in_enclave hE hA₁
    (hO.mem_F hFsub _ O.end_mem_support) hh
  have hF₂ : ∀ e ∈ (Y₂.append T).edges, e ∈ F.E := hfan.swap.tail_in_enclave hE hA₂
    (hI.mem_F hFsub _ I.end_mem_support) hh
  rw [GraphWalk.edges_append] at hF₁ hF₂
  have hY₁F : ∀ e ∈ Y₁.edges, e ∈ F.E := fun e he ↦ hF₁ e (List.mem_append_left _ he)
  have hTF : ∀ e ∈ T.edges, e ∈ F.E := fun e he ↦ hF₁ e (List.mem_append_right _ he)
  have hY₂F : ∀ e ∈ Y₂.edges, e ∈ F.E := fun e he ↦ hF₂ e (List.mem_append_left _ he)
  have hY₁D : ∀ e ∈ Y₁.edges, e ∈ Dv.E := fun e he ↦ (hC.mem_E e).mpr (.inr (.inr (.inl (by
    rw [hA₁, GraphWalk.edges_append]; exact List.mem_append_right _ he))))
  have hY₂D : ∀ e ∈ Y₂.edges, e ∈ Dv.E := fun e he ↦ (hC.mem_E e).mpr (.inr (.inr (.inr (by
    rw [hA₂, GraphWalk.edges_append]; exact List.mem_append_right _ he))))
  have hTW : ∀ x ∈ T.support, x ∈ W ∧ x ≠ r := fun x hx' ↦ by
    have hm : x ∈ (A₁.append T).support := (GraphWalk.mem_support_append _ _).mpr (.inr hx')
    exact ⟨IsSpokeWalk.subset_W hW hbdS hinn hK₁ ((mem_walkDrawing_U _ _).mpr (.inl hm)),
      fun h' ↦ hfan.r_notMem_spoke hK₁ (h' ▸ hm)⟩
  -- The first vertex of `O` after `r*` in `W`.
  obtain ⟨y, g, hg, O', hOeq⟩ : ∃ (y : Shat) (g : Set Shat) (hg : D.rad.G.toGraph.IsLink g r y)
    (O' : GraphWalk D.rad.G.toGraph y a₁), O = .cons hg O' := by
    cases O with
    | nil _ => exact absurd rfl hO.ne
    | cons hl t => exact ⟨_, _, hl, t, rfl⟩
  subst hOeq
  have ha₁W : a₁ ∈ W := IsSpokeWalk.subset_W hW hbdS hinn hK₁ ((mem_walkDrawing_U _ _).mpr (.inl
    ((GraphWalk.mem_support_append _ _).mpr (.inl ha₁))))
  obtain ⟨v', hv'W, O₁, O₂, hO', hfirst⟩ := GraphWalk.exists_first_mem O' (X
    := W) ⟨a₁, O'.end_mem_support, ha₁W⟩
  subst hO'
  have hgoff : Disjoint g W := by
    rcases hW.edge_side hg.1 with hs | hd
    · exact absurd hs (hfan.edge_off_W hC hb₁ hb₂ hΔv hbv hΔW (IsLink.left_mem_closure hg)
        (hOo g List.mem_cons_self))
    · exact hd
  have hO₁nil : y ≠ v' := by
    rintro rfl
    have htil : tilde g ⊆ discBd W := by
      intro p hp
      have hpV : p ∈ closure g ∩ D.rad.G.V := ⟨hp.1, by
        by_contra hn
        exact hp.2 (closure_edge_subset hg.1 hp.1 |>.resolve_right hn)⟩
      rw [hg.2.2.2] at hpV
      rcases hpV with rfl | rfl
      · exact hfan.r_bd
      · exact hW.mem_bd_of_closure hgoff (IsLink.right_mem_closure hg) hv'W
    exact disjoint_left.mp hgoff (edge_nonempty hg.1).some_mem (hW.chord_in_W g hg.1 htil
      (edge_nonempty hg.1).some_mem)
  have hyW : y ∉ W := fun hn ↦ hO₁nil (hfirst y O₁.start_mem_support hn)
  have hv'bd : v' ∈ discBd W := hW.mem_bd_of_walk O₁ hyW hv'W fun x hx' hne hn ↦ hne
    (hfirst x hx' hn)
  have hO₁len : 1 ≤ O₁.length := by
    by_contra hn
    cases O₁ with
    | nil _ => exact hO₁nil rfl
    | cons _ _ => simp at hn
  -- The outer arc has at least `ρ + 2` edges, counted with the rest of the spoke.
  have hO' : IsArcOn D.rad.G Dv F ((GraphWalk.cons hg O₁).append O₂) := hO
  have hv'V : v' ∈ D.rad.G.V := O₂.mem_vertexSet_of_mem_support O₂.start_mem_support
  obtain ⟨L', hLs, -, hLe⟩ := GM11.GraphWalk.exists_isSimple (O₂.append (Y₁.append T))
  have hb := IsSpokeWalk.le_walk_of_bd hW hbdS hinn hK₁ L' hv'V hv'bd
  have sl₁ := hW.spoke_length hK₁
  have sl₂ := hW.spoke_length hK₂
  have hlong : ρ + 2 ≤ (GraphWalk.cons hg O₁).length + L'.length := by
    have hc : (GraphWalk.cons hg O₁).length = O₁.length + 1 := rfl
    rw [hc]
    have hl : (A₁.append T).length + 1 ≤ L'.length ∨ 2 ≤ O₁.length := by
      by_contra hn
      push Not at hn
      have hone : O₁.length = 1 := by omega
      have heq : (A₁.append T).length = L'.length := by omega
      have hpar := D.even_length_walk (GraphWalk.cons hg O₁)
      rw [hc, hone] at hpar
      exact hfan.r_mem.2 ((hpar.mp (by decide)).mpr (hb.2 heq))
    omega
  have hLm : ∀ e ∈ L'.edges, e ∈ O₂.edges ∨ e ∈ Y₁.edges ∨ e ∈ T.edges := fun e he ↦ by
    have := hLe e he
    rwa [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_append, List.mem_append] at this
  have hOin : ∀ e, (e ∈ (GraphWalk.cons hg O₁).edges ∨ e ∈ O₂.edges) → e ∈
    ((GraphWalk.cons hg O₁).append O₂).edges := fun e he ↦ by
    rw [GraphWalk.edges_append, List.mem_append]
    exact he
  have hOo' : ∀ e, (e ∈ (GraphWalk.cons hg O₁).edges ∨ e ∈ O₂.edges) → Disjoint e Δv
    := fun e he ↦ hOo e (hOin e he)
  have hnotI : ∀ e, (e ∈ (GraphWalk.cons hg O₁).edges ∨ e ∈ O₂.edges) → e ∉ I.edges
    := fun e he hI' ↦ by
    obtain ⟨x, hxe⟩ := edge_nonempty (hI.inF e hI' |> hFsub.2)
    exact disjoint_left.mp (hOo' e he) hxe (discInt_subset _ (hIi e hI' hxe))
  have hTI : ∀ e ∈ T.edges, e ∉ I.edges := fun e he hI' ↦ by
    obtain ⟨x, hxe⟩ := edge_nonempty (hI.inF e hI' |> hFsub.2)
    have hin := hIi e hI' hxe
    have hU : x ∈ (walkDrawing D.rad.G (A₁.append T)).U := by
      refine (mem_walkDrawing_U _ _).mpr (.inr ⟨e, ?_, subset_closure hxe⟩)
      rw [GraphWalk.edges_append]
      exact List.mem_append_right _ he
    exact hin.2 (hmain _ _ _ hK₁ ⟨hin.1, hU⟩)
  have hOT : ∀ e ∈ (GraphWalk.cons hg O₁).edges, e ∉ T.edges := fun e he hT' ↦ by
    obtain ⟨p, q, hpq, hp, hq, hcap⟩ := D.exists_ends_of_mem_edges _ he
    obtain ⟨hp', hq'⟩ := D.ends_mem_support T hT' hcap
    have key : ∀ x, x ∈ (GraphWalk.cons hg O₁).support → x ∈ T.support → x = v' := fun x h₁ h₂ ↦ by
      rw [GraphWalk.support_cons, List.mem_cons] at h₁
      rcases h₁ with h₁ | h₁
      · exact absurd h₁ (hTW x h₂).2
      · exact hfirst x h₁ (hTW x h₂).1
    exact hpq ((key p hp hp').trans (key q hq hq').symm)
  have hA₂s : (X₂.append Y₂).IsSimple := hA₂ ▸ (isSimple_of_append hK₂.1).1
  have hcard : (GraphWalk.cons hg O₁).edges.length + L'.edges.length + I.edges.length +
    Y₂.edges.length ≤ F.E.ncard := by
    rw [← List.length_append, ← List.length_append, ← List.length_append]
    refine length_le_of_nodup F ?_ ?_
    · have n₁ := (isSimple_of_append hO'.simple).1.edges_nodup
      refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨n₁,
        hLs.edges_nodup, ?_⟩, hI.simple.edges_nodup, ?_⟩, (isSimple_of_append hA₂s).2.edges_nodup,
          ?_⟩
      · rintro e he _ he' rfl
        rcases hLm e he' with h₁ | h₁ | h₁
        · exact Splits.append_edge hO'.simple he h₁
        · exact hO'.off e (hOin e (.inl he)) (hY₁D e h₁)
        · exact hOT e he h₁
      · rintro e he _ he' rfl
        rw [List.mem_append] at he
        rcases he with he | he
        · exact hnotI e (.inl he) he'
        · rcases hLm e he with h₁ | h₁ | h₁
          · exact hnotI e (.inr h₁) he'
          · exact hI.off e he' (hY₁D e h₁)
          · exact hTI e h₁ he'
      · rintro e he _ he' rfl
        have hD := hY₂D e he'
        rw [List.mem_append, List.mem_append] at he
        rcases he with (he | he) | he
        · exact hO'.off e (hOin e (.inl he)) hD
        · rcases hLm e he with h₁ | h₁ | h₁
          · exact hO'.off e (hOin e (.inr h₁)) hD
          · exact hfan.edges_disjoint e (by
              rw [hA₁, GraphWalk.edges_append]
              exact List.mem_append_right _ h₁) (by
              rw [hA₂, GraphWalk.edges_append]
              exact List.mem_append_right _ he')
          · exact hfan.swap.edges_disjoint_T e (by
              rw [hA₂, GraphWalk.edges_append]
              exact List.mem_append_right _ he') h₁
        · exact hI.off e he hD
    · intro e he
      simp only [List.mem_append] at he
      rcases he with ((he | he) | he) | he
      · exact hO'.inF e (hOin e (.inl he))
      · rcases hLm e he with h₁ | h₁ | h₁
        · exact hO'.inF e (hOin e (.inr h₁))
        · exact hY₁F e h₁
        · exact hTF e h₁
      · exact hI.inF e he
      · exact hY₂F e he
  -- The inner arc is a chord of `D_v`, and both of its circuits are shorter than `F`.
  have hrX : r ∉ X₂.support := fun hn ↦ hfan.r_notMem_spoke hK₂ ((GraphWalk.mem_support_append _
    _).mpr (.inl (by
    rw [hA₂, GraphWalk.mem_support_append]; exact .inl hn)))
  have hPas : (GraphWalk.cons hfan.link₂ X₂).IsSimple := by
    change (r :: X₂.support).Nodup
    exact List.nodup_cons.mpr ⟨hrX, (isSimple_of_append hA₂s).1⟩
  have hPaE : ∀ e ∈ (GraphWalk.cons hfan.link₂ X₂).edges, e ∈ Dv.E := fun e he ↦ by
    rw [GraphWalk.edges_cons, List.mem_cons] at he
    refine (hC.mem_E e).mpr ?_
    rcases he with rfl | he
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inr (by
        rw [hA₂, GraphWalk.edges_append]
        exact List.mem_append_left _ he)))
  obtain ⟨W₁, W₂, hs⟩ := exists_splits hC.circuit.2 hC.circuit.1 hI.left hI.right hI.ne
  obtain ⟨R, hR⟩ := exists_side_of_walk (D := D) hI.ne hPas hPaE hs
  have hadd := hR.card_add
  have e₁ : (edgeSet (GraphWalk.cons hfan.link₂ X₂)).ncard = (GraphWalk.cons hfan.link₂ X₂).length
    := by
    rw [← ncard_walk_E D.rad.G hPas, walkDrawing_E]
    rfl
  have e₂ : (edgeSet R).ncard = R.length := by
    rw [← ncard_walk_E D.rad.G hR.s₂, walkDrawing_E]
    rfl
  have e₃ : Dv.length = Dv.E.ncard := rfl
  have hcl := hC.card
  have hc₁ : (GraphWalk.cons hfan.link₂ X₂).length = X₂.length + 1 := rfl
  have hlen₁ : (A₁.append T).length = A₁.length + T.length := GraphWalk.length_append _ _
  have hlen₂ : (A₂.append T).length = A₂.length + T.length := GraphWalk.length_append _ _
  have hlen₃ : A₂.length = X₂.length + Y₂.length := by rw [hA₂, GraphWalk.length_append]
  simp only [edges_length] at hcard
  exact hx.no_short_chord hR hI.ne hI.simple hI.inner hI.off (by omega) (by omega)

/-- A vertex of `D_v` in `F` other than `r*` is joined to `u` along `D_v`, inside `F`. -/
theorem exists_tail (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (hfan : D.IsFan W H ρ r f₁ f₂
  A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv)
    (hh : h ∈ F.V) {x : Shat} (hx : x ∈ Dv.V) (hxr : x ≠ r) (hxF : x ∈ F.V) : ∃ w : GraphWalk
      D.rad.G.toGraph x u, ∀ e ∈ w.edges, e ∈ F.E ∧ e ∈ Dv.E := by
  rcases (hC.mem_V x).mp hx with rfl | hm | hm
  · exact absurd rfl hxr
  · obtain ⟨X, Y, hA⟩ := A₁.exists_append_of_mem hm
    refine ⟨Y, fun e he ↦ ⟨hfan.tail_in_enclave hf.enc.isEnclave hA hxF hh e ?_,
      (hC.mem_E e).mpr (.inr (.inr (.inl ?_)))⟩⟩
    · rw [GraphWalk.edges_append]
      exact List.mem_append_left _ he
    · rw [hA, GraphWalk.edges_append]
      exact List.mem_append_right _ he
  · obtain ⟨X, Y, hA⟩ := A₂.exists_append_of_mem hm
    refine ⟨Y, fun e he ↦ ⟨hfan.swap.tail_in_enclave hf.enc.isEnclave hA hxF hh e ?_,
      (hC.mem_E e).mpr (.inr (.inr (.inr ?_)))⟩⟩
    · rw [GraphWalk.edges_append]
      exact List.mem_append_left _ he
    · rw [hA, GraphWalk.edges_append]
      exact List.mem_append_right _ he

/-- If `h ∈ ins(F)`, then every arc has the end `r*`: otherwise `F` would be one arc and a walk of
`D_v`, and there are both an inner and an outer edge. -/
theorem arc_end (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (hfan : D.IsFan W H ρ r f₁ f₂ A₁ A₂
  T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv)
    (hh : h ∈ F.V) {a b : Shat} {P : GraphWalk D.rad.G.toGraph a b} (hP : IsArcOn D.rad.G Dv F P) :
      a = r ∨ b = r := by
  by_contra hn
  push Not at hn
  have hx := hf.enc
  have hFi := hx.isInsOf_F
  have hΔv := hx.sector.is_disc
  have hbv := hx.sector.Dv_U.symm
  have hFsub := hFi.1.1
  obtain ⟨wa, ha⟩ := hf.exists_tail hfan hC hh hP.left hn.1 (hP.mem_F hFsub _ P.start_mem_support)
  obtain ⟨wb, hb⟩ := hf.exists_tail hfan hC hh hP.right hn.2 (hP.mem_F hFsub _ P.end_mem_support)
  have hJ : ∀ e ∈ (wb.append wa.reverse).edges, e ∈ F.E ∧ e ∈ Dv.E := fun e he ↦ by
    rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse] at he
    rcases he with he | he
    · exact hb e he
    · exact ha e he
  have hcov := circuit_cover hFi.1 hP.ne hP.simple hP.inF _ (fun e he ↦
    (hJ e he).1) fun e he hp ↦ hP.off e hp (hJ e he).2
  have hin : ∀ e ∈ F.E, e ∉ Dv.E → e ∈ P.edges := fun e he hd ↦ (hcov e he).resolve_right fun hj ↦
    hd (hJ e hj).2
  have hsubΔ : ∀ x ∈ Dv.U, x ∈ discBd Δv := fun x hx' ↦ hbv ▸ hx'
  obtain ⟨e₁, he₁, hd₁⟩ := hf.exists_edge_out
  obtain ⟨e₂, he₂, hd₂⟩ := hf.exists_edge_in
  obtain ⟨p₁, hp₁⟩ := edge_nonempty (hFsub.2 he₁)
  obtain ⟨p₂, hp₂⟩ := edge_nonempty (hFsub.2 he₂)
  have hUmem : ∀ {e : Set Shat}, e ∈ Dv.E → ∀ {p : Shat}, p ∈ e → p ∈ discBd Δv := fun he _ hp ↦
    hsubΔ _ (Dv.closure_subset_U he (subset_closure hp))
  have m₁ := hin e₁ he₁ fun hD ↦ disjoint_left.mp hd₁ hp₁ (Surface.discBd_subset _ (hUmem hD hp₁))
  have m₂ := hin e₂ he₂ fun hD ↦ (hd₂ hp₂).2 (hUmem hD hp₂)
  rcases IsArcOn.side (D := D) hP hx.sector.Dv_circuit.1 hΔv hbv with h₁ | h₁
  · exact disjoint_left.mp hd₁ hp₁ (discInt_subset _ (h₁ e₁ m₁ hp₁))
  · exact disjoint_left.mp (h₁ e₂ m₂) hp₂ (discInt_subset _ (hd₂ hp₂))

/-- Step (7) of the proof of (13.6): `h ∉ ins(F)`. -/
theorem notMem_ins_F (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) : h ∉ D.ins F := by
  intro hm
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hx := hf.enc
  have hW := hx.wheel
  have hFi := hx.isInsOf_F
  have hFsub := hFi.1.1
  obtain ⟨hV, -, hU⟩ := hf.point_of_mem_ins hm
  have hhG : h ∈ D.rad.G.V := hW.H_sub.1 (by rw [hV]; rfl)
  have hh : h ∈ F.V := IsSubdrawing.mem_V hFsub hU hhG
  have hHeq : ∀ {y : Shat}, y ∈ H.V → y = h := fun hy ↦ by rw [hV] at hy; exact hy
  rcases IsBoundarySector.cases hW hx.hbdS hx.hin hx.sector with ⟨v₁, v₂, u, h', f₁, f₂, A₁, A₂, T,
    hfan, hC, hb₁, hb₂⟩ |
    ⟨v₁, v₂, h₁, h₂, f₁, f₂, K₁, K₂, P, -, -, -, -, -, s₁, s₂, hdis, -⟩
  · obtain rfl : h' = h := hHeq hfan.spoke₁.2.h_mem
    obtain ⟨a, b, P₀, hP₀, hout⟩ := hf.exists_outer_arc
    obtain ⟨a', b', P₁, hP₁, hinn⟩ := hf.exists_inner_arc
    have orient : ∀ {a b : Shat} (P : GraphWalk D.rad.G.toGraph a b), IsArcOn D.rad.G Dv F P →
        ∃ (c : Shat) (P' : GraphWalk D.rad.G.toGraph r c), IsArcOn D.rad.G Dv F P'
          ∧ ∀ e ∈ P'.edges, e ∈ P.edges := by
      intro a b P hP
      rcases hf.arc_end hfan hC hh hP with rfl | rfl
      · exact ⟨_, P, hP, fun _ he ↦ he⟩
      · refine ⟨_, P.reverse, TangleDatum.IsArcOn.reverse hP, fun e he ↦ ?_⟩
        rwa [GraphWalk.edges_reverse, List.mem_reverse] at he
    obtain ⟨a₁, O, hO, hOm⟩ := orient P₀ hP₀
    obtain ⟨a₂, I, hI, hIm⟩ := orient P₁ hP₁
    have hOo : ∀ e ∈ O.edges, Disjoint e Δv := fun e he ↦ hout e (hOm e he)
    have hIi : ∀ e ∈ I.edges, e ⊆ discInt Δv := fun e he ↦ hinn e (hIm e he)
    have hdis : ∀ e ∈ I.edges, e ∉ O.edges := fun e he he' ↦ by
      obtain ⟨p, hp⟩ := edge_nonempty (hFsub.2 (hI.inF e he))
      exact disjoint_left.mp (hOo e he') hp (discInt_subset _ (hIi e he hp))
    have hpos : ∀ {c : Shat}, c ∈ Dv.V → c ≠ r → c ∈ A₁.support ∨ c ∈ A₂.support := fun hc hne ↦
      ((hC.mem_V _).mp hc).resolve_left hne
    have good₁ : a₁ ∈ A₁.support → a₂ ∈ A₂.support → False := fun h₁ h₂ ↦ hf.false_of_ends hfan hC
      hb₁ hb₂ hh hO hI hOo hIi h₁ h₂
    have good₂ : a₁ ∈ A₂.support → a₂ ∈ A₁.support → False := fun h₁ h₂ ↦ hf.false_of_ends
      hfan.swap hC.swap hb₂ hb₁ hh hO hI hOo hIi h₁ h₂
    have hFa₁ := hO.mem_F hFsub _ O.end_mem_support
    have hFa₂ := hI.mem_F hFsub _ I.end_mem_support
    rcases hpos hO.right hO.ne.symm with h₁ | h₁ <;> rcases hpos hI.right hI.ne.symm with h₂ | h₂
    · by_cases hu₁ : a₁ = u
      · exact good₂ (hu₁ ▸ A₂.end_mem_support) h₂
      by_cases hu₂ : a₂ = u
      · exact good₁ h₁ (hu₂ ▸ A₂.end_mem_support)
      exact hfan.no_two_ends hFi.1 hx.isEnclave hC hh h₁ h₂ hu₁ hu₂ hFa₁ hFa₂ hO.simple hI.simple
        hO.inF hI.inF hO.off hI.off hdis
    · exact good₁ h₁ h₂
    · exact good₂ h₁ h₂
    · by_cases hu₁ : a₁ = u
      · exact good₁ (hu₁ ▸ A₁.end_mem_support) h₂
      by_cases hu₂ : a₂ = u
      · exact good₂ h₁ (hu₂ ▸ A₁.end_mem_support)
      exact hfan.swap.no_two_ends hFi.1 hx.isEnclave hC.swap hh h₁ h₂ hu₁ hu₂ hFa₁ hFa₂ hO.simple
        hI.simple hO.inF hI.inF hO.off hI.off hdis
  · have e₁ : h₁ = h := hHeq s₁.2.h_mem
    have e₂ : h₂ = h := hHeq s₂.2.h_mem
    exact hdis h (e₁ ▸ K₁.end_mem_support) (e₂ ▸ K₂.end_mem_support)

end TangleDatum.IsFar

end GraphMinor.GM19
