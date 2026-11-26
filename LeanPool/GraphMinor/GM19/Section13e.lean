/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13d

/-!
# Graph Minors XIX, Section 13: the fan of two spokes that meet

`IsFan` is the setting of (13.4). The spokes are the walks `A₁ + T` and `A₂ + T`, the vertex `r*` of
`bd(W)` is joined to their
outer ends by the edges `f₁, f₂`, and the circuit `C` runs through `f₁, A₁, A₂, f₂`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- The two parts of a simple walk meet only where they are joined. -/
theorem GraphWalk.inter_of_simple {α' β : Type*} {G : Graph α' β} {a u b : α'} {A : GraphWalk G a
  u} {T : GraphWalk G u b}
    (hs : (A.append T).IsSimple) {x : α'} (h₁ : x ∈ A.support) (h₂ : x ∈ T.support) : x = u := by
  induction A with
  | nil h =>
    simpa [GraphWalk.support_nil] using h₁
  | @cons a c u e h r ih =>
    have hs' : (GraphWalk.cons h (r.append T)).support.Nodup := hs
    rcases List.mem_cons.mp h₁ with rfl | h₁'
    · exact absurd ((GraphWalk.mem_support_append r T).mpr (.inr h₂)) (List.nodup_cons.mp hs').1
    · exact ih (GraphWalk.IsSimple.of_cons hs) h₁' h₂

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r v₁ v₂ u h : Shat} {f₁
  f₂ : Set Shat}

omit [T2Space S] [T2Space Shat] in
/-- Two vertices of `Γ` are not adjacent in `Γ*`. -/
theorem not_link_hatV (D : TangleDatum cap χ) {g : Set Shat} {a b : Shat}
  (hl : D.rad.G.toGraph.IsLink g a b)
    (ha : a ∈ D.P.Γ.hatV cap) (hb : b ∈ D.P.Γ.hatV cap) : False := by
  obtain ⟨x, hx, y, hy, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hl.1
  have hab := hl.2.2.2
  have hya : y ∈ ({a, b} : Set Shat) := by
    rw [← hab, hcap]
    exact .inr rfl
  rcases hya with rfl | rfl
  · exact hy.2 ha
  · exact hy.2 hb

omit [T2Space S] [T2Space Shat] in
/-- A walk between two different vertices of `Γ` has at least two edges. -/
theorem two_le_of_hatV (D : TangleDatum cap χ) {a b : Shat} (A : GraphWalk D.rad.G.toGraph a b)
  (ha : a ∈ D.P.Γ.hatV cap)
    (hb : b ∈ D.P.Γ.hatV cap) (hab : a ≠ b) : 2 ≤ A.length := by
  cases A with
  | nil _ => exact absurd rfl hab
  | @cons _ c _ e hl r =>
    cases r with
    | nil _ => exact (D.not_link_hatV hl ha hb).elim
    | @cons _ c' _ e' hl' r' =>
      rw [GraphWalk.length_cons, GraphWalk.length_cons]
      omega

omit [T2Space S] in
/-- The ends of an edge of a walk lie on the walk. -/
theorem ends_mem_support (D : TangleDatum cap χ) {a b x y : Shat} (K : GraphWalk D.rad.G.toGraph a
  b) {e : Set Shat}
    (he : e ∈ K.edges) (hcap : closure e ∩ D.rad.G.V = {x, y}) : x ∈ K.support ∧ y ∈ K.support := by
  have heG : e ∈ D.rad.G.E := TieBreaker.mem_edges_E K he
  have hx : x ∈ closure e ∩ D.rad.G.V := by rw [hcap]; exact .inl rfl
  have hy : y ∈ closure e ∩ D.rad.G.V := by rw [hcap]; exact .inr rfl
  have hl : D.rad.G.toGraph.IsLink e x y := ⟨heG, hx.2, hy.2, hcap⟩
  have hl' : D.rad.G.toGraph.IsLink e y x := ⟨heG, hy.2, hx.2, by rw [hcap, pair_comm]⟩
  exact ⟨K.left_mem_support_of_mem_edges he hl, K.left_mem_support_of_mem_edges he hl'⟩

omit [T2Space S] in
/-- The tail of a spoke after a vertex does not depend on the spoke. -/
theorem IsSpokeWalk.tail_after {v v' a h : Shat} {L : GraphWalk D.rad.G.toGraph v a} {R : GraphWalk
  D.rad.G.toGraph a h}
    {A : GraphWalk D.rad.G.toGraph v' a} {R₁ : GraphWalk D.rad.G.toGraph a h}
      (h1 : D.IsSpokeWalk W H (L.append R))
    (h2 : D.IsSpokeWalk W H (A.append R₁)) : R = R₁ := by
  have ha₁ : a ∈ (L.append R).support := (GraphWalk.mem_support_append L R).mpr
    (.inl L.end_mem_support)
  have ha₂ : a ∈ (A.append R₁).support := (GraphWalk.mem_support_append A R₁).mpr
    (.inl A.end_mem_support)
  obtain ⟨u, B₁, B₂, T, h₁, h₂, ha, -⟩ := h1.merge h2 ha₁ ha₂
  obtain ⟨X, Y, rfl⟩ := T.exists_append_of_mem ha
  rw [← GraphWalk.append_assoc'] at h₁ h₂
  have e₁ := (tail_unique L (B₁.append X) R Y h1.1 h₁).1
  have e₂ := (tail_unique A (B₂.append X) R₁ Y h2.1 h₂).1
  rw [e₁, e₂]

/-- The setting of (13.4), with the two spokes read as walks. -/
structure IsFan (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat) (ρ : ℕ) (r : Shat)
  (f₁ f₂ : Set Shat)
    (A₁ : GraphWalk D.rad.G.toGraph v₁ u) (A₂ : GraphWalk D.rad.G.toGraph v₂ u)
      (T : GraphWalk D.rad.G.toGraph u h) : Prop where
  hub : D.IsWheelHubOfRadius W H ρ
  bd_off : discBd W ⊆ cap.emb '' (univ \ bd S)
  inner : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty
  r_mem : r ∈ D.rad.Rstar
  r_bd : r ∈ discBd W
  ne : v₁ ≠ v₂
  link₁ : D.rad.G.toGraph.IsLink f₁ r v₁
  link₂ : D.rad.G.toGraph.IsLink f₂ r v₂
  spoke₁ : D.IsSpokeWalk W H (A₁.append T)
  spoke₂ : D.IsSpokeWalk W H (A₂.append T)
  meet : ∀ y ∈ A₁.support, y ∈ A₂.support → y = u

variable {A₁ : GraphWalk D.rad.G.toGraph v₁ u} {A₂ : GraphWalk D.rad.G.toGraph v₂ u} {T : GraphWalk
  D.rad.G.toGraph u h}

omit [T2Space S] in
theorem IsFan.swap (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : D.IsFan W H ρ r f₂ f₁ A₂ A₁ T :=
  ⟨hf.hub, hf.bd_off, hf.inner, hf.r_mem, hf.r_bd, hf.ne.symm, hf.link₂, hf.link₁, hf.spoke₂,
    hf.spoke₁,
    fun y h₁ h₂ ↦ hf.meet y h₂ h₁⟩

/-- A walk from `r*` to the hub has at least `ρ` edges, by (13.1). -/
theorem IsFan.walk_from_r (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) {z : Shat} (hz : z ∈ H.V)
  (L : GraphWalk D.rad.G.toGraph r z) :
    ρ ≤ L.length := by
  obtain ⟨P, hP, hle⟩ := exists_path_of_walk L
  by_contra hn
  exact theorem_13_1_proof hf.hub hf.bd_off hf.inner hf.r_mem hf.r_bd ⟨P, z, hz, hP, by omega⟩

/-- `r*` is on no spoke, by (13.1). -/
theorem IsFan.r_notMem_spoke (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) {v h' : Shat} {K : GraphWalk
  D.rad.G.toGraph v h'}
    (hK : D.IsSpokeWalk W H K) : r ∉ K.support := by
  intro hr
  obtain ⟨L, R, rfl⟩ := K.exists_append_of_mem hr
  have h₁ := hf.walk_from_r hK.2.h_mem R
  have h₂ := (hf.hub.spoke_length hK).1
  rw [GraphWalk.length_append] at h₂
  have hpos : 1 ≤ L.length := by
    cases L with
    | nil _ => exact absurd hK.2.v_mem.1 hf.r_mem.2
    | @cons _ c _ e hl q =>
      rw [GraphWalk.length_cons]
      omega
  omega

omit [T2Space S] in
/-- The outer end of a spoke of the fan is not `u`. -/
theorem IsFan.v₁_ne (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : v₁ ≠ u := by
  rintro rfl
  have hs := (GraphWalk.IsSimple.of_append hf.spoke₁.1).1.length_eq_zero
  have h₂ := D.two_le_of_hatV A₂ hf.spoke₂.2.v_mem.1 hf.spoke₁.2.v_mem.1 hf.ne.symm
  have h₃ := (hf.hub.spoke_length hf.spoke₂).1
  have h₄ := (hf.hub.spoke_length hf.spoke₁).2
  rw [GraphWalk.length_append] at h₃ h₄
  omega

omit [T2Space S] in
theorem IsFan.A_pos (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : 1 ≤ A₁.length := by
  cases hA : A₁ with
  | nil _ => exact absurd rfl hf.v₁_ne
  | @cons _ c _ e hl q =>
    rw [GraphWalk.length_cons]
    omega

omit [T2Space S] in
theorem IsFan.T_lt (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : T.length < ρ := by
  have h₃ := (hf.hub.spoke_length hf.spoke₁).1
  have := hf.A_pos
  rw [GraphWalk.length_append] at h₃
  omega

omit [T2Space S] in
theorem IsFan.u_mem_G (_ : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : u ∈ D.rad.G.V :=
  T.mem_vertexSet_of_mem_support T.start_mem_support

/-- `u` is not on `bd(W)`. If `u ∈ V(Γ)` then `A₁` has at least two edges, and if not then (13.1)
applies. -/
theorem IsFan.u_notMem_bd (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : u ∉ discBd W := by
  intro hu
  have hh := hf.spoke₁.2.h_mem
  have h₃ := (hf.hub.spoke_length hf.spoke₁).1
  rw [GraphWalk.length_append] at h₃
  by_cases huV : u ∈ D.P.Γ.hatV cap
  · have h₁ := hf.hub.walk_ge ⟨huV, hu⟩ hh T
    have h₂ := D.two_le_of_hatV A₁ hf.spoke₁.2.v_mem.1 huV hf.v₁_ne
    omega
  · obtain ⟨P, hP, hle⟩ := exists_path_of_walk T
    have := hf.A_pos
    exact theorem_13_1_proof hf.hub hf.bd_off hf.inner ⟨hf.u_mem_G, huV⟩ hu ⟨P, h, hh, hP, by omega⟩

/-- The circuit of the fan. -/
structure IsFanCircuit (D : TangleDatum cap χ) (r : Shat) (f₁ f₂ : Set Shat)
  (A₁ : GraphWalk D.rad.G.toGraph v₁ u)
    (A₂ : GraphWalk D.rad.G.toGraph v₂ u) (C : Drawing Shat) : Prop where
  circuit : C.IsCircuitOf D.rad.G
  mem_V : ∀ x, x ∈ C.V ↔ x = r ∨ x ∈ A₁.support ∨ x ∈ A₂.support
  mem_E : ∀ e, e ∈ C.E ↔ e = f₁ ∨ e = f₂ ∨ e ∈ A₁.edges ∨ e ∈ A₂.edges
  card : C.E.ncard ≤ A₁.length + A₂.length + 2

omit [T2Space S] in
omit [T2Space Shat] in
theorem IsFanCircuit.swap {C : Drawing Shat} (h : D.IsFanCircuit r f₁ f₂ A₁ A₂ C) : D.IsFanCircuit
  r f₂ f₁ A₂ A₁ C := by
  refine ⟨h.circuit, fun x ↦ ?_, fun e ↦ ?_, by have := h.card; omega⟩
  · rw [h.mem_V x]
    tauto
  · rw [h.mem_E e]
    tauto

/-- The circuit of a fan exists. -/
theorem IsFan.exists_circuit (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : ∃ C, D.IsFanCircuit r f₁ f₂ A₁
  A₂ C := by
  classical
  have hA₁ : A₁.IsSimple := (GraphWalk.IsSimple.of_append hf.spoke₁.1).1
  have hA₂ : A₂.IsSimple := (GraphWalk.IsSimple.of_append hf.spoke₂.1).1
  have hr₁ : r ∉ A₁.support := fun h' ↦ hf.r_notMem_spoke hf.spoke₁
    ((GraphWalk.mem_support_append A₁ T).mpr (.inl h'))
  have hr₂ : r ∉ A₂.support := fun h' ↦ hf.r_notMem_spoke hf.spoke₂
    ((GraphWalk.mem_support_append A₂ T).mpr (.inl h'))
  set R₁ := GraphWalk.cons hf.link₁ A₁ with hR₁
  set R₂ := (GraphWalk.cons hf.link₂ A₂).reverse with hR₂
  have hs₁ : R₁.IsSimple := List.nodup_cons.mpr ⟨hr₁, hA₁⟩
  have hs₂' : (GraphWalk.cons hf.link₂ A₂).IsSimple := List.nodup_cons.mpr ⟨hr₂, hA₂⟩
  have hs₂ : R₂.IsSimple := hs₂'.reverse
  have hsup₁ : ∀ x, x ∈ R₁.support ↔ x = r ∨ x ∈ A₁.support := fun x ↦ by simp [hR₁]
  have hsup₂ : ∀ x, x ∈ R₂.support ↔ x = r ∨ x ∈ A₂.support := fun x ↦ by
    simp only [hR₂, GraphWalk.support_reverse, List.mem_reverse]
    simp
  have hed₁ : ∀ e, e ∈ R₁.edges ↔ e = f₁ ∨ e ∈ A₁.edges := fun e ↦ by simp [hR₁]
  have hed₂ : ∀ e, e ∈ R₂.edges ↔ e = f₂ ∨ e ∈ A₂.edges := fun e ↦ by
    simp only [hR₂, GraphWalk.edges_reverse, List.mem_reverse]
    simp
  have hcl : (R₁.append R₂).IsSimpleClosed := by
    refine GraphWalk.isSimpleClosed_append hs₁ hs₂ ?_ ?_
    · intro x h₁ h₂
      rcases (hsup₁ x).mp h₁ with rfl | h₁'
      · exact .inl rfl
      rcases (hsup₂ x).mp h₂ with rfl | h₂'
      · exact .inl rfl
      exact .inr (hf.meet x h₁' h₂')
    · intro e h₁ h₂
      rcases (hed₁ e).mp h₁ with rfl | h₁' <;> rcases (hed₂ e).mp h₂ with h₂' | h₂'
      · subst h₂'
        have hc := hf.link₁.2.2.2
        rw [hf.link₂.2.2.2] at hc
        have hm : v₂ ∈ ({r, v₁} : Set Shat) := by
          rw [← hc]
          exact .inr rfl
        rcases hm with rfl | hm
        · exact hf.r_mem.2 hf.spoke₂.2.v_mem.1
        · exact hf.ne hm.symm
      · exact hr₂ (A₂.left_mem_support_of_mem_edges h₂' hf.link₁)
      · subst h₂'
        exact hr₁ (A₁.left_mem_support_of_mem_edges h₁' hf.link₂)
      · obtain ⟨x, y, hxy, hx, hy, hcap⟩ := D.exists_ends_of_mem_edges A₁ h₁'
        obtain ⟨hx', hy'⟩ := D.ends_mem_support A₂ h₂' hcap
        exact hxy ((hf.meet x hx hx').trans (hf.meet y hy hy').symm)
  have hpos : 0 < (R₁.append R₂).length := by
    rw [GraphWalk.length_append, hR₁, GraphWalk.length_cons]
    omega
  refine ⟨walkDrawing _ (R₁.append R₂), ⟨walkDrawing_isSubdrawing _ _,
    isCircuit_walkDrawing _ hcl hpos⟩, fun x ↦ ?_, fun e ↦ ?_, ?_⟩
  · rw [walkDrawing_V]
    change x ∈ (R₁.append R₂).support ↔ _
    rw [GraphWalk.mem_support_append, hsup₁, hsup₂]
    tauto
  · rw [walkDrawing_E]
    change e ∈ (R₁.append R₂).edges ↔ _
    rw [GraphWalk.edges_append, List.mem_append, hed₁, hed₂]
    tauto
  · rw [walkDrawing_E]
    refine (ncard_mem_list_le _).trans ?_
    change (R₁.append R₂).length ≤ _
    rw [GraphWalk.length_append, hR₁, hR₂, GraphWalk.length_cons, GraphWalk.length_reverse,
      GraphWalk.length_cons]
    omega

omit [T2Space S] in
/-- `H` meets the circuit of the fan at most in `u`, and then `u` is the inner end. -/
theorem IsFan.hub_meet (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) {C : Drawing Shat}
  (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C) {x : Shat}
    (hx : x ∈ H.U) (hxC : x ∈ C.U) : x = u ∧ u = h := by
  have : ConnectedSpace Shat := cap.connected
  have hHW := hf.hub.H_in_int
  have hG := hC.circuit.1
  have key : ∀ z ∈ H.V, z ∈ C.V → z = u ∧ u = h := by
    intro z hz hzC
    have side : ∀ {v : Shat} {A : GraphWalk D.rad.G.toGraph v u}, D.IsSpokeWalk W H (A.append T)
      → z ∈ A.support →
        z = u ∧ u = h := by
      intro v A hA hzA
      have e₁ : z = h := hA.support_hub ((GraphWalk.mem_support_append A T).mpr (.inl hzA)) hz
      have e₂ : z = u := GraphWalk.inter_of_simple hA.1 hzA (e₁ ▸ T.end_mem_support)
      exact ⟨e₂, e₂.symm.trans e₁⟩
    rcases (hC.mem_V z).mp hzC with rfl | h₁ | h₂
    · exact absurd hf.r_bd (hHW (H.V_subset_U hz)).2
    · exact side hf.spoke₁ h₁
    · exact side hf.spoke₂ h₂
  by_cases hxV : x ∈ H.V
  · exact key x hxV (mem_V_of_mem_U hG hxC (hf.hub.H_sub.1 hxV))
  · obtain ⟨g, hg, hxg⟩ := H.exists_edge_of_mem hx hxV
    have hgG : g ∈ D.rad.G.E := hf.hub.H_sub.2 hg
    have hxG : x ∉ D.rad.G.V := ((hgG.2.1 hxg)).2
    have hxCV : x ∉ C.V := fun h' ↦ hxG (hG.1 h')
    obtain ⟨g', hg', hxg'⟩ := C.exists_edge_of_mem hxC hxCV
    obtain rfl := D.rad.G.edge_eq_of_mem hgG (hG.2 hg') hxg hxg'
    obtain ⟨a, ha, b, hb, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hgG
    have hl : D.rad.G.toGraph.IsLink g a b := ⟨hgG, D.rad.isPreRadial.2.1 ha, hb.1, hcap⟩
    have h₁ := Drawing.IsLink.mem_V_of_sub hf.hub.H_sub hl hg
    have h₂ := Drawing.IsLink.mem_V_of_sub hG hl hg'
    have e₁ := key a h₁.1 h₂.1
    have e₂ := key b h₁.2 h₂.2
    exact absurd (e₁.1.trans e₂.1.symm ▸ ha) hb.2

/-- A spoke through a vertex of the circuit of the fan has the same inner end. -/
theorem IsFan.spoke_end (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) {C : Drawing Shat}
  (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C)
    {v h' a : Shat} {K : GraphWalk D.rad.G.toGraph v h'} (hK : D.IsSpokeWalk W H K)
      (ha : a ∈ K.support) (haC : a ∈ C.V) :
    h' = h := by
  rcases (hC.mem_V a).mp haC with rfl | h₁ | h₂
  · exact absurd ha (hf.r_notMem_spoke hK)
  · exact hK.same_end hf.spoke₁ ha ((GraphWalk.mem_support_append A₁ T).mpr (.inl h₁))
  · exact hK.same_end hf.spoke₂ ha ((GraphWalk.mem_support_append A₂ T).mpr (.inl h₂))

omit [T2Space S] in
/-- After a vertex of `A₁`, a spoke follows `A₁`, then `T`. -/
theorem IsFan.spoke_tail_left (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) {v a : Shat} {L : GraphWalk
  D.rad.G.toGraph v a}
    {R : GraphWalk D.rad.G.toGraph a h} (hK : D.IsSpokeWalk W H (L.append R))
      (ha : a ∈ A₁.support) :
    ∃ X : GraphWalk D.rad.G.toGraph a u, R = X.append T ∧ (∀ e ∈ X.edges, e ∈ A₁.edges)
      ∧ ∀ x ∈ X.support, x ∈ A₁.support := by
  obtain ⟨Y, X, rfl⟩ := A₁.exists_append_of_mem ha
  have hs₁ := hf.spoke₁
  rw [GraphWalk.append_assoc'] at hs₁
  refine ⟨X, hK.tail_after hs₁, fun e he ↦ ?_, fun x hx ↦ ?_⟩
  · rw [GraphWalk.edges_append, List.mem_append]
    exact .inr he
  · exact (GraphWalk.mem_support_append Y X).mpr (.inr hx)

/-- After a vertex of the circuit of the fan, a spoke follows the circuit, then `T`. -/
theorem IsFan.spoke_tail (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) {C : Drawing Shat}
  (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C)
    {v a : Shat} {L : GraphWalk D.rad.G.toGraph v a} {R : GraphWalk D.rad.G.toGraph a h}
      (hK : D.IsSpokeWalk W H (L.append R))
    (haC : a ∈ C.V) :
    ∃ X : GraphWalk D.rad.G.toGraph a u, R = X.append T ∧ (∀ e ∈ X.edges, e ∈ C.E)
      ∧ ∀ x ∈ X.support, x ∈ C.V := by
  rcases (hC.mem_V a).mp haC with rfl | h₁ | h₂
  · exact absurd ((GraphWalk.mem_support_append L R).mpr (.inl L.end_mem_support))
      (hf.r_notMem_spoke hK)
  · obtain ⟨X, h₃, h₄, h₅⟩ := hf.spoke_tail_left hK h₁
    exact ⟨X, h₃, fun e he ↦ (hC.mem_E e).mpr (.inr (.inr (.inl (h₄ e he)))),
      fun x hx ↦ (hC.mem_V x).mpr (.inr (.inl (h₅ x hx)))⟩
  · obtain ⟨X, h₃, h₄, h₅⟩ := hf.swap.spoke_tail_left hK h₂
    exact ⟨X, h₃, fun e he ↦ (hC.mem_E e).mpr (.inr (.inr (.inr (h₄ e he)))),
      fun x hx ↦ (hC.mem_V x).mpr (.inr (.inr (h₅ x hx)))⟩

omit [T2Space S] in
theorem IsFan.card_lt (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) {C : Drawing Shat}
  (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C) :
    C.E.ncard ≤ 2 * ρ + 2 ∧ C.E.ncard < 2 * D.rep := by
  have h₁ := (hf.hub.spoke_length hf.spoke₁).1
  have h₂ := (hf.hub.spoke_length hf.spoke₂).1
  rw [GraphWalk.length_append] at h₁ h₂
  have h₃ := hC.card
  have h₄ := hf.hub.rep_ge
  omega

omit [T2Space S] in
/-- The disc in `W` bounded by a short circuit is its inside, since `W` is a wheel and `W` is not
all of `Σ̂`. -/
theorem IsWheelHubOfRadius.eq_ins_of_disc (hW : D.IsWheelHubOfRadius W H ρ) {C : Drawing Shat}
  (hC : C.IsCircuitOf D.rad.G)
    (hle : C.E.ncard ≤ 4 * ρ + 4) {Δ : Set Shat} (hΔ : IsClosedDisc Δ) (hΔW : Δ ⊆ W)
      (hbd : discBd Δ = C.U) : Δ = D.ins C := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlt : C.E.ncard < 2 * D.rep := by
    have := hW.rep_ge
    omega
  have hs := D.ins_spec hC hlt
  have hsub : D.ins C ⊆ W := hW.ins_sub C hC hle (by
    rw [← hbd]
    exact (Surface.discBd_subset Δ).trans hΔW)
  by_contra hne
  have hcov := cover_of_discBd_eq hT hΔ hs.2.2.1 (hbd.trans hs.2.2.2.1.symm) hne
  obtain ⟨p, hp⟩ := hW.isConnected_compl.nonempty
  have : p ∈ Δ ∪ D.ins C := by
    rw [hcov]
    exact mem_univ p
  rcases this with h' | h'
  · exact hp (hΔW h')
  · exact hp (hsub h')

omit [T2Space S] in
/-- Strictly inside a circuit means in the interior of its inside. -/
theorem ins_diff_iff (D : TangleDatum cap χ) {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
  (hlt : F.E.ncard < 2 * D.rep)
    {x : Shat} : x ∈ D.ins F \ F.U ↔ x ∈ interior (D.ins F) := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length (D.isSlope (by omega)) hF.2 hF.1 hlt
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra hn
    apply h₂
    rw [← hfr, frontier, hcl.closure_eq]
    exact ⟨h₁, hn⟩
  · intro h'
    refine ⟨interior_subset h', fun hu ↦ ?_⟩
    rw [← hfr, frontier] at hu
    exact hu.2 h'

omit [T2Space S] in
/-- A part of a simple walk that starts off the strict inside of a circuit and meets the circuit at
most in its last vertex
misses the strict inside of the circuit. -/
theorem part_outside (D : TangleDatum cap χ) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hlt : C.E.ncard < 2 * D.rep)
    {s e : Shat} (L : GraphWalk D.rad.G.toGraph s e) (hs : L.IsSimple) (hout : s ∉ D.ins C \ C.U)
    (hfirst : ∀ y ∈ L.support, y ∈ C.V → y = e) {p : Shat} (hp : p ∈ (walkDrawing D.rad.G L).U)
      (hpi : p ∈ D.ins C) :
    p ∈ C.U := by
  have : ConnectedSpace Shat := cap.connected
  have hsl := D.isSlope (by omega)
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length hsl hC.2 hC.1 hlt
  have hvert : ∀ x ∈ L.support, x ∉ D.ins C \ C.U := by
    intro x hx hxi
    obtain ⟨L₁, L₂, rfl⟩ := L.exists_append_of_mem hx
    obtain ⟨a, ha, haC⟩ := D.walk_meets_circuit hC hlt L₁.reverse hxi.1 hout
    have ha' : a ∈ L₁.support := by simpa [GraphWalk.support_reverse] using ha
    have hae := hfirst a ((GraphWalk.mem_support_append L₁ L₂).mpr (.inl ha')) haC
    subst hae
    have := GraphWalk.inter_of_simple hs ha' L₂.end_mem_support
    subst this
    exact hxi.2 (C.V_subset_U haC)
  have hvert' : ∀ x ∈ L.support, x ∈ D.ins C → x ∈ C.V := by
    intro x hx hxi
    by_contra hn
    exact hvert x hx ⟨hxi, fun hu ↦ hn (mem_V_of_mem_U hC.1 hu (L.mem_vertexSet_of_mem_support hx))⟩
  rcases (mem_walkDrawing_U _ _).mp hp with hp' | ⟨g, hg, hpg⟩
  · exact C.V_subset_U (hvert' p hp' hpi)
  · by_cases hgC : g ∈ C.E
    · exact C.closure_subset_U hgC hpg
    have hgE : g ∈ D.rad.G.E := TieBreaker.mem_edges_E L hg
    obtain ⟨x, y, hxy, hx, hy, hcap⟩ := D.exists_ends_of_mem_edges L hg
    have hmem : ∀ z, z ∈ closure g ∩ D.rad.G.V → z ∈ L.support := by
      intro z hz
      rw [hcap] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    rcases closure_edge_subset hgE hpg with h' | h'
    · have hsub : g ⊆ D.ins C := by
        rcases edge_subset_or_disjoint_of_length hsl hC.2 hC.1 hlt hgE with h₁ | h₁
        · exact h₁
        · exact absurd hpi (disjoint_left.mp h₁ h')
      have hcl' := closure_minimal hsub hcl
      have hxc : x ∈ closure g ∩ D.rad.G.V := by rw [hcap]; exact .inl rfl
      have hyc : y ∈ closure g ∩ D.rad.G.V := by rw [hcap]; exact .inr rfl
      have hxV := hvert' x hx (hcl' hxc.1)
      have hyV := hvert' y hy (hcl' hyc.1)
      exact absurd ((hfirst x hx hxV).trans (hfirst y hy hyV).symm) hxy
    · exact C.V_subset_U (hvert' p (hmem p ⟨hpg, h'⟩) hpi)

/-- A part of a spoke between two points of `ins(F)`, for an enclave `F`, lies in `ins(F)`. -/
theorem IsSpokeWalk.part_in_ins {F : Drawing Shat} (hF : IsEnclave D.tb D.ord D.𝒯 F) {v a b h :
  Shat}
    {A : GraphWalk D.rad.G.toGraph v a} {M : GraphWalk D.rad.G.toGraph a b} {B : GraphWalk
      D.rad.G.toGraph b h}
    (hK : D.IsSpokeWalk W H (A.append (M.append B))) (ha : a ∈ D.ins F) (hb : b ∈ D.ins F) :
    (∀ z ∈ M.support, z ∈ D.ins F) ∧ ∀ e ∈ M.edges, e ⊆ D.ins F := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨ord', 𝒯', h𝒯', hc, hlt, -⟩ := id hF
  have hlt' : F.E.ncard < 2 * D.rep := hlt
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length (D.isSlope (by omega)) hc.2 hc.1 hlt'
  have hE : ∀ {K : GraphWalk D.rad.G.toGraph v h}, ∀ e, e ∈ (walkDrawing D.rad.G K).E ↔ e ∈ K.edges
    := fun e ↦ IsSpokeWalk.mem_E
  have hMin : ∀ z ∈ M.support, z ∈ D.ins F := by
    intro z hz
    by_contra hzn
    obtain ⟨M₁, M₂, rfl⟩ := M.exists_append_of_mem hz
    have heq : A.append ((M₁.append M₂).append B) = (A.append M₁).append (M₂.append B) := by
      rw [GraphWalk.append_assoc', GraphWalk.append_assoc']
    obtain ⟨p, hp, hpF⟩ := D.walk_meets_circuit hc hlt' M₁ ha fun h' ↦ hzn h'.1
    obtain ⟨q, hq, hqF⟩ := D.walk_meets_circuit hc hlt' M₂.reverse hb fun h' ↦ hzn h'.1
    have hq' : q ∈ (M₂.append B).support :=
      (GraphWalk.mem_support_append M₂ B).mpr (.inl (by simpa [GraphWalk.support_reverse] using hq))
    have hp' : p ∈ (A.append M₁).support := (GraphWalk.mem_support_append A M₁).mpr (.inr hp)
    rw [heq] at hK
    have hzF := hK.2.mem_of_between hF (K₁ := A.append M₁) (K₂ := M₂.append B) hK.1 (fun e ↦ hE e)
      ⟨p, hp', hpF⟩ ⟨q, hq', hqF⟩
    exact hzn (hU (F.V_subset_U hzF))
  refine ⟨hMin, fun e he ↦ ?_⟩
  obtain ⟨x, y, hl, M₁, M₂, rfl⟩ := GraphWalk.exists_split_edge M he
  have hxm : x ∈ (M₁.append (GraphWalk.cons hl M₂)).support :=
    (GraphWalk.mem_support_append _ _).mpr (.inl M₁.end_mem_support)
  have hym : y ∈ (M₁.append (GraphWalk.cons hl M₂)).support :=
    (GraphWalk.mem_support_append _ _).mpr (.inr (by simp [M₂.start_mem_support]))
  by_cases hxF : x ∈ F.V
  · by_cases hyF : y ∈ F.V
    · have heq : A.append ((M₁.append (GraphWalk.cons hl M₂)).append B) =
          (A.append M₁).append ((GraphWalk.cons hl (GraphWalk.nil hl.right_mem)).append
            (M₂.append B)) := by
        simp only [GraphWalk.append_assoc']
        rfl
      rw [heq] at hK
      have hin := hK.2.subwalk_in_enclave hF (GraphWalk.cons hl (GraphWalk.nil hl.right_mem)) hK.1
        (fun f ↦ hE f) hxF hyF
      have heF := hin e (by simp)
      exact fun q hq ↦ hU (F.closure_subset_U heF (subset_closure hq))
    · have hl' : D.rad.G.toGraph.IsLink e y x := ⟨hl.1, hl.2.2.1, hl.2.1, by rw [hl.2.2.2,
        pair_comm]⟩
      exact (D.edge_inside_of_mem hc hlt' hl' ⟨hMin y hym, fun hu ↦ hyF
        (mem_V_of_mem_U hc.1 hu hl.right_mem)⟩).1
  · exact (D.edge_inside_of_mem hc hlt' hl ⟨hMin x hxm, fun hu ↦ hxF (mem_V_of_mem_U hc.1 hu
      hl.left_mem)⟩).1

end TangleDatum

end GraphMinor.GM19
