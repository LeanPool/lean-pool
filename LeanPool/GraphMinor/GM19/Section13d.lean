/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13c

/-!
# Graph Minors XIX, Section 13: spokes as walks, and hubs at one vertex

These are the tools for (13.4). A spoke is read as a simple walk. Two spokes that meet share a final
part (`IsSpokeWalk.merge`).
There is a spoke at each vertex of `V(Γ) ∩ bd(W)` (`IsWheelHubOfRadius.exists_spoke`). A vertex on
every spoke that no small enclave
surrounds is a hub of smaller radius (`IsWheelHubOfRadius.hub_at`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- Two simple walks with the same ends and the same edges are the same walk. -/
theorem simple_walk_eq_of_edges {T : Type} [TopologicalSpace T] {G : Drawing T} {u a :
  T} (A B : GraphWalk G.toGraph u a)
    (hA : A.IsSimple) (hB : B.IsSimple) (hE : ∀ e, e ∈ A.edges ↔ e ∈ B.edges) : A = B := by
  obtain ⟨h, hwalk⟩ := simple_walk_eq_of_common_start_and_edges A B hA hB hE
  cases h
  exact hwalk

/-- In a simple walk, the part after a vertex does not depend on how the walk is split. -/
theorem tail_unique {α' β : Type*} {G : Graph α' β} {a x b : α'} (A A' : GraphWalk G a x)
  (T T' : GraphWalk G x b)
    (hs : (A.append T).IsSimple) (heq : A.append T = A'.append T') : T = T' ∧ A = A' := by
  induction A with
  | nil h =>
    cases A' with
    | nil _ => exact ⟨heq, rfl⟩
    | @cons _ c _ e hl r =>
      exfalso
      have h₁ : (GraphWalk.nil h).append T = T := rfl
      rw [h₁] at hs heq
      subst heq
      have hs' : (GraphWalk.cons hl (r.append T')).support.Nodup := hs
      refine (List.nodup_cons.mp hs').1 ?_
      exact (GraphWalk.mem_support_append r T').mpr (.inr T'.start_mem_support)
  | @cons a c x e hl r ih =>
    cases A' with
    | nil _ =>
      exfalso
      have h₁ : (GraphWalk.nil hl.left_mem).append T' = T' := rfl
      have hs' : (GraphWalk.cons hl (r.append T)).support.Nodup := hs
      have : a ∈ (r.append T).support := (GraphWalk.mem_support_append r T).mpr
        (.inl r.end_mem_support)
      exact (List.nodup_cons.mp hs').1 this
    | @cons _ c' _ e' hl' r' =>
      change GraphWalk.cons hl (r.append T) = GraphWalk.cons hl' (r'.append T') at heq
      injection heq with h₁ h₂ h₃ h₄ h₅
      subst h₂
      subst h₄
      obtain ⟨h₆, h₇⟩ := ih r' T T' (GraphWalk.IsSimple.of_cons hs) (eq_of_heq h₅)
      exact ⟨h₆, by rw [h₇]⟩

/-- The drawing with one vertex and no edge. -/
theorem point_drawing_facts {T : Type} [TopologicalSpace T] [T2Space T] (G : Drawing T) {u : T}
  (hu : u ∈ G.V) :
    (walkDrawing G (GraphWalk.nil hu)).V = {u} ∧ (walkDrawing G (GraphWalk.nil hu)).E = ∅ ∧
      (walkDrawing G (GraphWalk.nil hu)).U = {u} := by
  have hV : (walkDrawing G (GraphWalk.nil hu)).V = {u} := by
    rw [walkDrawing_V]
    ext x
    change x ∈ [u] ↔ _
    simp
  have hE : (walkDrawing G (GraphWalk.nil hu)).E = ∅ := by
    rw [walkDrawing_E]
    ext x
    simp [GraphWalk.edges]
  refine ⟨hV, hE, ?_⟩
  rw [Drawing.U_eq, hV, hE]
  simp

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {v h : Shat}

/-- A walk gives a path between the same ends with at most as many edges. -/
theorem exists_path_of_walk {T : Type} [TopologicalSpace T] [T2Space T] {G : Drawing T} {a b : T}
  (L : GraphWalk G.toGraph a b) :
    ∃ P : Drawing T, Drawing.IsPathOf P G a b ∧ P.E.ncard ≤ L.length := by
  classical
  obtain ⟨L', hs, -, he⟩ := GM11.GraphWalk.exists_isSimple L
  refine ⟨walkDrawing G L', ⟨walkDrawing_isSubdrawing _ _, walkDrawing_isPathBetween _ hs⟩, ?_⟩
  rw [ncard_walk_E G hs]
  exact (hs.edges_nodup.subperm he).length_le

/-- A spoke, read as a simple walk. -/
def IsSpokeWalk (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat) {v h : Shat}
  (K : GraphWalk D.rad.G.toGraph v h) : Prop :=
  K.IsSimple ∧ D.IsSpoke W H v h (walkDrawing D.rad.G K)

omit [T2Space S] in
theorem IsSpoke.exists_walk {P : Drawing Shat} (hS : D.IsSpoke W H v h P) :
    ∃ K : GraphWalk D.rad.G.toGraph v h, D.IsSpokeWalk W H K ∧ P = walkDrawing D.rad.G K := by
  obtain ⟨K, hK, hV, hE⟩ := Drawing.IsPathOf.exists_simple_walk hS.is_path
  have heq : P = walkDrawing D.rad.G K := by
    refine Drawing.ext_of_V_E ?_ ?_
    · rw [walkDrawing_V]
      ext x
      exact hV x
    · rw [walkDrawing_E]
      ext e
      exact hE e
  exact ⟨K, ⟨hK, heq ▸ hS⟩, heq⟩

omit [T2Space S] in
theorem IsSpokeWalk.mem_E {K : GraphWalk D.rad.G.toGraph v h} {e : Set Shat} :
    e ∈ (walkDrawing D.rad.G K).E ↔ e ∈ K.edges := by
  rw [walkDrawing_E]
  rfl

omit [T2Space S] in
theorem IsSpokeWalk.ncard {K : GraphWalk D.rad.G.toGraph v h} (hK : D.IsSpokeWalk W H K) :
    (walkDrawing D.rad.G K).E.ncard = K.length :=
  ncard_walk_E D.rad.G hK.1

omit [T2Space S] in
/-- A spoke walk is shortest among the walks from `v` to `V(H)`, and lightest among those of its
length. -/
theorem IsSpokeWalk.bound {K : GraphWalk D.rad.G.toGraph v h} (hK : D.IsSpokeWalk W H K) {h' :
  Shat} (hh' : h' ∈ H.V)
    (T : GraphWalk D.rad.G.toGraph v h') : K.length ≤ T.length ∧
      (T.length = K.length → D.tb.walkWeight K ≤ D.tb.walkWeight T) := by
  have : ConnectedSpace Shat := cap.connected
  have h₁ := hK.2.walk_bound hh' T
  rw [hK.ncard, D.tb.weightSub_eq_of_simple hK.1 (fun e ↦ IsSpokeWalk.mem_E)] at h₁
  exact h₁

omit [T2Space S] in
/-- The final part of a spoke walk is shortest and lightest too. -/
theorem IsSpokeWalk.tail_bound {u : Shat} {A : GraphWalk D.rad.G.toGraph v u} {B : GraphWalk
  D.rad.G.toGraph u h}
    (hK : D.IsSpokeWalk W H (A.append B)) {h' : Shat} (hh' : h' ∈ H.V)
      (T : GraphWalk D.rad.G.toGraph u h') :
    B.length ≤ T.length ∧ (T.length = B.length → D.tb.walkWeight B ≤ D.tb.walkWeight T) := by
  obtain ⟨h₁, h₂⟩ := hK.bound hh' (A.append T)
  simp only [GraphWalk.length_append, D.tb.walkWeight_append] at h₁ h₂
  refine ⟨by omega, fun heq ↦ ?_⟩
  have := h₂ (by omega)
  linarith

omit [T2Space S] in
/-- A spoke walk meets `V(H)` only in its last vertex. -/
theorem IsSpokeWalk.support_hub {K : GraphWalk D.rad.G.toGraph v h} (hK : D.IsSpokeWalk W H K) {y :
  Shat} (hy : y ∈ K.support)
    (hyH : y ∈ H.V) : y = h := by
  obtain ⟨A, B, rfl⟩ := K.exists_append_of_mem hy
  have h₁ := (hK.bound hyH A).1
  rw [GraphWalk.length_append] at h₁
  exact GraphWalk.eq_of_length_eq_zero (show B.length = 0 by omega)

omit [T2Space S] in
/-- Two spokes that meet have the same inner end. -/
theorem IsSpokeWalk.same_end {v₁ v₂ h₁ h₂ x : Shat} {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁} {K₂ :
  GraphWalk D.rad.G.toGraph v₂ h₂}
    (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂) (hx₁ : x ∈ K₁.support)
      (hx₂ : x ∈ K₂.support) : h₁ = h₂ := by
  have : ConnectedSpace Shat := cap.connected
  have hV : ∀ {a b : Shat} (K : GraphWalk D.rad.G.toGraph a b), x ∈ K.support → x ∈
    (walkDrawing D.rad.G K).V := by
    intro a b K hx
    rw [walkDrawing_V]
    exact hx
  exact (theorem_13_2_proof h1.2 h2.2 ⟨x, hV _ hx₁, hV _ hx₂⟩).1

omit [T2Space S] in
/-- **Two spokes that meet end the same way.** This is the proof of (13.2) for walks: `K₁ = A₁ + T`
and `K₂ = A₂ + T`, the
vertex `x` lies on `T`, and `A₁` meets `K₂` only in the first vertex of `T`. -/
theorem IsSpokeWalk.merge {v₁ v₂ h x : Shat} {K₁ : GraphWalk D.rad.G.toGraph v₁ h} {K₂ : GraphWalk
  D.rad.G.toGraph v₂ h}
    (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂) (hx₁ : x ∈ K₁.support)
      (hx₂ : x ∈ K₂.support) :
    ∃ (u : Shat) (A₁ : GraphWalk D.rad.G.toGraph v₁ u) (A₂ : GraphWalk D.rad.G.toGraph v₂ u)
      (T : GraphWalk D.rad.G.toGraph u h), K₁ = A₁.append T ∧ K₂ = A₂.append T ∧ x ∈ T.support ∧
      (∀ y ∈ A₁.support, y ∈ K₂.support → y = u) := by
  obtain ⟨u, hu, P₁, Q₁, rfl, hfirst⟩ := GraphWalk.exists_first_mem K₁ (X
    := {y | y ∈ K₂.support}) ⟨x, hx₁, hx₂⟩
  obtain ⟨P₂, Q₂, rfl⟩ := K₂.exists_append_of_mem hu
  have hh := h1.2.h_mem
  obtain ⟨b₁, w₁⟩ := h1.tail_bound hh Q₂
  obtain ⟨b₂, w₂⟩ := h2.tail_bound hh Q₁
  have hlen : Q₁.length = Q₂.length := by omega
  have hw : D.tb.walkWeight Q₁ = D.tb.walkWeight Q₂ := le_antisymm (w₁ hlen.symm) (w₂ hlen)
  have hs₁ : Q₁.IsSimple := (GraphWalk.IsSimple.of_append h1.1).2
  have hs₂ : Q₂.IsSimple := (GraphWalk.IsSimple.of_append h2.1).2
  obtain rfl := simple_walk_eq_of_edges Q₁ Q₂ hs₁ hs₂ (D.edges_eq_of_weight_eq hs₁ hs₂ hw)
  refine ⟨u, P₁, P₂, Q₁, rfl, rfl, ?_, hfirst⟩
  rcases (GraphWalk.mem_support_append P₁ Q₁).mp hx₁ with h' | h'
  · rw [hfirst x h' hx₂]
    exact Q₁.start_mem_support
  · exact h'

omit [T2Space S] in
/-- A spoke at each vertex of `V(Γ) ∩ bd(W)`. It exists since a shortest and then lightest path
exists, there being finitely many
paths. -/
theorem IsWheelHubOfRadius.exists_spoke (hW : D.IsWheelHubOfRadius W H ρ) (hv : v ∈
  (cap.emb '' D.Γ.V) ∩ discBd W) :
    ∃ (h : Shat) (K : GraphWalk D.rad.G.toGraph v h), D.IsSpokeWalk W H K := by
  classical
  let Ps : Set (Drawing Shat) := {P | P.IsSubdrawing D.rad.G ∧ ∃ z ∈ H.V, Drawing.IsPathOf P
    D.rad.G v z}
  have hfin : Ps.Finite := by
    refine Set.Finite.of_finite_image (f := fun C : Drawing Shat ↦ (C.V, C.E)) ?_ ?_
    · refine (D.rad.G.finite_V.finite_subsets.prod D.rad.G.finite_edges.finite_subsets).subset ?_
      rintro _ ⟨C, ⟨hs', -⟩, rfl⟩
      exact ⟨hs'.1, hs'.2⟩
    · intro C _ C' _ h
      exact Drawing.ext_of_V_E (congrArg Prod.fst h) (congrArg Prod.snd h)
  obtain ⟨P₀, z₀, hz₀, hP₀, -⟩ := (hW.bd_dist v hv).1
  have hne : Ps.Nonempty := ⟨P₀, hP₀.1, z₀, hz₀, hP₀⟩
  obtain ⟨P, ⟨-, z, hz, hP⟩, hmin⟩ := Set.exists_min_image Ps (fun P ↦ toLex
    (P.E.ncard, D.tb.weightSub P)) hfin hne
  have hS : D.IsSpoke W H v z P := by
    refine ⟨hv, hz, hP, ?_, ?_⟩
    · intro P' h' hh' hP'
      have := hmin P' ⟨hP'.1, h', hh', hP'⟩
      rcases Prod.Lex.toLex_le_toLex.mp this with h₁ | ⟨h₁, -⟩
      · exact h₁.le
      · exact h₁.le
    · intro P' h' hh' hP' heq
      have := hmin P' ⟨hP'.1, h', hh', hP'⟩
      rcases Prod.Lex.toLex_le_toLex.mp this with h₁ | ⟨-, h₁⟩
      · have h₁' : P.E.ncard < P'.E.ncard := h₁
        omega
      · exact h₁
  obtain ⟨K, hK, -⟩ := hS.exists_walk
  exact ⟨z, K, hK⟩

omit [T2Space S] in
/-- Walks from `V(Γ) ∩ bd(W)` to `V(H)` have at least `ρ - 1` edges. -/
theorem IsWheelHubOfRadius.walk_ge (hW : D.IsWheelHubOfRadius W H ρ) (hv : v ∈
  (cap.emb '' D.Γ.V) ∩ discBd W) {z : Shat}
    (hz : z ∈ H.V) (T : GraphWalk D.rad.G.toGraph v z) : ρ ≤ T.length + 1 := by
  obtain ⟨P, hP, hle⟩ := exists_path_of_walk T
  by_contra hn
  exact (hW.bd_dist v hv).2 ⟨P, z, hz, hP, by omega⟩

omit [T2Space S] in
/-- A spoke has `ρ` or `ρ - 1` edges. -/
theorem IsWheelHubOfRadius.spoke_length (hW : D.IsWheelHubOfRadius W H ρ) {K : GraphWalk
  D.rad.G.toGraph v h}
    (hK : D.IsSpokeWalk W H K) : K.length ≤ ρ ∧ ρ ≤ K.length + 1 := by
  refine ⟨?_, hW.walk_ge hK.2.v_mem hK.2.h_mem K⟩
  obtain ⟨P, z, hz, hP, hle⟩ := (hW.bd_dist v hK.2.v_mem).1
  have := hK.2.min_length P z hz hP
  rw [hK.ncard] at this
  omega

omit [T2Space S] in
/-- A vertex `u` of `Γ*` strictly inside `W`, at distance `T.length < ρ` from `H`, that lies on a
way from each vertex
of `V(Γ) ∩ bd(W)` to `H`, and that no small enclave surrounds, is a hub of radius `ρ - T.length`.
This is the claim in the
proof of (13.4). -/
theorem IsWheelHubOfRadius.hub_at (hW : D.IsWheelHubOfRadius W H ρ) {u h₀ : Shat}
  (huG : u ∈ D.rad.G.V)
    (T : GraphWalk D.rad.G.toGraph u h₀) (hh₀ : h₀ ∈ H.V) (hlt : T.length < ρ)
      (hu : u ∈ W \ discBd W)
    (hsp : ∀ v ∈ (cap.emb '' D.Γ.V) ∩ discBd W, ∃ A : GraphWalk D.rad.G.toGraph v u, A.length +
      T.length ≤ ρ)
    (hen : ∀ F : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 F → F.E.ncard ≤ 4 * ρ + 4
      → u ∉ D.ins F \ F.U) :
    D.IsWheelHubOfRadius W (walkDrawing D.rad.G (GraphWalk.nil huG)) (ρ - T.length) := by
  obtain ⟨hV, hE, hU⟩ := point_drawing_facts D.rad.G huG
  refine ⟨by omega, ?_, hW.is_disc, hW.bd_sub, walkDrawing_isSubdrawing _ _, ?_, ?_,
    hW.two_nbrs_in_W, hW.chord_in_W, ?_, ?_, ?_⟩
  · have := hW.rep_ge
    omega
  · rw [hU]
    exact singleton_subset_iff.mpr hu
  · intro F hF hle hsub
    exact hW.ins_sub F hF (by omega) hsub
  · refine .inl ⟨by rw [hV, ncard_singleton], hE, fun H' h₁ h₂ hsub ↦ ?_⟩
    rw [hV] at hsub
    exact hen H' h₁ (by omega) (hsub rfl)
  · rintro x hx ⟨P, z, hz, hP, hle⟩
    rw [hV] at hz
    obtain rfl : z = u := hz
    obtain ⟨L, hL⟩ := Drawing.IsPathOf.exists_walk hP
    obtain ⟨P', hP', hle'⟩ := exists_path_of_walk (L.append T)
    rw [GraphWalk.length_append] at hle'
    exact hW.close_in_W x hx ⟨P', h₀, hh₀, hP', by omega⟩
  · intro x hx
    obtain ⟨A, hA⟩ := hsp x hx
    obtain ⟨P, hP, hle⟩ := exists_path_of_walk A
    refine ⟨⟨P, u, by rw [hV]; rfl, hP, by omega⟩, ?_⟩
    rintro ⟨P', z, hz, hP', hle'⟩
    rw [hV] at hz
    obtain rfl : z = u := hz
    obtain ⟨L, hL⟩ := Drawing.IsPathOf.exists_walk hP'
    have := hW.walk_ge hx hh₀ (L.append T)
    rw [GraphWalk.length_append] at this
    omega

end TangleDatum

end GraphMinor.GM19
