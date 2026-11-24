/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffCollar

/-!
# The core of a collar

Graph Minors VII, (5.9), pages 234-235. For one cuff `C` we collect what the first half of the
paper's proof gives: the disc of `A(C)`, the circuits `B_i(C)`, the circuit `N(C)` cut in pieces
`N_i(C)`, the paths `Q_i`, and the ends of the paths `P_i` past `N(C)`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

/-- A simple walk that meets the circuit `N` only at its last vertex stays on one side of the
circuit. Here `Ω` and `Ω'` are the two sides, as open sets of `T`. -/
theorem walk_stays_side {G N : Drawing S} (hN : N.IsSubdrawing G) {j : S → T}
  (hj : Continuous j) {Ω Ω' : Set T} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hd : Disjoint Ω Ω') (hcov : ∀ z, z ∉ N.U → j z ∈ Ω ∪ Ω') (hoffΩ : ∀ z, j z ∈ Ω
      → z ∉ N.U) {y t : S} (W : GraphWalk G.toGraph y t) (hs : W.IsSimple)
        (hoff : ∀ z ∈ W.support, z ≠ t → z ∉ N.V) (hy : j y ∈ Ω) :
    (∀ z ∈ W.support, z = t ∨ j z ∈ Ω) ∧ ∀ e ∈ W.edges, ∀ z ∈ e, j z ∈ Ω := by
  induction W with
  | nil _ =>
    refine ⟨fun z hz => .inl (List.mem_singleton.mp hz), fun e he => ?_⟩
    simp [GraphWalk.edges] at he
  | @cons u' v' w' e h r ih =>
    have hoffU : u' ∉ N.U := hoffΩ u' hy
    have hcl : u' ∈ closure e := (h.2.2.2 ▸ mem_insert _ _ : u' ∈ closure e ∩ G.V).1
    have hcl' : v' ∈ closure e := (h.2.2.2 ▸ mem_insert_of_mem _ rfl : v' ∈ closure e ∩ G.V).1
    have heN : e ∉ N.E := fun h1 => hoffU (N.closure_subset_U h1 hcl)
    have heoff : ∀ x ∈ e, x ∉ N.U := fun x hx hxU => by
      have hxV : x ∉ N.V := fun h2 => (h.1.2.1 hx).2 (hN.1 h2)
      obtain ⟨e', he'', hxe'⟩ := N.exists_edge_of_mem hxU hxV
      exact heN (arcComponent_eq h.1 (hN.2 he'') hx hxe' ▸ he'')
    have hpre : IsPreconnected (j '' e) := h.1.2.2.1.isConnected.isPreconnected.image _
      hj.continuousOn
    have hmeet : (j '' e ∩ Ω).Nonempty := by
      have h2 : j u' ∈ closure (j '' e) := map_mem_closure hj hcl fun x hx => mem_image_of_mem j hx
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp h2 _ hΩ hy
      exact ⟨w, hw2, hw1⟩
    have hsub : j '' e ⊆ Ω ∪ Ω' := by
      rintro _ ⟨x, hx, rfl⟩
      exact hcov x (heoff x hx)
    have heΩ : j '' e ⊆ Ω := hpre.subset_left_of_subset_union hΩ hΩ' hd hsub hmeet
    have hnd : r.support.Nodup := (List.nodup_cons.mp hs).2
    by_cases hvt : v' = w'
    · subst hvt
      have hr : r.support = [v'] ∧ r.edges = [] := by
        cases r with
        | nil _ => exact ⟨rfl, rfl⟩
        | cons h' r' =>
          have h1 : (_ :: r'.support).Nodup := hnd
          exact absurd r'.end_mem_support (List.nodup_cons.mp h1).1
      refine ⟨fun z hz => ?_, fun e' he' z hz => ?_⟩
      · rw [GraphWalk.support, List.mem_cons, hr.1, List.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact .inr hy
        · exact .inl rfl
      · rw [GraphWalk.edges, List.mem_cons, hr.2] at he'
        rcases he' with rfl | he'
        · exact heΩ (mem_image_of_mem j hz)
        · simp at he'
    · have hvN : v' ∉ N.U := fun hU => hoff v' (List.mem_cons_of_mem _ r.start_mem_support) hvt
        (mem_V_of_subdrawing hN hU h.2.2.1)
      have hvΩ : j v' ∈ Ω := by
        rcases hcov v' hvN with h1 | h1
        · exact h1
        · have h2 : j v' ∈ closure (j '' e) := map_mem_closure hj hcl' fun x hx
            => mem_image_of_mem j hx
          obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp h2 _ hΩ' h1
          exact absurd hw1 (disjoint_left.mp hd (heΩ hw2))
      obtain ⟨i1, i2⟩ := ih hnd (fun z' hz' hne => hoff z' (List.mem_cons_of_mem _ hz') hne) hvΩ
      refine ⟨fun z hz => ?_, fun e' he' z hz => ?_⟩
      · rw [GraphWalk.support, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact .inr hy
        · exact i1 z hz
      · rw [GraphWalk.edges, List.mem_cons] at he'
        rcases he' with rfl | he'
        · exact heΩ (mem_image_of_mem j hz)
        · exact i2 e' he' z hz

/-- The form of `walk_stays_side` for all the points of a walk. -/
theorem walk_U_stays_side [T2Space S] {G N : Drawing S} (hN : N.IsSubdrawing G) {j : S → T}
  (hj : Continuous j) {Ω Ω' : Set T} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hd : Disjoint Ω Ω') (hcov : ∀ z, z ∉ N.U → j z ∈ Ω ∪ Ω') (hoffΩ : ∀ z, j z ∈ Ω
      → z ∉ N.U) {y t : S} (W : GraphWalk G.toGraph y t) (hs : W.IsSimple)
        (hoff : ∀ z ∈ W.support, z ≠ t → z ∉ N.V) (hy : j y ∈ Ω) :
    ∀ z ∈ (walkDrawing G W).U, z = t ∨ j z ∈ Ω := fun z hz => by
  obtain ⟨h1, h2⟩ := walk_stays_side hN hj hΩ hΩ' hd hcov hoffΩ W hs hoff hy
  rcases walk_U_cases hz with h3 | ⟨e, he, hze⟩
  · exact h1 z h3
  · exact .inr (h2 e he z hze)

/-- The part of a path past a circuit `N`. Let `P` be a path of `G` that ends off the disc `E` of
`N`, and that meets `N`. Then `P` has a connected part from a vertex of `N` to the end, whose other
points are off `E`. The vertex is in any `Rv` that has all the vertices shared by `P` and `N`. -/
theorem exists_gate [T2Space S] [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) {G N P : Drawing S}
  (hN : N.IsSubdrawing G) (hP : P.IsSubdrawing G) {j : S → T} (hj : Continuous j)
    (hji : Injective j) {E : Set T} (hE : IsClosedDisc E) (hb : discBd E = j '' N.U) {u v : S}
      (hpath : P.IsPathBetween u v) (hv : j v ∉ E) (hmeet : (P.V ∩ N.V).Nonempty) :
    ∃ Γ w, IsPreconnected Γ ∧ Γ ⊆ P.U ∧ w ∈ Γ ∧ v ∈ Γ ∧ w ∈ P.V ∩ N.V ∧ ∀ z ∈ Γ, z ≠ w → j z ∉ E
      := by
  classical
  obtain ⟨W₀, hs₀, hV₀, hE₀⟩ := hpath
  obtain ⟨W, hsW, heW⟩ := hP.exists_walk_up W₀
  have hvs : v ∈ W.support := by
    rw [hsW]
    exact W₀.end_mem_support
  obtain ⟨y₀, hy₀, hy₀N⟩ := hmeet
  have hsupP : ∀ z ∈ W.support, z ∈ P.V := fun z hz => by
    rw [hV₀]
    rw [hsW] at hz
    exact hz
  have hy₀W : y₀ ∈ W.support := by
    rw [hsW]
    rw [hV₀] at hy₀
    exact hy₀
  obtain ⟨w, hwN, T', hT'e, hT's, hT'A⟩ := exists_last_in N.V W ⟨y₀, hy₀W, hy₀N⟩
  obtain ⟨W₁, hs₁, hs₁', he₁⟩ := GraphWalk.exists_isSimple T'.reverse
  have hsup : ∀ z ∈ W₁.support, z ∈ T'.support := fun z hz => by
    have h1 := hs₁' z hz
    rwa [GraphWalk.support_reverse, List.mem_reverse] at h1
  have hedg : ∀ e ∈ W₁.edges, e ∈ W.edges := fun e he => by
    have h1 := he₁ e he
    rw [GraphWalk.edges_reverse, List.mem_reverse] at h1
    exact hT'e.subset h1
  have hP' : ∀ z ∈ (walkDrawing G W₁).U, z ∈ P.U := fun z hz => by
    rcases walk_U_cases hz with h1 | ⟨e, he, hze⟩
    · exact P.V_subset_U (hsupP z (hT's z (hsup z h1)))
    · have h2 : e ∈ P.E := by
        rw [hE₀, ← heW]
        exact hedg e he
      exact P.closure_subset_U h2 (subset_closure hze)
  have hd : Disjoint Eᶜ (discInt E) := disjoint_left.mpr fun x hx hx' => hx hx'.1
  have hstay := walk_U_stays_side hN hj hE.isClosed.isOpen_compl (hE.isOpen_discInt hman) hd
    (fun z hz => by
    by_cases h1 : j z ∈ E
    · exact .inr ⟨h1, fun h2 => hz (by
        rw [hb] at h2
        obtain ⟨x, hx, he⟩ := h2
        exact hji he ▸ hx)⟩
    · exact .inl h1) (fun z hz hU => hz (Surface.discBd_subset E (hb ▸ mem_image_of_mem j hU))) W₁
        hs₁ (fun z hz hne hzN => hne (hT'A z (hsup z hz) hzN)) hv
  have hpb := walkDrawing_isPathBetween G hs₁
  refine ⟨(walkDrawing G W₁).U, w, isPreconnected_of_isPathBetween hpb, hP', ?_, ?_, ⟨?_, hwN⟩,
    fun z hz hne => ?_⟩
  · exact (mem_walkDrawing_U G W₁).mpr (.inl W₁.end_mem_support)
  · exact (mem_walkDrawing_U G W₁).mpr (.inl W₁.start_mem_support)
  · exact hsupP w (hT's w T'.start_mem_support)
  · rcases hstay z hz with h1 | h1
    · exact absurd h1 hne
    · exact h1

/-- What the first half of the proof of (5.9) gives at one cuff `C`, in the capped surface `T`. Here
`Nk` is `N(C)` with its disc `E₀`, the `R i` are the pieces `N_i(C)`, the walks `Q i` go from the
vertices `x i` on `C` to the vertices `t i` of `R i`, and `Bo` with the disc `Do` is the outermost
circuit. The disc `Δ'` is where the boxes will be. The circuits `L i` in their discs `El i` are the
circuits `B_j(C)` past `N(C)`, all in the disc `Y`. -/
structure IsCuffCore (G : Drawing S) (C : Set S) (j : S → T) (D : Set T) (r v : ℕ) {ks m : ℕ}
  (Y E₀ Δ' Do : Set T) (Nk Bo : Drawing S) (R : Fin ks → Drawing S) (x t : Fin ks → S)
    (Q : ∀ i, GraphWalk G.toGraph (x i) (t i)) (L : Fin m → Drawing S) (El : Fin m
      → Set T) : Prop where
  nkSub : Nk.IsSubdrawing G
  nkCirc : Nk.IsCircuit
  discE : IsClosedDisc E₀
  bdE : discBd E₀ = j '' Nk.U
  DinE : D ⊆ discInt E₀
  discΔ : IsClosedDisc Δ'
  EΔ : E₀ ⊆ Δ' \ discBd Δ'
  discO : IsClosedDisc Do
  boSub : Bo.IsSubdrawing G
  boCirc : Bo.IsCircuit
  bdO : discBd Do = j '' Bo.U
  ΔO : Δ' ⊆ Do \ discBd Do
  offO : Disjoint Do (bd T)
  reach : ∀ y ∈ Bo.V, ∃ X, IsScriptASet G r C X ∧ y ∈ X
  Rsub : ∀ i, (R i).IsSubdrawing Nk
  Rpath : ∀ i, ∃ a b, (R i).IsPathBetween a b
  Rdis : ∀ i i', i ≠ i' → Disjoint (R i).V (R i').V
  Rcov : ∀ y ∈ Nk.V, ∃ i, y ∈ (R i).V
  xmem : ∀ i, x i ∈ G.V ∩ C
  tmem : ∀ i, t i ∈ (R i).V
  Qsimple : ∀ i, (Q i).IsSimple
  Qin : ∀ i, ∀ z ∈ (Q i).support, z = t i ∨ z ∈ G.V ∩ j ⁻¹' discInt E₀
  Qdis : ∀ i i', i ≠ i' → Disjoint {z | z ∈ (Q i).support} {z | z ∈ (Q i').support}
  ks2 : 2 ≤ ks
  kcard : ks = (G.V ∩ C).ncard
  inner : ∀ F : Set S, IsOArc F → G.IsNormal F → (G.V ∩ F).ncard ≤ v → SurroundsCuff F C → Disjoint
    (j ⁻¹' discInt E₀) F → False
  discY : IsClosedDisc Y
  YO : Y ⊆ Do
  ΔY : Δ' ⊆ Y
  layerSub : ∀ i, (L i).IsSubdrawing G
  layerDisc : ∀ i, IsClosedDisc (El i)
  layerBd : ∀ i, discBd (El i) = j '' (L i).U
  layerIn : ∀ i, D ⊆ discInt (El i)
  layerY : ∀ i, El i ⊆ Y
  layerOff : ∀ i, Disjoint Δ' (discBd (El i))
  layerDis : ∀ i i', i ≠ i' → Disjoint (L i).V (L i').V
  mv : v ≤ 2 * m
  gates : ∀ i, ∃ (Γ : Fin v → Set S) (w y : Fin v → S), (∀ a, IsPreconnected (Γ a) ∧ Γ a ⊆ G.U
    ∧ w a ∈ Γ a ∧ y a ∈ Γ a ∧ w a ∈ (R i).V ∧ j (y a) ∉ Y ∧ j (y a) ∈ Do ∧ ∀ z ∈ Γ a, z ≠ w a
      → j z ∉ E₀ ∧ j z ∈ Do) ∧ ∀ a a', a ≠ a' → Disjoint (G.V ∩ Γ a) (G.V ∩ Γ a')

private theorem inner_surrounding_arc_forbidden
    {S : Type u}
    {T : Type u}
    [TopologicalSpace S]
    [TopologicalSpace T]
    (hS : IsSurface S)
    {C : Set S}
    {j : S → T}
    {D : Set T}
    (hc : IsCappedCuff C T j D)
    {G : Drawing S}
    {v : ℕ}
    [T2Space T]
    (hman : ∀ (x : T), IsManifoldPoint x)
    (hji : Injective j)
    (ks : ℕ)
    (hks : 2 ≤ ks)
    (ra : ℕ)
    (hra : ra = v * ks)
    (hks1 : ks ≤ ra)
    (E : Set T)
    (hd : IsCuffDisc G j D ra E)
    (hmax : ∀ (Δ' : Set T), IsCuffDisc G j D ra Δ' → cuffCount G j Δ' ≤ cuffCount G j E)
    (Δ : Set T)
    (β : ℕ)
    (B : ℕ → Drawing S)
    (Ds : ℕ → Set T)
    (hn : IsCuffNest G j C E (ra + (β + 3)) (β + 3) B Ds Δ)
    (Δ₂ : Set T)
    (N : Fin β → Drawing S)
    (En : Fin β → Set T)
    (hsd : ∀ {t t' : ℕ}, t < t' → t' < β + 3 → Ds t ⊆ Ds t' \ discBd (Ds t'))
    (hE0 : E ⊆ Ds 0)
    (hEn : ∀ (l : Fin β), IsClosedDisc (En l) ∧ discBd (En l) = j '' (N l).U ∧ Ds 1 ⊆ En l ∧ En l
      ⊆ Δ₂)
    (hDint : ∀ (l : Fin β), D ⊆ discInt (En l))
    (l0 : Fin β)
    (F : Set S)
    (hO : IsOArc F)
    (hnF : G.IsNormal F)
    (hcard : (G.V ∩ F).ncard ≤ v)
    (hs : SurroundsCuff F C)
    (hdj : Disjoint (j ⁻¹' discInt (En l0)) F) :
    False := by
  obtain ⟨Δ_F, hΔF, hDF, hbF⟩ := exists_disc_of_surrounds hS hc hO hs
  have hpre : j ⁻¹' discBd Δ_F = F := by
    rw [hbF]
    exact preimage_image_eq F hji
  have hB' : IsCuffDisc G j D ra Δ_F := by
    refine ⟨hΔF, hDF, ?_, ?_⟩
    · rw [hpre]
      exact hnF
    · rw [hpre]
      refine hcard.trans ?_
      rw [hra]
      nlinarith
  have h5 := hmax Δ_F hB'
  have hoffI : Disjoint (discInt (En l0)) (discBd Δ_F) := by
    rw [hbF, disjoint_left]
    rintro _ h6 ⟨y, hy, rfl⟩
    exact disjoint_left.mp hdj h6 hy
  obtain ⟨d, hdD⟩ := hc.isClosedDisc.nonempty_discInt
  have hsubF : En l0 ⊆ Δ_F := disc_subset_of_int_off_bd hman (hEn l0).1 hΔF hoffI ⟨d, hDint l0
    hdD.1, hDF hdD.1⟩
  have hE₂ : E ⊆ Δ_F := hE0.trans ((hsd (by omega) (by omega)).trans (sdiff_subset.trans
    ((hEn l0).2.2.1.trans hsubF)))
  have hinf : (B 0).U.Infinite := by
    have h6 := isOArc_infinite_any (hn.disc 0 (by omega)).isOArc_discBd
    rw [hn.bd_eq 0 (by omega)] at h6
    exact fun hf => h6 (hf.image j)
  obtain ⟨y, hy, hyV⟩ := (hinf.sdiff (B 0).finite_V).nonempty
  obtain ⟨e, he, hye⟩ := (B 0).exists_edge_of_mem hy hyV
  have heG : e ∈ G.E := (hn.sub 0 (by omega)).2 he
  have hnew : ∃ e ∈ G.E, j '' e ⊆ Δ_F ∧ ¬ j '' e ⊆ E := by
    refine ⟨e, heG, ?_, fun h6 => ?_⟩
    · rintro _ ⟨y', hy', rfl⟩
      have h7 : j y' ∈ discBd (Ds 0) := by
        rw [hn.bd_eq 0 (by omega)]
        exact mem_image_of_mem j (he.2.1 hy').1
      exact hsubF ((hEn l0).2.2.1 (hn.mono (Nat.zero_le 1) (by omega)
        (Surface.discBd_subset _ h7)))
    · have h7 := h6 (mem_image_of_mem j hye)
      have h8 : j y ∉ discInt E := fun h9 => disjoint_left.mp (hn.offE 0 (by omega)) h9 hy
      have h9 : j y ∈ discBd E := by
        by_contra h10
        exact h8 ⟨h7, h10⟩
      exact (heG.2.1 hye).2 (hd.2.2.1 ⟨h9, (heG.2.1 hye).1⟩)
  have h6 := cuffCount_lt G j hE₂ (.inr hnew)
  omega

/-- **The core at one cuff.** This is the first half of the proof of (5.9), pages 234-235: `A(C)`
with its maximal choice, the circuits, the paths of (5.8), the pieces `N_i(C)`, and the paths `Q_i`.
-/
theorem exists_cuff_core (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a b c)) (habc : 3 ≤ 3 * a + 3 * b + c) (hcyl : ¬ Nonempty
    (S ≃ₜ SurfaceModel 0 0 2)) {C : Set S} (hC : C ∈ cuffs S) {j : S → T} {D : Set T}
      (hc : IsCappedCuff C T j D) (hbT : bd T = j '' (bd S \ C)) {G : Drawing S} (hG : G.IsProper)
        (hns : ¬ IsSphere T) (hbl : IsBoundaryLinked G) {v : ℕ} (hv2 : 2 ≤ v) (hev : v ≤ 2 *
          (v / 2)) (hks : 2 ≤ (G.V ∩ C).ncard) (hkv : (G.V ∩ C).ncard ≤ v)
    (hα₁ : v * (G.V ∩ C).ncard + (v / 2 + (G.V ∩ C).ncard + 2 + 3) < alpha G) (hα₂ : v *
      (G.V ∩ C).ncard + (v * (G.V ∩ C).ncard + (v / 2 + (G.V ∩ C).ncard + 2 + 3)) < alpha G)
        (hα₃ : ∀ C₁ ∈ cuffs S, C₁ ≠ C → v * (G.V ∩ C).ncard + (v / 2 + (G.V ∩ C).ncard + 2 + 3) +
          (G.V ∩ C₁).ncard < alpha G) (hα₄ : 9 * (v * (G.V ∩ C).ncard + (v / 2 +
            (G.V ∩ C).ncard + 2 + 3) + 1) ≤ 2 * alpha G) :
    ∃ (Y E₀ Δ' Do : Set T) (Nk Bo : Drawing S) (R : Fin (G.V ∩ C).ncard → Drawing S) (x t : Fin
      (G.V ∩ C).ncard → S) (Q : ∀ i, GraphWalk G.toGraph (x i) (t i)) (L : Fin (v / 2) → Drawing S)
        (El : Fin (v / 2) → Set T), IsCuffCore G C j D (v * (G.V ∩ C).ncard + (v / 2 +
          (G.V ∩ C).ncard + 2 + 3)) v Y E₀ Δ' Do Nk Bo R x t Q L El := by
  classical
  have hT := hc.isSurface
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  have : ConnectedSpace T := hc.connectedSpace hS
  have hman := hT.2.2
  have hcont := hc.isEmbedding.continuous
  have hji := hc.isEmbedding.injective
  set ks := (G.V ∩ C).ncard with hksdef
  set ra := v * ks with hra
  have hpreC : j ⁻¹' discBd D = C := by
    rw [hc.discBd_eq]
    exact preimage_image_eq C hji
  have hks1 : ks ≤ ra := by
    rw [hra]
    nlinarith
  have h₀ : IsCuffDisc G j D ra D := by
    refine ⟨hc.isClosedDisc, subset_rfl, ?_, ?_⟩
    · rw [hpreC]
      exact fun z hz => hG ⟨cuff_subset_bd hC hz.1, hz.2⟩
    · rw [hpreC]
      exact hks1
  obtain ⟨E, hd, hmax⟩ := exists_max_count G j h₀
  obtain ⟨Δ, hΔ, hA⟩ := exists_scriptA_disc hS hm habc hG hC hc hα₄
  have hEΔ : E ⊆ Δ := by
    refine disc_subset_of_bd_subset hT hns hΔ hd.1 ?_
    rw [← image_preimage_bd hc hd.2.1]
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hd.isScriptASet hS hC hc hns
    refine hA z ⟨_, ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.trans
      (Nat.le_add_right _ _)⟩, hz⟩
  set β := v / 2 + ks + 2 with hβdef
  obtain ⟨B, Ds, hn⟩ := exists_cuff_nest hS hm habc hcyl hC hc hbT hG hd hα₁ hα₂ hα₃ hΔ hEΔ hA (s
    := β + 3) le_rfl (by omega)
  obtain ⟨D₁, Δ₂, P, u, v', N, En, hD₁, hΔ₂, h1, h2, h3, h4, hg⟩ := hn.exists_grid
    hS hc hd hmax (β := β) (by omega)
  have hkβ : ks < β := by omega
  have hvk : 2 ≤ v * ks := hks.trans hks1
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ := hg.exists_groups (by omega) (by omega) hvk ⟨ks, hkβ⟩
  have hsd : ∀ {t t'}, t < t' → t' < β + 3 → Ds t ⊆ Ds t' \ discBd (Ds t') := fun htt ht
    => hn.subset_diff hman hji htt ht
  have hE0 : E ⊆ Ds 0 := hn.mem 0 (by omega)
  have hDs0 : Ds 0 ⊆ discInt (Ds 1) := hsd (by omega) (by omega)
  have hEn : ∀ l, IsClosedDisc (En l) ∧ discBd (En l) = j '' (N l).U ∧ Ds 1 ⊆ En l ∧ En l ⊆ Δ₂
    := fun l => by
    obtain ⟨-, -, c1, c2, c3, c4⟩ := hg.circuit l
    exact ⟨c1, c2, h1.trans c3, c4⟩
  have hDint : ∀ l, D ⊆ discInt (En l) := fun l => (hd.2.1.trans (hE0.trans hDs0)).trans
    (discInt_mono hman (hn.disc 1 (by omega)) (hEn l).2.2.1)
  have hoff : Disjoint Δ₂ (bd T) := (hn.off (β + 2) (by omega)).mono_left (h4.trans sdiff_subset)
  obtain ⟨x, t, Q, hQ, hQd⟩ := hg.exists_Q_walks hS hC hc hns hbl hDint hoff hkv hkβ (fun i =>
    (hR1 i).1) hR2 hR4
  have hlt : ∀ l l' : Fin β, l < l' → En l ⊆ discInt (En l') := fun l l' hll z hz => by
    refine ⟨hg.mono l l' hll.le hz, fun hb => ?_⟩
    by_cases hzi : z ∈ discBd (En l)
    · rw [(hEn l).2.1] at hzi
      rw [(hEn l').2.1] at hb
      obtain ⟨y, hy, rfl⟩ := hzi
      obtain ⟨y', hy', he⟩ := hb
      have h5 := disjoint_U_of_disjoint_V (hg.circuit l).1 (hg.circuit l').1
        (hg.circuit_disj l l' hll.ne)
      exact disjoint_left.mp h5 hy (hji he ▸ hy')
    · exact (discInt_mono hman (hEn l).1 (hg.mono l l' hll.le) ⟨hz, hzi⟩).2 hb
  have hmono : ∀ l l' : Fin β, l ≤ l' → En l ⊆ En l' := hg.mono
  set l0 : Fin β := ⟨ks, hkβ⟩ with hl0
  set l1 : Fin β := ⟨ks + 1, by omega⟩ with hl1
  set lY : Fin β := ⟨v / 2 + ks, by omega⟩ with hlY
  set lT : Fin β := ⟨v / 2 + ks + 1, by omega⟩ with hlT
  have hl01 : l0 < l1 := by simp [hl0, hl1, Fin.lt_def]
  have hint : ∀ z ∈ discBd (En l0), IsInteriorPoint z := fun z hz => by
    by_contra hb
    exact disjoint_left.mp hoff ((hEn l0).2.2.2 (Surface.discBd_subset _ hz)) hb
  obtain ⟨Δ', hΔ', hEΔ', hΔ'sub⟩ := exists_disc_around hman (hEn l0).1 hint
    ((hEn l1).1.isOpen_discInt hman) ((Surface.discBd_subset _).trans (hlt l0 l1 hl01))
  have hΔ'1 : Δ' ⊆ discInt (En l1) := hΔ'sub.trans (union_subset (hlt l0 l1 hl01) subset_rfl)
  have hΔ'l : ∀ l : Fin β, l1 ≤ l → Δ' ⊆ discInt (En l) := fun l hl => by
    rcases hl.lt_or_eq with h5 | rfl
    · exact hΔ'1.trans (sdiff_subset.trans (hlt l1 l h5))
    · exact hΔ'1
  have hl1Y : l1 ≤ lY := by
    simp only [hl1, hlY, Fin.le_def]
    omega
  have hYout : ∀ y, j y ∈ discBd Δ₂ → j y ∉ En lY := fun y hy hyY => by
    have h5 : En lY ⊆ discInt Δ₂ := fun z hz => discInt_mono hman (hEn lT).1 (hEn lT).2.2.2
      (hlt lY lT (by simp [hlY, hlT, Fin.lt_def]) hz)
    exact (h5 hyY).2 hy
  have hE0Y : En l0 ⊆ En lY := hmono _ _ (hl01.le.trans hl1Y)
  -- the ends of the paths past `N(C)`
  have hgate : ∀ i, ∀ a : Fin (v * ks), (P a).V ∩ (N l0).V ⊆ (R i).V → ∃ Γ w, IsPreconnected Γ
    ∧ Γ ⊆ (P a).U ∧ w ∈ Γ ∧ v' a ∈ Γ ∧ w ∈ (P a).V ∩ (N l0).V ∧ ∀ z ∈ Γ, z ≠ w → j z ∉ En l0
      := fun i a hsub => by
    obtain ⟨c1, c2, c3, c4, c5⟩ := hg.path a
    refine exists_gate hman (hg.circuit l0).1 c1 hcont hji (hEn l0).1 (hEn l0).2.1 c4 (fun hin
      => hYout _ c3 (hE0Y hin)) ?_
    obtain ⟨Q', x', y', -, -, hV, W, -, hWV, -⟩ := hg.inter a l0
    exact ⟨x', hV ▸ (hWV ▸ W.start_mem_support : x' ∈ Q'.V)⟩
  have hinner : ∀ F : Set S, IsOArc F → G.IsNormal F → (G.V ∩ F).ncard ≤ v → SurroundsCuff F C
    → Disjoint (j ⁻¹' discInt (En l0)) F → False := fun F hO hnF hcard hs hdj => by
    exact inner_surrounding_arc_forbidden (S := S) (T := T) hS (C := C)
      (j := j) (D := D) hc (G := G) (v := v) hman hji ks hks ra hra hks1 E hd hmax Δ β B
      Ds hn Δ₂ N En hsd hE0 hEn hDint l0 F hO hnF hcard hs hdj
  have hgates : ∀ i, ∃ (Γ : Fin v → Set S) (w y : Fin v → S), (∀ a, IsPreconnected (Γ a)
    ∧ Γ a ⊆ G.U ∧ w a ∈ Γ a ∧ y a ∈ Γ a ∧ w a ∈ (R i).V ∧ j (y a) ∉ En lY ∧ j (y a) ∈ Ds (β + 2)
      ∧ ∀ z ∈ Γ a, z ≠ w a → j z ∉ En l0 ∧ j z ∈ Ds (β + 2)) ∧ ∀ a a', a ≠ a' → Disjoint
        (G.V ∩ Γ a) (G.V ∩ Γ a') := fun i => by
    obtain ⟨f', hf', hfR⟩ := hR4 i
    choose Γ w c1 c2 c3 c4 c5 c6 using fun a => hgate i (f' a) (hfR a)
    have hin : ∀ a, ∀ z ∈ (P (f' a)).U, j z ∈ Ds (β + 2) := fun a z hz => h4 ((hg.path
      (f' a)).2.2.2.2 (mem_image_of_mem j hz)).1 |>.1
    refine ⟨Γ, w, fun a => v' (f' a), fun a => ⟨c1 a, (c2 a).trans (hg.path
      (f' a)).1.U_subset, c3 a, c4 a, hfR a (c5 a), hYout _ (hg.path (f' a)).2.2.1, hin a _ (c2 a
        (c4 a)), fun z hz hne => ⟨c6 a z hz hne, hin a z (c2 a hz)⟩⟩, fun a a' hne => ?_⟩
    rw [disjoint_left]
    rintro z ⟨hzV, hz⟩ ⟨-, hz'⟩
    have h5 := mem_V_of_subdrawing (hg.path (f' a)).1 (c2 a hz) hzV
    have h6 := mem_V_of_subdrawing (hg.path (f' a')).1 (c2 a' hz') hzV
    exact disjoint_left.mp (hg.path_disj _ _ (hf'.ne hne)) h5 h6
  have hβ2 : β + 2 < β + 3 := by omega
  have hlay : ∀ i : Fin (v / 2), ks + 1 + i.1 < β := fun i => by
    have := i.2
    omega
  exact ⟨En lY, En l0, Δ', Ds (β + 2), N l0, B (β + 2), R, x, t, Q, fun i => N ⟨ks + 1 + i.1,
    hlay i⟩, fun i => En ⟨ks + 1 + i.1, hlay i⟩,
    { nkSub := (hg.circuit l0).1
      nkCirc := (hg.circuit l0).2.1
      discE := (hEn l0).1
      bdE := (hEn l0).2.1
      DinE := hDint l0
      discΔ := hΔ'
      EΔ := hEΔ'
      discO := hn.disc _ hβ2
      boSub := hn.sub _ hβ2
      boCirc := hn.circuit _ hβ2
      bdO := hn.bd_eq _ hβ2
      ΔO := (hΔ'1.trans (sdiff_subset.trans (hEn l1).2.2.2)).trans h4
      offO := hn.off _ hβ2
      reach := fun y hy => by
        obtain ⟨X, hX, hyX, -⟩ := hn.reach _ hβ2 y hy
        exact ⟨X, hX, hyX⟩
      Rsub := fun i => (hR1 i).1
      Rpath := fun i => (hR1 i).2
      Rdis := hR2
      Rcov := hR3
      xmem := fun i => (hQ i).1
      tmem := fun i => (hQ i).2.1
      Qsimple := fun i => (hQ i).2.2.1
      Qin := fun i => (hQ i).2.2.2
      Qdis := hQd
      ks2 := hks
      kcard := rfl
      inner := hinner
      discY := (hEn lY).1
      YO := (hEn lY).2.2.2.trans (h4.trans sdiff_subset)
      ΔY := (hΔ'l lY hl1Y).trans sdiff_subset
      layerSub := fun i => (hg.circuit _).1
      layerDisc := fun i => (hEn _).1
      layerBd := fun i => (hEn _).2.1
      layerIn := fun i => hDint _
      layerY := fun i => hmono _ _ (by
        simp only [hlY, Fin.le_def]
        have := i.2
        omega)
      layerOff := fun i => disjoint_left.mpr fun z hz hz' => (hΔ'l _ (by
        simp only [hl1, Fin.le_def]
        omega) hz).2 hz'
      layerDis := fun i i' hne => hg.circuit_disj _ _ (fun he => hne (Fin.ext (by
        have := congrArg Fin.val he
        simp only at this
        omega)))
      mv := hev
      gates := hgates }⟩

end GraphMinor.GM07
