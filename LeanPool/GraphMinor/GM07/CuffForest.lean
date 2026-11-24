/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffArcWalk
public import LeanPool.GraphMinor.GM11.Separate
public import LeanPool.GraphMinor.GM11.OArcCircuit
public import LeanPool.GraphMinor.GM11.EvenCircuit
public import LeanPool.GraphMinor.GM11.Section4
public import LeanPool.GraphMinor.GM07.Matched

/-!
# From `H'` back to `H`, in (6.1)

Graph Minors VII, (6.1), page 238: "By our inductive hypothesis $H'$ is $G'$-feasible, and so $H$ is
$G$-feasible as required."

The paper moves `H` by a homotopy, so that it runs through `a₁` and `a₂`, and then restricts it to
`Σ'`. We do not move `H`. Instead we add the new vertices to `H` as isolated vertices, and we pull
back along the shift `h` of the
collar. The forest found by induction, carried by `h`, together with the path of `G` from `C` to
`a₁`, is a subdrawing of `G`. The square of the homotopy `Φ` gives the homotopy of curves. It is a
fill-in of the sentence of the paper, with the same forest.

Two facts make this short. A forest contains no `O`-arc, so its point set is flat, and so two curves
in it with the same ends are homotopic. A walk of the new forest projects to a walk of the old one,
by contracting the path.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A forest contains no `O`-arc. -/
theorem noOArc_of_forest [T2Space S] [ConnectedSpace S] {H : Drawing S}
  (hf : IsGraphForest H.toGraph) {X : Set S} (hX : IsOArc X) (hs : X ⊆ H.U) : False := by
  obtain ⟨C, ⟨u, W, hW, hpos, -, -⟩, hsub, -⟩ := exists_circuit_of_oArc hX hs
  obtain ⟨W', hsup, hed⟩ := hsub.exists_walk_up W
  have h1 : W'.IsSimpleClosed := by
    unfold GraphWalk.IsSimpleClosed
    rw [hsup, hed]
    exact hW
  have h2 := hf u W' h1
  have h3 : W'.length = W.length := by
    unfold GraphWalk.length
    rw [hed]
  omega

/-- The point set of a forest is flat. -/
theorem isFlat_U_of_forest (hS : IsSurface S) [ConnectedSpace S] {H : Drawing S}
  (hf : IsGraphForest H.toGraph) : IsFlat H.U := by
  have : T2Space S := hS.2.1
  exact isFlat_of_forall_isNullHomotopicOArc hS fun F hFZ hF => (noOArc_of_forest hf hF hFZ).elim

/-- A drawing whose point set has no `O`-arc is a forest. -/
theorem isForest_of_noOArc [T2Space S] {H : Drawing S} (h : ∀ F, IsOArc F → F ⊆ H.U
  → False) : IsGraphForest H.toGraph := by
  intro u W hW
  by_contra hne
  have hC := isCircuit_walkDrawing H hW (Nat.pos_of_ne_zero hne)
  exact h _ (IsCircuit.isOArc_U hC) (walkDrawing_isSubdrawing H W).U_subset

/-- An `O`-arc has two points. -/
theorem IsOArc.exists_ne {X : Set S} (hX : IsOArc X) (x : S) : ∃ y ∈ X, y ≠ x := by
  obtain ⟨φ⟩ := id hX
  by_contra hall
  push Not at hall
  have h3 : (φ 1).1 = (φ (Circle.exp Real.pi)).1 := by
    rw [hall _ (φ 1).2, hall _ (φ _).2]
  have h4 : (1 : Circle) = Circle.exp Real.pi := φ.injective (Subtype.ext h3)
  have h5 : ((1 : Circle) : ℂ) = (Circle.exp Real.pi : ℂ) := congrArg _ h4
  rw [Circle.coe_exp, Complex.exp_pi_mul_I, Circle.coe_one] at h5
  norm_num at h5

/-- The union of two subdrawings. -/
theorem exists_union_drawing [T1Space S] {G A B : Drawing S} (hA : A.IsSubdrawing G)
  (hB : B.IsSubdrawing G) : ∃ D : Drawing S, D.IsSubdrawing G ∧ D.V = A.V ∪ B.V ∧ D.E = A.E ∪ B.E
    ∧ D.U = A.U ∪ B.U := by
  have hE : (G.span (A.V ∪ B.V) (A.E ∪ B.E)).E = A.E ∪ B.E := by
    rw [G.span_E]
    exact inter_eq_left.mpr (union_subset hA.2 hB.2)
  have hV : (G.span (A.V ∪ B.V) (A.E ∪ B.E)).V = A.V ∪ B.V := by
    rw [G.span_V]
    apply subset_antisymm
    · rintro x (hx | hx)
      · exact hx.1
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        rcases he.1 with h | h
        · rw [← hA.closure_inter_V h] at hxe
          exact .inl hxe.2
        · rw [← hB.closure_inter_V h] at hxe
          exact .inr hxe.2
    · rintro x (hx | hx)
      · exact .inl ⟨.inl hx, hA.1 hx⟩
      · exact .inl ⟨.inr hx, hB.1 hx⟩
  refine ⟨_, Drawing.span_isSubdrawing G _ _, hV, hE, ?_⟩
  rw [Drawing.U_eq, hV, hE, A.U_eq, B.U_eq, biUnion_union]
  ext x
  simp only [mem_union]
  tauto

theorem mem_V_of_subdrawing {F G : Drawing S} (h : F.IsSubdrawing G) {x : S} (hx : x ∈ F.U)
  (hV : x ∈ G.V) : x ∈ F.V := by
  by_contra hn
  obtain ⟨e, he, hxe⟩ := F.exists_edge_of_mem hx hn
  exact (h.2 he).2.1 hxe |>.2 hV

/-- The vertices of a walk are its start and points of its edges. -/
theorem walk_support_mem {H : Drawing S} {u v : S} (W : GraphWalk H.toGraph u v) : ∀ x ∈ W.support,
  x = u ∨ ∃ e ∈ W.edges, x ∈ closure e := by
  induction W with
  | nil _ =>
    intro x hx
    simp only [GraphWalk.support, List.mem_singleton] at hx
    exact .inl hx
  | @cons a b c e hl rest ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl rfl
    · rcases ih x hx with rfl | ⟨f, hf, hxf⟩
      · have h1 : x ∈ closure e ∩ H.V := by
          rw [hl.2.2.2]
          exact mem_insert_of_mem _ rfl
        exact .inr ⟨e, List.mem_cons_self, h1.1⟩
      · exact .inr ⟨f, List.mem_cons_of_mem _ hf, hxf⟩

/-- **The square of a homotopy.** If `ψ` maps the unit square to `Σ`, then the bottom side is
homotopic to the left side, then the top side, then the right side backwards. -/
theorem homotopic_square (ψ : C(unitInterval × unitInterval, S)) : ∀ {a b a' b' : S} (_ : a = ψ
  (0, 0)) (_ : b = ψ (1, 0)) (_ : a' = ψ (0, 1)) (_ : b' = ψ (1, 1)) (p : Path a b) (l : Path a a')
    (m : Path a' b') (r : Path b b'),
    (∀ t, p t = ψ (t, 0)) → (∀ t, l t = ψ (0, t)) → (∀ t, m t = ψ (t, 1)) → (∀ t, r t = ψ (1, t))
      → p.Homotopic (l.trans (m.trans r.symm)) := by
  rintro _ _ _ _ rfl rfl rfl rfl p l m r hp hl hm hr
  let u : Path (0 : unitInterval) 1 := ⟨ContinuousMap.id _, rfl, rfl⟩
  let bottom : Path ((0, 0) : unitInterval × unitInterval) (1, 0) := u.prod (Path.refl 0)
  let top : Path ((0, 1) : unitInterval × unitInterval) (1, 1) := u.prod (Path.refl 1)
  let left : Path ((0, 0) : unitInterval × unitInterval) (0, 1) := (Path.refl 0).prod u
  let right : Path ((1, 0) : unitInterval × unitInterval) (1, 1) := (Path.refl 1).prod u
  have : SimplyConnectedSpace (unitInterval × unitInterval) := by
    have : ContractibleSpace unitInterval :=
      (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
    infer_instance
  have h := (SimplyConnectedSpace.paths_homotopic bottom (left.trans (top.trans right.symm))).map ψ
  simp only [Path.map_trans] at h
  have e1 : bottom.map ψ.continuous = p := by
    ext t
    exact (hp t).symm
  have e2 : left.map ψ.continuous = l := by
    ext t
    exact (hl t).symm
  have e3 : top.map ψ.continuous = m := by
    ext t
    exact (hm t).symm
  have e4 : right.map ψ.continuous = r := by
    ext t
    exact (hr t).symm
  have e5 : right.symm.map ψ.continuous = r.symm := by
    rw [← Path.map_symm, e4]
  rwa [e1, e2, e3, e5] at h

/-- A homotopy of paths is a homotopy of curves. -/
theorem curvesHomotopic_of_homotopic {a b : S} {p q : Path a b} (h : p.Homotopic q) (φ ψ : Curve S)
  (hφ : ∀ t, φ t = p t) (hψ : ∀ t, ψ t = q t) : CurvesHomotopic φ ψ := by
  obtain ⟨F⟩ := h
  refine ⟨F.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩, fun _ => mem_univ _, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x
    simp [hφ]
  · intro x
    simp [hψ]
  · intro y
    simp [hφ]
  · intro y
    simp [hψ]
  · intro y
    simp [hφ]
  · intro y
    simp [hψ]

private theorem union_with_attached_path_is_forest
    {S : Type u}
    [TopologicalSpace S]
    [T1Space S]
    [ConnectedSpace S]
    {h : S → S}
    {G : Drawing S}
    {x₀ : S}
    {x₁ : S}
    [T2Space S]
    (W : GraphWalk G.toGraph x₁ (h x₀))
    (hLO : ∀ (X : Set S), IsOArc X → ¬X ⊆ (walkDrawing G W).U)
    (F₀ : Drawing S)
    (F : Drawing S)
    (hFU : F.U = F₀.U ∪ (walkDrawing G W).U)
    (hF₀F : F₀.IsSubdrawing F)
    (ha₁ : h x₀ ∈ F₀.V)
    (hmeet : (walkDrawing G W).U ∩ F₀.U ⊆ {h x₀})
    (ha₁L : h x₀ ∈ (walkDrawing G W).U)
    (hF₀f : IsGraphForest F₀.toGraph) :
    IsGraphForest F.toGraph := by
  refine isForest_of_noOArc (H := F) fun X hX hsub => ?_
  have hpre : IsPreconnected (X \ {h x₀}) := by
    by_cases hm' : h x₀ ∈ X
    · obtain ⟨Cc, hCc, hCF, hCU⟩ := exists_circuit_of_oArc hX hsub
      rw [← hCU]
      exact isPreconnected_U_diff hCc (mem_V_of_subdrawing hCF (hCU ▸ hm') (hF₀F.1 ha₁))
    · rw [sdiff_singleton_eq_self hm']
      exact (isConnected_of_isOArc hX).isPreconnected
  have hcov : X \ {h x₀} ⊆ F₀.U ∪ (walkDrawing G W).U := fun z hz => hFU ▸ hsub hz.1
  by_cases hb : (X \ {h x₀} ∩ F₀.U).Nonempty ∧ (X \ {h x₀} ∩ (walkDrawing G W).U).Nonempty
  · obtain ⟨z, hz, hzA, hzB⟩ := isPreconnected_closed_iff.mp hpre _ _ F₀.isClosed_U
      (walkDrawing G W).isClosed_U hcov hb.1 hb.2
    exact hz.2 (hmeet ⟨hzB, hzA⟩)
  · have hF₀a : h x₀ ∈ F₀.U := F₀.V_subset_U ha₁
    by_cases h1 : (X \ {h x₀} ∩ F₀.U).Nonempty
    · have h2 : X \ {h x₀} ∩ (walkDrawing G W).U = ∅ := not_nonempty_iff_eq_empty.mp fun h3
        => hb ⟨h1, h3⟩
      refine noOArc_of_forest hF₀f hX fun z hz => ?_
      by_cases hza : z = h x₀
      · exact hza ▸ hF₀a
      · rcases hcov ⟨hz, hza⟩ with h3 | h3
        · exact h3
        · exact absurd ⟨⟨hz, hza⟩, h3⟩ (eq_empty_iff_forall_notMem.mp h2 z)
    · refine hLO X hX fun z hz => ?_
      by_cases hza : z = h x₀
      · exact hza ▸ ha₁L
      · rcases hcov ⟨hz, hza⟩ with h3 | h3
        · exact absurd ⟨z, ⟨hz, hza⟩, h3⟩ h1
        · exact h3

private theorem walk_steps_lift_to_shifted_forest
    {S : Type u}
    [TopologicalSpace S]
    [T1Space S]
    {h : S → S}
    {G : Drawing S}
    {x₀ : S}
    {x₁ : S}
    (H₂ : Drawing S)
    (W : GraphWalk G.toGraph x₁ (h x₀))
    (F₀ : Drawing S)
    (F : Drawing S)
    (hFE : F.E = F₀.E ∪ (walkDrawing G W).E)
    (hF₀F : F₀.IsSubdrawing F)
    (hLF : (walkDrawing G W).IsSubdrawing F)
    (hx₀H₂ : x₀ ∈ H₂.V)
    (ψ : S → S)
    (hψc : IsCarry F₀ H₂ ψ F₀.V)
    (π : S → S)
    (hπW : ∀ v ∈ W.support, π v = x₀)
    (hπ₀ : ∀ v ∈ F₀.V, π v = ψ v) :
    ∀ (e : Set S) (x y : S), F.toGraph.IsLink e x y → ∃ _ : GraphWalk H₂.toGraph (π x) (π y), True
      := by
  intro e x y hl
  have hmem : x ∈ closure e ∩ F.V ∧ y ∈ closure e ∩ F.V := by
    have h2 := hl.2.2.2
    exact ⟨h2 ▸ mem_insert _ _, h2 ▸ mem_insert_of_mem _ rfl⟩
  rcases hFE ▸ hl.1 with he | he
  · have hclU : closure e ⊆ F₀.U := F₀.closure_subset_U he
    have hx : x ∈ F₀.V := mem_V_of_subdrawing hF₀F (hclU hmem.1.1) hmem.1.2
    have hy : y ∈ F₀.V := mem_V_of_subdrawing hF₀F (hclU hmem.2.1) hmem.2.2
    have hl₀ : F₀.toGraph.IsLink e x y := (hF₀F.isLink_iff he).mpr hl
    obtain ⟨R, -⟩ := hψc.walk (.cons hl₀ (.nil hy)) hx (ψ x) (ψ y) rfl rfl
    rw [hπ₀ x hx, hπ₀ y hy]
    exact ⟨R, trivial⟩
  · have hlL := (hLF.isLink_iff he).mpr hl
    have hxs : x ∈ W.support := by
      have := hlL.2.1
      rwa [walkDrawing_V] at this
    have hys : y ∈ W.support := by
      have := hlL.2.2.1
      rwa [walkDrawing_V] at this
    rw [hπW x hxs, hπW y hys]
    exact ⟨.nil hx₀H₂, trivial⟩

private theorem conclude_shifted_forest_feasible
    {S : Type u}
    [TopologicalSpace S]
    [T1Space S]
    (hS : IsSurface S)
    [ConnectedSpace S]
    {C : Set S}
    {h : S → S}
    {Φ : ↑unitInterval × S → S}
    (hs : IsCuffShift C h Φ)
    {G : Drawing S}
    {G' : Drawing S}
    {H : Drawing S}
    (hH : IsSurfaceForest H)
    {x₀ : S}
    {x₁ : S}
    (hx₀V : x₀ ∈ G'.V ∩ bd S)
    (hHC : ∀ s ∈ H.V ∩ bd S, s ∈ C → s = x₀ ∧ x₁ = x₀)
    [T2Space S]
    [CompactSpace S]
    (H₂ : Drawing S)
    (β : S ≃ₜ S)
    (hβ : ∀ x ∈ bd S, β x = x)
    (W : GraphWalk G.toGraph x₁ (h x₀))
    (hLm : (walkDrawing G W).U ∩ h '' G'.U ⊆ {h x₀})
    (hLO : ∀ (X : Set S), IsOArc X → ¬X ⊆ (walkDrawing G W).U)
    (hWb : ∀ v ∈ W.support, v ∈ bd S → v ∈ C)
    (P : Path x₀ (h x₀))
    (Q : Path x₀ (h x₀))
    (hP : ∀ (t : ↑unitInterval), P t = Φ (t, x₀))
    (hPQ : P.Homotopic Q)
    (hQ : x₀ ∈ H.V → ∀ (t : ↑unitInterval), Q t ∈ (walkDrawing G W).U)
    (H' : Drawing S)
    (hf₁ : IsGraphForest (mapDrawingHomeo β H').toGraph)
    (hpaths : ∀ s ∈ (mapDrawingHomeo β H').V ∩ bd S, ∀ t ∈ (mapDrawingHomeo β H').V ∩ bd S, s ≠ t
      → ((∃ P₁ : GraphWalk (mapDrawingHomeo β H').toGraph s t, P₁.IsSimple) ↔
        ∃ P₂ : GraphWalk H₂.toGraph s t, P₂.IsSimple) ∧ ∀ (P₁ : GraphWalk (mapDrawingHomeo β
      H').toGraph s t) (P₂ : GraphWalk H₂.toGraph s t) (φ₁ φ₂ : Curve S), P₁.IsSimple →
      P₂.IsSimple → CurveTracesWalk (mapDrawingHomeo β H') φ₁ P₁ → CurveTracesWalk H₂ φ₂ P₂ →
      CurvesHomotopic φ₁ φ₂)
    (hbdβ : ∀ {A : Set S} {x : S}, x ∈ bd S → (x ∈ ⇑β '' A ↔ x ∈ A))
    (hsub₁ : (mapDrawingHomeo β H).IsSubdrawing (mapDrawingHomeo β H'))
    (hE₁ : (mapDrawingHomeo β H').E = (mapDrawingHomeo β H).E)
    (F₀ : Drawing S)
    (hF₀ : IsMatched H₂ F₀ h ∅)
    (hF₀U : F₀.U = h '' H₂.U)
    (F : Drawing S)
    (hFG : F.IsSubdrawing G)
    (hFV : F.V = F₀.V ∪ (walkDrawing G W).V)
    (hFE : F.E = F₀.E ∪ (walkDrawing G W).E)
    (hFU : F.U = F₀.U ∪ (walkDrawing G W).U)
    (hF₀F : F₀.IsSubdrawing F)
    (hLF : (walkDrawing G W).IsSubdrawing F)
    (hx₀H₂ : x₀ ∈ H₂.V)
    (ha₁ : h x₀ ∈ F₀.V)
    (hmeet : (walkDrawing G W).U ∩ F₀.U ⊆ {h x₀})
    (ha₁L : h x₀ ∈ (walkDrawing G W).U)
    (hFf : IsGraphForest F.toGraph)
    (hFp : F.IsProper)
    (π : S → S)
    (hx₀U : x₀ ∈ H₂.U)
    (hπW : ∀ v ∈ W.support, π v = x₀)
    (hwalk : ∀ {u v : S}, GraphWalk F.toGraph u v →
      ∃ _ : GraphWalk H₂.toGraph (π u) (π v), True)
    (hsV : ∀ s ∈ H.V ∩ bd S, s ∈ H₂.V)
    (hπs : ∀ s ∈ H.V ∩ bd S, π s = s)
    (hWF : ∃ _ : GraphWalk F.toGraph x₁ (h x₀), True)
    (hsF : ∀ s ∈ H.V ∩ bd S, ∃ _ : GraphWalk F.toGraph s (h s), True)
    (hH₁V : ∀ s ∈ H.V ∩ bd S, s ∈ (mapDrawingHomeo β H).V)
    (hH₁'V : ∀ s ∈ H.V ∩ bd S, s ∈ (mapDrawingHomeo β H').V ∩ bd S)
    (hFVb : F.V ∩ bd S = H.V ∩ bd S) :
    IsGFeasible G H := by
  classical
  have hreduce : ∀ s ∈ H.V ∩ bd S, ∀ t ∈ H.V ∩ bd S, ∀ _ : GraphWalk F.toGraph s t, ∃ P : GraphWalk
    H₂.toGraph s t, P.IsSimple := by
    intro s hs' t ht' R
    obtain ⟨R₁, -⟩ := hwalk R
    rw [hπs s hs', hπs t ht'] at R₁
    obtain ⟨P, hP', -, -⟩ := GM09.exists_isSimple_subwalk R₁
    exact ⟨P, hP'⟩
  have hdown : ∀ s ∈ H.V ∩ bd S, ∀ t, ∀ P : GraphWalk (mapDrawingHomeo β H').toGraph s t,
    P.IsSimple → ∃ P₁ : GraphWalk (mapDrawingHomeo β H).toGraph s t, P₁.IsSimple := by
    intro s hs' t P hP'
    have hsupp : ∀ x ∈ P.support, x ∈ (mapDrawingHomeo β H).V := fun x hx => by
      rcases walk_support_mem P x hx with rfl | ⟨e, he, hxe⟩
      · exact hH₁V _ hs'
      · have hee : e ∈ (mapDrawingHomeo β H).E := hE₁ ▸ mem_E_of_mem_edges P he
        exact mem_V_of_subdrawing hsub₁ ((mapDrawingHomeo β H).closure_subset_U hee hxe)
          (P.mem_vertexSet_of_mem_support hx)
    obtain ⟨P₁, h1, -⟩ := hsub₁.exists_walk_down P hsupp (fun e he => hE₁ ▸ mem_E_of_mem_edges P he)
    refine ⟨P₁, ?_⟩
    unfold GraphWalk.IsSimple
    rw [h1]
    exact hP'
  have hups : ∀ s ∈ H.V ∩ bd S, ∀ t ∈ H.V ∩ bd S, ∀ _ : GraphWalk H₂.toGraph s t, ∃ P : GraphWalk
    F.toGraph s t, P.IsSimple := by
    intro s hs' t ht' R
    obtain ⟨R₁, -⟩ := hF₀.carry.walk R ⟨hsV s hs', by simp⟩ (h s) (h t) rfl rfl
    obtain ⟨R₂, -, -⟩ := hF₀F.exists_walk_up R₁
    obtain ⟨A, -⟩ := hsF s hs'
    obtain ⟨B', -⟩ := hsF t ht'
    obtain ⟨P, hP', -, -⟩ := GM09.exists_isSimple_subwalk (A.append (R₂.append B'.reverse))
    exact ⟨P, hP'⟩
  -- the path that each boundary vertex follows, and a copy of it in `F`
  have hlift : ∀ s ∈ H.V ∩ bd S, ∃ (l l' : Path s (h s)), (∀ t, l t = Φ (t, s)) ∧ (∀ t, l' t ∈ F.U)
    ∧ l.Homotopic l' := by
    intro s hs'
    have hsFU : s ∈ F.U := F.V_subset_U (hFVb.symm ▸ hs' : s ∈ F.V ∩ bd S).1
    let l : Path s (h s) := ⟨⟨fun t => Φ (t, s), by
      have := hs.contΦ
      fun_prop⟩, by simp [hs.zero], by simp [hs.one]⟩
    have hl : ∀ t, l t = Φ (t, s) := fun _ => rfl
    by_cases hsC : s ∈ C
    · obtain ⟨h1, -⟩ := hHC s hs' hsC
      subst h1
      have hlP : l = P := by
        ext t
        exact (hP t).symm
      refine ⟨l, Q, hl, fun t => hFU ▸ .inr (hQ hs'.1 t), hlP ▸ hPQ⟩
    · have hconst : ∀ t, l t = s := fun t => (hs.fix s hs'.2 hsC).2 t
      exact ⟨l, l, hl, fun t => by rw [hconst]; exact hsFU, Path.Homotopic.refl _⟩
  have hthe : ∀ s ∈ H.V ∩ bd S, s ∈ H₂.V ∩ bd S := fun s hs' => ⟨hsV s hs', hs'.2⟩
  have hV₃ : (mapDrawingHomeo β H).V ∩ bd S = H.V ∩ bd S := by
    ext x
    exact and_congr_left fun hx => hbdβ hx
  refine ⟨F, ⟨hFp, hFf⟩, ⟨β, hβ, (hH.map_homeo β).1, hFp, (hH.map_homeo β).2, hFf,
    hV₃.trans hFVb.symm, ?_⟩, hFG⟩
  intro s hs₁ t ht₁ hne
  have hs' : s ∈ H.V ∩ bd S := hV₃ ▸ hs₁
  have ht' : t ∈ H.V ∩ bd S := hV₃ ▸ ht₁
  have hp := hpaths s (hH₁'V s hs') t (hH₁'V t ht') hne
  refine ⟨⟨fun ⟨P₁, hP₁⟩ => ?_, fun ⟨P₂, _⟩ => ?_⟩, ?_⟩
  · obtain ⟨P', hP', -⟩ := hsub₁.exists_walk_up P₁
    have hsim : P'.IsSimple := by
      unfold GraphWalk.IsSimple
      rw [hP']
      exact hP₁
    obtain ⟨R, -⟩ := hp.1.mp ⟨P', hsim⟩
    exact hups s hs' t ht' R
  · obtain ⟨R, hR⟩ := hreduce s hs' t ht' P₂
    obtain ⟨P', hP'⟩ := hp.1.mpr ⟨R, hR⟩
    exact hdown s hs' t P' hP'
  · intro P₁ P₂ φ₁ φ₂ hP₁ hP₂ ht₁' ht₂
    obtain ⟨R, hR⟩ := hreduce s hs' t ht' P₂
    obtain ⟨P', hP'⟩ := hp.1.mpr ⟨R, hR⟩
    obtain ⟨φ', hφ'⟩ := exists_curveTracesWalk P'
    obtain ⟨φ'', hφ''⟩ := exists_curveTracesWalk R
    have ha := hp.2 P' R φ' φ'' hP' hR hφ' hφ''
    have hb : CurvesHomotopic φ₁ φ' := by
      refine IsFlat.curvesHomotopic (isFlat_U_of_forest hS hf₁) ((CurveTracesWalk.range_subset P₁
        φ₁ ht₁').trans hsub₁.U_subset) (CurveTracesWalk.range_subset P' φ' hφ') ?_ ?_
      · rw [ht₁'.endpoints.1, hφ'.endpoints.1]
      · rw [ht₁'.endpoints.2, hφ'.endpoints.2]
    obtain ⟨e0, e1⟩ := hφ''.endpoints
    let p : Path s t := (⟨φ'', rfl, rfl⟩ : Path (φ'' 0) (φ'' 1)).cast e0.symm e1.symm
    have hpt : ∀ u, p u = φ'' u := fun _ => rfl
    obtain ⟨l, l', hl, hl'F, hll⟩ := hlift s hs'
    obtain ⟨r, r', hr, hr'F, hrr⟩ := hlift t ht'
    let m : Path (h s) (h t) := p.map hs.cont
    have hmt : ∀ u, m u = h (φ'' u) := fun _ => rfl
    let ψq : C(unitInterval × unitInterval, S) := ⟨fun q => Φ (q.2, p q.1), by
      have := hs.contΦ
      fun_prop⟩
    have hsq := homotopic_square ψq (a := s) (b := t) (a' := h s) (b' := h t)
      (by simp [ψq, hs.zero]) (by simp [ψq, hs.zero]) (by simp [ψq, hs.one])
        (by simp [ψq, hs.one]) p l m r
      (fun u => (hs.zero _).symm) (fun u => by rw [hl]; simp [ψq])
      (fun u => (hs.one _).symm) (fun u => by rw [hr]; simp [ψq])
    have hcomp := hsq.trans (hll.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl m) hrr.symm₂))
    let κ : Curve S := (l'.trans (m.trans r'.symm)).toContinuousMap
    have hc : CurvesHomotopic φ'' κ := curvesHomotopic_of_homotopic hcomp φ'' κ hpt (fun _ => rfl)
    have hκr : range κ ⊆ F.U := by
      change range (l'.trans (m.trans r'.symm)) ⊆ F.U
      rw [Path.trans_range, Path.trans_range, Path.symm_range]
      rintro x (⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩)
      · exact hl'F u
      · rw [hmt]
        have h1 : φ'' u ∈ H₂.U := CurveTracesWalk.range_subset R φ'' hφ'' (mem_range_self u)
        exact hF₀F.U_subset (hF₀U ▸ mem_image_of_mem h h1)
      · exact hr'F u
    have hd : CurvesHomotopic κ φ₂ := by
      refine IsFlat.curvesHomotopic (isFlat_U_of_forest hS hFf) hκr (CurveTracesWalk.range_subset
        P₂ φ₂ ht₂) ?_ ?_
      · rw [ht₂.endpoints.1]
        exact (l'.trans (m.trans r'.symm)).source
      · rw [ht₂.endpoints.2]
        exact (l'.trans (m.trans r'.symm)).target
    exact CurvesHomotopic.trans hb (CurvesHomotopic.trans ha (CurvesHomotopic.trans hc hd))

/-- **From the feasibility of `H'` to that of `H`.** Let `h` be a shift of the cuff `C`, and let
`G'` be the graph that `h` carries into `G`. Let `H'` be `H` with isolated vertices added, on the
vertices of `G'` on the boundary. A walk `W` of `G` runs from `x₁` to `a₁ = h x₀`, and it meets
the image of `G'` only at `a₁`. If `H` has a vertex on `C`, then it is `x₀`, the walk starts there,
and the path `Q` along the walk is homotopic to the path traced by `x₀`. Then a forest for `H'` in
`G'` gives a forest for `H` in `G`. -/
theorem isGFeasible_of_shift [T1Space S] (hS : IsSurface S) [ConnectedSpace S] {C : Set S} {h : S
  → S} {Φ : unitInterval × S → S} (hs : IsCuffShift C h Φ) {G G' G₁ H : Drawing S}
    (hG : G.IsProper) (hH : IsSurfaceForest H) (hVb : G.V ∩ bd S = H.V ∩ bd S)
    (hm : IsMatched G' G₁ h ∅) (hG₁ : G₁.IsSubdrawing G) {B : Set S} {hf : B.Finite} {hB : Disjoint
      B H.U} (hVb' : (addIsolated H B hf hB).V ∩ bd S = G'.V ∩ bd S)
    {x₀ a₁ x₁ : S} (hx₀ : h x₀ = a₁) (hx₀V : x₀ ∈ G'.V ∩ bd S) (W : GraphWalk G.toGraph x₁ a₁)
      (hLm : (walkDrawing G W).U ∩ h '' G'.U ⊆ {a₁}) (hLO : ∀ X, IsOArc X → ¬ X ⊆
        (walkDrawing G W).U)
    (hWb : ∀ v ∈ W.support, v ∈ bd S → v ∈ C) (hHC : ∀ s ∈ H.V ∩ bd S, s ∈ C → s = x₀ ∧ x₁ = x₀)
      (P Q : Path x₀ a₁) (hP : ∀ t, P t = Φ (t, x₀)) (hPQ : P.Homotopic Q) (hQ : x₀ ∈ H.V
        → ∀ t, Q t ∈ (walkDrawing G W).U)
    (hfe : IsGFeasible G' (addIsolated H B hf hB)) : IsGFeasible G H := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hcl := hs.isClosedEmbedding
  obtain ⟨H₂, ⟨hH₂p, hH₂f⟩, ⟨β, hβ, hhom⟩, hH₂G⟩ := hfe
  have : Nonempty S := ⟨x₀⟩
  subst hx₀
  have hI : (addIsolated H B hf hB).E = H.E := by
    change arcComponentsIn ((H.U ∪ B) \ (H.V ∪ B)) = arcComponentsIn (H.U \ H.V)
    congr 1
    ext x
    simp only [mem_sdiff, mem_union, not_or]
    constructor
    · rintro ⟨h1 | h1, h2, h3⟩
      · exact ⟨h1, h2⟩
      · exact absurd h1 h3
    · rintro ⟨h1, h2⟩
      exact ⟨.inl h1, h2, fun h3 => disjoint_left.mp hB h3 h1⟩
  set H' := addIsolated H B hf hB with hH'
  have hH'V : H'.V = H.V ∪ B := rfl
  have hH'U : H'.U = H.U ∪ B := rfl
  obtain ⟨hp₁, hp₂, hf₁, hf₂, hV₂, hpaths⟩ := hhom
  have hbdβ : ∀ {A : Set S} {x : S}, x ∈ bd S → (x ∈ β '' A ↔ x ∈ A) := fun {A x} hx => by
    constructor
    · rintro ⟨y, hy, he⟩
      have : β y = β x := he.trans (hβ x hx).symm
      rwa [← β.injective this]
    · intro h
      exact ⟨x, h, hβ x hx⟩
  have hH₂V : ∀ {x : S}, x ∈ bd S → (x ∈ H₂.V ↔ x ∈ H'.V) := fun {x} hx => by
    have h1 : x ∈ (mapDrawingHomeo β H').V ∩ bd S ↔ x ∈ H₂.V ∩ bd S := by rw [hV₂]
    constructor
    · intro h
      exact (hbdβ hx).mp (h1.mpr ⟨h, hx⟩).1
    · intro h
      exact (h1.mp ⟨(hbdβ hx).mpr h, hx⟩).1
  have hsub₁ : (mapDrawingHomeo β H).IsSubdrawing (mapDrawingHomeo β H') := by
    refine ⟨image_mono subset_union_left, ?_⟩
    rw [mapDrawingHomeo_E, mapDrawingHomeo_E, hI]
  have hE₁ : (mapDrawingHomeo β H').E = (mapDrawingHomeo β H).E := by
    rw [mapDrawingHomeo_E, mapDrawingHomeo_E, hI]
  obtain ⟨F₀, hF₀⟩ := exists_image_matched hcl H₂
  have hF₀V : F₀.V = h '' H₂.V := by
    rw [← hF₀.image_V, sdiff_empty]
  have hF₀U : F₀.U = h '' H₂.U := by
    rw [← hF₀.image_U, sdiff_empty]
  have hF₀G : F₀.IsSubdrawing G := by
    refine ⟨?_, ?_⟩
    · rw [hF₀V]
      rintro _ ⟨x, hx, rfl⟩
      refine hG₁.1 ?_
      rw [← hm.image_V, sdiff_empty]
      exact mem_image_of_mem h (hH₂G.1 hx)
    · rw [hF₀.image_E]
      rintro _ ⟨e, he, rfl⟩
      refine hG₁.2 ?_
      rw [hm.image_E]
      exact mem_image_of_mem _ (hH₂G.2 he)
  obtain ⟨F, hFG, hFV, hFE, hFU⟩ := exists_union_drawing hF₀G (walkDrawing_isSubdrawing G W)
  have hF₀F : F₀.IsSubdrawing F := ⟨hFV ▸ subset_union_left, hFE ▸ subset_union_left⟩
  have hLF : (walkDrawing G W).IsSubdrawing F := ⟨hFV ▸ subset_union_right, hFE ▸
    subset_union_right⟩
  have hx₀H₂ : x₀ ∈ H₂.V := (hH₂V hx₀V.2).mpr (by
    have : x₀ ∈ H'.V ∩ bd S := hVb' ▸ hx₀V
    exact this.1)
  have ha₁ : h x₀ ∈ F₀.V := hF₀V ▸ mem_image_of_mem h hx₀H₂
  have hmeet : (walkDrawing G W).U ∩ F₀.U ⊆ {h x₀} := fun x hx => hLm ⟨hx.1, by
    rw [hF₀U] at hx
    exact image_mono hH₂G.U_subset hx.2⟩
  have ha₁L : h x₀ ∈ (walkDrawing G W).U := (mem_walkDrawing_U G W).mpr (.inl W.end_mem_support)
  have hF₀f : IsGraphForest F₀.toGraph := hF₀.isGraphForest_iff.mp hH₂f
  have hFf : IsGraphForest F.toGraph := by
    exact union_with_attached_path_is_forest (S := S) (h := h) (G := G) (x₀ := x₀) (x₁ := x₁) W
      hLO F₀ F hFU hF₀F ha₁ hmeet ha₁L hF₀f
  have hFp : F.IsProper := fun x hx => mem_V_of_subdrawing hFG hx.2 (hG ⟨hx.1, hFG.U_subset hx.2⟩)
  obtain ⟨ψ, hψl, hψr, hψc⟩ := hF₀.exists_inverse
  let π : S → S := fun v => if v ∈ W.support then x₀ else ψ v
  have hx₀U : x₀ ∈ H₂.U := H₂.V_subset_U hx₀H₂
  have hπW : ∀ v ∈ W.support, π v = x₀ := fun v hv => ite_eq_left hv
  have hπ₀ : ∀ v ∈ F₀.V, π v = ψ v := fun v hv => by
    by_cases hvs : v ∈ W.support
    · have h1 : v = h x₀ := hmeet ⟨(mem_walkDrawing_U G W).mpr (.inl hvs), F₀.V_subset_U hv⟩
      simp only [π, ite_eq_left hvs]
      rw [h1, hψl x₀ hx₀U]
    · simp only [π, ite_eq_right hvs]
  have hstep : ∀ e x y, F.toGraph.IsLink e x y → ∃ _ : GraphWalk H₂.toGraph (π x) (π y), True := by
    exact walk_steps_lift_to_shifted_forest (S := S) (h := h) (G := G) (x₀ := x₀) (x₁ := x₁) H₂ W
      F₀ F hFE hF₀F hLF hx₀H₂ ψ hψc π hπW hπ₀
  have hwalk : ∀ {u v : S} (_ : GraphWalk F.toGraph u v), ∃ _ : GraphWalk H₂.toGraph (π u)
    (π v), True := by
    intro u v R
    induction R with
    | @nil v hv =>
      by_cases hvs : v ∈ W.support
      · rw [hπW v hvs]
        exact ⟨.nil hx₀H₂, trivial⟩
      · have hv' : v ∈ F.V := hv
        rw [hFV] at hv'
        rcases hv' with h1 | h1
        · rw [hπ₀ v h1]
          exact ⟨.nil (hψc.mem v h1).2, trivial⟩
        · rw [walkDrawing_V] at h1
          exact absurd h1 hvs
    | cons hl _ ih =>
      obtain ⟨R₁, -⟩ := hstep _ _ _ hl
      obtain ⟨R₂, -⟩ := ih
      exact ⟨R₁.append R₂, trivial⟩
  have hsV : ∀ s ∈ H.V ∩ bd S, s ∈ H₂.V := fun s hs' => (hH₂V hs'.2).mpr (.inl hs'.1)
  have hπs : ∀ s ∈ H.V ∩ bd S, π s = s := fun s hs' => by
    by_cases hsC : s ∈ C
    · obtain ⟨h1, h2⟩ := hHC s hs' hsC
      have : s ∈ W.support := by
        rw [h1.trans h2.symm]
        exact W.start_mem_support
      rw [hπW s this]
      exact h1.symm
    · have h1 : s ∉ W.support := fun hsw => hsC (hWb s hsw hs'.2)
      simp only [π, ite_eq_right h1]
      have h2 := hψl s (H₂.V_subset_U (hsV s hs'))
      rwa [(hs.fix s hs'.2 hsC).1] at h2
  have hWF : ∃ W' : GraphWalk F.toGraph x₁ (h x₀), True := by
    obtain ⟨W₁, -, -⟩ := (walkDrawing_isSubdrawing G W).exists_walk_down W (by
      rw [walkDrawing_V]
      exact fun x hx => hx) (by
      rw [walkDrawing_E]
      exact fun e he => he)
    obtain ⟨W₂, -, -⟩ := hLF.exists_walk_up W₁
    exact ⟨W₂, trivial⟩
  have hsF : ∀ s ∈ H.V ∩ bd S, ∃ _ : GraphWalk F.toGraph s (h s), True := fun s hs' => by
    by_cases hsC : s ∈ C
    · obtain ⟨h1, h2⟩ := hHC s hs' hsC
      obtain ⟨W₂, -⟩ := hWF
      have e2 : h s = h x₀ := by rw [h1]
      rw [e2, h1.trans h2.symm]
      exact ⟨W₂, trivial⟩
    · rw [(hs.fix s hs'.2 hsC).1]
      refine ⟨.nil (hF₀F.1 ?_), trivial⟩
      have := mem_image_of_mem h (hsV s hs')
      rw [(hs.fix s hs'.2 hsC).1, ← hF₀V] at this
      exact this
  have hH₁V : ∀ s ∈ H.V ∩ bd S, s ∈ (mapDrawingHomeo β H).V := fun s hs' => (hbdβ hs'.2).mpr hs'.1
  have hH₁'V : ∀ s ∈ H.V ∩ bd S, s ∈ (mapDrawingHomeo β H').V ∩ bd S := fun s hs' => ⟨hsub₁.1
    (hH₁V s hs'), hs'.2⟩
  have hFVb : F.V ∩ bd S = H.V ∩ bd S := by
    apply subset_antisymm
    · rintro x ⟨hx, hb⟩
      have : x ∈ G.V ∩ bd S := ⟨hFG.1 hx, hb⟩
      rwa [hVb] at this
    · intro s hs'
      refine ⟨?_, hs'.2⟩
      obtain ⟨R, -⟩ := hsF s hs'
      exact R.mem_vertexSet_of_mem_support R.start_mem_support
  have shift_feasible_forest : IsGFeasible G H := by
    exact conclude_shifted_forest_feasible (S := S) hS (C := C) (h := h) (Φ := Φ) hs (G := G) (G'
      := G') (H := H) hH (x₀ := x₀) (x₁ := x₁) hx₀V hHC H₂ β hβ W hLm hLO hWb P Q hP hPQ hQ H' hf₁
      hpaths hbdβ hsub₁ hE₁ F₀ hF₀ hF₀U F hFG hFV hFE hFU hF₀F hLF hx₀H₂ ha₁ hmeet ha₁L hFf hFp
      π hx₀U hπW hwalk hsV hπs hWF hsF hH₁V hH₁'V hFVb
  exact shift_feasible_forest

end GraphMinor.GM07
