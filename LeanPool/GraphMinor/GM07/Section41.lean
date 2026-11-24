/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.DiscChain
public import LeanPool.GraphMinor.GM07.Section3
public import LeanPool.GraphMinor.GM12.Section3SubgraphDrawing
public import LeanPool.GraphMinor.GM19.Section13zc

/-!
# Graph Minors VII, (4.1)

(4.1) (page 221) is "Theorem (3.6) of [4], stated in different language". A division of the points
of `bd(Δ)` comes from the components of `H`.
We translate each side.

Suppose first that `H` is feasible, and let `F` be a normal arc. Each component of `H` that `F`
separates gives a component of the forest in `G`
which crosses `F` (`disc_crossing`), and it does so at a vertex of `G`. Different components cross
at different vertices (`card_le_of_feasible`).

Suppose next that all normal arcs satisfy the bound. A chain gives an arc (`exists_arc_of_chain`),
and the vertices of the chain pay for the
members of the division that meet the ends of the chain. So each chain has non-negative redundancy,
and (3.6) of VI gives a realization. It is a
forest in `G` with the same connections between points of `bd(Δ)` as `H`, and in a disc this is all
that homoplastic asks for (`isGFeasible_of_arcs`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM06

universe u

variable {S : Type u} [TopologicalSpace S]

private theorem exists_isDualPointSet_u (C V : Set S) : ∃ U, IsDualPointSet C V U := by
  classical
  by_cases hV : V = ∅
  · exact ⟨∅, fun _ ↦ rfl, fun h ↦ absurd hV h.ne_empty⟩
  have hne : ∀ s ∈ segmentsOf C V, s.Nonempty := fun s hs ↦ by
    obtain ⟨x, hx, rfl⟩ := hs.1
    exact ⟨x, mem_connectedComponentIn hx⟩
  have : Nonempty S := ⟨(nonempty_iff_ne_empty.mpr hV).some⟩
  choose! pt hpt using hne
  have hsub : ∀ s ∈ segmentsOf C V, s ⊆ C \ V := fun s hs ↦ by
    obtain ⟨x, hx, rfl⟩ := hs.1
    exact connectedComponentIn_subset _ _
  refine ⟨pt '' segmentsOf C V, fun h ↦ absurd h hV, fun _ ↦ ⟨?_, fun s hs ↦ ?_⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hsub s hs (hpt s hs)
  · have : pt '' segmentsOf C V ∩ s = {pt s} := by
      ext z
      constructor
      · rintro ⟨⟨s', hs', rfl⟩, hz⟩
        obtain ⟨x, hx, rfl⟩ := hs.1
        obtain ⟨x', hx', rfl⟩ := hs'.1
        have e₁ := connectedComponentIn_eq hz
        have e₂ := connectedComponentIn_eq (hpt _ hs')
        rw [mem_singleton_iff, e₁.trans e₂.symm]
      · rintro rfl
        exact ⟨mem_image_of_mem _ hs, hpt s hs⟩
    rw [this, ncard_singleton]

/-- Any two curves in a disc with the same ends are homotopic, along straight segments of the disc.
-/
theorem curvesHomotopic_of_disc (hDS : IsClosedDiscSpace S) {φ₀ φ₁ : Curve S} (h0 : φ₀ 0 = φ₁ 0)
  (h1 : φ₀ 1 = φ₁ 1) : CurvesHomotopic φ₀ φ₁ := by
  obtain ⟨e⟩ := hDS
  let a : unitInterval → EuclideanPlane := fun x => (e.symm (φ₀ x)).1
  let b : unitInterval → EuclideanPlane := fun x => (e.symm (φ₁ x)).1
  have ha : Continuous a := continuous_subtype_val.comp (e.symm.continuous.comp φ₀.continuous)
  have hb : Continuous b := continuous_subtype_val.comp (e.symm.continuous.comp φ₁.continuous)
  let f : unitInterval × unitInterval → EuclideanPlane := fun p => (1 - (p.2 : ℝ)) • a p.1 +
    (p.2 : ℝ) • b p.1
  have hf : Continuous f := by
    have h2 : Continuous fun p : unitInterval × unitInterval => (p.2 : ℝ)
      := continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.sub h2).smul (ha.comp continuous_fst)).add (h2.smul
      (hb.comp continuous_fst))
  have hmem : ∀ p, f p ∈ ClosedUnitDisc := fun p =>
    (convex_closedBall (0 : EuclideanPlane) 1) (e.symm (φ₀ p.1)).2 (e.symm (φ₁ p.1)).2
      (by linarith [p.2.2.2]) p.2.2.1 (by ring)
  let g : unitInterval × unitInterval → ClosedUnitDisc := fun p => ⟨f p, hmem p⟩
  have hg : Continuous g := Continuous.subtype_mk hf _
  have hval : ∀ x (y : unitInterval), a x = b x → f (x, y) = a x := fun x y h => by
    simp only [f, ← h]
    rw [← add_smul]
    simp
  have hend : ∀ x (y : unitInterval), φ₀ x = φ₁ x → e (g (x, y)) = φ₀ x := fun x y h => by
    have h2 : g (x, y) = e.symm (φ₀ x) := Subtype.ext (hval x y (by simp only [a, b, h]))
    rw [h2, e.apply_symm_apply]
  refine ⟨⟨fun p => e (g p), e.continuous.comp hg⟩, fun _ => mem_univ _, fun x => ?_, fun x
    => ?_, fun y => hend 0 y h0, fun y => (hend 0 y h0).trans h0, fun y => hend 1 y h1, fun y =>
      (hend 1 y h1).trans h1⟩
  · have h2 : g (x, 0) = e.symm (φ₀ x) := Subtype.ext (by simp [g, f, a])
    change e (g (x, 0)) = _
    rw [h2, e.apply_symm_apply]
  · have h2 : g (x, 1) = e.symm (φ₁ x) := Subtype.ext (by simp [g, f, b])
    change e (g (x, 1)) = _
    rw [h2, e.apply_symm_apply]

theorem isConnected_line {F : Set S} {s t : S} (h : IsLineWithEnds F s t) : IsConnected F := by
  obtain ⟨f, -, -⟩ := h
  have hF : F = (fun x => (f x).1) '' univ := by
    ext z
    simp only [image_univ, mem_range]
    exact ⟨fun hz => ⟨f.symm ⟨z, hz⟩, by simp⟩, fun ⟨x, hx⟩ => hx ▸ (f x).2⟩
  rw [hF]
  exact isConnected_univ.image _ (continuous_subtype_val.comp f.continuous).continuousOn

/-- The ends of a line do not depend on the choice of the parametrization, because only its ends
leave it connected. -/
theorem line_end_mem {F : Set S} {s t u v : S} (h1 : IsLineWithEnds F s t)
  (h2 : IsLineWithEnds F u v) : s ∈ ({u, v} : Set S) := by
  by_contra hn
  have hsu : s ≠ u := fun e => hn (.inl e)
  have hsv : s ≠ v := fun e => hn (.inr e)
  have hsF : s ∈ F := h1.left_mem
  have hc := GM11.IsLineWithEnds.isPreconnected_sdiff h1
  obtain ⟨g, hg0, hg1⟩ := h2
  let B : Set F := {z | z.1 ≠ s}
  have hBim : Subtype.val '' B = F \ {s} := by
    ext z
    simp only [mem_image, B, mem_ofPred_eq, Subtype.exists, exists_and_right, exists_eq_right,
      mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨h3, h4⟩ => ⟨h3, h4⟩, fun ⟨h3, h4⟩ => ⟨h3, h4⟩⟩
  have hB : IsPreconnected B := IsInducing.subtypeVal.isPreconnected_image.mp (hBim ▸ hc)
  have hA : IsPreconnected (g.symm '' B) := hB.image _ g.symm.continuous.continuousOn
  have h0 : (0 : unitInterval) ∈ g.symm '' B :=
    ⟨g 0, by simpa only [B, mem_ofPred_eq, hg0] using hsu.symm, by simp⟩
  have h3 : (1 : unitInterval) ∈ g.symm '' B :=
    ⟨g 1, by simpa only [B, mem_ofPred_eq, hg1] using hsv.symm, by simp⟩
  have h4 : g.symm ⟨s, hsF⟩ ∈ Icc (0 : unitInterval) 1 := ⟨bot_le, le_top⟩
  obtain ⟨z, hz, e⟩ := hA.Icc_subset h0 h3 h4
  have : z = ⟨s, hsF⟩ := g.symm.injective e
  exact hz (by rw [this])

omit [TopologicalSpace S] in
/-- A walk from a vertex of a component stays in the component. -/
theorem IsGraphComponent.mem_of_walk {G C : Graph S (Set S)} (hC : IsGraphComponent C G) {u v : S}
  (W : GraphWalk G u v) (hu : u ∈ V(C)) : v ∈ V(C) := by
  induction W with
  | nil _ => exact hu
  | cons hl _ ih => exact ih ((hC.mem_iff_of_isLink hl).mp hu)

theorem bd_inter_V_eq_of_homoplastic {H H' : Drawing S} (h : ForestsHomoplastic H H') : H.V ∩ bd S
  = H'.V ∩ bd S := by
  obtain ⟨α, hα, -, -, -, -, heqV, -⟩ := h
  rw [← heqV]
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨z, h1, hα z h2⟩, h2⟩
  · rintro ⟨⟨y, hy, rfl⟩, h2⟩
    have hb : α y ∈ bd S := h2
    have : y = α y := α.injective (hα _ hb).symm
    rw [← this]
    exact ⟨hy, this ▸ hb⟩

/-- Connections between points of `bd(Σ)` agree in homoplastic forests. -/
theorem walk_iff_of_homoplastic {H H' : Drawing S} (h : ForestsHomoplastic H H') {p q : S}
  (hp : p ∈ H.V) (hb : p ∈ bd S) (hq : q ∈ H.V) (hqb : q ∈ bd S) :
    p ∈ H'.V ∧ (Nonempty (GraphWalk H.toGraph p q) ↔ Nonempty (GraphWalk H'.toGraph p q)) := by
  classical
  obtain ⟨α, hα, -, -, -, -, heqV, hrel⟩ := h
  have hmem : ∀ z ∈ H.V, z ∈ bd S → z ∈ (mapDrawingHomeo α H).V ∩ bd S := fun z hz hzb
    => ⟨⟨z, hz, hα z hzb⟩, hzb⟩
  have hp' := hmem p hp hb
  have hq' := hmem q hq hqb
  have hpH' : p ∈ H'.V := (heqV ▸ hp' : p ∈ H'.V ∩ bd S).1
  have hqH' : q ∈ H'.V := (heqV ▸ hq' : q ∈ H'.V ∩ bd S).1
  refine ⟨hpH', ?_⟩
  by_cases hne : p = q
  · subst hne
    exact ⟨fun _ => ⟨.nil hpH'⟩, fun _ => ⟨.nil hp⟩⟩
  have hsymm : ∀ {z}, z ∈ bd S → α.symm z = z := fun {z} hz => (α.symm_apply_eq).mpr (hα z hz).symm
  constructor
  · rintro ⟨W⟩
    have W₁ := mapWalkHomeo α W
    rw [hα p hb, hα q hqb] at W₁
    obtain ⟨W₂, hs, -⟩ := GM11.GraphWalk.exists_isSimple W₁
    obtain ⟨P, -⟩ := ((hrel p hp' q hq' hne).1).mp ⟨W₂, hs⟩
    exact ⟨P⟩
  · rintro ⟨W⟩
    obtain ⟨W₂, hs, -⟩ := GM11.GraphWalk.exists_isSimple W
    obtain ⟨P, -⟩ := ((hrel p hp' q hq' hne).1).mpr ⟨W₂, hs⟩
    have W₁ := mapWalkHomeo α.symm P
    rw [mapDrawingHomeo_symm_mapDrawingHomeo, hsymm hb, hsymm hqb] at W₁
    exact ⟨W₁⟩

/-- The forward direction of (4.1): in a feasible forest, a component that `F` separates uses a
vertex of `F`, and different components use different
vertices. -/
theorem card_le_of_feasible (hDS : IsClosedDiscSpace S) {G H : Drawing S}
  (hF : IsGFeasible G H) {F : Set S} {s t : S} {C₁ C₂ : Set S}
    (hN : G.IsNormal F) (hline : IsLineWithEnds F s t) (hsb : s ∈ bd S) (htb : t ∈ bd S)
      (hst : s ≠ t) (hcomp : componentsIn (bd S \ {s, t}) = {C₁, C₂}) (hC : C₁ ≠ C₂) :
    {V₀ : Set S | ∃ H' : Drawing S, IsGraphComponent H'.toGraph H.toGraph ∧ V₀ = H'.V ∧
      (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty ∧ s ∉ V₀ ∧ t ∉ V₀}.ncard ≤
      (G.V ∩ (F \ {s, t})).ncard := by
  classical
  obtain ⟨H₂, hf2, hhom, hsub⟩ := hF
  have hsplit : ∀ C ∈ componentsIn (bd S \ {s, t}), (∀ z ∈ C, z ∈ bd S ∧ z ≠ s ∧ z ≠ t
    ∧ connectedComponentIn (bd S \ {s, t}) z = C) := by
    rintro _ ⟨z₀, -, rfl⟩ z hz
    have h1 := connectedComponentIn_subset _ _ hz
    exact ⟨h1.1, fun e => h1.2 (.inl e), fun e => h1.2 (.inr e), (connectedComponentIn_eq hz).symm⟩
  have hC₁ : C₁ ∈ componentsIn (bd S \ {s, t}) := hcomp ▸ .inl rfl
  have hC₂ : C₂ ∈ componentsIn (bd S \ {s, t}) := hcomp ▸ .inr rfl
  have hpick : ∀ V₀ ∈ {V₀ : Set S | ∃ H' : Drawing S, IsGraphComponent H'.toGraph H.toGraph ∧ V₀
    = H'.V ∧ (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty ∧ s ∉ V₀ ∧ t ∉ V₀},
      ∃ w ∈ G.V ∩ (F \ {s, t}), ∃ C : Graph S (Set S), IsGraphComponent C H₂.toGraph ∧ w ∈ V(C)
        ∧ ∃ p ∈ V₀, p ∈ bd S ∧ p ∈ V(C) := by
    rintro _ ⟨H₀, hH₀, rfl, ⟨p, hp, hpC⟩, ⟨q, hq, hqC⟩, hsV, htV⟩
    obtain ⟨hpb, hps, hpt, hpe⟩ := hsplit C₁ hC₁ p hpC
    obtain ⟨hqb, hqs, hqt, hqe⟩ := hsplit C₂ hC₂ q hqC
    have hpH : p ∈ H.V := hH₀.1.vertexSet_mono hp
    have hqH : q ∈ H.V := hH₀.1.vertexSet_mono hq
    obtain ⟨hpH₂, hiff⟩ := walk_iff_of_homoplastic hhom hpH hpb hqH hqb
    obtain ⟨W₀⟩ := hH₀.2.1.2 p hp q hq
    obtain ⟨W₂⟩ := hiff.mp ⟨W₀.mono hH₀.1⟩
    have hcc : IsGraphComponent (compOf H₂.toGraph p) H₂.toGraph := isGraphComponent_compOf hpH₂
    have hpc : p ∈ V(compOf H₂.toGraph p) := by
      change p ∈ reachSet H₂.toGraph p
      exact self_mem_reachSet hpH₂
    have hqc : q ∈ V(compOf H₂.toGraph p) := IsGraphComponent.mem_of_walk hcc W₂ hpc
    obtain ⟨W₃⟩ := hcc.2.1.2 p hpc q hqc
    obtain ⟨K, hKc, hKcon, hpK, hqK, hKsub, hKU, hKV⟩ := exists_compact_connected_of_walk H₂ hcc.1
      W₃
    have hcross : CrossesOn (bd S) s t p q := ⟨hsb, hpb, htb, hqb, hst, ?_, hps.symm, hqs.symm,
      hpt.symm, hqt.symm, ?_⟩
    · obtain ⟨w, hwF, hwK⟩ := discCrossing_of_isClosedDiscSpace hDS hline.isCompact hKc
        (isConnected_line hline) hKcon hline.left_mem hline.right_mem hpK hqK hcross
      have hwU : w ∈ G.U := hsub.U_subset (hKU hwK)
      have hwV : w ∈ G.V := hN ⟨hwF, hwU⟩
      have hwC : w ∈ V(compOf H₂.toGraph p) := by
        rcases hKsub hwK with h | h
        · exact h
        · simp only [mem_iUnion, exists_prop] at h
          obtain ⟨e, he, hwe⟩ := h
          exact ((hsub.2 (hcc.1.edgeSet_mono he)).2.1 hwe).2 hwV |>.elim
      have hnot : ∀ z ∈ bd S, z ∉ H₀.V → w = z → False := fun z hzb hzV e => by
        subst e
        have hzH : w ∈ H₂.V := hcc.1.vertexSet_mono hwC
        have hzH₁ : w ∈ H.V := (bd_inter_V_eq_of_homoplastic hhom ▸ (⟨hzH, hzb⟩ : w ∈ H₂.V ∩ bd S)
          : w ∈ H.V ∩ bd S).1
        obtain ⟨W₄⟩ := hcc.2.1.2 p hpc w hwC
        obtain ⟨-, hiff'⟩ := walk_iff_of_homoplastic hhom hpH hpb hzH₁ hzb
        obtain ⟨W₅⟩ := hiff'.mpr ⟨W₄.mono hcc.1⟩
        exact hzV (IsGraphComponent.mem_of_walk hH₀ W₅ hp)
      refine ⟨w, ⟨hwV, hwF, ?_⟩, _, hcc, hwC, p, hp, hpb, hpc⟩
      rintro (e | e)
      · exact hnot s hsb hsV e
      · exact hnot t htb htV e
    · exact fun e => hC (by rw [← hpe, ← hqe, e])
    · exact fun e => hC (by rw [← hpe, ← hqe, e])
  have hNS : Nonempty S := ⟨s⟩
  choose! f hfT C hCc hfC p hpV hpb hpC using hpick
  refine ncard_le_ncard_of_injOn f hfT ?_ (G.finite_V.subset fun z hz => hz.1)
  rintro V₀ hV₀ V₁ hV₁ e
  have hsame : C V₀ = C V₁ := (hCc V₀ hV₀).eq_of_mem_mem (hCc V₁ hV₁) (hfC V₀ hV₀) (e ▸ hfC V₁ hV₁)
  obtain ⟨H₀, hH₀, rfl, -⟩ := id hV₀
  obtain ⟨H₁, hH₁, rfl, -⟩ := id hV₁
  have hp0 := hpV _ hV₀
  have hp1 := hpV _ hV₁
  have hpH₀ : p H₀.V ∈ H.V := hH₀.1.vertexSet_mono hp0
  have hpH₁ : p H₁.V ∈ H.V := hH₁.1.vertexSet_mono hp1
  obtain ⟨W⟩ := (hCc _ hV₀).2.1.2 _ (hpC _ hV₀) _ (hsame ▸ hpC _ hV₁)
  obtain ⟨-, hiff⟩ := walk_iff_of_homoplastic hhom hpH₀ (hpb _ hV₀) hpH₁ (hpb _ hV₁)
  obtain ⟨W₂⟩ := hiff.mpr ⟨W.mono (hCc _ hV₀).1⟩
  have h1 : p H₁.V ∈ V(H₀.toGraph) := IsGraphComponent.mem_of_walk hH₀ W₂ hp0
  have h2 := hH₀.eq_of_mem_mem hH₁ h1 hp1
  exact congrArg (fun g : Graph S (Set S) => V(g)) h2

private theorem nonnegative_chain_redundancy_for_component_division
    {S : Type u}
    [TopologicalSpace S]
    (hD : IsClosedDisc (univ : Set S))
    {G : Drawing S}
    {H : Drawing S}
    (hG : G.IsProper)
    (hbd : H.V ∩ bd S = G.V ∩ bd S)
    (harc : ∀ (F : Set S) (s t : S) (C₁ C₂ : Set S), G.IsNormal F → IsProperIArc F →
      IsLineWithEnds F s t → componentsIn (bd S \ {s, t}) = {C₁, C₂} → C₁ ≠ C₂
        → {V₀ | ∃ H' : Drawing S,
      IsGraphComponent H'.toGraph H.toGraph ∧ V₀ = H'.V ∧ (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty
      ∧ s ∉ V₀ ∧ t ∉ V₀}.ncard ≤ (G.V ∩ (F \ {s, t})).ncard)
    [T2Space S]
    (hDS : IsClosedDiscSpace S) :
    let Y : Set S := H.V ∩ bd S
    (Y.Finite) →
    let C : S → Graph S (Set S) := compOf H.toGraph
    (∀ y ∈ H.V, IsGraphComponent (C y) H.toGraph) →
    (∀ y ∈ H.V, y ∈ V(C y)) →
    (∀ (y z : S), z ∈ V(C y) → z ∈ H.V) →
    let cls : S → Set S := fun y => V(C y) ∩ bd S
    let Δ : Set (Set S) := cls '' Y
    (∀ y ∈ H.V, ∀ z ∈ V(C y), C z = C y) →
    (IsDivision Δ) →
    ∀ (U : Set S),
    (∀ z ∈ U ∪ divisionUnion Δ, z ∈ bd S) →
    ∀ x ∈ U ∪ divisionUnion Δ, ∀ y ∈ U ∪ divisionUnion Δ, ∀ (A : List (ChainTerm S)), IsXYChain G
      x y A → 0 ≤ chainRedundancy G Δ x y A := by
  intro Y hYf C hCc hself hCV cls Δ hCeq hDiv U hbdpt x hx y hy A hA
  have hNS : Nonempty S := ⟨x⟩
  have hxb := hbdpt x hx
  have hyb := hbdpt y hy
  -- The ends of the chain that are vertices are terms of the chain.
  have hmem1 : ∀ z ∈ ({x, y} : Set S), z ∈ Y → Sum.inl z ∈ A := by
    have hhead : ∀ z ∈ Y, ∀ t : ChainTerm S, t ∈ A → t.MatchesEnd z → Sum.inl z ∈ A
      := fun z hz t ht hm => by
      have hzV : z ∈ G.V := (hbd ▸ hz : z ∈ G.V ∩ bd S).1
      rcases t with v | r
      · obtain rfl : v = z := hm
        exact ht
      · have hr : r ∈ G.R := hA.valid _ ht
        rcases hr with ⟨z₀, -, rfl⟩
        exact ((connectedComponentIn_subset _ _ hm).2 (G.V_subset_U hzV)).elim
    rintro z (rfl | h) hz
    · exact hhead z hz _ (List.head_mem hA.ne_nil) hA.head_matches
    · obtain rfl : z = y := h
      exact hhead z hz _ (List.getLast_mem hA.ne_nil) hA.last_matches
  let D₁ : Set (Set S) := {δ ∈ Δ | (δ ∩ {x, y}).Nonempty}
  let D₂ : Set (Set S) := {δ ∈ Δ | ¬ (δ ∩ {x, y}).Nonempty ∧ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn
    (bd S) u v x y}
  have hD₁ : D₁.ncard ≤ (({x, y} : Set S) ∩ Y).ncard := by
    have hsub : D₁ ⊆ cls '' (({x, y} : Set S) ∩ Y) := by
      rintro _ ⟨⟨y₀, hy₀, rfl⟩, z, hz, hzxy⟩
      have hzY : z ∈ Y := ⟨hCV _ _ hz.1, hz.2⟩
      refine ⟨z, ⟨hzxy, hzY⟩, ?_⟩
      simp only [cls, hCeq y₀ hy₀.1 z hz.1]
    have hfin : (({x, y} : Set S) ∩ Y).Finite := hYf.subset inter_subset_right
    exact (ncard_le_ncard hsub (hfin.image _)).trans (ncard_image_le hfin)
  -- The arc from the chain pays for `D₂`.
  obtain ⟨T, hTA, hTd, hTc⟩ : ∃ T : Set S, (∀ w ∈ T, Sum.inl w ∈ A) ∧ Disjoint T {x, y}
    ∧ D₂.ncard ≤ T.ncard := by
    by_cases hne : x = y
    · subst hne
      refine ⟨∅, by simp, by simp, ?_⟩
      have : D₂ = ∅ := eq_empty_of_forall_notMem fun δ ⟨_, _, u, _, v, _, h⟩ => h.2.2.2.2.2.1 rfl
      rw [this]
      simp
    have hbdO : IsOArc (bd S) := hDS.isOArc_bd
    obtain ⟨C₁, C₂, hcomp, hCne⟩ := exists_two_comps hbdO hxb hyb hne
    obtain ⟨F, hF, hFb, hFn, hFA⟩ := exists_arc_of_chain hD hG hA hxb hyb hne
    have hbound := harc F x y C₁ C₂ hFn ⟨x, y, hne, hFb, hF⟩ hF hcomp hCne
    refine ⟨G.V ∩ (F \ {x, y}), fun w hw => hFA w hw.2.1 hw.1 (fun e => hw.2.2 (.inl e)) (fun e
      => hw.2.2 (.inr e)), disjoint_left.mpr fun w hw h => hw.2.2 h, le_trans ?_ hbound⟩
    -- Each member of `D₂` gives a component that `F` separates.
    have hpick : ∀ δ ∈ D₂, ∃ y₀ ∈ Y, cls y₀ = δ := fun δ hδ => hδ.1
    choose! rep hrY hrc using hpick
    refine ncard_le_ncard_of_injOn (fun δ => V(C (rep δ))) ?_ ?_ ?_
    · rintro δ hδ
      obtain ⟨hδΔ, hnm, u, hu, v, hv, hcr⟩ := id hδ
      obtain ⟨Dd, hsubd, hdV, hdg⟩ := GM12.exists_subdrawing_of_subgraph H (C (rep δ)) (hCc _
        (hrY δ hδ).1).1
      have hu' : u ∈ cls (rep δ) := (hrc δ hδ).symm ▸ hu
      have hv' : v ∈ cls (rep δ) := (hrc δ hδ).symm ▸ hv
      have hcr' := hcr.comm hbdO
      have hmemb : ∀ z, z ∈ bd S → z ≠ x → z ≠ y → connectedComponentIn (bd S \ {x, y}) z ∈
        ({C₁, C₂} : Set (Set S)) ∧ z ∈ connectedComponentIn (bd S \ {x, y}) z := fun z h1 h2 h3
          => by
        have hzm : z ∈ bd S \ {x, y} := ⟨h1, by simp [h2, h3]⟩
        exact ⟨hcomp ▸ ⟨z, hzm, rfl⟩, mem_connectedComponentIn hzm⟩
      obtain ⟨h1, h2⟩ := hmemb u hcr'.2.1 hcr'.2.2.2.2.2.2.1.symm hcr'.2.2.2.2.2.2.2.2.1.symm
      obtain ⟨h3, h4⟩ := hmemb v hcr'.2.2.2.1 hcr'.2.2.2.2.2.2.2.1.symm
        hcr'.2.2.2.2.2.2.2.2.2.1.symm
      have hdiff := hcr'.2.2.2.2.2.2.2.2.2.2
      have hboth : (V(C (rep δ)) ∩ C₁).Nonempty ∧ (V(C (rep δ)) ∩ C₂).Nonempty := by
        rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3
        · exact (hdiff (h1.trans h3.symm)).elim
        · exact ⟨⟨u, hu'.1, h1 ▸ h2⟩, ⟨v, hv'.1, h3 ▸ h4⟩⟩
        · exact ⟨⟨v, hv'.1, h3 ▸ h4⟩, ⟨u, hu'.1, h1 ▸ h2⟩⟩
        · exact (hdiff (h1.trans h3.symm)).elim
      have hout : ∀ z ∈ ({x, y} : Set S), z ∈ bd S → z ∉ V(C (rep δ)) := fun z hz hzb hzV
        => hnm ⟨z, (hrc δ hδ) ▸ ⟨hzV, hzb⟩, hz⟩
      refine ⟨Dd, ?_, hdV.symm, hboth.1, hboth.2, hout x (.inl rfl) hxb, hout y (.inr rfl) hyb⟩
      rw [hdg]
      exact hCc _ (hrY δ hδ).1
    · rintro δ hδ δ' hδ' e
      have h1 : C (rep δ) = C (rep δ') := by
        have h2 := hself _ (hrY δ hδ).1
        have e' : V(C (rep δ)) = V(C (rep δ')) := e
        have h3 : rep δ ∈ V(C (rep δ')) := e' ▸ h2
        exact (hCeq _ (hrY δ' hδ').1 _ h3)
      rw [← hrc δ hδ, ← hrc δ' hδ']
      simp only [cls, h1]
    · refine (H.finite_V.finite_subsets).subset ?_
      rintro _ ⟨H₀, hH₀, rfl, -⟩
      exact hH₀.1.vertexSet_mono
  unfold chainRedundancy divisionCount
  have hcover : {δ ∈ Δ | (δ ∩ {x, y}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn
    (bd S) u v x y} ⊆ D₁ ∪ D₂ := by
    rintro δ ⟨hδ, h | h⟩
    · exact .inl ⟨hδ, h⟩
    · by_cases h2 : (δ ∩ {x, y}).Nonempty
      · exact .inl ⟨hδ, h2⟩
      · exact .inr ⟨hδ, h2, h⟩
  have hfinΔ : Δ.Finite := hDiv.1
  have hfin₁ : D₁.Finite := hfinΔ.subset fun _ h => h.1
  have hfin₂ : D₂.Finite := hfinΔ.subset fun _ h => h.1
  have h1 := ncard_le_ncard hcover (hfin₁.union hfin₂)
  have h2 := ncard_union_le D₁ D₂
  have hfinA := finite_inl_mem A
  have hT : T.Finite := hfinA.subset hTA
  have h3 : (({x, y} : Set S) ∩ Y).ncard + T.ncard ≤ {w : S | Sum.inl w ∈ A}.ncard := by
    rw [← ncard_union_eq ?_ ((by simp : ({x, y} : Set S).Finite).subset inter_subset_left) hT]
    · refine ncard_le_ncard (union_subset (fun z hz => hmem1 z hz.1 hz.2) hTA) hfinA
    · exact (hTd.symm.mono_left inter_subset_left)
  have h4 := ncard_inl_mem_le_chainLength A
  omega

/-- The backward direction of (4.1). The bound for each normal arc gives non-negative redundancy for
each chain, so VI (3.6) gives a realization, and
this realization is a forest in `G` homoplastic to `H`. -/
theorem isGFeasible_of_arcs (hS : IsSurface S) (hD : IsClosedDisc (univ : Set S)) {G H : Drawing S}
  (hG : G.IsProper) (hH : IsSurfaceForest H) (hbd : H.V ∩ bd S = G.V ∩ bd S)
    (harc : ∀ (F : Set S) (s t : S) (C₁ C₂ : Set S), G.IsNormal F → IsProperIArc F
      → IsLineWithEnds F s t → componentsIn (bd S \ {s, t}) = {C₁, C₂} → C₁ ≠ C₂ →
      {V₀ : Set S | ∃ H' : Drawing S, IsGraphComponent H'.toGraph H.toGraph ∧ V₀ = H'.V ∧
        (V₀ ∩ C₁).Nonempty ∧ (V₀ ∩ C₂).Nonempty ∧ s ∉ V₀ ∧ t ∉ V₀}.ncard ≤
        (G.V ∩ (F \ {s, t})).ncard) : IsGFeasible G H := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hDS := isClosedDiscSpace_of_univ hD
  let Y : Set S := H.V ∩ bd S
  have hYf : Y.Finite := H.finite_V.subset inter_subset_left
  let C : S → Graph S (Set S) := compOf H.toGraph
  have hCc : ∀ y ∈ H.V, IsGraphComponent (C y) H.toGraph := fun y hy => isGraphComponent_compOf hy
  have hself : ∀ y ∈ H.V, y ∈ V(C y) := fun y hy => self_mem_reachSet hy
  have hCV : ∀ y z, z ∈ V(C y) → z ∈ H.V := fun y z h => reachSet_subset _ _ h
  let cls : S → Set S := fun y => V(C y) ∩ bd S
  let Δ : Set (Set S) := cls '' Y
  have hCeq : ∀ y ∈ H.V, ∀ z, z ∈ V(C y) → C z = C y := fun y hy z hz => (hCc z
    (hCV y z hz)).eq_of_mem_mem (hCc y hy) (hself z (hCV y z hz)) hz
  have hdisj : ∀ y ∈ H.V, ∀ y' ∈ H.V, C y ≠ C y' → Disjoint V(C y) V(C y') := fun y hy y' hy' h =>
    (hCc y hy).disjoint_vertexSet_of_ne (hCc y' hy') h
  have hDiv : IsDivision Δ := by
    refine ⟨hYf.image _, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hself y hy.1, hy.2⟩
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hne
      have h1 : C y ≠ C y' := fun e => hne (by simp only [cls, e])
      exact (hdisj y hy.1 y' hy'.1 h1).mono inter_subset_left inter_subset_left
  have hUnion : divisionUnion Δ = G.V ∩ bd S := by
    rw [← hbd]
    apply subset_antisymm
    · rintro z ⟨_, ⟨y, hy, rfl⟩, hz⟩
      exact ⟨hCV y z hz.1, hz.2⟩
    · intro z hz
      exact ⟨cls z, ⟨z, hz, rfl⟩, hself z hz.1, hz.2⟩
  obtain ⟨U, hU⟩ := exists_isDualPointSet_u (bd S) (divisionUnion Δ)
  have hbdpt : ∀ z ∈ U ∪ divisionUnion Δ, z ∈ bd S := by
    rintro z (hz | hz)
    · by_cases h : divisionUnion Δ = ∅
      · rw [hU.1 h] at hz
        exact hz.elim
      · exact (hU.2 (nonempty_iff_ne_empty.mpr h)).1 hz |>.1
    · exact (hUnion ▸ hz : z ∈ G.V ∩ bd S).2
  have hcross : IsCrossFree (bd S) Δ := by
    rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨y', hy', rfl⟩, hne, a, ha, c, hc, b, hb, d, hd, hcr⟩
    have h1 : C y ≠ C y' := fun e => hne (by simp only [cls, e])
    obtain ⟨W₁⟩ := (hCc y hy.1).2.1.2 a ha.1 c hc.1
    obtain ⟨W₂⟩ := (hCc y' hy'.1).2.1.2 b hb.1 d hd.1
    obtain ⟨K₁, h1c, h1k, ha1, hc1, h1s, h1U, -⟩ := exists_compact_connected_of_walk H
      (hCc y hy.1).1 W₁
    obtain ⟨K₂, h2c, h2k, hb2, hd2, h2s, h2U, -⟩ := exists_compact_connected_of_walk H
      (hCc y' hy'.1).1 W₂
    obtain ⟨z, hz1, hz2⟩ := discCrossing_of_isClosedDiscSpace hDS h1c h2c h1k h2k ha1 hc1 hb2 hd2
      hcr
    have hE : ∀ {D : Graph S (Set S)} {e}, D ≤ H.toGraph → e ∈ E(D) → e ∈ H.E := fun hle he
      => hle.edgeSet_mono he
    rcases h1s hz1 with h3 | h3 <;> rcases h2s hz2 with h4 | h4
    · exact disjoint_left.mp (hdisj y hy.1 y' hy'.1 h1) h3 h4
    · simp only [mem_iUnion, exists_prop] at h4
      obtain ⟨e, he, hze⟩ := h4
      exact ((hE (hCc y' hy'.1).1 he).2.1 hze).2 (hCV _ _ h3)
    · simp only [mem_iUnion, exists_prop] at h3
      obtain ⟨e, he, hze⟩ := h3
      exact ((hE (hCc y hy.1).1 he).2.1 hze).2 (hCV _ _ h4)
    · simp only [mem_iUnion, exists_prop] at h3 h4
      obtain ⟨e, he, hze⟩ := h3
      obtain ⟨e', he', hze'⟩ := h4
      have heq : e = e' := H.edge_eq_of_mem (hE (hCc y hy.1).1 he) (hE
        (hCc y' hy'.1).1 he') hze hze'
      subst heq
      exact disjoint_left.mp ((hCc y hy.1).disjoint_edgeSet_of_ne (hCc y' hy'.1) h1) he he'
  have hchains : ∀ x ∈ U ∪ divisionUnion Δ, ∀ y ∈ U ∪ divisionUnion Δ, ∀ A : List
    (ChainTerm S), IsXYChain G x y A → 0 ≤ chainRedundancy G Δ x y A := by
    exact nonnegative_chain_redundancy_for_component_division (S := S) hD (G := G) (H := H) hG hbd
      harc hDS  hYf  hCc hself hCV   hCeq hDiv U hbdpt
  obtain ⟨Hg, hR⟩ := (GM06.theorem_3_6_proof G Δ U hDS hG hDiv hUnion hU).mpr ⟨hcross, hchains⟩
  obtain ⟨-, hsubV, hle, hforest, Hc, hinj, hcompHc, -⟩ := hR
  obtain ⟨K, hKs, hKV, hKg⟩ := GM12.exists_subdrawing_of_subgraph G Hg hle
  have hYK : ∀ z ∈ Y, z ∈ K.V := fun z hz => by
    rw [hKV]
    exact (hcompHc (cls z) ⟨z, hz, rfl⟩).1.1.vertexSet_mono ((hcompHc (cls z) ⟨z, hz,
      rfl⟩).2 ⟨hself z hz.1, hz.2⟩)
  have hGY : ∀ z, z ∈ G.V ∩ bd S → z ∈ Y := fun z h => by
    change z ∈ H.V ∩ bd S
    rw [hbd]
    exact h
  have hKf : IsSurfaceForest K := by
    refine ⟨fun z hz => ?_, hKg ▸ hforest⟩
    exact hYK z (hGY z ⟨hG ⟨hz.1, hKs.U_subset hz.2⟩, hz.1⟩)
  have hVeq : H.V ∩ bd S = K.V ∩ bd S := by
    apply subset_antisymm
    · exact fun z hz => ⟨hYK z hz, hz.2⟩
    · exact fun z hz => hGY z ⟨hKs.1 hz.1, hz.2⟩
  have hwalks : ∀ s ∈ Y, ∀ t ∈ Y, (Nonempty (GraphWalk H.toGraph s t) ↔ Nonempty
    (GraphWalk K.toGraph s t)) := by
    intro s hs t ht
    have hδs : cls s ∈ Δ := ⟨s, hs, rfl⟩
    have hδt : cls t ∈ Δ := ⟨t, ht, rfl⟩
    have hss : s ∈ cls s := ⟨hself s hs.1, hs.2⟩
    have htt : t ∈ cls t := ⟨hself t ht.1, ht.2⟩
    constructor
    · rintro ⟨W⟩
      have ht' : t ∈ cls s := ⟨IsGraphComponent.mem_of_walk (hCc s hs.1) W (hself s hs.1), ht.2⟩
      have h1 := hcompHc (cls s) hδs
      obtain ⟨W₁⟩ := h1.1.2.1.2 s (h1.2 hss) t (h1.2 ht')
      have W₂ := W₁.mono h1.1.1
      rw [← hKg] at W₂
      exact ⟨W₂⟩
    · rintro ⟨W⟩
      have W₂ : GraphWalk Hg s t := hKg ▸ W
      have h1 := hcompHc (cls s) hδs
      have h2 := hcompHc (cls t) hδt
      have ht1 : t ∈ V(Hc (cls s)) := IsGraphComponent.mem_of_walk h1.1 W₂ (h1.2 hss)
      have h3 := hinj hδs hδt (h1.1.eq_of_mem_mem h2.1 ht1 (h2.2 htt))
      have ht2' : t ∈ cls s := h3 ▸ htt
      obtain ⟨W₃⟩ := (hCc s hs.1).2.1.2 s (hself s hs.1) t ht2'.1
      exact ⟨W₃.mono (hCc s hs.1).1⟩
  refine ⟨K, hKf, ⟨Homeomorph.refl S, fun _ _ => rfl, ?_⟩, hKs⟩
  rw [mapDrawingHomeo_refl]
  refine ⟨hH.1, hKf.1, hH.2, hKf.2, hVeq, fun s hs t ht hne => ⟨?_,
    fun P₁ P₂ φ₁ φ₂ _ _ h₁ h₂ => ?_⟩⟩
  · constructor
    · rintro ⟨P, -⟩
      obtain ⟨W⟩ := (hwalks s hs t ht).mp ⟨P⟩
      obtain ⟨W', hW, -⟩ := GM11.GraphWalk.exists_isSimple W
      exact ⟨W', hW⟩
    · rintro ⟨P, -⟩
      obtain ⟨W⟩ := (hwalks s hs t ht).mpr ⟨P⟩
      obtain ⟨W', hW, -⟩ := GM11.GraphWalk.exists_isSimple W
      exact ⟨W', hW⟩
  · have e1 := h₁.endpoints
    have e2 := h₂.endpoints
    exact curvesHomotopic_of_disc hDS (e1.1.trans e2.1.symm) (e1.2.trans e2.2.symm)

/-- **Graph Minors VII, (4.1) (page 221).** This is Theorem (3.6) of Graph Minors VI, in the
language of normal arcs. -/
theorem discFeasibilityArcTranslation : DiscFeasibilityArcTranslationStatement.{u} := by
  intro S _ _ hS hD G H hG hH hbd
  have hDS := isClosedDiscSpace_of_univ hD
  have ht2 : T2Space S := hS.2.1
  refine ⟨fun hF F s t C₁ C₂ hN hI hL hc hne => ?_, isGFeasible_of_arcs hS hD hG hH hbd⟩
  obtain ⟨u, v, -, hb, hL'⟩ := hI
  have hub : u ∈ bd S := (hb ▸ (.inl rfl : u ∈ ({u, v} : Set S)) : u ∈ F ∩ bd S).2
  have hvb : v ∈ bd S := (hb ▸ (.inr rfl : v ∈ ({u, v} : Set S)) : v ∈ F ∩ bd S).2
  have hmem : ∀ z ∈ ({u, v} : Set S), z ∈ bd S := by
    rintro z (rfl | h)
    · exact hub
    · exact (mem_singleton_iff.mp h) ▸ hvb
  have hst : s ≠ t := fun e => by
    obtain ⟨f, h0, h1⟩ := hL
    have : f 0 = f 1 := Subtype.ext (h0.trans (e.trans h1.symm))
    exact zero_ne_one (f.injective this)
  exact card_le_of_feasible hDS hF hN hL (hmem s (line_end_mem hL hL')) (hmem t
    (line_end_mem hL.symm hL')) hst hc hne

end GraphMinor.GM07
