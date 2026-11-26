/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialExists
public import LeanPool.GraphMinor.GM11.RadialChord

/-!
# Radial drawings with prescribed spokes

Graph Minors XI, Section 3 (page 75), says that every 2-cell drawing has a radial drawing. Graph
Minors XII, proof of (6.1) (page 258), needs more: "we may choose a radial drawing $K$ of $\Gamma$
such
that ... $D_i$ contains a vertex $v_i$ say of $K$, and $D_i$ includes edges of $K$ from $v_i$ to
every
vertex of $P_i$". This file proves the general form. We fix a point in each region and some lines,
each from the point of a region to a vertex at that region. If the lines meet only in common ends
and
no two have the same ends, then some radial drawing has these points as vertices and these lines as
edges (`exists_radial_with_spokes`).

The proof adds the lines one at a time to the drawing of the points (`exists_glue_spoke`), and then
takes a drawing with the most edges among those that satisfy (i)–(iv) and contain it
(`exists_radial_extending`), as in `exists_radial_of_bound`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : PaintingOrDrawing S}

/-- **Adding a spoke.** A line from a point `c` of `Γ'` in a region `r` to a vertex `x` of `Γ`, that
runs in `r` and misses `Γ'` except at its ends, can be added to a drawing `Γ'` that satisfies
(i)–(iv), if no edge of `Γ'` has the same ends. -/
theorem exists_glue_spoke {Γ' : Drawing S} (hpre : Γ.IsPreRadialDrawing Γ')
    {K r : Set S} {c x : S} (hr : r ∈ Γ.R) (hcr : c ∈ r) (hc : c ∈ Γ'.V) (hx : x ∈ Γ.V)
    (hK : IsLineWithEnds K c x) (hKr : K \ {c, x} ⊆ r) (hKU : Disjoint (K \ {c, x}) Γ'.U)
    (hno : ∀ f ∈ Γ'.E, closure f ∩ Γ'.V ≠ {x, c}) :
    ∃ G : Drawing S, Γ.IsPreRadialDrawing G ∧ G.V = Γ'.V ∧ G.E = Γ'.E ∪ {K \ {c, x}} ∧
      G.U = Γ'.U ∪ K := by
  have hVU : Γ.V ⊆ Γ.U := V_subset_U'
  have hrU : Disjoint r Γ.U :=
    disjoint_left.mpr fun _ hp hpU => not_mem_U_of_region hr hp hpU
  have hcnV : c ∉ Γ.V := fun h => disjoint_left.mp hrU hcr (hVU h)
  have hcx : c ≠ x := fun h => hcnV (h ▸ hx)
  have hKV := line_inter_spoke_vertices hc (hpre.2.1 hx) hK hcx hKU
  exact exists_glue_spoke_of_no_bounded_disc (R := Γ.R) hpre hcr hc hx hK hcx hKr hKU hrU hVU
    (fun f hf _ _ _ _ _ _ _ hKe hfe _ => hno f hf (hfe.trans (hKe.symm.trans hKV)))

omit [T2Space S] in
/-- **A drawing that satisfies (i)–(iv) lies in a radial drawing.** Among the drawings that satisfy
(i)–(iv) and contain `K₀`, one with the most edges is maximal. -/
theorem exists_radial_extending (hT : Γ.IsTwoCell) {N : ℕ}
    (hN : ∀ Γ' : Drawing S, Γ.IsPreRadialDrawing Γ' → Γ'.E.ncard ≤ N)
    {K₀ : Drawing S} (h₀ : Γ.IsPreRadialDrawing K₀) :
    ∃ K : Drawing S, Γ.IsRadialDrawing K ∧ K₀.IsSubdrawing K := by
  classical
  let A : Set ℕ :=
    {n | ∃ Γ' : Drawing S, Γ.IsPreRadialDrawing Γ' ∧ K₀.IsSubdrawing Γ' ∧ Γ'.E.ncard = n}
  have hAne : A.Nonempty := ⟨_, K₀, h₀, ⟨subset_rfl, subset_rfl⟩, rfl⟩
  have hbdd : BddAbove A := ⟨N, by rintro _ ⟨Γ', h, -, rfl⟩; exact hN Γ' h⟩
  obtain ⟨Γ', hpre, hsub₀, hc⟩ := Nat.sSup_mem hAne hbdd
  refine ⟨Γ', ⟨hT, hpre, ?_⟩, hsub₀⟩
  rintro Γ'' hpre' ⟨hV, hE⟩
  refine ⟨?_, ?_⟩
  · intro w hw
    by_cases hwV : w ∈ Γ.V
    · exact hpre.2.1 hwV
    obtain ⟨r, hr, hwr⟩ := hpre'.2.2.2.1 w ⟨hw, hwV⟩
    obtain ⟨w', ⟨hw'r, hw'⟩, -⟩ := hpre.2.2.1 r hr
    rw [(hpre'.2.2.1 r hr).unique ⟨hwr, hw⟩ ⟨hw'r, hV hw'⟩]
    exact hw'
  · have hle : Γ''.E.ncard ≤ Γ'.E.ncard := by
      rw [hc]
      exact le_csSup hbdd ⟨Γ'', hpre', ⟨hsub₀.1.trans hV, hsub₀.2.trans hE⟩, rfl⟩
    exact (eq_of_subset_of_ncard_le hE hle Γ''.finite_edges).ge

omit [TopologicalSpace S] [T2Space S] in
/-- Two pairs, each of a point in `P` and a point outside `P`, are equal only term by term. -/
theorem pair_eq_of_mem {P : Set S} {a b c d : S} (ha : a ∈ P) (hb : b ∉ P) (hc : c ∈ P)
    (hd : d ∉ P) (h : ({a, b} : Set S) = {c, d}) : a = c ∧ b = d := by
  have ha' : a ∈ ({c, d} : Set S) := h ▸ Or.inl rfl
  have hb' : b ∈ ({c, d} : Set S) := h ▸ Or.inr rfl
  refine ⟨ha'.resolve_right fun e => hd (e ▸ ha), hb'.resolve_left fun e => hb (e ▸ hc)⟩

variable (hub : Set S → S) (hhub : ∀ r ∈ Γ.R, hub r ∈ r)
  {ι : Type*} (ρ : ι → Set S) (x : ι → S) (L : ι → Set S) (s : Finset ι)
  (hρ : ∀ j ∈ s, ρ j ∈ Γ.R) (hx : ∀ j ∈ s, x j ∈ Γ.V)
  (hL : ∀ j ∈ s, IsLineWithEnds (L j) (hub (ρ j)) (x j))
  (hLr : ∀ j ∈ s, L j \ {x j} ⊆ ρ j)
  (hmeet : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → L j ∩ L j' ⊆ {hub (ρ j), x j})
  (hinj : ∀ j ∈ s, ∀ j' ∈ s, ρ j = ρ j' → x j = x j' → j = j')

omit [T2Space S] in
include hhub hρ hLr in
/-- A prescribed spoke meets the points and the vertices of `Γ` only at its ends. -/
theorem spoke_inter_points {j : ι} (hj : j ∈ s) :
    L j ∩ (Γ.V ∪ hub '' Γ.R) ⊆ {hub (ρ j), x j} := by
  rintro y ⟨hyL, hyV | ⟨r, hr, rfl⟩⟩
  · by_cases hyx : y = x j
    · exact Or.inr hyx
    · exact (not_mem_U_of_region (hρ j hj) (hLr j hj ⟨hyL, hyx⟩) (V_subset_U' hyV)).elim
  · by_cases hyx : hub r = x j
    · exact Or.inr hyx
    · have h1 := hLr j hj ⟨hyL, hyx⟩
      rw [region_eq_of_common hr (hρ j hj) (hhub r hr) h1]
      exact Or.inl rfl

include hhub hρ hx hL hLr hmeet hinj in
/-- **The drawing of the points and the prescribed spokes satisfies (i)–(iv).** -/
theorem exists_preRadial_spokes (hR : Γ.R.Finite) :
    ∃ K₀ : Drawing S, Γ.IsPreRadialDrawing K₀ ∧ K₀.V = Γ.V ∪ hub '' Γ.R ∧
      K₀.E = (fun j => L j \ {hub (ρ j), x j}) '' s := by
  classical
  have hA : (Γ.V ∪ hub '' Γ.R).Finite := finite_V'.union (hR.image _)
  suffices H : ∀ t : Finset ι, t ⊆ s → ∃ K₀ : Drawing S, Γ.IsPreRadialDrawing K₀ ∧
      K₀.V = Γ.V ∪ hub '' Γ.R ∧ K₀.U = (Γ.V ∪ hub '' Γ.R) ∪ ⋃ j ∈ t, L j ∧
      K₀.E = (fun j => L j \ {hub (ρ j), x j}) '' t by
    obtain ⟨K₀, h1, h2, -, h4⟩ := H s subset_rfl
    exact ⟨K₀, h1, h2, h4⟩
  intro t
  induction t using Finset.induction_on with
  | empty =>
    intro _
    have hV : (pointsDrawing hA).V = Γ.V ∪ hub '' Γ.R := rfl
    have hU : (pointsDrawing hA).U = Γ.V ∪ hub '' Γ.R := rfl
    have hE := pointsDrawing_E hA
    refine ⟨pointsDrawing hA, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, by simp [hU], by simp [hE]⟩
    · rw [hU]
      ext y
      constructor
      · rintro ⟨hyU, hy | ⟨r, hr, rfl⟩⟩
        · exact hy
        · exact absurd hyU (not_mem_U_of_region hr (hhub r hr))
      · exact fun hy => ⟨V_subset_U' hy, Or.inl hy⟩
    · rw [hV]
      exact subset_union_left
    · intro r hr
      refine ⟨hub r, ⟨hhub r hr, Or.inr ⟨r, hr, rfl⟩⟩, ?_⟩
      rintro w ⟨hwr, hw | ⟨r', hr', rfl⟩⟩
      · exact absurd (V_subset_U' hw) (not_mem_U_of_region hr hwr)
      · rw [region_eq_of_common hr hr' hwr (hhub r' hr')]
    · rintro w ⟨hw | ⟨r, hr, rfl⟩, hn⟩
      · exact absurd hw hn
      · exact ⟨r, hr, hhub r hr⟩
    · intro e he
      rw [hE] at he
      exact absurd he (notMem_empty _)
    · intro e he
      rw [hE] at he
      exact absurd he (notMem_empty _)
  | insert j₀ t hj₀ ih =>
    intro hts
    obtain ⟨K₀, hpre, hV, hU, hE⟩ := ih ((Finset.subset_insert _ _).trans hts)
    have hj₀s : j₀ ∈ s := hts (Finset.mem_insert_self _ _)
    have hts' : ∀ j ∈ t, j ∈ s := fun j hj => hts (Finset.mem_insert_of_mem hj)
    have hr := hρ j₀ hj₀s
    have hcr := hhub _ hr
    have hc : hub (ρ j₀) ∈ K₀.V := hV ▸ Or.inr ⟨_, hr, rfl⟩
    have hKr : L j₀ \ {hub (ρ j₀), x j₀} ⊆ ρ j₀ := fun y hy =>
      hLr j₀ hj₀s ⟨hy.1, fun h => hy.2 (Or.inr h)⟩
    have hKU : Disjoint (L j₀ \ {hub (ρ j₀), x j₀}) K₀.U := by
      refine disjoint_left.mpr fun y hy hyU => ?_
      rw [hU] at hyU
      rcases hyU with hyA | hyL
      · exact hy.2 (spoke_inter_points hub hhub ρ x L s hρ hLr hj₀s ⟨hy.1, hyA⟩)
      · obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hyL
        have hne : j₀ ≠ j := fun e => hj₀ (e ▸ hj)
        exact hy.2 (hmeet j₀ hj₀s j (hts' j hj) hne ⟨hy.1, hyj⟩)
    have hno : ∀ f ∈ K₀.E, closure f ∩ K₀.V ≠ {x j₀, hub (ρ j₀)} := by
      intro f hf heq
      rw [hE] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have hjs := hts' j hj
      have hcl : closure (L j \ {hub (ρ j), x j}) = L j := closure_sdiff_pair (hL j hjs)
      have hLV : L j ∩ K₀.V = {hub (ρ j), x j} := by
        rw [hV]
        refine subset_antisymm (spoke_inter_points hub hhub ρ x L s hρ hLr hjs) ?_
        obtain ⟨φ, hφ0, hφ1⟩ := hL j hjs
        rintro y (rfl | rfl)
        · exact ⟨hφ0 ▸ (φ 0).2, Or.inr ⟨_, hρ j hjs, rfl⟩⟩
        · exact ⟨hφ1 ▸ (φ 1).2, Or.inl (hx j hjs)⟩
      rw [hcl, hLV, pair_comm] at heq
      have hnot : ∀ r ∈ Γ.R, hub r ∉ Γ.V := fun r hr hv =>
        not_mem_U_of_region hr (hhub r hr) (V_subset_U' hv)
      obtain ⟨e1, e2⟩ := pair_eq_of_mem (P := Γ.V) (hx j hjs) (hnot _ (hρ j hjs)) (hx j₀ hj₀s)
        (hnot _ hr) heq
      have hρe : ρ j = ρ j₀ :=
        region_eq_of_common (hρ j hjs) hr (hhub _ (hρ j hjs)) (e2 ▸ hcr)
      exact hj₀ (hinj j hjs j₀ hj₀s hρe e1 ▸ hj)
    obtain ⟨G, hG, hGV, hGE, hGU⟩ := exists_glue_spoke hpre hr hcr hc (hx j₀ hj₀s) (hL j₀ hj₀s)
      hKr hKU hno
    refine ⟨G, hG, hGV.trans hV, ?_, ?_⟩
    · rw [hGU, hU, Finset.set_biUnion_insert]
      ext y
      simp only [mem_union]
      tauto
    · rw [hGE, hE, Finset.coe_insert, image_insert_eq, union_comm]
      rfl

/-- **A radial drawing with prescribed spokes.** Let `hub r` be a point of each region `r` of a
2-cell
drawing `Γ`, and let `L j` (`j ∈ s`) be lines, each from `hub (ρ j)` to a vertex `x j` of `Γ` and
inside the region `ρ j` but for its end `x j`. If two of the lines meet only in common ends and no
two
have the same ends, then there is a radial drawing of `Γ` with all `hub r` as vertices and all
`L j` as edges (minus their ends). -/
theorem exists_radial_with_spokes (hS : IsClosedSurface S) {Γ : Drawing S}
    (hT : (PaintingOrDrawing.drawing Γ).IsTwoCell) (hub : Set S → S)
    (hhub : ∀ r ∈ Γ.R, hub r ∈ r) {ι : Type*} (ρ : ι → Set S) (x : ι → S) (L : ι → Set S)
    (s : Finset ι) (hρ : ∀ j ∈ s, ρ j ∈ Γ.R) (hx : ∀ j ∈ s, x j ∈ Γ.V)
    (hL : ∀ j ∈ s, IsLineWithEnds (L j) (hub (ρ j)) (x j))
    (hLr : ∀ j ∈ s, L j \ {x j} ⊆ ρ j)
    (hmeet : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → L j ∩ L j' ⊆ {hub (ρ j), x j})
    (hinj : ∀ j ∈ s, ∀ j' ∈ s, ρ j = ρ j' → x j = x j' → j = j') :
    ∃ K : Drawing S, (PaintingOrDrawing.drawing Γ).IsRadialDrawing K ∧ (∀ r ∈ Γ.R, hub r ∈ K.V) ∧
      ∀ j ∈ s, L j \ {hub (ρ j), x j} ∈ K.E := by
  have : ConnectedSpace S := hT.1
  obtain ⟨K₀, hpre, hV, hE⟩ := exists_preRadial_spokes (Γ := PaintingOrDrawing.drawing Γ) hub hhub
    ρ x L s hρ hx hL hLr hmeet hinj (finite_R hS Γ)
  obtain ⟨N, hN⟩ := exists_spoke_bound_drawing hT hS
  obtain ⟨K, hK, hsub⟩ := exists_radial_extending hT hN hpre
  refine ⟨K, hK, fun r hr => hsub.1 (hV ▸ Or.inr ⟨r, hr, rfl⟩), fun j hj => hsub.2 ?_⟩
  rw [hE]
  exact ⟨j, hj, rfl⟩

end GraphMinor.GM11
