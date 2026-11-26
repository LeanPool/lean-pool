/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.PullForest
import LeanPool.GraphMinor.GM07.CutLines
import LeanPool.GraphMinor.GM07.Section46CentralLift
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.GM11.DrawingOps
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# The pullback of a graph across a cut

Page 227 uses `φ⁻¹(G)` as a graph in the disc. `exists_pullback` builds a
pullback for forests. A graph `G` may have loops, and a loop of `G` lifts to
a line or to a loop, depending on the ends. We cut each edge at an inner point
into two lines, lift them with `exists_lift_line`, and join the lifts at the
one point over the inner point. Then we glue the results.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']

/-- A line without one end is path connected. -/
private theorem isPathConnected_line_diff {L : Set S'} {u v : S'}
    (h : IsLineWithEnds L u v) : IsPathConnected (L \ {u}) := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := h.exists_arc
  have hc : Continuous fun r : ℝ => a (Set.projIcc 0 1 zero_le_one r) :=
    ha.1.comp continuous_projIcc
  have heq : (fun r : ℝ => a (Set.projIcc 0 1 zero_le_one r)) '' Ioc 0 1 = range a \ {a 0} := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨mem_range_self _, fun h => ?_⟩
      have h0 := ha.2 h
      have := congrArg Subtype.val h0
      rw [Set.projIcc_of_mem zero_le_one ⟨hr.1.le, hr.2⟩] at this
      exact hr.1.ne' this
    · rintro ⟨⟨r, rfl⟩, hr⟩
      refine ⟨r.1, ⟨lt_of_le_of_ne r.2.1 fun h => hr ?_, r.2.2⟩, ?_⟩
      · exact congrArg a (Subtype.ext h.symm)
      · simp
  rw [← heq]
  exact (convex_Ioc (0 : ℝ) 1).isPathConnected ⟨1, by norm_num, le_rfl⟩ |>.image hc

/-- The two lifted halves of an edge. -/
private theorem exists_lift_edge [CompactSpace S'] [T2Space S'] [T2Space S] {B : Set S} {φ : S' → S}
    (hφ : GM19.IsCutMap φ B) (hB : IsClosed B) {G : Drawing S} {e : Set S} (he : e ∈ G.E)
    (hAB : closure e ∩ B ⊆ G.V) (hf : (φ ⁻¹' G.V).Finite) :
    ∃ Le : Set S', (∃ D : Drawing S', D.U = Le ∧ D.V = Le ∩ φ ⁻¹' G.V) ∧ Le ⊆ φ ⁻¹' closure e ∧
      (∀ z, φ z ∈ e → z ∈ Le) ∧ IsPathConnected (φ ⁻¹' e) := by
  classical
  obtain ⟨m, hme⟩ := he.1
  have hmV : m ∉ G.V := (he.2.1 hme).2
  have hmc : m ∈ closure e := subset_closure hme
  have hmB : m ∉ B := fun h => hmV (hAB ⟨hmc, h⟩)
  have heB : ∀ z ∈ e, z ∉ B := fun z hz h => (he.2.1 hz).2 (hAB ⟨subset_closure hz, h⟩)
  obtain ⟨u, v, A₁, A₂, hA₁, hA₂, hun, hcapV, hin⟩ : ∃ (u v : S) (A₁ A₂ : Set S),
      IsLineWithEnds A₁ u m ∧ IsLineWithEnds A₂ v m ∧ A₁ ∪ A₂ = closure e ∧
      closure e ∩ G.V = {u, v} ∧ A₁ ∩ A₂ ⊆ {m} ∪ ({u} ∩ {v}) := by
    rcases G.edge_cond e he with ⟨u, v, -, hcap, hl⟩ | ⟨u, hcap, hO⟩
    · have hu : u ∈ closure e ∩ G.V := hcap ▸ mem_insert u {v}
      have hv : v ∈ closure e ∩ G.V := hcap ▸ mem_insert_of_mem u (mem_singleton v)
      obtain ⟨L₁, L₂, h₁, h₂, hU, hI⟩ := hl.split hmc (fun h => hmV (h ▸ hu.2))
        (fun h => hmV (h ▸ hv.2))
      refine ⟨u, v, L₁, L₂, h₁, h₂.symm, hU, hcap, ?_⟩
      rw [hI]
      exact subset_union_left
    · have hu : u ∈ closure e ∩ G.V := hcap ▸ mem_singleton u
      obtain ⟨A, B', hA, hB', hU, hI⟩ := hO.lines hu.1 hmc (fun h => hmV (h ▸ hu.2))
      refine ⟨u, u, A, B', hA, hB', hU, by rw [pair_eq_singleton]; exact hcap, ?_⟩
      rw [hI, inter_self, pair_comm]
      rfl
  have hA₁c : A₁ ⊆ closure e := hun ▸ subset_union_left
  have hA₂c : A₂ ⊆ closure e := hun ▸ subset_union_right
  have huv : ∀ z ∈ closure e, z ∈ B → z = u ∨ z = v := fun z hz hb => by
    have : z ∈ closure e ∩ G.V := ⟨hz, hAB ⟨hz, hb⟩⟩
    rw [hcapV] at this
    exact this
  have hvA₁ : ∀ z ∈ A₁, z = v → z ∈ A₂ → z = u := fun z hz h h₂ => by
    rcases hin ⟨hz, h₂⟩ with h' | h'
    · have hvV : v ∈ closure e ∩ G.V := hcapV ▸ mem_insert_of_mem u (mem_singleton v)
      exact (hmV ((mem_singleton_iff.mp h').symm.trans h ▸ hvV.2)).elim
    · exact h'.1
  have hA₂v : v ∈ A₂ := hA₂.left_mem
  have hA₁u : u ∈ A₁ := hA₁.left_mem
  obtain ⟨L₁, u₁, m₁, hL₁, hu₁, hm₁, him₁, hinj₁, hpre₁⟩ := exists_lift_line hφ hB hA₁
    (fun z hz => by
      rcases huv z (hA₁c hz.1) hz.2 with h | h
      · exact h
      · exact hvA₁ z hz.1 h (h ▸ hA₂v))
  obtain ⟨L₂, u₂, m₂, hL₂, hu₂, hm₂, him₂, hinj₂, hpre₂⟩ := exists_lift_line hφ hB hA₂
    (fun z hz => by
      rcases huv z (hA₂c hz.1) hz.2 with h | h
      · have := hvA₁ v (by
          have hzu : z ∈ A₁ := h ▸ hA₁u
          rcases hin ⟨hzu, hz.1⟩ with h' | h'
          · have huV : u ∈ closure e ∩ G.V := hcapV ▸ mem_insert u {v}
            exact (hmV ((mem_singleton_iff.mp h').symm.trans h ▸ huV.2)).elim
          · have : v = u := h'.2.symm.trans h'.1
            exact this ▸ hA₁u) rfl hA₂v
        exact h.trans this.symm
      · exact h)
  have hoff : ∀ {x y : S'}, φ x = m → φ y = m → x = y := fun {x y} hx hy =>
    hφ.2.2.1 (show φ x ∈ Bᶜ by rw [hx]; exact hmB) (show φ y ∈ Bᶜ by rw [hy]; exact hmB)
      (hx.trans hy.symm)
  obtain rfl : m₁ = m₂ := hoff hm₁ hm₂
  have hsub : L₁ ∪ L₂ ⊆ φ ⁻¹' closure e := by
    rintro z (hz | hz)
    · exact hA₁c (him₁ ▸ mem_image_of_mem φ hz)
    · exact hA₂c (him₂ ▸ mem_image_of_mem φ hz)
  have hcov : ∀ z, φ z ∈ e → z ∈ L₁ ∪ L₂ := by
    intro z hz
    have hzc : φ z ∈ A₁ ∪ A₂ := hun ▸ subset_closure hz
    rcases hzc with h | h
    · have : z ∈ φ ⁻¹' (A₁ ∪ B) := .inl h
      rw [hpre₁] at this
      exact .inl (this.resolve_right (heB _ hz))
    · have : z ∈ φ ⁻¹' (A₂ ∪ B) := .inl h
      rw [hpre₂] at this
      exact .inr (this.resolve_right (heB _ hz))
  have hAfin : ((L₁ ∪ L₂) ∩ φ ⁻¹' G.V).Finite := hf.subset inter_subset_right
  have hu₁V : u₁ ∈ (L₁ ∪ L₂) ∩ φ ⁻¹' G.V := ⟨.inl hL₁.left_mem, by
    change φ u₁ ∈ G.V
    rw [hu₁]
    exact (hcapV.symm.subset (mem_insert u {v})).2⟩
  have hu₂V : u₂ ∈ (L₁ ∪ L₂) ∩ φ ⁻¹' G.V := ⟨.inr hL₂.left_mem, by
    change φ u₂ ∈ G.V
    rw [hu₂]
    exact (hcapV.symm.subset (mem_insert_of_mem u (mem_singleton v))).2⟩
  have hcross : ∀ z ∈ L₁ ∩ L₂, z = m₁ ∨ (z = u₁ ∧ z = u₂) := by
    rintro z ⟨h₁, h₂⟩
    have hA : φ z ∈ A₁ ∩ A₂ := ⟨him₁ ▸ mem_image_of_mem φ h₁, him₂ ▸ mem_image_of_mem φ h₂⟩
    rcases hin hA with h | ⟨h, h'⟩
    · exact .inl (hoff h hm₁)
    · refine .inr ⟨hinj₁ h₁ hL₁.left_mem ?_, hinj₂ h₂ hL₂.left_mem ?_⟩
      · rw [hu₁]
        exact h
      · rw [hu₂]
        exact h'
  have hdraw : ∃ D : Drawing S', D.U = L₁ ∪ L₂ ∧ D.V = (L₁ ∪ L₂) ∩ φ ⁻¹' G.V := by
    by_cases heq : u₁ = u₂
    · subst heq
      have hne : u₁ ≠ m₁ := fun h => hmV (by
        have := hu₁V.2
        rw [h] at this
        rw [← hm₁]
        exact this)
      have hO : IsOArc (L₁ ∪ L₂) := oArc_of_lines hL₁ hL₂ (by
        ext z
        constructor
        · intro hz
          rcases hcross z hz with h | h
          · exact .inr h
          · exact .inl h.1
        · rintro (rfl | h)
          · exact ⟨hL₁.left_mem, hL₂.left_mem⟩
          · obtain rfl : z = m₁ := h
            exact ⟨hL₁.right_mem, hL₂.right_mem⟩)
      exact exists_drawing_on_oArc hO hAfin ⟨u₁, hu₁V⟩ inter_subset_left
    · have hL : IsLineWithEnds (L₁ ∪ L₂) u₁ u₂ := hL₁.union hL₂.symm (by
        ext z
        constructor
        · intro hz
          rcases hcross z hz with h | h
          · exact h
          · exact (heq (h.1.symm.trans h.2)).elim
        · intro h
          obtain rfl : z = m₁ := h
          exact ⟨hL₁.right_mem, hL₂.right_mem⟩)
      exact exists_drawing_on_line _ hL heq hAfin hu₁V hu₂V inter_subset_left le_rfl
  have hconn : IsPathConnected (φ ⁻¹' e) := by
    have hu₁G : φ u₁ ∈ G.V := hu₁V.2
    have hu₂G : φ u₂ ∈ G.V := hu₂V.2
    have hin' : ∀ z, φ z ∈ closure e → φ z ∉ G.V → φ z ∈ e := fun z hz hn => by
      rw [← G.closure_diff_V he]
      exact ⟨hz, hn⟩
    have hmne : ∀ x, φ x ∈ G.V → m₁ ≠ x := fun x hx h => hmV (by
      rw [← hm₁, h]
      exact hx)
    have hpart : φ ⁻¹' e = (L₁ \ {u₁}) ∪ (L₂ \ {u₂}) := by
      ext z
      constructor
      · intro hz
        have hzV : φ z ∉ G.V := (he.2.1 hz).2
        rcases hcov z hz with h | h
        · exact .inl ⟨h, fun h' => hzV (by rw [mem_singleton_iff.mp h']; exact hu₁G)⟩
        · exact .inr ⟨h, fun h' => hzV (by rw [mem_singleton_iff.mp h']; exact hu₂G)⟩
      · have hcap : ∀ {w : S}, w ∈ closure e → w ∈ G.V → w = u ∨ w = v := fun {w} h₁ h₂ => by
          have : w ∈ closure e ∩ G.V := ⟨h₁, h₂⟩
          rw [hcapV] at this
          exact this
        rintro (⟨hz, hne⟩ | ⟨hz, hne⟩)
        · have hzA : φ z ∈ A₁ := him₁ ▸ mem_image_of_mem φ hz
          refine hin' z (hA₁c hzA) fun hV => ?_
          have hu₀ : φ z = u := by
            rcases hcap (hA₁c hzA) hV with h | h
            · exact h
            · exact hvA₁ _ hzA h (h ▸ hA₂v)
          exact hne (hinj₁ hz hL₁.left_mem (hu₀.trans hu₁.symm))
        · have hzA : φ z ∈ A₂ := him₂ ▸ mem_image_of_mem φ hz
          refine hin' z (hA₂c hzA) fun hV => ?_
          have hv₀ : φ z = v := by
            rcases hcap (hA₂c hzA) hV with h | h
            · rcases hin ⟨h ▸ hA₁u, hzA⟩ with h' | h'
              · exact (hmV (mem_singleton_iff.mp h' ▸ hV)).elim
              · exact h'.2
            · exact h
          exact hne (hinj₂ hz hL₂.left_mem (hv₀.trans hu₂.symm))
    rw [hpart]
    exact (isPathConnected_line_diff hL₁).union (isPathConnected_line_diff hL₂)
      ⟨m₁, ⟨hL₁.right_mem, hmne _ hu₁G⟩, hL₂.right_mem, hmne _ hu₂G⟩
  exact ⟨L₁ ∪ L₂, hdraw, hsub, hcov, hconn⟩

/-- **The pullback of a graph.** When `U(J)` is `G`-normal, `φ⁻¹(G)` is a proper graph, and each of
its edges is the full preimage of an edge of `G`. -/
theorem exists_pullback_graph {J G : Drawing S} {φ : S' → S} (hS : IsSurface S)
    (hJ : IsCutAlongGraph J S' φ) (hG : G.IsProper) (hN : G.IsNormal J.U) :
    ∃ G' : Drawing S', IsPullbackDrawing φ G G' ∧ G'.IsProper ∧
      ∀ e' ∈ G'.E, ∃ e ∈ G.E, e' = φ ⁻¹' e := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hY := hJ.isSurface
  have : CompactSpace S' := hY.1
  have : T2Space S' := hY.2.1
  have hcut := hJ.toSet
  have hφ := hcut.isCutMap
  have hB : IsClosed (bd S ∪ J.U) := (isClosed_bd S).union J.isClosed_U
  have hUB : ∀ z ∈ G.U, z ∈ bd S ∪ J.U → z ∈ G.V := fun z hz hb => by
    rcases hb with h | h
    · exact hG ⟨h, hz⟩
    · exact hN ⟨h, hz⟩
  have hVf : (φ ⁻¹' G.V).Finite := Set.Finite.preimage' G.finite_V fun x _ => hcut.finite_fiber x
  have hedge : ∀ e : G.E, ∃ Le : Set S', (∃ D : Drawing S', D.U = Le ∧ D.V = Le ∩ φ ⁻¹' G.V) ∧
      Le ⊆ φ ⁻¹' closure e.1 ∧ (∀ z, φ z ∈ e.1 → z ∈ Le) ∧ IsPathConnected (φ ⁻¹' e.1) := fun e =>
    exists_lift_edge hφ hB e.2 (fun z hz => hUB z (G.closure_subset_U e.2 hz.1) hz.2) hVf
  choose Le hdraw hsub hcov hconn using hedge
  have key : ∀ T : Finset (Set S), (∀ e ∈ T, e ∈ G.E) →
      ∃ C : Drawing S', C.U = φ ⁻¹' G.V ∪ ⋃ e ∈ T, ⋃ he : e ∈ G.E, Le ⟨e, he⟩ ∧ C.V = φ ⁻¹' G.V
        := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨pointsDrawing hVf, by simp [pointsDrawing], rfl⟩
    | insert e T he ih =>
      intro hT
      obtain ⟨C, hCU, hCV⟩ := ih fun f hf => hT f (Finset.mem_insert_of_mem hf)
      have heE := hT e (Finset.mem_insert_self _ _)
      obtain ⟨L, hLU, hLV⟩ := hdraw ⟨e, heE⟩
      have hmeet : C.U ∩ L.U ⊆ C.V ∩ L.V := by
        rw [hCU, hCV, hLU, hLV]
        rintro x ⟨hx | hx, hxe⟩
        · exact ⟨hx, hxe, hx⟩
        · by_cases hxA : x ∈ φ ⁻¹' G.V
          · exact ⟨hxA, hxe, hxA⟩
          · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
            obtain ⟨hfE, hxf⟩ := mem_iUnion.mp hxf
            have h1 : φ x ∈ closure f := hsub ⟨f, hfE⟩ hxf
            have h2 : φ x ∈ closure e := hsub ⟨e, heE⟩ hxe
            have h1' : φ x ∈ f := G.closure_diff_V hfE ▸ (⟨h1, hxA⟩ : φ x ∈ closure f \ G.V)
            have h2' : φ x ∈ e := G.closure_diff_V heE ▸ (⟨h2, hxA⟩ : φ x ∈ closure e \ G.V)
            exact (he ((G.edge_eq_of_mem hfE heE h1' h2') ▸ hf)).elim
      refine ⟨C.glue L hmeet, ?_, ?_⟩
      · change C.U ∪ L.U = _
        rw [hCU, hLU]
        ext x
        simp only [mem_union, mem_iUnion, Finset.mem_insert, exists_prop]
        constructor
        · rintro ((hx | ⟨f, hf, hx⟩) | hx)
          · exact .inl hx
          · exact .inr ⟨f, .inr hf, hx⟩
          · exact .inr ⟨e, .inl rfl, heE, hx⟩
        · rintro (hx | ⟨f, rfl | hf, hx⟩)
          · exact .inl (.inl hx)
          · exact .inr hx.2
          · exact .inl (.inr ⟨f, hf, hx⟩)
      · change C.V ∪ L.V = _
        rw [hCV, hLV]
        exact union_eq_self_of_subset_right inter_subset_right
  obtain ⟨G', hU, hV⟩ := key G.finite_edges.toFinset fun e he => G.finite_edges.mem_toFinset.mp he
  have hUeq : G'.U = φ ⁻¹' G.U := by
    rw [hU]
    ext z
    constructor
    · rintro (h | h)
      · exact G.V_subset_U h
      · obtain ⟨e, -, hz⟩ := mem_iUnion₂.mp h
        obtain ⟨hE, hz⟩ := mem_iUnion.mp hz
        exact G.closure_subset_U hE (hsub ⟨e, hE⟩ hz)
    · intro hz
      by_cases hzV : φ z ∈ G.V
      · exact .inl hzV
      · obtain ⟨e, he, hze⟩ := exists_edge_of_mem hz hzV
        exact .inr (mem_iUnion₂.mpr ⟨e, G.finite_edges.mem_toFinset.mpr he,
          mem_iUnion.mpr ⟨he, hcov ⟨e, he⟩ z hze⟩⟩)
  have hφc := hJ.quotientMap.continuous
  have hs := hJ.quotientMap.surjective
  refine ⟨G', ⟨hUeq, hV⟩, ?_, ?_⟩
  · rintro z ⟨hzb, hzU⟩
    rw [hV]
    rw [hUeq] at hzU
    rw [← hJ.preimage_bd_union_U] at hzb
    exact hUB _ hzU hzb
  · intro e' he'
    obtain ⟨x, hx⟩ := he'.1
    have hdiff : G'.U \ G'.V = φ ⁻¹' (G.U \ G.V) := by
      rw [hUeq, hV]
      rfl
    have hx' := he'.2.1 hx
    rw [hdiff] at hx'
    obtain ⟨e, he, hxe⟩ := exists_edge_of_mem hx'.1 hx'.2
    refine ⟨e, he, Subset.antisymm ?_ ?_⟩
    · have hconn' : IsPathConnected (e ∪ φ '' e') :=
        he.2.2.1.union (he'.2.2.1.image hφc) ⟨φ x, hxe, mem_image_of_mem φ hx⟩
      have heq := he.2.2.2 _ (union_subset he.2.1 (by
        rintro _ ⟨y, hy, rfl⟩
        have := he'.2.1 hy
        rw [hdiff] at this
        exact this)) hconn' subset_union_left
      intro y hy
      change φ y ∈ e
      rw [← heq]
      exact .inr (mem_image_of_mem φ hy)
    · have hconn' : IsPathConnected (e' ∪ φ ⁻¹' e) :=
        he'.2.2.1.union (hconn ⟨e, he⟩) ⟨x, hx, hxe⟩
      have heq := he'.2.2.2 _ (union_subset he'.2.1 (by
        rw [hdiff]
        exact preimage_mono he.2.1)) hconn' subset_union_left
      intro y hy
      rw [← heq]
      exact .inr hy

end GraphMinor.GM07
