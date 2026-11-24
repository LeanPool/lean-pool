/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section5b
public import LeanPool.GraphMinor.GM11.ThreeCircuits
public import LeanPool.GraphMinor.Surface.Crossing

/-!
# The regions inside a circuit

For a circuit `C` of length `< 2θ`, let `A` be the set of regions of `Γ` included in `ins(C)`. The
proof of (5.4) in Graph Minors XI (pages 83–85) uses that `N(A) = C`, and that `ins(C) - U(C)` is a
region of `C` and so is connected. This file proves these facts.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Metric Complex

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The image of the open disc under coordinates on a closed disc is open: this is invariance of
domain, in a chart of the surface around each point. -/
private theorem isOpen_image_ball (hS : IsClosedSurface S) {g : ℂ → S}
    (hg : ContinuousOn g (ball 0 1)) (hinj : InjOn g (ball 0 1)) : IsOpen (g '' ball 0 1) := by
  have : T2Space S := hS.2.1
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨U, hU, hxU, ⟨f⟩⟩ := hS.2.2 (g z)
  classical
  let F : S → ℂ := fun y => if hy : y ∈ U then complexPlane.symm (f ⟨y, hy⟩).1 else 0
  have hF : ∀ y (hy : y ∈ U), F y = complexPlane.symm (f ⟨y, hy⟩).1 := fun y hy => by
    simp only [F, hy, dite_true]
  have hFc : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : U.domRestrict F = fun y : U => complexPlane.symm (f y).1 := by
      ext y
      exact hF y.1 y.2
    rw [this]
    exact complexPlane.symm.continuous.comp (continuous_subtype_val.comp f.continuous)
  have hFi : InjOn F U := by
    intro a ha b hb hab
    rw [hF a ha, hF b hb] at hab
    have h₁ := complexPlane.symm.injective hab
    have h₂ := f.injective (Subtype.ext h₁)
    exact congrArg Subtype.val h₂
  let B : Set ℂ := ball 0 1 ∩ g ⁻¹' U
  have hBo : IsOpen B := hg.isOpen_inter_preimage isOpen_ball hU
  have hzB : z ∈ B := ⟨hz, hxU⟩
  have hGc : ContinuousOn (F ∘ g) B :=
    hFc.comp (hg.mono inter_subset_left) fun w hw => hw.2
  have hGi : InjOn (F ∘ g) B := fun a ha b hb hab =>
    hinj ha.1 hb.1 (hFi ha.2 hb.2 hab)
  have hOpen := isOpen_image_of_injOn hBo hGc hGi
  have hO' : IsOpen (U ∩ F ⁻¹' ((F ∘ g) '' B)) := hFc.isOpen_inter_preimage hU hOpen
  refine Filter.mem_of_superset (hO'.mem_nhds ⟨hxU, z, hzB, rfl⟩) ?_
  rintro y ⟨hyU, w, hw, hwy⟩
  exact ⟨w, hw.1, hFi hw.2 hyU hwy⟩

/-- The interior of a closed disc in a closed surface is connected. -/
theorem IsClosedDisc.isPreconnected_diff_frontier (hS : IsClosedSurface S) {D : Set S}
    (hD : IsClosedDisc D) : IsPreconnected (D \ frontier D) := by
  obtain ⟨h, g, -, hg, hhD, hgD, hl, hr, -⟩ := IsClosedDisc.exists_chart hD
  have hgb : ContinuousOn g (ball 0 1) := hg.mono ball_subset_closedBall
  have hinj : InjOn g (ball 0 1) := by
    intro a ha b hb hab
    have ha' := hr (ball_subset_closedBall ha)
    have hb' := hr (ball_subset_closedBall hb)
    rw [← ha', ← hb']
    exact congrArg h hab
  have hO := isOpen_image_ball hS hgb hinj
  have hsub : g '' ball 0 1 ⊆ D := by
    rintro _ ⟨z, hz, rfl⟩
    exact hgD (ball_subset_closedBall hz)
  have hpre : IsPreconnected (g '' ball 0 1) :=
    (convex_ball (0 : ℂ) 1).isPreconnected.image g hgb
  refine hpre.subset_closure ?_ ?_
  · intro y hy
    refine ⟨hsub hy, fun hfr => hfr.2 ?_⟩
    exact interior_maximal hsub hO hy
  · rintro y ⟨hy, -⟩
    have hz := hhD hy
    have hzc : h y ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) one_ne_zero]
      exact hz
    have hwithin : ContinuousWithinAt g (ball 0 1) (h y) :=
      (hg (h y) hz).mono ball_subset_closedBall
    have := hwithin.mem_closure_image hzc
    rwa [hl hy] at this

/-- A connected set that misses the frontier of a closed set lies in it or misses it. -/
theorem subset_or_disjoint_of_frontier {X A : Set S} (hX : IsClosed X) (hA : IsPreconnected A)
    (hdis : Disjoint A (frontier X)) : A ⊆ X ∨ Disjoint A X := by
  have hcov : A ⊆ interior X ∪ Xᶜ := by
    intro y hy
    by_cases hyX : y ∈ X
    · refine Or.inl ?_
      by_contra hi
      exact disjoint_left.mp hdis hy ⟨subset_closure hyX, hi⟩
    · exact Or.inr hyX
  by_cases hm : (A ∩ X).Nonempty
  · left
    obtain ⟨x, hxA, hxX⟩ := hm
    have hxi : x ∈ interior X := (hcov hxA).resolve_right fun h => h hxX
    intro y hy
    by_contra hyX
    obtain ⟨z, -, hz₁, hz₂⟩ := hA _ _ isOpen_interior hX.isOpen_compl hcov ⟨x, hxA, hxi⟩ ⟨y, hy,
      hyX⟩
    exact hz₂ (interior_subset hz₁)
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hm))

variable {Γ : Drawing S} {k : ℕ} {ins : Drawing S → Set S}

/-- The set `A` of regions of `Γ` included in `ins(C)`. -/
def insideRegions (Γ : Drawing S) (X : Set S) : Set (Set S) := {r | r ∈ Γ.R ∧ r ⊆ X}

/-- A vertex of a circuit lies on an edge of it. -/
theorem exists_edge_at_vertex {C : Drawing S} (hC : C.IsCircuit) {v : S} (hv : v ∈ C.V) :
    ∃ g ∈ C.E, v ∈ closure g := by
  obtain ⟨X, -, hpos, -, hE⟩ := exists_walk_at hC hv
  cases X with
  | nil _ => simp at hpos
  | @cons a y a' g hg t =>
    have hgC : g ∈ C.E := by rw [hE]; exact List.mem_cons_self
    have hm : v ∈ closure g ∩ C.V := by rw [hg.2.2.2]; simp
    exact ⟨g, hgC, hm.1⟩

/-- A circuit whose edges are edges of a subdrawing is a subdrawing of it. -/
theorem circuit_isSubdrawing_of_E {C N : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing Γ) (hNs : N.IsSubdrawing Γ) (hE : C.E ⊆ N.E) : C.IsSubdrawing N := by
  refine ⟨fun v hv => ?_, hE⟩
  obtain ⟨g, hg, hvg⟩ := exists_edge_at_vertex hC hv
  have hm : v ∈ closure g ∩ C.V := ⟨hvg, hv⟩
  rw [hCs.closure_inter_V hg, ← hNs.closure_inter_V (hE hg)] at hm
  exact hm.2

/-- An edge outside a subdrawing misses its point set. -/
theorem edge_disjoint_U {C : Drawing S} (hCs : C.IsSubdrawing Γ) {f : Set S}
    (hf : f ∈ Γ.E) (hfC : f ∉ C.E) : Disjoint f C.U := by
  refine disjoint_left.mpr fun y hy hyU => hfC ?_
  have hyV : y ∉ C.V := fun h => (hf.2.1 hy).2 (hCs.1 h)
  obtain ⟨g, hg, hyg⟩ := C.exists_edge_of_mem hyU hyV
  rw [Γ.edge_eq_of_mem hf (hCs.2 hg) hy hyg]
  exact hg

section Disc

variable [T2Space S] (hS : IsClosedSurface S) (hs : IsSlope Γ k ins) {C : Drawing S}
  (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ) (hl : C.length < k)
include hS hs hC hCs hl

/-- The interior `ins(C) - U(C)` is connected. -/
theorem isPreconnected_inner : IsPreconnected (ins C \ C.U) := by
  obtain ⟨-, hfr, -⟩ := ins_facts_of_length hs hC hCs hl
  have := IsClosedDisc.isPreconnected_diff_frontier hS (hs.isClosedDisc C hC hCs hl)
  rwa [hfr] at this

/-- If `ins(C) - U(C)` is not empty, it is a region of `C`. -/
theorem inner_mem_R {x : S} (hx : x ∈ ins C) (hxU : x ∉ C.U) :
    ins C \ C.U ∈ C.R := by
  have hs' := theorem_4_2_proof hs hCs
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
  have hsub : r ⊆ ins C :=
    (region_subset_or_disjoint hs' hC (Drawing.IsSubdrawing.refl C) hl hr).resolve_right
      fun h => disjoint_left.mp h hxr hx
  have heq : ins C \ C.U = r := by
    refine subset_antisymm ?_ fun y hy => ⟨hsub hy, fun hyU => region_subset hr hy hyU⟩
    exact subset_region hr (isPreconnected_inner hS hs hC hCs hl) disjoint_sdiff_left ⟨hx, hxU⟩ hxr
  rw [heq]
  exact hr

omit hS in
/-- A region with a point of the interior of `ins(C)` in its closure lies in `ins(C)`. -/
theorem region_subset_ins_of_closure {r : Set S} (hr : r ∈ Γ.R) {p : S} (hp : p ∈ closure r)
    (hpi : p ∈ ins C) (hpU : p ∉ C.U) : r ⊆ ins C := by
  obtain ⟨-, hfr, -⟩ := ins_facts_of_length hs hC hCs hl
  have hint : p ∈ interior (ins C) := by
    by_contra h
    apply hpU
    rw [← hfr]
    exact ⟨subset_closure hpi, h⟩
  obtain ⟨z, hz, hzr⟩ := mem_closure_iff.mp hp _ isOpen_interior hint
  exact (region_subset_or_disjoint hs hC hCs hl hr).resolve_right fun h =>
    disjoint_left.mp h hzr (interior_subset hz)

/-- `N(A) = C` for the set `A` of regions of `Γ` in `ins(C)` (Graph Minors XI, proof of (5.4), page
84: "`N(A) = C₁`"). -/
theorem boundaryDrawing_inside :
    boundaryDrawing Γ (insideRegions Γ (ins C)) = C := by
  obtain ⟨hcl, hfr, -⟩ := ins_facts_of_length hs hC hCs hl
  refine Drawing.ext_of_V_E ?_ ?_
  · ext v
    rw [mem_boundaryDrawing_V hS]
    constructor
    · rintro ⟨⟨a, ⟨ha, hai⟩, hva⟩, b, ⟨hb, hbn⟩, hvb⟩
      by_contra hvC
      have hvU : v ∉ C.U := by
        intro hvU
        obtain ⟨g, hg, hvg⟩ := C.exists_edge_of_mem hvU hvC
        exact ((hCs.2 hg).2.1 hvg).2 hva.1
      have hvi : v ∈ ins C := hcl.closure_subset_iff.mpr hai hva.2.2
      exact hbn ⟨hb, region_subset_ins_of_closure hs hC hCs hl hb hvb.2.2 hvi hvU⟩
    · intro hv
      obtain ⟨g, hg, hvg⟩ := exists_edge_at_vertex hC hv
      obtain ⟨⟨r, hr, h, hsub⟩, r', hr', h', hnot⟩ :=
        exists_regions_of_circuit_edge hS hs hC hCs hl hg
      exact ⟨⟨r, ⟨hr, hsub⟩, hCs.1 hv, Or.inr hr, closure_minimal h isClosed_closure hvg⟩, r',
        ⟨hr', fun h'' => hnot h''.2⟩, hCs.1 hv, Or.inr hr',
        closure_minimal h' isClosed_closure hvg⟩
  · ext e
    rw [mem_boundaryDrawing_E]
    constructor
    · rintro ⟨⟨a, ⟨ha, hai⟩, hia⟩, b, ⟨hb, hbn⟩, hib⟩
      by_contra heC
      obtain ⟨p, hpe, hpb⟩ := hib.2.2
      have hea := edge_subset_closure_of_incident hS hia.1 ha hia.2.2
      have hpi : p ∈ ins C := hcl.closure_subset_iff.mpr hai (hea hpe)
      have hpU : p ∉ C.U := disjoint_left.mp (edge_disjoint_U hCs hia.1 heC) hpe
      exact hbn ⟨hb, region_subset_ins_of_closure hs hC hCs hl hb hpb hpi hpU⟩
    · intro he
      obtain ⟨x, hx⟩ := he.1
      obtain ⟨⟨r, hr, h, hsub⟩, r', hr', h', hnot⟩ :=
        exists_regions_of_circuit_edge hS hs hC hCs hl he
      exact ⟨⟨r, ⟨hr, hsub⟩, hCs.2 he, hr, x, hx, h hx⟩, r', ⟨hr', fun h'' => hnot h''.2⟩, hCs.2 he,
        hr', x, hx, h' hx⟩

end Disc

end GraphMinor.GM11
