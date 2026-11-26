/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section75Defs
public import LeanPool.GraphMinor.GM12.Section72
public import LeanPool.GraphMinor.GM12.Section73VertexReduction
public import LeanPool.GraphMinor.GM12.Section73NoParallel
import LeanPool.GraphMinor.GM12.Section74Bridge
import LeanPool.GraphMinor.GM12.Section78
import LeanPool.GraphMinor.GM12.Section79
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.Theorem66

/-!
# Graph Minors XII, (7.5) and Case 1 of (7.4)

This file formalizes the proved components of **(7.4)** (pages 262–263) and **(7.5)**
(pages 263–266) of Graph Minors XII:
1. **Case 1 of (7.4) (`theorem_7_4_case_1_step`, `exists_theorem_7_4_disc_reduction`,
   pages 262–263):** The inductive step on `|E(Γ)|` using **(7.2)** (`theorem_7_2`) when there is a
   `Γ`-normal `O`-arc `F` with `F ∩ V(Γ) = {v}` whose selected disc `Δ = ins(F)` contains an edge of
   `Γ`, together with the finite reduction to a subdrawing `Γ₀` with no such `O`-arc `F`.
2. **Case 1 of (7.5) (`theorem_7_5_lost_atoms_region`, `theorem_7_5_case_1_step`,
   `exists_theorem_7_5_disc_reduction`, page 264):** The inductive step on `|E(Γ)|` using **(7.2)**
   (`theorem_7_2`) when there is a `Γ`-normal `O`-arc `F ⊆ r ∪ {v}` with `F ∩ V(Γ) = {v}` whose
   selected disc `Δ = ins(F)` contains an edge of `Γ`, together with the finite reduction to a
   subdrawing `Γ₀` with no such `O`-arc `F`.
3. **Transition to Case 2 of (7.5) (`vertices_in_selected_region_disc_of_no_edges`,
   `no_parallel_spokes_at_region_hub`, page 265):** Once no `Γ₀`-normal `O`-arc `F ⊆ r₀ ∪ {v}` with
   `F ∩ V(Γ₀) = {v}` has an edge of `Γ₀` in its selected disc, the hub of `r₀` in any radial
   drawing `K` of `Γ₀` has no two parallel radial edges to the same vertex `v ∈ V(Γ₀)`.
4. **Case 2 deduction from (7.4) (`closure_region_subset_of_region_subset`,
   `incident_edge_subset_region_of_vertex_mem`, `U_subset_of_deleteVertices_U_subset`,
   `theorem_7_5_case_2_from_7_4`, pages 265–266):** Deduction of `(i)`–`(iv)` of **(7.5)** from
   `Theorem74Statement` applied to `(Γ₃, T₃, d₃, r₂*)`.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Function Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Subdrawing and vertex-deletion helpers for (7.4) and (7.5) -/

/-- If `Γ₁` is a subdrawing of `Γ₂` and `Z₂ ∩ Γ₁.V ⊆ Z₁`, then `deleteVertices Γ₁ Z₁` is a
subdrawing of `deleteVertices Γ₂ Z₂`. -/
theorem deleteVertices_mono_subdrawing {Γ₁ Γ₂ : Drawing S} {Z₁ Z₂ : Set S}
    (hSub : Γ₁.IsSubdrawing Γ₂) (hZ : Z₂ ∩ Γ₁.V ⊆ Z₁) :
    (deleteVertices Γ₁ Z₁).IsSubdrawing (deleteVertices Γ₂ Z₂) := by
  rw [isSubdrawing_deleteVertices_iff]
  refine ⟨(deleteVertices_isSubdrawing Γ₁ Z₁).trans hSub, ?_⟩
  rw [deleteVertices_V, disjoint_iff_inter_eq_empty]
  ext x
  simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false, not_and]
  intro ⟨hxV₁, hxZ₁⟩ hxZ₂
  exact hxZ₁ (hZ ⟨hxZ₂, hxV₁⟩)

omit [T2Space S] in
/-- In Case 1 of **(7.5)** (page 264), if `Γ''` is a subdrawing of `Γ` and `r ⊆ r''`, then the
vertices of `Γ''` incident with `r` in `Γ` are also incident with `r''` in `Γ''`:
`Z ∩ V(Γ'') ⊆ Z''`. -/
theorem incident_vertices_inter_subset {Γ Γ'' : Drawing S} {r r'' : Set S}
    (hr : r ⊆ r'') :
    {v ∈ Γ.V | v ∈ closure r} ∩ Γ''.V ⊆ {v ∈ Γ''.V | v ∈ closure r''} := by
  rintro v ⟨⟨_, hvr⟩, hv''⟩
  exact ⟨hv'', closure_mono hr hvr⟩

/-- In Case 1 of **(7.5)** (page 264), "Certainly $\Gamma'$ is a subdrawing of $\Gamma \setminus Z$,
since $Z \cap V(\Gamma'')
\subseteq Z''$": if `Γ''` is a subdrawing of `Γ`, `r ⊆ r''`, and `Γ'` is a subdrawing of
`Γ'' \ Z''`, then `Γ'` is a subdrawing of `Γ \ Z`. -/
theorem isSubdrawing_deleteVertices_of_region_subset {Γ Γ'' Γ' : Drawing S} {r r'' : Set S}
    (hSub'' : Γ''.IsSubdrawing Γ) (hr : r ⊆ r'')
    (hSub' : Γ'.IsSubdrawing (deleteVertices Γ'' {v ∈ Γ''.V | v ∈ closure r''})) :
    Γ'.IsSubdrawing (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}) :=
  hSub'.trans (deleteVertices_mono_subdrawing hSub'' (incident_vertices_inter_subset hr))

/-- Under the hypotheses of **(7.2)** (pages 259–260), the point set of `Γ` is contained in the
point set of `Γ'' = Γ.interSet (closure (univ \ Δ))` together with the merged region
`Y = r ∪ (Δ \ {v})`: `U(Γ) ⊆ U(Γ'') ∪ r''`. -/
theorem interSet_compl_disc_U_subset
    {Γ : Drawing S} {Δ F r : Set S} {v : S}
    (hbd : subBd Δ = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v}) :
    Γ.U ⊆ (Γ.interSet (closure (univ \ Δ))).U ∪ (r ∪ (Δ \ {v})) := by
  have hfr : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hbd
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hnorm : frontier (closure (univ \ Δ)) ∩ Γ.U ⊆ Γ.V := by
    rw [← compl_eq_univ_sdiff, closure_compl, frontier_compl]
    exact fun x hx => hn ⟨hfr ▸ frontier_interior_subset hx.1, hx.2⟩
  have hUeq := interSet_U_eq_of_normal_frontier isClosed_closure hnorm
  intro x hx
  by_cases hxout : x ∈ closure (univ \ Δ)
  · exact Or.inl (hUeq.symm ▸ ⟨hx, hxout⟩)
  · have hxi : x ∈ interior Δ := by
      by_contra h
      exact hxout (by rw [← compl_eq_univ_sdiff, closure_compl]; exact h)
    exact Or.inr (Or.inr ⟨interior_subset hxi, fun hxv =>
      (hfr.symm ▸ hvFV.1).2 (mem_singleton_iff.mp hxv ▸ hxi)⟩)

/-! ## 2. Case 1 of (7.4) (pages 262–263) -/

/-- The inductive step (Case 1) in the proof of **(7.4)** (Graph Minors XII, pages 262–263):
given a closed disc `D` bounded by a `Γ`-normal `O`-arc `F` with `F ∩ V(Γ) = {v}` and
`(Γ ∩ D, Γ ∩ closure (Σ \ D)) ∈ T`, let `Γ'' = Γ.interSet (closure (univ \ D))` and
`T'' = restrictTangle T Γ''.toHypergraph`. Then **(7.2)** provides a metric `d''` for `T''` in
`Γ''`, and any `(Γ', T', d', r')` satisfying the conclusion of **(7.4)** for `(Γ'', θ, T'', d'', v)`
also satisfies the conclusion of **(7.4)** for `(Γ, θ, T, d, v)`. -/
theorem theorem_7_4_case_1_step [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {v : S}
    (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d) (hv : v ∈ Γ.V)
    {D F : Set S} (hD : IsClosedDisc D) (hF : IsOArc F) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) :
    let Γ'' := Γ.interSet (closure (univ \ D))
    let T'' := restrictTangle T Γ''.toHypergraph
    v ∈ Γ''.V ∧
    ∃ (d'' : Set S → Set S → ℕ),
      HasTangleMetric Γ'' θ T'' d'' ∧
      (∀ (Γ' : Drawing S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ) (r' : Set S),
        Γ'.IsSubdrawing (deleteVertices Γ'' {v}) →
        (PaintingOrDrawing.drawing Γ').IsTwoCell →
        HasTangleMetric Γ' (θ - 1) T' d' →
        r' ∈ Γ'.R → v ∈ r' →
        Γ''.U ⊆ Γ'.U ∪ r' →
        (∀ a ∈ Γ''.A ∩ Γ'.A, ∀ b ∈ Γ''.A ∩ Γ'.A, d'' a b - 2 ≤ d' a b) →
        (∀ a ∈ Γ''.A ∩ Γ'.A, d'' a {v} - 1 ≤ d' a r') →
        (∀ a ∈ Γ''.A, a ⊆ r' → d'' a {v} ≤ 2) →
        Γ'.IsSubdrawing (deleteVertices Γ {v}) ∧
        (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
        HasTangleMetric Γ' (θ - 1) T' d' ∧
        r' ∈ Γ'.R ∧ v ∈ r' ∧
        Γ.U ⊆ Γ'.U ∪ r' ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 2 ≤ d' a b) ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, d a {v} - 1 ≤ d' a r') ∧
        (∀ a ∈ Γ.A, a ⊆ r' → d a {v} ≤ 2)) := by
  intro Γ'' T''
  have hSub'' : Γ''.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hfront : frontier D = F := (subBd_eq_frontier D).symm.trans hbd
  have hvF : v ∈ F := (hFV.symm ▸ mem_singleton v).1
  have hv'' : v ∈ Γ''.V := by
    have hvFront : v ∈ frontier D := hfront.symm ▸ hvF
    rw [frontier_eq_closure_inter_closure] at hvFront
    exact (mem_interSet_V_iff isClosed_closure).mpr
      ⟨hv, by simpa only [compl_eq_univ_sdiff] using hvFront.2⟩
  obtain ⟨r, hr, hFr⟩ := exists_region_of_normal_circle_single_vertex hF hn hFV
  obtain ⟨_, hlost, d'', r'', hd'', hr'', hrr'', hcomp_ab, _⟩ :=
    theorem_7_2_proof hS hθ hd hD hbd hn hFV hr hFr hm
  have hY : r ∪ (D \ {v}) ∈ Γ''.R := theorem_7_2_region hS hD hbd hn hFV hr hFr
  obtain ⟨x₀, hx₀r⟩ := region_nonempty hr
  have hr''_eq : r'' = r ∪ (D \ {v}) :=
    atom_eq_of_inter_nonempty (Or.inr hr'') (Or.inr hY) ⟨x₀, hrr'' hx₀r, Or.inl hx₀r⟩
  have hU_Γ'' : Γ.U ⊆ Γ''.U ∪ r'' :=
    hr''_eq.symm ▸ interSet_compl_disc_U_subset hbd hn hFV
  refine ⟨hv'', d'', hd'', ?_⟩
  intro Γ' T' d' r' hSub' htwo' hd' hr' hvr' hU' hii' hiii' hiv'
  have hSub_Γ'Γ'' : Γ'.IsSubdrawing Γ'' :=
    hSub'.trans (deleteVertices_isSubdrawing Γ'' {v})
  have hSub_del : Γ'.IsSubdrawing (deleteVertices Γ {v}) :=
    hSub'.trans (deleteVertices_mono_subdrawing hSub'' inter_subset_left)
  have hv_bd : v ∈ discBd D :=
    ((IsClosedDisc.frontier_eq_discBd hS hD).symm.trans hfront) ▸ hvF
  have hInt_sub : discInt D ⊆ r'' := fun x hx =>
    hr''_eq ▸ Or.inr ⟨hx.1, fun hxv => hx.2 (mem_singleton_iff.mp hxv ▸ hv_bd)⟩
  have hvr''_cl : v ∈ closure r'' :=
    closure_mono hInt_sub (hD.subset_closure_discInt (Surface.discBd_subset D hv_bd))
  have hr''_sub_r' : r'' ⊆ r' := by
    have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
    obtain ⟨w, hwr', hwr''⟩ := mem_closure_iff.mp hvr''_cl r' (region_isOpen hr') hvr'
    exact region_subset_region_of_inter_nonempty hSub_Γ'Γ'' hr'' hr' ⟨w, hwr'', hwr'⟩
  have hU_Γ : Γ.U ⊆ Γ'.U ∪ r' :=
    hU_Γ''.trans (union_subset hU' (hr''_sub_r'.trans subset_union_right))
  have hvA_Γ : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hvA_Γ'' : ({v} : Set S) ∈ Γ''.A := Or.inl (Or.inl ⟨v, hv'', rfl⟩)
  refine ⟨hSub_del, htwo', hd', hr', hvr', hU_Γ, ?_, ?_, ?_⟩
  · intro a ha b hb
    have ha'' : a ∈ Γ''.A := shared_atom_mem_intermediate hSub'' hSub_Γ'Γ'' ha.1 ha.2
    have hb'' : b ∈ Γ''.A := shared_atom_mem_intermediate hSub'' hSub_Γ'Γ'' hb.1 hb.2
    have h1 := hcomp_ab a ⟨ha.1, ha''⟩ b ⟨hb.1, hb''⟩
    have h2 := hii' a ⟨ha'', ha.2⟩ b ⟨hb'', hb.2⟩
    omega
  · intro a ha
    have ha'' : a ∈ Γ''.A := shared_atom_mem_intermediate hSub'' hSub_Γ'Γ'' ha.1 ha.2
    have h1 := hcomp_ab a ⟨ha.1, ha''⟩ {v} ⟨hvA_Γ, hvA_Γ''⟩
    have h2 := hiii' a ⟨ha'', ha.2⟩
    omega
  · intro a ha har'
    by_cases ha'' : a ∈ Γ''.A
    · have h1 := hcomp_ab a ⟨ha, ha''⟩ {v} ⟨hvA_Γ, hvA_Γ''⟩
      have h2 := hiv' a ha'' har'
      omega
    · have h1 := hlost a ⟨ha, ha''⟩
      omega

/-- The finite selected-disc reduction for **(7.4)** (Graph Minors XII, pages 262–263):
by induction on `|E(Γ)|` using `theorem_7_4_case_1_step`, there is a 2-cell subdrawing `Γ₀` of `Γ`
with `v ∈ V(Γ₀)` and a respectful tangle `T₀` of order `θ` in `Γ₀` with metric `d₀` such that:
1. no `Γ₀`-normal `O`-arc `F` with `F ∩ V(Γ₀) = {v}` has an edge of `Γ₀` in its selected disc, and
2. any `(Γ', T', d', r')` satisfying the conclusion of **(7.4)** for `(Γ₀, θ, T₀, d₀, v)` also
   satisfies the conclusion of **(7.4)** for `(Γ, θ, T, d, v)`. -/
theorem exists_theorem_7_4_disc_reduction [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {v : S}
    (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d) (hv : v ∈ Γ.V) :
    ∃ (Γ₀ : Drawing S)
      (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₀ : Set S → Set S → ℕ),
      Γ₀.IsSubdrawing Γ ∧ v ∈ Γ₀.V ∧
      HasTangleMetric Γ₀ θ T₀ d₀ ∧
      (∀ D F : Set S, IsClosedDisc D → IsOArc F → subBd D = F →
        (PaintingOrDrawing.drawing Γ₀).IsNormal F → F ∩ Γ₀.V = {v} →
        ((PaintingOrDrawing.drawing Γ₀).inter D,
          (PaintingOrDrawing.drawing Γ₀).interOutside D) ∈ T₀ →
        ∀ e ∈ Γ₀.E, ¬ e ⊆ D) ∧
      (∀ (Γ' : Drawing S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ) (r' : Set S),
        Γ'.IsSubdrawing (deleteVertices Γ₀ {v}) →
        (PaintingOrDrawing.drawing Γ').IsTwoCell →
        HasTangleMetric Γ' (θ - 1) T' d' →
        r' ∈ Γ'.R → v ∈ r' →
        Γ₀.U ⊆ Γ'.U ∪ r' →
        (∀ a ∈ Γ₀.A ∩ Γ'.A, ∀ b ∈ Γ₀.A ∩ Γ'.A, d₀ a b - 2 ≤ d' a b) →
        (∀ a ∈ Γ₀.A ∩ Γ'.A, d₀ a {v} - 1 ≤ d' a r') →
        (∀ a ∈ Γ₀.A, a ⊆ r' → d₀ a {v} ≤ 2) →
        Γ'.IsSubdrawing (deleteVertices Γ {v}) ∧
        (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
        HasTangleMetric Γ' (θ - 1) T' d' ∧
        r' ∈ Γ'.R ∧ v ∈ r' ∧
        Γ.U ⊆ Γ'.U ∪ r' ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 2 ≤ d' a b) ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, d a {v} - 1 ≤ d' a r') ∧
        (∀ a ∈ Γ.A, a ⊆ r' → d a {v} ≤ 2)) := by
  classical
  have hex : ∃ n : ℕ, ∃ (Γ₀ : Drawing S)
      (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₀ : Set S → Set S → ℕ),
      Γ₀.IsSubdrawing Γ ∧ v ∈ Γ₀.V ∧
      HasTangleMetric Γ₀ θ T₀ d₀ ∧
      (∀ (Γ' : Drawing S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ) (r' : Set S),
        Γ'.IsSubdrawing (deleteVertices Γ₀ {v}) →
        (PaintingOrDrawing.drawing Γ').IsTwoCell →
        HasTangleMetric Γ' (θ - 1) T' d' →
        r' ∈ Γ'.R → v ∈ r' →
        Γ₀.U ⊆ Γ'.U ∪ r' →
        (∀ a ∈ Γ₀.A ∩ Γ'.A, ∀ b ∈ Γ₀.A ∩ Γ'.A, d₀ a b - 2 ≤ d' a b) →
        (∀ a ∈ Γ₀.A ∩ Γ'.A, d₀ a {v} - 1 ≤ d' a r') →
        (∀ a ∈ Γ₀.A, a ⊆ r' → d₀ a {v} ≤ 2) →
        Γ'.IsSubdrawing (deleteVertices Γ {v}) ∧
        (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
        HasTangleMetric Γ' (θ - 1) T' d' ∧
        r' ∈ Γ'.R ∧ v ∈ r' ∧
        Γ.U ⊆ Γ'.U ∪ r' ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 2 ≤ d' a b) ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, d a {v} - 1 ≤ d' a r') ∧
        (∀ a ∈ Γ.A, a ⊆ r' → d a {v} ≤ 2)) ∧
      Γ₀.E.ncard = n :=
    ⟨Γ.E.ncard, Γ, T, d, Drawing.IsSubdrawing.refl Γ, hv, hd,
      fun _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, rfl⟩
  obtain ⟨Γ₀, T₀, d₀, hΓ₀, hv₀, hd₀, hlift₀, hcount⟩ := Nat.find_spec hex
  refine ⟨Γ₀, T₀, d₀, hΓ₀, hv₀, hd₀, ?_, hlift₀⟩
  intro D F hD hF hbd hn hFV hm e he heD
  obtain ⟨hv₁, d₁, hd₁, hstep₁⟩ :=
    theorem_7_4_case_1_step hS hθ hd₀ hv₀ hD hF hbd hn hFV hm
  let Γ₁ := Γ₀.interSet (closure (univ \ D))
  let T₁ := restrictTangle T₀ Γ₁.toHypergraph
  have hΓ₁ : Γ₁.IsSubdrawing Γ₀ := Drawing.span_isSubdrawing Γ₀ _ _
  have hfront : frontier D = F := (subBd_eq_frontier D).symm.trans hbd
  have hless : Γ₁.E.ncard < Γ₀.E.ncard := ncard_edges_outside_lt_of_edge_inside
    (fun x hx => hn ⟨hfront ▸ hx.1, hx.2⟩) he heD
  have hlift₁ : ∀ (Γ' : Drawing S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r' : Set S),
      Γ'.IsSubdrawing (deleteVertices Γ₁ {v}) →
      (PaintingOrDrawing.drawing Γ').IsTwoCell →
      HasTangleMetric Γ' (θ - 1) T' d' →
      r' ∈ Γ'.R → v ∈ r' →
      Γ₁.U ⊆ Γ'.U ∪ r' →
      (∀ a ∈ Γ₁.A ∩ Γ'.A, ∀ b ∈ Γ₁.A ∩ Γ'.A, d₁ a b - 2 ≤ d' a b) →
      (∀ a ∈ Γ₁.A ∩ Γ'.A, d₁ a {v} - 1 ≤ d' a r') →
      (∀ a ∈ Γ₁.A, a ⊆ r' → d₁ a {v} ≤ 2) →
      Γ'.IsSubdrawing (deleteVertices Γ {v}) ∧
      (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
      HasTangleMetric Γ' (θ - 1) T' d' ∧
      r' ∈ Γ'.R ∧ v ∈ r' ∧
      Γ.U ⊆ Γ'.U ∪ r' ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 2 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, d a {v} - 1 ≤ d' a r') ∧
      (∀ a ∈ Γ.A, a ⊆ r' → d a {v} ≤ 2) := by
    intro Γ' T' d' r' h1 h2 h3 h4 h5 h6 h7 h8 h9
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ :=
      hstep₁ Γ' T' d' r' h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact hlift₀ Γ' T' d' r' s1 s2 s3 s4 s5 s6 s7 s8 s9
  have hminimal : Nat.find hex ≤ Γ₁.E.ncard := Nat.find_min' hex
    ⟨Γ₁, T₁, d₁, hΓ₁.trans hΓ₀, hv₁, hd₁, hlift₁, rfl⟩
  rw [← hcount] at hminimal
  exact (Nat.not_le_of_lt hless) hminimal

/-! ## 3. Case 1 of (7.5) (page 264) -/

/-- In Case 1 of **(7.5)** (Graph Minors XII, page 264, line 639):
"If $a \notin A(\Gamma'')$, then $a \cap ins(F) \ne \emptyset$, and so $d(a, r) \le 1 \le 3$." -/
theorem theorem_7_5_lost_atoms_region (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {Δ F r : Set S} {v : S} (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F)
    (hFV : F ∩ Γ.V = {v}) (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hm : ((PaintingOrDrawing.drawing Γ).inter Δ,
      (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T)
    {a : Set S} (ha : a ∈ Γ.A)
    (han : a ∉ (Γ.interSet (closure (univ \ Δ))).A) : d a r ≤ 1 := by
  let Γ'' := Γ.interSet (closure (univ \ Δ))
  let Y := r ∪ (Δ \ {v})
  have hsub : Γ''.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hY : Y ∈ Γ''.R := theorem_7_2_region hS hΔ hbd hn hFV hr hFr
  have hfr : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hbd
  have hdb : discBd Δ = F := (IsClosedDisc.frontier_eq_discBd hS hΔ).symm.trans hfr
  have hcover : Γ.U ⊆ Γ''.U ∪ Y := interSet_compl_disc_U_subset hbd hn hFV
  obtain ⟨a', ha', haa'⟩ := exists_atom_superset_of_isSubdrawing hsub ha
  have haY : a ⊆ Y := by
    rcases atom_eq_or_eq_region_of_U_subset hsub hY hcover ha ha' haa' with
      ⟨_, hmem⟩ | ⟨_, haY⟩
    · exact (han hmem.2).elim
    · exact haY
  have hrΔ : (r ∩ Δ).Nonempty := by
    obtain ⟨w, hw, hwv⟩ :=
      (infinite_of_isOArc hΔ.isOArc_discBd).exists_notMem_finite (finite_singleton v)
    exact ⟨w, hFr ⟨hdb ▸ hw, hwv⟩, Surface.discBd_subset Δ hw⟩
  have haΔ : (a ∩ Δ).Nonempty := by
    obtain ⟨x, hxa⟩ := atom_nonempty' ha
    rcases haY hxa with hxr | hxΔ
    · have heq : a = r := atom_eq_of_inter_nonempty ha (Or.inr hr) ⟨x, hxa, hxr⟩
      exact heq.symm ▸ hrΔ
    · exact ⟨x, hxa, hxΔ.1⟩
  have hcard : (F ∩ Γ.V).ncard < θ := by rw [hFV, ncard_singleton]; omega
  have hbound := dist_le_of_oarc_disc hS hd (hdb ▸ hΔ.isOArc_discBd) hn hcard hΔ hbd hm ha
    (Or.inr hr) haΔ hrΔ
  simpa only [hFV, ncard_singleton] using hbound

/-- The inductive step (Case 1) in the proof of **(7.5)** (Graph Minors XII, page 264,
lines 601–640):
Suppose there is a `Γ`-normal `O`-arc `F ⊆ r ∪ {v}` with `F ∩ V(Γ) = {v}` and selected closed
disc `Δ = ins(F)`. Let `Γ'' = Γ.interSet (closure (univ \ Δ))` and
`T'' = restrictTangle T Γ''.toHypergraph`. Then **(7.2)** provides a metric `d''` for `T''` in
`Γ''` and a region `r'' ∈ R(Γ'')` with `r ⊆ r''` satisfying `(v)` and `(vi)` of page 264, and any
`(Γ', T', d', r')` satisfying the conclusion `(i')`–`(iv')` of **(7.5)** for `(Γ'', θ, T'', d'',
r'')`
also satisfies `(i)`–`(iv)` of **(7.5)** for `(Γ, θ, T, d, r)`. -/
theorem theorem_7_5_case_1_step [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r : Set S}
    (hθ : 3 ≤ θ) (hd : HasTangleMetric Γ θ T d) (hr : r ∈ Γ.R)
    {Δ F : Set S} {v : S} (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hFr : F \ {v} ⊆ r)
    (hm : ((PaintingOrDrawing.drawing Γ).inter Δ,
      (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T) :
    let Γ'' := Γ.interSet (closure (univ \ Δ))
    let T'' := restrictTangle T Γ''.toHypergraph
    ∃ (d'' : Set S → Set S → ℕ) (r'' : Set S),
      HasTangleMetric Γ'' θ T'' d'' ∧
      r'' ∈ Γ''.R ∧ r ⊆ r'' ∧
      (∀ a ∈ Γ.A ∩ Γ''.A, ∀ b ∈ Γ.A ∩ Γ''.A, d a b ≤ d'' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ''.A, d a r ≤ d'' a r'') ∧
      (∀ (Γ' : Drawing S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ) (r' : Set S),
        Γ'.IsSubdrawing (deleteVertices Γ'' {w ∈ Γ''.V | w ∈ closure r''}) →
        (PaintingOrDrawing.drawing Γ').IsTwoCell →
        HasTangleMetric Γ' (θ - 2) T' d' →
        r' ∈ Γ'.R → r'' ⊆ r' →
        Γ''.U ⊆ Γ'.U ∪ r' →
        (∀ a ∈ Γ''.A ∩ Γ'.A, ∀ b ∈ Γ''.A ∩ Γ'.A, d'' a b - 4 ≤ d' a b) →
        (∀ a ∈ Γ''.A ∩ Γ'.A, d'' a r'' - 2 ≤ d' a r') →
        (∀ a ∈ Γ''.A, a ⊆ r' → d'' a r'' ≤ 3) →
        Γ'.IsSubdrawing (deleteVertices Γ {w ∈ Γ.V | w ∈ closure r}) ∧
        (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
        HasTangleMetric Γ' (θ - 2) T' d' ∧
        r' ∈ Γ'.R ∧ r ⊆ r' ∧
        Γ.U ⊆ Γ'.U ∪ r' ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 ≤ d' a b) ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 ≤ d' a r') ∧
        (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 3)) := by
  intro Γ'' T''
  have hθ2 : 2 ≤ θ := by omega
  have hSub'' : Γ''.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  obtain ⟨_, _, d'', r'', hd'', hr'', hrr'', hv_ab, hvi_ar⟩ :=
    theorem_7_2_proof hS hθ2 hd hΔ hbd hn hFV hr hFr hm
  have hY : r ∪ (Δ \ {v}) ∈ Γ''.R := theorem_7_2_region hS hΔ hbd hn hFV hr hFr
  obtain ⟨x₀, hx₀r⟩ := region_nonempty hr
  have hr''_eq : r'' = r ∪ (Δ \ {v}) :=
    atom_eq_of_inter_nonempty (Or.inr hr'') (Or.inr hY) ⟨x₀, hrr'' hx₀r, Or.inl hx₀r⟩
  have hU_Γ'' : Γ.U ⊆ Γ''.U ∪ r'' :=
    hr''_eq.symm ▸ interSet_compl_disc_U_subset hbd hn hFV
  refine ⟨d'', r'', hd'', hr'', hrr'', hv_ab, hvi_ar, ?_⟩
  intro Γ' T' d' r' hSub' htwo' hd' hr' hr''r' hU' hii' hiii' hiv'
  have hSub_Γ'Γ'' : Γ'.IsSubdrawing Γ'' :=
    hSub'.trans (deleteVertices_isSubdrawing Γ'' _)
  have hSub_del : Γ'.IsSubdrawing (deleteVertices Γ {w ∈ Γ.V | w ∈ closure r}) :=
    isSubdrawing_deleteVertices_of_region_subset hSub'' hrr'' hSub'
  have hrr' : r ⊆ r' := hrr''.trans hr''r'
  have hU_Γ : Γ.U ⊆ Γ'.U ∪ r' :=
    hU_Γ''.trans (union_subset hU' (hr''r'.trans subset_union_right))
  refine ⟨hSub_del, htwo', hd', hr', hrr', hU_Γ, ?_, ?_, ?_⟩
  · intro a ha b hb
    have ha'' : a ∈ Γ''.A := shared_atom_mem_intermediate hSub'' hSub_Γ'Γ'' ha.1 ha.2
    have hb'' : b ∈ Γ''.A := shared_atom_mem_intermediate hSub'' hSub_Γ'Γ'' hb.1 hb.2
    have h1 := hv_ab a ⟨ha.1, ha''⟩ b ⟨hb.1, hb''⟩
    have h2 := hii' a ⟨ha'', ha.2⟩ b ⟨hb'', hb.2⟩
    omega
  · intro a ha
    have ha'' : a ∈ Γ''.A := shared_atom_mem_intermediate hSub'' hSub_Γ'Γ'' ha.1 ha.2
    have h1 := hvi_ar a ⟨ha.1, ha''⟩
    have h2 := hiii' a ⟨ha'', ha.2⟩
    omega
  · intro a ha har'
    by_cases ha'' : a ∈ Γ''.A
    · have h1 := hvi_ar a ⟨ha, ha''⟩
      have h2 := hiv' a ha'' har'
      omega
    · have h1 := theorem_7_5_lost_atoms_region hS hθ2 hd hΔ hbd hn hFV hr hFr hm ha ha''
      omega

/-- The finite selected-disc reduction for **(7.5)** (Graph Minors XII, page 264):
by induction on `|E(Γ)|` using `theorem_7_5_case_1_step`, there is a 2-cell subdrawing `Γ₀` of `Γ`,
a respectful tangle `T₀` of order `θ` in `Γ₀` with metric `d₀`, and a region `r₀ ∈ R(Γ₀)` with
`r ⊆ r₀` such that:
1. no `Γ₀`-normal `O`-arc `F ⊆ r₀ ∪ {v}` with `F ∩ V(Γ₀) = {v}` has an edge of `Γ₀` in its
   selected disc `Δ = ins(F)`, and
2. any `(Γ', T', d', r')` satisfying the conclusion of **(7.5)** for `(Γ₀, θ, T₀, d₀, r₀)` also
   satisfies the conclusion of **(7.5)** for `(Γ, θ, T, d, r)`. -/
theorem exists_theorem_7_5_disc_reduction [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {r : Set S}
    (hθ : 3 ≤ θ) (hd : HasTangleMetric Γ θ T d) (hr : r ∈ Γ.R) :
    ∃ (Γ₀ : Drawing S)
      (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₀ : Set S → Set S → ℕ) (r₀ : Set S),
      Γ₀.IsSubdrawing Γ ∧
      HasTangleMetric Γ₀ θ T₀ d₀ ∧
      r₀ ∈ Γ₀.R ∧ r ⊆ r₀ ∧
      (∀ Δ F : Set S, ∀ v : S, IsClosedDisc Δ → subBd Δ = F →
        (PaintingOrDrawing.drawing Γ₀).IsNormal F → F ∩ Γ₀.V = {v} →
        F \ {v} ⊆ r₀ →
        ((PaintingOrDrawing.drawing Γ₀).inter Δ,
          (PaintingOrDrawing.drawing Γ₀).interOutside Δ) ∈ T₀ →
        ∀ e ∈ Γ₀.E, ¬ e ⊆ Δ) ∧
      (∀ (Γ' : Drawing S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ) (r' : Set S),
        Γ'.IsSubdrawing (deleteVertices Γ₀ {w ∈ Γ₀.V | w ∈ closure r₀}) →
        (PaintingOrDrawing.drawing Γ').IsTwoCell →
        HasTangleMetric Γ' (θ - 2) T' d' →
        r' ∈ Γ'.R → r₀ ⊆ r' →
        Γ₀.U ⊆ Γ'.U ∪ r' →
        (∀ a ∈ Γ₀.A ∩ Γ'.A, ∀ b ∈ Γ₀.A ∩ Γ'.A, d₀ a b - 4 ≤ d' a b) →
        (∀ a ∈ Γ₀.A ∩ Γ'.A, d₀ a r₀ - 2 ≤ d' a r') →
        (∀ a ∈ Γ₀.A, a ⊆ r' → d₀ a r₀ ≤ 3) →
        Γ'.IsSubdrawing (deleteVertices Γ {w ∈ Γ.V | w ∈ closure r}) ∧
        (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
        HasTangleMetric Γ' (θ - 2) T' d' ∧
        r' ∈ Γ'.R ∧ r ⊆ r' ∧
        Γ.U ⊆ Γ'.U ∪ r' ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 ≤ d' a b) ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 ≤ d' a r') ∧
        (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 3)) := by
  classical
  have hex : ∃ n : ℕ, ∃ (Γ₀ : Drawing S)
      (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₀ : Set S → Set S → ℕ) (r₀ : Set S),
      Γ₀.IsSubdrawing Γ ∧
      HasTangleMetric Γ₀ θ T₀ d₀ ∧
      r₀ ∈ Γ₀.R ∧ r ⊆ r₀ ∧
      (∀ (Γ' : Drawing S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ) (r' : Set S),
        Γ'.IsSubdrawing (deleteVertices Γ₀ {w ∈ Γ₀.V | w ∈ closure r₀}) →
        (PaintingOrDrawing.drawing Γ').IsTwoCell →
        HasTangleMetric Γ' (θ - 2) T' d' →
        r' ∈ Γ'.R → r₀ ⊆ r' →
        Γ₀.U ⊆ Γ'.U ∪ r' →
        (∀ a ∈ Γ₀.A ∩ Γ'.A, ∀ b ∈ Γ₀.A ∩ Γ'.A, d₀ a b - 4 ≤ d' a b) →
        (∀ a ∈ Γ₀.A ∩ Γ'.A, d₀ a r₀ - 2 ≤ d' a r') →
        (∀ a ∈ Γ₀.A, a ⊆ r' → d₀ a r₀ ≤ 3) →
        Γ'.IsSubdrawing (deleteVertices Γ {w ∈ Γ.V | w ∈ closure r}) ∧
        (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
        HasTangleMetric Γ' (θ - 2) T' d' ∧
        r' ∈ Γ'.R ∧ r ⊆ r' ∧
        Γ.U ⊆ Γ'.U ∪ r' ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 ≤ d' a b) ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 ≤ d' a r') ∧
        (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 3)) ∧
      Γ₀.E.ncard = n :=
    ⟨Γ.E.ncard, Γ, T, d, r, Drawing.IsSubdrawing.refl Γ, hd, hr, Subset.rfl,
      fun _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, rfl⟩
  obtain ⟨Γ₀, T₀, d₀, r₀, hΓ₀, hd₀, hr₀, hrr₀, hlift₀, hcount⟩ := Nat.find_spec hex
  refine ⟨Γ₀, T₀, d₀, r₀, hΓ₀, hd₀, hr₀, hrr₀, ?_, hlift₀⟩
  intro Δ F v hΔ hbd hn hFV hFr₀ hm e he heΔ
  obtain ⟨d₁, r₁, hd₁, hr₁, hr₀r₁, _, _, hstep₁⟩ :=
    theorem_7_5_case_1_step hS hθ hd₀ hr₀ hΔ hbd hn hFV hFr₀ hm
  let Γ₁ := Γ₀.interSet (closure (univ \ Δ))
  let T₁ := restrictTangle T₀ Γ₁.toHypergraph
  have hΓ₁ : Γ₁.IsSubdrawing Γ₀ := Drawing.span_isSubdrawing Γ₀ _ _
  have hfront : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hbd
  have hless : Γ₁.E.ncard < Γ₀.E.ncard := ncard_edges_outside_lt_of_edge_inside
    (fun x hx => hn ⟨hfront ▸ hx.1, hx.2⟩) he heΔ
  have hlift₁ : ∀ (Γ' : Drawing S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r' : Set S),
      Γ'.IsSubdrawing (deleteVertices Γ₁ {w ∈ Γ₁.V | w ∈ closure r₁}) →
      (PaintingOrDrawing.drawing Γ').IsTwoCell →
      HasTangleMetric Γ' (θ - 2) T' d' →
      r' ∈ Γ'.R → r₁ ⊆ r' →
      Γ₁.U ⊆ Γ'.U ∪ r' →
      (∀ a ∈ Γ₁.A ∩ Γ'.A, ∀ b ∈ Γ₁.A ∩ Γ'.A, d₁ a b - 4 ≤ d' a b) →
      (∀ a ∈ Γ₁.A ∩ Γ'.A, d₁ a r₁ - 2 ≤ d' a r') →
      (∀ a ∈ Γ₁.A, a ⊆ r' → d₁ a r₁ ≤ 3) →
      Γ'.IsSubdrawing (deleteVertices Γ {w ∈ Γ.V | w ∈ closure r}) ∧
      (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
      HasTangleMetric Γ' (θ - 2) T' d' ∧
      r' ∈ Γ'.R ∧ r ⊆ r' ∧
      Γ.U ⊆ Γ'.U ∪ r' ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 4 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, d a r - 2 ≤ d' a r') ∧
      (∀ a ∈ Γ.A, a ⊆ r' → d a r ≤ 3) := by
    intro Γ' T' d' r' h1 h2 h3 h4 h5 h6 h7 h8 h9
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ :=
      hstep₁ Γ' T' d' r' h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact hlift₀ Γ' T' d' r' s1 s2 s3 s4 s5 s6 s7 s8 s9
  have hminimal : Nat.find hex ≤ Γ₁.E.ncard := Nat.find_min' hex
    ⟨Γ₁, T₁, d₁, r₁, hΓ₁.trans hΓ₀, hd₁, hr₁, hrr₀.trans hr₀r₁, hlift₁, rfl⟩
  rw [← hcount] at hminimal
  exact (Nat.not_le_of_lt hless) hminimal

/-! ## 4. Transition to Case 2 of (7.5): no parallel radial spokes at the region hub (page 265) -/

/-- In a 2-cell drawing `Γ` on a closed surface `S`, if `D` is a closed disc whose `Γ`-normal
boundary `F = subBd D` meets `Γ.V` only at `{v}`, and `D` contains no edge of `Γ`, then
`Γ.V ∩ D = {v}` (without requiring `(deleteVertices Γ {v}).IsTwoCell`). -/
theorem vertices_in_selected_region_disc_of_no_edges [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S}
    (htwo : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    {D F : Set S} {v : S}
    (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hno : ∀ e ∈ Γ.E, ¬ e ⊆ D) : Γ.V ∩ D = {v} := by
  have hfront : frontier D = F := (subBd_eq_frontier D).symm.trans hbd
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hvD : v ∈ D := hD.isClosed.closure_subset_iff.mpr subset_rfl ((hfront.symm ▸ hvFV.1).1)
  apply Subset.antisymm
  · rintro w ⟨hwV, hwD⟩
    by_contra hwv
    have hw_not_F : w ∉ F := fun hwF => hwv (mem_singleton_iff.mp (hFV.subset ⟨hwF, hwV⟩))
    have hw_int : w ∈ interior D := by
      by_contra hw_nint
      exact hw_not_F (hfront ▸ ⟨subset_closure hwD, hw_nint⟩)
    have hUD_sub_V : Γ.U ∩ D ⊆ Γ.V := by
      rintro x ⟨hxU, hxD⟩
      by_cases hxV : x ∈ Γ.V
      · exact hxV
      · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
        have hdis : Disjoint e (frontier D) := by
          apply disjoint_left.mpr
          intro y hye hyF
          exact (he.2.1 hye).2 (hn ⟨hfront ▸ hyF, (he.2.1 hye).1⟩)
        exact (hno e he (subset_of_disjoint_frontier he.2.2.1.isConnected.isPreconnected
          hD.isClosed hdis hxe hxD)).elim
    have hUint_eq : Γ.U ∩ interior D = (Γ.V ∩ D) \ {v} := by
      ext x
      simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨hxU, hxInt⟩
        have hxD : x ∈ D := interior_subset hxInt
        have hxV : x ∈ Γ.V := hUD_sub_V ⟨hxU, hxD⟩
        refine ⟨⟨hxV, hxD⟩, ?_⟩
        rintro rfl
        exact (hfront.symm ▸ hvFV.1).2 hxInt
      · rintro ⟨⟨hxV, hxD⟩, hxv⟩
        refine ⟨Γ.V_subset_U hxV, ?_⟩
        by_contra hx_nint
        have hxF : x ∈ F := hfront ▸ ⟨subset_closure hxD, hx_nint⟩
        exact hxv (mem_singleton_iff.mp (hFV.subset ⟨hxF, hxV⟩))
    have hVfin : Γ.V.Finite := Γ.toHypergraph.vertexSet_finite
    have hfin : ((Γ.V ∩ D) \ {v}).Finite :=
      (hVfin.subset inter_subset_left).subset sdiff_subset
    have hclosed : IsClosed ((Γ.V ∩ D) \ {v}) := hfin.isClosed
    have hU_conn : IsPreconnected Γ.U := isPreconnected_U_of_isTwoCell hS htwo
    have hsub_union : Γ.U ⊆ interior D ∪ ((Γ.V ∩ D) \ {v})ᶜ := by
      intro x hxU
      by_cases hxInt : x ∈ interior D
      · exact Or.inl hxInt
      · refine Or.inr (fun hx_mem => hxInt ?_)
        have : x ∈ Γ.U ∩ interior D := hUint_eq.symm ▸ hx_mem
        exact this.2
    have hne_left : (Γ.U ∩ interior D).Nonempty := ⟨w, Γ.V_subset_U hwV, hw_int⟩
    have hne_right : (Γ.U ∩ ((Γ.V ∩ D) \ {v})ᶜ).Nonempty :=
      ⟨v, Γ.V_subset_U hvFV.2, fun hv_mem => hv_mem.2 rfl⟩
    obtain ⟨z, hzU, hzInt, hzn⟩ :=
      hU_conn (interior D) (((Γ.V ∩ D) \ {v})ᶜ) isOpen_interior hclosed.isOpen_compl
        hsub_union hne_left hne_right
    exact hzn (hUint_eq ▸ ⟨hzU, hzInt⟩)
  · rintro x hx
    rcases mem_singleton_iff.mp hx with rfl
    exact ⟨hvFV.2, hvD⟩

/-- In Case 2 of **(7.5)** (Graph Minors XII, page 265, line 643), once there is no `Γ`-normal
`O`-arc `F ⊆ r ∪ {v}` with `F ∩ V(Γ) = {v}` whose selected disc `Δ = ins(F)` contains an edge of
`Γ`, in any radial drawing `K` of `Γ`, the hub `u ∈ r ∩ K.V` has no two parallel radial edges
`g ≠ h` to the same vertex `v ∈ V(Γ)`. -/
theorem no_parallel_spokes_at_region_hub [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {r : Set S} (hr : r ∈ Γ.R)
    (hno : ∀ Δ F : Set S, ∀ v : S, IsClosedDisc Δ → subBd Δ = F →
      (PaintingOrDrawing.drawing Γ).IsNormal F → F ∩ Γ.V = {v} →
      F \ {v} ⊆ r →
      ((PaintingOrDrawing.drawing Γ).inter Δ,
        (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T →
      ∀ e ∈ Γ.E, ¬ e ⊆ Δ)
    {g h : Set S} {v u : S} (hv : v ∈ Γ.V) (hg : g ∈ K.E) (hh : h ∈ K.E) (hgh : g ≠ h)
    (hur : u ∈ r) (huK : u ∈ K.V)
    (hcapg : closure g ∩ K.V = {v, u}) (hcaph : closure h ∩ K.V = {v, u}) : False := by
  apply parallel_spokes_contradiction hS hθ hT hK hv hg hh hgh hr hur huK hcapg hcaph
  intro D F hD _ hbd hn hFV hFr hm
  have hnone := hno D F v hD hbd hn hFV hFr hm
  exact ⟨vertices_in_selected_region_disc_of_no_edges hS hT.1 hD hbd hn hFV hnone, hnone⟩

/-! ## 5. Case 2 of (7.5): deduction of (i)–(iv) from (7.4) (pages 265–266) -/

/-- If two drawings `H` and `H₁` share a radial drawing `K` and derived slope `ins`, and `a` and
`a_star` (respectively `b` and `b_star`) have the same corresponding atoms in `A(K)` (with
`a = b ↔ a_star = b_star`), then `tangleMetric H₁ K ins θ a_star b_star = tangleMetric H K ins θ a
b`
(Graph Minors XII, Section 7, page 265, line 643). -/
theorem tangleMetric_eq_of_correspondingAtom_iff {H H₁ K : Drawing S}
    {ins : Drawing S → Set S} {θ : ℕ} {a b a_star b_star : Set S}
    (heq : a = b ↔ a_star = b_star)
    (ha : ∀ x' : Set S, IsCorrespondingAtom H K a x' ↔ IsCorrespondingAtom H₁ K a_star x')
    (hb : ∀ y' : Set S, IsCorrespondingAtom H K b y' ↔ IsCorrespondingAtom H₁ K b_star y') :
    tangleMetric H₁ K ins θ a_star b_star = tangleMetric H K ins θ a b := by
  classical
  unfold tangleMetric
  by_cases hab : a = b
  · have hab_star : a_star = b_star := heq.mp hab
    simp [hab, hab_star]
  · have hab_star : a_star ≠ b_star := fun h => hab (heq.mpr h)
    simp only [hab, hab_star, ↓reduceIte, ← ha, ← hb]

/-- In Case 2 of **(7.5)** (Graph Minors XII, page 265):
"By [5, Theorem (6.6)], there is a respectful tangle $\mathscr{T}_1$ of order $\theta$ in
$\Gamma_1$,
with metric $d_1$, such that $d_1(a^*, b^*) = d(a, b)$ for all $a, b \in A(\Gamma)$."
Here `Γ` and `Γ₁` share the radial drawing `K` witnessing `HasTangleMetric Γ θ T d`. -/
theorem exists_dual_tangleMetric_of_common_radial [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ Γ₁ K : Drawing S} {ins : Drawing S → Set S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 3 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    (hE₁ : Γ₁.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hK₁ : (PaintingOrDrawing.drawing Γ₁).IsRadialDrawing K)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins) :
    ∃ (T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d₁ : Set S → Set S → ℕ),
      HasTangleMetric Γ₁ θ T₁ d₁ ∧
      IsDerivedSlope (PaintingOrDrawing.drawing Γ₁) K θ T₁ ins ∧
      (∀ x ∈ Γ₁.A, ∀ y ∈ Γ₁.A, d₁ x y = tangleMetric Γ₁ K ins θ x y) ∧
      (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a_star ∈ Γ₁.A, ∀ b_star ∈ Γ₁.A,
        (a = b ↔ a_star = b_star) →
        (∀ x' : Set S, IsCorrespondingAtom Γ K a x' ↔ IsCorrespondingAtom Γ₁ K a_star x') →
        (∀ y' : Set S, IsCorrespondingAtom Γ K b y' ↔ IsCorrespondingAtom Γ₁ K b_star y') →
        d₁ a_star b_star = tangleMetric Γ K ins θ a b) := by
  have hθ_2 : 2 ≤ θ := by omega
  have hE : Γ.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hT.2.1 hθ_2
  have hloop : θ ≠ 2 ∨ (∀ e ∈ Γ.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ.V = {x, y}) ∧
      ∀ e ∈ Γ₁.E, ∃ x y, x ≠ y ∧ closure e ∩ Γ₁.V = {x, y} := Or.inl (by omega)
  obtain ⟨φ, hφ⟩ := GM11.theorem_6_6_proof hS hE hE₁ hK hK₁ hloop
  let T_sub : GM11.RespectfulTangle Γ θ := ⟨T, hT.2.1, hT.2.2⟩
  let T₁ := (φ T_sub).1
  have hT₁_tangle : GM10.IsTangle Γ₁.toHypergraph θ T₁ := (φ T_sub).2.1
  have hT₁_resp : (PaintingOrDrawing.drawing Γ₁).IsRespectful θ T₁ := (φ T_sub).2.2
  have hins₁ : IsDerivedSlope (PaintingOrDrawing.drawing Γ₁) K θ T₁ ins :=
    (hφ T_sub ins).mp hins
  let d₁ : Set S → Set S → ℕ := tangleMetric Γ₁ K ins θ
  have hd₁ : HasTangleMetric Γ₁ θ T₁ d₁ :=
    ⟨⟨hK₁.1, hT₁_tangle, hT₁_resp⟩, K, ins, hK₁, hins₁, fun _ _ _ _ => rfl⟩
  refine ⟨T₁, d₁, hd₁, hins₁, fun _ _ _ _ => rfl, ?_⟩
  intro a _ b _ a_star _ b_star _ heq ha hb
  exact tangleMetric_eq_of_correspondingAtom_iff heq ha hb

/-- In Case 2 of **(7.5)** (Graph Minors XII, page 265, line 663):
if `Γ'` is a subdrawing of `Γ \ Z`, `r ∈ R(Γ)`, `r' ∈ R(Γ')`, and `r ⊆ r'`, then
`Z = {v ∈ V(Γ) | v ∈ closure r} ⊆ r'`. -/
theorem incident_vertices_subset_region_of_region_subset {Γ Γ' : Drawing S} {r r' : Set S}
    (hr : r ∈ Γ.R) (hr' : r' ∈ Γ'.R)
    (hSub' : Γ'.IsSubdrawing (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}))
    (hrr' : r ⊆ r') :
    {v ∈ Γ.V | v ∈ closure r} ⊆ r' := by
  have ⟨hSubΓ, hDisjZ⟩ := isSubdrawing_deleteVertices_iff.mp hSub'
  rintro v ⟨hvV, hvr⟩
  have hv_not_U' : v ∉ Γ'.U := by
    intro hvU'
    have hvV' : v ∈ Γ'.V := (isSubdrawing_U_inter_V hSubΓ).subset ⟨hvU', hvV⟩
    exact disjoint_left.mp hDisjZ hvV' ⟨hvV, hvr⟩
  have hr_conn : IsPreconnected r := region_isPreconnected hr
  have hrv_conn : IsPreconnected (r ∪ {v}) :=
    hr_conn.subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.mpr hvr))
  obtain ⟨x₀, hx₀r⟩ := region_nonempty hr
  have hrv_off : r ∪ {v} ⊆ univ \ Γ'.U := by
    rintro y (hyr | hyv)
    · exact ⟨mem_univ y, region_subset hr' (hrr' hyr)⟩
    · rcases mem_singleton_iff.mp hyv with rfl
      exact ⟨mem_univ y, hv_not_U'⟩
  have hsub_comp := hrv_conn.subset_connectedComponentIn (Or.inl hx₀r) hrv_off
  have hcomp_R : connectedComponentIn (univ \ Γ'.U) x₀ ∈ Γ'.R :=
    (mem_R_iff Γ').mpr ⟨x₀, (hrv_off (Or.inl hx₀r)).2, rfl⟩
  have hcomp_eq : connectedComponentIn (univ \ Γ'.U) x₀ = r' :=
    atom_eq_of_inter_nonempty (Or.inr hcomp_R) (Or.inr hr')
      ⟨x₀, mem_connectedComponentIn (hrv_off (Or.inl hx₀r)), hrr' hx₀r⟩
  exact hcomp_eq ▸ hsub_comp (Or.inr rfl)

/-- In Case 2 of **(7.5)** (Graph Minors XII, page 265, lines 663–664):
since `Z ⊆ r'`, every edge of `Γ` incident with a member of `Z` is included in `r'`. -/
theorem incident_edge_subset_region_of_vertex_mem {Γ Γ' : Drawing S} {Z r' e : Set S} {z : S}
    (hr' : r' ∈ Γ'.R) (hSub' : Γ'.IsSubdrawing (deleteVertices Γ Z))
    (he : e ∈ Γ.E) (hzV : z ∈ Γ.V) (hzZ : z ∈ Z) (hze : z ∈ closure e) (hZr' : Z ⊆ r') :
    e ⊆ r' := by
  have ⟨hSubΓ, _⟩ := isSubdrawing_deleteVertices_iff.mp hSub'
  have he_not_del : e ∉ (deleteVertices Γ Z).E := by
    rw [deleteVertices_E]
    intro ⟨_, hdisj⟩
    exact disjoint_left.mp hdisj ⟨hze, hzV⟩ hzZ
  have he_not_E' : e ∉ Γ'.E := fun he' => he_not_del (hSub'.2 he')
  have he_disj_U' : Disjoint e Γ'.U := by
    rw [disjoint_iff_inter_eq_empty]
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxe hxU'
    by_cases hxV' : x ∈ Γ'.V
    · exact (he.2.1 hxe).2 (hSubΓ.1 hxV')
    · obtain ⟨e', he', hxe'⟩ := Γ'.exists_edge_of_mem hxU' hxV'
      have heq : e = e' := atom_eq_of_inter_nonempty (Or.inl (Or.inr he))
        (Or.inl (Or.inr (hSubΓ.2 he'))) ⟨x, hxe, hxe'⟩
      exact he_not_E' (heq ▸ he')
  have he_conn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  have hez_conn : IsPreconnected (e ∪ {z}) :=
    he_conn.subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.mpr hze))
  have hzr' : z ∈ r' := hZr' hzZ
  have hez_off : e ∪ {z} ⊆ univ \ Γ'.U := by
    rintro y (hye | hyz)
    · exact ⟨mem_univ y, disjoint_left.mp he_disj_U' hye⟩
    · rcases mem_singleton_iff.mp hyz with rfl
      exact ⟨mem_univ y, region_subset hr' hzr'⟩
  have hsub_comp := hez_conn.subset_connectedComponentIn (Or.inr rfl) hez_off
  have hcomp_R : connectedComponentIn (univ \ Γ'.U) z ∈ Γ'.R :=
    (mem_R_iff Γ').mpr ⟨z, (hez_off (Or.inr rfl)).2, rfl⟩
  have hcomp_eq : connectedComponentIn (univ \ Γ'.U) z = r' :=
    atom_eq_of_inter_nonempty (Or.inr hcomp_R) (Or.inr hr')
      ⟨z, mem_connectedComponentIn (hez_off (Or.inr rfl)), hzr'⟩
  exact subset_union_left.trans (hcomp_eq ▸ hsub_comp)

/-- In Case 2 of **(7.5)** (Graph Minors XII, page 265, lines 663–669):
since `Z ⊆ r'`, every edge of `Γ` incident with a member of `Z` is included in `r'`, and by (vii)
`U(Γ \ Z) ⊆ U(Γ₃) ⊆ U(Γ') ∪ r'`; consequently `U(Γ) ⊆ U(Γ') ∪ r'`, proving `(i)`. -/
theorem U_subset_of_deleteVertices_U_subset {Γ Γ' : Drawing S} {r r' : Set S}
    (hr : r ∈ Γ.R) (hr' : r' ∈ Γ'.R)
    (hSub' : Γ'.IsSubdrawing (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}))
    (hrr' : r ⊆ r')
    (hU_del : (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).U ⊆ Γ'.U ∪ r') :
    Γ.U ⊆ Γ'.U ∪ r' := by
  let Z := {v ∈ Γ.V | v ∈ closure r}
  have hZr' : Z ⊆ r' := incident_vertices_subset_region_of_region_subset hr hr' hSub' hrr'
  intro x hxU
  by_cases hxV : x ∈ Γ.V
  · by_cases hxZ : x ∈ Z
    · exact Or.inr (hZr' hxZ)
    · have hx_del : x ∈ (deleteVertices Γ Z).V := by
        rw [deleteVertices_V]
        exact ⟨hxV, hxZ⟩
      exact hU_del ((deleteVertices Γ Z).V_subset_U hx_del)
  · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
    by_cases hdisj : Disjoint (closure e ∩ Γ.V) Z
    · have he_del : e ∈ (deleteVertices Γ Z).E := by
        rw [deleteVertices_E]
        exact ⟨he, hdisj⟩
      exact hU_del ((he_del.2.1 hxe).1)
    · rw [not_disjoint_iff] at hdisj
      obtain ⟨z, ⟨hze, hzV⟩, hzZ⟩ := hdisj
      exact Or.inr (incident_edge_subset_region_of_vertex_mem hr' hSub' he hzV hzZ hze hZr' hxe)

/-- In Case 2 of **(7.5)** (Graph Minors XII, page 265, line 669):
for any shared atom `a ∈ A(Γ) ∩ A(Γ')`, we have `a ∩ r' = ∅` (and hence `a ∩ r = ∅`). -/
theorem theorem_7_5_disjoint_region_of_shared_atom [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ Γ' : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {r r' : Set S} (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    (hr : r ∈ Γ.R) (hr' : r' ∈ Γ'.R)
    (hSub' : Γ'.IsSubdrawing (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}))
    (hrr' : r ⊆ r') {a : Set S} (ha : a ∈ Γ.A ∩ Γ'.A) :
    Disjoint a r' ∧ Disjoint a r := by
  have hE : Γ.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hT.2.1 hθ
  obtain ⟨z, hzV, hzr⟩ := exists_vertex_at_region hS hE hr
  have hz_r' : z ∈ r' :=
    incident_vertices_subset_region_of_region_subset hr hr' hSub' hrr' ⟨hzV, hzr⟩
  obtain ⟨x₀, hx₀r⟩ := region_nonempty hr
  have hx₀r' : x₀ ∈ r' := hrr' hx₀r
  have har' : Disjoint a r' := by
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne
    obtain ⟨x, hxa, hxr'⟩ := nonempty_iff_ne_empty.mpr hne
    have har'_eq : a = r' := atom_eq_of_inter_nonempty ha.2 (Or.inr hr') ⟨x, hxa, hxr'⟩
    have hza : z ∈ a := har'_eq.symm ▸ hz_r'
    have haz_eq : a = {z} := atom_eq_of_inter_nonempty ha.1 (Or.inl (Or.inl ⟨z, hzV, rfl⟩))
      ⟨z, hza, rfl⟩
    have hx₀_a : x₀ ∈ a := har'_eq.symm ▸ hx₀r'
    have har_eq : a = r := atom_eq_of_inter_nonempty ha.1 (Or.inr hr) ⟨x₀, hx₀_a, hx₀r⟩
    have hzr_mem : z ∈ r := har_eq ▸ haz_eq ▸ mem_singleton z
    exact region_subset hr hzr_mem (Γ.V_subset_U hzV)
  exact ⟨har', Disjoint.mono_right hrr' har'⟩

/-- In Case 2 of **(7.5)** (Graph Minors XII, page 265, lines 652–669):
applying **(7.4)** (`Theorem74Statement`) to `(Γ₃, θ - 1, T₃, d₃, r₂_star)` where
`r₂_star ∈ V(Γ₃) ∩ r` and `Γ₃ \ {r₂_star} = Γ \ Z` yields a 2-cell subdrawing `Γ'` of `Γ \ Z`,
a respectful tangle `T'` of order `θ - 2` in `Γ'` with metric `d'`, and the region `r' ∈ R(Γ')`
including `r` such that `(i)` `U(Γ) ⊆ U(Γ') ∪ r'` and the bounds `(viii)`, `(ix)`, `(x)` of line
654 hold. -/
theorem theorem_7_5_apply_7_4 [ConnectedSpace S]
    (hS : IsClosedSurface S)
    {Γ Γ₃ : Drawing S} {θ : ℕ}
    {T₃ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d₃ : Set S → Set S → ℕ} {r : Set S} {r₂_star : S}
    (hθ : 3 ≤ θ) (hr : r ∈ Γ.R)
    (hd₃ : HasTangleMetric Γ₃ (θ - 1) T₃ d₃)
    (hr₂_V : r₂_star ∈ Γ₃.V) (hr₂_r : r₂_star ∈ r)
    (hdel_eq : deleteVertices Γ₃ {r₂_star} = deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}) :
    ∃ (Γ' : Drawing S)
      (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r' : Set S),
      Γ'.IsSubdrawing (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}) ∧
      (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
      HasTangleMetric Γ' (θ - 2) T' d' ∧
      r' ∈ Γ'.R ∧ r ⊆ r' ∧
      Γ.U ⊆ Γ'.U ∪ r' ∧
      (∀ a ∈ Γ₃.A ∩ Γ'.A, ∀ b ∈ Γ₃.A ∩ Γ'.A, d₃ a b - 2 ≤ d' a b) ∧
      (∀ a ∈ Γ₃.A ∩ Γ'.A, d₃ a {r₂_star} - 1 ≤ d' a r') ∧
      (∀ a ∈ Γ₃.A, a ⊆ r' → d₃ a {r₂_star} ≤ 2) := by
  have hθ_3 : 2 ≤ θ - 1 := by omega
  obtain ⟨Γ', T', d', r', hSub'₃, htwo', hd', hr', hr₂_r', hU₃, hii₃, hiii₃, hiv₃⟩ :=
    gm12_theorem_7_4 S hS Γ₃ (θ - 1) T₃ d₃ r₂_star hθ_3 hd₃ hr₂_V
  have hSub' : Γ'.IsSubdrawing (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}) :=
    hdel_eq ▸ hSub'₃
  have hSub_Γ'Γ : Γ'.IsSubdrawing Γ :=
    hSub'.trans (deleteVertices_isSubdrawing Γ _)
  have hrr' : r ⊆ r' :=
    region_subset_region_of_inter_nonempty hSub_Γ'Γ hr hr' ⟨r₂_star, hr₂_r, hr₂_r'⟩
  have hU_del : (deleteVertices Γ {v ∈ Γ.V | v ∈ closure r}).U ⊆ Γ'.U ∪ r' := by
    rw [← hdel_eq]
    exact (deleteVertices_isSubdrawing Γ₃ {r₂_star}).U_subset.trans hU₃
  have hU_Γ : Γ.U ⊆ Γ'.U ∪ r' :=
    U_subset_of_deleteVertices_U_subset hr hr' hSub' hrr' hU_del
  have hθ_eq : θ - 1 - 1 = θ - 2 := by omega
  have hd'_θ : HasTangleMetric Γ' (θ - 2) T' d' := hθ_eq ▸ hd'
  exact ⟨Γ', T', d', r', hSub', htwo', hd'_θ, hr', hrr', hU_Γ, hii₃, hiii₃, hiv₃⟩

end GraphMinor.GM12
