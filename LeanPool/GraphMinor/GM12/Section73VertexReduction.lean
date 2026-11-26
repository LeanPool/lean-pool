/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72
public import LeanPool.GraphMinor.GM12.Section73DiscPreprocess
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM07.Section3

/-!
# Finite selected-disc reduction before vertex contraction

To correct the parallel-spoke claim in XII (7.3), page 261, repeatedly
apply (7.2) while a selected one-vertex inside contains an old edge.
The deleted drawing does not change and the number of edges drops.
Choose a drawing with the fewest edges among these reductions.
Both metric comparisons are retained by transitivity. This supplies
the reduced case with no extra assumption in the original problem.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

variable {S : Type*} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- An atom shared by the first and last drawings in a chain of
subdrawings is an atom of the intermediate drawing as well. -/
theorem shared_atom_mem_intermediate {Γ K H : Drawing S}
    (hK : K.IsSubdrawing Γ) (hH : H.IsSubdrawing K) {a : Set S}
    (haΓ : a ∈ Γ.A) (haH : a ∈ H.A) : a ∈ K.A := by
  obtain ⟨b, hb, hab⟩ := exists_atom_superset_of_isSubdrawing hK haΓ
  obtain ⟨c, hc, hbc⟩ := exists_atom_superset_of_isSubdrawing hH hb
  obtain ⟨x, hxa⟩ := atom_nonempty' haH
  have hac : a = c := atom_eq_of_inter_nonempty haH hc ⟨x, hxa, hbc (hab hxa)⟩
  have habEq : a = b := Subset.antisymm hab (hbc.trans hac.symm.subset)
  exact habEq.symm ▸ hb

omit [T2Space S] in
/-- The punctured normal circle through one old vertex lies in a
single region, the region used when applying XII (7.2). -/
theorem exists_region_of_normal_circle_single_vertex {Γ : Drawing S} {F : Set S} {v : S}
    (hF : IsOArc F) (hn : (PaintingOrDrawing.drawing Γ).IsNormal F)
    (hFV : F ∩ Γ.V = {v}) : ∃ r ∈ Γ.R, F \ {v} ⊆ r := by
  have hvF : v ∈ F := (hFV.symm ▸ mem_singleton v).1
  have hpath := isPathConnected_oArc_diff hF hvF
  have hdis : Disjoint (F \ {v}) Γ.U := by
    apply disjoint_left.mpr
    rintro x ⟨hxF, hxv⟩ hxΓ
    exact hxv (hFV.subset ⟨hxF, hn ⟨hxF, hxΓ⟩⟩)
  obtain ⟨x, hx⟩ := hpath.nonempty
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp hdis hx)
  exact ⟨r, hr, subset_region hr hpath.isConnected.isPreconnected hdis hx hxr⟩

/-- Remove selected one-vertex insides until none contains an edge.
The deleted drawing stays fixed, and distances between shared atoms
do not decrease. This is the preprocessing correction for XII (7.3). -/
theorem exists_vertex_reduction [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell) :
    ∃ (Γ₀ : Drawing S) (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₀ : Set S → Set S → ℕ),
      Γ₀.IsSubdrawing Γ ∧ v ∈ Γ₀.V ∧ deleteVertices Γ₀ {v} = deleteVertices Γ {v} ∧
      HasTangleMetric Γ₀ θ T₀ d₀ ∧
      (∀ a ∈ Γ.A ∩ Γ₀.A, ∀ b ∈ Γ.A ∩ Γ₀.A, d a b ≤ d₀ a b) ∧
      (∀ D F : Set S, IsClosedDisc D → IsOArc F → subBd D = F →
        (PaintingOrDrawing.drawing Γ₀).IsNormal F → F ∩ Γ₀.V = {v} →
        ((PaintingOrDrawing.drawing Γ₀).inter D, (PaintingOrDrawing.drawing Γ₀).interOutside D) ∈
          T₀ →
        ∀ e ∈ Γ₀.E, ¬ e ⊆ D) := by
  classical
  have hex : ∃ n : ℕ, ∃ (K : Drawing S)
      (U : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (δ : Set S → Set S → ℕ),
      K.IsSubdrawing Γ ∧ v ∈ K.V ∧ deleteVertices K {v} = deleteVertices Γ {v} ∧
      HasTangleMetric K θ U δ ∧
      (∀ a ∈ Γ.A ∩ K.A, ∀ b ∈ Γ.A ∩ K.A, d a b ≤ δ a b) ∧ K.E.ncard = n :=
    ⟨Γ.E.ncard, Γ, T, d, Drawing.IsSubdrawing.refl Γ, hv, rfl, hd,
      fun _ _ _ _ => le_rfl, rfl⟩
  obtain ⟨Γ₀, T₀, d₀, hΓ₀, hv₀, hdelete₀, hd₀, hcomp₀, hcount⟩ := Nat.find_spec hex
  refine ⟨Γ₀, T₀, d₀, hΓ₀, hv₀, hdelete₀, hd₀, hcomp₀, ?_⟩
  intro D F hD hF hbd hn hFV hm e he heD
  obtain ⟨r, hr, hFr⟩ := exists_region_of_normal_circle_single_vertex hF hn hFV
  obtain ⟨_, _, d₁, r₁, hd₁, _, _, hcomp₁, _⟩ :=
    theorem_7_2_proof hS hθ hd₀ hD hbd hn hFV hr hFr hm
  let Γ₁ := Γ₀.interSet (closure (univ \ D))
  let T₁ := restrictTangle T₀ Γ₁.toHypergraph
  have hΓ₁ : Γ₁.IsSubdrawing Γ₀ := Drawing.span_isSubdrawing Γ₀ _ _
  have hfront : frontier D = F := (subBd_eq_frontier D).symm.trans hbd
  have hvF : v ∈ F := (hFV.symm ▸ mem_singleton v).1
  have hv₁ : v ∈ Γ₁.V := by
    have hvFront : v ∈ frontier D := hfront.symm ▸ hvF
    rw [frontier_eq_closure_inter_closure] at hvFront
    exact (mem_interSet_V_iff isClosed_closure).mpr
      ⟨hv₀, by simpa only [compl_eq_univ_sdiff] using hvFront.2⟩
  have htwo₀ : (PaintingOrDrawing.drawing (deleteVertices Γ₀ {v})).IsTwoCell := by
    rw [hdelete₀]
    exact htwo
  have hdelete₁ : deleteVertices Γ₁ {v} = deleteVertices Γ {v} :=
    (selected_disc_restriction_delete_vertex_eq hS hd₀.1.2.1 htwo₀ hD hbd hn hFV hm).trans hdelete₀
  have hcomp : ∀ a ∈ Γ.A ∩ Γ₁.A, ∀ b ∈ Γ.A ∩ Γ₁.A, d a b ≤ d₁ a b := by
    intro a ha b hb
    have ha₀ := shared_atom_mem_intermediate hΓ₀ hΓ₁ ha.1 ha.2
    have hb₀ := shared_atom_mem_intermediate hΓ₀ hΓ₁ hb.1 hb.2
    exact (hcomp₀ a ⟨ha.1, ha₀⟩ b ⟨hb.1, hb₀⟩).trans (hcomp₁ a ⟨ha₀, ha.2⟩ b ⟨hb₀, hb.2⟩)
  have hless : Γ₁.E.ncard < Γ₀.E.ncard := ncard_edges_outside_lt_of_edge_inside
    (fun x hx => hn ⟨hfront ▸ hx.1, hx.2⟩) he heD
  have hminimal : Nat.find hex ≤ Γ₁.E.ncard := Nat.find_min' hex
    ⟨Γ₁, T₁, d₁, hΓ₁.trans hΓ₀, hv₁, hdelete₁, hd₁, hcomp, rfl⟩
  rw [← hcount] at hminimal
  exact (Nat.not_le_of_lt hless) hminimal

end GraphMinor.GM12
