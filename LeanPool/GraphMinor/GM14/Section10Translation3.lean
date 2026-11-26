/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section10Translation2
public import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM12.Section2
import LeanPool.GraphMinor.GM12.Section1
import LeanPool.GraphMinor.GM11.Section64
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# Graph Minors XIV – Section 10 Translation (Part 3: Tangle Metric vs. Curve Distance Bounds)

This file proves the two curve-enclosure translation lemmas for Graph Minors XIV (1.1):
1. **Lemma 4 (`not_exists_curve_of_dist_gt_three`):** If `d {u} {v} > 3` for `u, v ∈ V(H)`, then
   there is no `H`-normal `O`-arc `φ : C(Circle, S)` meeting `H.U` at most 3 times with
   `u, v ∈ curveIns φ`.
2. **Lemma 5a (`exists_curve_le_39_of_mem_lambdaZone`):** If `Λ₀` is a `39`-zone around `z ∈ H.A`
   in `H` with `subBd Λ₀ = C.U` for a circuit `C` of `H`, then there exists `x ∈ Λ₀` such that for
   every `y ∈ Λ₀`, there is a closed curve `φ : C(Circle, S)` meeting `H.U` at most 39 times with
   `x ∈ curveIns φ` and `y ∈ curveIns φ`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Metric unitInterval Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14.Whitney

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Monotonicity of `curveIns` and Inclusion of `insWalk` in `curveIns` -/

omit [T2Space S] in
/-- If `range φ ⊆ range ψ`, then `curveIns φ ⊆ curveIns ψ`. -/
theorem curveIns_mono {φ ψ : C(Circle, S)} (hsub : range φ ⊆ range ψ) :
    curveIns φ ⊆ curveIns ψ := by
  rintro x (hx | hx)
  · exact Or.inl (hsub hx)
  · obtain ⟨Δ, ⟨hΔ, hbd⟩, hxΔ⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion₂.mpr ⟨Δ, ⟨hΔ, hbd.trans hsub⟩, hxΔ⟩)

omit [T2Space S] in
/-- If `range φ = range ψ`, then `curveIns φ = curveIns ψ`. -/
theorem curveIns_eq_of_range_eq {φ ψ : C(Circle, S)} (heq : range φ = range ψ) :
    curveIns φ = curveIns ψ :=
  Subset.antisymm (curveIns_mono heq.subset) (curveIns_mono heq.superset)

/-- For a closed walk `W` of length `< 2 * θ` in a radial drawing `K` with derived slope `ins`,
any curve `φ : C(Circle, S)` with `range φ = (walkDrawing K W).U` satisfies
`insWalk ins K W ⊆ curveIns φ`. -/
theorem insWalk_subset_curveIns {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hslope : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    {u : S} {W : GraphWalk K.toGraph u u} (hW_lt : W.length < 2 * θ)
    {φ : C(Circle, S)} (hran : range φ = (walkDrawing K W).U) :
    insWalk ins K W ⊆ curveIns φ := by
  classical
  have hLs : (walkDrawing K W).IsSubdrawing K := walkDrawing_isSubdrawing K W
  rintro x (hxU | hxC)
  · exact Or.inl (hran.symm ▸ hxU)
  · obtain ⟨C, ⟨hC, hCs⟩, hx_ins⟩ := mem_iUnion₂.mp hxC
    have hlen : C.length < 2 * θ := by
      refine lt_of_le_of_lt ?_ hW_lt
      have hsub : C.E ⊆ {e | e ∈ W.edges} := by
        have := hCs.2
        rwa [walkDrawing_E] at this
      calc C.E.ncard ≤ ({e | e ∈ W.edges} : Set (Set S)).ncard :=
            Set.ncard_le_ncard hsub (List.finite_toSet _)
        _ ≤ W.edges.length := by
            rw [show ({e | e ∈ W.edges} : Set (Set S)) = ↑W.edges.toFinset by ext; simp,
              Set.ncard_coe_finset]
            exact List.toFinset_card_le _
        _ = W.length := rfl
    obtain ⟨hdisc, hbd, -⟩ := hslope C hC (hCs.trans hLs) hlen
    refine Or.inr (mem_iUnion₂.mpr ⟨ins C, ⟨hdisc, ?_⟩, hx_ins⟩)
    rw [hbd, hran]
    exact hCs.U_subset

/-! ## 2. Lemma 4: `d {u} {v} > 3` Precludes a 3-Hit Normal `O`-Arc Enclosing `u` and `v` -/

/-- **Lemma 4 (`not_exists_curve_of_dist_gt_three`):** Let `H` be a drawing in a connected closed
non-spherical surface `S` with a respectful tangle `T` of order `θ ≥ 4` and metric `d`. If
`u, v ∈ H.V` satisfy `¬ d {u} {v} ≤ 3`, then there is no `φ : C(Circle, S)` such that `range φ` is
an `H`-normal `O`-arc with `(range φ ∩ H.U).ncard ≤ 3`, `u ∈ curveIns φ`, and `v ∈ curveIns φ`. -/
theorem not_exists_curve_of_dist_gt_three [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hθ : 4 ≤ θ) (hd : HasTangleMetric H θ T d)
    {u v : S} (hu : u ∈ H.V) (hv : v ∈ H.V) (hdist : ¬ d {u} {v} ≤ 3) :
    ¬ ∃ φ : C(Circle, S),
      IsOArc (range φ) ∧ H.IsNormal (range φ) ∧
      (range φ ∩ H.U).ncard ≤ 3 ∧ u ∈ curveIns φ ∧ v ∈ curveIns φ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rintro ⟨φ, hO, hnorm, hcard, hu_ins, hv_ins⟩
  obtain ⟨hResp, K, ins, hrad, hslope, hd_eq⟩ := id hd
  have hVU_eq : range φ ∩ H.V = range φ ∩ H.U :=
    Subset.antisymm (inter_subset_inter_right _ H.V_subset_U) (fun x hx => ⟨hx.1, hnorm hx⟩)
  have hcard_V : (range φ ∩ H.V).ncard ≤ 3 := hVU_eq.symm ▸ hcard
  obtain ⟨ψ, hranψ, hnormψ, hlenψ⟩ := GM12.exists_closedCurve_of_isOArc hO hnorm
  have hlenψ_le : GM12.curveLength H ψ ≤ 3 := hlenψ ▸ hcard_V
  have hlenψ_lt : GM12.curveLength H ψ < θ := by omega
  have h21_app := GM12.theorem_2_1_statement S hS H K θ T ins hrad hResp.2.1.one_le
    hResp.2.1 hResp.2.2 hslope ψ hnormψ hlenψ_lt
  obtain ⟨⟨w₀, W, htr⟩, h21_prop⟩ := h21_app
  obtain ⟨hW_lt, h21_disc⟩ := h21_prop w₀ W htr
  have hW_len : W.length = 2 * GM12.curveLength H ψ := by
    rcases htr.2 with ⟨h0, hW0, -⟩ | ⟨-, hW2, -⟩
    · rw [h0, hW0]
    · exact hW2
  have hmeet_of_ins : ∀ x ∈ H.V, x ∈ curveIns φ → ({x} ∩ insWalk ins K W).Nonempty := by
    intro x hxV hx_ins
    have hxA : ({x} : Set S) ∈ H.A := Or.inl (Or.inl ⟨x, hxV, rfl⟩)
    rcases hx_ins with hx_ran | hx_disc
    · obtain ⟨y, hyx, hyU⟩ :=
        GM12.meets_walkDrawing_of_isTrace htr hxA ⟨x, rfl, hranψ.symm ▸ hx_ran⟩
      exact ⟨y, hyx, Or.inl hyU⟩
    · obtain ⟨Δ, ⟨hΔ, hbd_sub⟩, hxΔ⟩ := mem_iUnion₂.mp hx_disc
      let F : Set S := subBd Δ
      have hbd_eq : subBd Δ = discBd Δ := IsClosedDisc.subBd_eq_discBd hS hΔ
      have hF_oarc : IsOArc F := by
        change IsOArc (subBd Δ)
        rw [hbd_eq]
        exact hΔ.isOArc_discBd
      have hF_norm : H.IsNormal F := fun z hz => hnorm ⟨hbd_sub hz.1, hz.2⟩
      have hFV_sub : F ∩ H.V ⊆ range φ ∩ H.V := inter_subset_inter_left _ hbd_sub
      have hFV_lt : (F ∩ H.V).ncard < θ := by
        have hle := Set.ncard_le_ncard hFV_sub (H.finite_V.subset inter_subset_right)
        omega
      obtain ⟨Δ', hΔ'_disc, hbdΔ', hΔ'_memT⟩ := hResp.2.2.2 F hF_oarc hF_norm hFV_lt
      have hbdΔ'_eq : discBd Δ' = discBd Δ :=
        (IsClosedDisc.subBd_eq_discBd hS hΔ'_disc).symm.trans (hbdΔ'.trans hbd_eq)
      have hΔ_eq : Δ = Δ' :=
        eq_of_discBd_eq (IsClosedSurface.isSurface hS) hns hΔ hΔ'_disc hbdΔ'_eq.symm
      have hΔ_memT :
          ((PaintingOrDrawing.drawing H).inter Δ,
            (PaintingOrDrawing.drawing H).interOutside Δ) ∈ T := hΔ_eq ▸ hΔ'_memT
      exact h21_disc {x} hxA F Δ hF_oarc (hranψ.symm ▸ hbd_sub) hΔ rfl hΔ_memT ⟨x, rfl, hxΔ⟩
  have huW := hmeet_of_ins u hu hu_ins
  have hvW := hmeet_of_ins v hv hv_ins
  have huA : ({u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hd_le : d {u} {v} ≤ 3 := by
    by_cases huv : ({u} : Set S) = {v}
    · rw [huv, GM12.metric_self hd hvA]
      omega
    · obtain ⟨u_K, hu_K, -⟩ := GM12.existsUnique_correspondingAtom' hrad huA
      obtain ⟨v_K, hv_K, -⟩ := GM12.existsUnique_correspondingAtom' hrad hvA
      have hu_sub : u_K ⊆ insWalk ins K W :=
        (GM12.corresponding_atom_subset_iff hS hrad hslope hu_K W hW_lt).mpr huW
      have hv_sub : v_K ⊆ insWalk ins K W :=
        (GM12.corresponding_atom_subset_iff hS hrad hslope hv_K W hW_lt).mpr hvW
      have hwit : GM11.MetricWitness H K ins θ {u} {v} (GM12.curveLength H ψ) :=
        ⟨w₀, W, u_K, v_K, hu_K, hv_K, hW_lt, hW_len, hu_sub, hv_sub⟩
      rw [hd_eq {u} huA {v} hvA]
      exact (GM11.tangleMetric_le hwit).trans hlenψ_le
  exact hdist hd_le

/-! ## 3. Constructing Closed Curves from Radial Walks and Appending Region Paths -/

omit [T2Space S] in
/-- Any closed path `p : Path u u` in `S` lifts to a continuous closed curve `φ : C(Circle, S)`
with `range φ = range p`. -/
theorem exists_closedCurve_of_loop {u : S} (p : Path u u) :
    ∃ φ : C(Circle, S), range φ = range p := by
  obtain ⟨φ, hRange, _⟩ := GM12.exists_closedCurve_of_loop_with_parameter p
  exact ⟨φ, hRange⟩

omit [T2Space S] in
/-- Given any closed curve `φ : C(Circle, S)`, a point `z₀ : Circle`, and a path `γ : Path (φ z₀)
y`,
there is a closed curve `φ' : C(Circle, S)` with `range φ' = range φ ∪ range γ`. -/
theorem exists_closedCurve_union_path (φ : C(Circle, S)) (z₀ : Circle) {y : S}
    (γ : Path (φ z₀) y) :
    ∃ φ' : C(Circle, S), range φ' = range φ ∪ range γ := by
  let p₀ : Path (φ z₀) (φ z₀) :=
    { toFun := fun t => φ (z₀ * Circle.exp (2 * Real.pi * t.1))
      continuous_toFun :=
        φ.continuous.comp (continuous_const.mul
          (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)))
      source' := by simp
      target' := by simp [Circle.exp_two_pi] }
  have hran₀ : range p₀ = range φ := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact mem_range_self _
    · rintro ⟨z, rfl⟩
      obtain ⟨s, hs, hsz⟩ := (GM12.circle_parameter_bijOn 0).surjOn (mem_univ (z₀⁻¹ * z))
      rw [zero_add] at hs
      let t : unitInterval := ⟨s, hs.1, hs.2.le⟩
      have hsz' : Circle.exp (2 * Real.pi * s) = z₀⁻¹ * z := hsz
      refine ⟨t, ?_⟩
      change φ (z₀ * Circle.exp (2 * Real.pi * s)) = φ z
      rw [hsz', mul_inv_cancel_left]
  let p₁ : Path (φ z₀) (φ z₀) := p₀.trans (γ.trans γ.symm)
  obtain ⟨φ', hran'⟩ := exists_closedCurve_of_loop p₁
  refine ⟨φ', ?_⟩
  rw [hran', Path.trans_range, Path.trans_range, Path.symm_range, Set.union_self, hran₀]

omit [T2Space S] in
/-- Given a single radial link `K.toGraph.IsLink e u w`, there is a path `p : Path u w` with
`range p = closure e`. -/
private theorem exists_path_of_radial_link' {Γ K : Drawing S}
    (hrad : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {e : Set S} {u w : S} (hlink : K.toGraph.IsLink e u w) :
    ∃ p : Path u w, range p = closure e := by
  have heK : e ∈ K.E := hlink.1
  have hcap : closure e ∩ K.V = {u, w} := hlink.2.2.2
  obtain ⟨v₀, hv₀, w₀, hw₀, hcap₀⟩ := hrad.2.2.2.2.1 e heK
  have hpair : ({u, w} : Set S) = {v₀, w₀} := hcap.symm.trans hcap₀
  have hvw_ne : v₀ ≠ w₀ := fun h => hw₀.2 (h ▸ hv₀)
  have huw_ne : u ≠ w := by
    intro h
    subst h
    have hsing : ({v₀, w₀} : Set S) = {u} := by
      rw [← hpair, pair_eq_singleton]
    have hv₀_u : v₀ = u := mem_singleton_iff.mp (hsing ▸ mem_insert v₀ {w₀})
    have hw₀_u : w₀ = u := mem_singleton_iff.mp (hsing ▸ mem_insert_of_mem v₀ (mem_singleton w₀))
    exact hvw_ne (hv₀_u.trans hw₀_u.symm)
  have hline : IsLineWithEnds (closure e) u w := by
    rcases K.edge_cond e heK with ⟨u₁, w₁, _, hcap₁, hl₁⟩ | ⟨u₁, hcap₁, _⟩
    · have hp₁ : ({u, w} : Set S) = {u₁, w₁} := hcap.symm.trans hcap₁
      have hu₁ : u ∈ ({u₁, w₁} : Set S) := hp₁ ▸ mem_insert u {w}
      have hw₁ : w ∈ ({u₁, w₁} : Set S) := hp₁ ▸ mem_insert_of_mem u (mem_singleton w)
      rcases hu₁ with rfl | rfl <;> rcases hw₁ with rfl | rfl
      · exact (huw_ne rfl).elim
      · exact hl₁
      · exact hl₁.symm
      · exact (huw_ne rfl).elim
    · exfalso
      have hp₁ : ({u, w} : Set S) = {u₁} := hcap.symm.trans hcap₁
      have hu₁ : u = u₁ := mem_singleton_iff.mp (hp₁ ▸ mem_insert u {w})
      have hw₁ : w = u₁ := mem_singleton_iff.mp (hp₁ ▸ mem_insert_of_mem u (mem_singleton w))
      exact huw_ne (hu₁.trans hw₁.symm)
  obtain ⟨a, ha, hran, ha0, ha1⟩ := hline.exists_arc
  exact ⟨⟨⟨a, ha.1⟩, ha0, ha1⟩, hran⟩

/-- Every walk `W` of positive length in a radial drawing `K` is traced by a continuous path
`p : Path u v` with `range p = (walkDrawing K W).U`. -/
private theorem exists_path_of_radial_walk' {Γ K : Drawing S}
    (hrad : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {u v : S} (W : GraphWalk K.toGraph u v) (hpos : 0 < W.length) :
    ∃ p : Path u v, range p = (walkDrawing K W).U := by
  induction W with
  | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hpos
  | @cons u w v e hlink rest ih =>
    obtain ⟨p₁, hran₁⟩ := exists_path_of_radial_link' hrad hlink
    cases hrest : rest with
    | nil hw =>
      subst hrest
      have hU : (walkDrawing K (.cons hlink (.nil hw))).U = closure e := by
        have hV : (walkDrawing K (.cons hlink (.nil hw))).V = {u, w} := by
          rw [walkDrawing_V]
          ext x
          simp [GraphWalk.support]
        have hE : (walkDrawing K (.cons hlink (.nil hw))).E = {e} := by
          rw [walkDrawing_E]
          ext f
          simp [GraphWalk.edges]
        rw [Drawing.U_eq, hV, hE, biUnion_singleton]
        refine Subset.antisymm (union_subset ?_ subset_rfl) subset_union_right
        rw [← hlink.2.2.2]
        exact inter_subset_left
      exact ⟨p₁, hran₁.trans hU.symm⟩
    | cons hl₂ rest₂ =>
      subst hrest
      have hpos₂ : 0 < (GraphWalk.cons hl₂ rest₂).length := by
        simp [GraphWalk.length, GraphWalk.edges]
      obtain ⟨p₂, hran₂⟩ := ih hpos₂
      refine ⟨p₁.trans p₂, ?_⟩
      rw [Path.trans_range, hran₁, hran₂]
      have hV : (walkDrawing K (.cons hlink (.cons hl₂ rest₂))).V =
          insert u (walkDrawing K (.cons hl₂ rest₂)).V := by
        rw [walkDrawing_V, walkDrawing_V]
        ext x
        simp [GraphWalk.support]
      have hE : (walkDrawing K (.cons hlink (.cons hl₂ rest₂))).E =
          insert e (walkDrawing K (.cons hl₂ rest₂)).E := by
        rw [walkDrawing_E, walkDrawing_E]
        ext f
        simp [GraphWalk.edges]
      have hu_cl : u ∈ closure e := by
        have : u ∈ closure e ∩ K.V := hlink.2.2.2 ▸ mem_insert u {w}
        exact this.1
      rw [Drawing.U_eq, Drawing.U_eq, hV, hE]
      ext x
      simp only [mem_union, mem_insert_iff, mem_iUnion, exists_prop]
      constructor
      · rintro (hx | hx | ⟨f, hf, hxf⟩)
        · exact Or.inr ⟨e, Or.inl rfl, hx⟩
        · exact Or.inl (Or.inr hx)
        · exact Or.inr ⟨f, Or.inr hf, hxf⟩
      · rintro ((rfl | hx) | ⟨f, rfl | hf, hxf⟩)
        · exact Or.inl hu_cl
        · exact Or.inr (Or.inl hx)
        · exact Or.inl hxf
        · exact Or.inr (Or.inr ⟨f, hf, hxf⟩)

/-- Every closed walk `W` of positive length `≤ 2 * m` in a radial drawing `K` of `Γ` is traced by
a closed curve `φ : C(Circle, S)` with `range φ = (walkDrawing K W).U` and
`(range φ ∩ Γ.U).encard ≤ m`. -/
theorem exists_closedCurve_of_radial_walk_ncard {Γ K : Drawing S}
    (hrad : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {u : S} (W : GraphWalk K.toGraph u u) (hpos : 0 < W.length)
    {m : ℕ} (hlen : W.length ≤ 2 * m) :
    ∃ φ : C(Circle, S),
      range φ = (walkDrawing K W).U ∧ (range φ ∩ Γ.U).encard ≤ m := by
  classical
  obtain ⟨p, hran⟩ := exists_path_of_radial_walk' hrad W hpos
  obtain ⟨φ, hranφ⟩ := exists_closedCurve_of_loop p
  have hran_W : range φ = (walkDrawing K W).U := hranφ.trans hran
  refine ⟨φ, hran_W, ?_⟩
  rw [hran_W, Set.encard_le_coe_iff_finite_ncard_le]
  have hsub_V : (walkDrawing K W).U ∩ Γ.U ⊆ {x | x ∈ W.support.tail ∧ x ∈ Γ.V} := by
    rintro x ⟨hxW, hxΓ⟩
    have hxV : x ∈ Γ.V := by
      have hrad1 : Γ.U ∩ K.U = Γ.V := hrad.1
      have : x ∈ Γ.U ∩ K.U := ⟨hxΓ, (walkDrawing_isSubdrawing K W).U_subset hxW⟩
      rwa [hrad1] at this
    have hxWV : x ∈ (walkDrawing K W).V := by
      by_cases h : x ∈ (walkDrawing K W).V
      · exact h
      · obtain ⟨e, he, hxe⟩ := (walkDrawing K W).exists_edge_of_mem hxW h
        have heK : e ∈ K.E := (walkDrawing_isSubdrawing K W).2 he
        exact absurd (hrad.2.1 hxV) ((heK.2.1 hxe).2)
    rw [walkDrawing_V] at hxWV
    refine ⟨?_, hxV⟩
    cases W with
    | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hpos
    | cons hl rest =>
      simp only [GraphWalk.support_cons, List.tail_cons, List.mem_cons] at hxWV ⊢
      rcases hxWV with rfl | hx_rest
      · exact rest.end_mem_support
      · exact hx_rest
  have hfin_supp : {x | x ∈ W.support.tail ∧ x ∈ Γ.V}.Finite :=
    (List.finite_toSet W.support.tail).subset fun x hx => hx.1
  refine ⟨hfin_supp.subset hsub_V, ?_⟩
  have hcard_le : ((walkDrawing K W).U ∩ Γ.U).ncard ≤
      (W.support.tail.filter (· ∈ Γ.V)).length := by
    calc ((walkDrawing K W).U ∩ Γ.U).ncard
      _ ≤ {x | x ∈ W.support.tail ∧ x ∈ Γ.V}.ncard := Set.ncard_le_ncard hsub_V hfin_supp
      _ = (W.support.tail.filter (· ∈ Γ.V)).toFinset.card := by
          rw [← Set.ncard_coe_finset]
          congr 1
          ext x
          simp
      _ ≤ (W.support.tail.filter (· ∈ Γ.V)).length := List.toFinset_card_le _
  -- Count bipartite alternations along `W` to show `2 * (filter length) ≤ W.length`
  have hb := GM11.bipartite_of_preRadial hrad
  have hcount : ∀ {a b : S} (W₀ : GraphWalk K.toGraph a b),
      2 * (W₀.support.tail.filter (· ∈ Γ.V)).length + (if b ∈ Γ.V then 0 else 1) ≤
        W₀.length + (if a ∈ Γ.V then 0 else 1) := by
    intro a b W₀
    induction W₀ with
    | nil _ => simp
    | @cons x y z e hl r ih =>
      have hx : x ∈ Γ.V ↔ y ∉ Γ.V := hb _ _ _ hl
      have hlen₀ : (GraphWalk.cons hl r).length = r.length + 1 := rfl
      have hsup₀ : (GraphWalk.cons hl r).support.tail = r.support := rfl
      rw [hlen₀, hsup₀, r.support_eq_cons, List.filter_cons]
      by_cases hy : y ∈ Γ.V
      · have hx' : x ∉ Γ.V := fun h => hx.mp h hy
        simp only [hy, hx', ite_true, ite_false, decide_true, List.length_cons] at ih ⊢
        omega
      · have hx' : x ∈ Γ.V := hx.mpr hy
        simp only [hy, hx', ite_true, ite_false, decide_false, Bool.false_eq_true] at ih ⊢
        omega
  have hcount_W := hcount W
  omega

/-! ## 4. Lemma 5a: 39-Zone Curve Enclosure (`(1.1)(iii)(ii)`) -/

/-- Every atom `a ∈ H.A` that meets a `λ`-zone `Λ` around `z` is contained in `Λ`. -/
theorem atom_subset_zone_of_inter_nonempty {H : Drawing S}
    {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ a : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ) (ha : a ∈ H.A) (hmeet : (a ∩ Λ).Nonempty) :
    a ⊆ Λ := by
  obtain ⟨y, hya, hyΛ⟩ := hmeet
  rcases ha with (⟨v, -, rfl⟩ | haE) | haR
  · rw [mem_singleton_iff.mp hya] at hyΛ
    exact singleton_subset_iff.mpr hyΛ
  · rcases edge_subset_or_subset_compl_of_zone hZone haE with hsub | hsub
    · exact hsub
    · exact absurd hyΛ (hsub hya).2
  · obtain ⟨_, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
    let O₂ : Set S := univ \ (H.U ∪ closure Λ)
    have hO₂ : IsOpen O₂ := isOpen_univ.sdiff (H.isClosed_U.union isClosed_closure)
    have hdisO : Disjoint Λ O₂ :=
      disjoint_left.mpr fun x hx hxO => hxO.2 (Or.inr (subset_closure hx))
    have hcov : a ⊆ Λ ∪ O₂ := by
      intro w hwa
      have hwU : w ∉ H.U := region_subset haR hwa
      by_cases hwcl : w ∈ closure Λ
      · rw [hclL] at hwcl
        exact Or.inl (hwcl.resolve_right fun hbd => hwU (hZone.bd_subset_U hbd))
      · exact Or.inr ⟨mem_univ _, fun h => h.elim hwU hwcl⟩
    exact (region_isPreconnected haR).subset_left_of_subset_union
      hZone.isOpenDisc.1 hO₂ hdisO hcov ⟨y, hya, hyΛ⟩

/-- **Lemma 5a (`exists_curve_le_39_of_mem_lambdaZone`):** Let `H` have tangle metric `d` of order
`θ ≥ 209`, and let `Λ₀` be a `lam`-zone around `z` in `H` (`lam ≤ 39`) whose boundary is a circuit
`C` of `H`. Then there exists `x ∈ Λ₀` such that for every `y ∈ Λ₀`, there is a closed curve
`φ : C(Circle, S)` with `(range φ ∩ H.U).encard ≤ lam`, `x ∈ curveIns φ`, and `y ∈ curveIns φ`. -/
theorem exists_curve_le_of_mem_lambdaZone
    (hS : IsClosedSurface S)
    {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hlam : lam < θ) (hd : HasTangleMetric H θ T d)
    {z Λ₀ : Set S} (hZone : IsLambdaZoneAround H d lam z Λ₀)
    {C : Drawing S} (hC_circ : C.IsCircuit) (hC_sub : C.IsSubdrawing H) (hC_bd : C.U = subBd Λ₀) :
    ∃ x ∈ Λ₀, ∀ y ∈ Λ₀,
      ∃ φ : C(Circle, S), (range φ ∩ H.U).encard ≤ lam ∧ x ∈ curveIns φ ∧ y ∈ curveIns φ := by
  classical
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hResp, K, ins, hrad, hslope, hd_eq⟩ := id hd
  obtain ⟨z', hz', -⟩ := GM12.existsUnique_correspondingAtom' hrad hZone.z_mem
  have hzz'_ne : (z ∩ z').Nonempty := by
    obtain ⟨-, -, hcase⟩ := hz'
    rcases hcase with ⟨v, -, rfl, rfl⟩ | ⟨he, _, hsub⟩ | ⟨_, v, hv, rfl⟩
    · exact ⟨v, rfl, rfl⟩
    · obtain ⟨w, hw⟩ := he.1
      exact ⟨w, hw, hsub hw⟩
    · exact ⟨v, hv.2, rfl⟩
  obtain ⟨x, hxz, hxz'⟩ := hzz'_ne
  refine ⟨x, hZone.z_subset hxz, fun y hyΛ => ?_⟩
  obtain ⟨a_y, ha_y, hya⟩ := GM11.exists_atom H y
  have hay_sub : a_y ⊆ Λ₀ := atom_subset_zone_of_inter_nonempty hZone ha_y ⟨y, hya, hyΛ⟩
  obtain ⟨ay', hay', -⟩ := GM12.existsUnique_correspondingAtom' hrad ha_y
  -- Find a partner atom `b ∈ H.A` with `b ⊆ closure Λ₀`, `z ≠ b`, `d z b ≤ lam`, and `ay' ⊆ ...`
  have hex_walk : ∃ (u₀ : S) (W : GraphWalk K.toGraph u₀ u₀),
      0 < W.length ∧ W.length < 2 * θ ∧ W.length ≤ 2 * lam ∧
      z' ⊆ insWalk ins K W ∧ ay' ⊆ insWalk ins K W := by
    by_cases hz_ay : z = a_y
    · subst hz_ay
      have hay'_eq : ay' = z' :=
        (GM12.existsUnique_correspondingAtom' hrad hZone.z_mem).unique hay' hz'
      rw [hay'_eq]
      obtain ⟨u_c, W_c, _, hpos_c, hVC, _⟩ := id hC_circ
      have hu_cV : u_c ∈ C.V := hVC ▸ W_c.start_mem_support
      have hu_H : u_c ∈ H.V := hC_sub.1 hu_cV
      have hu_bd : u_c ∈ subBd Λ₀ := hC_bd ▸ C.V_subset_U hu_cV
      obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
      have hu_cl : ({u_c} : Set S) ⊆ closure Λ₀ :=
        singleton_subset_iff.mpr (hclL ▸ Or.inr hu_bd)
      have hu_A : ({u_c} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u_c, hu_H, rfl⟩)
      have hzu_ne : z ≠ {u_c} := by
        intro h
        have hu_Λ : u_c ∈ Λ₀ := hZone.z_subset (h ▸ mem_singleton u_c)
        exact disjoint_left.mp hdisL hu_Λ hu_bd
      have hd_le : d z {u_c} ≤ lam := hZone.dist_le {u_c} hu_A hu_cl
      have hd_lt : d z {u_c} < θ := lt_of_le_of_lt hd_le hlam
      have hd_pos : 0 < d z {u_c} :=
        Nat.pos_of_ne_zero fun h0 => hzu_ne ((GM12.tangleMetric_eq_zero_iff hS hd hZone.z_mem
          hu_A).mp h0)
      have hd_zu : d z {u_c} = tangleMetric H K ins θ z {u_c} := hd_eq z hZone.z_mem {u_c} hu_A
      rcases GM11.tangleMetric_cases (ins := ins) (θ := θ) hrad.2.1 hzu_ne with h_eq_θ | ⟨_, hwit⟩
      · omega
      · rw [← hd_zu] at hwit
        obtain ⟨u₀, W, z₁', _, hz₁', _, hW_lt, hW_len, hz₁_sub, _⟩ := hwit
        have hz₁_eq : z₁' = z' :=
          (GM12.existsUnique_correspondingAtom' hrad hZone.z_mem).unique hz₁' hz'
        rw [hz₁_eq] at hz₁_sub
        refine ⟨u₀, W, by omega, hW_lt, by omega, hz₁_sub, hz₁_sub⟩
    · have hd_le : d z a_y ≤ lam :=
        hZone.dist_le a_y ha_y (hay_sub.trans subset_closure)
      have hd_lt : d z a_y < θ := lt_of_le_of_lt hd_le hlam
      have hd_pos : 0 < d z a_y :=
        Nat.pos_of_ne_zero fun h0 => hz_ay ((GM12.tangleMetric_eq_zero_iff hS hd hZone.z_mem
          ha_y).mp h0)
      have hd_za : d z a_y = tangleMetric H K ins θ z a_y := hd_eq z hZone.z_mem a_y ha_y
      rcases GM11.tangleMetric_cases (ins := ins) (θ := θ) hrad.2.1 hz_ay with h_eq_θ | ⟨_, hwit⟩
      · omega
      · rw [← hd_za] at hwit
        obtain ⟨u₀, W, z₁', ay₁', hz₁', hay₁', hW_lt, hW_len, hz₁_sub, hay₁_sub⟩ := hwit
        have hz₁_eq : z₁' = z' :=
          (GM12.existsUnique_correspondingAtom' hrad hZone.z_mem).unique hz₁' hz'
        have hay₁_eq : ay₁' = ay' :=
          (GM12.existsUnique_correspondingAtom' hrad ha_y).unique hay₁' hay'
        rw [hz₁_eq] at hz₁_sub
        rw [hay₁_eq] at hay₁_sub
        refine ⟨u₀, W, by omega, hW_lt, by omega, hz₁_sub, hay₁_sub⟩
  obtain ⟨u₀, W, hposW, hW_lt, hW_le, hz'_sub, hay'_sub⟩ := hex_walk
  obtain ⟨φ, hranφ, hcardφ⟩ := exists_closedCurve_of_radial_walk_ncard hrad.2.1 W hposW hW_le
  have hins_sub : insWalk ins K W ⊆ curveIns φ := insWalk_subset_curveIns hslope hW_lt hranφ
  have hx_ins : x ∈ curveIns φ := hins_sub (hz'_sub hxz')
  by_cases hy_ins : y ∈ curveIns φ
  · exact ⟨φ, hcardφ, hx_ins, hy_ins⟩
  · -- `y ∉ curveIns φ`, so `a_y` must be a region `r ∈ H.R` meeting `range φ`
    obtain ⟨-, -, hcase⟩ := hay'
    rcases hcase with ⟨v, -, rfl, rfl⟩ | ⟨_, _, hsub⟩ | ⟨hr, w_y, hwy, rfl⟩
    · exact (hy_ins (hins_sub (hay'_sub hya))).elim
    · exact (hy_ins (hins_sub (hay'_sub (hsub hya)))).elim
    · have hwy_ins : w_y ∈ insWalk ins K W := hay'_sub (mem_singleton w_y)
      have hy_not_insW : y ∉ insWalk ins K W := fun h => hy_ins (hins_sub h)
      have hr_meet_W : (a_y ∩ range φ).Nonempty := by
        rw [hranφ]
        rcases hwy_ins with hwy_U | hwy_C
        · exact ⟨w_y, hwy.2, hwy_U⟩
        · obtain ⟨C₀, ⟨hC₀, hC₀s⟩, hwy_C₀⟩ := mem_iUnion₂.mp hwy_C
          have hy_not_C₀ : y ∉ ins C₀ := fun hyC₀ =>
            hy_not_insW (Or.inr (mem_iUnion₂.mpr ⟨C₀, ⟨hC₀, hC₀s⟩, hyC₀⟩))
          have hLs : (walkDrawing K W).IsSubdrawing K := walkDrawing_isSubdrawing K W
          have hlen₀ : C₀.length < 2 * θ := by
            refine lt_of_le_of_lt ?_ hW_lt
            have hsub₀ : C₀.E ⊆ {e | e ∈ W.edges} := by
              have := hC₀s.2
              rwa [walkDrawing_E] at this
            calc C₀.E.ncard ≤ ({e | e ∈ W.edges} : Set (Set S)).ncard :=
                  Set.ncard_le_ncard hsub₀ (List.finite_toSet _)
              _ ≤ W.edges.length := by
                  rw [show ({e | e ∈ W.edges} : Set (Set S)) = ↑W.edges.toFinset by ext; simp,
                    Set.ncard_coe_finset]
                  exact List.toFinset_card_le _
              _ = W.length := rfl
          obtain ⟨hdisc₀, hbd₀, -⟩ := hslope C₀ hC₀ (hC₀s.trans hLs) hlen₀
          have hcl₀ : IsClosed (ins C₀) := hdisc₀.isClosed
          have hfr₀ : frontier (ins C₀) = C₀.U := by rw [subBd_eq_frontier', hbd₀]
          have hnot_dis : ¬ Disjoint a_y (frontier (ins C₀)) := fun hdis =>
            hy_not_C₀ (GM12.subset_of_disjoint_frontier (region_isPreconnected hr) hcl₀ hdis hwy.2
              hwy_C₀ hya)
          rw [Set.not_disjoint_iff] at hnot_dis
          obtain ⟨p₀, hp₀_ay, hp₀_fr⟩ := hnot_dis
          rw [hfr₀] at hp₀_fr
          exact ⟨p₀, hp₀_ay, hC₀s.U_subset hp₀_fr⟩
      obtain ⟨p₀, hp₀_ay, z₀, rfl⟩ := hr_meet_W
      have hpc_ay : IsPathConnected a_y := (hResp.1.2 a_y hr).isPathConnected
      obtain ⟨γ, hγ_sub⟩ := hpc_ay.joinedIn (φ z₀) hp₀_ay y hya
      obtain ⟨φ', hranφ'⟩ := exists_closedCurve_union_path φ z₀ γ
      have hγ_disj : range γ ∩ H.U = ∅ := by
        refine eq_empty_of_forall_notMem fun q ⟨⟨t, hqt⟩, hqU⟩ => ?_
        subst hqt
        exact region_subset hr (hγ_sub t) hqU
      have hran_inter : range φ' ∩ H.U = range φ ∩ H.U := by
        rw [hranφ', union_inter_distrib_right, hγ_disj, union_empty]
      refine ⟨φ', hran_inter.symm ▸ hcardφ, ?_, ?_⟩
      · exact curveIns_mono (hranφ'.symm ▸ subset_union_left) hx_ins
      · refine Or.inl ?_
        rw [hranφ']
        exact Or.inr ⟨1, γ.target⟩

end GraphMinor.GM14
