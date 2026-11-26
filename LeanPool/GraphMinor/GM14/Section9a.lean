/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section7
public import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM14.Section5
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM12.Section4WalkMetric

/-!
# Graph Minors XIV, Section 9 (Part 1): (9.1), (9.2), and (9.4)

This file formalizes `(9.1)`, `(9.2)`, and `(9.4)` of Section 9 (*Constant Radius Discs*,
pages 43–45) of N. Robertson and P. D. Seymour, *Graph Minors. XIV. Extending an embedding*,
J. Combin. Theory Ser. B **65** (1995) 23–50:

- `theorem_9_1`: Graph Minors XIV, (9.1) (page 43), showing that the union `Z` of `ins(W)` over
  all closed walks `W` of a radial drawing `K` of length `< 2κ` (`1 ≤ κ ≤ θ`) with `z ⊆ ins(W)`
  (`z ∈ A(K)`) is included in the interior `Δ \ subBd Δ` of some closed disc `Δ ⊆ Σ`.
- `full_of_9_2` / `theorem_9_2`: Graph Minors XIV, (9.2) (page 43), proving
  `GM16.GM14Theorem92Statement` (existence of a `(κ + 2)`-zone `Λ` around `z ∈ A(H)` including all
  atoms `x ∈ A(H)` with `d(z, x) < κ`, for `2 ≤ κ ≤ θ - 3`).
- `theorem_9_4`: Graph Minors XIV, (9.4) (page 45), constructing a closed disc `Δ ⊆ Σ` with
  `α`-normal boundary around a `κ`-zone `Λ` (`1 ≤ κ ≤ θ - 7`) such that `Λ ⊆ Δ \ subBd Δ`,
  `H ∩ closure (Σ - Δ)` has a circuit, and `d(z, x) ≤ κ + 3` for all `x ∈ A(H)` meeting `Δ`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph Hypergraph Metric
open GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11

universe u v w

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Walk Unions, Restraint Unions, and Proof of (9.1) (page 43) -/

/-- The union of `insWalk ins K W` over all closed walks `W` of `K` of length `< k` with
`z ⊆ insWalk ins K W` (Graph Minors XIV, (9.1), page 43). -/
def walkUnion [T1Space S] (K : Drawing S) (ins : Drawing S → Set S) (k : ℕ) (z : Set S) : Set S :=
  ⋃ X ∈ {X : Set S | ∃ (u : S) (W : GraphWalk K.toGraph u u),
    W.length < k ∧ z ⊆ insWalk ins K W ∧ X = insWalk ins K W}, X

/-- For `z ∈ A(K)`, `c ∈ z`, and `1 ≤ κ ≤ θ`, the union `walkUnion K ins (2 * κ) z` over closed
walks of length `< 2κ` equals `restraintUnion K ins (2 * θ) c (2 * κ - 1)`. -/
theorem walkUnion_eq_restraintUnion [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S)
    {K : Drawing S} {ins : Drawing S → Set S} {θ κ : ℕ}
    (hsl : IsSlope K (2 * θ) ins) {z : Set S} (hz : z ∈ K.A) {c : S} (hc : c ∈ z)
    (hκ1 : 1 ≤ κ) (hκθ : κ ≤ θ) :
    walkUnion K ins (2 * κ) z = restraintUnion K ins (2 * θ) c (2 * κ - 1) := by
  apply subset_antisymm
  · refine iUnion₂_subset ?_
    rintro X ⟨u, W, hW, hzW, rfl⟩
    have hWθ : W.length < 2 * θ := by omega
    obtain ⟨hrest, hlen⟩ := GM11.theorem_8_5_proof hS hsl W hWθ
    have hle : perimeterWalkLength K (insWalk ins K W) ≤ 2 * κ - 1 := by omega
    exact subset_biUnion_of_mem (u := id) ⟨hrest, hle, hzW hc⟩
  · refine iUnion₂_subset ?_
    rintro X ⟨hrest, hlen, hcX⟩
    obtain ⟨u, W, -, hWlen, hWθ, -, hd⟩ := hrest.exists_walk hS
    have hins_eq : insWalk ins K W = X := GM11.insWalk_eq hS hsl hrest hd
    have hWκ : W.length < 2 * κ := by omega
    have hzX : z ⊆ insWalk ins K W := hins_eq ▸ GM11.nice_atom hrest.isGammaNice hz ⟨c, hc, hcX⟩
    intro x hx
    rw [← hins_eq] at hx
    exact mem_iUnion₂.mpr ⟨insWalk ins K W, ⟨u, W, hWκ, hzX, rfl⟩, hx⟩

/-- A closed subset `Z` of an open disc `Λ` in a closed surface `S` is contained in the interior
`Δ \ subBd Δ` of some closed disc `Δ ⊆ Λ`. -/
theorem exists_closedDisc_interior_superset [T2Space S]
    (hS : IsClosedSurface S) {Λ Z : Set S} (hΛ : IsOpenDisc Λ) (hZ : IsClosed Z) (hZΛ : Z ⊆ Λ) :
    ∃ Δ : Set S, Δ ⊆ Λ ∧ IsClosedDisc Δ ∧ Z ⊆ Δ \ subBd Δ := by
  have : CompactSpace S := hS.1
  obtain ⟨hΛopen, ⟨φ⟩⟩ := hΛ
  have hZc : IsCompact Z := hZ.isCompact
  let T : Set Λ := Subtype.val ⁻¹' Z
  have hT : IsCompact T := Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr (by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hZΛ]
    exact hZc)
  have hT' : IsCompact (φ.symm '' T) := hT.image φ.symm.continuous
  have hbd : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ x ∈ φ.symm '' T, ‖(x : EuclideanPlane)‖ < ρ := by
    by_cases hne : (φ.symm '' T).Nonempty
    · obtain ⟨x₀, hx₀, hmax⟩ := hT'.exists_isMaxOn hne
        (f := fun x : OpenUnitDisc => ‖(x : EuclideanPlane)‖) (by fun_prop)
      have hn : ‖(x₀ : EuclideanPlane)‖ < 1 := by
        have := x₀.2
        simpa [OpenUnitDisc] using this
      refine ⟨(‖(x₀ : EuclideanPlane)‖ + 1) / 2, by positivity, by linarith, fun x hx => ?_⟩
      have hle : ‖(x : EuclideanPlane)‖ ≤ ‖(x₀ : EuclideanPlane)‖ := hmax hx
      linarith
    · refine ⟨1 / 2, by norm_num, by norm_num, fun x hx => ?_⟩
      exact absurd ⟨x, hx⟩ hne
  obtain ⟨ρ, h0, h1, hρ⟩ := hbd
  have hin : ∀ x : ClosedUnitDisc, ρ • (x : EuclideanPlane) ∈ OpenUnitDisc := by
    intro x
    have hx : ‖(x : EuclideanPlane)‖ ≤ 1 := by
      have := x.2
      simpa [ClosedUnitDisc] using this
    have : ‖ρ • (x : EuclideanPlane)‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg h0.le]
      nlinarith
    simpa [OpenUnitDisc] using this
  let m : ClosedUnitDisc → S := fun x => (φ ⟨ρ • x.1, hin x⟩).1
  have hmc : Continuous m :=
    continuous_subtype_val.comp (φ.continuous.comp (Continuous.subtype_mk (by fun_prop) _))
  have hmi : Function.Injective m := by
    intro x y hxy
    have h₁ := φ.injective (Subtype.ext hxy)
    have h₂ : ρ • x.1 = ρ • y.1 := congrArg Subtype.val h₁
    exact Subtype.ext (smul_right_injective _ h0.ne' h₂)
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hemb := hmc.isClosedEmbedding hmi
  have hD : IsClosedDisc (range m) := ⟨hemb.isEmbedding.toHomeomorph⟩
  have hsubΛ : range m ⊆ Λ := by
    rintro _ ⟨x, rfl⟩
    exact (φ _).2
  let U₀ : Set OpenUnitDisc := {x : OpenUnitDisc | ‖(x : EuclideanPlane)‖ < ρ}
  have hU₀_open : IsOpen U₀ := isOpen_lt (by fun_prop) continuous_const
  let V : Set S := Subtype.val '' (φ '' U₀)
  have hV_open : IsOpen V :=
    hΛopen.isOpenMap_subtype_val _ (φ.isOpenMap U₀ hU₀_open)
  have hZV : Z ⊆ V := by
    intro y hy
    have hyΛ : y ∈ Λ := hZΛ hy
    refine ⟨⟨y, hyΛ⟩, ⟨φ.symm ⟨y, hyΛ⟩, ?_, φ.apply_symm_apply _⟩, rfl⟩
    exact hρ _ ⟨⟨y, hyΛ⟩, hy, rfl⟩
  have hVm : V ⊆ range m := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hzn : ‖(z : EuclideanPlane)‖ ≤ ρ := le_of_lt hz
    have hmem : ρ⁻¹ • (z : EuclideanPlane) ∈ ClosedUnitDisc := by
      have : ‖ρ⁻¹ • (z : EuclideanPlane)‖ ≤ 1 := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg h0.le]
        exact (inv_mul_le_iff₀ h0).mpr (by simpa using hzn)
      simpa [ClosedUnitDisc] using this
    refine ⟨⟨_, hmem⟩, ?_⟩
    have heq : (⟨ρ • (ρ⁻¹ • (z : EuclideanPlane)), hin ⟨_, hmem⟩⟩ : OpenUnitDisc) = z :=
      Subtype.ext (smul_inv_smul₀ h0.ne' _)
    change (φ _).1 = (φ z).1
    rw [heq]
  have hint : Z ⊆ interior (range m) := hZV.trans (interior_maximal hVm hV_open)
  refine ⟨range m, hsubΛ, hD, fun y hy => ⟨ interior_subset (hint hy), fun hybd => ?_⟩⟩
  rw [← subBd_eq_frontier'] at hybd
  exact hybd.2 (hint hy)

/-- **Graph Minors XIV, (9.1)** (page 43):
"Let $H$ be a 2-cell drawing in $\Sigma$, with radial drawing $K$. Let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta$, let $\kappa$ be an integer with $1 \le \kappa
\le \theta$, let $z \in A(K)$, and let $Z$ be the union of $ins(W)$, taken over all closed
walks $W$ of $K$ of length $< 2\kappa$ with $z \subseteq ins(W)$. Then there is a closed
disc $\Delta \subseteq \Sigma$ with $Z \subseteq \Delta - bd(\Delta)$." -/
theorem theorem_9_1_proof
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {H K : Drawing S} {θ κ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S} {z : Set S}
    (hResp : IsRespectfulDrawingTangle H θ T)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hκ1 : 1 ≤ κ) (hκθ : κ ≤ θ) (hz : z ∈ K.A) :
    ∃ Δ : Set S, IsClosedDisc Δ ∧ walkUnion K ins (2 * κ) z ⊆ Δ \ subBd Δ := by
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hResp.2.1.isPretangle hK.2.1.1 hd
  obtain ⟨c, hc⟩ := atom_nonempty hz
  have hZ_eq : walkUnion K ins (2 * κ) z = restraintUnion K ins (2 * θ) c (2 * κ - 1) :=
    walkUnion_eq_restraintUnion hS hsl hz hc hκ1 hκθ
  set Z := restraintUnion K ins (2 * θ) c (2 * κ - 1)
  have hZcl : IsClosed Z := GM11.isClosed_restraintUnion hS c (2 * κ - 1)
  have hZnice : IsGammaNice K Z := GM11.isGammaNice_restraintUnion c (2 * κ - 1)
  obtain ⟨r₀, hr₀, hno₀⟩ := GM11.theorem_8_12_proof hS hsl c
  obtain ⟨p₀, hp₀⟩ := region_nonempty hr₀
  have hp₀_not : p₀ ∉ Z := by
    intro hpZ
    obtain ⟨X, ⟨hrest, -, hcX⟩, hpX⟩ := mem_iUnion₂.mp hpZ
    have hrX : r₀ ⊆ X := GM11.nice_region hrest.isGammaNice hr₀ ⟨p₀, hp₀, hpX⟩
    exact hno₀ X hrest ⟨hcX, hrX⟩
  have hZ_ne_univ : Z ≠ univ := fun h => hp₀_not (h ▸ mem_univ p₀)
  by_cases hZne : Z.Nonempty
  · have hZsc : IsSimplyConnectedSet Z := GM11.theorem_8_10_proof hS hsl hZne
    obtain ⟨Λ, hΛ, hZΛ⟩ := GM11.exists_openDisc_around hS hZcl hZnice hZsc hZ_ne_univ
    obtain ⟨Δ, -, hΔ, hZΔ⟩ := exists_closedDisc_interior_superset hS hΛ hZcl hZΛ
    exact ⟨Δ, hΔ, hZ_eq ▸ hZΔ⟩
  · have hZ_emp : walkUnion K ins (2 * κ) z = ∅ :=
      hZ_eq.trans (not_nonempty_iff_eq_empty.mp hZne)
    obtain ⟨Δ, -, hΔ, -⟩ := exists_closedDisc_nbhd hS isOpen_univ (mem_univ c)
    exact ⟨Δ, hΔ, hZ_emp.symm ▸ empty_subset _⟩

/-! ## 2. Region-Edge Distance and Proof of (9.2) (page 43) -/

/-- If `T` is a tangle of order `θ ≥ 2` in a hypergraph `G`, then `E(G)` is nonempty. -/
theorem edgeSet_nonempty_of_isTangle {α β : Type*} {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ T) (hθ : 2 ≤ θ) :
    G.edgeSet.Nonempty := by
  have hsep : G.IsSeparation ⊥ G := by
    rw [isSeparation_iff_of_le bot_le le_rfl]
    simp
  have hord : separationOrder (⊥ : Hypergraph α β) G < θ := by
    have : ((⊥ : Hypergraph α β) ∩ G).vertexSet = ∅ := by simp
    rw [separationOrder, this, ncard_empty]
    omega
  have hbot : (⊥, G) ∈ T :=
    (hT.axiom1 hsep hord).resolve_right fun h => hT.axiom3 h rfl
  have hne := GM10.theorem_2_3_proof hT hθ hbot hbot hbot
  by_contra hemp
  rw [not_nonempty_iff_eq_empty] at hemp
  apply hne
  simp [hemp]

/-- If `r ∈ H.R` and `r' ∈ K.R` have nonempty intersection `(r ∩ r').Nonempty`, and `w ∈ K.V ∩ r`
is the hub of `r` in `K`, then `w ∈ closure r'`. -/
theorem hub_mem_closure_of_inter_nonempty
    (hS : IsClosedSurface S) {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    {r r' : Set S} (hr : r ∈ H.R) (hr' : r' ∈ K.R) (hne : (r ∩ r').Nonempty)
    {w : S} (hw : w ∈ K.V ∩ r) :
    w ∈ closure r' := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨y, hyr, hyr'⟩ := hne
  have hrad : PreRad (PaintingOrDrawing.drawing H) K := ⟨hK.1, hK.2.1⟩
  have hyU : y ∉ (radialUnion hrad).U :=
    fun h => h.elim (region_subset hr hyr) (region_subset hr' hyr')
  obtain ⟨p, hp, hyp⟩ := exists_region_of_notMem hyU
  have hpr' : p ⊆ r' := GM11.region_sub_of_mem hrad hS hr' hp (subset_closure hyp) hyr'
  have hpr : p ⊆ r := subset_region hr (region_isPreconnected hp)
    (disjoint_left.mpr fun z hz hzU => region_subset hp hz (Or.inl hzU)) hyp hyr
  exact closure_mono hpr' (GM11.hub_mem_closure hrad hS hr hp hpr hw.2 hw.1)

/-- If `r ∈ H.R`, `e ∈ H.E`, `r' ∈ K.R`, `e ⊆ r'`, and `(r ∩ r').Nonempty`, then
`tangleMetric H K ins θ r e ≤ 2` (Graph Minors XIV, proof of (9.2), pages 43–44). -/
theorem tangleMetric_region_edge_le [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hResp : IsRespectfulDrawingTangle H θ T)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    {r e r' : Set S} (hr : r ∈ H.R) (he : e ∈ H.E) (hr' : r' ∈ K.R)
    (her' : e ⊆ r') (hne : (r ∩ r').Nonempty) :
    tangleMetric H K ins θ r e ≤ 2 := by
  classical
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hP := hK.2.1
  by_cases hθ : θ ≤ 2
  · exact (GM11.tangleMetric_le_order hP _ _).trans hθ
  push Not at hθ
  have hT := hResp.2.1
  have hefin : (H.toHypergraph.ends e).Finite :=
    H.toHypergraph.vertexSet_finite.subset fun _ hx => H.toHypergraph.vertex_mem_of_inc hx
  have h2 := GM12.drawing_edge_ends_ncard_le_two he
  obtain ⟨D, hD, hDs, hDl, hDV, heD⟩ :=
    GM14.exists_circuit_around_drawing_edge hS ‹_› hResp (by omega) hK hd he
  have hT' : IsPretangle (PaintingOrDrawing.drawing H).toHypergraph θ T := hT.isPretangle
  have hs := GM11.isSlope_of_derived hS hT' hP.1 hd
  obtain ⟨-, -, hnice⟩ := GM11.ins_slope_facts hS hs hD hDs hDl
  have hcl : IsClosed (ins D) := (hs.isClosedDisc D hD hDs hDl).isCompact.isClosed
  obtain ⟨u, W₀, hW₀, -, hV, hE⟩ := id hD
  obtain ⟨W, hsu, hed⟩ := hDs.exists_walk_up W₀
  have hDeq := (circuit_length_eq_two_mul_ncard hP hD hDs).1
  have hWlen : W.length = D.length := by
    rw [Drawing.length, hE, ← hed]
    have h : {f | f ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext; simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup (hed ▸ hW₀.2)]
    rfl
  have hDV_ends : D.V ∩ H.V ⊆ H.toHypergraph.ends e := fun x hx => (hDV hx).1
  have hncard_le : (D.V ∩ H.V).ncard ≤ 2 :=
    (ncard_le_ncard hDV_ends hefin).trans h2
  set n := (D.V ∩ H.V).ncard
  have hsub : D.IsSubdrawing (walkDrawing K W) := by
    refine ⟨fun x hx => ?_, fun f hf => ?_⟩
    · rw [walkDrawing_V, hsu]
      rw [hV] at hx
      exact hx
    · rw [walkDrawing_E, hed]
      rw [hE] at hf
      exact hf
  have hins : ins D ⊆ insWalk ins K W := fun x hx =>
    Or.inr (mem_iUnion₂.mpr ⟨D, ⟨hD, hsub⟩, hx⟩)
  obtain ⟨y, hy⟩ := he.1
  have hr'D : r' ⊆ ins D := GM11.nice_atom hnice (Or.inr hr') ⟨y, her' hy, heD hy⟩
  obtain ⟨w, ⟨hwr, hwV⟩, -⟩ := hP.2.2.1 r hr
  have hw_cl : w ∈ closure r' :=
    hub_mem_closure_of_inter_nonempty hS hK hr hr' hne ⟨hwV, hwr⟩
  have hwit : GM11.MetricWitness H K ins θ r e n := by
    refine ⟨u, W, {w}, r', ?_, ?_, by omega, by omega, ?_, hr'D.trans hins⟩
    · exact ⟨Or.inr hr, Or.inl (Or.inl ⟨w, hwV, rfl⟩), Or.inr (Or.inr ⟨hr, w, ⟨hwV, hwr⟩, rfl⟩)⟩
    · exact ⟨Or.inl (Or.inr he), Or.inr hr', Or.inr (Or.inl ⟨he, hr', her'⟩)⟩
    · rw [singleton_subset_iff]
      exact hins (closure_minimal hr'D hcl hw_cl)
  exact (GM11.tangleMetric_le hwit).trans hncard_le

/-- For any atom `z' ∈ A(K)`, if `3 ≤ θ`, then there is a closed walk `W` of `K` of length `< 2θ`
with `z' ⊆ insWalk ins K W`, so `z' ⊆ walkUnion K ins (2 * θ) z'`. -/
theorem atom_subset_walkUnion_of_three_le [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hResp : IsRespectfulDrawingTangle H θ T)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hθ : 3 ≤ θ) {z' : Set S} (hz' : z' ∈ K.A) :
    z' ⊆ walkUnion K ins (2 * θ) z' := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hP := hK.2.1
  rcases hz' with (⟨v, hv, rfl⟩ | hg) | hr'
  · let W : GraphWalk K.toGraph v v := GraphWalk.nil hv
    have hWlen : W.length < 2 * θ := by
      change 0 < 2 * θ
      omega
    have hvW : ({v} : Set S) ⊆ insWalk ins K W := by
      rw [singleton_subset_iff]
      refine Or.inl ((walkDrawing K W).V_subset_U ?_)
      rw [walkDrawing_V]
      exact W.start_mem_support
    exact fun x hx => mem_iUnion₂.mpr ⟨insWalk ins K W, ⟨v, W, hWlen, hvW, rfl⟩, hvW hx⟩
  · obtain ⟨v, hv, r, hr, w, hwr, hwV, hcap, -⟩ := GM11.spoke_ends ⟨hK.1, hK.2.1⟩ hS hg
    have hlink : K.toGraph.IsLink z' v w := ⟨hg, hK.2.1.2.1 hv, hwV, hcap⟩
    let W : GraphWalk K.toGraph v v :=
      GraphWalk.cons hlink (GraphWalk.cons hlink.symm (GraphWalk.nil (hK.2.1.2.1 hv)))
    have hWlen : W.length < 2 * θ := by
      change 2 < 2 * θ
      omega
    have hgW : z' ⊆ insWalk ins K W := by
      intro x hx
      refine Or.inl ?_
      have heW : z' ∈ (walkDrawing K W).E := by
        rw [walkDrawing_E]
        simp [W]
      exact (walkDrawing K W).closure_subset_U heW (subset_closure hx)
    exact fun x hx => mem_iUnion₂.mpr ⟨insWalk ins K W, ⟨v, W, hWlen, hgW, rfl⟩, hgW hx⟩
  · have hE : H.E.Nonempty := edgeSet_nonempty_of_isTangle hResp.2.1 (by omega)
    have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
    obtain ⟨e, he, her'⟩ := hrf.1 z' hr'
    have hT := hResp.2.1
    have hefin : (H.toHypergraph.ends e).Finite :=
      H.toHypergraph.vertexSet_finite.subset fun _ hx => H.toHypergraph.vertex_mem_of_inc hx
    have h2 := GM12.drawing_edge_ends_ncard_le_two he
    obtain ⟨D, hD, hDs, hDl, hDV, heD⟩ :=
      GM14.exists_circuit_around_drawing_edge hS ‹_› hResp (by omega) hK hd he
    have hT' : IsPretangle (PaintingOrDrawing.drawing H).toHypergraph θ T := hT.isPretangle
    have hs := GM11.isSlope_of_derived hS hT' hP.1 hd
    obtain ⟨-, -, hnice⟩ := GM11.ins_slope_facts hS hs hD hDs hDl
    obtain ⟨u, W₀, hW₀, -, hV, hE_D⟩ := id hD
    obtain ⟨W, hsu, hed⟩ := hDs.exists_walk_up W₀
    have hDeq := (circuit_length_eq_two_mul_ncard hP hD hDs).1
    have hWlen : W.length = D.length := by
      rw [Drawing.length, hE_D, ← hed]
      have h : {f | f ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext; simp
      rw [h, ncard_coe_finset, List.toFinset_card_of_nodup (hed ▸ hW₀.2)]
      rfl
    have hDV_ends : D.V ∩ H.V ⊆ H.toHypergraph.ends e := fun x hx => (hDV hx).1
    have hncard_le : (D.V ∩ H.V).ncard ≤ 2 :=
      (ncard_le_ncard hDV_ends hefin).trans h2
    have hWlt : W.length < 2 * θ := by omega
    have hsub : D.IsSubdrawing (walkDrawing K W) := by
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · rw [walkDrawing_V, hsu]
        rw [hV] at hx
        exact hx
      · rw [walkDrawing_E, hed]
        rw [hE_D] at hf
        exact hf
    have hins : ins D ⊆ insWalk ins K W := fun x hx =>
      Or.inr (mem_iUnion₂.mpr ⟨D, ⟨hD, hsub⟩, hx⟩)
    obtain ⟨y, hy⟩ := he.1
    have hr'W : z' ⊆ insWalk ins K W :=
      (GM11.nice_atom hnice (Or.inr hr') ⟨y, her' hy, heD hy⟩).trans hins
    exact fun x hx => mem_iUnion₂.mpr ⟨insWalk ins K W, ⟨u, W, hWlt, hr'W, rfl⟩, hr'W hx⟩

/-- If `Λ` is an open disc with `IsClosedDisc (closure Λ)` and `subBd (closure Λ) = C.U` for a
subdrawing `C` of `H`, and `closure Λ \ C.U = Λ`, then any atom `x ∈ A(H)` meeting `Λ` satisfies
`x ⊆ Λ`. -/
theorem atom_subset_open_of_inter_nonempty
    (hS : IsClosedSurface S) {H C : Drawing S} {Λ x : Set S}
    (hCH : C.IsSubdrawing H) (_hcl_disc : IsClosedDisc (closure Λ))
    (hbd_cl : subBd (closure Λ) = C.U) (hdiff : closure Λ \ C.U = Λ)
    (hx : x ∈ H.A) (hne : (x ∩ Λ).Nonempty) :
    x ⊆ Λ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨p, hpx, hpΛ⟩ := hne
  have hp_cl : p ∈ closure Λ := by
    rw [← hdiff] at hpΛ
    exact hpΛ.1
  have hp_not_CU : p ∉ C.U := by
    rw [← hdiff] at hpΛ
    exact hpΛ.2
  have hfr : frontier (closure Λ) = C.U := by rw [subBd_eq_frontier', hbd_cl]
  rcases hx with (⟨v, -, rfl⟩ | he) | hr
  · rwa [singleton_subset_iff, ← mem_singleton_iff.mp hpx]
  · have hdis : Disjoint x C.U := by
      refine disjoint_left.mpr fun y hyx hyCU => ?_
      have hyV : y ∉ C.V := fun hyV => (he.2.1 hyx).2 (hCH.1 hyV)
      obtain ⟨f, hfC, hyf⟩ := C.exists_edge_of_mem hyCU hyV
      have hxf : x = f := H.edge_eq_of_mem he (hCH.2 hfC) hyx hyf
      exact hp_not_CU (C.closure_subset_U hfC (subset_closure (hxf ▸ hpx)))
    have hsub : x ⊆ closure Λ :=
      subset_of_disjoint_frontier he.2.2.1.isConnected.isPreconnected isClosed_closure
        (hfr ▸ hdis) hpx hp_cl
    rw [← hdiff]
    exact fun y hy => ⟨hsub hy, disjoint_left.mp hdis hy⟩
  · have hdis : Disjoint x C.U :=
      disjoint_left.mpr fun y hyx hyCU => region_subset hr hyx (hCH.U_subset hyCU)
    have hsub : x ⊆ closure Λ :=
      subset_of_disjoint_frontier (region_isPreconnected hr) isClosed_closure
        (hfr ▸ hdis) hpx hp_cl
    rw [← hdiff]
    exact fun y hy => ⟨hsub hy, disjoint_left.mp hdis hy⟩

/-- If `Λ` is an open disc with `IsClosedDisc (closure Λ)` and `subBd (closure Λ) = C.U` for a
subdrawing `C` of `H`, and `closure Λ \ C.U = Λ`, then any atom `x ∈ A(H)` meeting `closure Λ`
satisfies `x ⊆ closure Λ`. -/
theorem atom_subset_closure_of_inter_nonempty
    (hS : IsClosedSurface S) {H C : Drawing S} {Λ x : Set S}
    (hCH : C.IsSubdrawing H) (hcl_disc : IsClosedDisc (closure Λ))
    (hbd_cl : subBd (closure Λ) = C.U) (hdiff : closure Λ \ C.U = Λ)
    (hx : x ∈ H.A) (hne : (x ∩ closure Λ).Nonempty) :
    x ⊆ closure Λ := by
  by_cases hneΛ : (x ∩ Λ).Nonempty
  · have hsub : Λ ⊆ closure Λ := fun y hy => ((Set.ext_iff.mp hdiff y).mpr hy).1
    exact (atom_subset_open_of_inter_nonempty hS hCH hcl_disc hbd_cl hdiff hx hneΛ).trans hsub
  · obtain ⟨p, hpx, hpcl⟩ := hne
    have hpCU : p ∈ C.U := by
      by_contra hpnot
      exact hneΛ ⟨p, hpx, hdiff ▸ ⟨hpcl, hpnot⟩⟩
    rcases hx with (⟨v, -, rfl⟩ | he) | hr
    · rwa [singleton_subset_iff, ← mem_singleton_iff.mp hpx]
    · have hpV : p ∉ C.V := fun hpV => (he.2.1 hpx).2 (hCH.1 hpV)
      obtain ⟨f, hfC, hpf⟩ := C.exists_edge_of_mem hpCU hpV
      have hxf : x = f := H.edge_eq_of_mem he (hCH.2 hfC) hpx hpf
      have hCU_sub : C.U ⊆ closure Λ := by
        rw [← hbd_cl]
        intro y hy
        have hy' := hy.1
        rwa [closure_closure] at hy'
      exact hxf ▸ (subset_closure.trans (C.closure_subset_U hfC)).trans hCU_sub
    · exact absurd (hCH.U_subset hpCU) (region_subset hr hpx)

/-- Every atom `x ∈ A(H)` of a drawing `H` on `S` is preconnected. -/
theorem atom_isPreconnected {H : Drawing S} {x : Set S} (hx : x ∈ H.A) : IsPreconnected x := by
  rcases hx with (⟨v, -, rfl⟩ | he) | hr
  · exact isPreconnected_singleton
  · exact he.2.2.1.isConnected.isPreconnected
  · exact region_isPreconnected hr

/-- If `x'` is the atom of `K` corresponding to `x ∈ A(H)`, then `(x ∩ x').Nonempty`. -/
theorem correspondingAtom_inter_nonempty {H K : Drawing S} {x x' : Set S}
    (hx' : IsCorrespondingAtom H K x x') : (x ∩ x').Nonempty := by
  rcases hx'.2.2 with ⟨v, -, rfl, rfl⟩ | ⟨he, -, hsub⟩ | ⟨-, v, ⟨-, hvx⟩, rfl⟩
  · exact ⟨v, rfl, rfl⟩
  · obtain ⟨q, hq⟩ := he.1
    exact ⟨q, hq, hsub hq⟩
  · exact ⟨v, hvx, rfl⟩

/-- Every point of a closed surface `S` belongs to some atom `x ∈ A(H)` of a drawing `H` on `S`. -/
theorem exists_atom_mem_of_point (H : Drawing S) (p : S) :
    ∃ x ∈ H.A, p ∈ x := by
  obtain ⟨x, hx, hpx⟩ := GM11.exists_atom H p
  exact ⟨x, hx, hpx⟩

/-- If `Λ` is a `λ`-zone around `z` in `H`, then `closure Λ` is covered by the atoms `x ∈ A(H)`
with `x ⊆ closure Λ` (each of which satisfies `d(z, x) ≤ λ`). Consequently, if `U ⊆ S` contains
every `x ∈ A(H)` with `d(z, x) ≤ λ`, then `closure Λ ⊆ U`. -/
theorem closure_zone_subset [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H : Drawing S} {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ U : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ)
    (hU : ∀ x ∈ H.A, d z x ≤ lam → x ⊆ U) :
    closure Λ ⊆ U := by
  obtain ⟨C, hC, hCH, hCU⟩ := GM11.exists_circuit_of_oArc hZone.isOArc_bd hZone.bd_subset_U
  have hbd_cl : subBd (closure Λ) = C.U := by
    rw [IsClosedDisc.subBd_eq_discBd hS hZone.isClosedDisc_closure,
      discBd_closure_eq_subBd hS hZone.isOpenDisc hZone.isOArc_bd hZone.isClosedDisc_closure, hCU]
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
  have hdiff : closure Λ \ C.U = Λ := by
    rw [hCU]
    ext y
    exact ⟨fun ⟨hycl, hynot⟩ => (hclL ▸ hycl).resolve_right hynot,
      fun hy => ⟨subset_closure hy, disjoint_left.mp hdisL hy⟩⟩
  intro p hp
  obtain ⟨x, hxA, hpx⟩ := exists_atom_mem_of_point H p
  have hx_sub : x ⊆ closure Λ :=
    atom_subset_closure_of_inter_nonempty hS hCH hZone.isClosedDisc_closure hbd_cl hdiff
      hxA ⟨p, hpx, hp⟩
  exact hU x hxA (hZone.dist_le x hxA hx_sub) hpx

private theorem close_corresponding_atom_lies_in_walk_union
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (θ : ℕ)
    (d : Set S → Set S → ℕ)
    (z : Set S)
    (hz : z ∈ H.A)
    (K : Drawing S)
    (ins : Drawing S → Set S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    (z' : Set S)
    (hz' : IsCorrespondingAtom H K z z')
    (hz'_uniq : ∀ (y : Set S), (fun x' => IsCorrespondingAtom H K z x') y → y = z')
    (c : S)
    (hc : c ∈ z')
    (Δ : Set S)
    (hWθ_sub : walkUnion K ins (2 * θ) z' ⊆ Δ \ subBd Δ)
    (hz'_sub_Wθ : z' ⊆ walkUnion K ins (2 * θ) z')
    (hz'_sub_Δ : z' ⊆ Δ \ subBd Δ) :
    ∀ {m : ℕ} {x x' : Set S}, m ≤ θ → IsCorrespondingAtom H K x x' → d z x < m → x' ⊆ z' ∪
      walkUnion K ins (2 * m) z' := by
  intro m x x' hm hx' hlt
  by_cases hzx : z = x
  · subst hzx
    have heq : x' = z' := hz'_uniq x' hx'
    exact heq ▸ subset_union_left
  · rw [hd_eq z hz x hx'.1] at hlt
    rcases (GM11.tangleMetric_cases (ins := ins) (θ := θ) hK.2.1 hzx).resolve_left (by omega) with
      ⟨-, u, W, z₁', x₁', hz₁, hx₁, hWθ, hWlen, hzW, hxW⟩
    have hz₁_eq : z₁' = z' := hz'_uniq z₁' hz₁
    have hx₁_eq : x₁' = x' :=
      (existsUnique_correspondingAtom hK hx'.1).unique hx₁ hx'
    subst hz₁_eq hx₁_eq
    have hWm : W.length < 2 * m := by omega
    exact fun y hy => Or.inr (mem_iUnion₂.mpr ⟨insWalk ins K W, ⟨u, W, hWm, hzW, rfl⟩, hxW hy⟩)

private theorem atom_outside_disc_is_distant_region
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    (H : Drawing S)
    (θ : ℕ)
    (κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (z : Set S)
    (hz : z ∈ H.A)
    (hκ2 : 2 ≤ κ)
    (hκθ : κ + 3 ≤ θ)
    [ConnectedSpace S]
    [LocallyConnectedSpace S]
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hResp : IsRespectfulDrawingTangle H θ T)
    (K : Drawing S)
    (ins : Drawing S → Set S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    (hsl : IsSlope K (2 * θ) ins)
    (hrf : RegionFacts (PaintingOrDrawing.drawing H) K)
    (z' : Set S)
    (hz' : IsCorrespondingAtom H K z z')
    (c : S)
    (hc : c ∈ z')
    (Δ : Set S)
    (hWθ_sub : walkUnion K ins (2 * θ) z' ⊆ Δ \ subBd Δ)
    (hz'_sub_Wθ : z' ⊆ walkUnion K ins (2 * θ) z')
    (hcorr_sub_walkUnion : ∀ {m : ℕ} {x x' : Set S}, m ≤ θ → IsCorrespondingAtom H K x x' → d z x
      < m → x' ⊆ z' ∪ walkUnion K ins (2 * m) z') :
    ∀ x ∈ H.A, d z x < θ → ¬x ⊆ Δ \ subBd Δ → x ∈ H.R ∧ θ - 2 ≤ d z x := by
  intro x hx hlt hnot
  obtain ⟨x', hx', -⟩ := existsUnique_correspondingAtom hK hx
  have hx'_sub_Wθ : x' ⊆ walkUnion K ins (2 * θ) z' := by
    rcases union_subset hz'_sub_Wθ Subset.rfl with hsub
    exact (hcorr_sub_walkUnion le_rfl hx' hlt).trans hsub
  have hx'_sub_Δ : x' ⊆ Δ \ subBd Δ := hx'_sub_Wθ.trans hWθ_sub
  have hx_not_x' : ¬ (x ⊆ x') := fun h => hnot (h.trans hx'_sub_Δ)
  have hxR : x ∈ H.R := by
    rcases hx'.2.2 with ⟨v, -, rfl, rfl⟩ | ⟨-, -, hsub⟩ | ⟨hr, -⟩
    · exact absurd Subset.rfl hx_not_x'
    · exact absurd hsub hx_not_x'
    · exact hr
  set Z_θ := walkUnion K ins (2 * θ) z'
  have hZθ_eq : Z_θ = restraintUnion K ins (2 * θ) c (2 * θ - 1) :=
    walkUnion_eq_restraintUnion hS hsl hz'.2.1 hc (by omega) le_rfl
  have hZθ_cl : IsClosed Z_θ := hZθ_eq ▸ GM11.isClosed_restraintUnion hS c (2 * θ - 1)
  have hx_not_Zθ : ¬ (x ⊆ Z_θ) := fun h => hnot (h.trans hWθ_sub)
  obtain ⟨y₀, hy₀x, hy₀Z⟩ := not_subset.mp hx_not_Zθ
  have hO : IsOpen (x \ Z_θ) := (region_isOpen hxR).sdiff hZθ_cl
  obtain ⟨y, ⟨hyx, hyZ⟩, hyK⟩ := GM11.exists_off_U hS K hO ⟨y₀, hy₀x, hy₀Z⟩
  obtain ⟨r', hr', hyr'⟩ := exists_region_of_notMem hyK
  have hr'_not_Zθ : ¬ (r' ⊆ Z_θ) := fun h => hyZ (h hyr')
  obtain ⟨e, he, her'⟩ := hrf.1 r' hr'
  have he_corr : IsCorrespondingAtom H K e r' :=
    ⟨Or.inl (Or.inr he), Or.inr hr', Or.inr (Or.inl ⟨he, hr', her'⟩)⟩
  have hze_θ : d z e = θ := by
    by_contra hne_θ
    have hle_θ : d z e ≤ θ := by
      rw [hd_eq z hz e (Or.inl (Or.inr he))]
      exact GM11.tangleMetric_le_order hK.2.1 z e
    have hlt_θ : d z e < θ := lt_of_le_of_ne hle_θ hne_θ
    have hr'_sub : r' ⊆ Z_θ :=
      (hcorr_sub_walkUnion le_rfl he_corr hlt_θ).trans (union_subset hz'_sub_Wθ Subset.rfl)
    exact hr'_not_Zθ hr'_sub
  have hxe_le : d x e ≤ 2 := by
    rw [hd_eq x hx e (Or.inl (Or.inr he))]
    exact tangleMetric_region_edge_le hS hResp hK hd hxR he hr' her' ⟨y, hyx, hyr'⟩
  have htri' := htri z hz x hx e (Or.inl (Or.inr he))
  refine ⟨hxR, by omega⟩

private theorem atom_meeting_walk_union_is_close
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    (H : Drawing S)
    (θ : ℕ)
    (d : Set S → Set S → ℕ)
    (z : Set S)
    (hz : z ∈ H.A)
    [ConnectedSpace S]
    (hrefl : ∀ a ∈ H.A, d a a = 0)
    (K : Drawing S)
    (ins : Drawing S → Set S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    (hsl : IsSlope K (2 * θ) ins)
    (z' : Set S)
    (hz' : IsCorrespondingAtom H K z z') :
    ∀ {m : ℕ} {x x' : Set S}, 1 ≤ m → m ≤ θ → IsCorrespondingAtom H K x x' → (x' ∩ walkUnion K ins
      (2 * m) z').Nonempty → d z x < m := by
  intro m x x' hm1 hmθ hx' ⟨p, hpx', hpW⟩
  by_cases hzx : z = x
  · subst hzx
    rw [hrefl z hz]
    omega
  · obtain ⟨X, ⟨u, W, hWm, hzW, rfl⟩, hpX⟩ := mem_iUnion₂.mp hpW
    have hWθ : W.length < 2 * θ := by omega
    obtain ⟨hrest, -⟩ := GM11.theorem_8_5_proof hS hsl W hWθ
    have hx'W : x' ⊆ insWalk ins K W :=
      GM11.nice_atom hrest.isGammaNice hx'.2.1 ⟨p, hpx', hpX⟩
    have h2le := two_mul_tangleMetric_le_walk_length hK hz' hx' W hWθ hzW hx'W
    rw [hd_eq z hz x hx'.1]
    omega

private theorem restraint_with_selected_regions_is_preconnected
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    (H : Drawing S)
    (θ : ℕ)
    (κ : ℕ)
    (z : Set S)
    [ConnectedSpace S]
    (K : Drawing S)
    (ins : Drawing S → Set S)
    (hsl : IsSlope K (2 * θ) ins)
    (z' : Set S)
    (hz' : IsCorrespondingAtom H K z z')
    (c : S)
    (hWκ_eq : (walkUnion K ins (2 * κ) z') = restraintUnion K ins (2 * θ) c (2 * κ - 1)) :
    IsPreconnected (z' ∪ (walkUnion K ins (2 * κ) z')) := by
  let W_κ := walkUnion K ins (2 * κ) z'
  let Z := z' ∪ W_κ
  change IsPreconnected Z
  change W_κ = _ at hWκ_eq
  by_cases hne : W_κ.Nonempty
  · obtain ⟨q, hq⟩ := id hne
    obtain ⟨X, ⟨u, W, hW, hzW, rfl⟩, -⟩ := mem_iUnion₂.mp hq
    have hz'_Wκ : z' ⊆ W_κ := fun x hx =>
      mem_iUnion₂.mpr ⟨insWalk ins K W, ⟨u, W, hW, hzW, rfl⟩, hzW hx⟩
    have hZ_eq_Wκ : Z = W_κ := union_eq_right.mpr hz'_Wκ
    have hsc : IsSimplyConnectedSet W_κ :=
      hWκ_eq ▸ GM11.theorem_8_10_proof hS hsl (hWκ_eq ▸ hne)
    exact hZ_eq_Wκ ▸ hsc.1.isConnected.isPreconnected
  · have hWκ_emp : W_κ = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hZ_eq_z' : Z = z' := by simp [Z, hWκ_emp]
    exact hZ_eq_z' ▸ atom_isPreconnected hz'.2.1

private theorem region_meeting_restraint_is_close
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    (H : Drawing S)
    (θ : ℕ)
    (κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (z : Set S)
    (hz : z ∈ H.A)
    (hκ2 : 2 ≤ κ)
    (hκθ : κ + 3 ≤ θ)
    [this : ConnectedSpace S]
    [LocallyConnectedSpace S]
    (hrefl : ∀ a ∈ H.A, d a a = 0)
    (hsymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hv_reg : H.E.Nonempty → ∀ v ∈ H.V, ∀ r ∈ H.R, v ∈ closure r → d {v} r ≤ 1)
    (hResp : IsRespectfulDrawingTangle H θ T)
    (K : Drawing S)
    (ins : Drawing S → Set S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    (hE : H.E.Nonempty)
    (z' : Set S)
    (hz' : IsCorrespondingAtom H K z z')
    (hz'_uniq : ∀ (y : Set S), (fun x' => IsCorrespondingAtom H K z x') y → y = z')
    (c : S)
    (hc : c ∈ z')
    (Δ : Set S)
    (hWθ_sub : walkUnion K ins (2 * θ) z' ⊆ Δ \ subBd Δ)
    (hz'_sub_Wθ : z' ⊆ walkUnion K ins (2 * θ) z')
    (hz'_sub_Δ : z' ⊆ Δ \ subBd Δ)
    (hcorr_sub_walkUnion : ∀ {m : ℕ} {x x' : Set S}, m ≤ θ → IsCorrespondingAtom H K x x' → d z x
      < m → x' ⊆ z' ∪ walkUnion K ins (2 * m) z')
    (hclaim1 : ∀ x ∈ H.A, d z x < θ → ¬x ⊆ Δ \ subBd Δ → x ∈ H.R ∧ θ - 2 ≤ d z x)
    (hWκ_eq : (walkUnion K ins (2 * κ) z') = restraintUnion K ins (2 * θ) c (2 * κ - 1))
    (hWκ_cl : IsClosed (walkUnion K ins (2 * κ) z'))
    (hWκ_nice : IsGammaNice K (walkUnion K ins (2 * κ) z'))
    (hZne : (z' ∪ (walkUnion K ins (2 * κ) z')).Nonempty)
    (hZconn : IsPreconnected (z' ∪ (walkUnion K ins (2 * κ) z')))
    (hdist_lt_of_inter_walkUnion : ∀ {m : ℕ} {x x' : Set S}, 1 ≤ m → m ≤ θ → IsCorrespondingAtom H
      K x x' → (x' ∩ walkUnion K ins (2 * m) z').Nonempty → d z x < m) :
    ∀ r ∈ H.R, (closure r ∩ (z' ∪ (walkUnion K ins (2 * κ) z'))).Nonempty → d z r ≤ κ ∧ r ⊆ Δ \
      subBd Δ := by
  let W_κ := walkUnion K ins (2 * κ) z'
  let Z := z' ∪ W_κ
  intro r hr ⟨p, hpr, hpZ⟩
  have hrA : r ∈ H.A := Or.inr hr
  obtain ⟨w, ⟨hwr, hwV⟩, -⟩ := hK.2.1.2.2.1 r hr
  have hr_corr : IsCorrespondingAtom H K r {w} :=
    ⟨hrA, Or.inl (Or.inl ⟨w, hwV, rfl⟩), Or.inr (Or.inr ⟨hr, w, ⟨hwV, hwr⟩, rfl⟩)⟩
  have hzr_le : d z r ≤ κ := by
    rcases hpZ with hpz' | hpW
    · rcases hz'.2.2 with ⟨v, hv, rfl, rfl⟩ | ⟨he, hr', her'⟩ | ⟨hzR, v, ⟨-, hcz⟩, rfl⟩
      · have hvp : p = v := mem_singleton_iff.mp hpz'
        have hvr : d {v} r ≤ 1 := hv_reg hE v hv r hr (hvp ▸ hpr)
        omega
      · obtain ⟨q, hqr', hqr⟩ := mem_closure_iff.mp hpr z' (region_isOpen hr') hpz'
        have hrz : d r z ≤ 2 := by
          rw [hd_eq r hrA z hz]
          exact tangleMetric_region_edge_le hS hResp hK hd hr he hr' her' ⟨q, hqr, hqr'⟩
        rw [hsymm z hz r hrA]
        omega
      · obtain ⟨q, hqz, hqr⟩ := mem_closure_iff.mp hpr z (region_isOpen hzR)
          (mem_singleton_iff.mp hpz' ▸ hcz)
        have hrz_eq : r = z := region_eq_of_mem hr hzR hqr hqz
        subst hrz_eq
        rw [hrefl r hrA]
        omega
    · by_cases hpHV : p ∈ H.V
      · have hp_corr : IsCorrespondingAtom H K {p} {p} :=
          ⟨Or.inl (Or.inl ⟨p, hpHV, rfl⟩), Or.inl (Or.inl ⟨p, hK.2.1.2.1 hpHV, rfl⟩),
            Or.inl ⟨p, hpHV, rfl, rfl⟩⟩
        have hzp_lt : d z {p} < κ :=
          hdist_lt_of_inter_walkUnion (by omega) (by omega) hp_corr ⟨p, rfl, hpW⟩
        have hpr_le : d {p} r ≤ 1 := hv_reg hE p hpHV r hr hpr
        have htri' := htri z hz {p} (Or.inl (Or.inl ⟨p, hpHV, rfl⟩)) r hrA
        omega
      · -- Show `w ∈ W_κ`, so `d z r < κ`.
        have hHUK_eq : H.U ∩ K.U = H.V := hK.2.1.1
        have hwW : w ∈ W_κ := by
          by_cases hpKV : p ∈ K.V
          · have hp_in_r : p ∈ r := by
              by_contra hp_not_r
              have hpHU : p ∈ H.U := by
                by_contra hp_not_HU
                obtain ⟨r₀, hr₀, hpr₀⟩ := exists_region_of_notMem hp_not_HU
                obtain ⟨q, hqr₀, hqr⟩ := mem_closure_iff.mp hpr r₀ (region_isOpen hr₀) hpr₀
                exact hp_not_r (region_eq_of_mem hr₀ hr hqr₀ hqr ▸ hpr₀)
              have : p ∈ H.U ∩ K.U := ⟨hpHU, K.V_subset_U hpKV⟩
              rw [hHUK_eq] at this
              exact hpHV this
            have hpw : p = w :=
              GM11.hub_unique ⟨hK.1, hK.2.1⟩ hr hwr hwV hp_in_r hpKV
            exact hpw ▸ hpW
          · by_cases hpKU : p ∈ K.U
            · obtain ⟨g, hg, hpg⟩ := K.exists_edge_of_mem hpKU hpKV
              obtain ⟨v₀, -, r₀, hr₀, w₀, hw₀r, hw₀V, hcap, hsubr₀⟩ :=
                GM11.spoke_ends ⟨hK.1, hK.2.1⟩ hS hg
              obtain ⟨q, hqr₀, hqr⟩ :=
                mem_closure_iff.mp hpr r₀ (region_isOpen hr₀) (hsubr₀ hpg)
              have hr₀_eq : r₀ = r := region_eq_of_mem hr₀ hr hqr₀ hqr
              subst hr₀_eq
              have hw₀_eq : w₀ = w :=
                GM11.hub_unique ⟨hK.1, hK.2.1⟩ hr hwr hwV hw₀r hw₀V
              have hgW : g ⊆ W_κ :=
                GM11.nice_atom hWκ_nice (Or.inl (Or.inr hg)) ⟨p, hpg, hpW⟩
              have hw_clg : w ∈ closure g := by
                have : w ∈ closure g ∩ K.V := by rw [hcap, hw₀_eq]; simp
                exact this.1
              exact hWκ_cl.closure_subset_iff.mpr hgW hw_clg
            · obtain ⟨r', hr', hpr'⟩ := exists_region_of_notMem hpKU
              have hr'W : r' ⊆ W_κ :=
                GM11.nice_atom hWκ_nice (Or.inr hr') ⟨p, hpr', hpW⟩
              obtain ⟨q, hqr', hqr⟩ :=
                mem_closure_iff.mp hpr r' (region_isOpen hr') hpr'
              have hw_clr' : w ∈ closure r' :=
                hub_mem_closure_of_inter_nonempty hS hK hr hr' ⟨q, hqr, hqr'⟩ ⟨hwV, hwr⟩
              exact hWκ_cl.closure_subset_iff.mpr hr'W hw_clr'
        have hzr_lt : d z r < κ :=
          hdist_lt_of_inter_walkUnion (by omega) (by omega) hr_corr ⟨w, rfl, hwW⟩
        omega
  refine ⟨hzr_le, ?_⟩
  by_contra hnot
  have h1 := hclaim1 r hrA (by omega) hnot
  omega

private theorem circuit_edge_closures_in_enlarged_restraint
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (hS : IsClosedSurface S)
    (H : Drawing S)
    (θ : ℕ)
    (κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (z : Set S)
    (hz : z ∈ H.A)
    (hκ2 : 2 ≤ κ)
    (hκθ : κ + 3 ≤ θ)
    [this : ConnectedSpace S]
    [LocallyConnectedSpace S]
    (htri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hResp : IsRespectfulDrawingTangle H θ T)
    (K : Drawing S)
    (ins : Drawing S → Set S)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    (hsl : IsSlope K (2 * θ) ins)
    (hE : H.E.Nonempty)
    (z' : Set S)
    (hz' : IsCorrespondingAtom H K z z')
    (hz'_uniq : ∀ (y : Set S), (fun x' => IsCorrespondingAtom H K z x') y → y = z')
    (Δ : Set S)
    (hcorr_sub_walkUnion : ∀ {m : ℕ} {x x' : Set S}, m ≤ θ → IsCorrespondingAtom H K x x' → d z x
      < m → x' ⊆ z' ∪ walkUnion K ins (2 * m) z')
    (hclaim2 : ∀ r ∈ H.R, (closure r ∩ (z' ∪ walkUnion K ins (2 * κ) z')).Nonempty →
      d z r ≤ κ ∧ r ⊆ Δ \ subBd Δ)
    (C : Drawing S)
    (hCH : C.IsSubdrawing H)
    (heR : ∀ e ∈ C.E, ∃ r ∈ H.R, H.EdgeRegionIncident e r ∧
      (closure r ∩ (z' ∪ walkUnion K ins (2 * κ) z')).Nonempty)
    (hY_cl : IsClosed (walkUnion K ins (2 * (κ + 3)) z'))
    (hHUK_eq : H.U ∩ K.U = H.V) :
    ∀ e ∈ C.E, closure e ⊆ (walkUnion K ins (2 * (κ + 3)) z') := by
  let Z := z' ∪ walkUnion K ins (2 * κ) z'
  let Y := walkUnion K ins (2 * (κ + 3)) z'
  intro e heC
  obtain ⟨r, hr, hinc, hrZ⟩ := heR e heC
  have heH : e ∈ H.E := hCH.2 heC
  obtain ⟨p, hpe⟩ := heH.1
  have hpK : p ∉ K.U := by
    intro hpK
    have : p ∈ H.U ∩ K.U := ⟨(heH.2.1 hpe).1, hpK⟩
    rw [hHUK_eq] at this
    exact (heH.2.1 hpe).2 this
  obtain ⟨r', hr', hpr'⟩ := exists_region_of_notMem hpK
  have her' : e ⊆ r' :=
    subset_region hr' heH.2.2.1.isConnected.isPreconnected
      (disjoint_left.mpr fun y hye hyK => (heH.2.1 hye).2 (hHUK_eq ▸ ⟨(heH.2.1 hye).1, hyK⟩))
      hpe hpr'
  obtain ⟨q₀, hq₀e, hq₀r⟩ := hinc.2.2
  obtain ⟨q, hqr', hqr⟩ := mem_closure_iff.mp hq₀r r' (region_isOpen hr') (her' hq₀e)
  have hre_le : d r e ≤ 2 := by
    rw [hd_eq r (Or.inr hr) e (Or.inl (Or.inr heH))]
    exact tangleMetric_region_edge_le hS hResp hK hd hr heH hr' her' ⟨q, hqr, hqr'⟩
  have hzr_le : d z r ≤ κ := (hclaim2 r hr hrZ).1
  have htri' := htri z hz r (Or.inr hr) e (Or.inl (Or.inr heH))
  have hze_lt : d z e < κ + 3 := by omega
  have he_corr : IsCorrespondingAtom H K e r' :=
    ⟨Or.inl (Or.inr heH), Or.inr hr', Or.inr (Or.inl ⟨heH, hr', her'⟩)⟩
  have hr'_sub_Y : r' ⊆ Y := by
    by_cases hze : z = e
    · have hz'_eq : r' = z' := hz'_uniq r' (hze.symm ▸ he_corr)
      have hefin : (H.toHypergraph.ends e).Finite :=
        H.toHypergraph.vertexSet_finite.subset fun _ hx => H.toHypergraph.vertex_mem_of_inc hx
      have h2 := GM12.drawing_edge_ends_ncard_le_two heH
      obtain ⟨D, hD, hDs, hDl, hDV, heD⟩ :=
        GM14.exists_circuit_around_drawing_edge hS ‹_› hResp (by omega) hK hd heH
      obtain ⟨-, -, hnice⟩ := GM11.ins_slope_facts hS hsl hD hDs hDl
      obtain ⟨u, W₀, hW₀, -, hV, hE_D⟩ := id hD
      obtain ⟨W, hsu, hed⟩ := hDs.exists_walk_up W₀
      have hDeq := (circuit_length_eq_two_mul_ncard hK.2.1 hD hDs).1
      have hWlen : W.length = D.length := by
        rw [Drawing.length, hE_D, ← hed]
        have h : {f | f ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext; simp
        rw [h, ncard_coe_finset, List.toFinset_card_of_nodup (hed ▸ hW₀.2)]
        rfl
      have hDV_ends : D.V ∩ H.V ⊆ H.toHypergraph.ends e := fun x hx => (hDV hx).1
      have hncard_le : (D.V ∩ H.V).ncard ≤ 2 :=
        (ncard_le_ncard hDV_ends hefin).trans h2
      have hWlt : W.length < 2 * (κ + 3) := by omega
      have hsub : D.IsSubdrawing (walkDrawing K W) := by
        refine ⟨fun x hx => ?_, fun f hf => ?_⟩
        · rw [walkDrawing_V, hsu]
          rw [hV] at hx
          exact hx
        · rw [walkDrawing_E, hed]
          rw [hE_D] at hf
          exact hf
      have hins : ins D ⊆ insWalk ins K W := fun x hx =>
        Or.inr (mem_iUnion₂.mpr ⟨D, ⟨hD, hsub⟩, hx⟩)
      have hr'W : r' ⊆ insWalk ins K W :=
        (GM11.nice_atom hnice (Or.inr hr') ⟨p, hpr', heD hpe⟩).trans hins
      exact fun x hx => mem_iUnion₂.mpr ⟨insWalk ins K W, ⟨u, W, hWlt, hz'_eq ▸ hr'W, rfl⟩,
        hr'W hx⟩
    · have hsub := hcorr_sub_walkUnion (by omega) he_corr hze_lt
      intro x hx
      rcases hsub hx with hxz' | hxY
      · exfalso
        exact hze (correspondingAtom_inj hS hK hE hz'
          ⟨Or.inl (Or.inr heH), hz'.2.1, by
            have hr'_eq : z' = r' := by
              by_contra hne'
              exact disjoint_left.mp (disjoint_of_mem_A_ne hz'.2.1 (Or.inr hr') hne') hxz' hx
            exact hr'_eq ▸ he_corr.2.2⟩)
      · exact hxY
  exact hY_cl.closure_subset_iff.mpr (her'.trans hr'_sub_Y)

/-- Stronger internal form of Graph Minors XIV, (9.2) (page 43), also returning the bounding
circuit `C` of `H` with `subBd Λ = C.U`, `subBd (closure Λ) = C.U`, and `closure Λ \ C.U = Λ`. -/
theorem full_of_9_2
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (H : Drawing S) (θ κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S)
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A)
    (hκ2 : 2 ≤ κ) (hκθ : κ + 3 ≤ θ) :
    ∃ (C : Drawing S) (Λ : Set S),
      C.IsSubdrawing H ∧ C.IsCircuit ∧
      subBd Λ = C.U ∧ subBd (closure Λ) = C.U ∧ closure Λ \ C.U = Λ ∧
      IsLambdaZoneAround H d (κ + 2) z Λ ∧
      ∀ x ∈ H.A, d z x < κ → x ⊆ Λ := by
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have h91_prop := GM11.gm15_theorem_9_1 H θ T d hS hConn hMetric
  have hrefl := h91_prop.2.1
  have hsymm := h91_prop.2.2.2.1
  have htri := h91_prop.2.2.2.2.1
  have hv_reg := h91_prop.2.2.2.2.2.1
  obtain ⟨hResp, K, ins, hK, hd, hd_eq⟩ := hMetric
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hResp.2.1.isPretangle hK.2.1.1 hd
  have hE : H.E.Nonempty := edgeSet_nonempty_of_isTangle hResp.2.1 (by omega)
  have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  obtain ⟨z', hz', hz'_uniq⟩ := existsUnique_correspondingAtom hK hz
  obtain ⟨c, hc⟩ := atom_nonempty hz'.2.1
  -- Apply (9.1) with `κ = θ` to get a closed disc `Δ` with `walkUnion K ins (2 * θ) z' ⊆ Δ \ subBd
  -- Δ`.
  obtain ⟨Δ, hΔ, hWθ_sub⟩ := theorem_9_1_proof hS hResp hK hd (by omega) le_rfl hz'.2.1
  have hz'_sub_Wθ : z' ⊆ walkUnion K ins (2 * θ) z' :=
    atom_subset_walkUnion_of_three_le hS hResp hK hd (by omega) hz'.2.1
  have hz'_sub_Δ : z' ⊆ Δ \ subBd Δ := hz'_sub_Wθ.trans hWθ_sub
  -- Helper: if `x ∈ A(H)` and `d z x < m` (`m ≤ θ`), then the atom `x'` of `K` corresponding to `x`
  -- satisfies `x' ⊆ z' ∪ walkUnion K ins (2 * m) z'`.
  have hcorr_sub_walkUnion : ∀ {m : ℕ} {x x' : Set S}, m ≤ θ →
      IsCorrespondingAtom H K x x' → d z x < m →
      x' ⊆ z' ∪ walkUnion K ins (2 * m) z' := by
    exact close_corresponding_atom_lies_in_walk_union (S := S) H θ d z hz K ins hK hd_eq z'
      hz' hz'_uniq c hc Δ hWθ_sub hz'_sub_Wθ hz'_sub_Δ
  -- Claim (1): For every `x ∈ A(H)` with `d z x < θ`, if `¬ (x ⊆ Δ \ subBd Δ)`, then `x ∈ H.R` and
  -- `θ - 2 ≤ d z x`.
  have hclaim1 : ∀ x ∈ H.A, d z x < θ → ¬ (x ⊆ Δ \ subBd Δ) → x ∈ H.R ∧ θ - 2 ≤ d z x := by
    exact atom_outside_disc_is_distant_region (S := S) hS H θ κ T d z hz hκ2 hκθ htri hResp K
      ins hK hd hd_eq hsl hrf z' hz' c hc Δ hWθ_sub hz'_sub_Wθ hcorr_sub_walkUnion
  -- Define `Z = z' ∪ walkUnion K ins (2 * κ) z'`.
  set W_κ := walkUnion K ins (2 * κ) z'
  set Z := z' ∪ W_κ
  have hWκ_eq : W_κ = restraintUnion K ins (2 * θ) c (2 * κ - 1) :=
    walkUnion_eq_restraintUnion hS hsl hz'.2.1 hc (by omega) (by omega)
  have hWκ_cl : IsClosed W_κ := hWκ_eq ▸ GM11.isClosed_restraintUnion hS c (2 * κ - 1)
  have hWκ_nice : IsGammaNice K W_κ := hWκ_eq ▸ GM11.isGammaNice_restraintUnion c (2 * κ - 1)
  have hZne : Z.Nonempty := ⟨c, Or.inl hc⟩
  have hZconn : IsPreconnected Z := by
    exact restraint_with_selected_regions_is_preconnected (S := S) hS H θ κ z K ins hsl z' hz' c
      hWκ_eq
  -- Helper: if `x' ∈ A(K)` corresponds to `x ∈ A(H)` and `(x' ∩ W_m).Nonempty`, then `d z x < m`.
  have hdist_lt_of_inter_walkUnion : ∀ {m : ℕ} {x x' : Set S},
      1 ≤ m → m ≤ θ → IsCorrespondingAtom H K x x' →
      (x' ∩ walkUnion K ins (2 * m) z').Nonempty → d z x < m := by
    exact atom_meeting_walk_union_is_close (S := S) hS H θ d z hz hrefl K ins hK hd_eq hsl
      z' hz'
  -- Claim (2): For every `r ∈ H.R` with `(closure r ∩ Z).Nonempty`, `d z r ≤ κ` and
  -- `r ⊆ Δ \ subBd Δ`.
  have hclaim2 : ∀ r ∈ H.R, (closure r ∩ Z).Nonempty → d z r ≤ κ ∧ r ⊆ Δ \ subBd Δ := by
    exact region_meeting_restraint_is_close (S := S) hS H θ κ T d z hz hκ2 hκθ hrefl hsymm
      htri hv_reg hResp K ins hK hd hd_eq hE z' hz' hz'_uniq c hc Δ hWθ_sub hz'_sub_Wθ hz'_sub_Δ
      hcorr_sub_walkUnion hclaim1 hWκ_eq hWκ_cl hWκ_nice hZne hZconn hdist_lt_of_inter_walkUnion
  -- Apply (5.2) (`theorem_5_2_full`) to `H`, `Δ`, `Z`.
  obtain ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, hbd_clΛ, hdiffΛ, hZΛ, heR⟩ :=
    theorem_5_2_full hS H hΔ hZne hZconn (fun r hr hrZ => (hclaim2 r hr hrZ).2)
  -- Show `x ⊆ Λ` for every `x ∈ A(H)` with `d z x < κ`.
  have hx_sub_Λ : ∀ x ∈ H.A, d z x < κ → x ⊆ Λ := by
    intro x hx hlt
    obtain ⟨x', hx', -⟩ := existsUnique_correspondingAtom hK hx
    have hx'_Z : x' ⊆ Z := hcorr_sub_walkUnion (by omega) hx' hlt
    have hx'_Λ : x' ⊆ Λ := hx'_Z.trans hZΛ
    obtain ⟨q, hq⟩ := correspondingAtom_inter_nonempty hx'
    exact atom_subset_open_of_inter_nonempty hS hCH hclΛ_disc hbd_clΛ hdiffΛ hx ⟨q, hq.1,
      hx'_Λ hq.2⟩
  have hz_sub_Λ : z ⊆ Λ := hx_sub_Λ z hz (by rw [hrefl z hz]; omega)
  -- Let `Y = walkUnion K ins (2 * (κ + 3)) z'`. Show `C.U ⊆ Y` and `closure Λ ⊆ Y`.
  set Y := walkUnion K ins (2 * (κ + 3)) z'
  have hY_eq : Y = restraintUnion K ins (2 * θ) c (2 * (κ + 3) - 1) :=
    walkUnion_eq_restraintUnion hS hsl hz'.2.1 hc (by omega) (by omega)
  have hY_cl : IsClosed Y := hY_eq ▸ GM11.isClosed_restraintUnion hS c (2 * (κ + 3) - 1)
  have hY_sub_Wθ : Y ⊆ walkUnion K ins (2 * θ) z' := by
    refine iUnion₂_subset ?_
    rintro X ⟨u, W, hW, hzW, rfl⟩
    exact subset_biUnion_of_mem (u := id) ⟨u, W, by omega, hzW, rfl⟩
  have hY_sub_Δ : Y ⊆ Δ := hY_sub_Wθ.trans (hWθ_sub.trans sdiff_subset)
  have hHUK_eq : H.U ∩ K.U = H.V := hK.2.1.1
  have hCE_sub_Y : ∀ e ∈ C.E, closure e ⊆ Y := by
    exact circuit_edge_closures_in_enlarged_restraint (S := S) hS H θ κ T d z hz hκ2 hκθ htri
      hResp K ins hK hd hd_eq hsl hE z' hz' hz'_uniq Δ hcorr_sub_walkUnion hclaim2 C hCH heR hY_cl
      hHUK_eq
  have hCU_sub_Y : C.U ⊆ Y := by
    rw [C.U_eq]
    refine union_subset (fun v hv => ?_) (iUnion₂_subset hCE_sub_Y)
    obtain ⟨e, he, hve⟩ := exists_edge_closure_of_mem_circuit_U hC (C.V_subset_U hv)
    exact hCE_sub_Y e he hve
  have hO : IsOArc C.U := isOArc_of_isCircuit hC
  have hYne : Y.Nonempty := (IsOArc.nonempty hO).mono hCU_sub_Y
  have hYsc : IsSimplyConnectedSet Y :=
    hY_eq ▸ GM11.theorem_8_10_proof hS hsl (hY_eq ▸ hYne)
  have hnull : IsNullHomotopicOArcIn Y C.U := by
    obtain ⟨ψ⟩ := id hO
    refine ⟨ψ, hYsc.2 _ ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hCU_sub_Y (ψ x).2
  obtain ⟨Δ₁, hΔ₁Y, hd₁, hb₁⟩ := GM11.theorem_7_2_proof hS hO hCU_sub_Y hnull
  have hb₁' : discBd Δ₁ = C.U := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hd₁, hb₁]
  have hb₂' : discBd (closure Λ) = C.U := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hclΛ_disc, hbd_clΛ]
  have hclΛ_eq_Δ₁ : closure Λ = Δ₁ := by
    by_contra hne_eq
    have hcov : closure Λ ∪ Δ₁ = univ :=
      cover_of_discBd_eq hS hclΛ_disc hd₁ (hb₂'.trans hb₁'.symm) hne_eq
    have hΔ_univ : Δ = univ :=
      subset_antisymm (subset_univ _)
        (hcov ▸ union_subset hclΛ_sub (hΔ₁Y.trans hY_sub_Δ))
    obtain ⟨q, hq⟩ := IsOArc.nonempty hΔ.isOArc_discBd
    rw [← IsClosedDisc.frontier_eq_discBd hS hΔ, hΔ_univ, frontier_univ] at hq
    exact hq
  have hclΛ_sub_Y : closure Λ ⊆ Y := hclΛ_eq_Δ₁ ▸ hΔ₁Y
  have hZone : IsLambdaZoneAround H d (κ + 2) z Λ := by
    refine ⟨hz, hOpenΛ, hz_sub_Λ, hbdΛ ▸ hO, hclΛ_disc, hbdΛ ▸ hCH.U_subset, ?_, fun _ => by omega⟩
    intro x hx hx_cl
    obtain ⟨x', hx', -⟩ := existsUnique_correspondingAtom hK hx
    obtain ⟨q, hqx, hqx'⟩ := correspondingAtom_inter_nonempty hx'
    have hlt : d z x < κ + 3 :=
      hdist_lt_of_inter_walkUnion (by omega) (by omega) hx' ⟨q, hqx', hclΛ_sub_Y (hx_cl hqx)⟩
    omega
  exact ⟨C, Λ, hCH, hC, hbdΛ, hbd_clΛ, hdiffΛ, hZone, hx_sub_Λ⟩

/-- **Graph Minors XIV, (9.2)** (page 43), proving `GM16.GM14Theorem92Statement`:
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$
of order $\theta$, with metric $d$. Let $z \in A(H)$ and let $\kappa$ be an integer with $2
\le \kappa \le \theta - 3$. Then there is a $(\kappa + 2)$-zone $\Lambda$ around $z$ such
that $x \subseteq \Lambda$ for every $x \in A(H)$ with $d(z, x) < \kappa$." -/
theorem theorem_9_2_proof :
    GM16.GM14Theorem92Statement.{w} := by
  intro S _ _ H θ κ T d z hS hConn hMetric hz hκ2 hκθ
  obtain ⟨_, Λ, -, -, -, -, -, hZone, hx_sub⟩ :=
    full_of_9_2 hS hConn H θ κ T d z hMetric hz hκ2 hκθ
  exact ⟨Λ, hZone, hx_sub⟩

/-! ## 3. Proof of (9.4) (page 45) -/

/-- **Graph Minors XIV, (9.4)** (page 45):
"Let $H$ be a 2-cell drawing in $\Sigma$, let $z \in A(H)$, and let $\mathscr{T}$ be a respectful
tangle in $H$ of order $\theta$, with metric $d$. Let $1 \le \kappa \le \theta - 7$, and let
$\Lambda$ be a $\kappa$-zone around $z$, including every $x \in A(H)$ with $d(z, x) \le 3$. Let $H$
be a subgraph of $G$, let $\mathscr{S}$ be a $\mathscr{T}$-local 3-segregation of $G$, and let
$\alpha$ be an arrangement of $\mathscr{S}$ in $\Sigma$ compatible with $H$. Then there is a closed
disc $\Delta \subseteq \Sigma$ such that $\Lambda \subseteq \Delta$, $bd(\Delta)$ is
$\alpha$-normal, $H \cap \Sigma - \Delta$ has a circuit, and $d(z, x) \le \kappa + 3$ for all $x
\in A(H)$ with $x \cap \Delta \ne \emptyset$." -/
theorem theorem_9_4_proof
    [T2Space S] (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {α : Type v} {β : Type w}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ κ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Λ : Set S}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hMetric : HasTangleMetric H θ T d) (hz : z ∈ H.A)
    (hκ1 : 1 ≤ κ) (hκθ : κ + 7 ≤ θ)
    (hZone : IsLambdaZoneAround H d κ z Λ)
    (hΛ_le3 : ∀ x ∈ H.A, d z x ≤ 3 → x ⊆ Λ)
    (hSeg : IsThreeSegregation G S_seg) (hLoc : IsTangleLocal G H η T S_seg)
    (hArr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hComp : IsCompatibleWith G H η S_seg α_disc α_pt) :
    ∃ (F Δ : Set S) (C_out : Drawing S),
      IsOArc F ∧ IsArrangementNormal S_seg α_disc α_pt F ∧
      IsClosedDisc Δ ∧ subBd Δ = F ∧ closure Λ ⊆ Δ ∧
      C_out.IsCircuit ∧ C_out.IsSubdrawing (H.interSet (closure (univ \ Δ))) ∧
      C_out.IsSubdrawing (clearedSubdrawing H Δ) ∧
      ∀ x ∈ H.A, (x ∩ Δ).Nonempty → d z x ≤ κ + 3 := by
  have : ConnectedSpace S := hConn
  -- Apply (9.2) with `κ + 1` to obtain a `(κ + 3)`-zone `Λ₁` around `z`.
  obtain ⟨C₁, Λ₁, hC₁H, hC₁, hbdΛ₁, hbd_clΛ₁, hdiffΛ₁, hZone₁, hx_sub_Λ₁⟩ :=
    full_of_9_2 hS hConn H θ (κ + 1) T d z hMetric hz (by omega) (by omega)
  -- Apply (9.2) with `κ + 4` to obtain a `(κ + 6)`-zone `Λ₂` around `z` with `closure Λ₁ ⊆ Λ₂`.
  obtain ⟨C_out, Λ₂, hCoutH, hCout, hbdΛ₂, hbd_clΛ₂, hdiffΛ₂, hZone₂, hx_sub_Λ₂⟩ :=
    full_of_9_2 hS hConn H θ (κ + 4) T d z hMetric hz (by omega) (by omega)
  have hclΛ_sub_Λ₁ : closure Λ ⊆ Λ₁ :=
    closure_zone_subset hS hZone (fun x hx hle => hx_sub_Λ₁ x hx (by omega))
  have hclΛ₁_sub_Λ₂ : closure Λ₁ ⊆ Λ₂ :=
    closure_zone_subset hS hZone₁ (fun x hx hle => hx_sub_Λ₂ x hx (by omega))
  -- Obtain the circuit `C₂ = H ∩ bd(Λ)` of `H` bounding `closure Λ`.
  obtain ⟨C₂, hC₂, hC₂H, hC₂U⟩ := GM11.exists_circuit_of_oArc hZone.isOArc_bd hZone.bd_subset_U
  have hbd_clΛ : subBd (closure Λ) = C₂.U := by
    rw [IsClosedDisc.subBd_eq_discBd hS hZone.isClosedDisc_closure,
      discBd_closure_eq_subBd hS hZone.isOpenDisc hZone.isOArc_bd hZone.isClosedDisc_closure, hC₂U]
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
  have hdiffΛ : closure Λ \ subBd (closure Λ) = Λ := by
    rw [hbd_clΛ, hC₂U]
    ext y
    exact ⟨fun ⟨hycl, hynot⟩ => (hclL ▸ hycl).resolve_right hynot,
      fun hy => ⟨subset_closure hy, disjoint_left.mp hdisL hy⟩⟩
  have hdisj_C₁_C₂ : Disjoint C₁.V C₂.V := by
    refine disjoint_left.mpr fun v hv₁ hv₂ => ?_
    have hv_clΛ : v ∈ closure Λ := by
      have h1 : v ∈ subBd (closure Λ) := hbd_clΛ ▸ C₂.V_subset_U hv₂
      have h2 := h1.1
      rwa [closure_closure] at h2
    have hv_Λ₁ : v ∈ Λ₁ := hclΛ_sub_Λ₁ hv_clΛ
    rw [← hdiffΛ₁] at hv_Λ₁
    exact hv_Λ₁.2 (C₁.V_subset_U hv₁)
  -- Apply (7.7) (`theorem_7_7_proof`) to `Δ₁ = closure Λ₁` and `Δ₂ = closure Λ`.
  obtain ⟨F, Δ, hFO, -, hFnorm, hΔdisc, hbdΔ, hΔ_sub_clΛ₁, hclΛ_sub_Δ⟩ :=
    theorem_7_7_proof hS hConn (by omega) hMetric hz
      hZone₁.isClosedDisc_closure hZone.isClosedDisc_closure
      (hZone.z_subset.trans (by rw [hdiffΛ]))
      (hclΛ_sub_Λ₁.trans (by rw [hbd_clΛ₁, hdiffΛ₁]))
      (fun x hx hx_sub => (hZone₁.dist_le x hx hx_sub).trans (by omega))
      (fun x hx hle => (hΛ_le3 x hx hle).trans (by rw [hdiffΛ]))
      hC₁ hC₁H hbd_clΛ₁ hC₂ hC₂H hbd_clΛ hdisj_C₁_C₂
      hSeg hLoc hArr hComp
  -- Show `C_out.U ⊆ univ \ Δ ⊆ closure (univ \ Δ)`.
  have hCout_disj_Δ : C_out.U ⊆ univ \ Δ := by
    intro y hy
    refine ⟨mem_univ y, fun hyΔ => ?_⟩
    have hyΛ₂ : y ∈ Λ₂ := hclΛ₁_sub_Λ₂ (hΔ_sub_clΛ₁ hyΔ)
    rw [← hdiffΛ₂] at hyΛ₂
    exact hyΛ₂.2 hy
  have hCout_sub_cl : C_out.IsSubdrawing (H.interSet (closure (univ \ Δ))) := by
    refine ⟨fun v hv => ?_, fun e he => ?_⟩
    · exact GM11.mem_interSet_V (hCoutH.1 hv) (subset_closure (hCout_disj_Δ (C_out.V_subset_U hv)))
    · rw [GM11.mem_interSet_E_iff]
      exact ⟨hCoutH.2 he,
        (subset_closure.trans (C_out.closure_subset_U he)).trans
          (hCout_disj_Δ.trans subset_closure)⟩
  have hCout_sub_cleared : C_out.IsSubdrawing (clearedSubdrawing H Δ) := by
    refine ⟨fun v hv => ?_, fun e he => ?_⟩
    · exact GM11.mem_interSet_V (hCoutH.1 hv) (hCout_disj_Δ (C_out.V_subset_U hv))
    · rw [clearedSubdrawing, GM11.mem_interSet_E_iff]
      exact ⟨hCoutH.2 he,
        (subset_closure.trans (C_out.closure_subset_U he)).trans hCout_disj_Δ⟩
  refine ⟨F, Δ, C_out, hFO, hFnorm, hΔdisc, hbdΔ, hclΛ_sub_Δ, hCout, hCout_sub_cl,
    hCout_sub_cleared, ?_⟩
  intro x hx hne
  have hx_clΛ₁ : x ⊆ closure Λ₁ :=
    atom_subset_closure_of_inter_nonempty hS hC₁H hZone₁.isClosedDisc_closure hbd_clΛ₁ hdiffΛ₁ hx
      (hne.mono (inter_subset_inter_right x hΔ_sub_clΛ₁))
  exact hZone₁.dist_le x hx hx_clΛ₁

end GraphMinor.GM14
