/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM11.Section5b
import LeanPool.GraphMinor.GM11.ForestRegions
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# Graph Minors XIV, Section 5: Circuits in Cylinders

This file formalizes Section 5 (pages 31–32) of Robertson and Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B 65 (1995), 23–50. The
formal statements use connected closed surfaces:

- `theorem_5_1_proof` ((5.1), page 31): Given a nonempty connected set `R_set` of regions of `H`
  in the interior `Δ \ bd(Δ)` of a closed disc `Δ`, there is a circuit `C` of `H` with `U(C) ⊆ Δ`
  bounding an open disc `Λ ⊆ Δ` that includes every member of `R_set`. Every edge of `C` is
  incident with some member of `R_set`.
- `theorem_5_2_proof` ((5.2), page 31): Given a nonempty arc-wise connected
  subset `Z ⊆ Δ \ bd(Δ)` such that every region `r` of `H` with `closure r ∩ Z ≠ ∅` satisfies
  `r ⊆ Δ \ bd(Δ)`, there is a circuit `C` of `H` with `U(C) ⊆ Δ` bounding an open disc `Λ ⊆ Δ`
  including `Z`, with every edge of `C` incident with a region `r` satisfying `closure r ∩ Z ≠ ∅`.
- `theorem_5_3_proof` ((5.3), page 32): A circuit around `Z` reduces the regional distance
  to `Σ \ Δ` by at most `1`.
- `theorem_5_4_proof` ((5.4), page 32): `k - 1` disjoint circuits in `Δ` bound open discs
  including `Z` when the regional distance between `Z` and `Σ \ Δ` is at least `k ≥ 2`.
- `theorem_5_5_step` and `theorem_5_5_proof` ((5.5), page 32): Single-step and
  `(k - 1)`-circuit versions in `Δ \ bd(Δ)` when the regional distance between `Z` and
  `bd(Δ)` is at least `k ≥ 1`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Preliminaries on Regions, Arc-Connectedness, and Closed Discs -/

/-- An arc-connected subset `Z ⊆ S` is preconnected. -/
theorem IsArcConnected.isPreconnected {Z : Set S} (hZ : IsArcConnected Z) : IsPreconnected Z := by
  refine isPreconnected_of_forall_pair fun a ha b hb => ?_
  by_cases hab : a = b
  · exact ⟨{a}, singleton_subset_iff.mpr ha, mem_singleton a, hab ▸ mem_singleton a,
      isPreconnected_singleton⟩
  · obtain ⟨L, hLZ, f, hf0, hf1⟩ := hZ a ha b hb hab
    have hLconn : IsPreconnected L := by
      have hEq : Subtype.val '' (range f) = L := by
        rw [f.surjective.range_eq]
        simp
      rw [← hEq, ← range_comp, ← image_univ]
      exact isPreconnected_univ.image _ (continuous_subtype_val.comp f.continuous).continuousOn
    exact ⟨L, hLZ, hf0 ▸ (f 0).2, hf1 ▸ (f 1).2, hLconn⟩

/-- A closed disc `D ⊆ S` is nonempty and preconnected. -/
theorem IsClosedDisc.nonempty {D : Set S} (hD : IsClosedDisc D) : D.Nonempty := by
  obtain ⟨f⟩ := hD
  have h0 : (0 : EuclideanPlane) ∈ ClosedUnitDisc := by simp [ClosedUnitDisc]
  exact ⟨(f ⟨0, h0⟩).1, (f ⟨0, h0⟩).2⟩

theorem IsClosedDisc.isPreconnected {D : Set S} (hD : IsClosedDisc D) : IsPreconnected D := by
  obtain ⟨f⟩ := hD
  have hc : IsPreconnected ClosedUnitDisc := by
    have : ClosedUnitDisc = Metric.closedBall (0 : EuclideanPlane) 1 := by
      ext x; simp [ClosedUnitDisc]
    rw [this]
    exact (convex_closedBall (0 : EuclideanPlane) 1).isPreconnected
  have : PreconnectedSpace ClosedUnitDisc := isPreconnected_iff_preconnectedSpace.mp hc
  have hEq : Subtype.val '' (range f) = D := by
    rw [f.surjective.range_eq]
    simp
  rw [← hEq, ← range_comp, ← image_univ]
  exact isPreconnected_univ.image _ (continuous_subtype_val.comp f.continuous).continuousOn

/-- In a drawing `H` on a connected closed surface `S`, every point of `S` lies in the closure of
some region of `H`. -/
private theorem exists_region_closure_mem [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) (x : S) :
    ∃ r ∈ H.R, x ∈ closure r := by
  have : T2Space S := hS.2.1
  have hfin : H.R.Finite := finite_R hS H
  by_contra hnot
  push Not at hnot
  have hcl : IsClosed (⋃ r ∈ H.R, closure r) :=
    hfin.isClosed_biUnion fun r _ => isClosed_closure
  have hx : x ∈ (⋃ r ∈ H.R, closure r)ᶜ := by
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    exact hnot
  obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := H) hS hcl.isOpen_compl ⟨x, hx⟩
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
  exact hyO (mem_iUnion₂.mpr ⟨r, hr, subset_closure hyr⟩)

/-! ## 2. Proof of (5.1) (page 31) -/

/-- Closed-surface form of Graph Minors XIV (5.1) (page 31):
"Let $H$ be a drawing in a surface $\Sigma$, and let $\Delta \subseteq \Sigma$ be a closed
disc. Let $\mathscr{R}$ be a non-empty connected set of regions of $H$, such that $r
\subseteq \Delta - \text{bd}(\Delta)$ for all $r \in \mathscr{R}$. Then there is a circuit
$C$ of $H$ with $U(C) \subseteq \Delta$, bounding a disc in $\Delta$ including each member
of $\mathscr{R}$, and such that every edge of $C$ is incident with a member of
$\mathscr{R}$." -/
theorem theorem_5_1_proof [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {R_set : Set (Set S)} (hne : R_set.Nonempty) (hconn : IsConnectedRegionSet H R_set)
    (hsub : ∀ r ∈ R_set, r ⊆ Δ \ subBd Δ) :
    ∃ (C : Drawing S) (Λ : Set S),
      C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ ∧
      IsOpenDisc Λ ∧ closure Λ ⊆ Δ ∧ IsClosedDisc (closure Λ) ∧
      subBd Λ = C.U ∧ subBd (closure Λ) = C.U ∧ closure Λ \ C.U = Λ ∧
      (∀ r ∈ R_set, r ⊆ Λ) ∧
      ∀ e ∈ C.E, ∃ r ∈ R_set, H.EdgeRegionIncident e r := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hΔcl : IsClosed Δ := hΔ.isCompact.isClosed
  set N := boundaryDrawing H R_set with hN
  have hNs : N.IsSubdrawing H := Drawing.span_isSubdrawing H _ _
  have hNE_sub : ∀ e ∈ N.E, closure e ⊆ Δ := by
    intro e he
    obtain ⟨⟨r, hrR, hinc⟩, -⟩ := (mem_boundaryDrawing_E (Γ := H)).mp he
    have hes : e ⊆ closure r :=
      edge_subset_closure_of_incident hS (hNs.2 he) (hconn.1 hrR) hinc.2.2
    have hrΔ : closure r ⊆ Δ := hΔcl.closure_subset_iff.mpr ((hsub r hrR).trans sdiff_subset)
    exact (closure_minimal hes isClosed_closure).trans hrΔ
  have hNU : N.U ⊆ Δ := by
    rw [N.U_eq]
    refine union_subset ?_ (iUnion₂_subset hNE_sub)
    intro v hv
    obtain ⟨⟨r, hrR, hinc⟩, -⟩ :=
      (mem_boundaryDrawing_V (Γ := H) hS).mp hv
    exact hΔcl.closure_subset_iff.mpr ((hsub r hrR).trans sdiff_subset) hinc.2.2
  let k : ℕ := N.E.ncard + 2
  have hk : 2 ≤ k := Nat.le_add_left 2 _
  have hs : IsSlope N k (discIns Δ) := isSlope_discIns hS hΔ hNU hk
  have hconf : IsConfined k N := by
    intro C _ hCs
    change C.E.ncard < N.E.ncard + 2
    have hle : C.E.ncard ≤ N.E.ncard := Set.ncard_le_ncard hCs.2 N.finite_edges
    omega
  obtain ⟨r₁, hr₁⟩ := hne
  obtain ⟨r', hr', hr₁'⟩ := exists_region_superset hNs (hconn.1 hr₁)
  have hstep : ∀ a b : Set S, a ∈ R_set → b ∈ R_set →
      (∃ e ∈ H.E, H.EdgeRegionIncident e a ∧ H.EdgeRegionIncident e b) → a ⊆ r' → b ⊆ r' := by
    rintro a b ha hb ⟨e, heH, hia, hib⟩ har'
    by_cases hab : a = b
    · exact hab ▸ har'
    · have heN : e ∉ N.E := by
        intro heN
        obtain ⟨-, c, ⟨hcR, hcnot⟩, hic⟩ := (mem_boundaryDrawing_E (Γ := H)).mp heN
        have hea := edge_subset_closure_of_incident hS heH (hconn.1 ha) hia.2.2
        have heb := edge_subset_closure_of_incident hS heH (hconn.1 hb) hib.2.2
        have hec := edge_subset_closure_of_incident hS heH hcR hic.2.2
        rcases region_incident_two hS heH (hconn.1 ha) (hconn.1 hb) hcR
          hea heb hec with h | h | h
        · exact hab h
        · exact hcnot (h ▸ ha)
        · exact hcnot (h ▸ hb)
      have hea := edge_subset_closure_of_incident hS heH (hconn.1 ha) hia.2.2
      have heb := edge_subset_closure_of_incident hS heH (hconn.1 hb) hib.2.2
      obtain ⟨p, hp⟩ := heH.1
      have hpNU : p ∉ N.U := by
        intro hpU
        have hpV : p ∉ N.V := fun hpV => (heH.2.1 hp).2 (hNs.1 hpV)
        obtain ⟨f, hfN, hpf⟩ := N.exists_edge_of_mem hpU hpV
        have hfe := H.edge_eq_of_mem (hNs.2 hfN) heH hpf hp
        exact heN (hfe ▸ hfN)
      obtain ⟨rp, hrp, hprp⟩ := exists_region_of_notMem hpNU
      obtain ⟨x, hxr, hxa⟩ := mem_closure_iff.mp (hea hp) rp (region_isOpen hrp) hprp
      have hrp_eq : rp = r' := region_eq_of_mem hrp hr' hxr (har' hxa)
      have hpr' : p ∈ r' := hrp_eq ▸ hprp
      obtain ⟨y, hyr', hyb⟩ := mem_closure_iff.mp (heb hp) r' (region_isOpen hr') hpr'
      refine subset_region hr' (region_isPreconnected (hconn.1 hb)) ?_ hyb hyr'
      exact disjoint_left.mpr fun z hz hzN => region_subset (hconn.1 hb) hz (hNs.U_subset hzN)
  have hall_r' : ∀ r ∈ R_set, r ⊆ r' := by
    intro r hr
    have hrel := hconn.2 r₁ hr₁ r hr
    clear hr
    induction hrel with
    | refl => exact hr₁'
    | @tail a b _ hab ih =>
      exact hstep a b hab.1 hab.2.1 hab.2.2 ih
  have hr₀ : univ \ insOf (discIns Δ) N ∈ N.R :=
    GM11.theorem_4_4_proof hS hs (Drawing.IsSubdrawing.refl N) hconf
  set r₀ := univ \ insOf (discIns Δ) N
  have hins_sub : insOf (discIns Δ) N ⊆ Δ := by
    refine union_subset hNU (iUnion₂_subset ?_)
    rintro C ⟨hC, hCs⟩
    exact (discIns_spec hΔ hC (hCs.U_subset.trans hNU)).1.1
  have hcompl_ne : Δᶜ.Nonempty := by
    obtain ⟨f⟩ := hΔ.isOArc_discBd
    have hbd_ne : (discBd Δ).Nonempty := ⟨(f 1).1, (f 1).2⟩
    obtain ⟨w, hw⟩ := hbd_ne
    rw [← IsClosedDisc.frontier_eq_discBd hS hΔ] at hw
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_eq_univ_sdiff, sdiff_eq_empty] at hemp
    have hΔuniv : Δ = univ := subset_antisymm (subset_univ _) hemp
    rw [hΔuniv, frontier_univ] at hw
    exact hw
  obtain ⟨y, hyΔ, hyHU⟩ := exists_notMem_U (Γ := H) hS
    hΔcl.isOpen_compl hcompl_ne
  obtain ⟨r_out, hr_out, hy_out⟩ := exists_region_of_notMem hyHU
  have hr_out_not : r_out ∉ R_set := fun h => hyΔ ((hsub r_out h hy_out).1)
  have hy_r₀ : y ∈ r₀ := ⟨mem_univ y, fun h => hyΔ (hins_sub h)⟩
  have hr_out_r₀ : r_out ⊆ r₀ := by
    refine subset_region hr₀ (region_isPreconnected hr_out) ?_ hy_out hy_r₀
    exact disjoint_left.mpr fun z hz hzN => region_subset hr_out hz (hNs.U_subset hzN)
  have hne_r' : r' ≠ r₀ := by
    intro heq
    obtain ⟨e, -, heN, a, b, haR, hbR, -, -, hia, hib⟩ :=
      GM11.theorem_5_1_proof hS hNs hr₀ (hconn.1 hr₁) hr₁ hr_out hr_out_not
        (heq ▸ hr₁') hr_out_r₀
    exact heN ((mem_boundaryDrawing_E (Γ := H)).mpr ⟨⟨a, haR, hia⟩, b, ⟨hib.2.1, hbR⟩, hib⟩)
  have hnot_r₀ : ¬ Captures (discIns Δ) k N r₀ := by
    rintro ⟨C, hC, hCs, -, hin⟩
    exact hy_r₀.2 (Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hin hy_r₀⟩))
  have hcap : Captures (discIns Δ) k N r' := by
    rcases captures_of_ne hS hs (Drawing.IsSubdrawing.refl N) hconf
      hr' hr₀ hne_r' with h | h
    · exact h
    · exact absurd h hnot_r₀
  obtain ⟨C, hC, hCs, -, hr'_sub⟩ := hcap
  have hCH : C.IsSubdrawing H := hCs.trans hNs
  have hCU : C.U ⊆ Δ := hCs.U_subset.trans hNU
  obtain ⟨⟨hDΔ, hDdisc, hDbd⟩, -⟩ := discIns_spec hΔ hC hCU
  have hDsubBd : subBd (discIns Δ C) = C.U := by
    rw [IsClosedDisc.subBd_eq_discBd hS hDdisc, hDbd]
  obtain ⟨hOpenΛ, hclΛ, hbdΛ⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hDdisc
  refine ⟨C, discIns Δ C \ subBd (discIns Δ C), hCH, hC, hCU, hOpenΛ,
    hclΛ.symm ▸ hDΔ, hclΛ.symm ▸ hDdisc, hbdΛ.trans hDsubBd,
    hclΛ.symm ▸ hDsubBd, by rw [hclΛ, hDsubBd], ?_, ?_⟩
  · intro r hr x hxr
    refine ⟨hr'_sub (hall_r' r hr hxr), ?_⟩
    rw [hDsubBd]
    exact fun hxC => region_subset (hconn.1 hr) hxr (hCH.U_subset hxC)
  · intro e he
    obtain ⟨⟨r, hrR, hinc⟩, -⟩ := (mem_boundaryDrawing_E (Γ := H)).mp (hCs.2 he)
    exact ⟨r, hrR, hinc⟩

/-! ## 3. Proof of (5.2) (page 31) -/

/-- If every region `r ∈ H.R` whose closure meets `Z` is contained in a closed set `D`, then
`Z ⊆ interior D`. -/
private theorem subset_interior_of_regions_subset [ConnectedSpace S] (hS : IsClosedSurface S)
    {H : Drawing S} {Z D : Set S} (hD : IsClosed D)
    (hrD : ∀ r ∈ H.R, (closure r ∩ Z).Nonempty → r ⊆ D) :
    Z ⊆ interior D := by
  have : T2Space S := hS.2.1
  let R_set : Set (Set S) := {r ∈ H.R | (closure r ∩ Z).Nonempty}
  let K : Set S := ⋃ r ∈ H.R \ R_set, closure r
  have hfin : (H.R \ R_set).Finite := (finite_R hS H).subset sdiff_subset
  have hK : IsClosed K := hfin.isClosed_biUnion fun r _ => isClosed_closure
  have hZK : Z ⊆ Kᶜ := by
    intro z hz hzK
    obtain ⟨r, ⟨hrR, hrnot⟩, hzr⟩ := mem_iUnion₂.mp hzK
    exact hrnot ⟨hrR, z, hzr, hz⟩
  have hKD : Kᶜ ⊆ D := by
    intro w hwK
    by_contra hwD
    obtain ⟨y, ⟨hyK, hyD⟩, hyU⟩ := exists_notMem_U (Γ := H) hS
      (hK.isOpen_compl.sdiff hD) ⟨w, hwK, hwD⟩
    obtain ⟨r, hrR, hyr⟩ := exists_region_of_notMem hyU
    by_cases hrZ : (closure r ∩ Z).Nonempty
    · exact hyD (hrD r hrR hrZ hyr)
    · exact hyK (mem_iUnion₂.mpr ⟨r, ⟨hrR, fun h => hrZ h.2⟩, subset_closure hyr⟩)
  exact hZK.trans (interior_maximal hKD hK.isOpen_compl)

/-- The set of regions `r` of `H` whose closure meets a preconnected set `Z` is connected
in the sense of Section 5 (page 31). -/
private theorem isConnectedRegionSet_of_isPreconnected [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Z : Set S} (hZ : IsPreconnected Z) :
    IsConnectedRegionSet H {r ∈ H.R | (closure r ∩ Z).Nonempty} := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let R_set : Set (Set S) := {r ∈ H.R | (closure r ∩ Z).Nonempty}
  refine ⟨fun _ h => h.1, fun r₀ hr₀ r_t hr_t => ?_⟩
  let Adj : Set S → Set S → Prop := fun r₁ r₂ =>
    r₁ ∈ R_set ∧ r₂ ∈ R_set ∧ ∃ e ∈ H.E, H.EdgeRegionIncident e r₁ ∧ H.EdgeRegionIncident e r₂
  let R₁ : Set (Set S) := {r ∈ R_set | Relation.ReflTransGen Adj r₀ r}
  let R₂ : Set (Set S) := R_set \ R₁
  by_contra hnot
  have hr_t₂ : r_t ∈ R₂ := ⟨hr_t, fun h => hnot h.2⟩
  have hr₀₁ : r₀ ∈ R₁ := ⟨hr₀, Relation.ReflTransGen.refl⟩
  have hfinR : H.R.Finite := finite_R hS H
  let K₁ : Set S := ⋃ r ∈ R₁, closure r
  let K₂ : Set S := ⋃ r ∈ R₂, closure r
  let K₃ : Set S := ⋃ r ∈ H.R \ R_set, closure r
  have hR₁fin : R₁.Finite := hfinR.subset fun _ h => h.1.1
  have hR₂fin : R₂.Finite := hfinR.subset fun _ h => h.1.1
  have hK₁ : IsClosed K₁ := hR₁fin.isClosed_biUnion fun _ _ => isClosed_closure
  have hK₂ : IsClosed K₂ := hR₂fin.isClosed_biUnion fun _ _ => isClosed_closure
  have hK₃ : IsClosed K₃ :=
    (hfinR.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  have hcov_univ : ∀ x : S, x ∉ K₃ → x ∈ K₁ ∪ K₂ := by
    intro x hxK₃
    obtain ⟨r, hrR, hxr⟩ := exists_region_closure_mem hS H x
    by_cases hr_in : r ∈ R_set
    · by_cases hr₁ : r ∈ R₁
      · exact Or.inl (mem_iUnion₂.mpr ⟨r, hr₁, hxr⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨r, ⟨hr_in, hr₁⟩, hxr⟩)
    · exact absurd (mem_iUnion₂.mpr ⟨r, ⟨hrR, hr_in⟩, hxr⟩) hxK₃
  have hinter_V : K₁ ∩ K₂ ⊆ H.V := by
    rintro x ⟨hx₁, hx₂⟩
    by_contra hxV
    obtain ⟨a, ha₁, hxa⟩ := mem_iUnion₂.mp hx₁
    obtain ⟨b, hb₂, hxb⟩ := mem_iUnion₂.mp hx₂
    by_cases hxU : x ∈ H.U
    · obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxU hxV
      have hia : H.EdgeRegionIncident e a := ⟨he, ha₁.1.1, x, hxe, hxa⟩
      have hib : H.EdgeRegionIncident e b := ⟨he, hb₂.1.1, x, hxe, hxb⟩
      exact hb₂.2 ⟨hb₂.1, Relation.ReflTransGen.tail ha₁.2 ⟨ha₁.1, hb₂.1, e, he, hia, hib⟩⟩
    · obtain ⟨s, hs, hxs⟩ := exists_region_of_notMem hxU
      obtain ⟨y₁, hy₁s, hy₁a⟩ := mem_closure_iff.mp hxa s (region_isOpen hs) hxs
      obtain ⟨y₂, hy₂s, hy₂b⟩ := mem_closure_iff.mp hxb s (region_isOpen hs) hxs
      have has : a = s := region_eq_of_mem ha₁.1.1 hs hy₁a hy₁s
      have hbs : b = s := region_eq_of_mem hb₂.1.1 hs hy₂b hy₂s
      exact hb₂.2 (hbs.trans has.symm ▸ ha₁)
  have hZK₃ : ∀ z ∈ Z, z ∉ K₃ := by
    intro z hz hzK₃
    obtain ⟨r, ⟨hrR, hrnot⟩, hzr⟩ := mem_iUnion₂.mp hzK₃
    exact hrnot ⟨hrR, z, hzr, hz⟩
  have hZ_cov : Z ⊆ K₁ᶜ ∪ K₂ᶜ := by
    intro v hvZ
    rw [mem_union, mem_compl_iff, mem_compl_iff, ← not_and_or]
    rintro ⟨hv₁, hv₂⟩
    have hvV : v ∈ H.V := hinter_V ⟨hv₁, hv₂⟩
    have hvK₃ : v ∈ K₃ᶜ := hZK₃ v hvZ
    have hV_cl : IsClosed (H.V \ {v}) := (H.finite_V.subset sdiff_subset).isClosed
    have hO : IsOpen (K₃ᶜ \ (H.V \ {v})) := hK₃.isOpen_compl.sdiff hV_cl
    have hvO : v ∈ K₃ᶜ \ (H.V \ {v}) := ⟨hvK₃, fun h => h.2 rfl⟩
    obtain ⟨W, hWopen, hvW, hWO, hWconn, -⟩ := exists_punctured_nbhd hS hO hvO
    have hW_cov : W \ {v} ⊆ K₁ᶜ ∪ K₂ᶜ := by
      rintro y ⟨hyW, hyv⟩
      rw [mem_union, mem_compl_iff, mem_compl_iff, ← not_and_or]
      rintro ⟨hy₁, hy₂⟩
      exact (hWO hyW).2 ⟨hinter_V ⟨hy₁, hy₂⟩, hyv⟩
    have hW_disj : (W \ {v}) ∩ (K₁ᶜ ∩ K₂ᶜ) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_compl_iff, mem_empty_iff_false,
        iff_false, not_and]
      intro hy hy₁ hy₂
      rcases hcov_univ y (hWO hy.1).1 with h | h
      · exact hy₁ h
      · exact hy₂ h
    rcases (isPreconnected_iff_subset_of_disjoint.mp hWconn) K₁ᶜ K₂ᶜ
      hK₁.isOpen_compl hK₂.isOpen_compl hW_cov hW_disj with hsub₁ | hsub₂
    · obtain ⟨a, ha₁, hva⟩ := mem_iUnion₂.mp hv₁
      obtain ⟨y, hyW, hya⟩ := mem_closure_iff.mp hva W hWopen hvW
      have hyv : y ≠ v := fun h => region_subset ha₁.1.1 hya (H.V_subset_U (h ▸ hvV))
      exact hsub₁ ⟨hyW, hyv⟩ (mem_iUnion₂.mpr ⟨a, ha₁, subset_closure hya⟩)
    · obtain ⟨b, hb₂, hvb⟩ := mem_iUnion₂.mp hv₂
      obtain ⟨y, hyW, hyb⟩ := mem_closure_iff.mp hvb W hWopen hvW
      have hyv : y ≠ v := fun h => region_subset hb₂.1.1 hyb (H.V_subset_U (h ▸ hvV))
      exact hsub₂ ⟨hyW, hyv⟩ (mem_iUnion₂.mpr ⟨b, hb₂, subset_closure hyb⟩)
  have hZ_disj : Z ∩ (K₁ᶜ ∩ K₂ᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzZ hz₁ hz₂
    rcases hcov_univ z (hZK₃ z hzZ) with h | h
    · exact hz₁ h
    · exact hz₂ h
  rcases (isPreconnected_iff_subset_of_disjoint.mp hZ) K₁ᶜ K₂ᶜ
    hK₁.isOpen_compl hK₂.isOpen_compl hZ_cov hZ_disj with hZ₁ | hZ₂
  · obtain ⟨z₀, hz₀r, hz₀Z⟩ := hr₀.2
    exact hZ₁ hz₀Z (mem_iUnion₂.mpr ⟨r₀, hr₀₁, hz₀r⟩)
  · obtain ⟨zt, hztr, hztZ⟩ := hr_t.2
    exact hZ₂ hztZ (mem_iUnion₂.mpr ⟨r_t, hr_t₂, hztr⟩)

/-- Stronger internal form of Graph Minors XIV, (5.2) (page 31), taking `IsPreconnected Z` and
recording that `closure Λ ⊆ Δ` is a closed disc with `subBd (closure Λ) = C.U` and
`closure Λ \ C.U = Λ`. -/
theorem theorem_5_2_full [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ)
    (hZne : Z.Nonempty) (hZconn : IsPreconnected Z)
    (hsub : ∀ r ∈ H.R, (closure r ∩ Z).Nonempty → r ⊆ Δ \ subBd Δ) :
    ∃ (C : Drawing S) (Λ : Set S),
      C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ ∧
      IsOpenDisc Λ ∧ closure Λ ⊆ Δ ∧ IsClosedDisc (closure Λ) ∧
      subBd Λ = C.U ∧ subBd (closure Λ) = C.U ∧ closure Λ \ C.U = Λ ∧
      Z ⊆ Λ ∧
      ∀ e ∈ C.E, ∃ r ∈ H.R, H.EdgeRegionIncident e r ∧ (closure r ∩ Z).Nonempty := by
  have : T2Space S := hS.2.1
  let R_set : Set (Set S) := {r ∈ H.R | (closure r ∩ Z).Nonempty}
  have hR_ne : R_set.Nonempty := by
    obtain ⟨z₀, hz₀⟩ := hZne
    obtain ⟨r₀, hr₀, hz₀r⟩ := exists_region_closure_mem hS H z₀
    exact ⟨r₀, hr₀, z₀, hz₀r, hz₀⟩
  have hR_conn : IsConnectedRegionSet H R_set :=
    isConnectedRegionSet_of_isPreconnected hS H hZconn
  obtain ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, hbd_clΛ, hdiffΛ, hrΛ, heR⟩ :=
    theorem_5_1_proof hS H hΔ hR_ne hR_conn (fun r hr => hsub r hr.1 hr.2)
  have hZΛ : Z ⊆ Λ := by
    have hDcl : IsClosed (closure Λ) := isClosed_closure
    have hint : Z ⊆ interior (closure Λ) :=
      subset_interior_of_regions_subset hS hDcl fun r hrR hrZ =>
        (hrΛ r ⟨hrR, hrZ⟩).trans subset_closure
    rw [← hdiffΛ]
    intro z hz
    have hzi := hint hz
    refine ⟨interior_subset hzi, fun hzC => ?_⟩
    rw [← hbd_clΛ, subBd_eq_frontier] at hzC
    exact hzC.2 hzi
  refine ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, hbd_clΛ, hdiffΛ, hZΛ, ?_⟩
  intro e he
  obtain ⟨r, ⟨hrR, hrZ⟩, hinc⟩ := heR e he
  exact ⟨r, hrR, hinc, hrZ⟩

/-- Closed-surface form of Graph Minors XIV (5.2) (page 31), cited in XIX on pages 345 and 363:
"(5.2) *Let $H$ be a drawing in $\Sigma$, and let $\Delta \subseteq \Sigma$ be a closed disc.
Let $Z \subseteq \Delta - \text{bd}(\Delta)$ be non-empty and arc-wise connected, and such
that $r \subseteq \Delta - \text{bd}(\Delta)$ for every region $r$ of $H$ with $\bar{r} \cap
Z \ne \emptyset$. Then there is a circuit $C$ of $H$ with $U(C) \subseteq \Delta$, bounding
an open disc in $\Delta$ including $Z$, such that every edge of $C$ is incident with a
region $r$ of $H$ satisfying $\bar{r} \cap Z \ne \emptyset$." -/
theorem theorem_5_2_proof :
    ∀ (S : Type u) [TopologicalSpace S],
      IsClosedSurface S → ConnectedSpace S →
    ∀ (H : Drawing S) (Δ Z : Set S),
      IsClosedDisc Δ → Z ⊆ Δ \ subBd Δ → Z.Nonempty → IsArcConnected Z →
      (∀ r ∈ H.R, (closure r ∩ Z).Nonempty → r ⊆ Δ \ subBd Δ) →
      ∃ (C : Surface.Drawing S) (Λ : Set S),
        C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ ∧
        IsOpenDisc Λ ∧ Λ ⊆ Δ ∧ subBd Λ = C.U ∧
        Z ⊆ Λ ∧
        ∀ e ∈ C.E, ∃ r ∈ H.R, H.EdgeRegionIncident e r ∧ (closure r ∩ Z).Nonempty := by
  intro S _ hS hconnS H Δ Z hΔ _ hZne hZconn hsub
  obtain ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, -, hbdΛ, -, -, hZΛ, heR⟩ :=
    theorem_5_2_full hS H hΔ hZne (IsArcConnected.isPreconnected hZconn) hsub
  exact ⟨C, Λ, hCH, hC, hCU, hOpenΛ, subset_closure.trans hclΛ_sub, hbdΛ, hZΛ, heR⟩

/-! ## 4. Regional Distance and Proofs of (5.3), (5.4), and (5.5) (page 32) -/

/-- On a connected closed surface `S`, between any two nonempty sets `X` and `Y` there exists a
region chain in `H`. -/
private theorem exists_regionChain [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {X Y : Set S} (hX : X.Nonempty) (hY : Y.Nonempty) :
    ∃ (k : ℕ) (v_seq : Fin (k + 1) → S) (r_seq : Fin k → Set S),
      IsRegionChain H X Y v_seq r_seq := by
  have : T2Space S := hS.2.1
  let Reach : Set S := {z : S | ∃ (k : ℕ) (v_seq : Fin (k + 1) → S) (r_seq : Fin k → Set S),
    IsRegionChain H X {z} v_seq r_seq}
  have hReach_ext : ∀ r ∈ H.R, (closure r ∩ Reach).Nonempty → closure r ⊆ Reach := by
    rintro r hrR ⟨z, hzr, k, v_seq, r_seq, hv0, hvlast, hsteps⟩ w hwr
    refine ⟨k + 1, Fin.snoc v_seq w, Fin.snoc r_seq r, ?_, ?_, ?_⟩
    · simpa [Fin.snoc] using hv0
    · simp [Fin.snoc]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.succ_last]
        have hzj : v_seq (Fin.last k) = z := mem_singleton_iff.mp hvlast
        exact ⟨hrR, hzj ▸ hzr, hwr⟩
      · simp only [Fin.snoc_castSucc, Fin.succ_castSucc]
        exact hsteps j
  obtain ⟨x₀, hx₀⟩ := hX
  have hx₀_reach : x₀ ∈ Reach :=
    ⟨0, fun _ => x₀, Fin.elim0, hx₀, rfl, fun i => i.elim0⟩
  let R_reach : Set (Set S) := {r ∈ H.R | (closure r ∩ Reach).Nonempty}
  have hfinR : H.R.Finite := finite_R hS H
  have hReach_eq : Reach = ⋃ r ∈ R_reach, closure r := by
    apply subset_antisymm
    · intro z hz
      obtain ⟨r, hrR, hzr⟩ := exists_region_closure_mem hS H z
      exact mem_iUnion₂.mpr ⟨r, ⟨hrR, z, hzr, hz⟩, hzr⟩
    · exact iUnion₂_subset fun r hr => hReach_ext r hr.1 hr.2
  have hReach_compl : Reachᶜ = ⋃ r ∈ H.R \ R_reach, closure r := by
    apply subset_antisymm
    · intro z hz
      obtain ⟨r, hrR, hzr⟩ := exists_region_closure_mem hS H z
      refine mem_iUnion₂.mpr ⟨r, ⟨hrR, ?_⟩, hzr⟩
      intro hr_in
      exact hz (hReach_ext r hrR hr_in.2 hzr)
    · rintro z ⟨_, ⟨r, rfl⟩, _, ⟨⟨hrR, hrnot⟩, rfl⟩, hzr⟩ hzR
      exact hrnot ⟨hrR, z, hzr, hzR⟩
  have hClopen : IsClopen Reach := by
    refine ⟨?_, ?_⟩
    · rw [hReach_eq]
      have hRfin : R_reach.Finite := hfinR.subset fun _ h => h.1
      exact hRfin.isClosed_biUnion fun _ _ => isClosed_closure
    · rw [← isClosed_compl_iff, hReach_compl]
      exact (hfinR.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  have hReach_univ : Reach = univ :=
    (isClopen_iff.mp hClopen).resolve_left (nonempty_iff_ne_empty.mp ⟨x₀, hx₀_reach⟩)
  obtain ⟨y₀, hy₀⟩ := hY
  have hy₀_reach : y₀ ∈ Reach := hReach_univ ▸ mem_univ y₀
  obtain ⟨k, v_seq, r_seq, hv0, hvlast, hsteps⟩ := hy₀_reach
  exact ⟨k, v_seq, r_seq, hv0, (mem_singleton_iff.mp hvlast) ▸ hy₀, hsteps⟩

theorem regionalDistance_spec [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {X Y : Set S} (hX : X.Nonempty) (hY : Y.Nonempty) :
    ∃ (v_seq : Fin (regionalDistance H X Y + 1) → S) (r_seq : Fin (regionalDistance H X Y) → Set S),
      IsRegionChain H X Y v_seq r_seq := by
  let lengths : Set ℕ :=
    {k | ∃ (v_seq : Fin (k + 1) → S) (r_seq : Fin k → Set S), IsRegionChain H X Y v_seq r_seq}
  have hnonempty : lengths.Nonempty := exists_regionChain hS H hX hY
  exact Nat.sInf_mem (s := lengths) hnonempty

theorem regionalDistance_le {H : Drawing S} {X Y : Set S} {k : ℕ}
    {v_seq : Fin (k + 1) → S} {r_seq : Fin k → Set S} (hc : IsRegionChain H X Y v_seq r_seq) :
    regionalDistance H X Y ≤ k :=
  Nat.sInf_le ⟨v_seq, r_seq, hc⟩

/-- Prepending a region incident with an edge of `C` to a shortest chain from `D = closure Λ` to
`W` shows that `regionalDistance H D W ≥ regionalDistance H Z W - 1`. -/
private theorem regionalDistance_closure_disc_ge [ConnectedSpace S] (hS : IsClosedSurface S)
    {H C : Drawing S} {Z D W : Set S} {k : ℕ}
    (hCH : C.IsSubdrawing H) (hC : C.IsCircuit)
    (hD : IsClosedDisc D) (hbdD : subBd D = C.U)
    (hZD : Z ⊆ D) (hZne : Z.Nonempty) (hWne : W.Nonempty) (hDW : Disjoint D W)
    (heR : ∀ e ∈ C.E, ∃ r ∈ H.R, H.EdgeRegionIncident e r ∧ (closure r ∩ Z).Nonempty)
    (hk : k ≤ regionalDistance H Z W) :
    k - 1 ≤ regionalDistance H D W := by
  have : T2Space S := hS.2.1
  have hDcl : IsClosed D := hD.isCompact.isClosed
  have hDne : D.Nonempty := hZne.mono hZD
  have hspec := regionalDistance_spec hS H hDne hWne
  generalize hk' : regionalDistance H D W = k' at hspec ⊢
  obtain ⟨v_seq, r_seq, hv0, hvlast, hsteps⟩ := hspec
  rcases k' with _ | m
  · exfalso
    have h0 : Fin.last 0 = (0 : Fin 1) := rfl
    rw [h0] at hvlast
    exact disjoint_left.mp hDW hv0 hvlast
  · have hv1_not_D : v_seq 1 ∉ D := by
      intro hv1D
      have hchain' : IsRegionChain H D W (fun i : Fin (m + 1) => v_seq i.succ)
          (fun i : Fin m => r_seq i.succ) := by
        refine ⟨hv1D, ?_, fun i => ?_⟩
        · simpa [Fin.last] using hvlast
        · exact hsteps i.succ
      have hle : m + 1 ≤ m := hk' ▸ regionalDistance_le hchain'
      omega
    have hr0_R : r_seq 0 ∈ H.R := (hsteps 0).1
    have hv0_r0 : v_seq 0 ∈ closure (r_seq 0) := (hsteps 0).2.1
    have hv1_r0 : v_seq 1 ∈ closure (r_seq 0) := (hsteps 0).2.2
    have hr0_not_sub : ¬ r_seq 0 ⊆ D :=
      fun hsub => hv1_not_D (hDcl.closure_subset_iff.mpr hsub hv1_r0)
    have hfrD : frontier D = C.U := by rw [← subBd_eq_frontier, hbdD]
    have hr0_disj_fr : Disjoint (r_seq 0) (frontier D) := by
      rw [hfrD]
      exact disjoint_left.mpr fun x hxr hxC => region_subset hr0_R hxr (hCH.U_subset hxC)
    have hr0_disj_D : Disjoint (r_seq 0) D :=
      (subset_or_disjoint_of_frontier hDcl (region_isPreconnected hr0_R) hr0_disj_fr).resolve_left
        hr0_not_sub
    have hv0_CU : v_seq 0 ∈ C.U := by
      rw [← hbdD]
      refine ⟨subset_closure hv0, closure_mono ?_ hv0_r0⟩
      exact fun x hxr => ⟨mem_univ x, disjoint_left.mp hr0_disj_D hxr⟩
    have hv0_edge : ∃ e ∈ C.E, v_seq 0 ∈ closure e := by
      by_cases hv0V : v_seq 0 ∈ C.V
      · obtain ⟨W_walk, -, hpos, -, -⟩ := exists_walk_at hC hv0V
        cases W_walk with
        | nil _ => simp at hpos
        | @cons _ w _ e hl _ =>
          have : v_seq 0 ∈ closure e ∩ C.V := by rw [hl.2.2.2]; simp
          exact ⟨e, hl.1, this.1⟩
      · obtain ⟨e, heC, hv0e⟩ := C.exists_edge_of_mem hv0_CU hv0V
        exact ⟨e, heC, subset_closure hv0e⟩
    obtain ⟨e, heC, hv0_e⟩ := hv0_edge
    obtain ⟨r, hrR, hinc, z, hzr, hzZ⟩ := heR e heC
    have her : e ⊆ closure r :=
      edge_subset_closure_of_incident hS (hCH.2 heC) hrR hinc.2.2
    have hv0_r : v_seq 0 ∈ closure r := closure_minimal her isClosed_closure hv0_e
    have hchain_ext : IsRegionChain H Z W (Fin.cons z v_seq) (Fin.cons r r_seq) := by
      refine ⟨hzZ, ?_, fun i => ?_⟩
      · rw [← Fin.succ_last (m + 1), Fin.cons_succ]
        exact hvlast
      · refine Fin.cases ?_ (fun j => ?_) i
        · exact ⟨hrR, hzr, hv0_r⟩
        · simpa using hsteps j
    have hle : k ≤ (m + 1) + 1 := hk.trans (regionalDistance_le (k := m + 1 + 1) hchain_ext)
    omega

/-- Preconnected version of Graph Minors XIV, (5.3) (page 32), used in the induction for (5.4). -/
theorem theorem_5_3_of_isPreconnected [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ)
    (hZne : Z.Nonempty) (hZconn : IsPreconnected Z)
    {k : ℕ} (hk2 : 2 ≤ k) (hdist : k ≤ regionalDistance H Z (univ \ Δ)) :
    ∃ (C : Drawing S) (Λ : Set S),
      C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ ∧
      IsOpenDisc Λ ∧ closure Λ ⊆ Δ ∧ IsClosedDisc (closure Λ) ∧
      subBd Λ = C.U ∧ subBd (closure Λ) = C.U ∧ closure Λ \ C.U = Λ ∧
      Z ⊆ Λ ∧ k - 1 ≤ regionalDistance H (closure Λ) (univ \ Δ) := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hsub : ∀ r ∈ H.R, (closure r ∩ Z).Nonempty → r ⊆ Δ \ subBd Δ := by
    rintro r hrR ⟨z, hzr, hzZ⟩
    by_contra hnot
    have hr_not_Δ : ¬ r ⊆ Δ := by
      intro hrΔ
      apply hnot
      have hopen : IsOpen r := region_isOpen hrR
      have hint : r ⊆ interior Δ := interior_maximal hrΔ hopen
      intro x hxr
      exact ⟨hrΔ hxr, fun hxbd => ((subBd_eq_frontier Δ ▸ hxbd : x ∈ frontier Δ)).2 (hint hxr)⟩
    obtain ⟨y, hyr, hyΔ⟩ := not_subset.mp hr_not_Δ
    have hchain1 : IsRegionChain H Z (univ \ Δ) ![z, y] ![r] := by
      refine ⟨hzZ, ⟨mem_univ y, hyΔ⟩, fun i => ?_⟩
      fin_cases i
      exact ⟨hrR, hzr, subset_closure hyr⟩
    have hle1 : regionalDistance H Z (univ \ Δ) ≤ 1 := regionalDistance_le hchain1
    omega
  obtain ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, hbd_clΛ, hdiffΛ, hZΛ, heR⟩ :=
    theorem_5_2_full hS H hΔ hZne hZconn hsub
  have hcompl_ne : (univ \ Δ).Nonempty := by
    obtain ⟨f⟩ := hΔ.isOArc_discBd
    have hbd_ne : (discBd Δ).Nonempty := ⟨(f 1).1, (f 1).2⟩
    obtain ⟨w, hw⟩ := hbd_ne
    rw [← IsClosedDisc.frontier_eq_discBd hS hΔ] at hw
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hemp
    have hΔuniv : Δ = univ := subset_antisymm (subset_univ _) hemp
    rw [hΔuniv, frontier_univ] at hw
    exact hw
  have hdisj : Disjoint (closure Λ) (univ \ Δ) :=
    disjoint_left.mpr fun _ hx hnot => hnot.2 (hclΛ_sub hx)
  have hdist' := regionalDistance_closure_disc_ge hS hCH hC hclΛ_disc hbd_clΛ
    (hZΛ.trans subset_closure) hZne hcompl_ne hdisj heR hdist
  exact ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, hbd_clΛ, hdiffΛ, hZΛ, hdist'⟩

/-- Closed-surface form of Graph Minors XIV (5.3) (page 32):
"Let $H$ be a drawing in $\Sigma$, and let $\Delta \subseteq \Sigma$ be a closed disc. Let $Z
\subseteq \Delta - \text{bd}(\Delta)$ be non-empty and arc-wise connected, such that the
regional distance between $Z$ and $\Sigma - \Delta$ is $\ge k \ge 2$. Then there is a
circuit $C$ of $H$ with $U(C) \subseteq \Delta$, bounding an open disc $\Lambda$ including
$Z$, such that the regional distance between $\bar{\Lambda}$ and $\Sigma - \Delta$ is $\ge k
- 1$." -/
theorem theorem_5_3_proof [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ)
    (_hZ : Z ⊆ Δ \ subBd Δ) (hZne : Z.Nonempty) (hZconn : IsArcConnected Z)
    {k : ℕ} (hk2 : 2 ≤ k) (hdist : k ≤ regionalDistance H Z (univ \ Δ)) :
    ∃ (C : Drawing S) (Λ : Set S),
      C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ ∧
      IsOpenDisc Λ ∧ closure Λ ⊆ Δ ∧ IsClosedDisc (closure Λ) ∧ subBd Λ = C.U ∧
      Z ⊆ Λ ∧ k - 1 ≤ regionalDistance H (closure Λ) (univ \ Δ) := by
  obtain ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, -, -, hZΛ, hdist'⟩ :=
    theorem_5_3_of_isPreconnected hS H hΔ hZne (IsArcConnected.isPreconnected hZconn) hk2 hdist
  exact ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, hZΛ, hdist'⟩

/-- Inductive helper for (5.4): produces `m` nested circuits and open discs around `Z` when
`m + 1 ≤ regionalDistance H Z (univ \ Δ)`. -/
private theorem theorem_5_4_aux [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ : Set S} (hΔ : IsClosedDisc Δ) :
    ∀ (m : ℕ) {Z : Set S}, Z.Nonempty → IsPreconnected Z →
      m + 1 ≤ regionalDistance H Z (univ \ Δ) →
      ∃ (C : Fin m → Drawing S) (Λ : Fin m → Set S),
        (∀ i : Fin m, (C i).IsSubdrawing H ∧ (C i).IsCircuit ∧ (C i).U ⊆ Δ ∧
          IsOpenDisc (Λ i) ∧ closure (Λ i) ⊆ Δ ∧ subBd (Λ i) = (C i).U ∧
          closure (Λ i) \ (C i).U = Λ i ∧ Z ⊆ Λ i) ∧
        (∀ i j : Fin m, i < j → closure (Λ i) ⊆ Λ j)
  | 0, Z, _, _, _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | m + 1, Z, hZne, hZconn, hdist => by
    have hk2 : 2 ≤ m + 2 := Nat.le_add_left 2 m
    obtain ⟨C₀, Λ₀, hC₀H, hC₀, hC₀U, hOpen₀, hcl₀_sub, hcl₀_disc, hbd₀, hbd_cl₀, hdiff₀,
      hZΛ₀, hdist₀⟩ :=
      theorem_5_3_of_isPreconnected hS H hΔ hZne hZconn hk2 hdist
    obtain ⟨C_rest, Λ_rest, hrest, hnest⟩ :=
      theorem_5_4_aux hS H hΔ m (IsClosedDisc.nonempty hcl₀_disc)
        (IsClosedDisc.isPreconnected hcl₀_disc) hdist₀
    refine ⟨Fin.cons C₀ C_rest, Fin.cons Λ₀ Λ_rest, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hC₀H, hC₀, hC₀U, hOpen₀, hcl₀_sub, hbd₀, hdiff₀, hZΛ₀⟩
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrest j
        exact ⟨h1, h2, h3, h4, h5, h6, h7, (hZΛ₀.trans subset_closure).trans h8⟩
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> intro hij
      · exact absurd hij (lt_irrefl 0)
      · exact (hrest j').2.2.2.2.2.2.2
      · exact absurd hij (Nat.not_lt_zero _)
      · exact hnest i' j' (Fin.succ_lt_succ_iff.mp hij)

/-- Closed-surface form of Graph Minors XIV (5.4) (page 32):
"Let $H, \Sigma, \Delta, Z, k$ be as in (5.3). Then there are mutually disjoint circuits
$C_1, \dots, C_{k-1}$ of $H$ with $U(C_1), \dots, U(C_{k-1}) \subseteq \Delta$, all bounding
open discs including $Z$." -/
theorem theorem_5_4_proof [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ)
    (_hZ : Z ⊆ Δ \ subBd Δ) (hZne : Z.Nonempty) (hZconn : IsArcConnected Z)
    {k : ℕ} (hk2 : 2 ≤ k) (hdist : k ≤ regionalDistance H Z (univ \ Δ)) :
    ∃ (C : Fin (k - 1) → Drawing S) (Λ : Fin (k - 1) → Set S),
      (∀ i : Fin (k - 1), (C i).IsSubdrawing H ∧ (C i).IsCircuit ∧ (C i).U ⊆ Δ ∧
        IsOpenDisc (Λ i) ∧ closure (Λ i) ⊆ Δ ∧ subBd (Λ i) = (C i).U ∧ Z ⊆ Λ i) ∧
      (∀ i j : Fin (k - 1), i < j → closure (Λ i) ⊆ Λ j) ∧
      Pairwise (fun i j => Disjoint (C i).U (C j).U) := by
  have hdist' : (k - 1) + 1 ≤ regionalDistance H Z (univ \ Δ) := by omega
  obtain ⟨C, Λ, hprops, hnest⟩ :=
    theorem_5_4_aux hS H hΔ (k - 1) hZne (IsArcConnected.isPreconnected hZconn) hdist'
  refine ⟨C, Λ, fun i => ?_, hnest, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := hprops i
    exact ⟨h1, h2, h3, h4, h5, h6, h8⟩
  · intro i j hij
    have hlt_or_gt : i < j ∨ j < i := lt_or_gt_of_ne hij
    have key : ∀ a b : Fin (k - 1), a < b → Disjoint (C a).U (C b).U := by
      intro a b hab
      have hCa_cl : (C a).U ⊆ closure (Λ a) := by
        rw [← (hprops a).2.2.2.2.2.1]
        exact fun _ hx => hx.1
      have hsub_b : (C a).U ⊆ Λ b := hCa_cl.trans (hnest a b hab)
      have hdiff_b : closure (Λ b) \ (C b).U = Λ b := (hprops b).2.2.2.2.2.2.1
      rw [disjoint_left]
      intro x hxa hxb
      have hxΛb : x ∈ Λ b := hsub_b hxa
      rw [← hdiff_b] at hxΛb
      exact hxΛb.2 hxb
    rcases hlt_or_gt with h | h
    · exact key i j h
    · exact (key j i h).symm

/-- Single-step version of Graph Minors XIV, (5.5) (page 32, used on page 48 in the proof of (9.6)):
if `Z ⊆ Δ \ subBd Δ` is nonempty and preconnected and the regional distance between `Z` and
`subBd Δ` is `≥ k ≥ 2`, there is a circuit `C` of `H` with `U(C) ⊆ Δ \ subBd Δ` bounding an open
disc `Λ` with `closure Λ ⊆ Δ \ subBd Δ`, `Z ⊆ Λ`, and
`regionalDistance H (closure Λ) (subBd Δ) ≥ k - 1`. -/
theorem theorem_5_5_step_of_isPreconnected [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ)
    (hZ : Z ⊆ Δ \ subBd Δ) (hZne : Z.Nonempty) (hZconn : IsPreconnected Z)
    {k : ℕ} (hk2 : 2 ≤ k) (hdist : k ≤ regionalDistance H Z (subBd Δ)) :
    ∃ (C : Drawing S) (Λ : Set S),
      C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ \ subBd Δ ∧
      IsOpenDisc Λ ∧ closure Λ ⊆ Δ \ subBd Δ ∧ IsClosedDisc (closure Λ) ∧
      subBd Λ = C.U ∧ subBd (closure Λ) = C.U ∧ closure Λ \ C.U = Λ ∧
      Z ⊆ Λ ∧ k - 1 ≤ regionalDistance H (closure Λ) (subBd Δ) := by
  have : T2Space S := hS.2.1
  have hΔcl : IsClosed Δ := hΔ.isCompact.isClosed
  have hcl_r_sub : ∀ r ∈ H.R, (closure r ∩ Z).Nonempty → closure r ⊆ Δ \ subBd Δ := by
    rintro r hrR ⟨z, hzr, hzZ⟩
    have hdisj_bd : Disjoint (closure r) (subBd Δ) := by
      rw [disjoint_left]
      intro y hyr hybd
      have hchain1 : IsRegionChain H Z (subBd Δ) ![z, y] ![r] := by
        refine ⟨hzZ, hybd, fun i => ?_⟩
        fin_cases i
        exact ⟨hrR, hzr, hyr⟩
      have hle1 : regionalDistance H Z (subBd Δ) ≤ 1 := regionalDistance_le hchain1
      omega
    have hr_disj_fr : Disjoint r (frontier Δ) := by
      rw [← subBd_eq_frontier]
      exact hdisj_bd.mono_left subset_closure
    have hr_sub_Δ : r ⊆ Δ := by
      rcases subset_or_disjoint_of_frontier hΔcl (region_isPreconnected hrR) hr_disj_fr with h | h
      · exact h
      · exfalso
        have hz_int : z ∈ interior Δ := by
          have hzΔ := hZ hzZ
          rw [subBd_eq_frontier] at hzΔ
          by_contra hni
          exact hzΔ.2 ⟨subset_closure hzΔ.1, hni⟩
        obtain ⟨x, hxi, hxr⟩ := mem_closure_iff.mp hzr (interior Δ) isOpen_interior hz_int
        exact disjoint_left.mp h hxr (interior_subset hxi)
    have hcl_Δ : closure r ⊆ Δ := hΔcl.closure_subset_iff.mpr hr_sub_Δ
    exact fun x hxr => ⟨hcl_Δ hxr, disjoint_left.mp hdisj_bd hxr⟩
  have hsub : ∀ r ∈ H.R, (closure r ∩ Z).Nonempty → r ⊆ Δ \ subBd Δ :=
    fun r hrR hrZ => subset_closure.trans (hcl_r_sub r hrR hrZ)
  obtain ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, hbd_clΛ, hdiffΛ, hZΛ, heR⟩ :=
    theorem_5_2_full hS H hΔ hZne hZconn hsub
  have hCU_int : C.U ⊆ Δ \ subBd Δ := by
    rw [C.U_eq]
    have he_sub : ∀ e ∈ C.E, closure e ⊆ Δ \ subBd Δ := by
      intro e he
      obtain ⟨r, hrR, hinc, hrZ⟩ := heR e he
      have her := edge_subset_closure_of_incident hS (hCH.2 he) hrR hinc.2.2
      exact (closure_minimal her isClosed_closure).trans (hcl_r_sub r hrR hrZ)
    refine union_subset ?_ (iUnion₂_subset he_sub)
    intro v hv
    obtain ⟨W_walk, -, hpos, -, -⟩ := exists_walk_at hC hv
    cases W_walk with
    | nil _ => simp at hpos
    | @cons _ w _ e hl _ =>
      have : v ∈ closure e ∩ C.V := by rw [hl.2.2.2]; simp
      exact he_sub e hl.1 this.1
  have hclΛ_int : closure Λ ⊆ Δ \ subBd Δ := by
    intro x hx
    refine ⟨hclΛ_sub hx, fun hxbd => ?_⟩
    rw [subBd_eq_frontier] at hxbd
    have hx_fr : x ∈ frontier (closure Λ) :=
      ⟨subset_closure hx, fun hxi => hxbd.2 (interior_mono hclΛ_sub hxi)⟩
    rw [← subBd_eq_frontier, hbd_clΛ] at hx_fr
    exact (hCU_int hx_fr).2 (by rwa [subBd_eq_frontier])
  have hbd_ne : (subBd Δ).Nonempty := by
    rw [IsClosedDisc.subBd_eq_discBd hS hΔ]
    obtain ⟨f⟩ := hΔ.isOArc_discBd
    exact ⟨(f 1).1, (f 1).2⟩
  have hdisj : Disjoint (closure Λ) (subBd Δ) :=
    disjoint_left.mpr fun _ hx hxbd => (hclΛ_int hx).2 hxbd
  have hdist' := regionalDistance_closure_disc_ge hS hCH hC hclΛ_disc hbd_clΛ
    (hZΛ.trans subset_closure) hZne hbd_ne hdisj heR hdist
  exact ⟨C, Λ, hCH, hC, hCU_int, hOpenΛ, hclΛ_int, hclΛ_disc, hbdΛ, hbd_clΛ, hdiffΛ, hZΛ, hdist'⟩

/-- Single-step version of Graph Minors XIV, (5.5) (page 32) for arc-connected `Z`. -/
theorem theorem_5_5_step [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ)
    (hZ : Z ⊆ Δ \ subBd Δ) (hZne : Z.Nonempty) (hZconn : IsArcConnected Z)
    {k : ℕ} (hk2 : 2 ≤ k) (hdist : k ≤ regionalDistance H Z (subBd Δ)) :
    ∃ (C : Drawing S) (Λ : Set S),
      C.IsSubdrawing H ∧ C.IsCircuit ∧ C.U ⊆ Δ \ subBd Δ ∧
      IsOpenDisc Λ ∧ closure Λ ⊆ Δ \ subBd Δ ∧ IsClosedDisc (closure Λ) ∧
      subBd Λ = C.U ∧ Z ⊆ Λ ∧ k - 1 ≤ regionalDistance H (closure Λ) (subBd Δ) := by
  obtain ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, -, -, hZΛ, hdist'⟩ :=
    theorem_5_5_step_of_isPreconnected hS H hΔ hZ hZne (IsArcConnected.isPreconnected hZconn)
      hk2 hdist
  exact ⟨C, Λ, hCH, hC, hCU, hOpenΛ, hclΛ_sub, hclΛ_disc, hbdΛ, hZΛ, hdist'⟩

/-- Inductive helper for (5.5): produces `m` nested circuits and open discs in `Δ \ subBd Δ` around
`Z` when `m + 1 ≤ regionalDistance H Z (subBd Δ)`. -/
theorem theorem_5_5_aux [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ : Set S} (hΔ : IsClosedDisc Δ) :
    ∀ (m : ℕ) {Z : Set S}, Z ⊆ Δ \ subBd Δ → Z.Nonempty → IsPreconnected Z →
      m + 1 ≤ regionalDistance H Z (subBd Δ) →
      ∃ (C : Fin m → Drawing S) (Λ : Fin m → Set S),
        (∀ i : Fin m, (C i).IsSubdrawing H ∧ (C i).IsCircuit ∧ (C i).U ⊆ Δ \ subBd Δ ∧
          IsOpenDisc (Λ i) ∧ closure (Λ i) ⊆ Δ \ subBd Δ ∧ IsClosedDisc (closure (Λ i)) ∧
          subBd (Λ i) = (C i).U ∧ subBd (closure (Λ i)) = (C i).U ∧
          closure (Λ i) \ (C i).U = Λ i ∧ Z ⊆ Λ i) ∧
        (∀ i j : Fin m, i < j → closure (Λ i) ⊆ Λ j)
  | 0, Z, _, _, _, _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | m + 1, Z, hZ, hZne, hZconn, hdist => by
    have hk2 : 2 ≤ m + 2 := Nat.le_add_left 2 m
    obtain ⟨C₀, Λ₀, hC₀H, hC₀, hC₀U, hOpen₀, hcl₀_sub, hcl₀_disc, hbd₀, hbd_cl₀, hdiff₀,
      hZΛ₀, hdist₀⟩ :=
      theorem_5_5_step_of_isPreconnected hS H hΔ hZ hZne hZconn hk2 hdist
    obtain ⟨C_rest, Λ_rest, hrest, hnest⟩ :=
      theorem_5_5_aux hS H hΔ m hcl₀_sub (IsClosedDisc.nonempty hcl₀_disc)
        (IsClosedDisc.isPreconnected hcl₀_disc) hdist₀
    refine ⟨Fin.cons C₀ C_rest, Fin.cons Λ₀ Λ_rest, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hC₀H, hC₀, hC₀U, hOpen₀, hcl₀_sub, hcl₀_disc, hbd₀, hbd_cl₀, hdiff₀, hZΛ₀⟩
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrest j
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, (hZΛ₀.trans subset_closure).trans h10⟩
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> intro hij
      · exact absurd hij (lt_irrefl 0)
      · exact (hrest j').2.2.2.2.2.2.2.2.2
      · exact absurd hij (Nat.not_lt_zero _)
      · exact hnest i' j' (Fin.succ_lt_succ_iff.mp hij)

/-- Closed-surface form of Graph Minors XIV (5.5) (page 32):
"Let $H$ be a drawing in $\Sigma$, and let $\Delta \subseteq \Sigma$ be a closed disc. Let $Z
\subseteq \Delta - \text{bd}(\Delta)$ be non-empty and arc-wise connected, such that the
regional distance between $Z$ and $\text{bd}(\Delta)$ is $\ge k \ge 1$. Then there are $k -
1$ mutually disjoint circuits $C_1, \dots, C_{k-1}$ of $H$ with $U(C_1), \dots, U(C_{k-1})
\subseteq \Delta - \text{bd}(\Delta)$, all bounding open discs including $Z$." -/
theorem theorem_5_5_proof [ConnectedSpace S] (hS : IsClosedSurface S)
    (H : Drawing S) {Δ Z : Set S} (hΔ : IsClosedDisc Δ)
    (hZ : Z ⊆ Δ \ subBd Δ) (hZne : Z.Nonempty) (hZconn : IsArcConnected Z)
    {k : ℕ} (hk1 : 1 ≤ k) (hdist : k ≤ regionalDistance H Z (subBd Δ)) :
    ∃ (C : Fin (k - 1) → Drawing S) (Λ : Fin (k - 1) → Set S),
      (∀ i : Fin (k - 1), (C i).IsSubdrawing H ∧ (C i).IsCircuit ∧ (C i).U ⊆ Δ \ subBd Δ ∧
        IsOpenDisc (Λ i) ∧ closure (Λ i) ⊆ Δ \ subBd Δ ∧ IsClosedDisc (closure (Λ i)) ∧
        subBd (Λ i) = (C i).U ∧ subBd (closure (Λ i)) = (C i).U ∧
        closure (Λ i) \ (C i).U = Λ i ∧ Z ⊆ Λ i) ∧
      (∀ i j : Fin (k - 1), i < j → closure (Λ i) ⊆ Λ j) ∧
      Pairwise (fun i j => Disjoint (C i).U (C j).U) := by
  have hdist' : (k - 1) + 1 ≤ regionalDistance H Z (subBd Δ) := by omega
  obtain ⟨C, Λ, hprops, hnest⟩ :=
    theorem_5_5_aux hS H hΔ (k - 1) hZ hZne (IsArcConnected.isPreconnected hZconn) hdist'
  refine ⟨C, Λ, hprops, hnest, ?_⟩
  intro i j hij
  have hlt_or_gt : i < j ∨ j < i := lt_or_gt_of_ne hij
  have key : ∀ a b : Fin (k - 1), a < b → Disjoint (C a).U (C b).U := by
    intro a b hab
    have hCa_cl : (C a).U ⊆ closure (Λ a) := by
      rw [← (hprops a).2.2.2.2.2.2.1]
      exact fun _ hx => hx.1
    have hsub_b : (C a).U ⊆ Λ b := hCa_cl.trans (hnest a b hab)
    have hdiff_b : closure (Λ b) \ (C b).U = Λ b := (hprops b).2.2.2.2.2.2.2.2.1
    rw [disjoint_left]
    intro x hxa hxb
    have hxΛb : x ∈ Λ b := hsub_b hxa
    rw [← hdiff_b] at hxΛb
    exact hxΛb.2 hxb
  rcases hlt_or_gt with h | h
  · exact key i j h
  · exact (key j i h).symm

end GraphMinor.GM14
