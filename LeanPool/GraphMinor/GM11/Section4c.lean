/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.ForestRegions
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Graph Minors XI, (4.4) and (4.5)

Throughout, `Γ` is a drawing in a connected closed surface with a slope `ins`.

(4.4) says that the complement of `ins(Γ')` is a region of `Γ'`, for `Γ'` confined. We follow the
paper. There is a region not captured, by (4.3)(ii). Any two distinct regions contain a captured
one,
by induction on the number of edges, deleting an edge of a circuit.

(4.5) says that a region of a confined `Γ'` that `Γ` captures is captured by `Γ'`. The paper says
that some circuit `C'` of `Γ'` bounds a closed disc in `ins(C)` around the region. We prove what is
needed by deleting edges of `Γ'` as long as the region stays in `ins(C)`.

The topological input on discs is `closedDisc_not_subset_edge`: a neighbourhood in a closed disc is
not contained in an edge. A real-valued injective map on a circle would have `f(x) = f(-x)`
for some `x`, by the intermediate value theorem.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

/-- No continuous real function on a circle in the plane is injective. -/
theorem not_injective_sphere {c : EuclideanPlane} {s : ℝ} (hs : 0 < s)
    (g : Metric.sphere c s → ℝ) (hg : Continuous g) : ¬ Function.Injective g := by
  intro hinj
  have hrank : 1 < Module.rank ℝ EuclideanPlane := by
    apply Module.lt_rank_of_lt_finrank
    simp
  have hconn : IsPreconnected (univ : Set (Metric.sphere c s)) :=
    isPreconnected_iff_preconnectedSpace.mp (isPreconnected_sphere hrank c s) |>.isPreconnected_univ
  have hanti : ∀ x : Metric.sphere c s, c - (x.1 - c) ∈ Metric.sphere c s := by
    intro x
    have hx : ‖x.1 - c‖ = s := by simpa [dist_eq_norm] using x.2
    simp only [mem_sphere_iff_norm, sub_sub_cancel_left, norm_neg, hx]
  let σ : Metric.sphere c s → Metric.sphere c s := fun x => ⟨c - (x.1 - c), hanti x⟩
  have hσ : Continuous σ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hσσ : ∀ x, σ (σ x) = x := fun x => Subtype.ext (by simp [σ])
  have hne : ∀ x, σ x ≠ x := by
    intro x h
    have hx : ‖x.1 - c‖ = s := by simpa [dist_eq_norm] using x.2
    have h₁ : c - (x.1 - c) = x.1 := congrArg Subtype.val h
    have h₂ : (2 : ℝ) • (x.1 - c) = 0 := by
      rw [two_smul]
      have : x.1 - c = -(x.1 - c) := by
        nth_rw 1 [← h₁]
        abel
      nth_rw 1 [this]
      simp
    have h₃ : x.1 - c = 0 := by simpa using h₂
    rw [h₃, norm_zero] at hx
    exact hs.ne hx
  let d : Metric.sphere c s → ℝ := fun x => g x - g (σ x)
  have hd : Continuous d := hg.sub (hg.comp hσ)
  obtain ⟨x⟩ : Nonempty (Metric.sphere c s) := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := c)).mpr hs.le
    exact ⟨⟨x, hx⟩⟩
  have hdσ : d (σ x) = - d x := by simp [d, hσσ]
  have hzero : (0 : ℝ) ∈ Icc (min (d x) (d (σ x))) (max (d x) (d (σ x))) := by
    rw [hdσ]
    rcases le_total (d x) 0 with h | h
    · exact ⟨le_trans (min_le_left _ _) h, le_trans (by linarith) (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) (by linarith), le_trans h (le_max_left _ _)⟩
  have hsub : Icc (min (d x) (d (σ x))) (max (d x) (d (σ x))) ⊆ d '' univ := by
    rcases le_total (d x) (d (σ x)) with h | h
    · rw [min_eq_left h, max_eq_right h]
      exact hconn.intermediate_value (mem_univ _) (mem_univ _) hd.continuousOn
    · rw [min_eq_right h, max_eq_left h]
      exact hconn.intermediate_value (mem_univ _) (mem_univ _) hd.continuousOn
  obtain ⟨y, -, hy⟩ := hsub hzero
  have : g y = g (σ y) := by linarith [show g y - g (σ y) = 0 from hy]
  exact hne y (hinj this).symm

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- A neighbourhood in a closed disc is not contained in an edge. Otherwise a small circle in the
disc would embed in an open interval. -/
theorem closedDisc_not_subset_edge {Δ W : Set S} (hΔ : IsClosedDisc Δ) (hW : IsOpen W) {p : S}
    (hpW : p ∈ W) (hp : p ∈ Δ) (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) : ¬ W ∩ Δ ⊆ e := by
  intro hsub
  obtain ⟨φ⟩ := hΔ
  let f : ClosedUnitDisc → S := fun x => (φ x).1
  have hf : Continuous f := continuous_subtype_val.comp φ.continuous
  have hfinj : Function.Injective f := fun x y h => φ.injective (Subtype.ext h)
  -- A round circle inside the open disc whose image lies in `W`.
  let c₀ : ClosedUnitDisc := φ.symm ⟨p, hp⟩
  have hfc : f c₀ = p := by simp [f, c₀]
  have hopen : IsOpen {x : ClosedUnitDisc | f x ∈ W} := hW.preimage hf
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen c₀ (by simpa [hfc] using hpW)
  have hcl : (c₀ : EuclideanPlane) ∈ closure (OpenUnitDisc : Set EuclideanPlane) := by
    have : closure (OpenUnitDisc : Set EuclideanPlane) = ClosedUnitDisc :=
      closure_ball _ one_ne_zero
    rw [this]
    exact c₀.2
  obtain ⟨w, hwb, hwO⟩ := Metric.mem_closure_iff.mp hcl δ hδ
  let P : Set EuclideanPlane := Metric.ball (c₀ : EuclideanPlane) δ ∩ OpenUnitDisc
  have hP : IsOpen P := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hwP : w ∈ P := ⟨by rw [Metric.mem_ball, dist_comm]; exact hwO, hwb⟩
  obtain ⟨ρ, hρ, hρP⟩ := Metric.isOpen_iff.mp hP w hwP
  let s : ℝ := ρ / 2
  have hs : 0 < s := half_pos hρ
  have hsphere : Metric.sphere w s ⊆ P :=
    (Metric.sphere_subset_closedBall.trans
      (Metric.closedBall_subset_ball (half_lt_self hρ))).trans hρP
  let i : Metric.sphere w s → ClosedUnitDisc := fun x =>
    ⟨x.1, Metric.ball_subset_closedBall (hsphere x.2).2⟩
  have hi : Continuous i := Continuous.subtype_mk continuous_subtype_val _
  have hiW : ∀ x, f (i x) ∈ W := fun x => hball (hsphere x.2).1
  have hie : ∀ x, f (i x) ∈ e := fun x => hsub ⟨hiW x, (φ (i x)).2⟩
  -- Move the circle to the interval by the parametrization of `e`.
  obtain ⟨γ, hγ, hγ0, hγ1, hinj, hγe⟩ := exists_edge_param Γ he
  let Y : Set S := range (fun x => f (i x))
  have : CompactSpace (Metric.sphere w s) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hYcpt : IsCompact Y := isCompact_range (hf.comp hi)
  let K : Set unitInterval := γ ⁻¹' Y
  have hKcpt : IsCompact K := (hYcpt.isClosed.preimage hγ).isCompact
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
  have hKIoo : K ⊆ Ioo 0 1 := by
    intro t ht
    obtain ⟨x, hx⟩ := ht
    have hte : γ t ∈ e := by
      have := hie x
      simpa [hx] using this
    refine ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩
    · rintro rfl
      exact (he.2.1 hte).2 hγ0
    · rintro rfl
      exact (he.2.1 hte).2 hγ1
  let γK : K → S := fun t => γ t.1
  have hγK : Continuous γK := hγ.comp continuous_subtype_val
  have hγKinj : Function.Injective γK := fun s t h =>
    Subtype.ext (hinj (hKIoo s.2) (hKIoo t.2) h)
  have hγKemb : IsClosedEmbedding γK := hγK.isClosedEmbedding hγKinj
  have hch : ∀ x, ∃ t : K, γK t = f (i x) := by
    intro x
    have hmem : f (i x) ∈ e := hie x
    rw [← hγe] at hmem
    obtain ⟨t, -, ht⟩ := hmem
    exact ⟨⟨t, ⟨x, ht.symm⟩⟩, ht⟩
  choose τ hτ using hch
  have hτc : Continuous τ := by
    refine hγKemb.isInducing.continuous_iff.mpr ?_
    have : γK ∘ τ = fun x => f (i x) := funext hτ
    rw [this]
    exact hf.comp hi
  have hinj' : Function.Injective fun x => ((τ x).1 : ℝ) := by
    intro x y hxy
    have h₁ : τ x = τ y := Subtype.ext (Subtype.ext hxy)
    have h₂ : f (i x) = f (i y) := by rw [← hτ, ← hτ, h₁]
    have h₃ := hfinj h₂
    have h₄ : (x : EuclideanPlane) = y := congrArg (fun z : ClosedUnitDisc => z.1) h₃
    exact Subtype.ext h₄
  exact not_injective_sphere hs _ (continuous_subtype_val.comp
    (continuous_subtype_val.comp hτc)) hinj'

variable {Γ : Drawing S}

/-- A region of a subdrawing either lies in `ins(C)` or misses it, since it misses the frontier
`U(C)` of `ins(C)`. -/
theorem region_subset_or_disjoint {Γ' C : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope Γ' k ins) (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ') (hl : C.length < k)
    {r : Set S} (hr : r ∈ Γ'.R) : r ⊆ ins C ∨ Disjoint r (ins C) := by
  have hcl : IsClosed (ins C) := (hs.isClosedDisc C hC hCs hl).isClosed
  have hfr : frontier (ins C) = C.U := by rw [subBd_eq_frontier', hs.subBd_eq C hC hCs hl]
  have hcov : r ⊆ interior (ins C) ∪ (ins C)ᶜ := by
    intro x hx
    by_cases hxi : x ∈ ins C
    · refine Or.inl ?_
      by_contra hxn
      exact region_subset hr hx (hCs.U_subset (hfr ▸ ⟨subset_closure hxi, hxn⟩))
    · exact Or.inr hxi
  have hdis : Disjoint (interior (ins C)) (ins C)ᶜ :=
    disjoint_left.mpr fun x hx hx' => hx' (interior_subset hx)
  by_cases hmeet : (r ∩ ins C).Nonempty
  · refine Or.inl (subset_trans ?_ interior_subset)
    obtain ⟨x, hxr, hxi⟩ := hmeet
    have hxint : x ∈ interior (ins C) := by
      rcases hcov hxr with h | h
      · exact h
      · exact absurd hxi h
    exact (region_isPreconnected hr).subset_left_of_subset_union isOpen_interior
      hcl.isOpen_compl hdis hcov ⟨x, hxr, hxint⟩
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet))

/-- Every edge of a circuit `C` of `Γ'` is incident with a region of `Γ'` inside `ins(C)` and with
a region not inside `ins(C)`. -/
theorem exists_regions_of_circuit_edge (hS : IsClosedSurface S)
    {Γ' C : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope Γ' k ins) (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ') (hl : C.length < k)
    {e : Set S} (he : e ∈ C.E) :
    (∃ r ∈ Γ'.R, e ⊆ closure r ∧ r ⊆ ins C) ∧ ∃ r ∈ Γ'.R, e ⊆ closure r ∧ ¬ r ⊆ ins C := by
  have heΓ : e ∈ Γ'.E := hCs.2 he
  obtain ⟨p, hp⟩ := he.1
  obtain ⟨W, A₁, A₂, hW, hpW, hsub, hcov, h₁, h₂, d₁, d₂, c₁, c₂⟩ :=
    exists_edge_sides hS Γ' heΓ hp
  have heU : e ⊆ C.U := fun x hx => (he.2.1 hx).1
  have hUins := hs.U_subset_ins hC hCs hl
  -- Regions through a side of `e` near `p`.
  have hreg : ∀ x ∈ W, x ∉ Γ'.U → ∃ r ∈ Γ'.R, x ∈ r ∧ e ⊆ closure r := by
    intro x hxW hxU
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
    refine ⟨r, hr, hxr, edge_subset_closure_of_incident hS heΓ hr ⟨p, hp, ?_⟩⟩
    rcases hcov ⟨hxW, hxU⟩ with hx | hx
    · exact closure_mono (subset_region hr h₁ d₁ hx hxr) (c₁ ⟨hp, hpW⟩)
    · exact closure_mono (subset_region hr h₂ d₂ hx hxr) (c₂ ⟨hp, hpW⟩)
  constructor
  · -- A point of `ins(C)` near `p` that is not on `e`.
    have hnot := closedDisc_not_subset_edge (hs.isClosedDisc C hC hCs hl) hW hpW (hUins (heU hp))
      Γ' heΓ
    obtain ⟨x, ⟨hxW, hxin⟩, hxe⟩ := not_subset.mp hnot
    have hxU : x ∉ Γ'.U := fun h => hxe (hsub ⟨hxW, h⟩)
    obtain ⟨r, hr, hxr, hinc⟩ := hreg x hxW hxU
    refine ⟨r, hr, hinc, ?_⟩
    rcases region_subset_or_disjoint hs hC hCs hl hr with h | h
    · exact h
    · exact absurd hxin (disjoint_left.mp h hxr)
  · -- A point outside `ins(C)` near `p`.
    have hpfr : p ∈ closure (univ \ ins C) := by
      have : p ∈ subBd (ins C) := by
        rw [hs.subBd_eq C hC hCs hl]
        exact heU hp
      exact this.2
    obtain ⟨x, hxW, hxout⟩ := mem_closure_iff.mp hpfr W hW hpW
    have hxU : x ∉ Γ'.U := fun h => hxout.2 (hUins (heU (hsub ⟨hxW, h⟩)))
    obtain ⟨r, hr, hxr, hinc⟩ := hreg x hxW hxU
    exact ⟨r, hr, hinc, fun h => hxout.2 (h hxr)⟩

/-- A region not incident with `e` is a region after `e` is deleted. -/
theorem region_deleteEdge_of_not_incident [LocallyConnectedSpace S] {e r : Set S} (he : e ∈ Γ.E)
    (hr : r ∈ Γ.R) (hinc : Disjoint e (closure r)) : r ∈ (Γ.deleteEdge e).R := by
  obtain ⟨x, hxr⟩ := region_nonempty hr
  have hxU : x ∉ Γ.U := region_subset hr hxr
  have hU := deleteEdge_U Γ he
  have hxU' : x ∉ (Γ.deleteEdge e).U := by
    rw [hU]
    exact fun h => hxU h.1
  refine (mem_R_iff _).mpr ⟨x, hxU', subset_antisymm ?_ ?_⟩
  · refine (region_isPreconnected hr).subset_connectedComponentIn hxr ?_
    intro y hy
    refine ⟨mem_univ _, ?_⟩
    rw [hU]
    exact fun h => region_subset hr hy h.1
  · have hcov : connectedComponentIn (univ \ (Γ.deleteEdge e).U) x ⊆ r ∪ (closure r)ᶜ := by
      intro y hy
      by_cases hyc : y ∈ closure r
      · refine Or.inl ?_
        rcases closure_region_subset hr hyc with h | h
        · exact h
        · exfalso
          have hy' := (connectedComponentIn_subset _ _ hy).2
          rw [hU] at hy'
          have hye : y ∈ e := by
            by_contra hye
            exact hy' ⟨h, hye⟩
          exact disjoint_left.mp hinc hye hyc
      · exact Or.inr hyc
    refine (isPreconnected_connectedComponentIn).subset_left_of_subset_union (region_isOpen hr)
      isClosed_closure.isOpen_compl ?_ hcov ⟨x, ?_, hxr⟩
    · exact disjoint_left.mpr fun y hy h => h (subset_closure hy)
    · exact mem_connectedComponentIn ⟨mem_univ _, hxU'⟩

omit [T2Space S] in
/-- Every region lies in a region of any subdrawing. -/
theorem exists_region_superset {Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) {r : Set S}
    (hr : r ∈ Γ.R) : ∃ r' ∈ Γ'.R, r ⊆ r' := by
  obtain ⟨x, hxr⟩ := region_nonempty hr
  have hxU : x ∉ Γ'.U := fun h => region_subset hr hxr (hsub.U_subset h)
  obtain ⟨r', hr', hxr'⟩ := exists_region_of_notMem hxU
  exact ⟨r', hr', subset_region hr' (region_isPreconnected hr)
    (disjoint_left.mpr fun y hy h => region_subset hr hy (hsub.U_subset h)) hxr hxr'⟩

/-- A point in any nonempty open set is off `U(Γ)`. A drawing has empty interior. -/
theorem exists_notMem_U (hS : IsClosedSurface S)
    {O : Set S} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ y ∈ O, y ∉ Γ.U := by
  obtain ⟨x, hx⟩ := hne
  -- First a point off the vertices.
  obtain ⟨y, hyO, hyV⟩ : ∃ y ∈ O, y ∉ Γ.V := by
    have hF : IsOpen (O ∩ (Γ.V \ {x})ᶜ) :=
      hO.inter (Γ.finite_V.subset sdiff_subset).isClosed.isOpen_compl
    obtain ⟨Z, -, -, hZsub, -, hZcl⟩ := exists_punctured_nbhd hS hF ⟨hx, fun h => h.2 rfl⟩
    obtain ⟨y, hy⟩ : (Z \ {x}).Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty] at hcon
      rw [hcon, closure_empty] at hZcl
      exact hZcl
    exact ⟨y, (hZsub hy.1).1, fun hyV => (hZsub hy.1).2 ⟨hyV, hy.2⟩⟩
  by_cases hyU : y ∈ Γ.U
  · obtain ⟨e, he, hye⟩ := Γ.exists_edge_of_mem hyU hyV
    obtain ⟨W, A₁, A₂, hW, hyW, -, -, -, -, d₁, -, c₁, -⟩ := exists_edge_sides hS Γ he hye
    obtain ⟨a, ⟨haW, haO⟩, ha⟩ := mem_closure_iff.mp (c₁ ⟨hye, hyW⟩) _ (hW.inter hO) ⟨hyW, hyO⟩
    exact ⟨a, haO, disjoint_left.mp d₁ ha⟩
  · exact ⟨y, hyO, hyU⟩

omit [T2Space S] in
/-- If a drawing has a circuit, some circuit `C` has `ins(C)` maximal. -/
theorem exists_maximal_circuit {Γ' C₀ : Drawing S} (ins : Drawing S → Set S) (hC₀ : C₀.IsCircuit)
    (hC₀s : C₀.IsSubdrawing Γ') :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing Γ' ∧
      ∀ C' : Drawing S, C'.IsCircuit → C'.IsSubdrawing Γ' → ins C ⊆ ins C' → ins C' ⊆ ins C := by
  let 𝓒 : Set (Drawing S) := {C | C.IsCircuit ∧ C.IsSubdrawing Γ'}
  have hfin : 𝓒.Finite := by
    refine Set.Finite.of_finite_image (f := fun C : Drawing S => (C.V, C.E)) ?_ ?_
    · refine (Γ'.finite_V.finite_subsets.prod Γ'.finite_edges.finite_subsets).subset ?_
      rintro _ ⟨C, ⟨-, hs⟩, rfl⟩
      exact ⟨hs.1, hs.2⟩
    · intro C _ D _ h
      have h₁ : C.V = D.V := congrArg Prod.fst h
      have h₂ : C.E = D.E := congrArg Prod.snd h
      exact Drawing.ext_of_V_E h₁ h₂
  obtain ⟨X, hX⟩ := (hfin.image ins).exists_maximal ⟨_, C₀, ⟨hC₀, hC₀s⟩, rfl⟩
  obtain ⟨C, ⟨hC, hCs⟩, rfl⟩ := hX.1
  exact ⟨C, hC, hCs, fun C' hC' hC's h => hX.2 ⟨C', ⟨hC', hC's⟩, rfl⟩ h⟩

omit [T2Space S] in
theorem IsCircuit.E_nonempty {C : Drawing S} (hC : C.IsCircuit) : C.E.Nonempty := by
  obtain ⟨u, W, -, hpos, -, hE⟩ := hC
  cases W with
  | nil _ => simp at hpos
  | @cons _ w _ e h r => exact ⟨e, h.1⟩

omit [T2Space S] in
/-- Either an edge is incident with a region, or it misses the closure of the region. -/
theorem edge_incident_or_disjoint (hS : IsClosedSurface S)
    {e r : Set S} (he : e ∈ Γ.E) (hr : r ∈ Γ.R) :
    e ⊆ closure r ∨ Disjoint e (closure r) := by
  by_cases h : (e ∩ closure r).Nonempty
  · exact Or.inl (edge_subset_closure_of_incident hS he hr h)
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h))

/-- The inductive claim in the proof of (4.4) (page 80): if `r₁, r₂` are distinct regions of a
confined `Γ'`, then `Γ'` captures at least one of them. -/
theorem captures_of_ne (hS : IsClosedSurface S) [PreconnectedSpace S]
    {k : ℕ} {ins : Drawing S → Set S} (hs : IsSlope Γ k ins)
    {Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ') {r₁ r₂ : Set S}
    (h₁ : r₁ ∈ Γ'.R) (h₂ : r₂ ∈ Γ'.R) (hne : r₁ ≠ r₂) :
    Captures ins k Γ' r₁ ∨ Captures ins k Γ' r₂ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  induction hn : Γ'.E.ncard using Nat.strong_induction_on generalizing Γ' r₁ r₂ with
  | _ n ih =>
    have hs' := theorem_4_2_proof hs hsub
    by_cases hcirc : ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing Γ'
    · obtain ⟨C, hC, hCs⟩ := hcirc
      have hl := hconf C hC hCs
      obtain ⟨e, he⟩ := IsCircuit.E_nonempty hC
      have heΓ : e ∈ Γ'.E := hCs.2 he
      obtain ⟨⟨r', hr', hinc', hsubC⟩, -⟩ := exists_regions_of_circuit_edge hS hs' hC hCs hl he
      have hcap : ∀ r, r = r' → Captures ins k Γ' r := fun r hrr => ⟨C, hC, hCs, hl, hrr ▸ hsubC⟩
      by_cases he₁ : r₁ = r'
      · exact Or.inl (hcap _ he₁)
      by_cases he₂ : r₂ = r'
      · exact Or.inr (hcap _ he₂)
      -- The step with `r₁` not incident with `e`.
      have hstep : ∀ {a b : Set S}, a ∈ Γ'.R → b ∈ Γ'.R → a ≠ b → Disjoint e (closure a) →
          Captures ins k Γ' a ∨ Captures ins k Γ' b := by
        intro a b ha hb hab hda
        have hdel := deleteEdge_isSubdrawing Γ' e
        have ha' := region_deleteEdge_of_not_incident heΓ ha hda
        obtain ⟨b', hb', hbsub⟩ := exists_region_superset hdel hb
        have hab' : a ≠ b' := by
          rintro rfl
          obtain ⟨x, hx⟩ := region_nonempty hb
          exact hab (region_eq_of_mem ha hb (hbsub hx) hx)
        have hlt : (Γ'.deleteEdge e).E.ncard < n := by
          rw [deleteEdge_E, ← hn]
          exact Set.ncard_sdiff_singleton_lt_of_mem heΓ Γ'.finite_edges
        have hconf' : IsConfined k (Γ'.deleteEdge e) := fun D hD hDs => hconf D hD (hDs.trans hdel)
        rcases ih _ hlt (hdel.trans hsub) hconf' ha' hb' hab' rfl with
          ⟨D, hD, hDs, hl', hin⟩ | ⟨D, hD, hDs, hl', hin⟩
        · exact Or.inl ⟨D, hD, hDs.trans hdel, hl', hin⟩
        · exact Or.inr ⟨D, hD, hDs.trans hdel, hl', hbsub.trans hin⟩
      rcases edge_incident_or_disjoint hS heΓ h₁ with i₁ | d₁
      · rcases edge_incident_or_disjoint hS heΓ h₂ with i₂ | d₂
        · rcases region_incident_two hS heΓ hr' h₁ h₂ hinc' i₁ i₂ with h | h | h
          · exact absurd h.symm he₁
          · exact absurd h.symm he₂
          · exact absurd h hne
        · exact (hstep h₂ h₁ (Ne.symm hne) d₂).symm
      · exact hstep h₁ h₂ hne d₁
    · push Not at hcirc
      exact absurd (region_eq_of_noCircuit hS (Γ := Γ')
        (fun C hC hCs => hcirc C hC hCs) h₁ h₂) hne

/-- Graph Minors XI, (4.4) (page 80): "If $\Gamma'$ is confined then $\Sigma -
\operatorname{ins}(\Gamma')$ is a region of $\Gamma'$."
Here `Σ` is a connected closed surface. -/
theorem theorem_4_4_proof (hS : IsClosedSurface S) [ConnectedSpace S]
    {k : ℕ} {ins : Drawing S → Set S} (hs : IsSlope Γ k ins)
    {Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ') :
    univ \ insOf ins Γ' ∈ Γ'.R := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hs' := theorem_4_2_proof hs hsub
  -- There is a region that is not captured.
  obtain ⟨r₀, hr₀, hnot⟩ : ∃ r₀ ∈ Γ'.R, ¬ Captures ins k Γ' r₀ := by
    by_cases hcirc : ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing Γ'
    · obtain ⟨C₀, hC₀, hC₀s⟩ := hcirc
      obtain ⟨C, hC, hCs, hmax⟩ := exists_maximal_circuit ins hC₀ hC₀s
      obtain ⟨e, he⟩ := IsCircuit.E_nonempty hC
      obtain ⟨-, r, hr, hinc, hnsub⟩ :=
        exists_regions_of_circuit_edge hS hs' hC hCs (hconf C hC hCs) he
      obtain ⟨x, hx⟩ := he.1
      exact ⟨r, hr, theorem_4_3_ii hs hsub hconf hC hCs hmax he ⟨x, hx, hinc hx⟩ hnsub⟩
    · push Not at hcirc
      obtain ⟨y, -, hy⟩ := exists_notMem_U (Γ := Γ') hS isOpen_univ univ_nonempty
      obtain ⟨r, hr, -⟩ := exists_region_of_notMem hy
      refine ⟨r, hr, ?_⟩
      rintro ⟨C, hC, hCs, -⟩
      exact hcirc C hC hCs
  have hEq : univ \ insOf ins Γ' = r₀ := by
    ext x
    constructor
    · rintro ⟨-, hx⟩
      have hxU : x ∉ Γ'.U := fun h => hx (Or.inl h)
      obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
      have hrc : ¬ Captures ins k Γ' r := by
        rintro ⟨C, hC, hCs, -, hin⟩
        exact hx (Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hin hxr⟩))
      by_cases hre : r = r₀
      · exact hre ▸ hxr
      · rcases captures_of_ne hS hs hsub hconf hr hr₀ hre with h | h
        · exact absurd h hrc
        · exact absurd h hnot
    · intro hx
      refine ⟨mem_univ _, ?_⟩
      rintro (hxU | hxC)
      · exact region_subset hr₀ hx hxU
      · obtain ⟨C, ⟨hC, hCs⟩, hxC⟩ := mem_iUnion₂.mp hxC
        have hl := hconf C hC hCs
        rcases region_subset_or_disjoint hs' hC hCs hl hr₀ with h | h
        · exact hnot ⟨C, hC, hCs, hl, h⟩
        · exact disjoint_left.mp h hx hxC
  rw [hEq]
  exact hr₀

/-- The induction in the proof of (4.5). -/
private theorem captures_aux (hS : IsClosedSurface S) [PreconnectedSpace S]
    {k : ℕ} {ins : Drawing S → Set S} (hs : IsSlope Γ k ins)
    {Γ' C : Drawing S} (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ') (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing Γ) (hl : C.length < k) {r' : Set S} {Γ'' : Drawing S}
    (hsub' : Γ''.IsSubdrawing Γ') {r'' : Set S} (hr'' : r'' ∈ Γ''.R) (hr'r : r' ⊆ r'')
    (hrΔ : r'' ⊆ ins C) : Captures ins k Γ' r' := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hΔcl : IsClosed (ins C) := (hs.isClosedDisc C hC hCs hl).isClosed
  induction hn : Γ''.E.ncard using Nat.strong_induction_on generalizing Γ'' r'' with
  | _ n ih =>
    have hsubΓ := hsub'.trans hsub
    have hs'' := theorem_4_2_proof hs hsubΓ
    by_cases hcirc : ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing Γ''
    · obtain ⟨D, hD, hDs⟩ := hcirc
      have hDl := hconf D hD (hDs.trans hsub')
      by_cases hdel : ∃ g ∈ D.E, ∃ r₃ ∈ (Γ''.deleteEdge g).R, r'' ⊆ r₃ ∧ r₃ ⊆ ins C
      · obtain ⟨g, hg, r₃, hr₃, h₁, h₂⟩ := hdel
        have hgΓ : g ∈ Γ''.E := hDs.2 hg
        have hlt : (Γ''.deleteEdge g).E.ncard < n := by
          rw [deleteEdge_E, ← hn]
          exact Set.ncard_sdiff_singleton_lt_of_mem hgΓ Γ''.finite_edges
        exact ih _ hlt ((deleteEdge_isSubdrawing Γ'' g).trans hsub') hr₃ (hr'r.trans h₁) h₂ rfl
      · push Not at hdel
        -- Every edge of `D` is incident with `r''`, so `U(D)` lies in `ins(C)`.
        have hincD : ∀ g ∈ D.E, g ⊆ closure r'' := by
          intro g hg
          rcases edge_incident_or_disjoint hS (hDs.2 hg) hr'' with h | h
          · exact h
          · exact absurd hrΔ (hdel g hg r''
              (region_deleteEdge_of_not_incident (hDs.2 hg) hr'' h) subset_rfl)
        have hclΔ : closure r'' ⊆ ins C := hΔcl.closure_subset_iff.mpr hrΔ
        have hclg : ∀ g ∈ D.E, closure g ⊆ ins C := fun g hg =>
          (closure_minimal (hincD g hg) isClosed_closure).trans hclΔ
        have hU : D.U ⊆ ins C := by
          rw [D.U_eq]
          refine union_subset ?_ (iUnion₂_subset hclg)
          intro v hv
          obtain ⟨W, -, hpos, -, -⟩ := exists_walk_at hD hv
          cases W with
          | nil _ => simp at hpos
          | @cons _ w _ e h r =>
            have : v ∈ closure e ∩ D.V := by rw [h.2.2.2]; simp
            exact hclg e h.1 this.1
        have hDΓ := (hDs.trans hsub')
        have hinsD : ins D ⊆ ins C :=
          hs.monotone D C hD (hDΓ.trans hsub) hDl hC hCs hl hU
        obtain ⟨g, hg⟩ := IsCircuit.E_nonempty hD
        have hgΓ : g ∈ Γ''.E := hDs.2 hg
        obtain ⟨⟨ri, hri, iin, hrisub⟩, ro, hro, iout, hronot⟩ :=
          exists_regions_of_circuit_edge hS hs'' hD hDs hDl hg
        have hio : ri ≠ ro := fun h => hronot (h ▸ hrisub)
        rcases region_incident_two hS hgΓ hri hro hr'' iin iout (hincD g hg) with h | h | h
        · exact absurd h hio
        · exact ⟨D, hD, hDΓ, hDl, hr'r.trans (h ▸ hrisub)⟩
        · -- Now `r'' = ro`, and the second region at `g` lies in `ins(C)`.
          exfalso
          have hdels := deleteEdge_isSubdrawing Γ'' g
          obtain ⟨r₃, hr₃, hsub₃⟩ := exists_region_superset hdels hr''
          obtain ⟨x, hx₃, hxout⟩ := not_subset.mp (hdel g hg r₃ hr₃ hsub₃)
          have hxg : x ∉ g := fun h' => hxout (hclΔ (hincD g hg h'))
          have hxU : x ∉ Γ''.U := by
            intro h'
            have := region_subset hr₃ hx₃
            rw [deleteEdge_U Γ'' hgΓ] at this
            exact this ⟨h', hxg⟩
          obtain ⟨t, ht, hxt⟩ := exists_region_of_notMem hxU
          rcases edge_incident_or_disjoint hS hgΓ ht with hit | hdt
          · rcases region_incident_two hS hgΓ hri hro ht iin iout hit with h' | h' | h'
            · exact hio h'
            · exact hxout (hinsD (hrisub (h' ▸ hxt)))
            · exact hxout (hrΔ (h ▸ h' ▸ hxt))
          · have htdel := region_deleteEdge_of_not_incident hgΓ ht hdt
            have ht₃ : t = r₃ := region_eq_of_mem htdel hr₃ hxt hx₃
            obtain ⟨y, hy⟩ := region_nonempty hr''
            have htr : t = r'' := region_eq_of_mem ht hr'' (ht₃ ▸ hsub₃ hy) hy
            exact hxout (hrΔ (htr ▸ hxt))
    · -- Without circuits there is only one region, which would be all of `Σ` off `U(Γ'')`.
      push Not at hcirc
      exfalso
      obtain ⟨e, he⟩ := IsCircuit.E_nonempty hC
      obtain ⟨x, hx⟩ := he.1
      have hxU : x ∈ subBd (ins C) := by
        rw [hs.subBd_eq C hC hCs hl]
        exact (he.2.1 hx).1
      obtain ⟨z, hz⟩ : (ins C)ᶜ.Nonempty := by
        by_contra hcon
        rw [not_nonempty_iff_eq_empty] at hcon
        have h₁ := hxU.2
        rw [← compl_eq_univ_sdiff, hcon, closure_empty] at h₁
        exact h₁
      obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := Γ'') hS hΔcl.isOpen_compl ⟨z, hz⟩
      obtain ⟨t, ht, hyt⟩ := exists_region_of_notMem hyU
      have := region_eq_of_noCircuit hS (Γ := Γ'')
        (fun D hD hDs => hcirc D hD hDs) ht hr''
      exact hyO (hrΔ (this ▸ hyt))

/-- Graph Minors XI, (4.5) (pages 80–81): "Let $\Gamma' \subseteq \Gamma$ be confined, and let $r'
\in R(\Gamma')$. Suppose that
$\Gamma$ captures $r'$. Then so does $\Gamma'$." The paper takes a circuit of `Γ'` bounding a closed
disc
in `ins(C)` around `r'`. We replace this step by `captures_aux`. -/
theorem theorem_4_5_proof (hS : IsClosedSurface S) [PreconnectedSpace S]
    {k : ℕ} {ins : Drawing S → Set S} (hs : IsSlope Γ k ins)
    {Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ') {r' : Set S}
    (hr' : r' ∈ Γ'.R) (hcap : Captures ins k Γ r') : Captures ins k Γ' r' := by
  obtain ⟨C, hC, hCs, hl, hin⟩ := hcap
  exact captures_aux hS hs hsub hconf hC hCs hl (Drawing.IsSubdrawing.refl Γ') hr'
    subset_rfl hin

end GraphMinor.GM11
