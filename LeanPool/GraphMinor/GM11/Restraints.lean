/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PerimeterCount
public import LeanPool.GraphMinor.GM11.Section8

/-!
# The outside of a set, and restraints

`theorem_7_6` is (7.6) of Graph Minors XI, for sets other than the whole surface. The paper derives
it from
(7.5) with a set `Y` of two points. We derive it from the collar of a perimeter walk, which is
shorter here,
since that collar is already there: each component of the complement of `X` meets the collar.

From this, `compl_mem_R` says that `Σ - X` is a region of `Γ ∩ bd(X)`. `theorem_8_3` and
`theorem_8_4` are
(8.3) and (8.4).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A path-connected set in a Hausdorff space is arc-connected. -/
theorem isArcConnected_of_isPathConnected [T2Space S] {C : Set S} (hpc : IsPathConnected C) :
    IsArcConnected C := by
  intro a ha b hb hab
  have hj := hpc.joinedIn a ha b hb
  obtain ⟨e, hec, hei, he0, he1, hsub⟩ := exists_arc_of_path (γ := hj.somePath)
    hj.somePath.continuous
    (by simpa using hab)
  have hc : CompactSpace (range e) := isCompact_iff_compactSpace.mp (isCompact_range hec)
  refine ⟨range e, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨u, hu⟩ := hsub (mem_range_self t)
    exact hu ▸ hj.somePath_mem u
  · have hjb : Function.Bijective (rangeFactorization e) :=
      ⟨fun x y hxy => hei (congrArg Subtype.val hxy), rangeFactorization_surjective⟩
    refine ⟨(Continuous.subtype_mk hec _).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective _ hjb), ?_, ?_⟩
    · exact he0.trans (by simp)
    · exact he1.trans (by simp)

section Runs

variable {Γ : Drawing S} {φ : ℝ → S}

/-- Each vertex of a walk is a point of its curve. -/
theorem runs_support {u v : S} (W : GraphWalk Γ.toGraph u v) :
    ∀ {a b : ℝ}, RunsAlongOn Γ φ a b W → ∀ x ∈ W.support, ∃ t ∈ Icc a b, φ t = x := by
  induction W with
  | nil hv =>
    rintro a b ⟨rfl, hu⟩ x hx
    obtain rfl : x = _ := by simpa [GraphWalk.support] using hx
    exact ⟨a, ⟨le_rfl, le_rfl⟩, hu⟩
  | @cons x y w e hlink rest ih =>
    rintro a b ⟨c, hac, hu, -, -, hrest⟩ t ht
    rcases List.mem_cons.mp ht with rfl | h
    · exact ⟨a, ⟨le_rfl, (hac.trans_le (runs_le rest hrest)).le⟩, hu⟩
    · obtain ⟨s, hs, hse⟩ := ih hrest t h
      exact ⟨s, ⟨hac.le.trans hs.1, hs.2⟩, hse⟩

/-- A point of the curve that is a vertex is a vertex of the walk. -/
theorem runs_vertex {u v : S} (W : GraphWalk Γ.toGraph u v) :
    ∀ {a b : ℝ}, RunsAlongOn Γ φ a b W → ∀ t ∈ Icc a b, φ t ∈ Γ.V → φ t ∈ W.support := by
  induction W with
  | nil hv =>
    rintro a b ⟨rfl, hu⟩ t ⟨h₁, h₂⟩ -
    obtain rfl : t = a := le_antisymm h₂ h₁
    simp [GraphWalk.support, hu]
  | @cons x y w e hlink rest ih =>
    rintro a b ⟨c, hac, hu, -, him, hrest⟩ t ht hV
    rcases lt_or_ge t c with htc | htc
    · rcases eq_or_lt_of_le ht.1 with rfl | hat
      · exact hu ▸ List.mem_cons_self
      · have hm : φ t ∈ e := him ▸ mem_image_of_mem φ ⟨hat, htc⟩
        exact ((hlink.1.2.1 hm).2 hV).elim
    · exact List.mem_cons_of_mem _ (ih hrest t ⟨htc, ht.2⟩ hV)

end Runs

variable [ConnectedSpace S]

/-- The complement of a closed set `X` with a collar is connected: each component of the complement
meets
the collar. -/
theorem isConnected_compl_of_collar (hS : IsClosedSurface S) {X : Set S} (hXc : IsClosed X)
    (hne : X.Nonempty) (hu : X ≠ univ) (h : C(Circle × I, S))
    (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ X) (hbot : ∀ z, h (z, 0) ∈ X)
    (hop : IsOpen (X ∪ h '' {p | p.2 < 1})) : IsConnected Xᶜ := by
  have hlp : LocallyPathConnectedSpace S := IsClosedSurface.locallyPathConnectedSpace hS
  obtain ⟨a, ha⟩ : ∃ a, a ∉ X := by
    by_contra hall
    push Not at hall
    exact hu (eq_univ_of_forall hall)
  let T : Set S := h '' (univ ×ˢ Ioo 0 1)
  have hTc : IsPreconnected T :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image _ h.continuous.continuousOn
  have hTX : T ⊆ Xᶜ := by
    rintro _ ⟨p, hp, rfl⟩
    exact hoff p hp.2.1
  have hopc : IsOpen Xᶜ := hXc.isOpen_compl
  -- Each component meets `T`.
  have hmeet : ∀ b ∈ Xᶜ, (connectedComponentIn Xᶜ b ∩ T).Nonempty := by
    intro b hb
    set D := connectedComponentIn Xᶜ b with hD
    have hDo : IsOpen D := hopc.connectedComponentIn
    have hDne : D.Nonempty := ⟨b, mem_connectedComponentIn hb⟩
    have hDX : D ⊆ Xᶜ := connectedComponentIn_subset _ _
    have hDu : D ≠ univ := fun h' => by
      obtain ⟨x, hx⟩ := hne
      exact hDX (h' ▸ mem_univ x) hx
    obtain ⟨p, hp⟩ : (frontier D).Nonempty := nonempty_frontier_iff.mpr ⟨hDne, hDu⟩
    have hpX : p ∈ X := by
      by_contra hpX
      -- A boundary point of a component lies outside the open set only if it is in the component.
      have hpc : p ∈ D := by
        have hconn : IsPreconnected (D ∪ connectedComponentIn Xᶜ p) := by
          refine IsPreconnected.union' ?_ isPreconnected_connectedComponentIn
            isPreconnected_connectedComponentIn
          obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp hp.1 _ hopc.connectedComponentIn
            (mem_connectedComponentIn hpX)
          exact ⟨z, hz₂, hz₁⟩
        have hsub := IsPreconnected.subset_connectedComponentIn hconn (Or.inl
          (mem_connectedComponentIn hb))
          (union_subset hDX (connectedComponentIn_subset _ _))
        exact hsub (Or.inr (mem_connectedComponentIn hpX))
      exact hp.2 (by
        rw [hDo.interior_eq]
        exact hpc)
    obtain ⟨d, hd₁, hd₂⟩ := mem_closure_iff.mp hp.1 _ hop (Or.inl hpX)
    have hdX : d ∉ X := hDX hd₂
    obtain ⟨q, hq, rfl⟩ := hd₁.resolve_left hdX
    have hq0 : 0 < q.2 := by
      by_contra hq0
      have ht : q.2 = 0 := le_antisymm (not_lt.mp hq0) (unitInterval.nonneg _)
      have hqz : q = (q.1, 0) := Prod.ext rfl ht
      exact hdX (hqz ▸ hbot q.1)
    exact ⟨h q, hd₂, q, ⟨mem_univ _, hq0, hq⟩, rfl⟩
  obtain ⟨c, hcD, hcT⟩ := hmeet a ha
  have hcX : c ∈ Xᶜ := hTX hcT
  have hall : Xᶜ ⊆ connectedComponentIn Xᶜ c := by
    intro b hb
    obtain ⟨d, hd₁, hd₂⟩ := hmeet b hb
    have hdc : IsPreconnected (T ∪ connectedComponentIn Xᶜ b) :=
      IsPreconnected.union' ⟨d, hd₂, hd₁⟩ hTc isPreconnected_connectedComponentIn
    exact IsPreconnected.subset_connectedComponentIn hdc (Or.inl hcT)
      (union_subset hTX (connectedComponentIn_subset _ _)) (Or.inr (mem_connectedComponentIn hb))
  have heq : connectedComponentIn Xᶜ c = Xᶜ :=
    subset_antisymm (connectedComponentIn_subset _ _) hall
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.mpr hcX

variable [T2Space S]

omit [ConnectedSpace S] in
theorem IsRestraint.ne_univ {Γ : Drawing S} {ins : Drawing S → Set S} {k : ℕ} {X : Set S}
    (hr : IsRestraint Γ ins k X) : X ≠ univ := by
  rintro rfl
  apply hr.compl_not_subset
  simp

section Main

variable (hS : IsClosedSurface S)
  {Γ : Drawing S} {X : Set S}

include hS

/-- The complement of a closed, simply-connected, `Γ`-nice set is connected. -/
theorem isConnected_compl (hXc : IsClosed X) (hXn : IsGammaNice Γ X) (hXs : IsSimplyConnectedSet X)
    (hne : X.Nonempty) (hu : X ≠ univ) : IsConnected Xᶜ := by
  obtain ⟨u, W, ⟨h, -, hoff, hrng, hop, -⟩, -⟩ := exists_perimeterWalk hS hXc hXn hXs hne hu
  rw [subBd_eq_frontier] at hrng
  exact isConnected_compl_of_collar hS hXc hne hu h hoff
    (fun z => hXc.frontier_subset (hrng ▸ mem_range_self z)) hop

/-- **(7.6)** of Graph Minors XI (page 94): "If $\Sigma$ is connected, and $X \subseteq \Sigma$ is
closed, nice, and simply-connected,
then $\Sigma - X$ is arc-wise connected." Here `X` is non-empty and `Γ`-nice. -/
theorem theorem_7_6_proof (hXc : IsClosed X) (hXn : IsGammaNice Γ X) (hXs : IsSimplyConnectedSet X)
    (hne : X.Nonempty) : IsArcConnected Xᶜ := by
  have hlp : LocallyPathConnectedSpace S := IsClosedSurface.locallyPathConnectedSpace hS
  by_cases hu : X = univ
  · intro a ha
    exact (ha (hu ▸ mem_univ a)).elim
  have hc := isConnected_compl hS hXc hXn hXs hne hu
  exact isArcConnected_of_isPathConnected (hXc.isOpen_compl.isConnected_iff_isPathConnected.mp hc)

/-- `Σ - X` is a region of `Γ ∩ bd(X)`. The proof of (8.3) gets this from (7.6). -/
theorem compl_mem_R (hXc : IsClosed X) (hXn : IsGammaNice Γ X) (hXs : IsSimplyConnectedSet X)
    (hne : X.Nonempty) (hu : X ≠ univ) : Xᶜ ∈ (Γ.interSet (frontier X)).R := by
  have hc := isConnected_compl hS hXc hXn hXs hne hu
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  set B := Γ.interSet (frontier X)
  have hBU : B.U = frontier X := frontier_interSet hS hXc hXn
  obtain ⟨a, ha⟩ := hc.nonempty
  have haU : a ∉ B.U := fun h => ha (hXc.frontier_subset (hBU ▸ h))
  obtain ⟨p, hp, hap⟩ := exists_region_of_notMem haU
  have hdis : Disjoint Xᶜ B.U := disjoint_left.mpr fun x hx hxU =>
    hx (hXc.frontier_subset (hBU ▸ hxU))
  have h₁ : Xᶜ ⊆ p := subset_region hp hc.isPreconnected hdis ha hap
  have h₂ : p ⊆ Xᶜ := by
    have hcov : p ⊆ interior X ∪ Xᶜ := by
      intro x hx
      by_cases hxX : x ∈ X
      · refine Or.inl ?_
        by_contra hint
        exact region_subset hp hx (hBU ▸ (⟨subset_closure hxX, hint⟩ : x ∈ frontier X))
      · exact Or.inr hxX
    have hdj : Disjoint (interior X) Xᶜ := disjoint_left.mpr fun x hx h => h (interior_subset hx)
    rcases (region_isPreconnected hp).subset_or_subset isOpen_interior hXc.isOpen_compl hdj hcov
      with
      h | h
    · exact (ha (interior_subset (h hap))).elim
    · exact h
  exact subset_antisymm h₂ h₁ ▸ hp

omit [ConnectedSpace S] in
/-- The vertices and edges of a shortest perimeter walk are those of `Γ ∩ bd(X)`. -/
theorem walkDrawing_eq (hXc : IsClosed X) (hXn : IsGammaNice Γ X) {u : S}
    {W : GraphWalk Γ.toGraph u u} (hW : IsPerimeterWalk Γ X W)
    (hc : ∀ e ∈ Γ.E, edgeCount W.edges e = perimeterCount X e) :
    walkDrawing Γ W = Γ.interSet (frontier X) := by
  classical
  have hE : ∀ e, e ∈ W.edges ↔ e ∈ Γ.E ∧ e ⊆ frontier X := by
    intro e
    constructor
    · intro he
      have heE := mem_E_of_mem_edges W he
      have hpos : 0 < edgeCount W.edges e := List.count_pos_iff.mpr he
      rw [hc e heE] at hpos
      by_cases hef : (e ∩ frontier X).Nonempty
      · obtain ⟨y, hy, hyf⟩ := hef
        exact ⟨heE, edge_subset_frontier hS hXc hXn heE hy hyf⟩
      · simp [perimeterCount, hef] at hpos
    · rintro ⟨heE, hsub⟩
      obtain ⟨y, hy⟩ : e.Nonempty := heE.1
      have hef : (e ∩ frontier X).Nonempty := ⟨y, hy, hsub hy⟩
      have hpos : 0 < edgeCount W.edges e := by
        rw [hc e heE]
        simp only [perimeterCount, hef, ite_true]
        split_ifs <;> omega
      exact List.count_pos_iff.mp hpos
  have hV : {x | x ∈ W.support} = Γ.V ∩ frontier X := by
    obtain ⟨h, -, -, hrng, -, hcase⟩ := hW
    rw [subBd_eq_frontier] at hrng
    ext x
    constructor
    · intro hx
      refine ⟨mem_V_of_mem_support W hx, ?_⟩
      rcases hcase with ⟨h0, hu⟩ | ⟨-, hrun⟩
      · have hxu : x = u := by
          cases W with
          | nil hv => simpa [GraphWalk.support] using hx
          | cons hl rest => simp [GraphWalk.length, GraphWalk.edges] at h0
        rw [hxu, ← hu 1, ← hrng]
        exact ⟨1, rfl⟩
      · obtain ⟨t, -, rfl⟩ := runs_support W hrun x hx
        rw [← hrng]
        exact ⟨_, rfl⟩
    · rintro ⟨hxV, hxf⟩
      obtain ⟨z, hz⟩ := hrng.superset hxf
      rcases hcase with ⟨h0, hu⟩ | ⟨-, hrun⟩
      · have hzu : x = u := hz.symm.trans (hu z)
        rw [hzu]
        exact W.start_mem_support
      · obtain ⟨t, ht, rfl⟩ := exists_collar_time z
        have hz' : h (Circle.exp (2 * Real.pi * t), 0) = x := hz
        have hmem := runs_vertex W hrun t ⟨ht.1, ht.2.le⟩ (by
          change h (_, 0) ∈ Γ.V
          rw [hz']
          exact hxV)
        change h (_, 0) ∈ W.support at hmem
        rw [hz'] at hmem
        exact hmem
  have hEs : {e | e ∈ W.edges} = {e | e ∈ Γ.E ∧ e ⊆ frontier X} := by
    ext e
    exact hE e
  change Γ.span {x | x ∈ W.support} {e | e ∈ W.edges} = Γ.span (Γ.V ∩ frontier X) _
  rw [hV, hEs]

variable {ins : Drawing S → Set S} {k : ℕ}

/-- A restraint has a shortest perimeter walk, of length `< 2θ`, whose drawing is `Γ ∩ bd(X)`. -/
theorem IsRestraint.exists_walk (hr : IsRestraint Γ ins k X) :
    ∃ (u : S) (W : GraphWalk Γ.toGraph u u), IsPerimeterWalk Γ X W ∧
      W.length = perimeterWalkLength Γ X ∧ W.length < k ∧
      (∀ e ∈ Γ.E, edgeCount W.edges e = perimeterCount X e) ∧
      walkDrawing Γ W = Γ.interSet (frontier X) := by
  obtain ⟨u, W, hW, h₁, -, h₂⟩ := exists_minimal_perimeterWalk hS hr.isClosed hr.isGammaNice
    hr.isSimplyConnected hr.nonempty hr.ne_univ
  exact ⟨u, W, hW, h₁, h₁ ▸ hr.length_lt, h₂, walkDrawing_eq hS hr.isClosed hr.isGammaNice hW h₂⟩

/-- `Γ ∩ bd(X)` is confined, for a restraint `X`. -/
theorem IsRestraint.isConfined (hr : IsRestraint Γ ins k X) :
    IsConfined k (Γ.interSet (frontier X)) := by
  obtain ⟨u, W, -, -, hl, -, hd⟩ := hr.exists_walk hS
  intro C hC hCs
  have hsub : C.E ⊆ {x | x ∈ W.edges} := by
    intro e he
    have h₁ : e ∈ (Γ.interSet (frontier X)).E := hCs.2 he
    rw [← hd] at h₁
    change e ∈ (Γ.span _ _).E at h₁
    rw [Γ.span_E] at h₁
    exact h₁.1
  have hfin : {x | x ∈ W.edges}.Finite := W.edges.finite_toSet
  calc C.length = C.E.ncard := rfl
    _ ≤ {x | x ∈ W.edges}.ncard := ncard_le_ncard hsub hfin
    _ ≤ W.edges.length := ncard_mem_list_le _
    _ < k := hl

/-- **(8.3)** of Graph Minors XI (page 97): "If $X \subseteq \Sigma$ is a restraint, then
$\mathrm{ins}(\Gamma \cap bd(X)) = X$." -/
theorem theorem_8_3_proof (hs : IsSlope Γ k ins) (hr : IsRestraint Γ ins k X) :
    insOf ins (Γ.interSet (subBd X)) = X := by
  rw [subBd_eq_frontier]
  have hnot := hr.compl_not_subset
  rw [subBd_eq_frontier] at hnot
  have hr₁ := compl_mem_R hS hr.isClosed hr.isGammaNice hr.isSimplyConnected hr.nonempty
    hr.ne_univ
  have hr₂ := theorem_4_4_proof hS hs (Drawing.span_isSubdrawing Γ _ _)
    (hr.isConfined hS)
  obtain ⟨x, hx, hxi⟩ := not_subset.mp hnot
  have heq := region_eq_of_mem hr₁ hr₂ (hx.2 : x ∈ Xᶜ) ⟨mem_univ x, hxi⟩
  have := congrArg compl heq
  rw [compl_compl, ← compl_eq_univ_sdiff, compl_compl] at this
  exact this.symm

/-- `ins(W) = X` for a shortest perimeter walk `W` of a restraint `X`, as the proof of (8.4) uses
it. -/
theorem insWalk_eq (hs : IsSlope Γ k ins) (hr : IsRestraint Γ ins k X) {u : S}
    {W : GraphWalk Γ.toGraph u u} (hd : walkDrawing Γ W = Γ.interSet (frontier X)) :
    insWalk ins Γ W = X := by
  have := theorem_8_3_proof hS hs hr
  rw [subBd_eq_frontier] at this
  rw [insWalk, hd, this]

/-- **(8.4)** of Graph Minors XI (page 97): "If $X_1, X_2, X_3$ are restraints then $X_1 \cup X_2
\cup X_3 \ne \Sigma$." -/
theorem theorem_8_4_proof (hs : IsSlope Γ k ins) {X₁ X₂ X₃ : Set S} (h₁ : IsRestraint Γ ins k X₁)
    (h₂ : IsRestraint Γ ins k X₂) (h₃ : IsRestraint Γ ins k X₃) : X₁ ∪ X₂ ∪ X₃ ≠ univ := by
  obtain ⟨u₁, W₁, -, -, l₁, -, d₁⟩ := h₁.exists_walk hS
  obtain ⟨u₂, W₂, -, -, l₂, -, d₂⟩ := h₂.exists_walk hS
  obtain ⟨u₃, W₃, -, -, l₃, -, d₃⟩ := h₃.exists_walk hS
  obtain ⟨r, hr, n₁, n₂, n₃⟩ := theorem_8_2_proof hS hs W₁ W₂ W₃ l₁ l₂ l₃
  rw [insWalk_eq hS hs h₁ d₁] at n₁
  rw [insWalk_eq hS hs h₂ d₂] at n₂
  rw [insWalk_eq hS hs h₃ d₃] at n₃
  intro hun
  obtain ⟨x, hx⟩ := region_nonempty hr
  rcases (hun ▸ mem_univ x : x ∈ X₁ ∪ X₂ ∪ X₃) with (h | h) | h
  · exact n₁ (nice_region h₁.isGammaNice hr ⟨x, hx, h⟩)
  · exact n₂ (nice_region h₂.isGammaNice hr ⟨x, hx, h⟩)
  · exact n₃ (nice_region h₃.isGammaNice hr ⟨x, hx, h⟩)

end Main

end GraphMinor.GM11
