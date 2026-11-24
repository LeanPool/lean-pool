/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.ArcDrawings
public import LeanPool.GraphMinor.GM11.Section6

/-!
# The cells of a 2-cell painting

We use the following facts to reduce radial drawings of paintings to radial drawings of drawings.

- `discRay`: in a closed disc with a chart, the line from the centre to a point. Hence a closed disc
  minus finitely many points of its boundary is arc-wise connected (`isPathConnected_disc_sdiff`).
- `isOpenDisc_interior`: the interior of a closed disc in a surface is an open disc.
- `Cell.isClosed_U`, `Cell.closure_sdiff_V`, `Cell.closure_inter_subset_V`: if all regions of
  a painting are open discs, then `U` is closed, a cell is its closure minus the vertices, and two
  cells meet only in vertices.
- `componentsIn_of_partition`: the components of a union of disjoint connected open sets.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The point `t z` of the closed unit disc. -/
def scaleDisc (t : I) (z : ClosedUnitDisc) : ClosedUnitDisc :=
  ⟨(t : ℝ) • z.1, by
    have hz : ‖z.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using z.2
    have ht : (t : ℝ) ≤ 1 := t.2.2
    have h0 : (0 : ℝ) ≤ t := t.2.1
    have : ‖(t : ℝ) • z.1‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg h0]
      nlinarith [norm_nonneg z.1]
    simpa [ClosedUnitDisc] using this⟩

theorem continuous_scaleDisc (z : ClosedUnitDisc) : Continuous fun t : I => scaleDisc t z :=
  Continuous.subtype_mk (by fun_prop) _

theorem scaleDisc_one (z : ClosedUnitDisc) : scaleDisc 1 z = z := by
  apply Subtype.ext
  simp [scaleDisc]

theorem scaleDisc_zero (z w : ClosedUnitDisc) : scaleDisc 0 z = scaleDisc 0 w := by
  apply Subtype.ext
  simp [scaleDisc]

theorem norm_scaleDisc (t : I) (z : ClosedUnitDisc) : ‖(scaleDisc t z).1‖ = t * ‖z.1‖ := by
  simp only [scaleDisc, norm_smul]
  rw [Real.norm_of_nonneg t.2.1]

theorem norm_le_one_disc (z : ClosedUnitDisc) : ‖z.1‖ ≤ 1 := by
  simpa [ClosedUnitDisc] using z.2

/-- The centre of the closed unit disc. -/
def discCentre : ClosedUnitDisc := ⟨0, by simp [ClosedUnitDisc]⟩

theorem scaleDisc_zero_eq (z : ClosedUnitDisc) : scaleDisc 0 z = discCentre := by
  apply Subtype.ext
  simp [scaleDisc, discCentre]

/-- A closed disc minus a set of its boundary points is arc-wise connected. -/
theorem isPathConnected_disc_sdiff {D A : Set S} (hD : IsClosedDisc D) (hA : A ∩ D ⊆ discBd D) :
    IsPathConnected (D \ A) := by
  obtain ⟨φ⟩ := id hD
  have hb := disc_boundary D φ
  let c : S := (φ discCentre).1
  have hbd : ∀ z : ClosedUnitDisc, ‖z.1‖ < 1 → (φ z).1 ∉ A := by
    intro z hz hzA
    have : (φ z).1 ∈ discBd D := hA ⟨hzA, (φ z).2⟩
    rw [hb] at this
    obtain ⟨w, hw, he⟩ := this
    have : w = z := φ.injective (Subtype.ext he)
    subst this
    have hw' : ‖w.1‖ = 1 := by simpa [UnitCircle] using hw
    linarith
  have hcA : c ∈ D \ A := ⟨(φ _).2, hbd _ (by simp [discCentre])⟩
  refine ⟨c, hcA, fun {y} hy => ?_⟩
  obtain ⟨z, hz⟩ := φ.surjective ⟨y, hy.1⟩
  have hzy : (φ z).1 = y := by rw [hz]
  let g : I → S := fun t => (φ (scaleDisc t z)).1
  have hg : Continuous g :=
    continuous_subtype_val.comp (φ.continuous.comp (continuous_scaleDisc z))
  have h0 : g 0 = c := by simp only [g, c, scaleDisc_zero_eq]
  have h1 : g 1 = y := by simp only [g, scaleDisc_one, hzy]
  refine ⟨⟨⟨g, hg⟩, h0, h1⟩, fun t => ⟨(φ _).2, ?_⟩⟩
  change g t ∉ A
  have hle := norm_le_one_disc z
  by_cases ht : t = 1
  · rw [ht, h1]
    exact hy.2
  · have ht' : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => ht (Subtype.ext h)
    refine hbd _ ?_
    rw [norm_scaleDisc]
    nlinarith [t.2.1, norm_nonneg z.1]

theorem interior_eq_sdiff_discBd (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D) :
    interior D = D \ discBd D := by
  have : T2Space S := hS.2.1
  rw [← IsClosedDisc.frontier_eq_discBd hS hD]
  have hc : IsClosed D := hD.isCompact.isClosed
  ext x
  constructor
  · intro hx
    exact ⟨interior_subset hx, fun h => h.2 hx⟩
  · rintro ⟨hx, hn⟩
    by_contra h
    exact hn ⟨subset_closure hx, h⟩

/-- The interior of a closed disc in a surface is an open disc. -/
theorem isOpenDisc_interior (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D) :
    IsOpenDisc (D \ discBd D) := by
  refine ⟨interior_eq_sdiff_discBd hS hD ▸ isOpen_interior, ?_⟩
  obtain ⟨φ⟩ := id hD
  have hsub : OpenUnitDisc ⊆ ClosedUnitDisc := Metric.ball_subset_closedBall
  let m : OpenUnitDisc → S := fun z => (φ (inclusion hsub z)).1
  have hm : IsEmbedding m :=
    IsEmbedding.subtypeVal.comp (φ.isEmbedding.comp (IsEmbedding.inclusion hsub))
  have hr : range m = D \ discBd D := by
    rw [disc_boundary D φ]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨(φ _).2, ?_⟩
      rintro ⟨w, hw, he⟩
      have hw' : w = inclusion hsub z := φ.injective (Subtype.ext he)
      subst hw'
      have h₁ : ‖z.1‖ < 1 := by simpa [OpenUnitDisc] using z.2
      have h₂ : ‖z.1‖ = 1 := by simpa [UnitCircle] using hw
      linarith
    · rintro ⟨hy, hn⟩
      obtain ⟨w, hw⟩ := φ.surjective ⟨y, hy⟩
      have hle := norm_le_one_disc w
      have hlt : ‖w.1‖ < 1 := by
        refine lt_of_le_of_ne hle fun h => hn ⟨w, by simpa [UnitCircle] using h, by simp [hw]⟩
      refine ⟨⟨w.1, by simpa [OpenUnitDisc] using hlt⟩, ?_⟩
      simp [m, inclusion, hw]
  exact ⟨hm.toHomeomorph.trans (Homeomorph.setCongr hr)⟩

/-- A point of a set lies in an arc-wise connected component of it. -/
theorem exists_mem_arcComponent {F : Set S} {x : S} (hx : x ∈ F) :
    ∃ C ∈ arcComponentsIn F, x ∈ C := by
  refine ⟨pathComponentIn F x, ⟨⟨x, mem_pathComponentIn_self hx⟩, pathComponentIn_subset,
    isPathConnected_pathComponentIn hx, fun D hD hc hsub => ?_⟩, mem_pathComponentIn_self hx⟩
  exact subset_antisymm (hc.subset_pathComponentIn (hsub (mem_pathComponentIn_self hx)) hD) hsub

/-- Two arc-wise connected components with a common point are equal. -/
theorem arcComponent_eq {F C D : Set S} (hC : C ∈ arcComponentsIn F) (hD : D ∈ arcComponentsIn F)
    {x : S} (hxC : x ∈ C) (hxD : x ∈ D) : C = D := by
  have hu : IsPathConnected (C ∪ D) := hC.2.2.1.union hD.2.2.1 ⟨x, hxC, hxD⟩
  have h₁ := hC.2.2.2 _ (union_subset hC.2.1 hD.2.1) hu subset_union_left
  have h₂ := hD.2.2.2 _ (union_subset hC.2.1 hD.2.1) hu subset_union_right
  exact h₂.symm.trans h₁ |>.symm

/-- The components of a union of disjoint connected open sets are those sets. -/
theorem componentsIn_of_partition {Y : Set S} {F : Set (Set S)}
    (hF : ∀ a ∈ F, IsOpen a ∧ IsPreconnected a ∧ a.Nonempty)
    (hd : ∀ a ∈ F, ∀ b ∈ F, (a ∩ b).Nonempty → a = b) (hY : ⋃₀ F = Y) : componentsIn Y = F := by
  have key : ∀ a ∈ F, ∀ x ∈ a, connectedComponentIn Y x = a := by
    intro a ha x hx
    have haY : a ⊆ Y := fun y hy => hY ▸ ⟨a, ha, hy⟩
    have hxY := haY hx
    apply subset_antisymm _ ((hF a ha).2.1.subset_connectedComponentIn hx haY)
    have hrest : IsOpen (⋃₀ (F \ {a})) := isOpen_sUnion fun b hb => (hF b hb.1).1
    refine (isPreconnected_connectedComponentIn).subset_left_of_subset_union (hF a ha).1 hrest ?_ ?_
      ⟨x, mem_connectedComponentIn hxY, hx⟩
    · refine disjoint_left.mpr ?_
      rintro y hya ⟨b, hb, hyb⟩
      exact hb.2 (hd a ha b hb.1 ⟨y, hya, hyb⟩).symm
    · intro y hy
      have hy' : y ∈ Y := connectedComponentIn_subset _ _ hy
      rw [← hY] at hy'
      obtain ⟨b, hb, hyb⟩ := hy'
      by_cases hab : b = a
      · exact Or.inl (hab ▸ hyb)
      · exact Or.inr ⟨b, ⟨hb, hab⟩, hyb⟩
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hY] at hx
    obtain ⟨b, hb, hxb⟩ := hx
    rw [key b hb x hxb]
    exact hb
  · intro ha
    obtain ⟨x, hx⟩ := (hF a ha).2.2
    exact ⟨x, hY ▸ ⟨a, ha, hx⟩, key a ha x hx⟩

namespace Cell

variable (Γ : Painting S)

/-- If the regions of a painting are open, its point set is closed. -/
theorem isClosed_U (hP : ∀ r ∈ Γ.R, IsOpen r) : IsClosed Γ.U := by
  rw [← isOpen_compl_iff]
  have : Γ.Uᶜ = ⋃₀ Γ.R := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ univ \ Γ.U := ⟨trivial, hx⟩
      exact ⟨_, ⟨x, hx', rfl⟩, mem_connectedComponentIn hx'⟩
    · rintro ⟨r, ⟨y, -, rfl⟩, hx⟩
      exact (connectedComponentIn_subset _ _ hx).2
  rw [this]
  exact isOpen_sUnion hP

/-- A point of a painting is a vertex or lies in a cell. -/
theorem mem_V_or_cell {x : S} (hx : x ∈ Γ.U) : x ∈ Γ.V ∨ ∃ e ∈ Γ.E, x ∈ e := by
  by_cases hV : x ∈ Γ.V
  · exact Or.inl hV
  · exact Or.inr (exists_mem_arcComponent ⟨hx, hV⟩)

variable {Γ}

theorem isClosedDisc_closure {e : Set S} (he : e ∈ Γ.E) : IsClosedDisc (closure e) :=
  (Γ.edge_cond e he).1

theorem closure_inter_V_subset (hS : IsClosedSurface S) {e : Set S} (he : e ∈ Γ.E) :
    closure e ∩ Γ.V ⊆ discBd (closure e) := by
  have := (Γ.edge_cond e he).2
  rwa [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS (isClosedDisc_closure he)] at this

/-- In a painting with closed `U`, a cell is its closure without the vertices. -/
theorem closure_sdiff_V (hS : IsClosedSurface S) (hU : IsClosed Γ.U) {e : Set S} (he : e ∈ Γ.E) :
    closure e \ Γ.V = e := by
  have hsub : e ⊆ Γ.U \ Γ.V := he.2.1
  have hcl : closure e ⊆ Γ.U := closure_minimal (hsub.trans sdiff_subset) hU
  have hpc := isPathConnected_disc_sdiff (isClosedDisc_closure he) (A := Γ.V) (by
    rw [inter_comm]
    exact closure_inter_V_subset hS he)
  refine he.2.2.2 _ (fun x hx => ⟨hcl hx.1, hx.2⟩) hpc fun x hx => ⟨subset_closure hx, (hsub hx).2⟩

/-- In a painting with closed `U`, two cells meet only in vertices. -/
theorem closure_inter_subset_V (hS : IsClosedSurface S) (hU : IsClosed Γ.U) {e f : Set S}
    (he : e ∈ Γ.E) (hf : f ∈ Γ.E) (hef : e ≠ f) : closure e ∩ closure f ⊆ Γ.V := by
  rintro x ⟨hxe, hxf⟩
  by_contra hV
  have h₁ : x ∈ e := closure_sdiff_V hS hU he ▸ (⟨hxe, hV⟩ : x ∈ closure e \ Γ.V)
  have h₂ : x ∈ f := closure_sdiff_V hS hU hf ▸ (⟨hxf, hV⟩ : x ∈ closure f \ Γ.V)
  exact hef (arcComponent_eq he hf h₁ h₂)

end Cell

/-- A finite set of points, as a drawing with no edges. -/
def pointsDrawing [T1Space S] {A : Set S} (hA : A.Finite) : Drawing S where
  U := A
  V := A
  V_subset_U := Subset.rfl
  isClosed_U := hA.isClosed
  finite_V := hA
  finite_edges := by
    refine finite_empty.subset ?_
    rintro C ⟨⟨x, hx⟩, hsub, -⟩
    simpa using hsub hx
  edge_cond := by
    rintro C ⟨⟨x, hx⟩, hsub, -⟩
    simpa using hsub hx

variable [T2Space S]

/-- The drawing of the boundaries of the cells of a painting, with vertex set `V₀`. -/
theorem exists_boundary_drawing (hS : IsClosedSurface S) {Γ : Painting S} (hU : IsClosed Γ.U)
    {V₀ : Set S} (hfin : V₀.Finite) (hsub : Γ.V ⊆ V₀)
    (hne : ∀ e ∈ Γ.E, (V₀ ∩ discBd (closure e)).Nonempty) :
    ∃ D : Drawing S, D.U = V₀ ∪ ⋃ e ∈ Γ.E, discBd (closure e) ∧ D.V = V₀ := by
  classical
  have key : ∀ T : Finset (Set S), (∀ e ∈ T, e ∈ Γ.E) →
      ∃ D : Drawing S, D.U = V₀ ∪ ⋃ e ∈ T, discBd (closure e) ∧ D.V = V₀ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨pointsDrawing hfin, by simp [pointsDrawing], rfl⟩
    | insert e T he ih =>
      intro hT
      obtain ⟨D, hU', hV'⟩ := ih fun f hf => hT f (Finset.mem_insert_of_mem hf)
      have hee := hT e (Finset.mem_insert_self _ _)
      obtain ⟨C, hCU, hCV⟩ := exists_drawing_on_oArc
        (Cell.isClosedDisc_closure hee).isOArc_discBd (hfin.inter_of_left _)
        (hne e hee) inter_subset_right
      have hmeet : D.U ∩ C.U ⊆ D.V ∩ C.V := by
        rw [hU', hV', hCU, hCV]
        rintro x ⟨hx | hx, hxb⟩
        · exact ⟨hx, hx, hxb⟩
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
          have hfe : e ≠ f := fun h => he (h ▸ hf)
          have hxV := Cell.closure_inter_subset_V hS hU hee (hT f (Finset.mem_insert_of_mem hf))
            hfe ⟨discBd_subset _ hxb, discBd_subset _ hxf⟩
          exact ⟨hsub hxV, hsub hxV, hxb⟩
      refine ⟨D.glue C hmeet, ?_, ?_⟩
      · change D.U ∪ C.U = _
        rw [hU', hCU]
        ext x
        simp only [mem_union, mem_iUnion, Finset.mem_insert, exists_prop]
        constructor
        · rintro ((h | ⟨f, hf, h⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨f, Or.inr hf, h⟩
          · exact Or.inr ⟨e, Or.inl rfl, h⟩
        · rintro (h | ⟨f, rfl | hf, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · exact Or.inl (Or.inr ⟨f, hf, h⟩)
      · change D.V ∪ C.V = V₀
        rw [hV', hCV]
        exact union_eq_left.mpr inter_subset_left
  have hfe : Γ.E.Finite := Γ.finite_edges
  obtain ⟨D, hD, hV⟩ := key hfe.toFinset fun e he => hfe.mem_toFinset.mp he
  refine ⟨D, ?_, hV⟩
  rw [hD]
  simp only [hfe.mem_toFinset]

end GraphMinor.GM11
