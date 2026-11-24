/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingRegions

/-!
# Stars in the cells of a painting

Let `Γ` be a 2-cell painting with radial drawing `Γ'`, such that each cell has a vertex. We add a
point
`c e` inside each cell `e`, joined by a line to each vertex of `e`. The result `Γ''` is a radial
drawing
of the drawing `D` of the boundaries of the cells (`radial_of_stars`): the regions of `D` are the
regions of `Γ` and the interiors of the cells.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The interior of the cell `e`. -/
def cellInt (e : Set S) : Set S := closure e \ discBd (closure e)

/-- The centres and lines of the stars in the cells of a painting. -/
structure CellStars (Γ : Painting S) (c : Set S → S) (K : Set S → S → Set S) : Prop where
  /-- The centre is inside the cell. -/
  hub : ∀ e ∈ Γ.E, c e ∈ cellInt e
  /-- A line from the centre to a boundary point. -/
  line : ∀ e ∈ Γ.E, ∀ b ∈ discBd (closure e), IsLineWithEnds (K e b) (c e) b
  /-- Apart from its end, the line is inside the cell. -/
  sub : ∀ e ∈ Γ.E, ∀ b ∈ discBd (closure e), K e b \ {b} ⊆ cellInt e
  /-- Two lines meet only in the centre. -/
  inter : ∀ e ∈ Γ.E, ∀ b ∈ discBd (closure e), ∀ b' ∈ discBd (closure e), b ≠ b' →
    K e b ∩ K e b' = {c e}

variable [T2Space S]

/-- A closed disc has a star: a centre, and lines to its boundary points that meet only there. -/
theorem exists_disc_star {D : Set S} (hD : IsClosedDisc D) :
    ∃ (c : S) (K : S → Set S), c ∈ D \ discBd D ∧
      (∀ b ∈ discBd D, IsLineWithEnds (K b) c b) ∧ (∀ b ∈ discBd D, K b \ {b} ⊆ D \ discBd D) ∧
      ∀ b ∈ discBd D, ∀ b' ∈ discBd D, b ≠ b' → K b ∩ K b' = {c} := by
  classical
  obtain ⟨φ⟩ := id hD
  have hbd := disc_boundary D φ
  let g : ClosedUnitDisc → I → S := fun z t => (φ (scaleDisc t z)).1
  have hgc : ∀ z, Continuous (g z) := fun z =>
    continuous_subtype_val.comp (φ.continuous.comp (continuous_scaleDisc z))
  have hbdiff : ∀ z : ClosedUnitDisc, ‖z.1‖ < 1 → (φ z).1 ∉ discBd D := by
    intro z hz h
    rw [hbd] at h
    obtain ⟨w, hw, he⟩ := h
    obtain rfl : w = z := φ.injective (Subtype.ext he)
    have hw' : ‖w.1‖ = 1 := by simpa [UnitCircle] using hw
    linarith
  have hsplit : ∀ b ∈ discBd D, ∃ z : ClosedUnitDisc, ‖z.1‖ = 1 ∧ (φ z).1 = b := by
    intro b hb
    rw [hbd] at hb
    obtain ⟨z, hz, rfl⟩ := hb
    exact ⟨z, by simpa [UnitCircle] using hz, rfl⟩
  have : Nonempty ClosedUnitDisc := ⟨discCentre⟩
  choose! z hz1 hzb using hsplit
  let c : S := (φ discCentre).1
  have hg1 : ∀ w, g w 1 = (φ w).1 := fun w => by simp only [g, scaleDisc_one]
  have hg0 : ∀ w, g w 0 = c := fun w => by simp only [g, c, scaleDisc_zero_eq]
  have hnorm : ∀ b ∈ discBd D, ∀ t : I, ‖(scaleDisc t (z b)).1‖ = t := fun b hb t => by
    rw [norm_scaleDisc, hz1 b hb, mul_one]
  have hinj : ∀ b ∈ discBd D, Function.Injective (g (z b)) := by
    intro b hb s t h
    have h' := φ.injective (Subtype.ext h)
    have := congrArg (fun w : ClosedUnitDisc => ‖w.1‖) h'
    simp only [hnorm b hb] at this
    exact Subtype.ext this
  refine ⟨c, fun b => range (g (z b)), ⟨(φ _).2, hbdiff _ (by simp [discCentre])⟩, ?_, ?_, ?_⟩
  · intro b hb
    have := isLine_range (hgc (z b)) (hinj b hb)
    rwa [hg0, hg1, hzb b hb] at this
  · rintro b hb _ ⟨⟨t, rfl⟩, hn⟩
    refine ⟨(φ _).2, hbdiff _ ?_⟩
    rw [hnorm b hb]
    refine lt_of_le_of_ne t.2.2 fun h => hn ?_
    have ht : t = 1 := Subtype.ext h
    rw [ht, hg1, hzb b hb]
    rfl
  · intro b hb b' hb' hne
    apply subset_antisymm
    · rintro _ ⟨⟨t, rfl⟩, ⟨t', ht'⟩⟩
      have h' := φ.injective (Subtype.ext ht')
      have hn := congrArg (fun w : ClosedUnitDisc => ‖w.1‖) h'
      simp only [hnorm b hb, hnorm b' hb'] at hn
      have htt : t' = t := Subtype.ext hn
      subst htt
      by_cases h0 : t' = 0
      · rw [h0, hg0]
        rfl
      · exfalso
        have hpos : (t' : ℝ) ≠ 0 := fun h => h0 (Subtype.ext h)
        have hv := congrArg (fun w : ClosedUnitDisc => w.1) h'
        have hzz : (z b').1 = (z b).1 := smul_right_injective _ hpos hv
        exact hne (by rw [← hzb b hb, ← hzb b' hb', Subtype.ext hzz])
    · rintro _ rfl
      exact ⟨⟨0, hg0 _⟩, ⟨0, hg0 _⟩⟩

theorem exists_cellStars [Nonempty S] {Γ : Painting S} :
    ∃ (c : Set S → S) (K : Set S → S → Set S), CellStars Γ c K := by
  classical
  have h : ∀ e ∈ Γ.E, ∃ (c : S) (K : S → Set S), c ∈ cellInt e ∧
      (∀ b ∈ discBd (closure e), IsLineWithEnds (K b) c b) ∧
      (∀ b ∈ discBd (closure e), K b \ {b} ⊆ cellInt e) ∧
      ∀ b ∈ discBd (closure e), ∀ b' ∈ discBd (closure e), b ≠ b' → K b ∩ K b' = {c} :=
    fun e he => exists_disc_star (Cell.isClosedDisc_closure he)
  choose! c K h₁ h₂ h₃ h₄ using h
  exact ⟨c, K, h₁, h₂, h₃, h₄⟩

/-- The pairs of a cell and a vertex of it. -/
def cellPairs (Γ : Painting S) : Set (Set S × S) := {t | t.1 ∈ Γ.E ∧ t.2 ∈ Γ.V ∧ t.2 ∈ closure t.1}

omit [T2Space S] in
theorem finite_cellPairs (Γ : Painting S) : (cellPairs Γ).Finite := by
  have hfe : Γ.E.Finite := Γ.finite_edges
  exact (hfe.prod Γ.finite_V).subset fun t ht => ⟨ht.1, ht.2.1⟩

variable {Γ : Painting S} {Γ' : Drawing S} {c : Set S → S} {K : Set S → S → Set S}

/-- The drawing `Γ'` with the stars of the cells. -/
structure IsStarDrawing (Γ : Painting S) (Γ' : Drawing S) (c : Set S → S) (K : Set S → S → Set S)
    (G : Drawing S) : Prop where
  /-- The point set. -/
  U : G.U = Γ'.U ∪ ⋃ t ∈ cellPairs Γ, K t.1 t.2
  /-- The vertices. -/
  V : G.V = Γ'.V ∪ (fun t : Set S × S => c t.1) '' cellPairs Γ
  /-- The edges. -/
  E : G.E = Γ'.E ∪ (fun t : Set S × S => K t.1 t.2 \ {c t.1, t.2}) '' cellPairs Γ

section

variable (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') (hst : CellStars Γ c K)
  (hS : IsClosedSurface S)

omit [T2Space S] in
theorem cell_isClosed_U (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') :
    IsClosed Γ.U :=
  Cell.isClosed_U Γ fun r hr => (hrad.1.2 r hr).1

omit [T2Space S] in
theorem closure_subset_cell_U (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') {e : Set S}
    (he : e ∈ Γ.E) : closure e ⊆ Γ.U :=
  closure_minimal (he.2.1.trans sdiff_subset) (cell_isClosed_U hrad)

omit [T2Space S] in
theorem cellInt_subset_U (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ') {e : Set S}
    (he : e ∈ Γ.E) : cellInt e ⊆ Γ.U :=
  sdiff_subset.trans (closure_subset_cell_U hrad he)

omit [T2Space S] in
theorem cellInt_disjoint_V (hS : IsClosedSurface S) {e : Set S} (he : e ∈ Γ.E) :
    Disjoint (cellInt e) Γ.V :=
  disjoint_left.mpr fun _ hx hxV => hx.2 (Cell.closure_inter_V_subset hS he ⟨hx.1, hxV⟩)

omit [T2Space S] in
theorem cellInt_disjoint (hrad : PreRad (PaintingOrDrawing.painting Γ) Γ')
    (hS : IsClosedSurface S) {e f : Set S} (he : e ∈ Γ.E) (hf : f ∈ Γ.E) (hef : e ≠ f) :
    Disjoint (cellInt e) (closure f) :=
  disjoint_left.mpr fun _ hx hxf => disjoint_left.mp (cellInt_disjoint_V hS he) hx
    (Cell.closure_inter_subset_V hS (cell_isClosed_U hrad) he hf hef ⟨hx.1, hxf⟩)

include hst in
omit [T2Space S] in
theorem star_subset_closure {e : Set S} (he : e ∈ Γ.E) {b : S} (hb : b ∈ discBd (closure e)) :
    K e b ⊆ closure e := fun x hx => by
  by_cases hxb : x = b
  · exact hxb ▸ discBd_subset _ hb
  · exact (hst.sub e he b hb ⟨hx, hxb⟩).1

include hst hS

omit [T2Space S] in
theorem hub_notMem_V {e : Set S} (he : e ∈ Γ.E) : c e ∉ Γ.V :=
  disjoint_left.mp (cellInt_disjoint_V hS he) (hst.hub e he)

include hrad

omit [T2Space S] in
/-- A point of a line of a star that lies in `Γ'` is the vertex at the end of the line. -/
theorem star_inter_U {t : Set S × S} (ht : t ∈ cellPairs Γ) {x : S} (hx : x ∈ K t.1 t.2)
    (hx' : x ∈ Γ'.U) : x = t.2 := by
  have hb := Cell.closure_inter_V_subset hS ht.1 ⟨ht.2.2, ht.2.1⟩
  have hxU : x ∈ Γ.U := closure_subset_cell_U hrad ht.1 (star_subset_closure hst ht.1 hb hx)
  have hxV : x ∈ Γ.V := (show Γ.U ∩ Γ'.U = Γ.V from hrad.2.1) ▸ ⟨hxU, hx'⟩
  by_contra hne
  exact disjoint_left.mp (cellInt_disjoint_V hS ht.1) (hst.sub _ ht.1 _ hb ⟨hx, hne⟩) hxV

/-- `Γ'` together with the stars is a drawing. -/
theorem exists_star_drawing : ∃ G : Drawing S, IsStarDrawing Γ Γ' c K G := by
  classical
  have key : ∀ F : Finset (Set S × S), (∀ t ∈ F, t ∈ cellPairs Γ) → ∃ G : Drawing S,
      G.U = Γ'.U ∪ (⋃ t ∈ F, K t.1 t.2) ∧
      G.V = Γ'.V ∪ (fun t : Set S × S => c t.1) '' F ∧
      G.E = Γ'.E ∪ (fun t : Set S × S => K t.1 t.2 \ {c t.1, t.2}) '' F := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨Γ', by simp, by simp, by simp⟩
    | insert t F htF ih =>
      intro hF
      obtain ⟨G, hU, hV, hE⟩ := ih fun u hu => hF u (Finset.mem_insert_of_mem hu)
      have ht := hF t (Finset.mem_insert_self _ _)
      obtain ⟨e, b⟩ := t
      have he : e ∈ Γ.E := ht.1
      have hbV : b ∈ Γ.V := ht.2.1
      have hb : b ∈ discBd (closure e) := Cell.closure_inter_V_subset hS he ⟨ht.2.2, hbV⟩
      have hL := hst.line e he b hb
      have hcb : c e ≠ b := fun h => hub_notMem_V hst hS he (h ▸ hbV)
      have hbG : b ∈ G.V := hV ▸ Or.inl (hrad.2.2.1 hbV)
      have hmeet : G.U ∩ (lineDrawing hL hcb).U ⊆ G.V ∩ (lineDrawing hL hcb).V := by
        rintro x ⟨hxG, hxL⟩
        have hxL' : x ∈ K e b := hxL
        by_cases hxb : x = b
        · subst hxb
          exact ⟨hbG, Or.inr rfl⟩
        have hxint := hst.sub e he b hb ⟨hxL', hxb⟩
        rw [hU] at hxG
        rcases hxG with hx' | hx'
        · exact (hxb (star_inter_U hrad hst hS ht hxL' hx')).elim
        · obtain ⟨⟨e', b'⟩, ht', hx''⟩ := mem_iUnion₂.mp hx'
          have ht'P := hF _ (Finset.mem_insert_of_mem ht')
          have he' : e' ∈ Γ.E := ht'P.1
          have hb' : b' ∈ discBd (closure e') :=
            Cell.closure_inter_V_subset hS he' ⟨ht'P.2.2, ht'P.2.1⟩
          have hxK : x ∈ K e' b' := hx''
          by_cases hee : e = e'
          · subst hee
            have hbb : b ≠ b' := fun h => htF (by rw [h]; exact ht')
            have : x ∈ K e b ∩ K e b' := ⟨hxL', hxK⟩
            rw [hst.inter e he b hb b' hb' hbb] at this
            have hxc : x = c e := this
            refine ⟨?_, Or.inl hxc⟩
            rw [hV, hxc]
            exact Or.inr ⟨(e, b'), ht', rfl⟩
          · exact (disjoint_left.mp (cellInt_disjoint hrad hS he he' hee) hxint
              (star_subset_closure hst he' hb' hxK)).elim
      refine ⟨G.glue (lineDrawing hL hcb) hmeet, ?_, ?_, ?_⟩
      · change G.U ∪ K e b = _
        rw [hU, Finset.set_biUnion_insert, union_assoc, union_comm (⋃ t ∈ F, K t.1 t.2) (K e b)]
      · change G.V ∪ {c e, b} = _
        rw [hV, Finset.coe_insert, image_insert_eq]
        ext x
        simp only [mem_union, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ((h | h) | (h | h))
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl (h ▸ hrad.2.2.1 hbV)
        · rintro (h | h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inr h)
      · rw [Drawing.glue_E, lineDrawing_E, hE, Finset.coe_insert, image_insert_eq, union_assoc]
        congr 1
        rw [union_comm, ← insert_eq]
  have hfin := finite_cellPairs Γ
  obtain ⟨G, hU, hV, hE⟩ := key hfin.toFinset fun t ht => hfin.mem_toFinset.mp ht
  refine ⟨G, ⟨?_, ?_, ?_⟩⟩
  · rw [hU]
    simp only [hfin.mem_toFinset]
  · rw [hV, hfin.coe_toFinset]
  · rw [hE, hfin.coe_toFinset]

end

end GraphMinor.GM11
