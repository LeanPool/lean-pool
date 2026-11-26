/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidGood
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.GM11.SplitEdge
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.Surface.Lunes
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# The wheel around a closed disc

`exists_wheel` builds the wheel of `RigidGood` in a closed disc `D₂`. Its rim is the boundary of
`D₂`,
with the given finite set `B` among its vertices. We put a new vertex in each edge of the rim, so no
rim edge joins two vertices of `B`. The hub is the centre of `D₂`, and a spoke goes to each rim
vertex.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph Metric GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- A line in `ℂ` has a line as its image under a map that is continuous and injective on it. -/
theorem line_image {Z : Set ℂ} {a b : ℂ} (hl : IsLineWithEnds Z a b) {g : ℂ → S}
    (hc : ContinuousOn g Z) (hi : InjOn g Z) : IsLineWithEnds (g '' Z) (g a) (g b) :=
  hl.image_under_injOn hc hi

omit [T2Space S] in
theorem line_start {L : Set S} {u v : S} (h : IsLineWithEnds L u v) : u ∈ L := by
  obtain ⟨f, h0, -⟩ := h
  exact h0 ▸ (f 0).2

omit [T2Space S] in
theorem line_end {L : Set S} {u v : S} (h : IsLineWithEnds L u v) : v ∈ L := by
  obtain ⟨f, -, h1⟩ := h
  exact h1 ▸ (f 1).2

omit [T2Space S] in
theorem line_preconn {L : Set S} {u v : S} (h : IsLineWithEnds L u v) : IsPreconnected L := by
  obtain ⟨f, -, -⟩ := h
  have hr : range (fun c : unitInterval => (f c).1) = L := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact (f c).2
    · intro hz
      exact ⟨f.symm ⟨z, hz⟩, by simp⟩
  rw [← hr]
  exact isPreconnected_range (continuous_subtype_val.comp f.continuous)

omit [T2Space S] in
/-- An O-arc is preconnected. -/
theorem isPreconnected_of_oArc {F : Set S} (hF : IsOArc F) : IsPreconnected F := by
  obtain ⟨f⟩ := hF
  have hr : range (fun c : Circle => (f c).1) = F := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact (f c).2
    · intro hz
      exact ⟨f.symm ⟨z, hz⟩, by simp⟩
  rw [← hr]
  exact isPreconnected_range (continuous_subtype_val.comp f.continuous)

/-- Lines from `a` that meet only in `a` form a drawing. -/
theorem exists_star {a : S} {L : S → Set S} {R : Set S} (hR : R.Finite) :
    (∀ z ∈ R, z ≠ a ∧ IsLineWithEnds (L z) a z) → (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → L z ∩ L z' ⊆ {a}) →
    ∃ St : Drawing S, St.U = insert a (⋃ z ∈ R, L z) ∧ St.V = insert a R ∧
      St.E = (fun z => L z \ {a, z}) '' R := by
  induction R, hR using Set.Finite.induction_on with
  | empty =>
    intro _ _
    refine ⟨pointsDrawing (finite_singleton a), by simp [pointsDrawing], by simp [pointsDrawing],
      ?_⟩
    rw [pointsDrawing_E]
    simp
  | @insert z R hz hfin ih =>
    intro h₁ h₂
    obtain ⟨St, hU, hV, hE⟩ := ih (fun w hw => h₁ w (mem_insert_of_mem _ hw))
      (fun w hw w' hw' hne => h₂ w (mem_insert_of_mem _ hw) w' (mem_insert_of_mem _ hw') hne)
    obtain ⟨hne, hl⟩ := h₁ z (mem_insert _ _)
    have hc : St.U ∩ (lineDrawing hl hne.symm).U ⊆ St.V ∩ (lineDrawing hl hne.symm).V := by
      rintro p ⟨hp, hpL⟩
      have hpL' : p ∈ L z := hpL
      have hpa : p = a := by
        rw [hU] at hp
        rcases hp with hp | hp
        · exact hp
        · obtain ⟨w, hw, hpw⟩ := mem_iUnion₂.mp hp
          have hne' : w ≠ z := fun h' => hz (h' ▸ hw)
          exact h₂ w (mem_insert_of_mem _ hw) z (mem_insert _ _) hne' ⟨hpw, hpL'⟩
      subst hpa
      exact ⟨hV ▸ mem_insert _ _, Or.inl rfl⟩
    refine ⟨St.glue (lineDrawing hl hne.symm) hc, ?_, ?_, ?_⟩
    · change St.U ∪ L z = _
      rw [hU]
      ext p
      simp only [mem_union, mem_insert_iff, mem_iUnion, exists_prop]
      constructor
      · rintro ((h' | ⟨w, hw, hp⟩) | h')
        · exact Or.inl h'
        · exact Or.inr ⟨w, Or.inr hw, hp⟩
        · exact Or.inr ⟨z, Or.inl rfl, h'⟩
      · rintro (h' | ⟨w, rfl | hw, hp⟩)
        · exact Or.inl (Or.inl h')
        · exact Or.inr hp
        · exact Or.inl (Or.inr ⟨w, hw, hp⟩)
    · change St.V ∪ {a, z} = _
      rw [hV]
      ext p
      simp only [mem_union, mem_insert_iff, mem_singleton_iff]
      tauto
    · rw [Drawing.glue_E, hE, lineDrawing_E, image_insert_eq, union_comm, singleton_union]

/-- Spokes in a closed disc. -/
theorem exists_spokes {D : Set S} (hD : IsClosedDisc D) {R : Set S} (hR : R ⊆ discBd D) :
    ∃ (a : S) (L : S → Set S), a ∈ D ∧ a ∉ discBd D ∧
      (∀ z ∈ R, z ≠ a ∧ IsLineWithEnds (L z) a z ∧ L z ⊆ D ∧ L z ∩ discBd D = {z}) ∧
      ∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → L z ∩ L z' ⊆ {a} := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hsph : ∀ {z}, z ∈ discBd D → h z ∈ sphere (0 : ℂ) 1 := fun hz => c.bd ▸ mem_image_of_mem h hz
  have hzD : ∀ {z}, z ∈ discBd D → z ∈ D := fun hz => Surface.discBd_subset D hz
  have hgh : ∀ {z}, z ∈ discBd D → g (h z) = z := fun hz => c.gh (hzD hz)
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  have hseg : ∀ {w : ℂ}, w ∈ sphere (0 : ℂ) 1 → segment ℝ 0 w ⊆ closedBall (0 : ℂ) 1 := fun hw =>
    (convex_closedBall _ _).segment_subset h0 (sphere_subset_closedBall hw)
  have hne0 : ∀ {w : ℂ}, w ∈ sphere (0 : ℂ) 1 → (0 : ℂ) ≠ w := fun hw h' => by
    rw [← h'] at hw
    simp at hw
  have hnorm : ∀ {w p : ℂ}, w ∈ sphere (0 : ℂ) 1 → p ∈ segment ℝ 0 w →
      ∃ t : ℝ, 0 ≤ t ∧ p = (t : ℂ) * w ∧ ‖p‖ = t := by
    rintro w p hw ⟨c₁, t, -, ht, -, rfl⟩
    have hw1 : ‖w‖ = 1 := by simpa using hw
    refine ⟨t, ht, by simp, ?_⟩
    simp [hw1, abs_of_nonneg ht]
  refine ⟨g 0, fun z => g '' segment ℝ 0 (h z), c.gm h0, ?_, ?_, ?_⟩
  · intro h'
    have h₁ := hsph h'
    rw [c.hg h0] at h₁
    simp at h₁
  · intro z hz
    have hzb := hR hz
    have hw := hsph hzb
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h'
      have h₁ := hsph hzb
      rw [h', c.hg h0] at h₁
      simp at h₁
    · have := line_image (isLineWithEnds_segment (hne0 hw)) (c.gc.mono (hseg hw))
        (c.hg.injOn.mono (hseg hw))
      rwa [hgh hzb] at this
    · exact image_subset_iff.mpr fun p hp => c.gm (hseg hw hp)
    · ext x
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hxb⟩
        have h₁ := hsph hxb
        rw [c.hg (hseg hw hp)] at h₁
        obtain ⟨t, -, hpt, hn⟩ := hnorm hw hp
        have ht : t = 1 := by
          rw [← hn]
          simpa using h₁
        rw [hpt, ht]
        simp [hgh hzb]
      · rintro rfl
        refine ⟨⟨h x, right_mem_segment ℝ _ _, hgh hzb⟩, hzb⟩
  · rintro z hz z' hz' hne x ⟨⟨p, hp, rfl⟩, ⟨p', hp', heq⟩⟩
    have hw := hsph (hR hz)
    have hw' := hsph (hR hz')
    have hpp : p' = p := by
      have := congrArg h heq
      rwa [c.hg (hseg hw' hp'), c.hg (hseg hw hp)] at this
    subst hpp
    obtain ⟨t, -, hpt, hn⟩ := hnorm hw hp
    obtain ⟨t', -, hpt', hn'⟩ := hnorm hw' hp'
    have htt : t = t' := hn.symm.trans hn'
    subst htt
    by_cases h0t : t = 0
    · rw [hpt, h0t]
      simp
    · exfalso
      have heqw : h z = h z' := by
        have h₁ : (t : ℂ) ≠ 0 := by exact_mod_cast h0t
        exact mul_left_cancel₀ h₁ (hpt.symm.trans hpt')
      apply hne
      rw [← hgh (hR hz), ← hgh (hR hz'), heqw]

/-- One round of splitting edges. -/
theorem exists_split_step [Nonempty S] (D : Drawing S) :
    ∃ (D' : Drawing S) (T : Set S), D'.U = D.U ∧ D.V ⊆ D'.V ∧
      (∀ g u, ¬ D'.toGraph.IsLink g u u) ∧
      (∀ g u v, D'.toGraph.IsLink g u v → u ∈ D.V → v ∉ D.V) ∧
      ((∀ g u, ¬ D.toGraph.IsLink g u u) →
        ∀ g g' u v, D'.toGraph.IsLink g u v → D'.toGraph.IsLink g' u v → g = g') ∧
      2 * D.E.ncard ≤ D'.E.ncard ∧ T.ncard = D.E.ncard ∧ T ⊆ D'.V ∧
      ∀ t ∈ T, ∃ g g', g ≠ g' ∧ D'.toGraph.Inc g t ∧ D'.toGraph.Inc g' t := by
  classical
  obtain ⟨D', A, B, m, x, y, hU, hV, hf, hall⟩ := exists_split D
  have hmV : ∀ e ∈ D.E, m e ∉ D.V := fun e he => edge_notMem_V he (hf e he).2.2.1
  have hsubV : D.V ⊆ D'.V := hV ▸ subset_union_left
  have hmV' : ∀ e ∈ D.E, m e ∈ D'.V := fun e he => hV ▸ Or.inr (mem_image_of_mem m he)
  have hAe : ∀ e ∈ D.E, A e ⊆ e := fun e he z hz => by
    rw [(hf e he).2.2.2.2.2.2.1]
    exact Or.inl (Or.inl hz)
  have hBe : ∀ e ∈ D.E, B e ⊆ e := fun e he z hz => by
    rw [(hf e he).2.2.2.2.2.2.1]
    exact Or.inr hz
  have hshape : ∀ g ∈ D'.E, ∃ e ∈ D.E, ∃ p ∈ D.V, closure g ∩ D'.V = {p, m e} ∧
      ((g = A e ∧ p = x e) ∨ (g = B e ∧ p = y e)) := by
    intro g hg
    obtain ⟨e, he, rfl | rfl⟩ := hall g hg
    · have := hf e he
      exact ⟨e, he, x e, this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.1, Or.inl ⟨rfl, rfl⟩⟩
    · have := hf e he
      refine ⟨e, he, y e, this.2.2.2.2.2.2.2.2.1, ?_, Or.inr ⟨rfl, rfl⟩⟩
      rw [this.2.2.2.2.2.2.2.2.2.2.2, pair_comm]
  have hminj : ∀ e ∈ D.E, ∀ e' ∈ D.E, m e = m e' → e = e' := fun e he e' he' h =>
    D.edge_eq_of_mem he he' (hf e he).2.2.1 (h ▸ (hf e' he').2.2.1)
  have hAinj : InjOn A D.E := fun e he e' he' h => by
    obtain ⟨z, hz⟩ := (hf e he).1.1
    exact D.edge_eq_of_mem he he' (hAe e he hz) (hAe e' he' (h ▸ hz))
  have hBinj : InjOn B D.E := fun e he e' he' h => by
    obtain ⟨z, hz⟩ := (hf e he).2.1.1
    exact D.edge_eq_of_mem he he' (hBe e he hz) (hBe e' he' (h ▸ hz))
  have hABne : ∀ e ∈ D.E, A e ≠ B e := fun e he h => by
    obtain ⟨z, hz⟩ := (hf e he).1.1
    exact disjoint_left.mp (hf e he).2.2.2.2.2.1 hz (h ▸ hz)
  have hAB : Disjoint (A '' D.E) (B '' D.E) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨e, he, rfl⟩ ⟨e', he', h⟩
    obtain ⟨z, hz⟩ := (hf e he).1.1
    have heq : e = e' := D.edge_eq_of_mem he he' (hAe e he hz) (hBe e' he' (h ▸ hz))
    subst heq
    exact hABne e he h.symm
  refine ⟨D', m '' D.E, hU, hsubV, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g u hl
    obtain ⟨e, he, p, hp, heq, -⟩ := hshape g hl.1
    have hc := hl.2.2.2
    rw [heq] at hc
    have h₁ : p ∈ ({u, u} : Set S) := hc ▸ Or.inl rfl
    have h₂ : m e ∈ ({u, u} : Set S) := hc ▸ Or.inr rfl
    simp only [pair_eq_singleton, mem_singleton_iff] at h₁ h₂
    exact hmV e he (h₂.trans h₁.symm ▸ hp)
  · intro g u v hl hu
    obtain ⟨e, he, p, hp, heq, -⟩ := hshape g hl.1
    have hc := hl.2.2.2
    rw [heq] at hc
    have h₂ : m e ∈ ({u, v} : Set S) := hc ▸ Or.inr rfl
    rcases h₂ with h₂ | h₂
    · exact absurd (h₂ ▸ hu) (hmV e he)
    · exact h₂ ▸ hmV e he
  · intro hnl g g' u v hl hl'
    obtain ⟨e, he, p, hp, heq, hc₁⟩ := hshape g hl.1
    obtain ⟨e', he', p', hp', heq', hc₂⟩ := hshape g' hl'.1
    have hc : ({p, m e} : Set S) = {p', m e'} := by
      rw [← heq, ← heq', hl.2.2.2, hl'.2.2.2]
    have hme : m e = m e' := by
      have : m e ∈ ({p', m e'} : Set S) := hc ▸ Or.inr rfl
      rcases this with h₁ | h₁
      · exact absurd (h₁ ▸ hp') (hmV e he)
      · exact h₁
    have hee : e = e' := hminj e he e' he' hme
    subst hee
    have hpp : p = p' := by
      have : p ∈ ({p', m e} : Set S) := hc ▸ Or.inl rfl
      rcases this with h₁ | h₁
      · exact h₁
      · exact absurd (h₁ ▸ hp) (hmV e he)
    have hno : x e ≠ y e := by
      intro hxy
      have h₁ := hf e he
      refine hnl e (x e) ⟨he, h₁.2.2.2.2.2.2.2.1, h₁.2.2.2.2.2.2.2.1, ?_⟩
      rw [h₁.2.2.2.2.2.2.2.2.2.1, ← hxy]
    rcases hc₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hpp hno
    · exact absurd hpp.symm hno
    · rfl
  · have h₁ : (A '' D.E ∪ B '' D.E).ncard = D.E.ncard + D.E.ncard := by
      rw [ncard_union_eq hAB (D.finite_edges.image _) (D.finite_edges.image _),
        hAinj.ncard_image, hBinj.ncard_image]
    have h₂ : A '' D.E ∪ B '' D.E ⊆ D'.E := by
      rintro _ (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
      · exact (hf e he).1
      · exact (hf e he).2.1
    have := ncard_le_ncard h₂ D'.finite_edges
    omega
  · exact InjOn.ncard_image fun e he e' he' h => hminj e he e' he' h
  · exact hV ▸ subset_union_right
  · rintro _ ⟨e, he, rfl⟩
    have h₁ := hf e he
    refine ⟨A e, B e, hABne e he, ⟨x e, h₁.1, hmV' e he, hsubV h₁.2.2.2.2.2.2.2.1, ?_⟩,
      ⟨y e, h₁.2.1, hmV' e he, hsubV h₁.2.2.2.2.2.2.2.2.1, h₁.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    rw [h₁.2.2.2.2.2.2.2.2.2.2.1, pair_comm]

/-- Three rounds of splitting. The rim has no loops and no parallel edges, no edge joins two old
vertices, and at least four vertices meet two edges. -/
theorem exists_rim (D : Drawing S) (hne : D.E.Nonempty) :
    ∃ (Rim : Drawing S) (T : Set S), Rim.U = D.U ∧ D.V ⊆ Rim.V ∧
      (∀ g u, ¬ Rim.toGraph.IsLink g u u) ∧
      (∀ g u v, Rim.toGraph.IsLink g u v → u ∈ D.V → v ∉ D.V) ∧
      (∀ g g' u v, Rim.toGraph.IsLink g u v → Rim.toGraph.IsLink g' u v → g = g') ∧
      4 ≤ T.ncard ∧ T ⊆ Rim.V ∧
      ∀ t ∈ T, ∃ g g', g ≠ g' ∧ Rim.toGraph.Inc g t ∧ Rim.toGraph.Inc g' t := by
  obtain ⟨e, he⟩ := hne
  obtain ⟨z, -⟩ := he.1
  have : Nonempty S := ⟨z⟩
  obtain ⟨D₁, -, hU₁, hV₁, -, -, -, hc₁, -⟩ := exists_split_step D
  obtain ⟨D₂, -, hU₂, hV₂, hl₂, -, -, hc₂, -⟩ := exists_split_step D₁
  obtain ⟨D₃, T, hU₃, hV₃, hl₃, hn₃, hs₃, -, hT, hTV, hT2⟩ := exists_split_step D₂
  have hc₀ : 1 ≤ D.E.ncard := Nat.one_le_iff_ne_zero.mpr
    ((ncard_ne_zero_of_mem he D.finite_edges))
  refine ⟨D₃, T, by rw [hU₃, hU₂, hU₁], hV₁.trans (hV₂.trans hV₃), hl₃, ?_, hs₃ hl₂, by omega,
    hTV, hT2⟩
  exact fun g u v hl hu hv => hn₃ g u v hl (hV₂ (hV₁ hu)) (hV₂ (hV₁ hv))

section Glue

variable {Γ₁ Γ₂ : Drawing S}

omit [T2Space S] in
theorem cap_glue_left (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) {e : Set S} (he : e ∈ Γ₁.E) :
    closure e ∩ (Γ₁.V ∪ Γ₂.V) = closure e ∩ Γ₁.V := by
  refine subset_antisymm ?_ fun z hz => ⟨hz.1, Or.inl hz.2⟩
  rintro z ⟨hz, h₁ | h₁⟩
  · exact ⟨hz, h₁⟩
  · exact ⟨hz, (h ⟨Γ₁.closure_subset_U he hz, Γ₂.V_subset_U h₁⟩).1⟩

omit [T2Space S] in
theorem cap_glue_right (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) {e : Set S} (he : e ∈ Γ₂.E) :
    closure e ∩ (Γ₁.V ∪ Γ₂.V) = closure e ∩ Γ₂.V := by
  refine subset_antisymm ?_ fun z hz => ⟨hz.1, Or.inr hz.2⟩
  rintro z ⟨hz, h₁ | h₁⟩
  · exact ⟨hz, (h ⟨Γ₁.V_subset_U h₁, Γ₂.closure_subset_U he hz⟩).2⟩
  · exact ⟨hz, h₁⟩

omit [T2Space S] in
/-- The links of a union of two drawings are those of the parts. -/
theorem isUnion_glue (h : Γ₁.U ∩ Γ₂.U ⊆ Γ₁.V ∩ Γ₂.V) : IsUnion Γ₁ Γ₂ (Γ₁.glue Γ₂ h) := by
  refine ⟨rfl, Drawing.glue_E h, fun e he u v => ?_, fun e he u v => ?_⟩
  · constructor
    · rintro ⟨-, -, -, hc⟩
      have hc' : closure e ∩ Γ₁.V = {u, v} := (cap_glue_left h he).symm.trans hc
      have hu : u ∈ closure e ∩ Γ₁.V := hc' ▸ Or.inl rfl
      have hv : v ∈ closure e ∩ Γ₁.V := hc' ▸ Or.inr rfl
      exact ⟨he, hu.2, hv.2, hc'⟩
    · rintro ⟨-, hu, hv, hc⟩
      exact ⟨(Drawing.glue_E h).symm ▸ Or.inl he, Or.inl hu, Or.inl hv,
        (cap_glue_left h he).trans hc⟩
  · constructor
    · rintro ⟨-, -, -, hc⟩
      have hc' : closure e ∩ Γ₂.V = {u, v} := (cap_glue_right h he).symm.trans hc
      have hu : u ∈ closure e ∩ Γ₂.V := hc' ▸ Or.inl rfl
      have hv : v ∈ closure e ∩ Γ₂.V := hc' ▸ Or.inr rfl
      exact ⟨he, hu.2, hv.2, hc'⟩
    · rintro ⟨-, hu, hv, hc⟩
      exact ⟨(Drawing.glue_E h).symm ▸ Or.inr he, Or.inr hu, Or.inr hv,
        (cap_glue_right h he).trans hc⟩

end Glue

omit [T2Space S] in
/-- A preconnected set covered by two closed sets that it does not meet together lies in one. -/
theorem preconn_side {P U₁ U₂ : Set S} (hP : IsPreconnected P) (h₁ : IsClosed U₁) (h₂ : IsClosed U₂)
    (hc : P ⊆ U₁ ∪ U₂) (hd : ∀ z ∈ P, z ∈ U₁ → z ∈ U₂ → False) : P ⊆ U₁ ∨ P ⊆ U₂ := by
  by_contra hn
  push Not at hn
  obtain ⟨hn₁, hn₂⟩ := hn
  obtain ⟨x, hx, hx₁⟩ := not_subset.mp hn₁
  obtain ⟨y, hy, hy₂⟩ := not_subset.mp hn₂
  have hx₂ : x ∈ U₂ := (hc hx).resolve_left hx₁
  have hy₁ : y ∈ U₁ := (hc hy).resolve_right hy₂
  obtain ⟨z, hz, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hP U₁ U₂ h₁ h₂ hc ⟨y, hy, hy₁⟩ ⟨x, hx,
    hx₂⟩
  exact hd z hz hz₁ hz₂

private theorem spokes_meet_wheel_vertices_at_ends
    {S : Type u}
    [TopologicalSpace S]
    {D₂ : Set S}
    (Rim : Drawing S)
    (hVC : Rim.V ⊆ discBd D₂)
    (a : S)
    (L : S → Set S)
    (haD : a ∈ D₂)
    (hab : a ∉ discBd D₂)
    (hL : ∀ z ∈ Rim.V, z ≠ a ∧ IsLineWithEnds (L z) a z ∧ L z ⊆ D₂ ∧ L z ∩ discBd D₂ = {z})
    (hdis : ∀ z ∈ Rim.V, ∀ z' ∈ Rim.V, z ≠ z' → L z ∩ L z' ⊆ {a})
    (St : Drawing S)
    (hSU : St.U = insert a (⋃ z ∈ Rim.V, L z))
    (hSV : St.V = insert a Rim.V)
    (hSE : St.E = (fun z => L z \ {a, z}) '' Rim.V)
    (W : Drawing S)
    (hWU : W.U = discBd D₂ ∪ insert a (⋃ z ∈ Rim.V, L z))
    (hWV : W.V = insert a Rim.V)
    (haW : a ∈ W.V) :
    ∀ z ∈ Rim.V, L z ∩ W.V = {a, z} := by
  intro z hz
  obtain ⟨hne, hl, -, hm⟩ := hL z hz
  apply subset_antisymm
  · rintro p ⟨hp, hpV⟩
    rw [hWV] at hpV
    rcases hpV with h₁ | h₁
    · exact Or.inl h₁
    · have h₂ : p ∈ L z ∩ discBd D₂ := ⟨hp, hVC h₁⟩
      rw [hm] at h₂
      exact Or.inr h₂
  · rintro p (rfl | rfl)
    · exact ⟨line_start hl, haW⟩
    · exact ⟨line_end hl, hWV ▸ Or.inr hz⟩

private theorem star_edges_link_spoke_endpoints
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {D₂ : Set S}
    (Rim : Drawing S)
    (a : S)
    (L : S → Set S)
    (hL : ∀ z ∈ Rim.V, z ≠ a ∧ IsLineWithEnds (L z) a z ∧ L z ⊆ D₂ ∧ L z ∩ discBd D₂ = {z})
    (St : Drawing S)
    (hSE : St.E = (fun z => L z \ {a, z}) '' Rim.V)
    (W : Drawing S)
    (hcap : ∀ z ∈ Rim.V, L z ∩ W.V = {a, z}) :
    ∀ {g : Set S} {u v : S}, g ∈ St.E → W.toGraph.IsLink g u v →
      ∃ z ∈ Rim.V, z ≠ a ∧ ({u, v} : Set S) = {a, z} := by
  intro g u v hg hl
  rw [hSE] at hg
  obtain ⟨z, hz, rfl⟩ := hg
  obtain ⟨hne, hl', -, -⟩ := hL z hz
  refine ⟨z, hz, hne, ?_⟩
  have := hl.2.2.2
  rw [closure_sdiff_pair hl'] at this
  rw [← this]
  exact hcap z hz

private theorem wheel_has_no_small_separation
    {S : Type u}
    [TopologicalSpace S]
    {B : Set S}
    {D₂ : Set S}
    (hO : IsOArc (discBd D₂))
    (Rim : Drawing S)
    (hVC : Rim.V ⊆ discBd D₂)
    (a : S)
    (L : S → Set S)
    (haD : a ∈ D₂)
    (hab : a ∉ discBd D₂)
    (hL : ∀ z ∈ Rim.V, z ≠ a ∧ IsLineWithEnds (L z) a z ∧ L z ⊆ D₂ ∧ L z ∩ discBd D₂ = {z})
    (hdis : ∀ z ∈ Rim.V, ∀ z' ∈ Rim.V, z ≠ z' → L z ∩ L z' ⊆ {a})
    (St : Drawing S)
    (hSU : St.U = insert a (⋃ z ∈ Rim.V, L z))
    (hSV : St.V = insert a Rim.V)
    (hSE : St.E = (fun z => L z \ {a, z}) '' Rim.V)
    (W : Drawing S)
    (hWU : W.U = discBd D₂ ∪ insert a (⋃ z ∈ Rim.V, L z))
    (hWV : W.V = insert a Rim.V)
    (haW : a ∈ W.V)
    (hcap : ∀ z ∈ Rim.V, L z ∩ W.V = {a, z})
    (hspoke : ∀ {g : Set S} {u v : S}, g ∈ St.E → W.toGraph.IsLink g u v → ∃ z ∈ Rim.V, z ≠ a ∧
      ({u, v} : Set S) = {a, z})
    (hrimV : ∀ {g : Set S} {u v : S}, g ∈ Rim.E → W.toGraph.IsLink g u v → u ≠ a)
    (hanB : a ∉ B)
    (hpairs : ∀ {u v z : S}, ({u, v} : Set S) = {a, z} → u = a ∧ v = z ∨ u = z ∧ v = a) :
    ∀ (U₁ U₂ X : Set S), IsClosed U₁ → IsClosed U₂ → W.U ⊆ U₁ ∪ U₂ → W.U ∩ U₁ ∩ U₂ ⊆ X → X ⊆ W.V →
      X.ncard ≤ 2 → W.V \ X ⊆ U₁ ∨ W.V \ X ⊆ U₂ := by
  intro U₁ U₂ X h₁ h₂ hcov hcap₂ hXV hXc
  by_cases haX : a ∈ X
  · let P := discBd D₂ \ (X \ {a})
    have hX' : (X \ {a}).ncard ≤ 1 := by
      rw [ncard_sdiff_singleton_of_mem haX]
      omega
    have hP : IsPreconnected P := by
      rcases eq_empty_or_nonempty (X \ {a}) with h₀ | ⟨q, hq⟩
      · change IsPreconnected (discBd D₂ \ (X \ {a}))
        rw [h₀, sdiff_empty]
        exact isPreconnected_of_oArc hO
      · have hXf : (X \ {a}).Finite := W.finite_V.subset fun z hz => hXV hz.1
        have hs : X \ {a} = {q} := subset_antisymm
          (fun z hz => (ncard_le_one hXf).mp hX' z hz q hq) (singleton_subset_iff.mpr hq)
        change IsPreconnected (discBd D₂ \ (X \ {a}))
        rw [hs]
        by_cases hqO : q ∈ discBd D₂
        · exact (isPathConnected_oArc_diff hO hqO).isConnected.isPreconnected
        · rw [sdiff_singleton_eq_self hqO]
          exact isPreconnected_of_oArc hO
    have hPU : P ⊆ W.U := fun z hz => hWU ▸ Or.inl hz.1
    have hside := preconn_side hP h₁ h₂ (hPU.trans hcov) (fun z hz hz₁ hz₂ => hz.2
      ⟨hcap₂ ⟨⟨hPU hz, hz₁⟩, hz₂⟩, fun h₃ => hab (h₃ ▸ hz.1)⟩)
    have hVP : W.V \ X ⊆ P := by
      rintro z ⟨hz, hzX⟩
      rw [hWV] at hz
      rcases hz with hz | hz
      · exact absurd (hz ▸ haX) hzX
      · exact ⟨hVC hz, fun h₃ => hzX h₃.1⟩
    rcases hside with hs | hs
    · exact Or.inl (hVP.trans hs)
    · exact Or.inr (hVP.trans hs)
  · have haU : a ∈ W.U := W.V_subset_U haW
    have key : ∀ {K K' : Set S}, IsClosed K → IsClosed K' → W.U ⊆ K ∪ K' →
        W.U ∩ K ∩ K' ⊆ X → a ∈ K → W.V \ X ⊆ K := by
      intro K K' hK hK' hc' hd ha z hz
      obtain ⟨hzV, hzX⟩ := hz
      rw [hWV] at hzV
      rcases hzV with rfl | hzV
      · exact ha
      · have hlU : L z ⊆ W.U := fun p hp =>
          hWU ▸ Or.inr (Or.inr (mem_iUnion₂.mpr ⟨z, hzV, hp⟩))
        have hdis₂ : ∀ p ∈ L z, p ∈ K → p ∈ K' → False := by
          intro p hp hp₁ hp₂
          have hpX := hd ⟨⟨hlU hp, hp₁⟩, hp₂⟩
          have : p ∈ L z ∩ W.V := ⟨hp, hXV hpX⟩
          rw [hcap z hzV] at this
          rcases this with h₃ | h₃
          · exact haX (h₃ ▸ hpX)
          · exact hzX (h₃ ▸ hpX)
        rcases preconn_side (line_preconn (hL z hzV).2.1) hK hK' (hlU.trans hc') hdis₂
          with h₃ | h₃
        · exact h₃ (line_end (hL z hzV).2.1)
        · exact (hdis₂ a (line_start (hL z hzV).2.1) ha (h₃ (line_start (hL z hzV).2.1))).elim
    rcases hcov haU with ha | ha
    · exact Or.inl (key h₁ h₂ hcov hcap₂ ha)
    · refine Or.inr (key h₂ h₁ (by rwa [union_comm]) ?_ ha)
      rintro z ⟨⟨h₃, h₄⟩, h₅⟩
      exact hcap₂ ⟨⟨h₃, h₅⟩, h₄⟩

/-- **The wheel.** `D₁` is any preconnected set that holds the rim. -/
theorem exists_wheel {B D₁ D₂ : Set S} (hD₂ : IsClosedDisc D₂) (hB : B.Finite) (hBb : B ⊆ discBd D₂)
    (hD₁ : IsPreconnected D₁) (hsub : discBd D₂ ⊆ D₁) :
    ∃ (W : Drawing S) (a : S), Wheel W B D₁ D₂ ∧ a ∈ W.V ∧ a ∈ D₂ ∧ a ∉ discBd D₂ ∧
      W.V ⊆ insert a (discBd D₂) ∧ ∀ z ∈ W.V, z ≠ a → ∃ g, W.toGraph.IsLink g a z := by
  classical
  have hO : IsOArc (discBd D₂) := hD₂.isOArc_discBd
  obtain ⟨c, hc⟩ : (discBd D₂).Nonempty := (infinite_of_isOArc hO).nonempty
  obtain ⟨D₀, hU₀, hV₀⟩ := exists_drawing_on_oArc hO (hB.insert c) (insert_nonempty _ _)
    (insert_subset hc hBb)
  have hE₀ : D₀.E.Nonempty := by
    by_contra hn
    have hemp : D₀.E = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hU := D₀.U_eq
    rw [hemp] at hU
    have : D₀.U = D₀.V := by simpa using hU
    exact infinite_of_isOArc hO ((hU₀.symm.trans this) ▸ D₀.finite_V)
  obtain ⟨Rim, T, hRU, hRV, hnl, hnob, hsimple, hT4, hTV, hT2⟩ := exists_rim D₀ hE₀
  have hBV : B ⊆ D₀.V := by
    rw [hV₀]
    exact subset_insert _ _
  have hVC : Rim.V ⊆ discBd D₂ := fun z hz => by
    have := Rim.V_subset_U hz
    rwa [hRU, hU₀] at this
  obtain ⟨a, L, haD, hab, hL, hdis⟩ := exists_spokes hD₂ hVC
  obtain ⟨St, hSU, hSV, hSE⟩ := exists_star (a := a) (L := L) Rim.finite_V
    (fun z hz => ⟨(hL z hz).1, (hL z hz).2.1⟩) hdis
  have hmeet : Rim.U ∩ St.U ⊆ Rim.V ∩ St.V := by
    rintro z ⟨hz, hz'⟩
    have hzb : z ∈ discBd D₂ := by rwa [hRU, hU₀] at hz
    rw [hSU] at hz'
    rcases hz' with hz' | hz'
    · exact absurd (hz' ▸ hzb) hab
    · obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp hz'
      have h₁ : z ∈ L w ∩ discBd D₂ := ⟨hzw, hzb⟩
      rw [(hL w hw).2.2.2] at h₁
      have h₂ : z = w := h₁
      subst h₂
      exact ⟨hw, hSV ▸ Or.inr hw⟩
  let W := Rim.glue St hmeet
  have hu : IsUnion Rim St W := isUnion_glue hmeet
  have hWU : W.U = discBd D₂ ∪ insert a (⋃ z ∈ Rim.V, L z) := by
    change Rim.U ∪ St.U = _
    rw [hRU, hU₀, hSU]
  have hWV : W.V = insert a Rim.V := by
    change Rim.V ∪ St.V = _
    rw [hSV, union_eq_right.mpr (subset_insert _ _)]
  have haW : a ∈ W.V := hWV ▸ mem_insert _ _
  -- The links of a spoke.
  have hcap : ∀ z ∈ Rim.V, L z ∩ W.V = {a, z} := by
    exact spokes_meet_wheel_vertices_at_ends (S := S) (D₂ := D₂) Rim hVC a L haD hab hL hdis St
      hSU hSV hSE W hWU hWV haW
  have hspoke : ∀ {g u v}, g ∈ St.E → W.toGraph.IsLink g u v → ∃ z ∈ Rim.V, z ≠ a ∧
      ({u, v} : Set S) = {a, z} := by
    exact star_edges_link_spoke_endpoints (S := S) (D₂ := D₂) Rim a L hL St hSE W hcap
  have hrimC : ∀ {g u v}, g ∈ Rim.E → W.toGraph.IsLink g u v → Rim.toGraph.IsLink g u v :=
    fun {g u v} hg hl => (hu.linkH g hg u v).mp hl
  have hEsplit : ∀ {g}, g ∈ W.E → g ∈ Rim.E ∨ g ∈ St.E := fun {g} hg => by
    have h₁ : g ∈ W.E := hg
    rw [hu.hE] at h₁
    exact h₁
  have hrimV : ∀ {g u v}, g ∈ Rim.E → W.toGraph.IsLink g u v → u ≠ a := by
    intro g u v hg hl h
    exact hab (h ▸ hVC (hrimC hg hl).left_mem)
  have hanB : a ∉ B := fun h => hab (hBb h)
  have hpairs : ∀ {u v z : S}, ({u, v} : Set S) = {a, z} → (u = a ∧ v = z) ∨ (u = z ∧ v = a) := by
    intro u v z h
    exact Set.pair_eq_pair_iff.mp h
  refine ⟨W, a, ?_, haW, haD, hab, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hWU]
      refine union_subset (Surface.discBd_subset D₂) (insert_subset haD ?_)
      exact iUnion₂_subset fun z hz => (hL z hz).2.2.1
    · rw [hWU]
      exact subset_union_left
    · have hstar : IsPreconnected (⋃ z ∈ Rim.V, L z) := by
        have := isPreconnected_sUnion a (L '' Rim.V)
          (by rintro _ ⟨z, hz, rfl⟩; exact line_start (hL z hz).2.1)
          (by rintro _ ⟨z, hz, rfl⟩; exact line_preconn (hL z hz).2.1)
        rwa [sUnion_image] at this
      obtain ⟨z, hz⟩ : Rim.V.Nonempty := ⟨c, hRV (hV₀ ▸ mem_insert _ _)⟩
      have hzs : z ∈ ⋃ z ∈ Rim.V, L z := mem_iUnion₂.mpr ⟨z, hz, line_end (hL z hz).2.1⟩
      have hun := hD₁.union z (hsub (hVC hz)) hzs hstar
      convert hun using 1
      rw [hWU]
      have has : a ∈ ⋃ z ∈ Rim.V, L z := mem_iUnion₂.mpr ⟨z, hz, line_start (hL z hz).2.1⟩
      rw [insert_eq_of_mem has, ← union_assoc, union_eq_left.mpr hsub]
    · exact (hBV.trans hRV).trans fun z hz => hWV ▸ Or.inr hz
    · intro e u hl
      rcases hEsplit hl.1 with he | he
      · exact hnl e u (hrimC he hl)
      · obtain ⟨z, hz, hne, hp⟩ := hspoke he hl
        rcases hpairs hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact hne (h₂.symm.trans h₁)
        · exact hne (h₁.symm.trans h₂)
    · intro e e' u v hl hl'
      rcases hEsplit hl.1 with he | he <;> rcases hEsplit hl'.1 with he' | he'
      · exact hsimple e e' u v (hrimC he hl) (hrimC he' hl')
      · exfalso
        obtain ⟨z, -, -, hp⟩ := hspoke he' hl'
        have ha := hpairs hp
        have hu₁ := hrimV he hl
        have hv₁ := hrimV he hl.symm
        rcases ha with ⟨h₁, -⟩ | ⟨-, h₁⟩
        · exact hu₁ h₁
        · exact hv₁ h₁
      · exfalso
        obtain ⟨z, -, -, hp⟩ := hspoke he hl
        have hu₁ := hrimV he' hl'
        have hv₁ := hrimV he' hl'.symm
        rcases hpairs hp with ⟨h₁, -⟩ | ⟨-, h₁⟩
        · exact hu₁ h₁
        · exact hv₁ h₁
      · have hSE' := hSE
        obtain ⟨z, hz, hne, hp⟩ := hspoke he hl
        obtain ⟨z', hz', hne', hp'⟩ := hspoke he' hl'
        have hzz : z = z' := by
          have h₁ : ({a, z} : Set S) = {a, z'} := hp.symm.trans hp'
          have h₂ : z ∈ ({a, z'} : Set S) := h₁ ▸ Or.inr rfl
          rcases h₂ with h₂ | h₂
          · exact absurd h₂ hne
          · exact h₂
        subst hzz
        rw [hSE] at he he'
        obtain ⟨w, hw, rfl⟩ := he
        obtain ⟨w', hw', rfl⟩ := he'
        have hc₁ := hl.2.2.2
        have hc₂ := hl'.2.2.2
        rw [closure_sdiff_pair (hL w hw).2.1, hcap w hw] at hc₁
        rw [closure_sdiff_pair (hL w' hw').2.1, hcap w' hw'] at hc₂
        have h₃ : ({a, w} : Set S) = {a, w'} := hc₁.trans hc₂.symm
        have h₄ : w ∈ ({a, w'} : Set S) := h₃ ▸ Or.inr rfl
        have hww : w = w' := by
          rcases h₄ with h₄ | h₄
          · exact absurd h₄ (hL w hw).1
          · exact h₄
        rw [hww]
    · intro e u v hl huB
      rcases hEsplit hl.1 with he | he
      · exact fun hvB => hnob e u v (hrimC he hl) (hBV huB) (hBV hvB)
      · obtain ⟨z, -, -, hp⟩ := hspoke he hl
        rcases hpairs hp with ⟨h₁, -⟩ | ⟨-, h₁⟩
        · exact absurd (h₁ ▸ huB) hanB
        · exact h₁ ▸ hanB
    · refine ⟨T, hTV.trans fun z hz => hWV ▸ Or.inr hz, hT4, ?_⟩
      intro v hv
      obtain ⟨g, g', hne, hi, hi'⟩ := hT2 v hv
      have hvV := hTV hv
      obtain ⟨hne', hl', -, -⟩ := hL v hvV
      let sp := L v \ {a, v}
      have hsp : sp ∈ St.E := hSE ▸ mem_image_of_mem _ hvV
      have hspW : sp ∈ W.E := hu.hE ▸ Or.inr hsp
      have hspl : W.toGraph.IsLink sp v a := by
        refine ⟨hspW, hWV ▸ Or.inr hvV, haW, ?_⟩
        rw [closure_sdiff_pair hl', hcap v hvV, pair_comm]
      have hconv : ∀ {g}, Rim.toGraph.Inc g v → W.toGraph.Inc g v := by
        rintro g ⟨t, ht⟩
        exact ⟨t, (hu.linkH g ht.1 v t).mpr ht⟩
      have hspne : ∀ {g}, Rim.toGraph.Inc g v → sp ≠ g := by
        rintro g ⟨t, ht⟩ h
        have h₁ : a ∈ closure sp ∩ W.V := by
          rw [hspl.2.2.2]
          exact Or.inr rfl
        have h₂ : a ∈ closure g := h ▸ h₁.1
        have h₃ := Rim.closure_subset_U ht.1 h₂
        rw [hRU, hU₀] at h₃
        exact hab h₃
      have hsub₃ : ({sp, g, g'} : Set (Set S)) ⊆ {e | W.toGraph.Inc e v} := by
        rintro e (rfl | rfl | rfl)
        · exact ⟨a, hspl⟩
        · exact hconv hi
        · exact hconv hi'
      have hfin : {e | W.toGraph.Inc e v}.Finite := W.finite_edges.subset fun e he => he.edge_mem
      have hc₃ : ({sp, g, g'} : Set (Set S)).ncard = 3 := by
        rw [ncard_eq_three]
        exact ⟨sp, g, g', hspne hi, hspne hi', hne, rfl⟩
      rw [← hc₃]
      exact ncard_le_ncard hsub₃ hfin
    · exact wheel_has_no_small_separation (S := S) (B := B) (D₂ := D₂) hO Rim hVC a L haD hab hL
        hdis St hSU hSV hSE W hWU hWV haW hcap hspoke hrimV hanB hpairs
  · rw [hWV]
    exact insert_subset_insert hVC
  · intro z hz hza
    rw [hWV] at hz
    have hzR : z ∈ Rim.V := hz.resolve_left hza
    obtain ⟨-, hl', -, -⟩ := hL z hzR
    have hsp : L z \ {a, z} ∈ St.E := hSE ▸ mem_image_of_mem _ hzR
    refine ⟨L z \ {a, z}, hu.hE ▸ Or.inr hsp, haW, hWV ▸ Or.inr hzR, ?_⟩
    rw [closure_sdiff_pair hl', hcap z hzR]

end GraphMinor.GM14.Whitney
