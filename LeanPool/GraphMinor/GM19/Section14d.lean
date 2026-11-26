/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14c
public import LeanPool.GraphMinor.Surface.PlaneSeparation
public import LeanPool.GraphMinor.Surface.Crossing
public import LeanPool.GraphMinor.Surface.CrossCut
public import LeanPool.GraphMinor.Surface.CutTree
public import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Graph Minors XIX, Section 14: a set that does not cut the plane

The hub with all the spokes does not separate the plane. So each point of `W` off that set is joined
to `bd(W)`. This is how we see that the sectors and `ins(H)` cover `W`, which the paper takes as
seen.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface

/-- `A` does not separate the plane. -/
def NonSep (A : Set ℂ) : Prop := ∀ a b, a ∉ A → b ∉ A → b ∈ connectedComponentIn Aᶜ a

theorem nonSep_of_line {L : Set ℂ} {u v : ℂ} (h : IsLineWithEnds L u v) : NonSep L := by
  obtain ⟨φ, -⟩ := h
  intro a b ha hb
  rw [component_eq_of_arc φ ha hb]
  exact mem_connectedComponentIn hb

theorem nonSep_singleton (z : ℂ) : NonSep {z} := by
  intro a b ha hb
  have hc : IsPreconnected ({z}ᶜ : Set ℂ) := (isConnected_compl_singleton_of_one_lt_rank
    (by simp) z).isPreconnected
  exact hc.subset_connectedComponentIn ha subset_rfl hb

theorem NonSep.union {A B : Set ℂ} (hA : NonSep A) (hB : NonSep B) (cA : IsCompact A)
  (cB : IsCompact B) (hAB : IsPreconnected (A ∩ B)) :
    NonSep (A ∪ B) := fun a b ha hb ↦
  janiszewski cA cB hAB ha hb (hA a b (fun h ↦ ha (.inl h)) fun h ↦ hb (.inl h)) (hB a b
    (fun h ↦ ha (.inr h)) fun h ↦ hb (.inr h))

/-- The inside of an `O`-arc in the closed unit disc of `ℂ` lies in that disc. -/
theorem closedInner_subset_closedBall {G : Set ℂ} (hG : G ⊆ closedBall 0 1) : closedInner G ⊆
  closedBall 0 1 := by
  rintro z (⟨hz, hb⟩ | hz)
  · by_contra hn
    have hz1 : 1 < ‖z‖ := by simpa [mem_closedBall, dist_zero_right] using hn
    set L : Set ℂ := (fun t : ℝ ↦ (t : ℂ) * z) '' Ici 1 with hL
    have hLc : IsPreconnected L := (isPreconnected_Ici).image _ (by fun_prop)
    have hLoff : L ⊆ Gᶜ := by
      rintro _ ⟨t, ht, rfl⟩ hm
      have h₁ := hG hm
      simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs] at h₁
      have ht' : (1 : ℝ) ≤ t := ht
      rw [abs_of_pos (by linarith)] at h₁
      nlinarith [norm_nonneg z]
    have hzL : z ∈ L := ⟨1, mem_Ici.mpr le_rfl, by simp⟩
    have hsub := hLc.subset_connectedComponentIn hzL hLoff
    obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℂ)
    have hpos : 0 < ‖z‖ := by linarith
    have h₂ : (((|R| + 1) : ℝ) : ℂ) * z ∈ L :=
      ⟨|R| + 1, mem_Ici.mpr (by linarith [abs_nonneg R]), rfl⟩
    have h₃ := hR (hsub h₂)
    simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h₃
    rw [abs_of_pos (by have := abs_nonneg R; linarith)] at h₃
    have := le_abs_self R
    nlinarith [abs_nonneg R]
  · exact hG hz

/-- A closed disc in the closed unit disc does not separate the plane. -/
theorem nonSep_of_disc {E : Set ℂ} (hE : IsClosedDisc E) (hsub : E ⊆ closedBall 0 1) : NonSep E
  := by
  obtain ⟨φ⟩ := hE.isOArc_discBd
  have hparts := isJordanParts φ
  have hbsub : discBd E ⊆ closedBall 0 1 := (Surface.discBd_subset E).trans hsub
  obtain ⟨h₁, h₂⟩ := isClosedDisc_closedInner ⟨φ⟩
  have hin := closedInner_subset_closedBall hbsub
  obtain ⟨Δ, -, huniq⟩ := disc_oArc (closedBall (0 : ℂ) 1) (discBd E) isClosedDisc_closedBall.1
    hbsub hE.isOArc_discBd
  have heq : E = closedInner (discBd E) := (huniq E hsub hE rfl).trans (huniq _ hin h₁ h₂).symm
  have hcompl : Eᶜ = outer (discBd E) := by
    apply subset_antisymm
    · intro z hz
      have hz' : z ∈ (discBd E)ᶜ := fun h ↦ hz (Surface.discBd_subset E h)
      rw [← hparts.union_eq] at hz'
      rcases hz' with h | h
      · exact absurd (heq ▸ (Or.inl h : z ∈ closedInner (discBd E))) hz
      · exact h
    · intro z hz hzE
      rw [heq] at hzE
      rcases hzE with h | h
      · exact disjoint_left.mp hparts.disjoint h hz
      · exact hz.1 h
  intro a b ha hb
  have hc : IsPreconnected Eᶜ := hcompl ▸ hparts.isConnected_outer.isPreconnected
  exact hc.subset_connectedComponentIn ha subset_rfl hb

/-- A point of the open unit disc off a set that does not separate the plane is joined, off that
set, to a point of the unit circle. -/
theorem exists_plane_exit {A : Set ℂ} (hA : NonSep A) (cA : IsCompact A)
  (hsub : A ⊆ closedBall 0 1) {x : ℂ} (hx : x ∈ ball (0 : ℂ) 1) (hxA : x ∉ A) :
    ∃ J y, IsPreconnected J ∧ x ∈ J ∧ J ⊆ ball 0 1 \ A ∧ y ∈ sphere (0 : ℂ) 1 \ A ∧ y ∈ closure J
      := by
  classical
  have hbA : (2 : ℂ) ∉ A := fun h ↦ by
    have := hsub h
    simp at this
  have hb := hA x 2 hxA hbA
  have hop : IsOpen Aᶜ := cA.isClosed.isOpen_compl
  have hcc : IsOpen (connectedComponentIn Aᶜ x) := hop.connectedComponentIn
  have hconn : IsConnected (connectedComponentIn Aᶜ x) := isConnected_connectedComponentIn_iff.mpr
    hxA
  have hpath := (hcc.isConnected_iff_isPathConnected).mp hconn
  obtain ⟨γ, hγ⟩ := hpath.joinedIn x (mem_connectedComponentIn hxA) 2 hb
  have hγA : ∀ s, γ s ∉ A := fun s ↦ connectedComponentIn_subset _ _ (hγ s)
  have hTc : IsCompact {s : unitInterval | 1 ≤ ‖γ s‖} :=
    (isClosed_le continuous_const (continuous_norm.comp γ.continuous)).isCompact
  have hTne : {s : unitInterval | 1 ≤ ‖γ s‖}.Nonempty := ⟨1, by simp⟩
  obtain ⟨t, ht, hmin⟩ := hTc.exists_isLeast hTne
  have ht0 : (0 : unitInterval) < t := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h ↦ ?_
    have h₁ : 1 ≤ ‖γ t‖ := ht
    rw [← h, γ.source] at h₁
    have h₂ : ‖x‖ < 1 := by simpa using hx
    linarith
  have hIio : Iio t ⊆ {s : unitInterval | 1 ≤ ‖γ s‖}ᶜ := fun s hs h ↦ absurd (hmin h)
    (not_le.mpr hs)
  have hJball : γ '' Iio t ⊆ ball 0 1 \ A := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨?_, hγA s⟩
    have := hIio hs
    simpa using this
  have hcl : γ t ∈ closure (γ '' Iio t) := by
    have hmem : t ∈ closure (Iio t) := by
      rw [closure_Iio' (a := t) (⟨0, ht0⟩ : (Iio t).Nonempty)]
      exact Set.mem_Iic.mpr le_rfl
    exact image_closure_subset_closure_image γ.continuous (mem_image_of_mem _ hmem)
  refine ⟨γ '' Iio t, γ t, isPreconnected_Iio.image _ γ.continuous.continuousOn, ⟨0, ht0,
    γ.source⟩, hJball, ⟨?_, hγA t⟩, hcl⟩
  have h₁ : 1 ≤ ‖γ t‖ := ht
  have h₂ : γ t ∈ closedBall (0 : ℂ) 1 := closure_minimal (hJball.trans
    (sdiff_subset.trans ball_subset_closedBall)) isClosed_closedBall hcl
  have h₃ : ‖γ t‖ ≤ 1 := by simpa using h₂
  simpa using le_antisymm h₃ h₁

/-- `exists_plane_exit` in a closed disc. -/
theorem exists_plane_exit_of_disc {T : Type} [TopologicalSpace T] {W A : Set T}
  {h : T → ℂ} {g : ℂ → T} (c : IsChart W h g)
    (hA : NonSep (h '' A)) (cA : IsCompact A) (hAW : A ⊆ W) {x : T} (hx : x ∈ discInt W)
      (hxA : x ∉ A) :
    ∃ J y, IsPreconnected J ∧ x ∈ J ∧ J ⊆ discInt W \ A ∧ y ∈ discBd W \ A ∧ y ∈ closure J := by
  have hxW : x ∈ W := hx.1
  have hcA : IsCompact (h '' A) := cA.image_of_continuousOn (c.hc.mono hAW)
  have hsub : h '' A ⊆ closedBall 0 1 := image_subset_iff.mpr fun a ha ↦ c.hm (hAW ha)
  have hnot : ∀ {z}, z ∈ W → h z ∈ h '' A → z ∈ A := fun {z} hz ⟨a, ha, he⟩ ↦ by
    rw [← c.gh hz, ← he, c.gh (hAW ha)]
    exact ha
  have hxb : h x ∈ ball (0 : ℂ) 1 := by
    have hm := c.hm hxW
    rcases (mem_closedBall.mp hm).lt_or_eq with h' | h'
    · exact mem_ball.mpr h'
    · exfalso
      have hs : h x ∈ sphere (0 : ℂ) 1 := mem_sphere.mpr h'
      rw [← c.bd] at hs
      obtain ⟨z, hz, he⟩ := hs
      have : z = x := by rw [← c.gh (Surface.discBd_subset W hz), ← c.gh hxW, he]
      exact hx.2 (this ▸ hz)
  obtain ⟨J, y, hJc, hxJ, hJ, hy, hyc⟩ := exists_plane_exit hA hcA hsub hxb fun h' ↦ hxA
    (hnot hxW h')
  have hsubB : J ⊆ closedBall 0 1 := hJ.trans (sdiff_subset.trans ball_subset_closedBall)
  have hyB : y ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hy.1
  have hgi : ∀ {z}, z ∈ ball (0 : ℂ) 1 → g z ∈ discInt W := fun {z} hz ↦ by
    rw [c.discInt_eq]
    exact mem_image_of_mem _ hz
  refine ⟨g '' J, g y, hJc.image _ (c.gc.mono hsubB), ⟨h x, hxJ, c.gh hxW⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨hgi (hJ hz).1, fun hm ↦ (hJ hz).2 ⟨g z, hm, c.hg (ball_subset_closedBall (hJ hz).1)⟩⟩
  · have hs : y ∈ h '' discBd W := c.bd ▸ hy.1
    obtain ⟨z, hz, rfl⟩ := hs
    rw [c.gh (Surface.discBd_subset W hz)]
    exact hz
  · exact fun hm ↦ hy.2 ⟨g y, hm, c.hg hyB⟩
  · have hcw : ContinuousWithinAt g J y := (c.gc y hyB).mono hsubB
    exact hcw.mem_closure_image hyc

end GraphMinor.GM19
