/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscNbhd
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Complex.ReImTopology

/-!
# A fan of squares

A fan at a point `y` given by maps of the unit square, each with the corner `0` at `y`. Each square
has a left side and a
lower side at this corner. The left sides are pasted in pairs by a map `tw` and the lower sides by a
map `pt`, where
`pt g = g` means that the lower side of `g` is free. Then the union of the squares is a closed disc
(`IsSquareFan.exists_disc`), with `y` on its boundary exactly when a lower side is free.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Complex

universe u v

variable {X : Type u} [TopologicalSpace X]

local notation "𝕀" => unitInterval

/-- The unit square. -/
def unitSq : Set ℂ := Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1

theorem isCompact_unitSq : IsCompact unitSq :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    (Metric.isBounded_Icc _ _ |>.reProdIm (Metric.isBounded_Icc _ _))

theorem unitSq_disc : IsClosedDisc unitSq ∧ discBd unitSq = frontier unitSq := by
  have hc : Convex ℝ unitSq :=
    ((convex_Icc (0 : ℝ) 1).is_linear_preimage reLm.isLinear).inter
      ((convex_Icc (0 : ℝ) 1).is_linear_preimage imLm.isLinear)
  have hcl : IsClosed unitSq := isClosed_Icc.reProdIm isClosed_Icc
  have hi : (interior unitSq).Nonempty := by
    rw [unitSq, interior_reProdIm, interior_Icc]
    exact ⟨⟨1 / 2, 1 / 2⟩, by constructor <;> norm_num⟩
  obtain ⟨e, -, h2, h3⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hi
    isCompact_unitSq.isBounded
  rw [hcl.closure_eq] at h2
  have h4 := (isClosedDisc_closedBall).1.image (f := e.symm) (f' := e)
    e.symm.continuous.continuousOn
    e.continuous.continuousOn (fun z _ => e.apply_symm_apply z)
  have h5 : ∀ A : Set ℂ, e.symm '' (e '' A) = A := fun A => by
    rw [image_image]
    simp
  rw [← h2, h5] at h4
  refine ⟨h4.1, ?_⟩
  rw [h4.2, h2, isClosedDisc_closedBall.2, ← h3, h5]

theorem mem_frontier_unitSq {z : ℂ} (hz : z ∈ unitSq) (h : z.re = 0 ∨ z.im
  = 0) : z ∈ frontier unitSq := by
  have hcl : IsClosed unitSq := isClosed_Icc.reProdIm isClosed_Icc
  rw [frontier, hcl.closure_eq]
  refine ⟨hz, ?_⟩
  rw [unitSq, interior_reProdIm, interior_Icc]
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · exact h1.1.ne' h
  · exact h2.1.ne' h

/-- The hypotheses on a fan of squares. -/
structure IsSquareFan (y : X) {G : Type v} (M : G → ℂ → X) (tw pt : G → G) : Prop where
  cont : ∀ g, ContinuousOn (M g) unitSq
  zero : ∀ g, M g 0 = y
  tw_ne : ∀ g, tw g ≠ g
  tw_eq : ∀ g, ∀ s ∈ Icc (0 : ℝ) 1, M (tw g) (s * I) = M g (s * I)
  pt_eq : ∀ g, ∀ s ∈ Icc (0 : ℝ) 1, M (pt g) s = M g s
  core : ∀ g g' z z', z ∈ unitSq → z' ∈ unitSq → M g z = M g' z' →
    (g = g' ∧ z = z') ∨ (z = 0 ∧ z' = 0) ∨ (z = z' ∧ z.re = 0 ∧ g' = tw g) ∨ (z = z' ∧ z.im = 0
      ∧ g' = pt g)
  conn : ∀ A : Set G, A.Nonempty → (∀ g ∈ A, tw g ∈ A ∧ pt g ∈ A) → A = univ

namespace IsSquareFan

variable {y : X} {G : Type v} {M : G → ℂ → X} {tw pt : G → G}

theorem mem_left {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : (s * I : ℂ) ∈ unitSq := by
  constructor <;> simp [hs.1, hs.2]

theorem mem_low {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : (s : ℂ) ∈ unitSq := by
  constructor <;> simp [hs.1, hs.2]

theorem injOn (h : IsSquareFan y M tw pt) (g : G) : InjOn (M g) unitSq := fun z hz z' hz' he => by
  rcases h.core g g z z' hz hz' he with h1 | h1 | h1 | h1
  · exact h1.2
  · rw [h1.1, h1.2]
  · exact h1.1
  · exact h1.1

/-- The ray of the left side. -/
def left (M : G → ℂ → X) (g : G) : Set X := (fun s : ℝ => M g (s * I)) '' Icc (0 : ℝ) 1

/-- The ray of the lower side. -/
def low (M : G → ℂ → X) (g : G) : Set X := (fun s : ℝ => M g s) '' Icc (0 : ℝ) 1

/-- The member of the fan of `g`. -/
def piece (M : G → ℂ → X) (g : G) : Set X × Set (Set X) := (M g '' unitSq, {left M g, low M g})

theorem left_tw (h : IsSquareFan y M tw pt) (g : G) : left M (tw g) = left M g :=
  image_congr fun s hs => h.tw_eq g s hs

theorem low_pt (h : IsSquareFan y M tw pt) (g : G) : low M (pt g) = low M g :=
  image_congr fun s hs => h.pt_eq g s hs

theorem I_ne_ofReal (t : ℝ) : (I : ℂ) ≠ t := fun he => by
  have := congrArg Complex.im he
  simp at this

theorem of_left (h : IsSquareFan y M tw pt) {g g' : G} (hr : left M g ∈ (piece M g').2) : g' = g
  ∨ g' = tw g := by
  have hm : M g I ∈ left M g := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have h1 : (I : ℂ) ∈ unitSq := by simpa using mem_left (s := 1) ⟨zero_le_one, le_rfl⟩
  rcases hr with hr | hr
  · rw [hr] at hm
    obtain ⟨s, hs, he⟩ := hm
    rcases h.core g g' _ _ h1 (mem_left hs) he.symm with h2 | h2 | h2 | h2
    · exact .inl h2.1.symm
    · simp at h2
    · exact .inr h2.2.2
    · simp at h2
  · rw [hr] at hm
    obtain ⟨s, hs, he⟩ := hm
    rcases h.core g g' _ _ h1 (mem_low hs) he.symm with h2 | h2 | h2 | h2
    · exact absurd h2.2 (I_ne_ofReal s)
    · simp at h2
    · exact absurd h2.1 (I_ne_ofReal s)
    · simp at h2

theorem of_low (h : IsSquareFan y M tw pt) {g g' : G} (hr : low M g ∈ (piece M g').2) : g' = g ∨ g'
  = pt g := by
  have hm : M g 1 ∈ low M g := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have h1 : (1 : ℂ) ∈ unitSq := by simpa using mem_low (s := 1) ⟨zero_le_one, le_rfl⟩
  rcases hr with hr | hr
  · rw [hr] at hm
    obtain ⟨s, hs, he⟩ := hm
    rcases h.core g g' _ _ h1 (mem_left hs) he.symm with h2 | h2 | h2 | h2
    · have := congrArg Complex.re h2.2
      simp at this
    · simp at h2
    · simp at h2
    · have := congrArg Complex.re h2.1
      simp at this
  · rw [hr] at hm
    obtain ⟨s, hs, he⟩ := hm
    rcases h.core g g' _ _ h1 (mem_low hs) he.symm with h2 | h2 | h2 | h2
    · exact .inl h2.1.symm
    · simp at h2
    · simp at h2
    · exact .inr h2.2.2

theorem piece_inj (h : IsSquareFan y M tw pt) : Function.Injective (piece M) := by
  intro g g' he
  have h1 : ((1 / 2 + 1 / 2 * I : ℂ)) ∈ unitSq := by
    constructor <;> norm_num
  have h2 : M g (1 / 2 + 1 / 2 * I) ∈ M g' '' unitSq := by
    have h3 : M g '' unitSq = M g' '' unitSq := congrArg Prod.fst he
    rw [← h3]
    exact mem_image_of_mem _ h1
  obtain ⟨z, hz, h3⟩ := h2
  rcases h.core g g' _ _ h1 hz h3.symm with h4 | h4 | h4 | h4
  · exact h4.1
  · have := congrArg Complex.re h4.1
    norm_num at this
  · have := h4.2.1
    norm_num at this
  · have := h4.2.1
    norm_num at this

theorem low_subset (_h : IsSquareFan y M tw pt) (g _g' : G) {s : Set X} (hs : s ∈ (piece M g).2) :
    s ⊆ M g '' unitSq := by
  rcases hs with rfl | rfl
  · rintro _ ⟨t, ht, rfl⟩
    exact mem_image_of_mem _ (mem_left ht)
  · rintro _ ⟨t, ht, rfl⟩
    exact mem_image_of_mem _ (mem_low ht)

theorem isFan [T2Space X] [Finite G] (h : IsSquareFan y M tw pt) : IsFan y (range (piece M)) := by
  classical
  have hdisc : ∀ g, IsClosedDisc (M g '' unitSq) ∧ discBd (M g '' unitSq) = M g '' frontier unitSq
    := by
    intro g
    obtain ⟨f', h1, h2⟩ := exists_inv_of_compactOn isCompact_unitSq (h.cont g) (h.injOn g)
    have h3 := unitSq_disc.1.image (h.cont g) h1 h2
    rw [unitSq_disc.2] at h3
    exact h3
  have hhalf : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ((s : ℂ)) ∈ unitSq := fun s hs => mem_low hs
  refine ⟨finite_range _, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact (hdisc g).1
  · rintro _ ⟨g, rfl⟩
    have hL : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → M g (s * I) = M g t → s = 0 ∧ t
      = 0 := by
      intro s t hs ht he
      have h1 := h.injOn g (mem_left hs) (mem_low ht) he
      have h2 := congrArg Complex.re h1
      have h3 := congrArg Complex.im h1
      exact ⟨by simpa using h3, by simpa using h2.symm⟩
    have harc : ∀ c : ℂ, (c = 1 ∨ c = I) → IsArcMap fun t : 𝕀 => M g (t.1 * c) := by
      intro c hc
      have hm : ∀ t : 𝕀, (t.1 : ℂ) * c ∈ unitSq := fun t => by
        rcases hc with rfl | rfl
        · rw [mul_one]
          exact mem_low t.2
        · exact mem_left t.2
      refine ⟨?_, fun t t' he => ?_⟩
      · refine (h.cont g).comp_continuous (by fun_prop) hm
      · have h1 := h.injOn g (hm t) (hm t') he
        have hc0 : c ≠ 0 := by
          rcases hc with rfl | rfl <;> simp
        exact Subtype.ext (by exact_mod_cast mul_right_cancel₀ hc0 h1)
    have hr : ∀ c : ℂ, (c = 1 ∨ c = I) → range (fun t : 𝕀 => M g (t.1 * c)) = (fun s : ℝ => M g
      (s * c)) '' Icc (0 : ℝ) 1 := by
      intro c _
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t.1, t.2, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hs⟩, rfl⟩
    have hL1 : IsLineWithEnds (left M g) y (M g I) := by
      have h1 := (harc I (.inr rfl)).isLineWithEnds
      rw [hr I (.inr rfl)] at h1
      simpa [h.zero, left] using h1
    have hL2 : IsLineWithEnds (low M g) y (M g 1) := by
      have h1 := (harc 1 (.inl rfl)).isLineWithEnds
      rw [hr 1 (.inl rfl)] at h1
      simpa [h.zero, left, low] using h1
    have hinter : left M g ∩ low M g = {y} := by
      apply Subset.antisymm
      · rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, he⟩⟩
        have h1 := hL s t hs ht he.symm
        simp [h1.1, h.zero]
      · rintro _ rfl
        exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, by simp [h.zero]⟩, ⟨0, ⟨le_rfl, zero_le_one⟩,
          by simp [h.zero]⟩⟩
    refine ⟨left M g, low M g, M g I, M g 1, rfl, fun he => ?_, hL1, hL2, ?_, ?_, hinter⟩
    · have h1 : M g I ∈ left M g ∩ low M g := ⟨hL1.right_mem, he ▸ hL1.right_mem⟩
      rw [hinter] at h1
      have h2 : M g I = M g 0 := by rw [h.zero]; exact h1
      have h3 := h.injOn g (by simpa using mem_left (s := 1) ⟨zero_le_one, le_rfl⟩)
        (by simpa using mem_low (s := 0) ⟨le_rfl, zero_le_one⟩) h2
      simp at h3
    · change (left M g) ⊆ discBd (M g '' unitSq)
      rw [(hdisc g).2]
      rintro _ ⟨s, hs, rfl⟩
      exact mem_image_of_mem _ (mem_frontier_unitSq (mem_left hs) (.inl (by simp)))
    · change (low M g) ⊆ discBd (M g '' unitSq)
      rw [(hdisc g).2]
      rintro _ ⟨s, hs, rfl⟩
      exact mem_image_of_mem _ (mem_frontier_unitSq (mem_low hs) (.inr (by simp)))
  · rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩ hne
    have hgg : g ≠ g' := fun he => hne (by rw [he])
    apply Subset.antisymm
    · rintro x ⟨⟨z, hz, rfl⟩, ⟨z', hz', he⟩⟩
      rcases h.core g g' z z' hz hz' he.symm with h1 | h1 | h1 | h1
      · exact absurd h1.1 hgg
      · exact .inl (by rw [h1.1, h.zero]; rfl)
      · refine .inr ⟨left M g, ⟨.inl rfl, ?_⟩, ?_⟩
        · rw [h1.2.2, ← left_tw h g]
          exact .inl (by rw [left_tw h g])
        · refine ⟨z.im, ?_, ?_⟩
          · exact hz.2
          · change M g _ = M g z
            congr 1
            apply Complex.ext <;> simp [h1.2.1]
      · refine .inr ⟨low M g, ⟨.inr rfl, ?_⟩, ?_⟩
        · rw [h1.2.2]
          exact .inr (low_pt h g).symm
        · refine ⟨z.re, hz.1, ?_⟩
          change M g _ = M g z
          congr 1
          apply Complex.ext <;> simp [h1.2.1]
    · rintro x (rfl | ⟨r, ⟨h1, h2⟩, hx⟩)
      · exact ⟨⟨0, by simpa using mem_low (s := 0) ⟨le_rfl, zero_le_one⟩, h.zero g⟩,
          ⟨0, by simpa using mem_low (s := 0) ⟨le_rfl, zero_le_one⟩, h.zero g'⟩⟩
      · exact ⟨low_subset h g g h1 hx, low_subset h g' g' h2 hx⟩
  · intro r
    by_cases hemp : {P ∈ range (piece M) | r ∈ P.2} = ∅
    · rw [hemp]
      simp
    obtain ⟨_, ⟨g, rfl⟩, hg⟩ := nonempty_iff_ne_empty.mpr hemp
    have hb : ∀ c : G, (∀ g', r ∈ (piece M g').2 → g' = g ∨ g' = c) →
        {P ∈ range (piece M) | r ∈ P.2}.encard ≤ 2 := by
      intro c hc
      have hs : {P ∈ range (piece M) | r ∈ P.2} ⊆ {piece M g, piece M c} := by
        rintro _ ⟨⟨g', rfl⟩, h2⟩
        rcases hc g' h2 with rfl | rfl
        · exact .inl rfl
        · exact .inr rfl
      refine (encard_le_encard hs).trans ((encard_insert_le _ _).trans ?_)
      rw [encard_singleton]
      norm_num
    rcases hg with rfl | rfl
    · exact hb (tw g) fun g' hr => of_left h hr
    · exact hb (pt g) fun g' hr => of_low h hr
  · rintro 𝓠 hQ ⟨_, hq⟩ hcl
    obtain ⟨g, rfl⟩ := hQ hq
    have hA := h.conn {g | piece M g ∈ 𝓠} ⟨g, hq⟩ fun g hg => by
      refine ⟨hcl _ hg _ ⟨_, rfl⟩ ⟨left M g, .inl rfl, ?_⟩, hcl _ hg _ ⟨_, rfl⟩ ⟨low M g,
        .inr rfl, ?_⟩⟩
      · exact .inl (left_tw h g).symm
      · exact .inr (low_pt h g).symm
    apply Subset.antisymm hQ
    rintro _ ⟨g', rfl⟩
    have : g' ∈ {g | piece M g ∈ 𝓠} := hA ▸ mem_univ g'
    exact this

/-- The union of the squares of a fan is a closed disc. The point is on its boundary exactly when a
lower side is
free. -/
theorem exists_disc [T2Space X] [Finite G] [Nonempty G] (h : IsSquareFan y M tw pt) :
    ∃ E, IsClosedDisc E ∧ E = (⋃ g, M g '' unitSq) ∧ ((∀ g, pt g ≠ g) → y ∉ discBd E) ∧
      ((∃ g, pt g = g) → y ∈ discBd E) := by
  obtain ⟨E, h1, h2, h3, h4⟩ := h.isFan.exists_disc _ y _ rfl (range_nonempty _)
  refine ⟨E, h1, ?_, fun hp => h3 ?_, fun hp => h4 ?_⟩
  · rw [h2, biUnion_range]
    rfl
  · rintro _ ⟨g, rfl⟩ r hr
    rcases hr with rfl | rfl
    · exact ⟨_, ⟨tw g, rfl⟩, fun he => h.tw_ne g (h.piece_inj he), .inl (left_tw h g).symm⟩
    · exact ⟨_, ⟨pt g, rfl⟩, fun he => hp g (h.piece_inj he), .inr (low_pt h g).symm⟩
  · obtain ⟨g, hg⟩ := hp
    refine ⟨_, ⟨g, rfl⟩, low M g, .inr rfl, ?_⟩
    rintro _ ⟨g', rfl⟩ hr
    rcases of_low h hr with rfl | rfl
    · rfl
    · rw [hg]

end IsSquareFan

end GraphMinor.Surface
