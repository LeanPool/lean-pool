/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.ThinFits
public import LeanPool.GraphMinor.GM19.CircleLift
public import LeanPool.GraphMinor.GM11.ArcDrawings

/-!
# The frame in the proof of Graph Minors XIX, (2.1)

Fix a way to read each cuff as the circle. The upper half of the circle is the short side on that
cuff, and the
lower half is the long side. This gives a frame.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-! ### Arcs of a cuff -/

section Arc

variable {Θ : Set S} (f : Circle ≃ₜ Θ)

/-- The open arc of angles between `a` and `b`. -/
noncomputable def arcOf (a b : ℝ) : Set S := cuffPoint f '' Ioo a b

omit [T2Space S] in
theorem cuffPoint_eq {s t : ℝ} (h : cuffPoint f s = cuffPoint f t) :
    ∃ m : ℤ, s = t + m * (2 * Real.pi) := by
  have h1 : f (Circle.exp s) = f (Circle.exp t) := Subtype.ext h
  exact Circle.exp_eq_exp.mp (f.injective h1)

omit [T2Space S] in
theorem cuffPoint_injOn {a b : ℝ} (hab : b ≤ a + 2 * Real.pi) {s t : ℝ} (hs : s ∈ Ico a b)
    (ht : t ∈ Ico a b) (h : cuffPoint f s = cuffPoint f t) : s = t := by
  obtain ⟨m, hm⟩ := cuffPoint_eq f h
  have hpi := Real.pi_pos
  have h0 : m = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have h2 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      nlinarith [hs.1, ht.2]
    · have h2 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith [ht.1, hs.2]
  rw [hm, h0]
  simp

omit [T2Space S] in
theorem cuffPoint_injOn_Icc {a b : ℝ} (hab : b < a + 2 * Real.pi) :
    InjOn (cuffPoint f) (Icc a b) := fun s hs t ht h ↦
  cuffPoint_injOn f (b := a + 2 * Real.pi) le_rfl ⟨hs.1, by linarith [hs.2]⟩
    ⟨ht.1, by linarith [ht.2]⟩ h

omit [T2Space S] in
theorem isPathConnected_arcOf {a b : ℝ} (hab : a < b) : IsPathConnected (arcOf f a b) :=
  ((convex_Ioo a b).isPathConnected (nonempty_Ioo.mpr hab)).image (continuous_cuffPoint f)

theorem closure_arcOf {a b : ℝ} (hab : a < b) : closure (arcOf f a b) = cuffPoint f '' Icc a b := by
  have h := image_closure_of_isCompact (f := cuffPoint f) (s := Ioo a b)
    (by rw [closure_Ioo hab.ne]; exact isCompact_Icc) (continuous_cuffPoint f).continuousOn
  rw [closure_Ioo hab.ne] at h
  exact h.symm

theorem isLine_arcOf {a b : ℝ} (hab : a < b) (hb : b < a + 2 * Real.pi) :
    IsLineWithEnds (closure (arcOf f a b)) (cuffPoint f a) (cuffPoint f b) := by
  rw [closure_arcOf f hab]
  exact GM11.isLine_of_injOn (continuous_cuffPoint f) hab (cuffPoint_injOn_Icc f hb)

theorem tilde_arcOf {a b : ℝ} (hab : a < b) (hb : b < a + 2 * Real.pi) :
    tilde (arcOf f a b) = {cuffPoint f a, cuffPoint f b} := by
  rw [tilde, closure_arcOf f hab]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hn⟩
    rcases eq_or_lt_of_le ht.1 with rfl | h1
    · exact Or.inl rfl
    rcases eq_or_lt_of_le ht.2 with rfl | h2
    · exact Or.inr rfl
    exact absurd ⟨t, ⟨h1, h2⟩, rfl⟩ hn
  · rintro (rfl | rfl)
    · refine ⟨⟨a, ⟨le_rfl, hab.le⟩, rfl⟩, ?_⟩
      rintro ⟨t, ht, he⟩
      have := cuffPoint_injOn_Icc f hb ⟨ht.1.le, ht.2.le⟩ ⟨le_rfl, hab.le⟩ he
      linarith [ht.1]
    · refine ⟨⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, ?_⟩
      rintro ⟨t, ht, he⟩
      have := cuffPoint_injOn_Icc f hb ⟨ht.1.le, ht.2.le⟩ ⟨hab.le, le_rfl⟩ he
      linarith [ht.2]

omit [T2Space S] in
theorem cuffPoint_mem (t : ℝ) : cuffPoint f t ∈ Θ := (f _).2

omit [T2Space S] in
theorem arcOf_subset (a b : ℝ) : arcOf f a b ⊆ Θ := by
  rintro _ ⟨t, -, rfl⟩
  exact cuffPoint_mem f t

omit [T2Space S] in
theorem cuffPoint_add_two_pi (t : ℝ) : cuffPoint f (t + 2 * Real.pi) = cuffPoint f t := by
  simp only [cuffPoint]
  rw [exp_add_two_pi]

omit [T2Space S] in
/-- Each point of `Θ` has an angle in `[a, a + 2π)`. -/
theorem exists_angle_in (a : ℝ) (x : Θ) : ∃ t ∈ Ico a (a + 2 * Real.pi), cuffPoint f t = x := by
  have hpi := Real.pi_pos
  by_cases hx : (f.symm x) = Circle.exp a
  · refine ⟨a, ⟨le_rfl, by linarith⟩, ?_⟩
    simp only [cuffPoint, ← hx]
    simp
  have hne : (Circle.exp a)⁻¹ * f.symm x ≠ 1 := fun h ↦ hx (inv_mul_eq_one.mp h).symm
  obtain ⟨s, hs0, hs1, hs⟩ := exists_angle hne
  refine ⟨a + s, ⟨by linarith, by linarith⟩, ?_⟩
  simp only [cuffPoint]
  rw [Circle.exp_add, ← hs]
  simp

end Arc

/-! ### The frame -/

section Frame

variable (par : ∀ C : cuffs S, Circle ≃ₜ C.1)

/-- The short side on a cuff. -/
noncomputable def upSide (C : cuffs S) : Set S := arcOf (par C) 0 Real.pi

/-- The long side on a cuff. -/
noncomputable def lowSide (C : cuffs S) : Set S := arcOf (par C) Real.pi (2 * Real.pi)

/-- The two points of a cuff that are vertices of the frame. -/
noncomputable def pt₀ (C : cuffs S) : S := cuffPoint (par C) 0

/-- The frame vertex at angle `π` on a cuff. -/
noncomputable def pt₁ (C : cuffs S) : S := cuffPoint (par C) Real.pi

/-- The two chosen frame vertices on each cuff, taken over all cuffs. -/
noncomputable def frameV : Set S := ⋃ C, {pt₀ par C, pt₁ par C}

omit [T2Space S] in
theorem cuff_subset_bd (C : cuffs S) : C.1 ⊆ bd S := by
  obtain ⟨C, x, -, rfl⟩ := C
  exact connectedComponentIn_subset _ _

omit [T2Space S] in
theorem cuffs_disjoint' {C C' : cuffs S} (hne : C ≠ C') : Disjoint C.1 C'.1 := by
  obtain ⟨_, x, hx, rfl⟩ := C
  obtain ⟨_, y, hy, rfl⟩ := C'
  refine disjoint_left.mpr fun z hzx hzy ↦ hne (Subtype.ext ?_)
  simp only
  rw [connectedComponentIn_eq hzx, connectedComponentIn_eq hzy]

theorem pi_lt : Real.pi < 0 + 2 * Real.pi := by linarith [Real.pi_pos]

theorem two_pi_lt : 2 * Real.pi < Real.pi + 2 * Real.pi := by linarith [Real.pi_pos]

theorem tilde_up (C : cuffs S) : tilde (upSide par C) = {pt₀ par C, pt₁ par C} :=
  tilde_arcOf (par C) Real.pi_pos pi_lt

theorem tilde_low (C : cuffs S) : tilde (lowSide par C) = {pt₁ par C, pt₀ par C} := by
  have h := tilde_arcOf (par C) (a := Real.pi) (b := 2 * Real.pi) (by linarith [Real.pi_pos])
    two_pi_lt
  have h2 : cuffPoint (par C) (2 * Real.pi) = cuffPoint (par C) 0 := by
    have := cuffPoint_add_two_pi (par C) 0
    rwa [zero_add] at this
  rw [h2] at h
  exact h

theorem pt_ne (C : cuffs S) : pt₀ par C ≠ pt₁ par C :=
  (GM20.line_facts (isLine_arcOf (par C) Real.pi_pos pi_lt)).1

theorem line_up (C : cuffs S) : IsLineWithEnds (closure (upSide par C)) (pt₀ par C) (pt₁ par C) :=
  isLine_arcOf (par C) Real.pi_pos pi_lt

theorem line_low (C : cuffs S) : IsLineWithEnds (closure (lowSide par C)) (pt₁ par C) (pt₀ par C)
  := by
  have h := isLine_arcOf (par C) (a := Real.pi) (b := 2 * Real.pi) (by linarith [Real.pi_pos])
    two_pi_lt
  have h2 : cuffPoint (par C) (2 * Real.pi) = cuffPoint (par C) 0 := by
    have := cuffPoint_add_two_pi (par C) 0
    rwa [zero_add] at this
  rw [h2] at h
  exact h

omit [T2Space S] in
theorem up_nonempty (C : cuffs S) : (upSide par C).Nonempty :=
  (isPathConnected_arcOf _ Real.pi_pos).nonempty

omit [T2Space S] in
theorem low_nonempty (C : cuffs S) : (lowSide par C).Nonempty :=
  (isPathConnected_arcOf _ (by linarith [Real.pi_pos])).nonempty

omit [T2Space S] in
theorem disjoint_up_low (C : cuffs S) : Disjoint (upSide par C) (lowSide par C) := by
  have hpi := Real.pi_pos
  refine disjoint_left.mpr ?_
  rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
  have := cuffPoint_injOn (par C) (a := 0) (b := 2 * Real.pi) (by linarith)
    ⟨hs.1.le, by linarith [hs.2]⟩ ⟨by linarith [ht.1], ht.2⟩ he.symm
  linarith [hs.2, ht.1]

/-- The sides of the frame. -/
noncomputable def sidePieces : Set (Set S) := range (upSide par) ∪ range (lowSide par)

omit [T2Space S] in
theorem sidePieces_mem_cases {s : Set S} (hs : s ∈ sidePieces par) :
    ∃ C : cuffs S, s ⊆ C.1 ∧ s.Nonempty ∧ (s = upSide par C ∨ s = lowSide par C) := by
  rcases hs with ⟨C, rfl⟩ | ⟨C, rfl⟩
  · exact ⟨C, arcOf_subset _ _ _, up_nonempty par C, Or.inl rfl⟩
  · exact ⟨C, arcOf_subset _ _ _, low_nonempty par C, Or.inr rfl⟩

theorem sides_eq (hS : IsSurface S) : arcComponentsIn (bd S \ frameV par) = sidePieces par := by
  have hpi := Real.pi_pos
  have hfin : Finite (cuffs S) := (cuff_statement S hS).2.1.to_subtype
  have hVt : ∀ C : cuffs S, pt₀ par C ∈ frameV par ∧ pt₁ par C ∈ frameV par := fun C ↦
    ⟨mem_iUnion.2 ⟨C, Or.inl rfl⟩, mem_iUnion.2 ⟨C, Or.inr rfl⟩⟩
  refine arcComponentsIn_of_pieces ((finite_range _).union (finite_range _)) ?_ ?_ ?_ ?_
  · rintro s (⟨C, rfl⟩ | ⟨C, rfl⟩)
    · exact isPathConnected_arcOf _ hpi
    · exact isPathConnected_arcOf _ (by linarith)
  · intro s hs t ht hne
    obtain ⟨C, hsC, -, hs'⟩ := sidePieces_mem_cases par hs
    obtain ⟨C', htC, -, ht'⟩ := sidePieces_mem_cases par ht
    by_cases hCC : C = C'
    · subst hCC
      rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl
      · exact absurd rfl hne
      · exact disjoint_up_low par C
      · exact (disjoint_up_low par C).symm
      · exact absurd rfl hne
    · exact (cuffs_disjoint' hCC).mono hsC htC
  · rintro s (⟨C, rfl⟩ | ⟨C, rfl⟩) x ⟨hx, hxW⟩
    · by_contra hn
      have : x ∈ tilde (upSide par C) := ⟨hx, hn⟩
      rw [tilde_up] at this
      rcases this with rfl | rfl
      · exact hxW.2 (hVt C).1
      · exact hxW.2 (hVt C).2
    · by_contra hn
      have : x ∈ tilde (lowSide par C) := ⟨hx, hn⟩
      rw [tilde_low] at this
      rcases this with rfl | rfl
      · exact hxW.2 (hVt C).2
      · exact hxW.2 (hVt C).1
  · ext x
    constructor
    · rintro ⟨hx, hxV⟩
      let C : cuffs S := ⟨_, x, hx, rfl⟩
      have hxC : x ∈ C.1 := mem_connectedComponentIn hx
      obtain ⟨t, ht, he⟩ := exists_angle_in (par C) 0 ⟨x, hxC⟩
      have he' : cuffPoint (par C) t = x := he
      rcases eq_or_lt_of_le ht.1 with rfl | h0
      · exact absurd (he' ▸ (hVt C).1) hxV
      rcases lt_trichotomy t Real.pi with h1 | rfl | h1
      · exact ⟨_, Or.inl ⟨C, rfl⟩, t, ⟨h0, h1⟩, he'⟩
      · exact absurd (he' ▸ (hVt C).2) hxV
      · exact ⟨_, Or.inr ⟨C, rfl⟩, t, ⟨h1, by linarith [ht.2]⟩, he'⟩
    · rintro ⟨s, hs, hx⟩
      obtain ⟨C, hsC, -, hs'⟩ := sidePieces_mem_cases par hs
      refine ⟨cuff_subset_bd C (hsC hx), fun hxV ↦ ?_⟩
      obtain ⟨C', hC'⟩ := mem_iUnion.mp hxV
      have hxC' : x ∈ C'.1 := by
        rcases hC' with rfl | rfl <;> exact cuffPoint_mem _ _
      by_cases hCC : C = C'
      · subst hCC
        rcases hs' with rfl | rfl
        · have : x ∉ tilde (upSide par C) := fun h ↦ h.2 hx
          rw [tilde_up] at this
          exact this hC'
        · have : x ∉ tilde (lowSide par C) := fun h ↦ h.2 hx
          rw [tilde_low] at this
          rcases hC' with h | h
          · exact this (Or.inr h)
          · exact this (Or.inl h)
      · exact disjoint_left.mp (cuffs_disjoint' hCC) (hsC hx) hxC'

omit [T2Space S] in
theorem up_injective : Function.Injective (upSide par) := fun C C' he ↦ by
  by_contra hne
  obtain ⟨x, hx⟩ := up_nonempty par C
  exact disjoint_left.mp (cuffs_disjoint' hne) (arcOf_subset _ _ _ hx)
    (arcOf_subset _ _ _ (he ▸ hx))

omit [T2Space S] in
theorem low_injective : Function.Injective (lowSide par) := fun C C' he ↦ by
  by_contra hne
  obtain ⟨x, hx⟩ := low_nonempty par C
  exact disjoint_left.mp (cuffs_disjoint' hne) (arcOf_subset _ _ _ hx)
    (arcOf_subset _ _ _ (he ▸ hx))

omit [T2Space S] in
theorem up_ne_low (C C' : cuffs S) : upSide par C ≠ lowSide par C' := fun he ↦ by
  by_cases hCC : C = C'
  · subst hCC
    obtain ⟨x, hx⟩ := up_nonempty par C
    exact disjoint_left.mp (disjoint_up_low par C) hx (he ▸ hx)
  · obtain ⟨x, hx⟩ := up_nonempty par C
    exact disjoint_left.mp (cuffs_disjoint' hCC) (arcOf_subset _ _ _ hx)
      (arcOf_subset _ _ _ (he ▸ hx))

/-- The direction of each side of the frame. -/
noncomputable def sideγ (s : Set S) : List S :=
  open Classical in
  if h : ∃ C, upSide par C = s then [pt₀ par h.choose, pt₁ par h.choose]
  else if h : ∃ C, lowSide par C = s then [pt₁ par h.choose, pt₀ par h.choose]
  else []

omit [T2Space S] in
theorem sideγ_up (C : cuffs S) : sideγ par (upSide par C) = [pt₀ par C, pt₁ par C] := by
  have h : ∃ C', upSide par C' = upSide par C := ⟨C, rfl⟩
  rw [sideγ, dite_eq_left h, up_injective par h.choose_spec]

omit [T2Space S] in
theorem sideγ_low (C : cuffs S) : sideγ par (lowSide par C) = [pt₁ par C, pt₀ par C] := by
  have h₁ : ¬ ∃ C', upSide par C' = lowSide par C := fun ⟨C', h⟩ ↦ up_ne_low par C' C h
  have h : ∃ C', lowSide par C' = lowSide par C := ⟨C, rfl⟩
  rw [sideγ, dite_eq_right h₁, dite_eq_left h, low_injective par h.choose_spec]

theorem side_line {s : Set S} (hs : s ∈ sidePieces par) :
    ∃ x y, x ≠ y ∧ sideγ par s = [x, y] ∧ tilde s = {x, y} ∧ IsLineWithEnds (closure s) x y := by
  rcases hs with ⟨C, rfl⟩ | ⟨C, rfl⟩
  · exact ⟨_, _, pt_ne par C, sideγ_up par C, tilde_up par C, line_up par C⟩
  · exact ⟨_, _, (pt_ne par C).symm, sideγ_low par C, tilde_low par C, line_low par C⟩

/-- The frame in the proof of (2.1). -/
noncomputable def stdFrame (hS : IsSurface S) : Frame S where
  V := frameV par
  γ := sideγ par
  isLong s := s ∈ range (lowSide par)
  V_subset := by
    refine iUnion_subset fun C x hx ↦ ?_
    rcases hx with rfl | rfl <;> exact cuff_subset_bd C (cuffPoint_mem _ _)
  finite_V := by
    have : Finite (cuffs S) := (cuff_statement S hS).2.1.to_subtype
    exact finite_iUnion fun C ↦ (finite_singleton _).insert _
  finite_sides := by
    have : Finite (cuffs S) := (cuff_statement S hS).2.1.to_subtype
    rw [sides_eq par hS]
    exact (finite_range _).union (finite_range _)
  side_shape := by
    rw [sides_eq par hS]
    intro s hs
    obtain ⟨x, y, hxy, -, ht, hL⟩ := side_line par hs
    obtain ⟨f, hf⟩ := id hL
    exact ⟨by rw [ht, ncard_pair hxy], by rw [ht]; exact (finite_singleton y).insert x, ⟨f⟩,
      by rw [ht]; exact (GM20.line_facts hL).2.2.2⟩
  γ_nodup := by
    rw [sides_eq par hS]
    intro s hs
    obtain ⟨x, y, hxy, hγ, -, -⟩ := side_line par hs
    rw [hγ]
    simpa using hxy
  γ_set := by
    rw [sides_eq par hS]
    intro s hs
    obtain ⟨x, y, hxy, hγ, ht, -⟩ := side_line par hs
    rw [hγ, ht]
    ext z
    simp
  long_disjoint := by
    rw [sides_eq par hS]
    rintro _ - _ - hne ⟨C, rfl⟩ ⟨C', rfl⟩
    have hCC : C ≠ C' := fun h ↦ hne (by rw [h])
    rw [tilde_low, tilde_low]
    refine (cuffs_disjoint' hCC).mono ?_ ?_
    · rintro _ (rfl | rfl) <;> exact cuffPoint_mem _ _
    · rintro _ (rfl | rfl) <;> exact cuffPoint_mem _ _

theorem stdFrame_short (hS : IsSurface S) {t : Set S} (ht : t ∈ (stdFrame par hS).shortSides) :
    ∃ C, t = upSide par C := by
  obtain ⟨hs, hl⟩ := ht
  change t ∈ arcComponentsIn (bd S \ frameV par) at hs
  rw [sides_eq par hS] at hs
  rcases hs with ⟨C, rfl⟩ | h
  · exact ⟨C, rfl⟩
  · exact absurd h hl

/-- Either order of the ends of a line in a side agrees with the direction of the side. -/
theorem dirAgrees_or (hS : IsSurface S) {s e : Set S} (hs : s ∈ (stdFrame par hS).sides) {x y : S}
    (hxy : x ≠ y) (hes : e ⊆ s) (hx : x ∈ closure s) (hy : y ∈ closure s) :
    DirAgrees s ((stdFrame par hS).γ s) e [x, y] ∨ DirAgrees s ((stdFrame par hS).γ s) e [y, x]
      := by
  change s ∈ arcComponentsIn (bd S \ frameV par) at hs
  rw [sides_eq par hS] at hs
  obtain ⟨u, v, -, hγ, -, f, hf0, hf1⟩ := side_line par hs
  change Set.Icc (0 : ℝ) 1 ≃ₜ closure s at f
  have hG : (stdFrame par hS).γ s = [u, v] := hγ
  rw [hG]
  let a := f.symm ⟨x, hx⟩
  let b := f.symm ⟨y, hy⟩
  have hfa : (f a).1 = x := by simp [a]
  have hfb : (f b).1 = y := by simp [b]
  have hne : a ≠ b := fun h ↦ hxy (by rw [← hfa, ← hfb, h])
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl ⟨f, a, b, h, hes, by simpa using hf0.symm, by simpa using hf1.symm,
      by simpa using hfa.symm, by simpa using hfb.symm⟩
  · exact Or.inr ⟨f, b, a, h, hes, by simpa using hf0.symm, by simpa using hf1.symm,
      by simpa using hfb.symm, by simpa using hfa.symm⟩

end Frame

end GraphMinor.GM19
