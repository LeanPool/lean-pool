/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.CuffPieces

/-!
# Directions along a cuff

A side of a frame on a cuff, and a border edge inside it, are both open arcs of the cuff. If we read
both
in the same sense, then the direction of the edge agrees with the direction of the side, in the
sense of
`DirAgrees`. This file proves that, for either sense, and that an arc inside an arc can be shifted
by a
multiple of `2π` to have its angles between those of the larger arc.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S] {Θ : Set S} (f : Circle ≃ₜ Θ)

omit [T2Space S] in
/-- If an open arc lies in an open arc whose two ends are not on it, then a shift by a multiple of
`2π` puts
the angles of the first between those of the second. -/
theorem exists_shift {a b a' b' : ℝ} (hab : a < b) (hab' : a' < b') (hub : b < a + 2 * Real.pi)
    (hsub : arcOf f a' b' ⊆ arcOf f a b) :
    ∃ m : ℤ, a ≤ a' + m * (2 * Real.pi) ∧ b' + m * (2 * Real.pi) ≤ b := by
  have hpi := Real.pi_pos
  have hmid : cuffPoint f ((a' + b') / 2) ∈ arcOf f a b :=
    hsub ⟨_, ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨s, hs, hse⟩ := hmid
  obtain ⟨m, hm⟩ := cuffPoint_eq f hse
  have hnot : ∀ {r : ℝ}, r ∈ Ioo a' b' → ∀ k : ℤ, r + k * (2 * Real.pi) ≠ a ∧
      r + k * (2 * Real.pi) ≠ b := by
    intro r hr k
    have hrm : cuffPoint f r ∈ arcOf f a b := hsub ⟨r, hr, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hrm
    have hpt : ∀ c, r + k * (2 * Real.pi) = c → cuffPoint f q = cuffPoint f c := by
      intro c hc
      rw [hqe, ← hc, cuffPoint_shift]
    have hi := fun c (hc : c ∈ Ico a (a + 2 * Real.pi)) (he : cuffPoint f q = cuffPoint f c) ↦
      cuffPoint_injOn f le_rfl ⟨hq.1.le, by linarith [hq.2]⟩ hc he
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have := hi a ⟨le_rfl, by linarith⟩ (hpt a h)
      linarith [hq.1]
    · have := hi b ⟨hab.le, hub⟩ (hpt b h)
      linarith [hq.2]
  refine ⟨m, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    refine (hnot (r := a - m * (2 * Real.pi)) ⟨by linarith, by linarith [hs.1]⟩ m).1 (by ring)
  · by_contra hn
    push Not at hn
    refine (hnot (r := b - m * (2 * Real.pi)) ⟨by linarith [hs.2], by linarith⟩ m).2 (by ring)

/-- A continuous reading of the interval `[a, b]` by the unit interval gives a homeomorphism onto
the
closed arc. -/
theorem exists_homeo_arc {a b : ℝ} (hab : a < b) (hub : b < a + 2 * Real.pi) {m : unitInterval → ℝ}
    (hm : Continuous m) (hbij : BijOn m univ (Icc a b)) :
    ∃ g : unitInterval ≃ₜ closure (arcOf f a b), ∀ t, (g t).1 = cuffPoint f (m t) := by
  have hcl := closure_arcOf f hab
  have hmem : ∀ t, cuffPoint f (m t) ∈ closure (arcOf f a b) := fun t ↦ by
    rw [hcl]
    exact mem_image_of_mem _ (hbij.mapsTo (mem_univ t))
  let ι : unitInterval → closure (arcOf f a b) := fun t ↦ ⟨cuffPoint f (m t), hmem t⟩
  have hc : Continuous ι := ((continuous_cuffPoint f).comp hm).subtype_mk _
  have hb : Function.Bijective ι := by
    constructor
    · intro s t hst
      have h : (ι s).1 = (ι t).1 := by rw [hst]
      exact hbij.injOn (mem_univ _) (mem_univ _) (cuffPoint_injOn_Icc f hub
        (hbij.mapsTo (mem_univ s)) (hbij.mapsTo (mem_univ t)) h)
    · rintro ⟨y, hy⟩
      rw [hcl] at hy
      obtain ⟨c, hc', rfl⟩ := hy
      obtain ⟨t, -, rfl⟩ := hbij.surjOn hc'
      exact ⟨t, rfl⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective ι hb) hc, fun _ ↦ rfl⟩

omit [T2Space S] in
theorem arcOf_mono {a b a' b' : ℝ} (h₁ : a ≤ a') (h₂ : b' ≤ b) : arcOf f a' b' ⊆ arcOf f a b :=
  image_mono (Ioo_subset_Ioo h₁ h₂)

/-- Reading the cuff forward: the direction of a sub-arc agrees with that of the arc. -/
theorem dirAgrees_forward {a b a' b' : ℝ} (hub : b < a + 2 * Real.pi) (h₁ : a ≤ a') (h₂ : a' < b')
    (h₃ : b' ≤ b) :
    DirAgrees (arcOf f a b) [cuffPoint f a, cuffPoint f b] (arcOf f a' b')
      [cuffPoint f a', cuffPoint f b'] := by
  have hab : a < b := by linarith
  have hl : 0 < b - a := by linarith
  let m : unitInterval → ℝ := fun t ↦ a + t * (b - a)
  have hm : Continuous m := by fun_prop
  have hbij : BijOn m univ (Icc a b) := by
    refine ⟨fun t _ ↦ ?_, fun s _ t _ h ↦ ?_, fun c hc ↦ ?_⟩
    · have h0 := t.2.1
      have h1 := t.2.2
      exact ⟨by nlinarith, by nlinarith⟩
    · have h' : (s : ℝ) * (b - a) = t * (b - a) := by
        have : a + (s : ℝ) * (b - a) = a + t * (b - a) := h
        linarith
      exact Subtype.ext (mul_right_cancel₀ hl.ne' h')
    · refine ⟨⟨(c - a) / (b - a), div_nonneg (by linarith [hc.1]) hl.le,
        (div_le_one hl).mpr (by linarith [hc.2])⟩, mem_univ _, ?_⟩
      change a + (c - a) / (b - a) * (b - a) = c
      field_simp
      ring
  obtain ⟨g, hg⟩ := exists_homeo_arc f hab hub hm hbij
  have hval : ∀ x (hx : x ∈ Icc a b), ∃ t : unitInterval, m t = x := fun x hx ↦ by
    obtain ⟨t, -, ht⟩ := hbij.surjOn hx
    exact ⟨t, ht⟩
  obtain ⟨t₁, ht₁⟩ := hval a' ⟨h₁, by linarith⟩
  obtain ⟨t₂, ht₂⟩ := hval b' ⟨by linarith, h₃⟩
  refine ⟨g, t₁, t₂, ?_, arcOf_mono f h₁ h₃, ?_, ?_, ?_, ?_⟩
  · have hlt : m t₁ < m t₂ := by rw [ht₁, ht₂]; exact h₂
    have : (t₁ : ℝ) < t₂ := by
      by_contra hn
      have hle : (t₂ : ℝ) ≤ t₁ := not_lt.mp hn
      have : (t₂ : ℝ) * (b - a) ≤ t₁ * (b - a) := mul_le_mul_of_nonneg_right hle hl.le
      change a + (t₁ : ℝ) * (b - a) < a + t₂ * (b - a) at hlt
      linarith
    exact this
  · simp only [List.head?_cons, hg]
    simp [m]
  · simp only [List.getLast?_cons_cons, List.getLast?_singleton, hg]
    simp [m]
  · simp only [List.head?_cons, hg, ht₁]
  · simp only [List.getLast?_cons_cons, List.getLast?_singleton, hg, ht₂]

/-- Reading the cuff backward: the direction of a sub-arc agrees with that of the arc. -/
theorem dirAgrees_backward {a b a' b' : ℝ} (hub : b < a + 2 * Real.pi) (h₁ : a ≤ a') (h₂ : a' < b')
    (h₃ : b' ≤ b) :
    DirAgrees (arcOf f a b) [cuffPoint f b, cuffPoint f a] (arcOf f a' b')
      [cuffPoint f b', cuffPoint f a'] := by
  have hab : a < b := by linarith
  have hl : 0 < b - a := by linarith
  let m : unitInterval → ℝ := fun t ↦ b - t * (b - a)
  have hm : Continuous m := by fun_prop
  have hbij : BijOn m univ (Icc a b) := by
    refine ⟨fun t _ ↦ ?_, fun s _ t _ h ↦ ?_, fun c hc ↦ ?_⟩
    · have h0 := t.2.1
      have h1 := t.2.2
      exact ⟨by nlinarith, by nlinarith⟩
    · have h' : (s : ℝ) * (b - a) = t * (b - a) := by
        have : b - (s : ℝ) * (b - a) = b - t * (b - a) := h
        linarith
      exact Subtype.ext (mul_right_cancel₀ hl.ne' h')
    · refine ⟨⟨(b - c) / (b - a), div_nonneg (by linarith [hc.2]) hl.le,
        (div_le_one hl).mpr (by linarith [hc.1])⟩, mem_univ _, ?_⟩
      change b - (b - c) / (b - a) * (b - a) = c
      field_simp
      ring
  obtain ⟨g, hg⟩ := exists_homeo_arc f hab hub hm hbij
  have hval : ∀ x (hx : x ∈ Icc a b), ∃ t : unitInterval, m t = x := fun x hx ↦ by
    obtain ⟨t, -, ht⟩ := hbij.surjOn hx
    exact ⟨t, ht⟩
  obtain ⟨t₁, ht₁⟩ := hval b' ⟨by linarith, h₃⟩
  obtain ⟨t₂, ht₂⟩ := hval a' ⟨h₁, by linarith⟩
  refine ⟨g, t₁, t₂, ?_, arcOf_mono f h₁ h₃, ?_, ?_, ?_, ?_⟩
  · have hlt : m t₂ < m t₁ := by rw [ht₁, ht₂]; exact h₂
    have : (t₁ : ℝ) < t₂ := by
      by_contra hn
      have hle : (t₂ : ℝ) ≤ t₁ := not_lt.mp hn
      have : (t₂ : ℝ) * (b - a) ≤ t₁ * (b - a) := mul_le_mul_of_nonneg_right hle hl.le
      change b - (t₂ : ℝ) * (b - a) < b - t₁ * (b - a) at hlt
      linarith
    exact this
  · simp only [List.head?_cons, hg]
    simp [m]
  · simp only [List.getLast?_cons_cons, List.getLast?_singleton, hg]
    simp [m]
  · simp only [List.head?_cons, hg, ht₁]
  · simp only [List.getLast?_cons_cons, List.getLast?_singleton, hg, ht₂]

end GraphMinor.GM19
