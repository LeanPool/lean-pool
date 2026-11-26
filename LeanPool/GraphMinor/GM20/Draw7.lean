/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Draw6

/-!
# Drawing a graph in a surface of large genus: fans

To the left of a set of disjoint curves there is a strip free of circles. In this strip straight
segments join the left ends of the curves to points on a vertical line, one point for each vertex.
If
the heights of these points increase with the heights of the left ends, then the segments meet only
at
the points on the vertical line.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface

variable {a b c : ℕ}

/-- Disjoint curves with left ends sorted by height extend to a common vertical line on the left. -/
theorem exists_fans [T2Space (SurfaceModel a b c)] {n : ℕ} {π : Equiv.Perm (Fin n)} {m₀ : ℤ}
    {r : ℝ} (hr : 3 * (m₀ : ℝ) + 3 / 2 < r) (hS : Slab a b c n (3 * (m₀ : ℝ) + 3 / 2) r π)
    {h : Fin n → ℝ} (hh : Monotone h) :
    ∃ A : Fin n → Set (SurfaceModel a b c),
      (∀ p, IsLineWithEnds (A p) (qq a b c (3 * (m₀ : ℝ) + 5 / 4, h p)) (qq a b c (r, π p))) ∧
      (∀ p p', p ≠ p' → ∀ w ∈ A p, w ∈ A p' →
        w = qq a b c (3 * (m₀ : ℝ) + 5 / 4, h p) ∧ h p = h p') ∧
      (∀ p y, qq a b c (3 * (m₀ : ℝ) + 5 / 4, y) ∈ A p → y = h p) ∧
      (∀ p z, Ok a b c z → r ≤ z.1 → qq a b c z ∈ A p → qq a b c z = qq a b c (r, π p)) := by
  obtain ⟨P, hP, hPd, hPz, hPl, hPr⟩ := hS
  set X : ℝ := 3 * (m₀ : ℝ) + 5 / 4 with hX
  set Y : ℝ := 3 * (m₀ : ℝ) + 3 / 2 with hY
  let S : Fin n → Set (ℝ × ℝ) := fun p ↦ sg (X, h p) (Y, ((p : ℕ) : ℝ))
  have hseg := fun p : Fin n ↦ isLine_sg (a := a) (b := b) (c := c) m₀ (z := (X, h p))
    (z' := (Y, ((p : ℕ) : ℝ))) (by simp only [hX]; linarith) (by simp only [hX]; linarith)
    (by simp only [hY]; linarith) (by simp only [hY]; linarith)
    (fun he ↦ by
      have := congrArg Prod.fst he
      simp only [hX, hY] at this
      linarith)
  have hcl : ∀ p, ∀ z ∈ S p, Clear a b c z := fun p ↦ (hseg p).2
  have hfst : ∀ p, ∀ z ∈ S p, X ≤ z.1 ∧ z.1 ≤ Y := fun p z hz ↦
    sg_fst hz le_rfl (by simp only [hX, hY]; linarith) (by simp only [hX, hY]; linarith) le_rfl
  have hright : ∀ p, ∀ z ∈ S p, z.1 = Y → z.2 = ((p : ℕ) : ℝ) := by
    rintro p _ ⟨s, hs, rfl⟩ h₁
    simp only at h₁ ⊢
    have h₂ : (1 - s) * (Y - X) = 0 := by linarith
    have h₃ : 1 - s = 0 := (mul_eq_zero.mp h₂).resolve_right (by simp only [hX, hY]; linarith)
    have h₄ : s = 1 := by linarith
    subst h₄
    simp
  have hleft : ∀ p, ∀ z ∈ S p, z.1 = X → z.2 = h p := by
    rintro p _ ⟨s, hs, rfl⟩ h₁
    simp only at h₁ ⊢
    have h₂ : s * (Y - X) = 0 := by linarith
    have h₃ : s = 0 := (mul_eq_zero.mp h₂).resolve_right (by simp only [hX, hY]; linarith)
    subst h₃
    simp
  have hsegs : ∀ p p', p < p' → ∀ z ∈ S p, z ∈ S p' → z = (X, h p) ∧ h p = h p' := by
    rintro p p' hlt _ ⟨s, hs, rfl⟩ ⟨s', hs', heq⟩
    obtain ⟨h₁, h₂⟩ := Prod.ext_iff.mp heq
    simp only at h₁ h₂
    have h₃ : (s' - s) * (Y - X) = 0 := by linarith
    have h₄ : s' - s = 0 := (mul_eq_zero.mp h₃).resolve_right (by simp only [hX, hY]; linarith)
    have h₅ : s' = s := by linarith
    subst h₅
    have h₆ : ((p : ℕ) : ℝ) + 1 ≤ ((p' : ℕ) : ℝ) := by exact_mod_cast hlt
    have h₇ : h p ≤ h p' := hh hlt.le
    have h₈ := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h₇)
    have h₉ : s' * (((p' : ℕ) : ℝ) - p) + (1 - s') * (h p' - h p) = 0 := by linarith
    have h₁₀ : s' * ((p' : ℕ) - p : ℝ) ≥ 0 := mul_nonneg hs.1 (by linarith)
    have h₁₁ : s' * ((p' : ℕ) - p : ℝ) = 0 := by linarith
    have h₁₂ : s' = 0 := (mul_eq_zero.mp h₁₁).resolve_right (by linarith)
    subst h₁₂
    exact ⟨by simp, (by simpa using h₂ : h p' = h p).symm⟩
  have hsegP : ∀ p p', ∀ z ∈ S p, qq a b c z ∈ P p' → p = p' := by
    intro p p' z hz hzP
    have h₁ := hPl p' z (hcl p z hz).ok (hfst p z hz).2 hzP
    have h₂ : Ok a b c (Y, (((p' : ℕ) : ℝ))) :=
      (clear_of_gap m₀ (by simp only [hY]; linarith) (by simp only [hY]; linarith)).ok
    have h₃ := eq_of_qq_eq (hcl p z hz) h₂ h₁
    have h₄ := hright p z hz (by rw [h₃])
    rw [h₃] at h₄
    simp only at h₄
    exact (Fin.ext (by exact_mod_cast h₄)).symm
  refine ⟨fun p ↦ qq a b c '' S p ∪ P p, ?_, ?_, ?_, ?_⟩
  · intro p
    refine GM11.IsLineWithEnds.union (GM11.IsLineWithEnds.symm (hseg p).1) (hP p) ?_
    ext w
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzP⟩
      exact hPl p z (hcl p z hz).ok (hfst p z hz).2 hzP
    · rintro rfl
      exact ⟨(mem_of_line (hseg p).1).2, (mem_of_line (hP p)).1⟩
  · intro p p' hne w hw hw'
    rcases hw with ⟨z, hz, rfl⟩ | hw
    · rcases hw' with ⟨z', hz', heq⟩ | hw'
      · have h₁ := eq_of_qq_eq (hcl p' z' hz') (hcl p z hz).ok heq
        subst h₁
        rcases lt_or_gt_of_ne hne with h₂ | h₂
        · obtain ⟨h₃, h₄⟩ := hsegs p p' h₂ z' hz hz'
          exact ⟨by rw [h₃], h₄⟩
        · obtain ⟨h₃, h₄⟩ := hsegs p' p h₂ z' hz' hz
          exact ⟨by rw [h₃, h₄], h₄.symm⟩
      · exact absurd (hsegP p p' z hz hw') hne
    · rcases hw' with ⟨z', hz', rfl⟩ | hw'
      · exact absurd (hsegP p' p z' hz' hw) hne.symm
      · exact absurd hw' (Set.disjoint_left.mp (hPd hne) hw)
  · rintro p y (⟨z, hz, heq⟩ | hw)
    · have h₁ := eq_of_qq_eq (hcl p z hz)
        (clear_of_gap (y := y) m₀ (by simp only [hX]; linarith)
          (by simp only [hX]; linarith)).ok heq
      have h₂ := hleft p z hz (by rw [h₁])
      rw [h₁] at h₂
      exact h₂
    · obtain ⟨z, ⟨_, h₂, _⟩, heq⟩ := hPz p hw
      have h₃ := eq_of_qq_eq (clear_of_gap (y := y) (a := a) (b := b) (c := c) m₀
        (by simp only [hX]; linarith) (by simp only [hX]; linarith)) (by assumption) heq.symm
      have h₄ := congrArg Prod.fst h₃
      simp only at h₄
      simp only [hX] at h₄
      linarith
  · rintro p z hz hzr (⟨z', hz', heq⟩ | hw)
    · have h₁ := eq_of_qq_eq (hcl p z' hz') hz heq
      subst h₁
      have := (hfst p z' hz').2
      linarith
    · exact hPr p z hz hzr hw

end GraphMinor.GM20.Draw
