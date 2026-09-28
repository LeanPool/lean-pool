/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
/-!
# Moving sofa: related mathematical developments

* `Geometry.Convex.HorizontalExtrema`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Convex / Horizontal Extrema
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A horizontal extreme slice is a singleton when every defining normal has nonzero sine. -/
lemma ConvexBody.eq_of_mem_of_fst_eq_of_fst_extremal
    (K : ConvexBody Point) (N : Set Real.Angle) (hN : N.Finite)
    (hK : HasHalfPlaneRepresentation K N) (hsin : ∀ t ∈ N, t.sin ≠ 0)
    {a b : Point} (ha : a ∈ (K : Set Point)) (hb : b ∈ (K : Set Point))
    (hab : a 0 = b 0)
    (hext : (∀ q ∈ (K : Set Point), q 0 ≤ a 0) ∨
      (∀ q ∈ (K : Set Point), a 0 ≤ q 0)) : a = b := by
  by_contra hne
  have hy : a 1 ≠ b 1 := by
    intro h
    apply hne
    ext i
    fin_cases i
    · exact hab
    · exact h
  let m : Point := (2 : ℝ)⁻¹ • (a + b)
  let U : Set Point := ⋂ t ∈ N,
    {q | inner ℝ q (normalVector t) < supportValue K t}
  have hU : IsOpen U := by
    apply hN.isOpen_biInter
    intro t ht
    exact isOpen_lt (by fun_prop) continuous_const
  have hm : m ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_ofPred_eq]
    intro t ht
    have ha' := inner_le_supportValue K ha t
    have hb' := inner_le_supportValue K hb t
    have hneq : inner ℝ a (normalVector t) ≠ inner ℝ b (normalVector t) := by
      intro heq
      have hdiff : t.sin * (a 1 - b 1) = 0 := by
        simp only [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at heq
        simp at heq
        rw [hab] at heq
        nlinarith
      exact hy (sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (hsin t ht)))
    have hmid : inner ℝ m (normalVector t) =
        (inner ℝ a (normalVector t) + inner ℝ b (normalVector t)) / 2 := by
      simp only [m, inner_add_left, real_inner_smul_left]
      ring
    rw [hmid]
    rcases lt_or_gt_of_ne hneq with h | h <;> linarith
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hU) m hm
  have hmem (r : ℝ) (hr : |r| < ε) :
      m + r • normalVector (0 : Real.Angle) ∈ (K : Set Point) := by
    have hqm : m + r • normalVector (0 : Real.Angle) ∈ Metric.ball m ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul]
      have hn : ‖normalVector (0 : Real.Angle)‖ = 1 := by
        simpa only [Real.Angle.coe_zero] using norm_normalVector_real 0
      simpa only [hn, mul_one, Real.norm_eq_abs] using hr
    rw [hK.eq_iInter_supportValue]
    simp only [Set.mem_iInter]
    intro t ht
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp (hball hqm) t) ht
    change inner ℝ (m + r • normalVector (0 : Real.Angle)) (normalVector t) <
      supportValue K t at h
    exact h.le
  have hcoord (r : ℝ) : (m + r • normalVector (0 : Real.Angle)) 0 = a 0 + r := by
    simp [m, normalVector, frame, ← hab]
    ring
  rcases hext with hmax | hmin
  · have hq := hmem (ε / 2) (by rw [abs_of_pos (half_pos hε)]; linarith)
    have h := hmax _ hq
    rw [hcoord] at h
    linarith
  · have hq := hmem (-ε / 2) (by rw [abs_of_neg (by linarith : -ε / 2 < 0)]; linarith)
    have h := hmin _ hq
    rw [hcoord] at h
    linarith

/-- Every horizontal coordinate between two points of a convex body is attained. -/
lemma ConvexBody.exists_mem_fst_eq_of_mem_Icc (K : ConvexBody Point) {a b : Point}
    (ha : a ∈ (K : Set Point)) (hb : b ∈ (K : Set Point)) (hab : a 0 < b 0)
    {x : ℝ} (hx : x ∈ Set.Icc (a 0) (b 0)) :
    ∃ q ∈ (K : Set Point), q 0 = x := by
  let r := (x - a 0) / (b 0 - a 0)
  have hd : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one hd]
    linarith [hx.2]
  refine ⟨(1 - r) • a + r • b,
    K.convex ha hb (sub_nonneg.mpr hr1) hr (by ring), ?_⟩
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  dsimp [r]
  field_simp
  ring

end MovingSofa

end

end

end
