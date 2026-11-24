/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Lunes
public import LeanPool.GraphMinor.Surface.CircleMove
import LeanPool.GraphMinor.Surface.Crossing

/-!
# Alternating circle ports force a chord crossing

For the crossing drawing of XII (4.5), page 253, put the ends of
one chord at angles minus delta and delta. The other chord has one
end between them and one outside that arc. Cosine puts these ends
on opposite sides of the vertical line through the first ends.
The crossing lemma for the unit disc then gives an intersection.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- A normalized pair of chords with alternating circle ends
intersects. This is the crossing test used in XII (4.5), page 253. -/
theorem alternating_unit_chords_inter
    {δ β γ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (hβ : |β| < δ) (hγ : δ < γ) (hγ' : γ < 2 * Real.pi - δ) :
    (segment ℝ (eC (-δ)) (eC δ) ∩ segment ℝ (eC β) (eC γ)).Nonempty := by
  have hcomp : IsCompact (segment ℝ (eC (-δ)) (eC δ)) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (AffineMap.lineMap_continuous (p := eC (-δ)) (q := eC δ))
  have hball : ∀ t : ℝ, eC t ∈ closedBall (0 : ℂ) 1 := by
    intro t
    simp [norm_eC]
  have hline : ∀ z : ℂ, ‖z‖ = 1 → z.re = Real.cos δ →
      z = eC (-δ) ∨ z = eC δ := by
    intro z hz hre
    have hsq : z.im * z.im = Real.sin δ * Real.sin δ := by
      have h1 := Complex.sq_norm z
      rw [Complex.normSq_apply, hz, hre] at h1
      have h2 := Real.sin_sq_add_cos_sq δ
      nlinarith
    have hfac : (z.im - Real.sin δ) * (z.im + Real.sin δ) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · right
      apply Complex.ext
      · simpa only [eC_re] using hre
      · rw [eC_im]
        linarith
    · left
      apply Complex.ext
      · simpa only [eC_re, Real.cos_neg] using hre
      · rw [eC_im, Real.sin_neg]
        linarith
  apply crossing_of_vertical_line hcomp
    (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected
    ((convex_closedBall (0 : ℂ) 1).segment_subset (hball _) (hball _))
    ((convex_closedBall (0 : ℂ) 1).segment_subset (hball _) (hball _))
    (left_mem_segment _ _ _) (right_mem_segment _ _ _)
    (left_mem_segment _ _ _) (right_mem_segment _ _ _)
    (norm_eC _) (norm_eC _) hline
  · rw [eC_re]
    exact (cos_arc hδ hδπ).2.1 hβ
  · rw [eC_re]
    exact (cos_arc hδ hδπ).2.2.2 hγ hγ'

private theorem eC_mul (a b : ℝ) : eC a * eC b = eC (a + b) := by
  change ((Circle.exp a * Circle.exp b : Circle) : ℂ) = (Circle.exp (a + b) : ℂ)
  rw [Circle.exp_add]

private theorem mul_mem_segment (m : ℂ) {a b x : ℂ} (hx : x ∈ segment ℝ a b) :
    m * x ∈ segment ℝ (m * a) (m * b) := by
  obtain ⟨r, s, hr, hs, hrs, rfl⟩ := hx
  refine ⟨r, s, hr, hs, hrs, ?_⟩
  simp only [mul_add, mul_smul_comm]

/-- Chords whose four circle ends alternate in a full turn
intersect. This is the unnormalized crossing test for XII (4.5),
page 253. -/
theorem ordered_unit_chords_inter {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d < a + 2 * Real.pi) :
    (segment ℝ (eC a) (eC c) ∩ segment ℝ (eC b) (eC d)).Nonempty := by
  let μ := (a + c) / 2
  let δ := (c - a) / 2
  obtain ⟨x, hx, hx'⟩ := alternating_unit_chords_inter
    (δ := δ) (β := b - μ) (γ := d - μ)
    (by dsimp [δ]; linarith)
    (by dsimp [δ]; linarith)
    (by rw [abs_lt]; dsimp [δ, μ]; constructor <;> linarith)
    (by dsimp [δ, μ]; linarith)
    (by dsimp [δ, μ]; linarith)
  refine ⟨eC μ * x, ?_, ?_⟩
  · have h := mul_mem_segment (eC μ) hx
    rw [eC_mul, eC_mul] at h
    rw [show μ + -δ = a by dsimp [μ, δ]; ring,
      show μ + δ = c by dsimp [μ, δ]; ring] at h
    exact h
  · have h := mul_mem_segment (eC μ) hx'
    rw [eC_mul, eC_mul] at h
    simpa only [add_sub_cancel] using h

/-- The same crossing test in the full-turn parametrization used
when choosing the circle ports for XII (4.5), page 253. -/
theorem ordered_chords_inter {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d < a + 1) :
    (segment ℝ (ee a : ℂ) (ee c : ℂ) ∩ segment ℝ (ee b : ℂ) (ee d : ℂ)).Nonempty := by
  change (segment ℝ (eC (2 * Real.pi * a)) (eC (2 * Real.pi * c)) ∩
    segment ℝ (eC (2 * Real.pi * b)) (eC (2 * Real.pi * d))).Nonempty
  apply ordered_unit_chords_inter
  · exact mul_lt_mul_of_pos_left hab (by positivity)
  · exact mul_lt_mul_of_pos_left hbc (by positivity)
  · exact mul_lt_mul_of_pos_left hcd (by positivity)
  · nlinarith [Real.pi_pos]

end GraphMinor.GM12
