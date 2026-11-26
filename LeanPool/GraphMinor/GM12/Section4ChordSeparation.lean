/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Lunes
public import LeanPool.GraphMinor.Surface.CircleMove

/-!
# Nonalternating circle ports give disjoint chords

In XII (4.5), page 253, the two chosen incident Hamilton edges
must not cross each other. For two nonalternating pairs of ports,
the chord of one pair lies on a line and the chord of the other
pair lies strictly on one side of that line. The linear function
`gf` gives the separating inequality.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem gf_eq_on_segment {μ r : ℝ} {a b x : ℂ}
    (ha : gf μ a = r) (hb : gf μ b = r) (hx : x ∈ segment ℝ a b) :
    gf μ x = r := by
  obtain ⟨s, t, _, _, hst, rfl⟩ := hx
  rw [gf_add, gf_smul, gf_smul, ha, hb, ← add_mul, hst, one_mul]

private theorem gf_lt_on_segment {μ r : ℝ} {a b x : ℂ}
    (ha : gf μ a < r) (hb : gf μ b < r) (hx : x ∈ segment ℝ a b) :
    gf μ x < r := by
  refine lt_of_le_of_ne (gf_segment_le ha.le hb.le hx) ?_
  intro heq
  rcases gf_segment_eq ha.le hb.le hx heq with rfl | rfl | h
  · exact ha.ne heq
  · exact hb.ne heq
  · exact ha.ne h.1

/-- Nonalternating pairs of circle ports have disjoint chords.
This is the separation test for XII (4.5)(vii), page 253. -/
theorem ordered_unit_chords_disjoint {a c b d : ℝ}
    (hac : a < c) (hcb : c < b) (hbd : b < d) (hda : d < a + 2 * Real.pi) :
    Disjoint (segment ℝ (eC a) (eC c)) (segment ℝ (eC b) (eC d)) := by
  let μ := (a + c) / 2
  let δ := (c - a) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδπ : δ < Real.pi := by dsimp [δ]; linarith
  have hga : gf μ (eC a) = Real.cos δ := by
    rw [gf_eC, show a - μ = -δ by dsimp [μ, δ]; ring, Real.cos_neg]
  have hgc : gf μ (eC c) = Real.cos δ := by
    rw [gf_eC, show c - μ = δ by dsimp [μ, δ]; ring]
  have hgb : gf μ (eC b) < Real.cos δ := by
    rw [gf_eC]
    apply (cos_arc hδ hδπ).2.2.2
    · dsimp [δ, μ]; linarith
    · dsimp [δ, μ]; linarith
  have hgd : gf μ (eC d) < Real.cos δ := by
    rw [gf_eC]
    apply (cos_arc hδ hδπ).2.2.2
    · dsimp [δ, μ]; linarith
    · dsimp [δ, μ]; linarith
  apply disjoint_left.mpr
  intro x hx hx'
  exact (gf_lt_on_segment hgb hgd hx').ne (gf_eq_on_segment hga hgc hx)

/-- The nonalternation test in the full-turn parametrization used
for the circle ports of XII (4.5), page 253. -/
theorem ordered_chords_disjoint {a c b d : ℝ}
    (hac : a < c) (hcb : c < b) (hbd : b < d) (hda : d < a + 1) :
    Disjoint (segment ℝ (ee a : ℂ) (ee c : ℂ))
      (segment ℝ (ee b : ℂ) (ee d : ℂ)) := by
  change Disjoint (segment ℝ (eC (2 * Real.pi * a)) (eC (2 * Real.pi * c)))
    (segment ℝ (eC (2 * Real.pi * b)) (eC (2 * Real.pi * d)))
  apply ordered_unit_chords_disjoint
  · exact mul_lt_mul_of_pos_left hac (by positivity)
  · exact mul_lt_mul_of_pos_left hcb (by positivity)
  · exact mul_lt_mul_of_pos_left hbd (by positivity)
  · nlinarith [Real.pi_pos]

end GraphMinor.GM12
