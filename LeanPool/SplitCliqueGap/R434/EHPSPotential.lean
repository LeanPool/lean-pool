/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.EHPSRegion
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The EHPS potential and its uniform pointwise curvature. -/

@[expose] public section

namespace GapExtremal.R434.EHPS

/-- A quadratic potential that restarts at the half-unit boundary. -/
noncomputable def bend (u : ℝ) : ℝ := if u < 1 / 2 then u ^ 2 else (u - 1 / 2) ^ 2

/-- The weighted quadratic potential used to control midpoint defects. -/
noncomputable def potential (ε : ℝ) (x : Point) : ℝ :=
  (24 / ε ^ 2) * total x ^ 2 + 6 * bend x.1

theorem bend_bounds {u : ℝ} (h₀ : 0 ≤ u) (h₁ : u < 1) : 0 ≤ bend u ∧ bend u ≤ 1 / 4 := by
  unfold bend
  split
  · rename_i h
    exact ⟨sq_nonneg _, by
      have hh : u ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ h₀ h.le 2
      linarith⟩
  · rename_i h
    have hw : 0 ≤ u - 1 / 2 := sub_nonneg.mpr (le_of_not_gt h)
    have hh : (u - 1 / 2) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hw (by linarith) 2
    exact ⟨sq_nonneg _, by linarith⟩

theorem bend_lower {ε : ℝ} {x : Point} (hε : 0 < ε) (hx : Region ε x) :
    (x.1 - 1 / 2) ^ 2 ≤ bend x.1 := by
  unfold bend
  split
  · rename_i h
    have hh := (left_total hx h).2
    nlinarith only [hh, hε, hx.2.2.2.1]
  · exact le_rfl

theorem bend_midpoint {a b c : ℝ} (ha : 0 ≤ a) (ha' : a < 1)
    (hb : 0 ≤ b) (hb' : b < 1) (hc : 0 ≤ c) (hc' : c < 1)
    (h : Wrap a b c) : bend b = bend ((a + c) / 2) := by
  rcases h with h | h | h
  · have hb₁ : b < 1 / 2 := by linarith
    have hm : ¬ (a + c) / 2 < 1 / 2 := by linarith
    simp only [bend, ite_eq_left hb₁, ite_eq_right hm]
    rw [show b = (a + c) / 2 - 1 / 2 by linarith]
  · rw [show b = (a + c) / 2 by linarith]
  · have hb₁ : ¬ b < 1 / 2 := by linarith
    have hm : (a + c) / 2 < 1 / 2 := by linarith
    simp only [bend, ite_eq_right hb₁, ite_eq_left hm]
    rw [show b - 1 / 2 = (a + c) / 2 by linarith]

theorem bend_convex_if_close {ε : ℝ} {x y z : Point} (hε : 0 < ε)
    (hx : Region ε x) (hy : Region ε y) (hz : Region ε z)
    (hw : Wrap x.1 y.1 z.1)
    (hd₁ : total x - total z < ε) (hd₂ : total z - total x < ε) :
    2 * bend y.1 + (x.1 - z.1) ^ 2 / 2 ≤ bend x.1 + bend z.1 := by
  rw [bend_midpoint hx.1 hx.2.1 hy.1 hy.2.1 hz.1 hz.2.1 hw]
  by_cases h : 1 / 2 ≤ x.1 ∨ 1 / 2 ≤ z.1
  · have hm : ¬ (x.1 + z.1) / 2 < 1 / 2 := by
      linarith only [close_first_sum hx hz hd₁ hd₂ h]
    have hid : 2 * bend ((x.1 + z.1) / 2) + (x.1 - z.1) ^ 2 / 2 =
        (x.1 - 1 / 2) ^ 2 + (z.1 - 1 / 2) ^ 2 := by
      simp only [bend, ite_eq_right hm]
      ring
    rw [hid]
    exact add_le_add (bend_lower hε hx) (bend_lower hε hz)
  · have hx' : x.1 < 1 / 2 := lt_of_not_ge (fun hn => h (Or.inl hn))
    have hz' : z.1 < 1 / 2 := lt_of_not_ge (fun hn => h (Or.inr hn))
    have hm : (x.1 + z.1) / 2 < 1 / 2 := by linarith
    simp only [bend, ite_eq_left hx', ite_eq_left hz', ite_eq_left hm]
    nlinarith

theorem potential_bounds {ε : ℝ} {x : Point} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hx : Region ε x) : 0 ≤ potential ε x ∧ potential ε x ≤ 100 / ε ^ 2 := by
  have hb := bend_bounds hx.1 hx.2.1
  have hxs := total_bounds hε hx
  have hsq : total x ^ 2 ≤ 4 := by
    have hh : total x ^ 2 ≤ (2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hxs.1]) (by linarith only [hxs.2]) 2
    linarith
  have hep : 0 < ε ^ 2 := by positivity
  have he : ε ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hε.le hε₁ 2
  have h₄ : (4 : ℝ) ≤ 4 / ε ^ 2 := (le_div_iff₀ hep).mpr (by linarith)
  unfold potential
  constructor
  · have hn := hb.1
    positivity
  · have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 24 / ε ^ 2 by positivity)
    have hid : (100 : ℝ) / ε ^ 2 = (24 / ε ^ 2) * 4 + 4 / ε ^ 2 := by ring
    linarith only [hmul, h₄, hb.2, hid]

theorem potential_midpoint {ε : ℝ} {x y z : Point} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hx : Region ε x) (hy : Region ε y) (hz : Region ε z)
    (hw₁ : Wrap x.1 y.1 z.1) (hw₂ : Wrap x.2 y.2 z.2) :
    (x.1 - z.1) ^ 2 + (x.2 - z.2) ^ 2 ≤
      potential ε x + potential ε z - 2 * potential ε y := by
  have hep : 0 < ε ^ 2 := by positivity
  have hcoef : 0 ≤ 24 / ε ^ 2 := by positivity
  have he : ε ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hε.le hε₁ 2
  have hbₓ := bend_bounds hx.1 hx.2.1
  have hbᵧ := bend_bounds hy.1 hy.2.1
  have hb_z := bend_bounds hz.1 hz.2.1
  have hdist₁ : (x.1 - z.1) ^ 2 ≤ 1 := by
    have h : |x.1 - z.1| ≤ 1 := abs_le.mpr
      ⟨by linarith only [hx.1, hz.2.1], by linarith only [hx.2.1, hz.1]⟩
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have hdist₂ : (x.2 - z.2) ^ 2 ≤ 1 := by
    have h : |x.2 - z.2| ≤ 1 := abs_le.mpr
      ⟨by linarith only [hx.2.2.1, hz.2.2.2.1],
       by linarith only [hx.2.2.2.1, hz.2.2.1]⟩
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have large : ε ^ 2 / 2 ≤ total x ^ 2 + total z ^ 2 - 2 * total y ^ 2 →
      (x.1 - z.1) ^ 2 + (x.2 - z.2) ^ 2 ≤
        potential ε x + potential ε z - 2 * potential ε y := by
    intro h
    have hmul := mul_le_mul_of_nonneg_left h hcoef
    have hid : (24 / ε ^ 2) * (ε ^ 2 / 2) = 12 := by
      (field_simp [hε.ne']; norm_num)
    rw [hid] at hmul
    unfold potential
    nlinarith only [hmul, hdist₁, hdist₂, hbₓ.1, hbᵧ.2, hb_z.1]
  rcases midpoint_total hε hx hy hz hw₁ hw₂ with hsum | hsum
  · by_cases hlarge : ε ≤ |total x - total z|
    · apply large
      have hh := pow_le_pow_left₀ hε.le hlarge 2
      rw [sq_abs] at hh
      have hid : total x ^ 2 + total z ^ 2 - 2 * total y ^ 2 =
          (total x - total z) ^ 2 / 2 := by
        rw [show total y = (total x + total z) / 2 by linarith only [hsum]]
        ring
      linarith only [hh, hid]
    · have hc := abs_lt.mp (lt_of_not_ge hlarge)
      have hb := bend_convex_if_close hε hx hy hz hw₁ hc.2 (by linarith only [hc.1])
      have ht : (2 : ℝ) ≤ 12 / ε ^ 2 := (le_div_iff₀ hep).mpr (by linarith)
      have hm := mul_le_mul_of_nonneg_right ht (sq_nonneg (total x - total z))
      have hid : (24 / ε ^ 2) * (total x ^ 2 + total z ^ 2 - 2 * total y ^ 2) =
          12 / ε ^ 2 * (total x - total z) ^ 2 := by
        rw [show total y = (total x + total z) / 2 by linarith only [hsum]]
        ring
      have hsq : (x.2 - z.2) ^ 2 ≤
          2 * (total x - total z) ^ 2 + 2 * (x.1 - z.1) ^ 2 := by
        unfold total
        nlinarith only [sq_nonneg ((x.1 - z.1) + (x.1 + x.2 - (z.1 + z.2)))]
      unfold potential
      nlinarith only [hb, hm, hid, hsq]
  · apply large
    have hid : total x ^ 2 + total z ^ 2 - 2 * total y ^ 2 =
        (total x - total z) ^ 2 / 2 + 2 * total y + 1 / 2 := by
      rw [show total y = (total x + total z - 1) / 2 by linarith only [hsum]]
      ring
    linarith only [he, hid, (total_bounds hε hy).1, sq_nonneg (total x - total z)]

end GapExtremal.R434.EHPS
