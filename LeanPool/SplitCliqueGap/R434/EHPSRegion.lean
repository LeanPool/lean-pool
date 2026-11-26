/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! The polygonal inequalities in EHPS, Definition 4.1 and Lemmas 4.4, 4.6. -/

@[expose] public section

namespace GapExtremal.R434.EHPS

/-- A point in the real plane. -/
abbrev Point := ℝ × ℝ
/-- The sum of the two coordinates of a point. -/
def total (x : Point) : ℝ := x.1 + x.2

/-- The admissible half-open region for the midpoint-defect construction. -/
def Region (ε : ℝ) (x : Point) : Prop :=
  0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1 ∧
    ((1 / 2 ≤ x.1 ∧ 2 / 3 < total x ∧ total x ≤ 7 / 6) ∨
     (1 / 2 ≤ x.1 ∧ x.2 < 1 / 2 ∧ 7 / 6 + ε ≤ total x ∧ total x ≤ 17 / 12) ∨
     (x.1 < 1 / 2 ∧ 1 / 2 ≤ x.2 ∧ 7 / 6 + ε ≤ total x ∧
       total x ≤ 17 / 12 ∧ 3 / 2 + ε ≤ 2 * x.1 + x.2))

/-- Each doubled coordinate of the midpoint differs by one of these integers. -/
def Wrap (a b c : ℝ) : Prop :=
  2 * b = a + c - 1 ∨ 2 * b = a + c ∨ 2 * b = a + c + 1

theorem total_bounds {ε : ℝ} {x : Point} (hε : 0 < ε) (hx : Region ε x) :
    2 / 3 < total x ∧ total x ≤ 17 / 12 := by
  rcases hx.2.2.2.2 with ⟨_, h1, h2⟩ | ⟨_, _, h1, h2⟩ | ⟨_, _, h1, h2, _⟩
  all_goals constructor <;> linarith only [hε, h1, h2]

theorem left_total {ε : ℝ} {x : Point} (hx : Region ε x) (hl : x.1 < 1 / 2) :
    7 / 6 + ε ≤ total x ∧ 3 / 2 + ε ≤ 2 * x.1 + x.2 := by
  rcases hx.2.2.2.2 with ⟨hf, _, _⟩ | ⟨hf, _, _, _⟩ | ⟨_, _, h1, _, h2⟩
  · exact False.elim ((not_le_of_gt hl) hf)
  · exact False.elim ((not_le_of_gt hl) hf)
  · exact ⟨h1, h2⟩

theorem upper_right_total {ε : ℝ} {x : Point} (hx : Region ε x)
    (h₁ : 1 / 2 ≤ x.1) (h₂ : 1 / 2 ≤ x.2) : total x ≤ 7 / 6 := by
  rcases hx.2.2.2.2 with ⟨_, _, hu⟩ | ⟨_, hl, _, _⟩ | ⟨hl, _, _, _, _⟩
  · exact hu
  · exact False.elim ((not_le_of_gt hl) h₂)
  · exact False.elim ((not_le_of_gt hl) h₁)

theorem one_coordinate_high {ε : ℝ} {x : Point} (hx : Region ε x) :
    1 / 2 ≤ x.1 ∨ 1 / 2 ≤ x.2 := by
  rcases hx.2.2.2.2 with ⟨h, _, _⟩ | ⟨h, _, _, _⟩ | ⟨_, h, _, _, _⟩
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr h

theorem midpoint_total {ε : ℝ} {x y z : Point} (hε : 0 < ε)
    (hx : Region ε x) (hy : Region ε y) (hz : Region ε z)
    (h₁ : Wrap x.1 y.1 z.1) (h₂ : Wrap x.2 y.2 z.2) :
    2 * total y = total x + total z ∨ 2 * total y = total x + total z - 1 := by
  have hxs := total_bounds hε hx
  have hys := total_bounds hε hy
  have hzs := total_bounds hε hz
  have hmax₁ : 2 * y.1 ≤ x.1 + z.1 + 1 := by
    rcases h₁ with h | h | h <;> linarith only [h]
  have hmax₂ : 2 * y.2 ≤ x.2 + z.2 + 1 := by
    rcases h₂ with h | h | h <;> linarith only [h]
  have hnotup : ¬ (total x + total z + 1 ≤ 2 * total y) := by
    intro hup
    have hraw := hup
    unfold total at hraw
    by_cases hs : x.1 + z.1 < 1
    · have hlarge : 11 / 6 < total x + total z := by
        by_cases ht : x.1 < 1 / 2
        · linarith only [hε, (left_total hx ht).1, hzs.1]
        · have ht' : z.1 < 1 / 2 := by linarith only [hs, le_of_not_gt ht]
          linarith only [hε, (left_total hz ht').1, hxs.1]
      linarith only [hup, hlarge, hys.2]
    · have hs' := le_of_not_gt hs
      have hfirst : 1 / 2 ≤ y.1 := by linarith only [hraw, hmax₂, hs']
      have hsecond : 1 / 2 ≤ y.2 := by
        rcases h₁ with h | h | h
        · linarith only [h, hraw, hmax₂]
        · linarith only [h, hraw, hx.2.2.1, hz.2.2.1]
        · linarith only [h, hs', hy.2.1]
      linarith only [hup, hxs.1, hzs.1, upper_right_total hy hfirst hsecond]
  have hnotdown : ¬ (2 * y.1 = x.1 + z.1 - 1 ∧ 2 * y.2 = x.2 + z.2 - 1) := by
    intro ⟨ha, hb⟩
    rcases one_coordinate_high hy with hh | hh
    · linarith only [ha, hh, hx.2.1, hz.2.1]
    · linarith only [hb, hh, hx.2.2.2.1, hz.2.2.2.1]
  rcases h₁ with ha | ha | ha <;> rcases h₂ with hb | hb | hb <;>
    first
    | exact False.elim (hnotdown ⟨ha, hb⟩)
    | left; unfold total; linarith only [ha, hb]
    | right; unfold total; linarith only [ha, hb]
    | exfalso; apply hnotup; unfold total; linarith only [ha, hb]

theorem close_first_sum {ε : ℝ} {x z : Point}
    (hx : Region ε x) (hz : Region ε z)
    (hd₁ : total x - total z < ε) (hd₂ : total z - total x < ε)
    (hside : 1 / 2 ≤ x.1 ∨ 1 / 2 ≤ z.1) :
    1 ≤ x.1 + z.1 := by
  have hxbox := hx.2.2.2.2
  have hzbox := hz.2.2.2.2
  unfold total at hd₁ hd₂ hxbox hzbox
  rcases hside with hs | hs <;>
    rcases hxbox with ⟨hx₁,hx₂,hx₃⟩ | ⟨hx₁,hx₂,hx₃,hx₄⟩ |
      ⟨hx₁,hx₂,hx₃,hx₄,hx₅⟩ <;>
    rcases hzbox with ⟨hz₁,hz₂,hz₃⟩ | ⟨hz₁,hz₂,hz₃,hz₄⟩ |
      ⟨hz₁,hz₂,hz₃,hz₄,hz₅⟩ <;> linarith

end GapExtremal.R434.EHPS
