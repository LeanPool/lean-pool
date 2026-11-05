/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset


/-!
# Burkholder majorants: basic definitions

Defines the conjugate exponent `q`, `pStar`, the Burkholder expression `v`, and
the sector parameters used to build the majorant, and a shared reflection lemma
for extending the candidate and its first partials to the plane.
-/

@[expose] public section

noncomputable section

namespace Majorants

/-- The conjugate exponent, with a harmless value at `p = 1`. -/
def q (p : ℝ) : ℝ := if p = 1 then 0 else p / (p - 1)

/-- `pStar = max p q`; in the main `p ≥ 2` regime this is just `p`. -/
def pStar (p : ℝ) : ℝ := max p (q p)

/-- The original Burkholder-type expression, written with `pStar`. -/
def v (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - Real.rpow (|pStar p - 1|) p * Real.rpow (|((x - y) / 2)|) p

/-- The slope parameter separating the two smooth sectors in the first quadrant. -/
  def a (p : ℝ) : ℝ := 1 - 2 / (pStar p)

/-- Normalization constant for the affine-in-`y` sector formula. -/
  def alpha (p : ℝ) : ℝ :=  p* Real.rpow (pStar p/(pStar p - 1)) (1-p)

/-- Central reflection of a four-sector extension, with an involution on its values.
This treats the candidate and its odd first partials with the same sector argument.
The classical branch decisions match the opaque sector predicates used by the candidates. -/
theorem quarterPlaneExtension_reflection
    (f g : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (hσ : Function.Involutive σ)
    (x y : ℝ) (hy : y < 0) :
    let extension := fun x y : ℝ =>
      @ite ℝ (0 ≤ x ∧ y ≤ x ∧ -x ≤ y) (Classical.propDecidable _) (f x y) <|
      @ite ℝ (x ≤ 0 ∧ y ≤ -x ∧ x ≤ y) (Classical.propDecidable _) (σ (f (-x) (-y))) <|
      @ite ℝ (0 ≤ y ∧ -y ≤ x ∧ x ≤ y) (Classical.propDecidable _) (g y x) <|
      @ite ℝ (y ≤ 0 ∧ y ≤ x ∧ x ≤ -y) (Classical.propDecidable _) (σ (g (-y) (-x))) 0
    extension x y = σ (extension (-x) (-y)) := by
  dsimp only
  by_cases hleft : x ≤ y
  · have hQ2 : x ≤ 0 ∧ y ≤ -x ∧ x ≤ y :=
      ⟨by linarith only [hy, hleft], by linarith only [hy, hleft], hleft⟩
    have hQ : 0 ≤ -x ∧ -y ≤ -x ∧ -(-x) ≤ -y :=
      ⟨by linarith only [hy, hleft], neg_le_neg hleft,
        by linarith only [hy, hleft]⟩
    have hnotQ : ¬ (0 ≤ x ∧ y ≤ x ∧ -x ≤ y) :=
      fun h => not_le_of_gt (lt_of_le_of_lt hleft hy) h.1
    simp only [ite_eq_right hnotQ, ite_eq_left hQ2, ite_eq_left hQ]
  · have hyx : y < x := lt_of_not_ge hleft
    by_cases hmiddle : x < -y
    · have hQ4 : y ≤ 0 ∧ y ≤ x ∧ x ≤ -y := ⟨hy.le, hyx.le, hmiddle.le⟩
      have hQ3 : 0 ≤ -y ∧ -(-y) ≤ -x ∧ -x ≤ -y :=
        ⟨neg_nonneg.mpr hy.le, by linarith only [hmiddle], neg_le_neg hyx.le⟩
      have hnotQ1 : ¬ (0 ≤ x ∧ y ≤ x ∧ -x ≤ y) := by
        intro h
        linarith only [h.2.2, hmiddle]
      have hnotQ2 : ¬ (x ≤ 0 ∧ y ≤ -x ∧ x ≤ y) := fun h => not_le_of_gt hyx h.2.2
      have hnotQ3 : ¬ (0 ≤ y ∧ -y ≤ x ∧ x ≤ y) := fun h => not_le_of_gt hy h.1
      have hnotRef1 : ¬ (0 ≤ -x ∧ -y ≤ -x ∧ -(-x) ≤ -y) := by
        intro h
        linarith only [h.2.1, hyx]
      have hnotRef2 : ¬ (-x ≤ 0 ∧ -y ≤ -(-x) ∧ -x ≤ -y) := by
        intro h
        linarith only [h.2.1, hmiddle]
      simp only [ite_eq_right hnotQ1, ite_eq_right hnotQ2, ite_eq_right hnotQ3, ite_eq_left hQ4,
        ite_eq_right hnotRef1, ite_eq_right hnotRef2, ite_eq_left hQ3]
    · have hright : -y ≤ x := le_of_not_gt hmiddle
      have hx : 0 < x := lt_of_lt_of_le (neg_pos.mpr hy) hright
      have hQ : 0 ≤ x ∧ y ≤ x ∧ -x ≤ y :=
        ⟨hx.le, hyx.le, by linarith only [hright]⟩
      have hQ2 : -x ≤ 0 ∧ -y ≤ -(-x) ∧ -x ≤ -y :=
        ⟨neg_nonpos.mpr hx.le, by simpa only [neg_neg] using hright, neg_le_neg hyx.le⟩
      have hnotQ : ¬ (0 ≤ -x ∧ -y ≤ -x ∧ -(-x) ≤ -y) :=
        fun h => not_le_of_gt (neg_lt_zero.mpr hx) h.1
      rw [ite_eq_left hQ, ite_eq_right hnotQ, ite_eq_left hQ2]
      simp only [neg_neg]
      exact (hσ (f x y)).symm


end Majorants
