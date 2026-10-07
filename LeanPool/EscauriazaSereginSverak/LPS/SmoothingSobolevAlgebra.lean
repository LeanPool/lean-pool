/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevProductTwo
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevProductHigh

/-!
# Whole-space ordered Sobolev algebra

Smooth `H^m` multiplication is bounded at every integer order
`m ≥ 2`, including the critical middle Leibniz split at order two.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The ordered whole-space `H^m` energy is an algebra for every
integer `m ≥ 2` (eq:lps-Hm-energy). -/
theorem lps_smooth_product_normSq (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (wordDeriv α f) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (wordDeriv α g) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (wordDeriv α (fun x => f x * g x)) 2 volume) ∧
      sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => f x * g x)) ≤
        C * sobolevNormSqOn m univ (fun α => wordDeriv α f) *
          sobolevNormSqOn m univ (fun α => wordDeriv α g) := by
  by_cases htwo : m = 2
  · subst m
    exact lps_smooth_product_normSq_two
  · have hthree : 3 ≤ m := by omega
    exact lps_smooth_product_normSq_high m hthree

end ESS
