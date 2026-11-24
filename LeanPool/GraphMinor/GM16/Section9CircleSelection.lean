/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM16.CircleListing
import LeanPool.GraphMinor.GM16.ErdosSzekeres
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Linarith

/-!
# Selecting paths with ends in order on two circles

This is the Erdős–Szekeres step of XVI (8.1), Claim (4). First order
the ends on one circle. The angle order on the second circle has an
increasing or decreasing subsequence of the desired size. In the
second case invert the circle parameter to reverse its orientation.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface
universe w
variable {S : Type w} [TopologicalSpace S]

/-- Graph Minors XVI, proof of (8.1), Claim (4), page 72: from `m²`
pairs of distinct boundary points, select `m` pairs that occur in order
on both circles under suitable orientations. -/
theorem section9_select_circle_orders {F₁ F₂ : Set S}
    (φ₁ : Circle ≃ₜ F₁) (φ₂ : Circle ≃ₜ F₂)
    (m : ℕ) (hm : 1 ≤ m) (a b : Fin (m ^ 2) → S)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (haF : ∀ i, a i ∈ F₁) (hbF : ∀ i, b i ∈ F₂) :
    ∃ g : Fin m → Fin (m ^ 2), Function.Injective g ∧
      GM12.IsListedInOrderOn F₁ (List.ofFn (a ∘ g)) ∧
      GM12.IsListedInOrderOn F₂ (List.ofFn (b ∘ g)) := by
  classical
  obtain ⟨e, τ, he, hτ, hτBounds, hτEq⟩ := exists_increasing_circle_angles φ₁ a ha haF
  let pt : Fin (m ^ 2) → Circle := fun i => φ₂.symm ⟨b (e i), hbF (e i)⟩
  let angle : Fin (m ^ 2) → ℝ := fun i => Complex.arg (pt i).val
  have hEq : ∀ i, (φ₂ (Circle.exp (angle i))).val = b (e i) := by
    intro i
    rw [show Circle.exp (angle i) = pt i from Circle.exp_arg (pt i)]
    exact congrArg Subtype.val (φ₂.apply_symm_apply ⟨b (e i), hbF (e i)⟩)
  have hAngle : Function.Injective angle := by
    intro i j hij
    exact he.1 (hb ((hEq i).symm.trans ((congrArg (fun t => (φ₂ (Circle.exp t)).val) hij).trans
      (hEq j))))
  obtain ⟨sel, hsel, hOrder⟩ := erdos_szekeres_subsequence m hm angle hAngle
  let g : Fin m → Fin (m ^ 2) := e ∘ sel
  have hmpos : 0 < m := by omega
  refine ⟨g, he.1.comp hsel.injective, ?_, ?_⟩
  · apply listedInOrderOn_of_angles φ₁ hmpos (a ∘ g) (τ ∘ sel) (hτ.comp hsel)
    · intro i
      have hi := hτBounds (sel i)
      have hzero := hτBounds (sel ⟨0, hmpos⟩)
      change τ (sel i) < τ (sel ⟨0, hmpos⟩) + 2 * Real.pi
      linarith
    · intro i
      exact hτEq (sel i)
  · rcases hOrder with hMono | hAnti
    · apply listedInOrderOn_of_angles φ₂ hmpos (b ∘ g) (angle ∘ sel) hMono
      · intro i
        have hi := Complex.arg_le_pi (pt (sel i)).val
        have hzero := Complex.neg_pi_lt_arg (pt (sel ⟨0, hmpos⟩)).val
        change angle (sel i) < angle (sel ⟨0, hmpos⟩) + 2 * Real.pi
        dsimp only [angle] at *
        linarith
      · intro i
        exact hEq (sel i)
    · let φ₂rev : Circle ≃ₜ F₂ := (Homeomorph.inv Circle).trans φ₂
      let τrev : Fin m → ℝ := fun i => -angle (sel i)
      have hRevMono : StrictMono τrev := fun i j hij => neg_lt_neg (hAnti hij)
      apply listedInOrderOn_of_angles φ₂rev hmpos (b ∘ g) τrev hRevMono
      · intro i
        have hi := Complex.neg_pi_lt_arg (pt (sel i)).val
        have hzero := Complex.arg_le_pi (pt (sel ⟨0, hmpos⟩)).val
        change -angle (sel i) < -angle (sel ⟨0, hmpos⟩) + 2 * Real.pi
        dsimp only [angle] at *
        linarith
      · intro i
        change (φ₂ ((Circle.exp (-angle (sel i)))⁻¹)).val = b (e (sel i))
        rw [Circle.exp_neg, inv_inv]
        exact hEq (sel i)

end GraphMinor.GM16
