/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.Surface.CircleMove
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Boundary parameters for the four vertices of an eye

The cyclic-order assumption in XII (4.5), page 252, gives
four increasing angles on its circuit. Divide them by one
full turn to obtain the ordered parameters used by claim (1).
The original opposite pairs are retained.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

/-- The four boundary vertices of an eye have increasing
parameters in one turn, with their specified order unchanged. -/
theorem exists_eye_boundary_parameters
    {S : Type*} [TopologicalSpace S] {C : Drawing S} {a b c d : S}
    (h : OccurInCircuitOrder C a b c d) :
    ∃ (φ : Circle ≃ₜ C.U) (β : Fin 4 → ℝ),
      StrictMono β ∧ (∀ i, β i ∈ Ico 0 1) ∧
      (φ (ee (β 0))).val = a ∧ (φ (ee (β 1))).val = b ∧
      (φ (ee (β 2))).val = c ∧ (φ (ee (β 3))).val = d := by
  obtain ⟨φ, t₀, t₁, t₂, t₃, h0, h01, h12, h23, h3, ha, hb, hc, hd⟩ := h
  let t : Fin 4 → ℝ := ![t₀, t₁, t₂, t₃]
  have ht : StrictMono t := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact h01
    · exact h12
    · exact h23
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  let β : Fin 4 → ℝ := fun i => t i / (2 * Real.pi)
  have hβ : StrictMono β := fun i j hij => div_lt_div_of_pos_right (ht hij) hpi
  have hβrange : ∀ i, β i ∈ Ico 0 1 := by
    intro i
    have hi0 : 0 ≤ t i := h0.trans (ht.monotone (Fin.zero_le i))
    have hi3 : t i < 2 * Real.pi := (ht.monotone (Fin.le_last i)).trans_lt h3
    exact ⟨div_nonneg hi0 hpi.le, (div_lt_one hpi).mpr hi3⟩
  have hee : ∀ i, ee (β i) = Circle.exp (t i) := by
    intro i
    unfold ee β
    rw [mul_div_cancel₀ _ hpi.ne']
  refine ⟨φ, β, hβ, hβrange, ?_, ?_, ?_, ?_⟩
  · simpa only [hee, t, Matrix.cons_val_zero] using ha
  · simpa [hee, t] using hb
  · simpa [hee, t] using hc
  · simpa [hee, t] using hd

end GraphMinor.GM12
