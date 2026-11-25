/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/


module

public import Mathlib.Algebra.Group.Nat.Even
meta import Lean.Elab.Tactic.Omega

/-!
# Parameters for the eye induction in Graph Minors XV and XVI
-/

@[expose] public section

namespace GraphMinor.GM15

/-- The tangle orders and size bounds used by the eye induction. -/
structure EyeInductionParameters where
  /-- The enlarged order `θ''` of the next span. -/
  enlargedOrder : ℕ
  /-- The first crooked-transaction threshold `τ₁`. -/
  firstThreshold : ℕ
  /-- The second crooked-transaction threshold `τ₂`. -/
  secondThreshold : ℕ
  /-- The size `π` of the crooked transaction. -/
  transactionSize : ℕ
  /-- The size `β` of the battlefield. -/
  battlefieldSize : ℕ
  /-- The order `θ_k` of the previous span. -/
  order : ℕ
  /-- The flatness threshold `λ_k` of the previous span. -/
  flatness : ℕ
  /-- The width `p_k` of the final segregation. -/
  segregationWidth : ℕ

/-- Parameters for the induction step in Graph Minors XV (1.2). -/
abbrev eyeInductionParameters (φ μ θ' : ℕ) : EyeInductionParameters :=
  let θ'' := 2 * (θ' + 3 * μ + 8)
  let τ₁ := 4 + μ / 2
  let τ₂ := 6 + θ'' / 2
  let π := (φ - 1) * (2 * τ₁ + τ₂ - 7)
  let beta := 2 * π + 8
  ⟨θ'', τ₁, τ₂, π, beta, 100 * beta, 20 * beta, 3 * π + 9⟩

/-- Arithmetic bounds for the Section 7 parameters `θ'', τ₁, τ₂, π, beta, θ_k, lam_k, p_k`
(Graph Minors XV, Section 7, page 135). -/
theorem eye_induction_parameter_bounds {φ μ lam' θ' : ℕ}
    (hφ8 : 8 ≤ φ) (hμ12 : 12 ≤ μ) (hlam'4 : 4 ≤ lam') (hθ'_ge : 4 * lam' + μ + 2 ≤ θ') :
    let θ'' := (eyeInductionParameters φ μ θ').enlargedOrder
    let τ₁ := (eyeInductionParameters φ μ θ').firstThreshold
    let τ₂ := (eyeInductionParameters φ μ θ').secondThreshold
    let π := (eyeInductionParameters φ μ θ').transactionSize
    let beta := (eyeInductionParameters φ μ θ').battlefieldSize
    let θ_k := (eyeInductionParameters φ μ θ').order
    let lam_k := (eyeInductionParameters φ μ θ').flatness
    Even θ'' ∧ θ' ≤ θ'' ∧ 4 ≤ θ' ∧ 4 ≤ θ_k ∧
    4 * lam' + μ + 2 ≤ θ'' ∧ 6 * μ + 14 < θ'' ∧
    2 ≤ φ ∧ 3 ≤ φ ∧ 3 ≤ τ₁ ∧ 4 ≤ τ₂ ∧
    2 ≤ π ∧ π ≠ 3 ∧
    4 * lam_k + μ + 2 ≤ θ_k ∧
    6 * (3 * μ + 3) + 5 * lam' + 3 * μ + 4 ≤ lam_k ∧
    θ'' + 16 * μ + 17 ≤ θ_k ∧
    θ'' + 13 * μ + 14 ≤ beta ∧
    16 * beta + 17 ≤ θ_k ∧
    6 * beta + 12 < θ_k ∧
    φ ≤ θ_k - 4 * (3 * beta + 3) - 2 ∧
    3 * beta + 3 ≤ lam_k ∧
    2 * τ₁ < θ_k - 4 * (3 * beta + 3) - 2 ∧
    6 * (3 * beta + 3) + 5 * lam' + 3 * μ + 4 ≤ lam_k := by
  let parameters := eyeInductionParameters φ μ θ'
  have hθ''_even : Even parameters.enlargedOrder := by
    dsimp only [parameters, eyeInductionParameters]
    exact ⟨θ' + 3 * μ + 8, by omega⟩
  have hτ_sum : θ' + 4 * μ + 11 ≤
      2 * parameters.firstThreshold + parameters.secondThreshold - 7 := by
    dsimp only [parameters, eyeInductionParameters]
    omega
  have hφ_sub : 7 ≤ φ - 1 := by omega
  have hπ_ge : 7 * (θ' + 4 * μ + 11) ≤ parameters.transactionSize := Nat.mul_le_mul hφ_sub hτ_sum
  have hπ_ge_φ : φ ≤ parameters.transactionSize := by
    have h2 : 2 ≤ 2 * parameters.firstThreshold + parameters.secondThreshold - 7 :=
      Nat.le_trans (by omega) hτ_sum
    have h3 := Nat.mul_le_mul_left (φ - 1) h2
    dsimp only [parameters, eyeInductionParameters] at h3 ⊢
    omega
  dsimp only [parameters, eyeInductionParameters] at hπ_ge hπ_ge_φ
  dsimp only [eyeInductionParameters]
  refine ⟨hθ''_even, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end GraphMinor.GM15
