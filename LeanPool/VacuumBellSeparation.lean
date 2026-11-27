/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.OQP12
public import LeanPool.VacuumBellSeparation.FreeField.Existence
public import LeanPool.VacuumBellSeparation.FreeField.LocalAlgebraNonabelian

/-!
# Vacuum Bell correlation at large spacelike separation

Source: url:https://github.com/physical-superintelligence/oqp-batch-2026/tree/7049357c42a8fe85262da08fdc10d57b4d9e67a0/oqp12-vacuum-bell-correlations
Authors: David Turturean
Status: verified
Main declarations: `VacuumBellSeparation.OQP12.theorem_1_1`,
  `VacuumBellSeparation.OQP12.corollary_1_2`,
  `VacuumBellSeparation.OQP12.no_chsh_violation_far_apart`,
  `VacuumBellSeparation.OQP12.no_chsh_violation_far_apart_uniform`,
  `VacuumBellSeparation.OQP12.freeFieldVacuum_exists`,
  `VacuumBellSeparation.OQP12.localAlgebra_open_nonabelian`
Tags: quantum-field-theory, bell-inequalities, operator-algebras, free-scalar-field
MSC: 81T05, 81P40, 46L60
-/

/-!
## Upstream attribution

Physical Superintelligence PBC released this formalization under Apache 2.0 on October 23, 2026
as part of its Open Quantum Problems batch. It follows the full manuscript of October 21,
2026. Its Theorem 1.1 and Corollary 1.2 correspond to Theorem 1 and Corollary 1 of the
October 22 letter.

The upstream NOTICE records the following attribution.

> This result was released by Physical Superintelligence (PSI). The
> mathematics was developed by PSI researchers working with AI models (OpenAI's GPT-6-Astra and
> GPT-5.6 Pro and Anthropic's Claude Fable 5.1) in automated research workflows at PSI. The Lean
> formalization was written by AI agents (Anthropic's Claude Opus 5.5 in Claude Code, and OpenAI's
> GPT-6-Astra in Codex) under PSI's direction. David
> Turturean is responsible for the correctness of the paper. The paper's AI disclosure has the
> details; formalization.yaml records which agent did which part.

This port adapts the module layout, imports, and proofs to Lean Pool's pinned toolchain.
-/

public section

open scoped InnerProductSpace

namespace VacuumBellSeparation.OQP12

theorem no_chsh_violation_far_apart (m : ℝ) (hm : 0 < m)
    (O₁ O₂ : Set Spacetime) (hO₁ : Bornology.IsBounded O₁) (hO₂ : Bornology.IsBounded O₂)
    (a : Spacetime) (ha : a.1 ^ 2 < ‖a.2‖ ^ 2) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H) (A₀ A₁ B₀ B₁ : H →L[ℂ] H),
        A₀ ∈ localAlgebra V O₁ → A₁ ∈ localAlgebra V O₁ →
        B₀ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) →
        B₁ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) →
        IsSelfAdjoint A₀ → IsSelfAdjoint A₁ → IsSelfAdjoint B₀ → IsSelfAdjoint B₁ →
        ‖A₀‖ ≤ 1 → ‖A₁‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖B₁‖ ≤ 1 →
        ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖ ≤ 2 :=
  VacuumBellSeparation.no_chsh_violation_far_apart m hm O₁ O₂ hO₁ hO₂ a ha

theorem theorem_1_1 :
    ∃ Cstar : ℝ, 2 < Cstar ∧
      ∀ m R L : ℝ, 0 < m → 0 < R → Cstar * R ≤ L →
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum m H),
          sSup {v : ℝ | ∃ A₀ A₁ B₀ B₁ : H →L[ℂ] H,
            A₀ ∈ localAlgebra V (doubleCone 0 R) ∧ A₁ ∈ localAlgebra V (doubleCone 0 R) ∧
            B₀ ∈ localAlgebra V (doubleCone (0, L • e₁) R) ∧
            B₁ ∈ localAlgebra V (doubleCone (0, L • e₁) R) ∧
            IsSelfAdjoint A₀ ∧ IsSelfAdjoint A₁ ∧ IsSelfAdjoint B₀ ∧ IsSelfAdjoint B₁ ∧
            ‖A₀‖ ≤ 1 ∧ ‖A₁‖ ≤ 1 ∧ ‖B₀‖ ≤ 1 ∧ ‖B₁‖ ≤ 1 ∧
            v = (1 / 2 : ℝ) * ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖} = 1 :=
  VacuumBellSeparation.theorem_1_1_explicit

theorem corollary_1_2 :
    ∀ m : ℝ, 0 < m → ∀ O₁ O₂ : Set Spacetime, Bornology.IsBounded O₁ → Bornology.IsBounded O₂ →
      ∀ a : Spacetime, a.1 ^ 2 < ‖a.2‖ ^ 2 →
        ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
          ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
            (V : FreeFieldVacuum m H),
            sSup {v : ℝ | ∃ A₀ A₁ B₀ B₁ : H →L[ℂ] H,
              A₀ ∈ localAlgebra V O₁ ∧ A₁ ∈ localAlgebra V O₁ ∧
              B₀ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) ∧
              B₁ ∈ localAlgebra V ((fun x => x + t • a) '' O₂) ∧
              IsSelfAdjoint A₀ ∧ IsSelfAdjoint A₁ ∧ IsSelfAdjoint B₀ ∧ IsSelfAdjoint B₁ ∧
              ‖A₀‖ ≤ 1 ∧ ‖A₁‖ ≤ 1 ∧ ‖B₀‖ ≤ 1 ∧ ‖B₁‖ ≤ 1 ∧
              v = (1 / 2 : ℝ) * ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖} =
              1 :=
  VacuumBellSeparation.corollary_1_2_explicit

theorem freeFieldVacuum_exists :
    ∀ m : ℝ, 0 < m → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H), Nonempty (FreeFieldVacuum m H) :=
  VacuumBellSeparation.freeFieldVacuum_exists

theorem no_chsh_violation_far_apart_uniform (m : ℝ) (hm : 0 < m)
    (O₁ O₂ : Set Spacetime) (hO₁ : Bornology.IsBounded O₁) (hO₂ : Bornology.IsBounded O₂) :
    ∃ D : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), D ≤ ‖x‖ →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H) (A₀ A₁ B₀ B₁ : H →L[ℂ] H),
        A₀ ∈ localAlgebra V O₁ → A₁ ∈ localAlgebra V O₁ →
        B₀ ∈ localAlgebra V ((fun y => y + ((0 : ℝ), x)) '' O₂) →
        B₁ ∈ localAlgebra V ((fun y => y + ((0 : ℝ), x)) '' O₂) →
        IsSelfAdjoint A₀ → IsSelfAdjoint A₁ → IsSelfAdjoint B₀ → IsSelfAdjoint B₁ →
        ‖A₀‖ ≤ 1 → ‖A₁‖ ≤ 1 → ‖B₀‖ ≤ 1 → ‖B₁‖ ≤ 1 →
        ‖⟪V.vacuum, (A₀ * (B₀ + B₁) + A₁ * (B₀ - B₁)) V.vacuum⟫_ℂ‖ ≤ 2 :=
  VacuumBellSeparation.no_chsh_violation_far_apart_uniform m hm O₁ O₂ hO₁ hO₂

theorem localAlgebra_open_nonabelian (m : ℝ) (hm : 0 < m)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : FreeFieldVacuum m H) (O : Set Spacetime) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ A ∈ localAlgebra V O, ∃ B ∈ localAlgebra V O, A * B ≠ B * A :=
  V.localAlgebra_open_nonabelian hm hO hne

end VacuumBellSeparation.OQP12
