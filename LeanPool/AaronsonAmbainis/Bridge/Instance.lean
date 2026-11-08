/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import LeanPool.AaronsonAmbainis.Bridge.Capstone

/-!
# The Mathlib-only statements are not vacuous

The hypotheses of `ExplicitBound` and `PrintedConjecture` (`Conjecture.lean`) are satisfied by the
polynomial `p = X₀` in one variable (`N = 1`, `d = 1`, `ε = 1/4`): its total degree is `1`, its
values on `{0,1}` lie in `[0,1]`, its variance is exactly `1/4`, and the influence of its
variable, in the normalisation of Aaronson–Ambainis (`E[(p(X) − p(X^i))²]`), is exactly `1`.

The hypotheses of `ExplicitBoundPM` are satisfied by the polynomial `p = X₀` in one variable on
`{-1,1}` (`true ↦ 1`, `false ↦ -1`, `ε = 1`): bounded by `1`, variance exactly `1`, influence
`E[((p(x) − p(x^i))/2)²]` exactly `1`.

The statements `conj6_instance`, `problemPM_instance` and `conj6_instance_conclusion` are written
with Mathlib notions only.
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset MvPolynomial

theorem ev01_X {N : ℕ} (i : Fin N) (Y : Fin N → Bool) :
    ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) Y = if Y i then 1 else 0 := by
  simp [ev01]

theorem evPM_X {N : ℕ} (i : Fin N) (Y : Fin N → Bool) :
    evPM (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) Y = if Y i then -1 else 1 := by
  simp [evPM]

theorem flipBit_self {N : ℕ} (Y : Fin N → Bool) (i : Fin N) : flipBit Y i i = !Y i := by
  simp [flipBit]

theorem card_points (N : ℕ) : (Fintype.card (Fin N → Bool) : ℝ) = 2 ^ N := by
  have h := card_cube (ι := Fin N)
  rw [Fintype.card_fin] at h
  exact h

theorem Ex_const_one {N : ℕ} : Ex (fun _ : Fin N → Bool => (1 : ℝ)) = 1 := by
  unfold Ex
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [card_points]
  exact div_self (by positivity)

/-- The influence of the variable of `p = X_i` on `{0,1}^N`, normalisation of arXiv:0911.0996. -/
theorem aaInfl_X {N : ℕ} (i : Fin N) :
    Ex (fun Y => (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) Y
      - ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) (flipBit Y i)) ^ 2) = 1 := by
  have h : ∀ Y : Fin N → Bool,
      (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) Y
        - ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) (flipBit Y i)) ^ 2 = 1 := by
    intro Y
    rw [ev01_X, ev01_X, flipBit_self]
    cases Y i <;> simp
  simp only [h]
  exact Ex_const_one

theorem ev01_X_eq_affine {N : ℕ} (i : Fin N) :
    (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) : Cube (Fin N) → ℝ)
      = fun Y => 1 / 2 + (-1 / 2) * dict i Y := by
  funext Y
  rw [ev01_X]
  unfold dict
  split_ifs <;> norm_num

theorem evPM_X_eq_dict {N : ℕ} (i : Fin N) :
    (evPM (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) : Cube (Fin N) → ℝ) = dict i := by
  funext Y
  rw [evPM_X]
  rfl

theorem variance_ev01_X {N : ℕ} (i : Fin N) :
    variance (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) : Cube (Fin N) → ℝ) = 1 / 4 := by
  rw [ev01_X_eq_affine, variance_affine (1 / 2) (-1 / 2) (dict i), variance_dict]
  norm_num

/-- **Non-vacuity of `ExplicitBound` and `PrintedConjecture`.** For `p = X₀` in one variable: total
degree at most `1`, values in `[0,1]` on the cube, variance exactly `1/4`, and the influence of
the variable (normalisation of arXiv:0911.0996) exactly `1`. -/
theorem conj6_instance :
    (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ).totalDegree ≤ 1 ∧
    (∀ Y : Fin 1 → Bool,
      0 ≤ MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) ∧
        MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) ≤ 1) ∧
    (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - (∑ Z : Fin 1 → Bool, MvPolynomial.eval (fun i => if Z i then (1 : ℝ) else 0)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) / 2 ^ 1) ^ 2) / 2 ^ 1 = 1 / 4 ∧
    (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun k => if Y k then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - MvPolynomial.eval (fun k => if Function.update Y 0 (!Y 0) k then (1 : ℝ) else 0)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) ^ 2) / 2 ^ 1 = 1 := by
  refine ⟨(MvPolynomial.totalDegree_X _).le, fun Y => ?_, ?_, ?_⟩
  · change 0 ≤ ev01 (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y ∧
      ev01 (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y ≤ 1
    rw [ev01_X]
    split_ifs <;> norm_num
  · have h := variance_eq_Ex (ev01 (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ))
    exact h.symm.trans (variance_ev01_X 0)
  · exact aaInfl_X (0 : Fin 1)

/-- **Non-vacuity of `ExplicitBoundPM`.** For `p = X₀` in one variable on `{-1,1}` (`true ↦ 1`,
`false ↦ -1`): total degree at most `1`, bounded by `1`, variance exactly `1`, influence exactly
`1`. -/
theorem problemPM_instance :
    (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ).totalDegree ≤ 1 ∧
    (∀ Y : Fin 1 → Bool,
      |MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else -1)
          (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)| ≤ 1) ∧
    (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else -1)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - (∑ Z : Fin 1 → Bool, MvPolynomial.eval (fun i => if Z i then (1 : ℝ) else -1)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) / 2 ^ 1) ^ 2) / 2 ^ 1 = 1 ∧
    (∑ Y : Fin 1 → Bool,
        ((MvPolynomial.eval (fun k => if Y k then (1 : ℝ) else -1)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - MvPolynomial.eval (fun k => if Function.update Y 0 (!Y 0) k then (1 : ℝ) else -1)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) / 2) ^ 2) / 2 ^ 1 = 1 := by
  refine ⟨(MvPolynomial.totalDegree_X _).le, ?_, ?_, ?_⟩
  · change ∀ Y, |evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y| ≤ 1
    rw [evPMt_bound_iff]
    intro Y
    rw [evPM_X]
    split_ifs <;> simp
  · change Ex (fun Y => (evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y
        - Ex (evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ))) ^ 2) = 1
    rw [variance_evPMt]
    have h := variance_eq_Ex (evPM (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ))
    have h1 : variance (evPM (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) : Cube (Fin 1) → ℝ)
        = 1 := by
      rw [evPM_X_eq_dict, variance_dict]
    exact h.symm.trans h1
  · change Ex (fun Y => ((evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) Y
        - evPMt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) (flipBit Y 0)) / 2) ^ 2) = 1
    rw [infl_evPMt]
    have h := inflR_eq_Ex (evPM (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) 0
    have h1 : inflR (evPM (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ) : Cube (Fin 1) → ℝ) 0
        = 1 := by
      rw [evPM_X_eq_dict, inflR_dict_self]
    exact h.symm.trans h1

/-- What the hypothesis-free theorem `explicitBound` says at this instance: the variable of
`p = X₀` has influence at least `(8 √15 / (125 π^4)) (1/4)^{5/2}`. (The true value is `1`.) -/
theorem conj6_instance_conclusion :
    ∃ i : Fin 1,
      (∑ Y : Fin 1 → Bool,
        (MvPolynomial.eval (fun k => if Y k then (1 : ℝ) else 0)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)
          - MvPolynomial.eval (fun k => if Function.update Y i (!Y i) k then (1 : ℝ) else 0)
              (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℝ)) ^ 2) / 2 ^ 1
        ≥ 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * (1 / 4 : ℝ) ^ ((5 : ℝ) / 2)
            / ((1 : ℕ) : ℝ) ^ 6 :=
  explicitBound 1 1 (MvPolynomial.X 0) conj6_instance.1 conj6_instance.2.1 (1 / 4)
    (by norm_num) (le_of_eq conj6_instance.2.2.1.symm)

end AaronsonAmbainis.Bridge
