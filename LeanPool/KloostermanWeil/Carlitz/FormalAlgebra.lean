/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Formal generating-series algebra

Formal power-series and coefficient identities underlying the Carlitz (1969)
generating method. The particular identities are derived in Lean.
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open PowerSeries

/-- The formal series with positive-degree coefficients `K n / n` and constant term zero. -/
noncomputable def KSeries (K : ℕ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else K n / (n : ℂ)

/-- The quadratic formal series `1 + K1 * X + q * X²`. -/
noncomputable def quadraticL (K1 q : ℂ) : ℂ⟦X⟧ :=
  1 + C K1 * X + C q * X ^ 2

@[simp] theorem constantCoeff_quadraticL (K1 q : ℂ) :
    constantCoeff (quadraticL K1 q) = 1 := by
  simp [quadraticL]

theorem derivative_logOf_mul_self
    {f : ℂ⟦X⟧} (hf : constantCoeff f = 1) :
    d⁄dX (logOf f) * f = d⁄dX f := by
  have hg0 : constantCoeff (f - 1) = 0 := by
    simp [hf]
  have hg : HasSubst (f - 1) :=
    HasSubst.of_constantCoeff_zero' hg0
  rw [logOf_eq, derivative_subst hg]
  have hlog :=
    congrArg (fun s : ℂ⟦X⟧ => substAlgHom hg s)
      (derivative_log_mul_one_add_X (A := ℂ))
  simp only [map_mul, map_add, map_one, substAlgHom_X] at hlog
  have hlog' :
      ((d⁄dX (log ℂ)).subst (f - 1)) * f = 1 := by
    simpa [← coe_substAlgHom hg] using hlog
  rw [Derivation.map_sub, derivative_one, sub_zero]
  calc
    ((d⁄dX (log ℂ)).subst (f - 1) * d⁄dX f) * f =
        d⁄dX f * (((d⁄dX (log ℂ)).subst (f - 1)) * f) := by
          ring
    _ = d⁄dX f := by rw [hlog', mul_one]

@[simp] theorem coeff_KSeries_succ (K : ℕ → ℂ) (n : ℕ) :
    coeff (n + 1) (KSeries K) = K (n + 1) / ((n + 1 : ℕ) : ℂ) := by
  simp [KSeries]

theorem coeff_derivative_KSeries (K : ℕ → ℂ) (n : ℕ) :
    coeff n (d⁄dX (KSeries K)) = K (n + 1) := by
  rw [coeff_derivative, coeff_KSeries_succ]
  have hcast : (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 := by
    norm_num
  rw [hcast]
  field_simp

theorem coeff_quadraticL_of_three_le
    (K1 q : ℂ) {n : ℕ} (hn : 3 ≤ n) :
    coeff n (quadraticL K1 q) = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  simp [quadraticL, coeff_X, coeff_X_pow, hn0, hn1, hn2]

theorem coeff_mul_quadraticL
    (D : ℂ⟦X⟧) (K1 q : ℂ) (r : ℕ) :
    coeff (r + 2) (D * quadraticL K1 q) =
      coeff (r + 2) D +
        K1 * coeff (r + 1) D +
        q * coeff r D := by
  have h1 :
      coeff (r + 2) (D * (C K1 * X)) =
        coeff (r + 1) D * K1 := by
    rw [← mul_assoc]
    rw [show (X : ℂ⟦X⟧) = X ^ 1 by simp]
    rw [show r + 2 = (r + 1) + 1 by omega]
    simp [coeff_mul_C]
  have h2 :
      coeff (r + 2) (D * (C q * X ^ 2)) =
        coeff r D * q := by
    rw [← mul_assoc]
    rw [coeff_mul_X_pow]
    simp [coeff_mul_C]
  rw [quadraticL, mul_add, mul_add, map_add, map_add]
  rw [h1, h2]
  simp
  ring

theorem recurrence_shifted_of_generating_identity
    (K : ℕ → ℂ) (q : ℂ)
    (hgen :
      KSeries K = logOf (quadraticL (K 1) q)) :
    ∀ r : ℕ,
      K (r + 3) + K 1 * K (r + 2) + q * K (r + 1) = 0 := by
  intro r
  have hder :
      d⁄dX (KSeries K) * quadraticL (K 1) q =
        d⁄dX (quadraticL (K 1) q) := by
    rw [hgen]
    exact derivative_logOf_mul_self
      (constantCoeff_quadraticL (K 1) q)
  have hc := congrArg (coeff (r + 2)) hder
  rw [coeff_mul_quadraticL] at hc
  rw [coeff_derivative_KSeries, coeff_derivative_KSeries,
    coeff_derivative_KSeries] at hc
  rw [coeff_derivative, coeff_quadraticL_of_three_le (K 1) q (by omega)] at hc
  simp at hc
  simpa [mul_comm, mul_left_comm, mul_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

theorem recurrence_of_generating_identity
    (K : ℕ → ℂ) (q : ℂ)
    (hgen :
      KSeries K = logOf (quadraticL (K 1) q)) :
    ∀ n : ℕ, 1 ≤ n →
      K (n + 2) + K 1 * K (n + 1) + q * K n = 0 := by
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    recurrence_shifted_of_generating_identity K q hgen r



open PowerSeries

theorem coeff_one_mul_quadraticL
    (D : ℂ⟦X⟧) (K1 q : ℂ) :
    coeff 1 (D * quadraticL K1 q) =
      coeff 1 D + K1 * coeff 0 D := by
  have h1 :
      coeff 1 (D * (C K1 * X)) =
        coeff 0 D * K1 := by
    rw [← mul_assoc]
    rw [show (X : ℂ⟦X⟧) = X ^ 1 by simp]
    simp [coeff_mul_C]
  have h2 :
      coeff 1 (D * (C q * X ^ 2)) = 0 := by
    rw [← mul_assoc]
    rw [coeff_mul_X_pow']
    simp
  rw [quadraticL, mul_add, mul_add, map_add, map_add]
  rw [h1, h2]
  simp
  ring

theorem K_two_eq_of_generating_identity
    (K : ℕ → ℂ) (q : ℂ)
    (hgen :
      KSeries K = logOf (quadraticL (K 1) q)) :
    K 2 = 2 * q - K 1 ^ 2 := by
  have hder :
      d⁄dX (KSeries K) * quadraticL (K 1) q =
        d⁄dX (quadraticL (K 1) q) := by
    rw [hgen]
    exact derivative_logOf_mul_self
      (constantCoeff_quadraticL (K 1) q)
  have hc := congrArg (coeff 1) hder
  rw [coeff_one_mul_quadraticL] at hc
  rw [coeff_derivative_KSeries, coeff_derivative_KSeries] at hc
  rw [coeff_derivative] at hc
  have hq2 : coeff 2 (quadraticL (K 1) q) = q := by
    simp [quadraticL]
  rw [hq2] at hc
  norm_num at hc ⊢
  linear_combination hc



open Polynomial PowerSeries

/-- The quadratic polynomial whose two roots encode the extension-sum recurrence. -/
noncomputable def spectralPoly (K1 q : ℂ) : ℂ[X] :=
  Polynomial.X ^ 2 +
    (Polynomial.C K1 * Polynomial.X +
      Polynomial.C q)

theorem spectralPoly_degree (K1 q : ℂ) :
    (spectralPoly K1 q).degree = 2 := by
  unfold spectralPoly
  rw [degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow 2
  · apply (degree_add_le _ _).trans_lt
    apply max_lt
    · exact (degree_C_mul_X_le K1).trans_lt (by norm_num)
    · exact degree_C_le.trans_lt (by norm_num)

theorem exists_spectral_roots_of_generating_identity
    (K : ℕ → ℂ) (q : ℂ)
    (hgen :
      KSeries K = logOf (quadraticL (K 1) q)) :
    ∃ α β : ℂ,
      α + β = -K 1 ∧
      α * β = q ∧
      ∀ n : ℕ, 1 ≤ n →
        K n = -(α ^ n + β ^ n) := by
  have hdeg : 0 < (spectralPoly (K 1) q).degree := by
    rw [spectralPoly_degree]
    norm_num
  obtain ⟨α, hαroot⟩ := Complex.exists_root hdeg
  have hα' :
      α ^ 2 + (K 1 * α + q) = 0 := by
    simpa [spectralPoly, Polynomial.IsRoot] using hαroot
  have hα :
      α ^ 2 + K 1 * α + q = 0 := by
    linear_combination hα'
  let β : ℂ := -K 1 - α
  have hsum : α + β = -K 1 := by
    dsimp [β]
    ring
  have hprod : α * β = q := by
    dsimp [β]
    linear_combination -hα
  have hβ :
      β ^ 2 + K 1 * β + q = 0 := by
    dsimp [β]
    linear_combination hα
  have hK2 := K_two_eq_of_generating_identity K q hgen
  have hrec := recurrence_of_generating_identity K q hgen
  have hSrec :
      ∀ n : ℕ,
        (-(α ^ (n + 2) + β ^ (n + 2))) +
            K 1 * (-(α ^ (n + 1) + β ^ (n + 1))) +
            q * (-(α ^ n + β ^ n)) = 0 := by
    intro n
    rw [show n + 2 = n + 2 by rfl, show n + 1 = n + 1 by rfl]
    rw [pow_add, pow_add, pow_add, pow_add]
    norm_num
    linear_combination
      -(α ^ n) * hα - (β ^ n) * hβ
  have hshift :
      ∀ r : ℕ,
        K (r + 1) = -(α ^ (r + 1) + β ^ (r + 1)) := by
    intro r
    induction r using Nat.twoStepInduction with
    | zero =>
        simp [hsum]
    | one =>
        rw [hK2]
        have hsquare :
            α ^ 2 + β ^ 2 = (K 1) ^ 2 - 2 * q := by
          calc
            α ^ 2 + β ^ 2 =
                (α + β) ^ 2 - 2 * (α * β) := by ring
            _ = (K 1) ^ 2 - 2 * q := by rw [hsum, hprod]; ring
        rw [hsquare]
        ring
    | more n ih0 ih1 =>
        have hk :=
          hrec (n + 1) (by omega)
        have hs := hSrec (n + 1)
        rw [ih1, ih0] at hk
        linear_combination hk - hs
  refine ⟨α, β, hsum, hprod, ?_⟩
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift r


end KloostermanWeil.Carlitz
