/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.AuxiliarySeries
public import LeanPool.NairTenenbaum.Polynomials.PolynomialLocal

/-! # Root-weighted auxiliary Euler products

The local convergence needed in §4 now includes every prime, including primes
dividing the discriminant. The bounds use the explicit uniform estimate for
the root counts of each irreducible factor.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- The multiplicative summand `f_h(n) ρ_h(n) / n`. -/
noncomputable def rootAuxiliary (A B ε : ℝ) (γ : ℕ) (Q : ℤ[X]) (n : ℕ) : ℝ :=
  auxiliary A B ε γ n * rootCount Q n / n

@[simp] theorem rootAuxiliary_one (A B ε : ℝ) (γ : ℕ) (Q : ℤ[X]) :
    rootAuxiliary A B ε γ Q 1 = 1 := by simp [rootAuxiliary]

theorem rootAuxiliary_nonneg {A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (γ : ℕ) (Q : ℤ[X]) (n : ℕ) : 0 ≤ rootAuxiliary A B ε γ Q n :=
  div_nonneg (mul_nonneg (auxiliary_nonneg hA hB _ _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem rootAuxiliary_mul (A B ε : ℝ) (γ : ℕ) (Q : ℤ[X]) {m n : ℕ}
    (hmn : m.Coprime n) : rootAuxiliary A B ε γ Q (m * n) =
      rootAuxiliary A B ε γ Q m * rootAuxiliary A B ε γ Q n := by
  simp only [rootAuxiliary, auxiliary_mul γ hmn, rootCount_mul Q hmn, Nat.cast_mul]
  ring

/-- The pointwise majorization of the root-weighted summand used in §4. -/
theorem Admissible.pullback_root_weight_le {k r : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (γ : Fin k → Fin r → ℕ) (Q : Fin r → ℤ[X]) (n : Tuple r) :
    pullback γ F n * (∏ h, (rootCount (Q h) (n h) : ℝ) / (n h : ℝ)) ≤
      F 1 * ∏ h, rootAuxiliary A B ε (totalExponent γ h) (Q h) (n h) := by
  have hG := hF.le_minimalMajorant_mul hA (zero_le_one.trans hB)
    (substitute γ n) 1 (coprime_one_right _)
  rw [mul_one] at hG
  have hbound : pullback γ F n ≤ F 1 * ∏ h, auxiliary A B ε (totalExponent γ h) (n h) := by
    exact hG.trans (by
      simpa only [pullback, mul_comm] using mul_le_mul_of_nonneg_right
        (hF.pullback_minimalMajorant_le_auxiliary hA hB γ n) (hF.nonneg 1))
  calc
    _ ≤ (F 1 * ∏ h, auxiliary A B ε (totalExponent γ h) (n h)) *
        (∏ h, (rootCount (Q h) (n h) : ℝ) / (n h : ℝ)) :=
      mul_le_mul_of_nonneg_right hbound (Finset.prod_nonneg fun _ _ => by positivity)
    _ = _ := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro h _
      simp only [rootAuxiliary]
      ring

theorem rootAuxiliary_prime_pow_le {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    (C ν : ℕ) (hρ : rootCount Q (p ^ ν) ≤ C) :
    rootAuxiliary A B ε γ Q (p ^ ν) ≤ (C : ℝ) * B * auxiliaryRatio ε γ p ^ ν := by
  rw [rootAuxiliary, auxiliary_prime_pow A B ε γ hp, Nat.cast_pow]
  calc
    _ = (rootCount Q (p ^ ν) : ℝ) *
        (auxiliaryLocal A B ε γ p ν / (p : ℝ) ^ ν) := by ring
    _ ≤ (C : ℝ) * (auxiliaryLocal A B ε γ p ν / (p : ℝ) ^ ν) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hρ)
      exact div_nonneg (auxiliaryLocal_nonneg hA (zero_le_one.trans hB) _ _ _) (by positivity)
    _ ≤ (C : ℝ) * (B * auxiliaryRatio ε γ p ^ ν) :=
      mul_le_mul_of_nonneg_left (auxiliaryLocal_div_pow_le hA hB hε γ hp ν) (Nat.cast_nonneg C)
    _ = _ := by ring

theorem rootAuxiliary_prime_pow_summable {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) (Q : ℤ[X])
    {p : ℕ} (hp : p.Prime) (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    Summable (fun ν : ℕ => rootAuxiliary A B ε γ Q (p ^ ν)) :=
  Summable.of_nonneg_of_le
    (fun _ => rootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _ _)
    (fun ν => rootAuxiliary_prime_pow_le hA hB hε γ Q hp C ν (hρ ν))
    ((summable_geometric_of_lt_one (auxiliaryRatio_nonneg ε γ p)
      (auxiliaryRatio_lt_one hp hγε)).mul_left ((C : ℝ) * B))

theorem rootAuxiliary_prime_pow_tsum_le {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) (Q : ℤ[X])
    {p : ℕ} (hp : p.Prime) (C : ℕ) (hρ : ∀ ν, rootCount Q (p ^ ν) ≤ C) :
    (∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ ν)) ≤
      (C : ℝ) * B / (1 - auxiliaryRatio ε γ p) := by
  have hsum := rootAuxiliary_prime_pow_summable hA hB hε γ hγε Q hp C hρ
  have hgeom := (summable_geometric_of_lt_one (auxiliaryRatio_nonneg ε γ p)
    (auxiliaryRatio_lt_one hp hγε)).mul_left ((C : ℝ) * B)
  calc
    _ ≤ ∑' ν : ℕ, (C : ℝ) * B * auxiliaryRatio ε γ p ^ ν :=
      Summable.tsum_le_tsum (fun ν => rootAuxiliary_prime_pow_le hA hB hε γ Q hp C ν (hρ ν))
        hsum hgeom
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (auxiliaryRatio_nonneg ε γ p)
        (auxiliaryRatio_lt_one hp hγε)]
      rfl

theorem rootAuxiliary_smooth_hasSum {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (hγε : (γ : ℝ) * ε < 1) (Q : ℤ[X])
    (C : ℕ) (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C) (s : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers s => rootAuxiliary A B ε γ Q n)
      (∏ p ∈ s.filter Nat.Prime, ∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ ν)) := by
  apply (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (rootAuxiliary_one A B ε γ Q)
    (fun hmn => rootAuxiliary_mul A B ε γ Q hmn) ?_ s).2
  intro p hp
  simp_rw [Real.norm_eq_abs, abs_of_nonneg
    (rootAuxiliary_nonneg hA (zero_le_one.trans hB) γ Q _)]
  exact rootAuxiliary_prime_pow_summable hA hB hε γ hγε Q hp C (hρ p hp)

end NairTenenbaum
