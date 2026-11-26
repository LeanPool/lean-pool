/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8JointSignatureInverse

/-!
# Invariance of the manuscript's weighted residual and joint constants

The manuscript's `v_p = (a_i t_i^p)` uses an enumeration of non-ground modal
coordinates. Simultaneously reindexing the weights `a` and nodes `t` does not
change the literal weighted least-squares objective, its attained minimum
`kappa^2`, or the resulting joint constants in Theorem C.

The proof uses the accepted global minimality and attainment theorems for the
actual orthogonal projection. No chosen projection coefficients, independence
of the first three moments, or positive/nonzero weights are assumptions.
-/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators

variable {m n : ℕ}

/-- The exact weighted objective in the manuscript is independent of the
enumeration of the modal pairs `(a_i, t_i)`. -/
theorem weighted_least_squares_sum_reindex (e : Fin m ≃ Fin n)
    (a t : Fin n → ℝ) (p : ℕ) (c0 c1 c2 : ℝ) :
    (∑ i : Fin m, a (e i) ^ 2 *
      (t (e i) ^ p-c0-c1 * t (e i)-c2 * t (e i) ^ 2) ^ 2) =
    ∑ i : Fin n, a i ^ 2 * (t i ^ p-c0-c1 * t i-c2 * t i ^ 2) ^ 2 := by
  exact e.sum_comp (fun i => a i ^ 2 * (t i ^ p-c0-c1 * t i-c2 * t i ^ 2) ^ 2)

/-- The product-square form used by the accepted projection-minimality
interface has the same finite-coordinate invariance. -/
theorem quadratic_residual_sum_reindex (e : Fin m ≃ Fin n)
    (a t : Fin n → ℝ) (p : ℕ) (c0 c1 c2 : ℝ) :
    (∑ i : Fin m,
      (a (e i) * (t (e i) ^ p-(c0 + c1 * t (e i) + c2 * t (e i) ^ 2))) ^ 2) =
    ∑ i : Fin n, (a i * (t i ^ p-(c0 + c1 * t i + c2 * t i ^ 2))) ^ 2 := by
  exact e.sum_comp (fun i => (a i * (t i ^ p-(c0 + c1 * t i + c2 * t i ^ 2))) ^ 2)

/-- The true least-squares minimum is unchanged by a simultaneous modal
reindexing. The two inequalities use attained minimizers of the two actual
projection problems, rather than supplied coefficients or certificates. -/
theorem kappa_sq_reindex (e : Fin m ≃ Fin n)
    (a t : Fin n → ℝ) (p : ℕ) :
    kappa (a ∘ e) (t ∘ e) p ^ 2 = kappa a t p ^ 2 := by
  apply le_antisymm
  · obtain ⟨c0, c1, c2, hc⟩ := exists_kappa_coefficients a t p
    calc
      kappa (a ∘ e) (t ∘ e) p ^ 2 ≤
          ∑ i : Fin m,
            (a (e i) * (t (e i) ^ p-(c0 + c1 * t (e i) + c2 * t (e i) ^ 2))) ^ 2 :=
        kappa_sq_le_quadratic_residual (a ∘ e) (t ∘ e) p c0 c1 c2
      _ = ∑ i : Fin n, (a i * (t i ^ p-(c0 + c1 * t i + c2 * t i ^ 2))) ^ 2 :=
        quadratic_residual_sum_reindex e a t p c0 c1 c2
      _ = kappa a t p ^ 2 := hc
  · obtain ⟨c0, c1, c2, hc⟩ := exists_kappa_coefficients (a ∘ e) (t ∘ e) p
    calc
      kappa a t p ^ 2 ≤
          ∑ i : Fin n, (a i * (t i ^ p-(c0 + c1 * t i + c2 * t i ^ 2))) ^ 2 :=
        kappa_sq_le_quadratic_residual a t p c0 c1 c2
      _ = ∑ i : Fin m,
          (a (e i) * (t (e i) ^ p-(c0 + c1 * t (e i) + c2 * t (e i) ^ 2))) ^ 2 :=
        (quadratic_residual_sum_reindex e a t p c0 c1 c2).symm
      _ = kappa (a ∘ e) (t ∘ e) p ^ 2 := hc

/-- The manuscript's nonnegative residual norm itself is invariant. -/
theorem kappa_reindex (e : Fin m ≃ Fin n)
    (a t : Fin n → ℝ) (p : ℕ) :
    kappa (a ∘ e) (t ∘ e) p = kappa a t p := by
  have hs := kappa_sq_reindex e a t p
  have h0 := kappa_nonneg (a ∘ e) (t ∘ e) p
  have h1 := kappa_nonneg a t p
  nlinarith

/-- All three literal Theorem C numerators are invariant, retaining the
distinct residuals `kappa_3`, `kappa_4`, and `kappa_5`. -/
theorem jointNumerator_reindex (e : Fin m ≃ Fin n)
    (a t : Fin n → ℝ) (theta : ℝ) :
    jointNumerator (a ∘ e) (t ∘ e) theta = jointNumerator a t theta := by
  simp only [jointNumerator, kappa_reindex]

/-- Each of the three literal constants `beta_r` is invariant. -/
theorem jointBeta_reindex (e : Fin m ≃ Fin n)
    (a t : Fin n → ℝ) (theta : ℝ) (r : Fin 3) :
    jointBeta (a ∘ e) (t ∘ e) theta r = jointBeta a t theta r := by
  rw [jointBeta, jointBeta, jointNumerator_reindex e a t theta]

/-- The sum of the squares of the three Theorem C constants is invariant. -/
theorem jointBetaSq_reindex (e : Fin m ≃ Fin n)
    (a t : Fin n → ℝ) (theta : ℝ) :
    jointBetaSq (a ∘ e) (t ∘ e) theta = jointBetaSq a t theta := by
  simp only [jointBetaSq, jointBeta_reindex]

/-- The manuscript's joint norm `beta` is invariant. -/
theorem jointBetaNorm_reindex (e : Fin m ≃ Fin n)
    (a t : Fin n → ℝ) (theta : ℝ) :
    jointBetaNorm (a ∘ e) (t ∘ e) theta = jointBetaNorm a t theta := by
  rw [jointBetaNorm, jointBetaNorm, jointBetaSq_reindex e a t theta]

/-- Pointwise coordinate transport is enough to identify residuals of two
enumerated modal data sets. -/
theorem kappa_eq_of_reindex (e : Fin m ≃ Fin n)
    (a0 t0 : Fin m → ℝ) (a1 t1 : Fin n → ℝ)
    (ha : ∀ i, a0 i = a1 (e i)) (ht : ∀ i, t0 i = t1 (e i)) (p : ℕ) :
    kappa a0 t0 p = kappa a1 t1 p := by
  have ha' : a0 = a1 ∘ e := funext ha
  have ht' : t0 = t1 ∘ e := funext ht
  rw [ha', ht', kappa_reindex e a1 t1 p]

/-- Pointwise coordinate transport preserves exactly the joint squared
constant used by the accepted original-graph criterion. -/
theorem jointBetaSq_eq_of_reindex (e : Fin m ≃ Fin n)
    (a0 t0 : Fin m → ℝ) (a1 t1 : Fin n → ℝ)
    (ha : ∀ i, a0 i = a1 (e i)) (ht : ∀ i, t0 i = t1 (e i)) (theta : ℝ) :
    jointBetaSq a0 t0 theta = jointBetaSq a1 t1 theta := by
  have ha' : a0 = a1 ∘ e := funext ha
  have ht' : t0 = t1 ∘ e := funext ht
  rw [ha', ht', jointBetaSq_reindex e a1 t1 theta]

/-- The same data-level transport also preserves the joint norm appearing
in the manuscript's strict identification bound. -/
theorem jointBetaNorm_eq_of_reindex (e : Fin m ≃ Fin n)
    (a0 t0 : Fin m → ℝ) (a1 t1 : Fin n → ℝ)
    (ha : ∀ i, a0 i = a1 (e i)) (ht : ∀ i, t0 i = t1 (e i)) (theta : ℝ) :
    jointBetaNorm a0 t0 theta = jointBetaNorm a1 t1 theta := by
  have ha' : a0 = a1 ∘ e := funext ha
  have ht' : t0 = t1 ∘ e := funext ht
  rw [ha', ht', jointBetaNorm_reindex e a1 t1 theta]


end C145DRE8

end
