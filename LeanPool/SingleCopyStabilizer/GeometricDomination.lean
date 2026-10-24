/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.AdaptiveProcess
public import Mathlib.Tactic.FieldSimp


/-!
# Geometric-product tail bounds for finite adaptive processes

Per-state, history-dependent strict-progress bounds imply the same
exponential upper-tail product as independent geometric waiting times. The
proof is direct: derive a one-step contraction of a killed product potential
and iterate it over the finite probability tree. No independent waiting-time
coupling or final tail bound is assumed.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace LeanPool.SingleCopyStabilizer.GeometricDomination

/-- The geometric moment-generating factor, in the parameterization
`q = 1/(1-λ)`. -/
def geometricFactor (p : ℕ → ℝ) (lambda : ℝ) (j : ℕ) : ℝ :=
  (1 - lambda / p j)⁻¹

/-- Product over the positive ranks up to and including `r`. -/
def productPotential (p : ℕ → ℝ) (lambda : ℝ) (r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r, geometricFactor p lambda (j + 1)

/-- Set the potential to zero at the terminal rank. -/
def killedPotential (p : ℕ → ℝ) (lambda : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0 else productPotential p lambda r

variable (p : ℕ → ℝ) (lambda : ℝ)

@[simp] theorem productPotential_zero : productPotential p lambda 0 = 1 := by
  simp [productPotential]

@[simp] theorem killedPotential_zero : killedPotential p lambda 0 = 0 := by
  simp [killedPotential]

theorem productPotential_succ (r : ℕ) :
    productPotential p lambda (r + 1) =
      productPotential p lambda r * geometricFactor p lambda (r + 1) := by
  simp [productPotential, Finset.prod_range_succ]

variable (hlambda : 0 ≤ lambda) (hrate : ∀ j, 0 < j → lambda < p j)
include hlambda hrate

theorem factor_denominator_pos (j : ℕ) (hj : 0 < j) : 0 < 1 - lambda / p j := by
  have hp : 0 < p j := lt_of_le_of_lt hlambda (hrate j hj)
  have hdiv : lambda / p j < 1 := (div_lt_iff₀ hp).2 (by simpa using hrate j hj)
  linarith

theorem one_le_geometricFactor (j : ℕ) (hj : 0 < j) :
    1 ≤ geometricFactor p lambda j := by
  have hp : 0 < p j := lt_of_le_of_lt hlambda (hrate j hj)
  have hden := factor_denominator_pos p lambda hlambda hrate j hj
  unfold geometricFactor
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hden).2
  have hdiv : 0 ≤ lambda / p j := div_nonneg hlambda (le_of_lt hp)
  linarith

theorem one_le_productPotential (r : ℕ) : 1 ≤ productPotential p lambda r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [productPotential_succ]
      have hf := one_le_geometricFactor p lambda hlambda hrate (r + 1) (by omega)
      nlinarith

theorem productPotential_nonneg (r : ℕ) : 0 ≤ productPotential p lambda r :=
  le_trans (by norm_num) (one_le_productPotential p lambda hlambda hrate r)

theorem productPotential_mono : Monotone (productPotential p lambda) := by
  apply monotone_nat_of_le_succ
  intro r
  rw [productPotential_succ]
  have hg := productPotential_nonneg p lambda hlambda hrate r
  have hf := one_le_geometricFactor p lambda hlambda hrate (r + 1) (by omega)
  nlinarith

theorem killedPotential_nonneg (r : ℕ) : 0 ≤ killedPotential p lambda r := by
  unfold killedPotential
  split_ifs
  · exact le_rfl
  · exact productPotential_nonneg p lambda hlambda hrate r

theorem killedPotential_le_productPotential {a b : ℕ} (hab : a ≤ b) :
    killedPotential p lambda a ≤ productPotential p lambda b := by
  unfold killedPotential
  split_ifs
  · exact productPotential_nonneg p lambda hlambda hrate b
  · exact productPotential_mono p lambda hlambda hrate hab

/-- The defining product has exactly the one-step recurrence of a geometric
waiting-time generating function at each positive rank. -/
theorem productPotential_recurrence (r : ℕ) :
    (1 - p (r + 1)) * productPotential p lambda (r + 1) +
        p (r + 1) * productPotential p lambda r =
      (1 - lambda) * productPotential p lambda (r + 1) := by
  have hp : p (r + 1) ≠ 0 := ne_of_gt (lt_of_le_of_lt hlambda (hrate _ (by omega)))
  have hden : 1 - lambda / p (r + 1) ≠ 0 :=
    ne_of_gt (factor_denominator_pos p lambda hlambda hrate _ (by omega))
  have hsub : p (r + 1) - lambda ≠ 0 := ne_of_gt (sub_pos.mpr (hrate _ (by omega)))
  rw [productPotential_succ]
  unfold geometricFactor
  field_simp [hsub]
  ring

variable {S Ω : Type*} [Fintype Ω]

/-- History-conditioned progress gives contraction of the product
potential at every state of the finite tree. -/
theorem product_potential_drift (P : AdaptiveProcess.RankedProcess S Ω)
    (hprogress : ∀ s, 0 < P.rank s → p (P.rank s) ≤ P.progressMass s) (s : S) :
    (∑ o, P.weight s o * killedPotential p lambda (P.rank (P.next s o))) ≤
      (1 - lambda) * killedPotential p lambda (P.rank s) := by
  cases hs : P.rank s with
  | zero =>
      have hnext : ∀ o, P.rank (P.next s o) = 0 := fun o => by
        have h := P.rank_mono s o
        omega
      simp [hnext]
  | succ r =>
      have hpoint (o : Ω) :
          P.weight s o * killedPotential p lambda (P.rank (P.next s o)) ≤
            P.weight s o * productPotential p lambda (r + 1) -
              (if P.rank (P.next s o) < P.rank s then P.weight s o else 0) *
                (productPotential p lambda (r + 1) - productPotential p lambda r) := by
        split_ifs with hlt
        · have hr : P.rank (P.next s o) ≤ r := by omega
          have hh := mul_le_mul_of_nonneg_left
            (killedPotential_le_productPotential p lambda hlambda hrate hr) (P.weight_nonneg s o)
          linarith
        · have hr : P.rank (P.next s o) ≤ r + 1 := by
            simpa [hs] using P.rank_mono s o
          simpa using mul_le_mul_of_nonneg_left
            (killedPotential_le_productPotential p lambda hlambda hrate hr) (P.weight_nonneg s o)
      have hdiff : 0 ≤ productPotential p lambda (r + 1) - productPotential p lambda r :=
        sub_nonneg.mpr (productPotential_mono p lambda hlambda hrate (by omega))
      have hpr : p (r + 1) ≤ P.progressMass s := by
        simpa [hs] using hprogress s (by omega)
      calc
        _ ≤ ∑ o, (P.weight s o * productPotential p lambda (r + 1) -
            (if P.rank (P.next s o) < P.rank s then P.weight s o else 0) *
              (productPotential p lambda (r + 1) - productPotential p lambda r)) :=
          Finset.sum_le_sum fun o _ => hpoint o
        _ = productPotential p lambda (r + 1) - P.progressMass s *
              (productPotential p lambda (r + 1) - productPotential p lambda r) := by
          simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, P.weight_sum, one_mul,
            AdaptiveProcess.RankedProcess.progressMass]
        _ ≤ productPotential p lambda (r + 1) - p (r + 1) *
              (productPotential p lambda (r + 1) - productPotential p lambda r) := by
          exact sub_le_sub_left (mul_le_mul_of_nonneg_right hpr hdiff) _
        _ = (1 - p (r + 1)) * productPotential p lambda (r + 1) +
              p (r + 1) * productPotential p lambda r := by ring
        _ = (1 - lambda) * productPotential p lambda (r + 1) :=
          productPotential_recurrence p lambda hlambda hrate r
        _ = (1 - lambda) * killedPotential p lambda (r + 1) := by
          simp [killedPotential]

/-- The product-geometric tail inequality for a fully adaptive finite tree.
Only local kernel/progress hypotheses are used. -/
theorem failure_probability_le_product (P : AdaptiveProcess.RankedProcess S Ω)
    (hlambda1 : lambda ≤ 1)
    (hprogress : ∀ s, 0 < P.rank s → p (P.rank s) ≤ P.progressMass s)
    (t : ℕ) (s : S) :
    P.failureProbability t s ≤ productPotential p lambda (P.rank s) * (1 - lambda) ^ t := by
  have hq : 0 ≤ 1 - lambda := sub_nonneg.mpr hlambda1
  have hmain (t : ℕ) (s : S) :
      P.failureProbability t s ≤ (1 - lambda) ^ t * killedPotential p lambda (P.rank s) := by
    induction t generalizing s with
    | zero =>
        by_cases hs : P.rank s = 0
        · simp [AdaptiveProcess.RankedProcess.failureProbability, killedPotential, hs]
        · simpa [AdaptiveProcess.RankedProcess.failureProbability, killedPotential, hs] using
            one_le_productPotential p lambda hlambda hrate (P.rank s)
    | succ t ih =>
        calc
          P.failureProbability (t + 1) s =
              ∑ o, P.weight s o * P.failureProbability t (P.next s o) := rfl
          _ ≤ ∑ o, P.weight s o * ((1 - lambda) ^ t *
              killedPotential p lambda (P.rank (P.next s o))) :=
            Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (ih _) (P.weight_nonneg s o)
          _ = (1 - lambda) ^ t * ∑ o,
              P.weight s o * killedPotential p lambda (P.rank (P.next s o)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro o _
            ring
          _ ≤ (1 - lambda) ^ t * ((1 - lambda) * killedPotential p lambda (P.rank s)) :=
            mul_le_mul_of_nonneg_left
              (product_potential_drift p lambda hlambda hrate P hprogress s) (pow_nonneg hq t)
          _ = (1 - lambda) ^ (t + 1) * killedPotential p lambda (P.rank s) := by
            rw [pow_succ]
            ring
  calc
    _ ≤ (1 - lambda) ^ t * killedPotential p lambda (P.rank s) := hmain t s
    _ ≤ (1 - lambda) ^ t * productPotential p lambda (P.rank s) :=
      mul_le_mul_of_nonneg_left
        (killedPotential_le_productPotential p lambda hlambda hrate (le_refl _)) (pow_nonneg hq t)
    _ = _ := by ring

end LeanPool.SingleCopyStabilizer.GeometricDomination
