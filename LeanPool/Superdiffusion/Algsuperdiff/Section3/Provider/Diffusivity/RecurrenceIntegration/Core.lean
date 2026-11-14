/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.GeometricSums
public import Mathlib.Tactic.Polyrith

/-!
# Core

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic recurrence integration: local estimates

This file contains the exact scalar increment/comparator objects and Steps 1--2 of
ABK26 `l.integrate.approx.recurrence`.  It is purely deterministic.  The
recurrence increment and comparator use the directional `cstar`; the Frobenius
envelope constant does not enter these local estimates.

The geometric-sum identities are consumed from the current public
`Provider.Stream.GeometricSums` A.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

open scoped BigOperators
open Finset

noncomputable section

/-- The geometric term `3^(2 gamma k)` used throughout the recurrence. -/
def geometricTerm (gamma : ℝ) (k : ℤ) : ℝ :=
  (3 : ℝ) ^ (2 * gamma * (k : ℝ))

/-- The directional increment `A_{n,m}` from `e.A.def`. -/
def recurrenceIncrement (cstar gamma : ℝ) (n m : ℤ) : ℝ :=
  cstar * Real.log 3 *
    ∑ k ∈ Finset.Icc (n + 1) m, (3 : ℝ) ^ (2 * gamma * (k : ℝ))

/-- The exact-increment comparator `T_m`. -/
def recurrenceComparator (nu cstar gamma : ℝ) (m : ℤ) : ℝ :=
  nu ^ 2 + cstar * Stream.Kgamma gamma * geometricTerm gamma m

namespace Internal

@[simp] theorem geometricTerm_pos (gamma : ℝ) (k : ℤ) :
    0 < geometricTerm gamma k :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The exact comparator increment `T_m - T_n = 2 A_{n,m}`. -/
theorem recurrenceComparator_sub_eq_two_increment
    {nu cstar gamma : ℝ} (hgamma : 0 < gamma) {n m : ℤ} (hnm : n ≤ m) :
    recurrenceComparator nu cstar gamma m - recurrenceComparator nu cstar gamma n =
      2 * recurrenceIncrement cstar gamma n m := by
  have hset : Finset.Icc (n + 1) m = Finset.Ioc n m := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsum := Stream.two_mul_log_three_mul_sum_Ioc_rpow hgamma hnm
  change 2 * Real.log 3 * ∑ j ∈ Finset.Ioc n m, geometricTerm gamma j =
    Stream.Kgamma gamma * (geometricTerm gamma m - geometricTerm gamma n) at hsum
  calc
    recurrenceComparator nu cstar gamma m - recurrenceComparator nu cstar gamma n =
        cstar * Stream.Kgamma gamma *
          (geometricTerm gamma m - geometricTerm gamma n) := by
            rw [recurrenceComparator, recurrenceComparator]
            ring
    _ = cstar * (2 * Real.log 3 * ∑ j ∈ Finset.Ioc n m,
          geometricTerm gamma j) := by
      rw [hsum]
      ring
    _ = 2 * recurrenceIncrement cstar gamma n m := by
      rw [recurrenceIncrement, hset]
      simp only [geometricTerm]
      ring

/-- A crude bound used in Step 2. -/
theorem log_three_le_two : Real.log 3 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith only [h]

/-- Upper half of `e.local.square.increments`: `x² − y² − 2A ≤ (3ε + (A yi²)² +
2D)(y² + 2A)`. Obtained by squaring the upper recurrence bound. -/
lemma square_increment_upper
    {x y yi ε A D : ℝ} (hx : 0 < x) (hy : 0 < y) (hyi : 0 < yi)
    (hyyi : y * yi = 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hu : x ≤ (1 + ε) * y + A * yi) :
    x ^ 2 - y ^ 2 - 2 * A ≤ (3 * ε + (A * yi ^ 2) ^ 2 + 2 * D) * (y ^ 2 + 2 * A) := by
  have hyy : y ^ 2 * yi ^ 2 = 1 := by rw [← mul_pow, hyyi, one_pow]
  -- square the upper bound
  have hB : 0 ≤ (1 + ε) * y + A * yi := by positivity
  have hx2 : x ^ 2 ≤ ((1 + ε) * y + A * yi) ^ 2 :=
    pow_le_pow_left₀ hx.le hu 2
  -- expand using y*yi = 1
  have hkey : x ^ 2 ≤ (1 + ε) ^ 2 * y ^ 2 + 2 * (1 + ε) * A + A ^ 2 * yi ^ 2 := by
    have hexp : ((1 + ε) * y + A * yi) ^ 2
        = (1 + ε) ^ 2 * y ^ 2 + 2 * (1 + ε) * A * (y * yi) + A ^ 2 * yi ^ 2 := by
      ring
    rw [hexp, hyyi, mul_one] at hx2
    exact hx2
  -- replace A² yi² by (A yi²)² y²
  have hA2 : A ^ 2 * yi ^ 2 = (A * yi ^ 2) ^ 2 * y ^ 2 := by
    have : (A * yi ^ 2) ^ 2 * y ^ 2 = A ^ 2 * yi ^ 2 * (y ^ 2 * yi ^ 2) := by ring
    rw [this, hyy, mul_one]
  rw [hA2] at hkey
  -- finish: the gap − LHS is a sum of manifestly nonnegative products
  linarith only [hkey,
    mul_nonneg (mul_nonneg hε0 (by linarith only [hε1] : (0:ℝ) ≤ 1 - ε)) (sq_nonneg y),
    mul_nonneg hε0 hA,
    mul_nonneg (sq_nonneg (A * yi ^ 2)) hA,
    mul_nonneg hD (sq_nonneg y),
    mul_nonneg hD hA]

/-- Lower half of `e.local.square.increments`: `x² − y² − 2A ≥ −2(ε + D)(y² +
2A)`, obtained by squaring the lower recurrence bound and the elementary
inequality `(1−u)⁻² ≥ 1 + 2u` (equivalently `(1+2u)(1−u)² ≤ 1` for `u < 1`) with
`u = A yi² − D`. -/
lemma square_increment_lower_strong
    {x y yi ε A D : ℝ} (hx : 0 < x) (hy : 0 < y) (_hyi : 0 < yi)
    (hyyi : y * yi = 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hl : (1 - ε) * y ≤ (1 - A * yi ^ 2 + D) * x) :
    -(2 * (ε + D) * (y ^ 2 + 2 * A)) ≤ x ^ 2 - y ^ 2 - 2 * A := by
  have hyy : y ^ 2 * yi ^ 2 = 1 := by rw [← mul_pow, hyyi, one_pow]
  -- A = (A yi²) y²
  have hAeq : A = A * yi ^ 2 * y ^ 2 := by
    have : A * yi ^ 2 * y ^ 2 = A * (y ^ 2 * yi ^ 2) := by ring
    rw [this, hyy, mul_one]
  -- 1 − A yi² + D > 0
  have hposfac : 0 < 1 - A * yi ^ 2 + D := by
    by_contra h
    push Not at h
    have h1 : (1 - A * yi ^ 2 + D) * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hx.le
    have h2 : 0 < (1 - ε) * y := by
      apply mul_pos (by linarith only [hε1]) hy
    linarith only [h1, h2, hl]
  set u := A * yi ^ 2 - D with hu_def
  have hposu : 0 < 1 - u := by rw [hu_def]; linarith only [hposfac]
  -- square the lower bound
  have hsq : ((1 - ε) * y) ^ 2 ≤ ((1 - u) * x) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg (by linarith only [hε1] : (0:ℝ) ≤ 1 - ε) hy.le) _ 2
    have hrw : (1 - u) * x = (1 - A * yi ^ 2 + D) * x := by rw [hu_def]; ring
    rw [hrw]; exact hl
  -- (1+2u)(1-u)² ≤ 1 for u < 1, i.e. 0 ≤ 1 − (1+2u)(1−u)²
  have hcert : 0 ≤ 1 - (1 + 2 * u) * (1 - u) ^ 2 := by
    linarith only [mul_nonneg (sq_nonneg u) (by linarith only [hposu] : (0:ℝ) ≤ 3 - 2 * u)]
  -- S:= x² − (1+2u)(1−ε)² y² ≥ 0
  have hposu2 : 0 < (1 - u) ^ 2 := pow_pos hposu 2
  have hnn : 0 ≤ (1 - ε) ^ 2 * y ^ 2 * (1 - (1 + 2 * u) * (1 - u) ^ 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hcert
  have hcS : 0 ≤ (1 - u) ^ 2 * (x ^ 2 - (1 + 2 * u) * (1 - ε) ^ 2 * y ^ 2) := by
    linarith only [hsq, hnn]
  have hstar : 0 ≤ x ^ 2 - (1 + 2 * u) * (1 - ε) ^ 2 * y ^ 2 :=
    (mul_nonneg_iff_of_pos_left hposu2).mp hcS
  rw [hu_def] at hstar
  -- convert to the paper's form, folding A yi² y² = A
  have hstar' : 0 ≤ x ^ 2
      - ((1 - ε) ^ 2 * y ^ 2 + 2 * (1 - ε) ^ 2 * A - 2 * (1 - ε) ^ 2 * D * y ^ 2) := by
    have hconv : (1 + 2 * (A * yi ^ 2 - D)) * (1 - ε) ^ 2 * y ^ 2
        = (1 - ε) ^ 2 * y ^ 2 + 2 * (1 - ε) ^ 2 * A - 2 * (1 - ε) ^ 2 * D * y ^ 2 := by
      have hexp : (1 + 2 * (A * yi ^ 2 - D)) * (1 - ε) ^ 2 * y ^ 2
          = (1 - ε) ^ 2 * y ^ 2 + 2 * (1 - ε) ^ 2 * (A * yi ^ 2 * y ^ 2)
            - 2 * (1 - ε) ^ 2 * D * y ^ 2 := by ring
      rw [hexp, ← hAeq]
    rw [← hconv]; exact hstar
  -- conclude: actual − target is a sum of nonnegative products
  linarith only [hstar',
    mul_nonneg (sq_nonneg ε) (sq_nonneg y),
    mul_nonneg (sq_nonneg ε) hA,
    mul_nonneg (mul_nonneg (mul_nonneg hε0 hD) (sq_nonneg y))
      (by linarith only [hε1] : (0:ℝ) ≤ 2 - ε),
    mul_nonneg hD hA]

/-- `e.double.local.square.increment`: the two-sided bound on the squared
increment. -/
theorem double_local_square_increment
    {x y yi ε A D : ℝ} (hx : 0 < x) (hy : 0 < y) (hyi : 0 < yi)
    (hyyi : y * yi = 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hu : x ≤ (1 + ε) * y + A * yi)
    (hl : (1 - ε) * y ≤ (1 - A * yi ^ 2 + D) * x) :
    |x ^ 2 - y ^ 2 - 2 * A|
      ≤ (3 * ε + (A * yi ^ 2) ^ 2 + 2 * D) * (y ^ 2 + 2 * A) := by
  have hup := square_increment_upper hx hy hyi hyyi hε0 (le_of_lt hε1) hA hD hu
  have hlo := square_increment_lower_strong hx hy hyi hyyi hε0 hε1 hA hD hl
  rw [abs_le]
  refine ⟨?_, hup⟩
  -- − ≤ −2(ε+D)(y²+2A) ≤ x²−y²−2A
  have hgap : 2 * (ε + D) * (y ^ 2 + 2 * A)
      ≤ (3 * ε + (A * yi ^ 2) ^ 2 + 2 * D) * (y ^ 2 + 2 * A) := by
    have hfac : 0 ≤ y ^ 2 + 2 * A := by positivity
    linarith only [mul_nonneg (add_nonneg hε0 (sq_nonneg (A * yi ^ 2))) hfac]
  linarith only [hlo, hgap]


open scoped BigOperators
open Finset

variable {ν cstar γ : ℝ}

/-- `k ↦ 3^{2γk}` is monotone for `γ > 0`. -/
lemma geometricTerm_mono (hγ : 0 < γ) {k l : ℤ} (hkl : k ≤ l) :
    geometricTerm γ k ≤ geometricTerm γ l := by
  rw [geometricTerm, geometricTerm]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
  have hkl' : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
  exact mul_le_mul_of_nonneg_left hkl' (mul_nonneg (by norm_num) hγ.le)

/-- On a unit `gamma⁻¹` step, `3^{2γm} ≤ 9·3^{2γn}`. -/
lemma geometricTerm_ratio_le (hγ : 0 < γ) {n m : ℤ}
    (hrange : (m : ℝ) ≤ (n : ℝ) + γ⁻¹) :
    geometricTerm γ m ≤ 9 * geometricTerm γ n := by
  -- geometricTerm γ m = geometricTerm γ n * 3^{2γ(m-n)}
  have hsplit : geometricTerm γ m = geometricTerm γ n * (3 : ℝ) ^ (2 * γ * ((m : ℝ) - n))
    := by
    rw [geometricTerm, geometricTerm, ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1; ring
  have hγinv : γ * γ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hγ)
  -- 2γ(m-n) ≤ 2
  have hexp_le : 2 * γ * ((m : ℝ) - n) ≤ 2 := by
    have h1 : (m : ℝ) - n ≤ γ⁻¹ := by linarith only [hrange]
    have h2 : γ * ((m : ℝ) - n) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 hγ.le
      rwa [hγinv] at this
    linarith only [h2]
  have hpow_le : (3 : ℝ) ^ (2 * γ * ((m : ℝ) - n)) ≤ (9 : ℝ) := by
    calc (3 : ℝ) ^ (2 * γ * ((m : ℝ) - n))
        ≤ (3 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
      _ = 9 := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hgn : 0 < geometricTerm γ n := geometricTerm_pos γ n
  rw [hsplit]
  calc geometricTerm γ n * (3 : ℝ) ^ (2 * γ * ((m : ℝ) - n))
      ≤ geometricTerm γ n * 9 := mul_le_mul_of_nonneg_left hpow_le hgn.le
    _ = 9 * geometricTerm γ n := by ring

/-- `A_{n,m} ≥ 0`. -/
lemma recurrenceIncrement_nonneg (hcstar : 0 ≤ cstar) (n m : ℤ) : 0 ≤ recurrenceIncrement
  cstar γ n m := by
  rw [recurrenceIncrement]
  apply mul_nonneg (mul_nonneg hcstar (Real.log_nonneg (by norm_num)))
  apply Finset.sum_nonneg
  intro k _
  exact (geometricTerm_pos γ k).le

/-- `A_{n,m} ≤ c⋆ (log 3)(m−n) 3^{2γm}` (each of the `m−n` terms is `≤ 3^{2γm}`). -/
lemma recurrenceIncrement_le_count (hγ : 0 < γ) (hcstar : 0 ≤ cstar) {n m : ℤ} (hnm : n
  ≤ m) :
    recurrenceIncrement cstar γ n m ≤ cstar * Real.log 3 * ((m : ℝ) - n) * geometricTerm γ
      m := by
  have hsum : ∑ k ∈ Finset.Icc (n + 1) m, geometricTerm γ k
      ≤ ((m : ℝ) - n) * geometricTerm γ m := by
    have h1 : ∑ k ∈ Finset.Icc (n + 1) m, geometricTerm γ k
        ≤ ∑ _k ∈ Finset.Icc (n + 1) m, geometricTerm γ m := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_Icc] at hk
      exact geometricTerm_mono hγ (by omega : k ≤ m)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have hcard : (Finset.Icc (n + 1) m).card = (m - n).toNat := by
      rw [Int.card_Icc]; congr 1; omega
    have hcast : ((Finset.Icc (n + 1) m).card : ℝ) = (m : ℝ) - n := by
      have h2 : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
      rw [hcard]; exact_mod_cast h2
    rw [hcast] at h1
    exact h1
  have hcl : 0 ≤ cstar * Real.log 3 :=
    mul_nonneg hcstar (Real.log_nonneg (by norm_num))
  rw [recurrenceIncrement]
  calc cstar * Real.log 3 * ∑ k ∈ Finset.Icc (n + 1) m, geometricTerm γ k
      ≤ cstar * Real.log 3 * (((m : ℝ) - n) * geometricTerm γ m) :=
        mul_le_mul_of_nonneg_left hsum hcl
    _ = cstar * Real.log 3 * ((m : ℝ) - n) * geometricTerm γ m := by ring

/-- `T_n ≥ ν²`. -/
lemma nu_sq_le_recurrenceComparator (hcstar : 0 ≤ cstar) (hγ : 0 < γ) (n : ℤ) :
    ν ^ 2 ≤ recurrenceComparator ν cstar γ n := by
  rw [recurrenceComparator]
  have hK : 0 ≤ Stream.Kgamma γ := le_trans (by positivity) (Stream.le_Kgamma hγ)
  have hnn : 0 ≤ cstar * Stream.Kgamma γ * geometricTerm γ n :=
    mul_nonneg (mul_nonneg hcstar hK) (geometricTerm_pos γ n).le
  linarith only [hnn]

/-- `T_n ≥ c⋆ γ⁻¹ 3^{2γn}` (from `K_γ ≥ γ⁻¹`). -/
lemma cstar_geometricTerm_le_recurrenceComparator (_hν : 0 < ν) (hcstar : 0 ≤ cstar) (hγ :
  0 < γ) (n : ℤ) :
    cstar * γ⁻¹ * geometricTerm γ n ≤ recurrenceComparator ν cstar γ n := by
  rw [recurrenceComparator]
  have hK : γ⁻¹ ≤ Stream.Kgamma γ := Stream.le_Kgamma hγ
  have hg : 0 < geometricTerm γ n := geometricTerm_pos γ n
  have h1 : cstar * γ⁻¹ * geometricTerm γ n ≤ cstar * Stream.Kgamma γ * geometricTerm γ
    n := by
    apply mul_le_mul_of_nonneg_right _ hg.le
    exact mul_le_mul_of_nonneg_left hK hcstar
  linarith only [h1, sq_nonneg ν]

/-- The `min` factor `min{ν⁻²c⋆3^{2γn}, γ}` used in the two Step-2 estimates. -/
private lemma one_le_nu_inv_mul_recurrenceComparator (hν : 0 < ν) (hcstar : 0 < cstar) (hγ :
  0 < γ) (n : ℤ) :
    1 ≤ (ν ^ 2)⁻¹ * recurrenceComparator ν cstar γ n := by
  have hnu2pos : 0 < ν ^ 2 := pow_pos hν 2
  have hTnu : ν ^ 2 ≤ recurrenceComparator ν cstar γ n := nu_sq_le_recurrenceComparator
    hcstar.le hγ n
  linarith only [mul_nonneg (inv_nonneg.mpr hnu2pos.le)
      (by linarith only [hTnu] : (0:ℝ) ≤ recurrenceComparator ν cstar γ n - ν ^ 2),
    inv_mul_cancel₀ (ne_of_gt hnu2pos)]

/-- `e.chunk` display:
`2 A_{n,m} ≤ 40 · min{ν⁻²c⋆3^{2γn}, γ} · (m−n) · T_n`. -/
lemma two_recurrenceIncrement_min_bound (hν : 0 < ν) (hcstar : 0 < cstar)
    (hγ : 0 < γ) {n m : ℤ} (hnm : n ≤ m) (hrange : (m : ℝ) ≤ (n : ℝ) + γ⁻¹) :
    2 * recurrenceIncrement cstar γ n m
      ≤ 40 * min ((ν ^ 2)⁻¹ * cstar * geometricTerm γ n) γ * ((m : ℝ) - n) *
        recurrenceComparator ν cstar γ n := by
  have hgn : 0 < geometricTerm γ n := geometricTerm_pos γ n
  have hmn0 : (0 : ℝ) ≤ (m : ℝ) - n := by
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith only [hnm']
  have hTn0 : 0 ≤ recurrenceComparator ν cstar γ n := le_trans (sq_nonneg ν)
    (nu_sq_le_recurrenceComparator hcstar.le hγ n)
  have hfac_nn : 0 ≤ cstar * geometricTerm γ n * ((m : ℝ) - n) :=
    mul_nonneg (mul_nonneg hcstar.le hgn.le) hmn0
  -- 2A ≤ 18 c⋆ (log 3)(m−n) 3^{2γn}
  have hAbound : 2 * recurrenceIncrement cstar γ n m
      ≤ 18 * cstar * Real.log 3 * ((m : ℝ) - n) * geometricTerm γ n := by
    have h1 : recurrenceIncrement cstar γ n m
        ≤ cstar * Real.log 3 * ((m : ℝ) - n) * geometricTerm γ m :=
          recurrenceIncrement_le_count hγ hcstar.le hnm
    have h2 : geometricTerm γ m ≤ 9 * geometricTerm γ n :=
      geometricTerm_ratio_le hγ hrange
    have hnn : 0 ≤ cstar * Real.log 3 * ((m : ℝ) - n) :=
      mul_nonneg (mul_nonneg hcstar.le (Real.log_nonneg (by norm_num))) hmn0
    linarith only [h1, mul_le_mul_of_nonneg_left h2 hnn]
  have hge1 : 1 ≤ (ν ^ 2)⁻¹ * recurrenceComparator ν cstar γ n :=
    one_le_nu_inv_mul_recurrenceComparator hν hcstar hγ n
  -- branch inequalities
  have hbP : 2 * recurrenceIncrement cstar γ n m
      ≤ 40 * ((m : ℝ) - n) * recurrenceComparator ν cstar γ n * ((ν ^ 2)⁻¹ * cstar *
        geometricTerm γ n) := by
    have hscalar : 18 * Real.log 3 ≤ 40 * ((ν ^ 2)⁻¹ * recurrenceComparator ν cstar γ n)
      := by
      linarith only [hge1, log_three_le_two]
    calc 2 * recurrenceIncrement cstar γ n m
        ≤ 18 * cstar * Real.log 3 * ((m : ℝ) - n) * geometricTerm γ n := hAbound
      _ = (cstar * geometricTerm γ n * ((m : ℝ) - n)) * (18 * Real.log 3) := by ring
      _ ≤ (cstar * geometricTerm γ n * ((m : ℝ) - n)) * (40 * ((ν ^ 2)⁻¹ *
        recurrenceComparator ν cstar γ n)) :=
          mul_le_mul_of_nonneg_left hscalar hfac_nn
      _ = 40 * ((m : ℝ) - n) * recurrenceComparator ν cstar γ n * ((ν ^ 2)⁻¹ * cstar *
        geometricTerm γ n) := by ring
  have hbγ : 2 * recurrenceIncrement cstar γ n m
      ≤ 40 * ((m : ℝ) - n) * recurrenceComparator ν cstar γ n * γ := by
    have hb2 : cstar * γ⁻¹ * geometricTerm γ n ≤ recurrenceComparator ν cstar γ n :=
      cstar_geometricTerm_le_recurrenceComparator hν hcstar.le hγ n
    have hscalar : 18 * cstar * Real.log 3 * geometricTerm γ n ≤ 40 * γ *
      recurrenceComparator ν cstar γ n := by
      have h := mul_le_mul_of_nonneg_left hb2 (show (0 : ℝ) ≤ 40 * γ by positivity)
      have heq : (40 * γ) * (cstar * γ⁻¹ * geometricTerm γ n) = 40 * cstar * geometricTerm
        γ n := by
        rw [show (40 * γ) * (cstar * γ⁻¹ * geometricTerm γ n)
            = 40 * cstar * geometricTerm γ n * (γ * γ⁻¹) by ring,
          mul_inv_cancel₀ (ne_of_gt hγ), mul_one]
      rw [heq] at h
      linarith only [h, mul_nonneg hcstar.le hgn.le,
        mul_le_mul_of_nonneg_right log_three_le_two (mul_nonneg hcstar.le hgn.le)]
    calc 2 * recurrenceIncrement cstar γ n m
        ≤ 18 * cstar * Real.log 3 * ((m : ℝ) - n) * geometricTerm γ n := hAbound
      _ = ((m : ℝ) - n) * (18 * cstar * Real.log 3 * geometricTerm γ n) := by ring
      _ ≤ ((m : ℝ) - n) * (40 * γ * recurrenceComparator ν cstar γ n) :=
          mul_le_mul_of_nonneg_left hscalar hmn0
      _ = 40 * ((m : ℝ) - n) * recurrenceComparator ν cstar γ n * γ := by ring
  -- combine via `a * min b c = min (a*b) (a*c)`
  have hK0 : 0 ≤ 40 * ((m : ℝ) - n) * recurrenceComparator ν cstar γ n :=
    mul_nonneg (mul_nonneg (by norm_num) hmn0) hTn0
  rw [show 40 * min ((ν ^ 2)⁻¹ * cstar * geometricTerm γ n) γ * ((m : ℝ) - n) *
    recurrenceComparator ν cstar γ n
      = (40 * ((m : ℝ) - n) * recurrenceComparator ν cstar γ n) * min ((ν ^ 2)⁻¹ * cstar
        * geometricTerm γ n) γ by ring,
    mul_min_of_nonneg _ _ hK0]
  refine le_min ?_ ?_
  · calc 2 * recurrenceIncrement cstar γ n m
        ≤ 40 * ((m : ℝ) - n) * recurrenceComparator ν cstar γ n * ((ν ^ 2)⁻¹ * cstar *
          geometricTerm γ n) := hbP
      _ = 40 * ((m : ℝ) - n) * recurrenceComparator ν cstar γ n * ((ν ^ 2)⁻¹ * cstar *
        geometricTerm γ n) := rfl
  · exact hbγ

/-- `e.chunk` display:
`c⋆ 3^{2γm} ≤ 9 · min{ν⁻²c⋆3^{2γn}, γ} · T_n`
(the paper's `T_n⁻¹3^{2γm} ≤ C c⋆⁻¹ min{…}` in division-free form). -/
lemma cstar_geometricTerm_min_bound (hν : 0 < ν) (hcstar : 0 < cstar)
    (hγ : 0 < γ) {n m : ℤ} (_hnm : n ≤ m)
    (hrange : (m : ℝ) ≤ (n : ℝ) + γ⁻¹) :
    cstar * geometricTerm γ m
      ≤ 9 * min ((ν ^ 2)⁻¹ * cstar * geometricTerm γ n) γ * recurrenceComparator ν
        cstar γ n := by
  have hgn : 0 < geometricTerm γ n := geometricTerm_pos γ n
  have hTn0 : 0 ≤ recurrenceComparator ν cstar γ n := le_trans (sq_nonneg ν)
    (nu_sq_le_recurrenceComparator hcstar.le hγ n)
  have hratio : geometricTerm γ m ≤ 9 * geometricTerm γ n :=
    geometricTerm_ratio_le hγ hrange
  have hb1 : cstar * geometricTerm γ m ≤ 9 * cstar * geometricTerm γ n :=
    calc cstar * geometricTerm γ m ≤ cstar * (9 * geometricTerm γ n) :=
          mul_le_mul_of_nonneg_left hratio hcstar.le
      _ = 9 * cstar * geometricTerm γ n := by ring
  have hge1 : 1 ≤ (ν ^ 2)⁻¹ * recurrenceComparator ν cstar γ n :=
    one_le_nu_inv_mul_recurrenceComparator hν hcstar hγ n
  have hbP : cstar * geometricTerm γ m
      ≤ 9 * recurrenceComparator ν cstar γ n * ((ν ^ 2)⁻¹ * cstar * geometricTerm γ n)
        := by
    have hscalar : (9 : ℝ) ≤ 9 * ((ν ^ 2)⁻¹ * recurrenceComparator ν cstar γ n) := by
      linarith only [hge1]
    calc cstar * geometricTerm γ m
        ≤ 9 * cstar * geometricTerm γ n := hb1
      _ = (cstar * geometricTerm γ n) * 9 := by ring
      _ ≤ (cstar * geometricTerm γ n) * (9 * ((ν ^ 2)⁻¹ * recurrenceComparator ν cstar
        γ n)) :=
          mul_le_mul_of_nonneg_left hscalar (mul_nonneg hcstar.le hgn.le)
      _ = 9 * recurrenceComparator ν cstar γ n * ((ν ^ 2)⁻¹ * cstar * geometricTerm γ n)
        := by ring
  have hbγ : cstar * geometricTerm γ m ≤ 9 * recurrenceComparator ν cstar γ n * γ := by
    have hb2 : cstar * γ⁻¹ * geometricTerm γ n ≤ recurrenceComparator ν cstar γ n :=
      cstar_geometricTerm_le_recurrenceComparator hν hcstar.le hγ n
    have hstep : 9 * cstar * geometricTerm γ n ≤ 9 * recurrenceComparator ν cstar γ n * γ
      := by
      have h := mul_le_mul_of_nonneg_left hb2 (show (0 : ℝ) ≤ 9 * γ by positivity)
      have heq : (9 * γ) * (cstar * γ⁻¹ * geometricTerm γ n) = 9 * cstar * geometricTerm
        γ n := by
        rw [show (9 * γ) * (cstar * γ⁻¹ * geometricTerm γ n)
            = 9 * cstar * geometricTerm γ n * (γ * γ⁻¹) by ring,
          mul_inv_cancel₀ (ne_of_gt hγ), mul_one]
      rw [heq] at h
      linarith only [h]
    linarith only [hb1, hstep]
  have hK0 : 0 ≤ 9 * recurrenceComparator ν cstar γ n := mul_nonneg (by norm_num) hTn0
  rw [show 9 * min ((ν ^ 2)⁻¹ * cstar * geometricTerm γ n) γ * recurrenceComparator ν
    cstar γ n
      = (9 * recurrenceComparator ν cstar γ n) * min ((ν ^ 2)⁻¹ * cstar * geometricTerm γ
        n) γ by ring,
    mul_min_of_nonneg _ _ hK0]
  exact le_min hbP hbγ


open scoped BigOperators

/-- `3^{4γm} = (3^{2γm})²`. -/
lemma geometricTerm_two_gamma (γ : ℝ) (m : ℤ) : geometricTerm (2 * γ) m = (geometricTerm
  γ m) ^ 2 := by
  rw [geometricTerm, geometricTerm, sq, ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1; ring

/-- Pure real-algebra core of Step 2: everything downstream of the two
min-estimates and the sandwich, over abstract reals (no `rpow`/`def` inside,
so the numeric tactics stay polynomial). Here `sn, sm, A, g, Tn, Tm, mn, μ0, μ`
abstract `s_n, s_m, A_{n,m}, 3^{2γm}, T_n, T_m, m−n, min{ν⁻²c⋆3^{2γn},γ},
min{ν⁻²c⋆γ⁻¹3^{2γn},1}`. -/
private lemma chunk_algebra
    {sn sm A g Tn Tm mn μ0 μ cstar γ E F : ℝ}
    (hsn2pos : 0 < sn ^ 2) (hyi2 : (sn⁻¹) ^ 2 * sn ^ 2 = 1)
    (hAnn : 0 ≤ A) (hcstar0 : 0 ≤ cstar) (hg0 : 0 ≤ g) (hc2 : 0 < cstar ^ 2)
    (hγ : 0 < γ) (hE : 1 ≤ E) (hF : 1 ≤ F) (hmn0 : 0 ≤ mn)
    (hμ0nn : 0 ≤ μ0) (hTmpos : 0 < Tm)
    (hF4 : 2 * A ≤ 40 * μ0 * mn * Tn) (hF5 : cstar * g ≤ 9 * μ0 * Tn)
    (hTle : Tn ≤ 2 * sn ^ 2) (hSbound : sn ^ 2 + 2 * A ≤ 2 * Tm)
    (hμ0sq : μ0 ^ 2 = γ ^ 2 * μ ^ 2)
    (hstep1 : |sm ^ 2 - sn ^ 2 - 2 * A|
      ≤ (3 * (E * γ) + (A * (sn⁻¹) ^ 2) ^ 2 + 2 * (F * mn ^ 2 * (sn⁻¹) ^ 4 * g ^ 2))
        * (sn ^ 2 + 2 * A)) :
    |sm ^ 2 - sn ^ 2 - 2 * A|
      ≤ 3200 * γ * (E + (1 + (cstar ^ 2)⁻¹ * F) * μ ^ 2 * γ * mn ^ 2) * Tm := by
  have hc2nn : 0 ≤ (cstar ^ 2)⁻¹ := inv_nonneg.mpr hc2.le
  -- (i)  A sn⁻² ≤ 40 μ0 mn
  have hi : A * (sn⁻¹) ^ 2 ≤ 40 * μ0 * mn := by
    have hAle : A ≤ 40 * μ0 * mn * sn ^ 2 := by
      linarith only [hF4, mul_nonneg (mul_nonneg hμ0nn hmn0)
        (by linarith only [hTle] : (0:ℝ) ≤ 2 * sn ^ 2 - Tn)]
    have hkey : (A * (sn⁻¹) ^ 2) * sn ^ 2 = A := by
      calc (A * (sn⁻¹) ^ 2) * sn ^ 2 = A * ((sn⁻¹) ^ 2 * sn ^ 2) := by ring
        _ = A * 1 := by rw [hyi2]
        _ = A := by ring
    have hstep : (A * (sn⁻¹) ^ 2) * sn ^ 2 ≤ (40 * μ0 * mn) * sn ^ 2 := by
      rw [hkey]; linarith only [hAle]
    exact le_of_mul_le_mul_right hstep hsn2pos
  -- (ii)  c⋆ g sn⁻² ≤ 18 μ0
  have hii : cstar * g * (sn⁻¹) ^ 2 ≤ 18 * μ0 := by
    have hcgle : cstar * g ≤ 18 * μ0 * sn ^ 2 := by
      linarith only [hF5,
        mul_nonneg hμ0nn (by linarith only [hTle] : (0:ℝ) ≤ 2 * sn ^ 2 - Tn)]
    have hkey : (cstar * g * (sn⁻¹) ^ 2) * sn ^ 2 = cstar * g := by
      calc (cstar * g * (sn⁻¹) ^ 2) * sn ^ 2 = cstar * g * ((sn⁻¹) ^ 2 * sn ^ 2) := by ring
        _ = cstar * g * 1 := by rw [hyi2]
        _ = cstar * g := by ring
    have hstep : (cstar * g * (sn⁻¹) ^ 2) * sn ^ 2 ≤ (18 * μ0) * sn ^ 2 := by
      rw [hkey]; linarith only [hcgle]
    exact le_of_mul_le_mul_right hstep hsn2pos
  -- squared middle terms
  have hi_nn : 0 ≤ A * (sn⁻¹) ^ 2 := mul_nonneg hAnn (sq_nonneg _)
  have hMid1 : (A * (sn⁻¹) ^ 2) ^ 2 ≤ 1600 * μ0 ^ 2 * mn ^ 2 := by
    calc (A * (sn⁻¹) ^ 2) ^ 2 ≤ (40 * μ0 * mn) ^ 2 := pow_le_pow_left₀ hi_nn hi 2
      _ = 1600 * μ0 ^ 2 * mn ^ 2 := by ring
  have hii_nn : 0 ≤ cstar * g * (sn⁻¹) ^ 2 :=
    mul_nonneg (mul_nonneg hcstar0 hg0) (sq_nonneg _)
  have hgyi2 : (g * (sn⁻¹) ^ 2) ^ 2 ≤ 324 * (cstar ^ 2)⁻¹ * μ0 ^ 2 := by
    have hsq : (cstar * g * (sn⁻¹) ^ 2) ^ 2 ≤ (18 * μ0) ^ 2 := pow_le_pow_left₀ hii_nn hii 2
    have hX : (g * (sn⁻¹) ^ 2) ^ 2 = (cstar ^ 2)⁻¹ * ((cstar * g * (sn⁻¹) ^ 2) ^ 2) := by
      rw [show (cstar * g * (sn⁻¹) ^ 2) ^ 2 = cstar ^ 2 * (g * (sn⁻¹) ^ 2) ^ 2 by ring,
        ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc2), one_mul]
    rw [hX]
    calc (cstar ^ 2)⁻¹ * ((cstar * g * (sn⁻¹) ^ 2) ^ 2)
        ≤ (cstar ^ 2)⁻¹ * ((18 * μ0) ^ 2) := mul_le_mul_of_nonneg_left hsq hc2nn
      _ = 324 * (cstar ^ 2)⁻¹ * μ0 ^ 2 := by ring
  have hDrw : F * mn ^ 2 * (sn⁻¹) ^ 4 * g ^ 2 = F * mn ^ 2 * (g * (sn⁻¹) ^ 2) ^ 2 := by ring
  have hFmn_nn : 0 ≤ 2 * F * mn ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hF])) (sq_nonneg _)
  have hMid2 : 2 * (F * mn ^ 2 * (sn⁻¹) ^ 4 * g ^ 2)
      ≤ 648 * (cstar ^ 2)⁻¹ * F * mn ^ 2 * μ0 ^ 2 := by
    rw [hDrw]
    calc 2 * (F * mn ^ 2 * (g * (sn⁻¹) ^ 2) ^ 2)
        = (2 * F * mn ^ 2) * (g * (sn⁻¹) ^ 2) ^ 2 := by ring
      _ ≤ (2 * F * mn ^ 2) * (324 * (cstar ^ 2)⁻¹ * μ0 ^ 2) :=
          mul_le_mul_of_nonneg_left hgyi2 hFmn_nn
      _ = 648 * (cstar ^ 2)⁻¹ * F * mn ^ 2 * μ0 ^ 2 := by ring
  have hSnn : 0 ≤ sn ^ 2 + 2 * A := add_nonneg (sq_nonneg sn) (by linarith only [hAnn])
  have hBr : 3 * (E * γ) + (A * (sn⁻¹) ^ 2) ^ 2 + 2 * (F * mn ^ 2 * (sn⁻¹) ^ 4 * g ^ 2)
      ≤ 3 * (E * γ) + 1600 * μ0 ^ 2 * mn ^ 2
        + 648 * (cstar ^ 2)⁻¹ * F * mn ^ 2 * μ0 ^ 2 := by
    linarith only [hMid1, hMid2]
  have hbr'_nn : 0 ≤ 3 * (E * γ) + 1600 * μ0 ^ 2 * mn ^ 2
      + 648 * (cstar ^ 2)⁻¹ * F * mn ^ 2 * μ0 ^ 2 := by
    have h1 : 0 ≤ E * γ := mul_nonneg (by linarith only [hE]) hγ.le
    have h2 : 0 ≤ μ0 ^ 2 * mn ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have h3 : 0 ≤ (cstar ^ 2)⁻¹ * F * mn ^ 2 * μ0 ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hc2nn (by linarith only [hF])) (sq_nonneg _))
        (sq_nonneg _)
    linarith only [h1, h2, h3]
  have hRHS := mul_le_mul hBr hSbound hSnn hbr'_nn
  have hfinal : (3 * (E * γ) + 1600 * μ0 ^ 2 * mn ^ 2
        + 648 * (cstar ^ 2)⁻¹ * F * mn ^ 2 * μ0 ^ 2) * (2 * Tm)
      ≤ 3200 * γ * (E + (1 + (cstar ^ 2)⁻¹ * F) * μ ^ 2 * γ * mn ^ 2) * Tm := by
    rw [hμ0sq]
    have hpE : 0 ≤ E * γ * Tm := mul_nonneg (mul_nonneg (by linarith only [hE]) hγ.le) hTmpos.le
    have hpF : 0 ≤ (cstar ^ 2)⁻¹ * F * γ ^ 2 * μ ^ 2 * mn ^ 2 * Tm :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc2nn
        (by linarith only [hF]))
        (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)) hTmpos.le
    have hexp : 3200 * γ * (E + (1 + (cstar ^ 2)⁻¹ * F) * μ ^ 2 * γ * mn ^ 2) * Tm
        - (3 * (E * γ) + 1600 * (γ ^ 2 * μ ^ 2) * mn ^ 2
            + 648 * (cstar ^ 2)⁻¹ * F * mn ^ 2 * (γ ^ 2 * μ ^ 2)) * (2 * Tm)
        = 3194 * (E * γ * Tm)
          + 1904 * ((cstar ^ 2)⁻¹ * F * γ ^ 2 * μ ^ 2 * mn ^ 2 * Tm) := by ring
    linarith only [hpE, hpF, hexp]
  calc |sm ^ 2 - sn ^ 2 - 2 * A|
      ≤ (3 * (E * γ) + (A * (sn⁻¹) ^ 2) ^ 2 + 2 * (F * mn ^ 2 * (sn⁻¹) ^ 4 * g ^ 2))
        * (sn ^ 2 + 2 * A) := hstep1
    _ ≤ (3 * (E * γ) + 1600 * μ0 ^ 2 * mn ^ 2
          + 648 * (cstar ^ 2)⁻¹ * F * mn ^ 2 * μ0 ^ 2) * (2 * Tm) := hRHS
    _ ≤ 3200 * γ * (E + (1 + (cstar ^ 2)⁻¹ * F) * μ ^ 2 * γ * mn ^ 2) * Tm := hfinal

variable {ν cstar γ E F : ℝ} {m₀ : ℤ} {s : ℤ → ℝ}

/-- `e.chunk.increment.under.sass`. -/
theorem chunk_increment_under_sass
    (hν : 0 < ν) (hcstar : 0 < cstar) (hγ : 0 < γ)
    (hE : 1 ≤ E) (hF : 1 ≤ F) (hpos : ∀ k, 0 < s k) (hEγ : E * γ < 1)
    (hupper : ∀ a b : ℤ, b ≤ m₀ → a ≤ b → (b : ℝ) ≤ (a : ℝ) + cstar *
      γ⁻¹ →
      s b ≤ (1 + E * γ) * s a + recurrenceIncrement cstar γ a b * (s a)⁻¹)
    (hlower : ∀ a b : ℤ, b ≤ m₀ → a ≤ b → (b : ℝ) ≤ (a : ℝ) + cstar *
      γ⁻¹ →
      (1 - E * γ) * s a + recurrenceIncrement cstar γ a b * ((s a)⁻¹) ^ 2 * s b
          - F * ((b : ℝ) - (a : ℝ)) ^ 2 * ((s a)⁻¹) ^ 4 * s b * geometricTerm (2 * γ) b
        ≤ s b)
    {n m : ℤ} (hm₀ : m ≤ m₀) (hnm : n ≤ m)
    (hsourceRange : (m : ℝ) ≤ (n : ℝ) + cstar * γ⁻¹)
    (hunitRange : (m : ℝ) ≤ (n : ℝ) + γ⁻¹)
    (hsass_lo : (1 / 2) * recurrenceComparator ν cstar γ n ≤ (s n) ^ 2)
    (hsass_hi : (s n) ^ 2 ≤ 2 * recurrenceComparator ν cstar γ n) :
    |(s m) ^ 2 - (s n) ^ 2 - 2 * recurrenceIncrement cstar γ n m|
      ≤ 3200 * γ * (E + (1 + (cstar ^ 2)⁻¹ * F)
          * (min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1) ^ 2 * γ * ((m : ℝ) - n) ^ 2)
        * recurrenceComparator ν cstar γ m := by
  -- Phase A: all facts that need the concrete definitions.
  have hsnpos : 0 < s n := hpos n
  have hsmpos : 0 < s m := hpos m
  have hmn0 : (0 : ℝ) ≤ (m : ℝ) - n := by
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith only [hnm']
  have hyyi : s n * (s n)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hsnpos)
  have hyi2 : ((s n)⁻¹) ^ 2 * (s n) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hsnpos), one_pow]
  have hAnn : 0 ≤ recurrenceIncrement cstar γ n m := recurrenceIncrement_nonneg hcstar.le n m
  have hg2 : 0 < geometricTerm (2 * γ) m := geometricTerm_pos (2 * γ) m
  have hgm : 0 < geometricTerm γ m := geometricTerm_pos γ m
  have hu : s m ≤ (1 + E * γ) * s n + recurrenceIncrement cstar γ n m * (s n)⁻¹ :=
    hupper n m hm₀ hnm hsourceRange
  have hl : (1 - E * γ) * s n
      ≤ (1 - recurrenceIncrement cstar γ n m * ((s n)⁻¹) ^ 2
          + F * ((m : ℝ) - n) ^ 2 * ((s n)⁻¹) ^ 4 * geometricTerm (2 * γ) m) * s m := by
    have hlo := hlower n m hm₀ hnm hsourceRange
    have hexp : (1 - recurrenceIncrement cstar γ n m * ((s n)⁻¹) ^ 2
        + F * ((m : ℝ) - n) ^ 2 * ((s n)⁻¹) ^ 4 * geometricTerm (2 * γ) m) * s m
        = s m - recurrenceIncrement cstar γ n m * ((s n)⁻¹) ^ 2 * s m
          + F * ((m : ℝ) - n) ^ 2 * ((s n)⁻¹) ^ 4 * s m * geometricTerm (2 * γ) m := by ring
    linarith only [hlo, hexp]
  have hDnn : (0 : ℝ) ≤ F * ((m : ℝ) - n) ^ 2 * ((s n)⁻¹) ^ 4 * geometricTerm (2 * γ) m :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hF]) (sq_nonneg _))
      (pow_nonneg (inv_nonneg.mpr hsnpos.le) 4)) hg2.le
  have hstep1 := double_local_square_increment (x := s m) (y := s n) (yi := (s n)⁻¹)
    (ε := E * γ) (A := recurrenceIncrement cstar γ n m)
    (D := F * ((m : ℝ) - n) ^ 2 * ((s n)⁻¹) ^ 4 * geometricTerm (2 * γ) m)
    hsmpos hsnpos (inv_pos.mpr hsnpos) hyyi (mul_nonneg (by linarith only [hE]) hγ.le) hEγ hAnn
    hDnn hu hl
  -- fold `3^{4γm} = (3^{2γm})²` inside Step 1's bound
  rw [geometricTerm_two_gamma] at hstep1
  have hF4 := two_recurrenceIncrement_min_bound hν hcstar hγ hnm hunitRange
  have hF5 := cstar_geometricTerm_min_bound hν hcstar hγ hnm hunitRange
  have hTsub : recurrenceComparator ν cstar γ m - recurrenceComparator ν cstar γ n = 2 *
    recurrenceIncrement cstar γ n m :=
    recurrenceComparator_sub_eq_two_increment hγ hnm
  have hsn2pos : 0 < (s n) ^ 2 := pow_pos hsnpos 2
  have hμ0nn : 0 ≤ min ((ν ^ 2)⁻¹ * cstar * geometricTerm γ n) γ :=
    le_min (mul_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg ν)) hcstar.le)
      (geometricTerm_pos γ n).le) hγ.le
  have hTle : recurrenceComparator ν cstar γ n ≤ 2 * (s n) ^ 2 := by linarith only [hsass_lo]
  have hc2 : 0 < cstar ^ 2 := pow_pos hcstar 2
  have hTmpos : 0 < recurrenceComparator ν cstar γ m :=
    lt_of_lt_of_le (pow_pos hν 2) (nu_sq_le_recurrenceComparator hcstar.le hγ m)
  have hSbound : (s n) ^ 2 + 2 * recurrenceIncrement cstar γ n m ≤ 2 * recurrenceComparator
    ν cstar γ m := by
    linarith only [hsass_hi, hTsub, hAnn]
  have hμ0sq : (min ((ν ^ 2)⁻¹ * cstar * geometricTerm γ n) γ) ^ 2
      = γ ^ 2 * (min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1) ^ 2 := by
    have hμ0 : min ((ν ^ 2)⁻¹ * cstar * geometricTerm γ n) γ
        = γ * min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n) 1 := by
      rw [mul_min_of_nonneg _ _ hγ.le, mul_one]
      congr 1
      rw [show γ * ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ n)
          = (ν ^ 2)⁻¹ * cstar * geometricTerm γ n * (γ * γ⁻¹) by ring,
        mul_inv_cancel₀ (ne_of_gt hγ), mul_one]
    rw [hμ0]; ring
  -- discharge via the pure-algebra core (all rpow/def terms passed as data)
  exact chunk_algebra hsn2pos hyi2 hAnn hcstar.le hgm.le hc2 hγ hE hF hmn0 hμ0nn hTmpos
    hF4 hF5 hTle hSbound hμ0sq hstep1


end Internal

end

end Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
