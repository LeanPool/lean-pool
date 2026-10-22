/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! Frobenius noncancellation from injectivity of finite coefficient jets.
These are statements about power series in prime-power characteristic. -/

@[expose] public section
namespace CCDN
noncomputable section
open PowerSeries

private lemma powerSeries_frobenius_constant_congruence {K : Type*} [Field K]
    (p r : ℕ) [Fact p.Prime] [CharP K p] (g : PowerSeries K) :
    PowerSeries.X ^ (p ^ r) ∣ g ^ (p ^ r) - PowerSeries.C (g.constantCoeff ^ (p ^ r)) := by
  let : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
  have hh : (PowerSeries.X : PowerSeries K) ∣ g - PowerSeries.C g.constantCoeff :=
    PowerSeries.X_dvd_iff.mpr (by simp)
  have ht := pow_dvd_pow_of_dvd hh (p ^ r)
  rw [sub_pow_char_pow, ← map_pow] at ht
  exact ht

/-- A relation with Frobenius-powered series coefficients forces all their
constant terms to vanish if the low coefficient jets of f are independent. -/
private lemma powerSeries_frobenius_relation_constants {K ι : Type*} [Field K]
    [Fintype ι] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (f g : ι → PowerSeries K)
    (hjet : ∀ a : ι → K, (∀ n < p ^ r, PowerSeries.coeff n (∑ i, a i • f i) = 0) → ∀ i, a i = 0)
    (hrel : ∑ i, f i * (g i) ^ (p ^ r) = 0) : ∀ i, (g i).constantCoeff = 0 := by
  classical
  have hdiff : PowerSeries.X ^ (p ^ r) ∣
      (∑ i, f i * (g i) ^ (p ^ r)) - ∑ i, ((g i).constantCoeff ^ (p ^ r)) • f i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro i _
    have hh := dvd_mul_of_dvd_right (powerSeries_frobenius_constant_congruence p r (g i)) (f i)
    convert hh using 1
    rw [Algebra.smul_def, PowerSeries.algebraMap_eq]
    ring
  rw [hrel, zero_sub] at hdiff
  have hzero := hjet (fun i => (g i).constantCoeff ^ (p ^ r))
    (PowerSeries.X_pow_dvd_iff.mp (dvd_neg.mp hdiff))
  intro i
  exact (eq_zero_of_pow_eq_zero (hzero i))

/-- A finite family of series has a common lowest power of X; after dividing
it out, at least one remaining series has nonzero constant coefficient. -/
private lemma powerSeries_common_order_factor {K ι : Type*} [Field K] [Finite ι]
    (g : ι → PowerSeries K) (hg : ∃ i, g i ≠ 0) :
    ∃ (m : ℕ) (h : ι → PowerSeries K), (∀ i, g i = PowerSeries.X ^ m * h i) ∧
      ∃ i, (h i).constantCoeff ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  let S := Finset.univ.filter (fun i => g i ≠ 0)
  have hS : S.Nonempty := by obtain ⟨i, hi⟩ := hg; exact ⟨i, by simp [S, hi]⟩
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image (fun i => (g i).order.toNat) hS
  have hj0 : g j ≠ 0 := (Finset.mem_filter.mp hj).2
  let m := (g j).order.toNat
  have hdiv (i : ι) : PowerSeries.X ^ m ∣ g i := by
    by_cases hi : g i = 0
    · simp [hi]
    · have hle := hmin i (by simp [S, hi])
      exact (pow_dvd_pow PowerSeries.X hle).trans (PowerSeries.X_pow_order_dvd (φ := g i))
  choose h hh using hdiv
  refine ⟨m, h, hh, j, ?_⟩
  have hc := PowerSeries.coeff_order hj0
  change PowerSeries.coeff m (g j) ≠ 0 at hc
  rw [hh j] at hc
  simpa only [PowerSeries.coeff_X_pow_mul',
    le_refl, ite_true, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hc

/-- Independent jets of length p^r prevent any nontrivial relation with
p^r-th-power power-series coefficients. -/
theorem powerSeries_frobenius_relation_trivial {K ι : Type*} [Field K]
    [Fintype ι] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (f : ι → PowerSeries K)
    (hjet : ∀ a : ι → K, (∀ n < p ^ r, PowerSeries.coeff n (∑ i, a i • f i) = 0) → ∀ i, a i = 0)
    (g : ι → PowerSeries K) (hrel : ∑ i, f i * (g i) ^ (p ^ r) = 0) : ∀ i, g i = 0 := by
  classical
  by_contra! hn
  obtain ⟨m, h, hh, j, hj⟩ := powerSeries_common_order_factor g hn
  have hfactor : (∑ i, f i * (g i) ^ (p ^ r)) =
      (PowerSeries.X : PowerSeries K) ^ (m * (p ^ r)) * ∑ i, f i * (h i) ^ (p ^ r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hh i, mul_pow, ← pow_mul]
    ring
  have hX : (PowerSeries.X : PowerSeries K) ^ (m * (p ^ r)) ≠ 0 :=
    pow_ne_zero _ PowerSeries.X_ne_zero
  rw [hfactor] at hrel
  have hz := (mul_eq_zero.mp hrel).resolve_left hX
  exact hj (powerSeries_frobenius_relation_constants p r f h hjet hz j)

end
end CCDN
