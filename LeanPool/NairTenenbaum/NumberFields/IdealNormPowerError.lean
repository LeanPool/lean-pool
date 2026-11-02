/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IdealClassPowerError
public import LeanPool.NairTenenbaum.NumberFields.IdealNormMean
public import LeanPool.NairTenenbaum.NumberFields.PowerErrorMean

/-! # The quantitative ideal-counting estimate

Summing the power-saving counts over the finite class group gives a linear
main term. The established qualitative mean identifies its coefficient with
the positive Dedekind zeta residue.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace NairTenenbaum

open NumberField Ideal Finset Filter
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- The count of nonzero integral ideals below a real norm cutoff. -/
noncomputable def nonzeroIdealNormCount (x : ℝ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ x}

theorem nonzeroIdealNormCount_eq_sum_classes {x : ℝ} (hx : 0 ≤ x) :
    nonzeroIdealNormCount K x = ∑ A : ClassGroup (𝓞 K), idealClassNormCount K A x := by
  classical
  have : Fintype {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ x} := by
    simp_rw [← Nat.le_floor_iff hx]
    exact @Fintype.ofFinite _ (finite_setOfPred_absNorm_le₀ ⌊x⌋₊)
  let e := fun A : ClassGroup (𝓞 K) => Equiv.subtypeSubtypeEquivSubtypeInter
    (fun I : (Ideal (𝓞 K))⁰ => absNorm I.1 ≤ x) (fun I => ClassGroup.mk0 I = A)
  unfold nonzeroIdealNormCount idealClassNormCount
  simp_rw [← Nat.card_congr (e _), Nat.card_eq_fintype_card, Fintype.subtype_card]
  rw [Fintype.card, Finset.card_eq_sum_card_fiberwise (f := fun I => ClassGroup.mk0 I.1)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]

theorem exists_nonzeroIdealNormCount_power_error :
    ∃ V C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |(nonzeroIdealNormCount K x : ℝ) - V * x| ≤ C * x ^ numberFieldCountingExponent K := by
  choose V C hC HC using exists_idealClassNormCount_power_error K
  refine ⟨∑ A, V A, ∑ A, C A, sum_nonneg (fun A _ => hC A), fun x hx => ?_⟩
  rw [nonzeroIdealNormCount_eq_sum_classes K (by linarith : 0 ≤ x), Nat.cast_sum,
    sum_mul, ← sum_sub_distrib]
  calc
    _ ≤ ∑ A : ClassGroup (𝓞 K), |(idealClassNormCount K A x : ℝ) - V A * x| := abs_sum_le_sum_abs
        _ _
    _ ≤ ∑ A : ClassGroup (𝓞 K), C A * x ^ numberFieldCountingExponent K :=
      sum_le_sum (fun A _ => HC A x hx)
    _ = _ := by rw [sum_mul]

theorem sum_idealNormCount_eq_nonzero_count (n : ℕ) :
    (∑ k ∈ Icc 1 n, idealNormCount K k) =
      Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ n} := by
  unfold idealNormCount
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Icc 1 n = Ioc 0 n from Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem arithmeticSummatory_idealNormArithmetic_eq {x : ℝ} (hx : 0 ≤ x) :
    arithmeticSummatory (idealNormArithmetic K) x = (nonzeroIdealNormCount K x : ℝ) := by
  unfold arithmeticSummatory
  have H : (∑ n ∈ Icc 1 ⌊x⌋₊, idealNormArithmetic K n) =
      ∑ n ∈ Icc 1 ⌊x⌋₊, (idealNormCount K n : ℝ) := by
    apply sum_congr rfl
    intro n hn
    exact idealNormArithmetic_apply_pos K (mem_Icc.mp hn).1
  rw [H, ← Nat.cast_sum, sum_idealNormCount_eq_nonzero_count]
  congr 1
  unfold nonzeroIdealNormCount
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun _ => Nat.le_floor_iff hx)

theorem exists_idealNormArithmetic_power_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |arithmeticSummatory (idealNormArithmetic K) x - dedekindZeta_residue K * x| ≤
        C * x ^ numberFieldCountingExponent K := by
  obtain ⟨V, C, hC, HC⟩ := exists_nonzeroIdealNormCount_power_error K
  have HA (x : ℝ) (hx : 1 ≤ x) :
      |arithmeticSummatory (idealNormArithmetic K) x - V * x| ≤ C * x ^
          numberFieldCountingExponent K := by
    rw [arithmeticSummatory_idealNormArithmetic_eq K (by linarith : 0 ≤ x)]
    exact HC x hx
  have HV : V = dedekindZeta_residue K := leading_coefficient_eq_of_power_error
    (numberFieldCountingExponent_lt_one K) HA
    (arithmeticSummatory_limit_of_nat_limit (idealNormArithmetic_mean K))
  exact ⟨C, hC, HV ▸ HA⟩

end NairTenenbaum
