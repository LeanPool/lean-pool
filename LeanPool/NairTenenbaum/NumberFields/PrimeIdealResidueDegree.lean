/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IdealMultiplicityVectors

/-! # Residue-degree totals and prime-norm ideal counts -/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

theorem primeIdealSupport_weighted_degree_eq {p : ℕ} (hp : p.Prime) :
    (∑ P : primeIdealSupport K p, P.1.inertiaDeg ℤ *
      (normalizedFactors (Ideal.span {(p : 𝓞 K)})).count P.1) = Module.finrank ℚ K := by
  apply Nat.pow_right_injective hp.two_le
  change p ^ (∑ P : primeIdealSupport K p, P.1.inertiaDeg ℤ *
    (normalizedFactors (Ideal.span {(p : 𝓞 K)})).count P.1) = p ^ Module.finrank ℚ K
  rw [← idealOfMultiplicities_norm hp (fun P =>
      (normalizedFactors (Ideal.span {(p : 𝓞 K)})).count P.1),
    idealOfMultiplicities_factor_counts (span_prime_natCast_ne_bot hp) (primeIdealSupport K p)
      (show (normalizedFactors (Ideal.span {(p : 𝓞 K)})).toFinset ⊆ primeIdealSupport K p from
          Subset.refl _),
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem primeIdealSupport_sum_inertiaDeg_le {p : ℕ} (hp : p.Prime) :
    (∑ P : primeIdealSupport K p, P.1.inertiaDeg ℤ) ≤ Module.finrank ℚ K := by
  rw [← primeIdealSupport_weighted_degree_eq hp]
  apply sum_le_sum
  intro P _
  apply Nat.le_mul_of_pos_right
  exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.2)

end NairTenenbaum
