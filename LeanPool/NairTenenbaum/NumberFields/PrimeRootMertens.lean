/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.IdealMangoldtMertensReduction
public import LeanPool.NairTenenbaum.NumberFields.IdealNormPowerError

/-! # The sharp weighted prime-root upper bound

The quantitative ideal count supplies the Mertens estimate for the ideal von
Mangoldt function. Eventual root/ideal agreement gives the bound for each
irreducible polynomial, with leading coefficient one.
-/

@[expose] public section

namespace NairTenenbaum

open NumberField Polynomial

theorem exists_irreducible_rational_primeRootLogSum_bound {Q : ℤ[X]}
    (hQ : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → primeRootLogSum Q x ≤ Real.log x + B := by
  let : Fact (Irreducible (Q.map (Int.castRingHom ℚ))) := ⟨hQ⟩
  let K := AdjoinRoot (Q.map (Int.castRingHom ℚ))
  obtain ⟨N, hmatch⟩ := exists_irreducible_prime_ideal_match (Q := Q)
  obtain ⟨E, hE, HE⟩ := exists_idealNormArithmetic_power_error K
  exact exists_primeRootLogSum_mertens_bound_of_power_error K N hmatch hE
    (numberFieldCountingExponent_nonneg K) (numberFieldCountingExponent_lt_one K) HE

theorem exists_irreducible_primeRootLogSum_bound {Q : ℤ[X]} (hQ : Irreducible Q)
    (hdeg : 0 < Q.natDegree) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → primeRootLogSum Q x ≤ Real.log x + B := by
  have hprim := hQ.isPrimitive hdeg.ne'
  exact exists_irreducible_rational_primeRootLogSum_bound
    ((Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hQ)

end NairTenenbaum
