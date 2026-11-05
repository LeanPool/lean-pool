/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IrreduciblePrimeIdealMatch
public import LeanPool.NairTenenbaum.NumberFields.RootDensityFromIdealCounts

/-! # The dyadic root-density lower bound for irreducible polynomials

Integral normalization identifies prime root counts with prime-norm ideal
counts away from finitely many primes. The correction theorem then gives a
positive mean for the squarefree root counts of the original polynomial.
-/

@[expose] public section

namespace NairTenenbaum

open Filter NumberField Polynomial
open scoped Topology

theorem exists_primitive_irreducible_squarefreeRoot_mean {Q : ℤ[X]}
    (hprim : Q.IsPrimitive) (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun x : ℝ => arithmeticSummatory (squarefreeRootArithmetic Q) x / x)
        atTop (𝓝 L) := by
  let : Fact (Irreducible (Q.map (Int.castRingHom ℚ))) := ⟨hirr⟩
  obtain ⟨N, hmatch⟩ := exists_irreducible_prime_ideal_match (Q := Q)
  exact exists_squarefreeRoot_mean_of_eventual_ideal_match
    (AdjoinRoot (Q.map (Int.castRingHom ℚ))) hprim N hmatch

theorem exists_irreducible_squarefreeRoot_mean {Q : ℤ[X]} (hQ : Irreducible Q)
    (hdeg : 0 < Q.natDegree) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun x : ℝ => arithmeticSummatory (squarefreeRootArithmetic Q) x / x)
        atTop (𝓝 L) := by
  have hprim := hQ.isPrimitive hdeg.ne'
  exact exists_primitive_irreducible_squarefreeRoot_mean hprim
    ((Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hQ)

theorem exists_irreducible_dyadicRootDensity_lower_bound {Q : ℤ[X]} (hQ : Irreducible Q)
    (hdeg : 0 < Q.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop, c ≤ dyadicRootDensitySum Q y := by
  obtain ⟨L, hL, hmean⟩ := exists_irreducible_squarefreeRoot_mean hQ hdeg
  exact ⟨L / 4, by positivity,
    eventually_dyadicRootDensity_ge_of_minorant_mean
      (squarefreeRootArithmetic_nonneg _) (squarefreeRootArithmetic_le_rootCount _) hL hmean⟩

end NairTenenbaum
