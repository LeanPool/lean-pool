/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.MinpolyPrimeLowerBound
public import LeanPool.NairTenenbaum.NumberFields.RootNormalizationEquality

/-! # The lower prime-root logarithmic bound for irreducible polynomials -/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial NumberField

theorem exists_irreducible_rootPrimePowerSum_lower_bound {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ C b : ℝ, 1 < b ∧ ∀ σ : ℝ, 1 < σ → σ < b →
      -Real.log (σ - 1) - C ≤ rootPrimePowerSum Q σ := by
  let : Fact (Irreducible (Q.map (Int.castRingHom ℚ))) := ⟨hirr⟩
  have hQ0 : Q ≠ 0 := by intro h; simp [h] at hirr
  let B : PowerBasis ℚ (AdjoinRoot (Q.map (Int.castRingHom ℚ))) := AdjoinRoot.powerBasis
      hirr.ne_zero
  have hroot : aeval B.gen Q = 0 := by
    rw [← aeval_map_algebraMap ℚ]
    change aeval (AdjoinRoot.root (Q.map (Int.castRingHom ℚ))) (Q.map (Int.castRingHom ℚ)) = 0
    exact (AdjoinRoot.aeval_eq (f := Q.map (Int.castRingHom ℚ)) _).trans AdjoinRoot.mk_self
  have hdeg : Q.natDegree = B.dim := by
    exact (natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective Q).symm
  obtain ⟨θ, B', hB', hmin⟩ := exists_integralGenerator_of_polynomial hQ0 B hroot hdeg
  obtain ⟨C, b, hb, H⟩ := exists_minpoly_rootPrimePowerSum_lower_bound θ
      (conductor_exponent_ne_zero θ B' hB')
  rw [hmin] at H
  refine ⟨C + Q.leadingCoeff.natAbs.primeFactors.card, b, hb, fun σ hσ hσb => ?_⟩
  have hdegpos : 1 ≤ Q.natDegree := by
    rw [← natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective Q]
    exact hirr.natDegree_pos
  have HE := rootPrimePowerSum_integralNormalization_le hQ hdegpos hσ
  have HL := H σ hσ hσb
  linarith

end NairTenenbaum
