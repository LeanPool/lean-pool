/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.ConductorNonzero
public import Mathlib.RingTheory.Adjoin.PowerBasis

/-! # Integral normalization of a primitive algebraic root

Multiplying a primitive root by the leading coefficient gives an integral
primitive generator. Away from primes dividing that coefficient, its monic
polynomial has at least as many residue roots as the original polynomial.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial NumberField Algebra

theorem rootCount_le_integralNormalization {Q : ℤ[X]} (hdeg : 1 ≤ Q.natDegree)
    {p : ℕ} (hp : p.Prime) (hgood : ¬p ∣ Q.leadingCoeff.natAbs) :
    rootCount Q p ≤ rootCount Q.integralNormalization p := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : (Q.leadingCoeff : ZMod p) ≠ 0 := by
    simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd] using hgood
  let f : ResidueRoots Q p → ResidueRoots Q.integralNormalization p := fun a =>
    ⟨(Q.leadingCoeff : ZMod p) * a.1, by
      have H := integralNormalization_eval₂_leadingCoeff_mul hdeg (Int.castRingHom (ZMod p)) a.1
      exact H.trans (by rw [a.2, mul_zero])⟩
  apply Nat.card_le_card_of_injective f
  intro a b h
  apply Subtype.ext
  exact mul_left_cancel₀ hc (congrArg Subtype.val h)

variable {K : Type*} [Field K] [NumberField K]

theorem exists_integralGenerator_of_polynomial {Q : ℤ[X]} (hQ : Q ≠ 0)
    (B : PowerBasis ℚ K) (hroot : aeval B.gen Q = 0) (hdeg : Q.natDegree = B.dim) :
    ∃ θ : 𝓞 K, ∃ B' : PowerBasis ℚ K,
      B'.gen = (θ : K) ∧ minpoly ℤ θ = Q.integralNormalization := by
  have hc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  let x : K := algebraMap ℤ K Q.leadingCoeff * B.gen
  have hxroot : aeval x Q.integralNormalization = 0 :=
    integralNormalization_aeval_eq_zero hroot (fun z hz => by
      change (z : K) = 0 at hz; exact_mod_cast hz)
  have hxint : IsIntegral ℤ x := ⟨Q.integralNormalization, monic_integralNormalization hQ, hxroot⟩
  let θ : 𝓞 K := ⟨x, hxint⟩
  have hxtop : Algebra.adjoin ℚ ({x} : Set K) = ⊤ := by
    apply B.adjoin_eq_top_of_gen_mem_adjoin
    have H := (Algebra.adjoin ℚ ({x} : Set K)).smul_mem
      (Algebra.self_mem_adjoin_singleton ℚ x) ((Q.leadingCoeff : ℚ)⁻¹)
    have hcK : (Q.leadingCoeff : K) ≠ 0 := by exact_mod_cast hc
    simpa [x, Algebra.smul_def, map_inv₀, ← mul_assoc, hcK] using H
  let B' : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ x) hxtop
  have hB' : B'.gen = x := rfl
  have hdim : B'.dim = B.dim := B'.finrank.symm.trans B.finrank
  refine ⟨θ, B', hB', ?_⟩
  rw [← RingOfIntegers.minpoly_coe]
  change minpoly ℤ x = Q.integralNormalization
  symm
  apply minpoly.unique' ℤ x (monic_integralNormalization hQ) hxroot
  intro q hq
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  right
  intro hqx
  have H := B'.dim_le_natDegree_of_root
    (show q.map (algebraMap ℤ ℚ) ≠ 0 from (Polynomial.map_ne_zero_iff (show Function.Injective
        (algebraMap ℤ ℚ) from Int.cast_injective)).mpr hq0)
    (by rw [hB', aeval_map_algebraMap]; exact hqx)
  rw [natDegree_map_eq_of_injective (show Function.Injective (algebraMap ℤ ℚ) from
      Int.cast_injective), hdim, ← hdeg] at H
  have H' : q.natDegree < Q.natDegree := by
    rw [degree_integralNormalization] at hq
    exact (natDegree_lt_natDegree hq0 hq)
  omega

end NairTenenbaum
