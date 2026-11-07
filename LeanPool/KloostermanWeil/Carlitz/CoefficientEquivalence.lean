/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.FactorData


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Coefficients of monic polynomials

Equivalences between coefficient vectors and monic polynomials used in the Carlitz
factorization. The coefficient algebra is proved here.
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial
open KloostermanWeil.Dickson

noncomputable def coeffVectorToMonic
    (p n : ℕ) [Fact p.Prime] :
    (Fin n → ZMod p) → MonicDeg p n := by
  intro a
  refine ⟨monicFromCoeffs p n a, monicFromCoeffs_monic p n a, ?_⟩
  exact natDegree_eq_of_degree_eq_some
    (monicFromCoeffs_degree p n a)

noncomputable def monicToCoeffVector
    (p n : ℕ) [Fact p.Prime] :
    MonicDeg p n → (Fin n → ZMod p) :=
  fun f i => f.1.coeff i

theorem coeffVector_left_inv
    (p n : ℕ) [Fact p.Prime] (a : Fin n → ZMod p) :
    monicToCoeffVector p n (coeffVectorToMonic p n a) = a := by
  funext i
  exact monicFromCoeffs_coeff_lt p n i.1 i.2 a

theorem coeffVector_right_inv
    (p n : ℕ) [Fact p.Prime] (f : MonicDeg p n) :
    coeffVectorToMonic p n (monicToCoeffVector p n f) = f := by
  apply Subtype.ext
  let g := monicFromCoeffs p n (monicToCoeffVector p n f)
  have hgMonic : g.Monic := monicFromCoeffs_monic p n _
  have hgDeg : g.natDegree = n :=
    natDegree_eq_of_degree_eq_some
      (monicFromCoeffs_degree p n (monicToCoeffVector p n f))
  change g = f.1
  apply Polynomial.ext
  intro k
  by_cases hk : k < n
  · change g.coeff k = f.1.coeff k
    simpa [g, monicToCoeffVector] using
      (monicFromCoeffs_coeff_lt p n k hk (monicToCoeffVector p n f))
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    by_cases hEq : k = n
    · subst k
      have hfTop : f.1.coeff n = 1 := by
        calc
          f.1.coeff n = f.1.leadingCoeff := by
            rw [Polynomial.leadingCoeff, f.2.2]
          _ = 1 := f.2.1
      have hgTop : g.coeff n = 1 := by
        calc
          g.coeff n = g.leadingCoeff := by
            rw [Polynomial.leadingCoeff, hgDeg]
          _ = 1 := hgMonic
      exact hgTop.trans hfTop.symm
    · have hlt : n < k := lt_of_le_of_ne hnk (Ne.symm hEq)
      have hf0 : f.1.coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by simpa [f.2.2] using hlt)
      have hg0 : g.coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by simpa [hgDeg] using hlt)
      exact hg0.trans hf0.symm

noncomputable def coeffVectorEquivMonicDeg
    (p n : ℕ) [Fact p.Prime] :
    (Fin n → ZMod p) ≃ MonicDeg p n where
  toFun := coeffVectorToMonic p n
  invFun := monicToCoeffVector p n
  left_inv := coeffVector_left_inv p n
  right_inv := coeffVector_right_inv p n


end KloostermanWeil.Carlitz
