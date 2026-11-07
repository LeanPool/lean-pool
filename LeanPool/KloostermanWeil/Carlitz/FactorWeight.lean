/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.CoefficientEquivalence


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Multiplicative polynomial weights

Relates multiplicative polynomial weights to factorization data in the Carlitz (1969)
extension-sum construction.
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial
open KloostermanWeil.Dickson

theorem etaPoly_multiset_prod_of_monic
    (p : ℕ) [Fact p.Prime] (t : ZMod p)
    (s : Multiset (Polynomial (ZMod p)))
    (hs : ∀ f ∈ s, f.Monic) :
    etaPoly p t s.prod =
      (s.map (etaPoly p t)).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      simp [etaPoly_one]
  | @cons f s ih =>
      have hf : f.Monic := hs f (Multiset.mem_cons_self _ _)
      have hs' : ∀ g ∈ s, g.Monic :=
        fun g hg => hs g (Multiset.mem_cons_of_mem hg)
      have hprod : s.prod.Monic := by
        simpa using
          (monic_multiset_prod_of_monic s (fun g => g) hs')
      rw [Multiset.prod_cons, etaPoly_mul_of_monic p t hf hprod,
        Multiset.map_cons, Multiset.prod_cons, ih hs']

/-- The product of the additive-character weights of the irreducible factors. -/
noncomputable def factorWeight
    (p : ℕ) [Fact p.Prime] (t : ZMod p) {n : ℕ}
    (s : FactorData p n) : ℂ :=
  (s.1.map (etaPoly p t)).prod

theorem etaPoly_eq_factorWeight
    (p n : ℕ) [Fact p.Prime] (t : ZMod p)
    (f : MonicDeg p n) :
    etaPoly p t f.1 =
      factorWeight p t (factorDataOf p n f) := by
  let s := UniqueFactorizationMonoid.normalizedFactors f.1
  have hmonic : ∀ q ∈ s, q.Monic := by
    intro q hq
    have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor q hq
    exact (normalize_eq_self_iff_monic
      (UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hq)).mp hnorm
  have hprod : s.prod = f.1 := by
    dsimp [s]
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq f.2.1.ne_zero,
      f.2.1.normalize_eq_self]
  unfold factorWeight
  have hval :
      (factorDataOf p n f).1 =
        UniqueFactorizationMonoid.normalizedFactors f.1 := by
    rfl
  rw [hval]
  change etaPoly p t f.1 =
    ((UniqueFactorizationMonoid.normalizedFactors f.1).map
      (etaPoly p t)).prod
  calc
    etaPoly p t f.1 = etaPoly p t s.prod := by
      exact congrArg (etaPoly p t) hprod.symm
    _ = (s.map (etaPoly p t)).prod :=
      etaPoly_multiset_prod_of_monic p t s hmonic
    _ = ((UniqueFactorizationMonoid.normalizedFactors f.1).map
          (etaPoly p t)).prod := by
      rfl

/-- Parametrize irreducible factor data by the lower coefficients of its product. -/
noncomputable def coeffFactorEquiv
    (p n : ℕ) [Fact p.Prime] :
    (Fin n → ZMod p) ≃ FactorData p n :=
  (coeffVectorEquivMonicDeg p n).trans (monicFactorEquiv p n)

theorem A_eq_factorData_sum
    (p : ℕ) [Fact p.Prime] (t : ZMod p) (n : ℕ) :
    A p t n =
      letI : Fintype (FactorData p n) :=
        Fintype.ofEquiv (Fin n → ZMod p) (coeffFactorEquiv p n)
      ∑ s : FactorData p n, factorWeight p t s := by
  classical
  let e := coeffFactorEquiv p n
  let : Fintype (FactorData p n) :=
    Fintype.ofEquiv (Fin n → ZMod p) e
  unfold A
  refine Fintype.sum_equiv e _ _ ?_
  intro a
  change etaPoly p t (monicFromCoeffs p n a) =
    factorWeight p t
      (factorDataOf p n (coeffVectorToMonic p n a))
  exact etaPoly_eq_factorWeight p n t
    (coeffVectorToMonic p n a)


end KloostermanWeil.Carlitz
