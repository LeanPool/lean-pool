/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Monic factorization data

Encodes monic polynomial factorizations as finite data for Carlitz-type generating
identities (Carlitz 1969).
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial
open UniqueFactorizationMonoid

/-- Polynomials over the prime residue ring. -/
abbrev FpPoly (p : ℕ) := Polynomial (ZMod p)

/-- Monic polynomials of the specified natural degree. -/
def MonicDeg (p n : ℕ) :=
  {f : FpPoly p // f.Monic ∧ f.natDegree = n}

/-- Multisets of monic irreducibles whose degrees sum to the specified total degree. -/
def FactorData (p n : ℕ) :=
  {s : Multiset (FpPoly p) //
    (∀ q ∈ s, Irreducible q ∧ q.Monic) ∧
    (s.map Polynomial.natDegree).sum = n}

/-- The normalized irreducible factor multiset of a monic polynomial. -/
noncomputable def factorDataOf
    (p n : ℕ) [Fact p.Prime] :
    MonicDeg p n → FactorData p n := by
  intro f
  let s := normalizedFactors f.1
  have hfac : ∀ q ∈ s, Irreducible q ∧ q.Monic := by
    intro q hq
    refine ⟨irreducible_of_normalized_factor q hq, ?_⟩
    have hnorm := normalize_normalized_factor q hq
    exact (normalize_eq_self_iff_monic
      (ne_zero_of_mem_normalizedFactors hq)).mp hnorm
  refine ⟨s, hfac, ?_⟩
  have hprod :
      s.prod = f.1 := by
    dsimp [s]
    rw [prod_normalizedFactors_eq f.2.1.ne_zero,
      f.2.1.normalize_eq_self]
  calc
    (s.map Polynomial.natDegree).sum =
        s.prod.natDegree := by
          symm
          exact natDegree_multiset_prod_of_monic s
            (fun q hq => (hfac q hq).2)
    _ = f.1.natDegree := by rw [hprod]
    _ = n := f.2.2

/-- Reconstruct a monic polynomial by multiplying its irreducible factor data. -/
noncomputable def monicDegOfFactorData
    (p n : ℕ) [Fact p.Prime] :
    FactorData p n → MonicDeg p n := by
  intro s
  have hmonic : ∀ q ∈ s.1, q.Monic :=
    fun q hq => (s.2.1 q hq).2
  refine ⟨s.1.prod, ?_, ?_⟩
  · simpa using
      (monic_multiset_prod_of_monic s.1 (fun q => q) hmonic)
  · rw [natDegree_multiset_prod_of_monic s.1 hmonic]
    exact s.2.2

theorem factorData_left_inv
    (p n : ℕ) [Fact p.Prime] (f : MonicDeg p n) :
    monicDegOfFactorData p n (factorDataOf p n f) = f := by
  apply Subtype.ext
  change (normalizedFactors f.1).prod = f.1
  rw [prod_normalizedFactors_eq f.2.1.ne_zero,
    f.2.1.normalize_eq_self]

theorem factorData_right_inv
    (p n : ℕ) [Fact p.Prime] (s : FactorData p n) :
    factorDataOf p n (monicDegOfFactorData p n s) = s := by
  apply Subtype.ext
  change normalizedFactors s.1.prod = s.1
  rw [normalizedFactors_prod_eq s.1 (fun q hq => (s.2.1 q hq).1)]
  calc
    s.1.map normalize = s.1.map id := by
      apply Multiset.map_congr rfl
      intro q hq
      exact (s.2.1 q hq).2.normalize_eq_self
    _ = s.1 := Multiset.map_id _

/-- Unique factorization as an equivalence between monic polynomials and factor data. -/
noncomputable def monicFactorEquiv
    (p n : ℕ) [Fact p.Prime] :
    MonicDeg p n ≃ FactorData p n where
  toFun := factorDataOf p n
  invFun := monicDegOfFactorData p n
  left_inv := factorData_left_inv p n
  right_inv := factorData_right_inv p n


end KloostermanWeil.Carlitz
