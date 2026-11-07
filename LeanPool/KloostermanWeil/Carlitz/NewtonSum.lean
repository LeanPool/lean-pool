/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.NewtonIndex


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Newton sums for the recurrence

Newton identities connecting polynomial coefficients and power sums. The algebra is
standard; its indexing here serves the Carlitz (1969) construction.
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial
open KloostermanWeil.Dickson

/-- The degree-weighted character contribution of an irreducible prime power. -/
noncomputable def primePowerWeight
    (p n : ℕ) [Fact p.Prime] (t : ZMod p)
    (z : PrimePowerDecomp p n) : ℂ :=
  let j := z.1
  let P := z.2.1
  let u := z.2.2
  (P.1.natDegree : ℂ) *
    etaPoly p t P.1 ^ ((j.1 + 1) / P.1.natDegree) *
      factorWeight p t u

/-- The factor weight multiplied by the degree of the marked irreducible. -/
noncomputable def pointedWeight
    (p n : ℕ) [Fact p.Prime] (t : ZMod p)
    (z : PointedFactorData p n) : ℂ :=
  (z.2.1.1.natDegree : ℂ) * factorWeight p t z.1

theorem pointedWeight_primePowerToPointed
    (p n : ℕ) [Fact p.Prime] (t : ZMod p)
    (z : PrimePowerDecomp p n) :
    pointedWeight p n t (primePowerToPointed p n z) =
      primePowerWeight p n t z := by
  rcases z with ⟨j, P, u⟩
  unfold pointedWeight primePowerWeight
  simp [primePowerToPointed, factorWeight,
    Multiset.map_add, Multiset.map_replicate,
    Multiset.prod_add, Multiset.prod_replicate,
    mul_assoc]



open Polynomial
open KloostermanWeil.Dickson

theorem sum_count_natDegree
    {p : ℕ} (s : Multiset (Polynomial (ZMod p))) :
    ∑ q ∈ s.toFinset, s.count q * q.natDegree =
      (s.map Polynomial.natDegree).sum := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      by_cases ha : a ∈ s
      · have hfin : (a ::ₘ s).toFinset = s.toFinset := by
          ext q
          simp [ha]
        rw [hfin]
        calc
          ∑ q ∈ s.toFinset, (a ::ₘ s).count q * q.natDegree =
              ∑ q ∈ s.toFinset,
                (s.count q + if q = a then 1 else 0) * q.natDegree := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  rw [Multiset.count_cons]
          _ = (∑ q ∈ s.toFinset, s.count q * q.natDegree) +
                a.natDegree := by
                  simp only [add_mul]
                  rw [Finset.sum_add_distrib]
                  have hamem : a ∈ s.toFinset := Multiset.mem_toFinset.mpr ha
                  simp [hamem]
          _ = (s.map Polynomial.natDegree).sum + a.natDegree := by
                  rw [ih]
          _ = ((a ::ₘ s).map Polynomial.natDegree).sum := by
                  simp [add_comm]
      · have hfin : (a ::ₘ s).toFinset = insert a s.toFinset := by
          ext q
          simp
        rw [hfin, Finset.sum_insert]
        · have hsum :
              ∑ x ∈ s.toFinset, (a ::ₘ s).count x * x.natDegree =
                ∑ x ∈ s.toFinset, s.count x * x.natDegree := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxa : x ≠ a := by
              intro h
              subst x
              exact ha (Multiset.mem_toFinset.mp hx)
            simp [hxa]
          rw [hsum, ih]
          simp [ha, add_comm]
        · simpa using ha

theorem pointedFiber_sum
    (p n : ℕ) [Fact p.Prime] (t : ZMod p)
    (s : FactorData p n) :
    (∑ z :
        (Σ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
          Fin (s.1.count q.1)),
      (z.1.1.natDegree : ℂ) * factorWeight p t s) =
      (n : ℂ) * factorWeight p t s := by
  classical
  have hsplit :
      (∑ z :
          (Σ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
            Fin (s.1.count q.1)),
        (z.1.1.natDegree : ℂ) * factorWeight p t s) =
        ∑ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
          ∑ _k : Fin (s.1.count q.1),
            (q.1.natDegree : ℂ) * factorWeight p t s := by
    simpa using
      (Fintype.sum_sigma'
        (fun (q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset})
          (_k : Fin (s.1.count q.1)) =>
            (q.1.natDegree : ℂ) * factorWeight p t s))
  have hqsum :
      (∑ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
        (s.1.count q.1 : ℂ) * (q.1.natDegree : ℂ)) = (n : ℂ) := by
    let S := s.1.toFinset
    let f : Polynomial (ZMod p) → ℂ :=
      fun q => (s.1.count q : ℂ) * (q.natDegree : ℂ)
    change (∑ q : S, f q.1) = (n : ℂ)
    rw [show (Finset.univ : Finset S) = S.attach from Finset.univ_eq_attach S]
    rw [Finset.sum_attach]
    dsimp [S, f]
    have hdeg := sum_count_natDegree s.1
    rw [s.2.2] at hdeg
    exact_mod_cast hdeg
  calc
    (∑ z :
        (Σ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
          Fin (s.1.count q.1)),
      (z.1.1.natDegree : ℂ) * factorWeight p t s) =
      ∑ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
        ∑ _k : Fin (s.1.count q.1),
          (q.1.natDegree : ℂ) * factorWeight p t s := hsplit
    _ =
      ∑ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
        ((s.1.count q.1 : ℂ) * (q.1.natDegree : ℂ)) *
          factorWeight p t s := by
            apply Fintype.sum_congr
            intro q
            simp [nsmul_eq_mul]
            ring
    _ = (∑ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
          (s.1.count q.1 : ℂ) * (q.1.natDegree : ℂ)) *
        factorWeight p t s := by
          rw [Finset.sum_mul]
    _ = (n : ℂ) * factorWeight p t s := by rw [hqsum]



open Polynomial
open KloostermanWeil.Dickson

theorem sum_primePowerWeight_eq_sum_pointedWeight
    (p n : ℕ) [Fact p.Prime] (t : ZMod p) :
    (∑ z : PrimePowerDecomp p n, primePowerWeight p n t z) =
      ∑ z : PointedFactorData p n, pointedWeight p n t z := by
  classical
  exact Fintype.sum_equiv
    (primePowerPointedEquiv p n)
    (primePowerWeight p n t)
    (pointedWeight p n t)
    (fun z => (pointedWeight_primePowerToPointed p n t z).symm)

theorem sum_pointedWeight_eq_n_mul_A
    (p n : ℕ) [Fact p.Prime] (t : ZMod p) :
    (∑ z : PointedFactorData p n, pointedWeight p n t z) =
      (n : ℂ) * A p t n := by
  classical
  have hsplit :
      (∑ z : PointedFactorData p n, pointedWeight p n t z) =
        ∑ s : FactorData p n,
          ∑ z :
            (Σ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
              Fin (s.1.count q.1)),
            (z.1.1.natDegree : ℂ) * factorWeight p t s := by
    simpa [pointedWeight] using
      (Fintype.sum_sigma'
        (fun (s : FactorData p n)
          (z :
            (Σ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
              Fin (s.1.count q.1))) =>
            (z.1.1.natDegree : ℂ) * factorWeight p t s))
  calc
    (∑ z : PointedFactorData p n, pointedWeight p n t z) =
        ∑ s : FactorData p n,
          ∑ z :
            (Σ q : {a : Polynomial (ZMod p) // a ∈ s.1.toFinset},
              Fin (s.1.count q.1)),
            (z.1.1.natDegree : ℂ) * factorWeight p t s := hsplit
    _ = ∑ s : FactorData p n,
          (n : ℂ) * factorWeight p t s := by
          apply Fintype.sum_congr
          intro s
          exact pointedFiber_sum p n t s
    _ = (n : ℂ) *
          (∑ s : FactorData p n, factorWeight p t s) := by
          rw [Finset.mul_sum]
    _ = (n : ℂ) * A p t n := by
          rw [A_eq_factorData_sum]

theorem sum_primePowerWeight_eq_ghost_convolution
    (p n : ℕ) [Fact p.Prime] (t : ZMod p) :
    (∑ z : PrimePowerDecomp p n, primePowerWeight p n t z) =
      ∑ j : Fin n,
        irredGhost p (j.1 + 1) t *
          A p t (n - (j.1 + 1)) := by
  classical
  have hsplit :
      (∑ z : PrimePowerDecomp p n, primePowerWeight p n t z) =
        ∑ j : Fin n,
          ∑ pu :
            RelevantIrred p (j.1 + 1) ×
              FactorData p (n - (j.1 + 1)),
            primePowerWeight p n t ⟨j, pu⟩ := by
    simpa using
      (Fintype.sum_sigma'
        (fun (j : Fin n)
          (pu :
            RelevantIrred p (j.1 + 1) ×
              FactorData p (n - (j.1 + 1))) =>
            primePowerWeight p n t ⟨j, pu⟩))
  rw [hsplit]
  apply Fintype.sum_congr
  intro j
  rw [Fintype.sum_prod_type]
  change
    (∑ P : RelevantIrred p (j.1 + 1),
      ∑ u : FactorData p (n - (j.1 + 1)),
        (P.1.natDegree : ℂ) *
          etaPoly p t P.1 ^ ((j.1 + 1) / P.1.natDegree) *
            factorWeight p t u) =
      irredGhost p (j.1 + 1) t *
        A p t (n - (j.1 + 1))
  calc
    (∑ P : RelevantIrred p (j.1 + 1),
      ∑ u : FactorData p (n - (j.1 + 1)),
        (P.1.natDegree : ℂ) *
          etaPoly p t P.1 ^ ((j.1 + 1) / P.1.natDegree) *
            factorWeight p t u) =
      ∑ P : RelevantIrred p (j.1 + 1),
        ((P.1.natDegree : ℂ) *
          etaPoly p t P.1 ^ ((j.1 + 1) / P.1.natDegree)) *
          (∑ u : FactorData p (n - (j.1 + 1)),
            factorWeight p t u) := by
              apply Fintype.sum_congr
              intro P
              rw [Finset.mul_sum]
    _ = (∑ P : RelevantIrred p (j.1 + 1),
          (P.1.natDegree : ℂ) *
            etaPoly p t P.1 ^ ((j.1 + 1) / P.1.natDegree)) *
        (∑ u : FactorData p (n - (j.1 + 1)),
          factorWeight p t u) := by
            rw [Finset.sum_mul]
    _ = irredGhost p (j.1 + 1) t *
        A p t (n - (j.1 + 1)) := by
          rw [A_eq_factorData_sum]
          rfl



open Polynomial
open KloostermanWeil.Dickson

theorem newton_irredGhost
    (p n : ℕ) [Fact p.Prime] (t : ZMod p) :
    (n : ℂ) * A p t n =
      ∑ j : Fin n,
        irredGhost p (j.1 + 1) t *
          A p t (n - (j.1 + 1)) := by
  calc
    (n : ℂ) * A p t n =
        ∑ z : PointedFactorData p n, pointedWeight p n t z :=
      (sum_pointedWeight_eq_n_mul_A p n t).symm
    _ = ∑ z : PrimePowerDecomp p n, primePowerWeight p n t z :=
      (sum_primePowerWeight_eq_sum_pointedWeight p n t).symm
    _ = ∑ j : Fin n,
        irredGhost p (j.1 + 1) t *
          A p t (n - (j.1 + 1)) :=
      sum_primePowerWeight_eq_ghost_convolution p n t

theorem newton_Kext
    (p n : ℕ) [Fact p.Prime] (t : ZMod p) :
    (n : ℂ) * A p t n =
      ∑ j : Fin n,
        Kext p (j.1 + 1) t *
          A p t (n - (j.1 + 1)) := by
  rw [newton_irredGhost p n t]
  apply Fintype.sum_congr
  intro j
  rw [Kext_eq_irredGhost]


end KloostermanWeil.Carlitz
