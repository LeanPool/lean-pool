/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.ClassGhost
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.Polynomial.Splits


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Irreducibles in the generating identity

Organizes the irreducible polynomial factors that contribute to the Carlitz (1969)
generating-series construction.
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial

def RelevantIrred
    (p n : ℕ) [Fact p.Prime] :=
  {P : Polynomial (Fp p) //
    P.Monic ∧ Irreducible P ∧ P.natDegree ∣ n}

noncomputable def classToRelevant
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    (c : ConjRootClass (Fp p) (Ext p n)) :
    RelevantIrred p n := by
  refine ⟨c.minpoly, c.monic_minpoly, c.irreducible_minpoly, ?_⟩
  have hd :
      c.minpoly.natDegree ∣
        Module.finrank (Fp p) (Ext p n) := by
    induction c with
    | h x =>
        simpa [ConjRootClass.minpoly_mk] using
          (minpoly.degree_dvd (IsIntegral.of_finite (Fp p) x))
  rw [GaloisField.finrank p (NeZero.ne n)] at hd
  exact hd

lemma classToRelevant_injective
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    Function.Injective (classToRelevant p n) := by
  intro c d h
  apply ConjRootClass.minpoly_injective
  exact congrArg Subtype.val h

lemma classToRelevant_surjective
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    Function.Surjective (classToRelevant p n) := by
  intro P
  rcases P with ⟨P, hmonic, hirr, hdeg⟩
  let : Fact (Irreducible P) := ⟨hirr⟩
  let KP := AdjoinRoot P
  have hfinK :
      Module.finrank (Fp p) KP = P.natDegree := by
    exact finrank_quotient_span_eq_natDegree
  have hfinL :
      Module.finrank (Fp p) (Ext p n) = n :=
    GaloisField.finrank p (NeZero.ne n)
  have hdvd :
      Module.finrank (Fp p) KP ∣
        Module.finrank (Fp p) (Ext p n) := by
    rw [hfinK, hfinL]
    exact hdeg
  obtain ⟨phi⟩ :=
    FiniteField.nonempty_algHom_of_finrank_dvd
      (F := Fp p) (K := KP) (L := Ext p n) hdvd
  let x : Ext p n := phi (AdjoinRoot.root P)
  have hx : Polynomial.aeval x P = 0 := by
    have htransport :=
      Polynomial.hom_eval₂
        P (AdjoinRoot.of P) phi.toRingHom (AdjoinRoot.root P)
    rw [AdjoinRoot.eval₂_root, map_zero] at htransport
    have hcomp :
        phi.toRingHom.comp (AdjoinRoot.of P) =
          algebraMap (Fp p) (Ext p n) := by
      ext a
      exact phi.commutes a
    rw [hcomp] at htransport
    exact htransport.symm
  let c := ConjRootClass.mk (Fp p) x
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change c.minpoly = P
  rw [ConjRootClass.minpoly_mk]
  exact (minpoly.eq_of_irreducible_of_monic hirr hx hmonic).symm

noncomputable def classRelevantEquiv
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    ConjRootClass (Fp p) (Ext p n) ≃ RelevantIrred p n :=
  Equiv.ofBijective (classToRelevant p n)
    ⟨classToRelevant_injective p n,
     classToRelevant_surjective p n⟩


end KloostermanWeil.Carlitz
