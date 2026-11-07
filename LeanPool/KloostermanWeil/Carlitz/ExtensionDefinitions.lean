/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Weil.PrimeFoundation
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Extension-field Kloosterman sums

Defines additive characters, trace maps and sums over finite extensions. Compare
Carlitz (1969), equations (2.8)–(2.13); the exact Lean normalization is specified by
the definitions below.
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

/-- The prime residue ring used as the base field when `p` is prime. -/
abbrev Fp (p : ℕ) := ZMod p
/-- The chosen finite Galois extension of the prime field. -/
abbrev Ext (p n : ℕ) [Fact p.Prime] := GaloisField p n

/-- Canonical additive character on the chosen degree-n extension:
the base standard additive character composed with algebra trace. -/
noncomputable def psiExt
    (p n : ℕ) [Fact p.Prime] :
    AddChar (Ext p n) ℂ where
  toFun x := ZMod.stdAddChar (Algebra.trace (Fp p) (Ext p n) x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [map_add, AddChar.map_add_eq_mul]

/-- Carlitz extension-field Kloosterman sum in prime-modulus argument/sign convention. -/
noncomputable def Kext
    (p n : ℕ) [Fact p.Prime] (t : Fp p) : ℂ := by
  classical
  letI := Fintype.ofFinite (Ext p n)
  exact ∑ x : Ext p n,
    if x = 0 then 0
    else psiExt p n
      (x + algebraMap (Fp p) (Ext p n) t * x⁻¹)

/-- Canonical degree-one change of variables from the base field. -/
noncomputable def degreeOneEquiv
    (p : ℕ) [Fact p.Prime] :
    Fp p ≃ₐ[Fp p] Ext p 1 :=
  (GaloisField.equivZmodP p).symm

lemma trace_degreeOneEquiv
    (p : ℕ) [Fact p.Prime] (x : Fp p) :
    Algebra.trace (Fp p) (Ext p 1) (degreeOneEquiv p x) = x := by
  rw [Algebra.trace_eq_of_algEquiv (degreeOneEquiv p) x]
  exact Algebra.trace_self_apply x

lemma psiExt_degreeOneEquiv
    (p : ℕ) [Fact p.Prime] (x : Fp p) :
    psiExt p 1 (degreeOneEquiv p x) = ZMod.stdAddChar x := by
  simp [psiExt, trace_degreeOneEquiv]

theorem Kext_one_eq_kloostermanSumPrime
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    Kext p 1 t = KloostermanWeil.kloostermanSumPrime p t 1 := by
  classical
  let := Fintype.ofFinite (Ext p 1)
  let e := degreeOneEquiv p
  unfold Kext KloostermanWeil.kloostermanSumPrime
  symm
  refine Fintype.sum_equiv e.toEquiv
    (fun x : Fp p =>
      if x = 0 then (0 : ℂ) else
        ZMod.stdAddChar (1 * x + t * x⁻¹))
    (fun y : Ext p 1 =>
      if y = 0 then (0 : ℂ) else
        psiExt p 1 (y + algebraMap (Fp p) (Ext p 1) t * y⁻¹)) ?_
  intro x
  by_cases hx : x = 0
  · subst hx
    simp [e, degreeOneEquiv]
  · have hex : e.toEquiv x ≠ 0 := by
      simpa using ((map_ne_zero e).2 hx)
    simp only [ite_eq_right hx, ite_eq_right hex]
    change ZMod.stdAddChar (1 * x + t * x⁻¹) =
      psiExt p 1
        (e x + algebraMap (Fp p) (Ext p 1) t * (e x)⁻¹)
    have het :
        e t = algebraMap (Fp p) (Ext p 1) t := by
      simpa using e.commutes t
    have harg :
        e (x + t * x⁻¹) =
          e x + algebraMap (Fp p) (Ext p 1) t * (e x)⁻¹ := by
      rw [map_add, map_mul, map_inv₀, het]
    rw [← harg, psiExt_degreeOneEquiv]
    simp


end KloostermanWeil.Carlitz
