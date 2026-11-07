/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.DicksonFiniteAlgebra
public import LeanPool.KloostermanWeil.Carlitz.ExtensionDefinitions
public import LeanPool.KloostermanWeil.Carlitz.MinimalPolynomialInverse


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Trace characters of polynomial classes

Relates extension-field trace characters to values on polynomial classes. The
underlying construction follows Carlitz (1969).
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial

lemma trace_carlitz_arg
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (t : K) {x : L} (hx : x ≠ 0) :
    Algebra.trace K L
        (x + algebraMap K L t * x⁻¹) =
      (Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L : K) *
        (-(minpoly K x).nextCoeff -
          t * ((minpoly K x).coeff 1 / (minpoly K x).coeff 0)) := by
  have hxtrace :=
    trace_eq_finrank_mul_minpoly_nextCoeff (K := K) x
  have hinvtrace :=
    trace_eq_finrank_mul_minpoly_nextCoeff (K := K) x⁻¹
  have hfin :
      Module.finrank (IntermediateField.adjoin K ({x⁻¹} : Set L)) L =
        Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L := by
    rw [adjoin_inv_eq_adjoin]
  have hnext :=
    minpoly_inv_nextCoeff_eq_coeff_one_div_coeff_zero
      (K := K) (L := L) hx
  rw [map_add]
  rw [show algebraMap K L t * x⁻¹ = t • x⁻¹ by
    rw [Algebra.smul_def]]
  rw [map_smul]
  rw [hxtrace, hinvtrace, hfin, hnext]
  ring



theorem psiExt_carlitz_arg_eq_etaPoly_pow
    (p n : ℕ) [Fact p.Prime]
    (t : Fp p) {x : Ext p n} (hx : x ≠ 0) :
    psiExt p n
        (x + algebraMap (Fp p) (Ext p n) t * x⁻¹) =
      KloostermanWeil.Dickson.etaPoly p t (minpoly (Fp p) x) ^
        Module.finrank
          (IntermediateField.adjoin (Fp p) ({x} : Set (Ext p n)))
          (Ext p n) := by
  have hc :
      (minpoly (Fp p) x).coeff 0 ≠ 0 :=
    minpoly_coeff_zero_ne_zero_of_ne_zero hx
  rw [show psiExt p n
      (x + algebraMap (Fp p) (Ext p n) t * x⁻¹) =
      ZMod.stdAddChar
        (Algebra.trace (Fp p) (Ext p n)
          (x + algebraMap (Fp p) (Ext p n) t * x⁻¹)) by rfl]
  rw [trace_carlitz_arg t hx]
  unfold KloostermanWeil.Dickson.etaPoly
  rw [ite_eq_right hc]
  simpa [nsmul_eq_mul] using
    (AddChar.map_nsmul_eq_pow
      ZMod.stdAddChar
      (Module.finrank
        (IntermediateField.adjoin (Fp p) ({x} : Set (Ext p n)))
        (Ext p n))
      (-(minpoly (Fp p) x).nextCoeff -
        t * ((minpoly (Fp p) x).coeff 1 /
          (minpoly (Fp p) x).coeff 0)))


end KloostermanWeil.Carlitz
