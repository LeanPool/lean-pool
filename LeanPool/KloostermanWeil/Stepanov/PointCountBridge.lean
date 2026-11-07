/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.FiniteSum
public import LeanPool.KloostermanWeil.Stepanov.ScalarExtensionSum


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# From point counts to spectral sums

Connects extension Kloosterman sums and the point-count discrepancy in Harcos (2015),
equation (3).
-/

@[expose] public section

namespace KloostermanWeil.Stepanov

open scoped BigOperators
open KloostermanWeil.Carlitz

theorem Kseq_eq_Kext_of_ne_zero
    (p n : ℕ) [Fact p.Prime] (t : ZMod p) (hn : n ≠ 0) :
    Kseq p t n = by
      letI : NeZero n := ⟨hn⟩
      exact Kext p n t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rfl

theorem scalarTraceSum_zero
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    (c : GaloisField p n) :
    extensionKloostermanScalarSum p n c 0 =
      ((p ^ n - 1 : ℕ) : ℂ) := by
  classical
  let := Fintype.ofFinite (GaloisField p n)
  unfold extensionKloostermanScalarSum
  simp only [map_add, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_inj]
  rw [Fintype.card_units]
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p n (NeZero.ne n)
  rw [hcard]

theorem errorAggregate_eq_Kext_sum
    (p n : ℕ) [Fact p.Prime] (c : ZMod p) (hn : n ≠ 0) :
    errorAggregate p n c =
      -1 +
      ∑ m : {m : ZMod p // m ≠ 0},
        (letI : NeZero n := ⟨hn⟩
         Kext p n (m.1 ^ 2 * c)) := by
  classical
  unfold errorAggregate
  apply congrArg (fun z : ℂ => -1 + z)
  apply Finset.sum_congr rfl
  intro m hm
  exact Kseq_eq_Kext_of_ne_zero p n (m.1 ^ 2 * c) hn

/-- Exact point-count bridge:
the specialized affine curve defect is literally the finite aggregate consumed
in the Stepanov argument. -/
theorem pointCountError_eq_errorAggregate
    (p n : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (c : ZMod p) (hc : c ≠ 0) (hn : n ≠ 0) :
    letI : NeZero n := ⟨hn⟩
    letI := Fintype.ofFinite (GaloisField p n)
    (((hyperellipticAffinePointFinset
        (kloostermanCurvePolynomial p n c)).card : ℕ) : ℂ) -
        (p ^ n : ℕ) =
      errorAggregate p n c := by
  classical
  let : NeZero n := ⟨hn⟩
  let := Fintype.ofFinite (GaloisField p n)
  have hcurve :=
    card_quadraticArtinCurve_eq_scalarSums
      p n hpodd hn
      (algebraMap (ZMod p) (GaloisField p n) c)
      (by
        intro hzero
        apply hc
        apply FaithfulSMul.algebraMap_injective
          (ZMod p) (GaloisField p n)
        simpa using hzero)
  have hcard :=
    card_quadraticArtinCurve_eq_hyperelliptic p n c
  have hsplit :
      (∑ m : ZMod p,
          extensionKloostermanScalarSum p n
            (algebraMap (ZMod p) (GaloisField p n) c) m) =
        ((p ^ n - 1 : ℕ) : ℂ) +
        ∑ m : {m : ZMod p // m ≠ 0},
          Kext p n (m.1 ^ 2 * c) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun m : ZMod p =>
        extensionKloostermanScalarSum p n
          (algebraMap (ZMod p) (GaloisField p n) c) m) 0]
    rw [scalarTraceSum_zero]
    apply congrArg (fun z : ℂ => ((p ^ n - 1 : ℕ) : ℂ) + z)
    apply Finset.sum_congr rfl
    intro m hm
    exact scalarTraceSum_eq_Kext_sq p n c m.1 m.2
  have hcurveC :
      (((hyperellipticAffinePointFinset
          (kloostermanCurvePolynomial p n c)).card : ℕ) : ℂ) =
        ((p ^ n - 1 : ℕ) : ℂ) +
        ∑ m : {m : ZMod p // m ≠ 0},
          Kext p n (m.1 ^ 2 * c) := by
    rw [← hsplit]
    rw [← hcurve]
    exact_mod_cast hcard.symm
  rw [errorAggregate_eq_Kext_sum p n c hn]
  rw [hcurveC]
  have hp_pos : 0 < p ^ n :=
    pow_pos (show 0 < p from (show p.Prime from Fact.out).pos) _
  have hp1 : 1 ≤ p ^ n := by omega
  rw [Nat.cast_sub hp1]
  have hsum :
      (∑ m : {m : ZMod p // m ≠ 0},
          Kext p n (m.1 ^ 2 * c)) =
        ∑ m : {m : ZMod p // m ≠ 0},
          Kext p n (c * m.1 ^ 2) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [mul_comm]
  rw [hsum]
  push_cast
  ring


end KloostermanWeil.Stepanov
