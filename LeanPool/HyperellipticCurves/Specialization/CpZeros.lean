/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.CanonDeg
public import LeanPool.HyperellipticCurves.Series.ZeroCount

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# Zeros of the disk expansion over an algebraically closed complete field

Toward `thm:spec`: the disk expansion `h` has a Weierstrass factorization `h = W·u` over the
discrete valuation ring `O_K` (`LeanPool.HyperellipticCurves.Series.ZeroCount`), with `W` a
distinguished
polynomial whose degree is the vanishing order of the reduction. Over an algebraically closed
complete field (e.g. `ℂ_p`, whose ring of integers is `O`), `W` splits, and — being
distinguished — all its roots lie in the open disk `𝔪`
(`root_mem_maximalIdeal_of_distinguished`).

(The multiplicity-exact count over the algebraic closure —
`ChabautyColeman.finsum_rootMultiplicity_map` and `ChabautyColeman.zeros_eq_ord`, the analytic
right-hand side of a chart-level form of `thm:spec` — is formalized in
`upstream HyperellipticCurves.Archive.SpecializationGeneric`; the main theorems do not depend on it,
since
the per-disk point sums of `LeanPool.HyperellipticCurves.Specialization.DiskPointSum` enumerate the
zeros as
actual points.)
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace ChabautyColeman

/-- The norm polynomial `P² - f·Q²` commutes with `Polynomial.map`. -/
theorem map_norm_poly {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f P Q : R[X]) :
    (P.map φ) ^ 2 - (f.map φ) * (Q.map φ) ^ 2 = (P ^ 2 - f * Q ^ 2).map φ := by
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]

variable {O F : Type*} [CommRing O] [Field F] [Algebra O F] [IsFractionRing O F]

/-- Every root in `F` of a distinguished polynomial comes from the maximal ideal of `O`, so
all the zeros counted by `ChabautyColeman.finsum_rootMultiplicity_maximalIdeal` lie in the
(open) disk `𝔪`. -/
theorem root_mem_maximalIdeal_of_distinguished [IsLocalRing O] [IsIntegrallyClosed O]
    {W : O[X]} (hW : W.IsDistinguishedAt (maximalIdeal O)) {z : F}
    (hz : (W.map (algebraMap O F)).IsRoot z) : ∃ w ∈ maximalIdeal O, algebraMap O F w = z := by
  have hint : IsIntegral O z := ⟨W, hW.monic, by rwa [← eval_map]⟩
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨w, PSeries.mem_maximalIdeal_of_isRoot hW ?_, hw⟩
  have h0 : algebraMap O F (W.eval w) = 0 := by rwa [← eval_map_apply, hw]
  exact (map_eq_zero_iff _ (IsFractionRing.injective O F)).mp h0

end ChabautyColeman
