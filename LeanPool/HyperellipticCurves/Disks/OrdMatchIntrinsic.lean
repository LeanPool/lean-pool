/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.InftyPlace
public import LeanPool.HyperellipticCurves.Curve.PointValuation
public import LeanPool.HyperellipticCurves.Disks.OrdMatch
public import LeanPool.HyperellipticCurves.Disks.OrdPoint

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# Order matching: reduced expansion order = intrinsic order

`lem:ord-match`: for the differential `ω = h(x) dx/y`, the order of the reduced disk expansion
`w_bar_D` at a residue point `P_bar` — computed via the disk chart in
`HyperellipticCurves/Disks/OrdMatch.lean` — equals
the *intrinsic* order `ord_{P_bar}(ω_bar)`. The order of a differential at a point is taken in a
local
uniformizer (the disk parameter `z`); this file identifies the chart order with the intrinsic
function order plus the canonical (differential) contribution:

* generic `(ā, b_bar)`: `ord_z(w_bar_D) = ord_{P_bar}(h_bar)` (`ordMatch_generic`), the point-ideal
multiplicity
  (`HyperellipticCurves/Curve/PointValuation.lean`), since `dx/y` is regular nonvanishing there;
* Weierstrass `(ω_bar, 0)`: `ord_z(w_bar_D) = ord_{P_bar}(h_bar)` (`ordMatch_weierstrass`), `=
2·rootMult`;
* infinity: `ord_z(w_bar_D) = ord_∞(h_bar) + (2g-2)` (`ordMatch_inf`), with `ord_∞(h_bar) = -2·deg
h_bar` the
  function order (`HyperellipticCurves/Curve/InftyPlace.lean`) and `2g-2` the canonical divisor
  contribution.

In the form the per-disk count of blueprint `thm:disk-bound` consumes it, the statement is
that the expansion has a *unit* coefficient in degree `ord_P_bar(ω_bar)`, in all three charts
(`ChabautyColeman.isUnit_coeff_ordAffine_omegaExpansionGeneric`,
`ChabautyColeman.isUnit_coeff_ordAffine_omegaExpansionWeierstrass`,
`ChabautyColeman.isUnit_coeff_ordInf_omegaExpansionInf`): the reduced expansion has exactly
that order, so its coefficient there is nonzero, hence the integral one is a unit.

Blueprint node: `lem:ord-match`.
-/

@[expose] public section

open PowerSeries IsLocalRing Polynomial

namespace ChabautyColeman

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- A coefficient of an integral power series in the degree where its reduction has its order
is a unit — the reduction is nonzero there. -/
theorem isUnit_coeff_of_order_map_eq {W : O⟦X⟧} {n : ℕ}
    (hord : (W.map (residue O)).order = n) :
    IsUnit (PowerSeries.coeff n W) := by
  have hne := (PowerSeries.order_eq_nat.mp hord).1
  rw [PowerSeries.coeff_map] at hne
  exact (residue_ne_zero_iff_isUnit _).mp hne

variable {f : O[X]}

/-- **The infinity disk expansion has a unit coefficient in degree `ord_P_bar(ω_bar)`** — the
companion of `ChabautyColeman.isUnit_coeff_ordAffine_omegaExpansionGeneric` at the point at
infinity, where the intrinsic order is `2g-2-2·deg h_bar`. -/
theorem isUnit_coeff_ordInf_omegaExpansionInf {h : O[X]} (hf : f.Monic)
    (hh : h.map (residue O) ≠ 0) (hdeg : (h.map (residue O)).natDegree ≤ genus f - 1)
    (h2 : (2 : ResidueField O) ≠ 0) :
    IsUnit (PowerSeries.coeff (ordInf (f.map (residue O)) (h.map (residue O)))
      (omegaExpansionInf h hf)) := by
  have harith : 2 * (genus f - 1) - 2 * (h.map (residue O)).natDegree
      = 2 * (genus f - 1 - (h.map (residue O)).natDegree) := by lia
  refine isUnit_coeff_of_order_map_eq ?_
  rw [order_map_omegaExpansionInf hf hh h2, rootMultiplicity_zero_reflect hh hdeg, ordInf_eq,
    genus_map hf, harith, nsmul_eq_mul]
  push_cast
  ring

variable [Fact (Odd (f.map (residue O)).natDegree)]

/-- **Order matching, infinity chart (intrinsic).** The reduced expansion order equals the
intrinsic order at `∞`: `ord_∞(h_bar) + (2g-2)`, with `ord_∞(h_bar) = -2·deg h_bar` the function
order and
`2g-2` the canonical (differential) contribution. -/
theorem ordMatch_inf {h : O[X]} (hf : f.Monic) (hh : h.map (residue O) ≠ 0)
    (hdeg : (h.map (residue O)).natDegree ≤ genus f - 1) (hg : 1 ≤ genus f)
    (h2 : (2 : ResidueField O) ≠ 0) :
    (((omegaExpansionInf h hf).map (residue O)).order.toNat : ℤ)
      = inftyOrd (algebraMap (RatFunc (ResidueField O))
          (HypField (ResidueField O) (f.map (residue O)))
            (algebraMap (ResidueField O)[X] (RatFunc (ResidueField O)) (h.map (residue O))))
        + 2 * ((genus f : ℤ) - 1) := by
  rw [order_map_omegaExpansionInf hf hh h2, rootMultiplicity_zero_reflect hh hdeg,
    inftyOrd_algebraMap, nsmul_eq_mul, ← Nat.cast_ofNat (n := 2), ← Nat.cast_mul,
    ENat.toNat_natCast]
  push_cast [Nat.cast_sub hdeg, Nat.cast_sub hg]
  ring

variable [NeZero (2 : ResidueField O)] [Fact (Squarefree (f.map (residue O)))]

/-- **Order matching, generic chart (intrinsic).** The reduced expansion order equals the
intrinsic order of `h_bar` at the generic residue point `(ā, b_bar)` (`dx/y` is regular there). -/
theorem ordMatch_generic {h : O[X]} {a b : O} (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a))
    (hh : h.map (residue O) ≠ 0) :
    ((omegaExpansionGeneric f h a b).map (residue O)).order
      = emultiplicity (pointIdeal (f.map (residue O)) (residue O a) (residue O b))
          (Ideal.span {(algebraMap (ResidueField O)[X]
            (HypRing (ResidueField O) (f.map (residue O))) (h.map (residue O)))}) := by
  have hbr : (residue O b) ^ 2 = (f.map (residue O)).eval (residue O a) := onCurve_map _ hb
  have hyr : residue O b ≠ 0 := ((isUnit_b hb hfa).map (residue O)).ne_zero
  rw [order_map_omegaExpansionGeneric hb hfa hh, emultiplicity_pointIdeal_generic hbr hyr hh]

/-- **Order matching, Weierstrass chart (intrinsic).** The reduced expansion order equals the
intrinsic order of `h_bar` at the Weierstrass residue point `(ω_bar, 0)`. -/
theorem ordMatch_weierstrass {h : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) (hh : h.map (residue O) ≠ 0)
    (h2 : (2 : ResidueField O) ≠ 0) :
    ((omegaExpansionWeierstrass h hf hdeg hω hu).map (residue O)).order
      = emultiplicity (pointIdeal (f.map (residue O)) (residue O ω) 0)
          (Ideal.span {(algebraMap (ResidueField O)[X]
            (HypRing (ResidueField O) (f.map (residue O))) (h.map (residue O)))}) := by
  have hbr : (0 : ResidueField O) ^ 2 = (f.map (residue O)).eval (residue O ω) :=
    onCurve_map_of_root _ hω
  rw [order_map_omegaExpansionWeierstrass hf hdeg hω hu hh h2,
    emultiplicity_pointIdeal_weierstrass hbr hh]

/-! ### The leading coefficient of the disk expansion is a unit -/

/-- **The generic disk expansion has a unit coefficient in degree `ord_P_bar(ω_bar)`** — the
hypothesis `hmu` of the per-disk bound of blueprint `thm:disk-bound`, at the sharpest index.
`lem:ord-match` says that index is the intrinsic order at the residue point. -/
theorem isUnit_coeff_ordAffine_omegaExpansionGeneric {h : O[X]} {a b : O}
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (hh : h.map (residue O) ≠ 0) :
    IsUnit (PowerSeries.coeff (ordAffine (f.map (residue O)) (h.map (residue O))
      (residue O a) (residue O b)) (omegaExpansionGeneric f h a b)) := by
  refine isUnit_coeff_of_order_map_eq ?_
  rw [ordAffine_eq, ← ordMatch_generic hb hfa hh, order_map_omegaExpansionGeneric hb hfa hh]
  simp

/-- **The Weierstrass disk expansion has a unit coefficient in degree `ord_P_bar(ω_bar)`** — the
companion of `ChabautyColeman.isUnit_coeff_ordAffine_omegaExpansionGeneric` at a Weierstrass
residue point. -/
theorem isUnit_coeff_ordAffine_omegaExpansionWeierstrass {h : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω))
    (hh : h.map (residue O) ≠ 0) (h2 : (2 : ResidueField O) ≠ 0) :
    IsUnit (PowerSeries.coeff (ordAffine (f.map (residue O)) (h.map (residue O))
      (residue O ω) 0) (omegaExpansionWeierstrass h hf hdeg hω hu)) := by
  refine isUnit_coeff_of_order_map_eq ?_
  rw [ordAffine_eq, ← ordMatch_weierstrass hf hdeg hω hu hh h2,
    order_map_omegaExpansionWeierstrass hf hdeg hω hu hh h2]
  simp

end ChabautyColeman
