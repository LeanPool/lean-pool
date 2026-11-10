/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.OmegaExpansion
public import LeanPool.HyperellipticCurves.Disks.OmegaExpansionInf
public import LeanPool.HyperellipticCurves.Series.Strassmann

import LeanPool.HyperellipticCurves.ForMathlib.PowerSeries

/-!
# Order matching: the order of a reduced disk expansion

For a regular differential `ω = h(x) dx/y` (`h_bar ≠ 0`) the order `m_{P_bar} := ord_z(w_bar_D)` of
the
reduced disk expansion at a residue point `P_bar` — the quantity feeding the antiderivative zero
count (`ChabautyColeman.PSeries.antideriv_zeros_le`) — is computed explicitly per chart. The key
tool is `ChabautyColeman.order_aeval_of_order_sub`: the order of a polynomial evaluated at a power
series is the root multiplicity times the order of `s - s(0)`.

* Generic disk `(ā, b_bar)`: `m_{P_bar} = rootMultiplicity ā h_bar`
(`order_map_omegaExpansionGeneric`).
* Weierstrass disk `(ω_bar, 0)`: `m_{P_bar} = 2·rootMultiplicity ω_bar h_bar`
  (`order_map_omegaExpansionWeierstrass`); `x - ω` has a double zero in `z = y`.
* Infinity disk: `m_{P_bar} = 2·rootMultiplicity₀(reflect_{g-1} h_bar) = 2(g-1) - 2·deg h_bar`
  (`order_map_omegaExpansionInf`); `u = 1/x` has a double zero in `z = t`.

Blueprint node: `lem:ord-match`.
-/

@[expose] public section

open PowerSeries IsLocalRing Polynomial

namespace ChabautyColeman

variable {κ : Type*} [Field κ]

/-- The order of a polynomial `p` evaluated at a power series `s` with `s(0) = c` is the root
multiplicity of `p` at `c` times the order of `s - c`. (For `s = X + c` this specializes to
`ChabautyColeman.PSeries.order_coe_taylor`.) -/
theorem order_aeval_of_order_sub {s : κ⟦X⟧} {c : κ} (hsc : constantCoeff s = c) {p : κ[X]}
    (hp : p ≠ 0) :
    (aeval s p).order = p.rootMultiplicity c • (s - PowerSeries.C c).order := by
  set m := p.rootMultiplicity c
  set g := p /ₘ (Polynomial.X - Polynomial.C c) ^ m
  have hfac : (Polynomial.X - Polynomial.C c) ^ m * g = p :=
    pow_mul_divByMonic_rootMultiplicity_eq p c
  have hgc : g.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hp
  have hsX : aeval s (Polynomial.X - Polynomial.C c) = s - PowerSeries.C c := by
    rw [map_sub, aeval_X, aeval_C, PowerSeries.algebraMap_eq]
  have hgorder : (aeval s g).order = 0 :=
    PowerSeries.order_eq_zero_of_constantCoeff_ne_zero
      (by rw [PowerSeries.constantCoeff_aeval, hsc]; exact hgc)
  calc (aeval s p).order = (aeval s ((Polynomial.X - Polynomial.C c) ^ m) * aeval s g).order := by
        rw [← map_mul, hfac]
    _ = ((s - PowerSeries.C c) ^ m).order + (aeval s g).order := by rw [order_mul, map_pow, hsX]
    _ = m • (s - PowerSeries.C c).order := by rw [order_pow, hgorder, add_zero]

/-- A simple root (a root of `p` but not of `p'`) has multiplicity `1`. -/
theorem rootMultiplicity_eq_one {p : κ[X]} (hp : p ≠ 0) {a : κ} (hpa : p.eval a = 0)
    (hd : p.derivative.eval a ≠ 0) : p.rootMultiplicity a = 1 :=
  le_antisymm (not_lt.mp fun hlt ↦ hd ((one_lt_rootMultiplicity_iff_isRoot hp).mp hlt).2)
    ((rootMultiplicity_pos hp).mpr hpa)

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- If the reduction of the constant coefficient is nonzero, the reduced series has order `0`. -/
theorem order_map_residue_eq_zero {φ : O⟦X⟧} (h : residue O (PowerSeries.constantCoeff φ) ≠ 0) :
    ((PowerSeries.map (residue O)) φ).order = 0 := by
  refine PowerSeries.order_eq_zero_of_constantCoeff_ne_zero ?_
  rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The reduced Weierstrass coordinate series has a double zero at its centre: `f(x(z)) = z²` and
`ω` is a simple root of `f`, so `x(z) - ω` has order `2` in the local parameter `z = y`. -/
theorem order_map_weierstrassSeries_sub_C {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    ((weierstrassSeries hf hdeg hω hu).map (residue O)
      - PowerSeries.C (residue O ω)).order = 2 := by
  set ρ := residue O
  have hfmap : f.map ρ ≠ 0 := (hf.map ρ).ne_zero
  have hsc : constantCoeff ((weierstrassSeries hf hdeg hω hu).map ρ) = ρ ω := by simp
  have hrm1 : (f.map ρ).rootMultiplicity (ρ ω) = 1 := by
    refine rootMultiplicity_eq_one hfmap ?_ ?_
    · rw [eval_map_apply, hω, map_zero]
    · rw [derivative_map, eval_map_apply]; exact (hu.map ρ).ne_zero
  have key : (aeval ((weierstrassSeries hf hdeg hω hu).map ρ) (f.map ρ)).order
      = ((PowerSeries.X : (ResidueField O)⟦X⟧) ^ 2).order := by
    rw [← PowerSeries.map_aeval, weierstrassSeries_eval, map_pow, PowerSeries.map_X]
  rw [order_aeval_of_order_sub hsc hfmap, hrm1, one_smul, order_pow, order_X] at key
  simpa using key

/-- **Order matching, generic chart.** The order of the reduced generic-disk expansion of
`ω = h(x) dx/y` equals the root multiplicity of `h_bar` at `ā` — i.e. `ord_{P_bar}(ω_bar)` at the
generic
point `P_bar = (ā, b_bar)`. -/
theorem order_map_omegaExpansionGeneric {f h : O[X]} {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (hh : h.map (residue O) ≠ 0) :
    ((omegaExpansionGeneric f h a b).map (residue O)).order
      = (h.map (residue O)).rootMultiplicity (residue O a) := by
  set ρ := residue O
  have hbu : IsUnit b := isUnit_b hb hfa
  rw [omegaExpansionGeneric, map_mul, map_mul, order_mul, order_mul]
  have hB : ((PowerSeries.C (Ring.inverse b)).map ρ).order = 0 := by
    refine PowerSeries.order_eq_zero_of_constantCoeff_ne_zero ?_
    rw [PowerSeries.map_C, PowerSeries.constantCoeff_C]
    have hne : ρ (Ring.inverse b) * ρ b ≠ 0 := by
      rw [← map_mul, Ring.inverse_mul_cancel _ hbu, map_one]; exact one_ne_zero
    exact left_ne_zero_of_mul hne
  have hC : ((invOfUnit (diskSeriesGeneric f a) 1).map ρ).order = 0 := by
    refine PowerSeries.order_eq_zero_of_constantCoeff_ne_zero ?_
    rw [PowerSeries.constantCoeff_map, constantCoeff_invOfUnit, inv_one, Units.val_one, map_one]
    exact one_ne_zero
  rw [hB, hC, add_zero, add_zero, ← polynomial_map_coe, map_taylor, PSeries.order_coe_taylor hh]

/-- **Order matching, Weierstrass chart.** At the Weierstrass point `(ω_bar, 0)` the reduced
expansion has order `2·rootMultiplicity ω_bar h_bar` (the local parameter is `y = z`, and `x - ω`
has a
double zero). -/
theorem order_map_omegaExpansionWeierstrass {f h : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω))
    (hh : h.map (residue O) ≠ 0) (h2 : (2 : ResidueField O) ≠ 0) :
    ((omegaExpansionWeierstrass h hf hdeg hω hu).map (residue O)).order
      = (h.map (residue O)).rootMultiplicity (residue O ω) • (2 : ℕ∞) := by
  set ρ := residue O
  set ws := weierstrassSeries hf hdeg hω hu with hws
  have hsc : constantCoeff ((PowerSeries.map ρ) ws) = ρ ω := by simp [hws]
  have hord2 : ((PowerSeries.map ρ) ws - PowerSeries.C (ρ ω)).order = 2 :=
    order_map_weierstrassSeries_sub_C hf hdeg hω hu
  have hunit : IsUnit (aeval ws f.derivative) := isUnit_aeval_deriv_weierstrassSeries hf hdeg hω hu
  have hinv0 : ((PowerSeries.map ρ) (Ring.inverse (aeval ws f.derivative))).order = 0 := by
    refine PowerSeries.order_eq_zero_of_constantCoeff_ne_zero ?_
    have hprod : constantCoeff ((PowerSeries.map ρ) (aeval ws f.derivative))
        * constantCoeff ((PowerSeries.map ρ) (Ring.inverse (aeval ws f.derivative))) = 1 := by
      rw [← map_mul, ← map_mul, Ring.mul_inverse_cancel _ hunit, map_one, map_one]
    exact right_ne_zero_of_mul (by rw [hprod]; exact one_ne_zero)
  have h2ne : residue O (PowerSeries.constantCoeff (2 : O⟦X⟧)) ≠ 0 := by
    simp only [map_ofNat]; exact h2
  rw [omegaExpansionWeierstrass, map_mul, map_mul, order_mul, order_mul,
    order_map_residue_eq_zero h2ne, zero_add, hinv0, add_zero, PowerSeries.map_aeval,
    order_aeval_of_order_sub hsc hh, hord2]

/-- **Order matching, infinity chart.** At the infinity point the reduced expansion has order
`2·rootMultiplicity₀(reflect_{g-1} h_bar) = 2(g-1) - 2·deg h_bar` (the local parameter is `z = t`,
and
`u = 1/x` has a double zero). -/
theorem order_map_omegaExpansionInf {f h : O[X]} (hf : f.Monic) (hh : h.map (residue O) ≠ 0)
    (h2 : (2 : ResidueField O) ≠ 0) :
    ((omegaExpansionInf h hf).map (residue O)).order
      = (reflect (genus f - 1) (h.map (residue O))).rootMultiplicity 0 • (2 : ℕ∞) := by
  set ρ := residue O
  set u := infSeries hf with hu
  have hsc : constantCoeff ((PowerSeries.map ρ) u) = 0 := by simp [hu]
  have hord2 : ((PowerSeries.map ρ) u).order = 2 := order_map_infSeries hf
  set D := 1 - PowerSeries.X ^ 2 * aeval u f.reverse.derivative
  have hinv0 : ((PowerSeries.map ρ) (Ring.inverse D)).order = 0 := by
    refine PowerSeries.order_eq_zero_of_constantCoeff_ne_zero ?_
    have hprod : constantCoeff ((PowerSeries.map ρ) D)
        * constantCoeff ((PowerSeries.map ρ) (Ring.inverse D)) = 1 := by
      rw [← map_mul, ← map_mul, Ring.mul_inverse_cancel _ (isUnit_infDenom hf), map_one, map_one]
    exact right_ne_zero_of_mul (by rw [hprod]; exact one_ne_zero)
  have hrefl : (reflect (genus f - 1) h).map ρ = reflect (genus f - 1) (h.map ρ) :=
    (reflect_map ρ h _).symm
  have hreflne : reflect (genus f - 1) (h.map ρ) ≠ 0 := fun hz ↦ hh (reflect_eq_zero_iff.mp hz)
  have h2ne : residue O (PowerSeries.constantCoeff (-2 : O⟦X⟧)) ≠ 0 := by
    simp only [map_neg, map_ofNat]; exact neg_ne_zero.mpr h2
  rw [omegaExpansionInf, map_mul, map_mul, order_mul, order_mul,
    order_map_residue_eq_zero h2ne, zero_add, hinv0, add_zero, PowerSeries.map_aeval, hrefl,
    order_aeval_of_order_sub hsc hreflne, map_zero, sub_zero, hord2]

end ChabautyColeman
