/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.FuncExpansion
public import LeanPool.HyperellipticCurves.Log.Cantor.PipelineCerts
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The curve-to-chart map (`def:phiD`)

Per-disk formalization of `def:phiD` (checked at genus 2 by `prototype/g2_omega_prime.py`):
the expansion of the map
`P ↦ [P] - [P₀] + τ = ([P + ι Q - 2∞] + τ) + [Q + ι P₀ - 2∞]` on a residue disk is a
certified Cantor pipeline over `O⟦z⟧` applied to *pair data*.

This file provides:

* the **pair datum** over any commutative ring: the interpolating line through two
  curve points with unit `x`-separation, with the slope passed as a certificate
  (`ChabautyColeman.pairV`, `ChabautyColeman.pair_dvd`) — the Mumford datum of
  `[pt₁ + pt₂ - 2∞]`;
* the **disk point as a power-series point of the curve**
  (`ChabautyColeman.diskY_sq`): `(b·η(z))² = f(a + z)` in `O⟦z⟧`, from the
  square-root series of `lem:disk-param`;
* the **moving pair datum** over `O⟦z⟧` (`ChabautyColeman.movingPair_dvd`): the line
  through `P_z = (a + z, b·η(z))` and a constant curve point, with unit `x`-separation
  from the center (`ChabautyColeman.isUnit_C_sub_diskX`) and the slope as a certificate;
* **certificate existence over `O⟦z⟧`**
  (`ChabautyColeman.exists_isPipelineCerts_powerSeries`): the generic pipeline lifting
  (`LeanPool.HyperellipticCurves.Log.Cantor.PipelineCerts`) instantiated at the residue map of
  `O⟦z⟧` over a
  local base (`ChabautyColeman.seriesResidue`);
* the **three-block configurations** `ChabautyColeman.diskConfig` (a moving block over
  `O⟦z⟧` with the `τ`-block and the constant pair block), its instance
  `ChabautyColeman.phiConfig` at the generic disk point, and their common reduction
  `ChabautyColeman.diskCenterConfig` at the disk centre;
* the **chart coordinates** of a monic datum relative to a center
  (`ChabautyColeman.chartCoords`, `ChabautyColeman.eq_add_chartCoords`);
* the **pair-class calculus** over a field: a pair datum's class is the product of its
  point classes (`ChabautyColeman.mk0_pair`), and the pair data of `[P + ι Q]` and
  `[Q + ι P]` are inverse classes (`ChabautyColeman.mk0_pair_mul_mk0_pair`);
* **the disk pipeline itself** (`ChabautyColeman.phiPipeline`, with data
  `ChabautyColeman.phiU₁`/`phiV₁`/`phiU₃`/`phiV₃`) and its chart coordinates
  `ζ(z) = ChabautyColeman.phiZeta`, with the **center identification**
  (`ChabautyColeman.phiPipeline_map_constantCoeff`,
  `ChabautyColeman.constantCoeff_phiZeta`): at `z = 0` the pipeline returns the
  `τ`-datum exactly, so `ζ(0) = 0`. The individual blocks reduce to the pair data of the
  centre configuration (`ChabautyColeman.phiU₁_map_seriesResidue`,
  `ChabautyColeman.phiV₁_map_seriesResidue`).

The addition chain is ordered so that all support overlaps are of doubling type
(cancelling overlaps are genuinely singular). The
derivative `ω′ = d/dz Λ(ζ)` is the next layer.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section PairDatum

variable {R : Type*} [CommRing R] {F : R[X]} {α β yα yβ m : R}

/-- The interpolating `v`-polynomial of a pair datum: the line through `(α, yα)` and
`(β, yβ)`, with the slope `m` passed as a certificate `m·(β - α) = yβ - yα`. -/
noncomputable def pairV (α yα m : R) : R[X] := C yα + C m * (X - C α)

@[simp] theorem pairV_eval_left : (pairV α yα m).eval α = yα := by simp [pairV]

theorem pairV_eval_right (hm : m * (β - α) = yβ - yα) :
    (pairV α yα m).eval β = yβ := by
  simp only [pairV, eval_add, eval_mul, eval_sub, eval_C, eval_X]
  linear_combination hm

theorem pairV_degree_lt [Nontrivial R] :
    (pairV α yα m).degree < ((X - C α) * (X - C β)).degree := by
  rw [show ((X - C α) * (X - C β) : R[X]).degree = 2 by compute_degree!]
  calc (pairV α yα m).degree ≤ 1 := by simp only [pairV]; compute_degree!
    _ < 2 := by decide

@[simp] theorem pairV_map {S : Type*} [CommRing S] (φ : R →+* S) (α yα m : R) :
    (pairV α yα m).map φ = pairV (φ α) (φ yα) (φ m) := by
  simp [pairV]

section Transport

variable {S : Type*} [CommRing S] (φ : R →+* S)

/-- Nodes with unit separation stay distinct under any base change: this is what keeps the
two points of a pair block apart over the target ring. -/
theorem map_ne_of_isUnit_sub [Nontrivial S] (h : IsUnit (β - α)) : φ α ≠ φ β :=
  (sub_ne_zero.mp (by rw [← map_sub]; exact (h.map φ).ne_zero)).symm

/-- The slope certificate of a pair block through `(β, -yβ)` and `(α, yα)` transports along
any base change. -/
theorem map_slope (h : m * (β - α) = -yβ - yα) :
    φ m * (φ β - φ α) = -φ yβ - φ yα := by
  simpa using congrArg φ h

/-- A point of the curve stays on the base-changed curve. -/
theorem map_sq_eq_eval_map (h : yα ^ 2 = F.eval α) : φ yα ^ 2 = (F.map φ).eval (φ α) := by
  rw [eval_map_apply, ← h, map_pow]

end Transport

/-- The slope certificates of a pair block and of its opposite are opposite. -/
theorem neg_slope_eq {m' : R} (h : IsUnit (β - α)) (hm : m * (β - α) = -yβ - yα)
    (hm' : m' * (α - β) = -yα - yβ) : m' = -m :=
  eq_neg_of_add_eq_zero_left (h.mul_left_eq_zero.mp (by linear_combination hm - hm'))

/-- **A pair block and its opposite have opposite `v`-parts**: the line through `(α, yα)`
and `(β, -yβ)` is the negative of the line through `(β, yβ)` and `(α, -yα)`. This is what
makes the two outer blocks of the per-disk configuration cancel in the class group. -/
theorem pairV_neg {m' : R} (hmm : m' = -m) (hm : m * (β - α) = -yβ - yα) :
    pairV β yβ m' = -(pairV α yα m) := by
  subst hmm
  simp only [pairV, C_neg]
  linear_combination map_slope (C : R →+* R[X]) hm

/-- Point data are Mumford data: a curve point gives a divisibility certificate. -/
theorem X_sub_C_dvd_C_sq_sub (hα : yα ^ 2 = F.eval α) :
    (X - C α : R[X]) ∣ C yα ^ 2 - F := by
  rw [dvd_iff_isRoot]
  simp [IsRoot, hα]

/-- **The pair datum lies on the curve**: the interpolating line through two curve
points, with unit `x`-separation, is a square root of `F` modulo `(X-α)(X-β)`. -/
theorem pair_dvd (h : IsUnit (β - α)) (hm : m * (β - α) = yβ - yα)
    (hα : yα ^ 2 = F.eval α) (hβ : yβ ^ 2 = F.eval β) :
    (X - C α) * (X - C β) ∣ (pairV α yα m) ^ 2 - F := by
  refine (isCoprime_X_sub_C_of_isUnit_sub h).symm.mul_dvd ?_ ?_
  · rw [dvd_iff_isRoot]
    simp only [IsRoot, eval_sub, eval_pow, pairV_eval_left]
    linear_combination hα
  · rw [dvd_iff_isRoot]
    simp only [IsRoot, eval_sub, eval_pow, pairV_eval_right hm]
    linear_combination hβ

/-- A polynomial with unit value at `α` is coprime to `X - α` — the factors of
`Polynomial.isCoprime_X_sub_C_of_isUnit_eval` in the order the pair datum needs. -/
theorem isCoprime_X_sub_C_of_isUnit_eval {p : R[X]} (h : IsUnit (p.eval α)) :
    IsCoprime (X - C α : R[X]) p :=
  (Polynomial.isCoprime_X_sub_C_of_isUnit_eval h).symm

/-- **Weierstrass avoidance for a pair datum**: the interpolating line is invertible modulo
`(X-α)(X-β)` as soon as both doubled `y`-values are units — for a divisor on the curve, that
neither of its two points is a Weierstrass point. -/
theorem isCoprime_pairV (hm : m * (β - α) = yβ - yα) (hα : IsUnit (2 * yα))
    (hβ : IsUnit (2 * yβ)) :
    IsCoprime ((X - C α) * (X - C β)) (2 * pairV α yα m) :=
  IsCoprime.mul_left (isCoprime_X_sub_C_of_isUnit_eval (by
    simpa using hα))
    (isCoprime_X_sub_C_of_isUnit_eval (by simpa [pairV_eval_right hm] using hβ))

end PairDatum

section DiskDatum

open PowerSeries

variable {O : Type*} [CommRing O] {f : O[X]} {a b : O}

/-- The Taylor expansion as evaluation at the shifted power-series variable. -/
theorem taylor_coe_eq_eval₂ (f : O[X]) (a : O) :
    (taylor a f : O⟦X⟧)
      = f.eval₂ PowerSeries.C (PowerSeries.C a + PowerSeries.X) := by
  rw [← eval₂_C_X_eq_coe, taylor_apply, eval₂_comp, eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_C, add_comm]

/-- **The disk point is a power-series point of the curve**: `(b·η(z))² = f(a + z)` as
power series, for `b² = f(a)` a unit (and `2` a unit). -/
theorem diskY_sq (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a))
    (h2 : IsUnit (2 : O)) :
    (PowerSeries.C b * diskSeriesGeneric f a) ^ 2
      = (f.map (PowerSeries.C : O →+* O⟦X⟧)).eval
          (PowerSeries.C a + PowerSeries.X) := by
  rw [eval_map, mul_pow, diskSeriesGeneric_sq hfa h2, ← map_pow, hb,
    ← taylor_coe_eq_eval₂, mul_left_comm, ← mul_assoc, mul_assoc,
    ← (PowerSeries.C (R := O)).map_mul, Ring.mul_inverse_cancel _ hfa, map_one, mul_one]

end DiskDatum

section MovingPair

open scoped PowerSeries

variable {O : Type*} [CommRing O] {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧}

/-- The `x`-separation of the moving disk point from a constant point is a unit as soon as
it is one at the center. -/
theorem isUnit_C_sub_diskX (hsep : IsUnit (xQ - a)) :
    IsUnit (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X) : O⟦X⟧) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simpa using hsep

/-- **The moving pair datum lies on the curve**: the line through the moving disk point
`P_z = (a + z, b·η(z))` and the constant curve point `(xQ, -yQ)` (the involute of an
auxiliary point `Q`), with slope certificate `m`, is a square root of `f` modulo
`(X - (a+z))·(X - xQ)` over `O⟦z⟧`. -/
theorem movingPair_dvd (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ) :
    (X - Polynomial.C (PowerSeries.C a + PowerSeries.X))
        * (X - Polynomial.C (PowerSeries.C xQ))
      ∣ pairV (PowerSeries.C a + PowerSeries.X) (PowerSeries.C b * diskSeriesGeneric f a) m
          ^ 2 - f.map (PowerSeries.C : O →+* O⟦X⟧) := by
  refine pair_dvd (isUnit_C_sub_diskX hsep) hm (diskY_sq hb hfa h2) ?_
  rw [← map_pow, neg_pow_two, hyQ, eval_map_apply]

end MovingPair

section ChartCoords

variable {O A B : Type*} [CommRing O] [CommRing A] [CommRing B] (φ : O →+* A)

/-- The chart coordinates of a monic polynomial `U` relative to the center `u`: the
coefficients of the perturbation `U - u.map φ`. For the `u`-part of a Cantor pipeline
over `O⟦z⟧` these are the coordinates `ζ(z)` of `def:phiD`. -/
noncomputable def chartCoords (u : O[X]) (U : A[X]) (j : Fin u.natDegree) : A :=
  (U - u.map φ).coeff j

/-- Chart coordinates transform naturally under base change. -/
theorem map_chartCoords (ρ : A →+* B) (u : O[X]) (U : A[X]) (j : Fin u.natDegree) :
    ρ (chartCoords φ u U j) = chartCoords (ρ.comp φ) u (U.map ρ) j := by
  rw [chartCoords, chartCoords, ← coeff_map, Polynomial.map_sub, Polynomial.map_map]

/-- A monic polynomial of the center's degree is the center plus its chart-coordinate
perturbation (the shape of `ChabautyColeman.chartU`). -/
theorem eq_add_chartCoords {u : O[X]} {U : A[X]} (hu : u.Monic) (hU : U.Monic)
    (hdeg : U.natDegree = u.natDegree) :
    U = u.map φ + ∑ j : Fin u.natDegree, C (chartCoords φ u U j) * X ^ (j : ℕ) := by
  simp only [chartCoords]
  rw [Fin.sum_univ_eq_sum_range fun i ↦ C ((U - u.map φ).coeff i) * X ^ i]
  rcases eq_or_ne (U - u.map φ) 0 with h0 | h0
  · rw [sub_eq_zero] at h0
    rw [h0]
    simp
  · have : Nontrivial A := Polynomial.nontrivial_iff.mp (nontrivial_of_ne _ _ h0)
    have hUφ : (u.map φ).Monic := hu.map φ
    have hd : U.degree = (u.map φ).degree := by
      rw [degree_eq_natDegree hU.ne_zero, degree_eq_natDegree hUφ.ne_zero, hdeg, hu.natDegree_map]
    have hlt : (U - u.map φ).degree < (u.natDegree : WithBot ℕ) := by
      have h := degree_sub_lt_left hd hU.ne_zero (by rw [hU.leadingCoeff, hUφ.leadingCoeff])
      rwa [degree_eq_natDegree hU.ne_zero, hdeg] at h
    simp only [C_mul_X_pow_eq_monomial]
    rw [← (U - u.map φ).as_sum_range' _ ((natDegree_lt_iff_degree_lt h0).mpr hlt)]
    ring

end ChartCoords

section SeriesResidue

open PowerSeries IsLocalRing

variable (O : Type*) [CommRing O] [IsLocalRing O]

/-- The residue map of `O⟦z⟧` over a local base: the residue of the constant
coefficient. -/
noncomputable def seriesResidue : O⟦X⟧ →+* ResidueField O :=
  (residue O).comp (constantCoeff : O⟦X⟧ →+* O)

theorem seriesResidue_surjective : Function.Surjective (seriesResidue O) :=
  residue_surjective.comp PowerSeries.constantCoeff_surj

theorem seriesResidue_apply (x : O⟦X⟧) : seriesResidue O x = residue O (constantCoeff x) := rfl

@[simp] theorem seriesResidue_C (x : O) : seriesResidue O (PowerSeries.C x) = residue O x := by
  rw [seriesResidue_apply, constantCoeff_C]

@[simp] theorem seriesResidue_X : seriesResidue O (PowerSeries.X : O⟦X⟧) = 0 := by
  rw [seriesResidue_apply, constantCoeff_X, map_zero]

/-- The moving disk point reduces to the centre. -/
theorem seriesResidue_C_add_X (x : O) :
    seriesResidue O (PowerSeries.C x + PowerSeries.X) = residue O x := by
  rw [map_add, seriesResidue_C, seriesResidue_X, add_zero]

/-- A constant datum reduces to its own residue. -/
theorem map_C_map_seriesResidue (p : O[X]) :
    (p.map (PowerSeries.C : O →+* O⟦X⟧)).map (seriesResidue O) = p.map (residue O) := by
  have h : (p.map (PowerSeries.C : O →+* O⟦X⟧)).map (constantCoeff : O⟦X⟧ →+* O) = p := by
    rw [Polynomial.map_map, constantCoeff_comp_C, Polynomial.map_id]
  rw [seriesResidue, ← Polynomial.map_map, h]

theorem isUnit_of_seriesResidue_ne_zero {x : O⟦X⟧} (hx : seriesResidue O x ≠ 0) :
    IsUnit x :=
  PowerSeries.isUnit_iff_constantCoeff.mpr ((residue_ne_zero_iff_isUnit _).mp hx)

theorem ker_seriesResidue_le_jacobson : RingHom.ker (seriesResidue O) ≤ Ideal.jacobson ⊥ := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact fun x hx ↦ (mem_maximalIdeal x).mpr
    (mem_nonunits_iff.mpr fun hu ↦ (hu.map (seriesResidue O)).ne_zero (RingHom.mem_ker.mp hx))

variable {O}

/-- **Existence of a valid certificate pack for a Cantor pipeline over `O⟦z⟧`**: a valid
and generic pack for the reduced pipeline over the residue field of the local base lifts
to a valid pack over `O⟦z⟧`. -/
theorem exists_isPipelineCerts_powerSeries {f : (O⟦X⟧)[X]} {D : PipelineData O⟦X⟧}
    (hf : f.Monic) (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic) (hu₃ : D.u₃.Monic)
    (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hd₃ : D.u₃ ∣ D.v₃ ^ 2 - f)
    {n : ℕ} (d' : CantorCertData (ResidueField O))
    (hd' : IsPipelineCenterCerts (f.map (seriesResidue O)) (D.map (seriesResidue O)) d' n) :
    ∃ d : CantorCertData O⟦X⟧,
      IsPipelineCerts f D d n ∧ d.map (seriesResidue O) = d' :=
  exists_isPipelineCerts_of_center (seriesResidue_surjective O)
    (fun _ ↦ isUnit_of_seriesResidue_ne_zero O) (ker_seriesResidue_le_jacobson O)
    hf hu₁ hu₂ hu₃ hd₁ hd₂ hd₃ d' hd'

end SeriesResidue

section PairClass

open nonZeroDivisors

variable {K : Type*} [Field K] {f : K[X]} {α β yα yβ m : K} [NeZero (2 : K)]
  [Fact (Odd f.natDegree)] [Fact (Squarefree f)]

/-- **The class of a pair datum is the product of its point classes.** -/
theorem mk0_pair (hne : α ≠ β) (hm : m * (β - α) = yβ - yα)
    (hα : yα ^ 2 = f.eval α) (hβ : yβ ^ 2 = f.eval β) :
    ClassGroup.mk0 ⟨mumfordIdeal f ((X - C α) * (X - C β)) (pairV α yα m),
        mumfordIdeal_mem_nonZeroDivisors f
          (((monic_X_sub_C α).mul (monic_X_sub_C β)).ne_zero) _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (X - C α) (C yα),
            mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C α).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f (X - C β) (C yβ),
            mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C β).ne_zero _⟩ := by
  have hunit : IsUnit (β - α) := (sub_ne_zero.mpr (Ne.symm hne)).isUnit
  have hcop := (isCoprime_X_sub_C_of_isUnit_sub (R := K) hunit).symm
  obtain ⟨s₁, s₂, hs⟩ := id hcop
  have hbez : s₁ * (X - C α) + s₂ * (X - C β) + 0 * (C yα + C yβ) = 1 := by
    rw [zero_mul, add_zero]; exact hs
  rw [mk0_mumfordIdeal_mul_of_bezout f hbez (X_sub_C_dvd_C_sq_sub hα)
    (X_sub_C_dvd_C_sq_sub hβ) (monic_X_sub_C α).ne_zero (monic_X_sub_C β).ne_zero]
  obtain ⟨w₁, hw₁⟩ := X_sub_C_dvd_C_sq_sub hα
  obtain ⟨w₂, hw₂⟩ := X_sub_C_dvd_C_sq_sub hβ
  have hmC : C m * (C β - C α) = C yβ - C yα := by rw [← C_sub, ← C_mul, hm, C_sub]
  have hdvd : (X - C α) * (X - C β)
      ∣ cantorV f (X - C α) (C yα) (X - C β) (C yβ) s₁ s₂ 0 - pairV α yα m :=
    hcop.mul_dvd ⟨s₁ * (C yβ - C yα) - C m,
        by simp only [pairV]; linear_combination cantorV_sub_left f hbez hw₁⟩
      ⟨s₂ * (C yα - C yβ) - C m,
        by simp only [pairV]; linear_combination cantorV_sub_right f hbez hw₂ - hmC⟩
  obtain ⟨q, hq⟩ := hdvd
  have hV : cantorV f (X - C α) (C yα) (X - C β) (C yβ) s₁ s₂ 0
      = pairV α yα m + (X - C α) * (X - C β) * q := by linear_combination hq
  have hid : mumfordIdeal f ((X - C α) * (X - C β)) (pairV α yα m)
      = mumfordIdeal f ((X - C α) * (X - C β))
        (cantorV f (X - C α) (C yα) (X - C β) (C yβ) s₁ s₂ 0) := by
    rw [hV, mumfordIdeal_add_mul]
  exact congrArg ClassGroup.mk0 (Subtype.ext hid)

/-- **The two auxiliary pair data cancel in the class group**: for curve points
`P = (xP, yP)` and `Q = (xQ, yQ)` with distinct `x`-coordinates, the pair data of
`[P + ιQ - 2∞]` and `[Q + ιP - 2∞]` represent inverse classes. This is the cancellation
behind the center identification `ζ(0) = 0` of `def:phiD`. -/
theorem mk0_pair_mul_mk0_pair {xP yP xQ yQ m m' : K} (hne : xP ≠ xQ)
    (hm : m * (xQ - xP) = -yQ - yP) (hm' : m' * (xP - xQ) = -yP - yQ)
    (hP : yP ^ 2 = f.eval xP) (hQ : yQ ^ 2 = f.eval xQ) :
    ClassGroup.mk0 ⟨mumfordIdeal f ((X - C xP) * (X - C xQ)) (pairV xP yP m),
        mumfordIdeal_mem_nonZeroDivisors f
          (((monic_X_sub_C xP).mul (monic_X_sub_C xQ)).ne_zero) _⟩
      * ClassGroup.mk0 ⟨mumfordIdeal f ((X - C xQ) * (X - C xP)) (pairV xQ yQ m'),
          mumfordIdeal_mem_nonZeroDivisors f
            (((monic_X_sub_C xQ).mul (monic_X_sub_C xP)).ne_zero) _⟩ = 1 := by
  rw [mk0_pair hne hm hP (by rwa [neg_pow_two]), mk0_pair hne.symm hm' hQ (by rwa [neg_pow_two])]
  simp only [map_neg]
  have h1 := mk0_mumfordIdeal_mul_neg f (monic_X_sub_C xP) (X_sub_C_dvd_C_sq_sub hP)
  have h2 := mk0_mumfordIdeal_mul_neg f (monic_X_sub_C xQ) (X_sub_C_dvd_C_sq_sub hQ)
  rw [eq_inv_of_mul_eq_one_right h1, eq_inv_of_mul_eq_one_right h2]
  group

/-- **The middle point of two chained pair data cancels in the class group**:
`[P + ιQ - 2∞] + [Q + ιR - 2∞] = [P + ιR - 2∞]` at the level of point classes. -/
theorem mk0_pair_mul_mk0_pair_chain {xP yP xQ yQ xR yR mPQ mQR : K}
    (hnePQ : xP ≠ xQ) (hneQR : xQ ≠ xR)
    (hmPQ : mPQ * (xQ - xP) = -yQ - yP) (hmQR : mQR * (xR - xQ) = -yR - yQ)
    (hP : yP ^ 2 = f.eval xP) (hQ : yQ ^ 2 = f.eval xQ) (hR : yR ^ 2 = f.eval xR) :
    ClassGroup.mk0 ⟨mumfordIdeal f ((X - C xP) * (X - C xQ)) (pairV xP yP mPQ),
        mumfordIdeal_mem_nonZeroDivisors f
          (((monic_X_sub_C xP).mul (monic_X_sub_C xQ)).ne_zero) _⟩
      * ClassGroup.mk0 ⟨mumfordIdeal f ((X - C xQ) * (X - C xR)) (pairV xQ yQ mQR),
          mumfordIdeal_mem_nonZeroDivisors f
            (((monic_X_sub_C xQ).mul (monic_X_sub_C xR)).ne_zero) _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (X - C xP) (C yP),
            mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C xP).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f (X - C xR) (C (-yR)),
            mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C xR).ne_zero _⟩ := by
  rw [mk0_pair hnePQ hmPQ hP (by rwa [neg_pow_two]), mk0_pair hneQR hmQR hQ (by rwa [neg_pow_two])]
  simp only [map_neg]
  have h1 := mk0_mumfordIdeal_mul_neg f (monic_X_sub_C xQ) (X_sub_C_dvd_C_sq_sub hQ)
  rw [eq_inv_of_mul_eq_one_right h1]
  group

end PairClass

section PhiData

open scoped PowerSeries

variable {O : Type*} [CommRing O]

/-- The `u`-polynomial of the moving pair datum of `def:phiD`: the divisor
`(P_z) + (ι Q)` with `P_z = (a + z, b·η(z))` the moving disk point and `Q = (xQ, yQ)`
the auxiliary point. -/
noncomputable def phiU₁ (a xQ : O) : (O⟦X⟧)[X] :=
  (X - C (PowerSeries.C a + PowerSeries.X)) * (X - C (PowerSeries.C xQ))

/-- The moving pair block splits along any ring homomorphism out of `O⟦z⟧`. -/
theorem phiU₁_map {S : Type*} [CommRing S] (φ : O⟦X⟧ →+* S) (a xQ : O) :
    (phiU₁ a xQ).map φ
      = (X - C (φ (PowerSeries.C a + PowerSeries.X))) * (X - C (φ (PowerSeries.C xQ))) := by
  simp [phiU₁]

/-- The `v`-polynomial of the moving pair datum of `def:phiD` (slope certificate `m`). -/
noncomputable def phiV₁ (f : O[X]) (a b : O) (m : O⟦X⟧) : (O⟦X⟧)[X] :=
  pairV (PowerSeries.C a + PowerSeries.X) (PowerSeries.C b * diskSeriesGeneric f a) m

/-- The `u`-polynomial of the constant pair datum of `def:phiD`: the divisor
`(Q) + (ι P₀)` with `P₀ = (a, b)` the disk center. -/
noncomputable def phiU₃ (a xQ : O) : (O⟦X⟧)[X] :=
  ((X - C xQ) * (X - C a)).map (PowerSeries.C : O →+* O⟦X⟧)

/-- The `v`-polynomial of the constant pair datum of `def:phiD` (slope certificate
`m₀`). -/
noncomputable def phiV₃ (xQ yQ m₀ : O) : (O⟦X⟧)[X] :=
  (pairV xQ yQ m₀).map (PowerSeries.C : O →+* O⟦X⟧)

/-- **The per-disk three-block configuration** over `O⟦z⟧`: a moving pair block `(u₁, v₁)`
through the disk point and `ι Q`, the constant `τ`-block, and the constant pair block
`[Q + ι P₀]` at the disk centre `a`. Both the generic chart (`ChabautyColeman.phiU₁`,
`ChabautyColeman.phiV₁`) and the Weierstrass chart (`ChabautyColeman.wU₁`,
`ChabautyColeman.wV₁`) differ only in the moving block. -/
@[simps] noncomputable def diskConfig (u₁ v₁ : (O⟦X⟧)[X]) (a xQ yQ m₀ : O) (uτ vτ : O[X]) :
    PipelineData O⟦X⟧ :=
  ⟨u₁, v₁, uτ.map PowerSeries.C, vτ.map PowerSeries.C, phiU₃ a xQ, phiV₃ xQ yQ m₀⟩

/-- **The per-disk configuration at the disk centre**, over the base ring: the value of
`ChabautyColeman.diskConfig` at `z = 0`, with the moving block the pair datum of the centre
`(a, b)` and the auxiliary point `(xQ, yQ)` (slope certificate `m`). -/
@[simps] noncomputable def diskCenterConfig (a b xQ yQ m m₀ : O) (uτ vτ : O[X]) :
    PipelineData O :=
  ⟨(X - C a) * (X - C xQ), pairV a b m, uτ, vτ, (X - C xQ) * (X - C a), pairV xQ yQ m₀⟩

variable (f : O[X]) (a b xQ yQ : O) (m : O⟦X⟧) (m₀ : O) (uτ vτ : O[X])
  (d : CantorCertData O⟦X⟧)

/-- The per-disk configuration of `def:phiD`, with the moving pair block through the
generic disk point `P_z = (a + z, b·η(z))`. -/
@[simps!] noncomputable def phiConfig : PipelineData O⟦X⟧ :=
  diskConfig (phiU₁ a xQ) (phiV₁ f a b m) a xQ yQ m₀ uτ vτ

/-- **The disk pipeline of `def:phiD`**: the Cantor pipeline computing
`[P_z + ι Q - 2∞] + τ + [Q + ι P₀ - 2∞] = [P_z] - [P₀] + τ` over `O⟦z⟧`, steered by the
certificate pack `d`. The addition chain is ordered so that all support overlaps are of
doubling type. -/
noncomputable def phiPipeline : (O⟦X⟧)[X] × (O⟦X⟧)[X] :=
  cantorPipeline (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d

/-- **The disk chart coordinates `ζ(z)` of `def:phiD`**: the coefficients of the
perturbation of the pipeline's `u`-part relative to the `τ`-center. -/
noncomputable def phiZeta (j : Fin uτ.natDegree) : O⟦X⟧ :=
  chartCoords PowerSeries.C uτ (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1 j

end PhiData

section PhiResidue

open scoped PowerSeries
open IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {f : O[X]} {a b xQ : O} {m : O⟦X⟧}

/-- The moving pair datum reduces to the pair `(P_bar₀) + (ι Q_bar)` at the disk centre. -/
theorem phiU₁_map_seriesResidue :
    (phiU₁ a xQ).map (seriesResidue O) = ((X - C a) * (X - C xQ)).map (residue O) := by
  rw [phiU₁_map, seriesResidue_C_add_X, seriesResidue_C]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C]

theorem phiV₁_map_seriesResidue :
    (phiV₁ f a b m).map (seriesResidue O)
      = (pairV a b (PowerSeries.constantCoeff m)).map (residue O) := by
  have hb : seriesResidue O (PowerSeries.C b * diskSeriesGeneric f a) = residue O b := by
    rw [map_mul, seriesResidue_C, seriesResidue_apply, constantCoeff_diskSeriesGeneric,
      map_one, mul_one]
  rw [phiV₁, pairV_map, pairV_map, seriesResidue_C_add_X, hb, seriesResidue_apply]

/-- **The per-disk configuration reduces to the centre configuration**: at `z = 0` the
moving pair block becomes the pair block of the disk centre `(a, b)` and the auxiliary
point `Q`, so the whole configuration is the base-ring one of
`ChabautyColeman.diskCenterConfig`, reduced. -/
theorem phiConfig_map_seriesResidue (yQ m₀ : O) (uτ vτ : O[X]) :
    (phiConfig f a b xQ yQ m m₀ uτ vτ).map (seriesResidue O)
      = (diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map
        (residue O) := by
  simp only [PipelineData.map, phiConfig, diskConfig, diskCenterConfig, phiU₁_map_seriesResidue,
    phiV₁_map_seriesResidue, map_C_map_seriesResidue, phiU₃, phiV₃]

end PhiResidue

section CenterZero

open scoped PowerSeries
open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧}
  {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The centre of a disk pipeline is the `τ`-datum**: for any moving pair block `(u₁, v₁)`
that becomes the pair block of the centre `(a, b)` and the auxiliary point `Q` at `z = 0`,
evaluating the pipeline there returns `(uτ, vτ)` exactly. The two pair data at `z = 0` are
`[P₀ + ι Q - 2∞]` and `[Q + ι P₀ - 2∞]`, whose classes cancel, so over the fraction field the
pipeline output and the `τ`-datum are reduced representatives of the same class; the
identification descends to `O` by injectivity. The generic and the Weierstrass chart differ
only in the moving block, which enters through `hidu₁`, `hidv₁` and the mapped slope
identity `hmF`. -/
theorem cantorPipeline_map_constantCoeff_of_pair (hf : f.Monic) {u₁ v₁ : (O⟦X⟧)[X]}
    (hu₁ : u₁.Monic) (hd₁ : u₁ ∣ v₁ ^ 2 - f.map PowerSeries.C)
    (hidu₁ : u₁.map ((algebraMap O (FractionRing O)).comp PowerSeries.constantCoeff)
      = (X - C (algebraMap O (FractionRing O) a)) * (X - C (algebraMap O (FractionRing O) xQ)))
    (hidv₁ : v₁.map ((algebraMap O (FractionRing O)).comp PowerSeries.constantCoeff)
      = pairV (algebraMap O (FractionRing O) a) (algebraMap O (FractionRing O) b)
        (algebraMap O (FractionRing O) (PowerSeries.constantCoeff m)))
    (hsep : IsUnit (xQ - a))
    (hmF : PowerSeries.constantCoeff m * (xQ - a) = -yQ - b)
    (hm₀ : m₀ * (a - xQ) = -b - yQ) (hb : b ^ 2 = f.eval a) (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hvτ : vτ.degree < uτ.degree) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C)
      (diskConfig u₁ v₁ a xQ yQ m₀ uτ vτ) d uτ.natDegree) :
    (cantorPipeline (f.map PowerSeries.C) (diskConfig u₁ v₁ a xQ yQ m₀ uτ vτ) d).1.map
        PowerSeries.constantCoeff = uτ
      ∧ (cantorPipeline (f.map PowerSeries.C) (diskConfig u₁ v₁ a xQ yQ m₀ uτ vτ) d).2.map
        PowerSeries.constantCoeff = vτ := by
  set F := FractionRing O
  set φF : O →+* F := algebraMap O F
  set ε : O⟦X⟧ →+* O := PowerSeries.constantCoeff with hε
  set ρ : O⟦X⟧ →+* F := φF.comp ε with hρ
  have hinj : Function.Injective φF := IsFractionRing.injective O F
  -- basic facts about the pipeline data over `O⟦z⟧`
  have hu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).Monic := huτ.map _
  have hu₃ : (phiU₃ a xQ (O := O)).Monic :=
    ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hd₂ : uτ.map (PowerSeries.C : O →+* O⟦X⟧)
      ∣ (vτ.map PowerSeries.C) ^ 2 - f.map PowerSeries.C := map_dvd_sq_sub _ hdvdτ
  have hsep' : IsUnit (a - xQ) := by rw [← neg_sub]; exact hsep.neg
  have hd₃ : phiU₃ a xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - f.map (PowerSeries.C : O →+* O⟦X⟧) :=
    map_dvd_sq_sub _ (pair_dvd hsep' hm₀ hyQ (by rwa [neg_pow_two]))
  -- the composite evaluation `ρ` and the identification of the mapped data over `F`
  have hcompC : ρ.comp (PowerSeries.C : O →+* O⟦X⟧) = φF :=
    RingHom.ext fun x ↦ congrArg φF (PowerSeries.constantCoeff_C x)
  have hidf : (f.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ = f.map φF := by
    rw [Polynomial.map_map, hcompC]
  have hidu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ = uτ.map φF := by
    rw [Polynomial.map_map, hcompC]
  have hidv₂ : (vτ.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ = vτ.map φF := by
    rw [Polynomial.map_map, hcompC]
  have hidu₃ : (phiU₃ a xQ).map ρ = (X - C (φF xQ)) * (X - C (φF a)) := by
    rw [phiU₃, Polynomial.map_map, hcompC]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C]
  have hidv₃ : (phiV₃ xQ yQ m₀).map ρ = pairV (φF xQ) (φF yQ) (φF m₀) := by
    rw [phiV₃, Polynomial.map_map, hcompC, pairV_map]
  have hidD : (diskConfig u₁ v₁ a xQ yQ m₀ uτ vτ).map ρ
      = ⟨(X - C (φF a)) * (X - C (φF xQ)), pairV (φF a) (φF b) (φF (ε m)), uτ.map φF,
        vτ.map φF, (X - C (φF xQ)) * (X - C (φF a)), pairV (φF xQ) (φF yQ) (φF m₀)⟩ := by
    simp only [PipelineData.map, diskConfig, hidu₁, hidv₁, hidu₂, hidv₂, hidu₃, hidv₃]
  -- transport the certificate pack to `F` and rewrite along the identifications
  have hcertsF := hcerts.map ρ hu₁ hu₂ hu₃
  rw [hidf, hidD, ← huτ.natDegree_map φF] at hcertsF
  -- the mapped pipeline identity, rewritten to the concrete `F`-data
  have hmap := map_cantorPipeline_generic ρ hu₁ hu₂ hu₃ hcerts
  rw [hidf, hidD] at hmap
  -- the class-cancellation over `F`
  have hneF := map_ne_of_isUnit_sub φF hsep
  have hmFF := map_slope φF hmF
  have hm₀F := map_slope φF hm₀
  have hbF : φF b ^ 2 = (f.map φF).eval (φF a) := onCurve_map _ hb
  have hyQF : φF yQ ^ 2 = (f.map φF).eval (φF xQ) := onCurve_map _ hyQ
  have hcancel := mk0_pair_mul_mk0_pair (f := f.map φF) hneF hmFF hm₀F hbF hyQF
  -- monic/dvd/degree facts over `F`
  have hu₁F : ((X - C (φF a)) * (X - C (φF xQ))).Monic :=
    (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂F : (uτ.map φF).Monic := huτ.map _
  have hu₃F : ((X - C (φF xQ)) * (X - C (φF a))).Monic :=
    (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hd₁F : (X - C (φF a)) * (X - C (φF xQ))
      ∣ pairV (φF a) (φF b) (φF (ε m)) ^ 2 - f.map φF := by
    have h := map_dvd_sq_sub ρ hd₁
    rwa [hidf, hidu₁, hidv₁] at h
  have hd₂F : uτ.map φF ∣ (vτ.map φF) ^ 2 - f.map φF := by
    have h := map_dvd_sq_sub ρ hd₂
    rwa [hidf, hidu₂, hidv₂] at h
  have hd₃F : (X - C (φF xQ)) * (X - C (φF a))
      ∣ pairV (φF xQ) (φF yQ) (φF m₀) ^ 2 - f.map φF := by
    have h := map_dvd_sq_sub ρ hd₃
    rwa [hidf, hidu₃, hidv₃] at h
  have hv₂F : (vτ.map φF).degree < (uτ.map φF).degree :=
    degree_map_le.trans_lt (hvτ.trans_eq (huτ.degree_map φF).symm)
  have hgF : 2 * (uτ.map φF).natDegree < (f.map φF).natDegree := by
    rw [huτ.natDegree_map, hf.natDegree_map]
    exact hgτ
  -- the pipeline over `F` returns the τ-datum
  rw [cantorPipeline_eq_middle hu₁F hd₁F hu₂F hd₂F hu₃F hd₃F hcertsF hcancel hv₂F hgF hgF]
    at hmap
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hmap
  dsimp only at h1 h2
  -- descend along the injective `φF`
  have hmapinj : Function.Injective (Polynomial.map φF) := Polynomial.map_injective φF hinj
  exact ⟨hmapinj (by
    rw [Polynomial.map_map, ← hρ]; exact h1),
    hmapinj (by rw [Polynomial.map_map, ← hρ]; exact h2)⟩

/-- **The center of the disk pipeline is the `τ`-datum** (`ζ(0) = 0`, blueprint
`def:phiD`): evaluating the pipeline at `z = 0` returns `(uτ, vτ)` exactly. At `z = 0`
the two pair data are `[P₀ + ι Q - 2∞]` and `[Q + ι P₀ - 2∞]`, whose classes cancel, so
over the fraction field the pipeline output and the `τ`-datum are reduced representatives
of the same class; the identification descends to `O` by injectivity. -/
theorem phiPipeline_map_constantCoeff (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hvτ : vτ.degree < uτ.degree) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree) :
    (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.map PowerSeries.constantCoeff = uτ
      ∧ (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2.map PowerSeries.constantCoeff = vτ := by
  refine cantorPipeline_map_constantCoeff_of_pair (m := m) hf
    ((monic_X_sub_C _).mul (monic_X_sub_C _)) (movingPair_dvd hsep hm hb hfa h2 hyQ) ?_ ?_
    hsep ?_ hm₀ hb hyQ huτ hvτ hdvdτ hgτ hcerts
  · simp only [phiU₁, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_X, map_C, RingHom.comp_apply, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, map_add, map_zero, add_zero]
  · rw [phiV₁, pairV_map]
    simp only [map_add, map_mul, RingHom.comp_apply, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, constantCoeff_diskSeriesGeneric, map_one, map_zero,
      add_zero, mul_one]
  · simpa only [map_mul, map_sub, map_add, map_neg, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, constantCoeff_diskSeriesGeneric, add_zero, mul_one]
      using congrArg PowerSeries.constantCoeff hm

/-- **`ζ(0) = 0`** (blueprint `def:phiD`): the disk chart coordinates vanish at `z = 0`. -/
theorem constantCoeff_phiZeta (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hvτ : vτ.degree < uτ.degree) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree) (j : Fin uτ.natDegree) :
    PowerSeries.constantCoeff (phiZeta f a b xQ yQ m m₀ uτ vτ d j) = 0 := by
  have h := (phiPipeline_map_constantCoeff hf hsep hm hm₀ hb hfa h2 hyQ huτ hvτ hdvdτ hgτ hcerts).1
  rw [phiZeta, map_chartCoords, PowerSeries.constantCoeff_comp_C, h, chartCoords,
    Polynomial.map_id, sub_self, coeff_zero]

end CenterZero

section PointwiseClass

open IsLocalRing nonZeroDivisors
open scoped PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]}
  {d : CantorCertData O⟦X⟧}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **A disk pipeline evaluated at `z₀` computes `[P_{z₀} - P₀] + [τ]`**: over the fraction
field the evaluated Mumford datum is the product of the moving point's class, the inverse of
the centre's, and the `τ`-datum's. The moving pair block enters abstractly through the images
`hidu₁`, `hidv₁` of its two parts at `z₀`, so the generic chart (moving point `(a + z₀, …)`,
centre `(a, b)`) and the Weierstrass chart (moving point `(W(z₀), z₀)`, centre `(ω, 0)`) are
the same computation. -/
theorem mk0_cantorPipeline_eval_of_pair {u₁ v₁ : (O⟦X⟧)[X]} {px py α β : O}
    (hu₁ : u₁.Monic) (hd₁ : u₁ ∣ v₁ ^ 2 - f.map PowerSeries.C) {z₀ : O}
    (hz₀ : z₀ ∈ maximalIdeal O)
    (hidu₁ : u₁.map ((algebraMap O (FractionRing O)).comp (PSeries.evalRingHom hz₀))
      = (X - C (algebraMap O (FractionRing O) px))
        * (X - C (algebraMap O (FractionRing O) xQ)))
    (hidv₁ : v₁.map ((algebraMap O (FractionRing O)).comp (PSeries.evalRingHom hz₀))
      = pairV (algebraMap O (FractionRing O) px) (algebraMap O (FractionRing O) py)
        (algebraMap O (FractionRing O) (PSeries.eval z₀ m)))
    (hpx : px - α ∈ maximalIdeal O) (hsep : IsUnit (xQ - α))
    (hpy : py ^ 2 = f.eval px) (hyQ : yQ ^ 2 = f.eval xQ) (hβ : β ^ 2 = f.eval α)
    (hmPQ : PSeries.eval z₀ m * (xQ - px) = -yQ - py) (hm₀ : m₀ * (α - xQ) = -β - yQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C)
      (diskConfig u₁ v₁ α xQ yQ m₀ uτ vτ) d uτ.natDegree)
    {P : (O⟦X⟧)[X] × (O⟦X⟧)[X]}
    (hP : P = cantorPipeline (f.map PowerSeries.C) (diskConfig u₁ v₁ α xQ yQ m₀ uτ vτ) d)
    (hDm : P.1.Monic) :
    ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
        ((P.1.map (PSeries.evalRingHom hz₀)).map (algebraMap O (FractionRing O)))
        ((P.2.map (PSeries.evalRingHom hz₀)).map (algebraMap O (FractionRing O))),
        mumfordIdeal_mem_nonZeroDivisors _ (((hDm.map _).map _).ne_zero) _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (X - C (algebraMap O (FractionRing O) px))
            (C (algebraMap O (FractionRing O) py)),
            mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (X - C (algebraMap O (FractionRing O) α))
            (C (-algebraMap O (FractionRing O) β)),
            mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (uτ.map (algebraMap O (FractionRing O)))
            (vτ.map (algebraMap O (FractionRing O))),
            mumfordIdeal_mem_nonZeroDivisors _ ((huτ.map _).ne_zero) _⟩ := by
  classical
  set K := FractionRing O
  set φK : O →+* K := algebraMap O K
  set ε : O⟦X⟧ →+* O := PSeries.evalRingHom hz₀
  set ρ : O⟦X⟧ →+* K := φK.comp ε with hρdef
  have hinjK : Function.Injective φK := IsFractionRing.injective O K
  have hεapp (x : O⟦X⟧) : ε x = PSeries.eval z₀ x :=
    congrFun (PSeries.coe_evalRingHom hz₀) x
  have hεC (x : O) : ε (PowerSeries.C x) = x := by rw [hεapp]; exact PSeries.eval_C x z₀
  have hρC (x : O) : ρ (PowerSeries.C x) = φK x := by rw [hρdef, RingHom.comp_apply, hεC]
  have hcompC : ρ.comp (PowerSeries.C : O →+* O⟦X⟧) = φK := RingHom.ext hρC
  -- basic data facts over `O⟦z⟧`
  have hu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).Monic := huτ.map _
  have hu₃ : (phiU₃ α xQ (O := O)).Monic :=
    ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hd₂ : uτ.map (PowerSeries.C : O →+* O⟦X⟧)
      ∣ (vτ.map PowerSeries.C) ^ 2 - f.map PowerSeries.C := map_dvd_sq_sub _ hdvdτ
  have hsepn : IsUnit (α - xQ) := by rw [← neg_sub]; exact hsep.neg
  have hd₃ : phiU₃ α xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - f.map (PowerSeries.C : O →+* O⟦X⟧) :=
    map_dvd_sq_sub _ (pair_dvd hsepn hm₀ hyQ (by rwa [neg_pow_two]))
  -- mapped-pipeline identity and transported certificates
  have hmap := map_cantorPipeline_generic ρ hu₁ hu₂ hu₃ hcerts
  have hcertsK := hcerts.map ρ hu₁ hu₂ hu₃
  -- identifications of the mapped data
  have hidf : (f.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ = f.map φK := by
    rw [Polynomial.map_map, hcompC]
  have hidu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ = uτ.map φK := by
    rw [Polynomial.map_map, hcompC]
  have hidv₂ : (vτ.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ = vτ.map φK := by
    rw [Polynomial.map_map, hcompC]
  have hidu₃ : (phiU₃ α xQ).map ρ = (X - C (φK xQ)) * (X - C (φK α)) := by
    rw [phiU₃, Polynomial.map_map, hcompC]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C]
  have hidv₃ : (phiV₃ xQ yQ m₀).map ρ = pairV (φK xQ) (φK yQ) (φK m₀) := by
    rw [phiV₃, Polynomial.map_map, hcompC, pairV_map]
  set DK : PipelineData K := ⟨(X - C (φK px)) * (X - C (φK xQ)),
    pairV (φK px) (φK py) (φK (PSeries.eval z₀ m)), uτ.map φK, vτ.map φK,
    (X - C (φK xQ)) * (X - C (φK α)), pairV (φK xQ) (φK yQ) (φK m₀)⟩ with hDKdef
  have hidD : (diskConfig u₁ v₁ α xQ yQ m₀ uτ vτ).map ρ = DK := by
    simp only [hDKdef, PipelineData.map, diskConfig, hidu₁, hidv₁, hidu₂, hidv₂, hidu₃, hidv₃]
  rw [hidf, hidD] at hmap hcertsK
  -- the point conditions over `K`
  have hPz : φK py ^ 2 = (f.map φK).eval (φK px) := onCurve_map _ hpy
  have hQK : φK yQ ^ 2 = (f.map φK).eval (φK xQ) := onCurve_map _ hyQ
  have hRK : φK β ^ 2 = (f.map φK).eval (φK α) := onCurve_map _ hβ
  have hsepz : IsUnit (xQ - px) :=
    isUnit_of_sub_mem hsep (by rw [sub_sub_sub_cancel_left, ← neg_sub px α]; exact neg_mem hpx)
  have hne1 : φK px ≠ φK xQ := fun h ↦ hsepz.ne_zero (by rw [← hinjK h, sub_self])
  have hne2 : φK xQ ≠ φK α := fun h ↦ hsep.ne_zero (by rw [hinjK h, sub_self])
  have hmPQK : φK (PSeries.eval z₀ m) * (φK xQ - φK px) = -φK yQ - φK py := by
    simpa only [map_mul, map_sub, map_neg] using congrArg φK hmPQ
  have hmQR : φK m₀ * (φK α - φK xQ) = -φK β - φK yQ := by
    simpa only [map_mul, map_sub, map_neg] using congrArg φK hm₀
  have hchain := mk0_pair_mul_mk0_pair_chain (f := f.map φK) hne1 hne2 hmPQK hmQR hPz hQK hRK
  -- monic/dvd facts for the concrete data over `K`
  have hu₁K : ((X - C (φK px)) * (X - C (φK xQ))).Monic :=
    (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂K : (uτ.map φK).Monic := huτ.map _
  have hu₃K : ((X - C (φK xQ)) * (X - C (φK α))).Monic :=
    (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hd₁K := map_dvd_sq_sub ρ hd₁
  rw [hidf, hidu₁, hidv₁] at hd₁K
  have hd₂K := map_dvd_sq_sub ρ hd₂
  rw [hidf, hidu₂, hidv₂] at hd₂K
  have hd₃K := map_dvd_sq_sub ρ hd₃
  rw [hidf, hidu₃, hidv₃] at hd₃K
  -- the class formula for the mapped pipeline
  have hfinK := cantorPipeline_monic_dvd_degree_lt hu₁K hd₁K hu₂K hd₂K hu₃K hd₃K hcertsK
  have hcls := mk0_cantorPipeline_generic hu₁K hd₁K hu₂K hd₂K hu₃K hd₃K hcertsK hfinK.1
  -- identify the goal datum with the mapped pipeline
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hmap
  dsimp only at h1 h2
  have hid : mumfordIdeal (f.map φK) ((P.1.map ε).map φK) ((P.2.map ε).map φK)
      = mumfordIdeal (f.map φK) (cantorPipeline (f.map φK) DK (d.map ρ)).1
        (cantorPipeline (f.map φK) DK (d.map ρ)).2 := by
    rw [hP, Polynomial.map_map, Polynomial.map_map, ← hρdef, h1, h2]
  calc ClassGroup.mk0 ⟨mumfordIdeal (f.map φK) ((P.1.map ε).map φK) ((P.2.map ε).map φK),
        mumfordIdeal_mem_nonZeroDivisors _ (((hDm.map _).map _).ne_zero) _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map φK) _ _,
          mumfordIdeal_mem_nonZeroDivisors _ hfinK.1.ne_zero _⟩ :=
        congrArg ClassGroup.mk0 (Subtype.ext hid)
    _ = _ := by rw [hcls, mul_right_comm, hchain]

/-- **The disk pipeline computes `[P_z] - [P₀] + τ` pointwise** (the geometric content of
blueprint `thm:omega-prime-global`(b)): evaluating the `def:phiD` pipeline at a point
`z₀` of the maximal ideal produces a reduced Mumford datum representing the class
`(P_{z₀}) + (ι P₀) - 2∞ + [τ]` over the fraction field, where
`P_{z₀} = (a + z₀, (b·η)(z₀))` is the disk point and `P₀ = (a, b)` the center. -/
theorem mk0_phiPipeline_eval (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hDm : (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.Monic)
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
        (((phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.map (PSeries.evalRingHom hz₀)).map
          (algebraMap O (FractionRing O)))
        (((phiPipeline f a b xQ yQ m m₀ uτ vτ d).2.map (PSeries.evalRingHom hz₀)).map
          (algebraMap O (FractionRing O))),
        mumfordIdeal_mem_nonZeroDivisors _ (((hDm.map _).map _).ne_zero) _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (X - C (algebraMap O (FractionRing O) (a + z₀)))
            (C (algebraMap O (FractionRing O)
              (PSeries.eval z₀ (PowerSeries.C b * diskSeriesGeneric f a)))),
            mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (X - C (algebraMap O (FractionRing O) a))
            (C (-algebraMap O (FractionRing O) b)),
            mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (uτ.map (algebraMap O (FractionRing O)))
            (vτ.map (algebraMap O (FractionRing O))),
            mumfordIdeal_mem_nonZeroDivisors _ ((huτ.map _).ne_zero) _⟩ := by
  refine mk0_cantorPipeline_eval_of_pair (m := m) ((monic_X_sub_C _).mul (monic_X_sub_C _))
    (movingPair_dvd hsep hm hb hfa h2 hyQ) hz₀ ?_ ?_ (by simpa using hz₀) hsep ?_ hyQ hb ?_
    hm₀ huτ hdvdτ hcerts rfl hDm
  · simp [PSeries.evalRingHom_apply, PSeries.eval_C, PSeries.eval_X]
  · rw [pairV_map]
    simp only [RingHom.comp_apply, PSeries.evalRingHom_apply, PSeries.eval_add hz₀,
      PSeries.eval_C, PSeries.eval_X]
  · have h := congrArg (PSeries.evalRingHom hz₀) (diskY_sq hb hfa h2)
    rw [map_pow, eval_map, Polynomial.hom_eval₂, PSeries.evalRingHom_comp_C, eval₂_id] at h
    simpa only [PSeries.evalRingHom_apply, PSeries.eval_add hz₀, PSeries.eval_C,
      PSeries.eval_X] using h
  · have h := congrArg (PSeries.evalRingHom hz₀) hm
    simp only [map_mul, map_sub, PSeries.evalRingHom_apply, PSeries.eval_add hz₀,
      PSeries.eval_mul hz₀, PSeries.eval_C, PSeries.eval_X] at h ⊢
    linear_combination h

end PointwiseClass

end ChabautyColeman

end
