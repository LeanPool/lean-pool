/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGCarrierRHS
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGDischargeAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineRecutSupport

/-!
# HomSpineCzGridGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The grid gauge against `CoarseGraining`'s negative Besov seminorm

## What this file does

Clause 1 of the transcribed source hypothesis reduces to the Calderón--Zygmund
flux comparison lemma read at the multiscale grid gauge, and that reduction
comes down to a SINGLE inequality of pure fractional-Sobolev type, with no
PDE content and no carrier of this repository in it:

```text
  [F]_{B^{-s}_{p,p}(Q)}  ≤  C(p,d) · ‖F‖_{W_hat^{-s,p}(Q)}          (★)
```

— the CONVERSE of `CoarseGraining`'s proved
`cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm`
(`EuclideanWspSmoothDualBesovBound`), on the range `s·p' < 1` where `p' =
p/(p-1)` is the conjugate exponent.  `(★)` is not proved in this repository, in
`CoarseGraining`, or in Mathlib.

What this file supplies is the development-carrier identification (`§2` below)
that the reduction runs on.  The analytic halves are elsewhere: the CZ step at
the smooth-dual reading is `CoarseGraining`'s proved
`exists_centeredCubeFluxComparison_cz`, the coarse-graining half is its
unconditional `exists_localCoarseGrainingLp`, and the smooth-dual composition is
assembled in `HomCGDischargeAssembly`.

## The carrier identification (`§2`)

The depth-truncated `(p,p)` grid gauge of `HomFinitePGauge` is the printed
`3^{-ms}[F]_{B^{-s}_{p,p}(□_m)}` truncated at depth `N`, built on the
Euclidean magnitude of the cell averages.  `CoarseGraining`'s
`cubeEuclideanNegativeBesovESeminorm` is the same lattice sum without the
`3^{-ms}` normalization and with the *sup* magnitude of the cell averages.
Hence

```text
  negBesovLpPartialNorm Q s p N F  ≤  √d · 3^{-s·Q.scale} · [F]_{B^{-s}_{p,p}(Q)}
```

by a depth reindexing (`descendantsAtScale_eq_descendantsAtDepth`) and the
Euclidean/sup comparison `√(Σ xᵢ²) ≤ √d · sup|xᵢ|`.  No constant beyond `√d` is
spent; the depth-seminorm form of the comparison is
`ofReal_negBesovLpDepthSeminorm_rpow_le`.

## The smoothness question, CLOSED

The grid gauge's own dual tests are multi-depth grid-piecewise constants, which
are not `C^∞`; the natural worry is that `CoarseGraining`'s smooth-dual carrier
does not see them.  It does.  `CoarseGraining` proves, unconditionally,

```text
  ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le:
    |⟨F, G⟩|  ≤  ‖F‖_{W_hat^{-s,p}(Q)} · ‖G‖_{W^{s,p'}(Q)}
```

for EVERY `G ∈ W^{s,p'}(Q) ∩ L²(Q)` (`EuclideanWspSmoothDualFieldPairing`; the
mechanism is the completed-graph extension of
`EuclideanWspCompletedDualExtension`, built on the smooth density theorem
`exists_cubeEuclideanWspSmoothTest_fullENorm_and_l2_sub_lt`).  So `(★)` carries
no smoothness obligation whatsoever, and the existence of normalized
`W^{s,p'} ∩ L²` tests that see the truncated grid mass is the exact and only
remaining analytic content of the multiscale clause.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The Euclidean magnitude against the carrier's sup norm -/

/-- **`√(Σ xᵢ²) ≤ √d · sup|xᵢ|`.**  `Vec d` carries the product (sup) norm; the
gauge of this repository is built on the Euclidean magnitude.  This is the only constant
the identification of the two gauges costs. -/
theorem sqrt_vecNormSq_le_sqrt_dim_mul_norm (x : Vec d) :
    Real.sqrt (vecNormSq x) ≤ Real.sqrt d * ‖x‖ := by
  have hb : ∀ i : Fin d, x i * x i ≤ ‖x‖ * ‖x‖ := by
    intro i
    have h1 : |x i| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    have h2 := mul_self_le_mul_self (abs_nonneg (x i)) h1
    rwa [abs_mul_abs_self] at h2
  have hsum : vecNormSq x ≤ (d : ℝ) * (‖x‖ * ‖x‖) := by
    have hrw : vecNormSq x = ∑ i : Fin d, x i * x i := rfl
    rw [hrw]
    calc ∑ i : Fin d, x i * x i ≤ ∑ _i : Fin d, ‖x‖ * ‖x‖ :=
          Finset.sum_le_sum fun i _ => hb i
      _ = (d : ℝ) * (‖x‖ * ‖x‖) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (vecNormSq x) ≤ Real.sqrt ((d : ℝ) * (‖x‖ * ‖x‖)) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * ‖x‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self (norm_nonneg x)]

/-! ## 2. This repository's gauge against `CoarseGraining`'s grid seminorm -/

/-- The scale factor relating the two gauges: `√d · 3^{-s·m}`. -/
def gridScaleGauge (d : ℕ) (s : ℝ) (m : ℤ) : ℝ :=
  Real.sqrt d * (3 : ℝ) ^ (-s * (m : ℝ))

theorem gridScaleGauge_nonneg (d : ℕ) (s : ℝ) (m : ℤ) : 0 ≤ gridScaleGauge d s m :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)

/-- `CoarseGraining`'s `Real.rpow`-spelling of the base-`3` power, in the
 notation used here. -/
theorem real_rpow_three_eq (x : ℝ) : Real.rpow 3 x = (3 : ℝ) ^ x := rfl

/-- The depth-`j` term of this development gauge against the depth-`j` term of `CoarseGraining`'s
running-scale negative Besov seminorm. -/
theorem ofReal_negBesovLpDepthSeminorm_rpow_le (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    ENNReal.ofReal
        (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ^ p.exponent.toReal) ≤
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
  classical
  have ht : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  set D : Finset (TriadicCube d) := descendantsAtDepth Q j with hD
  have hDcard : (0 : ℝ) < (D.card : ℝ) := descendantsAtDepth_card_pos Q j
  set M : ℝ := descendantsAverage Q j
      (fun R => Real.sqrt (vecNormSq (cubeAverageVec R F.toField)) ^ p.exponent.toReal) with hM
  have hMnn : 0 ≤ M :=
    descendantsAverage_nonneg Q j _ fun R _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
  set S : ℝ≥0∞ := ∑ R ∈ D,
    (ENNReal.ofReal ‖cubeAverageVec R F.toField‖) ^ p.exponent.toReal with hS
  /- the depth seminorm, in closed fo -/
  have hLHS : negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ^ p.exponent.toReal
      = (3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ)) * M := by
    rw [negBesovLpDepthSeminorm_def, negBesovLpDepthMean_def,
      Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hMnn _),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_mul hMnn,
      one_div, inv_mul_cancel₀ (ne_of_gt ht), Real.rpow_one]
    congr 2
    ring
  /- the Euclidean/sup comparison, averag -/
  have hMbound : ENNReal.ofReal M ≤
      ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal) * ((D.card : ℝ≥0∞)⁻¹ * S) := by
    have hMeq : M = ((D.card : ℝ)⁻¹) *
        ∑ R ∈ D, Real.sqrt (vecNormSq (cubeAverageVec R F.toField)) ^ p.exponent.toReal := rfl
    have hcard : ENNReal.ofReal ((D.card : ℝ)⁻¹) = ((D.card : ℝ≥0∞))⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hDcard, ENNReal.ofReal_natCast]
    rw [hMeq, ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hDcard)),
      ENNReal.ofReal_sum_of_nonneg
        (fun R _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p.exponent.toReal),
      hcard, ← mul_assoc,
      mul_comm (ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal)) ((D.card : ℝ≥0∞))⁻¹,
      mul_assoc]
    refine mul_le_mul' le_rfl ?_
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun R _ => ?_
    have hpt : Real.sqrt (vecNormSq (cubeAverageVec R F.toField)) ^ p.exponent.toReal ≤
        Real.sqrt d ^ p.exponent.toReal *
          ‖cubeAverageVec R F.toField‖ ^ p.exponent.toReal := by
      rw [← Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)]
      exact Real.rpow_le_rpow (Real.sqrt_nonneg _)
        (sqrt_vecNormSq_le_sqrt_dim_mul_norm _) ht.le
    calc ENNReal.ofReal
          (Real.sqrt (vecNormSq (cubeAverageVec R F.toField)) ^ p.exponent.toReal)
        ≤ ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal *
            ‖cubeAverageVec R F.toField‖ ^ p.exponent.toReal) := ENNReal.ofReal_le_ofReal hpt
      _ = ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal) *
            (ENNReal.ofReal ‖cubeAverageVec R F.toField‖) ^ p.exponent.toReal := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Real.sqrt_nonneg _) _),
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ht.le]
  /- `CoarseGraining`'s depth term, flattened and reindex -/
  have hscale : descendantsAtScale Q (Q.scale - (j : ℤ)) = D := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q (by omega : Q.scale - (j : ℤ) ≤ Q.scale)]
    congr 1
    omega
  have hexp : Real.rpow 3 (s.1 * p.exponent.toReal * (((Q.scale - (j : ℤ) : ℤ) : ℝ))) =
      (3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ))) := by
    show (3 : ℝ) ^ (s.1 * p.exponent.toReal * (((Q.scale - (j : ℤ) : ℤ) : ℝ))) = _
    congr 1
    push_cast
    ring
  have hEnergy : cubeEuclideanNegativeBesovDepthEnergy Q s p F j =
      ENNReal.ofReal ((3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ)))) *
        ((D.card : ℝ≥0∞))⁻¹ * S := by
    rw [cubeEuclideanNegativeBesovDepthEnergy,
      Finset.sum_attach (descendantsAtScale Q (Q.scale - (j : ℤ)))
        (fun R => (ENNReal.ofReal ‖cubeAverageVec R F.toField‖) ^ p.exponent.toReal),
      hscale, ← hS, hexp]
  /- the coefficient identi -/
  have hcoeff : ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ))) *
      ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal) =
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
        ENNReal.ofReal ((3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ)))) := by
    have hR : gridScaleGauge d s.1 Q.scale ^ p.exponent.toReal *
        (3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ))) =
        Real.sqrt d ^ p.exponent.toReal *
          (3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ)) := by
      have hsum : -s.1 * (Q.scale : ℝ) * p.exponent.toReal +
          s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ)) =
          -s.1 * p.exponent.toReal * (j : ℝ) := by ring
      rw [gridScaleGauge,
        Real.mul_rpow (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hsum]
    rw [ENNReal.ofReal_rpow_of_nonneg (gridScaleGauge_nonneg d s.1 Q.scale) ht.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← ENNReal.ofReal_mul
        (Real.rpow_nonneg (gridScaleGauge_nonneg d s.1 Q.scale) p.exponent.toReal),
      hR, mul_comm (Real.sqrt d ^ p.exponent.toReal)]
  /- assemb -/
  rw [hLHS, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), hEnergy]
  calc ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ))) * ENNReal.ofReal M
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ))) *
          (ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal) * ((D.card : ℝ≥0∞)⁻¹ * S)) :=
        mul_le_mul' le_rfl hMbound
    _ = (ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * p.exponent.toReal * (j : ℝ))) *
          ENNReal.ofReal (Real.sqrt d ^ p.exponent.toReal)) * ((D.card : ℝ≥0∞)⁻¹ * S) := by
        ring
    _ = (ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
          ENNReal.ofReal ((3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ))))) *
          ((D.card : ℝ≥0∞)⁻¹ * S) := by rw [hcoeff]
    _ = ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
          (ENNReal.ofReal ((3 : ℝ) ^ (s.1 * p.exponent.toReal * ((Q.scale : ℝ) - (j : ℝ)))) *
            (D.card : ℝ≥0∞)⁻¹ * S) := by ring

end

end Algsuperdiff.Section4.Provider.Homogenization
