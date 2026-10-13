/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthBandReduction

/-!
# HomSpineDepthBandInput

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# THE GAGLIARDO BAND INPUT, DISCHARGED — and the unconditional sup clause

## What this file is for

`HomSpineDepthGagliardoBand` reduced the sup-form multiscale clause to ONE named
input, `GridDepthGagliardoBandInput d p Cd`.  This file discharges it at the
explicit numeral

```text
  Cd = gridDepthGagliardoConst d p = 2^{p'} · 2^{d+3} · (d+1) · 3^d.
```

Three pieces.

* `lintegral_normalized_enorm_gridDualTestCoeff_le` — the FLAT half in the exact
  form the reduction needs: `⨍_Q ‖g_j‖^{p'} ≤ (cell side)^{s·p'}·(depth energy)`,
  the same conjugacy bookkeeping `(p-1)p' = p`, `p·p' = p+p'` as
  `HomSpineCzGridDepthTest.weight_mul_flat_rpow_le_depthEnergy` but keeping the
  `3^{-s·j·p'}` that display discards — it is exactly the cell-side weight the
  band reduction produces.
* `gridDepthGagliardoBandInput_holds` — the input, carrier and all: the
  `W^{s,p'} ∩ L²` bundle for the depth slice (its Gagliardo finiteness IS the
  reduction, its `L²` half is the finite indicator sum), and the band bound.
Together they leave the SUP-FORM MULTISCALE CLAUSE with NO named input:
`HomSpineDepthGagliardoBand`'s producer runs at
`Cd = gridDepthGagliardoConst d p`, so at
`CA = (1 + Cd·(near + 2·x₀⁻¹))^{1/p'}` on the two-sided order pin
`x₀ ≤ s·p' ≤ 1/2`.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The `L^q` membership of a depth slice -/

/-- The depth slice, as a finite sum of indicators in the Hilbert realization. -/
theorem ofVec_gridDualDepthTest_eq (Q : TriadicCube d) (j : ℕ) (v : TriadicCube d → Vec d)
    (x : Vec d) :
    HilbertVec.ofVec (gridDualDepthTest Q j v x) =
      ∑ R ∈ descendantsAtDepth Q j,
        (cubeSet R).indicator (fun _ => HilbertVec.ofVec (v R)) x := by
  classical
  rw [gridDualDepthTest, ofVec_finset_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  by_cases hx : x ∈ cubeSet R
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    rfl

/-- A depth slice belongs to every `L^q(Q)`: it is a finite sum of constants
times indicators of measurable sets, on a finite measure. -/
theorem memLp_ofVec_gridDualDepthTest (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) (q : ℝ≥0∞) :
    MemLp (fun x => HilbertVec.ofVec (gridDualDepthTest Q j v x)) q
      (normalizedCubeMeasure Q) := by
  classical
  have hfun : (fun x => HilbertVec.ofVec (gridDualDepthTest Q j v x)) =
      fun x => ∑ R ∈ descendantsAtDepth Q j,
        (cubeSet R).indicator (fun _ => HilbertVec.ofVec (v R)) x :=
    funext fun x => ofVec_gridDualDepthTest_eq Q j v x
  rw [hfun]
  refine memLp_finsetSum _ fun R _ => ?_
  exact MemLp.indicator (measurableSet_cubeSet R) (memLp_const _)

/-! ## 2. The flat half, with the cell-side weight kept -/

/-- **THE FLAT HALF.**  The normalized `L^{p'}` mass of the depth slice is below
`(cell side)^{s·p'}` times the depth energy.  (`HomSpineCzGridDepthTest`'s
`weight_mul_flat_rpow_le_depthEnergy` throws this weight away against the scale
factor of the full norm; the band reduction needs it, because the band factor is
displayed relative to the CELL scale, not the cube scale.) -/
theorem lintegral_normalized_enorm_gridDualTestCoeff_le (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    (∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j
          (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j) x)‖ₑ ^
          p.conjugate.exponent.toReal ∂(normalizedCubeMeasure Q)) ≤
      ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (s.1 * p.conjugate.exponent.toReal)) *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
  classical
  set t : ℝ := p.exponent.toReal with hts
  set r : ℝ := p.conjugate.exponent.toReal with hrs
  have ht : 0 < t := finiteLpExponent_toReal_pos p
  have hr : 0 < r := finiteLpExponent_toReal_pos p.conjugate
  have hconj : t.HolderConjugate r := holderConjugate_toReal p
  set D : Finset (TriadicCube d) := descendantsAtDepth Q j with hD
  have hcardpos : (0 : ℝ) < ((D.card : ℝ)) := descendantsAtDepth_card_pos Q j
  set M : ℝ := (((Q.scale - (j : ℤ) : ℤ)) : ℝ) with hM
  set A : ℝ := descendantsAverage Q j (fun R => ‖cubeAverageVec R F.toField‖ ^ t) with hA
  have hA0 : 0 ≤ A :=
    descendantsAverage_nonneg Q j _ fun R _ => Real.rpow_nonneg (norm_nonneg _) _
  /- the cell side, as a real power of thr -/
  have hcell : cubeScaleFactor Q / (3 : ℝ) ^ j = (3 : ℝ) ^ M := by
    rw [cubeScaleFactor, ← Real.rpow_intCast (3 : ℝ) Q.scale, ← Real.rpow_natCast (3 : ℝ) j,
      ← Real.rpow_sub (by norm_num)]
    congr 1
    rw [hM]
    push_cast
    ring
  have hcellpow : (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (s.1 * r) = (3 : ℝ) ^ (M * (s.1 * r)) := by
    rw [hcell, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  /- the mass, cell by cell (verbatim from the flat displa -/
  have hterm : ∀ R ∈ D,
      ((D.card : ℝ≥0∞))⁻¹ *
          ‖euclideanNorm (gridDualTestCoeff Q s.1 t F.toField j R)‖ₑ ^ r ≤
        ((D.card : ℝ≥0∞))⁻¹ *
          ENNReal.ofReal ((3 : ℝ) ^ (s.1 * t * M * r) *
            ‖cubeAverageVec R F.toField‖ ^ t) := by
    intro R _
    refine mul_le_mul' le_rfl ?_
    have h1 : ‖euclideanNorm (gridDualTestCoeff Q s.1 t F.toField j R)‖ₑ ^ r ≤
        (ENNReal.ofReal ((3 : ℝ) ^ (s.1 * t * M) *
          ‖cubeAverageVec R F.toField‖ ^ (t - 1))) ^ r :=
      ENNReal.rpow_le_rpow (enorm_euclideanNorm_gridDualTestCoeff_le Q s.1 t F.toField j R) hr.le
    refine h1.trans (le_of_eq ?_)
    have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (s.1 * t * M) * ‖cubeAverageVec R F.toField‖ ^ (t - 1) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (norm_nonneg _) _)
    have hreal : ((3 : ℝ) ^ (s.1 * t * M) * ‖cubeAverageVec R F.toField‖ ^ (t - 1)) ^ r =
        (3 : ℝ) ^ (s.1 * t * M * r) * ‖cubeAverageVec R F.toField‖ ^ t := by
      rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_mul (norm_nonneg _), hconj.sub_one_mul_conj]
    rw [ENNReal.ofReal_rpow_of_nonneg hnn hr.le, hreal]
  have hsum : (∑ R ∈ D, ((D.card : ℝ≥0∞))⁻¹ *
      ENNReal.ofReal ((3 : ℝ) ^ (s.1 * t * M * r) * ‖cubeAverageVec R F.toField‖ ^ t)) =
      ENNReal.ofReal ((3 : ℝ) ^ (s.1 * t * M * r) * A) := by
    have hinv : ((D.card : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((D.card : ℝ)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos hcardpos, ENNReal.ofReal_natCast]
    have hstep : ∀ R ∈ D, ((D.card : ℝ≥0∞))⁻¹ *
        ENNReal.ofReal ((3 : ℝ) ^ (s.1 * t * M * r) * ‖cubeAverageVec R F.toField‖ ^ t) =
        ENNReal.ofReal ((D.card : ℝ)⁻¹ *
          ((3 : ℝ) ^ (s.1 * t * M * r) * ‖cubeAverageVec R F.toField‖ ^ t)) := by
      intro R _
      rw [hinv, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hcardpos))]
    rw [Finset.sum_congr rfl hstep,
      ← ENNReal.ofReal_sum_of_nonneg fun R _ =>
        mul_nonneg (le_of_lt (inv_pos.mpr hcardpos))
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg (norm_nonneg _) _))]
    congr 1
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    show ((D.card : ℝ))⁻¹ * ((3 : ℝ) ^ (s.1 * t * M * r) *
        ∑ R ∈ D, ‖cubeAverageVec R F.toField‖ ^ t) =
      (3 : ℝ) ^ (s.1 * t * M * r) *
        (((D.card : ℝ))⁻¹ * ∑ R ∈ D, ‖cubeAverageVec R F.toField‖ ^ t)
    ring
  /- the exponent bookkeeping: `s·t·M·r = M·(s·r) + s·t·M` -/
  have hexp : s.1 * t * M * r = M * (s.1 * r) + s.1 * t * M := by
    have hmul : t * r = t + r := hconj.mul_eq_add
    calc s.1 * t * M * r = s.1 * M * (t * r) := by ring
      _ = s.1 * M * (t + r) := by rw [hmul]
      _ = M * (s.1 * r) + s.1 * t * M := by ring
  rw [lintegral_enorm_euclideanNorm_gridDualDepthTest_rpow Q j _ hr,
    depthEnergy_eq_ofReal Q s p F j, hcellpow]
  refine le_trans ((Finset.sum_le_sum hterm).trans (le_of_eq hsum)) (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  congr 1
  rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring

/-! ## 3. The band input, discharged -/

/-- **THE DIMENSIONAL GAGLIARDO BAND CONSTANT**, pinned:
`2^{p'}·2^{d+3}·(d+1)·3^d`.  The `2^{p'}` is the crude increment splitting
(`ennreal_add_rpow_le`) and is bounded only on a bounded range of `p'` — on the
repository's band `p ≥ 2` it is at most `4`. -/
def gridDepthGagliardoConst (d : ℕ) (p : FiniteLpExponent) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ p.conjugate.exponent.toReal *
    (2 ^ (d + 3) * ((d : ℝ) + 1) * 3 ^ d))

theorem gridDepthGagliardoConst_ne_top (d : ℕ) (p : FiniteLpExponent) :
    gridDepthGagliardoConst d p ≠ ⊤ := by
  rw [gridDepthGagliardoConst]
  exact ENNReal.ofReal_ne_top

/-- **THE BAND INPUT, DISCHARGED.**  `HomSpineDepthGagliardoBand`'s one named
input holds, at the explicit numeral `gridDepthGagliardoConst d p`. -/
theorem gridDepthGagliardoBandInput_holds (d : ℕ) (p : FiniteLpExponent) :
    GridDepthGagliardoBandInput d p (gridDepthGagliardoConst d p) := by
  classical
  intro Q s hband F j
  set q : FiniteLpExponent := p.conjugate with hq
  set r : ℝ := q.exponent.toReal with hrs
  set v : TriadicCube d → Vec d := gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j with hv
  set g : Vec d → Vec d := gridDualDepthTest Q j v with hg
  have hr : 0 < r := finiteLpExponent_toReal_pos q
  have hLpos : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hcellpos : (0 : ℝ) < cubeScaleFactor Q / (3 : ℝ) ^ j := by positivity
  /- the reduction, composed with the flat ha -/
  have hflat := lintegral_normalized_enorm_gridDualTestCoeff_le Q s p F j
  have hred := cubeEuclideanWspESeminorm_gridDualDepthTest_rpow_le Q s q j v hband
  have hchain : cubeEuclideanWspESeminorm Q s q g ^ r ≤
      gridDepthGagliardoConst d p *
          ENNReal.ofReal (gridDepthBandFactor (s.1 * r) j) *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
    refine le_trans hred ?_
    refine le_trans (mul_le_mul' le_rfl hflat) (le_of_eq ?_)
    /- the cell-side weights cancel and the numerals colle -/
    have hcancel : ENNReal.ofReal (2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d *
          (cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * r)) * gridDepthBandFactor (s.1 * r) j) *
        ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (s.1 * r)) =
        ENNReal.ofReal (2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d) *
          ENNReal.ofReal (gridDepthBandFactor (s.1 * r) j) := by
      have hprod : (cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * r)) *
          (cubeScaleFactor Q / 3 ^ j) ^ (s.1 * r) = 1 := by
        rw [← Real.rpow_add hcellpos]
        simp
      have hd0 : (0 : ℝ) ≤ (d : ℝ) + 1 := by
        have hdn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        linarith only [hdn]
      have hnn1 : (0 : ℝ) ≤ 2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d *
          (cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * r)) * gridDepthBandFactor (s.1 * r) j :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hd0) (by positivity))
          (Real.rpow_nonneg hcellpos.le _)) (gridDepthBandFactor_nonneg _ _)
      rw [← ENNReal.ofReal_mul hnn1, ← ENNReal.ofReal_mul (mul_nonneg
        (mul_nonneg (by positivity) hd0) (by positivity))]
      congr 1
      calc 2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d *
            (cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * r)) * gridDepthBandFactor (s.1 * r) j *
            (cubeScaleFactor Q / 3 ^ j) ^ (s.1 * r)
          = 2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d * gridDepthBandFactor (s.1 * r) j *
              ((cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * r)) *
                (cubeScaleFactor Q / 3 ^ j) ^ (s.1 * r)) := by ring
        _ = 2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d * gridDepthBandFactor (s.1 * r) j := by
            rw [hprod, mul_one]
        _ = 2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d * gridDepthBandFactor (s.1 * r) j := rfl
    have htwo : (2 : ℝ≥0∞) ^ r = ENNReal.ofReal ((2 : ℝ) ^ r) := by
      rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have hconst : ENNReal.ofReal (2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d) *
        ((2 : ℝ≥0∞) ^ r * 2) = gridDepthGagliardoConst d p := by
      rw [gridDepthGagliardoConst, ← hrs, htwo, ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_add, pow_add]
      ring
    calc ENNReal.ofReal (2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d *
            (cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * r)) * gridDepthBandFactor (s.1 * r) j) *
          ((2 : ℝ≥0∞) ^ r * 2) *
          (ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (s.1 * r)) *
            cubeEuclideanNegativeBesovDepthEnergy Q s p F j)
        = (ENNReal.ofReal (2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d *
              (cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * r)) * gridDepthBandFactor (s.1 * r) j) *
            ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (s.1 * r))) *
            ((2 : ℝ≥0∞) ^ r * 2) * cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
          ring
      _ = ENNReal.ofReal (2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d) *
            ((2 : ℝ≥0∞) ^ r * 2) * ENNReal.ofReal (gridDepthBandFactor (s.1 * r) j) *
            cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
          rw [hcancel]
          ring
      _ = gridDepthGagliardoConst d p * ENNReal.ofReal (gridDepthBandFactor (s.1 * r) j) *
            cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by rw [hconst]
  /- the carri -/
  have hfinite : cubeEuclideanWspESeminorm Q s q g < ⊤ := by
    have hEtop : cubeEuclideanNegativeBesovDepthEnergy Q s p F j ≠ ⊤ := by
      rw [depthEnergy_eq_ofReal]
      exact ENNReal.ofReal_ne_top
    have htop : cubeEuclideanWspESeminorm Q s q g ^ r < ⊤ := by
      refine lt_of_le_of_lt hchain ?_
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top) ?_
      · exact lt_top_iff_ne_top.mpr (gridDepthGagliardoConst_ne_top d p)
      · exact lt_top_iff_ne_top.mpr hEtop
    exact (ENNReal.rpow_lt_top_iff_of_pos hr).mp htop
  refine ⟨⟨⟨⟨g, memLp_ofVec_gridDualDepthTest Q j v q.exponent⟩, hfinite⟩,
    memLp_ofVec_gridDualDepthTest Q j v 2⟩, rfl, ?_⟩
  exact hchain

end

end Algsuperdiff.Section4.Provider.Homogenization
