/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineCzGridDualTest

/-!
# HomSpineCzGridDepthTest

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The SINGLE-DEPTH dual test: the exact pairing and the FREE flat part

## What this file is for

`HomSpineCzGridDualTest` builds the MULTI-depth aggregate `G₀ = Σ_{j≤N} g_j`
and proves its pairing exact.  The multi-depth flat part then costs a
Hölder-in-depth factor `(1-3^{-s·p})^{-1/p}`, which the necessity record of
`HomSpineCzGridGaugeRefuted` shows SHARP.  This file does the SINGLE depth,
where that factor is not merely avoidable but absent by an exact computation:

```text
  ⟨F, g_j⟩              =  cubeEuclideanNegativeBesovDepthEnergy Q s p F j   (EXACT)
  3^{-s·m}‖g_j‖_{L^{p'}}  =  3^{-s·j} · (depth energy)^{1/p'}                  (EXACT)
```

so the flat half of the single-depth full norm is bounded by `(depth energy)^{1/p'}`
at CONSTANT ONE, with room `3^{-s·j}` to spare — no geometric factor, no band, no
`s₀`.  Both displays are proved below (`§1`, `§3`).

## The residue, measured exactly — and a WARNING

What is NOT free at a single depth is the Gagliardo half.  `§4` records the exact
band arithmetic.  Writing `ℓ = 3^{m-j}` for the depth-`j` cell side and banding the
double integral at `|x-y| ~ 3^{m-k}`:

* the NEAR bands `k ≥ j` (distances below the cell side) are geometric at ratio
  `3^{-(1-s·p')} ≤ 3^{-1/2}` on the band `s·p' ≤ 1/2`, and sum to the uniform
  `nearBandGeometricConstant` — this half IS `γ`-uniform, as this file expected;
* the FAR bands `k < j` (distances above the cell side, up to `diam Q`) are NOT.
  A depth-`j` piecewise constant straddles at EVERY coarser scale, so the far
  bands contribute the truncated geometric sum `Σ_{i<j} 3^{-i·s·p'}`, which is
  `≥ j/3` as soon as `j·s·p' ≤ 1`, and `≈ min(j·log 3, (s·p')^{-1})` in general.

So the single-depth Gagliardo bound carries a factor
`(1 + min(j·log 3 + c_d, (s·p')^{-1}))^{1/p'}`, NOT `C(d,p)`.  The factor is real,
not an artefact of the estimate: the alternating field (`(F)_R = ±e_1` on the
depth-`j` cells) makes `|g_j(x) - g_j(y)|` of full size for a fixed fraction of the
far pairs.  At the Step-3 pin `s ≈ |log γ|⁻¹` this is `|log γ|^{1/p'}` — WORSE than
the banded lane's `|log γ|^{1/p}` (`p' ≈ 1`, `p = 4d`).

## What this file proves

* `ofReal_cubeAverage_vecDot_gridDualDepthTest_eq` — the single-depth pairing, EXACT;
* `weight_mul_flat_rpow_le_depthEnergy` — the flat half at constant one, `γ`-uniform;
* `sum_near_band_le` — the near-band arithmetic of the Gagliardo half, uniform
  in `s`, `j` and `d`;
* `fullENorm_gridDualDepthTest_le_of_gagliardo` — the full norm of the slice from
  ANY Gagliardo input `[g_j]^{p'} ≤ Cg^{p'}·(depth energy)`;
* `depthEnergy_rpow_le_smoothDual_of_gagliardo` — THE ENDPOINT: the depth-`j` gauge
  inequality at `CA = (1+Cg^{p'})^{1/p'}`, with NO normalization step (the common
  factor is cancelled, so the positive homogeneity of `cubeEuclideanWspFullENorm`
  — proved upstream but PRIVATE — is never needed).
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The pairing at ONE depth

The depth-`j` slice of `HomSpineCzGridDualTest`'s grid dual test pairs with `F`
against exactly the depth-`j` term of `CoarseGraining`'s running-scale negative
Besov seminorm.  No sum over depths is taken, so no Hölder in the depth index
is spent and no geometric factor appears. -/

/-- The real-valued single-depth pairing: the cube average of `⟨F, g_j⟩` is
`3^{s·p·(m-j)}` times the depth-`j` descendant average of `‖(F)_R‖^p`. -/
theorem cubeAverage_vecDot_gridDualDepthTest_coeff (Q : TriadicCube d) (s t : ℝ) (ht : 0 < t)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    cubeAverage Q (fun x => vecDot (F.toField x)
        (gridDualDepthTest Q j (gridDualTestCoeff Q s t F.toField j) x)) =
      (3 : ℝ) ^ (s * t * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
        descendantsAverage Q j (fun R => ‖cubeAverageVec R F.toField‖ ^ t) := by
  rw [cubeAverage_vecDot_gridDualDepthTest Q j (gridDualTestCoeff Q s t F.toField j) F]
  have hcell : ∀ R : TriadicCube d,
      vecDot (cubeAverageVec R F.toField) (gridDualTestCoeff Q s t F.toField j R) =
        (3 : ℝ) ^ (s * t * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
          ‖cubeAverageVec R F.toField‖ ^ t := by
    intro R
    rw [gridDualTestCoeff, vecDot_smul_right, vecDot_vecSupDual, mul_assoc,
      rpow_sub_one_mul_self _ t (norm_nonneg _) ht]
  rw [show (fun R => vecDot (cubeAverageVec R F.toField)
        (gridDualTestCoeff Q s t F.toField j R)) =
      (fun R => (3 : ℝ) ^ (s * t * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
        ‖cubeAverageVec R F.toField‖ ^ t) from funext hcell]
  exact descendantsAverage_mul_left Q j _ _

/-- The single-depth pairing is nonnegative: it is a geometric weight times a
descendant average of `p`-th powers. -/
theorem cubeAverage_vecDot_gridDualDepthTest_nonneg (Q : TriadicCube d) (s t : ℝ) (ht : 0 < t)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    0 ≤ cubeAverage Q (fun x => vecDot (F.toField x)
      (gridDualDepthTest Q j (gridDualTestCoeff Q s t F.toField j) x)) := by
  rw [cubeAverage_vecDot_gridDualDepthTest_coeff Q s t ht F j]
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
  exact descendantsAverage_nonneg Q j _ fun R _ => Real.rpow_nonneg (norm_nonneg _) _

/-- **THE SINGLE-DEPTH EXACT PAIRING.**

```text
  ⟨F, g_j⟩ = cubeEuclideanNegativeBesovDepthEnergy Q s p F j
```

on the nose — the depth-`j` gauge term, with no constant spent, no `√d`, and no
inequality.  This is the whole of `HomSpineCzGridDualTest`'s exact-duality
mechanism read at ONE depth: the depth-`j` cells partition `Q`, the slice is
constant on each, and `vecSupDual` realizes the sup-norm duality exactly. -/
theorem ofReal_cubeAverage_vecDot_gridDualDepthTest_eq (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    ENNReal.ofReal (cubeAverage Q (fun x => vecDot (F.toField x)
        (gridDualDepthTest Q j
          (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j) x))) =
      cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
  rw [cubeAverage_vecDot_gridDualDepthTest_coeff Q s.1 p.exponent.toReal
      (finiteLpExponent_toReal_pos p) F j, depthEnergy_eq_ofReal]

/-! ## 2. The flat part at ONE depth: the cell-measure bookkeeping

One depth, one geometric weight, no Hölder in the depth index.  The depth-`j`
cells carry normalized measure `|D_j|⁻¹` each, so the normalized `L^{p'}` norm of
the slice is the `ℓ^{p'}` average of the cell values, and the identity
`(p-1)·p' = p` turns it into the depth energy to the power `1/p'`. -/

/-- Each depth-`j` cell carries normalized measure `|D_j|⁻¹`. -/
theorem normalizedCubeMeasure_cubeSet_of_mem_descendantsAtDepth {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    normalizedCubeMeasure Q (cubeSet R) = (((descendantsAtDepth Q j).card : ℝ≥0∞))⁻¹ := by
  have hvolR : volume (cubeSet R) = ENNReal.ofReal (cubeVolume R) := by
    rw [← cubeMeasure_apply_univ, cubeMeasure_apply_univ_eq]
  have hsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hcard := cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR
  have hcardpos : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := descendantsAtDepth_card_pos Q j
  have hQpos : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
  have hratio : (cubeVolume Q)⁻¹ * cubeVolume R = (((descendantsAtDepth Q j).card : ℝ))⁻¹ := by
    rw [hcard]
    have hRpos : (0 : ℝ) < cubeVolume R := cubeVolume_pos R
    field_simp
  show (ENNReal.ofReal ((cubeVolume Q)⁻¹) • cubeMeasure Q) (cubeSet R) = _
  rw [Measure.smul_apply, smul_eq_mul, cubeMeasure,
    Measure.restrict_apply (measurableSet_cubeSet R),
    Set.inter_eq_self_of_subset_left hsub, hvolR,
    ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hQpos)), hratio,
    ENNReal.ofReal_inv_of_pos hcardpos, ENNReal.ofReal_natCast]

/-- The `r`-th power of the pointwise Euclidean size of a depth slice, as a sum of
indicators of the depth-`j` cells. -/
theorem enorm_euclideanNorm_gridDualDepthTest_rpow (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r =
      ∑ R ∈ descendantsAtDepth Q j,
        (cubeSet R).indicator (fun _ => ‖euclideanNorm (v R)‖ₑ ^ r) x := by
  classical
  by_cases hx : ∃ R ∈ descendantsAtDepth Q j, x ∈ cubeSet R
  · obtain ⟨R, hR, hxR⟩ := hx
    have hdisj : (↑(descendantsAtDepth Q j) : Set (TriadicCube d)).PairwiseDisjoint cubeSet :=
      pairwiseDisjoint_descendantsAtDepth Q j
    rw [gridDualDepthTest_apply_of_mem v hR hxR, Finset.sum_eq_single R]
    · rw [Set.indicator_of_mem hxR]
    · intro S hS hSR
      refine Set.indicator_of_notMem ?_ _
      intro hxS
      exact (Set.disjoint_left.mp
        (hdisj (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hR) hSR) hxS) hxR
    · intro h
      exact absurd hR h
  · push Not at hx
    have hzero : gridDualDepthTest Q j v x = 0 := by
      rw [gridDualDepthTest]
      exact Finset.sum_eq_zero fun R hR => Set.indicator_of_notMem (hx R hR) _
    rw [hzero, euclideanNorm_zero, enorm_zero, ENNReal.zero_rpow_of_pos hr]
    exact (Finset.sum_eq_zero fun R hR => Set.indicator_of_notMem (hx R hR) _).symm

/-- The normalized `L^r` mass of a depth slice is the `ℓ^r` average of its cell
values: one depth, `|D_j|` cells of equal normalized measure. -/
theorem lintegral_enorm_euclideanNorm_gridDualDepthTest_rpow (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r ∂(normalizedCubeMeasure Q)) =
      ∑ R ∈ descendantsAtDepth Q j,
        (((descendantsAtDepth Q j).card : ℝ≥0∞))⁻¹ * ‖euclideanNorm (v R)‖ₑ ^ r := by
  classical
  rw [show (fun x => ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ r) =
      (fun x => ∑ R ∈ descendantsAtDepth Q j,
        (cubeSet R).indicator (fun _ => ‖euclideanNorm (v R)‖ₑ ^ r) x) from
    funext fun x => enorm_euclideanNorm_gridDualDepthTest_rpow Q j v hr x]
  rw [lintegral_finsetSum _
    (fun R _ => (measurable_const.indicator (measurableSet_cubeSet R)))]
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [lintegral_indicator (measurableSet_cubeSet R), setLIntegral_const,
    normalizedCubeMeasure_cubeSet_of_mem_descendantsAtDepth hR, mul_comm]

/-- The flat (normalized `L^{p'}`) norm of a depth slice, computed. -/
theorem normalizedEuclideanLpENorm_gridDualDepthTest (Q : TriadicCube d) (j : ℕ)
    (v : TriadicCube d → Vec d) (q : FiniteLpExponent) :
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent
        (gridDualDepthTest Q j v) =
      (∑ R ∈ descendantsAtDepth Q j,
        (((descendantsAtDepth Q j).card : ℝ≥0∞))⁻¹ *
          ‖euclideanNorm (v R)‖ₑ ^ q.exponent.toReal) ^ (1 / q.exponent.toReal) := by
  simp only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  have hmeas : Measurable (gridDualDepthTest Q j v) := by
    classical
    refine Finset.measurable_sum _ fun R _ => ?_
    exact measurable_const.indicator (measurableSet_cubeSet R)
  have hnorm : AEStronglyMeasurable (fun x => euclideanNorm (gridDualDepthTest Q j v x))
      (normalizedCubeMeasure Q) := by
    simp only [euclideanNorm_eq_norm_ofVec]
    exact ((HilbertVec.ofVecL d).continuous.measurable.comp hmeas).norm.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (lt_trans zero_lt_one q.one_lt)) q.lt_top.ne
      hnorm,
    lintegral_enorm_euclideanNorm_gridDualDepthTest_rpow Q j v (finiteLpExponent_toReal_pos q)]

/-- The Euclidean size of a dual-test coefficient: the `vecSupDual` factor is a
Euclidean unit vector, so no constant is spent. -/
theorem enorm_euclideanNorm_gridDualTestCoeff_le (Q : TriadicCube d) (s t : ℝ)
    (Fv : Vec d → Vec d) (j : ℕ) (R : TriadicCube d) :
    ‖euclideanNorm (gridDualTestCoeff Q s t Fv j R)‖ₑ ≤
      ENNReal.ofReal ((3 : ℝ) ^ (s * t * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
        ‖cubeAverageVec R Fv‖ ^ (t - 1)) := by
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * t * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
      ‖cubeAverageVec R Fv‖ ^ (t - 1) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hle : euclideanNorm (gridDualTestCoeff Q s t Fv j R) ≤
      (3 : ℝ) ^ (s * t * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
        ‖cubeAverageVec R Fv‖ ^ (t - 1) := by
    rw [gridDualTestCoeff, euclideanNorm_smul, abs_of_nonneg hc0]
    calc ((3 : ℝ) ^ (s * t * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
          ‖cubeAverageVec R Fv‖ ^ (t - 1)) * euclideanNorm (vecSupDual (cubeAverageVec R Fv))
        ≤ ((3 : ℝ) ^ (s * t * (((Q.scale - (j : ℤ) : ℤ)) : ℝ)) *
            ‖cubeAverageVec R Fv‖ ^ (t - 1)) * 1 :=
          mul_le_mul_of_nonneg_left (euclideanNorm_vecSupDual_le_one _) hc0
      _ = _ := mul_one _
  rw [Real.enorm_eq_ofReal (euclideanNorm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

/-! ## 3. The flat half of the single-depth full norm, at CONSTANT ONE

The identity behind the display is `(p-1)·p' = p` together with `p·p' = p + p'`:
the depth-`j` slice has normalized `L^{p'}` mass `3^{s·p·(m-j)}·A_j^{1/p'}` with
`A_j` the descendant average of `‖(F)_R‖^p`, and the scale weight `3^{-s·m·p'}`
turns the product into `3^{-s·j·p'}` times the depth energy `3^{s·p·(m-j)}·A_j`.
The spare factor `3^{-s·j·p'} ≤ 1` is thrown away below. -/

/-- The pure-real exponent bookkeeping of the flat half: with `t·r = t + r`
(the conjugacy relation) the flat exponent beats the depth-energy exponent by
exactly `s·r·j`. -/
private theorem depthFlat_exponent_le {s t r m0 jj : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hj : 0 ≤ jj) (hconj : t * r = t + r) :
    -(s * r) * m0 + s * t * (m0 - jj) * r ≤ s * t * (m0 - jj) := by
  have hrw : s * t * (m0 - jj) * r = s * (m0 - jj) * (t * r) := by ring
  have hkey : -(s * r) * m0 + s * (m0 - jj) * (t + r) =
      s * t * (m0 - jj) - s * r * jj := by ring
  have hpos : 0 ≤ s * r * jj := by positivity
  rw [hrw, hconj, hkey]
  linarith only [hpos]

/-- The Hölder conjugacy of a finite exponent, read in the reals. -/
theorem holderConjugate_toReal (p : FiniteLpExponent) :
    (p.exponent.toReal).HolderConjugate p.conjugate.exponent.toReal := by
  let : ENNReal.HolderConjugate p.exponent p.conjugate.exponent := p.holderConjugate
  exact ENNReal.HolderConjugate.toReal (one_lt_finiteLpExponent_toReal p)

/-- The scale weight of the full norm, in `ENNReal.ofReal` form. -/
theorem cubeEuclideanWspScalePowerWeight_eq_ofReal (Q : TriadicCube d) (s : FractionalOrder)
    (q : FiniteLpExponent) :
    cubeEuclideanWspScalePowerWeight Q s q =
      ENNReal.ofReal ((3 : ℝ) ^ (-(s.1 * q.exponent.toReal) * ((Q.scale : ℤ) : ℝ))) := by
  have hpos : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale
  rw [cubeEuclideanWspScalePowerWeight, ENNReal.ofReal_rpow_of_pos hpos]
  congr 1
  rw [cubeScaleFactor, ← Real.rpow_intCast (3 : ℝ) Q.scale,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  ring_nf

/-- **THE SINGLE-DEPTH FLAT HALF IS FREE.**

```text
  3^{-s·m·p'} · ‖g_j‖_{L^{p'}(Q)}^{p'}  ≤  cubeEuclideanNegativeBesovDepthEnergy Q s p F j
```

at constant ONE, uniformly in `s`, `j`, `Q`, `F` — no band, no `s₀`, no
`(1-3^{-s·p})^{-1/p}`.  (The true value of the left side is `3^{-s·j·p'}` times the
right side; the spare factor is discarded.)  This is the display the multi-depth
aggregate cannot have: there the same computation is followed by a Minkowski sum
and a discrete Hölder over the depths, and THAT is what buys the geometric
factor the necessity record of `HomSpineCzGridGaugeRefuted` shows sharp. -/
theorem weight_mul_flat_rpow_le_depthEnergy (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    cubeEuclideanWspScalePowerWeight Q s p.conjugate *
        ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.conjugate.exponent
            (gridDualDepthTest Q j
              (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j)))
          ^ p.conjugate.exponent.toReal ≤
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
  /- the flat mass, term by te -/
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
    calc ENNReal.ofReal ((3 : ℝ) ^ (s.1 * t * M) *
            ‖cubeAverageVec R F.toField‖ ^ (t - 1)) ^ r
        = ENNReal.ofReal (((3 : ℝ) ^ (s.1 * t * M) *
            ‖cubeAverageVec R F.toField‖ ^ (t - 1)) ^ r) :=
          ENNReal.ofReal_rpow_of_nonneg hnn hr.le
      _ = ENNReal.ofReal ((3 : ℝ) ^ (s.1 * t * M * r) *
            ‖cubeAverageVec R F.toField‖ ^ t) := by rw [hreal]
  /- the flat mass, summ -/
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
  /- assemb -/
  rw [normalizedEuclideanLpENorm_gridDualDepthTest Q j _ p.conjugate, ← hrs, one_div,
    ← ENNReal.rpow_mul, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one,
    cubeEuclideanWspScalePowerWeight_eq_ofReal Q s p.conjugate, ← hrs,
    depthEnergy_eq_ofReal Q s p F j]
  refine le_trans (mul_le_mul' le_rfl ((Finset.sum_le_sum hterm).trans (le_of_eq hsum))) ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : (3 : ℝ) ^ (-(s.1 * r) * ((Q.scale : ℤ) : ℝ)) * (3 : ℝ) ^ (s.1 * t * M * r) ≤
      (3 : ℝ) ^ (s.1 * t * M) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hMval : M = ((Q.scale : ℤ) : ℝ) - (j : ℝ) := by
      rw [hM]; push_cast; ring
    rw [hMval]
    exact depthFlat_exponent_le s.2.1 hr (Nat.cast_nonneg j) hconj.mul_eq_add
  calc (3 : ℝ) ^ (-(s.1 * r) * ((Q.scale : ℤ) : ℝ)) * ((3 : ℝ) ^ (s.1 * t * M * r) * A)
      = ((3 : ℝ) ^ (-(s.1 * r) * ((Q.scale : ℤ) : ℝ)) * (3 : ℝ) ^ (s.1 * t * M * r)) * A := by
        ring
    _ ≤ (3 : ℝ) ^ (s.1 * t * M) * A := mul_le_mul_of_nonneg_right hexp hA0

/-! ## 4. The band arithmetic of the Gagliardo half: near bands uniform, far bands NOT

A depth-`j` piecewise constant differs only across the depth-`j` skeleton, so the
Gagliardo double integral splits at the cell side `ℓ = 3^{m-j}`.

* NEAR bands (`|x-y| ~ 3^{m-k}`, `k ≥ j`): the straddling-pair measure is
  `3^{j-k}`-small and the kernel contributes `3^{(k-j)·s·p'}`, so band `k` is
  `3^{-(k-j)(1-s·p')}` relative to the flat mass — geometric at ratio `≤ 3^{-1/2}`
  on the band `s·p' ≤ 1/2`.  `sum_near_band_le` bounds the whole near half by
  `nearBandGeometricConstant`, uniformly in `s`, `j` and `d`.
* FAR bands (`k < j`, up to `diam Q`): every pair straddles, and band `k` is
  `3^{-(j-k)·s·p'}` relative to the flat mass.  The sum over the far bands is the
  truncated geometric series `Σ_{i<j} 3^{-i·s·p'}`, which is `≥ j/3` whenever
  `j·s·p' ≤ 1` and is UNBOUNDED over the admissible parameter range.
  This is this file's central negative finding: the
  single-depth Gagliardo half is NOT `γ`-uniform. -/

/-- The near-band geometric constant `(1-3^{-1/2})^{-1}`: the whole `k ≥ j` half of
the banded boundary-layer estimate, at any admissible `s·p' ≤ 1/2`. -/
def nearBandGeometricConstant : ℝ := (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

/-- **The near half is uniform.**  On the band `s·p' ≤ 1/2` the near bands sum at
ratio at most `3^{-1/2}`, so the whole near half costs `nearBandGeometricConstant`
— no `s`, no `j`, no `γ`. -/
theorem sum_near_band_le {x : ℝ} (hx : x ≤ 1 / 2) (K : ℕ) :
    (∑ i ∈ Finset.range K, (3 : ℝ) ^ (-(1 - x) * (i : ℝ))) ≤ nearBandGeometricConstant := by
  set r : ℝ := (3 : ℝ) ^ (-(1 - x)) with hr
  set r0 : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ)) with hr0
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr0pos : 0 < r0 := Real.rpow_pos_of_pos (by norm_num) _
  have hrr0 : r ≤ r0 :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hx])
  have hr0lt : r0 < 1 := by
    rw [hr0]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hden : 0 < 1 - r0 := by linarith only [hr0lt]
  have hpow : ∀ i : ℕ, (3 : ℝ) ^ (-(1 - x) * (i : ℝ)) = r ^ i := by
    intro i
    rw [hr, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 - x))) i,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hstep : (∑ i ∈ Finset.range K, (3 : ℝ) ^ (-(1 - x) * (i : ℝ))) ≤
      ∑ i ∈ Finset.range K, r0 ^ i := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hpow i]
    exact pow_le_pow_left₀ hrpos.le hrr0 i
  have hgeom : (∑ i ∈ Finset.range K, r0 ^ i) = (1 - r0 ^ K) / (1 - r0) := by
    rw [geom_sum_eq (by linarith only [hr0lt] : r0 ≠ 1),
      div_eq_div_iff (by linarith only [hr0lt] : r0 - 1 ≠ 0)
        (by linarith only [hden] : 1 - r0 ≠ 0)]
    ring
  have hnum : (1 : ℝ) - r0 ^ K ≤ 1 := by
    have : (0 : ℝ) ≤ r0 ^ K := pow_nonneg hr0pos.le _
    linarith only [this]
  calc (∑ i ∈ Finset.range K, (3 : ℝ) ^ (-(1 - x) * (i : ℝ)))
      ≤ ∑ i ∈ Finset.range K, r0 ^ i := hstep
    _ = (1 - r0 ^ K) / (1 - r0) := hgeom
    _ ≤ 1 / (1 - r0) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
    _ = nearBandGeometricConstant := by rw [nearBandGeometricConstant, ← hr0, one_div]

/-- **The single-depth full norm from a Gagliardo input.**  The flat half is free
(`§3`); so any Gagliardo bound `[g_j]^{p'} ≤ Cg^{p'}·(depth energy)` gives the full
norm at `(1+Cg^{p'})^{1/p'}·(depth energy)^{1/p'}`. -/
theorem fullENorm_gridDualDepthTest_le_of_gagliardo (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ)
    (Cg : ℝ≥0∞)
    (hgag : cubeEuclideanWspESeminorm Q s p.conjugate
          (gridDualDepthTest Q j (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j))
          ^ p.conjugate.exponent.toReal ≤
        Cg ^ p.conjugate.exponent.toReal *
          cubeEuclideanNegativeBesovDepthEnergy Q s p F j) :
    cubeEuclideanWspFullENorm Q s p.conjugate
        (gridDualDepthTest Q j (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j)) ≤
      (1 + Cg ^ p.conjugate.exponent.toReal) ^ (p.conjugate.exponent.toReal)⁻¹ *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j ^ (p.conjugate.exponent.toReal)⁻¹ := by
  have hrnn : (0 : ℝ) ≤ (p.conjugate.exponent.toReal)⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  have hsum : cubeEuclideanWspScalePowerWeight Q s p.conjugate *
        ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.conjugate.exponent
            (gridDualDepthTest Q j
              (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j)))
          ^ p.conjugate.exponent.toReal +
        cubeEuclideanWspESeminorm Q s p.conjugate
          (gridDualDepthTest Q j (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j))
          ^ p.conjugate.exponent.toReal ≤
      (1 + Cg ^ p.conjugate.exponent.toReal) *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
    refine le_trans (add_le_add (weight_mul_flat_rpow_le_depthEnergy Q s p F j) hgag) ?_
    rw [add_mul, one_mul]
  rw [cubeEuclideanWspFullENorm]
  calc (cubeEuclideanWspScalePowerWeight Q s p.conjugate *
          ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.conjugate.exponent
              (gridDualDepthTest Q j
                (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j)))
            ^ p.conjugate.exponent.toReal +
          cubeEuclideanWspESeminorm Q s p.conjugate
            (gridDualDepthTest Q j (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j))
            ^ p.conjugate.exponent.toReal) ^ (p.conjugate.exponent.toReal)⁻¹
      ≤ ((1 + Cg ^ p.conjugate.exponent.toReal) *
          cubeEuclideanNegativeBesovDepthEnergy Q s p F j) ^
            (p.conjugate.exponent.toReal)⁻¹ := ENNReal.rpow_le_rpow hsum hrnn
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hrnn

/-- **THE SINGLE-DEPTH GAUGE INEQUALITY.**

```text
  (depth energy)^{1/p}  ≤  (1+Cg^{p'})^{1/p'} · ‖F‖_{W^{-s,p}(Q), smooth dual}
```

from the Gagliardo input alone: the exact pairing of `§1`, the free flat half of
`§3`, `CoarseGraining`'s pairing bound, and a cancellation of the common factor
`(depth energy)^{1/p'}` — legitimate because the depth energy is an
`ENNReal.ofReal`, hence never `⊤`.  The hypothesis `hGfield` says only that `G` is a
`W^{s,p'} ∩ L²` carrier FOR THE SLICE ITSELF; no normalization is performed. -/
theorem depthEnergy_rpow_le_smoothDual_of_gagliardo (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ)
    (Cg : ℝ≥0∞) (G : CubeEuclideanWspL2Field Q s p.conjugate)
    (hGfield : G.toField =
      gridDualDepthTest Q j (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j))
    (hgag : cubeEuclideanWspESeminorm Q s p.conjugate
          (gridDualDepthTest Q j (gridDualTestCoeff Q s.1 p.exponent.toReal F.toField j))
          ^ p.conjugate.exponent.toReal ≤
        Cg ^ p.conjugate.exponent.toReal *
          cubeEuclideanNegativeBesovDepthEnergy Q s p F j) :
    cubeEuclideanNegativeBesovDepthEnergy Q s p F j ^ (p.exponent.toReal)⁻¹ ≤
      (1 + Cg ^ p.conjugate.exponent.toReal) ^ (p.conjugate.exponent.toReal)⁻¹ *
        cubeEuclideanNegativeWspSmoothDualENorm Q s p F := by
  classical
  set t : ℝ := p.exponent.toReal with hts
  set r : ℝ := p.conjugate.exponent.toReal with hrs
  have ht : 0 < t := finiteLpExponent_toReal_pos p
  have hr : 0 < r := finiteLpExponent_toReal_pos p.conjugate
  have hconj : t.HolderConjugate r := holderConjugate_toReal p
  set E : ℝ≥0∞ := cubeEuclideanNegativeBesovDepthEnergy Q s p F j with hE
  set K : ℝ≥0∞ := (1 + Cg ^ r) ^ r⁻¹ with hK
  have hEtop : E ≠ ⊤ := by
    rw [hE, depthEnergy_eq_ofReal]
    exact ENNReal.ofReal_ne_top
  /- the exact pairing, read off the carri -/
  have hpair : ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G| = E := by
    rw [cubeEuclideanNormalizedFieldPairing_eq_cubeAverage F G, hGfield,
      abs_of_nonneg (cubeAverage_vecDot_gridDualDepthTest_nonneg Q s.1 t ht F j),
      ofReal_cubeAverage_vecDot_gridDualDepthTest_eq Q s p F j]
  /- `CoarseGraining`'s pairing bound, and the full norm of the sli -/
  have hLIH : E ≤ cubeEuclideanNegativeWspSmoothDualENorm Q s p F *
      cubeEuclideanWspFullENorm Q s p.conjugate G.toField := by
    rw [← hpair]
    exact ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le F G
  have hfull : cubeEuclideanWspFullENorm Q s p.conjugate G.toField ≤ K * E ^ r⁻¹ := by
    rw [hGfield]
    exact fullENorm_gridDualDepthTest_le_of_gagliardo Q s p F j Cg hgag
  have hchain : E ≤ (cubeEuclideanNegativeWspSmoothDualENorm Q s p F * K) * E ^ r⁻¹ := by
    refine hLIH.trans ?_
    rw [mul_assoc]
    exact mul_le_mul' le_rfl hfull
  rcases eq_or_ne E 0 with hE0 | hE0
  · rw [hE0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  · have hsplit : E = E ^ t⁻¹ * E ^ r⁻¹ := by
      have hinv : t⁻¹ + r⁻¹ = 1 := by
        have := hconj.mul_eq_add
        field_simp
        linarith only [this]
      rw [← ENNReal.rpow_add_of_nonneg _ _ (le_of_lt (inv_pos.mpr ht))
        (le_of_lt (inv_pos.mpr hr)), hinv, ENNReal.rpow_one]
    have hne0 : E ^ r⁻¹ ≠ 0 := by
      intro hcon
      rcases ENNReal.rpow_eq_zero_iff.mp hcon with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hE0 h1
      · exact hEtop h1
    have hnetop : E ^ r⁻¹ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (le_of_lt (inv_pos.mpr hr)) hEtop
    have hcancel : E ^ t⁻¹ ≤ cubeEuclideanNegativeWspSmoothDualENorm Q s p F * K :=
      (ENNReal.mul_le_mul_iff_left hne0 hnetop).mp (by rw [← hsplit]; exact hchain)
    rw [mul_comm K]
    exact hcancel

end

end Algsuperdiff.Section4.Provider.Homogenization
