/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineDepthBandIntegral

/-!
# HomSpineDepthBandReduction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# THE GAGLIARDO REDUCTION of a single depth slice

## What this file is for

The Gagliardo double integral of the depth-`j` slice `g_j`, reduced to the band
sums.  Three moves, in order.

* `enorm_cubeEuclideanWspKernel_rpow_le_tsum` — POINTWISE.  On a pair inside `Q`
  the kernel either vanishes (`g_j` does not jump) or the pair sits in EXACTLY
  ONE triadic band (`exists_triadic_band`), where the kernel is at most the
  band's lower endpoint to the power `-(a+d)` (`euclideanDist ≥ dist`,
  `HomSpineDepthBandGeometry`) and the increment is at most `2^{p'}` times the
  two endpoint masses.
* `lintegral_lintegral_enorm_cubeEuclideanWspKernel_rpow_le` — the two
  integrals: one `lintegral_prod` to split the Gagliardo product measure, one
  `lintegral_tsum` per variable to exchange the band sum with the integrals,
  and `HomSpineDepthBandIntegral`'s band integral in each term.
* `cubeEuclideanWspESeminorm_gridDualDepthTest_rpow_le` — the result:

```text
  [g_j]_{W^{s,p'}(Q)}^{p'} ≤ 2^{p'}·2^{d+3}·(d+1)·3^d ·
      (cell side)^{-s·p'} · (near + Σ_{i<j} 3^{-i·s·p'}) · ⨍_Q ‖g_j‖^{p'},
```

with `gridDepthBandFactor` on the nose — the band shape
`HomSpineDepthGagliardoBand.GridDepthGagliardoBandInput` demands.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Two elementary `ℝ≥0∞` facts -/

/-- The crude `p`-th power splitting, at the constant `2^p` (no convexity). -/
theorem ennreal_add_rpow_le (u v : ℝ≥0∞) {r : ℝ} (hr : 0 ≤ r) :
    (u + v) ^ r ≤ 2 ^ r * (u ^ r + v ^ r) := by
  rcases le_total u v with h | h
  · have h1 : u + v ≤ 2 * v := by
      rw [two_mul]
      exact add_le_add h le_rfl
    calc (u + v) ^ r ≤ (2 * v) ^ r := ENNReal.rpow_le_rpow h1 hr
      _ = 2 ^ r * v ^ r := ENNReal.mul_rpow_of_nonneg _ _ hr
      _ ≤ 2 ^ r * (u ^ r + v ^ r) := mul_le_mul' le_rfl le_add_self
  · have h1 : u + v ≤ 2 * u := by
      rw [two_mul]
      exact add_le_add le_rfl h
    calc (u + v) ^ r ≤ (2 * u) ^ r := ENNReal.rpow_le_rpow h1 hr
      _ = 2 ^ r * u ^ r := ENNReal.mul_rpow_of_nonneg _ _ hr
      _ ≤ 2 ^ r * (u ^ r + v ^ r) := mul_le_mul' le_rfl le_self_add

/-- The Euclidean magnitude is subadditive on differences. -/
theorem euclideanNorm_sub_le (u w : Vec d) :
    euclideanNorm (u - w) ≤ euclideanNorm u + euclideanNorm w := by
  have hmap : HilbertVec.ofVec (u - w) = HilbertVec.ofVec u - HilbertVec.ofVec w := by
    simpa only [HilbertVec.ofVecL_apply] using map_sub (HilbertVec.ofVecL d) u w
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    hmap]
  exact norm_sub_le _ _

/-! ## 2. The band integrand -/

/-- The integrand of one triadic band: the band's kernel ceiling
`(3^{-(k+1)}L)^{-(a+d)}` times `2^{p'}` times the two endpoint masses of the
depth slice, supported on the straddling band. -/
def bandIntegrand (Q : TriadicCube d) (s : FractionalOrder) (q : FiniteLpExponent)
    (j : ℕ) (v : TriadicCube d → Vec d) (k : ℕ) : Vec d × Vec d → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (((1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q) ^
        (-(s.1 * q.exponent.toReal + (d : ℝ)))) * (2 : ℝ≥0∞) ^ q.exponent.toReal *
      ((straddleBand Q j k v).indicator
          (fun z : Vec d × Vec d =>
            ‖euclideanNorm (gridDualDepthTest Q j v z.1)‖ₑ ^ q.exponent.toReal) z +
        (straddleBand Q j k v).indicator
          (fun z : Vec d × Vec d =>
            ‖euclideanNorm (gridDualDepthTest Q j v z.2)‖ₑ ^ q.exponent.toReal) z)

theorem measurable_bandIntegrand (Q : TriadicCube d) (s : FractionalOrder)
    (q : FiniteLpExponent) (j : ℕ) (v : TriadicCube d → Vec d) (k : ℕ) :
    Measurable (bandIntegrand Q s q j v k) := by
  refine Measurable.const_mul ?_ _
  exact (((measurable_enorm_gridDualDepthTest Q j v q.exponent.toReal).comp
      measurable_fst).indicator (measurableSet_straddleBand Q j k v)).add
    (((measurable_enorm_gridDualDepthTest Q j v q.exponent.toReal).comp
      measurable_snd).indicator (measurableSet_straddleBand Q j k v))

/-! ## 3. The pointwise band bound -/


/-- **THE POINTWISE BAND BOUND.**  Every pair of `Q` is either a non-jump of the
depth slice (kernel zero) or sits in exactly one triadic band. -/
theorem enorm_cubeEuclideanWspKernel_rpow_le_tsum (Q : TriadicCube d) (s : FractionalOrder)
    (q : FiniteLpExponent) (j : ℕ) (v : TriadicCube d → Vec d)
    {x y : Vec d} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) :
    ‖cubeEuclideanWspKernel s q (gridDualDepthTest Q j v) (x, y)‖ₑ ^ q.exponent.toReal ≤
      ∑' k : ℕ, bandIntegrand Q s q j v k (x, y) := by
  classical
  set r : ℝ := q.exponent.toReal with hrs
  set g : Vec d → Vec d := gridDualDepthTest Q j v with hg
  have hr : 0 < r := finiteLpExponent_toReal_pos q
  have hL : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  set e : ℝ := s.1 + (d : ℝ) / r with he
  have he0 : 0 < e := by
    have h1 : (0 : ℝ) < s.1 := s.2.1
    have h2 : (0 : ℝ) ≤ (d : ℝ) / r := div_nonneg (Nat.cast_nonneg d) hr.le
    rw [he]
    linarith only [h1, h2]
  by_cases hgxy : g y = g x
  · have hzero : cubeEuclideanWspKernel s q g (x, y) = 0 := by
      rw [cubeEuclideanWspKernel_apply]
      have hsub : g (x, y).1 - g (x, y).2 = 0 := by
        change g x - g y = 0
        rw [hgxy]
        exact sub_self _
      rw [hsub]
      simp
    rw [hzero, enorm_zero, ENNReal.zero_rpow_of_pos hr]
    exact zero_le
  · have hne : x ≠ y := fun hxy => hgxy (by rw [hxy])
    have hdpos : 0 < dist x y := dist_pos.mpr hne
    have hdlt : dist x y < cubeScaleFactor Q := dist_lt_cubeScaleFactor hx hy
    obtain ⟨k, hk1, hk2⟩ := exists_triadic_band (u := dist x y / cubeScaleFactor Q)
      (by positivity) ((div_lt_one hL).mpr hdlt)
    have hlow : (1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q ≤ dist x y := by
      rw [le_div_iff₀ hL] at hk1
      linarith only [hk1]
    have hhigh : dist x y < (1 / 3 : ℝ) ^ k * cubeScaleFactor Q := by
      rw [div_lt_iff₀ hL] at hk2
      linarith only [hk2]
    have hmem : (x, y) ∈ straddleBand Q j k v := ⟨hx, hy, hgxy, hlow, hhigh⟩
    set c : ℝ := (1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q with hc
    have hcpos : 0 < c := by
      rw [hc]
      exact mul_pos (by positivity) hL
    refine le_trans ?_ (ENNReal.le_tsum k)
    simp only [bandIntegrand, Set.indicator_of_mem hmem]
    /- the kernel, bounded on the ba -/
    have hkerbd : ‖cubeEuclideanWspKernel s q g (x, y)‖ ≤
        c ^ (-e) * (euclideanNorm (g x) + euclideanNorm (g y)) := by
      rw [norm_cubeEuclideanWspKernel]
      refine mul_le_mul ?_ (euclideanNorm_sub_le _ _) (euclideanNorm_nonneg _)
        (Real.rpow_nonneg hcpos.le _)
      calc euclideanDist (x, y).1 (x, y).2 ^ (-e) ≤ dist x y ^ (-e) :=
            euclideanDist_rpow_neg_le x y he0
        _ ≤ c ^ (-e) := Real.rpow_le_rpow_of_nonpos hcpos hlow (by linarith only [he0])
    /- pass to `ℝ≥0∞` -/
    have hcr : c ^ (-e) ≥ 0 := Real.rpow_nonneg hcpos.le _
    have hsplit : ENNReal.ofReal (c ^ (-e) *
        (euclideanNorm (g x) + euclideanNorm (g y))) =
        ENNReal.ofReal (c ^ (-e)) *
          (ENNReal.ofReal (euclideanNorm (g x)) + ENNReal.ofReal (euclideanNorm (g y))) := by
      rw [ENNReal.ofReal_mul hcr,
        ENNReal.ofReal_add (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)]
    have hpow : ENNReal.ofReal (c ^ (-e)) ^ r =
        ENNReal.ofReal (c ^ (-(s.1 * r + (d : ℝ)))) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hcr hr.le, ← Real.rpow_mul hcpos.le]
      congr 2
      rw [he]
      field_simp
    have hNx : ENNReal.ofReal (euclideanNorm (g x)) ^ r = ‖euclideanNorm (g x)‖ₑ ^ r := by
      rw [Real.enorm_eq_ofReal (euclideanNorm_nonneg _)]
    have hNy : ENNReal.ofReal (euclideanNorm (g y)) ^ r = ‖euclideanNorm (g y)‖ₑ ^ r := by
      rw [Real.enorm_eq_ofReal (euclideanNorm_nonneg _)]
    calc ‖cubeEuclideanWspKernel s q g (x, y)‖ₑ ^ r
        = ENNReal.ofReal ‖cubeEuclideanWspKernel s q g (x, y)‖ ^ r := by
          rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (c ^ (-e) * (euclideanNorm (g x) + euclideanNorm (g y))) ^ r :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hkerbd) hr.le
      _ = ENNReal.ofReal (c ^ (-e)) ^ r *
            (ENNReal.ofReal (euclideanNorm (g x)) +
              ENNReal.ofReal (euclideanNorm (g y))) ^ r := by
          rw [hsplit, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
      _ ≤ ENNReal.ofReal (c ^ (-(s.1 * r + (d : ℝ)))) *
            (2 ^ r * (ENNReal.ofReal (euclideanNorm (g x)) ^ r +
              ENNReal.ofReal (euclideanNorm (g y)) ^ r)) := by
          rw [hpow]
          exact mul_le_mul' le_rfl (ennreal_add_rpow_le _ _ hr.le)
      _ = ENNReal.ofReal (c ^ (-(s.1 * r + (d : ℝ)))) * 2 ^ r *
            (‖euclideanNorm (g x)‖ₑ ^ r + ‖euclideanNorm (g y)‖ₑ ^ r) := by
          rw [hNx, hNy]
          ring


/-! ## 4. The band integral, at the band term -/

theorem lintegral_lintegral_bandIntegrand_le (Q : TriadicCube d) (s : FractionalOrder)
    (q : FiniteLpExponent) (j : ℕ) (v : TriadicCube d → Vec d) (k : ℕ) :
    (∫⁻ x, ∫⁻ y, bandIntegrand Q s q j v k (x, y) ∂(cubeMeasure Q) ∂(cubeMeasure Q)) ≤
      ENNReal.ofReal (bandTerm (s.1 * q.exponent.toReal) (cubeScaleFactor Q)
            ((d : ℝ) + 1) d j k) *
          ((2 : ℝ≥0∞) ^ q.exponent.toReal * 2) *
        ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ q.exponent.toReal
          ∂(cubeMeasure Q) := by
  classical
  have hr : 0 < q.exponent.toReal := finiteLpExponent_toReal_pos q
  have hL : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hbase : (0 : ℝ) < (1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q :=
    mul_pos (by norm_num) hL
  have hK0 : (0 : ℝ) ≤ ((1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q) ^
      (-(s.1 * q.exponent.toReal + (d : ℝ))) := Real.rpow_nonneg hbase.le _
  have hB0 : (0 : ℝ) ≤ (2 * ((1 / 3 : ℝ) ^ k * cubeScaleFactor Q)) ^ d :=
    pow_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hL.le)) _
  have hD0 : (0 : ℝ) ≤ (d : ℝ) + 1 := by
    have hdn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith only [hdn]
  have hc : ENNReal.ofReal (((1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q) ^
      (-(s.1 * q.exponent.toReal + (d : ℝ)))) * (2 : ℝ≥0∞) ^ q.exponent.toReal ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hr.le (by norm_num))
  have hpull : ∀ x : Vec d,
      (∫⁻ y, bandIntegrand Q s q j v k (x, y) ∂(cubeMeasure Q)) =
        ENNReal.ofReal (((1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q) ^
            (-(s.1 * q.exponent.toReal + (d : ℝ)))) * (2 : ℝ≥0∞) ^ q.exponent.toReal *
          ∫⁻ y, ((straddleBand Q j k v).indicator
              (fun z : Vec d × Vec d =>
                ‖euclideanNorm (gridDualDepthTest Q j v z.1)‖ₑ ^ q.exponent.toReal) (x, y) +
            (straddleBand Q j k v).indicator
              (fun z : Vec d × Vec d =>
                ‖euclideanNorm (gridDualDepthTest Q j v z.2)‖ₑ ^ q.exponent.toReal) (x, y))
            ∂(cubeMeasure Q) := by
    intro x
    exact lintegral_const_mul' _ _ hc
  have hofReal : ENNReal.ofReal (bandTerm (s.1 * q.exponent.toReal) (cubeScaleFactor Q)
        ((d : ℝ) + 1) d j k) =
      ENNReal.ofReal (((1 / 3 : ℝ) ^ (k + 1) * cubeScaleFactor Q) ^
          (-(s.1 * q.exponent.toReal + (d : ℝ)))) *
        ENNReal.ofReal ((2 * ((1 / 3 : ℝ) ^ k * cubeScaleFactor Q)) ^ d) *
        ENNReal.ofReal (bandStraddleWeight ((d : ℝ) + 1) j k) := by
    rw [bandTerm, bandKernelVolume, ENNReal.ofReal_mul (mul_nonneg hK0 hB0),
      ENNReal.ofReal_mul hK0]
  rw [lintegral_congr hpull, lintegral_const_mul' _ _ hc]
  refine le_trans (mul_le_mul' le_rfl
    (lintegral_lintegral_straddleBand_pair_le Q j k v hr)) (le_of_eq ?_)
  rw [hofReal]
  ring

/-! ## 5. The double integral -/

/-- The band sum of `HomSpineDepthBandArith`, read as an `ℝ≥0∞` series. -/
theorem tsum_ofReal_bandTerm_le {a L : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) (hL : 0 < L)
    {D : ℝ} (hD : 1 ≤ D) (dd j : ℕ) :
    (∑' k : ℕ, ENNReal.ofReal (bandTerm a L D dd j k)) ≤
      ENNReal.ofReal (2 ^ (dd + 2) * D * 3 ^ dd * (L / 3 ^ j) ^ (-a) *
        gridDepthBandFactor a j) := by
  have hD0 : (0 : ℝ) ≤ D := by linarith only [hD]
  have hnn : ∀ k : ℕ, 0 ≤ bandTerm a L D dd j k := fun k =>
    mul_nonneg (bandKernelVolume_nonneg hL.le dd k) (bandStraddleWeight_nonneg hD0 j k)
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k]
  exact ENNReal.ofReal_le_ofReal (sum_bandTerm_le ha0 ha hL hD dd j n)

/-- **THE DOUBLE INTEGRAL.**  Pointwise band bound, one `lintegral_tsum` per
variable, the band integral in each term, and the closed band sum. -/
theorem lintegral_lintegral_enorm_cubeEuclideanWspKernel_rpow_le (Q : TriadicCube d)
    (s : FractionalOrder) (q : FiniteLpExponent) (j : ℕ) (v : TriadicCube d → Vec d)
    (hband : s.1 * q.exponent.toReal ≤ 1 / 2) :
    (∫⁻ x, ∫⁻ y, ‖cubeEuclideanWspKernel s q (gridDualDepthTest Q j v) (x, y)‖ₑ ^
        q.exponent.toReal ∂(cubeMeasure Q) ∂(cubeMeasure Q)) ≤
      ENNReal.ofReal (2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d *
            (cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * q.exponent.toReal)) *
            gridDepthBandFactor (s.1 * q.exponent.toReal) j) *
          ((2 : ℝ≥0∞) ^ q.exponent.toReal * 2) *
        ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ q.exponent.toReal
          ∂(cubeMeasure Q) := by
  classical
  have : IsFiniteMeasure (cubeMeasure Q) :=
    ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top Q)⟩
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have hr : 0 < q.exponent.toReal := finiteLpExponent_toReal_pos q
  have hL : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have ha0 : 0 < s.1 * q.exponent.toReal := mul_pos s.2.1 hr
  have hD : (1 : ℝ) ≤ (d : ℝ) + 1 := by
    have hdn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith only [hdn]
  have hmono : ∀ (f₁ f₂ : Vec d → ℝ≥0∞), (∀ y ∈ cubeSet Q, f₁ y ≤ f₂ y) →
      (∫⁻ y, f₁ y ∂(cubeMeasure Q)) ≤ ∫⁻ y, f₂ y ∂(cubeMeasure Q) := by
    intro f₁ f₂ hle
    refine lintegral_mono_ae ?_
    rw [cubeMeasure]
    exact (ae_restrict_iff' (measurableSet_cubeSet Q)).mpr (Filter.Eventually.of_forall hle)
  have hexchange : (∫⁻ x, ∫⁻ y, (∑' k : ℕ, bandIntegrand Q s q j v k (x, y))
        ∂(cubeMeasure Q) ∂(cubeMeasure Q)) =
      ∑' k : ℕ, ∫⁻ x, ∫⁻ y, bandIntegrand Q s q j v k (x, y)
        ∂(cubeMeasure Q) ∂(cubeMeasure Q) := by
    have hinner : ∀ x : Vec d,
        (∫⁻ y, (∑' k : ℕ, bandIntegrand Q s q j v k (x, y)) ∂(cubeMeasure Q)) =
          ∑' k : ℕ, ∫⁻ y, bandIntegrand Q s q j v k (x, y) ∂(cubeMeasure Q) :=
      fun x => lintegral_tsum fun k =>
        (((measurable_bandIntegrand Q s q j v k).comp measurable_prodMk_left)).aemeasurable
    rw [lintegral_congr hinner]
    exact lintegral_tsum fun k =>
      ((measurable_bandIntegrand Q s q j v k).lintegral_prod_right').aemeasurable
  calc (∫⁻ x, ∫⁻ y, ‖cubeEuclideanWspKernel s q (gridDualDepthTest Q j v) (x, y)‖ₑ ^
          q.exponent.toReal ∂(cubeMeasure Q) ∂(cubeMeasure Q))
      ≤ ∫⁻ x, ∫⁻ y, (∑' k : ℕ, bandIntegrand Q s q j v k (x, y))
          ∂(cubeMeasure Q) ∂(cubeMeasure Q) :=
        hmono _ _ fun x hx => hmono _ _ fun y hy =>
          enorm_cubeEuclideanWspKernel_rpow_le_tsum Q s q j v hx hy
    _ = ∑' k : ℕ, ∫⁻ x, ∫⁻ y, bandIntegrand Q s q j v k (x, y)
          ∂(cubeMeasure Q) ∂(cubeMeasure Q) := hexchange
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (bandTerm (s.1 * q.exponent.toReal) (cubeScaleFactor Q)
            ((d : ℝ) + 1) d j k) *
          ((2 : ℝ≥0∞) ^ q.exponent.toReal * 2 *
            ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ q.exponent.toReal
              ∂(cubeMeasure Q)) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        refine le_trans (lintegral_lintegral_bandIntegrand_le Q s q j v k) (le_of_eq ?_)
        ring
    _ = (∑' k : ℕ, ENNReal.ofReal (bandTerm (s.1 * q.exponent.toReal) (cubeScaleFactor Q)
            ((d : ℝ) + 1) d j k)) *
          ((2 : ℝ≥0∞) ^ q.exponent.toReal * 2 *
            ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ q.exponent.toReal
              ∂(cubeMeasure Q)) := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d *
            (cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * q.exponent.toReal)) *
            gridDepthBandFactor (s.1 * q.exponent.toReal) j) *
          ((2 : ℝ≥0∞) ^ q.exponent.toReal * 2 *
            ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ q.exponent.toReal
              ∂(cubeMeasure Q)) :=
        mul_le_mul' (tsum_ofReal_bandTerm_le ha0 hband hL hD d j) le_rfl
    _ = _ := by ring

/-! ## 6. The Gagliardo seminorm of the depth slice -/

/-- **THE GAGLIARDO REDUCTION.**  The single-depth Gagliardo seminorm, reduced to
the band factor `gridDepthBandFactor` at the explicit dimensional constant
`2^{p'}·2^{d+3}·(d+1)·3^d` and the cell-side weight. -/
theorem cubeEuclideanWspESeminorm_gridDualDepthTest_rpow_le (Q : TriadicCube d)
    (s : FractionalOrder) (q : FiniteLpExponent) (j : ℕ) (v : TriadicCube d → Vec d)
    (hband : s.1 * q.exponent.toReal ≤ 1 / 2) :
    cubeEuclideanWspESeminorm Q s q (gridDualDepthTest Q j v) ^ q.exponent.toReal ≤
      ENNReal.ofReal (2 ^ (d + 2) * ((d : ℝ) + 1) * 3 ^ d *
            (cubeScaleFactor Q / 3 ^ j) ^ (-(s.1 * q.exponent.toReal)) *
            gridDepthBandFactor (s.1 * q.exponent.toReal) j) *
          ((2 : ℝ≥0∞) ^ q.exponent.toReal * 2) *
        ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ q.exponent.toReal
          ∂(normalizedCubeMeasure Q) := by
  classical
  have : IsFiniteMeasure (cubeMeasure Q) :=
    ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top Q)⟩
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have hr : 0 < q.exponent.toReal := finiteLpExponent_toReal_pos q
  have hmeasW : Measurable (fun z : Vec d × Vec d =>
      ‖cubeEuclideanWspKernel s q (gridDualDepthTest Q j v) z‖ₑ ^ q.exponent.toReal) :=
    ((measurable_cubeEuclideanWspKernel s q
      (measurable_gridDualDepthTest Q j v)).enorm).pow_const _
  have h0 : cubeEuclideanWspESeminorm Q s q (gridDualDepthTest Q j v) ^ q.exponent.toReal =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) *
        ∫⁻ x, ∫⁻ y, ‖cubeEuclideanWspKernel s q (gridDualDepthTest Q j v) (x, y)‖ₑ ^
          q.exponent.toReal ∂(cubeMeasure Q) ∂(cubeMeasure Q) := by
    rw [cubeEuclideanWspESeminorm_eq_lintegral Q s q _ (measurable_cubeEuclideanWspKernel s q
        (measurable_gridDualDepthTest Q j v)).aestronglyMeasurable,
      one_div, ENNReal.rpow_inv_rpow hr.ne',
      Gagliardo.gagliardoCubeMeasure, lintegral_prod _ hmeasW.aemeasurable,
      normalizedCubeMeasure, lintegral_smul_measure, smul_eq_mul]
  have hnorm : (∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ q.exponent.toReal
        ∂(normalizedCubeMeasure Q)) =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) *
        ∫⁻ x, ‖euclideanNorm (gridDualDepthTest Q j v x)‖ₑ ^ q.exponent.toReal
          ∂(cubeMeasure Q) := by
    rw [normalizedCubeMeasure, lintegral_smul_measure, smul_eq_mul]
  rw [h0, hnorm]
  refine le_trans (mul_le_mul' le_rfl
    (lintegral_lintegral_enorm_cubeEuclideanWspKernel_rpow_le Q s q j v hband))
    (le_of_eq ?_)
  ring

end

end Algsuperdiff.Section4.Provider.Homogenization
