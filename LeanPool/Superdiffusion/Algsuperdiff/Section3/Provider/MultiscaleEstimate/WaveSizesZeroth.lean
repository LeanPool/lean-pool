/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.WaveSizes
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TwoTermCalculus
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLinftyNorm
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.WaveTranslation

/-!
# WaveSizesZeroth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the zeroth-order leg and the full `W^{2,∞}` carrier of `e.wave.sizes`

Companion of `Provider/MultiscaleEstimate/WaveSizes.lean`, which carries the
*derivative half* of ABK26's wave-size display `e.wave.sizes`.  This
module adds the missing **zeroth-order `L∞` leg**, forms the extended carrier,
records the zeroth-order fidelity statement, and states
the headline endpoint `wave_sizes_bound` at that extended carrier.

This is a *provider endpoint only*.  It is not a source node, not a frozen
declaration, and it does not close `p.multiscale.estimate`.

## Why the zeroth order is required

The printed display carries `‖k_m - k_{l-h}‖_{W^{2,∞}(z+cu_l)}`.  **At `p = ∞`
the printed object is a maximum, not a sum.**  Reading at `p = ∞` on a cube of
side `3^l` (where `|U|^{-1/d} = 3^{-l}`) and iterating to second order gives

`3^{2l} ‖f‖_{W^{2,∞}(z+cu_l)}
   = max{‖f‖_{L∞(z+cu_l)}, 3^l ‖∇f‖_{L∞(z+cu_l)},
         3^{2l} ‖∇²f‖_{L∞(z+cu_l)}}`,

the `p → ∞` limit of the printed `ℓ^p` combination.  This module works with the
three-order **sum**

`‖f‖_{L∞(z+cu_l)} + 3^l ‖∇f‖_{L∞(z+cu_l)} + 3^{2l} ‖∇²f‖_{L∞(z+cu_l)}`,

which *dominates* that maximum, all three legs being nonnegative (and is at most
three times it, so the two are equivalent).  Every bound proved here against the
sum is therefore a bound on the printed maximum: the domination runs in the safe
direction and nothing is over-claimed.  An earlier version of this docstring
wrote the two with an `=`; that equation was false as written and is withdrawn.
"The three-order object" below always means the sum.

The zeroth-order term is **load-bearing**.  The frozen sensitivity remainder of
`Frozen/Section24/ResponseJSensitivity.lean` carries `vecNormSq p *
h.w1Infinity ^ 2` with `w1Infinity = max{‖∇h‖_{L∞(□₀)}, ‖h‖_{L∞(□₀)}}`
(`Frozen/Section24/UnitCubeSkewW2Infinity/W1Infinity.lean`), i.e. it contains
`‖h‖_{L∞}`, at a strictly positive coefficient; it is consumed verbatim at
`Provider/BadEvents/GoodLocalEvents.lean`.  The printed `e.J.sensitivity.apppp`
merges that remainder with the `gradientW1Infinity` remainder into the single
`3^{4l}‖·‖²_{W^{2,∞}}` object.  Any wave carrier that drops the `L∞` term
therefore does not feed the consumer.  See the full discussion in the sibling
module's docstring.

## The extended carrier

`waveGaugeW2 m h R` is the sum of the two legs at the triadic cube `R` of scale
`l = R.scale`, read at the base point `z = cubeCenter R`:

`waveGaugeW2 m h R = cubeSupBound R (l-h) m + waveGauge l m h (cubeCenter R)`.

* the **derivative leg** is the sibling module's `waveGauge`.

The `Γ₂` input for the zeroth-order leg is
`Stream.isBigOWith_gammaSigma_cubeSupBound`
(`Provider/Stream/WaveTranslation.lean`), the `Γ₂` form whose only binder
is `hnm : n < m` -- it carries **no** `m ≤ Q.scale` binder, which is what makes
it usable at `n = l-h`, `Q.scale = l ≤ m`.  The *squared* companions in that
module do carry `m ≤ Q.scale` and are unusable in the wave lane;
they are not touched here.  `cubeSupBound R m m = 0` covers the single
degenerate case `h = 0`, `l = m`.

`cubeCenter R = triadicCubeShift R` holds by definitional unfolding, so the two
legs really live on the same set: the cube `R` is exactly
`cubeCenter R + cu_l` (`openCubeSet_eq_translateSet_originCube_of_triadicCube`).

## The endpoint arithmetic, and why it is exactly `s^{-2}`

At `n = l-h`, `Q.scale = l = m-j` the amplitude of
`isBigOWith_gammaSigma_cubeSupBound` is

`(3 max{1, log |subcubeShifts d (l-h) l|})^{1/2}
   · C_∞(d) · min{√(γ^{-1}), √(m-l+h)} · 3^{γm}`,

with `|subcubeShifts d (l-h) l| = (2·3^{h+1}+1)^d`, so the covering penalty is
`O(√(h+1))`.  After the `3^{-γl}` normalization of `waveSizeW2` the factor
`3^{γm}` leaves `3^{γj}`, and after squaring and paying the grid maximum
(`waveGridConst d (1+j)`) the per-scale base is

`∝ (1+j) (j+h) 3^{2γj}`,

which is **quadratic** in the depth `j`.  The exponent split `three_rpow_split`
(legitimate because `s ≥ 8γ`) turns `3^{-sj} 3^{2γj}` into `3^{-(3/4)sj}`, and

`s Σ_j (1+j)(j+h) 3^{-(3/4)sj} ≤ C h s^{-2}`,

the printed `s^{-2}` exactly.  This is the reason the printed amplitude is
`s^{-2}` and not the `s^{-1}` the derivative half alone would give: the
zeroth-order leg, not the derivative leg, is what saturates the printed
exponent.  The summation lemma is `tsum_weighted_sq_le` below, proved from
`half_le_one_sub_three_rpow_neg` and the elementary
`(1+j) x^j ≤ (1-x)^{-1}` at the two auxiliary ratios `3^{-s/8}` and `3^{-s/2}`.

## Main definitions

* `waveCoverConst`, `waveSupAmp`, `waveAmpW2`, `waveLayerAmpW2`, `waveKW2`,
  `waveSizesConstW2`: the constants, all explicit.
* `waveGaugeW2`: the extended (three-order) wave carrier.
* `waveSizeW2`, `waveSizeMaxW2`, `waveSizesTotalW2`: the per-cube quantity, its
  grid maximum, and the complete left-hand side of `e.wave.sizes`, all at the
  extended carrier.
* `waveCutoff`: the integer cutoff `⌈C |log ε|⌉`.

## Main results

* `summable_weighted_sq`, `tsum_weighted_sq_le`: the weighted scale sum at a
  *quadratic* base, at `s^{-3}` (hence `s^{-2}` after the outer `s`).  Reusable
  development arithmetic.
* `streamIncrementLinftyNorm_le_waveGaugeW2`: **the zeroth-order half of the
  fidelity statement.**  The extended carrier dominates
  `‖k_m-k_{l-h}‖_{L∞(z+cu_l)}` in the genuine `L∞`-norm carrier
  `Stream.streamIncrementLinftyNorm`.
* `isBigOWith_gammaSigma_waveSup`: the `Γ₂` estimate for the zeroth-order leg.
* `isBigOWith_gammaSigma_waveGaugeW2`, `isBigOWith_gammaSigma_waveSizeW2`: the
  per-cube `Γ₂` estimate at the extended carrier.
* `isBigOWith_gammaSigma_waveSizeMaxW2_sq`: the per-scale `Γ₁` estimate.
* `isBigOWith_gammaSigma_waveSizesTotalW2`: `e.wave.sizes` at the extended
  carrier and the printed `s^{-2}`.
* `wave_sizes_bound`: **the headline**, the printed form `O_{Γ₁}(C s^{-2}
  ε^{-C})` at the extended carrier and at the integer cutoff `h = ⌈C₀|log ε|⌉`.

## The fidelity convention, stated

This module is stated against the **honest scale-`l`
convention** for the volume-normalized norm on a cube of side `3^l`.  At
`p = ∞` that norm is the maximum

`3^{2l}‖f‖_{W^{2,∞}(Q)}
   = max{‖f‖_{L∞(Q)}, 3^l‖∇f‖_{L∞(Q)}, 3^{2l}‖∇²f‖_{L∞(Q)}}`,

which is the reading (`‖·‖_{W^{1,p}}` with the `|U|^{-p/d}` weight on the
zeroth-order term, taken at `p = ∞` and iterated to second order) used
throughout the Section 3 stream chain.  The carrier is built against the
three-order **sum**

`‖f‖_{L∞(Q)} + 3^l‖∇f‖_{L∞(Q)} + 3^{2l}‖∇²f‖_{L∞(Q)}`,

which **dominates** that maximum (all three legs are nonnegative), so every
bound proved here against the sum implies the corresponding bound on the
printed `W^{2,∞}` object and claims nothing beyond it.  Writing the sum with
an `=` -- as an earlier version of this section did -- was wrong, and is
withdrawn: the relation is `max ≤ sum ≤ 3 max`, and only the first inequality
is used.  What *is* available, and used, is that the zeroth-order leg is stated
in the genuine `L∞`-norm carrier `Stream.streamIncrementLinftyNorm`, which
`Provider/Stream/IncrementLinftyNorm.lean` identifies with `eLpNorm ∞
(volume.restrict (openCubeSet (originCube d l)))` -- the same shape as the
frozen norms, one rescaling away.

## The grid/lattice identification, asserted not proved

Unchanged from the sibling module: the printed index set `z ∈ 3^l Z^d ∩ cu_m`
is realized as `descendantsAtScale (originCube d m) l` with `z:= cubeCenter R`.
This is the convention inherited from
`Localization.legScaleAverage` (`Provider/Localization/Breakdown.lean`),
asserted and not proved; the required set-equality pair is
recorded verbatim in the sibling module's docstring.  No declaration here
depends on it being a bijection.

## References

* ABK26, `e.wave.sizes`.
* ABK26, `e.J.sensitivity.apppp` (the consumer shape).
* ABK26, `e.km.kn.Linfty` (the zeroth-order input).
* ABK26, `l.maximums.Gamma.s`.
* ABK26, (the volume-normalized Sobolev norm convention).
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.IndependentSums
open _root_.Algsuperdiff.Frozen.Assumptions
open _root_.Algsuperdiff.Section3.Cutoff
open _root_.Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## Elementary real arithmetic: the quadratic base

All of this section is abstract-real: no model, no measure, no cube. -/

/-- `3^{-a j} = (3^{-a})^j`. -/
private theorem three_rpow_neg_mul_nat (a : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (-a * (j : ℝ)) = ((3 : ℝ) ^ (-a)) ^ j := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-a)) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- For `0 ≤ x < 1` the linear-times-geometric term is bounded by the geometric
sum: `(1 + j) x^j ≤ (1 - x)^{-1}`.  This is the elementary device that replaces
a closed form for `Σ j² x^j`. -/
private theorem one_add_mul_pow_le_inv_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (j : ℕ) : (1 + (j : ℝ)) * x ^ j ≤ (1 - x)⁻¹ := by
  have hsum : Summable (fun i : ℕ => x ^ i) := summable_geometric_of_lt_one hx0 hx1
  have hcard : ((Finset.range (j + 1)).card : ℕ) = j + 1 := Finset.card_range _
  have hstep : ∀ i ∈ Finset.range (j + 1), x ^ j ≤ x ^ i := by
    intro i hi
    exact pow_le_pow_of_le_one hx0 hx1.le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hle : (1 + (j : ℝ)) * x ^ j ≤ ∑ i ∈ Finset.range (j + 1), x ^ i := by
    have hnsmul := Finset.card_nsmul_le_sum (Finset.range (j + 1))
      (fun i => x ^ i) (x ^ j) hstep
    rw [hcard, nsmul_eq_mul] at hnsmul
    refine le_trans (le_of_eq ?_) hnsmul
    push_cast
    ring
  refine hle.trans ?_
  rw [← tsum_geometric_of_lt_one hx0 hx1]
  exact hsum.sum_le_tsum _ (fun i _ => pow_nonneg hx0 i)

/-- The quadratic-base term bound: at the split exponent `3/4 s` the factor
`(1+j)^2` costs `256 s^{-2}` and leaves the geometric ratio `3^{-s/2}`. -/
private theorem quad_term_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (j : ℕ) :
    (3 : ℝ) ^ (-(3 / 4 * s) * (j : ℝ)) * (1 + (j : ℝ)) ^ 2 ≤
      256 / s ^ 2 * ((3 : ℝ) ^ (-(s / 2))) ^ j := by
  set u : ℝ := (3 : ℝ) ^ (-(s / 8)) with hu
  set v : ℝ := (3 : ℝ) ^ (-(s / 2)) with hv
  have hu0 : (0 : ℝ) ≤ u := Real.rpow_nonneg (by norm_num) _
  have hv0 : (0 : ℝ) ≤ v := Real.rpow_nonneg (by norm_num) _
  have hgapu : s / 16 ≤ 1 - u := by
    have h := half_le_one_sub_three_rpow_neg (a := s / 8) (by linarith) (by linarith)
    rw [hu]
    linarith
  have hu1 : u < 1 := by linarith
  have hbase : (1 + (j : ℝ)) * u ^ j ≤ 16 / s :=
    (one_add_mul_pow_le_inv_one_sub hu0 hu1 j).trans
      (by
        have hpos : (0 : ℝ) < s / 16 := by linarith
        calc (1 - u)⁻¹ ≤ (s / 16)⁻¹ := inv_anti₀ hpos hgapu
          _ = 16 / s := by field_simp)
  have hsplit : (3 : ℝ) ^ (-(3 / 4 * s) * (j : ℝ)) = (u ^ j) ^ 2 * v ^ j := by
    rw [three_rpow_neg_mul_nat]
    have hprod : (3 : ℝ) ^ (-(3 / 4 * s)) = u ^ 2 * v := by
      rw [hu, hv, sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring_nf
    rw [hprod, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hnn : (0 : ℝ) ≤ (1 + (j : ℝ)) * u ^ j :=
    mul_nonneg (by positivity) (pow_nonneg hu0 j)
  have hsq : ((1 + (j : ℝ)) * u ^ j) ^ 2 ≤ (16 / s) ^ 2 :=
    pow_le_pow_left₀ hnn hbase 2
  have hexpand : (3 : ℝ) ^ (-(3 / 4 * s) * (j : ℝ)) * (1 + (j : ℝ)) ^ 2 =
      ((1 + (j : ℝ)) * u ^ j) ^ 2 * v ^ j := by
    rw [hsplit]
    ring
  rw [hexpand]
  refine (mul_le_mul_of_nonneg_right hsq (pow_nonneg hv0 j)).trans (le_of_eq ?_)
  rw [show (16 : ℝ) / s = 16 / s from rfl]
  field_simp
  ring

/-- **The weighted scale sum at a quadratic base.**  The zeroth-order leg of the
wave carrier has a per-scale base quadratic in the depth `j`; against the
geometric weight `3^{-s(m-l)}`, after the `γ`-drift has been absorbed by
`three_rpow_split`, it is summable and sums to at most `1024 K s^{-3}` -- the
printed `s^{-2}` after the outer prefactor `s`.

The route is the `three_rpow_split` step, a `Summable.of_nonneg_of_le`
majorization, and `tsum_mul_left` / `tsum_geometric_of_lt_one` / `inv_anti₀`
closing off `half_le_one_sub_three_rpow_neg`; the quadratic base is paid by
`one_add_mul_pow_le_inv_one_sub` and `quad_term_le` at the auxiliary ratio
`3^{-s/8}`. -/
private theorem weighted_sq_core {s gamma K : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hsg : 8 * gamma ≤ s) (hK : 0 ≤ K) :
    Summable (fun j : ℕ => (3 : ℝ) ^ (-s * (j : ℝ)) *
        ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K))) ∧
      ∑' j : ℕ, (3 : ℝ) ^ (-s * (j : ℝ)) *
        ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K)) ≤
          1024 * K / s ^ 3 := by
  set v : ℝ := (3 : ℝ) ^ (-(s / 2)) with hv
  have hv0 : (0 : ℝ) ≤ v := Real.rpow_nonneg (by norm_num) _
  have hgapv : s / 4 ≤ 1 - v := by
    have h := half_le_one_sub_three_rpow_neg (a := s / 2) (by linarith) (by linarith)
    rw [hv]
    linarith
  have hv1 : v < 1 := by linarith
  have hterm : ∀ j : ℕ, (3 : ℝ) ^ (-s * (j : ℝ)) *
      ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K)) ≤
      256 * K / s ^ 2 * v ^ j := by
    intro j
    have hstep : (3 : ℝ) ^ (-s * (j : ℝ)) * (3 : ℝ) ^ (2 * gamma * (j : ℝ)) ≤
        (3 : ℝ) ^ (-(3 / 4 * s) * (j : ℝ)) := by
      have h := three_rpow_split (s := s) (gamma := gamma) hsg j
      rw [show -(3 / 4 * s) = -(3 / 4 * s) from rfl]
      exact h
    have hquad := quad_term_le hs hs1 j
    have hj2 : (0 : ℝ) ≤ (1 + (j : ℝ)) ^ 2 := by positivity
    calc (3 : ℝ) ^ (-s * (j : ℝ)) *
          ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K))
        = ((3 : ℝ) ^ (-s * (j : ℝ)) * (3 : ℝ) ^ (2 * gamma * (j : ℝ))) *
            ((1 + (j : ℝ)) ^ 2 * K) := by ring
      _ ≤ (3 : ℝ) ^ (-(3 / 4 * s) * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K) :=
          mul_le_mul_of_nonneg_right hstep (mul_nonneg hj2 hK)
      _ = ((3 : ℝ) ^ (-(3 / 4 * s) * (j : ℝ)) * (1 + (j : ℝ)) ^ 2) * K := by ring
      _ ≤ (256 / s ^ 2 * v ^ j) * K := mul_le_mul_of_nonneg_right hquad hK
      _ = 256 * K / s ^ 2 * v ^ j := by ring
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ (3 : ℝ) ^ (-s * (j : ℝ)) *
      ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K)) := by
    intro j
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-s * (j : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * gamma * (j : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h3 : (0 : ℝ) ≤ (1 + (j : ℝ)) ^ 2 := by positivity
    positivity
  have hgeom : Summable (fun j : ℕ => v ^ j) := summable_geometric_of_lt_one hv0 hv1
  have hmaj : Summable (fun j : ℕ => 256 * K / s ^ 2 * v ^ j) :=
    hgeom.mul_left (256 * K / s ^ 2)
  have hsummable : Summable (fun j : ℕ => (3 : ℝ) ^ (-s * (j : ℝ)) *
      ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K))) :=
    Summable.of_nonneg_of_le hnn hterm hmaj
  refine ⟨hsummable, ?_⟩
  have hle := Summable.tsum_le_tsum hterm hsummable hmaj
  have hval : ∑' j : ℕ, 256 * K / s ^ 2 * v ^ j = 256 * K / s ^ 2 * ∑' j : ℕ, v ^ j :=
    hgeom.tsum_mul_left (256 * K / s ^ 2)
  have hgeoval : ∑' j : ℕ, v ^ j = (1 - v)⁻¹ := tsum_geometric_of_lt_one hv0 hv1
  have hinv : (1 - v)⁻¹ ≤ 4 / s := by
    have hpos : (0 : ℝ) < s / 4 := by linarith
    calc (1 - v)⁻¹ ≤ (s / 4)⁻¹ := inv_anti₀ hpos hgapv
      _ = 4 / s := by field_simp
  have hKs : (0 : ℝ) ≤ 256 * K / s ^ 2 := by positivity
  refine hle.trans ?_
  rw [hval, hgeoval]
  calc 256 * K / s ^ 2 * (1 - v)⁻¹ ≤ 256 * K / s ^ 2 * (4 / s) :=
        mul_le_mul_of_nonneg_left hinv hKs
    _ = 1024 * K / s ^ 3 := by field_simp; ring

/-- The quadratic-base weighted scale family is summable. -/
theorem summable_weighted_sq {s gamma K : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hsg : 8 * gamma ≤ s) (hK : 0 ≤ K) :
    Summable (fun j : ℕ => (3 : ℝ) ^ (-s * (j : ℝ)) *
      ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K))) :=
  (weighted_sq_core hs hs1 hsg hK).1

/-- **The quadratic-base weighted scale sum**, at `s^{-3}`. -/
theorem tsum_weighted_sq_le {s gamma K : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hsg : 8 * gamma ≤ s) (hK : 0 ≤ K) :
    ∑' j : ℕ, (3 : ℝ) ^ (-s * (j : ℝ)) *
        ((3 : ℝ) ^ (2 * gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K)) ≤
      1024 * K / s ^ 3 :=
  (weighted_sq_core hs hs1 hsg hK).2

/-! ## The covering penalty of the zeroth-order leg -/

/-- The dimensional constant of the covering penalty of `e.km.kn.Linfty` at the
wave lane's cutoff depth.

*Duplication, disclosed.*  This constant and the lemma `cover_log_le` below
re-derive a proved result of the same family, by the same route, from inside
this module's own import closure: `Provider/Stream/LargeCubeLinfty.lean` bounds
the same `3 max{1, log |subcubeShifts d n l|}` in
`three_mul_max_one_log_card_subcubeShifts_le`, at the constant
`largeCubeLogConst = 3(1 + 3 log 3)` there, by the same three steps.  The
constants are **different** (`3(1 + 2d log 3)` here, with `d` inside; `d` sits
outside there as a separate factor), and the reason for re-deriving rather than
consuming is the `h = 0` case -- see `cover_log_le`. -/
def waveCoverConst (d : ℕ) : ℝ := 3 * (1 + 2 * (d : ℝ) * Real.log 3)

theorem waveCoverConst_pos (d : ℕ) : 0 < waveCoverConst d := by
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [waveCoverConst]
  positivity

theorem waveCoverConst_nonneg (d : ℕ) : 0 ≤ waveCoverConst d :=
  (waveCoverConst_pos d).le

/-- The covering family of `cu_l` by cubes of scale `l - h` has cardinality
`(2·3^{h+1}+1)^d`, so the maximum-lemma penalty of `l.maximums.Gamma.s` is at
most `waveCoverConst d (1 + h)`.  Stated for every `h`, including `h = 0`, where
the family is the `7^d` covering of a cube by translates of itself.

*Why this is not the proved lemma.*  `Stream.three_mul_max_one_log_card_`
`subcubeShifts_le` (`Provider/Stream/LargeCubeLinfty.lean`, in this module's
under `n < l`, and with a right-hand side that vanishes at `n = l`.  The wave
lane meets `n = l - h` at `h = 0`, i.e. exactly `n = l`, so that form is
unusable at the degenerate cutoff; the `(1 + h)` here is positive there.  That
generalization is the whole content of the duplication, and it is why the
proved lemma is re-derived rather than consumed. -/
private theorem cover_log_le (d : ℕ) (l : ℤ) (h : ℕ) :
    3 * max 1 (Real.log
        (((subcubeShifts d (l - (h : ℤ)) l).card : ℕ) : ℝ)) ≤
      waveCoverConst d * (1 + (h : ℝ)) := by
  have hrad : subcubeRadius (l - (h : ℤ)) l = 3 ^ (h + 1) := by
    rw [subcubeRadius]
    congr 1
    omega
  have hcard : ((subcubeShifts d (l - (h : ℤ)) l).card : ℕ) = (2 * 3 ^ (h + 1) + 1) ^ d := by
    rw [card_subcubeShifts, hrad]
  have hbase : (0 : ℝ) < ((2 * 3 ^ (h + 1) + 1 : ℕ) : ℝ) := by
    have h0 : 0 < 2 * 3 ^ (h + 1) + 1 := by positivity
    exact_mod_cast h0
  have hle : 2 * 3 ^ (h + 1) + 1 ≤ 3 ^ (h + 2) := by
    have hone : 1 ≤ 3 ^ (h + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hpow : 3 ^ (h + 2) = 3 * 3 ^ (h + 1) := by ring
    omega
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hlogcard : Real.log (((subcubeShifts d (l - (h : ℤ)) l).card : ℕ) : ℝ) ≤
      (d : ℝ) * (((h : ℝ) + 2) * Real.log 3) := by
    rw [hcard]
    have hcast : (((2 * 3 ^ (h + 1) + 1) ^ d : ℕ) : ℝ) =
        ((2 * 3 ^ (h + 1) + 1 : ℕ) : ℝ) ^ d := by
      push_cast
      ring
    rw [hcast, Real.log_pow]
    have hmono : Real.log ((2 * 3 ^ (h + 1) + 1 : ℕ) : ℝ) ≤
        Real.log ((3 ^ (h + 2) : ℕ) : ℝ) :=
      Real.log_le_log hbase (by exact_mod_cast hle)
    have hpow : Real.log ((3 ^ (h + 2) : ℕ) : ℝ) = ((h : ℝ) + 2) * Real.log 3 := by
      have hc : (((3 : ℕ) ^ (h + 2) : ℕ) : ℝ) = (3 : ℝ) ^ (h + 2) := by norm_cast
      rw [hc, Real.log_pow]
      push_cast
      ring
    rw [hpow] at hmono
    exact mul_le_mul_of_nonneg_left hmono hd
  have hmax : max 1 (Real.log (((subcubeShifts d (l - (h : ℤ)) l).card : ℕ) : ℝ)) ≤
      (1 + 2 * (d : ℝ) * Real.log 3) * (1 + (h : ℝ)) := by
    refine max_le ?_ ?_
    · have hone : (1 : ℝ) ≤ 1 + 2 * (d : ℝ) * Real.log 3 := by
        have h2d := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd) hlog3
        linarith
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ (1 + 2 * (d : ℝ) * Real.log 3) * (1 + (h : ℝ)) :=
            mul_le_mul hone (by linarith) zero_le_one (by linarith)
    · refine hlogcard.trans ?_
      linarith only [hh, mul_nonneg (mul_nonneg hd hlog3) hh]
  rw [waveCoverConst]
  calc 3 * max 1 (Real.log (((subcubeShifts d (l - (h : ℤ)) l).card : ℕ) : ℝ))
      ≤ 3 * ((1 + 2 * (d : ℝ) * Real.log 3) * (1 + (h : ℝ))) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
    _ = 3 * (1 + 2 * (d : ℝ) * Real.log 3) * (1 + (h : ℝ)) := by ring

/-! ## The zeroth-order leg -/

/-- The uniform supremum gauge vanishes on an empty layer range.  Used for the
single degenerate case `h = 0`, `l = m` of the wave lane. -/
private theorem cubeSupBound_eq_zero (Q : TriadicCube d) {n m : ℤ} (hmn : m ≤ n)
    (omega : ShellSeq d) : cubeSupBound Q n m omega = 0 := by
  have hIoc : Finset.Ioc n m = (∅ : Finset ℤ) := Finset.Ioc_eq_empty_of_le hmn
  have hterm : ∀ p : Fin d → ℤ,
      translatedIncrementSupBound (cubeSubcubeCenter Q n p) n m omega = 0 := by
    intro p
    rw [translatedIncrementSupBound_eq, hIoc, Finset.sum_empty, mul_zero, add_zero]
    have hzero : finiteShellIncrement omega n m (cubeSubcubeCenter Q n p) = 0 := by
      rw [finiteShellIncrement_apply, hIoc, Finset.sum_empty]
    rw [hzero, Book.Ch02.matrixOperatorNorm_zero]
  rw [cubeSupBound]
  refine le_antisymm (Finset.sup'_le _ _ fun p _ => (hterm p).le) ?_
  obtain ⟨p, hp⟩ := subcubeShifts_nonempty d n Q.scale
  exact le_trans (le_of_eq (hterm p).symm)
    (Finset.le_sup'
      (fun q : Fin d → ℤ => translatedIncrementSupBound (cubeSubcubeCenter Q n q) n m omega)
      hp)

/-- The `Γ₂` amplitude of the zeroth-order leg at depth `j = m - l` and cutoff
`h`, after the `3^{-γl}` normalization: the covering penalty `√(C(d)(1+h))`, the
`e.km.kn.Linfty` constant, the layer count `√(j+h)`, and the residual `3^{γ j}`
left over from `3^{γ m} = 3^{γ j} 3^{γ l}`. -/
def waveSupAmp (M : ABKModel d) (h j : ℕ) : ℝ :=
  Real.sqrt (waveCoverConst d * (1 + (h : ℝ))) *
    (streamLinftyConst d * Real.sqrt ((j : ℝ) + (h : ℝ))) *
    (3 : ℝ) ^ (M.gamma * (j : ℝ))

theorem waveSupAmp_nonneg (M : ABKModel d) (h j : ℕ) : 0 ≤ waveSupAmp M h j := by
  have hd : 0 < d := by
    have := M.shellPrefix.dimension
    omega
  have hC : (0 : ℝ) < streamLinftyConst d := streamLinftyConst_pos hd
  have h1 : (0 : ℝ) ≤ Real.sqrt (waveCoverConst d * (1 + (h : ℝ))) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ Real.sqrt ((j : ℝ) + (h : ℝ)) := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  rw [waveSupAmp]
  positivity

/-- The exact square of the zeroth-order amplitude. -/
private theorem waveSupAmp_sq (M : ABKModel d) (h j : ℕ) :
    waveSupAmp M h j ^ 2 =
      waveCoverConst d * (1 + (h : ℝ)) * streamLinftyConst d ^ 2 *
        ((j : ℝ) + (h : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
  have hcov : (0 : ℝ) ≤ waveCoverConst d * (1 + (h : ℝ)) := by
    have := waveCoverConst_nonneg d
    have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    positivity
  have hjh : (0 : ℝ) ≤ (j : ℝ) + (h : ℝ) := by positivity
  have hrpow : ((3 : ℝ) ^ (M.gamma * (j : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (j : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    ring_nf
  rw [waveSupAmp, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hcov, Real.sq_sqrt hjh, hrpow]
  ring

/-- **The `Γ₂` estimate of the zeroth-order leg.**  On the triadic cube `R` of
scale `l = m - j`, the uniform supremum gauge of `k_m - k_{l-h}` obeys

`cubeSupBound R (l-h) m ≤ O_{Γ₂}(waveSupAmp M h j · 3^{γ l})`,

the amplitude being the `e.km.kn.Linfty` amplitude of
`Stream.isBigOWith_gammaSigma_cubeSupBound` with the covering penalty made
explicit.  Unlike the derivative leg, this amplitude *does* grow with the scale
gap `j = m - l`, through `√(j+h)` and `3^{γ j}`; that growth is exactly what
makes the `l`-sum land at the printed `s^{-2}`. -/
theorem isBigOWith_gammaSigma_waveSup (M : ABKModel d) (m : ℤ) (h j : ℕ)
    {R : TriadicCube d} (hR : R.scale = m - (j : ℤ)) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => cubeSupBound R (R.scale - (h : ℤ)) m omega)
      (waveSupAmp M h j * (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ))) := by
  have hgl : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hamp : (0 : ℝ) ≤ waveSupAmp M h j * (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ)) :=
    mul_nonneg (waveSupAmp_nonneg M h j) hgl.le
  rcases Nat.eq_zero_or_pos (j + h) with hjh | hjh
  · refine isBigOWith_gammaSigma_of_eq_zero hamp ?_
    intro omega
    have hj0 : j = 0 := by omega
    have hh0 : h = 0 := by omega
    refine cubeSupBound_eq_zero R ?_ omega
    rw [hR, hj0, hh0]
    omega
  · have hnm : R.scale - (h : ℤ) < m := by
      rw [hR]
      omega
    refine (isBigOWith_gammaSigma_cubeSupBound M hnm R).mono_scale ?_
    have hsqrt_eq : ∀ x : ℝ, x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
      intro x
      rw [Real.sqrt_eq_rpow, one_div]
    have h1 : (3 * max 1 (Real.log
        (((subcubeShifts d (R.scale - (h : ℤ)) R.scale).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ ≤
        Real.sqrt (waveCoverConst d * (1 + (h : ℝ))) := by
      rw [hsqrt_eq]
      exact Real.sqrt_le_sqrt (cover_log_le d R.scale h)
    have hgap : ((m : ℤ) : ℝ) - (((R.scale - (h : ℤ)) : ℤ) : ℝ) = (j : ℝ) + (h : ℝ) := by
      rw [hR]
      push_cast
      ring
    have hmR : ((m : ℤ) : ℝ) = ((R.scale : ℤ) : ℝ) + (j : ℝ) := by
      rw [hR]
      push_cast
      ring
    have hpowsplit : (3 : ℝ) ^ (M.gamma * ((m : ℤ) : ℝ)) =
        (3 : ℝ) ^ (M.gamma * (j : ℝ)) * (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hmR]
      ring_nf
    have hd : 0 < d := by
      have := M.shellPrefix.dimension
      omega
    have hCpos : (0 : ℝ) < streamLinftyConst d := streamLinftyConst_pos hd
    have hmin : min (Real.sqrt M.gamma⁻¹)
        (Real.sqrt (((m : ℤ) : ℝ) - (((R.scale - (h : ℤ)) : ℤ) : ℝ))) ≤
        Real.sqrt ((j : ℝ) + (h : ℝ)) := by
      rw [hgap]
      exact min_le_right _ _
    have hmin0 : (0 : ℝ) ≤ min (Real.sqrt M.gamma⁻¹)
        (Real.sqrt (((m : ℤ) : ℝ) - (((R.scale - (h : ℤ)) : ℤ) : ℝ))) :=
      le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h2 : streamLinftyConst d *
        min (Real.sqrt M.gamma⁻¹)
          (Real.sqrt (((m : ℤ) : ℝ) - (((R.scale - (h : ℤ)) : ℤ) : ℝ))) *
        (3 : ℝ) ^ (M.gamma * ((m : ℤ) : ℝ)) ≤
        streamLinftyConst d * Real.sqrt ((j : ℝ) + (h : ℝ)) *
          ((3 : ℝ) ^ (M.gamma * (j : ℝ)) *
            (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ))) := by
      rw [hpowsplit]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hmin hCpos.le
    have h2nn : (0 : ℝ) ≤ streamLinftyConst d *
        min (Real.sqrt M.gamma⁻¹)
          (Real.sqrt (((m : ℤ) : ℝ) - (((R.scale - (h : ℤ)) : ℤ) : ℝ))) *
        (3 : ℝ) ^ (M.gamma * ((m : ℤ) : ℝ)) := by
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * ((m : ℤ) : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      exact mul_nonneg (mul_nonneg hCpos.le hmin0) h3
    refine le_trans (mul_le_mul h1 h2 h2nn (Real.sqrt_nonneg _)) (le_of_eq ?_)
    rw [waveSupAmp]
    ring

/-! ## The extended carrier -/

/-- The base point of a triadic cube, as the development convention reads it, is
its translation vector: `cubeCenter` and `triadicCubeShift` are the same
function. -/
private theorem cubeCenter_eq_triadicCubeShift (R : TriadicCube d) :
    cubeCenter R = triadicCubeShift R := rfl

/-- **The extended wave carrier.**  The full three-order object of the printed
display at the cube `R` of scale `l = R.scale`, read at the base point
`z = cubeCenter R`:

`waveGaugeW2 m h R = ‖k_m-k_{l-h}‖_{L∞(R)}-gauge + waveGauge l m h z`,

the first summand the proved uniform supremum gauge `Stream.cubeSupBound` and
the second the derivative half of the sibling module.  It dominates
`3^{2l}‖k_m-k_{l-h}‖_{W^{2,∞}(z+cu_l)}`; the zeroth-order half of that
domination is `streamIncrementLinftyNorm_le_waveGaugeW2`. -/
def waveGaugeW2 (m : ℤ) (h : ℕ) (R : TriadicCube d) (omega : ShellSeq d) : ℝ :=
  cubeSupBound R (R.scale - (h : ℤ)) m omega +
    waveGauge R.scale m h (cubeCenter R) omega

theorem waveGaugeW2_nonneg (m : ℤ) (h : ℕ) (R : TriadicCube d) (omega : ShellSeq d) :
    0 ≤ waveGaugeW2 m h R omega :=
  add_nonneg (cubeSupBound_nonneg _ _ _ _) (waveGauge_nonneg _ _ _ _ _)

theorem measurable_waveGaugeW2 (m : ℤ) (h : ℕ) (R : TriadicCube d) :
    Measurable (fun omega : ShellSeq d => waveGaugeW2 m h R omega) :=
  (measurable_cubeSupBound R (R.scale - (h : ℤ)) m).add
    (measurable_waveGauge R.scale m h (cubeCenter R))

/-- **The zeroth-order half of the fidelity statement.**  The literal `L∞` norm
of the realized increment `k_m - k_{l-h}` on the cube `R`, in the genuine
`L∞`-norm carrier `Stream.streamIncrementLinftyNorm` read at the translated
sample (equivalently: on `cubeCenter R + cu_l`, which is `R`), is dominated by
the extended carrier. -/
theorem streamIncrementLinftyNorm_le_waveGaugeW2 (m : ℤ) (h : ℕ)
    (R : TriadicCube d) (omega : ShellSeq d) :
    streamIncrementLinftyNorm R.scale (R.scale - (h : ℤ)) m
        (ShellField.translateSequence (cubeCenter R) omega) ≤
      waveGaugeW2 m h R omega := by
  have hzero : streamIncrementLinftyNorm R.scale (R.scale - (h : ℤ)) m
      (ShellField.translateSequence (cubeCenter R) omega) ≤
      cubeSupBound R (R.scale - (h : ℤ)) m omega := by
    rw [cubeSupBound_eq_largeCubeSupBound_translate, cubeCenter_eq_triadicCubeShift]
    exact streamIncrementLinftyNorm_le_largeCubeSupBound
      (ShellField.translateSequence (triadicCubeShift R) omega) R.scale
      (R.scale - (h : ℤ)) m
  have hderiv : (0 : ℝ) ≤ waveGauge R.scale m h (cubeCenter R) omega :=
    waveGauge_nonneg _ _ _ _ _
  rw [waveGaugeW2]
  linarith

/-- The per-cube `Γ₂` amplitude of the extended carrier: the countable-triangle
constant applied to the two legs. -/
def waveAmpW2 (M : ABKModel d) (h j : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 * (waveSupAmp M h j + waveAmp d h)

theorem waveAmpW2_pos (M : ABKModel d) (h j : ℕ) : 0 < waveAmpW2 M h j := by
  have h1 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h2 : (0 : ℝ) ≤ waveSupAmp M h j := waveSupAmp_nonneg M h j
  have h3 : (0 : ℝ) < waveAmp d h := waveAmp_pos d h
  rw [waveAmpW2]
  positivity

theorem waveAmpW2_nonneg (M : ABKModel d) (h j : ℕ) : 0 ≤ waveAmpW2 M h j :=
  (waveAmpW2_pos M h j).le

/-- **The per-cube `Γ₂` estimate at the extended carrier.**  On every triadic
cube `R` of scale `l = m - j`,

`3^{2l}‖k_m-k_{l-h}‖_{W^{2,∞}(z+cu_l)} ≤ O_{Γ₂}(waveAmpW2 M h j · 3^{γ l})`. -/
theorem isBigOWith_gammaSigma_waveGaugeW2 (M : ABKModel d) (m : ℤ) (h j : ℕ)
    {R : TriadicCube d} (hR : R.scale = m - (j : ℤ)) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => waveGaugeW2 m h R omega)
      (waveAmpW2 M h j * (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ))) := by
  have hgl : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlm : R.scale ≤ m := by
    rw [hR]
    omega
  have hsup := isBigOWith_gammaSigma_waveSup M m h j hR
  have hgauge := isBigOWith_gammaSigma_waveGauge M hlm h (cubeCenter R)
  have hadd := Orlicz.isBigOWith_gammaSigma_add (μ := M.P.toMeasure) (σ := 2)
    (f := fun omega : ShellSeq d => cubeSupBound R (R.scale - (h : ℤ)) m omega)
    (g := fun omega : ShellSeq d => waveGauge R.scale m h (cubeCenter R) omega)
    (a := waveSupAmp M h j * (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ)))
    (b := waveAmp d h * (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ)))
    (by norm_num)
    (fun omega => cubeSupBound_nonneg _ _ _ _)
    (fun omega => waveGauge_nonneg _ _ _ _ _)
    (measurable_cubeSupBound R (R.scale - (h : ℤ)) m)
    (measurable_waveGauge R.scale m h (cubeCenter R))
    (mul_nonneg (waveSupAmp_nonneg M h j) hgl.le)
    (mul_nonneg (waveAmp_nonneg d h) hgl.le)
    hsup hgauge
  refine hadd.mono_scale (le_of_eq ?_)
  rw [waveAmpW2]
  ring

/-! ## The per-cube quantity, the grid maximum, and the scale sum -/

/-- **The printed per-cube quantity of `e.wave.sizes` at the extended
carrier**, `3^{(2-γ)l}‖k_m-k_{l-h}‖_{W^{2,∞}(z+cu_l)}`: the scale-`l`
normalized carrier already carries `3^{2l}`, so what is left is `3^{-γl}`. -/
def waveSizeW2 (M : ABKModel d) (m : ℤ) (h : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : ℝ :=
  (3 : ℝ) ^ (-M.gamma * ((R.scale : ℤ) : ℝ)) * waveGaugeW2 m h R omega

theorem waveSizeW2_nonneg (M : ABKModel d) (m : ℤ) (h : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : 0 ≤ waveSizeW2 M m h R omega :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (waveGaugeW2_nonneg _ _ _ _)

theorem measurable_waveSizeW2 (M : ABKModel d) (m : ℤ) (h : ℕ) (R : TriadicCube d) :
    Measurable (fun omega : ShellSeq d => waveSizeW2 M m h R omega) :=
  measurable_const.mul (measurable_waveGaugeW2 m h R)

/-- **The per-cube `Γ₂` estimate at the printed normalization.** -/
theorem isBigOWith_gammaSigma_waveSizeW2 (M : ABKModel d) (m : ℤ) (h j : ℕ)
    {R : TriadicCube d} (hR : R.scale = m - (j : ℤ)) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => waveSizeW2 M m h R omega) (waveAmpW2 M h j) := by
  have hbase := isBigOWith_gammaSigma_waveGaugeW2 M m h j hR
  have hmul := hbase.const_mul
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-M.gamma * ((R.scale : ℤ) : ℝ)))
  refine hmul.mono_scale (le_of_eq ?_)
  have hcancel : (3 : ℝ) ^ (-M.gamma * ((R.scale : ℤ) : ℝ)) *
      (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show -M.gamma * ((R.scale : ℤ) : ℝ) + M.gamma * ((R.scale : ℤ) : ℝ) = 0 by ring]
    exact Real.rpow_zero 3
  calc (3 : ℝ) ^ (-M.gamma * ((R.scale : ℤ) : ℝ)) *
        (waveAmpW2 M h j * (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ)))
      = waveAmpW2 M h j * ((3 : ℝ) ^ (-M.gamma * ((R.scale : ℤ) : ℝ)) *
          (3 : ℝ) ^ (M.gamma * ((R.scale : ℤ) : ℝ))) := by ring
    _ = waveAmpW2 M h j := by rw [hcancel, mul_one]

/-- The grid maximum of the printed per-cube quantity at depth `j = m - l`, at
the extended carrier. -/
def waveSizeMaxW2 (M : ABKModel d) (m : ℤ) (h j : ℕ) (omega : ShellSeq d) : ℝ :=
  (descendantsAtScale (originCube d m) (m - (j : ℤ))).sup'
    (waveGrid_nonempty m j) fun R => waveSizeW2 M m h R omega

theorem waveSizeW2_le_waveSizeMaxW2 (M : ABKModel d) (m : ℤ) (h j : ℕ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)))
    (omega : ShellSeq d) : waveSizeW2 M m h R omega ≤ waveSizeMaxW2 M m h j omega :=
  Finset.le_sup' (fun Q => waveSizeW2 M m h Q omega) hR

theorem waveSizeMaxW2_nonneg (M : ABKModel d) (m : ℤ) (h j : ℕ) (omega : ShellSeq d) :
    0 ≤ waveSizeMaxW2 M m h j omega := by
  obtain ⟨R, hR⟩ := waveGrid_nonempty (d := d) m j
  exact le_trans (waveSizeW2_nonneg M m h R omega)
    (waveSizeW2_le_waveSizeMaxW2 M m h j hR omega)

/-- The per-scale `Γ₁` amplitude at the extended carrier: the per-cube
amplitude squared, times the grid-maximum penalty. -/
def waveLayerAmpW2 (M : ABKModel d) (h j : ℕ) : ℝ :=
  waveGridConst d * (1 + (j : ℝ)) * waveAmpW2 M h j ^ 2

/-- **The per-scale `Γ₁` estimate at the extended carrier.** -/
theorem isBigOWith_gammaSigma_waveSizeMaxW2_sq (M : ABKModel d) (m : ℤ) (h j : ℕ) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => waveSizeMaxW2 M m h j omega ^ 2)
      (waveLayerAmpW2 M h j) := by
  have hmax : IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d => waveSizeMaxW2 M m h j omega)
      ((3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
          waveAmpW2 M h j) := by
    refine Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
      (descendantsAtScale (originCube d m) (m - (j : ℤ))) (waveGrid_nonempty m j)
      (by norm_num) (waveAmpW2_nonneg M h j) ?_
    intro R hR
    exact isBigOWith_gammaSigma_waveSizeW2 M m h j
      (descendant_scale_eq_of_mem_descendantsAtScale hR)
  have hsq := (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg (μ := M.P.toMeasure)
    (σ := 2)
    (K := (3 * max 1 (Real.log
      (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        waveAmpW2 M h j)
    (by
      have h1 : (0 : ℝ) ≤ (3 * max 1 (Real.log
          (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ :=
        Real.rpow_nonneg (by positivity) _
      exact mul_nonneg h1 (waveAmpW2_nonneg M h j))
    (fun omega => waveSizeMaxW2_nonneg M m h j omega)).1 hmax
  rw [show ((2 : ℝ) / 2) = 1 by norm_num] at hsq
  refine hsq.mono_scale ?_
  have hbase : (0 : ℝ) ≤ 3 * max 1 (Real.log
      (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ)) := by
    have h1 : (1 : ℝ) ≤ max 1 (Real.log
      (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ)) := le_max_left _ _
    linarith
  have hsqbase : ((3 * max 1 (Real.log
      (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹) ^ 2 =
      3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast ((3 * max 1 (Real.log
      (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹) 2,
      ← Real.rpow_mul hbase]
    norm_num
  have hexpand : ((3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        waveAmpW2 M h j) ^ 2 =
      (3 * max 1 (Real.log
        (((descendantsAtScale (originCube d m) (m - (j : ℤ))).card : ℕ) : ℝ))) *
        waveAmpW2 M h j ^ 2 := by
    rw [mul_pow, hsqbase]
  rw [hexpand, waveLayerAmpW2]
  exact mul_le_mul_of_nonneg_right (three_mul_max_one_log_card_waveGrid_le m j)
    (by positivity)

/-- **The left-hand side of `e.wave.sizes` at the extended carrier**, reindexed
by the depth `j = m - l`. -/
def waveSizesTotalW2 (M : ABKModel d) (m : ℤ) (h : ℕ) (s : ℝ)
    (omega : ShellSeq d) : ℝ :=
  s * ∑' j : ℕ, (3 : ℝ) ^ (-s * (j : ℝ)) *
    Localization.legScaleAverage (originCube d m) (m - (j : ℤ)) s
      (fun R => waveSizeW2 M m h R omega ^ 2)

/-- The per-scale power mean is at most the squared grid maximum.  As in the
sibling module, `d ≠ 0` is derived from `M`, not assumed. -/
theorem legScaleAverage_waveSizeW2_sq_le (M : ABKModel d) (m : ℤ) (h j : ℕ) {s : ℝ}
    (hs : 0 < s) (omega : ShellSeq d) :
    Localization.legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => waveSizeW2 M m h R omega ^ 2) ≤ waveSizeMaxW2 M m h j omega ^ 2 := by
  have hd : d ≠ 0 := by
    have := M.shellPrefix.dimension
    omega
  refine Localization.legScaleAverage_le_const (originCube d m) (m - (j : ℤ)) hs
    (by positivity) (fun R _ => by positivity) (fun R hR => ?_) hd
  have hle := waveSizeW2_le_waveSizeMaxW2 M m h j hR omega
  have hnn := waveSizeW2_nonneg M m h R omega
  exact pow_le_pow_left₀ hnn hle 2

/-- **Measurability hook, per-scale level, extended carrier.** -/
theorem measurable_waveScaleAverageW2 (M : ABKModel d) (m : ℤ) (h j : ℕ) {s : ℝ}
    (hs : 0 < s) :
    Measurable (fun omega : ShellSeq d =>
      Localization.legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => waveSizeW2 M m h R omega ^ 2)) := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have houter : Measurable (fun x : ℝ => Real.rpow x (s / (d : ℝ))) :=
    (Real.continuous_rpow_const (by positivity)).measurable
  have hinner : Measurable (fun x : ℝ => Real.rpow x ((d : ℝ) / s)) :=
    (Real.continuous_rpow_const (by positivity)).measurable
  simp only [Localization.legScaleAverage, Book.Ch02.finsetAverageReal]
  refine houter.comp (Measurable.const_mul ?_ _)
  exact Finset.measurable_sum _ fun R _ =>
    hinner.comp ((measurable_waveSizeW2 M m h R).pow_const 2)

/-- The cutoff-dependent per-scale majorant of the extended carrier: the
constant `K` for which the per-scale `Γ₁` amplitude is at most
`(1+j)^2 3^{2γj} K`. -/
def waveKW2 (d h : ℕ) : ℝ :=
  waveGridConst d * (2 * IndependentSums.gammaTriangleConst 2 ^ 2) *
    (waveCoverConst d * (1 + (h : ℝ)) ^ 2 * streamLinftyConst d ^ 2 + waveAmp d h ^ 2)

theorem waveKW2_pos (d h : ℕ) : 0 < waveKW2 d h := by
  have h1 : (0 : ℝ) < waveGridConst d := waveGridConst_pos d
  have h2 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h3 : (0 : ℝ) < waveAmp d h := waveAmp_pos d h
  have h4 : (0 : ℝ) ≤ waveCoverConst d * (1 + (h : ℝ)) ^ 2 * streamLinftyConst d ^ 2 := by
    have h5 : (0 : ℝ) ≤ waveCoverConst d := waveCoverConst_nonneg d
    have h6 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    positivity
  rw [waveKW2]
  have h7 : (0 : ℝ) < waveCoverConst d * (1 + (h : ℝ)) ^ 2 * streamLinftyConst d ^ 2 +
      waveAmp d h ^ 2 := add_pos_of_nonneg_of_pos h4 (pow_pos h3 2)
  positivity

theorem waveKW2_nonneg (d h : ℕ) : 0 ≤ waveKW2 d h := (waveKW2_pos d h).le

/-- The per-scale amplitude is dominated by the quadratic base. -/
theorem waveLayerAmpW2_le (M : ABKModel d) (h j : ℕ) :
    waveLayerAmpW2 M h j ≤
      (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * waveKW2 d h) := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hgrid : (0 : ℝ) < waveGridConst d := waveGridConst_pos d
  have htri : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hcov : (0 : ℝ) ≤ waveCoverConst d := waveCoverConst_nonneg d
  have hamp : (0 : ℝ) ≤ waveAmp d h := waveAmp_nonneg d h
  have hsup : (0 : ℝ) ≤ waveSupAmp M h j := waveSupAmp_nonneg M h j
  have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
    have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
    have hexp : (0 : ℝ) ≤ 2 * M.gamma * (j : ℝ) := by positivity
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    simpa using this
  have hpow0 : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by linarith
  -- Step 1: the squared per-cube amplitude, split by `(a+b)^2 ≤ 2(a^2+b^2)`.
  have hsplit : waveAmpW2 M h j ^ 2 ≤
      IndependentSums.gammaTriangleConst 2 ^ 2 * 2 *
        (waveSupAmp M h j ^ 2 + waveAmp d h ^ 2) := by
    rw [waveAmpW2, mul_pow]
    have hab : (waveSupAmp M h j + waveAmp d h) ^ 2 ≤
        2 * (waveSupAmp M h j ^ 2 + waveAmp d h ^ 2) := by
      linarith only [sq_nonneg (waveSupAmp M h j - waveAmp d h)]
    calc IndependentSums.gammaTriangleConst 2 ^ 2 * (waveSupAmp M h j + waveAmp d h) ^ 2
        ≤ IndependentSums.gammaTriangleConst 2 ^ 2 *
            (2 * (waveSupAmp M h j ^ 2 + waveAmp d h ^ 2)) :=
          mul_le_mul_of_nonneg_left hab (sq_nonneg _)
      _ = IndependentSums.gammaTriangleConst 2 ^ 2 * 2 *
            (waveSupAmp M h j ^ 2 + waveAmp d h ^ 2) := by ring
  have hsupsq := waveSupAmp_sq M h j
  have hSpos : (0 : ℝ) ≤ waveCoverConst d * (1 + (h : ℝ)) * streamLinftyConst d ^ 2 := by
    positivity
  -- Step 2: `(1+j)(j+h) ≤ (1+h)(1+j)^2` and `(1+j) ≤ (1+j)^2 3^{2γj}`.
  have hcross : (1 + (j : ℝ)) * ((j : ℝ) + (h : ℝ)) ≤
      (1 + (h : ℝ)) * (1 + (j : ℝ)) ^ 2 := by
    have hnn : (0 : ℝ) ≤ (1 + (j : ℝ)) * (1 + (h : ℝ) * (j : ℝ)) := by positivity
    linarith only [hnn]
  have hlin : (1 + (j : ℝ)) ≤ (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
    have hb : (0 : ℝ) ≤ 1 + (j : ℝ) := by linarith
    have h1 : (1 + (j : ℝ)) ≤ (1 + (j : ℝ)) ^ 2 := by
      rw [pow_two]
      exact le_mul_of_one_le_right hb (by linarith)
    exact h1.trans (le_mul_of_one_le_right (sq_nonneg _) hpow)
  have hSP : (0 : ℝ) ≤ waveCoverConst d * (1 + (h : ℝ)) * streamLinftyConst d ^ 2 *
      (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := mul_nonneg hSpos hpow0.le
  have hkey : waveGridConst d * (1 + (j : ℝ)) *
      (IndependentSums.gammaTriangleConst 2 ^ 2 * 2 *
        (waveSupAmp M h j ^ 2 + waveAmp d h ^ 2)) ≤
      (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * waveKW2 d h) := by
    rw [hsupsq, waveKW2]
    have hA : (1 + (j : ℝ)) * (waveCoverConst d * (1 + (h : ℝ)) * streamLinftyConst d ^ 2 *
          ((j : ℝ) + (h : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) ≤
        (1 + (j : ℝ)) ^ 2 * (waveCoverConst d * (1 + (h : ℝ)) ^ 2 *
          streamLinftyConst d ^ 2) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
      calc (1 + (j : ℝ)) * (waveCoverConst d * (1 + (h : ℝ)) * streamLinftyConst d ^ 2 *
              ((j : ℝ) + (h : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)))
          = ((1 + (j : ℝ)) * ((j : ℝ) + (h : ℝ))) *
              (waveCoverConst d * (1 + (h : ℝ)) * streamLinftyConst d ^ 2 *
                (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by ring
        _ ≤ ((1 + (h : ℝ)) * (1 + (j : ℝ)) ^ 2) *
              (waveCoverConst d * (1 + (h : ℝ)) * streamLinftyConst d ^ 2 *
                (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) :=
            mul_le_mul_of_nonneg_right hcross hSP
        _ = (1 + (j : ℝ)) ^ 2 * (waveCoverConst d * (1 + (h : ℝ)) ^ 2 *
              streamLinftyConst d ^ 2) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by ring
    have hB : (1 + (j : ℝ)) * waveAmp d h ^ 2 ≤
        (1 + (j : ℝ)) ^ 2 * waveAmp d h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
      have hstep := mul_le_mul_of_nonneg_right hlin (sq_nonneg (waveAmp d h))
      calc (1 + (j : ℝ)) * waveAmp d h ^ 2
          ≤ ((1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) *
              waveAmp d h ^ 2 := hstep
        _ = (1 + (j : ℝ)) ^ 2 * waveAmp d h ^ 2 *
              (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by ring
    have hfacnn : (0 : ℝ) ≤
        waveGridConst d * (IndependentSums.gammaTriangleConst 2 ^ 2 * 2) := by positivity
    calc waveGridConst d * (1 + (j : ℝ)) *
          (IndependentSums.gammaTriangleConst 2 ^ 2 * 2 *
            (waveCoverConst d * (1 + (h : ℝ)) * streamLinftyConst d ^ 2 *
              ((j : ℝ) + (h : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) + waveAmp d h ^ 2))
        = waveGridConst d * (IndependentSums.gammaTriangleConst 2 ^ 2 * 2) *
            ((1 + (j : ℝ)) * (waveCoverConst d * (1 + (h : ℝ)) * streamLinftyConst d ^ 2 *
                ((j : ℝ) + (h : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) +
              (1 + (j : ℝ)) * waveAmp d h ^ 2) := by ring
      _ ≤ waveGridConst d * (IndependentSums.gammaTriangleConst 2 ^ 2 * 2) *
            ((1 + (j : ℝ)) ^ 2 * (waveCoverConst d * (1 + (h : ℝ)) ^ 2 *
                streamLinftyConst d ^ 2) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) +
              (1 + (j : ℝ)) ^ 2 * waveAmp d h ^ 2 *
                (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) :=
          mul_le_mul_of_nonneg_left (add_le_add hA hB) hfacnn
      _ = (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 *
            (waveGridConst d * (2 * IndependentSums.gammaTriangleConst 2 ^ 2) *
              (waveCoverConst d * (1 + (h : ℝ)) ^ 2 * streamLinftyConst d ^ 2 +
                waveAmp d h ^ 2))) := by ring
  refine le_trans ?_ hkey
  rw [waveLayerAmpW2]
  exact mul_le_mul_of_nonneg_left hsplit (by positivity)

/-- The dimensional constant of the extended wave-size endpoint. -/
def waveSizesConstW2 : ℝ := 1024 * IndependentSums.gammaTriangleConst 1

theorem waveSizesConstW2_pos : 0 < waveSizesConstW2 := by
  have h1 : (0 : ℝ) < IndependentSums.gammaTriangleConst 1 :=
    IndependentSums.gammaTriangleConst_pos
  rw [waveSizesConstW2]
  positivity

/-- **`e.wave.sizes` at the extended carrier and the printed `s^{-2}`.**  For
every integer cutoff `h` and every `s ∈ [8γ, 1]`,

`s Σ_{l ≤ m} 3^{-s(m-l)}
   (⨍_z (3^{(2-γ)l}‖k_m-k_{l-h}‖_{W^{2,∞}(z+cu_l)})^{2d/s})^{s/d}
     ≤ O_{Γ₁}(C(d,h) s^{-2})`,

with the *full* `W^{2,∞}` object on the left.  The exponent is exactly the
printed one: the zeroth-order leg's quadratic base is what saturates it. -/
theorem isBigOWith_gammaSigma_waveSizesTotalW2 (M : ABKModel d) (m : ℤ) (h : ℕ)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hsg : 8 * M.gamma ≤ s) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => waveSizesTotalW2 M m h s omega)
      (waveSizesConstW2 * waveKW2 d h / s ^ 2) := by
  set K : ℝ := waveKW2 d h with hKdef
  have hKpos : (0 : ℝ) < K := by
    rw [hKdef]
    exact waveKW2_pos d h
  have hK : (0 : ℝ) ≤ K := hKpos.le
  set a : ℕ → ℝ := fun j => (3 : ℝ) ^ (-s * (j : ℝ)) *
    ((3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) * ((1 + (j : ℝ)) ^ 2 * K)) with hadef
  set X : ℕ → ShellSeq d → ℝ := fun j omega => (3 : ℝ) ^ (-s * (j : ℝ)) *
    Localization.legScaleAverage (originCube d m) (m - (j : ℤ)) s
      (fun R => waveSizeW2 M m h R omega ^ 2) with hXdef
  have hapos : ∀ j : ℕ, 0 < a j := by
    intro j
    have h1 : (0 : ℝ) < (3 : ℝ) ^ (-s * (j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h3 : (0 : ℝ) < (1 + (j : ℝ)) ^ 2 := by positivity
    rw [hadef]
    positivity
  have hleg_nonneg : ∀ (j : ℕ) (omega : ShellSeq d),
      0 ≤ Localization.legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => waveSizeW2 M m h R omega ^ 2) := fun j omega =>
    Localization.legScaleAverage_nonneg _ _ _ (fun R _ => by positivity)
  have hXnonneg : ∀ (j : ℕ) (omega : ShellSeq d), 0 ≤ X j omega := by
    intro j omega
    rw [hXdef]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hleg_nonneg j omega)
  have hXmeas : ∀ j : ℕ, Measurable (X j) := by
    intro j
    rw [hXdef]
    exact measurable_const.mul (measurable_waveScaleAverageW2 M m h j hs)
  have hXbig : ∀ j : ℕ,
      IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
        (X j) (a j) := by
    intro j
    have hlayer := (isBigOWith_gammaSigma_waveSizeMaxW2_sq M m h j).of_le
      (fun omega => legScaleAverage_waveSizeW2_sq_le M m h j hs omega)
    have hmul := hlayer.const_mul
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-s * (j : ℝ)))
    refine hmul.mono_scale ?_
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-s * (j : ℝ)) := Real.rpow_nonneg (by norm_num) _
    rw [hadef, hKdef]
    exact mul_le_mul_of_nonneg_left (waveLayerAmpW2_le M h j) hw
  have hsummable : Summable a := by
    rw [hadef]
    exact summable_weighted_sq hs hs1 hsg hK
  have htsum := Orlicz.isBigOWith_gammaSigma_tsum (μ := M.P.toMeasure) (X := X)
    (a := a) (σ := 1) (by norm_num) hXnonneg hXmeas hapos hsummable hXbig
  have hbound : ∑' j : ℕ, a j ≤ 1024 * K / s ^ 3 := by
    rw [hadef]
    exact tsum_weighted_sq_le hs hs1 hsg hK
  have htri : (0 : ℝ) ≤ IndependentSums.gammaTriangleConst 1 :=
    IndependentSums.gammaTriangleConst_pos.le
  have hstep := (htsum.mono_scale (mul_le_mul_of_nonneg_left hbound htri)).const_mul hs.le
  refine hstep.mono_scale (le_of_eq ?_)
  rw [waveSizesConstW2, hKdef]
  field_simp

/-! ## The printed cutoff `h = ⌈C|log ε|⌉` -/

/-- **The integer cutoff.**  The manuscript sets `h := C|log ε|`, which is not an
integer, while every occurrence of `k_{l-h}` needs an integer scale.  This is
the ceiling; the overshoot is a fixed factor, absorbed into the dimensional
constant below. -/
def waveCutoff (C0 eps : ℝ) : ℕ := ⌈C0 * |Real.log eps|⌉₊

/-- The ceiling overshoot, discharged: `3^{8h} ≤ 3^8 ε^{-8C₀log 3}`. -/
private theorem three_pow_eight_cutoff_le {C0 eps : ℝ} (hC0 : 0 < C0) (heps : 0 < eps)
    (heps1 : eps ≤ 1) :
    (3 : ℝ) ^ (8 * waveCutoff C0 eps) ≤
      6561 * eps ^ (-(8 * C0 * Real.log 3)) := by
  set L : ℝ := |Real.log eps| with hLdef
  have hlogneg : Real.log eps ≤ 0 := Real.log_nonpos heps.le heps1
  have hL : L = -Real.log eps := by rw [hLdef, abs_of_nonpos hlogneg]
  have hL0 : 0 ≤ L := abs_nonneg _
  have hprod : 0 ≤ C0 * L := mul_nonneg hC0.le hL0
  have hceil : ((waveCutoff C0 eps : ℕ) : ℝ) < C0 * L + 1 := by
    rw [waveCutoff, ← hLdef]
    exact Nat.ceil_lt_add_one hprod
  have hcast : (3 : ℝ) ^ (8 * waveCutoff C0 eps) =
      (3 : ℝ) ^ ((8 : ℝ) * ((waveCutoff C0 eps : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (3 : ℝ) (8 * waveCutoff C0 eps)]
    push_cast
    ring_nf
  have hmono : (3 : ℝ) ^ ((8 : ℝ) * ((waveCutoff C0 eps : ℕ) : ℝ)) ≤
      (3 : ℝ) ^ ((8 : ℝ) * (C0 * L + 1)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsplit : (3 : ℝ) ^ ((8 : ℝ) * (C0 * L + 1)) =
      (3 : ℝ) ^ (8 : ℝ) * (3 : ℝ) ^ (8 * C0 * L) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have h38 : (3 : ℝ) ^ (8 : ℝ) = 6561 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have heq : (3 : ℝ) ^ (8 * C0 * L) = eps ^ (-(8 * C0 * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos heps, hL]
    congr 1
    ring
  rw [hcast]
  refine hmono.trans (le_of_eq ?_)
  rw [hsplit, h38, heq]

/-- The per-cube derivative amplitude at the printed cutoff. -/
private theorem waveAmp_sq_cutoff_le (d : ℕ) {C0 eps : ℝ} (hC0 : 0 < C0)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    waveAmp d (waveCutoff C0 eps) ^ 2 ≤
      4 * IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 * 6561 *
        eps ^ (-(8 * C0 * Real.log 3)) := by
  set h : ℕ := waveCutoff C0 eps with hhdef
  have hnat : (h : ℕ) < 3 ^ h := Nat.lt_pow_self (by norm_num)
  have hhle : (h : ℝ) ≤ (3 : ℝ) ^ h := by
    have := (Nat.cast_le (α := ℝ)).2 hnat.le
    push_cast at this
    exact this
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have h3h : (0 : ℝ) < (3 : ℝ) ^ h := by positivity
  have hsq : (h : ℝ) ^ 2 ≤ (3 : ℝ) ^ (2 * h) := by
    have hpow : (3 : ℝ) ^ (2 * h) = ((3 : ℝ) ^ h) ^ 2 := by
      rw [pow_mul']
    rw [hpow]
    exact pow_le_pow_left₀ hh0 hhle 2
  have h4h : (3 : ℝ) ^ (4 * h) = (3 : ℝ) ^ (2 * h) * (3 : ℝ) ^ (2 * h) := by
    rw [← pow_add]
    ring_nf
  have h2h0 : (0 : ℝ) < (3 : ℝ) ^ (2 * h) := by positivity
  have h1le : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * h) := one_le_pow₀ (by norm_num)
  have hinner : (h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1 ≤ 2 * (3 : ℝ) ^ (4 * h) := by
    rw [h4h]
    have e1 : (h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) ≤ (3 : ℝ) ^ (2 * h) * (3 : ℝ) ^ (2 * h) :=
      mul_le_mul_of_nonneg_right hsq h2h0.le
    have e2 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * h) * (3 : ℝ) ^ (2 * h) :=
      h1le.trans (le_mul_of_one_le_right h2h0.le h1le)
    linarith only [e1, e2]
  have hinner0 : (0 : ℝ) ≤ (h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1 := by positivity
  have hsq2 : ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1) ^ 2 ≤ 4 * (3 : ℝ) ^ (8 * h) := by
    have h8h : (3 : ℝ) ^ (8 * h) = (3 : ℝ) ^ (4 * h) * (3 : ℝ) ^ (4 * h) := by
      rw [← pow_add]
      ring_nf
    rw [h8h]
    calc ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1) ^ 2
        ≤ (2 * (3 : ℝ) ^ (4 * h)) ^ 2 := pow_le_pow_left₀ hinner0 hinner 2
      _ = 4 * ((3 : ℝ) ^ (4 * h) * (3 : ℝ) ^ (4 * h)) := by ring
  have hcut := three_pow_eight_cutoff_le (C0 := C0) (eps := eps) hC0 heps heps1
  rw [← hhdef] at hcut
  have hgt : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hCd : (0 : ℝ) < shellW1InfConst d := shellW1InfConst_pos d
  have hexpand : waveAmp d h ^ 2 =
      IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 *
        ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1) ^ 2 := by
    rw [waveAmp]
    ring
  rw [hexpand]
  have hfac : (0 : ℝ) ≤ IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 := by
    positivity
  calc IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 *
        ((h : ℝ) ^ 2 * (3 : ℝ) ^ (2 * h) + 1) ^ 2
      ≤ IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 *
          (4 * (3 : ℝ) ^ (8 * h)) := mul_le_mul_of_nonneg_left hsq2 hfac
    _ ≤ IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 *
          (4 * (6561 * eps ^ (-(8 * C0 * Real.log 3)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hfac
        exact mul_le_mul_of_nonneg_left hcut (by norm_num)
    _ = 4 * IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 * 6561 *
          eps ^ (-(8 * C0 * Real.log 3)) := by ring

/-- The covering factor at the printed cutoff. -/
private theorem one_add_cutoff_sq_le {C0 eps : ℝ} (hC0 : 0 < C0) (heps : 0 < eps)
    (heps1 : eps ≤ 1) :
    (1 + ((waveCutoff C0 eps : ℕ) : ℝ)) ^ 2 ≤
      4 * 6561 * eps ^ (-(8 * C0 * Real.log 3)) := by
  set h : ℕ := waveCutoff C0 eps with hhdef
  have hnat : (h : ℕ) < 3 ^ h := Nat.lt_pow_self (by norm_num)
  have hhle : (h : ℝ) ≤ (3 : ℝ) ^ h := by
    have := (Nat.cast_le (α := ℝ)).2 hnat.le
    push_cast at this
    exact this
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ h := one_le_pow₀ (by norm_num)
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hsum : 1 + (h : ℝ) ≤ 2 * (3 : ℝ) ^ h := by linarith
  have h8h : (3 : ℝ) ^ (8 * h) = ((3 : ℝ) ^ h) ^ 2 * (3 : ℝ) ^ (6 * h) := by
    rw [← pow_mul', ← pow_add]
    ring_nf
  have h6h : (1 : ℝ) ≤ (3 : ℝ) ^ (6 * h) := one_le_pow₀ (by norm_num)
  have hsq : (1 + (h : ℝ)) ^ 2 ≤ 4 * (3 : ℝ) ^ (8 * h) := by
    have hstep : (1 + (h : ℝ)) ^ 2 ≤ 4 * ((3 : ℝ) ^ h) ^ 2 := by
      calc (1 + (h : ℝ)) ^ 2 ≤ (2 * (3 : ℝ) ^ h) ^ 2 :=
            pow_le_pow_left₀ (by linarith) hsum 2
        _ = 4 * ((3 : ℝ) ^ h) ^ 2 := by ring
    have hST : ((3 : ℝ) ^ h) ^ 2 ≤ ((3 : ℝ) ^ h) ^ 2 * (3 : ℝ) ^ (6 * h) :=
      le_mul_of_one_le_right (sq_nonneg _) h6h
    rw [h8h]
    linarith only [hstep, hST]
  have hcut := three_pow_eight_cutoff_le (C0 := C0) (eps := eps) hC0 heps heps1
  rw [← hhdef] at hcut
  calc (1 + (h : ℝ)) ^ 2 ≤ 4 * (3 : ℝ) ^ (8 * h) := hsq
    _ ≤ 4 * (6561 * eps ^ (-(8 * C0 * Real.log 3))) :=
        mul_le_mul_of_nonneg_left hcut (by norm_num)
    _ = 4 * 6561 * eps ^ (-(8 * C0 * Real.log 3)) := by ring

/-- The per-scale majorant at the printed cutoff. -/
private theorem waveKW2_cutoff_le (d : ℕ) {C0 eps : ℝ} (hC0 : 0 < C0)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    waveKW2 d (waveCutoff C0 eps) ≤
      waveGridConst d * (2 * IndependentSums.gammaTriangleConst 2 ^ 2) *
        (waveCoverConst d * (4 * 6561) * streamLinftyConst d ^ 2 +
          4 * IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 * 6561) *
        eps ^ (-(8 * C0 * Real.log 3)) := by
  set h : ℕ := waveCutoff C0 eps with hhdef
  set E : ℝ := eps ^ (-(8 * C0 * Real.log 3)) with hEdef
  have hE : (0 : ℝ) < E := by
    rw [hEdef]
    exact Real.rpow_pos_of_pos heps _
  have hcov := one_add_cutoff_sq_le (C0 := C0) (eps := eps) hC0 heps heps1
  rw [← hhdef, ← hEdef] at hcov
  have hamp := waveAmp_sq_cutoff_le d (C0 := C0) (eps := eps) hC0 heps heps1
  rw [← hhdef, ← hEdef] at hamp
  have hcovc : (0 : ℝ) ≤ waveCoverConst d := waveCoverConst_nonneg d
  have hsl : (0 : ℝ) ≤ streamLinftyConst d ^ 2 := sq_nonneg _
  have hgrid : (0 : ℝ) < waveGridConst d := waveGridConst_pos d
  have htri : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hfac : (0 : ℝ) ≤ waveGridConst d * (2 * IndependentSums.gammaTriangleConst 2 ^ 2) := by
    positivity
  have hinner : waveCoverConst d * (1 + (h : ℝ)) ^ 2 * streamLinftyConst d ^ 2 +
      waveAmp d h ^ 2 ≤
      (waveCoverConst d * (4 * 6561) * streamLinftyConst d ^ 2 +
        4 * IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 * 6561) * E := by
    have h1 : waveCoverConst d * (1 + (h : ℝ)) ^ 2 * streamLinftyConst d ^ 2 ≤
        waveCoverConst d * (4 * 6561) * streamLinftyConst d ^ 2 * E := by
      calc waveCoverConst d * (1 + (h : ℝ)) ^ 2 * streamLinftyConst d ^ 2
          = waveCoverConst d * streamLinftyConst d ^ 2 * (1 + (h : ℝ)) ^ 2 := by ring
        _ ≤ waveCoverConst d * streamLinftyConst d ^ 2 * (4 * 6561 * E) :=
            mul_le_mul_of_nonneg_left hcov (mul_nonneg hcovc hsl)
        _ = waveCoverConst d * (4 * 6561) * streamLinftyConst d ^ 2 * E := by ring
    linarith only [h1, hamp]
  rw [waveKW2]
  calc waveGridConst d * (2 * IndependentSums.gammaTriangleConst 2 ^ 2) *
        (waveCoverConst d * (1 + (h : ℝ)) ^ 2 * streamLinftyConst d ^ 2 + waveAmp d h ^ 2)
      ≤ waveGridConst d * (2 * IndependentSums.gammaTriangleConst 2 ^ 2) *
          ((waveCoverConst d * (4 * 6561) * streamLinftyConst d ^ 2 +
            4 * IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 * 6561) * E) :=
        mul_le_mul_of_nonneg_left hinner hfac
    _ = waveGridConst d * (2 * IndependentSums.gammaTriangleConst 2 ^ 2) *
          (waveCoverConst d * (4 * 6561) * streamLinftyConst d ^ 2 +
            4 * IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 * 6561) *
          E := by ring

/-- **`e.wave.sizes` in the printed form, at the extended `W^{2,∞}` carrier.**
For every cutoff coefficient `C₀ > 0` there is a constant `C`, depending only on
the dimension and `C₀`, with

`s Σ_{l ≤ m} 3^{-s(m-l)}
   (⨍_{z ∈ 3^l Z^d ∩ cu_m} (3^{(2-γ)l}‖k_m-k_{l-h}‖_{W^{2,∞}(z+cu_l)})^{2d/s})^{s/d}
     ≤ O_{Γ₁}(C s^{-2} ε^{-C})`

at the integer cutoff `h = ⌈C₀|log ε|⌉`, for every `ε ∈ (0,1]` and every `s ∈
[8γ, 1]`.  The left-hand side carries the **full** three-order object, not
merely its derivative half. -/
theorem wave_sizes_bound (d : ℕ) {C0 : ℝ} (hC0 : 0 < C0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m : ℤ) (eps s : ℝ), 0 < eps → eps ≤ 1 → 0 < s → s ≤ 1 →
        8 * M.gamma ≤ s →
          IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 1)
            (fun omega : ShellSeq d =>
              waveSizesTotalW2 M m (waveCutoff C0 eps) s omega)
            (C * eps ^ (-C) / s ^ 2) := by
  set B : ℝ := waveSizesConstW2 *
    (waveGridConst d * (2 * IndependentSums.gammaTriangleConst 2 ^ 2) *
      (waveCoverConst d * (4 * 6561) * streamLinftyConst d ^ 2 +
        4 * IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 * 6561))
    with hBdef
  have hBpos : 0 < B := by
    have h1 : (0 : ℝ) < waveSizesConstW2 := waveSizesConstW2_pos
    have h2 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos
    have h3 : (0 : ℝ) < shellW1InfConst d := shellW1InfConst_pos d
    have h4 : (0 : ℝ) < waveGridConst d := waveGridConst_pos d
    have h5 : (0 : ℝ) ≤ waveCoverConst d := waveCoverConst_nonneg d
    have h6 : (0 : ℝ) ≤ streamLinftyConst d ^ 2 := sq_nonneg _
    have h7 : (0 : ℝ) < waveCoverConst d * (4 * 6561) * streamLinftyConst d ^ 2 +
        4 * IndependentSums.gammaTriangleConst 2 ^ 2 * shellW1InfConst d ^ 2 * 6561 := by
      have h8 : (0 : ℝ) ≤ waveCoverConst d * (4 * 6561) * streamLinftyConst d ^ 2 := by
        positivity
      have h9 : (0 : ℝ) < 4 * IndependentSums.gammaTriangleConst 2 ^ 2 *
          shellW1InfConst d ^ 2 * 6561 := by positivity
      linarith
    rw [hBdef]
    positivity
  refine ⟨max B (8 * C0 * Real.log 3), lt_of_lt_of_le hBpos (le_max_left _ _), ?_⟩
  intro M m eps s heps heps1 hs hs1 hsg
  refine (isBigOWith_gammaSigma_waveSizesTotalW2 M m (waveCutoff C0 eps)
    hs hs1 hsg).mono_scale ?_
  have hK := waveKW2_cutoff_le d (C0 := C0) (eps := eps) hC0 heps heps1
  have hCpos : (0 : ℝ) < waveSizesConstW2 := waveSizesConstW2_pos
  have hstep : waveSizesConstW2 * waveKW2 d (waveCutoff C0 eps) ≤
      B * eps ^ (-(8 * C0 * Real.log 3)) := by
    rw [hBdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left hK hCpos.le
  have hexp : eps ^ (-(8 * C0 * Real.log 3)) ≤ eps ^ (-max B (8 * C0 * Real.log 3)) := by
    refine Real.rpow_le_rpow_of_exponent_ge heps heps1 ?_
    have := le_max_right B (8 * C0 * Real.log 3)
    linarith
  have hepos : (0 : ℝ) < eps ^ (-max B (8 * C0 * Real.log 3)) :=
    Real.rpow_pos_of_pos heps _
  have hnum : waveSizesConstW2 * waveKW2 d (waveCutoff C0 eps) ≤
      max B (8 * C0 * Real.log 3) * eps ^ (-max B (8 * C0 * Real.log 3)) := by
    refine hstep.trans ?_
    calc B * eps ^ (-(8 * C0 * Real.log 3))
        ≤ B * eps ^ (-max B (8 * C0 * Real.log 3)) :=
          mul_le_mul_of_nonneg_left hexp hBpos.le
      _ ≤ max B (8 * C0 * Real.log 3) * eps ^ (-max B (8 * C0 * Real.log 3)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hepos.le
  exact div_le_div_of_nonneg_right hnum (by positivity) |>.trans (le_refl _)

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
