/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveOscillations
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpLarge

/-!
# WaveThirdTerm

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `e.wave.influence.bound`, the printed **three**-term right-hand side

This module re-bases the lower leg of the node
`p.bfA.multiscalebound`, the wave-oscillations step (ABK26, proof of Proposition
`p.bfA.multiscalebound`, Step 2) onto the manuscript's own cube-averaged
`L⁴(cu_{n-k})` amplitude, and thereby splits the merged leg
`Provider.Multiscale.waveLowerTerm` into the display's printed **first** and
**third** terms.  The printed display reads

```
  c gamma^{1/2} 3^{-gamma(n-k-h_k)} ||k_L - k_{n-k-h_k}||_{L^4bar(cu_{n-k})}
     <= gamma^{1/2} hsep^{1/2} + O_{Gamma_2}(gamma^{1/2}(L-l)^{1/2} 3^{gamma(L-l)})
        + O_{Gamma_{2(1+sigma)^{-1}}}(sigma^{-1} 3^{-(d/8)k_0}) ,
```

with `l = n - k - h_k + hsep = n - k - ceil(b(1-b)^{-1}k) - k_0` deterministic;
the parameters are named `ell = l` and `lout = n - k` here, so `lout - ell =
ceil(b(1-b)^{-1}k) + k_0` is exactly the manuscript's gain exponent, and in
particular `lout - ell >= k_0`.

## The partial reversal, and why it is needed

`Provider/Multiscale/WaveOscillations.lean` provides the display in the merged
two-leg form, at the **uniform** (`L^infinity`) per-layer gauge of
`e.km.kn.Linfty`, and its section "Divergences from the printed right-hand
side, recorded honestly" (its paragraph) records the reason the merged first
and third terms cannot be split there: **no uniform gauge can carry the
`3^{-(d/8)k_0}` gain.**  That gain is a cube-**averaging** phenomenon, and a
bound on the supremum of a stationary nondegenerate field over a growing cube
cannot decay in the cube size (the proved `e.km.kn.Linfty` amplitude in fact G
like `(lout-ell+i)^{1/2}`).  Splitting the third term therefore requires
**reinstating the manuscript's `L⁴` Minkowski step for the lower leg** — a
partial reversal of form choice, for the lower leg only.

This module performs that reversal and nothing more:

* `streamIncrementLpNorm_add_le` is the reinstated `L⁴(cu_lout)` triangle
  inequality, proved from Mathlib's `ENNReal.lintegral_Lp_add_le` at the
  volume-normalized cube average.  It is used exactly once, to split `k_L -
  k_{ell-hsep}` at the scale `ell`, which is the manuscript's own first
  display.
* The **upper** leg is not touched here.  It keeps the local uniform
  formulation, where the passage to the large-cube amplitude costs constant `1`
  (`Stream.streamIncrementLinftyNorm_le_largeCubeSupBound`; `|.|` is the matrix
  operator norm, so a supremum of a pointwise-dominated quantity is dominated
  with constant `1`).  The form choice is therefore reversed for the lower leg
  and retained for the upper one.
* The **lower** leg is priced by the proved unconditional `e.km.kn.Lp`
  (`Provider.Stream.streamIncrementLpNorm_head_tail_gain`) at `p = 4`, applied
  — as the manuscript does — to the **whole** lower increment `k_ell -
  k_{ell-h}` at each depth `h`, not per layer.  Its deterministic head is `C(d)
  min{gamma^{-1/2}, h^{1/2}} 3^{gamma ell}` (`waveL4Head_eq`), which after the
  prefactor is the display's first term; its `Gamma_2` part carries the gain
  `3^{-(d/(2p))(lout-ell)} = 3^{-(d/8)(lout-ell)}` (`waveL4TailScale_eq`),
  which is the display's third term.

## The assembly, and why the proved truncated-sum core suffices

The manuscript assembles over `1_{{hsep = h}}`; this repository assembles over
`1_{{i < hsep}}`, and the proved
`WaveOscillationsCore.isBigOWith_gammaSigma_truncatedSum` is exactly that
assembly.  No head+tail variant of it is needed, because of one elementary
observation: writing `X_h` for the nonnegative `Gamma_2` part at depth `h`,

```
  X_{hsep}  <=  sum_{i < hsep} X_{i+1}                (waveL4Tail_le_range_sum)
```

— for `hsep = H >= 1` the term `i = H-1` of the right-hand sum *is* `X_H`, and
for `hsep = 0` both sides vanish because the empty increment has zero mass.
The **deterministic head needs no summation at all**: it is evaluated at the
single random depth `hsep`, which is what produces the printed `hsep^{1/2}`
(summing per-layer heads would have produced the weaker `hsep`).  The shift by
one keeps every summand at a strictly positive depth, where `e.km.kn.Lp`'s own
binder `n < m` holds; that is why the proved core's `0 < a i` is available.

## Divergences from the printed right-hand side, recorded honestly

* The printed first term is the bare `gamma^{1/2} hsep^{1/2}`; the local one is
  `C(d) gamma^{1/2} hsep^{1/2}` with the explicit dimensional constant
  `waveL4HeadConst d`, which is what the manuscript's own proof produces
  (`C 3^{gamma ell} hsep^{1/2}`).  With the left-hand constant `c` taken to be `1`
  (the manuscript does not pin `c`), the constant has to appear somewhere; it
  appears here.  Class `[C]`.
* The printed third term is `sigma^{-1} 3^{-(d/8)k_0}`; the local scale
  `waveTailGainScale` is `C(d, sigma_2) * (sum_i indicator scale) *
  3^{-(d/8)(lout-ell)}`, where the indicator series is the manuscript's own `C
  b^{-1} sigma^{-1}` factor at `t = 1/sigma_2` and the gain is the manuscript's
  own exponent.  Class `[C]`.
* The Orlicz exponent of the lower leg is kept free, exactly as in the proved
  `WaveOscillations.lean`: `e.indc.O.sigma` is applied at a general `sigma_2 >
  0`, and at the manuscript's `t = sigma/2`, i.e. `sigma_2 = 2/sigma`, the
  delivered index `2 sigma_2/(2 + sigma_2)` is the printed `2(1+sigma)^{-1}` on
  the nose.

## Main definitions

* `waveL4Head`, `waveL4Tail`, `waveL4TailScale`, `waveL4HeadConst`: the `p = 4`
  head/tail carriers of `e.km.kn.Lp` at the lower increment.
* `waveHeadTerm`, `waveTailTerm`: the printed first and third terms.
* `waveTailScale`, `waveTailGainScale`: the third term's sharp series and its
  gain-factored dominator.

## Main results

* `streamIncrementLpNorm_add_le`: the reinstated `L⁴` Minkowski step.
* `measurable_streamIncrementLpMass`: the cube mass is a random variable.
* `waveL4Head_eq`, `waveL4TailScale_eq`: the closed forms of the head and of the
  gain.
* `waveHeadTerm_le`: the printed `C(d) gamma^{1/2} hsep^{1/2}`.
* `waveTailScale_le_waveTailGainScale`: the printed `3^{-(d/8)k_0}` decay.
* `isBigOWith_gammaSigma_waveTailTerm_of_gates`: the third term's Orlicz bound,
  in the premise-minimal form that reads the bad-event gates directly.

## References

* ABK26, proof of `p.bfA.multiscalebound`, Step 2, (first display, indicator
  display, `e.km.kn.Lp` application, assembly).
* ABK26, `e.km.kn.Lp`; `e.kl.bounds.large`; `e.kmn.bounds`;
  `e.km.kn.Linfty`; `e.indc.O.sigma`; `e.multGammasig`;
  `l.Gamma.sigma.triangle`; `e.hsep.tails`.
* `Provider/Multiscale/WaveOscillations.lean` (the merged two-leg display and
  its section "Divergences from the printed right-hand side, recorded honestly"
  (its paragraph)), `Provider/Multiscale/WaveOscillationsCore.lean` (the
  truncated-sum assembly), `Provider/Stream/IncrementLpLarge.lean` (the
  unconditional corrected `e.km.kn.Lp`).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## Deterministic preliminaries on the layer split -/

private theorem finiteShellIncrement_add_split (omega : ShellSeq d) {a b c : ℤ}
    (hab : a ≤ b) (hbc : b ≤ c) (x : Vec d) :
    finiteShellIncrement omega a c x =
      finiteShellIncrement omega a b x + finiteShellIncrement omega b c x := by
  have hdisj : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
    refine Finset.disjoint_left.2 fun k hk hk' => ?_
    rw [Finset.mem_Ioc] at hk hk'
    omega
  rw [finiteShellIncrement_apply, finiteShellIncrement_apply, finiteShellIncrement_apply,
    ← Finset.Ioc_union_Ioc_eq_Ioc hab hbc, Finset.sum_union hdisj]

private theorem matrixOperatorNorm_add_le_add (A B : Mat d) :
    matrixOperatorNorm (A + B) ≤ matrixOperatorNorm A + matrixOperatorNorm B := by
  have h := matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub (A + B) A
  simpa using h

private theorem rpow_inv_two_eq_sqrt (x : ℝ) : x ^ ((2 : ℝ)⁻¹) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  norm_num

private theorem continuous_matrixOperatorNorm_finiteShellIncrement (omega : ShellSeq d)
    (n m : ℤ) :
    Continuous fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega n m x) := by
  have h := continuous_streamIncrementLpDensity (d := d) (p := 1) one_pos n m omega
  have hfun : streamIncrementLpDensity (1 : ℝ) n m omega =
      fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega n m x) := by
    funext x
    rw [streamIncrementLpDensity, Real.rpow_one]
  rwa [hfun] at h

/-! ## Minkowski's inequality for the cube `L^p` norm

The step reinstated by the partial reversal of form choice: the manuscript's
own `L⁴(cu_{n-k})` triangle inequality. -/

private theorem lintegral_ofReal_streamIncrementLpDensity {p : ℝ} (hp : 0 < p) (l n m : ℤ)
    (omega : ShellSeq d) :
    ∫⁻ x in openCubeSet (originCube d l),
        ENNReal.ofReal (matrixOperatorNorm (finiteShellIncrement omega n m x)) ^ p =
      ENNReal.ofReal (∫ x in openCubeSet (originCube d l),
        streamIncrementLpDensity p n m omega x) := by
  have hpt : ∀ x : Vec d,
      ENNReal.ofReal (matrixOperatorNorm (finiteShellIncrement omega n m x)) ^ p =
        ENNReal.ofReal (streamIncrementLpDensity p n m omega x) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (matrixOperatorNorm_nonneg _) hp.le]
    rfl
  rw [lintegral_congr fun x => hpt x]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_streamIncrementLpDensity hp l n m omega)
    (Filter.Eventually.of_forall fun x => streamIncrementLpDensity_nonneg p n m omega x)).symm

/-- The Minkowski inequality on the origin cube, at the level of the
unnormalized `L^p` energies. -/
private theorem integral_streamIncrementLpDensity_rpow_inv_add_le {p : ℝ} (hp : 1 ≤ p)
    (l : ℤ) (omega : ShellSeq d) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ x in openCubeSet (originCube d l), streamIncrementLpDensity p a c omega x) ^ p⁻¹ ≤
      (∫ x in openCubeSet (originCube d l), streamIncrementLpDensity p a b omega x) ^ p⁻¹ +
        (∫ x in openCubeSet (originCube d l),
          streamIncrementLpDensity p b c omega x) ^ p⁻¹ := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set S : Set (Vec d) := openCubeSet (originCube d l) with hS
  set F : Vec d → ENNReal := fun x =>
    ENNReal.ofReal (matrixOperatorNorm (finiteShellIncrement omega a b x)) with hF
  set G : Vec d → ENNReal := fun x =>
    ENNReal.ofReal (matrixOperatorNorm (finiteShellIncrement omega b c x)) with hG
  have hFm : AEMeasurable F (volume.restrict S) :=
    (ENNReal.measurable_ofReal.comp
      (continuous_matrixOperatorNorm_finiteShellIncrement omega a b).measurable).aemeasurable
  have hGm : AEMeasurable G (volume.restrict S) :=
    (ENNReal.measurable_ofReal.comp
      (continuous_matrixOperatorNorm_finiteShellIncrement omega b c).measurable).aemeasurable
  have hdom : ∀ x : Vec d,
      ENNReal.ofReal (matrixOperatorNorm (finiteShellIncrement omega a c x)) ≤ (F + G) x := by
    intro x
    have hpt : matrixOperatorNorm (finiteShellIncrement omega a c x) ≤
        matrixOperatorNorm (finiteShellIncrement omega a b x) +
          matrixOperatorNorm (finiteShellIncrement omega b c x) := by
      rw [finiteShellIncrement_add_split omega hab hbc x]
      exact matrixOperatorNorm_add_le_add _ _
    calc ENNReal.ofReal (matrixOperatorNorm (finiteShellIncrement omega a c x))
        ≤ ENNReal.ofReal (matrixOperatorNorm (finiteShellIncrement omega a b x) +
            matrixOperatorNorm (finiteShellIncrement omega b c x)) :=
          ENNReal.ofReal_le_ofReal hpt
      _ = (F + G) x := by
          rw [ENNReal.ofReal_add (matrixOperatorNorm_nonneg _) (matrixOperatorNorm_nonneg _)]
          rfl
  have hmono : ∫⁻ x in S,
        ENNReal.ofReal (matrixOperatorNorm (finiteShellIncrement omega a c x)) ^ p ≤
      ∫⁻ x in S, (F + G) x ^ p :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (hdom x) hp0.le
  have hkey := ENNReal.lintegral_Lp_add_le (μ := volume.restrict S) hFm hGm hp
  have hchain : (ENNReal.ofReal (∫ x in S, streamIncrementLpDensity p a c omega x)) ^ (1 / p) ≤
      (ENNReal.ofReal (∫ x in S, streamIncrementLpDensity p a b omega x)) ^ (1 / p) +
        (ENNReal.ofReal (∫ x in S, streamIncrementLpDensity p b c omega x)) ^ (1 / p) := by
    rw [← lintegral_ofReal_streamIncrementLpDensity hp0 l a c omega,
      ← lintegral_ofReal_streamIncrementLpDensity hp0 l a b omega,
      ← lintegral_ofReal_streamIncrementLpDensity hp0 l b c omega]
    exact le_trans (ENNReal.rpow_le_rpow hmono (by positivity)) hkey
  have hnn : ∀ n m : ℤ, (0 : ℝ) ≤ ∫ x in S, streamIncrementLpDensity p n m omega x :=
    fun n m => setIntegral_nonneg (isOpen_openCubeSet _).measurableSet
      fun x _ => streamIncrementLpDensity_nonneg p n m omega x
  rw [ENNReal.ofReal_rpow_of_nonneg (hnn a c) (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (hnn a b) (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (hnn b c) (by positivity),
    ← ENNReal.ofReal_add (Real.rpow_nonneg (hnn a b) _) (Real.rpow_nonneg (hnn b c) _),
    ENNReal.ofReal_le_ofReal_iff
      (add_nonneg (Real.rpow_nonneg (hnn a b) _) (Real.rpow_nonneg (hnn b c) _))] at hchain
  simpa only [one_div] using hchain

/-- **Minkowski's inequality for the volume-normalized `L^p` norm on the origin
cube.**  This is the manuscript's own `L⁴(cu_{n-k})` triangle inequality,
reinstated by the partial reversal. -/
theorem streamIncrementLpNorm_add_le {p : ℝ} (hp : 1 ≤ p) (l : ℤ) {a b c : ℤ}
    (hab : a ≤ b) (hbc : b ≤ c) (omega : ShellSeq d) :
    streamIncrementLpNorm p l a c omega ≤
      streamIncrementLpNorm p l a b omega + streamIncrementLpNorm p l b c omega := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hV : (0 : ℝ) < (volume (openCubeSet (originCube d l))).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d l)
  have hnn : ∀ n m : ℤ, (0 : ℝ) ≤
      ∫ x in openCubeSet (originCube d l), streamIncrementLpDensity p n m omega x :=
    fun n m => setIntegral_nonneg (isOpen_openCubeSet _).measurableSet
      fun x _ => streamIncrementLpDensity_nonneg p n m omega x
  have hmass : ∀ n m : ℤ, streamIncrementLpNorm p l n m omega =
      ((volume (openCubeSet (originCube d l))).toReal⁻¹) ^ p⁻¹ *
        (∫ x in openCubeSet (originCube d l),
          streamIncrementLpDensity p n m omega x) ^ p⁻¹ := by
    intro n m
    rw [streamIncrementLpNorm, streamIncrementLpMass, Book.Ch02.average,
      Book.Ch02.cubeDomain_coe, Real.mul_rpow (by positivity) (hnn n m)]
  have hc : (0 : ℝ) ≤ ((volume (openCubeSet (originCube d l))).toReal⁻¹) ^ p⁻¹ := by
    positivity
  rw [hmass a c, hmass a b, hmass b c, ← mul_add]
  exact mul_le_mul_of_nonneg_left
    (integral_streamIncrementLpDensity_rpow_inv_add_le hp l omega hab hbc) hc

/-! ## The `L^p ≤ L^∞` passage on the observation cube -/


/-! ## Measurability of the cube mass in the sample

The bookkeeping demands measurable summands.  At the uniform gauge that was
automatic; the re-based leg needs the cube mass itself to be a random variable,
which is Fubini--Tonelli applied to the jointly measurable density. -/

/-- The volume-normalized cube `L^p` mass is a random variable. -/
theorem measurable_streamIncrementLpMass {p : ℝ} (hp : 0 < p) (l n m : ℤ) :
    Measurable (streamIncrementLpMass (d := d) p l n m) :=
  Algsuperdiff.Section3.Provider.Stream.measurable_streamIncrementLpMass hp l n m

/-! ## The empty increment -/

private theorem streamIncrementLpMass_self {p : ℝ} (hp : 0 < p) (l n : ℤ)
    (omega : ShellSeq d) : streamIncrementLpMass p l n n omega = 0 := by
  have hdens : streamIncrementLpDensity p n n omega = fun _ : Vec d => (0 : ℝ) := by
    funext x
    rw [streamIncrementLpDensity, finiteShellIncrement_apply]
    simp only [Finset.Ioc_self, Finset.sum_empty, matrixOperatorNorm_zero]
    exact Real.zero_rpow (ne_of_gt hp)
  rw [streamIncrementLpMass, hdens, Book.Ch02.average]
  simp

private theorem streamIncrementLpNorm_self {p : ℝ} (hp : 0 < p) (l n : ℤ)
    (omega : ShellSeq d) : streamIncrementLpNorm p l n n omega = 0 := by
  rw [streamIncrementLpNorm, streamIncrementLpMass_self hp l n omega,
    Real.zero_rpow (inv_ne_zero (ne_of_gt hp))]

private theorem streamIncrementLpTail_self (M : ABKModel d) {p : ℝ} (hp : 0 < p) (l n : ℤ)
    (omega : ShellSeq d) : streamIncrementLpTail M p l n n omega = 0 := by
  have hz : ∀ (l' : ℤ) (w : ShellSeq d), streamIncrementLpMass p l' n n w = 0 :=
    fun l' w => streamIncrementLpMass_self hp l' n w
  rw [streamIncrementLpTail]
  split
  · have hint : (∫ w, streamIncrementLpMass p (n + (incrementPartitionShift d : ℤ)) n n w
        ∂M.P.toMeasure) = 0 := by
      simp only [hz]
      exact integral_zero _ _
    rw [hz l omega, hint]
    simp
  · exact hz l omega

/-! ## The `p = 4` carriers of the re-based lower leg

The manuscript's own amplitude is the cube-averaged `L⁴(cu_{n-k})` norm of the
increment, i.e. `streamIncrementLpNorm 4 lout` at the observation cube. -/

/-- The deterministic head of `e.km.kn.Lp` at `p = 4`, at the lower increment
`k_ell - k_{ell-h}` (: `C h^{1/2} 3^{gamma ell}`). -/
def waveL4Head (M : ABKModel d) (ell : ℤ) (h : ℕ) : ℝ :=
  streamIncrementLpMassHead M 4 (ell - (h : ℤ)) ell ^ ((4 : ℝ)⁻¹)

/-- The random part of `e.km.kn.Lp` at `p = 4`, at the lower increment. -/
def waveL4Tail (M : ABKModel d) (lout ell : ℤ) (h : ℕ) (omega : CutoffSample d) : ℝ :=
  streamIncrementLpTail M 4 lout (ell - (h : ℤ)) ell omega.1 ^ ((4 : ℝ)⁻¹)

/-- The `Gamma_2` scale of the random part: the `p = 4` root of the mass-level
gain, i.e. the printed `C gamma^{-1/2} 3^{gamma ell} 3^{-(d/8)(lout-ell)}`. -/
def waveL4TailScale (M : ABKModel d) (lout ell : ℤ) (h : ℕ) : ℝ :=
  streamIncrementLpGainScale M 4 lout (ell - (h : ℤ)) ell ^ ((4 : ℝ)⁻¹)

/-- The dimensional constant of the deterministic head at `p = 4`. -/
def waveL4HeadConst (d : ℕ) : ℝ :=
  2 * IndependentSums.gammaMomentConst 2 * IndependentSums.gammaTriangleConst 2 *
    (d : ℝ) ^ 2 * geometricConcentrationConst

theorem waveL4HeadConst_nonneg (d : ℕ) : 0 ≤ waveL4HeadConst d := by
  rw [waveL4HeadConst]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (IndependentSums.gammaMomentConst_pos (by norm_num)).le)
    IndependentSums.gammaTriangleConst_pos.le) (by positivity))
    geometricConcentrationConst_pos.le

private theorem streamPointScale_nonneg_local (M : ABKModel d) (n m : ℤ) :
    0 ≤ streamPointScale M n m := by
  have hmin : (0 : ℝ) ≤ min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [streamPointScale]
  exact mul_nonneg IndependentSums.gammaTriangleConst_pos.le
    (mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg geometricConcentrationConst_pos.le hmin)
        (Real.rpow_nonneg (by norm_num) _)))

private theorem streamIncrementLpMassHead_nonneg (M : ABKModel d) {p : ℝ} (hp : 0 ≤ p)
    (n m : ℤ) : 0 ≤ streamIncrementLpMassHead M p n m :=
  Real.rpow_nonneg (mul_nonneg (mul_nonneg
    (IndependentSums.gammaMomentConst_pos (by norm_num)).le
    (streamPointScale_nonneg_local M n m)) (Real.rpow_nonneg hp _)) _

theorem waveL4Head_nonneg (M : ABKModel d) (ell : ℤ) (h : ℕ) : 0 ≤ waveL4Head M ell h :=
  Real.rpow_nonneg (streamIncrementLpMassHead_nonneg M (by norm_num) _ _) _

theorem waveL4Tail_nonneg (M : ABKModel d) (lout ell : ℤ) (h : ℕ)
    (omega : CutoffSample d) : 0 ≤ waveL4Tail M lout ell h omega :=
  Real.rpow_nonneg (streamIncrementLpTail_nonneg M 4 lout _ ell omega.1) _

theorem waveL4Tail_zero (M : ABKModel d) (lout ell : ℤ) (omega : CutoffSample d) :
    waveL4Tail M lout ell 0 omega = 0 := by
  rw [waveL4Tail]
  simp only [Nat.cast_zero, sub_zero]
  rw [streamIncrementLpTail_self M (by norm_num : (0 : ℝ) < 4) lout ell omega.1,
    Real.zero_rpow (by norm_num : ((4 : ℝ)⁻¹) ≠ 0)]

theorem waveL4TailScale_pos (M : ABKModel d) (lout ell : ℤ) (i : ℕ) :
    0 < waveL4TailScale M lout ell (i + 1) := by
  have hnm : ell - ((i + 1 : ℕ) : ℤ) < ell := by push_cast; omega
  exact Real.rpow_pos_of_pos
    (streamIncrementLpGainScale_pos M (by norm_num : (1 : ℝ) ≤ 4) hnm lout) _

private theorem rpow_four_rpow_inv_four {A : ℝ} (hA : 0 ≤ A) :
    (A ^ (4 : ℝ)) ^ ((4 : ℝ)⁻¹) = A := by
  rw [← Real.rpow_mul hA, show (4 : ℝ) * (4 : ℝ)⁻¹ = 1 by norm_num, Real.rpow_one]

/-- **The closed form of the deterministic head at `p = 4`**: the manuscript's `C
min{gamma^{-1/2}, h^{1/2}} 3^{gamma ell}`. -/
theorem waveL4Head_eq (M : ABKModel d) (ell : ℤ) (h : ℕ) :
    waveL4Head M ell h =
      waveL4HeadConst d * min (Real.sqrt M.gamma⁻¹) (Real.sqrt (h : ℝ)) *
        (3 : ℝ) ^ (M.gamma * (ell : ℝ)) := by
  have hA : (0 : ℝ) ≤ IndependentSums.gammaMomentConst 2 *
      streamPointScale M (ell - (h : ℤ)) ell * (4 : ℝ) ^ ((2 : ℝ)⁻¹) :=
    mul_nonneg (mul_nonneg (IndependentSums.gammaMomentConst_pos (by norm_num)).le
      (streamPointScale_nonneg_local M _ _)) (Real.rpow_nonneg (by norm_num) _)
  have h4 : (4 : ℝ) ^ ((2 : ℝ)⁻¹) = 2 := by
    rw [rpow_inv_two_eq_sqrt, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hcast : (ell : ℝ) - ((ell - (h : ℤ) : ℤ) : ℝ) = (h : ℝ) := by push_cast; ring
  rw [waveL4Head, streamIncrementLpMassHead, rpow_four_rpow_inv_four hA, h4,
    streamPointScale, hcast, waveL4HeadConst]
  ring

/-- **The closed form of the `Gamma_2` scale at `p = 4`**: the head times the
printed large-scale gain `3^{-(d/8)(lout-ell)}` (at `lout - ell = b(1-b)^{-1}k
+ k_0`). -/
theorem waveL4TailScale_eq (M : ABKModel d) (lout ell : ℤ) (h : ℕ) :
    waveL4TailScale M lout ell h =
      streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
        (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) * waveL4Head M ell h := by
  have hG : (0 : ℝ) ≤ streamIncrementLpGainConst d (2 / 4) :=
    (streamIncrementLpGainConst_pos d _).le
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) / 2) * ((lout : ℝ) - (ell : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hH : (0 : ℝ) ≤ streamIncrementLpMassHead M 4 (ell - (h : ℤ)) ell :=
    streamIncrementLpMassHead_nonneg M (by norm_num) _ _
  have hexp : -((d : ℝ) / 2) * ((lout : ℝ) - (ell : ℝ)) * (4 : ℝ)⁻¹ =
      -((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ)) := by ring
  rw [waveL4TailScale, waveL4Head, streamIncrementLpGainScale,
    Real.mul_rpow (mul_nonneg hG h3) hH, Real.mul_rpow hG h3,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hexp]

/-- The head and tail at `p = 4` dominate the manuscript's `L⁴` amplitude of the
lower increment. -/
theorem streamIncrementLpNorm_le_waveL4Head_add_waveL4Tail (M : ABKModel d)
    (lout ell : ℤ) (h : ℕ) (omega : CutoffSample d) :
    streamIncrementLpNorm 4 lout (ell - (h : ℤ)) ell omega.1 ≤
      waveL4Head M ell h + waveL4Tail M lout ell h omega := by
  rcases Nat.eq_zero_or_pos h with hzero | hpos
  · subst hzero
    simp only [Nat.cast_zero, sub_zero]
    rw [streamIncrementLpNorm_self (by norm_num : (0 : ℝ) < 4) lout ell omega.1]
    exact add_nonneg (waveL4Head_nonneg M ell 0) (waveL4Tail_nonneg M lout ell 0 omega)
  · have hnm : ell - (h : ℤ) < ell := by
      have h1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hpos
      omega
    exact (streamIncrementLpNorm_head_tail_gain M (by norm_num : (1 : ℝ) ≤ 4) hnm lout).1 omega.1

theorem measurable_waveL4Tail (M : ABKModel d) (lout ell : ℤ) (h : ℕ) :
    Measurable (waveL4Tail M lout ell h) := by
  have hmass := measurable_streamIncrementLpMass (d := d) (p := 4) (by norm_num)
    lout (ell - (h : ℤ)) ell
  have hm : Measurable (streamIncrementLpTail M 4 lout (ell - (h : ℤ)) ell) := by
    by_cases hsl : ell + (incrementPartitionShift d : ℤ) ≤ lout
    · have hfun : streamIncrementLpTail M 4 lout (ell - (h : ℤ)) ell =
          fun w : ShellSeq d =>
            |streamIncrementLpMass 4 lout (ell - (h : ℤ)) ell w -
              ∫ w', streamIncrementLpMass 4 (ell + (incrementPartitionShift d : ℤ))
                (ell - (h : ℤ)) ell w' ∂M.P.toMeasure| := by
        funext w
        rw [streamIncrementLpTail, ite_eq_left hsl]
      rw [hfun]
      exact (hmass.sub measurable_const).abs
    · have hfun : streamIncrementLpTail M 4 lout (ell - (h : ℤ)) ell =
          streamIncrementLpMass 4 lout (ell - (h : ℤ)) ell := by
        funext w
        rw [streamIncrementLpTail, ite_eq_right hsl]
      rw [hfun]
      exact hmass
  exact ((hm.comp measurable_subtype_coe).pow_const ((4 : ℝ)⁻¹))

theorem isBigOWith_gammaSigma_waveL4Tail (M : ABKModel d) (lout ell : ℤ) (i : ℕ) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2)
      (waveL4Tail M lout ell (i + 1)) (waveL4TailScale M lout ell (i + 1)) := by
  have hnm : ell - ((i + 1 : ℕ) : ℤ) < ell := by push_cast; omega
  exact isBigOWith_cutoffSampleLaw_comp_val
    (streamIncrementLpNorm_head_tail_gain M (by norm_num : (1 : ℝ) ≤ 4) hnm lout).2

/-! ## Summability of the re-based tail series -/

private theorem summable_truncationIndicatorScale {b sigma sigma2 K : ℝ}
    (hb : 0 < b) (hsigma2 : 0 < sigma2) (hsigma : 0 < 1 - sigma) (hK : 0 < K) :
    Summable fun i : ℕ => truncationIndicatorScale b sigma sigma2 K i := by
  have hq : 0 < (1 - sigma) / sigma2 := div_pos hsigma hsigma2
  have hbq : 0 < b * ((1 - sigma) / sigma2) := mul_pos hb hq
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-(b * ((1 - sigma) / sigma2))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(b * ((1 - sigma) / sigma2))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have heq : ∀ i : ℕ, K ^ ((1 - sigma) / sigma2) *
      ((3 : ℝ) ^ (-(b * ((1 - sigma) / sigma2)))) ^ i =
      truncationIndicatorScale b sigma sigma2 K i := by
    intro i
    have h1 : ((3 : ℝ) ^ (-(b * (i : ℝ)))) ^ ((1 - sigma) / sigma2) =
        (3 : ℝ) ^ (-(b * ((1 - sigma) / sigma2)) * (i : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      ring_nf
    have h2 : ((3 : ℝ) ^ (-(b * ((1 - sigma) / sigma2)))) ^ i =
        (3 : ℝ) ^ (-(b * ((1 - sigma) / sigma2)) * (i : ℝ)) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(b * ((1 - sigma) / sigma2)))) i,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [truncationIndicatorScale, Real.mul_rpow hK.le (Real.rpow_nonneg (by norm_num) _),
      h1, h2]
  exact ((summable_geometric_of_lt_one hr0.le hr1).mul_left _).congr heq

/-- The re-based per-depth `Gamma_2` scale is bounded uniformly in the depth:
the growing factor `min{gamma^{-1/2}, h^{1/2}}` is capped at `gamma^{-1/2}`. -/
private theorem waveL4TailScale_le (M : ABKModel d) (lout ell : ℤ) (h : ℕ) :
    waveL4TailScale M lout ell h ≤
      streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
        (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) *
        (waveL4HeadConst d * Real.sqrt M.gamma⁻¹ * (3 : ℝ) ^ (M.gamma * (ell : ℝ))) := by
  rw [waveL4TailScale_eq, waveL4Head_eq]
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (Real.rpow_nonneg (streamIncrementLpGainConst_pos d _).le _)
      (Real.rpow_nonneg (by norm_num) _))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (waveL4HeadConst_nonneg d))
    (Real.rpow_nonneg (by norm_num) _)

private theorem summable_waveL4TailScale_mul_truncationIndicatorScale (M : ABKModel d)
    {b sigma sigma2 : ℝ} (hb : 0 < b) (hsigma2 : 0 < sigma2) (hsigma : 0 < 1 - sigma)
    (lout ell : ℤ) :
    Summable fun i : ℕ =>
      waveL4TailScale M lout ell (i + 1) *
        truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i := by
  have hK : 0 < hsepAmplitude sigma b := by
    rw [hsepAmplitude]
    positivity
  set A : ℝ := streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
      (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) *
      (waveL4HeadConst d * Real.sqrt M.gamma⁻¹ * (3 : ℝ) ^ (M.gamma * (ell : ℝ))) with hA
  have hmaj : Summable fun i : ℕ =>
      A * truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i :=
    (summable_truncationIndicatorScale hb hsigma2 hsigma hK).mul_left A
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hmaj
  · exact mul_nonneg (waveL4TailScale_pos M lout ell i).le
      (truncationIndicatorScale_pos hK i).le
  · exact mul_le_mul_of_nonneg_right (waveL4TailScale_le M lout ell (i + 1))
      (truncationIndicatorScale_pos hK i).le

/-! ## The three legs of the printed display -/

/-- **The first printed term of `e.wave.influence.bound`**: the deterministic head
of `e.km.kn.Lp` at the random depth `hsep`, carried by the prefactor
`gamma^{1/2} 3^{-gamma ell}`. -/
def waveHeadTerm (M : ABKModel d) (m : ℤ) (E b : ℝ) (ell : ℤ)
    (omega : CutoffSample d) : ℝ :=
  Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
    waveL4Head M ell (hsep M m E b omega)

/-- **The third printed term of `e.wave.influence.bound`**: the `Gamma_2`-bounded
random part of `e.km.kn.Lp` at the random depth, decomposed over `1_{{i <
hsep}}` per form choice. -/
def waveTailTerm (M : ABKModel d) (m : ℤ) (E b : ℝ) (lout ell : ℤ)
    (omega : CutoffSample d) : ℝ :=
  Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
    ∑ i ∈ Finset.range (hsep M m E b omega), waveL4Tail M lout ell (i + 1) omega

/-- The `Gamma_{2 sigma_2/(2+sigma_2)}` scale of the third term: an explicit
convergent series, the termwise `e.multGammasig` product of the re-based
per-depth `Gamma_2` scale with the `e.indc.O.sigma` indicator scale. -/
def waveTailScale (M : ABKModel d) (b sigma sigma2 : ℝ) (lout ell : ℤ) : ℝ :=
  Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
    (IndependentSums.gammaTriangleConst (2 * sigma2 / (2 + sigma2)) *
      ∑' i : ℕ, HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 *
        (waveL4TailScale M lout ell (i + 1) *
          truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i))

/-- **The printed shape of the third term's scale**: a dimensional constant, the
manuscript's `C b^{-1} sigma^{-1}` indicator series, and the printed large-scale
gain `3^{-(d/8)(lout-ell)}` as an explicit factor.  Note that `gamma^{-1/2}` of
the manuscript's amplitude has cancelled against the `gamma^{1/2}` of the
display's prefactor. -/
def waveTailGainScale (d : ℕ) (b sigma sigma2 : ℝ) (lout ell : ℤ) : ℝ :=
  IndependentSums.gammaTriangleConst (2 * sigma2 / (2 + sigma2)) *
      (HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 *
        (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) * waveL4HeadConst d *
          ∑' i : ℕ, truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i)) *
    (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ)))

theorem waveHeadTerm_nonneg (M : ABKModel d) (m : ℤ) (E b : ℝ) (ell : ℤ)
    (omega : CutoffSample d) : 0 ≤ waveHeadTerm M m E b ell omega :=
  mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos (by norm_num) _).le)
    (waveL4Head_nonneg M ell _)

theorem waveTailTerm_nonneg (M : ABKModel d) (m : ℤ) (E b : ℝ) (lout ell : ℤ)
    (omega : CutoffSample d) : 0 ≤ waveTailTerm M m E b lout ell omega :=
  mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos (by norm_num) _).le)
    (Finset.sum_nonneg fun i _ => waveL4Tail_nonneg M lout ell (i + 1) omega)

/-- **The printed shape of the first term**: the head term is at most `C(d)
gamma^{1/2} hsep^{1/2}`, the manuscript's `gamma^{1/2} hsep^{1/2}` with the
dimensional constant of `e.k.ell.upscales`. -/
theorem waveHeadTerm_le (M : ABKModel d) (m : ℤ) (E b : ℝ) (ell : ℤ)
    (omega : CutoffSample d) :
    waveHeadTerm M m E b ell omega ≤
      waveL4HeadConst d * (Real.sqrt M.gamma * Real.sqrt (hsep M m E b omega : ℝ)) := by
  have hcancel : (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) * (3 : ℝ) ^ (M.gamma * (ell : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    simp
  rw [waveHeadTerm, waveL4Head_eq]
  calc Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
        (waveL4HeadConst d * min (Real.sqrt M.gamma⁻¹) (Real.sqrt (hsep M m E b omega : ℝ)) *
          (3 : ℝ) ^ (M.gamma * (ell : ℝ)))
      = waveL4HeadConst d * (Real.sqrt M.gamma *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt (hsep M m E b omega : ℝ))) *
          ((3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) * (3 : ℝ) ^ (M.gamma * (ell : ℝ))) := by ring
    _ = waveL4HeadConst d * (Real.sqrt M.gamma *
            min (Real.sqrt M.gamma⁻¹) (Real.sqrt (hsep M m E b omega : ℝ))) := by
        rw [hcancel, mul_one]
    _ ≤ waveL4HeadConst d * (Real.sqrt M.gamma * Real.sqrt (hsep M m E b omega : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.sqrt_nonneg _))
          (waveL4HeadConst_nonneg d)

/-- The random-depth tail is dominated by its own truncated layer series: the
bookkeeping, in the shifted form that keeps every summand at a strictly
positive depth. -/
theorem waveL4Tail_le_range_sum (M : ABKModel d) (lout ell : ℤ) (h : ℕ)
    (omega : CutoffSample d) :
    waveL4Tail M lout ell h omega ≤
      ∑ i ∈ Finset.range h, waveL4Tail M lout ell (i + 1) omega := by
  cases h with
  | zero =>
      rw [waveL4Tail_zero]
      simp
  | succ k =>
      exact Finset.single_le_sum
        (f := fun i : ℕ => waveL4Tail M lout ell (i + 1) omega)
        (fun i _ => waveL4Tail_nonneg M lout ell (i + 1) omega)
        (Finset.self_mem_range_succ k)

/-- **The `Gamma_{2 sigma_2/(2+sigma_2)}` bound on the third term from the
direct bad-event gates.**  This is the premise-minimal form used by the exact
wave endpoint; in particular it does not assume the stronger preliminary
package `badClustersConst d ≤ E * cstar M`. -/
theorem isBigOWith_gammaSigma_waveTailTerm_of_gates (M : ABKModel d) {m : ℤ}
    {E sigma sigma2 b : ℝ} (hd2 : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (hsigma2 : 0 < sigma2)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M) (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ E)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) (lout ell : ℤ) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma (2 * sigma2 / (2 + sigma2)))
      (waveTailTerm M m E b lout ell) (waveTailScale M b sigma sigma2 lout ell) := by
  have hsigma1 : (0 : ℝ) < 1 - sigma := by linarith
  have hK : 0 < hsepAmplitude sigma b := by
    rw [hsepAmplitude]
    positivity
  have hc : (0 : ℝ) ≤ Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos (by norm_num) _).le
  have htail := isBigOWith_gammaSigma_three_rpow_hsep_of_gates M hd2 hE hS hsigma0
    hsigma hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgammaE
  have hsum := isBigOWith_gammaSigma_truncatedSum
    (mu := (cutoffSampleLaw M).toMeasure)
    (N := fun omega : CutoffSample d => hsep M m E b omega)
    (Y := fun i omega => waveL4Tail M lout ell (i + 1) omega)
    (a := fun i => waveL4TailScale M lout ell (i + 1))
    (B := fun i => truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i)
    (by norm_num) hsigma2
    (fun i => measurableSet_lt_hsep M m E b i)
    (fun i => measurable_waveL4Tail M lout ell (i + 1))
    (fun i omega => waveL4Tail_nonneg M lout ell (i + 1) omega)
    (fun i => waveL4TailScale_pos M lout ell i)
    (fun i => truncationIndicatorScale_pos hK i)
    (fun i => isBigOWith_gammaSigma_waveL4Tail M lout ell i)
    (fun i => isBigOWith_gammaSigma_indicator_natLt hb0 hsigma2 hsigma1 hK htail i)
    (summable_waveL4TailScale_mul_truncationIndicatorScale M hb0 hsigma2 hsigma1 lout ell)
  exact hsum.const_mul hc


/-- **The third term's scale carries the printed `3^{-(d/8)k_0}` decay.**  The
`gamma^{1/2}` of the display's prefactor cancels the `gamma^{-1/2}` of the
amplitude, and the growing factor `min{gamma^{-1/2}, h^{1/2}}` is capped,
leaving the geometric gain `3^{-(d/8)(lout-ell)} = 3^{-(d/8)(b(1-b)^{-1}k +
k_0)}` as an explicit factor. -/
theorem waveTailScale_le_waveTailGainScale (M : ABKModel d) {b sigma sigma2 : ℝ}
    (hb : 0 < b) (hsigma2 : 0 < sigma2) (hsigma : 0 < 1 - sigma) (lout ell : ℤ) :
    waveTailScale M b sigma sigma2 lout ell ≤
      waveTailGainScale d b sigma sigma2 lout ell := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hK : 0 < hsepAmplitude sigma b := by
    rw [hsepAmplitude]
    positivity
  have hCprod : (0 : ℝ) < HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 := by
    rw [HCPolySupport.Book.Ch04.gammaProductConst]
    positivity
  have hsumB := summable_truncationIndicatorScale hb hsigma2 hsigma hK
  have hsum1 : Summable fun i : ℕ =>
      HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 *
        (waveL4TailScale M lout ell (i + 1) *
          truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i) :=
    (summable_waveL4TailScale_mul_truncationIndicatorScale M hb hsigma2 hsigma
      lout ell).mul_left _
  have hsum2 : Summable fun i : ℕ =>
      HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 *
        (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
            (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) *
            (waveL4HeadConst d * Real.sqrt M.gamma⁻¹ *
              (3 : ℝ) ^ (M.gamma * (ell : ℝ))) *
          truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i) :=
    (hsumB.mul_left _).mul_left _
  have hterm : ∀ i : ℕ,
      HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 *
          (waveL4TailScale M lout ell (i + 1) *
            truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i) ≤
        HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 *
          (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
              (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) *
              (waveL4HeadConst d * Real.sqrt M.gamma⁻¹ *
                (3 : ℝ) ^ (M.gamma * (ell : ℝ))) *
            truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i) :=
    fun i => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (waveL4TailScale_le M lout ell (i + 1))
        (truncationIndicatorScale_pos hK i).le) hCprod.le
  have heval : (∑' i : ℕ, HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 *
        (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
            (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) *
            (waveL4HeadConst d * Real.sqrt M.gamma⁻¹ *
              (3 : ℝ) ^ (M.gamma * (ell : ℝ))) *
          truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i)) =
      HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 *
        (streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) *
            (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) *
            (waveL4HeadConst d * Real.sqrt M.gamma⁻¹ *
              (3 : ℝ) ^ (M.gamma * (ell : ℝ))) *
          ∑' i : ℕ, truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i) := by
    rw [tsum_mul_left, tsum_mul_left]
  have hpre : (0 : ℝ) ≤ Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos (by norm_num) _).le
  rw [waveTailScale, waveTailGainScale]
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      ((Summable.tsum_le_tsum hterm hsum1 hsum2).trans (le_of_eq heval))
      IndependentSums.gammaTriangleConst_pos.le) hpre) (le_of_eq ?_)
  have hsq : Real.sqrt M.gamma * Real.sqrt M.gamma⁻¹ = 1 := by
    rw [← Real.sqrt_mul hgamma.le, mul_inv_cancel₀ (ne_of_gt hgamma), Real.sqrt_one]
  have hcancel : (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) * (3 : ℝ) ^ (M.gamma * (ell : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    simp
  set u : ℝ := Real.sqrt M.gamma
  set v : ℝ := Real.sqrt M.gamma⁻¹
  set w : ℝ := (3 : ℝ) ^ (-(M.gamma * (ell : ℝ)))
  set z : ℝ := (3 : ℝ) ^ (M.gamma * (ell : ℝ))
  set g3 : ℝ := (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ)))
  set Gam : ℝ := IndependentSums.gammaTriangleConst (2 * sigma2 / (2 + sigma2))
  set Cp : ℝ := HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2
  set G4 : ℝ := streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹)
  set hc : ℝ := waveL4HeadConst d
  set S : ℝ := ∑' i : ℕ, truncationIndicatorScale b sigma sigma2 (hsepAmplitude sigma b) i
  calc u * w * (Gam * (Cp * (G4 * g3 * (hc * v * z) * S)))
      = Gam * (Cp * (G4 * hc * S)) * g3 * ((u * v) * (w * z)) := by ring
    _ = Gam * (Cp * (G4 * hc * S)) * g3 := by rw [hsq, hcancel]; ring

/-! ## The generalized three-term provider -/


end

end Algsuperdiff.Section3.Provider.Multiscale
