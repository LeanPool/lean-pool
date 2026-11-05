/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.LargeCubeLinfty
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffL2Expectation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import Mathlib.Analysis.Convex.Integral

/-!
# IncrementLp

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `e.kmn.bounds`: the volume-normalized `L^p` mass of a stream increment

This module provides the volume-normalized `L^p` estimate `e.kmn.bounds` used
in `l.km.kn.Lp.estimates` (ABK26),

```
  ⨍_{cu_l} |(k_m - k_n)(x)|^p dx
      <= O_{Gamma_{2/p}}( (C p)^{p/2} min{gamma^{-p/2}, (m-n)^{p/2}} 3^{gamma p m} ) ,
```

together with the norm-level estimate it supports and the exact algebraic
interface through which the *next* node, `e.kl.bounds.large`, upgrades that
estimate to the printed `e.km.kn.Lp`.  The exact frozen all-`p` export now has
a sorry-free proof term supplied by the later moment-boosted provider; that
separate export, not the precursor declarations in this file, is the
source-facing object.

## The route

The manuscript derives `e.kmn.bounds` from the pointwise `e.k.ell.upscales` "by
`R^d`-stationarity and Lemma `l.Gamma.sigma.triangle`".

1. the proved `isBigOWith_gammaSigma_incrementAt` gives, at **every** point `x`
   with one and the same amplitude `A = C_d min{gamma^{-1/2},(m-n)^{1/2}}
   3^{gamma m}`, the tail bound `|(k_m - k_n)(x)| = O_{Gamma_2}(A)`;
2. CoarseGraining's `hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma`
   converts it to `E|(k_m-k_n)(x)|^q <= ( q^{1/2})^q` for every `q >= 1`,
   uniformly in `x`;
3. Jensen on the cube (`streamIncrementLpMass_rpow_le`, the cube average being
   a probability average) and Fubini give the same growth for the mass:
   `E[(⨍|k_m-k_n|^p)^r] <= ( (pr)^{1/2})^{pr} = (^p p^{p/2} r^{p/2})^r`;
4. CoarseGraining's
   `isBigOWith_gammaSigma_of_hasGammaMomentGrowthWith_of_nonneg` converts back,
   at Orlicz exponent `2/p`.

This module's constants carry it, so no adjustment is needed downstream.

## Historical scope and the later large-cube providers

The printed `e.km.kn.Lp` has two terms: a deterministic head and a random part
carrying the large-scale gain `3^{-(d/p)(l-m)}`.  That gain is the content of
`e.kl.bounds.large`, whose proof uses `a.j.frd` (finite range) and
`p.concentration` on the average of the mass over the scale-`m` subcubes of
`cu_l`.  This precursor proves only the `l`-uniform estimate and supplies the
transfer used by the later files `IncrementLpGain.lean`,
`IncrementLpLarge.lean`, `IncrementLpSquared.lean`, and the translated-provider
chain.  Those later providers now implement the finite-range/stationarity
route.  The exact frozen all-`p` theorem is now wired to the ordinary provider
in `MomentBoostedLargeAllP.lean`; this precursor itself makes no source-node
status claim:

* `isBigOWith_gammaSigma_two_rpow_inv` — a `Gamma_{2/p}` mass tail at scale `K`
  has a `Gamma_2` norm tail at scale `K^{1/p}`; every geometric gain in `K` has
  its exponent divided by `p`, so the mass gain `3^{-(d/2)(l-m)}` of
  `e.kl.bounds.large` becomes the norm gain `3^{-(d/(2p))(l-m)}`, i.e.
  `3^{-(d/8)(l-m)}` at `p = 4`;
* `streamIncrementLpNorm_head_tail_of_mass_head_tail` — the packaged
  "deterministic head + geometrically decaying `Gamma_2` tail" form, which is
  what the wave-oscillations step of `p.bfA.multiscalebound` needs for the third term
  `O_{Gamma_{2(1+sigma)^{-1}}}(sigma^{-1} 3^{-(d/8)k_0})` of
  `e.wave.influence.bound`.

## Disclosed conventions

* `|·|` is the exact Euclidean matrix operator norm
  `Book.Ch02.matrixOperatorNorm`, the same reading the proved
  `e.k.ell.upscales`, `e.k.ell.upscales.infty` and `e.km.kn.Linfty` use.  (The
  `L²` display `e.km.kn.L2.exact` is a Frobenius statement, since it is an
  identity for `j_k : j_{k'}`; the two are related by
  `matrixOperatorNorm_le_matrixFrobeniusNorm`.)
* The resulting `Gamma_{2/p}` scale is `e · (gammaMomentConst 2 · C_d ·
  min{gamma^{-1/2},(m-n)^{1/2}} 3^{gamma m})^p · p^{p/2}` — NOTE the
  `gammaMomentConst 2 = 2e` inside the `p`-th power.  This implies the printed
  `(Cp)^{p/2} min{.}^p 3^{gamma p m}` with the source's generic `C` read as
  `C:= e^2 · (2e · C_d)^2` (`C^{p/2} ≥ e·(2e·C_d)^p` for all `p ≥ 1`), a `p`-uniform
  dimension-only constant.  `C_d` is the proved amplitude of `e.k.ell.upscales`
  (`streamPointScale`).
* No relation between `l` and `m` is used: `e.kmn.bounds` is stated in the
  source for every `l`, and the proof here is uniform in `l`.

## Main definitions

* `streamIncrementLpDensity`, `streamIncrementLpMass`, `streamIncrementLpNorm`.
* `streamPointScale`: the proved `Gamma_2` amplitude of `e.k.ell.upscales`.
* `streamIncrementLpMassScale`, `streamIncrementLpNormScale`.

## Main results

* `streamIncrementLpMass_rpow_le`: Jensen on the cube.
* `integral_streamIncrementLpMass_le`, `integrable_streamIncrementLpMass`:
  the Fubini step.
* `hasGammaMomentGrowthWith_streamIncrementLpMass`,
  `isBigOWith_gammaSigma_streamIncrementLpMass`: **`e.kmn.bounds`**.
* `isBigOWith_gammaSigma_streamIncrementLpNorm`: its norm form.
* `isBigOWith_gammaSigma_two_rpow_inv`,
  `streamIncrementLpNorm_head_tail_of_mass_head_tail`: the additive interface
  for `e.kl.bounds.large`.

## References

* ABK26, `l.km.kn.Lp.estimates`; `e.kmn.bounds`; `e.kl.bounds.large`;
  `e.km.kn.Lp`; `e.k.ell.upscales`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The `L^p` density, mass and norm of a stream increment -/

/-- The `p`-th power of the pointwise size of the stream increment `k_m - k_n`,
measured in the exact Euclidean matrix operator norm (the `|·|` of
`e.k.ell.upscales`). -/
def streamIncrementLpDensity (p : ℝ) (n m : ℤ) (omega : ShellSeq d) (x : Vec d) : ℝ :=
  Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p

/-- The volume-normalized `L^p` mass `⨍_{cu_l} |k_m - k_n|^p` of a stream
increment on the origin cube `cu_l`. -/
def streamIncrementLpMass (p : ℝ) (l n m : ℤ) (omega : ShellSeq d) : ℝ :=
  Book.Ch02.average (Book.Ch02.cubeDomain (originCube d l))
    (streamIncrementLpDensity p n m omega)

/-- The volume-normalized `L^p` norm `‖k_m - k_n‖_{L^p(cu_l)}` of a stream
increment on the origin cube `cu_l`. -/
def streamIncrementLpNorm (p : ℝ) (l n m : ℤ) (omega : ShellSeq d) : ℝ :=
  streamIncrementLpMass p l n m omega ^ p⁻¹

theorem streamIncrementLpDensity_nonneg (p : ℝ) (n m : ℤ) (omega : ShellSeq d)
    (x : Vec d) : 0 ≤ streamIncrementLpDensity p n m omega x :=
  Real.rpow_nonneg (Book.Ch02.matrixOperatorNorm_nonneg _) _

/-! ## Continuity, measurability and integrability of the density -/

private theorem continuous_finiteShellIncrement_apply (omega : ShellSeq d) (n m : ℤ) :
    Continuous (fun x : Vec d => finiteShellIncrement omega n m x) := by
  have h : (fun x : Vec d => finiteShellIncrement omega n m x) =
      fun x : Vec d => ∑ k ∈ Finset.Ioc n m, (omega k) x := by
    funext x
    rw [finiteShellIncrement_apply]
    rfl
  rw [h]
  exact continuous_finsetSum _ fun k _ => (omega k).1.1.continuous

/-- The `L^p` density is continuous in the point. -/
theorem continuous_streamIncrementLpDensity {p : ℝ} (hp : 0 < p) (n m : ℤ)
    (omega : ShellSeq d) : Continuous (streamIncrementLpDensity p n m omega) := by
  have hbase : Continuous
      (fun x : Vec d => Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m x)) :=
    ShellField.continuous_matrixOperatorNorm.comp
      (continuous_finiteShellIncrement_apply omega n m)
  exact (Real.continuous_rpow_const hp.le).comp hbase

/-- The `L^p` density at a fixed point is measurable in the sample. -/
theorem measurable_streamIncrementLpDensity (p : ℝ) (n m : ℤ) (x : Vec d) :
    Measurable (fun omega : ShellSeq d => streamIncrementLpDensity p n m omega x) :=
  (measurable_matrixOperatorNorm_finiteShellIncrement n m x).pow_const p

/-- Carathéodory joint measurability of the `L^p` density. -/
theorem measurable_uncurry_streamIncrementLpDensity {p : ℝ} (hp : 0 < p) (n m : ℤ) :
    Measurable (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
      streamIncrementLpDensity p n m omega x)) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun omega => continuous_streamIncrementLpDensity hp n m omega)
    (fun x => measurable_streamIncrementLpDensity p n m x)

/-- The `L^p` density is integrable on every origin cube: it is continuous and
the cube is bounded. -/
theorem integrableOn_streamIncrementLpDensity {p : ℝ} (hp : 0 < p) (l n m : ℤ)
    (omega : ShellSeq d) :
    IntegrableOn (streamIncrementLpDensity p n m omega)
      (openCubeSet (originCube d l)) volume := by
  have hcont := continuous_streamIncrementLpDensity hp n m omega
  have hcompact : IsCompact (Metric.closedBall (cubeCenter (originCube d l))
      (cubeRadius (originCube d l))) := isCompact_closedBall _ _
  exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set
    ((openCubeSet_subset_cubeSet _).trans (cubeSet_subset_closedBall _))

/-! ## The cube average as a Mathlib set average -/

private theorem average_eq_setAverage (Q : TriadicCube d) (f : Vec d → ℝ) :
    Book.Ch02.average (Book.Ch02.cubeDomain Q) f = ⨍ x in openCubeSet Q, f x := by
  rw [setAverage_eq]
  simp only [Book.Ch02.average, Book.Ch02.cubeDomain_coe, measureReal_def, smul_eq_mul]

private theorem volume_openCubeSet_ne_zero (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ 0 := by
  intro h
  have hpos : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
  rw [← volume_openCubeSet_toReal, h] at hpos
  simp at hpos

/-- The volume-normalized `L^p` mass is nonnegative. -/
theorem streamIncrementLpMass_nonneg (p : ℝ) (l n m : ℤ) (omega : ShellSeq d) :
    0 ≤ streamIncrementLpMass p l n m omega := by
  rw [streamIncrementLpMass, Book.Ch02.average, Book.Ch02.cubeDomain_coe]
  refine mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ?_
  exact setIntegral_nonneg (isOpen_openCubeSet _).measurableSet
    fun x _ => streamIncrementLpDensity_nonneg p n m omega x

/-- The volume-normalized `L^p` norm is nonnegative. -/
theorem streamIncrementLpNorm_nonneg (p : ℝ) (l n m : ℤ) (omega : ShellSeq d) :
    0 ≤ streamIncrementLpNorm p l n m omega :=
  Real.rpow_nonneg (streamIncrementLpMass_nonneg p l n m omega) _

private theorem streamIncrementLpDensity_rpow (p r : ℝ) (n m : ℤ)
    (omega : ShellSeq d) (x : Vec d) :
    streamIncrementLpDensity p n m omega x ^ r =
      streamIncrementLpDensity (p * r) n m omega x := by
  simp only [streamIncrementLpDensity]
  rw [← Real.rpow_mul (Book.Ch02.matrixOperatorNorm_nonneg _)]

/-! ## Jensen's inequality on the cube -/

/-- **Jensen's inequality for the cube mass.**  Raising the `L^p` mass to a
power `r ≥ 1` is dominated by the `L^{pr}` mass, because the cube average is a
probability average. -/
theorem streamIncrementLpMass_rpow_le {p r : ℝ} (hp : 0 < p) (hr : 1 ≤ r)
    (l n m : ℤ) (omega : ShellSeq d) :
    streamIncrementLpMass p l n m omega ^ r ≤
      streamIncrementLpMass (p * r) l n m omega := by
  let : Fact (volume (openCubeSet (originCube d l)) < ⊤) :=
    ⟨volume_openCubeSet_lt_top _⟩
  have : NeZero (volume.restrict (openCubeSet (originCube d l))) :=
    ⟨fun h => volume_openCubeSet_ne_zero (originCube d l)
      (Measure.restrict_eq_zero.1 h)⟩
  have hpr : 0 < p * r := mul_pos hp (lt_of_lt_of_le zero_lt_one hr)
  have hint : Integrable (streamIncrementLpDensity p n m omega)
      (volume.restrict (openCubeSet (originCube d l))) :=
    integrableOn_streamIncrementLpDensity hp l n m omega
  have hcomp : ((fun t : ℝ => t ^ r) ∘ streamIncrementLpDensity p n m omega) =
      streamIncrementLpDensity (p * r) n m omega := by
    funext x
    exact streamIncrementLpDensity_rpow p r n m omega x
  have hintr : Integrable ((fun t : ℝ => t ^ r) ∘ streamIncrementLpDensity p n m omega)
      (volume.restrict (openCubeSet (originCube d l))) := by
    rw [hcomp]
    exact integrableOn_streamIncrementLpDensity hpr l n m omega
  have hJ := (convexOn_rpow hr).map_average_le
    (Real.continuous_rpow_const (le_trans zero_le_one hr)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun x =>
      Set.mem_Ici.2 (streamIncrementLpDensity_nonneg p n m omega x))
    hint hintr
  rw [streamIncrementLpMass, streamIncrementLpMass, average_eq_setAverage,
    average_eq_setAverage]
  calc (⨍ x in openCubeSet (originCube d l), streamIncrementLpDensity p n m omega x) ^ r
      ≤ ⨍ x in openCubeSet (originCube d l),
          streamIncrementLpDensity p n m omega x ^ r := hJ
    _ = ⨍ x in openCubeSet (originCube d l),
          streamIncrementLpDensity (p * r) n m omega x := by
        exact congrArg _ hcomp

/-! ## The pointwise moment growth of `e.k.ell.upscales` -/

/-- The `Γ₂` amplitude of the proved `e.k.ell.upscales` at a point
(`isBigOWith_gammaSigma_incrementAt`). -/
def streamPointScale (M : ABKModel d) (n m : ℤ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 * ((d : ℝ) ^ 2 *
    (geometricConcentrationConst *
      min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ))))

theorem streamPointScale_pos (M : ABKModel d) {n m : ℤ} (hnm : n < m) :
    0 < streamPointScale M n m := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hdR : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hmin : 0 < min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) := by
    refine lt_min (Real.sqrt_pos.2 (inv_pos.2 M.shellPrefix.gamma_pos))
      (Real.sqrt_pos.2 ?_)
    have hlt : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  refine mul_pos IndependentSums.gammaTriangleConst_pos (mul_pos hdR ?_)
  exact mul_pos (mul_pos geometricConcentrationConst_pos hmin)
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- Absolute moment growth of the pointwise increment size, uniform in the point.
This is the moment form of the proved `e.k.ell.upscales`. -/
theorem hasGammaMomentGrowthWith_incrementAt (M : ABKModel d) {n m : ℤ}
    (hnm : n < m) (x : Vec d) :
    IndependentSums.HasGammaMomentGrowthWith M.P.toMeasure 2
      (fun omega : ShellSeq d =>
        Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m x))
      (IndependentSums.gammaMomentConst 2 * streamPointScale M n m) :=
  IndependentSums.hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma
    (by norm_num) (streamPointScale_pos M hnm)
    (fun _ => Book.Ch02.matrixOperatorNorm_nonneg _)
    (measurable_matrixOperatorNorm_finiteShellIncrement n m x).aemeasurable
    (isBigOWith_gammaSigma_incrementAt M hnm x)

/-- The uniform-in-`x` moment bound, written directly at the `L^q` density. -/
private theorem density_moment (M : ABKModel d) {q : ℝ} (hq : 1 ≤ q) {n m : ℤ}
    (hnm : n < m) (x : Vec d) :
    Integrable (fun omega : ShellSeq d => streamIncrementLpDensity q n m omega x)
        M.P.toMeasure ∧
      ∫ omega : ShellSeq d, streamIncrementLpDensity q n m omega x ∂M.P.toMeasure ≤
        (IndependentSums.gammaMomentConst 2 * streamPointScale M n m *
          q ^ ((2 : ℝ)⁻¹)) ^ q := by
  have habs : (fun omega : ShellSeq d =>
      |Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega n m x)| ^ q) =
      fun omega : ShellSeq d => streamIncrementLpDensity q n m omega x := by
    funext omega
    rw [abs_of_nonneg (Book.Ch02.matrixOperatorNorm_nonneg _)]
    rfl
  obtain ⟨hint, hbound⟩ := hasGammaMomentGrowthWith_incrementAt M hnm x hq
  rw [habs] at hint hbound
  exact ⟨hint, hbound⟩

/-! ## Fubini on the cube -/

private theorem prod_integrable_density (M : ABKModel d) {q : ℝ} (hq : 1 ≤ q) {n m : ℤ}
    (hnm : n < m) (l : ℤ) :
    Integrable (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
        streamIncrementLpDensity q n m omega x))
      ((volume.restrict (openCubeSet (originCube d l))).prod M.P.toMeasure) := by
  let : Fact (volume (openCubeSet (originCube d l)) < ⊤) :=
    ⟨volume_openCubeSet_lt_top _⟩
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hjoint := measurable_uncurry_streamIncrementLpDensity (d := d) hq0 n m
  refine (integrable_prod_iff hjoint.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards with x
    exact (density_moment M hq hnm x).1
  · have hSM : StronglyMeasurable (fun x : Vec d =>
        ∫ omega : ShellSeq d, ‖streamIncrementLpDensity q n m omega x‖
          ∂M.P.toMeasure) :=
      (hjoint.norm.stronglyMeasurable).integral_prod_right'
    refine Integrable.mono' (integrable_const
      ((IndependentSums.gammaMomentConst 2 * streamPointScale M n m *
        q ^ ((2 : ℝ)⁻¹)) ^ q)) hSM.aestronglyMeasurable ?_
    filter_upwards with x
    have hnorm : (fun omega : ShellSeq d =>
        ‖streamIncrementLpDensity q n m omega x‖) =
        fun omega : ShellSeq d => streamIncrementLpDensity q n m omega x := by
      funext omega
      exact Real.norm_of_nonneg (streamIncrementLpDensity_nonneg q n m omega x)
    simp only [Function.uncurry_apply_pair]
    rw [hnorm, Real.norm_of_nonneg
      (integral_nonneg fun omega => streamIncrementLpDensity_nonneg q n m omega x)]
    exact (density_moment M hq hnm x).2

/-- The cube `L^q` mass of the increment is integrable. -/
theorem integrable_streamIncrementLpMass (M : ABKModel d) {q : ℝ} (hq : 1 ≤ q)
    {n m : ℤ} (hnm : n < m) (l : ℤ) :
    Integrable (streamIncrementLpMass q l n m) M.P.toMeasure := by
  have hint : Integrable (fun omega : ShellSeq d =>
      ∫ x in openCubeSet (originCube d l),
        streamIncrementLpDensity q n m omega x) M.P.toMeasure :=
    (prod_integrable_density M hq hnm l).swap.integral_prod_left
  have heq : streamIncrementLpMass q l n m = fun omega : ShellSeq d =>
      (volume (openCubeSet (originCube d l))).toReal⁻¹ *
        ∫ x in openCubeSet (originCube d l),
          streamIncrementLpDensity q n m omega x := by
    funext omega
    rw [streamIncrementLpMass, Book.Ch02.average, Book.Ch02.cubeDomain_coe]
  rw [heq]
  exact hint.const_mul _

/-- **The cube `L^q` mass inherits the pointwise moment bound.**  Fubini turns
the uniform-in-`x` moment estimate of `e.k.ell.upscales` into the same estimate
for the volume-normalized mass. -/
theorem integral_streamIncrementLpMass_le (M : ABKModel d) {q : ℝ} (hq : 1 ≤ q)
    {n m : ℤ} (hnm : n < m) (l : ℤ) :
    ∫ omega : ShellSeq d, streamIncrementLpMass q l n m omega ∂M.P.toMeasure ≤
      (IndependentSums.gammaMomentConst 2 * streamPointScale M n m *
        q ^ ((2 : ℝ)⁻¹)) ^ q := by
  let : Fact (volume (openCubeSet (originCube d l)) < ⊤) :=
    ⟨volume_openCubeSet_lt_top _⟩
  have hVpos : (0 : ℝ) < (volume (openCubeSet (originCube d l))).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d l)
  have hswapEq := integral_integral_swap (prod_integrable_density M hq hnm l)
  have hinner : Integrable (fun x : Vec d =>
      ∫ omega : ShellSeq d, streamIncrementLpDensity q n m omega x ∂M.P.toMeasure)
      (volume.restrict (openCubeSet (originCube d l))) :=
    (prod_integrable_density M hq hnm l).integral_prod_left
  have hmono : (∫ x in openCubeSet (originCube d l),
        ∫ omega : ShellSeq d, streamIncrementLpDensity q n m omega x ∂M.P.toMeasure) ≤
      (volume (openCubeSet (originCube d l))).toReal *
        (IndependentSums.gammaMomentConst 2 * streamPointScale M n m *
          q ^ ((2 : ℝ)⁻¹)) ^ q := by
    have hle := integral_mono hinner
      (integrable_const ((IndependentSums.gammaMomentConst 2 * streamPointScale M n m *
        q ^ ((2 : ℝ)⁻¹)) ^ q)) (fun x => (density_moment M hq hnm x).2)
    rwa [setIntegral_const, measureReal_def, smul_eq_mul] at hle
  calc ∫ omega : ShellSeq d, streamIncrementLpMass q l n m omega ∂M.P.toMeasure
      = (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ∫ omega : ShellSeq d, (∫ x in openCubeSet (originCube d l),
            streamIncrementLpDensity q n m omega x) ∂M.P.toMeasure := by
        simp only [streamIncrementLpMass, Book.Ch02.average, Book.Ch02.cubeDomain_coe]
        rw [integral_const_mul]
    _ = (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ∫ x in openCubeSet (originCube d l),
            (∫ omega : ShellSeq d, streamIncrementLpDensity q n m omega x
              ∂M.P.toMeasure) := by
        rw [hswapEq]
    _ ≤ (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ((volume (openCubeSet (originCube d l))).toReal *
            (IndependentSums.gammaMomentConst 2 * streamPointScale M n m *
              q ^ ((2 : ℝ)⁻¹)) ^ q) := by
        exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hVpos.le)
    _ = (IndependentSums.gammaMomentConst 2 * streamPointScale M n m *
          q ^ ((2 : ℝ)⁻¹)) ^ q := by
        field_simp

/-! ## Numeric preliminaries

The one real-power identity behind the passage from the `L^{pr}` moment bound
to `Γ_{2/p}` moment growth, isolated from every probabilistic statement. -/

private theorem rpow_moment_identity {a p r : ℝ} (ha : 0 ≤ a) (hp : 0 < p)
    (hr : 0 < r) :
    (a * (p * r) ^ ((2 : ℝ)⁻¹)) ^ (p * r) =
      (a ^ p * p ^ (p / 2) * r ^ (p / 2)) ^ r := by
  have hpr : (0 : ℝ) ≤ p * r := (mul_pos hp hr).le
  have he : (2 : ℝ)⁻¹ * (p * r) = p * r / 2 := by ring
  have he2 : p / 2 * r = p * r / 2 := by ring
  have hL : (a * (p * r) ^ ((2 : ℝ)⁻¹)) ^ (p * r) =
      a ^ (p * r) * (p ^ (p * r / 2) * r ^ (p * r / 2)) := by
    rw [Real.mul_rpow ha (Real.rpow_nonneg hpr _), ← Real.rpow_mul hpr, he,
      Real.mul_rpow hp.le hr.le]
  have hR : (a ^ p * p ^ (p / 2) * r ^ (p / 2)) ^ r =
      a ^ (p * r) * (p ^ (p * r / 2) * r ^ (p * r / 2)) := by
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hp.le _))
        (Real.rpow_nonneg hr.le _),
      Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hp.le _),
      ← Real.rpow_mul ha, ← Real.rpow_mul hp.le, ← Real.rpow_mul hr.le, he2,
      mul_assoc]
  rw [hL, hR]

/-! ## `e.kmn.bounds` -/

/-- The `Γ_{2/p}` moment growth of the cube `L^p` mass: Jensen on the cube plus
the uniform pointwise moment bound. -/
theorem hasGammaMomentGrowthWith_streamIncrementLpMass (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) (l : ℤ) :
    IndependentSums.HasGammaMomentGrowthWith M.P.toMeasure (2 / p)
      (streamIncrementLpMass p l n m)
      ((IndependentSums.gammaMomentConst 2 * streamPointScale M n m) ^ p *
        p ^ (p / 2)) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have ha : (0 : ℝ) ≤ IndependentSums.gammaMomentConst 2 * streamPointScale M n m :=
    (mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
      (streamPointScale_pos M hnm)).le
  intro r hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hpr1 : (1 : ℝ) ≤ p * r := by nlinarith
  have habs : (fun omega : ShellSeq d => |streamIncrementLpMass p l n m omega| ^ r) =
      fun omega : ShellSeq d => streamIncrementLpMass p l n m omega ^ r := by
    funext omega
    rw [abs_of_nonneg (streamIncrementLpMass_nonneg p l n m omega)]
  have hdom : ∀ omega : ShellSeq d,
      streamIncrementLpMass p l n m omega ^ r ≤
        streamIncrementLpMass (p * r) l n m omega :=
    fun omega => streamIncrementLpMass_rpow_le hp0 hr l n m omega
  have hAE : AEStronglyMeasurable
      (fun omega : ShellSeq d => streamIncrementLpMass p l n m omega ^ r)
      M.P.toMeasure :=
    (Real.continuous_rpow_const hr0.le).comp_aestronglyMeasurable
      (integrable_streamIncrementLpMass M hp hnm l).aestronglyMeasurable
  have hbig : Integrable (streamIncrementLpMass (p * r) l n m) M.P.toMeasure :=
    integrable_streamIncrementLpMass M hpr1 hnm l
  have hint : Integrable
      (fun omega : ShellSeq d => streamIncrementLpMass p l n m omega ^ r)
      M.P.toMeasure := by
    refine Integrable.mono' hbig hAE (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_of_nonneg
      (Real.rpow_nonneg (streamIncrementLpMass_nonneg p l n m omega) r)]
    exact hdom omega
  refine ⟨by rwa [habs], ?_⟩
  rw [habs]
  have hsig : ((2 : ℝ) / p)⁻¹ = p / 2 := by
    field_simp
  rw [hsig, ← rpow_moment_identity ha hp0 hr0]
  calc ∫ omega : ShellSeq d, streamIncrementLpMass p l n m omega ^ r ∂M.P.toMeasure
      ≤ ∫ omega : ShellSeq d, streamIncrementLpMass (p * r) l n m omega
          ∂M.P.toMeasure := integral_mono hint hbig hdom
    _ ≤ (IndependentSums.gammaMomentConst 2 * streamPointScale M n m *
          (p * r) ^ ((2 : ℝ)⁻¹)) ^ (p * r) :=
        integral_streamIncrementLpMass_le M hpr1 hnm l

/-- The `Γ_{2/p}` scale of `e.kmn.bounds`: the `p`-th power of the pointwise
`e.k.ell.upscales` amplitude, times the moment factor `p^{p/2}`, times the
universal `e` of the moment-to-tail conversion. -/
def streamIncrementLpMassScale (M : ABKModel d) (p : ℝ) (n m : ℤ) : ℝ :=
  Real.exp 1 * ((IndependentSums.gammaMomentConst 2 * streamPointScale M n m) ^ p *
    p ^ (p / 2))

theorem streamIncrementLpMassScale_pos (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m : ℤ} (hnm : n < m) : 0 < streamIncrementLpMassScale M p n m := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have ha : (0 : ℝ) < IndependentSums.gammaMomentConst 2 * streamPointScale M n m :=
    mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
      (streamPointScale_pos M hnm)
  rw [streamIncrementLpMassScale]
  exact mul_pos (Real.exp_pos 1)
    (mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hp0 _))

/-- **ABK26's `e.kmn.bounds`**:

`⨍_{cu_l} |(k_m - k_n)(x)|^p dx ≤ O_{Γ_{2/p}}( (C p)^{p/2} min{γ^{-p/2}, (m-n)^{p/2}} 3^{γ p m} )`,

for every `p ≥ 1` and every `l, m, n ∈ ℤ` with `n < m` (no relation between `l`
and `m` is used).  The resulting scale is
`e · (C_d min{γ^{-1/2},(m-n)^{1/2}} 3^{γ m})^p · p^{p/2}`, which is the printed
right-hand side with the source's generic `C` read as `C_d^2`. -/
theorem isBigOWith_gammaSigma_streamIncrementLpMass (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) (l : ℤ) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (streamIncrementLpMass p l n m) (streamIncrementLpMassScale M p n m) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hMpos : (0 : ℝ) <
      (IndependentSums.gammaMomentConst 2 * streamPointScale M n m) ^ p *
        p ^ (p / 2) := by
    have ha : (0 : ℝ) < IndependentSums.gammaMomentConst 2 * streamPointScale M n m :=
      mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
        (streamPointScale_pos M hnm)
    exact mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hp0 _)
  exact IndependentSums.isBigOWith_gammaSigma_of_hasGammaMomentGrowthWith_of_nonneg
    (by positivity) hMpos (fun omega => streamIncrementLpMass_nonneg p l n m omega)
    (hasGammaMomentGrowthWith_streamIncrementLpMass M hp hnm l)

/-! ## The mass-to-norm transfer -/

/-- **The `Γ` bookkeeping of the `1/p`-th root.**  A nonnegative
`O_{Γ_{2/p}}(K)` mass-level quantity has an `O_{Γ₂}(K^{1/p})` `1/p`-th root.

Every geometric gain carried by `K` therefore has its exponent divided by `p`;
at `p = 4` a mass gain `3^{-(d/2)(l-m)}` becomes the norm gain
`3^{-(d/8)(l-m)}`, which is the `3^{-(d/8)k₀}` of `e.wave.influence.bound`. -/
theorem isBigOWith_gammaSigma_two_rpow_inv {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {T : Omega → ℝ} {p K : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hT_nonneg : ∀ omega, 0 ≤ T omega)
    (hT : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma (2 / p)) T K) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 2)
      (fun omega => T omega ^ p⁻¹) (K ^ p⁻¹) := by
  have h := (Orlicz.isBigOWith_gammaSigma_rpow_iff_of_nonneg
    (μ := mu) (X := T) (K := K) (σ := 2 / p) (p := p⁻¹)
    (by positivity) hK hT_nonneg).1 hT
  have hsig : (2 / p) / p⁻¹ = 2 := by
    field_simp
  rwa [hsig] at h

/-- **The deterministic half of the mass-to-norm transfer.**  Subadditivity of
`t ↦ t^{1/p}` splits a mass bound `mass ≤ H + T` into the norm bound
`mass^{1/p} ≤ H^{1/p} + T^{1/p}`, keeping the deterministic head deterministic. -/
theorem rpow_inv_le_add_rpow_inv_of_le_add {p H T z : ℝ} (hp : 1 ≤ p)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hz : 0 ≤ z) (hle : z ≤ H + T) :
    z ^ p⁻¹ ≤ H ^ p⁻¹ + T ^ p⁻¹ := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hinv0 : (0 : ℝ) ≤ p⁻¹ := (inv_pos.2 hp0).le
  have hinv1 : p⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hp
  calc z ^ p⁻¹ ≤ (H + T) ^ p⁻¹ := Real.rpow_le_rpow hz hle hinv0
    _ ≤ H ^ p⁻¹ + T ^ p⁻¹ := Real.rpow_add_le_add_rpow hH hT hinv0 hinv1

/-! ## The norm-level estimate available from `e.kmn.bounds` alone -/

/-- The `Γ₂` scale of the `L^p` norm delivered by `e.kmn.bounds`, before the
finite-range improvement `e.kl.bounds.large`. -/
def streamIncrementLpNormScale (M : ABKModel d) (p : ℝ) (n m : ℤ) : ℝ :=
  streamIncrementLpMassScale M p n m ^ p⁻¹

/-- The `1/p`-th root of `e.kmn.bounds`:

`‖k_m - k_n‖_{L^p(cu_l)} ≤ O_{Γ₂}( (C p)^{1/2} min{γ^{-1/2}, (m-n)^{1/2}} 3^{γ m} )`.

This is the norm-level estimate that `e.kmn.bounds` alone supports: a single
`Γ₂` envelope, uniform in `l`, with **no** large-scale gain.  The printed
`e.km.kn.Lp` (in the form corrected) additionally splits off a deterministic
head and gains the factor `3^{-(d/(2p))(l-m)}` on the random part; that
improvement is the content of `e.kl.bounds.large`, which is not proved in this
precursor.  It is supplied by the later large-cube provider chain culminating
in `MomentBoostedLargeAllP.lean`.  See `isBigOWith_gammaSigma_two_rpow_inv` for
the transfer that turns the improved mass estimate into the improved norm
estimate with no restatement.  The exact frozen export is maintained separately
from this helper theorem. -/
theorem isBigOWith_gammaSigma_streamIncrementLpNorm (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) (l : ℤ) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (streamIncrementLpNorm p l n m) (streamIncrementLpNormScale M p n m) :=
  isBigOWith_gammaSigma_two_rpow_inv (lt_of_lt_of_le zero_lt_one hp)
    (streamIncrementLpMassScale_pos M hp hnm).le
    (fun omega => streamIncrementLpMass_nonneg p l n m omega)
    (isBigOWith_gammaSigma_streamIncrementLpMass M hp hnm l)

/-! ## The wave-facing packaging -/

/-- **The shape the wave-oscillations step of `p.bfA.multiscalebound` consumes.**

Whenever the cube `L^p` mass of a stream increment is dominated by a
*deterministic* head `H` plus a nonnegative tail `T` obeying a `Γ_{2/p}` bound
at scale `K`, the `L^p` *norm* is dominated by the deterministic head `H^{1/p}`
plus a tail obeying a `Γ₂` bound at scale `K^{1/p}`.

This is the exact interface for `e.kl.bounds.large`: with `H = (Cp)^{p/2}
A^{p/2}` and `K = (Cp)^{p/2} A^{p/2} 3^{-(d/2)(l-m)}`, `A = min{γ^{-1}, m-n}
3^{2γm}`, the conclusion is the corrected `e.km.kn.Lp`  in the form `(Cp)^{1/2}
A^{1/2} + O_{Γ₂}((Cp)^{1/2} A^{1/2} 3^{-(d/(2p))(l-m)})`, whose `p = 4`
instance carries the `3^{-(d/8)(l-m)}` gain of the third term of
`e.wave.influence.bound`. -/
theorem streamIncrementLpNorm_head_tail_of_mass_head_tail (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) (l n m : ℤ) {H K : ℝ} {T : ShellSeq d → ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hT_nonneg : ∀ omega, 0 ≤ T omega)
    (hmass : ∀ omega, streamIncrementLpMass p l n m omega ≤ H + T omega)
    (hT : IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma (2 / p)) T K) :
    (∀ omega : ShellSeq d,
        streamIncrementLpNorm p l n m omega ≤ H ^ p⁻¹ + T omega ^ p⁻¹) ∧
      IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega => T omega ^ p⁻¹) (K ^ p⁻¹) := by
  refine ⟨fun omega => ?_, ?_⟩
  · exact rpow_inv_le_add_rpow_inv_of_le_add hp hH (hT_nonneg omega)
      (streamIncrementLpMass_nonneg p l n m omega) (hmass omega)
  · exact isBigOWith_gammaSigma_two_rpow_inv (lt_of_lt_of_le zero_lt_one hp) hK
      hT_nonneg hT

end

end Algsuperdiff.Section3.Provider.Stream
