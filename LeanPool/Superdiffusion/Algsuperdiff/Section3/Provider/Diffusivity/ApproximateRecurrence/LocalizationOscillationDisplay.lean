/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationGridMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationAssemblyShell

/-!
# LocalizationOscillationDisplay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `e.lower.bound.oscillations` at the fresh-shell correctors

Source displays in ABK26:

* `e.lower.bound.oscillations` (label; `\begin{multline}`, `\end{multline}`;
  the printed chain occupies),
* `e.nablaw.oscillations` (label; display),
* `e.recurrence.params` (label), which fixes `n` and `K`,
* `e.def.w` (label), which defines the two finite-volume correctors.

ABK26 asserts, for `w` either of the two correctors of `e.def.w`,

```
  ( avsum_{z in 3^n Zd cap cu_K} E[ ‖grad w - (grad w)_{z+cu_n}‖^4_{L2bar(z+cu_n)} ] )^{1/4}
    + shom_{m-h}^{-1} 3^n E[ ‖grad(k_m - k_{m-h})‖^4_{Linf(cu_{m-h})} ]^{1/4}
  <= C 3^{-(m-h-n)}
     + C shom_{m-h}^{-1} 3^{-(m-h-n)} 3^{gamma(m-h)} gamma^{-1}
     + C 3^{-(K-m+h)/4}
  <= gamma^{15} .
```

This module assembles the first inequality at the manuscript's own carriers: the
actual finite-volume Dirichlet and Neumann correctors on `cu_K`, the actual
fresh-shell forcing, the actual triadic meso grid of scale `n = m - h - N`, and
the actual shell-derivative gauge of `e.nabla.km.kn.infty`.

## The three consumed ingredients

* the per-site estimate `e.nablaw.oscillations` at the genuine carriers,
  `Corrector.exists_freshShellDirichlet_gradient_oscillation_interior_mesh_localGauge`
  and its Neumann mirror (module `OscillationAssemblyShell`);
* the fourth moment of the forcing gauge,
  `integral_shellDerivNormSum_rpow_four_le` and
  `mul_shellDerivNormSum_momentRoot_four_le_gap` (module
  `LocalizationOscillationTail`);
* the grid functional and its two-term majorant step,
  `gridFourthMomentRoot_le_add_of_le` (module
  `LocalizationOscillationGridMoment`), on the interior grid
  `interiorMesoCubeGrid` of `LocalizationGrid`.

## What is proved

* `meshOscillationCell`, `meshEnergyCell` -- the two per-cube quantities of the
  display, based at the cube's own site `triadicCubeShift R`.
* `openCubeAtScale_subset_of_mem_interiorMesoCubeGrid` -- membership in the
  interior grid at outer scale `n + N - 1` is exactly the containment
  `z + cu_{n+N} subset cu_K` that `e.nablaw.oscillations` needs.
* `integrable_shellDerivNormSum_rpow_four`,
  `gridFourthMoment_shellDerivNormSum_le` -- the forcing gauge is fourth-power
  integrable and its grid fourth moment obeys the uniform shell bound.
* `exists_freshShellDirichlet_gradient_oscillation_lower_bound_display` and
  `exists_freshShellNeumann_gradient_oscillation_lower_bound_display` -- the
  display itself, at the two correctors.

## Declared divergences from the printed statement

* **The grid is the interior grid.**  The manuscript averages over the
  unrestricted mesh `3^n Zd cap cu_K` while the preceding per-site estimate
  holds only where `z + cu_{m-h} subset cu_K`.  Averaging only over the
  interior mesh is the route taken here: the grid below is
  `interiorMesoCubeGrid d K n (n + N - 1)`.  Consequently **the printed third
  term `C 3^{-(K-m+h)/4}` does not appear**: there is no boundary contribution
  to bound.
* **The printed boundary exponent is unreachable anyway.**  The quarter
  exponent `3^{-(K-m+h)/4}` follows only from a uniform-in-window annealed
  fourth moment that is not available, and the global `L^8` envelope gives at
  best `3^{-(K-m+h)/8}`.  Nothing below asserts either exponent.
* **The gap restriction `d + 3 <= N`.**  The per-site estimate is the
  birth-scale telescope, not the false adjacent-cube `1/3`-contraction; its
  coarse leg needs a gap of at least `d + 3` scales.  The restriction is
  inherited verbatim and appears as an explicit hypothesis.
* **The forcing amplitude is sharper than printed.**  The printed second term
  carries `gamma^{-1}`; the bound below carries the number of telescope scales
  `N = m - h - n` on the oscillation leg and no factor at all on the standalone
  leg, with the absolute constant `shellDerivGammaFourthConst` of the class
  `Gamma_2`.  In the regime of `e.recurrence.params` one has `N <= 2
  gamma^{-1}` (`recurrenceGap_le_two_mul_inv`, module `LocalizationParams`,
  under its coverage gate), so the bound below implies the printed one up to
  the absolute factor `2`; nothing is weakened to match the printed form.
* **The forcing random variable is the dominating gauge, not the `L^infty`
  norm.**  Both on the left of the display and inside the per-site estimate, the
  manuscript's `‖grad(k_m - k_{m-h})‖_{Linf(z + cu_{m-h})}` is replaced by the
  summed first-derivative shell gauge `shellDerivNormSum`, which dominates it by
  the triangle inequality over the shells with no loss (see the carrier note of
  `LocalizationOscillationTail`).  The statements below therefore imply the
  printed ones and are stronger.  The standalone left-hand term is moreover
  stated at an arbitrary base point `z0`, of which the manuscript's untranslated
  `cu_{m-h}` is one instance.
* **The triangle step costs `8^{1/4}`.**  The manuscript's implicit Minkowski
  inequality in `L^4(counting x P)` has constant `1`; the elementary route used
  here has the absolute constant `8^{1/4}`, written out in
  `oscillationDisplayConst` and absorbed by the manuscript's dimension-only `C`.
* **The visible `sqrt d` and the explicit `sigmaInv`.**  The carrier `Vec d` is
  sup-normed while the shell gauge is Euclidean, so the forcing amplitude reads
  `sigmaInv * sqrt d * |e|_2`; the manuscript's `C` is dimension-only and absorbs
  the `sqrt d`.  The manuscript's `shom_{m-h}^{-1}` is the free nonnegative
  parameter `sigmaInv` here; no value is assumed for it.
* None of the three is assumed or asserted below.

## What is not proved here

**The meso-window energy average `hcoarse` is NOT discharged here.**  The
manuscript writes "by `e.nablaw.in.L.eight`", which controls the single global
normalized `L^8` norm of `grad w` on `cu_K`.  Passing from that to
`avsum_{z} E[ ‖grad w‖^4_{L2bar(z + cu_{m-h})} ]` requires a bounded-overlap
count: the windows `z + cu_{m-h}` indexed by the scale-`n` grid **overlap**, each
point of `cu_K` lying in `3^{d(m-h-n)}` of them, so the tiling identity
`cubeAverage_originCube_eq_mesoGridAverage` of `LocalizationGrid` -- which is a
partition statement -- does not apply.  The correct multiplicity is `3^{dN}` and
makes the constant `1`, but no covering lemma at ratio `3^N` is available in this
repository; `LocalizationGrid`'s transfer is at ratio `3` only.  The binder
`hcoarse` therefore carries the whole passage, visibly, at every instantiation
site.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The two per-cube quantities of the display -/

/-- The left-hand side of `e.nablaw.oscillations` at the cube `R`, based at the
cube's own site: `‖grad w - (grad w)_{z + cu_n}‖_{L2bar(z + cu_n)}`. -/
def meshOscillationCell (n : ℤ) (u : Vec d → Vec d) (R : TriadicCube d) : ℝ :=
  Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
    (openCubeAtScale (triadicCubeShift R) n) u)

/-- The coarse energy on the outer window of `e.nablaw.oscillations`:
`‖grad w‖_{L2bar(z + cu_{m-h})}`. -/
def meshEnergyCell (ell : ℤ) (u : Vec d → Vec d) (R : TriadicCube d) : ℝ :=
  Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
    (openCubeAtScale (triadicCubeShift R) ell) u 0)

theorem meshOscillationCell_nonneg (n : ℤ) (u : Vec d → Vec d) (R : TriadicCube d) :
    0 ≤ meshOscillationCell n u R := Real.sqrt_nonneg _

theorem meshEnergyCell_nonneg (ell : ℤ) (u : Vec d → Vec d) (R : TriadicCube d) :
    0 ≤ meshEnergyCell ell u R := Real.sqrt_nonneg _

/-! ## The interior grid supplies the containment of `e.nablaw.oscillations` -/

/-- **Membership in the interior grid at outer scale `n + N - 1` is the containment
`z + cu_{n+N} ⊆ cu_K`** printed. -/
theorem openCubeAtScale_subset_of_mem_interiorMesoCubeGrid {K n : ℤ} {N : ℕ}
    {R : TriadicCube d} (hR : R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1)) :
    openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)) ⊆ openCubeSet (originCube d K) := by
  have h := window_subset_of_mem_interiorMesoCubeGrid hR
  rw [show (n + (N : ℤ) - 1) + 1 = n + (N : ℤ) by ring] at h
  rwa [openCubeAtScale_eq_translateSet, openCubeAtScale_zero_eq_openCubeSet_originCube]

/-! ## The forcing gauge: integrability and the grid moment -/

/-- The forcing gauge of `e.nablaw.oscillations` is fourth-power integrable.  Same
route as `integral_shellDerivNormSum_rpow_four_le`: the weak-Orlicz tail
`e.nabla.km.kn.infty` at the translated cube, through CoarseGraining's
layer-cake bound. -/
theorem integrable_shellDerivNormSum_rpow_four (M : ABKModel d)
    {lowScale highScale : ℤ} (hlt : lowScale < highScale) (z : Vec d) :
    Integrable
      (fun omega : ShellSeq d => shellDerivNormSum lowScale highScale z omega ^ (4 : ℝ))
      M.P.toMeasure := by
  have hA : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 *
      (3 : ℝ) ^ ((M.gamma - 1) * (lowScale : ℝ)) := by
    have h3 : 0 < IndependentSums.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos
    positivity
  exact IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    (μ := M.P.toMeasure) (p := (4 : ℝ)) (by norm_num : (0 : ℝ) < 2) hA
    (by norm_num : (1 : ℝ) ≤ 4)
    (fun omega => shellDerivNormSum_nonneg lowScale highScale z omega)
    (measurable_shellDerivNormSum lowScale highScale z).aemeasurable
    (Provider.Stream.isBigOWith_gammaSigma_shellDerivNormSum_Ioc_translate M hlt z)

/-- **The grid fourth moment of the forcing gauge.**  The per-site bound of
`integral_shellDerivNormSum_rpow_four_le` is uniform in the base point, so it
survives the grid average unchanged. -/
theorem gridFourthMoment_shellDerivNormSum_le (M : ABKModel d)
    (I : Finset (TriadicCube d)) {lowScale highScale : ℤ} (hlt : lowScale < highScale) :
    gridFourthMoment M.P.toMeasure I
        (fun R omega => shellDerivNormSum lowScale highScale (triadicCubeShift R) omega) ≤
      (shellDerivGammaFourthConst * (3 : ℝ) ^ ((M.gamma - 1) * (lowScale : ℝ))) ^ (4 : ℕ) := by
  have hpos : (0 : ℝ) < shellDerivGammaFourthConst := shellDerivGammaFourthConst_pos
  refine gridFourthMoment_le_of_forall_le _ I _ (by positivity) fun R _ => ?_
  refine (integral_shellDerivNormSum_rpow_four_le M hlt (triadicCubeShift R)).trans_eq ?_
  exact rpow_four_eq_pow_four _

/-! ## The constant of the display -/

/-- The absolute constant of the display: the `8^{1/4}` of the elementary
triangle step, the dimension-only constant `C` of `e.nablaw.oscillations`, and
the `Gamma_2` fourth-moment constant of the forcing gauge, combined so that a
single constant dominates all three terms. -/
def oscillationDisplayConst (C : ℝ) : ℝ :=
  (8 : ℝ) ^ ((4 : ℝ)⁻¹) * (C + 1) * (shellDerivGammaFourthConst + 1) +
    shellDerivGammaFourthConst

theorem oscillationDisplayConst_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ oscillationDisplayConst C := by
  have hS : (0 : ℝ) < shellDerivGammaFourthConst := shellDerivGammaFourthConst_pos
  have hE8 : (0 : ℝ) ≤ (8 : ℝ) ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg (by norm_num) _
  unfold oscillationDisplayConst
  have : (0 : ℝ) ≤ (8 : ℝ) ^ ((4 : ℝ)⁻¹) * (C + 1) * (shellDerivGammaFourthConst + 1) :=
    mul_nonneg (mul_nonneg hE8 (by linarith)) (by linarith)
  linarith

/-! ## The core assembly -/

/-- **The display, from the per-site estimate.**  Everything specific to the
Dirichlet or Neumann leg has been abstracted into the hypothesis `hcell`, which
is exactly the conclusion of `e.nablaw.oscillations` at the genuine carriers. -/
private theorem oscillation_lower_bound_display_core (M : ABKModel d) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀) (K n : ℤ) (N : ℕ) {highScale : ℤ} (hlt : n + (N : ℤ) < highScale)
    {sigmaInv : ℝ} (hsigma : 0 ≤ sigmaInv) (e z₀ : Vec d)
    (u : ShellSeq d → Vec d → Vec d) {W : ℝ} (hW : 0 ≤ W)
    (hcell : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1), ∀ omega : ShellSeq d,
      meshOscillationCell n (u omega) R ≤
        C₀ * (3 : ℝ) ^ (-(N : ℤ)) * meshEnergyCell (n + (N : ℤ)) (u omega) R +
          C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
            (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e *
              shellDerivNormSum (n + (N : ℤ)) highScale (triadicCubeShift R) omega)))
    (hcoarse : gridFourthMoment M.P.toMeasure
        (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
        (fun R omega => meshEnergyCell (n + (N : ℤ)) (u omega) R) ≤ W ^ (4 : ℕ))
    (hcoarseInt : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
      Integrable (fun omega : ShellSeq d =>
        meshEnergyCell (n + (N : ℤ)) (u omega) R ^ (4 : ℝ)) M.P.toMeasure) :
    gridFourthMomentRoot M.P.toMeasure (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
        (fun R omega => meshOscillationCell n (u omega) R) +
        sigmaInv * ((3 : ℝ) ^ ((n : ℝ)) *
          (∫ omega : ShellSeq d,
            shellDerivNormSum (n + (N : ℤ)) highScale z₀ omega ^ (4 : ℝ)
              ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)) ≤
      oscillationDisplayConst C₀ * ((3 : ℝ) ^ (-(N : ℝ)) * W) +
        oscillationDisplayConst C₀ *
            ((N : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e)) *
            ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) +
        oscillationDisplayConst C₀ * sigmaInv *
            ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) := by
  have hS : (0 : ℝ) < shellDerivGammaFourthConst := shellDerivGammaFourthConst_pos
  have hE8 : (0 : ℝ) ≤ (8 : ℝ) ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg (by norm_num) _
  have hnorm : (0 : ℝ) ≤ Book.Ch02.vecNorm e := Book.Ch02.vecNorm_nonneg e
  have h3z : (0 : ℝ) < (3 : ℝ) ^ (-(N : ℤ)) := zpow_pos (by norm_num) _
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hzN : (3 : ℝ) ^ (-(N : ℤ)) = (3 : ℝ) ^ (-(N : ℝ)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (-(N : ℤ))]
    norm_num
  have hzn : (3 : ℝ) ^ n = (3 : ℝ) ^ ((n : ℝ)) := (Real.rpow_intCast (3 : ℝ) n).symm
  have hcast : (((n + (N : ℤ)) : ℤ) : ℝ) = (n : ℝ) + (N : ℝ) := by push_cast; ring
  -- the two majorant families
  have hc1nn : (0 : ℝ) ≤ C₀ * (3 : ℝ) ^ (-(N : ℤ)) := mul_nonneg hC₀ h3z.le
  have hc2nn : (0 : ℝ) ≤ C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
      (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e)) :=
    mul_nonneg (mul_nonneg hC₀ (Nat.cast_nonneg N))
      (mul_nonneg h3n.le (mul_nonneg (mul_nonneg hsigma (Real.sqrt_nonneg _)) hnorm))
  have hle : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1), ∀ omega : ShellSeq d,
      meshOscillationCell n (u omega) R ≤
        (C₀ * (3 : ℝ) ^ (-(N : ℤ))) * meshEnergyCell (n + (N : ℤ)) (u omega) R +
          (C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
            (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) *
            shellDerivNormSum (n + (N : ℤ)) highScale (triadicCubeShift R) omega := by
    intro R hR omega
    refine (hcell R hR omega).trans_eq ?_
    ring
  have hGi : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
      Integrable (fun omega : ShellSeq d =>
        ((C₀ * (3 : ℝ) ^ (-(N : ℤ))) * meshEnergyCell (n + (N : ℤ)) (u omega) R) ^ (4 : ℝ))
        M.P.toMeasure := by
    intro R hR
    refine ((hcoarseInt R hR).const_mul ((C₀ * (3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ))).congr
      (Filter.Eventually.of_forall fun omega => ?_)
    simp only [rpow_four_eq_pow_four]
    ring
  have hHi : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
      Integrable (fun omega : ShellSeq d =>
        ((C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
            (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) *
          shellDerivNormSum (n + (N : ℤ)) highScale (triadicCubeShift R) omega) ^ (4 : ℝ))
        M.P.toMeasure := by
    intro R _
    refine ((integrable_shellDerivNormSum_rpow_four M hlt (triadicCubeShift R)).const_mul
      ((C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
        (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) ^ (4 : ℕ))).congr
      (Filter.Eventually.of_forall fun omega => ?_)
    simp only [rpow_four_eq_pow_four]
    ring
  have hG : gridFourthMoment M.P.toMeasure (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
      (fun R omega => (C₀ * (3 : ℝ) ^ (-(N : ℤ))) *
        meshEnergyCell (n + (N : ℤ)) (u omega) R) ≤
      ((C₀ * (3 : ℝ) ^ (-(N : ℤ))) * W) ^ (4 : ℕ) := by
    rw [gridFourthMoment_const_mul]
    calc (C₀ * (3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ) *
          gridFourthMoment M.P.toMeasure (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
            (fun R omega => meshEnergyCell (n + (N : ℤ)) (u omega) R)
        ≤ (C₀ * (3 : ℝ) ^ (-(N : ℤ))) ^ (4 : ℕ) * W ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_left hcoarse (pow_nonneg hc1nn 4)
      _ = ((C₀ * (3 : ℝ) ^ (-(N : ℤ))) * W) ^ (4 : ℕ) := (mul_pow _ _ 4).symm
  have hH : gridFourthMoment M.P.toMeasure (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
      (fun R omega => (C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
          (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) *
        shellDerivNormSum (n + (N : ℤ)) highScale (triadicCubeShift R) omega) ≤
      ((C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
          (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) *
        (shellDerivGammaFourthConst *
          (3 : ℝ) ^ ((M.gamma - 1) * (((n + (N : ℤ)) : ℤ) : ℝ)))) ^ (4 : ℕ) := by
    rw [gridFourthMoment_const_mul]
    calc (C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
            (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) ^ (4 : ℕ) *
          gridFourthMoment M.P.toMeasure (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
            (fun R omega =>
              shellDerivNormSum (n + (N : ℤ)) highScale (triadicCubeShift R) omega)
        ≤ (C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
            (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) ^ (4 : ℕ) *
            (shellDerivGammaFourthConst *
              (3 : ℝ) ^ ((M.gamma - 1) * (((n + (N : ℤ)) : ℤ) : ℝ))) ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_left
            (gridFourthMoment_shellDerivNormSum_le M _ hlt) (pow_nonneg hc2nn 4)
      _ = ((C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
            (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) *
          (shellDerivGammaFourthConst *
            (3 : ℝ) ^ ((M.gamma - 1) * (((n + (N : ℤ)) : ℤ) : ℝ)))) ^ (4 : ℕ) :=
          (mul_pow _ _ 4).symm
  have hroot := gridFourthMomentRoot_le_add_of_le M.P.toMeasure
    (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
    (fun R omega => meshOscillationCell n (u omega) R)
    (fun R omega => (C₀ * (3 : ℝ) ^ (-(N : ℤ))) *
      meshEnergyCell (n + (N : ℤ)) (u omega) R)
    (fun R omega => (C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
        (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) *
      shellDerivNormSum (n + (N : ℤ)) highScale (triadicCubeShift R) omega)
    (mul_nonneg hc1nn hW)
    (mul_nonneg hc2nn (mul_nonneg hS.le (Real.rpow_nonneg (by norm_num) _)))
    (fun R _ omega => meshOscillationCell_nonneg n (u omega) R) hle hGi hHi hG hH
  have hstand := mul_le_mul_of_nonneg_left
    (mul_shellDerivNormSum_momentRoot_four_le_gap M hlt z₀) hsigma
  -- the three constant comparisons
  have hC1 : (8 : ℝ) ^ ((4 : ℝ)⁻¹) * C₀ ≤ oscillationDisplayConst C₀ := by
    unfold oscillationDisplayConst
    linarith only [mul_nonneg (mul_nonneg hE8 hC₀) hS.le, mul_nonneg hE8 hS.le,
      hE8, hS.le]
  have hC2 : (8 : ℝ) ^ ((4 : ℝ)⁻¹) * C₀ * shellDerivGammaFourthConst ≤
      oscillationDisplayConst C₀ := by
    unfold oscillationDisplayConst
    linarith only [mul_nonneg hE8 hC₀, mul_nonneg hE8 hS.le, hE8, hS.le]
  have hC3 : shellDerivGammaFourthConst ≤ oscillationDisplayConst C₀ := by
    unfold oscillationDisplayConst
    exact le_add_of_nonneg_left
      (mul_nonneg (mul_nonneg hE8 (by linarith : (0:ℝ) ≤ C₀ + 1))
        (by linarith : (0:ℝ) ≤ shellDerivGammaFourthConst + 1))
  -- the three term-by-term estimates
  have hXnn : (0 : ℝ) ≤ (N : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e) :=
    mul_nonneg (Nat.cast_nonneg N)
      (mul_nonneg (mul_nonneg hsigma (Real.sqrt_nonneg _)) hnorm)
  have hYnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(N : ℝ)) *
      (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ))) := by positivity
  have hterm1 : (8 : ℝ) ^ ((4 : ℝ)⁻¹) * ((C₀ * (3 : ℝ) ^ (-(N : ℤ))) * W) ≤
      oscillationDisplayConst C₀ * ((3 : ℝ) ^ (-(N : ℝ)) * W) := by
    have hXW : (0 : ℝ) ≤ (3 : ℝ) ^ (-(N : ℝ)) * W :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hW
    calc (8 : ℝ) ^ ((4 : ℝ)⁻¹) * ((C₀ * (3 : ℝ) ^ (-(N : ℤ))) * W)
        = ((8 : ℝ) ^ ((4 : ℝ)⁻¹) * C₀) * ((3 : ℝ) ^ (-(N : ℝ)) * W) := by
          rw [hzN]; ring
      _ ≤ oscillationDisplayConst C₀ * ((3 : ℝ) ^ (-(N : ℝ)) * W) :=
          mul_le_mul_of_nonneg_right hC1 hXW
  have hterm2 : (8 : ℝ) ^ ((4 : ℝ)⁻¹) *
        ((C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
            (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) *
          (shellDerivGammaFourthConst *
            (3 : ℝ) ^ ((M.gamma - 1) * (((n + (N : ℤ)) : ℤ) : ℝ)))) ≤
      oscillationDisplayConst C₀ *
        ((N : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e)) *
        ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) := by
    calc (8 : ℝ) ^ ((4 : ℝ)⁻¹) *
          ((C₀ * (N : ℝ) * ((3 : ℝ) ^ n *
              (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e))) *
            (shellDerivGammaFourthConst *
              (3 : ℝ) ^ ((M.gamma - 1) * (((n + (N : ℤ)) : ℤ) : ℝ))))
        = ((8 : ℝ) ^ ((4 : ℝ)⁻¹) * C₀ * shellDerivGammaFourthConst) *
            (((N : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e)) *
              ((3 : ℝ) ^ ((n : ℝ)) *
                (3 : ℝ) ^ ((M.gamma - 1) * ((n : ℝ) + (N : ℝ))))) := by
          rw [hcast, hzn]; ring
      _ = ((8 : ℝ) ^ ((4 : ℝ)⁻¹) * C₀ * shellDerivGammaFourthConst) *
            (((N : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e)) *
              ((3 : ℝ) ^ (-(N : ℝ)) *
                (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ))))) := by
          rw [rpow_gap_factorization M.gamma n N]
      _ ≤ oscillationDisplayConst C₀ *
            (((N : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e)) *
              ((3 : ℝ) ^ (-(N : ℝ)) *
                (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ))))) :=
          mul_le_mul_of_nonneg_right hC2 (mul_nonneg hXnn hYnn)
      _ = oscillationDisplayConst C₀ *
            ((N : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e)) *
            ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) := by
          ring
  have hterm3 : sigmaInv * (shellDerivGammaFourthConst *
        ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ))))) ≤
      oscillationDisplayConst C₀ * sigmaInv *
        ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) := by
    calc sigmaInv * (shellDerivGammaFourthConst *
          ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))))
        = shellDerivGammaFourthConst * (sigmaInv *
            ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ))))) := by ring
      _ ≤ oscillationDisplayConst C₀ * (sigmaInv *
            ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ))))) :=
          mul_le_mul_of_nonneg_right hC3 (mul_nonneg hsigma hYnn)
      _ = oscillationDisplayConst C₀ * sigmaInv *
            ((3 : ℝ) ^ (-(N : ℝ)) * (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) := by ring
  linarith [hroot, hstand, hterm1, hterm2, hterm3]

/-! ## The display at the two correctors -/

/-- **`e.lower.bound.oscillations` for the Dirichlet corrector of `e.def.w`, on the
interior meso grid.**

The second printed term is proved in the sharper form carrying `N = m - h - n`
instead of `gamma^{-1}`.

**Conditional A.**  The caller supplies `hd : 0 < d`, the telescope gap `hN: d
+ 3 ≤ N`, the nonempty shell range `hlt: n + N < highScale`, `hsigma: 0 ≤
sigmaInv` for `shom_{m-h}^{-1}`, the weak-solution property `hwD` of `e.def.w`
at every sample, and the two propositions `hcoarse`, `hcoarseInt` about the
meso-window corrector energies.  `hcoarse` is the manuscript's "by
`e.nablaw.in.L.eight`" step and is **not** discharged here; see the module's
open obstruction. -/
theorem exists_freshShellDirichlet_gradient_oscillation_lower_bound_display (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : ABKModel d) (K n : ℤ) (N : ℕ), d + 3 ≤ N →
        ∀ highScale : ℤ, n + (N : ℤ) < highScale →
          ∀ sigmaInv : ℝ, 0 ≤ sigmaInv →
            ∀ (e z₀ : Vec d)
              (wD : ShellSeq d → H10Function (openCubeSet (originCube d K))),
              (∀ omega : ShellSeq d,
                IsZeroTraceDirichletRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet (originCube d K)) (wD omega)
                  fun x =>
                    -Corrector.streamForcing sigmaInv omega (n + (N : ℤ)) highScale e x) →
              ∀ W : ℝ, 0 ≤ W →
                gridFourthMoment M.P.toMeasure
                    (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
                    (fun R omega => meshEnergyCell (n + (N : ℤ))
                      (wD omega).toH1Function.grad R) ≤ W ^ (4 : ℕ) →
                (∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
                  Integrable (fun omega : ShellSeq d => meshEnergyCell (n + (N : ℤ))
                    (wD omega).toH1Function.grad R ^ (4 : ℝ)) M.P.toMeasure) →
                gridFourthMomentRoot M.P.toMeasure
                    (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
                    (fun R omega => meshOscillationCell n
                      (wD omega).toH1Function.grad R) +
                    sigmaInv * ((3 : ℝ) ^ ((n : ℝ)) *
                      (∫ omega : ShellSeq d,
                        shellDerivNormSum (n + (N : ℤ)) highScale z₀ omega ^ (4 : ℝ)
                          ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)) ≤
                  C * ((3 : ℝ) ^ (-(N : ℝ)) * W) +
                    C * ((N : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e)) *
                      ((3 : ℝ) ^ (-(N : ℝ)) *
                        (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) +
                    C * sigmaInv *
                      ((3 : ℝ) ^ (-(N : ℝ)) *
                        (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) := by
  obtain ⟨C₀, hC₀, hC⟩ :=
    Corrector.exists_freshShellDirichlet_gradient_oscillation_interior_mesh_localGauge hd
  refine ⟨oscillationDisplayConst C₀, oscillationDisplayConst_nonneg hC₀, ?_⟩
  intro M K n N hN highScale hlt sigmaInv hsigma e z₀ wD hwD W hW hcoarse hcoarseInt
  refine oscillation_lower_bound_display_core M hC₀ K n N hlt hsigma e z₀
    (fun omega => (wD omega).toH1Function.grad) hW ?_ hcoarse hcoarseInt
  intro R hR omega
  exact hC K n N hN (triadicCubeShift R)
    (openCubeAtScale_subset_of_mem_interiorMesoCubeGrid hR) sigmaInv hsigma omega
    (n + (N : ℤ)) highScale e (wD omega) (hwD omega)

/-- **`e.lower.bound.oscillations` for the Neumann corrector of `e.def.w`, on the
interior meso grid.**  The Neumann mirror of the previous statement; the
manuscript's "the same results are valid for `w_{N,e'}^{(K)}`".

**Conditional A.**  The binders are those of the Dirichlet leg, with `hwN` the
mean-zero Neumann weak-solution property in place of the zero-trace one. -/
theorem exists_freshShellNeumann_gradient_oscillation_lower_bound_display (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : ABKModel d) (K n : ℤ) (N : ℕ), d + 3 ≤ N →
        ∀ highScale : ℤ, n + (N : ℤ) < highScale →
          ∀ sigmaInv : ℝ, 0 ≤ sigmaInv →
            ∀ (e' z₀ : Vec d)
              (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d K))),
              (∀ omega : ShellSeq d,
                IsMeanZeroNeumannRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet (originCube d K)) (wN omega)
                  fun x =>
                    -Corrector.streamForcing sigmaInv omega (n + (N : ℤ)) highScale e' x) →
              ∀ W : ℝ, 0 ≤ W →
                gridFourthMoment M.P.toMeasure
                    (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
                    (fun R omega => meshEnergyCell (n + (N : ℤ))
                      (wN omega).toH1Function.grad R) ≤ W ^ (4 : ℕ) →
                (∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
                  Integrable (fun omega : ShellSeq d => meshEnergyCell (n + (N : ℤ))
                    (wN omega).toH1Function.grad R ^ (4 : ℝ)) M.P.toMeasure) →
                gridFourthMomentRoot M.P.toMeasure
                    (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
                    (fun R omega => meshOscillationCell n
                      (wN omega).toH1Function.grad R) +
                    sigmaInv * ((3 : ℝ) ^ ((n : ℝ)) *
                      (∫ omega : ShellSeq d,
                        shellDerivNormSum (n + (N : ℤ)) highScale z₀ omega ^ (4 : ℝ)
                          ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)) ≤
                  C * ((3 : ℝ) ^ (-(N : ℝ)) * W) +
                    C * ((N : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e')) *
                      ((3 : ℝ) ^ (-(N : ℝ)) *
                        (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) +
                    C * sigmaInv *
                      ((3 : ℝ) ^ (-(N : ℝ)) *
                        (3 : ℝ) ^ (M.gamma * ((n : ℝ) + (N : ℝ)))) := by
  obtain ⟨C₀, hC₀, hC⟩ :=
    Corrector.exists_freshShellNeumann_gradient_oscillation_interior_mesh_localGauge hd
  refine ⟨oscillationDisplayConst C₀, oscillationDisplayConst_nonneg hC₀, ?_⟩
  intro M K n N hN highScale hlt sigmaInv hsigma e' z₀ wN hwN W hW hcoarse hcoarseInt
  refine oscillation_lower_bound_display_core M hC₀ K n N hlt hsigma e' z₀
    (fun omega => (wN omega).toH1Function.grad) hW ?_ hcoarse hcoarseInt
  intro R hR omega
  exact hC K n N hN (triadicCubeShift R)
    (openCubeAtScale_subset_of_mem_interiorMesoCubeGrid hR) sigmaInv hsigma omega
    (n + (N : ℤ)) highScale e' (wN omega) (hwN omega)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
