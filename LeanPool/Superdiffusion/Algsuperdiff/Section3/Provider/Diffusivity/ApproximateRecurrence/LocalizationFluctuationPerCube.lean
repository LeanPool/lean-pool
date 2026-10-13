/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledPairingResponse
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationDuality
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Variational.PerCubeFluctuationArithmetic

/-!
# LocalizationFluctuationPerCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cube fluctuation bound of Step 2, at the localization carriers

Source displays in ABK26, inside Step 2 of `l.approximate.recurrence.formula`:

* The Euler--Lagrange identity and the block Besov duality bound (proved as
  `LocalizationFluctuationDuality.two_mul_doubledMuValue_le_besovDualityConst_localizationFz`);
* The doubled coarse Poincare inequality (proved as
`partialSeminormTwo_blockGaugeDown_le_of_isDoubledResponseField`);
* The self-improvement that cancels one power of `|| bfA_m^{1/2} tilde S_z
  ||`, the cross-term bound;
* The display `e.lower.bound.localization.terms`, whose bracketed integrand is
  `2 P_z.
  fint bfA_m tilde S_z + fint tilde S_z. bfA_m tilde S_z` -- verbatim the two
  fluctuation summands of
`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`.

## What is proved

```
2 (kappa Theta^2) | bfAhom^{1/2} P_z | Bg  +  (kappa Theta Bg)^2 ,
```

`kappa = besovDualityConst R s` being the pinned constant, `Theta =
doubledPoincareEllipticityFactor` the factor of `e.CG.Poincare.doubled.vars`, and
`Bg` any envelope of the finite-depth positive `q = 2` Besov seminorms of the
gauged `bfF_z`.

The cross term is taken by the depth-zero route
(`CoarseEllipticity.abs_blockVecDot_cubeAverage_le`), after the gauge
conjugation.

## Binders

Beyond the geometry (`hsub`), the defining property of `w_{N,e'}^{(K)}`
(`hwN`), the names of `tilde S_z` (`hT`, `hresp`) and the exponent/gauge
windows `0 < s < 1`, `0 < sigma_0`, the hypotheses are the **analytic side
conditions of the two consumed displays**: four `L^2` memberships, two
integrabilities of the gauged pairing integrands, the sign of `Bg` and the two
positive-seminorm envelopes.  They are conditional A obligations of this
module, discharged by the caller at its carrier, and are not premises of the
pinned source statement.  No smallness, moment or measurability proposition
occurs.

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Variational
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Integrability of the coordinates of an `L^2` field -/

/-- A field in `L^2` of the normalized cube measure has integrable coordinates on
the cube. -/
theorem integrableOn_cubeSet_coord_of_memLp_two (Q : TriadicCube d) {u : Vec d → Vec d}
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) (i : Fin d) :
    IntegrableOn (fun x => u x i) (cubeSet Q) volume := by
  have hint : Integrable u (normalizedCubeMeasure Q) := hu.integrable (by norm_num)
  have hne : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.mpr (cubeVolume_pos Q)
  have htop : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [normalizedCubeMeasure, integrable_smul_measure hne htop, cubeMeasure] at hint
  exact ContinuousLinearMap.integrable_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) hint

/-- A linear functional of an `L^2` field is integrable on the cube. -/
theorem integrableOn_const_vecDot (Q : TriadicCube d) (u : Vec d → Vec d) (c : Vec d)
    (hu : ∀ i, IntegrableOn (fun x => u x i) (cubeSet Q) volume) :
    IntegrableOn (fun x => vecDot c (u x)) (cubeSet Q) volume := by
  unfold vecDot
  exact integrable_finsetSum Finset.univ fun i _ => (hu i).const_mul (c i)

/-- The cube average of a linear functional of a field is the functional of the
cube average. -/
theorem cubeAverage_const_vecDot (Q : TriadicCube d) (u : Vec d → Vec d) (c : Vec d)
    (hu : ∀ i, IntegrableOn (fun x => u x i) (cubeSet Q) volume) :
    cubeAverage Q (fun x => vecDot c (u x)) = vecDot c (cubeAverageVec Q u) := by
  unfold cubeAverage vecDot cubeAverageVec
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => (hu i).const_mul (c i)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul]
  unfold cubeAverage
  ring

/-! ## The cross term by the depth-zero route -/

/-- ** at the localization cell, after the gauge conjugation.**

```
| fint_R P_z . bfA_m tilde S_z |  <=  | bfAhom^{1/2} P_z | * Bu
```

for any envelope `Bu` of the finite-depth negative `q = 2` Besov seminorms of
the two components of `bfAhom^{-1/2} bfA_m tilde S_z`, the doubled norm being
read in the component-sum rendering `blockVecNormSum`.

: the two `L^2` memberships and the two envelopes are caller obligations. -/
theorem abs_cubeAverage_blockVecDot_const_le (R : TriadicCube d) (s : ℝ) {sig0 : ℝ}
    (hsig0 : 0 < sig0) (P : BlockVec d) (Y : Vec d → BlockVec d) {Bu : ℝ}
    (hY1 : MemLp (fun x => (Y x).1) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hY2 : MemLp (fun x => (Y x).2) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hneg1 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeDown sig0 (Y x)).1) ≤ Bu)
    (hneg2 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeDown sig0 (Y x)).2) ≤ Bu) :
    |cubeAverage R (fun x => blockVecDot P (Y x))| ≤
      blockVecNormSum (blockGaugeUp sig0 P) * Bu := by
  have hsq : Real.sqrt sig0 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsig0)
  -- the coordinate integrabilities of the gauged field
  have hg1 : ∀ i, IntegrableOn (fun x => (blockGaugeDown sig0 (Y x)).1 i) (cubeSet R)
      volume := by
    intro i
    have h := integrableOn_cubeSet_coord_of_memLp_two R hY1 i
    have hfun : (fun x => (blockGaugeDown sig0 (Y x)).1 i) =
        fun x => (Real.sqrt sig0)⁻¹ * (Y x).1 i := by
      funext x; simp [blockGaugeDown]
    rw [hfun]
    exact h.const_mul _
  have hg2 : ∀ i, IntegrableOn (fun x => (blockGaugeDown sig0 (Y x)).2 i) (cubeSet R)
      volume := by
    intro i
    have h := integrableOn_cubeSet_coord_of_memLp_two R hY2 i
    have hfun : (fun x => (blockGaugeDown sig0 (Y x)).2 i) =
        fun x => Real.sqrt sig0 * (Y x).2 i := by
      funext x; simp [blockGaugeDown]
    rw [hfun]
    exact h.const_mul _
  -- the pointwise gauge conjugation
  have hpt : (fun x => blockVecDot P (Y x)) =
      fun x => vecDot ((blockGaugeUp sig0 P).1) ((blockGaugeDown sig0 (Y x)).1) +
        vecDot ((blockGaugeUp sig0 P).2) ((blockGaugeDown sig0 (Y x)).2) := by
    funext x
    have h := blockVecDot_blockGaugeDown_blockGaugeUp hsig0 (Y x) P
    rw [CoarseEllipticity.blockVecDot_comm P (Y x), ← h,
      CoarseEllipticity.blockVecDot_comm (blockGaugeDown sig0 (Y x)) (blockGaugeUp sig0 P)]
    rfl
  rw [hpt,
    cubeAverage_add_of_integrableOn R _ _
      (integrableOn_const_vecDot R _ _ hg1) (integrableOn_const_vecDot R _ _ hg2),
    cubeAverage_const_vecDot R _ _ hg1, cubeAverage_const_vecDot R _ _ hg2]
  exact abs_blockVecDot_cubeAverage_le R s (blockGaugeUp sig0 P)
    (fun x => blockGaugeDown sig0 (Y x)) hneg1 hneg2

/-! ## The pinned duality constant is nonnegative -/

theorem besovDualityConst_nonneg (R : TriadicCube d) (s : ℝ) :
    0 ≤ besovDualityConst R s := by
  unfold besovDualityConst cubeBesovScaleWeight
  have hf : (0 : ℝ) < cubeScaleFactor R := cubeScaleFactor_pos' R
  have h1 : (0 : ℝ) ≤ Real.rpow (cubeScaleFactor R) (-(-s)) := Real.rpow_nonneg hf.le _
  have h2 : (0 : ℝ) ≤ Real.rpow (cubeScaleFactor R) (-s) := Real.rpow_nonneg hf.le _
  have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((d : ℝ) + s) :=
    Real.rpow_nonneg (by norm_num) _
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  positivity

/-! ## The per-cube bound -/

/-- **The bracketed integrand on one mesoscopic cell.**

```
2 P_z . fint_R bfA_m tilde S_z + 2 mu_R(tilde S_z)
  <= 2 kappa Theta^2 | bfAhom^{1/2} P_z | Bg + (kappa Theta Bg)^2 ,
```

`kappa = besovDualityConst R s`, `Theta = doubledPoincareEllipticityFactor`,
and `Bg` an envelope of the finite-depth positive `q = 2` Besov seminorms of
the gauged `bfF_z`.  The two summands carry exactly the manuscript's power of
the ellipticity factor: once in the cross term and once in the quadratic term.

The left-hand side is verbatim the fluctuation part of the integrand of
`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`.

as described in the module docstring. -/
theorem perCube_localizationFluctuation_le [NeZero d] (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wD : H10Function (openCubeSet Q)) {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x))
    (af : TriadicCoeffFamily d) {T : DoubledField d} (P : BlockVec d)
    (hT : IsDoubledMuMinimizerField (cubeDomain R) (af.coeffOn R)
      (localizationFz sigma omega lowScale highScale e' R wD wN) T)
    (hresp : IsDoubledResponseField (cubeDomain R) (af.coeffOn R) T)
    {s sig0 Bg : ℝ} (hs : 0 < s) (hs1 : s < 1) (hsig0 : 0 < sig0) (hBg : 0 ≤ Bg)
    (hwDmem : MemLp wD.toH1Function.grad (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hwNmem : MemLp (neumannFluxField sigma omega lowScale highScale e' wN) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R))
    (hY1 : MemLp
      (fun x => (blockMatVecMul (blockMatrixField (af.coeffOn R) x) (T.eval x)).1)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hY2 : MemLp
      (fun x => (blockMatVecMul (blockMatrixField (af.coeffOn R) x) (T.eval x)).2)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hF1 : MemLp
      (fun x => ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x).1)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hF2 : MemLp
      (fun x => ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x).2)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hInt1 : IntegrableOn
      (fun x =>
        vecDot ((blockGaugeDown sig0
            (blockMatVecMul (blockMatrixField (af.coeffOn R) x) (T.eval x))).1)
          (cubeFluctuationVec R
            (fun y => (blockGaugeUp sig0
              ((localizationFz sigma omega lowScale highScale e' R wD wN).eval y)).1) x))
      (cubeSet R) volume)
    (hInt2 : IntegrableOn
      (fun x =>
        vecDot ((blockGaugeDown sig0
            (blockMatVecMul (blockMatrixField (af.coeffOn R) x) (T.eval x))).2)
          (cubeFluctuationVec R
            (fun y => (blockGaugeUp sig0
              ((localizationFz sigma omega lowScale highScale e' R wD wN).eval y)).2) x))
      (cubeSet R) volume)
    (hpos1 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeUp sig0
        ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x)).1) ≤ Bg)
    (hpos2 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeUp sig0
        ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x)).2) ≤ Bg) :
    2 * volumeAverage (openCubeSet R) (fun x =>
          blockVecDot P (blockMatVecMul (blockMatrixField (af.coeffOn R) x) (T.eval x))) +
        2 * doubledMuValue (cubeDomain R) (af.coeffOn R) T ≤
      2 * (besovDualityConst R s * doubledPoincareEllipticityFactor sig0 R af s *
            doubledPoincareEllipticityFactor sig0 R af s) *
          blockVecNormSum (blockGaugeUp sig0 P) * Bg +
        (besovDualityConst R s * doubledPoincareEllipticityFactor sig0 R af s * Bg) *
          (besovDualityConst R s * doubledPoincareEllipticityFactor sig0 R af s * Bg) := by
  obtain ⟨hmu0, hneg1, hneg2⟩ :=
    partialSeminormTwo_blockGaugeDown_le_of_isDoubledResponseField R af hs hs1 hsig0 hresp
  -- the Poincare envelope, used as the value of `Bu`
  have hblockE0 : (0 : ℝ) ≤
      Real.sqrt (2 * doubledMuValue (cubeDomain R) (af.coeffOn R) T) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (2 * doubledMuValue (cubeDomain R) (af.coeffOn R) T) *
      Real.sqrt (2 * doubledMuValue (cubeDomain R) (af.coeffOn R) T) =
      2 * doubledMuValue (cubeDomain R) (af.coeffOn R) T :=
    Real.mul_self_sqrt (by linarith)
  -- the duality leg
  have hquad := two_mul_doubledMuValue_le_besovDualityConst_localizationFz sigma omega
    lowScale highScale e' R hsub wD hwN hT hs hsig0 hBg hwDmem hwNmem hY1 hY2 hF1 hF2
    hInt1 hInt2 hneg1 hneg2 hpos1 hpos2
  -- the cross leg
  have hcrossabs := abs_cubeAverage_blockVecDot_const_le R s hsig0 P
    (fun x => blockMatVecMul (blockMatrixField (af.coeffOn R) x) (T.eval x))
    hY1 hY2 hneg1 hneg2
  have hcross : volumeAverage (openCubeSet R) (fun x =>
        blockVecDot P (blockMatVecMul (blockMatrixField (af.coeffOn R) x) (T.eval x))) ≤
      blockVecNormSum (blockGaugeUp sig0 P) *
        (doubledPoincareEllipticityFactor sig0 R af s *
          Real.sqrt (2 * doubledMuValue (cubeDomain R) (af.coeffOn R) T)) := by
    rw [volumeAverage_openCubeSet_eq_cubeAverage R]
    exact (le_abs_self _).trans hcrossabs
  exact perCube_fluct_le (blockVecNormSum_nonneg _) (besovDualityConst_nonneg R s) hBg
    (doubledPoincareEllipticityFactor_nonneg sig0 R af hs) hblockE0 hsq hcross hquad
    le_rfl rfl

/-- **The per-cube bound with the ellipticity factor in the gauged form.**  The
square of the Poincare factor is replaced by `32 c_{s,2}^{-1}` times
`gaugedEllipticitySum`, which is the quantity the ellipticity display then
transfers from the mesoscopic cell to the recurrence scale by
`gaugedEllipticitySum_descendant_le`. -/
theorem doubledPoincareEllipticityFactor_sq_le_gaugedEllipticitySum [NeZero d]
    (R : TriadicCube d) (af : TriadicCoeffFamily d) {s sig0 : ℝ} (hs : 0 < s)
    (hsig0 : 0 < sig0) :
    doubledPoincareEllipticityFactor sig0 R af s *
        doubledPoincareEllipticityFactor sig0 R af s ≤
      32 * (Ch03.poincareDiscountFactor s (.finite 2) *
          Ch03.poincareDiscountFactor s (.finite 2)) *
        gaugedEllipticitySum sig0 R s af := by
  have h := doubledPoincareEllipticityFactor_sq_le (sig0 := sig0) R af hs hsig0
  unfold gaugedEllipticitySum
  exact h

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
