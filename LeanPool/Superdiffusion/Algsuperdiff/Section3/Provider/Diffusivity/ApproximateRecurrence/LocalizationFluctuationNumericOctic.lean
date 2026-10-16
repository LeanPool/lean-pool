/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationCellIntegrable
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationGridEighth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableOctic

/-!
# LocalizationFluctuationNumericOctic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hmem8`: the `L^2`-in-the-sample membership of the oscillation cells

`LocalizationOscillationFullMesh` carries two `e.nablaw.in.L.eight` side
conditions into the Step-5 shape.  The first of them is

```
  forall R in the mesh,
    MemLp (fun omega => osc(z_R + cu_n; grad w_omega) ^ 4) 2 P ,
```

i.e. the finiteness of the **eighth** moment of the oscillation cell together
with its measurability in the sample.  This module discharges it.

## The two halves

**Measurability.**  `CorrectorMeasurableQuartic` and
`LocalizationFluctuationCellIntegrable` supply the quartic and the quadratic
window observables; what the *oscillation* cell needs on top of the quadratic
one is the **centring**, and the centring is a difference of two window
observables:

```
  osc^2(V; u) = fint_V |u|^2 - |fint_V u|^2 ,
```

`meanSquareOscillationVecOn_eq_sub_vecNormSq_volumeAverageVec` below.  The first
term is measurable by
`measurable_volumeAverage_vecNormSq_freshShellDirichletGrad`; the second is a
finite sum of squares of the *linear* window observables of
`Corrector.measurable_setIntegral_gradCoordL2`, which are continuous.  So the
oscillation cell -- more precisely its fourth power, which is `osc^2` squared
and therefore free of the square root -- is measurable in the sample.

**Finiteness.**  Domination, exactly as in
`LocalizationFluctuationCellIntegrable`, one power up:

```
  osc^8 <= fint_{z+cu_n} |u|^8                         (per-cell Jensen)
        <= |cu_K| |z+cu_n|^{-1} fint_{cu_K} |u|^8      (window <= cube)
         = |cu_K| |z+cu_n|^{-1} (‖u‖^2_{L8bar(cu_K)})^4
        <= |cu_K| |z+cu_n|^{-1} (Chead + T')^4 ,
```

with `T' = max((fint_{cu_K} |u|^8)^{1/4} - Chead, 0)` the measurable dominating
fluctuation -- the octic analogue of the device of
`LocalizationFluctuationCellIntegrable`, measurable because
`CorrectorMeasurableOctic` makes `fint_{cu_K} |u|^8` measurable -- whose fourth
power is integrable from the `Gamma_1` tail of `e.nablaw.in.L.eight`
(`LocalizationFluctuationGridEighth.integrable_rpow_four_of_isBigOWith_gammaSigma_one`).

## Main results

* `meanSquareOscillationVecOn_eq_sub_vecNormSq_volumeAverageVec` -- the centring
  identity.
* `measurable_meshOscillationCell_rpow_four_freshShellDirichletGrad` and its
  Neumann mirror -- the fourth power of the oscillation cell is measurable in
  the sample.
* `exists_gamma0_memLp_two_freshShellDirichlet_meshOscillationCell_rpow_four`
  and its Neumann mirror -- the binder `hmem8` of
  `LocalizationOscillationFullMesh`, as a theorem.

## Scope

There is no `sorry`.

## References

* ABK26, `e.def.w`, `e.nablaw.oscillations`, `e.nablaw.in.L.eight`,
  `e.lower.bound.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The oscillation cell as a square -/

/-- The fourth power of the oscillation cell is the square of the mean-square
oscillation over the cell's own realization.

only on the scale identification `hsc`, which names the cell. -/
theorem meshOscillationCell_rpow_four_eq_sq {n : ℤ} (R : TriadicCube d)
    (hsc : R.scale = n) (u : Vec d → Vec d) :
    meshOscillationCell n u R ^ (4 : ℝ) =
      (Book.Ch01.meanSquareOscillationVecOn (openCubeSet R) u) ^ 2 := by
  have hwin : openCubeAtScale (triadicCubeShift R) n = openCubeSet R := by
    rw [← hsc]
    exact openCubeAtScale_triadicCubeShift_eq_openCubeSet R
  have hnn : (0 : ℝ) ≤ Book.Ch01.meanSquareOscillationVecOn (openCubeSet R) u :=
    Corrector.meanSquareOscillationVecOn_nonneg _ _
  rw [meshOscillationCell, hwin, rpow_four_eq_pow_four,
    show Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeSet R) u) ^ (4 : ℕ) =
      (Real.sqrt (Book.Ch01.meanSquareOscillationVecOn (openCubeSet R) u) ^ 2) ^ 2 by ring,
    Real.sq_sqrt hnn]

/-- The square of the fourth power of the oscillation cell is its eighth power.
Unconditional apart from the nonnegativity, which is automatic. -/
theorem sq_meshOscillationCell_rpow_four (n : ℤ) (u : Vec d → Vec d)
    (R : TriadicCube d) :
    (meshOscillationCell n u R ^ (4 : ℝ)) ^ 2 = meshOscillationCell n u R ^ (8 : ℕ) := by
  rw [rpow_four_eq_pow_four]
  ring

/-! ## Measurability of the oscillation cell -/

/-- A representative identified almost everywhere gives the same coordinate window integral. -/
theorem setIntegral_coordL2_eq_of_ae {U : Set (Vec d)}
    {F : HilbertVectorL2 U} {u : Vec d → Vec d}
    (hFu : (F : Vec d → HilbertVec d) =ᵐ[volumeMeasureOn U] hilbertifyVecField u)
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ U) (i : Fin d) :
    ∫ x in S, (F : Vec d → HilbertVec d) x i ∂(volumeMeasureOn U) =
      ∫ x in S, u x i ∂volume := by
  have hrestrict : (volumeMeasureOn U).restrict S = volume.restrict S := by
    rw [volumeMeasureOn, Measure.restrict_restrict hS,
      Set.inter_eq_self_of_subset_left hSU]
  have hae : ∀ᵐ x ∂((volumeMeasureOn U).restrict S),
      (F : Vec d → HilbertVec d) x i = u x i := by
    refine (hFu.filter_mono (ae_mono Measure.restrict_le_self)).mono fun x hx => ?_
    rw [hx]
    simp [hilbertifyVecField]
  rw [integral_congr_ae hae, hrestrict]

/-- Oscillation is measurable for arbitrary representatives of measurable `L²` classes.
Quadratic-observable measurability and the window integrabilities remain explicit premises. -/
theorem measurable_meanSquareOscillationVecOn_of_measurable_representative
    {Omega : Type*} [MeasurableSpace Omega] (Q : TriadicCube d) {S : Set (Vec d)}
    (hS : MeasurableSet S) (hSU : S ⊆ openCubeSet Q)
    (hfin : volume S ≠ ⊤) (hpos : 0 < (volume S).toReal)
    {F : Omega → HilbertVectorL2 (openCubeSet Q)} (hF : Measurable F)
    {u : Omega → Vec d → Vec d}
    (hFu : ∀ omega, (F omega : Vec d → HilbertVec d) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      hilbertifyVecField (u omega))
    (hsqMeas : Measurable fun omega => volumeAverage S (fun x => vecNormSq (u omega x)))
    (hcoord : ∀ (omega : Omega) (k : Fin d), IntegrableOn (fun x => u omega x k) S volume)
    (hcoordsq : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => (u omega x k) ^ 2) S volume) :
    Measurable fun omega => Book.Ch01.meanSquareOscillationVecOn S (u omega) := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hcoordMeas : ∀ k : Fin d, Measurable fun omega =>
      volumeAverage S (fun x => u omega x k) := by
    intro k
    have hEq : (fun omega => volumeAverage S (fun x => u omega x k)) =
        fun omega => (volume S).toReal⁻¹ *
          ∫ x in S, (F omega : Vec d → HilbertVec d) x k
            ∂(volumeMeasureOn (openCubeSet Q)) := by
      funext omega
      rw [setIntegral_coordL2_eq_of_ae (hFu omega) hS hSU k, volumeAverage]
    rw [hEq]
    exact measurable_const.mul
      (Corrector.measurable_setIntegral_gradCoordL2 Q hS k hF)
  have hEq : (fun omega => Book.Ch01.meanSquareOscillationVecOn S (u omega)) =
      fun omega => volumeAverage S (fun x => vecNormSq (u omega x)) -
        ∑ k : Fin d, (volumeAverage S (fun x => u omega x k)) ^ 2 := by
    funext omega
    have hnorm : vecNormSq (volumeAverageVec S (u omega)) =
        ∑ k : Fin d, (volumeAverage S (fun x => u omega x k)) ^ 2 := by
      simp only [vecNormSq, vecDot, volumeAverageVec, pow_two]
    rw [meanSquareOscillationVecOn_eq_sub_vecNormSq_volumeAverageVec hfin hpos
      (u omega) (hcoord omega) (hcoordsq omega), hnorm]
  rw [hEq]
  exact hsqMeas.sub (Finset.measurable_sum Finset.univ
    fun k _ => (hcoordMeas k).pow_const 2)

/-- **The measurability core.**  For a measurable family of gradient classes on
the cube whose quadratic window observable is already known measurable, the
mean-square oscillation over a measurable window is measurable in the sample.

: the window data `hS`, `hSU`, `hfin`, `hpos`; the family identification `hw`;
the quadratic measurability `hsqMeas`; and the coordinate integrabilities on
the window. -/
private theorem measurable_meanSquareOscillationVecOn_of_measurable {Omega : Type*}
    [MeasurableSpace Omega] (Q : TriadicCube d) {S : Set (Vec d)}
    (hS : MeasurableSet S) (hSU : S ⊆ openCubeSet Q)
    (hfin : volume S ≠ ⊤) (hpos : 0 < (volume S).toReal)
    {F : Omega → HilbertVectorL2 (openCubeSet Q)} (hF : Measurable F)
    {w : Omega → H1Function (openCubeSet Q)}
    (hw : ∀ omega, F omega = (w omega).gradToHilbertVectorL2)
    (hsqMeas : Measurable fun omega =>
      volumeAverage S (fun x => vecNormSq ((w omega).grad x)))
    (hcoord : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => (w omega).grad x k) S volume)
    (hcoordsq : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => ((w omega).grad x k) ^ 2) S volume) :
    Measurable fun omega =>
      Book.Ch01.meanSquareOscillationVecOn S ((w omega).grad) := by
  refine measurable_meanSquareOscillationVecOn_of_measurable_representative Q hS hSU hfin hpos
    hF ?_ hsqMeas hcoord hcoordsq
  intro omega
  rw [hw omega]
  exact (w omega).coeFn_gradToHilbertVectorL2

/-- Unconditional in the sample: **the fourth power of the oscillation cell of
`e.nablaw.oscillations` is a measurable function of the sample**, for an
arbitrary family of zero-trace weak solutions of `e.def.w`.

on the cell data `hsc`, `hsub` and on the two coordinate integrability families
on the cell. -/
theorem measurable_meshOscillationCell_rpow_four_freshShellDirichletGrad [NeZero d]
    (Q : TriadicCube d) (sigmaInv : ℝ) (nsh msh : ℤ) (e : Vec d)
    {n : ℤ} (R : TriadicCube d) (hsc : R.scale = n)
    (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (hsol : ∀ omega : Cutoff.ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -Corrector.streamForcing sigmaInv omega nsh msh e x))
    (hcoord : ∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => (wD omega).toH1Function.grad x k) (openCubeSet R) volume)
    (hcoordsq : ∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => ((wD omega).toH1Function.grad x k) ^ 2)
        (openCubeSet R) volume) :
    Measurable fun omega : Cutoff.ShellSeq d =>
      meshOscillationCell n (wD omega).toH1Function.grad R ^ (4 : ℝ) := by
  have hEq : (fun omega : Cutoff.ShellSeq d =>
      meshOscillationCell n (wD omega).toH1Function.grad R ^ (4 : ℝ)) =
      fun omega => (Book.Ch01.meanSquareOscillationVecOn (openCubeSet R)
        ((wD omega).toH1Function.grad)) ^ 2 := by
    funext omega
    exact meshOscillationCell_rpow_four_eq_sq R hsc _
  rw [hEq]
  refine Measurable.pow_const ?_ 2
  exact measurable_meanSquareOscillationVecOn_of_measurable Q
    (measurableSet_openCubeSet R) hsub (volume_openCubeSet_ne_top' R)
    (volume_openCubeSet_toReal_pos' R)
    (Corrector.measurable_freshShellDirichletGradL2 Q sigmaInv nsh msh e wD hsol)
    (w := fun omega => (wD omega).toH1Function) (fun _ => rfl)
    (measurable_volumeAverage_vecNormSq_freshShellDirichletGrad Q sigmaInv nsh msh e
      (measurableSet_openCubeSet R) hsub wD hsol)
    hcoord hcoordsq

/-- The Neumann mirror of the previous statement. -/
theorem measurable_meshOscillationCell_rpow_four_freshShellNeumannGrad
    (Q : TriadicCube d) (sigmaInv : ℝ) (nsh msh : ℤ) (e : Vec d)
    {n : ℤ} (R : TriadicCube d) (hsc : R.scale = n)
    (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hsol : ∀ omega : Cutoff.ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -Corrector.streamForcing sigmaInv omega nsh msh e x))
    (hcoord : ∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => (wN omega).toH1Function.grad x k) (openCubeSet R) volume)
    (hcoordsq : ∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => ((wN omega).toH1Function.grad x k) ^ 2)
        (openCubeSet R) volume) :
    Measurable fun omega : Cutoff.ShellSeq d =>
      meshOscillationCell n (wN omega).toH1Function.grad R ^ (4 : ℝ) := by
  have hEq : (fun omega : Cutoff.ShellSeq d =>
      meshOscillationCell n (wN omega).toH1Function.grad R ^ (4 : ℝ)) =
      fun omega => (Book.Ch01.meanSquareOscillationVecOn (openCubeSet R)
        ((wN omega).toH1Function.grad)) ^ 2 := by
    funext omega
    exact meshOscillationCell_rpow_four_eq_sq R hsc _
  rw [hEq]
  refine Measurable.pow_const ?_ 2
  exact measurable_meanSquareOscillationVecOn_of_measurable Q
    (measurableSet_openCubeSet R) hsub (volume_openCubeSet_ne_top' R)
    (volume_openCubeSet_toReal_pos' R)
    (Corrector.measurable_freshShellNeumannGradL2 Q sigmaInv nsh msh e wN hsol)
    (w := fun omega => (wN omega).toH1Function) (fun _ => rfl)
    (measurable_volumeAverage_vecNormSq_freshShellNeumannGrad Q sigmaInv nsh msh e
      (measurableSet_openCubeSet R) hsub wN hsol)
    hcoord hcoordsq

/-! ## The cell is dominated by the cube -/

/-- The cell average of `|u|^8` is at most the volume ratio times the cube
average of `|u|^8`, for any cell contained in `cu_K`.

: the containment `hsub` and the integrability `height` on `cu_K`. -/
theorem volumeAverage_vecNormSq_pow_four_le_ratio_mul {K : ℤ} {R : TriadicCube d}
    (u : Vec d → Vec d) (hsub : openCubeSet R ⊆ openCubeSet (originCube d K))
    (height : IntegrableOn (fun x => vecNormSq (u x) ^ (4 : ℕ))
      (openCubeSet (originCube d K)) volume) :
    volumeAverage (openCubeSet R) (fun x => vecNormSq (u x) ^ (4 : ℕ)) ≤
      (volume (openCubeSet R)).toReal⁻¹ *
          (volume (openCubeSet (originCube d K))).toReal *
        volumeAverage (openCubeSet (originCube d K))
          (fun x => vecNormSq (u x) ^ (4 : ℕ)) := by
  have hWpos : (0 : ℝ) < (volume (openCubeSet (originCube d K))).toReal :=
    volume_openCubeSet_toReal_pos' _
  have hVnn : (0 : ℝ) ≤ (volume (openCubeSet R)).toReal⁻¹ := by positivity
  have hmono : ∫ x in openCubeSet R, vecNormSq (u x) ^ (4 : ℕ) ∂volume ≤
      ∫ x in openCubeSet (originCube d K), vecNormSq (u x) ^ (4 : ℕ) ∂volume :=
    setIntegral_mono_set height
      (Filter.Eventually.of_forall fun _ => by positivity) hsub.eventuallyLE
  have hcancel : (volume (openCubeSet (originCube d K))).toReal *
      volumeAverage (openCubeSet (originCube d K)) (fun x => vecNormSq (u x) ^ (4 : ℕ)) =
        ∫ x in openCubeSet (originCube d K), vecNormSq (u x) ^ (4 : ℕ) ∂volume := by
    unfold volumeAverage
    field_simp
  change (volume (openCubeSet R)).toReal⁻¹ *
      ∫ x in openCubeSet R, vecNormSq (u x) ^ (4 : ℕ) ∂volume ≤ _
  calc (volume (openCubeSet R)).toReal⁻¹ *
        ∫ x in openCubeSet R, vecNormSq (u x) ^ (4 : ℕ) ∂volume
      ≤ (volume (openCubeSet R)).toReal⁻¹ *
          ∫ x in openCubeSet (originCube d K), vecNormSq (u x) ^ (4 : ℕ) ∂volume :=
        mul_le_mul_of_nonneg_left hmono hVnn
    _ = (volume (openCubeSet R)).toReal⁻¹ *
          (volume (openCubeSet (originCube d K))).toReal *
            volumeAverage (openCubeSet (originCube d K))
              (fun x => vecNormSq (u x) ^ (4 : ℕ)) := by rw [← hcancel]; ring

/-! ## The integrability core -/

/-- A measurable nonnegative fourth-power envelope inherits integrability and the
explicit eighth-energy bound, even when the dominating fluctuation is not measurable. -/
theorem integrable_and_integral_le_freshShellEighthEnergyConst_of_envelope
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {G : Omega → ℝ} (hG0 : ∀ omega, 0 ≤ G omega)
    (hglobMeas : Measurable G) {Chead A : ℝ} (hChead : 0 ≤ Chead) (hA : 0 < A)
    {T : Omega → ℝ} (hT0 : ∀ omega, 0 ≤ T omega)
    (hT : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) T A)
    (hGT : ∀ omega, G omega ≤ (Chead + T omega) ^ (4 : ℕ)) :
    Integrable G mu ∧ (∫ omega, G omega ∂mu) ≤ freshShellEighthEnergyConst Chead A := by
  -- the measurable dominating fluctuation, exactly the device of the octic layer
  set root : Omega → ℝ := fun omega => Real.sqrt (Real.sqrt (G omega)) with hrootdef
  have hrootnn : ∀ omega, 0 ≤ root omega := fun _ => Real.sqrt_nonneg _
  have hroot : ∀ omega, (root omega) ^ (4 : ℕ) = G omega := by
    intro omega
    have h1 : Real.sqrt (Real.sqrt (G omega)) ^ (2 : ℕ) = Real.sqrt (G omega) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (G omega) ^ (2 : ℕ) = G omega := Real.sq_sqrt (hG0 omega)
    calc (root omega) ^ (4 : ℕ)
        = (Real.sqrt (Real.sqrt (G omega)) ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [hrootdef]; ring
      _ = Real.sqrt (G omega) ^ (2 : ℕ) := by rw [h1]
      _ = G omega := h2
  set T' : Omega → ℝ := fun omega => max (root omega - Chead) 0 with hT'def
  have hT'0 : ∀ omega, 0 ≤ T' omega := fun _ => le_max_right _ _
  have hT'meas : Measurable T' :=
    (((hglobMeas.sqrt).sqrt).sub measurable_const).max measurable_const
  have hT'le : ∀ omega, T' omega ≤ T omega := by
    intro omega
    have hnn : (0 : ℝ) ≤ Chead + T omega := by linarith [hT0 omega]
    have hle : root omega ≤ Chead + T omega := by
      by_contra hcon
      push Not at hcon
      have hlt : (Chead + T omega) ^ (4 : ℕ) < (root omega) ^ (4 : ℕ) :=
        pow_lt_pow_left₀ hcon hnn (by norm_num)
      rw [hroot omega] at hlt
      exact absurd (hGT omega) (not_le.mpr hlt)
    have hTeq : T' omega = max (root omega - Chead) 0 := rfl
    rw [hTeq]
    exact max_le (by linarith) (hT0 omega)
  have hT'tail : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) T' A :=
    hT.of_le hT'le
  have hGT' : ∀ omega, G omega ≤ (Chead + T' omega) ^ (4 : ℕ) := by
    intro omega
    have hle : root omega ≤ Chead + T' omega := by
      have hbase := le_max_left (root omega - Chead) 0
      have hTeq : T' omega = max (root omega - Chead) 0 := rfl
      rw [hTeq]
      linarith
    calc G omega = (root omega) ^ (4 : ℕ) := (hroot omega).symm
      _ ≤ (Chead + T' omega) ^ (4 : ℕ) := pow_le_pow_left₀ (hrootnn omega) hle 4
  -- integrability of the dominating cube observable
  have hT'fourInt : Integrable (fun omega => T' omega ^ (4 : ℕ)) mu :=
    integrable_rpow_four_of_isBigOWith_gammaSigma_one hA hT'0 hT'meas.aemeasurable hT'tail
  have hdomInt : Integrable
      (fun omega => 8 * Chead ^ (4 : ℕ) + 8 * T' omega ^ (4 : ℕ)) mu :=
    (integrable_const _).add (hT'fourInt.const_mul 8)
  have hGint : Integrable G mu := by
    refine hdomInt.mono' hglobMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_of_nonneg (hG0 omega)]
    have h := hGT' omega
    have hstep := add_pow_four_le_eight_mul Chead (T' omega)
    linarith
  have hEbound : ∫ omega, G omega ∂mu ≤ freshShellEighthEnergyConst Chead A :=
    integral_le_freshShellEighthEnergyConst hA hT'0 hT'meas.aemeasurable hT'tail hGint hGT'
  exact ⟨hGint, hEbound⟩

/-- **The generic `MemLp` step.**  Given the pathwise `L^8` bound with a
`Gamma_1` fluctuation, the measurability of the two octic observables, and the
six spatial families on `cu_K`, the fourth power of the oscillation cell is
`L^2` in the sample.

: complete binder census beyond the typing binders `d, Omega, its
MeasurableSpace instance, mu, K, n, R, u, Chead, A, T`: `[IsProbabilityMeasure
mu]`; `hChead : 0 <= Chead`; `hA : 0 < A`; `hT0`, `hT` (the `Gamma_1` tail);
`hmem`, `hpath` (the spatial `L^8` membership and the pathwise `L^8` bound);
`hcoord`, `hcoordsq`, `hsq`, `hfour`, `height` on `cu_K`; `hsc`, `hsub` (the
cell data); and `hglobMeas`, `hcellMeas` (measurability in the sample of the
cube's eighth energy and of the fourth power of the cell).  No integrability in
the sample is assumed. -/
theorem memLp_two_meshOscillationCell_rpow_four_of_measurable
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {K n : ℤ} {R : TriadicCube d}
    (u : Omega → Vec d → Vec d) {Chead A : ℝ} (hChead : 0 ≤ Chead) (hA : 0 < A)
    {T : Omega → ℝ} (hT0 : ∀ omega, 0 ≤ T omega)
    (hT : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) T A)
    (hmem : ∀ omega, MemLp (fun x => Book.Ch02.vecNorm (u omega x)) 8
      (normalizedCubeMeasure (originCube d K)))
    (hpath : ∀ omega,
      Corrector.cubeEuclideanLpNorm (originCube d K) 8 (u omega) ^ (2 : ℕ) ≤
        Chead + T omega)
    (hcoord : ∀ (omega : Omega) (k : Fin d), IntegrableOn (fun x => u omega x k)
      (openCubeSet (originCube d K)) volume)
    (hcoordsq : ∀ (omega : Omega) (k : Fin d), IntegrableOn (fun x => (u omega x k) ^ 2)
      (openCubeSet (originCube d K)) volume)
    (hsq : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x))
      (openCubeSet (originCube d K)) volume)
    (hfour : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x) ^ 2)
      (openCubeSet (originCube d K)) volume)
    (height : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x) ^ (4 : ℕ))
      (openCubeSet (originCube d K)) volume)
    (hsc : R.scale = n) (hsub : openCubeSet R ⊆ openCubeSet (originCube d K))
    (hglobMeas : Measurable fun omega =>
      volumeAverage (openCubeSet (originCube d K))
        (fun x => vecNormSq (u omega x) ^ (4 : ℕ)))
    (hcellMeas : Measurable fun omega =>
      meshOscillationCell n (u omega) R ^ (4 : ℝ)) :
    MemLp (fun omega => meshOscillationCell n (u omega) R ^ (4 : ℝ)) 2 mu := by
  classical
  set G : Omega → ℝ := fun omega =>
    volumeAverage (openCubeSet (originCube d K))
      (fun x => vecNormSq (u omega x) ^ (4 : ℕ)) with hGdef
  have hG0 : ∀ omega, 0 ≤ G omega := fun omega =>
    volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet _)
      fun _ _ => by positivity
  -- the cube average is the eighth power of the manuscript's `L^8` norm
  have hGeq : ∀ omega,
      G omega = (Corrector.cubeEuclideanLpNorm (originCube d K) 8 (u omega) ^ (2 : ℕ))
        ^ (4 : ℕ) := by
    intro omega
    have h1 : G omega =
        cubeAverage (originCube d K) (fun x => vecNormSq (u omega x) ^ (4 : ℕ)) :=
      volumeAverage_openCubeSet_eq_cubeAverage' _ _
    rw [h1, cubeAverage_vecNormSq_pow_four_eq_cubeEuclideanLpNorm_eight_pow_eight
      (originCube d K) (u omega) (hmem omega)]
    ring
  have hGT : ∀ omega, G omega ≤ (Chead + T omega) ^ (4 : ℕ) := by
    intro omega
    rw [hGeq omega]
    exact pow_le_pow_left₀ (sq_nonneg _) (hpath omega) 4
  have hGint := (integrable_and_integral_le_freshShellEighthEnergyConst_of_envelope
    hG0 hglobMeas hChead hA hT0 hT hGT).1
  -- the dominating variable
  set ratio : ℝ := (volume (openCubeSet R)).toReal⁻¹ *
    (volume (openCubeSet (originCube d K))).toReal with hratio
  have hdomInt : Integrable
      (fun omega => ratio * G omega) mu := hGint.const_mul ratio
  -- the per-cell restrictions of the spatial families
  have hcoordW : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => u omega x k) (openCubeSet R) volume :=
    fun omega k => (hcoord omega k).mono_set hsub
  have hcoordsqW : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => (u omega x k) ^ 2) (openCubeSet R) volume :=
    fun omega k => (hcoordsq omega k).mono_set hsub
  have hsqW : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x))
      (openCubeSet R) volume := fun omega => (hsq omega).mono_set hsub
  have hfourW : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x) ^ 2)
      (openCubeSet R) volume := fun omega => (hfour omega).mono_set hsub
  have heightW : ∀ omega, IntegrableOn (fun x => (vecNormSq (u omega x) ^ 2) ^ 2)
      (openCubeSet R) volume := by
    intro omega
    have hcong : (fun x => (vecNormSq (u omega x) ^ 2) ^ 2) =
        fun x => vecNormSq (u omega x) ^ (4 : ℕ) := by
      funext x; ring
    rw [hcong]
    exact (height omega).mono_set hsub
  -- the pathwise chain
  have hchain : ∀ omega,
      (meshOscillationCell n (u omega) R ^ (4 : ℝ)) ^ 2 ≤
        ratio * G omega := by
    intro omega
    have hcell := meshOscillationCell_pow_eight_le_volumeAverage R hsc (u omega)
      (hcoordW omega) (hcoordsqW omega) (hsqW omega) (hfourW omega) (heightW omega)
    have hratioStep := volumeAverage_vecNormSq_pow_four_le_ratio_mul (K := K)
      (u omega) hsub (height omega)
    rw [sq_meshOscillationCell_rpow_four]
    exact le_trans hcell hratioStep
  have hsqInt : Integrable
      (fun omega => (meshOscillationCell n (u omega) R ^ (4 : ℝ)) ^ 2) mu := by
    refine hdomInt.mono' (hcellMeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    have hnn : (0 : ℝ) ≤ (meshOscillationCell n (u omega) R ^ (4 : ℝ)) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg hnn]
    exact hchain omega
  exact (memLp_two_iff_integrable_sq hcellMeas.aestronglyMeasurable).2 hsqInt

/-! ## The two wired consumers -/

/-- **`hmem8` for the Dirichlet corrector of `e.def.w`, as a theorem.**

For every `gamma` below one explicit threshold, in the whole parameter range of
`e.recurrence.params`, and for every sample family of zero-trace weak solutions
of `e.def.w` obeying the six spatial families on `cu_K`, the fourth power of the
oscillation cell of any cell contained in `cu_K` is `L^2` in the sample.

Reaches exactly the external anchor
`Algsuperdiff.Frozen.External.calderon_zygmund`, a **proved** external,
inherited from `exists_freshShell_cubeEuclideanL8_leg_bound`. -/
theorem exists_gamma0_memLp_two_freshShellDirichlet_meshOscillationCell_rpow_four
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (hh : ℕ), 0 < hh → m - (hh : ℤ) ≤ m0 →
            (hh : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
              Book.Ch02.vecNorm e' ≤ 1 →
              ∀ wD : Cutoff.ShellSeq d → H10Function (openCubeSet (originCube d K)),
                (∀ omega, IsZeroTraceDirichletRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d K)) (wD omega)
                    (fun x => -Corrector.streamForcing
                      ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
                      (m - (hh : ℤ)) m e x)) →
                (∀ omega, MemLp (fun x => Book.Ch02.vecNorm
                    ((wD omega).toH1Function.grad x)) 8
                    (normalizedCubeMeasure (originCube d K))) →
                (∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
                  IntegrableOn (fun x => (wD omega).toH1Function.grad x k)
                    (openCubeSet (originCube d K)) volume) →
                (∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
                  IntegrableOn (fun x => ((wD omega).toH1Function.grad x k) ^ 2)
                    (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wD omega).toH1Function.grad x))
                  (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ 2)
                  (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ (4 : ℕ))
                  (openCubeSet (originCube d K)) volume) →
                ∀ (n : ℤ) (R : TriadicCube d), R.scale = n →
                  openCubeSet R ⊆ openCubeSet (originCube d K) →
                  MemLp (fun omega : Cutoff.ShellSeq d =>
                    meshOscillationCell n (wD omega).toH1Function.grad R ^ (4 : ℝ))
                    2 M.P.toMeasure := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Chead, hCheadpos, gamma0, hg0pos, hg0quarter, hleg⟩ :=
    exists_freshShell_cubeEuclideanL8_leg_bound d hd
  refine ⟨gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he' wD hsol hmem
    hcoord hcoordsq hsq hfour height n R hsc hsub
  obtain ⟨Tfluct, hTnn, hTtail, hD, -⟩ :=
    hleg M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he'
  have hApos : (0 : ℝ) < M.gamma ^ (100 : ℕ) := pow_pos M.shellPrefix.gamma_pos _
  exact memLp_two_meshOscillationCell_rpow_four_of_measurable
    (fun omega => (wD omega).toH1Function.grad) hCheadpos.le hApos hTnn hTtail hmem
    (fun omega => hD omega (wD omega) (hsol omega)) hcoord hcoordsq hsq hfour height
    hsc hsub
    (Corrector.measurable_volumeAverage_vecNormSq_pow_four_freshShellDirichletGrad
      (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
      (m - (hh : ℤ)) m e (measurableSet_openCubeSet _) subset_rfl wD hsol)
    (measurable_meshOscillationCell_rpow_four_freshShellDirichletGrad
      (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
      (m - (hh : ℤ)) m e R hsc hsub wD hsol
      (fun omega k => (hcoord omega k).mono_set hsub)
      (fun omega k => (hcoordsq omega k).mono_set hsub))

/-- **`hmem8` for the Neumann corrector of `e.def.w`, as a theorem.**  The
mean-zero Neumann mirror of the previous statement. -/
theorem exists_gamma0_memLp_two_freshShellNeumann_meshOscillationCell_rpow_four
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (hh : ℕ), 0 < hh → m - (hh : ℤ) ≤ m0 →
            (hh : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
              Book.Ch02.vecNorm e' ≤ 1 →
              ∀ wN : Cutoff.ShellSeq d →
                  H1MeanZeroFunction (openCubeSet (originCube d K)),
                (∀ omega, IsMeanZeroNeumannRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d K)) (wN omega)
                    (fun x => -Corrector.streamForcing
                      ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
                      (m - (hh : ℤ)) m e' x)) →
                (∀ omega, MemLp (fun x => Book.Ch02.vecNorm
                    ((wN omega).toH1Function.grad x)) 8
                    (normalizedCubeMeasure (originCube d K))) →
                (∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
                  IntegrableOn (fun x => (wN omega).toH1Function.grad x k)
                    (openCubeSet (originCube d K)) volume) →
                (∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
                  IntegrableOn (fun x => ((wN omega).toH1Function.grad x k) ^ 2)
                    (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wN omega).toH1Function.grad x))
                  (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wN omega).toH1Function.grad x) ^ 2)
                  (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wN omega).toH1Function.grad x) ^ (4 : ℕ))
                  (openCubeSet (originCube d K)) volume) →
                ∀ (n : ℤ) (R : TriadicCube d), R.scale = n →
                  openCubeSet R ⊆ openCubeSet (originCube d K) →
                  MemLp (fun omega : Cutoff.ShellSeq d =>
                    meshOscillationCell n (wN omega).toH1Function.grad R ^ (4 : ℝ))
                    2 M.P.toMeasure := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Chead, hCheadpos, gamma0, hg0pos, hg0quarter, hleg⟩ :=
    exists_freshShell_cubeEuclideanL8_leg_bound d hd
  refine ⟨gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he' wN hsol hmem
    hcoord hcoordsq hsq hfour height n R hsc hsub
  obtain ⟨Tfluct, hTnn, hTtail, -, hN⟩ :=
    hleg M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he'
  have hApos : (0 : ℝ) < M.gamma ^ (100 : ℕ) := pow_pos M.shellPrefix.gamma_pos _
  exact memLp_two_meshOscillationCell_rpow_four_of_measurable
    (fun omega => (wN omega).toH1Function.grad) hCheadpos.le hApos hTnn hTtail hmem
    (fun omega => hN omega (wN omega) (hsol omega)) hcoord hcoordsq hsq hfour height
    hsc hsub
    (Corrector.measurable_volumeAverage_vecNormSq_pow_four_freshShellNeumannGrad
      (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
      (m - (hh : ℤ)) m e' (measurableSet_openCubeSet _) subset_rfl wN hsol)
    (measurable_meshOscillationCell_rpow_four_freshShellNeumannGrad
      (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
      (m - (hh : ℤ)) m e' R hsc hsub wN hsol
      (fun omega k => (hcoord omega k).mono_set hsub)
      (fun omega k => (hcoordsq omega k).mono_set hsub))

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
