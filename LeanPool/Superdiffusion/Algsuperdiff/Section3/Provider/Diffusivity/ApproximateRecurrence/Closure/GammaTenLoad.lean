/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5InputGradMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5InputSideConditions
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitFoldCellMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitProducerLoad
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellL8

/-!
# GammaTenLoad

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The **load** leg of the `cgamma^{10}` estimate

ABK26, Step 2 of `l.approximate.recurrence.formula`, the display

```
  ( avsum_{z in 3^n Zd cap cu_K}  E[ | bfAhom_{m-h}^{1/2} P_z |^4 ] )^{1/4}
      <=  C ,
```

quoted there "by `e.nablaw.in.L.eight`" (label).

## The gap this module fills

`PrincipalResponseMomentsFourth` carries the whole **pathwise** chain of the
display --- the collapse of the normalization
(`annealedSqrtNormSq_principalPz_eq`), the fourth power
(`sq_annealedSqrtNormSq_principalPz_le`) and its grid form --- and records
explicitly that "the final numerical bound by the dimensional constant `C` is
**not** proved": that bound needs `e.nablaw.in.L.eight`, which the module does
not invoke.  This module supplies exactly that missing step, at the closure's
own corrector families and under the closure's own law
`(cutoffSampleLaw M).toMeasure`.

## The route

Four steps, all of them the manuscript's own.

1. **Pathwise, per cell.**  `sq_annealedSqrtNormSq_principalPz_le` at the load's
   own gauge (`gaugeRatio_self`) bounds `| bfAhom^{1/2} P_z |^4` by the fourth
   powers of the two averaged legs `e' + (grad w_D)_R` and
   `e + (grad w_N + shom^{-1} h e')_R`.
2. **The grid re-assembly.**
   `PrincipalResponseDisplayTwoGrid.descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le`
   turns the grid average of each leg into the constant term and the
   volume-normalized Euclidean `L^8` norm of the field on `cu_K`; the depth `j`
   drops out, because the grid tiles `cu_K`.  This is
   `descendantsAverage_sq_annealedSqrtNormSq_principalPz_le_norms`.
3. **`e.nablaw.in.L.eight`, lines (i) and (ii).**  Calder\'on--Zygmund
   (`Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le`) releases the two
   corrector gradients against the forcing of `e.def.w`, and
   `Corrector.cubeEuclideanLpNorm_streamForcing_le` reads that forcing as
   `shom_n^{-1} ||k_{n+h} - k_n||_{L8bar(cu_K)}`.  The flux leg is the Neumann
   gradient *plus* the same forcing, so Minkowski
   (`PrincipalResponseDisplayTwoGrid.cubeEuclideanLpNorm_add_le`) puts it on the
   same carrier.  What is left is the single **measurable** random variable
   `L(omega) = ||k_{n+h} - k_n||_{L8bar(cu_K)}` --- this is
   `exists_gammaTenLoadPathwiseConst`.
4. **`e.km.kn.Lp` and line (iii).**  The fourth moment of `L` under the cutoff
   sample law is the proved
   `Step5InputGradMoment.exists_integral_streamIncrementLpNorm_eight_pow_four_le`
   (the *proved* frozen theorem with its `Gamma_1` tail replaced by a
   measurable positive part), and the deterministic normalization
   `Corrector.inv_sigmaBarSq_mul_shellWidth_le` --- `shom_n^{-2} h 3^{2 cgamma
   (n+h)} <= 24 * 3^18` --- turns the resulting bound into an **absolute**
   constant.  This is `exists_gammaTenLoadConst`.

## The shape delivered, and why it is a grid average

The source display is a **grid** average over `z in 3^n Zd cap cu_K`, and so is
the statement here: `gridFourthMoment`, respectively `gridFourthMomentRoot`, over
`descendantsAtDepth cu_K j`.  A *uniform per-cell* fourth moment is **not**
available and is not claimed: the grid step of item 2 above is the tiling
identity `avsum_R fint_R = fint_{cu_K}`, which loses a factor `3^{jd}` when read
at a single cell.  The companion module `Closure.GammaTenLoadFold` therefore
supplies the grid-load variant of
`Closure.GammaTenGridFold.descendantsAverage_integral_fold_le_of_moments`, whose
`hload` binder is exactly `exists_gammaTenLoadConst_root`'s conclusion.

## Binders

All binders are regime binders: the induction state
`Algsuperdiff.Frozen.Section3.inductionState M m0 Ec` and the parameters of
`e.recurrence.params` --- `0 < h`, `n <= m0`, `h <= 6 cstar cgamma^{-1}`, `n +
h <= K` --- together with `|e|, |e'| <= 1` and the standing `2 <= d`.  Nothing
about the corrector families is assumed: they are the closure's own
`closureDirichletAlong` and `closureNeumannAlong`, whose two weak formulations
are proved in `Closure.SplitProducerFold`.  No smallness gate on `cgamma`
occurs, and the constant is produced **before** the model.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2; the load display;
  `e.Pz.def`; `e.nablaw.in.L.eight`; `e.km.kn.Lp`; `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Elementary arithmetic -/

theorem gaugeRatio_self (sigma : PositiveScalar) : gaugeRatio sigma sigma = 1 := by
  rw [gaugeRatio, div_self (ne_of_gt sigma.2), max_self]

theorem pow_four_add_le (a b : ℝ) :
    (a + b) ^ (4 : ℕ) ≤ 8 * (a ^ (4 : ℕ) + b ^ (4 : ℕ)) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * a - b * b),
    sq_nonneg (a * a + b * b), sq_nonneg a, sq_nonneg b]

theorem sq_vecNormSq_le_one {v : Vec d} (hv : vecNorm v ≤ 1) :
    vecNormSq v ^ (2 : ℕ) ≤ 1 := by
  have hnn : (0 : ℝ) ≤ vecNorm v := vecNorm_nonneg v
  have hsq : vecNormSq v = vecNorm v ^ (2 : ℕ) := (vecNorm_sq_eq_vecNormSq v).symm
  rw [hsq, ← pow_mul]
  norm_num
  exact pow_le_one₀ hnn hv

/-! ## The pathwise grid bound of the load -/

/-- **The grid average of `|bfAhom^{1/2}P_z|^4` at a fixed sample.**

`PrincipalResponseMomentsFourth.descendantsAverage_sq_annealedSqrtNormSq_principalPz_le`
read at the load's own gauge, with the two grid legs released by
`PrincipalResponseDisplayTwoGrid.descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le`
into the volume-normalized `L^8` norms of `e.nablaw.in.L.eight`.

only on the two `L^8` memberships and on the two direction bounds `|e|, |e'| <=
1`. -/
theorem descendantsAverage_sq_annealedSqrtNormSq_principalPz_le_norms
    (sigma : PositiveScalar) (omega : ShellSeq d) (n m : ℤ) {e e' : Vec d}
    (he : vecNorm e ≤ 1) (he' : vecNorm e' ≤ 1) (Q : TriadicCube d) (j : ℕ)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q))
    (hD : MemLp wD.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hF : MemLp (neumannFluxField sigma omega n m e' wN) (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    descendantsAverage Q j
        (fun R => annealedSqrtNormSq sigma
          (principalPz sigma omega n m e e' R wD wN) ^ 2) ≤
      32 + 16 * cubeEuclideanLpNorm Q 8 wD.toH1Function.grad ^ (4 : ℕ) +
        16 * cubeEuclideanLpNorm Q 8
          (neumannFluxField sigma omega n m e' wN) ^ (4 : ℕ) := by
  have hbase := descendantsAverage_sq_annealedSqrtNormSq_principalPz_le sigma sigma
    omega n m e e' Q j wD wN
  rw [gaugeRatio_self] at hbase
  have hlegD := descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le Q j e'
    (fun x => wD.toH1Function.grad x) hD
  have hlegN := descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le Q j e
    (neumannFluxField sigma omega n m e' wN) hF
  have h1 : vecNormSq e' ^ (2 : ℕ) ≤ 1 := sq_vecNormSq_le_one he'
  have h2 : vecNormSq e ^ (2 : ℕ) ≤ 1 := sq_vecNormSq_le_one he
  have hgrad : (fun x => wD.toH1Function.grad x) = wD.toH1Function.grad := rfl
  rw [hgrad] at hlegD
  nlinarith [hbase, hlegD, hlegN, h1, h2]

/-! ## The pathwise majorant, in the fresh-shell carrier alone -/

/-- **The grid average of `|bfAhom^{1/2}P_z|^4` at the closure's own families,
majorized by the fresh-shell `L^8` carrier.**

Calderon--Zygmund releases the two corrector gradients against the forcing of
`e.def.w`, and `Corrector.cubeEuclideanLpNorm_streamForcing_le` reads the forcing
as `shom_n^{-1} ||k_{n+h} - k_n||_{L8bar(cu_K)}`.  What is left on the right is
the single *measurable* carrier of `e.km.kn.Lp`.

Proved from `Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le` and
`memLp_eight_grad_closure{Dirichlet,Neumann}Along`, hence from the external
Calderon--Zygmund input `Algsuperdiff.Frozen.External.calderon_zygmund`. -/
theorem exists_gammaTenLoadPathwiseConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cpath : ℝ, 0 < Cpath ∧
      ∀ (M : ABKModel d) (n : ℤ) (h K j : ℕ) (e e' : Vec d),
        vecNorm e ≤ 1 → vecNorm e' ≤ 1 →
        ∀ omega : ShellSeq d,
          descendantsAverage (originCube d (K : ℤ)) j
              (fun R => annealedSqrtNormSq (Annealed.sigmaBar M n)
                (principalPz (Annealed.sigmaBar M n) omega n (n + (h : ℤ)) e e' R
                  (closureDirichletAlong M n h K e omega)
                  (closureNeumannAlong M n h K e' omega)) ^ 2) ≤
            32 + Cpath * (((Annealed.sigmaBar M n : ℝ))⁻¹ *
              Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n (n + (h : ℤ))
                omega) ^ (4 : ℕ) := by
  classical
  obtain ⟨Ccz, hCczpos, hCZ⟩ := exists_cubeEuclideanL8_gradient_sq_sum_le (d := d) hd
  refine ⟨576 * Ccz ^ (2 : ℕ) + 128, by positivity, ?_⟩
  intro M n h K j e e' he he' omega
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  set m : ℤ := n + (h : ℤ) with hm
  set sigma : PositiveScalar := Annealed.sigmaBar M n with hsigma
  set sinv : ℝ := ((sigma : ℝ))⁻¹ with hsinv
  have hsinv0 : (0 : ℝ) ≤ sinv := (inv_pos.2 sigma.2).le
  set wD : H10Function (openCubeSet Q) := closureDirichletAlong M n h K e omega with hwD
  set wN : H1MeanZeroFunction (openCubeSet Q) := closureNeumannAlong M n h K e' omega
    with hwN
  set L : ℝ := Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n m omega with hL
  have hL0 : (0 : ℝ) ≤ L := Provider.Stream.streamIncrementLpNorm_nonneg _ _ _ _ _
  -- the three `L^8` memberships
  have hDmem : MemLp wD.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_eight_grad_closureDirichletAlong hd M n h K e omega
  have hNmem : MemLp wN.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_eight_grad_closureNeumannAlong hd M n h K e' omega
  have hSFmem : MemLp (streamForcing sinv omega n m e') (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_continuous Q _ (continuous_streamForcing _ _ _ _ _)
  have hFmem : MemLp (neumannFluxField sigma omega n m e' wN) (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    have hadd := hNmem.add hSFmem
    exact hadd
  -- the two solution properties
  have hsolD : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wD
      (fun x => -streamForcing sinv omega n m e x) :=
    isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e omega
  have hsolN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -streamForcing sinv omega n m e' x) :=
    isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e' omega
  -- Calderon--Zygmund
  have hczapp := hCZ Q (streamForcing sinv omega n m e) (streamForcing sinv omega n m e')
    (continuous_streamForcing _ _ _ _ _) (continuous_streamForcing _ _ _ _ _)
    wD hsolD wN hsolN
  have hfD : cubeEuclideanLpNorm Q 8 (streamForcing sinv omega n m e) ≤ sinv * L :=
    cubeEuclideanLpNorm_streamForcing_le hsinv0 (K : ℤ) n m omega he
  have hfN : cubeEuclideanLpNorm Q 8 (streamForcing sinv omega n m e') ≤ sinv * L :=
    cubeEuclideanLpNorm_streamForcing_le hsinv0 (K : ℤ) n m omega he'
  set ND : ℝ := cubeEuclideanLpNorm Q 8 wD.toH1Function.grad with hND
  set NN : ℝ := cubeEuclideanLpNorm Q 8 wN.toH1Function.grad with hNNdef
  set SF : ℝ := cubeEuclideanLpNorm Q 8 (streamForcing sinv omega n m e') with hSF
  have hND0 : (0 : ℝ) ≤ ND := cubeEuclideanLpNorm_nonneg _ _ _
  have hNN0 : (0 : ℝ) ≤ NN := cubeEuclideanLpNorm_nonneg _ _ _
  have hSF0 : (0 : ℝ) ≤ SF := cubeEuclideanLpNorm_nonneg _ _ _
  have hSL0 : (0 : ℝ) ≤ sinv * L := mul_nonneg hsinv0 hL0
  set S : ℝ := (sinv * L) ^ (4 : ℕ) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  have hDsq : cubeEuclideanLpNorm Q 8 (streamForcing sinv omega n m e) ^ 2 ≤
      (sinv * L) ^ 2 :=
    pow_le_pow_left₀ (cubeEuclideanLpNorm_nonneg _ _ _) hfD 2
  have hNsq : SF ^ 2 ≤ (sinv * L) ^ 2 := pow_le_pow_left₀ hSF0 hfN 2
  have hsum : ND ^ 2 + NN ^ 2 ≤ 2 * Ccz * (sinv * L) ^ 2 := by
    refine hczapp.trans ?_
    have hin : cubeEuclideanLpNorm Q 8 (streamForcing sinv omega n m e) ^ 2 + SF ^ 2 ≤
        2 * (sinv * L) ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left hin hCczpos.le
    linarith
  -- the flux leg
  have hflux : cubeEuclideanLpNorm Q 8 (neumannFluxField sigma omega n m e' wN) ≤
      NN + SF :=
    cubeEuclideanLpNorm_add_le Q (p := (8 : ℝ≥0∞)) (by norm_num)
      wN.toH1Function.grad (streamForcing sinv omega n m e')
      (memLp_vecNorm_of_memLp Q hNmem) (memLp_vecNorm_of_memLp Q hSFmem)
  -- the fourth powers
  have hNDsq : ND ^ 2 ≤ 2 * Ccz * (sinv * L) ^ 2 := by nlinarith [sq_nonneg NN]
  have hNNsq : NN ^ 2 ≤ 2 * Ccz * (sinv * L) ^ 2 := by nlinarith [sq_nonneg ND]
  have hND4 : ND ^ (4 : ℕ) ≤ 4 * (Ccz ^ (2 : ℕ) * S) := by
    have hstep := pow_le_pow_left₀ (sq_nonneg ND) hNDsq 2
    have hl : (ND ^ 2) ^ 2 = ND ^ (4 : ℕ) := by ring
    have hr : (2 * Ccz * (sinv * L) ^ 2) ^ 2 = 4 * (Ccz ^ (2 : ℕ) * S) := by
      rw [hSdef]; ring
    rw [hl, hr] at hstep
    exact hstep
  have hNN4 : NN ^ (4 : ℕ) ≤ 4 * (Ccz ^ (2 : ℕ) * S) := by
    have hstep := pow_le_pow_left₀ (sq_nonneg NN) hNNsq 2
    have hl : (NN ^ 2) ^ 2 = NN ^ (4 : ℕ) := by ring
    have hr : (2 * Ccz * (sinv * L) ^ 2) ^ 2 = 4 * (Ccz ^ (2 : ℕ) * S) := by
      rw [hSdef]; ring
    rw [hl, hr] at hstep
    exact hstep
  have hSF4 : SF ^ (4 : ℕ) ≤ S := by
    have := pow_le_pow_left₀ hSF0 hfN 4
    rw [hSdef]
    exact this
  have hflux4 : cubeEuclideanLpNorm Q 8 (neumannFluxField sigma omega n m e' wN) ^ (4 : ℕ)
      ≤ 32 * (Ccz ^ (2 : ℕ) * S) + 8 * S := by
    have hstep := pow_le_pow_left₀
      (cubeEuclideanLpNorm_nonneg Q 8 (neumannFluxField sigma omega n m e' wN)) hflux 4
    have hsplit := pow_four_add_le NN SF
    linarith [hstep, hsplit, hNN4, hSF4]
  -- the grid bound
  have hgrid := descendantsAverage_sq_annealedSqrtNormSq_principalPz_le_norms sigma omega
    n m he he' Q j wD wN hDmem hFmem
  have hrw : (576 * Ccz ^ (2 : ℕ) + 128) * S = 576 * (Ccz ^ (2 : ℕ) * S) + 128 * S := by
    ring
  rw [hrw]
  linarith [hgrid, hND4, hflux4]

/-! ## The annealed load leg -/

theorem rpow_four_sqrt {v : ℝ} (hv : 0 ≤ v) :
    Real.sqrt v ^ (4 : ℝ) = v ^ (2 : ℕ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 : Real.sqrt v ^ (2 : ℕ) = v := Real.sq_sqrt hv
  calc Real.sqrt v ^ (4 : ℕ) = (Real.sqrt v ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ = v ^ (2 : ℕ) := by rw [h2]

/-- **The load leg of the `cgamma^{10}` estimate, proved.**

One absolute constant `Cload`, produced before the model, such that on the
closure's own grid the fourth moment of the localized principal load obeys the
display,

```
  ( avsum_{R in descendantsAtDepth cu_K j}  E[ | bfAhom_n^{1/2} P_R |^4 ] )^{1/4}
      <=  Cload ,
```

at the recurrence's own parameters and uniformly in the localization scale `K`
and the depth `j`.

All binders are regime binders of `e.recurrence.params` and the induction
state; nothing about the corrector families is assumed beyond their being the
closure's own.

This is the manuscript's own "by `e.nablaw.in.L.eight`" and nothing more. -/
theorem exists_gammaTenLoadConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cload : ℝ, 0 < Cload ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ec : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ec →
        ∀ (n : ℤ) (h K j : ℕ) (e e' : Vec d),
          0 < h → n ≤ m0 → (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
          n + (h : ℤ) ≤ (K : ℤ) → vecNorm e ≤ 1 → vecNorm e' ≤ 1 →
          gridFourthMoment (cutoffSampleLaw M).toMeasure
              (descendantsAtDepth (originCube d (K : ℤ)) j)
              (fun (R : TriadicCube d) (omega : CutoffSample d) =>
                Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M n)
                  (meshCellLoad M n h (K : ℤ) e e'
                    (closureDirichletAlong M n h K e)
                    (closureNeumannAlong M n h K e') R omega))) ≤
            Cload ^ (4 : ℕ) := by
  classical
  obtain ⟨Cpath, hCpath0, hpath⟩ := exists_gammaTenLoadPathwiseConst d hd
  obtain ⟨Ckm, hCkm0, hkm⟩ := exists_integral_streamIncrementLpNorm_eight_pow_four_le d
  have hgap0 : (0 : ℝ) < 24 * (3 : ℝ) ^ (18 : ℝ) := by
    have : (0 : ℝ) < (3 : ℝ) ^ (18 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  set X : ℝ := 32 + Cpath * Ckm * (24 * (3 : ℝ) ^ (18 : ℝ)) ^ (2 : ℕ) with hX
  have hX0 : (0 : ℝ) < X := by
    have : (0 : ℝ) < Cpath * Ckm * (24 * (3 : ℝ) ^ (18 : ℝ)) ^ (2 : ℕ) := by positivity
    rw [hX]; linarith
  refine ⟨X ^ ((4 : ℝ)⁻¹), Real.rpow_pos_of_pos hX0 _, ?_⟩
  have hroot : (X ^ ((4 : ℝ)⁻¹)) ^ (4 : ℕ) = X := by
    rw [← Real.rpow_natCast (X ^ ((4 : ℝ)⁻¹)) 4, ← Real.rpow_mul hX0.le]
    norm_num
  rw [hroot]
  intro M m0 Ec hS n h K j e e' hh hnm0 hcap hmK he he'
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  set m : ℤ := n + (h : ℤ) with hm
  set sigma : PositiveScalar := Annealed.sigmaBar M n with hsigma
  set sinv : ℝ := ((sigma : ℝ))⁻¹ with hsinv
  have hsinv0 : (0 : ℝ) ≤ sinv := (inv_pos.2 sigma.2).le
  set mu : Measure (CutoffSample d) := (cutoffSampleLaw M).toMeasure with hmu
  set wDf : ShellSeq d → H10Function (openCubeSet Q) := closureDirichletAlong M n h K e
    with hwDf
  set wNf : ShellSeq d → H1MeanZeroFunction (openCubeSet Q) :=
    closureNeumannAlong M n h K e' with hwNf
  have hsolD : ∀ omega : ShellSeq d, IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) (wDf omega)
      (fun x => -streamForcing sinv omega n m e x) := fun omega =>
    isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e omega
  have hsolN : ∀ omega : ShellSeq d, IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) (wNf omega)
      (fun x => -streamForcing sinv omega n m e' x) := fun omega =>
    isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e' omega
  set Lc : CutoffSample d → ℝ := fun omega =>
    Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n m omega.val with hLc
  have hnlt : n < m := by
    have hpos : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh
    omega
  obtain ⟨hLint, hLbound⟩ := hkm M (K : ℤ) n m hnlt hmK
  set G : TriadicCube d → CutoffSample d → ℝ := fun R omega =>
    Real.sqrt (annealedSqrtNormSq sigma
      (meshCellLoad M n h (K : ℤ) e e' wDf wNf R omega)) with hG
  set Maj : CutoffSample d → ℝ := fun omega =>
    32 + Cpath * (sinv ^ (4 : ℕ) * Lc omega ^ (4 : ℕ)) with hMaj
  have hMajtail : Integrable (fun omega : CutoffSample d =>
      Cpath * (sinv ^ (4 : ℕ) * Lc omega ^ (4 : ℕ))) mu :=
    (hLint.const_mul (sinv ^ (4 : ℕ))).const_mul Cpath
  have hMajint : Integrable Maj mu := by
    rw [hMaj]
    exact (integrable_const (32 : ℝ)).add hMajtail
  -- the pathwise grid bound at the cell family
  have hle : ∀ omega : CutoffSample d,
      cubeFamilyAverage (descendantsAtDepth Q j) (fun R => G R omega ^ (4 : ℝ)) ≤
        Maj omega := by
    intro omega
    have hpt : (fun R : TriadicCube d => G R omega ^ (4 : ℝ)) =
        fun R : TriadicCube d => annealedSqrtNormSq sigma
          (principalPz sigma omega.val n m e e' R (wDf omega.val) (wNf omega.val))
            ^ (2 : ℕ) := by
      funext R
      rw [hG]
      exact rpow_four_sqrt (annealedSqrtNormSq_nonneg _ _)
    rw [hpt, ← descendantsAverage_eq_cubeFamilyAverage]
    have hbase := hpath M n h K j e e' he he' omega.val
    refine hbase.trans (le_of_eq ?_)
    rw [hMaj, hLc]
    ring
  -- measurability and integrability of the cell observable
  have hmeasG : ∀ R ∈ descendantsAtDepth Q j, Measurable (G R) := by
    intro R hR
    have hP : Measurable fun omega : CutoffSample d =>
        principalPz sigma omega.val n m e e' R (wDf omega.val) (wNf omega.val) :=
      measurable_principalPz_cutoffSample hR sigma sinv sinv n m e e' e e' wDf wNf
        hsolD hsolN
    have hA : Measurable fun omega : CutoffSample d =>
        annealedSqrtNormSq sigma
          (principalPz sigma omega.val n m e e' R (wDf omega.val) (wNf omega.val)) := by
      have hEq : (fun omega : CutoffSample d => annealedSqrtNormSq sigma
          (principalPz sigma omega.val n m e e' R (wDf omega.val) (wNf omega.val))) =
          fun omega : CutoffSample d => (sigma : ℝ) *
            vecNormSq (principalPz sigma omega.val n m e e' R
              (wDf omega.val) (wNf omega.val)).1 +
            ((sigma : ℝ))⁻¹ * vecNormSq (principalPz sigma omega.val n m e e' R
              (wDf omega.val) (wNf omega.val)).2 := rfl
      rw [hEq]
      exact ((measurable_vecNormSq_of_measurable (measurable_fst.comp hP)).const_mul _).add
        ((measurable_vecNormSq_of_measurable (measurable_snd.comp hP)).const_mul _)
    exact Real.continuous_sqrt.measurable.comp hA
  have hcardpos : ∀ R ∈ descendantsAtDepth Q j,
      (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    intro R hR
    exact_mod_cast Finset.card_pos.mpr ⟨R, hR⟩
  have hFint : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega : CutoffSample d => G R omega ^ (4 : ℝ)) mu := by
    intro R hR
    have hmeas := hmeasG R hR
    have hpow : Measurable fun omega : CutoffSample d => G R omega ^ (4 : ℝ) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (4 : ℝ))).measurable.comp hmeas
    refine (hMajint.const_mul ((descendantsAtDepth Q j).card : ℝ)).mono'
      hpow.aestronglyMeasurable ?_
    filter_upwards with omega
    have hnn : ∀ S : TriadicCube d, (0 : ℝ) ≤ G S omega ^ (4 : ℝ) := fun S =>
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hsingle : G R omega ^ (4 : ℝ) ≤
        ∑ S ∈ descendantsAtDepth Q j, G S omega ^ (4 : ℝ) :=
      Finset.single_le_sum (f := fun S => G S omega ^ (4 : ℝ)) (fun S _ => hnn S) hR
    have hcard := hcardpos R hR
    have havg := hle omega
    have hdefavg : cubeFamilyAverage (descendantsAtDepth Q j)
        (fun S => G S omega ^ (4 : ℝ)) =
        ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ S ∈ descendantsAtDepth Q j, G S omega ^ (4 : ℝ) := rfl
    rw [hdefavg] at havg
    have hmul := mul_le_mul_of_nonneg_left havg hcard.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcard), one_mul] at hmul
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn R)]
    exact hsingle.trans hmul
  -- the annealed step
  have hgrid := gridFourthMoment_le_integral_of_cubeFamilyAverage_le mu
    (descendantsAtDepth Q j) G Maj hFint hMajint hle
  refine hgrid.trans ?_
  -- the value of the majorant's integral
  have hMajval : (∫ omega, Maj omega ∂mu) =
      32 + Cpath * (sinv ^ (4 : ℕ) * ∫ omega, Lc omega ^ (4 : ℕ) ∂mu) := by
    rw [hMaj, integral_add (integrable_const (32 : ℝ)) hMajtail, integral_const,
      integral_const_mul, integral_const_mul]
    simp
  rw [hMajval]
  -- the normalization of line (iii)
  set W : ℝ := (h : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) with hW
  have hW0 : (0 : ℝ) ≤ W := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [hW]; positivity
  have hdiff : ((m : ℝ) - (n : ℝ)) = (h : ℝ) := by rw [hm]; push_cast; ring
  have hnorm : sinv ^ (2 : ℕ) * W ≤ 24 * (3 : ℝ) ^ (18 : ℝ) := by
    have hmh : m - (h : ℤ) = n := by rw [hm]; omega
    have hbase := inv_sigmaBarSq_mul_shellWidth_le M hS (m := m) (h := h)
      (by rw [hmh]; exact hnm0) hcap
    rw [hmh] at hbase
    have hsq : sinv ^ (2 : ℕ) = (((sigma : ℝ)) ^ 2)⁻¹ := by rw [hsinv, ← inv_pow]
    rw [hsq, hW, ← mul_assoc]
    exact hbase
  have hnormsq : sinv ^ (4 : ℕ) * W ^ (2 : ℕ) ≤ (24 * (3 : ℝ) ^ (18 : ℝ)) ^ (2 : ℕ) := by
    have hbase := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ sinv ^ (2 : ℕ) * W) hnorm 2
    have heq : (sinv ^ (2 : ℕ) * W) ^ (2 : ℕ) = sinv ^ (4 : ℕ) * W ^ (2 : ℕ) := by ring
    rwa [heq] at hbase
  have hLb : (∫ omega, Lc omega ^ (4 : ℕ) ∂mu) ≤ Ckm * W ^ (2 : ℕ) := by
    rw [hW]
    have := hLbound
    rw [hdiff] at this
    exact this
  have hstep : sinv ^ (4 : ℕ) * ∫ omega, Lc omega ^ (4 : ℕ) ∂mu ≤
      Ckm * (24 * (3 : ℝ) ^ (18 : ℝ)) ^ (2 : ℕ) := by
    have h1 : sinv ^ (4 : ℕ) * ∫ omega, Lc omega ^ (4 : ℕ) ∂mu ≤
        sinv ^ (4 : ℕ) * (Ckm * W ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hLb (by positivity)
    have h2 : sinv ^ (4 : ℕ) * (Ckm * W ^ (2 : ℕ)) =
        Ckm * (sinv ^ (4 : ℕ) * W ^ (2 : ℕ)) := by ring
    have h3 : Ckm * (sinv ^ (4 : ℕ) * W ^ (2 : ℕ)) ≤
        Ckm * (24 * (3 : ℝ) ^ (18 : ℝ)) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hnormsq hCkm0.le
    linarith [h1, h3, h2.le, h2.ge]
  have hfinal := mul_le_mul_of_nonneg_left hstep hCpath0.le
  rw [hX]
  linarith [hfinal]

/-- **The load leg in the root spelling the grid fold consumes.**

`exists_gammaTenLoadConst` read through the fourth root: this is the `hload`
binder of
`GammaTenLoadFold.descendantsAverage_integral_fold_le_of_grid_moments`, verbatim.

Inherited from `exists_gammaTenLoadConst`. -/
theorem exists_gammaTenLoadConst_root (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cload : ℝ, 0 < Cload ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (Ec : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ec →
        ∀ (n : ℤ) (h K j : ℕ) (e e' : Vec d),
          0 < h → n ≤ m0 → (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
          n + (h : ℤ) ≤ (K : ℤ) → vecNorm e ≤ 1 → vecNorm e' ≤ 1 →
          gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
              (descendantsAtDepth (originCube d (K : ℤ)) j)
              (fun (R : TriadicCube d) (omega : CutoffSample d) =>
                Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M n)
                  (meshCellLoad M n h (K : ℤ) e e'
                    (closureDirichletAlong M n h K e)
                    (closureNeumannAlong M n h K e') R omega))) ≤ Cload := by
  obtain ⟨Cload, hCload0, hC⟩ := exists_gammaTenLoadConst d hd
  refine ⟨Cload, hCload0, ?_⟩
  intro M m0 Ec hS n h K j e e' hh hnm0 hcap hmK he he'
  have hbase := hC M m0 Ec hS n h K j e e' hh hnm0 hcap hmK he he'
  have hroot := Real.rpow_le_rpow (gridFourthMoment_nonneg _ _ _) hbase
    (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
  have heq : (Cload ^ (4 : ℕ)) ^ ((4 : ℝ)⁻¹) = Cload := by
    rw [← Real.rpow_natCast Cload 4, ← Real.rpow_mul hCload0.le]
    norm_num
  rw [heq] at hroot
  exact hroot

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
