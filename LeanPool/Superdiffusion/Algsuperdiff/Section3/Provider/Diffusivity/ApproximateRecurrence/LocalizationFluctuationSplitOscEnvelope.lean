/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationNumericOctic

/-!
# LocalizationFluctuationSplitOscEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hE`: the eighth-moment grid envelope of the oscillation cells

`LocalizationOscillationFullMesh` and its Neumann mirror
`LocalizationFluctuationNumericNeumannMesh` carry **two** `e.nablaw.in.L.eight`
side conditions into the Step-5 shape:

* `hmem8`, the `L^2`-in-the-sample membership of the fourth powers of the
  oscillation cells --- discharged by
  `LocalizationFluctuationNumericOctic.exists_gamma0_memLp_two_freshShell{Dirichlet,
  Neumann}_meshOscillationCell_rpow_four`;
* `hE`, an envelope for their eighth-moment **grid average**, i.e. a real `E`
  with
  ```
    avsum_{z in 3^n Zd cap cu_K} E[ osc(z + cu_n; grad w_omega)^8 ]  <=  E ,
  ```
  `E` being quantified *before* the model, so that the threshold the full-mesh
  endpoint produces from it is uniform.

This module discharges `hE`, and re-exports `hmem8` alongside it so that a
consumer of the full-mesh endpoint obtains both side conditions from a single
call under a single threshold.

## Method

Nothing new is estimated.  Two proved pieces are composed.

1. `LocalizationFluctuationGridEighth.cubeFamilyAverage_integral_meshOscillationCell_pow_eight_le`
   bounds the eighth-moment grid average by the expectation of any observable
   `G` dominating the cube average `fint_{cu_K} |u|^8` pathwise.  Taking `G`
   to be that cube average itself, the hypothesis is `le_rfl` and the
   remaining work is a bound on `E[G]`.

2. `G` is measurable by `Corrector.CorrectorMeasurableOctic`, and it equals the
   fourth power of `‖u‖^2_{L8bar(cu_K)}`, which `e.nablaw.in.L.eight` bounds by
   `Chead + Tfluct` with `Tfluct = O_{Gamma_1}(gamma^100)`.  The produced
   `Tfluct` is **not** known to be measurable, so the `T'` device of
   `LocalizationFluctuationNumericOctic.memLp_two_meshOscillationCell_rpow_four_of_measurable`
   is reused verbatim: `T' := max ((G)^{1/4} - Chead, 0)` is measurable, is
   dominated by `Tfluct` (hence inherits its `Gamma_1` tail), and still
   dominates `G^{1/4} - Chead`.  Then
   `LocalizationFluctuationGridEighth.integral_le_freshShellEighthEnergyConst`
   gives `E[G] <= freshShellEighthEnergyConst Chead (gamma^100)`.

3. The amplitude is finally released: `freshShellEighthEnergyConst` is monotone
   in its second argument and `gamma^100 <= 1`, so the *model-independent*
   constant `freshShellEighthEnergyConst Chead 1` serves for every admissible
   model.  This is what lets `E` be quantified before `M`.

The consumers' `hE` is stated at the real exponent `^ (8 : ℝ)` while the grid
composition is stated at `^ (8 : ℕ)`; `rpow_eight_eq_pow_eight` converts.

## Main results

* `rpow_eight_eq_pow_eight`, `freshShellEighthEnergyConst_mono_right` --- the two
  pieces of bookkeeping.
* `cubeFamilyAverage_integral_meshOscillationCell_pow_eight_le_freshShellEighthEnergyConst`
  --- the generic core, for an arbitrary sample family with an
  `e.nablaw.in.L.eight`-shaped pathwise bound.
* `exists_freshShellDirichlet_meshOscillation_memLp_and_eighthMoment_le` and its
  Neumann mirror --- `hmem8` and `hE` together, as theorems, with `E` produced
  before the model.

## Binders

Beyond the typing binders: `hd : 2 <= d`; under the leading quantifiers the
model gate `M.gamma <= gamma0`, the induction state, the four gates of
`e.recurrence.params` and the two direction bounds; then the caller's family of
weak solutions of `e.def.w` (`hsol`) and the six *spatial* single-sample
families on `cu_K` (the `L^8` membership `hmem` and the five integrabilities it
implies); and finally the mesh index bound `n <= K`, which only names the mesh.
No hypothesis about the sample space survives; no measurability or selection
property of the corrector family is assumed; and no smallness or normalization
is assumed --- both `E` and the threshold are **produced**.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `e.def.w`, `e.nablaw.oscillations`, `e.nablaw.in.L.eight`,
  `e.lower.bound.oscillations`, `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Two pieces of bookkeeping -/

/-- The real power `x ^ (8 : ℝ)` is the monoid power `x ^ (8 : ℕ)`. -/
theorem rpow_eight_eq_pow_eight (x : ℝ) : x ^ (8 : ℝ) = x ^ (8 : ℕ) := by
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The eighth-energy envelope constant is monotone in the fluctuation
amplitude.  This is what releases the model-dependent amplitude `gamma^100` and
produces a constant uniform in the model. -/
theorem freshShellEighthEnergyConst_mono_right (Chead : ℝ) {A B : ℝ} (hA : 0 ≤ A)
    (hAB : A ≤ B) :
    freshShellEighthEnergyConst Chead A ≤ freshShellEighthEnergyConst Chead B := by
  have he : (0 : ℝ) ≤ 8 * Real.exp 1 := by positivity
  have hstep : 8 * Real.exp 1 * A ≤ 8 * Real.exp 1 * B :=
    mul_le_mul_of_nonneg_left hAB he
  have hnn : (0 : ℝ) ≤ 8 * Real.exp 1 * A := mul_nonneg he hA
  have hpow : (8 * Real.exp 1 * A) ^ (4 : ℕ) ≤ (8 * Real.exp 1 * B) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hnn hstep 4
  unfold freshShellEighthEnergyConst
  linarith

/-! ## The generic core -/

/-- **The eighth-moment grid envelope, from an `e.nablaw.in.L.eight`-shaped
pathwise bound.**

For any sample family `u` whose normalized Euclidean `L^8` norm on `cu_K` obeys
`‖u‖^2 <= Chead + T` pathwise with `T` a nonnegative `O_{Gamma_1}(A)` variable,
the eighth-moment grid average of the oscillation cells of
`e.nablaw.oscillations` over `3^n Zd cap cu_K` is below
`freshShellEighthEnergyConst Chead A`.

`T` is **not** assumed measurable: it enters only through the measurable
dominator `T' = max((fint_{cu_K}|u|^8)^{1/4} - Chead, 0)`, which is built from
the measurable cube observable `hglobMeas` and inherits the `Gamma_1` tail by
`IsBigOWith.of_le`.

: complete binder census beyond the typing binders `d, Omega, its
MeasurableSpace instance, mu, K, n, u, Chead, A, T`: `[IsProbabilityMeasure
mu]`; the mesh index bound `hn`; `hChead`, `hA`; `hT0`, `hT` (the `Gamma_1`
tail); `hmem`, `hpath` (the spatial `L^8` membership and the pathwise `L^8`
bound); the five spatial integrability families on `cu_K`; `hcellInt` (the
integrability in the sample of the per-cell eighth powers); and `hglobMeas`
(measurability in the sample of the cube's eighth energy).  No estimate on the
oscillation is used. -/
theorem cubeFamilyAverage_integral_meshOscillationCell_pow_eight_le_freshShellEighthEnergyConst
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {K n : ℤ} (hn : n ≤ K) (u : Omega → Vec d → Vec d)
    {Chead A : ℝ} (hChead : 0 ≤ Chead) (hA : 0 < A)
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
    (hcellInt : ∀ R ∈ mesoCubeGrid d K n,
      Integrable (fun omega => meshOscillationCell n (u omega) R ^ (8 : ℕ)) mu)
    (hglobMeas : Measurable fun omega =>
      volumeAverage (openCubeSet (originCube d K))
        (fun x => vecNormSq (u omega x) ^ (4 : ℕ))) :
    cubeFamilyAverage (mesoCubeGrid d K n)
        (fun R => ∫ omega, meshOscillationCell n (u omega) R ^ (8 : ℕ) ∂mu) ≤
      freshShellEighthEnergyConst Chead A := by
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
  have hGT : ∀ omega, G omega ≤ (Chead + T omega) ^ (4 : ℕ) := by
    intro omega
    rw [hGeq omega]
    exact pow_le_pow_left₀ (sq_nonneg _) (hpath omega) 4
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
  -- the grid composition, with `G` its own dominating observable
  have hcubeSet : ∀ (f : Vec d → ℝ),
      IntegrableOn f (openCubeSet (originCube d K)) volume →
        IntegrableOn f (cubeSet (originCube d K)) volume := by
    intro f hf
    exact integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hf
  have hpathG : ∀ omega,
      cubeAverage (originCube d K) (fun x => vecNormSq (u omega x) ^ (4 : ℕ)) ≤
        G omega := by
    intro omega
    exact le_of_eq (volumeAverage_openCubeSet_eq_cubeAverage' _ _).symm
  have hcomp := cubeFamilyAverage_integral_meshOscillationCell_pow_eight_le mu K n hn u G
    (fun omega k => hcubeSet _ (hcoord omega k))
    (fun omega k => hcubeSet _ (hcoordsq omega k))
    (fun omega => hcubeSet _ (hsq omega))
    (fun omega => hcubeSet _ (hfour omega))
    (fun omega => hcubeSet _ (height omega))
    hcellInt hGint hpathG
  exact hcomp.trans hEbound

/-! ## The two wired consumers -/

/-- **`hmem8` and `hE` for the Dirichlet corrector of `e.def.w`, as theorems.**

One constant `E`, produced *before* the model, and one explicit threshold
`gamma0`, such that in the whole parameter range of `e.recurrence.params` and
for every sample family of zero-trace weak solutions of `e.def.w` obeying the
six spatial families on `cu_K`, both `e.nablaw.in.L.eight` side conditions of
`LocalizationOscillationFullMesh` hold at every mesh scale `n <= K`.

Reaches exactly the external anchor
`Algsuperdiff.Frozen.External.calderon_zygmund`, a **proved** external,
inherited from `exists_freshShell_cubeEuclideanL8_leg_bound`. -/
theorem exists_freshShellDirichlet_meshOscillation_memLp_and_eighthMoment_le
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
        ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
          ∀ (m0 : ℤ) (Eind : {Eb : ℝ // 1 ≤ Eb}),
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
                  ∀ n : ℤ, n ≤ K →
                    (∀ R ∈ mesoCubeGrid d K n,
                      MemLp (fun omega : Cutoff.ShellSeq d =>
                        meshOscillationCell n (wD omega).toH1Function.grad R ^ (4 : ℝ))
                        2 M.P.toMeasure) ∧
                    cubeFamilyAverage (mesoCubeGrid d K n)
                        (fun R => ∫ omega : Cutoff.ShellSeq d,
                          meshOscillationCell n (wD omega).toH1Function.grad R ^ (8 : ℝ)
                            ∂M.P.toMeasure) ≤ E := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Chead, hCheadpos, gamma0, hg0pos, hg0quarter, hleg⟩ :=
    exists_freshShell_cubeEuclideanL8_leg_bound d hd
  refine ⟨freshShellEighthEnergyConst Chead 1, freshShellEighthEnergyConst_nonneg _ _,
    gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he' wD hsol hmem
    hcoord hcoordsq hsq hfour height n hn
  obtain ⟨Tfluct, hTnn, hTtail, hD, -⟩ :=
    hleg M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he'
  have hgammapos : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hApos : (0 : ℝ) < M.gamma ^ (100 : ℕ) := pow_pos hgammapos _
  have hglobMeas :
      Measurable fun omega : Cutoff.ShellSeq d =>
        volumeAverage (openCubeSet (originCube d K))
          (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ (4 : ℕ)) :=
    Corrector.measurable_volumeAverage_vecNormSq_pow_four_freshShellDirichletGrad
      (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
      (m - (hh : ℤ)) m e (measurableSet_openCubeSet _) subset_rfl wD hsol
  -- the mesh-cell data
  have hscale : n ≤ (originCube d K).scale := hn
  have hcell : ∀ R ∈ mesoCubeGrid d K n,
      R.scale = n ∧ openCubeSet R ⊆ openCubeSet (originCube d K) := by
    intro R hR
    exact ⟨scale_eq_of_mem_mesoCubeGrid hR,
      openCubeSet_subset_of_mem_descendantsAtScale hscale hR⟩
  -- `hmem8`
  have hmem8 : ∀ R ∈ mesoCubeGrid d K n,
      MemLp (fun omega : Cutoff.ShellSeq d =>
        meshOscillationCell n (wD omega).toH1Function.grad R ^ (4 : ℝ))
        2 M.P.toMeasure := by
    intro R hR
    obtain ⟨hsc, hsub⟩ := hcell R hR
    exact memLp_two_meshOscillationCell_rpow_four_of_measurable
      (fun omega => (wD omega).toH1Function.grad) hCheadpos.le hApos hTnn hTtail hmem
      (fun omega => hD omega (wD omega) (hsol omega)) hcoord hcoordsq hsq hfour height
      hsc hsub hglobMeas
      (measurable_meshOscillationCell_rpow_four_freshShellDirichletGrad
        (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
        (m - (hh : ℤ)) m e R hsc hsub wD hsol
        (fun omega k => (hcoord omega k).mono_set hsub)
        (fun omega k => (hcoordsq omega k).mono_set hsub))
  refine ⟨hmem8, ?_⟩
  -- `hcellInt`, from `hmem8`
  have hcellInt : ∀ R ∈ mesoCubeGrid d K n,
      Integrable (fun omega : Cutoff.ShellSeq d =>
        meshOscillationCell n (wD omega).toH1Function.grad R ^ (8 : ℕ)) M.P.toMeasure := by
    intro R hR
    have h8 := hmem8 R hR
    have hsq' := (memLp_two_iff_integrable_sq h8.aestronglyMeasurable).1 h8
    refine hsq'.congr (Filter.Eventually.of_forall fun omega => ?_)
    exact sq_meshOscillationCell_rpow_four n (wD omega).toH1Function.grad R
  -- the eighth-moment grid envelope at the model's own amplitude
  have hcore := cubeFamilyAverage_integral_meshOscillationCell_pow_eight_le_freshShellEighthEnergyConst
    (mu := M.P.toMeasure) hn (fun omega => (wD omega).toH1Function.grad)
    hCheadpos.le hApos hTnn hTtail hmem
    (fun omega => hD omega (wD omega) (hsol omega)) hcoord hcoordsq hsq hfour height
    hcellInt hglobMeas
  -- release the amplitude and convert the exponent
  have hgammale : M.gamma ^ (100 : ℕ) ≤ 1 :=
    pow_le_one₀ hgammapos.le (by linarith [hMgamma.trans hg0quarter])
  have hrelease := freshShellEighthEnergyConst_mono_right Chead hApos.le hgammale
  have hrw : (fun R => ∫ omega : Cutoff.ShellSeq d,
        meshOscillationCell n (wD omega).toH1Function.grad R ^ (8 : ℝ) ∂M.P.toMeasure) =
      fun R => ∫ omega : Cutoff.ShellSeq d,
        meshOscillationCell n (wD omega).toH1Function.grad R ^ (8 : ℕ) ∂M.P.toMeasure := by
    funext R
    refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
    exact rpow_eight_eq_pow_eight _
  rw [hrw]
  linarith [hcore, hrelease]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
