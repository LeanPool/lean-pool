/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5InputGradMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationSplitOscEnvelope

/-!
# Step5InputOscillation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hmemOsc` and `hosc` at the closure's Dirichlet family

Two of the residual legs of
`Closure.Step5Basket.step5GaugeEndpoint_closureFamilies_of_momentLegs` are about
the oscillation cell of `e.nablaw.oscillations` on the closure's grid:

* `hmemOsc` --- the cell is `L^4` in the sample;
* `hosc` --- `e.lower.bound.oscillations` itself, in the **re-sited** shape
  `Closure.Step5DefectGauge.exists_gamma0_freshShellDirichlet_step5MeshOscillationResited_le_gamma_pow_fifteen`
  delivers.

Both come from a single pair, the octic grid envelope
`ApproximateRecurrence.exists_freshShellDirichlet_meshOscillation_memLp_and_eighthMoment_le`.
That producer quantifies its constant `E` **before** the threshold `gamma0` and
before the model, and the re-sited endpoint takes `E` as an argument and produces
its own threshold; so the two compose in the only order that works: take `E`
from the envelope, feed it to the endpoint, and take the smaller of the two
thresholds.  This module carries out that composition and discharges the
envelope's six spatial side conditions at the closure's own Dirichlet family,
all six being consequences of the single `L^8` membership of the corrector
gradient.

## References

* ABK26, `e.lower.bound.oscillations`; `e.nablaw.oscillations`;
  `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two missing consequences of one `L^8` membership -/

private theorem integrableOn_cubeSet_of_integrable_normalized' {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) {g : Vec d → E}
    (hg : Integrable g (normalizedCubeMeasure Q)) :
    IntegrableOn g (cubeSet Q) volume := by
  have hne : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne'
  rw [normalizedCubeMeasure] at hg
  exact (integrable_smul_measure hne ENNReal.ofReal_ne_top).1 hg

/-- **Each coordinate of `grad w` is integrable on `cu_K`.**: on `hu`. -/
theorem integrableOn_openCubeSet_coord_of_memLp_eight (Q : TriadicCube d)
    {u : Vec d → Vec d} (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) (k : Fin d) :
    IntegrableOn (fun x => u x k) (openCubeSet Q) volume := by
  have hu1 : MemLp u (1 : ℝ≥0∞) (normalizedCubeMeasure Q) := hu.mono_exponent (by norm_num)
  have hintN : Integrable u (normalizedCubeMeasure Q) := memLp_one_iff_integrable.1 hu1
  have huC : IntegrableOn u (cubeSet Q) volume :=
    integrableOn_cubeSet_of_integrable_normalized' Q hintN
  have huO : IntegrableOn u (openCubeSet Q) volume :=
    huC.mono_set (openCubeSet_subset_cubeSet Q)
  have hmeas : AEStronglyMeasurable (fun x => u x k) (volume.restrict (openCubeSet Q)) :=
    (continuous_apply k).comp_aestronglyMeasurable huO.aestronglyMeasurable
  refine Integrable.mono huO.norm hmeas ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using norm_le_pi_norm (u x) k

/-- **`|grad w|^8` is integrable on `cu_K`.**: on `hu`. -/
theorem integrableOn_openCubeSet_vecNormSq_pow_four_of_memLp_eight (Q : TriadicCube d)
    {u : Vec d → Vec d} (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    IntegrableOn (fun x => vecNormSq (u x) ^ (4 : ℕ)) (openCubeSet Q) volume := by
  have huE : MemLp (fun x => vecNorm (u x)) (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_vecNorm_eight_of_memLp_eight Q hu
  have hint : Integrable (fun x => vecNormSq (u x) ^ (4 : ℕ)) (normalizedCubeMeasure Q) := by
    have h := (integrable_norm_rpow_iff huE.aestronglyMeasurable
      (by norm_num) (by norm_num)).2 huE
    have hfun : (fun x => ‖vecNorm (u x)‖ ^ ((8 : ℝ≥0∞).toReal)) =
        fun x => vecNormSq (u x) ^ (4 : ℕ) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (vecNorm_nonneg (u x))]
      rw [show ((8 : ℝ≥0∞).toReal) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        ← vecNorm_sq_eq_vecNormSq]
      ring
    rwa [hfun] at h
  exact (integrableOn_cubeSet_of_integrable_normalized' Q hint).mono_set
    (openCubeSet_subset_cubeSet Q)

/-! ## Measurability of the oscillation cell itself -/

/-- The oscillation cell of `e.nablaw.oscillations` is a measurable function of
the sample: it is the fourth root of the measurable fourth power. -/
theorem measurable_meshOscillationCell_freshShellDirichletGrad [NeZero d]
    (Q : TriadicCube d) (sigmaInv : ℝ) (nsh msh : ℤ) (e : Vec d)
    {n : ℤ} (R : TriadicCube d) (hsc : R.scale = n)
    (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wD : ShellSeq d → H10Function (openCubeSet Q))
    (hsol : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInv omega nsh msh e x))
    (hcoord : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => (wD omega).toH1Function.grad x k) (openCubeSet R) volume)
    (hcoordsq : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => ((wD omega).toH1Function.grad x k) ^ 2)
        (openCubeSet R) volume) :
    Measurable fun omega : ShellSeq d =>
      meshOscillationCell n (wD omega).toH1Function.grad R := by
  have h4 := measurable_meshOscillationCell_rpow_four_freshShellDirichletGrad Q sigmaInv
    nsh msh e R hsc hsub wD hsol hcoord hcoordsq
  have hEq : (fun omega : ShellSeq d =>
      meshOscillationCell n (wD omega).toH1Function.grad R) =
      fun omega : ShellSeq d =>
        Real.sqrt (Real.sqrt
          (meshOscillationCell n (wD omega).toH1Function.grad R ^ (4 : ℝ))) := by
    funext omega
    have hc0 : (0 : ℝ) ≤ meshOscillationCell n (wD omega).toH1Function.grad R :=
      meshOscillationCell_nonneg _ _ _
    have hpow : meshOscillationCell n (wD omega).toH1Function.grad R ^ (4 : ℝ) =
        ((meshOscillationCell n (wD omega).toH1Function.grad R) ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [rpow_four_eq_pow_four]
      ring
    rw [hpow, Real.sqrt_sq (by positivity), Real.sqrt_sq hc0]
  rw [hEq]
  exact Real.continuous_sqrt.measurable.comp (Real.continuous_sqrt.measurable.comp h4)

/-! ## The composition: `hmemOsc` and `hosc` at the closure's Dirichlet family -/

/-- **`hmemOsc` and `hosc`, produced.**

One threshold `gamma0`, produced before the model, such that in the manuscript's
own parameter range the closure's Dirichlet family satisfies both oscillation
legs of Step 5.

The composition is forced: the octic grid envelope produces its constant `E`
before its own threshold and before the model, and the re-sited endpoint takes
`E` as an argument; so `E` is taken first and the two thresholds are met at
their minimum.  The envelope's six spatial side conditions are discharged at the
closure family from the single `L^8` membership of the corrector gradient.

Proved from the ingredients listed in the module docstring. -/
theorem exists_gamma0_step5OscillationLegs (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {Eb : ℝ // 1 ≤ Eb}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (n : ℤ) (h : ℕ) (K j : ℕ) (nmesh : ℤ), 0 < h → n ≤ m0 →
            (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤
              ((K : ℤ) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ) →
            nmesh =
              recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) →
            (j : ℤ) = (K : ℤ) - nmesh →
            ∀ e : Vec d, vecNorm e ≤ 1 →
              (∀ R ∈ descendantsAtDepth (originCube d (K : ℤ)) j,
                MemLp (fun omega : CutoffSample d =>
                  meshOscillationCell nmesh
                    (fun x => (alongIncrementPath n h
                      (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
                        omega.val).toH1Function.grad x) R) 4
                  (cutoffSampleLaw M).toMeasure) ∧
              (gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
                    (descendantsAtDepth (originCube d (K : ℤ)) j)
                    (fun R omega => meshOscillationCell nmesh
                      (fun x => (alongIncrementPath n h
                        (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
                          omega.val).toH1Function.grad x) R) +
                  ((Annealed.sigmaBar M n : ℝ))⁻¹ *
                    gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
                      (descendantsAtDepth (originCube d (K : ℤ)) j)
                      (fun (R : TriadicCube d) (omega : CutoffSample d) =>
                        (3 : ℝ) ^ ((nmesh : ℤ) : ℝ) *
                          shellDerivNormSum n (n + (h : ℤ)) (triadicCubeShift R)
                            omega.val) ≤
                M.gamma ^ (15 : ℕ)) := by
  classical
  obtain ⟨E, hE0, g1, hg1pos, hg1q, henv⟩ :=
    exists_freshShellDirichlet_meshOscillation_memLp_and_eighthMoment_le d hd
  obtain ⟨g2, hg2pos, hg2q, hres⟩ :=
    exists_gamma0_freshShellDirichlet_step5MeshOscillationResited_le_gamma_pow_fifteen d hd E
  refine ⟨min g1 g2, lt_min hg1pos hg2pos, le_trans (min_le_left _ _) hg1q, ?_⟩
  intro M hMg m0 Eind hstate n h K j nmesh hh hn0 hcstar hK hnmesh hj e he
  have hMg1 : M.gamma ≤ g1 := le_trans hMg (min_le_left _ _)
  have hMg2 : M.gamma ≤ g2 := le_trans hMg (min_le_right _ _)
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  set sinv : ℝ := ((Annealed.sigmaBar M n : ℝ))⁻¹ with hsinv
  set wD : ShellSeq d → H10Function (openCubeSet Q) := fun omega =>
    alongIncrementPath n h (closureDirichletFamily sinv e K) omega with hwD
  have hsol : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sinv omega n (n + (h : ℤ)) e x) := fun omega =>
    isZeroTraceDirichletRhsWeakSolution_alongIncrementPath sinv e K n h omega
  -- the six spatial side conditions, from one `L^8` membership
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (wD omega).toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    fun omega => memLp_eight_grad_freshShellDirichlet hd Q sinv omega n (n + (h : ℤ)) e
      (wD omega) (hsol omega)
  have hmem : ∀ omega : ShellSeq d,
      MemLp (fun x => vecNorm ((wD omega).toH1Function.grad x)) 8
        (normalizedCubeMeasure Q) := fun omega =>
    memLp_vecNorm_eight_of_memLp_eight Q (hL8 omega)
  have hcoord : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => (wD omega).toH1Function.grad x k) (openCubeSet Q) volume :=
    fun omega k => integrableOn_openCubeSet_coord_of_memLp_eight Q (hL8 omega) k
  have hcoordsq : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => ((wD omega).toH1Function.grad x k) ^ 2)
        (openCubeSet Q) volume :=
    fun omega k => integrableOn_openCubeSet_coord_sq_of_memLp_eight Q (hL8 omega) k
  have hsq : ∀ omega : ShellSeq d,
      IntegrableOn (fun x => vecNormSq ((wD omega).toH1Function.grad x))
        (openCubeSet Q) volume :=
    fun omega => integrableOn_openCubeSet_vecNormSq_of_memLp_eight Q (hL8 omega)
  have hfour : ∀ omega : ShellSeq d,
      IntegrableOn (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ 2)
        (openCubeSet Q) volume :=
    fun omega => integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight Q (hL8 omega)
  have height : ∀ omega : ShellSeq d,
      IntegrableOn (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ (4 : ℕ))
        (openCubeSet Q) volume :=
    fun omega => integrableOn_openCubeSet_vecNormSq_pow_four_of_memLp_eight Q (hL8 omega)
  -- the envelope, at the shifted scale bookkeeping
  have hcancel : n + (h : ℤ) - (h : ℤ) = n := by omega
  have hsol' : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) (wD omega)
        (fun x => -streamForcing
          ((Annealed.sigmaBar M (n + (h : ℤ) - (h : ℤ)) : ℝ))⁻¹ omega
          (n + (h : ℤ) - (h : ℤ)) (n + (h : ℤ)) e x) := by
    simp only [hcancel]
    exact hsol
  have hnmeshK : nmesh ≤ (K : ℤ) := by omega
  obtain ⟨hmem8meso, hElemeso⟩ := henv M hMg1 m0 Eind hstate (n + (h : ℤ)) (K : ℤ) h hh
    (by omega) hcstar hK e 0 he
    (by
      have hz : vecNormSq (0 : Vec d) = 0 := by
        show ∑ i, (0 : Vec d) i * (0 : Vec d) i = 0
        simp
      rw [vecNorm_eq_sqrt_vecNormSq, hz, Real.sqrt_zero]
      norm_num)
    wD hsol' hmem hcoord hcoordsq hsq hfour height nmesh hnmeshK
  have hgridEq : mesoCubeGrid d (K : ℤ) nmesh = descendantsAtDepth Q j := by
    rw [mesoCubeGrid_eq_descendantsAtDepth hnmeshK, hQ]
    congr 1
    omega
  rw [hgridEq] at hmem8meso hElemeso
  -- `hosc`
  have hoscBound := hres M hMg2 m0 Eind hstate n h K j nmesh hh hn0 hcstar hK hnmesh hj
    e he wD hsol hmem8meso hElemeso
  refine ⟨?_, hoscBound⟩
  -- `hmemOsc`
  intro R hR
  have hscR : R.scale = nmesh := by
    have hbase := scale_of_mem_descendantsAtDepth_originCube hR
    rw [hbase]
    omega
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hmeas := measurable_meshOscillationCell_freshShellDirichletGrad Q sinv n
    (n + (h : ℤ)) e R hscR hsub wD hsol
    (fun omega k => (hcoord omega k).mono_set hsub)
    (fun omega k => (hcoordsq omega k).mono_set hsub)
  have hintP : Integrable (fun omega : ShellSeq d =>
      meshOscillationCell nmesh (wD omega).toH1Function.grad R ^ (4 : ℝ)) M.P.toMeasure :=
    (hmem8meso R hR).integrable (by norm_num)
  have hbase : MemLp (fun omega : ShellSeq d =>
      meshOscillationCell nmesh (wD omega).toH1Function.grad R) 4 M.P.toMeasure := by
    refine (integrable_norm_rpow_iff hmeas.aestronglyMeasurable
      (by norm_num) (by norm_num)).1 ?_
    have hfun : (fun omega : ShellSeq d =>
        ‖meshOscillationCell nmesh (wD omega).toH1Function.grad R‖ ^
          ((4 : ℝ≥0∞).toReal)) =
        fun omega : ShellSeq d =>
          meshOscillationCell nmesh (wD omega).toH1Function.grad R ^ (4 : ℝ) := by
      funext omega
      rw [Real.norm_eq_abs, abs_of_nonneg (meshOscillationCell_nonneg _ _ _)]
      norm_num
    rw [hfun]
    exact hintP
  exact memLp_comp_val_cutoffSampleLaw M hbase

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
