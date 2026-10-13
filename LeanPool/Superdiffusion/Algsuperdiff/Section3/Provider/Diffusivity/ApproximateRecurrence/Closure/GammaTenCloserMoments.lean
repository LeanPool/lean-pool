/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenCloserGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitProducerLoad
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationSplitFoldArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationStationarity

/-!
# GammaTenCloserMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two `L^4` memberships of the Step-2 grid fold

ABK26, Step 2 of `l.approximate.recurrence.formula`.

## The gap this module fills

`Closure.GammaTenAssemblyMoments.descendantsAverage_integral_fold_le_of_memLp_four_grid_load`
asks for three `L^4` legs.  The two *deterministic* ones have moment producers
but no membership producer:

* the **ellipticity** leg is measurable only at the origin cube
  (`LocalizationFluctuationNumericEllipticity.measurable_gaugedEllipticitySum_originCube`),
  while the fold reads it at the cell's own scale-`(n+h)` **ancestor**;
* the **load** leg has a grid fourth moment
  (`Closure.GammaTenLoad.exists_gammaTenLoadConst_root`) but a grid moment bound
  is not an integrability statement --- an undefined Bochner integral is `0`.

Both are supplied here.

## What is proved

* `measurePreserving_translateCutoffSample` --- the cutoff-sample law is
  translation invariant, in the `MeasurePreserving` spelling
  (`Cutoff.Symmetry.map_translateCutoffSample_cutoffSampleLaw` repackaged).
* `memLp_gaugedEllipticitySum_of_scale` --- `L^p` membership of the gauged
  ellipticity sum transports from `cu_m` to **any** cube of scale `m`, by the
  pathwise covariance
  `LocalizationFluctuationStationarity.gaugedEllipticitySum_scale_eq_originCube`
  composed with the measure-preserving translation.
* `exists_regime_memLp_four_gaugedEllipticitySum_ancestorAtScale` --- the
  ellipticity leg is in `L^4` at the ancestor, under exactly the two clauses of
  `Closure.ClosureRegime` that
  `LocalizationFluctuationSplitFoldArithmetic.exists_regime_gaugedEllipticitySum_pow_four_le`
  uses.  The membership comes from the `L^8` conjunct of
  `LocalizationFluctuationNumericEllipticity.integral_gaugedEllipticitySum_rpow_eight_le`.
* `memLp_four_of_integrable_pow_four`, `le_card_mul_descendantsAverage` --- two
  elementary devices.
* `measurable_gammaTenLoadLeg`, `memLp_four_gammaTenLoadLeg` --- the load leg is
  in `L^4` at every cell: measurable by
  `Closure.SplitProducerLoad.measurable_meshCellLoad`, and dominated cellwise by
  the pathwise majorant of `Closure.GammaTenLoad.exists_gammaTenLoadPathwiseConst`
  whose sample moment is `Closure.Step5InputGradMoment`'s
  `exists_integral_streamIncrementLpNorm_eight_pow_four_le`.

## Binders

Regime binders only for the ellipticity leg (the induction state, the two
largeness clauses and a produced `cgamma`-threshold); for the load leg the
parameters of `e.recurrence.params` and the two direction bounds.  No smallness
gate is assumed and every threshold is produced.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, the load display,
  `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The ellipticity leg -/

/-- The cutoff-sample law is invariant under a real translation of the shell
field, in the `MeasurePreserving` spelling. -/
theorem measurePreserving_translateCutoffSample (M : ABKModel d) (v : Vec d) :
    MeasurePreserving (translateCutoffSample (d := d) v)
      (cutoffSampleLaw M).toMeasure (cutoffSampleLaw M).toMeasure :=
  ⟨measurable_translateCutoffSample v, map_translateCutoffSample_cutoffSampleLaw M v⟩

/-- `L^p` membership of the gauged ellipticity sum transports from the origin
cube to an arbitrary cube of the same scale. -/
theorem memLp_gaugedEllipticitySum_of_scale [NeZero d] (M : ABKModel d) (L m : ℤ)
    {T : TriadicCube d} (hT : T.scale = m) (sigmaBar s : ℝ) (p : ℝ≥0∞)
    (hmem : MemLp (fun omega : CutoffSample d =>
        gaugedEllipticitySum sigmaBar (originCube d m) s
          (coefficientCutoffTriadicCoeffFamily M L omega)) p
      (cutoffSampleLaw M).toMeasure) :
    MemLp (fun omega : CutoffSample d =>
        gaugedEllipticitySum sigmaBar T s
          (coefficientCutoffTriadicCoeffFamily M L omega)) p
      (cutoffSampleLaw M).toMeasure := by
  set v : Vec d :=
    fun i => ((T.index i : ℤ) : ℝ) * cubeScaleFactor (originCube d m) with hv
  have hcomp := hmem.comp_measurePreserving (measurePreserving_translateCutoffSample M v)
  have hfun : (fun omega : CutoffSample d =>
      gaugedEllipticitySum sigmaBar T s
        (coefficientCutoffTriadicCoeffFamily M L omega)) =
      (fun omega : CutoffSample d =>
        gaugedEllipticitySum sigmaBar (originCube d m) s
          (coefficientCutoffTriadicCoeffFamily M L omega)) ∘
        (translateCutoffSample (d := d) v) := by
    funext omega
    exact gaugedEllipticitySum_scale_eq_originCube M L m omega hT sigmaBar s
  rw [hfun]
  exact hcomp

/-- **The `L^4` membership of the Step-2 ellipticity leg at the cell's own
scale-`m` ancestor**, under exactly the two regime clauses that
`LocalizationFluctuationSplitFoldArithmetic.exists_regime_gaugedEllipticitySum_pow_four_le`
uses and below a **produced** `cgamma`-threshold.

The membership at `cu_m` is the `L^8` conjunct of
`LocalizationFluctuationNumericEllipticity.integral_gaugedEllipticitySum_rpow_eight_le`;
`memLp_gaugedEllipticitySum_of_scale` transports it to the ancestor.

exactly on the four listed premises. -/
theorem exists_regime_memLp_four_gaugedEllipticitySum_ancestorAtScale (d : ℕ) [NeZero d] :
    ∃ Cell gamma0 : ℝ, 0 < Cell ∧ 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d) (m : ℤ) (Ec : {E : ℝ // 1 ≤ E}),
        M.gamma ≤ gamma0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) Ec →
        Cell * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) →
        M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ) →
        ∀ R : TriadicCube d, R.scale ≤ m →
          MemLp (fun omega : CutoffSample d =>
              gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ)
                (ancestorAtScale R m) M.gamma
                (coefficientCutoffTriadicCoeffFamily M m omega)) 4
            (cutoffSampleLaw M).toMeasure := by
  obtain ⟨C, hC0, hmain⟩ := integral_gaugedEllipticitySum_rpow_eight_le d
  obtain ⟨g0, hg00, hg0q, hgate⟩ := exists_gamma_threshold_ellipticityGate hC0
  refine ⟨regimeEllipticityConst C, g0, regimeEllipticityConst_pos C, hg00, hg0q, ?_⟩
  intro M m Ec hMgamma hstate hlarge hsmall R hm
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
  have hEone : (1 : ℝ) ≤ (Ec : ℝ) := Ec.property
  have hmax : max (Real.exp (2 * C)) (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) :=
    gammaRegime_max_exp_le hcstar0 hcstar hlarge
  have hrpow : (Ec : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) :=
    gammaRegime_E_le_rpow_neg_fifth hEone hgamma0 hsmall
  have hgateM : M.gamma / 2 +
      Real.exp (-(C⁻¹ * (((Ec : ℝ))⁻¹) ^ (2 : ℕ) * M.gamma⁻¹)) ≤ M.gamma :=
    hgate (Ec : ℝ) M.gamma hEone hgamma0 hMgamma hsmall
  obtain ⟨hmem8, -⟩ := hmain M m Ec hstate hmax hrpow hgateM
  have hmem4 : MemLp (fun omega : CutoffSample d =>
      gaugedEllipticitySum (Annealed.sigmaBar M (m - 1) : ℝ) (originCube d m) M.gamma
        (coefficientCutoffTriadicCoeffFamily M m omega)) 4
      (cutoffSampleLaw M).toMeasure := hmem8.mono_exponent (by norm_num)
  exact memLp_gaugedEllipticitySum_of_scale M m m (ancestorAtScale_scale R hm) _ _ 4 hmem4

/-! ## The load leg -/

/-- `L^4` membership of a nonnegative measurable function with an integrable
fourth power. -/
theorem memLp_four_of_integrable_pow_four {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ} (hf : ∀ w, 0 ≤ f w)
    (hm : AEStronglyMeasurable f mu)
    (hint : Integrable (fun w => f w ^ (4 : ℕ)) mu) : MemLp f 4 mu := by
  refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
  have hfun : (fun w => ‖f w‖ ^ ((4 : ℝ≥0∞).toReal)) = fun w => f w ^ (4 : ℕ) := by
    funext w
    rw [Real.norm_of_nonneg (hf w),
      show ((4 : ℝ≥0∞).toReal) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hfun]
  exact hint

/-- Each member of a nonnegative family is below the cardinality times its
descendant average. -/
theorem le_card_mul_descendantsAverage (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ) (hF : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ F R)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) :
    F R ≤ ((descendantsAtDepth Q j).card : ℝ) * descendantsAverage Q j F := by
  classical
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨R, hR⟩
  have hsum : F R ≤ ∑ S ∈ descendantsAtDepth Q j, F S :=
    Finset.single_le_sum hF hR
  have hEq : ((descendantsAtDepth Q j).card : ℝ) * descendantsAverage Q j F =
      ∑ S ∈ descendantsAtDepth Q j, F S := by
    unfold descendantsAverage
    field_simp
  rw [hEq]
  exact hsum

/-- **The Step-2 load leg is measurable in the sample**, at every cell of the
closure mesh and at the closure's own corrector families. -/
theorem measurable_gammaTenLoadLeg [NeZero d] (M : ABKModel d) (n : ℤ) (h K : ℕ)
    (e e' : Vec d) {j : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    Measurable fun omega : CutoffSample d =>
      Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M n)
        (meshCellLoad M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega)) := by
  have hP : Measurable (meshCellLoad M n h (K : ℤ) e e'
      (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R) :=
    measurable_meshCellLoad M n h (K : ℤ) e e' _ _
      (isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e)
      (isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e') hR
  refine Real.continuous_sqrt.measurable.comp ?_
  have hEq : (fun omega : CutoffSample d => annealedSqrtNormSq (Annealed.sigmaBar M n)
      (meshCellLoad M n h (K : ℤ) e e'
        (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega)) =
      fun omega : CutoffSample d => ((Annealed.sigmaBar M n : ℝ)) *
        vecNormSq (meshCellLoad M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega).1 +
        ((Annealed.sigmaBar M n : ℝ))⁻¹ *
        vecNormSq (meshCellLoad M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega).2 :=
    rfl
  rw [hEq]
  exact ((measurable_vecNormSq_of_measurable (measurable_fst.comp hP)).const_mul _).add
    ((measurable_vecNormSq_of_measurable (measurable_snd.comp hP)).const_mul _)

/-- **The Step-2 load leg is in `L^4`**, at every cell of the closure mesh.

The grid fourth moment of `Closure.GammaTenLoad.exists_gammaTenLoadConst_root` is
a bound on a Bochner integral and therefore not by itself an integrability
statement; the membership comes from the *pathwise* majorant of
`Closure.GammaTenLoad.exists_gammaTenLoadPathwiseConst`, read at a single cell
(one factor of the grid cardinality, which is harmless because the statement is
per cell), whose sample moment is
`Closure.Step5InputGradMoment.exists_integral_streamIncrementLpNorm_eight_pow_four_le`.

on the parameters of `e.recurrence.params` and the two direction bounds. -/
theorem memLp_four_gammaTenLoadLeg [NeZero d] (hd : 2 ≤ d) (M : ABKModel d) (n : ℤ)
    (h K : ℕ) (e e' : Vec d) (he : vecNorm e ≤ 1) (he' : vecNorm e' ≤ 1)
    (hh : 0 < h) (hmK : n + (h : ℤ) ≤ (K : ℤ)) {j : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    MemLp (fun omega : CutoffSample d =>
      Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M n)
        (meshCellLoad M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega))) 4
      (cutoffSampleLaw M).toMeasure := by
  classical
  obtain ⟨Cpath, hCpath0, hpath⟩ := exists_gammaTenLoadPathwiseConst d hd
  obtain ⟨Ckm, -, hkm⟩ := exists_integral_streamIncrementLpNorm_eight_pow_four_le d
  have hnlt : n < n + (h : ℤ) := by
    have : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh
    omega
  obtain ⟨hLint, -⟩ := hkm M (K : ℤ) n (n + (h : ℤ)) hnlt hmK
  set sigma : PositiveScalar := Annealed.sigmaBar M n with hsigma
  set G : CutoffSample d → ℝ := fun omega =>
    Real.sqrt (annealedSqrtNormSq sigma
      (meshCellLoad M n h (K : ℤ) e e'
        (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega))
    with hG
  have hG0 : ∀ omega, 0 ≤ G omega := fun omega => Real.sqrt_nonneg _
  have hmeas : Measurable G := measurable_gammaTenLoadLeg M n h K e e' hR
  set card : ℝ := ((descendantsAtDepth (originCube d (K : ℤ)) j).card : ℝ) with hcard
  set Maj : CutoffSample d → ℝ := fun omega =>
    card * (32 + Cpath * (((sigma : ℝ))⁻¹ ^ (4 : ℕ) *
      Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n (n + (h : ℤ))
        omega.val ^ (4 : ℕ))) with hMaj
  have hMajint : Integrable Maj (cutoffSampleLaw M).toMeasure := by
    rw [hMaj]
    exact (((integrable_const (32 : ℝ)).add
      ((hLint.const_mul (((sigma : ℝ))⁻¹ ^ (4 : ℕ))).const_mul Cpath))).const_mul card
  have hdom : ∀ omega : CutoffSample d, G omega ^ (4 : ℕ) ≤ Maj omega := by
    intro omega
    have hbase := hpath M n h K j e e' he he' omega.val
    have hpt : G omega ^ (4 : ℕ) = annealedSqrtNormSq sigma
        (meshCellLoad M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega)
          ^ (2 : ℕ) := by
      rw [hG]
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
        Real.sq_sqrt (annealedSqrtNormSq_nonneg _ _)]
    have hle := le_card_mul_descendantsAverage (originCube d (K : ℤ)) j
      (fun S => annealedSqrtNormSq sigma
        (principalPz sigma omega.val n (n + (h : ℤ)) e e' S
          (closureDirichletAlong M n h K e omega.val)
          (closureNeumannAlong M n h K e' omega.val)) ^ (2 : ℕ))
      (fun S _ => pow_nonneg (annealedSqrtNormSq_nonneg _ _) 2) hR
    have hcard0 : (0 : ℝ) ≤ card := by positivity
    rw [hpt]
    refine le_trans hle ?_
    rw [hMaj]
    refine mul_le_mul_of_nonneg_left ?_ hcard0
    refine hbase.trans (le_of_eq ?_)
    rw [mul_pow]
  refine memLp_four_of_integrable_pow_four hG0 hmeas.aestronglyMeasurable ?_
  refine Integrable.mono' hMajint (hmeas.pow_const 4).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ G omega ^ (4 : ℕ))]
  exact hdom omega

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
