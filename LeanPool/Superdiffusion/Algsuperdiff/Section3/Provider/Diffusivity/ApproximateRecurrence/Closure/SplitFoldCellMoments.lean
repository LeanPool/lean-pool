/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitObligationsBackground
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitObligationsRegime
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5InputGradMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationCorrectorRegularity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationCellIntegrable
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationOscillationBridge

/-!
# SplitFoldCellMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two cell-energy moments `hmom` of the Step-1--3 split, produced

ABK26, `l.approximate.recurrence.formula`, Steps 1--3, `e.Fz.def`, the
background display, `e.def.w`, `e.nablaw.in.L.eight`, `e.km.kn.Lp`.

## What this module supplies

`Closure.SplitObligations.splitScaleObligations_integrability_of_regime` carries
one analytic binder, `hmom`: for every mesoscopic cell of the closure mesh,

* the **second** sample moment of the Step-2 background's normalized *potential*
  cell energy `meshCellBackgroundPotentialEnergy`, and
* the **first** sample moment of its *flux* cell energy
  `meshCellBackgroundFluxEnergy`.

This module proves both, at the closure's own corrector families, inside the
manuscript's own regime, and therefore removes `hmom`: the export
`splitScaleObligations_integrability_closureFamilies` produces conjuncts (1) and
(2) of `Closure.SplitProducerFold.SplitScaleObligations` with no analytic binder
beyond `Closure.ClosureRegime` and the two direction bounds.

## The two routes

`SplitObligationsBackground.meshCellBackgroundPotentialEnergy_eq` and
`..._FluxEnergy_eq` put the two cell energies in the closed forms

```
  E_pot = shom^{-1} fint_R |e' + grad w_D|^2 ,
  E_flux = shom fint_R |e + (grad w_N + shom^{-1} (k_{n+h} - k_n) e')|^2 .
```

* **Potential leg.**  Since `|e' + v|^2 <= 2|e'|^2 + 2|v|^2` and the window
  identity `openCubeAtScale (triadicCubeShift R) R.scale = openCubeSet R`
  identifies `fint_R |grad w_D|^2` with `meshEnergyCell R.scale (grad w_D) R ^
  2`
  (`LocalizationFluctuationCellIntegrable.meshEnergyCell_rpow_four_eq_sq_volumeAverage`),
  the *square* of the potential energy is dominated by the proved fourth-power
  producer
  `LocalizationFluctuationCellIntegrable.exists_gamma0_integrable_freshShellDirichlet_meshEnergyCell_rpow_four`.
* **Flux leg.**  `|e + grad w_N + F|^2 <= 2|e|^2 + 4|grad w_N|^2 + 4|F|^2`.
  The middle term is the Neumann mirror of the same producer, read at its first
  moment; the forcing term is bounded by
  `volumeAverage_vecNormSq_streamForcing_le` --- a cell-level Jensen step (`L^2
  <= L^8` on the normalized cube) fed by the proved
  `Corrector.cubeEuclideanLpNorm_streamForcing_le` --- against the fourth
  moment of the fresh-shell `L^8` norm
  (`Closure.Step5InputGradMoment.exists_integral_streamIncrementLpNorm_eight_pow_four_le`,
  the proved frozen theorem `e.km.kn.Lp`).

The measurability halves of both legs are produced here by one generic device,
`measurable_volumeAverage_vecNormSq_of_measurable_class`: the window `L^2`
functional is `1`-Lipschitz on `L^2`, so the normalized second energy over a
measurable window is a continuous functional of the sample's `L^2` class, and
the two classes are the proved
`LocalizationFluctuationBackgroundClass.measurable_toHilbertVectorL2OfVecField_freshShellDirichletGrad`
and `..._neumannFluxField`, shifted by a constant vector.

## Binders

`splitScaleObligations_integrability_closureFamilies` carries exactly
`Closure.ClosureRegime` at the produced threshold and the two direction bounds
`|e| <= 1`, `|e'| <= 1`.  The large-cube gate, the depth-naming identity, the
`cgamma`-thresholds of the two producers and the spatial families of `e.def.w`
are all produced.  No smallness, moment or measurability proposition survives.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Steps 1--3, `e.Fz.def`, the
  background display, `e.def.w`, `e.nablaw.in.L.eight`, `e.recurrence.params`.
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

/-! ## The window `L^2` functional is Lipschitz on `L^2` -/

section Window

variable {alpha E : Type*} [MeasurableSpace alpha] [NormedAddCommGroup E]

/-- The `L^2` size of an `L^2` class over a window, read through the seminorm of
the restricted measure. -/
def cellWindowNorm (mu : Measure alpha) (S : Set alpha) (F : Lp E 2 mu) : ℝ :=
  (eLpNorm (F : alpha → E) 2 (mu.restrict S)).toReal

private theorem cellWindowNorm_ne_top (mu : Measure alpha) (S : Set alpha)
    (F : Lp E 2 mu) : eLpNorm (F : alpha → E) 2 (mu.restrict S) ≠ ⊤ :=
  ne_top_of_le_ne_top (Lp.memLp F).eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

private theorem cellWindow_restrict_sub_le (mu : Measure alpha) (S : Set alpha)
    (F G : Lp E 2 mu) :
    eLpNorm (F : alpha → E) 2 (mu.restrict S) ≤
      eLpNorm (G : alpha → E) 2 (mu.restrict S) +
        eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) := by
  have hsplit : (F : alpha → E) =
      (G : alpha → E) + ((F : alpha → E) - (G : alpha → E)) := by
    funext x; simp
  calc eLpNorm (F : alpha → E) 2 (mu.restrict S)
      = eLpNorm ((G : alpha → E) + ((F : alpha → E) - (G : alpha → E))) 2
          (mu.restrict S) := by rw [← hsplit]
    _ ≤ eLpNorm (G : alpha → E) 2 (mu.restrict S) +
          eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) :=
        eLpNorm_add_le (by norm_num)

/-- **The window `L^2` functional is `1`-Lipschitz on `L^2`.**  Restriction only
decreases the seminorm, so the ambient `L^2` distance controls the window one. -/
private theorem lipschitzWith_cellWindowNorm (mu : Measure alpha) (S : Set alpha) :
    LipschitzWith 1 (cellWindowNorm (E := E) mu S) := by
  refine LipschitzWith.of_dist_le_mul fun F G => ?_
  have hdiff : eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu =
      eLpNorm ((F - G : Lp E 2 mu) : alpha → E) 2 mu :=
    eLpNorm_congr_ae (Lp.coeFn_sub F G).symm
  have hdifftop : eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu ≠ ⊤ := by
    rw [hdiff]; exact (Lp.memLp (F - G)).eLpNorm_ne_top
  have hrestr : eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) ≤
      eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hrestrtop : eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) ≠ ⊤ :=
    ne_top_of_le_ne_top hdifftop hrestr
  have hdist : dist F G =
      (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu).toReal := by
    rw [hdiff, dist_eq_norm, Lp.norm_def]
  have hsym : eLpNorm ((G : alpha → E) - (F : alpha → E)) 2 (mu.restrict S) =
      eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) :=
    eLpNorm_sub_comm _ _ _ _
  have h1 : cellWindowNorm mu S F - cellWindowNorm mu S G ≤
      (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S)).toReal := by
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨cellWindowNorm_ne_top mu S G, hrestrtop⟩)
      (cellWindow_restrict_sub_le mu S F G)
    rw [ENNReal.toReal_add (cellWindowNorm_ne_top mu S G) hrestrtop] at hmono
    show (eLpNorm (F : alpha → E) 2 (mu.restrict S)).toReal -
      (eLpNorm (G : alpha → E) 2 (mu.restrict S)).toReal ≤ _
    linarith
  have h2 : cellWindowNorm mu S G - cellWindowNorm mu S F ≤
      (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S)).toReal := by
    have hbase := cellWindow_restrict_sub_le mu S G F
    rw [hsym] at hbase
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨cellWindowNorm_ne_top mu S F, hrestrtop⟩) hbase
    rw [ENNReal.toReal_add (cellWindowNorm_ne_top mu S F) hrestrtop] at hmono
    show (eLpNorm (G : alpha → E) 2 (mu.restrict S)).toReal -
      (eLpNorm (F : alpha → E) 2 (mu.restrict S)).toReal ≤ _
    linarith
  have hfin : (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S)).toReal ≤
      (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu).toReal :=
    ENNReal.toReal_mono hdifftop hrestr
  rw [Real.dist_eq, abs_le]
  refine ⟨?_, ?_⟩ <;> simp only [NNReal.coe_one, one_mul] <;> rw [hdist] <;> linarith

/-- The square of the window functional is the window integral of `‖F‖^2`. -/
private theorem cellWindowNorm_sq (mu : Measure alpha) (S : Set alpha) (F : Lp E 2 mu) :
    cellWindowNorm mu S F ^ 2 = ∫ x in S, ‖(F : alpha → E) x‖ ^ 2 ∂mu := by
  have hmem : MemLp (F : alpha → E) 2 (mu.restrict S) := (Lp.memLp F).restrict S
  have hnn : (0 : ℝ) ≤ ∫ x in S, ‖(F : alpha → E) x‖ ^ (2 : ℝ) ∂mu :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hrw : ∫ x in S, ‖(F : alpha → E) x‖ ^ (2 : ℝ) ∂mu =
      ∫ x in S, ‖(F : alpha → E) x‖ ^ (2 : ℕ) ∂mu := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  rw [cellWindowNorm, hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have hto : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [hto, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _),
    ← Real.rpow_natCast ((∫ x in S, ‖(F : alpha → E) x‖ ^ (2 : ℝ) ∂mu) ^ (2 : ℝ)⁻¹) 2,
    ← Real.rpow_mul hnn,
    show ((2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_one, hrw]

end Window

/-! ## The generic window second-energy observable -/

/-- **The normalized second energy of a measurable family of vector `L^2` classes
over a measurable window is measurable in the sample.**

Unconditional apart from the window geometry and the measurability of the family
of classes; no property of the underlying fields is used. -/
theorem measurable_volumeAverage_vecNormSq_of_measurable_class {Omega : Type*}
    [MeasurableSpace Omega] {U S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ U)
    {u : Omega → Vec d → Vec d} (hu : ∀ omega, MemVectorL2 U (u omega))
    (hmeas : Measurable fun omega => toHilbertVectorL2OfVecField (hu omega)) :
    Measurable fun omega => volumeAverage S (fun x => vecNormSq (u omega x)) := by
  have hrestrict : (volumeMeasureOn U).restrict S = volume.restrict S := by
    rw [volumeMeasureOn, Measure.restrict_restrict hS,
      Set.inter_eq_self_of_subset_left hSU]
  have hEq : (fun omega => volumeAverage S (fun x => vecNormSq (u omega x))) =
      fun omega => (volume S).toReal⁻¹ *
        cellWindowNorm (volumeMeasureOn U) S
          (toHilbertVectorL2OfVecField (hu omega)) ^ 2 := by
    funext omega
    rw [cellWindowNorm_sq]
    have hae : ∀ᵐ x ∂((volumeMeasureOn U).restrict S),
        ‖((toHilbertVectorL2OfVecField (hu omega) :
            HilbertVectorL2 U) : Vec d → HilbertVec d) x‖ ^ 2 =
          vecNormSq (u omega x) := by
      refine ((coeFn_toHilbertVectorL2OfVecField (hu omega)).filter_mono
        (ae_mono Measure.restrict_le_self)).mono fun x hx => ?_
      rw [hx, hilbertifyVecField]
      exact HilbertVec.norm_sq_ofVec (u omega x)
    rw [integral_congr_ae hae, hrestrict]
    rfl
  rw [hEq]
  exact measurable_const.mul
    (((lipschitzWith_cellWindowNorm (volumeMeasureOn U) S).continuous.measurable.comp
      hmeas).pow_const 2)

/-- Adding a fixed vector to a measurable family of vector `L^2` classes keeps the
family of classes measurable.  Unconditional. -/
theorem measurable_toHilbertVectorL2OfVecField_const_add {Omega : Type*}
    [MeasurableSpace Omega] {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (c : Vec d)
    {f : Omega → Vec d → Vec d} (hf : ∀ omega, MemVectorL2 U (f omega))
    (hcf : ∀ omega, MemVectorL2 U (fun x => c + f omega x))
    (hmeas : Measurable fun omega => toHilbertVectorL2OfVecField (hf omega)) :
    Measurable fun omega => toHilbertVectorL2OfVecField (hcf omega) := by
  have hconst : MemVectorL2 U (fun _ : Vec d => c) := memLp_const c
  have hrw : (fun omega => toHilbertVectorL2OfVecField (hcf omega)) =
      fun omega => toHilbertVectorL2OfVecField hconst +
        toHilbertVectorL2OfVecField (hf omega) := by
    funext omega
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_toHilbertVectorL2OfVecField (hcf omega),
      MeasureTheory.Lp.coeFn_add (toHilbertVectorL2OfVecField hconst)
        (toHilbertVectorL2OfVecField (hf omega)),
      coeFn_toHilbertVectorL2OfVecField hconst,
      coeFn_toHilbertVectorL2OfVecField (hf omega)] with x h1 h2 h3 h4
    rw [h1, h2]
    simp only [Pi.add_apply]
    rw [h3, h4]
    apply HilbertVec.ext
    intro i
    simp [hilbertifyVecField]
  rw [hrw]
  exact (continuous_const.add continuous_id).measurable.comp hmeas

/-! ## Small bridges -/

/-- The Chapter-2 average over a cell is the volume average over its open cube. -/
theorem average_cubeDomain_eq_volumeAverage (R : TriadicCube d) (f : Vec d → ℝ) :
    Ch02.average (cubeDomain R) f = volumeAverage (openCubeSet R) f := rfl

/-- The volume average over the open cube is the cube average. -/
theorem volumeAverage_openCubeSet_eq_cubeAverage_fold (Q : TriadicCube d)
    (f : Vec d → ℝ) : volumeAverage (openCubeSet Q) f = cubeAverage Q f := by
  unfold volumeAverage cubeAverage
  rw [volume_openCubeSet_toReal, setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-- `L^p` integrability transports from the shell-sequence law to the cutoff
sample law along the sample inclusion.  Unconditional. -/
theorem integrable_comp_val_cutoffSampleLaw (M : ABKModel d) {G : ShellSeq d → ℝ}
    (hG : Integrable G M.P.toMeasure) :
    Integrable (fun omega : CutoffSample d => G omega.val)
      (cutoffSampleLaw M).toMeasure := by
  have hemb : MeasurableEmbedding (Subtype.val : CutoffSample d → ShellSeq d) :=
    MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)
  rw [← map_cutoffSampleLaw_val M, hemb.integrable_map_iff] at hG
  exact hG

/-- A nonnegative random variable with an integrable square is integrable. -/
theorem integrable_of_sq_integrable {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {A : Omega → ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega) (hAm : AEStronglyMeasurable A mu)
    (hAsq : Integrable (fun omega => A omega ^ (2 : ℕ)) mu) : Integrable A mu := by
  refine Integrable.mono' ((integrable_const ((1 : ℝ) / 2)).add
    (hAsq.const_mul ((1 : ℝ) / 2))) hAm (Filter.Eventually.of_forall fun omega => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (hA0 omega)]
  nlinarith [sq_nonneg (A omega - 1)]

/-- The volume average of a constant plus an integrable function. -/
theorem volumeAverage_const_add {S : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn S)]
    (hvol : (MeasureTheory.volume S).toReal ≠ 0) (c : ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f S volume) :
    volumeAverage S (fun x => c + f x) = c + volumeAverage S f := by
  have hb := volumeAverage_add (U := S) (f := fun _ : Vec d => c) (g := f)
    (integrable_const c) hf
  rw [volumeAverage_const hvol] at hb
  exact hb

/-- The volume average of a constant multiple. -/
theorem volumeAverage_const_mul' (S : Set (Vec d)) (c : ℝ) (f : Vec d → ℝ) :
    volumeAverage S (fun x => c * f x) = c * volumeAverage S f := by
  have hb := volumeAverage_smul S c f
  simpa using! hb

/-- The regime's largeness gate is monotone in its threshold. -/
theorem closureRegime_mono {C C' : ℝ} (hC : C' ≤ C) {M : ABKModel d} {n : ℤ} {h : ℕ}
    {Ec : {E : ℝ // 1 ≤ E}} (hreg : ClosureRegime C M n h Ec) :
    ClosureRegime C' M n h Ec := by
  obtain ⟨hstate, hpos, hCE, hgammaE, hcap, hdrift⟩ := hreg
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  refine ⟨hstate, hpos, ?_, hgammaE, hcap, hdrift⟩
  exact le_trans (mul_le_mul_of_nonneg_right hC (inv_pos.2 hcstar0).le) hCE

/-! ## The `L^8` spatial families of the closure's corrector families -/

/-- The closure's Dirichlet corrector gradient is `L^8` on the localization cube.
Proved from `memLp_eight_grad_freshShellDirichlet`. -/
theorem memLp_eight_grad_closureDirichletAlong [NeZero d] (hd : 2 ≤ d) (M : ABKModel d)
    (n : ℤ) (h : ℕ) (K : ℕ) (e : Vec d) (omega : ShellSeq d) :
    MemLp (closureDirichletAlong M n h K e omega).toH1Function.grad (8 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (K : ℤ))) :=
  memLp_eight_grad_freshShellDirichlet hd (originCube d (K : ℤ))
    ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e _
    (isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e omega)

/-- The mean-zero Neumann mirror. -/
theorem memLp_eight_grad_closureNeumannAlong [NeZero d] (hd : 2 ≤ d) (M : ABKModel d)
    (n : ℤ) (h : ℕ) (K : ℕ) (e' : Vec d) (omega : ShellSeq d) :
    MemLp (closureNeumannAlong M n h K e' omega).toH1Function.grad (8 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (K : ℤ))) :=
  memLp_eight_grad_freshShellNeumann hd (originCube d (K : ℤ))
    ((Annealed.sigmaBar M n : ℝ))⁻¹ omega n (n + (h : ℤ)) e' _
    (isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e' omega)

/-! ## The cell `L^2` average of the forcing of `e.def.w` -/

/-- **The cell second energy of the forcing of `e.def.w`, against the fresh-shell
`L^8` norm.**

On any cell of the localization cube, `fint_R |shom^{-1} (k_m - k_n) e'|^2` is at
most a purely geometric ratio times `(shom^{-1} ||k_m - k_n||_{L^8bar(cu_l)})^2`:
the window integral is below the cube integral, and on the normalized cube
measure --- a probability measure --- the `L^2` norm is below the `L^8` one.

only on the geometry `hsub`, the sign of the gauge and the direction bound.
Anchor-free. -/
theorem volumeAverage_vecNormSq_streamForcing_le [NeZero d] {l : ℤ}
    {R : TriadicCube d} (hsub : openCubeSet R ⊆ openCubeSet (originCube d l))
    {sinv : ℝ} (hsinv : 0 ≤ sinv) (omega : ShellSeq d) (n m : ℤ) {e' : Vec d}
    (he' : Book.Ch02.vecNorm e' ≤ 1) :
    volumeAverage (openCubeSet R)
        (fun x => vecNormSq (streamForcing sinv omega n m e' x)) ≤
      (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ * cubeVolume (originCube d l) *
        (sinv * Provider.Stream.streamIncrementLpNorm 8 l n m omega) ^ (2 : ℕ) := by
  classical
  set Q : TriadicCube d := originCube d l with hQdef
  set sf : Vec d → Vec d := streamForcing sinv omega n m e' with hsf
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨by simp [normalizedCubeMeasure_apply_univ Q]⟩
  have hmem8 : MemLp sf (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_continuous Q _
      (continuous_streamForcing sinv omega n m e')
  have hnorm8 : MemLp (fun x => Book.Ch02.vecNorm (sf x)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := memLp_vecNorm_eight_of_memLp_eight Q hmem8
  have hnorm2 : MemLp (fun x => Book.Ch02.vecNorm (sf x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := hnorm8.mono_exponent (by norm_num)
  have hvolR : (0 : ℝ) < (MeasureTheory.volume (openCubeSet R)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos R
  have hvolQ : (MeasureTheory.volume (openCubeSet Q)).toReal = cubeVolume Q :=
    volume_openCubeSet_toReal Q
  have hvolQpos : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
  have hintQ : IntegrableOn (fun x => vecNormSq (sf x)) (openCubeSet Q) volume :=
    integrableOn_openCubeSet_vecNormSq_of_memLp_eight Q hmem8
  have hmono : ∫ x in openCubeSet R, vecNormSq (sf x) ∂volume ≤
      ∫ x in openCubeSet Q, vecNormSq (sf x) ∂volume :=
    setIntegral_mono_set hintQ (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
      hsub.eventuallyLE
  have hQint : ∫ x in openCubeSet Q, vecNormSq (sf x) ∂volume =
      cubeVolume Q * cubeAverage Q (fun x => vecNormSq (sf x)) := by
    rw [← volumeAverage_openCubeSet_eq_cubeAverage_fold]
    unfold volumeAverage
    rw [hvolQ]
    field_simp
  have hCA : cubeAverage Q (fun x => vecNormSq (sf x)) =
      cubeEuclideanLpNorm Q 2 sf ^ (2 : ℕ) := by
    have hb := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 2
      (fun x => Book.Ch02.vecNorm (sf x)) (by norm_num) (by norm_num) hnorm2
    have hto : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
    rw [hto, Real.rpow_natCast] at hb
    have hfun : (fun x => ‖Book.Ch02.vecNorm (sf x)‖ ^ ((2 : ℕ) : ℝ)) =
        fun x => vecNormSq (sf x) := by
      funext x
      rw [Real.rpow_natCast, Real.norm_eq_abs,
        abs_of_nonneg (Book.Ch02.vecNorm_nonneg (sf x)),
        Book.Ch02.vecNorm_sq_eq_vecNormSq]
    rw [hfun] at hb
    exact hb.symm
  have hexp : cubeEuclideanLpNorm Q 2 sf ≤ cubeEuclideanLpNorm Q 8 sf :=
    ENNReal.toReal_mono hnorm8.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
  have hforce : cubeEuclideanLpNorm Q 8 sf ≤
      sinv * Provider.Stream.streamIncrementLpNorm 8 l n m omega :=
    cubeEuclideanLpNorm_streamForcing_le hsinv l n m omega he'
  have hsq : cubeEuclideanLpNorm Q 2 sf ^ (2 : ℕ) ≤
      (sinv * Provider.Stream.streamIncrementLpNorm 8 l n m omega) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (cubeEuclideanLpNorm_nonneg Q 2 sf) (le_trans hexp hforce) 2
  have hstep : volumeAverage (openCubeSet R) (fun x => vecNormSq (sf x)) ≤
      (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
        (cubeVolume Q * cubeAverage Q (fun x => vecNormSq (sf x))) := by
    unfold volumeAverage
    rw [← hQint]
    exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hvolR.le)
  rw [hCA] at hstep
  refine hstep.trans ?_
  have hfac : (0 : ℝ) ≤
      (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ * cubeVolume Q := by positivity
  calc (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
        (cubeVolume Q * cubeEuclideanLpNorm Q 2 sf ^ (2 : ℕ))
      = ((MeasureTheory.volume (openCubeSet R)).toReal⁻¹ * cubeVolume Q) *
          cubeEuclideanLpNorm Q 2 sf ^ (2 : ℕ) := by ring
    _ ≤ ((MeasureTheory.volume (openCubeSet R)).toReal⁻¹ * cubeVolume Q) *
          (sinv * Provider.Stream.streamIncrementLpNorm 8 l n m omega) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hsq hfac

/-! ## The potential leg's second moment -/

/-- **The second sample moment of the Step-2 background's potential cell
energy**, from the fourth-power cell energy of the Dirichlet corrector.

exactly on the geometric membership of the cell and on `hcell`, the proved
producer read at the closure's own Dirichlet family. -/
theorem integrable_meshCellBackgroundPotentialEnergy_sq_of_meshEnergyCell [NeZero d]
    (hd : 2 ≤ d) (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e e' : Vec d)
    {jd : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) jd)
    (hcell : Integrable (fun omega : ShellSeq d =>
        meshEnergyCell R.scale
          (closureDirichletAlong M n h K e omega).toH1Function.grad R ^ (4 : ℝ))
      M.P.toMeasure) :
    Integrable (fun omega : CutoffSample d =>
        meshCellBackgroundPotentialEnergy M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
          R omega ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure := by
  classical
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  set sinv : ℝ := ((Annealed.sigmaBar M n : ℝ))⁻¹ with hsinv
  set wD : ShellSeq d → H10Function (openCubeSet Q) := closureDirichletAlong M n h K e
    with hwDdef
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hsinv0 : (0 : ℝ) < sinv := inv_pos.2 hsig
  have hsol := isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hwin : Book.Ch03.openCubeAtScale (triadicCubeShift R) R.scale = openCubeSet R :=
    openCubeAtScale_triadicCubeShift_eq_openCubeSet R
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hvol : (MeasureTheory.volume (openCubeSet R)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact ne_of_gt (cubeVolume_pos R)
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (wD omega).toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    fun omega => memLp_eight_grad_closureDirichletAlong hd M n h K e omega
  have hgradmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q) (wD omega).toH1Function.grad :=
    fun omega => (wD omega).toH1Function.grad_memVectorL2
  have haffmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q) (fun x => e' + (wD omega).toH1Function.grad x) :=
    fun omega => (memLp_const e').add (hgradmem omega)
  have hclassmeas : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hgradmem omega) :=
    measurable_toHilbertVectorL2OfVecField_freshShellDirichletGrad Q sinv n (n + (h : ℤ))
      e wD hsol hgradmem
  have haffclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (haffmem omega) :=
    measurable_toHilbertVectorL2OfVecField_const_add e' hgradmem haffmem hclassmeas
  have hEmeas : Measurable fun omega : ShellSeq d =>
      volumeAverage (openCubeSet R)
        (fun x => vecNormSq (e' + (wD omega).toH1Function.grad x)) :=
    measurable_volumeAverage_vecNormSq_of_measurable_class (measurableSet_openCubeSet R)
      hsub haffmem haffclass
  set A : ShellSeq d → ℝ := fun omega =>
    volumeAverage (openCubeSet R)
      (fun x => vecNormSq ((wD omega).toH1Function.grad x)) with hAdef
  have hA0 : ∀ omega, 0 ≤ A omega := fun omega =>
    volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
      fun x _ => vecNormSq_nonneg _
  have hcoordW : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => ((wD omega).toH1Function.grad x k) ^ 2)
        (Book.Ch03.openCubeAtScale (triadicCubeShift R) R.scale) volume := by
    intro omega k
    rw [hwin]
    exact (integrableOn_openCubeSet_coord_sq_of_memLp_eight Q (hL8 omega) k).mono_set hsub
  have hAsq : ∀ omega : ShellSeq d,
      meshEnergyCell R.scale (wD omega).toH1Function.grad R ^ (4 : ℝ) = A omega ^ 2 := by
    intro omega
    rw [meshEnergyCell_rpow_four_eq_sq_volumeAverage R.scale _ R (hcoordW omega), hwin]
  have hAsqInt : Integrable (fun omega : CutoffSample d => A omega.val ^ 2)
      (cutoffSampleLaw M).toMeasure :=
    integrable_comp_val_cutoffSampleLaw M
      (hcell.congr (Filter.Eventually.of_forall hAsq))
  have hcellBound : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet R)
          (fun x => vecNormSq (e' + (wD omega).toH1Function.grad x)) ≤
        2 * vecNormSq e' + 2 * A omega := by
    intro omega
    have hintL : IntegrableOn
        (fun x => vecNormSq (e' + (wD omega).toH1Function.grad x)) (openCubeSet R) volume :=
      (integrableOn_openCubeSet_vecNormSq_of_memLp_eight Q
        ((memLp_const e').add (hL8 omega))).mono_set hsub
    have hintg : IntegrableOn
        (fun x => vecNormSq ((wD omega).toH1Function.grad x)) (openCubeSet R) volume :=
      (integrableOn_openCubeSet_vecNormSq_of_memLp_eight Q (hL8 omega)).mono_set hsub
    have hintR : IntegrableOn
        (fun x => 2 * vecNormSq e' + 2 * vecNormSq ((wD omega).toH1Function.grad x))
        (openCubeSet R) volume := (integrable_const _).add (hintg.const_mul 2)
    have hmono := volumeAverage_le_volumeAverage_of_le_on
      (U := openCubeSet R) (measurableSet_openCubeSet R) hintL hintR
      (fun x _ => by
        have hb := vecNormSq_add_le e' ((wD omega).toH1Function.grad x)
        linarith)
    have hval : volumeAverage (openCubeSet R)
        (fun x => 2 * vecNormSq e' + 2 * vecNormSq ((wD omega).toH1Function.grad x)) =
        2 * vecNormSq e' + 2 * A omega := by
      rw [volumeAverage_const_add hvol _ (hintg.const_mul 2),
        volumeAverage_const_mul' (openCubeSet R) 2]
    linarith [hmono, hval]
  have hobs : (fun omega : CutoffSample d =>
        meshCellBackgroundPotentialEnergy M n h (K : ℤ) e e' wD
          (closureNeumannAlong M n h K e') R omega ^ (2 : ℕ)) =
      fun omega : CutoffSample d =>
        (sinv * volumeAverage (openCubeSet R)
          (fun x => vecNormSq (e' + (wD omega.val).toH1Function.grad x))) ^ (2 : ℕ) := by
    funext omega
    rw [meshCellBackgroundPotentialEnergy_eq, average_cubeDomain_eq_volumeAverage]
  rw [hobs]
  set B : ShellSeq d → ℝ := fun omega =>
    volumeAverage (openCubeSet R)
      (fun x => vecNormSq (e' + (wD omega).toH1Function.grad x)) with hBdef
  have hB0 : ∀ omega, 0 ≤ B omega := fun omega =>
    volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
      fun x _ => vecNormSq_nonneg _
  have hdom : Integrable (fun omega : CutoffSample d =>
      sinv ^ 2 * (8 * vecNormSq e' ^ 2 + 8 * A omega.val ^ 2))
      (cutoffSampleLaw M).toMeasure :=
    (((integrable_const _).add (hAsqInt.const_mul 8)).const_mul _)
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun omega => ?_)
  · exact ((measurable_const.mul (hEmeas.comp measurable_subtype_coe)).pow_const
      2).aestronglyMeasurable
  · have h1 := hcellBound omega.val
    have h2 := hB0 omega.val
    have h3 := hA0 omega.val
    have hnn : (0 : ℝ) ≤ (sinv * B omega.val) ^ (2 : ℕ) := by positivity
    rw [Real.norm_of_nonneg hnn]
    have hc : (0 : ℝ) ≤ vecNormSq e' := vecNormSq_nonneg _
    have hB2 : B omega.val ^ 2 ≤ 8 * vecNormSq e' ^ 2 + 8 * A omega.val ^ 2 := by
      nlinarith [h1, h2, h3, hc, sq_nonneg (vecNormSq e' - A omega.val)]
    calc (sinv * B omega.val) ^ (2 : ℕ) = sinv ^ 2 * B omega.val ^ 2 := by ring
      _ ≤ sinv ^ 2 * (8 * vecNormSq e' ^ 2 + 8 * A omega.val ^ 2) :=
          mul_le_mul_of_nonneg_left hB2 (sq_nonneg sinv)

/-! ## The flux leg's first moment -/

/-- **The first sample moment of the Step-2 background's flux cell energy**, from
the fourth-power cell energy of the Neumann corrector and the second moment of
the fresh-shell `L^8` norm.

exactly on the geometric membership of the cell, the direction bound `|e'| <=
1`, and the two named legs. -/
theorem integrable_meshCellBackgroundFluxEnergy_of_legs [NeZero d]
    (hd : 2 ≤ d) (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (e e' : Vec d)
    (he' : Book.Ch02.vecNorm e' ≤ 1)
    {jd : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) jd)
    (hcellN : Integrable (fun omega : ShellSeq d =>
        meshEnergyCell R.scale
          (closureNeumannAlong M n h K e' omega).toH1Function.grad R ^ (4 : ℝ))
      M.P.toMeasure)
    (hstream : Integrable (fun omega : CutoffSample d =>
        Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n (n + (h : ℤ)) omega.val ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure) :
    Integrable (fun omega : CutoffSample d =>
        meshCellBackgroundFluxEnergy M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e')
          R omega)
      (cutoffSampleLaw M).toMeasure := by
  classical
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  set sig : PositiveScalar := Annealed.sigmaBar M n with hsigdef
  set sinv : ℝ := ((sig : ℝ))⁻¹ with hsinv
  set wN : ShellSeq d → H1MeanZeroFunction (openCubeSet Q) :=
    closureNeumannAlong M n h K e' with hwNdef
  have hsig0 : (0 : ℝ) < (sig : ℝ) := sig.2
  have hsinv0 : (0 : ℝ) < sinv := inv_pos.2 hsig0
  have hsolN := isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e'
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hwin : Book.Ch03.openCubeAtScale (triadicCubeShift R) R.scale = openCubeSet R :=
    openCubeAtScale_triadicCubeShift_eq_openCubeSet R
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hvol : (MeasureTheory.volume (openCubeSet R)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact ne_of_gt (cubeVolume_pos R)
  have hL8 : ∀ omega : ShellSeq d,
      MemLp (wN omega).toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    fun omega => memLp_eight_grad_closureNeumannAlong hd M n h K e' omega
  have hL8f : ∀ omega : ShellSeq d,
      MemLp (streamForcing sinv omega n (n + (h : ℤ)) e') (8 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := fun omega =>
    memLp_normalizedCubeMeasure_of_continuous Q _
      (continuous_streamForcing sinv omega n (n + (h : ℤ)) e')
  have hL8nf : ∀ omega : ShellSeq d,
      MemLp (neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega)) (8 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := fun omega => (hL8 omega).add (hL8f omega)
  have hgradmemN : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q) (wN omega).toH1Function.grad :=
    fun omega => (wN omega).toH1Function.grad_memVectorL2
  have hnfmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q)
        (neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega)) := fun omega =>
    (hgradmemN omega).add
      (memVectorL2_openCubeSet_of_continuous Q
        (continuous_streamForcing sinv omega n (n + (h : ℤ)) e'))
  have hnfclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hnfmem omega) :=
    measurable_toHilbertVectorL2OfVecField_neumannFluxField Q sig sinv n (n + (h : ℤ))
      e' e' wN hsolN hnfmem
  have haffmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet Q)
        (fun x => e + neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega) x) :=
    fun omega => (memLp_const e).add (hnfmem omega)
  have haffclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (haffmem omega) :=
    measurable_toHilbertVectorL2OfVecField_const_add e hnfmem haffmem hnfclass
  have hCmeas : Measurable fun omega : ShellSeq d =>
      volumeAverage (openCubeSet R) (fun x =>
        vecNormSq (e + neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega) x)) :=
    measurable_volumeAverage_vecNormSq_of_measurable_class (measurableSet_openCubeSet R)
      hsub haffmem haffclass
  -- the Neumann gradient's cell energy
  set AN : ShellSeq d → ℝ := fun omega =>
    volumeAverage (openCubeSet R)
      (fun x => vecNormSq ((wN omega).toH1Function.grad x)) with hANdef
  have hAN0 : ∀ omega, 0 ≤ AN omega := fun omega =>
    volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
      fun x _ => vecNormSq_nonneg _
  have hANmeas : Measurable AN :=
    measurable_volumeAverage_vecNormSq_freshShellNeumannGrad Q sinv n (n + (h : ℤ)) e'
      (measurableSet_openCubeSet R) hsub wN hsolN
  have hcoordW : ∀ (omega : ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => ((wN omega).toH1Function.grad x k) ^ 2)
        (Book.Ch03.openCubeAtScale (triadicCubeShift R) R.scale) volume := by
    intro omega k
    rw [hwin]
    exact (integrableOn_openCubeSet_coord_sq_of_memLp_eight Q (hL8 omega) k).mono_set hsub
  have hANsq : ∀ omega : ShellSeq d,
      meshEnergyCell R.scale (wN omega).toH1Function.grad R ^ (4 : ℝ) = AN omega ^ 2 := by
    intro omega
    rw [meshEnergyCell_rpow_four_eq_sq_volumeAverage R.scale _ R (hcoordW omega), hwin]
  have hANsqInt : Integrable (fun omega : CutoffSample d => AN omega.val ^ 2)
      (cutoffSampleLaw M).toMeasure :=
    integrable_comp_val_cutoffSampleLaw M
      (hcellN.congr (Filter.Eventually.of_forall hANsq))
  have hANint : Integrable (fun omega : CutoffSample d => AN omega.val)
      (cutoffSampleLaw M).toMeasure :=
    integrable_of_sq_integrable (fun omega => hAN0 omega.val)
      (hANmeas.comp measurable_subtype_coe).aestronglyMeasurable hANsqInt
  -- the forcing's cell energy
  set ratio : ℝ :=
    (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ * cubeVolume Q with hratio
  have hratio0 : (0 : ℝ) ≤ ratio := by
    rw [hratio]
    have := cubeVolume_pos Q
    positivity
  set L : ShellSeq d → ℝ := fun omega =>
    Provider.Stream.streamIncrementLpNorm 8 (K : ℤ) n (n + (h : ℤ)) omega with hLdef
  have hSFle : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet R)
          (fun x => vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x)) ≤
        ratio * (sinv * L omega) ^ (2 : ℕ) := fun omega =>
    volumeAverage_vecNormSq_streamForcing_le hsub hsinv0.le omega n (n + (h : ℤ)) he'
  -- the per-sample cell bound
  have hcellBound : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet R) (fun x =>
          vecNormSq (e + neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega) x)) ≤
        2 * vecNormSq e + (4 * AN omega + 4 * (ratio * (sinv * L omega) ^ (2 : ℕ))) := by
    intro omega
    have hintL : IntegrableOn (fun x =>
        vecNormSq (e + neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega) x))
        (openCubeSet R) volume :=
      (integrableOn_openCubeSet_vecNormSq_of_memLp_eight Q
        ((memLp_const e).add (hL8nf omega))).mono_set hsub
    have hintg : IntegrableOn
        (fun x => vecNormSq ((wN omega).toH1Function.grad x)) (openCubeSet R) volume :=
      (integrableOn_openCubeSet_vecNormSq_of_memLp_eight Q (hL8 omega)).mono_set hsub
    have hintf : IntegrableOn
        (fun x => vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x))
        (openCubeSet R) volume :=
      (integrableOn_openCubeSet_vecNormSq_of_memLp_eight Q (hL8f omega)).mono_set hsub
    have hintsum : IntegrableOn
        (fun x => 4 * vecNormSq ((wN omega).toH1Function.grad x) +
          4 * vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x))
        (openCubeSet R) volume := (hintg.const_mul 4).add (hintf.const_mul 4)
    have hintR : IntegrableOn
        (fun x => 2 * vecNormSq e +
          (4 * vecNormSq ((wN omega).toH1Function.grad x) +
            4 * vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x)))
        (openCubeSet R) volume := (integrable_const _).add hintsum
    have hmono := volumeAverage_le_volumeAverage_of_le_on
      (U := openCubeSet R) (measurableSet_openCubeSet R) hintL hintR
      (fun x _ => by
        have hb1 := vecNormSq_add_le e
          (neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega) x)
        have hb2 : vecNormSq (neumannFluxField sig omega n (n + (h : ℤ)) e'
              (wN omega) x) ≤
            2 * (vecNormSq ((wN omega).toH1Function.grad x) +
              vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x)) :=
          vecNormSq_add_le ((wN omega).toH1Function.grad x)
            (streamForcing sinv omega n (n + (h : ℤ)) e' x)
        linarith)
    have hval : volumeAverage (openCubeSet R)
        (fun x => 2 * vecNormSq e +
          (4 * vecNormSq ((wN omega).toH1Function.grad x) +
            4 * vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x))) =
        2 * vecNormSq e +
          (4 * AN omega +
            4 * volumeAverage (openCubeSet R)
              (fun x => vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x))) := by
      have hstep1 : volumeAverage (openCubeSet R)
          (fun x => 2 * vecNormSq e +
            (4 * vecNormSq ((wN omega).toH1Function.grad x) +
              4 * vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x))) =
          2 * vecNormSq e +
            volumeAverage (openCubeSet R)
              (fun x => 4 * vecNormSq ((wN omega).toH1Function.grad x) +
                4 * vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x)) :=
        volumeAverage_const_add hvol _ hintsum
      have hstep2 : volumeAverage (openCubeSet R)
          (fun x => 4 * vecNormSq ((wN omega).toH1Function.grad x) +
            4 * vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x)) =
          volumeAverage (openCubeSet R)
              (fun x => 4 * vecNormSq ((wN omega).toH1Function.grad x)) +
            volumeAverage (openCubeSet R)
              (fun x => 4 * vecNormSq (streamForcing sinv omega n (n + (h : ℤ)) e' x)) :=
        volumeAverage_add (hintg.const_mul 4) (hintf.const_mul 4)
      rw [hstep1, hstep2, volumeAverage_const_mul' (openCubeSet R) 4,
        volumeAverage_const_mul' (openCubeSet R) 4]
    have hSF := hSFle omega
    linarith [hmono, hval]
  -- the observable in closed form
  have hobs : (fun omega : CutoffSample d =>
        meshCellBackgroundFluxEnergy M n h (K : ℤ) e e'
          (closureDirichletAlong M n h K e) wN R omega) =
      fun omega : CutoffSample d =>
        (sig : ℝ) * volumeAverage (openCubeSet R) (fun x =>
          vecNormSq (e + neumannFluxField sig omega.val n (n + (h : ℤ)) e'
            (wN omega.val) x)) := by
    funext omega
    rw [meshCellBackgroundFluxEnergy_eq, average_cubeDomain_eq_volumeAverage]
  rw [hobs]
  set C : ShellSeq d → ℝ := fun omega =>
    volumeAverage (openCubeSet R) (fun x =>
      vecNormSq (e + neumannFluxField sig omega n (n + (h : ℤ)) e' (wN omega) x))
    with hCdef
  have hC0 : ∀ omega, 0 ≤ C omega := fun omega =>
    volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
      fun x _ => vecNormSq_nonneg _
  have hLsqInt : Integrable (fun omega : CutoffSample d => L omega.val ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure := hstream
  have hdom : Integrable (fun omega : CutoffSample d =>
      (sig : ℝ) * (2 * vecNormSq e +
        (4 * AN omega.val + 4 * (ratio * (sinv * L omega.val) ^ (2 : ℕ)))))
      (cutoffSampleLaw M).toMeasure := by
    have hL2 : Integrable (fun omega : CutoffSample d =>
        ratio * (sinv * L omega.val) ^ (2 : ℕ)) (cutoffSampleLaw M).toMeasure := by
      have hrw : (fun omega : CutoffSample d => ratio * (sinv * L omega.val) ^ (2 : ℕ)) =
          fun omega : CutoffSample d => (ratio * sinv ^ 2) * (L omega.val ^ (2 : ℕ)) := by
        funext omega; ring
      rw [hrw]
      exact hLsqInt.const_mul _
    exact (((integrable_const _).add ((hANint.const_mul 4).add (hL2.const_mul 4)))).const_mul _
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun omega => ?_)
  · exact (measurable_const.mul (hCmeas.comp measurable_subtype_coe)).aestronglyMeasurable
  · have hb := hcellBound omega.val
    have hnn : (0 : ℝ) ≤ (sig : ℝ) * C omega.val :=
      mul_nonneg hsig0.le (hC0 omega.val)
    rw [Real.norm_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left hb hsig0.le

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
