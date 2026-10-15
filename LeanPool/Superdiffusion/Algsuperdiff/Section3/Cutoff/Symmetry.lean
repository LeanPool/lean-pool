/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.J2LInfSeal
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Law
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Symmetry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Symmetries of the genuine lower-infinite cutoff

This module begins the descent of the manuscript's sequence-level (J3)
symmetries to the genuine lower-tail carrier.  In particular, negation
preserves the actual convergence carrier and turns the skew cutoff into its
negative.  No law-level symmetry is postulated here: the remaining measure
transport must be derived from the exact whole-sequence J3 equality.
-/

namespace Algsuperdiff.Section3.Cutoff

open MeasureTheory ProbabilityTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-- The literal shell scaling conjugates translation by `z` to translation by
`3^{-k} z` before scaling. -/
theorem triadicScale_translate (gamma : ℝ) (k : ℤ) (z : Vec d)
    (j : ShellField d) :
    ShellField.translate z (ShellField.triadicScale gamma k j) =
      ShellField.triadicScale gamma k
        (ShellField.translate (((3 : ℝ) ^ k)⁻¹ • z) j) := by
  apply ShellField.ext
  intro x
  simp [ShellField.translate_apply, ShellField.triadicScale_apply, smul_add]

/-- J1 stationarity of shell zero, transported through the exact marginal
scaling law, gives real-translation stationarity of every shell marginal. -/
theorem shellMarginalLaw_stationary (M : ABKModel d) (k : ℤ) (z : Vec d) :
    Measure.map (ShellField.translate z) (ShellField.shellMarginalLaw M.P k).toMeasure =
      (ShellField.shellMarginalLaw M.P k).toMeasure := by
  have hscale := congrArg ProbabilityMeasure.toMeasure (M.shellPrefix.marginal_scaling k)
  change (ShellField.shellMarginalLaw M.P k).toMeasure =
    Measure.map (ShellField.triadicScale M.gamma k)
      (ShellField.zeroShellLaw M.P).toMeasure at hscale
  let w : Vec d := ((3 : ℝ) ^ k)⁻¹ • z
  calc
    Measure.map (ShellField.translate z) (ShellField.shellMarginalLaw M.P k).toMeasure =
        Measure.map (ShellField.translate z)
          (Measure.map (ShellField.triadicScale M.gamma k)
            (ShellField.zeroShellLaw M.P).toMeasure) := by rw [hscale]
    _ = Measure.map (ShellField.translate z ∘ ShellField.triadicScale M.gamma k)
          (ShellField.zeroShellLaw M.P).toMeasure :=
      Measure.map_map (ShellField.measurable_translate z)
        (ShellField.measurable_triadicScale M.gamma k)
    _ = Measure.map (ShellField.triadicScale M.gamma k ∘ ShellField.translate w)
          (ShellField.zeroShellLaw M.P).toMeasure := by
      apply congrArg (fun f : ShellField d → ShellField d =>
        Measure.map f (ShellField.zeroShellLaw M.P).toMeasure)
      funext j
      exact triadicScale_translate M.gamma k z j
    _ = Measure.map (ShellField.triadicScale M.gamma k)
          (Measure.map (ShellField.translate w) (ShellField.zeroShellLaw M.P).toMeasure) :=
      (Measure.map_map (ShellField.measurable_triadicScale M.gamma k)
        (ShellField.measurable_translate w)).symm
    _ = Measure.map (ShellField.triadicScale M.gamma k)
          (ShellField.zeroShellLaw M.P).toMeasure := by rw [M.J1.stationary w]
    _ = (ShellField.shellMarginalLaw M.P k).toMeasure := by rw [hscale]

/-- The canonical law of the whole shell sequence is invariant under every
real translation.  This is derived from the independent coordinates, their
exact marginal scaling, and J1; it is not a new model field. -/
theorem sequenceLaw_stationary (M : ABKModel d) (z : Vec d) :
    Measure.map (ShellField.translateSequence z) M.P.toMeasure = M.P.toMeasure := by
  have hprod := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℤ => ShellField.measurable_shellCoordinate k)).mp M.shellPrefix.independent
  have htransInd : iIndepFun
      (fun k : ℤ => fun F : ShellSeq d => ShellField.translate z (F k)) M.P.toMeasure :=
    M.shellPrefix.independent.comp (fun _ => ShellField.translate z)
      (fun _ => ShellField.measurable_translate z)
  have htransProd := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun _ : ℤ => (ShellField.measurable_translate z).comp
      (ShellField.measurable_shellCoordinate _))).mp htransInd
  calc
    Measure.map (ShellField.translateSequence z) M.P.toMeasure =
        Measure.map (fun F (k : ℤ) => ShellField.translate z (F k)) M.P.toMeasure := rfl
    _ = Measure.infinitePi (fun k : ℤ =>
        Measure.map (fun F : ShellSeq d => ShellField.translate z (F k)) M.P.toMeasure) :=
      by simpa only [Function.comp_apply] using! htransProd
    _ = Measure.infinitePi (fun k : ℤ =>
        Measure.map (fun F : ShellSeq d => F k) M.P.toMeasure) := by
      apply congrArg Measure.infinitePi
      funext k
      calc
        Measure.map (fun F : ShellSeq d => ShellField.translate z (F k)) M.P.toMeasure =
            Measure.map (ShellField.translate z)
              (Measure.map (fun F : ShellSeq d => F k) M.P.toMeasure) := by
          change Measure.map (ShellField.translate z ∘ fun F : ShellSeq d => F k)
            M.P.toMeasure = _
          rw [Measure.map_map (ShellField.measurable_translate z)
            (ShellField.measurable_shellCoordinate k)]
        _ = Measure.map (fun F : ShellSeq d => F k) M.P.toMeasure :=
          shellMarginalLaw_stationary M k z
    _ = Measure.map (fun F (k : ℤ) => F k) M.P.toMeasure := hprod.symm
    _ = M.P.toMeasure := Measure.map_id'

private theorem spatialScale_negate (r : ℝ) (j : ShellField d) :
    ShellField.spatialScale r (ShellField.negate j) =
      ShellField.negate (ShellField.spatialScale r j) := by
  apply ShellField.ext
  intro x
  simp [ShellField.spatialScale_apply, ShellField.negate_apply]

private theorem unitCubeValueNorm_negate (j : ShellField d) :
    ShellField.unitCubeValueNorm (ShellField.negate j) =
      ShellField.unitCubeValueNorm j := by
  rw [ShellField.unitCubeValueNorm_eq_eLpNorm_top,
    ShellField.unitCubeValueNorm_eq_eLpNorm_top]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  filter_upwards with x
  rw [ShellField.negate_apply]
  change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (-j x)‖ =
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (j x)‖
  rw [map_neg, norm_neg]

/-- The exact deterministic local cutoff control is unchanged by shell
negation. -/
theorem localCubeControl_negate (ell : ℤ) (j : ShellField d) :
    localCubeControl ell (ShellField.negate j) = localCubeControl ell j := by
  unfold localCubeControl
  rw [spatialScale_negate, unitCubeValueNorm_negate]

private theorem exists_translate_localCubeControl_bound (ell : ℤ) (z : Vec d) :
    ∃ ell' : ℤ, ∀ j : ShellField d,
      localCubeControl ell (ShellField.translate z j) ≤ localCubeControl ell' j := by
  let K : Set (Vec d) := closure (openCubeSet (originCube d ell))
  have hKcompact : IsCompact K := by
    simpa [K] using (isBounded_openCubeSet (originCube d ell)).isCompact_closure
  let f : Vec d → Vec d := fun x => x + z
  have hf : Continuous f := continuous_id.add continuous_const
  obtain ⟨ell', hell'⟩ := exists_openOriginCube_of_isCompact (hKcompact.image hf)
  refine ⟨ell', ?_⟩
  intro j
  apply localCubeControl_le_of_pointwise ell (ShellField.translate z j)
    (localCubeControl ell' j)
  · intro x hx
    change HCPolySupport.Book.Ch02.matrixOperatorNorm (j (x + z)) ≤
      localCubeControl ell' j
    apply matrixOperatorNorm_le_localCubeControl ell' j
    apply hell'
    exact ⟨x, by simpa [K] using (subset_closure hx), rfl⟩
  · exact localCubeControl_nonneg ell' j

/-- The lower-tail carrier is stable under every real spatial translation.
The new enclosing origin scale is deterministic in the requested scale and
translation; it does not depend on the shell or on a realization. -/
theorem lowerTailGood_translate {omega : ShellSeq d} (z : Vec d)
    (hgood : LowerTailGood omega) :
    LowerTailGood (ShellField.translateSequence z omega) := by
  intro ell m
  obtain ⟨ell', hlocal⟩ := exists_translate_localCubeControl_bound ell z
  obtain ⟨C, hC⟩ := hgood ell' m
  refine ⟨C, ?_⟩
  intro q
  unfold lowerTailPartialSum
  calc
    ∑ r ∈ Finset.range q,
        localCubeControl ell (ShellField.translateSequence z omega (m - r)) ≤
        ∑ r ∈ Finset.range q, localCubeControl ell' (omega (m - r)) := by
      gcongr with r hr
      simpa only [ShellField.translateSequence_apply] using hlocal (omega (m - r))
    _ = lowerTailPartialSum ell' m q omega := rfl
    _ ≤ C := hC q

/-- Real translation restricted to the genuine lower-tail carrier. -/
def translateCutoffSample (z : Vec d) (omega : CutoffSample d) : CutoffSample d :=
  ⟨ShellField.translateSequence z omega.1, lowerTailGood_translate z omega.2⟩

@[simp]
theorem translateCutoffSample_val (z : Vec d) (omega : CutoffSample d) :
    (translateCutoffSample z omega).1 = ShellField.translateSequence z omega.1 :=
  rfl

/-- Translation on the lower-tail carrier is measurable. -/
theorem measurable_translateCutoffSample (z : Vec d) :
    Measurable (translateCutoffSample (d := d) z) := by
  apply Measurable.subtype_mk
  exact (ShellField.measurable_translateSequence z).comp measurable_subtype_coe

private theorem translateSequence_add (z w : Vec d) (omega : ShellSeq d) :
    ShellField.translateSequence z (ShellField.translateSequence w omega) =
      ShellField.translateSequence (z + w) omega := by
  funext k
  apply ShellField.ext
  intro x
  simp [ShellField.translateSequence_apply, ShellField.translate_apply, add_assoc]

private theorem translateSequence_zero (omega : ShellSeq d) :
    ShellField.translateSequence (0 : Vec d) omega = omega := by
  funext k
  apply ShellField.ext
  intro x
  simp [ShellField.translateSequence_apply]

private theorem translateCutoffSample_add (z w : Vec d) (omega : CutoffSample d) :
    translateCutoffSample z (translateCutoffSample w omega) =
      translateCutoffSample (z + w) omega := by
  apply Subtype.ext
  exact translateSequence_add z w omega.1

private theorem translateCutoffSample_zero (omega : CutoffSample d) :
    translateCutoffSample 0 omega = omega := by
  apply Subtype.ext
  exact translateSequence_zero omega.1

private theorem translateCutoffSample_right_inverse (z : Vec d) :
    Function.RightInverse (translateCutoffSample (d := d) (-z))
      (translateCutoffSample z) := by
  intro omega
  rw [translateCutoffSample_add]
  simpa only [add_neg_cancel] using translateCutoffSample_zero omega

private theorem translateCutoffSample_preimage_image (z : Vec d)
    (t : Set (CutoffSample d)) :
    (Subtype.val : CutoffSample d → ShellSeq d) ''
        (translateCutoffSample z ⁻¹' t) =
      ShellField.translateSequence z ⁻¹'
        ((Subtype.val : CutoffSample d → ShellSeq d) '' t) := by
  ext omega
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨translateCutoffSample z x, hx, rfl⟩
  · rintro ⟨x, hx, hxval⟩
    refine ⟨translateCutoffSample (-z) x, ?_, ?_⟩
    · change translateCutoffSample z (translateCutoffSample (-z) x) ∈ t
      rw [translateCutoffSample_right_inverse z x]
      exact hx
    · calc
        (translateCutoffSample (-z) x).1 = ShellField.translateSequence (-z) x.1 := rfl
        _ = ShellField.translateSequence (-z)
            (ShellField.translateSequence z omega) := by rw [← hxval]
        _ = ShellField.translateSequence ((-z) + z) omega :=
          translateSequence_add (-z) z omega
        _ = omega := by simp only [neg_add_cancel, translateSequence_zero]

/-- J1 stationarity descends from the whole canonical sequence law to the
actual lower-tail carrier law, for every real translation. -/
theorem map_translateCutoffSample_cutoffSampleLaw (M : ABKModel d) (z : Vec d) :
    Measure.map (translateCutoffSample (d := d) z) (cutoffSampleLaw M).toMeasure =
      (cutoffSampleLaw M).toMeasure := by
  ext t ht
  rw [Measure.map_apply (measurable_translateCutoffSample z) ht]
  rw [show (cutoffSampleLaw M).toMeasure =
      Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure by rfl]
  have hcomap (u : Set (CutoffSample d)) :
      (Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure) u =
        M.P.toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) '' u) := by
    simpa only [CutoffSample, lowerTailGoodSet] using!
      (comap_subtype_coe_apply (s := lowerTailGoodSet d)
        (measurableSet_lowerTailGoodSet d) M.P.toMeasure u)
  rw [hcomap]
  have ht_image : MeasurableSet ((Subtype.val : CutoffSample d → ShellSeq d) '' t) :=
    ((MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)).measurableSet_image).2 ht
  calc
    M.P.toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) ''
        (translateCutoffSample z ⁻¹' t)) =
        M.P.toMeasure (ShellField.translateSequence z ⁻¹'
          ((Subtype.val : CutoffSample d → ShellSeq d) '' t)) := by
      rw [translateCutoffSample_preimage_image]
    _ = Measure.map (ShellField.translateSequence z) M.P.toMeasure
        ((Subtype.val : CutoffSample d → ShellSeq d) '' t) := by
      rw [Measure.map_apply (ShellField.measurable_translateSequence z) ht_image]
    _ = M.P.toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) '' t) := by
      rw [sequenceLaw_stationary M z]
    _ = (cutoffSampleLaw M).toMeasure t := by
      rw [show (cutoffSampleLaw M).toMeasure =
        Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure by rfl]
      exact (hcomap t).symm

/-- The lower-tail convergence condition is closed under simultaneous
whole-sequence negation. -/
theorem lowerTailGood_negate {omega : ShellSeq d} (hgood : LowerTailGood omega) :
    LowerTailGood (ShellField.negateSequence omega) := by
  intro ell m
  obtain ⟨C, hC⟩ := hgood ell m
  refine ⟨C, ?_⟩
  intro q
  simpa only [lowerTailPartialSum, ShellField.negateSequence_apply,
    localCubeControl_negate] using hC q

/-- Whole-sequence negation restricted to the genuine public cutoff carrier. -/
def negateCutoffSample (omega : CutoffSample d) : CutoffSample d :=
  ⟨ShellField.negateSequence omega.1, lowerTailGood_negate omega.2⟩

@[simp]
theorem negateCutoffSample_val (omega : CutoffSample d) :
    (negateCutoffSample omega).1 = ShellField.negateSequence omega.1 :=
  rfl

private theorem negateSequence_involutive (omega : ShellSeq d) :
    ShellField.negateSequence (ShellField.negateSequence omega) = omega := by
  funext k
  apply ShellField.ext
  intro x
  simp [ShellField.negateSequence_apply, ShellField.negate_apply]

/-- Whole-sequence negation is a genuine involution on the lower-tail carrier. -/
theorem negateCutoffSample_involutive (omega : CutoffSample d) :
    negateCutoffSample (negateCutoffSample omega) = omega := by
  apply Subtype.ext
  exact negateSequence_involutive omega.1

/-- The negation action on the lower-tail carrier is measurable. -/
theorem measurable_negateCutoffSample :
    Measurable (negateCutoffSample (d := d)) := by
  apply Measurable.subtype_mk
  exact ShellField.measurable_negateSequence.comp measurable_subtype_coe

private theorem negateCutoffSample_preimage_image (t : Set (CutoffSample d)) :
    (Subtype.val : CutoffSample d → ShellSeq d) ''
        (negateCutoffSample (d := d) ⁻¹' t) =
      ShellField.negateSequence ⁻¹'
        ((Subtype.val : CutoffSample d → ShellSeq d) '' t) := by
  ext omega
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨negateCutoffSample x, hx, rfl⟩
  · rintro ⟨x, hx, hxval⟩
    refine ⟨negateCutoffSample x, ?_, ?_⟩
    · change negateCutoffSample (negateCutoffSample x) ∈ t
      simpa only [negateCutoffSample_involutive] using hx
    · calc
        (negateCutoffSample x).1 = ShellField.negateSequence x.1 := rfl
        _ = ShellField.negateSequence (ShellField.negateSequence omega) := by
          rw [← hxval]
        _ = omega := negateSequence_involutive omega

/-- J3 negation invariance descends from the whole shell-sequence law to the
actual lower-tail carrier law. -/
theorem map_negateCutoffSample_cutoffSampleLaw (M : ABKModel d) :
    Measure.map (negateCutoffSample (d := d)) (cutoffSampleLaw M).toMeasure =
      (cutoffSampleLaw M).toMeasure := by
  ext t ht
  rw [Measure.map_apply measurable_negateCutoffSample ht]
  rw [show (cutoffSampleLaw M).toMeasure =
      Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure by rfl]
  have hcomap (u : Set (CutoffSample d)) :
      (Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure) u =
        M.P.toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) '' u) := by
    simpa only [CutoffSample, lowerTailGoodSet] using!
      (comap_subtype_coe_apply (s := lowerTailGoodSet d)
        (measurableSet_lowerTailGoodSet d) M.P.toMeasure u)
  rw [hcomap]
  have ht_image : MeasurableSet ((Subtype.val : CutoffSample d → ShellSeq d) '' t) :=
    ((MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)).measurableSet_image).2 ht
  have hJ3 := congrArg ProbabilityMeasure.toMeasure M.J3.negation
  change Measure.map ShellField.negateSequence M.P.toMeasure = M.P.toMeasure at hJ3
  calc
    M.P.toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) ''
        (negateCutoffSample (d := d) ⁻¹' t)) =
        M.P.toMeasure (ShellField.negateSequence ⁻¹'
          ((Subtype.val : CutoffSample d → ShellSeq d) '' t)) := by
      rw [negateCutoffSample_preimage_image]
    _ = Measure.map ShellField.negateSequence M.P.toMeasure
        ((Subtype.val : CutoffSample d → ShellSeq d) '' t) := by
      rw [Measure.map_apply ShellField.measurable_negateSequence ht_image]
    _ = M.P.toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) '' t) := by rw [hJ3]
    _ = (cutoffSampleLaw M).toMeasure t := by
      rw [show (cutoffSampleLaw M).toMeasure =
        Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure by rfl]
      exact (hcomap t).symm

/-- Translating the input sequence translates the genuine lower-infinite
cutoff, as an exact identity of regular coefficient fields. -/
theorem cutoff_translateCutoffSample (m : ℤ) (z : Vec d) (omega : CutoffSample d) :
    cutoff m (translateCutoffSample z omega) = translateReg z (cutoff m omega) := by
  apply RegCoeffField.ext
  intro x
  ext i j
  calc
    cutoff m (translateCutoffSample z omega) x i j =
        ∑' r : ℕ, (translateCutoffSample z omega).1 (m - (r : ℤ)) x i j :=
      cutoff_apply_entry m (translateCutoffSample z omega) x i j
    _ = ∑' r : ℕ, omega.1 (m - (r : ℤ)) (x + z) i j := by
      apply tsum_congr
      intro r
      rw [translateCutoffSample_val, ShellField.translateSequence_apply,
        ShellField.translate_apply]
    _ = cutoff m omega (x + z) i j := by
      rw [cutoff_apply_entry]
    _ = translateReg z (cutoff m omega) x i j := rfl

/-- The actual coefficient cutoff commutes exactly with every real
translation. -/
theorem coefficientCutoff_translateCutoffSample (nu : ℝ) (m : ℤ) (z : Vec d)
    (omega : CutoffSample d) :
    coefficientCutoff nu m (translateCutoffSample z omega) =
      translateReg z (coefficientCutoff nu m omega) := by
  apply RegCoeffField.ext
  intro x
  have hcutoff := congrArg (fun a : RegCoeffField d => a x)
    (cutoff_translateCutoffSample m z omega)
  change nu • (1 : Mat d) + cutoff m (translateCutoffSample z omega) x =
    nu • (1 : Mat d) + cutoff m omega (x + z)
  simpa only using! congrArg (fun A : Mat d => nu • (1 : Mat d) + A) hcutoff

/-- The coefficient-cutoff law is invariant under every real translation.
CoarseGraining's stationary-law interface is its integer-translation
specialization. -/
theorem coefficientCutoffLaw_stationary_real (M : ABKModel d) (m : ℤ) (z : Vec d) :
    Measure.map (translateReg z) (coefficientCutoffLaw M m) = coefficientCutoffLaw M m := by
  rw [coefficientCutoffLaw_eq_map]
  calc
    Measure.map (translateReg z)
        (Measure.map (coefficientCutoff M.nu m) (cutoffSampleLaw M).toMeasure) =
        Measure.map (translateReg z ∘ coefficientCutoff M.nu m)
          (cutoffSampleLaw M).toMeasure :=
      Measure.map_map (measurable_translateReg z) (measurable_coefficientCutoff M.nu m)
    _ = Measure.map (coefficientCutoff M.nu m ∘ translateCutoffSample z)
          (cutoffSampleLaw M).toMeasure := by
      apply congrArg (fun f : CutoffSample d → RegCoeffField d =>
        Measure.map f (cutoffSampleLaw M).toMeasure)
      funext omega
      exact (coefficientCutoff_translateCutoffSample M.nu m z omega).symm
    _ = Measure.map (coefficientCutoff M.nu m)
          (Measure.map (translateCutoffSample z) (cutoffSampleLaw M).toMeasure) := by
      rw [Measure.map_map (measurable_coefficientCutoff M.nu m)
        (measurable_translateCutoffSample z)]
    _ = Measure.map (coefficientCutoff M.nu m) (cutoffSampleLaw M).toMeasure := by
      rw [map_translateCutoffSample_cutoffSampleLaw]

/-- The exact CoarseGraining carrier-level stationarity predicate for the
coefficient cutoff law. -/
theorem coefficientCutoffLaw_stationary (M : ABKModel d) (m : ℤ) :
    IsStationaryR (coefficientCutoffLaw M m) := by
  intro z
  exact coefficientCutoffLaw_stationary_real M m (intVecToRealVec z)

private theorem matrixOperatorNorm_signedPermutation_le_dim_sq
    (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    HCPolySupport.Book.Ch02.matrixOperatorNorm R ≤ (d : ℝ) ^ 2 := by
  obtain ⟨σ, s, hs, hRdef⟩ := hR
  calc
    HCPolySupport.Book.Ch02.matrixOperatorNorm R ≤
        HCPolySupport.Book.Ch02.matrixFrobeniusNorm R :=
      HCPolySupport.Book.Ch02.matrixOperatorNorm_le_matrixFrobeniusNorm R
    _ ≤ ∑ i, ∑ j, |R i j| :=
      HCPolySupport.Book.Ch02.matrixFrobeniusNorm_le_sum_abs_entries R
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [hRdef]
      split_ifs with h
      · rcases hs j with hsj | hsj <;> simp [hsj]
      · norm_num
    _ = (d : ℝ) ^ 2 := by
      simp [pow_two]

private theorem matVecMul_mem_openCubeSet_originCube
    (R : Mat d) (hR : IsSignedPermutationMatrix R) (ell : ℤ)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) :
    matVecMul R x ∈ openCubeSet (originCube d ell) := by
  obtain ⟨σ, s, hs, hRdef⟩ := hR
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hval : matVecMul R x i = s (σ.symm i) * x (σ.symm i) := by
    unfold matVecMul
    rw [Finset.sum_eq_single (σ.symm i)]
    · rw [hRdef]
      have hi : i = σ (σ.symm i) := by simp
      rw [ite_eq_left hi]
    · intro j _ hj
      rw [hRdef]
      have hij : i ≠ σ j := by
        intro h
        apply hj
        have : σ.symm i = σ.symm (σ j) := congrArg σ.symm h
        have hsymm : σ.symm i = j := by
          simpa only [Equiv.symm_apply_apply] using this
        exact hsymm.symm
      simp [hij]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have hcoord := hx (σ.symm i)
  rw [hval]
  rcases hs (σ.symm i) with hsign | hsign
  · simpa [hsign] using hcoord
  · rw [hsign]
    constructor <;> nlinarith [hcoord.1, hcoord.2]

private theorem localCubeControl_rotate_le (ell : ℤ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (j : ShellField d) :
    localCubeControl ell (ShellField.rotate R hR j) ≤
      (d : ℝ) ^ 4 * localCubeControl ell j := by
  apply localCubeControl_le_of_pointwise ell (ShellField.rotate R hR j)
    ((d : ℝ) ^ 4 * localCubeControl ell j)
  · intro x hx
    rw [ShellField.rotate_apply]
    have hRbound := matrixOperatorNorm_signedPermutation_le_dim_sq R hR
    have hRtbound := matrixOperatorNorm_signedPermutation_le_dim_sq (matTranspose R) hR.transpose
    have hjbound := matrixOperatorNorm_le_localCubeControl ell j
      (matVecMul_mem_openCubeSet_originCube R hR ell hx)
    calc
      HCPolySupport.Book.Ch02.matrixOperatorNorm
          (matTranspose R * j (matVecMul R x) * R) =
          HCPolySupport.Book.Ch02.matrixOperatorNorm
            (matTranspose R * (j (matVecMul R x) * R)) := by
        rw [Matrix.mul_assoc]
      _ ≤
          HCPolySupport.Book.Ch02.matrixOperatorNorm (matTranspose R) *
            HCPolySupport.Book.Ch02.matrixOperatorNorm (j (matVecMul R x) * R) :=
        HCPolySupport.Book.Ch02.matrixOperatorNorm_mul_le _ _
      _ ≤ (d : ℝ) ^ 2 *
            HCPolySupport.Book.Ch02.matrixOperatorNorm (j (matVecMul R x) * R) := by
        exact mul_le_mul_of_nonneg_right hRtbound
          (HCPolySupport.Book.Ch02.matrixOperatorNorm_nonneg _)
      _ ≤ (d : ℝ) ^ 2 *
            (HCPolySupport.Book.Ch02.matrixOperatorNorm (j (matVecMul R x)) *
              HCPolySupport.Book.Ch02.matrixOperatorNorm R) := by
        exact mul_le_mul_of_nonneg_left
          (HCPolySupport.Book.Ch02.matrixOperatorNorm_mul_le _ _) (by positivity)
      _ ≤ (d : ℝ) ^ 2 *
            (HCPolySupport.Book.Ch02.matrixOperatorNorm (j (matVecMul R x)) * (d : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hRbound
            (HCPolySupport.Book.Ch02.matrixOperatorNorm_nonneg _)) (by positivity)
      _ ≤ (d : ℝ) ^ 2 * (localCubeControl ell j * (d : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hjbound (by positivity)) (by positivity)
      _ = (d : ℝ) ^ 4 * localCubeControl ell j := by ring
  · exact mul_nonneg (by positivity) (localCubeControl_nonneg ell j)

/-- The lower-tail carrier is stable under every signed-permutation
conjugation.  The deterministic polynomial comparison is only used to retain
summability; no probabilistic symmetry is assumed here. -/
theorem lowerTailGood_rotate {omega : ShellSeq d} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (hgood : LowerTailGood omega) :
    LowerTailGood (ShellField.rotateSequence R hR omega) := by
  intro ell m
  obtain ⟨C, hC⟩ := hgood ell m
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (d : ℝ) ^ 4 * (C : ℝ) ≤ N :=
    exists_nat_ge _
  refine ⟨N, ?_⟩
  intro q
  unfold lowerTailPartialSum at hC ⊢
  calc
    ∑ r ∈ Finset.range q,
        localCubeControl ell (ShellField.rotateSequence R hR omega (m - r)) ≤
        ∑ r ∈ Finset.range q, ((d : ℝ) ^ 4 *
          localCubeControl ell (omega (m - r))) := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [ShellField.rotateSequence_apply] using
        localCubeControl_rotate_le ell R hR (omega (m - r))
    _ = (d : ℝ) ^ 4 *
        ∑ r ∈ Finset.range q, localCubeControl ell (omega (m - r)) := by
      rw [Finset.mul_sum]
    _ ≤ (d : ℝ) ^ 4 * (C : ℝ) := by
      exact mul_le_mul_of_nonneg_left (hC q) (by positivity)
    _ ≤ N := hN

/-- Signed-permutation conjugation restricted to the genuine lower-tail
carrier. -/
def rotateCutoffSample (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (omega : CutoffSample d) : CutoffSample d :=
  ⟨ShellField.rotateSequence R hR omega.1, lowerTailGood_rotate R hR omega.2⟩

@[simp]
theorem rotateCutoffSample_val (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (omega : CutoffSample d) :
    (rotateCutoffSample R hR omega).1 = ShellField.rotateSequence R hR omega.1 :=
  rfl

/-- Signed-permutation conjugation on the lower-tail carrier is measurable. -/
theorem measurable_rotateCutoffSample (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measurable (rotateCutoffSample (d := d) R hR) := by
  apply Measurable.subtype_mk
  exact (ShellField.measurable_rotateSequence R hR).comp measurable_subtype_coe

private theorem matVecMul_one_local (x : Vec d) :
    matVecMul (1 : Mat d) x = x := by
  ext i
  unfold matVecMul
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hij : i ≠ j := fun h => hji h.symm
    simp [hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem rotate_transpose_rotate (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (j : ShellField d) :
    ShellField.rotate (matTranspose R) hR.transpose (ShellField.rotate R hR j) = j := by
  apply ShellField.ext
  intro x
  rw [ShellField.rotate_apply, ShellField.rotate_apply]
  have hx : matVecMul R (matVecMul (matTranspose R) x) = x := by
    rw [matVecMul_mul, hR.mul_transpose_self, matVecMul_one_local]
  rw [hx]
  simp only [matTranspose, Matrix.transpose_transpose]
  have hRRt : R * Matrix.transpose R = 1 := by
    simpa only [matTranspose] using hR.mul_transpose_self
  calc
    R * (Matrix.transpose R * j x * R) * Matrix.transpose R =
        (R * Matrix.transpose R) * j x * (R * Matrix.transpose R) := by
      simp only [Matrix.mul_assoc]
    _ = j x := by rw [hRRt, Matrix.one_mul, Matrix.mul_one]

private theorem rotate_rotate_transpose (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (j : ShellField d) :
    ShellField.rotate R hR (ShellField.rotate (matTranspose R) hR.transpose j) = j := by
  simpa only [matTranspose, Matrix.transpose_transpose] using
    rotate_transpose_rotate (matTranspose R) hR.transpose j

private theorem rotateSequence_transpose_rotate (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : ShellSeq d) :
    ShellField.rotateSequence (matTranspose R) hR.transpose
        (ShellField.rotateSequence R hR omega) = omega := by
  funext k
  exact rotate_transpose_rotate R hR (omega k)

private theorem rotateSequence_rotate_transpose (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : ShellSeq d) :
    ShellField.rotateSequence R hR
        (ShellField.rotateSequence (matTranspose R) hR.transpose omega) = omega := by
  funext k
  exact rotate_rotate_transpose R hR (omega k)

/-- Conjugation by `R.transpose` is the right inverse of conjugation by `R` on
the genuine cutoff carrier. -/
theorem rotateCutoffSample_rotate_transpose (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : CutoffSample d) :
    rotateCutoffSample R hR
        (rotateCutoffSample (matTranspose R) hR.transpose omega) = omega := by
  apply Subtype.ext
  exact rotateSequence_rotate_transpose R hR omega.1

private theorem subtype_val_image_preimage_eq_preimage_image
    {α : Type*} {p : α → Prop}
    (f fInv : Subtype p → Subtype p) (g gInv : α → α)
    (hval : ∀ x, (f x).1 = g x.1)
    (hInvVal : ∀ x, (fInv x).1 = gInv x.1)
    (hfInv : Function.RightInverse fInv f)
    (hgInv : Function.LeftInverse gInv g)
    (t : Set (Subtype p)) :
    (Subtype.val : Subtype p → α) '' (f ⁻¹' t) =
      g ⁻¹' ((Subtype.val : Subtype p → α) '' t) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨f y, hy, hval y⟩
  · rintro ⟨y, hy, hyval⟩
    refine ⟨fInv y, ?_, ?_⟩
    · change f (fInv y) ∈ t
      rw [hfInv y]
      exact hy
    · rw [hInvVal y, hyval, hgInv x]

private theorem rotateCutoffSample_preimage_image (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (t : Set (CutoffSample d)) :
    (Subtype.val : CutoffSample d → ShellSeq d) ''
        (rotateCutoffSample R hR ⁻¹' t) =
      ShellField.rotateSequence R hR ⁻¹'
        ((Subtype.val : CutoffSample d → ShellSeq d) '' t) := by
  exact subtype_val_image_preimage_eq_preimage_image
    (rotateCutoffSample R hR)
    (rotateCutoffSample (matTranspose R) hR.transpose)
    (ShellField.rotateSequence R hR)
    (ShellField.rotateSequence (matTranspose R) hR.transpose)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
    (rotateCutoffSample_rotate_transpose R hR)
    (rotateSequence_transpose_rotate R hR) t

/-- The exact whole-sequence J3 hyperoctahedral equality descends to the
genuine lower-tail carrier law. -/
theorem map_rotateCutoffSample_cutoffSampleLaw (M : ABKModel d)
    (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measure.map (rotateCutoffSample (d := d) R hR) (cutoffSampleLaw M).toMeasure =
      (cutoffSampleLaw M).toMeasure := by
  ext t ht
  rw [Measure.map_apply (measurable_rotateCutoffSample R hR) ht]
  rw [show (cutoffSampleLaw M).toMeasure =
      Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure by rfl]
  have hcomap (u : Set (CutoffSample d)) :
      (Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure) u =
        M.P.toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) '' u) := by
    simpa only [CutoffSample, lowerTailGoodSet] using!
      (comap_subtype_coe_apply (s := lowerTailGoodSet d)
        (measurableSet_lowerTailGoodSet d) M.P.toMeasure u)
  rw [hcomap]
  have ht_image : MeasurableSet ((Subtype.val : CutoffSample d → ShellSeq d) '' t) :=
    ((MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)).measurableSet_image).2 ht
  have hJ3 := congrArg ProbabilityMeasure.toMeasure (M.J3.hyperoctahedral R hR)
  change Measure.map (ShellField.rotateSequence R hR) M.P.toMeasure = M.P.toMeasure at hJ3
  calc
    M.P.toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) ''
        (rotateCutoffSample R hR ⁻¹' t)) =
        M.P.toMeasure (ShellField.rotateSequence R hR ⁻¹'
          ((Subtype.val : CutoffSample d → ShellSeq d) '' t)) := by
      rw [rotateCutoffSample_preimage_image]
    _ = Measure.map (ShellField.rotateSequence R hR) M.P.toMeasure
        ((Subtype.val : CutoffSample d → ShellSeq d) '' t) := by
      rw [Measure.map_apply (ShellField.measurable_rotateSequence R hR) ht_image]
    _ = M.P.toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) '' t) := by rw [hJ3]
    _ = (cutoffSampleLaw M).toMeasure t := by
      rw [show (cutoffSampleLaw M).toMeasure =
        Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure by rfl]
      exact (hcomap t).symm

/-- Signed-permutation conjugation commutes exactly with the genuine lower-infinite
cutoff, in CoarseGraining's `R.transpose * a(Rx) * R` convention. -/
theorem cutoff_rotateCutoffSample (m : ℤ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : CutoffSample d) :
    cutoff m (rotateCutoffSample R hR omega) = rotateReg R hR (cutoff m omega) := by
  obtain ⟨σ, s, _hs, hRdef⟩ := id hR
  apply RegCoeffField.ext
  intro x
  ext i j
  calc
    cutoff m (rotateCutoffSample R hR omega) x i j =
        ∑' r : ℕ, (rotateCutoffSample R hR omega).1 (m - (r : ℤ)) x i j :=
      cutoff_apply_entry m (rotateCutoffSample R hR omega) x i j
    _ = ∑' r : ℕ, s i * s j *
        omega.1 (m - (r : ℤ)) (matVecMul R x) (σ i) (σ j) := by
      apply tsum_congr
      intro r
      rw [rotateCutoffSample_val, ShellField.rotateSequence_apply,
        ShellField.rotate_apply, matTranspose_mul_mul_apply hRdef]
    _ = s i * s j *
        ∑' r : ℕ, omega.1 (m - (r : ℤ)) (matVecMul R x) (σ i) (σ j) := by
      rw [tsum_mul_left]
    _ = s i * s j * cutoff m omega (matVecMul R x) (σ i) (σ j) := by
      rw [cutoff_apply_entry]
    _ = rotateReg R hR (cutoff m omega) x i j := by
      rw [rotateReg_apply, matTranspose_mul_mul_apply hRdef]

/-- Signed-permutation conjugation commutes exactly with the actual
coefficient cutoff `a_m = nu I + k_m`. -/
theorem coefficientCutoff_rotateCutoffSample (nu : ℝ) (m : ℤ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : CutoffSample d) :
    coefficientCutoff nu m (rotateCutoffSample R hR omega) =
      rotateReg R hR (coefficientCutoff nu m omega) := by
  apply RegCoeffField.ext
  intro x
  have hcutoff := congrArg (fun a : RegCoeffField d => a x)
    (cutoff_rotateCutoffSample m R hR omega)
  have hidentity :
      matTranspose R * (nu • (1 : Mat d)) * R = nu • (1 : Mat d) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hR.transpose_mul_self]
  have hcutoff' :
      cutoff m (rotateCutoffSample R hR omega) x =
        matTranspose R * cutoff m omega (matVecMul R x) * R := by
    simpa only [rotateReg_apply] using hcutoff
  change nu • (1 : Mat d) + cutoff m (rotateCutoffSample R hR omega) x =
    matTranspose R * (nu • (1 : Mat d) + cutoff m omega (matVecMul R x)) * R
  rw [hcutoff', Matrix.mul_add, Matrix.add_mul, hidentity]

/-- The law of the actual coefficient cutoff has the exact CoarseGraining
signed-permutation isotropy required by `IsIsotropicInLawR`. -/
theorem coefficientCutoffLaw_isotropic (M : ABKModel d) (m : ℤ) :
    IsIsotropicInLawR (coefficientCutoffLaw M m) := by
  intro R hR
  rw [coefficientCutoffLaw_eq_map]
  calc
    Measure.map (rotateReg R hR)
        (Measure.map (coefficientCutoff M.nu m) (cutoffSampleLaw M).toMeasure) =
        Measure.map (rotateReg R hR ∘ coefficientCutoff M.nu m)
          (cutoffSampleLaw M).toMeasure :=
      Measure.map_map (measurable_rotateReg R hR) (measurable_coefficientCutoff M.nu m)
    _ = Measure.map (coefficientCutoff M.nu m ∘ rotateCutoffSample R hR)
          (cutoffSampleLaw M).toMeasure := by
      apply congrArg (fun f : CutoffSample d → RegCoeffField d =>
        Measure.map f (cutoffSampleLaw M).toMeasure)
      funext omega
      exact (coefficientCutoff_rotateCutoffSample M.nu m R hR omega).symm
    _ = Measure.map (coefficientCutoff M.nu m)
          (Measure.map (rotateCutoffSample R hR) (cutoffSampleLaw M).toMeasure) := by
      rw [Measure.map_map (measurable_coefficientCutoff M.nu m)
        (measurable_rotateCutoffSample R hR)]
    _ = Measure.map (coefficientCutoff M.nu m) (cutoffSampleLaw M).toMeasure := by
      rw [map_rotateCutoffSample_cutoffSampleLaw]

/-- Negating the input sequence negates the genuine lower-infinite cutoff.
This is an identity of regular coefficient fields, not an almost-everywhere
representative statement. -/
theorem cutoff_negateCutoffSample (m : ℤ) (omega : CutoffSample d) :
    cutoff m (negateCutoffSample omega) =
      Algsuperdiff.Probability.negReg (cutoff m omega) := by
  apply RegCoeffField.ext
  intro x
  ext i j
  calc
    cutoff m (negateCutoffSample omega) x i j =
        ∑' r : ℕ, (negateCutoffSample omega).1 (m - (r : ℤ)) x i j :=
      cutoff_apply_entry m (negateCutoffSample omega) x i j
    _ = ∑' r : ℕ, ShellField.negateSequence omega.1 (m - (r : ℤ)) x i j := by rfl
    _ =
        ∑' r : ℕ, -omega.1 (m - (r : ℤ)) x i j := by
      apply tsum_congr
      intro r
      rw [ShellField.negateSequence_apply, ShellField.negate_apply,
        Matrix.neg_apply]
    _ = -(∑' r : ℕ, omega.1 (m - (r : ℤ)) x i j) := by
      rw [tsum_neg]
    _ = -cutoff m omega x i j := by
      rw [cutoff_apply_entry]
    _ = Algsuperdiff.Probability.negReg (cutoff m omega) x i j := by
      rw [Algsuperdiff.Probability.negReg_apply, Matrix.neg_apply]

/-- Under whole-sequence negation, the actual coefficient cutoff becomes the
adjoint coefficient cutoff.  This uses the proved skewness of the genuine
lower-infinite cutoff; it does not assume an adjoint law. -/
theorem coefficientCutoff_negateCutoffSample_eq_adjoint (nu : ℝ) (m : ℤ)
    (omega : CutoffSample d) :
    coefficientCutoff nu m (negateCutoffSample omega) =
      adjointReg (coefficientCutoff nu m omega) := by
  apply RegCoeffField.ext
  intro x
  have hcutoff := congrArg (fun a : RegCoeffField d => a x)
    (cutoff_negateCutoffSample m omega)
  have hskew := cutoff_skew m omega x
  change nu • (1 : Mat d) + cutoff m (negateCutoffSample omega) x =
    (nu • (1 : Mat d) + cutoff m omega x).transpose
  have hcutoff' : cutoff m (negateCutoffSample omega) x =
      Algsuperdiff.Probability.negReg (cutoff m omega) x := by
    simpa only using hcutoff
  rw [hcutoff', Algsuperdiff.Probability.negReg_apply,
    Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hskew]

/-- The law of the actual coefficient cutoff is invariant under adjunction.
This is the J3 negation symmetry transported through the genuine lower-tail
carrier and the exact identity `a_m(-omega) = a_m(omega)^*`. -/
theorem coefficientCutoffLaw_adjoint_invariant (M : ABKModel d) (m : ℤ) :
    Measure.map adjointReg (coefficientCutoffLaw M m) = coefficientCutoffLaw M m := by
  rw [coefficientCutoffLaw_eq_map]
  calc
    Measure.map adjointReg
        (Measure.map (coefficientCutoff M.nu m) (cutoffSampleLaw M).toMeasure) =
        Measure.map (adjointReg ∘ coefficientCutoff M.nu m)
          (cutoffSampleLaw M).toMeasure :=
      Measure.map_map measurable_adjointReg (measurable_coefficientCutoff M.nu m)
    _ = Measure.map (coefficientCutoff M.nu m ∘ negateCutoffSample)
          (cutoffSampleLaw M).toMeasure := by
      apply congrArg (fun f : CutoffSample d → RegCoeffField d =>
        Measure.map f (cutoffSampleLaw M).toMeasure)
      funext omega
      exact (coefficientCutoff_negateCutoffSample_eq_adjoint M.nu m omega).symm
    _ = Measure.map (coefficientCutoff M.nu m)
          (Measure.map negateCutoffSample (cutoffSampleLaw M).toMeasure) := by
      rw [Measure.map_map (measurable_coefficientCutoff M.nu m)
        measurable_negateCutoffSample]
    _ = Measure.map (coefficientCutoff M.nu m) (cutoffSampleLaw M).toMeasure := by
      rw [map_negateCutoffSample_cutoffSampleLaw]

end

end Algsuperdiff.Section3.Cutoff
