/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumLayerCarrier
public import Mathlib.Probability.Independence.InfinitePi

/-!
# ShellSumLayerFlip

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The cross terms of the layer decomposition vanish

`ShellSumLayerCarrier.lean` resolves the shell-sum corrector energy into

`‖Σ_{k ∈ (n,m]} P 𝐟_k‖²`

on the layer carrier, `P` the stationary potential projection.

This module carries out that argument.

## The single-layer flip

Negating **one** layer preserves the joint law:

* each shell marginal is negation invariant — take the `k`-th marginal of the
  whole-sequence identity of (J3) (`map_negate_shellMarginalLaw`); this uses no
  independence;
* the joint law is the product of its marginals by (J1) independence, so a
  coordinatewise map preserves it as soon as each marginal is preserved
  (`map_negateLayer`), exactly the engine of `Cutoff.sequenceLaw_stationary`.

The flip is equivariant for the translation action, so its Koopman operator is a
linear isometry that **commutes with `P`**
(`stationaryPotentialProjection_carrierTransport`), and it negates `𝐟_k` while
fixing every `𝐟_l`, `l ≠ k`.  The pairing is therefore odd under it and vanishes.

## What is supplied

* `map_negate_shellMarginalLaw` — (J3) at a single shell marginal.
* `map_negateLayer` — the single-layer flip preserves the sequence law.
* `measurePreserving_flipLayer` — the same on the layer carrier.
* `flipKoopman_layerForcingL2` — the flip negates its own layer and fixes the
  others.
* `inner_stationaryPotentialProjection_layerForcingL2_eq_zero` — **the cross-term
  kill**.
* `integral_normSq_shellSumCorrectorRepr_eq_sum` — **the layer decomposition of
  `e.perturb.assumption`**: the shell-sum corrector energy is the sum over
  `k ∈ (n,m]` of the layer corrector energies.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3 (ABKModel)
open ProbabilityTheory

noncomputable section

variable {d : ℕ}

/-! ### (J3) at a single shell marginal -/

/-- **Each shell marginal is negation invariant.**  This is the `k`-th marginal
of the whole-sequence negation identity of (J3); no independence is used. -/
theorem map_negate_shellMarginalLaw (M : ABKModel d) (k : ℤ) :
    Measure.map (ShellField.negate (d := d))
        (ShellField.shellMarginalLaw M.P k).toMeasure
      = (ShellField.shellMarginalLaw M.P k).toMeasure := by
  have hJ3 : Measure.map (ShellField.negateSequence (d := d)) M.P.toMeasure
      = M.P.toMeasure := congrArg ProbabilityMeasure.toMeasure M.J3.negation
  have hmarg : (ShellField.shellMarginalLaw M.P k).toMeasure
      = Measure.map (fun F : ShellSeq d => F k) M.P.toMeasure := rfl
  rw [hmarg]
  calc
    Measure.map (ShellField.negate (d := d))
          (Measure.map (fun F : ShellSeq d => F k) M.P.toMeasure)
        = Measure.map (ShellField.negate (d := d) ∘ fun F : ShellSeq d => F k)
            M.P.toMeasure :=
      Measure.map_map ShellField.measurable_negate
        (ShellField.measurable_shellCoordinate k)
    _ = Measure.map ((fun F : ShellSeq d => F k) ∘
          ShellField.negateSequence (d := d)) M.P.toMeasure := rfl
    _ = Measure.map (fun F : ShellSeq d => F k)
          (Measure.map (ShellField.negateSequence (d := d)) M.P.toMeasure) :=
      (Measure.map_map (ShellField.measurable_shellCoordinate k)
        ShellField.measurable_negateSequence).symm
    _ = Measure.map (fun F : ShellSeq d => F k) M.P.toMeasure := by rw [hJ3]

/-! ### The single-layer flip on the sequence carrier -/

/-- Negate the shell field at index `l` exactly when `l = k`. -/
def negateLayerField (k l : ℤ) (j : ShellField d) : ShellField d :=
  if l = k then ShellField.negate j else j

theorem negateLayerField_self (k : ℤ) (j : ShellField d) :
    negateLayerField k k j = ShellField.negate j := by
  rw [negateLayerField, ite_eq_left rfl]

theorem negateLayerField_of_ne {k l : ℤ} (h : l ≠ k) (j : ShellField d) :
    negateLayerField k l j = j := by
  rw [negateLayerField, ite_eq_right h]

theorem measurable_negateLayerField (k l : ℤ) :
    Measurable (negateLayerField (d := d) k l) := by
  by_cases h : l = k
  · subst h
    have hfun : negateLayerField (d := d) l l = ShellField.negate :=
      funext fun j => negateLayerField_self l j
    rw [hfun]
    exact ShellField.measurable_negate
  · have hfun : negateLayerField (d := d) k l = id :=
      funext fun j => negateLayerField_of_ne h j
    rw [hfun]
    exact measurable_id

/-- Negate one layer of the shell sequence. -/
def negateLayer (k : ℤ) (omega : ShellSeq d) : ShellSeq d :=
  fun l => negateLayerField k l (omega l)

theorem measurable_negateLayer (k : ℤ) : Measurable (negateLayer (d := d) k) :=
  Measurable.of_eval fun l =>
    (measurable_negateLayerField k l).comp (measurable_pi_apply l)

/-- **Negating a single layer preserves the joint sequence law.**

(J1) independence turns the joint law into the product of its marginals, and
(J3) makes every marginal negation invariant; a coordinatewise map therefore
preserves the joint law.  The engine is exactly the one used by
`Cutoff.sequenceLaw_stationary` for translations. -/
theorem map_negateLayer (M : ABKModel d) (k : ℤ) :
    Measure.map (negateLayer (d := d) k) M.P.toMeasure = M.P.toMeasure := by
  have hprod := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun l : ℤ => ShellField.measurable_shellCoordinate l)).mp M.shellPrefix.independent
  have hInd : iIndepFun
      (fun l : ℤ => fun F : ShellSeq d => negateLayerField k l (F l)) M.P.toMeasure :=
    M.shellPrefix.independent.comp (fun l => negateLayerField k l)
      (fun l => measurable_negateLayerField k l)
  have hIndProd := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun l : ℤ => (measurable_negateLayerField k l).comp
      (ShellField.measurable_shellCoordinate l))).mp hInd
  calc
    Measure.map (negateLayer (d := d) k) M.P.toMeasure
        = Measure.map (fun F : ShellSeq d => fun l : ℤ => negateLayerField k l (F l))
            M.P.toMeasure := rfl
    _ = Measure.infinitePi (fun l : ℤ =>
          Measure.map (fun F : ShellSeq d => negateLayerField k l (F l))
            M.P.toMeasure) := by
        simpa only [Function.comp_apply] using! hIndProd
    _ = Measure.infinitePi (fun l : ℤ =>
          Measure.map (fun F : ShellSeq d => F l) M.P.toMeasure) := by
        refine congrArg Measure.infinitePi ?_
        funext l
        have hsplit : Measure.map (fun F : ShellSeq d => negateLayerField k l (F l))
              M.P.toMeasure
            = Measure.map (negateLayerField (d := d) k l)
              (Measure.map (fun F : ShellSeq d => F l) M.P.toMeasure) := by
          change Measure.map (negateLayerField (d := d) k l ∘
            fun F : ShellSeq d => F l) M.P.toMeasure = _
          rw [Measure.map_map (measurable_negateLayerField k l)
            (ShellField.measurable_shellCoordinate l)]
        rw [hsplit]
        by_cases h : l = k
        · subst h
          have hfun : negateLayerField (d := d) l l = ShellField.negate :=
            funext fun j => negateLayerField_self l j
          rw [hfun]
          exact map_negate_shellMarginalLaw M l
        · have hfun : negateLayerField (d := d) k l = id :=
            funext fun j => negateLayerField_of_ne h j
          rw [hfun, Measure.map_id]
    _ = Measure.map (fun F : ShellSeq d => fun l : ℤ => F l) M.P.toMeasure := hprod.symm
    _ = M.P.toMeasure := Measure.map_id'

/-! ### The single-layer flip on the layer carrier -/

/-- Negate one layer of the sequence of shell value paths. -/
def flipLayer (k : ℤ) (F : ℤ → C(Vec d, Mat d)) : ℤ → C(Vec d, Mat d) :=
  fun l => if l = k then -(F l) else F l

theorem flipLayer_self (k : ℤ) (F : ℤ → C(Vec d, Mat d)) :
    flipLayer k F k = -(F k) := by
  rw [flipLayer, ite_eq_left rfl]

theorem flipLayer_of_ne {k l : ℤ} (h : l ≠ k) (F : ℤ → C(Vec d, Mat d)) :
    flipLayer k F l = F l := by
  rw [flipLayer, ite_eq_right h]

theorem measurable_flipLayer (k : ℤ) : Measurable (flipLayer (d := d) k) := by
  refine Measurable.of_eval fun l => ?_
  by_cases h : l = k
  · subst h
    have hfun : (fun F : ℤ → C(Vec d, Mat d) => flipLayer l F l)
        = fun F : ℤ → C(Vec d, Mat d) => -(F l) := funext fun F => flipLayer_self l F
    rw [hfun]
    exact (measurable_pi_apply l).neg
  · have hfun : (fun F : ℤ → C(Vec d, Mat d) => flipLayer k F l)
        = fun F : ℤ → C(Vec d, Mat d) => F l := funext fun F => flipLayer_of_ne h F
    rw [hfun]
    exact measurable_pi_apply l

theorem flipLayer_seqValuePath (k : ℤ) (omega : ShellSeq d) :
    flipLayer k (seqValuePath omega) = seqValuePath (negateLayer (d := d) k omega) := by
  funext l
  by_cases h : l = k
  · subst h
    rw [flipLayer_self]
    change -ShellField.valuePath (omega l)
      = ShellField.valuePath (negateLayerField l l (omega l))
    rw [negateLayerField_self, ShellField.valuePath_negate]
  · rw [flipLayer_of_ne h]
    change ShellField.valuePath (omega l)
      = ShellField.valuePath (negateLayerField k l (omega l))
    rw [negateLayerField_of_ne h]

/-- Negation commutes with translation on the path carrier. -/
private theorem neg_vadd_path (z : Vec d) (f : C(Vec d, Mat d)) :
    -(z +ᵥ f) = z +ᵥ (-f) :=
  ContinuousMap.ext fun x => by
    rw [ContinuousMap.neg_apply, ShellField.vadd_apply, ShellField.vadd_apply,
      ContinuousMap.neg_apply]

theorem flipLayer_vadd (k : ℤ) (z : Vec d) (F : ℤ → C(Vec d, Mat d)) :
    flipLayer k (z +ᵥ F) = z +ᵥ flipLayer (d := d) k F := by
  funext l
  by_cases h : l = k
  · subst h
    rw [flipLayer_self]
    change -((z +ᵥ F) l) = z +ᵥ flipLayer l F l
    rw [flipLayer_self]
    exact neg_vadd_path z (F l)
  · rw [flipLayer_of_ne h]
    change (z +ᵥ F) l = z +ᵥ flipLayer k F l
    rw [flipLayer_of_ne h]
    rfl

/-- **The single-layer flip preserves the layer law.** -/
theorem measurePreserving_flipLayer (M : ABKModel d) (k : ℤ) :
    MeasurePreserving (flipLayer (d := d) k) (seqPathLaw M.P).toMeasure
      (seqPathLaw M.P).toMeasure := by
  refine ⟨measurable_flipLayer k, ?_⟩
  rw [seqPathLaw_toMeasure,
    Measure.map_map (measurable_flipLayer k) measurable_seqValuePath]
  calc
    Measure.map (flipLayer (d := d) k ∘ seqValuePath (d := d)) M.P.toMeasure
        = Measure.map (seqValuePath (d := d) ∘ negateLayer (d := d) k) M.P.toMeasure := by
      refine congrArg
        (fun g : ShellSeq d → (ℤ → C(Vec d, Mat d)) => Measure.map g M.P.toMeasure) ?_
      funext omega
      exact flipLayer_seqValuePath k omega
    _ = Measure.map (seqValuePath (d := d))
          (Measure.map (negateLayer (d := d) k) M.P.toMeasure) :=
      (Measure.map_map measurable_seqValuePath (measurable_negateLayer k)).symm
    _ = Measure.map (seqValuePath (d := d)) M.P.toMeasure := by rw [map_negateLayer M k]

/-! ### The Koopman operator of the flip -/

/-- The Koopman isometry of the single-layer flip on the stationary `L²` layer. -/
def flipKoopman (M : ABKModel d) (k : ℤ) :
    VectorL2 d (seqPathLaw M.P).toMeasure →L[ℝ] VectorL2 d (seqPathLaw M.P).toMeasure :=
  carrierTransport (HilbertVec d) (measurePreserving_flipLayer M k)

/-- The flip Koopman operator preserves inner products. -/
theorem inner_flipKoopman (M : ABKModel d) (k : ℤ)
    (u v : VectorL2 d (seqPathLaw M.P).toMeasure) :
    (inner ℝ (flipKoopman M k u) (flipKoopman M k v) : ℝ) = inner ℝ u v :=
  (Lp.compMeasurePreservingₗᵢ ℝ (flipLayer (d := d) k)
    (measurePreserving_flipLayer M k)).inner_map_map u v

/-- The flip Koopman operator commutes with the stationary potential
projection: the flip is an equivariant measure-preserving self-map, so
`StationaryCarrierTransport`'s naturality applies. -/
theorem flipKoopman_stationaryPotentialProjection (M : ABKModel d) (k : ℤ)
    (G : VectorL2 d (seqPathLaw M.P).toMeasure) :
    stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
        (flipKoopman M k G)
      = flipKoopman M k (stationaryPotentialProjection
          (μ := (seqPathLaw M.P).toMeasure) G) :=
  stationaryPotentialProjection_carrierTransport (measurePreserving_flipLayer M k)
    (fun z F => flipLayer_vadd k z F) G

/-- The flip negates the forcing of its own layer and fixes every other layer
forcing. -/
theorem flipKoopman_layerForcingL2 (M : ABKModel d) (e : Vec d) (k l : ℤ) :
    flipKoopman M k (layerForcingL2 M e l)
      = if l = k then -(layerForcingL2 M e l) else layerForcingL2 M e l := by
  have hcomp := Lp.toLp_compMeasurePreserving (p := 2)
    (f := flipLayer (d := d) k) (memLp_two_layerForcing M e l)
    (measurePreserving_flipLayer M k)
  by_cases h : l = k
  · subst h
    rw [ite_eq_left rfl]
    have hfun : layerForcing e l ∘ flipLayer (d := d) l
        = fun F => -(layerForcing (d := d) e l F) := by
      funext F
      change valuePathForcing e (flipLayer l F l)
        = -HilbertVec.ofVec (matVecMul (F l 0) e)
      rw [flipLayer_self]
      change HilbertVec.ofVec (matVecMul ((-(F l)) 0) e) = _
      rw [ContinuousMap.neg_apply]
      refine PiLp.ext fun i => ?_
      simp only [PiLp.neg_apply, matVecMul, Matrix.neg_apply]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hstep : flipKoopman M l (layerForcingL2 M e l)
        = ((memLp_two_layerForcing M e l).comp_measurePreserving
            (measurePreserving_flipLayer M l)).toLp
              (layerForcing e l ∘ flipLayer (d := d) l) := hcomp
    rw [hstep]
    refine (MemLp.toLp_eq_toLp_iff _ ((memLp_two_layerForcing M e l).neg)).2 ?_
    · exact Filter.Eventually.of_forall (congrFun hfun)
  · rw [ite_eq_right h]
    have hfun : layerForcing e l ∘ flipLayer (d := d) k = layerForcing (d := d) e l := by
      funext F
      change valuePathForcing e (flipLayer k F l) = valuePathForcing e (F l)
      rw [flipLayer_of_ne h]
    have hstep : flipKoopman M k (layerForcingL2 M e l)
        = ((memLp_two_layerForcing M e l).comp_measurePreserving
            (measurePreserving_flipLayer M k)).toLp
              (layerForcing e l ∘ flipLayer (d := d) k) := hcomp
    rw [hstep]
    refine (MemLp.toLp_eq_toLp_iff _ (memLp_two_layerForcing M e l)).2 ?_
    exact Filter.Eventually.of_forall (congrFun hfun)

/-! ### The cross-term kill -/

/-- **The cross terms of the layer decomposition vanish.**

For `k ≠ l` the pairing of the layer-`k` and layer-`l` correctors is zero.  The
argument is the single-layer flip: it is measure preserving by (J1) + (J3), it
is equivariant, so its Koopman isometry commutes with the projection, and it
negates exactly one of the two forcings. -/
theorem inner_stationaryPotentialProjection_layerForcingL2_eq_zero
    (M : ABKModel d) (e : Vec d) {k l : ℤ} (hkl : l ≠ k) :
    (inner ℝ (stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
        (layerForcingL2 M e k))
      (stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
        (layerForcingL2 M e l)) : ℝ) = 0 := by
  set A := stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
    (layerForcingL2 M e k) with hA
  set B := stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
    (layerForcingL2 M e l) with hB
  have hflipA : flipKoopman M k A = -A := by
    rw [hA, ← flipKoopman_stationaryPotentialProjection M k,
      flipKoopman_layerForcingL2 M e k k, ite_eq_left rfl, map_neg]
  have hflipB : flipKoopman M k B = B := by
    rw [hB, ← flipKoopman_stationaryPotentialProjection M k,
      flipKoopman_layerForcingL2 M e k l, ite_eq_right hkl]
  have hstep : (inner ℝ A B : ℝ) = inner ℝ (flipKoopman M k A) (flipKoopman M k B) :=
    (inner_flipKoopman M k A B).symm
  rw [hflipA, hflipB, inner_neg_left] at hstep
  linarith

/-! ### The layer decomposition of the corrector energy -/

/-- The `L²` norm square of the shell-sum corrector is the expectation of the
squared Euclidean norm of its strongly measurable representative. -/
theorem integral_normSq_shellSumCorrectorRepr_eq_norm_sq (M : ABKModel d)
    (e : Vec d) (n m : ℤ) :
    ∫ f, ‖shellSumCorrectorRepr M e n m f‖ ^ 2
        ∂(shellSumValuePathLaw M.P n m).toMeasure
      = ‖shellSumPotentialCorrector M e n m‖ ^ 2 := by
  set q := shellSumPotentialCorrector M e n m with hq
  have hae : (fun f : C(Vec d, Mat d) => ‖shellSumCorrectorRepr M e n m f‖ ^ 2)
      =ᵐ[(shellSumValuePathLaw M.P n m).toMeasure]
      fun f => ‖(q : C(Vec d, Mat d) → HilbertVec d) f‖ ^ 2 := by
    filter_upwards [(Lp.aestronglyMeasurable q).ae_eq_mk] with f hf
    exact congrArg (fun v : HilbertVec d => ‖v‖ ^ 2) hf.symm
  rw [integral_congr_ae hae]
  calc ∫ f, ‖(q : C(Vec d, Mat d) → HilbertVec d) f‖ ^ 2
        ∂(shellSumValuePathLaw M.P n m).toMeasure
      = ∫ f, (inner ℝ ((q : C(Vec d, Mat d) → HilbertVec d) f)
          ((q : C(Vec d, Mat d) → HilbertVec d) f) : ℝ)
          ∂(shellSumValuePathLaw M.P n m).toMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun f => ?_)
        exact (real_inner_self_eq_norm_sq _).symm
    _ = (inner ℝ q q : ℝ) := (MeasureTheory.L2.inner_def q q).symm
    _ = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q

/-- The norm square of a finite sum of pairwise orthogonal vectors. -/
private theorem norm_sq_finset_sum_of_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {iota : Type*} (s : Finset iota)
    (g : iota → E) (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (g i) (g j) : ℝ) = 0) :
    ‖∑ i ∈ s, g i‖ ^ 2 = ∑ i ∈ s, ‖g i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, Finset.sum_eq_single_of_mem i hi (fun j hj hji => h i hi j hj (Ne.symm hji)),
    real_inner_self_eq_norm_sq]

/-- **The layer decomposition of `e.perturb.assumption`.**

The corrector energy of the shell-sum forcing is the sum, over the layers of
the block `(n, m]`, of the layer corrector energies.

No normalization of `e` is assumed.  The per-layer factor `3^{2γk}` of
`e.perturb.assumption` is **not** proved here. -/
theorem integral_normSq_shellSumCorrectorRepr_eq_sum (M : ABKModel d) (e : Vec d)
    (n m : ℤ) :
    ∫ f, ‖shellSumCorrectorRepr M e n m f‖ ^ 2
        ∂(shellSumValuePathLaw M.P n m).toMeasure
      = ∑ k ∈ Finset.Ioc n m, ‖stationaryPotentialProjection
          (μ := (seqPathLaw M.P).toMeasure) (layerForcingL2 M e k)‖ ^ 2 := by
  classical
  rw [integral_normSq_shellSumCorrectorRepr_eq_norm_sq M e n m,
    norm_shellSumPotentialCorrector_eq M e n m]
  refine norm_sq_finset_sum_of_orthogonal _ _ fun i _ j _ hij => ?_
  exact inner_stationaryPotentialProjection_layerForcingL2_eq_zero M e (Ne.symm hij)

end

end Algsuperdiff.Section3.Provider.Corrector
