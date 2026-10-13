/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumCorrectorLimit

/-!
# ShellSumLayerCarrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The layer carrier: resolving the shell-sum corrector into its layers

The shell-sum law of `ShellSumCarrierLaw.lean` lives on `C(Vec d, Mat d)`, the
law of the *sum* `k_m − k_n = Σ_{k ∈ (n,m]} 𝐣_k`.  That carrier has forgotten the
individual layers, so the layer decomposition of `e.perturb.assumption` cannot
even be stated there.

This module introduces the **layer carrier** `ℤ → C(Vec d, Mat d)` — the whole
sequence of shell value paths — carrying the diagonal translation action, and
transports the shell-sum corrector energy onto it.  The transport is
`StationaryCarrierTransport.lean`'s naturality of the stationary potential
projection along an equivariant factor map, applied to the summation map

`seqPathSum n m : (ℤ → C(Vec d, Mat d)) → C(Vec d, Mat d)`, `F ↦ Σ_{k ∈ (n,m]} F k`,

which is equivariant and pushes the layer law onto the shell-sum law.  Under the
transport the shell-sum forcing becomes the **sum of the layer forcings**, and
the projection is linear, so the corrector energy becomes the norm-square of a
finite sum of layer correctors.  Splitting that norm-square into diagonal and
cross terms is `e.perturb.assumption`'s layer decomposition; the cross terms are
killed in `ShellSumLayerFlip.lean`.

## What is supplied

* `seqPathLaw` — the law of the whole sequence of shell value paths, with its
  translation-invariance instance (input: `Cutoff.sequenceLaw_stationary`, i.e.
  (J1) + `e.diff.law.shift`, exactly as for the shell-sum law).
* `measurePreserving_seqPathSum`, `measurePreserving_seqPathCoord` — the two
  equivariant factor maps onto the shell-sum law and onto the single-shell law.
* `layerForcing`, `layerForcingL2` — the layer-`k` forcing `𝐣_k(0) e` on the
  layer carrier, and its `L²` class.
* `carrierTransport_shellSumForcingL2` — the transported shell-sum forcing is
  the sum of the layer forcings.
* `norm_shellSumPotentialCorrector_eq` — **the layer decomposition of the
  corrector**: the shell-sum corrector energy equals the norm-square of
  `Σ_{k ∈ (n,m]} P 𝐟_k` on the layer carrier.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}

/-! ### The layer carrier and its law -/

/-- The whole sequence of shell value paths. -/
def seqValuePath (omega : ShellSeq d) : ℤ → C(Vec d, Mat d) :=
  fun k => ShellField.valuePath (omega k)

theorem measurable_seqValuePath : Measurable (seqValuePath (d := d)) :=
  Measurable.of_eval fun k =>
    ShellField.measurable_valuePath.comp (measurable_pi_apply k)

/-- **The layer law.**  The joint law of all shell value paths. -/
def seqPathLaw (P : ProbabilityMeasure (ℤ → ShellField d)) :
    ProbabilityMeasure (ℤ → C(Vec d, Mat d)) :=
  P.map (seqValuePath (d := d))

theorem seqPathLaw_toMeasure (P : ProbabilityMeasure (ℤ → ShellField d)) :
    (seqPathLaw P).toMeasure = Measure.map (seqValuePath (d := d)) P.toMeasure :=
  rfl

/-- The layer carrier is equivariant for the diagonal translation action. -/
theorem seqValuePath_translateSequence (z : Vec d) (omega : ShellSeq d) :
    seqValuePath (ShellField.translateSequence z omega)
      = z +ᵥ seqValuePath (d := d) omega := by
  funext k
  exact ShellField.valuePath_translate z (omega k)

/-- **The layer law is translation invariant.**  The only input is
`Cutoff.sequenceLaw_stationary`; no invariance is assumed on the target law. -/
theorem map_vadd_seqPathLaw (M : ABKModel d) (z : Vec d) :
    Measure.map (fun F : ℤ → C(Vec d, Mat d) => z +ᵥ F) (seqPathLaw M.P).toMeasure
      = (seqPathLaw M.P).toMeasure := by
  rw [seqPathLaw_toMeasure]
  calc
    Measure.map (fun F : ℤ → C(Vec d, Mat d) => z +ᵥ F)
          (Measure.map (seqValuePath (d := d)) M.P.toMeasure)
        = Measure.map ((fun F : ℤ → C(Vec d, Mat d) => z +ᵥ F) ∘
            seqValuePath (d := d)) M.P.toMeasure :=
      Measure.map_map (measurable_const_vadd z) measurable_seqValuePath
    _ = Measure.map (seqValuePath (d := d) ∘ ShellField.translateSequence z)
          M.P.toMeasure := by
        refine congrArg
          (fun g : ShellSeq d → (ℤ → C(Vec d, Mat d)) => Measure.map g M.P.toMeasure) ?_
        funext omega
        exact (seqValuePath_translateSequence z omega).symm
    _ = Measure.map (seqValuePath (d := d))
          (Measure.map (ShellField.translateSequence z) M.P.toMeasure) :=
      (Measure.map_map measurable_seqValuePath
        (ShellField.measurable_translateSequence z)).symm
    _ = Measure.map (seqValuePath (d := d)) M.P.toMeasure := by
        rw [sequenceLaw_stationary M z]

instance vaddInvariantMeasure_seqPathLaw (M : ABKModel d) :
    VAddInvariantMeasure (Vec d) (ℤ → C(Vec d, Mat d)) (seqPathLaw M.P).toMeasure where
  measure_preimage_vadd := by
    intro z s hs
    rw [← Measure.map_apply (measurable_const_vadd z) hs]
    exact congrArg (fun mu : Measure (ℤ → C(Vec d, Mat d)) => mu s)
      (map_vadd_seqPathLaw M z)

/-! ### The summation factor map -/

/-- The block summation map: the layer carrier maps onto the shell-sum carrier
by summing the layers of the block `(n, m]`. -/
def seqPathSum (n m : ℤ) (F : ℤ → C(Vec d, Mat d)) : C(Vec d, Mat d) :=
  ∑ k ∈ Finset.Ioc n m, F k

theorem measurable_seqPathSum (n m : ℤ) : Measurable (seqPathSum (d := d) n m) := by
  have : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  have : Filter.IsCountablyGenerated (uniformity (Mat d)) :=
    inferInstanceAs (Filter.IsCountablyGenerated (uniformity (Fin d → Fin d → ℝ)))
  exact Finset.measurable_sum _ fun k _ => measurable_pi_apply k

theorem seqPathSum_vadd (n m : ℤ) (z : Vec d) (F : ℤ → C(Vec d, Mat d)) :
    seqPathSum n m (z +ᵥ F) = z +ᵥ seqPathSum (d := d) n m F := by
  refine ContinuousMap.ext fun x => ?_
  rw [ShellField.vadd_apply]
  simp only [seqPathSum, ContinuousMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- **The summation map pushes the layer law onto the shell-sum law.** -/
theorem measurePreserving_seqPathSum (M : ABKModel d) (n m : ℤ) :
    MeasurePreserving (seqPathSum (d := d) n m) (seqPathLaw M.P).toMeasure
      (shellSumValuePathLaw M.P n m).toMeasure := by
  refine ⟨measurable_seqPathSum n m, ?_⟩
  rw [seqPathLaw_toMeasure, shellSumValuePathLaw_toMeasure,
    Measure.map_map (measurable_seqPathSum n m) measurable_seqValuePath]
  rfl

/-! ### The coordinate factor maps -/

/-- The block `(k-1, k]` is the single layer `k`. -/
theorem shellSumValuePath_pred_self (k : ℤ) (omega : ShellSeq d) :
    shellSumValuePath (k - 1) k omega = ShellField.valuePath (omega k) := by
  have hIoc : Finset.Ioc (k - 1) k = {k} := by
    ext l
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  rw [shellSumValuePath, hIoc, Finset.sum_singleton]

/-- **Reading a single layer pushes the layer law onto that layer's law**, which
is the shell-sum law of the one-element block `(k-1, k]`. -/
theorem measurePreserving_seqPathCoord (M : ABKModel d) (k : ℤ) :
    MeasurePreserving (fun F : ℤ → C(Vec d, Mat d) => F k) (seqPathLaw M.P).toMeasure
      (shellSumValuePathLaw M.P (k - 1) k).toMeasure := by
  refine ⟨measurable_pi_apply k, ?_⟩
  rw [seqPathLaw_toMeasure, shellSumValuePathLaw_toMeasure,
    Measure.map_map (measurable_pi_apply k) measurable_seqValuePath]
  refine congrArg
    (fun g : ShellSeq d → C(Vec d, Mat d) => Measure.map g M.P.toMeasure) ?_
  funext omega
  exact (shellSumValuePath_pred_self k omega).symm

/-! ### The layer forcings -/

/-- The layer-`k` forcing `𝐣_k(0) e`, read on the layer carrier. -/
def layerForcing (e : Vec d) (k : ℤ) (F : ℤ → C(Vec d, Mat d)) : HilbertVec d :=
  valuePathForcing e (F k)

theorem memLp_two_layerForcing (M : ABKModel d) (e : Vec d) (k : ℤ) :
    MemLp (layerForcing e k) 2 (seqPathLaw M.P).toMeasure :=
  (memLp_two_valuePathForcing_shellSum M e (k - 1) k).comp_measurePreserving
    (measurePreserving_seqPathCoord M k)

/-- The layer-`k` forcing as an element of the stationary `L²` layer of the
layer carrier. -/
def layerForcingL2 (M : ABKModel d) (e : Vec d) (k : ℤ) :
    VectorL2 d (seqPathLaw M.P).toMeasure :=
  (memLp_two_layerForcing M e k).toLp (layerForcing e k)

/-- `matVecMul` is additive in the matrix argument. -/
private theorem matVecMul_finset_sum {iota : Type*} (s : Finset iota)
    (A : iota → Mat d) (e : Vec d) :
    matVecMul (∑ k ∈ s, A k) e = ∑ k ∈ s, matVecMul (A k) e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      funext i
      simp [matVecMul]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      funext i
      simp only [matVecMul, Matrix.add_apply, Pi.add_apply, add_mul]
      exact Finset.sum_add_distrib

/-- The shell-sum forcing, transported to the layer carrier, is the pointwise
sum of the layer forcings. -/
theorem valuePathForcing_comp_seqPathSum (e : Vec d) (n m : ℤ) :
    valuePathForcing e ∘ seqPathSum (d := d) n m
      = fun F => ∑ k ∈ Finset.Ioc n m, layerForcing e k F := by
  funext F
  change HilbertVec.ofVec (matVecMul ((∑ k ∈ Finset.Ioc n m, F k) 0) e)
    = ∑ k ∈ Finset.Ioc n m, HilbertVec.ofVec (matVecMul (F k 0) e)
  rw [ContinuousMap.sum_apply, matVecMul_finset_sum]
  simpa only [HilbertVec.ofVecL_apply] using
    map_sum (HilbertVec.ofVecL d) (fun k => matVecMul (F k 0) e) (Finset.Ioc n m)

/-- `MemLp.toLp` commutes with finite sums. -/
private theorem toLp_finset_sum {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {iota : Type*} (s : Finset iota)
    (g : iota → Omega → HilbertVec d) (hg : ∀ i, MemLp (g i) 2 mu)
    (hs : MemLp (fun omega => ∑ i ∈ s, g i omega) 2 mu) :
    hs.toLp (fun omega => ∑ i ∈ s, g i omega)
      = ∑ i ∈ s, (hg i).toLp (g i) := by
  classical
  have hrest : ∀ t : Finset iota, MemLp (fun omega => ∑ i ∈ t, g i omega) 2 mu := by
    intro t
    have hfun : (∑ i ∈ t, g i) = fun omega => ∑ i ∈ t, g i omega :=
      funext fun omega => Finset.sum_apply omega t g
    have h := memLp_finsetSum' (μ := mu) t fun j _ => hg j
    rwa [hfun] at h
  induction s using Finset.induction_on with
  | empty =>
      have h0 : hs.toLp (fun omega => ∑ i ∈ (∅ : Finset iota), g i omega)
          = MemLp.zero.toLp (0 : Omega → HilbertVec d) :=
        (MemLp.toLp_eq_toLp_iff hs MemLp.zero).2
          (Filter.Eventually.of_forall fun _ => Finset.sum_empty)
      rw [Finset.sum_empty, h0, MemLp.toLp_zero]
  | insert i s hi ih =>
      have hsplit : (fun omega => ∑ j ∈ insert i s, g j omega)
          = fun omega => g i omega + ∑ j ∈ s, g j omega :=
        funext fun omega => Finset.sum_insert hi
      rw [Finset.sum_insert hi, ← ih (hrest s)]
      refine (MemLp.toLp_eq_toLp_iff hs ((hg i).add (hrest s))).2 ?_
      exact Filter.Eventually.of_forall (congrFun hsplit)

/-- **The transported shell-sum forcing is the sum of the layer forcings.** -/
theorem carrierTransport_shellSumForcingL2 (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    carrierTransport (HilbertVec d) (measurePreserving_seqPathSum M n m)
        (shellSumForcingL2 M e n m)
      = ∑ k ∈ Finset.Ioc n m, layerForcingL2 M e k := by
  have hcomp := Lp.toLp_compMeasurePreserving
    (p := 2) (f := seqPathSum (d := d) n m)
    (memLp_two_valuePathForcing_shellSum M e n m) (measurePreserving_seqPathSum M n m)
  have hmem : MemLp (fun F : ℤ → C(Vec d, Mat d) =>
      ∑ k ∈ Finset.Ioc n m, layerForcing e k F) 2 (seqPathLaw M.P).toMeasure := by
    have hfun : (∑ k ∈ Finset.Ioc n m, layerForcing (d := d) e k)
        = fun F => ∑ k ∈ Finset.Ioc n m, layerForcing e k F :=
      funext fun F => Finset.sum_apply F (Finset.Ioc n m) (fun k => layerForcing e k)
    have h := memLp_finsetSum' (μ := (seqPathLaw M.P).toMeasure) (Finset.Ioc n m)
      fun k _ => memLp_two_layerForcing M e k
    rwa [hfun] at h
  have hrewrite : ((memLp_two_valuePathForcing_shellSum M e n m).comp_measurePreserving
      (measurePreserving_seqPathSum M n m)).toLp
        (valuePathForcing e ∘ seqPathSum (d := d) n m)
      = hmem.toLp (fun F => ∑ k ∈ Finset.Ioc n m, layerForcing e k F) := by
    refine (MemLp.toLp_eq_toLp_iff _ hmem).2 ?_
    exact Filter.Eventually.of_forall
      (congrFun (valuePathForcing_comp_seqPathSum e n m))
  calc carrierTransport (HilbertVec d) (measurePreserving_seqPathSum M n m)
        (shellSumForcingL2 M e n m)
      = ((memLp_two_valuePathForcing_shellSum M e n m).comp_measurePreserving
          (measurePreserving_seqPathSum M n m)).toLp
            (valuePathForcing e ∘ seqPathSum (d := d) n m) := hcomp
    _ = hmem.toLp (fun F => ∑ k ∈ Finset.Ioc n m, layerForcing e k F) := hrewrite
    _ = ∑ k ∈ Finset.Ioc n m, layerForcingL2 M e k :=
        toLp_finset_sum _ (fun k => layerForcing e k)
          (fun k => memLp_two_layerForcing M e k) hmem

/-! ### The layer decomposition of the corrector -/

/-- **The shell-sum corrector energy, resolved into layers.**

The `L²(Ω)` norm of the canonical shell-sum corrector equals the norm of
`Σ_{k ∈ (n,m]} P 𝐟_k` computed on the layer carrier, where `P` is the stationary
potential projection there.  This is the exact point at which
`e.perturb.assumption`'s layer decomposition becomes available: on the shell-sum
carrier the individual layers are not measurable, on the layer carrier they are,
and the two projected energies agree because the summation map is an equivariant
factor map. -/
theorem norm_shellSumPotentialCorrector_eq (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    ‖shellSumPotentialCorrector M e n m‖
      = ‖∑ k ∈ Finset.Ioc n m, stationaryPotentialProjection
          (μ := (seqPathLaw M.P).toMeasure) (layerForcingL2 M e k)‖ := by
  have hnat := norm_stationaryPotentialProjection_carrierTransport
    (d := d) (measurePreserving_seqPathSum M n m)
    (fun z F => seqPathSum_vadd n m z F) (shellSumForcingL2 M e n m)
  rw [carrierTransport_shellSumForcingL2 M e n m] at hnat
  rw [shellSumPotentialCorrector, norm_neg, ← hnat, map_sum]

end

end Algsuperdiff.Section3.Provider.Corrector
