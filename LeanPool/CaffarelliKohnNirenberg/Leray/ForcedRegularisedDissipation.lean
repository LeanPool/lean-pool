/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureOperator
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMildBounds
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedHopfSlab
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy

/-!
# The gradient and dissipation of the forced regularized solution

Where the frequency dissipation of the complex solution is finite, the real
solution has a square-integrable weak gradient given by the inverse transform
of its frequency gradient. The mollified-gradient field represents it, and
its squared norm is bounded by the frequency dissipation; this is the
gradient data of `lem:regularised-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray


/-- The real part of a complex field with square-integrable frequency
gradient has a weak gradient in every component. -/
theorem forcedFourierGrad_hasWeakGradientOn (v : ComplexVectorL2)
    (hv : MemLp (forcedFourierGradHat v) 2 volume) (i : Fin 3) :
    CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => realPartVectorL2Representative v x i)
      (fun x j => ((forcedFourierGrad v hv : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) j i).re) :=
  fun j => forcedFourierGrad_hasWeakPartialDerivOn v hv j i

/-- The slices of the mollified-gradient field of a representative of the
real part represent the weak gradient, and their squared norms are bounded by
the frequency dissipation. -/
theorem forcedMollifiedGrad_of_fourier {u : Vec3 × ℝ → Vec3} {s : ℝ} (v : ComplexVectorL2)
    (hv : MemLp (forcedFourierGradHat v) 2 volume)
    (hrep : (fun x => u (x, s)) =ᵐ[volume] realPartVectorL2Representative v) :
    (∀ i, CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u (x, s) i)
      (fun x => forcedMollifiedGrad u (x, s) i)) ∧
    (∀ i j, (fun x => forcedMollifiedGrad u (x, s) i j) =ᵐ[volume]
      fun x => ((forcedFourierGrad v hv : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) j i).re) := by
  set G := forcedFourierGrad v hv with hGdef
  have hcomp : ∀ i, (fun x => realPartVectorL2Representative v x i) =ᵐ[volume]
      fun x => u (x, s) i := fun i => by
    filter_upwards [hrep] with x hx
    rw [hx]
  have hweak : ∀ i, CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u (x, s) i)
      (fun x j => ((G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) j i).re) := fun i =>
    hasWeakGradientOn_congr_ae_left (hcomp i) (forcedFourierGrad_hasWeakGradientOn v hv i)
  have huloc : ∀ i, LocallyIntegrable (fun x => u (x, s) i) volume := fun i =>
    ((memLp_re_coord v i).ae_eq (by
      filter_upwards [hcomp i] with x hx
      rw [← hx]; rfl)).locallyIntegrable (by norm_num)
  have hGloc : ∀ i j, LocallyIntegrable
      (fun x => ((G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) j i).re) volume := fun i j =>
    (memLp_re_tensor_coord G j i).locallyIntegrable (by norm_num)
  have hslice : ∀ i j, (fun x => forcedMollifiedGrad u (x, s) i j) =ᵐ[volume]
      fun x => ((G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) j i).re := fun i j =>
    forcedMollifiedGrad_slice_ae_eq (huloc i) (hGloc i j) (hweak i j)
  refine ⟨fun i => ?_, hslice⟩
  have hall : (fun x j => ((G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x) j i).re) =ᵐ[volume]
      fun x => forcedMollifiedGrad u (x, s) i := by
    have h := ae_all_iff.2 fun j => hslice i j
    filter_upwards [h] with x hx
    funext j
    exact (hx j).symm
  exact hasWeakGradientOn_congr_ae_right hall (hweak i)

/-- The squared entries of the real parts of a complex tensor are bounded by
its squared norm. -/
theorem sum_sq_re_le_norm_sq (T : ComplexTensor3) :
    ∑ i : Fin 3, ∑ j : Fin 3, (T j i).re ^ 2 ≤ ‖T‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith only [sq_nonneg (T j i).im]

/-- The squared gradient of a slice is bounded by the frequency dissipation. -/
theorem lintegral_spatialGradientSq_le {u : Vec3 × ℝ → Vec3} {s : ℝ} (v : ComplexVectorL2)
    (hv : MemLp (forcedFourierGradHat v) 2 volume)
    (hrep : (fun x => u (x, s)) =ᵐ[volume] realPartVectorL2Representative v) :
    ∫⁻ x, ENNReal.ofReal (CKN.spatialGradientSq u (forcedMollifiedGrad u) (x, s)) ≤
      ENNReal.ofReal (forcedFourierDissipation v) := by
  set G := forcedFourierGrad v hv with hGdef
  obtain ⟨-, hslice⟩ := forcedMollifiedGrad_of_fourier v hv hrep
  have hall := ae_all_iff.2 fun i => ae_all_iff.2 fun j => hslice i j
  have hle : ∀ᵐ x ∂(volume : Measure Vec3),
      ENNReal.ofReal (CKN.spatialGradientSq u (forcedMollifiedGrad u) (x, s)) ≤
        ENNReal.ofReal (‖(G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x)‖ ^ 2) := by
    filter_upwards [hall] with x hx
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [CKN.spatialGradientSq]
    simp_rw [hx]
    exact sum_sq_re_le_norm_sq _
  refine (lintegral_mono_ae hle).trans (le_of_eq ?_)
  have hmp := vec3ToL2Vec3_measurePreserving
  have h1 : ∫⁻ x : Vec3, ENNReal.ofReal (‖(G : L2Vec3 → ComplexTensor3) (WithLp.toLp 2 x)‖ ^ 2) =
      ∫⁻ y : L2Vec3, ENNReal.ofReal (‖(G : L2Vec3 → ComplexTensor3) y‖ ^ 2) :=
    hmp.lintegral_comp (f := fun y => ENNReal.ofReal (‖(G : L2Vec3 → ComplexTensor3) y‖ ^ 2))
      ((Lp.stronglyMeasurable G).norm.pow 2).measurable.ennreal_ofReal
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp G).integrable_norm_pow two_ne_zero) (Eventually.of_forall fun y => by positivity),
    integral_norm_sq_eq_norm_sq_Lp, hGdef, norm_sq_forcedFourierGrad]
  rfl

theorem restrict_spaceTimeSet_eq_prod (I : Set ℝ) :
    ((volume : Measure ParabolicPoint).restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) I) :
      Measure (Vec3 × ℝ)) = (volume : Measure Vec3).prod ((volume : Measure ℝ).restrict I) := by
  rw [forcedHopf_slab_measure_eq_prod, Measure.restrict_univ]

/-- The positive-time dissipation up to time `t` as a slab integral. -/
theorem regUniformDissipation_eq_slab (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (t : ℝ) :
    regUniformDissipation u Du t = ∫⁻ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      ENNReal.ofReal (CKN.spatialGradientSq u Du z) := by
  unfold regUniformDissipation regUniformPositiveTimeMeasure
  have hS : MeasurableSet {z : ParabolicPoint | z.2 < t} := measurableSet_lt measurable_snd
    measurable_const
  have heq : (fun z : ParabolicPoint => if z.2 < t then
      ENNReal.ofReal (CKN.spatialGradientSq u Du z) else 0) =
      {z : ParabolicPoint | z.2 < t}.indicator
        (fun z => ENNReal.ofReal (CKN.spatialGradientSq u Du z)) := by
    funext z
    by_cases hz : z.2 < t
    · simp only [hz, ↓reduceIte]
      rw [indicator_of_mem (show z ∈ {z : ParabolicPoint | z.2 < t} from hz)]
    · simp only [hz, ↓reduceIte]
      rw [indicator_of_notMem (show z ∉ {z : ParabolicPoint | z.2 < t} from hz)]
  rw [heq, lintegral_indicator hS, Measure.restrict_restrict hS]
  congr 2
  ext z
  exact ⟨fun h => ⟨mem_univ _, h.2.2, h.1⟩, fun h => ⟨h.2.2, mem_univ _, h.2.1⟩⟩

end CKN.Leray

end
