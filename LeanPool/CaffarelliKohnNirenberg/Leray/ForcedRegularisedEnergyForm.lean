/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedDissipation
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedForce

/-!
# The space-time form of the forced energy inequality

The slice-wise gradient bounds of the forced regularized solution give, by
Tonelli's theorem, the space-time dissipation bound and the square
integrability of the gradient field on bounded slabs; the work of the force
along the solution curve is the space-time integral of the force against the
velocity. These are the space-time forms of `eq:reg-energy-forced` used in
`lem:regularised-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- The squared norm of a matrix is bounded by the sum of its squared
entries. -/
theorem norm_sq_le_sum_sq_entries (M : Fin 3 → Vec3) :
    ‖M‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, M i j ^ 2 := by
  have hS : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, M i j ^ 2 := by positivity
  have hle : ‖M‖ ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, M i j ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    have h1 : M i j ^ 2 ≤ ∑ j' : Fin 3, M i j' ^ 2 :=
      Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h2 : ∑ j' : Fin 3, M i j' ^ 2 ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, M i' j' ^ 2 :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, M i' j' ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    exact h1.trans h2
  calc ‖M‖ ^ 2 ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, M i j ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := Real.sq_sqrt hS

theorem measurable_forcedMollifiedGrad {u : Vec3 × ℝ → Vec3} (hu : StronglyMeasurable u)
    (hloc : ∀ t i, LocallyIntegrable (fun y => u (y, t) i) volume) :
    Measurable (forcedMollifiedGrad u) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    (forcedMollifiedGrad_stronglyMeasurable hu hloc i j).measurable

theorem measurable_spatialGradientSq_forcedMollifiedGrad {u : Vec3 × ℝ → Vec3}
    (hu : StronglyMeasurable u) (hloc : ∀ t i, LocallyIntegrable (fun y => u (y, t) i) volume) :
    Measurable fun z : Vec3 × ℝ => CKN.spatialGradientSq u (forcedMollifiedGrad u) z := by
  unfold CKN.spatialGradientSq
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (forcedMollifiedGrad_stronglyMeasurable hu hloc i j).measurable.pow_const 2

/-- A time slice whose complex lift has square-integrable frequency gradient
has the mollified-gradient field as weak gradient, with squared norm bounded
by the frequency dissipation. -/
theorem forcedSlice_gradient_dissipation {U : ℝ → RealVectorL2} {u : Vec3 × ℝ → Vec3}
    (hrep : ∀ s, (fun x => u (x, s)) =ᵐ[volume] realVectorL2Representative (U s))
    {w : ComplexVectorL2} {s : ℝ} (hw : realPartVectorL2 w = U s)
    (hv : MemLp (forcedFourierGradHat w) 2 volume) :
    (∀ i, CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u (x, s) i)
      (fun x => forcedMollifiedGrad u (x, s) i)) ∧
    ∫⁻ x, ENNReal.ofReal (CKN.spatialGradientSq u (forcedMollifiedGrad u) (x, s)) ≤
      ENNReal.ofReal (forcedFourierDissipation w) := by
  have h' : (fun x => u (x, s)) =ᵐ[volume] realPartVectorL2Representative w := by
    have h := realPartVectorL2Representative_eq_ae w
    rw [hw] at h
    exact (hrep s).trans h
  exact ⟨(forcedMollifiedGrad_of_fourier w hv h').1, lintegral_spatialGradientSq_le w hv h'⟩

/-- A lower integral over a slab of all space is an integral for the
product measure. -/
theorem lintegral_slab_eq_prod (g : Vec3 × ℝ → ℝ≥0∞) (I : Set ℝ) :
    ∫⁻ z in CKN.spaceTimeSet (Set.univ : Set Vec3) I, g z =
      ∫⁻ z, g z ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict I)) :=
  congrArg (fun μ : Measure (Vec3 × ℝ) => ∫⁻ z, g z ∂μ) (restrict_spaceTimeSet_eq_prod I)

/-- An integral over a slab of all space is an integral for the product
measure. -/
theorem integral_slab_eq_prod (g : Vec3 × ℝ → ℝ) (I : Set ℝ) :
    ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) I, g z =
      ∫ z, g z ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict I)) :=
  congrArg (fun μ : Measure (Vec3 × ℝ) => ∫ z, g z ∂μ) (restrict_spaceTimeSet_eq_prod I)

/-- Square integrability for the product measure is square integrability on
the slab. -/
theorem memLp_slab_of_prod {E : Type*} [NormedAddCommGroup E] {g : Vec3 × ℝ → E} {I : Set ℝ}
    {p : ℝ≥0∞} (h : MemLp g p ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict I))) :
    MemLp (g : ParabolicPoint → E) p
      ((volume : Measure ParabolicPoint).restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) I)) :=
  (restrict_spaceTimeSet_eq_prod I) ▸ h

/-- Tonelli's bound for the dissipation on a slab by the integrated slice
bounds. -/
theorem lintegral_slab_spatialGradientSq_le {u : Vec3 × ℝ → Vec3} (hu : StronglyMeasurable u)
    (hloc : ∀ t i, LocallyIntegrable (fun y => u (y, t) i) volume) {D : ℝ → ℝ} {T : ℝ}
    (hD : IntegrableOn D (Ioc 0 T)) (hD0 : ∀ s, 0 ≤ D s)
    (hle : ∀ᵐ s ∂(volume.restrict (Ioc 0 T)),
      ∫⁻ x, ENNReal.ofReal (CKN.spatialGradientSq u (forcedMollifiedGrad u) (x, s)) ≤
        ENNReal.ofReal (D s)) :
    ∫⁻ z, ENNReal.ofReal (CKN.spatialGradientSq u (forcedMollifiedGrad u) z)
        ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) ≤
      ENNReal.ofReal (∫ s in Ioc 0 T, D s) := by
  have hm := (measurable_spatialGradientSq_forcedMollifiedGrad hu hloc).ennreal_ofReal
  rw [lintegral_prod_symm _ hm.aemeasurable, Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall hD0)]
  exact lintegral_mono_ae hle

/-- Finite dissipation on a slab makes the gradient field square integrable
there. -/
theorem memLp_forcedMollifiedGrad_prod {u : Vec3 × ℝ → Vec3} (hu : StronglyMeasurable u)
    (hloc : ∀ t i, LocallyIntegrable (fun y => u (y, t) i) volume) {μ : Measure (Vec3 × ℝ)}
    (hfin : ∫⁻ z, ENNReal.ofReal (CKN.spatialGradientSq u (forcedMollifiedGrad u) z) ∂μ < ⊤) :
    MemLp (forcedMollifiedGrad u) 2 μ := by
  have hm := measurable_spatialGradientSq_forcedMollifiedGrad hu hloc
  have hg : Integrable
      (fun z => (ENNReal.ofReal (CKN.spatialGradientSq u (forcedMollifiedGrad u) z)).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hm.ennreal_ofReal.aemeasurable hfin.ne
  have hDm : AEStronglyMeasurable (forcedMollifiedGrad u) μ :=
    (measurable_forcedMollifiedGrad hu hloc).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hDm]
  refine hg.mono' (hDm.norm.pow 2) (Eventually.of_forall fun z => ?_)
  have h0 : 0 ≤ CKN.spatialGradientSq u (forcedMollifiedGrad u) z := by
    unfold CKN.spatialGradientSq
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ENNReal.toReal_ofReal h0]
  exact norm_sq_le_sum_sq_entries _

/-- A property holding almost everywhere on every bounded time interval holds
almost everywhere on positive times. -/
theorem ae_Ioi_of_forall_Ioc {P : ℝ → Prop}
    (h : ∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) ((n : ℝ) + 1))), P s) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), P s := by
  have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc 0 ((n : ℝ) + 1) := by
    ext s
    constructor
    · intro hs
      obtain ⟨n, hn⟩ := exists_nat_gt s
      exact mem_iUnion.2 ⟨n, hs, by linarith only [hn]⟩
    · intro hs
      obtain ⟨n, hn⟩ := mem_iUnion.1 hs
      exact hn.1
  rw [hU, ae_restrict_iUnion_iff]
  exact h

/-- The coordinate representative of a real `L²` field has `L²` norm at most
the norm of the field. -/
theorem eLpNorm_realVectorL2Representative_le (W : RealVectorL2) :
    eLpNorm (realVectorL2Representative W) 2 volume ≤ ENNReal.ofReal ‖W‖ := by
  have h1 : eLpNorm (fun x : Vec3 => (W : L2Vec3 → L2Vec3) (WithLp.toLp 2 x)) 2 volume =
      eLpNorm W 2 volume :=
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable W) vec3ToL2Vec3_measurePreserving
  calc eLpNorm (realVectorL2Representative W) 2 volume
      ≤ eLpNorm (fun x : Vec3 => (W : L2Vec3 → L2Vec3) (WithLp.toLp 2 x)) 2 volume := by
        refine eLpNorm_mono (realVectorL2Representative_memLp_two W).aestronglyMeasurable
          fun x => ?_
        change ‖WithLp.ofLp ((W : L2Vec3 → L2Vec3) (WithLp.toLp 2 x))‖ ≤ _
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => PiLp.norm_apply_le _ i
    _ = ENNReal.ofReal ‖W‖ := by
        rw [h1, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top W)]

/-- A jointly measurable representative of a continuous curve of real `L²`
fields is square integrable on bounded slabs. -/
theorem memLp_curveRep_prod {U : ℝ → RealVectorL2} (hUc : Continuous U) {u : Vec3 × ℝ → Vec3}
    (hu : StronglyMeasurable u)
    (hrep : ∀ s, (fun x => u (x, s)) =ᵐ[volume] realVectorL2Representative (U s)) (T : ℝ) :
    MemLp u 2 ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hUc.norm.continuousOn
  have hfin : eLpNorm u 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) ^ (2 : ℝ) < ⊤ := by
    rw [← lintegral_eLpNorm_slice_sq_eq hu]
    calc ∫⁻ t in Ioo 0 T, eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ (2 : ℝ)
        ≤ ∫⁻ _t in Ioo 0 T, ENNReal.ofReal M ^ (2 : ℝ) := by
          refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
          rw [eLpNorm_congr_ae (hrep t)]
          refine ENNReal.rpow_le_rpow ((eLpNorm_realVectorL2Representative_le _).trans
            (ENNReal.ofReal_le_ofReal ?_)) (by norm_num)
          have := hM t (Ioo_subset_Icc_self ht)
          rwa [norm_norm] at this
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
            ENNReal.ofReal_ne_top) (by simp [Real.volume_Ioo])
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 hfin

/-- The pairing of a real `L²` field with a transferred coordinate field is
the integral of the pointwise dot product of the representatives. -/
theorem inner_realVectorL2OfCoordinateFunction {W : RealVectorL2} {w : Vec3 → Vec3}
    (hw : w =ᵐ[volume] realVectorL2Representative W) (g : Vec3 → Vec3) (hg : MemLp g 2 volume) :
    inner ℝ W (realVectorL2OfCoordinateFunction g hg) = ∫ x, ∑ i : Fin 3, g x i * w x i := by
  have hEmb : MeasurableEmbedding (WithLp.toLp 2 : Vec3 → L2Vec3) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.measurableEmbedding
  rw [L2.inner_def, ← vec3ToL2Vec3_measurePreserving.integral_comp hEmb]
  refine integral_congr_ae ?_
  have hG := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae
    (realVectorL2OfCoordinateFunction_ae_eq_toLp g hg)
  filter_upwards [hG, hw] with x hx hwx
  have hW : (W : L2Vec3 → L2Vec3) (WithLp.toLp 2 x) = WithLp.toLp 2 (w x) := by
    rw [hwx]
    rfl
  rw [hx, hW, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]

/-- The work of the force along the solution curve is the space-time integral
of the force against the velocity. -/
theorem forcedForce_work_eq {U : ℝ → RealVectorL2} (hUc : Continuous U) {u : Vec3 × ℝ → Vec3}
    (hu : StronglyMeasurable u)
    (hrep : ∀ s, (fun x => u (x, s)) =ᵐ[volume] realVectorL2Representative (U s))
    (f : ParabolicPoint → Vec3) (hf : CKN.IsLocallySquareIntegrableForce f) {t : ℝ}
    (ht : 0 < t) :
    ∫ s in Ioc 0 t, inner ℝ (U s) (forcedForceSlice (forcedForceMod f hf) s) =
      ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), ∑ i : Fin 3, f z i * u z i := by
  set F := forcedForceMod f hf with hFdef
  have hFm : StronglyMeasurable F := forcedForceMod_stronglyMeasurable f hf
  have h1 : ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), ∑ i : Fin 3, f z i * u z i =
      ∫ z in CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), ∑ i : Fin 3, F z i * u z i := by
    refine integral_congr_ae ?_
    filter_upwards [forcedForceMod_ae_eq f hf ht] with z hz
    have hz' : F z = f z := hz
    simp only [hz']
  have hF2 := memLp_forcedForceMod_prod f hf ht
  have hu2 := memLp_curveRep_prod hUc hu hrep t
  have hint : Integrable (fun z : Vec3 × ℝ => ∑ i : Fin 3, F z i * u z i)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 t))) :=
    integrable_finsetSum _ fun i _ => (hF2.eval i).integrable_mul (hu2.eval i)
  rw [h1, integral_slab_eq_prod (fun z : Vec3 × ℝ => ∑ i : Fin 3, F z i * u z i),
    integral_prod_symm _ hint, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  have hfin : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) t)),
      eLpNorm (fun x : Vec3 => F (x, s)) 2 volume ^ (2 : ℝ) < ⊤ := by
    refine ae_lt_top' ((measurable_eLpNorm_two_slice hFm).pow_const _).aemeasurable ?_
    rw [lintegral_eLpNorm_slice_sq_eq hFm]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hF2.eLpNorm_ne_top).ne
  filter_upwards [ae_restrict_iff' measurableSet_Ioo |>.1 hfin] with s hs hsI
  have hs' : MemLp (fun x : Vec3 => F (x, s)) 2 volume :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 (hs hsI)
  have heq : forcedForceSlice F s = realVectorL2OfCoordinateFunction _ hs' := by
    unfold forcedForceSlice
    rw [dite_eq_left hs']
  rw [heq, inner_realVectorL2OfCoordinateFunction (hrep s)]

end CKN.Leray

end
