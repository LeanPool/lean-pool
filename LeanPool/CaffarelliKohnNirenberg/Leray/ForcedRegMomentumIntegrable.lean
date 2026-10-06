/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumSlicePressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumRep
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularised

/-!
# Integrability of the momentum integrand

The regularized transport velocity of the forced regularized solution is a
jointly measurable convolution, bounded on bounded time intervals. Together
with the square integrability of the velocity, its gradient, the pressures and
the force on bounded slabs, this makes every term of the integrand of
`eq:reg-momentum-forced` integrable against a smooth compactly supported test.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

section Velocity

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

/-- The regularized transport velocity of the solution as a convolution. -/
theorem forcedRegTransport_eq (z : Vec3 × ℝ) (i : Fin 3) :
    regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z i =
      ∫ y, forcedTransportKernel ρ ε hε y * forcedRegRep ρ ε hε ha hf (z.1 - y, z.2) i := by
  have h := forcedTransport_component_eq (ρ := ρ) hε (a := fun x => forcedRegRep ρ ε hε ha hf (x, z.2))
    (forcedRegRep_memLp ρ ε hε ha hf z.2) z.1 i
  change regUniformMollifiedInitial ρ ε hε (fun x => forcedRegRep ρ ε hε ha hf (x, z.2)) z.1 i = _
  rw [h, convolution_def]
  rfl

theorem measurable_forcedRegTransport (i : Fin 3) :
    Measurable fun z : Vec3 × ℝ =>
      regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z i := by
  have hu := forcedRegRep_stronglyMeasurable ρ ε hε ha hf
  have hm : StronglyMeasurable fun q : (Vec3 × ℝ) × Vec3 =>
      forcedTransportKernel ρ ε hε q.2 * forcedRegRep ρ ε hε ha hf (q.1.1 - q.2, q.1.2) i := by
    have h1 : Measurable fun q : (Vec3 × ℝ) × Vec3 => forcedTransportKernel ρ ε hε q.2 :=
      (forcedTransportKernel_contDiff ρ ε hε).continuous.measurable.comp measurable_snd
    have h2 : Measurable fun q : (Vec3 × ℝ) × Vec3 =>
        forcedRegRep ρ ε hε ha hf (q.1.1 - q.2, q.1.2) i := by
      have hq : Measurable fun q : (Vec3 × ℝ) × Vec3 => (q.1.1 - q.2, q.1.2) :=
        ((measurable_fst.comp measurable_fst).sub measurable_snd).prodMk
          (measurable_snd.comp measurable_fst)
      exact (measurable_pi_apply i).comp (hu.measurable.comp hq)
    exact (h1.mul h2).stronglyMeasurable
  have h := hm.integral_prod_right' (ν := (volume : Measure Vec3))
  have heq : (fun z : Vec3 × ℝ =>
      regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z i) =
      fun z => ∫ y, forcedTransportKernel ρ ε hε y *
        forcedRegRep ρ ε hε ha hf (z.1 - y, z.2) i :=
    funext fun z => forcedRegTransport_eq ρ ε hε ha hf z i
  rw [heq]
  exact h.measurable

/-- The regularized transport velocity is bounded on bounded time intervals. -/
theorem forcedRegTransport_bound (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Vec3 × ℝ, z.2 ∈ Icc 0 T → ∀ i : Fin 3,
      |regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z i| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_forcedRegCurve ρ ε hε ha hf).norm.continuousOn
  have hκ : MemLp (forcedTransportKernel ρ ε hε) 2 volume :=
    (forcedTransportKernel_contDiff ρ ε hε).continuous.memLp_of_hasCompactSupport
      (forcedTransportKernel_hasCompactSupport ρ ε hε)
  refine ⟨(eLpNorm (forcedTransportKernel ρ ε hε) 2 volume * ENNReal.ofReal C).toReal,
    ENNReal.toReal_nonneg, fun z hz i => ?_⟩
  have hui : MemLp (fun x => forcedRegRep ρ ε hε ha hf (x, z.2) i) 2 volume :=
    (forcedRegRep_memLp ρ ε hε ha hf z.2).eval i
  have h1 := norm_convolution_le_of_memLp_two hκ hui z.1
  have hcomp : eLpNorm (fun x => forcedRegRep ρ ε hε ha hf (x, z.2) i) 2 volume ≤
      ENNReal.ofReal C := by
    calc eLpNorm (fun x => forcedRegRep ρ ε hε ha hf (x, z.2) i) 2 volume
        ≤ eLpNorm (fun x => forcedRegRep ρ ε hε ha hf (x, z.2)) 2 volume :=
          eLpNorm_mono (hui.aestronglyMeasurable) fun x => norm_le_pi_norm _ i
      _ = eLpNorm (realVectorL2Representative (forcedRegCurve ρ ε hε ha hf z.2)) 2 volume :=
          eLpNorm_congr_ae (forcedRegRep_slice ρ ε hε ha hf z.2)
      _ ≤ ENNReal.ofReal ‖forcedRegCurve ρ ε hε ha hf z.2‖ :=
          eLpNorm_realVectorL2Representative_le _
      _ ≤ ENNReal.ofReal C := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := hC z.2 hz
          rwa [norm_norm] at this
  have h2 : (eLpNorm (forcedTransportKernel ρ ε hε) 2 volume *
      eLpNorm (fun x => forcedRegRep ρ ε hε ha hf (x, z.2) i) 2 volume).toReal ≤
      (eLpNorm (forcedTransportKernel ρ ε hε) 2 volume * ENNReal.ofReal C).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top hκ.eLpNorm_ne_top ENNReal.ofReal_ne_top)
      (by gcongr)
  rw [forcedRegTransport_eq ρ ε hε ha hf z i, ← Real.norm_eq_abs]
  refine le_trans ?_ (h1.trans h2)
  rw [convolution_def]
  rfl

end Velocity


/-- The spatial divergence of a space-time test. -/
@[expose]
def stDiv (φ : Vec3 × ℝ → Vec3) : Vec3 × ℝ → ℝ := fun z => ∑ k : Fin 3, spaceDeriv k φ z k

theorem ae_mem_Ioo_prod (T : ℝ) :
    ∀ᵐ z ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))),
      z.2 ∈ Ioo 0 T := by
  rw [ae_iff]
  have hset : {z : Vec3 × ℝ | ¬z.2 ∈ Ioo 0 T} = (univ : Set Vec3) ×ˢ (Ioo 0 T)ᶜ := by
    ext z
    simp
  rw [hset, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioo.compl,
    compl_inter_self, measure_empty, mul_zero]

theorem memLp_test_component_prod {ψ : Vec3 × ℝ → Vec3} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (T : ℝ) (i : Fin 3) :
    MemLp (fun z => ψ z i) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
  ((continuous_apply i).comp hψ.continuous).memLp_of_hasCompactSupport
    (hψc.comp_left (g := fun v : Vec3 => v i) rfl)

theorem stDiv_contDiff {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (stDiv φ) :=
  ContDiff.sum fun k _ => contDiff_pi.1 (contDiff_spaceDeriv hφ k) k

theorem stDiv_hasCompactSupport {φ : Vec3 × ℝ → Vec3} (hφc : HasCompactSupport φ) :
    HasCompactSupport (stDiv φ) := by
  have h : ∀ k : Fin 3, HasCompactSupport (fun z => spaceDeriv k φ z k) := fun k =>
    (hasCompactSupport_spaceDeriv hφc k).comp_left (g := fun v : Vec3 => v k) rfl
  have heq : stDiv φ = (fun z => spaceDeriv 0 φ z 0) + (fun z => spaceDeriv 1 φ z 1) +
      (fun z => spaceDeriv 2 φ z 2) := by
    funext z
    simp [stDiv, Fin.sum_univ_three]
  rw [heq]
  exact ((h 0).add (h 1)).add (h 2)

section Terms

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)
  {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (T : ℝ)

theorem memLp_forcedRegRep_prod :
    MemLp (forcedRegRep ρ ε hε ha hf) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
  memLp_curveRep_prod (continuous_forcedRegCurve ρ ε hε ha hf)
    (forcedRegRep_stronglyMeasurable ρ ε hε ha hf) (forcedRegRep_slice ρ ε hε ha hf) T

include hφ hφc in
theorem integrable_time_term :
    Integrable (fun z => ∑ i : Fin 3, forcedRegRep ρ ε hε ha hf z i * timeDeriv φ z i)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
  integrable_finsetSum _ fun i _ =>
    ((memLp_forcedRegRep_prod ρ ε hε ha hf T).eval i).integrable_mul
      (memLp_test_component_prod (contDiff_timeDeriv hφ) (hasCompactSupport_timeDeriv hφc) T i)

include hφ hφc in
theorem integrable_transport_term :
    Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z j *
        forcedRegRep ρ ε hε ha hf z i * spaceDeriv j φ z i)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  obtain ⟨M, hM0, hM⟩ := forcedRegTransport_bound ρ ε hε ha hf T
  have hu2 := memLp_forcedRegRep_prod ρ ε hε ha hf T
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  have hprod : Integrable (fun z => forcedRegRep ρ ε hε ha hf z i * spaceDeriv j φ z i)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
    (hu2.eval i).integrable_mul (memLp_test_component_prod (contDiff_spaceDeriv hφ j)
      (hasCompactSupport_spaceDeriv hφc j) T i)
  have hmeas : AEStronglyMeasurable (fun z =>
      regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z j)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
    (measurable_forcedRegTransport ρ ε hε ha hf j).aestronglyMeasurable
  have h := hprod.bdd_mul hmeas (c := M) (by
    filter_upwards [ae_mem_Ioo_prod T] with z hz
    rw [Real.norm_eq_abs]
    exact hM z ⟨hz.1.le, hz.2.le⟩ j)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only
  ring


theorem memLp_forcedRegGrad_prod (hT : 0 ≤ T) :
    MemLp (forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf)) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  obtain ⟨D, hdis, -, -⟩ := forcedRegRep_energy ρ ε hε ha hf hT
  exact memLp_forcedMollifiedGrad_prod (forcedRegRep_stronglyMeasurable ρ ε hε ha hf)
    (forcedRegRep_locallyIntegrable ρ ε hε ha hf) (hdis.trans_lt ENNReal.ofReal_lt_top)

include hφ hφc in
theorem integrable_viscous_term (hT : 0 ≤ T) :
    Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) z i j * spaceDeriv j φ z i)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (((memLp_forcedRegGrad_prod ρ ε hε ha hf T hT).eval i).eval j).integrable_mul
      (memLp_test_component_prod (contDiff_spaceDeriv hφ j) (hasCompactSupport_spaceDeriv hφc j)
        T i)

include hφ hφc in
theorem integrable_quadPressure_term :
    Integrable (fun z => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) z * stDiv φ z)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
  (memLp_forcedQuadPressure_slab ρ ε hε (continuous_forcedRegCurve ρ ε hε ha hf) T).integrable_mul
    ((stDiv_contDiff hφ).continuous.memLp_of_hasCompactSupport (p := 2)
      (stDiv_hasCompactSupport hφc))

include hφ hφc in
theorem integrable_forcePressure_term (hT : 0 < T) :
    Integrable (fun z => forcePressure f hf z * stDiv φ z)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  obtain ⟨-, hfin, -, hbound⟩ := forcePressure_spec f hf T hT
  set K : Set Vec3 := Prod.fst '' tsupport φ with hKdef
  have hK : IsCompact K := hφc.image continuous_fst
  have hKm : MeasurableSet K := hK.measurableSet
  have hb := hbound K (Ioo 0 T) hKm measurableSet_Ioo subset_rfl
  have hKfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hIfin : volume (Ioo (0 : ℝ) T) ≠ ⊤ := by simp [Real.volume_Ioo]
  have hmem : MemLp (forcePressure f hf) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure ParabolicPoint).restrict (CKN.spaceTimeSet K (Ioo 0 T))) := by
    refine lt_of_le_of_lt hb ?_
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKfin)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hIfin))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne)
  have hmeasEq : ((volume : Measure ParabolicPoint).restrict (CKN.spaceTimeSet K (Ioo 0 T)) :
      Measure (Vec3 × ℝ)) =
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))).restrict
        (K ×ˢ univ) := by
    rw [forcedHopf_slab_measure_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hfinm : IsFiniteMeasure (((volume : Measure Vec3).prod
      ((volume : Measure ℝ).restrict (Ioo 0 T))).restrict (K ×ˢ univ)) := by
    rw [← hmeasEq, forcedHopf_slab_measure_eq_prod]
    refine ⟨?_⟩
    rw [← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top hK.measure_lt_top (by simp [Real.volume_Ioo])
  set g : Vec3 × ℝ → ℝ := fun z => forcePressure f hf z with hg
  have hmem' : MemLp g (ENNReal.ofReal (3 / 2 : ℝ))
      (((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))).restrict
        (K ×ˢ univ)) := hmeasEq ▸ hmem
  have hint : IntegrableOn g (K ×ˢ univ)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
    hmem'.integrable (by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num))
  have hind : Integrable ((K ×ˢ univ).indicator g)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
    (integrable_indicator_iff (hKm.prod MeasurableSet.univ)).2 hint
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support (stDiv_contDiff hφ).continuous
    (stDiv_hasCompactSupport hφc)
  have h := hind.mul_bdd (stDiv_contDiff hφ).continuous.aestronglyMeasurable
    (c := M) (Eventually.of_forall hM)
  refine h.congr (Eventually.of_forall fun z => ?_)
  by_cases hz : z.1 ∈ K
  · simp only [indicator, mem_prod, hz, mem_univ, and_self, ↓reduceIte]
    rfl
  · have hzt : z ∉ tsupport φ := fun h => hz ⟨z, h, rfl⟩
    have hd : fderiv ℝ φ z = 0 := by
      by_contra hne
      exact hzt (support_fderiv_subset ℝ hne)
    have h0 : stDiv φ z = 0 := by
      simp [stDiv, spaceDeriv, hd]
    simp [h0]

include hf hφ hφc in
theorem integrable_force_term (hT : 0 < T) :
    Integrable (fun z => ∑ i : Fin 3, f z i * φ z i)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  have h := hf T hT
  have h' : MemLp (fun z : Vec3 × ℝ => f z) 2
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
    restrict_spaceTimeSet_eq_prod (Ioo 0 T) ▸ h
  exact integrable_finsetSum _ fun i _ =>
    (h'.eval i).integrable_mul (memLp_test_component_prod hφ hφc T i)

end Terms

end CKN.Leray

end
