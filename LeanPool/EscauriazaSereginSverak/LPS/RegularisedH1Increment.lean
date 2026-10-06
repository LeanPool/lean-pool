/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedActualRHS
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedScalarCurve
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDirectRoute
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalCompose

/-!
# Time increments of the regularized velocity

The pointwise time derivative of the regularized velocity (`thm:regularised` of the CKN manuscript,
(R2)) and its slab square-integrability give the integrated increment of the
velocity against a fixed `L²` test field, by Fubini's theorem
(`lem:lps-regularized-Hk-start`).
-/

public section

open MeasureTheory Set
open scoped Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS
open CKN.Leray


/-- Pointwise time differentiation gives the integrated physical pairing
increment after Fubini, for any fixed spatial test in the product space.
This is the bridge from the regularized equation's pointwise derivatives to
the derivative classes in physical `L²`. -/
theorem lps_scalar_test_pairing_interval_increment
    {f g : Vec3 → ℝ → ℝ} {w : Vec3 → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hFcont : ∀ x, ContinuousOn (fun t => f x t) (Icc a b))
    (hGcont : ∀ x, ContinuousOn (fun t => g x t) (Icc a b))
    (hderiv : ∀ x t, t ∈ Ioo a b →
      HasDerivAt (fun s => f x s) (g x t) t)
    (hFa : Integrable (fun x => f x a * w x) volume)
    (hFb : Integrable (fun x => f x b * w x) volume)
    (hGprod : Integrable
      (fun z : Vec3 × ℝ => g z.1 z.2 * w z.1)
      ((volume.restrict Set.univ).prod (volume.restrict (Ioc a b)))) :
    (∫ x : Vec3, f x b * w x) - ∫ x : Vec3, f x a * w x =
      ∫ t in a..b, ∫ x : Vec3, g x t * w x := by
  have hpoint (x : Vec3) :
      f x b * w x - f x a * w x = ∫ t in a..b, g x t * w x := by
    have hFTC : ∫ t in a..b, g x t = f x b - f x a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
        (hFcont x) (fun t ht => hderiv x t ht)
        ((hGcont x).intervalIntegrable_of_Icc hab)
    calc
      f x b * w x - f x a * w x = (f x b - f x a) * w x := by ring
      _ = (∫ t in a..b, g x t) * w x := by rw [← hFTC]
      _ = ∫ t in a..b, g x t * w x := by
        rw [intervalIntegral.integral_mul_const]
  have hleft :
      (∫ x : Vec3, f x b * w x) - ∫ x : Vec3, f x a * w x =
        ∫ x : Vec3, (f x b * w x - f x a * w x) := by
    rw [integral_sub hFb hFa]
  have hswap :
    (∫ x : Vec3, ∫ t in a..b, g x t * w x) =
        ∫ t in a..b, ∫ x : Vec3, g x t * w x := by
    simp only [intervalIntegral.integral_of_le hab]
    have hGprod' : Integrable (fun z : Vec3 × ℝ => g z.1 z.2 * w z.1)
        (volume.prod (volume.restrict (Ioc a b))) := by
      simpa using hGprod
    exact integral_integral_swap hGprod'
  calc
    (∫ x : Vec3, f x b * w x) - ∫ x : Vec3, f x a * w x =
        ∫ x : Vec3, (f x b * w x - f x a * w x) := hleft
    _ = ∫ x : Vec3, ∫ t in a..b, g x t * w x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ t in a..b, ∫ x : Vec3, g x t * w x := hswap

/-- The regularized velocity has, at every positive time, the classical time derivative given by the regularized momentum right-hand side (`lem:lps-regularized-Hk-start`). -/
theorem lps_regR12_hasDerivAt_time
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) :
    ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      HasDerivAt (fun s : ℝ => CKN.Leray.regR12Velocity ρ ε hε b hb (z.1, s) i)
        (CKN.Leray.regR12TimeRHS ρ ε hε (CKN.Leray.regR12Velocity ρ ε hε b hb)
          (CKN.Leray.forcedQuadPressure ρ ε hε (CKN.Leray.regR12Curve ρ ε hε b hb)) z i) z.2 := by
  have hPath : ∀ T : ℝ, 0 ≤ T → ∃ v : C(CKN.Leray.RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
      ∀ t : CKN.Leray.RegularizedMildTimeInterval T,
        CKN.Leray.regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by positivity) (v t) =
          CKN.Leray.complexifyVectorL2 (CKN.Leray.regR12Curve ρ ε hε b hb t.1) :=
    fun T hT => CKN.Leray.regUniformMollifiedInitial_global_bessel_path ρ ε hε b hb 2 T hT
  exact CKN.Leray.regR12_hasDerivAt_of_inputs ρ ε hε b hb hPath
    (CKN.Leray.regR12Pressure_regularity ρ ε hε b hb hPath)
    CKN.Leray.regularisedR12_timeDerivative


/-- The regularized momentum right-hand side is continuous on positive times and square-integrable on every positive-time slab (`lem:lps-regularized-Hk-start`). -/
theorem lps_regR12_Q_facts
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) :
    (∀ i : Fin 3, ContinuousOn
      (fun z : ParabolicPoint => CKN.Leray.regR12TimeRHS ρ ε hε
        (CKN.Leray.regR12Velocity ρ ε hε b hb)
        (CKN.Leray.forcedQuadPressure ρ ε hε (CKN.Leray.regR12Curve ρ ε hε b hb)) z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T → ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint => CKN.Leray.regR12TimeRHS ρ ε hε
        (CKN.Leray.regR12Velocity ρ ε hε b hb)
        (CKN.Leray.forcedQuadPressure ρ ε hε (CKN.Leray.regR12Curve ρ ε hε b hb)) z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) := by
  have h := CKN.Leray.regR12_regularised_unconditional ρ b hb ε hε
  simp only [CKN.Leray.regR12Uε, CKN.Leray.regR12Pε, hε, ↓reduceDIte] at h
  obtain ⟨-, -, -, -, hDt, -, -, -, -, -, -, hL2, -, -, -⟩ := h
  have hEq : ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      timePartial (fun y => CKN.Leray.regR12Velocity ρ ε hε b hb y i) z =
        CKN.Leray.regR12TimeRHS ρ ε hε (CKN.Leray.regR12Velocity ρ ε hε b hb)
          (CKN.Leray.forcedQuadPressure ρ ε hε (CKN.Leray.regR12Curve ρ ε hε b hb)) z i :=
    fun z hz i => CKN.Leray.regR12_timePartial_eq_of_hasDerivAt
      (lps_regR12_hasDerivAt_time ρ ε hε b hb z hz i)
  refine ⟨fun i => (hDt i).congr fun z hz => (hEq z hz.2 i).symm, ?_⟩
  intro δ T hδ hδT i
  have hslab : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  refine (memLp_congr_ae ?_).1 ((hL2 δ T hδ hδT).2.2.2.1 i)
  filter_upwards [ae_restrict_mem hslab] with z hz
  exact hEq z (hδ.trans hz.2.1) i

/-- Fubini form of the pairing increment: pointwise differentiability in time together with slab square-integrability of the derivative gives the integrated increment against a fixed `L²` test function. -/
theorem lps_pairing_increment_of_slab
    {f g : Vec3 → ℝ → ℝ} {W : Vec3 → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ x, ∀ t ∈ Icc a b, HasDerivAt (f x) (g x t) t)
    (hgcont : ∀ x, ContinuousOn (g x) (Icc a b))
    (hfa : MemLp (fun x => f x a) 2 volume)
    (hfb : MemLp (fun x => f x b) 2 volume)
    (hW : MemLp W 2 volume)
    (hg : MemLp (fun z : Vec3 × ℝ => g z.1 z.2) 2
      (volume.restrict (Set.univ ×ˢ Ioc a b))) :
    IntervalIntegrable (fun t => ∫ x : Vec3, g x t * W x) volume a b ∧
    (∫ x : Vec3, f x b * W x) - ∫ x : Vec3, f x a * W x =
      ∫ t in a..b, ∫ x : Vec3, g x t * W x := by
  have hμ : (volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioc a b)) =
      volume.restrict (Set.univ ×ˢ Ioc a b) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hprodInt : Integrable (fun z : Vec3 × ℝ => g z.1 z.2 * W z.1)
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict (Ioc a b))) := by
    rw [hμ]
    have hWsq : Integrable (fun z : Vec3 × ℝ => W z.1 ^ 2)
        (volume.restrict (Set.univ ×ˢ Ioc a b)) := by
      have h := (hW.integrable_sq).comp_fst (volume.restrict (Ioc a b))
      rw [← hμ, Measure.restrict_univ]
      exact h
    have hgsq := hg.integrable_sq
    have hWmeas : AEStronglyMeasurable (fun z : Vec3 × ℝ => W z.1)
        (volume.restrict (Set.univ ×ˢ Ioc a b)) := by
      rw [← hμ, Measure.restrict_univ]
      exact hW.aestronglyMeasurable.comp_fst (ν := volume.restrict (Ioc a b))
    refine Integrable.mono' ((hgsq.add hWsq).div_const 2)
      (hg.aestronglyMeasurable.mul hWmeas) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    simp only [Pi.add_apply]
    nlinarith only [sq_nonneg (|g z.1 z.2| - |W z.1|), sq_abs (g z.1 z.2), sq_abs (W z.1)]
  refine ⟨?_, lps_scalar_test_pairing_interval_increment hab
    (fun x => (fun t ht => (hderiv x t ht).continuousAt.continuousWithinAt))
    hgcont
    (fun x t ht => hderiv x t ⟨ht.1.le, ht.2.le⟩)
    (hfa.integrable_mul hW) (hfb.integrable_mul hW) hprodInt⟩
  have hprod' := hprodInt.integral_prod_right
  have hprod'' : Integrable (fun t : ℝ => ∫ x : Vec3, g x t * W x)
      (volume.restrict (Ioc a b)) := by
    simpa [Measure.restrict_univ] using hprod'
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hprod''

/-- The pairing of the regularized velocity increment against a fixed `L²` test function equals the time integral of the pairing of the momentum right-hand side (`lem:lps-regularized-Hk-start`). -/
theorem lps_regR12_time_pairing_increment
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (W : Vec3 → ℝ) (hW : MemLp W 2 volume) (i : Fin 3) :
    IntervalIntegrable (fun t => ∫ x : Vec3, CKN.Leray.regR12TimeRHS ρ ε hε
        (CKN.Leray.regR12Velocity ρ ε hε b hb)
        (CKN.Leray.forcedQuadPressure ρ ε hε (CKN.Leray.regR12Curve ρ ε hε b hb))
        (x, t) i * W x) volume a c ∧
    (∫ x : Vec3, CKN.Leray.regR12Velocity ρ ε hε b hb (x, c) i * W x) -
        ∫ x : Vec3, CKN.Leray.regR12Velocity ρ ε hε b hb (x, a) i * W x =
      ∫ t in a..c, ∫ x : Vec3, CKN.Leray.regR12TimeRHS ρ ε hε
        (CKN.Leray.regR12Velocity ρ ε hε b hb)
        (CKN.Leray.forcedQuadPressure ρ ε hε (CKN.Leray.regR12Curve ρ ε hε b hb))
        (x, t) i * W x := by
  obtain ⟨hQcont, hQL2⟩ := lps_regR12_Q_facts ρ ε hε b hb
  refine lps_pairing_increment_of_slab
    (f := fun x t => CKN.Leray.regR12Velocity ρ ε hε b hb (x, t) i)
    (g := fun x t => CKN.Leray.regR12TimeRHS ρ ε hε
        (CKN.Leray.regR12Velocity ρ ε hε b hb)
        (CKN.Leray.forcedQuadPressure ρ ε hε (CKN.Leray.regR12Curve ρ ε hε b hb))
        (x, t) i) hac ?_ ?_ ?_ ?_ hW ?_
  · intro x t ht
    exact lps_regR12_hasDerivAt_time ρ ε hε b hb (x, t) (ha.trans_le ht.1) i
  · intro x
    have h1 : ContinuousOn (fun z : Vec3 × ℝ => CKN.Leray.regR12TimeRHS ρ ε hε
        (CKN.Leray.regR12Velocity ρ ε hε b hb)
        (CKN.Leray.forcedQuadPressure ρ ε hε (CKN.Leray.regR12Curve ρ ε hε b hb))
        ((z.1, z.2) : ParabolicPoint) i) (Set.univ ×ˢ Ioi 0) :=
      (hQcont i).comp parabolicHomeomorph.symm.continuous.continuousOn (fun _ hz => hz)
    exact h1.comp (f := fun t : ℝ => ((x, t) : Vec3 × ℝ))
      (s := Icc a c) (by fun_prop) (fun t ht => ⟨Set.mem_univ _, ha.trans_le ht.1⟩)
  · exact lps_regR12Velocity_all_word_memLp_slice ρ ε hε b hb a ha.le i []
  · exact lps_regR12Velocity_all_word_memLp_slice ρ ε hε b hb c (ha.le.trans hac) i []
  · have h := hQL2 (a / 2) (c + 1) (by linarith only [ha]) (by linarith only [ha, hac]) i
    refine h.mono_measure (Measure.restrict_mono ?_ le_rfl)
    intro z hz
    exact ⟨Set.mem_univ _, by linarith only [hz.2.1, ha], by linarith only [hz.2.2]⟩

end ESS.LPS

end
