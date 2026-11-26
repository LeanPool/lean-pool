/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145ActualResponseC2
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Time-domain convolution formulas for the first and second response variations.
-/

@[expose] public section

noncomputable section
namespace C145.ActualTimeConvolution
open MeasureTheory Set
open C145.ActualResponse
open scoped BigOperators Topology ContDiff
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

private theorem u2_continuous_extendInput {T : ℝ}
    (hT : 0 < T) (g : Input T) :
    Continuous (extendInput hT g) := by
  exact g.continuous.comp continuous_projIcc

private theorem u2_continuous_heat {n : ℕ}
    (Q : Frame n) (rates : State n) :
    Continuous (fun p : ℝ × State n =>
      C145.Pulse.heatAction Q rates p.1 p.2) := by
  unfold C145.Pulse.heatAction
  fun_prop

private theorem u2_continuous_firstState {n : ℕ} {T : ℝ}
    (hT : 0 < T) (Q : Frame n) (rates b : State n) (g : Input T) :
    Continuous (firstState hT Q rates b g) := by
  unfold firstState
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact ((u2_continuous_extendInput hT g).comp continuous_snd).smul
      ((u2_continuous_heat Q rates).comp
        ((continuous_fst.sub continuous_snd).prodMk continuous_const))
  · exact continuous_id

private theorem u2_continuous_delayIntegrand {n : ℕ}
    (Q : Frame n) (rates b : State n) :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      C145.DelayKernel.delayIntegrand Q rates b p.1.1 p.1.2 p.2) := by
  unfold C145.DelayKernel.delayIntegrand C145.Pulse.heatAction
  fun_prop

private theorem u2_continuous_delayKernel {n : ℕ}
    (Q : Frame n) (rates b : State n) :
    Continuous (fun p : ℝ × ℝ =>
      C145.DelayKernel.delayKernel Q rates b p.1 p.2) := by
  unfold C145.DelayKernel.delayKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact u2_continuous_delayIntegrand Q rates b
  · exact continuous_fst.min continuous_snd

private theorem u2_state_integral_apply {n : ℕ} {a c : ℝ}
    (f : ℝ → State n) (hf : Continuous f) (v : Fin (n + 1)) :
    (∫ s in a..c, f s) v = ∫ s in a..c, f s v := by
  simpa only [ContinuousLinearMap.proj_apply] using
    ((ContinuousLinearMap.proj v : State n →L[ℝ] ℝ).intervalIntegral_comp_comm
      (hf.intervalIntegrable a c)).symm

private theorem u2_observe_integral {n : ℕ} {a c : ℝ}
    (b : State n) (f : ℝ → State n) (hf : Continuous f) :
    observe b (∫ s in a..c, f s) =
      ∫ s in a..c, observe b (f s) := by
  classical
  have hterm (v : Fin (n + 1)) :
      IntervalIntegrable (fun s : ℝ => b v * f s v) volume a c := by
    have hcontinuous : Continuous (fun s : ℝ => b v * f s v) :=
      continuous_const.mul ((continuous_apply v).comp hf)
    exact hcontinuous.intervalIntegrable a c
  have hsum :
      (∫ s in a..c, ∑ v : Fin (n + 1), b v * f s v) =
        ∑ v : Fin (n + 1), ∫ s in a..c, b v * f s v :=
    intervalIntegral.integral_finsetSum
      (a := a) (b := c) (μ := volume)
      (s := Finset.univ) (f := fun v s => b v * f s v)
      (fun v _ => hterm v)
  change (∑ v : Fin (n + 1), b v * (∫ s in a..c, f s) v) =
    ∫ s in a..c, ∑ v : Fin (n + 1), b v * f s v
  calc
    (∑ v : Fin (n + 1), b v * (∫ s in a..c, f s) v) =
        ∑ v : Fin (n + 1), b v * (∫ s in a..c, f s v) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact congrArg (fun z : ℝ => b v * z)
        (u2_state_integral_apply (a := a) (c := c) f hf v)
    _ = ∑ v : Fin (n + 1), ∫ s in a..c, b v * f s v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (intervalIntegral.integral_const_mul
        (a := a) (b := c) (μ := volume) (b v) (fun s : ℝ => f s v)).symm
    _ = ∫ s in a..c, ∑ v : Fin (n + 1), b v * f s v := hsum.symm

private theorem u2_observe_heat_expansion {n : ℕ}
    (Q : Frame n) (rates b x : State n) (a : ℝ) :
    observe b (C145.Pulse.heatAction Q rates a x) =
      ∑ w, (∑ v, ∑ i,
        b v * Q v i * Real.exp (-rates i * a) * Q w i) * x w := by
  classical
  calc
    observe b (C145.Pulse.heatAction Q rates a x) =
        ∑ v, ∑ i, ∑ w,
          b v * (Q v i * Real.exp (-rates i * a) * (Q w i * x w)) := by
      simp only [observe, C145.Pulse.heatAction, Finset.mul_sum]
    _ = ∑ v, ∑ w, ∑ i,
          b v * (Q v i * Real.exp (-rates i * a) * (Q w i * x w)) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Finset.sum_comm
    _ = ∑ w, ∑ v, ∑ i,
          b v * (Q v i * Real.exp (-rates i * a) * (Q w i * x w)) :=
      Finset.sum_comm
    _ = ∑ w, (∑ v, ∑ i,
          b v * Q v i * Real.exp (-rates i * a) * Q w i) * x w := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem u2_observe_heat_firstState_product {n : ℕ} {T : ℝ}
    (hT : 0 < T) (Q : Frame n) (rates b : State n)
    (g h : Input T) (t s : ℝ) :
    observe b (C145.Pulse.heatAction Q rates (t - s)
      (fun w => firstState hT Q rates b g s w *
        firstState hT Q rates b h s w)) =
      ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s,
        extendInput hT g u * extendInput hT h v *
          C145.DelayKernel.delayIntegrand Q rates b
            (t - u) (t - v) (t - s) := by
  classical
  let L : Fin (n + 1) → ℝ := fun w =>
    ∑ v, ∑ i, b v * Q v i * Real.exp (-rates i * (t - s)) * Q w i
  let p : Fin (n + 1) → ℝ → ℝ := fun w u =>
    extendInput hT g u * C145.Pulse.heatAction Q rates (s - u) b w
  let q : Fin (n + 1) → ℝ → ℝ := fun w v =>
    extendInput hT h v * C145.Pulse.heatAction Q rates (s - v) b w
  have hp (w : Fin (n + 1)) : Continuous (p w) := by
    exact (u2_continuous_extendInput hT g).mul
      ((continuous_apply w).comp ((u2_continuous_heat Q rates).comp
        ((continuous_const.sub continuous_id).prodMk continuous_const)))
  have hq (w : Fin (n + 1)) : Continuous (q w) := by
    exact (u2_continuous_extendInput hT h).mul
      ((continuous_apply w).comp ((u2_continuous_heat Q rates).comp
        ((continuous_const.sub continuous_id).prodMk continuous_const)))
  have hfirst (k : Input T) (w : Fin (n + 1)) :
      firstState hT Q rates b k s w =
        ∫ u in (0 : ℝ)..s,
          extendInput hT k u * C145.Pulse.heatAction Q rates (s - u) b w := by
    simpa only [firstState, Pi.smul_apply, smul_eq_mul] using
      (u2_state_integral_apply
      (fun u => extendInput hT k u • C145.Pulse.heatAction Q rates (s - u) b)
      ((u2_continuous_extendInput hT k).smul
        ((u2_continuous_heat Q rates).comp
          ((continuous_const.sub continuous_id).prodMk continuous_const))) w)
  have hpoint (u v : ℝ) :
      extendInput hT g u * extendInput hT h v *
          C145.DelayKernel.delayIntegrand Q rates b (t - u) (t - v) (t - s) =
        ∑ w, L w * p w u * q w v := by
    change extendInput hT g u * extendInput hT h v *
      observe b (C145.Pulse.heatAction Q rates (t - s)
        (fun w => C145.Pulse.heatAction Q rates ((t - u) - (t - s)) b w *
          C145.Pulse.heatAction Q rates ((t - v) - (t - s)) b w)) = _
    rw [show (t - u) - (t - s) = s - u by ring,
      show (t - v) - (t - s) = s - v by ring,
      u2_observe_heat_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    dsimp only [L, p, q]
    ring
  have hterm (w : Fin (n + 1)) :
      L w * (∫ u in (0 : ℝ)..s, p w u) * (∫ v in (0 : ℝ)..s, q w v) =
        ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s, L w * p w u * q w v := by
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  have hinner (u : ℝ) :
      (∫ v in (0 : ℝ)..s, ∑ w, L w * p w u * q w v) =
        ∑ w, ∫ v in (0 : ℝ)..s, L w * p w u * q w v := by
    exact intervalIntegral.integral_finsetSum
      (fun w _ => (continuous_const.mul (hq w)).intervalIntegrable 0 s)
  have houter (w : Fin (n + 1)) :
      IntervalIntegrable
        (fun u => ∫ v in (0 : ℝ)..s, L w * p w u * q w v) volume 0 s := by
    simp only [intervalIntegral.integral_const_mul]
    exact ((continuous_const.mul (hp w)).mul continuous_const).intervalIntegrable 0 s
  calc
    observe b (C145.Pulse.heatAction Q rates (t - s)
        (fun w => firstState hT Q rates b g s w *
          firstState hT Q rates b h s w)) =
        ∑ w, L w * (∫ u in (0 : ℝ)..s, p w u) *
          (∫ v in (0 : ℝ)..s, q w v) := by
      rw [u2_observe_heat_expansion]
      apply Finset.sum_congr rfl
      intro w hw
      rw [hfirst g w, hfirst h w]
      dsimp only [L, p, q]
      ring
    _ = ∑ w, ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s,
          L w * p w u * q w v := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hterm w
    _ = ∫ u in (0 : ℝ)..s, ∑ w, ∫ v in (0 : ℝ)..s,
          L w * p w u * q w v :=
      (intervalIntegral.integral_finsetSum (fun w _ => houter w)).symm
    _ = ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s,
          ∑ w, L w * p w u * q w v := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact (hinner u).symm
    _ = ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s,
          extendInput hT g u * extendInput hT h v *
            C145.DelayKernel.delayIntegrand Q rates b
              (t - u) (t - v) (t - s) := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro v hv
      exact (hpoint u v).symm

private theorem u2_secondState_triple_integral {n : ℕ} {T : ℝ}
    (hT : 0 < T) (Q : Frame n) (rates b : State n)
    (g h : Input T) (t : ℝ) :
    observe b (secondState hT Q rates b g h t) =
      ∫ s in (0 : ℝ)..t, ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s,
        extendInput hT g u * extendInput hT h v *
          C145.DelayKernel.delayIntegrand Q rates b
            (t - u) (t - v) (t - s) := by
  let X : ℝ → State n := fun s =>
    firstState hT Q rates b g s * firstState hT Q rates b h s
  have hX : Continuous X :=
    (u2_continuous_firstState hT Q rates b g).mul
      (u2_continuous_firstState hT Q rates b h)
  let H : ℝ → State n := fun s =>
    C145.Pulse.heatAction Q rates (t - s) (X s)
  have htime : Continuous (fun s : ℝ => t - s) :=
    continuous_const.sub continuous_id
  have hpair : Continuous (fun s : ℝ => (t - s, X s)) :=
    htime.prodMk hX
  have hH : Continuous H :=
    (u2_continuous_heat Q rates).comp hpair
  have hobserve :
      observe b (∫ s in (0 : ℝ)..t, H s) =
        ∫ s in (0 : ℝ)..t, observe b (H s) :=
    u2_observe_integral (a := (0 : ℝ)) (c := t) b H hH
  calc
    observe b (secondState hT Q rates b g h t) =
        observe b (∫ s in (0 : ℝ)..t, H s) := rfl
    _ = ∫ s in (0 : ℝ)..t, observe b (H s) := hobserve
    _ = ∫ s in (0 : ℝ)..t, ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s,
          extendInput hT g u * extendInput hT h v *
            C145.DelayKernel.delayIntegrand Q rates b
              (t - u) (t - v) (t - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      change observe b (C145.Pulse.heatAction Q rates (t - s)
        (fun w => firstState hT Q rates b g s w *
          firstState hT Q rates b h s w)) = _
      exact u2_observe_heat_firstState_product hT Q rates b g h t s

private theorem u2_interval_eq_Icc {a c : ℝ}
    (hac : a ≤ c) (f : ℝ → ℝ) :
    (∫ s in a..c, f s) = ∫ s in Icc a c, f s := by
  rw [intervalIntegral.integral_of_le hac, integral_Icc_eq_integral_Ioc]

private theorem u2_compact_cube_integrable
    (t : ℝ) (_ht : 0 ≤ t) (F : ℝ → ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2)) :
    let ρ : Measure ℝ := volume.restrict (Icc (0 : ℝ) t)
    Integrable
      (({p : ℝ × (ℝ × ℝ) | p.2.1 ≤ p.1 ∧ p.2.2 ≤ p.1}).indicator
        (fun p => F p.1 p.2.1 p.2.2))
      (ρ.prod (ρ.prod ρ)) := by
  let C : Set ℝ := Icc (0 : ℝ) t
  have hcube : IsCompact (C ×ˢ (C ×ˢ C)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hbase : IntegrableOn
      (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2)
      (C ×ˢ (C ×ˢ C))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) :=
    hF.continuousOn.integrableOn_compact hcube
  have hrestricted : Integrable
      (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2)
      ((volume.restrict C).prod ((volume.restrict C).prod (volume.restrict C))) := by
    rw [Measure.prod_restrict C C, Measure.prod_restrict C (C ×ˢ C)]
    exact hbase
  have hclosed : IsClosed
      {p : ℝ × (ℝ × ℝ) | p.2.1 ≤ p.1 ∧ p.2.2 ≤ p.1} :=
    (isClosed_le (continuous_fst.comp continuous_snd) continuous_fst).inter
      (isClosed_le (continuous_snd.comp continuous_snd) continuous_fst)
  exact hrestricted.indicator hclosed.measurableSet

private theorem u2_lower_square_section
    (t s : ℝ) (hs : s ∈ Icc (0 : ℝ) t)
    (F : ℝ → ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2)) :
    (∫ q in Icc (0 : ℝ) t ×ˢ Icc (0 : ℝ) t,
      (({z : ℝ × ℝ | z.1 ≤ s ∧ z.2 ≤ s}).indicator
        (fun z => F s z.1 z.2)) q) =
      ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s, F s u v := by
  have hmask : MeasurableSet {z : ℝ × ℝ | z.1 ≤ s ∧ z.2 ≤ s} :=
    ((isClosed_le continuous_fst continuous_const).inter
      (isClosed_le continuous_snd continuous_const)).measurableSet
  have hset :
      (Icc (0 : ℝ) t ×ˢ Icc (0 : ℝ) t) ∩
          {z : ℝ × ℝ | z.1 ≤ s ∧ z.2 ≤ s} =
        Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) s := by
    ext z
    constructor
    · rintro ⟨⟨hu, hv⟩, hz⟩
      exact ⟨⟨hu.1, hz.1⟩, ⟨hv.1, hz.2⟩⟩
    · rintro ⟨hu, hv⟩
      exact ⟨⟨⟨hu.1, hu.2.trans hs.2⟩, ⟨hv.1, hv.2.trans hs.2⟩⟩,
        ⟨hu.2, hv.2⟩⟩
  have hsection : Continuous (fun z : ℝ × ℝ => F s z.1 z.2) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hint : IntegrableOn (fun z : ℝ × ℝ => F s z.1 z.2)
      (Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) s)
      ((volume : Measure ℝ).prod volume) :=
    hsection.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [setIntegral_indicator hmask, hset]
  change (∫ z in Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) s,
    F s z.1 z.2 ∂((volume : Measure ℝ).prod volume)) = _
  rw [setIntegral_prod _ hint, u2_interval_eq_Icc hs.1]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  exact (u2_interval_eq_Icc hs.1 (F s u)).symm

private theorem u2_upper_time_section
    (t u v : ℝ) (hu : u ∈ Icc (0 : ℝ) t)
    (hv : v ∈ Icc (0 : ℝ) t) (F : ℝ → ℝ → ℝ → ℝ) :
    (∫ s in Icc (0 : ℝ) t,
      (({s : ℝ | u ≤ s ∧ v ≤ s}).indicator
        (fun s => F s u v)) s) =
      ∫ s in max u v..t, F s u v := by
  have hmask : MeasurableSet {s : ℝ | u ≤ s ∧ v ≤ s} :=
    ((isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const continuous_id)).measurableSet
  have hset : Icc (0 : ℝ) t ∩ {s : ℝ | u ≤ s ∧ v ≤ s} =
      Icc (max u v) t := by
    ext s
    constructor
    · rintro ⟨hs, hm⟩
      exact ⟨max_le hm.1 hm.2, hs.2⟩
    · intro hs
      have hus : u ≤ s := (le_max_left u v).trans hs.1
      have hvs : v ≤ s := (le_max_right u v).trans hs.1
      exact ⟨⟨hu.1.trans hus, hs.2⟩, ⟨hus, hvs⟩⟩
  rw [setIntegral_indicator hmask, hset]
  exact (u2_interval_eq_Icc (max_le hu.2 hv.2) (fun s => F s u v)).symm

private theorem u2_compact_square_fubini
    (t : ℝ) (ht : 0 ≤ t) (F : ℝ → ℝ → ℝ → ℝ)
    (hF : Continuous (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2)) :
    (∫ s in (0 : ℝ)..t, ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s,
      F s u v) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
        ∫ s in max u v..t, F s u v := by
  let C : Set ℝ := Icc (0 : ℝ) t
  let ρ : Measure ℝ := volume.restrict C
  let : IsFiniteMeasure ρ := ⟨by
    change (volume.restrict C) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  let J : ℝ → (ℝ × ℝ) → ℝ := fun s q =>
    ({p : ℝ × (ℝ × ℝ) | p.2.1 ≤ p.1 ∧ p.2.2 ≤ p.1}).indicator
      (fun p => F p.1 p.2.1 p.2.2) (s, q)
  have hJ : Integrable (Function.uncurry J) (ρ.prod (ρ.prod ρ)) :=
    u2_compact_cube_integrable t ht F hF
  have hlower (s : ℝ) (hs : s ∈ C) :
      (∫ q, J s q ∂(ρ.prod ρ)) =
        ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s, F s u v := by
    change (∫ q, J s q ∂((volume.restrict C).prod (volume.restrict C))) = _
    rw [Measure.prod_restrict C C]
    exact u2_lower_square_section t s hs F hF
  have hupper (u v : ℝ) (hu : u ∈ C) (hv : v ∈ C) :
      (∫ s, J s (u, v) ∂ρ) = ∫ s in max u v..t, F s u v := by
    exact u2_upper_time_section t u v hu hv F
  have hmarginal : Integrable (fun q => ∫ s, J s q ∂ρ) (ρ.prod ρ) :=
    hJ.integral_prod_right
  have hrow (u : ℝ) (hu : u ∈ C) :
      (∫ v, ∫ s, J s (u, v) ∂ρ ∂ρ) =
        ∫ v in (0 : ℝ)..t, ∫ s in max u v..t, F s u v := by
    calc
      (∫ v, ∫ s, J s (u, v) ∂ρ ∂ρ) =
          ∫ v in C, ∫ s, J s (u, v) ∂ρ := rfl
      _ = ∫ v in C, ∫ s in max u v..t, F s u v := by
        apply setIntegral_congr_fun (s := C) measurableSet_Icc
        intro v hv
        change (∫ s, J s (u, v) ∂ρ) = ∫ s in max u v..t, F s u v
        exact hupper u v hu hv
      _ = ∫ v in (0 : ℝ)..t, ∫ s in max u v..t, F s u v :=
        (u2_interval_eq_Icc ht (fun v => ∫ s in max u v..t, F s u v)).symm
  calc
    (∫ s in (0 : ℝ)..t, ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s,
        F s u v) =
        ∫ s in C, ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s, F s u v :=
      u2_interval_eq_Icc ht
        (fun s => ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s, F s u v)
    _ = ∫ s in C, ∫ q, J s q ∂(ρ.prod ρ) := by
      apply setIntegral_congr_fun (s := C) measurableSet_Icc
      intro s hs
      change (∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s, F s u v) =
        ∫ q, J s q ∂(ρ.prod ρ)
      exact (hlower s hs).symm
    _ = ∫ s, ∫ q, J s q ∂(ρ.prod ρ) ∂ρ := rfl
    _ = ∫ q, ∫ s, J s q ∂ρ ∂(ρ.prod ρ) := integral_integral_swap hJ
    _ = ∫ u, ∫ v, ∫ s, J s (u, v) ∂ρ ∂ρ ∂ρ :=
      integral_prod (fun q : ℝ × ℝ => ∫ s, J s q ∂ρ) hmarginal
    _ = ∫ u in C, ∫ v in (0 : ℝ)..t, ∫ s in max u v..t, F s u v := by
      change (∫ u in C, ∫ v, ∫ s, J s (u, v) ∂ρ ∂ρ) = _
      apply setIntegral_congr_fun (s := C) measurableSet_Icc
      intro u hu
      change (∫ v, ∫ s, J s (u, v) ∂ρ ∂ρ) =
        ∫ v in (0 : ℝ)..t, ∫ s in max u v..t, F s u v
      exact hrow u hu
    _ = ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
          ∫ s in max u v..t, F s u v :=
      (u2_interval_eq_Icc ht
        (fun u => ∫ v in (0 : ℝ)..t, ∫ s in max u v..t, F s u v)).symm

private theorem u2_backward_delay_inner {n : ℕ} {T : ℝ}
    (hT : 0 < T) (Q : Frame n) (rates b : State n)
    (g h : Input T) (t u v : ℝ) :
    (∫ s in max u v..t,
      extendInput hT g u * extendInput hT h v *
        C145.DelayKernel.delayIntegrand Q rates b
          (t - u) (t - v) (t - s)) =
      C145.DelayKernel.delayKernel Q rates b (t - u) (t - v) *
        extendInput hT g u * extendInput hT h v := by
  have hendpoint : t - max u v = min (t - u) (t - v) := by
    rcases le_total u v with huv | hvu
    · rw [max_eq_right huv, min_eq_right (by linarith : t - v ≤ t - u)]
    · rw [max_eq_left hvu, min_eq_left (by linarith : t - u ≤ t - v)]
  have hreflect := intervalIntegral.integral_comp_sub_left
    (fun a : ℝ => C145.DelayKernel.delayIntegrand Q rates b (t - u) (t - v) a)
    (a := max u v) (b := t) t
  calc
    (∫ s in max u v..t,
        extendInput hT g u * extendInput hT h v *
          C145.DelayKernel.delayIntegrand Q rates b (t - u) (t - v) (t - s)) =
        (extendInput hT g u * extendInput hT h v) *
          (∫ s in max u v..t,
            C145.DelayKernel.delayIntegrand Q rates b (t - u) (t - v) (t - s)) :=
      intervalIntegral.integral_const_mul _ _
    _ = (extendInput hT g u * extendInput hT h v) *
          C145.DelayKernel.delayKernel Q rates b (t - u) (t - v) := by
      congr 1
      simpa only [C145.DelayKernel.delayKernel, sub_self, hendpoint] using hreflect
    _ = C145.DelayKernel.delayKernel Q rates b (t - u) (t - v) *
          extendInput hT g u * extendInput hT h v := by ring

theorem firstState_time_kernel {n : ℕ} {T : ℝ}
    (hT : 0 < T) (Q : Frame n) (rates b : State n)
    (g : Input T) (t : Time T) :
    observe b (firstState hT Q rates b g (t : ℝ)) =
      ∫ r in (0 : ℝ)..(t : ℝ),
        C145.DelayKernel.firstKernel Q rates b r *
          extendInput hT g ((t : ℝ) - r) := by
  have hcontinuous : Continuous
      (fun u : ℝ => extendInput hT g u •
        C145.Pulse.heatAction Q rates ((t : ℝ) - u) b) :=
    (u2_continuous_extendInput hT g).smul
      ((u2_continuous_heat Q rates).comp
        ((continuous_const.sub continuous_id).prodMk continuous_const))
  have hinverse (u : ℝ) : (t : ℝ) - ((t : ℝ) - u) = u := by ring
  unfold firstState
  rw [u2_observe_integral b _ hcontinuous]
  calc
    (∫ u in (0 : ℝ)..(t : ℝ),
        observe b (extendInput hT g u •
          C145.Pulse.heatAction Q rates ((t : ℝ) - u) b)) =
        ∫ u in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.firstKernel Q rates b ((t : ℝ) - u) * extendInput hT g u := by
      apply intervalIntegral.integral_congr
      intro u hu
      simp only [observe, C145.DelayKernel.firstKernel, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = ∫ r in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.firstKernel Q rates b r *
            extendInput hT g ((t : ℝ) - r) := by
      have hreflect := intervalIntegral.integral_comp_sub_left
        (fun r : ℝ => C145.DelayKernel.firstKernel Q rates b r *
          extendInput hT g ((t : ℝ) - r))
        (a := (0 : ℝ)) (b := (t : ℝ)) (t : ℝ)
      simpa only [sub_self, sub_zero, hinverse] using hreflect

theorem secondState_time_kernel {n : ℕ} {T : ℝ}
    (hT : 0 < T) (Q : Frame n) (rates b : State n)
    (g h : Input T) (t : Time T) :
    observe b (secondState hT Q rates b g h (t : ℝ)) =
      ∫ r₁ in (0 : ℝ)..(t : ℝ), ∫ r₂ in (0 : ℝ)..(t : ℝ),
        C145.DelayKernel.delayKernel Q rates b r₁ r₂ *
          extendInput hT g ((t : ℝ) - r₁) *
          extendInput hT h ((t : ℝ) - r₂) := by
  let D : (ℝ × ℝ) × ℝ → ℝ := fun z =>
    C145.DelayKernel.delayIntegrand Q rates b z.1.1 z.1.2 z.2
  have hD : Continuous D := u2_continuous_delayIntegrand Q rates b
  let U : ℝ × (ℝ × ℝ) → ℝ := fun p => p.2.1
  let V : ℝ × (ℝ × ℝ) → ℝ := fun p => p.2.2
  let S : ℝ × (ℝ × ℝ) → ℝ := fun p => p.1
  have hU : Continuous U := continuous_fst.comp continuous_snd
  have hV : Continuous V := continuous_snd.comp continuous_snd
  have hS : Continuous S := continuous_fst
  let R₁ : ℝ × (ℝ × ℝ) → ℝ := fun p => (t : ℝ) - U p
  let R₂ : ℝ × (ℝ × ℝ) → ℝ := fun p => (t : ℝ) - V p
  let A : ℝ × (ℝ × ℝ) → ℝ := fun p => (t : ℝ) - S p
  have hR₁ : Continuous R₁ := continuous_const.sub hU
  have hR₂ : Continuous R₂ := continuous_const.sub hV
  have hA : Continuous A := continuous_const.sub hS
  let P : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ := fun p => ((R₁ p, R₂ p), A p)
  have hP : Continuous P := (hR₁.prodMk hR₂).prodMk hA
  let G : ℝ × (ℝ × ℝ) → ℝ := fun p => extendInput hT g (U p)
  let H : ℝ × (ℝ × ℝ) → ℝ := fun p => extendInput hT h (V p)
  have hG : Continuous G := (u2_continuous_extendInput hT g).comp hU
  have hH : Continuous H := (u2_continuous_extendInput hT h).comp hV
  have hDP : Continuous (fun p : ℝ × (ℝ × ℝ) => D (P p)) := hD.comp hP
  have hproduct : Continuous
      (fun p : ℝ × (ℝ × ℝ) => (G p * H p) * D (P p)) :=
    (hG.mul hH).mul hDP
  let F : ℝ → ℝ → ℝ → ℝ := fun s u v =>
    extendInput hT g u * extendInput hT h v *
      C145.DelayKernel.delayIntegrand Q rates b
        ((t : ℝ) - u) ((t : ℝ) - v) ((t : ℝ) - s)
  have hFdef :
      (fun p : ℝ × (ℝ × ℝ) => (G p * H p) * D (P p)) =
        (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2) := rfl
  have hF : Continuous (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2.1 p.2.2) :=
    Eq.mp (congrArg (fun k : ℝ × (ℝ × ℝ) → ℝ => Continuous k) hFdef) hproduct
  have hinverse (u : ℝ) : (t : ℝ) - ((t : ℝ) - u) = u := by ring
  have hinner (u : ℝ) :
      (∫ v in (0 : ℝ)..(t : ℝ),
        C145.DelayKernel.delayKernel Q rates b ((t : ℝ) - u) ((t : ℝ) - v) *
          extendInput hT g u * extendInput hT h v) =
        ∫ r₂ in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.delayKernel Q rates b ((t : ℝ) - u) r₂ *
            extendInput hT g u * extendInput hT h ((t : ℝ) - r₂) := by
    have hreflect := intervalIntegral.integral_comp_sub_left
      (fun r₂ : ℝ => C145.DelayKernel.delayKernel Q rates b ((t : ℝ) - u) r₂ *
        extendInput hT g u * extendInput hT h ((t : ℝ) - r₂))
      (a := (0 : ℝ)) (b := (t : ℝ)) (t : ℝ)
    simpa only [sub_self, sub_zero, hinverse] using hreflect
  calc
    observe b (secondState hT Q rates b g h (t : ℝ)) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ u in (0 : ℝ)..s, ∫ v in (0 : ℝ)..s,
          F s u v :=
      u2_secondState_triple_integral hT Q rates b g h (t : ℝ)
    _ = ∫ u in (0 : ℝ)..(t : ℝ), ∫ v in (0 : ℝ)..(t : ℝ),
          ∫ s in max u v..(t : ℝ), F s u v :=
      u2_compact_square_fubini (t : ℝ) t.property.1 F hF
    _ = ∫ u in (0 : ℝ)..(t : ℝ), ∫ v in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.delayKernel Q rates b ((t : ℝ) - u) ((t : ℝ) - v) *
            extendInput hT g u * extendInput hT h v := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro v hv
      change (∫ s in max u v..(t : ℝ),
        extendInput hT g u * extendInput hT h v *
          C145.DelayKernel.delayIntegrand Q rates b
            ((t : ℝ) - u) ((t : ℝ) - v) ((t : ℝ) - s)) = _
      exact u2_backward_delay_inner hT Q rates b g h (t : ℝ) u v
    _ = ∫ u in (0 : ℝ)..(t : ℝ), ∫ r₂ in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.delayKernel Q rates b ((t : ℝ) - u) r₂ *
            extendInput hT g u * extendInput hT h ((t : ℝ) - r₂) := by
      apply intervalIntegral.integral_congr
      intro u hu
      change (∫ v in (0 : ℝ)..(t : ℝ),
        C145.DelayKernel.delayKernel Q rates b ((t : ℝ) - u) ((t : ℝ) - v) *
          extendInput hT g u * extendInput hT h v) = _
      exact hinner u
    _ = ∫ r₁ in (0 : ℝ)..(t : ℝ), ∫ r₂ in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.delayKernel Q rates b r₁ r₂ *
            extendInput hT g ((t : ℝ) - r₁) *
            extendInput hT h ((t : ℝ) - r₂) := by
      have hreflect := intervalIntegral.integral_comp_sub_left
        (fun r₁ : ℝ => ∫ r₂ in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.delayKernel Q rates b r₁ r₂ *
            extendInput hT g ((t : ℝ) - r₁) *
            extendInput hT h ((t : ℝ) - r₂))
        (a := (0 : ℝ)) (b := (t : ℝ)) (t : ℝ)
      simpa only [sub_self, sub_zero, hinverse] using hreflect

theorem actual_response_time_kernel {n : ℕ} {T : ℝ}
    (hT : 0 < T) (Q : Frame n) (rates b : State n)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (R : Input T → Path n T)
    (hR : IsActualResponse hT Q rates b R)
    (hcR : ContDiffAt ℝ 2 R 0)
    (g h : Input T) (t : Time T) :
    rawFirst b R g t =
        (∫ r in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.firstKernel Q rates b r *
            extendInput hT g ((t : ℝ) - r)) ∧
      rawMixed b R g h t =
        (∫ r₁ in (0 : ℝ)..(t : ℝ), ∫ r₂ in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.delayKernel Q rates b r₁ r₂ *
            extendInput hT g ((t : ℝ) - r₁) *
            extendInput hT h ((t : ℝ) - r₂)) ∧
      rawQuadratic b R g t =
        (∫ r₁ in (0 : ℝ)..(t : ℝ), ∫ r₂ in (0 : ℝ)..(t : ℝ),
          C145.DelayKernel.delayKernel Q rates b r₁ r₂ *
            extendInput hT g ((t : ℝ) - r₁) *
            extendInput hT g ((t : ℝ) - r₂)) := by
  obtain ⟨hfirst, hmixed, hquadratic⟩ :=
    actual_response_variations hT Q rates b hQ R hR hcR g h t
  exact ⟨hfirst.trans (firstState_time_kernel hT Q rates b g t),
    hmixed.trans (secondState_time_kernel hT Q rates b g h t),
    hquadratic.trans (secondState_time_kernel hT Q rates b g g t)⟩


end C145.ActualTimeConvolution
end

end
