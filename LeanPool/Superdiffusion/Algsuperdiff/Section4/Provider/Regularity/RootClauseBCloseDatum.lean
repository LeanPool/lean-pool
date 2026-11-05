/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.MinimalScaleShift
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepDatumSplit

/-!
# RootClauseBCloseDatum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The `L²` half -/

/-- **The pointwise bound from the Hölder seminorm**, against the cube's own
centre. -/
theorem norm_le_of_holderHalf_originCube {m : ℤ} {K : ℝ} {f : Vec d → Vec d}
    (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) :
    ‖f x‖ ≤ ‖f 0‖ + K * ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ) := by
  have h0 : (0 : Vec d) ∈ openCubeSet (originCube d m) :=
    zero_mem_openCubeSet_originCube d m
  have hdist : ‖x - 0‖ < (3 : ℝ) ^ m := by
    have h := openCubeSet_subset_ball h0 hx
    rwa [Metric.mem_ball, dist_eq_norm] at h
  have hhold := hf x hx 0 h0
  have hmono : ‖x - 0‖ ^ (1 / 2 : ℝ) ≤ ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hdist.le (by norm_num)
  have h2 : K * ‖x - 0‖ ^ (1 / 2 : ℝ) ≤ K * ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hmono hK
  have hid : f x - f 0 + f 0 = f x := by abel
  have htri : ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := by
    have h := norm_add_le (f x - f 0) (f 0)
    rwa [hid] at h
  linarith only [htri, hhold, h2]

/-- **The `L²` data binder from the root's own Hölder binder.**

A `C^{0,1/2}(□_m)` field is bounded and continuous there, hence `L^∞` for the
normalized cube measure and a fortiori `L²`. -/
theorem memLp_two_normalizedVolume_of_holderHalf {m : ℤ} {K : ℝ} {f : Vec d → Vec d}
    (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    MemLp f 2 (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) := by
  have hset : MeasurableSet (openCubeSet (originCube d m)) :=
    (isOpen_openCubeSet _).measurableSet
  have hvol0 : volume (openCubeSet (originCube d m)) ≠ 0 :=
    ((isOpen_openCubeSet _).measure_pos volume
      ⟨0, zero_mem_openCubeSet_originCube d m⟩).ne'
  have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top _
  have haes : AEStronglyMeasurable f
      (volume.restrict (openCubeSet (originCube d m))) :=
    (continuousOn_of_holderSeminormBoundOn hK hf).aestronglyMeasurable hset
  have htop : MemLp f ⊤ (volume.restrict (openCubeSet (originCube d m))) :=
    memLp_top_of_bound haes (‖f 0‖ + K * ((3 : ℝ) ^ m) ^ (1 / 2 : ℝ))
      (ae_restrict_of_forall_mem hset fun _ hx =>
        norm_le_of_holderHalf_originCube hK hf hx)
  have htwo : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) :=
    htop.mono_exponent le_top
  rw [Support.normalizedVolumeMeasureOn_def]
  exact htwo.smul_measure (ENNReal.inv_ne_top.mpr hvol0)

/-! ## 2. The kernel's measurability -/

/-- **The Gagliardo kernel is a.e. strongly measurable on the product measure.**

The scalar factor `|z₁-z₂|^{-(d/2+s)}` is GLOBALLY measurable; only the vector
factor `f(z₁) - f(z₂)` needs the window, and the Hölder bound makes it
continuous there. -/
theorem aestronglyMeasurable_gagliardoKernel_of_holderHalf {A : Set (Vec d)} {K s : ℝ}
    {f : Vec d → Vec d} (hA : MeasurableSet A) (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn A (1 / 2) K f) :
    AEStronglyMeasurable (Gagliardo.gagliardoKernel s 2 f)
      (Support.normalizedGagliardoMeasureOn A) := by
  have hcont := continuousOn_of_holderSeminormBoundOn hK hf
  have hmu : Support.normalizedGagliardoMeasureOn A =
      (volume A)⁻¹ • ((volume.prod volume).restrict (A ×ˢ A)) := by
    rw [Support.normalizedGagliardoMeasureOn_def, Support.normalizedVolumeMeasureOn_def,
      Measure.prod_smul_left, Measure.prod_restrict]
  rw [hmu]
  refine AEStronglyMeasurable.smul_measure ?_ _
  have hscal : AEStronglyMeasurable
      (fun z : Vec d × Vec d =>
        dist z.1 z.2 ^ (-(Gagliardo.kernelExponent d s 2)))
      ((volume.prod volume).restrict (A ×ˢ A)) :=
    (measurable_dist.pow measurable_const).aestronglyMeasurable
  have hfst : ContinuousOn (fun z : Vec d × Vec d => f z.1) (A ×ˢ A) :=
    hcont.comp continuous_fst.continuousOn fun _ hz => hz.1
  have hsnd : ContinuousOn (fun z : Vec d × Vec d => f z.2) (A ×ˢ A) :=
    hcont.comp continuous_snd.continuousOn fun _ hz => hz.2
  have hvec : AEStronglyMeasurable (fun z : Vec d × Vec d => f z.1 - f z.2)
      ((volume.prod volume).restrict (A ×ˢ A)) :=
    (hfst.sub hsnd).aestronglyMeasurable (hA.prod hA)
  exact hscal.smul hvec

/-! ## 3. The Gagliardo `MemLp` -/

/-- **The Gagliardo data binder from the root's own Hölder binder.**

`§2` supplies the measurability and the proved embedding atom
`normalizedGagliardoESeminormOn_cube_le` the finiteness — its bound
`K·C(d,s)·3^{m(1/2-s)}` is a real number, so the `L²` norm of the kernel is below `⊤`. -/
theorem memLp_two_gagliardoKernel_of_holderHalf {m : ℤ} {K s : ℝ} {f : Vec d → Vec d}
    (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    MemLp (Gagliardo.gagliardoKernel s 2 f) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) := by
  refine (?_)
  have hbound := normalizedGagliardoESeminormOn_cube_le (E := Vec d) (m := m) (g := f)
    (K := K) (s := s) hd hs0 hs hK hf
  rw [Support.normalizedGagliardoESeminormOn_def] at hbound
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

/-! ## 4. The pair at the §4.4 pin `s = 1/4` -/

/-- **Both data binders of the §4.4 chain, at the printed exponent.**

`stepOneS = 1/4` lies strictly inside `(0, 1/2)`, so the embedding applies and
the root's `C^{0,1/2}` binder — printed for `𝐠` at `K_g` and for `∇h` at `K_h`
— discharges BOTH `MemLp` hypotheses at once. -/
theorem memLp_pair_of_holderHalf {m : ℤ} {K : ℝ} {f : Vec d → Vec d} (hd : 1 ≤ d)
    (hK : 0 ≤ K)
    (hf : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K f) :
    MemLp f 2 (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))) ∧
      MemLp (Gagliardo.gagliardoKernel stepOneS 2 f) 2
        (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) := by
  refine ⟨memLp_two_normalizedVolume_of_holderHalf hK hf, ?_⟩
  exact memLp_two_gagliardoKernel_of_holderHalf hd (by rw [stepOneS]; norm_num)
    (by rw [stepOneS]; norm_num) hK hf

end

end Algsuperdiff.Section4.Provider.Regularity
