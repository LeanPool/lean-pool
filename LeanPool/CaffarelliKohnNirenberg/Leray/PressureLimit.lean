/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityQuadraticProduct
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityComponentConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Continuity of space-time Riesz pressure

Strong convergence of tensor components in space-time `L^r` passes through
all nine double Riesz transforms and their measurable pressure representative.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
open scoped Topology
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN.Leray

private theorem pressureLimit_tendsto_finset_sum_real
    {ι : Type*} {s : Finset ι} {f : ι → ℕ → ℝ} {g : ι → ℝ}
    (h : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (g i))) :
    Tendsto (fun n => ∑ i ∈ s, f i n) atTop (𝓝 (∑ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hs : ∀ j ∈ s, Tendsto (f j) atTop (𝓝 (g j)) := by
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert hi] using
        (h i (Finset.mem_insert_self i s)).add (ih hs)

private theorem rieszPressureSpaceTimeClass_sub
    (r : ℝ) (hr : 1 < r)
    (F G : RieszPressureSpaceTimeTensorLp r) :
    rieszPressureSpaceTimeClass r hr F - rieszPressureSpaceTimeClass r hr G =
      rieszPressureSpaceTimeClass r hr (fun i j => F i j - G i j) := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  simp only [rieszPressureSpaceTimeClass, map_sub, Finset.sum_sub_distrib]

private theorem rieszPressureSpaceTimeClass_tendsto
    (r : ℝ) (hr : 1 < r)
    [Fact (1 ≤ ENNReal.ofReal r)]
    (F : ℕ → RieszPressureSpaceTimeTensorLp r)
    (G : RieszPressureSpaceTimeTensorLp r)
    (hF : ∀ i j, Tendsto (fun n => F n i j) atTop (𝓝 (G i j))) :
    Tendsto (fun n => rieszPressureSpaceTimeClass r hr (F n)) atTop
      (𝓝 (rieszPressureSpaceTimeClass r hr G)) := by
  have hnorm (i j : Fin 3) :
      Tendsto (fun n => ‖F n i j - G i j‖) atTop (𝓝 0) := by
    exact (tendsto_iff_norm_sub_tendsto_zero).1 (hF i j)
  have hsumJ (i : Fin 3) :
      Tendsto (fun n => ∑ j : Fin 3, ‖F n i j - G i j‖) atTop (𝓝 0) := by
    simpa using pressureLimit_tendsto_finset_sum_real (s := Finset.univ)
      (f := fun j n => ‖F n i j - G i j‖) (g := fun _ => 0) (by
        intro j hj
        simpa using hnorm i j)
  have hsum :
      Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3, ‖F n i j - G i j‖)
        atTop (𝓝 0) := by
    simpa using pressureLimit_tendsto_finset_sum_real (s := Finset.univ)
      (f := fun i n => ∑ j : Fin 3, ‖F n i j - G i j‖)
      (g := fun _ => 0) (by
        intro i hi
        simpa using hsumJ i)
  have hmajor : Tendsto
      (fun n => rieszPressureOperatorBound r hr *
        ∑ i : Fin 3, ∑ j : Fin 3, ‖F n i j - G i j‖)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hsum)
  have hbound (n : ℕ) :
      ‖rieszPressureSpaceTimeClass r hr (F n) -
        rieszPressureSpaceTimeClass r hr G‖ ≤
        rieszPressureOperatorBound r hr *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖F n i j - G i j‖ := by
    rw [rieszPressureSpaceTimeClass_sub r hr]
    exact rieszPressureSpaceTimeClass_norm_le r hr
      (fun i j => F n i j - G i j)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact Filter.Eventually.of_forall hbound

/-- Strong space-time `L^r` convergence of every tensor component implies
strong `L^r` convergence of the canonical Riesz pressure representative. -/
theorem rieszPressureSpaceTime_eLpNorm_tendsto
    (r : ℝ) (hr : 1 < r)
    (F : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ n i j, MemLp (F n i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (hconv : ∀ i j, Tendsto
      (fun n => eLpNorm (F n i j - G i j) (ENNReal.ofReal r)
        (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (rieszPressureSpaceTime r hr (F n) (hF n) -
        rieszPressureSpaceTime r hr G hG)
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0) := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let Tin (n : ℕ) : RieszPressureSpaceTimeTensorLp r :=
    rieszPressureSpaceTimeTensorToLp r hr (F n) (hF n)
  let Tlim : RieszPressureSpaceTimeTensorLp r :=
    rieszPressureSpaceTimeTensorToLp r hr G hG
  have hTin (i j : Fin 3) : Tendsto (fun n => Tin n i j) atTop (𝓝 (Tlim i j)) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n z => F n i j z) (fun n => hF n i j) (G i j) (hG i j)).2 (hconv i j)
  have hclass := rieszPressureSpaceTimeClass_tendsto r hr Tin Tlim hTin
  have hP (n : ℕ) : MemLp (rieszPressureSpaceTime r hr (F n) (hF n))
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    rieszPressureSpaceTime_memLp r hr (F n) (hF n)
  have hPlim : MemLp (rieszPressureSpaceTime r hr G hG)
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    rieszPressureSpaceTime_memLp r hr G hG
  have hRep (n : ℕ) :
      (hP n).toLp (rieszPressureSpaceTime r hr (F n) (hF n)) =
        rieszPressureSpaceTimeClass r hr (Tin n) := by
    apply Lp.ext
    have hAE : rieszPressureSpaceTime r hr (F n) (hF n) =ᵐ[volume]
        (rieszPressureSpaceTimeClass r hr (Tin n) : Vec3 × ℝ → ℝ) := by
      simpa [Tin, rieszPressureSpaceTime, rieszPressureSpaceTimeRepresentative] using
        ((Lp.aestronglyMeasurable (rieszPressureSpaceTimeClass r hr (Tin n))).aemeasurable.ae_eq_mk.symm)
    filter_upwards [(hP n).coeFn_toLp, hAE] with z hto hrep
    exact hto.trans hrep
  have hRepLim :
      hPlim.toLp (rieszPressureSpaceTime r hr G hG) =
        rieszPressureSpaceTimeClass r hr Tlim := by
    apply Lp.ext
    have hAE : rieszPressureSpaceTime r hr G hG =ᵐ[volume]
        (rieszPressureSpaceTimeClass r hr Tlim : Vec3 × ℝ → ℝ) := by
      simpa [Tlim, rieszPressureSpaceTime, rieszPressureSpaceTimeRepresentative] using
        ((Lp.aestronglyMeasurable (rieszPressureSpaceTimeClass r hr Tlim)).aemeasurable.ae_eq_mk.symm)
    filter_upwards [hPlim.coeFn_toLp, hAE] with z hto hrep
    exact hto.trans hrep
  have hclass' : Tendsto
      (fun n => (hP n).toLp (rieszPressureSpaceTime r hr (F n) (hF n))) atTop
      (𝓝 (hPlim.toLp (rieszPressureSpaceTime r hr G hG))) := by
    simpa only [hRep, hRepLim] using hclass
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n z => rieszPressureSpaceTime r hr (F n) (hF n) z)
    hP (rieszPressureSpaceTime r hr G hG) hPlim).1 hclass'

local instance pressureLimit_holder_three_three_threeHalves :
    ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (ENNReal.ofReal (3 / 2 : ℝ)) := by
  have hreal : Real.HolderTriple 3 3 (3 / 2) := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
    hreal.ennrealOfReal

/-- Products of two spatial vector fields in `L³` have tensor components in
`L^(3/2)`, including after extension by zero from a measurable space-time set. -/
theorem rieszPressureSpaceTime_product_memLp_of_slab
    {s : Set (Vec3 × ℝ)} (hs : MeasurableSet s)
    (v w : Vec3 × ℝ → Vec3)
    (hv : ∀ i, MemLp (fun z => v z i) 3
      ((volume : Measure (Vec3 × ℝ)).restrict s))
    (hw : ∀ j, MemLp (fun z => w z j) 3
      ((volume : Measure (Vec3 × ℝ)).restrict s)) :
    ∀ i j, MemLp (s.indicator (fun z => v z i * w z j))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  intro i j
  rw [memLp_indicator_iff_restrict hs]
  exact (hv i).mul (hw j)

/-- The pressure of a tensor supported on a fixed measurable space-time set
is continuous under strong `L³` convergence of its two velocity factors. -/
theorem rieszPressureSpaceTime_product_tendsto_of_Lthree
    {s : Set (Vec3 × ℝ)} (hs : MeasurableSet s)
    (vseq wseq : ℕ → Vec3 × ℝ → Vec3)
    (v w : Vec3 × ℝ → Vec3)
    (hvseq : ∀ n, MemLp (vseq n) 3
      ((volume : Measure (Vec3 × ℝ)).restrict s))
    (hwseq : ∀ n, MemLp (wseq n) 3
      ((volume : Measure (Vec3 × ℝ)).restrict s))
    (hv : MemLp v 3 ((volume : Measure (Vec3 × ℝ)).restrict s))
    (hw : MemLp w 3 ((volume : Measure (Vec3 × ℝ)).restrict s))
    (hconvV : Tendsto (fun n => eLpNorm (vseq n - v) 3
      ((volume : Measure (Vec3 × ℝ)).restrict s)) atTop (𝓝 0))
    (hconvW : Tendsto (fun n => eLpNorm (wseq n - w) 3
      ((volume : Measure (Vec3 × ℝ)).restrict s)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (fun i j => s.indicator (fun z => vseq n z i * wseq n z j))
        (rieszPressureSpaceTime_product_memLp_of_slab hs (vseq n) (wseq n)
          (fun i => (hvseq n).eval i) (fun j => (hwseq n).eval j)) -
      rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (fun i j => s.indicator (fun z => v z i * w z j))
        (rieszPressureSpaceTime_product_memLp_of_slab hs v w
          (fun i => hv.eval i) (fun j => hw.eval j))
      ) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict s)) atTop (𝓝 0) := by
  have hFn (n : ℕ) : ∀ i j, MemLp
      (s.indicator (fun z => vseq n z i * wseq n z j))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    rieszPressureSpaceTime_product_memLp_of_slab hs (vseq n) (wseq n)
      (fun i => (hvseq n).eval i) (fun j => (hwseq n).eval j)
  have hG : ∀ i j, MemLp (s.indicator (fun z => v z i * w z j))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    rieszPressureSpaceTime_product_memLp_of_slab hs v w (fun i => hv.eval i) (fun j => hw.eval j)
  have hprod (i j : Fin 3) : Tendsto
      (fun n => eLpNorm
        (fun z => vseq n z i * wseq n z j - v z i * w z j)
        (3 / 2 : ℝ≥0∞) ((volume : Measure (Vec3 × ℝ)).restrict s))
      atTop (𝓝 0) :=
    stability_tendsto_eLpNorm_product_three
      (fun n z => vseq n z i) (fun n z => wseq n z j)
      (fun z => v z i) (fun z => w z j)
      (fun n => (hvseq n).eval i) (fun n => (hwseq n).eval j)
      (hv.eval i) (hw.eval j) (by
        have h := stability_tendsto_eLpNorm_component_three
          ((volume : Measure (Vec3 × ℝ)).restrict s) vseq v hvseq hconvV i
        have hsub (n : ℕ) : (fun z => vseq n z i) - (fun z => v z i) =
            (fun z => vseq n z i - v z i) := by
          funext z
          rfl
        simpa only [hsub] using h) (by
        have h := stability_tendsto_eLpNorm_component_three
          ((volume : Measure (Vec3 × ℝ)).restrict s) wseq w hwseq hconvW j
        have hsub (n : ℕ) : (fun z => wseq n z j) - (fun z => w z j) =
            (fun z => wseq n z j - w z j) := by
          funext z
          rfl
        simpa only [hsub] using h)
  have hconv (i j : Fin 3) : Tendsto
      (fun n => eLpNorm
        ((s.indicator (fun z => vseq n z i * wseq n z j)) -
          (s.indicator (fun z => v z i * w z j)))
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ))) atTop (𝓝 0) := by
    have hfun (n : ℕ) :
        (fun z => s.indicator (fun y => vseq n y i * wseq n y j) z -
          s.indicator (fun y => v y i * w y j) z) =
        s.indicator (fun z => vseq n z i * wseq n z j - v z i * w z j) := by
      funext z
      by_cases hz : z ∈ s <;> simp [hz]
    have hEq (n : ℕ) : eLpNorm
        ((s.indicator (fun z => vseq n z i * wseq n z j)) -
          (s.indicator (fun z => v z i * w z j)))
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) =
        eLpNorm (fun z => vseq n z i * wseq n z j - v z i * w z j)
          (ENNReal.ofReal (3 / 2 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict s) := by
      rw [show (s.indicator (fun z => vseq n z i * wseq n z j) -
          s.indicator (fun z => v z i * w z j)) =
          s.indicator (fun z => vseq n z i * wseq n z j - v z i * w z j) from hfun n]
      exact eLpNorm_indicator_eq_eLpNorm_restrict hs
    have hprod' : Tendsto
        (fun n => eLpNorm
          (fun z => vseq n z i * wseq n z j - v z i * w z j)
          (ENNReal.ofReal (3 / 2 : ℝ)) ((volume : Measure (Vec3 × ℝ)).restrict s))
        atTop (𝓝 0) := by
      simpa only [CKN.ofReal_threeHalves] using hprod i j
    exact hprod'.congr' (Filter.Eventually.of_forall fun n => (hEq n).symm)
  have hglobal := rieszPressureSpaceTime_eLpNorm_tendsto
    (3 / 2 : ℝ) (by norm_num)
    (fun n i j z => s.indicator (fun y => vseq n y i * wseq n y j) z)
    (fun i j z => s.indicator (fun y => v y i * w y j) z)
    hFn hG hconv
  have hle (n : ℕ) : eLpNorm
      (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (fun i j z => s.indicator (fun y => vseq n y i * wseq n y j) z) (hFn n) -
       rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (fun i j z => s.indicator (fun y => v y i * w y j) z) hG)
      (ENNReal.ofReal (3 / 2 : ℝ)) ((volume : Measure (Vec3 × ℝ)).restrict s) ≤
      eLpNorm
        (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (fun i j z => s.indicator (fun y => vseq n y i * wseq n y j) z) (hFn n) -
         rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (fun i j z => s.indicator (fun y => v y i * w y j) z) hG)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    exact eLpNorm_restrict_le _ _ _ _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hglobal
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · exact Filter.Eventually.of_forall hle

end CKN.Leray

end
