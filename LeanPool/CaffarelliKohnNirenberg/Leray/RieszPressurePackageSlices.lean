/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageAgreement
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Slice agreement for pressure extensions

The spatial extensions are independent of exponent on every tensor that is
integrable at two exponents. The proof reads them as time slices of extensions
of a tensor supported on a finite time interval.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

@[expose]
def rieszPressurePackageTimeTensor
    (F : Fin 3 → Fin 3 → Vec3 → ℝ) (i j : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  if z.2 ∈ Ioo 0 1 then F i j z.1 else 0

private theorem rieszPressurePackageTimeTensor_memLp
    (r : ℝ) (F : Fin 3 → Fin 3 → Vec3 → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r) (volume : Measure Vec3)) :
    ∀ i j, MemLp (rieszPressurePackageTimeTensor F i j)
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
  intro i j
  let E : Set (Vec3 × ℝ) := Set.univ ×ˢ Ioo 0 1
  let G : Vec3 × ℝ → ℝ := E.indicator (fun z => F i j z.1)
  have hE : MeasurableSet E := MeasurableSet.univ.prod measurableSet_Ioo
  have hProd : MemLp (fun z : Vec3 × ℝ => F i j z.1) (ENNReal.ofReal r)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 1))) :=
    (hF i j).comp_fst (volume.restrict (Ioo 0 1))
  have hG : MemLp G (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
    rw [Measure.volume_eq_prod Vec3 ℝ, memLp_indicator_iff_restrict hE]
    rw [← Measure.prod_restrict]
    simpa [E] using hProd
  have hTensor : G = rieszPressurePackageTimeTensor F i j := by
    funext z
    by_cases ht : z.2 ∈ Ioo 0 1 <;>
      simp [G, E, rieszPressurePackageTimeTensor, ht]
  simpa only [hTensor] using hG

theorem rieszPressureSlice_ae_eq_of_memLp_common
    (r : ℝ) (hr : 1 < r) (s : ℝ) (hs : 1 < s)
    (F : Fin 3 → Fin 3 → Vec3 → ℝ)
    (hFr : ∀ i j, MemLp (F i j) (ENNReal.ofReal r) (volume : Measure Vec3))
    (hFs : ∀ i j, MemLp (F i j) (ENNReal.ofReal s) (volume : Measure Vec3)) :
    rieszPressureSlice r hr (fun i j => (hFr i j).toLp (F i j)) =ᵐ[volume]
      rieszPressureSlice s hs (fun i j => (hFs i j).toLp (F i j)) := by
  let G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := rieszPressurePackageTimeTensor F
  have hGr : ∀ i j, MemLp (G i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    exact rieszPressurePackageTimeTensor_memLp r F hFr i j
  have hGs : ∀ i j, MemLp (G i j) (ENNReal.ofReal s)
      (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    exact rieszPressurePackageTimeTensor_memLp s F hFs i j
  let PR : Vec3 × ℝ → ℝ := rieszPressureSpaceTime r hr G hGr
  let PS : Vec3 × ℝ → ℝ := rieszPressureSpaceTime s hs G hGs
  have hEq : PR =ᵐ[volume] PS :=
    rieszPressureSpaceTime_ae_eq_of_memLp_common r hr s hs G hGr hGs
  have hPRmeas : Measurable PR := rieszPressureSpaceTime_measurable r hr G hGr
  have hPSmeas : Measurable PS := rieszPressureSpaceTime_measurable s hs G hGs
  have hSections := ae_time_sections_of_ae_eq hPRmeas hPSmeas hEq
  have hSliceR := rieszPressureSpaceTime_slice_ae_eq r hr G hGr
  have hSliceS := rieszPressureSpaceTime_slice_ae_eq s hs G hGs
  let Good : ℝ → Prop := fun t =>
    (∃ hFt : ∀ i j, MemLp (fun x : Vec3 => G i j (x, t))
        (ENNReal.ofReal r) (volume : Measure Vec3),
      (fun x : Vec3 => PR (x, t)) =ᵐ[volume]
        fun x => (rieszPressureSlice r hr
          (fun i j => (hFt i j).toLp (fun y : Vec3 => G i j (y, t))) : Vec3 → ℝ) x) ∧
    (∃ hFt : ∀ i j, MemLp (fun x : Vec3 => G i j (x, t))
        (ENNReal.ofReal s) (volume : Measure Vec3),
      (fun x : Vec3 => PS (x, t)) =ᵐ[volume]
        fun x => (rieszPressureSlice s hs
          (fun i j => (hFt i j).toLp (fun y : Vec3 => G i j (y, t))) : Vec3 → ℝ) x) ∧
    (fun x : Vec3 => PR (x, t)) =ᵐ[volume] fun x : Vec3 => PS (x, t)
  have hGood : ∀ᵐ t ∂(volume : Measure ℝ), Good t := by
    filter_upwards [hSliceR, hSliceS, hSections] with t hR hS hEqT
    rcases hR with ⟨hFrt, hR⟩
    rcases hS with ⟨hFst, hS⟩
    exact ⟨⟨hFrt, hR⟩, ⟨hFst, hS⟩, hEqT⟩
  have hInterval : (Ioo (0 : ℝ) 1).Nonempty := ⟨(1 / 2 : ℝ), by norm_num⟩
  have hBadNull : volume {t : ℝ | ¬ Good t} = 0 := ae_iff.mp hGood
  have hT : ∃ t : ℝ, t ∈ Ioo 0 1 ∧ Good t := by
    by_contra hnone
    have hSub : Ioo (0 : ℝ) 1 ⊆ {t : ℝ | ¬ Good t} := by
      intro t ht
      exact fun hgood => hnone ⟨t, ht, hgood⟩
    have hZero : volume (Ioo (0 : ℝ) 1) = 0 := measure_mono_null hSub hBadNull
    norm_num [Real.volume_Ioo] at hZero
  obtain ⟨t, ht, hGoodT⟩ := hT
  rcases hGoodT with ⟨⟨hFrt, hR⟩, ⟨hFst, hS⟩, hEqT⟩
  have hInputR : ∀ i j,
      (hFrt i j).toLp (fun x : Vec3 => G i j (x, t)) =
        (hFr i j).toLp (F i j) := by
    intro i j
    apply Lp.ext
    filter_upwards [(hFrt i j).coeFn_toLp, (hFr i j).coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂]
    simp [G, rieszPressurePackageTimeTensor, ht]
  have hInputS : ∀ i j,
      (hFst i j).toLp (fun x : Vec3 => G i j (x, t)) =
        (hFs i j).toLp (F i j) := by
    intro i j
    apply Lp.ext
    filter_upwards [(hFst i j).coeFn_toLp, (hFs i j).coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂]
    simp [G, rieszPressurePackageTimeTensor, ht]
  have hPressureR : rieszPressureSlice r hr
      (fun i j => (hFrt i j).toLp (fun x : Vec3 => G i j (x, t))) =
        rieszPressureSlice r hr (fun i j => (hFr i j).toLp (F i j)) := by
    congr 1
    funext i j
    exact hInputR i j
  have hPressureS : rieszPressureSlice s hs
      (fun i j => (hFst i j).toLp (fun x : Vec3 => G i j (x, t))) =
        rieszPressureSlice s hs (fun i j => (hFs i j).toLp (F i j)) := by
    congr 1
    funext i j
    exact hInputS i j
  filter_upwards [hR, hS, hEqT] with x hRx hSx hEqx
  rw [hRx, hSx, hPressureR, hPressureS] at hEqx
  exact hEqx

theorem rieszPressureSpaceTime_slice_exponent_agreement
    (r : ℝ) (hr : 1 < r) (s : ℝ) (hs : 1 < s)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hFr : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (hFs : ∀ i j, MemLp (F i j) (ENNReal.ofReal s)
      (volume : Measure (Vec3 × ℝ))) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      ∃ hFrt : ∀ i j, MemLp (fun x : Vec3 => F i j (x, t))
          (ENNReal.ofReal r) (volume : Measure Vec3),
      ∃ hFst : ∀ i j, MemLp (fun x : Vec3 => F i j (x, t))
          (ENNReal.ofReal s) (volume : Measure Vec3),
        rieszPressureSlice r hr (fun i j => (hFrt i j).toLp
          (fun x : Vec3 => F i j (x, t))) =ᵐ[volume]
        rieszPressureSlice s hs (fun i j => (hFst i j).toLp
          (fun x : Vec3 => F i j (x, t)) ) := by
  have hR := rieszPressureSpaceTime_slice_ae_eq r hr F hFr
  have hS := rieszPressureSpaceTime_slice_ae_eq s hs F hFs
  filter_upwards [hR, hS] with t hRt hSt
  obtain ⟨hFrt, _hRepR⟩ := hRt
  obtain ⟨hFst, _hRepS⟩ := hSt
  exact ⟨hFrt, hFst, rieszPressureSlice_ae_eq_of_memLp_common r hr s hs
    (fun i j x => F i j (x, t)) hFrt hFst⟩

end CKN.Leray

end
