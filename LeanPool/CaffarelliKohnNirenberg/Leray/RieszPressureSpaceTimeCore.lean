/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTime
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completion of the space-time pressure operator

Compactly supported continuous fields form the dense core for the space-time
extension in `def:riesz-pressure`.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Equality on almost every spatial time slice implies product almost-equality. -/
theorem ae_eq_of_ae_time_sections
    {f g : Vec3 × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x : Vec3 => f (x, t)) =ᵐ[volume] fun x => g (x, t)) :
    f =ᵐ[(volume : Measure (Vec3 × ℝ))] g := by
  let μx : Measure Vec3 := volume
  let μt : Measure ℝ := volume
  let E : Set (Vec3 × ℝ) := {z | f z = g z}
  have hE : MeasurableSet E := by
    exact measurableSet_eq_fun hf hg
  have hS : MeasurableSet (Prod.swap ⁻¹' E) := hE.preimage measurable_swap
  have hIter : ∀ᵐ z ∂(μt.prod μx), z ∈ Prod.swap ⁻¹' E := by
    apply (Measure.ae_prod_iff_ae_ae hS).2
    filter_upwards [h] with t ht
    filter_upwards [ht] with x hx
    exact hx
  have hBadSource : (μt.prod μx) ((Prod.swap ⁻¹' E)ᶜ) = 0 := by
    exact (ae_iff.mp hIter)
  have hswap := Measure.measurePreserving_swap (μ := μt) (ν := μx)
  have hBad : (μx.prod μt) Eᶜ = 0 := by
    have hpre := hswap.measure_preimage (hE.compl.nullMeasurableSet)
    have hpre0 : (μt.prod μx) (Prod.swap ⁻¹' Eᶜ) = 0 := by
      simpa only [Set.preimage_compl] using hBadSource
    rw [hpre0] at hpre
    exact hpre.symm
  have hEventually : ∀ᵐ z ∂(μx.prod μt), z ∈ E := (ae_iff.mpr hBad)
  rw [Measure.volume_eq_prod]
  change ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod (volume : Measure ℝ)),
    f z = g z
  simpa [E, μx, μt] using hEventually

/-- Product almost-equality gives almost-equality on almost every time slice. -/
theorem ae_time_sections_of_ae_eq
    {f g : Vec3 × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (h : f =ᵐ[(volume : Measure (Vec3 × ℝ))] g) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x : Vec3 => f (x, t)) =ᵐ[volume] fun x => g (x, t) := by
  let μx : Measure Vec3 := volume
  let μt : Measure ℝ := volume
  let E : Set (Vec3 × ℝ) := {z | f z = g z}
  have hE : MeasurableSet E := measurableSet_eq_fun hf hg
  have hBadTarget : (μx.prod μt) Eᶜ = 0 := by
    have h' : ∀ᵐ z ∂(μx.prod μt), z ∈ E := by
      rw [Measure.volume_eq_prod] at h
      filter_upwards [h] with z hz
      simpa [E] using hz
    exact ae_iff.mp h'
  have hswap := Measure.measurePreserving_swap (μ := μt) (ν := μx)
  have hBadSource : (μt.prod μx) (Prod.swap ⁻¹' Eᶜ) = 0 := by
    have hpre := hswap.measure_preimage (hE.compl.nullMeasurableSet)
    rw [hBadTarget] at hpre
    exact hpre
  have hS : MeasurableSet (Prod.swap ⁻¹' E) := hE.preimage measurable_swap
  have hIter : ∀ᵐ z ∂(μt.prod μx), z ∈ Prod.swap ⁻¹' E := ae_iff.mpr hBadSource
  have hSections := (Measure.ae_prod_iff_ae_ae hS).1 hIter
  filter_upwards [hSections] with t ht
  filter_upwards [ht] with x hx
  exact hx
/-- A measurable compact-input representative of the `i,j` space-time Riesz pressure component. -/
@[expose]
noncomputable def rieszPressureComponentCompactRepresentative
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    Vec3 × ℝ → ℝ :=
  Classical.choose (exists_rieszPressure_component_memLp_bound_of_compact r hr i j hF hFc)

private theorem rieszPressureComponentCompactRepresentative_measurable
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    Measurable (rieszPressureComponentCompactRepresentative r hr i j hF hFc) :=
  (Classical.choose_spec
    (exists_rieszPressure_component_memLp_bound_of_compact r hr i j hF hFc)).1

private theorem rieszPressureComponentCompactRepresentative_slice
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x => rieszPressureComponentCompactRepresentative r hr i j hF hFc (x, t)) =ᵐ[volume]
        fun x => rieszPressureOperator r hr i j
          (((hF.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
            (continuous_spaceTimeSlice_hasCompactSupport hFc t)).toLp
            (fun y => F (y, t))) x :=
  (Classical.choose_spec
    (exists_rieszPressure_component_memLp_bound_of_compact r hr i j hF hFc)).2.1

theorem rieszPressureComponentCompactRepresentative_memLp
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    MemLp (rieszPressureComponentCompactRepresentative r hr i j hF hFc)
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
  (Classical.choose_spec
    (exists_rieszPressure_component_memLp_bound_of_compact r hr i j hF hFc)).2.2.1

private theorem rieszPressureComponentCompactRepresentative_bound
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    eLpNorm (rieszPressureComponentCompactRepresentative r hr i j hF hFc)
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ≤
      ENNReal.ofReal (rieszPressureOperatorBound r hr) *
        eLpNorm F (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
  (Classical.choose_spec
    (exists_rieszPressure_component_memLp_bound_of_compact r hr i j hF hFc)).2.2.2
/-- The space-time `L^r` class of the compact slice representative, consumed
by `lem:riesz-duality`. -/
@[expose]
noncomputable def rieszPressureComponentCompactClass
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
  haveI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  exact (rieszPressureComponentCompactRepresentative_memLp r hr i j hF hFc).toLp
    (rieszPressureComponentCompactRepresentative r hr i j hF hFc)
theorem rieszPressureComponentCompactClass_add
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F G : Vec3 × ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hFc : HasCompactSupport F) (hGc : HasCompactSupport G) :
    rieszPressureComponentCompactClass r hr i j (F := F + G) (hF.add hG) (hFc.add hGc) =
      rieszPressureComponentCompactClass r hr i j (F := F) hF hFc +
        rieszPressureComponentCompactClass r hr i j (F := G) hG hGc := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let H := rieszPressureComponentCompactRepresentative r hr i j (F := F + G)
    (hF.add hG) (hFc.add hGc)
  let A := rieszPressureComponentCompactRepresentative r hr i j (F := F) hF hFc
  let B := rieszPressureComponentCompactRepresentative r hr i j (F := G) hG hGc
  have hHmeas := rieszPressureComponentCompactRepresentative_measurable
    r hr i j (hF.add hG) (hFc.add hGc)
  have hAmeas := rieszPressureComponentCompactRepresentative_measurable r hr i j hF hFc
  have hBmeas := rieszPressureComponentCompactRepresentative_measurable r hr i j hG hGc
  have hHmem := rieszPressureComponentCompactRepresentative_memLp
    r hr i j (hF.add hG) (hFc.add hGc)
  have hAmem := rieszPressureComponentCompactRepresentative_memLp r hr i j hF hFc
  have hBmem := rieszPressureComponentCompactRepresentative_memLp r hr i j hG hGc
  have hHslice := rieszPressureComponentCompactRepresentative_slice
    r hr i j (hF.add hG) (hFc.add hGc)
  have hAslice := rieszPressureComponentCompactRepresentative_slice r hr i j hF hFc
  have hBslice := rieszPressureComponentCompactRepresentative_slice r hr i j hG hGc
  have hSections : ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x : Vec3 => H (x, t)) =ᵐ[volume]
        fun x => A (x, t) + B (x, t) := by
    filter_upwards [hHslice, hAslice, hBslice] with t hHt hAt hBt
    let f : Vec3 → ℝ := fun x => F (x, t)
    let g : Vec3 → ℝ := fun x => G (x, t)
    have hf : MemLp f (ENNReal.ofReal r) (volume : Measure Vec3) := by
      dsimp [f]
      exact (hF.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
        (continuous_spaceTimeSlice_hasCompactSupport hFc t)
    have hg : MemLp g (ENNReal.ofReal r) (volume : Measure Vec3) := by
      dsimp [g]
      exact (hG.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
        (continuous_spaceTimeSlice_hasCompactSupport hGc t)
    let hsum := hf.add hg
    have hsumCompact : MemLp (fun x : Vec3 => (F + G) (x, t))
        (ENNReal.ofReal r) (volume : Measure Vec3) := by
      exact ((hF.add hG).comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
        (continuous_spaceTimeSlice_hasCompactSupport (hFc.add hGc) t)
    have hfun : (fun x : Vec3 => (F + G) (x, t)) = f + g := by
      funext x
      rfl
    have hInput : hsumCompact.toLp (fun x : Vec3 => (F + G) (x, t)) =
        hf.toLp f + hg.toLp g := by
      calc
        hsumCompact.toLp (fun x : Vec3 => (F + G) (x, t)) = hsum.toLp (f + g) := by
          apply MemLp.toLp_congr hsumCompact hsum
          filter_upwards [] with x
          exact congrFun hfun x
        _ = hf.toLp f + hg.toLp g := MemLp.toLp_add hf hg
    let T := rieszPressureOperator r hr i j
    have hOperatorClass : T (hsumCompact.toLp (fun x : Vec3 => (F + G) (x, t))) =
        T (hf.toLp f) + T (hg.toLp g) := by
      rw [hInput]
      exact map_add T (hf.toLp f) (hg.toLp g)
    have hOperator := (Lp.ext_iff).1 hOperatorClass
    have hOperatorAE : (fun x => T (hsumCompact.toLp
        (fun y : Vec3 => (F + G) (y, t))) x) =ᵐ[volume]
        fun x => T (hf.toLp f) x + T (hg.toLp g) x := by
      exact hOperator.trans (Lp.coeFn_add (T (hf.toLp f)) (T (hg.toLp g)))
    filter_upwards [hHt, hAt, hBt, hOperatorAE] with x hHx hAx hBx hTx
    calc
      H (x, t) = T (hsumCompact.toLp (fun y : Vec3 => (F + G) (y, t))) x := hHx
      _ = T (hf.toLp f) x + T (hg.toLp g) x := hTx
      _ = A (x, t) + B (x, t) := by
        dsimp [A, B]
        rw [← hAx, ← hBx]
  have hProduct := ae_eq_of_ae_time_sections hHmeas (hAmeas.add hBmeas) hSections
  apply Lp.ext
  have hClassH := hHmem.coeFn_toLp
  have hClassA := hAmem.coeFn_toLp
  have hClassB := hBmem.coeFn_toLp
  have hClassAdd := Lp.coeFn_add
    (rieszPressureComponentCompactClass r hr i j (F := F) hF hFc)
    (rieszPressureComponentCompactClass r hr i j (F := G) hG hGc)
  filter_upwards [hClassH, hClassA, hClassB, hClassAdd, hProduct] with
    z hhz haz hbz hab hz
  calc
    rieszPressureComponentCompactClass r hr i j (F := F + G) (hF.add hG) (hFc.add hGc) z =
      H z := hhz
    _ = A z + B z := hz
    _ = rieszPressureComponentCompactClass r hr i j (F := F) hF hFc z +
        rieszPressureComponentCompactClass r hr i j (F := G) hG hGc z := by
      dsimp [A, B]
      dsimp [rieszPressureComponentCompactClass]
      rw [haz, hbz]
    _ = (rieszPressureComponentCompactClass r hr i j (F := F) hF hFc +
        rieszPressureComponentCompactClass r hr i j (F := G) hG hGc) z := hab.symm
theorem rieszPressureComponentCompactClass_smul
    (r : ℝ) (hr : 1 < r) (i j : Fin 3) (c : ℝ)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    rieszPressureComponentCompactClass r hr i j (F := c • F)
        (hF.const_smul c) (hFc.smul_left) =
      c • rieszPressureComponentCompactClass r hr i j (F := F) hF hFc := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have hFsmulCompact : HasCompactSupport (c • F) := by
    apply HasCompactSupport.of_support_subset_isCompact hFc.isCompact
    intro z hz
    change c • F z ≠ 0 at hz
    have hFz : F z ≠ 0 := by
      intro hzero
      simp [hzero] at hz
    exact subset_tsupport F hFz
  let P := rieszPressureComponentCompactRepresentative r hr i j (F := c • F)
    (hF.const_smul c) hFsmulCompact
  let A := rieszPressureComponentCompactRepresentative r hr i j (F := F) hF hFc
  have hPmeas := rieszPressureComponentCompactRepresentative_measurable r hr i j
    (hF.const_smul c) hFsmulCompact
  have hAmeas := rieszPressureComponentCompactRepresentative_measurable r hr i j hF hFc
  have hPmem := rieszPressureComponentCompactRepresentative_memLp r hr i j
    (hF.const_smul c) hFsmulCompact
  have hAmem := rieszPressureComponentCompactRepresentative_memLp r hr i j hF hFc
  have hPslice := rieszPressureComponentCompactRepresentative_slice r hr i j
    (hF.const_smul c) hFsmulCompact
  have hAslice := rieszPressureComponentCompactRepresentative_slice r hr i j hF hFc
  have hSections : ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x : Vec3 => P (x, t)) =ᵐ[volume]
        fun x => c • A (x, t) := by
    filter_upwards [hPslice, hAslice] with t hPt hAt
    let f : Vec3 → ℝ := fun x => F (x, t)
    have hf : MemLp f (ENNReal.ofReal r) (volume : Measure Vec3) := by
      dsimp [f]
      exact (hF.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
        (continuous_spaceTimeSlice_hasCompactSupport hFc t)
    have hcf : MemLp (fun x : Vec3 => (c • F) (x, t))
        (ENNReal.ofReal r) (volume : Measure Vec3) := by
      have hFsupport : HasCompactSupport (c • F) := by
        exact hFsmulCompact
      have hcontinuous : Continuous (fun x : Vec3 => (c • F) (x, t)) :=
        (hF.const_smul c).comp (continuous_id.prodMk continuous_const)
      exact hcontinuous.memLp_of_hasCompactSupport
        (continuous_spaceTimeSlice_hasCompactSupport hFsupport t)
    have hInput : hcf.toLp (fun x : Vec3 => (c • F) (x, t)) = c • hf.toLp f := by
      calc
        hcf.toLp (fun x : Vec3 => (c • F) (x, t)) =
            (hf.const_smul c).toLp (c • f) := by
          apply MemLp.toLp_congr hcf (hf.const_smul c)
          filter_upwards [] with x
          simp [f]
        _ = c • hf.toLp f := MemLp.toLp_const_smul c hf
    let T := rieszPressureOperator r hr i j
    have hOperatorClass :
        T (hcf.toLp (fun x : Vec3 => (c • F) (x, t))) = c • T (hf.toLp f) := by
      rw [hInput]
      exact map_smul T c (hf.toLp f)
    have hOperator := (Lp.ext_iff).1 hOperatorClass
    have hOperatorAE : (fun x => T
        (hcf.toLp (fun y : Vec3 => (c • F) (y, t))) x) =ᵐ[volume]
        fun x => c • T (hf.toLp f) x := by
      exact hOperator.trans (Lp.coeFn_smul c (T (hf.toLp f)))
    filter_upwards [hPt, hAt, hOperatorAE] with x hPx hAx hTx
    calc
      P (x, t) = T (hcf.toLp (fun y : Vec3 => (c • F) (y, t))) x := hPx
      _ = c • T (hf.toLp f) x := hTx
      _ = c • A (x, t) := by rw [← hAx]
  have hProduct := ae_eq_of_ae_time_sections hPmeas (hAmeas.const_smul c) hSections
  apply Lp.ext
  have hPclass := hPmem.coeFn_toLp
  have hAclass := hAmem.coeFn_toLp
  have hClassSmul := Lp.coeFn_smul c
    (rieszPressureComponentCompactClass r hr i j (F := F) hF hFc)
  filter_upwards [hPclass, hAclass, hClassSmul, hProduct] with z hp ha hs hz
  calc
    rieszPressureComponentCompactClass r hr i j (F := c • F)
        (hF.const_smul c) (hFc.smul_left) z = P z := hp
    _ = c • A z := hz
    _ = c • rieszPressureComponentCompactClass r hr i j (F := F) hF hFc z := by
      dsimp [A, rieszPressureComponentCompactClass]
      rw [ha]
    _ = (c • rieszPressureComponentCompactClass r hr i j (F := F) hF hFc) z := hs.symm
private theorem rieszPressureComponentCompactClass_congr_ae
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F G : Vec3 × ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hFc : HasCompactSupport F) (hGc : HasCompactSupport G)
    (hFG : F =ᵐ[(volume : Measure (Vec3 × ℝ))] G) :
    rieszPressureComponentCompactClass r hr i j (F := F) hF hFc =
      rieszPressureComponentCompactClass r hr i j (F := G) hG hGc := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let P := rieszPressureComponentCompactRepresentative r hr i j (F := F) hF hFc
  let Q := rieszPressureComponentCompactRepresentative r hr i j (F := G) hG hGc
  have hPmeas := rieszPressureComponentCompactRepresentative_measurable r hr i j hF hFc
  have hQmeas := rieszPressureComponentCompactRepresentative_measurable r hr i j hG hGc
  have hPmem := rieszPressureComponentCompactRepresentative_memLp r hr i j hF hFc
  have hQmem := rieszPressureComponentCompactRepresentative_memLp r hr i j hG hGc
  have hPslice := rieszPressureComponentCompactRepresentative_slice r hr i j hF hFc
  have hQslice := rieszPressureComponentCompactRepresentative_slice r hr i j hG hGc
  have hInputSlices := ae_time_sections_of_ae_eq hF.measurable hG.measurable hFG
  have hSections : ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x : Vec3 => P (x, t)) =ᵐ[volume] fun x => Q (x, t) := by
    filter_upwards [hInputSlices, hPslice, hQslice] with t hfg hPt hQt
    let f : Vec3 → ℝ := fun x => F (x, t)
    let g : Vec3 → ℝ := fun x => G (x, t)
    have hf : MemLp f (ENNReal.ofReal r) (volume : Measure Vec3) := by
      dsimp [f]
      exact (hF.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
        (continuous_spaceTimeSlice_hasCompactSupport hFc t)
    have hg : MemLp g (ENNReal.ofReal r) (volume : Measure Vec3) := by
      dsimp [g]
      exact (hG.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
        (continuous_spaceTimeSlice_hasCompactSupport hGc t)
    have hInput := MemLp.toLp_congr hf hg hfg
    let T := rieszPressureOperator r hr i j
    have hOperatorClass : T (hf.toLp f) = T (hg.toLp g) := congrArg T hInput
    have hOperator := (Lp.ext_iff).1 hOperatorClass
    filter_upwards [hPt, hQt, hOperator] with x hPx hQx hTx
    exact hPx.trans (hTx.trans hQx.symm)
  have hProduct := ae_eq_of_ae_time_sections hPmeas hQmeas hSections
  apply Lp.ext
  have hPclass := hPmem.coeFn_toLp
  have hQclass := hQmem.coeFn_toLp
  filter_upwards [hPclass, hQclass, hProduct] with z hp hq hz
  exact hp.trans (hz.trans hq.symm)

/-- The compact-input pressure class has a measurable representative with the
slice values used in `def:riesz-pressure`. -/
theorem exists_rieszPressureComponentCompactClass_representative
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    ∃ P : Vec3 × ℝ → ℝ, Measurable P ∧
      MemLp P (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ∧
      (P =ᵐ[volume]
        (rieszPressureComponentCompactClass r hr i j (F := F) hF hFc :
          Vec3 × ℝ → ℝ)) ∧
      (∀ᵐ t ∂(volume : Measure ℝ),
        (fun x => P (x, t)) =ᵐ[volume]
          fun x => rieszPressureOperator r hr i j
            (((hF.comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
              (continuous_spaceTimeSlice_hasCompactSupport hFc t)).toLp
              (fun y => F (y, t))) x) := by
  refine ⟨rieszPressureComponentCompactRepresentative r hr i j hF hFc,
    rieszPressureComponentCompactRepresentative_measurable r hr i j hF hFc,
    rieszPressureComponentCompactRepresentative_memLp r hr i j hF hFc, ?_,
    rieszPressureComponentCompactRepresentative_slice r hr i j hF hFc⟩
  exact (rieszPressureComponentCompactRepresentative_memLp r hr i j hF hFc).coeFn_toLp.symm

theorem hasCompactSupport_const_smul
    {F : Vec3 × ℝ → ℝ} (hF : HasCompactSupport F)
    (c : ℝ) : HasCompactSupport (c • F) := by
  apply HasCompactSupport.of_support_subset_isCompact hF.isCompact
  intro x hx
  change c • F x ≠ 0 at hx
  have hFx : F x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  exact subset_tsupport F hFx

/-- A continuous compactly supported space-time scalar input, used as a dense
core for `def:riesz-pressure` and `lem:riesz-duality`. -/
structure RieszPressureCompactInput where
  /-- The continuous compactly supported scalar function underlying a Riesz pressure input. -/
  value : Vec3 × ℝ → ℝ
  continuous_value : Continuous value
  compact_support_value : HasCompactSupport value

/-- The pointwise sum of two compactly supported continuous pressure inputs. -/
@[expose]
def RieszPressureCompactInput.add (F G : RieszPressureCompactInput) :
    RieszPressureCompactInput :=
  ⟨F.value + G.value, F.continuous_value.add G.continuous_value,
    F.compact_support_value.add G.compact_support_value⟩

/-- The scalar multiple of a compactly supported continuous pressure input. -/
@[expose]
def RieszPressureCompactInput.smul (c : ℝ) (F : RieszPressureCompactInput) :
    RieszPressureCompactInput :=
  ⟨c • F.value, F.continuous_value.const_smul c,
    hasCompactSupport_const_smul F.compact_support_value c⟩
/-- The `L^r` class of a compactly supported continuous input, used by
the space-time pressure extension. -/
@[expose]
noncomputable def rieszPressureCompactInputLpClass
    (r : ℝ) (_hr : 1 < r) (F : RieszPressureCompactInput) :
    Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
  haveI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal _hr.le⟩
  exact (F.continuous_value.memLp_of_hasCompactSupport F.compact_support_value).toLp
    F.value
theorem rieszPressureCompactInputLpClass_add
    (r : ℝ) (hr : 1 < r) (F G : RieszPressureCompactInput) :
    rieszPressureCompactInputLpClass r hr (F.add G) =
      rieszPressureCompactInputLpClass r hr F + rieszPressureCompactInputLpClass r hr G := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have hF := F.continuous_value.memLp_of_hasCompactSupport
    (p := ENNReal.ofReal r) (μ := (volume : Measure (Vec3 × ℝ)))
    F.compact_support_value
  have hG := G.continuous_value.memLp_of_hasCompactSupport
    (p := ENNReal.ofReal r) (μ := (volume : Measure (Vec3 × ℝ)))
    G.compact_support_value
  simpa [rieszPressureCompactInputLpClass, RieszPressureCompactInput.add] using
    (MemLp.toLp_add hF hG)
theorem rieszPressureCompactInputLpClass_smul
    (r : ℝ) (hr : 1 < r) (c : ℝ) (F : RieszPressureCompactInput) :
    rieszPressureCompactInputLpClass r hr (F.smul c) =
      c • rieszPressureCompactInputLpClass r hr F := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have hF := F.continuous_value.memLp_of_hasCompactSupport
    (p := ENNReal.ofReal r) (μ := (volume : Measure (Vec3 × ℝ)))
    F.compact_support_value
  simpa [rieszPressureCompactInputLpClass, RieszPressureCompactInput.smul] using
    (MemLp.toLp_const_smul c hF)
/-- The submodule of `L^r` classes represented by continuous compactly
supported inputs, used by `lem:riesz-duality`. -/
@[expose]
def rieszPressureSpaceTimeCore (r : ℝ) (hr : 1 < r) :
    Submodule ℝ (Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) where
  carrier := {u | ∃ F : RieszPressureCompactInput,
    u = rieszPressureCompactInputLpClass r hr F}
  zero_mem' := by
    have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    refine ⟨⟨0, continuous_const, HasCompactSupport.zero⟩, ?_⟩
    simp [rieszPressureCompactInputLpClass, MemLp.toLp_zero]
  add_mem' := by
    intro u v hu hv
    rcases hu with ⟨F, rfl⟩
    rcases hv with ⟨G, rfl⟩
    exact ⟨F.add G, (rieszPressureCompactInputLpClass_add r hr F G).symm⟩
  smul_mem' := by
    intro c u hu
    rcases hu with ⟨F, rfl⟩
    exact ⟨F.smul c, (rieszPressureCompactInputLpClass_smul r hr c F).symm⟩

/-- The compact continuous input classes are dense in space-time `L^r`,
used by `def:riesz-pressure` and `lem:riesz-duality`. -/
theorem rieszPressureSpaceTimeCore_dense (r : ℝ) (hr : 1 < r) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    Dense {u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) |
      u ∈ rieszPressureSpaceTimeCore r hr} := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  intro u
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 ?_
  intro ε hε
  have hεE : ENNReal.ofReal ε ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hε
  obtain ⟨g, hgSupp, hgSub, hgCont, hgMem⟩ :=
    (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofReal_ne_top hεE
  let w : RieszPressureCompactInput := ⟨g, hgCont, hgSupp⟩
  let v : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := hgMem.toLp g
  have hvCore : v ∈ rieszPressureSpaceTimeCore r hr := by
    refine ⟨w, ?_⟩
    exact (MemLp.toLp_eq_toLp_iff hgMem
      (w.continuous_value.memLp_of_hasCompactSupport w.compact_support_value)).2
        (ae_of_all _ fun _ => rfl)
  refine ⟨v, hvCore, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def]
  have hsub : eLpNorm ((u : Vec3 × ℝ → ℝ) - (v : Vec3 × ℝ → ℝ))
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal ε := by
    change eLpNorm ((u : Vec3 × ℝ → ℝ) -
      ((hgMem.toLp g : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
        Vec3 × ℝ → ℝ)) (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal ε
    calc
      eLpNorm ((u : Vec3 × ℝ → ℝ) -
          ((hgMem.toLp g : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
            Vec3 × ℝ → ℝ)) (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) =
          eLpNorm ((u : Vec3 × ℝ → ℝ) - g)
            (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
      eLpNorm_congr_ae (hgMem.coeFn_toLp.mono fun z hz => by
        change (u : Vec3 × ℝ → ℝ) z - (v : Vec3 × ℝ → ℝ) z =
          (u : Vec3 × ℝ → ℝ) z - g z
        rw [hz])
      _ ≤ ENNReal.ofReal ε := hgSub
  have hfinite : eLpNorm ((u : Vec3 × ℝ → ℝ) - (v : Vec3 × ℝ → ℝ))
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) ≠ ∞ :=
    (Lp.memLp u).sub (Lp.memLp v) |>.eLpNorm_ne_top
  exact (ENNReal.le_ofReal_iff_toReal_le hfinite hε.le).1 hsub

/-- The real-valued space-time `L^r` space used for pressure components. -/
abbrev RieszPressureSpaceTimeLp (r : ℝ) :=
  Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))

/-- The quotient-like core of compactly supported inputs for the space-time pressure operator at
exponent `r`. -/
abbrev RieszPressureSpaceTimeCore (r : ℝ) (hr : 1 < r) :=
  rieszPressureSpaceTimeCore r hr

/-- The `L^r` pressure component assigned to a compact-input equivalence class. -/
@[expose]
noncomputable def rieszPressureSpaceTimeCoreComponentValue
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    (u : RieszPressureSpaceTimeCore r hr) : RieszPressureSpaceTimeLp r := by
  let F := Classical.choose u.property
  exact rieszPressureComponentCompactClass r hr i j
    (F := F.value) F.continuous_value F.compact_support_value

private theorem rieszPressureCompactInput_memLp
    (r : ℝ) (F : RieszPressureCompactInput) :
    MemLp F.value (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
  exact F.continuous_value.memLp_of_hasCompactSupport F.compact_support_value

theorem rieszPressureSpaceTimeCoreComponentValue_eq
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    (u : RieszPressureSpaceTimeCore r hr) (F : RieszPressureCompactInput)
    (hF : (u : RieszPressureSpaceTimeLp r) =
      rieszPressureCompactInputLpClass r hr F) :
    rieszPressureSpaceTimeCoreComponentValue r hr i j u =
      rieszPressureComponentCompactClass r hr i j (F := F.value) F.continuous_value
        F.compact_support_value := by
  let G := Classical.choose u.property
  have hG : (u : RieszPressureSpaceTimeLp r) =
      rieszPressureCompactInputLpClass r hr G := Classical.choose_spec u.property
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have hFmem := rieszPressureCompactInput_memLp r F
  have hGmem := rieszPressureCompactInput_memLp r G
  have hFG : F.value =ᵐ[volume] G.value :=
    (MemLp.toLp_eq_toLp_iff hFmem hGmem).1 (hF.symm.trans hG)
  unfold rieszPressureSpaceTimeCoreComponentValue
  dsimp only
  exact (rieszPressureComponentCompactClass_congr_ae r hr i j
    (F := F.value) (G := G.value)
    F.continuous_value G.continuous_value F.compact_support_value
    G.compact_support_value hFG).symm

/-- The linear map assigning the space-time Riesz pressure component to each compact-input
class. -/
@[expose]
def rieszPressureSpaceTimeCoreComponentMap
    (r : ℝ) (hr : 1 < r) (i j : Fin 3) :
    RieszPressureSpaceTimeCore r hr →ₗ[ℝ] RieszPressureSpaceTimeLp r where
  toFun := rieszPressureSpaceTimeCoreComponentValue r hr i j
  map_add' := by
    intro u v
    obtain ⟨F, hF⟩ := u.property
    obtain ⟨G, hG⟩ := v.property
    have hsum : ((u + v : RieszPressureSpaceTimeCore r hr) :
        RieszPressureSpaceTimeLp r) =
        rieszPressureCompactInputLpClass r hr (F.add G) := by
      rw [Submodule.coe_add, hF, hG]
      exact rieszPressureCompactInputLpClass_add r hr F G
    rw [rieszPressureSpaceTimeCoreComponentValue_eq r hr i j (u + v) (F.add G) hsum,
      rieszPressureSpaceTimeCoreComponentValue_eq r hr i j u F hF,
      rieszPressureSpaceTimeCoreComponentValue_eq r hr i j v G hG]
    exact rieszPressureComponentCompactClass_add r hr i j
      F.continuous_value G.continuous_value F.compact_support_value G.compact_support_value
  map_smul' := by
    intro c u
    obtain ⟨F, hF⟩ := u.property
    have hsmul : ((c • u : RieszPressureSpaceTimeCore r hr) :
        RieszPressureSpaceTimeLp r) = rieszPressureCompactInputLpClass r hr (F.smul c) := by
      rw [Submodule.coe_smul, hF]
      exact rieszPressureCompactInputLpClass_smul r hr c F
    rw [rieszPressureSpaceTimeCoreComponentValue_eq r hr i j (c • u) (F.smul c) hsmul,
      rieszPressureSpaceTimeCoreComponentValue_eq r hr i j u F hF]
    exact rieszPressureComponentCompactClass_smul r hr i j c
      F.continuous_value F.compact_support_value

theorem rieszPressureSpaceTimeCoreComponentMap_bound
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    (u : RieszPressureSpaceTimeCore r hr) :
    ‖rieszPressureSpaceTimeCoreComponentMap r hr i j u‖ ≤
      rieszPressureOperatorBound r hr * ‖(u : RieszPressureSpaceTimeLp r)‖ := by
  obtain ⟨F, hF⟩ := u.property
  have hInput := rieszPressureCompactInput_memLp r F
  have hOutput := rieszPressureComponentCompactRepresentative_memLp r hr i j
    F.continuous_value F.compact_support_value
  have hBound := rieszPressureComponentCompactRepresentative_bound r hr i j
    F.continuous_value F.compact_support_value
  have hC : 0 ≤ rieszPressureOperatorBound r hr := by
    have h := rieszPressureOperator_norm_le r hr i j
    exact le_trans (norm_nonneg _) h
  have hNormOutput :
      ‖rieszPressureComponentCompactClass r hr i j (F := F.value)
        F.continuous_value F.compact_support_value‖ =
        ENNReal.toReal (eLpNorm
          (rieszPressureComponentCompactRepresentative r hr i j
            F.continuous_value F.compact_support_value)
          (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) := by
    change ‖hOutput.toLp _‖ = _
    exact Lp.norm_toLp _ hOutput
  have hNormInput :
      ‖rieszPressureCompactInputLpClass r hr F‖ =
        ENNReal.toReal (eLpNorm F.value (ENNReal.ofReal r)
          (volume : Measure (Vec3 × ℝ))) := by
    change ‖hInput.toLp F.value‖ = _
    exact Lp.norm_toLp _ hInput
  have hRealBound :
      ENNReal.toReal (eLpNorm
        (rieszPressureComponentCompactRepresentative r hr i j
          F.continuous_value F.compact_support_value)
        (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) ≤
      rieszPressureOperatorBound r hr * ENNReal.toReal
        (eLpNorm F.value (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) := by
    calc
      _ ≤ ENNReal.toReal (ENNReal.ofReal (rieszPressureOperatorBound r hr) *
          eLpNorm F.value (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hInput.eLpNorm_ne_top) hBound
      _ = _ := by
        rw [ENNReal.toReal_mul]
        simp [hC]
  calc
    ‖rieszPressureSpaceTimeCoreComponentMap r hr i j u‖ =
        ‖rieszPressureComponentCompactClass r hr i j (F := F.value)
          F.continuous_value F.compact_support_value‖ := by
      change ‖rieszPressureSpaceTimeCoreComponentValue r hr i j u‖ = _
      rw [rieszPressureSpaceTimeCoreComponentValue_eq r hr i j u F hF]
    _ ≤ rieszPressureOperatorBound r hr *
        ‖rieszPressureCompactInputLpClass r hr F‖ := by
      rw [hNormOutput, hNormInput]
      exact hRealBound
    _ = rieszPressureOperatorBound r hr * ‖(u : RieszPressureSpaceTimeLp r)‖ := by
      exact congrArg (fun z : ℝ => rieszPressureOperatorBound r hr * z)
        (congrArg norm hF.symm)

/-- The space-time extension of one double Riesz transform, used by
`def:riesz-pressure` and `lem:riesz-duality`. -/
@[expose]
noncomputable def rieszPressureSpaceTimeComponent
    (r : ℝ) (hr : 1 < r) (i j : Fin 3) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    RieszPressureSpaceTimeLp r →L[ℝ] RieszPressureSpaceTimeLp r := by
  letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let f := rieszPressureSpaceTimeCoreComponentMap r hr i j
  have hbound : ∀ u, ‖f u‖ ≤ rieszPressureOperatorBound r hr *
      ‖(rieszPressureSpaceTimeCore r hr).subtypeL u‖ := by
    intro u
    exact rieszPressureSpaceTimeCoreComponentMap_bound r hr i j u
  exact f.extendOfNorm (rieszPressureSpaceTimeCore r hr).subtypeL

/-- The space-time operator norm bound for one component, used by
`eq:riesz-spacetime-bound`. -/
theorem rieszPressureSpaceTimeComponent_norm_le
    (r : ℝ) (hr : 1 < r) (i j : Fin 3) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    ‖rieszPressureSpaceTimeComponent r hr i j‖ ≤ rieszPressureOperatorBound r hr := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  apply LinearMap.opNorm_extendOfNorm_le
    (denseRange_subtype_val.mpr (rieszPressureSpaceTimeCore_dense r hr))
  · have h := rieszPressureOperator_norm_le r hr i j
    exact le_trans (norm_nonneg _) h
  · intro u
    exact rieszPressureSpaceTimeCoreComponentMap_bound r hr i j u

private theorem rieszPressureSpaceTimeComponent_core_eq
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    (u : RieszPressureSpaceTimeCore r hr) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hr.le⟩
    rieszPressureSpaceTimeComponent r hr i j (u : RieszPressureSpaceTimeLp r) =
      rieszPressureSpaceTimeCoreComponentMap r hr i j u := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  exact LinearMap.extendOfNorm_eq
    (denseRange_subtype_val.mpr (rieszPressureSpaceTimeCore_dense r hr))
    ⟨rieszPressureOperatorBound r hr,
      rieszPressureSpaceTimeCoreComponentMap_bound r hr i j⟩ u

/-- On compactly supported continuous space-time inputs, the space-time
extension is the joint representative constructed slice by slice, consumed
by `def:riesz-pressure`. -/
theorem rieszPressureSpaceTimeComponent_eq_compact
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    rieszPressureSpaceTimeComponent r hr i j
        ((hF.memLp_of_hasCompactSupport hFc).toLp F) =
      rieszPressureComponentCompactClass r hr i j (F := F) hF hFc := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let w : RieszPressureCompactInput := ⟨F, hF, hFc⟩
  let u : RieszPressureSpaceTimeCore r hr :=
    ⟨rieszPressureCompactInputLpClass r hr w, ⟨w, rfl⟩⟩
  calc
    rieszPressureSpaceTimeComponent r hr i j
        ((hF.memLp_of_hasCompactSupport hFc).toLp F) =
      rieszPressureSpaceTimeCoreComponentMap r hr i j u := by
        apply rieszPressureSpaceTimeComponent_core_eq r hr i j u
    _ = rieszPressureComponentCompactClass r hr i j (F := F) hF hFc := by
      exact rieszPressureSpaceTimeCoreComponentValue_eq r hr i j u w rfl

end CKN.Leray

end
