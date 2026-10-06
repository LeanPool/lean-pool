/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalCore

/-!
# Weak pairings for Leray solutions

Space-time integrability and weak derivative pairings used in the pressure identity.
-/

public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal
open scoped Convolution
open scoped Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

private theorem associatedPressureSolution_velocity_memLp_two_product
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹'
          spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  rcases hLH with ⟨hT, ha, huMeas, hDuMeas, hSliceTop, hJointTop,
    hWeakGrad, hWeakDiv, hTrace, hMomentum, hEnergy, hInitial⟩
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have huFinite : (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply lt_of_le_of_lt _ hJointTop
    apply lintegral_mono
    intro z
    exact le_add_of_nonneg_right (by positivity)
  have hu2 : MemLp u 2 (volume.restrict Q) :=
    associatedPressure_memLp_two_of_lintegral_lt_top huMeas huFinite
  have hQmeas : MeasurableSet Q := by
    dsimp [Q, spaceTimeSet]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hMap : MeasurePreserving parabolicHomeomorph.symm
      (volume.restrict (parabolicHomeomorph.symm ⁻¹' Q))
      (volume.restrict Q) :=
    parabolicHomeomorphSymm_measurePreserving.restrict_preimage hQmeas
  have hMapProd : MeasurePreserving parabolicHomeomorph.symm
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹' Q)) (volume.restrict Q) := by
    rw [← Measure.volume_eq_prod Vec3 ℝ]
    exact hMap
  have hcomp := hu2.comp_measurePreserving hMapProd
  change MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (parabolicHomeomorph.symm ⁻¹' Q)) at hcomp
  exact hcomp

private theorem associatedPressureSolution_gradient_memLp_two_product
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹'
          spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  rcases hLH with ⟨hT, ha, huMeas, hDuMeas, hSliceTop, hJointTop,
    hWeakGrad, hWeakDiv, hTrace, hMomentum, hEnergy, hInitial⟩
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have hDuFinite : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply lt_of_le_of_lt _ hJointTop
    apply lintegral_mono
    intro z
    exact le_add_left le_rfl
  have hDu2 : MemLp Du 2 (volume.restrict Q) :=
    associatedPressure_memLp_two_of_lintegral_lt_top hDuMeas hDuFinite
  have hQmeas : MeasurableSet Q := by
    dsimp [Q, spaceTimeSet]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hMap : MeasurePreserving parabolicHomeomorph.symm
      (volume.restrict (parabolicHomeomorph.symm ⁻¹' Q))
      (volume.restrict Q) :=
    parabolicHomeomorphSymm_measurePreserving.restrict_preimage hQmeas
  have hMapProd : MeasurePreserving parabolicHomeomorph.symm
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹' Q)) (volume.restrict Q) := by
    rw [← Measure.volume_eq_prod Vec3 ℝ]
    exact hMap
  have hcomp := hDu2.comp_measurePreserving hMapProd
  change MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (parabolicHomeomorph.symm ⁻¹' Q)) at hcomp
  exact hcomp

private theorem associatedPressureTensor_memLp_fiveThirds_product
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) (i j : Fin 3) :
    MemLp (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j)
      (ENNReal.ofReal (5 / 3 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹'
          spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let Q' := parabolicHomeomorph.symm ⁻¹' Q
  have hQmeas : MeasurableSet Q := by
    dsimp [Q, spaceTimeSet]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hQ'meas : MeasurableSet Q' := hQmeas.preimage
    parabolicHomeomorph.symm.measurable
  have hbase := associatedPressureTensor_memLp_fiveThirds hLH i j
  have hrestricted := hbase.restrict Q'
  apply (memLp_congr_ae ?_).2 hrestricted
  filter_upwards [ae_restrict_mem hQ'meas] with z hz
  have hz' : z ∈ parabolicHomeomorph.symm ⁻¹'
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    simpa [Q, Q'] using hz
  simp [associatedPressureTensor, hz']

/-- The velocity has finite space-time energy on the ordinary product-space
time slab. -/
theorem associatedPressureSolution_velocity_memLp_two_productSlab
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  have h := associatedPressureSolution_velocity_memLp_two_product hLH
  have hset : parabolicHomeomorph.symm ⁻¹'
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) =
        ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) := by
    ext z
    change ((parabolicHomeomorph.symm z).1 ∈ Set.univ ∧
      (parabolicHomeomorph.symm z).2 ∈ Ioo 0 T) ↔ z ∈ Set.univ ×ˢ Ioo 0 T
    simp
  rw [hset, ← Measure.prod_restrict] at h
  simpa using h

/-- The weak gradient has finite space-time energy on the ordinary
product-space time slab. -/
theorem associatedPressureSolution_gradient_memLp_two_productSlab
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  have h := associatedPressureSolution_gradient_memLp_two_product hLH
  have hset : parabolicHomeomorph.symm ⁻¹'
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) =
        ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) := by
    ext z
    change ((parabolicHomeomorph.symm z).1 ∈ Set.univ ∧
      (parabolicHomeomorph.symm z).2 ∈ Ioo 0 T) ↔ z ∈ Set.univ ×ˢ Ioo 0 T
    simp
  rw [hset, ← Measure.prod_restrict] at h
  simpa using h

@[expose]
def associatedPressureScalarSliceWeakTest
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (t : ℝ) :
    CKN.WeakTestFunction (Set.univ : Set Vec3) := by
  let K : Set Vec3 := (tsupport g).image Prod.fst
  have hK : IsCompact K := hgc.isCompact.image continuous_fst
  have hgSlice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) :=
    hg.comp (contDiff_id.prodMk contDiff_const)
  have hKzero : ∀ x ∉ K, g (x, t) = 0 := by
    intro x hx
    have hnot : (x, t) ∉ tsupport g := by
      intro hmem
      exact hx ⟨(x, t), hmem, rfl⟩
    exact image_eq_zero_of_notMem_tsupport hnot
  have hgcSlice : HasCompactSupport (fun x : Vec3 => g (x, t)) :=
    HasCompactSupport.of_support_subset_isCompact hK (by
      intro x hx
      have hx' : (x, t) ∈ Function.support g := by
        change g (x, t) ≠ 0
        exact Function.mem_support.mp hx
      exact ⟨(x, t), (subset_tsupport (f := g)) hx', rfl⟩)
  exact ⟨fun x => g (x, t), hgSlice, hgcSlice, Set.subset_univ _⟩

/-- The Leray weak-divergence clause pairs to zero with any compact smooth
scalar test on the finite-time slab. -/
theorem associatedPressureWeakDivergence_pairing_zero
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∫ z : Vec3 × ℝ,
      ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
        CKN.spatialPartialProd g i z
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  rcases hLH with ⟨hT, ha, huMeas, hDuMeas, hSliceTop, hJointTop,
    hWeakGrad, hWeakDiv, hTrace, hMomentum, hEnergy, hInitial⟩
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let F : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i * CKN.spatialPartialProd g i z
  have hU : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2 μ := by
    simpa [μ] using associatedPressureSolution_velocity_memLp_two_productSlab
      (T := T) (a := a) (u := u) (Du := Du) ⟨hT, ha, huMeas, hDuMeas,
        hSliceTop, hJointTop, hWeakGrad, hWeakDiv, hTrace, hMomentum, hEnergy, hInitial⟩
  have hGrad (i : Fin 3) : MemLp (CKN.spatialPartialProd g i) 2 μ := by
    have hglobal : MemLp (CKN.spatialPartialProd g i) 2
        (volume : Measure (Vec3 × ℝ)) := by
      change MemLp (fun z : Vec3 × ℝ => CKN.spatialPartial g i z) 2 _
      have hcont : Continuous (fun z : Vec3 × ℝ => CKN.spatialPartial g i z) :=
        (CKN.spatialPartial_contDiff hg i).continuous
      have hcompact := CKN.hasCompactSupport_spatialPartial hgc i
      simpa [CKN.spatialPartialProd] using hcont.memLp_of_hasCompactSupport hcompact
    have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
    simpa [μ] using hrestrict
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 := ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hFint : Integrable F μ := by
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro i hi
    have hUi : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i) 2 μ :=
      (memLp_pi_iff.mp hU) i
    have hterm : MemLp
        (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i *
          CKN.spatialPartialProd g i z) 1 μ := hUi.mul (hGrad i)
    exact memLp_one_iff_integrable.mp (by simpa [F] using hterm)
  have hEq :
      ∫ z : Vec3 × ℝ, F z ∂μ =
        ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
    calc
      ∫ z : Vec3 × ℝ, F z ∂μ =
          ∫ z : ℝ × Vec3, F z.swap
            ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
        simpa [μ, Function.comp_def] using
          (MeasureTheory.integral_prod_swap (μ := (volume : Measure Vec3))
            (ν := volume.restrict (Ioo 0 T)) F).symm
      _ = ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
        simpa using MeasureTheory.integral_prod
          (fun z : ℝ × Vec3 => F z.swap) hFint.swap
  have hzeroSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫ x : Vec3, F (x, t) ∂volume = 0 := by
    filter_upwards [hWeakDiv] with t ht
    let htest := associatedPressureScalarSliceWeakTest hg hgc t
    have hzero := ht htest
    have htestFun : htest.toFun = fun x : Vec3 => g (x, t) := rfl
    have hpartial (i : Fin 3) (x : Vec3) :
        htest.partialDeriv i x = CKN.spatialPartialProd g i (x, t) := by
      rfl
    have hfun : (fun x : Vec3 => F (x, t)) =
        (fun x => ∑ i : Fin 3, u (x, t) i * htest.partialDeriv i x) := by
      funext x
      simp [F, hpartial, parabolicHomeomorph_symm_apply]
    rw [hfun]
    exact hzero
  rw [hEq]
  rw [integral_congr_ae hzeroSlice]
  simp

/-- The Leray weak-gradient clause gives the distributional integration by
parts formula against any compact smooth scalar test on the finite-time
slab. -/
theorem associatedPressureWeakGradient_pairing
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (i j : Fin 3) :
    ∫ z : Vec3 × ℝ,
      Du (parabolicHomeomorph.symm z) i j * g z
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) =
      -∫ z : Vec3 × ℝ,
        u (parabolicHomeomorph.symm z) i * CKN.spatialPartialProd g j z
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  rcases hLH with ⟨hT, ha, huMeas, hDuMeas, hSliceTop, hJointTop,
    hWeakGrad, hWeakDiv, hTrace, hMomentum, hEnergy, hInitial⟩
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let F : Vec3 × ℝ → ℝ := fun z =>
    Du (parabolicHomeomorph.symm z) i j * g z
  let G : Vec3 × ℝ → ℝ := fun z =>
    u (parabolicHomeomorph.symm z) i * CKN.spatialPartialProd g j z
  have hU : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2 μ := by
    simpa [μ] using associatedPressureSolution_velocity_memLp_two_productSlab
      (T := T) (a := a) (u := u) (Du := Du) ⟨hT, ha, huMeas, hDuMeas,
        hSliceTop, hJointTop, hWeakGrad, hWeakDiv, hTrace, hMomentum, hEnergy, hInitial⟩
  have hDu : MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2 μ := by
    simpa [μ] using associatedPressureSolution_gradient_memLp_two_productSlab
      (T := T) (a := a) (u := u) (Du := Du) ⟨hT, ha, huMeas, hDuMeas,
        hSliceTop, hJointTop, hWeakGrad, hWeakDiv, hTrace, hMomentum, hEnergy, hInitial⟩
  have hsp : MemLp (CKN.spatialPartialProd g j) 2 μ := by
    have hglobal : MemLp (CKN.spatialPartialProd g j) 2
        (volume : Measure (Vec3 × ℝ)) := by
      change MemLp (fun z : Vec3 × ℝ => CKN.spatialPartial g j z) 2 _
      have hcont : Continuous (fun z : Vec3 × ℝ => CKN.spatialPartial g j z) :=
        (CKN.spatialPartial_contDiff hg j).continuous
      have hcompact := CKN.hasCompactSupport_spatialPartial hgc j
      simpa [CKN.spatialPartialProd] using hcont.memLp_of_hasCompactSupport hcompact
    have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
    simpa [μ] using hrestrict
  have hgLp : MemLp g 2 μ := by
    have hglobal : MemLp g 2 (volume : Measure (Vec3 × ℝ)) :=
      hg.continuous.memLp_of_hasCompactSupport hgc
    have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
    simpa [μ] using hrestrict
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 := ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hFint : Integrable F μ := by
    have hDuij : MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z) i j)
        2 μ := (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j
    have hterm : MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z) i j * g z)
        1 μ := hDuij.mul hgLp
    exact memLp_one_iff_integrable.mp (by simpa [F] using hterm)
  have hGint : Integrable G μ := by
    have hterm : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i *
        CKN.spatialPartialProd g j z) 1 μ := ((memLp_pi_iff.mp hU) i).mul hsp
    exact memLp_one_iff_integrable.mp (by simpa [G] using hterm)
  have hFEq : ∫ z : Vec3 × ℝ, F z ∂μ =
      ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
        ∂(volume.restrict (Ioo 0 T)) := by
    calc
      ∫ z : Vec3 × ℝ, F z ∂μ =
          ∫ z : ℝ × Vec3, F z.swap
            ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
        simpa [μ, Function.comp_def] using
          (MeasureTheory.integral_prod_swap (μ := (volume : Measure Vec3))
            (ν := volume.restrict (Ioo 0 T)) F).symm
      _ = ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
        simpa using MeasureTheory.integral_prod
          (fun z : ℝ × Vec3 => F z.swap) hFint.swap
  have hGEq : ∫ z : Vec3 × ℝ, G z ∂μ =
      ∫ t : ℝ, ∫ x : Vec3, G (x, t) ∂volume
        ∂(volume.restrict (Ioo 0 T)) := by
    calc
      ∫ z : Vec3 × ℝ, G z ∂μ =
          ∫ z : ℝ × Vec3, G z.swap
            ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
        simpa [μ, Function.comp_def] using
          (MeasureTheory.integral_prod_swap (μ := (volume : Measure Vec3))
            (ν := volume.restrict (Ioo 0 T)) G).symm
      _ = ∫ t : ℝ, ∫ x : Vec3, G (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
        simpa using MeasureTheory.integral_prod
          (fun z : ℝ × Vec3 => G z.swap) hGint.swap
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫ x : Vec3, F (x, t) ∂volume = -∫ x : Vec3, G (x, t) ∂volume := by
    filter_upwards [hWeakGrad] with t ht
    let htest := associatedPressureScalarSliceWeakTest hg hgc t
    have hweak : HasWeakPartialDerivOn (Set.univ : Set Vec3) j
        (fun x => u (x, t) i) (fun x => Du (x, t) i j) := by
      exact (ht i) j
    have hpair := (hasWeakPartialDerivOn_iff_forall_testFunction.mp hweak) htest
    have htestFun : htest.toFun = fun x : Vec3 => g (x, t) := rfl
    have hpartial (x : Vec3) : htest.partialDeriv j x =
        CKN.spatialPartialProd g j (x, t) := by
      rfl
    have hpair' : ∫ x : Vec3, G (x, t) ∂volume =
        -∫ x : Vec3, F (x, t) ∂volume := by
      simpa [F, G, htestFun, hpartial, parabolicHomeomorph_symm_apply] using hpair
    linarith only [hpair']
  rw [hFEq, hGEq]
  rw [integral_congr_ae hslice]
  rw [integral_neg]

end CKN.Leray

end
