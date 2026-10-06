/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalTimeLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalPairings
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityPotentialLimit

/-!
# Compact-gradient core

Time and weak-gradient cancellations for compact scalar gradient tests.
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

private theorem associatedPressureCompact_decay_bound
    {f : Vec3 × ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (k : ℕ) : ∃ C ≥ 0, ∀ z,
      |f z| ≤ C * (1 + vec3EuclideanNorm z.1) ^ (-(k : ℝ)) := by
  let w : Vec3 × ℝ → ℝ := fun z => |f z| *
    (1 + vec3EuclideanNorm z.1) ^ (k : ℝ)
  have hwc : Continuous w := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hb : Continuous (fun z : Vec3 × ℝ => 1 + vec3EuclideanNorm z.1) :=
      continuous_const.add
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp continuous_fst)
    change Continuous (fun z => |f z| *
      (1 + vec3EuclideanNorm z.1) ^ (k : ℝ))
    exact hf.abs.mul ((Real.continuous_rpow_const hk).comp hb)
  have hwzero : ∀ z ∉ tsupport f, w z = 0 := by
    intro z hz
    simp [w, image_eq_zero_of_notMem_tsupport hz]
  have hwcpt : HasCompactSupport w := HasCompactSupport.intro hfc.isCompact hwzero
  obtain ⟨B, hB⟩ := hwc.bddAbove_range_of_hasCompactSupport hwcpt
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hwBound (z : Vec3 × ℝ) : w z ≤ C :=
    ((mem_upperBounds.mp hB) (w z) (Set.mem_range_self z)).trans
      (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro z
  have hbase : 0 < 1 + vec3EuclideanNorm z.1 :=
    add_pos_of_pos_of_nonneg (by norm_num)
      (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)
  have hpow : 0 < (1 + vec3EuclideanNorm z.1) ^ (k : ℝ) :=
    Real.rpow_pos_of_pos hbase _
  have hratio : |f z| ≤ C / (1 + vec3EuclideanNorm z.1) ^ (k : ℝ) := by
    apply (le_div_iff₀ hpow).2
    simpa [w, mul_comm] using hwBound z
  have hneg : (1 + vec3EuclideanNorm z.1) ^ (-(k : ℝ)) =
      ((1 + vec3EuclideanNorm z.1) ^ (k : ℝ))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hbase), Real.rpow_natCast]
  calc
    |f z| ≤ C / (1 + vec3EuclideanNorm z.1) ^ (k : ℝ) := hratio
    _ = C * (1 + vec3EuclideanNorm z.1) ^ (-(k : ℝ)) := by
      rw [div_eq_mul_inv, hneg]

/-- A smooth compactly supported scalar test satisfies the decay hypotheses
used in the noncompact Riesz duality identity. -/
theorem associatedPressurePotentialDecay_of_compactSupport
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) : RieszPressurePotentialDecay g := by
  let K : Set ℝ := (tsupport g).image Prod.snd
  have hK : IsCompact K := hgc.isCompact.image continuous_snd
  have hzero : ∀ t ∉ K, ∀ x, g (x, t) = 0 := by
    intro t ht x
    have hnot : (x, t) ∉ tsupport g := by
      intro hz
      exact ht ⟨(x, t), hz, rfl⟩
    exact image_eq_zero_of_notMem_tsupport hnot
  have hvalue := associatedPressureCompact_decay_bound hg.continuous hgc 2
  have hgrad (i : Fin 3) := associatedPressureCompact_decay_bound
    (rieszPressureJointDirection_contDiff hg i).continuous
    (by
      have heq : rieszPressureJointDirection g i = CKN.spatialPartialProd g i := by
        funext z
        exact (rieszPressure_sliceSpatialDeriv_eq_joint hg i z).symm
      rw [heq]
      change HasCompactSupport (fun z : Vec3 × ℝ => CKN.spatialPartial g i z)
      exact CKN.hasCompactSupport_spatialPartial hgc i) 3
  have hhess (i j : Fin 3) := associatedPressureCompact_decay_bound
    (rieszPressureJointHessian_contDiff hg i j).continuous
    (rieszPressureJointHessian_hasCompactSupport hgc i j) 4
  obtain ⟨Cv, hCv, hvalue⟩ := hvalue
  choose Cg hCg hgrad using hgrad
  choose Ch hCh hhess using hhess
  have hgradAll : ∃ C ≥ 0, ∀ i z,
      |rieszPressureJointDirection g i z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
    let C : ℝ := ∑ i : Fin 3, Cg i
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => hCg i
    refine ⟨C, hC, ?_⟩
    intro i z
    have hC' : Cg i ≤ C := Finset.single_le_sum
      (fun j _ => hCg j) (Finset.mem_univ i)
    have hnonneg : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
      Real.rpow_nonneg (add_nonneg (by norm_num)
        (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
    exact (hgrad i z).trans (mul_le_mul_of_nonneg_right hC' hnonneg)
  have hhessAll : ∃ C ≥ 0, ∀ i j z,
      |rieszPressureJointHessian g i j z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) := by
    let C : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, Ch i j
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hCh i j
    refine ⟨C, hC, ?_⟩
    intro i j z
    have hCj : Ch i j ≤ ∑ l : Fin 3, Ch i l := Finset.single_le_sum
      (fun l _ => hCh i l) (Finset.mem_univ j)
    have hCi : (∑ l : Fin 3, Ch i l) ≤ C := Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun l _ => hCh k l) (Finset.mem_univ i)
    have hnonneg : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) :=
      Real.rpow_nonneg (add_nonneg (by norm_num)
        (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
    exact (hhess i j z).trans
      (mul_le_mul_of_nonneg_right (hCj.trans hCi) hnonneg)
  exact ⟨⟨K, hK, hzero⟩, ⟨Cv, hCv, hvalue⟩, hgradAll, hhessAll⟩

private theorem associatedPressureSpatialPartialProd_commute
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (CKN.spatialPartialProd g j) i z =
      CKN.spatialPartialProd (CKN.spatialPartialProd g i) j z := by
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, z.2)) :=
    hg.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
  change CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) i j z.1 =
    CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) j i z.1
  exact CKN.mixedSecond_swap hslice i j z.1

/-- The product-coordinate time derivative commutes with a spatial partial
derivative on a smooth scalar test. -/
theorem associatedPressureTimeSpatialPartialProd_commute
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.timePartialProd (CKN.spatialPartialProd g i) z =
      CKN.spatialPartialProd (CKN.timePartialProd g) i z := by
  change CKN.timePartial (fun y => CKN.spatialPartial g i y) z =
    CKN.spatialPartial (fun y => CKN.timePartial g y) i z
  exact timePartial_spatialPartial_comm hg z i

/-- The velocity pairs to zero with the time derivative of a compact smooth
gradient test, by its weak divergence. -/
theorem associatedPressureCompactGradient_timeTerm_zero
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∫ z : Vec3 × ℝ,
      ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
        CKN.timePartialProd (CKN.spatialPartialProd g i) z
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  have htime := associatedPressureWeakDivergence_pairing_zero hLH
    (CKN.contDiff_timePartial hg) (CKN.hasCompactSupport_timePartial hgc)
  calc
    ∫ z : Vec3 × ℝ,
        ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
          CKN.timePartialProd (CKN.spatialPartialProd g i) z
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) =
      ∫ z : Vec3 × ℝ,
        ∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
          CKN.spatialPartialProd (CKN.timePartialProd g) i z
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
        apply integral_congr_ae
        filter_upwards [] with z
        apply Finset.sum_congr rfl
        intro i hi
        rw [associatedPressureTimeSpatialPartialProd_commute hg i z]
    _ = 0 := htime

/-- A third spatial derivative has the coordinate symmetry used in gradient tests. -/
theorem associatedPressureSpatialTriple_commute
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j z =
      CKN.spatialPartialProd (CKN.spatialSecondPartialProd g j j) i z := by
  unfold CKN.spatialSecondPartialProd
  have hfirstFun :
      CKN.spatialPartialProd (CKN.spatialPartialProd g i) j =
        CKN.spatialPartialProd (CKN.spatialPartialProd g j) i := by
    funext w
    exact (associatedPressureSpatialPartialProd_commute hg i j w).symm
  have hgj : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialPartialProd g j) :=
    CKN.spatialPartial_contDiff hg j
  have hsecond := associatedPressureSpatialPartialProd_commute hgj j i z
  calc
    CKN.spatialPartialProd
        (CKN.spatialPartialProd (CKN.spatialPartialProd g i) j) j z =
      CKN.spatialPartialProd
        (CKN.spatialPartialProd (CKN.spatialPartialProd g j) i) j z := by
          rw [hfirstFun]
    _ = CKN.spatialPartialProd
        (CKN.spatialPartialProd (CKN.spatialPartialProd g j) j) i z := by
          exact hsecond

/-- A compact smooth scalar test is square-integrable on a finite time slab. -/
theorem associatedPressureCompact_memLp_two
    {T : ℝ} {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    MemLp f 2 ((volume : Measure Vec3).prod
      (volume.restrict (Ioo 0 T))) := by
  have hglobal : MemLp f 2 (volume : Measure (Vec3 × ℝ)) :=
    hf.continuous.memLp_of_hasCompactSupport hfc
  have hrestrict := hglobal.restrict
    ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
  rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
  simpa using hrestrict

private theorem associatedPressureCompactGradient_third_sum
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 3) (z : Vec3 × ℝ) :
    (∑ j : Fin 3,
      CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j z) =
      CKN.spatialPartialProd (fun q =>
        ∑ j : Fin 3, CKN.spatialSecondPartialProd g j j q) i z := by
  calc
    _ = ∑ j : Fin 3,
        CKN.spatialPartialProd (CKN.spatialSecondPartialProd g j j) i z := by
      apply Finset.sum_congr rfl
      intro j hj
      exact associatedPressureSpatialTriple_commute hg i j z
    _ = CKN.spatialPartialProd (fun q =>
        ∑ j : Fin 3, CKN.spatialSecondPartialProd g j j q) i z := by
      symm
      exact associatedPressureSpatialPartial_finset_sum
        (fun j => CKN.spatialSecondPartialProd g j j)
        (fun j => CKN.spatialPartial_contDiff
          (CKN.spatialPartial_contDiff hg j) j) i z

/-- The weak-gradient terms cancel on a compact smooth scalar gradient test.
This is the viscous cancellation needed when the test is decomposed into its
solenoidal and gradient parts. -/
theorem associatedPressureCompactGradient_viscosity_cancel
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∫ z : Vec3 × ℝ,
      ∑ i : Fin 3, ∑ j : Fin 3,
        Du (parabolicHomeomorph.symm z) i j *
          CKN.spatialSecondPartialProd g i j z
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let L : Vec3 × ℝ → ℝ := fun z =>
    ∑ j : Fin 3, CKN.spatialSecondPartialProd g j j z
  have hU : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2 μ := by
    simpa [μ] using associatedPressureSolution_velocity_memLp_two_productSlab hLH
  have hDu : MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2 μ := by
    simpa [μ] using associatedPressureSolution_gradient_memLp_two_productSlab hLH
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hHsmooth (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialSecondPartialProd g i j) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => CKN.spatialSecondPartial
        (show ParabolicPoint → ℝ from g) i j (z.1, z.2))
    exact CKN.spatialPartial_contDiff
      (CKN.spatialPartial_contDiff hg i) j
  have hHcompact (i j : Fin 3) :
      HasCompactSupport (CKN.spatialSecondPartialProd g i j) := by
    change HasCompactSupport (fun z : Vec3 × ℝ =>
      CKN.spatialSecondPartial (show ParabolicPoint → ℝ from g) i j
        (z.1, z.2))
    exact CKN.hasCompactSupport_spatialPartial
      (CKN.hasCompactSupport_spatialPartial hgc i) j
  have hHmem (i j : Fin 3) : MemLp (CKN.spatialSecondPartialProd g i j) 2 μ := by
    simpa [μ] using associatedPressureCompact_memLp_two (T := T)
      (hHsmooth i j) (hHcompact i j)
  have hDterm (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      Du (parabolicHomeomorph.symm z) i j *
        CKN.spatialSecondPartialProd g i j z) μ := by
    have hDuij : MemLp (fun z : Vec3 × ℝ =>
        Du (parabolicHomeomorph.symm z) i j) 2 μ :=
      (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j
    have hprod : MemLp (fun z : Vec3 × ℝ =>
        Du (parabolicHomeomorph.symm z) i j *
          CKN.spatialSecondPartialProd g i j z) 1 μ := hDuij.mul (hHmem i j)
    exact memLp_one_iff_integrable.mp hprod
  have hThirdsmooth (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j) := by
    exact CKN.spatialPartial_contDiff (hHsmooth i j) j
  have hThirdcompact (i j : Fin 3) :
      HasCompactSupport
        (CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j) := by
    change HasCompactSupport (fun z : Vec3 × ℝ =>
      CKN.spatialPartial (CKN.spatialSecondPartialProd g i j) j z)
    exact CKN.hasCompactSupport_spatialPartial (hHcompact i j) j
  have hThirdmem (i j : Fin 3) :
      MemLp (CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j) 2 μ := by
    simpa [μ] using associatedPressureCompact_memLp_two (T := T)
      (hThirdsmooth i j) (hThirdcompact i j)
  have hUterm (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) i *
        CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j z) μ := by
    have hUi : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z) i) 2 μ :=
      (memLp_pi_iff.mp hU) i
    have hprod : MemLp (fun z : Vec3 × ℝ =>
        u (parabolicHomeomorph.symm z) i *
          CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j z) 1 μ :=
      hUi.mul (hThirdmem i j)
    exact memLp_one_iff_integrable.mp hprod
  have hDivsmooth : ContDiff ℝ (⊤ : ℕ∞) L := by
    dsimp [L]
    apply ContDiff.sum
    intro j hj
    exact hHsmooth j j
  have hDivcompact : HasCompactSupport L := by
    let K : Set (Vec3 × ℝ) := ⋃ j : Fin 3,
      tsupport (CKN.spatialSecondPartialProd g j j)
    have hK : IsCompact K := isCompact_iUnion fun j => (hHcompact j j).isCompact
    have hzero : ∀ z ∉ K, L z = 0 := by
      intro z hz
      dsimp [L]
      apply Finset.sum_eq_zero
      intro j hj
      apply image_eq_zero_of_notMem_tsupport
      intro hzj
      exact hz (Set.mem_iUnion.mpr ⟨j, hzj⟩)
    exact HasCompactSupport.intro hK hzero
  have hdiv := associatedPressureWeakDivergence_pairing_zero hLH
    hDivsmooth hDivcompact
  have hWeak (i j : Fin 3) :=
    associatedPressureWeakGradient_pairing hLH (hHsmooth i j)
      (hHcompact i j) i j
  have hDsum :
      ∫ z : Vec3 × ℝ,
        ∑ i : Fin 3, ∑ j : Fin 3,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd g i j z ∂μ =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd g i j z ∂μ := by
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hDterm i j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (fun j hj => hDterm i j)]
  have hWeakSum :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd g i j z ∂μ) =
      -(∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ,
          u (parabolicHomeomorph.symm z) i *
            CKN.spatialPartialProd
              (CKN.spatialSecondPartialProd g i j) j z ∂μ) := by
    have hweak' (i j : Fin 3) :
        ∫ z : Vec3 × ℝ,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd g i j z ∂μ =
        -∫ z : Vec3 × ℝ,
          u (parabolicHomeomorph.symm z) i *
            CKN.spatialPartialProd
              (CKN.spatialSecondPartialProd g i j) j z ∂μ := by
      simpa [μ] using hWeak i j
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          -(∫ z : Vec3 × ℝ,
            u (parabolicHomeomorph.symm z) i *
              CKN.spatialPartialProd
                (CKN.spatialSecondPartialProd g i j) j z ∂μ) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hweak' i j
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hThirdSum (i : Fin 3) (z : Vec3 × ℝ) :
      ∑ j : Fin 3,
        CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j z =
      CKN.spatialPartialProd L i z := by
    simpa [L] using associatedPressureCompactGradient_third_sum hg i z
  have hUSum :
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ,
          u (parabolicHomeomorph.symm z) i *
            CKN.spatialPartialProd
              (CKN.spatialSecondPartialProd g i j) j z ∂μ = 0 := by
    have hsumIntegrable (i : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
        ∑ j : Fin 3,
          u (parabolicHomeomorph.symm z) i *
            CKN.spatialPartialProd
              (CKN.spatialSecondPartialProd g i j) j z) μ :=
      integrable_finsetSum _ (fun j hj => hUterm i j)
    have hpoint (i : Fin 3) (z : Vec3 × ℝ) :
        (∑ j : Fin 3,
          u (parabolicHomeomorph.symm z) i *
            CKN.spatialPartialProd
              (CKN.spatialSecondPartialProd g i j) j z) =
        u (parabolicHomeomorph.symm z) i * CKN.spatialPartialProd L i z := by
      rw [← Finset.mul_sum, hThirdSum]
    have hcombine (i : Fin 3) :
        (∑ j : Fin 3,
          ∫ z : Vec3 × ℝ,
            u (parabolicHomeomorph.symm z) i *
              CKN.spatialPartialProd
                (CKN.spatialSecondPartialProd g i j) j z ∂μ) =
        ∫ z : Vec3 × ℝ,
          u (parabolicHomeomorph.symm z) i * CKN.spatialPartialProd L i z ∂μ := by
      rw [← integral_finsetSum _ (fun j hj => hUterm i j)]
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint i z
    have hLi (i : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
        u (parabolicHomeomorph.symm z) i * CKN.spatialPartialProd L i z) μ :=
      Integrable.congr (hsumIntegrable i)
        (Filter.Eventually.of_forall fun z => hpoint i z)
    calc
      _ = ∑ i : Fin 3,
          ∫ z : Vec3 × ℝ,
            u (parabolicHomeomorph.symm z) i * CKN.spatialPartialProd L i z ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcombine i
      _ = ∫ z : Vec3 × ℝ, ∑ i : Fin 3,
          u (parabolicHomeomorph.symm z) i * CKN.spatialPartialProd L i z ∂μ := by
        rw [integral_finsetSum _ (fun i hi => hLi i)]
      _ = 0 := hdiv
  calc
    ∫ z : Vec3 × ℝ,
        ∑ i : Fin 3, ∑ j : Fin 3,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd g i j z ∂μ =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd g i j z ∂μ := hDsum
    _ = 0 := by rw [hWeakSum, hUSum]; simp

end CKN.Leray

end
