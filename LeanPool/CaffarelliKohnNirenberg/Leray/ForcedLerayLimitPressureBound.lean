/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedPressureLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitTransport
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Uniform bounds for the forced quadratic pressure

`eq:forced-pressure-bounds` in `lem:forced-energy-bounds`, in the `L^{3/2}`
form used on finite slabs: the quadratic part `p_ε − p_f` of the forced
regularized pressure is the space-time Riesz pressure of `J_ε u_ε ⊗ u_ε` on
the slab (`prop:leray-pressure-limit`), so the space-time Riesz bound
`eq:riesz-spacetime-bound` and Hölder's inequality bound it by the `L³` norms
of the transport velocity and of the velocity. The `L³` norm of the velocity
is itself bounded by interpolation between `L²` and `L^{10/3}`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

local instance forcedLerayLimit_holder_three_three_threeHalves :
    ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (ENNReal.ofReal (3 / 2 : ℝ)) := by
  have hreal : Real.HolderTriple 3 3 (3 / 2) := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using hreal.ennrealOfReal

/-- `eq:riesz-spacetime-bound` for the product pressure on a finite slab:
its `L^{3/2}` norm is at most the Riesz constant times the sum of the products
of the `L³` norms of the components of the two factors. -/
theorem forcedLerayLimit_productPressure_eLpNorm_le
    (T : ℝ) (v w : Vec3 × ℝ → Vec3)
    (hv : MemLp v 3 ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (hw : MemLp w 3 ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))) :
    eLpNorm (lerayProductPressureOnSlab T v w hv hw) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num)) *
        ∑ i : Fin 3, ∑ j : Fin 3,
          eLpNorm (fun z => v z i) 3
              ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) *
            eLpNorm (fun z => w z j) 3
              ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) := by
  have : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)⟩
  let S : Set (Vec3 × ℝ) := lerayPressureLimitSlab T
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioo
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => S.indicator (fun z => v z i * w z j)
  let hF := rieszPressureSpaceTime_product_memLp_of_slab hS v w
    (fun i => hv.eval i) (fun j => hw.eval j)
  let cls := rieszPressureSpaceTimeClass (3 / 2 : ℝ) (by norm_num)
    (rieszPressureSpaceTimeTensorToLp (3 / 2 : ℝ) (by norm_num) F hF)
  have hrep : lerayProductPressureOnSlab T v w hv hw =ᵐ[volume] (cls : Vec3 × ℝ → ℝ) :=
    (Lp.aestronglyMeasurable cls).aemeasurable.ae_eq_mk.symm
  have hbound := rieszPressureSpaceTime_bound (3 / 2 : ℝ) (by norm_num) F hF
  have hcomp (i j : Fin 3) : eLpNorm (F i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      eLpNorm (fun z => v z i) 3 ((volume : Measure (Vec3 × ℝ)).restrict S) *
        eLpNorm (fun z => w z j) 3 ((volume : Measure (Vec3 × ℝ)).restrict S) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hS]
    exact eLpNorm_smul_le_mul_eLpNorm (φ := fun z => v z i) (f := fun z => w z j)
      (hv.eval i).aestronglyMeasurable (hw.eval j).aestronglyMeasurable
  have hfin (i j : Fin 3) : eLpNorm (F i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≠ ⊤ :=
    (hF i j).eLpNorm_ne_top
  have hnorm : eLpNorm (cls : Vec3 × ℝ → ℝ) (ENNReal.ofReal (3 / 2 : ℝ)) volume =
      ENNReal.ofReal ‖cls‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top cls)]
  have hsum0 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖(hF i j).toLp (F i j)‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  rw [eLpNorm_congr_ae hrep, hnorm]
  calc ENNReal.ofReal ‖cls‖
      ≤ ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖(hF i j).toLp (F i j)‖) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num)) *
          ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (F i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
        rw [ENNReal.ofReal_mul' hsum0,
          ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => norm_nonneg _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Lp.norm_toLp, ENNReal.ofReal_toReal (hfin i j)]
    _ ≤ _ := by
        gcongr with i _ j _
        exact hcomp i j

/-- The `L³` interpolation inequality between `L²` and `L^{10/3}`, in integral
form: `∫|g|³ ≤ (∫|g|²)^{1/4} (∫|g|^{10/3})^{3/4}`. -/
theorem forcedLerayLimit_lintegral_cube_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : AEMeasurable g μ) :
    ∫⁻ x, ‖g x‖ₑ ^ (3 : ℝ) ∂μ ≤
      (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 4 : ℝ) *
        (∫⁻ x, ‖g x‖ₑ ^ (10 / 3 : ℝ) ∂μ) ^ (3 / 4 : ℝ) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3) := ⟨by norm_num, by norm_num, by norm_num⟩
  have hm : AEMeasurable (fun x => ‖g x‖ₑ) μ := hg.enorm
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (hm.pow_const (1 / 2 : ℝ))
    (hm.pow_const (5 / 2 : ℝ))
  have hprod : ∀ x, ((fun x => ‖g x‖ₑ ^ (1 / 2 : ℝ)) * fun x => ‖g x‖ₑ ^ (5 / 2 : ℝ)) x =
      ‖g x‖ₑ ^ (3 : ℝ) := fun x => by
    simp only [Pi.mul_apply]
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hf4 : ∀ x, (‖g x‖ₑ ^ (1 / 2 : ℝ)) ^ (4 : ℝ) = ‖g x‖ₑ ^ (2 : ℝ) := fun x => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hg43 : ∀ x, (‖g x‖ₑ ^ (5 / 2 : ℝ)) ^ (4 / 3 : ℝ) = ‖g x‖ₑ ^ (10 / 3 : ℝ) := fun x => by
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [hprod, hf4, hg43] at h
  convert h using 3
  norm_num

/-- Uniform slab bounds for the forced regularized solutions: on every finite
slab the `L³` norms of the velocity components and of the transport velocity
components, and the `L^{3/2}` norm of the quadratic pressure, are bounded
independently of `ε` (`lem:forced-energy-bounds`). -/
theorem forcedLerayLimit_uniform_slab_bounds
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (T : ℝ) (hT : 0 < T) :
    ∃ M3 MJ MP : ℝ≥0∞, M3 < ⊤ ∧ MJ < ⊤ ∧ MP < ⊤ ∧ ∀ (ε : ℝ) (hε : 0 < ε),
      (∀ j : Fin 3, eLpNorm (fun z : ParabolicPoint => forcedRegVelocity ρ a ha f hf ε z j) 3
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ M3) ∧
      (∀ i : Fin 3, eLpNorm (fun z : ParabolicPoint =>
          regUniformMollifiedVelocity ρ ε hε (forcedRegVelocity ρ a ha f hf ε) z i) 3
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ MJ) ∧
      eLpNorm (fun z : Vec3 × ℝ =>
          forcedRegPressure ρ a ha f hf ε (parabolicHomeomorph.symm z) -
            forcePressure f hf (parabolicHomeomorph.symm z)) (ENNReal.ofReal (3 / 2 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) ≤ MP := by
  let E : ℝ := Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
    ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2)
  let G : ℝ := ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
    (∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2) +
    T * E) / 2
  let B : ℝ≥0∞ := (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) *
    ENNReal.ofReal (Real.sqrt E) ^ (4 / 3 : ℝ) * ENNReal.ofReal G
  let M3 : ℝ≥0∞ := ((ENNReal.ofReal E * ENNReal.ofReal T) ^ (1 / 4 : ℝ) *
    B ^ (3 / 4 : ℝ)) ^ (1 / 3 : ℝ)
  let MJ : ℝ≥0∞ := (9 * (3 * M3 ^ (3 : ℝ))) ^ (1 / 3 : ℝ)
  let MP : ℝ≥0∞ := ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num)) *
    (9 * (MJ * M3))
  have hGN : (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      gagliardoNirenbergSobolevConstant_ne_top).ne
  have hB : B < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hGN
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)) ENNReal.ofReal_lt_top
  have hM3 : M3 < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne)).ne
  have hMJ : MJ < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top (by norm_num)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM3.ne))).ne
  have hMP : MP < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top hMJ hM3))
  refine ⟨M3, MJ, MP, hM3, hMJ, hMP, fun ε hε => ?_⟩
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  let U := forcedRegVelocity ρ a ha f hf ε
  have hc := forcedRegularised ρ a ha f hf ε hε
  obtain ⟨⟨hSlice, hcont, -, -⟩, -, hR2, hR4, hE⟩ := hc
  have hUs : StronglyMeasurable U := by
    change StronglyMeasurable (forcedRegVelocity ρ a ha f hf ε)
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact forcedRegRep_stronglyMeasurable ρ ε hε ha hf
  have hSliceAll : ∀ t : ℝ, MemLp (fun x : Vec3 => U (x, t)) 2 volume := by
    intro t
    change MemLp (fun x : Vec3 => forcedRegVelocity ρ a ha f hf ε (x, t)) 2 volume
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact forcedRegRep_memLp ρ ε hε ha hf t
  obtain ⟨hU2, -, hU3, hU103⟩ := forcedRegVelocity_memLp_slab ρ a ha f hf ε hε T hT
  have hu2 : ∀ S : ℝ, 0 < S →
      MemLp U 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 S))) := fun S hS =>
    (forcedRegVelocity_memLp_slab ρ a ha f hf ε hε S hS).1
  obtain ⟨hkin, -⟩ := forcedLerayLimit_energy_bounds ρ ε hε a ha.1 f hf U _ hSlice hcont
    hu2 (fun S hS => (hR2 S hS).1) (fun t ht => (hE t ht).2) T hT
  -- the velocity components in `L³`
  have hUj : ∀ j : Fin 3, eLpNorm (fun z : ParabolicPoint => U z j) 3 μ ≤ M3 := by
    intro j
    have hjm : Measurable fun z : ParabolicPoint => U z j :=
      (measurable_pi_apply j).comp hUs.measurable
    have h2 : ∫⁻ z, ‖U z j‖ₑ ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal E * ENNReal.ofReal T := by
      have hslice : ∀ t ∈ Ioo (0 : ℝ) T, ∫⁻ x : Vec3, ‖U (x, t) j‖ₑ ^ (2 : ℝ) ≤
          ENNReal.ofReal E := by
        intro t ht
        have hmem := (hSlice t ht.1.le).eval j
        rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 2),
          ← ENNReal.toReal_ofNat 2,
          ← eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmem.aestronglyMeasurable,
          vorticity_eLpNorm_two_eq_sqrt hmem, ENNReal.toReal_ofNat,
          ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
        refine le_trans ?_ (hkin t ⟨ht.1.le, ht.2.le⟩)
        exact Finset.single_le_sum (f := fun j : Fin 3 => ∫ x : Vec3, U (x, t) j ^ 2)
          (fun j _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ j)
      have hmeas : Measurable fun z : Vec3 × ℝ => ‖U z j‖ₑ ^ (2 : ℝ) :=
        hjm.enorm.pow_const _
      calc ∫⁻ z, ‖U z j‖ₑ ^ (2 : ℝ) ∂μ
          = ∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x : Vec3, ‖U (x, t) j‖ₑ ^ (2 : ℝ) :=
            (lintegral_slab_eq_prod _ (Ioo 0 T)).trans
              (lintegral_prod_symm _ hmeas.aemeasurable)
        _ ≤ ∫⁻ _t in Ioo (0 : ℝ) T, ENNReal.ofReal E :=
            setLIntegral_mono' measurableSet_Ioo hslice
        _ = ENNReal.ofReal E * ENNReal.ofReal T := by
            rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
    have h103 : ∫⁻ z, ‖U z j‖ₑ ^ (10 / 3 : ℝ) ∂μ ≤ B := by
      have hb := hU103 j
      rw [eLpNorm_eq_eLpNorm' (by norm_num) ENNReal.ofReal_ne_top hjm.aestronglyMeasurable,
        ENNReal.toReal_ofReal (by norm_num), eLpNorm'_eq_lintegral_enorm,
        ← ENNReal.rpow_mul] at hb
      simpa using hb
    have h3 := forcedLerayLimit_lintegral_cube_le (μ := μ) hjm.aemeasurable
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hjm.aestronglyMeasurable,
      ENNReal.toReal_ofNat,
      eLpNorm'_eq_lintegral_enorm]
    refine ENNReal.rpow_le_rpow (h3.trans ?_) (by norm_num)
    gcongr
  let J := regUniformMollifiedVelocity ρ ε hε U
  have hJi : ∀ i : Fin 3, eLpNorm (fun z : ParabolicPoint => J z i) 3 μ ≤ MJ := by
    intro i
    have ht := forcedLerayLimit_transport_eLpNorm_le ρ ε hε U hUs hSliceAll (p := 3)
      (by norm_num) (by norm_num) (Ioo 0 T) i
    simp only [ENNReal.toReal_ofNat] at ht
    have hsum : ∑ j : Fin 3, eLpNorm (fun z : ParabolicPoint => U z j) 3 μ ^ (3 : ℝ) ≤
        3 * M3 ^ (3 : ℝ) := by
      calc ∑ j : Fin 3, eLpNorm (fun z : ParabolicPoint => U z j) 3 μ ^ (3 : ℝ)
          ≤ ∑ _j : Fin 3, M3 ^ (3 : ℝ) :=
            Finset.sum_le_sum fun j _ => ENNReal.rpow_le_rpow (hUj j) (by norm_num)
        _ = 3 * M3 ^ (3 : ℝ) := by simp
    have h9 : (3 : ℝ≥0∞) ^ ((3 : ℝ) - 1) = 9 := by
      rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      norm_num
    rw [h9] at ht
    have hcube : eLpNorm (fun z : ParabolicPoint => J z i) 3 μ ^ (3 : ℝ) ≤ 9 * (3 * M3 ^ (3 : ℝ)) :=
      ht.trans (by gcongr)
    have hroot := ENNReal.rpow_le_rpow hcube (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← ENNReal.rpow_mul, show (3 : ℝ) * (1 / 3) = 1 by norm_num, ENNReal.rpow_one] at hroot
    exact hroot
  refine ⟨hUj, hJi, ?_⟩
  -- the quadratic pressure
  have hSmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) =
      lerayPressureLimitSlab T := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
  rw [hpre] at hmp
  have hJ3 : MemLp J 3 μ := memLp_pi_iff.2 fun i => (hJi i).trans_lt hMJ
  have hUprod : MemLp (fun z : Vec3 × ℝ => U (parabolicHomeomorph.symm z)) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) :=
    hU3.comp_measurePreserving hmp
  have hJprod : MemLp (fun z : Vec3 × ℝ => J (parabolicHomeomorph.symm z)) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) :=
    hJ3.comp_measurePreserving hmp
  have hmeas : AEStronglyMeasurable (fun z : Vec3 × ℝ =>
      forcedRegPressure ρ a ha f hf ε (parabolicHomeomorph.symm z) -
        forcePressure f hf (parabolicHomeomorph.symm z))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) :=
    ((hR2 T hT).2.comp_measurePreserving hmp).aestronglyMeasurable
  have hactual := forcedPressureLimit_quadratic_eq_product
    (fun z => forcedRegPressure ρ a ha f hf ε z - forcePressure f hf z) U J T hmeas
    (fun t ht => ⟨(hR4 t ht).choose, (hR4 t ht).choose_spec.1⟩) hUprod hJprod
  have hcompU (j : Fin 3) : eLpNorm (fun z : Vec3 × ℝ => U (parabolicHomeomorph.symm z) j) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) =
      eLpNorm (fun z : ParabolicPoint => U z j) 3 μ :=
    eLpNorm_comp_measurePreserving (hU3.eval j).aestronglyMeasurable hmp
  have hcompJ (i : Fin 3) : eLpNorm (fun z : Vec3 × ℝ => J (parabolicHomeomorph.symm z) i) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) =
      eLpNorm (fun z : ParabolicPoint => J z i) 3 μ :=
    eLpNorm_comp_measurePreserving (hJ3.eval i).aestronglyMeasurable hmp
  rw [eLpNorm_congr_ae hactual]
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
    ((forcedLerayLimit_productPressure_eLpNorm_le T _ _ hJprod hUprod).trans ?_)
  refine mul_le_mul' le_rfl ?_
  calc ∑ i : Fin 3, ∑ j : Fin 3,
        eLpNorm (fun z : Vec3 × ℝ => J (parabolicHomeomorph.symm z) i) 3
            ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) *
          eLpNorm (fun z : Vec3 × ℝ => U (parabolicHomeomorph.symm z) j) 3
            ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))
      ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, MJ * M3 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [hcompJ i, hcompU j]
        exact mul_le_mul' (hJi i) (hUj j)
    _ = 9 * (MJ * M3) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
        ring
/-- The transport velocity `J_ε u_ε` of a forced regularized solution lies in
`L³` on every finite slab (`lem:forced-energy-bounds`). -/
theorem forcedRegTransport_memLp_three_slab
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 < T) :
    MemLp (regUniformMollifiedVelocity ρ ε hε (forcedRegVelocity ρ a ha f hf ε)) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  obtain ⟨M3, MJ, MP, -, hMJ, -, hunif⟩ := forcedLerayLimit_uniform_slab_bounds ρ a ha f hf T hT
  exact memLp_pi_iff.2 fun i => ((hunif ε hε).2.1 i).trans_lt hMJ

end CKN.Leray

end
