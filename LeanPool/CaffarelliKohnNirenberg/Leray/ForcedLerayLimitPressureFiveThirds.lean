/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPressureBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageAgreement
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# The `L^{5/3}` bound for the forced quadratic pressure

`eq:forced-ten-thirds` and `eq:forced-pressure-bounds` in
`lem:forced-energy-bounds`, in the `L^{5/3}` form: the transport velocity
`J_ε u_ε` of a forced regularized solution obeys the same uniform
`L^{10/3}` bound on finite slabs as the velocity (Young's inequality for the
mollifier), so the quadratic tensor `J_ε u_ε ⊗ u_ε` is uniformly in `L^{5/3}`
on the slab, and the `L^{5/3}` space-time Riesz bound of
`def:riesz-pressure` gives a uniform `L^{5/3}` bound for the quadratic
pressure `p_ε − p_f`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private instance forcedPressureFiveThirdsHolder :
    ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ)) (ENNReal.ofReal (10 / 3 : ℝ))
      (ENNReal.ofReal (5 / 3 : ℝ)) := by
  have hreal : Real.HolderTriple (10 / 3) (10 / 3) (5 / 3) :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  exact hreal.ennrealOfReal

/-- `eq:riesz-spacetime-bound` in `L^{5/3}` for the product pressure on a
finite slab: when both factors are in `L^{10/3}` on the slab, the product
pressure is bounded in `L^{5/3}` by the Riesz constant times the products of
the `L^{10/3}` norms of the components. -/
theorem forcedLerayLimit_productPressure_eLpNorm_fiveThirds_le
    (T : ℝ) (v w : Vec3 × ℝ → Vec3)
    (hv : MemLp v 3 ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (hw : MemLp w 3 ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (hv' : ∀ i, MemLp (fun z => v z i) (ENNReal.ofReal (10 / 3 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (hw' : ∀ j, MemLp (fun z => w z j) (ENNReal.ofReal (10 / 3 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))) :
    eLpNorm (lerayProductPressureOnSlab T v w hv hw) (ENNReal.ofReal (5 / 3 : ℝ)) volume ≤
      ENNReal.ofReal (rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num)) *
        ∑ i : Fin 3, ∑ j : Fin 3,
          eLpNorm (fun z => v z i) (ENNReal.ofReal (10 / 3 : ℝ))
              ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) *
            eLpNorm (fun z => w z j) (ENNReal.ofReal (10 / 3 : ℝ))
              ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) := by
  have : Fact (1 ≤ ENNReal.ofReal (5 / 3 : ℝ)) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)⟩
  let S : Set (Vec3 × ℝ) := lerayPressureLimitSlab T
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioo
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => S.indicator (fun z => v z i * w z j)
  have hF32 := rieszPressureSpaceTime_product_memLp_of_slab hS v w
    (fun i => hv.eval i) (fun j => hw.eval j)
  have hF53 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (5 / 3 : ℝ)) volume := by
    intro i j
    rw [memLp_indicator_iff_restrict hS]
    exact (hv' i).mul (hw' j)
  have hagree := rieszPressureSpaceTime_ae_eq_of_memLp_common (3 / 2 : ℝ) (by norm_num)
    (5 / 3 : ℝ) (by norm_num) F hF32 hF53
  let cls := rieszPressureSpaceTimeClass (5 / 3 : ℝ) (by norm_num)
    (rieszPressureSpaceTimeTensorToLp (5 / 3 : ℝ) (by norm_num) F hF53)
  have hrep : rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num) F hF53 =ᵐ[volume]
      (cls : Vec3 × ℝ → ℝ) :=
    (Lp.aestronglyMeasurable cls).aemeasurable.ae_eq_mk.symm
  have hbound := rieszPressureSpaceTime_bound (5 / 3 : ℝ) (by norm_num) F hF53
  have hcomp (i j : Fin 3) : eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ)) volume ≤
      eLpNorm (fun z => v z i) (ENNReal.ofReal (10 / 3 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict S) *
        eLpNorm (fun z => w z j) (ENNReal.ofReal (10 / 3 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict S) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hS]
    exact eLpNorm_smul_le_mul_eLpNorm (φ := fun z => v z i) (f := fun z => w z j)
      (hv' i).aestronglyMeasurable (hw' j).aestronglyMeasurable
  have hfin (i j : Fin 3) : eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ)) volume ≠ ⊤ :=
    (hF53 i j).eLpNorm_ne_top
  have hnorm : eLpNorm (cls : Vec3 × ℝ → ℝ) (ENNReal.ofReal (5 / 3 : ℝ)) volume =
      ENNReal.ofReal ‖cls‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top cls)]
  have hsum0 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖(hF53 i j).toLp (F i j)‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  change eLpNorm (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF32)
    (ENNReal.ofReal (5 / 3 : ℝ)) volume ≤ _
  rw [eLpNorm_congr_ae (hagree.trans hrep), hnorm]
  calc ENNReal.ofReal ‖cls‖
      ≤ ENNReal.ofReal (rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖(hF53 i j).toLp (F i j)‖) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num)) *
          ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ)) volume := by
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

/-- `eq:forced-ten-thirds` and the `L^{5/3}` part of `eq:forced-pressure-bounds`
in `lem:forced-energy-bounds`: on a finite slab the velocity and the transport
velocity of the forced regularized solutions are bounded in `L^{10/3}`, and
the quadratic pressure `p_ε − p_f` in `L^{5/3}`, uniformly in `ε`. -/
theorem forcedLerayLimit_fiveThirds_bounds
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (T : ℝ) (hT : 0 < T) :
    ∃ M MJ MP : ℝ≥0∞, M < ⊤ ∧ MJ < ⊤ ∧ MP < ⊤ ∧ ∀ (ε : ℝ) (hε : 0 < ε),
      (∀ j : Fin 3, eLpNorm (fun z : ParabolicPoint => forcedRegVelocity ρ a ha f hf ε z j)
          (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ M) ∧
      (∀ i : Fin 3, eLpNorm (fun z : ParabolicPoint =>
          regUniformMollifiedVelocity ρ ε hε (forcedRegVelocity ρ a ha f hf ε) z i)
          (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ MJ) ∧
      eLpNorm (fun z : ParabolicPoint =>
          forcedRegPressure ρ a ha f hf ε z - forcePressure f hf z)
          (ENNReal.ofReal (5 / 3 : ℝ))
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ MP := by
  let E : ℝ := Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
    ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2)
  let G : ℝ := ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
    (∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2) +
    T * E) / 2
  let B : ℝ≥0∞ := (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) *
    ENNReal.ofReal (Real.sqrt E) ^ (4 / 3 : ℝ) * ENNReal.ofReal G
  have hB : B < ⊤ := by
    have hGN : (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        gagliardoNirenbergSobolevConstant_ne_top).ne
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hGN
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)) ENNReal.ofReal_lt_top
  let M : ℝ≥0∞ := B ^ (3 / 10 : ℝ)
  have hM : M < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne
  let MJ : ℝ≥0∞ := 3 * M
  have hMJ : MJ < ⊤ := ENNReal.mul_lt_top (by norm_num) hM
  let MP : ℝ≥0∞ := ENNReal.ofReal (rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num)) *
    (9 * (MJ * M))
  have hMP : MP < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top hMJ hM))
  refine ⟨M, MJ, MP, hM, hMJ, hMP, fun ε hε => ?_⟩
  let μ : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  let U := forcedRegVelocity ρ a ha f hf ε
  let J := regUniformMollifiedVelocity ρ ε hε U
  obtain ⟨⟨hSlice, -, -, -⟩, -, hR2, hR4, -⟩ := forcedRegularised ρ a ha f hf ε hε
  have hUs : StronglyMeasurable U := by
    change StronglyMeasurable (forcedRegVelocity ρ a ha f hf ε)
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact forcedRegRep_stronglyMeasurable ρ ε hε ha hf
  have hSliceAll : ∀ t : ℝ, MemLp (fun x : Vec3 => U (x, t)) 2 volume := by
    intro t
    change MemLp (fun x : Vec3 => forcedRegVelocity ρ a ha f hf ε (x, t)) 2 volume
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact forcedRegRep_memLp ρ ε hε ha hf t
  obtain ⟨-, hU103mem, hU3, hU103⟩ := forcedRegVelocity_memLp_slab ρ a ha f hf ε hε T hT
  -- the velocity in `L^{10/3}`
  have hUj : ∀ j : Fin 3, eLpNorm (fun z : ParabolicPoint => U z j)
      (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ M := by
    intro j
    have h := ENNReal.rpow_le_rpow (hU103 j) (by norm_num : (0 : ℝ) ≤ 3 / 10)
    rw [← ENNReal.rpow_mul] at h
    norm_num at h
    exact h
  -- the transport velocity in `L^{10/3}`
  have hJi : ∀ i : Fin 3, eLpNorm (fun z : ParabolicPoint => J z i)
      (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ MJ := by
    intro i
    have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (10 / 3 : ℝ) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    have ht := forcedLerayLimit_transport_eLpNorm_le ρ ε hε U hUs hSliceAll
      (p := ENNReal.ofReal (10 / 3 : ℝ)) hp ENNReal.ofReal_ne_top (Ioo 0 T) i
    rw [ENNReal.toReal_ofReal (by norm_num)] at ht
    have hsum : ∑ j : Fin 3, eLpNorm (fun z : ParabolicPoint => U z j)
        (ENNReal.ofReal (10 / 3 : ℝ)) μ ^ (10 / 3 : ℝ) ≤ 3 * M ^ (10 / 3 : ℝ) := by
      calc ∑ j : Fin 3, eLpNorm (fun z : ParabolicPoint => U z j)
            (ENNReal.ofReal (10 / 3 : ℝ)) μ ^ (10 / 3 : ℝ)
          ≤ ∑ _j : Fin 3, M ^ (10 / 3 : ℝ) :=
            Finset.sum_le_sum fun j _ => ENNReal.rpow_le_rpow (hUj j) (by norm_num)
        _ = 3 * M ^ (10 / 3 : ℝ) := by simp
    have hpow : eLpNorm (fun z : ParabolicPoint => J z i) (ENNReal.ofReal (10 / 3 : ℝ)) μ ^
        (10 / 3 : ℝ) ≤ MJ ^ (10 / 3 : ℝ) := by
      refine ht.trans ((mul_le_mul' le_rfl hsum).trans (le_of_eq ?_))
      change (3 : ℝ≥0∞) ^ ((10 / 3 : ℝ) - 1) * (3 * M ^ (10 / 3 : ℝ)) = (3 * M) ^ (10 / 3 : ℝ)
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc]
      congr 1
      rw [show (10 / 3 : ℝ) = ((10 / 3 : ℝ) - 1) + 1 by norm_num, ENNReal.rpow_add _ _
        (by norm_num) (by norm_num), ENNReal.rpow_one]
      norm_num
    have h := ENNReal.rpow_le_rpow hpow (by norm_num : (0 : ℝ) ≤ 3 / 10)
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h
    norm_num at h
    exact h
  -- the quadratic pressure in `L^{5/3}`
  have hSmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) =
      lerayPressureLimitSlab T := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
  rw [hpre] at hmp
  have hJ3 : MemLp J 3 μ := forcedRegTransport_memLp_three_slab ρ a ha f hf ε hε T hT
  have hUprod : MemLp (fun z : Vec3 × ℝ => U (parabolicHomeomorph.symm z)) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) :=
    hU3.comp_measurePreserving hmp
  have hJprod : MemLp (fun z : Vec3 × ℝ => J (parabolicHomeomorph.symm z)) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) :=
    hJ3.comp_measurePreserving hmp
  have hJ103 : ∀ i, MemLp (fun z : ParabolicPoint => J z i) (ENNReal.ofReal (10 / 3 : ℝ)) μ :=
    fun i => (hJi i).trans_lt hMJ
  have hPm := (hR2 T hT).2.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun z : Vec3 × ℝ =>
      forcedRegPressure ρ a ha f hf ε (parabolicHomeomorph.symm z) -
        forcePressure f hf (parabolicHomeomorph.symm z))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) :=
    ((hR2 T hT).2.comp_measurePreserving hmp).aestronglyMeasurable
  have hactual := forcedPressureLimit_quadratic_eq_product
    (fun z => forcedRegPressure ρ a ha f hf ε z - forcePressure f hf z) U J T hmeas
    (fun t ht => ⟨(hR4 t ht).choose, (hR4 t ht).choose_spec.1⟩) hUprod hJprod
  have hcompU (j : Fin 3) : eLpNorm (fun z : Vec3 × ℝ => U (parabolicHomeomorph.symm z) j)
      (ENNReal.ofReal (10 / 3 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) =
      eLpNorm (fun z : ParabolicPoint => U z j) (ENNReal.ofReal (10 / 3 : ℝ)) μ :=
    eLpNorm_comp_measurePreserving (hU3.eval j).aestronglyMeasurable hmp
  have hcompJ (i : Fin 3) : eLpNorm (fun z : Vec3 × ℝ => J (parabolicHomeomorph.symm z) i)
      (ENNReal.ofReal (10 / 3 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) =
      eLpNorm (fun z : ParabolicPoint => J z i) (ENNReal.ofReal (10 / 3 : ℝ)) μ :=
    eLpNorm_comp_measurePreserving (hJ3.eval i).aestronglyMeasurable hmp
  have hJ103p : ∀ i, MemLp (fun z : Vec3 × ℝ => J (parabolicHomeomorph.symm z) i)
      (ENNReal.ofReal (10 / 3 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) :=
    fun i => (hJ103 i).comp_measurePreserving hmp
  have hU103p : ∀ j, MemLp (fun z : Vec3 × ℝ => U (parabolicHomeomorph.symm z) j)
      (ENNReal.ofReal (10 / 3 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) :=
    fun j => (hU103mem.eval j).comp_measurePreserving hmp
  refine ⟨hUj, hJi, ?_⟩
  have hc := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (5 / 3 : ℝ)) hPm hmp
  rw [← hc]
  change eLpNorm (fun z : Vec3 × ℝ =>
      forcedRegPressure ρ a ha f hf ε (parabolicHomeomorph.symm z) -
        forcePressure f hf (parabolicHomeomorph.symm z)) (ENNReal.ofReal (5 / 3 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) ≤ MP
  rw [eLpNorm_congr_ae hactual]
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
    ((forcedLerayLimit_productPressure_eLpNorm_fiveThirds_le T _ _ hJprod hUprod
      hJ103p hU103p).trans ?_)
  refine mul_le_mul' le_rfl ?_
  calc ∑ i : Fin 3, ∑ j : Fin 3,
        eLpNorm (fun z : Vec3 × ℝ => J (parabolicHomeomorph.symm z) i)
            (ENNReal.ofReal (10 / 3 : ℝ))
            ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) *
          eLpNorm (fun z : Vec3 × ℝ => U (parabolicHomeomorph.symm z) j)
            (ENNReal.ofReal (10 / 3 : ℝ))
            ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))
      ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, MJ * M := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [hcompJ i, hcompU j]
        exact mul_le_mul' (hJi i) (hUj j)
    _ = 9 * (MJ * M) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
        ring

end CKN.Leray

end
