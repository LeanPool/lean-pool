/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.EssL5UniqueInputs
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionBundle
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionContraction

/-!
# Clauses of the short-time solution

Clauses of `prop:pv-local-solution` for the Duhamel fixed point: besides being
a finite-energy weak solution in `L⁵` of the slab, it lies in `L⁴` of the slab,
its pressure is the canonical pressure `P[U ⊗ U]` of `def:riesz-pressure` (cut
off to the slab), and that pressure lies in `L² ∩ L^{5/2}` of the slab.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The Duhamel fixed point of `prop:pv-local-solution` is a finite-energy weak
solution whose pressure is the canonical pressure `P[U ⊗ U]` cut off to the
slab. -/
theorem pvLocalClauses_bundle {a : Vec3 → Vec3} (ha : IsInJ a)
    {σ : ℝ} (hσ : 0 < σ) {U : ParabolicPoint → Vec3}
    (hU5 : MemLp U (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))))
    (hU4 : MemLp U (ENNReal.ofReal 4)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))))
    (hfix : ∀ z : ParabolicPoint, z.2 ≠ 0 → U z = pvLocalMap a σ U z)
    (hinit : ∀ x : Vec3, U (x, 0) = a x) :
    ∃ DU : ParabolicPoint → Fin 3 → Vec3,
      IsSerrinWeakSolution σ a U DU (pvSlabPressure σ U) := by
  set Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ) with hQdef
  have hQm : MeasurableSet Q := MeasurableSet.univ.prod measurableSet_Ioo
  set G := pvSlabForce σ U with hGdef
  set Z := forcedHeat G with hZdef
  have hG52 (i j : Fin 3) := (pvSlabForce_memLp_both hU5 hU4 i j).1
  have hG2 (i j : Fin 3) := (pvSlabForce_memLp_both hU5 hU4 i j).2
  have hGsupp (i j : Fin 3) (z : ParabolicPoint) (hz : z ∉ Q) : G i j z = 0 :=
    pvSlabForce_eq_zero hz i j
  have hT2 (i j : Fin 3) := (pvSlabTensor_memLp_both hU5 hU4 i j).2
  -- the forced part
  obtain ⟨DZ, hDZ, hDZgrad, hZweak⟩ := forcedHeat_rough_solution hσ hG52 hG2 hGsupp
  have hZ2 : MemLp Z 2 (volume.restrict Q) := forcedHeat_rough_memLp_two hσ hG52 hG2 hGsupp
  obtain ⟨K, hK, hZslice⟩ := forcedHeat_rough_slice_energy hσ hG52 hG2 hGsupp
  have hZdiv := forcedHeat_divFree hσ hG2 hGsupp (pvSlabForce_doubleDiv hT2)
  -- the heat part
  obtain ⟨hh2, hDh2⟩ := heatOrbit_memLp_two_slab ha hσ
  -- the fixed point splits
  have hUeq (z : ParabolicPoint) (hz : z.2 ≠ 0) : U z = heatOrbit a z + Z z := hfix z hz
  have hUQ (z : ParabolicPoint) (hz : z ∈ Q) : U z = heatOrbit a z + Z z :=
    hUeq z hz.2.1.ne'
  have hU2 : MemLp U 2 (volume.restrict Q) := by
    refine MemLp.ae_eq ?_ (hh2.add hZ2)
    filter_upwards [ae_restrict_mem hQm] with z hz
    exact (hUQ z hz).symm
  have hDZ2 : MemLp (fun z => fun i j => DZ i j z) 2 (volume.restrict Q) :=
    memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j => hDZ i j
  let DU : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1 + DZ i j z
  have hDU2 : MemLp DU 2 (volume.restrict Q) := hDh2.add hDZ2
  refine ⟨DU, ?_⟩
  refine
    { pos := hσ
      datum := ha.1
      meas_u := hU2.aestronglyMeasurable
      meas_Du := hDU2.aestronglyMeasurable
      slice_bound := ?_
      energy := ?_
      weak_grad := ?_
      div_free := ?_
      pressure := pvSlabPressure_memLp_fiveThirds hU2 hU4
      momentum := ?_
      weak_cont := ?_
      initial := ?_ }
  · -- the slices are uniformly square integrable
    set Kh : ℝ≥0∞ := ∑ i : Fin 3, eLpNorm (fun y => a y i) 2 volume ^ (2 : ℝ)
    have hKh : Kh ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) (memLp_pi_iff.1 ha.1 i).eLpNorm_ne_top
    have hbound : ∀ᵐ s ∂(volume.restrict (Ioo 0 σ)),
        ∫⁻ x : Vec3, ‖U (x, s)‖ₑ ^ (2 : ℝ) ≤ 2 * (Kh + K) := by
      filter_upwards [hZslice, ae_restrict_mem measurableSet_Ioo] with s hZs hs
      have hhc : Continuous (fun x : Vec3 => heatOrbit a (x, s)) :=
        continuous_pi fun i => heatOrbit_slice_continuous ha.1 hs.1 i
      have hpt (x : Vec3) : ‖U (x, s)‖ₑ ^ (2 : ℝ) ≤
          2 * (‖heatOrbit a (x, s)‖ₑ ^ (2 : ℝ) + ‖Z (x, s)‖ₑ ^ (2 : ℝ)) := by
        rw [hUeq (x, s) hs.1.ne']
        have h1 := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖heatOrbit a (x, s)‖ₑ ‖Z (x, s)‖ₑ
          (p := 2) (by norm_num)
        rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h1
        exact (ENNReal.rpow_le_rpow (enorm_add_le _ _) (by norm_num)).trans h1
      calc
        ∫⁻ x : Vec3, ‖U (x, s)‖ₑ ^ (2 : ℝ) ≤
            ∫⁻ x : Vec3, 2 * (‖heatOrbit a (x, s)‖ₑ ^ (2 : ℝ) + ‖Z (x, s)‖ₑ ^ (2 : ℝ)) :=
          lintegral_mono hpt
        _ = 2 * ((∫⁻ x : Vec3, ‖heatOrbit a (x, s)‖ₑ ^ (2 : ℝ)) +
            ∫⁻ x : Vec3, ‖Z (x, s)‖ₑ ^ (2 : ℝ)) := by
          rw [lintegral_const_mul' _ _ (by norm_num),
            lintegral_add_left' (hhc.aestronglyMeasurable.enorm.pow_const _)]
        _ ≤ 2 * (Kh + K) :=
          by
            gcongr
            · exact heatOrbit_slice_lintegral_le ha.1 hs.1
            · exact hZs.2
    refine lt_of_le_of_lt (essSup_le_of_ae_le _ hbound) ?_
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.2 ⟨hKh.lt_top, hK.lt_top⟩)
  · -- finite energy
    rw [lintegral_add_left' (hU2.aestronglyMeasurable.enorm.pow_const _)]
    exact ENNReal.add_lt_top.2 ⟨(memLp_two_iff_lintegral_enorm_sq hU2.aestronglyMeasurable).1 hU2,
      (memLp_two_iff_lintegral_enorm_sq hDU2.aestronglyMeasurable).1 hDU2⟩
  · -- slicewise weak gradients
    have hDZs : ∀ᵐ s ∂(volume.restrict (Ioo 0 σ)), ∀ ij : Fin 3 × Fin 3,
        MemLp (fun x : Vec3 => DZ ij.1 ij.2 (x, s)) 2 volume :=
      ae_all_iff.2 fun ij => serrin_slice_memLp_ae two_ne_zero ENNReal.ofNat_ne_top (hDZ ij.1 ij.2)
    filter_upwards [hDZgrad, hZslice, hDZs, ae_restrict_mem measurableSet_Ioo] with
      s hgrad hZs hDZs hs
    intro i
    have e1 : (fun x : Vec3 => U (x, s) i) = fun x => heatOrbit a (x, s) i + Z (x, s) i := by
      funext x
      rw [hUeq (x, s) hs.1.ne']
      rfl
    rw [e1]
    exact hasWeakGradientOn_univ_add
      (heatOrbit_slice_continuous ha.1 hs.1 i).locallyIntegrable
      ((memLp_pi_iff.1 hZs.1 i).locallyIntegrable (by norm_num))
      (fun j => heatOrbit_slice_grad_locallyIntegrable ha.1 hs.1 i j)
      (fun j => (hDZs (i, j)).locallyIntegrable (by norm_num))
      (heatOrbit_hasWeakGradientOn ha hs.1 i) (hgrad i)
  · -- divergence free
    filter_upwards [hZdiv, hZslice, ae_restrict_mem measurableSet_Ioo] with s hZd hZs hs
    intro ψ
    have hpc (i : Fin 3) : Continuous (ψ.partialDeriv i) :=
      (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
    have hps (i : Fin 3) : HasCompactSupport (ψ.partialDeriv i) :=
      ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hhi : Integrable (fun x => ∑ i : Fin 3, heatOrbit a (x, s) i * ψ.partialDeriv i x) :=
      integrable_finsetSum _ fun i _ => by
        simpa only [smul_eq_mul] using (heatOrbit_slice_continuous ha.1 hs.1 i).locallyIntegrable
          |>.integrable_smul_right_of_hasCompactSupport (hpc i) (hps i)
    have hZi : Integrable (fun x => ∑ i : Fin 3, Z (x, s) i * ψ.partialDeriv i x) :=
      integrable_finsetSum _ fun i _ =>
        integrable_mul_of_memLp_two_of_hasCompactSupport (memLp_pi_iff.1 hZs.1 i) (hpc i) (hps i)
    have hpt : (fun x : Vec3 => ∑ i : Fin 3, U (x, s) i * ψ.partialDeriv i x) =
        fun x => ∑ i : Fin 3, heatOrbit a (x, s) i * ψ.partialDeriv i x +
          ∑ i : Fin 3, Z (x, s) i * ψ.partialDeriv i x := by
      funext x
      rw [hUeq (x, s) hs.1.ne', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply]
      ring
    rw [hpt, integral_add hhi hZi, heatOrbit_weak_div_eq_zero ha hs.1 ψ, hZd ψ, add_zero]
  · -- the momentum equation
    intro φ hφmem
    have hh6 := heatOrbit_weak_heat_equation ha hφmem
    obtain ⟨hφ, hφc, hφs⟩ := hφmem
    have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => φ p i) := contDiff_pi.1 hφ i
    have hφic (i : Fin 3) : HasCompactSupport (fun p : Vec3 × ℝ => φ p i) :=
      hφc.comp_left (g := fun v : Vec3 => v i) rfl
    have hφis (i : Fin 3) : tsupport (fun p : Vec3 × ℝ => φ p i) ⊆
        (Set.univ : Set Vec3) ×ˢ Ioo 0 σ :=
      (tsupport_comp_subset (g := fun v : Vec3 => v i) rfl (fun p : Vec3 × ℝ => φ p)).trans hφs
    have hZw (i : Fin 3) := hZweak (fun y => φ y i) (hφi i) (hφic i) (hφis i) i
    have hT (i : Fin 3) := spaceTimeTest_derivs_memLp_two (hφi i) (hφic i) σ
    have hhi (i : Fin 3) : MemLp (fun z => heatOrbit a z i) 2 (volume.restrict Q) :=
      memLp_pi_iff.1 hh2 i
    have hDhi (i j : Fin 3) : MemLp (fun z : ParabolicPoint =>
        spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1) 2 (volume.restrict Q) :=
      memLp_pi_iff.1 (memLp_pi_iff.1 hDh2 i) j
    have hZi (i : Fin 3) : MemLp (fun z => Z z i) 2 (volume.restrict Q) := memLp_pi_iff.1 hZ2 i
    have hAint : Integrable (fun z : ParabolicPoint =>
        (-(∑ i : Fin 3, heatOrbit a z i * timePartial (fun y => φ y i) z)) +
          ∑ i : Fin 3, ∑ j : Fin 3,
            spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1 *
              spatialPartial (fun y => φ y i) j z) (volume.restrict Q) :=
      (integrable_finsetSum _ fun i _ => (hhi i).integrable_mul (hT i).1).neg.add
        (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hDhi i j).integrable_mul ((hT i).2 j))
    have hBint (i : Fin 3) : Integrable (fun z : ParabolicPoint =>
        -(Z z i * timePartial (fun y => φ y i) z) +
          ∑ j : Fin 3, DZ i j z * spatialPartial (fun y => φ y i) j z +
          ∑ j : Fin 3, G i j z * spatialPartial (fun y => φ y i) j z) (volume.restrict Q) :=
      (((hZi i).integrable_mul (hT i).1).neg.add
        (integrable_finsetSum _ fun j _ => (hDZ i j).integrable_mul ((hT i).2 j))).add
        (integrable_finsetSum _ fun j _ => ((hG2 i j).restrict _).integrable_mul ((hT i).2 j))
    have hpt : EqOn (fun z : ParabolicPoint =>
        (-(∑ i : Fin 3, U z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3, U z i * U z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3, DU z i j * spatialPartial (fun y => φ y i) j z
          - pvSlabPressure σ U z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i)
        (fun z : ParabolicPoint =>
          ((-(∑ i : Fin 3, heatOrbit a z i * timePartial (fun y => φ y i) z)) +
            ∑ i : Fin 3, ∑ j : Fin 3,
              spatialDeriv (fun y => heatOrbit a (y, z.2) i) j z.1 *
                spatialPartial (fun y => φ y i) j z) +
          ∑ i : Fin 3, (-(Z z i * timePartial (fun y => φ y i) z) +
            ∑ j : Fin 3, DZ i j z * spatialPartial (fun y => φ y i) j z +
            ∑ j : Fin 3, G i j z * spatialPartial (fun y => φ y i) j z)) Q := by
      intro z hz
      have hGz (i j : Fin 3) : G i j z * spatialPartial (fun y => φ y i) j z =
          -(U z i * U z j * spatialPartial (fun y => φ y i) j z) -
            if i = j then pvSlabPressure σ U z * spatialPartial (fun y => φ y i) j z else 0 := by
        have hT' : pvSlabTensor σ U U i j z = U z i * U z j := indicator_of_mem hz _
        simp only [hGdef, pvSlabForce, hT']
        split_ifs <;> ring
      have hrow (i : Fin 3) : ∑ j : Fin 3, G i j z * spatialPartial (fun y => φ y i) j z =
          -(∑ j : Fin 3, U z i * U z j * spatialPartial (fun y => φ y i) j z) -
            pvSlabPressure σ U z * spatialPartial (fun y => φ y i) i z := by
        simp only [hGz, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
      simp only [hrow]
      rw [hUQ z hz]
      simp only [DU, Pi.add_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero,
        Fin.sum_univ_three]
      ring
    rw [setIntegral_congr_fun hQm hpt, integral_add hAint (integrable_finsetSum _ fun i _ => hBint i),
      integral_finsetSum _ fun i _ => hBint i, hh6, Finset.sum_eq_zero fun i _ => hZw i, add_zero]
  · -- time continuity of the pairings
    intro ψ hψ hψc
    obtain ⟨hZint, hZcont, hZ0⟩ := forcedHeat_pairing_continuous hσ hG52 hGsupp hψ hψc
    obtain ⟨hHcont, hHlim⟩ := heatOrbit_weak_continuity_initial ha σ hψ hψc
    have hψi (i : Fin 3) : Continuous (fun x => ψ x i) := (continuous_apply i).comp hψ.continuous
    have hψic (i : Fin 3) : HasCompactSupport (fun x => ψ x i) :=
      hψc.comp_left (g := fun v : Vec3 => v i) rfl
    have hsplit (t : ℝ) (ht : t ∈ Ioc 0 σ) :
        ∫ x : Vec3, ∑ i : Fin 3, U (x, t) i * ψ x i =
          (∫ x : Vec3, ∑ i : Fin 3, heatOrbit a (x, t) i * ψ x i) +
            ∫ x : Vec3, ∑ i : Fin 3, Z (x, t) i * ψ x i := by
      have hhi : Integrable (fun x => ∑ i : Fin 3, heatOrbit a (x, t) i * ψ x i) :=
        integrable_finsetSum _ fun i _ => by
          simpa only [smul_eq_mul] using (heatOrbit_slice_continuous ha.1 ht.1 i).locallyIntegrable
            |>.integrable_smul_right_of_hasCompactSupport (hψi i) (hψic i)
      rw [← integral_add hhi (hZint t (Ioc_subset_Icc_self ht))]
      congr 1
      funext x
      rw [hUeq (x, t) ht.1.ne', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply]
      ring
    have hf0 : ∫ x : Vec3, ∑ i : Fin 3, U (x, 0) i * ψ x i =
        ∫ x : Vec3, ∑ i : Fin 3, a x i * ψ x i := by
      simp only [hinit]
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      rw [← Ioc_insert_left hσ.le, continuousWithinAt_insert_self, ContinuousWithinAt, hf0]
      have hH : Tendsto (fun t => ∫ x : Vec3, ∑ i : Fin 3, heatOrbit a (x, t) i * ψ x i)
          (𝓝[Ioc 0 σ] 0) (𝓝 (∫ x : Vec3, ∑ i : Fin 3, a x i * ψ x i)) :=
        hHlim.mono_left (nhdsWithin_mono _ Ioc_subset_Ioi_self)
      have hZt : Tendsto (fun t => ∫ x : Vec3, ∑ i : Fin 3, Z (x, t) i * ψ x i)
          (𝓝[Ioc 0 σ] 0) (𝓝 0) := by
        have h := hZcont 0 (left_mem_Icc.2 hσ.le)
        rw [ContinuousWithinAt, hZ0] at h
        exact h.mono_left (nhdsWithin_mono _ Ioc_subset_Icc_self)
      have hsum := hH.add hZt
      rw [add_zero] at hsum
      exact hsum.congr' (eventually_nhdsWithin_of_forall fun t ht => (hsplit t ht).symm)
    · have hmem : Ioc 0 σ ∈ 𝓝[Icc 0 σ] t :=
        mem_nhdsWithin.2 ⟨Ioi 0, isOpen_Ioi, hpos, fun x hx => ⟨hx.1, hx.2.2⟩⟩
      have hH := (hHcont t ⟨hpos, ht.2⟩).mono_of_mem_nhdsWithin hmem
      refine (hH.add (hZcont t ht)).congr_of_eventuallyEq ?_ (hsplit t ⟨hpos, ht.2⟩)
      filter_upwards [hmem] with x hx
      exact hsplit x hx
  · -- the initial datum
    intro ψ _ _
    simp only [hinit]

/-- The short-time solution of `prop:pv-local-solution`, with its `L⁴` bound and
its pressure: for every divergence-free datum in `L² ∩ L³` there are `σ > 0`
and a finite-energy weak solution on `ℝ³ × (0, σ)` in `L⁵ ∩ L⁴` of the slab,
whose pressure is the canonical pressure `P[U ⊗ U]` cut off to the slab and
lies in `L² ∩ L^{5/2}` of the slab. -/
theorem pvLocalSolution_clauses {a : Vec3 → Vec3} (ha : IsInJ a)
    (ha3 : MemLp a (ENNReal.ofReal (3 : ℝ)) volume) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ U : ParabolicPoint → Vec3, ∃ DU : ParabolicPoint → Fin 3 → Vec3,
      IsSerrinWeakSolution σ a U DU (pvSlabPressure σ U) ∧
      MemLp U (ENNReal.ofReal 5)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) ∧
      MemLp U (ENNReal.ofReal 4)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) ∧
      MemLp (pvSlabPressure σ U) (ENNReal.ofReal 2) volume ∧
      MemLp (pvSlabPressure σ U) (ENNReal.ofReal (5 / 2)) volume := by
  have ha3' : MemLp a 3 volume := by
    have e3 : ENNReal.ofReal (3 : ℝ) = 3 := by simp
    rw [e3] at ha3
    exact ha3
  obtain ⟨σ, hσ, U, hU5, hU4, hfix, hinit⟩ := pvLocal_fixedPoint ha.1 ha3'
  obtain ⟨DU, hU⟩ := pvLocalClauses_bundle ha hσ hU5 hU4 hfix hinit
  have hT52 : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal (5 / 2)) volume :=
    fun i j => (pvSlabTensor_memLp_both hU5 hU4 i j).1
  have hT2 : ∀ i j, MemLp (pvSlabTensor σ U U i j) (ENNReal.ofReal 2) volume :=
    fun i j => (pvSlabTensor_memLp_both hU5 hU4 i j).2
  exact ⟨σ, hσ, U, DU, hU, hU5, hU4, pvSlabPressure_memLp (by norm_num) hT2 hT2,
    pvSlabPressure_memLp (by norm_num) hT2 hT52⟩

end ESS

end
