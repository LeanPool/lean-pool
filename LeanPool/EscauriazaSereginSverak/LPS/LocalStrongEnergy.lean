/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliIdentity
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreMixed
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.EscauriazaSereginSverak.PartV.PvLocalSolutionLerayHopfCore
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.NhdsWithin

/-!
# Local energy identity for a strong solution

The compactly supported identity supplies the local kinetic-energy step for
`prop:lps-local-strong`. The strong right `L²` trace follows from continuity
and an a.e. initial representative.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

private theorem lps_slice_energy_continuousOn
    {a b : ℝ} {v : ℝ → Vec3 → Vec3}
    (hmem : ∀ t ∈ Icc a b, MemLp (fun x : Vec3 => v t x) 2 volume)
    (hcont : ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (fun x : Vec3 => v s x - v t x) 2 volume)
        (nhdsWithin t (Icc a b)) (nhds 0)) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3,
      ∑ i : Fin 3, v t x i * v t x i) (Icc a b) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  let N : ℝ → ℝ := fun s =>
    (eLpNorm (fun x : Vec3 => v s x - v t x) 2 volume).toReal
  have hN : Tendsto N (nhdsWithin t (Icc a b)) (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t ht)
    rw [ENNReal.toReal_zero] at h
    exact h
  have hlim : Tendsto (fun s =>
      3 * (N s * N s) +
        2 * (3 * (N s * (eLpNorm (fun x : Vec3 => v t x) 2 volume).toReal)))
      (nhdsWithin t (Icc a b)) (nhds 0) := by
    have h := ((hN.mul hN).const_mul 3).add
      (((hN.mul_const (eLpNorm (fun x : Vec3 => v t x) 2 volume).toReal).const_mul 3).const_mul 2)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hdiff : MemLp (fun x : Vec3 => v s x - v t x) 2 volume :=
    (hmem s hs).sub (hmem t ht)
  have hpairInt (f g : Vec3 → Vec3) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
      Integrable (fun x => ∑ i : Fin 3, f x i * g x i) :=
    integrable_finsetSum _ fun i _ =>
      (memLp_pi_iff.1 hf i).integrable_mul (memLp_pi_iff.1 hg i)
  have hsplit :
      (∫ x : Vec3, ∑ i : Fin 3, v s x i * v s x i) -
          ∫ x : Vec3, ∑ i : Fin 3, v t x i * v t x i =
        (∫ x : Vec3, ∑ i : Fin 3,
          (v s x - v t x) i * (v s x - v t x) i) +
          2 * ∫ x : Vec3, ∑ i : Fin 3,
            (v s x - v t x) i * v t x i := by
    rw [← integral_sub (hpairInt (v s) (v s) (hmem s hs) (hmem s hs))
        (hpairInt (v t) (v t) (hmem t ht) (hmem t ht)),
      ← integral_const_mul, ← integral_add
        (hpairInt (fun x => v s x - v t x) (fun x => v s x - v t x) hdiff hdiff)
        ((hpairInt (fun x => v s x - v t x) (v t) hdiff (hmem t ht)).const_mul 2)]
    congr 1
    funext x
    simp only [Pi.sub_apply, Fin.sum_univ_three]
    ring
  rw [Real.norm_eq_abs, hsplit]
  refine (abs_add_le _ _).trans (add_le_add (pvLH_pair_le hdiff hdiff) ?_)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (pvLH_pair_le hdiff (hmem t ht)) (by norm_num)

private theorem lps_strong_slice_memLp_two
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    MemLp (fun x : Vec3 => u (x, t)) 2 volume ∧
      MemLp (fun x : Vec3 => Du (x, t)) 2 volume := by
  rcases hU with ⟨_hT, hSlices, _hContinuity, _hHigher,
    _hPressure, _hEquation⟩
  rcases hSlices t ht with ⟨hJ, hH1⟩
  refine ⟨hJ.1, memLp_pi_iff.2 (fun i => ?_)⟩
  rcases hH1 i with ⟨h, _hFun, hGrad⟩
  apply memLp_pi_iff.2
  intro j
  simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ,
    hGrad] using h.gradMemL2 j

private theorem lps_four_memLp_sum_lintegral_lt_top
    {S : Set ParabolicPoint}
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hw : MemLp w 2 (volume.restrict S))
    (hDw : MemLp Dw 2 (volume.restrict S))
    (hD2w : MemLp D2w 2 (volume.restrict S))
    (hDtw : MemLp Dtw 2 (volume.restrict S)) :
    (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
      ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hfin (E : Type) [NormedAddCommGroup E]
      (f : ParabolicPoint → E) (hf : MemLp f 2 (volume.restrict S)) :
      (∫⁻ z in S, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hf.aestronglyMeasurable).1 hf
    simpa using h
  have hA := hfin _ w hw
  have hB := hfin _ Dw hDw
  have hC := hfin _ D2w hD2w
  have hD := hfin _ Dtw hDtw
  have hmA : AEMeasurable (fun z => ‖w z‖ₑ ^ (2 : ℝ))
      (volume.restrict S) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hw.aestronglyMeasurable.enorm
  have hmB : AEMeasurable (fun z => ‖Dw z‖ₑ ^ (2 : ℝ))
      (volume.restrict S) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hDw.aestronglyMeasurable.enorm
  have hmC : AEMeasurable (fun z => ‖D2w z‖ₑ ^ (2 : ℝ))
      (volume.restrict S) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hD2w.aestronglyMeasurable.enorm
  have hAB : (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ)) =
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ)) +
        (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ)) := by
    simpa only [Pi.add_apply] using
      (lintegral_add_left' hmA (fun z => ‖Dw z‖ₑ ^ (2 : ℝ)))
  have hABC : (∫⁻ z in S,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ)) =
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ)) +
        (∫⁻ z in S, ‖D2w z‖ₑ ^ (2 : ℝ) ) := by
    simpa only [Pi.add_apply] using
      (lintegral_add_left' (hmA.add hmB) (fun z => ‖D2w z‖ₑ ^ (2 : ℝ)))
  have hABCD : (∫⁻ z in S,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) =
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ)) + (∫⁻ z in S, ‖Dtw z‖ₑ ^ (2 : ℝ)) := by
    simpa only [Pi.add_apply] using
      (lintegral_add_left' ((hmA.add hmB).add hmC)
        (fun z => ‖Dtw z‖ₑ ^ (2 : ℝ)))
  rw [hABCD, hABC, hAB]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hA, hB⟩, hC⟩, hD⟩

private theorem lps_strong_zeroExtend_spacetime_data
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ T) u Du D2u Dtu)
    (hMemU : MemLp u 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T))))
    (hMemDu : MemLp Du 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T))))
    (hMemD2u : MemLp D2u 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T))))
    (hMemDtu : MemLp Dtu 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T)))) :
    MemLp (zeroExtendField (Set.univ ×ˢ Ioo t₀ T)
      (fun q : Vec3 × ℝ => u (parabolicHomeomorph.symm q))) 2 volume ∧
    MemLp (zeroExtendField (Set.univ ×ˢ Ioo t₀ T)
      (fun q : Vec3 × ℝ => Du (parabolicHomeomorph.symm q))) 2 volume ∧
    MemLp (zeroExtendField (Set.univ ×ˢ Ioo t₀ T)
      (fun q : Vec3 × ℝ => D2u (parabolicHomeomorph.symm q))) 2 volume ∧
    MemLp (zeroExtendField (Set.univ ×ˢ Ioo t₀ T)
      (fun q : Vec3 × ℝ => Dtu (parabolicHomeomorph.symm q))) 2 volume := by
  have hL2 : (∫⁻ z in spaceTimeSet Set.univ (Ioo t₀ T),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) +
        ‖D2u z‖ₑ ^ (2 : ℝ) + ‖Dtu z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lps_four_memLp_sum_lintegral_lt_top hMemU hMemDu hMemD2u hMemDtu
  exact zeroExtend_spaceTimeData_memLp isOpen_univ isOpen_Ioo hDerivs hL2

/-- Strong `L²` continuity of the velocity in a strong solution makes its
fixed-time kinetic-energy representative continuous up to both endpoints
(`prop:lps-local-strong`). -/
theorem lps_strong_velocity_energy_continuousOn
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3,
      ∑ i : Fin 3, u (x, t) i * u (x, t) i) (Icc t₀ T) := by
  have hMem : ∀ t ∈ Icc t₀ T,
      MemLp (fun x : Vec3 => u (x, t)) 2 volume := by
    intro t ht
    exact (lps_strong_slice_memLp_two hU ht).1
  rcases hU with ⟨_hT, _hSlices, hContinuity, _hHigher, _hPressure, _hEquation⟩
  apply lps_slice_energy_continuousOn
  · exact hMem
  · intro t ht
    exact (hContinuity t ht).1

/-- Strong `L²` continuity of the specified gradient gives continuity of its
fixed-time squared norm, with the same ordered component convention as
`prop:lps-local-strong`. -/
theorem lps_strong_gradient_energy_continuousOn
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3,
      ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) (Icc t₀ T) := by
  have hSliceMem : ∀ t ∈ Icc t₀ T,
      MemLp (fun x : Vec3 => u (x, t)) 2 volume ∧
        MemLp (fun x : Vec3 => Du (x, t)) 2 volume := by
    intro t ht
    exact lps_strong_slice_memLp_two hU ht
  rcases hU with ⟨_hT, _hSlices, hContinuity, _hHigher,
    _hPressure, _hEquation⟩
  have hrowMem (i : Fin 3) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      MemLp (fun x : Vec3 => Du (x, t) i) 2 volume := by
    exact memLp_pi_iff.1 (hSliceMem t ht).2 i
  have hrowCont (i : Fin 3) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      Tendsto (fun s => eLpNorm
        (fun x : Vec3 => Du (x, s) i - Du (x, t) i) 2 volume)
        (nhdsWithin t (Icc t₀ T)) (nhds 0) := by
    have hwhole := (hContinuity t ht).2
    have hle (s : ℝ) (hs : s ∈ Icc t₀ T) : eLpNorm
        (fun x : Vec3 => Du (x, s) i - Du (x, t) i) 2 volume ≤
        eLpNorm (fun x : Vec3 => Du (x, s) - Du (x, t)) 2 volume := by
      have hdiff : MemLp (fun x : Vec3 => Du (x, s) - Du (x, t)) 2 volume :=
        (hSliceMem s hs).2.sub (hSliceMem t ht).2
      apply eLpNorm_mono
        ((continuous_apply i).comp_aestronglyMeasurable
          hdiff.aestronglyMeasurable)
      intro x
      exact norm_le_pi_norm _ i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwhole
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hle s hs
  have hrowEnergy (i : Fin 3) : ContinuousOn
      (fun t : ℝ => ∫ x : Vec3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2)
      (Icc t₀ T) := by
    convert lps_slice_energy_continuousOn
      (a := t₀) (b := T) (v := fun t x => Du (x, t) i)
      (fun t ht => hrowMem i t ht) (fun t ht => hrowCont i t ht) using 1;
      simp [pow_two]
  have hsumCont : ContinuousOn (fun t : ℝ =>
      ∑ i : Fin 3, ∫ x : Vec3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2)
      (Icc t₀ T) :=
    continuousOn_finsetSum Finset.univ fun i _ => hrowEnergy i
  refine hsumCont.congr ?_
  intro t ht
  have hrowInt (i : Fin 3) : Integrable
      (fun x : Vec3 => ∑ j : Fin 3, (Du (x, t) i j) ^ 2) volume := by
    apply integrable_finsetSum
    intro j hj
    convert (memLp_pi_iff.1 (hrowMem i t ht) j).integrable_mul
      (memLp_pi_iff.1 (hrowMem i t ht) j) using 1
    funext x
    simp only [Pi.mul_apply]
    simp only [pow_two]
  have hsum :
      (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        (Du (x, t) i j) ^ 2) =
      ∑ i : Fin 3, ∫ x : Vec3, ∑ j : Fin 3,
        (Du (x, t) i j) ^ 2 := by
    rw [integral_finsetSum (f := fun i (x : Vec3) =>
      ∑ j : Fin 3, (Du (x, t) i j) ^ 2) _ fun i _ => hrowInt i]
  exact hsum

private theorem lps_spacetime_mixed_derivative_identity
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ T) u Du D2u Dtu)
    {φ : ParabolicPoint → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Set.univ (Ioo t₀ T))
    (i j : Fin 3) :
    ∫ z in spaceTimeSet Set.univ (Ioo t₀ T),
      Du z i j * timePartial φ z =
    ∫ z in spaceTimeSet Set.univ (Ioo t₀ T),
      Dtu z i * spatialPartial φ j z := by
  rcases hDerivs with ⟨_hu, _hDu, _hD2u, _hDtu, hweak⟩
  have htime :
      (fun z : ParabolicPoint => timePartial φ z) ∈
        spaceTimeTestFunction (V := ℝ) Set.univ (Ioo t₀ T) := by
    refine ⟨CKN.contDiff_timePartial hφ.1,
      CKN.hasCompactSupport_timePartial hφ.2.1, ?_⟩
    exact (CKN.tsupport_timePartial_subset φ).trans hφ.2.2
  have hspace :
      (fun z : ParabolicPoint => spatialPartial φ j z) ∈
        spaceTimeTestFunction (V := ℝ) Set.univ (Ioo t₀ T) := by
    refine ⟨CKN.spatialPartial_contDiff hφ.1 j,
      CKN.hasCompactSupport_spatialPartial hφ.2.1 j, ?_⟩
    exact (CKN.tsupport_spatialPartial_subset j).trans hφ.2.2
  have hspaceId := (hweak (timePartial φ) htime).1 i j
  have htimeId := (hweak (spatialPartial φ j) hspace).2.2 i
  have hcomm :
      (fun z : ParabolicPoint => spatialPartial (fun y => timePartial φ y) j z) =
        (fun z : ParabolicPoint => timePartial (fun y => spatialPartial φ j y) z) := by
    funext z
    exact (CKN.timePartial_spatialPartial_comm hφ.1 z j).symm
  calc
    ∫ z in spaceTimeSet Set.univ (Ioo t₀ T), Du z i j * timePartial φ z =
        -∫ z in spaceTimeSet Set.univ (Ioo t₀ T),
          u z i * spatialPartial (fun y => timePartial φ y) j z := by
            linarith only [hspaceId]
    _ = -∫ z in spaceTimeSet Set.univ (Ioo t₀ T),
          u z i * timePartial (fun y => spatialPartial φ j y) z := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with z
            exact congrArg (fun r : ℝ => u z i * r) (congrFun hcomm z)
    _ = ∫ z in spaceTimeSet Set.univ (Ioo t₀ T),
          Dtu z i * spatialPartial φ j z := by linarith only [htimeId]

/-- The open-slab derivative witnesses already contained in a strong solution
(`prop:lps-local-strong`). -/
theorem lps_strong_solution_derivative_data
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) :
    ∃ D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3,
      ∃ Dtu : ParabolicPoint → Vec3,
        HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ T) u Du D2u Dtu ∧
        MemLp u 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T))) ∧
        MemLp Du 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T))) ∧
        MemLp D2u 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T))) ∧
        MemLp Dtu 2
          (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T))) := by
  rcases hU with ⟨_hT, _hSlices, _hContinuity, hHigher,
    _hPressure, _hEquation⟩
  rcases hHigher with ⟨D2u, Dtu, hDerivs, hMemU, hMemDu,
    hMemD2u, hMemDtu⟩
  exact ⟨D2u, Dtu, hDerivs, hMemU, hMemDu, hMemD2u, hMemDtu⟩

/-- Strong `L²` continuity identifies any prescribed a.e. initial slice with
the strong right trace (`prop:lps-local-strong`). -/
theorem lps_l2_trace_of_ae_initial
    {t₀ T : ℝ} {b : Vec3 → Vec3} {u : ℝ → Vec3 → Vec3}
    (hT : t₀ < T)
    (hCont : ∀ t ∈ Icc t₀ T,
      Tendsto (fun s => eLpNorm (fun x : Vec3 => u s x - u t x) 2 volume)
        (nhdsWithin t (Icc t₀ T)) (nhds 0))
    (hTrace : u t₀ =ᵐ[volume] b) :
    Tendsto (fun t : ℝ => eLpNorm (fun x : Vec3 => u (t₀ + t) x - b x) 2 volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hzero : eLpNorm (fun x : Vec3 => u t₀ x - b x) 2 volume = 0 := by
    have hfun : (fun x : Vec3 => u t₀ x - b x) =ᵐ[volume] fun _ => (0 : Vec3) := by
      filter_upwards [hTrace] with x hx
      rw [hx]
      simp
    rw [eLpNorm_congr_ae hfun]
    simp
  have hgap : 0 < T - t₀ := sub_pos.mpr hT
  have hnear : Icc (0 : ℝ) (T - t₀) ∈ nhdsWithin 0 (Ioi 0) :=
    mem_of_superset (Ioo_mem_nhdsGT hgap) Ioo_subset_Icc_self
  have hid : Tendsto (fun t : ℝ => t)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds (0 : ℝ)) :=
    tendsto_id.mono_left
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ≤ nhds (0 : ℝ))
  have hc : Tendsto (fun _ : ℝ => t₀)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds t₀) := tendsto_const_nhds
  have hbase : Tendsto (fun t : ℝ => t₀ + t)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds t₀) := by
    simpa only [add_zero] using hc.add hid
  have hmap : Tendsto (fun t : ℝ => t₀ + t)
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin t₀ (Icc t₀ T)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hbase, ?_⟩
    filter_upwards [hnear] with t ht
    exact ⟨by linarith only [ht.1], by linarith only [ht.2, hT]⟩
  have hshift : Tendsto (fun t : ℝ => eLpNorm
      (fun x : Vec3 => u (t₀ + t) x - u t₀ x) 2 volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    (hCont t₀ (left_mem_Icc.2 hT.le)).comp hmap
  have hsum : Tendsto (fun t : ℝ => eLpNorm
      (fun x : Vec3 => u (t₀ + t) x - u t₀ x) 2 volume +
        eLpNorm (fun x : Vec3 => u t₀ x - b x) 2 volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [hzero] using hshift.add_const
      (eLpNorm (fun x : Vec3 => u t₀ x - b x) 2 volume)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [] with t
  have hdecomp : (fun x : Vec3 => u (t₀ + t) x - b x) =
      (fun x => u (t₀ + t) x - u t₀ x) + fun x => u t₀ x - b x := by
    funext x
    simp only [Pi.add_apply]
    abel
  rw [hdecomp]
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  exact eLpNorm_add_le hp

/-- The localized kinetic-energy identity with a compact space-time weight
(`prop:lps-local-strong`). -/
theorem lps_strong_localized_energy_identity
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ T) u Du D2u Dtu)
    (hL2 : (∫⁻ z in spaceTimeSet Set.univ (Ioo t₀ T),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) +
        ‖D2u z‖ₑ ^ (2 : ℝ) + ‖Dtu z‖ₑ ^ (2 : ℝ)) < ⊤)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hbuffer : ∀ q ∈ tsupport φ,
      Metric.closedBall q (4 * δ₀) ⊆ (Set.univ : Set Vec3) ×ˢ Ioo t₀ T) :
    (∑ i : Fin 3,
      ∫ q : Vec3 × ℝ,
        ((spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)).indicator
          (fun y => u (parabolicHomeomorph.symm y)) q) i *
        ((spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)).indicator
          (fun y => Dtu (parabolicHomeomorph.symm y)) q) i * φ q) +
    (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ q : Vec3 × ℝ, φ q *
        ((spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)).indicator
          (fun y => u (parabolicHomeomorph.symm y)) q) i *
        ((spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)).indicator
          (fun y => D2u (parabolicHomeomorph.symm y)) q) i j j) =
      -(1 / 2) * (∑ i : Fin 3,
        ∫ q : Vec3 × ℝ,
          ((spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)).indicator
            (fun y => u (parabolicHomeomorph.symm y)) q) i ^ 2 *
          (fderiv ℝ φ q) (0, 1)) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, φ q *
          (((spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)).indicator
            (fun y => Du (parabolicHomeomorph.symm y)) q) i j) ^ 2) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ,
          (fderiv ℝ φ q) (basisVec j, 0) *
            ((spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)).indicator
              (fun y => u (parabolicHomeomorph.symm y)) q) i *
            ((spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)).indicator
              (fun y => Du (parabolicHomeomorph.symm y)) q) i j) := by
  exact ESS.localizedEnergyIdentity isOpen_univ isOpen_Ioo hDerivs hL2
    hφ hφc hδ₀ hbuffer

end ESS.LPS

end
