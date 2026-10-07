/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinLerayHopf
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinRestrict
public import LeanPool.EscauriazaSereginSverak.PartV.PositiveL5
public import LeanPool.EscauriazaSereginSverak.PartV.TraceInitialL3

/-!
# Assembly of the `L⁵` bound and uniqueness

Given a short-time solution from an `L³` trace in the class of
`lem:pv-serrin-uniqueness`, a Leray–Hopf solution with the critical
`L^∞_t L³_x` bound lies in space-time `L⁵` and is unique among Leray–Hopf
solutions with the same datum (`thm:ess-l5-unique`). The positive-time part
uses `lem:pv-positive-l5`, which takes `thm:ess-local` as its input.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The critical hypothesis gives an almost-every-time `L³` bound on the slices. -/
theorem lerayHopf_slice_l3_bound_ae {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) (ENNReal.ofReal (3 : ℝ)) volume
        ≤ M := by
  set S := essSup (fun t : ℝ => ∫⁻ x : Vec3,
    ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ)) (volume.restrict (Ioo 0 T))
  refine ⟨S ^ (1 / 3 : ℝ), ENNReal.rpow_lt_top_of_nonneg (by norm_num) hL3.ne, ?_⟩
  obtain ⟨p, hU⟩ := serrinWeak_of_lerayHopf hLH
  filter_upwards [ENNReal.ae_le_essSup (fun t : ℝ => ∫⁻ x : Vec3,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ)),
    serrinWeak_slices_ae hU] with t ht hs
  have hm : AEStronglyMeasurable (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) volume :=
    CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hs.1.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp) hm]
  have hr : (ENNReal.ofReal (3 : ℝ)).toReal = 3 := by simp
  rw [hr]
  have heq : (∫⁻ x : Vec3, ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (3 : ℝ)) =
      ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ) := by
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
  rw [heq]
  gcongr

/-- Membership in `L^p` on two sets gives membership on their union. -/
theorem serrin_memLp_union {f : ParabolicPoint → Vec3} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    {A B : Set ParabolicPoint} (hA : MemLp f p (volume.restrict A))
    (hB : MemLp f p (volume.restrict B)) : MemLp f p (volume.restrict (A ∪ B)) := by
  have hm : AEStronglyMeasurable f (volume.restrict (A ∪ B)) :=
    aestronglyMeasurable_union_iff.mpr ⟨hA.aestronglyMeasurable, hB.aestronglyMeasurable⟩
  have hfin (C : Set ParabolicPoint) (hC : MemLp f p (volume.restrict C)) :
      (∫⁻ z in C, ‖f z‖ₑ ^ p.toReal) < ⊤ := by
    have h1 := hC.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hC.aestronglyMeasurable] at h1
    exact (ENNReal.rpow_lt_top_iff_of_pos (by
      have := ENNReal.toReal_pos hp0 hptop
      positivity)).mp h1
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hm]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  exact (lt_of_le_of_lt (lintegral_union_le _ A B)
    (ENNReal.add_lt_top.mpr ⟨hfin A hA, hfin B hB⟩)).ne

/-- `thm:ess-l5-unique`, given the short-time solution of
`prop:pv-local-solution` in the class of `lem:pv-serrin-uniqueness`. -/
theorem essL5Unique_of_localSolution
    (hE1 :
      ∀ u : ParabolicPoint → Vec3,
      ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      ∀ p : ParabolicPoint → ℝ,
        AEStronglyMeasurable u
          (volume.restrict
            (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
        AEStronglyMeasurable Du
          (volume.restrict
            (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
        AEStronglyMeasurable p
          (volume.restrict
            (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
        essSup
          (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
          (volume.restrict (Ioo (-1) 0)) < ⊤ →
        (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ →
        MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict
            (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
        essSup
          (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
          (volume.restrict (Ioo (-1) 0)) < ⊤ →
        (∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
          HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
            (fun x => u (x, t) i) (fun x => Du (x, t) i)) →
        (∀ ψ : ParabolicPoint → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ)
            (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
          ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
            ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0) →
        (∀ φ : ParabolicPoint → Vec3,
          φ ∈ spaceTimeTestFunction (V := Vec3)
            (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
          ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
            (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
              - ∑ i : Fin 3, ∑ j : Fin 3,
                  u z i * u z j * spatialPartial (fun y => φ y i) j z
              + ∑ i : Fin 3, ∑ j : Fin 3,
                  Du z i j * spatialPartial (fun y => φ y i) j z
              - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
              - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) →
        ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
          ∃ w : ParabolicPoint → Vec3,
            w =ᵐ[volume.restrict
              (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))] u ∧
            ParabolicHolderVecOn
              (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))) w γ)
    (hloc : ∀ a : Vec3 → Vec3, IsInJ a → MemLp a (ENNReal.ofReal (3 : ℝ)) volume →
      ∃ σ : ℝ, 0 < σ ∧ ∃ U : ParabolicPoint → Vec3, ∃ DU : ParabolicPoint → Fin 3 → Vec3,
        ∃ p : ParabolicPoint → ℝ, IsSerrinWeakSolution σ a U DU p ∧
          MemLp U (ENNReal.ofReal 5)
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ)))) :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      essSup
        (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
      MemLp u (ENNReal.ofReal (5 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      ∀ v : ParabolicPoint → Vec3,
        ∀ Dv : ParabolicPoint → Fin 3 → Vec3,
          IsLerayHopfSolution T a v Dv →
            v =ᵐ[volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u := by
  intro T a u Du hLH hL3
  have hT : 0 < T := hLH.1
  -- the initial trace is in `L³`
  obtain ⟨M, hM, hMb⟩ := lerayHopf_slice_l3_bound_ae hLH hL3
  have ha3 := (lerayHopf_initialTrace_memLp_three hLH M hM hMb).1
  -- the short-time solution
  obtain ⟨σ, hσ, U, DU, pU, hUw, hU5⟩ := hloc a hLH.2.1 ha3
  set σ' : ℝ := min σ T with hσ'def
  have hσ' : 0 < σ' := lt_min hσ hT
  have hUw' := hUw.restrict hσ' (min_le_left _ _)
  obtain ⟨pu, huw⟩ := serrinWeak_of_lerayHopf hLH
  have huw' := huw.restrict hσ' (min_le_right _ _)
  have hU5' : MemLp U (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ'))) :=
    hU5.mono_measure (serrin_slab_restrict_le (min_le_left _ _))
  have hu103' : MemLp u (ENNReal.ofReal (10 / 3))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ'))) :=
    (lerayHopf_memLp_tenThirds hLH).1.mono_measure (serrin_slab_restrict_le (min_le_right _ _))
  have huE : ∀ᵐ t ∂(volume.restrict (Ioo 0 σ')),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du q k j * Du q k j := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    have hs := (ae_restrict_iff' measurableSet_Ioo).mp (serrinWeak_slices_ae huw')
    filter_upwards [hs] with t ht htI
    exact lerayHopf_energy_inequality_real hLH
      ⟨htI.1.le, htI.2.le.trans (min_le_right _ _)⟩ (ht htI).1
  have hEq := serrin_weak_strong_uniqueness hUw' huw' hU5' hu103' huE
  have hu5' : MemLp u (ENNReal.ofReal 5)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ'))) :=
    (memLp_congr_ae hEq).mpr hU5'
  -- the positive-time part
  have hpos := pvPositiveL5 hE1 hLH hL3 (half_pos hσ')
  have hcover : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ') ∪
        spaceTimeSet (Set.univ : Set Vec3) (Ioo (σ' / 2) T) := by
    intro z hz
    by_cases h : z.2 < σ'
    · exact Or.inl ⟨hz.1, hz.2.1, h⟩
    · exact Or.inr ⟨hz.1, by linarith only [h, hσ'], hz.2.2⟩
  have hu5 : MemLp u (ENNReal.ofReal (5 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (serrin_memLp_union (by simp) (by simp) hu5' hpos).mono_measure
      (Measure.restrict_mono hcover le_rfl)
  refine ⟨hu5, fun v Dv hV => ?_⟩
  exact (lerayHopf_serrin_uniqueness hLH hV hu5).symm

end ESS
