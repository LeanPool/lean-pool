/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitPropFinalTails
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitPropFinalStrong
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitCompactness
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitSubcritical
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitJConvLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegEquicontinuityInputs
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPropProvider

/-!
# The compactness statement `prop:leray-limit`

For the regularized solutions of `thm:regularised`, every sequence `ε_n → 0`
in `(0,1]` has a subsequence along which the velocities converge to a limit
`u` with weak gradient `Du` in all the senses used by the proof of `thm:leray`.
The subsequence, the limit fields and their local convergence come from the
compactness step `CKN.Leray.lerayLimit_local_compactness`, whose time-pairing
modulus follows from the regularized contract; the whole-slab statements come
from the uniform spatial tails of `lem:reg-tails`, which enter as the
hypothesis `hregTails`. The limit velocity is the compactness limit at
positive times and the datum at time zero; its value at every positive time is
the iterated limit of spatial mollifications along the subsequence.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem lerayLimitFinal_piecewise_of_mem {β : Type*} [Zero β]
    (s : Set ParabolicPoint) (f g : ParabolicPoint → β) (z : ParabolicPoint) (hz : z ∈ s) :
    lerayLimitPiecewise s f g z = f z := by
  unfold lerayLimitPiecewise
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hz

private theorem lerayLimitFinal_fiber_enorm_sq (A : Fin 3 → Vec3) :
    ‖toCompactnessGradientFiber A‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, A i j ^ (2 : ℕ)) := by
  have h := norm_toCompactnessGradientFiber_sq (fun _ => (0 : Vec3)) (fun _ => A)
    (show ParabolicPoint from ((0 : Vec3), (0 : ℝ)))
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]
  exact congrArg ENNReal.ofReal h

/-- The iterated mollified limit at a point depends only on the slices of the
sequence at the time of that point. -/
private theorem lerayLimitFinal_mollifiedLimit_congr_slice
    (F G : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ) (z : Vec3 × ℝ)
    (hFG : ∀ n (y : Vec3), F n (y, z.2) = G n (y, z.2)) :
    compactnessMollifiedLimit F σ z = compactnessMollifiedLimit G σ z := by
  funext i
  unfold compactnessMollifiedLimit
  have h : ∀ k, (fun y : Vec3 => F (σ k) (y, z.2) i) = fun y => G (σ k) (y, z.2) i :=
    fun k => funext fun y => by rw [hFG]
  simp only [h]

/-- The compact cylinders `B̄_m × [T/(m+2), T - T/(m+2)]` exhausting the slab
`ℝ³ × (0,T)`. -/
@[expose]
def lerayLimitFinalCylinder (T : ℝ) (m : ℕ) : Set (Vec3 × ℝ) :=
  Metric.closedBall (0 : Vec3) (m : ℝ) ×ˢ Icc (T / ((m : ℝ) + 2)) (T - T / ((m : ℝ) + 2))

private theorem lerayLimitFinalCylinder_subset {T : ℝ} (hT : 0 < T) (m : ℕ) :
    lerayLimitFinalCylinder T m ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
  intro z hz
  have hpos : 0 < T / ((m : ℝ) + 2) := by positivity
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · exact lt_of_lt_of_le hpos hz.2.1
  · exact lt_of_le_of_lt hz.2.2 (by linarith only [hpos])

private theorem lerayLimitFinalCylinder_subset_pos {T : ℝ} (hT : 0 < T) (m : ℕ) :
    lerayLimitFinalCylinder T m ⊆ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) := by
  intro z hz
  exact ⟨Set.mem_univ _, ((lerayLimitFinalCylinder_subset hT m) hz).2.1⟩

private theorem lerayLimitFinalCylinder_isCompact (T : ℝ) (m : ℕ) :
    IsCompact (lerayLimitFinalCylinder T m) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

private theorem lerayLimitFinalCylinder_aecover (T : ℝ) :
    AECover ((volume : Measure (Vec3 × ℝ)).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) atTop
      (lerayLimitFinalCylinder T) := by
  have hSmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :
      Set (Vec3 × ℝ)) := MeasurableSet.univ.prod measurableSet_Ioo
  refine ⟨?_, fun m => (lerayLimitFinalCylinder_isCompact T m).isClosed.measurableSet⟩
  refine (ae_restrict_iff' hSmeas).2 (Eventually.of_forall fun z hz => ?_)
  obtain ⟨-, ht0, htT⟩ := hz
  have hsmall : Tendsto (fun m : ℕ => T / ((m : ℝ) + 2)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat T
    have hshift : Tendsto (fun m : ℕ => T / (((m + 2 : ℕ) : ℝ))) atTop (𝓝 0) :=
      h.comp (tendsto_add_atTop_nat 2)
    refine hshift.congr fun m => ?_
    push_cast
    ring
  have hδ : 0 < min z.2 (T - z.2) := lt_min ht0 (by linarith only [htT])
  have hev1 : ∀ᶠ m : ℕ in atTop, T / ((m : ℝ) + 2) < min z.2 (T - z.2) :=
    hsmall.eventually (gt_mem_nhds hδ)
  have hev2 : ∀ᶠ m : ℕ in atTop, ‖z.1‖ ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hev1, hev2] with m hm1 hm2
  have hm1a : T / ((m : ℝ) + 2) < z.2 := lt_of_lt_of_le hm1 (min_le_left _ _)
  have hm1b : T / ((m : ℝ) + 2) < T - z.2 := lt_of_lt_of_le hm1 (min_le_right _ _)
  refine ⟨?_, hm1a.le, by linarith only [hm1b]⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hm2

/-- `prop:leray-limit` for the regularized solutions `uε` with pressures `pε`
of `thm:regularised` (the contract `hregularised`), given the exterior
estimate `hregTails` of `lem:reg-tails`. The conclusion is the compactness
statement used by `CKN.lerayExistence_of_limits`. -/
theorem lerayLimit_prop_of_regularised_tails
    (ρ : RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε),
      let u := uε a ha ε
      let p := pε a ha ε
      let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
        spatialPartial (fun y => u y i) j z
      let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
        spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
      let Dt : ParabolicPoint → Vec3 := fun z i =>
        timePartial (fun y => u y i) z
      let Dp : ParabolicPoint → Vec3 := fun z i =>
        spatialPartial (fun y => p y) i z
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          CKN.Leray.realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          CKN.Leray.regUniformMollifiedInitial ρ ε hε a ∧
        ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
      (∀ i : Fin 3, ContinuousOn (fun z => u z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ i j, ContinuousOn (fun z => D z i j)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ i j k, ContinuousOn (fun z => DD z i j k)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ i, ContinuousOn (fun z => Dt z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
      (∀ i, ContinuousOn (fun z => Dp z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
        DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
            vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
            (∀ i j, |D z i j| ≤ C) ∧
            (∀ i j k, |DD z i j k| ≤ C) ∧
            (∀ i, |Dt z i| ≤ C) ∧
            (∀ i, |Dp z i| ≤ C)) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        MemLp p 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
        Dt z i - (∑ j : Fin 3, DD z i j j) +
          (∑ j : Fin 3,
            CKN.Leray.regUniformMollifiedVelocity ρ ε hε u z j * D z i j) +
          Dp z i = 0) ∧
      (∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume,
          (fun x : Vec3 => p (x, t)) =ᵐ[volume]
            CKN.Leray.rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 =>
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j)) ∧
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
              -∑ i : Fin 3, ∑ j : Fin 3,
                ∫ x : Vec3,
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j * mixedSecond ψ i j x) ∧
      (∀ t : ℝ, 0 ≤ t →
        eLpNorm (CKN.Leray.regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
          2 * CKN.Leray.regUniformDissipation u D t =
            eLpNorm (CKN.Leray.regMollifyVector ρ ε hε
              (CKN.Leray.regUniformSpatialField a)) 2 volume ^ (2 : ℕ)))
    (hregTails : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
        (_hεone : ε ≤ 1),
        (∀ R1 R2 t : ℝ, 0 < R1 → R1 < R2 → 0 ≤ t →
          (∫ x in {x : Vec3 | R2 < vec3EuclideanNorm x},
            (vec3EuclideanNorm (uε a ha ε (x, t))) ^ (2 : ℕ)) ≤
            (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
              (vec3EuclideanNorm
                (regUniformMollifiedInitial ρ ε hε a x)) ^ (2 : ℕ)) +
              C * (((eLpNorm a 2 volume).toReal) ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
                ((eLpNorm a 2 volume).toReal) ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) /
                (R2 - R1)) ∧
        (∀ R1 : ℝ, 0 < R1 →
          (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
            (vec3EuclideanNorm (regUniformMollifiedInitial ρ ε hε a x)) ^
              (2 : ℕ)) ≤
            ∫ x in {x : Vec3 | R1 - 1 < vec3EuclideanNorm x},
              (vec3EuclideanNorm (a x)) ^ (2 : ℕ))) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (_hεseq : Tendsto εseq atTop (nhds 0)),
      ∃ σ : ℕ → ℕ, ∃ u : ParabolicPoint → Vec3,
        ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        StrictMono σ ∧ Tendsto σ atTop atTop ∧
        Tendsto (fun n => εseq (σ n)) atTop (nhds 0) ∧
        (∀ x : Vec3, u (x, 0) = a x) ∧
        (∀ T : ℝ, 0 < T →
          let μ : Measure ParabolicPoint :=
            volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
          let U : ℕ → ParabolicPoint → Vec3 :=
            fun n => uε a ha (εseq (σ n))
          let J : ℕ → ParabolicPoint → Vec3 := fun n =>
            CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
              (by exact (hseq (σ n)).1) (U n)
          let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n z i j =>
            spatialPartial (fun y => U n y i) j z
          AEStronglyMeasurable u μ ∧ AEStronglyMeasurable Du μ ∧
          MemLp u 2 μ ∧ MemLp Du 2 μ ∧
          Tendsto (fun n => eLpNorm (U n - u) 2 μ) atTop (nhds 0) ∧
          (∀ i j, ∀ w : ParabolicPoint → ℝ, MemLp w 2 μ →
            Tendsto (fun n => ∫ z in spaceTimeSet
                (Set.univ : Set Vec3) (Ioo 0 T), Dseq n z i j * w z)
              atTop (nhds (∫ z in spaceTimeSet
                (Set.univ : Set Vec3) (Ioo 0 T), Du z i j * w z))) ∧
          (∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
            Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal q) μ)
              atTop (nhds 0)) ∧
          (∀ n, MemLp (U n) 3 μ) ∧
          (∀ n, MemLp (J n) 3 μ) ∧ MemLp u 3 μ ∧
          Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0) ∧
          (∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
            MemLp w 2 volume →
            Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3,
                U n (x, t) i * w x i) atTop
              (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i))) ∧
          (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
            HasWeakGradientOn (Set.univ : Set Vec3)
              (fun x => u (x, t) i) (fun x => Du (x, t) i))) ∧
        (∀ z : Vec3 × ℝ, 0 < z.2 →
          u (parabolicHomeomorph.symm z) =
            CKN.Leray.compactnessMollifiedLimit
              (fun n => fun y =>
                uε a ha (εseq (σ n)) (parabolicHomeomorph.symm y)) σ z) := by
  intro a ha εseq hseq hεseq
  classical
  -- the local compactness step, with the time-pairing modulus of the contract
  have hregEquicontinuity :=
    regEquicontinuity_modulus_of_regularised_contract ρ uε pε hregularised
  obtain ⟨σ, hσ, v, g, hv, -, hvrep, hlocal, hstrong, hgrad, hae, hslice, -⟩ :=
    lerayLimit_local_compactness ρ uε pε hregularised hregEquicontinuity a ha εseq hseq
  let P : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)
  have hPmeas : MeasurableSet P := MeasurableSet.univ.prod measurableSet_Ioi
  let Ubar : ℕ → Vec3 × ℝ → Vec3 := fun n z =>
    lerayLimitPiecewise P
      (fun q => uε a ha (εseq n) (parabolicHomeomorph.symm q))
      (fun q => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a q.1) z
  let Dbar : ℕ → Vec3 × ℝ → Fin 3 → Vec3 := fun n z i j =>
    lerayLimitPiecewise P
      (fun q k l => spatialPartial (fun y => uε a ha (εseq n) y k) l q)
      (fun _ _ _ => 0) (parabolicHomeomorph.symm z) i j
  have hUbar : ∀ n (x : Vec3) (t : ℝ), 0 < t →
      Ubar n (x, t) = uε a ha (εseq n) (x, t) := fun n x t ht =>
    lerayLimitFinal_piecewise_of_mem P _ _ (x, t) ⟨Set.mem_univ _, ht⟩
  have hDbar : ∀ n (z : Vec3 × ℝ), 0 < z.2 → ∀ i j,
      Dbar n z i j = spatialPartial (fun y => uε a ha (εseq n) y i) j z := by
    intro n z hz i j
    change lerayLimitPiecewise P
      (fun q k l => spatialPartial (fun y => uε a ha (εseq n) y k) l q)
      (fun _ _ _ => 0) z i j = _
    rw [lerayLimitFinal_piecewise_of_mem P _ _ z ⟨Set.mem_univ _, hz⟩]
  -- the regularized contract along the sequence
  have hdata := fun n =>
    lerayLimit_regularised_basic_data ρ uε pε hregularised a ha (εseq n) (hseq n).1
  have hSliceMem : ∀ n (t : ℝ), 0 ≤ t →
      MemLp (fun x : Vec3 => uε a ha (εseq n) (x, t)) 2 volume := fun n => (hdata n).1
  have hUcont : ∀ n (i : Fin 3), ContinuousOn (fun z => uε a ha (εseq n) z i) P :=
    fun n => (hdata n).2.1
  have hDcont : ∀ n (i j : Fin 3), ContinuousOn
      (fun z => spatialPartial (fun y => uε a ha (εseq n) y i) j z) P :=
    fun n => (hdata n).2.2.1
  have hUmeas : ∀ n (t : ℝ), 0 < t →
      Measurable (fun x : Vec3 => uε a ha (εseq n) (x, t)) := by
    intro n t ht
    have hm : Measurable (P.piecewise (uε a ha (εseq n)) 0) :=
      (continuousOn_pi.mpr (hUcont n)).measurable_piecewise continuousOn_const hPmeas
    have h := hm.comp (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3))
      (y := t))
    convert h using 1
    funext x
    exact (piecewise_eq_of_mem _ _ _ (show ((x, t) : ParabolicPoint) ∈ P from
      ⟨Set.mem_univ _, ht⟩)).symm
  -- the uniform slice energy bound
  have haL2 : MemLp (regUniformSpatialField a) 2 volume := by
    have hcoord : MemLp (fun x : L2Vec3 => a (WithLp.ofLp x)) (2 : ℝ≥0∞) volume :=
      ha.1.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  let A : ℝ≥0∞ := eLpNorm (regUniformSpatialField a) 2 volume
  have hA : A < ⊤ := haL2
  have hA2 : A ^ (2 : ℕ) < ⊤ := ENNReal.pow_lt_top hA
  have hSliceGlobal : ∀ n (t : ℝ), 0 ≤ t →
      (∫⁻ x : Vec3, ‖(WithLp.toLp 2 (uε a ha (εseq n) (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤
        A ^ (2 : ℕ) := by
    intro n
    refine lerayLimit_lintegral_slice_bound_of_energy (uε a ha (εseq n)) A (hSliceMem n) ?_
    intro t ht
    have hE := (hdata n).2.2.2 t ht
    have hM := regMollifyVector_eLpNorm_two_le ρ (εseq n) (hseq n).1 haL2
    calc eLpNorm (regUniformVelocitySlice (uε a ha (εseq n)) t) 2 volume ^ (2 : ℕ)
        ≤ eLpNorm (regUniformVelocitySlice (uε a ha (εseq n)) t) 2 volume ^ (2 : ℕ) +
            2 * regUniformDissipation (uε a ha (εseq n))
              (fun z i j => spatialPartial (fun y => uε a ha (εseq n) y i) j z) t :=
          le_self_add
      _ = eLpNorm (regMollifyVector ρ (εseq n) (hseq n).1 (regUniformSpatialField a))
            2 volume ^ (2 : ℕ) := hE
      _ ≤ A ^ (2 : ℕ) := pow_le_pow_left₀ zero_le hM 2
  have hUbarSlice : ∀ n (t : ℝ), 0 < t →
      (∫⁻ x : Vec3, ‖(WithLp.toLp 2 (Ubar n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤
        A ^ (2 : ℕ) := by
    intro n t ht
    have hfun : (fun x : Vec3 => ‖(WithLp.toLp 2 (Ubar n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) =
        fun x => ‖(WithLp.toLp 2 (uε a ha (εseq n) (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) := by
      funext x
      rw [hUbar n x t ht]
    rw [hfun]
    exact hSliceGlobal n t ht.le
  -- the limit fields
  let u : ParabolicPoint → Vec3 := fun z =>
    if 0 < z.2 then v (parabolicHomeomorph z) else a z.1
  let Du : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    WithLp.ofLp (g (parabolicHomeomorph z) i) j
  have huv : ∀ (x : Vec3) (t : ℝ), 0 < t → u (x, t) = v (x, t) := fun x t ht => by
    simp [u, ht]
  have hσtop : Tendsto σ atTop atTop := hσ.tendsto_atTop
  have hεsub : Tendsto (fun n => εseq (σ n)) atTop (𝓝 0) := hεseq.comp hσtop
  -- every-time weak convergence
  have hevery := lerayLimit_everyTime_pairing_tendsto_of_local_energy
    (fun n => uε a ha (εseq n)) Ubar σ v u hUmeas hv hUbar huv
    (fun _ _ => ⟨A, hA, fun n t ht _ => hSliceGlobal n t ht.le⟩) hlocal hslice
  refine ⟨σ, u, Du, hσ, hσtop, hεsub, fun x => by simp [u], fun T hT => ?_, ?_⟩
  · -- the clauses on the slab `ℝ³ × (0,T)`
    have hslabMeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    have htails := lerayLimit_regularised_spatialTails_with_limit ρ uε hregTails a ha
      εseq hseq hSliceMem Ubar hUbar σ v hv T hlocal
    obtain ⟨hU2, hu2, hL2⟩ := lerayLimit_slab_strongL2_of_local_and_tails T hT
      (fun n => uε a ha (εseq (σ n))) (fun k => Ubar (σ k)) (fun n => hUcont (σ n))
      (fun n x t ht => hUbar (σ n) x t ht) v hv u huv hstrong A hA
      (fun n t ht => hSliceGlobal (σ n) t ht.1.le)
      (fun t ht => lerayLimit_limit_slice_le_of_compact_transfer Ubar v hv (A ^ (2 : ℕ)) hA2
        t ht.1 (fun n => hUbarSlice n t ht.1) hslice)
      htails
    -- subcritical strong convergence
    have hLq := lerayLimit_regularised_subcritical ρ uε pε hregularised a ha εseq hseq σ T u
      (by rw [ENNReal.ofReal_ofNat]; exact hL2)
    have hL3 : Tendsto (fun n => eLpNorm (uε a ha (εseq (σ n)) - u) (ENNReal.ofReal (3 : ℝ))
        (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T)))) atTop (𝓝 0) :=
      hLq 3 (by norm_num) (by norm_num)
    -- cubic integrability of the regularized velocities
    obtain ⟨Bt, -, hBt⟩ := regEquicontinuity_regularized_velocity_tenThirds_bound
      ρ uε pε hregularised a ha (fun n => εseq (σ n)) (fun n => hseq (σ n))
    have hle : (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :
        Measure ParabolicPoint) ≤ regUniformPositiveTimeMeasure := by
      refine Measure.restrict_mono (fun z hz => ?_) le_rfl
      exact ⟨hz.1, hz.2.1⟩
    have hvec := lerayLimit_vector_tenThirds_of_component_bounds
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))
      (fun n => uε a ha (εseq (σ n))) (ENNReal.ofReal Bt)
      (fun n i => (hBt n i).1.mono_measure hle)
      (fun n i => (eLpNorm_mono_measure _ hle).trans (hBt n i).2)
    have hU3 : ∀ n, MemLp (uε a ha (εseq (σ n))) 3
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
      intro n
      have h := lerayLimit_memLp_of_exponent_between (p := 2) (q := 3) (r := 10 / 3)
        (by norm_num) (by norm_num) (by norm_num)
        (by rw [ENNReal.ofReal_ofNat]; exact hU2 n) (hvec n).1
      rwa [ENNReal.ofReal_ofNat] at h
    -- the mollified transport velocities
    obtain ⟨hJ3, hu3, hJconv⟩ := lerayLimit_regUniformMollifiedVelocity_tendsto_three ρ T
      (fun n => εseq (σ n)) (fun n => (hseq (σ n)).1) hεsub
      (fun n => uε a ha (εseq (σ n))) u (fun n => hUcont (σ n))
      (fun n => hSliceMem (σ n)) hU3 hL3
    -- the gradients
    have hDenergy : ∀ n,
        (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ‖toCompactnessGradientFiber (Dbar (σ n) z)‖ₑ ^ (2 : ℝ)) ≤ A ^ (2 : ℕ) := by
      intro n
      obtain ⟨-, hdiss, -⟩ := lerayLimit_regularised_energy_bounds ρ a ha (εseq (σ n))
        (hseq (σ n)).1 (uε a ha (εseq (σ n)))
        (fun z i j => spatialPartial (fun y => uε a ha (εseq (σ n)) y i) j z)
        (hUcont (σ n)) (hDcont (σ n)) (hdata (σ n)).2.2.2
      let ubarE : ParabolicPoint → Vec3 := lerayLimitPiecewise P (uε a ha (εseq (σ n)))
        (fun z => regUniformMollifiedInitial ρ (εseq (σ n)) (hseq (σ n)).1 a z.1)
      let DbarE : ParabolicPoint → Fin 3 → Vec3 := lerayLimitPiecewise P
        (fun z i j => spatialPartial (fun y => uε a ha (εseq (σ n)) y i) j z) (fun _ => 0)
      have hdiss' : 2 * (∫⁻ z, ENNReal.ofReal (spatialGradientSq ubarE DbarE z)
          ∂regUniformPositiveTimeMeasure) ≤ A ^ (2 : ℕ) := hdiss
      have hpt : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ‖toCompactnessGradientFiber (Dbar (σ n) z)‖ₑ ^ (2 : ℝ) =
            ENNReal.ofReal (spatialGradientSq ubarE DbarE z) := by
        intro z _
        rw [lerayLimitFinal_fiber_enorm_sq]
        rfl
      calc (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            ‖toCompactnessGradientFiber (Dbar (σ n) z)‖ₑ ^ (2 : ℝ))
          = ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              ENNReal.ofReal (spatialGradientSq ubarE DbarE z) :=
            setLIntegral_congr_fun hslabMeas hpt
        _ ≤ ∫⁻ z, ENNReal.ofReal (spatialGradientSq ubarE DbarE z)
              ∂regUniformPositiveTimeMeasure :=
            lintegral_mono_set (fun z hz => ⟨hz.1, hz.2.1⟩)
        _ ≤ (∫⁻ z, ENNReal.ofReal (spatialGradientSq ubarE DbarE z)
              ∂regUniformPositiveTimeMeasure) +
            ∫⁻ z, ENNReal.ofReal (spatialGradientSq ubarE DbarE z)
              ∂regUniformPositiveTimeMeasure := le_self_add
        _ = 2 * ∫⁻ z, ENNReal.ofReal (spatialGradientSq ubarE DbarE z)
              ∂regUniformPositiveTimeMeasure := (two_mul _).symm
        _ ≤ A ^ (2 : ℕ) := hdiss'
    have hmain := forcedLerayLimit_globalGradient_outputs T (fun n z => Dbar (σ n) z) g
      (lerayLimitFinalCylinder T) (lerayLimitFinalCylinder_subset hT)
      (lerayLimitFinalCylinder_aecover T) (A ^ (2 : ℕ)) hA2 hDenergy
      (fun m => hgrad _ (lerayLimitFinalCylinder_isCompact T m)
        (lerayLimitFinalCylinder_subset_pos hT m))
    obtain ⟨hDm, hD2, hDw⟩ := hmain
    have hDweak : ∀ i j, ∀ w : ParabolicPoint → ℝ,
        MemLp w 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
        Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            spatialPartial (fun y => uε a ha (εseq (σ n)) y i) j z * w z)
          atTop (nhds (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            Du z i j * w z)) := by
      intro i j w hw
      refine (hDw i j w hw).congr fun n => setIntegral_congr_fun hslabMeas fun z hz => ?_
      rw [hDbar (σ n) z hz.2.1 i j]
    have haeu : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
        HasWeakGradientOn (Set.univ : Set Vec3)
          (fun x => u (x, t) i) (fun x => Du (x, t) i) := by
      filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with t ht htpos
      intro i
      have hfun : (fun x : Vec3 => u (x, t) i) = fun x => v (x, t) i := by
        funext x
        rw [huv x t htpos]
      rw [hfun]
      exact ht i
    exact ⟨hu2.aestronglyMeasurable, hDm, hu2, hD2, hL2, hDweak, hLq, hU3, hJ3, hu3,
      hJconv, hevery, haeu⟩
  · -- the positive-time representative
    intro z hz
    have hu : u (parabolicHomeomorph.symm z) = v z := by
      change u (z.1, z.2) = v z
      rw [huv z.1 z.2 hz]
    let F0 : ℕ → Vec3 × ℝ → Vec3 := fun n y => uε a ha (εseq n) (parabolicHomeomorph.symm y)
    have hcongr : compactnessMollifiedLimit Ubar σ z = compactnessMollifiedLimit F0 σ z :=
      lerayLimitFinal_mollifiedLimit_congr_slice Ubar F0 σ z
        (fun n y => hUbar n y z.2 hz)
    rw [hu, hvrep z, hcongr]
    symm
    refine compactnessMollifiedLimit_comp_eq_of_tendsto F0 σ hσtop z ?_
    intro i m
    let r := CKN.sliceRadius m
    let hr := CKN.sliceRadius_pos m
    let w : Vec3 → Vec3 := fun y => Pi.single i (CKN.mollifier (d := 3) r hr (z.1 - y))
    have hw : MemLp w 2 volume :=
      (memLp_reflected_mollifier_coordinate m z.1 i).continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
    have hpair : ∀ G : Vec3 → Vec3,
        CKN.mollify (fun y => G y i) r hr z.1 = ∫ y, ∑ j : Fin 3, G y j * w y j := by
      intro G
      rw [← CKN.integral_mul_mollifier_sub]
      congr 1
      funext y
      simp [w, Pi.single_apply]
    refine ⟨∫ y, ∑ j : Fin 3, u (y, z.2) j * w y j, ?_⟩
    have h := hevery z.2 hz w hw
    refine h.congr (fun k => ?_)
    exact (hpair _).symm

end CKN.Leray

end
