/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsCutoff
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitInitialTail
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsWeakIdentity
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureOperator
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Reg Tails Main

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

theorem regTails_eLpNorm_euclidean_eq_spatialField
    (a : Vec3 → Vec3) (ha : MemLp a (2 : ℝ≥0∞) volume) :
    eLpNorm (fun x : Vec3 => vec3EuclideanNorm (a x)) 2 volume =
      eLpNorm (regUniformSpatialField a) 2 volume := by
  have hpres : MeasurePreserving (WithLp.ofLp : L2Vec3 → Vec3) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have hfield : MemLp (regUniformSpatialField a) 2 volume := by
    have hcoord : MemLp (fun x : L2Vec3 => a (WithLp.ofLp x)) 2 volume :=
      ha.comp_measurePreserving hpres
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hnormcont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm
  have hscalar : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (a x)) volume :=
    hnormcont.comp_aestronglyMeasurable ha.aestronglyMeasurable
  have hcomp : eLpNorm
      (fun x : L2Vec3 => vec3EuclideanNorm (a (WithLp.ofLp x))) 2 volume =
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (a x)) 2 volume :=
    eLpNorm_comp_measurePreserving hscalar hpres
  calc
    eLpNorm (fun x : Vec3 => vec3EuclideanNorm (a x)) 2 volume =
        eLpNorm (fun x : L2Vec3 => vec3EuclideanNorm (a (WithLp.ofLp x))) 2 volume :=
      hcomp.symm
    _ = eLpNorm (fun x : L2Vec3 => ‖regUniformSpatialField a x‖) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [] with x
      change vec3EuclideanNorm (a (WithLp.ofLp x)) =
        ‖WithLp.toLp 2 (a (WithLp.ofLp x))‖
      rw [vec3EuclideanNorm_eq_l2]
    _ = eLpNorm (regUniformSpatialField a) 2 volume :=
      eLpNorm_norm (regUniformSpatialField a) hfield.aestronglyMeasurable

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


variable (hregLocalEnergy : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
    (ε : ℝ) (hε : 0 < ε) (ψ : ParabolicPoint → ℝ),
    ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ (Ioi 0) →
    2 * ∫ z in spaceTimeSet Set.univ (Ioi 0),
        spatialGradientSq (uε a ha ε)
          (fun z i j => spatialPartial (fun y => uε a ha ε y i) j z) z * ψ z =
      ∫ z in spaceTimeSet Set.univ (Ioi 0),
        (vec3EuclideanNorm (uε a ha ε z)) ^ (2 : ℕ) *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
          ∑ i : Fin 3,
            ((vec3EuclideanNorm (uε a ha ε z)) ^ (2 : ℕ) *
                regUniformMollifiedVelocity ρ ε hε (uε a ha ε) z i +
              2 * pε a ha ε z * uε a ha ε z i) * spatialPartial ψ i z)

/- The contract projection below is shared by the energy and cutoff
calculations for `lem:reg-tails`. -/
theorem regTails_contract_slice_memLp
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
    (hε : 0 < ε),
    let u := uε a ha ε
    let p := pε a ha ε
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => u y i) j z
    let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
    let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
    let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
    (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t.1))
          (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → IsWeakDivFreeL2 (fun x => u (x, t))) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet Set.univ (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
       (spaceTimeSet Set.univ (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet Set.univ (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet Set.univ (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet Set.univ (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
        (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
        (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
        (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
    (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i - (∑ j : Fin 3, DD z i j j) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * D z i j) +
        Dp z i = 0) ∧
    (∀ t : ℝ, 0 < t →
      ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
          u (x, t) j) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => p (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF i j).toLp
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
        2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun x : Vec3 => uε a ha ε (x, t)) 2 volume := by
  rcases hregularised a ha ε hε with
    ⟨⟨hSlice, _hSliceContinuous, _hInitial, _hDivFree⟩,
      _hUcont, _hDcont, _hDDcont, _hDtcont, _hPcont, _hDpcont,
      _hC1, _hDdiff, _hPdiff, _hBounds, _hLocalLp, _hEquation,
      _hPressure, _hEnergy⟩
  exact hSlice t ht

/- The regularized contract supplies slice energy, global dissipation and
almost every `H¹` slice with the explicit gradient from the equation. -/
theorem regTails_contract_energy_bounds
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
    (hε : 0 < ε),
    let u := uε a ha ε
    let p := pε a ha ε
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => u y i) j z
    let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
    let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
    let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
    (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t.1))
          (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → IsWeakDivFreeL2 (fun x => u (x, t))) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet Set.univ (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
      (spaceTimeSet Set.univ (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
       (spaceTimeSet Set.univ (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet Set.univ (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet Set.univ (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet Set.univ (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
        (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
        (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
        (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict (spaceTimeSet Set.univ (Ioo δ T)))) ∧
    (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i - (∑ j : Fin 3, DD z i j j) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * D z i j) +
        Dp z i = 0) ∧
    (∀ t : ℝ, 0 < t →
      ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
          u (x, t) j) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => p (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF i j).toLp
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
        2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) :
    (∀ t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice (uε a ha ε) t) 2 volume ^ (2 : ℕ) ≤
        eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ)) ∧
    2 * (∫⁻ z, ENNReal.ofReal (spatialGradientSq (uε a ha ε)
      (fun z i j => spatialPartial (fun y => uε a ha ε y i) j z) z)
      ∂regUniformPositiveTimeMeasure) ≤
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) ∧
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ h : ∀ _i : Fin 3, CKN.H1Function (Set.univ : Set Vec3),
        (∀ i x, (h i).toFun x = uε a ha ε (x, t) i) ∧
        (∀ i x j, (h i).grad x j =
          spatialPartial (fun y => uε a ha ε y i) j (x, t)) := by
  rcases hregularised a ha ε hε with
    ⟨⟨hSlice, _hSliceContinuous, _hInitial, _hDivFree⟩,
      _hUcont, hDcont, _hDDcont, _hDtcont, _hPcont, _hDpcont,
      hC1, _hDdiff, _hPdiff, _hBounds, _hLocalLp, _hEquation,
      _hPressure, hR5⟩
  let u : ParabolicPoint → Vec3 := uε a ha ε
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y => u y i) j z
  have hSpatialC1 : ∀ t : ℝ, 0 < t → ∀ i : Fin 3,
      ContDiff ℝ 1 (fun x : Vec3 => u (x, t) i) :=
    lerayLimit_contDiff_spatial_slices u
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))) hC1
      (fun t ht x => ⟨Set.mem_univ _, ht⟩)
  have hDerivative : ∀ t, 0 < t → ∀ x i j,
      (fderiv ℝ (fun y : Vec3 => u (y, t) i) x) (basisVec j) = D (x, t) i j := by
    intro t ht x i j
    rfl
  have hR5' : ∀ t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
        2 volume ^ (2 : ℕ) := by
    intro t ht
    exact hR5 t ht
  have hDcont' : ∀ i j, ContinuousOn (fun z : ParabolicPoint => D z i j)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))) := by
    intro i j
    simpa [D, u] using hDcont i j
  simpa [u, D] using regTails_energy_bounds ρ ε hε a u D hR5'
    ha.1 hDcont' hSlice hSpatialC1 hDerivative

end CKN.Leray

end
