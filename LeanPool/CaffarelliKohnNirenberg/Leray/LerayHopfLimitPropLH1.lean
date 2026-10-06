/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropClass
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpace
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative

/-!
# Leray Hopf Limit Prop LH1

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN

noncomputable section

namespace CKN.Leray

/-- All six (LH1) properties follow from the slab limit fields, the global
weak slice convergence, the exact regularized energy identity, and its
regularized divergence-free slices. -/
theorem lerayHopfLimit_LH1_of_limitData
    (T : ℝ)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (ρ : RegMollifierProfile) (εseq : ℕ → ℝ) (σ : ℕ → ℕ)
    (hεpositive : ∀ n, 0 < εseq (σ n))
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (U : ℕ → ParabolicPoint → Vec3) (Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (humeas : AEStronglyMeasurable u
      (volume.restrict (CKN.spaceTimeSet Set.univ (Set.Ioo 0 T))))
    (hDmeas : AEStronglyMeasurable Du
      (volume.restrict (CKN.spaceTimeSet Set.univ (Set.Ioo 0 T))))
    (hu : MemLp u 2
      (volume.restrict (CKN.spaceTimeSet Set.univ (Set.Ioo 0 T))))
    (hDu : MemLp Du 2
      (volume.restrict (CKN.spaceTimeSet Set.univ (Set.Ioo 0 T))))
    (hgradient : ∀ᵐ s ∂(volume.restrict (Set.Ioo 0 T)), ∀ i : Fin 3,
      HasWeakGradientOn Set.univ (fun x => u (x,s) i)
        (fun x => Du (x,s) i))
    (hdivU : ∀ n t, 0 ≤ t → IsWeakDivFreeL2 (fun x => U n (x,t)))
    (hweakSlice : ∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
      MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3, U n (x,t) i * w x i)
        atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x,t) i * w x i)))
    (hsliceU : ∀ n t, 0 ≤ t →
      MemLp (fun x : Vec3 => U n (x,t)) 2 volume)
    (hR5 : ∀ n t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice (U n) t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation (U n) (Dseq n) t =
        eLpNorm (regMollifyVector ρ (εseq (σ n)) (hεpositive n)
          (regUniformSpatialField a)) 2 volume ^ (2 : ℕ)) :
    AEStronglyMeasurable u
      (volume.restrict (CKN.spaceTimeSet Set.univ (Set.Ioo 0 T))) ∧
    AEStronglyMeasurable Du
      (volume.restrict (CKN.spaceTimeSet Set.univ (Set.Ioo 0 T))) ∧
    essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x,s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Set.Ioo 0 T)) < ⊤ ∧
    (∫⁻ z in CKN.spaceTimeSet Set.univ (Set.Ioo 0 T),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    (∀ᵐ s ∂(volume.restrict (Set.Ioo 0 T)), ∀ i : Fin 3,
      HasWeakGradientOn Set.univ (fun x => u (x,s) i)
        (fun x => Du (x,s) i)) ∧
    (∀ᵐ s ∂(volume.restrict (Set.Ioo 0 T)),
      ∀ ψ : CKN.WeakTestFunction Set.univ,
        ∫ x : Vec3, ∑ i : Fin 3, u (x,s) i * ψ.partialDeriv i x = 0) := by
  have hA : MemLp (regUniformSpatialField a) 2 volume :=
    lerayHopfLimit_initialField_memLp a ha.1
  let B : ℝ≥0∞ := eLpNorm (regUniformSpatialField a) 2 volume
  have hB : B < ⊤ := by
    exact (hA.eLpNorm_lt_top)
  have hsliceTarget : ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 T)),
      MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x,t))) 2 volume :=
    lerayHopfLimit_ae_slice_memLp_of_spaceTime_memLp T u hu
  have hUmem (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
      MemLp (regUniformVelocitySlice (U n) t) 2 volume := by
    have hcoordinate : MemLp
        (fun x : L2Vec3 => U n (WithLp.ofLp x,t)) 2 volume :=
      (hsliceU n t ht).comp_measurePreserving
        (PiLp.volume_preserving_ofLp (Fin 3))
    have htoLp : MemLp
        (fun x : L2Vec3 => WithLp.toLp 2 (U n (WithLp.ofLp x,t))) 2 volume :=
      hcoordinate.continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    change MemLp (fun x : L2Vec3 =>
      WithLp.toLp 2 (U n (WithLp.ofLp x,t))) 2 volume at htoLp
    change MemLp (fun x : L2Vec3 =>
      WithLp.toLp 2 (U n (WithLp.ofLp x,t))) 2 volume
    exact htoLp
  have hUbound (n : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
      eLpNorm (fun x : Vec3 => WithLp.toLp 2 (U n (x,t))) 2 volume ≤ B := by
    exact lerayHopfLimit_regSlice_uniformBound ρ (εseq (σ n)) (hεpositive n)
      a (U n) (Dseq n) hA (fun s hs => hUmem n s hs)
      (hR5 n) t (le_of_lt ht.1)
  have hcore := lerayHopfLimit_LH1_core T u Du U humeas hDmeas hu hDu
    hgradient hdivU hweakSlice
  have hUtoLp (n : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
      MemLp (fun x : Vec3 => WithLp.toLp 2 (U n (x,t))) 2 volume :=
    (hsliceU n t (le_of_lt ht.1)).continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  refine ⟨humeas, hDmeas, ?_, hcore.2.2.1, hcore.2.2.2.1,
    hcore.2.2.2.2⟩
  exact lerayHopfLimit_slice_energy_essSup T u U B hB hsliceTarget
    hUtoLp hUbound hweakSlice

end CKN.Leray

end
