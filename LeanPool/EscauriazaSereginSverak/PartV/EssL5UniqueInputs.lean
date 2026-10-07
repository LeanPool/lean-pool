/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.EssL5Assembly
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionIteration
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionBundle

/-!
# The `L⁵` bound and uniqueness theorem

The short-time solution of `prop:pv-local-solution` from a solenoidal datum in
`L² ∩ L³`, and `thm:ess-l5-unique` with the local regularity theorem
`thm:ess-local` as its only input.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- `prop:pv-local-solution`: a solenoidal datum in `L² ∩ L³` generates a
finite-energy weak solution with pressure on a short slab, lying in space-time
`L⁵` there. -/
theorem pvLocalSolution {a : Vec3 → Vec3} (ha : IsInJ a)
    (ha3 : MemLp a (ENNReal.ofReal (3 : ℝ)) volume) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ U : ParabolicPoint → Vec3, ∃ DU : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ, IsSerrinWeakSolution σ a U DU p ∧
        MemLp U (ENNReal.ofReal 5)
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 σ))) := by
  have ha3' : MemLp a 3 volume := by
    have e3 : ENNReal.ofReal (3 : ℝ) = 3 := by simp
    rw [e3] at ha3
    exact ha3
  obtain ⟨σ, hσ, U, hU5, hU4, hfix, hinit⟩ := pvLocal_fixedPoint ha.1 ha3'
  obtain ⟨DU, p, hU⟩ := pvLocal_bundle ha hσ hU5 hU4 hfix hinit
  exact ⟨σ, hσ, U, DU, p, hU, hU5⟩

/-- `thm:ess-l5-unique`, with the local regularity theorem `thm:ess-local` as
its only input: a Leray–Hopf solution in `L^∞ L³` lies in space-time `L⁵` and
is the only Leray–Hopf solution with its datum. -/
theorem essL5Unique_of_inputs
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
              (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))) w γ) :
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
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))] u :=
  essL5Unique_of_localSolution hE1 fun _ ha ha3 => pvLocalSolution ha ha3

end ESS

end
