/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution

/-!
# Finite-energy weak solutions with a pressure

The comparison argument of `lem:pv-serrin-uniqueness` uses a solution only
through its energy class, its weak gradient, its divergence condition, a
momentum identity with a pressure in `L^{5/3}`, the continuity of its pairings
with smooth compactly supported fields, and its initial pairings. This file
names that class; Leray–Hopf solutions and the short-time solution of
`prop:pv-local-solution` both belong to it.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A finite-energy weak solution of the Navier–Stokes equations on
`ℝ³ × (0, T)` with pressure `p` and datum `a`, in the class used by the
weak–strong comparison `lem:pv-serrin-uniqueness`. -/
structure IsSerrinWeakSolution (T : ℝ) (a : Vec3 → Vec3)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) : Prop where
  pos : 0 < T
  datum : MemLp a 2 volume
  meas_u : AEStronglyMeasurable u
    (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))
  meas_Du : AEStronglyMeasurable Du
    (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))
  slice_bound : essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
    (volume.restrict (Ioo 0 T)) < ⊤
  energy : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
    ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤
  weak_grad : ∀ᵐ s ∂(volume.restrict (Ioo 0 T)), ∀ i : Fin 3,
    HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u (x, s) i) (fun x => Du (x, s) i)
  div_free : ∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
    ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * ψ.partialDeriv i x = 0
  pressure : MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
    (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))
  momentum : ∀ φ : ParabolicPoint → Vec3,
    φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => φ y i) j z
        - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
        - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0
  weak_cont : ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ContinuousOn (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * ψ x i) (Icc 0 T)
  initial : ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    (∫ x : Vec3, ∑ i : Fin 3, u (x, 0) i * ψ x i) = ∫ x : Vec3, ∑ i : Fin 3, a x i * ψ x i

end ESS
