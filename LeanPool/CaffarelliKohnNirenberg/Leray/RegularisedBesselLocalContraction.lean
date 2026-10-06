/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalBall
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesIntegrability

/-!
# Contraction of the local complete Sobolev mild map

The translated Abel integral makes the complete H²ᵏ mild map a
strict contraction on the chosen closed trajectory ball.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- On the chosen complete H²ᵏ trajectory ball, the local mild map
contracts differences by a factor of one half. -/
theorem regularisedBesselLocalMap_contraction
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (u v : C(RegularizedMildTimeInterval
      (regularisedBesselLocalLifespan ρ ε hε k b),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hu : ‖u‖ ≤ regularisedBesselLocalRadius k b)
    (hv : ‖v‖ ≤ regularisedBesselLocalRadius k b) :
    ‖regularisedBesselLocalMap ρ ε hε k b
        (regularisedBesselLocalLifespan ρ ε hε k b)
        (regularisedBesselLocalLifespan_pos ρ ε hε k b).le u -
      regularisedBesselLocalMap ρ ε hε k b
        (regularisedBesselLocalLifespan ρ ε hε k b)
        (regularisedBesselLocalLifespan_pos ρ ε hε k b).le v‖ ≤
      (1 / 2 : ℝ) * ‖u - v‖ := by
  let T := regularisedBesselLocalLifespan ρ ε hε k b
  let hT : 0 ≤ T := (regularisedBesselLocalLifespan_pos ρ ε hε k b).le
  let R := regularisedBesselLocalRadius k b
  let K := regularisedBesselTensorConstant ρ ε hε k
  let F := regularisedBesselClampedTensorPath ρ ε hε k T hT u
  let G := regularisedBesselClampedTensorPath ρ ε hε k T hT v
  let C := K * R ^ 2
  let D := K * (2 * R) * ‖u - v‖
  have hR : 0 ≤ R := by dsimp [R, regularisedBesselLocalRadius]; positivity
  have hK : 0 ≤ K := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  have hC : 0 ≤ C := mul_nonneg hK (sq_nonneg R)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have huPoint : ∀ q, ‖u q‖ ≤ R := (u.norm_le hR).1 hu
  have hvPoint : ∀ q, ‖v q‖ ≤ R := (v.norm_le hR).1 hv
  have hFcont : Continuous F :=
    regularisedBesselClampedTensorPath_continuous ρ ε hε k T hT u
  have hGcont : Continuous G :=
    regularisedBesselClampedTensorPath_continuous ρ ε hε k T hT v
  have hFC : ∀ s, ‖F s‖ ≤ C :=
    regularisedBesselClampedTensorPath_norm_le ρ ε hε k T hT u R hR huPoint
  have hGC : ∀ s, ‖G s‖ ≤ C :=
    regularisedBesselClampedTensorPath_norm_le ρ ε hε k T hT v R hR hvPoint
  have hFGcont : Continuous (fun s => F s - G s) := hFcont.sub hGcont
  have hFGC : ∀ s, ‖F s - G s‖ ≤ D := by
    intro s
    exact regularisedBesselClampedTensorPath_difference_norm_le
      ρ ε hε k T hT u v R huPoint hvPoint s
  have hFint (t : ℝ) : IntervalIntegrable
      (regularisedBesselShiftedStokesIntegrand k F t) volume 0 T :=
    regularisedBesselShiftedStokesIntegrand_intervalIntegrable
      k F hFcont C hFC hC T t hT
  have hGint (t : ℝ) : IntervalIntegrable
      (regularisedBesselShiftedStokesIntegrand k G t) volume 0 T :=
    regularisedBesselShiftedStokesIntegrand_intervalIntegrable
      k G hGcont C hGC hC T t hT
  have hFGpoint (t τ : ℝ) :
      regularisedBesselShiftedStokesIntegrand k (fun s => F s - G s) t τ =
        regularisedBesselShiftedStokesIntegrand k F t τ -
          regularisedBesselShiftedStokesIntegrand k G t τ := by
    by_cases h : 0 < τ ∧ τ < t
    · simp only [regularisedBesselShiftedStokesIntegrand, dite_eq_left h]
      exact map_sub (regularisedBesselStokesOperator h.1 k) _ _
    · simp [regularisedBesselShiftedStokesIntegrand, h]
  have hFGintegral (t : ℝ) :
      (∫ τ in (0 : ℝ)..T,
        regularisedBesselShiftedStokesIntegrand k (fun s => F s - G s) t τ) =
        (∫ τ in (0 : ℝ)..T,
          regularisedBesselShiftedStokesIntegrand k F t τ) -
          ∫ τ in (0 : ℝ)..T,
            regularisedBesselShiftedStokesIntegrand k G t τ := by
    calc
      _ = ∫ τ in (0 : ℝ)..T,
          (regularisedBesselShiftedStokesIntegrand k F t τ -
            regularisedBesselShiftedStokesIntegrand k G t τ) := by
              congr 1
              funext τ
              exact hFGpoint t τ
      _ = _ := intervalIntegral.integral_sub (hFint t) (hGint t)
  have hpointwise : ∀ t : RegularizedMildTimeInterval T,
      ‖regularisedBesselLocalMap ρ ε hε k b T hT u t -
        regularisedBesselLocalMap ρ ε hε k b T hT v t‖ ≤
        (1 / 2 : ℝ) * ‖u - v‖ := by
    intro t
    rw [regularisedBesselLocalMap_apply, regularisedBesselLocalMap_apply]
    have hcancel :
        (regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b -
          ∫ τ in (0 : ℝ)..T, regularisedBesselShiftedStokesIntegrand k F t.1 τ) -
        (regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b -
          ∫ τ in (0 : ℝ)..T, regularisedBesselShiftedStokesIntegrand k G t.1 τ) =
        -((∫ τ in (0 : ℝ)..T, regularisedBesselShiftedStokesIntegrand k F t.1 τ) -
          ∫ τ in (0 : ℝ)..T, regularisedBesselShiftedStokesIntegrand k G t.1 τ) := by
      abel
    rw [hcancel, norm_neg, ← hFGintegral]
    have hInt := regularisedBesselShiftedStokesIntegral_norm_le
      k (fun s => F s - G s) D hFGC hD T t.1 hT
    have hParam := regularisedBesselLocalLifespan_contraction_bound ρ ε hε k b
    calc
      ‖∫ τ in (0 : ℝ)..T,
          regularisedBesselShiftedStokesIntegrand k (fun s => F s - G s) t.1 τ‖ ≤
        2 * (D / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T := hInt
      _ = (2 * (K / Real.sqrt (2 * Real.exp 1)) * (2 * R) *
          Real.sqrt T) * ‖u - v‖ := by dsimp [D]; ring
      _ ≤ (1 / 2 : ℝ) * ‖u - v‖ :=
        mul_le_mul_of_nonneg_right hParam (norm_nonneg _)
  apply ((regularisedBesselLocalMap ρ ε hε k b T hT u -
    regularisedBesselLocalMap ρ ε hε k b T hT v).norm_le
      (by positivity : 0 ≤ (1 / 2 : ℝ) * ‖u - v‖)).2
  intro t
  simpa using hpointwise t

end CKN.Leray

end
