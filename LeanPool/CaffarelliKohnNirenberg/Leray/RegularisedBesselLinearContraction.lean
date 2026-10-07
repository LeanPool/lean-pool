/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearLocalMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselUniformEnergyStep
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesNorm

/-!
# Global contraction of the linear complete Sobolev mild map

With a fixed bounded physical L² coefficient, the complete Sobolev mild
map contracts on the entire trajectory Banach space over the uniform time step.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The linear complete Sobolev mild map is a one-half contraction
on the uniform energy time step, without a Sobolev norm ball. -/
theorem regularisedBesselLinearLocalMap_contraction
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (B : ℝ) (hB : 0 ≤ B)
    (g : C(RegularizedMildTimeInterval
      (regularisedBesselUniformEnergyStep ρ ε hε k B), ComplexVectorL2))
    (hg : ∀ q, ‖g q‖ ≤ B)
    (v w : C(RegularizedMildTimeInterval
      (regularisedBesselUniformEnergyStep ρ ε hε k B),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    ‖regularisedBesselLinearLocalMap ρ ε hε k b
        (regularisedBesselUniformEnergyStep ρ ε hε k B)
        (regularisedBesselUniformEnergyStep_pos ρ ε hε k B hB).le
        g B hB hg v -
      regularisedBesselLinearLocalMap ρ ε hε k b
        (regularisedBesselUniformEnergyStep ρ ε hε k B)
        (regularisedBesselUniformEnergyStep_pos ρ ε hε k B hB).le
        g B hB hg w‖ ≤ (1 / 2 : ℝ) * ‖v - w‖ := by
  let T := regularisedBesselUniformEnergyStep ρ ε hε k B
  let hT : 0 ≤ T := (regularisedBesselUniformEnergyStep_pos ρ ε hε k B hB).le
  let K := regularisedBesselTensorConstant ρ ε hε k
  let F := regularisedBesselLinearTensorPath ρ ε hε k T hT g v
  let G := regularisedBesselLinearTensorPath ρ ε hε k T hT g w
  let Cv := K * B * ‖v‖
  let Cw := K * B * ‖w‖
  let D := K * B * ‖v - w‖
  have hK : 0 ≤ K := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  have hCv : 0 ≤ Cv := mul_nonneg (mul_nonneg hK hB) (norm_nonneg v)
  have hCw : 0 ≤ Cw := mul_nonneg (mul_nonneg hK hB) (norm_nonneg w)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hK hB) (norm_nonneg (v - w))
  have hFcont : Continuous F :=
    regularisedBesselLinearTensorPath_continuous ρ ε hε k T hT g v
  have hGcont : Continuous G :=
    regularisedBesselLinearTensorPath_continuous ρ ε hε k T hT g w
  have hFC : ∀ s, ‖F s‖ ≤ Cv :=
    regularisedBesselLinearTensorPath_norm_le ρ ε hε k T hT g v B hB hg
  have hGC : ∀ s, ‖G s‖ ≤ Cw :=
    regularisedBesselLinearTensorPath_norm_le ρ ε hε k T hT g w B hB hg
  have hFGC : ∀ s, ‖F s - G s‖ ≤ D := by
    intro s
    exact regularisedBesselLinearTensorPath_difference_norm_le
      ρ ε hε k T hT g v w B hB hg s
  have hFint (t : ℝ) : IntervalIntegrable
      (regularisedBesselShiftedStokesIntegrand k F t) volume 0 T :=
    regularisedBesselShiftedStokesIntegrand_intervalIntegrable
      k F hFcont Cv hFC hCv T t hT
  have hGint (t : ℝ) : IntervalIntegrable
      (regularisedBesselShiftedStokesIntegrand k G t) volume 0 T :=
    regularisedBesselShiftedStokesIntegrand_intervalIntegrable
      k G hGcont Cw hGC hCw T t hT
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
      ‖regularisedBesselLinearLocalMap ρ ε hε k b T hT g B hB hg v t -
        regularisedBesselLinearLocalMap ρ ε hε k b T hT g B hB hg w t‖ ≤
        (1 / 2 : ℝ) * ‖v - w‖ := by
    intro t
    rw [regularisedBesselLinearLocalMap_apply,
      regularisedBesselLinearLocalMap_apply]
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
    calc
      ‖∫ τ in (0 : ℝ)..T,
          regularisedBesselShiftedStokesIntegrand k
            (fun s => F s - G s) t.1 τ‖ ≤
        2 * (D / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T := hInt
      _ = (2 * (K * B / Real.sqrt (2 * Real.exp 1)) *
          Real.sqrt T) * ‖v - w‖ := by dsimp [D]; ring
      _ ≤ (1 / 2 : ℝ) * ‖v - w‖ :=
        mul_le_mul_of_nonneg_right
          (regularisedBesselUniformEnergyStep_small ρ ε hε k B hB)
          (norm_nonneg _)
  apply ((regularisedBesselLinearLocalMap ρ ε hε k b T hT g B hB hg v -
    regularisedBesselLinearLocalMap ρ ε hε k b T hT g B hB hg w).norm_le
      (by positivity : 0 ≤ (1 / 2 : ℝ) * ‖v - w‖)).2
  intro t
  simpa using hpointwise t

end CKN.Leray

end
