/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedComplexLinearTensorPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedComplexShiftedStokesWeightedNorm

/-!
# Uniqueness for the complex linear regularized mild equation

An exponential time weight makes the Volterra map a contraction on any
finite interval for a fixed continuous physical coefficient path.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A continuous complex physical trajectory solving the linear Volterra
equation with a prescribed continuous coefficient is unique on every finite
interval. -/
theorem regularisedComplexLinearVolterra_unique
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (b : ComplexVectorL2)
    (u v : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (hu : ∀ t : RegularizedMildTimeInterval T,
      u t = heatSemigroup t.1 t.2.1 b -
        ∫ τ in (0 : ℝ)..T,
          if h : 0 < τ ∧ τ < t.1 then
            stokesL2Operator h.1
              (regularisedTensorPhysicalMap ρ ε hε
                (g (regularizedMildTimeClamp T hT (t.1 - τ)))
                (u (regularizedMildTimeClamp T hT (t.1 - τ))))
          else 0)
    (hv : ∀ t : RegularizedMildTimeInterval T,
      v t = heatSemigroup t.1 t.2.1 b -
        ∫ τ in (0 : ℝ)..T,
          if h : 0 < τ ∧ τ < t.1 then
            stokesL2Operator h.1
              (regularisedTensorPhysicalMap ρ ε hε
                (g (regularizedMildTimeClamp T hT (t.1 - τ)))
                (v (regularizedMildTimeClamp T hT (t.1 - τ))))
          else 0) : u = v := by
  let K := regularisedTensorPhysicalConstant ρ ε hε
  have hK : 0 ≤ K := (regularisedTensorPhysicalMap_norm_le ρ ε hε).1
  let A := K * ‖g‖ / Real.sqrt (2 * Real.exp 1) * Real.Gamma (1 / 2)
  obtain ⟨lam, hlam, hlamA⟩ := exists_forcedWeight A
  let w : C(RegularizedMildTimeInterval T, ComplexVectorL2) :=
    ⟨fun q => Real.exp (-lam * q.1) • (u - v) q,
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_subtype_val)).smul (u - v).continuous⟩
  let F := regularisedComplexLinearTensorPath ρ ε hε T hT g u
  let G := regularisedComplexLinearTensorPath ρ ε hε T hT g v
  let D := regularisedComplexLinearTensorPath ρ ε hε T hT g (u - v)
  let Cu := K * ‖g‖ * ‖u‖
  let Cv := K * ‖g‖ * ‖v‖
  have hCu : 0 ≤ Cu := by dsimp [Cu]; positivity
  have hCv : 0 ≤ Cv := by dsimp [Cv]; positivity
  have hFcont : Continuous F :=
    regularisedComplexLinearTensorPath_continuous ρ ε hε T hT g u
  have hGcont : Continuous G :=
    regularisedComplexLinearTensorPath_continuous ρ ε hε T hT g v
  have hFC : ∀ s, ‖F s‖ ≤ Cu :=
    regularisedComplexLinearTensorPath_norm_le
      ρ ε hε T hT g u ‖g‖ (norm_nonneg g)
        (fun q => g.norm_coe_le_norm q)
  have hGC : ∀ s, ‖G s‖ ≤ Cv :=
    regularisedComplexLinearTensorPath_norm_le
      ρ ε hε T hT g v ‖g‖ (norm_nonneg g)
        (fun q => g.norm_coe_le_norm q)
  have hFint (t : ℝ) : IntervalIntegrable
      (regularisedComplexShiftedStokesIntegrand F t) volume 0 T :=
    regularisedComplexShiftedStokesIntegrand_intervalIntegrable
      F hFcont Cu hFC hCu T t hT
  have hGint (t : ℝ) : IntervalIntegrable
      (regularisedComplexShiftedStokesIntegrand G t) volume 0 T :=
    regularisedComplexShiftedStokesIntegrand_intervalIntegrable
      G hGcont Cv hGC hCv T t hT
  have hDpoint (t τ : ℝ) :
      regularisedComplexShiftedStokesIntegrand D t τ =
        regularisedComplexShiftedStokesIntegrand F t τ -
          regularisedComplexShiftedStokesIntegrand G t τ := by
    by_cases h : 0 < τ ∧ τ < t
    · simp only [regularisedComplexShiftedStokesIntegrand, dite_eq_left h]
      change (regularisedStokesL2CLM h.1) (D (t - τ)) =
        (regularisedStokesL2CLM h.1) (F (t - τ)) -
          (regularisedStokesL2CLM h.1) (G (t - τ))
      have hsub := regularisedComplexLinearTensorPath_sub
        ρ ε hε T hT g u v (t - τ)
      change D (t - τ) = F (t - τ) - G (t - τ) at hsub
      rw [hsub]
      exact map_sub (regularisedStokesL2CLM h.1) _ _
    · simp [regularisedComplexShiftedStokesIntegrand, h]
  have hDintegral (t : ℝ) :
      (∫ τ in (0 : ℝ)..T,
        regularisedComplexShiftedStokesIntegrand D t τ) =
        (∫ τ in (0 : ℝ)..T,
          regularisedComplexShiftedStokesIntegrand F t τ) -
          ∫ τ in (0 : ℝ)..T,
            regularisedComplexShiftedStokesIntegrand G t τ := by
    calc
      _ = ∫ τ in (0 : ℝ)..T,
          (regularisedComplexShiftedStokesIntegrand F t τ -
            regularisedComplexShiftedStokesIntegrand G t τ) := by
              congr 1
              funext τ
              exact hDpoint t τ
      _ = _ := intervalIntegral.integral_sub (hFint t) (hGint t)
  have hweightPoint (q : RegularizedMildTimeInterval T) :
      ‖(u - v) q‖ ≤ ‖w‖ * Real.exp (lam * q.1) := by
    have hnorm : ‖w q‖ =
        Real.exp (-lam * q.1) * ‖(u - v) q‖ := by
      change ‖Real.exp (-lam * q.1) • (u - v) q‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      ‖(u - v) q‖ = Real.exp (lam * q.1) * ‖w q‖ := by
        rw [hnorm, ← mul_assoc, ← Real.exp_add]
        rw [show lam * q.1 + -lam * q.1 = 0 by ring, Real.exp_zero, one_mul]
      _ ≤ Real.exp (lam * q.1) * ‖w‖ :=
        mul_le_mul_of_nonneg_left (w.norm_coe_le_norm q)
          (Real.exp_pos _).le
      _ = ‖w‖ * Real.exp (lam * q.1) := mul_comm _ _
  let M := K * ‖g‖ * ‖w‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hDweight (s : ℝ) (hs0 : 0 ≤ s) (hsT : s ≤ T) :
      ‖D s‖ ≤ M * Real.exp (lam * s) := by
    let q : RegularizedMildTimeInterval T := ⟨s, hs0, hsT⟩
    have hclamp := regularizedMildTimeClamp_eq_of_mem T hT ⟨hs0, hsT⟩
    change ‖regularisedTensorPhysicalMap ρ ε hε
      (g (regularizedMildTimeClamp T hT s))
      ((u - v) (regularizedMildTimeClamp T hT s))‖ ≤ _
    rw [hclamp]
    have hKbound := (regularisedTensorPhysicalMap_norm_le ρ ε hε).2
    have hcoef :
        ‖regularisedTensorPhysicalMap ρ ε hε‖ * ‖g q‖ ≤ K * ‖g‖ := by
      calc
        _ ≤ K * ‖g q‖ :=
          mul_le_mul_of_nonneg_right hKbound (norm_nonneg (g q))
        _ ≤ K * ‖g‖ :=
          mul_le_mul_of_nonneg_left (g.norm_coe_le_norm q) hK
    calc
      ‖regularisedTensorPhysicalMap ρ ε hε (g q) ((u - v) q)‖ ≤
          ‖regularisedTensorPhysicalMap ρ ε hε‖ * ‖g q‖ * ‖(u - v) q‖ :=
        (regularisedTensorPhysicalMap ρ ε hε).le_opNorm₂ _ _
      _ ≤ (K * ‖g‖) * ‖(u - v) q‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ (K * ‖g‖) * (‖w‖ * Real.exp (lam * s)) :=
        mul_le_mul_of_nonneg_left (hweightPoint q)
          (mul_nonneg hK (norm_nonneg g))
      _ = M * Real.exp (lam * s) := by dsimp [M]; ring
  have hpoint (q : RegularizedMildTimeInterval T) :
      ‖w q‖ ≤ A * lam ^ (-(1 / 2 : ℝ)) * ‖w‖ := by
    have hu' : u q = heatSemigroup q.1 q.2.1 b -
        ∫ τ in (0 : ℝ)..T,
          regularisedComplexShiftedStokesIntegrand F q.1 τ := by
      simpa only [F, regularisedComplexShiftedStokesIntegrand,
        regularisedComplexLinearTensorPath] using hu q
    have hv' : v q = heatSemigroup q.1 q.2.1 b -
        ∫ τ in (0 : ℝ)..T,
          regularisedComplexShiftedStokesIntegrand G q.1 τ := by
      simpa only [G, regularisedComplexShiftedStokesIntegrand,
        regularisedComplexLinearTensorPath] using hv q
    have hdiff : u q - v q =
        -(∫ τ in (0 : ℝ)..T,
          regularisedComplexShiftedStokesIntegrand D q.1 τ) := by
      rw [hu', hv', hDintegral]
      abel
    have hstokes := regularisedComplexShiftedStokesIntegral_weighted_norm_le
      D T q.1 M lam hT q.2.2 hM hlam hDweight
    have hnorm : ‖w q‖ =
        Real.exp (-lam * q.1) * ‖u q - v q‖ := by
      change ‖Real.exp (-lam * q.1) • (u - v) q‖ = _
      rw [ContinuousMap.sub_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-lam * q.1) * Real.exp (lam * q.1) = 1 := by
      rw [← Real.exp_add]
      rw [show -lam * q.1 + lam * q.1 = 0 by ring, Real.exp_zero]
    calc
      ‖w q‖ = Real.exp (-lam * q.1) * ‖u q - v q‖ := hnorm
      _ = Real.exp (-lam * q.1) *
          ‖∫ τ in (0 : ℝ)..T,
            regularisedComplexShiftedStokesIntegrand D q.1 τ‖ := by
              rw [hdiff, norm_neg]
      _ ≤ Real.exp (-lam * q.1) *
          (M / Real.sqrt (2 * Real.exp 1) * Real.exp (lam * q.1) *
            (lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2))) :=
        mul_le_mul_of_nonneg_left hstokes (Real.exp_pos _).le
      _ = A * lam ^ (-(1 / 2 : ℝ)) * ‖w‖ := by
        dsimp [A, M]
        rw [show Real.exp (-lam * q.1) *
          ((K * ‖g‖ * ‖w‖) / Real.sqrt (2 * Real.exp 1) *
            Real.exp (lam * q.1) *
              (lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2))) =
          (Real.exp (-lam * q.1) * Real.exp (lam * q.1)) *
            ((K * ‖g‖ * ‖w‖) / Real.sqrt (2 * Real.exp 1) *
              (lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2))) by ring,
          hexp]
        ring
  have hsup : ‖w‖ ≤ A * lam ^ (-(1 / 2 : ℝ)) * ‖w‖ := by
    apply (w.norm_le (mul_nonneg (by positivity) (norm_nonneg w))).2
    exact hpoint
  have hhalf : ‖w‖ ≤ (1 / 2 : ℝ) * ‖w‖ :=
    hsup.trans (mul_le_mul_of_nonneg_right hlamA (norm_nonneg w))
  have hwzero : w = 0 := by
    apply norm_eq_zero.mp
    linarith only [hhalf, norm_nonneg w]
  ext1 q
  have hq : w q = 0 := by rw [hwzero]; rfl
  have hnorm : ‖w q‖ =
      Real.exp (-lam * q.1) * ‖u q - v q‖ := by
    change ‖Real.exp (-lam * q.1) • (u - v) q‖ = _
    rw [ContinuousMap.sub_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hz : Real.exp (-lam * q.1) * ‖u q - v q‖ = 0 := by
    rw [← hnorm, hq, norm_zero]
  have hnormzero : ‖u q - v q‖ = 0 :=
    (mul_eq_zero.mp hz).resolve_left (Real.exp_pos _).ne'
  have hsub : u q - v q = 0 := norm_eq_zero.mp hnormzero
  exact sub_eq_zero.mp hsub

end CKN.Leray

end
