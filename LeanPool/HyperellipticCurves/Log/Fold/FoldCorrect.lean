/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldChain
public import LeanPool.HyperellipticCurves.Log.Fold.FoldNum

import LeanPool.HyperellipticCurves.Log.Fold.Isobaric

/-!
# Correctness of the numerator fold

This file identifies the numerator fold recursion `ChabautyColeman.foldNum` with the
denominator-scaled honest fold `ChabautyColeman.foldChain` (at the computed scalars
`ChabautyColeman.foldGenH`), completing the Lean content of `lem:fold-universal`'s
denominator clause: as long as every earlier step-condition numerator
`ChabautyColeman.foldCondNum` is nonzero, the accumulated denominator is nonzero, all
three numerator components are the denominator-scaled honest values, and the honest pair
satisfies the fold invariants (`ChabautyColeman.isScaledState_foldNum`, invariant pack
`ChabautyColeman.IsScaledState`).

The composed Mumford divisibility of each step is *derived* from the step conditions —
`ChabautyColeman.foldStep_dvd_disjoint` at a disjoint step,
`ChabautyColeman.foldStep_dvd_double` at the doubling step; both take the scalar's
defining identity as a certificate hypothesis, so the whole development is division-free —
which is what makes the honest fold defined at any instance whose condition numerators
are certified nonzero (the engine direction). Conversely, at an instance where the honest
fold is certified (the cusp), the per-stage condition identity
`ChabautyColeman.foldCondNum_eq_den_mul` converts honest nonvanishing into nonvanishing of
the numerators (the `P_q ≠ 0` direction).

## Main statements

* `ChabautyColeman.IsScaledState`: the correctness invariant.
* `ChabautyColeman.IsScaledState.step`: one numerator step preserves it.
* `ChabautyColeman.isScaledState_foldNum`: the invariant holds at every stage, from the
  nonvanishing of the earlier step-condition numerators.
* `ChabautyColeman.foldCond`, `ChabautyColeman.foldCondNum_eq_den_mul`: the honest step
  conditions and the per-stage condition identity
  `foldCondNum j = den j · foldCond j`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### Generalities -/

section Helpers

variable {R : Type*} [CommRing R]

/-- `cantorReduce` at the certificate `-1` returns the negated cofactor datum. -/
theorem cantorReduce_neg_one_fst (f u v : R[X]) :
    (cantorReduce f u v (-1)).1 = -cantorCofactor f u v := by
  rw [cantorReduce_fst, map_neg, map_one, neg_one_mul]

theorem cantorReduce_neg_one_snd (f u v : R[X]) :
    (cantorReduce f u v (-1)).2 = (-v) %ₘ (-cantorCofactor f u v) := by
  rw [cantorReduce_snd, map_neg, map_one, neg_one_mul]

/-- A polynomial with a double root: value and derivative vanish. -/
theorem X_sub_C_sq_dvd {q : R[X]} {a : R} (h0 : q.eval a = 0)
    (h1 : q.derivative.eval a = 0) : (X - C a) ^ 2 ∣ q := by
  rcases eq_or_ne q 0 with rfl | hq
  · exact dvd_zero _
  · exact (pow_dvd_pow _ ((one_lt_rootMultiplicity_iff_isRoot hq).mpr ⟨h0, h1⟩)).trans
      (q.pow_rootMultiplicity_dvd a)

/-- The support divides the composed square relation, for every composition scalar. -/
theorem dvd_foldStep_sq_sub {f U V : R[X]} {H : R} (hU : U ∣ V ^ 2 - f) :
    U ∣ (V + C H * U) ^ 2 - f := by
  obtain ⟨k, hk⟩ := hU
  exact ⟨k + (2 * C H * V + C H ^ 2 * U), by linear_combination hk⟩

end Helpers

section FieldHelpers

variable {F : Type*} [Field F]

/-! ### The composed Mumford divisibility from the step conditions -/

variable {f U V : F[X]}

/-- **The composed Mumford divisibility at a disjoint step**: any composition scalar
matching the point value (`H·U(x_P) = y_P - V(x_P)`) makes the composed pair a Mumford
datum again. -/
theorem foldStep_dvd_disjoint {xP yP H : F} (hU : U ∣ V ^ 2 - f) (hUx : U.eval xP ≠ 0)
    (hy : yP ^ 2 = f.eval xP) (hHeq : H * U.eval xP = yP - V.eval xP) :
    U * (X - C xP) ∣ (V + C H * U) ^ 2 - f := by
  have h2 : X - C xP ∣ (V + C H * U) ^ 2 - f := by
    refine dvd_iff_isRoot.mpr ?_
    have h3 : (V + C H * U).eval xP = yP := by
      simp only [eval_add, eval_mul, eval_C]
      linear_combination hHeq
    simp [IsRoot, h3, hy]
  exact (isCoprime_X_sub_C_of_eval_ne_zero hUx).mul_dvd (dvd_foldStep_sq_sub hU) h2

/-- **The composed Mumford divisibility at the doubling step**: at a simple root of the
support matching the point, any composition scalar satisfying the tangency identity
`H·(2y₀U'(x₀)) = f'(x₀) - 2y₀V'(x₀)` makes the composed pair a Mumford datum. -/
theorem foldStep_dvd_double {x₀ y₀ H : F} (hU : U ∣ V ^ 2 - f) (hU0 : U.eval x₀ = 0)
    (hU' : U.derivative.eval x₀ ≠ 0) (hV0 : V.eval x₀ = y₀) (hy : y₀ ^ 2 = f.eval x₀)
    (hHeq : H * (2 * y₀ * U.derivative.eval x₀)
      = f.derivative.eval x₀ - 2 * y₀ * V.derivative.eval x₀) :
    U * (X - C x₀) ∣ (V + C H * U) ^ 2 - f := by
  -- the square of `X - x₀` divides: value and derivative vanish at `x₀`
  have h0 : ((V + C H * U) ^ 2 - f).eval x₀ = 0 := by simp [hV0, hU0, ← hy]
  have hder : ((V + C H * U) ^ 2 - f).derivative.eval x₀ = 0 := by
    simp only [derivative_sub, derivative_sq, derivative_add, derivative_C_mul, eval_sub,
      eval_mul, eval_add, eval_C, hV0, hU0]
    linear_combination hHeq
  have hsq : (X - C x₀) ^ 2 ∣ (V + C H * U) ^ 2 - f := X_sub_C_sq_dvd h0 hder
  -- the support has a simple root at `x₀`: split it off
  obtain ⟨Ut, hUt⟩ := dvd_iff_isRoot.mpr hU0
  have hUt0 : Ut.eval x₀ ≠ 0 := fun hc ↦ hU' (by rw [hUt]; simp [derivative_mul, hc])
  have hUtU : Ut ∣ U := ⟨X - C x₀, by linear_combination hUt⟩
  have hUtdvd : Ut ∣ (V + C H * U) ^ 2 - f := hUtU.trans (dvd_foldStep_sq_sub hU)
  have h7 : U * (X - C x₀) = (X - C x₀) ^ 2 * Ut := by rw [hUt]; ring
  rw [h7]
  exact ((isCoprime_X_sub_C_of_eval_ne_zero hUt0).symm.pow_left).mul_dvd hsq hUtdvd

end FieldHelpers

/-! ### One numerator step is the scaled honest step -/

section StepEq

variable {F : Type*} [Field F] {f U V : F[X]} {s : MumfordNum F} {d xP NH c H : F}

/-- The composed scaled square root is the scaled composed square root. -/
theorem stepVc_eq_scaled (hu : s.u = C d * U) (hv : s.v = C d * V) (hNH : NH = c * H) :
    s.stepVc NH c = C (d * c) * (V + C H * U) := by
  simp only [MumfordNum.stepVc_def, hu, hv, hNH, C_mul]
  ring

/-- The synthetic quotient of a step is the scaled composed cofactor. -/
theorem stepCof_eq_scaled (hUm : U.Monic) (hu : s.u = C d * U) (hv : s.v = C d * V)
    (hw : s.w = C d * cantorCofactor f U V) (hNH : NH = c * H) (hUdvd : U ∣ V ^ 2 - f)
    (hMum : U * (X - C xP) ∣ (V + C H * U) ^ 2 - f) :
    s.stepCof xP NH c
      = C (d * c ^ 2) * cantorCofactor f (U * (X - C xP)) (V + C H * U) := by
  have hspec := cantorCofactor_spec f hUm hUdvd
  have hspecc := cantorCofactor_spec f (hUm.mul (monic_X_sub_C xP)) hMum
  have hkey : C c ^ 2 * s.w + 2 * (C c * C NH) * s.v + C NH ^ 2 * s.u
      = (X - C xP) * (C (d * c ^ 2) * cantorCofactor f (U * (X - C xP)) (V + C H * U)) := by
    refine mul_left_cancel₀ hUm.ne_zero ?_
    simp only [hu, hv, hw, hNH, C_mul, C_pow]
    linear_combination (C d * C c ^ 2 : F[X]) * hspecc - (C d * C c ^ 2 : F[X]) * hspec
  rw [MumfordNum.stepCof_def, hkey, mul_divByMonic_cancel_left _ (monic_X_sub_C xP)]

variable {g : ℕ}

/-- The scaled `u`-component of a step. -/
theorem step_u_eq_scaled (hUm : U.Monic) (hu : s.u = C d * U) (hv : s.v = C d * V)
    (hw : s.w = C d * cantorCofactor f U V) (hNH : NH = c * H) (hUdvd : U ∣ V ^ 2 - f)
    (hMum : U * (X - C xP) ∣ (V + C H * U) ^ 2 - f) :
    (s.step xP NH c).u
      = C (d * c ^ 4) * (cantorReduce f (U * (X - C xP)) (V + C H * U) (-1)).1 := by
  rw [MumfordNum.step_u, stepCof_eq_scaled hUm hu hv hw hNH hUdvd hMum,
    cantorReduce_neg_one_fst]
  simp only [C_mul, C_pow]
  ring

/-- **The explicit one-step reduction of the composed square root**: against a negated
divisor of matching degree, `%ₘ` is one leading-term cancellation. -/
theorem neg_modByMonic_neg_eq {q : F[X]} (hUm : U.Monic) (hUdeg : U.natDegree = g)
    (hVdeg : V.degree < (g : WithBot ℕ)) (hlc : q.leadingCoeff = -1)
    (hdeg : q.natDegree = g) :
    (-(V + C H * U)) %ₘ (-q) = -(V + C H * U) - C H * q := by
  have hne : q ≠ 0 := fun hzero ↦ by simp [hzero] at hlc
  have hmonic : (-q).Monic := by rw [Monic, leadingCoeff_neg, hlc, neg_neg]
  refine modByMonic_eq_of_dvd_sub_of_degree_lt hmonic ⟨-C H, by ring⟩ ?_
  have hd : U.degree = (-q).degree := by
    rw [degree_neg, degree_eq_natDegree hUm.ne_zero, degree_eq_natDegree hne, hUdeg, hdeg]
  have h8 : (U + q).degree < (g : WithBot ℕ) := by
    have hlt := degree_sub_lt_left hd hUm.ne_zero (hUm.leadingCoeff.trans hmonic.leadingCoeff.symm)
    rwa [sub_neg_eq_add, degree_eq_natDegree hUm.ne_zero, hUdeg] at hlt
  have h9 : -(V + C H * U) - C H * q = -(V + C H * (U + q)) := by ring
  have hCH : (C H * (U + q)).degree ≤ (U + q).degree := by
    rw [← smul_eq_C_mul]
    exact degree_smul_le _ _
  rw [h9, degree_neg, degree_neg, degree_eq_natDegree hne, hdeg]
  exact (degree_add_le _ _).trans_lt (max_lt hVdeg (hCH.trans_lt h8))

/-- The scaled `v`-component of a step: the explicit one-step reduction. -/
theorem step_v_eq_scaled (hUm : U.Monic) (hu : s.u = C d * U) (hv : s.v = C d * V)
    (hw : s.w = C d * cantorCofactor f U V) (hNH : NH = c * H) (hUdvd : U ∣ V ^ 2 - f)
    (hMum : U * (X - C xP) ∣ (V + C H * U) ^ 2 - f) (hUdeg : U.natDegree = g)
    (hVdeg : V.degree < (g : WithBot ℕ))
    (hlc : (cantorCofactor f (U * (X - C xP)) (V + C H * U)).leadingCoeff = -1)
    (hdeg : (cantorCofactor f (U * (X - C xP)) (V + C H * U)).natDegree = g) :
    (s.step xP NH c).v
      = C (d * c ^ 4) * (cantorReduce f (U * (X - C xP)) (V + C H * U) (-1)).2 := by
  rw [cantorReduce_neg_one_snd, neg_modByMonic_neg_eq hUm hUdeg hVdeg hlc hdeg,
    MumfordNum.step_v, stepCof_eq_scaled hUm hu hv hw hNH hUdvd hMum,
    stepVc_eq_scaled hu hv hNH]
  simp only [hNH, C_mul, C_pow]
  ring

/-- The scaled `w`-component of a step: the cofactor of the reduced pair. -/
theorem step_w_eq_scaled (hUm : U.Monic) (hu : s.u = C d * U) (hv : s.v = C d * V)
    (hw : s.w = C d * cantorCofactor f U V) (hNH : NH = c * H) (hUdvd : U ∣ V ^ 2 - f)
    (hMum : U * (X - C xP) ∣ (V + C H * U) ^ 2 - f) (hUdeg : U.natDegree = g)
    (hVdeg : V.degree < (g : WithBot ℕ))
    (hlc : (cantorCofactor f (U * (X - C xP)) (V + C H * U)).leadingCoeff = -1)
    (hdeg : (cantorCofactor f (U * (X - C xP)) (V + C H * U)).natDegree = g) :
    (s.step xP NH c).w
      = C (d * c ^ 4)
        * cantorCofactor f (cantorReduce f (U * (X - C xP)) (V + C H * U) (-1)).1
            (cantorReduce f (U * (X - C xP)) (V + C H * U) (-1)).2 := by
  set cofc := cantorCofactor f (U * (X - C xP)) (V + C H * U) with hcofc
  have hmonic : (-cofc).Monic := by rw [Monic, leadingCoeff_neg, hlc, neg_neg]
  have hspecc := cantorCofactor_spec f (hUm.mul (monic_X_sub_C xP)) hMum
  -- the cofactor of the reduced pair, explicitly
  have hkey : cantorCofactor f (-cofc) (-(V + C H * U) - C H * cofc)
      = -(U * (X - C xP)) - 2 * C H * (V + C H * U) + C H ^ 2 * (-cofc) := by
    have h10 : (-(V + C H * U) - C H * cofc) ^ 2 - f
        = (-cofc) * (-(U * (X - C xP)) - 2 * C H * (V + C H * U) + C H ^ 2 * (-cofc)) := by
      linear_combination hspecc
    rw [cantorCofactor, h10, mul_divByMonic_cancel_left _ hmonic]
  rw [cantorReduce_neg_one_fst, cantorReduce_neg_one_snd,
    neg_modByMonic_neg_eq hUm hUdeg hVdeg hlc hdeg, ← hcofc, hkey, MumfordNum.step_w,
    stepCof_eq_scaled hUm hu hv hw hNH hUdvd hMum, stepVc_eq_scaled hu hv hNH, ← hcofc]
  simp only [hu, hNH, C_mul, C_pow]
  ring

end StepEq

/-! ### The correctness invariant and the main induction -/

section Main

variable {F : Type*} [Field F] {g : ℕ}

/-- **The correctness invariant of the numerator fold**: the numerator state is the
denominator-scaled honest fold state — nonzero denominator, all three components scaled by
it, and the honest pair a fold state. -/
structure IsScaledState (g : ℕ) (f : F[X]) (s : MumfordNum F) (U V : F[X]) : Prop where
  /-- The honest pair is a reduced Mumford pair of the generic degree. -/
  state : IsFoldState g f U V
  /-- The accumulated denominator does not vanish. -/
  den_ne : s.den ≠ 0
  /-- The `u`-component is the scaled honest support. -/
  u_eq : s.u = C s.den * U
  /-- The `v`-component is the scaled honest square root. -/
  v_eq : s.v = C s.den * V
  /-- The `w`-component is the scaled honest cofactor. -/
  w_eq : s.w = C s.den * cantorCofactor f U V

/-- **One numerator step preserves the correctness invariant**, given the step-condition
numerator is nonzero, the scalar-numerator identity, and the composed Mumford
divisibility. -/
theorem IsScaledState.step {f U V : F[X]} {s : MumfordNum F} {xP NH c H : F}
    (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1) (hs : IsScaledState g f s U V)
    (hc0 : c ≠ 0) (hNH : NH = c * H)
    (hMum : U * (X - C xP) ∣ (V + C H * U) ^ 2 - f) :
    IsScaledState g f (s.step xP NH c)
      (cantorReduce f (U * (X - C xP)) (V + C H * U) (-1)).1
      (cantorReduce f (U * (X - C xP)) (V + C H * U) (-1)).2 := by
  obtain ⟨hstate, hden, hu, hv, hw⟩ := hs
  have hUm := hstate.monicU
  have hUdeg := hstate.natDegree_U
  have hVdeg := hstate.degree_V
  -- leading data of the composed cofactor
  have hUcm : (U * (X - C xP)).Monic := hUm.mul (monic_X_sub_C _)
  have hUcdeg : (U * (X - C xP)).natDegree = g + 1 := by
    rw [hUm.natDegree_mul (monic_X_sub_C _), natDegree_X_sub_C, hUdeg]
  have hVcdeg : (V + C H * U).natDegree ≤ g := by
    refine (natDegree_add_le _ _).trans
      (max_le (natDegree_le_iff_degree_le.mpr hVdeg.le) ?_)
    exact natDegree_mul_le.trans (by simp [hUdeg])
  obtain ⟨hlc, hdegsum⟩ := leadingCoeff_natDegree_cantorCofactor f hf hfdeg hUcm hUcdeg hMum
    (by
      refine degree_le_natDegree.trans_lt ?_
      rw [degree_eq_natDegree hUcm.ne_zero, hUcdeg]
      exact_mod_cast by lia)
    (by lia)
  have hdeg : (cantorCofactor f (U * (X - C xP)) (V + C H * U)).natDegree = g := by lia
  refine ⟨hstate.step hf hfdeg hMum, ?_, ?_, ?_, ?_⟩
  · rw [MumfordNum.step_den]
    exact mul_ne_zero hden (pow_ne_zero 4 hc0)
  · rw [step_u_eq_scaled hUm hu hv hw hNH hstate.dvd_sq hMum, MumfordNum.step_den]
  · rw [step_v_eq_scaled hUm hu hv hw hNH hstate.dvd_sq hMum hUdeg hVdeg hlc hdeg,
      MumfordNum.step_den]
  · rw [step_w_eq_scaled hUm hu hv hw hNH hstate.dvd_sq hMum hUdeg hVdeg hlc hdeg,
      MumfordNum.step_den]

variable {f U₀ V₀ : F[X]} {xs ys : ℕ → F} {s₀ : MumfordNum F}

/-- The step pair at the doubling step: the scalar-numerator identity and the composed
Mumford divisibility, from the base data and the nonzero condition numerator. -/
private theorem pair_zero_spec (hbase : IsScaledState g f s₀ U₀ V₀)
    (hx₀ : U₀.eval (xs 0) = 0) (hV₀ : V₀.eval (xs 0) = ys 0)
    (hcv : ys 0 ^ 2 = f.eval (xs 0)) (hc0 : foldCondNum f xs ys s₀ 0 ≠ 0) :
    foldHNum f xs ys s₀ 0 = foldCondNum f xs ys s₀ 0 * foldGenH f xs ys U₀ V₀ 0
      ∧ U₀ * (X - C (xs 0)) ∣ (V₀ + C (foldGenH f xs ys U₀ V₀ 0) * U₀) ^ 2 - f := by
  have hcnum : foldCondNum f xs ys s₀ 0
      = s₀.den * (2 * ys 0 * U₀.derivative.eval (xs 0)) := by
    rw [foldCondNum_zero, hbase.u_eq, derivative_C_mul]
    simp only [eval_mul, eval_C]
    ring
  have hcond0 : 2 * ys 0 * U₀.derivative.eval (xs 0) ≠ 0 :=
    right_ne_zero_of_mul (hcnum ▸ hc0)
  have hHeq : foldGenH f xs ys U₀ V₀ 0 * (2 * ys 0 * U₀.derivative.eval (xs 0))
      = f.derivative.eval (xs 0) - 2 * ys 0 * V₀.derivative.eval (xs 0) := by
    rw [foldGenH_zero]
    exact div_mul_cancel₀ _ hcond0
  refine ⟨?_, foldStep_dvd_double hbase.state.dvd_sq hx₀
    (right_ne_zero_of_mul hcond0) hV₀ hcv hHeq⟩
  rw [foldHNum_zero, hcnum, hbase.v_eq, derivative_C_mul]
  simp only [eval_mul, eval_C]
  linear_combination (-s₀.den) * hHeq

/-- The step pair at a disjoint step: the scalar-numerator identity and the composed
Mumford divisibility, from the invariant at the current stage. -/
private theorem pair_succ_spec {m : ℕ}
    (hprev : IsScaledState g f (foldNum f xs ys s₀ (m + 1))
      (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (m + 1)).1
      (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (m + 1)).2)
    (hcv : ys (m + 1) ^ 2 = f.eval (xs (m + 1)))
    (hc0 : foldCondNum f xs ys s₀ (m + 1) ≠ 0) :
    foldHNum f xs ys s₀ (m + 1)
        = foldCondNum f xs ys s₀ (m + 1) * foldGenH f xs ys U₀ V₀ (m + 1)
      ∧ (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (m + 1)).1 * (X - C (xs (m + 1)))
        ∣ ((foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (m + 1)).2
            + C (foldGenH f xs ys U₀ V₀ (m + 1))
              * (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (m + 1)).1) ^ 2 - f := by
  have hcnum : foldCondNum f xs ys s₀ (m + 1)
      = (foldNum f xs ys s₀ (m + 1)).den
        * (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (m + 1)).1.eval (xs (m + 1)) := by
    rw [foldCondNum_succ, hprev.u_eq]
    simp
  have hUx : (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (m + 1)).1.eval (xs (m + 1))
      ≠ 0 := right_ne_zero_of_mul (hcnum ▸ hc0)
  have hHeq : foldGenH f xs ys U₀ V₀ (m + 1)
        * (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (m + 1)).1.eval (xs (m + 1))
      = ys (m + 1)
        - (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (m + 1)).2.eval (xs (m + 1)) := by
    rw [foldGenH_succ]
    exact div_mul_cancel₀ _ hUx
  refine ⟨?_, foldStep_dvd_disjoint hprev.state.dvd_sq hUx hcv hHeq⟩
  rw [foldHNum_succ, hcnum, hprev.v_eq]
  simp only [eval_mul, eval_C]
  linear_combination (-(foldNum f xs ys s₀ (m + 1)).den) * hHeq

/-- **Correctness of the numerator fold** (`lem:fold-universal`, denominator side): as long
as every earlier step-condition numerator is nonzero, the numerator state at stage `m` is
the denominator-scaled honest fold state at the computed scalars. -/
theorem isScaledState_foldNum (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (hbase : IsScaledState g f s₀ U₀ V₀)
    (hx₀ : U₀.eval (xs 0) = 0) (hV₀ : V₀.eval (xs 0) = ys 0) {m : ℕ}
    (hcurve : ∀ j < m, ys j ^ 2 = f.eval (xs j))
    (hc : ∀ j < m, foldCondNum f xs ys s₀ j ≠ 0) :
    IsScaledState g f (foldNum f xs ys s₀ m)
      (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ m).1
      (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ m).2 := by
  induction m with
  | zero => exact hbase
  | succ m ih =>
    have hprev := ih (fun j hj ↦ hcurve j (by lia)) fun j hj ↦ hc j (by lia)
    have hcm := hc m (by lia)
    rw [foldNum_succ, foldChain_succ]
    rcases m with _ | m
    · obtain ⟨hH, hMum⟩ := pair_zero_spec hbase hx₀ hV₀ (hcurve 0 (by lia)) hcm
      exact hprev.step hf hfdeg hcm hH hMum
    · obtain ⟨hH, hMum⟩ := pair_succ_spec hprev (hcurve (m + 1) (by lia)) hcm
      exact hprev.step hf hfdeg hcm hH hMum

/-- **The honest step conditions of the fold**: the doubling condition `2y₀u₀'(x₀)` at
step `0`, the disjointness values `u_j(x_j)` afterwards (at the computed scalars). -/
noncomputable def foldCond (f : F[X]) (xs ys : ℕ → F) (U₀ V₀ : F[X]) (j : ℕ) : F :=
  if j = 0 then 2 * ys 0 * U₀.derivative.eval (xs 0)
  else (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ j).1.eval (xs j)

theorem foldCond_zero :
    foldCond f xs ys U₀ V₀ 0 = 2 * ys 0 * U₀.derivative.eval (xs 0) := rfl

theorem foldCond_succ (j : ℕ) :
    foldCond f xs ys U₀ V₀ (j + 1)
      = (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ (j + 1)).1.eval (xs (j + 1)) :=
  ite_eq_right (Nat.succ_ne_zero j)

/-- **The per-stage condition identity**: each step-condition numerator is the accumulated
denominator times the honest condition value. -/
theorem foldCondNum_eq_den_mul (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (hbase : IsScaledState g f s₀ U₀ V₀)
    (hx₀ : U₀.eval (xs 0) = 0) (hV₀ : V₀.eval (xs 0) = ys 0) {j : ℕ}
    (hcurve : ∀ i < j, ys i ^ 2 = f.eval (xs i))
    (hc : ∀ i < j, foldCondNum f xs ys s₀ i ≠ 0) :
    foldCondNum f xs ys s₀ j
      = (foldNum f xs ys s₀ j).den * foldCond f xs ys U₀ V₀ j := by
  rcases j with _ | j
  · rw [foldCondNum_zero, foldCond_zero, foldNum_zero, hbase.u_eq, derivative_C_mul]
    simp only [eval_mul, eval_C]
    ring
  · have hspec := isScaledState_foldNum hf hfdeg hbase hx₀ hV₀ hcurve hc
    rw [foldCondNum_succ, foldCond_succ, hspec.u_eq]
    simp

end Main

end ChabautyColeman

end
