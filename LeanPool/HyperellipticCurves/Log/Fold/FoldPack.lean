/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldCerts
public import LeanPool.HyperellipticCurves.Log.Fold.FoldCorrect

import LeanPool.HyperellipticCurves.Log.Trace.TracePipeline

/-!
# The fold pack over a field

Over a field, the certificate pipeline `ChabautyColeman.foldPipe` at a suitable pack *is* the
honest fold chain `ChabautyColeman.foldChain` at the computed scalars `ChabautyColeman.foldGenH` —
so the chain conditions and per-stage avoidance certified by the centre-fold witness produce a
valid, Weierstrass-avoiding fold pack.

The identification is step-by-step: with the state's components coprime to the added
point's column, the certificate combination of one Cantor composition equals the
`H`-scalar representative `V + H·U` — by Chinese-remainder uniqueness at a disjoint step
(`ChabautyColeman.cantorCompose_point_eq_disjoint`), and by uniqueness of the square root
modulo the composed support at the doubling step
(`ChabautyColeman.cantorCompose_point_eq_double`). The certificates themselves are pair
Bézout data from the nonvanishing condition values, with a genuine third slot only at the
doubling step.

## Main statement

* `ChabautyColeman.exists_isFoldCerts_isFoldAvoid`: the fold conditions and the chain
  avoidance produce a pack `d` with `IsFoldCerts` and `IsFoldAvoid`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Compose

variable {F : Type*} [Field F] {f U V s₁ s₂ s₃ : F[X]}

/-- **The composed pair at a disjoint step is the scalar-step pair**: when the support
does not vanish at the added point, the certificate combination of the composition equals
the `H`-scalar representative `V + H·U` for the value-matching scalar. -/
theorem cantorCompose_point_eq_disjoint {xP yP H : F} (hUm : U.Monic)
    (hVdeg : V.degree < U.degree) (hdvd : U ∣ V ^ 2 - f) (hy : yP ^ 2 = f.eval xP)
    (hUx : U.eval xP ≠ 0) (hval : V.eval xP + H * U.eval xP = yP)
    (hbez : s₁ * U + s₂ * (X - C xP) + s₃ * (V + C yP) = 1) :
    cantorCompose f U V (X - C xP) (C yP) s₁ s₂ s₃ = (U * (X - C xP), V + C H * U) := by
  refine Prod.ext rfl ?_
  have hd₂ : (X - C xP) ∣ (C yP : F[X]) ^ 2 - f := by
    refine dvd_iff_isRoot.mpr ?_
    rw [IsRoot, eval_sub, eval_pow, eval_C, hy, sub_self]
  -- the difference is divisible by both coprime factors and has smaller degree
  have hUdvd : U ∣ (cantorCompose f U V (X - C xP) (C yP) s₁ s₂ s₃).2 - (V + C H * U) := by
    have h1 := dvd_cantorCompose_sub_left hbez hdvd
    rw [sub_add_eq_sub_sub]
    exact dvd_sub h1 (dvd_mul_left U (C H))
  have hXdvd : (X - C xP)
      ∣ (cantorCompose f U V (X - C xP) (C yP) s₁ s₂ s₃).2 - (V + C H * U) := by
    have h2 := dvd_cantorCompose_sub_right hbez hd₂
    have h3 : (X - C xP) ∣ (V + C H * U) - C yP := by
      refine dvd_iff_isRoot.mpr ?_
      rw [IsRoot]
      simp only [eval_sub, eval_add, eval_mul, eval_C]
      linear_combination hval
    have h4 := dvd_sub h2 h3
    rwa [sub_sub_sub_cancel_right] at h4
  have hMdvd : U * (X - C xP)
      ∣ (cantorCompose f U V (X - C xP) (C yP) s₁ s₂ s₃).2 - (V + C H * U) :=
    (isCoprime_X_sub_C_of_eval_ne_zero hUx).mul_dvd hUdvd hXdvd
  have hUlt : U.degree < (U * (X - C xP)).degree := by
    rw [degree_mul, degree_X_sub_C, degree_eq_natDegree hUm.ne_zero]
    exact_mod_cast Nat.lt_succ_self _
  have hWdeg : (cantorCompose f U V (X - C xP) (C yP) s₁ s₂ s₃).2.degree
      < (U * (X - C xP)).degree :=
    cantorCompose_degree_lt f hUm (monic_X_sub_C _)
  have hV'deg : (V + C H * U).degree < (U * (X - C xP)).degree := by
    refine (degree_add_le _ _).trans_lt (max_lt (hVdeg.trans hUlt) ?_)
    refine (degree_mul_le _ _).trans_lt (lt_of_le_of_lt ?_ hUlt)
    calc (C H).degree + U.degree ≤ 0 + U.degree := add_le_add degree_C_le le_rfl
      _ = U.degree := zero_add _
  have hdeg : ((cantorCompose f U V (X - C xP) (C yP) s₁ s₂ s₃).2
        - (V + C H * U)).degree < (U * (X - C xP)).degree :=
    (degree_sub_le _ _).trans_lt (max_lt hWdeg hV'deg)
  have hz := eq_zero_of_dvd_of_degree_lt hMdvd hdeg
  change (cantorCompose f U V (X - C xP) (C yP) s₁ s₂ s₃).2 = V + C H * U
  linear_combination hz

/-- **The composed pair at the doubling step is the scalar-step pair**: at a simple root
of the support matching the point, the certificate combination equals the `H`-scalar
representative for any tangency scalar, by uniqueness of the square root modulo the
composed support under Weierstrass avoidance of the state. -/
theorem cantorCompose_point_eq_double {x₀ y₀ H : F} (hUm : U.Monic)
    (hVdeg : V.degree < U.degree) (hdvd : U ∣ V ^ 2 - f) (hy : y₀ ^ 2 = f.eval x₀)
    (hU0 : U.eval x₀ = 0) (hV0 : V.eval x₀ = y₀) (h2y : 2 * y₀ ≠ 0)
    (hcop : IsCoprime U (2 * V)) (hMum : U * (X - C x₀) ∣ (V + C H * U) ^ 2 - f)
    (hbez : s₁ * U + s₂ * (X - C x₀) + s₃ * (V + C y₀) = 1) :
    cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃ = (U * (X - C x₀), V + C H * U) := by
  refine Prod.ext rfl ?_
  have hd₂ : (X - C x₀) ∣ (C y₀ : F[X]) ^ 2 - f := by
    refine dvd_iff_isRoot.mpr ?_
    rw [IsRoot, eval_sub, eval_pow, eval_C, hy, sub_self]
  have hWsq : U * (X - C x₀)
      ∣ (cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2 ^ 2 - f :=
    cantorCompose_dvd f hbez hdvd hd₂
  have hUlt : U.degree < (U * (X - C x₀)).degree := by
    rw [degree_mul, degree_X_sub_C, degree_eq_natDegree hUm.ne_zero]
    exact_mod_cast Nat.lt_succ_self _
  have hVdeg' : (V + C H * U).degree < (U * (X - C x₀)).degree := by
    refine (degree_add_le _ _).trans_lt (max_lt (hVdeg.trans hUlt) ?_)
    refine (degree_mul_le _ _).trans_lt (lt_of_le_of_lt ?_ hUlt)
    calc (C H).degree + U.degree ≤ 0 + U.degree := add_le_add degree_C_le le_rfl
      _ = U.degree := zero_add _
  -- Weierstrass avoidance of the state gives a Bézout certificate against the root sum
  have hWx : (X - C x₀) ∣ (cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2 - C y₀ :=
    dvd_cantorCompose_sub_right hbez hd₂
  have hcx : IsCoprime ((cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2
      + (V + C H * U)) (X - C x₀) := by
    refine isCoprime_X_sub_C_of_eval_ne_zero ?_
    have hW0 : (cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2.eval x₀ = y₀ := by
      have h := dvd_iff_isRoot.mp hWx
      rwa [IsRoot, eval_sub, eval_C, sub_eq_zero] at h
    rwa [eval_add, eval_add, eval_mul, eval_C, hW0, hV0, hU0, mul_zero, add_zero, ← two_mul]
  have hcU : IsCoprime U ((cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2
      + (V + C H * U)) := by
    obtain ⟨t, ht⟩ : U ∣ (cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2
        + (V + C H * U) - 2 * V := by
      rw [show (cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2 + (V + C H * U) - 2 * V
          = ((cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2 - V) + C H * U by
        ring]
      exact dvd_add (dvd_cantorCompose_sub_left hbez hdvd) (dvd_mul_left U (C H))
    have h := hcop.add_mul_left_right t
    rwa [show 2 * V + U * t = (cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2
        + (V + C H * U) by linear_combination -ht] at h
  obtain ⟨p, q, hpq⟩ := hcU.mul_left hcx.symm
  change (cantorCompose f U V (X - C x₀) (C y₀) s₁ s₂ s₃).2 = V + C H * U
  exact eq_of_dvd_sq_sub_of_bezout (hUm.mul (monic_X_sub_C _)) hWsq hMum
    (cantorCompose_degree_lt f hUm (monic_X_sub_C _)) hVdeg' hpq

end Compose

section Pack

variable {F : Type*} [Field F] {g : ℕ} {f U₀ V₀ : F[X]} {xs ys : ℕ → F}

/-- **Existence of a valid, avoiding fold pack over a field**: at a configuration whose honest fold
chain satisfies the step conditions and the per-stage Weierstrass avoidance, some certificate pack
makes the fold pipeline equal the honest chain — hence valid with the same avoidance. The
chain-state invariants enter as a hypothesis (supplied by `ChabautyColeman.isScaledState_foldNum`
at the tuple configuration). -/
theorem exists_isFoldCerts_isFoldAvoid
    (hstate : ∀ j ≤ 2 * g, IsFoldState g f
      (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ j).1
      (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ j).2)
    (hx₀ : U₀.eval (xs 0) = 0) (hV₀ : V₀.eval (xs 0) = ys 0)
    (hcurve : ∀ j < 2 * g, ys j ^ 2 = f.eval (xs j))
    (hcond : ∀ j < 2 * g, foldCond f xs ys U₀ V₀ j ≠ 0)
    (hav : ∀ j ≤ 2 * g, IsCoprime
      (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ j).1
      (2 * (foldChain f xs (foldGenH f xs ys U₀ V₀) U₀ V₀ j).2)) :
    ∃ d : FoldCertData F g, IsFoldCerts f xs ys U₀ V₀ d ∧ IsFoldAvoid f xs ys U₀ V₀ d := by
  classical
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · refine ⟨fun j ↦ j.elim0, fun j ↦ j.elim0, fun j hj ↦ ?_⟩
    obtain rfl : j = 0 := by lia
    exact hav 0 hj
  set H := foldGenH f xs ys U₀ V₀ with hHdef
  have h2g0 : 0 < 2 * g := by lia
  have h₀ : IsFoldState g f U₀ V₀ := hstate 0 (by lia)
  -- the components of the doubling-step condition
  have hcond0 := hcond 0 h2g0
  rw [foldCond_zero] at hcond0
  have h2y : 2 * ys 0 ≠ 0 := fun h ↦ hcond0 (by rw [h, zero_mul])
  have hder0 : U₀.derivative.eval (xs 0) ≠ 0 := fun h ↦ hcond0 (by rw [h, mul_zero])
  -- the tangency certificate of the computed initial scalar
  have hH0eq : H 0 * (2 * ys 0 * U₀.derivative.eval (xs 0))
      = f.derivative.eval (xs 0) - 2 * ys 0 * V₀.derivative.eval (xs 0) := by
    rw [hHdef, foldGenH_zero, div_mul_cancel₀ _ hcond0]
  have hMum0 : U₀ * (X - C (xs 0)) ∣ (V₀ + C (H 0) * U₀) ^ 2 - f :=
    foldStep_dvd_double h₀.dvd_sq hx₀ hder0 hV₀ (hcurve 0 h2g0) hH0eq
  -- the doubling-step certificate: the point column against the square-root column
  obtain ⟨α, β, hαβ⟩ := isCoprime_X_sub_C_of_eval_ne_zero
    (show (V₀ + C (ys 0)).eval (xs 0) ≠ 0 by
      rw [eval_add, eval_C, hV₀, ← two_mul]; exact h2y)
  -- the disjoint-step certificates: support against the point column
  have hUx : ∀ j, 0 < j → j < 2 * g →
      (foldChain f xs H U₀ V₀ j).1.eval (xs j) ≠ 0 := by
    intro j hj0 hjlt
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by lia⟩
    have h := hcond (m + 1) hjlt
    rwa [foldCond_succ] at h
  have hcopj : ∀ j, 0 < j → j < 2 * g →
      IsCoprime (foldChain f xs H U₀ V₀ j).1 (X - C (xs j)) := fun j hj0 hjlt ↦
    isCoprime_X_sub_C_of_eval_ne_zero (hUx j hj0 hjlt)
  choose s t hst using hcopj
  -- the pack
  set d : FoldCertData F g := fun j ↦ if hj : (j : ℕ) = 0 then ⟨0, β, α⟩
    else ⟨s j (Nat.pos_of_ne_zero hj) j.2, t j (Nat.pos_of_ne_zero hj) j.2, 0⟩ with hddef
  -- the value certificate of the computed scalar at a disjoint step
  have hHval : ∀ m, m + 1 < 2 * g →
      (foldChain f xs H U₀ V₀ (m + 1)).2.eval (xs (m + 1))
        + H (m + 1) * (foldChain f xs H U₀ V₀ (m + 1)).1.eval (xs (m + 1))
        = ys (m + 1) := by
    intro m hm
    rw [hHdef, foldGenH_succ, div_mul_cancel₀ _ (hUx (m + 1) m.succ_pos hm)]
    ring
  -- the pipeline at this pack is the honest chain
  have hpipe : ∀ j ≤ 2 * g, foldPipe f xs ys d.seq U₀ V₀ j
      = foldChain f xs H U₀ V₀ j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      have hjlt : j < 2 * g := by lia
      have hstj := hstate j (by lia)
      rw [foldPipe_succ, ih (by lia), d.seq_of_lt hjlt, foldChain_succ]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have hbez0 : (0 : F[X]) * U₀ + β * (X - C (xs 0))
            + α * (V₀ + C (ys 0)) = 1 := by linear_combination hαβ
        have hcomp := cantorCompose_point_eq_double h₀.monicU h₀.degree_V_lt h₀.dvd_sq
          (hcurve 0 h2g0) hx₀ hV₀ h2y (hav 0 (by lia)) hMum0 hbez0
        simp only [foldPipeStep, foldChain_zero, hddef, dite_eq_left]
        rw [hcomp]
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by lia⟩
        have hbezj : s (m + 1) m.succ_pos hjlt * (foldChain f xs H U₀ V₀ (m + 1)).1
            + t (m + 1) m.succ_pos hjlt * (X - C (xs (m + 1)))
            + 0 * ((foldChain f xs H U₀ V₀ (m + 1)).2 + C (ys (m + 1))) = 1 := by
          linear_combination hst (m + 1) m.succ_pos hjlt
        have hcomp := cantorCompose_point_eq_disjoint hstj.monicU hstj.degree_V_lt
          hstj.dvd_sq (hcurve (m + 1) hjlt) (hUx (m + 1) m.succ_pos hjlt)
          (hHval m hjlt) hbezj
        simp only [foldPipeStep, hddef, Nat.succ_ne_zero, dite_eq_right, not_false_iff]
        rw [hcomp]
  refine ⟨d, fun j ↦ ?_, fun j hj ↦ ?_⟩
  · rw [hpipe j j.2.le]
    simp only [hddef]
    split_ifs with hj0
    · dsimp only
      rw [hj0, foldChain_zero]
      linear_combination hαβ
    · dsimp only
      linear_combination hst j (Nat.pos_of_ne_zero hj0) j.2
  · rw [hpipe j hj]
    exact hav j hj

end Pack

end ChabautyColeman

end
