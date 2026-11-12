/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5332T1RightRows
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv

-- [TABLET NODE: P5332T1RightRounding]

/-!
# P5332T1RightRounding

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5332T1RightRounding (P : FordFareyParameter) (hq : 1 < P.q)
    (j : Fin 3) (t : Int) (ht : 0 ≤ t)
    (ht' : t ≤ ((![P.q₂, P.q₁, P.q] j : Nat) : Int)) :
    let V := (P5332T1RightRows P j t).values
    V 1 + V 2 + V 3 + V 4 - 4 * V 0 =
      if 0 < t ∧ t < ((![P.q₂, P.q₁, P.q] j : Nat) : Int) then 1 else 0 := by
-- BODY
  have hq' : 1 < (P.q : Int) := by exact_mod_cast hq
  have hr : 0 < (P.q₁ : Int) := by
    by_contra hn
    have hz : P.q₁ = 0 := by omega
    have hh := P.det₁
    rw [hz] at hh
    norm_num at hh
    have : (P.q : Int) ∣ 1 := ⟨P.p₁, by nlinarith⟩
    have := Int.le_of_dvd (by omega : (0 : Int) < 1) this
    omega
  have hs : 0 < (P.q₂ : Int) := by exact_mod_cast P.q₂_pos
  have hsum : (P.q : Int) = (P.q₁ : Int) + P.q₂ := by exact_mod_cast P.sum_q
  have hpr : P.p * (P.q₁ : Int) = P.p₁ * (P.q : Int) - 1 := by nlinarith [P.det₁]
  have hps : P.p * (P.q₂ : Int) = P.p₂ * (P.q : Int) + 1 := by nlinarith [P.det₂]
  have cancel (v : Int) (hv : (P.q : Int) ∣ P.p*v) : (P.q : Int) ∣ v := by
    obtain ⟨k, hk⟩ := hv
    refine ⟨P.p₁*v-(P.q₁ : Int)*k, ?_⟩
    have hm := congrArg (fun z : Int => z*v) P.det₁
    nlinarith only [hm, hk]
  have fm (K : Int) : (K*(P.q : Int)-1)/(P.q : Int) = K-1 := by
    apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
    constructor <;> nlinarith
  have fp (K : Int) : (K*(P.q : Int)+1)/(P.q : Int) = K := by
    apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
    constructor <;> nlinarith
  have ceil (N K : Int) (lo : K*(P.q : Int) < N) (hi : N ≤ K*(P.q : Int)+P.q) :
      -((-N)/(P.q : Int)) = K+1 := by
    have hh : (-N)/(P.q : Int) = -(K+1) := by
      apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
      constructor <;> nlinarith
    rw [hh]
    ring
  have cm (K : Int) : -((-(K*(P.q : Int)-1))/(P.q : Int)) = K := by
    convert ceil (K*(P.q : Int)-1) (K-1) (by nlinarith) (by nlinarith) using 1; ring
  have cp (K : Int) : -((-(K*(P.q : Int)+1))/(P.q : Int)) = K+1 :=
    ceil _ K (by omega) (by omega)
  have fnm (K : Int) : (1-K*(P.q : Int))/(P.q : Int) = -K := by
    apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
    constructor <;> nlinarith
  have fnp (K : Int) : (-1-K*(P.q : Int))/(P.q : Int) = -(K+1) := by
    apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
    constructor <;> nlinarith
  have dq (K : Int) : K*(P.q : Int)/(P.q : Int) = K :=
    Int.mul_ediv_cancel K (by omega)
  have cq (K : Int) : -((-(K*(P.q : Int)))/(P.q : Int)) = K := by
    rw [← neg_mul, dq]
    ring
  by_cases hEnd : t = 0 ∨ t = ((![P.q₂,P.q₁,P.q] j : Nat) : Int)
  · rcases hEnd with rfl | rfl
    · fin_cases j <;> dsimp [P5332T1RightRows] <;>
        norm_num [show (1 : Int)/(P.q : Int) = 0 by simpa using fp 0,
          show (-1 : Int)/(P.q : Int) = -1 by simpa using fm 0]
    · fin_cases j <;> dsimp [P5332T1RightRows] <;>
        norm_num only [hps, hpr, add_sub_cancel_left, add_sub_cancel_right, sub_add_cancel,
          sub_neg_eq_add, sub_self, lt_self_iff_false, and_false, ite_false,
          fm, fp, cm, cp, fnm, fnp, dq, cq] <;>
        nlinarith only [hpr, hps]
  · have htp : 0 < t := by omega
    have htL : t < ((![P.q₂,P.q₁,P.q] j : Nat) : Int) := by omega
    have htq : t < (P.q : Int) := by fin_cases j <;> dsimp at htL <;> omega
    let K := P.p*t/(P.q : Int)
    let R := P.p*t%(P.q : Int)
    have hR0 : 0 ≤ R := Int.emod_nonneg _ (by omega)
    have hRq : R < (P.q : Int) := Int.emod_lt_of_pos _ (by omega)
    have heq : P.p*t = K*(P.q : Int)+R := by
      dsimp [K, R]
      have := Int.emod_add_mul_ediv (P.p*t) (P.q : Int)
      nlinarith
    have hRn : R ≠ 0 := by
      intro hh
      have hd : (P.q : Int) ∣ t := cancel t ⟨K, by nlinarith [hh]⟩
      have := Int.le_of_dvd htp hd
      omega
    have hRp : 0 < R := by omega
    have hC : -((-(P.p*t))/(P.q : Int)) = K+1 :=
      ceil _ K (by nlinarith) (by nlinarith)
    fin_cases j
    · change t < (P.q₂ : Int) at htL
      have hR1 : R ≠ 1 := by
        intro hh
        have hd := cancel ((P.q₂ : Int)-t)
          (show (P.q : Int) ∣ P.p*((P.q₂ : Int)-t) from
            ⟨P.p₂-K, by nlinarith only [heq, hps, hh]⟩)
        have := Int.le_of_dvd (by omega : 0 < (P.q₂ : Int)-t) hd
        omega
      have hc : -((-(P.p*t-1))/(P.q : Int)) = K+1 :=
        ceil _ K (by
          have : 2 ≤ R := by omega
          nlinarith) (by nlinarith)
      dsimp [P5332T1RightRows]
      norm_num only [hc, show 0 < t ∧ t < (P.q₂ : Int) from ⟨htp,htL⟩, true_and, ite_true]
      change _ + _ + _ + _ - _ = 1
      dsimp [K] at hc
      nlinarith only [hc]
    · change t < (P.q₁ : Int) at htL
      have hR1 : R ≠ (P.q : Int)-1 := by
        intro hh
        have hd := cancel ((P.q₁ : Int)-t)
          (show (P.q : Int) ∣ P.p*((P.q₁ : Int)-t) from
            ⟨P.p₁-K-1, by nlinarith only [heq, hpr, hh]⟩)
        have := Int.le_of_dvd (by omega : 0 < (P.q₁ : Int)-t) hd
        omega
      have hf : (P.p*t+1)/(P.q : Int) = K := by
        apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
        have : R ≤ (P.q : Int)-2 := by omega
        constructor <;> nlinarith
      dsimp [P5332T1RightRows]
      norm_num only [hC, hf, show 0 < t ∧ t < (P.q₁ : Int) from ⟨htp,htL⟩, true_and, ite_true]
      ring
    · dsimp [P5332T1RightRows]
      norm_num only [hC, show 0 < t ∧ t < (P.q : Int) from ⟨htp,htq⟩, true_and, ite_true]
      change _ + _ + _ + _ - _ = 1
      dsimp [K] at hC
      nlinarith only [hC]

end ApollonianSuperharmonic

end
