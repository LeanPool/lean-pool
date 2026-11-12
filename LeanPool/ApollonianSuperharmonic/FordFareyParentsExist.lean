/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordFareyParameter

-- [TABLET NODE: FordFareyParentsExist]

/-!
# FordFareyParentsExist

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordFareyParentsExist (p : Int) (q : Nat) (hq : 0 < q)
    (hred : Nat.Coprime q p.natAbs) :
    ∃! P : FordFareyParameter, P.p = p ∧ P.q = q := by
-- BODY
  by_cases hunit : q = 1
  · subst q
    refine ⟨{
      p := p, q := 1, q_pos := by omega, reduced := hred,
      p₁ := 1, q₁ := 0, p₂ := p - 1, q₂ := 1,
      sum_p := by ring, sum_q := by rfl,
      det₁ := by norm_num, det₂ := by ring,
      q₁_lt := by omega, q₂_pos := by omega,
      unit_case := by intro; exact ⟨rfl, rfl, rfl, rfl⟩ },
      by simp, ?_⟩
    intro other hother
    have qvalue : other.q = 1 := hother.2
    have hsum := other.sum_q
    have hlt := other.q₁_lt
    have hpos := other.q₂_pos
    have qone : other.q₁ = 0 := by omega
    have qtwo : other.q₂ = 1 := by omega
    have pfirst : other.p₁ = 1 := by
      have hd := other.det₁
      rw [qvalue, qone] at hd
      norm_num at hd ⊢
      omega
    have psecond : other.p₂ = p - 1 := by
      have hs := other.sum_p
      have hp := hother.1
      omega
    cases other
    dsimp at hother qvalue hsum hlt hpos qone qtwo pfirst psecond
    rw [FordFareyParameter.mk.injEq]
    rcases hother with ⟨_, _⟩
    constructor <;> omega
  · have hqone : 1 < q := by omega
    obtain hp | hp := le_total 0 p
    · let y : Int := Nat.gcdA p.natAbs q
      obtain ⟨q₁, hq₁lt, hq₁mod⟩ :=
        Nat.exists_mul_mod_eq_of_coprime (q - 1) hred.symm (by omega)
      have hq₁mod' : p.natAbs * q₁ % q = q - 1 := by
        simpa [Nat.mod_eq_of_lt (show q - 1 < q by omega)] using hq₁mod
      have hmodNat : Nat.ModEq q (p.natAbs * q₁) (q - 1) := by
        simpa [Nat.ModEq] using hq₁mod'
      have hdiv := Nat.ModEq.dvd (n := q) (a := p.natAbs * q₁) (b := q - 1) hmodNat
      obtain ⟨t, ht⟩ := hdiv
      have hq₁pos : 0 < q₁ := by
        by_contra hn
        have : q₁ = 0 := by omega
        subst q₁
        simp at hq₁mod'
        omega
      let p₁ : Int := 1 - t
      let q₂ : Nat := q - q₁
      let p₂ : Int := p - p₁
      have hdet1 : p₁ * (q : Int) - (q₁ : Int) * p = 1 := by
        dsimp [p₁]
        rw [Nat.cast_sub (by omega)] at ht
        norm_num [Nat.cast_mul, Int.natAbs_of_nonneg hp] at ht ⊢
        nlinarith [ht]
      have hdet2 : p₂ * (q : Int) - (q₂ : Int) * p = -1 := by
        dsimp [p₁, p₂, q₂]
        rw [Nat.cast_sub hq₁lt.le]
        nlinarith [hdet1]
      let result : FordFareyParameter := by
        exact FordFareyParameter.mk p q hq hred p₁ q₁ p₂ q₂
          (by dsimp [p₂]; ring) (by dsimp [q₂]; omega) hdet1
          hdet2 hq₁lt
          (by dsimp [q₂]; omega) (by intro h; omega)
      refine ⟨result, ?_, ?_⟩
      · simp [result]
      · intro other hother
        rw [FordFareyParameter.mk.injEq]
        have hmul : Nat.ModEq q (p.natAbs * other.q₁) (p.natAbs * q₁) := by
          apply Nat.modEq_iff_dvd.mpr
          norm_num [Nat.cast_mul, Int.natAbs_of_nonneg hp]
          refine ⟨p₁ - other.p₁, ?_⟩
          have hd := other.det₁
          rw [hother.1, hother.2] at hd
          dsimp [p₁] at hdet1
          calc
            p * (q₁ : Int) - p * (other.q₁ : Int) =
                (q : Int) * (p₁ - other.p₁) +
                  ((other.p₁ * (q : Int) - (other.q₁ : Int) * p) -
                    (p₁ * (q : Int) - (q₁ : Int) * p)) := by ring
            _ = (q : Int) * (p₁ - other.p₁) := by rw [hd, hdet1]; norm_num
        have hcancel := Nat.ModEq.cancel_left_of_coprime hred.gcd_eq_one hmul
        have hqeq : other.q₁ = q₁ :=
          hcancel.eq_of_lt_of_lt (by simpa [hother.2] using other.q₁_lt) hq₁lt
        have hpone : other.p₁ = p₁ := by
          have hd := other.det₁
          rw [hother.1, hother.2, hqeq] at hd
          nlinarith [hd, hdet1]
        have hqtwo : other.q₂ = q₂ := by
          have hs := other.sum_q
          rw [hother.2, hqeq] at hs
          dsimp [q₂]
          omega
        have hptwo : other.p₂ = p₂ := by
          have hs := other.sum_p
          rw [hother.1, hpone] at hs
          dsimp [p₂]
          omega
        exact ⟨by simp [hother.1], hother.2, hpone, hqeq, hptwo, hqtwo⟩
    · by_cases hz : p = 0
      · subst p
        have : q = 1 := (Nat.coprime_zero_right q).mp hred
        omega
      · obtain ⟨q₁, hq₁lt, hq₁mod⟩ :=
          Nat.exists_mul_mod_eq_one_of_coprime hred.symm hqone
        have hdiv : (q : Int) ∣ (1 : Int) - (p.natAbs * q₁ : Int) := by
          have hm : Nat.ModEq q (p.natAbs * q₁) 1 := by
            simpa [Nat.ModEq, Nat.mod_eq_of_lt hqone] using hq₁mod
          exact Nat.ModEq.dvd hm
        obtain ⟨t, ht⟩ := hdiv
        have hq₁pos : 0 < q₁ := by
          by_contra hn
          have : q₁ = 0 := by omega
          subst q₁
          simp at hq₁mod
        obtain ⟨n, hpform⟩ : ∃ n : Nat, p = -(n.succ : Int) := by
          cases p with
          | ofNat n => simp_all
          | negSucc n => exact ⟨n, rfl⟩
        let p₁ : Int := t
        let q₂ : Nat := q - q₁
        let p₂ : Int := p - p₁
        have hdet1 : p₁ * (q : Int) - (q₁ : Int) * p = 1 := by
          dsimp [p₁]
          have hpabs : (p.natAbs : Int) = -p := by
            rw [hpform]
            change (n.succ : Int) = n.succ
            rfl
          rw [hpabs] at ht
          rw [hpform] at ht ⊢
          norm_num [Nat.cast_mul] at ht ⊢
          nlinarith [ht]
        have hdet2 : p₂ * (q : Int) - (q₂ : Int) * p = -1 := by
          dsimp [p₁, p₂, q₂]
          rw [hpform]
          rw [Nat.cast_sub hq₁lt.le]
          nlinarith [hdet1]
        let result : FordFareyParameter := by
          exact FordFareyParameter.mk p q hq hred p₁ q₁ p₂ q₂
            (by dsimp [p₂]; ring) (by dsimp [q₂]; omega) hdet1 hdet2 hq₁lt
            (by dsimp [q₂]; omega) (by intro h; omega)
        refine ⟨result, ?_, ?_⟩
        · simp [result]
        · intro other hother
          rw [FordFareyParameter.mk.injEq]
          have hpabs : (p.natAbs : Int) = -p := by
            rw [hpform]
            change (n.succ : Int) = n.succ
            rfl
          have hmul : Nat.ModEq q (p.natAbs * other.q₁) (p.natAbs * q₁) := by
            apply Nat.modEq_iff_dvd.mpr
            norm_num [Nat.cast_mul]
            rw [← Int.natCast_natAbs, hpabs]
            refine ⟨other.p₁ - p₁, ?_⟩
            have hd := other.det₁
            rw [hother.1, hother.2] at hd
            calc
              -p * (q₁ : Int) - -p * (other.q₁ : Int) =
                  (q : Int) * (other.p₁ - p₁) +
                    ((p₁ * (q : Int) - (q₁ : Int) * p) -
                      (other.p₁ * (q : Int) - (other.q₁ : Int) * p)) := by ring
              _ = (q : Int) * (other.p₁ - p₁) := by rw [hd, hdet1]; norm_num
          have hcancel := Nat.ModEq.cancel_left_of_coprime hred.gcd_eq_one hmul
          have hqeq : other.q₁ = q₁ :=
            hcancel.eq_of_lt_of_lt (by simpa [hother.2] using other.q₁_lt) hq₁lt
          have hpone : other.p₁ = p₁ := by
            have hd := other.det₁
            rw [hother.1, hother.2, hqeq] at hd
            nlinarith [hd, hdet1]
          have hqtwo : other.q₂ = q₂ := by
            have hs := other.sum_q
            rw [hother.2, hqeq] at hs
            dsimp [q₂]
            omega
          have hptwo : other.p₂ = p₂ := by
            have hs := other.sum_p
            rw [hother.1, hpone] at hs
            dsimp [p₂]
            omega
          exact ⟨by simp [hother.1], hother.2, hpone, hqeq, hptwo, hqtwo⟩

end ApollonianSuperharmonic

end
