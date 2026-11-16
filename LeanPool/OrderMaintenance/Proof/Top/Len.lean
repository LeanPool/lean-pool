/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Step


/-!
# M5: table lengths

Every node serves at most `Π_h` (`ew_le_any`), so a live table has seen fewer than `Dmax`
insertion events (`Room.dr_lt`): its length is bounded by a constant (`TabLen`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- A drain's targets weigh at most `Π_h` together. -/
theorem Timing.ew_le {s : TS} {cl : List Nat} {oj : Option Job} (Ti : Timing s cl oj) (hTP : TopParams s.P)
    {g : Nat} (hg : ghostN s g) : ew s cl g ≤ Pid s.P (ht s g) := by
  have h1 := Ti.wF g hg
  have h2 := (Ti.wB g hg).2
  have h3 := Ti.fund_le hTP hg
  unfold fundOf at h3
  unfold Pid; omega

/-- **Every node serves at most `Π_h`.** -/
theorem ew_le_any {s : TS} {cl : List Nat} {ord : Nat → List Nat} {oj : Option Job} (S : Shape s cl ord)
    (Ti : Timing s cl oj) (hTP : TopParams s.P) (hcap : cl.length + 2 ≤ Wd s.P (s.P.H - 1)) {T : Nat}
    (hT : isN s T) : ew s cl T ≤ Pid s.P (ht s T) := by
  by_cases hd : (nd s T).draining = true
  · exact Ti.ew_le hTP ⟨hT, hd⟩
  · have hl : liveN s T := ⟨hT, by simpa using hd⟩
    have hew : ew s cl T = tw s cl T := by unfold ew; rw [ite_eq_right hd]
    rw [hew]
    obtain ⟨h1, hH⟩ := S.htN T hT
    by_cases hs : srcOf s T = NIL
    · by_cases hp : (nd s T).livePar = NIL
      · -- the root
        have hroot : ht s T = s.P.H := by
          by_contra h; exact (S.up T hl (by omega)).1.1.1 hp
        have := tw_le (s := s) cl T
        have ha : 2 ≤ s.P.a := by have := hTP.lamK 1 le_rfl; simp [lamd] at this; omega
        have hw : Wd s.P (s.P.H - 1) ≤ Wd s.P s.P.H := by
          unfold Wd; have := Nat.pow_le_pow_right (show 1 ≤ s.P.a by omega) (show s.P.H - 1 ≤ s.P.H by omega)
          omega
        rw [hroot]; unfold Pid; omega
      · have := Ti.wA T hl hp hs
        have hw := Ti.wts T hl
        unfold Pid; split at hw <;> omega
    · obtain ⟨hg, htg⟩ := S.src T hl hs
      generalize srcOf s T = g at hg htg
      have hle := Ti.ew_le hTP hg
      obtain ⟨-, -, hh1, hh2, -⟩ := S.ghost _ hg
      unfold ew at hle; rw [ite_eq_left hg.2] at hle
      rcases htg with e | e
      · have : ht s T = ht s g := by rw [e]; exact hh1
        rw [this]; rw [← e] at hle; omega
      · have : ht s T = ht s g := by rw [e]; exact hh2
        rw [this]; rw [← e] at hle; omega

/-- **A live table has seen fewer than `Dmax` insertion events.** -/
theorem Room.dr_lt {s : TS} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {oj : Option Job}
    (Ro : Room s cl dr n0) (S : Shape s cl ord) (Ti : Timing s cl oj) (hTP : TopParams s.P)
    (hcap : cl.length + 2 ≤ Wd s.P (s.P.H - 1)) {T : Nat} (hT : isN s T) : dr T + 1 ≤ Dmax s.P (ht s T) := by
  have hew := ew_le_any S Ti hTP hcap hT
  obtain ⟨h1, hH⟩ := S.htN T hT
  have hc : 1 ≤ (if s.P.H < T then lamd s.P (ht s T) else 1) := by
    split
    · have := hTP.lamK (ht s T) (by omega); omega
    · exact le_rfl
  by_cases h2 : 2 ≤ ht s T
  · have hg1 := hTP.gam1 (ht s T - 1) (by omega)
    have hp := Ro.pot2 T hT h2
    have hn0 := Ro.n0le T hT
    unfold Dmax; rw [ite_eq_right (by omega)]
    set g := gamd s.P (ht s T - 1)
    have key : g * dr T + 1 ≤ Pid s.P (ht s T) + g * n0 T := by omega
    by_cases hdn : dr T ≤ n0 T
    · generalize Pid s.P (ht s T) / g = q; omega
    · have : dr T - n0 T ≤ Pid s.P (ht s T) / g := by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm, Nat.mul_sub]
        omega
      generalize Pid s.P (ht s T) / g = q at this; omega
  · have hh : ht s T = 1 := by omega
    have hp := Ro.pot1 T hT hh
    rw [hh] at hew hc ⊢
    unfold Dmax; rw [ite_eq_left le_rfl]
    have heven : Pid s.P 1 % 2 = 0 := by unfold Pid Wd; omega
    omega

/-- The bound `n0 + 2·dr ≤ 160` of a live table. -/
theorem Room.len_le {s : TS} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {oj : Option Job}
    (Ro : Room s cl dr n0) (S : Shape s cl ord) (Ti : Timing s cl oj) (hTP : TopParams s.P)
    (hcap : cl.length + 2 ≤ Wd s.P (s.P.H - 1)) {T : Nat} (hT : isN s T) : n0 T + 2 * dr T ≤ 160 := by
  have h1 := Ro.dr_lt S Ti hTP hcap hT
  have h2 := Ro.n0le T hT
  have h3 := hTP.tab (ht s T) (S.htN T hT).1
  omega

end OrderMaintenance.Proof.Top
