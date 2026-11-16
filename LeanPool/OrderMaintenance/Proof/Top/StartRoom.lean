/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartCount


/-!
# M5: room for `v1`, `v2` in the tables holding `v`
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- **A table one level up has room on both sides of an entry.** -/
theorem room_up {s : TS} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {oj : Option
  Job}
    (hI : InvJ s cl ord dr n0 oj) (hTP : TopParams s.P) {e T : Nat} (he : isN s e) (hT : T ∈ (nd
      s e).inTables)
    (y z : Nat) :
    ∃ A le Bs, (nd s T).table = A ++ (e, le) :: Bs ∧ e ∉ A.map (·.1) ∧
      ((nd s T).draining = true → (lookup (nd s T).side e).isSome) ∧
      roomLo A le true < roomHi s.P.beta Bs le true ∧ roomLo A le false < roomHi s.P.beta Bs le
        false ∧
      2 ≤ gapB s.P.beta (n0 T) (dr T) ∧
      GapsGe s.P.beta (gapB s.P.beta (n0 T) (dr T) / 2)
        ((A ++ (y, (roomLo A le true + roomHi s.P.beta Bs le true - 1) / 2) :: (e, le) ::
          (z, (roomLo A le false + roomHi s.P.beta Bs le false - 1) / 2) :: Bs).map (·.2)) := by
  have S := hI.shape
  have Ti := hI.time
  have Ro := hI.room
  obtain ⟨h1, hH⟩ := S.htN e he
  have hent : Ent ord (ht s e) e := (S.ordMem _ h1 hH e).mpr ⟨he, rfl⟩
  have hT' : T ∈ tabs s (ht s e) e := by unfold tabs; rw [ite_eq_right (by omega)]; exact hT
  obtain ⟨hTN, hTh, heT⟩ := (S.tabsIff _ e T hent).mp hT'
  obtain ⟨A, le, Bs, htab, hA⟩ := table_split (t := (nd s T).table) heT
  -- the insertion events of the table
  have hew := ew_le_any S Ti hTP hI.cap hTN
  have hg1 := hTP.gam1 (ht s T - 1) (by omega)
  have hp := Ro.pot2 T hTN (by omega)
  have hn0 := Ro.n0le T hTN
  have hc : 1 ≤ (if s.P.H < T then lamd s.P (ht s T) else 1) := by
    split
    · have := hTP.lamK (ht s T) (by omega); omega
    · exact le_rfl
  have hdr : dr T + 1 ≤ Dmax s.P (ht s T) := by
    unfold Dmax; rw [ite_eq_right (by omega)]
    set g := gamd s.P (ht s T - 1)
    have key : g * dr T + 1 ≤ Pid s.P (ht s T) + g * n0 T := by omega
    by_cases hdn : dr T ≤ n0 T
    · generalize Pid s.P (ht s T) / g = q; omega
    · have : dr T - n0 T ≤ Pid s.P (ht s T) / g := by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm, Nat.mul_sub]
        omega
      generalize Pid s.P (ht s T) / g = q at this; omega
  have hB := gap_two hn0 hdr (hTP.room _ (by omega))
  have hg := Ro.gaps T hTN
  unfold labs at hg; rw [htab] at hg
  obtain ⟨r1, r2, r3⟩ := gaps_room_around (y := y) (z := z) hB hg
  refine ⟨A, le, Bs, htab, hA, fun hd => ?_, r1, r2, hB, r3⟩
  have := S.side T ⟨hTN, hd⟩ e heT
  rw [this]; rfl

end OrderMaintenance.Proof.Top
