/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.Defs
public import LeanPool.OrderMaintenance.Impl.PeakBound
public import LeanPool.OrderMaintenance.Impl.PeakSafe


/-!
# Theorem W, option (A), stage A1: the leaves of the generic lemma from option (B)

`memW_of_enc`: a core with `WB K` (every stored value below `2^K`, handles excepted), handles
below `2^KH`, encoded in a machine state with capacities below `2^K`, satisfies `MemW K KH κ`,
the leaf hypothesis of `Exp.wd_sound`. So option (B)'s `theoremW_stored` provides the leaves
at the start of every core procedure; inside a procedure, each write must keep `MemW` (stage A2).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Impl

theorem b2n_lt {K : Nat} (hK : 1 ≤ K) (b : Bool) : b2n b < 2 ^ K := by
  have : 2 ≤ 2 ^ K := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  unfold b2n; split <;> omega

theorem small_lt {K n : Nat} (hK : 3 ≤ K) (hn : n ≤ 4) : n < 2 ^ K := by
  have : 8 ≤ 2 ^ K := by
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  omega

theorem St.toN_le (x : St) : x.toN ≤ 3 := by cases x <;> decide

theorem sideN_le (x : Side) : sideN x ≤ 1 := by cases x <;> decide

theorem getD_mem {α : Type} {l : List α} {j : Nat} {d : α} (hj : j < l.length) : l.getD j d ∈ l
  := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

theorem arrB_getX_of {K : Nat} {a : Array Nat} (h : ∀ v ∈ a, v < 2 ^ K) : ArrB K a :=
  fun i => getX_of (p := fun v => v < 2 ^ K) (pos K) h i

variable {K KH : Nat} {κ : Caps} {s : Core}

/-- The fields of a core with `WB`. -/
theorem fld_of_WB (hW : WB K s) (hK : 3 ≤ K) (hh : ∀ i, (s.E.getX i).h < 2 ^ KH) (f : Fld) (j :
  Nat) :
    f.get s j < 2 ^ f.wd K KH := by
  have hK1 : 1 ≤ K := by omega
  have h3 : ∀ x : St, x.toN < 2 ^ K := fun x => small_lt hK (le_trans (St.toN_le x) (by norm_num))
  cases f with
  | e k =>
    obtain ⟨h1, h2, h3, h4⟩ := hW.E j
    cases k <;> simp only [Fld.get, EF.get, Fld.wd] <;> first
      | assumption
      | exact b2n_lt hK1 _
      | exact hh j
  | g k =>
    obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, h9, h10⟩ := hW.Gs j
    cases k <;> simp only [Fld.get, GF.get, Fld.wd] <;> first
      | assumption
      | exact b2n_lt hK1 _
      | exact h3 _
  | c k =>
    obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, h9⟩ := hW.C j
    cases k <;> simp only [Fld.get, CF.get, Fld.wd] <;> first
      | assumption
      | exact b2n_lt hK1 _
      | exact h3 _
  | n k =>
    obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, -⟩ := hW.nodes j
    cases k <;> simp only [Fld.get, NF.get, Fld.wd] <;> first | assumption | exact b2n_lt hK1 _
  | a k =>
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hW.pq
    cases k <;> simp only [Fld.get, AF.get, Fld.wd]
    exacts [p1 j, p2 j, p3 j, p4 j, p5 j, p6 j, hW.lpar j]
  | s k =>
    obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8⟩ := hW.scalars
    cases k <;> simp only [Fld.get, SF.get, Fld.wd] <;> first | assumption | exact b2n_lt hK1 _

/-- The list entries of a core with `WB`. -/
theorem lst_of_WB (hW : WB K s) (hK : 3 ≤ K) (k : LK) (i j : Nat) (hj : j < (k.view s i).length) :
    ((k.view s i).getD j (0, 0)).1 < 2 ^ K ∧ ((k.view s i).getD j (0, 0)).2 < 2 ^ K := by
  have hm := getD_mem (d := (0, 0)) hj
  generalize (k.view s i).getD j (0, 0) = q at hm
  have hK1 : 1 ≤ K := by omega
  have h0 : 0 < 2 ^ K := pos K
  have h1 : 1 < 2 ^ K := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hK1)
  obtain ⟨-, -, -, -, -, -, -, -, hc, ht, hi, hs⟩ := hW.nodes i
  cases k with
  | children =>
    simp only [LK.view, List.mem_map] at hm; obtain ⟨c, hc', rfl⟩ := hm; exact ⟨hc c hc', h0⟩
  | table => simp only [LK.view] at hm; exact ht q hm
  | inTab =>
    simp only [LK.view, List.mem_map] at hm; obtain ⟨c, hc', rfl⟩ := hm; exact ⟨hi c hc', h0⟩
  | side =>
    simp only [LK.view, List.mem_map] at hm; obtain ⟨c, hc', rfl⟩ := hm
    exact ⟨hs c hc', lt_of_le_of_lt (sideN_le _) h1⟩
  | cin =>
    simp only [LK.view, List.mem_map] at hm; obtain ⟨c, hc', rfl⟩ := hm; exact ⟨hW.cin i c hc', h0⟩
  | freeG =>
    simp only [LK.view] at hm
    split at hm
    · simp only [List.mem_map,
      List.mem_reverse] at hm; obtain ⟨c, hc', rfl⟩ := hm; exact ⟨hW.freeG c hc', h0⟩
    · simp at hm

/-- The path rows of a core with `WB`. -/
theorem row_of_WB (hW : WB K s) (c j : Nat) : (rowOf s c).getX j < 2 ^ K := by
  unfold rowOf
  split
  · next pr hpr =>
    split
    · exact arrB_getX_of (hW.prep pr hpr).2.2.2.2 j
    · exact hW.path c j
  · exact hW.path c j

/-- The optional records of a core with `WB`. -/
theorem opt_of_WB (hW : WB K s) (hK : 3 ≤ K) (o : OF) : o.get s < 2 ^ K := by
  have hK1 : 1 ≤ K := by omega
  have h0 : 0 < 2 ^ K := pos K
  cases o
  case prepOn => exact b2n_lt hK1 _
  case jobOn => exact b2n_lt hK1 _
  all_goals simp only [OF.get]
  all_goals first
    | (cases hp : s.prep with
        | none => exact h0
        | some pr => obtain ⟨h1, h2, h3, h4, -⟩ := hW.prep pr hp; simp only; assumption)
    | (cases hj : s.resJob with
        | none => exact h0
        | some jb =>
          obtain ⟨h1, h2, h3, h4⟩ := hW.job jb hj
          simp only
          first
            | assumption
            | (rcases jb with ⟨x, y, z, pc⟩
               cases pc with
               | copy j' => simp only [pcEnc, JobPcB] at h4 ⊢; first | exact h4 | exact h0
               | walk v =>
                 cases v with
                 | none => simp only [pcEnc]; first | exact h0 | exact small_lt hK (by norm_num)
                 | some v => simp only [pcEnc, JobPcB] at h4 ⊢; first
                   | exact h4
                   | exact h0
                   | exact small_lt hK (by norm_num)
               | afterDrain v up =>
                 simp only [pcEnc,
                   JobPcB] at h4 ⊢; first
                     | exact h4.1
                     | exact h4.2
                     | exact h0
                     | exact small_lt hK (by norm_num)
               | fund v up src k =>
                 simp only [pcEnc, JobPcB] at h4 ⊢
                 first
                   | exact h4.1
                   | exact h4.2.1
                   | exact h4.2.2.1
                   | exact h4.2.2.2
                   | exact small_lt hK (by norm_num)))

/-- **The leaves of the generic lemma, from option (B).** A core with `WB K` (and handles below
`2^KH`) encoded with capacities below `2^K` satisfies `MemW K KH κ`. -/
theorem memW_of_enc {p : Nat} {m : Machine.State} (h : Enc p κ s m) (hW : WB K s) (hK : 3 ≤ K)
    (hh : ∀ i, (s.E.getX i).h < 2 ^ KH) (hT : ∀ t, κ.tbl t < 2 ^ K) (hpw : κ.pw < 2 ^ K) :
    MemW K KH κ s where
  fld f j _ := fld_of_WB hW hK hh f j
  size t := lt_of_le_of_lt (h.sle t) (hT t)
  prm k := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hW.P
    cases k <;> simp only [PF.get] <;> assumption
  H1 := by rw [← h.pwH]; exact hpw
  len k i hi := (h.llen k i hi).2
  lst k i j _ hj := lst_of_WB hW hK k i j hj
  row c j _ _ := row_of_WB hW c j
  opt o := opt_of_WB hW hK o

/-- **The stored values of a core with `WB`**, as the invariant of stage A2 needs them. -/
theorem vb_of_WB (hW : WB K s) (hK : 3 ≤ K) (hh : ∀ i, (s.E.getX i).h < 2 ^ KH) (hR : PRoom K s.P) :
    VB K KH κ s where
  fld f j _ := fld_of_WB hW hK hh f j
  prm k := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hW.P
    cases k <;> simp only [PF.get] <;> assumption
  lst k i j _ hj := lst_of_WB hW hK k i j hj
  row c j _ _ := row_of_WB hW c j
  opt o := opt_of_WB hW hK o
  room := hR

/-- **The invariant at the entry of a core procedure**, from option (B)'s `WB`. -/
theorem gd_of_WB {p : Nat} {m : Machine.State} {Γ : Machine.Reg → Nat} {L : Loc} (h : Enc p κ s m)
    (hW : WB K s) (hK : 3 ≤ K) (hh : ∀ i, (s.E.getX i).h < 2 ^ KH) (hR : PRoom K s.P)
    (hL : ∀ x, L x < 2 ^ Γ x) : Gd K KH κ Γ s L :=
  ⟨⟨p, m, h⟩, vb_of_WB hW hK hh hR, hL⟩

end OrderMaintenance.Proof.Word
