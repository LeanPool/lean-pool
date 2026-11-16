/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.T0


/-!
# M5: labels in tables

A new entry next to entry `e` gets the midpoint of the gap on that side (`roomNextTo`), and is
inserted there (`tableInsert`). With the table split as `A ++ (e, l) :: B`: the run lemmas
`roomNextTo_run`, `tableInsert_run`, and the gap arithmetic `gapsGe_insert_before/after`: if all
gaps are at least `B ≥ 2`, the insertion succeeds and all gaps stay at least `B / 2`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Chains with gaps -/

theorem isChain_insert_mid {X Y : List Nat} {p q B : Nat} (hB : 2 ≤ B)
    (h : (X ++ p :: q :: Y).IsChain fun a b => a + B ≤ b) :
    (X ++ p :: (p + q) / 2 :: q :: Y).IsChain fun a b => a + B / 2 ≤ b := by
  have hmono : ∀ l : List Nat, l.IsChain (fun a b => a + B ≤ b) → l.IsChain (fun a b => a + B /
    2 ≤ b) :=
    fun l hl => hl.imp fun a b hab => by omega
  rw [List.isChain_append] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hmono _ h1, ?_, ?_⟩
  · have hpq := (List.isChain_cons_cons.mp h2).1
    have hr := (List.isChain_cons_cons.mp h2).2
    refine List.isChain_cons_cons.mpr ⟨by omega, List.isChain_cons_cons.mpr ⟨by omega, hmono _ hr⟩⟩
  · intro x hx y hy
    have := h3 x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy; omega

/-- The shifted labels of a table, with sentinels: all gaps at least `B`. -/
theorem gapsGe_split {β B : Nat} {A Bs : List (Nat × Nat)} {e le : Nat} :
    GapsGe β B ((A ++ (e, le) :: Bs).map (·.2)) ↔
      ((0 :: A.map (fun p : Nat × Nat => p.2 + 1)) ++ (le + 1) ::
        (Bs.map (fun p : Nat × Nat => p.2 + 1) ++ [2 ^ β + 1])).IsChain
        fun a b => a + B ≤ b := by
  unfold GapsGe
  simp only [List.map_append, List.map_cons, List.map_map]
  constructor <;> intro h <;> simpa [Function.comp_def, List.append_assoc] using h

/-! ### Room next to an entry -/

theorem findIdx_split {A Bs : List (Nat × Nat)} {e le : Nat} (hA : e ∉ A.map (·.1)) :
    (A ++ (e, le) :: Bs).findIdx? (·.1 == e) = some A.length := by
  induction A with
  | nil => simp [List.findIdx?_cons]
  | cons x t ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hA
    simp only [List.cons_append, List.findIdx?_cons, List.length_cons]
    rw [ite_eq_right (by simpa using Ne.symm hA.1), ih hA.2]
    rfl

theorem getD_split_left {A Bs : List (Nat × Nat)} {x : Nat × Nat} (hA : A ≠ []) :
    (A ++ x :: Bs).getD (A.length - 1) (0, 0) = A.getLast hA := by
  rw [List.getD_eq_getElem _ _ (by simp; have := List.length_pos_of_ne_nil hA; omega),
    List.getElem_append_left (by have := List.length_pos_of_ne_nil hA; omega),
    List.getLast_eq_getElem]

theorem getD_split_mid {A Bs : List (Nat × Nat)} {x : Nat × Nat} :
    (A ++ x :: Bs).getD A.length (0, 0) = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]; simp

theorem getD_split_right {A Bs : List (Nat × Nat)} {x : Nat × Nat} (hB : Bs ≠ []) :
    (A ++ x :: Bs).getD (A.length + 1) (0, 0) = Bs.head hB := by
  rw [List.getD_eq_getElem _ _ (by simp; have := List.length_pos_of_ne_nil hB; omega),
    List.getElem_append_right (by omega)]
  cases Bs with
  | nil => exact absurd rfl hB
  | cons b t => simp

/-- The label `roomNextTo` picks before (`before`) or after entry `e`. -/
def roomLo (A : List (Nat × Nat)) (le : Nat) (before : Bool) : Nat :=
  if before then (if h : A = [] then 0 else (A.getLast h).2 + 1) else le + 1
/-- The upper label boundary before or after an entry, with the full-width sentinel at the end. -/
def roomHi (β : Nat) (Bs : List (Nat × Nat)) (le : Nat) (before : Bool) : Nat :=
  if before then le else (if h : Bs = [] then 1 <<< β else (Bs.head h).2)

theorem roomNextTo_run {s : Core} {t e : Nat} {A Bs : List (Nat × Nat)} {le : Nat}
    (htab : (s.nodes.getX t).table = A ++ (e, le) :: Bs) (hA : e ∉ A.map (·.1)) (before : Bool)
    (hroom : roomLo A le before < roomHi s.P.beta Bs le before) :
    (roomNextTo t e before).run s =
      .ok ((roomLo A le before + roomHi s.P.beta Bs le before - 1) / 2) s := by
  unfold roomNextTo
  simp only [run_getP_bind, run_getN_bind, htab, findIdx_split hA]
  have hlo : (if before then (if A.length > 0 then ((A ++ (e, le) :: Bs).getD (A.length - 1) (0,
    0)).2 + 1
      else 0) else ((A ++ (e, le) :: Bs).getD A.length (0, 0)).2 + 1) = roomLo A le before := by
    unfold roomLo
    cases before
    · simp []
    · by_cases h : A = []
      · subst h; simp
      · simp only [ite_true, dite_eq_right h, ite_eq_left (List.length_pos_of_ne_nil h),
        getD_split_left h]
  have hhi : (if before then ((A ++ (e, le) :: Bs).getD A.length (0, 0)).2
      else (if A.length + 1 < (A ++ (e, le) :: Bs).length then
        ((A ++ (e, le) :: Bs).getD (A.length + 1) (0, 0)).2 else 1 <<< s.P.beta)) =
      roomHi s.P.beta Bs le before := by
    unfold roomHi
    cases before
    · by_cases h : Bs = []
      · subst h; simp
      · simp only [Bool.false_eq_true, ite_false, dite_eq_right h]
        have hpos := List.length_pos_of_ne_nil h
        rw [ite_eq_left (by simp only [List.length_append, List.length_cons]; omega),
          getD_split_right h]
    · simp []
  simp only [apply_ite Prod.fst, apply_ite Prod.snd]
  rw [hlo, hhi, ite_eq_right (Nat.not_le.mpr hroom)]
  rfl

/-! ### Enough gap: the insertion succeeds and gaps halve at worst -/

theorem last_zero_cons_map (A : List (Nat × Nat)) :
    ∃ X, 0 :: A.map (fun p : Nat × Nat => p.2 + 1) = X ++ [if h : A = [] then 0 else (A.getLast
      h).2 + 1] := by
  by_cases h : A = []
  · subst h; exact ⟨[], by simp⟩
  · obtain ⟨A', a, rfl⟩ := List.eq_nil_or_concat A |>.resolve_left h
    refine ⟨0 :: A'.map (fun p : Nat × Nat => p.2 + 1), ?_⟩
    rw [dite_eq_right h]
    simp

theorem gaps_room_before {β B : Nat} {A Bs : List (Nat × Nat)} {e le new : Nat} (hB : 2 ≤ B)
    (hg : GapsGe β B ((A ++ (e, le) :: Bs).map (·.2))) :
    roomLo A le true < roomHi β Bs le true ∧
      GapsGe β (B / 2) ((A ++ (new, (roomLo A le true + roomHi β Bs le true - 1) / 2) :: (e, le)
        :: Bs).map (·.2)) := by
  rw [gapsGe_split] at hg
  obtain ⟨X, hX⟩ := last_zero_cons_map A
  set p := (if h : A = [] then 0 else (A.getLast h).2 + 1) with hp
  have hlo : roomLo A le true = p := by simp [roomLo, hp]
  have hhi : roomHi β Bs le true = le := by simp [roomHi]
  rw [hX, List.append_assoc, List.singleton_append] at hg
  have hpq : p + B ≤ le + 1 := by
    have := List.isChain_append.mp hg |>.2.1
    exact (List.isChain_cons_cons.mp this).1
  rw [hlo, hhi]
  refine ⟨by omega, ?_⟩
  unfold GapsGe
  have hm := isChain_insert_mid hB hg
  have : (0 :: (A ++ (new, (p + le - 1) / 2) :: (e, le) :: Bs).map (·.2 + 1) ++ [2 ^ β + 1]) =
      X ++ p :: (p + (le + 1)) / 2 :: (le + 1) :: (Bs.map (fun q : Nat × Nat => q.2 + 1) ++ [2 ^
        β + 1]) := by
    have hX' := hX
    simp only [List.map_append, List.map_cons, List.cons_append, List.append_assoc]
    rw [show (0 :: (A.map (fun q : Nat × Nat => q.2 + 1) ++ ((p + le - 1) / 2 + 1) :: (le + 1) ::
        (Bs.map (fun q : Nat × Nat => q.2 + 1) ++ [2 ^ β + 1]))) =
        (0 :: A.map (fun q : Nat × Nat => q.2 + 1)) ++ ((p + le - 1) / 2 + 1) :: (le + 1) ::
        (Bs.map (fun q : Nat × Nat => q.2 + 1) ++ [2 ^ β + 1]) by simp, hX']
    simp only [List.append_assoc, List.singleton_append]
    rw [show (p + le - 1) / 2 + 1 = (p + (le + 1)) / 2 by omega]
  simp only [List.map_map, Function.comp_def] at this ⊢
  rw [this]; exact hm

theorem gaps_room_after {β B : Nat} {A Bs : List (Nat × Nat)} {e le new : Nat} (hB : 2 ≤ B)
    (hg : GapsGe β B ((A ++ (e, le) :: Bs).map (·.2))) :
    roomLo A le false < roomHi β Bs le false ∧
      GapsGe β (B / 2) ((A ++ (e, le) :: (new, (roomLo A le false + roomHi β Bs le false - 1) /
        2) :: Bs).map (·.2)) := by
  rw [gapsGe_split] at hg
  obtain ⟨q, hq⟩ : ∃ q, q = (if h : Bs = [] then 1 <<< β else (Bs.head h).2) := ⟨_, rfl⟩
  have hlo : roomLo A le false = le + 1 := by simp [roomLo]
  have hhi : roomHi β Bs le false = q := by simp [roomHi, hq]
  obtain ⟨Y, hY⟩ : ∃ Y, Bs.map (fun p : Nat × Nat => p.2 + 1) ++ [2 ^ β + 1] = (q + 1) :: Y := by
    cases Bs with
    | nil => exact ⟨[], by simp [hq, Nat.shiftLeft_eq]⟩
    | cons b t => exact ⟨t.map (fun p : Nat × Nat => p.2 + 1) ++ [2 ^ β + 1], by simp [hq]⟩
  rw [hY] at hg
  have hpq : le + 1 + B ≤ q + 1 := by
    have := List.isChain_append.mp hg |>.2.1
    exact (List.isChain_cons_cons.mp this).1
  rw [hlo, hhi]
  refine ⟨by omega, ?_⟩
  unfold GapsGe
  have hm := isChain_insert_mid (X := 0 :: A.map (fun p : Nat × Nat => p.2 + 1)) (Y := Y) hB hg
  have : (0 :: (A ++ (e, le) :: (new, (le + 1 + q - 1) / 2) :: Bs).map (·.2 + 1) ++ [2 ^ β + 1]) =
      (0 :: A.map (fun p : Nat × Nat => p.2 + 1)) ++ (le + 1) :: (le + 1 + (q + 1)) / 2 :: (q +
        1) :: Y := by
    simp only [List.map_append, List.map_cons, List.cons_append, List.append_assoc]
    rw [show (Bs.map (·.2 + 1) ++ [2 ^ β + 1]) = (q + 1) :: Y from by simpa using hY]
    rw [show (le + 1 + q - 1) / 2 + 1 = (le + 1 + (q + 1)) / 2 by omega]
  simp only [List.map_map, Function.comp_def] at this ⊢
  rw [this]; exact hm

/-! ### Two new entries around one -/

theorem isChain_insert_around {X Y : List Nat} {p r q B : Nat} (hB : 2 ≤ B)
    (h : (X ++ p :: r :: q :: Y).IsChain fun a b => a + B ≤ b) :
    (X ++ p :: (p + r) / 2 :: r :: (r + q) / 2 :: q :: Y).IsChain fun a b => a + B / 2 ≤ b := by
  have hmono : ∀ l : List Nat, l.IsChain (fun a b => a + B ≤ b) → l.IsChain (fun a b => a + B /
    2 ≤ b) :=
    fun l hl => hl.imp fun a b hab => by omega
  rw [List.isChain_append] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hmono _ h1, ?_, ?_⟩
  · have hpr := (List.isChain_cons_cons.mp h2).1
    have h2' := (List.isChain_cons_cons.mp h2).2
    have hrq := (List.isChain_cons_cons.mp h2').1
    have hr := (List.isChain_cons_cons.mp h2').2
    refine List.isChain_cons_cons.mpr ⟨by omega, List.isChain_cons_cons.mpr ⟨by omega,
      List.isChain_cons_cons.mpr ⟨by omega, List.isChain_cons_cons.mpr ⟨by omega, hmono _ hr⟩⟩⟩⟩
  · intro x hx y hy
    have := h3 x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy; omega

/-- **Room around an entry**: with all gaps at least `B ≥ 2`, both new labels exist, and with both
new entries all gaps stay at least `B / 2`. -/
theorem gaps_room_around {β B : Nat} {A Bs : List (Nat × Nat)} {e le y z : Nat} (hB : 2 ≤ B)
    (hg : GapsGe β B ((A ++ (e, le) :: Bs).map (·.2))) :
    roomLo A le true < roomHi β Bs le true ∧ roomLo A le false < roomHi β Bs le false ∧
      GapsGe β (B / 2) ((A ++ (y, (roomLo A le true + roomHi β Bs le true - 1) / 2) :: (e, le) ::
        (z, (roomLo A le false + roomHi β Bs le false - 1) / 2) :: Bs).map (·.2)) := by
  rw [gapsGe_split] at hg
  obtain ⟨X, hX⟩ := last_zero_cons_map A
  obtain ⟨p, hp⟩ : ∃ p, p = (if h : A = [] then 0 else (A.getLast h).2 + 1) := ⟨_, rfl⟩
  rw [← hp] at hX
  obtain ⟨q, hq⟩ : ∃ q, q = (if h : Bs = [] then 1 <<< β else (Bs.head h).2) := ⟨_, rfl⟩
  have hlo1 : roomLo A le true = p := by simp [roomLo, hp]
  have hhi1 : roomHi β Bs le true = le := by simp [roomHi]
  have hlo2 : roomLo A le false = le + 1 := by simp [roomLo]
  have hhi2 : roomHi β Bs le false = q := by simp [roomHi, hq]
  obtain ⟨Y, hY⟩ : ∃ Y, Bs.map (fun p : Nat × Nat => p.2 + 1) ++ [2 ^ β + 1] = (q + 1) :: Y := by
    cases Bs with
    | nil => exact ⟨[], by simp [hq, Nat.shiftLeft_eq]⟩
    | cons b t => exact ⟨t.map (fun p : Nat × Nat => p.2 + 1) ++ [2 ^ β + 1], by simp [hq]⟩
  rw [hX, hY, List.append_assoc, List.singleton_append] at hg
  have hc := List.isChain_append.mp hg |>.2.1
  have hpq : p + B ≤ le + 1 := (List.isChain_cons_cons.mp hc).1
  have hrq : le + 1 + B ≤ q + 1 := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hc).2).1
  rw [hlo1, hhi1, hlo2, hhi2]
  refine ⟨by omega, by omega, ?_⟩
  unfold GapsGe
  have hm := isChain_insert_around hB hg
  have : (0 :: (A ++ (y, (p + le - 1) / 2) :: (e, le) :: (z, (le + 1 + q - 1) / 2) :: Bs).map
    (·.2 + 1) ++
      [2 ^ β + 1]) = X ++ p :: (p + (le + 1)) / 2 :: (le + 1) :: (le + 1 + (q + 1)) / 2 :: (q +
        1) :: Y := by
    simp only [List.map_append, List.map_cons, List.cons_append, List.append_assoc]
    rw [show (Bs.map (·.2 + 1) ++ [2 ^ β + 1]) = (q + 1) :: Y from by simpa using hY]
    rw [show (0 :: (A.map (fun q : Nat × Nat => q.2 + 1) ++ ((p + le - 1) / 2 + 1) :: (le + 1) ::
        ((le + 1 + q - 1) / 2 + 1) :: (q + 1) :: Y)) =
        (0 :: A.map (fun q : Nat × Nat => q.2 + 1)) ++ ((p + le - 1) / 2 + 1) :: (le + 1) ::
        ((le + 1 + q - 1) / 2 + 1) :: (q + 1) :: Y by simp, hX]
    simp only [List.append_assoc, List.singleton_append]
    rw [show (p + le - 1) / 2 + 1 = (p + (le + 1)) / 2 by omega,
      show (le + 1 + q - 1) / 2 + 1 = (le + 1 + (q + 1)) / 2 by omega]
  simp only [List.map_map, Function.comp_def] at this ⊢
  rw [this]; exact hm

/-! ### Inserting the entry -/

/-- The side list after an insertion next to `e` in table `T`. -/
def sideAfter (T : Node) (e new : Nat) : List (Nat × Side) :=
  if T.draining then assocSet T.side new ((lookup T.side e).getD .left) else T.side

theorem insertIdx_len {α : Type} (A B : List α) (x y : α) :
    (A ++ y :: B).insertIdx A.length x = A ++ x :: y :: B := by
  induction A with
  | nil => simp
  | cons a t ih => simp [List.insertIdx_succ_cons, ih]

theorem insertIdx_len1 {α : Type} (A B : List α) (x y : α) :
    (A ++ y :: B).insertIdx (A.length + 1) x = A ++ y :: x :: B := by
  induction A with
  | nil => simp [List.insertIdx_succ_cons]
  | cons a t ih => simp [List.insertIdx_succ_cons, ih]

/-- The table after inserting `(new, lab)` before or after the entry `(e, le)`. -/
def insTab (A Bs : List (Nat × Nat)) (e le new lab : Nat) (before : Bool) : List (Nat × Nat) :=
  if before then A ++ (new, lab) :: (e, le) :: Bs else A ++ (e, le) :: (new, lab) :: Bs

/-- Updates a node table and its side map together. -/
def setTS (tab : List (Nat × Nat)) (side : List (Nat × Side)) (n : Node) : Node :=
  { n with table := tab, side := side }

theorem tableInsert_run {s : Core} {t e new : Nat} {A Bs : List (Nat × Nat)} {le : Nat}
    (htab : (s.nodes.getX t).table = A ++ (e, le) :: Bs) (hA : e ∉ A.map (·.1)) (before : Bool)
    (lab : Nat) (hside : (s.nodes.getX t).draining = true → (lookup (s.nodes.getX t).side
      e).isSome) :
    (tableInsert t e new before lab).run s = .ok ⟨⟩ { s with nodes := s.nodes.modify t (setTS
      (insTab A Bs e le new lab before) (sideAfter (s.nodes.getX t) e new)) } := by
  unfold tableInsert sideAfter setTS insTab
  simp only [run_getN_bind, htab, findIdx_split hA]
  have hins : (A ++ (e, le) :: Bs).insertIdx (if before then A.length else A.length + 1) (new,
    lab) =
      if before then A ++ (new, lab) :: (e, le) :: Bs else A ++ (e, le) :: (new, lab) :: Bs := by
    cases before
    · simp only [Bool.false_eq_true, ite_false]; exact insertIdx_len1 _ _ _ _
    · simp only [ite_true]; exact insertIdx_len _ _ _ _
  rw [hins]
  by_cases hd : (s.nodes.getX t).draining = true
  · obtain ⟨sd, hsd⟩ := Option.isSome_iff_exists.mp (hside hd)
    simp only [hd, ite_true, hsd, run_pure_bind, run_modN, Option.getD_some]
  · simp only [Bool.not_eq_true] at hd
    simp only [hd, Bool.false_eq_true, ite_false, run_pure_bind, run_modN]

end OrderMaintenance.Proof.Top
