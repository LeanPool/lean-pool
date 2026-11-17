/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartTS


/-!
# M5: the tag-ordering invariant after a drain starts
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Evenly spaced labels -/

/-- A key's position in a table is unique. -/
theorem split_unique {A A' Bs Bs' : List (Nat × Nat)} {e le le' : Nat}
    (h : A ++ (e, le) :: Bs = A' ++ (e, le') :: Bs') (hA : e ∉ A.map (·.1)) (hA' : e ∉ A'.map
      (·.1)) :
    A = A' ∧ le = le' ∧ Bs = Bs' := by
  induction A generalizing A' with
  | nil =>
    cases A' with
    | nil => simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at h; exact
      ⟨rfl, h.1, h.2⟩
    | cons a A' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by rw [← h.1]; simp) hA'
  | cons a A ih =>
    cases A' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by rw [h.1]; simp) hA
    | cons a' A' =>
      simp only [List.cons_append, List.cons.injEq] at h
      simp only [List.map_cons, List.mem_cons, not_or] at hA hA'
      obtain ⟨e1, e2, e3⟩ := ih h.2 hA.2 hA'.2
      exact ⟨by rw [h.1, e1], e2, e3⟩

theorem chain_even (g : Nat) : ∀ (m x : Nat), m * g + 1 + g ≤ x →
    (0 :: (List.range m).map (fun i => (i + 1) * g + 1) ++ [x]).IsChain fun a b => a + g ≤ b
  | 0, x, hx => by simp; omega
  | m + 1, x, hx => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    rw [show 0 :: ((List.range m).map (fun i => (i + 1) * g + 1) ++ [(m + 1) * g + 1]) ++ [x] =
      (0 :: (List.range m).map (fun i => (i + 1) * g + 1) ++ [(m + 1) * g + 1]) ++ [x] by simp]
    rw [List.isChain_append]
    refine ⟨chain_even g m _ (by rw [Nat.succ_mul]; omega), List.isChain_singleton _, ?_⟩
    intro a ha b hb
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    rw [List.getLast?_append, List.getLast?_singleton] at ha
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at ha
    subst ha
    rw [Nat.succ_mul] at hx ⊢; omega

/-- **A fresh table's labels are evenly spaced.** -/
theorem evenTable_gaps (β : Nat) (part : List Nat) :
    GapsGe β (2 ^ β / (part.length + 1)) ((evenTable β part).map (·.2)) := by
  unfold GapsGe evenTable
  have key : ∀ f : Nat → Nat, ((List.range part.length).zip part).map (fun x => f x.1) =
      (List.range part.length).map f := by
    intro f
    rw [show (fun x : Nat × Nat => f x.1) = f ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (by simp)]
  have hl : ((((List.range part.length).zip part).map fun (x : Nat × Nat) =>
      (x.2, (x.1 + 1) * ((1 <<< β) / (part.length + 1)))).map (·.2)).map (· + 1) =
      (List.range part.length).map (fun i => (i + 1) * (2 ^ β / (part.length + 1)) + 1) := by
    simp only [List.map_map, Function.comp_def, Nat.one_shiftLeft]
    exact key (fun i => (i + 1) * (2 ^ β / (part.length + 1)) + 1)
  rw [hl]
  apply chain_even
  have h := Nat.div_mul_le_self (2 ^ β) (part.length + 1)
  have e : 2 ^ β / (part.length + 1) * (part.length + 1) =
      part.length * (2 ^ β / (part.length + 1)) + 2 ^ β / (part.length + 1) := by ring
  omega

/-- The order after `v` drains: `v1`, `v2` around `v` at its height. -/
def ordSD (ord : Nat → List Nat) (h v N : Nat) : Nat → List Nat :=
  fun k => if k = h then (ord h).replace1 v [N, v, N + 1] else ord k

namespace SDCtx

variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  {side : List (Nat × Side)} (C : SDCtx s cl ord dr n0 j v side)
include C

local notation "S'" => ts (sdS (wiC s v) v side)
local notation "O'" => ordSD ord (Top.ht (ts s) v) v s.nodes.size

theorem ordh : ∃ A B, ord (Top.ht (ts s) v) = A ++ v :: B ∧ v ∉ A ∧ v ∉ B ∧
    O' (Top.ht (ts s) v) = A ++ s.nodes.size :: v :: (s.nodes.size + 1) :: B := by
  have hm : v ∈ ord (Top.ht (ts s) v) := (C.S.ordMem _ C.h1 (C.S.htN v C.vl.1).2 v).mpr ⟨C.vl.1,
    rfl⟩
  obtain ⟨A, B, hAB⟩ := List.mem_iff_append.mp hm
  have hnd := C.S.ordNodup (Top.ht (ts s) v)
  rw [hAB] at hnd
  have h1 := List.nodup_append.mp hnd
  have hA : v ∉ A := fun h => h1.2.2 v h v (by simp) rfl
  have hB : v ∉ B := (List.nodup_cons.mp h1.2.1).1
  refine ⟨A, B, hAB, hA, hB, ?_⟩
  unfold ordSD; rw [ite_eq_left rfl, hAB, replace1_split _ hA]; simp

theorem fresh {k u : Nat} (hk : 1 ≤ k) (hk' : k ≤ s.P.H) (hu : u ∈ ord k) : u < s.nodes.size :=
  ((C.S.ordMem k hk hk' u).mp hu).1.2.1

theorem ord_mem (k u : Nat) : u ∈ O' k ↔ u ∈ ord k ∨ (k = Top.ht (ts s) v ∧ (u = s.nodes.size ∨
  u = s.nodes.size + 1)) := by
  by_cases hk : k = Top.ht (ts s) v
  · subst hk
    obtain ⟨A, B, hAB, -, -, h'⟩ := C.ordh
    rw [h', hAB]; simp only [List.mem_append, List.mem_cons, true_and]; tauto
  · unfold ordSD; rw [ite_eq_right hk]; simp [hk]

theorem ord_sub (k : Nat) : (ord k).Sublist (O' k) := by
  by_cases hk : k = Top.ht (ts s) v
  · subst hk
    obtain ⟨A, B, hAB, -, -, h'⟩ := C.ordh
    rw [h', hAB]
    exact (List.Sublist.refl A).append (((List.Sublist.refl B).cons _).cons_cons v |>.cons _)
  · unfold ordSD; rw [ite_eq_right hk]

theorem order_sup {X : Nat} (hX : Top.isN (ts s) X) (e : Nat) (he : e ∈ Top.order (ts s) X) :
    e ∈ Top.order S' X := by
  have hn := SDCtx.nN (s := s) X hX
  rw [C.order, ite_eq_right hn.1, ite_eq_right hn.2]
  split
  · next hT =>
    obtain ⟨-, -, hv⟩ := C.inTab X hT
    obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hv
    have hnd : (Top.order (ts s) X).Nodup := (C.S.ordNodup _).sublist (C.S.O1 X hX)
    rw [hPQ] at hnd he ⊢
    have hP : v ∉ P := fun h => (List.nodup_append.mp hnd).2.2 v h v (by simp) rfl
    rw [replace1_split _ hP]
    simp only [List.mem_append, List.mem_cons] at he ⊢; tauto
  · exact he

/-- The labels of a table holding `v`, after `v1`, `v2` join it. -/
theorem labs_tab {X : Nat} (hT : X ∈ (nd (ts s) v).inTables) :
    ∃ A le Bs, (nd (ts s) X).table = A ++ (v, le) :: Bs ∧ v ∉ A.map (·.1) ∧
      Top.labs S' X = (A ++ (s.nodes.size, (roomLo A le true + roomHi s.P.beta Bs le true - 1) /
        2) :: (v, le) ::
        (s.nodes.size + 1, (roomLo A le false + roomHi s.P.beta Bs le false - 1) / 2) :: Bs).map
          (·.2) := by
  have hX := (C.inTab X hT).1
  have hn := SDCtx.nN (s := s) X hX
  obtain ⟨A, le, Bs, htab, hA⟩ := table_split (C.inTab X hT).2.2
  refine ⟨A, le, Bs, htab, hA, ?_⟩
  unfold Top.labs
  rw [C.H.table, ite_eq_right hn.1, ite_eq_right hn.2, ite_eq_left hT, htab, aroundT_eq hA,
    roomL_eq hA, roomL_eq hA]
  rfl

/-- **The tag-ordering invariant after a drain starts.** -/
theorem shapeT : ShapeT S' cl O' := by
  have S := C.S
  have h3 := S.H3
  have hP : (ts s).P = s.P := rfl
  have hP' := SDHyps.P (s := s) (v := v) (side := side)
  have hvlt := C.H.hv
  have hh := C.h1
  have hhH := C.hH
  have h0 : O' 0 = ord 0 := by unfold ordSD; rw [ite_eq_right (by omega)]
  refine ⟨(by rw [hP']; exact h3), (by rw [h0]; exact S.ord0), fun k => ?_, fun k hk1 hk u =>
    ?_, fun k hk => ?_,
    fun u hu => ?_, ⟨?_, ?_, ?_⟩, fun c hc j hj => ?_, fun c hc j hj1 hj => ?_, fun j hj c d hcd
      => ?_,
    fun X hX => ?_, fun X hX => ?_⟩
  · -- ordNodup
    by_cases hk : k = Top.ht (ts s) v
    · subst hk
      obtain ⟨A, B, hAB, hA, hB, h'⟩ := C.ordh
      rw [h']
      have hnd := S.ordNodup (Top.ht (ts s) v)
      rw [hAB] at hnd
      have hfr : ∀ u ∈ A ++ v :: B, u < s.nodes.size := fun u hu =>
        C.fresh hh (by rw [hP] at h3; omega) (hAB ▸ hu)
      have h1 := List.nodup_append.mp hnd
      have hNA : s.nodes.size ∉ A := fun h => by have := hfr s.nodes.size (by simp [h]); omega
      have hNB : s.nodes.size ∉ B := fun h => by have := hfr s.nodes.size (by simp [h]); omega
      have hN1A : s.nodes.size + 1 ∉ A := fun h => by
        have := hfr (s.nodes.size + 1) (by simp [h])
        omega
      have hN1B : s.nodes.size + 1 ∉ B := fun h => by
        have := hfr (s.nodes.size + 1) (by simp [h])
        omega
      have hvN : v ≠ s.nodes.size := by have := C.H.hv; omega
      rw [List.nodup_append]
      refine ⟨h1.1, ?_, ?_⟩
      · simp only [List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨Ne.symm hvN, by omega, hNB⟩, ⟨by omega, hB⟩, hN1B, (List.nodup_cons.mp h1.2.1).2⟩
      · intro a ha b hb e; subst e
        simp only [List.mem_cons] at hb
        rcases hb with rfl | rfl | rfl | hb
        · exact hNA ha
        · exact hA ha
        · exact hN1A ha
        · exact h1.2.2 a ha a (by simp [hb]) rfl
    · unfold ordSD; rw [ite_eq_right hk]; exact S.ordNodup k
  · -- ordMem
    rw [hP'] at hk
    rw [C.ord_mem, S.ordMem k hk1 hk, C.isN, C.ht]
    constructor
    · rintro (⟨hn, hk'⟩ | ⟨rfl, hu⟩)
      · have := SDCtx.nN (s := s) u hn
        exact ⟨Or.inl hn, by rw [ite_eq_right (fun h => h.elim this.1 this.2)]; exact hk'⟩
      · exact ⟨Or.inr hu, by rw [ite_eq_left hu]⟩
    · rintro ⟨hn, hk'⟩
      by_cases hu : u = s.nodes.size ∨ u = s.nodes.size + 1
      · rw [ite_eq_left hu] at hk'; exact Or.inr ⟨hk'.symm, hu⟩
      · rw [ite_eq_right hu] at hk'
        rcases hn with hn | hn | hn
        · exact Or.inl ⟨hn, hk'⟩
        all_goals exact absurd (by tauto) hu
  · -- ordHigh
    rw [hP'] at hk
    unfold ordSD; rw [ite_eq_right (by omega)]; exact S.ordHigh k (by rw [hP]; omega)
  · -- htN
    rw [C.isN] at hu; rw [C.ht, hP']
    rcases hu with hu | hu | hu
    · have := SDCtx.nN (s := s) u hu; rw [ite_eq_right (fun h => h.elim this.1 this.2)]; exact
        S.htN u hu
    all_goals rw [ite_eq_left (by tauto)]; exact ⟨hh, by omega⟩
  · -- root
    rw [hP']; unfold ordSD; rw [ite_eq_right (by omega)]; exact S.root.1
  · rw [hP', C.liveN]
    have hr : Top.liveN (ts s) s.P.H := S.root.2.1
    refine Or.inl ⟨hr, fun e => ?_⟩
    have hc : Top.ht (ts s) s.P.H = s.P.H := C.Ti.chain s.P.H hr.1 le_rfl
    rw [e] at hc; omega
  · rw [hP']
    have hr : Top.liveN (ts s) s.P.H := S.root.2.1
    have hc : Top.ht (ts s) s.P.H = s.P.H := C.Ti.chain s.P.H hr.1 le_rfl
    have hHv : s.P.H ≠ v := fun e => by rw [e] at hc; omega
    rw [C.livePar_old hr.1 hHv (fun h1 hk => by
      obtain ⟨-, -, hkk⟩ := S.kids v C.vl
      have := ((S.mem_children C.vl).mp hk).1; rw [ite_eq_right h1] at this
      rw [this.2] at hc; omega)]
    exact S.root.2.2
  · -- pathEnt
    rw [hP'] at hj
    rw [SDCtx.pp]; exact (C.ord_sub j).subset (S.pathEnt c hc j hj)
  · -- W3
    rw [hP'] at hj
    rw [SDCtx.pp, SDCtx.pp]
    have hn := ((S.ordMem j hj1 hj _).mp (S.pathEnt c hc j hj)).1
    exact C.order_sup hn _ (S.W3 c hc j hj1 hj)
  · -- O2
    rw [hP'] at hj
    rw [SDCtx.pp, SDCtx.pp]
    rcases S.O2 j hj c d hcd with h | h
    · exact Or.inl h
    · exact Or.inr (h.mono (C.ord_sub j))
  · -- O1
    rw [C.isN] at hX
    rcases hX with hX | rfl | rfl
    · have hn := SDCtx.nN (s := s) X hX
      rw [C.ht,
        ite_eq_right (show ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) from fun h => h.elim hn.1
          hn.2),
        C.order, ite_eq_right hn.1, ite_eq_right hn.2]
      split
      · next hT =>
        obtain ⟨-, hXh, hvX⟩ := C.inTab X hT
        rw [hXh, Nat.add_sub_cancel]
        obtain ⟨A, B, hAB, hA, hB, h'⟩ := C.ordh
        rw [h']
        have hO := S.O1 X hX
        rw [hXh, Nat.add_sub_cancel, hAB] at hO
        obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hvX
        have hnd : (Top.order (ts s) X).Nodup := (S.ordNodup _).sublist (S.O1 X hX)
        rw [hPQ] at hnd hO ⊢
        have hP : v ∉ P := fun h => (List.nodup_append.mp hnd).2.2 v h v (by simp) rfl
        rw [replace1_split _ hP]
        have := sublist_around (y := s.nodes.size) (z := s.nodes.size + 1) hO hA hB
        simpa using this
      · exact (S.O1 X hX).trans (C.ord_sub _)
    · rw [C.order, ite_eq_left rfl, C.ht, ite_eq_left (Or.inl rfl)]
      unfold ordSD; rw [ite_eq_right (by omega)]
      refine List.filter_sublist.trans ?_
      unfold sEntries drainEntries
      rw [show ((wiC s v).nodes.getX v).order = Top.order (ts s) v from (wiC_sameTree s v).order v]
      exact List.filter_sublist.trans (S.O1 v C.vl.1)
    · rw [C.order, ite_eq_right (by omega), ite_eq_left rfl, C.ht, ite_eq_left (Or.inr rfl)]
      unfold ordSD; rw [ite_eq_right (by omega)]
      refine List.filter_sublist.trans ?_
      unfold sEntries drainEntries
      rw [show ((wiC s v).nodes.getX v).order = Top.order (ts s) v from (wiC_sameTree s v).order v]
      exact List.filter_sublist.trans (S.O1 v C.vl.1)
  · -- labsOk
    rw [hP']
    have hroom := C.TP.room _ hh
    have hpos : 1 ≤ 2 ^ Dmax s.P (Top.ht (ts s) v) := Nat.one_le_two_pow
    have hm1 : n0max s.P (Top.ht (ts s) v) + 1 ≤ 2 ^ s.P.beta := by
      calc n0max s.P (Top.ht (ts s) v) + 1 ≤ 2 ^ Dmax s.P (Top.ht (ts s) v) * (n0max s.P (Top.ht
        (ts s) v) + 1) :=
            Nat.le_mul_of_pos_left _ hpos
        _ ≤ 2 ^ s.P.beta := hroom
    rw [C.isN] at hX
    rcases hX with hX | rfl | rfl
    · have hn := SDCtx.nN (s := s) X hX
      by_cases hT : X ∈ (nd (ts s) v).inTables
      · obtain ⟨A, le, Bs, htab, hA, hl⟩ := C.labs_tab hT
        rw [hl]
        obtain ⟨A', le', Bs', htab', hA', -, -, -, hB, hg⟩ := room_up C.I C.TP C.vl.1 hT
          s.nodes.size (s.nodes.size + 1)
        rw [htab] at htab'
        obtain ⟨rfl, rfl, rfl⟩ := split_unique htab' hA hA'
        exact gapsGe_mono (by omega) hg
      · have : Top.labs S' X = Top.labs (ts s) X := by
          unfold Top.labs; rw [C.H.table, ite_eq_right hn.1, ite_eq_right hn.2, ite_eq_right hT]
        rw [this]; exact S.labsOk X hX
    · unfold Top.labs; rw [C.H.table, ite_eq_left rfl]
      have hlen := sc_left C.pc C.v0 C.I C.lp C.TP C.of C.W C.look
      refine gapsGe_mono ?_ (evenTable_gaps s.P.beta _)
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    · unfold Top.labs; rw [C.H.table, ite_eq_right (by omega), ite_eq_left rfl]
      have hlen := sc_right C.pc C.v0 C.I C.lp C.TP C.of C.W C.look
      refine gapsGe_mono ?_ (evenTable_gaps s.P.beta _)
      rw [Nat.le_div_iff_mul_le (by omega)]; omega

end SDCtx

end OrderMaintenance.Proof.Top
