/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.PrepStage


/-!
# M5: the complete initial chain satisfies the invariant

The chain `1 → 2 → … → H` above chunk `1`: node `k` has height `k`, the single child `k - 1`
(chunk `1` for `k = 1`), labelled `center`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- The level orders of the chain. -/
def chainOrd (P : Params) (h : Nat) : List Nat := if h = 0 then [1] else if h ≤ P.H then [h] else []

theorem center_two {P : Params} (hb : 1 ≤ P.beta) : 2 * center P = 2 ^ P.beta := by
  unfold center; rw [Nat.shiftLeft_eq, one_mul, ← Nat.pow_succ']; congr 1; omega

/-- A one-entry table labelled `center` has gaps `center`. -/
theorem gaps_center {P : Params} (hb : 1 ≤ P.beta) {B : Nat} (hB : B ≤ center P) :
    GapsGe P.beta B [center P] := by
  have := center_two hb
  unfold GapsGe
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.isChain_cons_cons,
    List.isChain_singleton, and_true]
  omega

theorem before_false {P : Params} {h u u' : Nat} (hb : Before (chainOrd P h) u u') : False := by
  have := hb.length_le
  unfold chainOrd at this
  by_cases h0 : h = 0
  · rw [ite_eq_left h0] at this; simp at this
  · rw [ite_eq_right h0] at this
    by_cases hH : h ≤ P.H
    · rw [ite_eq_left hH] at this; simp at this
    · rw [ite_eq_right hH] at this; simp at this

theorem n0max_pos {P : Params} (h : Nat) : 1 ≤ n0max P h := by
  unfold n0max; split
  · omega
  · exact Nat.le_trans (Nat.le_add_right 1 _) (Nat.le_add_right _ _)

namespace Final

variable {P : Params} {s : Core} (F : Final P s)
include F

theorem hP : (ts s).P = P := F.low.rest.1

theorem nd_eq (k : Nat) : nd (ts s) k = if 1 ≤ k ∧ k ≤ P.H then chainNd P P.H k else default := F.nodes k

theorem nd_of {k : Nat} (h1 : 1 ≤ k) (hH : k ≤ P.H) : nd (ts s) k = chainNd P P.H k := by
  rw [F.nd_eq, ite_eq_left ⟨h1, hH⟩]

theorem isN_iff (v : Nat) : isN (ts s) v ↔ 1 ≤ v ∧ v ≤ P.H := by
  unfold isN
  have hsz : (ts s).nodes.size = P.H + 1 := F.nsz
  rw [hsz]
  constructor
  · rintro ⟨h0, hlt, -⟩; unfold NIL at h0; omega
  · rintro ⟨h1, hH⟩; refine ⟨by unfold NIL; omega, by omega, ?_⟩
    rw [F.nd_of h1 hH]; rfl

theorem liveN_iff (v : Nat) : liveN (ts s) v ↔ 1 ≤ v ∧ v ≤ P.H := by
  unfold liveN; rw [F.isN_iff]
  constructor
  · exact fun h => h.1
  · intro h; refine ⟨h, ?_⟩; rw [F.nd_of h.1 h.2]; rfl

theorem not_ghost (v : Nat) : ¬ghostN (ts s) v := by
  rintro ⟨hn, hd⟩
  rw [F.isN_iff] at hn
  rw [F.nd_of hn.1 hn.2] at hd; exact absurd hd (by simp [chainNd])

theorem ht_of {v : Nat} (h1 : 1 ≤ v) (hH : v ≤ P.H) : ht (ts s) v = v := by
  unfold ht; rw [F.nd_of h1 hH]; rfl

theorem lpr1 : lpr (ts s) 1 = 1 := F.lpar
theorem cin1 : cinT (ts s) 1 = [1] := F.cin

theorem pp_eq {j : Nat} (hj : j ≤ P.H) : pp (ts s) 1 j = if j = 0 then 1 else j := by
  unfold pp pth
  split
  · rfl
  · have := F.path j
    rw [ite_eq_left ⟨by omega, hj⟩] at this; exact this

theorem anc_eq : ∀ j, 1 ≤ j → j ≤ P.H → anc (ts s) 1 j = j
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => F.lpr1
  | j + 2, _, hj => by
    show (nd (ts s) (anc (ts s) 1 (j + 1))).livePar = j + 2
    rw [anc_eq (j + 1) (by omega) (by omega), F.nd_of (by omega) (by omega)]
    simp [chainNd, show j + 1 < P.H by omega]

theorem tw_eq {u : Nat} (h1 : 1 ≤ u) (hH : u ≤ P.H) : tw (ts s) [1] u = 1 := by
  unfold tw; rw [F.ht_of h1 hH]; simp [F.anc_eq u h1 hH]

theorem rng_eq {u : Nat} (h1 : 1 ≤ u) (hH : u ≤ P.H) : rng (ts s) [1] u = [1] := by
  unfold rng; rw [F.ht_of h1 hH]; simp [F.pp_eq hH, show u ≠ 0 by omega]

theorem order_eq {X : Nat} (h1 : 1 ≤ X) (hH : X ≤ P.H) : order (ts s) X = [if X = 1 then 1 else X - 1] := by
  unfold order Node.order; rw [F.nd_of h1 hH]; simp [chainNd]

theorem labs_eq {X : Nat} (h1 : 1 ≤ X) (hH : X ≤ P.H) : labs (ts s) X = [center P] := by
  unfold labs; rw [F.nd_of h1 hH]; simp [chainNd]

theorem srcOf_eq (v : Nat) : srcOf (ts s) v = NIL := by
  unfold srcOf; rw [F.nd_eq]; split <;> rfl

theorem tabs0 : tabs (ts s) 0 1 = [1] := by unfold tabs; rw [ite_eq_left rfl]; exact F.cin1

theorem tabsH {h : Nat} (h1 : 1 ≤ h) (hH : h ≤ P.H) : tabs (ts s) h h = if h < P.H then [h + 1] else [] := by
  unfold tabs; rw [ite_eq_right (by omega), F.nd_of h1 hH]; rfl

theorem par_eq {h e : Nat} (h1 : 1 ≤ h) (he1 : 1 ≤ e) (heH : e ≤ P.H) :
    par (ts s) h e = if e < P.H then e + 1 else NIL := by
  unfold par; rw [ite_eq_right (by omega), F.nd_of he1 heH]; rfl

theorem digit_eq {j : Nat} (h1 : 1 ≤ j) (hH : j ≤ P.H) : digit (ts s) 1 j = center P := by
  unfold digit
  rw [F.pp_eq hH, ite_eq_right (by omega), F.pp_eq (j := j - 1) (by omega), F.nd_of h1 hH]
  simp only [Node.lab?, chainNd]
  by_cases hj : j = 1
  · subst hj; simp [lookup]
  · rw [ite_eq_right (show ¬(j - 1 = 0) by omega), ite_eq_right hj]; simp [lookup]

theorem tagUp_eq : ∀ m, m ≤ P.H → tagUp (ts s) 1 m = chainTag P m
  | 0, _ => rfl
  | m + 1, hm => by
    rw [tagUp_succ, tagUp_eq m (by omega), F.digit_eq (by omega) hm, F.hP]; rfl

theorem shapeT (H3 : 3 ≤ P.H) (hb : 1 ≤ P.beta) : ShapeT (ts s) [1] (chainOrd P) where
  H3 := by rw [F.hP]; exact H3
  ord0 := rfl
  ordNodup h := by
    unfold chainOrd
    by_cases h0 : h = 0
    · rw [ite_eq_left h0]; simp
    · rw [ite_eq_right h0]; by_cases hH : h ≤ P.H
      · rw [ite_eq_left hH]; simp
      · rw [ite_eq_right hH]; simp
  ordMem h h1 hH v := by
    rw [F.hP] at hH
    unfold chainOrd; rw [ite_eq_right (by omega), ite_eq_left hH, F.isN_iff]
    constructor
    · intro hv; simp at hv; subst hv; exact ⟨⟨h1, hH⟩, F.ht_of h1 hH⟩
    · rintro ⟨⟨a, b⟩, c⟩; rw [F.ht_of a b] at c; simp [c]
  ordHigh h hh := by
    rw [F.hP] at hh; unfold chainOrd; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  htN v hv := by
    rw [F.isN_iff] at hv; rw [F.ht_of hv.1 hv.2, F.hP]; omega
  root := by
    rw [F.hP]
    refine ⟨?_, (F.liveN_iff _).mpr ⟨by omega, le_rfl⟩, ?_⟩
    · unfold chainOrd; rw [ite_eq_right (by omega), ite_eq_left le_rfl]
    · rw [F.nd_of (by omega) le_rfl]; simp [chainNd]
  pathEnt c hc j hj := by
    simp only [List.mem_singleton] at hc; subst hc
    rw [F.hP] at hj
    show pp (ts s) 1 j ∈ chainOrd P j
    rw [F.pp_eq hj]; unfold chainOrd
    by_cases h0 : j = 0
    · rw [ite_eq_left h0, ite_eq_left h0]; simp
    · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_left hj]; simp
  W3 c hc j h1 hH := by
    simp only [List.mem_singleton] at hc; subst hc
    rw [F.hP] at hH
    rw [F.pp_eq (j := j - 1) (by omega), F.pp_eq hH, ite_eq_right (show ¬(j = 0) by omega),
      F.order_eq h1 hH]
    by_cases hj : j = 1
    · subst hj; simp
    · rw [ite_eq_right (show ¬(j - 1 = 0) by omega)]; simp [hj]
  O2 j hj c d hb' := by
    exfalso; have := hb'.length_le; simp at this
  O1 X hX := by
    rw [F.isN_iff] at hX
    rw [F.order_eq hX.1 hX.2, F.ht_of hX.1 hX.2]
    unfold chainOrd
    by_cases hX1 : X = 1
    · subst hX1; simp
    · rw [ite_eq_right hX1, ite_eq_right (by omega), ite_eq_left (by omega)]
  labsOk X hX := by
    rw [F.isN_iff] at hX
    rw [F.labs_eq hX.1 hX.2, F.hP]
    apply gaps_center hb
    unfold center; rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow

theorem ord_sub {u : Nat} (h1 : 1 ≤ u) (hH : u ≤ P.H) :
    [if u = 1 then 1 else u - 1].Sublist (chainOrd P (u - 1)) := by
  unfold chainOrd
  by_cases hu : u = 1
  · subst hu; simp
  · rw [ite_eq_right hu, ite_eq_right (by omega), ite_eq_left (by omega)]

theorem shape (H3 : 3 ≤ P.H) (hb : 1 ≤ P.beta) : Shape (ts s) [1] (chainOrd P) where
  toShapeT := F.shapeT H3 hb
  up v hv hh := by
    rw [F.liveN_iff] at hv
    rw [F.ht_of hv.1 hv.2, F.hP] at hh
    rw [F.ht_of hv.1 hv.2, F.nd_of hv.1 hv.2]
    simp only [chainNd, ite_eq_left hh]
    refine ⟨(F.liveN_iff _).mpr ⟨by omega, by omega⟩, F.ht_of (by omega) (by omega), ?_⟩
    rw [F.nd_of (by omega) (by omega)]; simp [chainNd]; omega
  lp c hc := by
    simp only [List.mem_singleton] at hc; subst hc
    rw [F.lpr1]
    refine ⟨(F.liveN_iff _).mpr ⟨le_rfl, by omega⟩, F.ht_of le_rfl (by omega), ?_⟩
    rw [F.nd_of le_rfl (by omega)]; simp [chainNd]
  kids u hu := by
    rw [F.liveN_iff] at hu
    rw [F.ht_of hu.1 hu.2]
    have hc : (nd (ts s) u).children = [if u = 1 then 1 else u - 1] := by rw [F.nd_of hu.1 hu.2]; rfl
    rw [hc]
    refine ⟨by simp, F.ord_sub hu.1 hu.2, fun e he => ?_⟩
    simp only [List.mem_singleton] at he
    by_cases hu1 : u = 1
    · subst hu1; rw [ite_eq_left rfl] at he; subst he
      exact ⟨by unfold par; rw [ite_eq_left rfl]; exact F.lpr1, fun h => absurd h (by omega)⟩
    · rw [ite_eq_right hu1] at he; subst he
      refine ⟨?_, fun _ => (F.liveN_iff _).mpr ⟨by omega, by omega⟩⟩
      rw [F.par_eq (by omega) (by omega) (by omega), ite_eq_left (by omega)]; omega
  OT h _ _ u u' e e' _ _ hb' := absurd hb' (fun h => before_false h)
  ghost v hv := absurd hv (F.not_ghost v)
  src t _ hs := absurd (F.srcOf_eq t) hs
  tabEnt X hX e he := ((F.shapeT H3 hb).O1 X hX).subset he
  tabsIff h e X he := by
    unfold Ent chainOrd at he
    by_cases h0 : h = 0
    · rw [ite_eq_left h0] at he; simp only [List.mem_singleton] at he; subst h0; subst he
      rw [F.tabs0, F.isN_iff]
      constructor
      · intro hX; simp only [List.mem_singleton] at hX; subst hX
        refine ⟨⟨le_rfl, by omega⟩, F.ht_of le_rfl (by omega), ?_⟩
        rw [F.order_eq le_rfl (by omega)]; simp
      · rintro ⟨⟨a, b⟩, c, -⟩; rw [F.ht_of a b] at c; simp [c]
    · rw [ite_eq_right h0] at he
      by_cases hH : h ≤ P.H
      · rw [ite_eq_left hH] at he; simp only [List.mem_singleton] at he; subst he
        rw [F.tabsH (by omega) hH, F.isN_iff]
        constructor
        · intro hX
          by_cases hlt : e < P.H
          · rw [ite_eq_left hlt] at hX; simp only [List.mem_singleton] at hX; subst hX
            refine ⟨⟨by omega, by omega⟩, F.ht_of (by omega) (by omega), ?_⟩
            rw [F.order_eq (by omega) (by omega), ite_eq_right (by omega)]; simp
          · rw [ite_eq_right hlt] at hX; simp at hX
        · rintro ⟨⟨a, b⟩, c, -⟩
          rw [F.ht_of a b] at c
          rw [ite_eq_left (by omega)]; simp [c]
      · rw [ite_eq_right hH] at he; simp at he
  tabsNodup h e he := by
    unfold Ent chainOrd at he
    by_cases h0 : h = 0
    · rw [ite_eq_left h0] at he; simp only [List.mem_singleton] at he; subst h0; subst he
      rw [F.tabs0]; simp
    · rw [ite_eq_right h0] at he
      by_cases hH : h ≤ P.H
      · rw [ite_eq_left hH] at he; simp only [List.mem_singleton] at he; subst he
        rw [F.tabsH (by omega) hH]; split <;> simp
      · rw [ite_eq_right hH] at he; simp at he
  Q h e X he hX := by
    left
    unfold Ent chainOrd at he
    by_cases h0 : h = 0
    · rw [ite_eq_left h0] at he; simp only [List.mem_singleton] at he; subst h0; subst he
      rw [F.tabs0] at hX; simp only [List.mem_singleton] at hX; subst hX
      unfold par; rw [ite_eq_left rfl, F.lpr1]
    · rw [ite_eq_right h0] at he
      by_cases hH : h ≤ P.H
      · rw [ite_eq_left hH] at he; simp only [List.mem_singleton] at he; subst he
        rw [F.tabsH (by omega) hH] at hX
        rw [F.par_eq (by omega) (by omega) hH]
        split at hX
        · next hlt => simp only [List.mem_singleton] at hX; rw [ite_eq_left hlt, hX]
        · simp at hX
      · rw [ite_eq_right hH] at he; simp at he
  W1 v hv := absurd hv (F.not_ghost v)
  side v hv := absurd hv (F.not_ghost v)
  pathSize c hc := by
    simp only [List.mem_singleton] at hc; subst hc
    rw [F.hP]; exact F.psz
  P c hc j h1 hH := by
    simp only [List.mem_singleton] at hc; subst hc
    rw [F.hP] at hH
    left; rw [F.pp_eq hH, ite_eq_right (by omega), F.anc_eq j h1 hH]
  Sr c _ j _ _ hg := absurd hg (F.not_ghost _)
  ends u hu := by
    rw [F.isN_iff] at hu
    rw [F.rng_eq hu.1 hu.2, F.nd_of hu.1 hu.2]
    exact ⟨rfl, rfl⟩
  tags c hc := by
    simp only [List.mem_singleton] at hc; subst hc
    show (s.C.getX 1).tag = tagUp (ts s) 1 (ts s).P.H
    rw [F.hP, F.tagUp_eq P.H le_rfl]; exact F.tag

theorem ew_eq {u : Nat} (h1 : 1 ≤ u) (hH : u ≤ P.H) : ew (ts s) [1] u = 1 := by
  unfold ew; rw [ite_eq_right (by rw [F.nd_of h1 hH]; simp [chainNd]), F.tw_eq h1 hH]

theorem weight_eq {u : Nat} (h1 : 1 ≤ u) (hH : u ≤ P.H) : (nd (ts s) u).weight = 1 := by
  rw [F.nd_of h1 hH]; rfl

theorem time (hTP : TopParams P) : Timing (ts s) [1] none := by
  have ha : 2 ≤ P.a := by have := hTP.lamK 1 le_rfl; simp [lamd] at this; omega
  refine ⟨fun u hu => ?_, fun u hu _ _ => ?_, fun g hg => absurd hg (F.not_ghost g),
    fun g hg => absurd hg (F.not_ghost g), fun g hg => absurd hg (F.not_ghost g),
    fun g hg => absurd hg (F.not_ghost g), fun u hu hH => ?_, fun t _ hs => absurd (F.srcOf_eq t) hs,
    fun u hu _ => ?_, fun u hu => ?_⟩
  · rw [F.liveN_iff] at hu
    simp only [pend, List.not_mem_nil, ite_false, Nat.add_zero]
    rw [F.weight_eq hu.1 hu.2, F.tw_eq hu.1 hu.2]
  · rw [F.liveN_iff] at hu
    rw [F.weight_eq hu.1 hu.2, F.hP]
    unfold Wd
    have := Nat.one_le_pow (ht (ts s) u) P.a (by omega)
    omega
  · rw [F.liveN_iff] at hu; rw [F.hP] at hH; omega
  · rw [F.isN_iff] at hu; exact F.ht_of hu.1 hu.2
  · rw [F.liveN_iff] at hu; rw [F.tw_eq hu.1 hu.2]

theorem room (hTP : TopParams P) (hb : 1 ≤ P.beta) : Room (ts s) [1] (fun _ => 0) (fun _ => 1) := by
  refine ⟨fun X hX => ?_, fun X hX => ?_, fun X hX h1 => ?_, fun X hX h2 => ?_⟩
  · rw [F.isN_iff] at hX
    rw [F.labs_eq hX.1 hX.2, F.hP]
    apply gaps_center hb
    unfold gapB; have := center_two hb; simp; omega
  · exact n0max_pos _
  · rw [F.isN_iff] at hX
    rw [F.ht_of hX.1 hX.2] at h1; subst h1
    rw [F.ew_eq le_rfl hX.2, F.hP, ite_eq_right (by omega)]
  · rw [F.isN_iff] at hX
    have hht := F.ht_of hX.1 hX.2
    rw [hht] at h2
    have hgr : growth (ts s) [1] X = 0 := by
      unfold growth; rw [F.order_eq hX.1 hX.2, ite_eq_right (by omega)]
      simp only [List.filter_cons, List.filter_nil]
      rw [ite_eq_right (by simp)]; rfl
    have hol : oldLive (ts s) X = 1 := by
      unfold oldLive; rw [F.order_eq hX.1 hX.2, ite_eq_right (by omega)]
      simp only [List.filter_cons, List.filter_nil]
      rw [ite_eq_left (by simp; exact ⟨(F.liveN_iff _).mpr ⟨by omega, by omega⟩, by omega⟩)]; rfl
    rw [hgr, hol, F.ew_eq hX.1 hX.2, F.hP, ite_eq_right (by omega)]
    simp

/-- **The complete chain satisfies the top structure's invariant.** -/
theorem topInv (hTP : TopParams P) (H3 : 3 ≤ P.H) : TopInv s := by
  have hb : 1 ≤ P.beta := by
    have h := hTP.room 1 le_rfl
    have h1 : 1 ≤ 2 ^ Dmax P 1 := Nat.one_le_two_pow
    have h2 : 2 ≤ n0max P 1 + 1 := by have := n0max_pos (P := P) 1; omega
    have : 2 ≤ 2 ^ P.beta := le_trans (by nlinarith) h
    by_contra hb0
    rw [show P.beta = 0 by omega] at this; simp at this
  have ha : 2 ≤ P.a := by have := hTP.lamK 1 le_rfl; simp [lamd] at this; omega
  have hP : s.P = P := F.hP
  have hCs : s.C.size = 2 := F.low.Csize
  have hC1 : s.C.getX 1 = { (initState P).C.getX 1 with tag := (s.C.getX 1).tag } := F.low.C 1
  have hfc : s.firstChunk = 1 := F.low.rest.2.2.2.2.2.1
  unfold TopInv; rw [F.res]; simp only [finS]
  refine ⟨by rw [hP]; exact hTP, [1], chainOrd P, fun _ => 0, fun _ => 1, ⟨by simp, by simp [NIL], ?_, ?_, ?_⟩,
    fun c => ?_, ⟨F.shape H3 hb, F.time hTP, F.room hTP hb, fun _ h => absurd h (by simp), ?_, fun X => ?_⟩⟩
  · rw [hfc]; rfl
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx
    show (s.C.getX 1).next = _; rw [hC1]; rfl
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx
    show (s.C.getX 1).prev = _; rw [hC1]; rfl
  · rw [hCs]; simp; omega
  · show 1 + 2 ≤ Wd (ts s).P ((ts s).P.H - 1)
    rw [F.hP]; unfold Wd
    have : 2 ^ (P.H - 1) ≤ P.a ^ (P.H - 1) := Nat.pow_le_pow_left ha _
    have : 2 ≤ 2 ^ (P.H - 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (P.H - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · unfold order Node.order
    rw [F.nd_eq X]
    split
    · simp [chainNd]
    · exact ⟨Nat.zero_le _, Nat.zero_le _, by norm_num⟩

end Final

end OrderMaintenance.Proof.Top
