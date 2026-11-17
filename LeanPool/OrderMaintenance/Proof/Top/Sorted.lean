/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Shape


/-!
# M5: Lemma T1 (sorted tags)

(O1), (O2) and (W3) imply that the tags spelled by the paths strictly increase along the chunk
list (`docs/PROOF.md` §4.5.1). So every guarded tag write of the top structure passes its guard
when the state after the write satisfies `Shape`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Labels in a table -/

theorem gapsGe_chain {β B : Nat} {ls : List Nat} (h : GapsGe β B ls) (hB : 1 ≤ B) :
    ls.IsChain (· < ·) ∧ ∀ l ∈ ls, l < 2 ^ β := by
  unfold GapsGe at h
  constructor
  · have h1 : (ls.map (· + 1)).IsChain (fun a b => a + B ≤ b) := by
      have := (List.isChain_append.mp h).1
      exact (List.isChain_cons.mp this |>.2 |> fun h => h) |> fun x => by
        cases ls with
        | nil => simp
        | cons a t => exact (List.isChain_cons_cons.mp this).2
    have h2 : (ls.map (· + 1)).IsChain (· < ·) := h1.imp fun a b hab => by omega
    rw [List.isChain_map] at h2
    exact h2.imp fun a b hab => by omega
  · intro l hl
    have hc := List.isChain_iff_pairwise.mp (h.imp (R := fun a b => a + B ≤ b) (S := (· < ·))
      (fun a b hab => by omega))
    have hm1 : l + 1 ∈ 0 :: ls.map (· + 1) := List.mem_cons_of_mem _ (List.mem_map_of_mem hl)
    have := List.pairwise_append.mp hc |>.2.2 (l + 1) hm1 (2 ^ β + 1) (by simp)
    omega

/-- In a table with distinct entries and increasing labels, label order is table order. -/
theorem lookup_lt_of_before {t : List (Nat × Nat)} (hk : (t.map (·.1)).Nodup)
    (hl : (t.map (·.2)).IsChain (· < ·)) {a b : Nat} (h : Before (t.map (·.1)) a b) :
    ∃ la lb, lookup t a = some la ∧ lookup t b = some lb ∧ la < lb := by
  induction t with
  | nil => exact absurd h.mem_left (by simp)
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons] at hk hl h
    have hk' := List.nodup_cons.mp hk
    rw [before_cons] at h
    rcases h with h | ⟨rfl, hb⟩
    · have hab : a ≠ k := fun e => hk'.1 (e ▸ h.mem_left)
      have hbb : b ≠ k := fun e => hk'.1 (e ▸ h.mem_right)
      obtain ⟨la, lb, h1, h2, h3⟩ := ih hk'.2 (hl.tail) h
      refine ⟨la, lb, ?_, ?_, h3⟩
      · simp only [lookup, List.find?_cons] at h1 ⊢
        rw [show (k == a) = false by simp [Ne.symm hab]]; exact h1
      · simp only [lookup, List.find?_cons] at h2 ⊢
        rw [show (k == b) = false by simp [Ne.symm hbb]]; exact h2
    · have hbk : b ≠ a := fun e => hk'.1 (e ▸ hb)
      obtain ⟨⟨k', lb⟩, hmem, hfind⟩ : ∃ q ∈ t, lookup t b = some q.2 ∧ q.1 = b := by
        obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hb
        have : (t.find? (·.1 == b)).isSome := List.find?_isSome.mpr ⟨q, hq, by simp [hq1]⟩
        obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp this
        exact ⟨q', List.mem_of_find?_eq_some hq', by simp [lookup, hq'],
          by simpa using List.find?_some hq'⟩
      refine ⟨v, lb, by simp [lookup], ?_, ?_⟩
      · simp only [lookup, List.find?_cons] at hfind ⊢
        rw [show (a == b) = false by simp [Ne.symm hbk]]; exact hfind.1
      · have hp := List.isChain_iff_pairwise.mp hl
        rw [List.pairwise_cons] at hp
        exact hp.1 lb (List.mem_map.mpr ⟨(k', lb), hmem, rfl⟩)

/-! ### Lemma T1 -/

variable {s : TS} {cl : List Nat} {ord : Nat → List Nat}

theorem ShapeT.pp_root (S : ShapeT s cl ord) {c : Nat} (hc : c ∈ cl) : pp s c s.P.H = s.P.H := by
  have := S.pathEnt c hc s.P.H le_rfl
  unfold Ent at this; rw [S.root.1] at this; simpa using this

theorem ShapeT.labs_ok (S : ShapeT s cl ord) {X : Nat} (hX : isN s X) :
    (labs s X).IsChain (· < ·) ∧ ∀ l ∈ labs s X, l < 2 ^ s.P.beta :=
  gapsGe_chain (S.labsOk X hX) le_rfl

theorem ShapeT.order_nodup (S : ShapeT s cl ord) {X : Nat} (hX : isN s X) : (order s X).Nodup :=
  (S.O1 X hX).nodup (S.ordNodup _)

theorem ShapeT.isN_pp (S : ShapeT s cl ord) {c : Nat} (hc : c ∈ cl) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ s.P.H) : isN s (pp s c j) ∧ ht s (pp s c j) = j :=
  (S.ordMem j hj1 hj _).mp (S.pathEnt c hc j hj)

/-- A digit of a tag is a label of the table on the path, so it fits in `β` bits. -/
theorem ShapeT.digit_lt (S : ShapeT s cl ord) {c : Nat} (hc : c ∈ cl) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ s.P.H) : digit s c j < 2 ^ s.P.beta := by
  obtain ⟨hN, -⟩ := S.isN_pp hc hj1 hj
  have hw := S.W3 c hc j hj1 hj
  unfold digit
  obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hw
  have : ((nd s (pp s c j)).table.find? (·.1 == pp s c (j - 1))).isSome :=
    List.find?_isSome.mpr ⟨q, hq, by simp [hq1]⟩
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp this
  simp only [Node.lab?, lookup, hq', Option.map_some, Option.getD_some]
  exact (S.labs_ok hN).2 _ (List.mem_map.mpr ⟨q', List.mem_of_find?_eq_some hq', rfl⟩)

/-- **Lemma T1.** Tags strictly increase along the chunk list. -/
theorem ShapeT.tagF_lt (S : ShapeT s cl ord) {c d : Nat} (hcd : Before cl c d) :
    tagF s c < tagF s d := by
  have hc := hcd.mem_left
  have hd := hcd.mem_right
  have hne : c ≠ d := hcd.ne (S.ord0 ▸ S.ordNodup 0)
  -- the highest level where the paths differ
  have hex : ∃ j, ∀ i, j < i → i ≤ s.P.H → pp s c i = pp s d i :=
    ⟨s.P.H, fun i h1 h2 => by omega⟩
  classical
  let j := Nat.find hex
  have hjspec : ∀ i, j < i → i ≤ s.P.H → pp s c i = pp s d i := Nat.find_spec hex
  have hjne : pp s c j ≠ pp s d j := by
    by_cases hj0 : j = 0
    · rw [hj0]; simpa [pp] using hne
    · intro e
      have := Nat.find_min hex (show j - 1 < j by omega)
      apply this
      intro i hi1 hi2
      by_cases hij : i = j
      · rw [hij]; exact e
      · exact hjspec i (by omega) hi2
  have hjH : j < s.P.H := by
    by_contra hcon
    have : j = s.P.H := by
      have : j ≤ s.P.H := Nat.find_min' hex (fun i h1 h2 => by omega)
      omega
    rw [this, S.pp_root hc, S.pp_root hd] at hjne; exact hjne rfl
  -- the two entries in the common table
  have hX : pp s c (j + 1) = pp s d (j + 1) := hjspec (j + 1) (by omega) (by omega)
  obtain ⟨hXN, hXh⟩ := S.isN_pp hc (by omega) (show j + 1 ≤ s.P.H by omega)
  have hwc := S.W3 c hc (j + 1) (by omega) (by omega)
  have hwd := S.W3 d hd (j + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hwc hwd
  rw [← hX] at hwd
  have hO2 := (S.O2 j (by omega) c d hcd).resolve_left hjne
  have hsub := S.O1 _ hXN
  rw [hXh, Nat.add_sub_cancel] at hsub
  have hbt := before_of_sublist hsub (S.ordNodup j) hwc hwd hO2
  obtain ⟨la, lb, h1, h2, h3⟩ := lookup_lt_of_before (S.order_nodup hXN) (S.labs_ok hXN).1 hbt
  have hdig : digit s c (j + 1) < digit s d (j + 1) := by
    unfold digit
    simp only [Nat.add_sub_cancel, Node.lab?]
    rw [← hX]
    rw [show lookup (nd s (pp s c (j + 1))).table (pp s c j) = some la from h1,
      show lookup (nd s (pp s c (j + 1))).table (pp s d j) = some lb from h2]
    simpa using h3
  unfold tagF
  refine tagUp_lt_of_digit rfl (by omega) (fun i hi1 hi2 => S.digit_lt hc hi1 (by omega)) hdig
    s.P.H (by omega) (fun i hi1 hi2 => ?_)
  unfold digit
  rw [hjspec i (by omega) hi2, hjspec (i - 1) (by omega) (by omega)]

end OrderMaintenance.Proof.Top
