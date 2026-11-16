/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.PrepRun


/-!
# M5: the stages of the initial chain's construction

Stage `h` (`1 ≤ h ≤ H + 1`): nodes `1, …, h-1` of the chain are built, node `k` of height `k`
above `k - 1` (chunk `1` for `k = 1`); `Final`: the chain is complete, with chunk `1`'s path and
tag stored.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- The label of every chain entry: the middle of the label range. -/
def center (P : Params) : Nat := 1 <<< (P.beta - 1)

/-- The tag of the chain's lowest `m` levels. -/
def chainTag (P : Params) : Nat → Nat
  | 0 => 0
  | m + 1 => chainTag P m + center P * 2 ^ (m * P.beta)

/-- Node `k` of the chain once nodes `1, …, m` are built. -/
def chainNd (P : Params) (m k : Nat) : Node :=
  { height := k, livePar := if k < m then k + 1 else NIL,
    children := [if k = 1 then 1 else k - 1], weight := 1,
    table := [(if k = 1 then 1 else k - 1, center P)],
    inTables := if k < m then [k + 1] else [],
    first := 1, last := 1 }

/-- Stage `h` of the construction. -/
structure Stage (P : Params) (h : Nat) (s : Core) : Prop where
  low : TopRelR (initState P) s
  res : s.resJob = none
  pr : ∃ pa : Array Nat, s.prep = some
      { chunk := 1, h := h, below := if h = 1 then 1 else h - 1, tag := chainTag P (h - 1), path := pa } ∧
    pa.size = P.H + 1 ∧ ∀ j, pa.getX j = if 1 ≤ j ∧ j < h then j else NIL
  nsz : 2 ≤ h → s.nodes.size = h
  nodes : 2 ≤ h → ∀ k, s.nodes.getX k = if 1 ≤ k ∧ k < h then chainNd P (h - 1) k else default
  cin : 2 ≤ h → s.cin.getX 1 = [1]
  lpar : 2 ≤ h → s.lpar.getX 1 = 1

/-- The complete chain. -/
structure Final (P : Params) (s : Core) : Prop where
  low : TopRelR (initState P) s
  res : s.resJob = none
  prep : s.prep = none
  nsz : s.nodes.size = P.H + 1
  nodes : ∀ k, s.nodes.getX k = if 1 ≤ k ∧ k ≤ P.H then chainNd P P.H k else default
  cin : s.cin.getX 1 = [1]
  lpar : s.lpar.getX 1 = 1
  psz : (s.path.getX 1).size = P.H + 1
  path : ∀ j, (s.path.getX 1).getX j = if 1 ≤ j ∧ j ≤ P.H then j else NIL
  tag : (s.C.getX 1).tag = chainTag P P.H

theorem Stage.P {P : Params} {h : Nat} {s : Core} (S : Stage P h s) : s.P = P := S.low.rest.1

theorem center_lt {P : Params} (hb : 1 ≤ P.beta) : center P < 2 ^ P.beta := by
  unfold center; rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by omega) (by omega)

theorem chainTag_lt {P : Params} (hb : 1 ≤ P.beta) : ∀ m, chainTag P m < 2 ^ (m * P.beta)
  | 0 => by simp [chainTag]
  | m + 1 => by
    have ih := chainTag_lt hb m
    have hc := center_lt hb
    show chainTag P m + center P * 2 ^ (m * P.beta) < 2 ^ ((m + 1) * P.beta)
    rw [Nat.add_mul, one_mul, Nat.pow_add, Nat.mul_comm (2 ^ (m * P.beta))]
    have : (center P + 1) * 2 ^ (m * P.beta) ≤ 2 ^ P.beta * 2 ^ (m * P.beta) :=
      Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul, one_mul] at this
    omega

theorem chainTag_succ {P : Params} (hb : 1 ≤ P.beta) (m : Nat) :
    chainTag P m ||| (center P <<< (m * P.beta)) = chainTag P (m + 1) := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt (chainTag_lt hb m), Nat.shiftLeft_eq]
  show _ = chainTag P m + center P * 2 ^ (m * P.beta)
  omega

/-- A step that only rewrites the top structure keeps the relation to the initial state. -/
theorem TopRelR.top {P : Params} {s : Core} (h : TopRelR (initState P) s) (nodes : Array Node)
    (path : Array (Array Nat)) (cin : Array (List Nat)) (lpar : Array Nat) (pr : Option Prep) :
    TopRelR (initState P) { s with nodes := nodes, path := path, cin := cin, lpar := lpar, prep := pr } :=
  h.trans (TopRel.topRelR ⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩)

/-- The lazy construction starts at stage 1. -/
theorem initCore_lazy_run (s : Core) : (initCore true).run s = .ok ()
    { initState s.P with
      prep := some { chunk := 1, below := 1, path := Array.replicate (s.P.H + 1) NIL },
      ready := false } := by
  unfold initCore initTop
  simp
  rfl

theorem stage_one (s : Core) (r : Bool) : Stage s.P 1
    { initState s.P with
      prep := some { chunk := 1, below := 1, path := Array.replicate (s.P.H + 1) NIL },
      ready := r } := by
  refine ⟨?_, rfl, ⟨_, rfl, by simp, fun j => ?_⟩, fun h => absurd h (by omega),
    fun h => absurd h (by omega), fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  · exact TopRel.topRelR ⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ |>.trans (by
        unfold TopRelR; exact ⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩)
  · rw [ite_eq_right (by omega)]
    simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl

/-- The first step: stage 1 to stage 2. -/
theorem stage_first {P : Params} {s : Core} (S : Stage P 1 s) (hH : 1 ≤ P.H) (hb : 1 ≤ P.beta) :
    ∃ s', initStep.run s = .ok false s' ∧ Stage P 2 s' ∧ s'.ready = s.ready := by
  obtain ⟨pa, hp, hsz, hpa⟩ := S.pr
  have hP := S.P
  rw [ite_eq_left rfl] at hp
  refine ⟨_, initStep_first s _ hp rfl (by rw [hP]; exact hH), ?_, rfl⟩
  refine ⟨TopRelR.top S.low _ _ _ _ _, S.res, ⟨pa.setX 1 1, ?_, ?_, fun j => ?_⟩, fun _ => ?_, fun _ k => ?_,
    fun _ => ?_, fun _ => ?_⟩
  · simp only [prepNext, hP]
    congr 2
    have := chainTag_succ hb 0
    simp only [Nat.zero_mul] at this
    simp only [Nat.zero_mul, Nat.sub_self]
    exact this
  · rw [size_setX', hsz]; omega
  · rw [getX_setX', hpa]
    by_cases hj : j = 1
    · subst hj; simp
    · rw [ite_eq_right hj, ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp
  · rw [getX_modify', getX_push']
    by_cases hk : k = 1
    · subst hk
      simp [chainNew, chainNd, center, hP, NIL]
    · rw [ite_eq_right (fun h => hk h.1)]
      by_cases hk0 : k = 0
      · subst hk0; simp; rfl
      · rw [ite_eq_right (by simp; omega), ite_eq_right (by omega), getX_ge (by simp; omega)]
  · rw [getX_setX', ite_eq_left rfl]
  · rw [getX_setX', ite_eq_left rfl]

/-- A middle step: stage `h` to stage `h + 1`. -/
theorem stage_mid {P : Params} {h : Nat} {s : Core} (S : Stage P h s) (h2 : 2 ≤ h) (hH : h ≤ P.H)
    (hb : 1 ≤ P.beta) : ∃ s', initStep.run s = .ok false s' ∧ Stage P (h + 1) s' ∧ s'.ready = s.ready := by
  obtain ⟨pa, hp, hsz, hpa⟩ := S.pr
  have hP := S.P
  have hn := S.nsz h2
  rw [ite_eq_right (by omega)] at hp
  refine ⟨_, initStep_mid s _ hp (by simp; omega) (by rw [hP]; exact hH), ?_, rfl⟩
  simp only [hn]
  refine ⟨TopRelR.top S.low _ _ _ _ _, S.res, ⟨pa.setX h h, ?_, ?_, fun j => ?_⟩, fun _ => ?_,
    fun _ k => ?_, fun _ => S.cin h2, fun _ => S.lpar h2⟩
  · simp only [prepNext, hP]
    rw [ite_eq_right (by omega), show h + 1 - 1 = h by omega]
    congr 2
    have := chainTag_succ hb (h - 1)
    rw [show h - 1 + 1 = h by omega] at this
    exact this
  · rw [size_setX', hsz]; omega
  · rw [getX_setX', hpa]
    by_cases hj : j = h
    · subst hj; rw [ite_eq_left rfl, ite_eq_left (by omega)]
    · rw [ite_eq_right hj]
      by_cases hj2 : 1 ≤ j ∧ j < h
      · rw [ite_eq_left hj2, ite_eq_left (by omega)]
      · rw [ite_eq_right hj2, ite_eq_right (by omega)]
  · simp [hn]
  · have hold := S.nodes h2
    rw [getX_modify', getX_modify', getX_push']
    simp only [Array.size_modify, Array.size_push, hn]
    by_cases hk : k = h - 1
    · rw [ite_eq_left ⟨hk, by omega⟩, ite_eq_right (show ¬(k = h ∧ h < h + 1) by omega),
      ite_eq_right (show ¬(k = h) by omega),
        hold k, ite_eq_left (show 1 ≤ k ∧ k < h by omega), ite_eq_left (show 1 ≤ k ∧ k < h + 1 by omega), hk]
      simp [chainNd, show h - 1 < h by omega]; omega
    · rw [ite_eq_right (fun e => hk e.1)]
      by_cases hkh : k = h
      · rw [ite_eq_left ⟨hkh, by omega⟩, ite_eq_left hkh, ite_eq_left (by omega), hkh]
        simp [chainNew, chainNd, hP, center, show h ≠ 1 by omega]
      · rw [ite_eq_right (fun e => hkh e.1), ite_eq_right hkh, hold k]
        by_cases hk1 : 1 ≤ k ∧ k < h
        · rw [ite_eq_left hk1, ite_eq_left (by omega)]
          simp [chainNd, show k < h - 1 by omega, show k < h by omega]
        · rw [ite_eq_right hk1, ite_eq_right (by omega)]

/-- The last step: stage `H + 1` to the complete chain. -/
theorem stage_last {P : Params} {s : Core} (S : Stage P (P.H + 1) s) (hH : 1 ≤ P.H) :
    ∃ s', initStep.run s = .ok true s' ∧ Final P s' ∧ s'.ready = s.ready := by
  obtain ⟨pa, hp, hsz, hpa⟩ := S.pr
  have hP := S.P
  rw [ite_eq_right (by omega)] at hp
  refine ⟨_, initStep_last s _ hp (show P.H + 1 ≠ 1 by omega) (by rw [hP]; show P.H < P.H + 1; omega), ?_, rfl⟩
  have hCs : s.C.size = 2 := by rw [S.low.Csize]; rfl
  refine ⟨?_, S.res, rfl, S.nsz (by omega), fun k => ?_, S.cin (by omega), S.lpar (by omega), ?_, fun j => ?_, ?_⟩
  · refine S.low.trans (TopRel.topRelR ?_)
    exact (⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ : TopRel s { s with path := s.path.setX 1 pa, prep := none }).trans
      (TopRel.of_tag _ 1 _)
  · rw [S.nodes (by omega) k, Nat.add_sub_cancel]
    by_cases hk : 1 ≤ k ∧ k ≤ P.H
    · rw [ite_eq_left (by omega), ite_eq_left hk]
    · rw [ite_eq_right (by omega), ite_eq_right hk]
  · show ((s.path.setX 1 pa).getX 1).size = _; rw [getX_setX', ite_eq_left rfl, hsz]
  · show ((s.path.setX 1 pa).getX 1).getX j = _
    rw [getX_setX', ite_eq_left rfl, hpa]
    by_cases hj : 1 ≤ j ∧ j ≤ P.H
    · rw [ite_eq_left (by omega), ite_eq_left hj]
    · rw [ite_eq_right (by omega), ite_eq_right hj]
  · show ((s.C.modify 1 fun C => { C with tag := chainTag P (P.H + 1 - 1) }).getX 1).tag = _
    rw [getX_modify', ite_eq_left ⟨rfl, by omega⟩, Nat.add_sub_cancel]

/-- A building step: stage `h` to stage `h + 1`. -/
theorem stage_next {P : Params} {h : Nat} {s : Core} (S : Stage P h s) (h1 : 1 ≤ h) (hH : h ≤ P.H)
    (hb : 1 ≤ P.beta) : ∃ s', initStep.run s = .ok false s' ∧ Stage P (h + 1) s' ∧ s'.ready = s.ready := by
  by_cases e : h = 1
  · subst e; exact stage_first S hH hb
  · exact stage_mid S (by omega) hH hb

/-- The steps left at stage `h`. -/
def topNu (s : Core) : Nat :=
  match s.prep with
  | some pr => s.P.H + 2 - pr.h
  | none => 0

theorem Stage.nu {P : Params} {h : Nat} {s : Core} (S : Stage P h s) : topNu s = P.H + 2 - h := by
  obtain ⟨pa, hp, -, -⟩ := S.pr
  unfold topNu; rw [hp, S.P]

end OrderMaintenance.Proof.Top
