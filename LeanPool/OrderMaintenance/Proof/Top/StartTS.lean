/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartRun


/-!
# M5: the top structure after a drain starts — derived views

`SDCtx` bundles the situation; `S'` is the state after `startDrain v`, `N = v1`, `N + 1 = v2`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
theorem evenTable_keys (β : Nat) (part : List Nat) : (evenTable β part).map (·.1) = part := by
  unfold evenTable
  rw [List.map_map]
  have : ((fun x : Nat × Nat => x.1) ∘ fun (x : Nat × Nat) => (x.2, (x.1 + 1) * ((1 <<< β) /
    (part.length + 1)))) =
      Prod.snd := by funext x; rfl
  rw [this, List.map_snd_zip (by simp)]

theorem aroundT_keys {tab : List (Nat × Nat)} {e : Nat} (he : e ∈ tab.map (·.1)) (n1 n2 a b : Nat) :
    (aroundT tab e n1 n2 a b).map (·.1) = (tab.map (·.1)).replace1 e [n1, e, n2] := by
  obtain ⟨A, le, Bs, htab, hA⟩ := table_split he
  rw [htab, aroundT_eq hA]
  unfold aroundTab
  simp only [List.map_append, List.map_cons]
  rw [replace1_split _ hA]; simp

/-- The situation when a drain of `v` starts, with the sides `startDrain` computes. -/
structure SDCtx (s : Core) (cl : List Nat) (ord : Nat → List Nat) (dr n0 : Nat → Nat) (j : Job)
  (v : Nat)
    (side : List (Nat × Side)) : Prop where
  pc : j.pc = .walk (some v)
  v0 : v ≠ NIL
  I : InvJ (ts s) cl ord dr n0 (some j)
  lp : (nd (ts s) v).livePar ≠ NIL
  TP : TopParams s.P
  of : (nd (ts s) v).overflowOf = NIL
  W : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2
  hside : sSideO (wiC s v) v = some side
  cl1 : ∀ c ∈ cl, 1 ≤ c
  look : ∀ x, lookup side x =
    if 2 ≤ ht (ts s) v ∧ x ∈ sEntries (wiC s v) v ∧ (nd (ts s) x).draining = true then
      lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (nd (ts
        s) x).t1
    else lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) x

namespace SDCtx

variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  {side : List (Nat × Side)} (C : SDCtx s cl ord dr n0 j v side)
include C

theorem S : Shape (ts s) cl ord := C.I.shape
theorem Ti : Timing (ts s) cl (some j) := C.I.time
theorem H : SDHyps s v side := sr_hyps C.pc C.v0 C.I C.lp C.TP C.of C.W C.look
theorem vl : liveN (ts s) v := (sd_live C.pc C.v0 C.I).1
theorem vy : v = anc (ts s) j.y (ht (ts s) v) := (sd_live C.pc C.v0 C.I).2
theorem h1 : 1 ≤ ht (ts s) v := (sd_ht C.pc C.v0 C.I C.lp).1
theorem hH : ht (ts s) v < s.P.H := (sd_ht C.pc C.v0 C.I C.lp).2
theorem hHt : ht (ts s) v < (ts s).P.H := (sd_ht C.pc C.v0 C.I C.lp).2
theorem up : liveN (ts s) (nd (ts s) v).livePar ∧ ht (ts s) (nd (ts s) v).livePar = ht (ts s) v
  + 1 ∧
    v ∈ (nd (ts s) (nd (ts s) v).livePar).children := sd_up C.pc C.v0 C.I C.lp
theorem ch : sCh1 (wiC s v) v side = (nd (ts s) v).children.take (sK (wiC s v) v) ∧
    sCh2 (wiC s v) v side = (nd (ts s) v).children.drop (sK (wiC s v) v) :=
  sw_ch C.pc C.v0 C.I C.lp C.TP C.of C.W C.look
theorem k : 2 ≤ (nd (ts s) v).children.length ∧ 1 ≤ sK (wiC s v) v ∧
    sK (wiC s v) v < (nd (ts s) v).children.length := sp_k C.pc C.v0 C.I C.lp C.TP C.of C.W

/-- The node count exceeds the chain. -/
theorem NH : s.P.H < s.nodes.size := by
  have := C.S.root.2.1.1.2.1
  change s.P.H < s.nodes.size; exact this

local notation "S'" => ts (sdS (wiC s v) v side)

theorem isN (u : Nat) : Top.isN S' u ↔ Top.isN (ts s) u ∨ u = s.nodes.size ∨ u = s.nodes.size +
  1 := by
  have hNH := C.NH
  unfold Top.isN
  rw [C.H.alive, C.H.size]
  constructor
  · rintro ⟨h0, hs, ha⟩
    by_cases hn : u = s.nodes.size ∨ u = s.nodes.size + 1
    · exact Or.inr hn
    · rw [ite_eq_right hn] at ha
      left; exact ⟨h0, by change u < s.nodes.size; omega, ha⟩
  · rintro (⟨h0, hs, ha⟩ | hn | hn)
    · have hn : ¬(u = s.nodes.size ∨ u = s.nodes.size + 1) := by
        have : u < s.nodes.size := hs; omega
      rw [ite_eq_right hn]; exact ⟨h0, by have : u < s.nodes.size := hs; omega, ha⟩
    · subst hn; rw [ite_eq_left (Or.inl rfl)]; exact ⟨by unfold NIL; omega, by omega, rfl⟩
    · subst hn; rw [ite_eq_left (Or.inr rfl)]; exact ⟨by unfold NIL; omega, by omega, rfl⟩

omit C in
theorem nN (u : Nat) (hu : Top.isN (ts s) u) : u ≠ s.nodes.size ∧ u ≠ s.nodes.size + 1 := by
  have : u < s.nodes.size := hu.2.1; omega

theorem draining' (u : Nat) : (nd S' u).draining = (if u = v then true
    else if u = s.nodes.size ∨ u = s.nodes.size + 1 then false else (nd (ts s) u).draining) :=
      C.H.draining u

theorem liveN (u : Nat) : Top.liveN S' u ↔ (Top.liveN (ts s) u ∧ u ≠ v) ∨ u = s.nodes.size ∨ u =
  s.nodes.size + 1 := by
  have hv := C.H.hv
  unfold Top.liveN
  rw [C.isN, C.draining']
  constructor
  · rintro ⟨hn, hd⟩
    by_cases huv : u = v
    · rw [ite_eq_left huv] at hd; exact absurd hd (by simp)
    · rw [ite_eq_right huv] at hd
      rcases hn with hn | hn | hn
      · have := SDCtx.nN (s := s) u hn
        rw [ite_eq_right (fun h => h.elim this.1 this.2)] at hd
        exact Or.inl ⟨⟨hn, hd⟩, huv⟩
      · exact Or.inr (Or.inl hn)
      · exact Or.inr (Or.inr hn)
  · rintro (⟨⟨hn, hd⟩, huv⟩ | hn | hn)
    · have := SDCtx.nN (s := s) u hn
      refine ⟨Or.inl hn, ?_⟩
      rw [ite_eq_right huv, ite_eq_right (fun h => h.elim this.1 this.2)]; exact hd
    · refine ⟨Or.inr (Or.inl hn), ?_⟩
      rw [ite_eq_right (by omega), ite_eq_left (Or.inl hn)]
    · refine ⟨Or.inr (Or.inr hn), ?_⟩
      rw [ite_eq_right (by omega), ite_eq_left (Or.inr hn)]

theorem ghostN (u : Nat) : Top.ghostN S' u ↔ Top.ghostN (ts s) u ∨ u = v := by
  have hv := C.H.hv
  unfold Top.ghostN
  rw [C.isN, C.draining']
  constructor
  · rintro ⟨hn, hd⟩
    by_cases huv : u = v
    · exact Or.inr huv
    · rw [ite_eq_right huv] at hd
      rcases hn with hn | hn | hn
      · have := SDCtx.nN (s := s) u hn
        rw [ite_eq_right (fun h => h.elim this.1 this.2)] at hd
        exact Or.inl ⟨hn, hd⟩
      · rw [ite_eq_left (Or.inl hn)] at hd; exact absurd hd (by simp)
      · rw [ite_eq_left (Or.inr hn)] at hd; exact absurd hd (by simp)
  · rintro (⟨hn, hd⟩ | huv)
    · have := SDCtx.nN (s := s) u hn
      have huv : u ≠ v := fun e => by rw [e] at hd; rw [C.vl.2] at hd; exact absurd hd (by simp)
      refine ⟨Or.inl hn, ?_⟩
      rw [ite_eq_right huv, ite_eq_right (fun h => h.elim this.1 this.2)]; exact hd
    · subst huv; exact ⟨Or.inl C.vl.1, by rw [ite_eq_left rfl]⟩

theorem ht (u : Nat) : Top.ht S' u = if u = s.nodes.size ∨ u = s.nodes.size + 1 then Top.ht (ts s) v
    else Top.ht (ts s) u := C.H.height u

theorem srcOf (u : Nat) : Top.srcOf S' u = if u = s.nodes.size ∨ u = s.nodes.size + 1 then v
    else Top.srcOf (ts s) u := C.H.overflowOf u

theorem inTab (T : Nat) (hT : T ∈ (nd (ts s) v).inTables) :
    Top.isN (ts s) T ∧ Top.ht (ts s) T = Top.ht (ts s) v + 1 ∧ v ∈ Top.order (ts s) T := by
  have hent : Ent ord (Top.ht (ts s) v) v := (C.S.ordMem _ C.h1 (C.S.htN v C.vl.1).2 v).mpr
    ⟨C.vl.1, rfl⟩
  have hT' : T ∈ tabs (ts s) (Top.ht (ts s) v) v := by
    unfold tabs; rw [ite_eq_right (by have := C.h1; omega)]; exact hT
  exact (C.S.tabsIff _ v T hent).mp hT'

theorem order (X : Nat) : Top.order S' X =
    if X = s.nodes.size then sLeft (wiC s v) v side
    else if X = s.nodes.size + 1 then sRight (wiC s v) v side
    else if X ∈ (nd (ts s) v).inTables then (Top.order (ts s) X).replace1 v [s.nodes.size, v,
      s.nodes.size + 1]
    else Top.order (ts s) X := by
  unfold Top.order Node.order
  rw [C.H.table]
  by_cases h1 : X = s.nodes.size
  · rw [ite_eq_left h1, ite_eq_left h1, evenTable_keys]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : X = s.nodes.size + 1
    · rw [ite_eq_left h2, ite_eq_left h2, evenTable_keys]
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases ht : X ∈ (nd (ts s) v).inTables
      · rw [ite_eq_left ht, ite_eq_left ht, aroundT_keys (C.inTab X ht).2.2]
      · rw [ite_eq_right ht, ite_eq_right ht]


theorem lpr (c : Nat) : Top.lpr S' c = if Top.ht (ts s) v = 1 then
    (if c ∈ (nd (ts s) v).children.drop (sK (wiC s v) v) then s.nodes.size + 1 else if c ∈ (nd
      (ts s) v).children.take (sK (wiC s v) v) then s.nodes.size else Top.lpr (ts s) c)
    else Top.lpr (ts s) c := by
  rw [SDHyps.lpar, C.ch.1, C.ch.2]

omit C in
theorem pp (c j : Nat) : Top.pp S' c j = Top.pp (ts s) c j := by
  unfold Top.pp Top.pth; rw [SDHyps.path (s := s) (v := v) (side := side)]; rfl

theorem livePar (u : Nat) : (nd S' u).livePar =
    if u = v then NIL else if u = s.nodes.size ∨ u = s.nodes.size + 1 then (nd (ts s) v).livePar
    else if Top.ht (ts s) v ≠ 1 ∧ u ∈ (nd (ts s) v).children.drop (sK (wiC s v) v) then
      s.nodes.size + 1
    else if Top.ht (ts s) v ≠ 1 ∧ u ∈ (nd (ts s) v).children.take (sK (wiC s v) v) then s.nodes.size
    else (nd (ts s) u).livePar := by
  rw [C.H.livePar, C.ch.1, C.ch.2]

theorem children (u : Nat) : (nd S' u).children =
    if u = v then [] else if u = s.nodes.size then (nd (ts s) v).children.take (sK (wiC s v) v)
      else if u = s.nodes.size + 1 then (nd (ts s) v).children.drop (sK (wiC s v) v)
    else if u = (nd (ts s) v).livePar then
      (nd (ts s) (nd (ts s) v).livePar).children.replace1 v [s.nodes.size, s.nodes.size + 1]
    else (nd (ts s) u).children := by
  rw [C.H.children, C.ch.1, C.ch.2]

/-- A node the drain does not touch keeps its live parent. -/
theorem livePar_old {u : Nat} (hu : Top.isN (ts s) u) (huv : u ≠ v) (hk : Top.ht (ts s) v ≠ 1 →
  u ∉ (nd (ts s) v).children) :
    (nd S' u).livePar = (nd (ts s) u).livePar := by
  have := SDCtx.nN (s := s) u hu
  rw [C.livePar, ite_eq_right huv, ite_eq_right (fun h => h.elim this.1 this.2)]
  rw [ite_eq_right (fun h => hk h.1 (List.mem_of_mem_drop h.2)),
    ite_eq_right (fun h => hk h.1 (List.mem_of_mem_take h.2))]

theorem kids_split {e : Nat} (he : e ∈ (nd (ts s) v).children) :
    (e ∈ (nd (ts s) v).children.take (sK (wiC s v) v) ∧ e ∉ (nd (ts s) v).children.drop (sK (wiC
      s v) v)) ∨
    (e ∉ (nd (ts s) v).children.take (sK (wiC s v) v) ∧ e ∈ (nd (ts s) v).children.drop (sK (wiC
      s v) v)) := by
  obtain ⟨hnd, -, -⟩ := C.S.kids v C.vl
  have hsp : (nd (ts s) v).children = (nd (ts s) v).children.take (sK (wiC s v) v) ++
      (nd (ts s) v).children.drop (sK (wiC s v) v) := (List.take_append_drop _ _).symm
  have hdis := (List.nodup_append.mp (hsp ▸ hnd)).2.2
  have hm := he; rw [hsp, List.mem_append] at hm
  rcases hm with h | h
  · exact Or.inl ⟨h, fun h' => hdis e h e h' rfl⟩
  · exact Or.inr ⟨fun h' => hdis e h' e h rfl, h⟩

/-- **The live ancestors after the drain starts.** -/
theorem anc {c : Nat} (hc : c ∈ cl) : ∀ i, i ≤ s.P.H → Top.anc S' c i =
    if i = Top.ht (ts s) v ∧ Top.anc (ts s) c (Top.ht (ts s) v) = v then
      (if Top.anc (ts s) c (Top.ht (ts s) v - 1) ∈ (nd (ts s) v).children.take (sK (wiC s v) v)
        then s.nodes.size else s.nodes.size + 1)
    else Top.anc (ts s) c i
  | 0, _ => by
    rw [ite_eq_right (fun h => by have := C.h1; omega)]; rfl
  | 1, hi => by
    change Top.lpr S' c = _
    rw [C.lpr]
    have e1 : Top.anc (ts s) c 1 = Top.lpr (ts s) c := rfl
    by_cases h1 : Top.ht (ts s) v = 1
    · rw [ite_eq_left h1]
      have hiff : Top.lpr (ts s) c = v ↔ c ∈ (nd (ts s) v).children := by
        rw [C.S.mem_children C.vl, ite_eq_left h1, h1, Nat.sub_self, par_live (Or.inl rfl),
          ite_eq_left rfl]
        exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
      have e0 : Top.anc (ts s) c (Top.ht (ts s) v - 1) = c := by rw [h1]; rfl
      have e2 : Top.anc (ts s) c (Top.ht (ts s) v) = Top.lpr (ts s) c := by rw [h1]; rfl
      rw [e0, e2]
      by_cases hl : Top.lpr (ts s) c = v
      · rw [ite_eq_left (show 1 = Top.ht (ts s) v ∧ Top.lpr (ts s) c = v from ⟨h1.symm, hl⟩)]
        rcases C.kids_split (hiff.mp hl) with ⟨a, b⟩ | ⟨a, b⟩
        · rw [ite_eq_right b, ite_eq_left a, ite_eq_left a]
        · rw [ite_eq_left b, ite_eq_right a]
      · rw [ite_eq_right (show ¬(1 = Top.ht (ts s) v ∧ Top.lpr (ts s) c = v) from fun h => hl h.2)]
        have hk : c ∉ (nd (ts s) v).children := fun h => hl (hiff.mpr h)
        rw [ite_eq_right (fun h => hk (List.mem_of_mem_drop h)),
          ite_eq_right (fun h => hk (List.mem_of_mem_take h)), e1]
    · rw [ite_eq_right h1,
      ite_eq_right (show ¬(1 = Top.ht (ts s) v ∧ _) from fun h => h1 h.1.symm)]; rfl
  | i + 2, hi => by
    change (nd S' (Top.anc S' c (i + 1))).livePar = _
    rw [anc hc (i + 1) (by omega)]
    have hP : (ts s).P = s.P := rfl
    obtain ⟨hal, hah⟩ := C.S.anc_live hc (i + 1) (by omega) (by rw [hP]; omega)
    have hnN : (nd S' s.nodes.size).livePar = (nd (ts s) v).livePar := by
      rw [C.livePar, ite_eq_right (by have := C.H.hv; omega), ite_eq_left (Or.inl rfl)]
    have hnN1 : (nd S' (s.nodes.size + 1)).livePar = (nd (ts s) v).livePar := by
      rw [C.livePar, ite_eq_right (by have := C.H.hv; omega), ite_eq_left (Or.inr rfl)]
    by_cases hb : i + 1 = Top.ht (ts s) v ∧ Top.anc (ts s) c (Top.ht (ts s) v) = v
    · rw [ite_eq_left hb,
      ite_eq_right (show ¬(i + 2 = Top.ht (ts s) v ∧ Top.anc (ts s) c (Top.ht (ts s) v) = v) from
        fun h => by have := h.1; have := hb.1; omega)]
      have hL : (nd (ts s) v).livePar = Top.anc (ts s) c (i + 2) := by
        rw [← hb.2, ← anc_succ c _ C.h1, show Top.ht (ts s) v + 1 = i + 2 by omega]
      split
      · rw [hnN, hL]
      · rw [hnN1, hL]
    · rw [ite_eq_right hb]
      have hav : Top.anc (ts s) c (i + 1) ≠ v := by
        intro e; apply hb; refine ⟨?_, ?_⟩
        · rw [← e, hah]
        · rw [show Top.ht (ts s) v = i + 1 by rw [← e, hah], e]
      by_cases hkk : Top.ht (ts s) v ≠ 1 ∧ Top.anc (ts s) c (i + 1) ∈ (nd (ts s) v).children
      · -- the ancestor is a child of `v`
        have h1v := C.h1
        have hk1 := hkk.1
        have hpar : (nd (ts s) (Top.anc (ts s) c (i + 1))).livePar = v := by
          obtain ⟨-, hp⟩ := (C.S.mem_children C.vl).mp hkk.2
          rw [par_live (Or.inr hal), ite_eq_right (by omega)] at hp
          exact hp
        have hih : i + 2 = Top.ht (ts s) v := by
          have := ((C.S.mem_children C.vl).mp hkk.2).1; rw [ite_eq_right hkk.1] at this; omega
        have hav2 : Top.anc (ts s) c (Top.ht (ts s) v) = v := by
          rw [← hih, anc_succ c _ (by omega), hpar]
        rw [ite_eq_left ⟨hih, hav2⟩, show Top.ht (ts s) v - 1 = i + 1 by omega]
        rw [C.livePar, ite_eq_right hav,
          ite_eq_right (fun h => h.elim (SDCtx.nN (s := s) _ hal.1).1 (SDCtx.nN (s := s) _
            hal.1).2)]
        rcases C.kids_split hkk.2 with ⟨a, b⟩ | ⟨a, b⟩
        · rw [ite_eq_right (fun h => b h.2), ite_eq_left ⟨hkk.1, a⟩, ite_eq_left a]
        · rw [ite_eq_left ⟨hkk.1, b⟩, ite_eq_right a]
      · rw [C.livePar_old hal.1 hav (fun h1 h => hkk ⟨h1, h⟩), ← anc_succ c _ (by omega)]
        rw [ite_eq_right]
        rintro ⟨hih, hav2⟩
        apply hkk
        have h1' : Top.ht (ts s) v ≠ 1 := by omega
        refine ⟨h1', (C.S.mem_children C.vl).mpr ⟨by rw [ite_eq_right h1']; exact ⟨hal, by
          omega⟩, ?_⟩⟩
        rw [par_live (Or.inr hal), ite_eq_right (by omega), ← anc_succ c _ (by omega), hih, hav2]

/-- **True weights of untouched nodes do not change.** -/
theorem tw_old {u : Nat} (hu : Top.isN (ts s) u) (huv : u ≠ v) : tw S' cl u = tw (ts s) cl u := by
  have hn := SDCtx.nN (s := s) u hu
  obtain ⟨-, hH⟩ := C.S.htN u hu
  unfold tw
  rw [C.ht, ite_eq_right (fun h => h.elim hn.1 hn.2)]
  congr 1
  apply List.filter_congr
  intro c hc
  rw [C.anc hc _ hH]
  split
  · next hb =>
    rw [hb.1, hb.2]
    have : (if Top.anc (ts s) c (Top.ht (ts s) v - 1) ∈ (nd (ts s) v).children.take (sK (wiC s v) v)
        then s.nodes.size else s.nodes.size + 1) ≠ u := by split <;> omega
    simp [this, Ne.symm huv]
  · rfl

/-- The drained node serves no chunk directly any more. -/
theorem tw_v : tw S' cl v = 0 := by
  have hn := SDCtx.nN (s := s) v C.vl.1
  unfold tw
  rw [C.ht, ite_eq_right (fun h => h.elim hn.1 hn.2)]
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro c hc
  rw [C.anc hc _ (by have := C.hH; omega)]
  split
  · split <;> simp <;> omega
  · next hb => simp only [decide_eq_true_eq]; exact fun h => hb ⟨rfl, h⟩

end SDCtx

end OrderMaintenance.Proof.Top
