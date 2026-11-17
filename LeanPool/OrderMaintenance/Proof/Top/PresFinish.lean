/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.RunFinish
public import LeanPool.OrderMaintenance.Proof.Top.PresDrain


/-!
# M5: the end of a drain keeps the invariant

A sweep call on a ghost `v` with an empty range removes `v` from every table, releases its targets
and marks it dead. The order loses `v`; nothing referred to it any more, since no path passes
through it. The released targets weigh at most `W_h` (Lemma T3, under `2 + 2K_h ≤ λ_h`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Removing an entry from a table -/

theorem assocErase_keys {β : Type} (t : List (Nat × β)) (v : Nat) (h : (t.map (·.1)).Nodup) :
    (assocErase t v).map (·.1) = (t.map (·.1)).erase v := by
  unfold assocErase
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, b⟩ := p
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [List.filter_cons, List.map_cons]
    by_cases hk : k = v
    · subst hk
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, List.erase_cons_head]
      have : (t.filter (fun x => x.1 != k)) = t := List.filter_eq_self.mpr fun q hq => by
        simp only [bne_iff_ne, ne_eq]; intro e
        exact h.1 (e ▸ List.mem_map_of_mem (f := fun x => x.1) hq)
      rw [this]
    · simp only [show (k != v) = true by simpa using hk, ite_true, List.map_cons]
      rw [List.erase_cons_tail (by simpa using hk), ih h.2]

theorem lookup_assocErase {β : Type} (t : List (Nat × β)) (v e : Nat) (he : e ≠ v) :
    lookup (assocErase t v) e = lookup t e := by
  unfold assocErase lookup
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, b⟩ := p
    simp only [List.filter_cons, List.find?_cons]
    by_cases hk : k = v
    · subst hk
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
      rw [ih, show (k == e) = false by simpa using Ne.symm he]
    · simp only [show (k != v) = true by simpa using hk, ite_true, List.find?_cons]
      split <;> simp_all

theorem gapsGe_sublist {β B : Nat} {ls ls' : List Nat} (h : GapsGe β B ls) (hs : ls'.Sublist ls) :
    GapsGe β B ls' := by
  unfold GapsGe at *
  have htr : IsTrans Nat (fun a b => a + B ≤ b) := ⟨fun a b c h1 h2 => by omega⟩
  rw [List.isChain_iff_pairwise] at *
  refine List.Pairwise.sublist ?_ h
  exact List.Sublist.cons_cons 0 (List.Sublist.append (hs.map _) (List.Sublist.refl _))

theorem gapsGe_assocErase {β B : Nat} {t : List (Nat × Nat)} (v : Nat)
    (h : GapsGe β B (t.map (·.2))) : GapsGe β B ((assocErase t v).map (·.2)) :=
  gapsGe_sublist h ((List.filter_sublist).map _)

/-! ### The views after the drain ends -/

/-- What changes when ghost `v` ends: `v` dies and leaves every table; its targets are released. -/
structure FinFrame (s s' : TS) (v : Nat) : Prop where
  P : s'.P = s.P
  size : s'.nodes.size = s.nodes.size
  path : s'.path = s.path
  lpar : s'.lpar = s.lpar
  tag : s'.tag = s.tag
  node : ∀ u, nd s' u = { nd s u with
    alive := if u = v then false else (nd s u).alive,
    table := if u ∈ (nd s v).inTables then assocErase (nd s u).table v else (nd s u).table,
    side := if u ∈ (nd s v).inTables then assocErase (nd s u).side v else (nd s u).side,
    inTables := if u = v then [] else if u ∈ order s v ∧ ht s v - 1 ≠ 0 then (nd s
      u).inTables.erase v
      else (nd s u).inTables,
    overflowOf := if (u = (nd s v).t1 ∨ u = (nd s v).t2) ∧ (nd s u).overflowOf = v then NIL
      else (nd s u).overflowOf }
  cin : ∀ e, cinT s' e = if ht s v - 1 = 0 ∧ e ∈ order s v then (cinT s e).erase v else cinT s e

theorem foldl_dropEntryS_rest (v : Nat) (l : List Nat) (s : Core) :
    (l.foldl (dropEntryS v) s).cin = s.cin ∧ (l.foldl (dropEntryS v) s).path = s.path ∧
      (l.foldl (dropEntryS v) s).lpar = s.lpar ∧ (l.foldl (dropEntryS v) s).P = s.P ∧
      (l.foldl (dropEntryS v) s).C = s.C ∧ (l.foldl (dropEntryS v) s).resJob = s.resJob ∧
      (l.foldl (dropEntryS v) s).nodes.size = s.nodes.size := by
  induction l generalizing s with
  | nil => simp
  | cons x t ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (dropEntryS v s x)
    simp only [List.foldl_cons]
    exact ⟨h1, h2, h3, h4, h5, h6, by rw [h7]; simp [dropEntryS]⟩

theorem fdS_rest (v : Nat) (s : Core) (hno : (s.nodes.getX v).order.Nodup) :
    (∀ e, (fdS v s).cin.getX e =
      if e ∈ (s.nodes.getX v).order ∧ (s.nodes.getX v).height - 1 = 0 then (s.cin.getX e).erase v
      else s.cin.getX e) ∧
    (fdS v s).path = s.path ∧ (fdS v s).lpar = s.lpar ∧ (fdS v s).P = s.P ∧ (fdS v s).C = s.C ∧
    (fdS v s).resJob = s.resJob ∧ (fdS v s).nodes.size = s.nodes.size := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := foldl_dropTableS v ((s.nodes.getX v).height - 1) _
    hno s
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := foldl_dropEntryS_rest v (s.nodes.getX v).inTables (fd1 v s)
  have r1 := releaseS_rest v (fd2 v s) (s.nodes.getX v).t1
  have r2 := releaseS_rest v (releaseS v (fd2 v s) (s.nodes.getX v).t1) (s.nodes.getX v).t2
  have hf2 : (fd2 v s).cin = (fd1 v s).cin ∧ (fd2 v s).path = s.path ∧ (fd2 v s).lpar = s.lpar ∧
      (fd2 v s).P = s.P ∧ (fd2 v s).C = s.C ∧ (fd2 v s).resJob = s.resJob ∧
      (fd2 v s).nodes.size = s.nodes.size := by
    unfold fd2; exact ⟨e1, e2.trans d4, e3.trans d5, e4.trans d6, e5.trans d7, e6.trans d8,
      e7.trans d2⟩
  have hf4 : (fd4 v s).cin = (fd1 v s).cin ∧ (fd4 v s).path = s.path ∧ (fd4 v s).lpar = s.lpar ∧
      (fd4 v s).P = s.P ∧ (fd4 v s).C = s.C ∧ (fd4 v s).resJob = s.resJob ∧
      (fd4 v s).nodes.size = s.nodes.size := by
    unfold fd4
    exact ⟨r2.1.trans (r1.1.trans hf2.1), r2.2.1.trans (r1.2.1.trans hf2.2.1),
      r2.2.2.1.trans (r1.2.2.1.trans hf2.2.2.1), r2.2.2.2.1.trans (r1.2.2.2.1.trans hf2.2.2.2.1),
      r2.2.2.2.2.1.trans (r1.2.2.2.2.1.trans hf2.2.2.2.2.1),
      r2.2.2.2.2.2.trans (r1.2.2.2.2.2.trans hf2.2.2.2.2.2.1),
      by rw [releaseS_size, releaseS_size]; exact hf2.2.2.2.2.2.2⟩
  have hc : (fdS v s).cin = (fd4 v s).cin := by simp only [fdS]
  refine ⟨fun e => ?_, by simp only [fdS]; exact hf4.2.1, by simp only [fdS]; exact hf4.2.2.1,
    by simp only [fdS]; exact hf4.2.2.2.1, by simp only [fdS]; exact hf4.2.2.2.2.1,
    by simp only [fdS]; exact hf4.2.2.2.2.2.1, by
      simp only [fdS]
      rw [Array.size_modify']
      exact hf4.2.2.2.2.2.2⟩
  rw [hc, hf4.1]
  unfold fd1; rw [d3 e]

attribute [local irreducible] fdS

/-! ### Released targets fit (Lemma T3) -/

/-- A drain has had at most `K_h` funding jobs. -/
theorem Timing.fund_le {s : TS} {cl : List Nat} {oj : Option Job} (Ti : Timing s cl oj)
    (hTP : TopParams s.P) {v : Nat} (hg : ghostN s v) :
    fundOf s cl v ≤ Kd s.P (ht s v) := by
  have h1 := Ti.wC' v hg
  have h2 := (Ti.wB v hg).2
  have hs := hTP.s3
  unfold Kd
  have : fundOf s cl v - 1 ≤ (Wd s.P (ht s v) + 2) / (s.P.s - 2) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have : (s.P.s - 2) * (fundOf s cl v - 1) ≤ (nd s v).weight := by
      refine le_trans (Nat.mul_le_mul_left _ ?_) h1
      split <;> omega
    rw [Nat.mul_comm]; omega
  omega

/-- **A released target fits under the drain threshold.** -/
theorem Timing.release {s : TS} {cl : List Nat} {ord : Nat → List Nat} {oj : Option Job}
    (S : Shape s cl ord) (Ti : Timing s cl oj) (hTP : TopParams s.P) {v t : Nat} (hg : ghostN s v)
    (htv : t = (nd s v).t1 ∨ t = (nd s v).t2) (htp : t ∉ pend s oj) :
    (nd s t).weight ≤ Wd s.P (ht s v) := by
  obtain ⟨hl1, hl2, hh1, hh2, hs1, hs2, -⟩ := S.ghost v hg
  have h12 : (nd s v).t1 ≠ (nd s v).t2 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinf⟩ := S.ghost v hg
    exact ((before_of_infix2 (infix3_left hinf)).trans (before_of_infix2 (infix3_right hinf))
      (S.ordNodup _)).ne (S.ordNodup _)
  have hv0 : v ≠ NIL := hg.1.1
  have hb1 := Ti.big _ hl1 (by rw [hs1]; exact hv0)
  have hb2 := Ti.big _ hl2 (by rw [hs2]; exact hv0)
  have hd1 := Ti.wD _ hl1 hb1
  have hd2 := Ti.wD _ hl2 hb2
  rw [hh1] at hd1; rw [hh2] at hd2
  have hf := Ti.fund_le hTP hg
  have hF := Ti.wF v hg
  have hB := (Ti.wB v hg).2
  have hlk := hTP.lamK (ht s v) (S.htN v hg.1).1
  have hew : ew s cl v = tw s cl (nd s v).t1 + tw s cl (nd s v).t2 := by
    unfold ew; rw [ite_eq_left hg.2]
  unfold fundOf at hf
  have hlive : liveN s t := by rcases htv with e | e <;> rw [e] <;> assumption
  have hw := Ti.wts t hlive
  rw [ite_eq_right htp, Nat.add_zero] at hw
  rw [hw]
  rcases htv with e | e <;> subst e <;> omega

/-- The order after ghost `v` (of height `h`) ends. -/
def ordE (ord : Nat → List Nat) (h v : Nat) : Nat → List Nat :=
  fun k => if k = h then (ord k).erase v else ord k

/-! ### Consequences of the frame -/

namespace FinFrame
variable {s s' : TS} {v : Nat} (F : FinFrame s s' v)
include F

theorem height (u : Nat) : (nd s' u).height = (nd s u).height := by rw [F.node u]
theorem livePar (u : Nat) : (nd s' u).livePar = (nd s u).livePar := by rw [F.node u]
theorem children (u : Nat) : (nd s' u).children = (nd s u).children := by rw [F.node u]
theorem weight (u : Nat) : (nd s' u).weight = (nd s u).weight := by rw [F.node u]
theorem first (u : Nat) : (nd s' u).first = (nd s u).first := by rw [F.node u]
theorem last (u : Nat) : (nd s' u).last = (nd s u).last := by rw [F.node u]
theorem draining (u : Nat) : (nd s' u).draining = (nd s u).draining := by rw [F.node u]
theorem t1 (u : Nat) : (nd s' u).t1 = (nd s u).t1 := by rw [F.node u]
theorem t2 (u : Nat) : (nd s' u).t2 = (nd s u).t2 := by rw [F.node u]
theorem alive (u : Nat) : (nd s' u).alive = if u = v then false else (nd s u).alive := by
  rw [F.node u]
theorem table (u : Nat) : (nd s' u).table =
    if u ∈ (nd s v).inTables then assocErase (nd s u).table v else (nd s u).table := by
      rw [F.node u]
theorem side (u : Nat) : (nd s' u).side =
    if u ∈ (nd s v).inTables then assocErase (nd s u).side v else (nd s u).side := by rw [F.node u]
theorem inTables (u : Nat) : (nd s' u).inTables =
    if u = v then [] else if u ∈ order s v ∧ ht s v - 1 ≠ 0 then (nd s u).inTables.erase v
    else (nd s u).inTables := by rw [F.node u]
theorem overflowOf (u : Nat) : (nd s' u).overflowOf =
    if (u = (nd s v).t1 ∨ u = (nd s v).t2) ∧ (nd s u).overflowOf = v then NIL
    else (nd s u).overflowOf := by rw [F.node u]

theorem ht (u : Nat) : Top.ht s' u = Top.ht s u := F.height u
theorem isN (u : Nat) : Top.isN s' u ↔ Top.isN s u ∧ u ≠ v := by
  unfold Top.isN; rw [F.size, F.alive]
  by_cases h : u = v <;> simp [h]
theorem liveN (u : Nat) : Top.liveN s' u ↔ Top.liveN s u ∧ u ≠ v := by
  unfold Top.liveN; rw [F.isN, F.draining]; tauto
theorem ghostN (u : Nat) : Top.ghostN s' u ↔ Top.ghostN s u ∧ u ≠ v := by
  unfold Top.ghostN; rw [F.isN, F.draining]; tauto
theorem lpr (c : Nat) : Top.lpr s' c = Top.lpr s c := by unfold Top.lpr; rw [F.lpar]
theorem pp (c j : Nat) : Top.pp s' c j = Top.pp s c j := by unfold Top.pp Top.pth; rw [F.path]
theorem par (k e : Nat) : Top.par s' k e = Top.par s k e := by
  unfold Top.par; rw [F.lpr, F.draining, F.t1, F.livePar, F.livePar]
theorem anc (c : Nat) : ∀ k, Top.anc s' c k = Top.anc s c k
  | 0 => rfl
  | 1 => F.lpr c
  | k + 2 => by
    change (nd s' (Top.anc s' c (k + 1))).livePar = (nd s (Top.anc s c (k + 1))).livePar
    rw [anc c (k + 1), F.livePar]
theorem tw (cl : List Nat) (u : Nat) : Top.tw s' cl u = Top.tw s cl u := by
  unfold Top.tw; simp only [F.ht, F.anc]
theorem rng (cl : List Nat) (u : Nat) : Top.rng s' cl u = Top.rng s cl u := by
  unfold Top.rng; simp only [F.ht, F.pp]
theorem srcOf (u : Nat) : Top.srcOf s' u =
    if (u = (nd s v).t1 ∨ u = (nd s v).t2) ∧ Top.srcOf s u = v then NIL else Top.srcOf s u :=
  F.overflowOf u
theorem upChain : ∀ f w, Top.upChain s' f w = Top.upChain s f w
  | 0, _ => rfl
  | f + 1, w => by unfold Top.upChain; rw [F.livePar, upChain f]

end FinFrame

section fin
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord) {v : Nat}
  (hg : ghostN (ts s) v)
include S hg

theorem Shape.fin_facts :
    v < s.nodes.size ∧ (nd (ts s) v).order.Nodup ∧ (nd (ts s) v).inTables.Nodup ∧ ((nd (ts s)
      v).height - 1 ≠ 0 → v ∉ (nd (ts s) v).order) ∧
      v ∉ (nd (ts s) v).inTables ∧ v ≠ (nd (ts s) v).t1 ∧ v ≠ (nd (ts s) v).t2 ∧ (nd (ts s)
        v).t1 ≠ (nd (ts s) v).t2 ∧ ((nd (ts s) v).height - 1 ≠ 0 → (nd (ts s) v).t1 ∉ (nd (ts s)
          v).order) ∧
      ((nd (ts s) v).height - 1 ≠ 0 → (nd (ts s) v).t2 ∉ (nd (ts s) v).order) ∧ (nd (ts s) v).t1
        ∉ (nd (ts s) v).inTables ∧ (nd (ts s) v).t2 ∉ (nd (ts s) v).inTables ∧
      (∀ u, u ∈ (nd (ts s) v).order → (nd (ts s) v).height - 1 ≠ 0 → u ∉ (nd (ts s) v).inTables) ∧
      (∀ u ∈ (nd (ts s) v).inTables, isN (ts s) u ∧ ht (ts s) u = ht (ts s) v + 1) ∧
      (∀ u ∈ (nd (ts s) v).order, (nd (ts s) v).height - 1 ≠ 0 → isN (ts s) u ∧ ht (ts s) u = ht
        (ts s) v - 1) := by
  obtain ⟨hl1, hl2, hh1, hh2, -, -, -, -, -, hlt, -⟩ := S.ghost v hg
  obtain ⟨hv1, hvH⟩ := S.htN v hg.1
  have hvent : Ent ord (ht (ts s) v) v := (S.ordMem _ hv1 hvH v).mpr ⟨hg.1, rfl⟩
  have htabs : tabs (ts s) (ht (ts s) v) v = (nd (ts s) v).inTables := by
    unfold tabs; rw [ite_eq_right (by omega)]
  have hin : ∀ u ∈ (nd (ts s) v).inTables, isN (ts s) u ∧ ht (ts s) u = ht (ts s) v + 1 := fun u
    hu => by
    rw [← htabs] at hu; obtain ⟨h1, h2, -⟩ := (S.tabsIff _ v u hvent).mp hu; exact ⟨h1, h2⟩
  have hent : ∀ u ∈ (nd (ts s) v).order, (nd (ts s) v).height - 1 ≠ 0 → isN (ts s) u ∧ ht (ts s)
    u = ht (ts s) v - 1 :=
    fun u hu h0 => by
      have := S.tabEnt v hg.1 u hu
      have h0' : ht (ts s) v - 1 ≠ 0 := h0
      exact (S.ordMem _ (by omega) (by omega) u).mp this
  have h12 := S.t1_ne_t2 hg
  refine ⟨hg.1.2.1, S.order_nodup hg.1, by rw [← htabs]; exact S.tabsNodup _ v hvent,
    fun h0 hm => ?_, fun hm => ?_, fun e => ?_, fun e => ?_, h12, fun h0 hm => ?_, fun h0 hm => ?_,
    fun hm => ?_, fun hm => ?_, fun u hu h0 hm => ?_, hin, hent⟩
  · have := (hent v hm h0).2; simp only [ht] at this hv1; omega
  · have := (hin v hm).2; omega
  · rw [e] at hg; exact absurd hg.2 (by rw [hl1.2]; simp)
  · rw [e] at hg; exact absurd hg.2 (by rw [hl2.2]; simp)
  · have := (hent _ hm h0).2; rw [hh1] at this; simp only [ht] at this hv1; omega
  · have := (hent _ hm h0).2; rw [hh2] at this; simp only [ht] at this hv1; omega
  · have := (hin _ hm).2; rw [hh1] at this; omega
  · have := (hin _ hm).2; rw [hh2] at this; omega
  · have h1 := (hin u hm).2; have h2 := (hent u hu h0).2; omega

/-- **The views after the drain ends.** -/
theorem Shape.fin_frame : FinFrame (ts s) (ts (fdS v s)) v := by
  obtain ⟨hv, hno, hni, hvo, hvi, h1, h2, h12, ho1, ho2, hi1, hi2, hoi, hin, hent⟩ := S.fin_facts hg
  obtain ⟨hc, hp, hl, hP, hC, hr, hsz⟩ := fdS_rest v s hno
  refine ⟨hP, hsz, hp, hl, by unfold ts; simp only [hC], fun u => ?_, fun e => ?_⟩
  · change (fdS v s).nodes.getX u = _
    rw [fdS_getX v s hv hno hni hvo hvi h1 h2 h12 ho1 ho2 hi1 hi2 hoi u]
    by_cases huv : u = v
    · subst huv
      have : ¬ (u = (s.nodes.getX u).t1 ∨ u = (s.nodes.getX u).t2) := by
        rintro (e | e)
        · exact h1 e
        · exact h2 e
      have hvi' : u ∉ (s.nodes.getX u).inTables := hvi
      simp [hvi', this, nd, ts]
    · rw [ite_eq_right huv]
      by_cases hu1 : u ∈ (s.nodes.getX v).order ∧ (s.nodes.getX v).height - 1 ≠ 0
      · have hus : u < s.nodes.size := (hent u hu1.1 hu1.2).1.2.1
        have hi : u ∉ (s.nodes.getX v).inTables := hoi u hu1.1 hu1.2
        have hn1 : u ≠ (s.nodes.getX v).t1 := fun e => ho1 hu1.2 (e ▸ hu1.1)
        have hn2 : u ≠ (s.nodes.getX v).t2 := fun e => ho2 hu1.2 (e ▸ hu1.1)
        rw [ite_eq_left ⟨hu1.1, hu1.2, hus⟩]
        simp only [order, ht, nd, ts] at hu1 ⊢
        simp [huv, hi, hn1, hn2, hu1]
      · rw [ite_eq_right (fun h => hu1 ⟨h.1, h.2.1⟩)]
        by_cases hu2 : u ∈ (s.nodes.getX v).inTables
        · have hus : u < s.nodes.size := (hin u hu2).1.2.1
          have hn1 : u ≠ (s.nodes.getX v).t1 := fun e => hi1 (e ▸ hu2)
          have hn2 : u ≠ (s.nodes.getX v).t2 := fun e => hi2 (e ▸ hu2)
          rw [ite_eq_left ⟨hu2, hus⟩]
          simp only [order, ht, nd, ts] at hu1 ⊢
          simp [huv, hu2, hn1, hn2, hu1]
        · rw [ite_eq_right (fun h => hu2 h.1)]
          simp only [order, ht, nd, ts] at hu1 ⊢
          by_cases hu3 : (u = (s.nodes.getX v).t1 ∨ u = (s.nodes.getX v).t2) ∧
              (s.nodes.getX u).overflowOf = v
          · have hus : u < s.nodes.size := by
              obtain ⟨hl1, hl2, -⟩ := S.ghost v hg
              rcases hu3.1 with e | e <;> rw [e] <;> [exact hl1.1.2.1; exact hl2.1.2.1]
            rw [ite_eq_left ⟨hu3.1, hu3.2, hus⟩]
            simp [huv, hu2, hu1, hu3]
          · rw [ite_eq_right (fun h => hu3 ⟨h.1, h.2.1⟩)]
            simp [huv, hu2, hu1, hu3]
  · change (fdS v s).cin.getX e = _
    rw [hc e]
    unfold cinT order ht nd ts
    simp only [and_comm]

/-! ### Tables after the drain ends -/

variable {s' : TS} (F : FinFrame (ts s) s' v) (hemp : rng (ts s) cl v = [])
include F

theorem Shape.fin_order (X : Nat) : order s' X =
    if X ∈ (nd (ts s) v).inTables then (order (ts s) X).erase v else order (ts s) X := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hin, -⟩ := S.fin_facts hg
  unfold order Node.order
  rw [F.table]
  split
  · next h => rw [assocErase_keys _ _ (S.order_nodup (hin X h).1)]
  · rfl

omit hg in
theorem Shape.fin_labs (X : Nat) (hX : isN (ts s) X) :
    GapsGe s'.P.beta 1 (labs s' X) := by
  unfold labs; rw [F.table, F.P]
  split
  · exact gapsGe_assocErase v (S.labsOk X hX)
  · exact S.labsOk X hX

omit S hg in
theorem Shape.fin_lab (X e : Nat) (he : X ∈ (nd (ts s) v).inTables → e ≠ v) :
    (nd s' X).lab? e = (nd (ts s) X).lab? e := by
  unfold Node.lab?; rw [F.table]; split
  · next h => exact lookup_assocErase _ _ _ (he h)
  · rfl

omit S hg in
theorem Shape.fin_sideL (X e : Nat) (he : X ∈ (nd (ts s) v).inTables → e ≠ v) :
    lookup (nd s' X).side e = lookup (nd (ts s) X).side e := by
  rw [F.side]; split
  · next h => exact lookup_assocErase _ _ _ (he h)
  · rfl

theorem Shape.fin_tabs (k e : Nat) (he : Ent ord k e) (hev : k = ht (ts s) v → e ≠ v) :
    tabs s' k e = if e ∈ order (ts s) v ∧ k = ht (ts s) v - 1 then (tabs (ts s) k e).erase v
      else tabs (ts s) k e := by
  obtain ⟨hv, hno, hni, hvo, hvi, h1, h2, h12, ho1, ho2, hi1, hi2, hoi, hin, hent⟩ := S.fin_facts hg
  obtain ⟨hv1, hvH⟩ := S.htN v hg.1
  unfold tabs
  by_cases hk : k = 0
  · subst hk
    simp only [ite_true]
    rw [F.cin]
    by_cases hm : e ∈ order (ts s) v ∧ 0 = ht (ts s) v - 1
    · rw [ite_eq_left ⟨hm.2.symm, hm.1⟩, ite_eq_left hm]
    · rw [ite_eq_right (fun h => hm ⟨h.2, h.1.symm⟩), ite_eq_right hm]
  · simp only [ite_eq_right hk]
    rw [F.inTables]
    have hkH : k ≤ (ts s).P.H := by
      by_contra hc
      have he' : e ∈ ord k := he
      rw [S.ordHigh k (by omega)] at he'; simp at he'
    obtain ⟨heN, heh⟩ := (S.ordMem k (by omega) hkH e).mp he
    have hev' : e ≠ v := fun e' => hev (by rw [← heh, e']) e'
    rw [ite_eq_right hev']
    by_cases hm : e ∈ order (ts s) v ∧ k = ht (ts s) v - 1
    · rw [ite_eq_left hm, ite_eq_left ⟨hm.1, by rw [← hm.2]; exact hk⟩]
    · rw [ite_eq_right hm, ite_eq_right]
      rintro ⟨hm1, hm2⟩
      exact hm ⟨hm1, by rw [← heh]; exact (hent e hm1 hm2).2⟩

omit hg F in
theorem Shape.fin_ent {k e : Nat} :
    Ent (ordE ord (ht (ts s) v) v) k e ↔ Ent ord k e ∧ (k = ht (ts s) v → e ≠ v) := by
  unfold Ent ordE
  split
  · next hk =>
    rw [(S.ordNodup k).mem_erase_iff]
    exact ⟨fun h => ⟨h.2, fun _ => h.1⟩, fun h => ⟨h.2 hk, h.1⟩⟩
  · next hk => exact ⟨fun h => ⟨h, fun e => absurd e hk⟩, fun h => h.1⟩

omit hg F in
theorem Shape.fin_before {k a b : Nat} (hab : k = ht (ts s) v → a ≠ v ∧ b ≠ v) :
    Before (ordE ord (ht (ts s) v) v k) a b ↔ Before (ord k) a b := by
  unfold ordE
  split
  · next hk => exact before_erase (S.ordNodup k) (hab hk).1 (hab hk).2
  · exact Iff.rfl

omit S hg F in
theorem Shape.fin_ppv (hemp : rng (ts s) cl v = []) {c : Nat} (hc : c ∈ cl) :
    pp (ts s) c (ht (ts s) v) ≠ v := by
  intro e
  have : c ∈ rng (ts s) cl v := by
    simp only [rng, List.mem_filter, decide_eq_true_eq]; exact ⟨hc, e⟩
  rw [hemp] at this; simp at this

/-- **The tag part of the invariant after the drain ends.** -/
theorem Shape.fin_shapeT (hemp : rng (ts s) cl v = []) :
    ShapeT s' cl (ordE ord (ht (ts s) v) v) := by
  obtain ⟨hv, hno, hni, hvo, hvi, h1, h2, h12, ho1, ho2, hi1, hi2, hoi, hin, hent⟩ := S.fin_facts hg
  obtain ⟨hv1, hvH⟩ := S.htN v hg.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hlt, -⟩ := S.ghost v hg
  have hP := F.P
  have hppv : ∀ {c : Nat}, c ∈ cl → pp (ts s) c (ht (ts s) v) ≠ v := fun hc => Shape.fin_ppv hemp hc
  refine ⟨by rw [hP]; exact S.H3, ?_, fun k => ?_, fun k k1 kH u => ?_, fun k hk => ?_,
    fun u hu => ?_, ?_, fun c hc j hj => ?_, fun c hc j hj1 hj => ?_, fun j hj c d hcd => ?_,
    fun X hX => ?_, fun X hX => ?_⟩
  · unfold ordE; rw [ite_eq_right (by omega)]; exact S.ord0
  · unfold ordE; split
    · exact (S.ordNodup k).erase v
    · exact S.ordNodup k
  · rw [hP] at kH
    rw [show (u ∈ ordE ord (ht (ts s) v) v k) = Ent (ordE ord (ht (ts s) v) v) k u from rfl,
      S.fin_ent, F.isN, F.ht]
    unfold Ent; rw [S.ordMem k k1 kH u]
    constructor
    · rintro ⟨⟨h1', h2'⟩, h3'⟩; exact ⟨⟨h1', fun e => h3' (by rw [← h2', e]) e⟩, h2'⟩
    · rintro ⟨⟨h1', h2'⟩, h3'⟩; exact ⟨⟨h1', h3'⟩, fun _ => h2'⟩
  · rw [hP] at hk; unfold ordE; rw [ite_eq_right (by omega)]; exact S.ordHigh k hk
  · rw [F.isN] at hu; rw [F.ht, hP]; exact S.htN u hu.1
  · rw [hP]
    obtain ⟨r1, r2, r3⟩ := S.root
    refine ⟨?_, (F.liveN _).mpr ⟨r2, ?_⟩, by rw [F.livePar]; exact r3⟩
    · unfold ordE; rw [ite_eq_right (by omega)]; exact r1
    · intro e; rw [← e] at hg; exact absurd hg.2 (by rw [r2.2]; simp)
  · rw [hP] at hj
    rw [F.pp]
    exact (S.fin_ent).mpr ⟨S.pathEnt c hc j hj, fun hjh => by subst hjh; exact hppv hc⟩
  · rw [hP] at hj
    rw [F.pp, F.pp, S.fin_order hg F]
    split
    · next hX =>
      have hjh : j = ht (ts s) v + 1 := by
        rw [← (hin _ hX).2, (S.isN_pp hc hj1 hj).2]
      rw [List.mem_erase_of_ne (by rw [show j - 1 = ht (ts s) v by omega]; exact hppv hc)]
      exact S.W3 c hc j hj1 hj
    · exact S.W3 c hc j hj1 hj
  · rw [hP] at hj
    rw [F.pp, F.pp]
    rcases S.O2 j hj c d hcd with h | h
    · exact Or.inl h
    · right
      exact (S.fin_before (fun hjh => by subst hjh; exact ⟨hppv hcd.mem_left, hppv
        hcd.mem_right⟩)).mpr h
  · rw [F.isN] at hX
    rw [S.fin_order hg F, F.ht]
    unfold ordE
    split
    · next hX' =>
      rw [ite_eq_left (by rw [(hin X hX').2]; omega)]
      have := S.O1 X hX.1
      rw [(hin X hX').2, Nat.add_sub_cancel] at this ⊢
      exact this.erase v
    · next hX' =>
      split
      · next hk =>
        refine sublist_erase_of_not_mem (S.O1 X hX.1) fun hm => hX' ?_
        have hvent : Ent ord (ht (ts s) v) v := (S.ordMem _ hv1 hvH v).mpr ⟨hg.1, rfl⟩
        have := (S.tabsIff _ v X hvent).mpr ⟨hX.1, by omega, hm⟩
        unfold tabs at this; rwa [ite_eq_right (by omega)] at this
      · exact S.O1 X hX.1
  · rw [F.isN] at hX; exact S.fin_labs F X hX.1

omit S in
theorem Shape.fin_live (u : Nat) : liveN s' u ↔ liveN (ts s) u := by
  rw [F.liveN]
  constructor
  · exact fun h => h.1
  · intro h; refine ⟨h, fun e => ?_⟩; rw [e] at h; exact absurd hg.2 (by rw [h.2]; simp)

/-- Ending one drain preserves the targets and order of every remaining ghost. -/
theorem Shape.fin_ghost : ∀ g, ghostN s' g →
    liveN s' (nd s' g).t1 ∧ liveN s' (nd s' g).t2 ∧ ht s' (nd s' g).t1 = ht s' g ∧
      ht s' (nd s' g).t2 = ht s' g ∧ srcOf s' (nd s' g).t1 = g ∧
      srcOf s' (nd s' g).t2 = g ∧ (nd s' g).livePar = NIL ∧
      (nd s' g).children = [] ∧ srcOf s' g = NIL ∧ ht s' g < s'.P.H ∧
      (nd s' (nd s' g).t1).livePar = (nd s' (nd s' g).t2).livePar ∧
      [(nd s' g).t1, (nd s' g).t2] <:+: (nd s' (nd s' (nd s' g).t1).livePar).children ∧
      [(nd s' g).t1, g, (nd s' g).t2] <:+: ordE ord (ht (ts s) v) v (ht s' g) := by
  obtain ⟨-, -, -, -, hs1, hs2, -⟩ := S.ghost v hg
  have hP := F.P
  have hL := Shape.fin_live hg F
  have hnv : ∀ u, liveN (ts s) u → u ≠ v := fun u hu e => by
    rw [e] at hu; exact absurd hg.2 (by rw [hu.2]; simp)
  -- a target of `v` is released; any other node keeps its source
  have hsrc : ∀ u, liveN (ts s) u → srcOf s' u =
      if u = (nd (ts s) v).t1 ∨ u = (nd (ts s) v).t2 then NIL else srcOf (ts s) u := fun u hu => by
    rw [F.srcOf]
    by_cases ht : u = (nd (ts s) v).t1 ∨ u = (nd (ts s) v).t2
    · rw [ite_eq_left ht, ite_eq_left ⟨ht, by rcases ht with e | e <;> rw [e] <;> assumption⟩]
    · rw [ite_eq_right ht, ite_eq_right (fun h => ht h.1)]
  intro g hg'; rw [F.ghostN] at hg'
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := S.ghost g hg'.1
  have hgv := hg'.2
  -- the targets of `g` are not those of `v`
  have hn1 : ¬ ((nd (ts s) g).t1 = (nd (ts s) v).t1 ∨ (nd (ts s) g).t1 = (nd (ts s) v).t2) := by
    rintro (e | e) <;> apply hgv <;> [rw [← g5, ← hs1, e]; rw [← g5, ← hs2, e]]
  have hn2 : ¬ ((nd (ts s) g).t2 = (nd (ts s) v).t1 ∨ (nd (ts s) g).t2 = (nd (ts s) v).t2) := by
    rintro (e | e) <;> apply hgv <;> [rw [← g6, ← hs1, e]; rw [← g6, ← hs2, e]]
  rw [F.t1, F.t2, hL, hL, F.ht, F.ht, F.ht, hsrc _ g1, hsrc _ g2, ite_eq_right hn1,
    ite_eq_right hn2,
    F.livePar, F.children, F.livePar, F.livePar, F.children, F.srcOf, hP]
  refine ⟨g1, g2, g3, g4, g5, g6, g7, g8, ?_, g10, g11, g12, ?_⟩
  · rw [g9]; split <;> rfl
  · unfold ordE; split
    · refine infix_erase (S.ordNodup _) g13 ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (e | e | e)
      · exact hnv _ g1 e.symm
      · exact hgv e.symm
      · exact hnv _ g2 e.symm
    · exact g13

/-- Removing an empty ghost range leaves every chunk tag correct. -/
theorem Shape.fin_tags (hemp : rng (ts s) cl v = []) :
    ∀ c ∈ cl, s'.tag c = tagF s' c := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hin, -⟩ := S.fin_facts hg
  have hP := F.P
  have hppv : ∀ {c : Nat}, c ∈ cl → pp (ts s) c (ht (ts s) v) ≠ v :=
    fun hc => Shape.fin_ppv hemp hc
  intro c hc; rw [F.tag]
  rw [S.tags c hc]
  unfold tagF; rw [hP]
  apply (tagUp_congr (by rw [hP]) _ _).symm
  intro i hi1 hi2
  unfold digit
  rw [F.pp, F.pp, Shape.fin_lab F]
  intro hX e
  have := (hin _ hX).2
  rw [(S.isN_pp hc hi1 (by omega)).2] at this
  rw [show i - 1 = ht (ts s) v by omega] at e
  exact hppv hc e

/-- **The order invariant after the drain ends.** -/
theorem Shape.fin_shape (hemp : rng (ts s) cl v = []) :
    Shape s' cl (ordE ord (ht (ts s) v) v) := by
  obtain ⟨hv, hno, hni, hvo, hvi, h1, h2, h12, ho1, ho2, hi1, hi2, hoi, hin, hent⟩ := S.fin_facts hg
  obtain ⟨hv1, hvH⟩ := S.htN v hg.1
  obtain ⟨hl1, hl2, hh1, hh2, hs1, hs2, -, -, -, hlt, -⟩ := S.ghost v hg
  have hP := F.P
  have hppv : ∀ {c : Nat}, c ∈ cl → pp (ts s) c (ht (ts s) v) ≠ v := fun hc => Shape.fin_ppv hemp hc
  have hL := Shape.fin_live hg F
  have hvent : Ent ord (ht (ts s) v) v := (S.ordMem _ hv1 hvH v).mpr ⟨hg.1, rfl⟩
  have htabv : ∀ X, X ∈ (nd (ts s) v).inTables ↔ isN (ts s) X ∧ ht (ts s) X = ht (ts s) v + 1 ∧
      v ∈ order (ts s) X := fun X => by
    have := S.tabsIff _ v X hvent; unfold tabs at this; rwa [ite_eq_right (by omega)] at this
  have hnv : ∀ u, liveN (ts s) u → u ≠ v := fun u hu e => by
    rw [e] at hu; exact absurd hg.2 (by rw [hu.2]; simp)
  -- a target of `v` is released; any other node keeps its source
  have hsrc : ∀ u, liveN (ts s) u → srcOf s' u =
      if u = (nd (ts s) v).t1 ∨ u = (nd (ts s) v).t2 then NIL else srcOf (ts s) u := fun u hu => by
    rw [F.srcOf]
    by_cases ht : u = (nd (ts s) v).t1 ∨ u = (nd (ts s) v).t2
    · rw [ite_eq_left ht, ite_eq_left ⟨ht, by rcases ht with e | e <;> rw [e] <;> assumption⟩]
    · rw [ite_eq_right ht, ite_eq_right (fun h => ht h.1)]
  refine {
    toShapeT := S.fin_shapeT hg F hemp
    up := ?_
    lp := ?_
    kids := ?_
    OT := ?_
    ghost := S.fin_ghost hg F
    src := ?_
    tabEnt := ?_
    tabsIff := ?_
    tabsNodup := ?_
    Q := ?_
    W1 := ?_
    side := ?_
    pathSize := ?_
    P := ?_
    Sr := ?_
    ends := ?_
    tags := S.fin_tags hg F hemp }
  · intro u hu hh; rw [hL] at hu; rw [F.ht, hP] at hh
    rw [F.livePar, hL, F.ht, F.ht, F.children]; exact S.up u hu hh
  · intro c hc; rw [F.lpr, hL, F.ht, F.children]; exact S.lp c hc
  · intro u hu; rw [hL] at hu
    obtain ⟨k1, k2, k3⟩ := S.kids u hu
    rw [F.children, F.ht]
    refine ⟨k1, ?_, fun e he => ?_⟩
    · unfold ordE; split
      · exact sublist_erase_of_not_mem k2 fun hm => by
          have := (k3 v hm).2 (by
            have := S.htN u hu.1; rename_i hk; omega)
          exact absurd hg.2 (by rw [this.2]; simp)
      · exact k2
    · rw [F.par, hL]; exact k3 e he
  · intro k k1 kH u u' e e' hu hu' hb he he' hpe hpe'
    rw [hP] at kH; rw [hL] at hu hu'; rw [F.par] at hpe hpe'
    rw [S.fin_before (fun _ => ⟨hnv u hu, hnv u' hu'⟩)] at hb
    rw [S.fin_ent] at he he'
    rw [S.fin_before (fun hk => ⟨he.2 hk, he'.2 hk⟩)]
    exact S.OT k k1 kH u u' e e' hu hu' hb he.1 he'.1 hpe hpe'
  · intro t ht' hst
    rw [hL] at ht'
    rw [hsrc t ht'] at hst ⊢
    split at hst
    · exact absurd rfl hst
    · next htv =>
      rw [ite_eq_right htv]
      obtain ⟨hs, hor⟩ := S.src t ht' hst
      have hsv : srcOf (ts s) t ≠ v := by
        intro e; rw [e] at hor; exact htv hor
      rw [F.ghostN, F.t1, F.t2]
      exact ⟨⟨hs, hsv⟩, hor⟩
  · -- table entries
    intro X hX e he
    rw [F.isN] at hX
    rw [S.fin_order hg F] at he
    rw [F.ht, S.fin_ent]
    have hmem : e ∈ order (ts s) X ∧ (X ∈ (nd (ts s) v).inTables → e ≠ v) := by
      split at he
      · next hX' => exact ⟨List.mem_of_mem_erase he, fun _ => ((S.order_nodup
        hX.1).mem_erase_iff.mp he).1⟩
      · next hX' => exact ⟨he, fun h => absurd h hX'⟩
    refine ⟨S.tabEnt X hX.1 e hmem.1, fun hk => ?_⟩
    by_cases hX' : X ∈ (nd (ts s) v).inTables
    · exact hmem.2 hX'
    · intro e'; subst e'; exact hX' ((htabv X).mpr ⟨hX.1, by omega, hmem.1⟩)
  · -- the tables of an entry
    intro k e X he
    rw [S.fin_ent] at he
    rw [S.fin_tabs hg F k e he.1 he.2, F.isN, F.ht, S.fin_order hg F]
    have hXh : X ∈ (nd (ts s) v).inTables → ht (ts s) X = ht (ts s) v + 1 := fun h => (hin X h).2
    split
    · next hA =>
      rw [(S.tabsNodup k e he.1).mem_erase_iff, S.tabsIff k e X he.1]
      constructor
      · rintro ⟨hxv, hx1, hx2, hx3⟩
        refine ⟨⟨hx1, hxv⟩, hx2, ?_⟩
        split
        · next hX' => exfalso; have := hXh hX'; omega
        · exact hx3
      · rintro ⟨⟨hx1, hxv⟩, hx2, hx3⟩
        refine ⟨hxv, hx1, hx2, ?_⟩
        split at hx3
        · next hX' => exfalso; have := hXh hX'; omega
        · exact hx3
    · next hB =>
      rw [S.tabsIff k e X he.1]
      constructor
      · rintro ⟨hx1, hx2, hx3⟩
        have hxv : X ≠ v := by
          intro e'; subst e'; exact hB ⟨hx3, by omega⟩
        refine ⟨⟨hx1, hxv⟩, hx2, ?_⟩
        split
        · next hX' => exact List.mem_erase_of_ne (he.2 (by have := hXh hX'; omega)) |>.mpr hx3
        · exact hx3
      · rintro ⟨⟨hx1, hxv⟩, hx2, hx3⟩
        refine ⟨hx1, hx2, ?_⟩
        split at hx3
        · exact List.mem_of_mem_erase hx3
        · exact hx3
  · intro k e he
    rw [S.fin_ent] at he
    rw [S.fin_tabs hg F k e he.1 he.2]
    split
    · exact (S.tabsNodup k e he.1).erase v
    · exact S.tabsNodup k e he.1
  · intro k e X he hX
    rw [S.fin_ent] at he
    rw [S.fin_tabs hg F k e he.1 he.2] at hX
    have hX' : X ∈ tabs (ts s) k e ∧ X ≠ v := by
      split at hX
      · next hA => exact ⟨List.mem_of_mem_erase hX, ((S.tabsNodup k e he.1).mem_erase_iff.mp hX).1⟩
      · next hB =>
        refine ⟨hX, fun e' => ?_⟩
        subst e'
        obtain ⟨-, hx2, hx3⟩ := (S.tabsIff k e X he.1).mp hX
        exact hB ⟨hx3, by omega⟩
    rw [F.par, F.srcOf]
    rcases S.Q k e X he.1 hX'.1 with h | h
    · exact Or.inl h
    · right
      rw [ite_eq_right _]
      · exact h
      rintro ⟨-, h'⟩; exact hX'.2 (h.trans h')
  · intro g hg' X hX
    rw [F.ghostN] at hg'
    rw [F.ht] at hX
    have hent' : Ent ord (ht (ts s) g) g :=
      (S.ordMem _ (S.htN g hg'.1.1).1 (S.htN g hg'.1.1).2 g).mpr ⟨hg'.1.1, rfl⟩
    rw [S.fin_tabs hg F _ g hent' (fun _ => hg'.2)] at hX
    have hX' : X ∈ tabs (ts s) (ht (ts s) g) g := by
      split at hX
      · exact List.mem_of_mem_erase hX
      · exact hX
    have hw := S.W1 g hg'.1 X hX'
    obtain ⟨g1, g2, -⟩ := S.ghost g hg'.1
    rw [S.fin_order hg F, F.t1, F.t2]
    split
    · refine infix_erase (S.order_nodup ((S.tabsIff _ g X hent').mp hX').1) hw ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (e | e | e)
      · exact hnv _ g1 e.symm
      · exact hg'.2 e.symm
      · exact hnv _ g2 e.symm
    · exact hw
  · intro g hg' e he
    rw [F.ghostN] at hg'
    rw [S.fin_order hg F] at he
    have hmem : e ∈ order (ts s) g ∧ (g ∈ (nd (ts s) v).inTables → e ≠ v) := by
      split at he
      · next hX' => exact ⟨List.mem_of_mem_erase he, fun _ => ((S.order_nodup
        hg'.1.1).mem_erase_iff.mp he).1⟩
      · next hX' => exact ⟨he, fun h => absurd h hX'⟩
    rw [Shape.fin_sideL F g e hmem.2, F.ht, F.par, F.t1]
    exact S.side g hg'.1 e hmem.1
  · intro c hc; rw [F.path, hP]; exact S.pathSize c hc
  · intro c hc j hj1 hj; rw [hP] at hj
    rw [F.pp, F.anc, F.ghostN, F.t1, F.t2]
    rcases S.P c hc j hj1 hj with h | ⟨h1', h2'⟩
    · exact Or.inl h
    · refine Or.inr ⟨⟨h1', fun e => ?_⟩, h2'⟩
      have hjh : j = ht (ts s) v := by rw [← (S.isN_pp hc hj1 hj).2, e]
      subst hjh; exact hppv hc e
  · intro c hc j hj1 hj hgj; rw [hP] at hj
    rw [F.pp, F.ghostN] at hgj; rw [F.pp, F.anc, S.fin_order hg F]
    have hsr := S.Sr c hc j hj1 hj hgj.1
    split
    · next hX =>
      have hjh : j = ht (ts s) v + 1 := by
        rw [← (hin _ hX).2, (S.anc_live hc j hj1 hj).2]
      rw [List.mem_erase_of_ne (by rw [show j - 1 = ht (ts s) v by omega]; exact hppv hc)]
      exact hsr
    · exact hsr
  · intro u hu; rw [F.isN] at hu; rw [F.first, F.last, F.rng]; exact S.ends u hu.1

end fin

theorem filter_erase_false {l : List Nat} {p : Nat → Bool} {v : Nat} (hv : p v = false) :
    (l.erase v).filter p = l.filter p := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    by_cases hx : x = v
    · subst hx; rw [List.erase_cons_head, List.filter_cons, hv]; rfl
    · rw [List.erase_cons_tail (by simpa using hx), List.filter_cons, List.filter_cons, ih]

/-- **A sweep call on an empty range keeps the invariant**: the drain ends, and the walk moves
up. -/
theorem inv_drainFinish {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {w up v k : Nat}
    (hI : InvJ (ts s) cl ord dr n0 (some { j with pc := .fund w up v k }))
    (hTP : TopParams s.P) (hemp : rng (ts s) cl v = []) :
    (drainStep v).run s = .ok false (fdS v s) ∧ TopRel s (fdS v s) ∧
      InvJ (ts (fdS v s)) cl (ordE ord (ht (ts s) v) v) dr n0 (some { j with pc := .walk (some
        up) }) := by
  have S := hI.shape
  obtain ⟨hpos, hat⟩ := hI.job _ rfl
  simp only [JobAt] at hat
  obtain ⟨hwl, hwa, hua, hg, hsw, hks⟩ := hat
  obtain ⟨hv, hno, hni, hvo, hvi, h1, h2, h12, ho1, ho2, hi1, hi2, hoi, hin, hent⟩ := S.fin_facts hg
  have hrun : (drainStep v).run s = .ok false (fdS v s) := by
    refine drainStep_finish hg.1.2.2 ?_ hni fun T hT => (S.fin_facts
      hg).2.2.2.2.2.2.2.2.2.2.2.2.2.1 T hT |>.2 |> fun _ => ?_
    · obtain ⟨hf, -⟩ := S.ends v hg.1
      change (nd (ts s) v).first = NIL
      rw [hf, hemp]; rfl
    · have hvent : Ent ord (ht (ts s) v) v :=
        (S.ordMem _ (S.htN v hg.1).1 (S.htN v hg.1).2 v).mpr ⟨hg.1, rfl⟩
      have := S.tabsIff _ v T hvent
      unfold tabs at this; rw [ite_eq_right (by have := (S.htN v hg.1).1; omega)] at this
      exact (this.mp hT).2.2
  refine ⟨hrun, by have := top_drainStep v s; rw [hrun] at this; exact this, ?_⟩
  have F := S.fin_frame hg
  have SH := S.fin_shape hg F hemp
  have hL := Shape.fin_live hg F
  -- the walk node is a target of the ghost
  have hsrc := S.src w hwl (by rw [hsw]; exact fun e => hg.1.1 e)
  rw [hsw] at hsrc
  obtain ⟨hl1, hl2, hh1, hh2, hs1, hs2, -, -, -, hlt, -⟩ := S.ghost v hg
  have hwh : ht (ts s) w = ht (ts s) v := by rcases hsrc.2 with e | e <;> rw [e] <;> assumption
  -- the walk goes on from the live parent of the target
  obtain ⟨hupl, huph, -⟩ := S.up w hwl (by omega)
  have hup : up = (nd (ts s) w).livePar := by
    rw [hua]
    have := anc_succ (s := ts s) j.y (ht (ts s) w) (S.htN w hwl.1).1
    rw [this, ← hwa]
  rw [← hup] at hupl huph
  have Ti := hI.time
  have Ro := hI.room
  have hpend : pend (ts (fdS v s)) (some { j with pc := .walk (some up) }) =
      pend (ts s) (some { j with pc := .fund w up v k }) := by
    change upChain _ ((ts (fdS v s)).P.H + 1) up = upChain _ ((ts s).P.H + 1) up
    rw [F.upChain, F.P]
  -- other ghosts owe the same sweeps
  have hslack : ∀ u, u ≠ v → slack (ts (fdS v s)) (some { j with pc := .walk (some up) }) u =
      slack (ts s) (some { j with pc := .fund w up v k }) u := by
    intro u hu
    have hc : curH (ts (fdS v s)) { j with pc := .walk (some up) } = ht (ts s) w + 1 := by
      unfold curH; simp only
      rw [ite_eq_right (fun e => by rw [e] at hupl; exact hupl.1.1 rfl), F.ht, huph]
    have hc' : curH (ts s) { j with pc := .fund w up v k } = ht (ts s) w + 1 := rfl
    unfold slack
    simp only [F.anc, F.ht, F.t1, F.t2, F.P, hc, hc', ite_eq_right (Ne.symm hu)]
  have hfun : ∀ u, funded (ts (fdS v s)) (some { j with pc := .walk (some up) }) u ↔
      funded (ts s) (some { j with pc := .fund w up v k }) u := by
    intro u; unfold funded; simp only [F.anc, F.ht, F.t1, F.t2]
  have hlen : TabLen (ts (fdS v s)) dr n0 := hI.len.mono fun X => by
    unfold order Node.order
    rw [F.node X]
    split
    · simp only [List.length_map, assocErase]
      exact ⟨List.length_filter_le _ _, List.length_filter_le _ _⟩
    · simp
  refine ⟨SH, ?_, ?_, ?_, by rw [F.P]; exact hI.cap, hlen⟩
  · refine ⟨fun u hu => ?_, fun u hu hp hs => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_,
      fun u hu => ?_, fun u hu hu' => ?_, fun u hu hs => ?_, ?_, ?_⟩
    · rw [hL] at hu; rw [F.weight, hpend, F.tw]; exact Ti.wts u hu
    · rw [hL] at hu; rw [F.livePar] at hp; rw [F.weight, F.ht, F.P]
      rw [F.srcOf] at hs
      split at hs
      · next hrel =>
        have := Ti.release S hTP hg hrel.1 (fun hm => by
          obtain ⟨-, hge⟩ := S.upChain_mem _ _ _ hupl hm
          rw [huph, hwh] at hge
          rcases hrel.1 with e | e <;> rw [e] at hge <;> [rw [hh1] at hge; rw [hh2] at hge] <;>
            omega)
        rcases hrel.1 with e | e <;> rw [e] <;> [rw [hh1]; rw [hh2]] <;> rw [← e] <;> exact this
      · exact Ti.wA u hu hp hs
    · rw [F.ghostN] at hu; rw [F.weight, F.ht, F.P]; exact Ti.wB u hu.1
    · rw [F.ghostN] at hu
      have : ew (ts (fdS v s)) cl u = ew (ts s) cl u := by
        unfold ew; rw [F.draining, F.t1, F.t2, F.tw, F.tw, F.tw]
      rw [F.weight, this]; exact Ti.wF u hu.1
    · rw [F.ghostN] at hu
      have hew : ew (ts (fdS v s)) cl u = ew (ts s) cl u := by
        unfold ew; rw [F.draining, F.t1, F.t2, F.tw, F.tw, F.tw]
      unfold fundOf; rw [hew, F.weight, F.rng, hslack u hu.2, F.P]
      exact Ti.wC u hu.1
    · rw [F.ghostN] at hu
      have hew : ew (ts (fdS v s)) cl u = ew (ts s) cl u := by
        unfold ew; rw [F.draining, F.t1, F.t2, F.tw, F.tw, F.tw]
      unfold fundOf; rw [hew, F.weight, F.P]
      have := Ti.wC' u hu.1
      unfold fundOf at this
      by_cases hf : funded (ts s) (some { j with pc := .fund w up v k }) u
      · rw [ite_eq_left ((hfun u).mpr hf)]; rw [ite_eq_left hf] at this; exact this
      · rw [ite_eq_right (fun h => hf ((hfun u).mp h))]; rw [ite_eq_right hf] at this; exact this
    · rw [hL] at hu; rw [F.P] at hu'; rw [F.tw, F.ht, F.P]; exact Ti.wD u hu hu'
    · rw [hL] at hu; rw [F.srcOf] at hs; rw [F.P]
      split at hs
      · exact absurd rfl hs
      · exact Ti.big u hu hs
    · intro u hu hH; rw [F.isN] at hu; rw [F.P] at hH; rw [F.ht]; exact Ti.chain u hu.1 hH
    · intro u hu; rw [hL] at hu; rw [F.tw]; exact Ti.tw1 u hu
  · refine ⟨fun X hX => ?_, fun X hX => ?_, fun X hX h1' => ?_, fun X hX h2' => ?_⟩
    · rw [F.isN] at hX
      unfold labs; rw [F.table, F.P]
      split
      · exact gapsGe_assocErase v (Ro.gaps X hX.1)
      · exact Ro.gaps X hX.1
    · rw [F.isN] at hX; rw [F.ht, F.P]; exact Ro.n0le X hX.1
    · rw [F.isN] at hX; rw [F.ht] at h1'
      have : ew (ts (fdS v s)) cl X = ew (ts s) cl X := by
        unfold ew; rw [F.draining, F.t1, F.t2, F.tw, F.tw, F.tw]
      rw [this, F.P]; exact Ro.pot1 X hX.1 h1'
    · rw [F.isN] at hX; rw [F.ht] at h2'
      have hew : ew (ts (fdS v s)) cl X = ew (ts s) cl X := by
        unfold ew; rw [F.draining, F.t1, F.t2, F.tw, F.tw, F.tw]
      have hvl : ¬ liveN (ts s) v := fun h => absurd hg.2 (by rw [h.2]; simp)
      have hgr : growth (ts (fdS v s)) cl X = growth (ts s) cl X := by
        unfold growth
        rw [S.fin_order hg F, F.ht, F.P]
        simp only [hL, F.tw]
        split
        · rw [filter_erase_false (by simp [hvl])]
        · rfl
      have hol : oldLive (ts (fdS v s)) X = oldLive (ts s) X := by
        unfold oldLive
        rw [S.fin_order hg F]
        simp only [hL]
        split
        · rw [filter_erase_false (by simp [hvl])]
        · rfl
      rw [hew, hgr, hol, F.ht, F.P]; exact Ro.pot2 X hX.1 h2'
  · intro j' hj'
    cases hj'
    refine ⟨hpos, ?_⟩
    simp only [JobAt]
    right
    rw [hL, F.ht, F.anc]
    refine ⟨hupl, ?_⟩
    rw [huph, hwh, hua, hwh]

end OrderMaintenance.Proof.Top
