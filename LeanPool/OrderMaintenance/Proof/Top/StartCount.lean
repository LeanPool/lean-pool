/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartParts


/-!
# M5: a fresh table is small (T4's counting)

A part holds at most `1 + (τ_h - 1)/λ_{h-1}` children (each fresh one weighs at least `λ_{h-1}`,
at most one is a chain node) and at most half as many ghosts (each between two of them).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- Few heavy elements fit under a weight bound. -/
theorem count_heavy {T : List Nat} (f : Nat → Nat) (lam tau : Nat) (P : Nat → Prop) [DecidablePred P]
    (hlam : 1 ≤ lam) (h1 : ∀ x ∈ T, 1 ≤ f x) (h2 : ∀ x ∈ T, ¬P x → lam ≤ f x)
    (h3 : (T.filter (fun x => decide (P x))).length ≤ 1) (hs : (T.map f).sum ≤ tau) :
    T.length ≤ 1 + (tau - 1) / lam := by
  have hsplit := List.length_eq_length_filter_add (fun x => decide (P x)) (l := T)
  set p := (T.filter (fun x => decide (P x))).length with hp
  set q := (T.filter (fun x => !decide (P x))).length with hq
  -- the sum is at least `lam * q + p`
  have hsum : lam * q + p ≤ (T.map f).sum := by
    have e := List.sum_map_filter_add_sum_map_filter_not P f T
    simp only [decide_not] at e
    have a1 : p ≤ ((T.filter (fun x => decide (P x))).map f).sum := by
      have := List.length_le_sum_of_one_le ((T.filter (fun x => decide (P x))).map f)
        (fun y hy => by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact h1 x (List.mem_of_mem_filter hx))
      simpa using this
    have a2 : lam * q ≤ ((T.filter (fun x => !decide (P x))).map f).sum := by
      have := List.card_nsmul_le_sum ((T.filter (fun x => !decide (P x))).map f) lam
        (fun y hy => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          have hm := List.mem_filter.mp hx
          exact h2 x hm.1 (by simpa using hm.2))
      simp only [List.length_map, smul_eq_mul] at this; rw [Nat.mul_comm]; exact this
    omega
  rw [Nat.add_comm, ← Nat.sub_le_iff_le_add, Nat.le_div_iff_mul_le hlam]
  rcases Nat.lt_or_ge p 1 with hp0 | hp1
  · have hp0' : p = 0 := by omega
    rw [hp0'] at hsum hsplit
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · rw [hq0] at hsplit
      rw [show T.length - 1 = 0 by omega]; simp
    · have e : lam * q = lam * (q - 1) + lam := by
        rw [show q = q - 1 + 1 from (Nat.succ_pred_eq_of_pos hq0).symm, Nat.mul_succ]; simp
      have : T.length - 1 = q - 1 := by omega
      rw [this, Nat.mul_comm]; omega
  · have : T.length - 1 = q := by omega
    rw [this, Nat.mul_comm]; omega

section count
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  (hpc : j.pc = .walk (some v)) (hv0 : v ≠ NIL) (hI : InvJ (ts s) cl ord dr n0 (some j))
  (hlp : (nd (ts s) v).livePar ≠ NIL) (hTP : TopParams s.P) (hof : (nd (ts s) v).overflowOf = NIL)
  (hW : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2)
include hpc hv0 hI hlp hTP hof hW

/-- Few children in a part. -/
theorem sc_part (h2 : 2 ≤ ht (ts s) v) {T : List Nat} (hT : T.Sublist (nd (ts s) v).children)
    (hs : (T.map (tw (ts s) cl)).sum ≤ taud s.P (ht (ts s) v)) :
    T.length ≤ 1 + (taud s.P (ht (ts s) v) - 1) / lamd s.P (ht (ts s) v - 1) := by
  have S := hI.shape
  have Ti := hI.time
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  obtain ⟨hnd, -, hk⟩ := S.kids v hvl
  have hkh : ∀ x ∈ T, liveN (ts s) x ∧ ht (ts s) x = ht (ts s) v - 1 := by
    intro x hx
    have hxk := hT.subset hx
    refine ⟨(hk x hxk).2 h2, ?_⟩
    have := ((S.mem_children hvl).mp hxk).1; rw [ite_eq_right (by omega)] at this; exact this.2
  have hlam : 2 + 2 * Kd s.P (ht (ts s) v - 1) ≤ lamd s.P (ht (ts s) v - 1) := hTP.lamK _ (by omega)
  refine count_heavy (tw (ts s) cl) _ _ (fun x => x ≤ (ts s).P.H) (by omega)
    (fun x hx => Ti.tw1 x (hkh x hx).1) (fun x hx hxH => ?_) ?_ hs
  · have := Ti.wD x (hkh x hx).1 (by omega)
    rw [(hkh x hx).2] at this; exact this
  · apply le_trans (List.Nodup.length_le_of_subset ((hnd.sublist hT).filter _)
      (l₂ := [ht (ts s) v - 1]) ?_) (by simp)
    intro x hx
    obtain ⟨hxT, hxH⟩ := List.mem_filter.mp hx
    simp only [decide_eq_true_eq] at hxH
    have := Ti.chain x (hkh x hxT).1.1 hxH
    rw [(hkh x hxT).2] at this
    simp [← this]

section side
variable {side : List (Nat × Side)}
  (hlook : ∀ x, lookup side x =
    if 2 ≤ ht (ts s) v ∧ x ∈ sEntries (wiC s v) v ∧ (nd (ts s) x).draining = true then
      lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (nd (ts s) x).t1
    else lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) x)
include hlook

/-- The ghosts of a part are at most half of its children. -/
theorem sc_ghosts (h2 : 2 ≤ ht (ts s) v) {Ch G : List Nat} (hCh : Ch.Nodup) (hG : G.Nodup)
    (hGo : ∀ g ∈ G, g ∈ order (ts s) v) (hGd : ∀ g ∈ G, (nd (ts s) g).draining = true)
    (hGt : ∀ g ∈ G, (nd (ts s) g).t1 ∈ Ch ∧ (nd (ts s) g).t2 ∈ Ch) :
    2 * G.length ≤ Ch.length := by
  have S := hI.shape
  have hgh : ∀ g ∈ G, ghostN (ts s) g := fun g hg =>
    ⟨((sp_entry hpc hv0 hI hlp hTP hof hW (hGo g hg)).2 h2).1, hGd g hg⟩
  have hsrc : ∀ g ∈ G, srcOf (ts s) (nd (ts s) g).t1 = g ∧ srcOf (ts s) (nd (ts s) g).t2 = g ∧
      (nd (ts s) g).t1 ≠ (nd (ts s) g).t2 := by
    intro g hg
    obtain ⟨-, -, -, -, h5, h6, -, -, -, -, -, -, hinf⟩ := S.ghost g (hgh g hg)
    exact ⟨h5, h6, ((before_of_infix2 (infix3_left hinf)).trans (before_of_infix2 (infix3_right hinf))
      (S.ordNodup _)).ne (S.ordNodup _)⟩
  have hnd : (G.map (fun g => (nd (ts s) g).t1) ++ G.map (fun g => (nd (ts s) g).t2)).Nodup := by
    rw [List.nodup_append]
    refine ⟨hG.map_on (fun x hx y hy e => by rw [← (hsrc x hx).1, ← (hsrc y hy).1, e]),
      hG.map_on (fun x hx y hy e => by rw [← (hsrc x hx).2.1, ← (hsrc y hy).2.1, e]), ?_⟩
    intro a ha b hb e
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    have hxy : x = y := by rw [← (hsrc x hx).1, ← (hsrc y hy).2.1, e]
    subst hxy
    exact (hsrc x hx).2.2 e
  have hsub : G.map (fun g => (nd (ts s) g).t1) ++ G.map (fun g => (nd (ts s) g).t2) ⊆ Ch := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h; exact (hGt x hx).1
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h; exact (hGt x hx).2
  have := hnd.length_le_of_subset hsub
  simp only [List.length_append, List.length_map] at this
  omega

/-- A part with these children is small. -/
theorem sc_part_len {Part Ch : List Nat} (hPn : Part.Nodup) (hCh : Ch.Sublist (nd (ts s) v).children)
    (hmem : ∀ e ∈ Part, e ∈ Ch ∨ (2 ≤ ht (ts s) v ∧ e ∈ order (ts s) v ∧ (nd (ts s) e).draining = true ∧
      (nd (ts s) e).t1 ∈ Ch ∧ (nd (ts s) e).t2 ∈ Ch))
    (hsum : 2 ≤ ht (ts s) v → (Ch.map (tw (ts s) cl)).sum ≤ taud s.P (ht (ts s) v))
    (hlen1 : ht (ts s) v = 1 → Ch.length ≤ taud s.P 1) :
    Part.length ≤ n0max s.P (ht (ts s) v) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  obtain ⟨hknd, -, hk⟩ := S.kids v hvl
  have hChn : Ch.Nodup := hknd.sublist hCh
  obtain ⟨h1, -⟩ := sd_ht hpc hv0 hI hlp
  by_cases h2 : 2 ≤ ht (ts s) v
  · have hc := sc_part hpc hv0 hI hlp hTP hof hW h2 hCh (hsum h2)
    have hsplit := List.length_eq_length_filter_add (fun x => (nd (ts s) x).draining) (l := Part)
    have hA : (Part.filter (fun x => !(nd (ts s) x).draining)).length ≤ Ch.length := by
      apply (hPn.filter _).length_le_of_subset
      intro x hx
      obtain ⟨hxP, hxd⟩ := List.mem_filter.mp hx
      rcases hmem x hxP with hc1 | ⟨-, -, hd, -⟩
      · exact hc1
      · rw [hd] at hxd; exact absurd hxd (by simp)
    have hG := sc_ghosts hpc hv0 hI hlp hTP hof hW hlook h2 hChn (hPn.filter _)
      (G := Part.filter (fun x => (nd (ts s) x).draining))
      (fun g hg => by
        obtain ⟨hgP, hgd⟩ := List.mem_filter.mp hg
        rcases hmem g hgP with hc1 | ⟨-, ho, -⟩
        · exfalso; have := (hk g (hCh.subset hc1)).2 h2; rw [this.2] at hgd; exact absurd hgd (by simp)
        · exact ho)
      (fun g hg => (List.mem_filter.mp hg).2)
      (fun g hg => by
        obtain ⟨hgP, hgd⟩ := List.mem_filter.mp hg
        rcases hmem g hgP with hc1 | ⟨-, -, -, t1, t2⟩
        · exfalso; have := (hk g (hCh.subset hc1)).2 h2; rw [this.2] at hgd; exact absurd hgd (by simp)
        · exact ⟨t1, t2⟩)
    unfold n0max; rw [ite_eq_right (by omega)]
    have hlen : Part.length ≤ Ch.length + Ch.length / 2 := by omega
    have : Ch.length / 2 ≤ (1 + (taud s.P (ht (ts s) v) - 1) / lamd s.P (ht (ts s) v - 1)) / 2 :=
      Nat.div_le_div_right hc
    omega
  · have hh : ht (ts s) v = 1 := by omega
    have : Part.length ≤ Ch.length := by
      apply hPn.length_le_of_subset
      intro x hx
      rcases hmem x hx with hc1 | ⟨hc2, -⟩
      · exact hc1
      · omega
    unfold n0max; rw [ite_eq_left (by omega)]
    have := hlen1 hh
    have e : taud s.P 1 = s.P.a + 1 := rfl
    omega

theorem sc_entries_nodup : (sEntries (wiC s v) v).Nodup := by
  unfold sEntries drainEntries
  rw [show ((wiC s v).nodes.getX v).order = order (ts s) v from (wiC_sameTree s v).order v]
  exact (sp_order_nodup hpc hv0 hI hlp hTP hof hW).filter _

/-- **A fresh table is small** (the left part). -/
theorem sc_left : (sLeft (wiC s v) v side).length ≤ n0max s.P (ht (ts s) v) := by
  refine sc_part_len hpc hv0 hI hlp hTP hof hW hlook ((sc_entries_nodup hpc hv0 hI hlp hTP hof hW hlook).filter _)
    (List.take_sublist _ _) (fun e he => ?_) (fun h2 => (sd_cut2 hpc hv0 hI hlp hTP h2 hof hW).2.2.2.2.2.1)
    (fun h1 => (sd_cut1 hpc hv0 hI hlp h1 hof hW).2.2.2.2.1)
  rcases (sw_left hpc hv0 hI hlp hTP hof hW hlook).mp he with hc1 | ⟨h2, ho, hd, -, ht1⟩
  · exact Or.inl hc1
  · exact Or.inr ⟨h2, ho, hd, ht1, (sw_nosep hpc hv0 hI hlp hTP hof hW hlook h2 ho hd).mp ht1⟩

/-- **A fresh table is small** (the right part). -/
theorem sc_right : (sRight (wiC s v) v side).length ≤ n0max s.P (ht (ts s) v) := by
  refine sc_part_len hpc hv0 hI hlp hTP hof hW hlook ((sc_entries_nodup hpc hv0 hI hlp hTP hof hW hlook).filter _)
    (List.drop_sublist _ _) (fun e he => ?_) (fun h2 => (sd_cut2 hpc hv0 hI hlp hTP h2 hof hW).2.2.2.2.2.2.2)
    (fun h1 => (sd_cut1 hpc hv0 hI hlp h1 hof hW).2.2.2.2.2.2)
  rcases (sw_right hpc hv0 hI hlp hTP hof hW hlook).mp he with hc1 | ⟨h2, ho, hd, -, ht1⟩
  · exact Or.inl hc1
  · refine Or.inr ⟨h2, ho, hd, ht1, ?_⟩
    have S := hI.shape
    obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
    obtain ⟨hnd, -, -⟩ := S.kids v hvl
    obtain ⟨-, ht2k, -⟩ := sp_ghost hpc hv0 hI hlp hTP hof hW h2 ho hd
    have hns := sw_nosep hpc hv0 hI hlp hTP hof hW hlook h2 ho hd
    have hsp : (nd (ts s) v).children = (nd (ts s) v).children.take (sK (wiC s v) v) ++
        (nd (ts s) v).children.drop (sK (wiC s v) v) := (List.take_append_drop _ _).symm
    have hdis := (List.nodup_append.mp (hsp ▸ hnd)).2.2
    have ht1n : (nd (ts s) e).t1 ∉ (nd (ts s) v).children.take (sK (wiC s v) v) :=
      fun hx => hdis _ hx _ ht1 rfl
    have hm := ht2k; rw [hsp, List.mem_append] at hm
    rcases hm with hx | hx
    · exact absurd (hns.mpr hx) ht1n
    · exact hx


end side

end count

end OrderMaintenance.Proof.Top
