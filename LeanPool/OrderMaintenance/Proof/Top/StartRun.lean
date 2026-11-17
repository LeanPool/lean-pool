/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartRoom


/-!
# M5: `startDrain` runs, at a drain start
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
section run
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  (hpc : j.pc = .walk (some v)) (hv0 : v ≠ NIL) (hI : InvJ (ts s) cl ord dr n0 (some j))
  (hlp : (nd (ts s) v).livePar ≠ NIL) (hTP : TopParams s.P) (hof : (nd (ts s) v).overflowOf = NIL)
  (hW : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2)
  {side : List (Nat × Side)} (hside : sSideO (wiC s v) v = some side)
  (hlook : ∀ x, lookup side x =
    if 2 ≤ ht (ts s) v ∧ x ∈ sEntries (wiC s v) v ∧ (nd (ts s) x).draining = true then
      lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (nd (ts
        s) x).t1
    else lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) x)
include hpc hv0 hI hlp hTP hof hW hlook

theorem sr_hyps : SDHyps s v side := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨hl, hlh, -⟩ := sd_up hpc hv0 hI hlp
  obtain ⟨h1, -⟩ := sd_ht hpc hv0 hI hlp
  obtain ⟨hknd, -, hk⟩ := S.kids v hvl
  have hent : Ent ord (ht (ts s) v) v := (S.ordMem _ h1 (S.htN v hvl.1).2 v).mpr ⟨hvl.1, rfl⟩
  have hen := sc_entries_nodup hpc hv0 hI
  obtain ⟨c1, c2⟩ := sw_ch hpc hv0 hI hlp hTP hof hW hlook
  refine ⟨hvl.1.2.1, hl.1.2.1, (fun e => by rw [e] at hlh; omega), ?_,
    fun T hT => ?_, hen.filter _, hen.filter _,
    (by rw [c1]; exact hknd.sublist (List.take_sublist _ _)),
    (by rw [c2]; exact hknd.sublist (List.drop_sublist _ _)),
    fun h2 e he => ?_, fun h2 e he => ?_⟩
  · have := S.tabsNodup _ v hent; unfold tabs at this; rw [ite_eq_right (by omega)] at this;
      exact this
  · have hT' : T ∈ tabs (ts s) (ht (ts s) v) v := by
      unfold tabs; rw [ite_eq_right (by omega)]; exact hT
    exact ((S.tabsIff _ v T hent).mp hT').1.2.1
  · have hm := ((sw_entries).mp he).1
    exact ((sp_entry hpc hv0 hI hlp hm).2 (by omega)).1.2.1
  · exact ((hk e he).2 (by omega)).1.2.1

include hside

/-- **`startDrain` runs** to the pure state, its guards passing. -/
theorem sr_run : (startDrain v).run (wiC s v) = .ok ⟨⟩ (sdS (wiC s v) v side) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨hl, hlh, hvL⟩ := sd_up hpc hv0 hI hlp
  obtain ⟨hk2, hk1, hkn⟩ := sp_k hpc hv0 hI hlp hTP hof hW
  have H := sr_hyps hpc hv0 hI hlp hTP hof hW hlook
  refine startDrain_run (by rw [sd_kids_eq]; exact hk2) (fun h => by omega) hside (fun T hT =>
    ?_) H.t_nd
    (fun e he => by
      rw [sd_kids_eq] at he
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook he]; rfl)
    (by rw [SDHyps.w_livePar, SDHyps.w_children]; exact hvL) H.t_hv
  rw [SDHyps.w_inTables] at hT
  obtain ⟨A, le, Bs, htab, hA, hsd, h1, h2, -⟩ := room_up hI hTP hvl.1 hT 0 0
  refine ⟨A, le, Bs, ?_, hA, ?_, h1, h2⟩
  · rw [SDHyps.w_table]; exact htab
  · rw [SDHyps.w_draining, SDHyps.w_side]; exact hsd

theorem sr_topRel : TopRel (wiC s v) (sdS (wiC s v) v side) := by
  have := top_startDrain v (wiC s v)
  rw [sr_run hpc hv0 hI hlp hTP hof hW hside hlook] at this
  exact this

end run

end OrderMaintenance.Proof.Top
