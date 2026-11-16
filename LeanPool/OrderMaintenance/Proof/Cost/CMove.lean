/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.CSteps


/-!
# The invariants across a chunk-split move and a chunk removal
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Counting -/

theorem length_filter_split {α : Type} (L : List α) (q P : α → Bool) (h : ∀ a ∈ L, P a → q a) :
    (L.filter fun a => q a && !P a).length + (L.filter P).length = (L.filter q).length := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : P a <;> cases hq : q a <;> simp_all <;> omega

theorem length_filter_or {α : Type} (L : List α) (q P : α → Bool) (h : ∀ a ∈ L, P a → q a = false) :
    (L.filter fun a => q a || P a).length = (L.filter q).length + (L.filter P).length := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : P a <;> cases hq : q a <;> simp_all <;> omega

/-- The elements in a set of groups, counted group by group. -/
theorem length_filter_mem (s : Core) (L : List Nat) (u : List Nat) (hnd : u.Nodup) :
    (L.filter fun e => decide (eG s e ∈ u)).length = (u.map fun g => (runOf s L g).length).sum := by
  induction u with
  | nil => simp only [List.not_mem_nil, decide_false, List.filter_false, List.length_nil,
      List.map_nil, List.sum_nil]
  | cons g u ih =>
    simp only [List.nodup_cons] at hnd
    have := length_filter_or L (fun e => decide (eG s e ∈ u)) (fun e => decide (eG s e = g))
      (fun e _ he => by
        simp only [decide_eq_false_iff_not, decide_eq_true_eq] at he ⊢
        rw [he]
        exact hnd.1)
    simp only [List.map_cons, List.sum_cons]
    rw [← ih hnd.2]
    unfold runOf
    have e1 : (L.filter fun e => decide (eG s e ∈ g :: u)) =
        L.filter (fun e => decide (eG s e ∈ u) || decide (eG s e = g)) := by
      congr 1; funext e; simp only [List.mem_cons]; rw [Bool.or_comm]; simp only [Bool.decide_or]
    rw [e1, this]; omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The group invariant across a chunk-split move (invariant F) -/

theorem CMoveSpec.gfields {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) (g : Nat) :
    gSz s' g = gSz s g ∧ gSt s' g = gSt s g ∧ gSrc s' g = gSrc s g ∧ gLl s' g = gLl s g ∧
      gRr s' g = gRr s g ∧ gN s' g = gN s g ∧ gA s' g = gA s g ∧ gP s' g = gP s g ∧
      gF s' g = gF s g ∧ gLs s' g = gLs s g ∧
      gC s' g = (if g ∈ u then dst else gC s g) := by
  simp only [gSz, gSt, gSrc, gLl, gRr, gN, gA, gP, gF, gLs, gC, M.G g]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CMoveSpec.liveG {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) (g : Nat) : LiveG s' g ↔ LiveG s g := by
  simp only [LiveG, M.Gsize, (M.gfields g).2.2.2.2.2.2.1]

theorem CMoveSpec.runOf {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) (L : List Nat) (g : Nat) : runOf s' L g = runOf s L g := by
  unfold OrderMaintenance.Proof.runOf; simp only [eG, M.E]

theorem CMoveSpec.eL {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) : eL s' = eL s := by
  funext e; simp only [OrderMaintenance.Proof.eL, M.E]

/-- A set of groups closed under families. -/
def FamClosed (s : Core) (u : List Nat) : Prop :=
  ∀ p, LiveG s p → gSt s p = .splitting → (gLl s p ∈ u ↔ p ∈ u) ∧ (gRr s p ∈ u ↔ p ∈ u)

theorem ginv_cmove {s s' : Core} {L : List Nat} {gh : GGh} {δ : Nat → Nat} {ex x dst : Nat}
    {u labs : List Nat} (hG : GInvE s L gh δ ex) (M : CMoveSpec s s' x dst u labs)
    (hcl : FamClosed s u) : GInvE s' L gh δ ex := by
  have F := M.gfields
  have hL := M.liveG
  have hR := M.runOf L
  have hfam : ∀ p, famT s' p = famT s p := by
    intro p; simp only [famT, (F _).1, (F _).2.2.2.1, (F _).2.2.2.2.1]
  refine
    { sz := ?_, fam := ?_, ovf := ?_, notDead := ?_, quiet := ?_, split := ?_, gaps := ?_,
      range := ?_, ghQ := ?_, ghO := ?_, ghS := ?_ }
  · intro g hg; rw [hL] at hg; rw [(F g).1, hR]; exact hG.sz g hg
  · intro p hp hs
    rw [hL] at hp; rw [(F p).2.1] at hs
    have Fp := hG.fam p hp hs
    obtain ⟨c1, c2⟩ := hcl p hp hs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(F p).2.2.2.1, hL]; exact Fp.lLive
    · rw [(F p).2.2.2.2.1, hL]; exact Fp.rLive
    · rw [(F p).2.2.2.1, (F _).2.2.2.2.2.1]; exact Fp.lAdj
    · rw [(F p).2.2.2.2.1, (F p).2.2.2.2.2.1]; exact Fp.rAdj
    · rw [(F p).2.2.2.1, (F _).2.1]; exact Fp.lSt
    · rw [(F p).2.2.2.1, (F _).2.2.1]; exact Fp.lSrc
    · rw [(F p).2.2.2.2.1, (F _).2.1]; exact Fp.rSt
    · rw [(F p).2.2.2.2.1, (F _).2.2.1]; exact Fp.rSrc
    · rw [(F p).2.2.2.1, (F _).2.2.2.2.2.2.2.2.2.2, (F p).2.2.2.2.2.2.2.2.2.2]
      by_cases hpu : p ∈ u
      · rw [ite_eq_left (c1.mpr hpu), ite_eq_left hpu]
      · rw [ite_eq_right (fun h => hpu (c1.mp h)), ite_eq_right hpu]; exact Fp.lC
    · rw [(F p).2.2.2.2.1, (F _).2.2.2.2.2.2.2.2.2.2, (F p).2.2.2.2.2.2.2.2.2.2]
      by_cases hpu : p ∈ u
      · rw [ite_eq_left (c2.mpr hpu), ite_eq_left hpu]
      · rw [ite_eq_right (fun h => hpu (c2.mp h)), ite_eq_right hpu]; exact Fp.rC
  · intro g hg hs
    rw [hL] at hg; rw [(F g).2.1] at hs
    have := hG.ovf g hg hs
    rw [(F g).2.2.1, hL, (F _).2.1, (F _).2.2.2.1, (F _).2.2.2.2.1]; exact this
  · intro g hg; rw [hL] at hg; rw [(F g).2.1]; exact hG.notDead g hg
  · intro g hg hs
    rw [hL] at hg; rw [(F g).2.1] at hs
    rw [(F g).1, M.P, M.head, hR]; exact hG.quiet g hg hs
  · intro g hg hs hx
    rw [hL] at hg; rw [(F g).2.1] at hs
    have := hG.split g hg hs hx
    unfold G1 at this ⊢
    rw [M.P, (F g).2.2.2.1, (F g).2.2.2.2.1, (F _).1, (F g).1, (F _).1]; exact this
  · intro g hg; rw [hL] at hg; rw [hR, M.eL, M.P]; exact hG.gaps g hg
  · intro g hg e he; rw [hL] at hg; rw [hR] at he; rw [M.eL, M.P]; exact hG.range g hg e he
  · intro g hg hs; rw [hL] at hg; rw [(F g).2.1] at hs; rw [(F g).1, M.P]; exact hG.ghQ g hg hs
  · intro g hg hs; rw [hL] at hg; rw [(F g).2.1] at hs
    rw [(F g).1, M.P, (F g).2.2.1, hfam]; exact hG.ghO g hg hs
  · intro g hg hs; rw [hL] at hg; rw [(F g).2.1] at hs; rw [M.P, hfam]; exact hG.ghS g hg hs

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The chunk invariant across a chunk-split move -/

theorem units_erase1 {s s' : Core} {c c' a : Nat} (ha : UnitG s c a) (ha' : ¬ UnitG s' c' a)
    (h : ∀ g, g ≠ a → (UnitG s' c' g ↔ UnitG s c g)) : units s' c' + 1 = units s c := by
  unfold units
  have hS : (Finset.range s'.Gs.size).filter (UnitG s' c') =
      ((Finset.range s.Gs.size).filter (UnitG s c)).erase a := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    by_cases hg : g = a
    · subst hg; simp only [ne_eq, not_true_eq_false, false_and, iff_false]
      exact fun ⟨_, h'⟩ => ha' h'
    · simp only [ne_eq, hg, not_false_eq_true, true_and]
      constructor
      · rintro ⟨_, h'⟩; have := (h g hg).mp h'; exact ⟨this.1.2.1, this⟩
      · rintro ⟨_, h'⟩; have := (h g hg).mpr h'; exact ⟨this.1.2.1, this⟩
  rw [hS,
    Finset.card_erase_of_mem (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨ha.1.2.1,
    ha⟩)]
  have : 0 < ((Finset.range s.Gs.size).filter (UnitG s c)).card :=
    Finset.card_pos.mpr ⟨a, by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨ha.1.2.1,
      ha⟩⟩
  omega

theorem CFamOK.disjoint {s : Core} {x x' : Nat} (F : CFamOK s x) (F' : CFamOK s x') (hxx : x ≠ x')
    (hs : cSt s x = .splitting) (hs' : cSt s x' = .splitting) :
    x' ≠ cLl s x ∧ x' ≠ cRr s x ∧ cLl s x' ≠ x ∧ cRr s x' ≠ x ∧ cLl s x' ≠ cLl s x ∧
      cLl s x' ≠ cRr s x ∧ cRr s x' ≠ cLl s x ∧ cRr s x' ≠ cRr s x := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; have := F.lSt; rw [← e, hs'] at this; cases this
  · intro e; have := F.rSt; rw [← e, hs'] at this; cases this
  · intro e; have := F'.lSt; rw [e, hs] at this; cases this
  · intro e; have := F'.rSt; rw [e, hs] at this; cases this
  · intro e; have h1 := F'.lSrc; rw [e, F.lSrc] at h1; exact hxx h1
  · intro e; have h1 := F'.lSrc; rw [e, F.rSrc] at h1; exact hxx h1
  · intro e; have h1 := F'.rSrc; rw [e, F.lSrc] at h1; exact hxx h1
  · intro e; have h1 := F'.rSrc; rw [e, F.rSrc] at h1; exact hxx h1

theorem cinv_cmove {s s' : Core} {A : Abs} {gh : GGh} {δ δu s₀ : Nat → Nat} {x dst : Nat}
    {u labs : List Nat} (hG : GInv s A.elist gh (fun _ => 0))
    (hC : CInvE s A.elist δ δu s₀ x) (M : CMoveSpec s s' x dst u labs) (hxL : LiveC s x)
    (hst : cSt s x = .splitting) (hdst : dst = cLl s x ∨ dst = cRr s x) (hxd : x ≠ dst)
    (hu : ∀ g ∈ u, LiveG s g ∧ gC s g = x) (hnd : u.Nodup)
    (hone : ∃ um ∈ u, UnitG s x um ∧ ∀ g ∈ u, g ≠ um → gSt s g = .overflow) :
    CInvE s' A.elist δ δu s₀ x ∧ units s' x + 1 = units s x ∧
      (u.map fun g => gSz s g).sum ≤ cSz s x := by
  have F := M.gfields
  have Fx := hC.cfam x hxL hst
  have hdL : LiveC s dst := by
    rcases hdst with rfl | rfl
    · exact Fx.lLive
    · exact Fx.rLive
  have hdst' : cSt s dst = .overflow := by
    rcases hdst with rfl | rfl
    · exact Fx.lSt
    · exact Fx.rSt
  have hLC : ∀ c, LiveC s' c ↔ LiveC s c := by intro c; simp only [LiveC, M.Csize]
  -- counting the moved elements
  set moved := (u.map fun g => gSz s g).sum with hmoved
  have hP : (A.elist.filter fun e => decide (eG s e ∈ u)).length = moved := by
    rw [length_filter_mem s A.elist u hnd, hmoved]
    congr 1
    refine List.map_congr_left fun g hg => ?_
    rw [hG.sz g (hu g hg).1]
  have hPq : ∀ e ∈ A.elist, decide (eG s e ∈ u) = true → decide (gC s (eG s e) = x) = true := by
    intro e _ he; simp only [decide_eq_true_eq] at he ⊢; exact (hu _ he).2
  have hgC' : ∀ e, gC s' (eG s' e) = if eG s e ∈ u then dst else gC s (eG s e) := by
    intro e; simp only [eG, M.E]; exact (F _).2.2.2.2.2.2.2.2.2.2
  have hcx : (celts s' A.elist x).length + moved = (celts s A.elist x).length := by
    have := length_filter_split A.elist (fun e => decide (gC s (eG s e) = x))
      (fun e => decide (eG s e ∈ u)) hPq
    rw [hP] at this
    unfold celts
    rw [← this]
    congr 2
    refine List.filter_congr fun e _ => ?_
    rw [hgC']
    by_cases he : eG s e ∈ u
    · simp only [he, ↓reduceIte, Ne.symm hxd, decide_false, decide_true, Bool.not_true,
        Bool.and_false]
    · simp only [he, ↓reduceIte, decide_false, Bool.not_false, Bool.and_true]
  have hcd : (celts s' A.elist dst).length = (celts s A.elist dst).length + moved := by
    have := length_filter_or A.elist (fun e => decide (gC s (eG s e) = dst))
      (fun e => decide (eG s e ∈ u)) (fun e _ he => by
        simp only [decide_eq_true_eq, decide_eq_false_iff_not] at he ⊢; rw [(hu _ he).2]; exact hxd)
    rw [hP] at this
    unfold celts
    rw [← this]
    congr 1
    refine List.filter_congr fun e _ => ?_
    rw [hgC']
    by_cases he : eG s e ∈ u
    · simp only [he, ↓reduceIte, decide_true, Bool.or_true]
    · simp only [he, ↓reduceIte, decide_false, Bool.or_false]
  have hco : ∀ c, c ≠ x → c ≠ dst → celts s' A.elist c = celts s A.elist c := by
    intro c h1 h2
    unfold celts
    refine List.filter_congr fun e _ => ?_
    rw [hgC']
    by_cases he : eG s e ∈ u
    · simp only [he, ite_true]; rw [(hu _ he).2]; simp only [Ne.symm h2, decide_false,
        Ne.symm h1]
    · simp only [he, ↓reduceIte]
  have hle : moved ≤ cSz s x := by rw [hC.csz x hxL]; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hC.δu⟩, ?_, hle⟩
  · intro c hc
    rw [hLC] at hc
    rw [M.csz]
    by_cases h1 : c = x
    · subst h1; rw [ite_eq_left rfl, hC.csz c hc]; omega
    · by_cases h2 : c = dst
      · subst h2; rw [ite_eq_right h1, ite_eq_left rfl, hC.csz c hc, hcd]
      · rw [ite_eq_right h1, ite_eq_right h2, hco c h1 h2]; exact hC.csz c hc
  · intro y hy hys
    rw [hLC] at hy; rw [M.cst] at hys
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC.cfam y hy hys
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hLC, M.cl, M.cr, M.cnext, M.cst, M.csrc] <;> assumption
  · intro c hc hcs
    rw [hLC] at hc; rw [M.cst] at hcs
    have := hC.covf c hc hcs
    simp only [hLC, M.csrc, M.cst, M.cl, M.cr]; exact this
  · intro g hg
    rw [M.liveG] at hg
    rw [hLC, M.cst, (F g).2.2.2.2.2.2.2.2.2.2]
    split
    · rw [hdst']; exact ⟨hdL, by simp⟩
    · exact hC.gchk g hg
  · intro y hy hys hyx
    rw [hLC] at hy; rw [M.cst] at hys
    have Fy := hC.cfam y hy hys
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := Fx.disjoint Fy (Ne.symm hyx) hst hys
    have hyd : y ≠ dst := by
      rcases hdst with rfl | rfl
      · exact d1
      · exact d2
    have hly : cLl s y ≠ dst := by
      rcases hdst with rfl | rfl
      · exact d5
      · exact d6
    have hry : cRr s y ≠ dst := by
      rcases hdst with rfl | rfl
      · exact d7
      · exact d8
    have hu' : units s' y = units s y := by
      apply units_congr
      intro g
      unfold UnitG
      rw [M.liveG, (F g).2.2.2.2.2.2.2.2.2.2, (F g).2.1]
      split
      · next hgu => simp only [Ne.symm hyd, false_and, and_false, false_iff, not_and]
                    intro _ h; exact absurd ((hu g hgu).2 ▸ h) (Ne.symm hyx)
      · rfl
    have := hC.c1 y hy hys hyx
    unfold C1 at this ⊢
    rw [M.P, M.cl, M.cr, M.csz, M.csz, M.csz, ite_eq_right hyx, ite_eq_right hyd, ite_eq_right d3,
      ite_eq_right hly,
      ite_eq_right d4, ite_eq_right hry, hu']
    exact this
  · obtain ⟨um, hum, humU, hrest⟩ := hone
    refine units_erase1 humU ?_ ?_
    · intro h; have := h.2.1; rw [(F um).2.2.2.2.2.2.2.2.2.2, ite_eq_left hum] at this; exact
      hxd this.symm
    · intro g hg
      unfold UnitG
      rw [M.liveG, (F g).2.2.2.2.2.2.2.2.2.2, (F g).2.1]
      by_cases hgu : g ∈ u
      · rw [ite_eq_left hgu]
        simp only [Ne.symm hxd, false_and, and_false, false_iff, not_and]
        intro _ _; rw [hrest g hgu hg]; simp only [ne_eq, not_true_eq_false, not_false_eq_true]
      · rw [ite_eq_right hgu]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Chunk removal -/

theorem cremoveState_C {s : Core} {x : Nat} (hx : x < s.C.size) (hl : cLl s x < s.C.size)
    (hr : cRr s x < s.C.size) (hlx : cLl s x ≠ x) (hrx : cRr s x ≠ x) (c : Nat) :
    (cremoveState s x).C.getX c =
      if c = x then deadC (s.C.getX c)
      else if c = cLl s x ∨ c = cRr s x then quietC (s.C.getX c) else s.C.getX c := by
  simp only [cremoveState, Array.getX_modify, Array.size_modify']
  by_cases h1 : c = x
  · subst h1; simp only [hrx, false_and, ↓reduceIte, hlx, hx, and_self]
  · by_cases h2 : c = cLl s x
    · subst h2
      by_cases h3 : cLl s x = cRr s x
      · simp only [h3, hr, and_self, ↓reduceIte, quietC, Ne.symm hrx, false_and, hrx, or_self]
      · simp only [Ne.symm h3, false_and, ↓reduceIte, hl, and_self, Ne.symm h1, h1, h3, or_false]
    · by_cases h3 : c = cRr s x
      · subst h3; simp only [hr, and_self, ↓reduceIte, Ne.symm h2, false_and, Ne.symm h1, h1, h2,
          or_true]
      · simp only [Ne.symm h3, false_and, ↓reduceIte, Ne.symm h2, Ne.symm h1, h1, h2, h3,
          or_self]

theorem cinv_cremove {s : Core} {A : Abs} {δ δu s₀ : Nat → Nat} {x : Nat} (hI : INV s A)
    (hC : CInvE s A.elist δ δu s₀ x) (hxL : LiveC s x) (hst : cSt s x = .splitting)
    (he : cF s x = NIL)
    (hδ : ∀ c, c ≠ cLl s x → c ≠ x → c ≠ cRr s x → δ c = 0) :
    CInv (cremoveState s x) A.elist (fun _ => 0) (fun _ => 0) s₀ := by
  have Fx := hC.cfam x hxL hst
  have hlx : cLl s x ≠ x := by
    intro e; have := Fx.lAdj; rw [e] at this
    have hxm := (hI.cAlloc x).mpr hxL
    rw [hI.cList.next x hxm] at this
    exact succOf_ne_self hI.cList.nodup x (by unfold NIL; have := hxL.1; omega) this
  have hrx : cRr s x ≠ x := by
    intro e; have := Fx.rAdj; rw [e] at this
    have hxm := (hI.cAlloc x).mpr hxL
    rw [hI.cList.next x hxm] at this
    exact succOf_ne_self hI.cList.nodup x (by unfold NIL; have := hxL.1; omega) this
  have hC' := cremoveState_C hxL.2 Fx.lLive.2 Fx.rLive.2 hlx hrx
  have hLC : ∀ c, LiveC (cremoveState s x) c ↔ LiveC s c := by
    intro c; simp only [LiveC, cremoveState, Array.size_modify]
  have hsz : ∀ c, cSz (cremoveState s x) c = cSz s c := by
    intro c; simp only [cSz, hC']; split_ifs <;> rfl
  have hnext : ∀ c, cN (cremoveState s x) c = cN s c := by
    intro c; simp only [cN, hC']; split_ifs <;> rfl
  have hll : ∀ c, cLl (cremoveState s x) c = cLl s c := by
    intro c; simp only [cLl, hC']; split_ifs <;> rfl
  have hrr : ∀ c, cRr (cremoveState s x) c = cRr s c := by
    intro c; simp only [cRr, hC']; split_ifs <;> rfl
  have hstO : ∀ c, c ≠ x → c ≠ cLl s x → c ≠ cRr s x →
      cSt (cremoveState s x) c = cSt s c ∧ cSrc (cremoveState s x) c = cSrc s c := by
    intro c h1 h2 h3; simp only [cSt, cSrc, hC', ite_eq_right h1, ite_eq_right (not_or.mpr ⟨h2,
      h3⟩)]; simp only [and_self]
  have hstx : cSt (cremoveState s x) x = .dead := by simp only [cSt, hC', ↓reduceIte, deadC]
  have hstlr : ∀ c, c = cLl s x ∨ c = cRr s x → cSt (cremoveState s x) c = .quiet := by
    intro c hc
    have : c ≠ x := by
      rcases hc with rfl | rfl
      · exact hlx
      · exact hrx
    simp only [cSt, hC', this, ↓reduceIte, hc, quietC]
  have hG' : ∀ g, gC (cremoveState s x) g = gC s g := fun g => rfl
  -- no group lies in the emptied chunk
  have hnog : ∀ g, LiveG s g → gC s g ≠ x := by
    intro g hg hgx
    have hgm := hI.mem_glist_iff.mpr hg
    have hgx' := hI.mem_grps_of_chk hgm hgx
    have hxm := (hI.cAlloc x).mpr hxL
    have hE := (hI.cEnds x hxm).1
    rw [he] at hE
    cases h : A.grps x with
    | nil => rw [h] at hgx'; simp only [List.not_mem_nil] at hgx'
    | cons a t =>
      rw [h] at hE
      simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at hE
      exact hI.gList.nonil (hE ▸ A.grps_sub_glist hxm (h ▸ by simp))
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => le_rfl⟩
  · intro c hc; rw [hLC] at hc; rw [hsz]; unfold celts; simp only [hG', eG]
    exact hC.csz c hc
  · intro y hy hys
    rw [hLC] at hy
    by_cases h1 : y = x
    · subst h1; rw [hstx] at hys; cases hys
    · by_cases h2 : y = cLl s x ∨ y = cRr s x
      · rw [hstlr y h2] at hys; cases hys
      · rw [(hstO y h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))).1] at hys
        have Fy := hC.cfam y hy hys
        obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := Fx.disjoint Fy (Ne.symm h1) hst hys
        have := hstO (cLl s y) d3 d5 d6
        have := hstO (cRr s y) d4 d7 d8
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [hLC, hll, hrr, hnext, (hstO (cLl s y) d3 d5 d6).1, (hstO (cLl s y) d3 d5 d6).2,
            (hstO (cRr s y) d4 d7 d8).1, (hstO (cRr s y) d4 d7 d8).2]
        exacts [Fy.lLive, Fy.rLive, Fy.lAdj, Fy.rAdj, Fy.lSt, Fy.lSrc, Fy.rSt, Fy.rSrc]
  · intro c hc hcs
    rw [hLC] at hc
    by_cases h1 : c = x
    · subst h1; rw [hstx] at hcs; cases hcs
    · by_cases h2 : c = cLl s x ∨ c = cRr s x
      · rw [hstlr c h2] at hcs; cases hcs
      · obtain ⟨o1, o2⟩ := hstO c h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))
        rw [o1] at hcs
        obtain ⟨p1, p2, p3⟩ := hC.covf c hc hcs
        have hq : cSrc s c ≠ x := by
          intro e; rw [e] at p3; rcases p3 with p3 | p3 <;> [exact h2 (Or.inl p3.symm);
            exact h2 (Or.inr p3.symm)]
        have Fq := hC.cfam _ p1 p2
        obtain ⟨d1, d2, -, -, -, -, -, -⟩ := Fx.disjoint Fq (Ne.symm hq) hst p2
        rw [o2, hLC, (hstO _ hq d1 d2).1, hll, hrr]
        exact ⟨p1, p2, p3⟩
  · intro g hg
    rw [hG', hLC]
    obtain ⟨g1, g2⟩ := hC.gchk g hg
    refine ⟨g1, ?_⟩
    have hgx := hnog g hg
    by_cases h2 : gC s g = cLl s x ∨ gC s g = cRr s x
    · rw [hstlr _ h2]; simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    · rw [(hstO _ hgx (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))).1]; exact g2
  · intro y hy hys _
    rw [hLC] at hy
    by_cases h1 : y = x
    · subst h1; rw [hstx] at hys; cases hys
    · by_cases h2 : y = cLl s x ∨ y = cRr s x
      · rw [hstlr y h2] at hys; cases hys
      · rw [(hstO y h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))).1] at hys
        have Fy := hC.cfam y hy hys
        obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := Fx.disjoint Fy (Ne.symm h1) hst hys
        have := hC.c1 y hy hys h1
        have hu : units (cremoveState s x) y = units s y := units_congr fun g => Iff.rfl
        unfold C1 at this ⊢
        rw [hδ _ d5 d3 d6, hδ _ (fun e => h2 (Or.inl e)) h1 (fun e => h2 (Or.inr e)),
          hδ _ d7 d4 d8] at this
        have hδu : δu y = 0 := by
          have := hC.δu y
          rw [hδ _ (fun e => h2 (Or.inl e)) h1 (fun e => h2 (Or.inr e))] at this; omega
        rw [hδu] at this
        have hP : (cremoveState s x).P = s.P := rfl
        simp only [hsz, hll, hrr, hu, hP]
        simpa using this

end OrderMaintenance.Proof
