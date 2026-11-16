/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.InsTime
public import LeanPool.OrderMaintenance.Proof.Cost.Wrap


/-!
# M5: the contract's `start` — a chunk split's job begins

`insertAround x y z` on the core with `y`, `z` linked around `x` succeeds (its two tag writes pass
their guards, by Lemma T1 on the order after the split), and the marked state satisfies `TopInv`
with the job at its first copy step.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- The contract's chunk capacity: nodes of height `H - 1` never drain. -/
def capT (P : Params) : Nat := Wd P (P.H - 1) - 1

/-- What `linkChunkPair` needs, from INV-S (as in `inv_splitChunk`). -/
theorem linkCOK_push2 {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hx : x ∈ A.chunks) :
    LinkCOK (push2 s) x s.C.size (s.C.size + 1) ∧ cP (push2 s) x = cP s x ∧
      cN (push2 s) x = cN s x := by
  generalize hydef : s.C.size = y
  have hxs : x < y := hydef ▸ ((hI.cAlloc x).mp hx).2
  have h1C : ∀ w, (push2 s).C.getX w = if w = y ∨ w = y + 1 then {} else s.C.getX w := by
    intro w
    simp only [push2, Array.getX_push, Array.size_push, hydef]
    by_cases h1 : w = y + 1
    · simp [h1]
    · by_cases h2 : w = y
      · simp [h2]
      · simp [h1, h2]
  have hcnd := hI.cList.nodup
  generalize hpdef : cP s x = p
  generalize hndef : cN s x = n
  have hpm : p = NIL ∨ p ∈ A.chunks := by
    rw [← hpdef, hI.cList.prev x hx]
    rcases predOf_mem_or (l := A.chunks) (x := x) with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hnm : n = NIL ∨ n ∈ A.chunks := by
    rw [← hndef, hI.cList.next x hx]
    rcases succOf_mem_or (l := A.chunks) (x := x) with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hmem_lt : ∀ c ∈ A.chunks, c < y := fun c hc => hydef ▸ ((hI.cAlloc c).mp hc).2
  have hp1 : cP (push2 s) x = p := by
    simp only [cP, h1C, show x ≠ y by omega, show x ≠ y + 1 by omega]; simp [hpdef]
  have hn1 : cN (push2 s) x = n := by
    simp only [cN, h1C, show x ≠ y by omega, show x ≠ y + 1 by omega]; simp [hndef]
  have hlt : ∀ c, c = NIL ∨ c ∈ A.chunks → c < y := by
    intro c hc; rcases hc with h | h
    · rw [h]; unfold NIL; omega
    · exact hmem_lt c h
  have hpy : p < y := hlt p hpm
  have hny : n < y := hlt n hnm
  have hx1 : 1 ≤ x := ((hI.cAlloc x).mp hx).1
  have hpx : p ≠ x := by
    rw [← hpdef, hI.cList.prev x hx]
    exact predOf_ne_self hcnd x (by unfold NIL; omega)
  have hnx : n ≠ x := by
    rw [← hndef, hI.cList.next x hx]
    exact succOf_ne_self hcnd x (by unfold NIL; omega)
  have hpn : p ≠ NIL → p ≠ n := by
    intro h0; rw [← hpdef, ← hndef, hI.cList.prev x hx, hI.cList.next x hx]
    exact predOf_ne_succOf hcnd hx (by rw [← hI.cList.prev x hx, hpdef]; exact h0)
  have h1sz : (push2 s).C.size = y + 2 := by simp [push2, hydef]
  refine ⟨⟨by omega, by omega, by omega, fun h => by rw [hp1] at h ⊢; omega,
      fun h => by rw [hn1] at h ⊢; omega, by omega, by omega, by omega,
      by rw [hp1]; omega, by rw [hp1]; omega, by rw [hn1]; omega, by rw [hn1]; omega,
      by rw [hp1]; exact hpx, by rw [hn1]; exact hnx, fun h => by rw [hp1, hn1] at *; exact hpn h⟩,
    hp1, hn1⟩

theorem idx?_some_of_mem {l : List Nat} {a : Nat} (ha : a ∈ l) : ∃ i, l.idx? a = some i := by
  cases h : l.idx? a with
  | none =>
    exfalso
    unfold List.idx? at h
    rw [List.findIdx?_eq_none_iff] at h
    have := h a ha; simp at this
  | some i => exact ⟨i, rfl⟩

theorem lookup_some_of_mem {l : List (Nat × Nat)} {k : Nat} (hk : k ∈ l.map (·.1)) :
    ∃ v, lookup l k = some v := by
  obtain ⟨⟨a, b⟩, hm, rfl⟩ := List.mem_map.mp hk
  unfold lookup
  cases h : List.find? (fun p => p.1 == a) l with
  | none =>
    rw [List.find?_eq_none] at h
    have := h _ hm; simp at this
  | some p => exact ⟨p.2, rfl⟩

theorem before_app_l {L R : List Nat} {a b : Nat} (ha : a ∈ L) : Before (L ++ b :: R) a b :=
  (List.singleton_sublist.mpr ha).append ((List.nil_sublist R).cons_cons b)

theorem before_app_r {L R : List Nat} {a b : Nat} (hb : b ∈ R) : Before (L ++ a :: R) a b :=
  ((List.singleton_sublist.mpr hb).cons_cons a).trans (List.sublist_append_right L _)

theorem cN_markState (t : Core) (x y z : Nat) (j : Job) (c : Nat) :
    cN (markState t x y z j) c = cN t c := by
  unfold cN markState; simp only [Array.getX_modify]; split_ifs <;> rfl
theorem cP_markState (t : Core) (x y z : Nat) (j : Job) (c : Nat) :
    cP (markState t x y z j) c = cP t c := by
  unfold cP markState; simp only [Array.getX_modify]; split_ifs <;> rfl

/-- An insertion invariant supplies a valid completed-copy frame and distinct containing tables. -/
theorem insFin_frame_of_invariant {s : Core} {cl : List Nat} {ord : Nat → List Nat}
    {dr n0 : Nat → Nat} {x f1x i1 : Nat} (hI : InvJ (ts s) cl ord dr n0 none)
    (hx : x ∈ cl) (hxs : x < s.C.size) :
    InsFrame s x f1x i1 (insFin s x f1x i1) ∧ (s.cin.getX x).Nodup := by
  have S := hI.shape
  have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
  have hnd : (s.cin.getX x).Nodup := by
    have := S.tabsNodup 0 x hent; unfold tabs at this; rw [ite_eq_left rfl] at this; exact this
  have hdist : ∀ i i', 1 ≤ i → i ≤ s.P.H → 1 ≤ i' → i' ≤ s.P.H → pth (ts s) x i = pth (ts s) x i' →
      i = i' := by
    intro i i' h1 h2 h1' h2' e
    have a := (ins_pp_ht hI hx h1 h2).2
    have b := (ins_pp_ht hI hx h1' h2').2
    unfold pp at a b; rw [ite_eq_right (by omega)] at a; rw [ite_eq_right (by omega)] at b
    rw [e] at a; omega
  have hex : ∀ i, 1 ≤ i → i ≤ s.P.H → pth (ts s) x i < s.nodes.size := by
    intro i h1 h2
    have a := (ins_pp_ht hI hx h1 h2).1
    unfold pp at a; rw [ite_eq_right (by omega)] at a; exact a.2.1
  exact ⟨insFin_frame s x f1x i1 hxs hnd hdist hex, hnd⟩

/-- The inserted and retained chunk tags agree with the completed tree interpretation. -/
theorem ins_tag_interpretation {s : Core} {cl : List Nat} {ord : Nat → List Nat}
    {dr n0 : Nat → Nat} {x f1x i1 : Nat} {t : TS} (hI : InvJ (ts s) cl ord dr n0 none)
    (hC : ∀ c, c ∈ cl ↔ 1 ≤ c ∧ c < s.C.size) (hx : x ∈ cl)
    (F : InsFrame s x f1x i1 t) (hTP : TopParams s.P) (hf1 : f1x = digit (ts s) x 1)
    (hi1 : (s.cin.getX x).idx? (pp (ts s) x 1) = some i1) :
    tagY (ins0 s x) x f1x i1 = tagF t s.C.size ∧
      tagZ (ins0 s x) x f1x i1 = tagF t (s.C.size + 1) ∧
      ∀ c ∈ cl, cT (ins0 s x) c = tagF t c := by
  have htags := ins_tags hI hC hx F hTP hf1 hi1
  obtain ⟨Al, Bl, hcl1, -, -, hcl'⟩ := ins_cl hI hC hx
  have hmem' : ∀ c, c ∈ clIns cl x s.C.size (s.C.size + 1) ↔
      c ∈ cl ∨ c = s.C.size ∨ c = s.C.size + 1 := by
    intro c; rw [hcl', hcl1]; simp only [List.mem_append, List.mem_cons]; tauto
  have hty : tagY (ins0 s x) x f1x i1 = tagF (t) s.C.size := by
    have := htags s.C.size ((hmem' _).mpr (Or.inr (Or.inl rfl)))
    rw [F.tag, ite_eq_right (by omega), ite_eq_left rfl] at this; exact this
  have htz : tagZ (ins0 s x) x f1x i1 = tagF (t) (s.C.size + 1) := by
    have := htags (s.C.size + 1) ((hmem' _).mpr (Or.inr (Or.inr rfl)))
    rw [F.tag, ite_eq_left rfl] at this; exact this
  have hto : ∀ c ∈ cl, cT (ins0 s x) c = tagF (t) c := by
    intro c hc
    have hcs := (hC c).mp hc
    have := htags c ((hmem' _).mpr (Or.inl hc))
    rw [F.tag, ite_eq_right (by omega), ite_eq_right (by omega)] at this
    unfold cT; rw [ins0_tag s x hcs.2, this]
  exact ⟨hty, htz, hto⟩

/-- A table holds at most 160 entries, and so does a side list (`TabLen`). -/
theorem tab_le_160 {t : TS} {dr n0 : Nat → Nat} (h : TabLen t dr n0) (X : Nat) :
    (nd t X).table.length ≤ 160 ∧ (nd t X).side.length ≤ 160 := by
  obtain ⟨a, b, c⟩ := h X
  have : (Top.order t X).length = (nd t X).table.length := by simp [Top.order, Node.order]
  omega

/-- **The hypotheses of `insertAround` at a split start** (those of `insertAround_run`, and the
facts the Level M program needs), from the top invariant. -/
theorem ins_start_guards {s : Core} {A : Abs} {x f1x i1 : Nat} (hA : INV s A) (hT : TopInv s)
    (hres : s.resJob = none) (hxL : LiveC s x)
    (hf1 : f1x = digit (ts s) x 1)
    (hi1 : (s.cin.getX x).idx? ((s.path.getX x).getX 1) = some i1) :
    (∀ T ∈ (ins0 s x).cin.getX x, RoomOK (ins0 s x) x T) ∧ (s.cin.getX x).Nodup ∧
      ((ins0 s x).nodes.getX (((ins0 s x).path.getX x).getX 1)).lab? x = some f1x ∧
      (s.cin.getX x).idx? ((s.path.getX x).getX 1) = some i1 ∧
      f1x ≤ ((ins0 s x).C.getX x).tag ∧
      x ∈ ((ins0 s x).nodes.getX ((ins0 s x).lpar.getX x)).children ∧
      TagOK (ins0 s x) s.C.size (tagY (ins0 s x) x f1x i1) ∧
      TagOK {
        (ins0 s x) with
        C := (ins0 s x).C.modify s.C.size fun C => {
          C with
          tag := tagY (ins0 s x) x f1x i1
        }
      }
        (s.C.size + 1) (tagZ (ins0 s x) x f1x i1) ∧
      cP (ins0 s x) s.C.size < s.C.size ∧ cN (ins0 s x) s.C.size < s.C.size + 2 ∧
      cP (ins0 s x) (s.C.size + 1) < s.C.size + 2 ∧ cN (ins0 s x) (s.C.size + 1) < s.C.size ∧
      (∀ T ∈ s.cin.getX x, T < s.nodes.size ∧ (s.nodes.getX T).table.length ≤ 160 ∧
        (s.nodes.getX T).side.length ≤ 160) ∧
      (s.cin.getX x).length ≤ 2 ∧ s.lpar.getX x < s.nodes.size ∧
      (s.nodes.getX (s.lpar.getX x)).children.length ≤ 160 ∧ x < s.C.size ∧ x ≠ NIL := by
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hT
  rw [hres] at hI
  change InvJ (ts s) cl ord dr n0 none at hI
  have S := hI.shape
  have h3 : 3 ≤ s.P.H := S.H3
  have hx : x ∈ cl := (hC x).mpr hxL
  have hxs : x < s.C.size := hxL.2
  have hcl : cl = A.chunks := NList.unique hL.nlist hA.cList.nlist
  have hxA : x ∈ A.chunks := hcl ▸ hx
  have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
  -- the split's data
  obtain ⟨F, hnd⟩ := insFin_frame_of_invariant (f1x := f1x) (i1 := i1) hI hx hxs
  have SH := ins_shape hI hC hx F hTP hf1 hi1
  have T1 : ∀ c d, Before (clIns cl x s.C.size (s.C.size + 1)) c d →
      tagF (insFin s x f1x i1) c < tagF (insFin s x f1x i1) d := fun c d h => SH.toShapeT.tagF_lt h
  obtain ⟨Al, Bl, hcl1, hA1, hB1, hcl'⟩ := ins_cl hI hC hx
  obtain ⟨hty, htz, hto⟩ := ins_tag_interpretation hI hC hx F hTP hf1 hi1
  have hnd1 : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  -- the links around the new chunks
  obtain ⟨hLk, hp2, hn2⟩ := linkCOK_push2 hA hxA
  have hpx : cP s x = Al.getLastD NIL := by
    rw [hA.cList.prev x hxA, ← hcl, hcl1, predOf_mid (hcl1 ▸ hnd1)]
  have hnx : cN s x = Bl.headD NIL := by
    rw [hA.cList.next x hxA, ← hcl, hcl1, succOf_mid (hcl1 ▸ hnd1)]
  have hyx : s.C.size ≠ x := by omega
  have cPy : cP (ins0 s x) s.C.size = Al.getLastD NIL := by
    unfold ins0; rw [hLk.cP', ite_eq_right hyx, ite_eq_left rfl, hp2, hpx]
  have cNy : cN (ins0 s x) s.C.size = x := by
    unfold ins0; rw [hLk.cN', ite_eq_right hyx, ite_eq_left rfl]
  have cPz : cP (ins0 s x) (s.C.size + 1) = x := by
    unfold ins0; rw [hLk.cP', ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  have cNz : cN (ins0 s x) (s.C.size + 1) = Bl.headD NIL := by
    unfold ins0; rw [hLk.cN', ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl,
      hn2, hnx]
  have hgy : TagOK (ins0 s x) s.C.size (tagY (ins0 s x) x f1x i1) := by
    refine ⟨fun hp => ?_, fun _ => ?_⟩
    · rw [cPy] at hp ⊢
      have hAl : Al ≠ [] := by rintro rfl; exact hp rfl
      have hm := getLastD_mem hAl NIL
      rw [hto _ (by
        rw [hcl1]
        exact List.mem_append_left _ hm), hty]
      apply T1; rw [hcl']; exact before_app_l hm
    · rw [cNy, hto x hx, hty]
      apply T1; rw [hcl', show Al ++ s.C.size :: x :: (s.C.size + 1) :: Bl =
        (Al ++ [s.C.size]) ++ x :: (s.C.size + 1) :: Bl by simp]
      exact before_app_l (by simp)
  have hgz : TagOK {
    (ins0 s x) with
    C := (ins0 s x).C.modify s.C.size fun C => {
      C with
      tag := tagY (ins0 s x) x f1x i1
    }
  }
      (s.C.size + 1) (tagZ (ins0 s x) x f1x i1) := by
    have eP : ∀ c, cP {
      (ins0 s x) with
      C := (ins0 s x).C.modify s.C.size fun C => {
        C with
        tag := tagY (ins0 s x) x f1x i1
      }
    } c =
        cP (ins0 s x) c := fun c => by unfold cP; simp only [Array.getX_modify]; split_ifs <;> rfl
    have eN : ∀ c, cN {
      (ins0 s x) with
      C := (ins0 s x).C.modify s.C.size fun C => {
        C with
        tag := tagY (ins0 s x) x f1x i1
      }
    } c =
        cN (ins0 s x) c := fun c => by unfold cN; simp only [Array.getX_modify]; split_ifs <;> rfl
    have eT : ∀ c, c ≠ s.C.size → cT {
      (ins0 s x) with
      C := (ins0 s x).C.modify s.C.size fun C => {
        C with
        tag := tagY (ins0 s x) x f1x i1
      }
    } c =
        cT (ins0 s x) c := fun c hc => by
      unfold cT; simp only [Array.getX_modify, Ne.symm hc, false_and, ite_false]
    refine ⟨fun _ => ?_, fun hn => ?_⟩
    · rw [eP, cPz, eT x (by omega), hto x hx, htz]
      apply T1; rw [hcl', show Al ++ s.C.size :: x :: (s.C.size + 1) :: Bl =
        (Al ++ [s.C.size]) ++ x :: (s.C.size + 1) :: Bl by simp]
      exact before_app_r (by simp)
    · rw [eN, cNz] at hn ⊢
      have hBl : Bl ≠ [] := by rintro rfl; exact hn rfl
      have hm := headD_mem hBl NIL
      have hmc : Bl.headD NIL ∈ cl := by
        rw [hcl1]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
      have hcs := (hC _).mp hmc
      rw [eT _ (by omega), hto _ hmc, htz]
      apply T1; rw [hcl', show Al ++ s.C.size :: x :: (s.C.size + 1) :: Bl =
        (Al ++ [s.C.size, x]) ++ (s.C.size + 1) :: Bl by simp]
      exact before_app_r hm
  -- the run
  have hroom : ∀ T ∈ (ins0 s x).cin.getX x, RoomOK (ins0 s x) x T := by
    intro T hT
    obtain ⟨A', le, Bs, htab, hA', hside, h1, h2, -, -⟩ :=
      start_room hI hTP hx (T := T) hT s.C.size (s.C.size + 1)
    exact ⟨A', le, Bs, htab, hA', hside, h1, h2⟩
  have hw : x ∈ (nd (ts s) (pp (ts s) x 1)).table.map (·.1) :=
    S.W3 x hx 1 le_rfl (by
      have := S.H3
      omega)
  obtain ⟨v, hv⟩ := lookup_some_of_mem hw
  have hfv : f1x = v := by
    rw [hf1]; unfold digit
    change ((nd (ts s) (pp (ts s) x 1)).lab? x).getD 0 = v
    unfold Node.lab?; rw [hv]; rfl
  have hf1' : ((ins0 s x).nodes.getX (((ins0 s x).path.getX x).getX 1)).lab? x = some f1x := by
    rw [hfv]; exact hv
  have htx : f1x ≤ ((ins0 s x).C.getX x).tag := by
    rw [ins0_tag s x hxs, show (s.C.getX x).tag = (ts s).tag x from rfl, S.tags x hx, hf1,
      ← tagUp_one]
    exact tagUp_mono _ _ _ _ (by
      have := S.H3
      omega)
  have hlp : x ∈ ((ins0 s x).nodes.getX ((ins0 s x).lpar.getX x)).children := (S.lp x hx).2.2
  -- the exported facts
  have hTL := tab_le_160 hI.len
  have hlpx := S.lp x hx
  have hlpl : (s.nodes.getX (s.lpar.getX x)).children.length ≤ 160 := by
    obtain ⟨-, hsub', -⟩ := S.kids _ hlpx.1
    have h2 := (sublist_of_subset_common hsub' (S.O1 _ hlpx.1.1) (S.ordNodup _)
      (fun e he => S.kid_mem hI.time hlpx.1 he)).length_le
    have hl2 := (hTL (lpr (ts s) x)).1
    change (nd (ts s) (lpr (ts s) x)).children.length ≤ 160
    simp only [Top.order, Node.order, List.length_map] at h2; omega
  have hcinT : ∀ T ∈ s.cin.getX x, T < s.nodes.size := by
    intro T hT
    have := S.tabsIff 0 x T hent
    unfold tabs at this; rw [ite_eq_left rfl] at this
    exact (this.mp hT).1.2.1
  have hcl2 : (s.cin.getX x).length ≤ 2 := by
    have := S.tabs_len hent; unfold tabs at this; rw [ite_eq_left rfl] at this; exact this
  have hlt : ∀ c ∈ cl, c < s.C.size := fun c hc => ((hC c).mp hc).2
  refine ⟨hroom, hnd, hf1', hi1, htx, hlp, hgy, hgz, ?_, ?_, ?_, ?_,
    fun T hT => ⟨hcinT T hT, (hTL T).1, (hTL T).2⟩, hcl2, hlpx.1.1.2.1, hlpl, hxs, ?_⟩
  · rw [cPy]
    rcases List.eq_nil_or_concat Al with h | ⟨L, b, h⟩
    · rw [h]; simp [NIL]; omega
    · have hm : Al.getLastD NIL ∈ cl := by
        rw [hcl1]; exact List.mem_append_left _ (getLastD_mem (by
          rw [h]
          simp) NIL)
      exact hlt _ hm
  · rw [cNy]; omega
  · rw [cPz]; omega
  · rw [cNz]
    rcases Bl with _ | ⟨b, Bl'⟩
    · simp [NIL]; omega
    · have hm : b ∈ cl := by rw [hcl1]; simp
      exact hlt _ hm
  · exact fun h => hL.nonil (h ▸ hx)

/-- **The hypotheses of `insertAround` at a split start** (those of `insertAround_run`, and the
facts the Level M program needs), from the top invariant. -/
theorem ins_hyps {s : Core} {A : Abs} {x : Nat} (hA : INV s A) (hT : TopInv s)
    (hres : s.resJob = none) (hxL : LiveC s x) :
    ∃ f1x i1, (∀ T ∈ (ins0 s x).cin.getX x, RoomOK (ins0 s x) x T) ∧ (s.cin.getX x).Nodup ∧
      ((ins0 s x).nodes.getX (((ins0 s x).path.getX x).getX 1)).lab? x = some f1x ∧
      (s.cin.getX x).idx? ((s.path.getX x).getX 1) = some i1 ∧
      f1x ≤ ((ins0 s x).C.getX x).tag ∧
      x ∈ ((ins0 s x).nodes.getX ((ins0 s x).lpar.getX x)).children ∧
      TagOK (ins0 s x) s.C.size (tagY (ins0 s x) x f1x i1) ∧
      TagOK {
        (ins0 s x) with
        C := (ins0 s x).C.modify s.C.size fun C => {
          C with
          tag := tagY (ins0 s x) x f1x i1
        }
      }
        (s.C.size + 1) (tagZ (ins0 s x) x f1x i1) ∧
      cP (ins0 s x) s.C.size < s.C.size ∧ cN (ins0 s x) s.C.size < s.C.size + 2 ∧
      cP (ins0 s x) (s.C.size + 1) < s.C.size + 2 ∧ cN (ins0 s x) (s.C.size + 1) < s.C.size ∧
      (∀ T ∈ s.cin.getX x, T < s.nodes.size ∧ (s.nodes.getX T).table.length ≤ 160 ∧
        (s.nodes.getX T).side.length ≤ 160) ∧
      (s.cin.getX x).length ≤ 2 ∧ s.lpar.getX x < s.nodes.size ∧
      (s.nodes.getX (s.lpar.getX x)).children.length ≤ 160 ∧ x < s.C.size ∧ x ≠ NIL := by
  have hT0 := hT
  obtain ⟨-, cl, ord, dr, n0, -, hC, hI⟩ := hT
  rw [hres] at hI
  change InvJ (ts s) cl ord dr n0 none at hI
  have hx : x ∈ cl := (hC x).mpr hxL
  obtain ⟨i1, hi1⟩ := idx?_some_of_mem (ins_pp1 hI hx)
  exact ⟨digit (ts s) x 1, i1, ins_start_guards hA hT0 hres hxL rfl hi1⟩

/-- **The contract's `start`.** -/
theorem length_assocSet_le {β : Type} (l : List (Nat × β)) (k : Nat) (v : β) :
    (assocSet l k v).length ≤ l.length + 1 := by
  unfold assocSet; split <;> simp

theorem length_aroundT_le (tab : List (Nat × Nat)) (e n1 n2 a b : Nat) :
    (aroundT tab e n1 n2 a b).length ≤ tab.length + 2 := by
  unfold aroundT; simp only [List.length_insertIdx]; split <;> split <;> omega

theorem length_sideAround_le (T : Node) (e n1 n2 : Nat) :
    (sideAround T e n1 n2).length ≤ T.side.length + 2 := by
  unfold sideAround; split
  · have h1 := length_assocSet_le T.side n1 ((lookup T.side e).getD .left)
    have h2 := length_assocSet_le (assocSet T.side n1 ((lookup T.side e).getD .left)) n2
      ((lookup T.side e).getD .left)
    omega
  · omega

theorem top_start {s : Core} {A : Abs} {x : Nat} (hA : INV s A) (hT : TopInv s)
    (hres : s.resJob = none) (hxL : LiveC s x) (hcap : s.C.size + 2 ≤ capT s.P) :
    ∃ job s2, (insertAround x s.C.size (s.C.size + 1)).run
        (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) = .ok job s2 ∧
      1 ≤ topMu (markState s2 x s.C.size (s.C.size + 1) job) ∧
      topMu (markState s2 x s.C.size (s.C.size + 1) job) ≤ topJ s.P ∧
      TopInv (markState s2 x s.C.size (s.C.size + 1) job) := by
  have hT0 := hT
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hT
  rw [hres] at hI
  change InvJ (ts s) cl ord dr n0 none at hI
  have S := hI.shape
  have h3 : 3 ≤ s.P.H := S.H3
  have hx : x ∈ cl := (hC x).mpr hxL
  have hxs : x < s.C.size := hxL.2
  have hcl : cl = A.chunks := NList.unique hL.nlist hA.cList.nlist
  have hxA : x ∈ A.chunks := hcl ▸ hx
  have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
  -- the split's data
  have hT1 := ins_pp1 hI hx
  obtain ⟨i1, hi1⟩ := idx?_some_of_mem hT1
  set f1x := digit (ts s) x 1 with hf1
  obtain ⟨F, hnd⟩ := insFin_frame_of_invariant (f1x := f1x) (i1 := i1) hI hx hxs
  have SH := ins_shape hI hC hx F hTP rfl hi1
  obtain ⟨Al, Bl, hcl1, hA1, hB1, hcl'⟩ := ins_cl hI hC hx
  have hmem' : ∀ c, c ∈ clIns cl x s.C.size (s.C.size + 1) ↔ c ∈ cl ∨ c = s.C.size ∨ c =
    s.C.size + 1 := by
    intro c; rw [hcl', hcl1]; simp only [List.mem_append, List.mem_cons]; tauto
  have hnd1 : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  have hyx : s.C.size ≠ x := by omega
  obtain ⟨hroom, -, hf1', -, htx, hlp, hgy, hgz, -, -, -, -, -, -, -, -, -, -⟩ :=
    ins_start_guards (f1x := f1x) (i1 := i1) hA hT0 hres hxL rfl hi1
  have hrun := insertAround_run (s := ins0 s x) (x := x) (y := s.C.size) (z := s.C.size + 1)
    (f1x := f1x) (i1 := i1) hroom hnd hyx hf1' hi1 htx hlp hgy hgz
  refine ⟨insJob s x, ins3 s x f1x i1, hrun, ?_⟩
  -- the marked state
  have hts : ts (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)) =
      ts (ins3 s x f1x i1) := ts_markState _ _ _ _ _
  have hP' : (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)).P = s.P :=
    ins3_P s x f1x i1
  have hmu : topMu (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)) =
      (s.P.H + 1 - 1) + walkLeft s.P 1 := by
    change jobLeft (ts (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)))
      (insJob s x) = _
    rw [hts]
    change ((ts (ins3 s x f1x i1)).P.H + 1 - 1) + walkLeft (ts (ins3 s x f1x i1)).P 1 = _
    rw [ts_P, ins3_P]
  have hfin : finS (ts (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)))
      (some (insJob s x)) = insFin s x f1x i1 := by
    rw [hts]
    change copyRest (insJob s x) (ts (ins3 s x f1x i1)).P.H (ts (ins3 s x f1x i1)) 1 = _
    rw [ts_P, ins3_P]; rfl
  refine ⟨by rw [hmu]; unfold walkLeft; omega, by rw [hmu]; unfold topJ walkLeft; omega, ?_⟩
  -- the invariant
  have hW := inv_splitChunk hA hxA hgy hgz
  have eN : cN (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)) =
      cN (withTag (withTag (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s.C.size
        (tagY (ins0 s x) x f1x i1)) (s.C.size + 1) (tagZ (ins0 s x) x f1x i1)) := by
    funext c; rw [cN_markState]; unfold cN; rw [ins3_eq, insFinS_C]; rfl
  have eP : cP (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)) =
      cP (withTag (withTag (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s.C.size
        (tagY (ins0 s x) x f1x i1)) (s.C.size + 1) (tagZ (ins0 s x) x f1x i1)) := by
    funext c; rw [cP_markState]; unfold cP; rw [ins3_eq, insFinS_C]; rfl
  have eF : (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)).firstChunk =
      (withTag (withTag (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s.C.size
        (tagY (ins0 s x) x f1x i1)) (s.C.size + 1) (tagZ (ins0 s x) x f1x i1)).firstChunk := by
    unfold markState; rw [ins3_eq]; unfold insFinS joinS; rfl
  have hch : (A.splitChunk x s.C.size (s.C.size + 1)).chunks = clIns cl x s.C.size (s.C.size +
    1) := by
    unfold Abs.splitChunk clIns; rw [hcl]
  have hsz : (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)).C.size =
      s.C.size + 2 := by
    unfold markState; simp only [Array.size_modify']
    rw [ins3_eq, insFinS_C, (tagsS_top (ins0 s x) _ _ _ _).2.2.2.2.2]
    simp only [Array.size_modify']; exact (ins0_top s x).2.2.2.2.2
  have hlen : cl.length = s.C.size - 1 := by
    rw [length_eq_of_mem_iff hnd1 List.nodup_range' (l' := List.range' 1 (s.C.size - 1))]
    · simp
    · intro c; rw [hC c, List.mem_range'_1]; omega
  refine ⟨by rw [hP']; exact hTP, clIns cl x s.C.size (s.C.size + 1),
    ordIns ord cl x s.C.size (s.C.size + 1), drIns dr (s.cin.getX x), n0, ?_, fun c => ?_, ?_⟩
  · rw [eN, eP, eF, ← hch]; exact hW.cList
  · rw [hmem', hsz, hC]; omega
  · change InvJ (finS (ts (markState (ins3 s x f1x i1) x s.C.size (s.C.size + 1) (insJob s x)))
      (some (insJob s x))) _ _ _ _ (some (insJob s x))
    rw [hfin]
    have hcap' : (clIns cl x s.C.size (s.C.size + 1)).length + 2 ≤
        Wd (insFin s x f1x i1).P ((insFin s x f1x i1).P.H - 1) := by
      rw [F.P, hcl', List.length_append, List.length_cons, List.length_cons, List.length_cons]
      rw [hcl1, List.length_append, List.length_cons] at hlen
      unfold capT at hcap
      omega
    have hTi := ins_time hI hC hx F hTP
    have hRo := ins_room hI hC hx F hTP
    have hTP' : TopParams (insFin s x f1x i1).P := by rw [F.P]; exact hTP
    have hTL : TabLen (insFin s x f1x i1) (drIns dr (s.cin.getX x)) n0 := by
      intro X
      obtain ⟨a, b, c⟩ := hI.len X
      by_cases hX : X ∈ s.cin.getX x
      · have hXT := (S.tabsIff 0 x X hent).mp (by unfold tabs; rw [ite_eq_left rfl]; exact hX)
        have hXN := hXT.1
        have hsz : X < s.nodes.size := hXN.2.1
        have hXN' : isN (insFin s x f1x i1) X :=
          ⟨hXN.1, by rw [F.size]; exact hsz, by rw [F.alive]; exact hXN.2.2⟩
        have hb := hRo.len_le SH hTi hTP' hcap' hXN'
        unfold drIns at hb ⊢; rw [ite_eq_left hX] at hb ⊢
        unfold order Node.order at a ⊢
        rw [F.table X, F.side X, ite_eq_left ⟨hX, hsz⟩, ite_eq_left ⟨hX, hsz⟩]
        refine ⟨?_, ?_, hb⟩
        · have := length_aroundT_le (s.nodes.getX X).table x s.C.size (s.C.size + 1) (insF s x
          X).1 (insF s x X).2
          rw [List.length_map]; rw [List.length_map] at a
          change _ ≤ n0 X + 2 * (dr X + 1)
          have e1 : ((s.nodes.getX X).table).length = ((nd (ts s) X).table).length := rfl
          omega
        · have := length_sideAround_le (s.nodes.getX X) x s.C.size (s.C.size + 1)
          have e1 : ((s.nodes.getX X).side).length = ((nd (ts s) X).side).length := rfl
          omega
      · unfold drIns; rw [ite_eq_right hX]
        unfold order Node.order at a ⊢
        rw [F.table X, F.side X, ite_eq_right (fun h => hX h.1), ite_eq_right (fun h => hX h.1)]
        exact ⟨a, b, c⟩
    refine ⟨SH, hTi, hRo, fun j hj => ?_, hcap', hTL⟩
    cases hj
    refine ⟨⟨Al, Bl, hcl'⟩, ?_⟩
    change 1 ≤ 1 ∧ 1 ≤ (insFin s x f1x i1).P.H ∧
      lpr (insFin s x f1x i1) s.C.size = lpr (insFin s x f1x i1) x ∧
      lpr (insFin s x f1x i1) (s.C.size + 1) = lpr (insFin s x f1x i1) x
    rw [F.P, F.lpar, F.lpar, F.lpar, ite_eq_left (Or.inl rfl), ite_eq_left (Or.inr rfl),
      ite_eq_right (by omega)]
    exact ⟨le_rfl, by omega, rfl, rfl⟩

end OrderMaintenance.Proof.Top
