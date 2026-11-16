/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Job
public import LeanPool.OrderMaintenance.Impl.Reservation
public import LeanPool.OrderMaintenance.Proof.Top.PresDrain
public import LeanPool.OrderMaintenance.Proof.Top.PresFinish
public import LeanPool.OrderMaintenance.Proof.Top.StartRun
public import LeanPool.OrderMaintenance.Proof.Top.InsStart


/-!
# M6: the glue for the top structure

Level F's top proofs establish the hypotheses of the run lemmas inside their proofs. Here they
are exported as lemmas from the top invariant, so that the Level M case lemmas apply.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- **The hypotheses of a sweep step that moves a chunk** (those of `drainStep_move`, and the shape
facts the Level M program needs), from the order invariant: the proof of `Shape.drain_run`. -/
theorem Shape.drain_move_hyps {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord) {v : Nat}
    (hg : ghostN (ts s) v) (hne : rng (ts s) cl v ≠ []) (hL : LList (cN s) (cP s) s.firstChunk cl) :
    let y := dsY s v
    let h := ht (ts s) v
    let pv := digit (ts s) y (h + 1)
    let vb := digit (ts s) y h
    let pt := ((nd (ts s) (pp (ts s) y (h + 1))).lab? (dsT s v)).getD 0
    let tb := ((nd (ts s) (dsT s v)).lab? (pp (ts s) y (h - 1))).getD 0
    (s.nodes.getX v).alive = true ∧ (s.nodes.getX v).first ≠ NIL ∧
    (goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right) ∧
    (s.nodes.getX v).height + 1 < (s.path.getX (dsY s v)).size ∧
    (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? (dsT s v) = some pt ∧
    (s.nodes.getX (dsT s v)).lab? (belowY s v (dsY s v)) = some tb ∧
    (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? v = some pv ∧
    (s.nodes.getX v).lab? (belowY s v (dsY s v)) = some vb ∧
    (pv <<< ((s.nodes.getX v).height * s.P.beta)) |||
        (vb <<< (((s.nodes.getX v).height - 1) * s.P.beta)) ≤ (s.C.getX (dsY s v)).tag ∧
    TagOK s (dsY s v) (dsTag s v pt tb pv vb) ∧
    1 ≤ (s.nodes.getX v).height ∧ (s.path.getX (dsY s v)).size = s.P.H + 1 ∧
    tb < 2 ^ s.P.beta ∧ vb < 2 ^ s.P.beta ∧ dsT s v ≠ v ∧ v < s.nodes.size ∧ dsT s v < s.nodes.size ∧
    dsY s v ∈ cl ∧ (s.nodes.getX v).height < s.P.H ∧
    (s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1) < s.nodes.size := by
  intro y h pv vb pt tb
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  obtain ⟨hy, hanc, hLe, hRi, hside⟩ := S.pick hg hne
  obtain ⟨hycl, hypp, -, hbel, -⟩ := S.rng_ghost hg hy
  obtain ⟨m1, m2, m3, m4⟩ := S.ds_mem hg hne
  have hXN := (S.isN_pp hycl (by omega) (show h + 1 ≤ _ by omega)).1
  have hcl : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  -- the tag of the new path
  set tag := dsTag s v pt tb pv vb with htag
  have T := dsS_sameTree (tag := tag) hvt hv htz
  have hpp := S.ds_pp hg hne tag
  have hd1 : digit (ts (dsS s v tag)) y (h + 1) = pt := by
    unfold digit; rw [T.lab?, hpp, hpp, ite_eq_right (fun e => by omega), ite_eq_left ⟨rfl, rfl⟩]
  have hd0 : digit (ts (dsS s v tag)) y h = tb := by
    unfold digit; rw [T.lab?, hpp, hpp, ite_eq_left ⟨rfl, rfl⟩, ite_eq_right (fun e => by omega)]
  have hP : (ts (dsS s v tag)).P = (ts s).P := dsS_P s v tag
  have hrep := tagUp_replace2 (s := ts s) (s' := ts (dsS s v tag)) (c := y) (c' := y)
    (by rw [hP]) (h := h) (k := (ts s).P.H) hh1 (by omega)
    (fun i _ _ hi1 hi2 => S.ds_digit hg hne tag y i hi1 (Or.inl hi2))
  have hvbl : vb < 2 ^ s.P.beta := S.digit_lt hycl hh1 (by omega)
  have htbl : tb < 2 ^ s.P.beta := lab_lt S.toShapeT hlive.1 (getD_of_mem m2)
  have hor1 := lor_shift_eq_add (pv := pv) (h := h) hvbl hh1
  have hor2 := lor_shift_eq_add (pv := pt) (h := h) htbl hh1
  have htagy : (s.C.getX y).tag = tagF (ts s) y := S.tags y hycl
  have e1 : tagF (ts (dsS s v tag)) y = tagF (ts s) y -
      (pv * 2 ^ (h * s.P.beta) + vb * 2 ^ ((h - 1) * s.P.beta)) +
      (pt * 2 ^ (h * s.P.beta) + tb * 2 ^ ((h - 1) * s.P.beta)) := by
    unfold tagF; rw [hP, hrep.2, hd1, hd0]; rfl
  have e2 : tag = (s.C.getX y).tag - (pv * 2 ^ (h * s.P.beta) + vb * 2 ^ ((h - 1) * s.P.beta)) +
      (pt * 2 ^ (h * s.P.beta) + tb * 2 ^ ((h - 1) * s.P.beta)) := by
    rw [htag]; unfold dsTag
    show (s.C.getX y).tag - ((pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta))) +
      ((pt <<< (h * s.P.beta)) ||| (tb <<< ((h - 1) * s.P.beta))) = _
    rw [hor1, hor2]
  have hnew : tag = tagF (ts (dsS s v tag)) y := by rw [e1, e2, htagy]
  have hpv : pv = ((nd (ts s) (pp (ts s) y (h + 1))).lab? v).getD 0 := by
    simp only [pv, digit, Nat.add_sub_cancel]; rw [show pp (ts s) y h = v from hypp]
  have hvb' : vb = ((nd (ts s) v).lab? (pp (ts s) y (h - 1))).getD 0 := by
    simp only [vb, digit]; rw [show pp (ts s) y h = v from hypp]
  refine ⟨hg.1.2.2, ?_, hside, ?_, getD_of_mem m1, ?_, (by rw [hpv]; exact getD_of_mem m3), ?_, ?_, ?_,
    hh1, S.pathSize y hycl, htbl, hvbl, Ne.symm hvt, hv, htz, hycl, hhH, ?_⟩
  · obtain ⟨hf, -⟩ := S.ends v hg.1
    show (nd (ts s) v).first ≠ NIL
    rw [hf]
    exact fun e => hL.nonil (e ▸ (S.rng_sub v).subset (headD_mem hne NIL))
  · show h + 1 < ((ts s).path.getX y).size
    rw [S.pathSize y hycl]; omega
  · show (nd (ts s) (dsT s v)).lab? (belowY s v y) = some tb
    rw [hbel]; exact getD_of_mem m2
  · show (nd (ts s) v).lab? (belowY s v y) = some vb
    rw [hbel, hvb']; exact getD_of_mem m4
  · show (pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta)) ≤ (s.C.getX y).tag
    rw [hor1, htagy]; unfold tagF; exact hrep.1
  · -- the guard: the new tag lies between the neighbours' tags (Lemma T1 after the step)
    have ST := S.drain_shapeT hg hne tag
    refine ⟨fun hp => ?_, fun hn => ?_⟩
    · rw [hL.prev y hycl] at hp ⊢
      generalize hq : predOf cl y = q at hp ⊢
      obtain ⟨l1, l2, e⟩ := predOf_split hq hp
      have hb : Before cl q y := by
        rw [e]
        have : l1 ++ q :: y :: l2 = (l1 ++ [q]) ++ y :: l2 := by simp
        rw [this]; exact before_split (by simp)
      have hpcl := hb.mem_left
      have hpy := hb.ne hcl
      show (s.C.getX q).tag < tag
      rw [show (s.C.getX q).tag = (ts s).tag q from rfl, S.tags _ hpcl,
        ← S.ds_tagF_other hg hne tag _ hpy]
      exact lt_of_lt_of_eq (ST.tagF_lt hb) hnew.symm
    · rw [hL.next y hycl] at hn ⊢
      generalize hq : succOf cl y = q at hn ⊢
      obtain ⟨l1, l2, e⟩ := succOf_split hq hn
      have hb : Before cl y q := by
        rw [e]
        have : l1 ++ y :: q :: l2 = (l1 ++ [y]) ++ q :: l2 := by simp
        rw [this]; exact before_split (by simp)
      have hpcl := hb.mem_right
      have hpy := hb.ne hcl
      show tag < (s.C.getX q).tag
      rw [show (s.C.getX q).tag = (ts s).tag q from rfl, S.tags _ hpcl,
        ← S.ds_tagF_other hg hne tag _ (Ne.symm hpy)]
      exact lt_of_eq_of_lt hnew (ST.tagF_lt hb)
  · have h2 := hXN.2.1
    unfold pp at h2; rw [ite_eq_right (by omega)] at h2; exact h2


theorem len_le_two_of {l : List Nat} {a b : Nat} (hnd : l.Nodup) (h : ∀ x ∈ l, x = a ∨ x = b) : l.length ≤ 2 := by
  have hs : l.toFinset ⊆ {a, b} := fun x hx => by
    rcases h x (List.mem_toFinset.mp hx) with e | e <;> simp [e]
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card hs).trans (Finset.card_le_two)

/-- An entry lies in at most two tables (invariant Q). -/
theorem Shape.tabs_len {t : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape t cl ord) {h e : Nat}
    (he : Ent ord h e) : (tabs t h e).length ≤ 2 :=
  len_le_two_of (S.tabsNodup h e he) (fun X hX => S.Q h e X he hX)

/-- **The hypotheses of a sweep step that ends the drain** (those of `drainStep_finish`, and the
shape facts the Level M program needs). -/
theorem Shape.drain_finish_hyps {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord)
    {v : Nat} (hg : ghostN (ts s) v) (hemp : rng (ts s) cl v = []) :
    (s.nodes.getX v).alive = true ∧ (s.nodes.getX v).first = NIL ∧ (s.nodes.getX v).inTables.Nodup ∧
    (∀ T ∈ (s.nodes.getX v).inTables, v ∈ (s.nodes.getX T).order) ∧ v ≠ 0 ∧ v < s.nodes.size ∧
    ((s.nodes.getX v).height - 1 ≠ 0 → v ∉ (s.nodes.getX v).order) ∧
    (∀ T ∈ (s.nodes.getX v).inTables, T < s.nodes.size) ∧
    (s.nodes.getX v).t1 < s.nodes.size ∧ (s.nodes.getX v).t2 < s.nodes.size ∧
    (∀ e ∈ (s.nodes.getX v).order, (s.nodes.getX v).height - 1 ≠ 0 →
      e < s.nodes.size ∧ (s.nodes.getX e).inTables.length ≤ 2) ∧
    (∀ e ∈ (s.nodes.getX v).order, (s.nodes.getX v).height - 1 = 0 → e ∈ cl ∧ (s.cin.getX e).length ≤ 2) := by
  obtain ⟨hv, hno, hni, hvo, hvi, h1, h2, h12, ho1, ho2, hi1, hi2, hoi, hin, hent⟩ := S.fin_facts hg
  obtain ⟨hl1, hl2, -, -, -, -, -, -, -, -, -⟩ := S.ghost v hg
  refine ⟨hg.1.2.2, ?_, hni, fun T hT => ?_, hg.1.1, hv, hvo, fun T hT => (hin T hT).1.2.1, hl1.1.2.1, hl2.1.2.1,
    fun e he h0 => ⟨(hent e he h0).1.2.1, ?_⟩, fun e he h0 => ?_⟩
  · obtain ⟨hf, -⟩ := S.ends v hg.1
    show (nd (ts s) v).first = NIL
    rw [hf, hemp]; rfl
  · have hvent : Ent ord (ht (ts s) v) v :=
      (S.ordMem _ (S.htN v hg.1).1 (S.htN v hg.1).2 v).mpr ⟨hg.1, rfl⟩
    have := S.tabsIff _ v T hvent
    unfold tabs at this; rw [ite_eq_right (by have := (S.htN v hg.1).1; omega)] at this
    exact (this.mp hT).2.2
  · have hE : Ent ord (ht (ts s) v - 1) e := S.tabEnt v hg.1 e he
    have hL := S.tabs_len hE
    have h0' : ht (ts s) v - 1 ≠ 0 := h0
    unfold tabs at hL; rw [ite_eq_right h0'] at hL
    exact hL
  · have hE : Ent ord (ht (ts s) v - 1) e := S.tabEnt v hg.1 e he
    have h0' : ht (ts s) v - 1 = 0 := h0
    rw [h0'] at hE
    have hE' : e ∈ ord 0 := hE
    rw [S.ord0] at hE'
    refine ⟨hE', ?_⟩
    have := S.tabs_len hE
    unfold tabs at this; rw [ite_eq_left rfl] at this
    exact this

/-- A table holds at most 160 entries, and so does a side list (`TabLen`). -/
theorem tab_le_160 {t : TS} {dr n0 : Nat → Nat} (h : TabLen t dr n0) (X : Nat) :
    (nd t X).table.length ≤ 160 ∧ (nd t X).side.length ≤ 160 := by
  obtain ⟨a, b, c⟩ := h X
  have : (Top.order t X).length = (nd t X).table.length := by simp [Top.order, Node.order]
  omega

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
      TagOK { (ins0 s x) with
        C := (ins0 s x).C.modify s.C.size fun C => { C with tag := tagY (ins0 s x) x f1x i1 } }
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
  have hnd : (s.cin.getX x).Nodup := by
    have := S.tabsNodup 0 x hent; unfold tabs at this; rw [ite_eq_left rfl] at this; exact this
  -- the split's data
  have hT1 := ins_pp1 hI hC hx
  obtain ⟨i1, hi1⟩ := idx?_some_of_mem hT1
  set f1x := digit (ts s) x 1 with hf1
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
  have F := insFin_frame s x f1x i1 hxs hnd hdist hex
  have SH := ins_shape hI hC hx F hTP rfl hi1
  have htags := ins_tags hI hC hx F hTP rfl hi1
  have T1 : ∀ c d, Before (clIns cl x s.C.size (s.C.size + 1)) c d →
      tagF (insFin s x f1x i1) c < tagF (insFin s x f1x i1) d := fun c d h => SH.toShapeT.tagF_lt h
  obtain ⟨Al, Bl, hcl1, hA1, hB1, hcl'⟩ := ins_cl hI hC hx
  have hmem' : ∀ c, c ∈ clIns cl x s.C.size (s.C.size + 1) ↔ c ∈ cl ∨ c = s.C.size ∨ c = s.C.size + 1 := by
    intro c; rw [hcl', hcl1]; simp only [List.mem_append, List.mem_cons]; tauto
  -- the tags after the split are `tagF`
  have hty : tagY (ins0 s x) x f1x i1 = tagF (insFin s x f1x i1) s.C.size := by
    have := htags s.C.size ((hmem' _).mpr (Or.inr (Or.inl rfl)))
    rw [F.tag, ite_eq_right (by omega), ite_eq_left rfl] at this; exact this
  have htz : tagZ (ins0 s x) x f1x i1 = tagF (insFin s x f1x i1) (s.C.size + 1) := by
    have := htags (s.C.size + 1) ((hmem' _).mpr (Or.inr (Or.inr rfl)))
    rw [F.tag, ite_eq_left rfl] at this; exact this
  have hto : ∀ c ∈ cl, cT (ins0 s x) c = tagF (insFin s x f1x i1) c := by
    intro c hc
    have hcs := (hC c).mp hc
    have := htags c ((hmem' _).mpr (Or.inl hc))
    rw [F.tag, ite_eq_right (by omega), ite_eq_right (by omega)] at this
    unfold cT; rw [ins0_tag s x hcs.2, this]
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
    unfold ins0; rw [hLk.cN', ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, hn2, hnx]
  have hgy : TagOK (ins0 s x) s.C.size (tagY (ins0 s x) x f1x i1) := by
    refine ⟨fun hp => ?_, fun _ => ?_⟩
    · rw [cPy] at hp ⊢
      have hAl : Al ≠ [] := by rintro rfl; exact hp rfl
      have hm := getLastD_mem hAl NIL
      rw [hto _ (by rw [hcl1]; exact List.mem_append_left _ hm), hty]
      apply T1; rw [hcl']; exact before_app_l hm
    · rw [cNy, hto x hx, hty]
      apply T1; rw [hcl', show Al ++ s.C.size :: x :: (s.C.size + 1) :: Bl =
        (Al ++ [s.C.size]) ++ x :: (s.C.size + 1) :: Bl by simp]
      exact before_app_l (by simp)
  have hgz : TagOK { (ins0 s x) with
      C := (ins0 s x).C.modify s.C.size fun C => { C with tag := tagY (ins0 s x) x f1x i1 } }
      (s.C.size + 1) (tagZ (ins0 s x) x f1x i1) := by
    have eP : ∀ c, cP { (ins0 s x) with
        C := (ins0 s x).C.modify s.C.size fun C => { C with tag := tagY (ins0 s x) x f1x i1 } } c =
        cP (ins0 s x) c := fun c => by unfold cP; simp only [Array.getX_modify]; split_ifs <;> rfl
    have eN : ∀ c, cN { (ins0 s x) with
        C := (ins0 s x).C.modify s.C.size fun C => { C with tag := tagY (ins0 s x) x f1x i1 } } c =
        cN (ins0 s x) c := fun c => by unfold cN; simp only [Array.getX_modify]; split_ifs <;> rfl
    have eT : ∀ c, c ≠ s.C.size → cT { (ins0 s x) with
        C := (ins0 s x).C.modify s.C.size fun C => { C with tag := tagY (ins0 s x) x f1x i1 } } c =
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
      have hmc : Bl.headD NIL ∈ cl := by rw [hcl1]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
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
    S.W3 x hx 1 le_rfl (by have := S.H3; omega)
  obtain ⟨v, hv⟩ := lookup_some_of_mem hw
  have hfv : f1x = v := by
    rw [hf1]; unfold digit
    show ((nd (ts s) (pp (ts s) x 1)).lab? x).getD 0 = v
    unfold Node.lab?; rw [hv]; rfl
  have hf1' : ((ins0 s x).nodes.getX (((ins0 s x).path.getX x).getX 1)).lab? x = some f1x := by
    rw [hfv]; exact hv
  have htx : f1x ≤ ((ins0 s x).C.getX x).tag := by
    rw [ins0_tag s x hxs, show (s.C.getX x).tag = (ts s).tag x from rfl, S.tags x hx, hf1,
      ← tagUp_one]
    exact tagUp_mono _ _ _ _ (by have := S.H3; omega)
  have hlp : x ∈ ((ins0 s x).nodes.getX ((ins0 s x).lpar.getX x)).children := (S.lp x hx).2.2
  -- the exported facts
  have hTL := tab_le_160 hI.len
  have hlpx := S.lp x hx
  have hlpl : (s.nodes.getX (s.lpar.getX x)).children.length ≤ 160 := by
    obtain ⟨-, hsub', -⟩ := S.kids _ hlpx.1
    have h2 := (sublist_of_subset_common hsub' (S.O1 _ hlpx.1.1) (S.ordNodup _)
      (fun e he => S.kid_mem hI.time hlpx.1 he)).length_le
    have hl2 := (hTL (lpr (ts s) x)).1
    show (nd (ts s) (lpr (ts s) x)).children.length ≤ 160
    simp only [Top.order, Node.order, List.length_map] at h2; omega
  have hcinT : ∀ T ∈ s.cin.getX x, T < s.nodes.size := by
    intro T hT
    have := S.tabsIff 0 x T hent
    unfold tabs at this; rw [ite_eq_left rfl] at this
    exact (this.mp hT).1.2.1
  have hcl2 : (s.cin.getX x).length ≤ 2 := by
    have := S.tabs_len hent; unfold tabs at this; rw [ite_eq_left rfl] at this; exact this
  have hlt : ∀ c ∈ cl, c < s.C.size := fun c hc => ((hC c).mp hc).2
  refine ⟨f1x, i1, hroom, hnd, hf1', hi1, htx, hlp, hgy, hgz, ?_, ?_, ?_, ?_,
    fun T hT => ⟨hcinT T hT, (hTL T).1, (hTL T).2⟩, hcl2, hlpx.1.1.2.1, hlpl, hxs, ?_⟩
  · rw [cPy]
    rcases List.eq_nil_or_concat Al with h | ⟨L, b, h⟩
    · rw [h]; simp [NIL]; omega
    · have hm : Al.getLastD NIL ∈ cl := by
        rw [hcl1]; exact List.mem_append_left _ (getLastD_mem (by rw [h]; simp) NIL)
      exact hlt _ hm
  · rw [cNy]; omega
  · rw [cPz]; omega
  · rw [cNz]
    rcases Bl with _ | ⟨b, Bl'⟩
    · simp [NIL]; omega
    · have hm : b ∈ cl := by rw [hcl1]; simp
      exact hlt _ hm
  · exact fun h => hL.nonil (h ▸ hx)

end OrderMaintenance.Proof.Top

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top

/-- **The capacities the top structure's programs need**, at state `s`: the record counts below the
capacities (with room for the two records a step may add), node capacity covering chunk indices,
and list capacities above the invariant bounds (tables of at most 160 entries, entries in at most
2 tables). -/
structure TopCaps (κ : Caps) (s : Core) : Prop where
  N : s.nodes.size + 2 ≤ κ.tbl .N
  NC : s.C.size ≤ κ.tbl .N
  C : s.C.size + 2 ≤ κ.tbl .C
  rc : s.nodes.size + 2 ≤ κ.lrec .children
  rs : s.nodes.size + 2 ≤ κ.lrec .side
  rt : s.nodes.size + 2 ≤ κ.lrec .table
  ri : s.nodes.size + 2 ≤ κ.lrec .inTab
  rcin : s.nodes.size + s.C.size + 2 ≤ κ.lrec .cin
  alp : s.nodes.size + s.C.size + 2 ≤ κ.arr .lpar
  lt : 162 ≤ κ.lcap .table
  ls : 322 ≤ κ.lcap .side
  li : 322 ≤ κ.lcap .inTab
  lcin : 322 ≤ κ.lcap .cin
  lc : 162 ≤ κ.lcap .children
  pw : κ.pw = s.P.H + 1

/-- The cost bound of `startDrain`, from tables of at most 160 entries and entries in at most two
tables. -/
def sdBound : Nat := sdCost 160 160 2 160 160 160

theorem sdCost_le {K T I S B P : Nat} (hK : K ≤ 160) (hT : T ≤ 160) (hI : I ≤ 2) (hS : S ≤ 160) (hB : B ≤ 160)
    (hP : P ≤ 160) : sdCost K T I S B P ≤ sdBound := by
  unfold sdBound sdCost; gcongr

/-- **`startDrain` agrees at a drain start** (the context of `sr_run`). -/
theorem sdAgree_walk {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {v : Nat} (hpc : j.pc = .walk (some v)) (hv0 : v ≠ NIL) (hI : InvJ (ts s) cl ord dr n0 (some j))
    (hlp : (nd (ts s) v).livePar ≠ NIL) (hTP : TopParams s.P) (hof : (nd (ts s) v).overflowOf = NIL)
    (hW : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2)
    {side : List (Nat × Side)} (hside : sSideO (wiC s v) v = some side)
    (hlook : ∀ x, lookup side x =
      if 2 ≤ ht (ts s) v ∧ x ∈ sEntries (wiC s v) v ∧ (nd (ts s) x).draining = true then
        lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (nd (ts s) x).t1
      else lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) x)
    (hcl : CLok s cl) (K : TopCaps κ s) :
    ∃ D, D ≤ sdBound ∧ SDAgree κ (wiC s v) v D := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  obtain ⟨hl, hlh, hvL⟩ := sd_up hpc hv0 hI hlp
  obtain ⟨h1, hhH⟩ := sd_ht hpc hv0 hI hlp
  obtain ⟨hk2, hk1, hkn⟩ := sp_k hpc hv0 hI hlp hTP hof hW
  have H := sr_hyps hpc hv0 hI hlp hTP hof hW hlook
  have W := wiC_sameTree s v
  have hsz : (wiC s v).nodes.size = s.nodes.size := by simp [wiC]
  have hCsz : (wiC s v).C.size = s.C.size := rfl
  have hent : Ent ord (ht (ts s) v) v := (S.ordMem _ h1 (S.htN v hvl.1).2 v).mpr ⟨hvl.1, rfl⟩
  have hTL := tab_le_160 hI.len
  have hsh : sH (wiC s v) v = ht (ts s) v := sd_h_eq s v
  obtain ⟨hknd, hksub, hk⟩ := S.kids v hvl
  -- the entries and children, by height
  have hkeys : ∀ e ∈ ((wiC s v).nodes.getX v).table.map (·.1),
      (ht (ts s) v - 1 ≠ 0 → e < s.nodes.size) ∧ (ht (ts s) v - 1 = 0 → e < s.C.size) := by
    intro e he
    have hwt : ((wiC s v).nodes.getX v).table = (nd (ts s) v).table := W.table v
    have he' : e ∈ Top.order (ts s) v := by rw [hwt] at he; simpa [Top.order, Node.order] using he
    have hE : Ent ord (ht (ts s) v - 1) e := S.tabEnt v hvl.1 e he'
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · exact ((S.ordMem _ (by omega) (by have := (S.htN v hvl.1).2; omega) e).mp hE).1.2.1
    · rw [h0] at hE
      have hE0 : e ∈ ord 0 := hE
      rw [S.ord0] at hE0
      have := (hcl.2 e).mp hE0; omega
  have hkid : ∀ e ∈ (nd (ts s) v).children,
      (ht (ts s) v ≠ 1 → e < s.nodes.size ∧ e ≠ v) ∧ (ht (ts s) v = 1 → e < s.C.size) := by
    intro e he
    refine ⟨fun h0 => ⟨H.kid h0 e he, fun hev => ?_⟩, fun h0 => ?_⟩
    · have hm : e ∈ ord (ht (ts s) v - 1) := hksub.subset he
      have := ((S.ordMem _ (by omega) (by have := (S.htN v hvl.1).2; omega) e).mp hm).2
      rw [hev] at this; omega
    · have hm : e ∈ ord (ht (ts s) v - 1) := hksub.subset he
      rw [h0, Nat.sub_self, S.ord0] at hm
      have := (hcl.2 e).mp hm; omega
  have hkl : (nd (ts s) v).children.length ≤ 160 := by
    have := (sp_kids_sub hpc hv0 hI hlp hTP hof hW).length_le
    have hl2 := (hTL v).1
    simp only [Top.order, Node.order, List.length_map] at this; omega
  have hpl : (nd (ts s) (nd (ts s) v).livePar).children.length ≤ 160 := by
    obtain ⟨-, hsub', -⟩ := S.kids _ hl
    have h2 := (sublist_of_subset_common hsub' (S.O1 _ hl.1) (S.ordNodup _)
      (fun e he => S.kid_mem hI.time hl he)).length_le
    have hl2 := (hTL (nd (ts s) v).livePar).1
    simp only [Top.order, Node.order, List.length_map] at h2; omega
  have hvent : Ent ord (ht (ts s) v) v := hent
  -- the tables holding `v` sit one level up
  have hTv : ∀ T ∈ (nd (ts s) v).inTables, ht (ts s) T = ht (ts s) v + 1 ∧ T < s.nodes.size := by
    intro T hT
    have := S.tabsIff _ v T hvent
    unfold tabs at this; rw [ite_eq_right (by omega)] at this
    obtain ⟨a, b, -⟩ := this.mp hT
    exact ⟨b, a.2.1⟩
  have hinv : (nd (ts s) v).inTables.length ≤ 2 := by
    have := S.tabs_len hvent
    unfold tabs at this; rw [ite_eq_right (by omega)] at this; exact this
  have htl : ∀ e ∈ ((wiC s v).nodes.getX v).table.map (·.1), tabsLen (wiC s v) (sH (wiC s v) v - 1) e ≤ 2 := by
    intro e he
    have hwt : ((wiC s v).nodes.getX v).table = (nd (ts s) v).table := W.table v
    have he' : e ∈ Top.order (ts s) v := by rw [hwt] at he; simpa [Top.order, Node.order] using he
    have hE : Ent ord (ht (ts s) v - 1) e := S.tabEnt v hvl.1 e he'
    have hL := S.tabs_len hE
    rw [hsh]; unfold tabsLen tabs at *
    by_cases h0 : ht (ts s) v - 1 = 0
    · rw [ite_eq_left h0] at hL ⊢; exact hL
    · rw [ite_eq_right h0] at hL ⊢; rw [H.w_inTables]; exact hL
  have hTt : ((wiC s v).nodes.getX v).table.length ≤ 160 := by rw [H.w_table]; exact (hTL v).1
  have hsl : side.length ≤ 160 := by
    have := sp_side_len hpc hv0 hI hlp hTP hof hW hside
    have := (hTL v).1
    simp only [Top.order, Node.order, List.length_map] at *; omega
  refine ⟨_, sdCost_le (by rw [H.w_children]; exact hkl) hTt (by rw [H.w_inTables]; exact hinv) hsl le_rfl
    (by rw [H.w_livePar,
      H.w_children]; exact hpl),
      sdAgree_ok (B := 160) (side := side) (by rw [sd_kids_eq]; exact hk2) (fun h => by omega) hside
    (fun T hT => ?_) H.t_nd
    (fun e he => by
      rw [sd_kids_eq] at he
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook he]; rfl)
    (by rw [H.w_livePar, H.w_children]; exact hvL) H.t_hv
    (fun h => by rw [H.w_inTables] at h; have := (hTv v h).1; omega)
    (fun h0 h => by rw [H.w_children] at h; exact (hkid v h).1 (by rw [hsh] at h0; exact h0) |>.2 rfl)
    (fun h0 e he => by rw [hsz]; exact (hkeys e he).1 (by rwa [hsh] at h0))
    (fun e he => by
      by_cases h0 : ht (ts s) v - 1 = 0
      · have := (hkeys e he).2 h0
        exact ⟨by have := K.NC; omega, fun _ => by have := K.rcin; omega⟩
      · have := (hkeys e he).1 h0
        exact ⟨by have := K.N; omega, fun h => absurd (by rwa [hsh] at h) h0⟩)
    (fun h0 e he => by rw [H.w_children] at he; rw [hsz]; exact ((hkid e he).1 (by rwa [hsh] at h0)).1)
    (fun h0 e he => by
      rw [H.w_children] at he; have := (hkid e he).2 (by rwa [hsh] at h0); have := K.alp; omega)
    H.t_hL (by rw [H.w_livePar]; exact H.hLv)
    (fun T hT => by rw [H.w_table, H.w_side]; exact hTL T)
    (by rw [hsz]; exact K.N) (by rw [hsz]; exact K.rc) (by rw [hsz]; exact K.rs) (by rw [hsz]; exact K.rt)
    (by rw [hsz]; exact K.ri) (by rw [hsz]; have := K.rcin; omega) (by rw [hsz]; have := K.alp; omega)
    (fun T hT => by rw [H.w_table, H.w_side]; have := hTL T; have := K.lt; have := K.ls; omega)
    (by have := K.ls; omega) (by have := K.lt; omega)
    (by rw [H.w_inTables]; have := K.li; omega)
    (fun e he => by have := htl e he; have := K.li; have := K.lcin; split <;> omega)
    (by rw [H.w_children]; have := K.lc; omega)
    (by rw [H.w_livePar, H.w_children]; have := K.lc; omega)⟩
  · rw [H.w_inTables] at hT
    obtain ⟨A, le, Bs, htab, hA, hsd, h1, h2, -⟩ := room_up hI hTP hvl.1 hT 0 0
    exact ⟨A, le, Bs, by rw [H.w_table]; exact htab, hA, by rw [H.w_draining, H.w_side]; exact hsd, h1, h2⟩

/-- A chunk of the chunk list links to chunks of the list (or `NIL`). -/
theorem CLok.links {s : Core} {cl : List Nat} (h : CLok s cl) {c : Nat} (hc : c ∈ cl) :
    (s.C.getX c).next < s.C.size ∧ (s.C.getX c).prev < s.C.size := by
  have hc' := (h.2 c).mp hc
  have hn : (s.C.getX c).next = succOf cl c := h.1.next c hc
  have hp : (s.C.getX c).prev = predOf cl c := h.1.prev c hc
  constructor
  · rw [hn]; rcases succOf_mem_or (l := cl) (x := c) with e | e
    · exact ((h.2 _).mp e).2
    · rw [e]; simp [NIL]; omega
  · rw [hp]; rcases predOf_mem_or (l := cl) (x := c) with e | e
    · exact ((h.2 _).mp e).2
    · rw [e]; simp [NIL]; omega

/-- The cost bound of one sweep step (`drainStep`), from tables of at most 160 entries and entries
in at most two tables: the end of a drain dominates. -/
def dsBound : Nat := 300 + 160 * (171 + 100 * 160) + 2 * (301 + 200 * 160)

/-- **A sweep step that moves a chunk agrees** (outside a preparation). -/
theorem dsAgree_moveI {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord)
    {dr n0 : Nat → Nat} (hTL : TabLen (ts s) dr n0)
    {v : Nat} (hg : ghostN (ts s) v) (hne : rng (ts s) cl v ≠ []) (hcl : CLok s cl) (hprep : s.prep = none)
    (K : TopCaps κ s) : ∃ D, D ≤ dsBound ∧ DSAgree κ s v D := by
  obtain ⟨hal, hf, hside, hsz, hpt, htb, hpv, hvb, hold, hok, h1, hpsz, htbB, hvbB, htv, hvs, hts, hycl, hhH, hpr⟩ :=
    S.drain_move_hyps hg hne hcl.1
  have hfl : (s.nodes.getX v).first ∈ cl ∧ (s.nodes.getX v).last ∈ cl := by
    obtain ⟨e1, e2⟩ := S.ends v hg.1
    have e1' : (s.nodes.getX v).first = (rng (ts s) cl v).headD NIL := e1
    have e2' : (s.nodes.getX v).last = (rng (ts s) cl v).getLastD NIL := e2
    rw [e1', e2']
    refine ⟨(S.rng_sub v).subset (headD_mem hne NIL), (S.rng_sub v).subset ?_⟩
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hne]; exact List.getLast_mem hne
  have hfC := ((hcl.2 _).mp hfl.1).2
  have hlC := ((hcl.2 _).mp hfl.2).2
  obtain ⟨hyN, hyP⟩ := CLok.links hcl hycl
  have hnp : ∀ c, notPrep s c := fun c => by simp [notPrep, hprep]
  have hB : ∀ X, (s.nodes.getX X).table.length ≤ 160 ∧ (s.nodes.getX X).side.length ≤ 160 :=
    fun X => tab_le_160 hTL X
  refine ⟨_, ?_, dsAgree_move hal hf hside hsz hpt htb hpv hvb hold hok h1 hpsz htbB hvbB htv hvs hts
    (by have := ((hcl.2 _).mp hycl).2; exact this) (hnp _) (hnp _)
    (by have := K.N; omega) (by have := K.N; omega) (by have := K.rs; omega) (by have := K.rt; omega)
    (by have := K.rt; omega) (by have := K.rt; omega)
    (by have := K.C; omega) (by have := K.C; omega) (by have := K.C; omega) (by have := K.C; omega)
    (by rw [K.pw]; omega)⟩
  have := hB v; have := hB (dsT s v); have := hB ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))
  unfold dsBound; omega

/-- **A sweep step that ends the drain agrees.** -/
theorem dsAgree_finishI {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    (S : Shape (ts s) cl ord) (hTL : TabLen (ts s) dr n0)
    {v : Nat} (hg : ghostN (ts s) v) (hemp : rng (ts s) cl v = []) (hcl : CLok s cl)
    (K : TopCaps κ s) : ∃ D, D ≤ dsBound ∧ DSAgree κ s v D := by
  obtain ⟨hal, hf, hnd, hT, hv0, hvs, hvo, hTs, ht1, ht2, hE1, hE0⟩ := S.drain_finish_hyps hg hemp
  have hvent : Ent ord (ht (ts s) v) v :=
    (S.ordMem _ (S.htN v hg.1).1 (S.htN v hg.1).2 v).mpr ⟨hg.1, rfl⟩
  have hin : (s.nodes.getX v).inTables.length ≤ 2 := by
    have := S.tabs_len hvent
    unfold tabs at this; rw [ite_eq_right (by have := (S.htN v hg.1).1; omega)] at this; exact this
  have htv : (s.nodes.getX v).table.length ≤ 160 := (tab_le_160 hTL v).1
  refine ⟨_, ?_, dsAgree_finish (B := 160) hal hf hnd hT hv0 hvs hvo
    (by have := K.N; omega) (by have := K.rt; omega) (by have := K.ri; omega)
    (by have := K.N; omega) (by have := K.N; omega)
    (fun e he => ⟨fun h0 => by
        obtain ⟨a, b⟩ := hE0 e he h0
        have := ((hcl.2 e).mp a).2
        exact ⟨by have := K.rcin; omega, by have := K.lcin; omega, by omega⟩,
      fun h0 => by
        obtain ⟨a, b⟩ := hE1 e he h0
        exact ⟨by have := K.ri; omega, by have := K.li; omega, by omega⟩⟩)
    (fun T hT => by
      have := hTs T hT
      obtain ⟨a, b⟩ := tab_le_160 hTL T
      have a' : (s.nodes.getX T).table.length ≤ 160 := a
      have b' : (s.nodes.getX T).side.length ≤ 160 := b
      have := K.lt; have := K.ls
      exact ⟨by have := K.rt; omega, by have := K.rs; omega, by omega, by omega, a', b'⟩)⟩
  unfold dsBound
  have e1 := Nat.mul_le_mul_right (171 + 100 * 160) htv
  have e2 := Nat.mul_le_mul_right (301 + 200 * 160) hin
  omega

/-- **The funding loop's sweep step agrees**: its source is a ghost, so the step moves a chunk or
ends the drain. -/
theorem dsAgree_fund {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {v up src k : Nat} (hcl : CLok s cl) (hprep : s.prep = none)
    (hI : InvJ (ts s) cl ord dr n0 (some { j with pc := .fund v up src k })) (K : TopCaps κ s) :
    ∃ D, D ≤ dsBound ∧ DSAgree κ s src D := by
  have S := hI.shape
  obtain ⟨-, hat⟩ := hI.job _ rfl
  simp only [JobAt] at hat
  obtain ⟨-, -, -, hg, -, -⟩ := hat
  by_cases hne : rng (ts s) cl src = []
  · exact dsAgree_finishI S hI.len hg hne hcl K
  · exact dsAgree_moveI S hI.len hg hne hcl hprep K

theorem SDAgree.mono {κ : Caps} {S : Core} {v D D' : Nat} (h : SDAgree κ S v D) (hD : D ≤ D') :
    SDAgree κ S v D' := fun S' e => by
  obtain ⟨L', c, a, b, d⟩ := h S' e; exact ⟨L', c, a, by omega, d⟩

theorem DSAgree.mono {κ : Caps} {S : Core} {v D D' : Nat} (h : DSAgree κ S v D) (hD : D ≤ D') :
    DSAgree κ S v D' := fun b S' e => by
  obtain ⟨L', c, a, b1, b2, d⟩ := h b S' e; exact ⟨L', c, a, b1, by omega, d⟩

theorem TopCaps.wiC {κ : Caps} {s : Core} (K : TopCaps κ s) (v : Nat) : TopCaps κ (OrderMaintenance.Proof.Top.wiC s v) := by
  have h : (OrderMaintenance.Proof.Top.wiC s v).nodes.size = s.nodes.size := by simp [OrderMaintenance.Proof.Top.wiC]
  obtain ⟨a, b, c, d, e, f, g, i, k, l, m, n, o, p, q⟩ := K
  exact ⟨by rw [h]; exact a, b, c, by rw [h]; exact d, by rw [h]; exact e, by rw [h]; exact f, by rw [h]; exact g,
    by rw [h]; exact i, by rw [h]; exact k, l, m, n, o, p, q⟩

/-- **The walk step's agreements**, at node `v` of the walk: `startDrain` where the walk starts a
drain, and the sweep step of the funding loop where `v` has an overflow source. -/
theorem walkAgree {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {v : Nat} (hpc : j.pc = .walk (some v)) (hTP : TopParams s.P) (hcl : CLok s cl)
    (hprep : s.prep = none) (hI : InvJ (ts s) cl ord dr n0 (some j)) (K : TopCaps κ s) :
    (v ≠ NIL → ((s.nodes.getX v).livePar != NIL && !(s.nodes.getX v).draining &&
      (s.nodes.getX v).overflowOf == NIL &&
      decide ((s.nodes.getX v).weight + 2 > 2 * s.P.a ^ (s.nodes.getX v).height)) = true →
        SDAgree κ (wiC s v) v sdBound) ∧
    (v ≠ NIL → (s.nodes.getX v).overflowOf ≠ NIL → DSAgree κ (wiC s v) (s.nodes.getX v).overflowOf dsBound) := by
  refine ⟨fun hv0 hc => ?_, fun hv0 hov => ?_⟩
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', beq_iff_eq,
    decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    obtain ⟨side, hside, hlook⟩ := sp_side hpc hv0 hI h1 hTP h3 (by unfold Wd ht; exact h4)
    obtain ⟨D, hD, hA⟩ := sdAgree_walk hpc hv0 hI h1 hTP h3 (by unfold Wd ht; exact h4) hside hlook hcl K
    exact hA.mono hD
  · have hno : ¬ ((nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
        (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2) :=
      fun h => hov h.2.2.1
    have hI' := inv_winc hpc hv0 hI hno
    have hn : walkNext (ts s) j v = { j with pc := .fund v (nd (ts s) v).livePar (srcOf (ts s) v) 0 } := by
      simp only [walkNext]; rw [ite_eq_right (show srcOf (ts s) v ≠ NIL from hov)]
    rw [hn] at hI'
    obtain ⟨D, hD, hA⟩ := dsAgree_fund (hcl.topRel (wiC_topRel s v)) hprep hI' (K.wiC v)
    exact hA.mono hD

/-- A copy step keeps the node count and the path of the chunk copied from. -/
theorem copyS_frame (t : TS) (j : Job) (l : Nat) (hxy : j.x ≠ j.y) (hxz : j.x ≠ j.z) :
    (OrderMaintenance.Proof.Top.copyS t j l).nodes.size = t.nodes.size ∧ (OrderMaintenance.Proof.Top.copyS t j l).path.getX j.x = t.path.getX j.x := by
  unfold OrderMaintenance.Proof.Top.copyS; dsimp only
  split_ifs <;> simp [Array.getX_setX, Ne.symm hxy, Ne.symm hxz, hxy, hxz]

theorem copyRest_frame (j : Job) (H : Nat) (hxy : j.x ≠ j.y) (hxz : j.x ≠ j.z) : ∀ k t l, H + 1 - l = k →
    (copyRest j H t l).nodes.size = t.nodes.size ∧ (copyRest j H t l).path.getX j.x = t.path.getX j.x := by
  intro k
  induction k with
  | zero => intro t l hk; unfold copyRest; rw [ite_eq_right (by omega)]; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro t l hk; unfold copyRest; rw [ite_eq_left (by omega)]
    obtain ⟨a, b⟩ := ih (OrderMaintenance.Proof.Top.copyS t j l) (l + 1) (by omega)
    obtain ⟨c, d⟩ := copyS_frame t j l hxy hxz
    exact ⟨a.trans c, b.trans d⟩

/-- The running job's chunks: in the chunk list, distinct, not `NIL`. -/
theorem job_chunks {t : TS} {s : Core} {cl : List Nat} {j : Job} (hcl : CLok s cl) (hJ : JobOK t cl j) :
    j.x ∈ cl ∧ j.y ∈ cl ∧ j.z ∈ cl ∧ j.x ≠ j.y ∧ j.x ≠ j.z ∧ j.y ≠ j.z := by
  obtain ⟨A, B, e⟩ := hJ.pos
  have hnd := hcl.1.nodup
  rw [e] at hnd ⊢
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
  refine ⟨by simp, by simp, by simp, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp_all

/-- **A copy step agrees.** -/
theorem copyAgree {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {l : Nat} (hpc : j.pc = .copy l) (hres : s.resJob = some j) (hcl : CLok s cl) (hprep : s.prep = none)
    (hI : InvJ (finS (ts s) (some j)) cl ord dr n0 (some j)) (K : TopCaps κ s) : JobAgree κ s j 140 := by
  intro r t1 h
  rw [jobStep_copy hpc] at h
  injection h with hr ht; subst hr; subst ht
  have hJ := hI.job j rfl
  obtain ⟨hx, hy, hz, hxy, hxz, hyz⟩ := job_chunks hcl hJ
  have hat := hJ.at_
  simp only [JobAt, hpc] at hat
  obtain ⟨hl1, hlH, -⟩ := hat
  have hfin : finS (ts s) (some j) = copyRest j s.P.H (ts s) l := by simp only [finS, hpc]; rfl
  have hP : (finS (ts s) (some j)).P = s.P := by rw [hfin]; exact copyRest_P j _ _ _ _ rfl
  rw [hP] at hlH
  obtain ⟨hsz, hpx⟩ := copyRest_frame j s.P.H hxy hxz _ (ts s) l rfl
  have hN := (hI.shape.toShapeT.isN_pp hx hl1 (by rw [hP]; exact hlH)).1.2.1
  unfold pp pth at hN; rw [ite_eq_right (by omega)] at hN
  rw [← hfin] at hsz hpx
  rw [hpx, hsz] at hN
  have hC : ∀ c ∈ cl, c < κ.tbl .C := fun c hc => by have := ((hcl.2 c).mp hc).2; have := K.C; omega
  have hnp : ∀ c, notPrep s c := fun c => by simp [notPrep, hprep]
  obtain ⟨L', c, e, hc⟩ := jobStepS_copy (κ := κ) (L := OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] []) hres hpc
    (fun h => hcl.1.nonil (h ▸ hx)) hyz (hnp _) (hnp _) (hnp _) (hC _ hx) (hC _ hy) (hC _ hz)
    (by rw [K.pw]; omega) (by have := K.N; have hN' : (s.path.getX j.x).getX l < s.nodes.size := hN; omega)
  exact ⟨L', c, e, hc⟩

/-- The cost bound of one job step at Level M. -/
def jobBound : Nat := sdBound + dsBound + 300

/-- **Every job step agrees**, under the top invariant, outside a preparation, with the capacities. -/
theorem jobAgree {κ : Caps} {s : Core} {j : Job} (hT : TopInv s) (hres : s.resJob = some j) (hprep : s.prep = none)
    (hpow : s.P.a = 2 ^ Nat.log2 s.P.a) (K : TopCaps κ s) : JobAgree κ s j jobBound := by
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hT
  rw [hres] at hI
  have hcl : CLok s cl := ⟨hL, hC⟩
  intro r t1 h
  cases hpc : j.pc with
  | copy l =>
    obtain ⟨L', c, e, hc⟩ := copyAgree hpc hres hcl hprep hI K r t1 h
    exact ⟨L', c, e, by unfold jobBound; omega⟩
  | walk ov =>
    have hfin : finS (ts s) (some j) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    cases ov with
    | none =>
      obtain ⟨hI', hl, -⟩ := walkNone_inv hpc hI
      obtain ⟨hsd, hds⟩ := walkAgree (j := { j with pc := .walk (some (lpr (ts s) j.y)) }) rfl hTP hcl hprep hI' K
      have hy := (job_chunks hcl (hI.job j rfl)).2.1
      have hyC := ((hcl.2 _).mp hy).2
      have hls : s.lpar.getX j.y < s.nodes.size := hl.1.2.1
      obtain ⟨L', c, e, hc⟩ := jobStepS_walkNone (κ := κ) (L := OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] [])
        hres hpc (by have := K.alp; omega) (fun _ => hls) (fun _ => by have := K.N; omega) hsd hds hpow h
      exact ⟨L', c, e, by unfold jobBound; omega⟩
    | some v =>
      obtain ⟨hsd, hds⟩ := walkAgree hpc hTP hcl hprep hI K
      have hat := (hI.job j rfl).at_
      simp only [JobAt, hpc] at hat
      have hvs : v ≠ 0 → v < s.nodes.size := fun h0 => by
        rcases hat with e | ⟨hl, -⟩
        · exact absurd e h0
        · exact hl.1.2.1
      obtain ⟨L', c, e, hc⟩ := jobStepS_walkSome (κ := κ) (L := OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] [])
        hres hpc hvs (fun h0 => by have := hvs h0; have := K.N; omega) hsd hds hpow h
      exact ⟨L', c, e, by unfold jobBound; omega⟩
  | afterDrain v up =>
    have hfin : finS (ts s) (some j) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    have hat := (hI.job j rfl).at_
    simp only [JobAt, hpc] at hat
    obtain ⟨hg, -, -⟩ := hat
    obtain ⟨-, -, -, -, -, -, -, -, hgs, -⟩ := hI.shape.ghost v hg
    have hvs : v < s.nodes.size := hg.1.2.1
    obtain ⟨L', c, e, hc⟩ := jobStepS_after (κ := κ) (L := OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] []) (D := 0)
      hres hpc (by have := K.N; omega) (fun hne => absurd hgs hne) h
    exact ⟨L', c, e, by unfold jobBound; omega⟩
  | fund v up src k =>
    have hfin : finS (ts s) (some j) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    rw [job_eta hpc] at hI
    obtain ⟨D, hD, hA⟩ := dsAgree_fund hcl hprep hI K
    obtain ⟨L', c, e, hc⟩ := jobStepS_fund (κ := κ) (L := OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] []) hres hpc hA h
    exact ⟨L', c, e, by unfold jobBound; omega⟩

/-- The cost bound of a split start at Level M. -/
def splitBound : Nat := 150 + (1200 + 60 * 160 + 2 * (1100 + 400 * 160) + 220 * 160)

/-- **A split start agrees**, under the top invariant with no job running, outside a preparation,
with the capacities and zero path rows beyond the chunks. -/
theorem splitAgree_top {κ : Caps} {s : Core} {A : Abs} {x : Nat} (hA : INV s A) (hT : TopInv s)
    (hres : s.resJob = none) (hxL : LiveC s x) (hprep : s.prep = none)
    (hrow : ∀ c, s.C.size ≤ c → ∀ j, (s.path.getX c).getX j = 0) (K : TopCaps κ s) :
    ∃ D, D ≤ splitBound ∧ SplitAgree κ s x D := by
  obtain ⟨f1x, i1, hroom, hnd, hf1, hi1, htx, hlp, hgy, hgz, cPy, cNy, cPz, cNz, hT', hcl2, hlps, hlpl, hxs,
    hx0⟩ := ins_hyps hA hT hres hxL
  have H3 : 3 ≤ s.P.H := by
    obtain ⟨-, cl, ord, dr, n0, -, -, hI⟩ := hT
    rw [hres] at hI; exact hI.shape.H3
  obtain ⟨-, -, -, -, -, hsz0⟩ := ins0_top (s := s) (x := x)
  obtain ⟨-, cl, ord, dr, n0, hL, hC, -⟩ := hT
  obtain ⟨hxn, hxp⟩ := CLok.links ⟨hL, hC⟩ ((hC x).mpr hxL)
  have hia : IAOK κ (ins0 s x) x s.C.size (s.C.size + 1) f1x i1 160 := {
    room := hroom, nd := hnd, yx := by omega, f1 := hf1, idx := hi1, tx := htx, lp := hlp, gy := hgy, gz := hgz,
    zx := by omega, yz := by omega,
    npx := by simp [notPrep, ins0, linkChunkPair, push2, hprep]
    npy := by simp [notPrep, ins0, linkChunkPair, push2, hprep]
    npz := by simp [notPrep, ins0, linkChunkPair, push2, hprep]
    xC := by have := K.C; omega
    pw := by rw [K.pw]; omega
    H := by rw [K.pw]; rfl
    xa := by have := K.alp; omega
    ya := by have := K.alp; omega
    za := by have := K.alp; omega
    ys := by rw [hsz0]; omega
    zs := by rw [hsz0]; omega
    yC := by have := K.C; omega
    zC := by have := K.C; omega
    yP := by have := K.C; exact lt_of_lt_of_le cPy (by omega)
    yN := by have := K.C; exact lt_of_lt_of_le cNy (by omega)
    zP := by have := K.C; exact lt_of_lt_of_le cPz (by omega)
    zN := by have := K.C; exact lt_of_lt_of_le cNz (by omega)
    ry := fun j _ => by
      simp only [rowOf, ins0, linkChunkPair, push2, hprep]; exact hrow _ le_rfl j
    rz := fun j _ => by
      simp only [rowOf, ins0, linkChunkPair, push2, hprep]; exact hrow _ (by omega) j
    xi := by have := K.rcin; omega
    yi := by have := K.rcin; omega
    zi := by have := K.rcin; omega
    cin := by have := K.lcin; exact le_trans hcl2 (by omega)
    capT := fun T hT => by
      obtain ⟨a, b, c⟩ := hT' T hT
      have b' : ((ins0 s x).nodes.getX T).table.length ≤ 160 := b
      have c' : ((ins0 s x).nodes.getX T).side.length ≤ 160 := c
      have := K.rt; have := K.rs; have := K.N; have := K.lt; have := K.ls
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    tB := fun T hT => ⟨(hT' T hT).2.1, (hT' T hT).2.2⟩
    lr := by have := K.rc; exact lt_of_lt_of_le hlps (by omega)
    ccap := by have := K.lc; exact le_trans (Nat.add_le_add_right hlpl 2) (by omega) }
  refine ⟨_, ?_, splitAgree_ok hx0 hxs (by have := K.C; omega) (fun _ => hxp) (fun _ => hxn) hia⟩
  unfold splitBound iaCost
  have e1 := Nat.mul_le_mul_right (1100 + 400 * 160) hcl2
  have e2 : (s.nodes.getX (s.lpar.getX x)).children.length ≤ 160 := hlpl
  show 150 + (1200 + 60 * 160 + (s.cin.getX x).length * (1100 + 400 * 160) +
    220 * (s.nodes.getX (s.lpar.getX x)).children.length) ≤ _
  omega

end OrderMaintenance.Impl
