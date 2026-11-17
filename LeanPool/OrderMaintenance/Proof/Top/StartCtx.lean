/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartData
public import LeanPool.OrderMaintenance.Proof.Top.PresWalk


/-!
# M5: the situation when a drain starts

The walk is at `v`, a live non-root node with no source, whose true weight exceeds `W_h`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
theorem sd_kids_eq (s : Core) (v : Nat) : sKids (wiC s v) v = (nd (ts s) v).children :=
  (wiC_sameTree s v).children v
theorem sd_h_eq (s : Core) (v : Nat) : sH (wiC s v) v = ht (ts s) v := (wiC_sameTree s v).height v

/-- A child's distinct neighbours by index. -/
theorem getD_ne_of_nodup {l : List Nat} (hl : l.Nodup) {i j : Nat} (hi : i < l.length) (hj : j <
  l.length)
    (hij : i ≠ j) : l.getD i 0 ≠ l.getD j 0 := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  intro e; exact hij ((List.Nodup.getElem_inj_iff hl).mp e)

theorem getD_mem' {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem cutLen_ones : ∀ (m b : Nat), cutLen (List.replicate m 1) b = min m b
  | 0, b => by simp [cutLen]
  | m + 1, b => by
    simp only [List.replicate_succ, cutLen]
    by_cases hb : 1 ≤ b
    · rw [ite_eq_left hb, cutLen_ones m (b - 1)]; omega
    · rw [ite_eq_right hb]; omega

section ctx
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  (hpc : j.pc = .walk (some v)) (hv0 : v ≠ NIL) (hI : InvJ (ts s) cl ord dr n0 (some j))
  (hlp : (nd (ts s) v).livePar ≠ NIL)
include hpc hv0 hI hlp

omit hlp in
theorem sd_live : liveN (ts s) v ∧ v = anc (ts s) j.y (ht (ts s) v) := by
  obtain ⟨-, hat⟩ := hI.job j rfl
  simp only [JobAt, hpc] at hat
  exact hat.resolve_left hv0

theorem sd_ht : 1 ≤ ht (ts s) v ∧ ht (ts s) v < s.P.H := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨h1, hH⟩ := S.htN v hvl.1
  have hH' : ht (ts s) v ≤ s.P.H := hH
  have h3 : 3 ≤ s.P.H := S.H3
  refine ⟨h1, ?_⟩
  by_contra h
  have hm := (S.ordMem (ts s).P.H (by have := S.H3; omega) le_rfl v).mpr ⟨hvl.1, by
    change ht (ts s) v = s.P.H; omega⟩
  rw [S.root.1] at hm; simp only [List.mem_singleton] at hm
  rw [hm] at hlp; exact hlp S.root.2.2

theorem sd_up : liveN (ts s) (nd (ts s) v).livePar ∧ ht (ts s) (nd (ts s) v).livePar = ht (ts s)
  v + 1 ∧
    v ∈ (nd (ts s) (nd (ts s) v).livePar).children := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  exact S.up v hvl (sd_ht hpc hv0 hI hlp).2

theorem sd_pend : pend (ts s) (some j) = v :: upChain (ts s) ((ts s).P.H + 1) (nd (ts s)
  v).livePar := by
  have S := hI.shape
  obtain ⟨hl, hh, -⟩ := sd_up hpc hv0 hI hlp
  simp only [pend, wStart, hpc]
  have : upChain (ts s) ((ts s).P.H + 1) v = v :: upChain (ts s) (ts s).P.H (nd (ts s)
    v).livePar := by
    simp [upChain, hv0]
  rw [this, S.upChain_succ (ts s).P.H _ hl (by rw [hh]; have := sd_ht hpc hv0 hI hlp; omega)]

/-- Nodes below `v` do not lag. -/
theorem sd_notpend {u : Nat} (hh : ht (ts s) u < ht (ts s) v) :
    u ∉ pend (ts s) (some j) := by
  have S := hI.shape
  obtain ⟨hl, hlh, -⟩ := sd_up hpc hv0 hI hlp
  rw [sd_pend hpc hv0 hI hlp]
  intro hm
  rcases List.mem_cons.mp hm with e | e
  · rw [e] at hh; omega
  · have := (S.upChain_mem _ _ u hl e).2; omega

theorem sd_tw : tw (ts s) cl v = (nd (ts s) v).weight + 2 := by
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  have := hI.time.wts v hvl
  rw [sd_pend hpc hv0 hI hlp, ite_eq_left (List.mem_cons_self ..)] at this
  omega

/-- A child's stored weight is its true weight. -/
theorem sd_kid_weight {e : Nat} (he : e ∈ (nd (ts s) v).children) (h2 : 2 ≤ ht (ts s) v) :
    (nd (ts s) e).weight = tw (ts s) cl e := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨-, -, hk⟩ := S.kids v hvl
  have hel := (hk e he).2 h2
  have heh : ht (ts s) e = ht (ts s) v - 1 := by
    have := ((S.mem_children hvl).mp he).1; rw [ite_eq_right (by omega)] at this; exact this.2
  have := hI.time.wts e hel
  rw [ite_eq_right (sd_notpend hpc hv0 hI hlp (by omega))] at this
  omega

/-- A child weighs at most `W_{h-1}`. -/
theorem sd_kid_le (hTP : TopParams s.P) {e : Nat} (he : e ∈ (nd (ts s) v).children) (h2 : 2 ≤ ht
  (ts s) v) :
    tw (ts s) cl e ≤ Wd s.P (ht (ts s) v - 1) := by
  have S := hI.shape
  have Ti := hI.time
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨-, -, hk⟩ := S.kids v hvl
  have hel := (hk e he).2 h2
  have heh : ht (ts s) e = ht (ts s) v - 1 := by
    have := ((S.mem_children hvl).mp he).1; rw [ite_eq_right (by omega)] at this; exact this.2
  rw [← sd_kid_weight hpc hv0 hI hlp he h2, ← heh]
  have hpe : (nd (ts s) e).livePar ≠ NIL := by
    have := (hk e he).1
    rw [par_live (Or.inr hel), ite_eq_right (by omega)] at this; rw [this]; exact hvl.1.1
  by_cases hs : srcOf (ts s) e = NIL
  · exact Ti.wA e hel hpe hs
  · obtain ⟨hg, htg⟩ := S.src e hel hs
    generalize hgv : srcOf (ts s) e = g at hg htg
    obtain ⟨-, -, hh1, hh2, -⟩ := S.ghost _ hg
    have := Ti.release S hTP hg htg (sd_notpend hpc hv0 hI hlp (by omega))
    have hhu : ht (ts s) e = ht (ts s) g := by rcases htg with e' | e' <;> rw [e'] <;> assumption
    rw [hhu]; exact this

omit hlp in
/-- **A pair of children is a drain's two targets.** -/
theorem sd_pair (h2 : 2 ≤ ht (ts s) v) {k : Nat} (hk1 : 1 ≤ k) (hkn : k < (nd (ts s)
  v).children.length)
    (hp : sPr (wiC s v) v k = true) :
    ∃ g, ghostN (ts s) g ∧ srcOf (ts s) ((nd (ts s) v).children.getD (k - 1) 0) = g ∧
      srcOf (ts s) ((nd (ts s) v).children.getD k 0) = g ∧
      ({(nd (ts s) v).children.getD (k - 1) 0, (nd (ts s) v).children.getD k 0} : Finset Nat) =
        {(nd (ts s) g).t1, (nd (ts s) g).t2} := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨hnd, -, hk⟩ := S.kids v hvl
  set kids := (nd (ts s) v).children
  have ha := getD_mem' (l := kids) (i := k - 1) (by omega)
  have hb := getD_mem' (l := kids) (i := k) hkn
  have hab := getD_ne_of_nodup hnd (i := k - 1) (j := k) (by omega) hkn (by omega)
  unfold sPr drainPr sameDrainN at hp
  rw [sd_kids_eq] at hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have e1 : srcOf (ts s) (kids.getD (k - 1) 0) = ((wiC s v).nodes.getX (kids.getD (k - 1)
    0)).overflowOf :=
    ((wiC_sameTree s v).overflowOf _).symm
  have e2 : srcOf (ts s) (kids.getD k 0) = ((wiC s v).nodes.getX (kids.getD k 0)).overflowOf :=
    ((wiC_sameTree s v).overflowOf _).symm
  have hal := (hk _ ha).2 h2
  have hbl := (hk _ hb).2 h2
  obtain ⟨hg, hat⟩ := S.src _ hal (by rw [e1]; exact hp1)
  have hsb : srcOf (ts s) (kids.getD k 0) = srcOf (ts s) (kids.getD (k - 1) 0) := by
    rw [e1, e2, hp2]
  obtain ⟨-, hbt⟩ := S.src _ hbl (by rw [hsb, e1]; exact hp1)
  rw [hsb] at hbt
  refine ⟨_, hg, rfl, hsb, ?_⟩
  generalize srcOf (ts s) (kids.getD (k - 1) 0) = g at hat hbt
  rcases hat with ea | ea <;> rcases hbt with eb | eb
  · exact absurd (ea.trans eb.symm) hab
  · rw [ea, eb]
  · rw [ea, eb, Finset.pair_comm]
  · exact absurd (ea.trans eb.symm) hab

/-- The children's weights, as `startDrain` reads them (above height 1). -/
theorem sd_ws (h2 : 2 ≤ ht (ts s) v) : sWs (wiC s v) v = (nd (ts s) v).children.map (tw (ts s)
  cl) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  unfold sWs sWt
  rw [sd_kids_eq, sd_h_eq]
  apply List.map_congr_left
  intro e he
  have heh : ht (ts s) e = ht (ts s) v - 1 := by
    have := ((S.mem_children hvl).mp he).1; rw [ite_eq_right (by omega)] at this; exact this.2
  have hev : e ≠ v := fun h' => by rw [h'] at heh; omega
  unfold drainWt
  rw [ite_eq_right (by simp; omega), ← sd_kid_weight hpc hv0 hI hlp he h2]
  change ((s.nodes.modify v _).getX e).weight = _
  rw [Array.getX_modify, ite_eq_right (fun h' => hev h'.1.symm)]; rfl

/-- **Lemma T0 at a drain** (above height 1). -/
theorem sd_cut2 (hTP : TopParams s.P) (h2 : 2 ≤ ht (ts s) v) (hof : (nd (ts s) v).overflowOf = NIL)
    (hW : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2) :
    2 ≤ (nd (ts s) v).children.length ∧ 1 ≤ sK (wiC s v) v ∧
      sK (wiC s v) v ≤ (nd (ts s) v).children.length - 1 ∧ sPr (wiC s v) v (sK (wiC s v) v) =
        false ∧
      lamd s.P (ht (ts s) v) ≤ (((nd (ts s) v).children.take (sK (wiC s v) v)).map (tw (ts s)
        cl)).sum ∧
      (((nd (ts s) v).children.take (sK (wiC s v) v)).map (tw (ts s) cl)).sum ≤ taud s.P (ht (ts
        s) v) ∧
      lamd s.P (ht (ts s) v) ≤ (((nd (ts s) v).children.drop (sK (wiC s v) v)).map (tw (ts s)
        cl)).sum ∧
      (((nd (ts s) v).children.drop (sK (wiC s v) v)).map (tw (ts s) cl)).sum ≤ taud s.P (ht (ts
        s) v) := by
  have S := hI.shape
  have Ti := hI.time
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  obtain ⟨hnd, -, hk⟩ := S.kids v hvl
  set kids := (nd (ts s) v).children with hkids
  set h := ht (ts s) v with hh
  have hU : Wd s.P (h - 1) ≤ Pid s.P (h - 1) := by unfold Pid; omega
  have hpw := hTP.piW h h2
  -- the weight of `v`
  have htv := sd_tw hpc hv0 hI hlp
  have hwa : (nd (ts s) v).weight ≤ Wd s.P h := Ti.wA v hvl hlp hof
  have hS : (kids.map (tw (ts s) cl)).sum = tw (ts s) cl v := (S.tw_kids hvl h2).symm
  have hkle : ∀ e ∈ kids, tw (ts s) cl e ≤ Wd s.P (h - 1) := fun e he => sd_kid_le hpc hv0 hI
    hlp hTP he h2
  have hlen : (kids.map (tw (ts s) cl)).length = kids.length := List.length_map _
  -- at least two children
  have hn : 2 ≤ kids.length := by
    by_contra hn
    have hle := List.sum_le_length_nsmul (kids.map (tw (ts s) cl)) (Wd s.P (h - 1))
      (fun x hx => by obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx; exact hkle e he)
    rw [hS, hlen, smul_eq_mul] at hle
    have : kids.length * Wd s.P (h - 1) ≤ Wd s.P (h - 1) := by
      rcases Nat.lt_or_ge kids.length 1 with h0 | h1
      · rw [show kids.length = 0 by omega]; simp
      · rw [show kids.length = 1 by omega]; simp
    omega
  -- the restricted pair test
  set n := kids.length with hn'
  let pr' : Nat → Bool := fun k => decide (1 ≤ k ∧ k < n) && sPr (wiC s v) v k
  have hK : sK (wiC s v) v = drainCut (kids.map (tw (ts s) cl)) pr' true := by
    unfold sK
    rw [sd_ws hpc hv0 hI hlp h2, sd_h_eq, show decide (h > 1) = true by simp; omega]
    apply drainCut_congr
    intro k h1 h2'; rw [hlen] at h2'; simp [pr', h1, h2']
  have hpr : ∀ k, pr' k = true → 1 ≤ k ∧ k < n ∧ sPr (wiC s v) v k = true := by
    intro k hk'; simp only [pr', Bool.and_eq_true, decide_eq_true_eq] at hk'; exact ⟨hk'.1.1,
      hk'.1.2, hk'.2⟩
  have hget : ∀ i, i < n → (kids.map (tw (ts s) cl)).getD i 0 = tw (ts s) cl (kids.getD i 0) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi), List.getD_eq_getElem _ _ hi,
      List.getElem_map]
  -- a pair weighs at most `Π_{h-1}`
  have hpair : ∀ k, 1 ≤ k → k < n → sPr (wiC s v) v k = true →
      tw (ts s) cl (kids.getD (k - 1) 0) + tw (ts s) cl (kids.getD k 0) ≤ Pid s.P (h - 1) := by
    intro k h1 hkn hp
    obtain ⟨g, hg, hs1, hs2, hfs⟩ := sd_pair hpc hv0 hI h2 h1 hkn hp
    have hew := Ti.ew_le hTP hg
    obtain ⟨-, -, hh1, hh2, -, -, -, -, -, -, -, -, hinf⟩ := S.ghost g hg
    have h12 : (nd (ts s) g).t1 ≠ (nd (ts s) g).t2 :=
      ((before_of_infix2 (infix3_left hinf)).trans (before_of_infix2 (infix3_right hinf))
        (S.ordNodup _)).ne (S.ordNodup _)
    have hab := getD_ne_of_nodup hnd (i := k - 1) (j := k) (by omega) hkn (by omega)
    have hgh : ht (ts s) g = h - 1 := by
      have ha := getD_mem' (l := kids) (i := k) hkn
      have := ((S.mem_children hvl).mp ha).1; rw [ite_eq_right (by omega)] at this
      have hm : kids.getD k 0 ∈ ({(nd (ts s) g).t1, (nd (ts s) g).t2} : Finset Nat) := by
        rw [← hfs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with e | e <;> rw [← this.2, e] <;> [exact hh1.symm; exact hh2.symm]
    have hsum : tw (ts s) cl (kids.getD (k - 1) 0) + tw (ts s) cl (kids.getD k 0) = ew (ts s) cl
      g := by
      unfold ew; rw [ite_eq_left hg.2]
      have hm1 : kids.getD (k - 1) 0 ∈ ({(nd (ts s) g).t1, (nd (ts s) g).t2} : Finset Nat) := by
        rw [← hfs]; exact Finset.mem_insert_self _ _
      have hm2 : kids.getD k 0 ∈ ({(nd (ts s) g).t1, (nd (ts s) g).t2} : Finset Nat) := by
        rw [← hfs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
      rcases hm1 with e1 | e1 <;> rcases hm2 with e2 | e2
      · exact absurd (e1.trans e2.symm) hab
      · rw [e1, e2]
      · rw [e1, e2, Nat.add_comm]
      · exact absurd (e1.trans e2.symm) hab
    rw [hsum, ← hgh]; exact hew
  -- pairs are disjoint
  have hpok : PairsOK pr' (kids.map (tw (ts s) cl)).length := by
    rw [hlen]
    intro k hk'
    obtain ⟨h1, hkn, hp⟩ := hpr k hk'
    refine ⟨h1, hkn, ?_⟩
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    obtain ⟨h1', hkn', hp'⟩ := hpr (k + 1) hc
    obtain ⟨g, hg, hs1, hs2, hfs⟩ := sd_pair hpc hv0 hI h2 h1 hkn hp
    obtain ⟨g', hg', hs1', hs2', hfs'⟩ := sd_pair hpc hv0 hI h2 h1' hkn' hp'
    simp only [Nat.add_sub_cancel] at hs1' hfs'
    have hgg : g' = g := by rw [← hs1', hs2]
    subst hgg
    have hm0 : kids.getD (k - 1) 0 ∈ ({(nd (ts s) g').t1, (nd (ts s) g').t2} : Finset Nat) := by
      rw [← hfs]; exact Finset.mem_insert_self _ _
    have hm1 : kids.getD k 0 ∈ ({(nd (ts s) g').t1, (nd (ts s) g').t2} : Finset Nat) := by
      rw [← hfs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hm2 : kids.getD (k + 1) 0 ∈ ({(nd (ts s) g').t1, (nd (ts s) g').t2} : Finset Nat) := by
      rw [← hfs']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have d01 := getD_ne_of_nodup hnd (i := k - 1) (j := k) (by omega) hkn (by omega)
    have d12 := getD_ne_of_nodup hnd (i := k) (j := k + 1) hkn hkn' (by omega)
    have d02 := getD_ne_of_nodup hnd (i := k - 1) (j := k + 1) (by omega) hkn' (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm0 hm1 hm2
    rcases hm0 with e0 | e0 <;> rcases hm1 with e1 | e1 <;> rcases hm2 with e2 | e2 <;>
      first | exact d01 (e0.trans e1.symm) | exact d12 (e1.trans e2.symm) | exact d02 (e0.trans
        e2.symm)
  have hU1 : ∀ i, i < (kids.map (tw (ts s) cl)).length → (kids.map (tw (ts s) cl)).getD i 0 ≤
    Pid s.P (h - 1) := by
    intro i hi; rw [hlen] at hi; rw [hget i hi]
    exact le_trans (hkle _ (getD_mem' hi)) hU
  have hU2 : ∀ k, pr' k = true → (kids.map (tw (ts s) cl)).getD (k - 1) 0 + (kids.map (tw (ts s)
    cl)).getD k 0 ≤
      Pid s.P (h - 1) := by
    intro k hk'
    obtain ⟨h1, hkn, hp⟩ := hpr k hk'
    rw [hget _ (by omega), hget _ hkn]; exact hpair k h1 hkn hp
  have hgive : true = true → ¬((kids.map (tw (ts s) cl)).length = 2 ∧ pr' 1 = true) := by
    rintro - ⟨h2', hp1⟩
    rw [hlen] at h2'
    obtain ⟨-, hkn, hp⟩ := hpr 1 hp1
    have := hpair 1 le_rfl hkn hp
    have hsum : (kids.map (tw (ts s) cl)).sum = tw (ts s) cl (kids.getD 0 0) + tw (ts s) cl
      (kids.getD 1 0) := by
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2'
      rw [hab]; simp
    rw [hS] at hsum; simp only [Nat.sub_self] at this; omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := cutK_spec (kids.map (tw (ts s) cl)) pr' true (Pid s.P (h - 1))
    (by rw [hlen]; exact hn) hpok hU1 hU2 hgive
  rw [← hK] at c1 c2 c3 c4 c5
  rw [hlen] at c2
  have c3' := c3 rfl
  have hb : lamd s.P h ≤ ((kids.take (sK (wiC s v) v)).map (tw (ts s) cl)).sum ∧
      ((kids.take (sK (wiC s v) v)).map (tw (ts s) cl)).sum ≤ taud s.P h ∧
      lamd s.P h ≤ ((kids.drop (sK (wiC s v) v)).map (tw (ts s) cl)).sum ∧
      ((kids.drop (sK (wiC s v) v)).map (tw (ts s) cl)).sum ≤ taud s.P h := by
    have htk : ((kids.take (sK (wiC s v) v)).map (tw (ts s) cl)).sum =
        ((kids.map (tw (ts s) cl)).take (sK (wiC s v) v)).sum := by rw [List.map_take]
    have hdk : ((kids.drop (sK (wiC s v) v)).map (tw (ts s) cl)).sum =
        (kids.map (tw (ts s) cl)).sum - ((kids.map (tw (ts s) cl)).take (sK (wiC s v) v)).sum := by
      rw [List.map_drop]
      have := List.sum_take_add_sum_drop (kids.map (tw (ts s) cl)) (sK (wiC s v) v)
      omega
    rw [htk, hdk]
    rw [hS] at c4 c5 ⊢
    obtain ⟨h', hh'⟩ : ∃ h', h = h' + 2 := ⟨h - 2, by omega⟩
    rw [hh']
    have e1 : taud s.P (h' + 2) = s.P.a ^ (h' + 2) + 1 + Pid s.P (h' + 1) := rfl
    have e2 : lamd s.P (h' + 2) = s.P.a ^ (h' + 2) + 1 - Pid s.P (h' + 1) := rfl
    have e3 : Wd s.P (h' + 2) = 2 * s.P.a ^ (h' + 2) := rfl
    rw [e1, e2]
    rw [hh', show h' + 2 - 1 = h' + 1 by omega] at c4 c5
    rw [hh', e3] at hW hwa
    omega
  refine ⟨hn, c1, c2, ?_, hb⟩
  by_contra hc; simp only [Bool.not_eq_false] at hc
  have : pr' (sK (wiC s v) v) = true := by simp [pr', c1, hc]; omega
  rw [c3'] at this; exact absurd this (by simp)

/-- **The cut at height 1**: unit weights, the halves. -/
theorem sd_cut1 (h1 : ht (ts s) v = 1) (hof : (nd (ts s) v).overflowOf = NIL)
    (hW : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2) :
    2 ≤ (nd (ts s) v).children.length ∧ 1 ≤ sK (wiC s v) v ∧
      sK (wiC s v) v ≤ (nd (ts s) v).children.length - 1 ∧
      lamd s.P 1 ≤ ((nd (ts s) v).children.take (sK (wiC s v) v)).length ∧
      ((nd (ts s) v).children.take (sK (wiC s v) v)).length ≤ taud s.P 1 ∧
      lamd s.P 1 ≤ ((nd (ts s) v).children.drop (sK (wiC s v) v)).length ∧
      ((nd (ts s) v).children.drop (sK (wiC s v) v)).length ≤ taud s.P 1 := by
  have S := hI.shape
  have Ti := hI.time
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI
  set kids := (nd (ts s) v).children with hkids
  have htv := sd_tw hpc hv0 hI hlp
  have hwa : (nd (ts s) v).weight ≤ Wd s.P (ht (ts s) v) := Ti.wA v hvl hlp hof
  have hn : kids.length = tw (ts s) cl v := (S.tw_one hvl h1).symm
  rw [h1] at hW hwa
  have e3 : Wd s.P 1 = 2 * s.P.a := by simp [Wd]
  rw [e3] at hW hwa
  have hK : sK (wiC s v) v = kids.length / 2 := by
    unfold sK sWs sWt
    rw [sd_kids_eq, sd_h_eq, h1]
    have hm : kids.map (drainWt (wiC s v).nodes 1) = List.replicate kids.length 1 := by
      rw [List.eq_replicate_iff]; simp [drainWt]
    rw [hm]
    unfold drainCut
    simp only [List.length_replicate, List.sum_replicate, smul_eq_mul, Nat.mul_one,
      List.take_replicate,
      cutLen_ones, show decide (1 > 1) = false by decide, Bool.false_and, ite_false,
        Bool.false_eq_true]
    omega
  rw [hK, List.length_take, List.length_drop]
  have e1 : lamd s.P 1 = s.P.a := rfl
  have e2 : taud s.P 1 = s.P.a + 1 := rfl
  rw [e1, e2]
  omega

end ctx

end OrderMaintenance.Proof.Top
