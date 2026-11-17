/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.GroupSplit


/-!
# Group split steps preserve INV-S (Lemma 3.2: split moves and group removal)

* `unlinkStep g` removes an alive, empty group from the group list and its chunk, and frees it.
* `moveElem g` moves the first (last) element of an alive, non-empty group to the end (front)
  of the group just before (after) it in the group list, with a guarded label.

Neither changes the element list. `groupSplitStep`, `removeGroup` and `driveGroup` are
compositions of these with updates that INV-S does not see.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Removing an empty group -/

theorem unlinkStep_run (s : Core) (g : Nat) :
    (g ≠ NIL ∧ g < s.Gs.size ∧ gA s g = true ∧ gF s g = NIL ∧
        (unlinkStep g).run s = .ok () (unlinkGroup s g)) ∨
    (∃ msg, (unlinkStep g).run s = .error (.guard msg) s) := by
  unfold unlinkStep
  simp only [run_getG_bind, run_get_bind, run_require_bind]
  by_cases h : (g != NIL && decide (g < s.Gs.size) && (s.Gs.getX g).alive &&
      (s.Gs.getX g).first == NIL) = true
  · rw [ite_eq_left h]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
    left; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2, rfl⟩
  · rw [ite_eq_right h]; right; exact ⟨_, rfl⟩

section unlink
variable {s : Core} {g : Nat}

theorem unlinkGroup_gN (hpg : gP s g ≠ g) (z : Nat) :
    gN (unlinkGroup s g) z =
      if z = g ∧ g < s.Gs.size then NIL
      else if z = gP s g ∧ gP s g ≠ NIL ∧ gP s g < s.Gs.size then gN s g else gN s z := by
  simp only [gN, gP] at *
  generalize hp : (s.Gs.getX g).prev = p at *
  generalize hn : (s.Gs.getX g).next = n at *
  simp only [unlinkGroup, hp, hn, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.next), bne_iff_ne, ne_eq]
  by_cases hzg : z = g
  · subst hzg; by_cases hs : z < s.Gs.size <;> simp [hs, hpg, Ne.symm hpg]
  · by_cases hzp : z = p
    · subst hzp
      by_cases hp0 : z = NIL
      · have hg0 : g ≠ NIL := fun e => hpg (hp0.trans e.symm)
        by_cases hs : z < s.Gs.size <;> simp [ hp0,   hg0, Ne.symm hg0]
      · by_cases hs : z < s.Gs.size <;> simp [hzg, hp0, hs, Ne.symm hzg]
    · simp [hzg, hzp, Ne.symm hzg, Ne.symm hzp]

theorem unlinkGroup_gP (hng : gN s g ≠ g) (z : Nat) :
    gP (unlinkGroup s g) z =
      if z = g ∧ g < s.Gs.size then NIL
      else if z = gN s g ∧ gN s g ≠ NIL ∧ gN s g < s.Gs.size then gP s g else gP s z := by
  simp only [gN, gP] at *
  generalize hp : (s.Gs.getX g).prev = p at *
  generalize hn : (s.Gs.getX g).next = n at *
  simp only [unlinkGroup, hp, hn, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.prev), bne_iff_ne, ne_eq]
  by_cases hzg : z = g
  · subst hzg; by_cases hs : z < s.Gs.size <;> simp [hs, hng, Ne.symm hng]
  · by_cases hzn : z = n
    · subst hzn
      by_cases hn0 : z = NIL
      · have hg0 : g ≠ NIL := fun e => hng (hn0.trans e.symm)
        by_cases hs : z < s.Gs.size <;> simp [ hn0,   hg0, Ne.symm hg0]
      · by_cases hs : z < s.Gs.size <;> simp [hzg, hn0, hs, Ne.symm hzg]
    · simp [hzg, hzn, Ne.symm hzg, Ne.symm hzn]

theorem unlinkGroup_gF (z : Nat) : gF (unlinkGroup s g) z = gF s z := by
  simp only [unlinkGroup, gF, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.first)]
  split_ifs <;> rfl

theorem unlinkGroup_gLs (z : Nat) : gLs (unlinkGroup s g) z = gLs s z := by
  simp only [unlinkGroup, gLs, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.last)]
  split_ifs <;> rfl

theorem unlinkGroup_gC (z : Nat) : gC (unlinkGroup s g) z = gC s z := by
  simp only [unlinkGroup, gC, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.chk)]
  split_ifs <;> rfl

theorem unlinkGroup_gL (z : Nat) : gL (unlinkGroup s g) z = gL s z := by
  simp only [unlinkGroup, gL, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.lab)]
  split_ifs <;> rfl

theorem unlinkGroup_gA (z : Nat) :
    gA (unlinkGroup s g) z = if z = g ∧ g < s.Gs.size then false else gA s z := by
  simp only [unlinkGroup, gA, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.alive)]
  by_cases hzg : z = g
  · subst hzg; by_cases hs : z < s.Gs.size <;> simp [hs]
  · simp only [hzg, false_and, ite_false, Ne.symm hzg]; split_ifs <;> rfl

theorem unlinkGroup_Gsize : (unlinkGroup s g).Gs.size = s.Gs.size := by
  simp only [unlinkGroup, Array.size_modify', Array.size_ite]; split_ifs <;> rfl

theorem unlinkGroup_C (z : Nat) (hc : gC s g < s.C.size) :
    (unlinkGroup s g).C.getX z =
      if z = gC s g then
        { s.C.getX z with
          first := if cF s (gC s g) = g ∧ cLs s (gC s g) = g then NIL
            else if cF s (gC s g) = g then gN s g else cF s (gC s g)
          last := if cF s (gC s g) = g ∧ cLs s (gC s g) = g then NIL
            else if cF s (gC s g) = g then cLs s (gC s g)
            else if cLs s (gC s g) = g then gP s g else cLs s (gC s g) }
      else s.C.getX z := by
  simp only [unlinkGroup, gC, cF, cLs, gN, gP,  Bool.and_eq_true,
    beq_iff_eq] at *
  by_cases hz : z = (s.Gs.getX g).chk
  · subst hz; split_ifs <;> simp_all
  · simp only [hz, ite_false]; split_ifs <;> simp [ Ne.symm hz]

theorem unlinkGroup_rest :
    (unlinkGroup s g).E = s.E ∧ (unlinkGroup s g).C.size = s.C.size ∧
      (unlinkGroup s g).freeG = g :: s.freeG ∧ (unlinkGroup s g).head = s.head ∧
      (unlinkGroup s g).tail = s.tail ∧ (unlinkGroup s g).firstChunk = s.firstChunk ∧
      (unlinkGroup s g).firstGroup = (if gP s g ≠ NIL then s.firstGroup else gN s g) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [unlinkGroup]; split_ifs <;> simp
  · simp only [unlinkGroup, gP, gN, bne_iff_ne, ne_eq]

end unlink

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The abstract nesting without group `g` (in chunk `c`). -/
def Abs.removeGroup (A : Abs) (c g : Nat) : Abs where
  chunks := A.chunks
  grps := fun c' => if c' = c then (A.grps c).replace1 g [] else A.grps c'
  elts := A.elts

theorem isChain_erase {l1 l2 : List Nat} {x : Nat} {f : Nat → Nat}
    (hs : ((l1 ++ x :: l2).map f).IsChain (· < ·)) : ((l1 ++ l2).map f).IsChain (· < ·) := by
  rw [List.isChain_iff_pairwise] at hs ⊢
  rw [List.pairwise_map] at hs ⊢
  exact hs.sublist (List.Sublist.append_left (List.sublist_cons_self x l2) l1)

theorem mem_erase_mid {l1 l2 : List Nat} {x z : Nat} : z ∈ l1 ++ l2 → z ∈ l1 ++ x :: l2 :=
  mem_split_of_mem

/-- Removing a group updates the ends of its chunk to the neighbouring groups. -/
theorem unlinkGroup_chunkEnds {s : Core} {A : Abs} (hI : INV s A) {g : Nat}
    (hg : g ∈ A.glist) :
    ∀ c' ∈ A.chunks, Ends (cF (unlinkGroup s g) c') (cLs (unlinkGroup s g) c')
      ((A.removeGroup (gC s g) g).grps c') := by
  obtain ⟨hc, hgc⟩ := hI.mem_glist hg
  generalize hcdef : gC s g = c at hc hgc ⊢
  generalize hpdef : gP s g = p
  generalize hndef : gN s g = n
  have hgnd := hI.gList.nodup
  have hcs : c < s.C.size := ((hI.cAlloc c).mp hc).2
  let s' := unlinkGroup s g
  have hC' : ∀ z, s'.C.getX z = if z = c then
      { s.C.getX z with
        first := if cF s c = g ∧ cLs s c = g then NIL else if cF s c = g then n else cF s c
        last := if cF s c = g ∧ cLs s c = g then NIL else if cF s c = g then cLs s c
          else if cLs s c = g then p else cLs s c }
      else s.C.getX z := by
    intro z
    have := unlinkGroup_C (s := s) (g := g) z (hcdef ▸ hcs)
    rw [hcdef, hpdef, hndef] at this
    exact this
  obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hgc
  have hrnd : (A.grps c).Nodup := by
    have := hgnd; rw [INV.glist_flatten] at this
    exact List.nodup_flatten.mp this |>.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hr1 : g ∉ r1 := by
    rw [hrun] at hrnd; exact fun h => (List.nodup_append.mp hrnd).2.2 g h g (by simp) rfl
  have hr2 : g ∉ r2 := by
    rw [hrun] at hrnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1
  have hgrps' : (A.removeGroup c g).grps c = r1 ++ r2 := by
    simp [Abs.removeGroup, hrun, replace1_mid hr1]
  have hgrpsO : ∀ c', c' ≠ c → (A.removeGroup c g).grps c' = A.grps c' := by
    intro c' h; simp [Abs.removeGroup, h]
  have hcE := hI.cEnds c hc
  rw [hrun] at hcE
  have hfirst : cF s c = g ↔ r1 = [] := by
    rw [hcE.1]
    constructor
    · intro e
      cases r1 with
      | nil => rfl
      | cons a t =>
        change a = g at e
        exact absurd (e ▸ (by simp : a ∈ a :: t)) hr1
    · rintro rfl; rfl
  have hlast : cLs s c = g ↔ r2 = [] := by
    rw [hcE.2]
    constructor
    · intro e
      cases r2 with
      | nil => rfl
      | cons a t =>
        rw [show r1 ++ g :: a :: t = (r1 ++ [g]) ++ a :: t by simp, getLastD_append_cons] at e
        exact absurd (e ▸ getLastD_cons_mem a t NIL) hr2
    · rintro rfl; simp
  have hpblk : r1 ≠ [] → p = r1.getLastD NIL := by
    intro h1
    rw [← hpdef, hI.gList.prev g hg, INV.glist_flatten]
    rw [INV.glist_flatten] at hgnd
    rw [predOf_flatten hgnd (List.mem_map.mpr ⟨c, hc, rfl⟩) hgc (by
      rw [hrun]; cases r1 with
      | nil => exact absurd rfl h1
      | cons a t =>
        simp only [List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
        intro e
        exact hr1 (e ▸ (by simp)))]
    rw [hrun, predOf_mid (hrun ▸ hrnd)]
  have hnblk : r2 ≠ [] → n = r2.headD NIL := by
    intro h2
    rw [← hndef, hI.gList.next g hg, INV.glist_flatten]
    rw [INV.glist_flatten] at hgnd
    rw [succOf_flatten hgnd (List.mem_map.mpr ⟨c, hc, rfl⟩) hgc (by
      rw [hrun]; cases r2 with
      | nil => exact absurd rfl h2
      | cons a t =>
        intro e
        rw [show r1 ++ g :: a :: t = (r1 ++ [g]) ++ a :: t by simp,
          List.getLast?_append_of_ne_nil _ (by simp)] at e
        exact hr2 (List.mem_of_getLast? e))]
    rw [hrun, succOf_mid (hrun ▸ hrnd)]
  intro c' hc'
  change Ends (cF s' c') (cLs s' c') ((A.removeGroup c g).grps c')
  by_cases hcc : c' = c
  · subst hcc
    rw [hgrps']
    simp only [cF, cLs, hC', ite_true]
    simp only [cF, cLs] at hfirst hlast hcE
    by_cases h1 : r1 = []
    · subst h1
      by_cases h2 : r2 = []
      · subst h2; simp [hfirst.mpr rfl, hlast.mpr rfl, Ends]
      · have hnl : ¬ (s.C.getX c').last = g := fun e => h2 (hlast.mp e)
        simp only [hfirst.mpr rfl, hnl, and_false, ite_false, ite_true]
        refine ⟨?_, ?_⟩
        · rw [hnblk h2]; rfl
        · rw [hcE.2]; obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h2
          rw [show ([] : List Nat) ++ g :: a :: t = [g] ++ a :: t by simp, getLastD_append_cons]
          simp
    · have hnf : ¬ (s.C.getX c').first = g := fun e => h1 (hfirst.mp e)
      simp only [hnf, false_and, ite_false]
      by_cases h2 : r2 = []
      · subst h2
        simp only [hlast.mpr rfl, ite_true]
        refine ⟨?_, ?_⟩
        · rw [hcE.1]; cases r1 with
          | nil => exact absurd rfl h1
          | cons a t => rfl
        · rw [hpblk h1]; simp
      · have hnl : ¬ (s.C.getX c').last = g := fun e => h2 (hlast.mp e)
        simp only [hnl, ite_false]
        refine ⟨?_, ?_⟩
        · rw [hcE.1]; cases r1 with
          | nil => exact absurd rfl h1
          | cons a t => rfl
        · rw [hcE.2]; obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h2
          rw [show r1 ++ g :: a :: t = (r1 ++ [g]) ++ a :: t by simp, getLastD_append_cons,
            getLastD_append_cons]
  · rw [hgrpsO c' hcc]
    simp only [cF, cLs, hC', hcc, ite_false]
    exact hI.cEnds c' hc'


/-- Flattening the abstract nesting after deleting one group removes exactly that group. -/
theorem removeGroup_glist_split {s : Core} {A : Abs} (hI : INV s A) {c g : Nat}
    (hc : c ∈ A.chunks) (hgc : g ∈ A.grps c) {l1 l2 : List Nat}
    (hsplit : A.glist = l1 ++ g :: l2) :
    (A.removeGroup c g).glist = l1 ++ l2 ∧
      ∀ z, z ∈ (A.removeGroup c g).glist ↔ z ≠ g ∧ z ∈ A.glist := by
  have hgnd := hI.gList.nodup
  have hnd' := hgnd
  rw [hsplit] at hnd'
  have hg1 : g ∉ l1 := fun h => (List.nodup_append.mp hnd').2.2 g h g (by simp) rfl
  have hg2 : g ∉ l2 := (List.nodup_cons.mp (List.nodup_append.mp hnd').2.1).1
  have hgl' : (A.removeGroup c g).glist = l1 ++ l2 := by
    have : (A.removeGroup c g).glist = A.glist.replace1 g [] :=
      flatMap_replace1 hgnd hI.cList.nodup hc hgc fun b => rfl
    rw [this, hsplit, replace1_mid hg1]; simp
  have hmem' : ∀ z, z ∈ (A.removeGroup c g).glist ↔ z ≠ g ∧ z ∈ A.glist := by
    intro z
    rw [hgl', hsplit]
    constructor
    · intro hz
      refine ⟨fun e => ?_, mem_split_of_mem hz⟩
      subst e
      simp only [List.mem_append] at hz
      rcases hz with h | h
      · exact hg1 h
      · exact hg2 h
    · rintro ⟨hzg, hz⟩
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      rcases hz with h | h | h
      · exact Or.inl h
      · exact absurd h hzg
      · exact Or.inr h
  exact ⟨hgl', hmem'⟩

/-- **Removing an empty group preserves INV-S.** -/
theorem good_unlinkStep (g : Nat) : Good (unlinkStep g) := by
  intro s A hI
  rcases unlinkStep_run s g with ⟨hg0, hgs, hga, hgf, hr⟩ | ⟨msg, hr⟩
  · rw [hr]
    have hg := hI.mem_of_alive hg0 hgs hga
    obtain ⟨hc, hgc⟩ := hI.mem_glist hg
    generalize hcdef : gC s g = c at hc hgc
    have hgnd := hI.gList.nodup
    have hel0 : A.elts g = [] := by
      have := (hI.gEnds g hg).1; rw [hgf] at this
      cases h : A.elts g with
      | nil => rfl
      | cons a t =>
        rw [h] at this
        change NIL = a at this
        exact absurd (this ▸ (h ▸ (by simp : a ∈ a :: t) : a ∈ A.elts g))
          (fun hm => hI.eList.nonil (A.elts_sub_elist hg hm))
    generalize hpdef : gP s g = p
    generalize hndef : gN s g = n
    have hpm : p = NIL ∨ p ∈ A.glist := hpdef ▸ hI.gP_mem hg
    have hnm : n = NIL ∨ n ∈ A.glist := hndef ▸ hI.gN_mem hg
    have hpg : p ≠ g := by
      rw [← hpdef, hI.gList.prev g hg]; exact predOf_ne_self hgnd g hg0
    have hng : n ≠ g := by
      rw [← hndef, hI.gList.next g hg]; exact succOf_ne_self hgnd g hg0
    have hps : p ≠ NIL → p < s.Gs.size := fun h => hI.gAlloc p (hpm.resolve_left h)
    have hns : n ≠ NIL → n < s.Gs.size := fun h => hI.gAlloc n (hnm.resolve_left h)
    -- accessors
    obtain ⟨rE, rCs, rF, rH, rT, rFC, rFG⟩ := unlinkGroup_rest (s := s) (g := g)
    set s' := unlinkGroup s g with hs'
    have gN' : ∀ z, gN s' z = if z = g then NIL else if z = p ∧ p ≠ NIL then n else gN s z := by
      intro z
      rw [unlinkGroup_gN (hpdef ▸ hpg), hpdef, hndef]
      by_cases h1 : z = g; · simp [h1, hgs]
      simp only [h1, false_and, ite_false]
      by_cases h2 : z = p ∧ p ≠ NIL
      · simp [h2, hps h2.2]
      · rw [ite_eq_right (fun h => h2 ⟨h.1, h.2.1⟩), ite_eq_right h2]
    have gP' : ∀ z, gP s' z = if z = g then NIL else if z = n ∧ n ≠ NIL then p else gP s z := by
      intro z
      rw [unlinkGroup_gP (hndef ▸ hng), hpdef, hndef]
      by_cases h1 : z = g; · simp [h1, hgs]
      simp only [h1, false_and, ite_false]
      by_cases h2 : z = n ∧ n ≠ NIL
      · simp [h2, hns h2.2]
      · rw [ite_eq_right (fun h => h2 ⟨h.1, h.2.1⟩), ite_eq_right h2]
    have gA' : ∀ z, gA s' z = if z = g then false else gA s z := by
      intro z; rw [unlinkGroup_gA]; by_cases h : z = g <;> simp [h, hgs]
    have hcs : c < s.C.size := ((hI.cAlloc c).mp hc).2
    have hC' : ∀ z, s'.C.getX z = if z = c then
        { s.C.getX z with
          first := if cF s c = g ∧ cLs s c = g then NIL else if cF s c = g then n else cF s c
          last := if cF s c = g ∧ cLs s c = g then NIL else if cF s c = g then cLs s c
            else if cLs s c = g then p else cLs s c }
        else s.C.getX z := by
      intro z
      have := unlinkGroup_C (s := s) (g := g) z (hcdef ▸ hcs)
      rw [hcdef, hpdef, hndef] at this
      exact this
    -- the abstract nesting
    obtain ⟨l1, l2, hsplit⟩ := List.mem_iff_append.mp hg
    have hnd' := hgnd
    rw [hsplit] at hnd'
    have hg1 : g ∉ l1 := fun h => (List.nodup_append.mp hnd').2.2 g h g (by simp) rfl
    have hg2 : g ∉ l2 := (List.nodup_cons.mp (List.nodup_append.mp hnd').2.1).1
    obtain ⟨hgl', hmem'⟩ := removeGroup_glist_split hI hc hgc hsplit
    have hel' : (A.removeGroup c g).elist = A.elist := by
      unfold Abs.elist
      rw [hgl', hsplit]
      simp [Abs.removeGroup, hel0]
    refine ⟨⟨by rw [rE], fun e => by simp [eN, rE], fun e => by simp [eP, rE],
      fun e => by rw [rE], fun e => by rw [rE], rH, rT, rfl⟩, A.removeGroup c g, ?_, hel'⟩
    obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hgc
    have hrnd : (A.grps c).Nodup := by
      have := hgnd; rw [INV.glist_flatten] at this
      exact List.nodup_flatten.mp this |>.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have hr1 : g ∉ r1 := by
      rw [hrun] at hrnd; exact fun h => (List.nodup_append.mp hrnd).2.2 g h g (by simp) rfl
    have hr2 : g ∉ r2 := by
      rw [hrun] at hrnd
      exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1
    have hgrps' : (A.removeGroup c g).grps c = r1 ++ r2 := by
      simp [Abs.removeGroup, hrun, replace1_mid hr1]
    have hgrpsO : ∀ c', c' ≠ c → (A.removeGroup c g).grps c' = A.grps c' := by
      intro c' h; simp [Abs.removeGroup, h]
    have hchunks' : (A.removeGroup c g).chunks = A.chunks := rfl
    have helts' : (A.removeGroup c g).elts = A.elts := rfl
    refine
      { eList := ?_, eAlloc := ?_, tail := ?_, gList := ?_, gAlloc := ?_, gPos := ?_, gAlive := ?_,
        gOut := ?_, free := ?_, freeNodup := ?_, cList := ?_, cAlloc := ?_, cOut := ?_,
        gEnds := ?_, cEnds := ?_, grp := ?_, chk := ?_, eSorted := ?_, gSorted := ?_,
        cSorted := ?_ }
    · rw [hel']
      have e1 : eN s' = eN s := by funext e; simp [eN, rE]
      have e2 : eP s' = eP s := by funext e; simp [eP, rE]
      rw [e1, e2, rH]; exact hI.eList
    · rw [hel', rE]; exact hI.eAlloc
    · rw [hel', rT]; exact hI.tail
    · rw [hgl']
      have hL := hI.gList
      rw [hsplit] at hL
      have := LList.erase (nxt' := gN s') (prv' := gP s') hL (fun z hz => ?_) (fun z hz => ?_)
      · rw [rFG, hpdef, hndef]
        rw [hpdef, hndef] at this
        by_cases hp0 : p = NIL
        · rw [ite_eq_left hp0] at this; rw [ite_eq_right (not_not.mpr hp0)]; exact this
        · rw [ite_eq_right hp0] at this; rw [ite_eq_left hp0]; exact this
      · have hzg : z ≠ g := fun e => (List.mem_append.mp (e ▸ hz)).elim hg1 hg2
        have hz0 : z ≠ NIL := fun e => hI.gList.nonil (hsplit ▸ e ▸ mem_split_of_mem hz)
        rw [gN', ite_eq_right hzg, hpdef, hndef]
        by_cases hzp : z = p
        · subst hzp; simp [hz0]
        · simp [hzp]
      · have hzg : z ≠ g := fun e => (List.mem_append.mp (e ▸ hz)).elim hg1 hg2
        have hz0 : z ≠ NIL := fun e => hI.gList.nonil (hsplit ▸ e ▸ mem_split_of_mem hz)
        rw [gP', ite_eq_right hzg, hpdef, hndef]
        by_cases hzn : z = n
        · subst hzn; simp [hz0]
        · simp [hzn]
    · intro b hb; rw [unlinkGroup_Gsize]; exact hI.gAlloc b ((hmem' b).mp hb).2
    · rw [unlinkGroup_Gsize]; exact hI.gPos
    · intro b hb1 hb2
      rw [unlinkGroup_Gsize] at hb2
      rw [gA', hmem']
      by_cases h : b = g
      · simp [h]
      · simp only [h, ite_false, ne_eq, not_false_eq_true, true_and]
        exact hI.gAlive b hb1 hb2
    · intro b hb
      rw [hmem'] at hb
      rw [gN', gP']
      by_cases h : b = g
      · simp [h]
      · have hb' : b ∉ A.glist := fun hm => hb ⟨h, hm⟩
        have hbp : ¬ (b = p ∧ p ≠ NIL) := fun ⟨e, hp0⟩ => hb' (e ▸ hpm.resolve_left hp0)
        have hbn : ¬ (b = n ∧ n ≠ NIL) := fun ⟨e, hn0⟩ => hb' (e ▸ hnm.resolve_left hn0)
        simp only [h, hbp, hbn, ite_false]
        exact hI.gOut b hb'
    · intro b hb
      rw [rF] at hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · refine ⟨by unfold NIL at hg0; omega, by rw [unlinkGroup_Gsize]; exact hgs, ?_⟩
        rw [hmem']; simp
      · obtain ⟨x1, x2, x3⟩ := hI.free b hb
        refine ⟨x1, by rw [unlinkGroup_Gsize]; exact x2, ?_⟩
        rw [hmem']; exact fun h => x3 h.2
    · rw [rF]
      refine List.nodup_cons.mpr ⟨fun hm => (hI.free g hm).2.2 hg, hI.freeNodup⟩
    · have e1 : cN s' = cN s := by
        funext z; simp only [cN, hC']; split <;> rfl
      have e2 : cP s' = cP s := by
        funext z; simp only [cP, hC']; split <;> rfl
      rw [hchunks', e1, e2, rFC]; exact hI.cList
    · rw [hchunks', rCs]; exact hI.cAlloc
    · intro z hz
      rw [hchunks'] at hz
      have hzc : z ≠ c := fun e => hz (e ▸ hc)
      simp only [cN, cP, cF, hC', hzc, ite_false]
      exact hI.cOut z hz
    · intro b hb
      have hb' := (hmem' b).mp hb
      rw [unlinkGroup_gF, unlinkGroup_gLs, helts']
      exact hI.gEnds b hb'.2
    · intro c' hc'; change c' ∈ A.chunks at hc'
      simpa only [hcdef] using unlinkGroup_chunkEnds hI hg c' hc'
    · intro b hb e he
      rw [helts'] at he
      simp only [eG, rE]
      exact hI.grp b ((hmem' b).mp hb).2 e he
    · intro c' hc' b hb
      rw [hchunks'] at hc'
      rw [unlinkGroup_gC]
      by_cases hcc : c' = c
      · subst hcc
        rw [hgrps'] at hb
        exact hI.chk c' hc' b (hrun ▸ mem_split_of_mem hb)
      · rw [hgrpsO c' hcc] at hb
        exact hI.chk c' hc' b hb
    · intro b hb
      rw [helts']
      have e1 : eL s' = eL s := by funext e; simp [eL, rE]
      rw [e1]; exact hI.eSorted b ((hmem' b).mp hb).2
    · intro c' hc'
      rw [hchunks'] at hc'
      have e1 : gL s' = gL s := funext unlinkGroup_gL
      rw [e1]
      by_cases hcc : c' = c
      · subst hcc
        rw [hgrps']
        have hs := hI.gSorted c' hc'
        rw [hrun] at hs
        exact isChain_erase hs
      · rw [hgrpsO c' hcc]; exact hI.gSorted c' hc'
    · have : cT s' = cT s := by
        funext z; simp only [cT, hC']; split <;> rfl
      rw [hchunks', this]; exact hI.cSorted
  · rw [hr]; exact EFrame.refl s

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Moving one element to a sibling -/

theorem moveElem_run (s : Core) (g : Nat) :
    (∃ lab, (g ≠ NIL ∧ g < s.Gs.size ∧ gA s g = true ∧ gF s g ≠ NIL) ∧
        gN s (s.Gs.getX g).l = g ∧
        (gF s (s.Gs.getX g).l ≠ NIL → eL s (gLs s (s.Gs.getX g).l) < lab) ∧
        (moveElem g).run s =
          .ok (s.Gs.getX g).l (moveFirstLeft s g (s.Gs.getX g).l (gF s g) lab)) ∨
    (∃ lab, (g ≠ NIL ∧ g < s.Gs.size ∧ gA s g = true ∧ gF s g ≠ NIL) ∧
        gP s (s.Gs.getX g).r = g ∧
        (gF s (s.Gs.getX g).r ≠ NIL → lab < eL s (gF s (s.Gs.getX g).r)) ∧
        (moveElem g).run s =
          .ok (s.Gs.getX g).r (moveLastRight s g (s.Gs.getX g).r (gLs s g) lab)) ∨
    (∃ msg, (moveElem g).run s = .error (.guard msg) s) := by
  unfold moveElem
  simp only [run_getP_bind, run_getG_bind, run_get_bind, run_require_bind]
  by_cases h0 : (g != NIL && decide (g < s.Gs.size) && (s.Gs.getX g).alive &&
      (s.Gs.getX g).first != NIL) = true
  · rw [ite_eq_left h0]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h0
    have C0 : g ≠ NIL ∧ g < s.Gs.size ∧ gA s g = true ∧ gF s g ≠ NIL :=
      ⟨h0.1.1.1, h0.1.1.2, h0.1.2, h0.2⟩
    by_cases hdir : (s.Gs.getX (s.Gs.getX g).l).size ≤ (s.Gs.getX (s.Gs.getX g).r).size
    · rw [ite_eq_left hdir, run_require_bind]
      by_cases hadj : ((s.Gs.getX (s.Gs.getX g).l).next == g) = true
      · rw [ite_eq_left hadj]
        have hadj' : gN s (s.Gs.getX g).l = g := beq_iff_eq.mp hadj
        by_cases he : (s.Gs.getX (s.Gs.getX g).l).first = NIL
        · rw [ite_eq_left (beq_iff_eq.mpr he)]
          left
          refine ⟨1 <<< (s.P.elementBits - 1), C0, hadj', fun h => absurd he h, ?_⟩
          rfl
        · rw [ite_eq_right (fun h => he (beq_iff_eq.mp h))]
          simp only [run_getE_bind]
          rw [run_bind, run_after]
          by_cases hg : (s.E.getX (s.Gs.getX (s.Gs.getX g).l).last).lab + s.P.elementSpacing ≥
            1 <<< s.P.elementBits ∨
              (s.E.getX (s.Gs.getX (s.Gs.getX g).l).last).lab + s.P.elementSpacing ≤
                (s.E.getX (s.Gs.getX (s.Gs.getX g).l).last).lab
          · right; right; exact ⟨_, by rw [ite_eq_left hg]⟩
          · left
            refine ⟨(s.E.getX (s.Gs.getX (s.Gs.getX g).l).last).lab + s.P.elementSpacing, C0, hadj',
              fun _ => ?_, ?_⟩
            · simp only [not_or] at hg; simp only [eL, gLs]; omega
            · rw [ite_eq_right hg]; rfl
      · rw [ite_eq_right hadj]; right; right; exact ⟨_, rfl⟩
    · rw [ite_eq_right hdir, run_require_bind]
      by_cases hadj : ((s.Gs.getX (s.Gs.getX g).r).prev == g) = true
      · rw [ite_eq_left hadj]
        have hadj' : gP s (s.Gs.getX g).r = g := beq_iff_eq.mp hadj
        by_cases he : (s.Gs.getX (s.Gs.getX g).r).first = NIL
        · rw [ite_eq_left (beq_iff_eq.mpr he)]
          right; left
          refine ⟨1 <<< (s.P.elementBits - 1), C0, hadj', fun h => absurd he h, ?_⟩
          rfl
        · rw [ite_eq_right (fun h => he (beq_iff_eq.mp h))]
          simp only [run_getE_bind]
          rw [run_bind, run_before]
          by_cases hg : (s.E.getX (s.Gs.getX (s.Gs.getX g).r).first).lab < s.P.elementSpacing ∨
            s.P.elementSpacing = 0
          · right; right; exact ⟨_, by rw [ite_eq_left hg]⟩
          · right; left
            refine ⟨(s.E.getX (s.Gs.getX (s.Gs.getX g).r).first).lab - s.P.elementSpacing, C0,
              hadj',
              fun _ => ?_, ?_⟩
            · simp only [not_or] at hg; simp only [eL, gF]; omega
            · rw [ite_eq_right hg]; rfl
      · rw [ite_eq_right hadj]; right; right; exact ⟨_, rfl⟩
  · rw [ite_eq_right h0]; right; right; exact ⟨_, rfl⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
section movefirst
variable {s : Core} {g gl e lab : Nat}

theorem moveFirstLeft_E :
    (moveFirstLeft s g gl e lab).E = s.E.modify e fun X => { X with grp := gl, lab := lab } := rfl

theorem moveFirstLeft_gF (hgl : gl ≠ g) (hg : g < s.Gs.size) (hl : gl < s.Gs.size) (z : Nat) :
    gF (moveFirstLeft s g gl e lab) z =
      if z = gl then (if gF s gl = NIL then e else gF s gl)
      else if z = g then (if gF s g = gLs s g then NIL else eN s e) else gF s z := by
  simp only [moveFirstLeft, gF, gLs, eN, Array.getX_modify, Array.size_modify', beq_iff_eq]
  by_cases h1 : z = gl
  · subst h1; simp [hl,  Ne.symm hgl, ]
  · by_cases h2 : z = g
    · subst h2
      simp [hg, Ne.symm h1, h1, apply_ite (f := Group.first)]
    · simp [Ne.symm h1, Ne.symm h2, h1, h2]

theorem moveFirstLeft_gLs (hgl : gl ≠ g) (hg : g < s.Gs.size) (hl : gl < s.Gs.size) (z : Nat) :
    gLs (moveFirstLeft s g gl e lab) z =
      if z = gl then e
      else if z = g then (if gF s g = gLs s g then NIL else gLs s g) else gLs s z := by
  simp only [moveFirstLeft, gF, gLs, Array.getX_modify, Array.size_modify', beq_iff_eq]
  by_cases h1 : z = gl
  · subst h1; simp [hl,  Ne.symm hgl, ]
  · by_cases h2 : z = g
    · subst h2
      simp [hg, Ne.symm h1, h1,  apply_ite (f := Group.last)]
    · simp [Ne.symm h1, Ne.symm h2, h1, h2]

theorem moveFirstLeft_same :
    (∀ z, gN (moveFirstLeft s g gl e lab) z = gN s z) ∧
    (∀ z, gP (moveFirstLeft s g gl e lab) z = gP s z) ∧
    (∀ z, gC (moveFirstLeft s g gl e lab) z = gC s z) ∧
    (∀ z, gL (moveFirstLeft s g gl e lab) z = gL s z) ∧
    (∀ z, gA (moveFirstLeft s g gl e lab) z = gA s z) ∧
    (moveFirstLeft s g gl e lab).Gs.size = s.Gs.size ∧
    (∀ z, eN (moveFirstLeft s g gl e lab) z = eN s z) ∧
    (∀ z, eP (moveFirstLeft s g gl e lab) z = eP s z) ∧
    (∀ z, ((moveFirstLeft s g gl e lab).E.getX z).live = (s.E.getX z).live) ∧
    (∀ z, ((moveFirstLeft s g gl e lab).E.getX z).h = (s.E.getX z).h) ∧
    (moveFirstLeft s g gl e lab).E.size = s.E.size ∧
    (moveFirstLeft s g gl e lab).C = s.C ∧ (moveFirstLeft s g gl e lab).freeG = s.freeG ∧
    (moveFirstLeft s g gl e lab).head = s.head ∧ (moveFirstLeft s g gl e lab).tail = s.tail ∧
    (moveFirstLeft s g gl e lab).firstGroup = s.firstGroup ∧
    (moveFirstLeft s g gl e lab).firstChunk = s.firstChunk := by
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, by simp [moveFirstLeft],
    fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, by simp [moveFirstLeft], rfl, rfl, rfl, rfl,
    rfl, rfl⟩ <;>
    simp only [moveFirstLeft, gN, gP, gC, gL, gA, eN, eP, Array.getX_modify, Array.size_modify',
      apply_ite (f := Group.next), apply_ite (f := Group.prev), apply_ite (f := Group.chk),
      apply_ite (f := Group.lab), apply_ite (f := Group.alive), apply_ite (f := Elem.next),
      apply_ite (f := Elem.prev), apply_ite (f := Elem.live), apply_ite (f := Elem.h)] <;>
    split_ifs <;> rfl

theorem moveFirstLeft_eG (z : Nat) :
    eG (moveFirstLeft s g gl e lab) z = if z = e ∧ e < s.E.size then gl else eG s z := by
  simp only [moveFirstLeft, eG, Array.getX_modify, apply_ite (f := Elem.grp)]
  by_cases h : z = e
  · simp [h]
  · simp [h, Ne.symm h]

theorem moveFirstLeft_eL (z : Nat) :
    eL (moveFirstLeft s g gl e lab) z = if z = e ∧ e < s.E.size then lab else eL s z := by
  simp only [moveFirstLeft, eL, Array.getX_modify, apply_ite (f := Elem.lab)]
  by_cases h : z = e
  · simp [h]
  · simp [h, Ne.symm h]

end movefirst

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem INV.mem_of_gN {s : Core} {A : Abs} (h : INV s A) {a b : Nat} (hab : gN s a = b)
    (hb : b ≠ NIL) : a ∈ A.glist := by
  by_contra hm; exact hb (hab ▸ (h.gOut a hm).1)

theorem INV.mem_of_gP {s : Core} {A : Abs} (h : INV s A) {a b : Nat} (hab : gP s a = b)
    (hb : b ≠ NIL) : a ∈ A.glist := by
  by_contra hm; exact hb (hab ▸ (h.gOut a hm).2)

theorem INV.run_nodup {s : Core} {A : Abs} (h : INV s A) {g : Nat} (hg : g ∈ A.glist) :
    (A.elts g).Nodup := by
  have := h.eList.nodup; rw [INV.elist_flatten] at this
  exact List.nodup_flatten.mp this |>.1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩)

theorem INV.runs_disjoint {s : Core} {A : Abs} (h : INV s A) {g g' e : Nat} (hg : g ∈ A.glist)
    (hg' : g' ∈ A.glist) (he : e ∈ A.elts g) (he' : e ∈ A.elts g') : g = g' := by
  rw [← h.grp g hg e he, h.grp g' hg' e he']

/-- **Moving the first element of `g` to the end of the group before it preserves INV-S.** -/
theorem inv_moveFirstLeft {s : Core} {A : Abs} (hI : INV s A) {g gl lab : Nat}
    (hg : g ∈ A.glist) (hne : gF s g ≠ NIL) (hadj : gN s gl = g)
    (hlab : gF s gl ≠ NIL → eL s (gLs s gl) < lab) :
    ∃ A', INV (moveFirstLeft s g gl (gF s g) lab) A' ∧ A'.elist = A.elist := by
  have hg0 : g ≠ NIL := fun e => hI.gList.nonil (e ▸ hg)
  have hgl := hI.mem_of_gN hadj hg0
  have hsucc : succOf A.glist gl = g := by rw [← hI.gList.next gl hgl]; exact hadj
  have hglg : gl ≠ g := by
    intro e; subst e
    exact succOf_ne_self hI.gList.nodup gl hg0 hsucc
  obtain ⟨l1, l2, hsplit⟩ := succOf_split hsucc hg0
  generalize hedef : gF s g = e at hne ⊢
  have hgE := hI.gEnds g hg
  obtain ⟨rest, hrun⟩ : ∃ rest, A.elts g = e :: rest := by
    cases h : A.elts g with
    | nil => rw [h] at hgE; exact absurd (hedef ▸ hgE.1) hne
    | cons a t =>
      rw [h] at hgE
      simp only [Ends, List.headD_cons] at hgE
      exact ⟨t, by rw [← hedef, hgE.1]⟩
  have he : e ∈ A.elist := A.elts_sub_elist hg (by rw [hrun]; simp)
  have hes := ((hI.eAlloc e).mp he).2
  have hrnd := hI.run_nodup hg
  rw [hrun] at hrnd
  have her : e ∉ rest := (List.nodup_cons.mp hrnd).1
  -- members
  have hnd := hI.gList.nodup
  rw [hsplit] at hnd
  have hnd2 := (List.nodup_append.mp hnd).2.1
  have hgl2 : gl ∉ l2 := fun h => (List.nodup_cons.mp hnd2).1 (by simp [h])
  have hg2 : g ∉ l2 := (List.nodup_cons.mp (List.nodup_cons.mp hnd2).2).1
  have hdis := (List.nodup_append.mp hnd).2.2
  have hl1 : ∀ b ∈ l1 ++ l2, b ≠ gl ∧ b ≠ g := by
    intro b hb
    simp only [List.mem_append] at hb
    rcases hb with hb | hb
    · exact ⟨hdis b hb gl (by simp), hdis b hb g (by simp)⟩
    · exact ⟨fun e => hgl2 (e ▸ hb), fun e => hg2 (e ▸ hb)⟩
  let A' : Abs := { A with elts := fun b => if b = gl then A.elts gl ++ [e]
                                        else if b = g then rest else A.elts b }
  have hglA : A'.glist = A.glist := rfl
  have hel : A'.elist = A.elist := by
    unfold Abs.elist; rw [hglA, hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, A', ite_true, hglg, Ne.symm hglg, ite_false]
    have h1 : l1.flatMap (fun b => if b = gl then A.elts gl ++ [e] else if b = g then rest
        else A.elts b) = l1.flatMap A.elts :=
      List.flatMap_congr fun b hb => by
        have := hl1 b (by simp [hb]); simp [this.1, this.2]
    have h2 : l2.flatMap (fun b => if b = gl then A.elts gl ++ [e] else if b = g then rest
        else A.elts b) = l2.flatMap A.elts :=
      List.flatMap_congr fun b hb => by
        have := hl1 b (by simp [hb]); simp [this.1, this.2]
    rw [h1, h2, hrun]; simp
  refine ⟨A', ?_, hel⟩
  obtain ⟨sN, sP, sC, sL, sA, sGs, seN, seP, -, -, sEs, sCC, sF, sH, sT, sFG, sFC⟩ :=
    moveFirstLeft_same (s := s) (g := g) (gl := gl) (e := e) (lab := lab)
  have hgs := hI.gAlloc g hg
  have hgls := hI.gAlloc gl hgl
  have gF' := moveFirstLeft_gF (s := s) (e := e) (lab := lab) hglg hgs hgls
  have gLs' := moveFirstLeft_gLs (s := s) (e := e) (lab := lab) hglg hgs hgls
  have eG' := moveFirstLeft_eG (s := s) (g := g) (gl := gl) (e := e) (lab := lab)
  have eL' := moveFirstLeft_eL (s := s) (g := g) (gl := gl) (e := e) (lab := lab)
  have helts : ∀ b, A'.elts b = if b = gl then A.elts gl ++ [e] else if b = g then rest
      else A.elts b := fun b => rfl
  -- `e` lies only in `g`'s run
  have heO : ∀ b ∈ A.glist, b ≠ g → e ∉ A.elts b := fun b hb hbg hm =>
    hbg (hI.runs_disjoint hb hg hm (by rw [hrun]; simp))
  refine
    { eList := ?_, eAlloc := ?_, tail := ?_, gList := ?_, gAlloc := ?_, gPos := ?_, gAlive := ?_,
      gOut := ?_, free := ?_, freeNodup := ?_, cList := ?_, cAlloc := ?_, cOut := ?_,
      gEnds := ?_, cEnds := ?_, grp := ?_, chk := ?_, eSorted := ?_, gSorted := ?_,
      cSorted := ?_ }
  · rw [hel, funext seN, funext seP, sH]; exact hI.eList
  · rw [hel, sEs]; exact hI.eAlloc
  · rw [hel, sT]; exact hI.tail
  · rw [hglA, funext sN, funext sP, sFG]; exact hI.gList
  · intro b hb; rw [sGs]; exact hI.gAlloc b hb
  · rw [sGs]; exact hI.gPos
  · intro b h1 h2; rw [sA, hglA]; rw [sGs] at h2; exact hI.gAlive b h1 h2
  · intro b hb; rw [sN, sP]; exact hI.gOut b hb
  · rw [sF, sGs]; exact hI.free
  · rw [sF]; exact hI.freeNodup
  · have e1 : cN (moveFirstLeft s g gl e lab) = cN s := by funext c; simp [cN, sCC]
    have e2 : cP (moveFirstLeft s g gl e lab) = cP s := by funext c; simp [cP, sCC]
    rw [e1, e2, sFC]; exact hI.cList
  · rw [sCC]; exact hI.cAlloc
  · intro c hc; simp only [cN, cP, cF, sCC]; exact hI.cOut c hc
  · intro b hb
    rw [gF', gLs', helts]
    by_cases h1 : b = gl
    · subst h1
      simp only [ite_true]
      have hE := hI.gEnds b hgl
      refine ⟨?_, by simp⟩
      by_cases hn : gF s b = NIL
      · rw [ite_eq_left hn]
        rw [hE.1] at hn
        cases h : A.elts b with
        | nil => simp
        | cons a t =>
          rw [h] at hn
          change a = NIL at hn
          exact absurd (hn ▸ A.elts_sub_elist hgl (h ▸ (by simp : a ∈ a :: t))) hI.eList.nonil
      · rw [ite_eq_right hn, hE.1]
        cases h : A.elts b with
        | nil => rw [h] at hE; exact absurd hE.1 hn
        | cons a t => simp
    · by_cases h2 : b = g
      · subst h2
        simp only [h1, ite_false, ite_true]
        rw [hrun] at hgE
        by_cases hfl : gF s b = gLs s b
        · simp only [hfl, ite_true]
          -- a one-element run
          cases rest with
          | nil => simp [Ends]
          | cons a t =>
            exfalso
            rw [hgE.1, hgE.2] at hfl
            simp only [List.headD_cons] at hfl
            rw [show e :: a :: t = [e] ++ a :: t by simp, getLastD_append_cons] at hfl
            exact her (by rw [hfl]; exact getLastD_cons_mem a t NIL)
        · simp only [hfl, ite_false]
          cases rest with
          | nil => exact absurd (by rw [hgE.1, hgE.2]; simp) hfl
          | cons a t =>
            refine ⟨?_, ?_⟩
            · rw [hI.eN_in_run hb (by rw [hrun]; simp) (by
                rw [hrun, show e :: a :: t = [e] ++ a :: t by simp,
                  List.getLast?_append_of_ne_nil _ (by simp)]
                intro h; exact her (List.mem_of_getLast? h)), hrun]
              simp [succOf_cons']
            · rw [hgE.2, show e :: a :: t = [e] ++ a :: t by simp, getLastD_append_cons]
      · simp only [h1, h2, ite_false]; exact hI.gEnds b hb
  · intro c hc; simp only [cF, cLs, sCC]; exact hI.cEnds c hc
  · intro b hb z hz
    rw [helts] at hz
    rw [eG']
    by_cases h1 : b = gl
    · rw [ite_eq_left h1, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · have hze : z ≠ e := fun e' => heO gl hgl hglg (e' ▸ hz)
        rw [ite_eq_right (fun h => hze h.1)]; exact hI.grp b hb z (h1 ▸ hz)
      · rw [ite_eq_left ⟨rfl, hes⟩, h1]
    · by_cases h2 : b = g
      · rw [ite_eq_right h1, ite_eq_left h2] at hz
        have hze : z ≠ e := fun e' => her (e' ▸ hz)
        rw [ite_eq_right (fun h => hze h.1)]
        exact hI.grp b hb z (by rw [h2, hrun]; simp [hz])
      · rw [ite_eq_right h1, ite_eq_right h2] at hz
        have hze : z ≠ e := fun e' => heO b hb h2 (e' ▸ hz)
        rw [ite_eq_right (fun h => hze h.1)]; exact hI.grp b hb z hz
  · intro c hc b hb; rw [sC]; exact hI.chk c hc b hb
  · intro b hb
    rw [helts]
    by_cases h1 : b = gl
    · subst h1
      simp only [ite_true]
      have hs := hI.eSorted b hgl
      have hmap : (A.elts b).map (eL (moveFirstLeft s g b e lab)) = (A.elts b).map (eL s) := by
        refine List.map_congr_left fun z hz => ?_
        have hze : z ≠ e := fun e' => heO b hgl hglg (e' ▸ hz)
        rw [eL', ite_eq_right (fun (h : z = e ∧ e < s.E.size) => hze h.1)]
      rw [List.map_append, hmap, List.isChain_append]
      refine ⟨hs, by simp, ?_⟩
      intro x hx y hy
      simp only [List.map_cons, List.map_nil, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hy
      subst hy
      rw [eL', ite_eq_left ⟨rfl, hes⟩]
      have hE := hI.gEnds b hgl
      cases h : A.elts b with
      | nil => rw [h] at hx; simp at hx
      | cons a t =>
        rw [h] at hx hE
        have hne' : gF s b ≠ NIL := by
          rw [hE.1]; simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, ne_eq]
          exact fun h0 => hI.eList.nonil (h0 ▸ A.elts_sub_elist hgl (h ▸ (by simp : a ∈ a :: t)))
        have := hlab hne'
        rw [hE.2] at this
        rw [List.getLast?_map] at hx
        simp only [Option.mem_def, Option.map_eq_some_iff] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        rw [List.getLastD_eq_getLast?, hw] at this
        exact this
    · by_cases h2 : b = g
      · subst h2
        simp only [h1, ite_false, ite_true]
        have hs := hI.eSorted b hb
        rw [hrun, List.map_cons, List.isChain_cons] at hs
        have hmap : rest.map (eL (moveFirstLeft s b gl e lab)) = rest.map (eL s) := by
          refine List.map_congr_left fun z hz => ?_
          rw [eL', ite_eq_right (fun (h : z = e ∧ e < s.E.size) => her (h.1 ▸ hz))]
        rw [hmap]; exact hs.2
      · simp only [h1, h2, ite_false]
        have hmap : (A.elts b).map (eL (moveFirstLeft s g gl e lab)) = (A.elts b).map (eL s) := by
          refine List.map_congr_left fun z hz => ?_
          rw [eL', ite_eq_right (fun (h : z = e ∧ e < s.E.size) => heO b hb h2 (h.1 ▸ hz))]
        rw [hmap]; exact hI.eSorted b hb
  · intro c hc; rw [funext sL]; exact hI.gSorted c hc
  · have : cT (moveFirstLeft s g gl e lab) = cT s := by funext c; simp [cT, sCC]
    rw [this]; exact hI.cSorted

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
section movelast
variable {s : Core} {g gr e lab : Nat}

theorem moveLastRight_gF (hgr : gr ≠ g) (hg : g < s.Gs.size) (hr : gr < s.Gs.size) (z : Nat) :
    gF (moveLastRight s g gr e lab) z =
      if z = gr then e
      else if z = g then (if gF s g = gLs s g then NIL else gF s g) else gF s z := by
  simp only [moveLastRight, gF, gLs, Array.getX_modify, Array.size_modify', beq_iff_eq]
  by_cases h1 : z = gr
  · subst h1; simp [hr,  Ne.symm hgr, ]
  · by_cases h2 : z = g
    · subst h2
      simp [hg, Ne.symm h1, h1, apply_ite (f := Group.first)]
    · simp [Ne.symm h1, Ne.symm h2, h1, h2]

theorem moveLastRight_gLs (hgr : gr ≠ g) (hg : g < s.Gs.size) (hr : gr < s.Gs.size) (z : Nat) :
    gLs (moveLastRight s g gr e lab) z =
      if z = gr then (if gF s gr = NIL then e else gLs s gr)
      else if z = g then (if gF s g = gLs s g then NIL else eP s e) else gLs s z := by
  simp only [moveLastRight, gF, gLs, eP, Array.getX_modify, Array.size_modify', beq_iff_eq]
  by_cases h1 : z = gr
  · subst h1; simp [hr,  Ne.symm hgr, ]
  · by_cases h2 : z = g
    · subst h2
      simp [hg, Ne.symm h1, h1,  apply_ite (f := Group.last)]
    · simp [Ne.symm h1, Ne.symm h2, h1, h2]

theorem moveLastRight_same :
    (∀ z, gN (moveLastRight s g gr e lab) z = gN s z) ∧
    (∀ z, gP (moveLastRight s g gr e lab) z = gP s z) ∧
    (∀ z, gC (moveLastRight s g gr e lab) z = gC s z) ∧
    (∀ z, gL (moveLastRight s g gr e lab) z = gL s z) ∧
    (∀ z, gA (moveLastRight s g gr e lab) z = gA s z) ∧
    (moveLastRight s g gr e lab).Gs.size = s.Gs.size ∧
    (∀ z, eN (moveLastRight s g gr e lab) z = eN s z) ∧
    (∀ z, eP (moveLastRight s g gr e lab) z = eP s z) ∧
    (∀ z, ((moveLastRight s g gr e lab).E.getX z).live = (s.E.getX z).live) ∧
    (∀ z, ((moveLastRight s g gr e lab).E.getX z).h = (s.E.getX z).h) ∧
    (moveLastRight s g gr e lab).E.size = s.E.size ∧
    (moveLastRight s g gr e lab).C = s.C ∧ (moveLastRight s g gr e lab).freeG = s.freeG ∧
    (moveLastRight s g gr e lab).head = s.head ∧ (moveLastRight s g gr e lab).tail = s.tail ∧
    (moveLastRight s g gr e lab).firstGroup = s.firstGroup ∧
    (moveLastRight s g gr e lab).firstChunk = s.firstChunk := by
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, by simp [moveLastRight],
    fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, by simp [moveLastRight], rfl, rfl, rfl, rfl,
    rfl, rfl⟩ <;>
    simp only [moveLastRight, gN, gP, gC, gL, gA, eN, eP, Array.getX_modify, Array.size_modify',
      apply_ite (f := Group.next), apply_ite (f := Group.prev), apply_ite (f := Group.chk),
      apply_ite (f := Group.lab), apply_ite (f := Group.alive), apply_ite (f := Elem.next),
      apply_ite (f := Elem.prev), apply_ite (f := Elem.live), apply_ite (f := Elem.h)] <;>
    split_ifs <;> rfl

theorem moveLastRight_eG (z : Nat) :
    eG (moveLastRight s g gr e lab) z = if z = e ∧ e < s.E.size then gr else eG s z := by
  simp only [moveLastRight, eG, Array.getX_modify, apply_ite (f := Elem.grp)]
  by_cases h : z = e
  · simp [h]
  · simp [h, Ne.symm h]

theorem moveLastRight_eL (z : Nat) :
    eL (moveLastRight s g gr e lab) z = if z = e ∧ e < s.E.size then lab else eL s z := by
  simp only [moveLastRight, eL, Array.getX_modify, apply_ite (f := Elem.lab)]
  by_cases h : z = e
  · simp [h]
  · simp [h, Ne.symm h]

end movelast

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- In INV-S, the element before `x` inside its run is its predecessor in the element list. -/
theorem INV.eP_in_run {s : Core} {A : Abs} (h : INV s A) {g x : Nat} (hg : g ∈ A.glist)
    (hx : x ∈ A.elts g) (hf : (A.elts g).head? ≠ some x) : eP s x = predOf (A.elts g) x := by
  rw [h.eList.prev x (A.elts_sub_elist hg hx), INV.elist_flatten]
  have hnd := h.eList.nodup
  rw [INV.elist_flatten] at hnd
  exact predOf_flatten hnd (List.mem_map.mpr ⟨g, hg, rfl⟩) hx hf

/-- **Moving the last element of `g` to the front of the group after it preserves INV-S.** -/
theorem inv_moveLastRight {s : Core} {A : Abs} (hI : INV s A) {g gr lab : Nat}
    (hg : g ∈ A.glist) (hne : gF s g ≠ NIL) (hadj : gP s gr = g)
    (hlab : gF s gr ≠ NIL → lab < eL s (gF s gr)) :
    ∃ A', INV (moveLastRight s g gr (gLs s g) lab) A' ∧ A'.elist = A.elist := by
  have hg0 : g ≠ NIL := fun e => hI.gList.nonil (e ▸ hg)
  have hgr := hI.mem_of_gP hadj hg0
  have hpred : predOf A.glist gr = g := by rw [← hI.gList.prev gr hgr]; exact hadj
  have hgrg : gr ≠ g := by
    intro e; subst e
    exact predOf_ne_self hI.gList.nodup gr hg0 hpred
  obtain ⟨l1, l2, hsplit⟩ := predOf_split hpred hg0
  have hgE := hI.gEnds g hg
  generalize hedef : gLs s g = e
  obtain ⟨rest, hrun⟩ : ∃ rest, A.elts g = rest ++ [e] := by
    rcases (A.elts g).eq_nil_or_concat with h | ⟨r, a, h⟩
    · rw [h] at hgE; exact absurd hgE.1 hne
    · refine ⟨r, ?_⟩
      rw [h]; rw [h] at hgE
      have := hgE.2; simp only [List.concat_eq_append,
        ] at this; rw [← hedef, this]; simp
  have he : e ∈ A.elist := A.elts_sub_elist hg (by rw [hrun]; simp)
  have hes := ((hI.eAlloc e).mp he).2
  have hrnd := hI.run_nodup hg
  rw [hrun] at hrnd
  have her : e ∉ rest := fun h => (List.nodup_append.mp hrnd).2.2 e h e (by simp) rfl
  have hnd := hI.gList.nodup
  rw [hsplit] at hnd
  have hnd2 := (List.nodup_append.mp hnd).2.1
  have hg2' : g ∉ l2 := fun h => (List.nodup_cons.mp hnd2).1 (by simp [h])
  have hgr2 : gr ∉ l2 := (List.nodup_cons.mp (List.nodup_cons.mp hnd2).2).1
  have hdis := (List.nodup_append.mp hnd).2.2
  have hl1 : ∀ b ∈ l1 ++ l2, b ≠ gr ∧ b ≠ g := by
    intro b hb
    simp only [List.mem_append] at hb
    rcases hb with hb | hb
    · exact ⟨hdis b hb gr (by simp), hdis b hb g (by simp)⟩
    · exact ⟨fun e => hgr2 (e ▸ hb), fun e => hg2' (e ▸ hb)⟩
  let A' : Abs := { A with elts := fun b => if b = gr then e :: A.elts gr
                                        else if b = g then rest else A.elts b }
  have hglA : A'.glist = A.glist := rfl
  have hel : A'.elist = A.elist := by
    unfold Abs.elist; rw [hglA, hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, A', ite_true, hgrg, Ne.symm hgrg, ite_false]
    have h1 : l1.flatMap (fun b => if b = gr then e :: A.elts gr else if b = g then rest
        else A.elts b) = l1.flatMap A.elts :=
      List.flatMap_congr fun b hb => by
        have := hl1 b (by simp [hb]); simp [this.1, this.2]
    have h2 : l2.flatMap (fun b => if b = gr then e :: A.elts gr else if b = g then rest
        else A.elts b) = l2.flatMap A.elts :=
      List.flatMap_congr fun b hb => by
        have := hl1 b (by simp [hb]); simp [this.1, this.2]
    rw [h1, h2, hrun]; simp
  refine ⟨A', ?_, hel⟩
  obtain ⟨sN, sP, sC, sL, sA, sGs, seN, seP, -, -, sEs, sCC, sF, sH, sT, sFG, sFC⟩ :=
    moveLastRight_same (s := s) (g := g) (gr := gr) (e := e) (lab := lab)
  have hgs := hI.gAlloc g hg
  have hgrs := hI.gAlloc gr hgr
  have gF' := moveLastRight_gF (s := s) (e := e) (lab := lab) hgrg hgs hgrs
  have gLs' := moveLastRight_gLs (s := s) (e := e) (lab := lab) hgrg hgs hgrs
  have eG' := moveLastRight_eG (s := s) (g := g) (gr := gr) (e := e) (lab := lab)
  have eL' := moveLastRight_eL (s := s) (g := g) (gr := gr) (e := e) (lab := lab)
  have helts : ∀ b, A'.elts b = if b = gr then e :: A.elts gr else if b = g then rest
      else A.elts b := fun b => rfl
  have heO : ∀ b ∈ A.glist, b ≠ g → e ∉ A.elts b := fun b hb hbg hm =>
    hbg (hI.runs_disjoint hb hg hm (by rw [hrun]; simp))
  refine
    { eList := ?_, eAlloc := ?_, tail := ?_, gList := ?_, gAlloc := ?_, gPos := ?_, gAlive := ?_,
      gOut := ?_, free := ?_, freeNodup := ?_, cList := ?_, cAlloc := ?_, cOut := ?_,
      gEnds := ?_, cEnds := ?_, grp := ?_, chk := ?_, eSorted := ?_, gSorted := ?_,
      cSorted := ?_ }
  · rw [hel, funext seN, funext seP, sH]; exact hI.eList
  · rw [hel, sEs]; exact hI.eAlloc
  · rw [hel, sT]; exact hI.tail
  · rw [hglA, funext sN, funext sP, sFG]; exact hI.gList
  · intro b hb; rw [sGs]; exact hI.gAlloc b hb
  · rw [sGs]; exact hI.gPos
  · intro b h1 h2; rw [sA, hglA]; rw [sGs] at h2; exact hI.gAlive b h1 h2
  · intro b hb; rw [sN, sP]; exact hI.gOut b hb
  · rw [sF, sGs]; exact hI.free
  · rw [sF]; exact hI.freeNodup
  · have e1 : cN (moveLastRight s g gr e lab) = cN s := by funext c; simp [cN, sCC]
    have e2 : cP (moveLastRight s g gr e lab) = cP s := by funext c; simp [cP, sCC]
    rw [e1, e2, sFC]; exact hI.cList
  · rw [sCC]; exact hI.cAlloc
  · intro c hc; simp only [cN, cP, cF, sCC]; exact hI.cOut c hc
  · intro b hb
    rw [gF', gLs', helts]
    by_cases h1 : b = gr
    · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left h1]
      have hE := hI.gEnds gr hgr
      refine ⟨by simp, ?_⟩
      by_cases hn : gF s gr = NIL
      · rw [ite_eq_left hn]
        rw [hE.1] at hn
        cases h : A.elts gr with
        | nil => simp
        | cons a t =>
          rw [h] at hn
          change a = NIL at hn
          exact absurd (hn ▸ A.elts_sub_elist hgr (h ▸ (by simp : a ∈ a :: t))) hI.eList.nonil
      · rw [ite_eq_right hn, hE.2]
        cases h : A.elts gr with
        | nil => rw [h] at hE; exact absurd hE.1 hn
        | cons a t =>
          rw [show e :: a :: t = [e] ++ a :: t by simp, getLastD_append_cons]
    · by_cases h2 : b = g
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2, ite_eq_right h1,
        ite_eq_left h2]
        rw [hrun] at hgE
        by_cases hfl : gF s g = gLs s g
        · simp only [hfl, ite_true]
          rcases rest.eq_nil_or_concat with hr | ⟨r, a, hr⟩
          · subst hr; exact ⟨rfl, rfl⟩
          · exfalso
            subst hr
            rw [hgE.1, hgE.2, show r.concat a ++ [e] = (r ++ [a]) ++ e :: [] by simp,
              getLastD_append_cons] at hfl
            rcases r with _ | ⟨b0, r'⟩
            · change a = e at hfl
              exact her (by rw [← hfl]; simp)
            · change b0 = e at hfl
              exact her (by rw [← hfl]; simp)
        · simp only [hfl, ite_false]
          rcases rest.eq_nil_or_concat with hr | ⟨r, a, hr⟩
          · subst hr; exact absurd (by rw [hgE.1, hgE.2]; simp) hfl
          · subst hr
            refine ⟨?_, ?_⟩
            · rw [hgE.1]; rcases r with _ | ⟨b0, r'⟩ <;> simp
            · rw [hI.eP_in_run hb (by rw [h2, hrun]; simp) (by
                rw [h2, hrun]; rcases r with _ | ⟨b0, r'⟩
                · simp only [List.concat_eq_append, List.nil_append, List.cons_append,
                  List.head?_cons, ne_eq,
                    Option.some.injEq]; intro h0; exact her (by simp [h0])
                · simp only [List.concat_eq_append, List.cons_append, List.append_assoc,
                  List.nil_append, List.head?_cons,
                    ne_eq, Option.some.injEq]; intro h0; exact her (by simp [h0])), h2, hrun]
              have hnd3 : ((r ++ [a]) ++ e :: []).Nodup := by simpa using hrnd
              rw [show r.concat a ++ [e] = (r ++ [a]) ++ e :: [] by simp, predOf_mid hnd3]
              simp
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2, ite_eq_right h1,
        ite_eq_right h2]; exact hI.gEnds b hb
  · intro c hc; simp only [cF, cLs, sCC]; exact hI.cEnds c hc
  · intro b hb z hz
    rw [helts] at hz
    rw [eG']
    by_cases h1 : b = gr
    · rw [ite_eq_left h1, List.mem_cons] at hz
      rcases hz with rfl | hz
      · rw [ite_eq_left ⟨rfl, hes⟩, h1]
      · have hze : z ≠ e := fun e' => heO gr hgr hgrg (e' ▸ hz)
        rw [ite_eq_right (fun h => hze h.1)]; exact hI.grp b hb z (h1 ▸ hz)
    · by_cases h2 : b = g
      · rw [ite_eq_right h1, ite_eq_left h2] at hz
        have hze : z ≠ e := fun e' => her (e' ▸ hz)
        rw [ite_eq_right (fun h => hze h.1)]
        exact hI.grp b hb z (by rw [h2, hrun]; simp [hz])
      · rw [ite_eq_right h1, ite_eq_right h2] at hz
        have hze : z ≠ e := fun e' => heO b hb h2 (e' ▸ hz)
        rw [ite_eq_right (fun h => hze h.1)]; exact hI.grp b hb z hz
  · intro c hc b hb; rw [sC]; exact hI.chk c hc b hb
  · intro b hb
    rw [helts]
    by_cases h1 : b = gr
    · rw [ite_eq_left h1]
      have hs := hI.eSorted gr hgr
      have hmap : (A.elts gr).map (eL (moveLastRight s g gr e lab)) = (A.elts gr).map (eL s) := by
        refine List.map_congr_left fun z hz => ?_
        have hze : z ≠ e := fun e' => heO gr hgr hgrg (e' ▸ hz)
        rw [eL', ite_eq_right (fun (h : z = e ∧ e < s.E.size) => hze h.1)]
      rw [List.map_cons, hmap, List.isChain_cons]
      refine ⟨?_, hs⟩
      intro y hy
      rw [eL', ite_eq_left ⟨rfl, hes⟩]
      have hE := hI.gEnds gr hgr
      cases h : A.elts gr with
      | nil => rw [h] at hy; simp at hy
      | cons a t =>
        rw [h] at hy hE
        simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        have hne' : gF s gr ≠ NIL := by
          rw [hE.1]; simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, ne_eq]
          exact fun h0 => hI.eList.nonil (h0 ▸ A.elts_sub_elist hgr (h ▸ (by simp : a ∈ a :: t)))
        have := hlab hne'
        rw [hE.1] at this; simpa using this
    · by_cases h2 : b = g
      · rw [ite_eq_right h1, ite_eq_left h2]
        have hs := hI.eSorted g hg
        rw [hrun, List.map_append, List.isChain_append] at hs
        have hmap : rest.map (eL (moveLastRight s g gr e lab)) = rest.map (eL s) := by
          refine List.map_congr_left fun z hz => ?_
          rw [eL', ite_eq_right (fun (h : z = e ∧ e < s.E.size) => her (h.1 ▸ hz))]
        rw [hmap]; exact hs.1
      · rw [ite_eq_right h1, ite_eq_right h2]
        have hmap : (A.elts b).map (eL (moveLastRight s g gr e lab)) = (A.elts b).map (eL s) := by
          refine List.map_congr_left fun z hz => ?_
          rw [eL', ite_eq_right (fun (h : z = e ∧ e < s.E.size) => heO b hb h2 (h.1 ▸ hz))]
        rw [hmap]; exact hI.eSorted b hb
  · intro c hc; rw [funext sL]; exact hI.gSorted c hc
  · have : cT (moveLastRight s g gr e lab) = cT s := by funext c; simp [cT, sCC]
    rw [this]; exact hI.cSorted

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem good_moveElem (g : Nat) : Good (moveElem g) := by
  intro s A hI
  rcases moveElem_run s g with ⟨lab, ⟨hg0, hgs, hga, hne⟩, hadj, hlab, hr⟩ |
      ⟨lab, ⟨hg0, hgs, hga, hne⟩, hadj, hlab, hr⟩ | ⟨msg, hr⟩
  · rw [hr]
    have hg := hI.mem_of_alive hg0 hgs hga
    obtain ⟨A', h1, h2⟩ := inv_moveFirstLeft hI hg hne hadj hlab
    obtain ⟨-, -, -, -, -, -, seN, seP, sLive, sH, sEs, -, -, sHd, sT, -, -⟩ :=
      moveFirstLeft_same (s := s) (g := g) (gl := (s.Gs.getX g).l) (e := gF s g) (lab := lab)
    exact ⟨⟨sEs, seN, seP, sLive, sH, sHd, sT, rfl⟩, A', h1, h2⟩
  · rw [hr]
    have hg := hI.mem_of_alive hg0 hgs hga
    obtain ⟨A', h1, h2⟩ := inv_moveLastRight hI hg hne hadj hlab
    obtain ⟨-, -, -, -, -, -, seN, seP, sLive, sH, sEs, -, -, sHd, sT, -, -⟩ :=
      moveLastRight_same (s := s) (g := g) (gr := (s.Gs.getX g).r) (e := gLs s g) (lab := lab)
    exact ⟨⟨sEs, seN, seP, sLive, sH, sHd, sT, rfl⟩, A', h1, h2⟩
  · rw [hr]; exact EFrame.refl s

/-- Updating group fields that INV-S does not read. -/
theorem pres_modG (i : Nat) (f : Group → Group)
    (hf : ∀ X, (f X).next = X.next ∧ (f X).prev = X.prev ∧ (f X).first = X.first ∧
      (f X).last = X.last ∧ (f X).chk = X.chk ∧ (f X).lab = X.lab ∧ (f X).alive = X.alive) :
    Pres Same (modG i f) := by
  unfold modG; pres
  intro s
  refine ⟨?_, fun _ => rfl⟩
  constructor <;> (try intro z) <;>
    simp [gN, gP, gF, gLs, gC, gL, gA, Array.getX_modify, apply_ite (f := Group.next),
      apply_ite (f := Group.prev), apply_ite (f := Group.first), apply_ite (f := Group.last),
      apply_ite (f := Group.chk), apply_ite (f := Group.lab), apply_ite (f := Group.alive), hf]

theorem good_modG_quiet (i : Nat) :
    Good (modG i fun X => { X with st := .quiet, src := NIL }) :=
  Good.of_pres (pres_modG i (fun X => { X with st := .quiet, src := NIL })
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).same_safe

theorem good_modG_dec (i : Nat) : Good (modG i fun X => { X with size := X.size - 1 }) :=
  Good.of_pres (pres_modG i (fun X => { X with size := X.size - 1 })
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).same_safe

theorem good_modG_inc (i : Nat) : Good (modG i fun X => { X with size := X.size + 1 }) :=
  Good.of_pres (pres_modG i (fun X => { X with size := X.size + 1 })
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).same_safe

theorem good_require (b : Bool) (msg : String) : Good (require b msg) := by
  unfold require; cases b
  · exact Good.guard msg
  · exact Good.pure ()

theorem good_removeGroup (g : Nat) : Good (removeGroup g) := by
  unfold removeGroup
  refine Good.bind (good_unlinkStep g) fun _ => ?_
  good [Good.of_pres pres_getP, Good.of_pres (pres_getG _), good_modG_quiet _,
    good_startGroupSplit _]

theorem good_groupSplitStep (g : Nat) : Good (groupSplitStep g) := by
  unfold groupSplitStep
  good [Good.of_pres (pres_getG _), good_require _ _, good_removeGroup _, good_moveElem _,
    good_modG_dec _, good_modG_inc _, Good.of_pres (pres_chunkSize _ _).same_safe]

theorem good_driveGroup (g : Nat) : Good (driveGroup g) := by
  unfold driveGroup driveGroupFrom
  good [Good.of_pres (pres_getG _), Good.of_pres pres_getP, good_groupSplitStep _]

end OrderMaintenance.Proof
