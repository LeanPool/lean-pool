/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.GroupMove


/-!
# Chunk split moves preserve INV-S (Lemma 3.2: chunk-split and family moves)

`moveUnit x left` takes the unit at one end of chunk `x` (one group, or a whole family of three
groups that the guard checks to lie in `x`, consecutively) and appends it to the end of the
sibling chunk before `x` (or prepends it to the one after), with guarded group labels. The group
list does not change; only the chunks' runs, the moved groups' `chk` and labels, and the chunks'
`first`/`last` pointers do.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The unit -/

theorem unit_run (s : Core) (x : Nat) (left : Bool) :
    ((unitCand s x left).length = 1 ∧ (unit x left).run s = .ok (unitCand s x left) s) ∨
    (unitOK s x (unitCand s x left) = true ∧ (unit x left).run s = .ok (unitCand s x left) s) ∨
    (∃ msg, (unit x left).run s = .error (.guard msg) s) := by
  unfold unit
  simp only [run_get_bind]
  by_cases h1 : (unitCand s x left).length = 1
  · left; refine ⟨h1, ?_⟩; simp only [h1, BEq.rfl, ↓reduceIte, EStateM.run_pure]
  · rw [ite_eq_right (by simpa using h1), run_require_bind]
    by_cases h2 : unitOK s x (unitCand s x left) = true
    · right; left; exact ⟨h2, by rw [ite_eq_left h2]; rfl⟩
    · right; right; exact ⟨_, by rw [ite_eq_right h2]⟩

theorem unitCand_left (s : Core) (x : Nat) :
    unitCand s x true = [cF s x] ∨ ∃ a b, unitCand s x true = [cF s x, a, b] := by
  simp only [unitCand, ite_true, Bool.true_and, Bool.not_true, Bool.false_and,
    Bool.false_eq_true, ite_false, cF]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl rfl

theorem unitCand_right (s : Core) (x : Nat) :
    unitCand s x false = [cLs s x] ∨ ∃ a b, unitCand s x false = [a, b, cLs s x] := by
  simp only [unitCand, ite_false, Bool.false_and, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, cLs]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl rfl

theorem unitOK_three {s : Core} {x a b c : Nat} (h : unitOK s x [a, b, c] = true) :
    a ≠ NIL ∧ b ≠ NIL ∧ c ≠ NIL ∧ gC s a = x ∧ gC s b = x ∧
      gC s c = x ∧ gN s a = b ∧ gN s b = c := by
  simp only [unitOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq, List.tail_cons, List.zip_cons_cons, List.zip_nil_right] at h
  obtain ⟨⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩⟩, h1, h2⟩ := h
  exact ⟨ha, hb, hc, ha', hb', hc', h1, h2⟩

theorem INV.mem_chunks_of_first {s : Core} {A : Abs} (h : INV s A) {x : Nat}
    (hx : cF s x ≠ NIL) : x ∈ A.chunks := by
  by_contra hm; exact hx (h.cOut x hm).2.2

theorem INV.run_ne_nil {s : Core} {A : Abs} (h : INV s A) {x : Nat} (hx : cF s x ≠ NIL) :
    x ∈ A.chunks ∧ ∃ t, A.grps x = cF s x :: t := by
  have hxc := h.mem_chunks_of_first hx
  refine ⟨hxc, ?_⟩
  have hE := (h.cEnds x hxc).1
  cases hr : A.grps x with
  | nil => rw [hr] at hE; exact absurd hE hx
  | cons a t => rw [hr] at hE; simp only [List.headD_eq_head?_getD, List.head?_cons,
      Option.getD_some] at hE; exact ⟨t, by rw [hE]⟩

theorem INV.grps_nodup {s : Core} {A : Abs} (h : INV s A) {c : Nat} (hc : c ∈ A.chunks) :
    (A.grps c).Nodup := by
  have := h.gList.nodup; rw [INV.glist_flatten] at this
  exact List.nodup_flatten.mp this |>.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- A group in the list whose `chk` is `x` lies in chunk `x`'s run. -/
theorem INV.mem_grps_of_chk {s : Core} {A : Abs} (h : INV s A) {a x : Nat} (ha : a ∈ A.glist)
    (hc : gC s a = x) : a ∈ A.grps x := by
  have := (h.mem_glist ha).2; rw [hc] at this; exact this

/-- The successor (in the group list) of a member of chunk `x`'s run, if it is also in chunk
`x`, is its successor in the run. -/
theorem INV.gN_in_run {s : Core} {A : Abs} (h : INV s A) {x a : Nat} (hx : x ∈ A.chunks)
    (ha : a ∈ A.grps x) (hb0 : gN s a ≠ NIL) (hbc : gC s (gN s a) = x) :
    gN s a = succOf (A.grps x) a := by
  have hag := A.grps_sub_glist hx ha
  have hbg : gN s a ∈ A.glist := (h.gN_mem hag).resolve_left hb0
  have hbx := h.mem_grps_of_chk hbg hbc
  rw [h.gList.next a hag, INV.glist_flatten]
  have hnd := h.gList.nodup
  have hnil := h.gList.nonil
  rw [INV.glist_flatten] at hnd hnil
  refine succOf_flatten_of_mem hnd hnil (List.mem_map.mpr ⟨x, hx, rfl⟩) ha ?_
  rw [← INV.glist_flatten, ← h.gList.next a hag]; exact hbx

/-- **The left unit is a prefix of the chunk's run.** -/
theorem unit_prefix {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hx : cF s x ≠ NIL)
    {u : List Nat} (hu : u = [cF s x] ∨ (∃ a b, u = [cF s x, a, b] ∧ unitOK s x u = true)) :
    x ∈ A.chunks ∧ ∃ rest, A.grps x = u ++ rest := by
  obtain ⟨hxc, t, ht⟩ := hI.run_ne_nil hx
  refine ⟨hxc, ?_⟩
  rcases hu with rfl | ⟨a, b, rfl, hok⟩
  · exact ⟨t, by rw [ht]; rfl⟩
  · obtain ⟨-, ha0, hb0, -, hac, hbc, hna, hnb⟩ := unitOK_three hok
    have hg0 : cF s x ∈ A.grps x := by rw [ht]; simp only [List.mem_cons, true_or]
    have h1 := hI.gN_in_run hxc hg0 (by rw [hna]; exact ha0) (by rw [hna]; exact hac)
    rw [hna, ht, succOf_cons', ite_eq_left rfl] at h1
    cases t with
    | nil => exact absurd h1 ha0
    | cons a' t' =>
      simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at h1; subst h1
      have hax : a ∈ A.grps x := by rw [ht]; simp only [List.mem_cons, true_or, or_true]
      have h2 := hI.gN_in_run hxc hax (by rw [hnb]; exact hb0) (by rw [hnb]; exact hbc)
      have hnd := hI.grps_nodup hxc
      rw [ht] at hnd
      have hga : cF s x ≠ a := fun e => (List.nodup_cons.mp hnd).1 (by simp only [e,
          List.mem_cons,
          true_or])
      rw [hnb, ht, succOf_cons', ite_eq_right (Ne.symm hga), succOf_cons', ite_eq_left rfl] at h2
      cases t' with
      | nil => exact absurd h2 hb0
      | cons b' t'' =>
        simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at h2
        subst h2
        exact ⟨t'', by rw [ht]; rfl⟩

/-- If the successor of `b ∈ l` in `l ++ z :: m` is `z`, then `b` is the last of `l`. -/
theorem succOf_eq_next_block {l m : List Nat} {b z : Nat} (hnd : (l ++ z :: m).Nodup) (hb : b ∈ l)
    (hs : succOf (l ++ z :: m) b = z) (hz : z ≠ NIL) : ∃ l', l = l' ++ [b] := by
  have h1 := (List.nodup_append.mp hnd).1
  rw [succOf_append h1, ite_eq_left hb] at hs
  by_cases hl : l.getLast? = some b
  · rcases l.eq_nil_or_concat with h | ⟨l', a, rfl⟩
    · subst h; simp only [List.not_mem_nil] at hb
    · simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
        Option.some_or, Option.some.injEq] at hl; subst hl; exact ⟨l', by simp⟩
  · rw [ite_eq_right hl] at hs
    rcases succOf_mem_or (l := l) (x := b) with h | h
    · rw [hs] at h; exact absurd rfl ((List.nodup_append.mp hnd).2.2 z h z (by simp))
    · exact absurd (hs ▸ h) hz

/-- **The right unit is a suffix of the chunk's run.** -/
theorem unit_suffix {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hx : cF s x ≠ NIL)
    {u : List Nat} (hu : u = [cLs s x] ∨ (∃ a b, u = [a, b, cLs s x] ∧ unitOK s x u = true)) :
    x ∈ A.chunks ∧ ∃ rest, A.grps x = rest ++ u := by
  obtain ⟨hxc, t, ht⟩ := hI.run_ne_nil hx
  refine ⟨hxc, ?_⟩
  have hE := hI.cEnds x hxc
  have hnd := hI.grps_nodup hxc
  obtain ⟨r0, hr0⟩ : ∃ r0, A.grps x = r0 ++ [cLs s x] := by
    rcases (A.grps x).eq_nil_or_concat with h | ⟨r, z, h⟩
    · rw [ht] at h; simp only [reduceCtorEq] at h
    · refine ⟨r, ?_⟩; rw [h]; rw [h] at hE; have := hE.2; simp only [List.concat_eq_append,
        List.getLastD_eq_getLast?,
        List.getLast?_append,
        List.getLast?_singleton,
        Option.some_or,
        Option.getD_some] at this; rw [this]; simp only [
        List.concat_eq_append]
  rcases hu with rfl | ⟨a, b, rfl, hok⟩
  · exact ⟨r0, hr0⟩
  · obtain ⟨ha0, hb0, hl0, hac, hbc, hlc, hna, hnb⟩ := unitOK_three hok
    have hbg := hI.mem_of_gN hnb hl0
    have hbx := hI.mem_grps_of_chk hbg hbc
    have hbl : b ≠ cLs s x := by
      intro e
      have := succOf_ne_self hI.gList.nodup b hb0
      rw [← hI.gList.next b hbg, hnb] at this; exact this e.symm
    have h1 := hI.gN_in_run hxc hbx (by rw [hnb]; exact hl0) (by rw [hnb]; exact hlc)
    rw [hnb] at h1
    have hb0' : b ∈ r0 := by
      rw [hr0] at hbx; simp only [List.mem_append, List.mem_singleton] at hbx
      rcases hbx with h | h
      · exact h
      · exact absurd h hbl
    rw [hr0] at h1 hnd
    obtain ⟨r1, rfl⟩ := succOf_eq_next_block (m := []) hnd hb0' h1.symm hl0
    have hag := hI.mem_of_gN hna hb0
    have hax := hI.mem_grps_of_chk hag hac
    have h2 := hI.gN_in_run hxc hax (by rw [hna]; exact hb0) (by rw [hna]; exact hbc)
    rw [hna] at h2
    have hab : a ≠ b := by
      intro e
      have := succOf_ne_self hI.gList.nodup a ha0
      rw [← hI.gList.next a hag, hna] at this; exact this e.symm
    have hal : a ≠ cLs s x := by
      intro e
      -- the last group of the chunk has no successor in the chunk
      rw [hr0, e] at h2
      have hnd' : (r1 ++ [b] ++ [cLs s x]).Nodup := hnd
      have : succOf (r1 ++ [b] ++ [cLs s x]) (cLs s x) = NIL := by
        rw [show r1 ++ [b] ++ [cLs s x] = (r1 ++ [b]) ++ cLs s x :: [] by simp, succOf_mid
          (by simpa using hnd')]
        rfl
      rw [this] at h2; exact hb0 h2
    have ha1 : a ∈ r1 := by
      rw [hr0] at hax; simp only [List.mem_append, List.mem_singleton] at hax
      rcases hax with (h | h) | h
      · exact h
      · exact absurd h hab
      · exact absurd h hal
    rw [hr0, show r1 ++ [b] ++ [cLs s x] = r1 ++ b :: [cLs s x] by simp] at h2
    have hnd2 : (r1 ++ b :: [cLs s x]).Nodup := by simpa using hnd
    obtain ⟨r2, rfl⟩ := succOf_eq_next_block hnd2 ha1 h2.symm hb0
    exact ⟨r2, by rw [hr0]; simp⟩

/-! ### Labels for moved groups -/

theorem pushBackLabs_run (s : Core) (center D B : Nat) (k : Nat) (prev : Option Nat) :
    (∃ labs, (pushBackLabs center D B prev k).run s = .ok labs s ∧ labs.length = k ∧
        labs.IsChain (· < ·) ∧ (∀ p, prev = some p → ∀ l ∈ labs.head?, p < l)) ∨
    (∃ msg, (pushBackLabs center D B prev k).run s = .error (.guard msg) s) := by
  induction k generalizing prev with
  | zero => left; exact ⟨[], rfl, rfl, List.IsChain.nil, by simp⟩
  | succ k ih =>
    -- the rest, after a first label `l`
    have rest : ∀ l : Nat, (∀ p, prev = some p → p < l) →
        ((∃ labs, (pushBackLabs center D B (some l) k >>= fun r => pure (l :: r) :
            CM (List Nat)).run s
          = .ok labs s ∧ labs.length = k + 1 ∧ labs.IsChain (· < ·) ∧
          (∀ p, prev = some p → ∀ l' ∈ labs.head?, p < l')) ∨
        (∃ msg, (pushBackLabs center D B (some l) k >>= fun r => pure (l :: r) :
            CM (List Nat)).run s
          = .error (.guard msg) s)) := by
      intro l hlp
      rw [run_bind]
      rcases ih (some l) with ⟨r, hr, hlen, hch, hh⟩ | ⟨msg, hr⟩
      · rw [hr]; left
        refine ⟨l :: r, rfl, by simp only [List.length_cons, hlen],
          List.IsChain.cons hch (hh l rfl), ?_⟩
        intro p hp q hq
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
        subst hq
        exact hlp p hp
      · rw [hr]; right; exact ⟨msg, rfl⟩
    cases prev with
    | none =>
      have := rest center (by simp)
      unfold pushBackLabs; simpa using this
    | some p =>
      unfold pushBackLabs
      simp only
      rw [run_bind, run_after]
      by_cases h : p + D ≥ 1 <<< B ∨ p + D ≤ p
      · right; exact ⟨_, by rw [ite_eq_left h]⟩
      · rw [ite_eq_right h]
        simp only [not_or] at h
        have := rest (p + D) (by intro q hq; simp only [Option.some.injEq] at hq; omega)
        simpa using this

theorem pushFrontLabs_run (s : Core) (center D : Nat) (k : Nat) (nxt : Option Nat) :
    (∃ labs, (pushFrontLabs center D nxt k).run s = .ok labs s ∧ labs.length = k ∧
        labs.IsChain (· < ·) ∧ (∀ n, nxt = some n → ∀ l ∈ labs.getLast?, l < n)) ∨
    (∃ msg, (pushFrontLabs center D nxt k).run s = .error (.guard msg) s) := by
  induction k generalizing nxt with
  | zero => left; exact ⟨[], rfl, rfl, List.IsChain.nil, by simp⟩
  | succ k ih =>
    have rest : ∀ l : Nat, (∀ n, nxt = some n → l < n) →
        ((∃ labs, (pushFrontLabs center D (some l) k >>= fun r => pure (r ++ [l]) :
            CM (List Nat)).run s
          = .ok labs s ∧ labs.length = k + 1 ∧ labs.IsChain (· < ·) ∧
          (∀ n, nxt = some n → ∀ l' ∈ labs.getLast?, l' < n)) ∨
        (∃ msg, (pushFrontLabs center D (some l) k >>= fun r => pure (r ++ [l]) :
            CM (List Nat)).run s
          = .error (.guard msg) s)) := by
      intro l hlp
      rw [run_bind]
      rcases ih (some l) with ⟨r, hr, hlen, hch, hh⟩ | ⟨msg, hr⟩
      · rw [hr]; left
        refine ⟨r ++ [l], rfl, by simp only [List.length_append, hlen, List.length_cons,
            List.length_nil, Nat.zero_add], ?_, ?_⟩
        · rw [List.isChain_append]
          refine ⟨hch, by simp, fun a ha b hb => ?_⟩
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
          subst hb
          exact hh l rfl a ha
        · intro n hn q hq; simp only [List.getLast?_append, List.getLast?_singleton,
            Option.some_or, Option.mem_def, Option.some.injEq] at hq; subst hq; exact hlp n hn
      · rw [hr]; right; exact ⟨msg, rfl⟩
    cases nxt with
    | none =>
      have := rest center (by simp)
      unfold pushFrontLabs; simpa using this
    | some n =>
      unfold pushFrontLabs
      simp only
      rw [run_bind, run_before]
      by_cases h : n < D ∨ D = 0
      · right; exact ⟨_, by rw [ite_eq_left h]⟩
      · rw [ite_eq_right h]
        simp only [not_or] at h
        have := rest (n - D) (by intro q hq; simp only [Option.some.injEq] at hq; omega)
        simpa using this

/-! ### Running `moveUnit` -/

theorem unit_left_ok {s : Core} {x : Nat} {u : List Nat}
    (h : ((unitCand s x true).length = 1 ∧ u = unitCand s x true) ∨
      (unitOK s x (unitCand s x true) = true ∧ u = unitCand s x true)) :
    u = [cF s x] ∨ (∃ a b, u = [cF s x, a, b] ∧ unitOK s x u = true) := by
  rcases unitCand_left s x with h1 | ⟨a, b, h1⟩
  · left; rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact h1
  · rcases h with ⟨hl, rfl⟩ | ⟨hok, rfl⟩
    · rw [h1] at hl; simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
        Nat.reduceEqDiff] at hl
    · right; exact ⟨a, b, h1, h1 ▸ hok⟩

theorem unit_right_ok {s : Core} {x : Nat} {u : List Nat}
    (h : ((unitCand s x false).length = 1 ∧ u = unitCand s x false) ∨
      (unitOK s x (unitCand s x false) = true ∧ u = unitCand s x false)) :
    u = [cLs s x] ∨ (∃ a b, u = [a, b, cLs s x] ∧ unitOK s x u = true) := by
  rcases unitCand_right s x with h1 | ⟨a, b, h1⟩
  · left; rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact h1
  · rcases h with ⟨hl, rfl⟩ | ⟨hok, rfl⟩
    · rw [h1] at hl; simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
        Nat.reduceEqDiff] at hl
    · right; exact ⟨a, b, h1, h1 ▸ hok⟩

theorem moveUnit_left_run (s : Core) (x : Nat) :
    (∃ u labs, cF s x ≠ NIL ∧
        (u = [cF s x] ∨ (∃ a b, u = [cF s x, a, b] ∧ unitOK s x u = true)) ∧
        cN s (s.C.getX x).l = x ∧ labs.length = u.length ∧ labs.IsChain (· < ·) ∧
        (cF s (s.C.getX x).l ≠ NIL → ∀ l ∈ labs.head?, gL s (cLs s (s.C.getX x).l) < l) ∧
        (moveUnit x true).run s =
          .ok ((s.C.getX x).l, u) (moveGroupsLeft s x (s.C.getX x).l u labs)) ∨
    (∃ msg, (moveUnit x true).run s = .error (.guard msg) s) := by
  unfold moveUnit
  simp only [run_getP_bind, run_getC_bind, run_require_bind]
  by_cases hf : ((s.C.getX x).first != NIL) = true
  · rw [ite_eq_left hf]
    simp only [bne_iff_ne, ne_eq] at hf
    rw [run_bind]
    rcases unit_run s x true with ⟨hl, hr⟩ | ⟨hok, hr⟩ | ⟨msg, hr⟩
    rotate_right
    · rw [hr]; right; exact ⟨msg, rfl⟩
    all_goals
      rw [hr]
      simp only [ite_true, run_getC_bind, run_require_bind]
      by_cases ha : ((s.C.getX (s.C.getX x).l).next == x) = true
      · rw [ite_eq_left ha]
        simp only [run_getG_bind]
        rw [run_bind]
        rcases pushBackLabs_run s (1 <<< (s.P.groupBits - 1)) s.P.groupSpacing s.P.groupBits
          (unitCand s x true).length
          (if ((s.C.getX (s.C.getX x).l).first == NIL) = true then none
           else some (s.Gs.getX (s.C.getX (s.C.getX x).l).last).lab) with
          ⟨labs, hlr, hlen, hch, hh⟩ | ⟨msg, hlr⟩
        · rw [hlr]
          left
          refine ⟨unitCand s x true, labs, hf, unit_left_ok (by first | exact Or.inl ⟨hl, rfl⟩ |
            exact Or.inr ⟨hok, rfl⟩), beq_iff_eq.mp ha, hlen, hch, fun hne => ?_, by rfl⟩
          apply hh
          rw [ite_eq_right (fun e => hne (beq_iff_eq.mp e))]
        · rw [hlr]; right; exact ⟨msg, rfl⟩
      · rw [ite_eq_right ha]; right; exact ⟨_, rfl⟩
  · rw [ite_eq_right hf]; right; exact ⟨_, rfl⟩

theorem moveUnit_right_run (s : Core) (x : Nat) :
    (∃ u labs, cF s x ≠ NIL ∧
        (u = [cLs s x] ∨ (∃ a b, u = [a, b, cLs s x] ∧ unitOK s x u = true)) ∧
        cP s (s.C.getX x).r = x ∧ labs.length = u.length ∧ labs.IsChain (· < ·) ∧
        (cF s (s.C.getX x).r ≠ NIL → ∀ l ∈ labs.getLast?, l < gL s (cF s (s.C.getX x).r)) ∧
        (moveUnit x false).run s =
          .ok ((s.C.getX x).r, u) (moveGroupsRight s x (s.C.getX x).r u labs)) ∨
    (∃ msg, (moveUnit x false).run s = .error (.guard msg) s) := by
  unfold moveUnit
  simp only [run_getP_bind, run_getC_bind, run_require_bind]
  by_cases hf : ((s.C.getX x).first != NIL) = true
  · rw [ite_eq_left hf]
    simp only [bne_iff_ne, ne_eq] at hf
    rw [run_bind]
    rcases unit_run s x false with ⟨hl, hr⟩ | ⟨hok, hr⟩ | ⟨msg, hr⟩
    rotate_right
    · rw [hr]; right; exact ⟨msg, rfl⟩
    all_goals
      rw [hr]
      simp only [Bool.false_eq_true, ite_false, run_getC_bind, run_require_bind]
      by_cases ha : ((s.C.getX (s.C.getX x).r).prev == x) = true
      · rw [ite_eq_left ha]
        simp only [run_getG_bind]
        rw [run_bind]
        rcases pushFrontLabs_run s (1 <<< (s.P.groupBits - 1)) s.P.groupSpacing (unitCand s x
          false).length
          (if ((s.C.getX (s.C.getX x).r).first == NIL) = true then none
           else some (s.Gs.getX (s.C.getX (s.C.getX x).r).first).lab) with
          ⟨labs, hlr, hlen, hch, hh⟩ | ⟨msg, hlr⟩
        · rw [hlr]
          left
          refine ⟨unitCand s x false, labs, hf, unit_right_ok (by first | exact Or.inl ⟨hl, rfl⟩ |
            exact Or.inr ⟨hok, rfl⟩), beq_iff_eq.mp ha, hlen, hch, fun hne => ?_, by rfl⟩
          apply hh
          rw [ite_eq_right (fun e => hne (beq_iff_eq.mp e))]
        · rw [hlr]; right; exact ⟨msg, rfl⟩
      · rw [ite_eq_right ha]; right; exact ⟨_, rfl⟩
  · rw [ite_eq_right hf]; right; exact ⟨_, rfl⟩

/-! ### The records after a chunk-level move -/

theorem foldChk_getX (u labs : List Nat) (y : Nat) (a : Array Group) (hnd : u.Nodup)
    (hlen : labs.length = u.length) (hsz : ∀ g ∈ u, g < a.size) (b : Nat) :
    ((u.zip labs).foldl
      (fun a p => a.modify p.1 fun G => { G with chk := y, lab := p.2 }) a).getX b =
      if b ∈ u then { a.getX b with chk := y, lab := labs.getD (u.idxOf b) 0 } else a.getX b := by
  induction u generalizing a labs with
  | nil => simp only [List.zip_nil_left, List.foldl_nil, List.not_mem_nil, ↓reduceIte]
  | cons g u' ih =>
    cases labs with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff,
        List.length_eq_zero_iff, Nat.succ_ne_self, and_false] at hlen
    | cons l labs' =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      simp only [List.nodup_cons] at hnd
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [ih labs' _ hnd.2 hlen (fun g' hg' => by
        rw [Array.size_modify]
        exact hsz g' (List.mem_cons_of_mem _ hg'))]
      have hg := hsz g (by simp)
      by_cases hb : b = g
      · subst hb; simp only [hnd.1, ↓reduceIte, Array.getX_modify, hg, and_self, List.mem_cons,
          or_false, List.idxOf_cons_self, List.getD_eq_getElem?_getD,
          List.length_cons, Nat.zero_lt_succ, getElem?_pos,
          List.getElem_cons_zero, Option.getD_some]
      · by_cases hbu : b ∈ u'
        · simp only [hbu, ↓reduceIte, Array.getX_modify, Ne.symm hb, false_and,
            List.getD_eq_getElem?_getD, List.mem_cons, hb, or_true,
            List.idxOf_cons_ne _ (Ne.symm hb), Nat.succ_eq_add_one,
            List.getElem?_cons_succ]
        · simp only [hbu, ↓reduceIte, Array.getX_modify, Ne.symm hb, false_and, List.mem_cons,
            hb, or_self]

theorem foldChk_size (u labs : List Nat) (y : Nat) (a : Array Group) :
    ((u.zip labs).foldl (fun a p => a.modify p.1 fun G => { G with chk := y, lab := p.2 }) a).size =
      a.size := by
  induction u generalizing a labs with
  | nil => simp only [List.zip_nil_left, List.foldl_nil]
  | cons g u' ih =>
    cases labs with
    | nil => simp only [List.zip_nil_right, List.foldl_nil]
    | cons l labs' => simp only [List.zip_cons_cons, List.foldl_cons]; rw [ih]; simp only [
        Array.size_modify]

theorem map_idxOf_labs {u labs : List Nat} (hnd : u.Nodup) (hlen : labs.length = u.length) :
    u.map (fun b => labs.getD (u.idxOf b) 0) = labs := by
  induction u generalizing labs with
  | nil => cases labs with
    | nil => rfl
    | cons _ _ => simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff,
        List.length_eq_zero_iff, Nat.succ_ne_self, and_false] at hlen
  | cons g u' ih =>
    cases labs with
    | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff,
        List.length_eq_zero_iff, Nat.succ_ne_self, and_false] at hlen
    | cons l labs' =>
      simp only [List.nodup_cons] at hnd
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.map_cons, List.idxOf_cons_self, List.getD_cons_zero, List.cons.injEq,
        true_and]
      conv_rhs => rw [← ih hnd.2 hlen]
      refine List.map_congr_left fun b hb => ?_
      have : b ≠ g := fun e => hnd.1 (e ▸ hb)
      rw [List.idxOf_cons_ne _ (Ne.symm this)]
      rfl

end OrderMaintenance.Proof


namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem moveGroupsLeft_C {s : Core} {x y : Nat} {u labs : List Nat} (hxy : x ≠ y)
    (hx : x < s.C.size) (hy : y < s.C.size) (z : Nat) :
    (moveGroupsLeft s x y u labs).C.getX z =
      if z = y then { s.C.getX y with first := if cF s y = NIL then u.headD NIL else cF s y,
                                      last := u.getLastD NIL }
      else if z = x then
        (if cLs s x = u.getLastD NIL then { s.C.getX x with first := NIL, last := NIL }
         else { s.C.getX x with first := gN s (u.getLastD NIL) })
      else s.C.getX z := by
  simp only [moveGroupsLeft, cF, cLs, gN, Array.getX_modify, Array.size_modify', beq_iff_eq]
  by_cases h1 : z = y
  · subst h1; simp only [hy, and_self, ↓reduceIte, hxy, false_and, List.headD_eq_head?_getD,
      List.getLastD_eq_getLast?]
  · by_cases h2 : z = x
    · subst h2; simp only [Ne.symm h1, false_and, ↓reduceIte, hx, and_self,
        List.getLastD_eq_getLast?, h1]
    · simp only [Ne.symm h1, false_and, ↓reduceIte, Ne.symm h2, h1, h2]

theorem moveGroupsRight_C {s : Core} {x z : Nat} {u labs : List Nat} (hxz : x ≠ z)
    (hx : x < s.C.size) (hz : z < s.C.size) (w : Nat) :
    (moveGroupsRight s x z u labs).C.getX w =
      if w = z then { s.C.getX z with last := if cF s z = NIL then u.getLastD NIL else cLs s z,
                                      first := u.headD NIL }
      else if w = x then
        (if cF s x = u.headD NIL then { s.C.getX x with first := NIL, last := NIL }
         else { s.C.getX x with last := gP s (u.headD NIL) })
      else s.C.getX w := by
  simp only [moveGroupsRight, cF, cLs, gP, Array.getX_modify, Array.size_modify', beq_iff_eq]
  by_cases h1 : w = z
  · subst h1; simp only [hz, and_self, ↓reduceIte, hxz, false_and, List.headD_eq_head?_getD,
      List.getLastD_eq_getLast?]
  · by_cases h2 : w = x
    · subst h2; simp only [Ne.symm h1, false_and, ↓reduceIte, hx, and_self,
        List.headD_eq_head?_getD, h1]
    · simp only [Ne.symm h1, false_and, ↓reduceIte, Ne.symm h2, h1, h2]

/-- What a chunk-level move does to the groups: the moved ones get chunk `d` and new labels. -/
theorem moveGroups_G {s : Core} {d : Nat} {u labs : List Nat} (hnd : u.Nodup)
    (hlen : labs.length = u.length) (hsz : ∀ g ∈ u, g < s.Gs.size) (b : Nat) :
    ((u.zip labs).foldl (fun a p => a.modify p.1 fun G => { G with chk := d, lab := p.2 })
        s.Gs).getX b =
      if b ∈ u then { s.Gs.getX b with chk := d, lab := labs.getD (u.idxOf b) 0 }
      else s.Gs.getX b :=
  foldChk_getX u labs d s.Gs hnd hlen hsz b

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem INV.mem_of_cN {s : Core} {A : Abs} (h : INV s A) {a b : Nat} (hab : cN s a = b)
    (hb : b ≠ NIL) : a ∈ A.chunks := by
  by_contra hm; exact hb (hab ▸ (h.cOut a hm).1)

theorem INV.mem_of_cP {s : Core} {A : Abs} (h : INV s A) {a b : Nat} (hab : cP s a = b)
    (hb : b ≠ NIL) : a ∈ A.chunks := by
  by_contra hm; exact hb (hab ▸ (h.cOut a hm).2.1)

/-- Moving a prefix of groups updates exactly the source and destination chunk ends. -/
theorem moveGroupsLeft_chunkEnds {s : Core} {A : Abs} (hI : INV s A)
    {x y : Nat} {u rest labs : List Nat} (hx : x ∈ A.chunks)
    (hy : y ∈ A.chunks) (hxy : x ≠ y) (hrun : A.grps x = u ++ rest)
    (hu : u ≠ []) :
    ∀ c ∈ A.chunks, Ends (cF (moveGroupsLeft s x y u labs) c)
      (cLs (moveGroupsLeft s x y u labs) c)
      (if c = y then A.grps y ++ u else if c = x then rest else A.grps c) := by
  have hxs := ((hI.cAlloc x).mp hx).2
  have hys := ((hI.cAlloc y).mp hy).2
  have hrnd := hI.grps_nodup hx
  rw [hrun] at hrnd
  have hrestu : ∀ g ∈ rest, g ∉ u := fun g hg hgu =>
    (List.nodup_append.mp hrnd).2.2 g hgu g hg rfl
  have hC := moveGroupsLeft_C (s := s) (u := u) (labs := labs) hxy hxs hys
  intro c hc
  simp only [cF, cLs, hC]
  by_cases h1 : c = y
  · subst h1
    simp only [ite_true]
    have hE := hI.cEnds c hy
    simp only [Ends, cF, cLs] at hE
    refine ⟨?_, ?_⟩
    · by_cases hn : (s.C.getX c).first = NIL
      · rw [ite_eq_left hn]
        rw [hE.1] at hn
        cases h : A.grps c with
        | nil => simp only [List.headD_eq_head?_getD, List.nil_append]
        | cons a t =>
          rw [h] at hn
          simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at hn
          exact absurd (hn ▸ A.grps_sub_glist hy (h ▸ (by simp : a ∈ a :: t))) hI.gList.nonil
      · rw [ite_eq_right hn, hE.1]
        cases h : A.grps c with
        | nil => rw [h] at hE; exact absurd hE.1 hn
        | cons a t => simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
            List.cons_append]
    · obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hu
      rw [ht, getLastD_append_cons]
  · by_cases h2 : c = x
    · subst h2
      simp only [h1, ite_false, ite_true]
      have hE := hI.cEnds c hx
      rw [hrun] at hE
      simp only [Ends, cF, cLs] at hE
      by_cases hl : (s.C.getX c).last = u.getLastD NIL
      · simp only [hl, ite_true]
        -- then `rest` is empty
        cases rest with
        | nil => simp only [Ends, List.headD_eq_head?_getD, List.head?_nil, Option.getD_none,
            List.getLastD_eq_getLast?, List.getLast?_nil, and_self]
        | cons a t =>
          exfalso
          rw [hE.2, getLastD_append_cons] at hl
          have := hrestu _ (getLastD_cons_mem a t NIL)
          rw [hl] at this
          obtain ⟨a', t', ht'⟩ := List.exists_cons_of_ne_nil hu
          exact this (by rw [ht']; exact getLastD_cons_mem a' t' NIL)
      · simp only [hl, ite_false]
        cases rest with
        | nil => rw [hE.2] at hl; simp only [List.append_nil, List.getLastD_eq_getLast?,
            not_true_eq_false] at hl
        | cons a t =>
          refine ⟨?_, ?_⟩
          · -- the group after the unit's last is the head of `rest`
            obtain ⟨u', w, hu'⟩ := u.eq_nil_or_concat.resolve_left hu
            simp only [List.concat_eq_append] at hu'
            subst hu'
            have hw : w ∈ A.grps c := by rw [hrun]; simp only [List.append_assoc,
                List.cons_append,
                List.nil_append,
                List.mem_append,
                List.mem_cons, true_or,
                or_true]
            rw [List.getLastD_concat]
            have hnd2 := hI.grps_nodup hx
            rw [hrun] at hnd2
            rw [hI.gN_in_run hx hw ?_ ?_, hrun]
            · rw [show u' ++ [w] ++ a :: t = u' ++ w :: (a :: t) by simp,
                succOf_mid (by simpa using hnd2)]
            · rw [hI.gList.next w (A.grps_sub_glist hx hw), INV.glist_flatten]
              have hnd := hI.gList.nodup; rw [INV.glist_flatten] at hnd
              rw [succOf_flatten hnd (List.mem_map.mpr ⟨c, hx, rfl⟩) hw (by
                rw [hrun, show u' ++ [w] ++ a :: t = (u' ++ [w]) ++ a :: t by simp,
                  List.getLast?_append_of_ne_nil _ (by simp)]
                intro e; exact hrestu w (List.mem_of_getLast? e) (by simp)), hrun,
                show u' ++ [w] ++ a :: t = u' ++ w :: (a :: t) by simp,
                succOf_mid (by simpa using hnd2)]
              simp only [List.headD_cons]
              exact fun e => hI.gList.nonil (e ▸ A.grps_sub_glist hx (by rw [hrun]; simp))
            · rw [hI.gList.next w (A.grps_sub_glist hx hw), INV.glist_flatten]
              have hnd := hI.gList.nodup; rw [INV.glist_flatten] at hnd
              rw [succOf_flatten hnd (List.mem_map.mpr ⟨c, hx, rfl⟩) hw (by
                rw [hrun, show u' ++ [w] ++ a :: t = (u' ++ [w]) ++ a :: t by simp,
                  List.getLast?_append_of_ne_nil _ (by simp)]
                intro e; exact hrestu w (List.mem_of_getLast? e) (by simp)), hrun,
                show u' ++ [w] ++ a :: t = u' ++ w :: (a :: t) by simp,
                succOf_mid (by simpa using hnd2)]
              exact hI.chk c hx a (by rw [hrun]; simp)
          · rw [hE.2, getLastD_append_cons]
    · simp only [h1, h2, ite_false]
      exact hI.cEnds c hc

/-- **Moving a prefix `u` of chunk `x` to the end of the chunk `y` before it preserves INV-S.** -/
theorem inv_moveGroupsLeft {s : Core} {A : Abs} (hI : INV s A) {x y : Nat} {u rest labs : List Nat}
    (hx : x ∈ A.chunks) (hrun : A.grps x = u ++ rest) (hu : u ≠ []) (hadj : cN s y = x)
    (hlen : labs.length = u.length) (hch : labs.IsChain (· < ·))
    (hlab : cF s y ≠ NIL → ∀ l ∈ labs.head?, gL s (cLs s y) < l) :
    ∃ A', INV (moveGroupsLeft s x y u labs) A' ∧ A'.elist = A.elist := by
  have hx0 : x ≠ NIL := fun e => hI.cList.nonil (e ▸ hx)
  have hy := hI.mem_of_cN hadj hx0
  have hsucc : succOf A.chunks y = x := by rw [← hI.cList.next y hy]; exact hadj
  have hxy : x ≠ y := by
    intro e; subst e; exact succOf_ne_self hI.cList.nodup x hx0 hsucc
  obtain ⟨c1, c2, hcsplit⟩ := succOf_split hsucc hx0
  have hcnd := hI.cList.nodup
  rw [hcsplit] at hcnd
  have hxs := ((hI.cAlloc x).mp hx).2
  have hys := ((hI.cAlloc y).mp hy).2
  have hrnd := hI.grps_nodup hx
  rw [hrun] at hrnd
  have hund : u.Nodup := (List.nodup_append.mp hrnd).1
  have husz : ∀ g ∈ u, g < s.Gs.size := fun g hg =>
    hI.gAlloc g (A.grps_sub_glist hx (by rw [hrun]; simp only [List.mem_append, hg, true_or]))
  -- groups of `u` lie only in chunk `x`
  have huO : ∀ c ∈ A.chunks, c ≠ x → ∀ g ∈ A.grps c, g ∉ u := by
    intro c hc hcx g hg hgu
    have := hI.chk c hc g hg
    rw [hI.chk x hx g (by rw [hrun]; simp only [List.mem_append, hgu, true_or])] at this
    exact hcx this.symm
  have hrestu : ∀ g ∈ rest, g ∉ u := fun g hg hgu =>
    (List.nodup_append.mp hrnd).2.2 g hgu g hg rfl
  -- chunks other than `x`, `y`
  have hc12 : ∀ c ∈ c1 ++ c2, c ≠ x ∧ c ≠ y := by
    have hnd2 := (List.nodup_append.mp hcnd).2.1
    have hy2 : y ∉ c2 := fun h => (List.nodup_cons.mp hnd2).1 (by simp only [List.mem_cons, h,
        or_true])
    have hx2 : x ∉ c2 := (List.nodup_cons.mp (List.nodup_cons.mp hnd2).2).1
    have hdis := (List.nodup_append.mp hcnd).2.2
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨hdis c hc x (by simp), hdis c hc y (by simp)⟩
    · exact ⟨fun e => hx2 (e ▸ hc), fun e => hy2 (e ▸ hc)⟩
  let A' : Abs := { A with grps := fun c => if c = y then A.grps y ++ u
                                        else if c = x then rest else A.grps c }
  have hgl : A'.glist = A.glist := by
    unfold Abs.glist
    rw [hcsplit]
    simp only [List.flatMap_append, List.flatMap_cons, A', ite_true, hxy, Ne.symm hxy, ite_false]
    have h1 : c1.flatMap (fun c => if c = y then A.grps y ++ u else if c = x then rest
        else A.grps c) = c1.flatMap A.grps :=
      List.flatMap_congr fun c hc => by
        have := hc12 c (by simp only [List.mem_append, hc, true_or])
        simp only [this.2, ↓reduceIte, this.1]
    have h2 : c2.flatMap (fun c => if c = y then A.grps y ++ u else if c = x then rest
        else A.grps c) = c2.flatMap A.grps :=
      List.flatMap_congr fun c hc => by
        have := hc12 c (by simp only [List.mem_append, hc, or_true])
        simp only [this.2, ↓reduceIte, this.1]
    rw [h1, h2, hrun]; simp only [List.append_assoc]
  have hel : A'.elist = A.elist := by unfold Abs.elist; rw [hgl]
  refine ⟨A', ?_, hel⟩
  have hG := moveGroups_G (s := s) (d := y) hund hlen husz
  have hGsz : (moveGroupsLeft s x y u labs).Gs.size = s.Gs.size := foldChk_size u labs y s.Gs
  have hC := moveGroupsLeft_C (s := s) (u := u) (labs := labs) hxy hxs hys
  -- group accessors
  have gN' : ∀ b, gN (moveGroupsLeft s x y u labs) b = gN s b := by
    intro b; simp only [gN, moveGroupsLeft]; rw [hG]; split <;> rfl
  have gP' : ∀ b, gP (moveGroupsLeft s x y u labs) b = gP s b := by
    intro b; simp only [gP, moveGroupsLeft]; rw [hG]; split <;> rfl
  have gF' : ∀ b, gF (moveGroupsLeft s x y u labs) b = gF s b := by
    intro b; simp only [gF, moveGroupsLeft]; rw [hG]; split <;> rfl
  have gLs' : ∀ b, gLs (moveGroupsLeft s x y u labs) b = gLs s b := by
    intro b; simp only [gLs, moveGroupsLeft]; rw [hG]; split <;> rfl
  have gA' : ∀ b, gA (moveGroupsLeft s x y u labs) b = gA s b := by
    intro b; simp only [gA, moveGroupsLeft]; rw [hG]; split <;> rfl
  have gC' : ∀ b, gC (moveGroupsLeft s x y u labs) b = if b ∈ u then y else gC s b := by
    intro b; simp only [gC, moveGroupsLeft]; rw [hG]; split <;> rfl
  have gL' : ∀ b, gL (moveGroupsLeft s x y u labs) b =
      if b ∈ u then labs.getD (u.idxOf b) 0 else gL s b := by
    intro b; simp only [gL, moveGroupsLeft]; rw [hG]; split <;> rfl
  have hsame : (moveGroupsLeft s x y u labs).E = s.E ∧
      (moveGroupsLeft s x y u labs).freeG = s.freeG ∧
      (moveGroupsLeft s x y u labs).head = s.head ∧ (moveGroupsLeft s x y u labs).tail = s.tail ∧
      (moveGroupsLeft s x y u labs).firstGroup = s.firstGroup ∧
      (moveGroupsLeft s x y u labs).firstChunk = s.firstChunk ∧
      (moveGroupsLeft s x y u labs).C.size = s.C.size :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp only [moveGroupsLeft, List.getLastD_eq_getLast?,
        beq_iff_eq, List.headD_eq_head?_getD,
        Array.size_modify]⟩
  obtain ⟨sE, sF, sH, sT, sFG, sFC, sCs⟩ := hsame
  have hchunks : A'.chunks = A.chunks := rfl
  have helts : A'.elts = A.elts := rfl
  have hgrps : ∀ c, A'.grps c = if c = y then A.grps y ++ u else if c = x then rest
      else A.grps c := fun c => rfl
  refine
    { eList := ?_, eAlloc := ?_, tail := ?_, gList := ?_, gAlloc := ?_, gPos := ?_, gAlive := ?_,
      gOut := ?_, free := ?_, freeNodup := ?_, cList := ?_, cAlloc := ?_, cOut := ?_,
      gEnds := ?_, cEnds := ?_, grp := ?_, chk := ?_, eSorted := ?_, gSorted := ?_,
      cSorted := ?_ }
  · have e1 : eN (moveGroupsLeft s x y u labs) = eN s := by funext e; simp only [eN, sE]
    have e2 : eP (moveGroupsLeft s x y u labs) = eP s := by funext e; simp only [eP, sE]
    rw [hel, e1, e2, sH]; exact hI.eList
  · rw [hel, sE]; exact hI.eAlloc
  · rw [hel, sT]; exact hI.tail
  · rw [hgl, funext gN', funext gP', sFG]; exact hI.gList
  · intro b hb; rw [hGsz]; rw [hgl] at hb; exact hI.gAlloc b hb
  · rw [hGsz]; exact hI.gPos
  · intro b h1 h2; rw [gA', hgl]; rw [hGsz] at h2; exact hI.gAlive b h1 h2
  · intro b hb; rw [gN', gP']; rw [hgl] at hb; exact hI.gOut b hb
  · rw [sF, hGsz, hgl]; exact hI.free
  · rw [sF]; exact hI.freeNodup
  · have e1 : cN (moveGroupsLeft s x y u labs) = cN s := by
      funext c; simp only [cN, hC]; split_ifs <;> subst_vars <;> rfl
    have e2 : cP (moveGroupsLeft s x y u labs) = cP s := by
      funext c; simp only [cP, hC]; split_ifs <;> subst_vars <;> rfl
    rw [hchunks, e1, e2, sFC]; exact hI.cList
  · rw [hchunks, sCs]; exact hI.cAlloc
  · intro c hc
    rw [hchunks] at hc
    have h1 : c ≠ y := fun e => hc (e ▸ hy)
    have h2 : c ≠ x := fun e => hc (e ▸ hx)
    simp only [cN, cP, cF, hC, h1, h2, ite_false]
    exact hI.cOut c hc
  · intro b hb; rw [gF', gLs', helts]; rw [hgl] at hb; exact hI.gEnds b hb
  · intro c hc
    change c ∈ A.chunks at hc
    change Ends (cF (moveGroupsLeft s x y u labs) c)
      (cLs (moveGroupsLeft s x y u labs) c)
      (if c = y then A.grps y ++ u else if c = x then rest else A.grps c)
    exact moveGroupsLeft_chunkEnds hI hx hy hxy hrun hu c hc
  · intro b hb e he; rw [helts] at he; rw [hgl] at hb
    simp only [eG, sE]; exact hI.grp b hb e he
  · intro c hc b hb
    rw [hchunks] at hc
    rw [hgrps] at hb
    rw [gC']
    by_cases h1 : c = y
    · rw [ite_eq_left h1] at hb
      simp only [List.mem_append] at hb
      rcases hb with hb | hb
      · have hbu : b ∉ u := huO y hy (Ne.symm hxy) b hb
        rw [ite_eq_right hbu, h1]; exact hI.chk y hy b hb
      · rw [ite_eq_left hb, h1]
    · by_cases h2 : c = x
      · rw [ite_eq_right h1, ite_eq_left h2] at hb
        rw [ite_eq_right (hrestu b hb), h2]; exact hI.chk x hx b (by rw [hrun]; simp only [
            List.mem_append,
            hb,
            or_true])
      · rw [ite_eq_right h1, ite_eq_right h2] at hb
        rw [ite_eq_right (huO c hc h2 b hb)]; exact hI.chk c hc b hb
  · intro b hb
    rw [helts]
    have e1 : eL (moveGroupsLeft s x y u labs) = eL s := by funext e; simp only [eL, sE]
    rw [e1]; rw [hgl] at hb; exact hI.eSorted b hb
  · intro c hc
    rw [hchunks] at hc
    rw [hgrps]
    by_cases h1 : c = y
    · rw [ite_eq_left h1]
      have hmy : (A.grps y).map (gL (moveGroupsLeft s x y u labs)) = (A.grps y).map (gL s) :=
        List.map_congr_left fun b hb => by rw [gL', ite_eq_right (huO y hy (Ne.symm hxy) b hb)]
      have hmu : u.map (gL (moveGroupsLeft s x y u labs)) = labs := by
        conv_rhs => rw [← map_idxOf_labs hund hlen]
        exact List.map_congr_left fun b hb => by rw [gL', ite_eq_left hb]
      rw [List.map_append, hmy, hmu, List.isChain_append]
      refine ⟨h1 ▸ hI.gSorted y hy, hch, ?_⟩
      intro a ha b hb
      have hE := hI.cEnds y hy
      cases h : A.grps y with
      | nil => rw [h] at ha; simp only [List.map_nil, List.getLast?_nil, Option.mem_def,
          reduceCtorEq] at ha
      | cons g0 t =>
        rw [h] at ha hE
        have hne : cF s y ≠ NIL := by
          rw [hE.1]; simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
              ne_eq]
          exact fun e => hI.gList.nonil (e ▸ A.grps_sub_glist hy (h ▸ (by simp : g0 ∈ g0 :: t)))
        have := hlab hne b hb
        rw [hE.2] at this
        rw [List.getLast?_map] at ha
        simp only [Option.mem_def, Option.map_eq_some_iff] at ha
        obtain ⟨w, hw, rfl⟩ := ha
        rw [List.getLastD_eq_getLast?, hw] at this
        exact this
    · by_cases h2 : c = x
      · rw [ite_eq_right h1, ite_eq_left h2]
        have hs := hI.gSorted x hx
        rw [hrun, List.map_append, List.isChain_append] at hs
        have hmr : rest.map (gL (moveGroupsLeft s x y u labs)) = rest.map (gL s) :=
          List.map_congr_left fun b hb => by rw [gL', ite_eq_right (hrestu b hb)]
        rw [hmr]; exact hs.2.1
      · rw [ite_eq_right h1, ite_eq_right h2]
        have hm : (A.grps c).map (gL (moveGroupsLeft s x y u labs)) = (A.grps c).map (gL s) :=
          List.map_congr_left fun b hb => by rw [gL', ite_eq_right (huO c hc h2 b hb)]
        rw [hm]; exact hI.gSorted c hc
  · have : cT (moveGroupsLeft s x y u labs) = cT s := by
      funext c; simp only [cT, hC]; split_ifs <;> subst_vars <;> rfl
    rw [hchunks, this]; exact hI.cSorted

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- Moving a suffix of groups updates exactly the source and destination chunk ends. -/
theorem moveGroupsRight_chunkEnds {s : Core} {A : Abs} (hI : INV s A)
    {x z : Nat} {u rest labs : List Nat} (hx : x ∈ A.chunks)
    (hz : z ∈ A.chunks) (hxz : x ≠ z) (hrun : A.grps x = rest ++ u)
    (hu : u ≠ []) :
    ∀ c ∈ A.chunks, Ends (cF (moveGroupsRight s x z u labs) c)
      (cLs (moveGroupsRight s x z u labs) c)
      (if c = z then u ++ A.grps z else if c = x then rest else A.grps c) := by
  have hxs := ((hI.cAlloc x).mp hx).2
  have hzs := ((hI.cAlloc z).mp hz).2
  have hrnd := hI.grps_nodup hx
  rw [hrun] at hrnd
  have hrestu : ∀ g ∈ rest, g ∉ u := fun g hg hgu =>
    (List.nodup_append.mp hrnd).2.2 g hg g hgu rfl
  have hC := moveGroupsRight_C (s := s) (u := u) (labs := labs) hxz hxs hzs
  intro c hc
  simp only [cF, cLs, hC]
  by_cases h1 : c = z
  · subst h1
    simp only [ite_true]
    have hE := hI.cEnds c hz
    simp only [Ends, cF, cLs] at hE
    refine ⟨?_, ?_⟩
    · obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hu
      rw [ht]; rfl
    · by_cases hn : (s.C.getX c).first = NIL
      · rw [ite_eq_left hn]
        rw [hE.1] at hn
        cases h : A.grps c with
        | nil => simp only [List.getLastD_eq_getLast?, List.append_nil]
        | cons a t =>
          rw [h] at hn
          simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at hn
          exact absurd (hn ▸ A.grps_sub_glist hz (h ▸ (by simp : a ∈ a :: t))) hI.gList.nonil
      · rw [ite_eq_right hn, hE.2]
        cases h : A.grps c with
        | nil => rw [h] at hE; exact absurd hE.1 hn
        | cons a t => rw [getLastD_append_cons]
  · by_cases h2 : c = x
    · subst h2
      simp only [h1, ite_false, ite_true]
      have hE := hI.cEnds c hx
      rw [hrun] at hE
      simp only [Ends, cF, cLs] at hE
      by_cases hl : (s.C.getX c).first = u.headD NIL
      · simp only [hl, ite_true]
        rcases rest.eq_nil_or_concat with hr | ⟨r', a, hr⟩
        · subst hr; simp only [Ends, List.headD_eq_head?_getD, List.head?_nil, Option.getD_none,
            List.getLastD_eq_getLast?, List.getLast?_nil, and_self]
        · exfalso
          subst hr
          rw [hE.1] at hl
          obtain ⟨a', t', ht'⟩ := List.exists_cons_of_ne_nil hu
          rw [ht'] at hl
          rcases r' with _ | ⟨b0, r''⟩
          · change a = a' at hl
            exact hrestu a (by simp) (by rw [ht', hl]; simp)
          · change b0 = a' at hl
            exact hrestu b0 (by simp) (by rw [ht', hl]; simp)
      · simp only [hl, ite_false]
        rcases rest.eq_nil_or_concat with hr | ⟨r', a, hr⟩
        · subst hr; rw [hE.1] at hl; simp only [List.nil_append, List.headD_eq_head?_getD,
            not_true_eq_false] at hl
        · subst hr
          simp only [List.concat_eq_append] at *
          refine ⟨?_, ?_⟩
          · rw [hE.1]; rcases r' with _ | ⟨b0, r''⟩ <;> simp only [List.nil_append,
              List.cons_append,
              List.headD_eq_head?_getD,
              List.head?_cons,
              Option.getD_some,
              List.append_assoc]
          · -- the group before the unit's first is the last of `rest`
            obtain ⟨w, u', hu'⟩ := List.exists_cons_of_ne_nil hu
            subst hu'
            simp only [List.headD_cons]
            have hw : w ∈ A.grps c := by rw [hrun]; simp only [List.append_assoc,
                List.cons_append,
                List.nil_append,
                List.mem_append,
                List.mem_cons, true_or,
                or_true]
            have hnd2 := hI.grps_nodup hx
            rw [hrun] at hnd2
            rw [hI.gList.prev w (A.grps_sub_glist hx hw), INV.glist_flatten]
            have hnd := hI.gList.nodup; rw [INV.glist_flatten] at hnd
            rw [predOf_flatten hnd (List.mem_map.mpr ⟨c, hx, rfl⟩) hw (by
              rw [hrun]
              rcases r' with _ | ⟨b0, r''⟩
              · change (some a : Option Nat) ≠ some w
                intro e
                exact hrestu w (by simp [Option.some.inj e]) (by simp)
              · change (some b0 : Option Nat) ≠ some w
                intro e
                exact hrestu w (by simp [Option.some.inj e]) (by simp)), hrun,
              show r' ++ [a] ++ w :: u' = (r' ++ [a]) ++ w :: u' by simp,
              predOf_mid (by simpa using hnd2)]
    · simp only [h1, h2, ite_false]
      exact hI.cEnds c hc

/-- **Moving a suffix `u` of chunk `x` to the front of the chunk `z` after it preserves
INV-S.** -/
theorem inv_moveGroupsRight {s : Core} {A : Abs} (hI : INV s A) {x z : Nat} {u rest labs : List Nat}
    (hx : x ∈ A.chunks) (hrun : A.grps x = rest ++ u) (hu : u ≠ []) (hadj : cP s z = x)
    (hlen : labs.length = u.length) (hch : labs.IsChain (· < ·))
    (hlab : cF s z ≠ NIL → ∀ l ∈ labs.getLast?, l < gL s (cF s z)) :
    ∃ A', INV (moveGroupsRight s x z u labs) A' ∧ A'.elist = A.elist := by
  have hx0 : x ≠ NIL := fun e => hI.cList.nonil (e ▸ hx)
  have hz := hI.mem_of_cP hadj hx0
  have hpred : predOf A.chunks z = x := by rw [← hI.cList.prev z hz]; exact hadj
  have hxz : x ≠ z := by
    intro e; subst e; exact predOf_ne_self hI.cList.nodup x hx0 hpred
  obtain ⟨c1, c2, hcsplit⟩ := predOf_split hpred hx0
  have hcnd := hI.cList.nodup
  rw [hcsplit] at hcnd
  have hxs := ((hI.cAlloc x).mp hx).2
  have hzs := ((hI.cAlloc z).mp hz).2
  have hrnd := hI.grps_nodup hx
  rw [hrun] at hrnd
  have hund : u.Nodup := (List.nodup_append.mp hrnd).2.1
  have husz : ∀ g ∈ u, g < s.Gs.size := fun g hg =>
    hI.gAlloc g (A.grps_sub_glist hx (by rw [hrun]; simp only [List.mem_append, hg, or_true]))
  have huO : ∀ c ∈ A.chunks, c ≠ x → ∀ g ∈ A.grps c, g ∉ u := by
    intro c hc hcx g hg hgu
    have := hI.chk c hc g hg
    rw [hI.chk x hx g (by rw [hrun]; simp only [List.mem_append, hgu, or_true])] at this
    exact hcx this.symm
  have hrestu : ∀ g ∈ rest, g ∉ u := fun g hg hgu =>
    (List.nodup_append.mp hrnd).2.2 g hg g hgu rfl
  have hc12 : ∀ c ∈ c1 ++ c2, c ≠ x ∧ c ≠ z := by
    have hnd2 := (List.nodup_append.mp hcnd).2.1
    have hx2 : x ∉ c2 := fun h => (List.nodup_cons.mp hnd2).1 (by simp only [List.mem_cons, h,
        or_true])
    have hz2 : z ∉ c2 := (List.nodup_cons.mp (List.nodup_cons.mp hnd2).2).1
    have hdis := (List.nodup_append.mp hcnd).2.2
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨hdis c hc x (by simp), hdis c hc z (by simp)⟩
    · exact ⟨fun e => hx2 (e ▸ hc), fun e => hz2 (e ▸ hc)⟩
  let A' : Abs := { A with grps := fun c => if c = z then u ++ A.grps z
                                        else if c = x then rest else A.grps c }
  have hgl : A'.glist = A.glist := by
    unfold Abs.glist
    rw [hcsplit]
    simp only [List.flatMap_append, List.flatMap_cons, A', ite_true, hxz, Ne.symm hxz, ite_false]
    have h1 : c1.flatMap (fun c => if c = z then u ++ A.grps z else if c = x then rest
        else A.grps c) = c1.flatMap A.grps :=
      List.flatMap_congr fun c hc => by
        have := hc12 c (by simp only [List.mem_append, hc, true_or])
        simp only [this.2, ↓reduceIte, this.1]
    have h2 : c2.flatMap (fun c => if c = z then u ++ A.grps z else if c = x then rest
        else A.grps c) = c2.flatMap A.grps :=
      List.flatMap_congr fun c hc => by
        have := hc12 c (by simp only [List.mem_append, hc, or_true])
        simp only [this.2, ↓reduceIte, this.1]
    rw [h1, h2, hrun]; simp only [List.append_assoc]
  have hel : A'.elist = A.elist := by unfold Abs.elist; rw [hgl]
  refine ⟨A', ?_, hel⟩
  have hG := moveGroups_G (s := s) (d := z) hund hlen husz
  have hGsz : (moveGroupsRight s x z u labs).Gs.size = s.Gs.size := foldChk_size u labs z s.Gs
  have hC := moveGroupsRight_C (s := s) (u := u) (labs := labs) hxz hxs hzs
  have gN' : ∀ b, gN (moveGroupsRight s x z u labs) b = gN s b := by
    intro b; simp only [gN, moveGroupsRight]; rw [hG]; split <;> rfl
  have gP' : ∀ b, gP (moveGroupsRight s x z u labs) b = gP s b := by
    intro b; simp only [gP, moveGroupsRight]; rw [hG]; split <;> rfl
  have gF' : ∀ b, gF (moveGroupsRight s x z u labs) b = gF s b := by
    intro b; simp only [gF, moveGroupsRight]; rw [hG]; split <;> rfl
  have gLs' : ∀ b, gLs (moveGroupsRight s x z u labs) b = gLs s b := by
    intro b; simp only [gLs, moveGroupsRight]; rw [hG]; split <;> rfl
  have gA' : ∀ b, gA (moveGroupsRight s x z u labs) b = gA s b := by
    intro b; simp only [gA, moveGroupsRight]; rw [hG]; split <;> rfl
  have gC' : ∀ b, gC (moveGroupsRight s x z u labs) b = if b ∈ u then z else gC s b := by
    intro b; simp only [gC, moveGroupsRight]; rw [hG]; split <;> rfl
  have gL' : ∀ b, gL (moveGroupsRight s x z u labs) b =
      if b ∈ u then labs.getD (u.idxOf b) 0 else gL s b := by
    intro b; simp only [gL, moveGroupsRight]; rw [hG]; split <;> rfl
  have sCs : (moveGroupsRight s x z u labs).C.size = s.C.size := by simp only [moveGroupsRight,
      List.headD_eq_head?_getD,
      beq_iff_eq,
      List.getLastD_eq_getLast?,
      Array.size_modify]
  have hchunks : A'.chunks = A.chunks := rfl
  have helts : A'.elts = A.elts := rfl
  have hgrps : ∀ c, A'.grps c = if c = z then u ++ A.grps z else if c = x then rest
      else A.grps c := fun c => rfl
  refine
    { eList := ?_, eAlloc := ?_, tail := ?_, gList := ?_, gAlloc := ?_, gPos := ?_, gAlive := ?_,
      gOut := ?_, free := ?_, freeNodup := ?_, cList := ?_, cAlloc := ?_, cOut := ?_,
      gEnds := ?_, cEnds := ?_, grp := ?_, chk := ?_, eSorted := ?_, gSorted := ?_,
      cSorted := ?_ }
  · have e1 : eN (moveGroupsRight s x z u labs) = eN s := by funext e; rfl
    have e2 : eP (moveGroupsRight s x z u labs) = eP s := by funext e; rfl
    rw [hel, e1, e2]; exact hI.eList
  · rw [hel]; exact hI.eAlloc
  · rw [hel]; exact hI.tail
  · rw [hgl, funext gN', funext gP']; exact hI.gList
  · intro b hb; rw [hGsz]; rw [hgl] at hb; exact hI.gAlloc b hb
  · rw [hGsz]; exact hI.gPos
  · intro b h1 h2; rw [gA', hgl]; rw [hGsz] at h2; exact hI.gAlive b h1 h2
  · intro b hb; rw [gN', gP']; rw [hgl] at hb; exact hI.gOut b hb
  · rw [hGsz, hgl]; exact hI.free
  · exact hI.freeNodup
  · have e1 : cN (moveGroupsRight s x z u labs) = cN s := by
      funext c; simp only [cN, hC]; split_ifs <;> subst_vars <;> rfl
    have e2 : cP (moveGroupsRight s x z u labs) = cP s := by
      funext c; simp only [cP, hC]; split_ifs <;> subst_vars <;> rfl
    rw [hchunks, e1, e2]; exact hI.cList
  · rw [hchunks, sCs]; exact hI.cAlloc
  · intro c hc
    rw [hchunks] at hc
    have h1 : c ≠ z := fun e => hc (e ▸ hz)
    have h2 : c ≠ x := fun e => hc (e ▸ hx)
    simp only [cN, cP, cF, hC, h1, h2, ite_false]
    exact hI.cOut c hc
  · intro b hb; rw [gF', gLs', helts]; rw [hgl] at hb; exact hI.gEnds b hb
  · intro c hc
    change c ∈ A.chunks at hc
    change Ends (cF (moveGroupsRight s x z u labs) c)
      (cLs (moveGroupsRight s x z u labs) c)
      (if c = z then u ++ A.grps z else if c = x then rest else A.grps c)
    exact moveGroupsRight_chunkEnds hI hx hz hxz hrun hu c hc
  · intro b hb e he; rw [helts] at he; rw [hgl] at hb
    exact hI.grp b hb e he
  · intro c hc b hb
    rw [hchunks] at hc
    rw [hgrps] at hb
    rw [gC']
    by_cases h1 : c = z
    · rw [ite_eq_left h1] at hb
      simp only [List.mem_append] at hb
      rcases hb with hb | hb
      · rw [ite_eq_left hb, h1]
      · have hbu : b ∉ u := huO z hz (Ne.symm hxz) b hb
        rw [ite_eq_right hbu, h1]; exact hI.chk z hz b hb
    · by_cases h2 : c = x
      · rw [ite_eq_right h1, ite_eq_left h2] at hb
        rw [ite_eq_right (hrestu b hb), h2]; exact hI.chk x hx b (by rw [hrun]; simp only [
            List.mem_append,
            hb,
            true_or])
      · rw [ite_eq_right h1, ite_eq_right h2] at hb
        rw [ite_eq_right (huO c hc h2 b hb)]; exact hI.chk c hc b hb
  · intro b hb
    rw [helts]; rw [hgl] at hb; exact hI.eSorted b hb
  · intro c hc
    rw [hchunks] at hc
    rw [hgrps]
    by_cases h1 : c = z
    · rw [ite_eq_left h1]
      have hmz : (A.grps z).map (gL (moveGroupsRight s x z u labs)) = (A.grps z).map (gL s) :=
        List.map_congr_left fun b hb => by rw [gL', ite_eq_right (huO z hz (Ne.symm hxz) b hb)]
      have hmu : u.map (gL (moveGroupsRight s x z u labs)) = labs := by
        conv_rhs => rw [← map_idxOf_labs hund hlen]
        exact List.map_congr_left fun b hb => by rw [gL', ite_eq_left hb]
      rw [List.map_append, hmz, hmu, List.isChain_append]
      refine ⟨hch, h1 ▸ hI.gSorted z hz, ?_⟩
      intro a ha b hb
      have hE := hI.cEnds z hz
      cases h : A.grps z with
      | nil => rw [h] at hb; simp only [List.map_nil, List.head?_nil, Option.mem_def,
          reduceCtorEq] at hb
      | cons g0 t =>
        rw [h] at hb hE
        have hne : cF s z ≠ NIL := by
          rw [hE.1]; simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
              ne_eq]
          exact fun e => hI.gList.nonil (e ▸ A.grps_sub_glist hz (h ▸ (by simp : g0 ∈ g0 :: t)))
        have := hlab hne a ha
        rw [hE.1] at this
        simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        rw [← hb]
        simpa using this
    · by_cases h2 : c = x
      · rw [ite_eq_right h1, ite_eq_left h2]
        have hs := hI.gSorted x hx
        rw [hrun, List.map_append, List.isChain_append] at hs
        have hmr : rest.map (gL (moveGroupsRight s x z u labs)) = rest.map (gL s) :=
          List.map_congr_left fun b hb => by rw [gL', ite_eq_right (hrestu b hb)]
        rw [hmr]; exact hs.1
      · rw [ite_eq_right h1, ite_eq_right h2]
        have hm : (A.grps c).map (gL (moveGroupsRight s x z u labs)) = (A.grps c).map (gL s) :=
          List.map_congr_left fun b hb => by rw [gL', ite_eq_right (huO c hc h2 b hb)]
        rw [hm]; exact hI.gSorted c hc
  · have : cT (moveGroupsRight s x z u labs) = cT s := by
      funext c; simp only [cT, hC]; split_ifs <;> subst_vars <;> rfl
    rw [hchunks, this]; exact hI.cSorted

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem moveGroupsLeft_eframe (s : Core) (x y : Nat) (u labs : List Nat) :
    EFrame s (moveGroupsLeft s x y u labs) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem moveGroupsRight_eframe (s : Core) (x z : Nat) (u labs : List Nat) :
    EFrame s (moveGroupsRight s x z u labs) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem good_moveUnit (x : Nat) (left : Bool) : Good (moveUnit x left) := by
  intro s A hI
  cases left
  · rcases moveUnit_right_run s x with ⟨u, labs, hf, hu, hadj, hlen, hch, hlab, hr⟩ | ⟨msg, hr⟩
    · rw [hr]
      obtain ⟨hx, rest, hrun⟩ := unit_suffix hI hf hu
      have hune : u ≠ [] := by rcases hu with rfl | ⟨a, b, rfl, -⟩ <;> simp only [ne_eq,
          List.cons_ne_self,
          not_false_eq_true,
          reduceCtorEq]
      obtain ⟨A', h1, h2⟩ := inv_moveGroupsRight hI hx hrun hune hadj hlen hch hlab
      exact ⟨moveGroupsRight_eframe _ _ _ _ _, A', h1, h2⟩
    · rw [hr]; exact EFrame.refl s
  · rcases moveUnit_left_run s x with ⟨u, labs, hf, hu, hadj, hlen, hch, hlab, hr⟩ | ⟨msg, hr⟩
    · rw [hr]
      obtain ⟨hx, rest, hrun⟩ := unit_prefix hI hf hu
      have hune : u ≠ [] := by rcases hu with rfl | ⟨a, b, rfl, -⟩ <;> simp only [ne_eq,
          List.cons_ne_self,
          not_false_eq_true,
          reduceCtorEq]
      obtain ⟨A', h1, h2⟩ := inv_moveGroupsLeft hI hx hrun hune hadj hlen hch hlab
      exact ⟨moveGroupsLeft_eframe _ _ _ _ _, A', h1, h2⟩
    · rw [hr]; exact EFrame.refl s

theorem pres_moveSizes (x dst : Nat) (u : List Nat) : Pres Same (moveSizes x dst u) := by
  unfold moveSizes modC; pres <;> same

theorem good_chunkSplitStep (x : Nat) : Good (chunkSplitStep x) := by
  unfold chunkSplitStep
  good [Good.of_pres (pres_getC _), Good.of_pres (pres_removeChunk _).same_safe,
    good_moveUnit _ _, Good.of_pres (pres_moveSizes _ _ _).same_safe]

theorem good_driveChunk (c : Nat) : Good (driveChunk c) := by
  unfold driveChunk driveChunkFrom
  good [Good.of_pres (pres_getC _), Good.of_pres pres_getP, good_chunkSplitStep _]

end OrderMaintenance.Proof
