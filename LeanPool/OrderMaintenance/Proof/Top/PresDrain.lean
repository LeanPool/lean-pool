/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Lists
public import LeanPool.OrderMaintenance.Proof.Top.RunDrain


/-!
# M5: a sweep step keeps the invariant

`drainStep src`, in the funding loop of a job (`.fund v up src k`, `k < s`), on a ghost with a
non-empty range: all its lookups succeed, its tag passes the guard, and the invariant holds
afterwards with `k + 1` (`docs/PROOF.md` §4.5.1, `SweepStep`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### The state after a sweep step -/

section views
variable (s : Core) (v tag : Nat)

theorem dsS_P : (dsS s v tag).P = s.P := by unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_cin : (dsS s v tag).cin = s.cin := by unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_lpar : (dsS s v tag).lpar = s.lpar := by unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_resJob : (dsS s v tag).resJob = s.resJob := by
  unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_path : (dsS s v tag).path =
    s.path.setX (dsY s v) ((s.path.getX (dsY s v)).setX (s.nodes.getX v).height (dsT s v)) := by
  unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_C : (dsS s v tag).C = s.C.modify (dsY s v) fun C => { C with tag := tag } := by
  unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_size : (dsS s v tag).nodes.size = s.nodes.size := by
  unfold dsS; dsimp only; split_ifs <;> simp only [Array.size_modify]

/-- New range pointers of the ghost. -/
def dsFirstV : Nat :=
  if (s.nodes.getX v).first == (s.nodes.getX v).last then NIL
  else if goesLeft s v then (s.C.getX (dsY s v)).next else (s.nodes.getX v).first
/-- The ghost range last pointer after transferring one chunk to a target. -/
def dsLastV : Nat :=
  if (s.nodes.getX v).first == (s.nodes.getX v).last then NIL
  else if goesLeft s v then (s.nodes.getX v).last else (s.C.getX (dsY s v)).prev
/-- New range pointers of the target. -/
def dsFirstT : Nat :=
  if goesLeft s v then
    (if (s.nodes.getX (dsT s v)).first == NIL then dsY s v else (s.nodes.getX (dsT s v)).first)
  else dsY s v
/-- The target range last pointer after receiving the transferred chunk. -/
def dsLastT : Nat :=
  if goesLeft s v then dsY s v
  else (if (s.nodes.getX (dsT s v)).last == NIL then dsY s v else (s.nodes.getX (dsT s v)).last)

theorem dsS_node (hvt : v ≠ dsT s v) (hv : v < s.nodes.size) (ht : dsT s v < s.nodes.size)
    (u : Nat) : (dsS s v tag).nodes.getX u =
      if u = v then { s.nodes.getX u with first := dsFirstV s v, last := dsLastV s v }
      else if u = dsT s v then { s.nodes.getX u with first := dsFirstT s v, last := dsLastT s v }
      else s.nodes.getX u := by
  unfold dsS dsFirstV dsLastV dsFirstT dsLastT
  dsimp only
  have hvt' := Ne.symm hvt
  by_cases huv : u = v
  · subst huv
    split_ifs <;> simp_all [Array.getX_modify]
  · by_cases hut : u = dsT s v
    · subst hut
      split_ifs <;> simp_all [Array.getX_modify]
    · split_ifs <;> simp only [Array.getX_modify, Ne.symm hut, Array.size_modify, false_and,
        ↓reduceIte, Ne.symm huv]

end views

/-! ### The top structure's part after a sweep step -/

section tsviews
variable {s : Core} {v tag : Nat} (hvt : v ≠ dsT s v) (hv : v < s.nodes.size)
  (ht : dsT s v < s.nodes.size)
include hvt hv ht

theorem dsS_sameTree : SameTree (ts s) (ts (dsS s v tag)) := by
  refine ⟨dsS_P s v tag, dsS_size s v tag, dsS_cin s v tag, dsS_lpar s v tag, fun u => ?_⟩
  change (dsS s v tag).nodes.getX u = { s.nodes.getX u with
    first := ((dsS s v tag).nodes.getX u).first
    last := ((dsS s v tag).nodes.getX u).last
    weight := ((dsS s v tag).nodes.getX u).weight }
  rw [dsS_node s v tag hvt hv ht u]
  split_ifs <;> rfl

theorem dsS_first (u : Nat) : (nd (ts (dsS s v tag)) u).first =
    if u = v then dsFirstV s v else if u = dsT s v then dsFirstT s v else (nd (ts s) u).first := by
  change ((dsS s v tag).nodes.getX u).first = _
  rw [dsS_node s v tag hvt hv ht u]
  split_ifs <;> rfl

theorem dsS_last (u : Nat) : (nd (ts (dsS s v tag)) u).last =
    if u = v then dsLastV s v else if u = dsT s v then dsLastT s v else (nd (ts s) u).last := by
  change ((dsS s v tag).nodes.getX u).last = _
  rw [dsS_node s v tag hvt hv ht u]
  split_ifs <;> rfl

theorem dsS_weight (u : Nat) : (nd (ts (dsS s v tag)) u).weight = (nd (ts s) u).weight := by
  change ((dsS s v tag).nodes.getX u).weight = _
  rw [dsS_node s v tag hvt hv ht u]
  split_ifs <;> rfl

end tsviews

theorem dsS_pp (s : Core) (v tag : Nat) (h1 : 1 ≤ (s.nodes.getX v).height) (c j : Nat) :
    pp (ts (dsS s v tag)) c j =
      if c = dsY s v ∧ j = (s.nodes.getX v).height then dsT s v else pp (ts s) c j := by
  unfold pp pth
  change (if j = 0 then c else ((dsS s v tag).path.getX c).getX j) = _
  rw [dsS_path, Array.getX_setX]
  by_cases hj : j = 0
  · subst hj; simp only [ite_true]; split_ifs <;> first | rfl | omega
  · simp only [ite_eq_right hj]
    by_cases hc : c = dsY s v
    · subst hc; rw [ite_eq_left rfl, Array.getX_setX]
      by_cases hjh : j = (s.nodes.getX v).height
      · simp only [hjh, ↓reduceIte, and_self]
      · simp only [hjh, ↓reduceIte, and_false]; rfl
    · simp only [hc, ↓reduceIte, false_and]; rfl

theorem dsS_tag (s : Core) (v tag : Nat) (hy : dsY s v < s.C.size) (c : Nat) :
    (ts (dsS s v tag)).tag c = if c = dsY s v then tag else (ts s).tag c := by
  change ((dsS s v tag).C.getX c).tag = _
  rw [dsS_C, Array.getX_modify]
  by_cases hc : c = dsY s v
  · subst hc; simp only [hy, and_self, ↓reduceIte]
  · simp only [Ne.symm hc, false_and, ↓reduceIte, hc]; rfl

/-! ### What a sweep step finds -/

theorem lab_some_of_mem {s : TS} {X e : Nat} (h : e ∈ order s X) :
    ∃ l, (nd s X).lab? e = some l := by
  obtain ⟨q, hq, hq1⟩ := List.mem_map.mp h
  have : ((nd s X).table.find? (·.1 == e)).isSome := List.find?_isSome.mpr ⟨q, hq, by
    simp only [hq1, BEq.rfl]⟩
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp this
  exact ⟨q'.2, by simp only [Node.lab?, lookup, hq', Option.map_some]⟩

theorem getD_of_mem {s : TS} {X e : Nat} (h : e ∈ order s X) :
    (nd s X).lab? e = some (((nd s X).lab? e).getD 0) := by
  obtain ⟨l, hl⟩ := lab_some_of_mem h; rw [hl]; rfl

theorem lab_lt {s : TS} {cl ord} (S : ShapeT s cl ord) {X e l : Nat} (hX : isN s X)
    (h : (nd s X).lab? e = some l) : l < 2 ^ s.P.beta := by
  unfold Node.lab? lookup at h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (S.labs_ok hX).2 _ (List.mem_map.mpr ⟨q, List.mem_of_find?_eq_some hq, rfl⟩)

section facts
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord)
include S

theorem Shape.ghost_ne_anc {v c j : Nat} (hc : c ∈ cl) (hj1 : 1 ≤ j) (hj : j ≤ (ts s).P.H)
    (hg : ghostN (ts s) v) : anc (ts s) c j ≠ v := by
  intro e
  have := (S.anc_live hc j hj1 hj).1
  rw [e] at this
  exact absurd hg.2 (by rw [this.2]; simp)

/-- A chunk in a ghost's range: its live ancestor is a target, and the entry below has a side. -/
theorem Shape.rng_ghost {v c : Nat} (hg : ghostN (ts s) v) (hc : c ∈ rng (ts s) cl v) :
    c ∈ cl ∧ pp (ts s) c (ht (ts s) v) = v ∧
      (anc (ts s) c (ht (ts s) v) = (nd (ts s) v).t1 ∨ anc (ts s) c (ht (ts s) v) = (nd (ts s)
        v).t2) ∧
      belowY s v c = pp (ts s) c (ht (ts s) v - 1) ∧
      lookup (nd (ts s) v).side (pp (ts s) c (ht (ts s) v - 1)) =
        some (if anc (ts s) c (ht (ts s) v) = (nd (ts s) v).t1 then .left else .right) := by
  simp only [rng, List.mem_filter, decide_eq_true_eq] at hc
  obtain ⟨hcl, hpp⟩ := hc
  obtain ⟨hh1, hhH⟩ := S.htN v hg.1
  refine ⟨hcl, hpp, ?_, ?_, ?_⟩
  · rcases S.P c hcl _ hh1 hhH with h | ⟨-, h⟩
    · exact absurd (h ▸ hpp) (S.ghost_ne_anc hcl hh1 hhH hg)
    · rw [hpp] at h; exact h
  · unfold belowY pp
    change (if (nd (ts s) v).height == 1 then c else pth (ts s) c ((nd (ts s) v).height - 1)) = _
    by_cases h1 : (nd (ts s) v).height = 1
    · simp only [h1, BEq.rfl, ↓reduceIte, ht, tsub_self]
    · have h2 : (nd (ts s) v).height - 1 ≠ 0 := by simp only [ht] at hh1; omega
      simp only [beq_iff_eq, h1, ↓reduceIte, ht, h2]
  · have hw := S.W3 c hcl _ hh1 hhH
    rw [hpp] at hw
    rw [S.side v hg _ hw, S.par_pp hcl hh1 hhH]

theorem Shape.t1_ne_t2 {v : Nat} (hg : ghostN (ts s) v) : (nd (ts s) v).t1 ≠ (nd (ts s) v).t2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinf⟩ := S.ghost v hg
  have := (before_of_infix2 (infix3_left hinf)).trans (before_of_infix2 (infix3_right hinf))
    (S.ordNodup _)
  exact this.ne (S.ordNodup _)

omit S in
theorem rng_sub (v : Nat) : (rng (ts s) cl v).Sublist cl := List.filter_sublist

/-- **The sweep step's pick**: the chunk moved is in the range, its live ancestor is the
target, it is the first (moving left) or the last (moving right) of the range. -/
theorem Shape.pick {v : Nat} (hg : ghostN (ts s) v) (hne : rng (ts s) cl v ≠ []) :
    dsY s v ∈ rng (ts s) cl v ∧ anc (ts s) (dsY s v) (ht (ts s) v) = dsT s v ∧
      (goesLeft s v → dsY s v = (rng (ts s) cl v).headD NIL ∧ dsT s v = (nd (ts s) v).t1) ∧
      (¬ goesLeft s v → dsY s v = (rng (ts s) cl v).getLastD NIL ∧ dsT s v = (nd (ts s) v).t2) ∧
      (goesLeft s v ∨
        lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
        lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right) := by
  have hcl : (cl).Nodup := S.ord0 ▸ S.ordNodup 0
  obtain ⟨hf, hl⟩ := S.ends v hg.1
  have hfm := headD_mem hne NIL
  have hlm := getLastD_mem hne NIL
  obtain ⟨-, -, hfa, hfb, hfs⟩ := S.rng_ghost hg hfm
  obtain ⟨-, -, hla, hlb, hls⟩ := S.rng_ghost hg hlm
  have h12 := S.t1_ne_t2 hg
  have hfirst : (s.nodes.getX v).first = (rng (ts s) cl v).headD NIL := hf
  have hlast : (s.nodes.getX v).last = (rng (ts s) cl v).getLastD NIL := hl
  have hgl : goesLeft s v ↔ anc (ts s) ((rng (ts s) cl v).headD NIL) (ht (ts s) v) = (nd (ts s)
    v).t1 := by
    unfold goesLeft; rw [hfirst, hfb]
    change lookup (nd (ts s) v).side _ = _ ↔ _
    rw [hfs]; split <;> simp_all
  by_cases hgo : goesLeft s v
  · have hy : dsY s v = (rng (ts s) cl v).headD NIL := by
      simp only [dsY, hgo, ↓reduceIte, hfirst, List.headD_eq_head?_getD]
    have ht' : dsT s v = (nd (ts s) v).t1 := by simp only [dsT, hgo, ↓reduceIte]; rfl
    refine ⟨by rw [hy]; exact hfm, by rw [hy, ht']; exact hgl.mp hgo, fun _ => ⟨hy, ht'⟩,
      fun h => absurd hgo h, Or.inl hgo⟩
  · have hy : dsY s v = (rng (ts s) cl v).getLastD NIL := by
      simp only [dsY, hgo, ↓reduceIte, hlast, List.getLastD_eq_getLast?]
    have ht' : dsT s v = (nd (ts s) v).t2 := by simp only [dsT, hgo, ↓reduceIte]; rfl
    have hf2 : anc (ts s) ((rng (ts s) cl v).headD NIL) (ht (ts s) v) = (nd (ts s) v).t2 :=
      hfa.resolve_left (fun h => hgo (hgl.mpr h))
    have hl2 : anc (ts s) ((rng (ts s) cl v).getLastD NIL) (ht (ts s) v) = (nd (ts s) v).t2 := by
      rcases hla with h | h
      · exfalso
        by_cases he : (rng (ts s) cl v).getLastD NIL = (rng (ts s) cl v).headD NIL
        · rw [he, hf2] at h; exact h12 h.symm
        · have hb := (before_headD hlm he).mono (rng_sub (s := s) (cl := cl) v)
          obtain ⟨hh1, hhH⟩ := S.htN v hg.1
          rcases S.anc_mono hb _ hhH with h3 | h3
          · rw [hf2, h] at h3; exact h12 h3.symm
          · rw [hf2, h] at h3
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinf⟩ := S.ghost v hg
            have h4 := (before_of_infix2 (infix3_left hinf)).trans
              (before_of_infix2 (infix3_right hinf)) (S.ordNodup _)
            exact h3.asymm (S.ordNodup _) h4
      · exact h
    refine ⟨by rw [hy]; exact hlm, by rw [hy, ht']; exact hl2, fun h => absurd h hgo,
      fun _ => ⟨hy, ht'⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [hfirst,
      hfb]; change lookup (nd (ts s) v).side _ = _; rw [hfs,
      ite_eq_right (by rw [hf2]; exact Ne.symm h12)]
    · rw [hlast,
      hlb]; change lookup (nd (ts s) v).side _ = _; rw [hls,
      ite_eq_right (by rw [hl2]; exact Ne.symm h12)]

/-! ### The tag part of the invariant after the step -/

variable {v : Nat} (hg : ghostN (ts s) v) (hne : rng (ts s) cl v ≠ [])
include hg hne

theorem Shape.ds_basics :
    v ≠ dsT s v ∧ v < s.nodes.size ∧ dsT s v < s.nodes.size ∧ liveN (ts s) (dsT s v) ∧
      ht (ts s) (dsT s v) = ht (ts s) v ∧ 1 ≤ ht (ts s) v ∧ ht (ts s) v < (ts s).P.H := by
  obtain ⟨hy, hanc, hL, hR, -⟩ := S.pick hg hne
  obtain ⟨hl1, hl2, hh1, hh2, -, -, -, -, -, hlt, -⟩ := S.ghost v hg
  have htt : dsT s v = (nd (ts s) v).t1 ∨ dsT s v = (nd (ts s) v).t2 := by
    by_cases h : goesLeft s v
    · exact Or.inl (hL h).2
    · exact Or.inr (hR h).2
  have hlive : liveN (ts s) (dsT s v) := by rcases htt with h | h <;> rw [h] <;> assumption
  have hht : ht (ts s) (dsT s v) = ht (ts s) v := by rcases htt with h | h <;> rw [h] <;> assumption
  refine ⟨fun e => ?_, hg.1.2.1, hlive.1.2.1, hlive, hht, (S.htN v hg.1).1, hlt⟩
  rw [← e] at hlive; exact absurd hg.2 (by rw [hlive.2]; simp)

theorem Shape.ds_pp (tag c j : Nat) :
    pp (ts (dsS s v tag)) c j = if c = dsY s v ∧ j = ht (ts s) v then dsT s v else pp (ts s) c j :=
  dsS_pp s v tag (S.ds_basics hg hne).2.2.2.2.2.1 c j

theorem Shape.drain_shapeT (tag : Nat) : ShapeT (ts (dsS s v tag)) cl ord := by
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  have T := dsS_sameTree (tag := tag) hvt hv htz
  have hP : (ts (dsS s v tag)).P = (ts s).P := dsS_P s v tag
  obtain ⟨hy, hanc, hL, hR, -⟩ := S.pick hg hne
  have hcl : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  obtain ⟨hycl, hypp, -, -, -⟩ := S.rng_ghost hg hy
  have hpp := S.ds_pp hg hne tag
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinf⟩ := S.ghost v hg
  have h1v := before_of_infix2 (infix3_left hinf)
  have hv2 := before_of_infix2 (infix3_right hinf)
  have hon := S.ordNodup (ht (ts s) v)
  have htmem : dsT s v ∈ ord (ht (ts s) v) := by
    rw [← hht]; exact (S.ordMem _ (by omega) (by omega) _).mpr ⟨hlive.1, rfl⟩
  have htt : dsT s v = (nd (ts s) v).t1 ∨ dsT s v = (nd (ts s) v).t2 := by
    by_cases h : goesLeft s v
    · exact Or.inl (hL h).2
    · exact Or.inr (hR h).2
  have inR : ∀ d, d ∈ cl → pp (ts s) d (ht (ts s) v) = v → d ∈ rng (ts s) cl v := fun d hd h => by
    simp only [rng, List.mem_filter, decide_eq_true_eq]; exact ⟨hd, h⟩
  refine ⟨by rw [hP]; exact S.H3, S.ord0, S.ordNodup, fun h h1 h2 u => ?_,
    fun h hh => by rw [hP] at hh; exact S.ordHigh h hh, fun u hu => ?_,
    ?_, fun c hc j hj => ?_, fun c hc j hj1 hj => ?_, fun j hj c d hcd => ?_, fun X hX => ?_,
    fun X hX => ?_⟩
  · rw [hP] at h2; rw [T.isN, T.ht]; exact S.ordMem h h1 h2 u
  · rw [T.isN] at hu; rw [T.ht, hP]; exact S.htN u hu
  · rw [hP, T.liveN, T.livePar]; exact S.root
  · rw [hP] at hj; rw [hpp]
    split_ifs with h
    · rw [h.2]; exact htmem
    · exact S.pathEnt c hc j hj
  · rw [hP] at hj; rw [T.order, hpp, hpp]
    by_cases hcy : c = dsY s v
    · subst hcy
      by_cases hjh : j = ht (ts s) v
      · subst hjh
        rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_right (by omega)]
        have := S.Sr _ hycl _ hj1 hj (by rw [hypp]; exact hg)
        rwa [hanc] at this
      · rw [ite_eq_right (fun h => hjh h.2)]
        by_cases hjh1 : j - 1 = ht (ts s) v
        · rw [ite_eq_left ⟨rfl, hjh1⟩]
          have hw := S.W3 _ hycl j hj1 hj
          rw [hjh1, hypp] at hw
          have hX : pp (ts s) (dsY s v) j ∈ tabs (ts s) (ht (ts s) v) v :=
            (S.tabsIff _ v _ ((S.ordMem _ hh1 (by omega) v).mpr ⟨hg.1, rfl⟩)).mpr
              ⟨(S.isN_pp hycl hj1 hj).1, by rw [(S.isN_pp hycl hj1 hj).2]; omega, hw⟩
          have hw1 := (S.W1 v hg _ hX).subset
          rcases htt with e | e <;> rw [e] <;> exact hw1 (by simp)
        · rw [ite_eq_right (fun h => hjh1 h.2)]; exact S.W3 _ hycl j hj1 hj
    · rw [ite_eq_right (fun h => hcy h.1),
      ite_eq_right (fun h => hcy h.1)]; exact S.W3 c hc j hj1 hj
  · rw [hP] at hj
    rw [hpp, hpp]
    have hc := hcd.mem_left
    have hd := hcd.mem_right
    have hne' : c ≠ d := hcd.ne hcl
    by_cases hjh : j = ht (ts s) v
    · subst hjh
      by_cases hcy : c = dsY s v
      · subst hcy
        rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_right (fun h => hne' h.1.symm)]
        rcases S.O2 _ hj _ _ hcd with h | h <;> rw [hypp] at h
        · by_cases hgo : goesLeft s v
          · right; rw [(hL hgo).2, ← h]; exact h1v
          · exfalso
            have hdr := inR d hd h.symm
            have := before_getLastD hdr (by rw [← (hR hgo).1]; exact Ne.symm hne')
            rw [← (hR hgo).1] at this
            exact (this.mono (rng_sub (s := s) (cl := cl) v)).asymm hcl hcd
        · by_cases hgo : goesLeft s v
          · right; rw [(hL hgo).2]; exact h1v.trans h hon
          · rw [(hR hgo).2]
            rcases before_succ hon (infix3_right hinf) h with e | e
            · left; exact e.symm
            · right; exact e
      · by_cases hdy : d = dsY s v
        · subst hdy
          rw [ite_eq_right (fun h => hcy h.1), ite_eq_left ⟨rfl, rfl⟩]
          rcases S.O2 _ hj _ _ hcd with h | h <;> rw [hypp] at h
          · by_cases hgo : goesLeft s v
            · exfalso
              have hcr := inR c hc h
              have := before_headD hcr (by rw [← (hL hgo).1]; exact hne')
              rw [← (hL hgo).1] at this
              exact (this.mono (rng_sub (s := s) (cl := cl) v)).asymm hcl hcd
            · right; rw [h, (hR hgo).2]; exact hv2
          · by_cases hgo : goesLeft s v
            · rw [(hL hgo).2]
              rcases before_pred hon (infix3_left hinf) h with e | e
              · left; exact e
              · right; exact e
            · right; rw [(hR hgo).2]; exact h.trans hv2 hon
        · rw [ite_eq_right (fun h => hcy h.1),
          ite_eq_right (fun h => hdy h.1)]; exact S.O2 _ hj c d hcd
    · rw [ite_eq_right (fun h => hjh h.2), ite_eq_right (fun h => hjh h.2)]; exact S.O2 j hj c d hcd
  · rw [T.isN] at hX; rw [T.order, T.ht]; exact S.O1 X hX
  · rw [T.isN] at hX; rw [T.labs, hP]; exact S.labsOk X hX

theorem Shape.ds_digit (tag c j : Nat) (hj : j ≠ ht (ts s) v) (hj1 : j ≠ ht (ts s) v + 1 ∨ c ≠
  dsY s v) :
    digit (ts (dsS s v tag)) c j = digit (ts s) c j := by
  obtain ⟨hvt, hv, htz, -⟩ := S.ds_basics hg hne
  have T := dsS_sameTree (tag := tag) hvt hv htz
  have hpp := S.ds_pp hg hne tag
  unfold digit
  rw [T.lab?, hpp, hpp, ite_eq_right (fun h => hj h.2)]
  by_cases hc : c = dsY s v
  · rw [ite_eq_right (fun h => by rcases hj1 with h' | h' <;> [exact h' (by omega); exact h' h.1])]
  · rw [ite_eq_right (fun h => hc h.1)]

theorem Shape.ds_tagF_other (tag c : Nat) (hc : c ≠ dsY s v) :
    tagF (ts (dsS s v tag)) c = tagF (ts s) c := by
  unfold tagF
  rw [show (ts (dsS s v tag)).P = (ts s).P from dsS_P s v tag]
  apply tagUp_congr (by rw [show (ts (dsS s v tag)).P = (ts s).P from dsS_P s v tag])
  intro i _ _
  obtain ⟨hvt, hv, htz, -⟩ := S.ds_basics hg hne
  have T := dsS_sameTree (tag := tag) hvt hv htz
  have hpp := S.ds_pp hg hne tag
  unfold digit
  rw [T.lab?, hpp, hpp, ite_eq_right (fun h => hc h.1), ite_eq_right (fun h => hc h.1)]

/-- The table entries a sweep step reads. -/
theorem Shape.ds_mem :
    let y := dsY s v
    let h := ht (ts s) v
    dsT s v ∈ order (ts s) (pp (ts s) y (h + 1)) ∧ pp (ts s) y (h - 1) ∈ order (ts s) (dsT s v) ∧
      v ∈ order (ts s) (pp (ts s) y (h + 1)) ∧ pp (ts s) y (h - 1) ∈ order (ts s) v := by
  intro y h
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  obtain ⟨hy, hanc, hL, hR, -⟩ := S.pick hg hne
  obtain ⟨hycl, hypp, -, -, -⟩ := S.rng_ghost hg hy
  have hw := S.W3 _ hycl (h + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hw
  rw [hypp] at hw
  have hw0 := S.W3 _ hycl h hh1 (by omega)
  rw [hypp] at hw0
  have hX : pp (ts s) y (h + 1) ∈ tabs (ts s) h v :=
    (S.tabsIff _ v _ ((S.ordMem _ hh1 (by omega) v).mpr ⟨hg.1, rfl⟩)).mpr
      ⟨(S.isN_pp hycl (by omega) (show h + 1 ≤ _ by omega)).1,
        by rw [(S.isN_pp hycl (by omega) (show h + 1 ≤ _ by omega)).2], hw⟩
  have hw1 := (S.W1 v hg _ hX).subset
  have htt : dsT s v = (nd (ts s) v).t1 ∨ dsT s v = (nd (ts s) v).t2 := by
    by_cases h' : goesLeft s v
    · exact Or.inl (hL h').2
    · exact Or.inr (hR h').2
  refine ⟨by rcases htt with e | e <;> rw [e] <;> exact hw1 (by simp), ?_, hw, hw0⟩
  have := S.Sr _ hycl h hh1 (by omega) (by rw [hypp]; exact hg)
  rwa [hanc] at this

omit S hg hne in
/-- Shared sweep-step guards, shape bounds and the interpretation of the new tag. -/
theorem Shape.drain_move_facts {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts
  s) cl ord) {v : Nat}
    (hg : ghostN (ts s) v) (hne : rng (ts s) cl v ≠ []) (hL : LList (cN s) (cP s) s.firstChunk cl) :
    let y := dsY s v
    let h := ht (ts s) v
    let pv := digit (ts s) y (h + 1)
    let vb := digit (ts s) y h
    let pt := ((nd (ts s) (pp (ts s) y (h + 1))).lab? (dsT s v)).getD 0
    let tb := ((nd (ts s) (dsT s v)).lab? (pp (ts s) y (h - 1))).getD 0
    ((s.nodes.getX v).alive = true ∧ (s.nodes.getX v).first ≠ NIL ∧
    (goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right) ∧
    (s.nodes.getX v).height + 1 < (s.path.getX (dsY s v)).size ∧
    (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? (dsT s v) =
      some pt ∧
    (s.nodes.getX (dsT s v)).lab? (belowY s v (dsY s v)) = some tb ∧
    (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? v = some pv ∧
    (s.nodes.getX v).lab? (belowY s v (dsY s v)) = some vb ∧
    (pv <<< ((s.nodes.getX v).height * s.P.beta)) |||
        (vb <<< (((s.nodes.getX v).height - 1) * s.P.beta)) ≤ (s.C.getX (dsY s v)).tag ∧
    TagOK s (dsY s v) (dsTag s v pt tb pv vb) ∧
    1 ≤ (s.nodes.getX v).height ∧ (s.path.getX (dsY s v)).size = s.P.H + 1 ∧
    tb < 2 ^ s.P.beta ∧ vb < 2 ^ s.P.beta ∧ dsT s v ≠ v ∧ v < s.nodes.size ∧ dsT s v <
      s.nodes.size ∧
    dsY s v ∈ cl ∧ (s.nodes.getX v).height < s.P.H ∧
    (s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1) < s.nodes.size) ∧
      dsTag s v pt tb pv vb =
      tagF (ts (dsS s v (dsTag s v pt tb pv vb))) y := by
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
    change (s.C.getX y).tag - ((pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta))) +
      ((pt <<< (h * s.P.beta)) ||| (tb <<< ((h - 1) * s.P.beta))) = _
    rw [hor1, hor2]
  have hnew : tag = tagF (ts (dsS s v tag)) y := by rw [e1, e2, htagy]
  refine ⟨?_, hnew⟩
  · have hpv : pv = ((nd (ts s) (pp (ts s) y (h + 1))).lab? v).getD 0 := by
      simp only [pv, digit, Nat.add_sub_cancel]; rw [show pp (ts s) y h = v from hypp]
    have hvb' : vb = ((nd (ts s) v).lab? (pp (ts s) y (h - 1))).getD 0 := by
      simp only [vb, digit]; rw [show pp (ts s) y h = v from hypp]
    refine ⟨hg.1.2.2, ?_, hside, ?_, getD_of_mem m1, ?_, (by
      rw [hpv]
      exact getD_of_mem m3), ?_, ?_, ?_,
      hh1, S.pathSize y hycl, htbl, hvbl, Ne.symm hvt, hv, htz, hycl, hhH, ?_⟩
    · obtain ⟨hf, -⟩ := S.ends v hg.1
      change (nd (ts s) v).first ≠ NIL
      rw [hf]
      exact fun e => hL.nonil (e ▸ (rng_sub (s := s) (cl := cl) v).subset (headD_mem hne NIL))
    · change h + 1 < ((ts s).path.getX y).size
      rw [S.pathSize y hycl]; omega
    · change (nd (ts s) (dsT s v)).lab? (belowY s v y) = some tb
      rw [hbel]; exact getD_of_mem m2
    · change (nd (ts s) v).lab? (belowY s v y) = some vb
      rw [hbel, hvb']; exact getD_of_mem m4
    · change (pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta)) ≤ (s.C.getX y).tag
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
        change (s.C.getX q).tag < tag
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
        change tag < (s.C.getX q).tag
        rw [show (s.C.getX q).tag = (ts s).tag q from rfl, S.tags _ hpcl,
          ← S.ds_tagF_other hg hne tag _ (Ne.symm hpy)]
        exact lt_of_eq_of_lt hnew (ST.tagF_lt hb)
    · have h2 := hXN.2.1
      unfold pp at h2; rw [ite_eq_right (by omega)] at h2; exact h2


/-- **The sweep step runs**, and the tag it writes is the tag of the new path. -/
theorem Shape.drain_run (hL : LList (cN s) (cP s) s.firstChunk cl) :
    let y := dsY s v
    let h := ht (ts s) v
    let pv := digit (ts s) y (h + 1)
    let vb := digit (ts s) y h
    let pt := ((nd (ts s) (pp (ts s) y (h + 1))).lab? (dsT s v)).getD 0
    let tb := ((nd (ts s) (dsT s v)).lab? (pp (ts s) y (h - 1))).getD 0
    (drainStep v).run s = .ok true (dsS s v (dsTag s v pt tb pv vb)) ∧
      dsTag s v pt tb pv vb = tagF (ts (dsS s v (dsTag s v pt tb pv vb))) y := by
  intro y h pv vb pt tb
  have facts := S.drain_move_facts hg hne hL
  obtain ⟨ha, hf, hs, hp, hpt, htb, hpv, hvb, hb, ht, -⟩ := facts.1
  exact ⟨drainStep_move ha hf hs hp hpt htb hpv hvb hb ht, facts.2⟩

/-! ### The rest of the order invariant after the step -/

omit hg hne in
theorem Shape.rng_infix (u : Nat) (hu : isN (ts s) u) : rng (ts s) cl u <:+: cl :=
  filter_infix_of_convex (S.ord0 ▸ S.ordNodup 0) fun a b d ha hd hab hbd => by
    have := S.rng_between hu (c := a) (d := d) (e := b)
      (List.mem_filter.mpr ⟨hab.mem_left, ha⟩) (List.mem_filter.mpr ⟨hbd.mem_right, hd⟩) hab hbd
    exact (List.mem_filter.mp this).2

/-- The ranges after the step: the chunk leaves the ghost's range and joins the target's, at the
end next to it. -/
theorem Shape.ds_rng (tag u : Nat) : rng (ts (dsS s v tag)) cl u =
    if u = v then (rng (ts s) cl v).erase (dsY s v)
    else if u = dsT s v then
      (if goesLeft s v then rng (ts s) cl (dsT s v) ++ [dsY s v] else dsY s v :: rng (ts s) cl
        (dsT s v))
    else rng (ts s) cl u := by
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  have T := dsS_sameTree (tag := tag) hvt hv htz
  obtain ⟨hy, hanc, hLe, hRi, -⟩ := S.pick hg hne
  obtain ⟨hycl, hypp, -, -, -⟩ := S.rng_ghost hg hy
  have hpp := S.ds_pp hg hne tag
  have hcl : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinf⟩ := S.ghost v hg
  have hon := S.ordNodup (ht (ts s) v)
  have h1v := before_of_infix2 (infix3_left hinf)
  have hv2 := before_of_infix2 (infix3_right hinf)
  unfold rng
  rw [T.ht]
  have hpred : ∀ c, decide (pp (ts (dsS s v tag)) c (ht (ts s) u) = u) =
      if c = dsY s v ∧ ht (ts s) u = ht (ts s) v then decide (dsT s v = u)
      else decide (pp (ts s) c (ht (ts s) u) = u) := by
    intro c; rw [hpp]; split_ifs <;> rfl
  by_cases huv : u = v
  · subst huv
    rw [ite_eq_left rfl]
    apply filter_erase_of hcl
    · intro c _ hc; rw [hpred, ite_eq_right (fun h => hc h.1)]
    · rw [hpred, ite_eq_left ⟨rfl, rfl⟩]; simpa using Ne.symm hvt
  · rw [ite_eq_right huv]
    by_cases hut : u = dsT s v
    · subst hut
      rw [ite_eq_left rfl, hht]
      have hpy : decide (pp (ts s) (dsY s v) (ht (ts s) v) = dsT s v) = false := by
        rw [hypp]; simpa using hvt
      by_cases hgo : goesLeft s v
      · rw [ite_eq_left hgo]
        apply filter_snoc_of (p := fun c => decide (pp (ts s) c (ht (ts s) v) = dsT s v))
          (c := dsY s v) hcl (fun c _ hc => by rw [hpp, ite_eq_right (fun h => hc h.1)])
          (by rw [hpp, ite_eq_left ⟨rfl, rfl⟩]; simp) hpy hycl
        intro c hc hpc hcy
        simp only [decide_eq_true_eq] at hpc
        rcases before_total hc hycl hcy with h | h
        · exact h
        · exfalso
          rcases S.O2 (ht (ts s) v) (by omega) _ _ h with h2 | h2 <;> rw [hypp, hpc, (hLe
            hgo).2] at h2
          · exact hvt (h2.trans (hLe hgo).2.symm)
          · exact h2.asymm hon h1v
      · rw [ite_eq_right hgo]
        apply filter_cons_of (p := fun c => decide (pp (ts s) c (ht (ts s) v) = dsT s v))
          (c := dsY s v) hcl (fun c _ hc => by rw [hpp, ite_eq_right (fun h => hc h.1)])
          (by rw [hpp, ite_eq_left ⟨rfl, rfl⟩]; simp) hpy hycl
        intro c hc hpc hcy
        simp only [decide_eq_true_eq] at hpc
        rcases before_total hycl hc (Ne.symm hcy) with h | h
        · exact h
        · exfalso
          rcases S.O2 (ht (ts s) v) (by omega) _ _ h with h2 | h2 <;> rw [hypp, hpc, (hRi
            hgo).2] at h2
          · exact hvt (h2.symm.trans (hRi hgo).2.symm)
          · exact h2.asymm hon hv2
    · rw [ite_eq_right hut]
      apply List.filter_congr
      intro c _
      rw [hpred]
      split_ifs with h
      · obtain ⟨rfl, hh⟩ := h
        rw [hh, hypp]
        simp only [Ne.symm hut, decide_false, Ne.symm huv]
      · rfl

/-- **Range pointers after the step.** -/
theorem Shape.ds_ends (hL : LList (cN s) (cP s) s.firstChunk cl) (tag u : Nat)
    (hu : isN (ts s) u) :
    (nd (ts (dsS s v tag)) u).first = (rng (ts (dsS s v tag)) cl u).headD NIL ∧
      (nd (ts (dsS s v tag)) u).last = (rng (ts (dsS s v tag)) cl u).getLastD NIL := by
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  obtain ⟨hy, hanc, hLe, hRi, -⟩ := S.pick hg hne
  obtain ⟨hycl, hypp, -, -, -⟩ := S.rng_ghost hg hy
  have hcl : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  rw [dsS_first hvt hv htz, dsS_last hvt hv htz, S.ds_rng hg hne tag]
  have hrnd : (rng (ts s) cl v).Nodup := hcl.sublist (rng_sub (s := s) (cl := cl) v)
  obtain ⟨hfv, hlv⟩ := S.ends v hg.1
  obtain ⟨hft, hlt⟩ := S.ends (dsT s v) hlive.1
  have hinf := S.rng_infix v hg.1
  by_cases huv : u = v
  · subst huv
    simp only [ite_true]
    unfold dsFirstV dsLastV
    have hfv' : (s.nodes.getX u).first = (rng (ts s) cl u).headD NIL := hfv
    have hlv' : (s.nodes.getX u).last = (rng (ts s) cl u).getLastD NIL := hlv
    rw [hfv', hlv']
    by_cases hgo : goesLeft s u
    · simp only [ite_eq_left hgo]
      obtain ⟨hyh, -⟩ := hLe hgo
      obtain ⟨rest, hr⟩ : ∃ rest, rng (ts s) cl u = dsY s u :: rest := by
        cases hrr : rng (ts s) cl u with
        | nil => exact absurd hrr hne
        | cons a t => rw [hrr] at hyh; exact ⟨t, by
          simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at hyh; rw [hyh]⟩
      rw [hr] at hrnd hinf ⊢
      cases rest with
      | nil => simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
          List.getLastD_eq_getLast?, List.getLast?_singleton, BEq.rfl, ↓reduceIte,
          List.erase_cons_head, List.head?_nil, Option.getD_none,
          List.getLast?_nil, and_self]
      | cons z r =>
        have hyn : dsY s u ∉ z :: r := (List.nodup_cons.mp hrnd).1
        have hlm : (dsY s u :: z :: r).getLastD NIL ∈ z :: r := by
          rw [List.getLastD_cons]; exact getLastD_mem (by simp) _
        have hlast : ((dsY s u :: z :: r).headD NIL == (dsY s u :: z :: r).getLastD NIL) = false
          := by
          simp only [List.headD_cons, beq_eq_false_iff_ne]
          exact fun e => hyn (e ▸ hlm)
        rw [hlast]
        simp only [Bool.false_eq_true, ite_false, List.erase_cons_head, List.headD_cons]
        refine ⟨?_, by simp only [List.getLastD_cons]⟩
        change cN s (dsY s u) = z
        rw [hL.next _ hycl]; exact succOf_infix hcl hinf
    · simp only [ite_eq_right hgo]
      obtain ⟨hyl, -⟩ := hRi hgo
      obtain ⟨r0, hr⟩ : ∃ r0, rng (ts s) cl u = r0 ++ [dsY s u] := by
        obtain ⟨r0, a, e⟩ := List.eq_nil_or_concat (rng (ts s) cl u) |>.resolve_left hne
        rw [e, List.concat_eq_append] at hyl
        simp only [List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton,
            Option.some_or, Option.getD_some] at hyl
        exact ⟨r0, by rw [e, List.concat_eq_append, hyl]⟩
      rw [hr] at hrnd hinf ⊢
      have hyn : dsY s u ∉ r0 := fun h => by
        have h2 := List.nodup_append.mp hrnd
        exact h2.2.2 _ h _ (List.mem_singleton_self _) rfl
      rw [List.erase_append_right _ hyn, List.erase_cons_head, List.append_nil]
      rcases List.eq_nil_or_concat r0 with h0 | ⟨r1, z, h0⟩
      · subst h0; simp only [List.nil_append, List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some, List.getLastD_eq_getLast?, List.getLast?_singleton,
          BEq.rfl, ↓reduceIte, List.head?_nil, Option.getD_none,
          List.getLast?_nil, and_self]
      · rw [List.concat_eq_append] at h0
        subst h0
        have hF : (r1 ++ [z] ++ [dsY s u]).headD NIL = (r1 ++ [z]).headD NIL := by
          cases r1 <;> simp only [List.nil_append, List.cons_append, List.headD_eq_head?_getD,
              List.head?_cons, Option.getD_some, List.append_assoc]
        have hL' : (r1 ++ [z] ++ [dsY s u]).getLastD NIL = dsY s u := by
          simp only [List.append_assoc, List.cons_append, List.nil_append,
            List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_cons_cons,
            List.getLast?_singleton, Option.some_or, Option.getD_some]
        have hFy : (r1 ++ [z]).headD NIL ≠ dsY s u := fun e =>
          hyn (e ▸ headD_mem (by simp) NIL)
        rw [hF, hL', show ((r1 ++ [z]).headD NIL == dsY s u) = false by simpa using hFy]
        simp only [Bool.false_eq_true, ite_false]
        refine ⟨by trivial, ?_⟩
        change cP s (dsY s u) = _
        rw [hL.prev _ hycl, predOf_infix hcl (r := r1) (z := z) (by simpa using hinf)]
        simp only [List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton,
            Option.some_or, Option.getD_some]
  · simp only [huv, ite_false]
    by_cases hut : u = dsT s v
    · subst hut
      simp only [ite_true]
      unfold dsFirstT dsLastT
      have hft' : (s.nodes.getX (dsT s v)).first = (rng (ts s) cl (dsT s v)).headD NIL := hft
      have hlt' : (s.nodes.getX (dsT s v)).last = (rng (ts s) cl (dsT s v)).getLastD NIL := hlt
      have hnilt : NIL ∉ rng (ts s) cl (dsT s v) := fun h => hL.nonil ((rng_sub (s := s) (cl :=
        cl) _).subset h)
      by_cases hgo : goesLeft s v
      · simp only [ite_eq_left hgo]
        refine ⟨?_, by simp⟩
        rw [hft']
        by_cases he : rng (ts s) cl (dsT s v) = []
        · rw [he]; simp only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none,
            BEq.rfl, ↓reduceIte, List.nil_append, List.head?_cons,
            Option.getD_some]
        · rw [ite_eq_right (by simpa using headD_ne_nil' hnilt he)]
          cases h : rng (ts s) cl (dsT s v) with
          | nil => exact absurd h he
          | cons a t => simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
              List.cons_append]
      · simp only [ite_eq_right hgo]
        refine ⟨by simp, ?_⟩
        rw [hlt']
        by_cases he : rng (ts s) cl (dsT s v) = []
        · rw [he]; simp only [List.getLastD_eq_getLast?, List.getLast?_nil, Option.getD_none,
            BEq.rfl, ↓reduceIte, List.getLast?_singleton, Option.getD_some]
        · rw [ite_eq_right (by simpa using getLastD_ne_nil' hnilt he)]
          cases h : rng (ts s) cl (dsT s v) with
          | nil => exact absurd h he
          | cons a t => simp only [List.getLastD_eq_getLast?, List.getLast?_cons_cons]
    · simp only [hut, ite_false]
      exact S.ends u hu

/-- **The order invariant after a sweep step.** -/
theorem Shape.drain_shape (hL : LList (cN s) (cP s) s.firstChunk cl)
    (hcs : ∀ c ∈ cl, c < s.C.size) (tag : Nat)
    (htag : tag = tagF (ts (dsS s v tag)) (dsY s v)) : Shape (ts (dsS s v tag)) cl ord := by
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  have T := dsS_sameTree (tag := tag) hvt hv htz
  have hP : (ts (dsS s v tag)).P = (ts s).P := dsS_P s v tag
  obtain ⟨hy, hanc, hLe, hRi, -⟩ := S.pick hg hne
  obtain ⟨hycl, hypp, -, -, -⟩ := S.rng_ghost hg hy
  have hpp := S.ds_pp hg hne tag
  have ST := S.drain_shapeT hg hne tag
  have hpar : ∀ k e, par (ts (dsS s v tag)) k e = par (ts s) k e := T.par
  refine {
    toShapeT := ST
    up := ?_
    lp := ?_
    kids := ?_
    OT := ?_
    ghost := ?_
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
    tags := ?_ }
  · intro u hu hh; rw [T.liveN] at hu; rw [T.ht, hP] at hh
    simp only [T.liveN, T.livePar, T.ht, T.children]; exact S.up u hu hh
  · intro c hc; simp only [T.lpr, T.liveN, T.ht, T.children]; exact S.lp c hc
  · intro u hu; rw [T.liveN] at hu; simp only [T.children, T.ht, hpar, T.liveN]; exact S.kids u hu
  · intro h h1 h2 u u' e e' hu hu' hb he he' hpe hpe'
    rw [hP] at h2; rw [T.liveN] at hu hu'; rw [hpar] at hpe hpe'
    exact S.OT h h1 h2 u u' e e' hu hu' hb he he' hpe hpe'
  · intro u hu; rw [T.ghostN] at hu
    simp only [T.t1, T.t2, T.liveN, T.ht, T.srcOf, T.livePar, T.children, hP]; exact S.ghost u hu
  · intro t ht' hs; rw [T.liveN] at ht'; rw [T.srcOf] at hs ⊢
    simp only [T.ghostN, T.t1, T.t2]; exact S.src t ht' hs
  · intro X hX e he; rw [T.isN] at hX; rw [T.order] at he; rw [T.ht]; exact S.tabEnt X hX e he
  · intro h e X he; rw [T.tabs, T.isN, T.ht, T.order]; exact S.tabsIff h e X he
  · intro h e he; rw [T.tabs]; exact S.tabsNodup h e he
  · intro h e X he hX; rw [T.tabs] at hX; rw [hpar, T.srcOf]; exact S.Q h e X he hX
  · intro u hu X hX; rw [T.ghostN] at hu; rw [T.ht, T.tabs] at hX
    rw [T.order, T.t1, T.t2]; exact S.W1 u hu X hX
  · intro u hu e he; rw [T.ghostN] at hu; rw [T.order] at he
    rw [T.side, T.ht, hpar, T.t1]; exact S.side u hu e he
  · intro c hc
    change ((dsS s v tag).path.getX c).size = _
    rw [dsS_path, Array.getX_setX, hP]
    split_ifs with h
    · subst h
      have h1 : (s.path.getX (dsY s v)).size = s.P.H + 1 := S.pathSize _ hc
      have h2 : (s.nodes.getX v).height < s.P.H := hhH
      rw [Array.size_setX, ite_eq_left (by omega)]; exact h1
    · exact S.pathSize c hc
  · intro c hc j hj1 hj
    rw [hP] at hj
    rw [hpp, T.anc]
    by_cases hcj : c = dsY s v ∧ j = ht (ts s) v
    · obtain ⟨rfl, rfl⟩ := hcj
      rw [ite_eq_left ⟨rfl, rfl⟩]; left; exact hanc.symm
    · rw [ite_eq_right hcj]
      rcases S.P c hc j hj1 hj with h | ⟨h1, h2⟩
      · left; exact h
      · right; rw [T.ghostN, T.t1, T.t2]; exact ⟨h1, h2⟩
  · intro c hc j hj1 hj hgj
    rw [hP] at hj
    rw [hpp] at hgj ⊢
    rw [T.order, T.anc]
    by_cases hcj : c = dsY s v ∧ j = ht (ts s) v
    · rw [ite_eq_left hcj] at hgj; rw [T.ghostN] at hgj
      exact absurd hgj.2 (by rw [hlive.2]; simp)
    · rw [ite_eq_right hcj] at hgj; rw [T.ghostN] at hgj
      by_cases hcj1 : c = dsY s v ∧ j - 1 = ht (ts s) v
      · obtain ⟨rfl, hj1'⟩ := hcj1
        rw [ite_eq_left ⟨rfl, hj1'⟩]
        -- the target is next to the ghost in every table holding it
        have hsr := S.Sr _ hycl j hj1 hj hgj
        rw [hj1', hypp] at hsr
        obtain ⟨hal, hah⟩ := S.anc_live hycl j hj1 hj
        have hX : anc (ts s) (dsY s v) j ∈ tabs (ts s) (ht (ts s) v) v :=
          (S.tabsIff _ v _ ((S.ordMem _ hh1 (by omega) v).mpr ⟨hg.1, rfl⟩)).mpr
            ⟨hal.1, by rw [hah]; omega, hsr⟩
        have hw1 := (S.W1 v hg _ hX).subset
        rcases (show dsT s v = (nd (ts s) v).t1 ∨ dsT s v = (nd (ts s) v).t2 by
            by_cases h : goesLeft s v
            · exact Or.inl (hLe h).2
            · exact Or.inr (hRi h).2) with e | e <;> rw [e] <;> exact hw1 (by simp)
      · rw [ite_eq_right hcj1]; exact S.Sr c hc j hj1 hj hgj
  · intro u hu; rw [T.isN] at hu; exact S.ds_ends hg hne hL tag u hu
  · intro c hc
    rw [dsS_tag s v tag (hcs _ hycl)]
    split_ifs with h
    · subst h; exact htag
    · rw [S.ds_tagF_other hg hne tag c h]; exact S.tags c hc

end facts

/-! ### Timing, room and the job after the step -/

section job
variable {s s' : TS} (T : SameTree s s')
include T

theorem SameTree.pend_fund (j : Job) (w up v k k' : Nat) :
    pend s' (some { j with pc := .fund w up v k' }) =
      pend s (some { j with pc := .fund w up v k }) := by
  change Top.upChain s' (s'.P.H + 1) up = Top.upChain s (s.P.H + 1) up
  rw [T.upChain, T.P]

theorem SameTree.funded (oj : Option Job) (u : Nat) : funded s' oj u ↔ funded s oj u := by
  unfold Top.funded; cases oj <;> simp only [T.anc, T.ht, T.t1, T.t2]

theorem SameTree.slack_other (j : Job) (w up v k k' u : Nat) (hu : u ≠ v) :
    slack s' (some { j with pc := .fund w up v k' }) u =
      slack s (some { j with pc := .fund w up v k }) u := by
  unfold slack curH
  simp only [T.anc, T.ht, T.t1, T.t2, T.P, ite_eq_right (Ne.symm hu)]

theorem SameTree.slack_self (j : Job) (w up v k k' : Nat) (hw : Top.ht s w = Top.ht s v)
    (hf : Top.anc s j.y (Top.ht s v) = (nd s v).t1 ∨ Top.anc s j.y (Top.ht s v) = (nd s v).t2) :
    slack s' (some { j with pc := .fund w up v k' }) v = s.P.s - k' ∧
      slack s (some { j with pc := .fund w up v k }) v = s.P.s - k := by
  unfold slack curH
  simp only [T.anc, T.ht, T.t1, T.t2, T.P, hw]
  simp only [ite_eq_left hf, show ¬ (Top.ht s v + 1 ≤ Top.ht s v) by omega, ite_false, ite_true,
    and_self]

end job

/-- **A sweep step keeps the invariant**, and moves the funding loop on. -/
theorem inv_drainMove {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {w up v k : Nat}
    (hI : InvJ (ts s) cl ord dr n0 (some { j with pc := .fund w up v k }))
    (hL : LList (cN s) (cP s) s.firstChunk cl) (hcs : ∀ c ∈ cl, c < s.C.size)
    (hk : k < s.P.s) (hne : rng (ts s) cl v ≠ []) :
    ∃ s', (drainStep v).run s = .ok true s' ∧ TopRel s s' ∧
      InvJ (ts s') cl ord dr n0 (some { j with pc := .fund w up v (k + 1) }) ∧
      ∀ u, ht (ts s') u = ht (ts s) u := by
  have S := hI.shape
  obtain ⟨hpos, hat⟩ := hI.job _ rfl
  simp only [JobAt] at hat
  obtain ⟨hwl, hwa, hua, hg, hsw, hks⟩ := hat
  obtain ⟨hrun, htag⟩ := S.drain_run hg hne hL
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  set tag := dsTag s v _ _ _ _
  have T := dsS_sameTree (tag := tag) hvt hv htz
  refine ⟨_, hrun, ?_, ?_, T.ht⟩
  · have := top_drainStep v s; rw [hrun] at this; exact this
  have hW : ∀ u, (nd (ts (dsS s v tag)) u).weight = (nd (ts s) u).weight :=
    dsS_weight (tag := tag) hvt hv htz
  have SH := S.drain_shape hg hne hL hcs tag htag
  obtain ⟨hy, -, -, -, -⟩ := S.pick hg hne
  -- the walk node is a target of the ghost
  have hsrc := S.src w hwl (by rw [hsw]; exact fun e => hg.1.1 e)
  rw [hsw] at hsrc
  have hwh : ht (ts s) w = ht (ts s) v := by
    obtain ⟨-, -, h1, h2, -⟩ := S.ghost v hg
    rcases hsrc.2 with e | e <;> rw [e] <;> assumption
  have hfun : anc (ts s) j.y (ht (ts s) v) = (nd (ts s) v).t1 ∨
      anc (ts s) j.y (ht (ts s) v) = (nd (ts s) v).t2 := by
    rw [← hwh, ← hwa]; exact hsrc.2
  have Ti := hI.time
  have Ro := hI.room
  refine ⟨SH, ?_, ?_, ?_, by rw [T.P]; exact hI.cap, hI.len.congr fun X => ⟨T.order X, T.side X⟩⟩
  · refine ⟨fun u hu => ?_, fun u hu hp hs => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_,
      fun u hu => ?_, fun u hu hu' => ?_, fun u hu hs => ?_, ?_, ?_⟩
    · rw [T.liveN] at hu; rw [hW, T.pend_fund j w up v k (k + 1), T.tw]; exact Ti.wts u hu
    · rw [T.liveN] at hu; rw [T.livePar] at hp; rw [T.srcOf] at hs
      rw [hW, T.ht, T.P]; exact Ti.wA u hu hp hs
    · rw [T.ghostN] at hu; rw [hW, T.ht, T.P]; exact Ti.wB u hu
    · rw [T.ghostN] at hu; rw [hW, T.ew]; exact Ti.wF u hu
    · rw [T.ghostN] at hu
      rw [T.fundOf cl u (hW u), hW, T.P]
      have hold := Ti.wC u hu
      by_cases huv : u = v
      · subst huv
        rw [S.ds_rng hg hne tag, ite_eq_left rfl]
        obtain ⟨e1, e2⟩ := T.slack_self j w up u k (k + 1) hwh hfun
        rw [e1]; rw [e2] at hold
        rw [List.length_erase_of_mem hy]
        have := List.length_pos_of_mem hy
        omega
      · rw [S.ds_rng hg hne tag, ite_eq_right huv, ite_eq_right (fun e => by
          rw [e] at hu; exact absurd hu.2 (by rw [hlive.2]; simp)),
          T.slack_other j w up v k (k + 1) u huv]
        exact hold
    · rw [T.ghostN] at hu
      rw [T.fundOf cl u (hW u), hW, T.P]
      have := Ti.wC' u hu
      by_cases hf : funded (ts s) (some { j with pc := .fund w up v k }) u
      · rw [ite_eq_left ((T.funded _ u).mpr (by unfold funded at hf ⊢; exact hf))]
        rw [ite_eq_left hf] at this; exact this
      · rw [ite_eq_right (fun h => hf (by
          have := (T.funded _ u).mp h
          unfold funded at this ⊢
          exact this))]
        rw [ite_eq_right hf] at this; exact this
    · rw [T.liveN] at hu; rw [T.P] at hu'; rw [T.tw, T.ht, T.P]; exact Ti.wD u hu hu'
    · rw [T.liveN] at hu; rw [T.srcOf] at hs; rw [T.P]; exact Ti.big u hu hs
    · intro u hu hH; rw [T.isN] at hu; rw [T.P] at hH; rw [T.ht]; exact Ti.chain u hu hH
    · intro u hu; rw [T.liveN] at hu; rw [T.tw]; exact Ti.tw1 u hu
  · refine ⟨fun X hX => ?_, fun X hX => ?_, fun X hX h1 => ?_, fun X hX h2 => ?_⟩
    · rw [T.isN] at hX; rw [T.labs, T.P]; exact Ro.gaps X hX
    · rw [T.isN] at hX; rw [T.ht, T.P]; exact Ro.n0le X hX
    · rw [T.isN] at hX; rw [T.ht] at h1; rw [T.ew, T.P]; exact Ro.pot1 X hX h1
    · rw [T.isN] at hX; rw [T.ht] at h2; rw [T.ew, T.growth, T.oldLive, T.ht, T.P]
      exact Ro.pot2 X hX h2
  · intro j' hj'
    cases hj'
    refine ⟨hpos, ?_⟩
    simp only [JobAt]
    rw [T.liveN, T.ht, T.anc, T.anc, T.ghostN, T.srcOf, T.P]
    exact ⟨hwl, hwa, hua, hg, hsw, show k + 1 ≤ s.P.s by omega⟩

end OrderMaintenance.Proof.Top
