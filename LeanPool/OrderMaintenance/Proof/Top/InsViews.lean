/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.CopyRest


/-!
# M5: the state after a chunk split, with the path copy completed

`insFin s x`: the top structure after `insertAround x y z` (`y, z` the new chunks) on the linked
core, with the job's path copy completed. Its views, field by field.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
theorem ts_tag (t : Core) (c : Nat) : (ts t).tag c = (t.C.getX c).tag := rfl
theorem ts_nodes (t : Core) : (ts t).nodes = t.nodes := rfl
theorem ts_path (t : Core) : (ts t).path = t.path := rfl
theorem ts_cin (t : Core) : (ts t).cin = t.cin := rfl
theorem ts_lpar (t : Core) : (ts t).lpar = t.lpar := rfl
theorem ts_P (t : Core) : (ts t).P = t.P := rfl

theorem ts_markState (t : Core) (x y z : Nat) (j : Job) : ts (markState t x y z j) = ts t := by
  unfold ts markState
  congr 1
  funext c
  simp only [Array.getX_modify]
  split_ifs <;> rfl

section defs
variable (s : Core) (x : Nat)

/-- The split's job. -/
def insJob : Job := { x := x, y := s.C.size, z := s.C.size + 1, pc := .copy 1 }

/-- The core with the two new chunks linked around `x`. -/
def ins0 : Core := linkChunkPair (push2 s) x s.C.size (s.C.size + 1)

/-- The labels of the new entries in table `T`. -/
def insF (T : Nat) : Nat × Nat :=
  (roomL s.P.beta (s.nodes.getX T).table x true, roomL s.P.beta (s.nodes.getX T).table x false)

variable (f1x i1 : Nat)

/-- The core after `insertAround`. -/
def ins3 : Core :=
  insFinS (tagsS (ins0 s x) s.C.size (s.C.size + 1) (tagY (ins0 s x) x f1x i1) (tagZ (ins0 s x)
    x f1x i1))
    x s.C.size (s.C.size + 1) (insF s x)

/-- The top structure after the split, path copy completed. -/
def insFin : TS := copyRest (insJob s x) s.P.H (ts (ins3 s x f1x i1)) 1

end defs

/-! ### The core after `insertAround` -/

section generic
variable (t : Core) (x y z : Nat) (f : Nat → Nat × Nat)

theorem insFinS_P : (insFinS t x y z f).P = t.P := by unfold insFinS joinS; rfl
theorem insFinS_C : (insFinS t x y z f).C = t.C := by unfold insFinS joinS; rfl
theorem insFinS_path : (insFinS t x y z f).path =
    (t.path.setX y (Array.replicate (t.P.H + 1) NIL)).setX z (Array.replicate (t.P.H + 1) NIL) := by
  unfold insFinS joinS; rfl
theorem insFinS_cin : (insFinS t x y z f).cin = (t.cin.setX y (t.cin.getX x)).setX z (t.cin.getX
  x) := by
  unfold insFinS joinS; rfl
theorem insFinS_lpar : (insFinS t x y z f).lpar = (t.lpar.setX y (t.lpar.getX x)).setX z
  (t.lpar.getX x) := by
  unfold insFinS joinS; rfl
theorem insFinS_nodes : (insFinS t x y z f).nodes =
    ((t.cin.getX x).foldl (fun ns T => ns.modify T (aroundF t x y z f T)) t.nodes).modify
      (t.lpar.getX x)
        (fun n => { n with children := n.children.replace1 x [y, x, z] }) := by
  unfold insFinS joinS; rfl

variable (a b : Nat)
theorem tagsS_top : (tagsS t y z a b).P = t.P ∧ (tagsS t y z a b).path = t.path ∧
    (tagsS t y z a b).cin = t.cin ∧ (tagsS t y z a b).lpar = t.lpar ∧ (tagsS t y z a b).nodes =
      t.nodes ∧
    (tagsS t y z a b).C = (t.C.modify y fun C => { C with tag := a }).modify z fun C => { C with
      tag := b } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end generic

section views
variable (s : Core) (x f1x i1 : Nat)

theorem ins0_top : (ins0 s x).nodes = s.nodes ∧ (ins0 s x).path = s.path ∧ (ins0 s x).cin = s.cin ∧
    (ins0 s x).lpar = s.lpar ∧ (ins0 s x).P = s.P ∧ (ins0 s x).C.size = s.C.size + 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold ins0
  rw [(linkChunkPair_rest (s := push2 s) (x := x) (y := s.C.size) (z := s.C.size +
    1)).2.2.2.2.2.2.1]
  simp [push2]

theorem ins0_tag {c : Nat} (hc : c < s.C.size) : ((ins0 s x).C.getX c).tag = (s.C.getX c).tag := by
  have := linkChunkPair_cT (s := push2 s) (x := x) (y := s.C.size) (z := s.C.size + 1) c
  unfold cT at this; unfold ins0; rw [this]
  simp [push2, Array.getX_push, Nat.ne_of_lt hc, show c ≠ s.C.size + 1 by omega]

/-- The core right before `insertAroundFinish`: both tags written. -/
abbrev ins2 : Core :=
  tagsS (ins0 s x) s.C.size (s.C.size + 1) (tagY (ins0 s x) x f1x i1) (tagZ (ins0 s x) x f1x i1)

theorem ins3_eq : ins3 s x f1x i1 = insFinS (ins2 s x f1x i1) x s.C.size (s.C.size + 1) (insF s
  x) := rfl

theorem ins2_top : (ins2 s x f1x i1).P = s.P ∧ (ins2 s x f1x i1).path = s.path ∧
    (ins2 s x f1x i1).cin = s.cin ∧ (ins2 s x f1x i1).lpar = s.lpar ∧ (ins2 s x f1x i1).nodes =
      s.nodes := by
  obtain ⟨t1, t2, t3, t4, t5, -⟩ := tagsS_top (ins0 s x) s.C.size (s.C.size + 1)
    (tagY (ins0 s x) x f1x i1) (tagZ (ins0 s x) x f1x i1)
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := ins0_top s x
  exact ⟨t1.trans u5, t2.trans u2, t3.trans u3, t4.trans u4, t5.trans u1⟩

theorem ins3_P : (ins3 s x f1x i1).P = s.P := by rw [ins3_eq, insFinS_P, (ins2_top s x f1x i1).1]
theorem ins3_path : (ins3 s x f1x i1).path =
    (s.path.setX s.C.size (Array.replicate (s.P.H + 1) NIL)).setX (s.C.size + 1)
      (Array.replicate (s.P.H + 1) NIL) := by
  rw [ins3_eq, insFinS_path, (ins2_top s x f1x i1).1, (ins2_top s x f1x i1).2.1]
theorem ins3_cin : (ins3 s x f1x i1).cin = (s.cin.setX s.C.size (s.cin.getX x)).setX (s.C.size +
  1) (s.cin.getX x) := by
  rw [ins3_eq, insFinS_cin, (ins2_top s x f1x i1).2.2.1]
theorem ins3_lpar : (ins3 s x f1x i1).lpar =
    (s.lpar.setX s.C.size (s.lpar.getX x)).setX (s.C.size + 1) (s.lpar.getX x) := by
  rw [ins3_eq, insFinS_lpar, (ins2_top s x f1x i1).2.2.2.1]
theorem ins3_nodes : (ins3 s x f1x i1).nodes =
    ((s.cin.getX x).foldl (fun ns T => ns.modify T (aroundF (ins2 s x f1x i1) x s.C.size
      (s.C.size + 1) (insF s x) T)) s.nodes).modify (s.lpar.getX x) (fun n => {
      n with children := n.children.replace1 x [s.C.size, x, s.C.size + 1] }) := by
  rw [ins3_eq, insFinS_nodes, (ins2_top s x f1x i1).2.2.1, (ins2_top s x f1x i1).2.2.2.1,
    (ins2_top s x f1x i1).2.2.2.2]

theorem ins3_tag (c : Nat) :
    (ts (ins3 s x f1x i1)).tag c = if c = s.C.size + 1 then tagZ (ins0 s x) x f1x i1
      else if c = s.C.size then tagY (ins0 s x) x f1x i1 else (s.C.getX c).tag := by
  rw [ts_tag, ins3_eq, insFinS_C, (tagsS_top (ins0 s x) s.C.size (s.C.size + 1)
    (tagY (ins0 s x) x f1x i1) (tagZ (ins0 s x) x f1x i1)).2.2.2.2.2]
  show ((((ins0 s x).C.modify s.C.size fun C => { C with tag := tagY (ins0 s x) x f1x i1 }).modify
      (s.C.size + 1) fun C => { C with tag := tagZ (ins0 s x) x f1x i1 }).getX c).tag = _
  have hsz := (ins0_top s x).2.2.2.2.2
  rw [Array.getX_modify, Array.getX_modify, Array.size_modify', hsz]
  by_cases hz : c = s.C.size + 1
  · subst hz; simp
  · by_cases hy : c = s.C.size
    · subst hy; simp
    · simp only [Ne.symm hz, Ne.symm hy, false_and, ite_false, hz, hy]
      have := linkChunkPair_cT (s := push2 s) (x := x) (y := s.C.size) (z := s.C.size + 1) c
      unfold cT at this; unfold ins0; rw [this]
      by_cases hc : c < s.C.size
      · simp [push2, Array.getX_push, Nat.ne_of_lt hc, show c ≠ s.C.size + 1 by omega]
      · have h1 : s.C.getX c = default := by unfold Array.getX Array.getD; rw [dite_eq_right hc]
        simp only [push2, Array.getX_push, Array.size_push, hz, hy, ite_false, h1]

end views

/-! ### The top structure after the split, copy completed -/

section fin
variable (s : Core) (x f1x i1 : Nat)

/-- The new tables: entries `y`, `z` around `x` in every table holding `x`. -/
def insNode (u : Nat) : Node :=
  let n := s.nodes.getX u
  let n1 := if u ∈ s.cin.getX x ∧ u < s.nodes.size then
    setTS (aroundT n.table x s.C.size (s.C.size + 1) (insF s x u).1 (insF s x u).2)
      (sideAround n x s.C.size (s.C.size + 1)) n else n
  if u = s.lpar.getX x ∧ u < s.nodes.size then
    { n1 with children := n1.children.replace1 x [s.C.size, x, s.C.size + 1] } else n1

theorem ins3_getX (hnd : (s.cin.getX x).Nodup) (u : Nat) :
    (ins3 s x f1x i1).nodes.getX u = insNode s x u := by
  rw [ins3_nodes, Array.getX_modify, foldl_modify_size]
  unfold insNode
  simp only
  have hfold : ((s.cin.getX x).foldl (fun ns T => ns.modify T (aroundF (ins2 s x f1x i1) x
    s.C.size (s.C.size + 1) (insF s x) T)) s.nodes).getX u =
      if u ∈ s.cin.getX x ∧ u < s.nodes.size then
        setTS (aroundT (s.nodes.getX u).table x s.C.size (s.C.size + 1) (insF s x u).1 (insF s x
          u).2)
          (sideAround (s.nodes.getX u) x s.C.size (s.C.size + 1)) (s.nodes.getX u)
      else s.nodes.getX u := by
    rw [foldl_modify_getX' _ (s.cin.getX x) hnd]
    split
    · unfold aroundF
      rw [(ins2_top s x f1x i1).2.2.2.2]
    · rfl
  rw [hfold]
  by_cases hu : u = s.lpar.getX x ∧ u < s.nodes.size
  · rw [ite_eq_left ⟨hu.1.symm, by rw [← hu.1]; exact hu.2⟩, ite_eq_left hu]
  · rw [ite_eq_right (fun h => hu ⟨h.1.symm, by rw [← h.1]; exact h.2⟩), ite_eq_right hu]

/-- The new chunks take over the first and last range pointers along the split chunk path. -/
def insFirst (u : Nat) : Nat :=
  if cpHit (insJob s x) s.P.H (ts s) 1 u = true ∧ (s.nodes.getX u).first = x then s.C.size
  else (s.nodes.getX u).first
/-- A node's range endpoint after inserting replacement chunks along the copied path. -/
def insLast (u : Nat) : Nat :=
  if cpHit (insJob s x) s.P.H (ts s) 1 u = true ∧ (s.nodes.getX u).last = x then s.C.size + 1
  else (s.nodes.getX u).last

/-- The views of the top structure after the split, with the copy completed. -/
structure InsFrame (t : TS) : Prop where
  P : t.P = s.P
  size : t.nodes.size = s.nodes.size
  node : ∀ u, nd t u = { insNode s x u with first := insFirst s x u, last := insLast s x u }
  path : ∀ c i, pth t c i = if c = s.C.size ∨ c = s.C.size + 1 then
    (if 1 ≤ i ∧ i ≤ s.P.H then pth (ts s) x i else NIL) else pth (ts s) c i
  psize : ∀ c, (c = s.C.size ∨ c = s.C.size + 1) → (t.path.getX c).size = s.P.H + 1
  pother : ∀ c, c ≠ s.C.size → c ≠ s.C.size + 1 → t.path.getX c = s.path.getX c
  cin : ∀ c, cinT t c = if c = s.C.size ∨ c = s.C.size + 1 then cinT (ts s) x else cinT (ts s) c
  lpar : ∀ c, lpr t c = if c = s.C.size ∨ c = s.C.size + 1 then lpr (ts s) x else lpr (ts s) c
  tag : ∀ c, t.tag c = if c = s.C.size + 1 then tagZ (ins0 s x) x f1x i1
    else if c = s.C.size then tagY (ins0 s x) x f1x i1 else (s.C.getX c).tag

theorem insFin_frame (hxs : x < s.C.size) (hnd : (s.cin.getX x).Nodup)
    (hdist : ∀ i i', 1 ≤ i → i ≤ s.P.H → 1 ≤ i' → i' ≤ s.P.H → pth (ts s) x i = pth (ts s) x i'
      → i = i')
    (hex : ∀ i, 1 ≤ i → i ≤ s.P.H → pth (ts s) x i < s.nodes.size) :
    InsFrame s x f1x i1 (insFin s x f1x i1) := by
  set t3 := ts (ins3 s x f1x i1) with ht3
  have hxy : x ≠ s.C.size := by omega
  have hxz : x ≠ s.C.size + 1 := by omega
  have hpath3 : ∀ c, t3.path.getX c = if c = s.C.size + 1 then Array.replicate (s.P.H + 1) NIL
      else if c = s.C.size then Array.replicate (s.P.H + 1) NIL else s.path.getX c := fun c => by
    rw [ht3, ts_path, ins3_path, Array.getX_setX, Array.getX_setX]
  have hpx : ∀ i, pth t3 x i = pth (ts s) x i := fun i => by
    unfold pth; rw [hpath3, ite_eq_right hxz, ite_eq_right hxy]; rfl
  have hsize3 : t3.nodes.size = s.nodes.size := by
    rw [ht3, ts_nodes, ins3_nodes, Array.size_modify', foldl_modify_size]
  have hok : CopyOK (insJob s x) s.P.H t3 1 :=
    ⟨by simp [insJob], by simp [insJob]; omega, by simp [insJob]; omega,
      fun i i' h1 h2 h3 h4 e => hdist i i' h1 h2 h3 h4 (by rw [← hpx, ← hpx]; exact e),
      by simp [insJob, hpath3], by simp [insJob, hpath3]⟩
  have hP3 : t3.P = s.P := by rw [ht3, ts_P, ins3_P]
  have ex : (insJob s x).x = x := rfl
  have ey : (insJob s x).y = s.C.size := rfl
  have ez : (insJob s x).z = s.C.size + 1 := rfl
  obtain ⟨cP, cC, cL, cT, cS, cO, cY, cZ, cSy, cSz, cN⟩ := copyRest_views (insJob s x) s.P.H
    (s.P.H + 1 - 1) t3 1 rfl hok (fun i h1 h2 => by rw [ex, hpx, hsize3]; exact hex i h1 h2)
  simp only [ex, ey, ez] at cO cY cZ cSy cSz
  have hfin : insFin s x f1x i1 = copyRest (insJob s x) s.P.H t3 1 := rfl
  rw [hfin]
  refine ⟨cP.trans hP3, cS.trans hsize3, fun u => ?_, fun c i => ?_, fun c hc => ?_, fun c h1 h2
    => ?_,
    fun c => ?_, fun c => ?_, fun c => ?_⟩
  · rw [cN]
    have hn3 : nd t3 u = insNode s x u := by rw [ht3]; exact ins3_getX s x f1x i1 hnd u
    have hhit : cpHit (insJob s x) s.P.H t3 1 u = cpHit (insJob s x) s.P.H (ts s) 1 u := by
      unfold cpHit; simp only [show (insJob s x).x = x from rfl, hpx]
    have hf : (insNode s x u).first = (s.nodes.getX u).first := by
      unfold insNode; split_ifs <;> rfl
    have hl : (insNode s x u).last = (s.nodes.getX u).last := by
      unfold insNode; split_ifs <;> rfl
    unfold cpFirst cpLast insFirst insLast
    rw [hn3, hhit, hf, hl]; rfl
  · by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · rw [ite_eq_left hc]
      rcases hc with rfl | rfl
      · have := cY i
        change ((copyRest (insJob s x) s.P.H t3 1).path.getX s.C.size).getX i = _
        rw [this, hpx]
        split
        · rfl
        · rw [hpath3, ite_eq_right (by omega), ite_eq_left rfl]
          by_cases hi : i < s.P.H + 1
          · simp [Array.getX, Array.getD, hi]
          · simp [Array.getX, Array.getD, hi]
      · have := cZ i
        change ((copyRest (insJob s x) s.P.H t3 1).path.getX (s.C.size + 1)).getX i = _
        rw [this, hpx]
        split
        · rfl
        · rw [hpath3, ite_eq_left rfl]
          by_cases hi : i < s.P.H + 1
          · simp [Array.getX, Array.getD, hi]
          · simp [Array.getX, Array.getD, hi]
    · rw [ite_eq_right hc]
      push Not at hc
      unfold pth; rw [cO c hc.1 hc.2, hpath3, ite_eq_right hc.2, ite_eq_right hc.1]; rfl
  · rcases hc with rfl | rfl
    · rw [cSy, hpath3, ite_eq_right (by omega), ite_eq_left rfl]; simp
    · rw [cSz, hpath3, ite_eq_left rfl]; simp
  · rw [cO c h1 h2, hpath3, ite_eq_right h2, ite_eq_right h1]
  · unfold cinT; rw [cC, ht3, ts_cin, ins3_cin, Array.getX_setX, Array.getX_setX]
    by_cases h1 : c = s.C.size + 1
    · simp [h1]; rfl
    · by_cases h2 : c = s.C.size
      · simp [h2]; rfl
      · simp [h1, h2]; rfl
  · unfold lpr; rw [cL, ht3, ts_lpar, ins3_lpar, Array.getX_setX, Array.getX_setX]
    by_cases h1 : c = s.C.size + 1
    · simp [h1]; rfl
    · by_cases h2 : c = s.C.size
      · simp [h2]; rfl
      · simp [h1, h2]; rfl
  · rw [cT, ht3, ins3_tag]

end fin

end OrderMaintenance.Proof.Top
