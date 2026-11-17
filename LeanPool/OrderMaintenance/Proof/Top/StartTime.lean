/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartShape


/-!
# M5: weights, drain timing and label room after a drain starts
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
theorem foldr_sum (l : List Nat) (f : Nat → Nat) : l.foldr (fun e acc => acc + f e) 0 = (l.map
  f).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]; omega

/-- One extra insertion event in each table holding `v`, and none in the new tables. -/
def drSD (dr : Nat → Nat) (tabs : List Nat) (N : Nat) (T : Nat) : Nat :=
  if T ∈ tabs then dr T + 1 else if T = N ∨ T = N + 1 then 0 else dr T

/-- The initial sizes after a drain starts. -/
def n0SD (n0 : Nat → Nat) (N lL lR : Nat) (T : Nat) : Nat :=
  if T = N then lL else if T = N + 1 then lR else n0 T

theorem length_replace1_le (l : List Nat) (x a b c : Nat) : (l.replace1 x [a, b, c]).length ≤
  l.length + 2 := by
  induction l with
  | nil => simp [List.replace1]
  | cons y t ih =>
    simp only [List.replace1]
    split
    · simp
    · simp only [List.length_cons]; omega

/-- The job after the walk starts a drain at `v` (`up` its live parent). -/
def drainJob (j : Job) (v up : Nat) : Job := { j with pc := .afterDrain v up }

namespace SDCtx

variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  {side : List (Nat × Side)} (C : SDCtx s cl ord dr n0 j v side)
include C

local notation "S'" => ts (sdS (wiC s v) v side)
local notation "O'" => ordSD ord (Top.ht (ts s) v) v s.nodes.size

/-- **The weight of a new node**: its part's children's, stored as its true weight. -/
theorem tw_new (w : Nat) (hw : w = s.nodes.size ∨ w = s.nodes.size + 1) :
    tw S' cl w = (nd S' w).weight ∧
      tw S' cl w = if Top.ht (ts s) v = 1 then (nd S' w).children.length
        else ((nd S' w).children.map (tw (ts s) cl)).sum := by
  have SH := C.shape
  have hvlt := C.H.hv
  have hwl : Top.liveN S' w := (C.liveN w).mpr (Or.inr hw)
  obtain ⟨-, -, hkk⟩ := C.S.kids v C.vl
  have hch : ∀ e ∈ (nd S' w).children, e ∈ (nd (ts s) v).children := by
    intro e he
    rw [C.children, ite_eq_right (by omega)] at he
    rcases hw with rfl | rfl
    · rw [ite_eq_left rfl] at he; exact List.mem_of_mem_take he
    · rw [ite_eq_right (by omega), ite_eq_left rfl] at he; exact List.mem_of_mem_drop he
  have hwt : (nd S' w).weight = ((nd S' w).children.map (sWt (wiC s v) v)).sum := by
    rw [C.H.weight]
    rcases hw with rfl | rfl
    · rw [ite_eq_left rfl, C.children, ite_eq_right (by omega), ite_eq_left rfl, C.ch.1]
    · rw [ite_eq_right (by omega), ite_eq_left rfl, C.children, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left rfl, C.ch.2]
  have hwh : Top.ht S' w = Top.ht (ts s) v := by rw [C.ht w, ite_eq_left hw]
  by_cases h1 : Top.ht (ts s) v = 1
  · rw [ite_eq_left h1, SH.tw_one hwl (by rw [hwh, h1]), hwt]
    have : ((nd S' w).children.map (sWt (wiC s v) v)) = List.replicate (nd S' w).children.length
      1 := by
      rw [List.eq_replicate_iff]; simp only [List.length_map, true_and]
      intro x hx; obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
      unfold sWt drainWt; rw [sd_h_eq, h1]; rfl
    rw [this]; simp
  · have h2 : 2 ≤ Top.ht (ts s) v := by have := C.h1; omega
    have hsum : ((nd S' w).children.map (tw S' cl)) = ((nd S' w).children.map (tw (ts s) cl)) := by
      apply List.map_congr_left; intro e he
      have hek := hch e he
      have hel := (hkk e hek).2 h2
      have hev : e ≠ v := by
        intro e'; have := ((C.S.mem_children C.vl).mp hek).1; rw [ite_eq_right h1, e'] at this;
          omega
      exact C.tw_old hel.1 hev
    have hws : ((nd S' w).children.map (sWt (wiC s v) v)) = ((nd S' w).children.map (tw (ts s)
      cl)) := by
      apply List.map_congr_left; intro e he
      have hek := hch e he
      have hev : e ≠ v := by
        intro e'; have := ((C.S.mem_children C.vl).mp hek).1; rw [ite_eq_right h1, e'] at this;
          omega
      unfold sWt drainWt
      rw [sd_h_eq, ite_eq_right (by simp; omega), ← sd_kid_weight C.pc C.v0 C.I C.lp hek h2]
      change ((s.nodes.modify v _).getX e).weight = _
      rw [Array.getX_modify, ite_eq_right (fun h' => hev h'.1.symm)]; rfl
    rw [ite_eq_right h1, SH.tw_kids hwl (by rw [hwh]; exact h2), hsum, hwt, hws]
    exact ⟨rfl, rfl⟩

/-- The drained node served what its two targets now serve. -/
theorem ew_v : ew S' cl v = tw (ts s) cl v := by
  have hvlt := C.H.hv
  have SH := C.shape
  obtain ⟨hknd, -, hkk⟩ := C.S.kids v C.vl
  have hd : (nd S' v).draining = true := by rw [C.draining', ite_eq_left rfl]
  have ht1 : (nd S' v).t1 = s.nodes.size := by rw [C.H.t1, ite_eq_left rfl]
  have ht2 : (nd S' v).t2 = s.nodes.size + 1 := by rw [C.H.t2, ite_eq_left rfl]
  unfold ew
  rw [ite_eq_left hd, ht1, ht2]
  obtain ⟨-, a1⟩ := C.tw_new _ (Or.inl rfl)
  obtain ⟨-, a2⟩ := C.tw_new _ (Or.inr rfl)
  rw [a1, a2, C.children s.nodes.size, ite_eq_right (show ¬(s.nodes.size = v) by omega),
    ite_eq_left rfl,
    C.children (s.nodes.size + 1), ite_eq_right (show ¬(s.nodes.size + 1 = v) by omega),
    ite_eq_right (show ¬(s.nodes.size + 1 = s.nodes.size) by omega), ite_eq_left rfl]
  by_cases h1 : Top.ht (ts s) v = 1
  · rw [ite_eq_left h1, ite_eq_left h1, List.length_take, List.length_drop, C.S.tw_one C.vl h1]
    have := C.k; omega
  · rw [ite_eq_right h1, ite_eq_right h1, C.S.tw_kids C.vl (by have := C.h1; omega),
    ← List.sum_append, ← List.map_append,
      List.take_append_drop]

/-- An old node serves as before. -/
theorem ew_old {X : Nat} (hX : Top.isN (ts s) X) : ew S' cl X = ew (ts s) cl X := by
  by_cases hXv : X = v
  · rw [hXv, C.ew_v]; unfold ew; rw [ite_eq_right (by rw [C.vl.2]; simp)]
  · have hXn := SDCtx.nN (s := s) X hX
    have hnn : ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) := fun h => h.elim hXn.1 hXn.2
    unfold ew
    rw [C.draining', ite_eq_right hXv, ite_eq_right hnn]
    split
    · next hd =>
      obtain ⟨g1, g2, -, -, h5, h6, -⟩ := C.S.ghost X ⟨hX, hd⟩
      have ht1v : (nd (ts s) X).t1 ≠ v := fun e => by
        rw [e] at h5
        rw [show Top.srcOf (ts s) v = NIL from C.of] at h5
        exact hX.1 h5.symm
      have ht2v : (nd (ts s) X).t2 ≠ v := fun e => by
        rw [e] at h6
        rw [show Top.srcOf (ts s) v = NIL from C.of] at h6
        exact hX.1 h6.symm
      rw [C.H.t1, C.H.t2, ite_eq_right hXv, ite_eq_right hXv, ite_eq_right hnn, ite_eq_right hnn,
        C.tw_old g1.1 ht1v, C.tw_old g2.1 ht2v]
    · exact C.tw_old hX hXv

/-- Live nodes above `v` keep their live parents. -/
theorem livePar_high {x : Nat} (hx : Top.liveN (ts s) x) (hh : Top.ht (ts s) v + 1 ≤ Top.ht (ts
  s) x) :
    (nd S' x).livePar = (nd (ts s) x).livePar :=
  C.livePar_old hx.1 (fun e => by rw [e] at hh; omega) (fun h1 hk => by
    have := ((C.S.mem_children C.vl).mp hk).1; rw [ite_eq_right h1] at this; omega)

theorem upChain_high : ∀ f x, (x = NIL ∨ (Top.liveN (ts s) x ∧ Top.ht (ts s) v + 1 ≤ Top.ht (ts
  s) x)) →
    upChain S' f x = upChain (ts s) f x
  | 0, _, _ => rfl
  | f + 1, x, hx => by
    simp only [upChain]
    split
    · rfl
    · next hx0 =>
      rcases hx with h | ⟨hl, hh⟩
      · exact absurd h hx0
      rw [C.livePar_high hl hh]
      congr 1
      apply upChain_high
      by_cases hH : Top.ht (ts s) x < s.P.H
      · obtain ⟨h1, h2, -⟩ := C.S.up x hl hH
        exact Or.inr ⟨h1, by omega⟩
      · left
        have hc := C.Ti.chain
        have hroot : x = s.P.H := by
          have h' : Top.ht (ts s) x ≤ s.P.H := (C.S.htN x hl.1).2
          have hm := (C.S.ordMem (ts s).P.H (by have := C.S.H3; omega) le_rfl x).mpr ⟨hl.1, by
            change Top.ht (ts s) x = s.P.H; omega⟩
          rw [C.S.root.1] at hm
          have : x = (ts s).P.H := by simpa using hm
          exact this
        rw [hroot]; exact C.S.root.2.2

/-- **The lagging nodes after the drain starts**: `v` has caught up. -/
theorem pend_mem {x : Nat} : x ∈ pend S' (some { j with pc := .afterDrain v (nd (ts s)
  v).livePar }) ↔
    x ∈ pend (ts s) (some j) ∧ x ≠ v := by
  obtain ⟨hl, hlh, -⟩ := C.up
  have hpold := sd_pend C.pc C.v0 C.I C.lp
  rw [hpold]
  unfold pend wStart
  simp only
  rw [SDHyps.P (s := s) (v := v) (side := side), C.upChain_high _ _ (Or.inr ⟨hl, by omega⟩)]
  have e : (ts s).P.H = s.P.H := rfl
  rw [e]
  have hvn : v ∉ upChain (ts s) (s.P.H + 1) (nd (ts s) v).livePar := by
    intro hm
    have := (C.S.upChain_mem _ _ v hl hm).2; omega
  constructor
  · intro h; exact ⟨List.mem_cons_of_mem _ h, fun e => hvn (e ▸ h)⟩
  · rintro ⟨h, hxv⟩
    rcases List.mem_cons.mp h with h | h
    · exact absurd h hxv
    · exact h


theorem y_mem : j.y ∈ cl := by
  obtain ⟨⟨A, B, hAB⟩, -⟩ := C.I.job j rfl
  rw [hAB]; simp

theorem rng_old {g : Nat} (hg : Top.isN (ts s) g) : rng S' cl g = rng (ts s) cl g := by
  have hn := SDCtx.nN (s := s) g hg
  unfold rng; rw [C.ht g, ite_eq_right (fun h => h.elim hn.1 hn.2)]; congr 1; funext c; rw
    [SDCtx.pp]

theorem funded_old {g : Nat} (hg : Top.ghostN (ts s) g) :
    funded S' (some (drainJob j v (nd (ts s) v).livePar)) g ↔ funded (ts s) (some j) g := by
  have hvlt := C.H.hv
  have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
  have hgn := SDCtx.nN (s := s) g hg.1
  have hgnn : ¬(g = s.nodes.size ∨ g = s.nodes.size + 1) := fun h => h.elim hgn.1 hgn.2
  obtain ⟨g1, g2, -, -, h5, h6, -⟩ := C.S.ghost g hg
  have ht1v : (nd (ts s) g).t1 ≠ v := fun e => by
    rw [e] at h5
    rw [show Top.srcOf (ts s) v = NIL from C.of] at h5
    exact hg.1.1 h5.symm
  have ht2v : (nd (ts s) g).t2 ≠ v := fun e => by
    rw [e] at h6
    rw [show Top.srcOf (ts s) v = NIL from C.of] at h6
    exact hg.1.1 h6.symm
  have h1n := SDCtx.nN (s := s) _ g1.1
  have h2n := SDCtx.nN (s := s) _ g2.1
  change Top.anc S' j.y (Top.ht S' g) = (nd S' g).t1 ∨ Top.anc S' j.y (Top.ht S' g) = (nd S' g).t2 ↔
    Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t1 ∨ Top.anc (ts s) j.y (Top.ht (ts s)
      g) = (nd (ts s) g).t2
  rw [C.ht g, ite_eq_right hgnn, C.H.t1, C.H.t2, ite_eq_right hgv, ite_eq_right hgv,
    ite_eq_right hgnn, ite_eq_right hgnn,
    C.anc C.y_mem _ (C.S.htN g hg.1).2]
  split
  · next hb =>
    rw [hb.1, hb.2]
    constructor
    · rintro (h | h) <;> split at h <;> omega
    · rintro (h | h)
      · exact absurd h.symm ht1v
      · exact absurd h.symm ht2v
  · rfl

theorem slack_old {g : Nat} (hg : Top.ghostN (ts s) g) : slack S' (some (drainJob j v (nd (ts s)
  v).livePar)) g = slack (ts s) (some j) g := by
  have hvlt := C.H.hv
  have hgn := SDCtx.nN (s := s) g hg.1
  have hgnn : ¬(g = s.nodes.size ∨ g = s.nodes.size + 1) := fun h => h.elim hgn.1 hgn.2
  have hf := C.funded_old hg
  have hcur : curH (ts s) j = Top.ht (ts s) v := by unfold curH; rw [C.pc]; simp [C.v0]
  have hcur' : curH S' (drainJob j v (nd (ts s) v).livePar) = Top.ht (ts s) v + 1 := by
    change Top.ht S' v + 1 = _
    have hvn := SDCtx.nN (s := s) v C.vl.1
    rw [C.ht v, ite_eq_right (fun h => h.elim hvn.1 hvn.2)]
  -- funded ghosts are not at `v`'s height
  have hfh : funded (ts s) (some j) g → Top.ht (ts s) g ≠ Top.ht (ts s) v := by
    intro hfd e
    obtain ⟨-, -, -, -, h5, h6, -⟩ := C.S.ghost g hg
    have hvy := C.vy
    change Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t1 ∨
      Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t2 at hfd
    rw [e, ← hvy] at hfd
    rcases hfd with h | h
    · rw [← h, show Top.srcOf (ts s) v = NIL from C.of] at h5; exact hg.1.1 h5.symm
    · rw [← h, show Top.srcOf (ts s) v = NIL from C.of] at h6; exact hg.1.1 h6.symm
  have hpc := C.pc
  unfold slack
  simp only
  by_cases hfd : funded (ts s) (some j) g
  · have hfd' : funded S' (some (drainJob j v (nd (ts s) v).livePar)) g := hf.mpr hfd
    have hne := hfh hfd
    rw [ite_eq_left (show Top.anc S' (drainJob j v (nd (ts s) v).livePar).y (Top.ht S' g) = (nd
      S' g).t1 ∨
        Top.anc S' (drainJob j v (nd (ts s) v).livePar).y (Top.ht S' g) = (nd S' g).t2 from hfd'),
      ite_eq_left (show Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t1 ∨
        Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t2 from hfd)]
    rw [hcur, hcur', SDHyps.P (s := s) (v := v) (side := side), C.ht g, ite_eq_right hgnn]
    by_cases hle : Top.ht (ts s) v ≤ Top.ht (ts s) g
    · rw [ite_eq_left (by omega), ite_eq_left hle]; rfl
    · rw [ite_eq_right (by omega), ite_eq_right hle, hpc]; rfl
  · rw [ite_eq_right (show ¬(Top.anc S' (drainJob j v (nd (ts s) v).livePar).y (Top.ht S' g) =
      (nd S' g).t1 ∨
        Top.anc S' (drainJob j v (nd (ts s) v).livePar).y (Top.ht S' g) = (nd S' g).t2) from fun
          h => hfd (hf.mp h)),
      ite_eq_right (show ¬(Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t1 ∨
        Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t2) from hfd)]

theorem slack_v : slack S' (some (drainJob j v (nd (ts s) v).livePar)) v = 0 := by
  have hvlt := C.H.hv
  have hvn := SDCtx.nN (s := s) v C.vl.1
  have hcur' : curH S' (drainJob j v (nd (ts s) v).livePar) = Top.ht (ts s) v + 1 := by
    change Top.ht S' v + 1 = _
    rw [C.ht v, ite_eq_right (fun h => h.elim hvn.1 hvn.2)]
  unfold slack
  simp only
  rw [hcur', C.ht v,
    ite_eq_right (show ¬(v = s.nodes.size ∨ v = s.nodes.size + 1) from fun h => h.elim hvn.1 hvn.2)]
  split
  · rw [ite_eq_right (by omega)]; rfl
  · rfl

/-- **The new nodes weigh between `λ_h` and `τ_h`** (Lemma T0). -/
theorem tw_new_range (w : Nat) (hw : w = s.nodes.size ∨ w = s.nodes.size + 1) :
    lamd s.P (Top.ht (ts s) v) ≤ tw S' cl w ∧ tw S' cl w ≤ taud s.P (Top.ht (ts s) v) := by
  have hvlt := C.H.hv
  obtain ⟨-, htw⟩ := C.tw_new w hw
  rw [htw]
  have hc : (nd S' w).children = if w = s.nodes.size then (nd (ts s) v).children.take (sK (wiC s
    v) v)
      else (nd (ts s) v).children.drop (sK (wiC s v) v) := by
    rcases hw with rfl | rfl
    · rw [C.children, ite_eq_right (show ¬(s.nodes.size = v) by omega), ite_eq_left rfl,
      ite_eq_left rfl]
    · rw [C.children, ite_eq_right (show ¬(s.nodes.size + 1 = v) by omega),
        ite_eq_right (show ¬(s.nodes.size + 1 = s.nodes.size) by omega), ite_eq_left rfl,
        ite_eq_right (show ¬(s.nodes.size + 1 = s.nodes.size) by omega)]
  rw [hc]
  by_cases h1 : Top.ht (ts s) v = 1
  · obtain ⟨-, -, -, a1, a2, a3, a4⟩ := sd_cut1 C.pc C.v0 C.I C.lp h1 C.of C.W
    rw [ite_eq_left h1]; rw [h1]
    split
    · exact ⟨a1, a2⟩
    · exact ⟨a3, a4⟩
  · obtain ⟨-, -, -, -, a1, a2, a3, a4⟩ := sd_cut2 C.pc C.v0 C.I C.lp C.TP (by
      have := C.h1
      omega) C.of C.W
    rw [ite_eq_right h1]
    split
    · exact ⟨a1, a2⟩
    · exact ⟨a3, a4⟩

theorem pend_new {w : Nat} (hw : w = s.nodes.size ∨ w = s.nodes.size + 1) :
    w ∉ pend S' (some (drainJob j v (nd (ts s) v).livePar)) := by
  intro h
  rw [show drainJob j v (nd (ts s) v).livePar = { j with pc := .afterDrain v (nd (ts s)
    v).livePar } from rfl,
    C.pend_mem] at h
  obtain ⟨hl, -, -⟩ := C.up
  have hp := sd_pend C.pc C.v0 C.I C.lp
  rw [hp] at h
  rcases List.mem_cons.mp h.1 with e | e
  · exact h.2 e
  · have := (C.S.upChain_mem _ _ w hl e).1
    have h' : w < s.nodes.size := this.1.2.1
    omega

theorem rng_v_le : (rng (ts s) cl v).length ≤ tw (ts s) cl v := by
  unfold rng tw
  have e : cl.filter (fun c => decide (Top.pp (ts s) c (Top.ht (ts s) v) = v)) =
      (cl.filter (fun c => decide (Top.anc (ts s) c (Top.ht (ts s) v) = v))).filter
        (fun c => decide (Top.pp (ts s) c (Top.ht (ts s) v) = v)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro c hc
    by_cases hp : Top.pp (ts s) c (Top.ht (ts s) v) = v
    · have : Top.anc (ts s) c (Top.ht (ts s) v) = v := by
        rcases C.S.P c hc _ C.h1 (by have := C.hHt; omega) with h | ⟨hg, -⟩
        · rw [← h, hp]
        · rw [hp] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      simp [hp, this]
    · simp [hp]
  rw [e]
  exact (List.filter_sublist).length_le

/-- **The drain timing after a drain starts.** -/
theorem time : Timing S' cl (some (drainJob j v (nd (ts s) v).livePar)) := by
  have Ti := C.Ti
  have hvlt := C.H.hv
  have hNH := C.NH
  have hP' := SDHyps.P (s := s) (v := v) (side := side)
  have hpm : ∀ x, x ∈ pend S' (some (drainJob j v (nd (ts s) v).livePar)) ↔ x ∈ pend (ts s)
    (some j) ∧ x ≠ v :=
    fun x => C.pend_mem
  have hwv : (nd (ts s) v).weight ≤ Wd s.P (Top.ht (ts s) v) := Ti.wA v C.vl C.lp C.of
  have htv := sd_tw C.pc C.v0 C.I C.lp
  have hW := C.W
  refine ⟨fun u hu => ?_, fun u hu hp hs => ?_, fun g hg => ?_, fun g hg => ?_, fun g hg => ?_,
    fun g hg => ?_, fun u hu hH => ?_, fun t ht hs => ?_, fun u hu hH => ?_, fun u hu => ?_⟩
  · -- wts
    rw [C.liveN] at hu
    rcases hu with ⟨hul, huv⟩ | hw | hw
    · have hun := SDCtx.nN (s := s) u hul.1
      rw [C.H.weight, ite_eq_right hun.1, ite_eq_right hun.2, ite_eq_right huv,
        C.tw_old hul.1 huv, ← Ti.wts u hul]
      by_cases hp : u ∈ pend (ts s) (some j)
      · rw [ite_eq_left ((hpm u).mpr ⟨hp, huv⟩), ite_eq_left hp]
      · rw [ite_eq_right (fun h => hp ((hpm u).mp h).1), ite_eq_right hp]
    all_goals
      rw [ite_eq_right (C.pend_new (by omega)), Nat.add_zero]
      exact (C.tw_new _ (by omega)).1.symm
  · -- wA
    rw [C.liveN] at hu
    rw [C.srcOf] at hs
    rcases hu with ⟨hul, huv⟩ | hw | hw
    · have hun := SDCtx.nN (s := s) u hul.1
      have hnn : ¬(u = s.nodes.size ∨ u = s.nodes.size + 1) := fun h => h.elim hun.1 hun.2
      rw [ite_eq_right hnn] at hs
      rw [C.H.weight, ite_eq_right hun.1, ite_eq_right hun.2, ite_eq_right huv, C.ht u,
        ite_eq_right hnn, hP']
      apply Ti.wA u hul _ hs
      by_cases hk : Top.ht (ts s) v ≠ 1 ∧ u ∈ (nd (ts s) v).children
      · have := ((C.S.mem_children C.vl).mp hk.2).2
        rw [par_live (Or.inr hul), ite_eq_right (by have := C.h1; omega)] at this
        rw [this]; exact C.v0
      · rwa [C.livePar_old hul.1 huv (fun h1 h => hk ⟨h1, h⟩)] at hp
    all_goals rw [ite_eq_left (by omega)] at hs; exact absurd hs C.v0
  · -- wB
    rw [C.ghostN] at hg
    rcases hg with hg | hgv
    · have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      have hgn := SDCtx.nN (s := s) g hg.1
      rw [C.H.weight, ite_eq_right hgn.1, ite_eq_right hgn.2, ite_eq_right hgv, C.ht g,
        ite_eq_right (fun h => h.elim hgn.1 hgn.2), hP']
      exact Ti.wB g hg
    · rw [hgv, C.H.weight, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl,
      C.ht v,
        ite_eq_right (show ¬(v = s.nodes.size ∨ v = s.nodes.size + 1) by omega), hP']
      constructor <;> omega
  · -- wF
    rw [C.ghostN] at hg
    rcases hg with hg | hgv
    · have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      have hgn := SDCtx.nN (s := s) g hg.1
      rw [C.H.weight, ite_eq_right hgn.1, ite_eq_right hgn.2, ite_eq_right hgv, C.ew_old hg.1]
      exact Ti.wF g hg
    · rw [hgv, C.H.weight, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl,
      C.ew_v, htv]
      simp
  · -- wC
    rw [C.ghostN] at hg
    rcases hg with hg | hgv
    · have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      have hgn := SDCtx.nN (s := s) g hg.1
      have hw : (nd S' g).weight = (nd (ts s) g).weight := by
        rw [C.H.weight, ite_eq_right hgn.1, ite_eq_right hgn.2, ite_eq_right hgv]
      have hf : fundOf S' cl g = fundOf (ts s) cl g := by unfold fundOf; rw [C.ew_old hg.1, hw]
      rw [C.rng_old hg.1, hf, hw, C.slack_old hg, hP']
      exact Ti.wC g hg
    · rw [hgv]
      have hw : (nd S' v).weight = (nd (ts s) v).weight + 2 := by
        rw [C.H.weight, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      have hf : fundOf S' cl v = 0 := by unfold fundOf; rw [C.ew_v, hw, htv]; simp
      rw [C.rng_old C.vl.1, hf, hw, C.slack_v]
      have := C.rng_v_le
      omega
  · -- wC'
    rw [C.ghostN] at hg
    rcases hg with hg | hgv
    · have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      have hgn := SDCtx.nN (s := s) g hg.1
      have hw : (nd S' g).weight = (nd (ts s) g).weight := by
        rw [C.H.weight, ite_eq_right hgn.1, ite_eq_right hgn.2, ite_eq_right hgv]
      have hf : fundOf S' cl g = fundOf (ts s) cl g := by unfold fundOf; rw [C.ew_old hg.1, hw]
      have := Ti.wC' g hg
      rw [hf, hw, hP']
      by_cases hfd : funded (ts s) (some j) g
      · rw [ite_eq_left ((C.funded_old hg).mpr hfd)]; rw [ite_eq_left hfd] at this; exact this
      · rw [ite_eq_right (fun h => hfd ((C.funded_old hg).mp h))]; rw [ite_eq_right hfd] at this
        exact this
    · rw [hgv]
      have hw : (nd S' v).weight = (nd (ts s) v).weight + 2 := by
        rw [C.H.weight, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      have hf : fundOf S' cl v = 0 := by unfold fundOf; rw [C.ew_v, hw, htv]; simp
      rw [hf]; simp
  · -- wD
    rw [C.liveN] at hu
    rw [hP'] at hH
    rcases hu with ⟨hul, huv⟩ | hw | hw
    · have hun := SDCtx.nN (s := s) u hul.1
      rw [C.ht u, ite_eq_right (fun h => h.elim hun.1 hun.2), C.tw_old hul.1 huv, hP']
      exact Ti.wD u hul hH
    · subst hw; rw [C.ht _, ite_eq_left (Or.inl rfl), hP']; exact (C.tw_new_range _ (Or.inl rfl)).1
    · subst hw; rw [C.ht _, ite_eq_left (Or.inr rfl), hP']; exact (C.tw_new_range _ (Or.inr rfl)).1
  · -- big
    rw [C.liveN] at ht
    rw [C.srcOf] at hs
    rw [hP']
    rcases ht with ⟨htl, -⟩ | hw | hw
    · have htn := SDCtx.nN (s := s) t htl.1
      rw [ite_eq_right (fun h => h.elim htn.1 htn.2)] at hs
      exact Ti.big t htl hs
    all_goals omega
  · -- chain
    rw [C.isN] at hu
    rw [hP'] at hH
    rcases hu with hu | hw | hw
    · have hun := SDCtx.nN (s := s) u hu
      rw [C.ht u, ite_eq_right (fun h => h.elim hun.1 hun.2)]
      exact Ti.chain u hu hH
    all_goals omega
  · -- tw1
    rw [C.liveN] at hu
    rcases hu with ⟨hul, huv⟩ | hw | hw
    · rw [C.tw_old hul.1 huv]; exact Ti.tw1 u hul
    all_goals
      have := (C.tw_new_range u (by omega)).1
      have hl := C.TP.lamK (Top.ht (ts s) v) C.h1
      omega

/-- **The potential of a table that held `v`.** -/
theorem growth_tab {X : Nat} (hT : X ∈ (nd (ts s) v).inTables) :
    growth S' cl X + (if X < v then tw (ts s) cl v - taud s.P (Top.ht (ts s) v) else 0) = growth
      (ts s) cl X ∧
    oldLive S' X + (if v < X then 1 else 0) = oldLive (ts s) X := by
  have hvlt := C.H.hv
  obtain ⟨hX, hXh, hvX⟩ := C.inTab X hT
  have hXn := SDCtx.nN (s := s) X hX
  have hXnn : ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) := fun h => h.elim hXn.1 hXn.2
  have hXv : X ≠ v := fun e => by rw [e] at hXh; omega
  obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hvX
  have hnd : (Top.order (ts s) X).Nodup := (C.S.ordNodup _).sublist (C.S.O1 X hX)
  have hord' : Top.order S' X = P ++ s.nodes.size :: v :: (s.nodes.size + 1) :: Q := by
    rw [C.order, ite_eq_right hXn.1, ite_eq_right hXn.2, ite_eq_left hT, hPQ]
    rw [hPQ] at hnd
    have hP : v ∉ P := fun h => (List.nodup_append.mp hnd).2.2 v h v (by simp) rfl
    rw [replace1_split _ hP]; simp
  rw [hPQ] at hnd
  have hPQv : ∀ e ∈ P ++ Q, e ≠ v ∧ Top.isN (ts s) e ∧ Top.ht (ts s) e = Top.ht (ts s) v := by
    intro e he
    have hvP : v ∉ P := fun h => (List.nodup_append.mp hnd).2.2 v h v (by simp) rfl
    have hvQ : v ∉ Q := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
    have hem : e ∈ Top.order (ts s) X := by
      rw [hPQ]
      rcases List.mem_append.mp he with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hent := C.S.tabEnt X hX e hem
    rw [hXh, Nat.add_sub_cancel] at hent
    obtain ⟨hn, hh⟩ := (C.S.ordMem _ C.h1 (by have := C.hHt; omega) e).mp hent
    refine ⟨fun h => ?_, hn, hh⟩
    subst h
    simp only [List.mem_append] at he
    rcases he with h | h
    · exact hvP h
    · exact hvQ h
  have hl : ∀ e ∈ P ++ Q, (Top.liveN S' e ↔ Top.liveN (ts s) e) ∧ tw S' cl e = tw (ts s) cl e := by
    intro e he
    obtain ⟨hev, hn, -⟩ := hPQv e he
    refine ⟨?_, C.tw_old hn hev⟩
    rw [C.liveN]
    have := SDCtx.nN (s := s) e hn
    constructor
    · rintro (⟨h, -⟩ | h | h)
      · exact h
      · exact absurd h this.1
      · exact absurd h this.2
    · intro h; exact Or.inl ⟨h, hev⟩
  have hNl : Top.liveN S' s.nodes.size := (C.liveN _).mpr (Or.inr (Or.inl rfl))
  have hN1l : Top.liveN S' (s.nodes.size + 1) := (C.liveN _).mpr (Or.inr (Or.inr rfl))
  have hvl' : ¬Top.liveN S' v := fun h => by
    rcases (C.liveN v).mp h with ⟨-, h⟩ | h | h
    · exact h rfl
    · omega
    · omega
  have hXN : X < s.nodes.size := hX.2.1
  have hτN := (C.tw_new_range _ (Or.inl rfl)).2
  have hτN1 := (C.tw_new_range _ (Or.inr rfl)).2
  have hht : Top.ht S' X - 1 = Top.ht (ts s) v := by
    rw [C.ht X, ite_eq_right hXnn, hXh, Nat.add_sub_cancel]
  have hht' : Top.ht (ts s) X - 1 = Top.ht (ts s) v := by rw [hXh, Nat.add_sub_cancel]
  constructor
  · unfold growth
    rw [hord', hPQ, foldr_sum, foldr_sum, hht, hht', SDHyps.P (s := s) (v := v) (side := side),
      show (ts s).P = s.P from rfl]
    have eP : (P.filter fun e => decide (Top.liveN S' e) && decide (X < e)) =
        P.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN
        (ts s) e)) from
        decide_eq_decide.mpr (hl e (by simp [he])).1])
    have eQ : (Q.filter fun e => decide (Top.liveN S' e) && decide (X < e)) =
        Q.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN
        (ts s) e)) from
        decide_eq_decide.mpr (hl e (by simp [he])).1])
    rw [List.filter_append, List.filter_append, eP, List.filter_cons, List.filter_cons,
      List.filter_cons,
      List.filter_cons, eQ]
    simp only [decide_eq_true hNl, decide_eq_true hN1l, decide_eq_false hvl', decide_eq_true C.vl,
      decide_eq_true hXN, decide_eq_true (show X < s.nodes.size + 1 by omega), Bool.true_and,
        Bool.false_and,
      ite_true, Bool.false_eq_true, ite_false]
    have mP : ((P.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw S' cl e - taud s.P (Top.ht (ts s) v)) =
        (P.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw (ts s) cl e - taud s.P (Top.ht (ts s) v) :=
      List.map_congr_left (fun e he => by rw [(hl e (by simp [(List.mem_filter.mp he).1])).2])
    have mQ : ((Q.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw S' cl e - taud s.P (Top.ht (ts s) v)) =
        (Q.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw (ts s) cl e - taud s.P (Top.ht (ts s) v) :=
      List.map_congr_left (fun e he => by rw [(hl e (by simp [(List.mem_filter.mp he).1])).2])
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, mP, mQ]
    by_cases hXv' : X < v
    · simp only [decide_eq_true hXv', ite_true, List.map_cons,
      List.sum_cons]; rw [ite_eq_left hXv']; omega
    · simp only [decide_eq_false hXv', Bool.false_eq_true, ite_false]; rw [ite_eq_right hXv']; omega
  · unfold oldLive
    rw [hord', hPQ]
    have eP : (P.filter fun e => decide (Top.liveN S' e) && decide (e < X)) =
        P.filter fun e => decide (Top.liveN (ts s) e) && decide (e < X) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN
        (ts s) e)) from
        decide_eq_decide.mpr (hl e (by simp [he])).1])
    have eQ : (Q.filter fun e => decide (Top.liveN S' e) && decide (e < X)) =
        Q.filter fun e => decide (Top.liveN (ts s) e) && decide (e < X) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN
        (ts s) e)) from
        decide_eq_decide.mpr (hl e (by simp [he])).1])
    rw [List.filter_append, List.filter_append, eP, List.filter_cons, List.filter_cons,
      List.filter_cons,
      List.filter_cons, eQ]
    simp only [decide_eq_false hvl', decide_eq_true C.vl,
      decide_eq_false (show ¬(s.nodes.size < X) by omega),
      decide_eq_false (show ¬(s.nodes.size + 1 < X) by omega), Bool.and_false, Bool.true_and,
        Bool.false_and,
      Bool.false_eq_true, ite_false]
    by_cases hvX : v < X
    · simp only [decide_eq_true hvX, ite_true, List.length_append,
      List.length_cons]; rw [ite_eq_left hvX]; omega
    · simp only [decide_eq_false hvX, Bool.false_eq_true, ite_false,
      List.length_append]; rw [ite_eq_right hvX]; omega

theorem growth_same {X : Nat} (hX : Top.isN (ts s) X) (h2 : 2 ≤ Top.ht (ts s) X)
    (hT : X ∉ (nd (ts s) v).inTables) :
    growth S' cl X = growth (ts s) cl X ∧ oldLive S' X = oldLive (ts s) X := by
  have hvlt := C.H.hv
  have hXn := SDCtx.nN (s := s) X hX
  have hXnn : ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) := fun h => h.elim hXn.1 hXn.2
  obtain ⟨h1X, hHX⟩ := C.S.htN X hX
  have hord : Top.order S' X = Top.order (ts s) X := by
    rw [C.order, ite_eq_right hXn.1, ite_eq_right hXn.2, ite_eq_right hT]
  have hent : ∀ e ∈ Top.order (ts s) X, Top.isN (ts s) e ∧ Top.ht (ts s) e = Top.ht (ts s) X - 1 :=
    fun e he => (C.S.ordMem _ (by omega) (by omega) e).mp (C.S.tabEnt X hX e he)
  have hvX : v ∉ Top.order (ts s) X := by
    intro h
    have hentv : Ent ord (Top.ht (ts s) v) v := (C.S.ordMem _ C.h1 (C.S.htN v C.vl.1).2 v).mpr
      ⟨C.vl.1, rfl⟩
    have hh : Top.ht (ts s) X = Top.ht (ts s) v + 1 := by have := (hent v h).2; omega
    apply hT
    have : X ∈ tabs (ts s) (Top.ht (ts s) v) v := (C.S.tabsIff _ v X hentv).mpr ⟨hX, hh, h⟩
    unfold tabs at this; rwa [ite_eq_right (by have := C.h1; omega)] at this
  have hl : ∀ e ∈ Top.order (ts s) X, (Top.liveN S' e ↔ Top.liveN (ts s) e) ∧ tw S' cl e = tw
    (ts s) cl e := by
    intro e he
    have hev : e ≠ v := fun h => hvX (h ▸ he)
    have hn := (hent e he).1
    have hen := SDCtx.nN (s := s) e hn
    refine ⟨?_, C.tw_old hn hev⟩
    rw [C.liveN]
    constructor
    · rintro (⟨h, -⟩ | h | h)
      · exact h
      · exact absurd h hen.1
      · exact absurd h hen.2
    · intro h; exact Or.inl ⟨h, hev⟩
  have hht : Top.ht S' X = Top.ht (ts s) X := by rw [C.ht X, ite_eq_right hXnn]
  constructor
  · unfold growth
    rw [hord, hht, SDHyps.P (s := s) (v := v) (side := side), show (ts s).P = s.P from rfl,
      foldr_sum, foldr_sum]
    have ef : ((Top.order (ts s) X).filter fun e => decide (Top.liveN S' e) && decide (X < e)) =
        (Top.order (ts s) X).filter fun e => decide (Top.liveN (ts s) e) && decide (X < e) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN
        (ts s) e)) from
        decide_eq_decide.mpr (hl e he).1])
    rw [ef]
    have em : (((Top.order (ts s) X).filter fun e => decide (Top.liveN (ts s) e) && decide (X <
      e)).map
        fun e => tw S' cl e - taud s.P (Top.ht (ts s) X - 1)) =
        ((Top.order (ts s) X).filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw (ts s) cl e - taud s.P (Top.ht (ts s) X - 1) :=
      List.map_congr_left (fun e he => by rw [(hl e (List.mem_of_mem_filter he)).2])
    rw [em]
  · unfold oldLive
    rw [hord]
    have ef : ((Top.order (ts s) X).filter fun e => decide (Top.liveN S' e) && decide (e < X)) =
        (Top.order (ts s) X).filter fun e => decide (Top.liveN (ts s) e) && decide (e < X) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN
        (ts s) e)) from
        decide_eq_decide.mpr (hl e he).1])
    rw [ef]

theorem new_notTab {w : Nat} (hw : w = s.nodes.size ∨ w = s.nodes.size + 1) : w ∉ (nd (ts s)
  v).inTables :=
  fun h => by have : w < s.nodes.size := (C.inTab w h).1.2.1; omega

/-- **The label room after a drain starts.** -/
theorem room : Room S' cl (drSD dr (nd (ts s) v).inTables s.nodes.size)
    (n0SD n0 s.nodes.size (sLeft (wiC s v) v side).length (sRight (wiC s v) v side).length) := by
  have Ro := C.I.room
  have hvlt := C.H.hv
  have hNH := C.NH
  have hP' := SDHyps.P (s := s) (v := v) (side := side)
  have hnewlive : ∀ w, (w = s.nodes.size ∨ w = s.nodes.size + 1) → ew S' cl w = tw S' cl w := by
    intro w hw
    have hd : (nd S' w).draining = false := by
      rw [C.draining', ite_eq_right (show ¬(w = v) by omega), ite_eq_left hw]
    unfold ew; rw [ite_eq_right (by rw [hd]; simp)]
  refine ⟨fun X hX => ?_, fun X hX => ?_, fun X hX h1 => ?_, fun X hX h2 => ?_⟩
  · -- gaps
    rw [hP']
    rw [C.isN] at hX
    rcases hX with hX | hw | hw
    · have hXn := SDCtx.nN (s := s) X hX
      unfold drSD n0SD
      rw [ite_eq_right hXn.1, ite_eq_right hXn.2]
      by_cases hT : X ∈ (nd (ts s) v).inTables
      · rw [ite_eq_left hT]
        obtain ⟨A, le, Bs, htab, hA, hl⟩ := C.labs_tab hT
        rw [hl, gapB_succ]
        obtain ⟨A', le', Bs', htab', hA', -, -, -, -, hg⟩ := room_up C.I C.TP C.vl.1 hT
          s.nodes.size (s.nodes.size + 1)
        rw [htab] at htab'
        obtain ⟨rfl, rfl, rfl⟩ := split_unique htab' hA hA'
        exact hg
      · rw [ite_eq_right hT, ite_eq_right (fun h => h.elim hXn.1 hXn.2)]
        have : Top.labs S' X = Top.labs (ts s) X := by
          unfold Top.labs; rw [C.H.table, ite_eq_right hXn.1, ite_eq_right hXn.2, ite_eq_right hT]
        rw [this]; exact Ro.gaps X hX
    · subst hw
      unfold drSD n0SD
      rw [ite_eq_right (C.new_notTab (Or.inl rfl)), ite_eq_left (Or.inl rfl), ite_eq_left rfl]
      unfold Top.labs gapB; rw [C.H.table, ite_eq_left rfl, pow_zero, Nat.div_one]
      exact evenTable_gaps s.P.beta _
    · subst hw
      unfold drSD n0SD
      rw [ite_eq_right (C.new_notTab (Or.inr rfl)), ite_eq_left (Or.inr rfl),
        ite_eq_right (by omega), ite_eq_left rfl]
      unfold Top.labs gapB; rw [C.H.table, ite_eq_right (by omega), ite_eq_left rfl, pow_zero,
        Nat.div_one]
      exact evenTable_gaps s.P.beta _
  · -- n0le
    rw [hP']
    rw [C.isN] at hX
    unfold n0SD
    rcases hX with hX | hw | hw
    · have hXn := SDCtx.nN (s := s) X hX
      rw [ite_eq_right hXn.1, ite_eq_right hXn.2, C.ht X,
        ite_eq_right (fun h => h.elim hXn.1 hXn.2)]; exact Ro.n0le X hX
    · subst hw; rw [ite_eq_left rfl, C.ht _, ite_eq_left (Or.inl rfl)]
      exact sc_left C.pc C.v0 C.I C.lp C.TP C.of C.W C.look
    · subst hw; rw [ite_eq_right (by omega), ite_eq_left rfl, C.ht _, ite_eq_left (Or.inr rfl)]
      exact sc_right C.pc C.v0 C.I C.lp C.TP C.of C.W C.look
  · -- pot1
    rw [hP']
    rw [C.isN] at hX
    rcases hX with hX | hw | hw
    · have hXn := SDCtx.nN (s := s) X hX
      have hXnn : ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) := fun h => h.elim hXn.1 hXn.2
      rw [C.ht X, ite_eq_right hXnn] at h1
      have hT : X ∉ (nd (ts s) v).inTables := fun h => by
        have := (C.inTab X h).2.1
        have := C.h1
        omega
      unfold drSD; rw [ite_eq_right hT, ite_eq_right hXnn, C.ew_old hX]
      exact Ro.pot1 X hX h1
    all_goals
      rw [C.ht _, ite_eq_left (by omega)] at h1
      unfold drSD; rw [ite_eq_right (C.new_notTab (by omega)), ite_eq_left (by omega), hnewlive
        _ (by omega), ite_eq_left (by omega)]
      have := (C.tw_new_range X (by omega)).1
      rw [h1] at this; omega
  · -- pot2
    rw [hP']
    rw [C.isN] at hX
    rcases hX with hX | hw | hw
    · have hXn := SDCtx.nN (s := s) X hX
      have hXnn : ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) := fun h => h.elim hXn.1 hXn.2
      have hht : Top.ht S' X = Top.ht (ts s) X := by rw [C.ht X, ite_eq_right hXnn]
      rw [hht] at h2 ⊢
      have hp := Ro.pot2 X hX h2
      rw [show (ts s).P = s.P from rfl] at hp
      unfold drSD n0SD
      rw [ite_eq_right hXn.1, ite_eq_right hXn.2, C.ew_old hX]
      by_cases hT : X ∈ (nd (ts s) v).inTables
      · rw [ite_eq_left hT]
        obtain ⟨hgr, hol⟩ := C.growth_tab hT
        have hXh := (C.inTab X hT).2.1
        have hXv : X ≠ v := fun e => by rw [e] at hXh; omega
        rw [hXh, Nat.add_sub_cancel] at hp ⊢
        have htv := sd_tw C.pc C.v0 C.I C.lp
        have hW := C.W
        have hτ : gamd s.P (Top.ht (ts s) v) ≤ tw (ts s) cl v - taud s.P (Top.ht (ts s) v) := by
          unfold gamd; omega
        rw [Nat.mul_succ]
        rcases Nat.lt_or_gt_of_ne hXv with hlt | hlt
        · rw [ite_eq_left hlt] at hgr; rw [ite_eq_right (show ¬(v < X) by omega), Nat.add_zero]
            at hol
          rw [hol]
          omega
        · rw [ite_eq_right (by omega)] at hgr; rw [ite_eq_left hlt] at hol
          have e : gamd s.P (Top.ht (ts s) v) * oldLive (ts s) X =
              gamd s.P (Top.ht (ts s) v) * oldLive S' X + gamd s.P (Top.ht (ts s) v) := by
                rw [← hol, Nat.mul_succ]
          omega
      · rw [ite_eq_right hT, ite_eq_right hXnn]
        obtain ⟨hgr, hol⟩ := C.growth_same hX h2 hT
        rw [hgr, hol]; exact hp
    all_goals
      have hwn : X = s.nodes.size ∨ X = s.nodes.size + 1 := by omega
      have hht : Top.ht S' X = Top.ht (ts s) v := by rw [C.ht X, ite_eq_left hwn]
      rw [hht] at h2 ⊢
      unfold drSD n0SD
      rw [ite_eq_right (C.new_notTab hwn), ite_eq_left hwn, hnewlive _ hwn, ite_eq_left (by omega)]
      have hgr : growth S' cl X = 0 := by
        unfold growth
        rw [foldr_sum]
        have : ((Top.order S' X).filter fun e => decide (Top.liveN S' e) && decide (X < e)) = []
          := by
          apply List.filter_eq_nil_iff.mpr
          intro e he
          rw [C.order_mem] at he
          have heo : e ∈ Top.order (ts s) v := by
            rcases he with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h1, h2, -⟩
            · exact SDCtx.left_mem (s := s) (v := v) (side := side) h
            · exact SDCtx.right_mem (s := s) (v := v) (side := side) h
            · exact absurd hwn (fun h => h.elim h1 h2)
          have : e < s.nodes.size := ((sp_entry C.pc C.v0 C.I C.lp heo).2 h2).1.2.1
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; intro; omega
        rw [this]; rfl
      have hol : oldLive S' X ≤ (Top.order S' X).length := List.length_filter_le _ _
      have hlen : (Top.order S' X).length =
          if X = s.nodes.size then (sLeft (wiC s v) v side).length else (sRight (wiC s v) v
            side).length := by
        rw [C.order]
        rcases hwn with h | h
        · rw [ite_eq_left h, ite_eq_left h]
        · rw [ite_eq_right (show ¬(X = s.nodes.size) by omega), ite_eq_left h,
          ite_eq_right (show ¬(X = s.nodes.size) by omega)]
      have hge := (C.tw_new_range X hwn).1
      rw [hgr]
      have hm : gamd s.P (Top.ht (ts s) v - 1) * oldLive S' X ≤
          gamd s.P (Top.ht (ts s) v - 1) * (if X = s.nodes.size then (sLeft (wiC s v) v side).length
            else if X = s.nodes.size + 1 then (sRight (wiC s v) v side).length else n0 X) := by
        apply Nat.mul_le_mul_left
        rcases hwn with h | h
        · rw [ite_eq_left h]; rw [ite_eq_left h] at hlen; omega
        · rw [ite_eq_right (show ¬(X = s.nodes.size) by omega), ite_eq_left h]
          rw [ite_eq_right (show ¬(X = s.nodes.size) by omega)] at hlen; omega
      simp only [Nat.mul_zero, Nat.zero_add]
      omega

/-- **The running job after a drain starts.** -/
theorem job : JobOK S' cl (drainJob j v (nd (ts s) v).livePar) := by
  have hvlt := C.H.hv
  have hvn := SDCtx.nN (s := s) v C.vl.1
  have hvnn : ¬(v = s.nodes.size ∨ v = s.nodes.size + 1) := fun h => h.elim hvn.1 hvn.2
  have hht : Top.ht S' v = Top.ht (ts s) v := by rw [C.ht v, ite_eq_right hvnn]
  have hH := C.hH
  refine ⟨(C.I.job j rfl).pos, ?_⟩
  change Top.ghostN S' v ∧
      (Top.anc S' j.y (Top.ht S' v) = (nd S' v).t1 ∨ Top.anc S' j.y (Top.ht S' v) = (nd S' v).t2) ∧
      (nd (ts s) v).livePar = Top.anc S' j.y (Top.ht S' v + 1)
  rw [hht, C.H.t1, C.H.t2, ite_eq_left rfl, ite_eq_left rfl]
  refine ⟨(C.ghostN v).mpr (Or.inr rfl), ?_, ?_⟩
  · rw [C.anc C.y_mem _ (by omega), ite_eq_left ⟨rfl, C.vy.symm⟩]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [C.anc C.y_mem _ (by omega), ite_eq_right (fun h => by omega), anc_succ _ _ C.h1, ← C.vy]

/-- **Table lengths after a drain starts.** -/
theorem len : TabLen S' (drSD dr (nd (ts s) v).inTables s.nodes.size)
    (n0SD n0 s.nodes.size (sLeft (wiC s v) v side).length (sRight (wiC s v) v side).length) := by
  have hvlt := C.H.hv
  have hTP' : TopParams (ts (sdS (wiC s v) v side)).P := by
    rw [SDHyps.P (s := s) (v := v) (side := side)]; exact C.TP
  have hcap' : cl.length + 2 ≤ Wd (ts (sdS (wiC s v) v side)).P ((ts (sdS (wiC s v) v side)).P.H
    - 1) := by
    rw [SDHyps.P (s := s) (v := v) (side := side)]; exact C.I.cap
  have hvT : v ∉ (nd (ts s) v).inTables := fun h => by have := (C.inTab v h).2.1; omega
  have htab := C.TP.tab (Top.ht (ts s) v) C.h1
  intro X
  obtain ⟨a, b, c⟩ := C.I.len X
  unfold drSD n0SD
  by_cases hT : X ∈ (nd (ts s) v).inTables
  · have hXn := SDCtx.nN (s := s) X (C.inTab X hT).1
    rw [ite_eq_left hT, ite_eq_right hXn.1, ite_eq_right hXn.2]
    have hXN : Top.isN S' X := (C.isN X).mpr (Or.inl (C.inTab X hT).1)
    have hb := C.room.len_le C.shape C.time hTP' hcap' hXN
    unfold drSD n0SD at hb; rw [ite_eq_left hT, ite_eq_right hXn.1, ite_eq_right hXn.2] at hb
    refine ⟨?_, ?_, hb⟩
    · rw [C.order, ite_eq_right hXn.1, ite_eq_right hXn.2, ite_eq_left hT]
      have := length_replace1_le (Top.order (ts s) X) v s.nodes.size v (s.nodes.size + 1)
      omega
    · rw [C.H.sides,
      ite_eq_right (show ¬X = v from fun e => hvT (Eq.mp (congrArg (· ∈ (nd (ts s) v).inTables)
        e) hT)),
        ite_eq_right (show ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) from fun h => h.elim hXn.1
          hXn.2), ite_eq_left hT]
      have := OrderMaintenance.Proof.Top.length_sideAround_le (nd (ts s) X) v s.nodes.size
        (s.nodes.size + 1)
      omega
  · rw [ite_eq_right hT]
    by_cases hN : X = s.nodes.size
    · subst hN
      rw [ite_eq_left (Or.inl rfl), ite_eq_left rfl]
      have hl := sc_left C.pc C.v0 C.I C.lp C.TP C.of C.W C.look
      refine ⟨?_, ?_, by omega⟩
      · rw [C.order, ite_eq_left rfl]; omega
      · rw [C.H.sides, ite_eq_right (by omega), ite_eq_left (Or.inl rfl)]; simp
    by_cases hN1 : X = s.nodes.size + 1
    · subst hN1
      rw [ite_eq_left (Or.inr rfl), ite_eq_right (by omega), ite_eq_left rfl]
      have hl := sc_right C.pc C.v0 C.I C.lp C.TP C.of C.W C.look
      refine ⟨?_, ?_, by omega⟩
      · rw [C.order, ite_eq_right (by omega), ite_eq_left rfl]; omega
      · rw [C.H.sides, ite_eq_right (by omega), ite_eq_left (Or.inr rfl)]; simp
    rw [ite_eq_right (show ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) from fun h => h.elim hN
      hN1), ite_eq_right hN,
      ite_eq_right hN1]
    refine ⟨?_, ?_, c⟩
    · rw [C.order, ite_eq_right hN, ite_eq_right hN1, ite_eq_right hT]; exact a
    · rw [C.H.sides,
      ite_eq_right (show ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) from fun h => h.elim hN hN1),
        ite_eq_right hT]
      by_cases hv : X = v
      · rw [ite_eq_left hv]; subst hv
        have := sp_side_len C.pc C.v0 C.I C.lp C.TP C.of C.W C.hside
        omega
      · rw [ite_eq_right hv]; exact b

/-- **The invariant after a drain starts.** -/
theorem inv : InvJ S' cl (ordSD ord (Top.ht (ts s) v) v s.nodes.size) (drSD dr (nd (ts s)
  v).inTables s.nodes.size)
    (n0SD n0 s.nodes.size (sLeft (wiC s v) v side).length (sRight (wiC s v) v side).length)
    (some (drainJob j v (nd (ts s) v).livePar)) :=
  ⟨C.shape, C.time, C.room, (fun j' hj => by cases hj; exact C.job), (by
    rw [SDHyps.P (s := s) (v := v) (side := side)]
    exact C.I.cap), C.len⟩

end SDCtx

end OrderMaintenance.Proof.Top
