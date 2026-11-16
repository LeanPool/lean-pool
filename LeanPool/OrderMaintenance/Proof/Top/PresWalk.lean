/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.PresCopy


/-!
# M5: walk steps that start no drain

At node `v` the walk adds 2 to the stored weight. If `v` is a target of a running drain, the job
then funds that drain with up to `s` sweep steps (`fundLoop`), else it moves up.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- The order invariant reads neither stored weights nor the running job. -/
theorem Shape.of_frame {s s' : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord)
    (T : SameTree s s') (hpath : s'.path = s.path) (htag : s'.tag = s.tag)
    (hfirst : ∀ u, (nd s' u).first = (nd s u).first) (hlast : ∀ u, (nd s' u).last = (nd s u).last) :
    Shape s' cl ord := by
  have hP := T.P
  have hpp : ∀ c j, pp s' c j = pp s c j := fun c j => by unfold pp pth; rw [hpath]
  have hrng : ∀ u, rng s' cl u = rng s cl u := fun u => by unfold rng; simp only [T.ht, hpp]
  have hdig : ∀ c j, digit s' c j = digit s c j := fun c j => by unfold digit; rw [hpp, hpp, T.lab?]
  have htagF : ∀ c, tagF s' c = tagF s c := fun c => by
    unfold tagF; rw [hP]; exact tagUp_congr (by rw [hP]) _ (fun i _ _ => hdig c i)
  refine { H3 := by rw [hP]; exact S.H3, ord0 := S.ord0, ordNodup := S.ordNodup, ordMem := ?_, ordHigh := ?_, htN := ?_, root := ?_, pathEnt := ?_, W3 := ?_, O2 := ?_, O1 := ?_, labsOk := ?_, up := ?_, lp := ?_, kids := ?_, OT := ?_, ghost := ?_, src := ?_, tabEnt := ?_, tabsIff := ?_, tabsNodup := ?_, Q := ?_, W1 := ?_, side := ?_, pathSize := ?_, P := ?_, Sr := ?_, ends := ?_, tags := ?_ }
  · intro h h1 h2 u; rw [hP] at h2; rw [T.isN, T.ht]; exact S.ordMem h h1 h2 u
  · intro h hh; rw [hP] at hh; exact S.ordHigh h hh
  · intro u hu; rw [T.isN] at hu; rw [T.ht, hP]; exact S.htN u hu
  · rw [hP, T.liveN, T.livePar]; exact S.root
  · intro c hc j hj; rw [hP] at hj; rw [hpp]; exact S.pathEnt c hc j hj
  · intro c hc j hj1 hj; rw [hP] at hj; rw [hpp, hpp, T.order]; exact S.W3 c hc j hj1 hj
  · intro j hj c d hcd; rw [hP] at hj; rw [hpp, hpp]; exact S.O2 j hj c d hcd
  · intro X hX; rw [T.isN] at hX; rw [T.order, T.ht]; exact S.O1 X hX
  · intro X hX; rw [T.isN] at hX; rw [T.labs, hP]; exact S.labsOk X hX
  · intro u hu hh; rw [T.liveN] at hu; rw [T.ht, hP] at hh
    simp only [T.liveN, T.livePar, T.ht, T.children]; exact S.up u hu hh
  · intro c hc; simp only [T.lpr, T.liveN, T.ht, T.children]; exact S.lp c hc
  · intro u hu; rw [T.liveN] at hu; simp only [T.children, T.ht, T.par, T.liveN]; exact S.kids u hu
  · intro h h1 h2 u u' e e' hu hu' hb he he' hpe hpe'
    rw [hP] at h2; rw [T.liveN] at hu hu'; rw [T.par] at hpe hpe'
    exact S.OT h h1 h2 u u' e e' hu hu' hb he he' hpe hpe'
  · intro u hu; rw [T.ghostN] at hu
    simp only [T.t1, T.t2, T.liveN, T.ht, T.srcOf, T.livePar, T.children, hP]; exact S.ghost u hu
  · intro t ht' hs; rw [T.liveN] at ht'; rw [T.srcOf] at hs ⊢
    simp only [T.ghostN, T.t1, T.t2]; exact S.src t ht' hs
  · intro X hX e he; rw [T.isN] at hX; rw [T.order] at he; rw [T.ht]; exact S.tabEnt X hX e he
  · intro h e X he; rw [T.tabs, T.isN, T.ht, T.order]; exact S.tabsIff h e X he
  · intro h e he; rw [T.tabs]; exact S.tabsNodup h e he
  · intro h e X he hX; rw [T.tabs] at hX; rw [T.par, T.srcOf]; exact S.Q h e X he hX
  · intro u hu X hX; rw [T.ghostN] at hu; rw [T.ht, T.tabs] at hX
    rw [T.order, T.t1, T.t2]; exact S.W1 u hu X hX
  · intro u hu e he; rw [T.ghostN] at hu; rw [T.order] at he
    rw [T.side, T.ht, T.par, T.t1]; exact S.side u hu e he
  · intro c hc; rw [hpath, hP]; exact S.pathSize c hc
  · intro c hc j hj1 hj; rw [hP] at hj
    rw [hpp, T.anc, T.ghostN, T.t1, T.t2]; exact S.P c hc j hj1 hj
  · intro c hc j hj1 hj hg; rw [hP] at hj; rw [hpp, T.ghostN] at hg
    rw [hpp, T.order, T.anc]; exact S.Sr c hc j hj1 hj hg
  · intro u hu; rw [T.isN] at hu; rw [hfirst, hlast, hrng]; exact S.ends u hu
  · intro c hc; rw [htag, htagF]; exact S.tags c hc

/-! ### The walk's chain -/

theorem upChain_nil (s : TS) : ∀ f, upChain s f NIL = []
  | 0 => rfl
  | _ + 1 => by simp [upChain]

/-- Enough fuel: the chain reaches the root. -/
theorem Shape.upChain_succ {s : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord) :
    ∀ f u, liveN s u → s.P.H + 1 - ht s u ≤ f → upChain s (f + 1) u = upChain s f u
  | 0, u, hu, hf => by have := S.htN u hu.1; omega
  | f + 1, u, hu, hf => by
    have h1 : upChain s (f + 1 + 1) u = u :: upChain s (f + 1) (nd s u).livePar := by
      simp [upChain, hu.1.1]
    have h2 : upChain s (f + 1) u = u :: upChain s f (nd s u).livePar := by
      simp [upChain, hu.1.1]
    rw [h1, h2]
    congr 1
    by_cases hH : ht s u < s.P.H
    · obtain ⟨hl, hh, -⟩ := S.up u hu hH
      exact S.upChain_succ f _ hl (by omega)
    · have hroot : (nd s u).livePar = NIL := by
        have := S.htN u hu.1
        have hm := (S.ordMem s.P.H (by have := S.H3; omega) le_rfl u).mpr ⟨hu.1, by omega⟩
        rw [S.root.1] at hm; simp at hm; rw [hm]; exact S.root.2.2
      rw [hroot, upChain_nil, upChain_nil]

/-! ### Adding 2 to a stored weight -/

/-- The walk's weight update at `v`. -/
def wiC (s : Core) (v : Nat) : Core :=
  { s with nodes := s.nodes.modify v fun n => { n with weight := n.weight + 2 } }

theorem wiC_sameTree (s : Core) (v : Nat) : SameTree (ts s) (ts (wiC s v)) := by
  refine ⟨rfl, by simp [wiC, ts], rfl, rfl, fun u => ?_⟩
  show (s.nodes.modify v fun n => { n with weight := n.weight + 2 }).getX u = { s.nodes.getX u with first := ((s.nodes.modify v fun n => { n with weight := n.weight + 2 }).getX u).first, last := ((s.nodes.modify v fun n => { n with weight := n.weight + 2 }).getX u).last, weight := ((s.nodes.modify v fun n => { n with weight := n.weight + 2 }).getX u).weight }
  rw [Array.getX_modify]; split <;> rfl

theorem wiC_weight (s : Core) (v u : Nat) (hv : v < s.nodes.size) :
    (nd (ts (wiC s v)) u).weight = if u = v then (nd (ts s) u).weight + 2 else (nd (ts s) u).weight := by
  show ((s.nodes.modify v _).getX u).weight = _
  rw [Array.getX_modify]
  by_cases h : u = v
  · subst h; simp [hv]; rfl
  · simp [h, Ne.symm h]; rfl

theorem wiC_first (s : Core) (v u : Nat) : (nd (ts (wiC s v)) u).first = (nd (ts s) u).first := by
  show ((s.nodes.modify v _).getX u).first = _
  rw [Array.getX_modify]; split <;> rfl

theorem wiC_last (s : Core) (v u : Nat) : (nd (ts (wiC s v)) u).last = (nd (ts s) u).last := by
  show ((s.nodes.modify v _).getX u).last = _
  rw [Array.getX_modify]; split <;> rfl

/-- The job after the walk visits `v` and starts no drain. -/
def walkNext (s : TS) (j : Job) (v : Nat) : Job :=
  if srcOf s v = NIL then { j with pc := .walk (some (nd s v).livePar) }
  else { j with pc := .fund v (nd s v).livePar (srcOf s v) 0 }

/-- **The weight update keeps the invariant**, when `v` does not start a drain. -/
theorem inv_winc {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {v : Nat} (hpc : j.pc = .walk (some v)) (hv0 : v ≠ NIL)
    (hI : InvJ (ts s) cl ord dr n0 (some j))
    (hno : ¬ ((nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
      (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2)) :
    InvJ (ts (wiC s v)) cl ord dr n0 (some (walkNext (ts s) j v)) := by
  have S := hI.shape
  obtain ⟨hpos, hat⟩ := hI.job j rfl
  simp only [JobAt, hpc] at hat
  obtain ⟨hvl, hva⟩ := hat.resolve_left hv0
  have T := wiC_sameTree s v
  have hP : (ts (wiC s v)).P = (ts s).P := rfl
  have SH := S.of_frame T rfl rfl (wiC_first s v) (wiC_last s v)
  obtain ⟨hv1, hvH⟩ := S.htN v hvl.1
  have hW := fun u => wiC_weight s v u hvl.1.2.1
  set up := (nd (ts s) v).livePar with hup
  -- the walk goes on from the live parent
  have hupl : up = NIL ∨ (liveN (ts s) up ∧ ht (ts s) up = ht (ts s) v + 1) := by
    by_cases hH : ht (ts s) v < (ts s).P.H
    · obtain ⟨h1, h2, -⟩ := S.up v hvl hH; exact Or.inr ⟨h1, h2⟩
    · left
      have hm := (S.ordMem (ts s).P.H (by have := S.H3; omega) le_rfl v).mpr ⟨hvl.1, by omega⟩
      rw [S.root.1] at hm; simp at hm; rw [hup, hm]; exact S.root.2.2
  have hupa : up = anc (ts s) j.y (ht (ts s) v + 1) := by
    rw [anc_succ j.y _ hv1, ← hva]
  -- the lagging nodes: `v` leaves them
  have hpold : pend (ts s) (some j) = v :: upChain (ts s) ((ts s).P.H + 1) up := by
    simp only [pend, wStart, hpc]
    have : upChain (ts s) ((ts s).P.H + 1) v = v :: upChain (ts s) (ts s).P.H up := by
      simp [upChain, hv0, hup]
    rw [this]
    rcases hupl with h | ⟨h1, h2⟩
    · rw [h, upChain_nil, upChain_nil]
    · rw [S.upChain_succ (ts s).P.H up h1 (by rw [h2]; omega)]
  have hpnew : pend (ts (wiC s v)) (some (walkNext (ts s) j v)) = upChain (ts s) ((ts s).P.H + 1) up := by
    simp only [pend, walkNext]
    split <;> (simp only [wStart]; rw [T.upChain]; rfl)
  have hvnot : v ∉ upChain (ts s) ((ts s).P.H + 1) up := by
    intro hm
    rcases hupl with h | ⟨h1, h2⟩
    · rw [h, upChain_nil] at hm; simp at hm
    · have := (S.upChain_mem _ _ v h1 hm).2; omega
  -- a ghost funded at the height of `v` is the drain `v` is a target of
  have hfv : ∀ u, ghostN (ts s) u → ht (ts s) u = ht (ts s) v →
      (anc (ts s) j.y (ht (ts s) u) = (nd (ts s) u).t1 ∨ anc (ts s) j.y (ht (ts s) u) = (nd (ts s) u).t2) →
      srcOf (ts s) v = u := by
    intro u hu hh hf
    rw [hh, ← hva] at hf
    obtain ⟨-, -, -, -, h5, h6, -⟩ := S.ghost u hu
    rcases hf with e | e <;> rw [e] <;> assumption
  have Ti := hI.time
  have hW' : ∀ u, u ≠ v → (nd (ts (wiC s v)) u).weight = (nd (ts s) u).weight := fun u hu => by
    rw [hW u, ite_eq_right hu]
  refine ⟨SH, ?_, ?_, ?_, by rw [hP]; exact hI.cap,
    hI.len.congr fun X => ⟨(wiC_sameTree s v).order X, (wiC_sameTree s v).side X⟩⟩
  · refine ⟨fun u hu => ?_, fun u hu hp hs => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_,
      fun u hu => ?_, fun u hu hu' => ?_, fun u hu hs => ?_, ?_, ?_⟩
    · rw [T.liveN] at hu
      rw [hpnew, T.tw]
      have := Ti.wts u hu
      rw [hpold] at this
      by_cases huv : u = v
      · subst huv; rw [hW, ite_eq_left rfl, ite_eq_right hvnot]; simp at this; omega
      · rw [hW' u huv]; simp only [List.mem_cons, huv, false_or] at this; exact this
    · rw [T.liveN] at hu; rw [T.livePar] at hp; rw [T.srcOf] at hs; rw [T.ht, hP]
      by_cases huv : u = v
      · subst huv
        rw [hW, ite_eq_left rfl]
        show (nd (ts s) u).weight + 2 ≤ Wd s.P (ht (ts s) u)
        by_contra hc
        exact hno ⟨hp, hu.2, hs, by omega⟩
      · rw [hW' u huv]; exact Ti.wA u hu hp hs
    · rw [T.ghostN] at hu
      have huv : u ≠ v := fun e => by rw [e] at hu; exact absurd hu.2 (by rw [hvl.2]; simp)
      rw [hW' u huv, T.ht, hP]; exact Ti.wB u hu
    · rw [T.ghostN] at hu
      have huv : u ≠ v := fun e => by rw [e] at hu; exact absurd hu.2 (by rw [hvl.2]; simp)
      rw [hW' u huv, T.ew]; exact Ti.wF u hu
    · rw [T.ghostN] at hu
      have huv : u ≠ v := fun e => by rw [e] at hu; exact absurd hu.2 (by rw [hvl.2]; simp)
      rw [T.fundOf cl u (hW' u huv), hW' u huv, hP]
      unfold rng; simp only [T.ht]
      have hpp : ∀ c, pp (ts (wiC s v)) c (ht (ts s) u) = pp (ts s) c (ht (ts s) u) := fun c => rfl
      simp only [hpp]
      have hold := Ti.wC u hu
      unfold rng at hold
      refine le_trans hold (Nat.add_le_add_left (le_of_eq ?_) _)
      -- the sweeps owed do not change
      have hy : (walkNext (ts s) j v).y = j.y := by unfold walkNext; split <;> rfl
      obtain ⟨hu1, huH⟩ := S.htN u hu.1
      obtain ⟨-, -, -, -, -, -, -, -, -, hulH, -⟩ := S.ghost u hu
      simp only [slack]
      rw [hy, T.anc, T.ht, T.t1, T.t2, T.P]
      by_cases hF : anc (ts s) j.y (ht (ts s) u) = (nd (ts s) u).t1 ∨
          anc (ts s) j.y (ht (ts s) u) = (nd (ts s) u).t2
      · rw [ite_eq_left hF, ite_eq_left hF]
        have hc : curH (ts s) j = ht (ts s) v := by simp [curH, hpc, hv0]
        rw [hc]
        simp only [hpc]
        by_cases hsv : srcOf (ts s) v = NIL
        · simp only [walkNext, ite_eq_left hsv]
          have hc' : curH (ts (wiC s v)) { j with pc := .walk (some up) } =
              if up = NIL then (ts s).P.H + 1 else ht (ts s) up := by
            simp [curH, T.ht, hP]
          rw [hc']
          by_cases hhu : ht (ts s) u = ht (ts s) v
          · exact absurd (hfv u hu hhu hF) (by rw [hsv]; exact Ne.symm hu.1.1)
          · have hupv : (if up = NIL then (ts s).P.H + 1 else ht (ts s) up) ≤ ht (ts s) u ↔
                ht (ts s) v ≤ ht (ts s) u := by
              rcases hupl with h | ⟨h1, h2⟩
              · rw [ite_eq_left h]
                have hvr : ht (ts s) v = (ts s).P.H := by
                  by_contra hc
                  have := (S.up v hvl (by omega)).1
                  rw [← hup, h] at this; exact this.1.1 rfl
                omega
              · rw [ite_eq_right (fun e => h1.1.1 e), h2]; omega
            by_cases hle : ht (ts s) v ≤ ht (ts s) u
            · rw [ite_eq_left hle, ite_eq_left (hupv.mpr hle)]
            · rw [ite_eq_right hle, ite_eq_right (fun h => hle (hupv.mp h))]
        · simp only [walkNext, ite_eq_right hsv]
          have hc' : curH (ts (wiC s v)) { j with pc := .fund v up (srcOf (ts s) v) 0 } =
              ht (ts s) v + 1 := by simp [curH, T.ht]
          rw [hc']
          obtain ⟨hsg, hst⟩ := S.src v hvl hsv
          obtain ⟨-, -, hh1, hh2, -⟩ := S.ghost _ hsg
          have hsh : ht (ts s) (srcOf (ts s) v) = ht (ts s) v := by
            rcases hst with e | e
            · rw [← hh1, ← e]
            · rw [← hh2, ← e]
          by_cases hhu : ht (ts s) u = ht (ts s) v
          · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
            simp only [ite_eq_left (hfv u hu hhu hF), Nat.sub_zero]
          · by_cases hle : ht (ts s) v ≤ ht (ts s) u
            · rw [ite_eq_left hle, ite_eq_left (by omega)]
            · rw [ite_eq_right hle, ite_eq_right (by omega)]
              rw [ite_eq_right (fun he => hhu (by rw [← he, hsh]))]
      · rw [ite_eq_right hF, ite_eq_right hF]
    · rw [T.ghostN] at hu
      have huv : u ≠ v := fun e => by rw [e] at hu; exact absurd hu.2 (by rw [hvl.2]; simp)
      rw [T.fundOf cl u (hW' u huv), hW' u huv]
      have := Ti.wC' u hu
      have hfe : funded (ts (wiC s v)) (some (walkNext (ts s) j v)) u ↔ funded (ts s) (some j) u := by
        have hy : (walkNext (ts s) j v).y = j.y := by unfold walkNext; split <;> rfl
        simp only [funded]; rw [hy, T.anc, T.ht, T.t1, T.t2]
      by_cases hf : funded (ts s) (some j) u
      · rw [ite_eq_left (hfe.mpr hf)]; rw [ite_eq_left hf] at this; exact this
      · rw [ite_eq_right (fun h => hf (hfe.mp h))]; rw [ite_eq_right hf] at this; exact this
    · rw [T.liveN] at hu; rw [hP] at hu'; rw [T.tw, T.ht, hP]; exact Ti.wD u hu hu'
    · rw [T.liveN] at hu; rw [T.srcOf] at hs; rw [hP]; exact Ti.big u hu hs
    · intro u hu hH; rw [T.isN] at hu; rw [hP] at hH; rw [T.ht]; exact Ti.chain u hu hH
    · intro u hu; rw [T.liveN] at hu; rw [T.tw]; exact Ti.tw1 u hu
  · have Ro := hI.room
    refine ⟨fun X hX => ?_, fun X hX => ?_, fun X hX h1' => ?_, fun X hX h2' => ?_⟩
    · rw [T.isN] at hX; rw [T.labs, hP]; exact Ro.gaps X hX
    · rw [T.isN] at hX; rw [T.ht, hP]; exact Ro.n0le X hX
    · rw [T.isN] at hX; rw [T.ht] at h1'; rw [T.ew, hP]; exact Ro.pot1 X hX h1'
    · rw [T.isN] at hX; rw [T.ht] at h2'; rw [T.ew, T.growth, T.oldLive, T.ht, hP]
      exact Ro.pot2 X hX h2'
  · intro j' hj'
    cases hj'
    have hxyz : (walkNext (ts s) j v).x = j.x ∧ (walkNext (ts s) j v).y = j.y ∧
        (walkNext (ts s) j v).z = j.z := by unfold walkNext; split <;> exact ⟨rfl, rfl, rfl⟩
    refine ⟨by rw [hxyz.1, hxyz.2.1, hxyz.2.2]; exact hpos, ?_⟩
    unfold walkNext
    split
    · next hsv =>
      simp only [JobAt]
      rcases hupl with h | ⟨h1, h2⟩
      · left; exact h
      · right; rw [T.liveN, T.ht, T.anc, h2]; exact ⟨h1, hupa⟩
    · next hsv =>
      simp only [JobAt]
      have hsrc := S.src v hvl hsv
      rw [T.liveN, T.ht, T.anc, T.anc, T.ghostN, T.srcOf]
      exact ⟨hvl, hva, hupa, hsrc.1, rfl, Nat.zero_le _⟩

end OrderMaintenance.Proof.Top
