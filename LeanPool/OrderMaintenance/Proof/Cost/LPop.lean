/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.LMove


/-!
# Lemma C3 at the reservation pop

Popping chunk `x` starts its split: two empty chunks `y = |C|`, `z = |C| + 1` are allocated as its
siblings, and `x` turns from quiet to splitting. The ghost state of the new chunks starts at 0, and
`s₀ x` becomes the size of `x`.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Fields read from the groups only -/

section GsFrame

variable {s s' : Core} (h : s'.Gs = s.Gs)
include h

theorem liveG_of_Gs (g : Nat) : LiveG s' g ↔ LiveG s g := by simp only [LiveG, gA, h]

theorem GrpsC_of_Gs (c : Nat) : GrpsC s' c = GrpsC s c := by
  ext g; simp only [mem_GrpsC, LiveG, gA, gC, h]

theorem units_of_Gs (c : Nat) : units s' c = units s c :=
  units_congr fun g => by unfold UnitG; simp only [LiveG, gA, gC, gSt, h]

theorem pending_of_Gs (lg : LGh) (c : Nat) : pending s' lg c = pending s lg c := by
  unfold pending; rw [GrpsC_of_Gs h]; simp only [gSt, h]

theorem charge_of_Gs (hP : s'.P = s.P) (lg : LGh) (c : Nat) : charge s' lg c = charge s lg c := by
  unfold charge; rw [GrpsC_of_Gs h]; simp only [gSt, gLl, gRr, gSz, famT, h, hP]

end GsFrame

/-! ### The pop -/

/-- What starting the split of `x` changes for the label invariant. -/
structure ResSpec' (s s' : Core) (x : Nat) : Prop where
  Gs : s'.Gs = s.Gs
  P : s'.P = s.P
  Csize : s'.C.size = s.C.size + 2
  old : ∀ c, c < s.C.size → c ≠ x →
    cSz s' c = cSz s c ∧ cLs s' c = cLs s c ∧ cSt s' c = cSt s c ∧ cSrc s' c = cSrc s c ∧
      cLl s' c = cLl s c ∧ cRr s' c = cRr s c
  xs : cSz s' x = cSz s x ∧ cLs s' x = cLs s x ∧ cSt s' x = .splitting ∧
    cLl s' x = s.C.size ∧ cRr s' x = s.C.size + 1
  new : ∀ c, c = s.C.size ∨ c = s.C.size + 1 →
    cSz s' c = 0 ∧ cLs s' c = NIL ∧ cSt s' c = .overflow ∧ cSrc s' c = x

/-- … and the chunk list's links. -/
structure ResSpec (s s' : Core) (x : Nat) : Prop extends ResSpec' s s' x where
  ylink : cN s' s.C.size = x
  xlink : cN s' x = s.C.size + 1
  next : ∀ c, c < s.C.size → c ≠ x → c ≠ cP s x → cN s' c = cN s c

/-- Fresh ghost counters for the chunks `y` and `z`. -/
def LGh.fresh (lg : LGh) (y z : Nat) : LGh :=
  let f := fun (h : Nat → Nat) (c : Nat) => if c = y ∨ c = z then 0 else h c
  { child := lg.child, hv := f lg.hv, cs := f lg.cs, rs := f lg.rs, ins := f lg.ins, pb := f lg.pb,
    pf := f lg.pf, arB := f lg.arB, arF := f lg.arF, e0 := lg.e0 }

/-- Reserving two chunks adds exactly their two fresh indices to the live chunks. -/
theorem ResSpec.liveC {s s' : Core} {x : Nat} (R : ResSpec s s' x) (hxL : LiveC s x) :
    ∀ c, LiveC s' c ↔ LiveC s c ∨ c = s.C.size ∨ c = s.C.size + 1 := by
  intro c; simp only [LiveC, R.Csize]; constructor
  · rintro ⟨h1, h2⟩
    by_cases h3 : c < s.C.size
    · exact Or.inl ⟨h1, h3⟩
    · right; have : c = s.C.size ∨ c = s.C.size + 1 := by omega
      exact this
  · rintro (⟨h1, h2⟩ | h | h)
    · exact ⟨h1, by omega⟩
    · subst h; exact ⟨hxL.1.trans (Nat.le_of_lt hxL.2), by omega⟩
    · subst h; exact ⟨by omega, by omega⟩

/-- A splitting family avoids every quiet chunk and has allocated siblings. -/
theorem CInvE.family_avoids_quiet {s : Core} {L : List Nat} {δ δu s₀ : Nat → Nat} {ex x : Nat}
    (hC : CInvE s L δ δu s₀ ex) (hxq : cSt s x = .quiet) :
    ∀ x', LiveC s x' → cSt s x' = .splitting →
      x' ≠ x ∧ cLl s x' ≠ x ∧ cRr s x' ≠ x ∧ cLl s x' < s.C.size ∧ cRr s x' < s.C.size := by
  intro x' hx' hs'
  have F := hC.cfam x' hx' hs'
  refine ⟨?_, ?_, ?_, F.lLive.2, F.rLive.2⟩
  · rintro rfl; rw [hxq] at hs'; cases hs'
  · intro e; have := F.lSt; rw [e, hxq] at this; cases this
  · intro e; have := F.rSt; rw [e, hxq] at this; cases this

/-- **Lemma C3 at the reservation pop.** -/
theorem linv_pop {s s' : Core} {A : Abs} {lg : LGh} {s₀ : Nat → Nat} {x : Nat}
    (R : ResSpec s s' x) (hC : CInv s A.elist (fun _ => 0) (fun _ => 0) s₀)
    (hL : LInv s lg s₀ (fun _ => 0) (fun _ => 0)) (hxL : LiveC s x) (hxq : cSt s x = .quiet)
    (hun : units s x ≤ unitsOf s.P (cSz s x)) :
    LInv s' (lg.fresh s.C.size (s.C.size + 1)) (Function.update s₀ x (cSz s x))
      (fun _ => 0) (fun _ => 0) := by
  have hnew : ∀ c, c = s.C.size ∨ c = s.C.size + 1 → ¬ c < s.C.size := by
    rintro c (rfl | rfl) <;> omega
  have hLv := liveG_of_Gs R.Gs
  have hg : ∀ g, s'.Gs.getX g = s.Gs.getX g := fun g => by rw [R.Gs]
  have hcg : ∀ g, LiveG s g → gC s g < s.C.size := fun g hg => (hC.gchk g hg).1.2
  have hcgx : ∀ g, LiveG s g → ¬ (gC s g = s.C.size ∨ gC s g = s.C.size + 1) := by
    intro g hg' h; exact hnew _ h (hcg g hg')
  -- an old chunk's fields
  have hold : ∀ c, c < s.C.size → (c = s.C.size ∨ c = s.C.size + 1) = False := by
    intro c hc; apply propext; constructor
    · intro h; exact hnew c h hc
    · intro h; exact h.elim
  have hLC := R.liveC hxL
  have hfamOld := hC.family_avoids_quiet hxq
  have hfamC : ∀ x', LiveC s x' → cSt s x' = .splitting → famC s' x' = famC s x' := by
    intro x' hx' hs'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hfamOld x' hx' hs'
    have o1 := R.old _ h4 h2
    have o2 := R.old _ hx'.2 h1
    have o3 := R.old _ h5 h3
    unfold famC; rw [o2.2.2.2.2.1, o2.2.2.2.2.2, o1.1, o2.1, o3.1]
  have hgrE : ∀ c, c = s.C.size ∨ c = s.C.size + 1 → GrpsC s' c = ∅ := by
    intro c hc
    rw [GrpsC_of_Gs R.Gs]
    ext g; simp only [mem_GrpsC, Finset.notMem_empty, iff_false, not_and]
    intro hg' e; exact hcgx g hg' (e ▸ hc)
  have hfr : ∀ (h : Nat → Nat) c, c < s.C.size →
      (if c = s.C.size ∨ c = s.C.size + 1 then 0 else h c) = h c := by
    intro h c hc; rw [ite_eq_right (hnew c · hc)]
  have hfr0 : ∀ (h : Nat → Nat) c, c = s.C.size ∨ c = s.C.size + 1 →
      (if c = s.C.size ∨ c = s.C.size + 1 then 0 else h c) = 0 := by
    intro h c hc; rw [ite_eq_left hc]
  have eL : ∀ g, gL s' g = gL s g := fun g => by simp only [gL, hg]
  have eN : ∀ g, gN s' g = gN s g := fun g => by simp only [gN, hg]
  have eC : ∀ g, gC s' g = gC s g := fun g => by simp only [gC, hg]
  have eSt : ∀ g, gSt s' g = gSt s g := fun g => by simp only [gSt, hg]
  have eLl : ∀ g, gLl s' g = gLl s g := fun g => by simp only [gLl, hg]
  have eRr : ∀ g, gRr s' g = gRr s g := fun g => by simp only [gRr, hg]
  have hfx : famC s' x = cSz s x := by
    unfold famC
    rw [R.xs.2.2.2.1, R.xs.2.2.2.2, (R.new _ (Or.inl rfl)).1, R.xs.1, (R.new _ (Or.inr rfl)).1]
    omega
  have hstN : ∀ c, c = s.C.size ∨ c = s.C.size + 1 → cSt s' c = .overflow := fun c h => (R.new c
    h).2.2.1
  refine
    { gaps := ?_, range := ?_, hv := ?_, pb := ?_, pf := ?_, roots := ?_, claim2 := ?_,
      insQ := ?_, insO := ?_, insS := ?_, arrS := ?_, arrN := ?_, e0 := ?_, famChild := ?_ }
  · intro g hg' hl
    rw [hLv] at hg'
    have hgc := hcg g hg'
    change gL s' g + s'.P.groupSpacing / 2 ^ (if gC s' g = s.C.size ∨ gC s' g = s.C.size + 1 then 0
      else lg.hv (gC s' g)) ≤ gL s' (gN s' g)
    rw [eC] at hl ⊢
    rw [eL, eL, eN, R.P, hfr _ _ hgc]
    have hls : cLs s' (gC s g) = cLs s (gC s g) := by
      by_cases hx : gC s g = x
      · rw [hx]; exact R.xs.2.1
      · exact (R.old _ hgc hx).2.1
    rw [hls] at hl
    exact hL.gaps g hg' hl
  · intro g hg'
    rw [hLv] at hg'
    have hgc := hcg g hg'
    change cG s'.P ≤ gL s' g + (if gC s' g = s.C.size ∨ gC s' g = s.C.size + 1 then 0
      else lg.pf (gC s' g)) * s'.P.groupSpacing ∧ gL s' g ≤ cG s'.P +
        (if gC s' g = s.C.size ∨ gC s' g = s.C.size + 1 then 0 else lg.pb (gC s' g)) *
          s'.P.groupSpacing
    rw [eL, eC, R.P, hfr _ _ hgc, hfr _ _ hgc]
    exact hL.range g hg'
  · intro c
    change (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.hv c) ≤
      2 * ((if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.cs c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.rs c))
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · simp only [ite_eq_left hc]; omega
    · simp only [ite_eq_right hc]; exact hL.hv c
  · intro c
    change (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.pb c) ≤
      (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.arB c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.rs c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.cs c)
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · simp only [ite_eq_left hc]; omega
    · simp only [ite_eq_right hc]; exact hL.pb c
  · intro c
    change (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.pf c) ≤
      (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.arF c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.rs c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.cs c)
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · simp only [ite_eq_left hc]; omega
    · simp only [ite_eq_right hc]; exact hL.pf c
  · intro d hd
    change (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.rs d) + pending s' lg d ≤
      (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.arB d) +
        (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.arF d) + 1
    rcases (hLC d).mp hd with hd | hdn
    · rw [hfr _ _ hd.2, hfr _ _ hd.2, hfr _ _ hd.2, pending_of_Gs R.Gs]; exact hL.roots d hd
    · rw [hfr0 _ _ hdn, hfr0 _ _ hdn, hfr0 _ _ hdn]
      unfold pending; rw [hgrE d hdn]; simp only [ne_eq, Finset.filter_empty, Finset.card_empty,
          add_zero, zero_add, zero_le]
  · intro d hd
    change (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.cs d) * gmin s'.P + charge s' lg d ≤
      (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.ins d)
    rcases (hLC d).mp hd with hd | hdn
    · rw [hfr _ _ hd.2, hfr _ _ hd.2, charge_of_Gs R.Gs R.P, R.P]; exact hL.claim2 d hd
    · rw [hfr0 _ _ hdn, hfr0 _ _ hdn, charge_eq, hgrE d hdn]; simp only [zero_mul,
        Finset.sum_empty, add_zero,
        Std.le_refl]
  · intro d hd hds
    change (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.ins d) + lg.e0 d ≤
      cSz s' d + kC s'.P s'.P.T
    rcases (hLC d).mp hd with hd | hdn
    · have hdx : d ≠ x := by intro e; rw [e, R.xs.2.2.1] at hds; cases hds
      have o := R.old d hd.2 hdx
      rw [o.2.2.1] at hds
      rw [hfr _ _ hd.2, o.1, R.P]; exact hL.insQ d hd hds
    · rw [hstN d hdn] at hds; cases hds
  · intro d hd hds
    change (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.ins d) +
      Function.update s₀ x (cSz s x) (cSrc s' d) ≤ famC s' (cSrc s' d)
    rcases (hLC d).mp hd with hd | hdn
    · have hdx : d ≠ x := by intro e; rw [e, R.xs.2.2.1] at hds; cases hds
      have o := R.old d hd.2 hdx
      rw [o.2.2.1] at hds
      obtain ⟨p1, p2, -⟩ := hC.covf d hd hds
      have hsx := (hfamOld _ p1 p2).1
      rw [hfr _ _ hd.2, o.2.2.2.1, Function.update_of_ne hsx, hfamC _ p1 p2]
      exact hL.insO d hd hds
    · rw [hfr0 _ _ hdn, (R.new d hdn).2.2.2, Function.update_self, hfx]; omega
  · intro d hd hds
    change (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.ins d) ≤ famC s' d + kC s'.P s'.P.T
    rcases (hLC d).mp hd with hd | hdn
    · rw [hfr _ _ hd.2, R.P]
      by_cases hdx : d = x
      · rw [hdx, hfx]; have := hL.insQ x hxL hxq; omega
      · have o := R.old d hd.2 hdx
        rw [o.2.2.1] at hds
        rw [hfamC d hd hds]; exact hL.insS d hd hds
    · rw [hstN d hdn] at hds; cases hds
  · intro x' hx' hxs'
    rcases (hLC x').mp hx' with hx' | hdn
    · by_cases hdx : x' = x
      · subst hdx
        change (if cLl s' x' = s.C.size ∨ cLl s' x' = s.C.size + 1 then 0 else lg.arB (cLl s' x')) +
            (if cLl s' x' = s.C.size ∨ cLl s' x' = s.C.size + 1 then 0 else lg.arF (cLl s' x')) +
            (if cRr s' x' = s.C.size ∨ cRr s' x' = s.C.size + 1 then 0 else lg.arB (cRr s' x')) +
            (if cRr s' x' = s.C.size ∨ cRr s' x' = s.C.size + 1 then 0 else lg.arF (cRr s' x')) +
            3 * units s' x' + 3 * (0 + 0 + 0) + 3 * Function.update s₀ x' (cSz s x') x' ≤
          3 * (unitsOf s'.P (Function.update s₀ x' (cSz s x') x') + famC s' x') + 3 * 0
        rw [R.xs.2.2.2.1, R.xs.2.2.2.2, hfr0 _ _ (Or.inl rfl), hfr0 _ _ (Or.inl rfl),
          hfr0 _ _ (Or.inr rfl), hfr0 _ _ (Or.inr rfl), units_of_Gs R.Gs, Function.update_self, hfx,
          R.P]
        omega
      · have o := R.old x' hx'.2 hdx
        rw [o.2.2.1] at hxs'
        obtain ⟨-, -, -, h4, h5⟩ := hfamOld x' hx' hxs'
        have h := hL.arrS x' hx' hxs'
        change (if cLl s' x' = s.C.size ∨ cLl s' x' = s.C.size + 1 then 0 else lg.arB (cLl s' x')) +
            (if cLl s' x' = s.C.size ∨ cLl s' x' = s.C.size + 1 then 0 else lg.arF (cLl s' x')) +
            (if cRr s' x' = s.C.size ∨ cRr s' x' = s.C.size + 1 then 0 else lg.arB (cRr s' x')) +
            (if cRr s' x' = s.C.size ∨ cRr s' x' = s.C.size + 1 then 0 else lg.arF (cRr s' x')) +
            3 * units s' x' + 3 * (0 + 0 + 0) + 3 * Function.update s₀ x (cSz s x) x' ≤
          3 * (unitsOf s'.P (Function.update s₀ x (cSz s x) x') + famC s' x') + 3 * 0
        rw [o.2.2.2.2.1, o.2.2.2.2.2, hfr _ _ h4, hfr _ _ h4, hfr _ _ h5, hfr _ _ h5,
          units_of_Gs R.Gs, Function.update_of_ne hdx, hfamC x' hx' hxs', R.P]
        exact h
    · rw [hstN x' hdn] at hxs'; cases hxs'
  · intro d hd hds
    change (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.arB d) +
      (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.arF d) ≤ 3 * Mu s'.P
    rcases (hLC d).mp hd with hd | hdn
    · rw [hfr _ _ hd.2, hfr _ _ hd.2, R.P]
      by_cases hdx : d = x
      · rw [hdx]; exact hL.arrN x hxL (by rw [hxq]; simp)
      · have o := R.old d hd.2 hdx
        rw [o.2.2.1] at hds
        exact hL.arrN d hd hds
    · exact absurd (hstN d hdn) hds
  · intro d hd hds
    change lg.e0 d ≤ cSz s' d
    rcases (hLC d).mp hd with hd | hdn
    · have hdx : d ≠ x := by intro e; rw [e, R.xs.2.2.1] at hds; cases hds
      have o := R.old d hd.2 hdx
      rw [o.2.2.1] at hds
      rw [o.1]; exact hL.e0 d hd hds
    · rw [hstN d hdn] at hds; cases hds
  · intro p hp hps
    rw [hLv] at hp; rw [eSt] at hps
    change lg.child (gLl s' p) = lg.child (gRr s' p)
    rw [eLl, eRr]; exact hL.famChild p hp hps

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Steps that change nothing the label invariant reads -/

/-- The fields `LInv` reads are equal. -/
structure LSame (s s' : Core) : Prop where
  Gs : s'.Gs = s.Gs
  P : s'.P = s.P
  Csize : s'.C.size = s.C.size
  csz : ∀ c, cSz s' c = cSz s c
  cst : ∀ c, cSt s' c = cSt s c
  csrc : ∀ c, cSrc s' c = cSrc s c
  cl : ∀ c, cLl s' c = cLl s c
  cr : ∀ c, cRr s' c = cRr s c
  clast : ∀ c, cLs s' c = cLs s c

theorem LInv.transfer {s s' : Core} {lg : LGh} {s₀ δ δu : Nat → Nat} (S : LSame s s')
    (hL : LInv s lg s₀ δ δu) : LInv s' lg s₀ δ δu := by
  have hg : ∀ g, s'.Gs.getX g = s.Gs.getX g := fun g => by rw [S.Gs]
  have hLv := liveG_of_Gs S.Gs
  have eL : ∀ g, gL s' g = gL s g := fun g => by simp only [gL, hg]
  have eN : ∀ g, gN s' g = gN s g := fun g => by simp only [gN, hg]
  have eC : ∀ g, gC s' g = gC s g := fun g => by simp only [gC, hg]
  have eSt : ∀ g, gSt s' g = gSt s g := fun g => by simp only [gSt, hg]
  have eLl : ∀ g, gLl s' g = gLl s g := fun g => by simp only [gLl, hg]
  have eRr : ∀ g, gRr s' g = gRr s g := fun g => by simp only [gRr, hg]
  have hLC : ∀ c, LiveC s' c ↔ LiveC s c := fun c => by simp only [LiveC, S.Csize]
  have hfamC : ∀ c, famC s' c = famC s c := fun c => by
    unfold famC; rw [S.cl, S.cr, S.csz, S.csz, S.csz]
  refine
    { gaps := ?_, range := ?_, hv := hL.hv, pb := hL.pb, pf := hL.pf, roots := ?_, claim2 := ?_,
      insQ := ?_, insO := ?_, insS := ?_, arrS := ?_, arrN := ?_, e0 := ?_, famChild := ?_ }
  · intro g hg' hl
    rw [hLv] at hg'; rw [eC, S.clast] at hl
    rw [eL, eL, eN, eC, S.P]; exact hL.gaps g hg' hl
  · intro g hg'; rw [hLv] at hg'; rw [eL, eC, S.P]; exact hL.range g hg'
  · intro d hd; rw [hLC] at hd; rw [pending_of_Gs S.Gs]; exact hL.roots d hd
  · intro d hd; rw [hLC] at hd; rw [charge_of_Gs S.Gs S.P, S.P]; exact hL.claim2 d hd
  · intro d hd hds; rw [hLC] at hd; rw [S.cst] at hds; rw [S.csz, S.P]; exact hL.insQ d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [S.cst] at hds; rw [S.csrc, hfamC]
    exact hL.insO d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [S.cst] at hds; rw [hfamC, S.P]; exact hL.insS d hd hds
  · intro x hx hxs; rw [hLC] at hx; rw [S.cst] at hxs
    rw [S.cl, S.cr, units_of_Gs S.Gs, hfamC, S.P]; exact hL.arrS x hx hxs
  · intro d hd hds; rw [hLC] at hd; rw [S.cst] at hds; rw [S.P]; exact hL.arrN d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [S.cst] at hds; rw [S.csz]; exact hL.e0 d hd hds
  · intro p hp hps; rw [hLv] at hp; rw [eSt] at hps; rw [eLl, eRr]; exact hL.famChild p hp hps

/-- The top structure's steps change nothing the label invariant reads. -/
theorem TopRel.lsame {s s' : Core} (h : TopRel s s') : LSame s s' := by
  have hc : ∀ c, s'.C.getX c = { s.C.getX c with tag := (s'.C.getX c).tag } := h.C
  refine ⟨h.Gs, h.rest.1, h.Csize, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_,
    fun c => ?_, fun c => ?_⟩ <;>
    simp only [cSz, cSt, cSrc, cLl, cRr, cLs] <;> rw [hc c]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem LSame.trans {a b c : Core} (h1 : LSame a b) (h2 : LSame b c) : LSame a c :=
  ⟨h2.Gs.trans h1.Gs, h2.P.trans h1.P, h2.Csize.trans h1.Csize, fun d => (h2.csz d).trans
    (h1.csz d),
    fun d => (h2.cst d).trans (h1.cst d), fun d => (h2.csrc d).trans (h1.csrc d),
    fun d => (h2.cl d).trans (h1.cl d), fun d => (h2.cr d).trans (h1.cr d),
    fun d => (h2.clast d).trans (h1.clast d)⟩

section lcp
variable {s : Core} {x y z : Nat}

theorem linkChunkPair_cSz (w : Nat) : cSz (linkChunkPair s x y z) w = cSz s w := by
  simp only [linkChunkPair, cSz, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.size)]
  split_ifs <;> rfl

theorem linkChunkPair_cSt (w : Nat) : cSt (linkChunkPair s x y z) w = cSt s w := by
  simp only [linkChunkPair, cSt, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.st)]
  split_ifs <;> rfl

theorem linkChunkPair_cSrc (w : Nat) : cSrc (linkChunkPair s x y z) w = cSrc s w := by
  simp only [linkChunkPair, cSrc, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.src)]
  split_ifs <;> rfl

theorem linkChunkPair_cLl (w : Nat) : cLl (linkChunkPair s x y z) w = cLl s w := by
  simp only [linkChunkPair, cLl, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.l)]
  split_ifs <;> rfl

theorem linkChunkPair_cRr (w : Nat) : cRr (linkChunkPair s x y z) w = cRr s w := by
  simp only [linkChunkPair, cRr, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Chunk.r)]
  split_ifs <;> rfl

end lcp

theorem linkChunkPair_lsame (s : Core) (x y z : Nat) : LSame s (linkChunkPair s x y z) :=
  ⟨rfl, rfl, (linkChunkPair_rest (s := s) (x := x) (y := y) (z := z)).2.2.2.2.2.2.1,
    linkChunkPair_cSz, linkChunkPair_cSt, linkChunkPair_cSrc, linkChunkPair_cLl, linkChunkPair_cRr,
    linkChunkPair_cLs⟩

theorem INV.cN_cP {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hx : x ∈ A.chunks)
    (hp : cP s x ≠ NIL) : cN s (cP s x) = x := by
  have hnd := hI.cList.nodup
  obtain ⟨l1, l2, e⟩ := predOf_split (hI.cList.prev x hx).symm hp
  have hm : cP s x ∈ A.chunks := by rw [e]; simp only [List.mem_append, List.mem_cons, true_or,
      or_true]
  rw [hI.cList.next _ hm, e, succOf_mid (e ▸ hnd)]; rfl

/-- The linking of two new chunks around `x` does what it should. -/
theorem linkCOK_push2 {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hx : x ∈ A.chunks) :
    LinkCOK (push2 s) x s.C.size (s.C.size + 1) := by
  have hcnd := hI.cList.nodup
  have hxs : x < s.C.size := ((hI.cAlloc x).mp hx).2
  have hx1 : 1 ≤ x := ((hI.cAlloc x).mp hx).1
  have hp1 : cP (push2 s) x = cP s x := by
    simp only [cP, push2, Array.getX_push,
      Array.size_push]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hn1 : cN (push2 s) x = cN s x := by
    simp only [cN, push2, Array.getX_push,
      Array.size_push]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hsz : (push2 s).C.size = s.C.size + 2 := by
    simp only [push2, Array.size_push, ]
  have hpm : cP s x = NIL ∨ cP s x ∈ A.chunks := by
    by_cases h : cP s x = NIL
    · exact Or.inl h
    · right; obtain ⟨l1, l2, e⟩ := predOf_split (hI.cList.prev x hx).symm h; rw [e]; simp only [
        List.mem_append,
        List.mem_cons,
        true_or,
        or_true]
  have hnm : cN s x = NIL ∨ cN s x ∈ A.chunks := by
    by_cases h : cN s x = NIL
    · exact Or.inl h
    · right; obtain ⟨l1, l2, e⟩ := succOf_split (hI.cList.next x hx).symm h; rw [e]; simp only [
        List.mem_append,
        List.mem_cons,
        true_or,
        or_true]
  have hlt : ∀ c, c = NIL ∨ c ∈ A.chunks → c < s.C.size := by
    intro c hc; rcases hc with h | h
    · rw [h]; unfold NIL; omega
    · exact ((hI.cAlloc c).mp h).2
  have hpy := hlt _ hpm
  have hny := hlt _ hnm
  have hpx : cP s x ≠ x := by
    rw [hI.cList.prev x hx]; exact predOf_ne_self hcnd x (by unfold NIL; omega)
  have hnx : cN s x ≠ x := by
    rw [hI.cList.next x hx]; exact succOf_ne_self hcnd x (by unfold NIL; omega)
  have hpn : cP s x ≠ NIL → cP s x ≠ cN s x := by
    intro h0; rw [hI.cList.prev x hx, hI.cList.next x hx]
    exact predOf_ne_succOf hcnd hx (by rw [← hI.cList.prev x hx]; exact h0)
  refine ⟨by omega, by omega, by omega, fun h => by rw [hp1] at h ⊢; omega,
    fun h => by rw [hn1] at h ⊢; omega, by omega, by omega, by omega,
    by rw [hp1]; omega, by rw [hp1]; omega, by rw [hn1]; omega, by rw [hn1]; omega,
    by rw [hp1]; exact hpx, by rw [hn1]; exact hnx, fun h => by rw [hp1, hn1] at *; exact hpn h⟩

/-- **The state after starting the split of `x`**, from the run of `splitChunkStart`: the fields
other than the chunk links. -/
theorem resSpec_run_core {s s2 : Core} {x : Nat} {job : Job} (hxs : x < s.C.size)
    (hT : TopRel (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s2) :
    ResSpec' s (markState s2 x s.C.size (s.C.size + 1) job) x := by
  have S := (linkChunkPair_lsame (push2 s) x s.C.size (s.C.size + 1)).trans hT.lsame
  have hsz2 : s2.C.size = s.C.size + 2 := by rw [S.Csize]; simp only [push2, Array.size_push,
      ]
  -- the fields of `push2 s`
  have hp : ∀ c, (push2 s).C.getX c =
      if c = s.C.size + 1 then {} else if c = s.C.size then {} else s.C.getX c := by
    intro c; simp only [push2, Array.getX_push, Array.size_push]
  -- the fields of the marked state, from those of `s2`
  have hm : ∀ c, (markState s2 x s.C.size (s.C.size + 1) job).C.getX c =
      if c = s.C.size + 1 then { s2.C.getX c with st := .overflow, src := x }
      else if c = s.C.size then { s2.C.getX c with st := .overflow, src := x }
      else if c = x then { s2.C.getX c with st := .splitting, l := s.C.size, r := s.C.size + 1 }
      else s2.C.getX c := by
    intro c
    simp only [markState, Array.getX_modify, Array.size_modify', hsz2]
    by_cases h1 : c = s.C.size + 1
    · subst h1; simp only [ add_lt_add_iff_left, Nat.one_lt_ofNat,
        and_self, ↓reduceIte, Nat.left_eq_add, one_ne_zero, lt_add_iff_pos_right,
        Nat.ofNat_pos, and_true, show x ≠ s.C.size + 1 by omega, false_and]
    · by_cases h2 : c = s.C.size
      · subst h2; simp only [Nat.add_eq_left, one_ne_zero, add_lt_add_iff_left, Nat.one_lt_ofNat,
          and_true, ↓reduceIte, lt_add_iff_pos_right, Nat.ofNat_pos, and_self,
          show x ≠ s.C.size by omega, false_and, Nat.left_eq_add]
      · by_cases h3 : c = x
        · subst h3; simp only [Ne.symm h1, add_lt_add_iff_left, Nat.one_lt_ofNat, and_true,
            ↓reduceIte, Ne.symm h2, lt_add_iff_pos_right, Nat.ofNat_pos,
            true_and, h1, h2, ite_eq_left_iff, not_lt]; omega
        · simp only [Ne.symm h1, add_lt_add_iff_left, Nat.one_lt_ofNat, and_true, ↓reduceIte,
            Ne.symm h2, lt_add_iff_pos_right, Nat.ofNat_pos, Ne.symm h3, false_and, h1,
            h2, h3]
  have e2 : ∀ c, cSz s2 c = cSz (push2 s) c ∧ cLs s2 c = cLs (push2 s) c ∧
      cSt s2 c = cSt (push2 s) c ∧ cSrc s2 c = cSrc (push2 s) c ∧ cLl s2 c = cLl (push2 s) c ∧
      cRr s2 c = cRr (push2 s) c := fun c => ⟨S.csz c, S.clast c, S.cst c, S.csrc c, S.cl c, S.cr c⟩
  refine ⟨?_, ?_, ?_, fun c hc hcx => ?_, ?_, fun c hc => ?_⟩
  · change s2.Gs = s.Gs; exact S.Gs
  · change s2.P = s.P; exact S.P
  · simp only [markState, Array.size_modify, hsz2]
  · have h1 : c ≠ s.C.size + 1 := by omega
    have h2 : c ≠ s.C.size := by omega
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := e2 c
    simp only [cSz, cLs, cSt, cSrc, cLl, cRr] at a1 a2 a3 a4 a5 a6 ⊢
    rw [hm, ite_eq_right h1, ite_eq_right h2, ite_eq_right hcx, a1, a2, a3, a4, a5, a6, hp,
      ite_eq_right h1, ite_eq_right h2]
    simp only [and_self]
  · have h1 : x ≠ s.C.size + 1 := by omega
    have h2 : x ≠ s.C.size := by omega
    obtain ⟨a1, a2, -, -, -, -⟩ := e2 x
    simp only [cSz, cLs, cSt, cLl, cRr] at a1 a2 ⊢
    rw [hm, ite_eq_right h1, ite_eq_right h2, ite_eq_left rfl]
    simp only
    rw [a1, a2, hp, ite_eq_right h1, ite_eq_right h2]
    simp only [and_self]
  · obtain ⟨a1, a2, -, -, -, -⟩ := e2 c
    simp only [cSz, cLs, cSt, cSrc] at a1 a2 ⊢
    rcases hc with rfl | rfl
    · rw [hm, ite_eq_right (by omega), ite_eq_left rfl]
      simp only
      rw [a1, a2, hp, ite_eq_right (by omega), ite_eq_left rfl]
      simp only [and_self]
    · rw [hm, ite_eq_left rfl]
      simp only
      rw [a1, a2, hp, ite_eq_left rfl]
      simp only [and_self]


theorem resSpec_run {s s2 : Core} {A : Abs} {x : Nat} {job : Job} (hI : INV s A)
    (hxA : x ∈ A.chunks)
    (hT : TopRel (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s2) :
    ResSpec s (markState s2 x s.C.size (s.C.size + 1) job) x := by
  have hxs : x < s.C.size := ((hI.cAlloc x).mp hxA).2
  have hLk := linkCOK_push2 hI hxA
  have hcN : ∀ w, cN (markState s2 x s.C.size (s.C.size + 1) job) w =
      cN (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) w := by
    intro w
    have h1 : cN (markState s2 x s.C.size (s.C.size + 1) job) w = cN s2 w := by
      simp only [cN, markState, Array.getX_modify]; split_ifs <;> rfl
    have h2 : cN s2 w = cN (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) w := by
      simp only [cN]; rw [hT.C w]
    rw [h1, h2]
  have hp1 : cP (push2 s) x = cP s x := by
    simp only [cP, push2, Array.getX_push,
      Array.size_push]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hn1 : cN (push2 s) x = cN s x := by
    simp only [cN, push2, Array.getX_push,
      Array.size_push]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hpw : ∀ w, w < s.C.size → cN (push2 s) w = cN s w := by
    intro w hw
    simp only [cN, push2, Array.getX_push,
      Array.size_push]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have RS := resSpec_run_core (job := job) hxs hT
  refine { RS with ylink := ?_, xlink := ?_, next := ?_ }
  · rw [hcN, hLk.cN']; simp only [show s.C.size ≠ x by omega, ↓reduceIte]
  · rw [hcN, hLk.cN', ite_eq_left rfl]
  · intro c hc hcx hcp
    rw [hcN, hLk.cN', ite_eq_right hcx, ite_eq_right (by omega), ite_eq_right (by omega), hp1,
      ite_eq_right (fun h => hcp h.1), hpw c hc]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Units of a chunk, at most -/

/-- A chunk's size is the sum of its groups' sizes. -/
theorem cSz_eq_sum {s : Core} {A : Abs} {gh : GGh} {δg δ δu s₀ : Nat → Nat} {ex ex' : Nat}
    (hI : INV s A) (hG : GInvE s A.elist gh δg ex) (hC : CInvE s A.elist δ δu s₀ ex') {x : Nat}
    (hx : LiveC s x) : cSz s x = ∑ h ∈ GrpsC s x, gSz s h := by
  rw [hC.csz x hx]; unfold celts
  have e1 : A.elist.filter (fun e => gC s (eG s e) = x) =
      A.elist.filter (fun e => decide (eG s e ∈ (GrpsC s x).toList)) := by
    refine List.filter_congr fun e he => ?_
    have hl : LiveG s (eG s e) := hI.mem_glist_iff.mp (hI.eG_mem he)
    by_cases h : gC s (eG s e) = x
    · simp only [h, decide_true, Finset.mem_toList, mem_GrpsC, hl, and_self]
    · simp only [h, decide_false, Finset.mem_toList, mem_GrpsC, and_false]
  rw [e1, length_filter_mem s _ _ (Finset.nodup_toList _), Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun h hh => ?_
  exact (hG.sz h (mem_GrpsC.mp hh).1).symm

/-- The groups a unit covers: a quiet group, or a whole family. -/
def unitMem (s : Core) (g : Nat) : Finset Nat :=
  if gSt s g = .splitting then {gLl s g, g, gRr s g} else {g}

/-- **Units at most `size / g_min + 1`**: every unit but the one holding the sentinel has at least
`g_min` elements. -/
theorem units_le {s : Core} {A : Abs} {gh : GGh} {δg δ δu s₀ : Nat → Nat} {ex' : Nat}
    (hI : INV s A) (hG : GInv s A.elist gh δg) (hC : CInvE s A.elist δ δu s₀ ex')
    {x : Nat} (hx : LiveC s x) :
    units s x * gmin s.P ≤ cSz s x + gmin s.P := by
  have hgG : gmin s.P ≤ s.P.G := by unfold gmin; omega
  set U := (Finset.range s.Gs.size).filter (UnitG s x) with hU
  have hmemU : ∀ g, g ∈ U ↔ UnitG s x g := by
    intro g; rw [hU, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨h.1.2.1, h⟩⟩
  -- the covered groups lie in `x`
  have hsub : U.biUnion (unitMem s) ⊆ GrpsC s x := by
    intro h hh
    obtain ⟨g, hg, hm⟩ := Finset.mem_biUnion.mp hh
    obtain ⟨hgL, hgx, -⟩ := (hmemU g).mp hg
    unfold unitMem at hm
    split at hm
    · next hs =>
      have F := hG.fam g hgL hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl
      · exact mem_GrpsC.mpr ⟨F.lLive, by rw [F.lC, hgx]⟩
      · exact mem_GrpsC.mpr ⟨hgL, hgx⟩
      · exact mem_GrpsC.mpr ⟨F.rLive, by rw [F.rC, hgx]⟩
    · rw [Finset.mem_singleton] at hm; subst hm; exact mem_GrpsC.mpr ⟨hgL, hgx⟩
  -- units cover disjoint sets of groups
  have hdisj : (U : Set Nat).PairwiseDisjoint (unitMem s) := by
    intro g1 h1 g2 h2 hne
    have u1 := (hmemU g1).mp h1
    have u2 := (hmemU g2).mp h2
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    unfold unitMem at ha hb
    by_cases s1 : gSt s g1 = .splitting <;> by_cases s2 : gSt s g2 = .splitting <;>
      simp only [s1, s2, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton] at ha hb
    · have F1 := hG.fam g1 u1.1 s1
      have F2 := hG.fam g2 u2.1 s2
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := F1.disjoint F2 hne s1 s2
      rcases ha with rfl | rfl | rfl <;> rcases hb with e | e | e <;> simp_all
    · have F1 := hG.fam g1 u1.1 s1
      subst hb
      rcases ha with e | e | e
      · have := F1.lSt; rw [← e] at this; exact u2.2.2 this
      · exact hne e.symm
      · have := F1.rSt; rw [← e] at this; exact u2.2.2 this
    · have F2 := hG.fam g2 u2.1 s2
      subst ha
      rcases hb with e | e | e
      · have := F2.lSt; rw [← e] at this; exact u1.2.2 this
      · exact hne e
      · have := F2.rSt; rw [← e] at this; exact u1.2.2 this
    · exact hne (ha.symm.trans hb)
  have hup : ∑ g ∈ U, ∑ h ∈ unitMem s g, gSz s h ≤ cSz s x := by
    rw [← Finset.sum_biUnion hdisj, cSz_eq_sum hI hG hC hx]
    exact Finset.sum_le_sum_of_subset hsub
  -- every unit but the sentinel's has `g_min` elements
  have hlow : ∀ g ∈ U.erase (eG s s.head), gmin s.P ≤ ∑ h ∈ unitMem s g, gSz s h := by
    intro g hg
    obtain ⟨hgh, hg⟩ := Finset.mem_erase.mp hg
    obtain ⟨hgL, -, hno⟩ := (hmemU g).mp hg
    unfold unitMem
    by_cases hs : gSt s g = .splitting
    · rw [ite_eq_left hs]
      have F := hG.fam g hgL hs
      have hlp := F.lp hI hgL
      have hrp := F.rp hI hgL
      have hlr := F.lr hI hgL
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, hlp, Finset.mem_singleton, hlr, or_self,
          not_false_eq_true]), Finset.sum_insert (by
            simp only [Finset.mem_singleton, Ne.symm hrp, not_false_eq_true]),
        Finset.sum_singleton]
      have := (hG.split g hgL hs (by unfold NIL; have := hgL.1; omega)).1
      omega
    · rw [ite_eq_right hs, Finset.sum_singleton]
      have hq : gSt s g = .quiet := by
        cases h : gSt s g
        · rfl
        · exact absurd h hno
        · exact absurd h hs
        · exact absurd h (hG.notDead g hgL)
      obtain ⟨-, -, h3⟩ := hG.quiet g hgL hq
      rcases h3 with h3 | h3
      · exact h3
      · exact absurd (mem_runOf.mp h3).2 (Ne.symm hgh)
  have h1 : gmin s.P * (U.erase (eG s s.head)).card ≤ ∑ g ∈ U, ∑ h ∈ unitMem s g, gSz s h := by
    calc gmin s.P * (U.erase (eG s s.head)).card
        = ∑ g ∈ U.erase (eG s s.head), gmin s.P := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ g ∈ U.erase (eG s s.head), ∑ h ∈ unitMem s g, gSz s h := Finset.sum_le_sum hlow
      _ ≤ ∑ g ∈ U, ∑ h ∈ unitMem s g, gSz s h :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  have h2 : U.card ≤ (U.erase (eG s s.head)).card + 1 := by
    by_cases h : eG s s.head ∈ U
    · rw [Finset.card_erase_of_mem h]; have := Finset.card_pos.mpr ⟨_, h⟩; omega
    · rw [Finset.erase_eq_of_notMem h]; omega
  have hunits : units s x = U.card := rfl
  rw [hunits]
  have : U.card * gmin s.P ≤ (U.erase (eG s s.head)).card * gmin s.P + gmin s.P := by
    have := Nat.mul_le_mul_right (gmin s.P) h2; rw [Nat.add_mul, Nat.one_mul] at this; exact this
  rw [mul_comm] at h1
  omega

theorem units_le_unitsOf {s : Core} {A : Abs} {gh : GGh} {δg δ δu s₀ : Nat → Nat} {ex' : Nat}
    (hI : INV s A) (hG : GInv s A.elist gh δg) (hC : CInvE s A.elist δ δu s₀ ex')
    (hP : GParams s.P) {x : Nat} (hx : LiveC s x) : units s x ≤ unitsOf s.P (cSz s x) := by
  have h := units_le hI hG hC hx
  have hgm : 0 < gmin s.P := by unfold gmin; have := hP.G4; omega
  unfold unitsOf
  have : units s x - 1 ≤ cSz s x / gmin s.P := by
    rw [Nat.le_div_iff_mul_le hgm, Nat.sub_mul, Nat.one_mul]; omega
  omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The insertion's state -/

/-- The chunk-size update of an insertion. -/
def sizeState (s : Core) (c : Nat) : Core :=
  { s with C := s.C.modify c fun C => { C with size := (s.C.getX c).size + 1 } }

theorem chunkSize_run_nq {s : Core} {c : Nat} (hq : cSt s c ≠ .quiet) :
    (chunkSize c true).run s = .ok () (sizeState s c) := by
  unfold chunkSize modC
  simp only [run_getC_bind, ite_true, run_modify_bind]
  rw [ite_eq_right (by simpa [cSt] using hq)]
  rfl

theorem chunkSize_run_q {s : Core} {c : Nat} (hq : cSt s c = .quiet) :
    (chunkSize c true).run s = (pqAdjust c (cSz s c) (cSz s c + 1)).run (sizeState s c) := by
  unfold chunkSize modC
  simp only [run_getC_bind, ite_true, run_modify_bind]
  rw [ite_eq_left (by simpa [cSt] using hq)]
  rfl

/-- **The insertion's effect on what the label invariant reads**: the element link, then the
chunk-size update (the priority-queue fields may change too). -/
theorem insSpec_link {s s2 : Core} {x lab hh : Nat} (hg : eG s x < s.Gs.size)
    (hcs : gC s (eG s x) < s.C.size)
    (hGs : s2.Gs = (linkElem s x s.E.size lab hh).Gs)
    (hC : s2.C = (sizeState (linkElem s x s.E.size lab hh) (gC s (eG s x))).C)
    (hP : s2.P = s.P) : InsSpec s s2 (eG s x) := by
  have hG : ∀ b, s2.Gs.getX b = (linkElem s x s.E.size lab hh).Gs.getX b := fun b => by rw [hGs]
  have hCx : ∀ d, s2.C.getX d = if gC s (eG s x) = d ∧ gC s (eG s x) < s.C.size then
      { s.C.getX d with size := (s.C.getX d).size + 1 } else s.C.getX d := by
    intro d
    have e : (linkElem s x s.E.size lab hh).C = s.C := rfl
    rw [hC]; simp only [sizeState, Array.getX_modify, e]
    by_cases h : gC s (eG s x) = d
    · subst h; simp only [true_and]
    · simp only [h, false_and, ↓reduceIte]
  have fld : ∀ b, gL s2 b = gL s b ∧ gN s2 b = gN s b ∧ gC s2 b = gC s b ∧ gSt s2 b = gSt s b ∧
      gLl s2 b = gLl s b ∧ gRr s2 b = gRr s b ∧ gA s2 b = gA s b := by
    intro b; simp only [gL, gN, gC, gSt, gLl, gRr, gA, hG b, linkElem_Gs]; split <;> simp only [
        and_self]
  have cfl : ∀ d, cSt s2 d = cSt s d ∧ cSrc s2 d = cSrc s d ∧ cLl s2 d = cLl s d ∧
      cRr s2 d = cRr s d ∧ cLs s2 d = cLs s d ∧ cN s2 d = cN s d := by
    intro d; simp only [cSt, cSrc, cLl, cRr, cLs, cN, hCx d]; split <;> simp only [and_self]
  have hGsz : s2.Gs.size = s.Gs.size := by rw [hGs]; simp only [linkElem, bne_iff_ne, ne_eq,
      ite_not, beq_iff_eq,
      Array.size_modify]
  refine
    { live := fun z => ?_, lab := fun z => (fld z).1, next := fun z => (fld z).2.1,
      chk := fun z => (fld z).2.2.1, st := fun z => (fld z).2.2.2.1, l := fun z => (fld
        z).2.2.2.2.1,
      r := fun z => (fld z).2.2.2.2.2.1, sz := fun z => ?_, Csize := ?_,
      cst := fun d => (cfl d).1, csrc := fun d => (cfl d).2.1, cl := fun d => (cfl d).2.2.1,
      cr := fun d => (cfl d).2.2.2.1, clast := fun d => (cfl d).2.2.2.2.1, csz := fun d => ?_,
      P := hP, cnext := fun d => (cfl d).2.2.2.2.2 }
  · simp only [LiveG, hGsz, (fld z).2.2.2.2.2.2]
  · have : gSz s2 z = gSz (linkElem s x s.E.size lab hh) z := by simp only [gSz, hGs]
    rw [this, linkElem_gSz s x lab hh z hg]
    split <;> simp_all
  · rw [hC]; simp only [sizeState, linkElem, bne_iff_ne, ne_eq, ite_not, beq_iff_eq,
      Array.size_modify]
  · simp only [cSz, hCx d]
    by_cases h : d = gC s (eG s x)
    · subst h; simp only [hcs, and_self, ↓reduceIte]
    · simp only [Ne.symm h, false_and, ↓reduceIte, h, add_zero]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem length_insertAfterL {x y : Nat} {l : List Nat} (hx : x ∈ l) :
    (OrderMaintenance.Spec.insertAfterL x y l).length = l.length + 1 := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hx
  | cons a t ih =>
    simp only [OrderMaintenance.Spec.insertAfterL]
    by_cases hax : a = x
    · simp only [hax, ↓reduceIte, List.length_cons]
    · have : x ∈ t := by
        simp only [List.mem_cons] at hx
        rcases hx with h | h
        · exact absurd h.symm hax
        · exact h
      simp only [hax, ↓reduceIte, List.length_cons, ih this]

/-- **The chunk invariant across an insertion**: the chunk's size grows with one more undriven
insertion. -/
theorem cinv_ins {s s2 : Core} {A : Abs} {δ δu s₀ : Nat → Nat} {ex x lab hh : Nat}
    (hI : INV s A) (hC : CInvE s A.elist δ δu s₀ ex) (hx : x ∈ A.elist)
    (S : InsSpec s s2 (eG s x)) (hE : ∀ e, eG s2 e = eG (linkElem s x s.E.size lab hh) e) :
    CInvE s2 (OrderMaintenance.Spec.insertAfterL x s.E.size A.elist)
      (Function.update δ (gC s (eG s x)) (δ (gC s (eG s x)) + 1)) δu s₀ ex := by
  have hy : s.E.size ∉ A.elist := fun h => by have := ((hI.eAlloc _).mp h).2; omega
  have hxy : x ≠ s.E.size := fun e => hy (e ▸ hx)
  have hcsz := S.csz
  generalize hc : gC s (eG s x) = c at hcsz ⊢
  have hLC : ∀ d, LiveC s2 d ↔ LiveC s d := fun d => by simp only [LiveC, S.Csize]
  have hcd : ∀ d, cSz s2 d - Function.update δ c (δ c + 1) d = cSz s d - δ d := by
    intro d; rw [hcsz]
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self, ite_eq_left rfl]; omega
    · rw [Function.update_of_ne hdc, ite_eq_right hdc]; omega
  have hun : ∀ d, units s2 d = units s d := fun d =>
    units_congr fun z => by unfold UnitG; rw [S.live, S.chk, S.st]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [hLC] at hd
    unfold celts
    have e1 : (OrderMaintenance.Spec.insertAfterL x s.E.size A.elist).filter
        (fun e => decide (gC s2 (eG s2 e) = d)) =
        (OrderMaintenance.Spec.insertAfterL x s.E.size A.elist).filter
          (fun e => decide (gC s (eG (linkElem s x s.E.size lab hh) e) = d)) := by
      congr 1; funext e; rw [S.chk, hE]
    rw [e1,
      filter_insertAfterL _ _ _ _ (by rw [linkElem_eG, linkElem_eG, ite_eq_right hxy,
      ite_eq_left rfl])]
    have e2 : A.elist.filter (fun e => decide (gC s (eG (linkElem s x s.E.size lab hh) e) = d)) =
        celts s A.elist d := by
      unfold celts
      refine List.filter_congr fun e he => ?_
      have : e ≠ s.E.size := fun h => hy (h ▸ he)
      rw [linkElem_eG, ite_eq_right this]
    rw [linkElem_eG, ite_eq_right hxy, hc, e2, hcsz, hC.csz d hd]
    by_cases hdc : c = d
    · subst hdc
      rw [ite_eq_left rfl, ite_eq_left (show decide (c = c) = true by simp), length_insertAfterL]
      unfold celts; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hc⟩
    · rw [ite_eq_right (Ne.symm hdc),
      ite_eq_right (show ¬ decide (c = d) = true by simpa using hdc)]; rfl
  · intro y hy hys
    rw [hLC] at hy; rw [S.cst] at hys
    have F := hC.cfam y hy hys
    exact ⟨by rw [hLC, S.cl]; exact F.lLive, by rw [hLC, S.cr]; exact F.rLive,
      by rw [S.cl, S.cnext]; exact F.lAdj, by rw [S.cnext, S.cr]; exact F.rAdj,
      by rw [S.cl, S.cst]; exact F.lSt, by rw [S.cl, S.csrc]; exact F.lSrc,
      by rw [S.cr, S.cst]; exact F.rSt, by rw [S.cr, S.csrc]; exact F.rSrc⟩
  · intro d hd hds
    rw [hLC] at hd; rw [S.cst] at hds
    obtain ⟨p1, p2, p3⟩ := hC.covf d hd hds
    rw [S.csrc, hLC, S.cst, S.cl, S.cr]; exact ⟨p1, p2, p3⟩
  · intro g hg
    rw [S.live] at hg
    rw [S.chk, hLC, S.cst]; exact hC.gchk g hg
  · intro y hy hys hyx
    rw [hLC] at hy; rw [S.cst] at hys
    have := hC.c1 y hy hys hyx
    unfold C1 at this ⊢
    rw [S.cl, S.cr, hcd, hcd, hcd, hun, S.P]; exact this
  · intro d
    have := hC.δu d
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hdc]; exact this

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- **The chunk invariant at the pop**: C1 starts for the new family of `x`, with `s₀ x` the size
of `x`. -/
theorem cinv_pop {s s' : Core} {A : Abs} {s₀ : Nat → Nat} {x : Nat} (hI : INV s A)
    (R : ResSpec s s' x) (hE : s'.E = s.E) (hC : CInv s A.elist (fun _ => 0) (fun _ => 0) s₀)
    (hxL : LiveC s x) (hxq : cSt s x = .quiet) (hT : cSz s x ≤ s.P.T)
    (hun : units s x ≤ unitsOf s.P (cSz s x)) :
    CInv s' A.elist (fun _ => 0) (fun _ => 0) (Function.update s₀ x (cSz s x)) := by
  have hg : ∀ g, s'.Gs.getX g = s.Gs.getX g := fun g => by rw [R.Gs]
  have hLv := liveG_of_Gs R.Gs
  have eC : ∀ g, gC s' g = gC s g := fun g => by simp only [gC, hg]
  have eG' : ∀ e, eG s' e = eG s e := fun e => by simp only [eG, hE]
  have hcg : ∀ g, LiveG s g → gC s g < s.C.size := fun g hg' => (hC.gchk g hg').1.2
  have hxA : x ∈ A.chunks := (hI.cAlloc x).mpr hxL
  have hLC : ∀ c, LiveC s' c ↔ LiveC s c ∨ c = s.C.size ∨ c = s.C.size + 1 := by
    intro c; simp only [LiveC, R.Csize]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : c < s.C.size
      · exact Or.inl ⟨h1, h3⟩
      · right; omega
    · rintro (⟨h1, h2⟩ | h | h)
      · exact ⟨h1, by omega⟩
      · subst h; exact ⟨hxL.1.trans (Nat.le_of_lt hxL.2), by omega⟩
      · subst h; exact ⟨by omega, by omega⟩
  -- an old splitting chunk's family avoids `x` and the predecessor of `x`
  have hfam : ∀ y, LiveC s y → cSt s y = .splitting →
      y ≠ x ∧ cLl s y ≠ x ∧ cRr s y ≠ x ∧ cLl s y ≠ cP s x ∧ y ≠ cP s x := by
    intro y hy hys
    have F := hC.cfam y hy hys
    have h1 : y ≠ x := by rintro rfl; rw [hxq] at hys; cases hys
    have h2 : cLl s y ≠ x := by intro e; have := F.lSt; rw [e, hxq] at this; cases this
    have h3 : cRr s y ≠ x := by intro e; have := F.rSt; rw [e, hxq] at this; cases this
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · intro e
      have hp0 : cP s x ≠ NIL := by rw [← e]; unfold NIL; have := F.lLive.1; omega
      have := hI.cN_cP hxA hp0
      rw [← e, F.lAdj] at this; exact h1 this
    · intro e
      have hp0 : cP s x ≠ NIL := by rw [← e]; unfold NIL; have := hy.1; omega
      have := hI.cN_cP hxA hp0
      rw [← e, F.rAdj] at this; exact h3 this
  have hunits : ∀ c, units s' c = units s c := units_of_Gs R.Gs
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => le_rfl⟩
  · -- sizes
    intro d hd
    unfold celts
    have hf : A.elist.filter (fun e => decide (gC s' (eG s' e) = d)) =
        A.elist.filter (fun e => decide (gC s (eG s e) = d)) := by
      congr 1; funext e; rw [eC, eG']
    rw [hf]
    rcases (hLC d).mp hd with hd | hdn
    · have hcs : cSz s' d = cSz s d := by
        by_cases hdx : d = x
        · rw [hdx]; exact R.xs.1
        · exact (R.old d hd.2 hdx).1
      rw [hcs]; exact hC.csz d hd
    · rw [(R.new d hdn).1]
      symm; apply List.length_eq_zero_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro e he
      have hl := hI.mem_glist_iff.mp (hI.eG_mem he)
      have := hcg _ hl
      simp only [decide_eq_true_eq]; rcases hdn with rfl | rfl <;> omega
  · -- families
    intro y hy hys
    rcases (hLC y).mp hy with hy | hyn
    · by_cases hyx : y = x
      · subst hyx
        have hNL : LiveC s' s.C.size := (hLC _).mpr (Or.inr (Or.inl rfl))
        have hNR : LiveC s' (s.C.size + 1) := (hLC _).mpr (Or.inr (Or.inr rfl))
        obtain ⟨-, -, -, hl, hr⟩ := R.xs
        refine ⟨by rw [hl]; exact hNL, by rw [hr]; exact hNR, by rw [hl, R.ylink], by rw [hr,
          R.xlink],
          by rw [hl]; exact (R.new _ (Or.inl rfl)).2.2.1, by rw [hl]; exact (R.new _ (Or.inl
            rfl)).2.2.2,
          by rw [hr]; exact (R.new _ (Or.inr rfl)).2.2.1, by rw [hr]; exact (R.new _ (Or.inr
            rfl)).2.2.2⟩
      · have o := R.old y hy.2 hyx
        rw [o.2.2.1] at hys
        have F := hC.cfam y hy hys
        obtain ⟨-, h2, h3, h4, h5⟩ := hfam y hy hys
        have ol := R.old _ F.lLive.2 h2
        have or' := R.old _ F.rLive.2 h3
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [o.2.2.2.2.1, hLC]; exact Or.inl F.lLive
        · rw [o.2.2.2.2.2, hLC]; exact Or.inl F.rLive
        · rw [o.2.2.2.2.1, R.next _ F.lLive.2 h2 h4]; exact F.lAdj
        · rw [R.next _ hy.2 hyx h5, o.2.2.2.2.2]; exact F.rAdj
        · rw [o.2.2.2.2.1, ol.2.2.1]; exact F.lSt
        · rw [o.2.2.2.2.1, ol.2.2.2.1]; exact F.lSrc
        · rw [o.2.2.2.2.2, or'.2.2.1]; exact F.rSt
        · rw [o.2.2.2.2.2, or'.2.2.2.1]; exact F.rSrc
    · rw [(R.new y hyn).2.2.1] at hys; cases hys
  · -- overflow chunks
    intro d hd hds
    rcases (hLC d).mp hd with hd | hdn
    · have hdx : d ≠ x := by intro e; rw [e, R.xs.2.2.1] at hds; cases hds
      have o := R.old d hd.2 hdx
      rw [o.2.2.1] at hds
      obtain ⟨p1, p2, p3⟩ := hC.covf d hd hds
      have hsx := (hfam _ p1 p2).1
      have os := R.old _ p1.2 hsx
      rw [o.2.2.2.1, hLC, os.2.2.1, os.2.2.2.2.1, os.2.2.2.2.2]
      exact ⟨Or.inl p1, p2, p3⟩
    · rw [(R.new d hdn).2.2.2, hLC, R.xs.2.2.1, R.xs.2.2.2.1, R.xs.2.2.2.2]
      refine ⟨Or.inl hxL, rfl, ?_⟩
      rcases hdn with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · -- groups
    intro g hg'
    rw [hLv] at hg'
    rw [eC, hLC]
    obtain ⟨g1, g2⟩ := hC.gchk g hg'
    refine ⟨Or.inl g1, ?_⟩
    by_cases hgx : gC s g = x
    · rw [hgx, R.xs.2.2.1]; simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    · rw [(R.old _ g1.2 hgx).2.2.1]; exact g2
  · -- C1
    intro y hy hys _
    rcases (hLC y).mp hy with hy | hyn
    · by_cases hyx : y = x
      · subst hyx
        unfold C1
        obtain ⟨hsz, -, -, hl, hr⟩ := R.xs
        rw [hl, hr, hsz, (R.new _ (Or.inl rfl)).1, (R.new _ (Or.inr rfl)).1, Function.update_self,
          hunits, R.P]
        simp only [Nat.sub_zero, Nat.zero_add, Nat.add_zero, Nat.sub_self, Nat.mul_zero]
        exact ⟨hT, le_rfl, hun, Nat.zero_le _, Nat.zero_le _⟩
      · have o := R.old y hy.2 hyx
        rw [o.2.2.1] at hys
        have h := hC.c1 y hy hys (by unfold NIL; have := hy.1; omega)
        obtain ⟨-, h2, h3, -, -⟩ := hfam y hy hys
        have F := hC.cfam y hy hys
        unfold C1 at h ⊢
        rw [o.2.2.2.2.1, o.2.2.2.2.2, (R.old _ F.lLive.2 h2).1, o.1, (R.old _ F.rLive.2 h3).1,
          Function.update_of_ne hyx, hunits, R.P]
        exact h
    · rw [(R.new y hyn).2.2.1] at hys; cases hys

end OrderMaintenance.Proof
