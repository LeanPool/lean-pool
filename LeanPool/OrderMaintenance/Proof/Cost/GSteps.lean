/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Groups


/-!
# Group steps, field by field

What `startGroupSplit`, a split move and group removal do to the group records, in a form
that the cost invariants (groups here, chunks later) can use directly.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Starting a split -/

section start
variable (s : Core) (g labL labR : Nat)

/-- The two groups a split start allocates. -/
def splitL : Nat := (allocGroup s (gC s g)).1
/-- The second fresh group allocated when a split starts. -/
def splitR : Nat := (allocGroup (allocGroup s (gC s g)).2 (gC s g)).1

/-- The state after a split start with labels `labL`, `labR`. -/
def splitState : Core :=
  linkGroupPair (allocGroup (allocGroup s (gC s g)).2 (gC s g)).2 g (splitL s g) (splitR s g)
    labL labR

end start

theorem startGroupSplit_ok {s : Core} {g labL labR : Nat} (hg : LiveG s g)
    (hL : (labBefore g).run s = .ok labL s) (hR : (labAfter g).run s = .ok labR s) :
    (startGroupSplit g).run s = .ok () (splitState s g labL labR) := by
  obtain ⟨h0, hs, ha⟩ := hg
  unfold startGroupSplit
  simp only [run_getG_bind, run_get_bind, run_require_bind]
  have hc : (g != NIL && decide (g < s.Gs.size) && (s.Gs.getX g).alive) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]; exact ⟨⟨h0, hs⟩, ha⟩
  rw [ite_eq_left hc, run_bind, hL]
  simp only
  rw [run_bind, hR]
  simp [splitState, splitL, splitR, gC]

section link
variable {s : Core} {g gl gr labL labR : Nat}

theorem linkGroupPair_gSz (z : Nat) : gSz (linkGroupPair s g gl gr labL labR) z = gSz s z := by
  simp only [linkGroupPair, gSz, Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite, apply_ite (f := Group.size)]
  split_ifs <;> rfl

/-- A field that `linkGroupPair` sets only at `g`, `gl` and `gr`. -/
theorem LinkOK.field {β : Type} (h : LinkOK s g gl gr) (F : Group → β) (z : Nat)
    (hn : ∀ X v, F { X with next := v } = F X) (hp : ∀ X v, F { X with prev := v } = F X) :
    F ((linkGroupPair s g gl gr labL labR).Gs.getX z) =
      if z = g then F { s.Gs.getX g with prev := gl, next := gr, st := .splitting, l := gl, r :=
        gr }
      else if z = gl then
        F { s.Gs.getX gl with lab := labL, st := .overflow, src := g, prev := gP s g, next := g }
      else if z = gr then
        F { s.Gs.getX gr with lab := labR, st := .overflow, src := g, prev := g, next := gN s g }
      else F (s.Gs.getX z) := by
  obtain ⟨szl, szr, szg, szp, szn, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := h
  simp only [gN, gP] at *
  generalize hp' : (s.Gs.getX g).prev = p at *
  generalize hn' : (s.Gs.getX g).next = n at *
  simp only [linkGroupPair, hp', hn', Array.getX_modify, Array.getX_ite, Array.size_modify',
    Array.size_ite]
  by_cases hzg : z = g
  · subst hzg; simp [szg, d2, d3,   d8, d9, ]
  · by_cases hzl : z = gl
    · subst hzl
      simp [szl,  Ne.symm d1, d2, Ne.symm d2, d4, d6,  ]
    · by_cases hzr : z = gr
      · subst hzr
        simp [szr, d1, Ne.symm d1, d3, Ne.symm d3, d5, d7,   ]
      · simp only [hzg, hzl, hzr, ite_false, Ne.symm hzg, Ne.symm hzl, Ne.symm hzr, false_and]
        split_ifs
        all_goals first
          | rfl
          | exact hn _ _
          | exact hp _ _
          | exact (hn { s.Gs.getX z with prev := gr } gl).trans (hp _ gr)

end link

/-- The group records after a split start. -/
structure SplitSpec (s s' : Core) (g gl gr labL labR : Nat) : Prop where
  glOut : ¬ LiveG s gl
  grOut : ¬ LiveG s gr
  glr : gl ≠ gr
  gl0 : gl ≠ NIL
  gr0 : gr ≠ NIL
  ggl : g ≠ gl
  ggr : g ≠ gr
  Gsize : s.Gs.size ≤ s'.Gs.size
  live : ∀ z, LiveG s' z ↔ z = gl ∨ z = gr ∨ LiveG s z
  sz : ∀ z, gSz s' z = if z = gl ∨ z = gr then 0 else gSz s z
  st : ∀ z, gSt s' z = if z = g then .splitting else if z = gl ∨ z = gr then .overflow else gSt s z
  src : ∀ z, gSrc s' z = if z = gl ∨ z = gr then g else gSrc s z
  l : ∀ z, gLl s' z = if z = g then gl else if z = gl ∨ z = gr then NIL else gLl s z
  r : ∀ z, gRr s' z = if z = g then gr else if z = gl ∨ z = gr then NIL else gRr s z
  chk : ∀ z, gC s' z = if z = gl ∨ z = gr then gC s g else gC s z
  next : ∀ z, gN s' z = if z = g then gr else if z = gl then g else if z = gr then gN s g
      else if z = gP s g ∧ gP s g ≠ NIL then gl else gN s z
  prev : ∀ z, gP s' z = if z = g then gl else if z = gl then gP s g else if z = gr then g
      else if z = gN s g ∧ gN s g ≠ NIL then gr else gP s z
  lab : ∀ z, gL s' z = if z = gl then labL else if z = gr then labR else gL s z
  E : s'.E = s.E
  head : s'.head = s.head
  P : s'.P = s.P
  C : ∀ z, s'.C.getX z = if z = gC s g then
      { s.C.getX z with first := if cF s (gC s g) = g then gl else cF s (gC s g),
                        last := if cLs s (gC s g) = g then gr else cLs s (gC s g) } else s.C.getX z
  Csize : s'.C.size = s.C.size

theorem splitSpec {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist)
    (labL labR : Nat) :
    SplitSpec s (splitState s g labL labR) g (splitL s g) (splitR s g) labL labR := by
  unfold splitState splitL splitR
  have hg0 : g ≠ NIL := fun e => hI.gList.nonil (e ▸ hg)
  obtain ⟨hc, hgc⟩ := hI.mem_glist hg
  generalize hcdef : gC s g = c at hc hgc
  have hF := hI.freeOK
  obtain ⟨al1, al2, al3, al4, al5, al6, al7, al8, hF1, al10, alE, alC, alH, alT, alFG, alFC,
    alS1, alS2⟩ := allocGroup_spec hF c
  have alP := allocGroup_P s c
  generalize hp1 : allocGroup s c = p1 at *
  obtain ⟨gl, s1⟩ := p1
  simp only at al1 al2 al3 al4 al5 al6 al7 al8 hF1 al10 alE alC alH alT alFG alFC alS1 alS2 alP
  obtain ⟨bl1, bl2, bl3, bl4, bl5, bl6, bl7, bl8, hF2, bl10, blE, blC, blH, blT, blFG, blFC,
    blS1, blS2⟩ := allocGroup_spec hF1 c
  have blP := allocGroup_P s1 c
  generalize hp2 : allocGroup s1 c = p2 at *
  obtain ⟨gr, s2⟩ := p2
  simp only at bl1 bl2 bl3 bl4 bl5 bl6 bl7 bl8 hF2 bl10 blE blC blH blT blFG blFC blS1 blS2 blP
  have hglr : gl ≠ gr := bl10 gl al3 al6
  have hggl : g ≠ gl := fun e => al1 (e ▸ hg)
  have hggr : g ≠ gr := fun e => bl1 (e ▸ hg)
  have hs2G : ∀ z, z ≠ gl → z ≠ gr → s2.Gs.getX z = s.Gs.getX z := by
    intro z h1 h2; rw [bl5 z h2, al5 z h1]
  have hs2gl : s2.Gs.getX gl = { chk := c } := by rw [bl5 gl hglr, al4]
  have hs2gr : s2.Gs.getX gr = { chk := c } := bl4
  have hsz12 : s.Gs.size ≤ s2.Gs.size := le_trans al7 bl7
  generalize hpdef : gP s g = p
  generalize hndef : gN s g = n
  have hp2 : gP s2 g = p := by simp only [gP, hs2G g hggl hggr]; exact hpdef
  have hn2 : gN s2 g = n := by simp only [gN, hs2G g hggl hggr]; exact hndef
  have hpm : p = NIL ∨ p ∈ A.glist := hpdef ▸ hI.gP_mem hg
  have hnm : n = NIL ∨ n ∈ A.glist := hndef ▸ hI.gN_mem hg
  have hgl0 : gl ≠ NIL := by unfold NIL; omega
  have hgr0 : gr ≠ NIL := by unfold NIL; omega
  have hpgl : p ≠ gl := by
    rcases hpm with h | h <;> intro e <;> [exact hgl0 (e ▸ h); exact al1 (e ▸ h)]
  have hpgr : p ≠ gr := by
    rcases hpm with h | h <;> intro e <;> [exact hgr0 (e ▸ h); exact bl1 (e ▸ h)]
  have hngl : n ≠ gl := by
    rcases hnm with h | h <;> intro e <;> [exact hgl0 (e ▸ h); exact al1 (e ▸ h)]
  have hngr : n ≠ gr := by
    rcases hnm with h | h <;> intro e <;> [exact hgr0 (e ▸ h); exact bl1 (e ▸ h)]
  have hpg : p ≠ g := by
    rw [← hpdef, hI.gList.prev g hg]; exact predOf_ne_self hI.gList.nodup g hg0
  have hng : n ≠ g := by
    rw [← hndef, hI.gList.next g hg]; exact succOf_ne_self hI.gList.nodup g hg0
  have hpn : p ≠ NIL → p ≠ n := by
    intro h0; rw [← hpdef, ← hndef, hI.gList.prev g hg, hI.gList.next g hg]
    exact predOf_ne_succOf hI.gList.nodup hg (by rw [← hI.gList.prev g hg, hpdef]; exact h0)
  have hLink : LinkOK s2 g gl gr := by
    refine ⟨by omega, bl3, by have := hI.gAlloc g hg; omega, fun h => ?_, fun h => ?_, hglr,
      Ne.symm hggl, Ne.symm hggr, by rw [hp2]; exact hpgl, by rw [hp2]; exact hpgr,
      by rw [hn2]; exact hngl, by rw [hn2]; exact hngr, by rw [hp2]; exact hpg,
      by rw [hn2]; exact hng, fun h => by rw [hp2, hn2] at *; exact hpn h⟩
    · rw [hp2] at h ⊢
      rcases hpm with h' | h'
      · exact absurd h' h
      · have := hI.gAlloc p h'; omega
    · rw [hn2] at h ⊢
      rcases hnm with h' | h'
      · exact absurd h' h
      · have := hI.gAlloc n h'; omega
  obtain ⟨rE, rCs, rF, rH, rT, rFC, rFG⟩ := linkGroupPair_rest (s := s2) (g := g) (gl := gl)
    (gr := gr) (labL := labL) (labR := labR)
  have hGs' : (linkGroupPair s2 g gl gr labL labR).Gs.size = s2.Gs.size := linkGroupPair_Gsize
  have hglOut : ¬ LiveG s gl := fun h => al1 ((hI.mem_glist_iff).mpr h)
  have hgrOut : ¬ LiveG s gr := fun h => bl1 ((hI.mem_glist_iff).mpr h)
  have hfield : ∀ {β : Type} (F : Group → β), (∀ X v, F { X with next := v } = F X) →
      (∀ X v, F { X with prev := v } = F X) → ∀ z,
      F ((linkGroupPair s2 g gl gr labL labR).Gs.getX z) =
        if z = g then F { s.Gs.getX g with prev := gl, next := gr, st := .splitting, l := gl, r
          := gr }
        else if z = gl then
          F ({ chk := c, lab := labL, st := .overflow, src := g, prev := p, next := g } : Group)
        else if z = gr then
          F ({ chk := c, lab := labR, st := .overflow, src := g, prev := g, next := n } : Group)
        else F (s.Gs.getX z) := by
    intro β F hn hp z
    rw [hLink.field F z hn hp, hs2G g hggl hggr, hs2gl, hs2gr, hp2, hn2]
    by_cases h1 : z = g; · simp [h1]
    by_cases h2 : z = gl; · simp [ h2]
    by_cases h3 : z = gr; · simp [  h3]
    simp [h1, h2, h3, hs2G z h2 h3]
  refine
    { glOut := hglOut, grOut := hgrOut, glr := hglr, gl0 := hgl0, gr0 := hgr0, ggl := hggl,
      ggr := hggr, Gsize := by rw [hGs']; exact hsz12, live := ?_, sz := ?_, st := ?_, src := ?_,
      l := ?_, r := ?_, chk := ?_, next := ?_, prev := ?_, lab := ?_, E := by rw [rE, blE, alE],
      head := by rw [rH, blH, alH], P := by rw [← alP, ← blP]; rfl, C := ?_,
      Csize := by rw [rCs, blC, alC] }
  · intro z
    simp only [LiveG, gA, hGs']
    rw [hfield Group.alive (fun _ _ => rfl) (fun _ _ => rfl) z]
    by_cases h1 : z = g
    · subst h1; simp only [ne_eq, hg0, not_false_eq_true, ↓reduceIte, true_and, hggl, hggr,
        false_or, and_congr_left_iff]; have := hI.gAlloc z hg; intro _; constructor <;> intro
      <;> omega
    by_cases h2 : z = gl
    · subst h2; simp [h1, hgl0]; omega
    by_cases h3 : z = gr
    · subst h3; simp [h1, h2, hgr0, bl3]
    simp only [h1, h2, h3, ite_false, false_or]
    constructor
    · rintro ⟨a1, a2, a3⟩
      refine ⟨a1, ?_, a3⟩
      by_contra hge; push Not at hge
      by_cases hb1' : z < s1.Gs.size
      · have := alS2 (by omega); omega
      · have := blS2 (by omega); omega
    · rintro ⟨a1, a2, a3⟩; exact ⟨a1, by omega, a3⟩
  · intro z
    rw [gSz, hfield Group.size (fun _ _ => rfl) (fun _ _ => rfl) z]
    by_cases h1 : z = g; · simp [h1, hggl, hggr]
    by_cases h2 : z = gl; · simp [ h2, Ne.symm hggl]
    by_cases h3 : z = gr; · simp [  h3, Ne.symm hggr]
    simp [h1, h2, h3]
  · intro z
    rw [gSt, hfield Group.st (fun _ _ => rfl) (fun _ _ => rfl) z]
    by_cases h1 : z = g; · simp [h1]
    by_cases h2 : z = gl; · simp [ h2, Ne.symm hggl]
    by_cases h3 : z = gr; · simp [  h3, Ne.symm hggr]
    simp [h1, h2, h3]
  · intro z
    rw [gSrc, hfield Group.src (fun _ _ => rfl) (fun _ _ => rfl) z]
    by_cases h1 : z = g; · simp [h1, hggl, hggr]
    by_cases h2 : z = gl; · simp [ h2, Ne.symm hggl]
    by_cases h3 : z = gr; · simp [  h3, Ne.symm hggr]
    simp [h1, h2, h3]
  · intro z
    rw [gLl, hfield Group.l (fun _ _ => rfl) (fun _ _ => rfl) z]
    by_cases h1 : z = g; · simp [h1]
    by_cases h2 : z = gl; · simp [ h2, Ne.symm hggl]
    by_cases h3 : z = gr; · simp [  h3, Ne.symm hggr]
    simp [h1, h2, h3]
  · intro z
    rw [gRr, hfield Group.r (fun _ _ => rfl) (fun _ _ => rfl) z]
    by_cases h1 : z = g; · simp [h1]
    by_cases h2 : z = gl; · simp [ h2, Ne.symm hggl]
    by_cases h3 : z = gr; · simp [  h3, Ne.symm hggr]
    simp [h1, h2, h3]
  · intro z
    rw [gC, hfield Group.chk (fun _ _ => rfl) (fun _ _ => rfl) z]
    by_cases h1 : z = g; · simp [h1, hggl, hggr]
    by_cases h2 : z = gl; · simp [ h2, Ne.symm hggl, ← hcdef]
    by_cases h3 : z = gr; · simp [  h3, Ne.symm hggr, ← hcdef]
    simp [h1, h2, h3]
  · intro z
    rw [hLink.gN' z, hp2, hn2, hpdef, hndef]
    by_cases h1 : z = g; · simp [h1]
    by_cases h2 : z = gl; · simp [h2, hggl.symm]
    by_cases h3 : z = gr; · simp [h3, hggr.symm, hglr.symm]
    simp only [h1, h2, h3, ite_false]
    split_ifs <;> simp [gN, hs2G z h2 h3]
  · intro z
    rw [hLink.gP' z, hp2, hn2, hpdef, hndef]
    by_cases h1 : z = g; · simp [h1]
    by_cases h2 : z = gl; · simp [h2, hggl.symm]
    by_cases h3 : z = gr; · simp [h3, hggr.symm, hglr.symm]
    simp only [h1, h2, h3, ite_false]
    split_ifs <;> simp [gP, hs2G z h2 h3]
  · intro z
    rw [hLink.gL' z]
    by_cases h2 : z = gl; · simp [h2]
    by_cases h3 : z = gr; · simp [h3, hglr.symm]
    simp [h2, h3, gL, hs2G z h2 h3]
  · intro z
    have hcs : c < s.C.size := ((hI.cAlloc c).mp hc).2
    have hgc' : (s.Gs.getX g).chk = c := hcdef
    have := linkGroupPair_C (s := s2) (g := g) (gl := gl) (gr := gr) (labL := labL)
      (labR := labR) z (by simp only [gC, hs2G g hggl hggr, blC, alC, hgc']; exact hcs)
    simp only [gC, hs2G g hggl hggr, blC, alC, cF, cLs, hgc'] at this
    simp only [gC, cF, cLs, hgc']
    exact this

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Neighbours in the group list -/

theorem INV.gN_gP {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist)
    (hp : gP s g ≠ NIL) : gN s (gP s g) = g := by
  have hnd := hI.gList.nodup
  obtain ⟨l1, l2, e⟩ := predOf_split (hI.gList.prev g hg).symm hp
  have hm : gP s g ∈ A.glist := by rw [e]; simp
  rw [hI.gList.next _ hm, e, succOf_mid (e ▸ hnd)]; rfl

theorem INV.gP_gN {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist)
    (hn : gN s g ≠ NIL) : gP s (gN s g) = g := by
  have hnd := hI.gList.nodup
  obtain ⟨l1, l2, e⟩ := succOf_split (hI.gList.next g hg).symm hn
  have hm : gN s g ∈ A.glist := by rw [e]; simp
  have e' : A.glist = (l1 ++ [g]) ++ gN s g :: l2 := by rw [e]; simp
  rw [hI.gList.prev _ hm, e', predOf_mid (e' ▸ hnd)]; simp

theorem INV.runOf_dead {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : ¬ LiveG s g) :
    runOf s A.elist g = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro e he
  obtain ⟨h1, rfl⟩ := mem_runOf.mp he
  exact hg (hI.mem_glist_iff.mp (hI.eG_mem h1))

/-! ### `GInv` across a split start -/

/-- Fresh ghost counters for the two new groups. -/
def GGh.reset (gh : GGh) (a b : Nat) : GGh where
  hv z := if z = a ∨ z = b then 0 else gh.hv z
  pb z := if z = a ∨ z = b then 0 else gh.pb z
  pf z := if z = a ∨ z = b then 0 else gh.pf z

/-- A split leaves the records of every other live group unchanged. -/
theorem SplitSpec.group_fields_of_ne {s s' : Core} {g gl gr labL labR z : Nat}
    (S : SplitSpec s s' g gl gr labL labR) (hz : LiveG s z) (hzg : z ≠ g) :
    gSt s' z = gSt s z ∧ gSrc s' z = gSrc s z ∧ gLl s' z = gLl s z ∧
      gRr s' z = gRr s z ∧ gSz s' z = gSz s z ∧ gC s' z = gC s z := by
  have h : ¬ (z = gl ∨ z = gr) :=
    not_or.mpr ⟨fun e => S.glOut (e ▸ hz), fun e => S.grOut (e ▸ hz)⟩
  exact ⟨by rw [S.st, ite_eq_right hzg, ite_eq_right h], by rw [S.src, ite_eq_right h],
    by rw [S.l, ite_eq_right hzg, ite_eq_right h], by rw [S.r, ite_eq_right hzg, ite_eq_right h],
    by rw [S.sz, ite_eq_right h], by rw [S.chk, ite_eq_right h]⟩

/-- A split preserves the element run of every group. -/
theorem SplitSpec.runOf_eq {s s' : Core} {g gl gr labL labR : Nat}
    (S : SplitSpec s s' g gl gr labL labR) (elements : List Nat) (z : Nat) :
    runOf s' elements z = runOf s elements z := by
  unfold runOf
  simp only [eG, S.E]

theorem ginv_splitStart {s : Core} {A : Abs} {gh : GGh} {g : Nat} (hI : INV s A)
    (hG : GInv s A.elist gh (fun b => if b = g then 1 else 0)) (hg : LiveG s g)
    (hq : gSt s g = .quiet) (hsz : s.P.G ≤ gSz s g) (labL labR : Nat) :
    GInv (splitState s g labL labR) A.elist (gh.reset (splitL s g) (splitR s g)) (fun _ => 0) := by
  have hgl := hI.mem_glist_iff.mpr hg
  have S := splitSpec hI hgl labL labR
  generalize splitState s g labL labR = s' at S ⊢
  generalize splitL s g = gl at S ⊢
  generalize splitR s g = gr at S ⊢
  have hRun := S.runOf_eq A.elist
  have hEL : eL s' = eL s := by funext e; simp only [eL, S.E]
  have hP := S.P
  have hgG : gSz s g = s.P.G := by
    have := (hG.quiet g hg hq).1; simp at this; omega
  -- live groups of `s` other than `g` keep their records
  have hne : ∀ z, LiveG s z → z ≠ gl ∧ z ≠ gr := fun z hz =>
    ⟨fun e => S.glOut (e ▸ hz), fun e => S.grOut (e ▸ hz)⟩
  have hδ0 : ∀ z, gSt s z ≠ .quiet → (if z = g then 1 else 0) = 0 := by
    intro z hz; rw [ite_eq_right]; rintro rfl; exact hz hq
  have hgP : ∀ z, gN s z ≠ g → ¬ (z = gP s g ∧ gP s g ≠ NIL) := by
    rintro z hz ⟨rfl, hp⟩; exact hz (hI.gN_gP hgl hp)
  have hfam' : ∀ p, LiveG s p → gSt s p = .splitting → famT s' p = famT s p := by
    intro p hp hs
    have hpg : p ≠ g := by rintro rfl; rw [hq] at hs; cases hs
    have := hne p hp
    have F := hG.fam p hp hs
    simp only [famT, S.sz, S.l, S.r, ite_eq_right hpg, ite_eq_right (not_or.mpr this),
      ite_eq_right (not_or.mpr (hne _ F.lLive)), ite_eq_right (not_or.mpr (hne _ F.rLive))]
  have hgglr : ¬ (g = gl ∨ g = gr) := not_or.mpr ⟨S.ggl, S.ggr⟩
  have hoth : ∀ z, LiveG s z → z ≠ g → gSt s' z = gSt s z ∧ gSrc s' z = gSrc s z ∧
      gLl s' z = gLl s z ∧ gRr s' z = gRr s z ∧ gSz s' z = gSz s z ∧ gC s' z = gC s z :=
    fun _ hz hzg => S.group_fields_of_ne hz hzg
  have hgf : gSt s' g = .splitting ∧ gLl s' g = gl ∧ gRr s' g = gr ∧ gSz s' g = gSz s g ∧
      gC s' g = gC s g := by
    refine ⟨by rw [S.st, ite_eq_left rfl], by rw [S.l, ite_eq_left rfl], by rw [S.r, ite_eq_left
      rfl],
      by rw [S.sz, ite_eq_right hgglr], by rw [S.chk, ite_eq_right hgglr]⟩
  have hlr : ∀ z, z = gl ∨ z = gr → gSt s' z = .overflow ∧ gSrc s' z = g ∧ gSz s' z = 0 ∧
      gC s' z = gC s g := by
    intro z hz
    have hzg : z ≠ g := by rcases hz with rfl | rfl <;> [exact Ne.symm S.ggl; exact Ne.symm S.ggr]
    exact ⟨by rw [S.st, ite_eq_right hzg, ite_eq_left hz], by rw [S.src, ite_eq_left hz], by rw
      [S.sz, ite_eq_left hz],
      by rw [S.chk, ite_eq_left hz]⟩
  have hfamg : famT s' g = s.P.G := by
    simp only [famT, hgf.2.1, hgf.2.2.1, hgf.2.2.2.1, (hlr gl (Or.inl rfl)).2.2.1,
      (hlr gr (Or.inr rfl)).2.2.1, hgG]; omega
  have hLg' : LiveG s' gl := (S.live gl).mpr (Or.inl rfl)
  have hRg' : LiveG s' gr := (S.live gr).mpr (Or.inr (Or.inl rfl))
  have hgg' : LiveG s' g := (S.live g).mpr (Or.inr (Or.inr hg))
  -- an old family survives intact
  have hoFam : ∀ p, LiveG s p → gSt s p = .splitting → FamOK s' p := by
    intro p hp hs
    have hpg : p ≠ g := by rintro rfl; rw [hq] at hs; cases hs
    have F := hG.fam p hp hs
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hoth p hp hpg
    have hlg : gLl s p ≠ g := by intro e; have := F.lSt; rw [e, hq] at this; cases this
    have hrg : gRr s p ≠ g := by intro e; have := F.rSt; rw [e, hq] at this; cases this
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hoth _ F.lLive hlg
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hoth _ F.rLive hrg
    have hlne := hne _ F.lLive
    have hrne := hne _ F.rLive
    have hpne := hne _ hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o3]; exact (S.live _).mpr (Or.inr (Or.inr F.lLive))
    · rw [o4]; exact (S.live _).mpr (Or.inr (Or.inr F.rLive))
    · rw [o3, S.next, ite_eq_right hlg, ite_eq_right hlne.1, ite_eq_right hlne.2,
        ite_eq_right (hgP _ (by rw [F.lAdj]; exact hpg))]
      exact F.lAdj
    · rw [o4, S.next, ite_eq_right hpg, ite_eq_right hpne.1, ite_eq_right hpne.2,
        ite_eq_right (hgP _ (by rw [F.rAdj]; exact hrg))]
      exact F.rAdj
    · rw [o3, l1]; exact F.lSt
    · rw [o3, l2]; exact F.lSrc
    · rw [o4, r1]; exact F.rSt
    · rw [o4, r2]; exact F.rSrc
    · rw [o3, l6, o6]; exact F.lC
    · rw [o4, r6, o6]; exact F.rC
  refine
    { sz := ?_, fam := ?_, ovf := ?_, notDead := ?_, quiet := ?_, split := ?_, gaps := ?_,
      range := ?_, ghQ := ?_, ghO := ?_, ghS := ?_ }
  · intro z hz
    rw [hRun]
    rcases (S.live z).mp hz with h | h | h
    · rw [S.sz, ite_eq_left (Or.inl h), hI.runOf_dead (h ▸ S.glOut)]; rfl
    · rw [S.sz, ite_eq_left (Or.inr h), hI.runOf_dead (h ▸ S.grOut)]; rfl
    · rw [S.sz, ite_eq_right (not_or.mpr (hne z h))]; exact hG.sz z h
  · intro z hz hs
    rcases (S.live z).mp hz with h | h | h
    · rw [(hlr z (Or.inl h)).1] at hs; cases hs
    · rw [(hlr z (Or.inr h)).1] at hs; cases hs
    by_cases hzg : z = g
    · subst hzg
      refine ⟨by rw [hgf.2.1]; exact hLg', by rw [hgf.2.2.1]; exact hRg', ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
      · rw [hgf.2.1, S.next, ite_eq_right (Ne.symm S.ggl), ite_eq_left rfl]
      · rw [hgf.2.2.1, S.next, ite_eq_left rfl]
      · rw [hgf.2.1]; exact (hlr gl (Or.inl rfl)).1
      · rw [hgf.2.1]; exact (hlr gl (Or.inl rfl)).2.1
      · rw [hgf.2.2.1]; exact (hlr gr (Or.inr rfl)).1
      · rw [hgf.2.2.1]; exact (hlr gr (Or.inr rfl)).2.1
      · rw [hgf.2.1, (hlr gl (Or.inl rfl)).2.2.2, hgf.2.2.2.2]
      · rw [hgf.2.2.1, (hlr gr (Or.inr rfl)).2.2.2, hgf.2.2.2.2]
    · rw [(hoth z h hzg).1] at hs
      exact hoFam z h hs
  · intro z hz hs
    rcases (S.live z).mp hz with h | h | h
    · rw [(hlr z (Or.inl h)).2.1]
      exact ⟨hgg', hgf.1, Or.inl (by rw [hgf.2.1, h])⟩
    · rw [(hlr z (Or.inr h)).2.1]
      exact ⟨hgg', hgf.1, Or.inr (by rw [hgf.2.2.1, h])⟩
    have hzg : z ≠ g := by rintro rfl; rw [hgf.1] at hs; cases hs
    obtain ⟨o1, o2, o3, o4, -, -⟩ := hoth z h hzg
    rw [o1] at hs
    obtain ⟨p1, p2, p3⟩ := hG.ovf z h hs
    have hpg : gSrc s z ≠ g := by intro e; rw [e, hq] at p2; cases p2
    obtain ⟨q1, -, q3, q4, -, -⟩ := hoth _ p1 hpg
    rw [o2, q1, q3, q4]
    exact ⟨(S.live _).mpr (Or.inr (Or.inr p1)), p2, p3⟩
  · intro z hz
    rcases (S.live z).mp hz with h | h | h
    · rw [(hlr z (Or.inl h)).1]; simp
    · rw [(hlr z (Or.inr h)).1]; simp
    by_cases hzg : z = g
    · subst hzg; rw [hgf.1]; simp
    · rw [(hoth z h hzg).1]; exact hG.notDead z h
  · intro z hz hs
    rcases (S.live z).mp hz with h | h | h
    · rw [(hlr z (Or.inl h)).1] at hs; cases hs
    · rw [(hlr z (Or.inr h)).1] at hs; cases hs
    have hzg : z ≠ g := by rintro rfl; rw [hgf.1] at hs; cases hs
    obtain ⟨o1, -, -, -, o5, -⟩ := hoth z h hzg
    rw [o1] at hs
    obtain ⟨q1, q2, q3⟩ := hG.quiet z h hs
    rw [o5, hP, S.head, hRun]
    exact ⟨by simpa [hzg] using q1, q2, q3⟩
  · intro z hz hs hzx
    rcases (S.live z).mp hz with h | h | h
    · rw [(hlr z (Or.inl h)).1] at hs; cases hs
    · rw [(hlr z (Or.inr h)).1] at hs; cases hs
    by_cases hzg : z = g
    · subst hzg
      unfold G1
      rw [hgf.2.1, hgf.2.2.1, hgf.2.2.2.1, (hlr gl (Or.inl rfl)).2.2.1,
        (hlr gr (Or.inr rfl)).2.2.1, hgG, hP]
      simp
    · obtain ⟨o1, -, o3, o4, o5, -⟩ := hoth z h hzg
      rw [o1] at hs
      have F := hG.fam z h hs
      have hlg : gLl s z ≠ g := by intro e; have := F.lSt; rw [e, hq] at this; cases this
      have hrg : gRr s z ≠ g := by intro e; have := F.rSt; rw [e, hq] at this; cases this
      have hG1 := hG.split z h hs hzx
      unfold G1 at hG1 ⊢
      rw [o3, o4, o5, (hoth _ F.lLive hlg).2.2.2.2.1, (hoth _ F.rLive hrg).2.2.2.2.1, hP]
      simpa [hzg, hlg, hrg] using hG1
  · intro z hz
    rw [hRun, hEL, hP]
    rcases (S.live z).mp hz with h | h | h
    · rw [hI.runOf_dead (h ▸ S.glOut)]; simp
    · rw [hI.runOf_dead (h ▸ S.grOut)]; simp
    · have : (gh.reset gl gr).hv z = gh.hv z := by
        simp [GGh.reset, (hne z h).1, (hne z h).2]
      rw [this]; exact hG.gaps z h
  · intro z hz e he
    rw [hRun] at he; rw [hEL, hP]
    rcases (S.live z).mp hz with h | h | h
    · rw [hI.runOf_dead (h ▸ S.glOut)] at he; simp at he
    · rw [hI.runOf_dead (h ▸ S.grOut)] at he; simp at he
    · simp only [GGh.reset, (hne z h).1, (hne z h).2, or_self, ite_false]
      exact hG.range z h e he
  · intro z hz hs
    rcases (S.live z).mp hz with h | h | h
    · rw [(hlr z (Or.inl h)).1] at hs; cases hs
    · rw [(hlr z (Or.inr h)).1] at hs; cases hs
    have hzg : z ≠ g := by rintro rfl; rw [hgf.1] at hs; cases hs
    obtain ⟨o1, -, -, -, o5, -⟩ := hoth z h hzg
    rw [o1] at hs
    simp only [GGh.reset, (hne z h).1, (hne z h).2, or_self, ite_false, o5, hP]
    exact hG.ghQ z h hs
  · intro z hz hs
    rcases (S.live z).mp hz with h | h | h
    · simp only [GGh.reset, h, true_or, ite_true, (hlr gl (Or.inl rfl)).2.1, hfamg, hP,
        (hlr gl (Or.inl rfl)).2.2.1]; omega
    · simp only [GGh.reset, h, or_true, ite_true, (hlr gr (Or.inr rfl)).2.1, hfamg, hP,
        (hlr gr (Or.inr rfl)).2.2.1]; omega
    have hzg : z ≠ g := by rintro rfl; rw [hgf.1] at hs; cases hs
    obtain ⟨o1, o2, -, -, o5, -⟩ := hoth z h hzg
    rw [o1] at hs
    obtain ⟨p1, p2, -⟩ := hG.ovf z h hs
    simp only [GGh.reset, (hne z h).1, (hne z h).2, or_self, ite_false, o5, hP, o2,
      hfam' _ p1 p2]
    exact hG.ghO z h hs
  · intro z hz hs
    rcases (S.live z).mp hz with h | h | h
    · rw [(hlr z (Or.inl h)).1] at hs; cases hs
    · rw [(hlr z (Or.inr h)).1] at hs; cases hs
    by_cases hzg : z = g
    · subst hzg
      have := hG.ghQ z h hq
      simp only [GGh.reset, (hne z h).1, (hne z h).2, or_self, ite_false, hfamg, hP]
      omega
    · obtain ⟨o1, -, -, -, -, -⟩ := hoth z h hzg
      rw [o1] at hs
      simp only [GGh.reset, (hne z h).1, (hne z h).2, or_self, ite_false, hP, hfam' z h hs]
      exact hG.ghS z h hs

end OrderMaintenance.Proof
