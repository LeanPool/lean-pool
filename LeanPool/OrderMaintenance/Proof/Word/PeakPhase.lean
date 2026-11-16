/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakChunk
public import LeanPool.OrderMaintenance.Impl.GlueCore
public import LeanPool.OrderMaintenance.Proof.Word.Hooks


/-!
# Theorem W, option (A), stage A2: the peak of the group drive, from the cost invariants

`ginv_drivePeak`: the drive of a splitting group (the context of `ginv_driveAgree`), whose
every step moves an element into a live sibling, of size at most `|L|` (`GInvE.sz`): with
`|L| + 2 ≤ 2^K`, every size it writes is below `2^K`.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof
open OrderMaintenance.Machine (Reg)

variable {K KH W : Nat} {κ : Caps}

/-- **The drive of a splitting group** (the context of `ginv_driveAgree`). -/
theorem ginv_drivePeak (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
    {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat}
    (hI : INV s A) (hXs : XSteps X Y A.elist δ p (gC s p)) (hX : X s)
    (hG : GInvE s A.elist gh δ p) (hP : GParams s.P) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hG1 : G1 s δ p)
    (hδ : ∀ z, z ≠ gLl s p → z ≠ p → z ≠ gRr s p → δ z = 0)
    (hδs : δ (gLl s p) + δ p + δ (gRr s p) ≤ 1)
    (hδle : δ (gLl s p) ≤ gSz s (gLl s p) ∧ δ p ≤ gSz s p ∧ δ (gRr s p) ≤ gSz s (gRr s p))
    (hXc : ∀ t, X t → ∀ g, LiveG t g → gC t g < t.C.size) (Kc : GCaps κ s)
    (hlen : A.elist.length + 2 ≤ 2 ^ K) {L : Loc} (hg : L "g" = p) (hGd : Gd K KH κ (ΓK K) s L) :
    PKok K KH κ (ΓK K) W driveGroupFromS s L := by
  generalize hl : gLl s p = l at *
  generalize hr : gRr s p = r at *
  generalize ha : gSz s l = a at *
  generalize hb : gSz s p = b at *
  generalize hc : gSz s r = c at *
  have hK2 := hP.K2
  have hI1 := hP.I1
  unfold G1 at hG1
  rw [hl, hr, ha, hb, hc] at hG1
  obtain ⟨g1, g2, g3, g4⟩ := hG1
  generalize hm : s.P.groupBudget - 1 = m at g2 hI1
  have hm1 : 1 ≤ m := by omega
  generalize hq : s.P.G / m = q at hI1
  have hXq : (a - δ l) + (b - δ p) + (c - δ r) - s.P.G ≤ q := by
    rw [← hq, Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
    have := Nat.le_add_left (m * ((a - δ l) + (b - δ p) + (c - δ r) - s.P.G)) (b - δ p)
    omega
  have hTlo : s.P.G ≤ a + b + c := by omega
  have hThi : a + b + c ≤ s.P.G + s.P.G / (s.P.groupBudget - 1) + 1 := by rw [hm, hq]; omega
  have hbal0 : a ≤ c + 2 ∧ c ≤ a + 2 := by omega
  let I' := fun j t => DriveInv X s A.elist δ p l r a b c j t ∧ t.Gs.size = s.Gs.size ∧ t.C.size
    = s.C.size
  have h0 : I' 0 s := ⟨⟨hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩, ⟨gh, hG⟩, hp, hs, hl, hr, by
    omega, by omega,
      Or.inl ⟨rfl, ha, hc⟩, rfl⟩, rfl, rfl⟩
  refine driveGroupFrom_pk hC hK hW I' h0 (fun j t ⟨hD, hGs, hCs⟩ hj => ?_) hGd hg
  have K' : GCaps κ t := Kc.of_sizes hGs hD.ef.size hCs
  obtain ⟨bb, t', hrun, hA, hG', hC', -⟩ := hD.stepAgree hXs hP hTlo
    hThi hbal0 (hXc t hD.x) K'
  obtain ⟨Lg, ng, eg, hok, -⟩ := hA (Machine.State.setLocs (fun _ => 0) ["g"] [p])
    (by
      simp [Machine.State.setLocs, Machine.State.upd])
  refine ⟨bb, t', Lg, ng, eg, hok, fun hbb => ?_, ?_⟩
  · subst hbb
    obtain ⟨t1, h1 | h1⟩ := hD.step hXs hP (by
      intro z h1 h2 h3
      exact hδ z h1 h2 h3) hTlo hThi hbal0
    · rw [h1.1] at hrun; injection hrun with _ e; subst e
      exact ⟨h1.2, hG'.trans hGs, hC'.trans hCs⟩
    · rw [h1.1] at hrun; injection hrun with e; cases e
  · -- the siblings are live, of size at most `|L|`
    intro z hz
    obtain ⟨A', hI', hel⟩ := hD.inv
    obtain ⟨gh', hGt⟩ := hD.ginv
    have Fp := hGt.fam p hD.live hD.st
    rcases hz with rfl | rfl
    · have := hGt.sz _ Fp.lLive; have := OrderMaintenance.Proof.Word.runOf_len_le t A.elist (gLl
        t p)
      simp only [gSz, gLl] at *; omega
    · have := hGt.sz _ Fp.rLive; have := OrderMaintenance.Proof.Word.runOf_len_le t A.elist (gRr
        t p)
      simp only [gSz, gRr] at *; omega

section phase
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- `driveGroup g`: the drive of the split `g` belongs to, if any. -/
theorem driveGroupS_pkok {g : Nat} (hG : Gd K KH κ (ΓK K) s L) (hgL : L "g" = g)
    (hD : ∀ q, ((s.Gs.getX g).st = .splitting ∧ q = g ∨ (s.Gs.getX g).st = .overflow ∧ q =
      (s.Gs.getX g).src) →
      ∀ L', L' "g" = q → Gd K KH κ (ΓK K) s L' → PKok K KH κ (ΓK K) W driveGroupFromS s L') :
    PKok K KH κ (ΓK K) W driveGroupS s L := by
  unfold driveGroupS
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by proveSafe) hG)) (fun s1 L1 n1
    h1 hG1 => ?_)
  obtain ⟨v, hv, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  obtain ⟨j, hj, hjc, rfl⟩ := Exp.ev_rd_inv hv
  simp only [Exp.ev, Option.some.injEq] at hj; subst hj
  have hLg : Machine.State.upd L "st" (Fld.get s (L "g") (.g .st)) "g" = g := by
    rw [upd_ne _ _ (by decide)]; exact hgL
  refine PKok.ite_ok hC hG1 (by proveSafe) (fun c hc hc0 => ?_) (fun hc => ?_)
  · have hst : (s.Gs.getX g).st = .splitting := by
      simp [Exp.ev, Machine.BinOp.eval,  Fld.get, GF.get] at hc
      rw [← hgL]
      by_contra hne
      have : (s.Gs.getX (L "g")).st.toN ≠ 2 := by
        cases h : (s.Gs.getX (L "g")).st <;> simp_all [St.toN]
      simp [this] at hc; exact hc0 hc.symm
    exact PKok.callS hC (Γe := ΓK K) hG1 (by proveSafe) (fun _ => le_refl K)
      (fun vs hvs hG0 => hD g (Or.inl ⟨hst, rfl⟩) _ (by
        simp only [evList, List.mapM_cons, Exp.ev, Machine.State.upd, String.reduceEq,
            ↓reduceIte, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
            Option.bind_some, Option.some.injEq] at hvs; subst hvs
        simp [driveP, Machine.State.setLocs, Machine.State.upd,
          hgL])
        hG0) (by simp [driveP]) (by simp)
  · refine PKok.ite_ok hC hG1 (by proveSafe) (fun c' hc' hc0' => ?_) (fun _ => PK.ok
      (PK.skip hG1))
    have hst : (s.Gs.getX g).st = .overflow := by
      simp [Exp.ev, Machine.BinOp.eval,  Fld.get, GF.get] at hc'
      rw [← hgL]
      by_contra hne
      have : (s.Gs.getX (L "g")).st.toN ≠ 1 := by
        cases h : (s.Gs.getX (L "g")).st <;> simp_all [St.toN]
      simp [this] at hc'; exact hc0' hc'.symm
    exact PKok.callS hC (Γe := ΓK K) hG1 (by proveSafe) (fun _ => le_refl K)
      (fun vs hvs hG0 => hD _ (Or.inr ⟨hst, rfl⟩) _ (by
        have hjc' : L "g" < κ.tbl .G := by simpa [Fld.cap] using hjc
        simp only [evList, Fld.get, GF.get, Exp.gF, List.mapM_cons, Exp.ev, Machine.State.upd,
            String.reduceEq, ↓reduceIte, Fld.cap, Option.bind_some, hjc', List.mapM_nil,
            Option.pure_def, Option.bind_eq_bind, Option.some.injEq] at hvs
        subst hvs
        simp [driveP, Machine.State.setLocs, Machine.State.upd,
          hgL])
        hG0) (by simp [driveP]) (by simp)

end phase

/-- **The drive of a group phase** (the context of `groupPhaseAgree`), from the state after the
split start, if any. -/
theorem groupPhasePeak (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
    {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {g : Nat} (hI : INV s A)
    (hXg : XGroup X Y A.elist (gC s g)) (hX : X s)
    (hG : GInv s A.elist gh (fun b => if b = g then 1 else 0)) (hP : GParams s.P)
    (hg : LiveG s g) (hpos : 1 ≤ gSz s g)
    (hroom : gSt s g = .quiet → s.P.G ≤ gSz s g → SplitRoom s g)
    (hXc : ∀ t, X t → ∀ g, LiveG t g → gC t g < t.C.size) (Kc : GCaps κ s) (hG2 : s.Gs.size + 2
      ≤ κ.tbl .G)
    {s1 : Core}
    (h1 : (if ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true then
      startGroupSplit g else pure ()).run s = .ok () s1)
    (hlen : A.elist.length + 2 ≤ 2 ^ K) {L1 : Loc} (hgL : L1 "g" = g) (hGd : Gd K KH κ (ΓK K) s1
      L1) :
    PKok K KH κ (ΓK K) W driveGroupS s1 L1 := by
  have hδle : ∀ p, (fun b => if b = g then 1 else 0) p ≤ gSz s p := by
    intro p; by_cases h : p = g
    · subst h; simp [hpos]
    · simp [h]
  refine driveGroupS_pkok hC hK hW hGd hgL (fun q hq L' hL' hG' => ?_)
  cases hst : gSt s g with
  | quiet =>
    by_cases hsz : s.P.G ≤ gSz s g
    · obtain ⟨labL, labR, hL, hR⟩ := hroom hst hsz
      have hc : ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
        simp only [gSt, gSz] at hst hsz; simp [hst, hsz]
      rw [ite_eq_left hc, startGroupSplit_ok hg hL hR] at h1
      injection h1 with _ e; subst e
      have hgG : gSz s g = s.P.G := by
        have := (hG.quiet g hg hst).1; simp at this; omega
      obtain ⟨hef1, A1, hI1, hel1⟩ := Good.ok_inv (good_startGroupSplit g) hI
        (startGroupSplit_ok hg hL hR)
      have hG1 := ginv_splitStart hI hG hg hst hsz labL labR
      have hX1 := hXg.split s A gh g labL labR hI rfl hG hg hst hgG hL hR hX
      have S := splitSpec hI (hI.mem_glist_iff.mpr hg) labL labR
      have hsz2 := splitState_size s g labL labR
      generalize splitState s g labL labR = s1 at hef1 hI1 hG1 hX1 S hsz2 hq hG' hGd ⊢
      generalize gh.reset (splitL s g) (splitR s g) = gh1 at hG1
      have hg1 : LiveG s1 g := (S.live g).mpr (Or.inr (Or.inr hg))
      have hs1 : gSt s1 g = .splitting := by rw [S.st, ite_eq_left rfl]
      rw [← hel1] at hG1
      have hP1 : GParams s1.P := by rw [S.P]; exact hP
      have hXd : XSteps X Y A1.elist (fun _ => 0) g (gC s1 g) := by
        rw [hel1, S.chk, ite_eq_right (not_or.mpr ⟨S.ggl, S.ggr⟩)]; exact hXg.drive _ g
      have K1 : GCaps κ s1 := ⟨by omega, by rw [S.E]; exact Kc.E, by rw [S.Csize]; exact Kc.C,
        Kc.fl, Kc.f0⟩
      rcases hq with ⟨-, hq'⟩ | ⟨h, -⟩
      · exact ginv_drivePeak hC hK hW hI1 hXd hX1 (hG1.weaken g) hP1 hg1 hs1 (hG1.split g hg1
          hs1 hg1.1)
          (fun _ _ _ _ => rfl) (by simp) (by simp) hXc K1 (by
            rw [hel1]
            exact hlen) (hq' ▸ hL') hG'
      · have hs1' : (s1.Gs.getX g).st = .splitting := hs1
        rw [hs1'] at h; cases h
    · have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
        simp only [gSt, gSz] at hst hsz; simp [hst]; omega
      rw [ite_eq_right hc] at h1
      injection h1 with _ e; subst e
      simp only [gSt] at hst
      rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hst] at h <;> cases h
  | overflow =>
    have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
      simp only [gSt] at hst; simp [hst]
    rw [ite_eq_right hc] at h1
    injection h1 with _ e; subst e
    obtain ⟨hp, hps, hlr⟩ := hG.ovf g hg hst
    have Fp := hG.fam _ hp hps
    have hgp : gSrc s g ≠ g := by intro e; rw [e, hst] at hps; cases hps
    have hlr0 : gLl s (gSrc s g) ≠ gRr s (gSrc s g) := Fp.lr hI hp
    have hδs : (fun b => if b = g then 1 else 0) (gLl s (gSrc s g)) +
        (fun b => if b = g then 1 else 0) (gSrc s g) +
        (fun b => if b = g then 1 else 0) (gRr s (gSrc s g)) ≤ 1 := by
      rcases hlr with e | e
      · have : gRr s (gSrc s g) ≠ g := fun h => hlr0 (e.trans h.symm)
        simp [e, hgp, this]
      · have : gLl s (gSrc s g) ≠ g := fun h => hlr0 (h.trans e.symm)
        simp [e, hgp, this]
    have hXd : XSteps X Y A.elist (fun b => if b = g then 1 else 0) (gSrc s g) (gC s (gSrc s g))
      := by
      rcases hlr with e | e
      · rw [← Fp.lC, e]; exact hXg.drive _ _
      · rw [← Fp.rC, e]; exact hXg.drive _ _
    rcases hq with ⟨h, -⟩ | ⟨-, hq'⟩
    · have hst' : (s.Gs.getX g).st = .overflow := hst
      rw [hst'] at h; cases h
    · exact ginv_drivePeak hC hK hW hI hXd hX (hG.weaken (gSrc s g)) hP hp hps (hG.split _ hp
        hps hp.1)
        (by intro z h1 h2 h3; have : z ≠ g := by
              rintro rfl; rcases hlr with e | e <;> [exact h1 e.symm; exact h3 e.symm]
            simp [this])
        hδs ⟨hδle _, hδle _, hδle _⟩ hXc Kc hlen (by rw [hL', hq']) hG'
  | splitting =>
    have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
      simp only [gSt] at hst; simp [hst]
    rw [ite_eq_right hc] at h1
    injection h1 with _ e; subst e
    have Fp := hG.fam g hg hst
    have hl0 : gLl s g ≠ g := Fp.lp hI hg
    have hr0 : gRr s g ≠ g := Fp.rp hI hg
    rcases hq with ⟨-, hq'⟩ | ⟨h, -⟩
    · exact ginv_drivePeak hC hK hW hI (hXg.drive _ _) hX (hG.weaken g) hP hg hst
        (hG.split g hg hst hg.1) (by
          intro z _ h2 _
          simp [h2]) (by simp [hl0, hr0])
        ⟨hδle _, hδle _, hδle _⟩ hXc Kc hlen (hq' ▸ hL') hG'
    · have hst' : (s.Gs.getX g).st = .splitting := hst
      rw [hst'] at h; cases h
  | dead => exact absurd hst (hG.notDead g hg)

/-- **The drive of a splitting chunk** (the context of `cinv_driveAgree`), with hooks that give
the stored-value bound of every state (`cxsteps_wb`). -/
theorem cinv_drivePeak (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
    {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {δ δu s₀ : Nat → Nat} {x : Nat}
    (hI : INV s A) (hG : GInv s A.elist gh (fun _ => 0)) (hCi : CInvE s A.elist δ δu s₀ x)
    (hC1 : C1 s δ δu s₀ x) (hXs : CXSteps X Y A.elist δ δu s₀ x) (hX : X s) (hP : GParams s.P)
    (hCP : CParams s.P) (hxL : LiveC s x) (hst : cSt s x = .splitting)
    (hδ : ∀ c, c ≠ cLl s x → c ≠ x → c ≠ cRr s x → δ c = 0)
    (hδs : δ (cLl s x) + δ x + δ (cRr s x) ≤ 1)
    (hδle : δ (cLl s x) ≤ cSz s (cLl s x) ∧ δ x ≤ cSz s x ∧ δ (cRr s x) ≤ cSz s (cRr s x))
    (Kc : GCaps κ s) (hXV : ∀ t, X t → FB K KH κ (.c .size) t) (hYV : ∀ t, Y t → FB K KH κ (.c
      .size) t)
    {L : Loc} (hgL : L "x" = x) (hGd : Gd K KH κ (ΓK K) s L) :
    PKok K KH κ (ΓK K) W driveChunkFromS s L := by
  have Fx := hCi.cfam x hxL hst
  generalize hl : cLl s x = y at *
  generalize hr : cRr s x = z at *
  generalize ha : cSz s y = a at *
  generalize hb : cSz s x = b at *
  generalize hc : cSz s z = c at *
  have hK2 := hCP.K2
  unfold C1 at hC1
  rw [hl, hr, ha, hb, hc] at hC1
  obtain ⟨hs0T, g1, g2, g3, g4⟩ := hC1
  generalize hσ : s₀ x = σ at hs0T g1 g2
  generalize hm : s.P.chunkBudget - 1 = m at g2
  have hm1 : 1 ≤ m := by omega
  generalize hX0 : (a - δ y) + (b - δ x) + (c - δ z) - σ = Xs at g2
  have hXq : Xs ≤ unitsOf s.P σ / m := by
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
    have := Nat.le_add_left (m * Xs) (units s x - δu x); omega
  have hU := unitsOf_mono s.P hs0T
  have hUd : unitsOf s.P σ / m ≤ unitsOf s.P s.P.T / m := Nat.div_le_div_right hU
  have hkC : kC s.P s.P.T = unitsOf s.P s.P.T / m + 1 := by unfold kC; rw [hm]
  have hThi : a + b + c ≤ s.P.T + kC s.P s.P.T := by rw [hkC]; omega
  have hbal0 : a ≤ c + umax s.P + 1 ∧ c ≤ a + umax s.P + 1 := by omega
  have hfam0 : a + b + c ≤ δ y + δ x + δ z + s₀ x + unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) := by
    rw [hσ, hm]; omega
  let I' := fun j t => CDriveInv X s A.elist δ δu s₀ x y z a b c (units s x) j t ∧
    t.Gs.size = s.Gs.size ∧ t.C.size = s.C.size
  have h0 : I' 0 s := ⟨⟨hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩, ⟨gh, hG⟩, hCi, hxL, hst, hl, hr,
    by omega, by omega,
      Or.inl ⟨rfl, ha, hc⟩⟩, rfl, rfl⟩
  have hs0 : s₀ x ≤ s.P.T := by rw [hσ]; exact hs0T
  refine driveChunkFrom_pk hC hK hW I' h0 (fun j t ⟨hD, hGs, hCs⟩ hj => ?_) hGd hgL
  have K' : GCaps κ t := Kc.of_sizes hGs hD.ef.size hCs
  obtain ⟨bb, t', hrun, hA, hG', hC', -⟩ := hD.stepAgree hXs hP hCP hThi hbal0 hfam0 hδs hs0 K'
  obtain ⟨Lg, ng, eg, hok, -⟩ := hA (Machine.State.setLocs (fun _ => 0) ["x"] [x])
    (by
      simp [Machine.State.setLocs, Machine.State.upd])
  obtain ⟨t1, h1 | h1⟩ := hD.step hXs hP hCP (by
    intro c' h1 h2 h3
    exact hδ c' h1 h2 h3) hThi hbal0 hfam0 hδs hs0
  · rw [h1.1] at hrun; injection hrun with e1 e2; subst e2; subst e1
    exact ⟨true, t1, Lg, ng, eg, hok, fun _ => ⟨h1.2, hG'.trans hGs, hC'.trans hCs⟩, hXV _ h1.2.xx⟩
  · rw [h1.1] at hrun; injection hrun with e1 e2; subst e2; subst e1
    refine ⟨false, t1, Lg, ng, eg, hok, fun h => absurd h (by decide), ?_⟩
    rcases h1.2.xx with h | h
    · exact hXV _ h
    · exact hYV _ h

section cphase
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- `driveChunk x`: the drive of the split `x` belongs to, if any. -/
theorem driveChunkS_pkok {x : Nat} (hG : Gd K KH κ (ΓK K) s L) (hxL : L "x" = x)
    (hD : ∀ q, ((s.C.getX x).st = .splitting ∧ q = x ∨ (s.C.getX x).st = .overflow ∧ q =
      (s.C.getX x).src) →
      ∀ L', L' "x" = q → Gd K KH κ (ΓK K) s L' → PKok K KH κ (ΓK K) W driveChunkFromS s L') :
    PKok K KH κ (ΓK K) W driveChunkS s L := by
  unfold driveChunkS
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by proveSafe) hG)) (fun s1 L1 n1
    h1 hG1 => ?_)
  obtain ⟨v, hv, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  obtain ⟨j, hj, hjc, rfl⟩ := Exp.ev_rd_inv hv
  simp only [Exp.ev, Option.some.injEq] at hj; subst hj
  have hLx : Machine.State.upd L "st" (Fld.get s (L "x") (.c .st)) "x" = x := by
    rw [upd_ne _ _ (by decide)]; exact hxL
  refine PKok.ite_ok hC hG1 (by proveSafe) (fun c hc hc0 => ?_) (fun hc => ?_)
  · have hst : (s.C.getX x).st = .splitting := by
      simp [Exp.ev, Machine.BinOp.eval,  Fld.get, CF.get] at hc
      rw [← hxL]
      by_contra hne
      have : (s.C.getX (L "x")).st.toN ≠ 2 := by
        cases h : (s.C.getX (L "x")).st <;> simp_all [St.toN]
      simp [this] at hc; exact hc0 hc.symm
    exact PKok.callS hC (Γe := ΓK K) hG1 (by proveSafe) (fun _ => le_refl K)
      (fun vs hvs hG0 => hD x (Or.inl ⟨hst, rfl⟩) _ (by
        simp only [evList, List.mapM_cons, Exp.ev, Machine.State.upd, String.reduceEq,
            ↓reduceIte, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
            Option.bind_some, Option.some.injEq] at hvs; subst hvs
        simp [cdriveP, Machine.State.setLocs, Machine.State.upd,
          hxL])
        hG0) (by simp [cdriveP]) (by simp)
  · refine PKok.ite_ok hC hG1 (by proveSafe) (fun c' hc' hc0' => ?_) (fun _ => PK.ok
      (PK.skip hG1))
    have hst : (s.C.getX x).st = .overflow := by
      simp [Exp.ev, Machine.BinOp.eval,  Fld.get, CF.get] at hc'
      rw [← hxL]
      by_contra hne
      have : (s.C.getX (L "x")).st.toN ≠ 1 := by
        cases h : (s.C.getX (L "x")).st <;> simp_all [St.toN]
      simp [this] at hc'; exact hc0' hc'.symm
    exact PKok.callS hC (Γe := ΓK K) hG1 (by proveSafe) (fun _ => le_refl K)
      (fun vs hvs hG0 => hD _ (Or.inr ⟨hst, rfl⟩) _ (by
        have hjc' : L "x" < κ.tbl .C := by simpa [Fld.cap] using hjc
        simp only [evList, Fld.get, CF.get, Exp.cF, List.mapM_cons, Exp.ev, Machine.State.upd,
            String.reduceEq, ↓reduceIte, Fld.cap, Option.bind_some, hjc', List.mapM_nil,
            Option.pure_def, Option.bind_eq_bind, Option.some.injEq] at hvs
        subst hvs
        simp [cdriveP, Machine.State.setLocs, Machine.State.upd,
          hxL])
        hG0) (by simp [cdriveP]) (by simp)

end cphase

/-- **The chunk phase** (the context of `driveChunk_wb`): the hooks of option (B) give the
stored-value bound of every state of the drive. -/
theorem chunkPhasePeak (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
    {t : Core} {A : Abs} {Lg : List Nat} {gh : GGh} {s₀ δu : Nat → Nat} {c : Nat}
    (hI : INV t A) (hel : A.elist = Lg) (hG : GInv t Lg gh (fun _ => 0)) (hCi : CInv t Lg (δ1 c)
      δu s₀)
    (hLX : LX s₀ (δ1 c) δu t) (hGP : GParams t.P) (hCP : CParams t.P) (hcL : LiveC t c)
    (hcnd : cSt t c ≠ .dead) (hcsz : 1 ≤ cSz t c) (hWB : OrderMaintenance.Proof.Word.WB K t) (hL
      : OrderMaintenance.Proof.Word.LabRoom K t.P)
    (hlen : 4 * Lg.length + 1 ≤ 2 ^ K) (Kc : GCaps κ t) {L : Loc} (hxL : L "x" = c)
    (hGd : Gd K KH κ (ΓK K) t L) : PKok K KH κ (ΓK K) W driveChunkS t L := by
  have hδu := hCi.δu
  have hFB : ∀ u, OrderMaintenance.Proof.Word.WB K u → FB K KH κ (.c .size) u := fun u hu j _ => by
    obtain ⟨-, -, -, -, h5, -⟩ := hu.C j; simpa [Fld.get, CF.get, Fld.wd] using h5
  have drive : ∀ x, LiveC t x → cSt t x = .splitting → (c = cLl t x ∨ c = x ∨ c = cRr t x) →
      ∀ L', L' "x" = x → Gd K KH κ (ΓK K) t L' → PKok K KH κ (ΓK K) W driveChunkFromS t L' := by
    intro x hxL' hxs hcx L' hL' hG'
    clear hxL hGd
    subst hel
    have Fx := hCi.cfam x hxL' hxs
    have hlx := Fx.lx hI hxL'
    have hrx := Fx.rx hI hxL'
    have hlr := Fx.lr hI hxL'
    have hCx : CInvE t A.elist (δ1 c) δu s₀ x :=
      { hCi with c1 := fun z hz hzs _ => hCi.c1 z hz hzs (by
        unfold NIL
        have := hz.1
        omega) }
    have hC1 := hCi.c1 x hxL' hxs (by
      unfold NIL
      have := hxL'.1
      omega)
    have hXs := OrderMaintenance.Proof.Word.cxsteps_wb (cxsteps_linv (L := A.elist) (δ := δ1 c)
      (δu := δu) (s₀ := s₀) (x := x))
      hL hlen
    exact cinv_drivePeak hC hK hW hI hG hCx hC1 hXs ⟨hLX, hWB, rfl⟩ hGP hCP
      hxL' hxs (fun c' h1 h2 h3 => by
        unfold δ1; rw [ite_eq_right]; rintro rfl; rcases hcx with h | h | h <;> contradiction)
      (by
        unfold δ1
        rcases hcx with rfl | rfl | rfl <;> simp [hlx, hrx, hlr, Ne.symm hlx, Ne.symm hrx,
          Ne.symm hlr])
      (by
        unfold δ1
        refine ⟨?_, ?_, ?_⟩ <;> split <;> first | omega | (subst_vars; exact hcsz))
      Kc (fun u hu => hFB u hu.2.1) (fun u hu => hFB u hu.2.1) hL' hG'
  refine driveChunkS_pkok hC hK hW hGd hxL (fun q hq L' hL' hG' => ?_)
  rcases hq with ⟨hs, hq'⟩ | ⟨hs, hq'⟩
  · exact drive c hcL hs (Or.inr (Or.inl rfl)) L' (by rw [hL', hq']) hG'
  · obtain ⟨hxL', hxs, hlr⟩ := hCi.covf c hcL hs
    exact drive _ hxL' hxs (by
      rcases hlr with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr h.symm)) L'
      (by rw [hL', hq']) hG'

end OrderMaintenance.Impl
