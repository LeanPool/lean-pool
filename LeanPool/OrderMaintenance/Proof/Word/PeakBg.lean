/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PeakRes
public import LeanPool.OrderMaintenance.Proof.Word.PeakPhase


/-!
# Theorem W, option (A), stage A2: the peak of the background work (`backgroundS`)

`backgroundS_peak`: the peak of `background y`, part by part, along Level F's trace of the parts
(as in `backgroundS_agree`): the chunk size (`csP_pk`), the split start of the group
(`startGroupSplit_pk`), the group drive (`groupPhasePeak`), the chunk drive (`chunkPhasePeak`) and
the reservation (`reservation_peak`). The state after each part is Level F's (the parts' agreement,
and `evalF` is a function).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

section bg
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- **The background work, part by part**: given Level F's trace and the agreement of each part,
the peak of each part's body gives the peak of `background y`. -/
theorem backgroundS_peak {L : Loc} {y : Nat} {s0 s1 s2 s3 s4 : Core}
    (hG : Gd K KH κ (ΓK K) s0 L) (hy : L "y" = y)
    (h2 : (if bgSplit s1 y s0.P then startGroupSplit (gOf s1 y) else pure ()).run s1 = .ok () s2)
    (m1 : ∃ L' n, evalF κ csP.body s0 (State.setLocs (fun _ => 0) ["c"] [cOf s0 y]) = .ok s1 L' n)
    (m2 : bgSplit s1 y s0.P = true →
      ∃ L' n, evalF κ sgsP.body s1 (State.setLocs (fun _ => 0) ["g"] [gOf s1 y]) = .ok s2 L' n)
    (m3 : ∃ L' n, evalF κ dgP.body s2 (State.setLocs (fun _ => 0) ["g"] [gOf s2 y]) = .ok s3 L' n)
    (m4 : ∃ L' n, evalF κ dcP.body s3 (State.setLocs (fun _ => 0) ["x"] [cOf s3 y]) = .ok s4 L' n)
    (p1 : Gd K KH κ (ΓK K) s0 (State.setLocs (fun _ => 0) ["c"] [cOf s0 y]) →
      PKok K KH κ (ΓK K) W csP.body s0 (State.setLocs (fun _ => 0) ["c"] [cOf s0 y]))
    (p3 : Gd K KH κ (ΓK K) s2 (State.setLocs (fun _ => 0) ["g"] [gOf s2 y]) →
      PKok K KH κ (ΓK K) W dgP.body s2 (State.setLocs (fun _ => 0) ["g"] [gOf s2 y]))
    (p4 : Gd K KH κ (ΓK K) s3 (State.setLocs (fun _ => 0) ["x"] [cOf s3 y]) →
      PKok K KH κ (ΓK K) W dcP.body s3 (State.setLocs (fun _ => 0) ["x"] [cOf s3 y]))
    (p5 : Gd K KH κ (ΓK K) s4 (State.setLocs (fun _ => 0) [] []) →
      PKok K KH κ (ΓK K) W resP.body s4 (State.setLocs (fun _ => 0) [] []))
    (hP1 : s1.P = s0.P) (hg1 : gOf s1 y < κ.tbl .G) :
    PKok K KH κ (ΓK K) W backgroundS s0 L := by
  obtain ⟨L1, n1, e1⟩ := m1
  obtain ⟨L3, n3, e3⟩ := m3
  obtain ⟨L4, n4, e4⟩ := m4
  have hrd : ∀ {S : Core} {L' : Loc} {f : Fld} {x : Reg} {v : Nat},
      (Exp.rd f (.var x)).ev κ S L' = some v → v = f.get S (L' x) := fun h => (Exp.ev_rdv h).2
  unfold backgroundS
  -- `g`, `c`, and the chunk's size
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hG)) (fun sa La na ha
    hGa => ?_)
  obtain ⟨va, hva, rfl, rfl⟩ := evalF_assign_inv ha
  have hva' : va = gOf s0 y := by rw [hrd hva, hy]; rfl
  subst hva'
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hGa)) (fun sb Lb nb hb
    hGb => ?_)
  obtain ⟨vb, hvb, rfl, rfl⟩ := evalF_assign_inv hb
  have hvb' : vb = cOf s0 y := by rw [hrd hvb, upd_eq]; rfl
  subst hvb'
  set La := State.upd (State.upd L "g" (gOf s0 y)) "c" (cOf s0 y)
  have hay : La "y" = y := by simp [La, Machine.State.upd, hy]
  have c1 := evalF_call_ok (q := csP) (args := [.var "c"]) (ds := []) (L := La)
    (by simp [evList, Exp.ev, La, Machine.State.upd]) e1
  refine PKok.seq (PKok.callS hC (Γc := ΓK K) (Γe := ΓK K) hGb (by jsafe) (fun _ => le_refl K)
    (fun vs hvs hG0 => ?_) (by simp [csP]) (by simp)) (fun sc Lc nc hc hGc => ?_)
  · simp only [evList, List.mapM_cons, Exp.ev, State.upd, ↓reduceIte, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, La] at hvs
    subst hvs; exact p1 hG0
  rw [c1] at hc
  injection hc with e5 e6; subst e5 e6
  -- the group's split
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hGc)) (fun sd Ld nd hd
    hGd => ?_)
  obtain ⟨vd, hvd, rfl, rfl⟩ := evalF_assign_inv hd
  have hvd' : vd = gOf s1 y := by rw [hrd hvd]; simp [Machine.State.setLocs, hay]; rfl
  subst hvd'
  set Lb := State.upd (State.setLocs La [] (csP.rets.map L1)) "g" (gOf s1 y)
  have hLb : Lb = State.upd La "g" (gOf s1 y) := rfl
  have hby : Lb "y" = y := by rw [hLb]; simp [Machine.State.upd, hay]
  have hcv : bgSplitC.ev κ s1 Lb = some (b2n (bgSplit s1 y s0.P)) := by
    rw [hLb]
    simp only [bgSplitC, bgSplit, Exp.gF, Exp.ev, Machine.State.upd, ite_true,
      Option.bind_some, hg1,
      Fld.cap, Fld.get, GF.get, PF.get, hP1]
    cases hst : (s1.Gs.getX (gOf s1 y)).st <;>
      by_cases hz : s0.P.G ≤ (s1.Gs.getX (gOf s1 y)).size <;> simp [Machine.BinOp.eval,  hz,
        St.toN, b2n]
  have e2 : ∃ c2, evalF κ (.ite bgSplitC (sgsP.call [.var "g"] []) .skip) s1 Lb = .ok s2 Lb c2 := by
    by_cases hb : bgSplit s1 y s0.P = true
    · obtain ⟨L2, n2, e2⟩ := m2 hb
      have c2 := evalF_call_ok (q := sgsP) (args := [.var "g"]) (ds := []) (L := Lb)
        (by simp [evList, Exp.ev, hLb, Machine.State.upd]) e2
      exact ⟨_, evalF_ite_t (by rw [hcv]) (by simp [hb, b2n]) c2⟩
    · rw [ite_eq_right hb] at h2
      have he : s2 = s1 := by
        have : (pure () : CM Unit).run s1 = .ok () s1 := rfl
        rw [this] at h2; injection h2 with _ h; exact h.symm
      rw [he]
      exact ⟨_, evalF_ite_f (by
        rw [hcv]
        simp [b2n, hb]) evalF_skip⟩
  obtain ⟨c2, e2⟩ := e2
  refine PKok.seq (PKok.ite_ok hC hGd (by
    simp only [bgSplitC]
    jsafe) (fun _ _ _ => ?_)
    (fun _ => PK.ok (PK.skip hGd))) (fun se Le ne he hGe => ?_)
  · exact PK.ok (PK.callS hC (Γc := ΓK K) (Γe := ΓK K) hGd (by jsafe) (fun _ => le_refl K)
      (fun vs _ hG0 => startGroupSplit_pk hC hK hW hG0) (by simp [sgsP]) (by simp))
  rw [e2] at he
  injection he with e7 e8; subst e7 e8
  -- the group drive
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hGe)) (fun sf Lf nf hf
    hGf => ?_)
  obtain ⟨vf, hvf, rfl, rfl⟩ := evalF_assign_inv hf
  have hvf' : vf = gOf s2 y := by rw [hrd hvf, hby]; rfl
  subst hvf'
  set Lc := State.upd Lb "g" (gOf s2 y)
  have hcy : Lc "y" = y := by simp [Lc, Machine.State.upd, hby]
  have c3 := evalF_call_ok (q := dgP) (args := [.var "g"]) (ds := []) (L := Lc)
    (by simp [evList, Exp.ev, Lc, Machine.State.upd]) e3
  refine PKok.seq (PKok.callS hC (Γc := ΓK K) (Γe := ΓK K) hGf (by jsafe) (fun _ => le_refl K)
    (fun vs hvs hG0 => ?_) (by simp [dgP]) (by simp)) (fun sg Lg ng hg hGg => ?_)
  · simp only [evList, List.mapM_cons, Exp.ev, State.upd, ↓reduceIte, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Lc] at hvs
    subst hvs; exact p3 hG0
  rw [c3] at hg
  injection hg with e9 e10; subst e9 e10
  -- the chunk drive
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hGg)) (fun sh Lh nh hh
    hGh => ?_)
  obtain ⟨vh, hvh, rfl, rfl⟩ := evalF_assign_inv hh
  have hvh' : vh = gOf s3 y := by rw [hrd hvh]; simp [Machine.State.setLocs, hcy]; rfl
  subst hvh'
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hGh)) (fun si Li ni hi
    hGi => ?_)
  obtain ⟨vi, hvi, rfl, rfl⟩ := evalF_assign_inv hi
  have hvi' : vi = cOf s3 y := by rw [hrd hvi, upd_eq]; rfl
  subst hvi'
  set Ld := State.upd (State.upd (State.setLocs Lc [] (dgP.rets.map L3)) "g" (gOf s3 y)) "x"
    (cOf s3 y)
  have c4 := evalF_call_ok (q := dcP) (args := [.var "x"]) (ds := []) (L := Ld)
    (by simp [evList, Exp.ev, Ld, Machine.State.upd]) e4
  refine PKok.seq (PKok.callS hC (Γc := ΓK K) (Γe := ΓK K) hGi (by jsafe) (fun _ => le_refl K)
    (fun vs hvs hG0 => ?_) (by simp [dcP]) (by simp)) (fun sj Lj nj hj hGj => ?_)
  · simp only [evList, State.setLocs, List.mapM_cons, Exp.ev, State.upd, ↓reduceIte,
      List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Ld] at hvs
    subst hvs; exact p4 hG0
  rw [c4] at hj
  injection hj with e11 e12; subst e11 e12
  -- the reservation
  exact PKok.callS hC (Γc := ΓK K) (Γe := ΓK K) hGj (by jsafe) (fun _ => le_refl K)
    (fun vs hvs hG0 => by simp only [evList, State.setLocs, List.mapM_nil, Option.pure_def,
        Option.some.injEq, List.nil_eq] at hvs; subst hvs; exact p5 hG0) (by simp [resP]) (by simp)

end bg

end OrderMaintenance.Impl

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Impl OrderMaintenance.Zeroing
open OrderMaintenance.Machine (Reg State)
variable {K KH W : Nat}

/-- **The background work of an insertion** (the context of `bgAgree` and `background_wb`): its
peak, from the parts' peaks along Level F's trace. -/
theorem background_peak {TI : Core → Prop} {μ : Core → Nat} {J k n R NB0 : Nat} {cap : Params → Nat}
    {L : List Nat} {s0 s1 s2 : Core} {y g c : Nat} (hTC : TopContract TI μ J cap) (hT : TopWB K
      TI μ)
    (hTI : ∀ t, TI t → OrderMaintenance.Proof.Top.TopInv t)
    (hPost : InsPost TI k J n R μ L s0 g c s2) (hy : y ∈ L) (heg1 : eG s1 y = g)
    (hgc1 : gC s1 g = c) (hchunk : (chunkSize c true).run s1 = .ok () s2)
    (hE12 : s2.E = s1.E) (hP1 : s1.P = s0.P) (hkP : s0.P.reservationBudget = k) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s2.count / (s0.P.theta + 1 - cmax s0.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s2.count / (s0.P.theta + 1 - cmax s0.P)) ≤ cap s0.P)
    (hI5 : (s0.P.theta : ℝ) + R * (OrderMaintenance.Zeroing.Hn (n - 1) + 1) ≤ s0.P.T)
    {κ : Caps} (Ly : Loc) (hLy : Ly "y" = y) (hpow : s0.P.a = 2 ^ Nat.log2 s0.P.a)
    (hq1 : PQCaps κ s1) (hcC : c < Ccap κ) (hcB : (s1.C.getX c).size + 1 < Bcap κ)
    (K1 : GCaps κ s1) (hG2 : s1.Gs.size + 2 ≤ κ.tbl .G) (hF0 : 0 < κ.lrec .freeG)
    (hF : s1.freeG.length ≤ κ.lcap .freeG)
    (Mc : Core → Prop) (hM4 : ∀ t, DFrame s2 t → PQCaps κ t → t.Gs.size ≤ s1.Gs.size + 2 → Mc t)
    (hMc : ∀ t, Mc t → TopCaps κ t ∧ PQCaps κ t ∧ t.prep = none ∧
      ∀ c, t.C.size ≤ c → ∀ j, (t.path.getX c).getX j = 0)
    (hMpop : ∀ t c t1, Mc t → pqPopMax.run t = .ok c t1 → Mc t1)
    (hMjob : ∀ s j t job r t1, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t →
      t.resJob = some job →
      (jobStep job).run t = .ok r t1 → ResInv TI s.P.reservationBudget J n R μ L s (j + 1) {
        t1 with
        resJob := r
      } →
      Mc {
        t1 with
        resJob := r
      })
    (hMsplit : ∀ s j t c t1 t2, ResInv TI s.P.reservationBudget J n R μ L s j t → Mc t →
      t.resJob = none → pqPopMax.run t = .ok c t1 →
      (splitChunkStart c).run t1 = .ok () t2 → ResInv TI s.P.reservationBudget J n R μ L s (j +
        1) t2 → Mc t2)
    (hW2 : WB K s2) (hL : LabRoom K s0.P) (hlen : 4 * L.length + 4 ≤ 2 ^ K)
    (hG2' : s2.Gs.size + 2 ≤ 2 ^ K) (hcnt : 2 * s2.count + 2 ≤ 2 ^ K)
    (hNB : s2.nodes.size + μ s2 ≤ NB0 + J * s2.C.size) (hNK : NB0 + J * (2 + 2 * s2.count) + 2 ≤
      2 ^ K)
    (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
    (hcapC : κ.lcap .children < 512) (hcapT : κ.lcap .table < 512) (hRm : TopRoom K s0.P)
    (hcs : (s1.C.getX c).size + 1 < 2 ^ K) (hGd : Gd K KH κ (ΓK K) s1 Ly) :
    PKok K KH κ (ΓK K) W backgroundS s1 Ly := by
  obtain ⟨A, hI, hel⟩ := hPost.inv
  obtain ⟨gh, hG⟩ := hPost.ginv
  obtain ⟨s₀, hCI, hLX⟩ := hPost.cinv
  obtain ⟨e, pops, hN⟩ := hPost.cnt
  obtain ⟨⟨lg, hLi⟩, hLP, hGP⟩ := hLX
  have hP2 : s2.P = s0.P := hPost.P
  obtain ⟨hgL, hgc, hpos⟩ := hPost.grp
  have heg2 : eG s2 y = g := by simp only [eG, hE12]; exact heg1
  have hS12 : Same s1 s2 := by have := pres_chunkSize c true s1; rw [hchunk] at this; exact this
  subst hel
  -- the group phase, with the stored-value bound added to its hooks
  have hXg := ((((xgroup_cinv (L := A.elist) (δ := δ1 c) (δu := fun _ => 0) (s₀ := s₀) (c := c)
    (by
      unfold δ1
      simp)).and (xgroup_linv (L := A.elist) (s₀ := s₀) (δ := δ1 c)
      (δu := fun _ => 0) (c := c))).and (xgroup_frame (L := A.elist) (c := c) s2)).and
    (xgroup_track (L := A.elist) (c' := c) y c hy)).and
    (xgroup_wb (K := K) (P := s0.P) (G0 := s2.Gs.size) (L := A.elist) (c := c) hL hG2' (by omega))
  have hroom : gSt s2 g = .quiet → s2.P.G ≤ gSz s2 g → SplitRoom s2 g := by
    intro hq hge
    have hq0 := (hG.quiet g hgL hq).1
    unfold δ1 at hq0; rw [ite_eq_left rfl] at hq0
    have hcl : LiveC s2 (gC s2 g) := by rw [hgc]; exact hPost.cL
    have hδ1 : ∀ x, LiveC s2 x → cSt s2 x = .splitting →
        δ1 c (cLl s2 x) + δ1 c x + δ1 c (cRr s2 x) ≤ 1 := by
      intro x hx hxs
      have Fx := hCI.cfam x hx hxs
      have h1 := Fx.lx hI hx; have h2 := Fx.rx hI hx; have h3 := Fx.lr hI hx
      unfold δ1; split_ifs <;> simp_all
    have hnd : cSt s2 c ≠ .dead := by rw [← hgc]; exact (hCI.gchk g hgL).2
    obtain ⟨harr, hins⟩ := chunk_budget hCI hLi hPost.cp hPost.cL hnd hδ1 hPost.quiet
    rw [← hgc] at harr hins
    exact split_room hI hLi hLP hGP hgL hq (by omega) hcl harr hins
  have hX0 : ((((CInv s2 A.elist (δ1 c) (fun _ => 0) s₀ ∧ LX s₀ (δ1 c) (fun _ => 0) s2) ∧
      CFrame s2 s2) ∧ gC s2 (eG s2 y) = c) ∧ XG K s0.P s2.Gs.size s2) :=
    ⟨⟨⟨⟨hCI, ⟨lg, hLi⟩, hLP, hGP⟩, CFrame.refl s2⟩, by rw [heg2, hgc]⟩,
      hW2, hP2, by omega, Or.inl le_rfl⟩
  obtain ⟨s3, hgp, hDD⟩ := groupPhase_ok hI (by
    rw [hgc]
    exact hXg) hX0 hG hGP hgL hpos hroom
  -- the state after the split start
  have hsplit : ∃ s2', (if ((s2.Gs.getX g).st == St.quiet && decide ((s2.Gs.getX g).size ≥
    s2.P.G)) = true then
      startGroupSplit g else pure ()).run s2 = .ok () s2' ∧ (driveGroup g).run s2' = .ok () s3 := by
    by_cases hcond : ((s2.Gs.getX g).st == St.quiet && decide ((s2.Gs.getX g).size ≥ s2.P.G)) = true
    · rw [ite_eq_left hcond] at hgp ⊢
      obtain ⟨u, s2', h2a, h2b⟩ := run_bind_ok hgp
      exact ⟨s2', h2a, h2b⟩
    · rw [ite_eq_right hcond] at hgp ⊢
      exact ⟨s2, rfl, hgp⟩
  obtain ⟨s2', h2a, h2b⟩ := hsplit
  have K2 : GCaps κ s2 := K1.of_sizes hS12.1.Gsize hS12.1.Esize hS12.1.Csize
  have hXc : ∀ t, ((((CInv t A.elist (δ1 c) (fun _ => 0) s₀ ∧ LX s₀ (δ1 c) (fun _ => 0) t) ∧
      CFrame s2 t) ∧ gC t (eG t y) = c) ∧ XG K s0.P s2.Gs.size t) → ∀ g, LiveG t g → gC t g <
        t.C.size :=
    fun t hx g hg => (hx.1.1.1.1.gchk g hg).1.2
  obtain ⟨mG2, ⟨L3, n3, e3, -⟩, hsz3⟩ := groupPhaseAgree hI (by
    rw [hgc]
    exact hXg) hX0 hG hGP hgL hpos hroom
    hXc K2 (by
      rw [hS12.1.Gsize]
      exact hG2) hF0 (by
      rw [hS12.1.freeG]
      exact hF) h2a h2b
  obtain ⟨hGs3, hCs3, hEs3, hE2', hP2'⟩ := hsz3
  -- the state after the group phase
  obtain ⟨A3, hI3, hel3⟩ := hDD.inv
  obtain ⟨gh3, hG3⟩ := hDD.ginv
  have hP3 : s3.P = s2.P := hDD.P
  obtain ⟨δu', hC3, hLX3, hCF, htr, hW3⟩ : ∃ δu' : Nat → Nat, CInv s3 A.elist (δ1 c) δu' s₀ ∧
      LX s₀ (δ1 c) δu' s3 ∧ CFrame s2 s3 ∧ gC s3 (eG s3 y) = c ∧ WB K s3 := by
    rcases hDD.x with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · exact ⟨_, h1, h2, h3, h4, h5.1⟩
    · exact ⟨_, h1, h2, h3, h4, h5.1⟩
  have hQS := hCF.qsame
  have hcL3 : LiveC s3 c := by simp only [LiveC, hCF.Csize]; exact hPost.cL
  have hcnd3 : cSt s3 c ≠ .dead := by
    rw [(hCF.C c).2.1, ← hgc]; exact (hCI.gchk g hgL).2
  have hcsz3 : 1 ≤ cSz s3 c := by rw [(hCF.C c).1]; exact hPost.csz
  -- the chunk phase
  obtain ⟨t4, hdc, hCP4⟩ := driveChunk_ok hI3 hel3 hG3 (hel3 ▸ hC3) hLX3
    (hN.frame hQS hCF.count) (by
      rw [hP3]
      exact hGP) (by
      rw [hP3]
      exact hPost.cp) hcL3 hcnd3
    hcsz3
  obtain ⟨t4', hdc', hW4⟩ := driveChunk_wb hI3 hel3 hG3 (hel3 ▸ hC3) hLX3 (by
    rw [hP3]
    exact hGP)
    (by
      rw [hP3]
      exact hPost.cp) hcL3 hcnd3 hcsz3 hW3 (by
      rw [hP3, hP2]
      exact hL) (by omega)
  rw [hdc] at hdc'
  obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hdc'
  have K3 : GCaps κ s3 := by
    refine ⟨?_, ?_, ?_, K1.fl, K1.f0⟩
    · have := hS12.1.Gsize
      have := K1.G
      omega
    · rw [hEs3, hS12.1.Esize]
      exact K1.E
    · rw [hCs3, hS12.1.Csize]
      exact K1.C
  obtain ⟨⟨L4, n4, e4, -⟩, hGs4, -⟩ := driveChunkAgree hI3 hel3 hG3 (hel3 ▸ hC3) hLX3
    (hN.frame hQS hCF.count) (by
      rw [hP3]
      exact hGP) (by
      rw [hP3]
      exact hPost.cp) hcL3 hcnd3
    hcsz3 K3 hdc
  have hD : DFrame s2 t4 := hCF.dframe.trans hCP4.fr
  -- the reservation
  obtain ⟨yg, ig, ag, ipg, jsg, hGm, hRA⟩ := hPost.game
  have hP4 : t4.P = s0.P := hD.P.trans hP2
  have h0 : ResInv TI k J n R μ A.elist t4 0 t4 := by
    refine ⟨⟨hCP4.inv, hCP4.ginv, ⟨s₀, hCP4.cinv, hCP4.lx⟩, hPost.pq.dframe hD, hCP4.cnt,
      by rw [hP4, ← hP2]; exact hPost.cp⟩, hTC.frame _ _ hD.topSame hPost.ti, rfl, rfl,
      yg, ig, ag, ipg, jsg, hGm.mono (fun j => le_of_eq (by rw [hD.gvec])), ?_⟩
    rw [hD.top.2.2.2.2.1, hTC.mframe _ _ hD.topSame]; exact hRA
  -- chunkSize at Level M
  have hcs1 : c < s1.C.size := by have := hPost.cL.2; rw [hS12.1.Csize] at this; exact this
  obtain ⟨⟨L1, n1, e1, -⟩, hq2⟩ := csP_agree (κ := κ) (L := Machine.State.setLocs (fun _ => 0)
    ["c"] [c])
    (by
      simp [Machine.State.setLocs, Machine.State.upd]) hcs1 (by
        have := K1.C
        omega) hq1 hcC hcB hchunk
  have hq4 : PQCaps κ t4 := hq2.of_same hD.pq
  have hkt : t4.P.reservationBudget = k := by rw [hP4]; exact hkP
  have hM4' := hM4 t4 hD hq4 (by
    rw [hGs4]
    have := hS12.1.Gsize
    omega)
  -- the names of the parts
  have hgo1 : gOf s1 y = g := heg1
  have hco1 : cOf s1 y = c := by change gC s1 (eG s1 y) = c; rw [heg1, hgc1]
  have hgo2 : gOf s2 y = g := heg2
  have hgo2' : gOf s2' y = g := by change (s2'.E.getX y).grp = g; rw [hE2']; exact heg2
  have hco3 : cOf s3 y = c := htr
  have hb : bgSplit s2 y s1.P = ((s2.Gs.getX g).st == St.quiet && decide ((s2.Gs.getX g).size ≥
    s2.P.G)) := by
    simp only [bgSplit, hgo2, hP1, hP2]
  refine backgroundS_peak hC hK hW (s2 := s2') (s3 := s3) (s4 := t4) hGd hLy (by
    rw [hb, hgo2]
    exact h2a)
    ⟨L1, n1, by rw [hco1]; exact e1⟩
    (fun hc => by
      rw [hb] at hc
      obtain ⟨L2, n2, e2, -⟩ := mG2 hc
      exact ⟨L2, n2, by rw [hgo2]; exact e2⟩)
    ⟨L3, n3, by rw [hgo2']; exact e3⟩ ⟨L4, n4, by rw [hco3]; exact e4⟩
    (fun hG0 => PK.ok (csP_pk hC hK hW hG0 (by
      simp only [State.setLocs, State.upd, ↓reduceIte]
      rw [hco1]
      exact hcs)))
    (fun hG0 => by
      rw [hgo2'] at hG0 ⊢
      exact groupPhasePeak hC hK hW hI (by
        rw [hgc]
        exact hXg) hX0 hG hGP hgL hpos hroom hXc K2
        (by
          rw [hS12.1.Gsize]
          exact hG2) h2a (by omega) (by
          simp [Machine.State.setLocs, Machine.State.upd]) hG0)
    (fun hG0 => by
      rw [hco3] at hG0 ⊢
      exact chunkPhasePeak hC hK hW hI3 hel3 hG3 (hel3 ▸ hC3) hLX3 (by
        rw [hP3]
        exact hGP)
        (by
          rw [hP3]
          exact hPost.cp) hcL3 hcnd3 hcsz3 hW3 (by
          rw [hP3, hP2]
          exact hL) (by omega) K3
        (by
          simp [Machine.State.setLocs, Machine.State.upd]) hG0)
    (fun hG0 => reservation_peak (s := t4) hTC hT hTI hn (by
      rw [hD.count, hP4]
      exact hsize)
      (by
        rw [hD.count, hP4]
        exact hcap) (by
        rw [hP4]
        exact hI5) (by
        rw [hD.count]
        exact hcnt)
      (by
        rw [hD.count]
        exact hNK) hMc hMpop (hMjob t4) (hMsplit t4) hC hK hW hcapC hcapT
      (by
        rw [hP4]
        exact hpow) (by
        rw [hP4]
        exact hRm) rfl
      ⟨by rw [hkt]; exact h0, hW4, by
        rw [hD.topSame.top.1, hD.topSame.Csize, hTC.mframe _ _ hD.topSame]
        exact hNB, hM4'⟩ hG0)
    (by rw [hP1, hP2]) (by
      rw [hgo2]
      have := hgL.2.1
      have := K2.G
      omega)

end OrderMaintenance.Proof.Word
