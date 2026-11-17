/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.BgParts


/-!
# The background work of one insertion

After the insertion step: the optional group split start and the group drive, the chunk phase, and
the reservation. Every guard passes, and the cost invariant holds again.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- The background work after the group split start. -/
theorem bg_rest_run {v s3 t4 s' : Core} {y g c k : Nat} (hg : eG v y = g)
    (hdg : (driveGroup g).run v = .ok () s3) (hc : gC s3 (eG s3 y) = c)
    (hdc : (driveChunk c).run s3 = .ok () t4) (hres : (reservation k).run t4 = .ok () s') :
    (do
      let e ← getE y
      driveGroup e.grp
      let e ← getE y
      let G ← getG e.grp
      driveChunk G.chk
      reservation k).run v = .ok () s' := by
  rw [run_getE_bind]
  have hg' : (v.E.getX y).grp = g := hg
  rw [hg', run_bind, hdg]
  dsimp only
  rw [run_getE_bind, run_getG_bind]
  have hc' : (s3.Gs.getX (s3.E.getX y).grp).chk = c := hc
  rw [hc', run_bind, hdc]
  exact hres

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- **The background work of one insertion** succeeds and restores the cost invariant. -/
theorem background_ok {TI : Core → Prop} {μ : Core → Nat} {J k n R : Nat} {cap : Params → Nat}
    {L : List Nat}
    {s0 s1 s2 : Core} {y g c : Nat} (hTC : TopContract TI μ J cap)
    (hPost : InsPost TI k J n R μ L s0 g c s2) (hy : y ∈ L) (heg1 : eG s1 y = g)
    (hgc1 : gC s1 g = c) (hchunk : (chunkSize c true).run s1 = .ok () s2)
    (hE12 : s2.E = s1.E) (hP1 : s1.P = s0.P) (hkP : s0.P.reservationBudget = k) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s2.count / (s0.P.theta + 1 - cmax s0.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s2.count / (s0.P.theta + 1 - cmax s0.P)) ≤ cap s0.P)
    (hI5 : (s0.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s0.P.T) :
    ∃ s', (background y).run s1 = .ok () s' ∧ LowInv s' L ∧ TI s' ∧ s'.count = s2.count ∧
      s'.P = s0.P ∧ ∃ y' i a ip js, GameInv n R s' y' i a ip ∧ RoundOK k J μ s' ip js := by
  obtain ⟨A, hI, hel⟩ := hPost.inv
  obtain ⟨gh, hG⟩ := hPost.ginv
  obtain ⟨s₀, hC, hLX⟩ := hPost.cinv
  obtain ⟨e, pops, hN⟩ := hPost.cnt
  obtain ⟨⟨lg, hLi⟩, hLP, hGP⟩ := hLX
  have hP2 : s2.P = s0.P := hPost.P
  obtain ⟨hgL, hgc, hpos⟩ := hPost.grp
  have heg2 : eG s2 y = g := by simp only [eG, hE12]; exact heg1
  subst hel
  -- the group phase
  have hXg := (((xgroup_cinv (L := A.elist) (δ := δ1 c) (δu := fun _ => 0) (s₀ := s₀) (c := c)
    (by unfold δ1; simp)).and (xgroup_linv (L := A.elist) (s₀ := s₀) (δ := δ1 c)
      (δu := fun _ => 0) (c := c))).and (xgroup_frame (L := A.elist) (c := c) s2)).and
    (xgroup_track (L := A.elist) (c' := c) y c hy)
  have hroom := hPost.split_room
  have hX0 : (((CInv s2 A.elist (δ1 c) (fun _ => 0) s₀ ∧ LX s₀ (δ1 c) (fun _ => 0) s2) ∧
      CFrame s2 s2) ∧ gC s2 (eG s2 y) = c) :=
    ⟨⟨⟨hC, ⟨lg, hLi⟩, hLP, hGP⟩, CFrame.refl s2⟩, by rw [heg2, hgc]⟩
  obtain ⟨s3, hgp, hDD⟩ := groupPhase_ok hI (by rw [hgc]; exact hXg) hX0 hG hGP hgL hpos hroom
  -- the state after the group phase
  obtain ⟨A3, hI3, hel3⟩ := hDD.inv
  obtain ⟨gh3, hG3⟩ := hDD.ginv
  have hP3 : s3.P = s2.P := hDD.P
  obtain ⟨δu', hC3, hLX3, hCF, htr⟩ : ∃ δu' : Nat → Nat, CInv s3 A.elist (δ1 c) δu' s₀ ∧
      LX s₀ (δ1 c) δu' s3 ∧ CFrame s2 s3 ∧ gC s3 (eG s3 y) = c := by
    rcases hDD.x with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · exact ⟨_, h1, h2, h3, h4⟩
    · exact ⟨_, h1, h2, h3, h4⟩
  have hQS := hCF.qsame
  have hcL3 : LiveC s3 c := by simp only [LiveC, hCF.Csize]; exact hPost.cL
  have hcnd3 : cSt s3 c ≠ .dead := by
    rw [(hCF.C c).2.1, ← hgc]; exact (hC.gchk g hgL).2
  have hcsz3 : 1 ≤ cSz s3 c := by rw [(hCF.C c).1]; exact hPost.csz
  -- the chunk phase
  obtain ⟨t4, hdc, hCP4⟩ := driveChunk_ok hI3 hel3 hG3 (hel3 ▸ hC3) hLX3
    (hN.frame hQS hCF.count) (by rw [hP3]; exact hGP) (by rw [hP3]; exact hPost.cp) hcL3 hcnd3
    hcsz3
  have hD : DFrame s2 t4 := hCF.dframe.trans hCP4.fr
  -- the reservation
  have hk2 : s1.P.reservationBudget = k := by rw [hP1]; exact hkP
  have hP4 : t4.P = s0.P := hD.P.trans hP2
  have h0 := hCP4.reservation_invariant hTC hPost hD
  obtain ⟨s', hres, hL', hTI', hc', hPs', hgame'⟩ := reservation_cost hTC h0 hn
    (by rw [hD.count, hP4]; exact hsize) (by rw [hD.count, hP4]; exact hcap)
    (by rw [hP4]; exact hI5)
  refine ⟨s', ?_, hL', hTI', hc'.trans hD.count, hPs'.trans hP4, hgame'⟩
  -- the run of `background`
  unfold background
  rw [run_getP_bind, run_getE_bind, run_getG_bind]
  have e1 : (s1.Gs.getX (s1.E.getX y).grp).chk = c := by
    change gC s1 (eG s1 y) = c; rw [heg1, hgc1]
  rw [e1, run_bind, hchunk]
  dsimp only
  rw [run_getE_bind, run_getG_bind]
  have e2 : (s2.E.getX y).grp = g := heg2
  rw [e2, hk2]
  have hPG : s1.P.G = s2.P.G := by rw [hP1, hP2]
  rw [hPG]
  by_cases hcond : ((s2.Gs.getX g).st == St.quiet && decide ((s2.Gs.getX g).size ≥ s2.P.G)) = true
  · rw [ite_eq_left hcond]
    rw [ite_eq_left hcond] at hgp
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨labL, labR, hLb, hLa⟩ := hroom hcond.1 hcond.2
    have hsg := startGroupSplit_ok hgL hLb hLa
    rw [run_bind, hsg] at hgp
    rw [run_bind, hsg]
    dsimp only at hgp ⊢
    have hEu : (splitState s2 g labL labR).E = s2.E :=
      (splitSpec hI (hI.mem_glist_iff.mpr hgL) labL labR).E
    exact bg_rest_run (by simp only [eG, hEu]; exact heg2) hgp htr hdc hres
  · rw [ite_eq_right hcond]
    rw [ite_eq_right hcond] at hgp
    exact bg_rest_run heg2 hgp htr hdc hres

end OrderMaintenance.Proof
