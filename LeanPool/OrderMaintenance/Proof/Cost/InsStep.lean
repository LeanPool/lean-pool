/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Budget


/-!
# The insertion step

The element link (`insertElem`) and the chunk-size update (`chunkSize`): every guard passes, and
the invariants hold with one undriven insertion in the group and in the chunk.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- **The element link succeeds**, keeping INV-S and Lemma G4's invariant. -/
theorem ins_elem_ok {s : Core} {A : Abs} {gh : GGh} (hI : INV s A)
    (hG : GInv s A.elist gh (fun _ => 0)) (hP : GParams s.P) {x : Nat} (hx : x ∈ A.elist)
    (hh : Nat) :
    ∃ lab, (insertElem x hh).run s = .ok s.E.size (linkElem s x s.E.size lab hh) ∧
      (∃ A', INV (linkElem s x s.E.size lab hh) A' ∧
        A'.elist = OrderMaintenance.Spec.insertAfterL x s.E.size A.elist) ∧
      ∃ gh', GInv (linkElem s x s.E.size lab hh) (OrderMaintenance.Spec.insertAfterL x s.E.size
        A.elist) gh'
        (fun b => if b = eG s x then 1 else 0) := by
  obtain ⟨lab, hrun, hG'⟩ := ginv_insertElem hI hG hP hx hh
  refine ⟨lab, hrun, ?_, hG'⟩
  rcases insertElem_run s x hh with ⟨lab', h1, h2, hr⟩ | ⟨msg, hr⟩
  · rw [hrun] at hr
    have he : linkElem s x s.E.size lab hh = linkElem s x s.E.size lab' hh := by
      injection hr
    rw [he]
    exact ⟨_, inv_linkElem hI hx h1 h2⟩
  · rw [hrun] at hr; cases hr

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- **The chunk-size update succeeds and keeps the queue invariant** (Lemma K2: no scan). -/
theorem chunkSize_ok {s : Core} {x lab hh : Nat} (hpq : PQC s) (hcL : LiveC s (gC s (eG s x))) :
    ∃ s2, (chunkSize (gC s (eG s x)) true).run (linkElem s x s.E.size lab hh) = .ok () s2 ∧
      PQOnly (sizeState (linkElem s x s.E.size lab hh) (gC s (eG s x))) s2 ∧ PQC s2 := by
  generalize hc : gC s (eG s x) = c at hcL ⊢
  generalize hs1 : linkElem s x s.E.size lab hh = s1
  have hC1 : s1.C = s.C := by rw [← hs1]; rfl
  have hP1 : s1.P = s.P := by rw [← hs1]; rfl
  have hst : ∀ d, cSt (sizeState s1 c) d = cSt s d := by
    intro d; simp only [cSt, sizeState, Array.getX_modify, hC1]; split <;> simp_all
  have hsz : ∀ d, cSz (sizeState s1 c) d = cSz s d + if d = c then 1 else 0 := by
    intro d; simp only [cSz, sizeState, Array.getX_modify, hC1]
    by_cases h : d = c
    · subst h; simp [hcL.2]
    · simp [h, Ne.symm h]
  have hLC : ∀ d, LiveC (sizeState s1 c) d ↔ LiveC s d := by
    intro d; simp only [LiveC, sizeState, Array.size_modify', hC1]
  have hPS : PQSame s (sizeState s1 c) := by
    rw [← hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hPs : (sizeState s1 c).P = s.P := by rw [← hP1]; rfl
  obtain ⟨bl, nb, hQ⟩ := hpq
  by_cases hq : cSt s c = .quiet
  · have hq1 : cSt s1 c = .quiet := by simp only [cSt, hC1]; exact hq
    rw [chunkSize_run_q hq1]
    have hsz1 : cSz s1 c = cSz s c := by simp only [cSz, hC1]
    rw [hsz1]
    have hss : sizeState s1 c = { s1 with C := s1.C.modify c fun C => { C with size :=
      (s1.C.getX c).size + 1 } } := rfl
    have hQ' : QRep (sizeState s1 c) (cSz s) (inQC s) bl nb := hQ.congr hPS (fun _ => rfl) (fun
      _ _ => rfl)
    have hin : inQC s c = decide ((sizeState s1 c).P.theta < cSz s c) := by
      unfold inQC; rw [hPs]; simp [hcL, hq]
    obtain ⟨st', hrun, hO, hQI⟩ := pqAdjust_inc hQ' (by have := hcL.1; omega) hin
      (fun _ => rfl)
    refine ⟨st', hrun, hO, ?_⟩
    have hsz' : ∀ d, cSz st' d = cSz s d + if d = c then 1 else 0 := by
      intro d; rw [← hsz d]; simp only [cSz, hO.C]
    refine QInv.congr (k' := cSz st') (inQ' := inQC st') hQI (PQSame.refl _) (fun d => ?_)
      (fun d hd => ?_)
    · unfold inQC
      have hL' : LiveC st' d ↔ LiveC s d := by simp only [LiveC, hO.C]; exact hLC d
      have hst' : cSt st' d = cSt s d := by rw [← hst d]; simp only [cSt, hO.C]
      rw [hsz', hst', hO.P, hPs]
      by_cases hdc : d = c
      · subst hdc; rw [Function.update_self]; simp [hL', hcL, hq]
      · rw [Function.update_of_ne hdc]; simp [hL', hdc]
    · rw [hsz']
      by_cases hdc : d = c
      · subst hdc; rw [Function.update_self]; simp
      · rw [Function.update_of_ne hdc]; simp [hdc]
  · have hq1 : cSt s1 c ≠ .quiet := by simp only [cSt, hC1]; exact hq
    rw [chunkSize_run_nq hq1]
    refine ⟨_, rfl, PQOnly.refl _, ⟨bl, nb, hQ.congr hPS (fun d => ?_) (fun d hd => ?_)⟩⟩
    · unfold inQC
      rw [hst, hsz, hPs]
      by_cases hdc : d = c
      · subst hdc; simp [hq]
      · simp only [ite_eq_right hdc, Nat.add_zero, hLC]
    · rw [hsz]
      have : d ≠ c := by
        rintro rfl; unfold inQC at hd; simp only [decide_eq_true_eq] at hd; exact hq hd.2.1
      simp [this]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- One undriven insertion at `c`. -/
def δ1 (c : Nat) : Nat → Nat := fun d => if d = c then 1 else 0

theorem update_zero_eq_δ1 (c : Nat) :
    Function.update (fun _ => 0) c ((fun (_ : Nat) => 0) c + 1) = δ1 c := by
  funext d; unfold δ1; by_cases h : d = c
  · subst h; simp
  · simp [h]

/-- The invariants right after the insertion of an element into group `g` of chunk `c`. -/
structure InsPost (TI : Core → Prop) (k J n R : Nat) (μ : Core → Nat) (L : List Nat) (s0 : Core)
    (g c : Nat) (s2 : Core) : Prop where
  inv : ∃ A, INV s2 A ∧ A.elist = L
  ginv : ∃ gh, GInv s2 L gh (δ1 g)
  cinv : ∃ s₀, CInv s2 L (δ1 c) (fun _ => 0) s₀ ∧ LX s₀ (δ1 c) (fun _ => 0) s2
  pq : PQC s2
  cnt : ∃ e pops, CountInv s2 e pops
  cp : CParams s2.P
  ti : TI s2
  game : ∃ y i a ip js, GameInv n R s2 y i a ip ∧ RoundAt k J (μ s2) s2.resJob ip js 0
  count : s2.count = s0.count + 1
  P : s2.P = s0.P
  grp : LiveG s2 g ∧ gC s2 g = c ∧ 1 ≤ gSz s2 g
  csz : 1 ≤ cSz s2 c
  quiet : cSt s2 c = .quiet → cSz s2 c ≤ s2.P.T + 1
  cL : LiveC s2 c


/-- An inserted element's pending chunk budget supplies room for the group split. -/
theorem InsPost.split_room {TI : Core → Prop} {μ : Core → Nat} {k J n R : Nat}
    {L : List Nat} {s0 s2 : Core} {g c : Nat}
    (hPost : InsPost TI k J n R μ L s0 g c s2) :
    gSt s2 g = .quiet → s2.P.G ≤ gSz s2 g → SplitRoom s2 g := by
  obtain ⟨A, hI, hel⟩ := hPost.inv
  obtain ⟨gh, hG⟩ := hPost.ginv
  obtain ⟨s₀, hC, ⟨lg, hLi⟩, hLP, hGP⟩ := hPost.cinv
  obtain ⟨hgL, hgc, -⟩ := hPost.grp
  subst hel
  intro hq hge
  have hq0 := (hG.quiet g hgL hq).1
  unfold δ1 at hq0; rw [ite_eq_left rfl] at hq0
  have hcl : LiveC s2 (gC s2 g) := by rw [hgc]; exact hPost.cL
  have hδ1 : ∀ x, LiveC s2 x → cSt s2 x = .splitting →
      δ1 c (cLl s2 x) + δ1 c x + δ1 c (cRr s2 x) ≤ 1 := by
    intro x hx hxs
    have Fx := hC.cfam x hx hxs
    have h1 := Fx.lx hI hx
    have h2 := Fx.rx hI hx
    have h3 := Fx.lr hI hx
    unfold δ1; split_ifs <;> simp_all
  have hnd : cSt s2 c ≠ .dead := by rw [← hgc]; exact (hC.gchk g hgL).2
  obtain ⟨harr, hins⟩ := chunk_budget hC hLi hPost.cp hPost.cL hnd hδ1 hPost.quiet
  rw [← hgc] at harr hins
  exact OrderMaintenance.Proof.split_room hI hLi hLP hGP hgL hq (by omega) hcl harr hins

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- **The game across an insertion**: one value grows by at most 1,
and the round has room for it. -/
theorem game_ins {n R k J : Nat} {μ : Core → Nat} {s s2 : Core} {y : Fin n → ℝ} {i : Fin n}
    {a : Fin n → ℝ} {ip js : Nat} (hG : GameInv n R s y i a ip) (hRO : RoundOK k J μ s ip js)
    (hk : 1 ≤ k) (hR : J / k + 1 ≤ R) (hn : 1 ≤ n) {c : Nat} (hc1 : 1 ≤ c) (hcn : c - 1 < n)
    (hle : ∀ d, gval s2 d ≤ gval s d + if d = c then 1 else 0) (hres : s2.resJob = s.resJob)
    (hμ : μ s2 = μ s) :
    ∃ y' i' a' ip' js', GameInv n R s2 y' i' a' ip' ∧ RoundAt k J (μ s2) s2.resJob ip' js' 0 := by
  have hlev : ∀ j : Fin n, gvec n s2 j ≤ gvec n s j + if j = ⟨c - 1, hcn⟩ then 1 else 0 := by
    intro j
    unfold gvec
    have h := hle (j.val + 1)
    by_cases hj : j = ⟨c - 1, hcn⟩
    · rw [ite_eq_left hj]; rw [ite_eq_left (by rw [hj]; simp only; omega)] at h; exact_mod_cast h
    · rw [ite_eq_right hj]
      have hne : j.val + 1 ≠ c := by intro e; apply hj; ext; simp only; omega
      rw [ite_eq_right hne] at h; simp only [add_zero]; exact_mod_cast h
  have hipR : ∀ m, m * k ≤ J → m + 1 ≤ R := by
    intro m hm
    have : m ≤ J / k := (Nat.le_div_iff_mul_le hk).mpr hm
    omega
  unfold RoundOK at hRO
  rw [hres]
  cases hj : s.resJob with
  | some job =>
    rw [hj] at hRO
    obtain ⟨h1, h2, h3⟩ := hRO
    exact ⟨y, i, _, ip + 1, js, hG.insert ⟨c - 1, hcn⟩ hlev (hipR ip (by omega)),
      by change (ip + 1) * k ≤ js + (k - 0) ∧ js + μ s2 ≤ J ∧ 1 ≤ μ s2
         rw [hμ]; refine ⟨?_, h2, h3⟩; rw [Nat.add_mul, Nat.one_mul]; omega⟩
  | none =>
    rw [hj] at hRO
    rcases hRO with hz | hip
    · have hz' : ∀ j : Fin n, gvec n s j = 0 := fun j => by unfold gvec; rw [hz]; simp
      have hG0 := GameInv.reset (R := R) hz' ⟨0, hn⟩
      exact ⟨0, ⟨0, hn⟩, _, 0 + 1, 0, hG0.insert ⟨c - 1, hcn⟩ hlev (hipR 0 (by simp)),
        by change (0 + 1) * k ≤ J + (k - 0); omega⟩
    · exact ⟨y, i, _, ip + 1, js, hG.insert ⟨c - 1, hcn⟩ hlev (hipR ip hip),
        by change (ip + 1) * k ≤ J + (k - 0); rw [Nat.add_mul, Nat.one_mul]; omega⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
theorem sizeState_sameLinks (t : Core) (c : Nat) : SameLinks t (sizeState t c) := by
  refine ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ =>
    rfl, rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ =>
      rfl,
    rfl, rfl, rfl, rfl, rfl, by simp [sizeState], fun d => ?_, fun d => ?_, fun d => ?_, fun d
      => ?_,
    rfl⟩ <;> simp only [cN, cP, cF, cLs, sizeState, Array.getX_modify] <;> split <;> simp_all

theorem sizeState_cT (t : Core) (c d : Nat) : cT (sizeState t c) d = cT t d := by
  simp only [cT, sizeState, Array.getX_modify]; split <;> simp_all

/-- **The insertion step**: the element link and the size update succeed; all invariants hold
with one undriven insertion. -/
theorem insert_step {TI : Core → Prop} {μ : Core → Nat} {J k n R : Nat} {cap : Params → Nat} {L
  : List Nat}
    {s : Core} {y : Fin n → ℝ} {i : Fin n} {a : Fin n → ℝ} {ip js x : Nat}
    (hTC : TopContract TI μ J cap) (hL : LowInv s L) (hTI : TI s) (hG : GameInv n R s y i a ip)
    (hRO : RoundOK k J μ s ip js) (hx : x ∈ L) (hk : 1 ≤ k) (hR : J / k + 1 ≤ R) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T) (hh : Nat) :
    ∃ s1 s2, (insertElem x hh).run s = .ok s.E.size s1 ∧
      (chunkSize (gC s1 (eG s1 s.E.size)) true).run s1 = .ok () s2 ∧
      InsPost TI k J n R μ (OrderMaintenance.Spec.insertAfterL x s.E.size L) s (eG s x) (gC s
        (eG s x)) s2 ∧
      eG s1 s.E.size = eG s x ∧ gC s1 (eG s x) = gC s (eG s x) ∧ s2.E = s1.E ∧ s1.P = s.P := by
  obtain ⟨A, hI, hel⟩ := hL.inv
  subst hel
  obtain ⟨gh, hG0⟩ := hL.ginv
  obtain ⟨s₀, hC, ⟨lg, hLi⟩, hLP, hGP⟩ := hL.cinv
  obtain ⟨e, pops, hN⟩ := hL.cnt
  obtain ⟨lab, hrun1, ⟨A', hI1, hel1⟩, gh', hG1⟩ := ins_elem_ok hI hG0 hGP hx hh
  have hgL : LiveG s (eG s x) := hI.mem_glist_iff.mp (hI.eG_mem hx)
  have hcL : LiveC s (gC s (eG s x)) := (hC.gchk _ hgL).1
  obtain ⟨s2, hrun2, hO, hpq2⟩ := chunkSize_ok (lab := lab) (hh := hh) hL.pq hcL
  have heG : eG (linkElem s x s.E.size lab hh) s.E.size = eG s x := by
    rw [linkElem_eG, ite_eq_left rfl]
  have hgC : gC (linkElem s x s.E.size lab hh) (eG s x) = gC s (eG s x) :=
    (linkElem_glinks s x lab hh).chk _
  refine ⟨_, s2, hrun1, by rw [heG, hgC]; exact hrun2, ?_, heG, hgC, by rw [hO.E]; rfl, rfl⟩
  -- the insertion's effect on the chunks
  have hGs2 : s2.Gs = (linkElem s x s.E.size lab hh).Gs := by rw [hO.Gs]; rfl
  have hC2 : s2.C = (sizeState (linkElem s x s.E.size lab hh) (gC s (eG s x))).C := hO.C
  have hP2 : s2.P = s.P := by rw [hO.P]; rfl
  have hE2 : s2.E = (linkElem s x s.E.size lab hh).E := by rw [hO.E]; rfl
  have S : InsSpec s s2 (eG s x) := insSpec_link hgL.2.1 hcL.2 hGs2 hC2 hP2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r12, r13, r14, r15⟩ := hO.rest
  have hcnt2 : s2.count = s.count + 1 := by rw [r2]; rfl
  have hhead2 : s2.head = (linkElem s x s.E.size lab hh).head := by rw [r3]; rfl
  have hcov : cSt s (gC s (eG s x)) = .overflow →
      cLl s (cSrc s (gC s (eG s x))) = gC s (eG s x) ∨
        cRr s (cSrc s (gC s (eG s x))) = gC s (eG s x) := by
    intro ho; obtain ⟨-, -, h⟩ := hC.covf _ hcL ho
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- Lemma R's size bound before the insertion
  have hd := hL.cp.I4
  have hchunks := hN.chunks (by omega)
  have hcn : gC s (eG s x) - 1 < n := by have := hcL.2; omega
  have hTS2 : TopSame s s2 := topSame_ins hC2 hP2 ⟨by rw [r12]; rfl, by rw [r13]; rfl,
    by rw [r14]; rfl, by rw [r15]; rfl, by rw [r9]; rfl, by rw [r8]; rfl, by rw [r7]; rfl,
    by rw [r6]; rfl⟩
  let lg' : LGh := { lg with
    ins := Function.update lg.ins (gC s (eG s x)) (lg.ins (gC s (eG s x)) + 1) }
  refine
    { inv := ⟨A', hI1.of_sameLinks ?_ ?_, hel1⟩
      ginv := ⟨gh', hG1.of_gsame (GSame.of_eq hGs2 hE2 hhead2 (by rw [hP2]; rfl))⟩
      cinv := ⟨s₀, ?_, ⟨lg', ?_⟩, by rw [hP2]; exact hLP, by rw [hP2]; exact hGP⟩
      pq := hpq2
      cnt := ⟨e, pops, hN.ins S hcnt2⟩
      cp := by rw [hP2]; exact hL.cp
      ti := hTC.frame _ _ hTS2 hTI
      game := ?_
      count := hcnt2
      P := hP2
      grp := ⟨(S.live _).mpr hgL, by rw [S.chk], by rw [S.sz, ite_eq_left rfl]; omega⟩
      csz := by rw [S.csz, ite_eq_left rfl]; omega
      quiet := fun hq => ?_
      cL := by simp only [LiveC, S.Csize]; exact hcL }
  · exact (sizeState_sameLinks _ _).trans hO.sameLinks
  · intro d; rw [show cT s2 d = cT (sizeState (linkElem s x s.E.size lab hh) (gC s (eG s x))) d by
      simp only [cT, hO.C], sizeState_cT]
  · rw [← update_zero_eq_δ1]
    exact cinv_ins (lab := lab) (hh := hh) hI hC hx S (fun e => by simp only [eG, hE2])
  · rw [← update_zero_eq_δ1]
    exact linv_ins hI hG0 hLi S hgL hcov
  · refine game_ins hG hRO hk hR hn hcL.1 hcn (fun d => ?_) (by rw [r9]; rfl)
      (hTC.mframe _ _ hTS2)
    unfold gval
    have hL' : LiveC s2 d ↔ LiveC s d := by simp only [LiveC, S.Csize]
    rw [S.cst, S.csz, hP2]
    by_cases hd : LiveC s d ∧ cSt s d = .quiet
    · rw [ite_eq_left ⟨hL'.mpr hd.1, hd.2⟩, ite_eq_left hd]; split <;> omega
    · rw [ite_eq_right (fun h => hd ⟨hL'.mp h.1, h.2⟩), ite_eq_right hd]; omega
  · rw [S.cst] at hq
    have := cSz_le_T hG hI5 hcL.1 hcn ⟨hcL, hq⟩
    rw [S.csz, ite_eq_left rfl, hP2]; omega

end OrderMaintenance.Proof
