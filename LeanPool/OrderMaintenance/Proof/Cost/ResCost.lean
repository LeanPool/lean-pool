/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.ResStep


/-!
# The reservation of one insertion (Lemma R's rounds)

A round runs from one pop to the next. Its job takes at most `J` steps, and every insertion runs
`k` of them. So a round has at most `J / k + 1` insertions, each adding at most 1 to one game
value: the game's `R`. The round accounting (`RoundOK`) carries this from insertion to insertion.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- Round accounting at the start of an insertion's reservation, with `ip` insertions in the
round (this one included), `js` job steps so far, and `j` iterations of this reservation done. -/
def RoundAt (k J m : Nat) (r : Option Job) (ip js j : Nat) : Prop :=
  match r with
  | some _ => ip * k ≤ js + (k - j) ∧ js + m ≤ J ∧ 1 ≤ m
  | none => ip * k ≤ J + (k - j)

/-- Round accounting between insertions. -/
def RoundOK (k J : Nat) (μ : Core → Nat) (s : Core) (ip js : Nat) : Prop :=
  match s.resJob with
  | some _ => ip * k ≤ js ∧ js + μ s ≤ J ∧ 1 ≤ μ s
  | none => (∀ c, gval s c = 0) ∨ ip * k ≤ J

/-- The reservation's iteration invariant. -/
def ResInv (TI : Core → Prop) (k J n R : Nat) (μ : Core → Nat) (L : List Nat) (s : Core) (j : Nat)
    (t : Core) : Prop :=
  LowInv t L ∧ TI t ∧ t.count = s.count ∧ t.P = s.P ∧
    ∃ y i a ip js, GameInv n R t y i a ip ∧ RoundAt k J (μ t) t.resJob ip js j

/-- The quiet sizes are within `T`, by Lemma R. -/
theorem cSz_le_T {n R : Nat} {t : Core} {y : Fin n → ℝ} {i : Fin n} {a : Fin n → ℝ} {ip : Nat}
    (hG : GameInv n R t y i a ip) (hI5 : (t.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ t.P.T)
    {c : Nat} (hc1 : 1 ≤ c) (hcn : c - 1 < n) (hcq : LiveC t c ∧ cSt t c = .quiet) :
    cSz t c ≤ t.P.T := by
  have hb := hG.bound ⟨c - 1, hcn⟩
  unfold gvec at hb
  simp only [show c - 1 + 1 = c by omega] at hb
  unfold gval at hb
  rw [ite_eq_left hcq] at hb
  have : ((cSz t c - t.P.theta : Nat) : ℝ) + t.P.theta ≤ t.P.T := by linarith
  have h2 : cSz t c ≤ (cSz t c - t.P.theta) + t.P.theta := by omega
  exact_mod_cast (show (cSz t c : ℝ) ≤ t.P.T from by
    calc (cSz t c : ℝ) ≤ ((cSz t c - t.P.theta + t.P.theta : Nat) : ℝ) := by exact_mod_cast h2
      _ = ((cSz t c - t.P.theta : Nat) : ℝ) + t.P.theta := by push_cast; ring
      _ ≤ t.P.T := this)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- The iteration step of `reservation_cost` (its proof, as a lemma). -/
theorem resInv_step {TI : Core → Prop} {μ : Core → Nat} {J k n R : Nat} {cap : Params → Nat} {L
  : List Nat}
    {s : Core} (hTC : TopContract TI μ J cap) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T) :
    ∀ j t, ResInv TI k J n R μ L s j t → j < k →
      (t.resJob = none → (t.pqHi = 0 ∧ (LowInv t L ∧ TI t ∧ t.count = s.count ∧ t.P = s.P ∧
          t.resJob = none ∧ ∀ c, gval t c = 0)) ∨
        (t.pqHi ≠ 0 ∧ ∃ c t1 t2, pqPopMax.run t = .ok c t1 ∧ (splitChunkStart c).run t1 = .ok ()
          t2 ∧
          ResInv TI k J n R μ L s (j + 1) t2)) ∧
      (∀ job, t.resJob = some job → ∃ r t1, (jobStep job).run t = .ok r t1 ∧
        ResInv TI k J n R μ L s (j + 1) {
          t1 with
          resJob := r
        }) := by
    intro j t hI hj
    obtain ⟨hL, hT, hc, hP, y, i, a, ip, js, hG, hR⟩ := hI
    refine ⟨fun hnone => ?_, fun job hjob => ?_⟩
    · by_cases hq0 : t.pqHi = 0
      · exact Or.inl ⟨hq0, hL, hT, hc, hP, hnone, gval_zero_of_empty hL.pq hq0⟩
      · right
        refine ⟨hq0, ?_⟩
        obtain ⟨bl, nb, hQ⟩ := hL.pq
        obtain ⟨c, hpop, hcin, hmax⟩ := pqPopMax_ok hQ hq0
        have hcq := hcin
        unfold inQC at hcq; simp only [decide_eq_true_eq] at hcq
        obtain ⟨hcL, hcQ, hθ⟩ := hcq
        obtain ⟨A, hIA, hel⟩ := hL.inv
        obtain ⟨e, pops, hN⟩ := hL.cnt
        have hI4 := hL.cp.I4
        have hd : 1 ≤ t.P.theta + 1 - cmax t.P := by omega
        -- the chunks fit
        have hpops : pops + 1 ≤ t.count / (t.P.theta + 1 - cmax t.P) := by
          rw [Nat.le_div_iff_mul_le hd]
          have hb := hN.bound
          have hcQs : c ∈ quietSet t := mem_quietSet.mpr ⟨hcL, hcQ⟩
          have hterm : cSz t c - e c ≤ ∑ d ∈ quietSet t, (cSz t d - e d) :=
            Finset.single_le_sum (f := fun d => cSz t d - e d) (fun _ _ => Nat.zero_le _) hcQs
          have he := hN.e_le c hcL hcQ
          rw [Nat.add_mul, Nat.one_mul]; omega
        have hsz := hN.size
        rw [hc, hP] at hpops
        have hcn : c - 1 < n := by have := hcL.2; omega
        have hT5 := cSz_le_T hG (by
          rw [hP]
          exact hI5) hcL.1 hcn ⟨hcL, hcQ⟩
        -- start the split of `c`
        have hD := delSt_only t c
        have hI1 : INV (delSt t c) A := hIA.of_sameLinks hD.sameLinks (fun d => by simp only
          [cT, hD.C])
        have hTI1 : TI (delSt t c) := hTC.frame _ _ hD.topSame hT
        have hsz1 : (delSt t c).C.size = t.C.size := by rw [hD.C]
        have hQS := hD.lowSame.qsame
        have hcL1 : LiveC (delSt t c) c := by simp only [LiveC, hsz1]; exact hcL
        have hcq1 : cSt (delSt t c) c = .quiet := (hQS.q c hcL).mpr hcQ
        have hnone1 : (delSt t c).resJob = none := by rw [hD.rest.2.2.2.2.2.2.2.2.1]; exact hnone
        obtain ⟨job, s2, hj, hμ1, hμJ, hTI2⟩ :=
          hTC.start (delSt t c) A c hI1 hTI1 hnone1 hcL1 hcq1 (by
            rw [hsz1, hD.P, hP]
            omega)
        have hrun := splitChunkStart_ok (by
          unfold NIL
          have := hcL.1
          omega) hcL1.2 hj
        have hs2 : TopRel (linkChunkPair (push2 (delSt t c)) c (delSt t c).C.size
            ((delSt t c).C.size + 1)) s2 := by
          have := top_insertAround c (delSt t c).C.size ((delSt t c).C.size + 1)
            (linkChunkPair (push2 (delSt t c)) c (delSt t c).C.size ((delSt t c).C.size + 1))
          rw [hj] at this; exact this
        refine ⟨c, delSt t c, _, hpop, hrun, ?_⟩
        have hGP : GParams t.P := hL.cinv.choose_spec.2.2.2
        have hL2 := lowinv_pop hL hGP hcin hT5 hs2 hrun
        have hcA : c ∈ A.chunks := (hI1.cAlloc c).mpr hcL1
        have RS := resSpec_run (job := job) hI1 hcA hs2
        obtain ⟨rE, rcnt, rhead, rP⟩ := split_rest (job := job) hs2
        have hjm : (⟨c - 1, hcn⟩ : Fin n).val + 1 = c := by simp only; have := hcL.1; omega
        refine ⟨hL2, hTI2, rcnt.trans (hD.rest.2.1.trans hc), rP.trans (hD.P.trans hP),
          gvec n t, ⟨c - 1, hcn⟩, fun _ => 0, 0, 0, hG.pop ⟨c - 1, hcn⟩ (fun jj => ?_) (fun jj
            => ?_),
          ?_⟩
        · unfold gvec; rw [hjm]; exact_mod_cast gval_max hcin hmax _
        · unfold gvec
          have hp := gval_pop RS (jj.val + 1)
          by_cases hjj : jj = ⟨c - 1, hcn⟩
          · rw [ite_eq_left hjj]; rw [ite_eq_left (by rw [hjj, hjm])] at hp; exact_mod_cast hp
          · rw [ite_eq_right hjj]
            have hne : jj.val + 1 ≠ c := by
              intro e; apply hjj; ext; simp only; omega
            rw [ite_eq_right hne] at hp
            exact_mod_cast hp
        · change RoundAt k J (μ (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job))
            (some job) 0 0 (j + 1)
          exact ⟨by simp, by omega, hμ1⟩
    · obtain ⟨A, hIA, hel⟩ := hL.inv
      obtain ⟨r, t1, hj1, hTI1, hμ⟩ := hTC.step t A job hIA hT hjob
      have hTR : TopRel t t1 := by have := top_jobStep job t; rw [hj1] at this; exact this
      have hSafe : Safe t t1 := by have := pres_jobStep job t; rw [hj1] at this; exact this
      have hI1 := hSafe.2 A hIA
      have hTR' : TopRel t {
        t1 with
        resJob := r
      } :=
        hTR.trans ⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      have hI1' : INV {
        t1 with
        resJob := r
      } A :=
        hI1.of_sameLinks (by
          constructor <;> intros <;> rfl) (fun _ => rfl)
      refine ⟨r, t1, hj1, hL.top hTR' ⟨A, hI1', hel⟩, hTI1, hTR'.rest.2.1.trans hc,
        hTR'.rest.1.trans hP, y, i, a, ip, js + 1,
        hG.mono (fun jj => le_of_eq (by rw [hTR'.qsame.gvec])), ?_⟩
      unfold RoundAt at hR
      rw [hjob] at hR
      obtain ⟨h1, h2, h3⟩ := hR
      change RoundAt k J (μ {
        t1 with
        resJob := r
      }) r ip (js + 1) (j + 1)
      cases r with
      | none => change ip * k ≤ J + (k - (j + 1)); omega
      | some j' =>
        obtain ⟨hm1, hm2⟩ := hμ j' rfl
        exact ⟨by omega, by omega, hm1⟩


/-- **The reservation of one insertion** succeeds, keeps the lower invariants and the top
structure's invariant, and carries the zeroing game and its round accounting. -/
theorem reservation_cost {TI : Core → Prop} {μ : Core → Nat} {J k n R : Nat} {cap : Params →
  Nat} {L : List Nat}
    {s : Core} (hTC : TopContract TI μ J cap) (h0 : ResInv TI k J n R μ L s 0 s) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T) :
    ∃ t', (reservation k).run s = .ok () t' ∧ LowInv t' L ∧ TI t' ∧ t'.count = s.count ∧
      t'.P = s.P ∧ ∃ y i a ip js, GameInv n R t' y i a ip ∧ RoundOK k J μ t' ip js := by
  obtain ⟨t', hrun, hres⟩ := reservation_ok (ResInv TI k J n R μ L s)
    (fun t => LowInv t L ∧ TI t ∧ t.count = s.count ∧ t.P = s.P ∧ t.resJob = none ∧
      ∀ c, gval t c = 0) h0 (resInv_step hTC hn hsize hcap hI5)
  refine ⟨t', hrun, ?_⟩
  rcases hres with ⟨hL, hT, hc, hP, y, i, a, ip, js, hG, hR⟩ | ⟨hL, hT, hc, hP, hnone, hz⟩
  · refine ⟨hL, hT, hc, hP, y, i, a, ip, js, hG, ?_⟩
    unfold RoundOK
    unfold RoundAt at hR
    cases hj : t'.resJob with
    | none => rw [hj] at hR; simp only [Nat.sub_self, Nat.add_zero] at hR; exact Or.inr hR
    | some job => rw [hj] at hR; simp only [Nat.sub_self, Nat.add_zero] at hR; exact hR
  · refine ⟨hL, hT, hc, hP, 0, ⟨0, hn⟩, fun _ => 0, 0, 0,
      GameInv.reset (fun jj => by unfold gvec; rw [hz]; simp) _, ?_⟩
    unfold RoundOK; rw [hnone]; exact Or.inl hz

end OrderMaintenance.Proof
