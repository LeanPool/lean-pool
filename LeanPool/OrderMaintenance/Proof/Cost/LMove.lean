/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Labels


/-!
# Lemma C3 across chunk-split moves

A chunk-split move carries a unit (a quiet group, or a whole family) from one end of the splitting
chunk `x` to the adjacent end of a sibling `dst`. The moved groups get fresh labels pushed at that
end and stop being children; the sibling's arrivals and pushes grow by the unit's length.

`linv_cmove_core` handles every field but the gaps and the label range, which depend on the
direction and are proved separately.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- **The group-label invariant across a chunk-split move**, given the gaps and ranges after it. -/
theorem linv_cmove_core {s s' : Core} {A : Abs} {s₀ δ δu : Nat → Nat}
    {lg lg' : LGh} {x dst : Nat} {u labs : List Nat} (hI : INV s A)
    (hC : CInvE s A.elist δ δu s₀ x) (hL : LInv s lg s₀ δ δu)
    (M : CMoveSpec s s' x dst u labs) (hxL : LiveC s x) (hst : cSt s x = .splitting)
    (hdst : dst = cLl s x ∨ dst = cRr s x) (hu : ∀ g ∈ u, LiveG s g ∧ gC s g = x)
    (hk : u.length ≤ 3) (hunits : units s' x + 1 = units s x)
    (hm : (u.map fun g => gSz s g).sum ≤ cSz s x) (hcl : FamClosed s u)
    (hchild : ∀ g, lg'.child g = if g ∈ u then false else lg.child g)
    (hhv : lg'.hv = lg.hv) (hcs : lg'.cs = lg.cs) (hrs : lg'.rs = lg.rs) (hins : lg'.ins = lg.ins)
    (he0 : lg'.e0 = lg.e0)
    (hpb : ∀ c, lg'.pb c ≤ lg'.arB c + lg'.rs c + lg'.cs c)
    (hpf : ∀ c, lg'.pf c ≤ lg'.arF c + lg'.rs c + lg'.cs c)
    (harr : ∀ c, lg'.arB c + lg'.arF c = lg.arB c + lg.arF c + if c = dst then u.length else 0)
    (hgaps : ∀ g, LiveG s' g → g ≠ cLs s' (gC s' g) →
      gL s' g + s'.P.groupSpacing / 2 ^ lg'.hv (gC s' g) ≤ gL s' (gN s' g))
    (hrange : ∀ g, LiveG s' g →
      cG s'.P ≤ gL s' g + lg'.pf (gC s' g) * s'.P.groupSpacing ∧
        gL s' g ≤ cG s'.P + lg'.pb (gC s' g) * s'.P.groupSpacing) :
    LInv s' lg' s₀ δ δu := by
  have F := M.gfields
  have Fx := hC.cfam x hxL hst
  have hxy := Fx.lx hI hxL
  have hxz := Fx.rx hI hxL
  have hyz := Fx.lr hI hxL
  have hxd : x ≠ dst := by
    rcases hdst with rfl | rfl
    · exact Ne.symm hxy
    · exact Ne.symm hxz
  have hdov : cSt s dst = .overflow := by
    rcases hdst with rfl | rfl
    · exact Fx.lSt
    · exact Fx.rSt
  have hLC : ∀ c, LiveC s' c ↔ LiveC s c := by intro c; simp only [LiveC, M.Csize]
  have hLv : ∀ z, LiveG s' z ↔ LiveG s z := M.liveG
  -- the family of a splitting chunk keeps its size
  have hfam : ∀ x', LiveC s x' → cSt s x' = .splitting → famC s' x' = famC s x' := by
    intro x' hx' hs'
    unfold famC
    rw [M.cl, M.cr, M.csz, M.csz, M.csz]
    by_cases hxx : x' = x
    · subst hxx
      rw [ite_eq_right hxy, ite_eq_left rfl, ite_eq_right hxz]
      rcases hdst with rfl | rfl
      · rw [ite_eq_left rfl, ite_eq_right hyz.symm]; omega
      · rw [ite_eq_right hyz, ite_eq_left rfl]; omega
    · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ :=
        Fx.disjoint (hC.cfam x' hx' hs') (Ne.symm hxx) hst hs'
      have hnd1 : cLl s x' ≠ dst := by
        rcases hdst with rfl | rfl
        · exact d5
        · exact d6
      have hnd2 : x' ≠ dst := by
        rcases hdst with rfl | rfl
        · exact d1
        · exact d2
      have hnd3 : cRr s x' ≠ dst := by
        rcases hdst with rfl | rfl
        · exact d7
        · exact d8
      rw [ite_eq_right d3, ite_eq_right hnd1, ite_eq_right hxx, ite_eq_right hnd2,
        ite_eq_right d4, ite_eq_right hnd3]
  have hcszq : ∀ d, d ≠ x → d ≠ dst → cSz s' d = cSz s d := by
    intro d h1 h2; rw [M.csz, ite_eq_right h1, ite_eq_right h2]
  -- groups by chunk
  have hgrp : ∀ c z, z ∈ GrpsC s' c ↔ LiveG s z ∧ (if z ∈ u then dst else gC s z) = c := by
    intro c z; rw [mem_GrpsC, hLv, (F z).2.2.2.2.2.2.2.2.2.2]
  -- charge terms
  have hterm : ∀ z, LiveG s z → chTerm s' lg' z ≤ if z ∉ u then chTerm s lg z else 0 := by
    intro z hz
    have hft : famT s' z = famT s z := by
      unfold famT; rw [(F z).2.2.2.1, (F z).2.2.2.2.1, (F _).1, (F z).1, (F _).1]
    unfold chTerm
    rw [(F z).2.1, (F z).2.2.2.1, (F z).1, hft, M.P, hchild, hchild]
    by_cases hzu : z ∈ u
    · rw [ite_eq_right (not_not.mpr hzu), ite_eq_left hzu]
      by_cases hs : gSt s z = .splitting
      · have hl : gLl s z ∈ u := ((hcl z hz hs).1).mpr hzu
        rw [ite_eq_left hl]; simp [hs]
      · simp [hs]
    · rw [ite_eq_left hzu, ite_eq_right hzu]
      by_cases hs : gSt s z = .splitting
      · have hl : gLl s z ∉ u := fun h => hzu (((hcl z hz hs).1).mp h)
        rw [ite_eq_right hl]
      · simp only [hs, false_and, ite_false]; exact le_rfl
  have hcharge : ∀ c, charge s' lg' c ≤ charge s lg c := by
    intro c
    rw [charge_eq, charge_eq]
    calc ∑ z ∈ GrpsC s' c, chTerm s' lg' z
        ≤ ∑ z ∈ GrpsC s' c, (if z ∉ u then chTerm s lg z else 0) :=
          Finset.sum_le_sum fun z hz => hterm z ((hgrp c z).mp hz).1
      _ = ∑ z ∈ (GrpsC s' c).filter (· ∉ u), chTerm s lg z := (Finset.sum_filter _ _).symm
      _ ≤ ∑ z ∈ GrpsC s c, chTerm s lg z := by
          apply Finset.sum_le_sum_of_subset
          intro z hz
          rw [Finset.mem_filter, hgrp] at hz
          rw [ite_eq_right hz.2] at hz
          exact mem_GrpsC.mpr hz.1
  -- pending roots
  have hpend : ∀ c, pending s' lg' c ≤ pending s lg c + if c = dst then u.length else 0 := by
    intro c
    unfold pending
    have hsub : (GrpsC s' c).filter (fun g => lg'.child g = false ∧ gSt s' g ≠ .splitting) ⊆
        (GrpsC s c).filter (fun g => lg.child g = false ∧ gSt s g ≠ .splitting) ∪
          (if c = dst then u.toFinset else ∅) := by
      intro z hz
      rw [Finset.mem_filter, hgrp, hchild, (F z).2.1] at hz
      rw [Finset.mem_union, Finset.mem_filter, mem_GrpsC]
      by_cases hzu : z ∈ u
      · right; rw [ite_eq_left hzu] at hz; rw [ite_eq_left hz.1.2.symm]; exact
        List.mem_toFinset.mpr hzu
      · left; rw [ite_eq_right hzu] at hz; rw [ite_eq_right hzu] at hz; exact ⟨hz.1, hz.2⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
    split
    · exact Nat.add_le_add_left (List.toFinset_card_le u) _
    · simp
  have hunits' : ∀ x', LiveC s x' → cSt s x' = .splitting → x' ≠ x → units s' x' = units s x' := by
    intro x' _ hs' hxx
    have hdx : dst ≠ x' := by intro e; rw [e, hs'] at hdov; cases hdov
    apply units_congr; intro z
    unfold UnitG
    rw [hLv, (F z).2.2.2.2.2.2.2.2.2.2, (F z).2.1]
    by_cases hzu : z ∈ u
    · rw [ite_eq_left hzu]
      have := (hu z hzu).2
      constructor
      · rintro ⟨-, h, -⟩; exact absurd h hdx
      · rintro ⟨-, h, -⟩; exact absurd (this.symm.trans h) (Ne.symm hxx)
    · rw [ite_eq_right hzu]
  refine
    { gaps := hgaps, range := hrange, hv := ?_, pb := hpb, pf := hpf, roots := ?_, claim2 := ?_,
      insQ := ?_, insO := ?_, insS := ?_, arrS := ?_, arrN := ?_, e0 := ?_, famChild := ?_ }
  · intro c; rw [hhv, hcs, hrs]; exact hL.hv c
  · intro d hd; rw [hLC] at hd
    have h1 := hL.roots d hd
    have h2 := hpend d
    have h3 := harr d
    rw [hrs]
    split at h2 <;> split at h3 <;> omega
  · intro d hd; rw [hLC] at hd
    have h1 := hL.claim2 d hd
    have h2 := hcharge d
    rw [hcs, hins, M.P]; omega
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    have h1 : d ≠ x := by intro e; rw [e, hst] at hds; cases hds
    have h2 : d ≠ dst := by intro e; rw [e, hdov] at hds; cases hds
    rw [hins, he0, hcszq d h1 h2, M.P]; exact hL.insQ d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    obtain ⟨hsL, hss, -⟩ := hC.covf d hd hds
    rw [hins, M.csrc, hfam _ hsL hss]; exact hL.insO d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    rw [hins, hfam d hd hds, M.P]; exact hL.insS d hd hds
  · intro x' hx' hxs'; rw [hLC] at hx'; rw [M.cst] at hxs'
    have h1 := hL.arrS x' hx' hxs'
    rw [M.cl, M.cr, hfam x' hx' hxs', M.P]
    by_cases hxx : x' = x
    · subst hxx
      have e1 := harr (cLl s x')
      have e2 := harr (cRr s x')
      rcases hdst with rfl | rfl
      · rw [ite_eq_left rfl] at e1; rw [ite_eq_right hyz.symm] at e2; omega
      · rw [ite_eq_right hyz] at e1; rw [ite_eq_left rfl] at e2; omega
    · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ :=
        Fx.disjoint (hC.cfam x' hx' hxs') (Ne.symm hxx) hst hxs'
      have hnd1 : cLl s x' ≠ dst := by
        rcases hdst with rfl | rfl
        · exact d5
        · exact d6
      have hnd3 : cRr s x' ≠ dst := by
        rcases hdst with rfl | rfl
        · exact d7
        · exact d8
      have e1 := harr (cLl s x'); rw [ite_eq_right hnd1] at e1
      have e2 := harr (cRr s x'); rw [ite_eq_right hnd3] at e2
      rw [hunits' x' hx' hxs' hxx]; omega
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    have h2 : d ≠ dst := by intro e; rw [e, hdov] at hds; exact hds rfl
    have e1 := harr d; rw [ite_eq_right h2] at e1
    have := hL.arrN d hd hds
    rw [M.P]; omega
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    have h1 : d ≠ x := by intro e; rw [e, hst] at hds; cases hds
    have h2 : d ≠ dst := by intro e; rw [e, hdov] at hds; cases hds
    rw [he0, hcszq d h1 h2]; exact hL.e0 d hd hds
  · intro p hp hps
    rw [hLv] at hp; rw [(F p).2.1] at hps
    rw [(F p).2.2.2.1, (F p).2.2.2.2.1, hchild, hchild]
    have hc := hcl p hp hps
    by_cases hpu : p ∈ u
    · rw [ite_eq_left (hc.1.mpr hpu), ite_eq_left (hc.2.mpr hpu)]
    · rw [ite_eq_right (fun h => hpu (hc.1.mp h)), ite_eq_right (fun h => hpu (hc.2.mp h))]
      exact hL.famChild p hp hps

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Facts for the two directions -/

/-- Across a chunk boundary, the last group of a chunk is followed by the first of the next. -/
theorem INV.gN_cLs {s : Core} {A : Abs} (hI : INV s A) {y x : Nat} (hy : y ∈ A.chunks)
    (hyx : cN s y = x) (hx0 : x ≠ NIL) (hyne : cF s y ≠ NIL) (hxne : cF s x ≠ NIL) :
    gN s (cLs s y) = cF s x := by
  obtain ⟨l1, l2, e⟩ := succOf_split ((hI.cList.next y hy).symm.trans hyx) hx0
  obtain ⟨-, tx, htx⟩ := hI.run_ne_nil hxne
  obtain ⟨-, ty, hty⟩ := hI.run_ne_nil hyne
  have hlast : cLs s y = (A.grps y).getLastD NIL := (hI.cEnds y hy).2
  obtain ⟨ry, hry⟩ : ∃ ry, A.grps y = ry ++ [cLs s y] := by
    rw [hlast, hty]
    obtain ⟨r, b, hb⟩ : ∃ r b, cF s y :: ty = r ++ [b] := by
      rcases List.eq_nil_or_concat (cF s y :: ty) with h | ⟨r, b, h⟩
      · simp at h
      · exact ⟨r, b, by rw [h, List.concat_eq_append]⟩
    exact ⟨r, by rw [hb]; simp⟩
  have hg : A.glist = (l1.flatMap A.grps ++ ry) ++ cLs s y :: cF s x ::
      (tx ++ l2.flatMap A.grps) := by
    simp only [Abs.glist, e, List.flatMap_append, List.flatMap_cons, hry, htx]; simp
  have hm : cLs s y ∈ A.glist := by rw [hg]; simp
  rw [hI.gList.next _ hm, hg, succOf_mid (hg ▸ hI.gList.nodup)]; rfl

/-- The labels pushed at the back: `b₀, b₀ + D, …`, from the centre or after `p`. -/
theorem pushBackLabs_vals {s : Core} {center D B : Nat} :
    ∀ {k : Nat} {prev : Option Nat} {labs : List Nat},
      (pushBackLabs center D B prev k).run s = .ok labs s →
      labs = (List.range k).map fun i => (match prev with | none => center | some p => p + D) +
        i * D
  | 0, prev, labs, h => by
    cases prev <;> (unfold pushBackLabs at h; cases h; rfl)
  | k + 1, prev, labs, h => by
    have rest : ∀ l, (pushBackLabs center D B (some l) k >>= fun r => pure (l :: r) : CM (List
      Nat)).run s
        = .ok labs s → labs = (List.range (k + 1)).map fun i => l + i * D := by
      intro l hl
      rw [run_bind] at hl
      rcases pushBackLabs_run s center D B k (some l) with ⟨r, hr, -⟩ | ⟨msg, hr⟩
      · rw [hr] at hl
        have ih := pushBackLabs_vals hr
        have hl' : EStateM.Result.ok (l :: r) s = .ok labs s := hl
        cases hl'
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, ih]
        simp only [Nat.zero_mul, Nat.add_zero, List.cons.injEq, true_and]
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, Nat.succ_mul]; omega
      · rw [hr] at hl; cases hl
    cases prev with
    | none => unfold pushBackLabs at h; exact rest center (by simpa using h)
    | some p =>
      unfold pushBackLabs at h
      simp only at h
      rw [run_bind, run_after] at h
      by_cases hg : p + D ≥ 1 <<< B ∨ p + D ≤ p
      · rw [ite_eq_left hg] at h; cases h
      · rw [ite_eq_right hg] at h; exact rest (p + D) h

/-- The labels pushed at the front: `…, n₀ − 2D, n₀ − D`, before `n` (or the centre's `n₀`). -/
theorem pushFrontLabs_vals {s : Core} {center D : Nat} :
    ∀ {k : Nat} {nxt : Option Nat} {labs : List Nat},
      (pushFrontLabs center D nxt k).run s = .ok labs s →
      labs = (List.range k).map
          (fun i => (match nxt with | none => center + D | some n => n) - (k - i) * D) ∧
        k * D ≤ (match nxt with | none => center + D | some n => n) ∧ (k ≠ 0 → D ≠ 0 ∨ nxt = none)
  | 0, nxt, labs, h => by
    cases nxt <;> (unfold pushFrontLabs at h; cases h; simp)
  | k + 1, nxt, labs, h => by
    have rest : ∀ l, (pushFrontLabs center D (some l) k >>= fun r => pure (r ++ [l]) : CM (List
      Nat)).run s
        = .ok labs s →
        labs = (List.range (k + 1)).map (fun i => (l + D) - (k + 1 - i) * D) ∧ k * D ≤ l := by
      intro l hl
      rw [run_bind] at hl
      rcases pushFrontLabs_run s center D k (some l) with ⟨r, hr, -⟩ | ⟨msg, hr⟩
      · rw [hr] at hl
        obtain ⟨ih, hk, -⟩ := pushFrontLabs_vals hr
        have hl' : EStateM.Result.ok (r ++ [l]) s = .ok labs s := hl
        cases hl'
        refine ⟨?_, hk⟩
        rw [List.range_succ, List.map_append, ih]
        simp only [List.map_cons, List.map_nil]
        congr 1
        · refine List.map_congr_left fun i hi => ?_
          have hi' : i < k := List.mem_range.mp hi
          have : (k + 1 - i) * D = (k - i) * D + D := by
            rw [show k + 1 - i = (k - i) + 1 by omega, Nat.add_mul, Nat.one_mul]
          rw [this]; omega
        · rw [Nat.add_sub_cancel_left, Nat.one_mul, Nat.add_sub_cancel]
      · rw [hr] at hl; cases hl
    cases nxt with
    | none =>
      unfold pushFrontLabs at h
      obtain ⟨h1, h2⟩ := rest center (by simpa using h)
      refine ⟨h1, ?_, fun _ => Or.inr rfl⟩
      change (k + 1) * D ≤ center + D
      rw [Nat.add_mul, Nat.one_mul]; omega
    | some n =>
      unfold pushFrontLabs at h
      simp only at h
      rw [run_bind, run_before] at h
      by_cases hg : n < D ∨ D = 0
      · rw [ite_eq_left hg] at h; cases h
      · rw [ite_eq_right hg] at h
        simp only [not_or] at hg
        obtain ⟨h1, h2⟩ := rest (n - D) h
        have e : n - D + D = n := by omega
        rw [e] at h1
        refine ⟨h1, ?_, fun _ => Or.inl hg.2⟩
        change (k + 1) * D ≤ n
        rw [Nat.add_mul, Nat.one_mul]; omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The chunk ends after a move to the left sibling. -/
theorem cmoveL_ends {s : Core} {x : Nat} {u labs : List Nat} (hxy : x ≠ cLl s x)
    (hx : x < s.C.size) (hy : cLl s x < s.C.size) :
    cLs (cmoveLState s x u labs) (cLl s x) = u.getLastD NIL ∧
      cLs (cmoveLState s x u labs) x = (if cLs s x = u.getLastD NIL then NIL else cLs s x) := by
  have hCs : (moveGroupsLeft s x (cLl s x) u labs).C.size = s.C.size := by simp [moveGroupsLeft]
  have hC : ∀ c, (cmoveLState s x u labs).C.getX c = _ := fun c =>
    cmoveSizes_C (t := moveGroupsLeft s x (cLl s x) u labs) (u := u) hxy (by rw [hCs]; exact hx)
      (by rw [hCs]; exact hy) c
  have hCm : ∀ c, (moveGroupsLeft s x (cLl s x) u labs).C.getX c = _ := fun c =>
    moveGroupsLeft_C (s := s) (u := u) (labs := labs) hxy hx hy c
  constructor
  · simp only [cLs]; rw [hC, ite_eq_right (Ne.symm hxy), ite_eq_left rfl, hCm, ite_eq_left rfl]
  · simp only [cLs]; rw [hC, ite_eq_left rfl, hCm, ite_eq_right hxy, ite_eq_left rfl]
    split <;> rfl

/-- The chunk ends after a move to the right sibling. -/
theorem cmoveR_ends {s : Core} {x : Nat} {u labs : List Nat} (hxz : x ≠ cRr s x)
    (hx : x < s.C.size) (hz : cRr s x < s.C.size) :
    cF (cmoveRState s x u labs) (cRr s x) = u.headD NIL ∧
      cLs (cmoveRState s x u labs) (cRr s x) =
        (if cF s (cRr s x) = NIL then u.getLastD NIL else cLs s (cRr s x)) ∧
      cLs (cmoveRState s x u labs) x =
        (if cF s x = u.headD NIL then NIL else gP s (u.headD NIL)) := by
  have hCs : (moveGroupsRight s x (cRr s x) u labs).C.size = s.C.size := by simp [moveGroupsRight]
  have hC : ∀ c, (cmoveRState s x u labs).C.getX c = _ := fun c =>
    cmoveSizes_C (t := moveGroupsRight s x (cRr s x) u labs) (u := u) hxz (by rw [hCs]; exact hx)
      (by rw [hCs]; exact hz) c
  have hCm : ∀ c, (moveGroupsRight s x (cRr s x) u labs).C.getX c = _ := fun c =>
    moveGroupsRight_C (s := s) (u := u) (labs := labs) hxz hx hz c
  refine ⟨?_, ?_, ?_⟩
  · simp only [cF]; rw [hC, ite_eq_right (Ne.symm hxz), ite_eq_left rfl, hCm, ite_eq_left rfl]
  · simp only [cLs]; rw [hC, ite_eq_right (Ne.symm hxz), ite_eq_left rfl, hCm, ite_eq_left rfl]
  · simp only [cLs]; rw [hC, ite_eq_left rfl, hCm, ite_eq_right hxz, ite_eq_left rfl]
    split <;> rfl

/-- A live group's chunk is not empty. -/
theorem INV.cF_ne_of_live {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : LiveG s g) :
    cF s (gC s g) ≠ NIL := by
  obtain ⟨hc, hgc⟩ := hI.mem_glist (hI.mem_glist_iff.mpr hg)
  rw [(hI.cEnds _ hc).1]
  cases h : A.grps (gC s g) with
  | nil => rw [h] at hgc; simp at hgc
  | cons a t =>
    simp only [List.headD_cons]
    intro e; subst e
    exact hI.gList.nonil (A.grps_sub_glist hc (by rw [h]; simp))

/-- The shape of a unit: one group, or three consecutive groups. -/
def UnitShape (s : Core) (u : List Nat) : Prop :=
  (∃ a, u = [a]) ∨ (∃ a b c, u = [a, b, c] ∧ gN s a = b ∧ gN s b = c)

/-- A group outside a unit followed by a member of it precedes the unit's head. -/
theorem UnitShape.pred {s : Core} {A : Abs} (hI : INV s A) {u : List Nat} (hsh : UnitShape s u)
    (hu : ∀ g ∈ u, LiveG s g) {h : Nat} (hh : LiveG s h) (hnu : h ∉ u) (hm : gN s h ∈ u) :
    gN s h = u.headD NIL := by
  have hhg := hI.mem_glist_iff.mpr hh
  have inj : ∀ a, LiveG s a → gN s a = gN s h → a = h := by
    intro a ha e
    have hn : gN s h ≠ NIL := by
      intro e0; rw [e0] at hm
      exact hI.gList.nonil (by rw [← e0] at hm ⊢; exact hI.mem_glist_iff.mpr (hu _ hm))
    have h1 := hI.gP_gN (hI.mem_glist_iff.mpr ha) (by rw [e]; exact hn)
    have h2 := hI.gP_gN hhg hn
    rw [e] at h1; exact h1.symm.trans h2
  rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, hab, hbc⟩
  · simp only [List.mem_singleton] at hm; simp [hm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hnu
    rcases hm with hm | hm | hm
    · simp [hm]
    · exfalso; exact hnu (Or.inl (inj a (hu a (by simp)) (hab.trans hm.symm)).symm)
    · exfalso; exact hnu (Or.inr (Or.inl (inj b (hu b (by simp)) (hbc.trans hm.symm)).symm))

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem CMoveSpec.gL_out {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) {g : Nat} (hg : g ∉ u) : gL s' g = gL s g := by
  simp only [gL, M.G g, ite_eq_right hg]

theorem CMoveSpec.gL_in {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) {g : Nat} (hg : g ∈ u) :
    gL s' g = labs.getD (u.idxOf g) 0 := by
  simp only [gL, M.G g, ite_eq_left hg]

/-- A gap away from the moved unit is unchanged. -/
theorem gaps_frame {s s' : Core} {s₀ δ δu : Nat → Nat} {lg lg' : LGh} {x dst : Nat}
    {u labs : List Nat} (M : CMoveSpec s s' x dst u labs) (hL : LInv s lg s₀ δ δu)
    (hhv : lg'.hv = lg.hv) {h : Nat} (hh : LiveG s h) (hnu : h ∉ u) (hnu' : gN s h ∉ u)
    (hl : h ≠ cLs s (gC s h)) :
    gL s' h + s'.P.groupSpacing / 2 ^ lg'.hv (gC s' h) ≤ gL s' (gN s' h) := by
  have F := M.gfields
  rw [(F h).2.2.2.2.2.1, (F h).2.2.2.2.2.2.2.2.2.2, ite_eq_right hnu, M.gL_out hnu, M.gL_out hnu',
    M.P,
    hhv]
  exact hL.gaps h hh hl

/-- The gaps after a move to the left sibling. -/
theorem gaps_left {s s' : Core} {A : Abs} {s₀ δ δu : Nat → Nat} {lg lg' : LGh} {x : Nat}
    {u labs : List Nat} (hI : INV s A) (hL : LInv s lg s₀ δ δu)
    (M : CMoveSpec s s' x (cLl s x) u labs) (hxy : cLl s x ≠ x) (hyx : cN s (cLl s x) = x)
    (hyC : LiveC s (cLl s x)) (hxL : LiveC s x) (hne : cF s x ≠ NIL) (hsh : UnitShape s u)
    (hhead : u.headD NIL = cF s x) (hnd : u.Nodup) (hu : ∀ g ∈ u, LiveG s g ∧ gC s g = x)
    (hlabs : labs = (List.range u.length).map fun i =>
      (if cF s (cLl s x) = NIL then cG s.P else gL s (cLs s (cLl s x)) + s.P.groupSpacing) + i
        * s.P.groupSpacing)
    (hlast' : cLs s' (cLl s x) = u.getLastD NIL)
    (hxlast' : cLs s' x = if cLs s x = u.getLastD NIL then NIL else cLs s x)
    (hhv : lg'.hv = lg.hv) :
    ∀ g, LiveG s' g → g ≠ cLs s' (gC s' g) →
      gL s' g + s'.P.groupSpacing / 2 ^ lg'.hv (gC s' g) ≤ gL s' (gN s' g) := by
  have F := M.gfields
  have hyA : cLl s x ∈ A.chunks := (hI.cAlloc _).mpr hyC
  have hlastu : u.getLastD NIL ∈ u := by
    rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, -, -⟩ <;> simp
  have hheadu : u.headD NIL ∈ u := by
    rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, -, -⟩ <;> simp
  generalize cLl s x = y at *
  intro h hh hl
  rw [M.liveG] at hh
  by_cases hu' : h ∈ u
  · rw [(F h).2.2.2.2.2.2.2.2.2.2, ite_eq_left hu', hlast'] at hl
    rw [(F h).2.2.2.2.2.1, (F h).2.2.2.2.2.2.2.2.2.2, ite_eq_left hu', M.P, hhv]
    have hq : s.P.groupSpacing / 2 ^ lg.hv y ≤ s.P.groupSpacing := Nat.div_le_self _ _
    generalize s.P.groupSpacing / 2 ^ lg.hv y = q at hq
    rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, hab, hbc⟩
    · simp only [List.mem_singleton] at hu'; subst hu'; simp at hl
    · have hab' : a ≠ b := by intro e; subst e; simp at hnd
      have hac' : a ≠ c := by intro e; subst e; simp at hnd
      have hbc' : b ≠ c := by intro e; subst e; simp at hnd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with rfl | rfl | rfl
      · rw [hab, M.gL_in (by simp), M.gL_in (by simp), hlabs]
        simp [hab', List.range_succ]; omega
      · rw [hbc, M.gL_in (by simp), M.gL_in (by simp), hlabs]
        simp [hab', hac', hbc', List.range_succ]; omega
      · simp at hl
  · rw [(F h).2.2.2.2.2.2.2.2.2.2, ite_eq_right hu'] at hl
    have hhA := hI.mem_glist_iff.mpr hh
    by_cases hhx : gC s h = x
    · -- a group of `x` behind the unit
      have hlx : h ≠ cLs s x := by
        rw [hhx, hxlast'] at hl
        split at hl
        · next he => intro e; rw [e, he] at hu'; exact hu' hlastu
        · exact hl
      have hnu : gN s h ∉ u := by
        intro hm
        have e := hsh.pred hI (fun g hg => (hu g hg).1) hh hu' hm
        rw [hhead] at e
        exact hI.not_before_first hne hhA hhx e
      exact gaps_frame M hL hhv hh hu' hnu (by rw [hhx]; exact hlx)
    · by_cases hhy : gC s h = y
      · by_cases hly : h = cLs s y
        · -- the old last group of `y` meets the unit's head
          have hyne : cF s y ≠ NIL := by rw [← hhy]; exact hI.cF_ne_of_live hh
          have hN : gN s h = cF s x := by
            rw [hly]; exact hI.gN_cLs hyA hyx (by unfold NIL; have := hxL.1; omega) hyne hne
          rw [(F h).2.2.2.2.2.1, (F h).2.2.2.2.2.2.2.2.2.2, ite_eq_right hu', M.gL_out hu', hN,
            ← hhead,
            M.gL_in hheadu, hlabs, M.P, hhv, hhy, ite_eq_right hyne, ← hly]
          have hq : s.P.groupSpacing / 2 ^ lg.hv y ≤ s.P.groupSpacing := Nat.div_le_self _ _
          have h0 : u.idxOf (u.headD NIL) = 0 := by
            rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, -, -⟩ <;> simp
          have hlen : 0 < u.length := List.length_pos_of_mem hheadu
          rw [h0]
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlen]
          simp only [Option.map_some, Option.getD_some, Nat.zero_mul, Nat.add_zero]
          omega
        · have hn := hI.next_in_chunk hh (by rw [hhy]; exact hly)
          have hnu : gN s h ∉ u := by
            intro hm; have := (hu _ hm).2; rw [hn.2, hhy] at this; exact hxy this
          exact gaps_frame M hL hhv hh hu' hnu (by rw [hhy]; exact hly)
      · have hd := M.fl (gC s h) hhx hhy
        rw [hd.2] at hl
        have hn := hI.next_in_chunk hh hl
        have hnu : gN s h ∉ u := by
          intro hm; have := (hu _ hm).2; rw [hn.2] at this; exact hhx this
        exact gaps_frame M hL hhv hh hu' hnu hl

/-- The gaps after a move to the right sibling. -/
theorem gaps_right {s s' : Core} {A : Abs} {s₀ δ δu : Nat → Nat} {lg lg' : LGh} {x : Nat}
    {u labs : List Nat} (hI : INV s A) (hL : LInv s lg s₀ δ δu)
    (M : CMoveSpec s s' x (cRr s x) u labs) (hxz : cRr s x ≠ x) (hxzN : cN s x = cRr s x)
    (hzC : LiveC s (cRr s x)) (hxL : LiveC s x) (hne : cF s x ≠ NIL) (hsh : UnitShape s u)
    (hlastu' : u.getLastD NIL = cLs s x) (hnd : u.Nodup) (hu : ∀ g ∈ u, LiveG s g ∧ gC s g = x)
    (hlabs : labs = (List.range u.length).map fun i =>
      (if cF s (cRr s x) = NIL then cG s.P + s.P.groupSpacing else gL s (cF s (cRr s x))) -
        (u.length - i) * s.P.groupSpacing)
    (hkD : u.length * s.P.groupSpacing ≤
      (if cF s (cRr s x) = NIL then cG s.P + s.P.groupSpacing else gL s (cF s (cRr s x))))
    (hzlast' : cLs s' (cRr s x) = if cF s (cRr s x) = NIL then u.getLastD NIL else cLs s (cRr s x))
    (hxlast' : cLs s' x = if cF s x = u.headD NIL then NIL else gP s (u.headD NIL))
    (hhv : lg'.hv = lg.hv) :
    ∀ g, LiveG s' g → g ≠ cLs s' (gC s' g) →
      gL s' g + s'.P.groupSpacing / 2 ^ lg'.hv (gC s' g) ≤ gL s' (gN s' g) := by
  have F := M.gfields
  have hxA : x ∈ A.chunks := (hI.cAlloc _).mpr hxL
  have hlastu : u.getLastD NIL ∈ u := by
    rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, -, -⟩ <;> simp
  generalize cRr s x = z at *
  -- the unit's last group meets the old first group of `z`
  have hmeet : cF s z ≠ NIL → gN s (cLs s x) = cF s z ∧ cF s z ∉ u := by
    intro hzne
    refine ⟨hI.gN_cLs hxA hxzN (by unfold NIL; have := hzC.1; omega) hne hzne, fun hm => ?_⟩
    obtain ⟨hzA, t, ht⟩ := hI.run_ne_nil hzne
    have := hI.chk z hzA (cF s z) (by rw [ht]; simp)
    rw [(hu _ hm).2] at this; exact hxz this.symm
  intro h hh hl
  rw [M.liveG] at hh
  by_cases hu' : h ∈ u
  · rw [(F h).2.2.2.2.2.2.2.2.2.2, ite_eq_left hu', hzlast'] at hl
    rw [(F h).2.2.2.2.2.1, (F h).2.2.2.2.2.2.2.2.2.2, ite_eq_left hu', M.P, hhv]
    have hq : s.P.groupSpacing / 2 ^ lg.hv z ≤ s.P.groupSpacing := Nat.div_le_self _ _
    generalize s.P.groupSpacing / 2 ^ lg.hv z = q at hq
    -- the last member: its successor is the old first group of `z`
    have hlast_case : h = u.getLastD NIL → gL s' h + q ≤ gL s' (gN s h) := by
      intro e
      by_cases hzne : cF s z = NIL
      · rw [ite_eq_left hzne] at hl; exact absurd e hl
      · obtain ⟨hN, hnu⟩ := hmeet hzne
        rw [e, hlastu', hN, M.gL_out hnu, ← hlastu', M.gL_in hlastu, hlabs]
        rw [ite_eq_right hzne] at hkD ⊢
        have hidx : u.idxOf (u.getLastD NIL) = u.length - 1 := by
          rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, -, -⟩
          · simp
          · have hab' : a ≠ b := by intro e; subst e; simp at hnd
            have hac' : a ≠ c := by intro e; subst e; simp at hnd
            have hbc' : b ≠ c := by intro e; subst e; simp at hnd
            simp [hac', hbc']
        have hlen : 0 < u.length := List.length_pos_of_mem hlastu
        rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range (by omega)]
        simp only [Option.map_some, Option.getD_some]
        rw [show u.length - (u.length - 1) = 1 by omega, Nat.one_mul]
        have : s.P.groupSpacing ≤ u.length * s.P.groupSpacing := Nat.le_mul_of_pos_left _ hlen
        omega
    rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, hab, hbc⟩
    · simp only [List.mem_singleton] at hu'; exact hlast_case (by simp [hu'])
    · have hab' : a ≠ b := by intro e; subst e; simp at hnd
      have hac' : a ≠ c := by intro e; subst e; simp at hnd
      have hbc' : b ≠ c := by intro e; subst e; simp at hnd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with rfl | rfl | rfl
      · rw [hab, M.gL_in (by simp), M.gL_in (by simp), hlabs]
        simp [hab', List.range_succ]
        simp at hkD; omega
      · rw [hbc, M.gL_in (by simp), M.gL_in (by simp), hlabs]
        simp [hab', hac', hbc', List.range_succ]
        simp at hkD; omega
      · exact hlast_case (by simp)
  · rw [(F h).2.2.2.2.2.2.2.2.2.2, ite_eq_right hu'] at hl
    have hhA := hI.mem_glist_iff.mpr hh
    by_cases hhx : gC s h = x
    · -- a group of `x` before the unit
      have hlx : h ≠ cLs s x := by intro e; rw [e, ← hlastu'] at hu'; exact hu' hlastu
      have hnu : gN s h ∉ u := by
        intro hm
        have e := hsh.pred hI (fun g hg => (hu g hg).1) hh hu' hm
        by_cases hf : cF s x = u.headD NIL
        · rw [← hf] at e; exact hI.not_before_first hne hhA hhx e
        · rw [hhx, hxlast', ite_eq_right hf] at hl
          apply hl
          have hn0 : gN s h ≠ NIL := by
            intro e0; rw [e0] at hm; exact hI.gList.nonil (hI.mem_glist_iff.mpr (hu _ hm).1)
          have := hI.gP_gN hhA hn0
          rw [e] at this; exact this.symm
      exact gaps_frame M hL hhv hh hu' hnu (by rw [hhx]; exact hlx)
    · by_cases hhz : gC s h = z
      · have hzne : cF s z ≠ NIL := by rw [← hhz]; exact hI.cF_ne_of_live hh
        rw [hhz, hzlast', ite_eq_right hzne] at hl
        have hn := hI.next_in_chunk hh (by rw [hhz]; exact hl)
        have hnu : gN s h ∉ u := by
          intro hm; have := (hu _ hm).2; rw [hn.2, hhz] at this; exact hxz this
        exact gaps_frame M hL hhv hh hu' hnu (by rw [hhz]; exact hl)
      · have hd := M.fl (gC s h) hhx hhz
        rw [hd.2] at hl
        have hn := hI.next_in_chunk hh hl
        have hnu : gN s h ∉ u := by
          intro hm; have := (hu _ hm).2; rw [hn.2] at this; exact hhx this
        exact gaps_frame M hL hhv hh hu' hnu hl

/-- Pushing at the back succeeds when every label fits. -/
theorem pushBackLabs_ok (s : Core) {center D B : Nat} (hD : 0 < D) :
    ∀ {k : Nat} {prev : Option Nat},
      (∀ j < k, (match prev with | none => center | some p => p + D) + j * D < 1 <<< B) →
      ∃ labs, (pushBackLabs center D B prev k).run s = .ok labs s
  | 0, prev, _ => by cases prev <;> exact ⟨[], rfl⟩
  | k + 1, prev, h => by
    have rest : ∀ l, (∀ j < k, l + D + j * D < 1 <<< B) →
        ∃ labs, (pushBackLabs center D B (some l) k >>= fun r => pure (l :: r) : CM (List
          Nat)).run s
          = .ok labs s := by
      intro l hl
      obtain ⟨r, hr⟩ := pushBackLabs_ok s hD (k := k) (prev := some l) hl
      exact ⟨l :: r, by rw [run_bind, hr]; rfl⟩
    cases prev with
    | none =>
      unfold pushBackLabs
      obtain ⟨labs, hl⟩ := rest center (fun j hj => by
        have := h (j + 1) (by omega); simp only [Nat.succ_mul] at this; omega)
      exact ⟨labs, by simpa using hl⟩
    | some p =>
      unfold pushBackLabs
      simp only
      rw [run_bind, run_after]
      have h0 := h 0 (by omega)
      simp only [Nat.zero_mul, Nat.add_zero] at h0
      rw [ite_eq_right (by omega)]
      obtain ⟨labs, hl⟩ := rest (p + D) (fun j hj => by
        have := h (j + 1) (by omega); simp only [Nat.succ_mul] at this; omega)
      exact ⟨labs, hl⟩

/-- Pushing at the front succeeds when every label stays nonnegative. -/
theorem pushFrontLabs_ok (s : Core) {center D : Nat} (hD : 0 < D) :
    ∀ {k : Nat} {nxt : Option Nat},
      k * D ≤ (match nxt with | none => center + D | some n => n) →
      ∃ labs, (pushFrontLabs center D nxt k).run s = .ok labs s
  | 0, nxt, _ => by cases nxt <;> exact ⟨[], rfl⟩
  | k + 1, nxt, h => by
    have rest : ∀ l, k * D ≤ l →
        ∃ labs, (pushFrontLabs center D (some l) k >>= fun r => pure (r ++ [l]) : CM (List
          Nat)).run s
          = .ok labs s := by
      intro l hl
      obtain ⟨r, hr⟩ := pushFrontLabs_ok s hD (k := k) (nxt := some l) hl
      exact ⟨r ++ [l], by rw [run_bind, hr]; rfl⟩
    rw [Nat.add_mul, Nat.one_mul] at h
    cases nxt with
    | none =>
      unfold pushFrontLabs
      obtain ⟨labs, hl⟩ := rest center (by simp only at h; omega)
      exact ⟨labs, by simpa using hl⟩
    | some n =>
      simp only at h
      unfold pushFrontLabs
      simp only
      rw [run_bind, run_before, ite_eq_right (by omega)]
      obtain ⟨labs, hl⟩ := rest (n - D) (by omega)
      exact ⟨labs, hl⟩

/-- **Room for pushes** at a sibling of a splitting chunk: with at least one unit left in `x`,
its pushes plus one more unit stay within `PC`. -/
theorem push_room {s : Core} {A : Abs} {lg : LGh} {s₀ δ δu : Nat → Nat} {x c k : Nat}
    (hC : CInvE s A.elist δ δu s₀ x) (hL : LInv s lg s₀ δ δu) (hP : GParams s.P)
    (hxL : LiveC s x) (hst : cSt s x = .splitting) (hFB : FamBound s δ s₀ x)
    (hun : 1 ≤ units s x) (hc : c = cLl s x ∨ c = cRr s x) (hk : k ≤ 3) :
    lg.pb c + k ≤ PC s.P ∧ lg.pf c + k ≤ PC s.P := by
  have Fx := hC.cfam x hxL hst
  have hgm : 0 < gmin s.P := by unfold gmin; have := hP.G4; omega
  have hU := unitsOf_mono s.P hFB.T
  have hUm : unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) ≤ unitsOf s.P s.P.T / (s.P.chunkBudget
    - 1) :=
    Nat.div_le_div_right hU
  have hA := hL.arrS x hxL hst
  unfold famC at hA
  have hF := hFB.fam
  have hδs := hFB.δs
  have hδu := hC.δu x
  have hcL : LiveC s c := by
    rcases hc with rfl | rfl
    · exact Fx.lLive
    · exact Fx.rLive
  have hco : cSt s c = .overflow := by
    rcases hc with rfl | rfl
    · exact Fx.lSt
    · exact Fx.rSt
  have hcs : cSrc s c = x := by
    rcases hc with rfl | rfl
    · exact Fx.lSrc
    · exact Fx.rSrc
  have hR := hL.roots c hcL
  have hQ := hL.claim2 c hcL
  have hO := hL.insO c hcL hco
  rw [hcs] at hO; unfold famC at hO
  have hpb := hL.pb c
  have hpf := hL.pf c
  have harr : lg.arB c + lg.arF c ≤ lg.arB (cLl s x) + lg.arF (cLl s x) + lg.arB (cRr s x) +
      lg.arF (cRr s x) := by rcases hc with rfl | rfl <;> omega
  have hcsB : lg.cs c ≤ csB s.P := by
    unfold csB; rw [Nat.le_div_iff_mul_le hgm]
    unfold IC kC
    have : lg.cs c * gmin s.P ≤ lg.ins c := by omega
    omega
  unfold PC rsB Mu kC at *
  generalize unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) = q1 at *
  generalize unitsOf s.P s.P.T / (s.P.chunkBudget - 1) = q2 at *
  constructor <;> omega

/-- The label range after a move, given the range of the pushed labels. -/
theorem range_cmove {s s' : Core} {s₀ δ δu : Nat → Nat} {lg lg' : LGh} {x dst : Nat}
    {u labs : List Nat} (M : CMoveSpec s s' x dst u labs) (hL : LInv s lg s₀ δ δu)
    (hpb : ∀ c, lg.pb c ≤ lg'.pb c) (hpf : ∀ c, lg.pf c ≤ lg'.pf c)
    (hin : ∀ i < u.length, cG s.P ≤ labs.getD i 0 + lg'.pf dst * s.P.groupSpacing ∧
      labs.getD i 0 ≤ cG s.P + lg'.pb dst * s.P.groupSpacing) :
    ∀ g, LiveG s' g → cG s'.P ≤ gL s' g + lg'.pf (gC s' g) * s'.P.groupSpacing ∧
      gL s' g ≤ cG s'.P + lg'.pb (gC s' g) * s'.P.groupSpacing := by
  intro g hg
  rw [M.liveG] at hg
  rw [M.P, (M.gfields g).2.2.2.2.2.2.2.2.2.2]
  by_cases hgu : g ∈ u
  · rw [ite_eq_left hgu, M.gL_in hgu]; exact hin _ (List.idxOf_lt_length_of_mem hgu)
  · rw [ite_eq_right hgu, M.gL_out hgu]
    have h1 := hL.range g hg
    have h2 := Nat.mul_le_mul_right s.P.groupSpacing (hpb (gC s g))
    have h3 := Nat.mul_le_mul_right s.P.groupSpacing (hpf (gC s g))
    omega

theorem cG_two (P : Params) (hB : 1 ≤ P.groupBits) : 1 <<< P.groupBits = 2 * cG P := by
  unfold cG; simp only [Nat.shiftLeft_eq, one_mul]
  rw [show P.groupBits = (P.groupBits - 1) + 1 by omega, pow_succ]; simp; ring

/-- The last group of a non-empty chunk is live and lies in it. -/
theorem INV.cLs_live {s : Core} {A : Abs} (hI : INV s A) {c : Nat} (hne : cF s c ≠ NIL) :
    LiveG s (cLs s c) ∧ gC s (cLs s c) = c := by
  obtain ⟨hc, t, ht⟩ := hI.run_ne_nil hne
  have hm : cLs s c ∈ A.grps c := by rw [(hI.cEnds c hc).2, ht]; exact getLastD_cons_mem _ _ _
  exact ⟨hI.mem_glist_iff.mp (A.grps_sub_glist hc hm), hI.chk c hc _ hm⟩

/-- The first group of a non-empty chunk is live and lies in it. -/
theorem INV.cF_live {s : Core} {A : Abs} (hI : INV s A) {c : Nat} (hne : cF s c ≠ NIL) :
    LiveG s (cF s c) ∧ gC s (cF s c) = c := by
  obtain ⟨hc, t, ht⟩ := hI.run_ne_nil hne
  have hm : cF s c ∈ A.grps c := by rw [ht]; simp
  exact ⟨hI.mem_glist_iff.mp (A.grps_sub_glist hc hm), hI.chk c hc _ hm⟩

theorem units_pos {s : Core} {x um : Nat} (h : UnitG s x um) : 1 ≤ units s x := by
  unfold units
  exact Finset.card_pos.mpr ⟨um, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1.2.1, h⟩⟩

/-- **Lemma C3 across a move to the left sibling** (the chunk drive's hook): the pushed labels fit,
and the invariant holds after the move. -/
theorem linv_cmoveL {s : Core} {A : Abs} {gh : GGh} {lg : LGh} {s₀ δ δu : Nat → Nat} {x : Nat}
    (hI : INV s A) (hG : GInv s A.elist gh (fun _ => 0)) (hP : GParams s.P) (hLP : LParams s.P)
    (hC : CInvE s A.elist δ δu s₀ x) (hL : LInv s lg s₀ δ δu) (hxL : LiveC s x)
    (hst : cSt s x = .splitting) (he : cF s x ≠ NIL) (hFB : FamBound s δ s₀ x) :
    ∃ labs, (pushLabsL s x (unitCand s x true).length).run s = .ok labs s ∧
      ∃ lg', LInv (cmoveLState s x (unitCand s x true) labs) lg' s₀ δ δu := by
  have Fx := hC.cfam x hxL hst
  have hxy := Fx.lx hI hxL
  obtain ⟨hxc, t0, ht0⟩ := hI.run_ne_nil he
  have hg0 : cF s x ∈ A.glist := A.grps_sub_glist hxc (by rw [ht0]; simp)
  have hg0L := hI.mem_glist_iff.mp hg0
  have hg0x : gC s (cF s x) = x := hI.chk x hxc _ (by rw [ht0]; simp)
  have lu := left_unit hI hG he
  have UF := unit_facts (u := unitCand s x true) (x := x) hI hG hP (by
    rcases lu with ⟨hq, h⟩ | ⟨p, hp, hps, hl, h, hok⟩
    · left; rw [h]; exact ⟨hq, rfl, hg0L, hg0x⟩
    · right
      refine ⟨p, hp, hps, by rw [h, hl], ?_⟩
      rw [h] at hok; exact (unitOK_three hok).2.2.2.2.1)
  obtain ⟨-, hnd, hmem, hone, hcl, -, -⟩ := UF
  have hsh : UnitShape s (unitCand s x true) ∧ (unitCand s x true).headD NIL = cF s x := by
    rcases lu with ⟨-, h⟩ | ⟨p, hp, hps, hl, h, -⟩
    · rw [h]; exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩
    · have F := hG.fam p hp hps
      rw [h]
      refine ⟨Or.inr ⟨_, _, _, rfl, ?_, F.rAdj⟩, rfl⟩
      rw [← hl]; exact F.lAdj
  obtain ⟨hsh, hhead⟩ := hsh
  generalize unitCand s x true = u at *
  have hk : u.length ≤ 3 := by rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, -, -⟩ <;> simp
  have hun : 1 ≤ units s x := by obtain ⟨um, -, hum, -⟩ := hone; exact units_pos hum
  obtain ⟨hpbR, -⟩ := push_room hC hL hP hxL hst hFB hun (Or.inl rfl) hk
  have hD := hLP.Dg
  have hpush := hLP.push
  have hPCD : (lg.pb (cLl s x) + u.length) * s.P.groupSpacing ≤ PC s.P * s.P.groupSpacing :=
    Nat.mul_le_mul_right _ hpbR
  rw [Nat.add_mul] at hPCD
  -- the last group of a non-empty left sibling, within range
  have hlastR : cF s (cLl s x) ≠ NIL →
      cG s.P ≤ gL s (cLs s (cLl s x)) + lg.pf (cLl s x) * s.P.groupSpacing ∧
        gL s (cLs s (cLl s x)) ≤ cG s.P + lg.pb (cLl s x) * s.P.groupSpacing := by
    intro hne
    have := hI.cLs_live hne
    have h := hL.range _ this.1; rw [this.2] at h; exact h
  -- the labels fit
  have hroom : ∀ j < u.length, (match (if cF s (cLl s x) = NIL then none
      else some (gL s (cLs s (cLl s x)))) with
        | none => cG s.P | some p => p + s.P.groupSpacing) + j * s.P.groupSpacing < 1 <<<
          s.P.groupBits := by
    intro j hj
    rw [cG_two _ hLP.Bg]
    have hjk : (j + 1) * s.P.groupSpacing ≤ u.length * s.P.groupSpacing := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hjk
    by_cases hy0 : cF s (cLl s x) = NIL
    · rw [ite_eq_left hy0]; change cG s.P + j * s.P.groupSpacing < 2 * cG s.P; omega
    · rw [ite_eq_right hy0]; change gL s (cLs s (cLl s x)) + s.P.groupSpacing + j *
      s.P.groupSpacing < 2 * cG s.P
      have := (hlastR hy0).2; omega
  obtain ⟨labs, hlabs⟩ := pushBackLabs_ok s (by omega) hroom
  refine ⟨labs, hlabs, ?_⟩
  have hlen : labs.length = u.length := pushBackLabs_len hlabs
  have hv : labs = (List.range u.length).map fun i =>
      (if cF s (cLl s x) = NIL then cG s.P else gL s (cLs s (cLl s x)) + s.P.groupSpacing) +
        i * s.P.groupSpacing := by
    rw [pushBackLabs_vals hlabs]
    by_cases hy0 : cF s (cLl s x) = NIL
    · simp only [ite_eq_left hy0]
    · simp only [ite_eq_right hy0]
  have M := cmoveL_spec (s := s) (x := x) (u := u) (labs := labs) (Ne.symm hxy) hxL.2 Fx.lLive.2
    hnd hlen (fun g hg => (hmem g hg).1.2.1)
  obtain ⟨-, hun', hle⟩ := cinv_cmove hG hC M hxL hst (Or.inl rfl) (Ne.symm hxy) hmem hnd hone
  have E := cmoveL_ends (s := s) (x := x) (u := u) (labs := labs) (Ne.symm hxy) hxL.2 Fx.lLive.2
  refine ⟨{ lg with
    child := fun g => if g ∈ u then false else lg.child g
    pb := Function.update lg.pb (cLl s x) (lg.pb (cLl s x) + u.length)
    arB := Function.update lg.arB (cLl s x) (lg.arB (cLl s x) + u.length) }, ?_⟩
  refine linv_cmove_core hI hC hL M hxL hst (Or.inl rfl) hmem hk hun' hle hcl (fun g => rfl)
    rfl rfl rfl rfl rfl ?_ (fun c => hL.pf c) ?_ ?_ ?_
  · intro c
    change Function.update lg.pb (cLl s x) _ c ≤ Function.update lg.arB (cLl s x) _ c + lg.rs c
      + lg.cs c
    by_cases hc : c = cLl s x
    · rw [hc, Function.update_self, Function.update_self]; have := hL.pb (cLl s x); omega
    · rw [Function.update_of_ne hc, Function.update_of_ne hc]; exact hL.pb c
  · intro c
    change Function.update lg.arB (cLl s x) _ c + lg.arF c = _
    by_cases hc : c = cLl s x
    · rw [hc, Function.update_self, ite_eq_left rfl]; omega
    · rw [Function.update_of_ne hc, ite_eq_right hc]; omega
  · exact gaps_left hI hL M hxy Fx.lAdj Fx.lLive hxL he hsh hhead hnd hmem hv E.1 E.2 rfl
  · refine range_cmove M hL (fun c => ?_) (fun c => le_rfl) (fun i hi => ?_)
    · change lg.pb c ≤ Function.update lg.pb (cLl s x) _ c
      by_cases hc : c = cLl s x
      · rw [hc, Function.update_self]; omega
      · rw [Function.update_of_ne hc]
    · change cG s.P ≤ labs.getD i 0 + lg.pf (cLl s x) * s.P.groupSpacing ∧
        labs.getD i 0 ≤ cG s.P + Function.update lg.pb (cLl s x) _ (cLl s x) * s.P.groupSpacing
      rw [Function.update_self, Nat.add_mul, hv, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi]
      simp only [Option.map_some, Option.getD_some]
      have hik : (i + 1) * s.P.groupSpacing ≤ u.length * s.P.groupSpacing :=
        Nat.mul_le_mul_right _ hi
      rw [Nat.add_mul, Nat.one_mul] at hik
      by_cases hy0 : cF s (cLl s x) = NIL
      · rw [ite_eq_left hy0]; omega
      · rw [ite_eq_right hy0]; have := hlastR hy0; omega

/-- **Lemma C3 across a move to the right sibling** (the chunk drive's hook). -/
theorem linv_cmoveR {s : Core} {A : Abs} {gh : GGh} {lg : LGh} {s₀ δ δu : Nat → Nat} {x : Nat}
    (hI : INV s A) (hG : GInv s A.elist gh (fun _ => 0)) (hP : GParams s.P) (hLP : LParams s.P)
    (hC : CInvE s A.elist δ δu s₀ x) (hL : LInv s lg s₀ δ δu) (hxL : LiveC s x)
    (hst : cSt s x = .splitting) (he : cF s x ≠ NIL) (hFB : FamBound s δ s₀ x) :
    ∃ labs, (pushLabsR s x (unitCand s x false).length).run s = .ok labs s ∧
      ∃ lg', LInv (cmoveRState s x (unitCand s x false) labs) lg' s₀ δ δu := by
  have Fx := hC.cfam x hxL hst
  have hxz := Fx.rx hI hxL
  obtain ⟨hxc', tl, htl⟩ := hI.run_ne_nil he
  have hE := hI.cEnds x hxc'
  have hlm : cLs s x ∈ A.grps x := by rw [hE.2, htl]; exact getLastD_cons_mem _ _ _
  have hgl : cLs s x ∈ A.glist := A.grps_sub_glist hxc' hlm
  have ru := right_unit hI hG he
  have UF := unit_facts (u := unitCand s x false) (x := x) hI hG hP (by
    rcases ru with ⟨hq, h⟩ | ⟨p, hp, hps, hr, h, hok⟩
    · left; rw [h]
      exact ⟨hq, rfl, hI.mem_glist_iff.mp hgl, hI.chk x hxc' _ hlm⟩
    · right
      refine ⟨p, hp, hps, by rw [h, hr], ?_⟩
      rw [h] at hok; exact (unitOK_three hok).2.2.2.2.1)
  obtain ⟨-, hnd, hmem, hone, hcl, -, -⟩ := UF
  have hsh : UnitShape s (unitCand s x false) ∧ (unitCand s x false).getLastD NIL = cLs s x := by
    rcases ru with ⟨-, h⟩ | ⟨p, hp, hps, hr, h, -⟩
    · rw [h]; exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩
    · have F := hG.fam p hp hps
      rw [h]
      refine ⟨Or.inr ⟨_, _, _, rfl, F.lAdj, ?_⟩, rfl⟩
      rw [← hr]; exact F.rAdj
  obtain ⟨hsh, hlastu'⟩ := hsh
  generalize unitCand s x false = u at *
  have hk : u.length ≤ 3 := by rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, -, -⟩ <;> simp
  have hk1 : 1 ≤ u.length := by rcases hsh with ⟨a, rfl⟩ | ⟨a, b, c, rfl, -, -⟩ <;> simp
  have hun : 1 ≤ units s x := by obtain ⟨um, -, hum, -⟩ := hone; exact units_pos hum
  obtain ⟨-, hpfR⟩ := push_room hC hL hP hxL hst hFB hun (Or.inr rfl) hk
  have hD := hLP.Dg
  have hpush := hLP.push
  have hPCD : (lg.pf (cRr s x) + u.length) * s.P.groupSpacing ≤ PC s.P * s.P.groupSpacing :=
    Nat.mul_le_mul_right _ hpfR
  rw [Nat.add_mul] at hPCD
  have hfirstR : cF s (cRr s x) ≠ NIL →
      cG s.P ≤ gL s (cF s (cRr s x)) + lg.pf (cRr s x) * s.P.groupSpacing ∧
        gL s (cF s (cRr s x)) ≤ cG s.P + lg.pb (cRr s x) * s.P.groupSpacing := by
    intro hne
    have := hI.cF_live hne
    have h := hL.range _ this.1; rw [this.2] at h; exact h
  have hkD : u.length * s.P.groupSpacing ≤
      (if cF s (cRr s x) = NIL then cG s.P + s.P.groupSpacing else gL s (cF s (cRr s x))) := by
    by_cases hz0 : cF s (cRr s x) = NIL
    · rw [ite_eq_left hz0]; omega
    · rw [ite_eq_right hz0]; have := (hfirstR hz0).1; omega
  have hroom : u.length * s.P.groupSpacing ≤ (match (if cF s (cRr s x) = NIL then none
      else some (gL s (cF s (cRr s x)))) with
        | none => cG s.P + s.P.groupSpacing | some n => n) := by
    by_cases hz0 : cF s (cRr s x) = NIL
    · rw [ite_eq_left hz0]; rw [ite_eq_left hz0] at hkD; exact hkD
    · rw [ite_eq_right hz0]; rw [ite_eq_right hz0] at hkD; exact hkD
  obtain ⟨labs, hlabs⟩ := pushFrontLabs_ok s (by omega) hroom
  refine ⟨labs, hlabs, ?_⟩
  have hlen : labs.length = u.length := pushFrontLabs_len hlabs
  have hv : labs = (List.range u.length).map fun i =>
      (if cF s (cRr s x) = NIL then cG s.P + s.P.groupSpacing else gL s (cF s (cRr s x))) -
        (u.length - i) * s.P.groupSpacing := by
    rw [(pushFrontLabs_vals hlabs).1]
    by_cases hz0 : cF s (cRr s x) = NIL
    · simp only [ite_eq_left hz0]
    · simp only [ite_eq_right hz0]
  have M := cmoveR_spec (s := s) (x := x) (u := u) (labs := labs) (Ne.symm hxz) hxL.2 Fx.rLive.2
    hnd hlen (fun g hg => (hmem g hg).1.2.1)
  obtain ⟨-, hun', hle⟩ := cinv_cmove hG hC M hxL hst (Or.inr rfl) (Ne.symm hxz) hmem hnd hone
  have E := cmoveR_ends (s := s) (x := x) (u := u) (labs := labs) (Ne.symm hxz) hxL.2 Fx.rLive.2
  refine ⟨{ lg with
    child := fun g => if g ∈ u then false else lg.child g
    pf := Function.update lg.pf (cRr s x) (lg.pf (cRr s x) + u.length)
    arF := Function.update lg.arF (cRr s x) (lg.arF (cRr s x) + u.length) }, ?_⟩
  refine linv_cmove_core hI hC hL M hxL hst (Or.inr rfl) hmem hk hun' hle hcl (fun g => rfl)
    rfl rfl rfl rfl rfl (fun c => hL.pb c) ?_ ?_ ?_ ?_
  · intro c
    change Function.update lg.pf (cRr s x) _ c ≤ Function.update lg.arF (cRr s x) _ c + lg.rs c
      + lg.cs c
    by_cases hc : c = cRr s x
    · rw [hc, Function.update_self, Function.update_self]; have := hL.pf (cRr s x); omega
    · rw [Function.update_of_ne hc, Function.update_of_ne hc]; exact hL.pf c
  · intro c
    change lg.arB c + Function.update lg.arF (cRr s x) _ c = _
    by_cases hc : c = cRr s x
    · rw [hc, Function.update_self, ite_eq_left rfl]; omega
    · rw [Function.update_of_ne hc, ite_eq_right hc]; omega
  · exact gaps_right hI hL M hxz Fx.rAdj Fx.rLive hxL he hsh hlastu' hnd hmem hv hkD E.2.1 E.2.2 rfl
  · refine range_cmove M hL (fun c => le_rfl) (fun c => ?_) (fun i hi => ?_)
    · change lg.pf c ≤ Function.update lg.pf (cRr s x) _ c
      by_cases hc : c = cRr s x
      · rw [hc, Function.update_self]; omega
      · rw [Function.update_of_ne hc]
    · change cG s.P ≤ labs.getD i 0 + Function.update lg.pf (cRr s x) _ (cRr s x) *
      s.P.groupSpacing ∧
        labs.getD i 0 ≤ cG s.P + lg.pb (cRr s x) * s.P.groupSpacing
      rw [Function.update_self, Nat.add_mul, hv, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi]
      simp only [Option.map_some, Option.getD_some]
      have h1 : (u.length - i) * s.P.groupSpacing ≤ u.length * s.P.groupSpacing :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : 1 * s.P.groupSpacing ≤ (u.length - i) * s.P.groupSpacing :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.one_mul] at h2
      by_cases hz0 : cF s (cRr s x) = NIL
      · rw [ite_eq_left hz0]; rw [ite_eq_left hz0] at hkD; omega
      · rw [ite_eq_right hz0]; rw [ite_eq_right hz0] at hkD; have := hfirstR hz0; omega

/-- **Lemma C3 across a chunk removal**: the emptied chunk dies, its siblings become quiet with
their current sizes as `e0`, and every undriven insertion counts as driven. -/
theorem linv_cremove {s : Core} {A : Abs} {lg : LGh} {s₀ δ δu : Nat → Nat} {x : Nat}
    (hI : INV s A) (hC : CInvE s A.elist δ δu s₀ x) (hL : LInv s lg s₀ δ δu) (hxL : LiveC s x)
    (hst : cSt s x = .splitting) (hFB : FamBound s δ s₀ x) :
    LInv (cremoveState s x)
      { lg with e0 := fun c => if c = cLl s x ∨ c = cRr s x then cSz s c else lg.e0 c } s₀
      (fun _ => 0) (fun _ => 0) := by
  have Fx := hC.cfam x hxL hst
  have hlx := Fx.lx hI hxL
  have hrx := Fx.rx hI hxL
  have hC' := cremoveState_C hxL.2 Fx.lLive.2 Fx.rLive.2 hlx hrx
  have hLC : ∀ c, LiveC (cremoveState s x) c ↔ LiveC s c := by
    intro c; simp [LiveC, cremoveState]
  have hsz : ∀ c, cSz (cremoveState s x) c = cSz s c := by
    intro c; simp only [cSz, hC']; split_ifs <;> rfl
  have hll : ∀ c, cLl (cremoveState s x) c = cLl s c := by
    intro c; simp only [cLl, hC']; split_ifs <;> rfl
  have hrr : ∀ c, cRr (cremoveState s x) c = cRr s c := by
    intro c; simp only [cRr, hC']; split_ifs <;> rfl
  have hls : ∀ c, cLs (cremoveState s x) c = cLs s c := by
    intro c; simp only [cLs, hC']; split_ifs <;> rfl
  have hstO : ∀ c, c ≠ x → c ≠ cLl s x → c ≠ cRr s x →
      cSt (cremoveState s x) c = cSt s c ∧ cSrc (cremoveState s x) c = cSrc s c := by
    intro c h1 h2 h3; simp only [cSt, cSrc, hC', ite_eq_right h1, ite_eq_right (not_or.mpr ⟨h2,
      h3⟩)]; simp
  have hstx : cSt (cremoveState s x) x = .dead := by simp [cSt, hC', deadC]
  have hstlr : ∀ c, c = cLl s x ∨ c = cRr s x → cSt (cremoveState s x) c = .quiet := by
    intro c hc
    have : c ≠ x := by
      rcases hc with rfl | rfl
      · exact hlx
      · exact hrx
    simp [cSt, hC', this, hc, quietC]
  have hfamC : ∀ c, famC (cremoveState s x) c = famC s c := by
    intro c; unfold famC; rw [hll, hrr, hsz, hsz, hsz]
  have hgs : ∀ g, (cremoveState s x).Gs.getX g = s.Gs.getX g := fun g => rfl
  have hgr : ∀ c, GrpsC (cremoveState s x) c = GrpsC s c := fun c => rfl
  have hP : (cremoveState s x).P = s.P := rfl
  have hun : ∀ c, units (cremoveState s x) c = units s c := fun c => rfl
  -- the family's size, as the drive knows it
  have hF := hFB.fam
  have hδs := hFB.δs
  have hδu := hC.δu x
  have hU := unitsOf_mono s.P hFB.T
  have hUm : unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) ≤ unitsOf s.P s.P.T / (s.P.chunkBudget
    - 1) :=
    Nat.div_le_div_right hU
  refine
    { gaps := ?_, range := hL.range, hv := hL.hv, pb := hL.pb, pf := hL.pf, roots := ?_,
      claim2 := ?_, insQ := ?_, insO := ?_, insS := ?_, arrS := ?_, arrN := ?_, e0 := ?_,
      famChild := hL.famChild }
  · intro g hg hl; rw [hls] at hl; exact hL.gaps g hg hl
  · intro d hd; rw [hLC] at hd; exact hL.roots d hd
  · intro d hd; rw [hLC] at hd; exact hL.claim2 d hd
  · intro d hd hds; rw [hLC] at hd
    change lg.ins d + (if d = cLl s x ∨ d = cRr s x then cSz s d else lg.e0 d) ≤
      cSz (cremoveState s x) d + kC s.P s.P.T
    rw [hsz]
    by_cases h2 : d = cLl s x ∨ d = cRr s x
    · rw [ite_eq_left h2]
      have hdo : cSt s d = .overflow := by
        rcases h2 with rfl | rfl
        · exact Fx.lSt
        · exact Fx.rSt
      have hds : cSrc s d = x := by
        rcases h2 with rfl | rfl
        · exact Fx.lSrc
        · exact Fx.rSrc
      have hO := hL.insO d hd hdo
      rw [hds] at hO; unfold famC at hO
      unfold kC
      generalize unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) = q1 at *
      generalize unitsOf s.P s.P.T / (s.P.chunkBudget - 1) = q2 at *
      omega
    · rw [ite_eq_right h2]
      have h1 : d ≠ x := by intro e; rw [e, hstx] at hds; cases hds
      rw [(hstO d h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))).1] at hds
      exact hL.insQ d hd hds
  · intro d hd hds; rw [hLC] at hd
    have h1 : d ≠ x := by intro e; rw [e, hstx] at hds; cases hds
    have h2 : ¬ (d = cLl s x ∨ d = cRr s x) := by intro h; rw [hstlr d h] at hds; cases hds
    obtain ⟨o1, o2⟩ := hstO d h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))
    rw [o1] at hds; rw [o2, hfamC]
    exact hL.insO d hd hds
  · intro d hd hds; rw [hLC] at hd
    have h1 : d ≠ x := by intro e; rw [e, hstx] at hds; cases hds
    have h2 : ¬ (d = cLl s x ∨ d = cLl s x ∨ d = cRr s x) := by
      rintro (h | h | h) <;> (rw [hstlr d (by simp [h])] at hds; cases hds)
    rw [(hstO d h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr (Or.inr e)))).1] at hds
    rw [hfamC, hP]; exact hL.insS d hd hds
  · intro x' hx' hxs'; rw [hLC] at hx'
    have h1 : x' ≠ x := by intro e; rw [e, hstx] at hxs'; cases hxs'
    have h2 : ¬ (x' = cLl s x ∨ x' = cRr s x) := by intro h; rw [hstlr x' h] at hxs'; cases hxs'
    rw [(hstO x' h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))).1] at hxs'
    have h := hL.arrS x' hx' hxs'
    have hδu' := hC.δu x'
    rw [hll, hrr, hun, hfamC, hP]
    dsimp only
    omega
  · intro d hd hds; rw [hLC] at hd
    by_cases h2 : d = cLl s x ∨ d = cRr s x
    · have hA := hL.arrS x hxL hst
      unfold famC at hA
      have harr : lg.arB d + lg.arF d ≤ lg.arB (cLl s x) + lg.arF (cLl s x) + lg.arB (cRr s x) +
          lg.arF (cRr s x) := by rcases h2 with rfl | rfl <;> omega
      change lg.arB d + lg.arF d ≤ 3 * Mu s.P
      unfold Mu kC
      generalize unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) = q1 at *
      generalize unitsOf s.P s.P.T / (s.P.chunkBudget - 1) = q2 at *
      omega
    · by_cases h1 : d = x
      · subst h1; exact hL.arrN d hd (by rw [hst]; simp)
      · rw [(hstO d h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))).1] at hds
        exact hL.arrN d hd hds
  · intro d hd hds; rw [hLC] at hd
    change (if d = cLl s x ∨ d = cRr s x then cSz s d else lg.e0 d) ≤ cSz (cremoveState s x) d
    rw [hsz]
    by_cases h2 : d = cLl s x ∨ d = cRr s x
    · rw [ite_eq_left h2]
    · rw [ite_eq_right h2]
      have h1 : d ≠ x := by intro e; rw [e, hstx] at hds; cases hds
      rw [(hstO d h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))).1] at hds
      exact hL.e0 d hd hds

end OrderMaintenance.Proof
