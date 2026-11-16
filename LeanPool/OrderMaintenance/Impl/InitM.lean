/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.OpsM


/-!
# M6: initialization as machine code

`initWS`: the first core (capacity `minimumCapacity = 64`), built eagerly in slot 0, the
  wrapper's scalars,
and the handle map of slot 0. It reaches Level F's `OrderMaintenance.init` in a constant number of steps.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

/-! ### The eager construction keeps the empty rows -/

theorem loop_runZ {P : Params} (hPP : topPP P) : ∀ (l : List Nat) (h : Nat) (s : Core), Stage P h s → PZ1 s →
    1 ≤ h → h ≤ P.H + 1 → P.H + 2 - h ≤ l.length →
    ∃ s', (forIn l PUnit.unit fun (_ : Nat) (_ : PUnit) => do
        let b ← initStep
        if b = true then pure (ForInStep.done PUnit.unit) else pure (ForInStep.yield PUnit.unit) :
        CM PUnit).run s = .ok () s' ∧ Final P s' ∧ PZ1 s'
  | [], h, s, _, _, _, hH, hl => by simp at hl; omega
  | x :: t, h, s, S, hz, h1, hH, hl => by
    have hH1 : 1 ≤ P.H := by have := hPP.2; omega
    rw [List.forIn_cons]
    by_cases hh : h ≤ P.H
    · obtain ⟨s', hr, S', -⟩ := stage_next S h1 hh hPP.beta
      obtain ⟨s'', hr', F, hz'⟩ := loop_runZ hPP t (h + 1) s' S' (prep_pz1 S hH1 hz hr) (by omega) (by omega)
        (by simp at hl; omega)
      refine ⟨s'', ?_, F, hz'⟩
      rw [run_bind, run_bind, hr]
      simp
      exact hr'
    · have e : h = P.H + 1 := by omega
      subst e
      obtain ⟨s', hr, F, -⟩ := stage_last S hH1
      refine ⟨s', ?_, F, prep_pz1 S hH1 hz hr⟩
      rw [run_bind, run_bind, hr]
      simp

/-- **An eagerly built core satisfies the capacity predicate.** -/
theorem eager_M {s s' : Core} (hPP : topPP s.P) (hN : 1 ≤ s.P.N) (h : (initCore false).run s = .ok () s') :
    Mc (capsOf s.P) s.P s' := by
  have S := stage_one s true
  obtain ⟨s1, hr, F, hz⟩ := loop_runZ hPP (List.range (s.P.H + 1)) 1 _ S (pz1_initState s.P true) le_rfl
    (by omega) (by simp)
  rw [initCore_eager_eq, run_bind, hr] at h
  simp only [run_modify] at h
  cases h
  exact mc_final (capsOf_ok s.P) hN (F.ready true) hz

/-! ### An eagerly built core -/

def eagerCoreS (q : Nat) : Stmt :=
  .seq (paramsS q) (.seq (allocSlot q)
    (.call "initCore" ["lz"] (initCoreS.compile q κ₀) [] [.lit 0] []))

/-- **An eagerly built core**: slot `q` holds Level F's `initCore false` of the proof parameters. -/
theorem eagerCore_ok (q : Nat) {m : State} {N : Nat} (hN : m.loc "nN" = N) (hpos : 0 < N) {n : Core}
    (hn : (initCore false).run ({ P := proofParams N } : Core) = .ok () n) :
    wp (eagerCoreS q) (fun m' k => Enc q (capsOf (proofParams N)) n m' ∧
      (∀ b, ¬ InSlot q b → Same b m m') ∧ (∀ x, x ∉ pLocs → m'.loc x = m.loc x) ∧
      k ≤ 4000 + ((proofParams N).H + 1) * 412) m := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := paramsS_ok q hN hpos
  set P := proofParams N
  set m1 := (exec (paramsS q) m).st
  obtain ⟨b1, b2, b3, b4, b5⟩ := fresh_enc (q := q) (m := m1) a3 a4 a5
  set m2 := (exec (allocSlot q) m1).st
  have hH : 1 ≤ P.H := by simp [P, proofParams]
  have hb : 1 ≤ P.beta := by simp [P, proofParams]
  obtain ⟨L', c, he, hc⟩ := initCoreS_eager (κ := capsOf P) (P := P)
    (L := OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["lz"] [0]) (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (proofParams_B N).1 (proofParams_B N).2 hb hH (capsOf_init P) (by simp [capsOf]) (by simp [capsOf]) rfl hn
  unfold eagerCoreS
  rw [OrderMaintenance.Machine.wp_seq]
  refine ⟨a1, ?_⟩
  show wp _ _ m1
  rw [OrderMaintenance.Machine.wp_seq]
  refine ⟨b1, ?_⟩
  show wp _ _ m2
  rw [compile_κ₀ q P]
  refine wp_coreCall b4 (by rfl) he (fun m3 hE hS hL => ?_)
  refine ⟨hE, fun b hb => ?_, fun x hx => ?_, ?_⟩
  · have h1 : Same b m m1 := by
      by_cases e : b = arr q .prm
      · exact absurd (e ▸ arr_inSlot q .prm) hb
      · exact a6 b e
    exact h1.trans ((b5 b hb).trans (hS b hb))
  · simp only [pLocs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12⟩ := hx
    rw [hL]; simp only [OrderMaintenance.Machine.State.setLocs, List.map]; rw [b3]
    exact a7 x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
  · rw [b2]
    have := a2
    have hb : OrderMaintenance.Machine.allocCost (Slot.allNP.map fun sl => (arr q sl, capE sl)) ≤ 1000 := by
      have e : OrderMaintenance.Machine.allocCost (Slot.allNP.map fun sl => (arr q sl, capE sl)) =
          (Slot.allNP.map fun sl => 1 + (capE sl).cost).sum + 1 := by
        simp only [OrderMaintenance.Machine.allocCost, List.map_map]; rfl
      rw [e]; decide
    simp only [OrderMaintenance.Machine.costList, List.map, Expr.cost, List.sum_cons,
      List.sum_nil, List.length] at *
    omega

/-! ### Initialization -/

/-- The wrapper's arrays: the eight scalars, and the handle map of slot 0. -/
def initAllocs : List (Arr × Expr) := (List.range 8).map (fun k => (wa k, .lit 1)) ++ [(wIdx 0, .lit 64)]

/-- **Initialization**, with `K_B` in local `kb`. -/
def initWS : Stmt :=
  .seq (.assign "nN" (.lit 64)) (.seq (eagerCoreS 0) (.seq (OrderMaintenance.Machine.allocAll initAllocs)
    (.store (wa 7) (.lit 0) (.var "kb"))))

/-- The cost bound of initialization. -/
def initB : Nat := 5000 + ((proofParams 64).H + 1) * 412

theorem initAllocs_nodup : (initAllocs.map Prod.fst).Nodup := by decide

/-- **Initialization at Level M**: Level F's initial state, with the invariant, in slot 0, within
`initB` steps. -/
theorem initW_ok {m : State} {KB : Nat} (hkb : m.loc "kb" = KB) (h4 : 4 ≤ KB) :
    ∃ om, OrderMaintenance.init proofParams KB = .ok om ∧ MInv om OrderMaintenance.Spec.State.empty ∧
      wp initWS (fun m' k => WEnc om m' 0 ∧ k ≤ initB) m := by
  obtain ⟨om, hinit, hW⟩ := init_cost costSetup h4
  obtain ⟨n, hnew, hrun⟩ := newCore_run (P := proofParams minimumCapacity) (lazy := false)
  have hom : om = { cur := n, KB := KB } := by
    unfold OrderMaintenance.init at hinit
    simp only [bind, Except.bind, hnew] at hinit
    injection hinit with h; exact h.symm
  subst hom
  obtain ⟨-, hPn⟩ := initCore_fields hrun
  have hPn' : n.P = proofParams 64 := hPn
  have hM : Mc (capsOf n.P) n.P n := by
    rw [hPn']
    exact eager_M (s := { P := proofParams minimumCapacity }) (pp_topPP _) (by decide) hrun
  refine ⟨_, hinit, ⟨hW, hM, fun n' h => by cases h⟩, ?_⟩
  unfold initWS
  rw [OrderMaintenance.Machine.wp_seq]
  refine wp_assign_g 64 rfl (fun s1 hl1 hm1 hc1 => ?_)
  have hN1 : s1.loc "nN" = 64 := by rw [hl1]; simp [OrderMaintenance.Machine.State.upd]
  rw [OrderMaintenance.Machine.wp_seq]
  refine OrderMaintenance.Machine.wp_mono (fun s2 k2 ⟨hE2, hS2, hl2, hk2⟩ => ?_) (eagerCore_ok 0 hN1 (by decide) hrun)
  rw [OrderMaintenance.Machine.wp_seq]
  have hev : ∀ ae ∈ initAllocs, ae.2.noLoad ∧ (ae.2.eval s2).isSome := by
    intro ae hae
    simp only [initAllocs, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hae
    rcases hae with ⟨k, -, rfl⟩ | rfl <;> exact ⟨rfl, rfl⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := OrderMaintenance.Machine.exec_allocAll initAllocs s2 hev initAllocs_nodup
  refine ⟨a1, ?_⟩
  set s3 := (exec (OrderMaintenance.Machine.allocAll initAllocs) s2).st
  have hwa : ∀ k, k < 8 → s3.cap (wa k) = 1 ∧ ∀ i, s3.mem (wa k) i = 0 := fun k hk => by
    have := a4 (wa k, .lit 1) (by simp [initAllocs]; exact ⟨k, hk, rfl⟩)
    exact ⟨this.1, this.2⟩
  have hix : s3.cap (wIdx 0) = 64 ∧ ∀ i, s3.mem (wIdx 0) i = 0 := by
    have := a4 (wIdx 0, .lit 64) (by simp [initAllocs])
    exact ⟨this.1, this.2⟩
  have hsl : ∀ b, InSlot 0 b → Same b s2 s3 := fun b hb => a5 b (by
    simp only [initAllocs, List.map_append, List.map_map, List.mem_append, List.mem_map,
      List.mem_range,
      Function.comp, List.map_cons, List.map_nil, List.mem_singleton, not_or]
    refine ⟨fun ⟨k, _, e⟩ => wa_notSlot (p := 0) (by decide) (e ▸ hb), fun e => wIdx_notSlot (p := 0) (by decide) (e ▸ hb)⟩)
  have hE3 : Enc 0 (capsOf n.P) n s3 := by rw [hPn']; exact hE2.of_same hsl
  have hkb3 : s3.loc "kb" = KB := by rw [a3, hl2 "kb" (by simp [pLocs]), hl1]; simp [OrderMaintenance.Machine.State.upd, hkb]
  refine wp_store_g 0 KB rfl (by simp [Expr.eval, hkb3]) (by rw [(hwa 7 (by decide)).1]; decide)
    (fun s4 hl4 hm4 hc4 => ⟨?_, ?_⟩)
  · have hne : ∀ b, b ≠ wa 7 → s4.mem b = s3.mem b := fun b hb => by rw [hm4]; simp [State.write, hb]
    have hm7 : s4.mem (wa 7) 0 = KB := by rw [hm4]; simp [State.write, OrderMaintenance.Machine.State.upd]
    have hk : ∀ k, k < 7 → s4.mem (wa k) 0 = 0 := fun k hk => by
      rw [hne _ (wa_ne (by omega))]; exact (hwa k (by omega)).2 0
    refine ⟨by decide, fun k hk => by rw [hc4]; exact (hwa k hk).1, hk 0 (by decide), hk 1 (by decide),
      hk 2 (by decide), hk 3 (by decide), hk 4 (by decide), hk 5 (by decide), hk 6 (by decide), hm7,
      hE3.of_same fun b hb => ⟨by rw [hne b (fun e => wa_notSlot (p := 0) (by decide) (e ▸ hb))], by rw [hc4]⟩,
      (fun n' h => by cases h), (fun i hi => ?_), (fun h => by cases h), ?_, (fun n' h => by cases h)⟩
    · rw [hne _ (Ne.symm (wa_ne_idx (by decide))), hix.2]; simp [Array.getX]
    · show 0 + (n.P.N - n.count) ≤ s4.cap (wIdx 0)
      rw [hc4, hix.1, hPn']; show 0 + (64 - n.count) ≤ 64; omega
  · rw [a2]
    have hac : OrderMaintenance.Machine.allocCost initAllocs = 19 := by decide
    rw [hac]; unfold initB; simp only [Expr.cost] at hk2 ⊢; omega

end OrderMaintenance.Impl
