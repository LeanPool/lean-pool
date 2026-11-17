/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Params


/-!
# M6: a new core in the free slot

`newCoreS q`: compute the parameters of capacity `N` (local `nN`), allocate slot `q`, and run the
compiled `initCore` in its lazy form. The slot then holds Level F's `prepStart P false`, the core
of `newCore P true` (`newCore_ok`), in a constant number of steps. The compiled code is fixed: it
is compiled with the capacities of any parameters (`κ₀`), since only the list strides enter it.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

/-- The capacities the fixed code is compiled with (any parameters give the same code). -/
def κ₀ : Caps := capsOf default

theorem compile_κ₀ (q : Nat) (P : Params) (c : Stm) : c.compile q κ₀ = c.compile q (capsOf P) :=
  Stm.compile_congr (fun k => capsOf_lcap default P k) c

/-- Compute a slot's parameters, allocate its arrays, and initialize its lazy core. -/
def newCoreS (q : Nat) : Stmt :=
  .seq (paramsS q) (.seq (allocSlot q)
    (.call "initCore" ["lz"] (initCoreS.compile q κ₀) [] [.lit 1] []))

theorem proofParams_B (N : Nat) : 1 ≤ (proofParams N).elementBits ∧ 1 ≤ (proofParams
  N).groupBits := by
  simp only [proofParams]; omega

/-- The locals the parameter computation sets. -/
def pLocs : List Reg := ["L", "kE", "kG", "kC", "kN", "kB", "kCc", "kL", "kR", "kRc", "kf", "kW"]

/-- **A new core**: slot `q` holds `prepStart (proofParams N) false`. -/
theorem newCore_ok (q : Nat) {m : State} {N : Nat} (hN : m.loc "nN" = N) (hpos : 0 < N) :
    wp (newCoreS q) (fun m' n => Enc q (capsOf (proofParams N)) (prepStart (proofParams N)
      false) m' ∧
      (∀ b, ¬ InSlot q b → Same b m m') ∧ m'.loc "nN" = N ∧ (∀ x, x ∉ pLocs → m'.loc x = m.loc x) ∧
      n ≤ 3000) m := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := paramsS_ok q hN hpos
  set P := proofParams N
  set m1 := (exec (paramsS q) m).st
  obtain ⟨b1, b2, b3, b4, b5⟩ := fresh_enc (q := q) (m := m1) a3 a4 a5
  set m2 := (exec (allocSlot q) m1).st
  obtain ⟨L', c, he, hc⟩ := initCoreS_lazy (κ := capsOf P) (P := P)
    (L := Machine.State.setLocs (fun _ => 0) ["lz"] [1]) (by
      simp [Machine.State.setLocs, Machine.State.upd])
    (proofParams_B N).1 (proofParams_B N).2 (capsOf_init P) (by simp [capsOf]) (by simp [capsOf])
  unfold newCoreS
  rw [Machine.wp_seq]
  refine ⟨a1, ?_⟩
  change wp _ _ m1
  rw [Machine.wp_seq]
  refine ⟨b1, ?_⟩
  change wp _ _ m2
  rw [compile_κ₀ q P]
  refine wp_coreCall b4 (by rfl) he (fun m3 hE hS hL => ?_)
  refine ⟨hE, fun b hb => ?_, ?_, fun x hx => ?_, ?_⟩
  · have h1 : Same b m m1 := by
      by_cases e : b = arr q .prm
      · exact absurd (e ▸ arr_inSlot q .prm) hb
      · exact a6 b e
    exact h1.trans ((b5 b hb).trans (hS b hb))
  · rw [hL]; simp [Machine.State.setLocs, b3, a7 "nN" (by decide) (by decide) (by decide) (by
      decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
        decide), hN]
  · simp only [pLocs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12⟩ := hx
    rw [hL]; simp only [Machine.State.setLocs]; rw [b3]
    exact a7 x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
  · rw [b2]
    have := a2
    have hb : Machine.allocCost (Slot.allNP.map fun sl => (arr q sl, capE sl)) ≤ 1000 := by
      have e : Machine.allocCost (Slot.allNP.map fun sl => (arr q sl, capE sl)) =
          (Slot.allNP.map fun sl => 1 + (capE sl).cost).sum + 1 := by
        simp only [Machine.allocCost, List.map_map]; rfl
      rw [e]; decide
    simp only [Machine.costList, List.map, Expr.cost, List.sum_cons,
      List.sum_nil, List.length] at *
    omega

end OrderMaintenance.Impl
