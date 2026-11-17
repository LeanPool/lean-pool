/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelOmegaJump.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.JumpIterationFormula
public import LeanPool.TuringConeRigidity.SetModels.ModelRealOperations

/-!
# Model Omega Jump
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel OracleJump
universe u

namespace Formula
/-- Bounded formula reading a paired bit of the join of finite jump iterates. -/
def omegaJumpBits (φ : Formula) : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 4
    (.conj (naturalPair 4 7 2 1 3)
      (.conj (jumpIteration φ 4 5 6 7 2 8 0) (.member 1 0)))))
end Formula

/-- The environment supplying the input, omega, real universe, graph bounds, and base oracle
for omega-jump bits. -/
noncomputable def omegaJumpEnv (R Qf Qn : ZFSet.{u}) (A : Oracle) (n : ℕ) : ℕ → ZFSet.{u} :=
  cons (natSet n) (cons ZFSet.omega (cons R (cons Qf (cons Qn (fun _ => realCode A)))))

theorem omegaJumpBits_spec {φ : Formula} (hφ : JumpFormula.{u} φ)
    (R Qf Qn : ZFSet.{u})
    (hQn : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ Qn)
    (hQf : ∀ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ R) → ∀ k, finiteModelGraph a k ∈ Qf)
    (hR : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    (A : Oracle) (hA : ∀ i, realCode (iterate A i) ∈ R) (N : ℕ) :
    (Formula.omegaJumpBits φ).Eval (omegaJumpEnv R Qf Qn A N) ↔
      iterate A (Nat.unpair N).1 (Nat.unpair N).2 = true := by
  let e := omegaJumpEnv R Qf Qn A N
  have hpair (i j : ℕ) (w : ZFSet.{u}) := Formula.naturalPair_spec 4 7 2 1 3
    (cons w (cons (natSet j) (cons (natSet i) e))) rfl hQn i j rfl rfl
  have hiter (i j : ℕ) (w : ZFSet.{u}) := Formula.jumpIteration_spec hφ 4 5 6 7 2 8 0
    (cons w (cons (natSet j) (cons (natSet i) e))) rfl hQn hQf hR A hA rfl i rfl
  simp only [Formula.omegaJumpBits,Formula.Eval,omegaJumpEnv,cons_zero,cons_succ]
  constructor
  · rintro ⟨i,hi,j,hj,w,_,hp,ht,hm⟩
    obtain ⟨i,rfl⟩ := (mem_omega i).mp hi
    obtain ⟨j,rfl⟩ := (mem_omega j).mp hj
    have hN : N = Nat.pair i j := natSet_injective ((hpair i j w).mp hp)
    have hw : w = realCode (iterate A i) := (hiter i j w).mp ht
    rw [hw,natSet_mem_realCode] at hm
    simpa only [hN,Nat.unpair_pair] using hm
  · intro h
    let i := (Nat.unpair N).1
    let j := (Nat.unpair N).2
    refine ⟨natSet i,(mem_omega _).mpr ⟨i,rfl⟩,natSet j,(mem_omega _).mpr ⟨j,rfl⟩,
      realCode (iterate A i),hA i,(hpair i j _).mpr ?_,(hiter i j _).mpr rfl,?_⟩
    · change natSet N = natSet (Nat.pair (Nat.unpair N).1 (Nat.unpair N).2)
      rw [Nat.pair_unpair]
    · exact (natSet_mem_realCode _ _).mpr h

theorem sourceT_real_omega_jump (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : Oracle} (hA : A ∈ modelReals M) :
    (fun v => iterate A (Nat.unpair v).1 (Nat.unpair v).2) ∈ modelReals M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨R,hRM,hR,hRdecode⟩ := internal_real_power M hM hT
  have hi : ∀ i, realCode (iterate A i) ∈ R :=
    fun i => (hR _).mpr (sourceT_real_iterate M hM hT hA i)
  obtain ⟨Qf,hQfM,_,hQf⟩ := internal_finite_model_graph_bound M hM hT.pairing hT.union hT.powerSet
    hS hω R hRM
  obtain ⟨Qn,hQnM,_,hQn⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hS hω
  obtain ⟨φ,hφ⟩ := jump_bounded_relation.{u}
  have hφ' : JumpFormula.{u} φ := hφ
  let e := cons ZFSet.omega (cons R (cons Qf (cons Qn (fun _ => realCode A))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hRM
    rcases i with _ | i
    · exact hQfM
    rcases i with _ | i
    · exact hQnM
    exact hA
  let B := ZFSet.sep (fun x => (Formula.omegaJumpBits φ).Eval (cons x e)) ZFSet.omega
  have hBM : B ∈ M := sep_mem M hM hS _ e he hω
  have hbits (n : ℕ) : natSet.{u} n ∈ B ↔ iterate A (Nat.unpair n).1 (Nat.unpair n).2 = true := by
    rw [ZFSet.mem_sep]
    change (natSet n ∈ ZFSet.omega ∧ (Formula.omegaJumpBits φ).Eval (omegaJumpEnv R Qf Qn A n)) ↔ _
    rw [omegaJumpBits_spec hφ' R Qf Qn hQn hQf
      (fun w hw => by obtain ⟨B,_,hB⟩ := hRdecode w hw; exact ⟨B,hB⟩) A hi n]
    exact and_iff_right ((mem_omega _).mpr ⟨n,rfl⟩)
  have hcode : realCode (fun v => iterate A (Nat.unpair v).1 (Nat.unpair v).2) = B := by
    apply ZFSet.ext; intro x
    by_cases hx : x ∈ ZFSet.omega.{u}
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      rw [natSet_mem_realCode,hbits]
    · exact ⟨fun h => False.elim (hx (realCode_subset _ h)),
        fun h => False.elim (hx (ZFSet.mem_sep.mp h).1)⟩
  change realCode _ ∈ M
  rw [hcode]
  exact hBM

end TuringRigidity.BoundedSetTheory

end OAI
