/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalPrimitiveRecursion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalProjectionFormula
public import Mathlib.Computability.Primrec.Basic

/-!
# Natural Primitive Recursion
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u
namespace Formula

def primitiveStep (ψ : Formula) : Formula := .existsMem 8
  (.conj (naturalPair 9 10 3 2 0) (pairedUnary ψ 9 10 6 0 1))

def primitiveRecursion (φ ψ : Formula) : Formula := .existsMem 2 (.existsMem 3 (.existsMem 4
  (.conj (naturalPair 5 6 2 1 4) (.conj (unary φ 5 6 2 0)
    (iteration 5 6 1 0 3 (primitiveStep ψ))))))

theorem primitiveStep_spec {ψ : Formula} {g : ℕ → ℕ} (hg : DefinesNatural.{u} ψ g)
    (e : ℕ → ZFSet.{u}) (ho : e 5 = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e 6) (z : ℕ) (hz : e 2 = natSet z)
    (i v : ℕ) (w : ZFSet.{u}) :
    (primitiveStep ψ).Eval (cons w (cons (natSet v) (cons (natSet i) e))) ↔
      w = natSet (g (Nat.pair z (Nat.pair i v))) := by
  let E := cons w (cons (natSet v) (cons (natSet i) e))
  have hp (t : ZFSet.{u}) := naturalPair_spec 9 10 3 2 0 (cons t E) ho hQ i v rfl rfl
  have hu := pairedUnary_spec hg 9 10 6 0 1 (cons (natSet (Nat.pair i v)) E)
    ho hQ z (Nat.pair i v) hz rfl
  simp only [primitiveStep,Formula.Eval]
  constructor
  · rintro ⟨t,_,ht,h⟩
    obtain rfl := (hp t).mp ht
    exact hu.mp h
  · intro h
    refine ⟨natSet (Nat.pair i v),?_,(hp _).mpr rfl,hu.mpr h⟩
    change natSet (Nat.pair i v) ∈ e 5
    rw [ho]; exact (mem_omega _).mpr ⟨Nat.pair i v,rfl⟩
end Formula

theorem DefinesNatural.prec {φ ψ : Formula} {f g : ℕ → ℕ}
    (hf : DefinesNatural.{u} φ f) (hg : DefinesNatural.{u} ψ g) :
    DefinesNatural.{u} (Formula.primitiveRecursion φ ψ)
      (Nat.unpaired fun z n => Nat.rec (f z) (fun i v => g (Nat.pair z (Nat.pair i v))) n) := by
  intro e ho hQ N hn
  have hmem (k : ℕ) : natSet.{u} k ∈ e 2 := by rw [ho]; exact (mem_omega _).mpr ⟨k,rfl⟩
  have decode (x : ZFSet.{u}) (hx : x ∈ e 2) : ∃ n, x = natSet n := by
    rw [ho] at hx; exact (mem_omega x).mp hx
  have hp (z n : ℕ) (b : ZFSet.{u}) := Formula.naturalPair_spec 5 6 2 1 4
    (cons b (cons (natSet n) (cons (natSet z) e))) ho hQ z n rfl rfl
  have hb (z n : ℕ) (b : ZFSet.{u}) := Formula.unary_spec hf 5 6 2 0
    (cons b (cons (natSet n) (cons (natSet z) e))) ho hQ z rfl
  have hi (z n : ℕ) := Formula.iteration_spec 5 6 1 0 3 (Formula.primitiveStep ψ)
    (cons (natSet (f z)) (cons (natSet n) (cons (natSet z) e))) ho hQ n (f z) rfl rfl
    (fun i v => g (Nat.pair z (Nat.pair i v)))
    (Formula.primitiveStep_spec hg _ ho hQ z rfl)
  simp only [Formula.primitiveRecursion,Formula.Eval]
  constructor
  · rintro ⟨z,hz,n,hnum,b,_,hp',hb',hi'⟩
    obtain ⟨z,rfl⟩ := decode z hz
    obtain ⟨n,rfl⟩ := decode n hnum
    have hN : N = Nat.pair z n := natSet_injective (hn.symm.trans ((hp z n b).mp hp'))
    obtain rfl := (hb z n b).mp hb'
    have h := (hi z n).mp hi'
    simpa only [cons_succ,hN,Nat.unpaired,Nat.unpair_pair] using h
  · intro h
    let z := (Nat.unpair N).1
    let n := (Nat.unpair N).2
    refine ⟨natSet z,hmem _,natSet n,hmem _,natSet (f z),hmem _,?_,(hb z n _).mpr rfl,?_⟩
    · apply (hp z n _).mpr
      simpa only [cons_succ,z,n,Nat.pair_unpair] using hn
    · apply (hi z n).mpr
      exact h

theorem primitive_bounded_definition {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ φ : Formula, DefinesNatural.{u} φ f := by
  induction hf with
  | zero => exact ⟨.empty 0,definesNatural_zero⟩
  | succ => exact ⟨.successor 0 1,definesNatural_succ⟩
  | left => exact ⟨.naturalProjection false,Formula.naturalProjection_spec false⟩
  | right => exact ⟨.naturalProjection true,Formula.naturalProjection_spec true⟩
  | pair _ _ ihf ihg =>
    obtain ⟨φ,hφ⟩ := ihf; obtain ⟨ψ,hψ⟩ := ihg
    exact ⟨.numericPair φ ψ,hφ.pair hψ⟩
  | comp _ _ ihf ihg =>
    obtain ⟨φ,hφ⟩ := ihf; obtain ⟨ψ,hψ⟩ := ihg
    exact ⟨.numericComposition φ ψ,hφ.comp hψ⟩
  | prec _ _ ihf ihg =>
    obtain ⟨φ,hφ⟩ := ihf; obtain ⟨ψ,hψ⟩ := ihg
    exact ⟨.primitiveRecursion φ ψ,hφ.prec hψ⟩

end TuringRigidity.BoundedSetTheory

end OAI
