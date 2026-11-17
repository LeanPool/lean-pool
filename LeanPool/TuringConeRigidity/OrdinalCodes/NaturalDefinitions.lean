/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalDefinitions.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalPairingFormula

/-!
# Natural Definitions
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

/-- A bounded formula defines the natural-number function under every adequate finite-graph
bound. -/
def DefinesNatural (φ : Formula) (f : ℕ → ℕ) : Prop :=
  ∀ e : ℕ → ZFSet.{u}, e 2 = ZFSet.omega →
    (∀ g : ℕ → ℕ, ∀ k, finiteNaturalGraph g k ∈ e 3) → ∀ n, e 1 = natSet n →
      (φ.Eval e ↔ e 0 = natSet (f n))

namespace Formula
/-- Variable renaming supplying the input, output, omega, and graph-bound slots of a unary
definition. -/
def unaryVars (o Q x y : ℕ) : ℕ → ℕ
  | 0 => y
  | 1 => x
  | 2 => o
  | _+3 => Q

/-- Place a unary numerical definition in the specified variable slots. -/
def unary (φ : Formula) (o Q x y : ℕ) : Formula := φ.rename (unaryVars o Q x y)

theorem unary_spec {φ : Formula} {f : ℕ → ℕ} (hφ : DefinesNatural.{u} φ f)
    (o Q x y : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ g : ℕ → ℕ, ∀ k, finiteNaturalGraph g k ∈ e Q) (n : ℕ) (hx : e x = natSet n) :
    (unary φ o Q x y).Eval e ↔ e y = natSet (f n) := by
  rw [unary,eval_rename]
  exact hφ (fun i => e (unaryVars o Q x y i)) ho hQ n hx

/-- Compose two unary numerical definitions through an intermediate natural number. -/
def numericComposition (φ ψ : Formula) : Formula := .existsMem 2
  (.conj (unary ψ 3 4 2 0) (unary φ 3 4 0 1))

/-- Compute two unary outputs and encode their ordered natural-number pair. -/
def numericPair (φ ψ : Formula) : Formula := .existsMem 2 (.existsMem 3
  (.conj (unary φ 4 5 3 1) (.conj (unary ψ 4 5 3 0) (naturalPair 4 5 1 0 2))))

/-- Apply a unary definition to the natural-number pair of two supplied inputs. -/
def pairedUnary (φ : Formula) (o Q a b y : ℕ) : Formula := .existsMem o
  (.conj (naturalPair (o+1) (Q+1) (a+1) (b+1) 0) (unary φ (o+1) (Q+1) 0 (y+1)))

theorem pairedUnary_spec {φ : Formula} {f : ℕ → ℕ} (hφ : DefinesNatural.{u} φ f)
    (o Q x n y : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ g : ℕ → ℕ, ∀ k, finiteNaturalGraph g k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (pairedUnary φ o Q x n y).Eval e ↔ e y = natSet (f (Nat.pair a b)) := by
  have hp (w : ZFSet.{u}) := naturalPair_spec (o+1) (Q+1) (x+1) (n+1) 0 (cons w e) ho hQ a b ha hb
  have hu := unary_spec hφ (o+1) (Q+1) 0 (y+1) (cons (natSet (Nat.pair a b)) e) ho hQ (Nat.pair a
    b) rfl
  simp only [pairedUnary,Formula.Eval]
  constructor
  · rintro ⟨w,_,hw,h⟩
    obtain rfl := (hp w).mp hw
    exact hu.mp h
  · intro h
    refine ⟨natSet (Nat.pair a b),?_,(hp _).mpr rfl,hu.mpr h⟩
    rw [ho]; exact (mem_omega _).mpr ⟨Nat.pair a b,rfl⟩
end Formula

theorem definesNatural_zero : DefinesNatural.{u} (.empty 0) (fun _ => 0) := by
  intro e _ _ n _
  exact Formula.eval_empty 0 e

theorem definesNatural_succ : DefinesNatural.{u} (.successor 0 1) Nat.succ := by
  intro e _ _ n hn
  rw [Formula.eval_successor,hn]
  rfl

theorem DefinesNatural.comp {φ ψ : Formula} {f g : ℕ → ℕ}
    (hf : DefinesNatural.{u} φ f) (hg : DefinesNatural.{u} ψ g) :
    DefinesNatural.{u} (Formula.numericComposition φ ψ) (fun n => f (g n)) := by
  intro e ho hQ n hn
  have hv (w : ZFSet.{u}) := Formula.unary_spec hg 3 4 2 0 (cons w e) ho hQ n hn
  have hu := Formula.unary_spec hf 3 4 0 1 (cons (natSet (g n)) e) ho hQ (g n) rfl
  simp only [Formula.numericComposition,Formula.Eval]
  constructor
  · rintro ⟨w,_,hw,h⟩
    obtain rfl := (hv w).mp hw
    exact hu.mp h
  · intro h
    refine ⟨natSet (g n),?_,(hv _).mpr rfl,hu.mpr h⟩
    rw [ho]; exact (mem_omega _).mpr ⟨g n,rfl⟩

theorem DefinesNatural.pair {φ ψ : Formula} {f g : ℕ → ℕ}
    (hf : DefinesNatural.{u} φ f) (hg : DefinesNatural.{u} ψ g) :
    DefinesNatural.{u} (Formula.numericPair φ ψ) (fun n => Nat.pair (f n) (g n)) := by
  intro e ho hQ n hn
  have hv (w z : ZFSet.{u}) := Formula.unary_spec hf 4 5 3 1 (cons z (cons w e)) ho hQ n hn
  have hw (w z : ZFSet.{u}) := Formula.unary_spec hg 4 5 3 0 (cons z (cons w e)) ho hQ n hn
  have hp := Formula.naturalPair_spec 4 5 1 0 2 (cons (natSet (g n)) (cons (natSet (f n)) e))
    ho hQ (f n) (g n) rfl rfl
  have hmem (k : ℕ) : natSet.{u} k ∈ e 2 := by rw [ho]; exact (mem_omega _).mpr ⟨k,rfl⟩
  simp only [Formula.numericPair,Formula.Eval]
  constructor
  · rintro ⟨w,_,z,_,hvw,hwz,h⟩
    obtain rfl := (hv w z).mp hvw
    obtain rfl := (hw _ z).mp hwz
    exact hp.mp h
  · intro h
    exact ⟨natSet (f n),hmem _,natSet (g n),hmem _,(hv _ _).mpr rfl,(hw _ _).mpr rfl,hp.mpr h⟩

end TuringRigidity.BoundedSetTheory

end OAI
