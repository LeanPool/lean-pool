/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import Mathlib.Topology.Constructions
public import LeanPool.TuringConeRigidity.Computability.OracleCode

/-!
# Truth-table reducibility and the truth-table degrees

We work with the oracles of the `DegreeRigidity` library: `Oracle := ℕ → Bool`, with Cantor
space topology (the product topology, `Bool` discrete).

A *tt-functional* is a map `Φ : Oracle → Oracle` computed by a single oracle program
(an `OracleCode`, the same programs that the library uses to characterise Mathlib's
`TuringReducible`) which halts **on every oracle and every input**.  This is the definition
used in Section 2.2 of the paper:

> A tt-functional is a total computable function `Φ : 2^ω → 2^ω`; that is, `Φ` is computed
> by an oracle Turing machine which halts on every oracle and every input.

`A ≤tt B` means `A = Φ B` for some tt-functional `Φ`.  With this definition, tt-reducibility
implies Turing reducibility immediately (`TTReducible.reduces`): the program witnessing the
tt-reduction is in particular a Turing reduction.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

/-- `Φ` is a *truth-table functional*: there is one oracle program `c` which, run with any
oracle `X`, halts on every input and outputs the characteristic function of `Φ X`. -/
def IsTTFunctional (Φ : Oracle → Oracle) : Prop :=
  ∃ c : OracleCode, ∀ X : Oracle, OracleCode.eval (oracleFunction X) c = oracleFunction (Φ X)

/-- Truth-table reducibility: `A ≤tt B` iff `A = Φ B` for some tt-functional `Φ`. -/
def TTReducible (A B : Oracle) : Prop := ∃ Φ : Oracle → Oracle, IsTTFunctional Φ ∧ Φ B = A

/-- tt-reducibility implies Turing reducibility (in the sense of the library, i.e. Mathlib's
`TuringReducible` on characteristic functions). -/
theorem TTReducible.reduces {A B : Oracle} (h : TTReducible A B) : Reduces A B := by
  obtain ⟨Φ, ⟨c, hc⟩, rfl⟩ := h
  exact (OracleCode.turingReducible_iff_exists_code _ _).mpr ⟨c, hc B⟩

/-- The same statement, phrased directly with Mathlib's `TuringReducible`. -/
theorem TTReducible.turingReducible {A B : Oracle} (h : TTReducible A B) :
    TuringReducible (oracleFunction A) (oracleFunction B) :=
  h.reduces

theorem isTTFunctional_id : IsTTFunctional id :=
  ⟨.query, fun _ => rfl⟩

/-- Substitute the program `d` for every oracle query in `c`. -/
def substCode (c d : OracleCode) : OracleCode :=
  match c with
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .query => d
  | .pair c₁ c₂ => .pair (substCode c₁ d) (substCode c₂ d)
  | .comp c₁ c₂ => .comp (substCode c₁ d) (substCode c₂ d)
  | .prec c₁ c₂ => .prec (substCode c₁ d) (substCode c₂ d)
  | .find c₁ => .find (substCode c₁ d)

theorem eval_substCode (g : ℕ →. ℕ) (c d : OracleCode) :
    OracleCode.eval g (substCode c d) = OracleCode.eval (OracleCode.eval g d) c := by
  induction c with
  | zero | succ | left | right | query => rfl
  | pair c₁ c₂ h₁ h₂ | comp c₁ c₂ h₁ h₂ | prec c₁ c₂ h₁ h₂ =>
    simp only [substCode, OracleCode.eval, h₁, h₂]
    rfl
  | find c₁ h₁ =>
    simp only [substCode, OracleCode.eval, h₁]
    rfl

theorem IsTTFunctional.comp {Φ Ψ : Oracle → Oracle} (hΦ : IsTTFunctional Φ)
    (hΨ : IsTTFunctional Ψ) : IsTTFunctional (Φ ∘ Ψ) := by
  obtain ⟨c, hc⟩ := hΦ
  obtain ⟨d, hd⟩ := hΨ
  exact ⟨substCode c d, fun X => by rw [eval_substCode, hd, hc]; rfl⟩

theorem TTReducible.refl (A : Oracle) : TTReducible A A := ⟨id, isTTFunctional_id, rfl⟩

theorem TTReducible.trans {A B C : Oracle} (h₁ : TTReducible A B) (h₂ : TTReducible B C) :
    TTReducible A C := by
  obtain ⟨Φ, hΦ, rfl⟩ := h₁
  obtain ⟨Ψ, hΨ, rfl⟩ := h₂
  exact ⟨Φ ∘ Ψ, hΦ.comp hΨ, rfl⟩

instance : IsPreorder Oracle TTReducible where
  refl := TTReducible.refl
  trans _ _ _ := TTReducible.trans

/-- The truth-table degrees: oracles modulo tt-equivalence. -/
def TTDegree : Type := Antisymmetrization Oracle TTReducible

/-- The partial order of the tt-degrees, induced by `≤tt`. -/
instance : PartialOrder TTDegree :=
  @instPartialOrderAntisymmetrization Oracle
    { le := TTReducible
      lt A B := TTReducible A B ∧ ¬ TTReducible B A
      lt_iff_le_not_ge _ _ := Iff.rfl
      le_refl := TTReducible.refl
      le_trans _ _ _ := TTReducible.trans }

/-- The tt-degree of an oracle. -/
def ttDegree (X : Oracle) : TTDegree := toAntisymmetrization TTReducible X

theorem ttDegree_le_iff {A B : Oracle} : ttDegree A ≤ ttDegree B ↔ TTReducible A B := Iff.rfl

theorem ttDegree_eq_iff {A B : Oracle} :
    ttDegree A = ttDegree B ↔ TTReducible A B ∧ TTReducible B A := by
  rw [le_antisymm_iff, ttDegree_le_iff, ttDegree_le_iff]

theorem ttDegree_surjective : Function.Surjective ttDegree := by
  intro a
  induction a using Quotient.inductionOn' with
  | h X => exact ⟨X, rfl⟩

/-- The canonical monotone map from tt-degrees to Turing degrees: it is well defined and
monotone because `≤tt` implies `≤T` (`TTReducible.reduces`). -/
def toTuringDegree : TTDegree →o Degree where
  toFun := Quotient.map' id fun _ _ h => ⟨h.1.reduces, h.2.reduces⟩
  monotone' := by
    intro a b
    induction a using Quotient.inductionOn' with
    | h A =>
      induction b using Quotient.inductionOn' with
      | h B => exact fun h => TTReducible.reduces h

theorem toTuringDegree_ttDegree (X : Oracle) :
    toTuringDegree (ttDegree X) = toAntisymmetrization Reduces X := rfl

/-- `F : 2^ω → 2^ω` *induces* the automorphism `π` of the tt-degrees:
`deg_tt (F X) = π (deg_tt X)` for all `X`. -/
def InducedBy (π : TTDegree ≃o TTDegree) (F : Oracle → Oracle) : Prop :=
  ∀ X : Oracle, ttDegree (F X) = π (ttDegree X)

/-- An automorphism `π` of the tt-degrees is *induced by a continuous function* if some
continuous `F : 2^ω → 2^ω` (Cantor space topology) induces it. -/
def InducedByContinuous (π : TTDegree ≃o TTDegree) : Prop :=
  ∃ F : Oracle → Oracle, Continuous F ∧ InducedBy π F

end TT
