/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Problems.Sat.Tseitin
import all LeanPool.DescriptiveCounting.Problems.Sat.Tseitin

/-!
# The Tseitin encoding determines its gate variables

Two facts about the encoding of `DescriptiveComplexity.Problems.Sat.Tseitin` that a
decision reduction does not need and a *parsimonious* one does: they say that a
model of the encoding carries no information beyond the block assignment it
induces.

* `DescriptiveComplexity.Tseitin.gates_unique`: a valuation of the position variables
  satisfying every gate is the canonical one, at every position and not only at
  the root (`DescriptiveComplexity.Tseitin.gates_realize`);
* `DescriptiveComplexity.Tseitin.litSem_varCanon`: a propositional variable occurring
  in a clause sits at a canonically padded tuple, of the length its kind
  prescribes (`DescriptiveComplexity.Tseitin.VarCanon`). So the non-canonical tuples
  are not variables of the encoding at all.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

namespace Tseitin

open Language Structure

section Unique

variable {L : Language.{0, 0}} {B : SOBlock} {A : Type} [L.Structure A]
variable (μ : B.Assignment A)

/-- **Gates determine the valuation**: a valuation of the position variables
satisfying every gate assigns to every position the truth value of its
subformula. -/
theorem gates_unique :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n) (ν : NodeVal A f),
      Gates μ f ν → ∀ (m : ℕ) (p : NodeAt f m) (w : Fin m → A),
        (ν m p w ↔ canonVal μ f m p w)
  | _, .falsum, ν, hg, _, p, w => by
      obtain ⟨rfl⟩ := p
      exact (gates_realize μ .falsum ν hg w).trans (canonVal_rootAt μ .falsum w).symm
  | _, .equal t₁ t₂, ν, hg, _, p, w => by
      obtain ⟨rfl⟩ := p
      exact (gates_realize μ (.equal t₁ t₂) ν hg w).trans
        (canonVal_rootAt μ (.equal t₁ t₂) w).symm
  | _, .rel R ts, ν, hg, _, p, w => by
      obtain ⟨rfl⟩ := p
      exact (gates_realize μ (.rel R ts) ν hg w).trans (canonVal_rootAt μ (.rel R ts) w).symm
  | _, .imp f₁ f₂, ν, hg, _, p, w => by
      obtain ⟨⟨rfl⟩⟩ | q | q := p
      · exact (gates_realize μ (f₁.imp f₂) ν hg w).trans
          (canonVal_rootAt μ (f₁.imp f₂) w).symm
      · exact gates_unique f₁ _ hg.2.1 _ q w
      · exact gates_unique f₂ _ hg.2.2 _ q w
  | _, .all f, ν, hg, _, p, w => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · exact (gates_realize μ f.all ν hg w).trans (canonVal_rootAt μ f.all w).symm
      · exact gates_unique f _ hg.2 _ q w

end Unique

section Canon

variable {L : Language.{0, 0}} {B : SOBlock} {A : Type} {D : ℕ}
variable [L.Structure A] [LE A]

/-- The tuple `x` is canonical for the propositional variable indexed by `v`:
padded from the arity on for a block variable, from the context length on for a
position variable. -/
def VarCanon {n : ℕ} {f : (L.sum B.lang).BoundedFormula Empty n}
    (v : B.ι ⊕ Σ m', NodeAt f m') (x : Fin D → A) : Prop :=
  match v with
  | Sum.inl i => Canon (B.arity i) x
  | Sum.inr σ => Canon σ.1 x

/-- **Variables of the encoding sit at canonical tuples**: a literal of a
clause of the Tseitin encoding is a propositional variable at a tuple that is
canonical for it. -/
theorem litSem_varCanon (s : Bool) :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n) (h : contextBound f ≤ D)
      {m : ℕ} (p : NodeAt f m) (k : Fin 3) (u : Fin D → A)
      (v : B.ι ⊕ Σ m', NodeAt f m') (x : Fin D → A),
      IsClauseSem f h p k u → LitSem s f h p k u v x → VarCanon v x
  | _, .falsum, _, _, _, _, _, _, _, hcl, hlit => by
      obtain ⟨-, -, rfl, rfl⟩ := hlit
      exact hcl.2
  | _, .equal _ _, _, _, _, _, _, _, _, hcl, hlit => by
      obtain ⟨rfl, rfl, -⟩ := hlit
      exact hcl.1
  | _, .rel R ts, _, _, _, _, _, _, _, hcl, hlit => by
      cases R with
      | inl r =>
          obtain ⟨rfl, rfl, -⟩ := hlit
          exact hcl.1
      | inr r =>
          rcases hlit with ⟨rfl, rfl, -⟩ | ⟨rfl, hat, -⟩
          · exact hcl.1
          · change Canon (B.arity r.1) _
            rw [r.2]
            exact hat.1
  | _, .imp f₁ f₂, h, _, p, k, u, v, x, hcl, hlit => by
      obtain ⟨⟨rfl⟩⟩ | q | q := p
      · obtain ⟨rfl, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := hlit <;> exact hcl
      · rcases v with i | ⟨m', (_ | q' | q')⟩
        · exact litSem_varCanon s f₁ ((le_max_left _ _).trans h) q k u (Sum.inl i) x hcl hlit
        · exact hlit.elim
        · exact litSem_varCanon s f₁ ((le_max_left _ _).trans h) q k u
            (Sum.inr ⟨m', q'⟩) x hcl hlit
        · exact hlit.elim
      · rcases v with i | ⟨m', (_ | q' | q')⟩
        · exact litSem_varCanon s f₂ ((le_max_right _ _).trans h) q k u (Sum.inl i) x hcl hlit
        · exact hlit.elim
        · exact hlit.elim
        · exact litSem_varCanon s f₂ ((le_max_right _ _).trans h) q k u
            (Sum.inr ⟨m', q'⟩) x hcl hlit
  | n, .all f, h, _, p, k, u, v, x, hcl, hlit => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · rcases hlit with ⟨hk, ⟨-, rfl, -, hx⟩ | ⟨-, rfl, rfl⟩⟩ |
          ⟨hk, ⟨-, rfl, rfl⟩ | ⟨-, rfl, -, hx⟩⟩
        · exact hx
        · rcases hcl with ⟨-, hu⟩ | ⟨hk', -⟩
          · exact hu
          · rw [hk] at hk'
            exact absurd hk' (by decide)
        · rcases hcl with ⟨hk', -⟩ | ⟨-, hu⟩
          · rw [hk] at hk'
            exact absurd hk' (by decide)
          · exact hu
        · exact hx
      · rcases v with i | ⟨m', (_ | q')⟩
        · exact litSem_varCanon s f h q k u (Sum.inl i) x hcl hlit
        · exact hlit.elim
        · exact litSem_varCanon s f h q k u (Sum.inr ⟨m', q'⟩) x hcl hlit

end Canon

end Tseitin

end DescriptiveComplexity
