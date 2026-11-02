/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Bad reduction of an integer polynomial at a prime: degree loss or failure of absolute
irreducibility modulo `p`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Bad reduction at `p`: `p` is prime and the reduction of `f` over the algebraic closure of
`𝔽_p` either has smaller total degree than `f` or is not irreducible. -/
def HypersurfaceBadReduction {σ : Type*} (f : MvPolynomial σ ℤ) (p : ℕ) : Prop :=
  ∃ hp : p.Prime, let _ : Fact p.Prime := ⟨hp⟩
    (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree ≠ f.totalDegree ∨
      ¬Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f)

/-- At a prime `p`, good reduction means that the reduction over the algebraic closure of
`𝔽_p` keeps the total degree and is irreducible. -/
lemma not_hypersurfaceBadReduction_iff {σ : Type*} (f : MvPolynomial σ ℤ) (p : ℕ)
    [Fact p.Prime] :
    ¬HypersurfaceBadReduction f p ↔
      (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree = f.totalDegree ∧
        Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hn
      exact h ⟨Fact.out, Or.inl hn⟩
    · by_contra hn
      exact h ⟨Fact.out, Or.inr hn⟩
  · rintro ⟨hdeg, hir⟩ ⟨_, hbad⟩
    exact hbad.elim (· hdeg) (· hir)

end
end CCDN
