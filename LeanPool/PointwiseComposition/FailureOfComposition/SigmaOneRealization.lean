/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.SigmaOneSemidecisionCore
public import LeanPool.PointwiseComposition.FailureOfComposition.ArithmeticFormulaAtoms
public import LeanPool.PointwiseComposition.FailureOfComposition.BoundedSemidecision
public import LeanPool.PointwiseComposition.FailureOfComposition.SigmaOneSearch
public import LeanPool.PointwiseComposition.FailureOfComposition.SigmaOneGraphWitness

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Internal semidecision and program realization of Sigma-one arithmetic formulas.
Every program is constructed from concrete Mathlib program descriptions, and
every correctness assertion quantifies over PA models rather than just ℕ.
-/

@[expose] public section

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition
namespace SigmaOneRealization

open ProgramGraph ArithmeticCodeCompiler ArithmeticFormulaAtoms BoundedSemidecision

/-- Accept the nonzero output of a Boolean program and return zero. -/
def truthProgram (c : PCode) : PCode :=
  acceptZeroProgram (.comp ConcreteEvaluator.isZeroProgram c)

private theorem exists_nonzero_bool {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐐] (P : Prop) :
    (∃ z : M, z ≠ 0 ∧ BoolValue P z) ↔ P :=
  by
  constructor
  · rintro ⟨z, hn, ⟨hp, _⟩ | ⟨_, hz⟩⟩
    · exact hp
    · exact False.elim (hn hz)
  · intro hp
    exact ⟨1, Arithmetic.one_ne_zero, Or.inl ⟨hp, rfl⟩⟩

section Semantics

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

theorem computes_truthProgram (c : PCode) (x y : M) :
    Computes (truthProgram c) x y ↔ y = 0 ∧ ∃ z : M, z ≠ 0 ∧ Computes c x z :=
  by
  rw [truthProgram, computes_acceptZero]
  simp only [computes_comp, ConcreteEvaluator.computes_isZero_iff]
  constructor
  · rintro ⟨hy, z, hz, h⟩
    rcases h with ⟨_, hbad⟩ | ⟨hn, _⟩
    · exact False.elim (zero_ne_one hbad)
    · exact ⟨hy, z, hn, hz⟩
  · rintro ⟨hy, z, hn, hz⟩
    exact ⟨hy, z, hz, Or.inr ⟨hn, trivial⟩⟩

end Semantics

theorem atom_semidecides {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) :
    Semidecides (.rel r ts) (truthProgram (compile (atomCode r ts))) :=
  by
  intro M _ _ _ v y
  rw [computes_truthProgram]
  simp only [computes_compile, atomCode_eval, exists_nonzero_bool]

theorem negAtom_semidecides {n k : ℕ} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Empty n) :
    Semidecides (.nrel r ts) (truthProgram (compile (negAtomCode r ts))) :=
  by
  intro M _ _ _ v y
  rw [computes_truthProgram]
  simp only [computes_compile, negAtomCode_eval, exists_nonzero_bool]

/-- Evaluate the bound and sequentially check the formula at each smaller
candidate, retaining the encoded environment as the recursion parameter. -/
def boundedProgram {n : ℕ} (t : ArithmeticSemiterm Empty n) (c : PCode) : PCode :=
  .comp (boundedAllProgram c) (.pair Nat.Partrec.Code.id (compile (termCode t)))

theorem bounded_semidecides {n : ℕ} (t : ArithmeticSemiterm Empty n)
    {φ : ArithmeticSemisentence (n + 1)} {c : PCode} (hφ : Semidecides φ c) :
    Semidecides (∀¹[“#0 < !!(Rew.bShift t)”] φ) (boundedProgram t c) :=
  by
  intro M _ _ _ v y
  have hbody (k : M) : Computes c (pair k (encodeVector v)) 0 ↔ φ.Evalb (k :> v) := by
    simpa only [encodeVector, Matrix.cons_val_zero, Matrix.cons_val_succ, eq_self_iff_true,
      true_and] using hφ M (k :> v) 0
  have hbound :
    Computes (.pair Nat.Partrec.Code.id (compile (termCode t))) (encodeVector v)
      (pair (encodeVector v) (t.valb v)) :=
    by
    apply (computes_pair _ _ _ _).mpr
    refine ⟨encodeVector v, t.valb v, (computes_id _ _).mpr rfl, ?_, rfl⟩
    exact (computes_compile _ _ _).mpr ((termCode_eval t _ v).mpr rfl)
  have hcomp :
    Computes (boundedProgram t c) (encodeVector v) y ↔
      Computes (boundedAllProgram c) (pair (encodeVector v) (t.valb v)) y :=
    by
    rw [boundedProgram, computes_comp]
    constructor
    · rintro ⟨u, hu, hc⟩
      rw [computes_unique _ _ _ _ hu hbound] at hc
      exact hc
    · intro hc
      exact ⟨_, hbound, hc⟩
  rw [hcomp, computes_boundedAll]
  simp only [hbody]
  simp [FFL.FirstOrder.ball, Semiterm.valb]

theorem or_semidecides {n : ℕ} {φ ψ : ArithmeticSemisentence n} {c d : PCode}
    (hφ : Semidecides φ c) (hψ : Semidecides ψ d) :
    Semidecides (φ ⋎ ψ) (SigmaOneSearch.unionProgram c d) :=
  by
  intro M _ _ _ v y
  rw [SigmaOneSearch.computes_unionProgram]
  simp [hφ M v 0, hψ M v 0]

theorem exists_semidecides {n : ℕ} {φ : ArithmeticSemisentence (n + 1)} {c : PCode}
    (hφ : Semidecides φ c) : Semidecides (∃¹ φ) (SigmaOneSearch.existsProgram c) :=
  by
  intro M _ _ _ v y
  have hbody (k : M) : Computes c (pair k (encodeVector v)) 0 ↔ φ.Evalb (k :> v) := by
    simpa only [encodeVector, Matrix.cons_val_zero, Matrix.cons_val_succ, eq_self_iff_true,
      true_and] using hφ M (k :> v) 0
  rw [SigmaOneSearch.computes_existsProgram]
  simp [hbody]

/-- Every Sigma-one arithmetic formula has a concrete zero-valued
semidecision program whose correctness holds in PA models. -/
theorem semidecision_exists {n : ℕ} (φ : ArithmeticSemisentence n) (hφ : Hierarchy Σ 1 φ) :
    ∃ c : PCode, Semidecides φ c :=
  by
  apply sigma₁_induction' hφ (P := fun _ φ => ∃ c : PCode, Semidecides φ c)
  · intro n
    exact ⟨.zero, verum_semidecides n⟩
  · intro n
    exact ⟨.rfind' .succ, falsum_semidecides n⟩
  · intro n t₁ t₂
    exact ⟨_, atom_semidecides Language.ORing.Rel.eq ![t₁, t₂]⟩
  · intro n t₁ t₂
    exact ⟨_, negAtom_semidecides Language.ORing.Rel.eq ![t₁, t₂]⟩
  · intro n t₁ t₂
    exact ⟨_, atom_semidecides Language.ORing.Rel.lt ![t₁, t₂]⟩
  · intro n t₁ t₂
    exact ⟨_, negAtom_semidecides Language.ORing.Rel.lt ![t₁, t₂]⟩
  · rintro n φ ψ _ _ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨_, and_semidecides hc hd⟩
  · rintro n φ ψ _ _ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨_, or_semidecides hc hd⟩
  · rintro n t φ _ ⟨c, hc⟩
    exact ⟨_, bounded_semidecides t hc⟩
  · rintro n φ _ ⟨c, hc⟩
    exact ⟨_, exists_semidecides hc⟩

/-- Every PA-provably functional Sigma-one graph has a program in the fixed
Mathlib numbering whose graph PA proves uniformly equivalent to it. -/
theorem realize_graph (F : ProofSearch.Graph) (hF : ProofSearch.Functional F) :
    ∃ e : ℕ, ProofSearch.Uniform 𝐏𝐀 (ConcreteEvaluator.eventualGraph e) F :=
  by
  obtain ⟨c, hc⟩ := semidecision_exists F.val F.sigma_prop
  exact ⟨encode (graphProgram c), realize_of_semidecides F hF c hc⟩

end SigmaOneRealization
end FailureOfComposition

end

end PointwiseComposition
