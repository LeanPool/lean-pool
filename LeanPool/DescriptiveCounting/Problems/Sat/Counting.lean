/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Problems.Sat
public import LeanPool.DescriptiveCounting.Counting.Class
import all LeanPool.DescriptiveCounting.Counting
import all LeanPool.DescriptiveCounting.Counting.SharpP

/-!
# #SAT: counting the models of a CNF formula

The counting version of `DescriptiveComplexity.SAT`, on the same vocabulary: the
number of *models* of a CNF formula ([Valiant 1979][valiant1979complexity]).

A model is a set of true variables satisfying every clause, and it is a set of
variables *of the formula*: an element that occurs in no clause is not a
variable (`DescriptiveComplexity.SatOccurs`), and a model does not contain it
(`DescriptiveComplexity.SatModel`). Without that convention every clause element and
every unused element of an instance would double the count, where the decision
problem can afford to leave them unconstrained.

`DescriptiveComplexity.SharpSAT` is the bundled counting problem; its support is SAT
(`DescriptiveComplexity.sharpSat_support_iff`), and it belongs to `#P`
(`DescriptiveComplexity.sharpSat_mem_sharpP`), the models being the witnesses of the
`Σ₁` definition of SAT with one conjunct added to the kernel. Its hardness is
in `DescriptiveComplexity.Problems.Sat.CountingHardness`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Models

variable (A : Type) [Language.sat.Structure A]

/-- The set `ν` of true variables is a model of the CNF formula: every clause
contains a true literal, and `ν` consists of variables of the formula. -/
def SatModel (ν : A → Prop) : Prop :=
  (∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)) ∧
  ∀ x : A, ν x → SatOccurs A x

variable {A}

/-- A satisfying assignment restricts to a model: only the values at the
variables of the formula matter. -/
theorem satModel_restrict {ν : A → Prop}
    (h : ∀ c : A, RelMap satIsClause ![c] →
      ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)) :
    SatModel A fun x => ν x ∧ SatOccurs A x := by
  refine ⟨fun c hc => ?_, fun x hx => hx.2⟩
  obtain ⟨x, ⟨hp, hx⟩ | ⟨hn, hx⟩⟩ := h c hc
  · exact ⟨x, Or.inl ⟨hp, hx, c, hc, Or.inl hp⟩⟩
  · exact ⟨x, Or.inr ⟨hn, fun h' => hx h'.1⟩⟩

/-- Models transport along an isomorphism. -/
private theorem satModel_equiv {B : Type} [Language.sat.Structure B] (e : A ≃[Language.sat] B)
    (ν : B → Prop) : SatModel A (fun a => ν (e a)) ↔ SatModel B ν := by
  have h1 : ∀ c, (RelMap satIsClause ![e c] : Prop) ↔ RelMap satIsClause ![c] :=
    fun c => (relMap_equiv₁ e satIsClause c).symm
  have h2 : ∀ c x, (RelMap satPosIn ![e c, e x] : Prop) ↔ RelMap satPosIn ![c, x] :=
    fun c x => (relMap_equiv₂ e satPosIn c x).symm
  have h3 : ∀ c x, (RelMap satNegIn ![e c, e x] : Prop) ↔ RelMap satNegIn ![c, x] :=
    fun c x => (relMap_equiv₂ e satNegIn c x).symm
  have hocc : ∀ x, SatOccurs A x ↔ SatOccurs B (e x) := by
    intro x
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨e c, (h1 c).mpr hc, h.imp (h2 c x).mpr (h3 c x).mpr⟩
    · rintro ⟨c, hc, h⟩
      obtain ⟨c, rfl⟩ := e.toEquiv.surjective c
      exact ⟨c, (h1 c).mp hc, h.imp (h2 c x).mp (h3 c x).mp⟩
  constructor
  · rintro ⟨hcl, hvar⟩
    refine ⟨fun c hc => ?_, fun x hx => ?_⟩
    · obtain ⟨c, rfl⟩ := e.toEquiv.surjective c
      obtain ⟨x, h⟩ := hcl c ((h1 c).mp hc)
      exact ⟨e x, h.imp (fun h => ⟨(h2 c x).mpr h.1, h.2⟩) fun h => ⟨(h3 c x).mpr h.1, h.2⟩⟩
    · obtain ⟨x, rfl⟩ := e.toEquiv.surjective x
      exact (hocc x).mp (hvar x hx)
  · rintro ⟨hcl, hvar⟩
    refine ⟨fun c hc => ?_, fun x hx => (hocc x).mpr (hvar _ hx)⟩
    obtain ⟨x, h⟩ := hcl (e c) ((h1 c).mpr hc)
    obtain ⟨x, rfl⟩ := e.toEquiv.surjective x
    exact ⟨x, h.imp (fun h => ⟨(h2 c x).mp h.1, h.2⟩) fun h => ⟨(h3 c x).mp h.1, h.2⟩⟩

/-- A CNF formula is satisfiable exactly when it has a model. -/
private theorem satisfiable_iff_exists_satModel : Satisfiable A ↔ ∃ ν : A → Prop, SatModel A ν :=
  ⟨fun ⟨_, hν⟩ => ⟨_, satModel_restrict hν⟩, fun ⟨ν, hν⟩ => ⟨ν, hν.1⟩⟩

end Models

/-! ### The kernel -/

section Kernel

open SOBlock

/-- Kernel conjunct: the truth assignment only holds of variables of the
formula, i.e., of elements occurring in a clause. -/
noncomputable def satVarKernel : satSOLang.Sentence :=
  fo% ∀ x, kNuSym(x) → ∃ c, kIsClSym(c) ∧ (kPosSym(c, x) ∨ kNegSym(c, x))

/-- The first-order kernel of #SAT: the kernel of SAT, and the truth assignment
only holds of variables of the formula. -/
noncomputable def sharpSatKernel : satSOLang.Sentence :=
  satKernel ⊓ satVarKernel

/-- Unary relations, as assignments of the truth-assignment block. -/
def satAssignEquiv (A : Type) : (A → Prop) ≃ satAssignBlock.Assignment A where
  toFun ν := fun _ x => ν (x ⟨0, Nat.one_pos⟩)
  invFun ρ := fun a => ρ satNuSym.1 fun _ => a
  left_inv _ := rfl
  right_inv ρ := by
    funext i x
    exact congrArg (ρ i) (funext fun j =>
      congrArg x (@Subsingleton.elim (Fin 1) _ _ _))

/-- Realization of the variable conjunct: the assignment holds only of
variables of the formula. -/
private theorem realize_satVarKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) satVarKernel) ↔
      ∀ x : A, (satAssignEquiv A).symm ρ x → SatOccurs A x := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [satVarKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  constructor
  · intro h x hx
    obtain ⟨c, hc, hor⟩ := h (fun _ => x) hx
    exact ⟨c 0, hc, hor⟩
  · intro h x hx
    obtain ⟨c, hc, hor⟩ := h (x 0) hx
    exact ⟨fun _ => c, hc, hor⟩

/-- Realization of the kernel of #SAT: the assignment is a model. -/
private theorem realize_sharpSatKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) sharpSatKernel) ↔
      SatModel A ((satAssignEquiv A).symm ρ) := by
  have h1 := realize_satKernel ρ
  have h2 := realize_satVarKernel ρ
  let := satAssignBlock.structure ρ
  rw [sharpSatKernel, Sentence.Realize, Formula.realize_inf]
  exact and_congr h1 h2

end Kernel

/-! ### The counting problem -/

/-- The number of models of a CNF formula is the number of witnesses of the
kernel of #SAT. -/
theorem card_satModel_eq_witnessCount (A : Type) [Language.sat.Structure A] :
    Nat.card {ν : A → Prop // SatModel A ν} = witnessCount satAssignBlock sharpSatKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_sharpSatKernel, Equiv.symm_apply_apply])

/-- **#SAT**: the number of models of a CNF formula. -/
noncomputable def SharpSAT : CountingProblem Language.sat where
  Count := fun A inst => Nat.card {ν : A → Prop // @SatModel A inst ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_satModel_eq_witnessCount A, card_satModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock sharpSatKernel e

theorem sharpSat_apply (A : Type) [Language.sat.Structure A] :
    SharpSAT A = Nat.card {ν : A → Prop // SatModel A ν} :=
  rfl

/-- **The support of #SAT is SAT**: on a finite structure, the number of models
is positive exactly when the formula is satisfiable. -/
theorem sharpSat_support_iff (A : Type) [Language.sat.Structure A] [Finite A] :
    SharpSAT.support A ↔ SAT A := by
  rw [CountingProblem.support_iff, sharpSat_apply, Nat.card_pos_iff]
  refine Iff.trans ?_ satisfiable_iff_exists_satModel.symm
  exact ⟨fun ⟨⟨ν, hν⟩, _⟩ => ⟨ν, hν⟩, fun ⟨ν, hν⟩ => ⟨⟨⟨ν, hν⟩⟩, inferInstance⟩⟩

/-- **#SAT is in `#P`**: the models of a CNF formula are the witnesses of an
existential second-order sentence. -/
theorem sharpSat_mem_sharpP : SharpSAT ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_satModel_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock sharpSatKernel)

end DescriptiveComplexity
