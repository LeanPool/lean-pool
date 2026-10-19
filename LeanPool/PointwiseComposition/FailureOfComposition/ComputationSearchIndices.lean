/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.KleeneNormalForm

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Concrete natural-number indices for the direct computation-search construction.
The graph equations proved here are standard-model equations. Their PA-provable
counterparts for the repository's arithmetized evaluator remain a separate task.
-/

@[expose] public section

namespace FailureOfComposition
namespace Kleene

open Encodable Denumerable _root_.Nat.Partrec

/-- The index Of construction in `FailureOfComposition.Kleene`. -/
noncomputable def indexOf (f : ℕ → Part ℕ) (hf : Partrec f) : ℕ :=
  encode (Classical.choose (Code.exists_code.mp (Partrec.nat_iff.mp hf)))

theorem eval_indexOf (f : ℕ → Part ℕ) (hf : Partrec f) (x : ℕ) : eval (indexOf f hf) x = f x :=
  by
  simp only [eval, indexOf, Denumerable.ofNat_encode]
  exact congrFun (Classical.choose_spec (Code.exists_code.mp (Partrec.nat_iff.mp hf))) x

/-- The guard Eval construction in `FailureOfComposition.Kleene`. -/
def guardEval (d n : ℕ) : Part ℕ :=
  ((if T₁ d d n then none else some n) : Option ℕ)

/-- The search Eval construction in `FailureOfComposition.Kleene`. -/
def searchEval (d : ℕ) (_x : ℕ) : Part ℕ :=
  Nat.rfind (fun n => Part.some (decide (T₁ d d n)))

theorem check_primrec (d : ℕ) : PrimrecPred (T₁ d d) :=
  T₁_primrec.comp ((Primrec.const (d, d)).pair Primrec.id)

theorem guardEval_partrec (d : ℕ) : Partrec (guardEval d) :=
  (Primrec.ite (check_primrec d) (Primrec.const none) Primrec.option_some).to_comp.ofOption

theorem searchEval_partrec (d : ℕ) : Partrec (searchEval d) :=
  Partrec.rfind (((check_primrec d).decide.to_comp.comp Computable.snd).to₂)

/-- The guard Index construction in `FailureOfComposition.Kleene`. -/
noncomputable def guardIndex (d : ℕ) : ℕ :=
  indexOf (guardEval d) (guardEval_partrec d)

/-- The search Index construction in `FailureOfComposition.Kleene`. -/
noncomputable def searchIndex (d : ℕ) : ℕ :=
  indexOf (searchEval d) (searchEval_partrec d)

/-- The identity Index construction in `FailureOfComposition.Kleene`. -/
def identityIndex : ℕ :=
  encode Code.id

/-- The empty Index construction in `FailureOfComposition.Kleene`. -/
noncomputable def emptyIndex : ℕ :=
  indexOf (fun _ => Part.none) Partrec.none

@[simp]
theorem guardIndex_spec (d x y : ℕ) : y ∈ eval (guardIndex d) x ↔ ¬T₁ d d x ∧ y = x :=
  by
  rw [guardIndex, eval_indexOf]
  by_cases h : T₁ d d x <;> simp [guardEval, h, eq_comm]

@[simp]
theorem searchIndex_spec (d x y : ℕ) :
    y ∈ eval (searchIndex d) x ↔ T₁ d d y ∧ ∀ r < y, ¬T₁ d d r :=
  by
  rw [searchIndex, eval_indexOf]
  change y ∈ Nat.rfind (fun n ↦ Part.some (decide (T₁ d d n))) ↔ _
  constructor
  · intro hy
    have h := Nat.mem_rfind.mp hy
    exact ⟨by simpa using h.1, fun r hr ↦ by simpa using h.2 hr⟩
  · rintro ⟨hy, hmin⟩
    apply Nat.mem_rfind.mpr
    exact ⟨by simpa using hy, fun {r} hr ↦ by simpa using hmin r hr⟩

@[simp]
theorem identityIndex_spec (x : ℕ) : eval identityIndex x = Part.some x := by
  simp [eval, identityIndex]

@[simp]
theorem emptyIndex_spec (x : ℕ) : eval emptyIndex x = Part.none :=
  eval_indexOf _ _ x

theorem guard_after_search (d x : ℕ) :
    eval (compIndex (guardIndex d) (searchIndex d)) x = Part.none :=
  by
  apply Part.ext
  intro y
  simp only [eval_compIndex, Part.mem_bind_iff, guardIndex_spec, searchIndex_spec,
    Part.notMem_none, iff_false]
  rintro ⟨z, ⟨hz, _⟩, hn, _⟩
  exact hn hz

theorem identity_after_search (d x : ℕ) :
    eval (compIndex identityIndex (searchIndex d)) x = eval (searchIndex d) x :=
  by
  apply Part.ext
  intro y
  simp [eval_compIndex]

theorem guard_eq_identity_of_divergence (d : ℕ) (hd : ¬FailureOfComposition.diagonalHalts d)
    (x : ℕ) : eval (guardIndex d) x = eval identityIndex x :=
  by
  apply Part.ext
  intro y
  have hn : ¬T₁ d d x := fun hx => hd ((diagonalHalts_iff d).mpr ⟨x, hx⟩)
  simp [hn]

theorem search_diverges_of_divergence (d : ℕ) (hd : ¬FailureOfComposition.diagonalHalts d)
    (x : ℕ) : eval (searchIndex d) x = Part.none :=
  by
  apply Part.ext
  intro y
  have hn : ¬T₁ d d y := fun hy => hd ((diagonalHalts_iff d).mpr ⟨y, hy⟩)
  simp [hn]

end Kleene
end FailureOfComposition

end

end PointwiseComposition
