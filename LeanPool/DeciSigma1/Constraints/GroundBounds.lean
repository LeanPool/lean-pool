/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Constraints.RankedExtensions
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Ground bounds as one-sided constructor literals

A ground bound `g ≤ x` or `x ≤ g`, with `g` a finite tree, is compiled into flat literals
(`GroundCompiler.compile`): each proper subtree occurrence of `g` is named by a fresh variable,
and every constructor literal has the direction of the bound. A solution of the compiled literals
satisfies the bound (`sound`), and an assignment that satisfies the bound extends to a solution
that gives each fresh variable the subtree at its occurrence (`complete`). The children of a
compiled constructor literal are fresh variables of greater occurrence depth than its bound, so
adding the compiled literals to a constraint gives a ranked extension (`extension`), which
creates no cycle clash.

## Main declarations

- `GroundCompiler.Occurrence`, `GroundCompiler.compile`: subtree occurrences and the compiled
  literals.
- `GroundCompiler.sound`, `GroundCompiler.complete`: the compiled literals express the bound.
- `GroundCompiler.extension`: compiling a bound gives a ranked extension.
-/

@[expose] public section


namespace DeciSigma1.Constraints.GroundCompiler
open DeciSigma1.Semantics
variable {n k : ℕ} {V : Type*}

/-- The proper subtree occurrences of a finite tree. -/
abbrev Occurrence : FTree n → Type
  | .bot | .top => Empty
  | .node a => Σ i : Fin n, Option (Occurrence (a i))

noncomputable instance occFintype (g : FTree n) : Fintype (Occurrence g) := by
  induction g with
  | bot => exact inferInstanceAs (Fintype Empty)
  | top => exact inferInstanceAs (Fintype Empty)
  | node a ih =>
    letI (i : Fin n) : Fintype (Occurrence (a i)) := ih i
    exact inferInstanceAs (Fintype (Σ i : Fin n, Option (Occurrence (a i))))

/-- The depth of a proper occurrence. -/
def depth : (g : FTree n) → Occurrence g → ℕ
  | .bot, o | .top, o => o.elim
  | .node _, ⟨_, none⟩ => 1
  | .node a, ⟨i, some o⟩ => depth (a i) o + 1

/-- The subtree at an occurrence. -/
def value : (g : FTree n) → Occurrence g → FTree n
  | .bot, o | .top, o => o.elim
  | .node a, ⟨i, none⟩ => a i
  | .node a, ⟨i, some o⟩ => value (a i) o

/-- The literals of the ground bound `g ≤ x` (`lower = true`) or `x ≤ g` (`lower = false`), where
`e` names the proper subtree occurrences of `g`: a constructor literal in the direction of the
bound at each constructor of `g`, and an equation to `⊤` or `⊥` at each leaf of `g` where the
bound is not trivial. -/
def compile (lower : Bool) (x : V) : (g : FTree n) → (Occurrence g → V) → List (LitT n (V))
  | .bot, _ => if lower then [] else [.eqBot x]
  | .top, _ => if lower then [.eqTop x] else []
  | .node a, e =>
      (if lower then .fLe (fun i => e ⟨i, none⟩) x else .leF x (fun i => e ⟨i, none⟩)) ::
        (List.finRange n).flatMap fun i =>
          compile lower (e ⟨i, none⟩) (a i) (fun o => e ⟨i, some o⟩)

/-- Every solution of the compiled literals satisfies the bound. -/
theorem sound (lower : Bool) (g : FTree n) (x : V) (e : Occurrence g → V)
    {ρ : V → Tree n} (h : Covariant.Sat ρ (compile lower x g e)) :
    if lower then g.toTree ≤ ρ x else ρ x ≤ g.toTree := by
  induction g generalizing x with
  | bot => cases lower <;> simp_all [compile, Covariant.Sat, Covariant.Holds]
  | top => cases lower <;> simp_all [compile, Covariant.Sat, Covariant.Holds]
  | node a ih =>
    rw [compile, sat_cons] at h
    have hc (i : Fin n) :
        Covariant.Sat ρ (compile lower (e ⟨i, none⟩) (a i) (fun o => e ⟨i, some o⟩)) :=
      fun l hl => h.2 l (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hl⟩)
    cases lower with
    | false => exact le_trans h.1 ((Tree.node_le_node_iff _ _).mpr
        (fun i => ih i _ _ (hc i)))
    | true => exact le_trans ((Tree.node_le_node_iff _ _).mpr
        (fun i => ih i _ _ (hc i))) h.1

/-- An assignment that satisfies the bound and gives the variable of each occurrence the subtree
at that occurrence satisfies the compiled literals. -/
theorem sat_values (lower : Bool) (g : FTree n) (x : V) (e : Occurrence g → V)
    (ρ : V → Tree n) (he : ∀ o, ρ (e o) = (value g o).toTree)
    (h : if lower then g.toTree ≤ ρ x else ρ x ≤ g.toTree) :
    Covariant.Sat ρ (compile lower x g e) := by
  induction g generalizing x with
  | bot => cases lower <;> simp_all [compile, Covariant.Sat, Covariant.Holds]
  | top => cases lower <;> simp_all [compile, Covariant.Sat, Covariant.Holds]
  | node a ih =>
    rw [compile, sat_cons]
    constructor
    · have ha : (fun i => ρ (e ⟨i, none⟩)) = fun i => (a i).toTree :=
        funext fun i => he ⟨i, none⟩
      cases lower <;> simpa [Covariant.Holds, Function.comp_def, ha] using h
    · intro l hl
      obtain ⟨i, _, hl⟩ := List.mem_flatMap.mp hl
      apply ih i _ _ (fun o => he ⟨i, some o⟩) _ l hl
      rw [he ⟨i, none⟩]
      cases lower <;> exact le_rfl

/-- The condition on a compiled literal: a constructor literal has the direction of the bound and
children in `Fresh` of strictly greater rank than its bound, and no literal is a variable
inequality. -/
def IsRankedLiteral (lower : Bool) (Fresh : V → Prop) (rank : V → ℕ) : LitT n (V) → Prop
  | .fLe a x => lower = true ∧ (∀ i, Fresh (a i) ∧ rank x < rank (a i))
  | .leF x a => lower = false ∧ (∀ i, Fresh (a i) ∧ rank x < rank (a i))
  | .le _ _ => False
  | .eqBot _ | .eqTop _ => True

/-- Every compiled literal satisfies `IsRankedLiteral` when the variables of the occurrences lie in
`Fresh` and have the rank of `x` plus the depth of their occurrence. -/
theorem isRankedLiteral_compile (lower : Bool) (g : FTree n) (x : V) (e : Occurrence g → V)
    (Fresh : V → Prop) (rank : V → ℕ)
    (hf : ∀ o, Fresh (e o)) (hr : ∀ o, rank (e o) = rank x + depth g o) :
    ∀ l ∈ compile lower x g e, IsRankedLiteral lower Fresh rank l := by
  induction g generalizing x with
  | bot => cases lower <;> simp [compile, IsRankedLiteral]
  | top => cases lower <;> simp [compile, IsRankedLiteral]
  | node a ih =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · have hi (i : Fin n) : Fresh (e ⟨i, none⟩) ∧ rank x < rank (e ⟨i, none⟩) := by
        refine ⟨hf _, ?_⟩
        rw [hr ⟨i, none⟩]
        simp [depth]
      cases lower <;> exact ⟨rfl, hi⟩
    · obtain ⟨i, _, hl⟩ := List.mem_flatMap.mp hl
      apply ih i _ _ (fun o => hf ⟨i, some o⟩) _ l hl
      intro o
      rw [hr ⟨i, some o⟩, hr ⟨i, none⟩]
      simp [depth, Nat.add_assoc, Nat.add_comm]

/-- The fresh variable of an occurrence: the occurrences are numbered after the `k` original
variables. -/
noncomputable def occurrenceVar (g : FTree n) :
    Occurrence g → Fin (k + Fintype.card (Occurrence g)) :=
  fun o => Fin.natAdd k (Fintype.equivFin (Occurrence g) o)

/-- The extension of an assignment that gives each fresh variable the subtree at its
occurrence. -/
noncomputable def extend (g : FTree n) (ρ : Fin k → Tree n) :
    Fin (k + Fintype.card (Occurrence g)) → Tree n :=
  Fin.addCases ρ (fun i => (value g ((Fintype.equivFin (Occurrence g)).symm i)).toTree)

@[simp] theorem extend_original (g : FTree n) (ρ : Fin k → Tree n) (x : Fin k) :
    extend g ρ (Fin.castAdd _ x) = ρ x := by simp [extend]

@[simp] theorem extend_fresh (g : FTree n) (ρ : Fin k → Tree n) (o : Occurrence g) :
    extend g ρ (occurrenceVar g o) = (value g o).toTree := by simp [extend, occurrenceVar]

/-- An assignment that satisfies the bound extends to a solution of the compiled literals. -/
theorem complete (lower : Bool) (g : FTree n) (x : Fin k) (ρ : Fin k → Tree n)
    (h : if lower then g.toTree ≤ ρ x else ρ x ≤ g.toTree) :
    Covariant.Sat (extend g ρ) (compile lower (Fin.castAdd _ x) g (occurrenceVar g)) := by
  apply sat_values lower g _ _ _ (extend_fresh g ρ)
  simpa using h

/-- The rank of a variable: zero for an original variable, and the depth of its occurrence for a
fresh variable. -/
noncomputable def rank (g : FTree n) : Fin (k + Fintype.card (Occurrence g)) → ℕ :=
  Fin.addCases (fun _ => 0) (fun i => depth g ((Fintype.equivFin (Occurrence g)).symm i))

/-- Adding the compiled literals of a ground bound to a constraint `Γ` gives a ranked extension
of `Γ`: the fresh variables are sources for a lower bound and sinks for an upper bound. -/
theorem extension (lower : Bool) (g : FTree n) (x : Fin k) (Γ : List (LitT n (Fin k))) :
    Ranked.Extension Γ (lift Γ _ ++ compile lower (Fin.castAdd _ x) g (occurrenceVar g))
      (fun z => lower = true ∧ k ≤ z.val) (fun z => lower = false ∧ k ≤ z.val) (rank g) := by
  let Fresh : Fin (k + Fintype.card (Occurrence g)) → Prop := fun z => k ≤ z.val
  have hf (o : Occurrence g) : Fresh (occurrenceVar g o) := by simp [Fresh, occurrenceVar]
  have hr (o : Occurrence g) : rank (k := k) g (occurrenceVar g o) = rank g (Fin.castAdd _ x) +
      depth g o := by
    simp [rank, occurrenceVar]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; omega
  · intro z hz; omega
  · intro z hz ht; simp_all
  · intro z
    by_cases hz : z.val < k
    · exact Or.inl ⟨⟨z.val, hz⟩, rfl⟩
    · cases lower <;> simp_all
  · intro l hl
    exact List.mem_append_left _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
  · intro a b hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨l, hl, he⟩ := List.mem_map.mp hz
      cases l <;> simp only [LitT.map, LitT.le.injEq, reduceCtorEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, hl, rfl, rfl⟩
    · exact False.elim (isRankedLiteral_compile lower g _ _ Fresh (rank g) hf hr _ hz)
  · intro a z hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨l, hl, he⟩ := List.mem_map.mp hz
      cases l <;> simp only [LitT.map, LitT.fLe.injEq, reduceCtorEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inl ⟨_, _, hl, rfl, rfl⟩
    · obtain ⟨hd, ha⟩ := isRankedLiteral_compile lower g _ _ Fresh (rank g) hf hr _ hz
      exact Or.inr ⟨fun i => ⟨⟨hd, (ha i).1⟩, (ha i).2⟩, by simp [hd]⟩
  · intro z a hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨l, hl, he⟩ := List.mem_map.mp hz
      cases l <;> simp only [LitT.map, LitT.leF.injEq, reduceCtorEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inl ⟨_, _, hl, rfl, rfl⟩
    · obtain ⟨hd, ha⟩ := isRankedLiteral_compile lower g _ _ Fresh (rank g) hf hr _ hz
      exact Or.inr ⟨fun i => ⟨⟨hd, (ha i).1⟩, (ha i).2⟩, by simp [hd]⟩

end DeciSigma1.Constraints.GroundCompiler
