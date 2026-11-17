/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Constraints.Basic
import Mathlib.Tactic.Bound.Init

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # The signed translation of constraints with variance

A constraint with variance `c` is translated into a covariant constraint over two signed copies `u⁺`
and `u⁻` of each variable (`signed`): the positive copy stands for the normalization of the value of
`u` and the negative copy for the normalization of its dual. A solution with variance gives a
covariant solution of the translation that is fixed by sign duality (exchanging the two copies and
dualizing), and every such fixed solution decodes to a solution with variance
(`normalized_decoded`).

## Main declarations

- `signedVar`, `base`, `sign`: the signed copies of the variables.
- `signedLit`, `signed`: the signed translation.
- `Signed.dual`: sign duality of assignments.
- `normalized`, `decoded`, `normalized_decoded`: solutions with variance as fixed
  solutions of the translation.
-/

@[expose] public section


namespace DeciSigma1.Constraints

open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n : ℕ} {V : Type*}

/-- The signed copy of a variable. -/
abbrev signedVar (u : V) (p : Bool) : V × Bool := (u, p)

/-- The underlying variable. -/
abbrev base (z : V × Bool) : V := z.1

/-- The sign of a variable. -/
abbrev sign (z : V × Bool) : Bool := z.2

@[simp] theorem base_signedVar (u : V) (p : Bool) : base (signedVar u p) = u := rfl
@[simp] theorem sign_signedVar (u : V) (p : Bool) : sign (signedVar u p) = p := rfl
@[simp] theorem signedVar_base_sign (z : V × Bool) : signedVar (base z) (sign z) = z := rfl

theorem exists_eq_signedVar (z : V × Bool) : ∃ u p, z = signedVar u p :=
  ⟨z.1, z.2, rfl⟩

/-- The signed translation of a literal: its covariant form on the positive copies and its dual form
on the negative copies. -/
def signedLit (c : Fin n → Bool) : LitT n V → List (LitT n (V × Bool))
  | .le u v => [.le (u, false) (v, false), .le (v, true) (u, true)]
  | .leF u a => [.leF (signedVar u false) (fun i => signedVar (a i) (c i)),
      .fLe (fun i => signedVar (a i) (!(c i))) (signedVar u true)]
  | .fLe a u => [.fLe (fun i => signedVar (a i) (c i)) (signedVar u false),
      .leF (signedVar u true) (fun i => signedVar (a i) (!(c i)))]
  | .eqBot u => [.eqBot (signedVar u false), .eqTop (signedVar u true)]
  | .eqTop u => [.eqTop (signedVar u false), .eqBot (signedVar u true)]

/-- The signed translation of a constraint. -/
def signed (c : Fin n → Bool) (Γ : List (LitT n V)) : List (LitT n (V × Bool)) :=
  Γ.flatMap (signedLit c)

/-- The sign dual of a signed assignment: the dual of the value of the opposite copy. -/
def Signed.dual (A : (V × Bool) → Semantics.Tree n) (z : (V × Bool)) : Semantics.Tree n :=
  Tree.dual (A (signedVar (base z) (!(sign z))))

@[simp] theorem signedDual_signedVar (A : (V × Bool) → Semantics.Tree n) (u : V) (p : Bool) :
    Signed.dual A (signedVar u p) = Tree.dual (A (signedVar u (!p))) := by simp [Signed.dual]

@[simp] theorem dual_eq_bot (t : Semantics.Tree n) : Tree.dual t = Tree.bot ↔ t = Tree.top := by
  constructor
  · intro h; have := congrArg Tree.dual h; simpa using this
  · rintro rfl; simp

@[simp] theorem dual_eq_top (t : Semantics.Tree n) : Tree.dual t = Tree.top ↔ t = Tree.bot := by
  constructor
  · intro h; have := congrArg Tree.dual h; simpa using this
  · rintro rfl; simp

@[simp] theorem sat_signed_iff (c : Fin n → Bool) (A : (V × Bool) → Semantics.Tree n)
    (Γ : List (LitT n V)) :
    Covariant.Sat A (signed c Γ) ↔ ∀ l ∈ Γ, Covariant.Sat A (signedLit c l) := by
  constructor
  · intro h l hl m hm
    exact h m (List.mem_flatMap.mpr ⟨l, hl, hm⟩)
  · intro h m hm
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp hm
    exact h l hl m hm

theorem sat_signedLit_signedDual_iff (c : Fin n → Bool) (A : (V × Bool) → Semantics.Tree n)
    (l : LitT n V) :
    Covariant.Sat (Signed.dual A) (signedLit c l) ↔ Covariant.Sat A (signedLit c l) := by
  cases l <;> simp
      [signedLit, Covariant.Sat, Covariant.Holds, Function.comp_def, ← dual_node, and_comm]

/-- The sign dual of a solution of the signed translation is again a solution: it exchanges the two
signed literals produced by each literal. -/
theorem sat_signedDual (c : Fin n → Bool) {A : (V × Bool) → Semantics.Tree n} {Γ : List (LitT n V)}
    (h : Covariant.Sat A (signed c Γ)) : Covariant.Sat (Signed.dual A) (signed c Γ) := by
  rw [sat_signed_iff] at h ⊢
  intro l hl
  exact (sat_signedLit_signedDual_iff c A l).mpr (h l hl)

/-- The signed assignment of an assignment with variance: the normalizations of each value at both
polarities. -/
def normalized (c : Fin n → Bool) (ρ : V → Semantics.Tree n) (z : (V × Bool)) : Semantics.Tree n :=
  Tree.normalize c (sign z) (ρ (base z))

@[simp] theorem normalized_signedVar (c : Fin n → Bool) (ρ : V → Semantics.Tree n) (u : V)
    (p : Bool) :
    normalized c ρ (signedVar u p) = Tree.normalize c p (ρ u) := by simp [normalized]

@[simp] theorem normalize_not (c : Fin n → Bool) (p : Bool) (t : Semantics.Tree n) :
    Tree.normalize c (!p) t = Tree.dual (Tree.normalize c p t) := by cases p <;> simp

@[simp] theorem normalize_false_eq_bot (c : Fin n → Bool) (t : Semantics.Tree n) :
    Tree.normalize c false t = Tree.bot ↔ t = Tree.bot := by
  constructor
  · intro h; have := congrArg (Tree.normalize c false) h; simpa using this
  · rintro rfl; simp

@[simp] theorem normalize_false_eq_top (c : Fin n → Bool) (t : Semantics.Tree n) :
    Tree.normalize c false t = Tree.top ↔ t = Tree.top := by
  constructor
  · intro h; have := congrArg (Tree.normalize c false) h; simpa using this
  · rintro rfl; simp

theorem holds_iff_signedLit (c : Fin n → Bool) (ρ : V → Semantics.Tree n) (l : LitT n V) :
    HoldsT c ρ l ↔ Covariant.Sat (normalized c ρ) (signedLit c l) := by
  cases l <;> simp [signedLit, Covariant.Sat, Covariant.Holds, HoldsT,
    treeLe_iff_normalize, Function.comp_def, ← dual_node]

/-- An assignment solves `Γ` with variance `c` exactly when its normalizations solve the signed
translation. -/
theorem sat_iff_signed (c : Fin n → Bool) (ρ : V → Semantics.Tree n) (Γ : List (LitT n V)) :
    SatT c ρ Γ ↔ Covariant.Sat (normalized c ρ) (signed c Γ) := by
  simp only [sat_signed_iff, SatT, holds_iff_signedLit]

/-- The assignment with variance decoded from the positive copies. -/
def decoded (c : Fin n → Bool) (A : (V × Bool) → Semantics.Tree n) (u : V) : Semantics.Tree n :=
  Tree.normalize c false (A (signedVar u false))

theorem normalized_decoded (c : Fin n → Bool) {A : (V × Bool) → Semantics.Tree n}
    (h : Signed.dual A = A) : normalized c (decoded c A) = A := by
  funext z
  obtain ⟨u, p, rfl⟩ := exists_eq_signedVar z
  cases p
  · simp [decoded]
  · have hh := congrFun h (signedVar u true)
    simpa [decoded] using hh

end DeciSigma1.Constraints
