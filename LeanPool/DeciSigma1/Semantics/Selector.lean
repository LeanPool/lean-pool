/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Constraints.Signed
public import LeanPool.DeciSigma1.Satisfiability.Shape

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Sign-symmetric solutions selected from a least shape

The signed translation of a constraint is closed under the involution that exchanges the two signed
copies of each variable, reverses the constructor literals and exchanges `⊥` and `⊤`. For such a
constraint the least shape `B` and its sign dual have the same constructor positions, and reading
`B` at paths of even signed polarity and its sign dual elsewhere gives a symmetric assignment
(`select`). The selected assignment solves the signed translation whenever `B` does (`select_sat`),
and it has bounded depth whenever `B` has; this gives finite solutions.

## Main declarations

- `SignSelection.flipV`, `SignSelection.FlipClosed`: the sign involution and closed constraints.
- `SignSelection.SameShape`: trees with the same constructor positions.
- `SignSelection.leastShape_sameShape_signedDual`: the least shape and its sign dual have the same
  shape.
- `SignSelection.select`, `select_sat`, `select_fixed`, `select_depth`: the selected symmetric
  solution.
-/

@[expose] public section


namespace DeciSigma1.Semantics.SignSelection

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability

variable {n : ℕ} {V : Type*}

/-! ## The sign involution -/

/-- Complement the sign of a signed variable: `u^p ↦ u^{1-p}`. -/
def flipV (z : (V × Bool)) : (V × Bool) := signedVar (base z) (!(sign z))

@[simp] theorem flipV_signedVar (u : V) (p : Bool) :
    flipV (signedVar u p) = signedVar u (!p) := by
  simp [flipV]

@[simp] theorem flipV_flipV (z : (V × Bool)) : flipV (flipV z) = z := by
  obtain ⟨u, p, rfl⟩ := exists_eq_signedVar z
  simp

/-- The sign dual reads the opposite sign. -/
theorem signedDual_eq_flipV (A : (V × Bool) → Tree n) (z : (V × Bool)) :
    dual A z = Tree.dual (A (flipV z)) := rfl

/-- The sign involution on literals: it reverses constructor literals, exchanges `⊥` and `⊤` and
flips the signs of all variables, keeping child positions. -/
def dualFlip : LitT n (V × Bool) → LitT n (V × Bool)
  | .le x y => .le (flipV y) (flipV x)
  | .leF x a => .fLe (flipV ∘ a) (flipV x)
  | .fLe a x => .leF (flipV x) (flipV ∘ a)
  | .eqBot x => .eqTop (flipV x)
  | .eqTop x => .eqBot (flipV x)

/-- A signed constraint is closed under the sign involution when it contains the image of each of
its literals. -/
def FlipClosed (ψ : List (LitT n (V × Bool))) : Prop :=
  ∀ l ∈ ψ, dualFlip l ∈ ψ

/-- The signed translation is closed under the sign involution: each literal of `Γ` produces a
pair of signed literals that the involution exchanges. -/
theorem signed_flipClosed (c : Fin n → Bool) (Γ : List (LitT n V)) :
    FlipClosed (signed c Γ) := by
  intro l hl
  obtain ⟨m, hm, hl⟩ := List.mem_flatMap.mp hl
  apply List.mem_flatMap.mpr
  refine ⟨m, hm, ?_⟩
  cases m <;> simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
  all_goals rcases hl with rfl | rfl <;> simp [dualFlip, Function.comp_def]

/-! ## The sign involution on derivations and path judgments -/

section Exchange

variable {ψ : List (LitT n (V × Bool))}

/-- On a closed constraint, the sign involution maps derivations to derivations with the endpoints
exchanged. -/
theorem derives_flip (hc : FlipClosed ψ) {u v : (V × Bool)} (h : Derives ψ u v) :
    Derives ψ (flipV v) (flipV u) := by
  induction h with
  | refl => exact .refl _
  | lit hl => exact .lit (hc _ hl)
  | trans _ _ ih ih' => exact ih'.trans ih
  | decomp i hl _ hu ih => exact Derives.decomp i (hc _ hu) ih (hc _ hl)

/-- On a closed constraint, the sign involution maps lower path judgments to upper ones. -/
theorem lowerAt_flip (hc : FlipClosed ψ) {π : List (Fin n)} {x y : (V × Bool)}
    (h : LowerAt ψ π x y) : UpperAt ψ π (flipV y) (flipV x) := by
  induction h with
  | nil hd => exact .nil (derives_flip hc hd)
  | cons hl hd _ ih => exact .cons (derives_flip hc hd) (hc _ hl) ih

/-- On a closed constraint, the sign involution maps upper path judgments to lower ones. -/
theorem upperAt_flip (hc : FlipClosed ψ) {π : List (Fin n)} {x y : (V × Bool)}
    (h : UpperAt ψ π x y) : LowerAt ψ π (flipV y) (flipV x) := by
  induction h with
  | nil hd => exact .nil (derives_flip hc hd)
  | cons hd hl _ ih => exact .cons (hc _ hl) (derives_flip hc hd) ih

/-- A constructor supported from below at `u^p` is a constructor supported from above at
`u^{1-p}`. -/
theorem lowerLabel_f_flip (hc : FlipClosed ψ) (z : (V × Bool)) (π : List (Fin n)) :
    LowerLabel ψ π .f z ↔ UpperLabel ψ π .f (flipV z) := by
  constructor
  · rintro ⟨a, y, hl, hp⟩
    exact ⟨flipV y, flipV ∘ a, hc _ hl, lowerAt_flip hc hp⟩
  · rintro ⟨y, b, hl, hp⟩
    exact ⟨flipV ∘ b, flipV y, hc _ hl, by simpa using upperAt_flip hc hp⟩

theorem upperLabel_f_flip (hc : FlipClosed ψ) (z : (V × Bool)) (π : List (Fin n)) :
    UpperLabel ψ π .f z ↔ LowerLabel ψ π .f (flipV z) := by
  have h := lowerLabel_f_flip hc (flipV z) π
  simp only [flipV_flipV] at h
  exact h.symm

/-- The constructor label of the least shape is invariant under the sign involution. -/
theorem shapeLabel_flip_f (hc : FlipClosed ψ) (z : (V × Bool)) (π : List (Fin n)) :
    shapeLabel ψ z π = .f ↔ shapeLabel ψ (flipV z) π = .f := by
  rw [shapeLabel_eq_f_iff, shapeLabel_eq_f_iff]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨(upperLabel_f_flip hc z π).mp hu, (lowerLabel_f_flip hc z π).mp hl⟩
  · rintro ⟨hl, hu⟩
    refine ⟨(lowerLabel_f_flip hc z π).mpr hu, ?_⟩
    have h := (lowerLabel_f_flip hc (flipV z) π).mp hl
    simpa using h

theorem active_shape_flip (hc : FlipClosed ψ) (z : (V × Bool)) (π : List (Fin n)) :
    IsLivePrefix (shapeLabel ψ z) π ↔ IsLivePrefix (shapeLabel ψ (flipV z)) π := by
  simp only [IsLivePrefix, shapeLabel_flip_f hc z]

/-- Constructor positions of the least shape agree at `u^p` and `u^{1-p}`. -/
theorem leastShape_flip_f (hc : FlipClosed ψ) (z : (V × Bool)) (π : List (Fin n)) :
    (leastShape ψ z).fn π = some .f ↔ (leastShape ψ (flipV z)).fn π = some .f := by
  classical
  have ha := active_shape_flip hc z π
  have hf := shapeLabel_flip_f hc z π
  rw [leastShape_fn, leastShape_fn]
  split_ifs <;> simp_all

end Exchange

/-! ## Equal shapes and path-dependent mixing -/

/-- Two trees with the same constructor positions (hence the same domain). -/
def SameShape (a b : Tree n) : Prop := ∀ π, a.fn π = some .f ↔ b.fn π = some .f

theorem SameShape.domain {a b : Tree n} (h : SameShape a b) (π : List (Fin n)) :
    (a.fn π).isSome = (b.fn π).isSome := by
  apply Bool.eq_iff_iff.mpr
  induction π using List.reverseRecOn with
  | nil => simp [Tree.root_isSome]
  | append_singleton π i => simp only [Tree.child_isSome_iff, h π]

/-- The tree that reads `b` at the paths `π` with `p ⊕ polarity c π = true` and `a` elsewhere;
`a` and `b` must have the same shape. -/
def mix (c : Fin n → Bool) (p : Bool) (a b : Tree n) (h : SameShape a b) : Tree n where
  fn π := if Bool.xor p (polarity c π) then b.fn π else a.fn π
  wf := by
    constructor
    · cases p
      · simpa using a.wf.1
      · simpa using b.wf.1
    · intro π i
      have hd := h.domain (π ++ [i])
      have hf := h π
      cases Bool.xor p (polarity c (π ++ [i])) <;>
        cases Bool.xor p (polarity c π) <;> simp_all [Tree.child_isSome_iff]

@[simp] theorem mix_fn (c : Fin n → Bool) (p : Bool) (a b : Tree n) (h : SameShape a b)
    (π : List (Fin n)) :
    (mix c p a b h).fn π = if Bool.xor p (polarity c π) then b.fn π else a.fn π := rfl

theorem mix_domain (c : Fin n → Bool) (p : Bool) (a b : Tree n) (h : SameShape a b)
    (π : List (Fin n)) : ((mix c p a b h).fn π).isSome = (a.fn π).isSome := by
  simp only [mix_fn]; split <;> simp_all [h.domain π]

/-- On a constraint closed under the sign involution, the least shape `B` and its sign dual have the
same constructor positions. -/
theorem leastShape_sameShape_signedDual {ψ : List (LitT n (V × Bool))} (hc : FlipClosed ψ)
    (z : (V × Bool)) : SameShape (leastShape ψ z) (dual (leastShape ψ) z) := by
  intro π
  rw [signedDual_eq_flipV]
  exact (leastShape_flip_f hc z π).trans
    (normalize_constructor (fun _ => false) true (leastShape ψ (flipV z)) π).symm

/-! ## Sign coherence -/

/-- A sign-coherent constraint: the two variables of a variable inequality have the same sign, and
the `i`-th child of a constructor literal has the sign of its bound shifted by `c i`. -/
def SignCoherent (c : Fin n → Bool) (ψ : List (LitT n (V × Bool))) : Prop :=
  (∀ x y, LitT.le x y ∈ ψ → sign x = sign y) ∧
  (∀ u a, LitT.leF u a ∈ ψ → ∀ i, sign (a i) = Bool.xor (sign u) (c i)) ∧
    (∀ a u, LitT.fLe a u ∈ ψ → ∀ i, sign (a i) = Bool.xor (sign u) (c i))

theorem signed_signCoherent (c : Fin n → Bool) (Γ : List (LitT n V)) :
    SignCoherent c (signed c Γ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v h
    obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
    cases l <;> simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false,
      LitT.le.injEq, reduceCtorEq] at hl
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · intro u a h i
    obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
    cases l with
    | leF x b =>
      simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false,
        LitT.leF.injEq, reduceCtorEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp
    | fLe b x =>
      simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false,
        LitT.leF.injEq, reduceCtorEq, false_or] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp
    | le x y => simp [signedLit] at hl
    | eqBot x => simp [signedLit] at hl
    | eqTop x => simp [signedLit] at hl
  · intro a u h i
    obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
    cases l with
    | leF x b =>
      simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false,
        LitT.fLe.injEq, reduceCtorEq, false_or] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp
    | fLe b x =>
      simp only [signedLit, List.mem_cons, List.not_mem_nil, or_false,
        LitT.fLe.injEq, reduceCtorEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp
    | le x y => simp [signedLit] at hl
    | eqBot x => simp [signedLit] at hl
    | eqTop x => simp [signedLit] at hl

/-! ## The selector -/

/-- The selected assignment: `B` at paths of even signed polarity `sign z ⊕ polarity c π`, and the
sign dual of `B` elsewhere. -/
def select (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) (z : (V × Bool)) : Tree n :=
  mix c (sign z) (B z) (dual B z) (h z)

theorem select_fn (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) (z : (V × Bool)) (π : List (Fin n)) :
    (select c B h z).fn π =
      if Bool.xor (sign z) (polarity c π) then (dual B z).fn π else (B z).fn π := rfl

/-- The selected assignment has the domain of `B`. -/
theorem select_domain (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) (z : (V × Bool)) (π : List (Fin n)) :
    ((select c B h z).fn π).isSome = ((B z).fn π).isSome :=
  mix_domain _ _ _ _ _ _

/-- The selected assignment has bounded depth whenever `B` has. -/
theorem select_depth (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) {D : ℕ}
    (hB : ∀ z π, ((B z).fn π).isSome → π.length ≤ D) (z : (V × Bool)) (π : List (Fin n))
    (hπ : ((select c B h z).fn π).isSome) : π.length ≤ D :=
  hB z π (by rwa [select_domain] at hπ)

/-- The selected assignment is fixed by sign duality. -/
theorem select_fixed (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) : dual (select c B h) = select c B h := by
  funext z
  obtain ⟨u, p, rfl⟩ := exists_eq_signedVar z
  apply Tree.ext; funext π
  simp only [signedDual_signedVar, dual_fn, select_fn, sign_signedVar, Bool.not_not]
  cases p <;> cases polarity c π <;> simp [Option.map_map, Function.comp_def]

/-- The selected assignment solves every sign-coherent constraint that `B` and its sign dual
solve. -/
theorem select_sat_of_coherent {c : Fin n → Bool} {ψ : List (LitT n (V × Bool))}
    (hψ : SignCoherent c ψ) {B : (V × Bool) → Tree n} (hs : Covariant.Sat B ψ)
        (hS : Covariant.Sat (dual B) ψ)
    (h : ∀ z, SameShape (B z) (dual B z)) : Covariant.Sat (select c B h) ψ := by
  intro l hl
  have hb := hs l hl
  have hc := hS l hl
  cases l with
  | le u v =>
    change B u ≤ B v at hb
    change dual B u ≤ dual B v at hc
    change select c B h u ≤ select c B h v
    intro π r s hr hs'
    rw [select_fn, hψ.1 u v hl] at hr
    rw [select_fn] at hs'
    split at hr <;> rename_i he
    · rw [ite_eq_left he] at hs'
      exact hc π r s hr hs'
    · rw [ite_eq_right he] at hs'
      exact hb π r s hr hs'
  | eqBot u =>
    change B u = Tree.bot at hb
    change dual B u = Tree.bot at hc
    change select c B h u = Tree.bot
    apply Tree.ext; funext π
    simp only [select_fn, hb, hc, ite_self]
  | eqTop u =>
    change B u = Tree.top at hb
    change dual B u = Tree.top at hc
    change select c B h u = Tree.top
    apply Tree.ext; funext π
    simp only [select_fn, hb, hc, ite_self]
  | leF u a =>
    change B u ≤ Tree.node (B ∘ a) at hb
    change dual B u ≤ Tree.node (dual B ∘ a) at hc
    change select c B h u ≤ Tree.node (select c B h ∘ a)
    intro π r s hr hs'
    cases π with
    | nil =>
      have he : s = .f := (Option.some.inj hs').symm
      subst he
      rw [select_fn] at hr
      split at hr
      · exact hc [] _ _ hr rfl
      · exact hb [] _ _ hr rfl
    | cons i π =>
      have hs'' : (select c B h (a i)).fn π = some s := hs'
      rw [select_fn, pol_cons, ← Bool.xor_assoc] at hr
      rw [select_fn, hψ.2.1 u a hl i] at hs''
      split at hr <;> rename_i he
      · rw [ite_eq_left he] at hs''
        exact hc (i :: π) _ _ hr hs''
      · rw [ite_eq_right he] at hs''
        exact hb (i :: π) _ _ hr hs''
  | fLe a u =>
    change Tree.node (B ∘ a) ≤ B u at hb
    change Tree.node (dual B ∘ a) ≤ dual B u at hc
    change Tree.node (select c B h ∘ a) ≤ select c B h u
    intro π r s hr hs'
    cases π with
    | nil =>
      have he : r = .f := (Option.some.inj hr).symm
      subst he
      rw [select_fn] at hs'
      split at hs'
      · exact hc [] _ _ rfl hs'
      · exact hb [] _ _ rfl hs'
    | cons i π =>
      have hr' : (select c B h (a i)).fn π = some r := hr
      rw [select_fn, pol_cons, ← Bool.xor_assoc] at hs'
      rw [select_fn, hψ.2.2 a u hl i] at hr'
      split at hs' <;> rename_i he
      · rw [ite_eq_left he] at hr'
        exact hc (i :: π) _ _ hr' hs'
      · rw [ite_eq_right he] at hr'
        exact hb (i :: π) _ _ hr' hs'

/-- The selected assignment solves the signed translation whenever `B` does. -/
theorem select_sat {c : Fin n → Bool} {Γ : List (LitT n V)} {B : (V × Bool) → Tree n}
    (hs : Covariant.Sat B (signed c Γ)) (h : ∀ z, SameShape (B z) (dual B z)) :
    Covariant.Sat (select c B h) (signed c Γ) :=
  select_sat_of_coherent (signed_signCoherent c Γ) hs (sat_signedDual c hs) h

end DeciSigma1.Semantics.SignSelection
