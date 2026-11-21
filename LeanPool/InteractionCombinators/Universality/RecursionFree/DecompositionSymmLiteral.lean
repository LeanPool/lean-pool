/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.Decomposition
public import LeanPool.InteractionCombinators.Universality.RecursionFree.ExpandedIso
public import LeanPool.InteractionCombinators.Text.RenameInj

/-!
# The canonical decomposition of a literally symmetric rule (page 86)

Lafont 1997, page 86 (PDF page 18): "To sum up, one can assume that in all cases
`φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, and `σ_{i,j}` is involutive." Part 3 of issue #66.

This file treats a rule `r : Rule S a a` of a symbol with itself that is *expanded* (every equation
is `p = t` with `p` a port and only internal wires in `t`) and *literally symmetric*: exchanging the
two cells gives the same net up to a permutation `π` of the internal wires,
`r.swap.net = r.net.bind (rename π)`. For such a rule the canonical decomposition `Rule.decompose`
(`RecursionFree/Decomposition.lean`) has `ψ` equal to `φ` up to a renumbering of the middle wires
(`τ`) and of the internal wires of the side, so `(φ, φ, τ⁻¹ σ)` is a symmetric decomposition whose
plug is the rule, and its permutation is involutive.

Contents, in the order of the file:

1. Auxiliary lemmas: `Term.bind_var_injective`, `Net.bind_var_injective`. Renaming the names of a
   tree or a net by an injective function is injective.
2. Renaming the internal wires of two parts: the definition `Half.rn`, its values `Half.rn_inl`,
   `Half.rn_inr_inl`, `Half.rn_inr_inr`, then `Half.rn_injective`, `Half.mem_vars_rn`,
   `Half.mem_middle_rn`, `Half.mem_inner_rn`, and `Half.half_rename`: renaming the internal wires
   of the two parts by a permutation renames the side by a bijection of its internal wires and the
   middle wires by any numbering compatible with the new one.
3. The parts of a literally symmetric rule: `Rule.SymmLit.swapName_rn`, the definition
   `Rule.SymmLit.ExpandedEq`, `Rule.SymmLit.leftRooted_swap`, `Rule.SymmLit.bind_rho`,
   `Rule.SymmLit.pi_invol` (`π` is involutive, by the rigidity lemma `Rule.eq_id_of_bind_eq` of
   `RecursionFree/ExpandedIso.lean`), and `Rule.SymmLit.leftPart_eq`, `rightPart_eq`,
   `leftSw_eq`, `rightSw_eq`: exchanging the cells exchanges the two parts.
4. Plugging a renamed copy of a side: `Rule.SymmLit.bind_add`, `Rule.SymmLit.midφ_congr'`,
   `Rule.SymmLit.plug_rename_equiv`.
5. Main result: `Rule.SymmLit.exists_symm_decomposition`, the decomposition `(φ, φ, σ)` with `σ`
   involutive of a literally symmetric expanded rule (page 86).
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: renaming is injective
-- ============================================================================================

/-- Renaming the names of a tree by an injective function is injective. -/
theorem Term.bind_var_injective
    -- the renaming, injective
    {ν μ : Type}
    {f : ν → μ}
    (hf : Function.Injective f) :
    Function.Injective (Term.bind (S := S) fun x => var (f x)) := by
  intro t u h
  induction t generalizing u with
  | var x =>
    cases u with
    | var y => exact congrArg var (hf (by simpa using h))
    | app β us => simp at h
  | app α ts ih =>
    cases u with
    | var y => simp at h
    | app β us =>
      simp only [Term.bind_app, Term.app.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have h3 := eq_of_heq h2
      congr 1
      funext i
      exact ih i (congrFun h3 i)

/-- Renaming the names of a net by an injective function is injective. -/
theorem Net.bind_var_injective
    -- the renaming, injective
    {ν μ : Type}
    {f : ν → μ}
    (hf : Function.Injective f) :
    Function.Injective (Net.bind (S := S) fun x => var (f x)) :=
  Multiset.map_injective (Sym2.map.injective (Term.bind_var_injective hf))

-- ============================================================================================
-- 2. Renaming the internal wires of two parts
-- ============================================================================================

namespace Half

-- the ports of the two cells and the internal wires
variable {a b n : ℕ}

/-- Renaming of the internal wires by `f`, ports fixed. -/
def rn
    -- the renaming of the internal wires
    (f : Fin n → Fin n) :
    Fin a ⊕ Fin b ⊕ Fin n → Fin a ⊕ Fin b ⊕ Fin n :=
  Sum.map id (Sum.map id f)

/-- `rn f` fixes the ports of the first cell. -/
@[simp] theorem rn_inl
    (f : Fin n → Fin n)
    (i : Fin a) :
    (rn (b := b) f (.inl i)) = .inl i := rfl

/-- `rn f` fixes the ports of the second cell. -/
@[simp] theorem rn_inr_inl
    (f : Fin n → Fin n)
    (j : Fin b) :
    (rn (a := a) f (.inr (.inl j))) = .inr (.inl j) := rfl

/-- `rn f` renames the internal wire `w` to `f w`. -/
@[simp] theorem rn_inr_inr
    (f : Fin n → Fin n)
    (w : Fin n) :
    (rn (a := a) (b := b) f (.inr (.inr w))) = .inr (.inr (f w)) := rfl

/-- `rn f` is injective when `f` is. -/
theorem rn_injective
    -- the renaming of the internal wires, injective
    {f : Fin n → Fin n}
    (hf : Function.Injective f) :
    Function.Injective (rn (a := a) (b := b) f) :=
  Sum.map_injective.2 ⟨Function.injective_id, Sum.map_injective.2 ⟨Function.injective_id, hf⟩⟩

-- the permutation of the internal wires, and two parts `X`, `Y` of a rule
variable (f : Equiv.Perm (Fin n)) (X Y : Net S (Fin a ⊕ Fin b ⊕ Fin n))

/-- The image of a name by `rn f` is a name of the renamed net exactly when the name is a name of
the net. -/
theorem mem_vars_rn
    -- a name
    {x : Fin a ⊕ Fin b ⊕ Fin n} :
    rn f x ∈ (X.bind fun y => var (rn f y)).vars ↔ x ∈ X.vars := by
  rw [Net.vars_bind_var]
  exact Multiset.mem_map_of_injective (rn_injective f.injective)

/-- The image of a name by `rn f` is a middle wire of the renamed parts exactly when the name is
a middle wire of the parts. -/
theorem mem_middle_rn
    -- a name
    (x : Fin a ⊕ Fin b ⊕ Fin n) :
    rn f x ∈ middle (X.bind fun y => var (rn f y)) (Y.bind fun y => var (rn f y))
      ↔ x ∈ middle X Y := by
  rcases x with i | j | w
  · simpa using mem_vars_rn f Y (x := .inl i)
  · simpa using mem_vars_rn f X (x := .inr (.inl j))
  · simpa using
      and_congr (mem_vars_rn f X (x := .inr (.inr w))) (mem_vars_rn f Y (x := .inr (.inr w)))

/-- `f w` is an internal wire of the side of the renamed parts exactly when `w` is one of the side
of the parts. -/
theorem mem_inner_rn
    -- an internal wire
    (w : Fin n) :
    f w ∈ inner (X.bind fun y => var (rn f y)) (Y.bind fun y => var (rn f y))
      ↔ w ∈ inner X Y := by
  simpa using and_congr (mem_vars_rn f X (x := .inr (.inr w)))
    (not_congr (mem_vars_rn f Y (x := .inr (.inr w))))

/-- The sides of two parts renamed by a permutation `f` of the internal wires: the side is renamed
by a bijection `κ` of its internal wires, and its middle wires by `τ`, when the new numbering of
the middle wires is `τ` after the old one. -/
theorem half_rename
    -- the two parts renamed by `f`
    (X' Y' : Net S (Fin a ⊕ Fin b ⊕ Fin n))
    (hX : X' = X.bind fun y => var (rn f y))
    (hY : Y' = Y.bind fun y => var (rn f y))
    -- a numbering of the middle wires of the parts, and one of the middle wires of the renamed
    -- parts
    (k : ℕ)
    (mid : (x : Fin a ⊕ Fin b ⊕ Fin n) → x ∈ middle X Y → Fin k)
    (mid' : (x : Fin a ⊕ Fin b ⊕ Fin n) → x ∈ middle X' Y' → Fin k)
    -- the new numbering is `τ` after the old one
    (τ : Fin k → Fin k)
    (hmid : ∀ x (h : x ∈ middle X Y) (h' : rn f x ∈ middle X' Y'), mid' _ h' = τ (mid x h)) :
    -- there is a renaming `κ` of the internal wires of the side such that
    ∃ κ : Fin (inner X Y).card → Fin (inner X' Y').card,
      -- `κ` is a bijection,
      Function.Bijective κ ∧
      -- and the new side is the old one, its middle wires renamed by `τ`, its internal wires by `κ`
      (half X' Y' k mid').net
        = (half X Y k mid).net.bind fun y => var (Sum.map id (Sum.map τ κ) y) := by
  classical
  have hmidd : ∀ x, rn f x ∈ middle X' Y' ↔ x ∈ middle X Y := fun x => by
    rw [hX, hY]; exact mem_middle_rn f X Y x
  have hinn : ∀ w, f w ∈ inner X' Y' ↔ w ∈ inner X Y := fun w => by
    rw [hX, hY]; exact mem_inner_rn f X Y w
  have hw : ∀ m : Fin (inner X Y).card, ∃ w, ∃ h : w ∈ inner X Y, innerIdx X Y h = m := fun m => by
    obtain ⟨w, hw, he⟩ := rankIn_surj (M := inner X Y) Fin.val_injective m.isLt
    exact ⟨w, hw, Fin.ext he⟩
  choose wOf hwOf hwOfe using hw
  let κ : Fin (inner X Y).card → Fin (inner X' Y').card := fun m =>
    innerIdx X' Y' ((hinn _).2 (hwOf m))
  have hidx : ∀ {w w'} (h : w ∈ inner X Y) (h' : w' ∈ inner X Y),
      innerIdx X Y h = innerIdx X Y h' → w = w' := fun h h' e =>
    rankIn_injOn Fin.val_injective h h' (congrArg Fin.val e)
  have hidx' : ∀ {w w'} (h : w ∈ inner X' Y') (h' : w' ∈ inner X' Y'),
      innerIdx X' Y' h = innerIdx X' Y' h' → w = w' := fun h h' e =>
    rankIn_injOn Fin.val_injective h h' (congrArg Fin.val e)
  have hκ : ∀ w (h : w ∈ inner X Y) (h' : f w ∈ inner X' Y'),
      κ (innerIdx X Y h) = innerIdx X' Y' h' := by
    intro w h h'
    have e : wOf (innerIdx X Y h) = w := hidx _ h (hwOfe _)
    refine Fin.ext ?_
    have e' : (κ (innerIdx X Y h)).val =
        rankIn (inner X' Y') Fin.val (f (wOf (innerIdx X Y h))) := rfl
    rw [e', e]
    rfl
  refine ⟨κ, ⟨fun m m' e => ?_, fun m' => ?_⟩, ?_⟩
  · have := f.injective (hidx' _ _ e)
    rw [← hwOfe m, ← hwOfe m']
    exact Fin.ext (by simp only [innerIdx, this])
  · obtain ⟨w', hw', he⟩ := rankIn_surj (M := inner X' Y') Fin.val_injective m'.isLt
    have h1 : f (f.symm w') ∈ inner X' Y' := by rwa [Equiv.apply_symm_apply]
    have h0 : f.symm w' ∈ inner X Y := (hinn _).1 h1
    refine ⟨innerIdx X Y h0, (hκ _ h0 h1).trans (Fin.ext ?_)⟩
    simp only [innerIdx, Equiv.apply_symm_apply]
    exact he
  · apply Net.bind_var_injective (f := (some : _ → Option _)) (Option.some_injective _)
    have e1 := half_bind X' Y' k mid' (fun y => some y) (ren X' Y' k mid')
      (fun x h => (ren_of_mem X' Y' k mid' h).symm)
      (fun i hi => by simp [ren, hi])
      (fun w h hw => by simp [ren, hw, h])
    have e2 := half_bind X Y k mid (fun y => some (Sum.map id (Sum.map τ κ) y))
      (fun x => ren X' Y' k mid' (rn f x))
      (fun x h => by
        have h' := (hmidd x).2 h
        rw [ren_of_mem X' Y' k mid' h', hmid x h h']
        rfl)
      (fun i hi => by
        have hi' : rn f (.inl i) ∉ middle X' Y' := fun h => hi ((hmidd _).1 h)
        simp only [rn_inl] at hi'
        simp [ren, hi'])
      (fun w h hw => by
        have hw' : rn f (.inr (.inr w)) ∉ middle X' Y' := fun h => hw ((hmidd _).1 h)
        have h' := (hinn w).2 h
        simp only [rn_inr_inr] at hw' ⊢
        simp [ren, hw', h', hκ w h h'])
    have hXb : X'.bind (fun x => var (ren X' Y' k mid' x)) =
        X.bind fun x => var (ren X' Y' k mid' (rn f x)) := by
      rw [show X'.bind (fun x => var (ren X' Y' k mid' x)) =
          (X.bind fun y => var (rn f y)).bind (fun x => var (ren X' Y' k mid' x)) from
        congrArg _ hX, Net.bind_bind]
      simp only [Term.bind_var]
    have hout : leftsOut X' Y' = leftsOut X Y := by
      ext i
      rw [mem_leftsOut, mem_leftsOut, ← hmidd]
      rfl
    have e3 : Net.bind (fun x => var (some x))
        (Net.bind (fun y => var (Sum.map id (Sum.map τ κ) y)) (halfNet X Y k mid)) =
        Net.bind (fun y => var (some (Sum.map id (Sum.map τ κ) y))) (halfNet X Y k mid) := by
      rw [Net.bind_bind]
      simp only [Term.bind_var]
    change Net.bind (fun x => var (some x)) (halfNet X' Y' k mid') =
      Net.bind (fun x => var (some x))
        (Net.bind (fun y => var (Sum.map id (Sum.map τ κ) y)) (halfNet X Y k mid))
    rw [e3]
    refine e1.trans ?_
    rw [hXb, hout]
    exact e2.symm

end Half

namespace Rule.SymmLit

open Half

-- the arity of the symbol, which interacts with itself
variable {a : ℕ}

-- ============================================================================================
-- 3. The parts of a literally symmetric rule
-- ============================================================================================

/-- Renaming the internal wires commutes with exchanging the two groups of ports. -/
theorem swapName_rn
    -- the renaming of the internal wires
    (f : Fin a → Fin a)
    -- a name: a port of the first cell, a port of the second, or an internal wire
    {n : ℕ}
    (x : Fin n ⊕ Fin n ⊕ Fin a) :
    Rule.swapName (rn f x) = rn f (Rule.swapName x) := by
  rcases x with i | j | w <;> rfl

-- the rule, of a symbol with itself
variable (r : Rule S a a)

/-- An expanded equation: rooted at a port, with only internal wires below the root. -/
def ExpandedEq
    -- an equation between trees over the names of `r`
    (e : Sym2 (Term S (Fin a ⊕ Fin a ⊕ Fin r.internal))) :
    Prop :=
  -- `e` is `p = t`, `p` is not an internal wire, and `t` has only internal wires
  ∃ p t, e = s(var p, t) ∧ (∀ w, p ≠ .inr (.inr w)) ∧ ∀ x ∈ t.vars, ∃ w, x = .inr (.inr w)

/-- An expanded equation, with the cells exchanged and the internal wires renamed by `π`, is
rooted at the first cell exactly when it was not. -/
theorem leftRooted_swap
    -- the permutation of the internal wires
    (π : Equiv.Perm (Fin r.internal))
    -- an expanded equation
    {e}
    (he : ExpandedEq r e) :
    LeftRooted (e.map (Term.bind fun x => var (Rule.swapName (rn π x))))
      ↔ ¬ LeftRooted e := by
  obtain ⟨p, t, rfl, hp, ht⟩ := he
  have hnot : ∀ (u : Term S (Fin a ⊕ Fin a ⊕ Fin r.internal)), (∀ x ∈ u.vars, ∃ w,
      x = .inr (.inr w)) → ∀ i, u ≠ var (.inl i) := by
    intro u hu i hui
    subst hui
    obtain ⟨w, hw⟩ := hu (.inl i) (by simp)
    cases hw
  have ht' : ∀ x ∈ (t.bind fun x => var (Rule.swapName (rn π x))).vars, ∃ w, x = .inr (.inr w) := by
    intro x hx
    rw [Term.vars_bind] at hx
    obtain ⟨y, hy, hxy⟩ := Multiset.mem_bind.1 hx
    obtain ⟨w, rfl⟩ := ht y hy
    simp only [rn_inr_inr, Term.vars_var, Multiset.mem_singleton] at hxy
    exact ⟨π w, hxy⟩
  simp only [Sym2.map_mk, Term.bind_var, LeftRooted, Sym2.mem_iff]
  constructor
  · rintro ⟨i, hi | hi⟩ ⟨i', hi' | hi'⟩
    · rcases p with j | j | w
      · cases hi
      · cases hi'
      · exact hp w rfl
    · exact hnot t ht i' hi'.symm
    · exact hnot _ ht' i hi.symm
    · exact hnot _ ht' i hi.symm
  · intro h
    rcases p with j | j | w
    · exact absurd ⟨j, Or.inl rfl⟩ h
    · exact ⟨j, Or.inl rfl⟩
    · exact absurd rfl (hp w)

section Parts

-- the permutation `π` of the internal wires, and the literal symmetry of the rule: exchanging the
-- cells gives the net renamed by `π`
variable {r} (π : Equiv.Perm (Fin r.internal))
  (hsym : r.swap.net = r.net.bind fun x => var (rn π x))
include hsym

/-- Exchanging the cells and renaming the internal wires by `π` fixes the net. -/
theorem bind_rho :
    r.net.bind (fun x => var (Rule.swapName (rn π x))) = r.net := by
  have hs : (r.net.bind fun x => var (Rule.swapName (n := r.internal) x)) =
      r.net.bind fun x => var (rn π x) := hsym
  have h := congrArg (Net.bind fun x => var (Rule.swapName (n := r.internal) x)) hs
  simp only [Net.bind_bind, Term.bind_var, Rule.swapName_swapName] at h
  rw [Net.bind_var_self] at h
  exact h.symm

/-- `π` is involutive. -/
theorem pi_invol
    -- the rule is linear and reduced
    (hl : r.Linear)
    (hred : r.Reduced) :
    ∀ w, π (π w) = w := by
  refine Rule.eq_id_of_bind_eq r hl hred (fun w => π (π w)) ?_
  have h := bind_rho π hsym
  calc r.net.bind (fun x => var (Sum.map id (Sum.map id (fun w => π (π w))) x))
      = (r.net.bind (fun x => var (Rule.swapName (rn π x)))).bind
          (fun x => var (Rule.swapName (rn π x))) := by
        rw [Net.bind_bind]
        simp only [Term.bind_var]
        refine Net.bind_congr fun x _ => ?_
        rcases x with i | j | w <;> rfl
    _ = r.net := by rw [h, h]

-- the rule is in expanded form
variable (hexp : r.Expanded)
include hexp

/-- The part rooted at the first cell is the other part, with the cells exchanged and the internal
wires renamed by `π`. -/
theorem leftPart_eq :
    r.leftPart
      = r.rightPart.bind fun x => var (Rule.swapName (rn π x)) := by
  change r.net.filter LeftRooted = _
  conv_lhs => rw [← bind_rho π hsym]
  unfold Net.bind
  rw [Multiset.filter_map]
  congr 1
  exact Multiset.filter_congr fun e he => leftRooted_swap r π (hexp e he)

/-- The part rooted at the second cell is the other part, with the cells exchanged and the
internal wires renamed by `π`. -/
theorem rightPart_eq :
    r.rightPart
      = r.leftPart.bind fun x => var (Rule.swapName (rn π x)) := by
  change r.net.filter (fun e => ¬LeftRooted e) = _
  conv_lhs => rw [← bind_rho π hsym]
  unfold Net.bind
  rw [Multiset.filter_map]
  congr 1
  exact Multiset.filter_congr fun e he => by
    simp only [Function.comp, leftRooted_swap r π (hexp e he), not_not]

/-- The first part of the rule read from the other cell is the first part renamed by `π`. -/
theorem leftSw_eq :
    r.leftSw
      = r.leftPart.bind fun x => var (rn π x) := by
  change Net.bind _ r.rightPart = _
  rw [rightPart_eq π hsym hexp, Net.bind_bind]
  simp only [Term.bind_var, Rule.swapName_swapName]

/-- The second part of the rule read from the other cell is the second part renamed by `π`. -/
theorem rightSw_eq :
    r.rightSw
      = r.rightPart.bind fun x => var (rn π x) := by
  change Net.bind _ r.leftPart = _
  rw [leftPart_eq π hsym hexp, Net.bind_bind]
  simp only [Term.bind_var, Rule.swapName_swapName]

end Parts

-- ============================================================================================
-- 4. Plugging a renamed copy of a side
-- ============================================================================================

/-- Renaming a sum of nets renames each of them. -/
theorem bind_add
    -- the renaming
    {ν μ : Type}
    (f : ν → Term S μ)
    -- the two nets
    (N M : Net S ν) :
    Net.bind f (N + M) = N.bind f + M.bind f := Multiset.map_add _ _ _

/-- The numbering `midφ` of the middle wires does not depend on the proof of membership. -/
theorem midφ_congr'
    -- two equal names, both middle wires
    {x y : Fin a ⊕ Fin a ⊕ Fin r.internal}
    (e : x = y)
    (h : x ∈ r.midL)
    (h' : y ∈ r.midL) :
    r.midφ x h = r.midφ y h' := by
  subst e; rfl

/-- Plugging `φ` with a copy `ψ` of `φ` whose middle wires are renumbered by `τ` and internal
wires by `κ`, through `σ₀`, is plugging `φ` with itself through `σ = τ⁻¹ σ₀`, up to a bijection of
the internal wires. So an `Equiv` from the first plug to a net renamed by an injective `ι₀` gives
one from the second (page 86). -/
theorem plug_rename_equiv
    -- a side `φ` with `k` middle wires, and its copy `ψ`: middle wires renumbered by `τ`,
    -- internal wires by `κe`
    {k n : ℕ}
    (φ ψ : Rule S a k)
    -- the permutation `σ₀` of the plug, and `σ = τ⁻¹ σ₀`
    (σ₀ σ : Equiv.Perm (Fin k))
    (τ : Fin k → Fin k)
    (κe : Fin φ.internal ≃ Fin ψ.internal)
    (hψ : ψ.net = φ.net.bind fun y => var (Sum.map id (Sum.map τ κe) y))
    (hσ : ∀ l, σ.symm l = σ₀.symm (τ l))
    -- a net `N`, and an `Equiv` from the plug of `φ` and `ψ` to `N` renamed by an injective `ι₀`
    {N : Net S (Fin a ⊕ Fin a ⊕ Fin n)}
    {ι₀ : Fin n → Fin (Rule.plug φ ψ σ₀).internal}
    (hι₀ : Function.Injective ι₀)
    (heq : Equiv (Rule.plug φ ψ σ₀).net (N.bind fun x => var (Sum.map id (Sum.map id ι₀) x))) :
    -- there is a renaming `ι` of the internal wires of `N` such that
    ∃ ι : Fin n → Fin (Rule.plug φ φ σ).internal,
      -- `ι` is injective,
      Function.Injective ι ∧
      -- and the plug of `φ` with itself through `σ` is `Equiv` to `N` renamed by `ι`
      Equiv (Rule.plug φ φ σ).net (N.bind fun x => var (Sum.map id (Sum.map id ι) x)) := by
  let θe : Fin (k + φ.internal + φ.internal) ≃ Fin (k + φ.internal + ψ.internal) :=
    finSumFinEquiv.symm.trans
      ((_root_.Equiv.sumCongr (_root_.Equiv.refl _) κe).trans finSumFinEquiv)
  have hθl : ∀ u, θe (Fin.castAdd _ u) = Fin.castAdd _ u := fun u => by simp [θe]
  have hθr : ∀ v, θe (Fin.natAdd _ v) = Fin.natAdd _ (κe v) := fun v => by simp [θe]
  let θ' : Fin (Rule.plug φ φ σ).internal → Fin (Rule.plug φ ψ σ₀).internal := θe
  let θi : Fin (Rule.plug φ ψ σ₀).internal → Fin (Rule.plug φ φ σ).internal := θe.symm
  have hP0 : (show Net S (Fin a ⊕ Fin a ⊕ Fin (k + φ.internal + ψ.internal)) from
        (Rule.plug φ ψ σ₀).net) =
      (show Net S (Fin a ⊕ Fin a ⊕ Fin (k + φ.internal + φ.internal)) from
        (Rule.plug φ φ σ).net).bind fun x => var (Sum.map id (Sum.map id θe) x) := by
    change φ.net.bind (fun x => var (plugL (b := a) (n := ψ.internal) x)) +
        ψ.net.bind (fun x => var (plugR (a := a) (m := φ.internal) σ₀ x)) =
      Net.bind _ (φ.net.bind (fun x => var (plugL (b := a) (n := φ.internal) x)) +
        φ.net.bind (fun x => var (plugR (a := a) (m := φ.internal) σ x)))
    rw [hψ, bind_add, Net.bind_bind, Net.bind_bind, Net.bind_bind]
    simp only [Term.bind_var]
    congr 1
    · refine Net.bind_congr fun x _ => ?_
      rcases x with i | l | j
      · rfl
      · simp only [plugL, Sum.map_inr, hθl]
      · simp only [plugL, Sum.map_inr, hθl]
    · refine Net.bind_congr fun x _ => ?_
      rcases x with i | l | j
      · rfl
      · simp only [plugR, Sum.map_inr, Sum.map_inl, hθl, hσ]
      · simp only [plugR, Sum.map_inr, hθr]
  have hP : (Rule.plug φ ψ σ₀).net =
      (Rule.plug φ φ σ).net.bind fun x => var (Sum.map id (Sum.map id θ') x) := hP0
  rw [hP] at heq
  have hinj : Function.Injective (Sum.map id (Sum.map id θi) :
      Fin a ⊕ Fin a ⊕ Fin (Rule.plug φ ψ σ₀).internal
        → Fin a ⊕ Fin a ⊕ Fin (Rule.plug φ φ σ).internal) :=
    Sum.map_injective.2 ⟨Function.injective_id,
      Sum.map_injective.2 ⟨Function.injective_id, θe.symm.injective⟩⟩
  have h2 := Equiv.bind_var _ hinj heq
  simp only [Net.bind_bind, Term.bind_var] at h2
  refine ⟨fun w => θi (ι₀ w), θe.symm.injective.comp hι₀, ?_⟩
  convert h2 using 1
  · conv_lhs => rw [← Net.bind_var_self (Rule.plug φ φ σ).net]
    refine Net.bind_congr fun x _ => ?_
    rcases x with i | j | t
    · rfl
    · rfl
    · exact congrArg (fun t => var (Sum.inr (Sum.inr t))) (θe.symm_apply_apply t).symm
  · refine Net.bind_congr fun x _ => ?_
    rcases x with i | j | t <;> rfl

-- ============================================================================================
-- 5. Main result: the symmetric decomposition
-- ============================================================================================

/-- **The symmetric decomposition of a literally symmetric expanded rule** (Lafont 1997,
page 86: "one can assume that in all cases `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, and
`σ_{i,j}` is involutive"; Fig. 7). Let `r` be a linear reduced rule of a symbol with itself, in
expanded form (every equation is `p = t` with `p` a port and only internal wires in `t`), such
that exchanging the two cells gives the same net up to a permutation `π` of the internal wires.
Then there is a decomposition with `ψ = φ` and an involutive `σ`, whose sides are linear and
reduced, and whose plug is `r` up to `Equiv` and an injective renaming of the internal wires. -/
theorem exists_symm_decomposition
    -- the rule `r` is linear and in expanded form (hence reduced)
    (hl : r.Linear)
    (hexp : r.Expanded)
    -- the literal symmetry: exchanging the cells gives the net renamed by a permutation `π` of
    -- the internal wires
    (π : Equiv.Perm (Fin r.internal))
    (hsym : r.swap.net = r.net.bind fun x => var (Sum.map id (Sum.map id π) x)) :
    -- there is a decomposition `D` such that
    ∃ D : Decomposition S a a,
      -- its two sides are equal,
      D.ψ = D.φ ∧
      -- its permutation is involutive,
      (∀ l, D.σ (D.σ l) = l) ∧
      -- its side is linear and reduced,
      D.φ.Linear ∧ D.φ.Reduced ∧
      -- and there is an injective renaming `ι` of the internal wires of `r` such that
      ∃ ι : Fin r.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal,
        Function.Injective ι ∧
        -- the plug of `D` is `Equiv` to `r` renamed by `ι`
        Equiv (Rule.plug D.φ D.ψ D.σ).net
          (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x)) := by
  classical
  have hred : r.Reduced := hexp.reduced
  have hsym' : r.swap.net = r.net.bind fun x => var (rn π x) := hsym
  have hinv := pi_invol π hsym' hl hred
  have hX := leftSw_eq π hsym' hexp
  have hY := rightSw_eq π hsym' hexp
  have hmidd : ∀ x, rn π x ∈ r.midR ↔ x ∈ r.midL := fun x => by
    change rn π x ∈ middle r.leftSw r.rightSw ↔ x ∈ middle r.leftPart r.rightPart
    rw [hX, hY]
    exact mem_middle_rn π _ _ x
  let τ : Fin r.kDec → Fin r.kDec := fun l =>
    r.midψ (rn π (r.unrankL l)) ((hmidd _).2 (r.unrankL_spec l).1)
  have hτ : ∀ x (h : x ∈ r.midL) (h' : rn π x ∈ r.midR), r.midψ (rn π x) h' = τ (r.midφ x h) :=
    fun x h h' => r.midψ_congr (by rw [r.unrankL_midφ x h]) h' _
  obtain ⟨κ, hκ, hψ⟩ := half_rename π r.leftPart r.rightPart r.leftSw r.rightSw hX hY r.kDec
    r.midφ r.midψ τ hτ
  have hτinj : Function.Injective τ := by
    intro l l' e
    have h2 := rn_injective π.injective (r.midψ_inj _ _ _ _ e)
    obtain ⟨_, e1⟩ := r.unrankL_spec l
    obtain ⟨_, e2⟩ := r.unrankL_spec l'
    rw [← e1, ← e2]
    exact midφ_congr' r h2 _ _
  let τe : Equiv.Perm (Fin r.kDec) := Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hτinj)
  let σ : Equiv.Perm (Fin r.kDec) := r.σDec.trans τe.symm
  have hrr : ∀ x : Fin a ⊕ Fin a ⊕ Fin r.internal, rn π (rn π x) = x := by
    intro x
    rcases x with i | j | w
    · rfl
    · rfl
    · exact congrArg (fun w => Sum.inr (Sum.inr w)) (hinv w)
  refine ⟨⟨r.kDec, r.decompose.φ, r.decompose.φ, σ⟩, rfl, ?_, (r.decompose_linear hl).1,
    (r.decompose_reduced hred).1, ?_⟩
  · have key : ∀ x (h : x ∈ r.midL), ∃ h' : rn π (Rule.swapName x) ∈ r.midL,
        σ (r.midφ x h) = r.midφ _ h' := by
      intro x h
      have hs : Rule.swapName x ∈ r.midR := (r.swapName_mem_midR x).2 h
      have hs' : rn π (rn π (Rule.swapName x)) ∈ r.midR := by rwa [hrr]
      have h' : rn π (Rule.swapName x) ∈ r.midL := (hmidd _).1 hs'
      refine ⟨h', ?_⟩
      change τe.symm (r.σDec (r.midφ x h)) = _
      rw [Equiv.symm_apply_eq, r.σDec_midφ x h]
      change _ = τ _
      rw [← hτ _ h' hs']
      exact r.midψ_congr (hrr _).symm _ _
    intro l
    obtain ⟨x, h, rfl⟩ := r.midφ_surj l
    obtain ⟨h1, e1⟩ := key x h
    obtain ⟨h2, e2⟩ := key _ h1
    change σ (σ _) = _
    rw [e1, e2]
    refine midφ_congr' r ?_ _ _
    rw [← swapName_rn, hrr, Rule.swapName_swapName]
  · obtain ⟨ι0, hι0, heq⟩ := r.plug_decompose hl
    exact plug_rename_equiv r.decompose.φ r.decompose.ψ r.decompose.σ σ τ (Equiv.ofBijective κ hκ)
      hψ (fun _ => rfl) hι0 heq

end Rule.SymmLit

end INet
