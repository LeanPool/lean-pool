/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFree
public import LeanPool.InteractionCombinators.Universality.RecursionFree.SymmPerm

/-!
# Normalising a decomposition (page 86)

Lafont 1997, Section 2.4, journal page 86 (PDF page 18): "To sum up, one can assume that in all
cases, `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, and `σ_{i,j}` is involutive", and "If `i ≠ j`, it
is always possible to include the permutation into `φ_{i,j}` … so that the decomposition is no
longer canonical, but `σ_{i,j}` is an identity."

* `Decomposition.absorb` — for `α ≠ β`, the permutation is moved into `φ` by renumbering its
  middle wires; cells, linearity, reducedness and `Plugs` are kept, and `σ` becomes `1`.
* `System.WellFormed.symmDec` — the symmetric decomposition of a rule `α`–`α` of a well-formed
  system (`Rule.exists_symm_decomposition_of_symmPerm`).

These were first written in the review file `RecursionFreeCheck.lean` (#79) and are moved here so
that library files can use them.

Contents, in the order of the file:

1. Definitions: moving `σ` into `φ`: `absorbName`, the renaming of the names of `φ`;
   `absorb`, the decomposition with `σ = 1`; `absorbWire`, the renaming of the internal wires of
   the plugged net.
2. Auxiliary lemmas: `absorbName_injective`, `absorbWire_mid`, `absorbWire_left`,
   `absorbWire_right`, and `absorb_plug_net`, the plug of `absorb` is the plug of `D` renamed.
3. Main results on `absorb` (page 86, `i ≠ j`): `absorb_cells`, `absorb_linear`,
   `absorb_reduced`, `absorb_plugs`.
4. The symmetric decomposition of a rule `α`–`α` (page 86): `System.WellFormed.symmDec` and
   `System.WellFormed.symmDec_spec`.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

namespace Decomposition

-- the numbers of auxiliary ports of the two cells of the rule
variable {a b : ℕ}

-- ============================================================================================
-- 1. Definitions: moving `σ` into `φ` (page 86, `i ≠ j`)
-- ============================================================================================

/-- The renaming of the names of `φ` that sends the middle wire `l` to `σ l`. -/
def absorbName
    -- the decomposition
    (D : Decomposition S a b) :
    Fin a ⊕ Fin D.k ⊕ Fin D.φ.internal → Fin a ⊕ Fin D.k ⊕ Fin D.φ.internal :=
  Sum.map id (Sum.map D.σ id)

/-- Page 86: "If `i ≠ j`, it is always possible to include the permutation into `φ_{i,j}` … so
that the decomposition is no longer canonical, but `σ_{i,j}` is an identity." The middle wire `l`
of `φ` is renamed `σ l`, and `σ` becomes `1`. -/
def absorb
    -- the decomposition
    (D : Decomposition S a b) :
    Decomposition S a b where
  k := D.k
  φ := ⟨D.φ.internal, D.φ.net.bind fun x => var (D.absorbName x)⟩
  ψ := D.ψ
  σ := 1

/-- The bijection of the internal wires of the plugged net that sends the joined wire `l` to
`σ l` and fixes the others. -/
def absorbWire
    -- the decomposition
    (D : Decomposition S a b) :
    Fin (D.k + D.φ.internal + D.ψ.internal) ≃ Fin (D.k + D.φ.internal + D.ψ.internal) :=
  finSumFinEquiv.symm.trans ((_root_.Equiv.sumCongr
    (finSumFinEquiv.symm.trans ((_root_.Equiv.sumCongr D.σ (_root_.Equiv.refl _)).trans
      finSumFinEquiv)) (_root_.Equiv.refl _)).trans finSumFinEquiv)

-- ============================================================================================
-- 2. Auxiliary lemmas: the two renamings
-- ============================================================================================

/-- The renaming `absorbName` of the names of `φ` is injective. -/
theorem absorbName_injective
    -- the decomposition
    (D : Decomposition S a b) :
    Function.Injective D.absorbName :=
  Sum.map_injective.2 ⟨Function.injective_id,
    Sum.map_injective.2 ⟨D.σ.injective, Function.injective_id⟩⟩

/-- `absorbWire` sends the joined wire `l` to `σ l`. -/
theorem absorbWire_mid
    -- the decomposition and a joined wire
    (D : Decomposition S a b)
    (l : Fin D.k) :
    D.absorbWire (Fin.castAdd _ (Fin.castAdd _ l)) = Fin.castAdd _ (Fin.castAdd _ (D.σ l)) := by
  simp [absorbWire]

/-- `absorbWire` fixes the internal wires of `φ`. -/
theorem absorbWire_left
    -- the decomposition and an internal wire of `φ`
    (D : Decomposition S a b)
    (j : Fin D.φ.internal) :
    D.absorbWire (Fin.castAdd _ (Fin.natAdd _ j)) = Fin.castAdd _ (Fin.natAdd _ j) := by
  simp [absorbWire]

/-- `absorbWire` fixes the internal wires of `ψ`. -/
theorem absorbWire_right
    -- the decomposition and an internal wire of `ψ`
    (D : Decomposition S a b)
    (j : Fin D.ψ.internal) :
    D.absorbWire (Fin.natAdd _ j) = Fin.natAdd _ j := by
  simp [absorbWire]

/-- The plug of `D.absorb` is the plug of `D` with its internal wires renamed by
`absorbWire`. -/
theorem absorb_plug_net
    -- the decomposition
    (D : Decomposition S a b) :
    -- the plugged net of `D.absorb`
    (show Net S (Fin a ⊕ Fin b ⊕ Fin (D.k + D.φ.internal + D.ψ.internal)) from
      (Rule.plug D.absorb.φ D.absorb.ψ D.absorb.σ).net)
    -- is the plugged net of `D`, renamed by `absorbWire`
    = (show Net S (Fin a ⊕ Fin b ⊕ Fin (D.k + D.φ.internal + D.ψ.internal)) from
        (Rule.plug D.φ D.ψ D.σ).net).bind
          fun x => var (Sum.map id (Sum.map id D.absorbWire) x) := by
  change (D.φ.net.bind fun x => var (D.absorbName x)).bind
        (fun x => var (Rule.plugL (b := b) (n := D.ψ.internal) x)) +
      D.ψ.net.bind (fun x => var (Rule.plugR (a := a) (m := D.φ.internal) 1 x)) =
    Net.bind _ (D.φ.net.bind (fun x => var (Rule.plugL (b := b) (n := D.ψ.internal) x)) +
      D.ψ.net.bind (fun x => var (Rule.plugR (a := a) (m := D.φ.internal) D.σ x)))
  have hadd : ∀ {ν μ : Type} (f : ν → Term S μ) (N M : Net S ν),
      Net.bind f (N + M) = N.bind f + M.bind f := fun _ _ _ => Multiset.map_add _ _ _
  rw [hadd, Net.bind_bind, Net.bind_bind, Net.bind_bind]
  simp only [Term.bind_var]
  congr 1
  · refine Net.bind_congr fun x _ => ?_
    rcases x with i | l | j
    · rfl
    · simp only [absorbName, Rule.plugL, Sum.map_inr, Sum.map_inl, absorbWire_mid]
    · simp only [absorbName, Rule.plugL, Sum.map_inr, id, absorbWire_left]
  · refine Net.bind_congr fun x _ => ?_
    rcases x with i | l | j
    · rfl
    · simp only [Rule.plugR, Sum.map_inr, absorbWire_mid, _root_.Equiv.apply_symm_apply]
      rfl
    · simp only [Rule.plugR, Sum.map_inr, absorbWire_right]

-- ============================================================================================
-- 3. Main results: what moving `σ` into `φ` keeps (page 86, `i ≠ j`)
-- ============================================================================================

/-- Moving `σ` into `φ` adds no cell to `φ`. -/
theorem absorb_cells
    -- the decomposition
    (D : Decomposition S a b) :
    D.absorb.φ.net.cells = D.φ.net.cells :=
  Net.cells_bind_var _ _

/-- Moving `σ` into `φ` keeps `φ` linear. -/
theorem absorb_linear
    -- a decomposition whose side `φ` is linear
    (D : Decomposition S a b)
    (h : D.φ.Linear) :
    D.absorb.φ.Linear := by
  have key : ∀ x, (Net.vars D.absorb.φ.net).count (D.absorbName x) =
      (Net.vars D.φ.net).count x := by
    intro x
    change (Net.vars (D.φ.net.bind fun x => var (D.absorbName x))).count _ = _
    rw [Net.vars_bind_var, Multiset.count_map_eq_count' _ _ D.absorbName_injective]
  refine ⟨fun i => (key (.inl i)).trans (h.left i), fun (l : Fin D.k) => ?_,
    fun w => (key (.inr (.inr w))).trans (h.internal w)⟩
  have := key (.inr (.inl (D.σ.symm l)))
  simp only [absorbName, Sum.map_inr, Sum.map_inl, _root_.Equiv.apply_symm_apply] at this
  exact this.trans (h.right _)

/-- Moving `σ` into `φ` keeps `φ` reduced. -/
theorem absorb_reduced
    -- a decomposition whose side `φ` is reduced
    (D : Decomposition S a b)
    (h : D.φ.Reduced) :
    D.absorb.φ.Reduced := by
  intro e he
  obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 he
  obtain ⟨p, t, rfl, hp⟩ := h e₀ he₀
  refine ⟨D.absorbName p, t.bind fun x => var (D.absorbName x), rfl, fun w hw => ?_⟩
  rcases p with i | l | j
  · cases hw
  · cases hw
  · exact hp j (by simp_all)

/-- Moving `σ` into `φ` keeps the plug: if `D` plugs `r`, so does `D.absorb`. -/
theorem absorb_plugs
    -- the decomposition
    (D : Decomposition S a b)
    -- a rule that `D` plugs
    {r : Rule S a b}
    (h : D.Plugs r) :
    D.absorb.Plugs r := by
  obtain ⟨ι₀, hι₀, heq⟩ := h
  have hinj : Function.Injective (Sum.map id (Sum.map id D.absorbWire) :
      Fin a ⊕ Fin b ⊕ Fin (D.k + D.φ.internal + D.ψ.internal) → _) :=
    Sum.map_injective.2 ⟨Function.injective_id,
      Sum.map_injective.2 ⟨Function.injective_id, D.absorbWire.injective⟩⟩
  have hP : (Rule.plug D.absorb.φ D.absorb.ψ D.absorb.σ).net =
      (Rule.plug D.φ D.ψ D.σ).net.bind fun x => var (Sum.map id (Sum.map id D.absorbWire) x) :=
    D.absorb_plug_net
  have h2 := Equiv.bind_var _ hinj heq
  let ι₀' : Fin r.internal → Fin (D.k + D.φ.internal + D.ψ.internal) := ι₀
  let ι₁ : Fin r.internal → Fin (D.k + D.φ.internal + D.ψ.internal) :=
    fun w => D.absorbWire (ι₀ w)
  have e : (r.net.bind fun x => var (Sum.map id (Sum.map id ι₁) x)) =
      (r.net.bind fun x => var (Sum.map id (Sum.map id ι₀') x)).bind
        fun y => var (Sum.map id (Sum.map id D.absorbWire) y) := by
    rw [Net.bind_bind]
    refine Net.bind_congr fun x _ => ?_
    rcases x with i | j | t <;> rfl
  exact ⟨ι₁, D.absorbWire.injective.comp hι₀, (congrArg₂ Equiv hP e).mpr h2⟩

end Decomposition

-- ============================================================================================
-- 4. The symmetric decomposition of a rule `α`–`α` (page 86)
-- ============================================================================================

/-- The symmetric decomposition of a rule `α`–`α` of a well-formed system, chosen by
`Rule.exists_symm_decomposition_of_symmPerm` (page 86: `φ_{i,i} = ψ_{i,i}`, `σ_{i,i}`
involutive). -/
noncomputable def System.WellFormed.symmDec
    -- a well-formed interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- a symbol and the rule of the system between two cells of that symbol
    (α : S.Sym)
    (r : Rule S (S.arity α) (S.arity α))
    (h : I.rule α α = some r) :
    Decomposition S (S.arity α) (S.arity α) :=
  Classical.choose
    (r.exists_symm_decomposition_of_symmPerm (hI.linear α α r h) (hI.reduced α α r h)
      (hI.symm α r h))

/-- The symmetric decomposition of a rule `α`–`α` (page 86) has `ψ = φ`, an involutive `σ`, a
linear and reduced side, and plugs back the rule. -/
theorem System.WellFormed.symmDec_spec
    -- a well-formed interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- a symbol and the rule of the system between two cells of that symbol
    (α : S.Sym)
    (r : Rule S (S.arity α) (S.arity α))
    (h : I.rule α α = some r) :
    -- the two sides are the same net,
    (hI.symmDec α r h).ψ = (hI.symmDec α r h).φ ∧
      -- the permutation of the middle wires is an involution,
      Function.Involutive (hI.symmDec α r h).σ ∧
      -- the side is linear,
      (hI.symmDec α r h).φ.Linear ∧
      -- the side is reduced,
      (hI.symmDec α r h).φ.Reduced ∧
      -- and the decomposition plugs back the rule
      (hI.symmDec α r h).Plugs r :=
  Classical.choose_spec
    (r.exists_symm_decomposition_of_symmPerm (hI.linear α α r h) (hI.reduced α α r h)
      (hI.symm α r h))

end INet
