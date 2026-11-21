/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.SimulationInvertible
public import LeanPool.InteractionCombinators.Universality.General.CodeCompatible
public import Mathlib.Basic.Finite.Sum

/-!
# Uniform bounds `L`, `M` for a compatible translation (page 81)

Lafont 1997, page 81: if `Φ` is a translation, then for each rule `Φ(α)` and `Φ(β)`, plugged by
their roots, reduce to a translation of the right member; "let `L` (resp. `M`) be the minimal
(resp. the maximal) length of all those reductions." The paper takes one reduction per rule. In
Lean, `Translation.Compatible` gives a reduction for every naming of the ports and of the internal
wires of the two instances, and `Translation.CompatibleWithin I I' L M` asks for a length in
`[L, M]` for every naming. This file shows that the two agree.

Contents, in the order of the file:

1. Auxiliary lemmas on namings: `SimulationUniform.exists_injective_extend` (two injective
   namings of a finite set extend to an injective renaming of `ℕ` sending one to the other),
   `count_le_count_map`, `vars_inst`, `inst_bind_var`, and `SimulationUniform.naming_injective`
   (when the pair `Φ(α)(xs) = Φ(β)(ys)` is linear and the names `xs`, `ys` of the ports are
   pairwise distinct, all the names of the pair, ports and internal wires of both instances, are
   pairwise distinct).
2. One length per rule: `Translation.Compatible.exists_length` (for every rule `α`–`β` there is a
   `k` such that every naming with distinct names is simulated in exactly `k` interactions; the
   reduction found for one naming is renamed into any other by `StepsEN.bind_var`,
   `Equiv.bind_var`, `NetTr.bind_var`), and the definitions `Compatible.len`, the chosen length
   of each rule, and `ruleLens`, the set of the lengths of the rules.
3. Main results, uniform bounds: `Translation.Compatible.compatibleWithin_len` (`L` and `M` are
   the minimum and the maximum of the lengths of the rules),
   `Translation.Compatible.exists_compatibleWithin` (on a finite signature, a compatible
   translation has `L`, `M` with `CompatibleWithin I I' L M`),
   `Translation.Compatible.exists_compatibleWithin_pos` (`0 < L` when the translation is
   strict), and `Comb.codeTranslation_compatibleWithin` (Theorem 1 with step counts: the
   translation of Fig. 10 has bounds `0 < L ≤ M`).
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

namespace SimulationUniform

-- ============================================================================================
-- 1. Auxiliary lemmas: namings
-- ============================================================================================

/-- **Two injective namings of a finite set are related by an injective renaming** (used for
Lafont 1997, page 81: the reduction of a rule does not depend on the names). If `ν₀` and `ν₁`
name the elements of a finite type injectively, some injective `ρ : ℕ → ℕ` sends `ν₀ i` to
`ν₁ i` for every `i`. Outside the names `ν₀ i`, `ρ` adds a bound of the names `ν₁ i`. -/
theorem exists_injective_extend
    -- a finite set of elements and two injective namings of them
    {ι : Type} [Finite ι]
    {ν₀ ν₁ : ι → ℕ}
    (h₀ : Function.Injective ν₀)
    (h₁ : Function.Injective ν₁) :
    -- there is a renaming `ρ`
    ∃ ρ : ℕ → ℕ,
      -- which is injective
      Function.Injective ρ ∧
      -- and sends the first naming to the second
      ∀ i, ρ (ν₀ i) = ν₁ i := by
  classical
  have := Fintype.ofFinite ι
  let B : ℕ := ∑ i, ν₁ i + 1
  have hB : ∀ i, ν₁ i < B := fun i => Nat.lt_succ_of_le
    (Finset.single_le_sum (f := ν₁) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  let ρ : ℕ → ℕ := fun n => if h : ∃ i, ν₀ i = n then ν₁ h.choose else B + n
  refine ⟨ρ, fun m n hmn => ?_, fun i => ?_⟩
  · simp only [ρ] at hmn
    split_ifs at hmn with hm hn hn
    · rw [← hm.choose_spec, ← hn.choose_spec, h₁ hmn]
    · have := hB hm.choose
      omega
    · have := hB hn.choose
      omega
    · omega
  · simp only [ρ]
    split_ifs with h
    · exact congrArg ν₁ (h₀ h.choose_spec)
    · exact absurd ⟨i, rfl⟩ h

/-- One element counts in the image of a multiset. -/
theorem count_le_count_map
    -- a map between types with decidable equality
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : α → β)
    -- a multiset and an element
    (s : Multiset α)
    (i : α) :
    -- the count of `i` is at most the count of its image in the image of `s`
    s.count i ≤ (s.map g).count (g i) := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  apply Multiset.card_le_card
  exact Multiset.monotone_filter_right _ fun z hz => congrArg g hz

/-- The names of an instance of a principal net with names on its ports. -/
theorem vars_inst
    -- the principal net
    {n : ℕ}
    (p : PNet S' n)
    -- the names of its ports and of its internal wires
    (xs : Fin n → ℕ)
    (f : Fin p.internal → ℕ) :
    -- the names of the instance are those of the tree of `p`, renamed
    (p.inst (fun i => .var (xs i)) f).vars = p.tree.vars.map (Sum.elim xs f) := by
  have e : p.inst (fun i => .var (xs i)) f = p.tree.bind fun x => var (Sum.elim xs f x) := by
    rw [PNet.inst]
    congr 1
    funext x
    cases x <;> rfl
  rw [e, Term.vars_bind]
  exact Multiset.bind_singleton _ _

/-- An instance of a principal net, renamed: the names of the ports and of the internal wires are
renamed. -/
theorem inst_bind_var
    -- the principal net
    {n : ℕ}
    (p : PNet S' n)
    -- the names of its ports and of its internal wires
    (xs : Fin n → ℕ)
    (f : Fin p.internal → ℕ)
    -- the renaming
    (ρ : ℕ → ℕ) :
    -- renaming the instance is taking the instance with renamed names
    (p.inst (fun i => .var (xs i)) f).bind (fun x => var (ρ x)) =
      p.inst (fun i => .var (ρ (xs i))) fun w => ρ (f w) := by
  rw [PNet.inst, PNet.inst, Term.bind_bind]
  congr 1
  funext q
  cases q <;> rfl

/-- **All the names of a linear pair are distinct** (Lafont 1997, page 80: the two cells of a rule
have distinct ports; a linear net has each internal wire twice). Let `Φ(α)(xs) = Φ(β)(ys)`, with
internal wires named by `f` and `g`, be linear, with the names `xs` pairwise distinct, the names
`ys` too, and no `xs i` equal to a `ys j`. Then the names of the ports and of the internal wires
of both instances are pairwise distinct. -/
theorem naming_injective
    -- the two principal nets
    {a b : ℕ}
    (p : PNet S' a)
    (q : PNet S' b)
    -- the names of their ports and of their internal wires
    (xs : Fin a → ℕ)
    (ys : Fin b → ℕ)
    (f : Fin p.internal → ℕ)
    (g : Fin q.internal → ℕ)
    -- the names of the ports are pairwise distinct
    (hx : Function.Injective xs)
    (hy : Function.Injective ys)
    (hxy : ∀ i j, xs i ≠ ys j)
    -- the pair of the two instances is linear
    (hl : Net.Linear ({s(p.inst (fun i => .var (xs i)) f, q.inst (fun j => .var (ys j)) g)} :
      Net S' ℕ)) :
    -- all the names, of the ports and of the internal wires, are pairwise distinct
    Function.Injective
      (Sum.elim xs (Sum.elim ys (Sum.elim f g)) : Fin a ⊕ Fin b ⊕ Fin p.internal ⊕ Fin q.internal
        → ℕ) := by
  classical
  let ν : Fin a ⊕ Fin b ⊕ Fin p.internal ⊕ Fin q.internal → ℕ :=
    Sum.elim xs (Sum.elim ys (Sum.elim f g))
  let e₁ : Fin a ⊕ Fin p.internal → Fin a ⊕ Fin b ⊕ Fin p.internal ⊕ Fin q.internal :=
    Sum.elim Sum.inl fun w => .inr (.inr (.inl w))
  let e₂ : Fin b ⊕ Fin q.internal → Fin a ⊕ Fin b ⊕ Fin p.internal ⊕ Fin q.internal :=
    Sum.elim (fun j => .inr (.inl j)) fun w => .inr (.inr (.inr w))
  let M := p.tree.vars.map e₁ + q.tree.vars.map e₂
  have hv : Net.vars ({s(p.inst (fun i => .var (xs i)) f, q.inst (fun j => .var (ys j)) g)} :
      Net S' ℕ) = M.map ν := by
    rw [Net.vars_singleton, eqVars_mk, vars_inst, vars_inst, Multiset.map_add,
      Multiset.map_map, Multiset.map_map]
    congr 1
    · congr 1
      funext x
      cases x <;> rfl
    · congr 1
      funext x
      cases x <;> rfl
  have l₁ : ∀ x, M.count (e₁ x) ≥ p.tree.vars.count x := fun x => by
    simp only [M, Multiset.count_add]
    have := count_le_count_map e₁ p.tree.vars x
    omega
  have l₂ : ∀ x, M.count (e₂ x) ≥ q.tree.vars.count x := fun x => by
    simp only [M, Multiset.count_add]
    have := count_le_count_map e₂ q.tree.vars x
    omega
  have key : ∀ x y, x ≠ y → ν x = ν y → M.count x + M.count y ≤ 2 := fun x y hne h =>
    (Multiset.count_add_count_le_count_map ν M hne h).trans (by rw [← hv]; exact hl _)
  have c₁ : ∀ i, 1 ≤ M.count (.inl i) := fun i => (p.port_count i).symm.le.trans (l₁ (.inl i))
  have c₂ : ∀ j, 1 ≤ M.count (.inr (.inl j)) := fun j =>
    (q.port_count j).symm.le.trans (l₂ (.inl j))
  have c₃ : ∀ w, 2 ≤ M.count (.inr (.inr (.inl w))) := fun w =>
    (p.internal_count w).symm.le.trans (l₁ (.inr w))
  have c₄ : ∀ w, 2 ≤ M.count (.inr (.inr (.inr w))) := fun w =>
    (q.internal_count w).symm.le.trans (l₂ (.inr w))
  let c : Fin a ⊕ Fin b ⊕ Fin p.internal ⊕ Fin q.internal → ℕ :=
    Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2) fun _ => 2))
  have lb : ∀ x, c x ≤ M.count x := by
    intro x
    rcases x with i | i | i | i
    exacts [c₁ i, c₂ i, c₃ i, c₄ i]
  intro x y h
  by_contra hne
  have k := key x y hne h
  have bx := lb x
  have bY := lb y
  rcases x with i | i | i | i <;> rcases y with j | j | j | j <;>
    simp only [c, Sum.elim_inl, Sum.elim_inr] at bx bY
  all_goals first
    | exact hne (congrArg _ (hx h))
    | exact hne (congrArg _ (congrArg _ (hy h)))
    | exact hxy _ _ h
    | exact hxy _ _ h.symm
    | omega

end SimulationUniform

open SimulationUniform

namespace Translation

variable {Φ : Translation S S'}

-- ============================================================================================
-- 2. One length per rule
-- ============================================================================================

/-- **One length per rule** (Lafont 1997, page 81: "let `L` (resp. `M`) be the minimal (resp.
the maximal) length of all those reductions", one reduction for each rule). Let `Φ` be
compatible. For every pair of symbols `α`, `β` there is a number `k` such that, for the rule `r`
of `α`–`β` and for every naming of the pair `Φ(α)(xs) = Φ(β)(ys)` that is linear, with pairwise
distinct names `xs`, `ys` on the ports, the pair reduces up to wires in exactly `k` interactions
to a net that is the same graph as a translation of an instance of `r`. The reduction given by
`Compatible` for one such naming is renamed into every other one by an injective `ρ`
(`exists_injective_extend`, `naming_injective`). -/
theorem Compatible.exists_length
    -- the two systems, and `Φ` compatible with them
    {I : System S} {I' : System S'}
    (h : Φ.Compatible I I')
    -- the two symbols
    (α β : S.Sym) :
    -- there is a length `k` such that
    ∃ k : ℕ,
      -- for the rule `r` of `α`–`β`,
      ∀ (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
      -- and for all names of the ports and of the internal wires of the two instances,
      ∀ (xs : Fin (S.arity α) → ℕ) (ys : Fin (S.arity β) → ℕ)
        (f : Fin (Φ.net α).internal → ℕ) (g : Fin (Φ.net β).internal → ℕ),
        -- with the names of the ports pairwise distinct,
        Function.Injective xs → Function.Injective ys → (∀ i j, xs i ≠ ys j) →
        -- and the pair `Φ(α)(xs) = Φ(β)(ys)` linear,
        Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
          (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) →
        -- there are nets `M`, `N'` and names `h` of the internal wires of `r` such that
        ∃ (M N' : Net S' ℕ) (h : Fin r.internal → ℕ),
          -- the pair reduces, up to wires, to `M` in exactly `k` interactions,
          StepsEN I' k {s((Φ.net α).inst (fun i => .var (xs i)) f,
            (Φ.net β).inst (fun j => .var (ys j)) g)} M ∧
          -- `M` is the same graph as `N'`,
          Equiv M N' ∧
          -- and `N'` is a translation of the instance of the right member of `r`
          Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N' := by
  classical
  by_cases hex : ∃ r, I.rule α β = some r ∧ ∃ (xs : Fin (S.arity α) → ℕ)
      (ys : Fin (S.arity β) → ℕ) (f : Fin (Φ.net α).internal → ℕ)
      (g : Fin (Φ.net β).internal → ℕ),
      Function.Injective xs ∧ Function.Injective ys ∧ (∀ i j, xs i ≠ ys j) ∧
      Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ)
  · obtain ⟨r₀, hr₀, xs₀, ys₀, f₀, g₀, hx₀, hy₀, hxy₀, hl₀⟩ := hex
    obtain ⟨M₀, N₀, h₀, hS, hE, hT⟩ := h α β r₀ hr₀ xs₀ ys₀ f₀ g₀ hl₀
    obtain ⟨k, hk⟩ := hS.exists_stepsEN
    refine ⟨k, fun r hr xs ys f g hx hy hxy hl => ?_⟩
    obtain rfl : r = r₀ := Option.some_injective _ (hr.symm.trans hr₀)
    obtain ⟨ρ, hρ, hρν⟩ := exists_injective_extend
      (naming_injective _ _ xs₀ ys₀ f₀ g₀ hx₀ hy₀ hxy₀ hl₀)
      (naming_injective _ _ xs ys f g hx hy hxy hl)
    obtain rfl : xs = fun i => ρ (xs₀ i) := funext fun i => (hρν (.inl i)).symm
    obtain rfl : ys = fun j => ρ (ys₀ j) := funext fun j => (hρν (.inr (.inl j))).symm
    obtain rfl : f = fun w => ρ (f₀ w) := funext fun w => (hρν (.inr (.inr (.inl w)))).symm
    obtain rfl : g = fun w => ρ (g₀ w) := funext fun w => (hρν (.inr (.inr (.inr w)))).symm
    refine ⟨M₀.bind fun x => var (ρ x), N₀.bind fun x => var (ρ x), fun w => ρ (h₀ w), ?_,
      hE.bind_var ρ hρ, ?_⟩
    · have := hk.bind_var ρ hρ
      rwa [Net.bind, Multiset.map_singleton, Sym2.map_mk, inst_bind_var,
        inst_bind_var] at this
    · have := hT.bind_var ρ hρ
      rwa [Rule.inst_bind_var] at this
  · exact ⟨0, fun r hr xs ys f g hx hy hxy hl =>
      absurd ⟨r, hr, xs, ys, f, g, hx, hy, hxy, hl⟩ hex⟩

/-- **The length of each rule**: a choice of the number given by `Compatible.exists_length` for
every pair of symbols (Lafont 1997, page 81). For a pair without rule its value is arbitrary. -/
noncomputable def Compatible.len
    -- the two systems, and `Φ` compatible with them
    {I : System S} {I' : System S'}
    (h : Φ.Compatible I I')
    -- the pair of symbols
    (p : S.Sym × S.Sym) :
    ℕ :=
  (h.exists_length p.1 p.2).choose

/-- The lengths of the rules of `I`, one for each pair of symbols with a rule. -/
def ruleLens
    -- the system
    {I : System S}
    -- a length for each pair of symbols
    (K : S.Sym × S.Sym → ℕ) :
    Set ℕ :=
  K '' {p | (I.rule p.1 p.2).isSome}

-- ============================================================================================
-- 3. Main results: uniform bounds
-- ============================================================================================

/-- **Uniform bounds, given by the lengths of the rules** (Lafont 1997, page 81: "let `L`
(resp. `M`) be the minimal (resp. the maximal) length of all those reductions"). On a finite
signature, a compatible translation is compatible within `L` and `M`, where `L` is the least and
`M` the greatest of the lengths `Compatible.len h (α, β)` of the rules of `I`. The rules of `I` are
those of a well-formed system and the rules of `I'` are linear, as in Proposition 4. -/
theorem Compatible.compatibleWithin_len
    -- a finite signature
    [Finite S.Sym]
    -- the two systems: `I` well-formed, the rules of `I'` linear
    {I : System S} {I' : System S'}
    (hI : I.WellFormed)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- `Φ` is compatible with them
    (h : Φ.Compatible I I') :
    -- `Φ` is compatible within the least and the greatest length of the rules
    Φ.CompatibleWithin I I' (sInf (ruleLens (I := I) h.len)) (sSup (ruleLens (I := I) h.len)) := by
  refine CompatibleWithin.of_distinct hI hI' ?_
  intro α β r hr xs ys f g hx hy hxy hl
  have hmem : h.len (α, β) ∈ ruleLens (I := I) h.len :=
    ⟨(α, β), by simp [hr], rfl⟩
  have hfin : (ruleLens (I := I) h.len).Finite :=
    (Set.finite_range h.len).subset (Set.image_subset_range _ _)
  obtain ⟨M, N', h', hS, hE, hT⟩ :=
    (h.exists_length α β).choose_spec r hr xs ys f g hx hy hxy hl
  exact ⟨M, N', h', ⟨h.len (α, β), Nat.sInf_le hmem, le_csSup hfin.bddAbove hmem, hS⟩, hE, hT⟩

/-- **A compatible translation on a finite signature has uniform bounds `L`, `M`** (Lafont 1997,
page 81: each interaction is simulated in `k` interactions with `L ≤ k ≤ M`, where `L` (resp.
`M`) is "the minimal (resp. the maximal) length of all those reductions"). The rules of `I` are
those of a well-formed system and the rules of `I'` are linear, as in Proposition 4. `L` and `M`
are the least and the greatest length of the rules (`Compatible.compatibleWithin_len`). -/
theorem Compatible.exists_compatibleWithin
    -- a finite signature
    [Finite S.Sym]
    -- the two systems: `I` well-formed, the rules of `I'` linear
    {I : System S} {I' : System S'}
    (hI : I.WellFormed)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- `Φ` is compatible with them
    (h : Φ.Compatible I I') :
    -- there are bounds `L`, `M` within which `Φ` is compatible
    ∃ L M, Φ.CompatibleWithin I I' L M :=
  ⟨_, _, h.compatibleWithin_len hI hI'⟩

/-- **A strict compatible translation on a finite signature has bounds `0 < L`** (Lafont 1997,
page 81: "`L > 0` if `Φ` is strict"). -/
theorem Compatible.exists_compatibleWithin_pos
    -- a finite signature
    [Finite S.Sym]
    -- the two systems: `I` well-formed, the rules of `I'` linear
    {I : System S} {I' : System S'}
    (hI : I.WellFormed)
    (hI' : ∀ α β r, I'.rule α β = some r → r.Linear)
    -- `Φ` is strict and compatible with them
    (hΦ : Φ.Strict)
    (h : Φ.Compatible I I') :
    -- there are bounds `L`, `M`
    ∃ L M,
      -- with `L` positive,
      0 < L ∧
      -- within which `Φ` is compatible
      Φ.CompatibleWithin I I' L M := by
  obtain ⟨L, M, hLM⟩ := h.exists_compatibleWithin hI hI'
  exact ⟨max L 1, M, by omega, hLM.pos hΦ hI hI'⟩

end Translation

namespace Comb

/-- **Theorem 1 with step counts** (Lafont 1997, page 81 and Theorem 1, page 82). For a
well-formed interaction system on a finite signature and decomposition data `D`, the translation
of Fig. 10 into the interaction combinators simulates every interaction in `k` interactions with
`0 < L ≤ k ≤ M`, for some `L`, `M`. By Proposition 4 (`Translation.CompatibleWithin.steps`),
`n` interactions of `I` are then simulated in `n'` interactions of the combinators with
`L n ≤ n' ≤ M n`. -/
theorem codeTranslation_compatibleWithin
    -- a well-formed system on a finite signature
    {S : Signature} [Finite S.Sym]
    {I : System S}
    (hI : I.WellFormed)
    -- decomposition data for its rules
    (D : I.DecData) :
    -- there are bounds `L`, `M`
    ∃ L M,
      -- with `L` positive,
      0 < L ∧
      -- within which the translation of Fig. 10 into the combinators is compatible
      (codeTranslation D.side).CompatibleWithin I system L M :=
  (D.codeTranslation_compatible hI).exists_compatibleWithin_pos hI system_wellFormed.linear
    (codeTranslation_strict _)

end Comb

end INet
