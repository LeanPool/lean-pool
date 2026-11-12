/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Problems.Sat
public import LeanPool.DescriptiveCounting.Problems.Sat.TseitinFormulas
public import Mathlib.Data.Fintype.Lattice
import all LeanPool.DescriptiveCounting.Complexity
import all LeanPool.DescriptiveCounting.Hierarchy
import all LeanPool.DescriptiveCounting.Padding
import all LeanPool.DescriptiveCounting.Problems.Sat.Tseitin

/-!
# The Cook–Levin theorem: hardness of SAT

The hardness half of the Cook–Levin theorem ([Cook 1971][cook1971complexity];
[Levin 1973][levin1973universal]), machine-free and in the style of Dahlhaus
([Dahlhaus 1983][dahlhaus1983reduction]): every existential-second-order
definable problem admits an ordered
first-order reduction to SAT
(`DescriptiveComplexity.sat_hard_of_sigmaSODefinable`). Since NP is *defined* as
`Σ₁`-definability (`DescriptiveComplexity.Hierarchy`), together with the membership
half `DescriptiveComplexity.sat_sigmaSODefinable` this makes SAT NP-complete
(`DescriptiveComplexity.SAT_NP_complete`) – relying on no axioms beyond
Lean's standard three, as `#print axioms` confirms.

Given the single second-order block `B` and the first-order kernel `φ` of a
`Σ₁` definition of a problem `Q`, the reduction interprets, inside an ordered
input structure `A`, the CNF instance of the Tseitin encoding
([Tseitin 1968][tseitin1968complexity]) of `φ`
(`DescriptiveComplexity.Problems.Sat.Tseitin`):

* propositional variables: one per relation variable `i` of `B` and
  `B.arity i`-tuple over `A` (element `(Sum.inr (Sum.inl i), x)`), and one
  per subformula position `p` of `φ` and context tuple (element
  `(Sum.inr (Sum.inr ⟨m, p⟩), x)`);
* clauses: up to three kinds per position (elements
  `(Sum.inl (Sum.inl (⟨m, p⟩, k)), u)`), plus the top-level unit clause
  `(Sum.inl (Sum.inr ()), u)` forcing the root variable;
* tuples of length `DescriptiveComplexity.tseitinDim B φ` are padded canonically with
  minimal elements of the order – the one place where the order is used;
  non-canonical tuples are junk: they are neither clauses nor occur in any
  clause.

The correctness proof (`DescriptiveComplexity.tseitin_satisfiable_iff`) composes the
characterization lemmas of the interpreted relations with the semantic
equivalence `DescriptiveComplexity.Tseitin.satCond_iff_gates` and the
gate-correctness lemmas `DescriptiveComplexity.Tseitin.gates_realize` /
`DescriptiveComplexity.Tseitin.gates_canonVal`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure Tseitin

section Interp

variable {L : Language.{0, 0}} (B : SOBlock) (φ : (L.sum B.lang).Sentence)

/-- The dimension of the Tseitin interpretation: large enough for every
context tuple of the kernel and every argument tuple of a block variable. -/
noncomputable def tseitinDim : ℕ :=
  max (contextBound φ) (blockArityBound B)

theorem contextBound_le_tseitinDim : contextBound φ ≤ tseitinDim B φ :=
  le_max_left _ _

theorem arity_le_tseitinDim (i : B.ι) : B.arity i ≤ tseitinDim B φ :=
  (arity_le_blockArityBound B i).trans (le_max_right _ _)

/-- The tags of the Tseitin interpretation: clauses of the encoding (per
position and kind, plus the top-level unit clause), then propositional
variables (per block variable, and per position). -/
def TseitinTag : Type :=
  ((Σ m, NodeAt φ m) × Fin 3 ⊕ Unit) ⊕ (B.ι ⊕ Σ m, NodeAt φ m)

instance : Finite (TseitinTag B φ) := by
  unfold TseitinTag
  infer_instance

instance : Nonempty (TseitinTag B φ) :=
  ⟨Sum.inl (Sum.inr ())⟩

/-- The defining formula of `satPosIn` (`s = true`) and `satNegIn`
(`s = false`), by clause and variable tag: the literals of the node clauses
(`DescriptiveComplexity.Tseitin.litF`), and the root variable, at fully padded tuples,
positively in the top clause. -/
noncomputable def tseitinLitFml (s : Bool) (tc tx : TseitinTag B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (tseitinDim B φ)) :=
  match tc, tx with
  | Sum.inl (Sum.inl (σp, k)), Sum.inr vt =>
      litF s φ (contextBound_le_tseitinDim B φ) σp.2 k vt
        (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
  | Sum.inl (Sum.inr _), Sum.inr (Sum.inr σp') =>
      if isRootB φ σp'.2 && s then
        canonF 0 (fun j => ((0 : Fin 2), j)) ⊓ canonF 0 fun j => ((1 : Fin 2), j)
      else ⊥
  | _, _ => ⊥

/-- The Tseitin interpretation: the CNF instance of the encoding of `φ`,
defined inside the ordered input structure. -/
noncomputable def tseitinInterp :
    FOInterpretation (L.sum Language.order) Language.sat (TseitinTag B φ)
      (tseitinDim B φ) where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
        (match t 0 with
         | Sum.inl (Sum.inl (σp, k)) =>
             isClauseF φ (contextBound_le_tseitinDim B φ) σp.2 k fun j => ((0 : Fin 1), j)
         | Sum.inl (Sum.inr _) => canonF 0 fun j => ((0 : Fin 1), j)
         | Sum.inr _ => ⊥)
    | _, .posIn => fun t => tseitinLitFml B φ true (t 0) (t 1)
    | _, .negIn => fun t => tseitinLitFml B φ false (t 0) (t 1)

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {A : Type} [L.Structure A] [LinearOrder A]

private theorem tseitin_isClause_node (σp : Σ m, NodeAt φ m) (k : Fin 3)
    (u : Fin (tseitinDim B φ) → A) :
    RelMap (M := (tseitinInterp B φ).Map A) satIsClause
        ![(Sum.inl (Sum.inl (σp, k)), u)] ↔
      IsClauseSem φ (contextBound_le_tseitinDim B φ) σp.2 k u := by
  rw [FOInterpretation.relMap_map]
  exact realize_isClauseF φ (contextBound_le_tseitinDim B φ) σp.2 k fun j => (0, j)

private theorem tseitin_isClause_top (u : Fin (tseitinDim B φ) → A) :
    RelMap (M := (tseitinInterp B φ).Map A) satIsClause
        ![(Sum.inl (Sum.inr ()), u)] ↔ Canon 0 u := by
  rw [FOInterpretation.relMap_map]
  exact realize_canonF

private theorem tseitin_isClause_var (vt : B.ι ⊕ Σ m, NodeAt φ m)
    (u : Fin (tseitinDim B φ) → A) :
    ¬RelMap (M := (tseitinInterp B φ).Map A) satIsClause ![(Sum.inr vt, u)] := by
  rw [FOInterpretation.relMap_map]
  exact id

/-- The semantic content of the literal formulas, by clause and variable
tag. -/
def TseitinLitSem (s : Bool) (tc tx : TseitinTag B φ)
    (u x : Fin (tseitinDim B φ) → A) : Prop :=
  match tc, tx with
  | Sum.inl (Sum.inl (σp, k)), Sum.inr vt =>
      LitSem s φ (contextBound_le_tseitinDim B φ) σp.2 k u vt x
  | Sum.inl (Sum.inr _), Sum.inr (Sum.inr σp') =>
      s = true ∧ σp' = ⟨0, rootAt φ⟩ ∧ Canon 0 u ∧ Canon 0 x
  | _, _ => False

private theorem tseitin_lit_iff (s : Bool) (tc tx : TseitinTag B φ)
    (u x : Fin (tseitinDim B φ) → A) :
    RelMap (M := (tseitinInterp B φ).Map A) (if s then satPosIn else satNegIn)
        ![(tc, u), (tx, x)] ↔ TseitinLitSem B φ s tc tx u x := by
  have hlit : RelMap (M := (tseitinInterp B φ).Map A)
        (if s then satPosIn else satNegIn) ![(tc, u), (tx, x)] ↔
      (tseitinLitFml B φ s tc tx).Realize
        (fun p => ((![((tc, u) : (tseitinInterp B φ).Map A), (tx, x)]) p.1).2 p.2) := by
    cases s
    · rw [ite_eq_right (by simp)]
      exact FOInterpretation.relMap_map _ _ satNegIn _
    · rw [ite_eq_left rfl]
      exact FOInterpretation.relMap_map _ _ satPosIn _
  rw [hlit]
  rcases tc with tcl | tcv
  · rcases tcl with ⟨σp, k⟩ | u'
    · rcases tx with txl | vt
      · exact iff_of_false id id
      · exact realize_litF s φ (contextBound_le_tseitinDim B φ) σp.2 k vt
          (fun j => (0, j)) fun j => (1, j)
    · rcases tx with txl | vt
      · exact iff_of_false id id
      · rcases vt with i | σp'
        · exact iff_of_false id id
        · rw [show tseitinLitFml B φ s (Sum.inl (Sum.inr u')) (Sum.inr (Sum.inr σp')) =
              if isRootB φ σp'.2 && s then
                canonF 0 (fun j => ((0 : Fin 2), j)) ⊓
                  canonF 0 fun j => ((1 : Fin 2), j)
              else ⊥ from rfl]
          split_ifs with hb
          · rw [Formula.realize_inf, realize_canonF, realize_canonF]
            obtain ⟨hroot, rfl⟩ : isRootB φ σp'.2 = true ∧ s = true := by
              simpa using hb
            have hσ : σp' = ⟨0, rootAt φ⟩ := by
              have := (isRootB_iff φ σp'.2).mp hroot
              exact (Sigma.eta σp') ▸ this
            constructor
            · rintro ⟨hu, hx⟩
              exact ⟨rfl, hσ, hu, hx⟩
            · rintro ⟨-, -, hu, hx⟩
              exact ⟨hu, hx⟩
          · rw [Formula.realize_bot]
            refine iff_of_false id ?_
            rintro ⟨rfl, rfl, -, -⟩
            rw [show isRootB φ (Sigma.mk 0 (rootAt φ)).2 = true from
              (isRootB_iff φ (rootAt φ)).mpr rfl] at hb
            exact hb rfl
  · exact iff_of_false id id

end Characterizations

/-! ### Correctness of the reduction

The two directions are stated for an explicit truth assignment of the
interpreted instance, so that they can be reused where the assignments
themselves matter and not only their existence (counting,
`DescriptiveComplexity.Problems.Sat.CountingHardness`). -/

section Correctness

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The valuation of the propositional variables of the encoding determined by
an assignment of the block: a block variable at a tuple reads the assignment at
the tuple's prefix, a position variable the truth value of its subformula. -/
def tseitinVal (μ : B.Assignment A) (vt : B.ι ⊕ Σ m, NodeAt φ m)
    (x : Fin (tseitinDim B φ) → A) : Prop :=
  match vt with
  | Sum.inl i => μ i fun j => x (Fin.castLE (arity_le_tseitinDim B φ i) j)
  | Sum.inr σp =>
      canonVal μ φ σp.1 σp.2
        (pref ((nodeAt_le_contextBound φ σp.2).trans (contextBound_le_tseitinDim B φ)) x)

omit [LinearOrder A] in
theorem padAssign_tseitinVal (a₀ : A) (μ : B.Assignment A) :
    padAssign a₀ (tseitinVal B φ μ) = μ := by
  funext i a
  change μ i (fun j => pad a₀ a (Fin.castLE (arity_le_tseitinDim B φ i) j)) = μ i a
  exact congrArg (μ i) (pref_pad a₀ (arity_le_tseitinDim B φ i) a)

omit [LinearOrder A] in
theorem padVal_tseitinVal (a₀ : A) (μ : B.Assignment A) :
    padVal a₀ (tseitinVal B φ μ) = canonVal μ φ := by
  funext m p w
  change canonVal μ φ m p
    (pref ((nodeAt_le_contextBound φ p).trans (contextBound_le_tseitinDim B φ)) (pad a₀ w)) =
      canonVal μ φ m p w
  exact congrArg (canonVal μ φ m p) (pref_pad a₀ _ w)

/-- **From clauses to gates**: a truth assignment satisfying every clause of
the interpreted instance induces, through canonical padding, a valuation
satisfying every gate, and the block assignment it induces realizes the
kernel. -/
theorem tseitin_gates_of_clauses {a₀ : A} (ha₀ : IsBot a₀)
    (ν : (tseitinInterp B φ).Map A → Prop)
    (hν : ∀ c : (tseitinInterp B φ).Map A, RelMap satIsClause ![c] →
      ∃ x, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)) :
    Gates (padAssign a₀ fun vt x => ν (Sum.inr vt, x)) φ
        (padVal a₀ fun vt x => ν (Sum.inr vt, x)) ∧
      RealizeWith (padAssign a₀ fun vt x => ν (Sum.inr vt, x)) φ finZeroElim := by
  have hctx := contextBound_le_tseitinDim B φ
  have harity := arity_le_tseitinDim B φ
  have hsat : SatCond φ hctx fun vt x => ν (Sum.inr vt, x) := by
    intro m p k u hcl
    obtain ⟨⟨tx, x⟩, hx⟩ := hν (Sum.inl (Sum.inl (⟨m, p⟩, k)), u)
      ((tseitin_isClause_node B φ ⟨m, p⟩ k u).mpr hcl)
    rcases hx with ⟨hpos, hval⟩ | ⟨hneg, hval⟩
    · have hls := (tseitin_lit_iff B φ true (Sum.inl (Sum.inl (⟨m, p⟩, k))) tx
        u x).mp hpos
      rcases tx with tcl | vt
      · exact hls.elim
      · exact ⟨vt, x, Or.inl ⟨hls, hval⟩⟩
    · have hls := (tseitin_lit_iff B φ false (Sum.inl (Sum.inl (⟨m, p⟩, k))) tx
        u x).mp hneg
      rcases tx with tcl | vt
      · exact hls.elim
      · exact ⟨vt, x, Or.inr ⟨hls, hval⟩⟩
  have hg := (satCond_iff_gates ha₀ harity φ hctx _).mp hsat
  refine ⟨hg, ?_⟩
  obtain ⟨⟨tx, x⟩, hx⟩ := hν (Sum.inl (Sum.inr ()), fun _ => a₀)
    ((tseitin_isClause_top B φ _).mpr fun j _ => ha₀)
  rcases hx with ⟨hpos, hval⟩ | ⟨hneg, hval⟩
  · have hls := (tseitin_lit_iff B φ true (Sum.inl (Sum.inr ())) tx _ x).mp hpos
    rcases tx with tcl | vt
    · exact hls.elim
    · rcases vt with i | σp'
      · exact hls.elim
      · obtain ⟨-, rfl, -, hcx⟩ := hls
        refine (gates_realize _ φ _ hg finZeroElim).mp ?_
        change ν (Sum.inr (Sum.inr ⟨0, rootAt φ⟩), pad a₀ finZeroElim)
        have hx0 : x = pad a₀ finZeroElim := by
          rw [← pad_pref_of_canon ha₀ (Nat.zero_le _) hcx]
          exact (congrArg (pad a₀) (Subsingleton.elim _ _)).symm
        rw [← hx0]
        exact hval
  · have hls := (tseitin_lit_iff B φ false (Sum.inl (Sum.inr ())) tx _ x).mp hneg
    rcases tx with tcl | vt
    · exact hls.elim
    · rcases vt with i | σp'
      · exact hls.elim
      · exact absurd hls.1 (by simp)

/-- **From an assignment to clauses**: a truth assignment of the interpreted
instance that reads, at the propositional variables, the valuation determined
by a block assignment realizing the kernel, satisfies every clause. -/
private theorem tseitin_clauses_of_realize {a₀ : A} (ha₀ : IsBot a₀) (μ : B.Assignment A)
    (hμ : RealizeWith μ φ finZeroElim) (ν : (tseitinInterp B φ).Map A → Prop)
    (hνμ : ∀ vt x, ν (Sum.inr vt, x) ↔ tseitinVal B φ μ vt x)
    (c : (tseitinInterp B φ).Map A) (hcl : RelMap satIsClause ![c]) :
    ∃ x, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x) := by
  have hctx := contextBound_le_tseitinDim B φ
  have harity := arity_le_tseitinDim B φ
  have hg : Gates (padAssign a₀ (tseitinVal B φ μ)) φ (padVal a₀ (tseitinVal B φ μ)) := by
    rw [padAssign_tseitinVal, padVal_tseitinVal]
    exact gates_canonVal μ φ
  have hsat := (satCond_iff_gates ha₀ harity φ hctx (tseitinVal B φ μ)).mpr hg
  obtain ⟨tc, u⟩ := c
  rcases tc with tcl | vt
  swap
  · exact absurd hcl (tseitin_isClause_var B φ vt u)
  rcases tcl with ⟨σp, k⟩ | u'
  · rw [tseitin_isClause_node] at hcl
    obtain ⟨vt, x, hor⟩ := hsat σp.1 σp.2 k u hcl
    rcases hor with ⟨hls, hval⟩ | ⟨hls, hval⟩
    · refine ⟨(Sum.inr vt, x), Or.inl ⟨?_, (hνμ vt x).mpr hval⟩⟩
      exact (tseitin_lit_iff B φ true (Sum.inl (Sum.inl (σp, k)))
        (Sum.inr vt) u x).mpr hls
    · refine ⟨(Sum.inr vt, x), Or.inr ⟨?_, fun h => hval ((hνμ vt x).mp h)⟩⟩
      exact (tseitin_lit_iff B φ false (Sum.inl (Sum.inl (σp, k)))
        (Sum.inr vt) u x).mpr hls
  · rw [tseitin_isClause_top] at hcl
    refine ⟨(Sum.inr (Sum.inr ⟨0, rootAt φ⟩), pad a₀ finZeroElim),
      Or.inl ⟨?_, (hνμ _ _).mpr ?_⟩⟩
    · exact (tseitin_lit_iff B φ true (Sum.inl (Sum.inr u'))
        (Sum.inr (Sum.inr ⟨0, rootAt φ⟩)) u _).mpr
        ⟨rfl, rfl, hcl, canon_pad ha₀ 0 _⟩
    · change canonVal μ φ 0 (rootAt φ)
        (pref ((nodeAt_le_contextBound φ (rootAt φ)).trans hctx) (pad a₀ finZeroElim))
      refine (canonVal_rootAt μ φ _).mpr ?_
      have he : (pref ((nodeAt_le_contextBound φ (rootAt φ)).trans hctx)
          (pad a₀ finZeroElim) : Fin 0 → A) = finZeroElim :=
        Subsingleton.elim _ _
      rw [he]
      exact hμ

end Correctness

/-- **Correctness of the Tseitin interpretation**: the interpreted CNF
instance is satisfiable iff some assignment of the block variables realizes
the kernel. -/
theorem tseitin_satisfiable_iff (A : Type) [L.Structure A] [LinearOrder A]
    [Finite A] [Nonempty A] :
    Satisfiable ((tseitinInterp B φ).Map A) ↔
      ∃ μ : B.Assignment A, RealizeWith μ φ finZeroElim := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  constructor
  · rintro ⟨ν, hν⟩
    exact ⟨_, (tseitin_gates_of_clauses B φ ha₀ ν hν).2⟩
  · rintro ⟨μ, hμ⟩
    refine ⟨fun e =>
      match e with
      | (Sum.inr vt, x) => tseitinVal B φ μ vt x
      | (Sum.inl _, _) => False, fun c hcl => ?_⟩
    exact tseitin_clauses_of_realize B φ ha₀ μ hμ _ (fun _ _ => Iff.rfl) c hcl

/-- The head of a one-block second-order satisfaction is realization of the
kernel in the expansion by an assignment. -/
theorem sorealize_head_iff {A : Type} [L.Structure A] :
    SORealize L A [B] φ true ↔ ∃ μ : B.Assignment A, RealizeWith μ φ finZeroElim := by
  refine exists_congr fun μ => ?_
  exact iff_of_eq (congrArg₂
    (fun (v : Empty → A) (xs : Fin 0 → A) =>
      @BoundedFormula.Realize _ A (B.structure₁ (L := L) μ) _ _ φ v xs)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/-- **The generic Tseitin reduction**: an ordered first-order reduction to
SAT from any problem defined, on nonempty finite structures, by an
existential second-order sentence with a single block. -/
noncomputable def tseitinReduction [L.IsRelational] (Q : DecisionProblem L)
    (hφ : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      Q A ↔ SORealize L A [B] φ true) : Q ≤ᶠᵒ[≤] SAT where
  Tag := TseitinTag B φ
  dim := tseitinDim B φ
  toInterpretation := tseitinInterp B φ
  correct A _ _ _ _ :=
    (hφ A).trans ((sorealize_head_iff B φ).trans
      (tseitin_satisfiable_iff B φ A).symm)

end Interp

/-! ### The Cook–Levin theorem -/

/-- The hardness half of the Cook–Levin theorem: every
existential-second-order definable problem admits an ordered first-order
reduction to SAT. Machine-free NP-hardness in the style of Dahlhaus, by the
generic Tseitin reduction `DescriptiveComplexity.tseitinReduction`.
Registered in the Lax archive as
[`Lax904597.CookLevin.sat_hard_of_sigmaSODefinable`](https://laxarchive.org/lax-904597/Lax904597.CookLevin.html#s-Lax904597.CookLevin.sat_hard_of_sigmaSODefinable). -/
theorem sat_hard_of_sigmaSODefinable :
    ∀ {L : Language.{0, 0}} [L.IsRelational] (Q : DecisionProblem L),
      SigmaSODefinable 1 Q → Nonempty (Q ≤ᶠᵒ[≤] SAT) := by
  rintro L _ Q ⟨Bs, hlen, φ, hφ⟩
  cases Bs with
  | nil => exact absurd hlen (by simp)
  | cons B Bs' =>
    cases Bs' with
    | nil => exact ⟨tseitinReduction B φ Q hφ⟩
    | cons B' Bs'' => simp at hlen

/-- **The Cook–Levin theorem**: SAT is NP-complete. Membership is
`DescriptiveComplexity.sat_sigmaSODefinable`; hardness is
`DescriptiveComplexity.sat_hard_of_sigmaSODefinable`, the generic Tseitin reduction.
Registered in the Lax archive as
[`Lax904597.CookLevin.SAT_NP_complete`](https://laxarchive.org/lax-904597/Lax904597.CookLevin.html#s-Lax904597.CookLevin.SAT_NP_complete). -/
theorem SAT_NP_complete : NP.Complete SAT :=
  ⟨sat_sigmaSODefinable,
    (hard_sigmaP_succ_iff 0 SAT).mpr fun Q hQ =>
      (sat_hard_of_sigmaSODefinable Q hQ).map OrderedFOReduction.toRel⟩

/-- SAT is in NP. -/
theorem sat_mem_NP : SAT ∈ NP :=
  SAT_NP_complete.mem

/-- SAT is NP-hard. -/
theorem sat_NP_hard : NP.Hard SAT :=
  SAT_NP_complete.hard

/-- The complement of SAT (essentially, propositional entailment of `⊥`) is
in coNP. -/
private theorem sat_compl_mem_coNP : SATᶜ ∈ coNP :=
  (compl_mem_coNP_iff SAT).mpr sat_mem_NP

end DescriptiveComplexity
