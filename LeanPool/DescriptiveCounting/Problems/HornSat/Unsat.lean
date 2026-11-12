/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import Mathlib.Order.Lattice.Nat
public import LeanPool.DescriptiveCounting.Problems.HornSat.Membership
public import Mathlib.Data.Set.Card

/-!
# Horn *un*satisfiability has a short certificate

`HORNSATᶜ ∈ NP` (`DescriptiveComplexity.hornSat_compl_mem_NP`), equivalently
`HORNSAT ∈ coNP`: an unsatisfiable Horn formula admits a polynomial-size,
first-order checkable certificate of its unsatisfiability.

This is what makes level 0 of the hierarchy behave like the levels above it.
Complementing the Horn discharge turns it into the two *crossing* inclusions
`PTIME ⊆ coNP` and `co-PTIME ⊆ NP` (`DescriptiveComplexity.PTIME_subset_coNP`,
`DescriptiveComplexity.coPTIME_subset_NP`), which state closure properties of level 0
that the Horn fragment does not obviously have.

## The certificate

A Horn formula is unsatisfiable exactly when unit propagation derives the
premises of some clause that has no positive literal. The certificate guesses

* a set `T` of variables, meant to be (part of) the propagation closure, and
* a strict order `≺`, meant to record the order of derivation,

and checks, first-order, that

* `≺` is irreflexive and transitive – on a finite structure that already makes
  it well-founded, which is all the induction below needs;
* every `x ∈ T` is the positive literal of some clause all of whose negative
  literals lie in `T` and are strictly `≺`-earlier. This is what pins `T`
  *inside* the propagation closure: without the ordering condition one could
  take `T` to be everything;
* some clause has no positive literal and all its negative literals in `T`.

Soundness (`DescriptiveComplexity.subset_of_derivClosed`): in any model, `T` is
contained in the set of true variables – by well-founded induction along `≺`,
using the Horn condition, which is what makes the positive literal of a
satisfied clause *unique* and hence identifiable. The exhibited clause is then
falsified, so there is no model.

Completeness: the propagation closure itself (`DescriptiveComplexity.Forced`, defined by
its stages `DescriptiveComplexity.ForcedIn`) is a certificate, ordered by the stage at
which a variable enters it (`DescriptiveComplexity.dep`). If it were *not* one – if
every clause whose negative literals are all forced had a positive literal –
then `Forced` would itself be a model, so the formula would be satisfiable
(`DescriptiveComplexity.exists_goalClause`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

/-! ### Unit propagation and its least model -/

section LeastModel

variable {A : Type} [Language.sat.Structure A]

/-- The stages of unit propagation: `ForcedIn n x` says that `x` is the
positive literal of a clause whose negative literals are all forced in fewer
than `n` rounds. -/
def ForcedIn : ℕ → A → Prop
  | 0, _ => False
  | n + 1, x => ∃ c : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
      ∀ y : A, RelMap satNegIn ![c, y] → ForcedIn n y

/-- A variable is *forced* when some stage forces it. On a Horn formula this
is the least model of the implications. -/
def Forced (x : A) : Prop := ∃ n, ForcedIn n x

private theorem forcedIn_succ {n : ℕ} {x : A} (h : ForcedIn n x) : ForcedIn (n + 1) x := by
  induction n generalizing x with
  | zero => exact h.elim
  | succ n ih =>
    obtain ⟨c, hc, hp, hneg⟩ := h
    exact ⟨c, hc, hp, fun y hy => ih (hneg y hy)⟩

private theorem forcedIn_le {m n : ℕ} (hmn : m ≤ n) {x : A} (h : ForcedIn m x) : ForcedIn n x := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact forcedIn_succ (ih (Nat.lt_succ_iff.mp hlt))
    · rwa [heq] at h

/-- The stage at which a variable becomes forced. -/
private noncomputable def dep (x : A) : ℕ := sInf {n | ForcedIn n x}

private theorem forcedIn_dep {x : A} (h : Forced x) : ForcedIn (dep x) x :=
  Nat.sInf_mem h

private theorem dep_le {n : ℕ} {x : A} (h : ForcedIn n x) : dep x ≤ n :=
  Nat.sInf_le h

/-- Every forced variable is forced by a clause whose negative literals are
forced *strictly earlier*: the propagation closure is derivation-closed along
the stage order. -/
private theorem derivClosed_forced (x : A) (hx : Forced x) :
    ∃ c : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
      ∀ y : A, RelMap satNegIn ![c, y] → Forced y ∧ dep y < dep x := by
  have h := forcedIn_dep hx
  cases hd : dep x with
  | zero =>
    rw [hd] at h
    exact h.elim
  | succ m =>
    rw [hd] at h
    obtain ⟨c, hc, hp, hneg⟩ := h
    refine ⟨c, hc, hp, fun y hy => ?_⟩
    have hy' := hneg y hy
    exact ⟨⟨m, hy'⟩, lt_of_le_of_lt (dep_le hy') (by omega)⟩

/-- On a finite structure the stages stabilize: one stage forces everything
that is forced at all. -/
private theorem exists_forcedIn_bound [Finite A] :
    ∃ N : ℕ, ∀ x : A, Forced x → ForcedIn N x := by
  classical
  have := Fintype.ofFinite A
  refine ⟨Finset.univ.sup (dep (A := A)), fun x hx => ?_⟩
  exact forcedIn_le (Finset.le_sup (Finset.mem_univ x)) (forcedIn_dep hx)

/-- **Completeness of the certificate**: if the formula is unsatisfiable then
some clause has no positive literal and all its negative literals forced.
Otherwise the propagation closure would itself be a model. -/
theorem exists_goalClause [Finite A] (hunsat : ¬Satisfiable A) :
    ∃ c : A, RelMap satIsClause ![c] ∧
      (∀ y : A, RelMap satNegIn ![c, y] → Forced y) ∧
      ∀ x : A, ¬RelMap satPosIn ![c, x] := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨N, hN⟩ := exists_forcedIn_bound (A := A)
  refine hunsat ⟨Forced, fun c hc => ?_⟩
  by_cases hall : ∀ y : A, RelMap satNegIn ![c, y] → Forced y
  · obtain ⟨x, hx⟩ := hno c hc hall
    exact ⟨x, Or.inl ⟨hx, N + 1, c, hc, hx, fun y hy => hN y (hall y hy)⟩⟩
  · push Not at hall
    obtain ⟨y, hy, hyf⟩ := hall
    exact ⟨y, Or.inr ⟨hy, hyf⟩⟩

/-- **Soundness of the certificate**: a derivation-closed set sits inside every
model. The Horn condition is what makes this work – it identifies the positive
literal by which a satisfied clause is satisfied. -/
theorem subset_of_derivClosed [Finite A] (hhorn : AtMostOnePositive A)
    {R : A → A → Prop} (hirr : ∀ x, ¬R x x) (htr : ∀ x y z, R x y → R y z → R x z)
    {T : A → Prop}
    (hderiv : ∀ x : A, T x → ∃ c : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
      ∀ y : A, RelMap satNegIn ![c, y] → T y ∧ R y x)
    {ν : A → Prop}
    (hν : ∀ c : A, RelMap satIsClause ![c] →
      ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x))
    (x : A) (hx : T x) : ν x := by
  have : IsTrans A R := ⟨htr⟩
  have : Std.Irrefl R := ⟨hirr⟩
  have hwf : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  induction x using hwf.induction with
  | _ x ih =>
    obtain ⟨c, hc, hp, hneg⟩ := hderiv x hx
    obtain ⟨z, hz⟩ := hν c hc
    rcases hz with ⟨hpz, hνz⟩ | ⟨hnz, hνz⟩
    · rwa [hhorn c z x hc hpz hp] at hνz
    · exact absurd (ih z (hneg z hnz).2 (hneg z hnz).1) hνz

/-- The propagation closure sits inside every model: the instance of
`DescriptiveComplexity.subset_of_derivClosed` at the closure itself, ordered by its
stages. -/
theorem forced_subset_model [Finite A] (hhorn : AtMostOnePositive A) {ν : A → Prop}
    (hν : ∀ c : A, RelMap satIsClause ![c] →
      ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x))
    (x : A) (hx : Forced x) : ν x :=
  subset_of_derivClosed (R := fun a b : A => dep a < dep b) (T := Forced) hhorn
    (fun a => lt_irrefl (dep a)) (fun _ _ _ hab hbc => lt_trans hab hbc)
    derivClosed_forced hν x hx

/-- A clause whose negative literals are all forced forces its positive
literal. -/
private theorem forced_of_allNeg [Finite A] {c x : A} (hc : RelMap satIsClause ![c])
    (hp : RelMap satPosIn ![c, x]) (hall : ∀ y : A, RelMap satNegIn ![c, y] → Forced y) :
    Forced x := by
  obtain ⟨N, hN⟩ := exists_forcedIn_bound (A := A)
  exact ⟨N + 1, c, hc, hp, fun y hy => hN y (hall y hy)⟩

/-- The certificate exists exactly for the formulas that are not
yes-instances of HORN-SAT. -/
private theorem not_hornSatisfiable_iff [Finite A] :
    ¬HornSatisfiable A ↔
      ¬AtMostOnePositive A ∨
        ∃ R : A → A → Prop, ∃ T : A → Prop,
          ((∀ x, ¬R x x) ∧ ∀ x y z, R x y → R y z → R x z) ∧
          (∀ x : A, T x → ∃ c : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
            ∀ y : A, RelMap satNegIn ![c, y] → T y ∧ R y x) ∧
          ∃ c : A, RelMap satIsClause ![c] ∧
            (∀ y : A, RelMap satNegIn ![c, y] → T y) ∧ ∀ x : A, ¬RelMap satPosIn ![c, x] := by
  classical
  constructor
  · intro h
    by_cases hhorn : AtMostOnePositive A
    · refine Or.inr ⟨fun x y => dep x < dep y, Forced, ⟨fun x => lt_irrefl _, ?_⟩,
        derivClosed_forced, exists_goalClause fun hsat => h ⟨hhorn, hsat⟩⟩
      exact fun x y z hxy hyz => lt_trans hxy hyz
    · exact Or.inl hhorn
  · rintro (hhorn | ⟨R, T, ⟨hirr, htr⟩, hderiv, c, hc, hneg, hpos⟩) ⟨hhorn', hsat⟩
    · exact hhorn hhorn'
    · obtain ⟨ν, hν⟩ := hsat
      obtain ⟨z, hz⟩ := hν c hc
      rcases hz with ⟨hpz, -⟩ | ⟨hnz, hνz⟩
      · exact hpos z hpz
      · exact hνz (subset_of_derivClosed hhorn' hirr htr hderiv hν z (hneg z hnz))

/-- The Horn condition fails exactly when some clause has two distinct
positive literals. -/
private theorem not_atMostOnePositive_iff :
    ¬AtMostOnePositive A ↔ ∃ c x y : A, RelMap satIsClause ![c] ∧
      RelMap satPosIn ![c, x] ∧ RelMap satPosIn ![c, y] ∧ x ≠ y := by
  rw [AtMostOnePositive]
  push Not
  exact Iff.rfl

/-- **The stages of unit propagation stabilize at the size of the universe**:
they form an increasing chain of subsets, so if each of the first `Nat.card A`
steps grew strictly the last would overflow the universe. This honest bound –
rather than the indefinite one of
`DescriptiveComplexity.exists_forcedIn_bound` – is what a machine doing one
propagation round per element needs. -/
theorem forced_forcedIn_card [Finite A] {x : A} (hx : Forced x) :
    ForcedIn (Nat.card A) x := by
  classical
  have hstab : ∀ N : ℕ, (∀ y : A, ForcedIn (N + 1) y → ForcedIn N y) →
      ∀ (s : ℕ) (y : A), ForcedIn s y → ForcedIn N y := by
    intro N hN s
    induction s with
    | zero => exact fun y hy => hy.elim
    | succ s ih =>
      intro y hy
      rcases Nat.lt_or_ge N (s + 1) with hlt | hge
      · obtain ⟨c, hc, hp, hneg⟩ := hy
        exact hN y ⟨c, hc, hp, fun z hz => ih z (hneg z hz)⟩
      · exact forcedIn_le hge hy
  by_cases hgood : ∃ N ≤ Nat.card A, ∀ y : A, ForcedIn (N + 1) y → ForcedIn N y
  · obtain ⟨N, hNle, hN⟩ := hgood
    obtain ⟨n, hn⟩ := hx
    exact forcedIn_le hNle (hstab N hN n x hn)
  · exfalso
    push Not at hgood
    have hcard : ∀ N ≤ Nat.card A + 1, N ≤ {y : A | ForcedIn N y}.ncard := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        intro hN
        obtain ⟨y, hy1, hy2⟩ := hgood N (by omega)
        have hsub : {y : A | ForcedIn N y} ⊂ {y : A | ForcedIn (N + 1) y} :=
          ⟨fun z hz => forcedIn_succ hz, fun hcontra => hy2 (hcontra hy1)⟩
        have h1 := ih (by omega)
        have h2 := Set.ncard_lt_ncard hsub (Set.toFinite _)
        omega
    have h1 := hcard (Nat.card A + 1) le_rfl
    have h2 := Set.ncard_le_ncard
      (Set.subset_univ {y : A | ForcedIn (Nat.card A + 1) y}) (Set.toFinite _)
    rw [Set.ncard_univ] at h2
    omega

/-- **For a Horn instance, satisfiability is decided by the propagation
closure**: the CNF is satisfiable exactly when the closure, read as an
assignment, satisfies every clause. This is the semantic half of the
unit-propagation machine of the machine bridge: the machine computes the
closure and then verifies each clause against it. -/
theorem satisfiable_iff_forced_model [Finite A] (hhorn : AtMostOnePositive A) :
    Satisfiable A ↔ ∀ c : A, RelMap satIsClause ![c] →
      ∃ x : A, (RelMap satPosIn ![c, x] ∧ Forced x) ∨
        (RelMap satNegIn ![c, x] ∧ ¬Forced x) := by
  constructor
  · rintro ⟨ν, hν⟩ c hc
    by_cases hall : ∀ y : A, RelMap satNegIn ![c, y] → Forced y
    · obtain ⟨x, hx⟩ := hν c hc
      rcases hx with ⟨hp, -⟩ | ⟨hn, hνx⟩
      · exact ⟨x, Or.inl ⟨hp, forced_of_allNeg hc hp hall⟩⟩
      · exact absurd (forced_subset_model hhorn hν x (hall x hn)) hνx
    · push Not at hall
      obtain ⟨y, hy, hyn⟩ := hall
      exact ⟨y, Or.inr ⟨hy, hyn⟩⟩
  · intro h
    exact ⟨Forced, h⟩

end LeastModel

/-! ### The `Σ₁` definition -/

section SigmaOne

/-- The single existential block of the `Σ₁` definition of Horn
unsatisfiability: a unary relation variable (`true`: the derived set) and a
binary one (`false`: the derivation order). -/
def unsatBlock : SOBlock where
  ι := Bool
  arity := fun i => cond i 1 2

/-- The symbol of the derived-set variable. -/
def ubTSym : unsatBlock.lang.Relations 1 := ⟨true, rfl⟩

/-- The symbol of the derivation-order variable. -/
def ubRSym : unsatBlock.lang.Relations 2 := ⟨false, rfl⟩

/-- The vocabulary of the kernel: CNF instances together with the two guessed
relation variables. -/
abbrev unsatSOLang : Language := Language.sat.sum unsatBlock.lang

/-- The symbol for “is a clause” in the kernel's vocabulary. -/
abbrev uIsClSym : unsatSOLang.Relations 1 := Sum.inl satIsClause

/-- The symbol for “occurs positively in” in the kernel's vocabulary. -/
abbrev uPosSym : unsatSOLang.Relations 2 := Sum.inl satPosIn

/-- The symbol for “occurs negatively in” in the kernel's vocabulary. -/
abbrev uNegSym : unsatSOLang.Relations 2 := Sum.inl satNegIn

/-- The derived-set symbol in the kernel's vocabulary. -/
abbrev uTSym : unsatSOLang.Relations 1 := Sum.inr ubTSym

/-- The derivation-order symbol in the kernel's vocabulary. -/
abbrev uRSym : unsatSOLang.Relations 2 := Sum.inr ubRSym

/-- Failure of the Horn condition: some clause has two distinct positive
literals. -/
private noncomputable def notHornF : unsatSOLang.Sentence :=
  fo% ∃ c x y, ((uIsClSym(c) ∧ uPosSym(c, x)) ∧ uPosSym(c, y)) ∧ ¬ x ≐ y

/-- The guessed order is irreflexive and transitive – on a finite structure,
enough to make it well-founded. -/
private noncomputable def strictF : unsatSOLang.Sentence :=
  fo% (∀ x, ¬ uRSym(x, x)) ∧ ∀ x y z, uRSym(x, y) ∧ uRSym(y, z) → uRSym(x, z)

/-- Every element of the guessed set is derived by a clause whose negative
literals lie in the set and are strictly earlier. -/
private noncomputable def derivF : unsatSOLang.Sentence :=
  fo% ∀ x, uTSym(x) → ∃ c, (uIsClSym(c) ∧ uPosSym(c, x)) ∧
    ∀ y, uNegSym(c, y) → uTSym(y) ∧ uRSym(y, x)

/-- Some clause has no positive literal and all its negative literals in the
guessed set. -/
private noncomputable def goalF : unsatSOLang.Sentence :=
  fo% ∃ c, (uIsClSym(c) ∧ ∀ y, uNegSym(c, y) → uTSym(y)) ∧ ∀ x, ¬ uPosSym(c, x)

/-- The first-order kernel of the `Σ₁` definition of Horn unsatisfiability:
either the Horn condition fails, or the guessed pair is a certificate. -/
private noncomputable def unsatKernel : unsatSOLang.Sentence :=
  notHornF ⊔ (strictF ⊓ derivF ⊓ goalF)

/-! #### Realization of the kernel -/

section Realize

variable {A : Type} [Language.sat.Structure A] (ρ : unsatBlock.Assignment A)

private theorem realize_notHornF :
    (@Sentence.Realize unsatSOLang A
        (@sumStructure _ _ A _ (unsatBlock.structure ρ)) notHornF) ↔
      ∃ c x y : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
        RelMap satPosIn ![c, y] ∧ x ≠ y := by
  let := unsatBlock.structure ρ
  rw [notHornF]
  simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Language.relMap_sumInl]
  constructor
  · rintro ⟨i, ⟨⟨hc, hp1⟩, hp2⟩, hne⟩
    exact ⟨i 0, i 1, i 2, hc, hp1, hp2, hne⟩
  · rintro ⟨c, x, y, hc, hp1, hp2, hne⟩
    exact ⟨![c, x, y], ⟨⟨hc, hp1⟩, hp2⟩, hne⟩

private theorem realize_strictF :
    (@Sentence.Realize unsatSOLang A
        (@sumStructure _ _ A _ (unsatBlock.structure ρ)) strictF) ↔
      (∀ x : A, ¬ρ false ![x, x]) ∧
        ∀ x y z : A, ρ false ![x, y] → ρ false ![y, z] → ρ false ![x, z] := by
  let := unsatBlock.structure ρ
  have hsubR : ∀ w : Fin 2 → A,
      RelMap (L := unsatSOLang) (M := A) uRSym w ↔ ρ false w := fun _ => Iff.rfl
  rw [strictF]
  simp only [Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_not, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr, hsubR]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x => h1 ![x], fun x y z hxy hyz => h2 ![x, y, z] ⟨hxy, hyz⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => h1 (i 0), fun i hi => h2 (i 0) (i 1) (i 2) hi.1 hi.2⟩

private theorem realize_derivF :
    (@Sentence.Realize unsatSOLang A
        (@sumStructure _ _ A _ (unsatBlock.structure ρ)) derivF) ↔
      ∀ x : A, ρ true ![x] → ∃ c : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
        ∀ y : A, RelMap satNegIn ![c, y] → ρ true ![y] ∧ ρ false ![y, x] := by
  let := unsatBlock.structure ρ
  have hsubT : ∀ w : Fin 1 → A,
      RelMap (L := unsatSOLang) (M := A) uTSym w ↔ ρ true w := fun _ => Iff.rfl
  have hsubR : ∀ w : Fin 2 → A,
      RelMap (L := unsatSOLang) (M := A) uRSym w ↔ ρ false w := fun _ => Iff.rfl
  rw [derivF]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp, Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, Language.relMap_sumInl, hsubT, hsubR]
  constructor
  · intro h x hx
    obtain ⟨c, ⟨hc, hp⟩, hneg⟩ := h ![x] hx
    exact ⟨c 0, hc, hp, fun y hy => hneg (fun _ => y) hy⟩
  · intro h i hi
    obtain ⟨c, hc, hp, hneg⟩ := h (i 0) hi
    exact ⟨fun _ => c, ⟨hc, hp⟩, fun k hk => hneg (k 0) hk⟩

private theorem realize_goalF :
    (@Sentence.Realize unsatSOLang A
        (@sumStructure _ _ A _ (unsatBlock.structure ρ)) goalF) ↔
      ∃ c : A, RelMap satIsClause ![c] ∧ (∀ y : A, RelMap satNegIn ![c, y] → ρ true ![y]) ∧
        ∀ x : A, ¬RelMap satPosIn ![c, x] := by
  let := unsatBlock.structure ρ
  have hsubT : ∀ w : Fin 1 → A,
      RelMap (L := unsatSOLang) (M := A) uTSym w ↔ ρ true w := fun _ => Iff.rfl
  rw [goalF]
  simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_iAlls,
    Formula.realize_inf, Formula.realize_imp, Formula.realize_not, Formula.realize_rel₁,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsubT]
  constructor
  · rintro ⟨c, ⟨hc, hneg⟩, hpos⟩
    exact ⟨c 0, hc, fun y hy => hneg (fun _ => y) hy, fun x hx => hpos (fun _ => x) hx⟩
  · rintro ⟨c, hc, hneg, hpos⟩
    exact ⟨fun _ => c, ⟨hc, fun k hk => hneg (k 0) hk⟩, fun k hk => hpos (k 0) hk⟩

private theorem realize_unsatKernel :
    (@Sentence.Realize unsatSOLang A
        (@sumStructure _ _ A _ (unsatBlock.structure ρ)) unsatKernel) ↔
      (∃ c x y : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
          RelMap satPosIn ![c, y] ∧ x ≠ y) ∨
        (((∀ x : A, ¬ρ false ![x, x]) ∧
            ∀ x y z : A, ρ false ![x, y] → ρ false ![y, z] → ρ false ![x, z]) ∧
          (∀ x : A, ρ true ![x] → ∃ c : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
            ∀ y : A, RelMap satNegIn ![c, y] → ρ true ![y] ∧ ρ false ![y, x]) ∧
          ∃ c : A, RelMap satIsClause ![c] ∧
            (∀ y : A, RelMap satNegIn ![c, y] → ρ true ![y]) ∧
            ∀ x : A, ¬RelMap satPosIn ![c, x]) := by
  let := unsatBlock.structure ρ
  have hsup : (@Sentence.Realize unsatSOLang A _ unsatKernel) ↔
      (@Sentence.Realize unsatSOLang A _ notHornF) ∨
        ((@Sentence.Realize unsatSOLang A _ strictF) ∧
          (@Sentence.Realize unsatSOLang A _ derivF)) ∧
        (@Sentence.Realize unsatSOLang A _ goalF) := by
    rw [unsatKernel]
    exact Formula.realize_sup.trans
      (or_congr Iff.rfl (Formula.realize_inf.trans (and_congr Formula.realize_inf Iff.rfl)))
  refine hsup.trans (or_congr (realize_notHornF ρ) ?_)
  exact (and_congr (and_congr (realize_strictF ρ) (realize_derivF ρ))
    (realize_goalF ρ)).trans and_assoc

end Realize

/-! ### Horn unsatisfiability is in NP -/

/-- **The complement of HORN-SAT is `Σ₁`-definable**: guess the derivation
order and the derived set, and check the certificate first-order. -/
private theorem hornSat_compl_sigmaSODefinable : SigmaSODefinable 1 HORNSATᶜ := by
  refine ⟨[unsatBlock], rfl, unsatKernel, ?_⟩
  intro A _ _ _
  refine Iff.trans (not_hornSatisfiable_iff (A := A)) ?_
  constructor
  · rintro (hnh | ⟨R, T, ⟨hirr, htr⟩, hderiv, hgoal⟩)
    · refine ⟨fun i => match i with
        | true => fun _ : Fin 1 → A => False
        | false => fun _ : Fin 2 → A => False, ?_⟩
      exact (realize_unsatKernel _).mpr (Or.inl (not_atMostOnePositive_iff.mp hnh))
    · refine ⟨fun i => match i with
        | true => fun w : Fin 1 → A => T (w 0)
        | false => fun w : Fin 2 → A => R (w 0) (w 1), ?_⟩
      exact (realize_unsatKernel _).mpr (Or.inr ⟨⟨hirr, htr⟩, hderiv, hgoal⟩)
  · rintro ⟨ρ, hρ⟩
    rcases (realize_unsatKernel ρ).mp hρ with h | ⟨⟨hirr, htr⟩, hderiv, hgoal⟩
    · exact Or.inl (not_atMostOnePositive_iff.mpr h)
    · exact Or.inr ⟨fun x y => ρ false ![x, y], fun x => ρ true ![x],
        ⟨hirr, htr⟩, hderiv, hgoal⟩

/-- The complement of HORN-SAT is in NP. -/
theorem hornSat_compl_mem_NP : HORNSATᶜ ∈ NP :=
  hornSat_compl_sigmaSODefinable

/-- **HORN-SAT is in coNP**: Horn unsatisfiability has a first-order checkable
certificate. -/
private theorem hornSat_mem_coNP : HORNSAT ∈ coNP :=
  (mem_piP_iff 1 HORNSAT).mpr hornSat_compl_mem_NP

end SigmaOne

end DescriptiveComplexity
