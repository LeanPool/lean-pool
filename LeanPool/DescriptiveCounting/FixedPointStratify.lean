/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrderBlockHom
public import LeanPool.DescriptiveCounting.FixedPointInflationary
import all LeanPool.DescriptiveCounting.FixedPointStep
import all LeanPool.DescriptiveCounting.SecondOrderBlockHom

/-!
# Stratified inflationary inductions

Composition of inflationary inductions: a second
induction whose step formulas read the *converged* relations of a first is
itself a single induction. The second stratum is presented as a
`DescriptiveComplexity.StepDef` over the base vocabulary *expanded by the
first stratum's block* – its semantics is «run over the structure expanded by
the first stratum's limit» – and the composite
`DescriptiveComplexity.StepDef.stratify` computes exactly that value
(`DescriptiveComplexity.StepDef.ifpHolds_stratify`).

The construction gates the second stratum on an arity-`0` *gate* variable,
derived once the first stratum's step formulas add nothing to its current
stage – a first-order condition, since the step formulas are formulas
(`DescriptiveComplexity.stratGateF`). Inflation makes the timing work: before
the gate fires the second stratum is empty; the gate fires exactly when the
first stratum has reached its limit, which it then never leaves; from that
point on the second stratum replays its own stages verbatim
(`DescriptiveComplexity.StepDef.strat2Assign_inflStage_add`).

Its consumer is the invariant layer of the Abiteboul–Vianu development: the
canonical order on `≡ᵏ`-classes is one stratum, the simulation of an ordered
induction over the invariant structure reads it as a second.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

/-! ### The combined block and its vocabulary -/

/-- The block of a stratified induction: the first stratum's variables, an
arity-`0` gate, the second stratum's variables. -/
def stratBlock (B₁ B₂ : SOBlock) : SOBlock where
  ι := (B₁.ι ⊕ Unit) ⊕ B₂.ι
  arity := fun i =>
    match i with
    | .inl (.inl i) => B₁.arity i
    | .inl (.inr _) => 0
    | .inr i => B₂.arity i

/-- The relation symbol of a first-stratum variable. -/
abbrev strat1Sym (L : Language.{0, 0}) (B₁ B₂ : SOBlock) (i : B₁.ι) :
    (L.sum (stratBlock B₁ B₂).lang).Relations (B₁.arity i) :=
  Sum.inr ⟨.inl (.inl i), rfl⟩

/-- The relation symbol of the gate. -/
abbrev stratGateSym (L : Language.{0, 0}) (B₁ B₂ : SOBlock) :
    (L.sum (stratBlock B₁ B₂).lang).Relations 0 :=
  Sum.inr ⟨.inl (.inr ()), rfl⟩

section Parts

variable {B₁ B₂ : SOBlock} {A : Type}

/-- The first-stratum part of an assignment of the combined block. -/
def strat1Assign (σ : (stratBlock B₁ B₂).Assignment A) : B₁.Assignment A :=
  fun i x => σ (.inl (.inl i)) x

/-- The second-stratum part of an assignment of the combined block. -/
def strat2Assign (σ : (stratBlock B₁ B₂).Assignment A) : B₂.Assignment A :=
  fun i x => σ (.inr i) x

/-- The gate bit of an assignment of the combined block. -/
def StratGate (σ : (stratBlock B₁ B₂).Assignment A) : Prop :=
  σ (.inl (.inr ())) Fin.elim0

/-- The first-stratum part is the pullback along the block inclusion. -/
private theorem strat1Assign_eq_homAssign (σ : (stratBlock B₁ B₂).Assignment A) :
    B₁.homAssign (B' := stratBlock B₁ B₂) (fun i => .inl (.inl i)) (fun _ => rfl)
      σ = strat1Assign σ :=
  rfl

end Parts

/-- The vocabulary morphism reading the first stratum inside the combined
block. -/
def strat1LHom (L : Language.{0, 0}) (B₁ B₂ : SOBlock) :
    L.sum B₁.lang →ᴸ L.sum (stratBlock B₁ B₂).lang :=
  LHom.sumMap (LHom.id L)
    (SOBlock.homLHom (B := B₁) (B' := stratBlock B₁ B₂)
      (fun i => .inl (.inl i)) (fun _ => rfl))

/-- The vocabulary morphism reading the doubly expanded vocabulary inside the
combined block. -/
def strat2LHom (L : Language.{0, 0}) (B₁ B₂ : SOBlock) :
    (L.sum B₁.lang).sum B₂.lang →ᴸ L.sum (stratBlock B₁ B₂).lang where
  onFunction := fun {_} f =>
    match f with
    | .inl (.inl g) => .inl g
    | .inl (.inr g) => isEmptyElim g
    | .inr g => isEmptyElim g
  onRelation := fun {_} r =>
    match r with
    | .inl (.inl s) => .inl s
    | .inl (.inr s) => .inr ⟨.inl (.inl s.1), s.2⟩
    | .inr s => .inr ⟨.inr s.1, s.2⟩

section Realize

variable {B₁ B₂ : SOBlock} {A : Type} [L.Structure A]

/-- Reading the first stratum inside the combined block: realization against
the combined assignment is realization against its first-stratum part. -/
private theorem realize_strat1Formula {α : Type} (σ : (stratBlock B₁ B₂).Assignment A)
    (φ : (L.sum B₁.lang).Formula α) (v : α → A) :
    (@Formula.Realize _ A ((stratBlock B₁ B₂).structure₁ (L := L) σ) _
      ((strat1LHom L B₁ B₂).onFormula φ) v) ↔
      @Formula.Realize _ A (B₁.structure₁ (L := L) (strat1Assign σ)) _ φ v := by
  have h := SOBlock.realize_homFormula (B := B₁) (B' := stratBlock B₁ B₂)
    (fun i => .inl (.inl i)) (fun _ => rfl) (L := L) (A := A) σ φ v
  rwa [strat1Assign_eq_homAssign] at h

/-- The combined structure is an expansion of the doubly expanded structure
along `DescriptiveComplexity.strat2LHom`. -/
theorem strat2LHom_isExpansionOn (σ : (stratBlock B₁ B₂).Assignment A) :
    @LHom.IsExpansionOn _ _ (strat2LHom L B₁ B₂) A
      (@SOBlock.structure₁ (L.sum B₁.lang) B₂ A
        (B₁.structure₁ (L := L) (strat1Assign σ)) (strat2Assign σ))
      ((stratBlock B₁ B₂).structure₁ (L := L) σ) := by
  let := B₁.structure₁ (L := L) (strat1Assign σ)
  let := @SOBlock.structure₁ (L.sum B₁.lang) B₂ A _ (strat2Assign σ)
  let := (stratBlock B₁ B₂).structure₁ (L := L) σ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · rcases f with (g | g) | g
    · rfl
    · exact isEmptyElim g
    · exact isEmptyElim g
  · rcases r with (s | s) | s
    · rfl
    · rfl
    · rfl

/-- Reading the second stratum inside the combined block: realization against
the combined assignment is realization over the structure expanded first by
the first-stratum part, then by the second. -/
private theorem realize_strat2Formula {α : Type} (σ : (stratBlock B₁ B₂).Assignment A)
    (φ : ((L.sum B₁.lang).sum B₂.lang).Formula α) (v : α → A) :
    (@Formula.Realize _ A ((stratBlock B₁ B₂).structure₁ (L := L) σ) _
      ((strat2LHom L B₁ B₂).onFormula φ) v) ↔
      @Formula.Realize _ A (@SOBlock.structure₁ (L.sum B₁.lang) B₂ A
        (B₁.structure₁ (L := L) (strat1Assign σ)) (strat2Assign σ)) _ φ v := by
  let := B₁.structure₁ (L := L) (strat1Assign σ)
  let := @SOBlock.structure₁ (L.sum B₁.lang) B₂ A _ (strat2Assign σ)
  let := (stratBlock B₁ B₂).structure₁ (L := L) σ
  have := strat2LHom_isExpansionOn (L := L) σ
  exact LHom.realize_onFormula (φ := strat2LHom L B₁ B₂) φ

/-- Realization of the gate atom: the gate bit of the assignment, whatever
the valuation. -/
private theorem realize_gateAtom {B₁ B₂ : SOBlock} (σ : (stratBlock B₁ B₂).Assignment A)
    {α : Type} (v : α → A) :
    (@Formula.Realize _ A ((stratBlock B₁ B₂).structure₁ (L := L) σ) _
      (Relations.formula (stratGateSym L B₁ B₂) Fin.elim0) v) ↔ StratGate σ := by
  let := (stratBlock B₁ B₂).structure₁ (L := L) σ
  rw [Formula.realize_rel]
  exact iff_of_eq (congrArg (σ (.inl (.inr ()))) (funext fun j => j.elim0))

end Realize

/-! ### The gate formula -/

/-- The gate formula: every step formula of the first stratum is absorbed by
the current stage – the first stratum has converged. -/
noncomputable def stratGateF (d₁ : StepDef L) (B₂ : SOBlock) :
    (L.sum (stratBlock d₁.B B₂).lang).Formula (Fin 0) :=
  letI := Fintype.ofFinite d₁.B.ι
  Formula.iInf fun i : d₁.B.ι =>
    Formula.iAlls (Fin (d₁.B.arity i))
      ((((strat1LHom L d₁.B B₂).onFormula (d₁.step i)).relabel
          (Sum.inr : Fin (d₁.B.arity i) → Fin 0 ⊕ Fin (d₁.B.arity i))) ⟹
        Relations.formula (strat1Sym L d₁.B B₂ i)
          fun j => Term.var (Sum.inr j))

/-- Realization of the gate formula: the first-stratum part absorbs one more
application of the first stratum's steps. -/
private theorem realize_stratGateF {B₂ : SOBlock} {A : Type} [L.Structure A]
    (d₁ : StepDef L) (σ : (stratBlock d₁.B B₂).Assignment A) (v : Fin 0 → A) :
    (@Formula.Realize _ A ((stratBlock d₁.B B₂).structure₁ (L := L) σ) _
      (stratGateF d₁ B₂) v) ↔
      ∀ (i : d₁.B.ι) (x : Fin (d₁.B.arity i) → A),
        d₁.next (strat1Assign σ) i x → strat1Assign σ i x := by
  let := Fintype.ofFinite d₁.B.ι
  let := (stratBlock d₁.B B₂).structure₁ (L := L) σ
  rw [stratGateF, Formula.realize_iInf]
  refine forall_congr' fun i => ?_
  rw [Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_imp, Formula.realize_relabel, Formula.realize_rel]
  constructor
  · intro h hx
    have hstep : @Formula.Realize _ A
        ((stratBlock d₁.B B₂).structure₁ (L := L) σ) _
        ((strat1LHom L d₁.B B₂).onFormula (d₁.step i)) x := by
      rw [realize_strat1Formula]
      exact hx
    have h' := h (by
      refine iff_of_eq (congrArg _ ?_) |>.mpr hstep
      funext j
      rfl)
    refine iff_of_eq (congrArg (σ (.inl (.inl i))) ?_) |>.mp h'
    funext j
    rfl
  · intro h hx
    have hx' : @Formula.Realize _ A
        ((stratBlock d₁.B B₂).structure₁ (L := L) σ) _
        ((strat1LHom L d₁.B B₂).onFormula (d₁.step i)) x := by
      refine iff_of_eq (congrArg _ ?_) |>.mp hx
      funext j
      rfl
    rw [realize_strat1Formula] at hx'
    refine iff_of_eq (congrArg (σ (.inl (.inl i))) ?_) |>.mpr (h hx')
    funext j
    rfl

/-! ### The stratified induction -/

namespace StepDef

variable (d₁ : StepDef L) (d₂ : StepDef (L.sum d₁.B.lang))

/-- **The stratified induction**: run the first stratum; once its steps add
nothing (the gate), run the second stratum over the frozen first. -/
noncomputable def stratify : StepDef L where
  B := stratBlock d₁.B d₂.B
  step := fun i =>
    match i with
    | .inl (.inl i) => (strat1LHom L d₁.B d₂.B).onFormula (d₁.step i)
    | .inl (.inr _) => stratGateF d₁ d₂.B
    | .inr i =>
        Relations.formula (stratGateSym L d₁.B d₂.B) Fin.elim0 ⊓
          (strat2LHom L d₁.B d₂.B).onFormula (d₂.step i)
  out := (strat2LHom L d₁.B d₂.B).onSentence d₂.out

variable {A : Type} [L.Structure A]

/-- A step is absorbed by its current stage exactly when the stage is an
inflationary fixed point. -/
private theorem isFixedPt_inflStep_iff (d : StepDef L) (ρ : d.B.Assignment A) :
    IsFixedPt d.inflStep ρ ↔ ∀ i x, d.next ρ i x → ρ i x := by
  constructor
  · intro h i x hx
    have := congrFun (congrFun h i) x
    exact (iff_of_eq this).mp (Or.inr hx)
  · intro h
    funext i x
    exact propext ⟨fun hor => hor.elim (fun h' => h') (h i x), Or.inl⟩

/-- The first-stratum part of the stratified stages is the first stratum's
own stages. -/
private theorem strat1Assign_inflStage (n : ℕ) :
    strat1Assign ((d₁.stratify d₂).inflStage A n) = d₁.inflStage A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i x
    rw [(d₁.stratify d₂).inflStage_succ, d₁.inflStage_succ]
    refine propext (or_congr (iff_of_eq (congrFun (congrFun ih i) x)) ?_)
    have h1 : (d₁.stratify d₂).next ((d₁.stratify d₂).inflStage A n)
        (.inl (.inl i)) x ↔
        d₁.next (strat1Assign ((d₁.stratify d₂).inflStage A n)) i x :=
      realize_strat1Formula ((d₁.stratify d₂).inflStage A n) (d₁.step i) x
    rw [ih] at h1
    exact h1

/-- The gate of the stratified stages: false at the start, and derived
exactly when the first stratum's current stage is an inflationary fixed
point. -/
private theorem stratGate_inflStage_succ (n : ℕ) :
    StratGate ((d₁.stratify d₂).inflStage A (n + 1)) ↔
      (StratGate ((d₁.stratify d₂).inflStage A n) ∨
        IsFixedPt d₁.inflStep (d₁.inflStage A n)) := by
  have hsucc : StratGate ((d₁.stratify d₂).inflStage A (n + 1)) ↔
      (StratGate ((d₁.stratify d₂).inflStage A n) ∨
        (d₁.stratify d₂).next ((d₁.stratify d₂).inflStage A n)
          (.inl (.inr ())) Fin.elim0) :=
    iff_of_eq (congrFun (congrFun ((d₁.stratify d₂).inflStage_succ (A := A) n)
      (.inl (.inr ()))) Fin.elim0)
  rw [hsucc]
  refine or_congr Iff.rfl ?_
  have h2 : (d₁.stratify d₂).next ((d₁.stratify d₂).inflStage A n)
      (.inl (.inr ())) Fin.elim0 ↔
      ∀ i x, d₁.next (strat1Assign ((d₁.stratify d₂).inflStage A n)) i x →
        strat1Assign ((d₁.stratify d₂).inflStage A n) i x :=
    realize_stratGateF d₁ ((d₁.stratify d₂).inflStage A n) Fin.elim0
  rw [d₁.strat1Assign_inflStage d₂] at h2
  exact h2.trans (d₁.isFixedPt_inflStep_iff (d₁.inflStage A n)).symm

/-- The gate only ever turns on. -/
private theorem stratGate_mono {m n : ℕ} (hmn : m ≤ n)
    (h : StratGate ((d₁.stratify d₂).inflStage A m)) :
    StratGate ((d₁.stratify d₂).inflStage A n) := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact (d₁.stratGate_inflStage_succ d₂ n).mpr
        (Or.inl (ih (Nat.lt_succ_iff.mp hlt)))
    · rwa [heq] at h

/-- While the gate is on, the first stratum sits at an inflationary fixed
point. -/
private theorem isFixedPt_of_stratGate {n : ℕ}
    (h : StratGate ((d₁.stratify d₂).inflStage A n)) :
    IsFixedPt d₁.inflStep (d₁.inflStage A n) := by
  induction n with
  | zero => exact absurd h (fun h => h)
  | succ n ih =>
    have hstep : d₁.inflStage A (n + 1) = d₁.inflStage A n → _ := fun heq =>
      heq ▸ ih
    rcases (d₁.stratGate_inflStage_succ d₂ n).mp h with hg | hfix
    · have hfix := ih hg
      have heq : d₁.inflStage A (n + 1) = d₁.inflStage A n := by
        rw [d₁.inflStage_succ]
        exact hfix
      rw [heq]
      exact hfix
    · have heq : d₁.inflStage A (n + 1) = d₁.inflStage A n := by
        rw [d₁.inflStage_succ]
        exact hfix
      rw [heq]
      exact hfix

/-- While the gate is on, the first stratum sits at its limit. -/
private theorem inflStage_eq_limit_of_stratGate {n m : ℕ} (hnm : n ≤ m)
    (h : StratGate ((d₁.stratify d₂).inflStage A n)) :
    d₁.inflStage A m = d₁.inflLimit A := by
  have hfix := d₁.isFixedPt_of_stratGate d₂ h
  have hm : d₁.inflStage A m = d₁.inflStage A n :=
    iterate_eq_of_isFixedPt hfix hnm
  funext i x
  rw [hm]
  refine propext ⟨fun hx => ⟨n, hx⟩, ?_⟩
  rintro ⟨p, hp⟩
  rcases le_total p n with hpn | hpn
  · exact d₁.inflStage_le_of_le hpn i x hp
  · have hpeq : d₁.inflStage A p = d₁.inflStage A n :=
      iterate_eq_of_isFixedPt hfix hpn
    rw [← hpeq]
    exact hp

/-- One step of the second stratum, decomposed: the gate at the current
stage, and the second stratum's own step over the frozen strata. -/
private theorem next_stratify_inr (σ : (stratBlock d₁.B d₂.B).Assignment A) (i : d₂.B.ι)
    (x : Fin (d₂.B.arity i) → A) :
    (d₁.stratify d₂).next σ (.inr i) x ↔
      (StratGate σ ∧
        @Formula.Realize _ A (@SOBlock.structure₁ (L.sum d₁.B.lang) d₂.B A
          (d₁.B.structure₁ (L := L) (strat1Assign σ)) (strat2Assign σ)) _
          (d₂.step i) x) := by
  have h0 : (@Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
      (Relations.formula (stratGateSym L d₁.B d₂.B) Fin.elim0 ⊓
        (strat2LHom L d₁.B d₂.B).onFormula (d₂.step i)) x) ↔
      (@Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
        (Relations.formula (stratGateSym L d₁.B d₂.B) Fin.elim0) x ∧
        @Formula.Realize _ A ((stratBlock d₁.B d₂.B).structure₁ (L := L) σ) _
          ((strat2LHom L d₁.B d₂.B).onFormula (d₂.step i)) x) :=
    letI := (stratBlock d₁.B d₂.B).structure₁ (L := L) σ
    Formula.realize_inf
  exact h0.trans (and_congr (realize_gateAtom σ x)
    (realize_strat2Formula σ (d₂.step i) x))

/-- While the gate is off, the second stratum does not move. -/
private theorem strat2Assign_inflStage_succ_of_not_stratGate {n : ℕ}
    (h : ¬StratGate ((d₁.stratify d₂).inflStage A n)) :
    strat2Assign ((d₁.stratify d₂).inflStage A (n + 1)) =
      strat2Assign ((d₁.stratify d₂).inflStage A n) := by
  funext i x
  have hsucc : strat2Assign ((d₁.stratify d₂).inflStage A (n + 1)) i x ↔
      (strat2Assign ((d₁.stratify d₂).inflStage A n) i x ∨
        (d₁.stratify d₂).next ((d₁.stratify d₂).inflStage A n) (.inr i) x) :=
    iff_of_eq (congrFun (congrFun ((d₁.stratify d₂).inflStage_succ (A := A) n)
      (.inr i)) x)
  refine propext (hsucc.trans ⟨fun hx => ?_, Or.inl⟩)
  rcases hx with hx' | hx'
  · exact hx'
  · exact absurd ((d₁.next_stratify_inr d₂ _ i x).mp hx').1 h

/-- While the gate is off, the second stratum is empty. -/
private theorem strat2Assign_eq_bot_of_not_stratGate {n : ℕ}
    (h : ¬StratGate ((d₁.stratify d₂).inflStage A n)) :
    strat2Assign ((d₁.stratify d₂).inflStage A n) = d₂.B.botAssign A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hgn : ¬StratGate ((d₁.stratify d₂).inflStage A n) := fun hg =>
      h (d₁.stratGate_mono d₂ (Nat.le_succ n) hg)
    rw [d₁.strat2Assign_inflStage_succ_of_not_stratGate d₂ hgn]
    exact ih hgn

/-- **The second stratum replays its own stages** once the gate fires: from
the first gate-on stage, the second-stratum parts are the stages of the
second stratum over the structure expanded by the first stratum's limit. -/
theorem strat2Assign_inflStage_add {G : ℕ}
    (hG : StratGate ((d₁.stratify d₂).inflStage A G))
    (hGmin : ∀ m < G, ¬StratGate ((d₁.stratify d₂).inflStage A m)) (m : ℕ) :
    strat2Assign ((d₁.stratify d₂).inflStage A (G + m)) =
      @StepDef.inflStage (L.sum d₁.B.lang) d₂ A
        (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) m := by
  induction m with
  | zero =>
    cases G with
    | zero => exact absurd hG fun h => h
    | succ G' =>
      rw [Nat.add_zero, d₁.strat2Assign_inflStage_succ_of_not_stratGate d₂
        (hGmin G' (Nat.lt_succ_self G'))]
      exact d₁.strat2Assign_eq_bot_of_not_stratGate d₂ (hGmin G' (Nat.lt_succ_self G'))
  | succ m ih =>
    funext i x
    have hgate : StratGate ((d₁.stratify d₂).inflStage A (G + m)) :=
      d₁.stratGate_mono d₂ (Nat.le_add_right G m) hG
    have hsucc : strat2Assign ((d₁.stratify d₂).inflStage A (G + m + 1)) i x ↔
        (strat2Assign ((d₁.stratify d₂).inflStage A (G + m)) i x ∨
          (d₁.stratify d₂).next ((d₁.stratify d₂).inflStage A (G + m)) (.inr i) x) :=
      iff_of_eq (congrFun (congrFun
        ((d₁.stratify d₂).inflStage_succ (A := A) (G + m)) (.inr i)) x)
    have hnext := d₁.next_stratify_inr d₂ ((d₁.stratify d₂).inflStage A (G + m)) i x
    have hlim1 : strat1Assign ((d₁.stratify d₂).inflStage A (G + m)) =
        d₁.inflLimit A := by
      rw [d₁.strat1Assign_inflStage d₂]
      exact d₁.inflStage_eq_limit_of_stratGate d₂ (Nat.le_add_right G m) hG
    rw [hlim1, ih, and_iff_right hgate] at hnext
    have hτ : @StepDef.inflStage (L.sum d₁.B.lang) d₂ A
        (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) (m + 1) i x ↔
        (@StepDef.inflStage (L.sum d₁.B.lang) d₂ A
          (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) m i x ∨
          @StepDef.next (L.sum d₁.B.lang) d₂ A
            (d₁.B.structure₁ (L := L) (d₁.inflLimit A))
            (@StepDef.inflStage (L.sum d₁.B.lang) d₂ A
              (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) m) i x) :=
      iff_of_eq (congrFun (congrFun
        (@StepDef.inflStage_succ (L.sum d₁.B.lang) d₂ A
          (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) m) i) x)
    refine propext (hsucc.trans (Iff.trans ?_ hτ.symm))
    exact or_congr (iff_of_eq (congrFun (congrFun ih i) x)) hnext

/-- The second-stratum part of the composite limit is the second stratum's
own limit over the structure expanded by the first stratum's limit. -/
theorem strat2Assign_inflLimit [Finite A] :
    strat2Assign ((d₁.stratify d₂).inflLimit A) =
      @StepDef.inflLimit (L.sum d₁.B.lang) d₂ A
        (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) := by
  classical
  have hEx : ∃ n, StratGate ((d₁.stratify d₂).inflStage A n) :=
    ⟨Nat.card (BAtom d₁.B A) + 1,
      (d₁.stratGate_inflStage_succ d₂ (Nat.card (BAtom d₁.B A))).mpr
        (Or.inr (d₁.isFixedPt_inflStep_card A))⟩
  set G := sInf {n | StratGate ((d₁.stratify d₂).inflStage A n)} with hGdef
  have hG : StratGate ((d₁.stratify d₂).inflStage A G) := Nat.sInf_mem hEx
  have hGmin : ∀ m < G, ¬StratGate ((d₁.stratify d₂).inflStage A m) :=
    fun m hm hmem => absurd (Nat.sInf_le hmem) (Nat.not_le_of_lt hm)
  funext i x
  refine propext ⟨?_, ?_⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmono : strat2Assign ((d₁.stratify d₂).inflStage A (G + n)) i x := by
      have := (d₁.stratify d₂).inflStage_le_of_le (Nat.le_add_left n G) (.inr i) x hn
      exact this
    have := congrFun (congrFun (d₁.strat2Assign_inflStage_add d₂ hG hGmin n) i) x
    exact (iff_of_eq this).mp hmono
  · rintro ⟨m, hm⟩
    refine ⟨G + m, ?_⟩
    have := congrFun (congrFun (d₁.strat2Assign_inflStage_add d₂ hG hGmin m) i) x
    exact (iff_of_eq this).mpr hm

/-- The first-stratum part of the composite limit is the first stratum's own
limit. -/
theorem strat1Assign_inflLimit :
    strat1Assign ((d₁.stratify d₂).inflLimit A) = d₁.inflLimit A := by
  funext i x
  refine propext (exists_congr fun n => ?_)
  exact iff_of_eq (congrFun (congrFun (d₁.strat1Assign_inflStage d₂ n) i) x)

/-- **Stratification**: the value of the stratified induction is the value of
the second stratum, read over the structure expanded by the first stratum's
limit. Nested inflationary inductions are one induction. -/
theorem ifpHolds_stratify [Finite A] :
    (d₁.stratify d₂).IFPHolds A ↔
      @StepDef.IFPHolds (L.sum d₁.B.lang) d₂ A
        (d₁.B.structure₁ (L := L) (d₁.inflLimit A)) := by
  have hout : (d₁.stratify d₂).IFPHolds A ↔
      @Formula.Realize _ A (@SOBlock.structure₁ (L.sum d₁.B.lang) d₂.B A
        (d₁.B.structure₁ (L := L)
          (strat1Assign ((d₁.stratify d₂).inflLimit A)))
        (strat2Assign ((d₁.stratify d₂).inflLimit A))) _ d₂.out
        (default : Empty → A) :=
    realize_strat2Formula ((d₁.stratify d₂).inflLimit A) d₂.out default
  rw [d₁.strat1Assign_inflLimit d₂, d₁.strat2Assign_inflLimit d₂] at hout
  exact hout

end StepDef

end DescriptiveComplexity
