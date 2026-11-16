/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Full.Closure.Automata
public import LeanPool.DeciSigma1.Full.Models.Pinning
public import LeanPool.DeciSigma1.Semantics.Classes
public import LeanPool.DeciSigma1.Semantics.FiniteMedian
import Mathlib.Basic.Finite.Prod

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Finite solutions that keep finitely many observations

An observation of a signed configuration is equivalent to a ground bound in the order with
variance. Finitely many ground bounds that hold together in some solution hold together in a
finite solution whenever the constraint has one: the bounds are placed on both signed copies and
realized by a finite solution of the signed translation, which is then symmetrized with a median.
Finite satisfiability is decided by testing the signed translation for label and cycle clashes.

## Main declarations

- `Signed.Observation.bound`, `Signed.observation_bound`: observations of signed configurations as
  ground bounds.
- `Signed.BoundRealization`: realization of ground bounds in a class of trees.
- `Signed.boundRealization_finiteTop`: realization by finite solutions.
- `Signed.satFin_iff_not_clash`, `Signed.decideSatFin`: finite satisfiability with variance.
-/

@[expose] public section


namespace DeciSigma1.Full.Models.Signed.FinitePinning
open DeciSigma1.Semantics
open DeciSigma1.Constraints

variable {n : ℕ} {V : Type*}

theorem sat_normalize_iff (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (Γ : List (LitT n V)) :
    SatT (fun _ => false) (normalized c ρ) (signed c Γ) ↔ SatT c ρ Γ :=
  (sat_false ..).trans (sat_iff_signed c ρ Γ).symm

theorem sat_signDual {c : Fin n → Bool} {A : V × Bool → Semantics.Tree n}
    {Γ : List (LitT n V)} (h : SatT (fun _ => false) A (signed c Γ)) :
    SatT (fun _ => false) (Constraints.Signed.dual A) (signed c Γ) :=
  (sat_false ..).mpr (sat_signedDual c ((sat_false ..).mp h))

theorem sat_decode (c : Fin n → Bool) {A : V × Bool → Semantics.Tree n}
    {Γ : List (LitT n V)} (h : SatT (fun _ => false) A (signed c Γ))
    (hf : Constraints.Signed.dual A = A) : SatT c (decoded c A) Γ := by
  apply (sat_normalize_iff c _ Γ).mp
  rwa [normalized_decoded c hf]

/-- The median of three covariant solutions of a flat constraint is a covariant solution. -/
theorem sat_median {A B D : V → Semantics.Tree n} {Γ : List (LitT n V)}
    (ha : SatT (fun _ => false) A Γ) (hb : SatT (fun _ => false) B Γ)
    (hd : SatT (fun _ => false) D Γ) :
    SatT (fun _ => false) (fun v => treeMedian (A v) (B v) (D v)) Γ := by
  intro l hl
  have h₁ := ha l hl
  have h₂ := hb l hl
  have h₃ := hd l hl
  cases l with
  | le u v =>
    simp only [HoldsT, treeLe_false_iff_le] at *
    exact treeMedian_mono h₁ h₂ h₃
  | fLe a u =>
    simp only [HoldsT, treeLe_false_iff_le] at *
    have hh := treeMedian_mono h₁ h₂ h₃
    simpa only [treeMedian_node, Function.comp_def] using hh
  | leF u a =>
    simp only [HoldsT, treeLe_false_iff_le] at *
    have hh := treeMedian_mono h₁ h₂ h₃
    simpa only [treeMedian_node, Function.comp_def] using hh
  | eqBot u =>
    change treeMedian (A u) (B u) (D u) = Tree.bot
    change A u = Tree.bot at h₁
    change B u = Tree.bot at h₂
    simp [h₁, h₂]
  | eqTop u =>
    change treeMedian (A u) (B u) (D u) = Tree.top
    change A u = Tree.top at h₁
    change B u = Tree.top at h₂
    simp [h₁, h₂]

/-- The finite symmetrization of a finite signed assignment, with a finite third input `D`. -/
def symmetrize (c : Fin n → Bool) (A : V × Bool → FTree n)
    (D : V → FTree n) (z : V × Bool) : FTree n :=
  FiniteMedian.median (A z) ((A (z.1, !z.2)).dual)
      ((D z.1).normalize c z.2)

@[simp] theorem symmetrize_toTree (c : Fin n → Bool) (A : V × Bool → FTree n)
    (D : V → FTree n) (z : V × Bool) :
    (symmetrize c A D z).toTree =
      treeMedian (A z).toTree (Constraints.Signed.dual (FTree.toTree ∘ A) z)
        (normalized c (FTree.toTree ∘ D) z) := by
  simp [symmetrize, Constraints.Signed.dual, normalized]

theorem symmetrize_fixed (c : Fin n → Bool) (A : V × Bool → FTree n)
    (D : V → FTree n) :
    Constraints.Signed.dual (FTree.toTree ∘ symmetrize c A D) =
      FTree.toTree ∘ symmetrize c A D := by
  funext ⟨v, s⟩
  simp only [Constraints.Signed.dual, signedVar, base, sign, Function.comp_apply,
    symmetrize_toTree, normalized,
    dual_treeMedian, dual_involutive, Bool.not_not, normalize_not]
  rw [treeMedian_swap]

theorem symmetrize_sat {c : Fin n → Bool} {A : V × Bool → FTree n}
    {D : V → FTree n} {Γ : List (LitT n V)}
    (ha : SatT (fun _ => false) (FTree.toTree ∘ A) (signed c Γ))
    (hd : SatT c (FTree.toTree ∘ D) Γ) :
    SatT (fun _ => false) (FTree.toTree ∘ symmetrize c A D) (signed c Γ) := by
  have hh := sat_median ha (sat_signDual ha) ((sat_normalize_iff c _ Γ).mpr hd)
  simpa only [Function.comp_def, symmetrize_toTree] using hh

end DeciSigma1.Full.Models.Signed.FinitePinning

namespace DeciSigma1.Full.Models
open DeciSigma1.Semantics

variable {n : ℕ}

/-- Truth of a ground bound in the order with variance `c`. -/
def GroundBound.HoldsWithVariance {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (b : GroundBound n V) : Prop :=
  if b.lower then Tree.Le c b.tree.toTree (ρ b.var)
  else Tree.Le c (ρ b.var) b.tree.toTree

end DeciSigma1.Full.Models

namespace DeciSigma1.Full.Models.Signed

open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints

variable {n : ℕ}

namespace FinitePinning
variable {V : Type*}

/-- The bound on the copy of sign `s`: the negative copy carries the dual bound. -/
def pin (c : Fin n → Bool) (b : GroundBound n V) (s : Bool) : GroundBound n (V × Bool) :=
  ⟨(b.var, s), Bool.xor b.lower s, b.tree.normalize c s⟩

/-- The bounds on both signed copies. -/
def pins (c : Fin n → Bool) (B : List (GroundBound n V)) : List (GroundBound n (V × Bool)) :=
  B.flatMap fun b => [pin c b false, pin c b true]

theorem pins_iff (c : Fin n → Bool) (B : List (GroundBound n V))
    (A : V × Bool → Semantics.Tree n) :
    (∀ p ∈ pins c B, p.Holds A) ↔ ∀ b ∈ B, ∀ s, (pin c b s).Holds A := by
  constructor
  · intro h b hb s
    apply h
    apply List.mem_flatMap.mpr
    exact ⟨b, hb, by cases s <;> simp⟩
  · intro h p hp
    obtain ⟨b, hb, hp⟩ := List.mem_flatMap.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h b hb false
    · exact h b hb true

theorem pin_normalize_iff (c : Fin n → Bool) (b : GroundBound n V) (s : Bool)
    (ρ : V → Semantics.Tree n) :
    (pin c b s).Holds (normalized c ρ) ↔ b.HoldsWithVariance c ρ := by
  obtain ⟨v, lower, g⟩ := b
  cases lower <;> cases s <;>
    simp [pin, GroundBound.Holds, GroundBound.HoldsWithVariance, normalized, treeLe_iff_normalize]

theorem pins_normalize_iff (c : Fin n → Bool) (B : List (GroundBound n V))
    (ρ : V → Semantics.Tree n) :
    (∀ p ∈ pins c B, p.Holds (normalized c ρ)) ↔ ∀ b ∈ B, b.HoldsWithVariance c ρ := by
  simp only [pins_iff, pin_normalize_iff, forall_const]

/-- The sign dual of `A` satisfies the bound on the copy of sign `s` exactly when `A` satisfies the
bound on the copy of sign `!s`. -/
theorem pin_signDual_iff (c : Fin n → Bool) (b : GroundBound n V) (s : Bool)
    (A : V × Bool → Semantics.Tree n) :
    (pin c b s).Holds (Constraints.Signed.dual A) ↔ (pin c b (!s)).Holds A := by
  obtain ⟨v, lower, g⟩ := b
  cases lower <;> cases s <;>
    simp only [pin, GroundBound.Holds, FTree.toTree_normalize, Constraints.Signed.dual,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true, normalize_true]
  all_goals exact (dual_le_iff _ _).symm.trans (by simp)

theorem pins_signDual {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → Semantics.Tree n} (h : ∀ p ∈ pins c B, p.Holds A) :
    ∀ p ∈ pins c B, p.Holds (Constraints.Signed.dual A) := by
  rw [pins_iff] at h ⊢
  intro b hb s
  exact (pin_signDual_iff c b s A).mpr (h b hb (!s))

/-- If two assignments satisfy a ground bound, so does their median with any third assignment. -/
theorem bound_median (b : GroundBound n V) {A A' D : V → Semantics.Tree n}
    (ha : b.Holds A) (hb : b.Holds A') :
    b.Holds (fun v => treeMedian (A v) (A' v) (D v)) := by
  obtain ⟨v, lower, g⟩ := b
  cases lower with
  | false =>
    change A v ≤ g.toTree at ha
    change A' v ≤ g.toTree at hb
    change treeMedian (A v) (A' v) (D v) ≤ g.toTree
    simpa using treeMedian_mono ha hb (le_refl (D v))
  | true =>
    change g.toTree ≤ A v at ha
    change g.toTree ≤ A' v at hb
    change g.toTree ≤ treeMedian (A v) (A' v) (D v)
    simpa using treeMedian_mono ha hb (le_refl (D v))

theorem symmetrize_pins {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → FTree n} (D : V → FTree n)
    (h : ∀ p ∈ pins c B, p.Holds (FTree.toTree ∘ A)) :
    ∀ p ∈ pins c B, p.Holds (FTree.toTree ∘ symmetrize c A D) := by
  intro p hp
  have hh := bound_median (D := normalized c (FTree.toTree ∘ D)) p
    (h p hp) (pins_signDual h p hp)
  simpa only [Function.comp_def, symmetrize_toTree] using hh

theorem pins_decode {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → Semantics.Tree n} (hf : Constraints.Signed.dual A = A)
    (h : ∀ p ∈ pins c B, p.Holds A) : ∀ b ∈ B, b.HoldsWithVariance c (decoded c A) := by
  apply (pins_normalize_iff c B _).mp
  rwa [normalized_decoded c hf]

end FinitePinning

/-- Finitely many ground bounds that hold together in some solution with variance hold together in a
finite solution, provided the constraint has a finite solution. -/
theorem realize_finite_bounds {V : Type*} (c : Fin n → Bool)
    (Γ : List (LitT n V))
    (hf : ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT c τ Γ)
    (B : List (GroundBound n V))
    (hs : ∃ ρ, SatT c ρ Γ ∧ ∀ b ∈ B, b.HoldsWithVariance c ρ) :
    ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT c τ Γ ∧ ∀ b ∈ B, b.HoldsWithVariance c τ := by
  classical
  obtain ⟨δ, hδfin, hδ⟩ := hf
  choose D hD using hδfin
  have hDeq : FTree.toTree ∘ D = δ := funext hD
  have hf' : SatisfiableIn FiniteTop (fun _ => false) (Constraints.signed c Γ) := by
    refine ⟨Constraints.normalized c δ, ?_,
      (FinitePinning.sat_normalize_iff c δ Γ).mpr hδ⟩
    intro z
    exact ⟨(D z.1).normalize c z.2, by simp [Constraints.normalized, hD]⟩
  obtain ⟨ρ, hρ, hB⟩ := hs
  obtain ⟨β, hβfin, hβ, hβB⟩ := Models.finiteBoundPinning
    (Constraints.signed c Γ) hf' (FinitePinning.pins c B)
    ⟨Constraints.normalized c ρ, (FinitePinning.sat_normalize_iff c ρ Γ).mpr hρ,
      (FinitePinning.pins_normalize_iff c B ρ).mpr hB⟩
  choose A hA using hβfin
  have hAeq : FTree.toTree ∘ A = β := funext hA
  have hAsat : SatT (fun _ => false) (FTree.toTree ∘ A)
      (Constraints.signed c Γ) := hAeq.symm ▸ hβ
  have hApins : ∀ p ∈ FinitePinning.pins c B, p.Holds (FTree.toTree ∘ A) :=
    hAeq.symm ▸ hβB
  let M := FinitePinning.symmetrize c A D
  have hfixed := FinitePinning.symmetrize_fixed c A D
  refine ⟨Constraints.decoded c (FTree.toTree ∘ M), ?_, ?_, ?_⟩
  · intro v
    exact ⟨(M (v, false)).normalize c false, by simp [Constraints.decoded]⟩
  · exact FinitePinning.sat_decode c
      (FinitePinning.symmetrize_sat hAsat (hDeq.symm ▸ hδ)) hfixed
  · exact FinitePinning.pins_decode hfixed (FinitePinning.symmetrize_pins D hApins)

end DeciSigma1.Full.Models.Signed

namespace DeciSigma1.Full.Models.Signed
open DeciSigma1.Full.Closure DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints

variable {n : ℕ}

/-- An observation of a signed configuration: asserted (`true`) or denied (`false`). -/
abbrev Observation (n : ℕ) (V : Type*) := Closure.Config n V × Bool

/-- Truth of an observation of a signed configuration for an assignment. -/
def Observation.Holds {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (o : Observation n V) : Prop :=
  if o.2 then o.1 ∈ configSet c ρ else o.1 ∉ configSet c ρ

/-- The same observation on the normalized assignment, in the covariant order. -/
def Observation.normalized {V : Type*} (o : Observation n V) : Models.Observation n V :=
  ⟨!o.1.2.1, o.1.1, o.1.2.2, !o.2⟩

theorem observation_normalized {V : Type*} (c : Fin n → Bool)
    (ρ : V → Semantics.Tree n) (o : Observation n V) :
    o.normalized.Holds (fun v => Tree.normalize c false (ρ v)) ↔ o.Holds c ρ := by
  obtain ⟨⟨v, s, w⟩, b⟩ := o
  cases s <;> cases b <;>
    simp only [Observation.normalized, Models.Observation.Holds, Observation.Holds,
      configSet, Set.mem_ofPred_eq, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true]
  · simpa only [leaf, Set.mem_ofPred_eq] using mem_nonBottomPrefixes_dual
      (Tree.normalize c false (ρ v)) w
  · simpa only [leaf, Set.mem_ofPred_eq, not_not] using
      (mem_nonBottomPrefixes_dual (Tree.normalize c false (ρ v)) w).not
  · simpa only [not_not] using (leaf_minus c (ρ v) w).not.symm
  · exact (leaf_minus c (ρ v) w).symm

/-- The ground bound equivalent to an observation of a signed configuration. -/
def Observation.bound {V : Type*} (c : Fin n → Bool) (o : Observation n V) :
    GroundBound n V :=
  let b := o.normalized.bound
  ⟨b.var, b.lower, b.tree.normalize c false⟩

/-- An observation of a signed configuration holds exactly when its ground bound holds in the
order with variance. -/
theorem observation_bound {V : Type*} (c : Fin n → Bool)
    (ρ : V → Semantics.Tree n) (o : Observation n V) :
    (o.bound c).HoldsWithVariance c ρ ↔ o.Holds c ρ := by
  rw [← observation_normalized, ← Models.observation_bound]
  simp only [Observation.bound, GroundBound.HoldsWithVariance, GroundBound.Holds,
    FTree.toTree_normalize, treeLe_iff_normalize, normalize_involutive]

/-- Any finitely many ground bounds that hold together in some solution of `Γ` also hold together
in a solution with values in `C`. -/
def BoundRealization {V : Type*} (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) : Prop :=
  ∀ B : List (GroundBound n V),
    (∃ ρ, SatT c ρ Γ ∧ ∀ b ∈ B, b.HoldsWithVariance c ρ) →
    ∃ τ, (∀ v, C (τ v)) ∧ SatT c τ Γ ∧ ∀ b ∈ B, b.HoldsWithVariance c τ

end DeciSigma1.Full.Models.Signed

namespace DeciSigma1.Full.Models.Signed
open DeciSigma1.Satisfiability DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints

variable {n : ℕ}

/-- A constraint with variance has a finite solution exactly when its signed translation has
neither a label clash nor a cycle clash. -/
theorem satFin_iff_not_clash {V : Type*} [Finite V]
    (c : Fin n → Bool) (Γ : List (LitT n V)) :
    SatFin c Γ ↔ ¬ LabelClash (signed c Γ) ∧ ¬ CycleClash (signed c Γ) :=
  (satFin_iff_finite_assignment c Γ).trans ((satFinite_iff_signed c Γ).trans satFin_iff)

/-- Finite satisfiability with variance `c` is decidable: the signed translation is tested for
label and cycle clashes. -/
def decideSatFin {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin n → Bool) (Γ : List (LitT n V)) : Decidable (SatFin c Γ) :=
  decidable_of_iff (satFinB c Γ = true)
    ((satFinB_iff c Γ).trans (satFin_iff_finite_assignment c Γ).symm)

/-- For a constraint with a finite solution, finitely many ground bounds that hold together in
some solution hold together in a finite solution. -/
theorem boundRealization_finiteTop {V : Type*} (c : Fin n → Bool)
    (Γ : List (LitT n V)) (hf : SatFin c Γ) : BoundRealization FiniteTop c Γ :=
  realize_finite_bounds c Γ hf

end DeciSigma1.Full.Models.Signed
