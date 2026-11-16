/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Satisfiability.Decide
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Ranked extensions of flat constraints

A ranked extension adds to a constraint `Γ` fresh variables of two kinds, sources and sinks, and
constructor literals whose children are fresh variables of strictly greater rank than the bounded
variable: the children of a lower constructor literal are sources, those of an upper one are
sinks. It adds no variable inequality. The derived inequalities between original variables are
then those of `Γ`, and every cycle clash of the extension is a cycle clash of `Γ`. Hence a
satisfiable ranked extension has a finite solution whenever `Γ` has one.

## Main declarations

- `lift`: a constraint over an enlarged type of variables.
- `Ranked.Extension`: ranked extensions.
- `Ranked.Extension.cycleClash_iff`: a ranked extension has a cycle clash exactly when the
  original constraint has one.
- `Ranked.Extension.satFin_iff`: finite satisfiability of ranked extensions.
-/

@[expose] public section


namespace DeciSigma1.Constraints

open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n k m : ℕ}

/-! ## Lifting constraints -/

/-- The constraint `Γ` over the variables `Fin (k + m)`, renamed along `Fin.castAdd m`. -/
def lift (Γ : List (LitT n (Fin k))) (m : ℕ) : List (LitT n (Fin (k + m))) :=
  Γ.map (LitT.map (Fin.castAdd m))

@[simp] theorem sat_lift (ρ' : Fin (k + m) → Semantics.Tree n) (Γ : List (LitT n (Fin k))) :
    Covariant.Sat ρ' (lift Γ m) ↔ Covariant.Sat (ρ' ∘ Fin.castAdd m) Γ :=
  sat_rename _ _ _

variable {V : Type*}

@[simp] theorem sat_append (ρ : V → Semantics.Tree n) (Γ ψ : List (LitT n V)) :
    Covariant.Sat ρ (Γ ++ ψ) ↔ Covariant.Sat ρ Γ ∧ Covariant.Sat ρ ψ := by
  simp only [Covariant.Sat, List.mem_append, or_imp, forall_and]

@[simp] theorem sat_cons (ρ : V → Semantics.Tree n) (l : LitT n V) (Γ : List (LitT n V)) :
    Covariant.Sat ρ (l :: Γ) ↔ Covariant.Holds ρ l ∧ Covariant.Sat ρ Γ := by
  simp [Covariant.Sat]

end DeciSigma1.Constraints

namespace DeciSigma1.Constraints

namespace Ranked

variable {n k m : ℕ}

/-- A ranked extension `ψ` of `Γ`: every variable is an original variable or lies in one of the
disjoint classes `Source` and `Sink` of fresh variables; `ψ` contains the literals of `Γ`; every
variable inequality of `ψ` is a literal of `Γ`; and every other lower (upper) constructor literal
of `ψ` has all children in `Source` (`Sink`), of strictly greater rank than its bound, and a bound
outside `Sink` (`Source`). -/
structure Extension (Γ : List (LitT n (Fin k))) (ψ : List (LitT n (Fin (k + m))))
    (Source Sink : Fin (k + m) → Prop) (rank : Fin (k + m) → ℕ) : Prop where
  source_not_original : ∀ {z}, Source z → ¬ z.val < k
  sink_not_original : ∀ {z}, Sink z → ¬ z.val < k
  source_not_sink : ∀ {z}, Source z → ¬ Sink z
  variable_cases : ∀ z, (∃ u : Fin k, z = Fin.castAdd m u) ∨ Source z ∨ Sink z
  original_mem : ∀ l ∈ Γ, l.map (Fin.castAdd m) ∈ ψ
  copy : ∀ a b, LitT.le a b ∈ ψ →
    ∃ a' b', LitT.le a' b' ∈ Γ ∧ a = Fin.castAdd m a' ∧ b = Fin.castAdd m b'
  lower : ∀ a c, LitT.fLe a c ∈ ψ →
    (∃ a' c', LitT.fLe a' c' ∈ Γ ∧ a = Fin.castAdd m ∘ a' ∧ c = Fin.castAdd m c') ∨
    ((∀ i, Source (a i) ∧ rank c < rank (a i)) ∧ ¬ Sink c)
  upper : ∀ c b, LitT.leF c b ∈ ψ →
    (∃ c' b', LitT.leF c' b' ∈ Γ ∧ c = Fin.castAdd m c' ∧ b = Fin.castAdd m ∘ b') ∨
    ((∀ i, Sink (b i) ∧ rank c < rank (b i)) ∧ ¬ Source c)

variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}

theorem Extension.not_source_original (e : Extension Γ ψ Source Sink rank) (u : Fin k) :
    ¬ Source (Fin.castAdd m u) := fun h => e.source_not_original h u.isLt

theorem Extension.not_sink_original (e : Extension Γ ψ Source Sink rank) (u : Fin k) :
    ¬ Sink (Fin.castAdd m u) := fun h => e.sink_not_original h u.isLt

theorem Extension.upper_children (e : Extension Γ ψ Source Sink rank)
    {c : Fin (k + m)} {b : Fin n → Fin (k + m)} (h : LitT.leF c b ∈ ψ) (i : Fin n) :
    ¬ Source (b i) := by
  rcases e.upper _ _ h with ⟨c', b', _, rfl, rfl⟩ | ⟨hb, _⟩
  · exact e.not_source_original (b' i)
  · exact e.source_not_sink.mt (not_not.mpr (hb i).1)

theorem Extension.lower_children (e : Extension Γ ψ Source Sink rank)
    {a : Fin n → Fin (k + m)} {c : Fin (k + m)} (h : LitT.fLe a c ∈ ψ) (i : Fin n) :
    ¬ Sink (a i) := by
  rcases e.lower _ _ h with ⟨a', c', _, rfl, rfl⟩ | ⟨ha, _⟩
  · exact e.not_sink_original (a' i)
  · exact e.source_not_sink (ha i).1

/-- A derivation that ends in a source is trivial. -/
theorem Extension.derives_into_source (e : Extension Γ ψ Source Sink rank)
    {a b : Fin (k + m)} (h : Derives ψ a b) (hb : Source b) : a = b := by
  induction h with
  | refl => rfl
  | lit hl =>
    obtain ⟨_, b, _, _, rfl⟩ := e.copy _ _ hl
    exact False.elim (e.not_source_original b hb)
  | trans _ _ ih ih' =>
    have he := ih' hb
    exact (ih (he ▸ hb)).trans he
  | decomp i _ _ hu => exact False.elim (e.upper_children hu i hb)

/-- A derivation that starts in a sink is trivial. -/
theorem Extension.derives_out_of_sink (e : Extension Γ ψ Source Sink rank)
    {a b : Fin (k + m)} (h : Derives ψ a b) (ha : Sink a) : b = a := by
  induction h with
  | refl => rfl
  | lit hl =>
    obtain ⟨a, _, _, rfl, _⟩ := e.copy _ _ hl
    exact False.elim (e.not_sink_original a ha)
  | trans _ _ ih ih' =>
    have he := ih ha
    exact (ih' (he ▸ ha)).trans he
  | decomp i hl _ _ => exact False.elim (e.lower_children hl i ha)

/-- A variable derivably between two original variables is itself original. -/
theorem Extension.middle_original (e : Extension Γ ψ Source Sink rank)
    {u v : Fin k} {w : Fin (k + m)}
    (hl : Derives ψ (Fin.castAdd m u) w)
    (hr : Derives ψ w (Fin.castAdd m v)) : ∃ t : Fin k, w = Fin.castAdd m t := by
  rcases e.variable_cases w with h | hs | ht
  · exact h
  · have he := e.derives_into_source hl hs
    exact False.elim (e.not_source_original u (he ▸ hs))
  · have he := e.derives_out_of_sink hr ht
    exact False.elim (e.not_sink_original v (he ▸ ht))

theorem Extension.derives_reflect (e : Extension Γ ψ Source Sink rank)
    {a b : Fin (k + m)} (h : Derives ψ a b) :
    ∀ u v : Fin k, a = Fin.castAdd m u → b = Fin.castAdd m v → Derives Γ u v := by
  induction h with
  | refl a =>
    intro u v hu hv
    have he : u = v := Fin.castAdd_injective _ _ (hu.symm.trans hv)
    subst v; exact .refl _
  | lit hl =>
    rintro u v rfl rfl
    obtain ⟨u', v', hl', hu, hv⟩ := e.copy _ _ hl
    have h₁ := Fin.castAdd_injective _ _ hu
    have h₂ := Fin.castAdd_injective _ _ hv
    subst u'; subst v'
    exact .lit hl'
  | trans hl hr ih ih' =>
    rintro u v rfl rfl
    obtain ⟨w, hw⟩ := e.middle_original hl hr
    exact .trans (ih u w rfl hw) (ih' w v hw rfl)
  | @decomp a b z w i hl _ hu ih =>
    rintro u v ha hb
    rcases e.lower _ _ hl with ⟨a', z', hl', rfl, rfl⟩ | ⟨hs, _⟩
    · rcases e.upper _ _ hu with ⟨w', b', hu', rfl, rfl⟩ | ⟨ht, _⟩
      · have h₁ : a' i = u := Fin.castAdd_injective _ _ ha
        have h₂ : b' i = v := Fin.castAdd_injective _ _ hb
        subst u; subst v
        exact .decomp i hl' (ih _ _ rfl rfl) hu'
      · exact False.elim (e.not_sink_original v (hb ▸ (ht i).1))
    · exact False.elim (e.not_source_original u (ha ▸ (hs i).1))

/-- The derivations between original variables are those of the original constraint. -/
theorem Extension.derives_original (e : Extension Γ ψ Source Sink rank) (u v : Fin k) :
    Derives ψ (Fin.castAdd m u) (Fin.castAdd m v) ↔ Derives Γ u v :=
  ⟨fun h => e.derives_reflect h u v rfl rfl, fun h => h.map _ e.original_mem⟩

/-- A lower path judgment ending at a source starts at a source of at least the same rank, and of
strictly greater rank when the path is nonempty. -/
theorem Extension.lowerAt_source (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (h : LowerAt ψ π a b)
    (hb : Source b) : Source a ∧ rank b ≤ rank a ∧ (π ≠ [] → rank b < rank a) := by
  induction h with
  | nil hd =>
    have he := e.derives_into_source hd hb
    subst he
    exact ⟨hb, le_rfl, fun hn => False.elim (hn rfl)⟩
  | @cons c z b a π i hl hd hp ih =>
    have he := e.derives_into_source hd hb
    subst z
    rcases e.lower _ _ hl with ⟨c', z', _, _, rfl⟩ | ⟨hc, _⟩
    · exact False.elim (e.not_source_original z' hb)
    · obtain ⟨ha, hle, _⟩ := ih (hc i).1
      have hlt := (hc i).2
      exact ⟨ha, (lt_of_lt_of_le hlt hle).le, fun _ => lt_of_lt_of_le hlt hle⟩

/-- An upper path judgment starting at a sink ends at a sink of at least the same rank, and of
strictly greater rank when the path is nonempty. -/
theorem Extension.upperAt_sink (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (h : UpperAt ψ π a b)
    (ha : Sink a) : Sink b ∧ rank a ≤ rank b ∧ (π ≠ [] → rank a < rank b) := by
  induction h with
  | nil hd =>
    have he := e.derives_out_of_sink hd ha
    subst he
    exact ⟨ha, le_rfl, fun hn => False.elim (hn rfl)⟩
  | @cons a z c b π i hd hl hp ih =>
    have he := e.derives_out_of_sink hd ha
    subst z
    rcases e.upper _ _ hl with ⟨z', c', _, rfl, _⟩ | ⟨hc, _⟩
    · exact False.elim (e.not_sink_original z' ha)
    · obtain ⟨hb, hle, _⟩ := ih (hc i).1
      have hlt := (hc i).2
      exact ⟨hb, (lt_of_lt_of_le hlt hle).le, fun _ => lt_of_lt_of_le hlt hle⟩

/-- A lower path judgment of the extension between original variables holds in the original
constraint. -/
theorem Extension.lowerAt_reflect (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (h : LowerAt ψ π a b) :
    ∀ u v : Fin k, a = Fin.castAdd m u → b = Fin.castAdd m v → LowerAt Γ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons c z b a π i hl hd hp ih =>
    rintro u v rfl rfl
    rcases e.lower _ _ hl with ⟨c', z', hl', rfl, rfl⟩ | ⟨hc, _⟩
    · exact LowerAt.cons hl' ((e.derives_original _ _).mp hd) (ih _ _ rfl rfl)
    · exact False.elim (e.not_source_original u (e.lowerAt_source hp (hc i).1).1)

/-- An upper path judgment of the extension between original variables holds in the original
constraint. -/
theorem Extension.upperAt_reflect (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (h : UpperAt ψ π a b) :
    ∀ u v : Fin k, a = Fin.castAdd m u → b = Fin.castAdd m v → UpperAt Γ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons a z c b π i hd hl hp ih =>
    rintro u v rfl rfl
    rcases e.upper _ _ hl with ⟨z', c', hl', rfl, rfl⟩ | ⟨hc, _⟩
    · exact UpperAt.cons ((e.derives_original _ _).mp hd) hl' (ih _ _ rfl rfl)
    · exact False.elim (e.not_sink_original v (e.upperAt_sink hp (hc i).1).1)

theorem Extension.lowerAt_original (e : Extension Γ ψ Source Sink rank)
    (π : List (Fin n)) (u v : Fin k) :
    LowerAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ LowerAt Γ π u v :=
  ⟨fun h => e.lowerAt_reflect h u v rfl rfl, fun h => h.map _ e.original_mem⟩

theorem Extension.upperAt_original (e : Extension Γ ψ Source Sink rank)
    (π : List (Fin n)) (u v : Fin k) :
    UpperAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ UpperAt Γ π u v :=
  ⟨fun h => e.upperAt_reflect h u v rfl rfl, fun h => h.map _ e.original_mem⟩

/-- The two variables of a cycle clash of the extension are original variables. -/
theorem Extension.cycle_original (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    (∃ u : Fin k, a = Fin.castAdd m u) ∧ (∃ v : Fin k, b = Fin.castAdd m v) := by
  have hsa : ¬ Source a := fun hs => (Nat.lt_irrefl _) ((e.lowerAt_source hl hs).2.2 hn)
  have htb : ¬ Sink b := fun ht => (Nat.lt_irrefl _) ((e.upperAt_sink hu ht).2.2 hn)
  constructor
  · rcases e.variable_cases a with h | hs | ht
    · exact h
    · exact False.elim (hsa hs)
    · have he := e.derives_out_of_sink hd ht
      exact False.elim (htb (he ▸ ht))
  · rcases e.variable_cases b with h | hs | ht
    · exact h
    · have he := e.derives_into_source hd hs
      exact False.elim (hsa (he ▸ hs))
    · exact False.elim (htb ht)

/-- A cycle clash of the extension along a path `π` gives a cycle clash of the original
constraint along `π`. -/
theorem Extension.cycle_reflect (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    ∃ u v : Fin k, LowerAt Γ π u u ∧ Derives Γ u v ∧ UpperAt Γ π v v := by
  obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := e.cycle_original hn hl hd hu
  exact ⟨u, v, (e.lowerAt_original ..).mp hl, (e.derives_original ..).mp hd,
    (e.upperAt_original ..).mp hu⟩

end Ranked

end DeciSigma1.Constraints

namespace DeciSigma1.Constraints.Ranked

open DeciSigma1.Constraints.Covariant DeciSigma1.Satisfiability DeciSigma1.Semantics

variable {n k m : ℕ}

section Extension

variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}

/-- A solution of an extension, restricted to the original variables, solves the original
constraint. -/
theorem Extension.restrict_sat (e : Extension Γ ψ Source Sink rank)
    {ρ' : Fin (k + m) → Semantics.Tree n} (h : Covariant.Sat ρ' ψ) : Covariant.Sat
        (ρ' ∘ Fin.castAdd m) Γ := by
  intro l hl
  exact (covariant_holds_map _ _ _).mp (h _ (e.original_mem l hl))

/-- A ranked extension has a cycle clash exactly when the original constraint has one. -/
theorem Extension.cycleClash_iff (e : Extension Γ ψ Source Sink rank) :
    CycleClash ψ ↔ CycleClash Γ := by
  constructor
  · rintro ⟨π, a, b, hn, hl, hd, hu⟩
    obtain ⟨u, v, hl', hd', hu'⟩ := e.cycle_reflect hn hl hd hu
    exact ⟨π, u, v, hn, hl', hd', hu'⟩
  · rintro ⟨π, u, v, hn, hl, hd, hu⟩
    exact ⟨π, _, _, hn, hl.map _ e.original_mem, hd.map _ e.original_mem, hu.map _ e.original_mem⟩

/-- A ranked extension has a finite solution exactly when it has a solution and the original
constraint has a finite solution. -/
theorem Extension.satFin_iff (e : Extension Γ ψ Source Sink rank) :
    (∃ σ : Fin (k + m) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ψ) ↔
      (∃ ρ', Covariant.Sat ρ' ψ) ∧ ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨_, hσ⟩, ⟨σ ∘ Fin.castAdd m, e.restrict_sat hσ⟩⟩
  · rintro ⟨⟨ρ', hρ'⟩, hf⟩
    apply Satisfiability.satFin_iff.mpr
    exact ⟨fun hl => hl.unsatisfiable ⟨ρ', hρ'⟩,
      fun hc => (Satisfiability.satFin_iff.mp hf).2 (e.cycleClash_iff.mp hc)⟩

end Extension

end DeciSigma1.Constraints.Ranked
