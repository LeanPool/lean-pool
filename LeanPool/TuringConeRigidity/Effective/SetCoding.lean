/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/SetCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.IndependentFamily
public import LeanPool.TuringConeRigidity.SetModels.CountableBound
public import LeanPool.TuringConeRigidity.Effective.AntichainParameters

/-!
# Set Coding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetCoding
open AntichainParameters IndependentFamily

/-- Three degree parameters defining a minimal common-lower antichain predicate. -/
structure AntichainCode where
  /-- The upper bound in the antichain code. -/
  bound : Degree
  /-- The first join parameter in the antichain code. -/
  left : Degree
  /-- The second join parameter in the antichain code. -/
  right : Degree

/-- Membership in the minimal common-lower antichain described by the three degree parameters. -/
def AntichainCode.Holds (p : AntichainCode) (x : Degree) : Prop :=
  CodedAntichain p.bound p.left p.right x

theorem exists_antichainCode (S : Set Degree) (hS : S.Countable)
    (hAnti : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → x = y) :
    ∃ p : AntichainCode, ∀ x, p.Holds x ↔ x ∈ S := by
  obtain ⟨b, hb⟩ := CountableBound.countable_bounded S hS
  obtain ⟨g₀, g₁, hg⟩ := countable_antichain_parameters S b hS hb hAnti
  exact ⟨⟨b, g₀, g₁⟩, hg⟩

/-- A bounded degree-set code using tag and decorated antichain codes. -/
structure SetCode where
  /-- The upper degree bound on values represented by the set code. -/
  bound : Degree
  /-- The antichain code for the tags attached to represented values. -/
  tags : AntichainCode
  /-- The antichain code for joins of represented values with their tags. -/
  decorated : AntichainCode

/-- A value is below the bound, its tag is valid, and their join satisfies the decorated code. -/
def SetCode.Graph (p : SetCode) (x c : Degree) : Prop :=
  x ≤ p.bound ∧ p.tags.Holds c ∧ p.decorated.Holds (x ⊔ c)

/-- The value has a tag satisfying the set code's graph relation. -/
def SetCode.Holds (p : SetCode) (x : Degree) : Prop := ∃ c, p.Graph x c

theorem codes_with_tags (S : Set Degree) (hS : S.Countable) (b : Degree)
    (hb : ∀ x ∈ S, x ≤ b) (index : S → ℕ) (hindex : Function.Injective index) :
    ∃ p : SetCode, p.bound = b ∧
      (∀ x c, p.Graph x c ↔ ∃ a : S, a.val = x ∧ column b (index a) = c) ∧
      ∀ x, p.Holds x ↔ x ∈ S := by
  let C : Set Degree := Set.range (fun a : S => column b (index a))
  let A : Set Degree := Set.range (fun a : S => a.val ⊔ column b (index a))
  have : Countable S := hS.to_subtype
  have hC : C.Countable := Set.countable_range _
  have hA : A.Countable := Set.countable_range _
  have htag (x y : Degree) (hx : x ≤ b) (hy : y ≤ b) (i j : ℕ) :
      x ⊔ column b i ≤ y ⊔ column b j ↔ x ≤ y ∧ i = j := by
    simpa using independence b x y hx hy i {j}
  have hac : ∀ x ∈ C, ∀ y ∈ C, x ≤ y → x = y := by
    rintro x ⟨a, rfl⟩ y ⟨d, rfl⟩ h
    have hi := (htag ⊥ ⊥ bot_le bot_le (index a) (index d)).mp (by simpa using h)
    exact congrArg (column b) hi.2
  have haa : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y := by
    rintro x ⟨a, rfl⟩ y ⟨d, rfl⟩ h
    have hi := (htag a.val d.val (hb _ a.property) (hb _ d.property) _ _).mp h
    have he := hindex hi.2
    subst d
    rfl
  obtain ⟨pc, hpc⟩ := exists_antichainCode C hC hac
  obtain ⟨pa, hpa⟩ := exists_antichainCode A hA haa
  let p : SetCode := ⟨b, pc, pa⟩
  have hgraph : ∀ x c, p.Graph x c ↔ ∃ a : S, a.val = x ∧ column b (index a) = c := by
    intro x c
    change (x ≤ b ∧ pc.Holds c ∧ pa.Holds (x ⊔ c)) ↔ _
    rw [hpc, hpa]
    constructor
    · rintro ⟨hx, ⟨a, rfl⟩, ⟨d, he⟩⟩
      have hl := (htag d.val x (hb _ d.property) hx (index d) (index a)).mp he.le
      have hr := (htag x d.val hx (hb _ d.property) (index a) (index d)).mp he.ge
      have hed := hindex hl.2
      subst d
      exact ⟨a, le_antisymm hl.1 hr.1, rfl⟩
    · rintro ⟨a, rfl, rfl⟩
      exact ⟨hb _ a.property, ⟨a, rfl⟩, ⟨a, rfl⟩⟩
  refine ⟨p, rfl, hgraph, ?_⟩
  intro x
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨a, rfl, _⟩ := (hgraph x c).mp hc
    exact a.property
  · intro hx
    exact ⟨column b (index ⟨x, hx⟩), (hgraph _ _).mpr ⟨⟨x, hx⟩, rfl, rfl⟩⟩

theorem countable_set_coding (S : Set Degree) (hS : S.Countable) :
    ∃ p : SetCode, ∀ x, p.Holds x ↔ x ∈ S := by
  classical
  have : Countable S := hS.to_subtype
  let := Encodable.ofCountable S
  obtain ⟨b, hb⟩ := CountableBound.countable_bounded S hS
  obtain ⟨p, _, _, hp⟩ := codes_with_tags S hS b hb Encodable.encode Encodable.encode_injective
  exact ⟨p, hp⟩

end TuringRigidity.SetCoding

end OAI
