/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.Core

/-!
This file isolates the reduction proved in Section 2 of Matiyasevich's
"Word Problem for Thue Systems with a Few Relations" (1995) from the
downstream construction of the standing Thue datum.

The paper starts with an arbitrary finite Thue system `T₀`, passes through
systems `T₁` and `T₂`, and finishes with the binary three-relation system

* `ddcc  ↔ cdd`,
* `ddcdc ↔ cdd`,
* `ρ₂(L) ↔ ρ₂(M)`.

With `d = 0` and `c = 1`, and with the first two relations exchanged, this is
definitionally the system `Thue.baseSystem` used by the project.
-/

@[expose] public section

namespace Undecidability

namespace Thue

namespace Matiyasevich1993

/-- A finite Thue system whose relations are explicitly indexed. -/
def finiteSystem {α : Type*} {r : ℕ}
    (F E : Fin r → List α) : ThueSystem α :=
  Set.range fun i => (F i, E i)

/-- A computable, equivalence-reflecting encoding of one Thue system into
another.  This is equivalence (10) in the paper. -/
structure Embedding {α β : Type*} [Primcodable α] [Primcodable β]
    (S : ThueSystem α) (T : ThueSystem β) where
  /-- The computable word encoding of an equivalence-reflecting Thue-system embedding. -/
  encode : List α → List β
  encode_computable : Computable encode
  thueEq_iff : ∀ X Y, ThueEq S X Y ↔ ThueEq T (encode X) (encode Y)

namespace Embedding

/-- Equivalence-reflecting encodings compose. -/
def comp {α β γ : Type*}
    [Primcodable α] [Primcodable β] [Primcodable γ]
    {S : ThueSystem α} {T : ThueSystem β} {U : ThueSystem γ}
    (g : Embedding T U) (f : Embedding S T) : Embedding S U where
  encode := g.encode ∘ f.encode
  encode_computable := g.encode_computable.comp f.encode_computable
  thueEq_iff := fun X Y => (f.thueEq_iff X Y).trans
    (g.thueEq_iff (f.encode X) (f.encode Y))

/-- Fixed-target undecidability is transported by an embedding. -/
theorem target_undecidable {α β : Type*}
    [Primcodable α] [Primcodable β]
    {S : ThueSystem α} {T : ThueSystem β}
    (f : Embedding S T) (P : List α)
    (h : ¬ ComputablePred fun Q : List α => ThueEq S Q P) :
    ¬ ComputablePred fun Q : List β => ThueEq T Q (f.encode P) := by
  apply not_computablePred_of_manyOneReducible h
  exact ⟨f.encode, f.encode_computable, fun Q => f.thueEq_iff Q P⟩

end Embedding

/-- The exact finite seed needed from the machine-to-Thue bridge.

No nonemptiness condition on the sides of the seed relations is needed:
Matiyasevich's first padding stage makes all sides nonempty.  Positivity of the
alphabet and relation index types avoids degenerate enumerations in the formulas
of Sections 2.2--2.4.  The machine construction naturally supplies both.
-/
structure FiniteFixedTargetSeed where
  /-- The number of letters in the finite seed alphabet. -/
  alphabetSize : ℕ
  /-- The number of rules in the finite seed Thue system. -/
  relationCount : ℕ
  alphabetSize_pos : 0 < alphabetSize
  relationCount_pos : 0 < relationCount
  /-- The indexed left-hand words of the finite seed rules. -/
  F : Fin relationCount → List (Fin alphabetSize)
  /-- The indexed right-hand words of the finite seed rules. -/
  E : Fin relationCount → List (Fin alphabetSize)
  /-- The fixed target word whose Thue-equivalence class is undecidable. -/
  P : List (Fin alphabetSize)
  undecidable :
    ¬ ComputablePred fun Q : List (Fin alphabetSize) =>
      ThueEq (finiteSystem F E) Q P

/-- Existence of a binary three-relation Thue system with an undecidable
fixed-target word problem. -/
def HasUndecidableThreeRuleSystem : Prop :=
  ∃ U₃ V₃ P₀ : List (Fin 2),
    U₃ ≠ [] ∧
    V₃ ≠ [] ∧
    P₀ ≠ [] ∧
    ¬ ComputablePred fun Q : List (Fin 2) =>
      ThueEq (baseSystem U₃ V₃) Q P₀

/-- The precise mathematical content required from Section 2 of the 1995
paper.  The encoding is nonempty even on the empty source word because the
first two stages append their marker words. -/
def CompressionTheorem : Prop :=
  ∀ (n r : ℕ), 0 < n → 0 < r →
    (F E : Fin r → List (Fin n)) →
    ∃ U₃ V₃ : List (Fin 2),
      U₃ ≠ [] ∧ V₃ ≠ [] ∧
      ∃ reduction : Embedding (finiteSystem F E) (baseSystem U₃ V₃),
        ∀ W, reduction.encode W ≠ []

/-- The three-stage compression theorem sends any finite fixed-target seed to
an undecidable binary three-relation system. -/
theorem has_undecidable_three_rule_system_of_compression
    (hcompression : CompressionTheorem)
    (seed : FiniteFixedTargetSeed) : HasUndecidableThreeRuleSystem := by
  obtain ⟨U₃, V₃, hU₃, hV₃, reduction, hnonempty⟩ :=
    hcompression seed.alphabetSize seed.relationCount
      seed.alphabetSize_pos seed.relationCount_pos seed.F seed.E
  refine ⟨U₃, V₃, reduction.encode seed.P, hU₃, hV₃,
    hnonempty seed.P, ?_⟩
  exact reduction.target_undecidable seed.P seed.undecidable

end Matiyasevich1993

end Thue

end Undecidability
