/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/ForcingRequirements.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.ForcingSymmetry

/-!
# Forcing Requirements
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CountableForcing
open Set
variable {P : Type*} [Preorder P]

def mergeRequirements (D E : ℕ → Set P) (n : ℕ) : Set P :=
  if n % 2 = 0 then D (n/2) else E (n/2)

theorem mergeRequirements_dense (D E : ℕ → Set P)
    (hD : ∀ n, Dense (D n)) (hE : ∀ n, Dense (E n)) :
    ∀ n, Dense (mergeRequirements D E n) := by
  intro n
  dsimp [mergeRequirements]
  split <;> first | exact hD _ | exact hE _

theorem generic_merge_iff (D E : ℕ → Set P) (G : GenericFilter P) :
    GenericFor (mergeRequirements D E) G ↔ GenericFor D G ∧ GenericFor E G := by
  constructor
  · intro h
    constructor
    · intro n; simpa [mergeRequirements] using h (2*n)
    · intro n; simpa [mergeRequirements,Nat.add_div] using h (2*n+1)
  · rintro ⟨hD,hE⟩ n
    dsimp [mergeRequirements]
    split <;> first | exact hD _ | exact hE _

namespace Sentence

theorem weak_iff_with_extra (p : P) (a : Sentence P)
    (E : ℕ → Set P) (hE : ∀ n, Dense (E n)) :
    WeakForces p a ↔ ∀ G : GenericFilter P,
      GenericFor (Requirements (.neg (.neg a))) G → GenericFor E G →
      p ∈ G.carrier → Truth G a := by
  constructor
  · intro h G hG _ hp
    exact (weak_iff_all_generic p a).mp h G hG hp
  · intro h q hqp hq
    obtain ⟨G,hqG,hG⟩ := exists_generic (mergeRequirements (Requirements (.neg (.neg a))) E)
      (mergeRequirements_dense _ _ (requirements_dense _) hE) q
    obtain ⟨hGa,hGE⟩ := (generic_merge_iff _ _ G).mp hG
    have hsub : GenericFor (Requirements (.neg a)) G := by
      intro n; simpa [Requirements] using hGa (n+1)
    have hn := (generic_truth (.neg a) G hsub).mpr ⟨q,hqG,hq⟩
    exact hn (h G hGa hGE (G.upper hqp hqG))

theorem weak_congr_of_generic_equiv (a b : Sentence P)
    (E : ℕ → Set P) (hE : ∀ n, Dense (E n))
    (heq : ∀ G : GenericFilter P,
      GenericFor (Requirements (.neg (.neg a))) G →
      GenericFor (Requirements (.neg (.neg b))) G → GenericFor E G →
      (Truth G a ↔ Truth G b)) (p : P) : WeakForces p a ↔ WeakForces p b := by
  constructor
  · intro ha
    apply (weak_iff_with_extra p b (mergeRequirements (Requirements (.neg (.neg a))) E)
      (mergeRequirements_dense _ _ (requirements_dense _) hE)).mpr
    intro G hGb hExtra hp
    obtain ⟨hGa,hGE⟩ := (generic_merge_iff _ _ G).mp hExtra
    exact (heq G hGa hGb hGE).mp ((weak_iff_all_generic p a).mp ha G hGa hp)
  · intro hb
    apply (weak_iff_with_extra p a (mergeRequirements (Requirements (.neg (.neg b))) E)
      (mergeRequirements_dense _ _ (requirements_dense _) hE)).mpr
    intro G hGa hExtra hp
    obtain ⟨hGb,hGE⟩ := (generic_merge_iff _ _ G).mp hExtra
    exact (heq G hGa hGb hGE).mpr ((weak_iff_all_generic p b).mp hb G hGb hp)

end Sentence
end TuringRigidity.CountableForcing

end OAI
