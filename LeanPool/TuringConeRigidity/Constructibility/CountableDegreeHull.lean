/-
Copyright (c) 2026 OpenAI and Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Bjørn Kjos-Hanssen
-/

/-
Extracted for Lean Pool from the Apache-2.0 closure constructions in
bjoernkjoshanssen/tt-auto/OAI/Computability/DegreeRigidity/Constructibility/
PersistentRestrictions.lean and RequestProject/TuringConePersistence.lean and
RequestProject/TuringTwoConePersistence.lean. A finite list of supplied maps
keeps the ordinary hull jump-free and preserves each original closure stage.
-/

module

public import LeanPool.TuringConeRigidity.Computability.Joins
public import LeanPool.TuringConeRigidity.Computability.OracleCode
public import Mathlib.Order.CompletePartialOrder

/-!
# Countable degree hulls under supplied operations
-/

@[expose] public section

namespace OAI.TuringRigidity.CountableDegreeHull

open Set

/-- Every principal lower set of Turing degrees is countable. -/
theorem countable_principal_lower (a : Degree) : (Set.Iic a).Countable := by
  obtain ⟨A, rfl⟩ := degree_surjective a
  apply ((countable_reduces A).image degree).mono
  intro b hb
  obtain ⟨B, rfl⟩ := degree_surjective b
  exact ⟨B, (degree_le_iff B A).mp hb, rfl⟩

/-- Add the images of a finite list of operations before an existing tail. -/
def addImages (operations : List (Degree → Degree)) (S T : Set Degree) : Set Degree :=
  match operations with
  | [] => T
  | f :: rest => f '' S ∪ addImages rest S T

/-- Finite operation images preserve countability. -/
theorem countable_addImages (operations : List (Degree → Degree))
    {S T : Set Degree} (hS : S.Countable) (hT : T.Countable) :
    (addImages operations S T).Countable := by
  induction operations with
  | nil => exact hT
  | cons f rest ih => exact (hS.image f).union ih

/-- The original tail survives the addition of operation images. -/
theorem tail_subset_addImages (operations : List (Degree → Degree)) (S T : Set Degree) :
    T ⊆ addImages operations S T := by
  induction operations with
  | nil => exact fun _ hx => hx
  | cons f rest ih => exact fun _ hx => Or.inr (ih hx)

/-- Every listed operation contributes the image of the current set. -/
theorem image_subset_addImages {operations : List (Degree → Degree)}
    {f : Degree → Degree} (hf : f ∈ operations) (S T : Set Degree) :
    f '' S ⊆ addImages operations S T := by
  induction operations with
  | nil => exact False.elim (List.not_mem_nil hf)
  | cons g rest ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact fun _ hx => Or.inl hx
    · exact fun _ hx => Or.inr (ih hf hx)

/-- Add supplied operation images, joins and lower degrees without choosing extra operations. -/
def closureStep (operations : List (Degree → Degree)) (S : Set Degree) : Set Degree :=
  S ∪ addImages operations S (Set.image2 (· ⊔ ·) S S ∪ ⋃ x ∈ S, Set.Iic x)

/-- A countable seed remains countable after one closure step. -/
theorem countable_closureStep (operations : List (Degree → Degree))
    {S : Set Degree} (hS : S.Countable) : (closureStep operations S).Countable :=
  hS.union (countable_addImages operations hS
    ((hS.image2 hS (· ⊔ ·)).union (hS.biUnion fun x _ => countable_principal_lower x)))

/-- Iterate exactly the supplied operations from the supplied seed. -/
def stage (operations : List (Degree → Degree)) (seed : Set Degree) : ℕ → Set Degree
  | 0 => seed
  | n + 1 => closureStep operations (stage operations seed n)

/-- Every finite closure stage of a countable seed is countable. -/
theorem countable_stage (operations : List (Degree → Degree))
    {seed : Set Degree} (hseed : seed.Countable) : ∀ n, (stage operations seed n).Countable
  | 0 => hseed
  | n + 1 => countable_closureStep operations (countable_stage operations hseed n)

/-- The closure stages increase because each step retains its input. -/
theorem stage_mono (operations : List (Degree → Degree)) (seed : Set Degree) :
    Monotone (stage operations seed) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  exact Or.inl hx

/-- The union of the finite closure stages of the specified seed. -/
def hullSet (operations : List (Degree → Degree)) (seed : Set Degree) : Set Degree :=
  ⋃ n, stage operations seed n

/-- The seed belongs to its closure hull. -/
theorem subset_hullSet (operations : List (Degree → Degree)) (seed : Set Degree) :
    seed ⊆ hullSet operations seed := fun _ hx => Set.mem_iUnion.mpr ⟨0, hx⟩

/-- The countable closure hull is countable. -/
theorem countable_hullSet (operations : List (Degree → Degree))
    {seed : Set Degree} (hseed : seed.Countable) : (hullSet operations seed).Countable :=
  Set.countable_iUnion (countable_stage operations hseed)

/-- The closure hull is downward closed. -/
theorem hullSet_lower (operations : List (Degree → Degree)) (seed : Set Degree)
    {x y : Degree} (hxy : x ≤ y) (hy : y ∈ hullSet operations seed) :
    x ∈ hullSet operations seed := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
  refine Set.mem_iUnion.mpr ⟨n + 1, Or.inr (tail_subset_addImages operations _ _ ?_)⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hn, hxy⟩⟩)

/-- The closure hull is closed under binary joins. -/
theorem hullSet_join (operations : List (Degree → Degree)) (seed : Set Degree)
    {x y : Degree} (hx : x ∈ hullSet operations seed) (hy : y ∈ hullSet operations seed) :
    x ⊔ y ∈ hullSet operations seed := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
  refine Set.mem_iUnion.mpr
    ⟨max m n + 1, Or.inr (tail_subset_addImages operations _ _ (Or.inl ?_))⟩
  exact ⟨x, stage_mono operations seed (le_max_left m n) hm,
    y, stage_mono operations seed (le_max_right m n) hn, rfl⟩

/-- Every supplied operation preserves the hull. -/
theorem hullSet_operation {operations : List (Degree → Degree)}
    {f : Degree → Degree} (hf : f ∈ operations) (seed : Set Degree)
    {x : Degree} (hx : x ∈ hullSet operations seed) : f x ∈ hullSet operations seed := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr
    ⟨n + 1, Or.inr (image_subset_addImages hf _ _ ⟨x, hn, rfl⟩)⟩

end OAI.TuringRigidity.CountableDegreeHull
