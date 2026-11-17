/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenSymmetry.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Data.Set.Finite.Basic

public import LeanPool.TuringConeRigidity.CohenForcing.ForcingSymmetry

/-!
# Cohen Symmetry
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenSymmetry
open Set CountableForcing

/-- A Boolean partial function with finite support, used as a Cohen condition. -/
@[ext] structure Condition (ι : Type*) where
  /-- The partial Boolean assignment underlying a Cohen condition. -/
  val : ι → Option Bool
  finite : {i | val i ≠ none}.Finite

variable {ι : Type*}

instance : PartialOrder (Condition ι) where
  le p q := ∀ i b, q.val i = some b → p.val i = some b
  le_refl _ := fun _ _ h => h
  le_trans _ _ _ hpq hqr := fun i b h => hpq i b (hqr i b h)
  le_antisymm p q hpq hqp := by
    apply Condition.ext
    funext i
    cases hp : p.val i with
    | none =>
      cases hq : q.val i with
      | none => rfl
      | some b => have h := hpq i b hq; simp [hp] at h
    | some b => exact (hqp i b hp).symm

instance : OrderTop (Condition ι) where
  top := ⟨fun _ => none, by simp⟩
  le_top _ := by intro i b h; cases h

/-- Flip each assigned Boolean value according to the mask `m`. -/
def flip (m : ι → Bool) (p : Condition ι) : Condition ι where
  val i := (p.val i).map (fun b => b.xor (m i))
  finite := p.finite.subset (by intro i hi; simpa using hi)

theorem flip_involutive (m : ι → Bool) (p : Condition ι) : flip m (flip m p) = p := by
  apply Condition.ext
  funext i
  cases h : p.val i with
  | none => simp [flip,h]
  | some b => cases b <;> cases hm : m i <;> simp [flip,h,hm]

theorem flip_mono (m : ι → Bool) {p q : Condition ι} (hpq : p ≤ q) :
    flip m p ≤ flip m q := by
  intro i b hb
  cases hq : q.val i with
  | none => simp [flip,hq] at hb
  | some c =>
    have hp := hpq i c hq
    simpa [flip,hp] using (show (some c).map (fun d => d.xor (m i)) = some b from by
      simpa [flip,hq] using hb)

/-- The involutive order automorphism induced by a Boolean coordinate mask. -/
def flipIso (m : ι → Bool) : Condition ι ≃o Condition ι where
  toFun := flip m
  invFun := flip m
  left_inv := flip_involutive m
  right_inv := flip_involutive m
  map_rel_iff' := by
    intro p q
    change flip m p ≤ flip m q ↔ p ≤ q
    exact ⟨fun h => by simpa only [flip_involutive] using flip_mono m h,flip_mono m⟩

/-- Two conditions agree at every coordinate where both assign a value. -/
def Compatible (p q : Condition ι) : Prop :=
  ∀ i a b, p.val i = some a → q.val i = some b → a = b

/-- Merge two partial assignments, preferring the first assignment on overlapping coordinates. -/
def merge (p q : Condition ι) : Condition ι where
  val i := (p.val i).orElse (fun _ => q.val i)
  finite := (p.finite.union q.finite).subset (by
    intro i hi
    by_cases hp : p.val i = none
    · exact Or.inr (by simpa [hp] using hi)
    · exact Or.inl hp)

theorem merge_le_left (p q : Condition ι) : merge p q ≤ p := by
  intro i b hb
  simp [merge,hb]

theorem merge_le_right {p q : Condition ι} (h : Compatible p q) : merge p q ≤ q := by
  intro i b hb
  cases hp : p.val i with
  | none => simp [merge,hp,hb]
  | some a => simpa [merge,hp] using congrArg some (h i a b hp hb)

/-- The coordinate mask comparing the assigned values of two conditions, with missing values
read as false. -/
def matchingMask (p q : Condition ι) (i : ι) : Bool :=
  (p.val i).getD false |>.xor ((q.val i).getD false)

theorem matching_compatible (p q : Condition ι) : Compatible (flip (matchingMask p q) p) q := by
  intro i a b ha hb
  cases hp : p.val i with
  | none => simp [flip,hp] at ha
  | some c =>
    cases c <;> cases b <;> simpa [flip,matchingMask,hp,hb] using ha.symm

theorem homogeneous (p q : Condition ι) :
    ∃ m : ι → Bool, ∃ r : Condition ι, r ≤ flipIso m p ∧ r ≤ q := by
  exact ⟨matchingMask p q,merge (flip (matchingMask p q) p) q,
    merge_le_left _ _,merge_le_right (matching_compatible p q)⟩

/-- Apply a Boolean flip to the Cohen factor while leaving the other product coordinate fixed. -/
def tailIso {P : Type*} [Preorder P] (m : ι → Bool) :
    (P × Condition ι) ≃o (P × Condition ι) where
  toFun p := (p.1,flipIso m p.2)
  invFun p := (p.1,(flipIso m).symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_rel_iff' := by intro p q; exact and_congr Iff.rfl (flipIso m).le_iff_le

theorem remove_tail {P : Type*} [Preorder P]
    (a : Sentence (P × Condition ι))
    (hinv : ∀ m p, Sentence.Forces p (Sentence.rename (tailIso m) a) ↔ Sentence.Forces p a)
    (p : P) (q : Condition ι) (h : Sentence.WeakForces (p, q) a) :
    ∀ r : Condition ι, Sentence.WeakForces (p,r) a := by
  apply Sentence.remove_tail_of_transport a ?_ p q h
  intro x u v hu
  obtain ⟨m,s,hs,hsv⟩ := homogeneous u v
  have he := (Sentence.forces_rename (tailIso m) a (x,u)).mpr hu
  have hf : Sentence.Forces (x,flipIso m u) a := (hinv m _).mp he
  exact ⟨s,hsv,Sentence.forces_mono a (p := (x,flipIso m u)) (q := (x,s)) ⟨le_rfl,hs⟩ hf⟩

theorem top_weak_of_invariant (a : Sentence (Condition ι))
    (hinv : ∀ m p, Sentence.Forces p (Sentence.rename (flipIso m) a) ↔ Sentence.Forces p a)
    (p : Condition ι) (hp : Sentence.Forces p a) : Sentence.WeakForces ⊤ a := by
  apply (Sentence.weak_iff_dense_below _ a).mpr
  intro q _
  obtain ⟨m,r,hr,hq⟩ := homogeneous p q
  have h := (hinv m _).mp ((Sentence.forces_rename (flipIso m) a p).mpr hp)
  exact ⟨r,hq,Sentence.forces_mono a hr h⟩

theorem remove_tail_weak {P : Type*} [Preorder P]
    (a : Sentence (P × Condition ι))
    (hinv : ∀ m p, Sentence.WeakForces p (Sentence.rename (tailIso m) a) ↔
      Sentence.WeakForces p a)
    (p : P) (q : Condition ι) (h : Sentence.WeakForces (p, q) a) :
    ∀ r : Condition ι, Sentence.WeakForces (p,r) a := by
  intro r
  apply (Sentence.weak_iff_dense_below _ a).mpr
  intro t ht
  have htu : Sentence.WeakForces (t.1,q) a :=
    Sentence.forces_mono (.neg (.neg a)) (p := (p,q)) (q := (t.1,q)) ⟨ht.1,le_rfl⟩ h
  obtain ⟨m,s,hs,hst⟩ := homogeneous q t.2
  have hren := (Sentence.weak_rename (tailIso m) a (t.1,q)).mpr htu
  have hf : Sentence.WeakForces (t.1,flipIso m q) a := (hinv m _).mp hren
  obtain ⟨u,hu,hua⟩ := (Sentence.weak_iff_dense_below _ a).mp hf
    (t.1,s) ⟨le_rfl,hs⟩
  exact ⟨u,⟨hu.1,hu.2.trans hst⟩,hua⟩

theorem top_weak_of_weak_invariant (a : Sentence (Condition ι))
    (hinv : ∀ m p, Sentence.WeakForces p (Sentence.rename (flipIso m) a) ↔
      Sentence.WeakForces p a)
    (p : Condition ι) (hp : Sentence.WeakForces p a) : Sentence.WeakForces ⊤ a := by
  apply (Sentence.weak_iff_dense_below _ a).mpr
  intro q _
  obtain ⟨m,r,hr,hq⟩ := homogeneous p q
  have h := (hinv m _).mp ((Sentence.weak_rename (flipIso m) a p).mpr hp)
  obtain ⟨s,hs,hsa⟩ := (Sentence.weak_iff_dense_below _ a).mp h r hr
  exact ⟨s,hs.trans hq,hsa⟩

end TuringRigidity.CohenSymmetry

end OAI
