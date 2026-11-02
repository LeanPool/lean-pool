/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Graf
-/
module

-- Adapted for Lean Pool from Iris-Lean.

public import LeanPool.IrisAlgebra.Algebra.OFE

/-! A guarded recursive domain equation solver.

Copyright (c) The Iris-Lean Contributors.
-/

@[expose] public section

namespace Iris.COFE.OFunctor
open OFE

variable {F : ∀ α β [COFE α] [COFE β], Type u} [OFunctorContractive F]
variable [∀ α [COFE α], IsCOFE (F α α)]
variable [inh : Inhabited (F (ULift Unit) (ULift Unit))]

namespace Fix.Impl

variable (F) in
/-- The approximation carriers bundled with their complete space structures. -/
def A' : Nat → Σ α : Type u, COFE α
  | 0 => ⟨ULift Unit, inferInstance⟩
  | n+1 => let ⟨A, _⟩ := A' n; ⟨F A A, inferInstance⟩

variable (F) in
/-- The carrier at one level of the recursive-domain approximation. -/
@[implicit_reducible] def A (n : Nat) : Type u := (A' F n).1

instance instA' (n) : COFE (A' F n).1 := (A' F n).2
instance instA (n) : COFE (A F n) := (A' F n).2

variable (F) in
/-- The section/retraction pair at every level, computed by a single recursion so
that evaluating either component at level `k` costs `O(k)` (the naive mutual
recursion recomputes both branches at every level, which is `2^k`). -/
def updown : ∀ k, (A F k -n> A F (k+1)) × (A F (k+1) -n> A F k)
  | 0 => (⟨fun _ => inh.default, ⟨fun _ _ _ _ => .rfl⟩⟩, ⟨fun _ => ⟨()⟩, ⟨fun _ _ _ _ => .rfl⟩⟩)
  | k+1 => let (u, d) := updown k; (map d u, map u d)

variable (F) in
/-- The section from one approximation level to its successor. -/
def up (k : Nat) : A F k -n> A F (k+1) := (updown F k).1

variable (F) in
/-- The retraction from a successor approximation to its predecessor. -/
def down (k : Nat) : A F (k+1) -n> A F k := (updown F k).2

theorem down_up : ∀ {k} x, down F k (up F k x) = x
  | 0, ⟨()⟩ => rfl
  | _+1, x => OFE.eq_dist_2 fun _ => (map_comp _ _ _ _ _).dist.symm.trans <|
    Dist.trans
      (map_ne.ne (fun y => (down_up y).dist) (fun y => (down_up y).dist) x)
      (map_id _).dist

theorem up_down {k} (x) : up F (k+1) (down F (k+1) x) ≡{k}≡ x := by
  refine (map_comp _ _ _ _ _).dist.symm.trans <| .trans ?_ (map_id _).dist
  open OFunctorContractive in exact match k with
  | 0 => map_contractive.zero (x := (_, _)) (y := (_, _)) _ _
  | k+1 => map_contractive.succ (x := (_, _)) (y := (_, _)) _ ⟨up_down, up_down⟩ _

variable (F) in
/-- A family of approximations compatible with all one-step retractions. -/
@[ext]
structure Tower : Type u where
  /-- The approximation at each tower level. -/
  val k : A F k
  protected down {k} : down F k (val (k+1)) = val k

instance : CoeFun (Tower F) (fun _ => ∀ k, A F k) := ⟨Tower.val⟩

instance : OFE (Tower F) where
  Dist n f g := ∀ k, f k ≡{n}≡ g k
  dist_eqv := {
    refl _ _ := dist_eqv.refl _
    symm h _ := dist_eqv.symm (h _)
    trans h1 h2 _ := dist_eqv.trans (h1 _) (h2 _)
  }
  eq_dist' {_ _} := by rw [Tower.ext_iff, funext_iff]; simpa only [eq_dist] using forall_comm
  dist_lt h1 h2 _ := dist_lt (h1 _) h2

/-- Evaluate a chain of coherent towers at one level. -/
def towerChain (c : Chain (Tower F)) (k : Nat) : Chain (A F k) where
  chain i := c.1 i k
  cauchy h := c.cauchy h k

instance : COFE (Tower F) where
  compl c := by
    refine ⟨fun k => compl ⟨fun i => c.1 i k, fun h => c.cauchy h k⟩, ?_⟩
    refine OFE.eq_dist_2 (fun n => ?_)
    refine ((down ..).ne.1 conv_compl).trans <| .trans ?_ conv_compl.symm
    exact (c.chain n).down.dist
  conv_compl _ := conv_compl

variable (F) in
/-- Compose the sections through a specified number of approximation levels. -/
def upN {k} : ∀ n, A F k -n> A F (k + n)
  | 0 => .id
  | n+1 => (up F (k + n)).comp (upN n)

variable (F) in
/-- Compose the retractions through a specified number of approximation levels. -/
def downN {k} : ∀ n, A F (k + n) -n> A F k
  | 0 => .id
  | n+1 => (downN n).comp (down F (k + n))

theorem downN_upN {k} (x : A F k) : ∀ {i}, downN F i (upN F i x) = x
  | 0 => rfl
  | n+1 => (congrArg (fun a => (downN F n) a) (down_up _)).trans (downN_upN _)

protected theorem Tower.up (X : Tower F) : up F (k+1) (X (k+1)) ≡{k}≡ X (k+2) :=
  ((up ..).ne.1 X.down.symm.dist).trans <| up_down _

protected theorem Tower.upN (X : Tower F) : ∀ i, upN F i (X (k+1)) ≡{k}≡ X (k+1+i)
  | 0 => .rfl
  | n+1 => by
    have : ∀ j, k+n+1 = j → up F j (X j) ≡{k}≡ X (j+1) := by
      rintro _ rfl; exact X.up.le (Nat.le_add_right ..)
    exact ((up ..).ne.1 (X.upN _)).trans <| this _ (Nat.add_right_comm ..)

protected theorem Tower.downN (X : Tower F) : ∀ i, downN F i (X (k+i)) = X k
  | 0 => rfl
  | _+1 => (congrArg (fun a => (downN ..) a) X.down).trans (X.downN _)

instance (k : Nat) : NonExpansive (fun X : Tower F => X.val k) := ⟨fun _ _ _ => (· _)⟩

/-- Project a coherent tower to one approximation level. -/
def Tower.proj (k) : Tower F -n> A F k := ⟨(· k), ⟨fun _ _ _ => (· _)⟩⟩

/-- Transport an approximation along an equality of its level indices. -/
def eqToHom (e : i = k) : A F i -n> A F k := e ▸ .id

theorem eqToHom_up {k k'} {x : A F k} (e : k = k') :
    eqToHom (congrArg Nat.succ e) (up F k x) = up F k' (eqToHom e x) := by
  cases e; rfl

theorem down_eqToHom {k k'} {x : A F (k + 1)} (e : k = k') :
    down F k' (eqToHom (congrArg Nat.succ e) x) = eqToHom e (down F k x) := by
  cases e; rfl

/-- Embed or retract between any two approximation levels. -/
def embed : A F k -n> A F i :=
  if h : k ≤ i then (eqToHom (Nat.add_sub_cancel' h)).comp (upN ..)
  else (downN ..).comp (eqToHom (Nat.add_sub_cancel' (Nat.le_of_not_ge h)).symm)

/-- Extend one approximation to a coherent tower. -/
protected def Tower.embed (k) : A F k -n> Tower F := by
  refine ⟨fun n => ⟨fun _ => embed n, fun {i} => ?_⟩, ⟨fun _ _ _ h _ => embed.ne.1 h⟩⟩
  dsimp [embed]; split <;> rename_i h₁
  · split <;> rename_i h₂
    · suffices ∀ a b (e₁ : k+a = i+1) (e₂ : k+b = i),
        down F i (eqToHom e₁ (upN F a n)) = eqToHom e₂ (upN F b n) from this _ _ _ _
      rintro a _ eq rfl
      rw [Nat.add_assoc, Nat.add_left_cancel_iff] at eq; subst a
      exact down_up _
    · cases (Nat.lt_or_eq_of_le h₁).resolve_left (h₂ ∘ Nat.lt_succ_iff.1)
      have {a b} (e₁ : i+1+a = i+1) (e₂ : i+1 = i+b) :
          down F i (eqToHom e₁ (upN F a n)) = downN F b (eqToHom e₂ n) := by
        cases Nat.add_left_cancel (k := 0) e₁; cases Nat.add_left_cancel e₂
        rfl
      apply this
  · rw [dite_eq_right (mt Nat.le_succ_of_le h₁)]
    suffices ∀ k a b (e₁ : k = i+1+a) (e₂ : k = i+b) (n : A F k),
        down F i (downN F a (eqToHom e₁ n)) = downN F b (eqToHom e₂ n) from this _ _ _ _ _ _
    rintro k a b eq rfl n
    rw [Nat.add_assoc, Nat.add_left_cancel_iff, Nat.add_comm] at eq; subst eq
    change _ = downN F a (down F (i+a) n)
    induction a with
    | zero => rfl
    | succ a ih =>
      dsimp [downN, Hom.comp]
      rw [down_eqToHom (Nat.add_right_comm i a 1)]
      apply ih

theorem Tower.embed_up (x : A F k) :
    Tower.embed (k+1) (up F k x) = Tower.embed k x := by
  refine OFE.eq_dist_2 (fun (n : Nat) i => ?_)
  dsimp [Tower.embed, embed]; split <;> rename_i h₁
  · simp only [Hom.comp_apply, Nat.le_of_succ_le h₁, ↓reduceDIte]
    suffices ∀ a b (e₁ : k + 1 + a = i) (e₂ : k+b = i),
      eqToHom e₁ (upN F a (up F k x)) = eqToHom e₂ (upN F b x) from this .. ▸ .rfl
    rintro a b eq rfl
    rw [Nat.add_right_comm, Nat.add_assoc, Nat.add_left_cancel_iff] at eq; subst b
    change _ = up F (k + a) (upN F a x); clear h₁
    induction a with
    | zero => rfl
    | succ a ih =>
      dsimp [upN, Hom.comp]
      rw [eqToHom_up (by omega : k + 1 + a = k + (a + 1))]; congr 1; apply ih
  · split <;> rename_i h₂
    · cases Nat.le_antisymm h₂ (Nat.not_lt.1 h₁)
      have {a b} {e₁ : k+1 = k+a} {e₂ : k+b = k+0} :
        downN F a (eqToHom e₁ (up F k x)) ≡{n}≡ eqToHom e₂ (upN F b x) := by
        cases Nat.add_left_cancel e₁; cases Nat.add_left_cancel e₂
        exact (down_up _).dist
      exact this
    · dsimp [Hom.comp]
      suffices ∀ a b (e₁ : k + 1 = i + a) (e₂ : k = i + b),
        downN F a (eqToHom e₁ (up F k x)) ≡{n}≡
        downN F b (eqToHom e₂ x) from this ..
      rintro a b eq rfl; cases Nat.add_left_cancel (m := b+1) eq
      exact (downN ..).ne.1 (down_up x).dist

theorem Tower.embed_self (X : Tower F) :
    Tower.embed (k+1) (X (k+1)) ≡{k}≡ X := by
  refine fun i => ?_
  dsimp [Tower.embed, embed]; split <;> rename_i h₁
  · refine ((eqToHom _).ne.1 (X.upN _)).trans ?_
    suffices ∀ a e, eqToHom e (X a) = X i from this .. ▸ .rfl
    rintro _ rfl; rfl
  · suffices ∀ a e, downN F a (eqToHom e (X (k + 1))) ≡{k}≡ X i from this ..
    rintro (_|a) eq
    · cases show k+1=i from eq; exact .rfl
    · cases show k=i+a from Nat.succ.inj eq
      exact (X.downN _).dist

instance : Inhabited (Tower F) := ⟨Tower.embed 0 ⟨()⟩⟩

/-- The Cauchy chain of functor images used to unfold a coherent tower. -/
def unfoldChain (X : Tower F) : Chain (F (Tower F) (Tower F)) where
  chain n := map (Tower.proj _) (Tower.embed _) (X (n+1))
  cauchy {n i} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
    induction k with
    | zero => exact .rfl
    | succ k ih =>
      exact (((map ..).ne.1 X.up).le (Nat.le_add_right ..)).symm.trans <|
        (map_comp _ _ _ _ _).dist.symm.trans <|
        (map_ne.ne (·.down.dist) (fun Y => (Tower.embed_up Y).dist) _).trans ih

/-- The explicit isomorphism between a coherent tower and its functor image. -/
def Tower.isoAux : OFE.Iso (F (Tower F) (Tower F)) (Tower F) where
  hom.f X := {
    val n := (down F n).comp (map (Tower.embed _) (Tower.proj _)) X
    down {n} := OFE.eq_dist_2 fun m => (down ..).ne.1 <|
      (map_comp _ _ _ _ _).dist.symm.trans <|
        map_ne.ne (fun Y => (Tower.embed_up Y).dist) (fun Y => Y.down.dist) _
  }
  hom.ne.1 _ _ _ h _ := by dsimp only; exact (Hom.ne _).1 h
  inv.f X := compl (unfoldChain X)
  inv.ne.1 n _ _ h := by
    refine conv_compl.trans <| .trans ?_ conv_compl.symm
    exact (map ..).ne.1 (h (n+1))
  hom_inv {X} := OFE.eq_dist_2 fun n => by
    intro k
    refine ((down ..).ne.1 (.trans ?_ (X.downN n).dist)).trans X.down.dist
    refine ((map ..).ne.1 (conv_compl.trans
      ((unfoldChain ..).cauchy (show n ≤ k+n+1 by omega)).symm)).trans ?_
    refine (((map ..).comp _).ne.1 (X.up.le (Nat.le_add_left ..)).symm).trans ?_
    refine ((map_comp _ _ _ _ _).trans
      (congrArg (fun a => (map ..) a) (map_comp _ _ _ _ _))).symm.dist.trans ?_
    refine .trans (y := map (upN F n) (downN F n) (X (k+n+1))) ?_ ?_
    · refine map_ne.ne (fun Y => ?_) (fun Y => ?_) _
      · simp only [Hom.comp, proj, Tower.embed, embed, Function.comp_apply, (by omega : k ≤ k + n
          + 1), ↓reduceDIte]
        have {a e} : down F (k + n) (eqToHom e (upN F a Y)) = upN F n Y := by
          cases Nat.add_left_cancel (k := n+1) e; exact down_up _
        exact this.dist
      · simp only [Hom.comp, proj, Tower.embed, embed, Function.comp_apply, show ¬k + n + 1 ≤ k by
          omega, ↓reduceDIte]
        have {a e} : downN F a (eqToHom e (up F (k + n) Y)) = downN F n Y := by
          cases Nat.add_left_cancel (m := n+1) e; exact congrArg (fun a => (downN ..) a) (down_up _)
        exact this.dist
    · have e : k+n+1 = k+1+n := by omega
      suffices ∀ x y, eqToHom e x = y → ∀ m, map (upN F n) (downN F n) x ≡{m}≡ downN F n y by
        refine this _ _ ?_ n
        clear this; revert e; generalize k+1+n = a; rintro rfl; rfl
      rintro x _ rfl m
      induction n with
      | zero => exact (map_id _).dist
      | succ n ih =>
        refine (map_comp _ _ _ _ _).dist.trans <|
          (ih (Nat.succ.inj e) _).trans (congrArg (fun a => (downN ..) a) ?_).dist
        exact (down_eqToHom _).symm
  inv_hom := OFE.eq_dist_2 fun n => by
    refine (conv_compl' n.le_succ).trans ?_
    dsimp [unfoldChain]; rw [down]
    refine ((map_comp _ _ _ _ _).trans
      (congrArg (fun a => (map ..) a) (map_comp _ _ _ _ _))).dist.symm.trans ?_
    refine (map_ne.ne (fun Y => ?_) (fun Y => ?_) _).trans (map_id _).dist
    · exact ((Tower.embed _).ne.1 Y.up).trans (Y.embed_self.le (by omega))
    · exact ((Tower.embed _).ne.1 Y.down.dist).trans Y.embed_self

/-- The tower isomorphism, kept irreducible during elaboration. -/
@[irreducible] def Tower.iso : OFE.Iso (F (Tower F) (Tower F)) (Tower F) := Tower.isoAux

end Fix.Impl
open Fix.Impl

variable (F) in
/-- The recursive domain constructed as a tower of finite approximations. -/
def Fix : Type u := Tower F

instance : Inhabited (Fix F) := inferInstanceAs (Inhabited (Tower F))
instance : COFE (Fix F) := inferInstanceAs (COFE (Tower F))

/-- The isomorphism from the functor image to the constructed recursive domain. -/
def Fix.iso : OFE.Iso (F (Fix F) (Fix F)) (Fix F) := Tower.iso

/-- Fold a functor value into the constructed recursive domain. -/
def Fix.fold : F (Fix F) (Fix F) -n> Fix F := Fix.iso.hom

/-- Unfold a recursive-domain value into its functor image. -/
def Fix.unfold : Fix F -n> F (Fix F) (Fix F) := Fix.iso.inv
theorem Fix.fold_unfold (X : Fix F) : Fix.fold (Fix.unfold X) = X := Fix.iso.hom_inv
theorem Fix.unfold_fold (X : F (Fix F) (Fix F)) : Fix.unfold (Fix.fold X) = X :=
  Fix.iso.inv_hom

attribute [irreducible] Fix Fix.fold Fix.unfold Fix.iso

end OFunctor

end COFE

end Iris
