/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConePersistence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeRigidity
public import LeanPool.TuringConeRigidity.TuringConePersistence

/-!
# Initial persistence infrastructure for maps between two cones

Partial maps have the symmetric type `Cone I a ≃o Cone I b`, where `I` is
an ordinary downward-closed countable degree ideal. Closing a countable seed
under both joined maps, join, jump and downward reducibility constructs
persistent restrictions of any global two-cone isomorphism. No arithmetic
presentation or generic representative is assumed or concluded here.
-/


@[expose] public section


namespace OAI.TuringRigidity.TwoConePersistence

open Set PersistentRestrictions OracleJump
open TwoConeRigidity
open ConePersistence (Cone JumpClosed)

noncomputable section

theorem pullback_imageJoin {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (x : Degree) : pullback e (imageJoin e x) = a ⊔ x := by
  simpa only [pullback, OrderIso.symm_symm] using apply_pullback_val e.symm x

def closureStep {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (S : Set Degree) : Set Degree :=
  S ∪ (imageJoin e '' S ∪ (pullback e '' S ∪
    (degreeJump '' S ∪ (Set.image2 (· ⊔ ·) S S ∪ ⋃ x ∈ S, Set.Iic x))))

theorem countable_closureStep {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    {S : Set Degree} (hS : S.Countable) : (closureStep e S).Countable :=
  hS.union ((hS.image (imageJoin e)).union ((hS.image (pullback e)).union
    ((hS.image degreeJump).union ((hS.image2 hS (· ⊔ ·)).union
      (hS.biUnion fun x _ => countable_principal_lower x)))))

def stage {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (S : Set Degree) : ℕ → Set Degree
  | 0 => insert a (insert b S)
  | n + 1 => closureStep e (stage e S n)

theorem countable_stage {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    {S : Set Degree} (hS : S.Countable) : ∀ n, (stage e S n).Countable
  | 0 => (hS.insert b).insert a
  | n + 1 => countable_closureStep e (countable_stage e hS n)

theorem stage_mono {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree) :
    Monotone (stage e S) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  exact Or.inl hx

def hullSet {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree) : Set Degree :=
  ⋃ n, stage e S n

theorem source_mem_hullSet {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree) :
    a ∈ hullSet e S := Set.mem_iUnion.mpr ⟨0, Or.inl rfl⟩

theorem target_mem_hullSet {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree) :
    b ∈ hullSet e S := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inl rfl)⟩

theorem subset_hullSet {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree) :
    S ⊆ hullSet e S := fun _ hx => Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inr hx)⟩

theorem hullSet_lower {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree)
    {x y : Degree} (hxy : x ≤ y) (hy : y ∈ hullSet e S) : x ∈ hullSet e S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
  refine Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hn, Set.mem_Iic.mpr hxy⟩⟩

theorem hullSet_join {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree)
    {x y : Degree} (hx : x ∈ hullSet e S) (hy : y ∈ hullSet e S) :
    x ⊔ y ∈ hullSet e S := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
  refine Set.mem_iUnion.mpr ⟨max m n + 1,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
  exact ⟨x, stage_mono e S (le_max_left m n) hm,
    y, stage_mono e S (le_max_right m n) hn, rfl⟩

theorem hullSet_forward {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree)
    {x : Degree} (hx : x ∈ hullSet e S) : imageJoin e x ∈ hullSet e S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inl ⟨x, hn, rfl⟩)⟩

theorem hullSet_backward {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree)
    {x : Degree} (hx : x ∈ hullSet e S) : pullback e x ∈ hullSet e S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inr (Or.inl ⟨x, hn, rfl⟩))⟩

theorem hullSet_jump {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (S : Set Degree)
    {x : Degree} (hx : x ∈ hullSet e S) : degreeJump x ∈ hullSet e S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hn, rfl⟩)))⟩

def invariantJumpHull {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (S : Set Degree) (hS : S.Countable) : CountableIdeal where
  carrier := hullSet e S
  nonempty := ⟨a, source_mem_hullSet e S⟩
  countable := Set.countable_iUnion (countable_stage e hS)
  lower := fun {_ _} hxy hy => hullSet_lower e S hxy hy
  join_mem := fun {_ _} hx hy => hullSet_join e S hx hy

theorem countable_invariant_jump_hull {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (S : Set Degree) (hS : S.Countable) :
    ∃ I : CountableIdeal, S ⊆ I.carrier ∧ a ∈ I.carrier ∧ b ∈ I.carrier ∧
      JumpClosed I ∧ (∀ x ∈ I.carrier, imageJoin e x ∈ I.carrier) ∧
      (∀ x ∈ I.carrier, pullback e x ∈ I.carrier) :=
  ⟨invariantJumpHull e S hS, subset_hullSet e S, source_mem_hullSet e S,
    target_mem_hullSet e S, fun _ hx => hullSet_jump e S hx,
    fun _ hx => hullSet_forward e S hx, fun _ hx => hullSet_backward e S hx⟩

/-- Neither side is an ordinary ideal: both are intersections with a cone. -/
def restrict {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (I : CountableIdeal)
    (hf : ∀ x ∈ I.carrier, imageJoin e x ∈ I.carrier)
    (hb : ∀ x ∈ I.carrier, pullback e x ∈ I.carrier) : Cone I a ≃o Cone I b where
  toFun x := ⟨imageJoin e x.val, hf x.val x.property.1,
    (e (ConeRigidity.coneJoin a x.val)).property⟩
  invFun y := ⟨pullback e y.val, hb y.val y.property.1, base_le_pullback e y.val⟩
  left_inv x := Subtype.ext ((pullback_imageJoin e x.val).trans
    (sup_eq_right.mpr x.property.2))
  right_inv y := Subtype.ext ((apply_pullback_val e y.val).trans
    (sup_eq_right.mpr y.property.2))
  map_rel_iff' := by
    intro x y
    change e (ConeRigidity.coneJoin a x.val) ≤ e (ConeRigidity.coneJoin a y.val) ↔
      x.val ≤ y.val
    rw [e.le_iff_le]
    change a ⊔ x.val ≤ a ⊔ y.val ↔ x.val ≤ y.val
    rw [sup_eq_right.mpr x.property.2, sup_eq_right.mpr y.property.2]

def RestrictsTo {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (I : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b) : Prop :=
  ∀ x : Cone I a, imageJoin e x.val = (ρ x).val

def Extends {a b : Degree} {I J : CountableIdeal} (hIJ : I.carrier ⊆ J.carrier)
    (ρ : Cone I a ≃o Cone I b) (σ : Cone J a ≃o Cone J b) : Prop :=
  ∀ x : Cone I a, (σ ⟨x.val, hIJ x.property.1, x.property.2⟩).val = (ρ x).val

def Persistent {a b : Degree} (I : CountableIdeal) (ρ : Cone I a ≃o Cone I b) : Prop :=
  ∀ x : Degree, ∃ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier)
    (σ : Cone J a ≃o Cone J b), x ∈ J.carrier ∧ Extends hIJ ρ σ

theorem extends_inverse {a b : Degree} {I J : CountableIdeal}
    {hIJ : I.carrier ⊆ J.carrier} {ρ : Cone I a ≃o Cone I b}
    {σ : Cone J a ≃o Cone J b} (h : Extends hIJ ρ σ) (y : Cone I b) :
    (σ.symm ⟨y.val, hIJ y.property.1, y.property.2⟩).val = (ρ.symm y).val := by
  have he : σ ⟨(ρ.symm y).val, hIJ (ρ.symm y).property.1, (ρ.symm y).property.2⟩ =
      ⟨y.val, hIJ y.property.1, y.property.2⟩ := by
    apply Subtype.ext
    exact (h (ρ.symm y)).trans (congrArg Subtype.val (ρ.apply_symm_apply y))
  have hi := congrArg (fun z => (σ.symm z).val) he
  simpa only [σ.symm_apply_apply] using hi.symm

theorem extends_trans {a b : Degree} {I J K : CountableIdeal}
    {hIJ : I.carrier ⊆ J.carrier} {hJK : J.carrier ⊆ K.carrier}
    {ρ : Cone I a ≃o Cone I b} {σ : Cone J a ≃o Cone J b}
    {τ : Cone K a ≃o Cone K b} (hρσ : Extends hIJ ρ σ) (hστ : Extends hJK σ τ) :
    Extends (hIJ.trans hJK) ρ τ := by
  intro x
  exact (hστ ⟨x.val, hIJ x.property.1, x.property.2⟩).trans (hρσ x)

theorem persistent_of_global_restriction {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (I : CountableIdeal) (ρ : Cone I a ≃o Cone I b) (hρ : RestrictsTo e I ρ) :
    Persistent I ρ := by
  intro x
  obtain ⟨J, hS, _, _, _, hf, hb⟩ := countable_invariant_jump_hull e
    (insert x I.carrier) (I.countable.insert x)
  let hIJ : I.carrier ⊆ J.carrier := fun _ hx => hS (Or.inr hx)
  exact ⟨J, hIJ, restrict e J hf hb, hS (Or.inl rfl), fun y => hρ y⟩

theorem persistent_countable_extension {a b : Degree} (I : CountableIdeal)
    (ρ : Cone I a ≃o Cone I b) (hp : Persistent I ρ)
    (S : Set Degree) (hS : S.Countable) :
    ∃ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (σ : Cone J a ≃o Cone J b),
      S ⊆ J.carrier ∧ Extends hIJ ρ σ := by
  obtain ⟨c, hc⟩ := CountableBound.countable_bounded S hS
  obtain ⟨J, hIJ, σ, hcJ, he⟩ := hp c
  exact ⟨J, hIJ, σ, fun x hx => J.lower (hc x hx) hcJ, he⟩

/-- Starting partial maps for the later model-theoretic representation proof. -/
theorem countable_persistent_restriction {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (S : Set Degree) (hS : S.Countable) :
    ∃ (I : CountableIdeal) (ρ : Cone I a ≃o Cone I b),
      S ⊆ I.carrier ∧ a ∈ I.carrier ∧ b ∈ I.carrier ∧ JumpClosed I ∧
      RestrictsTo e I ρ ∧ Persistent I ρ := by
  obtain ⟨I, hS, ha, hb, hj, hf, hback⟩ := countable_invariant_jump_hull e S hS
  let ρ := restrict e I hf hback
  have hρ : RestrictsTo e I ρ := fun _ => rfl
  exact ⟨I, ρ, hS, ha, hb, hj, hρ, persistent_of_global_restriction e I ρ hρ⟩

end
end OAI.TuringRigidity.TwoConePersistence
