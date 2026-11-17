/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConePersistence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentRestrictions
public import LeanPool.TuringConeRigidity.Computability.JumpProperties
public import LeanPool.TuringConeRigidity.SetModels.CountableBound
public import LeanPool.TuringConeRigidity.TuringConeRigidity

/-!
# Countable restrictions of cone isomorphisms

This is the countable-hull part of the proposed cone version of persistence.
The target of a restriction is `I ∩ Ici a`, not `I`: a principal cone is not
an ordinary downward-closed degree ideal.

From a global `e : Degree ≃o Set.Ici a` and any countable seed, we construct a
countable ideal closed under jump, the forward map, and `pullback e`. Its
restriction is an isomorphism onto its intersection with the cone. Every
restriction of a global cone isomorphism is persistent, and has persistent
jump-closed extensions containing any prescribed countable set.

This does NOT assert that an arbitrary persistent partial cone isomorphism
has an arithmetic presentation or extends to a forcing extension. Those are
separate remaining obligations in the representation argument.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePersistence

open Set ConeRigidity PersistentRestrictions OracleJump

noncomputable section

/-- The part of a countable ideal above the fixed base degree. -/
abbrev Cone (I : CountableIdeal) (a : Degree) :=
  {x : Degree // x ∈ I.carrier ∧ a ≤ x}

/-- The countable ideal is closed under the Turing jump. -/
def JumpClosed (I : CountableIdeal) : Prop :=
  ∀ x ∈ I.carrier, degreeJump x ∈ I.carrier

@[simp] theorem pullback_image {a : Degree} (e : Degree ≃o Set.Ici a)
    (x : Degree) : pullback e (e x).val = x := by
  apply e.injective
  apply Subtype.ext
  rw [apply_pullback_val]
  exact sup_eq_right.mpr (Set.mem_Ici.mp (e x).property)

/-- One closure step. Including jump here avoids any assumption that `e`
preserves jump. -/
def closureStep {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree) : Set Degree :=
  S ∪ ((fun x => (e x).val) '' S ∪ (pullback e '' S ∪
    (degreeJump '' S ∪ (Set.image2 (· ⊔ ·) S S ∪ ⋃ x ∈ S, Set.Iic x))))

theorem countable_closureStep {a : Degree} (e : Degree ≃o Set.Ici a)
    {S : Set Degree} (hS : S.Countable) : (closureStep e S).Countable :=
  hS.union ((hS.image (fun x => (e x).val)).union ((hS.image (pullback e)).union
    ((hS.image degreeJump).union ((hS.image2 hS (· ⊔ ·)).union
      (hS.biUnion fun x _ => countable_principal_lower x)))))

/-- The stages closing the seed and cone base under the cone-persistence operations. -/
def stage {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree) : ℕ → Set Degree
  | 0 => insert a S
  | n + 1 => closureStep e (stage e S n)

theorem countable_stage {a : Degree} (e : Degree ≃o Set.Ici a)
    {S : Set Degree} (hS : S.Countable) : ∀ n, (stage e S n).Countable
  | 0 => hS.insert a
  | n + 1 => countable_closureStep e (countable_stage e hS n)

theorem stage_mono {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree) :
    Monotone (stage e S) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  exact Or.inl hx

/-- The union of all cone-persistence closure stages. -/
def hullSet {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree) : Set Degree :=
  ⋃ n, stage e S n

theorem base_mem_hullSet {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree) :
    a ∈ hullSet e S := Set.mem_iUnion.mpr ⟨0, Or.inl rfl⟩

theorem subset_hullSet {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree) :
    S ⊆ hullSet e S := fun _ hx => Set.mem_iUnion.mpr ⟨0, Or.inr hx⟩

theorem hullSet_lower {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree)
    {x y : Degree} (hxy : x ≤ y) (hy : y ∈ hullSet e S) : x ∈ hullSet e S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
  refine Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hn, Set.mem_Iic.mpr hxy⟩⟩

theorem hullSet_join {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree)
    {x y : Degree} (hx : x ∈ hullSet e S) (hy : y ∈ hullSet e S) :
    x ⊔ y ∈ hullSet e S := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
  refine Set.mem_iUnion.mpr ⟨max m n + 1,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
  exact ⟨x, stage_mono e S (le_max_left m n) hm,
    y, stage_mono e S (le_max_right m n) hn, rfl⟩

theorem hullSet_forward {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree)
    {x : Degree} (hx : x ∈ hullSet e S) : (e x).val ∈ hullSet e S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inl ⟨x, hn, rfl⟩)⟩

theorem hullSet_backward {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree)
    {x : Degree} (hx : x ∈ hullSet e S) : pullback e x ∈ hullSet e S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inr (Or.inl ⟨x, hn, rfl⟩))⟩

theorem hullSet_jump {a : Degree} (e : Degree ≃o Set.Ici a) (S : Set Degree)
    {x : Degree} (hx : x ∈ hullSet e S) : degreeJump x ∈ hullSet e S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hn, rfl⟩)))⟩

/-- The countable invariant jump-closed ideal generated by the seed for the cone isomorphism. -/
def invariantJumpHull {a : Degree} (e : Degree ≃o Set.Ici a)
    (S : Set Degree) (hS : S.Countable) : CountableIdeal where
  carrier := hullSet e S
  nonempty := ⟨a, base_mem_hullSet e S⟩
  countable := Set.countable_iUnion (countable_stage e hS)
  lower := fun {_ _} hxy hy => hullSet_lower e S hxy hy
  join_mem := fun {_ _} hx hy => hullSet_join e S hx hy

theorem countable_invariant_jump_hull {a : Degree} (e : Degree ≃o Set.Ici a)
    (S : Set Degree) (hS : S.Countable) :
    ∃ I : CountableIdeal, S ⊆ I.carrier ∧ a ∈ I.carrier ∧ JumpClosed I ∧
      (∀ x ∈ I.carrier, (e x).val ∈ I.carrier) ∧
      (∀ x ∈ I.carrier, pullback e x ∈ I.carrier) :=
  ⟨invariantJumpHull e S hS, subset_hullSet e S, base_mem_hullSet e S,
    fun _ hx => hullSet_jump e S hx, fun _ hx => hullSet_forward e S hx,
    fun _ hx => hullSet_backward e S hx⟩

/-- Restrict a global cone isomorphism to an invariant ideal. -/
def restrict {a : Degree} (e : Degree ≃o Set.Ici a) (I : CountableIdeal)
    (hf : ∀ x ∈ I.carrier, (e x).val ∈ I.carrier)
    (hb : ∀ x ∈ I.carrier, pullback e x ∈ I.carrier) : I ≃o Cone I a where
  toFun x := ⟨(e x.val).val, hf x.val x.property, Set.mem_Ici.mp (e x.val).property⟩
  invFun y := ⟨pullback e y.val, hb y.val y.property.1⟩
  left_inv x := Subtype.ext (pullback_image e x.val)
  right_inv y := Subtype.ext ((apply_pullback_val e y.val).trans
    (sup_eq_right.mpr y.property.2))
  map_rel_iff' := by
    intro x y
    change (e x.val).val ≤ (e y.val).val ↔ x.val ≤ y.val
    exact e.le_iff_le

/-- The global isomorphism agrees on the ideal with the given ideal-to-cone isomorphism. -/
def RestrictsTo {a : Degree} (e : Degree ≃o Set.Ici a) (I : CountableIdeal)
    (ρ : I ≃o Cone I a) : Prop := ∀ x : I, (e x.val).val = (ρ x).val

/-- The isomorphism on the larger ideal agrees with the smaller cone isomorphism on its
domain. -/
def Extends {a : Degree} {I J : CountableIdeal} (hIJ : I.carrier ⊆ J.carrier)
    (ρ : I ≃o Cone I a) (σ : J ≃o Cone J a) : Prop :=
  ∀ x : I, (σ ⟨x.val, hIJ x.property⟩).val = (ρ x).val

/-- Every degree belongs to a larger countable ideal carrying an extension of the cone
isomorphism. -/
def Persistent {a : Degree} (I : CountableIdeal) (ρ : I ≃o Cone I a) : Prop :=
  ∀ x : Degree, ∃ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier)
    (σ : J ≃o Cone J a), x ∈ J.carrier ∧ Extends hIJ ρ σ

/-- Forward agreement of two restrictions entails inverse agreement as well. -/
theorem extends_inverse {a : Degree} {I J : CountableIdeal}
    {hIJ : I.carrier ⊆ J.carrier} {ρ : I ≃o Cone I a} {σ : J ≃o Cone J a}
    (h : Extends hIJ ρ σ) (y : Cone I a) :
    (σ.symm ⟨y.val, hIJ y.property.1, y.property.2⟩).val = (ρ.symm y).val := by
  have he : σ ⟨(ρ.symm y).val, hIJ (ρ.symm y).property⟩ =
      ⟨y.val, hIJ y.property.1, y.property.2⟩ := by
    apply Subtype.ext
    exact (h (ρ.symm y)).trans (congrArg Subtype.val (ρ.apply_symm_apply y))
  have hi := congrArg (fun z => (σ.symm z).val) he
  simpa only [σ.symm_apply_apply] using hi.symm

theorem extends_trans {a : Degree} {I J K : CountableIdeal}
    {hIJ : I.carrier ⊆ J.carrier} {hJK : J.carrier ⊆ K.carrier}
    {ρ : I ≃o Cone I a} {σ : J ≃o Cone J a} {τ : K ≃o Cone K a}
    (hρσ : Extends hIJ ρ σ) (hστ : Extends hJK σ τ) :
    Extends (hIJ.trans hJK) ρ τ := by
  intro x
  exact (hστ ⟨x.val, hIJ x.property⟩).trans (hρσ x)

/-- No definability or regularity is assumed in this persistence lemma. -/
theorem persistent_of_global_restriction {a : Degree} (e : Degree ≃o Set.Ici a)
    (I : CountableIdeal) (ρ : I ≃o Cone I a) (hρ : RestrictsTo e I ρ) :
    Persistent I ρ := by
  intro x
  obtain ⟨J, hS, _, _, hf, hb⟩ := countable_invariant_jump_hull e
    (insert x I.carrier) (I.countable.insert x)
  let hIJ : I.carrier ⊆ J.carrier := fun _ hx => hS (Or.inr hx)
  exact ⟨J, hIJ, restrict e J hf hb, hS (Or.inl rfl), fun y => hρ y⟩

/-- Persistence already permits any countable collection of degrees to be
included in an extension, by bounding it by one degree. This alone does not
assert that the extension is persistent or jump-closed. -/
theorem persistent_countable_extension {a : Degree} (I : CountableIdeal)
    (ρ : I ≃o Cone I a) (hp : Persistent I ρ) (S : Set Degree) (hS : S.Countable) :
    ∃ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (σ : J ≃o Cone J a),
      S ⊆ J.carrier ∧ Extends hIJ ρ σ := by
  obtain ⟨b, hb⟩ := CountableBound.countable_bounded S hS
  obtain ⟨J, hIJ, σ, hbJ, he⟩ := hp b
  exact ⟨J, hIJ, σ, fun x hx => J.lower (hb x hx) hbJ, he⟩

/-- A restriction of a global map has a persistent, jump-closed extension
containing an arbitrary countable seed. -/
theorem persistent_countable_jump_extension {a : Degree} (e : Degree ≃o Set.Ici a)
    (I : CountableIdeal) (ρ : I ≃o Cone I a) (hρ : RestrictsTo e I ρ)
    (S : Set Degree) (hS : S.Countable) :
    ∃ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (σ : J ≃o Cone J a),
      S ⊆ J.carrier ∧ a ∈ J.carrier ∧ JumpClosed J ∧ Extends hIJ ρ σ ∧
      RestrictsTo e J σ ∧ Persistent J σ := by
  obtain ⟨J, h, ha, hj, hf, hb⟩ := countable_invariant_jump_hull e
    (I.carrier ∪ S) (I.countable.union hS)
  let σ := restrict e J hf hb
  have hσ : RestrictsTo e J σ := fun _ => rfl
  exact ⟨J, fun _ hx => h (Or.inl hx), σ, fun _ hx => h (Or.inr hx), ha, hj,
    fun x => hρ x, hσ, persistent_of_global_restriction e J σ hσ⟩

/-- The starting countable persistent cone isomorphisms needed in a
model-theoretic argument can always be obtained from a global one. -/
theorem countable_persistent_restriction {a : Degree} (e : Degree ≃o Set.Ici a)
    (S : Set Degree) (hS : S.Countable) :
    ∃ (I : CountableIdeal) (ρ : I ≃o Cone I a),
      S ⊆ I.carrier ∧ a ∈ I.carrier ∧ JumpClosed I ∧
      RestrictsTo e I ρ ∧ Persistent I ρ := by
  obtain ⟨I, hS, ha, hj, hf, hb⟩ := countable_invariant_jump_hull e S hS
  let ρ := restrict e I hf hb
  have hρ : RestrictsTo e I ρ := fun _ => rfl
  exact ⟨I, ρ, hS, ha, hj, hρ, persistent_of_global_restriction e I ρ hρ⟩

end
end OAI.TuringRigidity.ConePersistence
