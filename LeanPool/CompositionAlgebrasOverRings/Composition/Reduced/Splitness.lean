/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.BaseChange
public import LeanPool.CompositionAlgebrasOverRings.Composition.NormClassification
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Defs
public import LeanPool.CompositionAlgebrasOverRings.Module.RankDecomposition

/-!
# Split composition algebras (`GPR 21.19`)

`GPR 21.19` first defines a composition algebra of constant rank `1`, `2`, `4`, or `8` to be
**split** when it is isomorphic to the corresponding standard model: `k`, `k × k`, `Mat₂(k)`,
or `Zor(k)`. For a composition algebra whose rank varies across `Spec k`, it then applies this
condition to the four factors of the rank decomposition (`GPR Exc. 9.31`).

This file formalizes both levels. Since mathlib's `AlgEquiv` requires associative multiplication,
an isomorphism of conic algebras is expressed by a norm isometry which preserves `1` and
multiplication. This is the same representation used by `Composition/NormClassification.lean`.

## Main definitions

* `ConicAlgebra.Isomorphic` : existence of a unital multiplicative norm isometry.
* `ConicAlgebra.IsSplitOfRank` : the four constant-rank clauses of `GPR 21.19`.
* `ConicAlgebra.SplitRankFactor`, `ConicAlgebra.splitRankComponent` : the factor ring and
  base-changed conic algebra cut out by a rank idempotent.
* `ConicAlgebra.IsSplit` : the composition property together with splitness on all four rank
  components.

## Main results

* `ConicAlgebra.Isomorphic.refl`, `.symm`, `.trans` : conic-algebra isomorphism is an equivalence
  relation.
* `ConicAlgebra.Isomorphic.of_subsingleton` : over the zero ring, any two conic algebras are
  isomorphic.
* `ConicAlgebra.Isomorphic.isComposition` : composition transports across an isomorphism.
* `ConicAlgebra.isSplitOfRank_baseRing`, `.isSplitOfRank_splitEtale`,
  `.isSplitOfRank_splitQuaternion`, `.isSplitOfRank_zor` : the four standard models are split.
* `ConicAlgebra.IsSplitOfRank.hasElementaryIdempotent_of_two_or_four_or_eight` : the
  constant-rank form of the easy direction of `GPR 22.16`.

## Implementation notes

`IsSplitOfRank C r` does not separately store the assertion that `C` has rank `r`: an isomorphism
to the standard model already forces that equality. The general predicate uses the quotients

`k ⧸ (1 - rankIdempotent k A r)`

for `r = 1, 2, 4, 8`, exactly as in the rank decomposition. Zero factors are retained, as in
`GPR 21.19`; this also handles the zero base ring without a separate definition.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Exc. 9.31,
  21.19, 22.16.
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace ConicAlgebra

variable {k : Type u} {A : Type v} {B : Type w} [CommRing k]
  [NonAssocRing A] [Module k A] [SMulCommClass k A A] [IsScalarTower k A A]
  [NonAssocRing B] [Module k B] [SMulCommClass k B B] [IsScalarTower k B B]

/-- Two conic algebras are **isomorphic** when there is a norm isometry preserving `1` and
multiplication.

⚠ Mathlib's `AlgEquiv` is not used because the algebras need not be associative. -/
def Isomorphic (C : ConicAlgebra k A) (D : ConicAlgebra k B) : Prop :=
  ∃ e : C.norm.IsometryEquiv D.norm,
    e (1 : A) = 1 ∧ ∀ x y, e (x * y) = e x * e y

namespace Isomorphic

variable {C : ConicAlgebra k A} {D : ConicAlgebra k B}

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] in
/-- Over a subsingleton base ring, any two conic algebras are isomorphic. Their underlying
modules, the norm values, and all algebra elements are subsingletons. -/
theorem of_subsingleton [Subsingleton k] : C.Isomorphic D := by
  let : Subsingleton A := Module.subsingleton k A
  let : Subsingleton B := Module.subsingleton k B
  exact ⟨⟨LinearEquiv.ofSubsingleton A B, fun _ ↦ Subsingleton.elim _ _⟩,
    Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- A conic algebra is isomorphic to itself. -/
@[refl] theorem refl (C : ConicAlgebra k A) : C.Isomorphic C :=
  ⟨QuadraticMap.IsometryEquiv.refl C.norm, rfl, fun _ _ ↦ rfl⟩

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] in
/-- The inverse of an isomorphism of conic algebras. -/
@[symm] theorem symm (h : C.Isomorphic D) : D.Isomorphic C := by
  obtain ⟨e, he1, hmul⟩ := h
  refine ⟨e.symm, ?_, fun x y ↦ ?_⟩
  · apply e.injective
    simp [he1]
  · apply e.injective
    change e (e.symm (x * y)) = e (e.symm x * e.symm y)
    rw [e.apply_symm_apply, hmul, e.apply_symm_apply, e.apply_symm_apply]

variable {E : Type t} [NonAssocRing E] [Module k E] [SMulCommClass k E E]
  [IsScalarTower k E E] {G : ConicAlgebra k E}

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] [SMulCommClass k E E] [IsScalarTower k E E] in
/-- The composite of two isomorphisms of conic algebras. -/
@[trans] theorem trans (hCD : C.Isomorphic D) (hDG : D.Isomorphic G) : C.Isomorphic G := by
  obtain ⟨e, he1, hemul⟩ := hCD
  obtain ⟨f, hf1, hfmul⟩ := hDG
  refine ⟨e.trans f, ?_, fun x y ↦ ?_⟩
  · change f (e (1 : A)) = 1
    rw [he1, hf1]
  · change f (e (x * y)) = f (e x) * f (e y)
    rw [hemul, hfmul]

variable [Module.Finite k A] [Module.Projective k A]
  [Module.Finite k B] [Module.Projective k B]

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] in
/-- Composition transports backwards across an isomorphism of conic algebras. -/
theorem isComposition (h : C.Isomorphic D) (hD : D.IsComposition.{u, w, t}) :
    C.IsComposition.{u, v, t} := by
  obtain ⟨e, -, hmul⟩ := h
  refine ⟨?_, fun x y ↦ ?_⟩
  · have hnorm : C.norm = D.norm.comp e.toLinearEquiv.toLinearMap :=
      QuadraticMap.ext fun x ↦ (e.map_app x).symm
    rw [hnorm]
    exact hD.isGPRNonsingular.comp_linearEquiv e.toLinearEquiv
  · calc
      C.norm (x * y) = D.norm (e (x * y)) := (e.map_app (x * y)).symm
      _ = D.norm (e x * e y) := congrArg D.norm (hmul x y)
      _ = D.norm (e x) * D.norm (e y) := hD.norm_mul (e x) (e y)
      _ = C.norm x * C.norm y := by rw [e.map_app, e.map_app]

end Isomorphic

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] in
/-- A unital norm isometry carries elementary idempotents to elementary idempotents. -/
theorem IsElementaryIdempotent.map_isometryEquiv {C : ConicAlgebra k A}
    {D : ConicAlgebra k B} {c : A} (hc : C.IsElementaryIdempotent c)
    (e : C.norm.IsometryEquiv D.norm) (he1 : e (1 : A) = 1) :
    D.IsElementaryIdempotent (e c) where
  norm_eq_zero := by rw [e.map_app, hc.norm_eq_zero]
  trace_eq_one := by rw [trace_map_of_isometryEquiv_map_one C D e he1, hc.trace_eq_one]

omit [SMulCommClass k A A] [IsScalarTower k A A] [SMulCommClass k B B]
  [IsScalarTower k B B] in
/-- Having an elementary idempotent is invariant under conic-algebra isomorphism. -/
theorem Isomorphic.hasElementaryIdempotent_iff {C : ConicAlgebra k A}
    {D : ConicAlgebra k B} (h : C.Isomorphic D) :
    C.HasElementaryIdempotent ↔ D.HasElementaryIdempotent := by
  obtain ⟨e, he1, -⟩ := h
  have he1' : e.symm (1 : B) = 1 := by
    apply e.injective
    simp [he1]
  exact ⟨fun ⟨c, hc⟩ ↦ ⟨e c, hc.map_isometryEquiv e he1⟩,
    fun ⟨d, hd⟩ ↦ ⟨e.symm d, hd.map_isometryEquiv e.symm he1'⟩⟩

/-! ### Constant-rank splitness -/

variable (C : ConicAlgebra k A)

/-- **`GPR 21.19(a)–(d)`.** A conic algebra is split of rank `r` if it is isomorphic to the
standard model of rank `r`. The predicate is false for ranks other than `1`, `2`, `4`, and `8`.

This definition is intended for composition algebras; `Isomorphic.isComposition` shows that being
isomorphic to one of the standard models supplies the composition laws. -/
def IsSplitOfRank : ℕ → Prop
  | 1 => C.Isomorphic (baseRing k)
  | 2 => C.Isomorphic (splitEtale k)
  | 4 => C.Isomorphic (splitQuaternion k)
  | 8 => C.Isomorphic (zor k)
  | _ => False

variable {C}

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem isSplitOfRank_one_iff : C.IsSplitOfRank 1 ↔ C.Isomorphic (baseRing k) :=
  Iff.rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem isSplitOfRank_two_iff : C.IsSplitOfRank 2 ↔ C.Isomorphic (splitEtale k) :=
  Iff.rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem isSplitOfRank_four_iff :
    C.IsSplitOfRank 4 ↔ C.Isomorphic (splitQuaternion k) :=
  Iff.rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem isSplitOfRank_eight_iff : C.IsSplitOfRank 8 ↔ C.Isomorphic (zor k) :=
  Iff.rfl

section StandardModels

variable (k : Type u) [CommRing k]

/-- The standard rank-one composition algebra is split of rank one. -/
theorem isSplitOfRank_baseRing : (baseRing k).IsSplitOfRank 1 :=
  Isomorphic.refl _

/-- The split quadratic étale algebra is split of rank two. -/
theorem isSplitOfRank_splitEtale : (splitEtale k).IsSplitOfRank 2 :=
  Isomorphic.refl _

/-- The split quaternion algebra is split of rank four. -/
theorem isSplitOfRank_splitQuaternion : (splitQuaternion k).IsSplitOfRank 4 :=
  Isomorphic.refl _

/-- The Zorn vector matrix algebra is split of rank eight. -/
theorem isSplitOfRank_zor : (zor k).IsSplitOfRank 8 :=
  Isomorphic.refl _

end StandardModels

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **`GPR 22.16`, constant-rank easy direction.** A split algebra of rank `2`, `4`, or `8` has
an elementary idempotent. The three standard models have visible elementary idempotents, and the
property is transported back across the defining isomorphism. -/
theorem IsSplitOfRank.hasElementaryIdempotent_of_two_or_four_or_eight {r : ℕ}
    (h : C.IsSplitOfRank r) (hr : r = 2 ∨ r = 4 ∨ r = 8) :
    C.HasElementaryIdempotent := by
  rcases hr with rfl | rfl | rfl
  · exact h.hasElementaryIdempotent_iff.mpr (hasElementaryIdempotent_splitEtale k)
  · exact h.hasElementaryIdempotent_iff.mpr (hasElementaryIdempotent_splitQuaternion k)
  · exact h.hasElementaryIdempotent_iff.mpr (hasElementaryIdempotent_zor k)

/-! ### Splitness through the rank decomposition -/

variable [Module.Finite k A] [Module.Projective k A]

/-- The factor of the base ring on which `A` has constant rank `r` (`GPR Exc. 9.31`). -/
abbrev SplitRankFactor (k : Type u) (A : Type v) [CommRing k] [AddCommGroup A] [Module k A]
    [Module.Finite k A] [Module.Projective k A] (r : ℕ) :=
  k ⧸ Ideal.span {1 - Module.rankIdempotent k A r}

/-- The conic algebra on the rank-`r` factor of the rank decomposition. -/
noncomputable def splitRankComponent (C : ConicAlgebra k A) (r : ℕ) :
    ConicAlgebra (SplitRankFactor k A r) ((SplitRankFactor k A r) ⊗[k] A) :=
  C.baseChangeOfProjective (SplitRankFactor k A r)

/-- **`GPR 21.19`, general splitness.** A conic algebra is split when each of its rank `1`, `2`,
`4`, and `8` components is isomorphic to the corresponding standard split composition algebra.

The composition hypothesis is included because `GPR 21.19` defines splitness only for
composition algebras; it also ensures through `GPR 19.18` that these four idempotent factors
exhaust the base. -/
def IsSplit (C : ConicAlgebra k A) : Prop :=
  C.IsComposition.{u, v, u} ∧ (C.splitRankComponent 1).IsSplitOfRank 1 ∧
    (C.splitRankComponent 2).IsSplitOfRank 2 ∧
    (C.splitRankComponent 4).IsSplitOfRank 4 ∧
    (C.splitRankComponent 8).IsSplitOfRank 8

/-- A split conic algebra is a composition algebra, by definition. -/
theorem IsSplit.isComposition {C : ConicAlgebra k A} (h : C.IsSplit) :
    C.IsComposition.{u, v, u} :=
  h.1

end ConicAlgebra
