/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index

/-!
# Cardinality bounds for `n`-torsion in finite commutative groups

The `n`-torsion subgroup of a commutative group `G` is `(powMonoidHom n : G →* G).ker`.

## Main results

* `MonoidHom.card_powMonoidHom_ker_le_of_surjective`: a surjection does not increase the
  `n`-torsion.
* `MonoidHom.card_powMonoidHom_ker_le_mul`: the `n`-torsion of `G` is bounded by the
  `n`-torsion of the kernel of `φ : G →* H` times the `n`-torsion of `H`.
* `MonoidHom.card_powMonoidHom_ker_le_of_coset_cover`: a subgroup covered by finitely many
  cosets of the image of `φ` has `m`-torsion bounded by the `m`-torsion of the source times the
  number of cosets.
-/

@[expose] public section

namespace MonoidHom

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- Power torsion maps functorially under a group homomorphism. -/
def powMonoidHomKerMap (φ : G →* H) (n : ℕ) :
    (powMonoidHom n : G →* G).ker →* (powMonoidHom n : H →* H).ker where
  toFun x := ⟨φ x, by
    change (φ x.val) ^ n = 1
    rw [← map_pow, show x.val ^ n = 1 from x.property, map_one]⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' x y := Subtype.ext (map_mul φ _ _)

/-- A surjective homomorphism does not increase the number of `n`-torsion elements. -/
theorem card_powMonoidHom_ker_le_of_surjective [Finite G] [Finite H]
    (φ : G →* H) (hφ : Function.Surjective φ) (n : ℕ) :
    Nat.card (powMonoidHom n : H →* H).ker ≤
      Nat.card (powMonoidHom n : G →* G).ker := by
  have hpow : (powMonoidHom n : G →* G).range ≤
      ((powMonoidHom n : H →* H).range).comap φ := by
    rintro x ⟨y, rfl⟩
    exact ⟨φ y, (map_pow φ y n).symm⟩
  have hq := QuotientGroup.map_surjective_of_surjective
    (powMonoidHom n : G →* G).range (powMonoidHom n : H →* H).range φ
    (QuotientGroup.mk_surjective.comp hφ) hpow
  have hc := Nat.card_le_card_of_surjective _ hq
  simpa only [← Subgroup.index_eq_card, Subgroup.index_range] using hc

/-- The torsion of the middle group is bounded by the torsion of a
homomorphism's kernel and the torsion of its target. -/
theorem card_powMonoidHom_ker_le_mul [Finite G] [Finite H]
    (φ : G →* H) (n : ℕ) :
    Nat.card (powMonoidHom n : G →* G).ker ≤
      Nat.card (powMonoidHom n : φ.ker →* φ.ker).ker *
        Nat.card (powMonoidHom n : H →* H).ker := by
  let ψ := powMonoidHomKerMap φ n
  let j : ψ.ker → (powMonoidHom n : φ.ker →* φ.ker).ker :=
    fun x ↦ ⟨⟨x.val.val, by
      have hx := congrArg Subtype.val x.property
      exact hx⟩, by
        apply Subtype.ext
        exact x.val.property⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (powMonoidHom n : φ.ker →* φ.ker).ker ↦ z.val.val) h
  have hk := Nat.card_le_card_of_injective j hj
  have hr := Subgroup.card_le_card_group ψ.range
  calc
    Nat.card (powMonoidHom n : G →* G).ker = Nat.card ψ.ker * Nat.card ψ.range :=
      (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ _ := Nat.mul_le_mul hk hr

/-- A subgroup covered by finitely many cosets of the image of `φ` has `m`-torsion bounded by the
`m`-torsion of the source times the number of cosets. -/
theorem card_powMonoidHom_ker_le_of_coset_cover
    {A G ι : Type*} [CommGroup A] [CommGroup G] [Finite A] [Finite G] [Fintype ι]
    (φ : A →* G) (S : Subgroup G) (c : ι → G)
    (hcover : ∀ x : S, ∃ a : A, ∃ i : ι, x.val = φ a * c i)
    (m : ℕ) :
    Nat.card (powMonoidHom m : S →* S).ker ≤
      Nat.card (powMonoidHom m : A →* A).ker * Fintype.card ι := by
  let π := QuotientGroup.mk' φ.range
  let ψ : S →* G ⧸ φ.range := π.comp S.subtype
  let δ := ψ.rangeRestrict
  have hφ (a : A) : π (φ a) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have hex (r : ψ.range) : ∃ i : ι, r.val = π (c i) := by
    obtain ⟨x, hx⟩ := r.property
    obtain ⟨a, i, he⟩ := hcover x
    refine ⟨i, ?_⟩
    rw [← hx]
    change π x.val = _
    rw [he, map_mul, hφ, one_mul]
  choose i hi using hex
  have hinj : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    rw [hi x, hi y, h]
  have hrange : Nat.card ψ.range ≤ Fintype.card ι := by
    simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective i hinj
  let j : δ.ker →* φ.range :=
    { toFun := fun x ↦ ⟨x.val.val, by
        have hh := congrArg Subtype.val x.property
        change QuotientGroup.mk x.val.val = 1 at hh
        exact (QuotientGroup.eq_one_iff _).mp hh⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ ↦ Subtype.ext rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : φ.range ↦ z.val) h
  have hjtor : Function.Injective (powMonoidHomKerMap j m) := by
    intro x y h
    apply Subtype.ext
    apply hj
    exact congrArg Subtype.val h
  have hker :
      Nat.card (powMonoidHom m : δ.ker →* δ.ker).ker ≤
        Nat.card (powMonoidHom m : A →* A).ker :=
    (Nat.card_le_card_of_injective _ hjtor).trans
      (card_powMonoidHom_ker_le_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective m)
  have hr : Nat.card (powMonoidHom m : ψ.range →* ψ.range).ker ≤ Fintype.card ι :=
    (Subgroup.card_le_card_group _).trans hrange
  exact (card_powMonoidHom_ker_le_mul δ m).trans (Nat.mul_le_mul hker hr)

end MonoidHom
