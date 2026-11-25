/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum

/-!
# Almost invariant submodules are close to invariant submodules

`d A B` is the length of `A / (A ∩ B)`. For vector spaces it is the dimension.
-/

@[expose] public section

open Submodule

namespace AlmostInvariant

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The length of `A / (A ∩ B)`. -/
noncomputable def d (A B : Submodule R M) : ℕ∞ := Module.length R (A ⧸ B.submoduleOf A)

theorem d_inf (A B : Submodule R M) : d A (A ⊓ B) = d A B := by
  have : (A ⊓ B).submoduleOf A = B.submoduleOf A := by
    ext x; simp [Submodule.submoduleOf]
  rw [d, d, this]

theorem d_sup (A B : Submodule R M) : d (A ⊔ B) B = d A B := by
  rw [← d_inf A B, d, d]
  exact (LinearMap.quotientInfEquivSupQuotient A B).length_eq.symm

theorem d_eq_zero {A B : Submodule R M} : d A B = 0 ↔ A ≤ B := by
  rw [d, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, Submodule.submoduleOf,
    Submodule.comap_subtype_eq_top]

/-- Additivity along a chain. -/
theorem d_add {A B C : Submodule R M} (hBC : C ≤ B) (hAB : B ≤ A) : d A C = d A B + d B C := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hBC
  let f : (B ⧸ C.submoduleOf B) →ₗ[R] (A ⧸ C.submoduleOf A) :=
    Submodule.mapQ _ _ (Submodule.inclusion hAB) (by
      intro x hx
      simpa [Submodule.submoduleOf] using hx)
  let g : (A ⧸ C.submoduleOf A) →ₗ[R] (A ⧸ B.submoduleOf A) := Submodule.factor hle
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hx : (Submodule.inclusion hAB x : A) ∈ C.submoduleOf A := by
      simpa [f, Submodule.Quotient.mk_eq_zero] using hm
    rw [Submodule.Quotient.mk_eq_zero]
    simpa [Submodule.submoduleOf] using hx
  have hg : Function.Surjective g := Submodule.factor_surjective hle
  have hfg : Function.Exact f g := by
    intro m
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    constructor
    · intro hm
      have hx : x ∈ B.submoduleOf A := by
        simpa [g, Submodule.Quotient.mk_eq_zero] using hm
      refine ⟨Submodule.Quotient.mk ⟨(x : M), by simpa [Submodule.submoduleOf] using hx⟩, ?_⟩
      simp only [f, Submodule.mapQ_apply]
      congr 1
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← hy]
      have : (Submodule.inclusion hAB y : A) ∈ B.submoduleOf A := by simp [Submodule.submoduleOf]
      simpa [f, g, Submodule.Quotient.mk_eq_zero] using this
  rw [d, d, d, Module.length_eq_add_of_exact f g hf hg hfg, add_comm]

theorem d_mono_left {A A' B : Submodule R M} (h : A ≤ A') : d A B ≤ d A' B := by
  rw [← d_sup A B, ← d_sup A' B,
    d_add (A := A' ⊔ B) (B := A ⊔ B) (C := B) le_sup_right (sup_le_sup_right h B)]
  exact le_add_self

theorem d_anti_right {A B B' : Submodule R M} (h : B ≤ B') : d A B' ≤ d A B := by
  rw [← d_inf A B, ← d_inf A B',
    d_add (A := A) (B := A ⊓ B') (C := A ⊓ B) (inf_le_inf_left A h) inf_le_left]
  exact le_self_add

/-- Modularity: the two sides of the diamond below `A`. -/
theorem d_modular_below {A X Y : Submodule R M} (hX : X ≤ A) (hY : Y ≤ A) :
    d A (X ⊓ Y) + d A (X ⊔ Y) = d A X + d A Y := by
  have h1 : d A (X ⊓ Y) = d A X + d X (X ⊓ Y) := d_add inf_le_left hX
  have h2 : d A Y = d A (X ⊔ Y) + d (X ⊔ Y) Y := d_add le_sup_right (sup_le hX hY)
  rw [h1, h2, d_sup, d_inf]
  ring

/-- Modularity: the two sides of the diamond above `A`. -/
theorem d_modular_above {A X Y : Submodule R M} (hX : A ≤ X) (hY : A ≤ Y) :
    d (X ⊔ Y) A + d (X ⊓ Y) A = d X A + d Y A := by
  have h1 : d (X ⊔ Y) A = d (X ⊔ Y) Y + d Y A := d_add hY le_sup_right
  have h2 : d X A = d X (X ⊓ Y) + d (X ⊓ Y) A := d_add (le_inf hX hY) inf_le_left
  rw [h1, h2, d_sup, d_inf]
  ring

/-- The symmetric distance. -/
noncomputable def delta (A B : Submodule R M) : ℕ∞ := d A B + d B A

theorem delta_comm (A B : Submodule R M) : delta A B = delta B A := add_comm _ _

/-- `S ↦ delta A S` is submodular. -/
theorem delta_submodular (A S T : Submodule R M) :
    delta A (S ⊓ T) + delta A (S ⊔ T) ≤ delta A S + delta A T := by
  have h1 : d A (S ⊓ T) + d A (S ⊔ T) ≤ d A S + d A T := by
    have := d_modular_below (A := A) (X := A ⊓ S) (Y := A ⊓ T) inf_le_left inf_le_left
    rw [d_inf, d_inf, ← inf_inf_distrib_left, d_inf] at this
    rw [← this]
    gcongr
    rw [← d_inf A (S ⊔ T)]
    exact d_anti_right (le_inf (sup_le inf_le_left inf_le_left)
      (sup_le_sup inf_le_right inf_le_right))
  have h2 : d (S ⊓ T) A + d (S ⊔ T) A ≤ d S A + d T A := by
    have := d_modular_above (A := A) (X := S ⊔ A) (Y := T ⊔ A) le_sup_right le_sup_right
    rw [d_sup, d_sup] at this
    have e : (S ⊔ A) ⊔ (T ⊔ A) = (S ⊔ T) ⊔ A := by
      rw [sup_sup_sup_comm, sup_idem]
    rw [e, d_sup] at this
    rw [← this, add_comm]
    gcongr
    rw [← d_sup (S ⊓ T) A]
    exact d_mono_left (sup_le (inf_le_inf le_sup_left le_sup_left) (le_inf le_sup_right
        le_sup_right))
  calc delta A (S ⊓ T) + delta A (S ⊔ T)
      = (d A (S ⊓ T) + d A (S ⊔ T)) + (d (S ⊓ T) A + d (S ⊔ T) A) := by
        simp only [delta]; ring
    _ ≤ (d A S + d A T) + (d S A + d T A) := add_le_add h1 h2
    _ = delta A S + delta A T := by simp only [delta]; ring

/-- The submodules of `A / (A ∩ B)` are the submodules between `A ∩ B` and `A`. -/
noncomputable def intervalIso (A B : Submodule R M) :
    Submodule R (A ⧸ B.submoduleOf A) ≃o Set.Icc (A ⊓ B) A :=
  (Submodule.comapMkQRelIso (B.submoduleOf A)).trans
    { toFun := fun S => ⟨S.1.map A.subtype, by
        refine ⟨?_, Submodule.map_subtype_le _ _⟩
        rintro x ⟨hxA, hxB⟩
        exact ⟨⟨x, hxA⟩, S.2 (by simpa [Submodule.submoduleOf] using hxB), rfl⟩⟩
      invFun := fun S => ⟨S.1.submoduleOf A, by
        intro x hx
        exact S.2.1 ⟨x.2, by simpa [Submodule.submoduleOf] using hx⟩⟩
      left_inv := fun S => by
        ext x
        simp [Submodule.submoduleOf]
      right_inv := fun S => by
        ext x
        simp only [Submodule.submoduleOf, Submodule.mem_map, Submodule.mem_comap,
            Submodule.subtype_apply]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, S.2.2 hx⟩, hx, rfl⟩
      map_rel_iff' := by
        rintro ⟨S, hS⟩ ⟨T, hT⟩
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk]
        exact Submodule.map_le_map_iff_of_injective A.injective_subtype S T }

theorem d_eq_krullDim (A B : Submodule R M) : (d A B : WithBot ℕ∞) = Order.krullDim (Set.Icc (A ⊓
    B) A) := by
  rw [d, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (intervalIso A B)

/-- An automorphism of the lattice of submodules keeps `d`. In particular a semilinear
automorphism of the module does. -/
theorem d_map (e : Submodule R M ≃o Submodule R M) (A B : Submodule R M) : d (e A) (e B)
    = d A B := by
  have h : (d (e A) (e B) : WithBot ℕ∞) = d A B := by
    rw [d_eq_krullDim, d_eq_krullDim, ← OrderIso.map_inf]
    refine (Order.krullDim_eq_of_orderIso ?_).symm
    exact
      { toFun := fun S => ⟨e S.1, e.monotone S.2.1, e.monotone S.2.2⟩
        invFun := fun S => ⟨e.symm S.1, by rw [e.le_symm_apply]; exact S.2.1,
            by rw [e.symm_apply_le]; exact S.2.2⟩
        left_inv := fun S => by simp
        right_inv := fun S => by simp
        map_rel_iff' := by
          rintro ⟨S, hS⟩ ⟨T, hT⟩
          exact e.le_iff_le }
  exact_mod_cast h

theorem delta_map (e : Submodule R M ≃o Submodule R M) (A B : Submodule R M) : delta (e A) (e B)
    = delta A B := by
  simp only [delta, d_map]

/-- Two comparable submodules with the same finite distances to `U` are equal. -/
theorem eq_of_d_eq {S S' U : Submodule R M} (h : S' ≤ S) (h1 : d U S = d U S') (h2 : d S' U = d S U)
    (f1 : d U S ≠ ⊤) (f2 : d S U ≠ ⊤) : S' = S := by
  have e1 : d U S' = d U S + d (U ⊓ S) (U ⊓ S') := by
    rw [← d_inf U S', ← d_inf U S]
    exact d_add (inf_le_inf_left U h) inf_le_left
  have e2 : d S U = d (S ⊔ U) (S' ⊔ U) + d S' U := by
    rw [← d_sup S U, ← d_sup S' U]
    exact d_add le_sup_right (sup_le_sup_right h U)
  have z1 : d (U ⊓ S) (U ⊓ S') = 0 := by
    rw [← h1] at e1
    have : d U S + 0 = d U S + d (U ⊓ S) (U ⊓ S') := by rw [add_zero]; exact e1
    exact (WithTop.add_left_cancel f1 this).symm
  have z2 : d (S ⊔ U) (S' ⊔ U) = 0 := by
    rw [h2] at e2
    have : 0 + d S U = d (S ⊔ U) (S' ⊔ U) + d S U := by rw [zero_add]; exact e2
    exact (WithTop.add_right_cancel f2 this).symm
  rw [d_eq_zero] at z1 z2
  refine eq_of_le_of_inf_le_of_sup_le (z := U) h ?_ z2
  rw [inf_comm, inf_comm S']
  exact z1

theorem d_self (A : Submodule R M) : d A A = 0 := d_eq_zero.mpr le_rfl

/-- The directed triangle inequality. -/
theorem d_triangle (X Y Z : Submodule R M) : d X Z ≤ d X Y + d Y Z := by
  calc d X Z = d X (X ⊓ Z) := (d_inf X Z).symm
    _ ≤ d X (X ⊓ Y ⊓ Z) := d_anti_right (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    _ = d X (X ⊓ Y) + d (X ⊓ Y) (X ⊓ Y ⊓ Z) := d_add inf_le_left inf_le_left
    _ ≤ d X Y + d Y Z := by
      rw [d_inf, d_inf]
      gcongr
      exact d_mono_left inf_le_right

end AlmostInvariant
