/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Multiplicative
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Defs
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Division

/-!
# Division conic algebras (`GPR 8.6`, `GPR 13.8`)

A conic algebra can fall short of being a division algebra in the sense of `GPR 8.6` (`IsDivision`:
nonzero, with bijective left and right multiplications by nonzero elements) in two ways: its norm
may have a nonzero null vector, or — without alternativity — a two-sided inverse may fail to make
the multiplications bijective. This file compares the three conditions

* `IsDivision A`,
* `C.HasTwoSidedInverses` (every nonzero element has a two-sided inverse),
* `C.norm.Anisotropic`,

over a field. Without any hypothesis on the multiplication, division implies anisotropy, and
anisotropy implies two-sided inverses (`n(x)⁻¹ (conj x)`). For an **alternative** conic algebra all
three agree, once `A ≠ 0`: that is `GPR 13.8` for conic algebras. The real sedenions show that the
alternativity hypothesis cannot be dropped (`ConicAlgebra.not_isDivision_realSedenion`,
`GPR Exc. 19.29(e)`).

The engine is the pair of identities `(conj x) (x y) = n(x) y = (y x) (conj x)`, which hold in every
alternative conic algebra: write `conj x = t(x)·1 - x` and apply the alternative laws and
`x² = t(x) x - n(x)·1`. So when `n(x)` is invertible, `n(x)⁻¹ (conj x)` inverts left and right
multiplication by `x`.

## Main results

* `ConicAlgebra.conj_mul_mul_of_isAlternative`, `ConicAlgebra.mul_mul_conj_of_isAlternative` :
  `(conj x) (x y) = n(x) y` and `(y x) (conj x) = n(x) y` in an alternative conic algebra.
* `ConicAlgebra.anisotropic_of_isDivision` : a division conic algebra has anisotropic norm.
* `ConicAlgebra.hasTwoSidedInverses_of_anisotropic` : over a field, an anisotropic norm gives
  two-sided inverses. No alternativity is needed.
* `ConicAlgebra.anisotropic_of_hasTwoSidedInverses` : for an alternative conic algebra, two-sided
  inverses force the norm to be anisotropic.
* `ConicAlgebra.isDivision_of_anisotropic` : over a field, a nonzero alternative conic algebra with
  anisotropic norm is a division algebra.
* `ConicAlgebra.isDivision_iff_hasTwoSidedInverses`, `ConicAlgebra.isDivision_iff_anisotropic` :
  **`GPR 13.8`** for alternative conic algebras over a field.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 8.6, 13.8,
  Exc. 19.29.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

section CommRing

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] (C : ConicAlgebra k A)

omit [SMulCommClass k A A] in
/-- In an alternative conic algebra, `(conj x) (x y) = n(x) y`: expand `conj x = t(x)·1 - x`, use
the left alternative law `x (x y) = (x x) y`, and the degree-two identity `x x = t(x) x - n(x)·1`.
-/
theorem conj_mul_mul_of_isAlternative [IsAlternative A] (x y : A) :
    C.conj x * (x * y) = C.norm x • y := by
  rw [C.conj_apply, sub_mul, smul_mul_assoc, one_mul, IsAlternative.mul_mul_self_left,
    C.mul_self_eq, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  abel

omit [IsScalarTower k A A] in
/-- In an alternative conic algebra, `(y x) (conj x) = n(x) y`, by the right alternative law. -/
theorem mul_mul_conj_of_isAlternative [IsAlternative A] (x y : A) :
    (y * x) * C.conj x = C.norm x • y := by
  rw [C.conj_apply, mul_sub, mul_smul_comm, mul_one, IsAlternative.mul_self_mul_right,
    C.mul_self_eq, mul_sub, mul_smul_comm, mul_smul_comm, mul_one]
  abel

omit [SMulCommClass k A A] in
/-- `x ((conj x) y) = n(x) y`: the identity `conj_mul_mul_of_isAlternative` for `conj x`. -/
theorem mul_conj_mul_of_isAlternative [IsAlternative A] (x y : A) :
    x * (C.conj x * y) = C.norm x • y := by
  simpa only [C.conj_conj, C.norm_conj] using C.conj_mul_mul_of_isAlternative (C.conj x) y

omit [IsScalarTower k A A] in
/-- `(y (conj x)) x = n(x) y`: the identity `mul_mul_conj_of_isAlternative` for `conj x`. -/
theorem mul_conj_mul_conj_of_isAlternative [IsAlternative A] (x y : A) :
    (y * C.conj x) * x = C.norm x • y := by
  simpa only [C.conj_conj, C.norm_conj] using C.mul_mul_conj_of_isAlternative (C.conj x) y

omit [IsScalarTower k A A] in
/-- **A division conic algebra has anisotropic norm.** If `n(x) = 0` then `x (conj x) = n(x)·1 = 0`,
and `conj x ≠ 0` when `x ≠ 0`, so `x` would be a zero divisor. No alternativity is needed. -/
theorem anisotropic_of_isDivision (h : IsDivision A) : C.norm.Anisotropic := by
  intro x hx
  by_contra hx0
  have hc : C.conj x ≠ 0 := fun h0 ↦ hx0 <| by
    simpa only [C.conj_conj, map_zero] using congrArg C.conj h0
  have hmul : x * C.conj x = 0 := by rw [C.mul_conj_self, hx, zero_smul]
  exact (h.eq_zero_or_eq_zero_of_mul_eq_zero hmul).elim hx0 hc

omit [SMulCommClass k A A] in
/-- **For an alternative conic algebra, two-sided inverses force an anisotropic norm.** If `x y = 1`
and `n(x) = 0`, then `conj x = (conj x) (x y) = n(x) y = 0`, so `x = 0`. Only the one-sided inverse
`x y = 1` is used. -/
theorem anisotropic_of_hasTwoSidedInverses [IsAlternative A] (h : C.HasTwoSidedInverses) :
    C.norm.Anisotropic := by
  intro x hx
  by_contra hx0
  obtain ⟨y, hxy, -⟩ := h hx0
  have hc : C.conj x = 0 := by
    have := C.conj_mul_mul_of_isAlternative x y
    rwa [hxy, mul_one, hx, zero_smul] at this
  exact hx0 (by simpa only [C.conj_conj, map_zero] using congrArg C.conj hc)

end CommRing

section Field

variable {K : Type u} {A : Type v} [Field K] [NonAssocRing A] [Module K A]
  [SMulCommClass K A A] [IsScalarTower K A A] (C : ConicAlgebra K A)

/-- **Over a field, an anisotropic norm gives two-sided inverses**: `n(x)⁻¹ (conj x)` inverts any
nonzero `x`. Only `x (conj x) = (conj x) x = n(x)·1` is used, so neither alternativity nor
associativity is needed — and the result is correspondingly weak: see
`ConicAlgebra.HasTwoSidedInverses`. -/
theorem hasTwoSidedInverses_of_anisotropic (h : C.norm.Anisotropic) : C.HasTwoSidedInverses := by
  intro x hx
  have hn : C.norm x ≠ 0 := fun h0 ↦ hx (h x h0)
  refine ⟨(C.norm x)⁻¹ • C.conj x, ?_, ?_⟩
  · rw [mul_smul_comm, C.mul_conj_self, smul_smul, inv_mul_cancel₀ hn, one_smul]
  · rw [smul_mul_assoc, C.conj_mul_self, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Over a field, a division conic algebra has two-sided inverses. -/
theorem hasTwoSidedInverses_of_isDivision (h : IsDivision A) : C.HasTwoSidedInverses :=
  C.hasTwoSidedInverses_of_anisotropic (C.anisotropic_of_isDivision h)

/-- **Over a field, a nonzero alternative conic algebra with anisotropic norm is a division
algebra** in the sense of `GPR 8.6`. For `u ≠ 0` the scalar `n(u)` is invertible, and
`v ↦ n(u)⁻¹ ((conj u) v)` and `v ↦ n(u)⁻¹ (v (conj u))` invert left and right multiplication by `u`,
by the identities `(conj x) (x y) = n(x) y = x ((conj x) y)` and
`(y x) (conj x) = n(x) y = (y (conj x)) x`. -/
theorem isDivision_of_anisotropic [IsAlternative A] [Nontrivial A] (h : C.norm.Anisotropic) :
    IsDivision A where
  nontrivial := inferInstance
  bijective_mul_left u hu := by
    have hn : C.norm u ≠ 0 := fun h0 ↦ hu (h u h0)
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun v ↦ (C.norm u)⁻¹ • (C.conj u * v), fun v ↦ ?_, fun v ↦ ?_⟩
    · change (C.norm u)⁻¹ • (C.conj u * (u * v)) = v
      rw [C.conj_mul_mul_of_isAlternative, smul_smul, inv_mul_cancel₀ hn, one_smul]
    · change u * ((C.norm u)⁻¹ • (C.conj u * v)) = v
      rw [mul_smul_comm, C.mul_conj_mul_of_isAlternative, smul_smul, inv_mul_cancel₀ hn,
        one_smul]
  bijective_mul_right u hu := by
    have hn : C.norm u ≠ 0 := fun h0 ↦ hu (h u h0)
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun v ↦ (C.norm u)⁻¹ • (v * C.conj u), fun v ↦ ?_, fun v ↦ ?_⟩
    · change (C.norm u)⁻¹ • ((v * u) * C.conj u) = v
      rw [C.mul_mul_conj_of_isAlternative, smul_smul, inv_mul_cancel₀ hn, one_smul]
    · change ((C.norm u)⁻¹ • (v * C.conj u)) * u = v
      rw [smul_mul_assoc, C.mul_conj_mul_conj_of_isAlternative, smul_smul, inv_mul_cancel₀ hn,
        one_smul]

/-- **`GPR 13.8`, for conic algebras over a field.** An alternative conic algebra is a division
algebra in the sense of `GPR 8.6` exactly when it is nonzero and every nonzero element has a
two-sided inverse. Without alternativity only `→` holds: the real sedenions have two-sided inverses
but are not a division algebra (`ConicAlgebra.not_isDivision_realSedenion`). -/
theorem isDivision_iff_hasTwoSidedInverses [IsAlternative A] :
    IsDivision A ↔ Nontrivial A ∧ C.HasTwoSidedInverses :=
  ⟨fun h ↦ ⟨h.nontrivial, C.hasTwoSidedInverses_of_isDivision h⟩, fun ⟨_, h⟩ ↦
    C.isDivision_of_anisotropic (C.anisotropic_of_hasTwoSidedInverses h)⟩

/-- An alternative conic algebra over a field is a division algebra exactly when it is nonzero and
its norm is anisotropic. -/
theorem isDivision_iff_anisotropic [IsAlternative A] :
    IsDivision A ↔ Nontrivial A ∧ C.norm.Anisotropic :=
  ⟨fun h ↦ ⟨h.nontrivial, C.anisotropic_of_isDivision h⟩, fun ⟨_, h⟩ ↦
    C.isDivision_of_anisotropic h⟩

end Field

end ConicAlgebra
