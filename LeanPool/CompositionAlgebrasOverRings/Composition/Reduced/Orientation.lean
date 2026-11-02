/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.ConstantRank
public import LeanPool.CompositionAlgebrasOverRings.Module.AlternatingBaseChange
public import LeanPool.CompositionAlgebrasOverRings.Module.ExteriorPower
public import LeanPool.CompositionAlgebrasOverRings.Module.RankDecomposition
public import LeanPool.CompositionAlgebrasOverRings.Module.VectorProduct
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Oriented rank-three projective modules (`GPR 22.14`)

An orientation `θ : ⋀³ M ≃ k` of a finite projective module of constant rank three induces
the two associated vector products used to define twisted Zorn vector matrices. To prove
Binet–Cauchy over an arbitrary commutative ring, we localize at each maximal ideal. The localized
module is free of rank three, while base change for projective duals identifies its dual with the
localized dual. The primal and dual volume coefficients multiply to one by the determinant
identity from `GPR 21.7`; the based calculation then applies. Descent from all maximal
localizations proves the global identity.

Conversely, on such a module **every** vector-product pair is `ofOrientation` of exactly one
orientation, namely its volume form `u ∧ v ∧ w ↦ ⟨u × v, w⟩`. Base change along any commutative
`k`-algebra carries a pair to a pair (`Module.VectorProductPair.baseChange`, with the dual handled
by `GPR 9.15`). At a maximal ideal the module is free, so the base-changed pair is the pair of a
basis (`Module.VectorProductPair.exists_eq_ofBasis`) and its two volume forms multiply to the
determinant of pairings; descending from all maximal ideals gives that triple identity,
`GPR (22.14.1)`, over `k`. The volume form `⋀³ M → k` is then surjective, because on a local basis
its value is a unit, and injective, because by the triple identity and the perfect pairing
`GPR 21.7` every functional on the projective module `⋀³ M` is a multiple of it. Applying the triple
identity once to the pair and once to the dual orientation `θ*⁻¹` identifies the dual products.
`Composition/Reduced/OrientedRankEight.lean` applies this to the Peirce pair of a reduced octonion
algebra (`GPR 22.15`).

⚠ **Orientation** means `GPR`'s notion, a linear isomorphism `⋀³ M ≃ k` (`GPR 21.8`, `22.14`), not
mathlib's `Orientation`, which is a ray of volume forms.

## Main definitions

* `Module.VectorProductPair.ofOrientation` : the pair of associated vector products induced by
  an orientation of a constant-rank-three finite projective module.
* `Module.VectorProductPair.baseChange` : the scalar extension of a vector-product pair on a
  finite projective module.
* `Module.VectorProductPair.orientation` : the orientation `⋀³ M ≃ k` of a vector-product pair on
  a constant-rank-three finite projective module.
* `Module.VectorProductPair.orientationEquiv` : orientations and vector-product pairs correspond.

## Main results

* `Module.VectorProductPair.crossAlternating_mul_crossDualAlternating` : the triple identity
  `GPR (22.14.1)` for an arbitrary pair.
* `Module.VectorProductPair.ofOrientation_orientation` : every pair is induced by its orientation;
  `Module.VectorProductPair.orientation_ofOrientation` : and that orientation is unique.

## Implementation notes

Nothing here involves a composition algebra; the file sits in `Composition/Reduced/` beside its
consumers. Duals are base changed with TauCeti's `TauCeti.Module.Dual.baseChangeEvaluationEquiv`
(`GPR 9.15`).

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 9.15, 21.7, 21.8,
  22.14, 22.15.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module

section OfOrientation

variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]
  [Module.Finite k M] [Module.Projective k M]

/-- **Binet–Cauchy for an orientation.** The vector products induced by an orientation `θ` of a
finite projective module of constant rank three (`GPR 22.14`) satisfy
`⟨v × w, f × g⟩ = ⟨f, v⟩⟨g, w⟩ - ⟨f, w⟩⟨g, v⟩`. It is checked at every maximal ideal, where the
module is free of rank three: the primal and dual volume coefficients of a basis are inverse
(`GPR (22.14.1)`, via the duality `GPR 21.7`), so the based calculation applies. -/
theorem cross_apply_crossDual_of_orientation
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) (v w : M) (f g : Module.Dual k M) :
    crossOfOrientation theta v w (crossDualOfOrientation theta f g) =
      f v * g w - f w * g v := by
  apply sub_eq_zero.mp
  apply eq_zero_of_localization
  intro J hJ
  let S := Localization.AtPrime J
  let MS := TensorProduct k S M
  let e : TensorProduct k S (Module.Dual k M) ≃ₗ[S] Module.Dual S MS :=
    TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := k) (M := M) (A := S)
  let A : MS [⋀^Fin 3]→ₗ[S] S :=
    AlternatingMap.baseChangeAlternatingFinThree (S := S) (orientationAlternating theta)
  let D : TensorProduct k S (Module.Dual k M) [⋀^Fin 3]→ₗ[S] S :=
    AlternatingMap.baseChangeAlternatingFinThree (S := S)
      (dualOrientationAlternating theta)
  let Dt : Module.Dual S MS [⋀^Fin 3]→ₗ[S] S :=
    D.compLinearMap e.symm.toLinearMap
  obtain ⟨b⟩ := nonempty_basis_atPrime_of_rankAtStalk_eq hM J
  let P : VectorProductPair S MS := VectorProductPair.ofBasis b
  let vS : MS := 1 ⊗ₜ[k] v
  let wS : MS := 1 ⊗ₜ[k] w
  let fS : Module.Dual S MS := e (1 ⊗ₜ[k] f)
  let gS : Module.Dual S MS := e (1 ⊗ₜ[k] g)
  let a : S := A b
  let d : S := Dt b.dualBasis
  have he (r s : S) (q : Module.Dual k M) (x : M) :
      e (r ⊗ₜ[k] q) (s ⊗ₜ[k] x) = r * s * algebraMap k S (q x) := by
    rw [TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply,
      TauCeti.Module.Dual.baseChangeEvaluation_tmul]
  have had : a * d = 1 := by
    have h := AlternatingMap.baseChangeFinThree_mul_eq_det
      (S := S) (orientationAlternating theta) (dualOrientationAlternating theta) e he
      (orientationAlternating_mul_dualOrientationAlternating_apply theta)
      (b 0) (b 1) (b 2) (e.symm (b.dualBasis 0))
      (e.symm (b.dualBasis 1)) (e.symm (b.dualBasis 2))
    change a * d = 1
    simpa [a, d, A, D, Dt, AlternatingMap.baseChangeAlternatingFinThree,
      Matrix.det_fin_three] using h
  have hcross (x : MS) :
      e (1 ⊗ₜ[k] crossOfOrientation theta v w) x =
        AlternatingMap.baseChangeFinThree (S := S) (orientationAlternating theta)
          vS wS x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul s x =>
      rw [AlternatingMap.baseChangeFinThree_tmul]
      simp [he, crossOfOrientation_apply]
  have hcrossEq : e (1 ⊗ₜ[k] crossOfOrientation theta v w) =
      a • P.cross vS wS := by
    apply LinearMap.ext
    intro x
    rw [hcross]
    change A ![vS, wS, x] = _
    have h := DFunLike.congr_fun (A.eq_smul_basis_det b) ![vS, wS, x]
    rw [← VectorProductPair.crossAlternating_ofBasis b] at h
    simpa [a, P] using h
  have hcrossDual (h : Module.Dual S MS) :
      h (1 ⊗ₜ[k] crossDualOfOrientation theta f g) = Dt ![fS, gS, h] := by
    let q := e.symm h
    rw [← e.apply_symm_apply h]
    simp only [Dt, D, fS, gS, AlternatingMap.compLinearMap_apply,
      AlternatingMap.baseChangeAlternatingFinThree]
    have hvec : (fun i ↦ e.symm
        (![e (1 ⊗ₜ[k] f), e (1 ⊗ₜ[k] g), e (e.symm h)] i)) =
        ![(1 ⊗ₜ[k] f), (1 ⊗ₜ[k] g), q] := by
      ext i
      fin_cases i <;> simp [q]
    change e (e.symm h) (1 ⊗ₜ[k] crossDualOfOrientation theta f g) =
      AlternatingMap.baseChangeAlternatingFinThree (S := S)
        (dualOrientationAlternating theta)
        (fun i ↦ e.symm (![e (1 ⊗ₜ[k] f), e (1 ⊗ₜ[k] g), e (e.symm h)] i))
    rw [hvec]
    change e q (1 ⊗ₜ[k] crossDualOfOrientation theta f g) =
      AlternatingMap.baseChangeFinThree (S := S) (dualOrientationAlternating theta)
        (1 ⊗ₜ[k] f) (1 ⊗ₜ[k] g) q
    induction q using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul r q =>
      rw [AlternatingMap.baseChangeFinThree_tmul]
      simp [he, apply_crossDualOfOrientation]
  have hcrossDualEq : (1 ⊗ₜ[k] crossDualOfOrientation theta f g : MS) =
      d • P.crossDual fS gS := by
    apply (Module.evalEquiv S MS).injective
    ext h
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply]
    rw [hcrossDual]
    rw [← alternating_fin_three_cycle Dt h fS gS]
    have hdet := DFunLike.congr_fun (Dt.eq_smul_basis_det b.dualBasis) ![h, fS, gS]
    rw [← VectorProductPair.crossDualAlternating_ofBasis b] at hdet
    simpa [d, P] using hdet
  have hleft : algebraMap k S
      (crossOfOrientation theta v w (crossDualOfOrientation theta f g)) =
      e (1 ⊗ₜ[k] crossOfOrientation theta v w)
        (1 ⊗ₜ[k] crossDualOfOrientation theta f g) := by
    symm
    simpa using he 1 1 (crossOfOrientation theta v w)
      (crossDualOfOrientation theta f g)
  rw [map_sub, map_sub, map_mul, map_mul, hleft, hcrossEq, hcrossDualEq]
  simp only [LinearMap.smul_apply, smul_eq_mul, map_smul]
  rw [← mul_assoc, mul_comm d a, had, one_mul]
  rw [P.cross_apply_crossDual]
  simp [fS, gS, vS, wS, he]
  ring

/-- **`GPR 22.14`.** An orientation of a finite projective module of constant rank three over an
arbitrary commutative ring induces its pair of associated vector products. -/
noncomputable def VectorProductPair.ofOrientation
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) : VectorProductPair k M where
  cross := crossOfOrientation theta
  crossDual := crossDualOfOrientation theta
  cross_self v := by
    apply LinearMap.ext
    intro w
    rw [crossOfOrientation_apply]
    exact (orientationAlternating theta).map_eq_zero_of_eq ![v, v, w]
      (by rfl) (show (0 : Fin 3) ≠ 1 by decide)
  crossDual_self f := by
    apply (Module.evalEquiv k M).injective
    ext h
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, map_zero]
    rw [apply_crossDualOfOrientation]
    exact (dualOrientationAlternating theta).map_eq_zero_of_eq ![f, f, h]
      (by rfl) (show (0 : Fin 3) ≠ 1 by decide)
  cross_apply_left v w := by
    rw [crossOfOrientation_apply]
    exact (orientationAlternating theta).map_eq_zero_of_eq ![v, w, v]
      (by rfl) (show (0 : Fin 3) ≠ 2 by decide)
  apply_crossDual_left f g := by
    rw [apply_crossDualOfOrientation]
    exact (dualOrientationAlternating theta).map_eq_zero_of_eq ![f, g, f]
      (by rfl) (show (0 : Fin 3) ≠ 2 by decide)
  cross_apply_crossDual := cross_apply_crossDual_of_orientation hM theta

@[simp] theorem VectorProductPair.ofOrientation_cross
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) :
    (VectorProductPair.ofOrientation hM theta).cross = crossOfOrientation theta := rfl

@[simp] theorem VectorProductPair.ofOrientation_crossDual
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (theta : (⋀[k]^3 M) ≃ₗ[k] k) :
    (VectorProductPair.ofOrientation hM theta).crossDual =
      crossDualOfOrientation theta := rfl

end OfOrientation

namespace VectorProductPair

variable {k : Type u} {M : Type v} [CommRing k] [AddCommGroup M] [Module k M]
  (P : VectorProductPair k M)

/-- The trilinear form of the dual vector product, read with its last argument as the
functional: `⟨χ, φ × ψ⟩`. -/
theorem crossDualAlternating_apply_cycle (φ ψ χ : Module.Dual k M) :
    P.crossDualAlternating ![φ, ψ, χ] = χ (P.crossDual φ ψ) := by
  rw [alternating_fin_three_cycle, alternating_fin_three_cycle]
  simp

/-- The linear form on `⋀³ M` induced by the volume form `(u, v, w) ↦ ⟨u × v, w⟩` of a
vector-product pair. -/
noncomputable def orientationLinearMap : ⋀[k]^3 M →ₗ[k] k :=
  exteriorPower.alternatingMapLinearEquiv P.crossAlternating

@[simp] theorem orientationLinearMap_ιMulti (x : Fin 3 → M) :
    P.orientationLinearMap (exteriorPower.ιMulti k 3 x) = P.crossAlternating x :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ x

section BaseChange

variable [Module.Finite k M] [Module.Projective k M] (S : Type w) [CommRing S] [Algebra k S]

/-- The dual vector product of the base change of a vector-product pair: the curried scalar
extension of the dual volume form, transported along the projective dual-base-change
equivalence `GPR 9.15` and read back in `S ⊗ M` by reflexivity. -/
noncomputable def baseChangeCrossDual :
    Module.Dual S (S ⊗[k] M) →ₗ[S] Module.Dual S (S ⊗[k] M) →ₗ[S] S ⊗[k] M :=
  (AlternatingMap.curryFinThree
    ((AlternatingMap.baseChangeAlternatingFinThree (S := S) P.crossDualAlternating).compLinearMap
      (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := k) (M := M)
        (A := S)).symm.toLinearMap)).compr₂
    (Module.evalEquiv S (S ⊗[k] M)).symm.toLinearMap

/-- The defining property of the base-changed dual vector product: `⟨χ, φ × ψ⟩` is the scalar
extension of the dual volume form evaluated at `(φ, ψ, χ)`, read in `S ⊗ M*`. This is the rule
`θ*⁻¹(φ ∧ ψ ∧ χ) = ⟨χ, φ × ψ⟩` of `GPR (22.14.2)`. -/
theorem apply_baseChangeCrossDual (f g h : Module.Dual S (S ⊗[k] M)) :
    h (P.baseChangeCrossDual S f g) =
      AlternatingMap.baseChangeFinThree (S := S) P.crossDualAlternating
        ((TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := k) (M := M) (A := S)).symm f)
        ((TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := k) (M := M) (A := S)).symm g)
        ((TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := k) (M := M) (A := S)).symm h) := by
  change Module.evalEquiv S (S ⊗[k] M) ((Module.evalEquiv S (S ⊗[k] M)).symm _) h = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The base-changed dual vector product on pure tensors. -/
theorem baseChangeCrossDual_tmul (r s : S) (φ ψ : Module.Dual k M) :
    P.baseChangeCrossDual S (TauCeti.Module.Dual.baseChangeEvaluation (A := S) (r ⊗ₜ[k] φ))
      (TauCeti.Module.Dual.baseChangeEvaluation (A := S) (s ⊗ₜ[k] ψ)) =
        (r * s) ⊗ₜ[k] P.crossDual φ ψ := by
  let e := TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := k) (M := M) (A := S)
  apply (Module.evalEquiv S (S ⊗[k] M)).injective
  ext h
  rw [Module.evalEquiv_apply, Module.evalEquiv_apply, Module.Dual.eval_apply,
    Module.Dual.eval_apply, apply_baseChangeCrossDual,
    ← TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply,
    ← TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]
  obtain ⟨q, rfl⟩ := e.surjective h
  rw [LinearEquiv.symm_apply_apply]
  induction q using TensorProduct.inductionOn with
  | add q₁ q₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply]; rw [h₁, h₂]
  | tmul t χ =>
    rw [AlternatingMap.baseChangeFinThree_tmul, crossDualAlternating_apply_cycle]
    simp only [e, TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply,
      TauCeti.Module.Dual.baseChangeEvaluation_tmul]
    ring

/-- **Base change of a vector-product pair** along a commutative `k`-algebra `S`, for `M` finitely
generated projective. The first product is the scalar extension of the volume form
`(u, v, w) ↦ ⟨u × v, w⟩`; the second is the scalar extension of the dual volume form, read
through the identification `S ⊗ M* = (S ⊗ M)*` of `GPR 9.15`. The axioms are checked on pure
tensors. -/
noncomputable def baseChange : VectorProductPair S (S ⊗[k] M) where
  cross := AlternatingMap.baseChangeFinThree (S := S) P.crossAlternating
  crossDual := P.baseChangeCrossDual S
  cross_self v := LinearMap.ext fun w ↦ by
    rw [AlternatingMap.baseChangeFinThree_self_zero_one]
    rfl
  crossDual_self f := by
    apply (Module.evalEquiv S (S ⊗[k] M)).injective
    ext h
    rw [Module.evalEquiv_apply, Module.Dual.eval_apply, apply_baseChangeCrossDual,
      AlternatingMap.baseChangeFinThree_self_zero_one, map_zero, LinearMap.zero_apply]
  cross_apply_left v w := AlternatingMap.baseChangeFinThree_self_zero_two _ v w
  apply_crossDual_left f g := by
    rw [apply_baseChangeCrossDual, AlternatingMap.baseChangeFinThree_self_zero_two]
  cross_apply_crossDual v w f g := by
    let e := TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := k) (M := M) (A := S)
    obtain ⟨q, rfl⟩ := e.surjective f
    obtain ⟨q', rfl⟩ := e.surjective g
    induction q using TensorProduct.inductionOn with
    | add q₁ q₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply] at h₁ h₂ ⊢
      rw [h₁, h₂]
      ring
    | tmul r φ =>
      induction q' using TensorProduct.inductionOn with
      | add q₁ q₂ h₁ h₂ =>
        simp only [map_add, LinearMap.add_apply] at h₁ h₂ ⊢
        rw [h₁, h₂]
        ring
      | tmul s ψ =>
        simp only [e, TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply]
        rw [baseChangeCrossDual_tmul]
        induction v using TensorProduct.inductionOn with
        | add v₁ v₂ h₁ h₂ =>
          simp only [map_add, LinearMap.add_apply] at h₁ h₂ ⊢
          rw [h₁, h₂]
          ring
        | tmul t x =>
          induction w using TensorProduct.inductionOn with
          | add w₁ w₂ h₁ h₂ =>
            simp only [map_add, LinearMap.add_apply] at h₁ h₂ ⊢
            rw [h₁, h₂]
            ring
          | tmul t' y =>
            rw [AlternatingMap.baseChangeFinThree_tmul]
            simp only [TauCeti.Module.Dual.baseChangeEvaluation_tmul]
            have h := P.cross_apply_crossDual x y φ ψ
            simp only [crossAlternating_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h, map_sub, map_mul]
            ring

@[simp] theorem baseChange_cross :
    (P.baseChange S).cross = AlternatingMap.baseChangeFinThree (S := S) P.crossAlternating := rfl

@[simp] theorem baseChange_crossDual : (P.baseChange S).crossDual = P.baseChangeCrossDual S := rfl

/-- The volume form of the base change is the scalar extension of the volume form. -/
theorem crossAlternating_baseChange :
    (P.baseChange S).crossAlternating =
      AlternatingMap.baseChangeAlternatingFinThree (S := S) P.crossAlternating :=
  rfl

/-- The volume form of the base change on scalar extensions of vectors of `M`. -/
theorem crossAlternating_baseChange_one_tmul (x : Fin 3 → M) :
    (P.baseChange S).crossAlternating (fun i ↦ 1 ⊗ₜ[k] x i) =
      algebraMap k S (P.crossAlternating x) := by
  have hx : ![x 0, x 1, x 2] = x := by
    ext i
    fin_cases i <;> rfl
  rw [crossAlternating_apply, baseChange_cross, AlternatingMap.baseChangeFinThree_tmul, hx]
  ring

/-- The dual volume form of the base change on scalar extensions of functionals on `M`. -/
theorem crossDualAlternating_baseChange_one_tmul (f : Fin 3 → Module.Dual k M) :
    (P.baseChange S).crossDualAlternating
        (fun i ↦ TauCeti.Module.Dual.baseChangeEvaluation (A := S) (1 ⊗ₜ[k] f i)) =
      algebraMap k S (P.crossDualAlternating f) := by
  rw [crossDualAlternating_apply, baseChange_crossDual, baseChangeCrossDual_tmul,
    TauCeti.Module.Dual.baseChangeEvaluation_tmul, crossDualAlternating_apply]
  ring

end BaseChange

/-- **The triple identity in the free case.** For a vector-product pair on a module with a basis
of size three, the volume forms of the two products multiply to the determinant of the matrix of
pairings: this is `GPR (22.14.1)` read for the pair. -/
theorem crossAlternating_mul_crossDualAlternating_of_basis (b : Module.Basis (Fin 3) k M)
    (x : Fin 3 → M) (f : Fin 3 → Module.Dual k M) :
    P.crossAlternating x * P.crossDualAlternating f = Matrix.det (.of fun i j ↦ f i (x j)) := by
  obtain ⟨b', rfl⟩ := VectorProductPair.exists_eq_ofBasis b P
  rw [VectorProductPair.crossAlternating_ofBasis, VectorProductPair.crossDualAlternating_ofBasis]
  exact b'.det_mul_det_dualBasis x f

variable [Module.Finite k M] [Module.Projective k M]

/-- **The triple identity**, `GPR (22.14.1)` for a vector-product pair on a constant-rank-three
finite projective module: `⟨u × v, w⟩ · ⟨φ, ψ × χ⟩ = det (⟨φᵢ, vⱼ⟩)`. It is checked at every
maximal ideal, where the module is free and the based case
`crossAlternating_mul_crossDualAlternating_of_basis` applies to the base-changed pair. -/
theorem crossAlternating_mul_crossDualAlternating
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) (x : Fin 3 → M) (f : Fin 3 → Module.Dual k M) :
    P.crossAlternating x * P.crossDualAlternating f = Matrix.det (.of fun i j ↦ f i (x j)) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_localization
  intro J hJ
  let S := Localization.AtPrime J
  obtain ⟨b⟩ := nonempty_basis_atPrime_of_rankAtStalk_eq hM J
  have h := (P.baseChange S).crossAlternating_mul_crossDualAlternating_of_basis b
    (fun i ↦ 1 ⊗ₜ[k] x i) (fun i ↦ TauCeti.Module.Dual.baseChangeEvaluation (A := S) (1 ⊗ₜ[k] f i))
  rw [crossAlternating_baseChange_one_tmul, crossDualAlternating_baseChange_one_tmul] at h
  rw [map_sub, map_mul, h, RingHom.map_det, sub_eq_zero]
  congr 1
  ext i j
  simp only [TauCeti.Module.Dual.baseChangeEvaluation_tmul, one_mul]
  rfl

/-- The volume form of a vector-product pair on a constant-rank-three finite projective module is
surjective. At a maximal ideal `J`, the base-changed pair has a unit volume on a basis
(`isUnit_crossAlternating_basis`), which could not happen if every volume of `M` lay in `J`. -/
theorem surjective_orientationLinearMap (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    Function.Surjective P.orientationLinearMap := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal _ hne
  have hval (x : Fin 3 → M) : P.crossAlternating x ∈ J :=
    hle ⟨exteriorPower.ιMulti k 3 x, P.orientationLinearMap_ιMulti x⟩
  let S := Localization.AtPrime J
  obtain ⟨b⟩ := nonempty_basis_atPrime_of_rankAtStalk_eq hM J
  have hmem (y₀ y₁ y₂ : S ⊗[k] M) :
      AlternatingMap.baseChangeFinThree (S := S) P.crossAlternating y₀ y₁ y₂ ∈
        Ideal.map (algebraMap k S) J := by
    induction y₀ using TensorProduct.inductionOn with
    | add a a' ha ha' =>
      rw [map_add, LinearMap.add_apply, LinearMap.add_apply]
      exact add_mem ha ha'
    | tmul r x =>
      induction y₁ using TensorProduct.inductionOn with
      | add a a' ha ha' =>
        rw [map_add, LinearMap.add_apply]
        exact add_mem ha ha'
      | tmul s y =>
        induction y₂ using TensorProduct.inductionOn with
        | add a a' ha ha' =>
          rw [map_add]
          exact add_mem ha ha'
        | tmul t z =>
          rw [AlternatingMap.baseChangeFinThree_tmul]
          exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hval _))
  have hunit := (P.baseChange S).isUnit_crossAlternating_basis b
  have hmax : (P.baseChange S).crossAlternating b ∈ IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact hmem (b 0) (b 1) (b 2)
  exact (IsLocalRing.mem_maximalIdeal _).mp hmax hunit

/-- The volume form of a vector-product pair on a constant-rank-three finite projective module is
injective. By the triple identity, every functional on `⋀³ M` — all of which come from `⋀³ M*`
by `GPR 21.7` — is a multiple of the volume form, and functionals separate the points of the
projective module `⋀³ M`. -/
theorem injective_orientationLinearMap (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    Function.Injective P.orientationLinearMap := by
  let B : ⋀[k]^3 (Module.Dual k M) →ₗ[k] k :=
    exteriorPower.alternatingMapLinearEquiv P.crossDualAlternating
  have hpair (η : ⋀[k]^3 (Module.Dual k M)) (ω : ⋀[k]^3 M) :
      exteriorPower.pairingDual k M 3 η ω = P.orientationLinearMap ω * B η := by
    have h₁ (x : Fin 3 → M) :
        Module.Dual.eval k _ (exteriorPower.ιMulti k 3 x) ∘ₗ exteriorPower.pairingDual k M 3 =
          P.crossAlternating x • B := by
      ext f
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        Module.Dual.eval_apply, exteriorPower.pairingDual_ιMulti_ιMulti, LinearMap.smul_apply,
        B, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, smul_eq_mul,
        P.crossAlternating_mul_crossDualAlternating hM]
      rw [show (Matrix.of fun i j ↦ f j (x i)) =
        Matrix.transpose (Matrix.of fun i j ↦ f i (x j)) by rfl, Matrix.det_transpose]
    have h₂ : exteriorPower.pairingDual k M 3 η = B η • P.orientationLinearMap := by
      ext x
      simpa [mul_comm] using LinearMap.congr_fun (h₁ x) η
    rw [h₂, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  refine (injective_iff_map_eq_zero _).mpr fun ω hω ↦ ?_
  refine (Module.forall_dual_apply_eq_zero_iff k ω).mp fun φ ↦ ?_
  obtain ⟨η, rfl⟩ := (exteriorPower.pairingDual_bijective_of_projective (M := M) 3).2 φ
  rw [hpair, hω, zero_mul]

/-- **The orientation of a vector-product pair.** On a finite projective module of constant rank
three, the volume form `u ∧ v ∧ w ↦ ⟨u × v, w⟩` of a vector-product pair is an orientation
`⋀³ M ≃ k`; this is the converse of the construction of `GPR 22.14`. -/
noncomputable def orientation (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    (⋀[k]^3 M) ≃ₗ[k] k :=
  LinearEquiv.ofBijective P.orientationLinearMap
    ⟨P.injective_orientationLinearMap hM, P.surjective_orientationLinearMap hM⟩

@[simp] theorem orientation_ιMulti (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (x : Fin 3 → M) : P.orientation hM (exteriorPower.ιMulti k 3 x) = P.crossAlternating x :=
  P.orientationLinearMap_ιMulti x

@[simp] theorem orientationAlternating_orientation
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    orientationAlternating (P.orientation hM) = P.crossAlternating :=
  AlternatingMap.ext fun x ↦ P.orientation_ιMulti hM x

/-- The dual orientation `θ*⁻¹` of `GPR 22.14` induced by the orientation of a pair is the volume
form of its dual vector product. Both satisfy the determinant identity `GPR (22.14.1)` against
the same primal volume form, which takes the value `1` on some element of `⋀³ M`. -/
theorem dualOrientationAlternating_orientation
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    dualOrientationAlternating (P.orientation hM) = P.crossDualAlternating := by
  ext f
  obtain ⟨ω, hω⟩ := (P.orientation hM).surjective 1
  have h : (dualOrientationAlternating (P.orientation hM) f - P.crossDualAlternating f) •
      (P.orientation hM).toLinearMap = 0 := by
    ext x
    have h₁ : orientationAlternating (P.orientation hM) x *
        dualOrientationAlternating (P.orientation hM) f = Matrix.det (.of fun i j ↦ f i (x j)) :=
      orientationAlternating_mul_dualOrientationAlternating_apply (P.orientation hM) x f
    have h₂ := P.crossAlternating_mul_crossDualAlternating hM x f
    rw [orientationAlternating_orientation] at h₁
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      orientation_ιMulti, smul_eq_mul, LinearMap.zero_compAlternatingMap,
      AlternatingMap.zero_apply]
    linear_combination h₁ - h₂
  have := LinearMap.congr_fun h ω
  rwa [LinearMap.smul_apply, LinearEquiv.coe_coe, hω, smul_eq_mul, mul_one, LinearMap.zero_apply,
    sub_eq_zero] at this

/-- **Every vector-product pair comes from an orientation.** On a finite projective module of
constant rank three, the pair induced (`GPR 22.14`) by the orientation of a pair is the pair
itself. -/
@[simp] theorem ofOrientation_orientation (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    VectorProductPair.ofOrientation hM (P.orientation hM) = P := by
  refine VectorProductPair.ext ?_ ?_
  · ext v w x
    rw [VectorProductPair.ofOrientation_cross, crossOfOrientation_apply,
      orientationAlternating_orientation, crossAlternating_apply]
    rfl
  · ext f g
    apply (Module.evalEquiv k M).injective
    ext h
    rw [Module.evalEquiv_apply, Module.evalEquiv_apply, Module.Dual.eval_apply,
      Module.Dual.eval_apply, VectorProductPair.ofOrientation_crossDual,
      apply_crossDualOfOrientation, dualOrientationAlternating_orientation,
      crossDualAlternating_apply_cycle]

/-- The orientation of the pair induced by an orientation is the orientation itself. -/
@[simp] theorem orientation_ofOrientation (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (θ : (⋀[k]^3 M) ≃ₗ[k] k) : (VectorProductPair.ofOrientation hM θ).orientation hM = θ := by
  apply LinearEquiv.toLinearMap_injective
  ext x
  have hx : ![x 0, x 1, x 2] = x := by
    ext i
    fin_cases i <;> rfl
  simp [crossAlternating_apply, hx]

/-- **Orientations are vector-product pairs** (`GPR 22.14`): on a finite projective module of
constant rank three, `VectorProductPair.ofOrientation` is a bijection from orientations to
vector-product pairs, with inverse `VectorProductPair.orientation`. -/
noncomputable def orientationEquiv (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    ((⋀[k]^3 M) ≃ₗ[k] k) ≃ VectorProductPair k M where
  toFun θ := VectorProductPair.ofOrientation hM θ
  invFun P := P.orientation hM
  left_inv θ := orientation_ofOrientation hM θ
  right_inv P := P.ofOrientation_orientation hM

@[simp] theorem orientationEquiv_apply (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
    (θ : (⋀[k]^3 M) ≃ₗ[k] k) : orientationEquiv hM θ = VectorProductPair.ofOrientation hM θ := rfl

@[simp] theorem orientationEquiv_symm_apply (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    (orientationEquiv hM).symm P = P.orientation hM := rfl

end VectorProductPair

end Module
