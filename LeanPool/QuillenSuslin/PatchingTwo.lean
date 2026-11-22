/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.PatchingCore

import Mathlib.RingTheory.Flat.Localization

/-!
# Patching extended modules over two comaximal localisations

For comaximal `a, b ∈ A`, a finitely presented `A[X]`-module that becomes extended after
inverting `a` and after inverting `b` is isomorphic to `A[X] ⊗[A] M(0)` (Quillen 1976, proof of
Theorem 1, p. 168).

## Main results

* `nonempty_linearEquiv_fibre_of_normalized`: gluing of normalised isomorphisms.
* `nonempty_linearEquiv_fibre_of_isCoprime`: the patching step.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A] {a b : A} {Ba Bb Bab : Type*} [CommRing Ba] [CommRing Bb]
  [CommRing Bab] [Algebra A Ba] [Algebra A Bb] [Algebra A Bab] [IsLocalization.Away a Ba]
  [IsLocalization.Away b Bb] [IsLocalization.Away (a * b) Bab] [Algebra Ba Bab] [Algebra Bb Bab]
  [IsScalarTower A Ba Bab] [IsScalarTower A Bb Bab]
  (M : Type v) [AddCommGroup M] [Module A[X] M]

theorem transP_locP (B B' : Type*) [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    [Algebra B B'] [IsScalarTower A B B'] (N : Type*) [AddCommGroup N] [Module A N] :
    letI := Polynomial.algebra A B
    letI := Polynomial.algebra A B'
    transP A B B' N ∘ₗ locP B N = locP B' N := by
  let _ := Polynomial.algebra A B
  let _ := Polynomial.algebra A B'
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul p n =>
    simp only [LinearMap.coe_comp, Function.comp_apply, locP_tmul, transP_tmul, Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq]
  | add x y hx hy => rw [map_add, hx, hy, map_add]

theorem transM_mk (B B' : Type*) [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    [Algebra B B'] [IsScalarTower A B B'] :
    letI := Polynomial.algebra A B
    letI := Polynomial.algebra A B'
    transM A M B B' ∘ₗ TensorProduct.mk A[X] B[X] M 1 = TensorProduct.mk A[X] B'[X] M 1 := by
  let _ := Polynomial.algebra A B
  let _ := Polynomial.algebra A B'
  ext m
  simp [transM_tmul]

theorem transP_endPoly (N : Type*) [AddCommGroup N] [Module A N] (B B' : Type*) [CommRing B]
    [CommRing B'] [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    (q : (B ⊗[A] Module.End A N)[X]) (x : B[X] ⊗[A] N) :
    transP A B B' N (endPoly N B q x) =
      endPoly N B' (q.map (tensorLeftMap (A := A) (Module.End A N) B B' :
        B ⊗[A] Module.End A N →+* B' ⊗[A] Module.End A N)) (transP A B B' N x) := by
  rw [transP_eq_polyTensorMap, transP_eq_polyTensorMap, endPoly_natural]
  rfl

include Bab in
/-- Gluing normalised extension isomorphisms over `A_a[X]` and `A_b[X]` for comaximal `a, b`. -/
theorem nonempty_linearEquiv_fibre_of_normalized [Module.FinitePresentation A[X] M]
    (hab : IsCoprime a b)
    (ua : (Ba[X] ⊗[A] fibre A M) ≃ₗ[Ba[X]] (letI := Polynomial.algebra A Ba; Ba[X] ⊗[A[X]] M))
    (hua : ∀ x, fibreMap A M Ba (ua x) = reduce (fibre A M) Ba x)
    (ub : (Bb[X] ⊗[A] fibre A M) ≃ₗ[Bb[X]] (letI := Polynomial.algebra A Bb; Bb[X] ⊗[A[X]] M))
    (hub : ∀ x, fibreMap A M Bb (ub x) = reduce (fibre A M) Bb x) :
    Nonempty ((A[X] ⊗[A] fibre A M) ≃ₗ[A[X]] M) := by
  let _ := Polynomial.algebra A Ba
  let _ := Polynomial.algebra A Bb
  let _ := Polynomial.algebra A Bab
  have : Module.Flat A Bab := IsLocalization.flat Bab (Submonoid.powers (a * b))
  let ua' := baseChangeEquiv (B' := Bab) ua
  let ub' := baseChangeEquiv (B' := Bab) ub
  have hua' := fibreMap_baseChangeEquiv (B' := Bab) ua hua
  have hub' := fibreMap_baseChangeEquiv (B' := Bab) ub hub
  let θ := ub'.trans ua'.symm
  have hθ : ∀ x, reduce (fibre A M) Bab (θ x) = reduce (fibre A M) Bab x := fun x => by
    rw [← hua', LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hub']
  obtain ⟨θ', hθ'E, hθ'0⟩ := exists_unit_endPoly_eq (fibre A M) Bab θ hθ
  obtain ⟨ψa, ψb, key⟩ := exists_factor_unit Ba Bb hab (Module.End A (fibre A M)) θ' hθ'0
  let ιa := (tensorLeftMap (A := A) (Module.End A (fibre A M)) Ba Bab :
    Ba ⊗[A] Module.End A (fibre A M) →+* Bab ⊗[A] Module.End A (fibre A M))
  let ψab := Units.map (mapRingHom ιa).toMonoidHom ψa
  -- the localisation data over `Λ = A[X]`
  have : IsLocalizedModule (Submonoid.powers (C a)) (locP Ba (fibre A M)) :=
    isLocalizedModule_locP a Ba (fibre A M)
  have : IsLocalizedModule (Submonoid.powers (C b)) (locP Bb (fibre A M)) :=
    isLocalizedModule_locP b Bb (fibre A M)
  have : IsLocalizedModule (Submonoid.powers (C a * C b)) (locP Bab (fibre A M)) := by
    rw [← C_mul]; exact isLocalizedModule_locP (a * b) Bab (fibre A M)
  have : IsLocalizedModule (Submonoid.powers (C a)) (TensorProduct.mk A[X] Ba[X] M 1) :=
    isLocalizedModule_mk_polynomial a Ba M
  have : IsLocalizedModule (Submonoid.powers (C b)) (TensorProduct.mk A[X] Bb[X] M 1) :=
    isLocalizedModule_mk_polynomial b Bb M
  have : IsLocalizedModule (Submonoid.powers (C a * C b)) (TensorProduct.mk A[X] Bab[X] M 1) := by
    rw [← C_mul]; exact isLocalizedModule_mk_polynomial (a * b) Bab M
  refine nonempty_linearEquiv_of_glue (hab.map C) (locP Ba (fibre A M)) (locP Bb (fibre A M))
    (locP Bab (fibre A M)) (transP A Ba Bab (fibre A M)) (transP A Bb Bab (fibre A M))
    (TensorProduct.mk A[X] Ba[X] M 1) (TensorProduct.mk A[X] Bb[X] M 1)
    (TensorProduct.mk A[X] Bab[X] M 1) (transM A M Ba Bab) (transM A M Bb Bab)
    (transP_locP Ba Bab (fibre A M)) (transP_locP Bb Bab (fibre A M)) (transM_mk M Ba Bab)
    (transM_mk M Bb Bab) (((endPolyEquiv (fibre A M) Ba ψa).trans ua).restrictScalars A[X])
    (((endPolyEquiv (fibre A M) Bb ψb).trans ub).restrictScalars A[X])
    (((endPolyEquiv (fibre A M) Bab ψab).trans ua').restrictScalars A[X]) ?_ ?_
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply, endPolyEquiv_apply]
    rw [← baseChangeEquiv_transP, transP_endPoly]
    rfl
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply, endPolyEquiv_apply]
    rw [← baseChangeEquiv_transP, transP_endPoly]
    change ub' _ = ua' (endPoly (fibre A M) Bab
      ((ψa : (Ba ⊗[A] Module.End A (fibre A M))[X]).map ιa) _)
    rw [← key, map_mul, mul_apply_eq_comp, hθ'E]
    simp [θ]

include Bab in
/-- **Patching over two comaximal localisations.** For comaximal `a, b ∈ A`, a finitely
presented `A[X]`-module that becomes extended after inverting `a` and after inverting `b` is
isomorphic to `A[X] ⊗[A] M(0)` (Quillen 1976, proof of Theorem 1, p. 168). -/
theorem nonempty_linearEquiv_fibre_of_isCoprime [Module.FinitePresentation A[X] M]
    (hab : IsCoprime a b) (ha : IsExtendedAfter A Ba M) (hb : IsExtendedAfter A Bb M) :
    Nonempty ((A[X] ⊗[A] fibre A M) ≃ₗ[A[X]] M) := by
  obtain ⟨ua, hua⟩ := exists_normalized_equiv A M Ba ha
  obtain ⟨ub, hub⟩ := exists_normalized_equiv A M Bb hb
  exact nonempty_linearEquiv_fibre_of_normalized (Bab := Bab) M hab ua hua ub hub

end LeanPool.QuillenSuslin

