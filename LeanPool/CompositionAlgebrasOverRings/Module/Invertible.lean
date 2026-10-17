/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Invertible modules and line bundles

This file proves the standard characterization of invertible modules as finite locally free
modules of rank one. This fills the corresponding TODO in mathlib's
`Mathlib/RingTheory/PicardGroup.lean`.

## Main definitions

* `Module.IsLocallyFreeRankOne R M`: `M` is finite projective and has rank one at every stalk.
* `Module.IsRankOnePairing R M`: the rank-one identity for the evaluation pairing.

## Main results

* `Module.invertible_iff_isLocallyFreeRankOne`: invertible modules are exactly the finite locally
  free modules of rank one.
* `Module.IsLocallyFreeRankOne.isRankOnePairing`: a line bundle satisfies the rank-one pairing
  identity.
* `Module.IsLocallyFreeRankOne.bilinMap_eq_zero_of_map_self_eq_zero`: an alternating bilinear
  map out of a line bundle vanishes.
* `Module.isRankOnePairing_of_invertible`: the pairing identity for mathlib's invertible modules.

## Proof idea

For the converse, choose a finite dual frame `mᵢ, φᵢ` for the projective module. Rank one at
every stalk gives the identity `φ(x)ψ(y) = φ(y)ψ(x)`. The trace of the frame is one, and
consequently every elementary tensor satisfies

`φ ⊗ x = φ(x) • ∑ᵢ φᵢ ⊗ mᵢ`.

Thus contraction with the evaluation pairing is bijective, which is precisely mathlib's
definition of `Module.Invertible`.

## References

* [Stacks, Tag 00NX] The Stacks Project, *Finite projective modules*.
* [Stacks, Tag 0B8I] The Stacks Project, *Invertible modules*.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- An `R`-module is **locally free of rank one** if it is finite projective and its localization
at every prime has rank one.

The finite-projective clauses are the algebraic form of finite local freeness; the stalk rank is
mathlib's `Module.rankAtStalk`. -/
def IsLocallyFreeRankOne : Prop :=
  Module.Finite R M ∧ Module.Projective R M ∧ Module.rankAtStalk (R := R) M = 1

/-- The evaluation pairing of `M` has the **rank-one pairing identity** if
`φ(x) ψ(y) = φ(y) ψ(x)` for all functionals and vectors. -/
def IsRankOnePairing : Prop :=
  ∀ (φ ψ : Module.Dual R M) (x y : M), φ x * ψ y = φ y * ψ x

variable {R M}

/-- A module isomorphic to the base ring has the rank-one pairing identity. -/
theorem isRankOnePairing_of_linearEquiv (e : M ≃ₗ[R] R) : IsRankOnePairing R M := by
  intro φ ψ x y
  have hx : ∀ z : M, z = e z • e.symm 1 := fun z ↦ by
    rw [← map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]
  rw [hx x, hx y, map_smul, map_smul, map_smul, map_smul]
  ring

/-- The base ring itself has the rank-one pairing identity. -/
theorem isRankOnePairing_self : IsRankOnePairing R R :=
  isRankOnePairing_of_linearEquiv (LinearEquiv.refl R R)

private theorem isRankOnePairing_of_finite_projective_of_rankAtStalk_eq_one
    [Module.Finite R M] [Module.Projective R M]
    (hrank : Module.rankAtStalk (R := R) M = 1) :
    IsRankOnePairing R M := by
  intro φ ψ x y
  let A (P : Ideal R) [P.IsMaximal] := Localization.AtPrime P
  let MP (P : Ideal R) [P.IsMaximal] := LocalizedModule P.primeCompl M
  let j (P : Ideal R) [P.IsMaximal] : M →ₗ[R] MP P :=
    LocalizedModule.mkLinearMap P.primeCompl M
  apply Module.eq_of_localization_maximal (fun P _ ↦ A P) (fun P _ ↦ Algebra.linearMap R (A P))
  intro P hP
  let φP : Module.Dual (A P) (MP P) :=
    (IsLocalizedModule.map P.primeCompl (j P)
      (Algebra.linearMap R (A P)) φ).extendScalarsOfIsLocalization P.primeCompl (A P)
  let ψP : Module.Dual (A P) (MP P) :=
    (IsLocalizedModule.map P.primeCompl (j P)
      (Algebra.linearMap R (A P)) ψ).extendScalarsOfIsLocalization P.primeCompl (A P)
  have hfinrank : Module.finrank (A P) (MP P) = 1 := by
    simpa [Module.rankAtStalk] using congrFun hrank ⟨P, hP.isPrime⟩
  let : Module.Free (A P) (MP P) := Module.free_of_flat_of_isLocalRing
  let e : A P ≃ₗ[A P] MP P := (Module.nonempty_linearEquiv_of_finrank_eq_one hfinrank).some
  have hpair := isRankOnePairing_of_linearEquiv e.symm φP ψP (j P x) (j P y)
  simpa [φP, ψP, j, map_mul] using hpair

/-- A finite locally free module of rank one has the rank-one pairing identity. -/
theorem IsLocallyFreeRankOne.isRankOnePairing (h : IsLocallyFreeRankOne R M) :
    IsRankOnePairing R M := by
  let : Module.Finite R M := h.1
  let : Module.Projective R M := h.2.1
  exact isRankOnePairing_of_finite_projective_of_rankAtStalk_eq_one h.2.2

-- Extension of scalars preserves the condition that a bilinear map vanishes on the diagonal.
private theorem bilinMap_baseChange_apply_self_eq_zero
    {S : Type*} [CommRing S] [Algebra R S]
    {N : Type*} [AddCommGroup N] [Module R N]
    (B : LinearMap.BilinMap R M N) (hB : ∀ x, B x x = 0)
    (z : S ⊗[R] M) : B.baseChange S z z = 0 := by
  -- The skew-symmetry of the base-changed map is an equality of bilinear maps, so it is enough
  -- to check it on elementary tensors on both sides.
  have hkey : ((B.baseChange S) + (B.baseChange S).flip).restrictScalars R = 0 :=
    TensorProduct.ext' fun a m ↦ by
      apply LinearMap.restrictScalars_injective R
      refine TensorProduct.ext' fun b n ↦ ?_
      change (a * b) ⊗ₜ[R] B m n + (b * a) ⊗ₜ[R] B n m = 0
      rw [mul_comm b a, ← TensorProduct.tmul_add, ← LinearMap.IsAlt.neg hB m n,
        add_neg_cancel, TensorProduct.tmul_zero]
  have hskewS (x y : S ⊗[R] M) : B.baseChange S x y + B.baseChange S y x = 0 :=
    DFunLike.congr_fun (DFunLike.congr_fun hkey x) y
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [((B.baseChange S) (x + y)).map_add, (B.baseChange S).map_add,
      LinearMap.add_apply, LinearMap.add_apply, hx, hy]
    simpa only [zero_add, add_zero, add_comm] using hskewS x y
  | tmul a m =>
    change (a * a) ⊗ₜ[R] B m m = 0
    rw [hB, TensorProduct.tmul_zero]

/-- Every alternating bilinear map out of a line bundle vanishes. Equivalently, the second
exterior power of a line bundle is zero. -/
theorem IsLocallyFreeRankOne.bilinMap_eq_zero_of_map_self_eq_zero
    {N : Type*} [AddCommGroup N] [Module R N] (h : IsLocallyFreeRankOne R M)
    (B : LinearMap.BilinMap R M N) (hB : ∀ x, B x x = 0) : B = 0 := by
  let : Module.Finite R M := h.1
  let : Module.Projective R M := h.2.1
  ext x y
  let A (P : Ideal R) [P.IsMaximal] := Localization.AtPrime P
  let T (P : Ideal R) [P.IsMaximal] := A P ⊗[R] M
  let U (P : Ideal R) [P.IsMaximal] := A P ⊗[R] N
  let jN (P : Ideal R) [P.IsMaximal] : N →ₗ[R] U P := TensorProduct.mk R (A P) N 1
  apply Module.eq_zero_of_localization_maximal (fun P _ ↦ U P) (fun P _ ↦ jN P) (B x y)
  intro P hP
  let BA : LinearMap.BilinMap (A P) (T P) (U P) := B.baseChange (A P)
  have hdiagA (z : T P) : BA z z = 0 :=
    bilinMap_baseChange_apply_self_eq_zero B hB z
  have hfinrank : Module.finrank (A P) (T P) = 1 := by
    calc
      Module.finrank (A P) (T P) =
          Module.rankAtStalk (R := R) M ⟨P, hP.isPrime⟩ :=
        (Module.rankAtStalk_eq_finrank_tensorProduct
          (R := R) (M := M) ⟨P, hP.isPrime⟩).symm
      _ = 1 := congrFun h.2.2 ⟨P, hP.isPrime⟩
  let : Module.Free (A P) (T P) := Module.free_of_flat_of_isLocalRing
  let e : A P ≃ₗ[A P] T P := (Module.nonempty_linearEquiv_of_finrank_eq_one hfinrank).some
  have he (z : T P) : z = e.symm z • e 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]
  change (1 : A P) ⊗ₜ[R] B x y = 0
  calc
    (1 : A P) ⊗ₜ[R] B x y =
        (1 * 1 : A P) ⊗ₜ[R] B x y := by rw [one_mul]
    _ = BA ((1 : A P) ⊗ₜ[R] x) ((1 : A P) ⊗ₜ[R] y) :=
      (LinearMap.BilinMap.baseChange_tmul B 1 x 1 y).symm
    _ = 0 := by
      rw [he ((1 : A P) ⊗ₜ[R] x), he ((1 : A P) ⊗ₜ[R] y),
        LinearMap.map_smul₂, map_smul, hdiagA]
      simp

-- The trace of a finite dual frame on a rank-one projective module is one. This isolates the
-- localization argument used to construct the inverse of the contraction pairing below.
private theorem sum_dual_frame_apply_eq_one_of_rankAtStalk_eq_one
    [Module.Finite R M] [Module.Projective R M]
    (hrank : Module.rankAtStalk (R := R) M = 1) {n : ℕ}
    (φ : Fin n → Module.Dual R M) (m : Fin n → M)
    (hframe : ∀ x, ∑ i, φ i x • m i = x) : ∑ i, φ i (m i) = 1 := by
  let A (P : Ideal R) [P.IsMaximal] := Localization.AtPrime P
  let MP (P : Ideal R) [P.IsMaximal] := LocalizedModule P.primeCompl M
  let j (P : Ideal R) [P.IsMaximal] : M →ₗ[R] MP P :=
    LocalizedModule.mkLinearMap P.primeCompl M
  apply Module.eq_of_localization_maximal (fun P _ ↦ A P)
    (fun P _ ↦ Algebra.linearMap R (A P))
  intro P hP
  let φP (i : Fin n) : Module.Dual (A P) (MP P) :=
    (IsLocalizedModule.map P.primeCompl (j P) (Algebra.linearMap R (A P))
      (φ i)).extendScalarsOfIsLocalization P.primeCompl (A P)
  have hfinrank : Module.finrank (A P) (MP P) = 1 := by
    simpa [Module.rankAtStalk] using congrFun hrank ⟨P, hP.isPrime⟩
  let : Module.Free (A P) (MP P) := Module.free_of_flat_of_isLocalRing
  let e : A P ≃ₗ[A P] MP P :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one hfinrank).some
  have hframeP :
      (∑ i, (φP i).smulRight (j P (m i))) = LinearMap.id := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext P.primeCompl (j P) (j P)
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply, φP,
      LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.map_apply]
    simpa only [map_sum, map_smul, Algebra.linearMap_apply,
      IsScalarTower.algebraMap_smul] using congrArg (j P) (hframe x)
  have hsum : ∑ i, φP i (e 1) * e.symm (j P (m i)) = 1 := by
    calc
      ∑ i, φP i (e 1) * e.symm (j P (m i)) =
          e.symm (∑ i, φP i (e 1) • j P (m i)) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = e.symm (e 1) := by
        have hx := DFunLike.congr_fun hframeP (e 1)
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply] at hx
        rw [hx]
      _ = 1 := e.symm_apply_apply 1
  have hpairP := isRankOnePairing_of_linearEquiv e.symm
  have hsum' : ∑ i, φP i (j P (m i)) = 1 := by
    calc
      ∑ i, φP i (j P (m i)) =
          ∑ i, φP i (e 1) * e.symm (j P (m i)) :=
        Finset.sum_congr rfl fun i _ ↦ by
          simpa using (hpairP (φP i) e.symm (e 1) (j P (m i))).symm
      _ = 1 := hsum
  rw [map_sum]
  convert hsum' using 1 <;>
    simp only [φP, Algebra.linearMap_apply, map_one,
      LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.map_apply]

private theorem invertible_of_finite_projective_of_rankAtStalk_eq_one
    [Module.Finite R M] [Module.Projective R M]
    (hrank : Module.rankAtStalk (R := R) M = 1) : Module.Invertible R M := by
  classical
  let hpair := isRankOnePairing_of_finite_projective_of_rankAtStalk_eq_one hrank
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let b := Pi.basisFun R (Fin n)
  let φ (i : Fin n) : Module.Dual R M := b.coord i ∘ₗ g
  let m (i : Fin n) : M := f (b i)
  have hframe (x : M) : ∑ i, φ i x • m i = x := by
    calc
      ∑ i, φ i x • m i = f (∑ i, (b.repr (g x) i) • b i) := by
        simp only [map_sum, map_smul, φ, m, LinearMap.coe_comp, Function.comp_apply,
          Basis.coord_apply]
      _ = f (g x) := by rw [b.sum_repr]
      _ = x := by
        simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] using
          DFunLike.congr_fun hfg x
  have htrace : ∑ i, φ i (m i) = 1 :=
    sum_dual_frame_apply_eq_one_of_rankAtStalk_eq_one hrank φ m hframe
  let z : Module.Dual R M ⊗[R] M := ∑ i, φ i ⊗ₜ[R] m i
  have hcontract : contractLeft R M z = 1 := by
    simpa only [z, map_sum, contractLeft_apply] using htrace
  have htensor (ψ : Module.Dual R M) (x : M) : ψ ⊗ₜ[R] x = ψ x • z := by
    calc
      ψ ⊗ₜ[R] x = ψ ⊗ₜ[R] (∑ i, φ i x • m i) := by rw [hframe]
      _ = ∑ i, (φ i x • ψ) ⊗ₜ[R] m i := by
        rw [TensorProduct.tmul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ (TensorProduct.smul_tmul _ _ _).symm
      _ = ∑ i, (ψ x • φ i) ⊗ₜ[R] m i :=
        Finset.sum_congr rfl fun i _ ↦ by
          congr 1
          ext y
          simp only [LinearMap.smul_apply, smul_eq_mul]
          exact (hpair (φ i) ψ x y).trans (mul_comm _ _)
      _ = ψ x • z := by
        simp only [z, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ (TensorProduct.smul_tmul' _ _ _).symm
  have hreconstruct (w : Module.Dual R M ⊗[R] M) : w = contractLeft R M w • z := by
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, add_smul, ← hx, ← hy]
    | tmul ψ x => exact htensor ψ x
  refine ⟨?_, ?_⟩
  · intro x y hxy
    rw [hreconstruct x, hreconstruct y, hxy]
  · intro r
    refine ⟨r • z, ?_⟩
    simp only [map_smul, hcontract, smul_eq_mul, mul_one]

/-- An `R`-module is invertible if and only if it is finite locally free of rank one.

This is the module-theoretic characterization of line bundles; see
[Stacks, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I). -/
theorem invertible_iff_isLocallyFreeRankOne :
    Module.Invertible R M ↔ IsLocallyFreeRankOne R M := by
  constructor
  · intro h
    let : Module.Invertible R M := h
    refine ⟨inferInstance, inferInstance, funext fun P ↦ ?_⟩
    simpa only [Module.rankAtStalk, Pi.one_apply] using Module.Invertible.finrank_eq_one
      (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl M)
  · rintro ⟨hfinite, hprojective, hrank⟩
    let : Module.Finite R M := hfinite
    let : Module.Projective R M := hprojective
    exact invertible_of_finite_projective_of_rankAtStalk_eq_one hrank

/-- An invertible module satisfies the rank-one identity for its evaluation pairing. -/
theorem isRankOnePairing_of_invertible [Module.Invertible R M] : IsRankOnePairing R M :=
  (invertible_iff_isLocallyFreeRankOne.mp inferInstance).isRankOnePairing

end Module
