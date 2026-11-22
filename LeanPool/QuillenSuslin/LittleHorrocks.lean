/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.Unimodular
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Little Horrocks' global theorem

Let `f ∈ A[X]ⁿ` be unimodular, and let `d` be formal degrees with `deg fᵢ ≤ dᵢ` such that the
coefficients of `fᵢ` in degree `dᵢ` generate the unit ideal of `A`. Then some invertible matrix
`g` over `A[X]` sends `f` to its value `f(0)` at `X = 0` (Lombardi–Quitté, Theorem XVI.5.15).

The proof here goes through projective modules rather than elementary operations. Choose `ψ`
with `ψ · f = 1`, and let `K = ker ψ ⊆ A[X]ⁿ`, a finitely generated projective module with
`A[X]ⁿ = A[X] f ⊕ K`. The kernels of such linear forms commute with base change. At a maximal
ideal `m` of `A`, some coefficient `fᵢ[dᵢ]` is a unit of `A_m`, so the image of `fᵢ` is a unit
times a monic polynomial and becomes a unit over `A_m⟨X⟩`. A unimodular vector with a unit
coordinate has a free complement, so the base change of `K` to `A_m⟨X⟩` is free, and the local
Horrocks theorem shows that the base change of `K` to `A_m[X]` is free. Quillen patching then
proves that `K` is extended from `A`, hence isomorphic to `A[X] ⊗ K(0)`, and `K(0)` is the kernel
of `ψ(0)` on `Aⁿ`. Therefore `K` is isomorphic to the kernel of `ψ(0)` on `A[X]ⁿ`, and the two
splittings `A[X]ⁿ ≅ A[X] × K` give an automorphism of `A[X]ⁿ` sending `f` to `f(0)`.

## Main results

* `dotForm`: the linear form `x ↦ ∑ ψᵢ xᵢ` on `ι → R`.
* `kerBaseChange`: `S ⊗[R] ker ψ ≅ ker ψ_S` when `ψ` takes the value `1` somewhere.
* `free_ker_dotForm_of_isUnit`: the kernel is free when the vector has a unit coordinate.
* `isExtendedFrom_ker_dotForm`: the kernel `K` above is extended from `A`.
* `exists_mulVec_eq_eval_zero`: little Horrocks' global theorem.

## References

* H. Lombardi, C. Quitté, *Commutative Algebra: Constructive Methods*, Springer, 2015,
  Section XVI.5.
* S. Lang, *Algebra*, Springer, 2002, Section XXI.3.
* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

section DotForm

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

/-- The linear form `x ↦ ∑ ψᵢ xᵢ` on `ι → R`. -/
def dotForm (ψ : ι → R) : (ι → R) →ₗ[R] R where
  toFun x := ∑ i, ψ i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

@[simp]
theorem dotForm_apply (ψ x : ι → R) : dotForm ψ x = ∑ i, ψ i * x i := rfl

/-- A ring homomorphism maps `ψ · x` to `σ(ψ) · σ(x)`. -/
theorem dotForm_map {S : Type*} [CommRing S] (σ : R →+* S) (ψ x : ι → R) :
    dotForm (fun i => σ (ψ i)) (fun i => σ (x i)) = σ (dotForm ψ x) := by
  simp [map_sum]

end DotForm

section BaseChange

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {ψ v : ι → R} {ψS : ι → S}

/-- The base change of the inclusion `ker ψ → ι → R`, landing in the kernel of `ψ_S`. -/
def kerBaseChangeFwd (hψ : ∀ i, ψS i = algebraMap R S (ψ i)) :
    S ⊗[R] LinearMap.ker (dotForm ψ) →ₗ[S] LinearMap.ker (dotForm ψS) :=
  LinearMap.codRestrict _ ((piScalarRight R S S ι).toLinearMap ∘ₗ
    LinearMap.baseChange S (LinearMap.ker (dotForm ψ)).subtype) fun t => by
    induction t using TensorProduct.inductionOn with
    | tmul s k =>
      have hk : ∑ i, ψ i * (k : ι → R) i = 0 := LinearMap.mem_ker.mp k.2
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.baseChange_tmul, Submodule.subtype_apply, piScalarRight_apply,
        piScalarRightHom_tmul, dotForm_apply, Algebra.mul_smul_comm]
      calc ∑ i, (k : ι → R) i • (ψS i * s) = algebraMap R S (∑ i, ψ i * (k : ι → R) i) * s := by
            simp only [hψ, Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hk, map_zero, zero_mul]
    | add x y hx hy => simp only [map_add]; exact add_mem hx hy

/-- After base change, the projection `x ↦ x - ψ(x) v` onto `ker ψ` becomes
`y ↦ y - ψ_S(y) v_S`. -/
theorem kerBaseChange_key (hv : dotForm ψ v = 1) (hψ : ∀ i, ψS i = algebraMap R S (ψ i)) :
    (piScalarRight R S S ι).toLinearMap ∘ₗ
      LinearMap.baseChange S ((LinearMap.ker (dotForm ψ)).subtype ∘ₗ projKer (dotForm ψ) hv) ∘ₗ
        (piScalarRight R S S ι).symm.toLinearMap =
      LinearMap.id - (LinearMap.toSpanSingleton S _ fun i => algebraMap R S (v i)) ∘ₗ
        dotForm ψS := by
  ext i j
  simp [Pi.single_apply, hψ, Algebra.smul_def]

/-- Kernels of linear forms taking the value `1` commute with base change:
`S ⊗[R] ker ψ ≅ ker ψ_S`. -/
def kerBaseChange (hv : dotForm ψ v = 1) (hψ : ∀ i, ψS i = algebraMap R S (ψ i)) :
    S ⊗[R] LinearMap.ker (dotForm ψ) ≃ₗ[S] LinearMap.ker (dotForm ψS) :=
  LinearEquiv.ofLinearMap (f := kerBaseChangeFwd hψ)
    (g := LinearMap.baseChange S (projKer (dotForm ψ) hv) ∘ₗ
      (piScalarRight R S S ι).symm.toLinearMap ∘ₗ (LinearMap.ker (dotForm ψS)).subtype)
    (by
      ext y : 2
      have := LinearMap.congr_fun (kerBaseChange_key hv hψ) (y : ι → S)
      simp only [LinearMap.comp_apply, LinearMap.baseChange_comp, LinearEquiv.coe_coe,
        LinearMap.sub_apply, LinearMap.id_apply, LinearMap.toSpanSingleton_apply,
        LinearMap.mem_ker.mp y.2, zero_smul, sub_zero] at this
      simpa [kerBaseChangeFwd] using this)
    (by
      ext k
      simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.comp_apply, LinearMap.id_apply]
      have hfwd : (LinearMap.ker (dotForm ψS)).subtype (kerBaseChangeFwd hψ (1 ⊗ₜ k)) =
          piScalarRight R S S ι (1 ⊗ₜ (k : ι → R)) := rfl
      rw [hfwd, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
      congr 1
      exact LinearMap.congr_fun (projKer_comp_subtype (dotForm ψ) hv) k)

end BaseChange

section UnitCoordinate

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The kernel of `x ↦ c xⱼ` for a unit `c` is the module of vectors vanishing at `j`. -/
def kerSingleEquiv (j : ι) (c : Rˣ) :
    LinearMap.ker (dotForm (Pi.single j (c : R))) ≃ₗ[R] ({i // i ≠ j} → R) where
  toFun x i := (x : ι → R) i
  invFun g := ⟨fun i => if h : i = j then 0 else g ⟨i, h⟩, by
    simp only [LinearMap.mem_ker, dotForm_apply]
    exact Finset.sum_eq_zero fun i _ => by
      by_cases h : i = j
      · simp [h]
      · simp [h]⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := by
    have hx' : (x : ι → R) j = 0 := by
      have := LinearMap.mem_ker.mp x.2
      rw [dotForm_apply] at this
      simpa [Pi.single_apply] using this
    ext i
    by_cases h : i = j
    · subst h; simp [hx']
    · simp [h]
  right_inv g := by
    ext i
    simp [i.2]

omit [DecidableEq ι] in
/-- If `ψ(v) = 1` and some coordinate of `v` is a unit, then the kernel of `ψ` is free. -/
theorem free_ker_dotForm_of_isUnit {ψ v : ι → R} (hv : dotForm ψ v = 1) {j : ι}
    (hj : IsUnit (v j)) : Module.Free R (LinearMap.ker (dotForm ψ)) := by
  classical
  have hv' : dotForm (Pi.single j ((hj.unit⁻¹ : Rˣ) : R)) v = 1 := by
    simp [Pi.single_apply]
  exact Module.Free.of_equiv (kerEquivKer _ _ hv hv' ≪≫ₗ kerSingleEquiv j hj.unit⁻¹).symm

end UnitCoordinate

section Horrocks

variable {A : Type u} [CommRing A] {n : ℕ} {ψ f : Fin n → A[X]}

/-- Over a local `A`-algebra `B`, the kernel of `ψ` becomes free over `B[X]` as soon as some `fᵢ`
has a coefficient of degree `dᵢ ≥ deg fᵢ` whose image in `B` is a unit. -/
theorem isExtendedAfter_ker_dotForm (hv : dotForm ψ f = 1) (B : Type u) [CommRing B]
    [Algebra A B] [IsLocalRing B] (i : Fin n) (d : ℕ) (hd : (f i).natDegree ≤ d)
    (hi : IsUnit (algebraMap A B ((f i).coeff d))) :
    IsExtendedAfter A B (LinearMap.ker (dotForm ψ)) := by
  let _ := Polynomial.algebra A B
  let ψB : Fin n → B[X] := fun i => algebraMap A[X] B[X] (ψ i)
  let fB : Fin n → B[X] := fun i => algebraMap A[X] B[X] (f i)
  have hB : dotForm ψB fB = 1 := by
    rw [dotForm_map, hv, map_one]
  let e := kerBaseChange (S := B[X]) (ψS := ψB) hv fun _ => rfl
  refine (isExtendedFrom_congr e).mpr ?_
  have := finite_ker _ hB
  have := projective_ker _ hB
  let L := Localization (monicSubmonoid B)
  have hL :
      dotForm (fun i => algebraMap B[X] L (ψB i)) (fun i => algebraMap B[X] L (fB i)) = 1 := by
    rw [dotForm_map, hB, map_one]
  have hunit : IsUnit (algebraMap B[X] L (fB i)) := by
    set u := hi.unit
    have hmonic : (C ((u⁻¹ : Bˣ) : B) * fB i).Monic := by
      refine monic_of_natDegree_le_of_coeff_eq_one d ?_ ?_
      · exact (natDegree_C_mul_le _ _).trans ((natDegree_map_le).trans hd)
      · simp [fB, coeff_map, u]
    have hfB : fB i = C (u : B) * (C ((u⁻¹ : Bˣ) : B) * fB i) := by
      rw [← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul]
    rw [hfB, map_mul]
    exact (u.isUnit.map _ |>.map _).mul
      (IsLocalization.map_units L (⟨_, hmonic⟩ : monicSubmonoid B))
  have := free_ker_dotForm_of_isUnit hL hunit
  have hfree := Module.Free.of_equiv (kerBaseChange (S := L) hB (fun _ => rfl)).symm
  have := free_of_free_monicLocalization_of_isLocalRing (LinearMap.ker (dotForm ψB)) hfree
  exact IsExtendedFrom.of_free

/-- The kernel `K` of `ψ`, where `ψ(f) = 1` and the head coefficients of `f` generate the unit
ideal, is extended from `A`. -/
theorem isExtendedFrom_ker_dotForm (hv : dotForm ψ f = 1) (d : Fin n → ℕ)
    (hd : ∀ i : Fin n, (f i).natDegree ≤ d i)
    (hhead : Ideal.span (Set.range fun i : Fin n => (f i).coeff (d i)) = ⊤) :
    IsExtendedFrom A A[X] (LinearMap.ker (dotForm ψ)) := by
  have := finite_ker _ hv
  have := projective_ker _ hv
  have := Module.finitePresentation_of_projective A[X] (LinearMap.ker (dotForm ψ))
  refine isExtendedFrom_of_forall_isMaximal _ fun m hm => ?_
  obtain ⟨i, hi⟩ : ∃ i, (f i).coeff (d i) ∉ m := by
    by_contra! h
    exact hm.ne_top (top_le_iff.mp (hhead ▸ Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)))
  exact isExtendedAfter_ker_dotForm hv (Localization.AtPrime m) i (d i) (hd i)
    ((IsLocalization.AtPrime.isUnit_to_map_iff _ m _).mpr hi)

/-- If the kernel of `ψ` is extended from `A`, it is isomorphic to the kernel of `ψ(0)`. -/
def kerEquivEvalZero (hv : dotForm ψ f = 1)
    (h : IsExtendedFrom A A[X] (LinearMap.ker (dotForm ψ))) :
    LinearMap.ker (dotForm ψ) ≃ₗ[A[X]]
      LinearMap.ker (dotForm fun i => C ((ψ i).eval 0)) :=
  letI := evalZeroAlgebra A
  let ψA : Fin n → A := fun i => (ψ i).eval 0
  have hvA : dotForm ψA (fun i => (f i).eval 0) = 1 := by
    simp only [ψA]
    rw [show (fun i => (ψ i).eval 0) = fun i => evalRingHom 0 (ψ i) from rfl,
      show (fun i => (f i).eval 0) = fun i => evalRingHom 0 (f i) from rfl, dotForm_map, hv,
      map_one]
  ((isExtendedFrom_iff_evalZero rfl _).mp h).some ≪≫ₗ
    LinearEquiv.baseChange A A[X] _ _ (kerBaseChange (S := A) (ψS := ψA) hv fun _ => rfl) ≪≫ₗ
    kerBaseChange (S := A[X]) hvA fun _ => by simp [ψA]

end Horrocks

/-- **5.1.** Little Horrocks' global theorem: a unimodular vector over `A[X]` whose head ideal,
for some formal degrees `d`, is the unit ideal is equivalent under `GLₙ(A[X])` to its value at
`X = 0` (Lombardi–Quitté, Theorem XVI.5.15). -/
theorem exists_mulVec_eq_eval_zero {A : Type u} [CommRing A] {n : ℕ} (f : Fin n → A[X])
    (hf : Ideal.span (Set.range f) = ⊤) (d : Fin n → ℕ) (hd : ∀ i : Fin n, (f i).natDegree ≤ d i)
    (hhead : Ideal.span (Set.range fun i : Fin n => (f i).coeff (d i)) = ⊤) :
    ∃ g : GL (Fin n) A[X],
      (g : Matrix (Fin n) (Fin n) A[X]).mulVec f = fun i : Fin n => C ((f i).eval 0) := by
  obtain ⟨ψ, hψ⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hf ▸ Submodule.mem_top :
    (1 : A[X]) ∈ Ideal.span (Set.range f))
  have hv : dotForm ψ f = 1 := hψ
  have hv0 : dotForm (fun i => C ((ψ i).eval 0)) (fun i => C ((f i).eval 0)) = 1 := by
    rw [show (fun i => C ((ψ i).eval 0)) = fun i => (C.comp (evalRingHom 0)) (ψ i) from rfl,
      show (fun i => C ((f i).eval 0)) = fun i => (C.comp (evalRingHom 0)) (f i) from rfl,
      dotForm_map, hv, map_one]
  obtain ⟨E, hE⟩ := exists_linearEquiv_apply_eq_of_kerEquiv _ _ hv hv0
    (kerEquivEvalZero hv (isExtendedFrom_ker_dotForm hv d hd hhead))
  exact ⟨toGL E, by rw [toGL_mulVec, hE]⟩

end LeanPool.QuillenSuslin
