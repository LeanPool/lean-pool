/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.FreeMvPolynomial
public import Mathlib.LinearAlgebra.Unimodular

/-!
# Suslin's completion theorem

Over a principal ideal domain `k`, every unimodular vector `v ∈ k[X₁, …, Xₙ]ᵐ⁺¹` is the first
column of an invertible matrix (Suslin 1976; Lombardi–Quitté, Theorem XVI.5.5, for a field).

The proof goes through the kernel of a linear form. If `φ(v) = 1`, then `Rᵐ⁺¹` is the direct
sum of `R v` and `ker φ`, so `ker φ` is a finitely generated projective module, free by the
Quillen–Suslin theorem, and of rank `m` by comparing ranks. A basis of `ker φ` together with `v`
is a basis of `Rᵐ⁺¹`, and the matrix of the corresponding automorphism has first column `v`.

## Main results

* `prodKerEquiv`: the splitting `R × ker φ ≃ Rᵐ⁺¹`, `(r, x) ↦ r v + x`, when `φ(v) = 1`.
* `kerEquivKer`: kernels of two linear forms taking the value `1` at `v` are isomorphic.
* `exists_linearEquiv_apply_eq_of_kerEquiv`: if `φ(v) = 1`, `φ'(v') = 1` and the kernels are
  isomorphic, an automorphism sends `v` to `v'`.
* `toGL`: the invertible matrix of a linear automorphism of `ι → R`.
* `exists_generalLinearGroup_col_eq_of_free_ker`: over a nontrivial commutative ring, if
  `φ(v) = 1` and `ker φ` is free, then `v` is the first column of an invertible matrix.
* `exists_generalLinearGroup_col_eq_of_isUnimodular`: Suslin's completion theorem.

## References

* A. A. Suslin, *Projective modules over polynomial rings are free*, Dokl. Akad. Nauk SSSR 229
  (1976), 1063–1066.
* H. Lombardi, C. Quitté, *Commutative Algebra: Constructive Methods*, Springer, 2015.
-/

@[expose] public noncomputable section

universe u

namespace LeanPool.QuillenSuslin

section Splitting

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The projection `x ↦ x - φ(x) v` onto the kernel of `φ`, when `φ(v) = 1`. -/
def projKer (φ : M →ₗ[R] R) {v : M} (hv : φ v = 1) : M →ₗ[R] LinearMap.ker φ :=
  LinearMap.codRestrict (LinearMap.ker φ)
    (LinearMap.id - (LinearMap.toSpanSingleton R M v).comp φ)
    (fun x => by simp [hv])

@[simp]
theorem coe_projKer_apply (φ : M →ₗ[R] R) {v : M} (hv : φ v = 1) (x : M) :
    (projKer φ hv x : M) = x - φ x • v := rfl

/-- The splitting `R × ker φ ≃ M`, `(r, x) ↦ r v + x`, for a linear form `φ` with `φ(v) = 1`. -/
def prodKerEquiv (φ : M →ₗ[R] R) {v : M} (hv : φ v = 1) : (R × LinearMap.ker φ) ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap
    (f := LinearMap.coprod (LinearMap.toSpanSingleton R M v) (LinearMap.ker φ).subtype)
    (g := LinearMap.prod φ (projKer φ hv))
    (by ext x; simp)
    (by
      apply LinearMap.prod_ext
      · ext <;> simp [hv]
      · ext x
        · simp [LinearMap.mem_ker.mp x.2]
        · simp [LinearMap.mem_ker.mp x.2])

@[simp]
theorem prodKerEquiv_apply (φ : M →ₗ[R] R) {v : M} (hv : φ v = 1) (x : R × LinearMap.ker φ) :
    prodKerEquiv φ hv x = x.1 • v + x.2 := rfl

/-- The kernel of a linear form taking the value `1` is a direct summand. -/
theorem projKer_comp_subtype (φ : M →ₗ[R] R) {v : M} (hv : φ v = 1) :
    (projKer φ hv).comp (LinearMap.ker φ).subtype = LinearMap.id := by
  ext x
  simp [LinearMap.mem_ker.mp x.2]

/-- The kernel of a linear form taking the value `1` on a finitely generated projective module
is finitely generated projective. -/
theorem projective_ker [Module.Projective R M] (φ : M →ₗ[R] R) {v : M} (hv : φ v = 1) :
    Module.Projective R (LinearMap.ker φ) :=
  Module.Projective.of_split _ _ (projKer_comp_subtype φ hv)

/-- The kernel of a linear form taking the value `1` on a finitely generated module is finitely
generated. -/
theorem finite_ker [Module.Finite R M] (φ : M →ₗ[R] R) {v : M} (hv : φ v = 1) :
    Module.Finite R (LinearMap.ker φ) :=
  Module.Finite.of_surjective (projKer φ hv) fun x =>
    ⟨x, LinearMap.congr_fun (projKer_comp_subtype φ hv) x⟩

/-- The kernels of two linear forms taking the value `1` at the same vector `v` are isomorphic,
through `x ↦ x - φ'(x) v`. -/
def kerEquivKer (φ φ' : M →ₗ[R] R) {v : M} (hv : φ v = 1) (hv' : φ' v = 1) :
    LinearMap.ker φ ≃ₗ[R] LinearMap.ker φ' :=
  LinearEquiv.ofLinearMap (f := (projKer φ' hv').comp (LinearMap.ker φ).subtype)
    (g := (projKer φ hv).comp (LinearMap.ker φ').subtype)
    (by ext x; simp [LinearMap.mem_ker.mp x.2, hv'])
    (by ext x; simp [LinearMap.mem_ker.mp x.2, hv])

/-- If linear forms `φ`, `φ'` take the value `1` at `v`, `v'` and have isomorphic kernels, then
some automorphism of `M` sends `v` to `v'`. -/
theorem exists_linearEquiv_apply_eq_of_kerEquiv (φ φ' : M →ₗ[R] R) {v v' : M} (hv : φ v = 1)
    (hv' : φ' v' = 1) (e : LinearMap.ker φ ≃ₗ[R] LinearMap.ker φ') :
    ∃ E : M ≃ₗ[R] M, E v = v' := by
  refine ⟨(prodKerEquiv φ hv).symm ≪≫ₗ (LinearEquiv.refl R R).prodCongr e ≪≫ₗ
    prodKerEquiv φ' hv', ?_⟩
  have h : (prodKerEquiv φ hv).symm v = (1, 0) := by
    apply (prodKerEquiv φ hv).injective
    simp
  simp [h]

end Splitting

section GeneralLinear

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The invertible matrix of a linear automorphism of `ι → R`. -/
def toGL (E : (ι → R) ≃ₗ[R] (ι → R)) : GL ι R :=
  ⟨LinearMap.toMatrix' (E : (ι → R) →ₗ[R] _), LinearMap.toMatrix' (E.symm : (ι → R) →ₗ[R] _),
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]⟩

@[simp]
theorem coe_toGL (E : (ι → R) ≃ₗ[R] (ι → R)) :
    (toGL E : Matrix ι ι R) = LinearMap.toMatrix' (E : (ι → R) →ₗ[R] _) := rfl

/-- The matrix `toGL E` acts on vectors as `E`. -/
theorem toGL_mulVec (E : (ι → R) ≃ₗ[R] (ι → R)) (x : ι → R) :
    (toGL E : Matrix ι ι R).mulVec x = E x := by
  rw [coe_toGL, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

end GeneralLinear

section Completion

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Over a nontrivial commutative ring, if a linear form `φ` takes the value `1` at
`v ∈ Rᵐ⁺¹` and its kernel is free, then `v` is the first column of an invertible matrix. -/
theorem exists_generalLinearGroup_col_eq_of_free_ker {m : ℕ} (v : Fin (m + 1) → R)
    (φ : (Fin (m + 1) → R) →ₗ[R] R) (hv : φ v = 1) [Module.Free R (LinearMap.ker φ)] :
    ∃ g : GL (Fin (m + 1)) R, ∀ i, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) i 0 = v i := by
  have : Module.Finite R (LinearMap.ker φ) := finite_ker φ hv
  have hrank : Module.finrank R (LinearMap.ker φ) = m := by
    have h := (prodKerEquiv φ hv).finrank_eq
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at h
    omega
  let b := Module.finBasisOfFinrankEq R (LinearMap.ker φ) hrank
  let E : (Fin (m + 1) → R) ≃ₗ[R] (Fin (m + 1) → R) :=
    (Fin.consLinearEquiv R fun _ : Fin (m + 1) => R).symm ≪≫ₗ
      (LinearEquiv.refl R R).prodCongr b.equivFun.symm ≪≫ₗ prodKerEquiv φ hv
  have hE : E (Pi.single 0 1) = v := by
    have h0 : (Fin.consLinearEquiv R fun _ : Fin (m + 1) => R).symm (Pi.single 0 1) =
        ((1 : R), (0 : Fin m → R)) := by
      apply (Fin.consLinearEquiv R fun _ : Fin (m + 1) => R).injective
      rw [LinearEquiv.apply_symm_apply]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.consLinearEquiv, Fin.consEquiv]
    simp [E, h0]
  exact ⟨toGL E, fun i => by simp [hE]⟩

end Completion

/-- **5.4.** Suslin: over a principal ideal domain `k`, every unimodular vector over
`k[X₁, …, Xₙ]` is the first column of an invertible matrix (Lombardi–Quitté, Theorem XVI.5.5,
for a field; Suslin 1976). The kernel of a linear form taking the value `1` at `v` is finitely
generated projective, hence free by the Quillen–Suslin theorem. -/
theorem exists_generalLinearGroup_col_eq_of_isUnimodular (k : Type u) [CommRing k] [IsDomain k]
    [IsPrincipalIdealRing k] (n m : ℕ) (v : Fin (m + 1) → MvPolynomial (Fin n) k)
    (hv : Module.IsUnimodular (MvPolynomial (Fin n) k) v) :
    ∃ g : GL (Fin (m + 1)) (MvPolynomial (Fin n) k),
      ∀ i, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin n) k)) i 0 = v i := by
  obtain ⟨φ, hφ⟩ := Module.isUnimodular_iff.mp hv
  have := finite_ker φ hφ
  have := projective_ker φ hφ
  have := free_mvPolynomial k n (LinearMap.ker φ)
  exact exists_generalLinearGroup_col_eq_of_free_ker v φ hφ

end LeanPool.QuillenSuslin
