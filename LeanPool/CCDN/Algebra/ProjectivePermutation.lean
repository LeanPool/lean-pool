/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveSection
public import LeanPool.CCDN.Height.ProjectiveBox
public import LeanPool.CCDN.Hilbert.AffineCurveDegree

/-! Coordinate permutations preserve projective heights, homogeneous
Hilbert functions, and prime coordinate ideals. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The ideal obtained from `I` by permuting the coordinates by `e`: the polynomials `f` with
`rename e f ∈ I`. -/
def projectivePermutedIdeal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : Equiv.Perm (Fin (n + 1))) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  RingHom.ker ((Ideal.Quotient.mkₐ K I).comp (renameEquiv K e).toAlgHom)

/-- A polynomial `f` lies in the permuted ideal `projectivePermutedIdeal I e` if and only if
`rename e f` lies in `I`. -/
lemma mem_projectivePermutedIdeal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : Equiv.Perm (Fin (n + 1)))
    (f : MvPolynomial (Fin (n + 1)) K) :
    f ∈ projectivePermutedIdeal I e ↔ rename e f ∈ I := by
  change (Ideal.Quotient.mk I) (rename e f) = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

instance projectivePermutedIdeal_isPrime {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (e : Equiv.Perm (Fin (n + 1))) : (projectivePermutedIdeal I e).IsPrime :=
  RingHom.ker_isPrime _

private theorem projectiveHilbertFunction_permuted {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : Equiv.Perm (Fin (n + 1))) (M : ℕ) :
    projectiveHilbertFunction (projectivePermutedIdeal I e) M = projectiveHilbertFunction I M := by
  let ψ := (Ideal.Quotient.mkₐ K I).comp (renameEquiv K e).toAlgHom
  let φ := Ideal.kerLiftAlg ψ
  let V := homogeneousCoordinateSpace (RingHom.ker ψ) M
  have he : V.map φ.toLinearMap = homogeneousCoordinateSpace I M := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hu
      exact Submodule.mem_map.mpr ⟨rename e f, hf.rename_isHomogeneous, rfl⟩
    · intro hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      refine Submodule.mem_map.mpr
        ⟨(Ideal.Quotient.mk (RingHom.ker ψ)) (rename e.symm f),
          Submodule.mem_map.mpr ⟨rename e.symm f, hf.rename_isHomogeneous, rfl⟩, ?_⟩
      change (Ideal.Quotient.mk I) (rename e (rename e.symm f)) = (Ideal.Quotient.mk I) f
      exact congrArg (Ideal.Quotient.mk I) ((renameEquiv K e).apply_symm_apply f)
  have h :=
    (Submodule.equivMapOfInjective φ.toLinearMap (Ideal.kerLiftAlg_injective ψ) V).finrank_eq
  rw [he] at h
  exact h

/-- Permuting the coordinates preserves the degree of a projective curve. -/
theorem projectiveCurveDegree_permuted {K : Type*} [Field K] {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : Equiv.Perm (Fin (n + 1)))
    (hdegree : HasProjectiveCurveDegree I d) :
    HasProjectiveCurveDegree (projectivePermutedIdeal I e) d := by
  obtain ⟨N, c, hN⟩ := hdegree
  exact ⟨N, c, fun M hM => by rw [projectiveHilbertFunction_permuted]; exact hN M hM⟩

private def coordinatePermutation {K : Type*} [Field K] {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) :
    (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun v := v ∘ e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma coordinatePermutation_injective {K : Type*} [Field K] {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) :
    Function.Injective (coordinatePermutation (K := K) e) := by
  intro v w he
  funext j
  simpa [coordinatePermutation] using congrFun he (e.symm j)

private def projectivePermutation {K : Type*} [Field K] {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) :
    Projectivization K (Fin (n + 1) → K) → Projectivization K (Fin (n + 1) → K) :=
  Projectivization.map (coordinatePermutation e) (coordinatePermutation_injective e)

private lemma projectivePermutation_injective {K : Type*} [Field K] {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) : Function.Injective (projectivePermutation (K := K) e) :=
  Projectivization.map_injective _ _

private lemma projectivePermutation_height {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (x : ProjectivePoint n) :
    (projectivePermutation e x).mulHeight = x.mulHeight := by
  conv_lhs => rw [← x.mk_rep]
  rw [projectivePermutation, Projectivization.map_mk, Projectivization.mulHeight_mk]
  change Height.mulHeight (x.rep ∘ e) = x.mulHeight
  rw [Height.mulHeight_comp_equiv, projective_rep_height]

private lemma projectivePermutation_zeroLocus {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : Equiv.Perm (Fin (n + 1)))
    (x : Projectivization K (Fin (n + 1) → K)) (hx : x ∈ projectiveIdealZeroLocus I) :
    projectivePermutation e x ∈ projectiveIdealZeroLocus (projectivePermutedIdeal I e) := by
  intro v hv hvx f hf
  have hxperm : coordinatePermutation e x.rep ≠ 0 := by
    intro h
    apply x.rep_nonzero
    apply coordinatePermutation_injective (K := K) e
    simpa only [map_zero] using h
  have he : Projectivization.mk K v hv =
      Projectivization.mk K (coordinatePermutation e x.rep) hxperm := by
    change Projectivization.mk K v hv =
      projectivePermutation e (Projectivization.mk K x.rep x.rep_nonzero)
    rw [x.mk_rep]
    exact hvx
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp he
  have hw : (c : K) • x.rep ≠ 0 := smul_ne_zero c.ne_zero x.rep_nonzero
  have hwx : Projectivization.mk K ((c : K) • x.rep) hw = x := by
    calc
      _ = Projectivization.mk K x.rep x.rep_nonzero :=
        (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨c, rfl⟩
      _ = x := x.mk_rep
  have h := hx ((c : K) • x.rep) hw hwx (rename e f) ((mem_projectivePermutedIdeal I e f).mp hf)
  rw [eval_rename] at h
  have hv' : ((c : K) • x.rep) ∘ e = v := hc
  rwa [hv'] at h

/-- Permuting the coordinates does not decrease the number of rational projective points of
height at most `B` on the zero locus of `I`. -/
theorem projectiveCount_le_permuted {n : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) (e : Equiv.Perm (Fin (n + 1))) (B : ℝ) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤
      projectiveCount (projectiveIdealZeroLocus (projectivePermutedIdeal I e)) B := by
  apply Finset.card_le_card_of_injOn (projectivePermutation e)
  · intro x hx
    obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp hx
    exact mem_projectivePoints.mpr ⟨by rwa [projectivePermutation_height],
      projectivePermutation_zeroLocus I e x hxI⟩
  · exact (projectivePermutation_injective e).injOn

end
end CCDN
