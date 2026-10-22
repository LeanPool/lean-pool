/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Basic
import LeanPool.CCDN.Algebra.SectionImageRank
import LeanPool.CCDN.ForMathlib.PowerSeries
import LeanPool.CCDN.Hilbert.PlaneHilbert
import LeanPool.CCDN.Noether.FormalPlaneBranch
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleRing.Principal

/-! A formal plane parameterization with a free coordinate has exactly the
curve equation as its kernel. The proof uses the section-image rank bound
and arbitrarily many independent powers of the formal parameter. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A formal map of an irreducible plane curve, with one coordinate equal to
X+a, kills precisely the multiples of its defining equation. -/
private theorem formal_plane_map_eq_zero_iff_dvd {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
    (g : MvPolynomial (Fin 2) K) : ψ g = 0 ↔ f ∣ g := by
  constructor
  · intro hg
    by_contra hnd
    let p : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
    have : p.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
    let φ : (MvPolynomial (Fin 2) K ⧸ p) →ₐ[K] PowerSeries K :=
      Ideal.Quotient.liftₐ p ψ (by
        intro l hl
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hl
        rw [map_mul, hψ, zero_mul])
    have hφ (l : MvPolynomial (Fin 2) K) : φ ((Ideal.Quotient.mk p) l) = ψ l := by
      rfl
    let N := f.totalDegree * g.totalDegree + 1
    let h : Fin N → MvPolynomial (Fin 2) K := fun i => (X j - C a) ^ i.val
    have hi : LinearIndependent K (fun i => φ ((Ideal.Quotient.mk p) (h i))) := by
      have he : (fun i => φ ((Ideal.Quotient.mk p) (h i))) =
          (fun i : Fin N => (PowerSeries.X : PowerSeries K) ^ i.val) := by
        funext i
        rw [hφ]
        simp only [h, map_pow, hparam]
      rw [he]
      exact PowerSeries.linearIndependent_of_order_injective _ Fin.val Fin.val_injective
        (fun i => PowerSeries.order_X_pow i.val)
    have hh := section_image_rank_le p f.totalDegree
      ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
        fun M hM => principal_plane_hilbert_function f hf.ne_zero hM⟩
      φ h hi g (by simpa only [p, Ideal.mem_span_singleton] using hnd) g.totalDegree le_rfl
      (by rw [hφ]; exact hg)
    rw [Fintype.card_fin] at hh
    dsimp only [N] at hh
    omega
  · rintro ⟨q, rfl⟩
    rw [map_mul, hψ, zero_mul]

/-- The substitution map attached to a chosen formal branch. -/
private def formalPlaneBranchMap {K : Type*} [Field K]
    (z : Fin 2 → K) (j : Fin 2) (g : PowerSeries K) :
    MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K :=
  MvPolynomial.aeval (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev))

private lemma formalPlaneBranchMap_parameter {K : Type*} [Field K]
    (z : Fin 2 → K) (j : Fin 2) (g : PowerSeries K) :
    formalPlaneBranchMap z j g (X j.rev - C (z j.rev)) = PowerSeries.X := by
  fin_cases j <;> simp [formalPlaneBranchMap, PowerSeries.algebraMap_eq]

private lemma formalPlaneBranchMap_constant {K : Type*} [Field K]
    (z : Fin 2 → K) (j : Fin 2) (g : PowerSeries K)
    (hg : PowerSeries.constantCoeff g = z j) (f : MvPolynomial (Fin 2) K) :
    PowerSeries.constantCoeff (formalPlaneBranchMap z j g f) = eval z f := by
  have he : PowerSeries.constantCoeff.comp (formalPlaneBranchMap z j g).toRingHom = eval z := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [formalPlaneBranchMap, PowerSeries.algebraMap_eq]
    · intro k
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        formalPlaneBranchMap, aeval_X]
      by_cases hk : k = j
      · subst k
        simp [hg]
      · simp only [ite_eq_right hk, map_add, PowerSeries.constantCoeff_X,
          PowerSeries.constantCoeff_C, zero_add]
        have hh := congrFun (plane_coordinate_cases z j) k
        simpa only [ite_eq_right hk, MvPolynomial.eval_X] using hh
  exact RingHom.congr_fun he f

/-- Every nonsingular point on an irreducible plane curve gives a
faithful formal branch, with the original point as its constant evaluation. -/
theorem exists_faithful_formal_plane_branch {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f) (z : Fin 2 → K) (j : Fin 2)
    (hz : eval z f = 0) (hj : eval z (pderiv j f) ≠ 0) :
    ∃ ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K,
      (∀ h, PowerSeries.constantCoeff (ψ h) = eval z h) ∧
      ψ (X j.rev - C (z j.rev)) = PowerSeries.X ∧
      ∀ h, ψ h = 0 ↔ f ∣ h := by
  obtain ⟨g, hg, _⟩ := exists_unique_formal_plane_branch f z j hz hj
  let ψ := formalPlaneBranchMap z j g
  have hψ : ψ f = 0 := by
    simpa only [ψ, formalPlaneBranchMap, MvPolynomial.aeval_def, PowerSeries.algebraMap_eq] using
      hg.2
  refine ⟨ψ, formalPlaneBranchMap_constant z j g hg.1, formalPlaneBranchMap_parameter z j g, ?_⟩
  intro h
  exact formal_plane_map_eq_zero_iff_dvd f hf ψ hψ j.rev (z j.rev)
    (formalPlaneBranchMap_parameter z j g) h

end
end CCDN
