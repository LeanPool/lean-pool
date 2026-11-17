/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection
public import LeanPool.CCDN.Noether.FormalPlaneDifferentiation
import LeanPool.CCDN.Determinant.PlaneSingularities
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The finite linear system producing Frobenius auxiliary coefficients.
A strict dimension inequality gives a nontrivial solution. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma planeTangent_totalDegree_le {K : Type*} [Field K]
    (f h : MvPolynomial (Fin 2) K) (j : Fin 2) :
    (planeTangent f j h).totalDegree ≤ h.totalDegree + f.totalDegree := by
  rw [planeTangent_apply]
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by
      have h1 := pderiv_totalDegree_le f j.rev
      have h2 := pderiv_totalDegree_le h j
      omega)
  · exact (totalDegree_mul _ _).trans (by
      have h1 := pderiv_totalDegree_le f j
      have h2 := pderiv_totalDegree_le h j.rev
      omega)

private lemma planeTangent_iterate_totalDegree_le {K : Type*} [Field K]
    (f h : MvPolynomial (Fin 2) K) (j : Fin 2) (r : ℕ) :
    ((planeTangent f j)^[r] h).totalDegree ≤ h.totalDegree + r * f.totalDegree := by
  induction r with
  | zero => simp
  | succ r hr =>
    rw [Function.iterate_succ_apply']
    exact (planeTangent_totalDegree_le f _ j).trans (by nlinarith)

/-- Independent bounded-degree coefficient classes and more unknowns than
constraints yield bounded-degree auxiliary coefficients. -/
theorem exists_planeFrobenius_coefficients {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ]
    (f : MvPolynomial (Fin 2) K) (j : Fin 2)
    (h : ι → MvPolynomial (Fin 2) K) (b : κ → MvPolynomial (Fin 2) K)
    {D A N : ℕ} (hd : ∀ i, (h i).totalDegree ≤ D) (hb : ∀ k, (b k).totalDegree ≤ A)
    (hbi : LinearIndependent K (fun k => (Ideal.Quotient.mkₐ K (Ideal.span {f})) (b k)))
    (hdim : (∑ r : Fin N, Module.finrank K
      (filteredCoordinateSpace (Ideal.span {f}) (D + A + r.val * f.totalDegree))) <
      Fintype.card ι * Fintype.card κ) :
    ∃ a : ι → MvPolynomial (Fin 2) K,
      (∀ i, (a i).totalDegree ≤ A) ∧ (∃ i, ¬ f ∣ a i) ∧
      ∀ r < N, f ∣ ∑ i, (planeTangent f j)^[r] (h i) * a i := by
  classical
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  let π := Ideal.Quotient.mkₐ K I
  let V (r : Fin N) := filteredCoordinateSpace I (D + A + r.val * f.totalDegree)
  let v (r : Fin N) (t : ι × κ) : V r :=
    ⟨π ((planeTangent f j)^[r.val] (h t.1) * b t.2), by
      apply Submodule.mem_map.mpr
      refine ⟨_, ?_, rfl⟩
      rw [mem_restrictTotalDegree]
      exact (totalDegree_mul _ _).trans (by
        have hh := planeTangent_iterate_totalDegree_le f (h t.1) j r.val
        have hh' := hd t.1
        have hb' := hb t.2
        omega)⟩
  let F : (ι × κ → K) →ₗ[K] (∀ r, V r) :=
    { toFun := fun c r => ∑ t, c t • v r t
      map_add' := by intros; funext r; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intros
        funext r
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hdim' : Module.finrank K (∀ r, V r) < Module.finrank K (ι × κ → K) := by
    rw [Module.finrank_pi, Fintype.card_prod, Module.finrank_pi_fintype]
    exact hdim
  obtain ⟨c, hFc, hc⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := F) hdim')
  rw [LinearMap.mem_ker] at hFc
  let a : ι → MvPolynomial (Fin 2) K := fun i => ∑ k, c (i, k) • b k
  refine ⟨a, ?_, ?_, ?_⟩
  · intro i
    apply totalDegree_finsetSum_le
    intro k _
    exact (totalDegree_smul_le _ _).trans (hb k)
  · by_contra! hn
    apply hc
    funext t
    have he : π (a t.1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hn t.1))
    have hs : ∑ k, c (t.1, k) • π (b k) = 0 := by
      simpa only [a, map_sum, map_smul] using he
    exact Fintype.linearIndependent_iff.mp hbi (fun k => c (t.1, k)) hs t.2
  · intro r hr
    have he := congrArg Subtype.val (congrFun hFc (⟨r, hr⟩ : Fin N))
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π (∑ i, (planeTangent f j)^[r] (h i) * a i) = 0
    simpa only [F, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
      Submodule.coe_smul, v, Fintype.sum_prod_type, a, Finset.mul_sum,
      mul_smul_comm, map_sum, map_smul, Pi.zero_apply, ZeroMemClass.coe_zero] using he

end
end CCDN
