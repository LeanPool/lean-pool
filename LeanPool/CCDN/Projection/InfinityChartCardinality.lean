/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Projection.InfinityParameterReduction
import LeanPool.CCDN.ForMathlib.LinearMap

/-!
The certified affine Hilbert degree bounds the number of geometric
infinity points in each normalized projective chart.

Homogeneous polynomials with extension-field coefficients contribute no
new directions beyond the extension-field span of ground-field monomials.

Finite interpolation in a projective affine chart can be performed by
homogeneous polynomials of any sufficiently large common degree.

Evaluating homogeneous polynomials at geometric infinity points has
L-linear rank at most the corresponding infinity Hilbert piece. The
source curve and its Hilbert function are defined over the original field K.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def homogeneousPointEvaluation {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] (z : ι → σ → L) (m : ℕ) :
    homogeneousSubmodule σ K m →ₗ[K] (ι → L) :=
  LinearMap.pi (fun i => (aeval (z i)).toLinearMap.comp (homogeneousSubmodule σ K m).subtype)

/-- The L-span of evaluations of K-polynomials is controlled by the
infinity quotient. -/
private theorem infinity_evaluation_span_finrank_le {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] [Finite σ] (I : Ideal (MvPolynomial σ K))
    (z : ι → σ → L) (hz : ∀ i, z i ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I))
    (m : ℕ) :
    Module.finrank L
        (Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z (m + 1)))) ≤
      Module.finrank K (infinityGradedSpace I m) := by
  classical
  let := Fintype.ofFinite σ
  let V := homogeneousSubmodule σ K (m + 1)
  let : Module.Finite K V := Module.Finite.of_fg (homogeneousSubmodule_fg σ K (m + 1))
  let f := (infinityCoordinateMap I).toLinearMap.comp V.subtype
  let g := homogeneousPointEvaluation (K := K) z (m + 1)
  have hker : f.ker ≤ g.ker := by
    intro p hp
    have hpI : (p : MvPolynomial σ K) ∈ leadingInfinityIdeal I := hp
    apply LinearMap.mem_ker.mpr
    funext i
    exact hz i _ hpI
  have hrange : f.range ≤ infinityGradedSpace I m := by
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨(Ideal.Quotient.mk I) p,
      ⟨p, (mem_restrictTotalDegree _ _ _).mpr p.property.totalDegree_le, rfl⟩⟩, ?_⟩
    change Ideal.Quotient.mk (projectiveInfinityIdeal I) (projectiveMonomialMap I (m + 1) _) =
      infinityCoordinateMap I p
    change _ = Ideal.Quotient.mk (projectiveInfinityIdeal I) (quotientRadialMap I p)
    rw [quotientRadialMap_homogeneous I p (m + 1) p.property]
  exact (LinearMap.finrank_span_range_le_of_ker_le f g hker).trans (Submodule.finrank_mono hrange)

/-- In stable degrees `m ≥ N`, where the filtered coordinate spaces have dimension `d * m + b`,
the `L`-span of the value vectors `(h (z i))_i` of the homogeneous polynomials `h` of degree
`m + 1` at points `z i` of the cone at infinity has dimension at most `d`. -/
private theorem infinity_evaluation_span_finrank_le_degree {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] [Finite σ] (I : Ideal (MvPolynomial σ K))
    (z : ι → σ → L) (hz : ∀ i, z i ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I))
    {d N : ℕ} {b : ℤ} (hdegree : ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + b)
    (m : ℕ) (hm : N ≤ m) :
    Module.finrank L
        (Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z (m + 1)))) ≤ d := by
  classical
  let := Fintype.ofFinite σ
  exact (infinity_evaluation_span_finrank_le I z hz m).trans_eq
    (infinityGradedSpace_eventually_degree I hdegree m hm)

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma exists_homogeneous_chart_delta {L σ ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]
    (z : ι → σ → L) (hz : Function.Injective z) (j : σ) (hj : ∀ i, z i j = 1)
    (m : ℕ) (hm : Fintype.card ι ≤ m) (i : ι) :
    ∃ p : MvPolynomial σ L, p.IsHomogeneous m ∧
      ∀ k, MvPolynomial.eval (z k) p = if i = k then 1 else 0 := by
  classical
  have hdiff (k : ι) (hik : i ≠ k) : ∃ q : σ, z i q ≠ z k q := by
    by_contra! he
    exact hik (hz (funext he))
  let q (k : ι) (hik : i ≠ k) := (hdiff k hik).choose
  have hq (k : ι) (hik : i ≠ k) : z i (q k hik) - z k (q k hik) ≠ 0 :=
    sub_ne_zero.mpr (hdiff k hik).choose_spec
  let l (k : ι) : MvPolynomial σ L := if hik : i = k then X j else
    C ((z i (q k hik) - z k (q k hik))⁻¹) *
      (X (q k hik) - C (z k (q k hik)) * X j)
  have hl (k : ι) : (l k).IsHomogeneous 1 := by
    dsimp [l]
    split_ifs
    · exact isHomogeneous_X L j
    · exact ((isHomogeneous_X L _).sub (isHomogeneous_C_mul_X _ _)).C_mul _
  have hli (k : ι) : MvPolynomial.eval (z i) (l k) = 1 := by
    dsimp [l]
    split_ifs with hik
    · simp [hj]
    · simp [hj, hq k hik]
  have hlk (k : ι) (hik : i ≠ k) : MvPolynomial.eval (z k) (l k) = 0 := by
    simp [l, hik, hj]
  let p := (∏ k, l k) * X j ^ (m - Fintype.card ι)
  refine ⟨p, ?_, ?_⟩
  · have hh : (∏ k, l k).IsHomogeneous (Fintype.card ι) := by
      simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
        IsHomogeneous.prod Finset.univ l (fun _ => 1) (fun k _ => hl k)
    have ht := hh.mul (isHomogeneous_X_pow j (m - Fintype.card ι))
    simpa only [Nat.add_sub_of_le hm] using ht
  · intro k
    by_cases hik : i = k
    · subst k
      simp [p, hli, hj]
    · have hh : ∏ t, MvPolynomial.eval (z k) (l t) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) (hlk k hik)
      simp [p, hik, hh]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma homogeneous_extension_evaluation_mem {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] (z : ι → σ → L) (m : ℕ) (p : MvPolynomial σ L)
    (hp : p.IsHomogeneous m) :
    (fun i => MvPolynomial.eval (z i) p) ∈
      Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z m)) := by
  classical
  let W := Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z m))
  have hdeg (e : σ →₀ ℕ) (he : e ∈ p.support) : e.degree = m :=
    by
      rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
      exact hp (mem_support_iff.mp he)
  have hmono (e : σ →₀ ℕ) (he : e ∈ p.support) :
      (fun i => MvPolynomial.eval (z i) (monomial e (p.coeff e))) ∈ W := by
    let q : homogeneousSubmodule σ K m := ⟨monomial e 1, isHomogeneous_monomial 1 (hdeg e he)⟩
    have hq : homogeneousPointEvaluation (K := K) z m q ∈ W := Submodule.subset_span ⟨q, rfl⟩
    have hval : (fun i => MvPolynomial.eval (z i) (monomial e (p.coeff e))) =
        p.coeff e • homogeneousPointEvaluation (K := K) z m q := by
      funext i
      simp [homogeneousPointEvaluation, q, MvPolynomial.eval_monomial, aeval_monomial]
    rw [hval]
    exact W.smul_mem _ hq
  have hsum : (fun i => MvPolynomial.eval (z i) p) =
      ∑ e ∈ p.support, (fun i => MvPolynomial.eval (z i) (monomial e (p.coeff e))) := by
    funext i
    simpa only [Finset.sum_apply, map_sum] using congrArg (MvPolynomial.eval (z i)) p.as_sum
  rw [hsum]
  exact W.sum_mem hmono

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma homogeneous_chart_evaluation_span_eq_top {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype ι] (z : ι → σ → L) (hz : Function.Injective z)
    (j : σ) (hj : ∀ i, z i j = 1) (m : ℕ) (hm : Fintype.card ι ≤ m) :
    Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z m)) = ⊤ := by
  classical
  let W := Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z m))
  let b := Pi.basisFun L ι
  have hb (i : ι) : b i ∈ W := by
    obtain ⟨p, hp, he⟩ := exists_homogeneous_chart_delta z hz j hj m hm i
    have hv := homogeneous_extension_evaluation_mem (K := K) z m p hp
    have heq : (fun k => MvPolynomial.eval (z k) p) = b i := by
      funext k
      simp [he, b, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rwa [heq] at hv
  apply top_unique
  intro v _
  rw [← b.sum_repr v]
  exact W.sum_mem (fun i _ => W.smul_mem _ (hb i))

/-- Every finite family of distinct normalized infinity points has size at
most the original affine Hilbert degree, over any extension field. -/
private theorem infinity_chart_card_le_degree {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] [Finite σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (d : ℕ)
    (hdegree : HasFilteredCurveDegree I d)
    (z : ι → σ → L) (hz : ∀ i, z i ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I))
    (hinj : Function.Injective z) (j : σ) (hj : ∀ i, z i j = 1) :
    Fintype.card ι ≤ d := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨N, c, hN⟩ := hdegree
  let m := N + Fintype.card ι
  have hb := infinity_evaluation_span_finrank_le_degree I z hz hN m (by dsimp [m]; omega)
  rw [homogeneous_chart_evaluation_span_eq_top z hinj j hj (m + 1) (by dsimp [m]; omega)] at hb
  simpa only [finrank_top, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] using hb

/-- Each normalized infinity chart is a finite set with at most d
points, not merely a bound for already finite subsets. -/
theorem exists_finite_infinity_chart {K L σ : Type*} [Field K] [Field L]
    [Algebra K L] [Finite σ] (I : Ideal (MvPolynomial σ K)) (d : ℕ)
    (hdegree : HasFilteredCurveDegree I d)
    (j : σ) :
    ∃ S : Finset (σ → L), S.card ≤ d ∧ ∀ z,
      z ∈ S ↔ z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I) ∧ z j = 1 := by
  classical
  let := Fintype.ofFinite σ
  let T := {z : σ → L | z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I) ∧ z j = 1}
  have hT : T.Finite := by
    by_contra hn
    obtain ⟨S, hS, hc⟩ := Set.Infinite.exists_subset_card_eq hn (d + 1)
    have hb := infinity_chart_card_le_degree I d hdegree (fun z : S => z.val)
      (fun z => (hS z.property).1) Subtype.val_injective j (fun z => (hS z.property).2)
    rw [Fintype.card_coe, hc] at hb
    omega
  refine ⟨hT.toFinset, ?_, fun z => hT.mem_toFinset⟩
  have hb := infinity_chart_card_le_degree I d hdegree (fun z : hT.toFinset => z.val)
    (fun z => (hT.mem_toFinset.mp z.property).1) Subtype.val_injective j
    (fun z => (hT.mem_toFinset.mp z.property).2)
  simpa only [Fintype.card_coe] using hb

end
end CCDN
