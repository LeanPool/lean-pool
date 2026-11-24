/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermAlgebraicParametrization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermIntegrallyClosed
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.WeierstrassDivisionUniqueness

/-!
# Minimal polynomials over `𝒪_d` and iterated Weierstrass reduction

Blueprint `lag:finite-extension`, `lag:minimal-polynomial-weierstrass`,
`lag:thin-subgerm` (algebraic step) (Demailly, *Complex analytic and differential
geometry*, II.4.13, II.4.26).

For a prime `Q ⊆ 𝒪_n` in Noether position over `𝒪_d`:

* `exists_minpoly_dvd`: every germ `y` has a monic minimal polynomial `W ∈ 𝒪_d[T]` of
  positive degree with `W(y) ∈ Q`, dividing every `F` with `F(y) ∈ Q`;
* `exists_minpoly_isWeierstrass`: if `y(0) = 0`, this `W` is a Weierstrass polynomial;
* `exists_eqn_of_not_mem`: for `f ∉ Q` there is `h ∈ 𝒪_d \ 0` with `h ∈ (f) + Q`;
* `exists_reduce`: modulo Weierstrass polynomials `p_k(z', z_k)`, `d ≤ k < n`, every germ
  is a polynomial in `z_d, …, z_{n-1}` over `𝒪_d`.
-/

@[expose] public section

open Filter Topology Polynomial

namespace SGPT.Foundations.Analysis.Pending.GermMinimalPolynomial

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open HolGerm GermAlgebraicParametrization

variable {n d : ℕ} {Q : Ideal (HolGerm (ComplexModel n))}

/-- Evaluation at `0` commutes with `𝒪_k → 𝒪_n`. -/
theorem eval_projGerm (n k : ℕ) (c : HolGerm (ComplexModel k)) :
    HolGerm.eval (projGerm n k c) = HolGerm.eval c :=
  eval_comap _ c

/-- `𝒪_n → 𝒪_m` commutes with evaluating a polynomial over `𝒪_d`. -/
theorem projGerm_evalGerm {m : ℕ} (hdn : d ≤ n) (F : (HolGerm (ComplexModel d))[X])
    (g : HolGerm (ComplexModel n)) :
    projGerm m n (evalGerm n F g) = evalGerm m F (projGerm m n g) := by
  rw [evalGerm, evalGerm, hom_eval₂]
  congr 1
  exact RingHom.ext fun c => projGerm_projGerm hdn c

/-- Pushing `R(z_0, …, z_{n-1})` to `𝒪_{n+1}` renames the variables along `Fin.castSucc`. -/
theorem projGerm_eval₂_rename (hdn : d ≤ n)
    (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) :
    projGerm (n + 1) n (MvPolynomial.eval₂ (projGerm n d) coord R) =
      MvPolynomial.eval₂ (projGerm (n + 1) d) coord (MvPolynomial.rename Fin.castSucc R) := by
  rw [MvPolynomial.hom_eval₂, MvPolynomial.eval₂_rename]
  congr 1
  · exact RingHom.ext fun c => projGerm_projGerm hdn c
  · funext k
    exact projGerm_coordGerm k.2 n.le_succ

/-- A monic polynomial over `𝒪_d` evaluated at the last coordinate of `ℂ^{n+1}` is a
`weierstrassGerm`. -/
theorem evalGerm_coord_last (hdn : d ≤ n) {W : (HolGerm (ComplexModel d))[X]} (hW : W.Monic) :
    evalGerm (n + 1) W (coord (Fin.last n)) =
      weierstrassGerm (n + 1) n n.lt_succ_self W.natDegree (fun j => projGerm n d (W.coeff j))
        := by
  rw [evalGerm, eval₂_eq_sum_range, Finset.sum_range_succ, hW.coeff_natDegree, map_one, one_mul,
    weierstrassGerm]
  simp only [projGerm_projGerm hdn]
  exact add_comm _ _

theorem exists_minpoly_dvd [Q.IsPrime] (hQ : IsNoetherNormalization Q d)
    (y : HolGerm (ComplexModel n)) :
    ∃ W : (HolGerm (ComplexModel d))[X], W.Monic ∧ 0 < W.natDegree ∧ evalGerm n W y ∈ Q ∧
      ∀ F : (HolGerm (ComplexModel d))[X], evalGerm n F y ∈ Q → W ∣ F := by
  let _ := (quotientStructureMap Q d).toAlgebra
  have : Module.IsTorsionFree (HolGerm (ComplexModel d)) (HolGerm (ComplexModel n) ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hQ.injective
  have key : ∀ F : (HolGerm (ComplexModel d))[X],
      aeval (Ideal.Quotient.mk Q y) F = 0 ↔ evalGerm n F y ∈ Q := fun F => by
    rw [aeval_def, ← Ideal.Quotient.eq_zero_iff_mem, evalGerm, hom_eval₂]
    rfl
  have hx : IsIntegral (HolGerm (ComplexModel d)) (Ideal.Quotient.mk Q y) := hQ.isIntegral _
  exact ⟨minpoly _ _, minpoly.monic hx, minpoly.natDegree_pos hx, (key _).1 (minpoly.aeval _ _),
    fun F hF => minpoly.isIntegrallyClosed_dvd hx ((key F).2 hF)⟩

section Preparation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Uniqueness of the remainder** in Weierstrass division by `prodWeierstrassGerm`. -/
theorem eq_zero_of_mul_prodWeierstrassGerm_add_eq_zero {s : ℕ} {A : ℕ → HolGerm E}
    (hA : ∀ j < s, HolGerm.eval (A j) = 0) {h : HolGerm (E × ℂ)} {r : ℕ → HolGerm E}
    (heq : h * prodWeierstrassGerm s A +
      ∑ j ∈ Finset.range s, ofFst (r j) * lastCoord ^ j = 0) :
    ∀ j < s, r j = 0 := by
  choose a ha hAa using fun j => exists_eq_mk (A j)
  obtain rfl : A = fun j => mk (a j) (ha j) := funext hAa
  choose c hc hrc using fun j => exists_eq_mk (r j)
  obtain rfl : r = fun j => mk (c j) (hc j) := funext hrc
  obtain ⟨H, hH, rfl⟩ := exists_eq_mk h
  rw [prodWeierstrassGerm_eq_mk, sum_ofFst_mul_lastCoord_pow_eq_mk] at heq
  have key := (mk_eq_mk_iff (hf := eventually_differentiableAt_add
    (eventually_differentiableAt_mul hH (eventually_differentiableAt_lastWeierstrass s a ha))
    (eventually_differentiableAt_lastPoly s c hc)) (hg := eventually_differentiableAt_zero)).1 heq
  have hu := (WeierstrassDivisionUniqueness.weierstrass_division_unique ha
    (fun j hj => by simpa only [HolGerm.eval_mk] using hA j hj) hH (r := c)
    (key.mono fun x hx => hx)).1
  intro j hj
  rw [← mk_zero, mk_eq_mk_iff]
  exact hu j hj

/-- **Weierstrass preparation for monic polynomials over `𝒪_E`**: a monic `W ∈ 𝒪_E[T]`
factors as `W = W' Q₁` with `W'` a Weierstrass polynomial of degree `≤ deg W` and
`Q₁(0, 0) ≠ 0`. -/
theorem exists_eq_isWeierstrass_mul {W : (HolGerm E)[X]} (hW : W.Monic) :
    ∃ W' Q₁ : (HolGerm E)[X], W'.Monic ∧
      (∀ j < W'.natDegree, HolGerm.eval (W'.coeff j) = 0) ∧
      W'.natDegree ≤ W.natDegree ∧ W = W' * Q₁ ∧ HolGerm.eval (Q₁.coeff 0) ≠ 0 := by
  classical
  set N := W.natDegree
  have hW₀m : (W.map (HolGerm.eval : HolGerm E →+* ℂ)).Monic := hW.map _
  have hW₀deg : (W.map (HolGerm.eval : HolGerm E →+* ℂ)).natDegree = N := hW.natDegree_map _
  obtain ⟨V₀, hfac, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd
    (W.map (HolGerm.eval : HolGerm E →+* ℂ)) hW₀m.ne_zero 0
  simp only [map_zero, sub_zero] at hfac hndvd
  set a := (W.map (HolGerm.eval : HolGerm E →+* ℂ)).rootMultiplicity 0
  have hV₀ : V₀.eval 0 ≠ 0 := fun h =>
    hndvd (X_dvd_iff.2 (by rw [coeff_zero_eq_eval_zero]; exact h))
  have hV₀ne : V₀ ≠ 0 := fun h => hndvd (h ▸ dvd_zero _)
  have haN : a ≤ N := by
    rw [← hW₀deg, hfac, natDegree_mul (pow_ne_zero _ X_ne_zero) hV₀ne, natDegree_X_pow]
    omega
  choose c hc hcW using fun j => exists_eq_mk (W.coeff j)
  have hG := eventually_differentiableAt_lastPoly (N + 1) c hc
  have hGu : ∀ᶠ t in 𝓝 (0 : ℂ),
      (fun x : E × ℂ => ∑ j ∈ Finset.range (N + 1), c j x.1 * x.2 ^ j) (0, t) =
        t ^ a * V₀.eval t := by
    refine Eventually.of_forall fun t => ?_
    have h1 : (W.map (HolGerm.eval : HolGerm E →+* ℂ)).eval t =
        ∑ j ∈ Finset.range (N + 1), c j 0 * t ^ j := by
      rw [eval_eq_sum_range, hW₀deg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coeff_map, hcW j, HolGerm.eval_mk]
    change ∑ j ∈ Finset.range (N + 1), c j 0 * t ^ j = t ^ a * V₀.eval t
    rw [← h1, hfac, eval_mul, eval_pow, eval_X]
  have hu : AnalyticAt ℂ (fun t => V₀.eval t) 0 := V₀.differentiable.analyticAt 0
  obtain ⟨q, hq, hq0, A, hA, hA0, heq⟩ :=
    HolomorphicGermWeierstrassPreparation.exists_weierstrass_preparation hG hu hV₀ hGu
  set W' : (HolGerm E)[X] := X ^ a + ∑ k ∈ Finset.range a, C (mk (A k) (hA k)) * X ^ k with hW'
  obtain ⟨hW'm, hW'deg⟩ :=
    AnalyticProjectionWeierstrass.monic_X_pow_add_sum a fun k => mk (A k) (hA k)
  have hW'coeff : ∀ j < a, W'.coeff j = mk (A j) (hA j) := by
    intro j hj
    simp only [W', coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow, ite_eq_right hj.ne,
      zero_add]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.2 hj)]
  set Φ := eval₂RingHom (ofFst : HolGerm E →+* HolGerm (E × ℂ)) lastCoord
  have hΦW : Φ W = mk _ hG := by
    rw [coe_eval₂RingHom, eval₂_eq_sum_range]
    simp only [hcW]
    exact sum_ofFst_mul_lastCoord_pow_eq_mk (N + 1) c hc
  have hΦW' : Φ W' = prodWeierstrassGerm a fun k => mk (A k) (hA k) := by
    simp only [W', Φ, coe_eval₂RingHom, eval₂_add, eval₂_X_pow, eval₂_finsetSum,
      eval₂_mul, eval₂_C, prodWeierstrassGerm]
  have hunit : mk q hq * Φ W = Φ W' := by
    rw [hΦW, hΦW', prodWeierstrassGerm_eq_mk]
    exact (mk_eq_mk_iff (hf := eventually_differentiableAt_mul hq hG)).2 heq
  have hqu : IsUnit (mk q hq) := (isUnit_iff_eval_ne_zero _).2 (by rwa [HolGerm.eval_mk])
  obtain ⟨v, hv⟩ := hqu.exists_left_inv
  have hdiv := modByMonic_add_div W W'
  have hR : W %ₘ W' = 0 := by
    by_contra hR
    have hlt : (W %ₘ W').natDegree < a :=
      hW'deg ▸ natDegree_lt_natDegree hR (degree_modByMonic_lt W hW'm)
    have hΦR : Φ (W %ₘ W') =
        ∑ j ∈ Finset.range a, ofFst ((W %ₘ W').coeff j) * lastCoord ^ j := by
      rw [coe_eval₂RingHom, eval₂_eq_sum_range' _ hlt]
    have hdivΦ := congrArg Φ hdiv
    rw [map_add, map_mul] at hdivΦ
    have hzero := eq_zero_of_mul_prodWeierstrassGerm_add_eq_zero (s := a)
      (A := fun k => mk (A k) (hA k)) (fun j hj => by rw [HolGerm.eval_mk]; exact hA0 j hj)
      (h := v * (mk q hq * Φ (W /ₘ W') - 1)) (r := fun j => (W %ₘ W').coeff j)
      (by
        rw [← hΦR, ← hΦW']
        linear_combination (Φ (W /ₘ W') * Φ W' - Φ W) * hv + v * hunit + hdivΦ)
    refine hR (AddMonoidAlgebra.ext (Finsupp.ext fun j => ?_))
    rw [coeff_zero]
    by_cases hj : j < a
    · exact hzero j hj
    · exact coeff_eq_zero_of_natDegree_lt (p := W %ₘ W') (n := j) (by omega)
  have hWQ : W = W' * (W /ₘ W') := by
    rw [hR, zero_add] at hdiv
    exact hdiv.symm
  have hW'₀ : W'.map (HolGerm.eval : HolGerm E →+* ℂ) = X ^ a := by
    rw [hW', Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      add_eq_left]
    exact Finset.sum_eq_zero fun k hk => by
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        HolGerm.eval_mk, hA0 k (Finset.mem_range.1 hk), map_zero, zero_mul]
  have hQ₁₀ : (W /ₘ W').map (HolGerm.eval : HolGerm E →+* ℂ) = V₀ := by
    refine mul_left_cancel₀ (pow_ne_zero a (X_ne_zero (R := ℂ))) ?_
    rw [← hfac, ← hW'₀, ← Polynomial.map_mul, ← hWQ]
  refine ⟨W', W /ₘ W', hW'm, fun j hj => ?_, hW'deg ▸ haN, hWQ, ?_⟩
  · rw [hW'deg] at hj
    rw [hW'coeff j hj, HolGerm.eval_mk]
    exact hA0 j hj
  · rwa [← coeff_map, hQ₁₀, coeff_zero_eq_eval_zero]

end Preparation

theorem exists_minpoly_isWeierstrass [Q.IsPrime] (hQ : IsNoetherNormalization Q d)
    (y : HolGerm (ComplexModel n)) (hy : HolGerm.eval y = 0) :
    ∃ W : (HolGerm (ComplexModel d))[X], IsWeierstrass W ∧ 0 < W.natDegree ∧
      evalGerm n W y ∈ Q ∧ ∀ F : (HolGerm (ComplexModel d))[X], evalGerm n F y ∈ Q → W ∣ F := by
  obtain ⟨W, hWm, hWpos, hWmem, hWdvd⟩ := exists_minpoly_dvd hQ y
  refine ⟨W, ?_, hWpos, hWmem, hWdvd⟩
  obtain ⟨W', Q₁, hW'm, hW'0, hdeg, hWQ, hQ₁⟩ := exists_eq_isWeierstrass_mul hWm
  have hunit : IsUnit (evalGerm n Q₁ y) := by
    rw [isUnit_iff_eval_ne_zero, evalGerm, hom_eval₂, hy, eval₂_at_zero, RingHom.comp_apply,
      eval_projGerm]
    exact hQ₁
  have hmem : evalGerm n W' y ∈ Q := by
    have h := hWmem
    rw [hWQ, evalGerm, eval₂_mul] at h
    exact (Ideal.mul_unit_mem_iff_mem Q hunit).1 h
  rw [← eq_of_monic_of_dvd_of_natDegree_le hWm hW'm (hWdvd W' hmem) hdeg]
  exact ⟨hW'm, hW'0⟩

theorem exists_eqn_of_not_mem [Q.IsPrime] (hQ : IsNoetherNormalization Q d)
    {f : HolGerm (ComplexModel n)} (hf : f ∉ Q) :
    ∃ h : HolGerm (ComplexModel d), h ≠ 0 ∧
      ∃ g : HolGerm (ComplexModel n), projGerm n d h - f * g ∈ Q := by
  obtain ⟨W, hWm, hWpos, hWmem, hWdvd⟩ := exists_minpoly_dvd hQ f
  have hsplit : evalGerm n W f = f * evalGerm n W.divX f + projGerm n d (W.coeff 0) := by
    have h := congrArg (fun P => evalGerm n P f) (X_mul_divX_add W)
    simp only [evalGerm, eval₂_add, eval₂_mul, eval₂_X, eval₂_C] at h
    exact h.symm
  refine ⟨W.coeff 0, fun h0 => ?_, -evalGerm n W.divX f, ?_⟩
  · rw [h0, map_zero, add_zero] at hsplit
    have hmem : evalGerm n W.divX f ∈ Q :=
      (Ideal.IsPrime.mem_or_mem inferInstance (hsplit ▸ hWmem)).resolve_left hf
    have hne : W.divX ≠ 0 := by
      intro h
      have := X_mul_divX_add W
      rw [h, h0, mul_zero, map_zero, add_zero] at this
      exact hWm.ne_zero this.symm
    have := natDegree_le_of_dvd (hWdvd _ hmem) hne
    rw [natDegree_divX_eq_natDegree_tsub_one] at this
    omega
  · rw [mul_neg, sub_neg_eq_add, add_comm, ← hsplit]
    exact hWmem

/-- `exists_reduce` with the support condition phrased via `MvPolynomial.supported`. -/
theorem exists_reduce_supported (hdn : d ≤ n) (p : Fin n → (HolGerm (ComplexModel d))[X])
    (hp : ∀ k : Fin n, d ≤ k.1 → IsWeierstrass (p k)) (g : HolGerm (ComplexModel n)) :
    ∃ (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) (q : Fin n → HolGerm (ComplexModel n)),
      R ∈ MvPolynomial.supported _ {i : Fin n | d ≤ i.1} ∧
      g = MvPolynomial.eval₂ (projGerm n d) coord R +
        ∑ k : Fin n, if d ≤ k.1 then q k * evalGerm n (p k) (coord k) else 0 := by
  induction n, hdn using Nat.le_induction with
  | base =>
    refine ⟨MvPolynomial.C g, 0, Subalgebra.algebraMap_mem _ g, ?_⟩
    rw [MvPolynomial.eval₂_C, projGerm_self, Finset.sum_eq_zero fun k _ => ite_eq_right (not_le.2
      k.2),
      add_zero]
  | succ n hdn ih =>
    obtain ⟨hWm, hW0⟩ := hp (Fin.last n) hdn
    obtain ⟨q₀, r, hg⟩ := exists_eq_mul_weierstrassGerm_add (s := (p (Fin.last n)).natDegree)
      (A := fun j => projGerm n d ((p (Fin.last n)).coeff j))
      (fun j hj => by rw [eval_projGerm]; exact hW0 j hj) g
    choose R q hR hq using fun j => ih (fun k => p k.castSucc) (fun k hk => hp k.castSucc hk) (r j)
    refine ⟨∑ j ∈ Finset.range (p (Fin.last n)).natDegree,
        MvPolynomial.rename Fin.castSucc (R j) * MvPolynomial.X (Fin.last n) ^ j,
      Fin.lastCases q₀ fun k => ∑ j ∈ Finset.range (p (Fin.last n)).natDegree,
        projGerm (n + 1) n (q j k) * coord (Fin.last n) ^ j,
      Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ ?_ _), ?_⟩
    · rw [MvPolynomial.mem_supported]
      intro i hi
      obtain ⟨i', hi', rfl⟩ := MvPolynomial.mem_vars_rename _ _ hi
      exact MvPolynomial.mem_supported.1 (hR j) hi'
    · exact MvPolynomial.X_mem_supported.2 hdn
    · have hr : ∀ j, projGerm (n + 1) n (r j) =
          MvPolynomial.eval₂ (projGerm (n + 1) d) coord (MvPolynomial.rename Fin.castSucc (R j)) +
            ∑ k ∈ Finset.univ.filter (fun k : Fin n => d ≤ k.1),
              projGerm (n + 1) n (q j k) * evalGerm (n + 1) (p k.castSucc) (coord k.castSucc) := by
        intro j
        rw [hq j, map_add, projGerm_eval₂_rename hdn, map_sum, Finset.sum_filter]
        refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
        split_ifs
        · rw [map_mul, projGerm_evalGerm hdn, projGerm_coordGerm k.2 n.le_succ]
          rfl
        · exact map_zero _
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_last, Fin.val_castSucc,
        ite_eq_left hdn]
      rw [← Finset.sum_filter, evalGerm_coord_last hdn hWm]
      conv_lhs => rw [hg]
      simp only [hr, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
        MvPolynomial.eval₂_X, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      have e : coord (Fin.last n) = coordGerm (n + 1) n n.lt_succ_self := rfl
      rw [e, Finset.sum_comm (s := Finset.range _) (t := Finset.univ.filter _)]
      have hsw : ∀ (x : Fin n) (i : ℕ),
          projGerm (n + 1) n (q i x) * evalGerm (n + 1) (p x.castSucc) (coord x.castSucc) *
            coordGerm (n + 1) n n.lt_succ_self ^ i =
          projGerm (n + 1) n (q i x) * coordGerm (n + 1) n n.lt_succ_self ^ i *
            evalGerm (n + 1) (p x.castSucc) (coord x.castSucc) := fun _ _ => mul_right_comm _ _ _
      simp only [hsw]
      ring

theorem exists_reduce (hdn : d ≤ n) (p : Fin n → (HolGerm (ComplexModel d))[X])
    (hp : ∀ k : Fin n, d ≤ k.1 → IsWeierstrass (p k)) (g : HolGerm (ComplexModel n)) :
    ∃ (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) (q : Fin n → HolGerm (ComplexModel n)),
      (∀ m ∈ R.support, ∀ i : Fin n, i.1 < d → m i = 0) ∧
      g = MvPolynomial.eval₂ (projGerm n d) coord R +
        ∑ k : Fin n, if d ≤ k.1 then q k * evalGerm n (p k) (coord k) else 0 := by
  obtain ⟨R, q, hR, hg⟩ := exists_reduce_supported hdn p hp g
  refine ⟨R, q, fun m hm i hi => ?_, hg⟩
  by_contra hmi
  have hi' : i ∈ R.vars :=
    (MvPolynomial.mem_vars_iff_mem_support i).2 ⟨m, hm, Finsupp.mem_support_iff.2 hmi⟩
  exact not_le.2 hi (MvPolynomial.mem_supported.1 hR hi')

end SGPT.Foundations.Analysis.Pending.GermMinimalPolynomial
