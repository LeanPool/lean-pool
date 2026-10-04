/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.Interior
public import LeanPool.EllipticPDE.Regularity.WeakLimit


/-!
# Membership of a cut-off directional derivative in `H₀¹(Ω)`

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 bootstraps interior
regularity by running the interior `H²` estimate on a derivative `∂_ℓ u` of the weak solution.
`EllipticPdes.Regularity.interior_H2_estimate` quantifies its solution over `H₀¹(Ω)`, and `∂_ℓ
u` has no boundary condition, so the derivative has to be cut off before it can be fed back in.
This file supplies the resulting admissibility statement: for the middle cutoff `ξ` of a cutoff
tower, the product `ξ · ∂_ℓ u` is again an element of `H₀¹(Ω)`.

The route is a weak limit of the discrete family `cutoffMul ξ (diffQuotG ℓ h u)`, every member
of which lies in `H₀¹(Ω)` by `cutoffMul_diffQuotG_mem_H01`. The family is bounded in the graph
norm uniformly in the step: the function coordinate and the second Leibniz summand of each
gradient coordinate are controlled by the first-order bound `‖Dₖ^h u‖ ≤ ‖∂ₖu‖`, and the first
Leibniz summand `ξ · Dₖ^h ∂ᵢu` is exactly what the master energy estimate
`interior_diffQuot_energy_bound` controls. Weak sequential compactness then produces a limit,
which stays in `H₀¹(Ω)` because a closed subspace equals its double orthogonal complement, and
the function coordinate of the limit is pinned by the weak `L²` convergence of the difference
quotients.

## Main declarations

* `restrictL2_diffQuot_extendL2`: the interior difference quotient as the restriction of the
  whole-space one.
* `inner_mulTest_comm`: multiplication by a cutoff is self-adjoint on `L²(Ω)`.
* `exists_mem_H01_mulTest_gradient`: the cutoff of a directional derivative lies in `H₀¹(Ω)`.
* `interior_cutoffGrad_mem_H01`: the same, together with the weak gradient it has.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Restricted and whole-space difference quotients -/

/-- **Interior difference quotient as a restriction of the whole-space one.** Both sides
evaluate to `((extendL2 g)(x + h eₖ) - g x) / h` almost everywhere on `Ω`, because extension by
zero agrees with the class there. No support hypothesis is needed: the identity is read on `Ω`
only (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
theorem restrictL2_diffQuot_extendL2 (k : Fin d) (h : ℝ) (hΩm : MeasurableSet Ω) (g : L2D Ω) :
    restrictL2 (diffQuot k h (extendL2 hΩm g)) = diffQuotD k h hΩm g := by
  apply Lp.ext
  filter_upwards [coeFn_restrictL2 (Ω := Ω) (diffQuot k h (extendL2 hΩm g)),
      ae_restrict_of_ae (coeFn_diffQuot k h (extendL2 hΩm g)),
      coeFn_diffQuotD k h hΩm g,
      ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hΩm]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, Set.indicator_of_mem h5]

/-- **Extension by zero is a left inverse of restriction on `Ω`.** Restricting the whole-space
extension of a class recovers the class. -/
theorem restrictL2_extendL2_eq (hΩm : MeasurableSet Ω) (g : L2D Ω) :
    restrictL2 (extendL2 hΩm g) = g := by
  apply Lp.ext
  filter_upwards [coeFn_restrictL2 (Ω := Ω) (extendL2 hΩm g),
      ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hΩm] with x h1 h2 h3
  rw [h1, h2, Set.indicator_of_mem h3]

/-- **First-order bound for the interior difference quotient.** For `u ∈ H₀¹(Ω)` the interior
difference quotient of the function coordinate is bounded by the corresponding gradient
coordinate, uniformly in the step: extension by zero preserves the weak derivative
(`hasWeakDeriv_extendL2_of_mem_H01`), the whole-space bound `‖Dₖ^h g‖ ≤ ‖g'‖` applies, and
restriction is non-expansive (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2). -/
theorem norm_diffQuotD_le_grad (hΩm : MeasurableSet Ω) (k : Fin d) (u : H01 Ω) (h : ℝ) :
    ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ≤ ‖(u : H1amb Ω) k.succ‖ := by
  rw [← restrictL2_diffQuot_extendL2]
  refine le_trans (norm_restrictL2_le _) ?_
  rw [← norm_extendL2 hΩm ((u : H1amb Ω) k.succ)]
  exact norm_diffQuot_le_of_hasWeakDeriv k _ _ (hasWeakDeriv_extendL2_of_mem_H01 hΩm k u.2) h

/-! ### Self-adjointness of the cutoff multipliers -/

/-- **Self-adjointness of the cutoff multiplier on `L²(Ω)`.** Both pairings are the integral of the
triple product `∫_Ω η · g · w`. -/
theorem inner_mulTest_comm {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η)
    (g w : L2D Ω) : ⟪mulTest hη g, w⟫ = ⟪g, mulTest hη w⟫ := by
  have key : ∀ p q : L2D Ω, ⟪mulTest hη p, q⟫ = ∫ x in Ω, η x * (p x : ℝ) * (q x : ℝ) :=
    fun p q => inner_mulCoeffL_eq _ _ p q
  rw [key g w, real_inner_comm, key w g]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-! ### One-neighbourhood shift margin -/

/-- **One-neighbourhood shift margin.** If the cutoff `η` is `≡ 1` on a neighbourhood of a
compact set `K`, then there is a positive margin `δ` such that `η` is locally constant `≡ 1`
near every point within `δ` of `K`. This restates, for use outside
`EllipticPdes.Regularity.Interior.NormBound`, the localisation fact that shifting a support
point of one tower cutoff by less than the margin lands where the next cutoff is identically
`1` (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
theorem exists_eventually_one_margin {η : EuclideanSpace ℝ (Fin d) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (hη : ∀ᶠ x in nhdsSet K, η x = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      (∃ p ∈ K, dist x p < δ) → η =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
  obtain ⟨U, hUopen, hKU, hUsub⟩ := mem_nhdsSet_iff_exists.mp hη
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hUopen hKU
  refine ⟨δ, hδpos, fun x hx => ?_⟩
  have hxU : x ∈ U :=
    hδ (Metric.thickening_subset_cthickening δ K (Metric.mem_thickening_iff.mpr hx))
  exact Filter.eventually_of_mem (hUopen.mem_nhds hxU) (fun y hy => hUsub hy)

/-! ### Uniform graph-norm bound on the discrete family -/

/-- **Uniform graph-norm bound.** For a weak solution `u` and a cutoff tower `T`, the discrete
family `ξ · Dₗ^h u` is bounded in the ambient graph norm uniformly over all steps below a
positive margin. The function coordinate and the second Leibniz summand of each gradient
coordinate are handled by the first-order bound `‖Dₗ^h u‖ ≤ ‖∂ₗu‖`; the first Leibniz summand
`ξ · Dₗ^h ∂ᵢu` is the quantity the master energy estimate
`interior_diffQuot_energy_bound` controls, once the four step-smallness conditions of that
estimate are read off the tower margins (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1). -/
private lemma exists_cutoffMul_diffQuotG_norm_bound (Op : FullEllipticOp d)
    (hΩm : MeasurableSet Ω) (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (ℓ : Fin d) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ h : ℝ, |h| < δ →
      ‖cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))‖ ≤ M := by
  classical
  have hlam : (0 : ℝ) < Op.lam := Op.toEllipticCoeff.lam_pos
  have htξ2ξ : tsupport (fun y => T.ξ y * T.ξ y) ⊆ tsupport T.ξ := tsupport_mul_subset_left
  have htξθ : tsupport T.ξ ⊆ tsupport T.θ := fun x hx =>
    subset_tsupport T.θ (by rw [Function.mem_support, T.theta_eqOn_one hx]; exact one_ne_zero)
  obtain ⟨δθ, hδθ, hθ1m⟩ := exists_eventually_one_margin T.hξ.2.1 T.hθ_one
  obtain ⟨CE, hCE0, hCE⟩ := interior_diffQuot_energy_bound Op hΩm hA T.hξ T.hθ ℓ
  set Mξ : ℝ := (exists_abs_bound T.hξ).choose with hMξdef
  have hMξ0 : (0 : ℝ) ≤ Mξ := le_trans (abs_nonneg _) ((exists_abs_bound T.hξ).choose_spec 0)
  set c : Fin d → ℝ := fun i => (exists_abs_bound_partialD T.hξ i).choose with hcdef
  have hc0 : ∀ i, (0 : ℝ) ≤ c i := fun i =>
    le_trans (abs_nonneg _) ((exists_abs_bound_partialD T.hξ i).choose_spec 0)
  set Q : ℝ := ‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2 with hQdef
  have hQ0 : (0 : ℝ) ≤ Q := by rw [hQdef]; positivity
  set Dl : ℝ := ‖(u : H1amb Ω) ℓ.succ‖ with hDldef
  set Btot : ℝ := (Mξ * Dl) ^ 2 + (2 * (2 * CE * Q / Op.lam)
      + 2 * ∑ i : Fin d, (c i * Dl) ^ 2) with hBdef
  refine ⟨min T.margin δθ, lt_min T.hmargin_pos hδθ, Real.sqrt Btot, ?_⟩
  intro h hsmall
  rcases eq_or_ne h 0 with rfl | hh
  · have hzero : diffQuotG ℓ (0 : ℝ) hΩm (u : H1amb Ω) = 0 := by
      refine PiLp.ext fun j => ?_
      rw [diffQuotG_apply]
      simp [diffQuotD]
    rw [hzero, map_zero, norm_zero]
    exact Real.sqrt_nonneg _
  have hm : |h| < T.margin := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hmθ : |h| < δθ := lt_of_lt_of_le hsmall (min_le_right _ _)
  -- The four step-smallness conditions of the master energy estimate.
  have hdistshift : ∀ x : EuclideanSpace ℝ (Fin d), dist x (x + hshift ℓ (-h)) = |h| := by
    intro x
    rw [dist_eq_norm, show x - (x + hshift ℓ (-h)) = hshift ℓ h from by
      rw [hshift_neg]; abel]
    simp [hshift, norm_smul]
  have hev_case : ∀ x, x ∈ tsupport (fun y => T.ξ y * T.ξ y)
        ∨ x + hshift ℓ (-h) ∈ tsupport (fun y => T.ξ y * T.ξ y) →
      T.θ =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
    rintro x (h1 | h2)
    · exact hθ1m x ⟨x, htξ2ξ h1, by rw [dist_self]; exact hδθ⟩
    · exact hθ1m x ⟨x + hshift ℓ (-h), htξ2ξ h2, by rw [hdistshift]; exact hmθ⟩
  have hsm_in : ∀ x ∈ tsupport (fun y => T.ξ y * T.ξ y), x + hshift ℓ h ∈ Ω :=
    fun x hx => T.hmargin ℓ h hm x (htξθ (htξ2ξ hx))
  have hsm_out : ∀ x ∈ tsupport T.θ, x + hshift ℓ (-h) ∈ Ω :=
    fun x hx => T.hmargin ℓ (-h) (by rw [abs_neg]; exact hm) x hx
  have hθ1 : ∀ x ∈ Ω, x ∈ tsupport (fun y => T.ξ y * T.ξ y)
        ∨ x + hshift ℓ (-h) ∈ tsupport (fun y => T.ξ y * T.ξ y) → T.θ x = 1 := by
    intro x _ hcase
    simpa using (hev_case x hcase).eq_of_nhds
  have hθ0 : ∀ (j : Fin d), ∀ x ∈ Ω, x ∈ tsupport (fun y => T.ξ y * T.ξ y)
        ∨ x + hshift ℓ (-h) ∈ tsupport (fun y => T.ξ y * T.ξ y) → partialD j T.θ x = 0 := by
    intro j x _ hcase
    rw [partialD, (hev_case x hcase).fderiv_eq]
    simp
  have hmaster := hCE u f hu h hh hsm_in hsm_out hθ1 hθ0
  -- The master estimate, with the extension bridge removed.
  have hE : ∑ i : Fin d, ‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))‖ ^ 2
      ≤ 2 * CE * Q / Op.lam := by
    have hext : ∀ i : Fin d,
        ‖extendL2 hΩm (mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ)))‖
          = ‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))‖ :=
      fun i => norm_extendL2 hΩm _
    simp_rw [hext] at hmaster
    rw [le_div_iff₀ hlam]
    linarith only [hmaster]
  -- The coordinates of the discrete family.
  have hW0 : (cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))) 0
      = mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) 0)) := by
    rw [cutoffMul_apply_zero, diffQuotG_apply]
  have hWs : ∀ i : Fin d, (cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))) i.succ
      = mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))
        + mulTestPartial T.hξ i (diffQuotD ℓ h hΩm ((u : H1amb Ω) 0)) := by
    intro i
    rw [cutoffMul_apply_succ, diffQuotG_apply, diffQuotG_apply]
  have hD0 : ‖diffQuotD ℓ h hΩm ((u : H1amb Ω) 0)‖ ≤ Dl := norm_diffQuotD_le_grad hΩm ℓ u h
  have hnorm0 : ‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) 0))‖ ≤ Mξ * Dl :=
    le_trans (norm_mulTest_le T.hξ _) (mul_le_mul_of_nonneg_left hD0 hMξ0)
  have hnormS : ∀ i : Fin d,
      ‖mulTestPartial T.hξ i (diffQuotD ℓ h hΩm ((u : H1amb Ω) 0))‖ ≤ c i * Dl :=
    fun i => le_trans (norm_mulTestPartial_le T.hξ i _)
      (mul_le_mul_of_nonneg_left hD0 (hc0 i))
  -- The per-coordinate square bound, split by the Leibniz rule.
  have hstep : ∀ i : Fin d,
      ‖(cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))) i.succ‖ ^ 2
        ≤ 2 * ‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))‖ ^ 2
          + 2 * (c i * Dl) ^ 2 := by
    intro i
    have htri : ‖(cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))) i.succ‖
        ≤ ‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))‖
          + ‖mulTestPartial T.hξ i (diffQuotD ℓ h hΩm ((u : H1amb Ω) 0))‖ := by
      rw [hWs i]; exact norm_add_le _ _
    have hXn := norm_nonneg ((cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))) i.succ)
    have han := norm_nonneg (mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ)))
    have hbn := norm_nonneg (mulTestPartial T.hξ i (diffQuotD ℓ h hΩm ((u : H1amb Ω) 0)))
    nlinarith [htri, hXn, han, hbn, hnormS i, mul_nonneg (hc0 i) (norm_nonneg
        ((u : H1amb Ω) ℓ.succ)),
      sq_nonneg (‖mulTest T.hξ (diffQuotD ℓ h hΩm ((u : H1amb Ω) i.succ))‖
        - ‖mulTestPartial T.hξ i (diffQuotD ℓ h hΩm ((u : H1amb Ω) 0))‖)]
  -- Sum the coordinates and take the square root.
  have hsum : ∑ i : Fin d, ‖(cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))) i.succ‖ ^ 2
      ≤ 2 * (2 * CE * Q / Op.lam) + 2 * ∑ i : Fin d, (c i * Dl) ^ 2 := by
    refine le_trans (Finset.sum_le_sum (fun i _ => hstep i)) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num)) (le_refl _)
  have hsq : ‖cutoffMul T.hξ (diffQuotG ℓ h hΩm (u : H1amb Ω))‖ ^ 2 ≤ Btot := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, hBdef]
    refine add_le_add ?_ hsum
    rw [hW0]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm0 2
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at this

/-! ### Membership of a cut-off directional derivative in `H₀¹(Ω)` -/

/-- **Cutoff of a directional derivative is admissible (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2, step 3).** For a weak solution `u ∈ H₀¹(Ω)` of
`L u = f` with `W^{1,∞}` principal coefficients and a cutoff tower `T` for `V ⋐ Ω`, the product
`ξ · ∂_ℓ u` of the middle tower cutoff with a directional derivative of `u` is again an element
of `H₀¹(Ω)`: there is `W ∈ H₀¹(Ω)` whose function coordinate is `ξ · ∂_ℓ u`. Since `H₀¹(Ω)`
sits inside the weak-gradient graph space, the gradient coordinates of `W` are then the weak
derivatives of `ξ · ∂_ℓ u`, which `hasWeakDeriv_extendL2_of_mem_H01` reads off.

This is the admissibility step the `H^k` bootstrap needs and that Evans does not: his interior
`H²` theorem asks only `u ∈ H¹(U)`, so he differentiates the equation without cutting off,
whereas `EllipticPdes.Regularity.interior_H2_estimate` quantifies its solution over `H₀¹(Ω)` and
`∂_ℓ u` has no boundary condition.

The proof takes a weak limit of the admissible discrete family `ξ · Dₗ^h u`, whose members lie
in `H₀¹(Ω)` by `cutoffMul_diffQuotG_mem_H01` and which is bounded in the graph norm by
`exists_cutoffMul_diffQuotG_norm_bound`. The limit stays in `H₀¹(Ω)` because a closed subspace
of a Hilbert space equals its double orthogonal complement, and its function coordinate is
pinned by the weak `L²` convergence `Dₗ^h u ⇀ ∂_ℓ u`. -/
theorem exists_mem_H01_mulTest_gradient (Op : FullEllipticOp d)
    (hΩm : MeasurableSet Ω) (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (ℓ : Fin d) :
    ∃ W : H1amb Ω, W ∈ H01 Ω ∧ W 0 = mulTest T.hξ ((u : H1amb Ω) ℓ.succ) := by
  classical
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have htξθ : tsupport T.ξ ⊆ tsupport T.θ := fun x hx =>
    subset_tsupport T.θ (by rw [Function.mem_support, T.theta_eqOn_one hx]; exact one_ne_zero)
  obtain ⟨δ, hδpos, M, hM⟩ := exists_cutoffMul_diffQuotG_norm_bound Op hΩm hA T u f hu ℓ
  set δ₀ : ℝ := min δ T.margin with hδ₀def
  have hδ₀pos : (0 : ℝ) < δ₀ := lt_min hδpos T.hmargin_pos
  -- A step sequence shrinking to zero inside the margin.
  set hs : ℕ → ℝ := fun m => δ₀ / ((m : ℝ) + 2) with hsdef
  have hs_pos : ∀ m, 0 < hs m := by
    intro m; simp only [hsdef]; positivity
  have hs_ne : ∀ m, hs m ≠ 0 := fun m => ne_of_gt (hs_pos m)
  have hs_small : ∀ m, |hs m| < δ₀ := by
    intro m
    rw [abs_of_pos (hs_pos m)]
    simp only [hsdef]
    refine div_lt_self hδ₀pos ?_
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hs_lim : Filter.Tendsto hs Filter.atTop (nhds 0) := by
    simp only [hsdef]
    exact tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop)
  -- The admissible discrete family and its uniform bound.
  set Wn : ℕ → H1amb Ω := fun m => cutoffMul T.hξ (diffQuotG ℓ (hs m) hΩm (u : H1amb Ω))
    with hWndef
  have hWn_mem : ∀ m, Wn m ∈ H01 Ω := by
    intro m
    refine cutoffMul_diffQuotG_mem_H01 T.hξ ℓ hΩm ?_ u.2
    intro x hx
    exact T.hmargin ℓ (hs m) (lt_of_lt_of_le (hs_small m) (min_le_right _ _)) x (htξθ hx)
  have hWn_bd : ∀ m, ‖Wn m‖ ≤ M := fun m =>
    hM (hs m) (lt_of_lt_of_le (hs_small m) (min_le_left _ _))
  obtain ⟨W, σ, hσ, _hWnorm, hWweak⟩ := exists_weak_limit_of_bounded_hilbert hWn_bd
  refine ⟨W, ?_, ?_⟩
  · -- The weak limit of a sequence in a closed subspace stays in it.
    have hperp : W ∈ ((H01 Ω)ᗮ)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      have hz : ∀ m : ℕ, ⟪Wn (σ m), y⟫ = (0 : ℝ) := fun m =>
        (Submodule.mem_orthogonal (H01 Ω) y).mp hy _ (hWn_mem (σ m))
      have hlim : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds ⟪W, y⟫) :=
        (hWweak y).congr hz
      rw [real_inner_comm]
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    rwa [Submodule.orthogonal_orthogonal] at hperp
  · -- The function coordinate of the limit is `ξ · ∂_ℓ u`.
    refine ext_inner_left ℝ ?_
    intro z
    have hrw : ∀ X : H1amb Ω, ⟪X, PiLp.single 2 (0 : Fin (d + 1)) z⟫ = ⟪z, X 0⟫ := by
      intro X
      rw [real_inner_comm, inner_single_left]
    have hA1 : Filter.Tendsto (fun m => ⟪z, (Wn (σ m)) 0⟫) Filter.atTop (nhds ⟪z, W 0⟫) := by
      have hbase := hWweak (PiLp.single 2 (0 : Fin (d + 1)) z)
      simpa only [hrw] using hbase
    have hstep : ∀ m : ℕ, ⟪z, (Wn m) 0⟫
        = ⟪diffQuot ℓ (hs m) (extendL2 hΩm ((u : H1amb Ω) 0)),
            extendL2 hΩm (mulTest T.hξ z)⟫ := by
      intro m
      have h0 : (Wn m) 0 = mulTest T.hξ (diffQuotD ℓ (hs m) hΩm ((u : H1amb Ω) 0)) := by
        simp only [hWndef]
        rw [cutoffMul_apply_zero, diffQuotG_apply]
      rw [h0, ← inner_mulTest_comm T.hξ z _, ← restrictL2_diffQuot_extendL2,
        ← extendL2_inner_restrictL2]
      exact real_inner_comm _ _
    have hη0 : ∀ m, hs (σ m) ≠ 0 := fun m => hs_ne (σ m)
    have hηlim : Filter.Tendsto (fun m => hs (σ m)) Filter.atTop (nhds 0) :=
      hs_lim.comp hσ.tendsto_atTop
    have hA2 : Filter.Tendsto (fun m => ⟪z, (Wn (σ m)) 0⟫) Filter.atTop
        (nhds ⟪extendL2 hΩm ((u : H1amb Ω) ℓ.succ), extendL2 hΩm (mulTest T.hξ z)⟫) := by
      have hbase := tendsto_inner_diffQuot_of_hasWeakDeriv ℓ
        (hasWeakDeriv_extendL2_of_mem_H01 hΩm ℓ u.2) hη0 hηlim
        (extendL2 hΩm (mulTest T.hξ z))
      exact hbase.congr (fun m => (hstep (σ m)).symm)
    have hval : ⟪extendL2 hΩm ((u : H1amb Ω) ℓ.succ), extendL2 hΩm (mulTest T.hξ z)⟫
        = ⟪z, mulTest T.hξ ((u : H1amb Ω) ℓ.succ)⟫ := by
      rw [extendL2_inner_restrictL2, restrictL2_extendL2_eq,
        ← inner_mulTest_comm T.hξ z ((u : H1amb Ω) ℓ.succ)]
      exact real_inner_comm _ _
    rw [hval] at hA2
    exact tendsto_nhds_unique hA1 hA2

/-- **Cutoff derivative is an `H₀¹` function with its weak gradient (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1, Theorem 2, step 3).** For a weak solution
`u ∈ H₀¹(Ω)` of `L u = f` with `W^{1,∞}` principal coefficients and a cutoff tower `T` for
`V ⋐ Ω`, the product `ξ · ∂_ℓ u` of the middle tower cutoff with a directional derivative of
`u` is an element `W` of `H₀¹(Ω)`, and each gradient coordinate `W_{k+1}` of that element is
the weak `k`-derivative of `ξ · ∂_ℓ u` on the whole space.

This is the admissibility step that lets `EllipticPdes.Regularity.interior_H2_estimate`, whose
solution is quantified over `H₀¹(Ω)`, be applied to a derivative of `u`, which has no boundary
condition of its own. Because `ξ ≡ 1` on `tsupport ζ`, and `ζ ≡ 1` on `V`, the function
coordinate agrees with `∂_ℓ u` on a neighbourhood of `V`, so nothing is lost on the region of
interest. -/
theorem interior_cutoffGrad_mem_H01 (Op : FullEllipticOp d)
    (hΩm : MeasurableSet Ω) (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (ℓ : Fin d) :
    ∃ W : H1amb Ω, W ∈ H01 Ω ∧ W 0 = mulTest T.hξ ((u : H1amb Ω) ℓ.succ)
      ∧ ∀ k : Fin d, HasWeakDeriv k
          (extendL2 hΩm (mulTest T.hξ ((u : H1amb Ω) ℓ.succ))) (extendL2 hΩm (W k.succ)) := by
  obtain ⟨W, hWmem, hW0⟩ := exists_mem_H01_mulTest_gradient Op hΩm hA T u f hu ℓ
  refine ⟨W, hWmem, hW0, fun k => ?_⟩
  rw [← hW0]
  exact hasWeakDeriv_extendL2_of_mem_H01 hΩm k hWmem

/-! ### Triviality of the cutoff on the base set -/

/-- **Middle tower cutoff as `1` on the base set.** `ζ ≡ 1` on `V`, so `V` sits
inside `tsupport ζ`, where `ξ ≡ 1`. -/
theorem CutoffTower.xi_eqOn_one_base {V : Set (EuclideanSpace ℝ (Fin d))}
    (T : CutoffTower Ω V) : Set.EqOn T.ξ 1 V := by
  intro x hx
  refine T.xi_eqOn_one (subset_tsupport T.ζ ?_)
  rw [Function.mem_support, T.zeta_eqOn_one hx]
  exact one_ne_zero

/-- **Invisibility of the cutoff on the base set.** Because `ξ ≡ 1` on `V`, the `V`-restriction of
the whole-space extension of `ξ · g` agrees with that of `g`. Applied to the function coordinate
of `interior_cutoffGrad_mem_H01`, this says that the admissible element has `∂_ℓ u` itself on
`V`, so nothing is lost on the region of interest.

Kept as the statement that reads `interior_cutoffGrad_mem_H01`, which is pinned in `AxiomAudit`.
Nothing else consumes it. -/
theorem restrictL2_extendL2_mulTest_xi (hΩm : MeasurableSet Ω)
    {V : Set (EuclideanSpace ℝ (Fin d))} (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω)
    (T : CutoffTower Ω V) (g : L2D Ω) :
    restrictL2 (Ω := V) (extendL2 hΩm (mulTest T.hξ g))
      = restrictL2 (Ω := V) (extendL2 hΩm g) := by
  have hAB : (extendL2 hΩm (mulTest T.hξ g) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict V] (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) := by
    have hmt : (mulTest T.hξ g : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict V] fun x => T.ξ x * (g x : ℝ) :=
      (mulTest_coeFn T.hξ g).filter_mono (ae_mono (Measure.restrict_mono hVΩ le_rfl))
    filter_upwards [ae_restrict_of_ae (coeFn_extendL2 hΩm (mulTest T.hξ g)),
      ae_restrict_of_ae (coeFn_extendL2 hΩm g), hmt, ae_restrict_mem hVm] with x he1 he2 hmtx hxV
    rw [he1, he2, Set.indicator_of_mem (hVΩ hxV), Set.indicator_of_mem (hVΩ hxV), hmtx]
    simp [T.xi_eqOn_one_base hxV]
  apply Lp.ext
  filter_upwards [coeFn_restrictL2 (Ω := V) (extendL2 hΩm (mulTest T.hξ g)),
    coeFn_restrictL2 (Ω := V) (extendL2 hΩm g), hAB] with x h1 h2 h3
  rw [h1, h2, h3]

end EllipticPdes.Regularity
