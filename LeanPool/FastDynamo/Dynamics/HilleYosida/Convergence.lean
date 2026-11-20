/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.HilleYosida.ApproximantSemigroup

/-!
# The limit semigroup of the Yosida approximants

This module performs the passage to the limit `r → ∞` in the approximant semigroups
`exp (t A_r)` of `ApproximantSemigroup.lean` and packages the result as a family of
bounded operators `hy.semigroupOperator hdense t` with the properties a strongly
continuous semigroup has to have: the semigroup laws, the growth bound `exp (M t)`,
strong continuity on `[0, ∞)`, and the commutation with the resolvents on the ray.

* **Existence of the limit.**  `cauchySeq_approx` is the heart: on the range of the
  embedding the Cauchy estimate `norm_approx_sub_approx_le` bounds
  `‖exp (t A_r) ι d - exp (t A_s) ι d‖` by `T exp (2 |M| T) ^ 2 ‖A_r ι d - A_s ι d‖`,
  which tends to `0` because `A_r ι d → A d` (`tendsto_yosida_embedding`); the uniform
  bound `norm_approx_le_uniform` and density of the domain then carry the Cauchy
  property to every `x : X` through the `ε/3` lemma
  `HilleYosida.cauchySeq_of_denseRange_of_norm_le`.  Completeness of `X` turns it into
  a limit, named by `HilleYosidaRay.limitFun` and identified by `tendsto_limitFun`.

* **The limit operator.**  `HilleYosidaRay.semigroupOperator` bundles
  `x ↦ limitFun t x` as a bounded operator: additivity and homogeneity by uniqueness of
  limits, and the bound `‖·‖ ≤ exp (M t)` of `norm_limitFun_le` from the sharp
  approximant bound `norm_approx_le` together with `M r / (r - M) → M`
  (`HilleYosida.tendsto_growthExponent`).  The definition clamps the time to
  `max t 0`, so the operator is total in `t` and equals the identity for `t ≤ 0`;
  `semigroupOperator_apply` is the only bridge needed for `0 ≤ t`.

* **The semigroup laws in the limit.**  `semigroupOperator_zero` and
  `semigroupOperator_add`.  The latter is the one place
  where a limit of *products* is taken: `exp (s A_r) (exp (t A_r) x)` is split as
  `exp (s A_r) (exp (t A_r) x - S t x) + exp (s A_r) (S t x)`, the first summand killed
  by the uniform bound and the second a strong limit at the *fixed* vector `S t x`.

* **Strong continuity.**  `tendstoUniformlyOn_approx` upgrades the convergence to
  uniform convergence on every compact time interval `[0, T]` — the Cauchy estimate is
  uniform in `t ∈ [0, T]`, and `norm_approx_sub_limitFun_le` is its limit form — so the
  limit orbit inherits the continuity of the approximant orbits
  (`continuousOn_limitFun`, `continuousOn_semigroupOperator_apply`).

* **Commutation with the resolvents.**  `semigroupOperator_stateResolvent` is the limit of
  `commute_approx_stateResolvent`; it is what makes the limit semigroup leave the
  domain invariant, and hence the input of the realization of the generator.

The time variable is real throughout, as in `ApproximantSemigroup.lean`, and the
parameter `r` ranges over `ℝ` rather than `ℕ`: `CauchySeq`,
`cauchySeq_tendsto_of_complete` and `TendstoUniformlyOn` all accept the real `atTop`
filter, and the arithmetic `M r / (r - M) → M` stays cast-free.

Namespaces follow the other modules of this directory: the generic material — two
statements that mention neither `DomainOperator` nor `HilleYosidaRay` — lives in
`FastDynamo.HilleYosida`, as in `OperatorExp.lean`; the definitions are
`HilleYosidaRay.limitFun` and `HilleYosidaRay.semigroupOperator`, so that `hy.limitFun`
and `hy.semigroupOperator` are dot notation; and every other theorem is a bare name in
`FastDynamo`, as in `YosidaApproximant.lean` and `ApproximantSemigroup.lean`.  The
Cauchy estimate the convergence rests on is `norm_approx_sub_approx_le` of
`ApproximantSemigroup.lean`, used at `x := A.embedding d`; this module does not restate
it.
-/

@[expose] public section

namespace FastDynamo

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D}

namespace HilleYosida

/--
The growth exponent of the approximant semigroups converges to the Hille–Yosida bound:
`M r / (r - M) → M` as `r → ∞`.

This is the arithmetic behind the passage from the sharp approximant bound
`‖exp (t A_r)‖ ≤ exp (t M r / (r - M))` of `norm_approx_le` to the bound
`‖S t‖ ≤ exp (M t)` of the limit semigroup.  The proof is the exact identity
`M r / (r - M) = M + M ^ 2 / (r - M)` for `r ≠ M` together with `r - M → ∞`.
-/
theorem tendsto_growthExponent (M : ℝ) :
    Filter.Tendsto (fun r : ℝ ↦ M * r / (r - M)) Filter.atTop (nhds M) := by
  have hsub : Filter.Tendsto (fun r : ℝ ↦ r - M) Filter.atTop Filter.atTop := by
    simpa [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right Filter.atTop (-M) Filter.tendsto_id
  have hadd : Filter.Tendsto (fun r : ℝ ↦ M + M ^ 2 / (r - M)) Filter.atTop (nhds (M + 0)) :=
    tendsto_const_nhds.add (hsub.const_div_atTop (M ^ 2))
  rw [add_zero] at hadd
  refine hadd.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop M] with r hr
  have hne : r - M ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
  field_simp
  ring

omit [CompleteSpace X] in
/--
Cauchy property on a dense set suffices: a family of operators that is uniformly bounded past
some parameter and Cauchy on a dense set is Cauchy at every point.

This is the `ε/3` argument: the difference `T m x - T n x` is split as
`T m (x - y) + (T m y - T n y) + T n (y - x)`, the two outer terms are at most `C ‖x - y‖`,
and the middle term is controlled by the Cauchy property of `r ↦ T r y`.  This is the form the
convergence of the approximants needs, because the limit operator does not exist yet when the
argument is made.  Completeness of `X` is not needed (only the *conclusion* is useless without it).
-/
theorem cauchySeq_of_denseRange_of_norm_le {T : ℝ → X →L[ℂ] X} {C : ℝ} {s : Set X}
    (hs : Dense s) (hC : ∀ᶠ r in Filter.atTop, ‖T r‖ ≤ C)
    (hconv : ∀ y ∈ s, CauchySeq fun r : ℝ ↦ T r y) (x : X) :
    CauchySeq fun r : ℝ ↦ T r x := by
  obtain ⟨r₀, hr₀⟩ := hC.exists
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (T r₀)) hr₀
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y, hys, hxy⟩ :=
    hs.exists_dist_lt x (show (0 : ℝ) < ε / (3 * (C + 1)) by positivity)
  rw [dist_eq_norm] at hxy
  have hkey : C * ‖x - y‖ < ε / 3 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * (C + 1))] at hxy
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [norm_nonneg (x - y)]
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hC
  obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.mp (hconv y hys) (ε / 3) (by linarith)
  refine ⟨max N₁ N₂, fun m hm n hn ↦ ?_⟩
  have hm₁ : N₁ ≤ m := le_trans (le_max_left _ _) hm
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hmid : ‖T m y - T n y‖ < ε / 3 := by
    have := hN₂ m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
    rwa [dist_eq_norm] at this
  have hsplit : T m x - T n x = T m (x - y) + (T m y - T n y) + T n (y - x) := by
    simp only [map_sub]
    abel
  have h1 : ‖T m (x - y)‖ ≤ C * ‖x - y‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right (hN₁ m hm₁) (norm_nonneg _))
  have h2 : ‖T n (y - x)‖ ≤ C * ‖x - y‖ := by
    rw [norm_sub_rev]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right (hN₁ n hn₁) (norm_nonneg _))
  rw [dist_eq_norm]
  calc ‖T m x - T n x‖ = ‖T m (x - y) + (T m y - T n y) + T n (y - x)‖ := by rw [hsplit]
    _ ≤ ‖T m (x - y)‖ + ‖T m y - T n y‖ + ‖T n (y - x)‖ := norm_add₃_le
    _ < ε := by linarith

end HilleYosida

/--
The approximant orbits of a *fixed* vector form a Cauchy family as `r → ∞`, at every
time `t ≥ 0`.

On the range of the embedding this is the Cauchy estimate `norm_approx_sub_approx_le`
applied at `T := t`, whose right-hand side `t exp (2 |M| t) ^ 2 ‖A_r ι d - A_s ι d‖`
tends to `0` because `A_r ι d → A d` (`tendsto_yosida_embedding`).  The uniform bound
`norm_approx_le_uniform` then extends the Cauchy property to every `x : X` by the `ε/3`
lemma `HilleYosida.cauchySeq_of_denseRange_of_norm_le`, which is where the density of
the domain is consumed.
-/
theorem cauchySeq_approx {M : ℝ} (hy : HilleYosidaRay A M) (hdense : DenseRange A.embedding)
    {t : ℝ} (ht : 0 ≤ t) (x : X) : CauchySeq fun r : ℝ ↦ hy.approx r t x := by
  refine HilleYosida.cauchySeq_of_denseRange_of_norm_le (C := Real.exp (2 * |M| * t))
    (s := Set.range (A.embedding : D → X)) hdense ?_ ?_ x
  · filter_upwards [Filter.eventually_ge_atTop (max (2 * |M|) 1 + 1)] with r hr
    exact norm_approx_le_uniform hy hr ht le_rfl
  · rintro _ ⟨d, rfl⟩
    have hK : (0 : ℝ) ≤ t * Real.exp (2 * |M| * t) ^ 2 := by positivity
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp
      (tendsto_yosida_embedding hy hdense d).cauchySeq
      (ε / (t * Real.exp (2 * |M| * t) ^ 2 + 1)) (by positivity)
    refine ⟨max (max (2 * |M|) 1 + 1) N, fun m hm n hn ↦ ?_⟩
    have hmt : max (2 * |M|) 1 + 1 ≤ m := le_trans (le_max_left _ _) hm
    have hnt : max (2 * |M|) 1 + 1 ≤ n := le_trans (le_max_left _ _) hn
    have hy₀ : ‖hy.yosida m (A.embedding d) - hy.yosida n (A.embedding d)‖
        < ε / (t * Real.exp (2 * |M| * t) ^ 2 + 1) := by
      have := hN m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
      rwa [dist_eq_norm] at this
    rw [lt_div_iff₀ (by positivity)] at hy₀
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (norm_approx_sub_approx_le hy ht le_rfl hmt hnt (A.embedding d)) ?_
    nlinarith [norm_nonneg (hy.yosida m (A.embedding d) - hy.yosida n (A.embedding d))]

/--
The limit of the approximant orbits, `S t x = lim_{r → ∞} exp (t A_r) x`, named by
`Filter.limUnder`.

The definition is total — `limUnder` of a family that does not converge is a junk value
— and is *identified* only by `tendsto_limitFun`, which needs `0 ≤ t` and the density of
the domain.  The bundled form is `HilleYosidaRay.semigroupOperator`; this unbundled one
exists because the uniform convergence and continuity statements are about the function
`t ↦ S t x` and are proved before the bundling.

Density is not an argument here: the definition does not use it.
-/
noncomputable def HilleYosidaRay.limitFun {M : ℝ} (hy : HilleYosidaRay A M) (t : ℝ) (x : X) :
    X :=
  Filter.limUnder Filter.atTop fun r : ℝ ↦ hy.approx r t x

/-- The defining property of `HilleYosidaRay.limitFun`: the approximant orbits converge
to it.  `cauchySeq_approx` plus completeness of `X` produce *a* limit, and
`Filter.Tendsto.limUnder_eq` identifies it with `limUnder`. -/
theorem tendsto_limitFun {M : ℝ} (hy : HilleYosidaRay A M) (hdense : DenseRange A.embedding)
    {t : ℝ} (ht : 0 ≤ t) (x : X) :
    Filter.Tendsto (fun r : ℝ ↦ hy.approx r t x) Filter.atTop (nhds (hy.limitFun t x)) := by
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_approx hy hdense ht x)
  rw [HilleYosidaRay.limitFun, ha.limUnder_eq]
  exact ha

/--
The limit inherits the Hille–Yosida bound in its sharp form:
`‖S t x‖ ≤ exp (M t) ‖x‖` for `t ≥ 0`.

The approximants obey `‖exp (t A_r) x‖ ≤ exp (t M r / (r - M)) ‖x‖` by `norm_approx_le`,
and both sides converge — the left to `‖S t x‖`, the right to `exp (M t) ‖x‖` by
`HilleYosida.tendsto_growthExponent` — so the inequality survives.  This is the bound
with which `HilleYosidaRay.semigroupOperator` is bundled.
-/
theorem norm_limitFun_le {M : ℝ} (hy : HilleYosidaRay A M) (hdense : DenseRange A.embedding)
    {t : ℝ} (ht : 0 ≤ t) (x : X) : ‖hy.limitFun t x‖ ≤ Real.exp (M * t) * ‖x‖ := by
  rw [mul_comm M t]
  have hlim : Filter.Tendsto (fun r : ℝ ↦ Real.exp (t * (M * r / (r - M))) * ‖x‖)
      Filter.atTop (nhds (Real.exp (t * M) * ‖x‖)) :=
    ((Real.continuous_exp.tendsto _).comp
      ((HilleYosida.tendsto_growthExponent M).const_mul t)).mul_const ‖x‖
  refine le_of_tendsto_of_tendsto (tendsto_limitFun hy hdense ht x).norm hlim ?_
  filter_upwards [Filter.eventually_gt_atTop (max M 0)] with r hr
  have hlt : M < r := lt_of_le_of_lt (le_max_left _ _) hr
  have h0 : 0 < r := lt_of_le_of_lt (le_max_right _ _) hr
  exact le_trans (ContinuousLinearMap.le_opNorm _ _)
    (mul_le_mul_of_nonneg_right (norm_approx_le hy hlt h0 ht) (norm_nonneg _))

/--
The limit semigroup as a family of bounded operators,
`S t = lim_{r → ∞} exp (t A_r)` in the strong topology.

Linearity is uniqueness of limits applied to the linearity of each approximant, and the
bound is `norm_limitFun_le`.  The time is clamped to `max t 0` so that the operator is
total in `t` (the semigroup interface indexes by `NNReal`, every
analytic step lives on `ℝ`); for `t ≤ 0` the clamped value is the identity, and for
`0 ≤ t` — the only case ever used —
`semigroupOperator_apply` identifies it with `HilleYosidaRay.limitFun`.
-/
noncomputable def HilleYosidaRay.semigroupOperator {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (t : ℝ) : X →L[ℂ] X :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ hy.limitFun (max t 0) x
      map_add' := fun x z ↦ tendsto_nhds_unique
        (tendsto_limitFun hy hdense (le_max_right t 0) (x + z))
        (by
          simpa using (tendsto_limitFun hy hdense (le_max_right t 0) x).add
            (tendsto_limitFun hy hdense (le_max_right t 0) z))
      map_smul' := fun c x ↦ by
        simp only [RingHom.id_apply]
        exact tendsto_nhds_unique (tendsto_limitFun hy hdense (le_max_right t 0) (c • x))
          (by
            simpa using (tendsto_limitFun hy hdense (le_max_right t 0) x).const_smul c) }
    (Real.exp (M * max t 0)) fun x ↦ norm_limitFun_le hy hdense (le_max_right t 0) x

/-- For nonnegative times the bundled limit operator is the pointwise limit: the clamp
`max t 0` of the definition is inactive. -/
theorem semigroupOperator_apply {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) {t : ℝ} (ht : 0 ≤ t) (x : X) :
    hy.semigroupOperator hdense t x = hy.limitFun t x := by
  rw [HilleYosidaRay.semigroupOperator, LinearMap.mkContinuous_apply]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [max_eq_left ht]

/-- The defining property of the limit semigroup: the approximant semigroups converge to
it strongly, at every nonnegative time. -/
theorem tendsto_semigroupOperator {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) {t : ℝ} (ht : 0 ≤ t) (x : X) :
    Filter.Tendsto (fun r : ℝ ↦ hy.approx r t x) Filter.atTop
      (nhds (hy.semigroupOperator hdense t x)) := by
  rw [semigroupOperator_apply hy hdense ht x]
  exact tendsto_limitFun hy hdense ht x

/--
The growth bound of the limit semigroup, `‖S t‖ ≤ exp (M t)` for `t ≥ 0`: the constant
of the Hille–Yosida hypothesis is exactly the exponential growth rate of the generated
semigroup.  This is `norm_limitFun_le` read as an operator bound.
-/
theorem norm_semigroupOperator_le {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) {t : ℝ} (ht : 0 ≤ t) :
    ‖hy.semigroupOperator hdense t‖ ≤ Real.exp (M * t) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x ↦ ?_
  rw [semigroupOperator_apply hy hdense ht x]
  exact norm_limitFun_le hy hdense ht x

/-- The limit semigroup starts at the identity: every approximant does
(`approx_zero`), so the constant family `x` is the one whose limit is taken. -/
theorem semigroupOperator_zero {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) :
    hy.semigroupOperator hdense 0 = ContinuousLinearMap.id ℂ X := by
  ext x
  refine tendsto_nhds_unique (tendsto_semigroupOperator hy hdense le_rfl x) ?_
  simp only [approx_zero, ContinuousLinearMap.id_apply]
  exact tendsto_const_nhds

/--
The semigroup law in the limit, `S (s + t) = S s ∘ S t` for `s, t ≥ 0`.

This is the only limit of *products* in the development, and the argument is the
following: the approximants satisfy `exp ((s+t) A_r) = exp (s A_r) exp (t A_r)`
(`approx_add`), and the right-hand side is split as
`exp (s A_r) (exp (t A_r) x - S t x) + exp (s A_r) (S t x)`.  The first summand is at
most `exp (2 |M| s) ‖exp (t A_r) x - S t x‖ → 0` by the uniform bound
`norm_approx_le_uniform`; the second is the strong limit of the approximants at the
*fixed* vector `S t x`, hence tends to `S s (S t x)`.
-/
theorem semigroupOperator_add {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    hy.semigroupOperator hdense (s + t)
      = (hy.semigroupOperator hdense s).comp (hy.semigroupOperator hdense t) := by
  ext x
  refine tendsto_nhds_unique
    (tendsto_semigroupOperator hy hdense (by linarith : (0 : ℝ) ≤ s + t) x) ?_
  have hsplit : ∀ r : ℝ, hy.approx r (s + t) x
      = hy.approx r s (hy.approx r t x - hy.semigroupOperator hdense t x)
        + hy.approx r s (hy.semigroupOperator hdense t x) := by
    intro r
    rw [approx_add hy]
    simp only [ContinuousLinearMap.comp_apply, ← map_add]
    congr 1
    abel
  have h1 : Filter.Tendsto
      (fun r : ℝ ↦ hy.approx r s (hy.approx r t x - hy.semigroupOperator hdense t x))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun r : ℝ ↦ Real.exp (2 * |M| * s)
      * ‖hy.approx r t x - hy.semigroupOperator hdense t x‖) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (max (2 * |M|) 1 + 1)] with r hr
      exact le_trans (ContinuousLinearMap.le_opNorm _ _)
        (mul_le_mul_of_nonneg_right (norm_approx_le_uniform hy hr hs le_rfl) (norm_nonneg _))
    · have hz := ((tendsto_semigroupOperator hy hdense ht x).sub_const
        (hy.semigroupOperator hdense t x)).norm
      simp only [sub_self, norm_zero] at hz
      simpa using hz.const_mul (Real.exp (2 * |M| * s))
  have h2 := tendsto_semigroupOperator hy hdense hs (hy.semigroupOperator hdense t x)
  simpa [hsplit] using h1.add h2

/--
The limit semigroup commutes with every resolvent on the ray,
`S t (R(s) x) = R(s) (S t x)`.

The approximants commute with `R(s)` (`commute_approx_stateResolvent`), and `R(s)` is a
bounded operator, so the identity passes to the strong limit.  Everything the
realization of the generator does — the invariance of the domain, the orbit of a domain
vector — rests on this one identity.
-/
theorem semigroupOperator_stateResolvent {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : M < s) (x : X) :
    hy.semigroupOperator hdense t (hy.resolvent.stateResolvent (s : ℂ) x)
      = hy.resolvent.stateResolvent (s : ℂ) (hy.semigroupOperator hdense t x) := by
  refine tendsto_nhds_unique
    (tendsto_semigroupOperator hy hdense ht (hy.resolvent.stateResolvent (s : ℂ) x)) ?_
  have hcont : Filter.Tendsto
      (fun r : ℝ ↦ hy.resolvent.stateResolvent (s : ℂ) (hy.approx r t x)) Filter.atTop
      (nhds (hy.resolvent.stateResolvent (s : ℂ) (hy.semigroupOperator hdense t x))) :=
    ((hy.resolvent.stateResolvent (s : ℂ)).continuous.tendsto _).comp
      (tendsto_semigroupOperator hy hdense ht x)
  refine hcont.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop M] with r hr
  have hcomm := DFunLike.congr_fun (commute_approx_stateResolvent hy hr hs t) x
  simp only [mul_apply_eq_comp] at hcomm
  exact hcomm.symm

/--
The limit form of the Cauchy estimate on the domain:
`‖exp (t A_r) ι d - S t ι d‖ ≤ T exp (2 |M| T) ^ 2 ‖A_r ι d - A d‖` for `0 ≤ t ≤ T`, with
`ι` the embedding of the domain.

Both sides of `norm_approx_sub_approx_le` converge as the second parameter `s` tends to
infinity — the left-hand side by `tendsto_limitFun`, the right-hand side by
`tendsto_yosida_embedding` — and the inequality survives.  The bound does not depend on
`t ∈ [0, T]`, which is exactly what makes the convergence uniform on compact time
intervals.
-/
theorem norm_approx_sub_limitFun_le {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) {r : ℝ}
    (hr : max (2 * |M|) 1 + 1 ≤ r) (d : D) :
    ‖hy.approx r t (A.embedding d) - hy.limitFun t (A.embedding d)‖
      ≤ T * Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r (A.embedding d) - A.op d‖ := by
  refine le_of_tendsto_of_tendsto
    ((tendsto_limitFun hy hdense ht (A.embedding d)).const_sub
      (hy.approx r t (A.embedding d))).norm
    ((((tendsto_yosida_embedding hy hdense d).const_sub
      (hy.yosida r (A.embedding d))).norm).const_mul
        (T * Real.exp (2 * |M| * T) ^ 2)) ?_
  filter_upwards [Filter.eventually_ge_atTop (max (2 * |M|) 1 + 1)] with s hs
  exact norm_approx_sub_approx_le hy ht htT hr hs (A.embedding d)

/--
Uniform convergence of the approximant orbits on every compact time interval:
`exp (· A_r) x → S · x` uniformly on `[0, T]`.

On the range of the embedding this is `norm_approx_sub_limitFun_le`, whose right-hand
side is independent of `t` and tends to `0`; the uniform bound `norm_approx_le_uniform`
and the operator bound `norm_semigroupOperator_le` carry it to every `x : X` by an
`ε/3` argument (the same split as `HilleYosida.cauchySeq_of_denseRange_of_norm_le`, but
performed by hand because the estimate must stay uniform in `t`).

This is the statement from which the strong continuity of the limit semigroup follows.

A hypothesis `0 ≤ T` is not needed and is therefore not taken: for `T < 0`
the interval `Set.Icc 0 T` is empty and the statement is vacuous, and inside the proof
`0 ≤ t ≤ T` already supplies it.
-/
theorem tendstoUniformlyOn_approx {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (T : ℝ) (x : X) :
    TendstoUniformlyOn (fun (r : ℝ) (t : ℝ) ↦ hy.approx r t x)
      (fun t ↦ hy.limitFun t x) Filter.atTop (Set.Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hCpos : (0 : ℝ) < Real.exp (2 * |M| * T) := Real.exp_pos _
  obtain ⟨d, hd⟩ : ∃ d : D, ‖A.embedding d - x‖ < ε / (3 * Real.exp (2 * |M| * T)) := by
    obtain ⟨d, hdd⟩ := Metric.denseRange_iff.mp hdense x
      (ε / (3 * Real.exp (2 * |M| * T))) (by positivity)
    exact ⟨d, by rwa [← dist_eq_norm, dist_comm]⟩
  have hmid : ∀ᶠ r : ℝ in Filter.atTop,
      T * Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r (A.embedding d) - A.op d‖ < ε / 3 := by
    have hz := ((tendsto_yosida_embedding hy hdense d).sub_const
      (A.op d)).norm.const_mul (T * Real.exp (2 * |M| * T) ^ 2)
    simp only [sub_self, norm_zero, mul_zero] at hz
    exact hz.eventually_lt_const (by linarith)
  filter_upwards [Filter.eventually_ge_atTop (max (2 * |M|) 1 + 1), hmid] with r hr hrmid
  rintro t ⟨ht0, htT⟩
  have hexp : Real.exp (M * t) ≤ Real.exp (2 * |M| * T) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : M * t ≤ |M| * t := mul_le_mul_of_nonneg_right (le_abs_self M) ht0
    have h2 : |M| * t ≤ |M| * T := mul_le_mul_of_nonneg_left htT (abs_nonneg M)
    nlinarith [abs_nonneg M, mul_nonneg (abs_nonneg M) (le_trans ht0 htT)]
  have houter : ‖hy.limitFun t x - hy.limitFun t (A.embedding d)‖
      ≤ Real.exp (2 * |M| * T) * ‖A.embedding d - x‖ := by
    have hlin : hy.limitFun t x - hy.limitFun t (A.embedding d)
        = hy.semigroupOperator hdense t (x - A.embedding d) := by
      rw [map_sub, semigroupOperator_apply hy hdense ht0, semigroupOperator_apply hy hdense ht0]
    rw [hlin, norm_sub_rev (A.embedding d) x]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right
        (le_trans (norm_semigroupOperator_le hy hdense ht0) hexp) (norm_nonneg _))
  have hinner : ‖hy.approx r t (A.embedding d) - hy.approx r t x‖
      ≤ Real.exp (2 * |M| * T) * ‖A.embedding d - x‖ := by
    rw [← map_sub]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right (norm_approx_le_uniform hy hr ht0 htT) (norm_nonneg _))
  have hthird : Real.exp (2 * |M| * T) * ‖A.embedding d - x‖ < ε / 3 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * Real.exp (2 * |M| * T))] at hd
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  have hsplit : hy.limitFun t x - hy.approx r t x
      = (hy.limitFun t x - hy.limitFun t (A.embedding d))
        + (hy.limitFun t (A.embedding d) - hy.approx r t (A.embedding d))
        + (hy.approx r t (A.embedding d) - hy.approx r t x) := by
    abel
  have hcentre : ‖hy.limitFun t (A.embedding d) - hy.approx r t (A.embedding d)‖
      ≤ T * Real.exp (2 * |M| * T) ^ 2 * ‖hy.yosida r (A.embedding d) - A.op d‖ := by
    rw [norm_sub_rev]
    exact norm_approx_sub_limitFun_le hy hdense ht0 htT hr d
  rw [dist_eq_norm, hsplit]
  calc ‖(hy.limitFun t x - hy.limitFun t (A.embedding d))
        + (hy.limitFun t (A.embedding d) - hy.approx r t (A.embedding d))
        + (hy.approx r t (A.embedding d) - hy.approx r t x)‖
      ≤ ‖hy.limitFun t x - hy.limitFun t (A.embedding d)‖
        + ‖hy.limitFun t (A.embedding d) - hy.approx r t (A.embedding d)‖
        + ‖hy.approx r t (A.embedding d) - hy.approx r t x‖ := norm_add₃_le
    _ < ε := by linarith

/--
Strong continuity of the limit semigroup: the orbit `t ↦ S t x` is continuous on
`[0, ∞)` for every `x`.

Each approximant orbit is continuous (`continuous_approx_apply`), and
`tendstoUniformlyOn_approx` makes the convergence uniform on `[0, T]`, so the limit is
continuous there by `TendstoUniformlyOn.continuousOn`.  A point `t₀ ≥ 0` is interior to
`[0, t₀ + 1]` relative to `[0, ∞)`, which upgrades the local statements to a single
`ContinuousOn … (Set.Ici 0)`.
-/
theorem continuousOn_limitFun {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (x : X) :
    ContinuousOn (fun t : ℝ ↦ hy.limitFun t x) (Set.Ici 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) ≤ t₀ := ht₀
  have hcont : ContinuousOn (fun t : ℝ ↦ hy.limitFun t x) (Set.Icc 0 (t₀ + 1)) :=
    (tendstoUniformlyOn_approx hy hdense (t₀ + 1) x).continuousOn
      (Filter.Eventually.frequently
        (Filter.Eventually.of_forall fun r ↦ (continuous_approx_apply hy r x).continuousOn))
  have hmem : Set.Icc (0 : ℝ) (t₀ + 1) ∈ nhdsWithin t₀ (Set.Ici (0 : ℝ)) := by
    rw [← Set.Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (hcont t₀ ⟨ht₀', by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- Strong continuity in the bundled form: `t ↦ S t x` is continuous on `[0, ∞)` for the
operator family `HilleYosidaRay.semigroupOperator`.  This is
`continuousOn_limitFun` transported by `semigroupOperator_apply`; it is the hypothesis
`strong_continuous'` of the semigroup interface. -/
theorem continuousOn_semigroupOperator_apply {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (x : X) :
    ContinuousOn (fun t : ℝ ↦ hy.semigroupOperator hdense t x) (Set.Ici 0) :=
  (continuousOn_limitFun hy hdense x).congr fun _ ht ↦ semigroupOperator_apply hy hdense ht x

end FastDynamo
