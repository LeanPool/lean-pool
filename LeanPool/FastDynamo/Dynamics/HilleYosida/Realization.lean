/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.HilleYosida.Semigroup

/-!
# The generated semigroup realizes the domain operator

This module supplies the second half of the Hille–Yosida theorem: the semigroup
`hy.semigroup hdense` built in `Semigroup.lean` is not merely a semigroup of bounded
operators, it *solves the Cauchy problem* for `A`.  The output is a
`DomainOperatorSemigroupRealization (hy.semigroup hdense) A`, the interface of
`FastDynamo/Dynamics/StronglyContinuousSemigroup.lean`: a domain-valued orbit
`domainOrbit d : ℝ → D` starting at `d`, embedding onto the semigroup orbit of
`A.embedding d`, and solving the forward equation in the strong sense.

## The domain orbit is algebra, not analysis

Fix the real shift `λ₀ := HilleYosida.shift M = max M 0 + 1`, which lies on the
Hille–Yosida ray.  The domain-valued resolvent `hy.resolvent.inv λ₀ : X →L[ℂ] D` inverts
the pencil `A.pencil λ₀ : D →L[ℂ] X` on both sides, so `D` and `X` are isomorphic through
it and the orbit can simply be *defined* by transport:

```
domainOrbit d t := hy.resolvent.inv λ₀ (S (Real.toNNReal t) (A.pencil λ₀ d))
```

No invariance-of-the-domain argument is needed.  Both identities

* `A.embedding (domainOrbit d t) = S t (A.embedding d)` (`embedding_domainOrbit`), and
* `A.op (domainOrbit d t) = S t (A.op d)` (`op_domainOrbit`)

follow from a single analytic input, the commutation `S t ∘ R(λ₀) = R(λ₀) ∘ S t`
(`semigroup_stateResolvent`, the bundled form of `semigroupOperator_stateResolvent`), plus
the two identities `op_comp_inv` and `HilleYosidaRay.inv_pencil` of `ResolventRay.lean`.
In particular the derivative that `IsForwardStrongSolution` demands is known in advance:
it must be `S t (A.op d)`.

## The one analytic obligation

What is left is the forward derivative at every `t ≥ 0`, the endpoint `t = 0` included,
where a two-sided derivative does not exist and the uniform-convergence transfer theorems
of Mathlib (which require an open set) do not apply.  The route is the classical one:

1. Each approximant satisfies the fundamental-theorem identity
   `exp (t A_r) x - x = ∫₀ᵗ exp (s A_r) (A_r x) ds` (`approx_sub_self_eq_integral`).
2. Passing `r → ∞` at `x = A.embedding d` gives
   `S t (A.embedding d) - A.embedding d = ∫₀ᵗ S s (A.op d) ds`
   (`semigroup_sub_eq_integral`).  The interchange of limit and integral is an explicit
   `ε`-estimate: on `[0, t]` the integrand differs from its limit by at most
   `‖exp (s A_r)‖ ‖A_r (A.embedding d) - A.op d‖` plus the uniform error of
   `tendstoUniformlyOn_approx` at the *fixed* vector `A.op d`, and both tend to `0`.
3. The integrand `s ↦ S (Real.toNNReal s) (A.op d)` is continuous on all of `ℝ`
   (`StronglyContinuousSemigroup.orbit_continuous` composed with `Real.toNNReal`), so the
   second fundamental theorem gives a two-sided `HasDerivAt` for the integral, and
   `HasDerivWithinAt.congr` transfers it to the orbit on `Set.Ici 0`
   (`hasDerivWithinAt_semigroup_embedding`).

Steps 2 and 3 are `semigroup_sub_eq_integral` and `hasDerivWithinAt_semigroup_embedding`;
together with `op_domainOrbit` they give `isForwardStrongSolution_domainOrbit` and hence
`HilleYosidaRay.realization`.

Namespaces follow the other modules of the directory: the generic shift and its one property are in
`FastDynamo.HilleYosida`, the two definitions are `HilleYosidaRay.domainOrbit` and
`HilleYosidaRay.realization` so that `hy.domainOrbit hdense` and `hy.realization hdense`
are dot notation, and the theorems are bare names in `FastDynamo`.
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
The spectral parameter used to transport the semigroup orbit from `X` back to the domain
`D`: the real number `max M 0 + 1`.  Any point of the Hille–Yosida ray would do; this
choice is explicit, positive, and strictly larger than the Hille–Yosida constant `M`.
-/
def shift (M : ℝ) : ℝ := max M 0 + 1

/-- The shift lies on the Hille–Yosida ray, so the resolvent is defined there and the
estimates of `ResolventRay.lean` apply to it. -/
theorem lt_shift (M : ℝ) : M < shift M := by
  have h : M ≤ max M 0 := le_max_left M 0
  simp only [shift]
  linarith

end HilleYosida

/--
The generated semigroup commutes with every resolvent on the ray, in the bundled form:
`S t (R(s) x) = R(s) (S t x)` for `t : ℝ≥0` and `M < s`.

This is `semigroupOperator_stateResolvent` of `Convergence.lean` read
through `HilleYosidaRay.semigroup_operator`; the nonnegativity of the time is automatic
for `t : ℝ≥0`.  It is the only analytic input of the algebraic transport below.
-/
theorem semigroup_stateResolvent {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (t : NNReal) {s : ℝ} (hs : M < s) (x : X) :
    (hy.semigroup hdense) t (hy.resolvent.stateResolvent (s : ℂ) x)
      = hy.resolvent.stateResolvent (s : ℂ) ((hy.semigroup hdense) t x) := by
  rw [hy.semigroup_operator hdense]
  exact semigroupOperator_stateResolvent hy hdense t.coe_nonneg hs x

/--
The domain-valued orbit of a domain datum `d`: transport the ambient semigroup orbit of
`A.pencil λ₀ d` back to `D` along the domain-valued resolvent at the shift
`λ₀ = HilleYosida.shift M`.

Because `hy.resolvent.inv λ₀` and `A.pencil λ₀` are mutually inverse, this is the unique
domain-valued curve whose embedding is the semigroup orbit of `A.embedding d`; see
`embedding_domainOrbit`.  The definition is total in `t`, the negative times being clamped
by `Real.toNNReal` exactly as the semigroup interface clamps them.
-/
noncomputable def HilleYosidaRay.domainOrbit {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (d : D) (t : ℝ) : D :=
  hy.resolvent.inv ((HilleYosida.shift M : ℝ) : ℂ)
    ((hy.semigroup hdense) (Real.toNNReal t) (A.pencil ((HilleYosida.shift M : ℝ) : ℂ) d))

omit [CompleteSpace X] in
/-- The ambient resolvent undoes the pencil at the shift: `R(λ₀) ∘ (λ₀ - A) = ι`.  This is
`HilleYosidaRay.inv_pencil` composed with the embedding. -/
theorem stateResolvent_pencil {M : ℝ} (hy : HilleYosidaRay A M) (d : D) :
    hy.resolvent.stateResolvent ((HilleYosida.shift M : ℝ) : ℂ)
        (A.pencil ((HilleYosida.shift M : ℝ) : ℂ) d) = A.embedding d := by
  rw [HasResolventOn.stateResolvent, ContinuousLinearMap.comp_apply,
    HilleYosidaRay.inv_pencil hy (HilleYosida.lt_shift M) d]

/-- The domain orbit starts at the prescribed datum: the semigroup is the identity at time
zero and the resolvent undoes the pencil. -/
theorem domainOrbit_zero {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (d : D) : hy.domainOrbit hdense d 0 = d := by
  rw [HilleYosidaRay.domainOrbit, Real.toNNReal_zero,
    StronglyContinuousSemigroup.apply_zero,
    HilleYosidaRay.inv_pencil hy (HilleYosida.lt_shift M) d]

/--
The embedded domain orbit is the ambient semigroup orbit,
`ι (domainOrbit d t) = S t (ι d)`.

The embedding turns `hy.resolvent.inv λ₀` into the ambient resolvent
`hy.resolvent.stateResolvent λ₀`, which commutes with `S t`
(`semigroup_stateResolvent`); `stateResolvent_pencil` then removes the pencil.
-/
theorem embedding_domainOrbit {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (d : D) (t : ℝ) :
    A.embedding (hy.domainOrbit hdense d t)
      = (hy.semigroup hdense) (Real.toNNReal t) (A.embedding d) := by
  rw [HilleYosidaRay.domainOrbit, ← ContinuousLinearMap.comp_apply,
    ← HasResolventOn.stateResolvent,
    ← semigroup_stateResolvent hy hdense _ (HilleYosida.lt_shift M),
    stateResolvent_pencil hy d]

/--
The operator applied to the domain orbit is the semigroup orbit of `A.op d`,
`A (domainOrbit d t) = S t (A d)`.

This is the identity `A ∘ R(λ₀) = λ₀ R(λ₀) - I` of `op_comp_inv` applied to
`S t (A.pencil λ₀ d)`, the same commutation as in `embedding_domainOrbit`, and the
elementary cancellation `λ₀ • ι d - (λ₀ • ι d - A d) = A d`.  It is what makes the
derivative of the orbit known in advance, with no invariance-of-the-domain argument.
-/
theorem op_domainOrbit {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (d : D) (t : ℝ) :
    A.op (hy.domainOrbit hdense d t)
      = (hy.semigroup hdense) (Real.toNNReal t) (A.op d) := by
  have hs : M < HilleYosida.shift M := HilleYosida.lt_shift M
  have hmem : ((HilleYosida.shift M : ℝ) : ℂ) ∈ hy.spectralSet := hy.mem_ofReal _ hs
  have hop : ∀ y : X, A.op (hy.resolvent.inv ((HilleYosida.shift M : ℝ) : ℂ) y)
      = ((HilleYosida.shift M : ℝ) : ℂ)
          • hy.resolvent.stateResolvent ((HilleYosida.shift M : ℝ) : ℂ) y - y := by
    intro y
    have h := congrArg (fun T : X →L[ℂ] X ↦ T y) (op_comp_inv hy.resolvent hmem)
    simpa using h
  rw [HilleYosidaRay.domainOrbit, hop, ← semigroup_stateResolvent hy hdense _ hs,
    stateResolvent_pencil hy d, ← map_smul, ← map_sub]
  congr 1
  rw [DomainOperator.pencil]
  simp only [sub_apply, smul_apply]
  abel

/--
The integral form of the Cauchy problem for the generated semigroup:
`S t (ι d) - ι d = ∫₀ᵗ S s (A d) ds` for every `t ≥ 0` and every domain datum `d`.

Each Yosida approximant satisfies the corresponding identity exactly
(`approx_sub_self_eq_integral`), and the passage to the limit `r → ∞` is performed
under the integral sign: on `[0, t]` the integrand
`exp (s A_r) (A_r (ι d))` differs from `S s (A d)` by at most
`‖exp (s A_r)‖ ‖A_r (ι d) - A d‖` — bounded uniformly in `s` by
`norm_approx_le_uniform` and `tendsto_yosida_embedding` — plus the uniform error of
`tendstoUniformlyOn_approx` at the fixed vector `A d`.  Both are eventually smaller than
`ε / (4 (t + 1))`, and `intervalIntegral.norm_integral_le_of_norm_le_const` turns the
pointwise bound into a bound on the integral.
-/
theorem semigroup_sub_eq_integral {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (d : D) {t : ℝ} (ht : 0 ≤ t) :
    (hy.semigroup hdense) (Real.toNNReal t) (A.embedding d) - A.embedding d
      = ∫ s in (0:ℝ)..t, (hy.semigroup hdense) (Real.toNNReal s) (A.op d) := by
  have hGcont : Continuous fun s : ℝ ↦ (hy.semigroup hdense) (Real.toNNReal s) (A.op d) :=
    ((hy.semigroup hdense).orbit_continuous (A.op d)).comp continuous_real_toNNReal
  have hSlim : ∀ s : ℝ, 0 ≤ s →
      (hy.semigroup hdense) (Real.toNNReal s) (A.op d) = hy.limitFun s (A.op d) := by
    intro s hs
    rw [hy.semigroup_apply hdense, Real.coe_toNNReal s hs]
  have hInt : Filter.Tendsto
      (fun r : ℝ ↦ ∫ s in (0:ℝ)..t, hy.approx r s (hy.yosida r (A.embedding d)))
      Filter.atTop
      (nhds (∫ s in (0:ℝ)..t, (hy.semigroup hdense) (Real.toNNReal s) (A.op d))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hCpos : (0:ℝ) < Real.exp (2 * |M| * t) := Real.exp_pos _
    have huc := (Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_approx hy hdense t (A.op d))) (ε / (4 * (t + 1))) (by positivity)
    have hyo : ∀ᶠ r : ℝ in Filter.atTop,
        ‖hy.yosida r (A.embedding d) - A.op d‖
          < ε / (4 * (t + 1) * Real.exp (2 * |M| * t)) := by
      have hz := ((tendsto_yosida_embedding hy hdense d).sub_const (A.op d)).norm
      simp only [sub_self, norm_zero] at hz
      exact hz.eventually_lt_const (by positivity)
    filter_upwards [Filter.eventually_ge_atTop (max (2 * |M|) 1 + 1), huc, hyo] with
      r hr huc' hyo'
    have hFint : IntervalIntegrable
        (fun s : ℝ ↦ hy.approx r s (hy.yosida r (A.embedding d))) MeasureTheory.volume 0 t :=
      (continuous_approx_apply hy r (hy.yosida r (A.embedding d))).intervalIntegrable 0 t
    have hGint : IntervalIntegrable
        (fun s : ℝ ↦ (hy.semigroup hdense) (Real.toNNReal s) (A.op d))
        MeasureTheory.volume 0 t := hGcont.intervalIntegrable 0 t
    rw [dist_eq_norm, ← intervalIntegral.integral_sub hFint hGint]
    refine lt_of_le_of_lt (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := ε / (2 * (t + 1))) ?_) ?_
    · intro s hsmem
      rw [Set.uIoc_of_le ht] at hsmem
      have hs0 : (0:ℝ) ≤ s := hsmem.1.le
      have hsT : s ≤ t := hsmem.2
      have hsplit : hy.approx r s (hy.yosida r (A.embedding d))
            - (hy.semigroup hdense) (Real.toNNReal s) (A.op d)
          = hy.approx r s (hy.yosida r (A.embedding d) - A.op d)
            + (hy.approx r s (A.op d) - hy.limitFun s (A.op d)) := by
        rw [map_sub, hSlim s hs0]
        abel
      have h1 : ‖hy.approx r s (hy.yosida r (A.embedding d) - A.op d)‖
          ≤ Real.exp (2 * |M| * t) * ‖hy.yosida r (A.embedding d) - A.op d‖ :=
        le_trans (ContinuousLinearMap.le_opNorm _ _)
          (mul_le_mul_of_nonneg_right (norm_approx_le_uniform hy hr hs0 hsT) (norm_nonneg _))
      have h2 : ‖hy.approx r s (A.op d) - hy.limitFun s (A.op d)‖ < ε / (4 * (t + 1)) := by
        have hd := huc' s ⟨hs0, hsT⟩
        rwa [dist_eq_norm, norm_sub_rev] at hd
      have h3 : Real.exp (2 * |M| * t) * ‖hy.yosida r (A.embedding d) - A.op d‖
          < ε / (4 * (t + 1)) := by
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4 * (t + 1) * Real.exp (2 * |M| * t))] at hyo'
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4 * (t + 1))]
        nlinarith [norm_nonneg (hy.yosida r (A.embedding d) - A.op d)]
      rw [hsplit]
      calc ‖hy.approx r s (hy.yosida r (A.embedding d) - A.op d)
              + (hy.approx r s (A.op d) - hy.limitFun s (A.op d))‖
          ≤ ‖hy.approx r s (hy.yosida r (A.embedding d) - A.op d)‖
            + ‖hy.approx r s (A.op d) - hy.limitFun s (A.op d)‖ := norm_add_le _ _
        _ ≤ ε / (2 * (t + 1)) := by
            have hne : t + 1 ≠ 0 := by positivity
            have heq : ε / (4 * (t + 1)) + ε / (4 * (t + 1)) = ε / (2 * (t + 1)) := by
              field_simp
              ring
            linarith [h1.trans_lt h3, h2]
    · rw [sub_zero, abs_of_nonneg ht, div_mul_eq_mul_div,
        div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (t + 1))]
      nlinarith
  exact tendsto_nhds_unique
    ((tendsto_semigroup_apply hy hdense ht (A.embedding d)).sub_const (A.embedding d))
    (hInt.congr fun r ↦ (approx_sub_self_eq_integral hy r t (A.embedding d)).symm)

/--
The forward derivative of the semigroup orbit of an embedded domain datum: at every
`t ≥ 0`, including the endpoint `t = 0`,

`HasDerivWithinAt (fun s ↦ S s (ι d)) (S t (A d)) (Set.Ici 0) t`.

The integrand `s ↦ S (Real.toNNReal s) (A d)` is continuous on all of `ℝ`, so the second
fundamental theorem of calculus differentiates `u ↦ ∫₀ᵘ S s (A d) ds` two-sidedly at every
real `u`; `semigroup_sub_eq_integral` identifies that primitive with the orbit on
`[0, ∞)`, and `HasDerivWithinAt.congr` transfers the derivative there.
-/
theorem hasDerivWithinAt_semigroup_embedding {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (d : D) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ ↦ (hy.semigroup hdense) (Real.toNNReal s) (A.embedding d))
      ((hy.semigroup hdense) (Real.toNNReal t) (A.op d)) (Set.Ici 0) t := by
  have hgc : Continuous fun s : ℝ ↦ (hy.semigroup hdense) (Real.toNNReal s) (A.op d) :=
    ((hy.semigroup hdense).orbit_continuous (A.op d)).comp continuous_real_toNNReal
  have hFTC : HasDerivAt
      (fun u : ℝ ↦ (∫ s in (0:ℝ)..u, (hy.semigroup hdense) (Real.toNNReal s) (A.op d))
        + A.embedding d)
      ((hy.semigroup hdense) (Real.toNNReal t) (A.op d)) t :=
    (intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 0 t)
      (hgc.stronglyMeasurableAtFilter MeasureTheory.volume (nhds t))
      hgc.continuousAt).add_const _
  exact hFTC.hasDerivWithinAt.congr
    (fun u hu ↦ eq_add_of_sub_eq (semigroup_sub_eq_integral hy hdense d hu))
    (eq_add_of_sub_eq (semigroup_sub_eq_integral hy hdense d ht))

/-- The domain orbit is a forward strong solution of `A`: its embedding is the semigroup
orbit (`embedding_domainOrbit`), whose forward derivative is
`hasDerivWithinAt_semigroup_embedding`, and that derivative is `A.op` of the orbit by
`op_domainOrbit`. -/
theorem isForwardStrongSolution_domainOrbit {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (d : D) :
    A.IsForwardStrongSolution (hy.domainOrbit hdense d) := by
  intro t ht
  simp only [embedding_domainOrbit hy hdense d, op_domainOrbit hy hdense d]
  exact hasDerivWithinAt_semigroup_embedding hy hdense d ht

/--
**The realization.**  The semigroup generated by a Hille–Yosida ray realizes the domain
operator: every domain datum `d` has a domain-valued forward strong solution starting at
`d` whose embedding is the semigroup orbit of `A.embedding d`.

The four fields are `domainOrbit_zero`, `isForwardStrongSolution_domainOrbit` and
`embedding_domainOrbit`; this is the object the growth-bound theory of
`FastDynamo/Dynamics/GrowthBound.lean` consumes.
-/
noncomputable def HilleYosidaRay.realization {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) :
    DomainOperatorSemigroupRealization (hy.semigroup hdense) A where
  domainOrbit := hy.domainOrbit hdense
  domainOrbit_zero d := domainOrbit_zero hy hdense d
  domainOrbit_isForwardStrongSolution d := isForwardStrongSolution_domainOrbit hy hdense d
  semigroup_eq_embedding_domainOrbit d t _ := (embedding_domainOrbit hy hdense d t).symm

end FastDynamo
