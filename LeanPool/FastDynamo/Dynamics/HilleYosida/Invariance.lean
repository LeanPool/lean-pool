/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.HilleYosida.Semigroup
public import LeanPool.FastDynamo.Dynamics.SemigroupRestriction

/-!
# Invariant closed subspaces of a Hille–Yosida semigroup

The generated semigroup of `FastDynamo/Dynamics/HilleYosida/Semigroup.lean` is not given
by a formula, so invariance of a subspace cannot be checked on it directly.  It is
obtained instead by pushing invariance along the Yosida approximation scheme, which is
where every explicit formula of the construction lives:

```
  resolvent  ⟶  Yosida approximant  ⟶  approximant semigroup  ⟶  semigroup
   R(r)          A_r = r² R(r) − r      exp (t A_r)              S t
```

Each arrow preserves membership in a subspace `W`, for a different elementary reason.

* `exp_mem_of_mem`: a *closed* submodule invariant under a bounded operator `B` is
  invariant under `NormedSpace.exp B`.  The exponential series converges in operator
  norm (`NormedSpace.expSeries_summable'`), hence pointwise after applying
  `ContinuousLinearMap.apply`; each partial sum lies in `W` because the powers of `B` do,
  and `IsClosed.mem_of_tendsto` passes to the limit.  This is the only step that uses
  closedness, and the only one that uses completeness of the ambient space.

* `HilleYosidaRay.yosida_mem`: the Yosida approximant is the combination
  `r² R(r) − r` of the state resolvent and the identity, so it preserves `W` as soon as
  the state resolvent does on the whole ray `M < r`.  The scalars of the definition are
  real and those of the submodule are complex, the bridge being `Complex.coe_smul`.

* `HilleYosidaRay.approx_mem`: the approximant semigroup `exp (t A_r)` preserves `W`, by
  the two previous items.

* `HilleYosidaRay.semigroup_mem_of_closed_resolvent_invariant`: the generated semigroup
  preserves `W`, because `tendsto_semigroup_apply` exhibits `S t x` as the limit of
  `exp (t A_r) x` as `r → ∞` and the approximants eventually lie on the ray.

The hypothesis is therefore exactly one thing — invariance of the state resolvent on the
real ray — and it is checked on an explicit operator.

`HilleYosidaRay.restrictedSemigroup` then packages
`FastDynamo.StronglyContinuousSemigroup.restrict` with that invariance, and carries the
two quantitative statements of `Semigroup.lean` across the restriction: the exponential
bound `‖S|_W t‖ ≤ exp (M t)` and the growth bound `(S|_W).growthBound ≤ M`.  Nothing here
claims the reverse inequality; a restricted semigroup can grow strictly more slowly.  This is
the interface `FastDynamo/Dynamics/Assembly/ProductSemigroup.lean` consumes for
`solenoidalInductionSemigroup`, whose two quantitative statements are exactly the two below at
the product ray.
-/

@[expose] public section

namespace FastDynamo

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D}

/--
A closed submodule invariant under a bounded operator `B` is invariant under the
exponential `NormedSpace.exp B`.

The exponential series `∑ (n !)⁻¹ • B ^ n` is summable in operator norm because `B` is
bounded and `X` is complete, so applying the evaluation map
`ContinuousLinearMap.apply ℂ X x` gives a `HasSum` in `X`.  Every partial sum lies in `W`
by `Submodule.sum_mem`, since `B ^ n` preserves `W` by induction, and `W` is closed, so
`IsClosed.mem_of_tendsto` transfers membership to the sum.
-/
theorem exp_mem_of_mem (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (B : X →L[ℂ] X) (hB : ∀ x ∈ W, B x ∈ W) (x : X) (hx : x ∈ W) :
    NormedSpace.exp B x ∈ W := by
  have hsum : Summable fun n : ℕ ↦ ((Nat.factorial n : ℂ)⁻¹ • B ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) B
  have hexp : NormedSpace.exp B = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ • B ^ n) := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have hHasSum : HasSum (fun n : ℕ ↦ ((Nat.factorial n : ℂ)⁻¹ • B ^ n) x)
      (NormedSpace.exp B x) := by
    have happly := (ContinuousLinearMap.apply ℂ X x).hasSum hsum.hasSum
    simpa only [hexp, ContinuousLinearMap.apply_apply] using happly
  have hpowmem : ∀ (n : ℕ) (y : X), y ∈ W → (B ^ n) y ∈ W := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ m ih =>
        intro y hy
        have hstep : ((B ^ (m + 1) : X →L[ℂ] X)) y = B ((B ^ m) y) := by
          rw [pow_succ']
          rfl
        rw [hstep]
        exact hB _ (ih y hy)
  exact hW.mem_of_tendsto hHasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall fun s ↦
      W.sum_mem fun n _ ↦ W.smul_mem _ (hpowmem n x hx))

omit [CompleteSpace X] in
/--
The Yosida approximant preserves a submodule on which the state resolvent of the ray is
invariant.

By definition `A_r = r² R(r) − r`, so the claim is `Submodule.sub_mem` applied to the two
summands.  The scalars `r ^ 2` and `r` are real while `W` is a complex submodule, so
`Complex.coe_smul` converts each real scalar action into the complex one before
`Submodule.smul_mem` applies.
-/
theorem HilleYosidaRay.yosida_mem {M : ℝ} (hy : HilleYosidaRay A M) (W : Submodule ℂ X)
    (hres : ∀ r : ℝ, M < r → ∀ x ∈ W, hy.resolvent.stateResolvent (r : ℂ) x ∈ W)
    {r : ℝ} (hr : M < r) (x : X) (hx : x ∈ W) :
    hy.yosida r x ∈ W := by
  rw [HilleYosidaRay.yosida]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, ← Complex.coe_smul]
  exact W.sub_mem (W.smul_mem _ (hres r hr x hx)) (W.smul_mem _ hx)

/--
The approximant semigroup `exp (t A_r)` preserves a closed submodule on which the state
resolvent of the ray is invariant, at every real time and every parameter on the ray.

This is `exp_mem_of_mem` applied to the bounded operator `t • A_r`, whose invariance of
`W` is `HilleYosidaRay.yosida_mem` followed by `Submodule.smul_mem` through
`Complex.coe_smul`.
-/
theorem HilleYosidaRay.approx_mem {M : ℝ} (hy : HilleYosidaRay A M) (W : Submodule ℂ X)
    (hW : IsClosed (W : Set X))
    (hres : ∀ r : ℝ, M < r → ∀ x ∈ W, hy.resolvent.stateResolvent (r : ℂ) x ∈ W)
    {r : ℝ} (hr : M < r) (t : ℝ) (x : X) (hx : x ∈ W) :
    hy.approx r t x ∈ W := by
  rw [HilleYosidaRay.approx]
  refine exp_mem_of_mem W hW _ (fun y hyW ↦ ?_) x hx
  rw [smul_apply, ← Complex.coe_smul]
  exact W.smul_mem _ (hy.yosida_mem W hres hr y hyW)

/--
The generated semigroup preserves a closed submodule on which the state resolvent of the
ray is invariant.

The orbit `S t x` is the limit of the approximant orbits `exp (t A_r) x` as `r → ∞`
(`tendsto_semigroup_apply`), the approximants eventually lie on the ray `M < r`, and each
of them keeps `x` inside `W` by `HilleYosidaRay.approx_mem`; `IsClosed.mem_of_tendsto`
concludes.  This is the invariance hypothesis consumed by
`HilleYosidaRay.restrictedSemigroup`.
-/
theorem HilleYosidaRay.semigroup_mem_of_closed_resolvent_invariant {M : ℝ}
    (hy : HilleYosidaRay A M) (hdense : DenseRange A.embedding) (W : Submodule ℂ X)
    (hW : IsClosed (W : Set X))
    (hres : ∀ r : ℝ, M < r → ∀ x ∈ W, hy.resolvent.stateResolvent (r : ℂ) x ∈ W)
    (t : NNReal) (x : X) (hx : x ∈ W) :
    (hy.semigroup hdense) t x ∈ W := by
  have htend := tendsto_semigroup_apply hy hdense t.coe_nonneg x
  rw [Real.toNNReal_coe] at htend
  refine hW.mem_of_tendsto htend ?_
  filter_upwards [Filter.eventually_gt_atTop M] with r hr
  exact hy.approx_mem W hW hres hr (t : ℝ) x hx

/--
The semigroup generated by a Hille–Yosida ray, restricted to a closed subspace on which
the state resolvent of the ray is invariant.

This is `FastDynamo.StronglyContinuousSemigroup.restrict` fed with
`HilleYosidaRay.semigroup_mem_of_closed_resolvent_invariant`.  It is the semigroup whose
growth bound is the growth rate of the evolution *on that subspace*, which is the
quantity a state space cut out by linear constraints carries.
-/
noncomputable def HilleYosidaRay.restrictedSemigroup {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (hres : ∀ r : ℝ, M < r → ∀ x ∈ W, hy.resolvent.stateResolvent (r : ℂ) x ∈ W) :
    StronglyContinuousSemigroup W :=
  (hy.semigroup hdense).restrict W
    (hy.semigroup_mem_of_closed_resolvent_invariant hdense W hW hres)

/-- The Hille–Yosida exponential bound survives the restriction:
`‖S|_W t‖ ≤ exp (M t)`.  This is `HilleYosidaRay.norm_semigroup_le` composed with
`FastDynamo.StronglyContinuousSemigroup.norm_restrict_le`. -/
theorem HilleYosidaRay.norm_restrictedSemigroup_le {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (hres : ∀ r : ℝ, M < r → ∀ x ∈ W, hy.resolvent.stateResolvent (r : ℂ) x ∈ W)
    (t : NNReal) :
    ‖(hy.restrictedSemigroup hdense W hW hres).operator t‖ ≤ Real.exp (M * (t : ℝ)) :=
  le_trans ((hy.semigroup hdense).norm_restrict_le W _ t) (hy.norm_semigroup_le hdense t)

/-- The Hille–Yosida constant bounds the growth bound of the restricted semigroup,
`(S|_W).growthBound ≤ M`.  Restriction can only decrease the growth bound
(`FastDynamo.StronglyContinuousSemigroup.growthBound_restrict_le`), and the ambient one is
bounded by `M` (`HilleYosidaRay.growthBound_le`). -/
theorem HilleYosidaRay.growthBound_restrictedSemigroup_le {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (W : Submodule ℂ X) (hW : IsClosed (W : Set X))
    (hres : ∀ r : ℝ, M < r → ∀ x ∈ W, hy.resolvent.stateResolvent (r : ℂ) x ∈ W) :
    (hy.restrictedSemigroup hdense W hW hres).growthBound ≤ (M : EReal) :=
  le_trans ((hy.semigroup hdense).growthBound_restrict_le W _) (hy.growthBound_le hdense)

end FastDynamo
