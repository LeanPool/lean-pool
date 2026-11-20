/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.HilleYosida.ResolventRay

/-!
# The Yosida approximants of a Hille–Yosida generator

The Yosida approximant of a generator `A` at a real parameter `r` to the right of the
Hille–Yosida bound `M` is the bounded operator

`A_r = r ^ 2 R(r) - r`

on the ambient space, where `R(r)` is the state resolvent of the ray hypothesis
`HilleYosidaRay A M` of `FastDynamo/Dynamics/HilleYosida/ResolventRay.lean`.  It is the
bounded operator through which the abstract Hille–Yosida theorem replaces the unbounded
generator: `A_r = A (r R(r))` regularises `A`, and `r R(r) → 1` strongly, so `A_r`
converges to `A` on the domain.

This module records the elementary — purely algebraic — properties of `A_r`; the
exponentials `exp (t A_r)` are built on top of it in the companion module
`ApproximantSemigroup.lean`.

* `HilleYosidaRay.yosida` is the definition, with **real** scalars: the time variable of
  the semigroup is real, so the exponential of `t • A_r` has to be differentiated over
  `ℝ` even though the operators are complex-linear.  The bridge to the complex-scalar
  identities of `ResolventRay.lean` is `Complex.coe_smul` and it is confined to
  `yosida_embedding`.
* `yosida_embedding` is the regularisation identity `A_r ι d = r R(r) (A d)` on the
  domain, and `tendsto_yosida_embedding` turns it, through
  `HilleYosidaRay.tendsto_smul_stateResolvent`, into the convergence `A_r ι d → A d` as
  `r → ∞`.
* `commute_yosida` and `commute_yosida_stateResolvent` record that all the operators in
  play commute — the approximants with each other and with every resolvent on the ray.
  Both descend from `HasResolventOn.commute_stateResolvent`.
* No `‖A_r‖` bound is recorded: the crude estimate `‖A_r‖ ≤ r ^ 2 / (r - M) + r` blows up
  like `r`, and the bound that matters for the semigroup,
  `‖exp (t A_r)‖ ≤ exp (t M r / (r - M))`, comes from the *split* `A_r = r ^ 2 R(r) - r`
  instead.

`HilleYosidaRay.lt_of_le_threshold` is the threshold arithmetic shared by every uniform
estimate of the development: past `r ≥ max (2 |M|) 1 + 1` one has `M < r` and
`r / (r - M) ≤ 2`, so `‖r R(r)‖ ≤ 2` and the approximant semigroups are bounded by
`exp (2 |M| T)` on `[0, T]` uniformly in `r`.
-/

@[expose] public section

namespace FastDynamo

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D}

/--
The threshold arithmetic of the uniform estimates: for `r` at least
`max (2 |M|) 1 + 1` the parameter lies on the resolvent ray, `M < r`, and the
Hille–Yosida bound is uniform, `r / (r - M) ≤ 2`.

Both conclusions are needed wherever an estimate has to hold uniformly in `r`: the
first to apply the ray hypothesis at all, the second to bound `‖r R(r)‖` and hence the
approximant semigroups by a constant independent of `r`.
-/
theorem HilleYosidaRay.lt_of_le_threshold {M r : ℝ} (hr : max (2 * |M|) 1 + 1 ≤ r) :
    M < r ∧ r / (r - M) ≤ 2 := by
  have habs : 2 * |M| ≤ max (2 * |M|) 1 := le_max_left _ _
  have hone : (1 : ℝ) ≤ max (2 * |M|) 1 := le_max_right _ _
  have hMabs : M ≤ |M| := le_abs_self M
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have hlt : M < r := by linarith
  refine ⟨hlt, ?_⟩
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < r - M)]
  linarith

/--
The Yosida approximant `A_r = r ^ 2 R(r) - r` of the generator at the real parameter
`r`, a bounded operator on the ambient space.

The scalars are real: the exponential `exp (t • A_r)` is
differentiated in the real time variable `t`, which forces the whole scheme to live in
the real module structure of `X →L[ℂ] X`, while the operators themselves stay
complex-linear.  The definition is total in `r`; every statement about it assumes
`M < r`.
-/
noncomputable def HilleYosidaRay.yosida {M : ℝ} (hy : HilleYosidaRay A M) (r : ℝ) :
    X →L[ℂ] X :=
  (r ^ 2 : ℝ) • hy.resolvent.stateResolvent (r : ℂ) - (r : ℝ) • ContinuousLinearMap.id ℂ X

/--
The regularisation identity on the domain: `A_r ι d = r R(r) (A d)`.

It is the reason the approximants approximate: `A_r` is `A` preceded by the smoothing
operator `r R(r)`, and `r R(r) → 1` strongly.  The proof is the right inverse equation
`A R(r) = r R(r) - 1` of `op_comp_inv` combined with the commutation
`A R(r) ι = R(r) A` of `op_inv_embedding`; the bridge from the complex scalar `(r : ℂ)`
of those identities to the real scalar of `yosida` is `Complex.coe_smul`.
-/
theorem yosida_embedding {M : ℝ} (hy : HilleYosidaRay A M) {r : ℝ} (hr : M < r) (d : D) :
    hy.yosida r (A.embedding d) = (r : ℝ) • hy.resolvent.stateResolvent (r : ℂ) (A.op d) := by
  have hmem := hy.mem_ofReal r hr
  have hright := DFunLike.congr_fun (op_comp_inv hy.resolvent hmem) (A.embedding d)
  simp only [ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply] at hright
  have hkey : hy.resolvent.stateResolvent (r : ℂ) (A.op d)
      = (r : ℝ) • hy.resolvent.stateResolvent (r : ℂ) (A.embedding d) - A.embedding d := by
    rw [← op_inv_embedding hy.resolvent hmem d, hright, Complex.coe_smul]
  rw [hkey, HilleYosidaRay.yosida]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, smul_sub, smul_smul]
  rw [← pow_two]

/--
Convergence of the approximants to the generator on the domain:
`A_r ι d → A d` as `r → ∞`.

Past `M` the approximant is `r R(r) (A d)` by `yosida_embedding`, and `r R(r)` converges
strongly to the identity by `HilleYosidaRay.tendsto_smul_stateResolvent`, which is where
the density of the domain enters.
-/
theorem tendsto_yosida_embedding {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (d : D) :
    Filter.Tendsto (fun r : ℝ ↦ hy.yosida r (A.embedding d)) Filter.atTop
      (nhds (A.op d)) := by
  refine (hy.tendsto_smul_stateResolvent hdense (A.op d)).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop M] with r hr
  exact (yosida_embedding hy hr d).symm

/--
Two Yosida approximants of the same generator commute.  Both are polynomials in the
resolvents `R(r)`, `R(s)`, which commute by `HasResolventOn.commute_stateResolvent`, and
the identity commutes with everything.  This is what makes the difference of two
approximant semigroups telescope.
-/
theorem commute_yosida {M : ℝ} (hy : HilleYosidaRay A M) {r s : ℝ} (hr : M < r) (hs : M < s) :
    Commute (hy.yosida r) (hy.yosida s) := by
  have hR := hy.resolvent.commute_stateResolvent (hy.mem_ofReal r hr) (hy.mem_ofReal s hs)
  simp only [HilleYosidaRay.yosida, ← ContinuousLinearMap.one_def]
  exact (((hR.smul_left _).smul_right _).sub_right
      ((Commute.one_right _).smul_right _)).sub_left
    (((Commute.one_left _).smul_left _).sub_right
      (((Commute.refl (1 : X →L[ℂ] X)).smul_left _).smul_right _))

/--
A Yosida approximant commutes with every resolvent on the ray.  This is the commutation
that survives the strong limit `r → ∞` and gives the commutation of the limit semigroup
with the resolvent.
-/
theorem commute_yosida_stateResolvent {M : ℝ} (hy : HilleYosidaRay A M) {r s : ℝ}
    (hr : M < r) (hs : M < s) :
    Commute (hy.yosida r) (hy.resolvent.stateResolvent (s : ℂ)) := by
  have hR := hy.resolvent.commute_stateResolvent (hy.mem_ofReal r hr) (hy.mem_ofReal s hs)
  simp only [HilleYosidaRay.yosida, ← ContinuousLinearMap.one_def]
  exact (hR.smul_left _).sub_left ((Commute.one_left _).smul_left _)

end FastDynamo
