/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.EnergyPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionLinearity
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.VecGauge

/-!
# SeriesEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The energy estimate on a cube, and the Dirichlet problem for a perturbed coefficient field

The `C^{0,1/2}` contraction of the Section 5.1 iteration says nothing about the
`H¹` size of its iterates, and a Hölder bound alone cannot identify a limit as a
weak solution.  What identifies it is the energy estimate

```text
  lam ‖∇u‖_{L²(y+□_n)} ≤ d ‖g‖_{L²(y+□_n)}
```

for `-∇·a∇u = ∇·g` with zero boundary values: the antisymmetric part of `a`
drops out when the equation is tested with the solution itself, so only the
lower ellipticity constant survives.  The dimensional factor `d` is the price of
the supremum-norm carrier, paid once in `abs_setIntegral_vecDot_le`.

This module collects that estimate together with the algebra a perturbed
coefficient field needs.  If `b = a + kap` pointwise and both fields are
elliptic on the cube, then a solution for `a` at forcing `G` is a solution for
`b` at forcing `G - kap ∇u`; the perturbation `kap` is automatically bounded
entrywise by the sum of the two upper ellipticity constants, and its action on
an `L²` field is again `L²` because it is the difference of the actions of `b`
and of `a`.  No separate regularity or boundedness hypothesis on `kap` is
required.

## Main results

* `sqrt_energy_grad_le_of_isDirichletSolutionAt` — the energy estimate.
* `sqrt_setIntegral_sq_le_of_sup_bound` — the `L²` size of a field from its
  supremum size on the cube.
* `sqrt_setIntegral_sq_matVecMul_le` — the `L²` size of the action of an
  entrywise bounded matrix field.
* `isDirichletSolutionAt_add` — additivity of the localized Dirichlet problem.
* `isDirichletSolutionAt_coeff_add` — the same solution read against the
  perturbed coefficient field.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. Elementary `L²` bookkeeping -/

/-- The square of the norm of an `L²` field is integrable. -/
theorem integrableOn_sq_norm_of_memVectorL2 {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) : IntegrableOn (fun x => ‖F x‖ ^ (2 : ℕ)) U := by
  have hn : MemLp (fun x => ‖F x‖) 2 (volume.restrict U) := hF.norm
  have hmul := hn.integrable_mul hn
  simpa [Pi.mul_apply, pow_two] using! hmul

/-- The energy integral of a field is nonnegative. -/
theorem setIntegral_sq_norm_nonneg (U : Set (Vec d)) (F : Vec d → Vec d) :
    (0 : ℝ) ≤ ∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume :=
  integral_nonneg fun _ => by positivity

/-- **The `L²` size of a field from its supremum size** on a set of finite
volume. -/
theorem sqrt_setIntegral_sq_le_of_sup_bound {U : Set (Vec d)} (hU : MeasurableSet U)
    (hUfin : volume U ≠ ⊤) {F : Vec d → Vec d} (hF : MemVectorL2 U F) {S : ℝ}
    (hS : 0 ≤ S) (hbd : ∀ x ∈ U, ‖F x‖ ≤ S) :
    Real.sqrt (∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume) ≤
      Real.sqrt ((volume U).toReal) * S := by
  have hint := integrableOn_sq_norm_of_memVectorL2 hF
  have hconst : IntegrableOn (fun _ : Vec d => S ^ (2 : ℕ)) U :=
    integrableOn_const hUfin
  have hle : ∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume ≤ ∫ _x in U, S ^ (2 : ℕ) ∂volume := by
    refine integral_mono_ae hint hconst ((ae_restrict_iff' hU).2 ?_)
    exact Filter.Eventually.of_forall fun x hx =>
      pow_le_pow_left₀ (norm_nonneg _) (hbd x hx) 2
  have hconstval : ∫ _x in U, S ^ (2 : ℕ) ∂volume = (volume U).toReal * S ^ (2 : ℕ) := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def]
  rw [hconstval] at hle
  have hvol : (0 : ℝ) ≤ (volume U).toReal := ENNReal.toReal_nonneg
  calc Real.sqrt (∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume)
      ≤ Real.sqrt ((volume U).toReal * S ^ (2 : ℕ)) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt ((volume U).toReal) * S := by
        rw [Real.sqrt_mul hvol, Real.sqrt_sq hS]

/-! ## 2. Matrix algebra on the ambient carrier -/

/-- The action of a matrix field is additive in the matrix. -/
theorem matVecMul_matAdd (A B : Mat d) (xi : Vec d) :
    matVecMul (A + B) xi = matVecMul A xi + matVecMul B xi := by
  funext i
  simp only [matVecMul, Pi.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- The action of a matrix field is subtractive in the matrix. -/
theorem matVecMul_matSub (A B : Mat d) (xi : Vec d) :
    matVecMul (A - B) xi = matVecMul A xi - matVecMul B xi := by
  funext i
  simp only [matVecMul, Pi.sub_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **The `L²` size of the action of an entrywise bounded matrix field.** -/
theorem sqrt_setIntegral_sq_matVecMul_le {U : Set (Vec d)} (hU : MeasurableSet U)
    {k : Vec d → Mat d} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hk : ∀ x ∈ U, ∀ i j, |k x i j| ≤ delta) {F : Vec d → Vec d} (hF : MemVectorL2 U F)
    (hkF : MemVectorL2 U fun x => matVecMul (k x) (F x)) :
    Real.sqrt (∫ x in U, ‖matVecMul (k x) (F x)‖ ^ (2 : ℕ) ∂volume) ≤
      (d : ℝ) * delta * Real.sqrt (∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume) := by
  have hc : (0 : ℝ) ≤ (d : ℝ) * delta := by positivity
  have h1 : ∫ x in U, ‖matVecMul (k x) (F x)‖ ^ (2 : ℕ) ∂volume ≤
      ((d : ℝ) * delta) ^ (2 : ℕ) * ∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume := by
    rw [← integral_const_mul]
    refine integral_mono_ae (integrableOn_sq_norm_of_memVectorL2 hkF)
      ((integrableOn_sq_norm_of_memVectorL2 hF).const_mul _)
      ((ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx => ?_))
    have hp := norm_matVecMul_le_of_entry_bound hdelta (hk x hx) (F x)
    calc ‖matVecMul (k x) (F x)‖ ^ (2 : ℕ)
        ≤ ((d : ℝ) * delta * ‖F x‖) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (norm_nonneg _) hp 2
      _ = ((d : ℝ) * delta) ^ (2 : ℕ) * ‖F x‖ ^ (2 : ℕ) := by rw [mul_pow]
  calc Real.sqrt (∫ x in U, ‖matVecMul (k x) (F x)‖ ^ (2 : ℕ) ∂volume)
      ≤ Real.sqrt (((d : ℝ) * delta) ^ (2 : ℕ) *
          ∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume) := Real.sqrt_le_sqrt h1
    _ = (d : ℝ) * delta * Real.sqrt (∫ x in U, ‖F x‖ ^ (2 : ℕ) ∂volume) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

/-! ## 3. The energy estimate -/

/-- **The energy estimate for the localized Dirichlet problem.**  Testing
`-∇·a∇u = ∇·g` with the solution itself and using only the lower ellipticity
constant gives

```text
  lam ‖∇u‖_{L²(y+□_n)} ≤ d ‖g‖_{L²(y+□_n)} .
```

The antisymmetric part of `a` contributes nothing: the hypothesis used is the
one-sided bound `lam |ξ|² ≤ ξ·aξ`, which a skew addition to `a` leaves
untouched. -/
theorem sqrt_energy_grad_le_of_isDirichletSolutionAt {y : Vec d} {n : ℤ} {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    {g : Vec d → Vec d} (hg : MemVectorL2 (cubeSetAt y n) g)
    {u : H1Function (cubeSetAt y n)} (hu : IsDirichletSolutionAt a y n u g) :
    lam * Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume) ≤
      (d : ℝ) * Real.sqrt (∫ x in cubeSetAt y n, ‖g x‖ ^ (2 : ℕ) ∂volume) := by
  have hUmeas : MeasurableSet (cubeSetAt y n) := measurableSet_cubeSetAt y n
  have hlam : 0 < lam := (hEll.2 y (mem_cubeSetAt_self y n)).1
  obtain ⟨w, _hwf, hwg⟩ := hu.1
  have hgradEq : ∀ x, w.toH1Function.grad x = u.grad x := fun x => (hwg x).symm
  have hAu : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hEq := hu.2 w
  simp only [hgradEq] at hEq
  have hEnergyInt : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (u.grad x)) (u.grad x)) (cubeSetAt y n) :=
    integrableOn_vecDot_of_memVectorL2 hAu u.grad_memVectorL2
  have hSqInt : IntegrableOn (fun x => lam * vecNormSq (u.grad x)) (cubeSetAt y n) :=
    (integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 u.grad_memVectorL2).const_mul lam
  have hlower : ∫ x in cubeSetAt y n, lam * vecNormSq (u.grad x) ∂volume ≤
      ∫ x in cubeSetAt y n, vecDot (matVecMul (a x) (u.grad x)) (u.grad x) ∂volume := by
    refine integral_mono_ae hSqInt hEnergyInt ((ae_restrict_iff' hUmeas).2 ?_)
    refine Filter.Eventually.of_forall fun x hx => ?_
    change lam * vecNormSq (u.grad x) ≤ vecDot (matVecMul (a x) (u.grad x)) (u.grad x)
    rw [vecDot_comm]
    exact (hEll.2 x hx).2.2.1 (u.grad x)
  have hNormInt : IntegrableOn (fun x => ‖u.grad x‖ ^ (2 : ℕ)) (cubeSetAt y n) :=
    integrableOn_sq_norm_of_memVectorL2 u.grad_memVectorL2
  have hEucInt : IntegrableOn (fun x => vecNormSq (u.grad x)) (cubeSetAt y n) :=
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 u.grad_memVectorL2
  have hcompare : ∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume ≤
      ∫ x in cubeSetAt y n, vecNormSq (u.grad x) ∂volume :=
    integral_mono hNormInt hEucInt fun x => sq_norm_le_vecNormSq _
  have hupper := abs_setIntegral_vecDot_le (cubeSetAt y n) hg u.grad_memVectorL2
  have hA0 : (0 : ℝ) ≤ ∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume :=
    setIntegral_sq_norm_nonneg _ _
  have hchain : lam * (Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume) *
        Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume)) ≤
      (d : ℝ) * (Real.sqrt (∫ x in cubeSetAt y n, ‖g x‖ ^ (2 : ℕ) ∂volume) *
        Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume)) := by
    rw [← pow_two, Real.sq_sqrt hA0]
    calc lam * ∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume
        ≤ ∫ x in cubeSetAt y n, lam * vecNormSq (u.grad x) ∂volume := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left hcompare hlam.le
      _ ≤ ∫ x in cubeSetAt y n, vecDot (matVecMul (a x) (u.grad x)) (u.grad x) ∂volume :=
          hlower
      _ = -∫ x in cubeSetAt y n, vecDot (g x) (u.grad x) ∂volume := hEq
      _ ≤ |∫ x in cubeSetAt y n, vecDot (g x) (u.grad x) ∂volume| := neg_le_abs _
      _ ≤ (d : ℝ) * (Real.sqrt (∫ x in cubeSetAt y n, ‖g x‖ ^ (2 : ℕ) ∂volume) *
            Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume)) := hupper
  rcases eq_or_lt_of_le (Real.sqrt_nonneg
      (∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume)) with hzero | hpos
  · rw [← hzero, mul_zero]
    positivity
  · have hmul : lam * Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume) *
        Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume) ≤
        (d : ℝ) * Real.sqrt (∫ x in cubeSetAt y n, ‖g x‖ ^ (2 : ℕ) ∂volume) *
          Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x‖ ^ (2 : ℕ) ∂volume) := by
      rw [mul_assoc, mul_assoc]
      exact hchain
    exact le_of_mul_le_mul_right hmul hpos

/-! ## 4. Additivity of the localized Dirichlet problem -/

private theorem h10Add_toH1Function {U : Set (Vec d)} (v w : H10Function U) :
    (v + w).toH1Function = v.toH1Function + w.toH1Function := rfl

/-- **The sum of two solutions solves the problem for the sum of the forcing
fields.** -/
theorem isDirichletSolutionAt_add {y : Vec d} {n : ℤ} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    {u u' : H1Function (cubeSetAt y n)} {g g' : Vec d → Vec d}
    (hgL2 : MemVectorL2 (cubeSetAt y n) g) (hg'L2 : MemVectorL2 (cubeSetAt y n) g')
    (hu : IsDirichletSolutionAt a y n u g) (hu' : IsDirichletSolutionAt a y n u' g') :
    IsDirichletSolutionAt a y n (u + u') fun x => g x + g' x := by
  obtain ⟨w1, h1f, h1g⟩ := hu.1
  obtain ⟨w2, h2f, h2g⟩ := hu'.1
  refine ⟨⟨w1 + w2, fun x => ?_, fun x => ?_⟩, ?_⟩
  · rw [h10Add_toH1Function]
    show (u + u').toFun x = (w1.toH1Function + w2.toH1Function).toFun x
    simp only [H1Function.add_toFun]
    rw [h1f x, h2f x]
  · rw [h10Add_toH1Function]
    show (u + u').grad x = (w1.toH1Function + w2.toH1Function).grad x
    simp only [H1Function.add_grad]
    rw [h1g x, h2g x]
  · intro phi
    have hAu : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u.grad x) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
    have hAu' : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u'.grad x) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u'.grad_memVectorL2
    have hsplitA : ∀ x, matVecMul (a x) ((u + u').grad x) =
        matVecMul (a x) (u.grad x) + matVecMul (a x) (u'.grad x) := by
      intro x
      have hgx : (u + u').grad x = u.grad x + u'.grad x := by
        simp only [H1Function.add_grad]
      rw [hgx, matVecMul_add]
    rw [Section4.Provider.Schauder.integral_vecDot_add_split hAu hAu' hsplitA phi,
      Section4.Provider.Schauder.integral_vecDot_add_split hgL2 hg'L2 (fun _ => rfl) phi,
      hu.2 phi, hu'.2 phi]
    ring

/-! ## 5. The perturbed coefficient field -/

/-- The perturbation between two fields elliptic on the cube is bounded
entrywise by the sum of their upper ellipticity constants. -/
theorem abs_perturbation_entry_le {U : Set (Vec d)} {a b : CoeffField d}
    {lamA LamA lamB LamB : ℝ} (hEllA : IsEllipticFieldOn lamA LamA U a)
    (hEllB : IsEllipticFieldOn lamB LamB U b) {kap : Vec d → Mat d}
    (hab : ∀ x, b x = a x + kap x) {x : Vec d} (hx : x ∈ U) (i j : Fin d) :
    |kap x i j| ≤ LamA + LamB := by
  have hentry : kap x i j = b x i j - a x i j := by
    have h := congrFun (congrFun (hab x) i) j
    simp only [Matrix.add_apply] at h
    linarith only [h]
  have hA := abs_apply_le_of_isEllipticFieldOn hEllA hx i j
  have hB := abs_apply_le_of_isEllipticFieldOn hEllB hx i j
  have htri : |b x i j - a x i j| ≤ |b x i j| + |a x i j| := abs_sub _ _
  rw [hentry]
  linarith only [htri, hA, hB]

/-- The sum of the two upper ellipticity constants is nonnegative. -/
theorem perturbation_bound_nonneg {U : Set (Vec d)} {a b : CoeffField d}
    {lamA LamA lamB LamB : ℝ} (hx : U.Nonempty) (hEllA : IsEllipticFieldOn lamA LamA U a)
    (hEllB : IsEllipticFieldOn lamB LamB U b) : 0 ≤ LamA + LamB := by
  obtain ⟨x, hxU⟩ := hx
  have hA := hEllA.2 x hxU
  have hB := hEllB.2 x hxU
  linarith only [hA.1, hA.2.1, hB.1, hB.2.1]

/-- The action of the perturbation on an `L²` field is again `L²`: it is the
difference of the actions of the two elliptic fields. -/
theorem memVectorL2_matVecMul_of_coeff_add {U : Set (Vec d)} {a b : CoeffField d}
    {lamA LamA lamB LamB : ℝ} (hEllA : IsEllipticFieldOn lamA LamA U a)
    (hEllB : IsEllipticFieldOn lamB LamB U b) {kap : Vec d → Mat d}
    (hab : ∀ x, b x = a x + kap x) {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemVectorL2 U fun x => matVecMul (kap x) (f x) := by
  have hA := memVectorL2_matVecMul_of_isEllipticFieldOn hEllA hf
  have hB := memVectorL2_matVecMul_of_isEllipticFieldOn hEllB hf
  have hkap : ∀ x, kap x = b x - a x := by
    intro x
    rw [hab x]
    abel
  have hfun : (fun x => matVecMul (kap x) (f x)) =
      fun x => matVecMul (b x) (f x) - matVecMul (a x) (f x) := by
    funext x
    rw [hkap x, matVecMul_matSub]
  rw [hfun]
  exact hB.sub hA

/-- **A solution for `a` is a solution for `b = a + kap`** at the forcing field
corrected by the action of the perturbation on its own gradient. -/
theorem isDirichletSolutionAt_coeff_add {y : Vec d} {n : ℤ} {a b : CoeffField d}
    {lamA LamA lamB LamB : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (cubeSetAt y n) a)
    (hEllB : IsEllipticFieldOn lamB LamB (cubeSetAt y n) b)
    {kap : Vec d → Mat d} (hab : ∀ x, b x = a x + kap x)
    {G : Vec d → Vec d} (hG : MemVectorL2 (cubeSetAt y n) G)
    {u : H1Function (cubeSetAt y n)} (hu : IsDirichletSolutionAt a y n u G) :
    IsDirichletSolutionAt b y n u fun x => G x - matVecMul (kap x) (u.grad x) := by
  refine ⟨hu.1, ?_⟩
  intro phi
  have hAu : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllA u.grad_memVectorL2
  have hKu : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (kap x) (u.grad x) :=
    memVectorL2_matVecMul_of_coeff_add hEllA hEllB hab u.grad_memVectorL2
  have hsplitL : ∀ x, matVecMul (b x) (u.grad x) =
      matVecMul (a x) (u.grad x) + matVecMul (kap x) (u.grad x) := by
    intro x
    rw [hab x, matVecMul_matAdd]
  rw [Section4.Provider.Schauder.integral_vecDot_add_split hAu hKu hsplitL phi,
    Section4.Provider.Schauder.integral_vecDot_sub_split hG hKu (fun _ => rfl) phi,
    hu.2 phi]
  ring

end

end Algsuperdiff.Section5.Support
