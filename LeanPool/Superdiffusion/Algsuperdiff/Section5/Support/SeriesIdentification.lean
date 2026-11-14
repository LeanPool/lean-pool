/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SeriesEnergy

/-!
# SeriesIdentification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The iteration series converges in `H¹₀` and sums to the solution for the perturbed field

Section 5.1 computes the solution of `-∇·a_m∇u = ∇·g` on `y + □_n` by an
iteration that starts from the solution `w_0` for the background field `a_n` and
whose increments solve

```text
  -∇·a_n ∇w_{j+1} = ∇·( (a_m - a_n) ∇w_j )      in y + □_n ,   w_{j+1} = 0 on the boundary.
```

The manuscript asserts `u_m = Σ_j w_j` "provided that we can establish the
convergence of the series" and does not establish it: the contraction it proves
is in `C^{0,1/2}`, which by itself does not identify a limit as a weak solution.
This module supplies the missing step in the norm in which the weak formulation
is continuous.

*The telescoped identity.*  Write `kap := a_m - a_n` and `S_J := Σ_{j ≤ J} w_j`.
Adding the weak equations of `w_0, …, w_J` gives

```text
  ∫ a_n ∇S_J · ∇φ = -∫ g · ∇φ - ∫ (kap ∇S_{J-1}) · ∇φ ,
```

and adding `∫ (kap ∇S_J)·∇φ` to both sides collapses the sum to its last term:

```text
  ∫ a_m ∇S_J · ∇φ = -∫ (g - kap ∇w_J) · ∇φ .
```

So `S_J` solves the problem for `a_m` with the *original* datum `g` up to the
single remainder `-kap ∇w_J`, and the difference `u - S_J` of any solution `u`
for `a_m` at datum `g` and the partial sum solves the problem for `a_m` at datum
`kap ∇w_J`.

*The remainder vanishes.*  The energy estimate applied to that difference gives

```text
  lam_m ‖∇(u - S_J)‖_{L²} ≤ d ‖kap ∇w_J‖_{L²} ≤ d² (Lam_n + Lam_m) ‖∇w_J‖_{L²} ,
```

so the remainder is measured in `L²` (equivalently, the forcing functional it
carries has `H⁻¹` size at most `d` times that `L²` norm), and it tends to zero
as soon as the iterates' energies do.  The per-step constant is bad — it depends
on the molecular diffusivity through `lam_m` and on the scale through the volume
of the cube — but it does not depend on the step index, so a geometric decay of
the data of the steps is enough.  That decay is exactly what the `C^{0,1/2}`
contraction supplies through the supremum bound on the data of the iteration.

## References

* ABK26, the iteration scheme of the proof of the `L^∞` injection estimate.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. Finite sums of Sobolev witnesses -/

/-- The gradient of a finite sum is the sum of the gradients. -/
theorem grad_finset_sum {U : Set (Vec d)} {iota : Type*} (s : Finset iota)
    (v : iota → H1Function U) (x : Vec d) :
    (∑ j ∈ s, v j).grad x = ∑ j ∈ s, (v j).grad x := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  simp only [Finset.sum_insert ha, H1Function.add_grad, ih]

/-- **The partial sum `Σ_{j ≤ J} w_j` of the iteration.** -/
def iterationPartialSum {U : Set (Vec d)} (w : ℕ → H1Function U) (J : ℕ) : H1Function U :=
  ∑ j ∈ Finset.range (J + 1), w j

@[simp] theorem iterationPartialSum_zero {U : Set (Vec d)} (w : ℕ → H1Function U) :
    iterationPartialSum w 0 = w 0 := by
  simp [iterationPartialSum]

theorem iterationPartialSum_succ {U : Set (Vec d)} (w : ℕ → H1Function U) (J : ℕ) :
    iterationPartialSum w (J + 1) = iterationPartialSum w J + w (J + 1) := by
  simp [iterationPartialSum, Finset.sum_range_succ]

theorem iterationPartialSum_grad {U : Set (Vec d)} (w : ℕ → H1Function U) (J : ℕ)
    (x : Vec d) :
    (iterationPartialSum w J).grad x = ∑ j ∈ Finset.range (J + 1), (w j).grad x :=
  grad_finset_sum _ _ _

/-! ## 2. From the Laplace step to the perturbation datum -/

private theorem matVecMul_smul_one {d : ℕ} (xi : Vec d) :
    matVecMul ((1 : ℝ) • (1 : Mat d)) xi = xi := by
  funext i
  simp only [matVecMul, one_smul, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem setIntegral_vecDot_neg_left {d : ℕ} (U : Set (Vec d)) (F p : Vec d → Vec d) :
    ∫ x in U, vecDot (-F x) (p x) ∂volume = -∫ x in U, vecDot (F x) (p x) ∂volume := by
  have hpt : ∀ x : Vec d, vecDot (-F x) (p x) = -vecDot (F x) (p x) := by
    intro x
    simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  simp only [hpt, integral_neg]

/-- **The two halves of one iteration step compose.**  If `h` solves the
Laplace problem with datum `-k ∇v` and the next iterate solves the background
problem with datum `∇h`, then the next iterate solves the background problem
with datum `k ∇v` directly.  This is the step that removes the auxiliary
Laplace solution from the recursion. -/
theorem isDirichletSolutionAt_of_laplacianStep {y : Vec d} {n : ℤ} {a : CoeffField d}
    {k : Vec d → Mat d} {v h u : H1Function (cubeSetAt y n)}
    (hh : IsDirichletSolutionAt (fun _ => (1 : ℝ) • (1 : Mat d)) y n h
      fun x => -matVecMul (k x) (v.grad x))
    (hu : IsDirichletSolutionAt a y n u h.grad) :
    IsDirichletSolutionAt a y n u fun x => matVecMul (k x) (v.grad x) := by
  refine ⟨hu.1, ?_⟩
  intro phi
  have h1 := hu.2 phi
  have h2 := hh.2 phi
  simp only [matVecMul_smul_one] at h2
  rw [setIntegral_vecDot_neg_left] at h2
  rw [h1, h2]
  ring

/-! ## 3. The telescoped weak formulation -/

/-- The partial sum solves the *background* problem with the accumulated
forcing. -/
theorem isDirichletSolutionAt_iterationPartialSum_background {y : Vec d} {n : ℤ}
    {a b : CoeffField d} {lamA LamA lamB LamB : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (cubeSetAt y n) a)
    (hEllB : IsEllipticFieldOn lamB LamB (cubeSetAt y n) b)
    {kap : Vec d → Mat d} (hab : ∀ x, b x = a x + kap x)
    {g : Vec d → Vec d} (hg : MemVectorL2 (cubeSetAt y n) g)
    {w : ℕ → H1Function (cubeSetAt y n)}
    (hw0 : IsDirichletSolutionAt a y n (w 0) g)
    (hwsucc : ∀ j, IsDirichletSolutionAt a y n (w (j + 1))
      fun x => matVecMul (kap x) ((w j).grad x))
    (J : ℕ) :
    IsDirichletSolutionAt a y n (iterationPartialSum w J)
      fun x => g x + ∑ j ∈ Finset.range J, matVecMul (kap x) ((w j).grad x) := by
  induction J with
  | zero =>
      have hdat : (fun x => g x + ∑ j ∈ Finset.range 0,
          matVecMul (kap x) ((w j).grad x)) = g := by
        funext x
        simp
      rw [iterationPartialSum_zero, hdat]
      exact hw0
  | succ J ih =>
      have hsum : MemVectorL2 (cubeSetAt y n)
          fun x => g x + ∑ j ∈ Finset.range J, matVecMul (kap x) ((w j).grad x) :=
        hg.add (memLp_finsetSum _ fun j _ =>
          memVectorL2_matVecMul_of_coeff_add hEllA hEllB hab (w j).grad_memVectorL2)
      have hlast : MemVectorL2 (cubeSetAt y n)
          fun x => matVecMul (kap x) ((w J).grad x) :=
        memVectorL2_matVecMul_of_coeff_add hEllA hEllB hab (w J).grad_memVectorL2
      have hstep := isDirichletSolutionAt_add hEllA hsum hlast ih (hwsucc J)
      have hdat : (fun x => (g x + ∑ j ∈ Finset.range J, matVecMul (kap x) ((w j).grad x)) +
            matVecMul (kap x) ((w J).grad x)) =
          fun x => g x + ∑ j ∈ Finset.range (J + 1), matVecMul (kap x) ((w j).grad x) := by
        funext x
        rw [Finset.sum_range_succ, add_assoc]
      rw [iterationPartialSum_succ, ← hdat]
      exact hstep

/-- **The telescoped weak formulation.**  Against the perturbed field the whole
accumulated forcing collapses to the original datum minus the action of the
perturbation on the gradient of the last iterate. -/
theorem isDirichletSolutionAt_iterationPartialSum {y : Vec d} {n : ℤ}
    {a b : CoeffField d} {lamA LamA lamB LamB : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (cubeSetAt y n) a)
    (hEllB : IsEllipticFieldOn lamB LamB (cubeSetAt y n) b)
    {kap : Vec d → Mat d} (hab : ∀ x, b x = a x + kap x)
    {g : Vec d → Vec d} (hg : MemVectorL2 (cubeSetAt y n) g)
    {w : ℕ → H1Function (cubeSetAt y n)}
    (hw0 : IsDirichletSolutionAt a y n (w 0) g)
    (hwsucc : ∀ j, IsDirichletSolutionAt a y n (w (j + 1))
      fun x => matVecMul (kap x) ((w j).grad x))
    (J : ℕ) :
    IsDirichletSolutionAt b y n (iterationPartialSum w J)
      fun x => g x - matVecMul (kap x) ((w J).grad x) := by
  have hbase := isDirichletSolutionAt_iterationPartialSum_background hEllA hEllB hab hg
    hw0 hwsucc J
  have hsum : MemVectorL2 (cubeSetAt y n)
      fun x => g x + ∑ j ∈ Finset.range J, matVecMul (kap x) ((w j).grad x) :=
    hg.add (memLp_finsetSum _ fun j _ =>
      memVectorL2_matVecMul_of_coeff_add hEllA hEllB hab (w j).grad_memVectorL2)
  have hshift := isDirichletSolutionAt_coeff_add hEllA hEllB hab hsum hbase
  have hdat : (fun x => (g x + ∑ j ∈ Finset.range J, matVecMul (kap x) ((w j).grad x)) -
        matVecMul (kap x) ((iterationPartialSum w J).grad x)) =
      fun x => g x - matVecMul (kap x) ((w J).grad x) := by
    funext x
    rw [iterationPartialSum_grad, matVecMul_finset_sum, Finset.sum_range_succ]
    abel
  rwa [hdat] at hshift

/-- **The remainder problem.**  Any solution for the perturbed field at the
original datum differs from the partial sum by the solution at the single
remainder datum. -/
theorem isDirichletSolutionAt_sub_iterationPartialSum {y : Vec d} {n : ℤ}
    {a b : CoeffField d} {lamA LamA lamB LamB : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (cubeSetAt y n) a)
    (hEllB : IsEllipticFieldOn lamB LamB (cubeSetAt y n) b)
    {kap : Vec d → Mat d} (hab : ∀ x, b x = a x + kap x)
    {g : Vec d → Vec d} (hg : MemVectorL2 (cubeSetAt y n) g)
    {w : ℕ → H1Function (cubeSetAt y n)}
    (hw0 : IsDirichletSolutionAt a y n (w 0) g)
    (hwsucc : ∀ j, IsDirichletSolutionAt a y n (w (j + 1))
      fun x => matVecMul (kap x) ((w j).grad x))
    {u : H1Function (cubeSetAt y n)} (hu : IsDirichletSolutionAt b y n u g) (J : ℕ) :
    IsDirichletSolutionAt b y n (u - iterationPartialSum w J)
      fun x => matVecMul (kap x) ((w J).grad x) := by
  have hlast : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (kap x) ((w J).grad x) :=
    memVectorL2_matVecMul_of_coeff_add hEllA hEllB hab (w J).grad_memVectorL2
  have hS := isDirichletSolutionAt_iterationPartialSum hEllA hEllB hab hg hw0 hwsucc J
  have hsub : MemVectorL2 (cubeSetAt y n)
      fun x => g x - matVecMul (kap x) ((w J).grad x) := by
    simpa only [Pi.sub_apply] using! hg.sub hlast
  have hdiff := isDirichletSolutionAt_sub hEllB hg hsub hu hS
  have hdat : (fun x => g x - (g x - matVecMul (kap x) ((w J).grad x))) =
      fun x => matVecMul (kap x) ((w J).grad x) := by
    funext x
    abel
  rwa [hdat] at hdiff

/-! ## 4. The remainder vanishes -/

/-- **The quantitative remainder bound.**  The distance from the partial sum to
any solution for the perturbed field is controlled, in the energy norm, by the
energy of the last iterate. -/
theorem sqrt_energy_grad_sub_iterationPartialSum_le {y : Vec d} {n : ℤ}
    {a b : CoeffField d} {lamA LamA lamB LamB : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (cubeSetAt y n) a)
    (hEllB : IsEllipticFieldOn lamB LamB (cubeSetAt y n) b)
    {kap : Vec d → Mat d} (hab : ∀ x, b x = a x + kap x)
    {g : Vec d → Vec d} (hg : MemVectorL2 (cubeSetAt y n) g)
    {w : ℕ → H1Function (cubeSetAt y n)}
    (hw0 : IsDirichletSolutionAt a y n (w 0) g)
    (hwsucc : ∀ j, IsDirichletSolutionAt a y n (w (j + 1))
      fun x => matVecMul (kap x) ((w j).grad x))
    {u : H1Function (cubeSetAt y n)} (hu : IsDirichletSolutionAt b y n u g) (J : ℕ) :
    lamB * Real.sqrt (∫ x in cubeSetAt y n,
        ‖u.grad x - (iterationPartialSum w J).grad x‖ ^ (2 : ℕ) ∂volume) ≤
      (d : ℝ) * ((d : ℝ) * (LamA + LamB)) *
        Real.sqrt (∫ x in cubeSetAt y n, ‖(w J).grad x‖ ^ (2 : ℕ) ∂volume) := by
  have hlast : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (kap x) ((w J).grad x) :=
    memVectorL2_matVecMul_of_coeff_add hEllA hEllB hab (w J).grad_memVectorL2
  have hdiff := isDirichletSolutionAt_sub_iterationPartialSum hEllA hEllB hab hg hw0
    hwsucc hu J
  have hEnergy := sqrt_energy_grad_le_of_isDirichletSolutionAt hEllB hlast hdiff
  have hgradEq : ∀ x, (u - iterationPartialSum w J).grad x =
      u.grad x - (iterationPartialSum w J).grad x := by
    intro x
    simp only [H1Function.sub_grad]
  simp only [hgradEq] at hEnergy
  have hdelta : (0 : ℝ) ≤ LamA + LamB :=
    perturbation_bound_nonneg (cubeSetAt_nonempty y n) hEllA hEllB
  have hact := sqrt_setIntegral_sq_matVecMul_le (measurableSet_cubeSetAt y n) hdelta
    (fun x hx i j => abs_perturbation_entry_le hEllA hEllB hab hx i j)
    (w J).grad_memVectorL2 hlast
  calc lamB * Real.sqrt (∫ x in cubeSetAt y n,
        ‖u.grad x - (iterationPartialSum w J).grad x‖ ^ (2 : ℕ) ∂volume)
      ≤ (d : ℝ) * Real.sqrt (∫ x in cubeSetAt y n,
          ‖matVecMul (kap x) ((w J).grad x)‖ ^ (2 : ℕ) ∂volume) := hEnergy
    _ ≤ (d : ℝ) * ((d : ℝ) * (LamA + LamB) *
          Real.sqrt (∫ x in cubeSetAt y n, ‖(w J).grad x‖ ^ (2 : ℕ) ∂volume)) :=
        mul_le_mul_of_nonneg_left hact (by positivity)
    _ = (d : ℝ) * ((d : ℝ) * (LamA + LamB)) *
          Real.sqrt (∫ x in cubeSetAt y n, ‖(w J).grad x‖ ^ (2 : ℕ) ∂volume) := by ring

/-- **The partial sums converge to the solution in the energy norm.** -/
theorem tendsto_sqrt_energy_grad_sub_iterationPartialSum {y : Vec d} {n : ℤ}
    {a b : CoeffField d} {lamA LamA lamB LamB : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (cubeSetAt y n) a)
    (hEllB : IsEllipticFieldOn lamB LamB (cubeSetAt y n) b)
    {kap : Vec d → Mat d} (hab : ∀ x, b x = a x + kap x)
    {g : Vec d → Vec d} (hg : MemVectorL2 (cubeSetAt y n) g)
    {w : ℕ → H1Function (cubeSetAt y n)}
    (hw0 : IsDirichletSolutionAt a y n (w 0) g)
    (hwsucc : ∀ j, IsDirichletSolutionAt a y n (w (j + 1))
      fun x => matVecMul (kap x) ((w j).grad x))
    {u : H1Function (cubeSetAt y n)} (hu : IsDirichletSolutionAt b y n u g)
    (hlim : Filter.Tendsto (fun j => Real.sqrt (∫ x in cubeSetAt y n,
        ‖(w j).grad x‖ ^ (2 : ℕ) ∂volume)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun J => Real.sqrt (∫ x in cubeSetAt y n,
        ‖u.grad x - (iterationPartialSum w J).grad x‖ ^ (2 : ℕ) ∂volume))
      Filter.atTop (nhds 0) := by
  have hlamB : 0 < lamB := (hEllB.2 y (mem_cubeSetAt_self y n)).1
  refine squeeze_zero (fun J => Real.sqrt_nonneg _) (fun J => ?_)
    (by simpa using hlim.const_mul (lamB⁻¹ * ((d : ℝ) * ((d : ℝ) * (LamA + LamB)))))
  have hstep := sqrt_energy_grad_sub_iterationPartialSum_le hEllA hEllB hab hg hw0
    hwsucc hu J
  rw [← le_div_iff₀' hlamB] at hstep
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- The value of the difference is controlled by its energy: a solution and a
partial sum both vanish on the boundary, so their difference is a zero-trace
function and the Poincaré inequality applies. -/
theorem tendsto_sqrt_setIntegral_sq_of_tendsto_energy [NeZero d] {y : Vec d} {n : ℤ}
    {v : ℕ → H1Function (cubeSetAt y n)}
    (hzero : ∀ J, ∃ p : H10Function (cubeSetAt y n),
      (∀ x, (v J).toFun x = p.toH1Function.toFun x) ∧
        (∀ x, (v J).grad x = p.toH1Function.grad x))
    (hlim : Filter.Tendsto (fun J => Real.sqrt (∫ x in cubeSetAt y n,
        ‖(v J).grad x‖ ^ (2 : ℕ) ∂volume)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun J => Real.sqrt (∫ x in cubeSetAt y n,
        (v J).toFun x ^ (2 : ℕ) ∂volume)) Filter.atTop (nhds 0) := by
  obtain ⟨CP, hCP, hpoin⟩ :=
    exists_poincare_integral_constant (isOpenBoundedConvexDomain_cubeSetAt y n)
  refine squeeze_zero (fun J => Real.sqrt_nonneg _) (fun J => ?_)
    (by simpa using hlim.const_mul CP)
  obtain ⟨p, hpf, hpg⟩ := hzero J
  have h := hpoin p
  simp only [← hpf, ← hpg] at h
  exact h

/-- **The partial sums converge to the solution in value as well.** -/
theorem tendsto_sqrt_setIntegral_sq_sub_iterationPartialSum [NeZero d] {y : Vec d} {n : ℤ}
    {a b : CoeffField d} {lamA LamA lamB LamB : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (cubeSetAt y n) a)
    (hEllB : IsEllipticFieldOn lamB LamB (cubeSetAt y n) b)
    {kap : Vec d → Mat d} (hab : ∀ x, b x = a x + kap x)
    {g : Vec d → Vec d} (hg : MemVectorL2 (cubeSetAt y n) g)
    {w : ℕ → H1Function (cubeSetAt y n)}
    (hw0 : IsDirichletSolutionAt a y n (w 0) g)
    (hwsucc : ∀ j, IsDirichletSolutionAt a y n (w (j + 1))
      fun x => matVecMul (kap x) ((w j).grad x))
    {u : H1Function (cubeSetAt y n)} (hu : IsDirichletSolutionAt b y n u g)
    (hlim : Filter.Tendsto (fun j => Real.sqrt (∫ x in cubeSetAt y n,
        ‖(w j).grad x‖ ^ (2 : ℕ) ∂volume)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun J => Real.sqrt (∫ x in cubeSetAt y n,
        (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume))
      Filter.atTop (nhds 0) := by
  have hgrad := tendsto_sqrt_energy_grad_sub_iterationPartialSum hEllA hEllB hab hg hw0
    hwsucc hu hlim
  have hzero : ∀ J, ∃ p : H10Function (cubeSetAt y n),
      (∀ x, (u - iterationPartialSum w J).toFun x = p.toH1Function.toFun x) ∧
        (∀ x, (u - iterationPartialSum w J).grad x = p.toH1Function.grad x) := by
    intro J
    exact (isDirichletSolutionAt_sub_iterationPartialSum hEllA hEllB hab hg hw0
      hwsucc hu J).1
  have hval := tendsto_sqrt_setIntegral_sq_of_tendsto_energy hzero
    (by simpa only [H1Function.sub_grad] using hgrad)
  simpa only [H1Function.sub_toFun] using hval

/-! ## 5. Geometric decay of the energies of the iterates -/

/-- One step of the iteration, in the energy norm: the energy of an iterate is
controlled by the supremum size of its datum on the cube. -/
theorem sqrt_energy_grad_succ_le_of_sup_bound {y : Vec d} {n : ℤ} {a : CoeffField d}
    {lamA LamA : ℝ} (hEllA : IsEllipticFieldOn lamA LamA (cubeSetAt y n) a)
    {w : ℕ → H1Function (cubeSetAt y n)} {G : ℕ → Vec d → Vec d}
    (hGL2 : ∀ j, MemVectorL2 (cubeSetAt y n) (G j))
    (hwsucc : ∀ j, IsDirichletSolutionAt a y n (w (j + 1)) (G j))
    {B rho : ℝ} (hB : 0 ≤ B) (hrho : 0 ≤ rho)
    (hGsup : ∀ j, ∀ x ∈ cubeSetAt y n, ‖G j x‖ ≤ B * rho ^ j) (j : ℕ) :
    lamA * Real.sqrt (∫ x in cubeSetAt y n,
        ‖(w (j + 1)).grad x‖ ^ (2 : ℕ) ∂volume) ≤
      (d : ℝ) * (Real.sqrt ((volume (cubeSetAt y n)).toReal) * (B * rho ^ j)) := by
  have hUfin : volume (cubeSetAt y n) ≠ ⊤ :=
    ((isOpenBoundedConvexDomain_cubeSetAt y n).volume_lt_top).ne
  have hdata : Real.sqrt (∫ x in cubeSetAt y n, ‖G j x‖ ^ (2 : ℕ) ∂volume) ≤
      Real.sqrt ((volume (cubeSetAt y n)).toReal) * (B * rho ^ j) :=
    sqrt_setIntegral_sq_le_of_sup_bound (measurableSet_cubeSetAt y n) hUfin (hGL2 j)
      (by positivity) (hGsup j)
  refine (sqrt_energy_grad_le_of_isDirichletSolutionAt hEllA (hGL2 j) (hwsucc j)).trans ?_
  exact mul_le_mul_of_nonneg_left hdata (by positivity)

/-- **The energies of the iterates tend to zero** when the data of the steps
decay geometrically in the supremum norm on the cube. -/
theorem tendsto_sqrt_energy_grad_of_sup_bound {y : Vec d} {n : ℤ} {a : CoeffField d}
    {lamA LamA : ℝ} (hEllA : IsEllipticFieldOn lamA LamA (cubeSetAt y n) a)
    {w : ℕ → H1Function (cubeSetAt y n)} {G : ℕ → Vec d → Vec d}
    (hGL2 : ∀ j, MemVectorL2 (cubeSetAt y n) (G j))
    (hwsucc : ∀ j, IsDirichletSolutionAt a y n (w (j + 1)) (G j))
    {B rho : ℝ} (hB : 0 ≤ B) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hGsup : ∀ j, ∀ x ∈ cubeSetAt y n, ‖G j x‖ ≤ B * rho ^ j) :
    Filter.Tendsto (fun j => Real.sqrt (∫ x in cubeSetAt y n,
        ‖(w j).grad x‖ ^ (2 : ℕ) ∂volume)) Filter.atTop (nhds 0) := by
  have hlam : 0 < lamA := (hEllA.2 y (mem_cubeSetAt_self y n)).1
  have hstep : ∀ j, Real.sqrt (∫ x in cubeSetAt y n,
      ‖(w (j + 1)).grad x‖ ^ (2 : ℕ) ∂volume) ≤
      lamA⁻¹ * ((d : ℝ) * (Real.sqrt ((volume (cubeSetAt y n)).toReal) * B)) * rho ^ j := by
    intro j
    have h := sqrt_energy_grad_succ_le_of_sup_bound hEllA hGL2 hwsucc hB hrho hGsup j
    rw [← le_div_iff₀' hlam] at h
    refine h.trans (le_of_eq ?_)
    field_simp
  have hgeom : Filter.Tendsto
      (fun j => lamA⁻¹ * ((d : ℝ) *
        (Real.sqrt ((volume (cubeSetAt y n)).toReal) * B)) * rho ^ j)
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hrho hrho1).const_mul
        (lamA⁻¹ * ((d : ℝ) * (Real.sqrt ((volume (cubeSetAt y n)).toReal) * B)))
  have hshift := squeeze_zero (fun j => Real.sqrt_nonneg _) hstep hgeom
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hshift

/-! ## 6. The cutoff coefficient fields of the model -/

/-- The coefficient field at scale `m` is the field at scale `n` perturbed by
the difference of the two cutoff shell sums; no order relation between the
scales is used. -/
theorem coefficientCutoff_eq_add_cutoff_sub (M : ABKModel d) (m n : ℤ)
    (omega : Cutoff.CutoffSample d) (x : Vec d) :
    ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) x =
      ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) x +
        (Cutoff.cutoff m omega x - Cutoff.cutoff n omega x) := by
  simp only [RegCoeffField.toCoeffField_apply, Cutoff.coefficientCutoff_apply]
  abel

/-- **Every solution for the coefficient field at scale `m` is the limit of the
partial sums of the iteration**, in gradient and in value.  The limit is the
same for every solution, so any two solutions of that Dirichlet problem agree
almost everywhere on the cube, in value and in gradient. -/
theorem tendsto_sub_iterationPartialSum_cutoff (M : ABKModel d) (m n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d}
    (hg : MemVectorL2 (cubeSetAt y n) g) {w : ℕ → H1Function (cubeSetAt y n)}
    (hw0 : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n (w 0) g)
    (hwsucc : ∀ j, IsDirichletSolutionAt
      ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n (w (j + 1))
      fun x => matVecMul (Cutoff.cutoff m omega x - Cutoff.cutoff n omega x)
        ((w j).grad x))
    {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField)
      y n u g)
    (hlim : Filter.Tendsto (fun j => Real.sqrt (∫ x in cubeSetAt y n,
        ‖(w j).grad x‖ ^ (2 : ℕ) ∂volume)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun J => Real.sqrt (∫ x in cubeSetAt y n,
        ‖u.grad x - (iterationPartialSum w J).grad x‖ ^ (2 : ℕ) ∂volume))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun J => Real.sqrt (∫ x in cubeSetAt y n,
        (u.toFun x - (iterationPartialSum w J).toFun x) ^ (2 : ℕ) ∂volume))
        Filter.atTop (nhds 0) := by
  have : NeZero d := Provider.Orlicz.neZero_of_model M
  obtain ⟨LamA, hEllA⟩ := exists_isEllipticFieldOn_cutoff M n n y omega
  obtain ⟨LamB, hEllB⟩ := exists_isEllipticFieldOn_cutoff M m n y omega
  have hab := coefficientCutoff_eq_add_cutoff_sub M m n omega
  exact ⟨tendsto_sqrt_energy_grad_sub_iterationPartialSum hEllA hEllB hab hg hw0 hwsucc
      hu hlim,
    tendsto_sqrt_setIntegral_sq_sub_iterationPartialSum hEllA hEllB hab hg hw0 hwsucc
      hu hlim⟩

end

end Algsuperdiff.Section5.Support
