/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Ellipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TwoTermCalculus
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.Translation
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareZeroTrace

/-!
# DirichletSolvability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Solvability of the localized Dirichlet problems, and uniqueness up to null sets

Section 5 names two solutions on `y + □_n`: the solution `u_m` of
`-∇·a_m∇u = ∇·g` for the cutoff coefficient field at scale `m`, and the
comparator `v` solving `-σ_n Δ v = ∇·g`.  Naming them presupposes that they
exist, and using them in a supremum presupposes that the family they range over
is nonempty.  This module supplies both existence statements on the translated
carrier, and the uniqueness that holds at this level of regularity: two
solutions of the same problem agree away from a null set.

Pointwise uniqueness is a statement about a *continuous representative*, not
about the `H¹` witnesses; it belongs to the representative theory and is not
proved here.

## Main results

* `exists_isDirichletSolutionAt_comparator` — the comparator exists for every
  `1/2`-Hölder forcing field.
* `exists_isDirichletSolutionAt_cutoff` — the rough-field solution exists for
  every `1/2`-Hölder forcing field, at every scale `m` and every sample.
* `isDirichletSolutionAt_ae_unique` — two solutions of the same problem, for a
  coefficient field that is elliptic on the cube, have gradients and values that
  agree almost everywhere on the cube.

## The ellipticity hypothesis of the uniqueness statement

`isDirichletSolutionAt_ae_unique` carries `IsEllipticFieldOn lam Lam` on the
cube.  This is a genuine premise, not a convenience: for a degenerate
coefficient field the Dirichlet problem has many solutions, so no
hypothesis-free uniqueness statement is true.  Both families used by Section 5
satisfy it — the comparator with `lam = Lam = σ_n`, the cutoff field with
`lam = ν` — and the two hypothesis-free specializations
`isDirichletSolutionAt_ae_unique_comparator` and
`isDirichletSolutionAt_ae_unique_cutoff` are recorded below.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Moving a solution from `□_n` back to `y + □_n` -/

/-- Two `H¹` witnesses with the same value and gradient are equal: the remaining
fields are propositions. -/
theorem h1Function_ext {U : Set (Vec d)} : ∀ {u v : H1Function U},
    u.toFun = v.toFun → u.grad = v.grad → u = v := by
  rintro ⟨uf, ug, up, uq, ur⟩ ⟨vf, vg, vp, vq, vr⟩ rfl rfl
  rfl

/-- An `H¹` witness on `□_n`, read on `y + □_n` as `x ↦ v(x - y)`. -/
def translateSolution (y : Vec d) (n : ℤ) (v : H1Function (openCubeSet (originCube d n))) :
    H1Function (cubeSetAt y n) :=
  castH1 (cubeSetAt_eq_translateSet y n).symm (H1Function.translate v y)

@[simp] theorem originPullback_translateSolution (y : Vec d) (n : ℤ)
    (v : H1Function (openCubeSet (originCube d n))) :
    originPullback y n (translateSolution y n v) = v := by
  refine h1Function_ext (funext fun x => ?_) (funext fun x => ?_) <;>
    simp [translateSolution, add_sub_cancel_right]

/-! ## 2. Hölder data on the translated cube -/

/-- The `C^{0,α}` bound transports to the origin cube. -/
theorem holderSeminormBoundOn_originCube_of_cubeSetAt {E : Type*} [NormedAddCommGroup E]
    {y : Vec d} {n : ℤ} {alpha K : ℝ} {f : Vec d → E}
    (hf : HolderSeminormBoundOn (cubeSetAt y n) alpha K f) :
    HolderSeminormBoundOn (openCubeSet (originCube d n)) alpha K (fun x => f (y + x)) := by
  intro x hx z hz
  have hx' : y + x ∈ cubeSetAt y n := by
    rw [mem_cubeSetAt_iff]; simpa [add_comm] using hx
  have hz' : y + z ∈ cubeSetAt y n := by
    rw [mem_cubeSetAt_iff]; simpa [add_comm] using hz
  have hsub : (y + x) - (y + z) = x - z := by ring
  have h := hf (y + x) hx' (y + z) hz'
  rw [hsub] at h
  exact h

/-- On the translated cube in dimension `d ≥ 1`, a Hölder bound forces its
constant to be nonnegative. -/
theorem holderSeminormBoundOn_nonneg_cubeSetAt {E : Type*} [NormedAddCommGroup E]
    {y : Vec d} {n : ℤ} {alpha K : ℝ} {f : Vec d → E} (hd : 0 < d)
    (hf : HolderSeminormBoundOn (cubeSetAt y n) alpha K f) : 0 ≤ K :=
  Section4.Provider.Schauder.holderSeminormBoundOn_nonneg_openCubeSet hd
    (holderSeminormBoundOn_originCube_of_cubeSetAt hf)

/-- **A Hölder-continuous vector field on `y + □_n` is square integrable there.** -/
theorem memVectorL2_of_holderSeminormBoundOn_cubeSetAt {y : Vec d} {n : ℤ} {alpha K : ℝ}
    {f : Vec d → Vec d} (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hf : HolderSeminormBoundOn (cubeSetAt y n) alpha K f) :
    MemVectorL2 (cubeSetAt y n) f := by
  have : IsFiniteMeasure (volumeMeasureOn (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  have hmeas : AEStronglyMeasurable f (volumeMeasureOn (cubeSetAt y n)) :=
    (Section4.Provider.Schauder.continuousOn_of_holderSeminormBoundOn hK halpha
      hf).aestronglyMeasurable (measurableSet_cubeSetAt y n)
  refine MemLp.of_bound hmeas (‖f y‖ + K * ((3 : ℝ) ^ n) ^ alpha) ?_
  refine (ae_restrict_iff' (measurableSet_cubeSetAt y n)).2 ?_
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hy := mem_cubeSetAt_self y n
  have hbd := hf x hx y hy
  have hdiam : ‖x - y‖ ≤ (3 : ℝ) ^ n := (norm_sub_lt_of_mem_cubeSetAt hx hy).le
  have hmono : ‖x - y‖ ^ alpha ≤ ((3 : ℝ) ^ n) ^ alpha :=
    Real.rpow_le_rpow (norm_nonneg _) hdiam halpha.le
  have hmul : K * ‖x - y‖ ^ alpha ≤ K * ((3 : ℝ) ^ n) ^ alpha :=
    mul_le_mul_of_nonneg_left hmono hK
  have htri : ‖f x‖ ≤ ‖f x - f y‖ + ‖f y‖ := by
    simpa using norm_add_le (f x - f y) (f y)
  linarith only [hbd, hmul, htri]

/-! ## 3. Existence for the comparator -/

/-- **The comparator exists.**  For every scale, centre and `1/2`-Hölder forcing
field the constant-coefficient Dirichlet problem `-σ_n Δ v = ∇·g` on `y + □_n`
with zero boundary values has a solution. -/
theorem exists_isDirichletSolutionAt_comparator (M : ABKModel d) (n : ℤ) (y : Vec d)
    {g : Vec d → Vec d} {Kg : ℝ}
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g) :
    ∃ v : H1Function (cubeSetAt y n),
      IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g := by
  have : NeZero d := Provider.Orlicz.neZero_of_model M
  obtain ⟨vOrigin, hvOrigin⟩ :=
    Section4.Provider.Schauder.exists_isDirichletSolutionOn_smul_one_of_holder
      (m := n) (Provider.Orlicz.sigmaBar_pos M n) 0
      (holderSeminormBoundOn_originCube_of_cubeSetAt hg)
  refine ⟨translateSolution y n vOrigin, ?_⟩
  rw [isDirichletSolutionAt_iff_origin, originPullback_translateSolution]
  exact hvOrigin

/-! ## 4. Existence for the rough field -/

/-- Every translated cube is contained in a centred cube of a large enough
scale. -/
theorem exists_cubeSetAt_subset_openCubeSet (y : Vec d) (n : ℤ) :
    ∃ ell : ℤ, cubeSetAt y n ⊆ openCubeSet (originCube d ell) := by
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt (2 * ‖y‖ + (3 : ℝ) ^ n) (by norm_num : (1 : ℝ) < 3)
  refine ⟨(k : ℤ), fun x hx => ?_⟩
  rw [mem_openCubeSet_originCube_iff]
  rw [mem_cubeSetAt_iff_forall_coord] at hx
  intro i
  have h1 := hx i
  have hyi : |y i| ≤ ‖y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
  have hy := abs_le.1 hyi
  have hpow : (3 : ℝ) ^ ((k : ℤ)) = (3 : ℝ) ^ k := zpow_natCast 3 k
  rw [hpow]
  constructor <;> linarith only [h1.1, h1.2, hy.1, hy.2, hk]

/-- **The rough-field solution exists.**  For every sample, every scale `m`,
every cube `y + □_n` and every `1/2`-Hölder forcing field the Dirichlet problem
`-∇·a_m∇u = ∇·g` with zero boundary values has a solution. -/
theorem exists_isDirichletSolutionAt_cutoff (M : ABKModel d) (m n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d} {Kg : ℝ}
    (hg : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g) :
    ∃ u : H1Function (cubeSetAt y n),
      IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n u g := by
  have : NeZero d := Provider.Orlicz.neZero_of_model M
  have hd : 0 < d := Provider.Orlicz.dim_pos_of_model M
  have hKg : 0 ≤ Kg := holderSeminormBoundOn_nonneg_cubeSetAt hd hg
  have : IsFiniteMeasure (volumeMeasureOn (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  obtain ⟨ell, hell⟩ := exists_cubeSetAt_subset_openCubeSet y n
  have hEll := Cutoff.isEllipticFieldOn_coefficientCutoff_of_entry_bound M m omega
    (measurableSet_cubeSetAt y n) (M.nu + Cutoff.cutoffLocalControl ell m omega)
    (fun x hx i j => Cutoff.abs_coefficientCutoff_entry_le M.nu M.nu_pos.le ell m omega
      (hell hx) i j)
  have hforce : MemVectorL2 (cubeSetAt y n) (fun x => -g x) :=
    (memVectorL2_of_holderSeminormBoundOn_cubeSetAt hKg (by norm_num) hg).neg
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := (Cutoff.coefficientCutoff M.nu m omega).toCoeffField) (U := cubeSetAt y n)
      (g := fun x => -g x) (lam := M.nu)
      hforce
      (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
        (isOpenBoundedConvexDomain_cubeSetAt y n))
      (cubeSetAt_nonempty y n) hEll
  refine ⟨w.toH1Function, ⟨w, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  exact (isZeroTraceDirichletRhsWeakSolution_iff_isDivFormWeakSolutionOn
    (u := w.toH1Function) (w := w) (fun _ => rfl)).1 hw

/-! ## 5. Uniqueness away from a null set -/

private theorem h10Sub_toH1Function {U : Set (Vec d)} (v w : H10Function U) :
    (v - w).toH1Function = v.toH1Function - w.toH1Function := rfl

/-- **Two solutions of the same localized Dirichlet problem agree almost
everywhere on the cube**, gradient and value.

The ellipticity of `a` on the cube is a genuine premise: without it the
homogeneous problem has nonzero solutions. -/
theorem isDirichletSolutionAt_ae_unique {a : CoeffField d} {lam Lam : ℝ}
    {y : Vec d} {n : ℤ} (hd : 0 < d)
    (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    {u u' : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    (hu : IsDirichletSolutionAt a y n u g) (hu' : IsDirichletSolutionAt a y n u' g) :
    u.grad =ᵐ[volume.restrict (cubeSetAt y n)] u'.grad ∧
      u.toFun =ᵐ[volume.restrict (cubeSetAt y n)] u'.toFun := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨w, hwf, hwg⟩ :
      ∃ w : H10Function (cubeSetAt y n),
        (∀ x, w.toH1Function.toFun x = u.toFun x - u'.toFun x) ∧
          (∀ x, w.toH1Function.grad x = u.grad x - u'.grad x) := by
    obtain ⟨w1, h1f, h1g⟩ := hu.1
    obtain ⟨w2, h2f, h2g⟩ := hu'.1
    refine ⟨w1 - w2, fun x => ?_, fun x => ?_⟩
    · rw [h1f x, h2f x, h10Sub_toH1Function]
      simp only [H1Function.sub_toFun]
    · rw [h1g x, h2g x, h10Sub_toH1Function]
      simp only [H1Function.sub_grad]
  have hgradL2 : MemVectorL2 (cubeSetAt y n) w.toH1Function.grad :=
    w.toH1Function.grad_memVectorL2
  have hAw : MemVectorL2 (cubeSetAt y n)
      (fun x => matVecMul (a x) (w.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hgradL2
  have hAu : MemVectorL2 (cubeSetAt y n) (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hAu' : MemVectorL2 (cubeSetAt y n) (fun x => matVecMul (a x) (u'.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u'.grad_memVectorL2
  have hsplit : ∀ x, matVecMul (a x) (w.toH1Function.grad x) =
      matVecMul (a x) (u.grad x) - matVecMul (a x) (u'.grad x) := by
    intro x
    rw [hwg x, sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]
  have hzero : ∫ x in cubeSetAt y n, vecDot (matVecMul (a x) (w.toH1Function.grad x))
      (w.toH1Function.grad x) ∂volume = 0 := by
    rw [Section4.Provider.Schauder.integral_vecDot_sub_split hAu hAu' hsplit w,
      hu.2 w, hu'.2 w, sub_self]
  have hlam : 0 < lam := (hEll.2 y (mem_cubeSetAt_self y n)).1
  have hnonneg : ∀ x ∈ cubeSetAt y n, lam * vecNormSq (w.toH1Function.grad x) ≤
      vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x) := by
    intro x hx
    have h := (hEll.2 x hx).2.2.1 (w.toH1Function.grad x)
    rw [vecDot_comm]
    exact h
  have hintAw : IntegrableOn (fun x => vecDot (matVecMul (a x) (w.toH1Function.grad x))
      (w.toH1Function.grad x)) (cubeSetAt y n) :=
    integrableOn_vecDot_of_memVectorL2 hAw hgradL2
  have hintSq : IntegrableOn (fun x => lam * vecNormSq (w.toH1Function.grad x))
      (cubeSetAt y n) :=
    (integrableOn_vecDot_of_memVectorL2 hgradL2 hgradL2).const_mul lam
  have hle : ∫ x in cubeSetAt y n, lam * vecNormSq (w.toH1Function.grad x) ∂volume ≤ 0 := by
    rw [← hzero]
    refine integral_mono_ae hintSq hintAw ?_
    exact (ae_restrict_iff' (measurableSet_cubeSetAt y n)).2
      (Filter.Eventually.of_forall hnonneg)
  have hge : (0 : ℝ) ≤ ∫ x in cubeSetAt y n,
      lam * vecNormSq (w.toH1Function.grad x) ∂volume :=
    integral_nonneg fun x => mul_nonneg hlam.le (vecNormSq_nonneg _)
  have haeSq : (fun x => lam * vecNormSq (w.toH1Function.grad x))
      =ᵐ[volume.restrict (cubeSetAt y n)] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => mul_nonneg hlam.le (vecNormSq_nonneg _)) hintSq).1 (le_antisymm hle hge)
  have haeGrad : w.toH1Function.grad =ᵐ[volume.restrict (cubeSetAt y n)] 0 := by
    filter_upwards [haeSq] with x hx
    simp only [Pi.zero_apply] at hx
    rcases mul_eq_zero.1 hx with h | h
    · exact absurd h hlam.ne'
    · exact vecNormSq_eq_zero h
  refine ⟨?_, ?_⟩
  · filter_upwards [haeGrad] with x hx
    have hdiff := hwg x
    rw [hx] at hdiff
    simp only [Pi.zero_apply] at hdiff
    exact sub_eq_zero.1 hdiff.symm
  · have hzeroVec : MemVectorL2 (cubeSetAt y n) (0 : Vec d → Vec d) := MemLp.zero
    have hgradL2zero : w.toH1Function.gradToVectorL2 = 0 :=
      (toVectorL2_eq_toVectorL2_iff w.toH1Function.grad_memVectorL2 hzeroVec).2 haeGrad
    have hscalar :=
      H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
        (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
          (isOpenBoundedConvexDomain_cubeSetAt y n)) w hgradL2zero
    have hzeroSc : MemScalarL2 (cubeSetAt y n) (0 : Vec d → ℝ) := MemLp.zero
    have haeFun : w.toH1Function.toFun =ᵐ[volume.restrict (cubeSetAt y n)] 0 :=
      (toScalarL2_eq_toScalarL2_iff w.toH1Function.memL2 hzeroSc).1 hscalar
    filter_upwards [haeFun] with x hx
    have hdiff := hwf x
    rw [hx] at hdiff
    simp only [Pi.zero_apply] at hdiff
    exact sub_eq_zero.1 hdiff.symm

/-! ### The two families of Section 5 -/

/-- The comparator background is elliptic on the cube, with both constants
`σ_n`. -/
theorem isEllipticFieldOn_comparator (M : ABKModel d) (n : ℤ) (y : Vec d) :
    IsEllipticFieldOn (Annealed.sigmaBar M n : ℝ) (Annealed.sigmaBar M n : ℝ)
      (cubeSetAt y n) (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) :=
  Section4.Provider.Schauder.isEllipticFieldOn_smul_one (Provider.Orlicz.sigmaBar_pos M n)
    (measurableSet_cubeSetAt y n)

/-- The cutoff coefficient field is elliptic on the cube, with lower constant
the molecular diffusivity. -/
theorem exists_isEllipticFieldOn_cutoff (M : ABKModel d) (m n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) :
    ∃ Lam : ℝ, IsEllipticFieldOn M.nu Lam (cubeSetAt y n)
      ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) := by
  obtain ⟨ell, hell⟩ := exists_cubeSetAt_subset_openCubeSet y n
  exact ⟨_, Cutoff.isEllipticFieldOn_coefficientCutoff_of_entry_bound M m omega
    (measurableSet_cubeSetAt y n) (M.nu + Cutoff.cutoffLocalControl ell m omega)
    (fun x hx i j => Cutoff.abs_coefficientCutoff_entry_le M.nu M.nu_pos.le ell m omega
      (hell hx) i j)⟩

/-- Two comparator solutions agree almost everywhere on the cube. -/
theorem isDirichletSolutionAt_ae_unique_comparator (M : ABKModel d) (n : ℤ) (y : Vec d)
    {u u' : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    (hu : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n u g)
    (hu' : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n u' g) :
    u.grad =ᵐ[volume.restrict (cubeSetAt y n)] u'.grad ∧
      u.toFun =ᵐ[volume.restrict (cubeSetAt y n)] u'.toFun :=
  isDirichletSolutionAt_ae_unique (Provider.Orlicz.dim_pos_of_model M)
    (isEllipticFieldOn_comparator M n y) hu hu'

/-- Two rough-field solutions agree almost everywhere on the cube. -/
theorem isDirichletSolutionAt_ae_unique_cutoff (M : ABKModel d) (m n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {u u' : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n u g)
    (hu' : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField)
      y n u' g) :
    u.grad =ᵐ[volume.restrict (cubeSetAt y n)] u'.grad ∧
      u.toFun =ᵐ[volume.restrict (cubeSetAt y n)] u'.toFun := by
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_cutoff M m n y omega
  exact isDirichletSolutionAt_ae_unique (Provider.Orlicz.dim_pos_of_model M) hEll hu hu'

end

end Algsuperdiff.Section5.Support
