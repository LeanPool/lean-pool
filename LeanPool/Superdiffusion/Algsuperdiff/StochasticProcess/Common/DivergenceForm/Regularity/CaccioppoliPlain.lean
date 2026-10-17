/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.CaccioppoliAbsorbed

/-!
# CaccioppoliPlain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Caccioppoli inequality at level zero

The De Giorgi cutoff estimates of `CaccioppoliIdentity.lean`, `CaccioppoliInequality.lean` and
`CaccioppoliAbsorbed.lean` are stated for the positive part of a solution above a level.  The
statement below is the same estimate at the solution itself, with no truncation: testing
`-div (a grad u) = g` against `eta^2 u` and absorbing half of the elliptic energy leaves
  `lam / 2 * ∫ eta^2 |grad u|^2 ≤ ∫ g eta^2 u + (2 Lam^2 / lam) * ∫ u^2 |grad eta|^2`.

The forcing term is kept signed, because the intended consumer has a nonpositive forcing (the
difference of two Dirichlet resolvents of the same datum on two nested cubes solves the
homogeneous shifted equation, whose forcing is a negative multiple of the solution).  The right
side is then quadratic in the solution, which turns the estimate into a Cauchy estimate.
-/

noncomputable section

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

/-- **The Caccioppoli inequality at level zero.**  Half of the elliptic energy is absorbed and
the forcing pairing is kept signed. -/
theorem cutoff_energy_absorbed_plain
    {a : CoeffField d} {g : Vec d → ℝ} {u : H1Function U}
    (hsol : IsScalarForcedWeakSolution a U g u)
    (hU : IsOpenBoundedConvexDomain U) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (eta : Vec d → ℝ) (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) (hetaU : tsupport eta ⊆ U) :
    lam / 2 * ∫ x in U, eta x ^ 2 * vecNormSq (u.grad x) ∂volume ≤
      (∫ x in U, g x * (eta x ^ 2 * u.toFun x) ∂volume) +
        (2 * Lam ^ 2 / lam) * ∫ x in U,
          u.toFun x ^ 2 * vecNormSq (fun i ↦ (fderiv ℝ eta x) (basisVec i)) ∂volume := by
  let mu := volumeMeasureOn U
  let de : Vec d → Vec d := fun x i ↦ (fderiv ℝ eta x) (basisVec i)
  let phi : Vec d → ℝ := fun x ↦ eta x ^ 2
  let q : Vec d → Vec d := fun x ↦ phi x • u.grad x
  let r : Vec d → Vec d := fun x ↦ (2 * eta x * u.toFun x) • de x
  have hphi : ContDiff ℝ (⊤ : ℕ∞) phi := by
    simpa only [phi, pow_two] using heta.mul heta
  have hphiCompact : HasCompactSupport phi := by
    simpa only [phi, pow_two] using! hetaCompact.mul_left (f := eta)
  have hphiU : tsupport phi ⊆ U := by
    rw [show phi = eta * eta by funext x; simp only [phi, pow_two, Pi.mul_apply]]
    exact (tsupport_mul_subset_left (f := eta) (g := eta)).trans hetaU
  have hetaTop : MemLp eta ∞ mu :=
    (heta.continuous.memLp_of_hasCompactSupport hetaCompact).restrict U
  have hphiTop : MemLp phi ∞ mu :=
    (hphi.continuous.memLp_of_hasCompactSupport hphiCompact).restrict U
  have hetaZ : MemVectorL2 U (fun x ↦ eta x • u.grad x) := by
    simpa only [MemVectorL2, volumeMeasureOn, Pi.smul_apply, smul_eq_mul, mul_comm] using!
      (MemLp.of_eval fun i : Fin d ↦
        (memScalarL2_coord_of_memVectorL2 u.grad_memVectorL2 i).fun_mul hetaTop)
  have hq : MemVectorL2 U q := by
    simpa only [MemVectorL2, volumeMeasureOn, q, Pi.smul_apply, smul_eq_mul, mul_comm] using!
      (MemLp.of_eval fun i : Fin d ↦
        (memScalarL2_coord_of_memVectorL2 u.grad_memVectorL2 i).fun_mul hphiTop)
  -- the localized product with the linear cutoff produces the `L²` control of `u • grad eta`
  have hpde : MemVectorL2 U (fun x ↦ u.toFun x • de x) := by
    have hbase : MemVectorL2 U
        (fun x ↦ (u.mulContDiffHasCompactSupport heta hetaCompact).grad x - eta x • u.grad x) :=
      (u.mulContDiffHasCompactSupport heta hetaCompact).grad_memVectorL2.sub hetaZ
    apply hbase.ae_eq
    filter_upwards with x
    rw [H1Function.mulContDiffHasCompactSupport_grad]
    funext i
    change eta x * u.grad x i + u.toFun x * (fderiv ℝ eta x) (basisVec i) -
        eta x * u.grad x i = u.toFun x * de x i
    simp only [de]
    ring
  have hr : MemVectorL2 U r := by
    have hetaPde : MemVectorL2 U (fun x ↦ eta x • (u.toFun x • de x)) := by
      simpa only [MemVectorL2, volumeMeasureOn, Pi.smul_apply, smul_eq_mul, mul_comm] using!
        (MemLp.of_eval fun i : Fin d ↦
          (memScalarL2_coord_of_memVectorL2 hpde i).fun_mul hetaTop)
    have htwo : MemVectorL2 U (fun x ↦ (2 : ℝ) • (eta x • (u.toFun x • de x))) :=
      hetaPde.const_smul (2 : ℝ)
    apply htwo.ae_eq
    filter_upwards with x
    funext i
    simp only [r, Pi.smul_apply, smul_eq_mul]
    ring
  have hflux : MemVectorL2 U (fun x ↦ matVecMul (a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have henergyInt : Integrable (fun x ↦ vecDot (matVecMul (a x) (u.grad x)) (q x)) mu :=
    integrableOn_vecDot_of_memVectorL2 hflux hq
  have hcrossInt : Integrable (fun x ↦ vecDot (matVecMul (a x) (u.grad x)) (r x)) mu :=
    integrableOn_vecDot_of_memVectorL2 hflux hr
  have htargetInt : Integrable (fun x ↦ phi x * vecNormSq (u.grad x)) mu := by
    apply (integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hq).congr
    filter_upwards with x
    simp only [vecNormSq, vecDot, q, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hcutInt : Integrable (fun x ↦ u.toFun x ^ 2 * vecNormSq (de x)) mu := by
    apply (integrableOn_vecDot_of_memVectorL2 hpde hpde).congr
    filter_upwards with x
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- the cutoff testing identity
  have hid : (∫ x, vecDot (matVecMul (a x) (u.grad x)) (q x) ∂mu) +
      ∫ x, vecDot (matVecMul (a x) (u.grad x)) (r x) ∂mu =
      ∫ x, g x * (phi x * u.toFun x) ∂mu := by
    have hweak := hsol.2 (localizedProductToH10 hU u hphi hphiCompact hphiU)
    have hgrad : ∀ᵐ x ∂mu,
        (localizedProductToH10 hU u hphi hphiCompact hphiU).toH1Function.grad x =
          q x + r x := by
      filter_upwards [localizedProductToH10_grad_ae hU u hphi hphiCompact hphiU] with x hx
      rw [hx, H1Function.mulContDiffHasCompactSupport_grad]
      funext i
      change phi x * u.grad x i + u.toFun x * (fderiv ℝ phi x) (basisVec i) = _
      have hetadiff : DifferentiableAt ℝ eta x := heta.differentiable (by simp) x
      rw [show phi = eta * eta by funext y; simp only [phi, pow_two, Pi.mul_apply]]
      rw [fderiv_mul hetadiff hetadiff]
      simp only [q, r, de, phi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
        add_apply, smul_apply]
      ring
    rw [← integral_add henergyInt hcrossInt]
    have hleft : (∫ x, (vecDot (matVecMul (a x) (u.grad x)) (q x) +
        vecDot (matVecMul (a x) (u.grad x)) (r x)) ∂mu) =
        ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          ((localizedProductToH10 hU u hphi hphiCompact hphiU).toH1Function.grad x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [hgrad] with x hx
      rw [hx]
      simp only [vecDot, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hleft, hweak, localizedProductToH10_toFun]
  -- the elliptic lower bound
  have hlower : lam * ∫ x, phi x * vecNormSq (u.grad x) ∂mu ≤
      ∫ x, vecDot (matVecMul (a x) (u.grad x)) (q x) ∂mu := by
    rw [← integral_const_mul]
    refine integral_mono_ae (htargetInt.const_mul lam) henergyInt ?_
    have hmem : ∀ᵐ x ∂mu, x ∈ U :=
      (ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun _ hx ↦ hx)
    filter_upwards [hmem] with x hx
    have hquad := lowerBound_symmPart_of_isEllipticMatrix (hEll.2 x hx) (u.grad x)
    rw [vecDot_matVecMul_symmPart] at hquad
    simp only [q, phi]
    rw [vecDot_smul_right, vecDot_comm]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hquad (sq_nonneg (eta x))
  -- the absorbed cross term
  have hpoint : ∀ᵐ x ∂mu,
      |vecDot (matVecMul (a x) (u.grad x)) (r x)| ≤
        lam / 2 * (phi x * vecNormSq (u.grad x)) +
          (2 * Lam ^ 2 / lam) * (u.toFun x ^ 2 * vecNormSq (de x)) := by
    have hmem : ∀ᵐ x ∂mu, x ∈ U :=
      (ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun _ hx ↦ hx)
    filter_upwards [hmem] with x hx
    have hyoung := cutoff_flux_young (lam := lam) (Lam := Lam) (e := eta x)
      (p := u.toFun x) (A := a x) (u.grad x) (de x) (hEll.2 x hx)
    simpa only [r, phi, vecDot_smul_right] using hyoung
  have hcrossBound : -∫ x, vecDot (matVecMul (a x) (u.grad x)) (r x) ∂mu ≤
      lam / 2 * ∫ x, phi x * vecNormSq (u.grad x) ∂mu +
        (2 * Lam ^ 2 / lam) * ∫ x, u.toFun x ^ 2 * vecNormSq (de x) ∂mu := by
    have habs : ∫ x, |vecDot (matVecMul (a x) (u.grad x)) (r x)| ∂mu ≤
        lam / 2 * ∫ x, phi x * vecNormSq (u.grad x) ∂mu +
          (2 * Lam ^ 2 / lam) * ∫ x, u.toFun x ^ 2 * vecNormSq (de x) ∂mu := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (htargetInt.const_mul _) (hcutInt.const_mul _)]
      exact integral_mono_ae hcrossInt.abs
        ((htargetInt.const_mul _).add (hcutInt.const_mul _)) hpoint
    exact ((neg_le_abs _).trans abs_integral_le_integral_abs).trans habs
  have hgoal : lam * ∫ x, phi x * vecNormSq (u.grad x) ∂mu ≤
      (∫ x, g x * (phi x * u.toFun x) ∂mu) +
        (lam / 2 * ∫ x, phi x * vecNormSq (u.grad x) ∂mu +
          (2 * Lam ^ 2 / lam) * ∫ x, u.toFun x ^ 2 * vecNormSq (de x) ∂mu) := by
    have := hlower
    linarith only [hlower, hcrossBound, hid]
  have hfinal : lam / 2 * ∫ x, phi x * vecNormSq (u.grad x) ∂mu ≤
      (∫ x, g x * (phi x * u.toFun x) ∂mu) +
        (2 * Lam ^ 2 / lam) * ∫ x, u.toFun x ^ 2 * vecNormSq (de x) ∂mu := by
    linarith only [hgoal]
  exact hfinal

end DivergenceFormProcess.Form
