/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Quasiconvex
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.External.BaernsteinMontgomerySmith.RemarkB
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.External.Lehto.LowerBound
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.L2
import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Quasiconvex.Domain

/-!
# Corollary 2, second part: the norm of the Beurling–Ahlfors transform

**Corollary 2** (`cor:Bp-BA`), second assertion `(eq:BA-sharp-norm)`:
`‖𝒮‖_{L^p (ℂ; ℂ) → L^p (ℂ; ℂ)} = p* − 1`, which is `(p − 1)⁻¹` for `1 < p ≤ 2` and `p − 1` for
`2 ≤ p < ∞` (`pStar_sub_one_of_le_two`, `pStar_sub_one_of_two_le`).

The paper derives it from Theorem 1 "by the arguments in [Baernstein1997a] (see also
[Guerra2026b] for further details)" (TeX line 301), with the lower bound from [Lehto1965] (TeX
line 320). The upper bound `beurlingNorm_le` follows these arguments, which are planar: those of
Baernstein–Montgomery-Smith (arXiv:math/9709215v2, §1: "Conjecture 2 ⇒ Conjecture 3" and remark
(b)) and of Guerra (arXiv:2608.23388, proof of the corollary labelled `cor:beurling-lp` in its
TeX, with the cut-offs of the proof of `cor:beurling`).

1. Quasiconvexity at `0` with compactly supported test maps. The first assertion of Corollary 2,
   for Lipschitz periodic maps (`corollary2_lipschitz`), is the quasiconvexity of `B_p` in the
   sense of the package `CalculusOfVariations` (`quasiconvex_burkholderB`, through
   `CalculusOfVariations.quasiconvexAtOn_iff_periodic`, Dacorogna, Prop. 5.13), hence on every
   bounded set (`CalculusOfVariations.quasiconvexAtOn_of_unitCube`, Dacorogna, Prop. 5.11). For
   `u : ℂ → ℂ` smooth with compact support and `φ = (Re u, Im u) : ℝ² → ℝ²`
   (`Agazzi.Corollary2Norm.toRealMap u`), at `A = 0` and on a ball that contains the support of
   `φ`, it gives `∫_{ℝ²} B_p (D φ) ≥ B_p (0) |Ω| = 0`
   (`Agazzi.Corollary2Norm.integral_burkholderB_jacobian_nonneg`). These are the test maps of
   Guerra's theorem, compactly supported maps of the plane; Baernstein–Montgomery-Smith state their
   conjectures for `f ∈ W_hom^{1,p} (ℂ)`, which contains them.
2. Baernstein–Montgomery-Smith's Conjecture 2. `a₊ (D φ) = ∂u` and `a₋ (D φ) = ∂_zbar u`
   (`Agazzi.Corollary2Norm.conformalPart_jacobian_toRealMap`,
   `Agazzi.Corollary2Norm.anticonformalPart_jacobian_toRealMap`; their §5:
   `α (∇f) = (∂f, ∂_zbar f)`), and `α_p B_p (A) = Φ_p (a₊, a₋)` for `p < 2`, `Φ_p (a₋, a₊)` for `p
   ≥ 2`,
   with `α_p > 0`. Hence `∫_ℂ Φ_p (∂u, ∂_zbar u) ≥ 0` for `p < 2` and `∫_ℂ Φ_p (∂_zbar u, ∂u) ≥ 0`
   for
   `p ≥ 2` (`Agazzi.Corollary2Norm.integral_phi_dz_dzbar_nonneg`,
   `Agazzi.Corollary2Norm.integral_phi_dzbar_dz_nonneg`).
3. Conjecture 3, by Burkholder's inequality `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p`
   (`External.BaernsteinMontgomerySmith.phi_le`): for `p ≥ 2`, `∫ |∂u|^p ≤ (p* − 1)^p ∫ |∂_zbar
   u|^p`;
   for `p < 2`, `∫ |∂_zbar u|^p ≤ (p* − 1)^p ∫ |∂u|^p`, which, applied to `ū` (`∂ū = conj (∂_zbar
   u)`,
   `∂_zbarū = conj (∂u)`: the interchangeability of `∂f` and `∂_zbar f` of
   Baernstein–Montgomery-Smith), is
   again `∫ |∂u|^p ≤ (p* − 1)^p ∫ |∂_zbar u|^p`, for every `1 < p < ∞`
   (`Agazzi.Corollary2Norm.integral_norm_dz_rpow_le`).
4. Remark (b) of Baernstein–Montgomery-Smith, with Guerra's details: the norm of `𝒮` on `L^p (ℂ)`
   is at most the constant of `∫ |∂u|^p ≤ C^p ∫ |∂_zbar u|^p` on `C_c^∞`
   (`External.BaernsteinMontgomerySmith.remark_b`). Its proof is general harmonic analysis, in the
   package `HarmonicAnalysis`
   (`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`): density, a potential,
   the cut-offs `η_R` of Guerra's proof, and the limit. The package follows Guerra's proof, with
   Guerra's dense class `C_c^∞`, in the gradient case: the Cauchy transform
   `f (z) = (1/π) ∫ g (w) / (z − w) dw` of `g`, with `∂_zbar f = g` and `∂f = 𝒮g`, in place of the
   logarithmic potential of a real `h`, a departure that the norm on complex `L^p` forces.

Steps 2 and 3 are Baernstein–Montgomery-Smith's passage from their Conjecture 2 to their
Conjecture 3; their passage from Conjecture 1 to Conjecture 2, through the Mellin identities, is
the first assertion of Corollary 2 (`corollary2_lipschitz`), which step 1 brings to the plane.
Step 4 is the argument of their remark (b), as Guerra details it. No step uses the torus beyond
Corollary 2 itself.

A shorter proof of the upper bound, through the torus and transference, is kept beside this one
and not used by `corollary2_norm` (`Agazzi.beurlingNorm_le_of_torus`, in
`Agazzi.Corollary2.NormTorus`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal ComplexConjugate ContDiff

namespace Agazzi

namespace Corollary2Norm

open External.BaernsteinMontgomerySmith (Phi alpha phi_le continuous_dz_of_contDiff
  continuous_dzbar_of_contDiff hasCompactSupport_dz hasCompactSupport_dzbar)

/-! ### The Burkholder integrand and the function `Φ_p` of Baernstein–Montgomery-Smith -/

/-- The `p*` of Baernstein–Montgomery-Smith is the paper's. -/
theorem bms_pStar_eq (p : ℝ) : External.BaernsteinMontgomerySmith.pStar p = pStar p := rfl

/-- `p ≤ p*`. -/
theorem le_pStar (p : ℝ) : p ≤ pStar p := le_max_left _ _

/-- `α_p = p (1 − 1/p*)^{p−1} > 0` for `1 < p`. -/
theorem alpha_pos {p : ℝ} (hp : 1 < p) : 0 < alpha p := by
  exact External.BaernsteinMontgomerySmith.alpha_pos hp

/-- `B_p (0) = 0`. -/
theorem burkholderB_zero (p : ℝ) : burkholderB p 0 = 0 := by
  have h1 : conformalPart 0 = 0 := by apply Complex.ext <;> simp [conformalPart]
  have h2 : anticonformalPart 0 = 0 := by apply Complex.ext <;> simp [anticonformalPart]
  simp [burkholderB, h1, h2]

/-- `α_p B_p (A) = Φ_p (a₊, a₋)` for `p < 2`. -/
theorem alpha_mul_burkholderB_of_lt_two {p : ℝ} (hp2 : p < 2) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    alpha p * burkholderB p A = Phi p (conformalPart A) (anticonformalPart A) := by
  rw [burkholderB, ite_eq_left hp2, Phi, bms_pStar_eq, mul_assoc]

/-- `α_p B_p (A) = Φ_p (a₋, a₊)` for `p ≥ 2`. -/
theorem alpha_mul_burkholderB_of_two_le {p : ℝ} (hp2 : 2 ≤ p) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    alpha p * burkholderB p A = Phi p (anticonformalPart A) (conformalPart A) := by
  rw [burkholderB, ite_eq_right (not_lt.2 hp2), Phi, bms_pStar_eq, mul_assoc,
    add_comm ‖anticonformalPart A‖]

/-! ### The Wirtinger derivatives and the jacobian -/

/-- `ℝ² → ℂ`, `x ↦ x₀ + i x₁`, as a continuous linear equivalence: the inverse of
`Complex.measurableEquivPi`. -/
def planeEquiv : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm

/-- `planeEquiv` is the inverse of `Complex.measurableEquivPi`. -/
theorem planeEquiv_apply (x : Fin 2 → ℝ) : planeEquiv x = Complex.measurableEquivPi.symm x := rfl

/-- `planeEquiv e₀ = 1`. -/
theorem planeEquiv_single_zero : planeEquiv (Pi.single 0 1) = 1 := by
  rw [planeEquiv_apply, Complex.measurableEquivPi_symm_apply]
  simp

/-- `planeEquiv e₁ = i`. -/
theorem planeEquiv_single_one : planeEquiv (Pi.single 1 1) = Complex.I := by
  rw [planeEquiv_apply, Complex.measurableEquivPi_symm_apply]
  simp

/-- The map `φ_u = (Re u, Im u) : ℝ² → ℝ²` of `u : ℂ → ℂ`, with `ℂ ≅ ℝ²`, `x + iy ↦ (x, y)`. -/
def toRealMap (u : ℂ → ℂ) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(u (planeEquiv y)).re, (u (planeEquiv y)).im]

/-- `φ_u` is as smooth as `u`. -/
theorem contDiff_toRealMap {n : WithTop ℕ∞} {u : ℂ → ℂ} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (toRealMap u) := by
  have h : ContDiff ℝ n fun y => u (planeEquiv y) := hu.comp planeEquiv.contDiff
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simp only [toRealMap, Fin.zero_eta, Matrix.cons_val_zero]
    exact Complex.reCLM.contDiff.comp h
  · simp only [toRealMap, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact Complex.imCLM.contDiff.comp h

/-- `φ_u` has compact support if `u` has. -/
theorem hasCompactSupport_toRealMap {u : ℂ → ℂ} (hu : HasCompactSupport u) :
    HasCompactSupport (toRealMap u) := by
  have h : HasCompactSupport fun y => u (planeEquiv y) :=
    hu.comp_homeomorph planeEquiv.toHomeomorph
  refine h.mono fun y hy => ?_
  simp only [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by simp [toRealMap, h0])

private lemma fderiv_re_comp {u : ℂ → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u (planeEquiv x)) (v : Fin 2 → ℝ) :
    fderiv ℝ (fun y => (u (planeEquiv y)).re) x v =
      (fderiv ℝ u (planeEquiv x) (planeEquiv v)).re := by
  have h := (Complex.reCLM.hasFDerivAt.comp x
    (hu.hasFDerivAt.comp x planeEquiv.hasFDerivAt)).fderiv
  have e : (fun y => (u (planeEquiv y)).re) = Complex.reCLM ∘ u ∘ planeEquiv := rfl
  rw [e, h]
  rfl

private lemma fderiv_im_comp {u : ℂ → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u (planeEquiv x)) (v : Fin 2 → ℝ) :
    fderiv ℝ (fun y => (u (planeEquiv y)).im) x v =
      (fderiv ℝ u (planeEquiv x) (planeEquiv v)).im := by
  have h := (Complex.imCLM.hasFDerivAt.comp x
    (hu.hasFDerivAt.comp x planeEquiv.hasFDerivAt)).fderiv
  have e : (fun y => (u (planeEquiv y)).im) = Complex.imCLM ∘ u ∘ planeEquiv := rfl
  rw [e, h]
  rfl

private lemma jacobian_toRealMap {u : ℂ → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u (planeEquiv x)) (j : Fin 2) :
    jacobian (toRealMap u) x 0 j =
        (fderiv ℝ u (planeEquiv x) (planeEquiv (Pi.single j 1))).re ∧
      jacobian (toRealMap u) x 1 j =
        (fderiv ℝ u (planeEquiv x) (planeEquiv (Pi.single j 1))).im := by
  have h0 : (fun y => toRealMap u y 0) = fun y => (u (planeEquiv y)).re := by
    funext y; simp [toRealMap]
  have h1 : (fun y => toRealMap u y 1) = fun y => (u (planeEquiv y)).im := by
    funext y; simp [toRealMap]
  simp only [jacobian, Matrix.of_apply, h0, h1]
  exact ⟨fderiv_re_comp hu _, fderiv_im_comp hu _⟩

/-- `a₊ (D φ_u) = ∂u`, at a point where `u` is differentiable (Baernstein–Montgomery-Smith, §5:
`α (∇f) = (∂f, ∂_zbar f)`). -/
theorem conformalPart_jacobian_toRealMap {u : ℂ → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u (planeEquiv x)) :
    conformalPart (jacobian (toRealMap u) x) = HarmonicAnalysis.dz u (planeEquiv x) := by
  obtain ⟨a0, b0⟩ := jacobian_toRealMap hu 0
  obtain ⟨a1, b1⟩ := jacobian_toRealMap hu 1
  rw [planeEquiv_single_zero] at a0 b0
  rw [planeEquiv_single_one] at a1 b1
  apply Complex.ext <;>
    simp [conformalPart, HarmonicAnalysis.dz, a0, b0, a1, b1, Complex.mul_re,
      Complex.mul_im] <;> ring

/-- `a₋ (D φ_u) = ∂_zbar u`, at a point where `u` is differentiable. -/
theorem anticonformalPart_jacobian_toRealMap {u : ℂ → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u (planeEquiv x)) :
    anticonformalPart (jacobian (toRealMap u) x) = HarmonicAnalysis.dzbar u (planeEquiv x) := by
  obtain ⟨a0, b0⟩ := jacobian_toRealMap hu 0
  obtain ⟨a1, b1⟩ := jacobian_toRealMap hu 1
  rw [planeEquiv_single_zero] at a0 b0
  rw [planeEquiv_single_one] at a1 b1
  apply Complex.ext <;>
    simp [anticonformalPart, HarmonicAnalysis.dzbar, a0, b0, a1, b1, Complex.mul_re,
      Complex.mul_im] <;> ring

/-- `x ↦ D φ (x)` is continuous for a `C¹` map `φ`. -/
theorem continuous_jacobian {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (jacobian φ) := by
  refine continuous_matrix fun i j => ?_
  have hi : ContDiff ℝ 1 fun y => φ y i := contDiff_pi.1 hφ i
  exact (hi.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- `D φ (x) = 0` outside the topological support of `φ`. -/
theorem jacobian_eq_zero_of_notMem_tsupport {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} {x : Fin 2 → ℝ}
    (hx : x ∉ tsupport φ) : jacobian φ x = 0 := by
  ext i j
  have hi : x ∉ tsupport (fderiv ℝ fun y => φ y i) := fun h =>
    hx ((tsupport_fderiv_subset ℝ).trans
      (tsupport_comp_subset (g := fun v : Fin 2 → ℝ => v i) rfl φ) h)
  simp [jacobian, image_eq_zero_of_notMem_tsupport hi]

/-! ### Step 1: quasiconvexity at `0` with compactly supported test maps -/

/-- Step 1: `∫_{ℝ²} B_p (D φ_u) ≥ 0` for `u : ℂ → ℂ` smooth with compact support and `1 < p`:
the quasiconvexity of `B_p` (`quasiconvex_burkholderB`, from Corollary 2 for Lipschitz periodic
maps) on a ball that contains the support of `φ_u`
(`CalculusOfVariations.quasiconvexAtOn_of_unitCube`), at `A = 0`, with `B_p (0) = 0`. -/
theorem integral_burkholderB_jacobian_nonneg {p : ℝ} (hp : 1 < p) {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    0 ≤ ∫ x, burkholderB p (jacobian (toRealMap u) x) := by
  have hφ : ContDiff ℝ ∞ (toRealMap u) := contDiff_toRealMap hu
  have hφc : HasCompactSupport (toRealMap u) := hasCompactSupport_toRealMap huc
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_ball (0 : Fin 2 → ℝ)
  have hB := continuous_burkholderB hp
  have hF0 : ∀ x ∉ tsupport (toRealMap u), burkholderB p (jacobian (toRealMap u) x) = 0 :=
    fun x hx => by rw [jacobian_eq_zero_of_notMem_tsupport hx, burkholderB_zero]
  have hFi : Integrable fun x => burkholderB p (jacobian (toRealMap u) x) :=
    (hB.comp (continuous_jacobian (hφ.of_le (by simp)))).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hφc hF0)
  have hq : CalculusOfVariations.QuasiconvexAtOn (ball 0 R) (burkholderB p) 0 :=
    CalculusOfVariations.quasiconvexAtOn_of_unitCube hB.measurable
      (CalculusOfVariations.isLocallyBounded_of_continuous hB) isBounded_ball measurableSet_ball
      (quasiconvex_burkholderB hp 0)
  have h := hq (toRealMap u) K hK
    (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hR h))
    (by simp only [zero_add]; exact hFi.integrableOn)
  simp only [burkholderB_zero, mul_zero, zero_add, ← jacobian_eq_grad] at h
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    hF0 x fun h' => hx (hR h')] at h

/-! ### Step 2: Baernstein–Montgomery-Smith's Conjecture 2 -/

/-- `∫_{ℝ²} G (x₀ + i x₁) dx = ∫_ℂ G`. -/
theorem integral_planeEquiv (G : ℂ → ℝ) : ∫ x, G (planeEquiv x) = ∫ z, G z :=
  (MeasurePreserving.symm _ Complex.volume_preserving_equiv_pi).integral_comp' G

/-- Step 2 for `1 < p < 2`: `∫_ℂ Φ_p (∂u, ∂_zbar u) ≥ 0` for `u` smooth with compact support
(Baernstein–Montgomery-Smith's Conjecture 2). -/
theorem integral_phi_dz_dzbar_nonneg {p : ℝ} (hp : 1 < p) (hp2 : p < 2) {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    0 ≤ ∫ z, Phi p (HarmonicAnalysis.dz u z) (HarmonicAnalysis.dzbar u z) := by
  have hd : ∀ z, DifferentiableAt ℝ u z := hu.differentiable (by simp)
  rw [← integral_planeEquiv fun z => Phi p (HarmonicAnalysis.dz u z) (HarmonicAnalysis.dzbar u z)]
  have e : ∀ x, Phi p (HarmonicAnalysis.dz u (planeEquiv x))
      (HarmonicAnalysis.dzbar u (planeEquiv x)) =
        alpha p * burkholderB p (jacobian (toRealMap u) x) := fun x => by
    rw [alpha_mul_burkholderB_of_lt_two hp2, conformalPart_jacobian_toRealMap (hd _),
      anticonformalPart_jacobian_toRealMap (hd _)]
  simp_rw [e]
  rw [integral_const_mul]
  exact mul_nonneg (alpha_pos hp).le (integral_burkholderB_jacobian_nonneg hp hu huc)

/-- Step 2 for `2 ≤ p`: `∫_ℂ Φ_p (∂_zbar u, ∂u) ≥ 0` for `u` smooth with compact support. -/
theorem integral_phi_dzbar_dz_nonneg {p : ℝ} (hp2 : 2 ≤ p) {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    0 ≤ ∫ z, Phi p (HarmonicAnalysis.dzbar u z) (HarmonicAnalysis.dz u z) := by
  have hp : 1 < p := by linarith
  have hd : ∀ z, DifferentiableAt ℝ u z := hu.differentiable (by simp)
  rw [← integral_planeEquiv fun z => Phi p (HarmonicAnalysis.dzbar u z) (HarmonicAnalysis.dz u z)]
  have e : ∀ x, Phi p (HarmonicAnalysis.dzbar u (planeEquiv x))
      (HarmonicAnalysis.dz u (planeEquiv x)) =
        alpha p * burkholderB p (jacobian (toRealMap u) x) := fun x => by
    rw [alpha_mul_burkholderB_of_two_le hp2, conformalPart_jacobian_toRealMap (hd _),
      anticonformalPart_jacobian_toRealMap (hd _)]
  simp_rw [e]
  rw [integral_const_mul]
  exact mul_nonneg (alpha_pos hp).le (integral_burkholderB_jacobian_nonneg hp hu huc)

/-! ### Step 3: Conjecture 3, `‖∂u‖_p ≤ (p* − 1) ‖∂_zbar u‖_p` -/

/-- From `0 ≤ ∫ Φ_p (f, g)` and Burkholder's inequality `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p`:
`∫ |g|^p ≤ (p* − 1)^p ∫ |f|^p`, for continuous `f`, `g` with compact support. -/
theorem integral_rpow_le_of_integral_phi_nonneg {p : ℝ} (hp : 1 < p) {f g : ℂ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g) (h : 0 ≤ ∫ z, Phi p (f z) (g z)) :
    ∫ z, ‖g z‖ ^ p ≤ (pStar p - 1) ^ p * ∫ z, ‖f z‖ ^ p := by
  have hp0 : 0 < p := by linarith
  have hpow : ∀ k : ℂ → ℂ, Continuous k → HasCompactSupport k →
      Integrable fun z => ‖k z‖ ^ p := fun k hk hkc =>
    (hk.norm.rpow_const fun _ => Or.inr hp0.le).integrable_of_hasCompactSupport
      (hkc.comp_left (g := fun t : ℂ => ‖t‖ ^ p) (by simp [Real.zero_rpow hp0.ne']))
  have hF := hpow f hf hfc
  have hG := hpow g hg hgc
  have hPhi : Integrable fun z => Phi p (f z) (g z) := by
    refine Continuous.integrable_of_hasCompactSupport ?_
      (HasCompactSupport.intro (hfc.isCompact.union hgc.isCompact) fun z hz => ?_)
    · unfold Phi
      exact (continuous_const.mul ((continuous_const.mul hf.norm).sub hg.norm)).mul
        ((hf.norm.add hg.norm).rpow_const fun _ => Or.inr (by linarith))
    · rw [Set.mem_union, not_or] at hz
      simp [Phi, image_eq_zero_of_notMem_tsupport hz.1, image_eq_zero_of_notMem_tsupport hz.2]
  have hR : Integrable fun z => (pStar p - 1) ^ p * ‖f z‖ ^ p - ‖g z‖ ^ p :=
    (hF.const_mul _).sub hG
  have hmono := integral_mono hPhi hR fun z => by
    simpa only [bms_pStar_eq] using phi_le hp (f z) (g z)
  rw [integral_sub (hF.const_mul _) hG, integral_const_mul] at hmono
  linarith

/-- Step 3: `∫ |∂u|^p ≤ (p* − 1)^p ∫ |∂_zbar u|^p` for `u` smooth with compact support and `1 < p`.
For `p < 2`, the inequality of step 2 for `p < 2` applied to `ū`, by the interchangeability of
`∂` and `∂_zbar` (Baernstein–Montgomery-Smith, §1: `∂ū = conj (∂_zbar u)`, `∂_zbarū = conj (∂u)`).
-/
theorem integral_norm_dz_rpow_le {p : ℝ} (hp : 1 < p) {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) :
    ∫ z, ‖HarmonicAnalysis.dz u z‖ ^ p ≤
      (pStar p - 1) ^ p * ∫ z, ‖HarmonicAnalysis.dzbar u z‖ ^ p := by
  rcases lt_or_ge p 2 with hp2 | hp2
  · have hv : ContDiff ℝ ∞ fun z => conj (u z) := Complex.conjCLE.contDiff.comp hu
    have hvc : HasCompactSupport fun z => conj (u z) :=
      huc.comp_left (g := starRingEnd ℂ) (map_zero _)
    have hv1 : ContDiff ℝ 1 fun z => conj (u z) := hv.of_le (by simp)
    have h := integral_rpow_le_of_integral_phi_nonneg hp (continuous_dz_of_contDiff hv1)
      (continuous_dzbar_of_contDiff hv1) (hasCompactSupport_dz hvc) (hasCompactSupport_dzbar hvc)
      (integral_phi_dz_dzbar_nonneg hp hp2 hv hvc)
    simpa only [HarmonicAnalysis.dz_conj, HarmonicAnalysis.dzbar_conj, Complex.norm_conj]
      using h
  · have hu1 : ContDiff ℝ 1 u := hu.of_le (by simp)
    exact integral_rpow_le_of_integral_phi_nonneg hp (continuous_dzbar_of_contDiff hu1)
      (continuous_dz_of_contDiff hu1) (hasCompactSupport_dzbar huc) (hasCompactSupport_dz huc)
      (integral_phi_dzbar_dz_nonneg hp2 hu huc)

end Corollary2Norm

/-- The upper bound in `(eq:BA-sharp-norm)`: `‖𝒮‖_p ≤ p* − 1` for `1 < p < ∞`.

The argument of Baernstein–Montgomery-Smith (§1, Conjectures 2 and 3 and remark (b)), with
Guerra's details for the passage to `L^p (ℂ)`: Corollary 2 at `A = 0`, as quasiconvexity with
compactly supported test maps, and Burkholder's inequality give
`∫ |∂u|^p ≤ (p* − 1)^p ∫ |∂_zbar u|^p` for `u ∈ C_c^∞ (ℂ)`
(`Corollary2Norm.integral_norm_dz_rpow_le`;
for `p < 2` through `u ↦ ū`); remark (b) (`External.BaernsteinMontgomerySmith.remark_b`, proved
in the package `HarmonicAnalysis` by density, the Cauchy transform and Guerra's cut-offs) passes
from this inequality to the norm of `𝒮`; see the module docstring. -/
theorem beurlingNorm_le {p : ℝ} (hp : 1 < p) : beurlingNorm p ≤ ENNReal.ofReal (pStar p - 1) := by
  rw [beurlingNorm_eq_beurlingPowNorm]
  exact External.BaernsteinMontgomerySmith.remark_b hp (by linarith [Corollary2Norm.le_pStar p])
    fun u hu huc => Corollary2Norm.integral_norm_dz_rpow_le hp hu huc

/-- **Corollary 2** (`cor:Bp-BA`), second assertion `(eq:BA-sharp-norm)`: the norm of the
Beurling–Ahlfors transform on `L^p (ℂ; ℂ)` is `p* − 1`, for `1 < p < ∞`. -/
theorem corollary2_norm {p : ℝ} (hp : 1 < p) : beurlingNorm p = ENNReal.ofReal (pStar p - 1) := by
  refine le_antisymm (beurlingNorm_le hp) ?_
  rw [beurlingNorm_eq_beurlingPowNorm]
  exact External.Lehto.lowerBound hp

/-- The sharp norm of Tau Ceti's Beurling–Ahlfors operator on complex-valued `L^p`. -/
theorem corollary2_norm_tauCeti {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ‖TauCeti.beurlingLp (F := ℂ) (ENNReal.ofReal p)
      (by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hp)
      ENNReal.ofReal_ne_top‖ₑ = ENNReal.ofReal (pStar p - 1) := by
  rw [← corollary2_norm hp, beurlingNorm_eq_beurlingPowNorm]
  apply HarmonicAnalysis.enorm_eq_multiplierNorm
  intro f
  exact (TauCeti.beurlingLp_toLp _ _ f).trans (HarmonicAnalysis.beurlingL2_toLp f)

end Agazzi
