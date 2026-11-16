/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Operator
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.Profile

/-! # Inverse-Hessian diffusion calculus

The nondivergence operator with inverse-Hessian coefficients and drift
`∇V ∘ ∇φ`: product, linearity over finite sums and `f − c g`, self-generator,
composition, continuity and cutoff bounds for given potentials (Letwin
arXiv:2607.24164v1, (2.3) and Lemma A.4). No semigroup generation or
source-potential regularity is inferred.
-/

@[expose] public section

noncomputable section
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Diffusion

/-- Letwin's second-order operator with the inverse Hessian as coefficient field and the drift
`∂_i V ∘ ∇φ`: `L f = Σ_ij ((∇²φ)⁻¹)_{ij} ∂_{ij} f − Σ_i (∂_i V)(∇φ) ∂_i f` (the
`nondivergenceOperator` of (2.3)
with `A = (∇²φ)⁻¹`, `b = ∇V ∘ ∇φ`, standard orthonormal basis). No Markov or symmetric-`L²` claim.
-/
def hessianInverseOperator (φ V f : E → ℝ) (x : E) : ℝ :=
  nondivergenceOperator (fun y => inverseHessianEntry φ (stdOrthonormalBasis ℝ E) y)
    (fun y i => fderiv ℝ V (gradient φ y) (stdOrthonormalBasis ℝ E i)) f x

/-- The Leibniz rule (2.3) for the inverse-Hessian operator. -/
theorem hessianInverseOperator_mul {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (V : E → ℝ)
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    hessianInverseOperator φ V (fun y => f y * g y) x =
      f x * hessianInverseOperator φ V g x + g x * hessianInverseOperator φ V f x +
        2 * ∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ g x (stdOrthonormalBasis ℝ E j) := by
  exact nondivergenceOperator_mul
    (fun y => inverseHessianEntry φ (stdOrthonormalBasis ℝ E) y)
    (fun y i j => inverseHessianEntry_symm (stdOrthonormalBasis ℝ E) hφ y i j)
    (fun y i => fderiv ℝ V (gradient φ y) (stdOrthonormalBasis ℝ E i)) hf hg x

end Diffusion

section Linearity

/-- The operator is additive over finite sums of `C²` functions. -/
theorem hessianInverseOperator_sum {ι : Type*} (s : Finset ι) (φ V : E → ℝ)
    {f : ι → E → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : E) :
    hessianInverseOperator φ V (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, hessianInverseOperator φ V (f i) x := by
  have hsum : ContDiff ℝ 2 (fun y => ∑ i ∈ s, f i y) := ContDiff.sum hf
  have hD (y v : E) :
      fderiv ℝ (fun z => ∑ i ∈ s, f i z) y v = ∑ i ∈ s, fderiv ℝ (f i) y v :=
    fderiv_sum_apply s (fun i hi => ((hf i hi).differentiable (by norm_num)).differentiableAt) v
  have hH (u v : E) :
      bilinearIteratedFDerivTwo ℝ (fun y => ∑ i ∈ s, f i y) x u v =
        ∑ i ∈ s, bilinearIteratedFDerivTwo ℝ (f i) x u v := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hsum]
    simp_rw [hD]
    rw [fderiv_sum_apply s (fun i hi => (differentiable_fderiv_apply (hf i hi) v).differentiableAt)
      u]
    exact Finset.sum_congr rfl fun i hi =>
      (bilinearIteratedFDerivTwo_eq_fderiv_apply (hf i hi) x u v).symm
  simp only [hessianInverseOperator, nondivergenceOperator]
  simp_rw [hH, hD, Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  congr 1
  · conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  · exact Finset.sum_comm

/-- The operator of `f − c g` for `C²` functions `f`, `g`. -/
theorem hessianInverseOperator_sub_const_mul (φ V : E → ℝ) {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (c : ℝ) (x : E) :
    hessianInverseOperator φ V (fun y => f y - c * g y) x =
      hessianInverseOperator φ V f x - c * hessianInverseOperator φ V g x := by
  have hcg : ContDiff ℝ 2 (fun y => c * g y) := contDiff_const.mul hg
  have hD (y v : E) :
      fderiv ℝ (fun z => f z - c * g z) y v = fderiv ℝ f y v - c * fderiv ℝ g y v := by
    rw [fderiv_sub_apply ((hf.differentiable (by norm_num)).differentiableAt)
      ((hcg.differentiable (by norm_num)).differentiableAt) v,
      fderiv_const_mul_apply ((hg.differentiable (by norm_num)).differentiableAt) c v]
  have hH (u v : E) :
      bilinearIteratedFDerivTwo ℝ (fun y => f y - c * g y) x u v =
        bilinearIteratedFDerivTwo ℝ f x u v - c * bilinearIteratedFDerivTwo ℝ g x u v := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply (hf.sub hcg)]
    simp_rw [hD]
    rw [fderiv_sub_apply (differentiable_fderiv_apply hf v).differentiableAt
      ((differentiable_fderiv_apply hg v).const_mul c).differentiableAt u,
      fderiv_const_mul_apply (differentiable_fderiv_apply hg v).differentiableAt c u,
      ← bilinearIteratedFDerivTwo_eq_fderiv_apply hf x u v,
      ← bilinearIteratedFDerivTwo_eq_fderiv_apply hg x u v]
  have hmul (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
  simp only [hessianInverseOperator, nondivergenceOperator]
  simp only [hH, hD, mul_sub, hmul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end Linearity

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis.BakryEmery

section SelfGenerator

/--
**Self-generator identity** (Letwin Lemma A.4, p. 17): at a point where the Hessian of a `C²`
potential is positive
definite, `L φ = dim E − ⟨∇V(∇φ), ∇φ⟩`. -/
theorem hessianInverseOperator_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (V : E → ℝ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    hessianInverseOperator φ V φ x =
      (Module.finrank ℝ E : ℝ) - inner ℝ (gradient V (gradient φ x)) (gradient φ x) := by
  let b := stdOrthonormalBasis ℝ E
  have hrow (i : Fin (Module.finrank ℝ E)) :
    (∑ j, inverseHessianEntry φ b x i j * bilinearIteratedFDerivTwo ℝ φ x (b i) (b j)) = 1 := by
    calc
      _ = ∑ j, inverseHessianEntry φ b x i j * bilinearIteratedFDerivTwo ℝ φ x (b j) (b i) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [bilinearIteratedFDerivTwo_symm hφ x (b i) (b j)]
      _ = 1 := by simpa using sum_inverseHessianEntry_mul_hessian b hφ x hPD i i
  have hrepr : (∑ i, (fderiv ℝ φ x (b i)) • b i) = gradient φ x := by
    simpa [inner_gradient_right] using b.sum_repr' (gradient φ x)
  have hdrift :
    (∑ i, fderiv ℝ V (gradient φ x) (b i) * fderiv ℝ φ x (b i)) =
      fderiv ℝ V (gradient φ x) (gradient φ x) := by
    calc
      _ = fderiv ℝ V (gradient φ x) (∑ i, (fderiv ℝ φ x (b i)) • b i) := by
        simp only [map_sum, map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
      _ = _ := by rw [hrepr]
  rw [inner_gradient_left]
  unfold hessianInverseOperator nondivergenceOperator
  change
    (∑ i, ∑ j, inverseHessianEntry φ b x i j * bilinearIteratedFDerivTwo ℝ φ x (b i) (b j)) -
        (∑ i, fderiv ℝ V (gradient φ x) (b i) * fderiv ℝ φ x (b i)) =
      (Module.finrank ℝ E : ℝ) - fderiv ℝ V (gradient φ x) (gradient φ x)
  simp only [hrow]
  rw [hdrift]
  simp

end SelfGenerator

section CompactImage

/--
**Bounded self-generator** (Letwin Lemma A.4, p. 17): if `∇φ` takes values in a bounded `K` and `V`
is `C¹` on an
open set containing `closure K`, then `L φ` is uniformly bounded; the bound is constructed from `dim
E` and the
compact-image bounds of `DV` and of `∇φ`. -/
theorem bounded_hessianInverseOperator_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {φ V : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) {K U : Set E}
    (hK : Bornology.IsBounded K) (hRange : Set.range (gradient φ) ⊆ K) (hU : IsOpen U)
    (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ 1 V U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : E, |hessianInverseOperator φ V φ x| ≤ D := by
  have hcont : ContinuousOn (fderiv ℝ V) (closure K) :=
    (hV.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU
  obtain ⟨B, hB⟩ := hK.isCompact_closure.exists_bound_of_continuousOn hcont
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  have hn : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨(Module.finrank ℝ E : ℝ) + max B 0 * max R 0, add_nonneg hn (mul_nonneg hB0 hR0), ?_⟩
  intro x
  have hxK : gradient φ x ∈ K := hRange ⟨x, rfl⟩
  have hxcl : gradient φ x ∈ closure K := subset_closure hxK
  have hBx : ‖fderiv ℝ V (gradient φ x)‖ ≤ max B 0 := (hB _ hxcl).trans (le_max_left _ _)
  have hRx : ‖gradient φ x‖ ≤ max R 0 := (hR _ hxK).trans (le_max_left _ _)
  have hbound : |fderiv ℝ V (gradient φ x) (gradient φ x)| ≤ max B 0 * max R 0 := by
    calc
      |fderiv ℝ V (gradient φ x) (gradient φ x)| = ‖fderiv ℝ V (gradient φ x) (gradient φ x)‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ V (gradient φ x)‖ * ‖gradient φ x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ max B 0 * max R 0 := mul_le_mul hBx hRx (norm_nonneg _) hB0
  rw [hessianInverseOperator_self hφ V x (hPD x), inner_gradient_left]
  calc
    |(Module.finrank ℝ E : ℝ) - fderiv ℝ V (gradient φ x) (gradient φ x)| ≤
        (Module.finrank ℝ E : ℝ) + |fderiv ℝ V (gradient φ x) (gradient φ x)| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hn] using
        (abs_sub_le (Module.finrank ℝ E : ℝ) 0 (fderiv ℝ V (gradient φ x) (gradient φ x)))
    _ ≤ (Module.finrank ℝ E : ℝ) + max B 0 * max R 0 :=
      add_le_add_right hbound (Module.finrank ℝ E : ℝ)

end CompactImage

section Composition

/--
**Composition rule** (Letwin Lemma A.4, p. 17, `Lχ_R = R⁻¹η′(W/R) LW + R⁻²η''(W/R) φ^{ij}∂_iW∂_jW`):
for `C²` `W`
and `h`, `L(h ∘ W) = h′(W) LW + h''(W) Σ_{ij} ((∇²φ)⁻¹)_{ij} ∂_iW ∂_jW`; the inverse-Hessian entries
are arbitrary
coefficients here (no hypothesis on `φ`). -/
theorem hessianInverseOperator_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ V W : E → ℝ} {h : ℝ → ℝ} (hW : ContDiff ℝ 2 W)
    (hh : ContDiff ℝ 2 h) (x : E) :
    hessianInverseOperator φ V (fun y => h (W y)) x =
      deriv h (W x) * hessianInverseOperator φ V W x +
        deriv (deriv h) (W x) *
          ∑ i,
            ∑ j,
              inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                  fderiv ℝ W x (stdOrthonormalBasis ℝ E i) *
                fderiv ℝ W x (stdOrthonormalBasis ℝ E j) := by
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hh' : ContDiff ℝ 1 (deriv h) := by
    change ContDiff ℝ 1 (fun y => fderiv ℝ h y (1 : ℝ))
    exact contDiff_fderiv_apply hh (by norm_num) 1
  have hh'd : Differentiable ℝ (deriv h) := hh'.differentiable (by norm_num)
  have hcomp : ContDiff ℝ 2 (fun y => h (W y)) := by
    simpa only [Function.comp_def] using hh.comp hW
  have hfirst (y : E) : fderiv ℝ (fun z => h (W z)) y = deriv h (W y) • fderiv ℝ W y := by
    exact ((hhd (W y)).hasDerivAt.comp_hasFDerivAt y (hWd y).hasFDerivAt).fderiv
  have hfirst' (y : E) :
    fderiv ℝ (fun z => deriv h (W z)) y = deriv (deriv h) (W y) • fderiv ℝ W y := by
    exact ((hh'd (W y)).hasDerivAt.comp_hasFDerivAt y (hWd y).hasFDerivAt).fderiv
  have hsecond (v w : E) :
    bilinearIteratedFDerivTwo ℝ (fun y => h (W y)) x v w =
      deriv h (W x) * bilinearIteratedFDerivTwo ℝ W x v w +
        deriv (deriv h) (W x) * fderiv ℝ W x v * fderiv ℝ W x w := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hcomp x v w,
      bilinearIteratedFDerivTwo_eq_fderiv_apply hW x v w]
    have hfun :
      (fun y => fderiv ℝ (fun z => h (W z)) y w) = (fun y => deriv h (W y) * fderiv ℝ W y w) := by
      funext y
      simp only [hfirst, smul_apply, smul_eq_mul]
    rw [hfun]
    change fderiv ℝ ((fun y => deriv h (W y)) * (fun y => fderiv ℝ W y w)) x v = _
    have hdiff : DifferentiableAt ℝ (fun y => deriv h (W y)) x := by
      simpa only [Function.comp_def] using ((hh'd (W x)).comp x (hWd x))
    rw [fderiv_mul hdiff (differentiable_fderiv_apply hW w x), hfirst']
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp only [hessianInverseOperator, nondivergenceOperator, hsecond, hfirst, smul_apply,
    smul_eq_mul]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [mul_left_comm, mul_comm]
  ring

end Composition

section CoefficientExtraction

/--
**Coefficient extraction** (Letwin Lemma A.4, p. 17, energy identity after (2.2)): in any
orthonormal basis,
`Σ_ij A_ij ∂_iφ ∂_j(h ∘ φ) = h′(φ) Σ_ij A_ij ∂_iφ ∂_jφ` for smooth `φ`, `h`. -/
theorem sum_inverseHessianEntry_mul_fderiv_comp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} {h : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h) (x : E) :
    (∑ i,
        ∑ j,
          inverseHessianEntry φ b x i j * fderiv ℝ φ x (b i) *
            fderiv ℝ (fun y => h (φ y)) x (b j)) =
      deriv h (φ x) *
        ∑ i, ∑ j, inverseHessianEntry φ b x i j * fderiv ℝ φ x (b i) * fderiv ℝ φ x (b j) := by
  have hchain (v : E) : fderiv ℝ (fun y => h (φ y)) x v = deriv h (φ x) * fderiv ℝ φ x v := by
    have hd :=
      ((hh.differentiable (by simp)) (φ x)).hasDerivAt.comp_hasFDerivAt x
        ((hφ.differentiable (by simp)) x).hasFDerivAt
    have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv
    simpa only [Function.comp_def, smul_apply, smul_eq_mul] using hv
  simp_rw [hchain, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end CoefficientExtraction

section DefectDomination

/--
**Pointwise defect domination** (Letwin Lemma A.4, p. 17, `Lχ_R = R⁻¹η′(W/R) LW + R⁻²η''(W/R) Γ(W)`):
for `C²` `φ`
and a `C²` profile `e`, all real `c`, `R` (total conventions), the generator of `e((φ − c)/R)` is
dominated by the
first- and second-derivative terms; no hypothesis on `V` or definiteness. -/
theorem abs_hessianInverseOperator_comp_sub_div_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {φ V : E → ℝ} {e : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (he : ContDiff ℝ 2 e) (c R : ℝ) (x : E) :
    |hessianInverseOperator φ V (fun y => e ((φ y - c) / R)) x| ≤
      |R⁻¹ * deriv e ((φ x - c) / R)| * |hessianInverseOperator φ V φ x| +
        (R⁻¹) ^ 2 * |deriv (deriv e) ((φ x - c) / R)| *
          |∑ i,
              ∑ j,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                    fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                  fderiv ℝ φ x (stdOrthonormalBasis ℝ E j)| := by
  let h : ℝ → ℝ := fun s => e ((s - c) / R)
  have hh : ContDiff ℝ 2 h := by exact he.comp ((contDiff_id.sub contDiff_const).div_const R)
  have hd :
    deriv h (φ x) = R⁻¹ * deriv e ((φ x - c) / R) ∧
      deriv (deriv h) (φ x) = (R⁻¹) ^ 2 * deriv (deriv e) ((φ x - c) / R) := by
    dsimp only [h]
    apply FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv
  change |hessianInverseOperator φ V (fun y => h (φ y)) x| ≤ _
  rw [hessianInverseOperator_comp hφ hh x, hd.1, hd.2]
  refine (abs_add_le _ _).trans ?_
  apply le_of_eq
  simp only [abs_mul, abs_of_nonneg (sq_nonneg (R⁻¹))]

end DefectDomination

section Continuity

/--
**Operator continuity** (Letwin Lemma A.4, p. 17, measurability of `Lχ_R`, hence `Lχ_R ∈ L¹(ν)` by
domination):
for smooth `φ` with positive definite Hessian, `V` `C¹` on an open set containing the gradient range
and `C²` `f`,
`L f` is continuous.
-/
theorem continuous_hessianInverseOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {φ V f : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) {U : Set E}
    (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U) (hRange : Set.range (gradient φ) ⊆ U)
    (hf : ContDiff ℝ 2 f) : Continuous (hessianInverseOperator φ V f) := by
  let b := stdOrthonormalBasis ℝ E
  have hInv (i j : Fin (Module.finrank ℝ E)) :
    Continuous (fun x => inverseHessianEntry φ b x i j) := by
    exact
      (contDiff_iff_contDiffAt.mpr
          (fun x => contDiffAt_inverseHessianEntry b hφ x (hPD x) i j)).continuous
  have hφ' : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hgrad : Continuous (gradient φ) := by
    unfold gradient
    continuity
  have hV' : ContinuousOn (fun x => fderiv ℝ V x) U :=
    hV.continuousOn_fderiv_of_isOpen hU le_rfl
  have hDV : Continuous (fun x => fderiv ℝ V (gradient φ x)) := by
    simpa [Function.comp_def] using
      hV'.comp_continuous hgrad (fun x => hRange (Set.mem_range_self x))
  have hDVcoord (i : Fin (Module.finrank ℝ E)) :
    Continuous (fun x => (fderiv ℝ V (gradient φ x)) (b i)) := by
    exact hDV.clm_apply (continuous_const : Continuous (fun _ : E => b i))
  have hfirst (i : Fin (Module.finrank ℝ E)) : Continuous (fun x => (fderiv ℝ f x) (b i)) := by
    exact
      (hf.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const : Continuous (fun _ : E => b i))
  have hsecond (i j : Fin (Module.finrank ℝ E)) :
    Continuous (fun x => bilinearIteratedFDerivTwo ℝ f x (b i) (b j)) := by
    have hcf : ContDiff ℝ 1 (fun y => (fderiv ℝ f y) (b j)) :=
      contDiff_fderiv_apply hf (by norm_num) (b j)
    have hc : Continuous (fderiv ℝ (fun y => (fderiv ℝ f y) (b j))) :=
      hcf.continuous_fderiv (by norm_num)
    have hright : Continuous (fun x => (fderiv ℝ (fun y => (fderiv ℝ f y) (b j)) x) (b i)) :=
      hc.clm_apply (continuous_const : Continuous (fun _ : E => b i))
    have heq :
      (fun x => bilinearIteratedFDerivTwo ℝ f x (b i) (b j)) =
        (fun x => (fderiv ℝ (fun y => (fderiv ℝ f y) (b j)) x) (b i)) := by
      funext x
      exact bilinearIteratedFDerivTwo_eq_fderiv_apply hf x (b i) (b j)
    rw [heq]
    exact hright
  unfold hessianInverseOperator nondivergenceOperator
  continuity

end Continuity

end FunctionalInequalities.Analysis.BakryEmery
