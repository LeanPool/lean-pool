/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteParsevalModes.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GaussianFourierUniqueness
public import LeanPool.GinibrePoincare.Analysis.PermutationLp
public import LeanPool.GinibrePoincare.Analysis.HolomorphicVandermondeL2Closure

/-! # Hermite antiholomorphic-degree modes in Gaussian L² -/


@[expose] public section


open MeasureTheory
open scoped BigOperators ENNReal

namespace GinibrePoincare

noncomputable section

open ComplexHermite

/-- Hermite coefficient of a Gaussian `L²` vector. -/
def gaussianHermiteCoefficient {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) : ℂ :=
  (gaussianHermiteHilbertBasis n hn).repr g pq

theorem gaussianHermiteCoefficient_eq_inner {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn g pq =
      inner ℂ (multivariateNormalizedL2 n hn pq.1 pq.2) g := by
  rw [gaussianHermiteCoefficient, HilbertBasis.repr_apply_apply]
  congr 1
  exact gaussianHermiteHilbertBasis_apply n hn pq

/-- The summand of `g` whose joint Hermite index has antiholomorphic degree `d`. -/
def gaussianHermiteModeTerm {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (d : ℕ)
    (pq : HermiteMultiIndex n) : Lp ℂ 2 (complexGaussianMeasure n) :=
  if totalAntiDegree pq = d then
    gaussianHermiteCoefficient hn g pq • multivariateNormalizedL2 n hn pq.1 pq.2
  else 0

theorem summable_gaussianHermiteModeTerm {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (d : ℕ) :
    Summable (gaussianHermiteModeTerm hn g d) := by
  have hs := (gaussianHermiteHilbertBasis n hn).hasSum_repr g
  refine (hs.summable.indicator (s := {pq | totalAntiDegree pq = d})).congr ?_
  intro pq
  simp only [gaussianHermiteModeTerm, Set.indicator, Set.mem_ofPred_eq]
  split_ifs with h
  · rw [gaussianHermiteCoefficient, gaussianHermiteHilbertBasis_apply]
  · rfl

/-- The antiholomorphic-degree `d` Hermite mode of `g`. -/
def gaussianHermiteMode {n : ℕ} (hn : 0 < n)
    (d : ℕ) (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  ∑' pq, gaussianHermiteModeTerm hn g d pq

theorem gaussianHermiteMode_mem_closedSpan {n : ℕ} (hn : 0 < n)
    (d : ℕ) (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianHermiteMode hn d g ∈ hermiteAntiDegreeClosedSpan n hn d := by
  apply (hermiteAntiDegreeClosedSpan n hn d).isClosed'.mem_of_tendsto
    (summable_gaussianHermiteModeTerm hn g d).hasSum
  filter_upwards with s
  apply Submodule.sum_mem
  intro pq hpq
  unfold gaussianHermiteModeTerm
  split_ifs with h
  · exact (hermiteAntiDegreeClosedSpan n hn d).smul_mem _
      (hermiteL2Family_mem_antiDegreeClosedSpan n hn pq d h)
  · exact (hermiteAntiDegreeClosedSpan n hn d).zero_mem

/-- The antiholomorphic-degree modes sum to the original Gaussian `L²` vector. -/
theorem hasSum_gaussianHermiteMode {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    HasSum (fun d ↦ gaussianHermiteMode hn d g) g := by
  let F : HermiteMultiIndex n → Lp ℂ 2 (complexGaussianMeasure n) :=
    fun pq ↦ gaussianHermiteCoefficient hn g pq •
      multivariateNormalizedL2 n hn pq.1 pq.2
  have hF : HasSum F g := by
    simpa [F, gaussianHermiteCoefficient] using
      (gaussianHermiteHilbertBasis n hn).hasSum_repr g
  let e := Equiv.sigmaFiberEquiv (@totalAntiDegree n)
  have hsigma : HasSum (F ∘ e) g := (e.hasSum_iff).2 hF
  apply hsigma.sigma
  intro d
  have hsub : Summable (F ∘ fun pq : {pq // totalAntiDegree pq = d} ↦ pq.1) :=
    hF.summable.subtype (fun pq ↦ totalAntiDegree pq = d)
  have hmode : gaussianHermiteMode hn d g =
      ∑' pq : {pq // totalAntiDegree pq = d}, F pq.1 := by
    rw [gaussianHermiteMode]
    calc
      (∑' pq, gaussianHermiteModeTerm hn g d pq) =
          ∑' pq, {pq | totalAntiDegree pq = d}.indicator F pq := by
            apply tsum_congr
            intro pq
            simp [gaussianHermiteModeTerm, F, Set.indicator]
      _ = ∑' pq : {pq // totalAntiDegree pq = d}, F pq.1 :=
        (tsum_subtype {pq | totalAntiDegree pq = d} F).symm
  rw [hmode]
  apply hsub.hasSum.congr_fun
  intro c
  rfl

theorem tsum_gaussianHermiteMode {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    ∑' d, gaussianHermiteMode hn d g = g :=
  (hasSum_gaussianHermiteMode hn g).tsum_eq

theorem inner_gaussianHermiteMode_eq_zero {n : ℕ} (hn : 0 < n)
    {d e : ℕ} (hde : d ≠ e)
    (g h : Lp ℂ 2 (complexGaussianMeasure n)) :
    inner ℂ (gaussianHermiteMode hn d g) (gaussianHermiteMode hn e h) = 0 := by
  have hterm (p q : HermiteMultiIndex n) :
      inner ℂ (gaussianHermiteModeTerm hn g d p)
        (gaussianHermiteModeTerm hn h e q) = 0 := by
    unfold gaussianHermiteModeTerm
    split_ifs with hp hq
    · have hpq : p ≠ q := by
        intro hpq
        subst q
        exact hde (hp.symm.trans hq)
      rw [inner_smul_left, inner_smul_right]
      have ho := (gaussianHermiteHilbertBasis n hn).orthonormal.inner_eq_zero hpq
      rw [gaussianHermiteHilbertBasis_apply, gaussianHermiteHilbertBasis_apply] at ho
      simp [ho]
    all_goals simp
  have htermMode (p : HermiteMultiIndex n) :
      inner ℂ (gaussianHermiteModeTerm hn g d p)
        (gaussianHermiteMode hn e h) = 0 := by
    rw [gaussianHermiteMode]
    change innerSL ℂ (gaussianHermiteModeTerm hn g d p)
      (∑' pq, gaussianHermiteModeTerm hn h e pq) = 0
    rw [(innerSL ℂ (gaussianHermiteModeTerm hn g d p)).map_tsum
        (summable_gaussianHermiteModeTerm hn h e)]
    simp_rw [innerSL_apply_apply, hterm p]
    exact tsum_zero
  rw [gaussianHermiteMode]
  change innerSLFlip ℂ (gaussianHermiteMode hn e h)
    (∑' pq, gaussianHermiteModeTerm hn g d pq) = 0
  rw [(innerSLFlip ℂ (gaussianHermiteMode hn e h)).map_tsum
      (summable_gaussianHermiteModeTerm hn g d)]
  simp_rw [innerSLFlip_apply_apply, htermMode]
  exact tsum_zero

theorem inner_gaussianHermiteMode_self_sum {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (d : ℕ) :
    inner ℂ g (gaussianHermiteMode hn d g) =
      inner ℂ (gaussianHermiteMode hn d g) (gaussianHermiteMode hn d g) := by
  calc
    inner ℂ g (gaussianHermiteMode hn d g) =
        inner ℂ (∑' e, gaussianHermiteMode hn e g)
          (gaussianHermiteMode hn d g) := by rw [tsum_gaussianHermiteMode]
    _ = ∑' e, inner ℂ (gaussianHermiteMode hn e g)
          (gaussianHermiteMode hn d g) := by
      change innerSLFlip ℂ (gaussianHermiteMode hn d g)
        (∑' e, gaussianHermiteMode hn e g) = _
      rw [(innerSLFlip ℂ (gaussianHermiteMode hn d g)).map_tsum
        (hasSum_gaussianHermiteMode hn g).summable]
      simp_rw [innerSLFlip_apply_apply]
    _ = inner ℂ (gaussianHermiteMode hn d g)
          (gaussianHermiteMode hn d g) := by
      rw [tsum_eq_single d]
      · intro e hed
        exact inner_gaussianHermiteMode_eq_zero hn hed g g

/-- Parseval's identity for the antiholomorphic-degree decomposition. -/
theorem hasSum_norm_sq_gaussianHermiteMode {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    HasSum (fun d ↦ ‖gaussianHermiteMode hn d g‖ ^ 2) (‖g‖ ^ 2) := by
  have hs := (hasSum_gaussianHermiteMode hn g).mapL (innerSL ℂ g)
  have hs' : HasSum
      (fun d ↦ inner ℂ g (gaussianHermiteMode hn d g)) (inner ℂ g g) := by
    simpa only [innerSL_apply_apply] using hs
  have hcomplex : HasSum
      (fun d ↦ (‖gaussianHermiteMode hn d g‖ : ℂ) ^ 2)
      ((‖g‖ : ℂ) ^ 2) := by
    convert hs' using 1
    · funext d
      rw [inner_gaussianHermiteMode_self_sum hn g d, inner_self_eq_norm_sq_to_K]
      norm_cast
    · rw [inner_self_eq_norm_sq_to_K]
      norm_cast
  convert hcomplex.mapL Complex.reCLM using 1
  · funext d
    norm_cast
  · norm_cast

theorem tsum_norm_sq_gaussianHermiteMode {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    ∑' d, ‖gaussianHermiteMode hn d g‖ ^ 2 = ‖g‖ ^ 2 :=
  (hasSum_norm_sq_gaussianHermiteMode hn g).tsum_eq

/-- Squared mass of the positive antiholomorphic mode indexed from zero,
so that entry `k` is the mass of mode `k + 1`. -/
def positiveHermiteModeMass {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (k : ℕ) : ℝ :=
  ‖gaussianHermiteMode hn (k + 1) g‖ ^ 2

theorem summable_positiveHermiteModeMass {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    Summable (positiveHermiteModeMass hn g) := by
  unfold positiveHermiteModeMass
  exact (hasSum_norm_sq_gaussianHermiteMode hn g).summable.comp_injective
    Nat.succ_injective

/-- Parseval split into the zero antiholomorphic mode and all strictly
positive modes, in exactly the indexing used by the deficit series. -/
theorem norm_sq_eq_zeroMode_add_positiveModeMass {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    ‖g‖ ^ 2 = ‖gaussianHermiteMode hn 0 g‖ ^ 2 +
      ∑' k, positiveHermiteModeMass hn g k := by
  let a : ℕ → ℝ := fun d => ‖gaussianHermiteMode hn d g‖ ^ 2
  have hs : HasSum a (‖g‖ ^ 2) := hasSum_norm_sq_gaussianHermiteMode hn g
  have htail : HasSum (fun k => a (k + 1)) (‖g‖ ^ 2 - a 0) := by
    simpa using (hasSum_nat_add_iff' 1).2 hs
  calc
    ‖g‖ ^ 2 = a 0 + (‖g‖ ^ 2 - a 0) := by ring
    _ = a 0 + ∑' k, a (k + 1) := by rw [htail.tsum_eq]
    _ = _ := rfl

theorem inner_basis_gaussianHermiteMode {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (d : ℕ)
    (pq : HermiteMultiIndex n) :
    inner ℂ (multivariateNormalizedL2 n hn pq.1 pq.2)
      (gaussianHermiteMode hn d g) =
      if totalAntiDegree pq = d then gaussianHermiteCoefficient hn g pq else 0 := by
  rw [gaussianHermiteMode]
  change innerSL ℂ (multivariateNormalizedL2 n hn pq.1 pq.2)
    (∑' r, gaussianHermiteModeTerm hn g d r) = _
  rw [(innerSL ℂ (multivariateNormalizedL2 n hn pq.1 pq.2)).map_tsum
    (summable_gaussianHermiteModeTerm hn g d)]
  simp_rw [innerSL_apply_apply]
  rw [tsum_eq_single pq]
  · unfold gaussianHermiteModeTerm
    split_ifs with hp
    · rw [inner_smul_right]
      have hone := (gaussianHermiteHilbertBasis n hn).orthonormal.1 pq
      rw [gaussianHermiteHilbertBasis_apply] at hone
      rw [inner_self_eq_norm_sq_to_K]
      simp [hone]
    · simp
  · intro r hr
    unfold gaussianHermiteModeTerm
    split_ifs
    · rw [inner_smul_right]
      have ho := (gaussianHermiteHilbertBasis n hn).orthonormal.inner_eq_zero hr.symm
      rw [gaussianHermiteHilbertBasis_apply, gaussianHermiteHilbertBasis_apply] at ho
      simp [ho]
    · simp

theorem gaussianHermiteMode_eq_antiDegreeProjection {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (d : ℕ) :
    gaussianHermiteMode hn d g = hermiteAntiDegreeProjection n hn d g := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (gaussianHermiteMode_mem_closedSpan hn d g)
  intro w hw
  rw [inner_sub_left]
  have hspan : ∀ x ∈ hermiteAntiDegreeSpan n hn d,
      inner ℂ (g - gaussianHermiteMode hn d g) x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨pq, hpq, rfl⟩
        change totalAntiDegree pq = d at hpq
        change inner ℂ (g - gaussianHermiteMode hn d g)
          (multivariateNormalizedL2 n hn pq.1 pq.2) = 0
        rw [inner_sub_left]
        have hg : inner ℂ g (multivariateNormalizedL2 n hn pq.1 pq.2) =
            (starRingEnd ℂ) (gaussianHermiteCoefficient hn g pq) := by
          calc
            _ = (starRingEnd ℂ)
                (inner ℂ (multivariateNormalizedL2 n hn pq.1 pq.2) g) :=
              (inner_conj_symm _ _).symm
            _ = _ := by rw [← gaussianHermiteCoefficient_eq_inner]
        have hm : inner ℂ (gaussianHermiteMode hn d g)
            (multivariateNormalizedL2 n hn pq.1 pq.2) =
            (starRingEnd ℂ) (gaussianHermiteCoefficient hn g pq) := by
          rw [← inner_conj_symm,
            inner_basis_gaussianHermiteMode hn g d pq, ite_eq_left hpq]
        rw [hg, hm, sub_self]
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
    | smul c x hx ih => simp [inner_smul_right, ih]
  have hz := closure_minimal hspan
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const) hw
  change inner ℂ (g - gaussianHermiteMode hn d g) w = 0 at hz
  simpa only [inner_sub_left] using hz

theorem gaussianPermutationL2_mem_antiDegreeClosedSpan {n : ℕ} (hn : 0 < n)
    (d : ℕ) (σ : ParticlePermutation n)
    {u : Lp ℂ 2 (complexGaussianMeasure n)}
    (hu : u ∈ hermiteAntiDegreeClosedSpan n hn d) :
    gaussianPermutationL2 σ u ∈ hermiteAntiDegreeClosedSpan n hn d := by
  exact (Set.MapsTo.closure
    (fun x hx ↦ gaussianPermutationL2_mem_hermiteAntiDegreeSpan n hn d σ hx)
    (gaussianPermutationL2 σ).continuous) hu

theorem totalAntiDegree_comp_permutation_symm {n : ℕ}
    (σ : ParticlePermutation n) (p q : Fin n → ℕ) :
    totalAntiDegree (p ∘ σ.symm, q ∘ σ.symm) = totalAntiDegree (p, q) := by
  change (∑ i, q (σ.symm i)) = ∑ i, q i
  exact Equiv.sum_comp σ.symm q

theorem gaussianPermutationL2_multivariateNormalizedL2 {n : ℕ} (hn : 0 < n)
    (σ : ParticlePermutation n) (p q : Fin n → ℕ) :
    gaussianPermutationL2 σ (multivariateNormalizedL2 n hn p q) =
      multivariateNormalizedL2 n hn (p ∘ σ.symm) (q ∘ σ.symm) := by
  exact gaussianPermutationL2_hermiteL2Family n hn σ p q

private theorem gaussianPermutationL2_one {n : ℕ}
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianPermutationL2 (1 : ParticlePermutation n) u = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving u
    (gaussian_measurePreserving_permute (1 : ParticlePermutation n))] with z hz
  unfold gaussianPermutationL2
  change (Lp.compMeasurePreserving (permute (1 : ParticlePermutation n))
    (gaussian_measurePreserving_permute (1 : ParticlePermutation n)) u) z = u z
  rw [hz]
  rfl

theorem gaussianPermutationL2_comm_antiDegreeProjection {n : ℕ} (hn : 0 < n)
    (d : ℕ) (σ : ParticlePermutation n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianPermutationL2 σ (hermiteAntiDegreeProjection n hn d g) =
      hermiteAntiDegreeProjection n hn d (gaussianPermutationL2 σ g) := by
  let U : Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) :=
    hermiteAntiDegreeClosedSpan n hn d
  let T := gaussianPermutationL2 σ
  have hmap : U.map T.toLinearMap = U := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact gaussianPermutationL2_mem_antiDegreeClosedSpan hn d σ hx
    · intro y hy
      refine ⟨gaussianPermutationL2 σ.symm y,
        gaussianPermutationL2_mem_antiDegreeClosedSpan hn d σ.symm hy, ?_⟩
      change gaussianPermutationL2 σ (gaussianPermutationL2 σ.symm y) = y
      rw [gaussianPermutationL2_comp_apply]
      change gaussianPermutationL2 (σ * σ⁻¹) y = y
      rw [mul_inv_cancel, gaussianPermutationL2_one]
  let : (U.map T.toLinearMap).HasOrthogonalProjection := hmap.symm ▸ inferInstance
  calc
    T (U.starProjection g) = (U.map T.toLinearMap).starProjection (T g) :=
      T.map_starProjection U g
    _ = U.starProjection (T g) := by simp only [hmap]

theorem gaussianPermutationL2_comm_gaussianHermiteMode {n : ℕ} (hn : 0 < n)
    (d : ℕ) (σ : ParticlePermutation n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianPermutationL2 σ (gaussianHermiteMode hn d g) =
      gaussianHermiteMode hn d (gaussianPermutationL2 σ g) := by
  rw [gaussianHermiteMode_eq_antiDegreeProjection,
    gaussianHermiteMode_eq_antiDegreeProjection,
    gaussianPermutationL2_comm_antiDegreeProjection]

theorem gaussianHermiteMode_mem_alternating {n : ℕ} (hn : 0 < n)
    (d : ℕ) {g : Lp ℂ 2 (complexGaussianMeasure n)}
    (hg : g ∈ gaussianAlternatingL2 n) :
    gaussianHermiteMode hn d g ∈ gaussianAlternatingL2 n := by
  intro σ
  rw [gaussianPermutationL2_comm_gaussianHermiteMode, hg σ,
    gaussianHermiteMode_eq_antiDegreeProjection, map_smul]
  rw [← gaussianHermiteMode_eq_antiDegreeProjection]

end

end GinibrePoincare
