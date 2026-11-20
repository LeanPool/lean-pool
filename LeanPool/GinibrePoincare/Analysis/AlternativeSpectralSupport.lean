/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSpectralSupport.lean.
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
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralSupportCFC
public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralSupportComplex
public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralPoincare
public import LeanPool.GinibrePoincare.Analysis.PolynomialGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
/-!
# Alternative spectral support

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `spectral_ginibre_full_generator_spectrum_support`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section

/-- A bounded inverse of the resolvent pencil gives a literal two-sided inverse
on the graph domain, rather than merely a spectral-measure surrogate. -/
theorem spectral_graph_resolvent_of_pencil_unit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : H →ₗ.[ℂ] H) (R : H →L[ℂ] H)
    (hgraph : ∀ u v, (u, v) ∈ L.graph ↔ R (u - v) = u)
    (z : ℂ) (hunit : IsUnit (1 + (z - 1) • R)) :
    HasBoundedGraphResolvent L z := by
  rcases hunit with ⟨a, ha⟩
  let S : H →L[ℂ] H := ↑a⁻¹
  have hST : S * (1 + (z-1) • R) = 1 := by
    rw [← ha]
    simp [S]
  have hTS : (1 + (z-1) • R) * S = 1 := by
    rw [← ha]
    simp [S]
  have hTS_apply (x : H) : S x + (z-1) • R (S x) = x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) hTS
    simpa [mul_apply_eq_comp] using h
  have hST_apply (x : H) : S (x + (z-1) • R x) = x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) hST
    simpa [mul_apply_eq_comp] using h
  refine ⟨S * R, ?_, ?_⟩
  · intro f
    apply (hgraph _ _).mpr
    change R (S (R f) - (z • S (R f) - f)) = S (R f)
    have h := hTS_apply (R f)
    rw [map_sub, map_sub, map_smul]
    rw [sub_smul, one_smul] at h
    calc
      _ = R (S (R f)) - (z • R (S (R f)) -
          (S (R f) + (z • R (S (R f)) - R (S (R f))))) :=
        congrArg (fun a => R (S (R f)) - (z • R (S (R f)) - a)) h.symm
      _ = _ := by abel
  · intro u v hg
    have hr := (hgraph _ _).mp hg
    change S (R (z • u - v)) = u
    have he : R (z • u - v) = u + (z-1) • R u := by
      rw [map_sub, map_smul]
      rw [map_sub] at hr
      rw [sub_smul, one_smul]
      calc
        _ = (R u - R v) + (z • R u - R u) := by abel
        _ = _ := by rw [hr]
    rw [he]
    exact hST_apply u

/-- The independent spectral gap controls the concrete resolvent after removing
its invariant constant component, without invoking the earlier Poincaré proof. -/
theorem spectral_ginibre_resolvent_gap_quadratic (n : ℕ) (hn : 0 < n)
    (f : ginibreSymmetricL2 n) :
    3 * ‖ginibreFullComplexResolvent n hn
      (f - ginibreFullComplexResolvent n hn f)‖ ^ 2 ≤
    (inner ℂ (f - ginibreFullComplexResolvent n hn f)
      (ginibreFullComplexResolvent n hn
        (f - ginibreFullComplexResolvent n hn f))).re := by
  let R := ginibreFullComplexResolvent n hn
  let k := f - R f
  let u := R k
  have hm (a b : GinibreFullValueL2 n) :
      ginibreL2Mean n (a-b) = ginibreL2Mean n a - ginibreL2Mean n b := by
    simp only [← ginibreRealConstantL2_one_inner n hn, inner_sub_right]
  have hkr : ginibreL2Mean n (ginibreFullSymmetricRe n k).val = 0 := by
    simp only [k, R, map_sub, ginibreFullComplexResolvent_re]
    change ginibreL2Mean n ((ginibreFullSymmetricRe n f).val -
      ginibreFullValueResolvent n hn (ginibreFullSymmetricRe n f).val) = 0
    rw [hm, ginibreFullValueResolvent_mean, sub_self]
  have hki : ginibreL2Mean n (ginibreFullSymmetricIm n k).val = 0 := by
    simp only [k, R, map_sub, ginibreFullComplexResolvent_im]
    change ginibreL2Mean n ((ginibreFullSymmetricIm n f).val -
      ginibreFullValueResolvent n hn (ginibreFullSymmetricIm n f).val) = 0
    rw [hm, ginibreFullValueResolvent_mean, sub_self]
  have hur : ginibreL2Mean n (ginibreFullSymmetricRe n u).val = 0 := by
    change ginibreL2Mean n (ginibreFullSymmetricRe n (ginibreFullComplexResolvent n hn k)).val = 0
    rw [ginibreFullComplexResolvent_re]
    exact (ginibreFullValueResolvent_mean n hn _).trans hkr
  have hui : ginibreL2Mean n (ginibreFullSymmetricIm n u).val = 0 := by
    change ginibreL2Mean n (ginibreFullSymmetricIm n (ginibreFullComplexResolvent n hn k)).val = 0
    rw [ginibreFullComplexResolvent_im]
    exact (ginibreFullValueResolvent_mean n hn _).trans hki
  have hg : (u, u-k) ∈ (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff]
    simpa only [sub_sub_cancel] using (show R k = u from rfl)
  have hgap := spectral_ginibre_full_generator_gap hn u (u-k) hg
  simp only [ginibreL2Variance, hur, hui, ginibreRealConstantL2_zero,
    sub_zero] at hgap
  have hnorm := ginibreFullComplex_norm_sq n u.val
  change ‖u‖^2 = ‖(ginibreFullSymmetricRe n u).val‖^2 +
    ‖(ginibreFullSymmetricIm n u).val‖^2 at hnorm
  rw [inner_sub_left, inner_self_eq_norm_sq_to_K] at hgap
  have he : ((‖u‖ : ℂ)^2).re = ‖u‖^2 := by simp [pow_two]
  simp only [Complex.sub_re] at hgap
  change 2 * (‖(ginibreFullSymmetricRe n u).val‖^2 +
    ‖(ginibreFullSymmetricIm n u).val‖^2) ≤
    -(((‖u‖ : ℂ)^2).re - (inner ℂ k u).re) at hgap
  rw [he] at hgap
  change 3 * ‖u‖^2 ≤ (inner ℂ k u).re
  nlinarith

/-- The sharp spectral gap makes the literal fourth-degree resolvent
polynomial positive on the full symmetric complex Hilbert space. -/
theorem spectral_ginibre_resolvent_polynomial_positive (n : ℕ) (hn : 0 < n) :
    let R := ginibreFullComplexResolvent n hn
    let K := 1-R
    (star K * R * K - (3 : ℂ) • (star (R*K) * (R*K))).IsPositive := by
  let R := ginibreFullComplexResolvent n hn
  let K : ginibreSymmetricL2 n →L[ℂ] ginibreSymmetricL2 n := 1-R
  have hs1 : IsSelfAdjoint (star K * R * K) :=
    (ginibreFullComplexResolvent_isSelfAdjoint n hn).conjugate' K
  have hs2 : IsSelfAdjoint ((3 : ℂ) • (star (R*K) * (R*K))) :=
    (show IsSelfAdjoint (3 : ℂ) by simp [IsSelfAdjoint]).smul
      (IsSelfAdjoint.star_mul_self (R*K))
  refine ⟨?_, ?_⟩
  · intro x y
    change inner ℂ ((star K * R * K) x - ((3 : ℂ) • (star (R*K)*(R*K))) x) y =
      inner ℂ x ((star K * R * K) y - ((3 : ℂ) • (star (R*K)*(R*K))) y)
    have h1 := hs1.isSymmetric x y
    have h2 := hs2.isSymmetric x y
    change inner ℂ ((star K * R * K) x) y = inner ℂ x ((star K * R * K) y) at h1
    change inner ℂ (((3 : ℂ) • (star (R*K)*(R*K))) x) y =
      inner ℂ x (((3 : ℂ) • (star (R*K)*(R*K))) y) at h2
    rw [inner_sub_left, inner_sub_right, h1, h2]
  intro f
  change 0 ≤ (inner ℂ ((star K * R * K - (3 : ℂ) • (star (R*K) * (R*K))) f) f).re
  simp only [sub_apply, smul_apply,
    mul_apply_eq_comp, inner_sub_left,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  change 0 ≤ (inner ℂ (R (K f)) (K f)).re -
    (inner ℂ ((3 : ℂ) • ((R*K).adjoint (R (K f)))) f).re
  have ht : (inner ℂ ((3 : ℂ) • ((R*K).adjoint (R (K f)))) f).re =
      3 * ‖R (K f)‖^2 := by
    calc
      _ = ((starRingEnd ℂ) 3 * inner ℂ ((R*K).adjoint (R (K f))) f).re :=
        congrArg Complex.re (inner_smul_left _ _ (3 : ℂ))
      _ = ((starRingEnd ℂ) 3 * inner ℂ (R (K f)) ((R*K) f)).re :=
        congrArg (fun z : ℂ => ((starRingEnd ℂ) 3 * z).re)
          (ContinuousLinearMap.adjoint_inner_left (R*K) f (R (K f)))
      _ = _ := by simp [mul_apply_eq_comp, inner_self_eq_norm_sq_to_K, pow_two]
  have hg := spectral_ginibre_resolvent_gap_quadratic n hn f
  change 3 * ‖R (K f)‖^2 ≤ (inner ℂ (K f) (R (K f))).re at hg
  have he : (inner ℂ (R (K f)) (K f)).re = (inner ℂ (K f) (R (K f))).re :=
    inner_re_symm (𝕜:=ℂ) _ _
  have hnrm : (((‖R (K f)‖ : ℝ) : ℂ)^2).re = ‖R (K f)‖^2 := by simp [pow_two]
  have hout := sub_nonneg.mpr hg
  calc
    0 ≤ (inner ℂ (K f) (R (K f))).re - 3 * ‖R (K f)‖^2 := hout
    _ = _ := congrArg₂ (fun a b : ℝ => a-b) he.symm ht.symm

/-- The actual bounded weak resolvent has its isolated equilibrium spectral
point at one and all remaining spectral points at most one third. -/
theorem spectral_ginibre_resolvent_spectrum_support (n : ℕ) (hn : 0 < n) :
    spectrum ℝ (ginibreFullComplexResolvent n hn) ⊆
      Set.Icc (0 : ℝ) (1/3) ∪ {1} := by
  let R := ginibreFullComplexResolvent n hn
  apply spectralSupportCFC_spectrum_gap_of_adjoint_form R
    (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_spectrum n hn)
  have hp := spectral_ginibre_resolvent_polynomial_positive n hn
  change (star (1-R)*R*(1-R) - (3 : ℂ) •
    (star (R*(1-R))*(R*(1-R)))).IsPositive at hp
  have he : (3 : ℝ) • (star (R*(1-R))*(R*(1-R))) =
      (3 : ℂ) • (star (R*(1-R))*(R*(1-R))) := by
    ext1 x
    change (3 : ℝ) • ((star (R*(1-R))*(R*(1-R))) x) =
      (3 : ℂ) • ((star (R*(1-R))*(R*(1-R))) x)
    exact RCLike.real_smul_eq_coe_smul (K:=ℂ) (3 : ℝ)
      ((star (R*(1-R))*(R*(1-R))) x)
  refine (congrArg (fun T => (star (1 - R) * R * (1 - R) - T).IsPositive) he).mpr ?_
  exact hp

/-- Section 3's support statement for the literal bounded two-sided graph
resolvent of the full symmetric complex generator, at paper speed αₙ=n. -/
theorem spectral_ginibre_full_generator_spectrum_support (n : ℕ) (hn : 0 < n) :
    graphOperatorSpectrum (ginibreFullGenerator n hn) ⊆
      {z : ℂ | z = 0 ∨ (z.im = 0 ∧ z.re ≤ -2)} := by
  intro z hz
  by_cases him : z.im = 0
  · by_cases hzero : z = 0
    · exact Or.inl hzero
    · refine Or.inr ⟨him, ?_⟩
      by_contra hgap
      have hre : z.re ≠ 0 := by
        intro he
        apply hzero
        exact Complex.ext (by simpa using he) (by simpa using him)
      have hez : (z.re : ℂ) = z := by
        apply Complex.ext <;> simp [him]
      have hu := spectralSupportCFC_pencil_isUnit (ginibreFullComplexResolvent n hn)
        (ginibreFullComplexResolvent_isSelfAdjoint n hn)
        (spectral_ginibre_resolvent_spectrum_support n hn) z.re (by linarith) hre
      rw [hez] at hu
      exact hz (spectral_graph_resolvent_of_pencil_unit _ _
        (ginibreFullGenerator_graph_iff n hn) z hu)
  · exact False.elim (hz (spectral_graph_resolvent_of_pencil_unit _ _
      (ginibreFullGenerator_graph_iff n hn) z
      (spectralSupportComplex_pencil_isUnit _
        (ginibreFullComplexResolvent_isSelfAdjoint n hn) z him)))

end
end GinibrePoincare
