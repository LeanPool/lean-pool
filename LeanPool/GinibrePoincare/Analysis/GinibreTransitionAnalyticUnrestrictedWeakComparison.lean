/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticUnrestrictedWeakComparison.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticWeakSymmetry

/-!
# Ginibre transition analytic unrestricted weak comparison

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreDistributionalWeakPair_compact_equation_complete`,
`ginibreFullSymmetricResolvent_unique_unrestricted_weak`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section

/-- Genuine Reynolds averaging carries every ordinary weak pair into the
actual symmetric weak space, derived through the concrete smooth core. -/
theorem ginibreDistributionalWeakPair_average_symmetric {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) :
    (ginibreRealPermutationAverageL2 u, ginibreGradientPermutationAverageL2 g) ∈
      ginibreFullWeakSpace n hn := by
  have hcore : closure (ginibreTheoremOneNineCorePairs n) ⊆ ginibreFullWeakSpace n hn := by
    apply closure_minimal _ (ginibreFullWeakSpace_isClosed n hn)
    intro p hp
    obtain ⟨φ, hφ, hv, hg⟩ := hp
    have he : p=(ginibreFullCorePair hn φ hφ).val := by
      apply Prod.ext
      · apply Lp.ext
        exact hv.trans (ginibreFullCoreValue_ae hn φ hφ).symm
      · apply Lp.ext
        exact hg.trans (ginibreFullCoreGradient_ae hn φ hφ).symm
    rw [he]
    exact (ginibreFullCorePair hn φ hφ).property
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp
    (ginibreWeakPair_mem_closure_interiorSmooth hn u g hu)
  have ht : Tendsto (fun k => (ginibreRealPermutationAverageL2 (q k).1,
      ginibreGradientPermutationAverageL2 (q k).2)) atTop
      (𝓝 (ginibreRealPermutationAverageL2 u, ginibreGradientPermutationAverageL2 g)) :=
    ((ginibreRealPermutationAverageL2.continuous.comp continuous_fst).prodMk
      (ginibreGradientPermutationAverageL2.continuous.comp continuous_snd)).tendsto (u, g) |>.comp
          hlim
  exact (ginibreFullWeakSpace_isClosed n hn).mem_of_tendsto ht
    (Eventually.of_forall fun k => hcore (ginibreInteriorSmoothPair_average_mem_coreClosure hn (q k)
        (hq k)))

/-- Pairing a genuine invariant gradient with the Reynolds average changes
nothing in the exact gradient Hilbert space. -/
theorem ginibreFullGradient_fixed_inner_average {n : ℕ}
    (g h : GinibreFullGradientL2 n)
    (hg : ∀ σ : ParticlePermutation n, ginibreGradientPermutationL2 σ g=g) :
    inner ℝ g (ginibreGradientPermutationAverageL2 h)=inner ℝ g h := by
  classical
  have hterm (σ : ParticlePermutation n) : inner ℝ g (ginibreGradientPermutationL2 σ h)=inner ℝ g h
      := by
    have hh := ginibreFullGradientPermutation_inner σ g h
    rw [hg σ] at hh
    exact hh
  unfold ginibreGradientPermutationAverageL2
  simp only [smul_apply, sum_apply]
  rw [real_inner_smul_right, inner_sum]
  simp_rw [hterm]
  have hc : (Fintype.card (ParticlePermutation n) : ℝ)≠0 := Nat.cast_ne_zero.mpr
      Fintype.card_ne_zero
  simp [hc]

/-- Literal compact collision-free equations extend to every ordinary weak
pair through the actual nonsymmetric form-core closure. -/
theorem ginibreDistributionalWeakPair_compact_equation_complete {n : ℕ} (hn : 0 < n)
    (u f : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (heq : ∀ p ∈ ginibreInteriorSmoothPair n,
      inner ℝ u p.1 + (1 / (n : ℝ)) * inner ℝ g p.2 = inner ℝ f p.1)
    (w : GinibreFullValueL2 n) (h : GinibreFullGradientL2 n)
    (hw : IsGinibreDistributionalGradient n w h) :
    inner ℝ u w+(1/(n : ℝ))*inner ℝ g h=inner ℝ f w := by
  have hc : IsClosed {p : GinibreFullValueL2 n × GinibreFullGradientL2 n |
      inner ℝ u p.1+(1/(n : ℝ))*inner ℝ g p.2=inner ℝ f p.1} :=
    isClosed_eq ((continuous_const.inner continuous_fst).add
      (continuous_const.mul (continuous_const.inner continuous_snd)))
      (continuous_const.inner continuous_fst)
  exact (closure_minimal (fun p hp => heq p hp) hc)
    (ginibreWeakPair_mem_closure_interiorSmooth hn w h hw)

/-- The actual symmetric analytic resolvent satisfies its variational equation
against every ordinary weak pair, with symmetry derived by genuine averaging. -/
theorem ginibreFullSymmetricResolvent_unrestricted_variational {n : ℕ} (hn : 0 < n)
    (f : ginibreFullSymmetricValues n) :
    ∃ G : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n (ginibreFullSymmetricResolvent n hn f).val G ∧
      ∀ w : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n w h →
        inner ℝ (ginibreFullSymmetricResolvent n hn f).val w+
          (1/(n : ℝ))*inner ℝ G h=inner ℝ f.val w := by
  let r := ginibreFullFormResolvent n hn f.val
  let U := ginibreFullSymmetricResolvent n hn f
  let G := ginibreFullFormGradient n hn r
  have hrv : ginibreFullFormValue n hn r=U.val := rfl
  have hweak := ginibreFullFormSpace_weak n hn r
  rw [hrv] at hweak
  refine ⟨G, hweak.1,?_⟩
  intro w h hw
  let p : ginibreFullWeakSpace n hn :=
    ⟨(ginibreRealPermutationAverageL2 w, ginibreGradientPermutationAverageL2 h),
      ginibreDistributionalWeakPair_average_symmetric hn w h hw⟩
  have hr := ginibreFullFormResolvent_riesz n hn f.val (ginibreFullFormOfWeak n hn p)
  rw [ginibreFullFormSpace_inner, ginibreFullFormOfWeak_value, ginibreFullFormOfWeak_gradient, hrv]
      at hr
  change inner ℝ U.val (ginibreRealPermutationAverageL2 w)+
    (1/(n : ℝ))*inner ℝ G (ginibreGradientPermutationAverageL2 h)=
    inner ℝ f.val (ginibreRealPermutationAverageL2 w) at hr
  rw [ginibreFullSymmetricValues_inner_average n U w,
    ginibreFullGradient_fixed_inner_average G h (fun σ => (hweak.2 σ).2),
    ginibreFullSymmetricValues_inner_average n f w] at hr
  exact hr

/-- Unrestricted ordinary weak solutions with symmetric forcing equal the
actual symmetric analytic resolvent, without an assumed solution symmetry. -/
theorem ginibreFullSymmetricResolvent_unique_unrestricted_weak {n : ℕ} (hn : 0 < n)
    (f : ginibreFullSymmetricValues n) (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (heq : ∀ w : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n w h →
      inner ℝ u w+(1/(n : ℝ))*inner ℝ g h=inner ℝ f.val w) :
    u=(ginibreFullSymmetricResolvent n hn f).val := by
  obtain ⟨G, hG, hEq⟩ := ginibreFullSymmetricResolvent_unrestricted_variational hn f
  let U := (ginibreFullSymmetricResolvent n hn f).val
  have hNeg : IsGinibreDistributionalGradient n (-U) (-G) := by
    simpa only [neg_one_smul] using ginibreFullGradient_smul hn U G hG (-1)
  have hd : IsGinibreDistributionalGradient n (u-U) (g-G) := by
    simpa only [sub_eq_add_neg] using ginibreFullGradient_add hn u (-U) g (-G) hu hNeg
  have ha := heq (u-U) (g-G) hd
  have hb := hEq (u-U) (g-G) hd
  have hi : inner ℝ (u-U) (u-U)+(1/(n : ℝ))*inner ℝ (g-G) (g-G)=0 := by
    rw [inner_sub_left, inner_sub_left]
    linarith
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  have hc : 0<1/(n : ℝ) := by positivity
  have hz : ‖u-U‖=0 := by nlinarith [sq_nonneg ‖g-G‖, norm_nonneg (u-U)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end
end GinibrePoincare
