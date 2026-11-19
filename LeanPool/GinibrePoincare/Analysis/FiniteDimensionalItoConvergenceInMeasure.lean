/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoConvergenceInMeasure.lean.
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

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Algebra of scalar convergence in measure for Itô errors

On a finite measure space, convergence in measure is characterized by
almost-everywhere convergent subsubsequences. The multiplication and addition
proofs extract a common such subsequence for both factors, then apply the
ordinary pointwise limit rule. Continuous scalar transformations use the
same criterion; finite sums follow by induction.

For a normalized error `R / (1 + Q)`, nonnegativity of `Q` prevents division
by zero. If `Q` converges in measure, multiply the vanishing ratio by the
convergent factor `1 + Q`. The dominated variant needs only a convergent
upper bound `S` for `Q`: increasing the denominator reduces the norm of the
ratio. This is useful when only a scalar bound on configuration quadratic
variation has been identified. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]

/-- Actual products of two measurable convergent-in-probability scalar sequences converge. -/
theorem itoTendstoInMeasure_mul (f g : ℕ → Ω → ℝ) (F G : Ω → ℝ)
    (hfm : ∀ n, AEStronglyMeasurable (f n) P) (hgm : ∀ n, AEStronglyMeasurable (g n) P)
    (hf : TendstoInMeasure P f atTop F) (hg : TendstoInMeasure P g atTop G) :
    TendstoInMeasure P (fun n ω => f n ω*g n ω) atTop (fun ω => F ω*G ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => (hfm n).mul (hgm n))).mpr
  intro ns hns
  obtain ⟨ms, hms, hmf⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks, hks, hmg⟩ := (hg.comp (hns.tendsto_atTop.comp
      hms.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ms ∘ ks, hms.comp hks,?_⟩
  filter_upwards [hmf, hmg] with ω hωf hωg
  exact (hωf.comp hks.tendsto_atTop).mul hωg

/-- Actual sums preserve convergence in probability. -/
theorem itoTendstoInMeasure_add (f g : ℕ → Ω → ℝ) (F G : Ω → ℝ)
    (hfm : ∀ n, AEStronglyMeasurable (f n) P) (hgm : ∀ n, AEStronglyMeasurable (g n) P)
    (hf : TendstoInMeasure P f atTop F) (hg : TendstoInMeasure P g atTop G) :
    TendstoInMeasure P (fun n ω => f n ω+g n ω) atTop (fun ω => F ω+G ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => (hfm n).add (hgm n))).mpr
  intro ns hns
  obtain ⟨ms, hms, hmf⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks, hks, hmg⟩ := (hg.comp (hns.tendsto_atTop.comp
      hms.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ms ∘ ks, hms.comp hks,?_⟩
  filter_upwards [hmf, hmg] with ω hωf hωg
  exact (hωf.comp hks.tendsto_atTop).add hωg

/-- Actual continuous scalar transformations preserve convergence in probability. -/
theorem itoTendstoInMeasure_continuous (f : ℕ → Ω → ℝ) (F : Ω → ℝ)
    (hfm : ∀ n, AEStronglyMeasurable (f n) P)
    (hf : TendstoInMeasure P f atTop F) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    TendstoInMeasure P (fun n ω => φ (f n ω)) atTop (fun ω => φ (F ω)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => hφ.comp_aestronglyMeasurable (hfm n))).mpr
  intro ns hns
  obtain ⟨ms, hms, hmf⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms,?_⟩
  filter_upwards [hmf] with ω hω
  exact (hφ.tendsto (F ω)).comp hω

/-- Vanishing normalized errors and actual convergent quadratic sums imply
vanishing actual errors in probability. -/
theorem itoNormalizedError_tendstoInMeasure (R Q : ℕ → Ω → ℝ) (q : Ω → ℝ)
    (hRm : ∀ n, AEStronglyMeasurable (R n) P) (hQm : ∀ n, AEStronglyMeasurable (Q n) P)
    (hQpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Q n ω)
    (hQ : TendstoInMeasure P Q atTop q)
    (hR : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω / (1 + Q n ω)) atTop (𝓝 0)) :
    TendstoInMeasure P R atTop (fun _ => 0) := by
  have hmQ (n : ℕ) : AEStronglyMeasurable (fun ω => 1+Q n ω) P :=
    aestronglyMeasurable_const.add (hQm n)
  have hmR (n : ℕ) : AEStronglyMeasurable (fun ω => R n ω/(1+Q n ω)) P :=
    ((hRm n).aemeasurable.div (hmQ n).aemeasurable).aestronglyMeasurable
  have hratio := tendstoInMeasure_of_tendsto_ae hmR hR
  have hplus := itoTendstoInMeasure_continuous P Q q hQm hQ (fun x => 1+x) (by fun_prop)
  have hprod := itoTendstoInMeasure_mul P _ _ (fun _ => 0) (fun ω => 1+q ω)
    hmR hmQ hratio hplus
  have he : ∀ᶠ n in atTop, (fun ω => (R n ω/(1+Q n ω))*(1+Q n ω)) =ᵐ[P] R n := by
    apply Eventually.of_forall
    intro n
    filter_upwards [hQpos n] with ω hω
    exact div_mul_cancel₀ _ (by linarith)
  exact hprod.congr' he (ae_of_all _ (fun ω => zero_mul _))

/-- A convergent scalar quadratic-variation upper bound suffices; the actual
configuration quadratic sum itself need not converge. -/
theorem itoNormalizedDominatedError_tendstoInMeasure (R Q S : ℕ → Ω → ℝ) (s : Ω → ℝ)
    (hRm : ∀ n, AEStronglyMeasurable (R n) P) (hSm : ∀ n, AEStronglyMeasurable (S n) P)
    (hQS : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Q n ω ∧ Q n ω ≤ S n ω)
    (hS : TendstoInMeasure P S atTop s)
    (hR : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω / (1 + Q n ω)) atTop (𝓝 0)) :
    TendstoInMeasure P R atTop (fun _ => 0) := by
  apply itoNormalizedError_tendstoInMeasure P R S s hRm hSm
    (fun n => (hQS n).mono (fun ω hω => hω.1.trans hω.2)) hS
  filter_upwards [hR, ae_all_iff.mpr hQS] with ω hω hqs
  have hn : Tendsto (fun n => ‖R n ω/(1+Q n ω)‖) atTop (𝓝 0) := by
    simpa using hω.norm
  apply squeeze_zero_norm _ hn
  intro n
  have hq : 0 < 1+Q n ω := by linarith [(hqs n).1]
  have hs : 0 < 1+S n ω := by linarith [(hqs n).1, (hqs n).2]
  simp only [norm_div, Real.norm_eq_abs, abs_of_nonneg hq.le, abs_of_nonneg hs.le]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hq (by linarith [(hqs n).2])

/-- Any actual finite family of convergent scalar processes has a convergent sum. -/
theorem itoTendstoInMeasure_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℕ → Ω → ℝ) (F : ι → Ω → ℝ)
    (hfm : ∀ i n, AEStronglyMeasurable (f i n) P)
    (hf : ∀ i, TendstoInMeasure P (f i) atTop (F i)) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ s, f i n ω) atTop (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const)
      (ae_of_all _ (fun ω => tendsto_const_nhds))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact itoTendstoInMeasure_add P _ _ _ _ (hfm i)
      (fun n => by
        convert Finset.aestronglyMeasurable_sum s (fun j hj => hfm j n) using 1
        ext ω
        simp) (hf i) ih

end
end GinibrePoincare
