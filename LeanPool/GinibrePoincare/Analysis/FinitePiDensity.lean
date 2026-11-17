/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FinitePiDensity.lean.
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

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Densities of finite product measures

This file proves that a finite product of measures with densities has density
the product of the coordinate densities.  Mathlib contains the binary version
(`Measure.prod_withDensity`); the theorem below packages its finite dependent
product analogue.
-/


@[expose] public section


open Fintype MeasureTheory

namespace GinibrePoincare

noncomputable section

/-- Tonelli's product formula for a product of `ℝ≥0∞`-valued functions on a
finite dependent product. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : ∀ i : Fin n, E i → ENNReal)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E ((0 : Fin (n + 1)).succAbove i)),
            f 0 x.1 * ∏ i : Fin n, f ((0 : Fin (n + 1)).succAbove i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ ((0 : Fin (n + 1)).succAbove i)))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          congr 1
          funext x
          rw [Fin.prod_univ_succAbove _ 0]
          simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
            Fin.insertNth_apply_succAbove]
        _ = (∫⁻ x, f 0 x ∂μ 0) *
            ∫⁻ x : (i : Fin n) → E ((0 : Fin (n + 1)).succAbove i),
              ∏ i, f ((0 : Fin (n + 1)).succAbove i) (x i) ∂(Measure.pi (fun i ↦ μ ((0 : Fin (n +
                1)).succAbove i))) := by
          have hg : AEMeasurable
              (fun x : (i : Fin n) → E ((0 : Fin (n + 1)).succAbove i) ↦
                ∏ i, f ((0 : Fin (n + 1)).succAbove i) (x i))
              (Measure.pi (fun i ↦ μ ((0 : Fin (n + 1)).succAbove i))) :=
            Finset.aemeasurable_fun_prod Finset.univ fun i _ ↦
              (hf ((0 : Fin (n + 1)).succAbove i)).aemeasurable.comp_quasiMeasurePreserving
                (Measure.quasiMeasurePreserving_eval _ i)
          exact lintegral_prod_mul (μ := μ 0)
            (ν := Measure.pi (fun i ↦ μ ((0 : Fin (n + 1)).succAbove i))) (hf 0).aemeasurable hg
        _ = (∫⁻ x, f 0 x ∂μ 0) *
            ∏ i : Fin n, ∫⁻ x, f ((0 : Fin (n + 1)).succAbove i) x ∂(μ ((0 : Fin (n +
              1)).succAbove i)) := by
          rw [ih (fun i ↦ f ((0 : Fin (n + 1)).succAbove i)) (fun i ↦ hf ((0 : Fin (n +
            1)).succAbove i))]
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
          rw [Fin.prod_univ_succAbove _ 0]

/-- Tonelli's product formula for a product of `ℝ≥0∞`-valued functions indexed
by an arbitrary finite type. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : ∀ i : ι, E i → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rw [lintegral_fin_nat_prod_eq_prod _ (fun i ↦ hf _)]

/-- A finite product of coordinate measures with measurable densities is the
product base measure with the product density. -/
theorem Measure.pi_withDensity {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i : ι, E i → ENNReal) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  simp_rw [withDensity_apply _ (hs _)]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [← lintegral_indicator (hs _)]
  rw [← lintegral_fintype_prod_eq_prod
    (fun i x ↦ (s i).indicator (f i) x)
    (fun i ↦ (hf i).indicator (hs i))]
  apply lintegral_congr
  intro x
  simp only [Set.indicator]
  split_ifs with h
  · have hh : ∀ i, x i ∈ s i := by simpa [Set.mem_pi] using h
    simp_rw [ite_eq_left (hh _)]
  · have hh : ¬ ∀ i, x i ∈ s i := by simpa [Set.mem_pi] using h
    push Not at hh
    obtain ⟨i, hi⟩ := hh
    symm
    apply Finset.prod_eq_zero (s := Finset.univ)
    · exact Finset.mem_univ i
    · exact ite_eq_right hi

end

end GinibrePoincare
