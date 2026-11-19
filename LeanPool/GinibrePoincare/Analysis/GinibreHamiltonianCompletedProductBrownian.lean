/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianCompletedProductBrownian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInitialMeasureIdentification
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Ginibre Hamiltonian completed product Brownian

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownian_completed_initial_noise_product`,
`ginibreCompletedProduct_initial_noise_independent`,
`ginibreBrownian_completed_product_independent_coordinates`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibre_completion_isProbabilityMeasure {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] : IsProbabilityMeasure μ.completion :=
  ⟨by change μ univ = 1; exact measure_univ⟩

local instance ginibreCompletedProduct_probability {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] : IsProbabilityMeasure μ.completion :=
  ginibre_completion_isProbabilityMeasure μ

theorem ginibreBrownian_precompose_measurePreserving {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] (Q : Measure A) (P : Measure Ω)
    (f : A → Ω) (hf : MeasurePreserving f Q P)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    IsBrownianReal (fun t x => B t (f x)) Q where
  toIsPreBrownianReal := ⟨fun I => (hB.hasLaw I).comp hf.hasLaw⟩
  cont := hf.quasiMeasurePreserving.ae hB.cont

theorem ginibre_iIndepFun_precompose_measurePreserving {A Ω ι E : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] [Finite ι] [MeasurableSpace E]
    (Q : Measure A) (P : Measure Ω) [IsProbabilityMeasure Q]
    (f : A → Ω) (hf : MeasurePreserving f Q P)
    (X : ι → Ω → E) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X P) :
    iIndepFun (fun i x => X i (f x)) Q := by
  have := Fintype.ofFinite ι
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hX i).comp hf.measurable).aemeasurable)).mpr
  have hAll := hi.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)
  have hm : Measurable (fun ω i => X i ω) := Measurable.of_eval hX
  change Q.map ((fun ω i => X i ω) ∘ f) = _
  rw [← Measure.map_map hm hf.measurable, hf.map_eq, hAll]
  congr 1
  funext i
  rw [← Measure.map_map (hX i) hf.measurable, hf.map_eq]

theorem ginibreCompletedProduct_snd_preserving {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (γ : Measure A) [IsProbabilityMeasure γ] (P : Measure Ω) [IsProbabilityMeasure P] :
    MeasurePreserving (fun x : NullMeasurableSpace (A × Ω) (γ.prod P) => x.2)
      (γ.prod P).completion P := by
  refine ⟨measurable_snd.nullMeasurable.measurable',?_⟩
  rw [ginibre_map_completion (γ.prod P) Prod.snd measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul]

theorem ginibreBrownian_completed_initial_noise_product {A Ω ι : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] [Finite ι]
    (γ : Measure A) [IsProbabilityMeasure γ] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ i, IsBrownianReal (fun t (x : NullMeasurableSpace (A × Ω) (γ.prod P)) => B i t x.2)
      (γ.prod P).completion := by
  have := Fintype.ofFinite ι
  intro i
  exact ginibreBrownian_precompose_measurePreserving _ P _ (ginibreCompletedProduct_snd_preserving γ
      P) (B i) (hB i)

theorem ginibreCompletedProduct_fst_preserving {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (γ : Measure A) (P : Measure Ω) [IsProbabilityMeasure P] :
    MeasurePreserving (fun x : NullMeasurableSpace (A × Ω) (γ.prod P) => x.1)
      (γ.prod P).completion γ := by
  refine ⟨measurable_fst.nullMeasurable.measurable',?_⟩
  rw [ginibre_map_completion (γ.prod P) Prod.fst measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

theorem ginibreCompletedProduct_initial_noise_independent {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (γ : Measure A) [IsProbabilityMeasure γ] (P : Measure Ω) [IsProbabilityMeasure P] :
    IndepFun (fun x : NullMeasurableSpace (A × Ω) (γ.prod P) => x.1)
      (fun x : NullMeasurableSpace (A × Ω) (γ.prod P) => x.2) (γ.prod P).completion := by
  have hfst := ginibreCompletedProduct_fst_preserving γ P
  have hsnd := ginibreCompletedProduct_snd_preserving γ P
  apply (indepFun_iff_map_prod_eq_prod_map_map hfst.measurable.aemeasurable
      hsnd.measurable.aemeasurable).mpr
  rw [hfst.map_eq, hsnd.map_eq]
  have he := ginibre_map_completion (γ.prod P) (id : A × Ω → A × Ω) measurable_id
  have hpair : (fun x : NullMeasurableSpace (A × Ω) (γ.prod P) => (x.1, x.2)) =
      (fun x : NullMeasurableSpace (A × Ω) (γ.prod P) => (id : A × Ω → A × Ω) x) := by
    funext x
    rfl
  rw [hpair]
  exact he.trans Measure.map_id

theorem ginibreBrownian_completed_product_independent_coordinates {A Ω ι : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] [Finite ι]
    (γ : Measure A) [IsProbabilityMeasure γ] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) :
    iIndepFun (fun i (x : NullMeasurableSpace (A × Ω) (γ.prod P)) t => B i t x.2)
      (γ.prod P).completion := by
  have := Fintype.ofFinite ι
  apply ginibre_iIndepFun_precompose_measurePreserving _ P _ (ginibreCompletedProduct_snd_preserving
      γ P)
    (fun i ω t => B i t ω) _ hiB
  intro i
  exact Measurable.of_eval (fun t => aemeasurable_iff_measurable.mp ((hB i).aemeasurable t))

end
end GinibrePoincare
