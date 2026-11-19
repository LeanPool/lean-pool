/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGaussianOUProductReversal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUContinuousReversal
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Ginibre Hamiltonian Gaussian OU product reversal

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `independent_coordinate_pairs_of_independent_families`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

theorem independent_coordinate_pairs_of_independent_families
    {Ω ι A B : Type*} [MeasurableSpace Ω] [Finite ι]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → A) (Y : ι → Ω → B)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hiX : iIndepFun X P) (hiY : iIndepFun Y P)
    (hind : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P) :
    iIndepFun (fun i ω => (X i ω, Y i ω)) P := by
  have := Fintype.ofFinite ι
  have hmX : Measurable (fun ω i => X i ω) := Measurable.of_eval hX
  have hmY : Measurable (fun ω i => Y i ω) := Measurable.of_eval hY
  have hpair (i : ι) : P.map (fun ω => (X i ω, Y i ω)) = (P.map (X i)).prod (P.map (Y i)) :=
    (hind.comp (measurable_pi_apply i) (measurable_pi_apply i)).map_prod_eq_prod_map_map
      (hX i).aemeasurable (hY i).aemeasurable
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hX i).prodMk (hY i)).aemeasurable)).mpr
  let e := MeasurableEquiv.arrowProdEquivProdArrow A B ι
  apply e.measurableEmbedding.map_injective
  rw [Measure.map_map e.measurable (Measurable.of_eval (fun i => (hX i).prodMk (hY i)))]
  change P.map (fun ω => ((fun i => X i ω), (fun i => Y i ω))) = _
  rw [hind.map_prod_eq_prod_map_map hmX.aemeasurable hmY.aemeasurable,
    hiX.map_fun_eq_pi_map (fun i => (hX i).aemeasurable),
    hiY.map_fun_eq_pi_map (fun i => (hY i).aemeasurable)]
  simp_rw [hpair]
  have (i : ι) : IsProbabilityMeasure (P.map (X i)) := (by infer_instance)
  have (i : ι) : IsProbabilityMeasure (P.map (Y i)) := (by infer_instance)
  exact (measurePreserving_arrowProdEquivProdArrow A B ι (fun i => P.map (X i)) (fun i => P.map (Y
      i))).map_eq.symm

end
end GinibrePoincare
