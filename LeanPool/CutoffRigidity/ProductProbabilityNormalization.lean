/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Normalization of an actual separated product measure

If a product of two genuine measures is a probability measure, then that
product is exactly the product of its probability marginals. No finiteness
or normalization of the individual unnormalized factors is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory Set
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem probability_product_eq_product_marginals
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (hp : IsProbabilityMeasure (μ.prod ν)) :
    μ.prod ν = ((μ.prod ν).map Prod.fst).prod ((μ.prod ν).map Prod.snd) := by
  let := hp
  have hmass : μ univ*ν univ=1 := by
    calc
      _ = (μ.prod ν) (univ ×ˢ univ) := (Measure.prod_prod univ univ).symm
      _ = 1 := by simp
  let μ' := ν univ • μ
  let ν' := μ univ • ν
  have hμ' : IsProbabilityMeasure μ' := ⟨by
    change ν univ*μ univ=1
    rwa [mul_comm]⟩
  have hν' : IsProbabilityMeasure ν' := ⟨by
    change μ univ*ν univ=1
    exact hmass⟩
  let := hμ'
  let := hν'
  have heq : μ'.prod ν'=μ.prod ν := by
    dsimp only [μ',ν']
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      mul_comm (ν univ) (μ univ), hmass, one_smul]
  rw [← heq,Measure.map_fst_prod,Measure.map_snd_prod]
  simp

end CutoffRigidity
