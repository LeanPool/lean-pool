/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.FreezingRadius
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CoefficientMeasurable

/-!
# Measurable stream coefficients

Coefficient-field evaluations depend measurably on the environment.
Ported from the Apache-2.0 Superdiffusion source at
`7f20476385d4af418f110303085ad0740c9eba46`.
-/

@[expose] public section

namespace Algsuperdiff.Section5.Measurability

open Algsuperdiff.Section3
open Algsuperdiff.Section5
open Algsuperdiff.Frozen.Assumptions
open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ} {gamma nu : ℝ}

theorem measurable_streamField_apply (x : Vec d) :
    Measurable fun omega : Field.FullSample d gamma => Field.streamField omega x := by
  refine measurable_matrix_of_entries fun i j => ?_
  apply Measurable.tsum
  intro n
  have hcont (z : Vec d) : Continuous fun j : ShellField d => j z :=
    (continuous_eval_const z).comp
      (continuous_fst.comp continuous_subtype_val)
  have hvalue (z : Vec d) : Measurable fun j : ShellField d => j z :=
    (hcont z).measurable
  have hshell (z : Vec d) : Measurable fun omega : Field.FullSample d gamma =>
      omega.1.1 n z :=
    (hvalue z).comp
      ((measurable_pi_apply n).comp (measurable_subtype_coe.comp measurable_subtype_coe))
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hshell x))).sub
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hshell 0)))

theorem measurable_streamCoefficient_apply (x : Vec d) :
    Measurable fun omega : Field.FullSample d gamma => Field.streamCoefficient nu omega x := by
  exact measurable_const.add (measurable_streamField_apply x)

theorem measurable_streamCoefficient_joint :
    Measurable fun p : Field.FullSample d gamma × Vec d =>
      Field.streamCoefficient nu p.1 p.2 := by
  have hswap : Measurable
      (Function.uncurry fun x : Vec d => fun omega : Field.FullSample d gamma =>
        Field.streamCoefficient nu omega x) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun omega => Field.continuous_streamCoefficient nu omega)
      (fun x => measurable_streamCoefficient_apply x)
  exact hswap.comp measurable_swap

/-- The full stream coefficient restricted to a compact spatial carrier. -/
def streamCoefficientRestrict (nu : ℝ) (K : Set (Vec d))
    (omega : Field.FullSample d gamma) : C(K, Mat d) :=
  ⟨fun x => Field.streamCoefficient nu omega x,
    (Field.continuous_streamCoefficient nu omega).comp continuous_subtype_val⟩

@[simp] theorem streamCoefficientRestrict_apply (nu : ℝ) (K : Set (Vec d))
    (omega : Field.FullSample d gamma) (x : K) :
    streamCoefficientRestrict nu K omega x = Field.streamCoefficient nu omega x := rfl

private theorem measurable_continuousMap_of_eval {Omega : Type*}
    (mOmega : MeasurableSpace Omega) {K : Set (Vec d)} [CompactSpace K]
    {F : Omega → C(K, Mat d)} (hF : ∀ z : K, Measurable[mOmega] fun w => F w z) :
    Measurable[mOmega] F := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  exact Support.measurable_continuousMap_of_dense_evaluations mOmega hDc hDd
    (fun z _ => hF z)

/-- The full stream coefficient, restricted to any compact set, is a Borel
measurable continuous matrix field. -/
theorem measurable_streamCoefficientRestrict (nu : ℝ) (K : Set (Vec d))
    [CompactSpace K] :
    Measurable (streamCoefficientRestrict (d := d) (gamma := gamma) nu K) := by
  refine measurable_continuousMap_of_eval _ fun z => ?_
  exact measurable_streamCoefficient_apply (nu := nu) (x := (z : Vec d))


end

end Algsuperdiff.Section5.Measurability
