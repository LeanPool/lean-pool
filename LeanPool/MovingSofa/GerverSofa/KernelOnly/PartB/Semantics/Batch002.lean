/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartB.Certificates.Batch001















public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartB.Certificates.Batch002















public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartB.Certificates.Batch003















public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartB.Certificates.Batch004















public import Mathlib.Tactic.FinCases
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartB.AllRows`.
-/

@[expose] public section

noncomputable section


section

/-! Assembly of the 64 independently kernel-checked product-cell rows. -/

@[expose] public section

namespace GerverSofa.PartB

theorem all_cell_lower (i j : Cell) :
    targetQ < (guCellInterval i j).lo ∧
    targetQ < (gvCellInterval i j).lo := by
  fin_cases i
  · exact cell_row_00 j
  · exact cell_row_01 j
  · exact cell_row_02 j
  · exact cell_row_03 j
  · exact cell_row_04 j
  · exact cell_row_05 j
  · exact cell_row_06 j
  · exact cell_row_07 j
  · exact cell_row_08 j
  · exact cell_row_09 j
  · exact cell_row_10 j
  · exact cell_row_11 j
  · exact cell_row_12 j
  · exact cell_row_13 j
  · exact cell_row_14 j
  · exact cell_row_15 j
  · exact cell_row_16 j
  · exact cell_row_17 j
  · exact cell_row_18 j
  · exact cell_row_19 j
  · exact cell_row_20 j
  · exact cell_row_21 j
  · exact cell_row_22 j
  · exact cell_row_23 j
  · exact cell_row_24 j
  · exact cell_row_25 j
  · exact cell_row_26 j
  · exact cell_row_27 j
  · exact cell_row_28 j
  · exact cell_row_29 j
  · exact cell_row_30 j
  · exact cell_row_31 j
  · exact cell_row_32 j
  · exact cell_row_33 j
  · exact cell_row_34 j
  · exact cell_row_35 j
  · exact cell_row_36 j
  · exact cell_row_37 j
  · exact cell_row_38 j
  · exact cell_row_39 j
  · exact cell_row_40 j
  · exact cell_row_41 j
  · exact cell_row_42 j
  · exact cell_row_43 j
  · exact cell_row_44 j
  · exact cell_row_45 j
  · exact cell_row_46 j
  · exact cell_row_47 j
  · exact cell_row_48 j
  · exact cell_row_49 j
  · exact cell_row_50 j
  · exact cell_row_51 j
  · exact cell_row_52 j
  · exact cell_row_53 j
  · exact cell_row_54 j
  · exact cell_row_55 j
  · exact cell_row_56 j
  · exact cell_row_57 j
  · exact cell_row_58 j
  · exact cell_row_59 j
  · exact cell_row_60 j
  · exact cell_row_61 j
  · exact cell_row_62 j
  · exact cell_row_63 j

end GerverSofa.PartB

end

end
