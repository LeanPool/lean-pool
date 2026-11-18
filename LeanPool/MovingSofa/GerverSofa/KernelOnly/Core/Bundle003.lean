/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.PartBMiddleRows

/-!
# Part B product-cell rows 0 through 15 and assembly

Closed cache checks and product-cell rows are grouped to bound each compiler process.
-/

@[expose] public section

noncomputable section
section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartB.CellRows.Row00`.
* `KernelOnly.PartB.CellRows.Row01`.
* `KernelOnly.PartB.CellRows.Row02`.
* `KernelOnly.PartB.CellRows.Row03`.
* `KernelOnly.PartB.CellRows.Row04`.
* `KernelOnly.PartB.CellRows.Row05`.
* `KernelOnly.PartB.CellRows.Row06`.
* `KernelOnly.PartB.CellRows.Row07`.
* `KernelOnly.PartB.CellRows.Row08`.
* `KernelOnly.PartB.CellRows.Row09`.
* `KernelOnly.PartB.CellRows.Row10`.
* `KernelOnly.PartB.CellRows.Row11`.
* `KernelOnly.PartB.CellRows.Row12`.
* `KernelOnly.PartB.CellRows.Row13`.
* `KernelOnly.PartB.CellRows.Row14`.
* `KernelOnly.PartB.CellRows.Row15`.
-/

@[expose] public section

noncomputable section

section

/-!
Independent exact product-cell lower bounds for row 00.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_00 :
    ∀ j : Cell,
      targetQ < (guCellInterval (0 : Cell) j).lo ∧
      targetQ < (gvCellInterval (0 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 01.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_01 :
    ∀ j : Cell,
      targetQ < (guCellInterval (1 : Cell) j).lo ∧
      targetQ < (gvCellInterval (1 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 02.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_02 :
    ∀ j : Cell,
      targetQ < (guCellInterval (2 : Cell) j).lo ∧
      targetQ < (gvCellInterval (2 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 03.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_03 :
    ∀ j : Cell,
      targetQ < (guCellInterval (3 : Cell) j).lo ∧
      targetQ < (gvCellInterval (3 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 04.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_04 :
    ∀ j : Cell,
      targetQ < (guCellInterval (4 : Cell) j).lo ∧
      targetQ < (gvCellInterval (4 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 05.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_05 :
    ∀ j : Cell,
      targetQ < (guCellInterval (5 : Cell) j).lo ∧
      targetQ < (gvCellInterval (5 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 06.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_06 :
    ∀ j : Cell,
      targetQ < (guCellInterval (6 : Cell) j).lo ∧
      targetQ < (gvCellInterval (6 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 07.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_07 :
    ∀ j : Cell,
      targetQ < (guCellInterval (7 : Cell) j).lo ∧
      targetQ < (gvCellInterval (7 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 08.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_08 :
    ∀ j : Cell,
      targetQ < (guCellInterval (8 : Cell) j).lo ∧
      targetQ < (gvCellInterval (8 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 09.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_09 :
    ∀ j : Cell,
      targetQ < (guCellInterval (9 : Cell) j).lo ∧
      targetQ < (gvCellInterval (9 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 10.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_10 :
    ∀ j : Cell,
      targetQ < (guCellInterval (10 : Cell) j).lo ∧
      targetQ < (gvCellInterval (10 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 11.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_11 :
    ∀ j : Cell,
      targetQ < (guCellInterval (11 : Cell) j).lo ∧
      targetQ < (gvCellInterval (11 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 12.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_12 :
    ∀ j : Cell,
      targetQ < (guCellInterval (12 : Cell) j).lo ∧
      targetQ < (gvCellInterval (12 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 13.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_13 :
    ∀ j : Cell,
      targetQ < (guCellInterval (13 : Cell) j).lo ∧
      targetQ < (gvCellInterval (13 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 14.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_14 :
    ∀ j : Cell,
      targetQ < (guCellInterval (14 : Cell) j).lo ∧
      targetQ < (gvCellInterval (14 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 15.
Build all 64 row modules sequentially before the final Part B assembly.
-/

@[expose] public section

namespace GerverSofa.PartB
theorem cell_row_15 :
    ∀ j : Cell,
      targetQ < (guCellInterval (15 : Cell) j).lo ∧
      targetQ < (gvCellInterval (15 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
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

end

end

end
