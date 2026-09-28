/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartB.Semantics.Batch001
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
