/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

module

public import LeanPool.CatalyticRegisters.BalancedProduct
public import LeanPool.CatalyticRegisters.BilinearFrobenius
public import LeanPool.CatalyticRegisters.CommRing
public import LeanPool.CatalyticRegisters.DigitSumDichotomy
public import LeanPool.CatalyticRegisters.ExtensionFieldSeparation
public import LeanPool.CatalyticRegisters.FourRegisterPowering
public import LeanPool.CatalyticRegisters.MathlibRing
public import LeanPool.CatalyticRegisters.NonVacuity
public import LeanPool.CatalyticRegisters.Pass2Soundness
public import LeanPool.CatalyticRegisters.PrimeFieldTools
public import LeanPool.CatalyticRegisters.ThreeRegisterBreakthrough

/-!
# Passive catalytic register programs over finite fields and commutative rings

Source: url:https://github.com/0thernes/catalytic-register-frontiers/tree/c80125c42956ff17e7d6d56c66d94ee9bb57ae33
Authors: Alexander S. Donahue
Status: verified
Main declarations: `Catalytic.rp_pass_two_iff`, `Catalytic.four_reg_powering_x13`,
  `Catalytic.balancedProdProg_clean`
Tags: catalytic-computation, register-programs, finite-fields, arithmetic-complexity
MSC: 68Q17, 68Q05, 12E20
-/

/-!
## Upstream Lean sources

The Apache 2.0 proofs come from Alexander S. Donahue's `catalytic-register-frontiers`,
commit `c80125c42956ff17e7d6d56c66d94ee9bb57ae33`. Lean Pool relocated the core
modules and adapted the proofs to its toolchain, Mathlib, and project checks.

The project card cites the corrected manuscript at that commit. The historical v1.0.1
manuscript remains available as [Zenodo deposit 24517199](https://doi.org/10.5281/zenodo.24517199).
-/
