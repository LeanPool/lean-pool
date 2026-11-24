/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: project entry point. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiSepticGlobalError
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SuzukiGlobalError

/-!
# Cancellation-aware error bounds for the fourth-order Suzuki formula

Source: arxiv:2611.27359, url:https://github.com/BryceT233/Foresight-Quantum-Formalization-Projects/tree/40b042ff69f569bbc8d94273620ee0b59d272455
Authors: Bingyu Xia, Jue Xu, Yue Wang
Status: verified
Main declarations: `FQFP.BCH.norm_suzukiProduct_pow_sub_septic_midpoint_le_of_skewAdjoint`,
  `FQFP.BCH.isBigO_fiveStageStrangProduct_pow_sub_septic_midpoint`,
  `FQFP.BCH.tendsto_nat_pow_four_mul_norm_suzukiProduct_pow_sub_exp_of_skewAdjoint`
Tags: functional-analysis, product-formulas, normed-algebras
MSC: 47D06, 65J10, 46H30
-/
