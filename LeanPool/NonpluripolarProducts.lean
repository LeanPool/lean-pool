/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrent3Currents
public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrent4Bounded

/-!
# Nonpluripolar products of positive currents

Source: arxiv:0812.3674, url:https://github.com/MingchenXia/SGPT-lean/tree/76cbff42fbefc4c953a0ea0ba5b6948ac20c69b3
Authors: Mingchen Xia, Jian Wang, Siqi He, Zayn Blore
Status: verified
Main declarations: `SGPT.NPP.currentProduct_restrict`,
  `SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct_append_bounded`,
  `SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure`
Tags: pluripotential-theory, complex-analysis, measure-theory, monge-ampere
MSC: 32U05, 32W20, 32J27

The compact Kähler finiteness proof, its one-slot mass argument, and supporting complex geometry
reuse material from
[Mingchen Xia's earlier envelope-property formalization](
https://github.com/MingchenXia/envelope-property-lean/tree/bb7130411c5594e951c5923f8b82c021ce3d6c8d/EnvelopeProperty/ComplexGeometry)
(2026-10-30, Apache-2.0).
-/
