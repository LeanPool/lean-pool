/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.Api
public import LeanPool.Parikh.ActivationAlgorithm
public import LeanPool.Parikh.BoundedEnumeration

/-!
# Parikh's theorem and a certified semilinear grammar compiler

Source: doi:10.1145/321356.321364, url:https://github.com/focs-lab/parikh-theorem/tree/9c1cde93f29bbaa91542e401e074ec3cd7646880
Authors: Umang Mathur
Status: verified
Main declarations: `Parikh.parikhImage_isSemilinear_of_isContextFree`
Tags: formal-languages, context-free-grammars, semilinear-sets, verified-algorithms
MSC: 68Q45, 68Q42, 03D05
-/

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; the mathematical library and certified
compiler are preserved. The standalone JSON CLI, examples and audit tooling are
outside this import. -/

/-! The derivation-tree proof follows Ryoma Sin'ya,
*Simple proof of Parikh's theorem a la Takahashi* (arXiv:1909.09393), and
Alexander Rubtsov, *The Simplest Proof of Parikh's Theorem via Derivation Trees*
(arXiv:2301.00047). The quantitative grammar compiler is the upstream project's
constructive extension, with bounds described in its mathematical reference. -/
