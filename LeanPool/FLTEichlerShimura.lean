/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

module

public import LeanPool.FLTEichlerShimura.Theorems.Thm_HeckeEis_exists_eichlerShimura_heckeEquivariant
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_explicitFunctionFieldModels
public import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_twelve_mul_genusFF_laurentBaseChange_gamma1_add_six_mul_natCard_doubleCoset_eq_index_add_twelve_of_isAlgClosed
public import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_isogenyEnd_eq_zsmul_of_transcendental_j
public import LeanPool.FLTEichlerShimura.Theorems.Thm_WeierstrassCurve_tateModuleRep_charpoly_frobenius

/-!
# FLT Eichler-Shimura

Source: url:https://github.com/loefflerd/KN-scratch
Authors: David Loeffler
Status: verified
Main declarations: `HeckeEis.exists_eichlerShimura_heckeEquivariant`
Tags: number-theory, modular-forms, elliptic-curves, galois-representations
MSC: 11F11
-/

/-!
## Upstream attribution

This project adapts material from David Loeffler’s loefflerd/KN-scratch fork and the original
anthropics/fermats-last-theorem release at commit aa2d8b34692b16c70f699536de0d8e75b9a3e9ef.

Fermat's Last Theorem in Lean 4
Copyright 2026 Anthropic, PBC

The original release is made available under the Apache License, Version 2.0. Its NOTICE and
ATTRIBUTION.md identify material adapted from the Imperial College London FLT project and Mathlib.
The applicable per-file notices below are reproduced from that frozen ATTRIBUTION.md; they
supplement the notices already retained in the individual imported modules.

Frozen source notices:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Path mapping: Definitions/Def_*.lean keeps the same suffix under
LeanPool/FLTEichlerShimura/Definitions/. An original P2M/Sol/S_*.lean file is imported under
LeanPool/FLTEichlerShimura/Theorems/Thm_*.lean with the same suffix.

### Applicable FLT and Mathlib per-file notices

- `Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean`
  `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper
  `FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean` — © 2025 Ruben Van de Velde; authors:
  Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
  `FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors:
  Kevin Buzzard, Salvatore Mercuri

- `P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean`
  `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors:
  Salvatore Mercuri, Kevin Buzzard

- `P2M/Sol/S_AlgebraicCurve_tateAgreement.lean`
  `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors:
  Salvatore Mercuri, Kevin Buzzard

- `P2M/Sol/S_AlgebraicCurve_tateChainRule.lean`
  `FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean` — © 2025 Ruben Van de Velde; authors:
  Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
  `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors:
  Salvatore Mercuri, Kevin Buzzard

- `P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean`
  `FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean` — © 2025 Ruben Van de Velde; authors:
  Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
  `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors:
  Salvatore Mercuri, Kevin Buzzard

- `P2M/Sol/S_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean`
  `FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean` — © 2025 Ruben Van de Velde; authors:
  Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
  `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors:
  Salvatore Mercuri, Kevin Buzzard

- `P2M/Sol/S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean`
  `FLT/Mathlib/LinearAlgebra/Countable.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard

- `Definitions/Def_FLTPrelim_FreyPackage.lean`
  `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben
  Van de Velde, Pietro Monticone (path as recorded in our port)

- `Definitions/Def_FLTPrelim_GaloisRep.lean`
  `FLT/EllipticCurve/Torsion.lean` (commit 7a87d3b25db1) — © 2024 Kevin Buzzard; authors: Kevin
  Buzzard (path as recorded in our port; the notice retained inside our file is our May port's
  generic one, the upstream notice is reproduced here)

- `P2M/Sol/S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean`
  `Mathlib/NumberTheory/ModularForms/EisensteinSeries/IsBoundedAtImInfty.lean` — Copyright (c)
  2024 Chris Birkbeck; Authors: Chris Birkbeck
  Material identified by upstream: the proof of
  `EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF` with its auxiliary norm bound, adapted
  to this repository's `eisensteinG` (≈15 lines)

- `P2M/Sol/S_EisensteinSeries_qExpansion_eisensteinG_coeff.lean`
  `Mathlib/NumberTheory/ModularForms/EisensteinSeries/IsBoundedAtImInfty.lean` — Copyright (c)
  2024 Chris Birkbeck; Authors: Chris Birkbeck
  Material identified by upstream: the same proof of
  `EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF`, adapted (≈15 lines)

The frozen upstream table records approximate extents and acknowledges incomplete detection of
small passages. Its §2 paths and author lists are recorded intermediate-port notes, except that
the FLT/EllipticCurve/Torsion.lean notice was checked at commit
7a87d3b25db19d008cd45b29edd2b92803e785b1. The table records the main FLT source snapshot as
2026-05-21 without a commit hash. This attribution preserves those limits; it is not an
independent completeness certificate for the historical provenance search.
-/
