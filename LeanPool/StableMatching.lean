/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.StableMatching.Auxiliary
public import LeanPool.StableMatching.Basic
public import LeanPool.StableMatching.DeferredAcceptance
public import LeanPool.StableMatching.Optimality
public import LeanPool.StableMatching.Lattice
public import LeanPool.StableMatching.Blocking
public import LeanPool.StableMatching.Impossibility
public import LeanPool.StableMatching.Examples

/-!
# Stable matching, deferred acceptance and incentives

Source: doi:10.1007/s00182-008-0117-6, url:https://github.com/TauCetiProject/TauCetiRoadmap/pull/2346
Authors: Michel Hua
Status: verified
Main declarations: `LeanPool.StableMatching.Market.exists_isStable_man_eq_deferredAcceptance`,
  `LeanPool.StableMatching.Market.exists_isStable`,
  `LeanPool.StableMatching.Market.rankM_deferredAcceptance_le`,
  `LeanPool.StableMatching.Market.exists_isStable_manSup`,
  `LeanPool.StableMatching.Market.exists_isStable_manInf`,
  `LeanPool.StableMatching.Market.man_eq_none_iff_of_isStable`,
  `LeanPool.StableMatching.Market.woman_eq_none_iff_of_isStable`,
  `LeanPool.StableMatching.Market.not_forall_rankM_lt_deferredAcceptance`,
  `LeanPool.StableMatching.Market.rankM_deferredAcceptance_le_updateMan`,
  `LeanPool.StableMatching.not_exists_truthful_stable_mechanism`
Tags: stable-matching, deferred-acceptance, gale-shapley, matching-markets, mechanism-design
MSC: 91B68, 91A80, 05C70
-/
