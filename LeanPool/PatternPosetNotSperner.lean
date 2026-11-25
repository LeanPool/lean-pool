/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler B. Hughes
-/

module

public import LeanPool.PatternPosetNotSperner.Defs
public import LeanPool.PatternPosetNotSperner.BoxChains
public import LeanPool.PatternPosetNotSperner.SevenPoint
public import LeanPool.PatternPosetNotSperner.Family

/-!
# Non-Sperner Intervals and Exact Deficiency Family in the Permutation Pattern Poset

Source: arxiv:1305.5569, doi:10.1016/j.jcta.2015.02.009, url:https://mathdiscoveries.org/results/pattern-poset-not-sperner/
Authors: Tyler B. Hughes
Status: verified
Main declarations: `PatternPoset.mcnamara_steingrimsson_Q9_5_false`,
  `PatternPoset.not_sperner_interval7`, `PatternPoset.interval7_card`,
  `PatternPoset.interval7_largestRank`, `PatternPoset.interval7_width`,
  `PatternPoset.family_exact_deficiency`, `PatternPoset.family_not_sperner`,
  `PatternPoset.family_largestRank`, `PatternPoset.family_width`
Tags: combinatorics, permutation-patterns, posets, sperner-property, symmetric-chain-decomposition
MSC: 05A05, 06A07
-/
