/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PseudolineArrangements.FlagSystem
public import LeanPool.PseudolineArrangements.DoubleCover
public import LeanPool.PseudolineArrangements.Cells
public import LeanPool.PseudolineArrangements.Chirotope
public import LeanPool.PseudolineArrangements.Realizable
public import LeanPool.PseudolineArrangements.Arrangement
public import LeanPool.PseudolineArrangements.Cartographic
public import LeanPool.PseudolineArrangements.Coset
public import LeanPool.PseudolineArrangements.Orientability
public import LeanPool.PseudolineArrangements.Regular

/-!
# Chirotopes, line arrangements and flag systems of maps

Source: doi:10.1017/CBO9780511586507, url:https://github.com/TauCetiProject/TauCetiRoadmap/pull/1523
Authors: Michel Hua
Status: verified
Main declarations: `LeanPool.PseudolineArrangements.GMap.isConnected_iff_preconnected_flagGraph`,
  `LeanPool.PseudolineArrangements.GMap.isConnected_orientationDoubleCover_iff`,
  `LeanPool.PseudolineArrangements.GMap.natCard_cell_orientationDoubleCover`,
  `LeanPool.PseudolineArrangements.Chirotope.isChirotope_ofVectorsFun`,
  `LeanPool.PseudolineArrangements.Chirotope.isChirotope_reorientFun`,
  `LeanPool.PseudolineArrangements.MonotoneArrangement.chiFun_ofLines`,
  `LeanPool.PseudolineArrangements.MonotoneArrangement.isUniform_chiFun_iff`,
  `LeanPool.PseudolineArrangements.GMap.exists_monoidHom_stringCoxeterMatrix_iff`,
  `LeanPool.PseudolineArrangements.GMap.nonempty_iso_cosetGMap_iff`,
  `LeanPool.PseudolineArrangements.GMap.isOrientable_iff_not_isPretransitive_evenMonodromy`,
  `LeanPool.PseudolineArrangements.GMap.isRegular_iff_isPretransitive_aut`,
  `LeanPool.PseudolineArrangements.GMap.isRegular_ofGroup`
Tags: oriented-matroids, chirotopes, pseudoline-arrangements, combinatorial-maps, coxeter-groups
MSC: 52C40, 52C30, 05B35, 05C10, 20F55
-/
