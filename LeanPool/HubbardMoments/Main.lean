/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Spec
public import LeanPool.HubbardMoments.Sectors
public import LeanPool.HubbardMoments.SecondMoment
public import LeanPool.HubbardMoments.ProjectedHopping
public import LeanPool.HubbardMoments.Doublon
public import LeanPool.HubbardMoments.SchriefferWolff
public import LeanPool.HubbardMoments.FinitePopulation
public import LeanPool.HubbardMoments.TorusBand
public import LeanPool.HubbardMoments.ClosedWalks
public import LeanPool.HubbardMoments.Hubbard
public import LeanPool.HubbardMoments.Weighted

/-!
# Proofs of the claims

Each theorem proves one of the propositions in `HubbardMoments.Spec`, which states the
formalized claims from the paper.
-/

public section

namespace HubbardMoments

theorem sectorDimensions : Spec.SectorDimensions := by
  intro V _ _ a b k hkb
  exact card_sector V a b k hkb

theorem sectorDimensionsQuoted : Spec.SectorDimensionsQuoted :=
  ⟨sector_dims_L4_two_two.1, sector_dims_L4_two_two.2.1, sector_dims_L4_two_two.2.2,
    sector_dims_L5_two_one.1, sector_dims_L5_two_one.2⟩

theorem hopAverage : Spec.HopAverage := by
  intro V _ _ G _ n hn hN
  exact average_card_hops G n hn hN

theorem hopAverageRegular : Spec.HopAverageRegular := by
  intro V _ _ G _ z n hz hn hN
  exact average_card_hops_regular G hz n hn hN

theorem hopAverageTorus : Spec.HopAverageTorus := by
  intro L n hL hn
  exact average_card_hops_torus L hL n hn

theorem hopAverageTorusValues : Spec.HopAverageTorusValues :=
  ⟨average_card_hops_torus_L4_n4, average_card_hops_torus_L5_n4⟩

theorem projectedHoppingDiagonalZero : Spec.ProjectedHoppingDiagonalZero := by
  intro V σ _ G t H hH c
  exact apply_self_eq_zero hH c

theorem projectedHoppingSquareDiagonal : Spec.ProjectedHoppingSquareDiagonal := by
  intro V σ _ _ _ _ G _ t H n hH c hc
  exact sum_mul_apply_self hH hc

theorem secondMomentTheorem : Spec.SecondMomentTheorem := by
  intro V σ _ _ _ _ G _ t H n hH hB hN
  exact second_moment hH n hB hN

theorem secondMomentRegular : Spec.SecondMomentRegular := by
  intro V σ _ _ _ _ G _ t H z n hH hz hB hN
  exact second_moment_regular hH hz n hB hN

theorem secondMomentTorus : Spec.SecondMomentTorus := by
  intro σ _ _ L t H n hL hH hB
  exact second_moment_torus hL hH n hB

theorem projectedHoppingExists : Spec.ProjectedHoppingExists := by
  intro V σ _ _ G _ t ht
  exact ⟨hopMatrix G t, isProjectedHopping_hopMatrix G ht⟩

theorem pairHoppingHermitian : Spec.PairHoppingHermitian := by
  intro V _ G _ t A hA
  exact pairHopping_isHermitian G t A hA

theorem doublonFirstOrderZero : Spec.DoublonFirstOrderZero := by
  intro V _ G _ t A R' R
  exact pairHopping_doublon G t A R' R

theorem doubledPeierlsPhase : Spec.DoubledPeierlsPhase := by
  intro V _ _ G _ t A U R R' h
  exact doublonSecondOrder_adj G t A h U

theorem doublonHoppingRange : Spec.DoublonHoppingRange := by
  intro V _ _ G _ t A U R R' hne h
  exact doublonSecondOrder_of_not_adj G t A hne h U

theorem doublonOnSiteShift : Spec.DoublonOnSiteShift := by
  intro V _ _ G _ t A U R hA
  exact doublonSecondOrder_self G t A hA U R

theorem doublonOnSiteShiftTorus : Spec.DoublonOnSiteShiftTorus := by
  intro L t A U R hL hA
  exact doublonSecondOrder_self_torus hL t A hA U R

theorem torusTriangleFree : Spec.TorusTriangleFree := by
  intro L
  constructor
  · rintro h rfl
    exact torus_three_not_cliqueFree h
  · exact torus_cliqueFree_three

theorem schriefferWolffCrossTerm : Spec.SchriefferWolffCrossTerm := by
  intro V σ _ _ G H B Q hH hG hB hQ
  exact sum_mul_virtualOp_eq_zero hH hG hB hQ

theorem schriefferWolffSecondMoment : Spec.SchriefferWolffSecondMoment := by
  intro V σ _ _ G H B Q U hH hG hB hQ
  exact secondMoment_sub_virtualOp hH hG hB hQ U

theorem schriefferWolffSecondMomentTorus : Spec.SchriefferWolffSecondMomentTorus := by
  intro σ _ L H B Q U hL hH hB hQ
  exact secondMoment_sub_virtualOp_torus hL hH hB hQ U

theorem crossTermNeedsTriangleFree : Spec.CrossTermNeedsTriangleFree :=
  exists_crossTerm_ne_zero_torus_three

theorem sampleMean : Spec.SampleMean := by
  intro V _ ε k hε
  exact sampleMoment_one hε k

theorem finitePopulationVariance : Spec.FinitePopulationVariance := by
  intro V _ ε k hε hk hN
  exact sampleMoment_two_fpc hε hk hN

theorem finitePopulationFourthMoment : Spec.FinitePopulationFourthMoment := by
  intro V _ ε k hε hk
  exact sampleMoment_four hε hk

theorem independentSumSecondMoment : Spec.IndependentSumSecondMoment := by
  intro A B _ _ _ _ f g hg
  exact independent_sum_two hg

theorem independentSumFourthMoment : Spec.IndependentSumFourthMoment := by
  intro A B _ _ _ _ f g hf hg
  exact independent_sum_four hf hg

theorem torusBandMoments : Spec.TorusBandMoments := by
  intro L t hL
  exact ⟨torusBand_sum (by omega) t, torusBand_sum_sq hL t⟩

theorem freeFermionSecondMomentTorus : Spec.FreeFermionSecondMomentTorus := by
  intro L n t hL hn
  exact sampleMoment_torusBand_two hL t hn

theorem freeAndProjectedSecondMomentsAgree : Spec.FreeAndProjectedSecondMomentsAgree := by
  intro L t H n hL hH hn hB
  exact sampleMoment_torusBand_eq_secondMoment hL hH hn hB

theorem finitePopulationTable : Spec.FinitePopulationTable :=
  fpc_table

theorem closedWalkFewMoved : Spec.ClosedWalkFewMoved := by
  intro P V _ _ G walk h σ hinj hw hσ hne
  exact card_support_lt_of_closedWalk hinj hw hσ hne

theorem fourHopPermutations : Spec.FourHopPermutations := by
  intro P V _ _ G walk σ hinj hw hσ
  exact closedWalk_four hinj hw hσ

theorem fourHopExchangesOccur : Spec.FourHopExchangesOccur := by
  intro L hL
  exact ⟨exists_closedWalk_swap hL, exists_closedWalk_threeCycle hL⟩

theorem threeCycleCountAffine : Spec.ThreeCycleCountAffine := by
  intro a b
  exact choose_three_add_choose_three a b

theorem sortedTupleSignRule : Spec.SortedTupleSignRule := by
  intro O _ _ ord o o' S' S
  exact create_mul_annihilate_apply ord o o' S' S

theorem hubbardHoppingHermitian : Spec.HubbardHoppingHermitian := by
  intro V σ _ _ _ _ G _ t A ord hA
  exact hubbardHopping_isHermitian G t ord hA

theorem hubbardHoppingIsHoppingOperator : Spec.HubbardHoppingIsHoppingOperator := by
  intro V σ _ _ _ _ G _ t A ord
  exact hubbardHopping_isHoppingOperator G t A ord

theorem projectedHubbardIsProjectedHopping : Spec.ProjectedHubbardIsProjectedHopping := by
  intro V σ _ _ _ _ G _ t A ord ht hA
  exact projectedHubbard_isProjectedHopping G t ord ht hA

theorem secondMomentHubbard : Spec.SecondMomentHubbard := by
  intro V σ _ _ _ _ G _ t A ord n ht hA hB hN
  exact secondMoment_projectedHubbard G t ord ht hA n hB hN

theorem secondMomentHubbardTorus : Spec.SecondMomentHubbardTorus := by
  intro σ _ _ L t A ord n hL ht hA hB
  exact secondMoment_projectedHubbard_torus t hL ht hA ord n hB

theorem schriefferWolffHubbard : Spec.SchriefferWolffHubbard := by
  intro V σ _ _ _ _ G _ t A ord B Q U hG hB hQ
  exact secondMoment_hubbardHopping_sub_virtualOp G t A ord hG hB hQ U

theorem secondMomentWeightedTheorem : Spec.SecondMomentWeightedTheorem := by
  intro V σ _ _ _ _ w H n hH hB hN
  exact second_moment_weighted hH n hB hN

theorem secondMomentHubbardWeighted : Spec.SecondMomentHubbardWeighted := by
  intro V σ _ _ _ _ tt ord n htt hB hN
  exact secondMoment_projectedHubbardWeighted ord htt n hB hN

end HubbardMoments
