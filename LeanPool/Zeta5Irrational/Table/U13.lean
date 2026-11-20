/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.RationalLogCertificate
import LeanPool.Zeta5Irrational.Table.RationalSeries

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U13) -/

@[expose] public section

open Finset

namespace Zeta5Irrational

open scoped LogarithmCertificates

lemma U_160_1 :
    Uω (aρ 1) (bρ 1) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(22679308077571814145547 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4141046962326717 / 40000000000000000 : ℝ) ≤
      (-(22679308077571814145547 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4141046962326717 / 40000000000000000 : ℚ))
        (r' := (4141046962326717 / 2500000000000000 : ℚ))
        (U := (-(22679308077571814145547 / 10000000000000000000000 : ℚ)))
        (U' := (5046579134428185854453 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (3519728384093 / 32000000000000 : ℚ))
      (s := (32347049350603 / 312500000000000 : ℚ))
      (q := (4141046962326717 / 40000000000000000 : ℚ))
      (U := (-(22679308077571814145547 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_160_2 :
    Uω (aρ 2) (bρ 2) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(22920417791434948469573 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4042396357536883 / 40000000000000000 : ℝ) ≤
      (-(22920417791434948469573 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4042396357536883 / 40000000000000000 : ℚ))
        (r' := (4042396357536883 / 2500000000000000 : ℚ))
        (U := (-(22920417791434948469573 / 10000000000000000000000 : ℚ)))
        (U' := (4805469420565051530427 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (3519728384093 / 32000000000000 : ℚ))
      (s := (1009549289334379 / 10000000000000000 : ℚ))
      (q := (4042396357536883 / 40000000000000000 : ℚ))
      (U := (-(22920417791434948469573 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_160_3 :
    Uω (aρ 3) (bρ 3) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(23429892300799022833847 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (768320980768329 / 8000000000000000 : ℝ) ≤
      (-(23429892300799022833847 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (768320980768329 / 8000000000000000 : ℚ))
        (r' := (768320980768329 / 500000000000000 : ℚ))
        (U := (-(23429892300799022833847 / 10000000000000000000000 : ℚ)))
        (U' := (4295994911200977166153 / 10000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (3519728384093 / 32000000000000 : ℚ))
      (s := (23913741720919 / 250000000000000 : ℚ))
      (q := (768320980768329 / 8000000000000000 : ℚ))
      (U := (-(23429892300799022833847 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_160_4 :
    Uω (aρ 4) (bρ 4) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(24373512065536270100317 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (699136227986493 / 8000000000000000 : ℝ) ≤
      (-(24373512065536270100317 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (699136227986493 / 8000000000000000 : ℚ))
        (r' := (699136227986493 / 500000000000000 : ℚ))
        (U := (-(24373512065536270100317 / 10000000000000000000000 : ℚ)))
        (U' := (3352375146463729899683 / 10000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (3519728384093 / 32000000000000 : ℚ))
      (s := (86188196794717 / 1000000000000000 : ℚ))
      (q := (699136227986493 / 8000000000000000 : ℚ))
      (U := (-(24373512065536270100317 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_160_5 :
    Uω (aρ 5) (bρ 5) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(26154357087978048520417 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2925436628593717 / 40000000000000000 : ℝ) ≤
      (-(26154357087978048520417 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2925436628593717 / 40000000000000000 : ℚ))
        (r' := (2925436628593717 / 2500000000000000 : ℚ))
        (U := (-(26154357087978048520417 / 10000000000000000000000 : ℚ)))
        (U' := (1571530124021951479583 / 10000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (3519728384093 / 32000000000000 : ℚ))
      (s := (173737407903199 / 2500000000000000 : ℚ))
      (q := (2925436628593717 / 40000000000000000 : ℚ))
      (U := (-(26154357087978048520417 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_160_6 :
    Uω (aρ 6) (bρ 6) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(30576880569535722827721 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1879848889828579 / 40000000000000000 : ℝ) ≤
      (-(30576880569535722827721 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1879848889828579 / 40000000000000000 : ℚ))
        (r' := (1879848889828579 / 1250000000000000 : ℚ))
        (U := (-(30576880569535722827721 / 10000000000000000000000 : ℚ)))
        (U' := (4080478445464277172279 / 10000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (3519728384093 / 32000000000000 : ℚ))
      (s := (339396137370227 / 10000000000000000 : ℚ))
      (q := (1879848889828579 / 40000000000000000 : ℚ))
      (U := (-(30576880569535722827721 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_160_7 :
    Uω (aρ 7) (bρ 7) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_160_8 :
    Uω (aρ 8) (bρ 8) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_160_9 :
    Uω (aρ 9) (bρ 9) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_160_10 :
    Uω (aρ 10) (bρ 10) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_160_11 :
    Uω (aρ 11) (bρ 11) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_160_12 :
    Uω (aρ 12) (bρ 12) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_160_13 :
    Uω (aρ 13) (bρ 13) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_160_14 :
    Uω (aρ 14) (bρ 14) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_160_15 :
    Uω (aρ 15) (bρ 15) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_160_16 :
    Uω (aρ 16) (bρ 16) (3519728384093 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_160 :
    Uρ (3519728384093 / 32000000000000 : ℝ) ≤
      (-(23235726291618061649999 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_160_1 U_160_2 U_160_3 U_160_4 U_160_5 U_160_6 U_160_7 U_160_8 U_160_9 U_160_10
    U_160_11 U_160_12 U_160_13 U_160_14 U_160_15 U_160_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_161_1 :
    Uω (aρ 1) (bρ 1) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(22645518540262755321593 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8310126069809573 / 80000000000000000 : ℝ) ≤
      (-(22645518540262755321593 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8310126069809573 / 80000000000000000 : ℚ))
        (r' := (8310126069809573 / 5000000000000000 : ℚ))
        (U := (-(22645518540262755321593 / 10000000000000000000000 : ℚ)))
        (U' := (5080368671737244678407 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (7061879112973 / 64000000000000 : ℚ))
      (s := (519305062067681 / 5000000000000000 : ℚ))
      (q := (8310126069809573 / 80000000000000000 : ℚ))
      (U := (-(22645518540262755321593 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_161_2 :
    Uω (aρ 2) (bρ 2) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(22885774473786439499311 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8112849690563841 / 80000000000000000 : ℝ) ≤
      (-(22885774473786439499311 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8112849690563841 / 80000000000000000 : ℚ))
        (r' := (8112849690563841 / 5000000000000000 : ℚ))
        (U := (-(22885774473786439499311 / 10000000000000000000000 : ℚ)))
        (U' := (4840112738213560500689 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (7061879112973 / 64000000000000 : ℚ))
      (s := (1013060041833929 / 10000000000000000 : ℚ))
      (q := (8112849690563841 / 80000000000000000 : ℚ))
      (U := (-(22885774473786439499311 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_161_3 :
    Uω (aρ 3) (bρ 3) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(4678666681552500330723 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7711350179937309 / 80000000000000000 : ℝ) ≤
      (-(4678666681552500330723 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7711350179937309 / 80000000000000000 : ℚ))
        (r' := (7711350179937309 / 5000000000000000 : ℚ))
        (U := (-(4678666681552500330723 / 2000000000000000000000 : ℚ)))
        (U' := (866510760847499669277 / 2000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (7061879112973 / 64000000000000 : ℚ))
      (s := (15001269851989 / 156250000000000 : ℚ))
      (q := (7711350179937309 / 80000000000000000 : ℚ))
      (U := (-(4678666681552500330723 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_161_4 :
    Uω (aρ 4) (bρ 4) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(12166473716122874792837 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (280791203339793 / 3200000000000000 : ℝ) ≤
      (-(12166473716122874792837 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (280791203339793 / 3200000000000000 : ℚ))
        (r' := (280791203339793 / 200000000000000 : ℚ))
        (U := (-(12166473716122874792837 / 5000000000000000000000 : ℚ)))
        (U' := (1696469889877125207163 / 5000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (7061879112973 / 64000000000000 : ℚ))
      (s := (34619317099267 / 400000000000000 : ℚ))
      (q := (280791203339793 / 3200000000000000 : ℚ))
      (U := (-(12166473716122874792837 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_161_5 :
    Uω (aρ 5) (bρ 5) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(26104083312985725933909 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5880361868833621 / 80000000000000000 : ℝ) ≤
      (-(26104083312985725933909 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5880361868833621 / 80000000000000000 : ℚ))
        (r' := (5880361868833621 / 5000000000000000 : ℚ))
        (U := (-(26104083312985725933909 / 10000000000000000000000 : ℚ)))
        (U' := (1621803899014274066091 / 10000000000000000000000 : ℚ))
        4 6 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (7061879112973 / 64000000000000 : ℚ))
      (s := (349409146575687 / 5000000000000000 : ℚ))
      (q := (5880361868833621 / 80000000000000000 : ℚ))
      (U := (-(26104083312985725933909 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_161_6 :
    Uω (aρ 6) (bρ 6) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(30474581016948763726831 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3798356722211609 / 80000000000000000 : ℝ) ≤
      (-(30474581016948763726831 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3798356722211609 / 80000000000000000 : ℚ))
        (r' := (3798356722211609 / 2500000000000000 : ℚ))
        (U := (-(30474581016948763726831 / 10000000000000000000000 : ℚ)))
        (U' := (4182777998051236273169 / 10000000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (7061879112973 / 64000000000000 : ℚ))
      (s := (345557381635871 / 10000000000000000 : ℚ))
      (q := (3798356722211609 / 80000000000000000 : ℚ))
      (U := (-(30474581016948763726831 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_161_7 :
    Uω (aρ 7) (bρ 7) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_161_8 :
    Uω (aρ 8) (bρ 8) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_161_9 :
    Uω (aρ 9) (bρ 9) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_161_10 :
    Uω (aρ 10) (bρ 10) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_161_11 :
    Uω (aρ 11) (bρ 11) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_161_12 :
    Uω (aρ 12) (bρ 12) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_161_13 :
    Uω (aρ 13) (bρ 13) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_161_14 :
    Uω (aρ 14) (bρ 14) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_161_15 :
    Uω (aρ 15) (bρ 15) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_161_16 :
    Uω (aρ 16) (bρ 16) (7061879112973 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_161 :
    Uρ (7061879112973 / 64000000000000 : ℝ) ≤
      (-(725589995154055185789 / 312500000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_161_1 U_161_2 U_161_3 U_161_4 U_161_5 U_161_6 U_161_7 U_161_8 U_161_9 U_161_10
    U_161_11 U_161_12 U_161_13 U_161_14 U_161_15 U_161_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_162_1 :
    Uω (aρ 1) (bρ 1) (44276884111 / 400000000000 : ℝ) ≤
      (-(22611842825845109650421 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2084539546656537 / 20000000000000000 : ℝ) ≤
      (-(22611842825845109650421 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2084539546656537 / 20000000000000000 : ℚ))
        (r' := (2084539546656537 / 1250000000000000 : ℚ))
        (U := (-(22611842825845109650421 / 10000000000000000000000 : ℚ)))
        (U' := (5114044386154890349579 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (44276884111 / 400000000000 : ℚ))
      (s := (1042114661966537 / 10000000000000000 : ℚ))
      (q := (2084539546656537 / 20000000000000000 : ℚ))
      (U := (-(22611842825845109650421 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_162_2 :
    Uω (aρ 2) (bρ 2) (44276884111 / 400000000000 : ℝ) ≤
      (-(5712812751008120059167 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (101761330820619 / 1000000000000000 : ℝ) ≤
      (-(5712812751008120059167 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (101761330820619 / 1000000000000000 : ℚ))
        (r' := (101761330820619 / 62500000000000 : ℚ))
        (U := (-(5712812751008120059167 / 2500000000000000000000 : ℚ)))
        (U' := (1218659051991879940833 / 2500000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (44276884111 / 400000000000 : ℚ))
      (s := (50828537211619 / 500000000000000 : ℚ))
      (q := (101761330820619 / 1000000000000000 : ℚ))
      (U := (-(5712812751008120059167 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_162_3 :
    Uω (aρ 3) (bρ 3) (44276884111 / 400000000000 : ℝ) ≤
      (-(364951699124394211791 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (386974486564303 / 4000000000000000 : ℝ) ≤
      (-(364951699124394211791 / 156250000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (386974486564303 / 4000000000000000 : ℚ))
        (r' := (386974486564303 / 250000000000000 : ℚ))
        (U := (-(364951699124394211791 / 156250000000000000000 : ℚ)))
        (U' := (68265288563105788209 / 156250000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (44276884111 / 400000000000 : ℚ))
      (s := (192722533398303 / 2000000000000000 : ℚ))
      (q := (386974486564303 / 4000000000000000 : ℚ))
      (U := (-(364951699124394211791 / 156250000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_162_4 :
    Uω (aρ 4) (bρ 4) (44276884111 / 400000000000 : ℝ) ≤
      (-(12146275602580457198217 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (881024337506673 / 10000000000000000 : ℝ) ≤
      (-(12146275602580457198217 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (881024337506673 / 10000000000000000 : ℚ))
        (r' := (881024337506673 / 625000000000000 : ℚ))
        (U := (-(12146275602580457198217 / 5000000000000000000000 : ℚ)))
        (U' := (1716668003419542801783 / 5000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (44276884111 / 400000000000 : ℚ))
      (s := (434541545124173 / 5000000000000000 : ℚ))
      (q := (881024337506673 / 10000000000000000 : ℚ))
      (U := (-(12146275602580457198217 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_162_5 :
    Uω (aρ 5) (bρ 5) (44276884111 / 400000000000 : ℝ) ≤
      (-(26054086950097842529433 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (147745878897207 / 2000000000000000 : ℝ) ≤
      (-(26054086950097842529433 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (147745878897207 / 2000000000000000 : ℚ))
        (r' := (147745878897207 / 125000000000000 : ℚ))
        (U := (-(26054086950097842529433 / 10000000000000000000000 : ℚ)))
        (U' := (1671800261902157470567 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (44276884111 / 400000000000 : ℚ))
      (s := (70268312354207 / 1000000000000000 : ℚ))
      (q := (147745878897207 / 2000000000000000 : ℚ))
      (U := (-(26054086950097842529433 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_162_6 :
    Uω (aρ 6) (bρ 6) (44276884111 / 400000000000 : ℝ) ≤
      (-(7593519709594403117721 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (959180877277593 / 20000000000000000 : ℝ) ≤
      (-(7593519709594403117721 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (959180877277593 / 20000000000000000 : ℚ))
        (r' := (959180877277593 / 625000000000000 : ℚ))
        (U := (-(7593519709594403117721 / 2500000000000000000000 : ℚ)))
        (U' := (1070820044155596882279 / 2500000000000000000000 : ℚ))
        5 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (44276884111 / 400000000000 : ℚ))
      (s := (351645586987593 / 10000000000000000 : ℚ))
      (q := (959180877277593 / 20000000000000000 : ℚ))
      (U := (-(7593519709594403117721 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_162_7 :
    Uω (aρ 7) (bρ 7) (44276884111 / 400000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_162_8 :
    Uω (aρ 8) (bρ 8) (44276884111 / 400000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_162_9 :
    Uω (aρ 9) (bρ 9) (44276884111 / 400000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_162_10 :
    Uω (aρ 10) (bρ 10) (44276884111 / 400000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_162_11 :
    Uω (aρ 11) (bρ 11) (44276884111 / 400000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_162_12 :
    Uω (aρ 12) (bρ 12) (44276884111 / 400000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_162_13 :
    Uω (aρ 13) (bρ 13) (44276884111 / 400000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_162_14 :
    Uω (aρ 14) (bρ 14) (44276884111 / 400000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_162_15 :
    Uω (aρ 15) (bρ 15) (44276884111 / 400000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_162_16 :
    Uω (aρ 16) (bρ 16) (44276884111 / 400000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_162 :
    Uρ (44276884111 / 400000000000 : ℝ) ≤
      (-(1450138413038403161583 / 625000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_162_1 U_162_2 U_162_3 U_162_4 U_162_5 U_162_6 U_162_7 U_162_8 U_162_9 U_162_10
    U_162_11 U_162_12 U_162_13 U_162_14 U_162_15 U_162_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_163_1 :
    Uω (aρ 1) (bρ 1) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(2822285021227761372561 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1673238055077623 / 16000000000000000 : ℝ) ≤
      (-(2822285021227761372561 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1673238055077623 / 16000000000000000 : ℚ))
        (r' := (1673238055077623 / 1000000000000000 : ℚ))
        (U := (-(2822285021227761372561 / 1250000000000000000000 : ℚ)))
        (U' := (643450880272238627439 / 1250000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (7106723802547 / 64000000000000 : ℚ))
      (s := (52280959639203 / 500000000000000 : ℚ))
      (q := (1673238055077623 / 16000000000000000 : ℚ))
      (U := (-(2822285021227761372561 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_163_2 :
    Uω (aρ 2) (bρ 2) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(22816846554124106986407 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8168963042399931 / 80000000000000000 : ℝ) ≤
      (-(22816846554124106986407 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8168963042399931 / 80000000000000000 : ℚ))
        (r' := (8168963042399931 / 5000000000000000 : ℚ))
        (U := (-(22816846554124106986407 / 10000000000000000000000 : ℚ)))
        (U' := (4909040657875893013593 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (7106723802547 / 64000000000000 : ℚ))
      (s := (510040698523507 / 5000000000000000 : ℚ))
      (q := (8168963042399931 / 80000000000000000 : ℚ))
      (U := (-(22816846554124106986407 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_163_3 :
    Uω (aρ 3) (bρ 3) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(23320617319657831171039 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7767628470721819 / 80000000000000000 : ℝ) ≤
      (-(23320617319657831171039 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7767628470721819 / 80000000000000000 : ℚ))
        (r' := (7767628470721819 / 5000000000000000 : ℚ))
        (U := (-(23320617319657831171039 / 10000000000000000000000 : ℚ)))
        (U' := (4405269892342168828961 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (7106723802547 / 64000000000000 : ℚ))
      (s := (483571930238743 / 5000000000000000 : ℚ))
      (q := (7767628470721819 / 80000000000000000 : ℚ))
      (U := (-(23320617319657831171039 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_163_4 :
    Uω (aρ 4) (bρ 4) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(24252321955188649295791 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7076606168984419 / 80000000000000000 : ℝ) ≤
      (-(24252321955188649295791 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7076606168984419 / 80000000000000000 : ℚ))
        (r' := (7076606168984419 / 5000000000000000 : ℚ))
        (U := (-(24252321955188649295791 / 10000000000000000000000 : ℚ)))
        (U' := (3473565256811350704209 / 10000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (7106723802547 / 64000000000000 : ℚ))
      (s := (109085308263517 / 1250000000000000 : ℚ))
      (q := (7076606168984419 / 80000000000000000 : ℚ))
      (U := (-(24252321955188649295791 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_163_5 :
    Uω (aρ 5) (bρ 5) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(26004364686440584843293 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5939293369830159 / 80000000000000000 : ℝ) ≤
      (-(26004364686440584843293 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5939293369830159 / 80000000000000000 : ℚ))
        (r' := (5939293369830159 / 5000000000000000 : ℚ))
        (U := (-(26004364686440584843293 / 10000000000000000000000 : ℚ)))
        (U' := (1721522525559415156707 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (7106723802547 / 64000000000000 : ℚ))
      (s := (706544185654571 / 10000000000000000 : ℚ))
      (q := (5939293369830159 / 80000000000000000 : ℚ))
      (U := (-(26004364686440584843293 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_163_6 :
    Uω (aρ 6) (bρ 6) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(15137646071887000568089 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3874813059751239 / 80000000000000000 : ℝ) ≤
      (-(15137646071887000568089 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3874813059751239 / 80000000000000000 : ℚ))
        (r' := (3874813059751239 / 2500000000000000 : ℚ))
        (U := (-(15137646071887000568089 / 5000000000000000000000 : ℚ)))
        (U' := (2191033435612999431911 / 5000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (7106723802547 / 64000000000000 : ℚ))
      (s := (357664483274841 / 10000000000000000 : ℚ))
      (q := (3874813059751239 / 80000000000000000 : ℚ))
      (U := (-(15137646071887000568089 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_163_7 :
    Uω (aρ 7) (bρ 7) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_163_8 :
    Uω (aρ 8) (bρ 8) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_163_9 :
    Uω (aρ 9) (bρ 9) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_163_10 :
    Uω (aρ 10) (bρ 10) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_163_11 :
    Uω (aρ 11) (bρ 11) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_163_12 :
    Uω (aρ 12) (bρ 12) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_163_13 :
    Uω (aρ 13) (bρ 13) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_163_14 :
    Uω (aρ 14) (bρ 14) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_163_15 :
    Uω (aρ 15) (bρ 15) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_163_16 :
    Uω (aρ 16) (bρ 16) (7106723802547 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_163 :
    Uρ (7106723802547 / 64000000000000 : ℝ) ≤
      (-(23185723736921093732363 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_163_1 U_163_2 U_163_3 U_163_4 U_163_5 U_163_6 U_163_7 U_163_8 U_163_9 U_163_10
    U_163_11 U_163_12 U_163_13 U_163_14 U_163_15 U_163_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_164_1 :
    Uω (aρ 1) (bρ 1) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(4508965963075115482201 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4197111168188307 / 40000000000000000 : ℝ) ≤
      (-(4508965963075115482201 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4197111168188307 / 40000000000000000 : ℚ))
        (r' := (4197111168188307 / 2500000000000000 : ℚ))
        (U := (-(4508965963075115482201 / 2000000000000000000000 : ℚ)))
        (U' := (1036211479324884517799 / 2000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (3564573073667 / 32000000000000 : ℚ))
      (s := (131140464582277 / 1250000000000000 : ℚ))
      (q := (4197111168188307 / 40000000000000000 : ℚ))
      (U := (-(4508965963075115482201 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_164_2 :
    Uω (aρ 2) (bρ 2) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(2278256030458170454529 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4098509711427897 / 40000000000000000 : ℝ) ≤
      (-(2278256030458170454529 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4098509711427897 / 40000000000000000 : ℚ))
        (r' := (4098509711427897 / 2500000000000000 : ℚ))
        (U := (-(2278256030458170454529 / 1000000000000000000000 : ℚ)))
        (U' := (494332690741829545471 / 1000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (3564573073667 / 32000000000000 : ℚ))
      (s := (1023592000788011 / 10000000000000000 : ℚ))
      (q := (4098509711427897 / 40000000000000000 : ℚ))
      (U := (-(2278256030458170454529 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_164_3 :
    Uω (aρ 3) (bρ 3) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(23284458156104073445189 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3897883203552751 / 40000000000000000 : ℝ) ≤
      (-(23284458156104073445189 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3897883203552751 / 40000000000000000 : ℚ))
        (r' := (3897883203552751 / 2500000000000000 : ℚ))
        (U := (-(23284458156104073445189 / 10000000000000000000000 : ℚ)))
        (U' := (4441429055895926554811 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (3564573073667 / 32000000000000 : ℚ))
      (s := (485337426600219 / 5000000000000000 : ℚ))
      (q := (3897883203552751 / 40000000000000000 : ℚ))
      (U := (-(23284458156104073445189 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_164_4 :
    Uω (aρ 4) (bρ 4) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(2421225827178593245939 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3552507264537567 / 40000000000000000 : ℝ) ≤
      (-(2421225827178593245939 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3552507264537567 / 40000000000000000 : ℚ))
        (r' := (3552507264537567 / 2500000000000000 : ℚ))
        (U := (-(2421225827178593245939 / 1000000000000000000000 : ℚ)))
        (U' := (351362894021406754061 / 1000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (3564573073667 / 32000000000000 : ℚ))
      (s := (438140532378923 / 5000000000000000 : ℚ))
      (q := (3552507264537567 / 40000000000000000 : ℚ))
      (U := (-(2421225827178593245939 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_164_5 :
    Uω (aρ 5) (bρ 5) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(5190982654415919228157 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2984368378214133 / 40000000000000000 : ℝ) ≤
      (-(5190982654415919228157 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2984368378214133 / 40000000000000000 : ℚ))
        (r' := (2984368378214133 / 2500000000000000 : ℚ))
        (U := (-(5190982654415919228157 / 2000000000000000000000 : ℚ)))
        (U' := (354194787984080771843 / 2000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (3564573073667 / 32000000000000 : ℚ))
      (s := (710401540931129 / 10000000000000000 : ℚ))
      (q := (2984368378214133 / 40000000000000000 : ℚ))
      (U := (-(5190982654415919228157 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_164_6 :
    Uω (aρ 6) (bρ 6) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(30178145148616695910741 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1956319570663707 / 40000000000000000 : ℝ) ≤
      (-(30178145148616695910741 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1956319570663707 / 40000000000000000 : ℚ))
        (r' := (1956319570663707 / 1250000000000000 : ℚ))
        (U := (-(30178145148616695910741 / 10000000000000000000000 : ℚ)))
        (U' := (4479213866383304089259 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (3564573073667 / 32000000000000 : ℚ))
      (s := (90904378073979 / 2500000000000000 : ℚ))
      (q := (1956319570663707 / 40000000000000000 : ℚ))
      (U := (-(30178145148616695910741 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_164_7 :
    Uω (aρ 7) (bρ 7) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_164_8 :
    Uω (aρ 8) (bρ 8) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_164_9 :
    Uω (aρ 9) (bρ 9) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_164_10 :
    Uω (aρ 10) (bρ 10) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_164_11 :
    Uω (aρ 11) (bρ 11) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_164_12 :
    Uω (aρ 12) (bρ 12) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_164_13 :
    Uω (aρ 13) (bρ 13) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_164_14 :
    Uω (aρ 14) (bρ 14) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_164_15 :
    Uω (aρ 15) (bρ 15) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_164_16 :
    Uω (aρ 16) (bρ 16) (3564573073667 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_164 :
    Uρ (3564573073667 / 32000000000000 : ℝ) ≤
      (-(23169400871890508402437 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_164_1 U_164_2 U_164_3 U_164_4 U_164_5 U_164_6 U_164_7 U_164_8 U_164_9 U_164_10
    U_164_11 U_164_12 U_164_13 U_164_14 U_164_15 U_164_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_165_1 :
    Uω (aρ 1) (bρ 1) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(225114910132635713543 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8422254369869049 / 80000000000000000 : ℝ) ≤
      (-(225114910132635713543 / 100000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8422254369869049 / 80000000000000000 : ℚ))
        (r' := (8422254369869049 / 5000000000000000 : ℚ))
        (U := (-(225114910132635713543 / 100000000000000000000 : ℚ)))
        (U' := (52143961987364286457 / 100000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (7151568492121 / 64000000000000 : ℚ))
      (s := (263157058414589 / 2500000000000000 : ℚ))
      (q := (8422254369869049 / 80000000000000000 : ℚ))
      (U := (-(225114910132635713543 / 100000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_165_2 :
    Uω (aρ 2) (bρ 2) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(11374195722188479028337 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8225075609029889 / 80000000000000000 : ℝ) ≤
      (-(11374195722188479028337 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8225075609029889 / 80000000000000000 : ℚ))
        (r' := (8225075609029889 / 5000000000000000 : ℚ))
        (U := (-(11374195722188479028337 / 5000000000000000000000 : ℚ)))
        (U' := (2488747883811520971663 / 5000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (7151568492121 / 64000000000000 : ℚ))
      (s := (513551277979283 / 5000000000000000 : ℚ))
      (q := (8225075609029889 / 80000000000000000 : ℚ))
      (U := (-(11374195722188479028337 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_165_3 :
    Uω (aρ 3) (bρ 3) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(23248430285377622815949 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7823903549169049 / 80000000000000000 : ℝ) ≤
      (-(23248430285377622815949 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7823903549169049 / 80000000000000000 : ℚ))
        (r' := (7823903549169049 / 5000000000000000 : ℚ))
        (U := (-(23248430285377622815949 / 10000000000000000000000 : ℚ)))
        (U' := (4477456926622377184051 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (7151568492121 / 64000000000000 : ℚ))
      (s := (243551411835839 / 2500000000000000 : ℚ))
      (q := (7823903549169049 / 80000000000000000 : ℚ))
      (U := (-(23248430285377622815949 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_165_4 :
    Uω (aρ 4) (bρ 4) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(24172358762633393102107 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7133419818469869 / 80000000000000000 : ℝ) ≤
      (-(24172358762633393102107 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7133419818469869 / 80000000000000000 : ℚ))
        (r' := (7133419818469869 / 5000000000000000 : ℚ))
        (U := (-(24172358762633393102107 / 10000000000000000000000 : ℚ)))
        (U' := (3553528449366606897893 / 10000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (7151568492121 / 64000000000000 : ℚ))
      (s := (879878895733561 / 10000000000000000 : ℚ))
      (q := (7133419818469869 / 80000000000000000 : ℚ))
      (U := (-(24172358762633393102107 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_165_5 :
    Uω (aρ 5) (bρ 5) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(25905729518360809311063 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5998165555909053 / 80000000000000000 : ℝ) ≤
      (-(25905729518360809311063 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (5998165555909053 / 80000000000000000 : ℚ))
        (r' := (5998165555909053 / 5000000000000000 : ℚ))
        (U := (-(25905729518360809311063 / 10000000000000000000000 : ℚ)))
        (U' := (1820157693639190688937 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (7151568492121 / 64000000000000 : ℚ))
      (s := (714255249428357 / 10000000000000000 : ℚ))
      (q := (5998165555909053 / 80000000000000000 : ℚ))
      (U := (-(25905729518360809311063 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_165_6 :
    Uω (aρ 6) (bρ 6) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(30082567552000849825557 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3950214487904321 / 80000000000000000 : ℝ) ≤
      (-(30082567552000849825557 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3950214487904321 / 80000000000000000 : ℚ))
        (r' := (3950214487904321 / 2500000000000000 : ℚ))
        (U := (-(30082567552000849825557 / 10000000000000000000000 : ℚ)))
        (U' := (4574791462999150174443 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (7151568492121 / 64000000000000 : ℚ))
      (s := (184753928783587 / 5000000000000000 : ℚ))
      (q := (3950214487904321 / 80000000000000000 : ℚ))
      (U := (-(30082567552000849825557 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_165_7 :
    Uω (aρ 7) (bρ 7) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_165_8 :
    Uω (aρ 8) (bρ 8) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_165_9 :
    Uω (aρ 9) (bρ 9) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_165_10 :
    Uω (aρ 10) (bρ 10) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_165_11 :
    Uω (aρ 11) (bρ 11) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_165_12 :
    Uω (aρ 12) (bρ 12) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_165_13 :
    Uω (aρ 13) (bρ 13) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_165_14 :
    Uω (aρ 14) (bρ 14) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_165_15 :
    Uω (aρ 15) (bρ 15) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_165_16 :
    Uω (aρ 16) (bρ 16) (7151568492121 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_165 :
    Uρ (7151568492121 / 64000000000000 : ℝ) ≤
      (-(11576620047079105469959 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_165_1 U_165_2 U_165_3 U_165_4 U_165_5 U_165_6 U_165_7 U_165_8 U_165_9 U_165_10
    U_165_11 U_165_12 U_165_13 U_165_14 U_165_15 U_165_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_166_1 :
    Uω (aρ 1) (bρ 1) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(22478263021719406875639 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2112571594034783 / 20000000000000000 : ℝ) ≤
      (-(22478263021719406875639 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2112571594034783 / 20000000000000000 : ℚ))
        (r' := (2112571594034783 / 1250000000000000 : ℚ))
        (U := (-(22478263021719406875639 / 10000000000000000000000 : ℚ)))
        (U' := (5247624190280593124361 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1793497709227 / 16000000000000 : ℚ))
      (s := (264033185963227 / 2500000000000000 : ℚ))
      (q := (2112571594034783 / 20000000000000000 : ℚ))
      (U := (-(22478263021719406875639 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_166_2 :
    Uω (aρ 2) (bρ 2) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(181714713366534310893 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (257910362590861 / 2500000000000000 : ℝ) ≤
      (-(181714713366534310893 / 80000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (257910362590861 / 2500000000000000 : ℚ))
        (r' := (257910362590861 / 156250000000000 : ℚ))
        (U := (-(181714713366534310893 / 80000000000000000000 : ℚ)))
        (U' := (40092384329465689107 / 80000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1793497709227 / 16000000000000 : ℚ))
      (s := (1030613063055013 / 10000000000000000 : ℚ))
      (q := (257910362590861 / 2500000000000000 : ℚ))
      (U := (-(181714713366534310893 / 80000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_166_3 :
    Uω (aρ 3) (bρ 3) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(2901566593777723928731 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1963009976379449 / 20000000000000000 : ℝ) ≤
      (-(2901566593777723928731 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1963009976379449 / 20000000000000000 : ℚ))
        (r' := (1963009976379449 / 1250000000000000 : ℚ))
        (U := (-(2901566593777723928731 / 1250000000000000000000 : ℚ)))
        (U' := (564169307722276071269 / 1250000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1793497709227 / 16000000000000 : ℚ))
      (s := (488868122528787 / 5000000000000000 : ℚ))
      (q := (1963009976379449 / 20000000000000000 : ℚ))
      (U := (-(2901566593777723928731 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_166_4 :
    Uω (aρ 4) (bρ 4) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(12066311026658035428937 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (223806939833861 / 2500000000000000 : ℝ) ≤
      (-(12066311026658035428937 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (223806939833861 / 2500000000000000 : ℚ))
        (r' := (223806939833861 / 156250000000000 : ℚ))
        (U := (-(12066311026658035428937 / 5000000000000000000000 : ℚ)))
        (U' := (1796632579341964571063 / 5000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1793497709227 / 16000000000000 : ℚ))
      (s := (883475968414013 / 10000000000000000 : ℚ))
      (q := (223806939833861 / 2500000000000000 : ℚ))
      (U := (-(12066311026658035428937 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_166_5 :
    Uω (aρ 5) (bρ 5) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(12928405148153663752511 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1506895000779397 / 20000000000000000 : ℝ) ≤
      (-(12928405148153663752511 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1506895000779397 / 20000000000000000 : ℚ))
        (r' := (1506895000779397 / 1250000000000000 : ℚ))
        (U := (-(12928405148153663752511 / 5000000000000000000000 : ℚ)))
        (U' := (934538457846336247489 / 5000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1793497709227 / 16000000000000 : ℚ))
      (s := (359052684928761 / 5000000000000000 : ℚ))
      (q := (1506895000779397 / 20000000000000000 : ℚ))
      (U := (-(12928405148153663752511 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_166_6 :
    Uω (aρ 6) (bρ 6) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(14994246997006309491453 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (996887726049841 / 20000000000000000 : ℝ) ≤
      (-(14994246997006309491453 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (996887726049841 / 20000000000000000 : ℚ))
        (r' := (996887726049841 / 625000000000000 : ℚ))
        (U := (-(14994246997006309491453 / 5000000000000000000000 : ℚ)))
        (U' := (2334432510493690508547 / 5000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1793497709227 / 16000000000000 : ℚ))
      (s := (187669235133983 / 5000000000000000 : ℚ))
      (q := (996887726049841 / 20000000000000000 : ℚ))
      (U := (-(14994246997006309491453 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_166_7 :
    Uω (aρ 7) (bρ 7) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_166_8 :
    Uω (aρ 8) (bρ 8) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_166_9 :
    Uω (aρ 9) (bρ 9) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_166_10 :
    Uω (aρ 10) (bρ 10) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_166_11 :
    Uω (aρ 11) (bρ 11) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_166_12 :
    Uω (aρ 12) (bρ 12) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_166_13 :
    Uω (aρ 13) (bρ 13) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_166_14 :
    Uω (aρ 14) (bρ 14) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_166_15 :
    Uω (aρ 15) (bρ 15) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_166_16 :
    Uω (aρ 16) (bρ 16) (1793497709227 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_166 :
    Uρ (1793497709227 / 16000000000000 : ℝ) ≤
      (-(4627447176003051539293 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_166_1 U_166_2 U_166_3 U_166_4 U_166_5 U_166_6 U_166_7 U_166_8 U_166_9 U_166_10
    U_166_11 U_166_12 U_166_13 U_166_14 U_166_15 U_166_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_167_1 :
    Uω (aρ 1) (bρ 1) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(22445145106352584507421 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8478318355456963 / 80000000000000000 : ℝ) ≤
      (-(22445145106352584507421 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8478318355456963 / 80000000000000000 : ℚ))
        (r' := (8478318355456963 / 5000000000000000 : ℚ))
        (U := (-(22445145106352584507421 / 10000000000000000000000 : ℚ)))
        (U' := (5280742105647415492579 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (1439282636339 / 12800000000000 : ℚ))
      (s := (1059637247309397 / 10000000000000000 : ℚ))
      (q := (8478318355456963 / 80000000000000000 : ℚ))
      (U := (-(22445145106352584507421 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_167_2 :
    Uω (aρ 2) (bρ 2) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(2835050336178665111439 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8281187406447127 / 80000000000000000 : ℝ) ≤
      (-(2835050336178665111439 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8281187406447127 / 80000000000000000 : ℚ))
        (r' := (8281187406447127 / 5000000000000000 : ℚ))
        (U := (-(2835050336178665111439 / 1250000000000000000000 : ℚ)))
        (U' := (630685565321334888561 / 1250000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (1439282636339 / 12800000000000 : ℚ))
      (s := (517061761283469 / 5000000000000000 : ℚ))
      (q := (8281187406447127 / 80000000000000000 : ℚ))
      (U := (-(2835050336178665111439 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_167_3 :
    Uω (aρ 3) (bρ 3) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(2317676460388831441057 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7880175484632751 / 80000000000000000 : ℝ) ≤
      (-(2317676460388831441057 / 1000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7880175484632751 / 80000000000000000 : ℚ))
        (r' := (7880175484632751 / 5000000000000000 : ℚ))
        (U := (-(2317676460388831441057 / 1000000000000000000000 : ℚ)))
        (U' := (454912260811168558943 / 1000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (1439282636339 / 12800000000000 : ℚ))
      (s := (61329165528959 / 625000000000000 : ℚ))
      (q := (7880175484632751 / 80000000000000000 : ℚ))
      (U := (-(2317676460388831441057 / 1000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_167_4 :
    Uω (aρ 4) (bρ 4) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(24093046787011313355059 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (287608853384591 / 3200000000000000 : ℝ) ≤
      (-(24093046787011313355059 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (287608853384591 / 3200000000000000 : ℚ))
        (r' := (287608853384591 / 200000000000000 : ℚ))
        (U := (-(24093046787011313355059 / 10000000000000000000000 : ℚ)))
        (U' := (3632840424988686644941 / 10000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (1439282636339 / 12800000000000 : ℚ))
      (s := (17741445840477 / 200000000000000 : ℚ))
      (q := (287608853384591 / 3200000000000000 : ℚ))
      (U := (-(24093046787011313355059 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_167_5 :
    Uω (aρ 5) (bρ 5) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(6452038133767527073457 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1211396065534587 / 16000000000000000 : ℝ) ≤
      (-(6452038133767527073457 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1211396065534587 / 16000000000000000 : ℚ))
        (r' := (1211396065534587 / 1000000000000000 : ℚ))
        (U := (-(6452038133767527073457 / 2500000000000000000000 : ℚ)))
        (U' := (479433669232472926543 / 2500000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (1439282636339 / 12800000000000 : ℚ))
      (s := (72195195962339 / 1000000000000000 : ℚ))
      (q := (1211396065534587 / 16000000000000000 : ℚ))
      (U := (-(6452038133767527073457 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_167_6 :
    Uω (aρ 6) (bρ 6) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(29895863580366005101939 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4024659356395267 / 80000000000000000 : ℝ) ≤
      (-(29895863580366005101939 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4024659356395267 / 80000000000000000 : ℚ))
        (r' := (4024659356395267 / 2500000000000000 : ℚ))
        (U := (-(29895863580366005101939 / 10000000000000000000000 : ℚ)))
        (U' := (4761495434633994898061 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (1439282636339 / 12800000000000 : ℚ))
      (s := (381112091943973 / 10000000000000000 : ℚ))
      (q := (4024659356395267 / 80000000000000000 : ℚ))
      (U := (-(29895863580366005101939 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_167_7 :
    Uω (aρ 7) (bρ 7) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_167_8 :
    Uω (aρ 8) (bρ 8) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_167_9 :
    Uω (aρ 9) (bρ 9) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_167_10 :
    Uω (aρ 10) (bρ 10) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_167_11 :
    Uω (aρ 11) (bρ 11) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_167_12 :
    Uω (aρ 12) (bρ 12) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_167_13 :
    Uω (aρ 13) (bρ 13) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_167_14 :
    Uω (aρ 14) (bρ 14) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_167_15 :
    Uω (aρ 15) (bρ 15) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_167_16 :
    Uω (aρ 16) (bρ 16) (1439282636339 / 12800000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_167 :
    Uρ (1439282636339 / 12800000000000 : ℝ) ≤
      (-(11560691531889299496159 / 5000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_167_1 U_167_2 U_167_3 U_167_4 U_167_5 U_167_6 U_167_7 U_167_8 U_167_9 U_167_10
    U_167_11 U_167_12 U_167_13 U_167_14 U_167_15 U_167_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_168_1 :
    Uω (aρ 1) (bρ 1) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(22412136540051290770829 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (850635030808907 / 8000000000000000 : ℝ) ≤
      (-(22412136540051290770829 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (850635030808907 / 8000000000000000 : ℚ))
        (r' := (850635030808907 / 500000000000000 : ℚ))
        (U := (-(22412136540051290770829 / 10000000000000000000000 : ℚ)))
        (U' := (5313750671948709229171 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (3609417763241 / 32000000000000 : ℚ))
      (s := (212628348818891 / 2000000000000000 : ℚ))
      (q := (850635030808907 / 8000000000000000 : ℚ))
      (U := (-(22412136540051290770829 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_168_2 :
    Uω (aρ 2) (bρ 2) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(22646581213851753936333 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4154621510790221 / 40000000000000000 : ℝ) ≤
      (-(22646581213851753936333 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4154621510790221 / 40000000000000000 : ℚ))
        (r' := (4154621510790221 / 2500000000000000 : ℚ))
        (U := (-(22646581213851753936333 / 10000000000000000000000 : ℚ)))
        (U' := (5079305998148246063667 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (3609417763241 / 32000000000000 : ℚ))
      (s := (518816967488649 / 5000000000000000 : ℚ))
      (q := (4154621510790221 / 40000000000000000 : ℚ))
      (U := (-(22646581213851753936333 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_168_3 :
    Uω (aρ 3) (bρ 3) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(23141124909983015902357 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3954155147436417 / 40000000000000000 : ℝ) ≤
      (-(23141124909983015902357 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3954155147436417 / 40000000000000000 : ℚ))
        (r' := (3954155147436417 / 2500000000000000 : ℚ))
        (U := (-(23141124909983015902357 / 10000000000000000000000 : ℚ)))
        (U' := (4584762302016984097643 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (3609417763241 / 32000000000000 : ℚ))
      (s := (246199214912599 / 2500000000000000 : ℚ))
      (q := (3954155147436417 / 40000000000000000 : ℚ))
      (U := (-(23141124909983015902357 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_168_4 :
    Uω (aρ 4) (bρ 4) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(12026815812091775261959 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3609308817279277 / 40000000000000000 : ℝ) ≤
      (-(12026815812091775261959 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3609308817279277 / 40000000000000000 : ℚ))
        (r' := (3609308817279277 / 2500000000000000 : ℚ))
        (U := (-(12026815812091775261959 / 5000000000000000000000 : ℚ)))
        (U' := (1836127793908224738041 / 5000000000000000000000 : ℚ))
        4 9 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (3609417763241 / 32000000000000 : ℚ))
      (s := (445333937818413 / 5000000000000000 : ℚ))
      (q := (3609308817279277 / 40000000000000000 : ℚ))
      (U := (-(12026815812091775261959 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_168_5 :
    Uω (aρ 5) (bρ 5) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(12879876610215081971411 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3043183377059021 / 40000000000000000 : ℝ) ≤
      (-(12879876610215081971411 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (3043183377059021 / 40000000000000000 : ℚ))
        (r' := (3043183377059021 / 2500000000000000 : ℚ))
        (U := (-(12879876610215081971411 / 5000000000000000000000 : ℚ)))
        (U' := (983066995784918028589 / 5000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (3609417763241 / 32000000000000 : ℚ))
      (s := (362897537430849 / 5000000000000000 : ℚ))
      (q := (3043183377059021 / 40000000000000000 : ℚ))
      (U := (-(12879876610215081971411 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_168_6 :
    Uω (aρ 6) (bρ 6) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(7451154866094100783241 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2030775025954889 / 40000000000000000 : ℝ) ≤
      (-(7451154866094100783241 / 2500000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2030775025954889 / 40000000000000000 : ℚ))
        (r' := (2030775025954889 / 1250000000000000 : ℚ))
        (U := (-(7451154866094100783241 / 2500000000000000000000 : ℚ)))
        (U' := (1213184887655899216759 / 2500000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (3609417763241 / 32000000000000 : ℚ))
      (s := (12088477326551 / 312500000000000 : ℚ))
      (q := (2030775025954889 / 40000000000000000 : ℚ))
      (U := (-(7451154866094100783241 / 2500000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_168_7 :
    Uω (aρ 7) (bρ 7) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_168_8 :
    Uω (aρ 8) (bρ 8) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_168_9 :
    Uω (aρ 9) (bρ 9) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_168_10 :
    Uω (aρ 10) (bρ 10) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_168_11 :
    Uω (aρ 11) (bρ 11) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_168_12 :
    Uω (aρ 12) (bρ 12) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_168_13 :
    Uω (aρ 13) (bρ 13) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_168_14 :
    Uω (aρ 14) (bρ 14) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_168_15 :
    Uω (aρ 15) (bρ 15) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_168_16 :
    Uω (aρ 16) (bρ 16) (3609417763241 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_168 :
    Uρ (3609417763241 / 32000000000000 : ℝ) ≤
      (-(2310567680468791145093 / 1000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_168_1 U_168_2 U_168_3 U_168_4 U_168_5 U_168_6 U_168_7 U_168_8 U_168_9 U_168_10
    U_168_11 U_168_12 U_168_13 U_168_14 U_168_15 U_168_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_169_1 :
    Uω (aρ 1) (bρ 1) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(22379236602886479923973 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1706876446859697 / 16000000000000000 : ℝ) ≤
      (-(22379236602886479923973 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1706876446859697 / 16000000000000000 : ℚ))
        (r' := (1706876446859697 / 1000000000000000 : ℚ))
        (U := (-(22379236602886479923973 / 10000000000000000000000 : ℚ)))
        (U' := (5346650609113520076027 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (7241257871269 / 64000000000000 : ℚ))
      (s := (13333077928423 / 125000000000000 : ℚ))
      (q := (1706876446859697 / 16000000000000000 : ℚ))
      (U := (-(22379236602886479923973 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_169_2 :
    Uω (aρ 2) (bρ 2) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(22612873965720201807563 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8337298450213229 / 80000000000000000 : ℝ) ≤
      (-(22612873965720201807563 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8337298450213229 / 80000000000000000 : ℚ))
        (r' := (8337298450213229 / 5000000000000000 : ℚ))
        (U := (-(22612873965720201807563 / 10000000000000000000000 : ℚ)))
        (U' := (5113013246279798192437 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (7241257871269 / 64000000000000 : ℚ))
      (s := (520572150381263 / 5000000000000000 : ℚ))
      (q := (8337298450213229 / 80000000000000000 : ℚ))
      (U := (-(22612873965720201807563 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_169_3 :
    Uω (aρ 3) (bρ 3) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(23105612742314276111357 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7936444344477101 / 80000000000000000 : ℝ) ≤
      (-(23105612742314276111357 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7936444344477101 / 80000000000000000 : ℚ))
        (r' := (7936444344477101 / 5000000000000000 : ℚ))
        (U := (-(23105612742314276111357 / 10000000000000000000000 : ℚ)))
        (U' := (4620274469685723888643 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (7241257871269 / 64000000000000 : ℚ))
      (s := (494163440339247 / 5000000000000000 : ℚ))
      (q := (7936444344477101 / 80000000000000000 : ℚ))
      (U := (-(23105612742314276111357 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_169_4 :
    Uω (aρ 4) (bρ 4) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(24014375242285785827619 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1449402202043753 / 16000000000000000 : ℝ) ≤
      (-(24014375242285785827619 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1449402202043753 / 16000000000000000 : ℚ))
        (r' := (1449402202043753 / 1000000000000000 : ℚ))
        (U := (-(24014375242285785827619 / 10000000000000000000000 : ℚ)))
        (U' := (3711511969714214172381 / 10000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (7241257871269 / 64000000000000 : ℚ))
      (s := (89426272817891 / 1000000000000000 : ℚ))
      (q := (1449402202043753 / 16000000000000000 : ℚ))
      (U := (-(24014375242285785827619 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_169_5 :
    Uω (aρ 5) (bρ 5) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(25711609393350256228287 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6115739502064329 / 80000000000000000 : ℝ) ≤
      (-(25711609393350256228287 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (6115739502064329 / 80000000000000000 : ℚ))
        (r' := (6115739502064329 / 5000000000000000 : ℚ))
        (U := (-(25711609393350256228287 / 10000000000000000000000 : ℚ)))
        (U' := (2014277818649743771713 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (7241257871269 / 64000000000000 : ℚ))
      (s := (729634770475301 / 10000000000000000 : ℚ))
      (q := (6115739502064329 / 80000000000000000 : ℚ))
      (U := (-(25711609393350256228287 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_169_6 :
    Uω (aρ 6) (bρ 6) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(29714708478032058836987 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (32785860077733 / 640000000000000 : ℝ) ≤
      (-(29714708478032058836987 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (32785860077733 / 640000000000000 : ℚ))
        (r' := (32785860077733 / 20000000000000 : ℚ))
        (U := (-(29714708478032058836987 / 10000000000000000000000 : ℚ)))
        (U' := (4942650536967941163013 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (7241257871269 / 64000000000000 : ℚ))
      (s := (3139987180227 / 80000000000000 : ℚ))
      (q := (32785860077733 / 640000000000000 : ℚ))
      (U := (-(29714708478032058836987 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_169_7 :
    Uω (aρ 7) (bρ 7) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_169_8 :
    Uω (aρ 8) (bρ 8) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_169_9 :
    Uω (aρ 9) (bρ 9) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_169_10 :
    Uω (aρ 10) (bρ 10) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_169_11 :
    Uω (aρ 11) (bρ 11) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_169_12 :
    Uω (aρ 12) (bρ 12) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_169_13 :
    Uω (aρ 13) (bρ 13) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_169_14 :
    Uω (aρ 14) (bρ 14) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_169_15 :
    Uω (aρ 15) (bρ 15) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_169_16 :
    Uω (aρ 16) (bρ 16) (7241257871269 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_169 :
    Uρ (7241257871269 / 64000000000000 : ℝ) ≤
      (-(23090112557678937190821 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_169_1 U_169_2 U_169_3 U_169_4 U_169_5 U_169_6 U_169_7 U_169_8 U_169_9 U_169_10
    U_169_11 U_169_12 U_169_13 U_169_14 U_169_15 U_169_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_170_1 :
    Uω (aρ 1) (bρ 1) (907960027007 / 8000000000000 : ℝ) ≤
      (-(1396652786376097337059 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2140603533586199 / 20000000000000000 : ℝ) ≤
      (-(1396652786376097337059 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2140603533586199 / 20000000000000000 : ℚ))
        (r' := (2140603533586199 / 1250000000000000 : ℚ))
        (U := (-(1396652786376097337059 / 625000000000000000000 : ℚ)))
        (U' := (336215164373902662941 / 625000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (907960027007 / 8000000000000 : ℚ))
      (s := (1070150717912449 / 10000000000000000 : ℚ))
      (q := (2140603533586199 / 20000000000000000 : ℚ))
      (U := (-(1396652786376097337059 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_170_2 :
    Uω (aρ 2) (bρ 2) (907960027007 / 8000000000000 : ℝ) ≤
      (-(22579280174561325422027 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2091338423556399 / 20000000000000000 : ℝ) ≤
      (-(22579280174561325422027 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (2091338423556399 / 20000000000000000 : ℚ))
        (r' := (2091338423556399 / 1250000000000000 : ℚ))
        (U := (-(22579280174561325422027 / 10000000000000000000000 : ℚ)))
        (U' := (5146607037438674577973 / 10000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (907960027007 / 8000000000000 : ℚ))
      (s := (1044654620392649 / 10000000000000000 : ℚ))
      (q := (2091338423556399 / 20000000000000000 : ℚ))
      (U := (-(22579280174561325422027 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_170_3 :
    Uω (aρ 3) (bρ 3) (907960027007 / 8000000000000 : ℝ) ≤
      (-(4614045436948869884133 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (497786102597929 / 5000000000000000 : ℝ) ≤
      (-(4614045436948869884133 / 2000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (497786102597929 / 5000000000000000 : ℚ))
        (r' := (497786102597929 / 312500000000000 : ℚ))
        (U := (-(4614045436948869884133 / 2000000000000000000000 : ℚ)))
        (U' := (931132005451130115867 / 2000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (907960027007 / 8000000000000 : ℚ))
      (s := (495928356788983 / 5000000000000000 : ℚ))
      (q := (497786102597929 / 5000000000000000 : ℚ))
      (U := (-(4614045436948869884133 / 2000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_170_4 :
    Uω (aρ 4) (bρ 4) (907960027007 / 8000000000000 : ℝ) ≤
      (-(1498454770966725311139 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (181885037418007 / 2000000000000000 : ℝ) ≤
      (-(1498454770966725311139 / 625000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (181885037418007 / 2000000000000000 : ℚ))
        (r' := (181885037418007 / 125000000000000 : ℚ))
        (U := (-(1498454770966725311139 / 625000000000000000000 : ℚ)))
        (U' := (234413179783274688861 / 625000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (907960027007 / 8000000000000 : ℚ))
      (s := (22446421460783 / 250000000000000 : ℚ))
      (q := (181885037418007 / 2000000000000000 : ℚ))
      (U := (-(1498454770966725311139 / 625000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_170_5 :
    Uω (aρ 5) (bρ 5) (907960027007 / 8000000000000 : ℝ) ≤
      (-(12831859074287055078487 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1536274696582797 / 20000000000000000 : ℝ) ≤
      (-(12831859074287055078487 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1536274696582797 / 20000000000000000 : ℚ))
        (r' := (1536274696582797 / 1250000000000000 : ℚ))
        (U := (-(12831859074287055078487 / 5000000000000000000000 : ℚ)))
        (U' := (1031084531712944921513 / 5000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (907960027007 / 8000000000000 : ℚ))
      (s := (733471100169047 / 10000000000000000 : ℚ))
      (q := (1536274696582797 / 20000000000000000 : ℚ))
      (U := (-(12831859074287055078487 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_170_6 :
    Uω (aρ 6) (bρ 6) (907960027007 / 8000000000000 : ℝ) ≤
      (-(29626080805288577062113 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (516839452818463 / 10000000000000000 : ℝ) ≤
      (-(29626080805288577062113 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (516839452818463 / 10000000000000000 : ℚ))
        (r' := (516839452818463 / 312500000000000 : ℚ))
        (U := (-(29626080805288577062113 / 10000000000000000000000 : ℚ)))
        (U' := (5031278209711422937887 / 10000000000000000000000 : ℚ))
        5 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (907960027007 / 8000000000000 : ℚ))
      (s := (49764460545397 / 1250000000000000 : ℚ))
      (q := (516839452818463 / 10000000000000000 : ℚ))
      (U := (-(29626080805288577062113 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_170_7 :
    Uω (aρ 7) (bρ 7) (907960027007 / 8000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_170_8 :
    Uω (aρ 8) (bρ 8) (907960027007 / 8000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_170_9 :
    Uω (aρ 9) (bρ 9) (907960027007 / 8000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_170_10 :
    Uω (aρ 10) (bρ 10) (907960027007 / 8000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_170_11 :
    Uω (aρ 11) (bρ 11) (907960027007 / 8000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_170_12 :
    Uω (aρ 12) (bρ 12) (907960027007 / 8000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_170_13 :
    Uω (aρ 13) (bρ 13) (907960027007 / 8000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_170_14 :
    Uω (aρ 14) (bρ 14) (907960027007 / 8000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_170_15 :
    Uω (aρ 15) (bρ 15) (907960027007 / 8000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_170_16 :
    Uω (aρ 16) (bρ 16) (907960027007 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_170 :
    Uρ (907960027007 / 8000000000000 : ℝ) ≤
      (-(23074686047490937971453 / 10000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_170_1 U_170_2 U_170_3 U_170_4 U_170_5 U_170_6 U_170_7 U_170_8 U_170_9 U_170_10
    U_170_11 U_170_12 U_170_13 U_170_14 U_170_15 U_170_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

lemma U_171_1 :
    Uω (aρ 1) (bρ 1) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(2789219971449951260491 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1718089201696839 / 16000000000000000 : ℝ) ≤
      (-(2789219971449951260491 / 1250000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (1718089201696839 / 16000000000000000 : ℚ))
        (r' := (1718089201696839 / 1000000000000000 : ℚ))
        (U := (-(2789219971449951260491 / 1250000000000000000000 : ℚ)))
        (U' := (676515930050048739509 / 1250000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 1) (t := (7286102560843 / 64000000000000 : ℚ))
      (s := (107365519507433 / 1000000000000000 : ℚ))
      (q := (1718089201696839 / 16000000000000000 : ℚ))
      (U := (-(2789219971449951260491 / 1250000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_171_2 :
    Uω (aρ 2) (bρ 2) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(11272899538842934213803 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8393408755472431 / 80000000000000000 : ℝ) ≤
      (-(11272899538842934213803 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (8393408755472431 / 80000000000000000 : ℚ))
        (r' := (8393408755472431 / 5000000000000000 : ℚ))
        (U := (-(11272899538842934213803 / 5000000000000000000000 : ℚ)))
        (U' := (2590044067157065786197 / 5000000000000000000000 : ℚ))
        4 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 2) (t := (7286102560843 / 64000000000000 : ℚ))
      (s := (1048164894331389 / 10000000000000000 : ℚ))
      (q := (8393408755472431 / 80000000000000000 : ℚ))
      (U := (-(11272899538842934213803 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_171_3 :
    Uω (aρ 3) (bρ 3) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(23034967331043341839631 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7992710194147811 / 80000000000000000 : ℝ) ≤
      (-(23034967331043341839631 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7992710194147811 / 80000000000000000 : ℚ))
        (r' := (7992710194147811 / 5000000000000000 : ℚ))
        (U := (-(23034967331043341839631 / 10000000000000000000000 : ℚ)))
        (U' := (4690919880956658160369 / 10000000000000000000000 : ℚ))
        4 11 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 3) (t := (7286102560843 / 64000000000000 : ℚ))
      (s := (497693180175117 / 5000000000000000 : ℚ))
      (q := (7992710194147811 / 80000000000000000 : ℚ))
      (U := (-(23034967331043341839631 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_171_4 :
    Uω (aρ 4) (bρ 4) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(11968166807144784725189 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7303789128620783 / 80000000000000000 : ℝ) ≤
      (-(11968166807144784725189 / 5000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (7303789128620783 / 80000000000000000 : ℚ))
        (r' := (7303789128620783 / 5000000000000000 : ℚ))
        (U := (-(11968166807144784725189 / 5000000000000000000000 : ℚ)))
        (U' := (1894776798855215274811 / 5000000000000000000000 : ℚ))
        4 10 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 4) (t := (7286102560843 / 64000000000000 : ℚ))
      (s := (901450275033477 / 10000000000000000 : ℚ))
      (q := (7303789128620783 / 80000000000000000 : ℚ))
      (U := (-(11968166807144784725189 / 5000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_171_5 :
    Uω (aρ 5) (bρ 5) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(25616076633271137021301 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (246977792683227 / 3200000000000000 : ℝ) ≤
      (-(25616076633271137021301 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (246977792683227 / 3200000000000000 : ℚ))
        (r' := (246977792683227 / 200000000000000 : ℚ))
        (U := (-(25616076633271137021301 / 10000000000000000000000 : ℚ)))
        (U' := (2109810578728862978699 / 10000000000000000000000 : ℚ))
        4 7 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 5) (t := (7286102560843 / 64000000000000 : ℚ))
      (s := (14746082329669 / 200000000000000 : ℚ))
      (q := (246977792683227 / 3200000000000000 : ℚ))
      (U := (-(25616076633271137021301 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_171_6 :
    Uω (aρ 6) (bρ 6) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(29538689691821717904251 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4171007712090927 / 80000000000000000 : ℝ) ≤
      (-(29538689691821717904251 / 10000000000000000000000 : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using
      log_le_of_split_neg_rational
        (r := (4171007712090927 / 80000000000000000 : ℚ))
        (r' := (4171007712090927 / 2500000000000000 : ℚ))
        (U := (-(29538689691821717904251 / 10000000000000000000000 : ℚ)))
        (U' := (5118669323178282095749 / 10000000000000000000000 : ℚ))
        5 12 (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using
    Uω_le_right_certificate_rational
      (j := 6) (t := (7286102560843 / 64000000000000 : ℚ))
      (s := (403685215376013 / 10000000000000000 : ℚ))
      (q := (4171007712090927 / 80000000000000000 : ℚ))
      (U := (-(29538689691821717904251 / 10000000000000000000000 : ℚ)))
      (by decide +kernel)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using hlg)

lemma U_171_7 :
    Uω (aρ 7) (bρ 7) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_7]) (by norm_num [bρ_7])]; exact Lmid_7

lemma U_171_8 :
    Uω (aρ 8) (bρ 8) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_171_9 :
    Uω (aρ 9) (bρ 9) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_171_10 :
    Uω (aρ 10) (bρ 10) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_171_11 :
    Uω (aρ 11) (bρ 11) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_171_12 :
    Uω (aρ 12) (bρ 12) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_171_13 :
    Uω (aρ 13) (bρ 13) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_171_14 :
    Uω (aρ 14) (bρ 14) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_171_15 :
    Uω (aρ 15) (bρ 15) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_171_16 :
    Uω (aρ 16) (bρ 16) (7286102560843 / 64000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_171 :
    Uρ (7286102560843 / 64000000000000 : ℝ) ≤
      (-(4611878649130685497723 / 2000000000000000000000 : ℝ)) := by
  refine (Uρ_le_weighted_bounds
    U_171_1 U_171_2 U_171_3 U_171_4 U_171_5 U_171_6 U_171_7 U_171_8 U_171_9 U_171_10
    U_171_11 U_171_12 U_171_13 U_171_14 U_171_15 U_171_16).trans ?_
  norm_num only [cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]

end Zeta5Irrational
