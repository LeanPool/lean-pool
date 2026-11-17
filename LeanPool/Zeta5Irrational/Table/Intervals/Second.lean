/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Real.Pi.Bounds
import LeanPool.Zeta5Irrational.Table.U14
import LeanPool.Zeta5Irrational.Table.U15
import LeanPool.Zeta5Irrational.Table.U16
import LeanPool.Zeta5Irrational.Table.U17
import LeanPool.Zeta5Irrational.Table.U18
import LeanPool.Zeta5Irrational.Table.U19
import LeanPool.Zeta5Irrational.Table.U20
import LeanPool.Zeta5Irrational.Table.U21
import LeanPool.Zeta5Irrational.Table.U22
import LeanPool.Zeta5Irrational.Table.U23
import LeanPool.Zeta5Irrational.Table.U24
import LeanPool.Zeta5Irrational.Table.U25
import LeanPool.Zeta5Irrational.Table.U26
import LeanPool.Zeta5Irrational.Table.U27
import LeanPool.Zeta5Irrational.Table.U28
import LeanPool.Zeta5Irrational.Table.V14
import LeanPool.Zeta5Irrational.Table.V15
import LeanPool.Zeta5Irrational.Table.V16
import LeanPool.Zeta5Irrational.Table.V17
import LeanPool.Zeta5Irrational.Table.V18
import LeanPool.Zeta5Irrational.Table.V19
import LeanPool.Zeta5Irrational.Table.V20
import LeanPool.Zeta5Irrational.Table.V21
import LeanPool.Zeta5Irrational.Table.V22
import LeanPool.Zeta5Irrational.Table.V23
import LeanPool.Zeta5Irrational.Table.V24
import LeanPool.Zeta5Irrational.Table.V25
import LeanPool.Zeta5Irrational.Table.V26
import LeanPool.Zeta5Irrational.Table.V27
import LeanPool.Zeta5Irrational.Table.V28

/-! # Interval certificates 171 through 341

These independent endpoint checks use only the corresponding upper and lower table bounds.
The covering argument is assembled in `LeanPool.Zeta5Irrational.Table.Intervals`.
-/

@[expose] public section

open Finset

namespace Zeta5Irrational

lemma tc_171 :
    ∀ t,
      (7286102560843 / 64000000000000 : ℝ) ≤ t →
        t ≤ (730852490563 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_172 V_171
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_172 :
    ∀ t,
      (730852490563 / 6400000000000 : ℝ) ≤ t →
        t ≤ (7330947250417 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_173 V_172
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_173 :
    ∀ t,
      (7330947250417 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1838342398801 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_174 V_173
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_174 :
    ∀ t,
      (1838342398801 / 16000000000000 : ℝ) ≤ t →
        t ≤ (3699107142389 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_175 V_174
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_175 :
    ∀ t,
      (3699107142389 / 32000000000000 : ℝ) ≤ t →
        t ≤ (465191185897 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_176 V_175
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_176 :
    ∀ t,
      (465191185897 / 4000000000000 : ℝ) ≤ t →
        t ≤ (3743951831963 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_177 V_176
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_177 :
    ∀ t,
      (3743951831963 / 32000000000000 : ℝ) ≤ t →
        t ≤ (15065496707 / 128000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_178 V_177
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_178 :
    ∀ t,
      (15065496707 / 128000000000 : ℝ) ≤ t →
        t ≤ (3788796521537 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_179 V_178
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_179 :
    ∀ t,
      (3788796521537 / 32000000000000 : ℝ) ≤ t →
        t ≤ (952804716581 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_180 V_179
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_180 :
    ∀ t,
      (952804716581 / 8000000000000 : ℝ) ≤ t →
        t ≤ (3833641211111 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_181 V_180
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_181 :
    ∀ t,
      (3833641211111 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1928031777949 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_182 V_181
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_182 :
    ∀ t,
      (1928031777949 / 16000000000000 : ℝ) ≤ t →
        t ≤ (121903382671 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_183 V_182
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_183 :
    ∀ t,
      (121903382671 / 1000000000000 : ℝ) ≤ t →
        t ≤ (1972876467523 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_184 V_183
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_184 :
    ∀ t,
      (1972876467523 / 16000000000000 : ℝ) ≤ t →
        t ≤ (199529881231 / 1600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_185 V_184
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_185 :
    ∀ t,
      (199529881231 / 1600000000000 : ℝ) ≤ t →
        t ≤ (2017721157097 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_186 V_185
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_186 :
    ∀ t,
      (2017721157097 / 16000000000000 : ℝ) ≤ t →
        t ≤ (510035875471 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_187 V_186
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_187 :
    ∀ t,
      (510035875471 / 4000000000000 : ℝ) ≤ t →
        t ≤ (1042494095729 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_188 V_187
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_188 :
    ∀ t,
      (1042494095729 / 8000000000000 : ℝ) ≤ t →
        t ≤ (266229110129 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_189 V_188
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_189 :
    ∀ t,
      (266229110129 / 2000000000000 : ℝ) ≤ t →
        t ≤ (110976113009 / 800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_190 V_189
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_190 :
    ∀ t,
      (110976113009 / 800000000000 : ℝ) ≤ t →
        t ≤ (72162863729 / 500000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_191 V_190
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_191 :
    ∀ t,
      (72162863729 / 500000000000 : ℝ) ≤ t →
        t ≤ (4675203313927 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_192 V_191
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_192 :
    ∀ t,
      (4675203313927 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2365991674599 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_193 V_192
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_193 :
    ∀ t,
      (2365991674599 / 16000000000000 : ℝ) ≤ t →
        t ≤ (4788763384469 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_194 V_193
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_194 :
    ∀ t,
      (4788763384469 / 32000000000000 : ℝ) ≤ t →
        t ≤ (9634306804209 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_195 V_194
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_195 :
    ∀ t,
      (9634306804209 / 64000000000000 : ℝ) ≤ t →
        t ≤ (242277170987 / 1600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_196 V_195
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_196 :
    ∀ t,
      (242277170987 / 1600000000000 : ℝ) ≤ t →
        t ≤ (9747866874751 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_197 V_196
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_197 :
    ∀ t,
      (9747866874751 / 64000000000000 : ℝ) ≤ t →
        t ≤ (4902323455011 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_198 V_197
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_198 :
    ∀ t,
      (4902323455011 / 32000000000000 : ℝ) ≤ t →
        t ≤ (9861426945293 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_199 V_198
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_199 :
    ∀ t,
      (9861426945293 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2479551745141 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_200 V_199
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_200 :
    ∀ t,
      (2479551745141 / 16000000000000 : ℝ) ≤ t →
        t ≤ (19893193996399 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_201 V_200
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_201 :
    ∀ t,
      (19893193996399 / 128000000000000 : ℝ) ≤ t →
        t ≤ (1994997403167 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_202 V_201
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_202 :
    ∀ t,
      (1994997403167 / 12800000000000 : ℝ) ≤ t →
        t ≤ (20006754066941 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_203 V_202
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_203 :
    ∀ t,
      (20006754066941 / 128000000000000 : ℝ) ≤ t →
        t ≤ (5015883525553 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_204 V_203
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_204 :
    ∀ t,
      (5015883525553 / 32000000000000 : ℝ) ≤ t →
        t ≤ (20120314137483 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_205 V_204
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_205 :
    ∀ t,
      (20120314137483 / 128000000000000 : ℝ) ≤ t →
        t ≤ (10088547086377 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_206 V_205
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_206 :
    ∀ t,
      (10088547086377 / 64000000000000 : ℝ) ≤ t →
        t ≤ (809354968321 / 5120000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_207 V_206
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_207 :
    ∀ t,
      (809354968321 / 5120000000000 : ℝ) ≤ t →
        t ≤ (634082945103 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_208 V_207
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_208 :
    ∀ t,
      (634082945103 / 4000000000000 : ℝ) ≤ t →
        t ≤ (20347434278567 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_209 V_208
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_209 :
    ∀ t,
      (20347434278567 / 128000000000000 : ℝ) ≤ t →
        t ≤ (10202107156919 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_210 V_209
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_210 :
    ∀ t,
      (10202107156919 / 64000000000000 : ℝ) ≤ t →
        t ≤ (20460994349109 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_211 V_210
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_211 :
    ∀ t,
      (20460994349109 / 128000000000000 : ℝ) ≤ t →
        t ≤ (1025888719219 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_212 V_211
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_212 :
    ∀ t,
      (1025888719219 / 6400000000000 : ℝ) ≤ t →
        t ≤ (20574554419651 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_213 V_212
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_213 :
    ∀ t,
      (20574554419651 / 128000000000000 : ℝ) ≤ t →
        t ≤ (10315667227461 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_214 V_213
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_214 :
    ∀ t,
      (10315667227461 / 64000000000000 : ℝ) ≤ t →
        t ≤ (20688114490193 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_215 V_214
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_215 :
    ∀ t,
      (20688114490193 / 128000000000000 : ℝ) ≤ t →
        t ≤ (2593111815683 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_216 V_215
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_216 :
    ∀ t,
      (2593111815683 / 16000000000000 : ℝ) ≤ t →
        t ≤ (4160334912147 / 25600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_217 V_216
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_217 :
    ∀ t,
      (4160334912147 / 25600000000000 : ℝ) ≤ t →
        t ≤ (10429227298003 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_218 V_217
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_218 :
    ∀ t,
      (10429227298003 / 64000000000000 : ℝ) ≤ t →
        t ≤ (20915234631277 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_219 V_218
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_219 :
    ∀ t,
      (20915234631277 / 128000000000000 : ℝ) ≤ t →
        t ≤ (5243003666637 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_220 V_219
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_220 :
    ∀ t,
      (5243003666637 / 32000000000000 : ℝ) ≤ t →
        t ≤ (21028794701819 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_221 V_220
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_221 :
    ∀ t,
      (21028794701819 / 128000000000000 : ℝ) ≤ t →
        t ≤ (2108557473709 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_222 V_221
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_222 :
    ∀ t,
      (2108557473709 / 12800000000000 : ℝ) ≤ t →
        t ≤ (21142354772361 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_223 V_222
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_223 :
    ∀ t,
      (21142354772361 / 128000000000000 : ℝ) ≤ t →
        t ≤ (1324945925477 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_224 V_223
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_224 :
    ∀ t,
      (1324945925477 / 8000000000000 : ℝ) ≤ t →
        t ≤ (10656347439087 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_225 V_224
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_225 :
    ∀ t,
      (10656347439087 / 64000000000000 : ℝ) ≤ t →
        t ≤ (5356563737179 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_226 V_225
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_226 :
    ∀ t,
      (5356563737179 / 32000000000000 : ℝ) ≤ t →
        t ≤ (10769907509629 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_227 V_226
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_227 :
    ∀ t,
      (10769907509629 / 64000000000000 : ℝ) ≤ t →
        t ≤ (108266875449 / 640000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_228 V_227
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_228 :
    ∀ t,
      (108266875449 / 640000000000 : ℝ) ≤ t →
        t ≤ (10883467580171 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_229 V_228
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_229 :
    ∀ t,
      (10883467580171 / 64000000000000 : ℝ) ≤ t →
        t ≤ (5470123807721 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_230 V_229
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_230 :
    ∀ t,
      (5470123807721 / 32000000000000 : ℝ) ≤ t →
        t ≤ (10997027650713 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_231 V_230
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_231 :
    ∀ t,
      (10997027650713 / 64000000000000 : ℝ) ≤ t →
        t ≤ (345431490187 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_232 V_231
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_232 :
    ∀ t,
      (345431490187 / 2000000000000 : ℝ) ≤ t →
        t ≤ (5583683878263 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_233 V_232
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_233 :
    ∀ t,
      (5583683878263 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2820231956767 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_234 V_233
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_234 :
    ∀ t,
      (2820231956767 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1139448789761 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_235 V_234
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_235 :
    ∀ t,
      (1139448789761 / 6400000000000 : ℝ) ≤ t →
        t ≤ (1438505996019 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_236 V_235
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_236 :
    ∀ t,
      (1438505996019 / 8000000000000 : ℝ) ≤ t →
        t ≤ (2933792027309 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_237 V_236
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_237 :
    ∀ t,
      (2933792027309 / 16000000000000 : ℝ) ≤ t →
        t ≤ (149528603129 / 800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_238 V_237
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_238 :
    ∀ t,
      (149528603129 / 800000000000 : ℝ) ≤ t →
        t ≤ (3047352097851 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_239 V_238
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_239 :
    ∀ t,
      (3047352097851 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1552066066561 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_240 V_239
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_240 :
    ∀ t,
      (1552066066561 / 8000000000000 : ℝ) ≤ t →
        t ≤ (201105762729 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_241 V_240
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_241 :
    ∀ t,
      (201105762729 / 1000000000000 : ℝ) ≤ t →
        t ≤ (3251812320751 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_242 V_241
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_242 :
    ∀ t,
      (3251812320751 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1642966218919 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_243 V_242
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_243 :
    ∀ t,
      (1642966218919 / 8000000000000 : ℝ) ≤ t →
        t ≤ (132802102197 / 640000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_244 V_243
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_244 :
    ∀ t,
      (132802102197 / 640000000000 : ℝ) ≤ t →
        t ≤ (6674225226937 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_245 V_244
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_245 :
    ∀ t,
      (6674225226937 / 32000000000000 : ℝ) ≤ t →
        t ≤ (838543168003 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_246 V_245
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_246 :
    ∀ t,
      (838543168003 / 4000000000000 : ℝ) ≤ t →
        t ≤ (6742465461111 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_247 V_246
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_247 :
    ∀ t,
      (6742465461111 / 32000000000000 : ℝ) ≤ t →
        t ≤ (3388292789099 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_248 V_247
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_248 :
    ∀ t,
      (3388292789099 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1362141139057 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_249 V_248
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_249 :
    ∀ t,
      (1362141139057 / 6400000000000 : ℝ) ≤ t →
        t ≤ (1711206453093 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_250 V_249
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_250 :
    ∀ t,
      (1711206453093 / 8000000000000 : ℝ) ≤ t →
        t ≤ (13723771741831 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_251 V_250
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_251 :
    ∀ t,
      (13723771741831 / 64000000000000 : ℝ) ≤ t →
        t ≤ (6878945929459 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_252 V_251
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_252 :
    ∀ t,
      (6878945929459 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2758402395201 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_253 V_252
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_253 :
    ∀ t,
      (2758402395201 / 12800000000000 : ℝ) ≤ t →
        t ≤ (3456533023273 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_254 V_253
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_254 :
    ∀ t,
      (3456533023273 / 16000000000000 : ℝ) ≤ t →
        t ≤ (13860252210179 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_255 V_254
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_255 :
    ∀ t,
      (13860252210179 / 64000000000000 : ℝ) ≤ t →
        t ≤ (6947186163633 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_256 V_255
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_256 :
    ∀ t,
      (6947186163633 / 32000000000000 : ℝ) ≤ t →
        t ≤ (13928492444353 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_257 V_256
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_257 :
    ∀ t,
      (13928492444353 / 64000000000000 : ℝ) ≤ t →
        t ≤ (87266328509 / 400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_258 V_257
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_258 :
    ∀ t,
      (87266328509 / 400000000000 : ℝ) ≤ t →
        t ≤ (13996732678527 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_259 V_258
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_259 :
    ∀ t,
      (13996732678527 / 64000000000000 : ℝ) ≤ t →
        t ≤ (7015426397807 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_260 V_259
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_260 :
    ∀ t,
      (7015426397807 / 32000000000000 : ℝ) ≤ t →
        t ≤ (14064972912701 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_261 V_260
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_261 :
    ∀ t,
      (14064972912701 / 64000000000000 : ℝ) ≤ t →
        t ≤ (3524773257447 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_262 V_261
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_262 :
    ∀ t,
      (3524773257447 / 16000000000000 : ℝ) ≤ t →
        t ≤ (4522628207 / 20480000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_263 V_262
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_263 :
    ∀ t,
      (4522628207 / 20480000000 : ℝ) ≤ t →
        t ≤ (7083666631981 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_264 V_263
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_264 :
    ∀ t,
      (7083666631981 / 32000000000000 : ℝ) ≤ t →
        t ≤ (14201453381049 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_265 V_264
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_265 :
    ∀ t,
      (14201453381049 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1779446687267 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_266 V_265
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_266 :
    ∀ t,
      (1779446687267 / 8000000000000 : ℝ) ≤ t →
        t ≤ (14269693615223 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_267 V_266
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_267 :
    ∀ t,
      (14269693615223 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1430381373231 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_268 V_267
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_268 :
    ∀ t,
      (1430381373231 / 6400000000000 : ℝ) ≤ t →
        t ≤ (14337933849397 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_269 V_268
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_269 :
    ∀ t,
      (14337933849397 / 64000000000000 : ℝ) ≤ t →
        t ≤ (3593013491621 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_270 V_269
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_270 :
    ∀ t,
      (3593013491621 / 16000000000000 : ℝ) ≤ t →
        t ≤ (14406174083571 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_271 V_270
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_271 :
    ∀ t,
      (14406174083571 / 64000000000000 : ℝ) ≤ t →
        t ≤ (7220147100329 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_272 V_271
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_272 :
    ∀ t,
      (7220147100329 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2894882863549 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_273 V_272
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_273 :
    ∀ t,
      (2894882863549 / 12800000000000 : ℝ) ≤ t →
        t ≤ (906783402177 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_274 V_273
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_274 :
    ∀ t,
      (906783402177 / 4000000000000 : ℝ) ≤ t →
        t ≤ (14542654551919 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_275 V_274
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_275 :
    ∀ t,
      (14542654551919 / 64000000000000 : ℝ) ≤ t →
        t ≤ (7288387334503 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_276 V_275
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_276 :
    ∀ t,
      (7288387334503 / 32000000000000 : ℝ) ≤ t →
        t ≤ (732250745159 / 3200000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_277 V_276
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_277 :
    ∀ t,
      (732250745159 / 3200000000000 : ℝ) ≤ t →
        t ≤ (7356627568677 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_278 V_277
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_278 :
    ∀ t,
      (7356627568677 / 32000000000000 : ℝ) ≤ t →
        t ≤ (1847686921441 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_279 V_278
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_279 :
    ∀ t,
      (1847686921441 / 8000000000000 : ℝ) ≤ t →
        t ≤ (7424867802851 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_280 V_279
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_280 :
    ∀ t,
      (7424867802851 / 32000000000000 : ℝ) ≤ t →
        t ≤ (3729493959969 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_281 V_280
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_281 :
    ∀ t,
      (3729493959969 / 16000000000000 : ℝ) ≤ t →
        t ≤ (299724321481 / 1280000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_282 V_281
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_282 :
    ∀ t,
      (299724321481 / 1280000000000 : ℝ) ≤ t →
        t ≤ (29403234977 / 125000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_283 V_282
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_283 :
    ∀ t,
      (29403234977 / 125000000000 : ℝ) ≤ t →
        t ≤ (7561348271199 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_284 V_283
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_284 :
    ∀ t,
      (7561348271199 / 32000000000000 : ℝ) ≤ t →
        t ≤ (3797734194143 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_285 V_284
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_285 :
    ∀ t,
      (3797734194143 / 16000000000000 : ℝ) ≤ t →
        t ≤ (383185431123 / 1600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_286 V_285
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_286 :
    ∀ t,
      (383185431123 / 1600000000000 : ℝ) ≤ t →
        t ≤ (3865974428317 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_287 V_286
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_287 :
    ∀ t,
      (3865974428317 / 16000000000000 : ℝ) ≤ t →
        t ≤ (975023636351 / 4000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_288 V_287
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_288 :
    ∀ t,
      (975023636351 / 4000000000000 : ℝ) ≤ t →
        t ≤ (3934214662491 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_289 V_288
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_289 :
    ∀ t,
      (3934214662491 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1984167389789 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_290 V_289
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_290 :
    ∀ t,
      (1984167389789 / 8000000000000 : ℝ) ≤ t →
        t ≤ (504571876719 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_291 V_290
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_291 :
    ∀ t,
      (504571876719 / 2000000000000 : ℝ) ≤ t →
        t ≤ (2052407623963 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_292 V_291
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_292 :
    ∀ t,
      (2052407623963 / 8000000000000 : ℝ) ≤ t →
        t ≤ (41730554821 / 160000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_293 V_292
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_293 :
    ∀ t,
      (41730554821 / 160000000000 : ℝ) ≤ t →
        t ≤ (269345996903 / 1000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_294 V_293
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_294 :
    ∀ t,
      (269345996903 / 1000000000000 : ℝ) ≤ t →
        t ≤ (8696815458149 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_295 V_294
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_295 :
    ∀ t,
      (8696815458149 / 32000000000000 : ℝ) ≤ t →
        t ≤ (4387279507701 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_296 V_295
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_296 :
    ∀ t,
      (4387279507701 / 16000000000000 : ℝ) ≤ t →
        t ≤ (1770460514531 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_297 V_296
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_297 :
    ∀ t,
      (1770460514531 / 6400000000000 : ℝ) ≤ t →
        t ≤ (17782348702563 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_298 V_297
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_298 :
    ∀ t,
      (17782348702563 / 64000000000000 : ℝ) ≤ t →
        t ≤ (2232511532477 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_299 V_298
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_299 :
    ∀ t,
      (2232511532477 / 8000000000000 : ℝ) ≤ t →
        t ≤ (17937835817069 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_300 V_299
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_300 :
    ∀ t,
      (17937835817069 / 64000000000000 : ℝ) ≤ t →
        t ≤ (9007789687161 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_301 V_300
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_301 :
    ∀ t,
      (9007789687161 / 32000000000000 : ℝ) ≤ t →
        t ≤ (723732917263 / 2560000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_302 V_301
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_302 :
    ∀ t,
      (723732917263 / 2560000000000 : ℝ) ≤ t →
        t ≤ (4542766622207 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_303 V_302
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_303 :
    ∀ t,
      (4542766622207 / 16000000000000 : ℝ) ≤ t →
        t ≤ (36419876534909 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_304 V_303
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_304 :
    ∀ t,
      (36419876534909 / 128000000000000 : ℝ) ≤ t →
        t ≤ (18248810046081 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_305 V_304
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_305 :
    ∀ t,
      (18248810046081 / 64000000000000 : ℝ) ≤ t →
        t ≤ (7315072729883 / 25600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_306 V_305
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_306 :
    ∀ t,
      (7315072729883 / 25600000000000 : ℝ) ≤ t →
        t ≤ (9163276801667 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_307 V_306
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_307 :
    ∀ t,
      (9163276801667 / 32000000000000 : ℝ) ≤ t →
        t ≤ (36730850763921 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_308 V_307
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_308 :
    ∀ t,
      (36730850763921 / 128000000000000 : ℝ) ≤ t →
        t ≤ (18404297160587 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_309 V_308
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_309 :
    ∀ t,
      (18404297160587 / 64000000000000 : ℝ) ≤ t →
        t ≤ (36886337878427 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_310 V_309
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_310 :
    ∀ t,
      (36886337878427 / 128000000000000 : ℝ) ≤ t →
        t ≤ (231025508973 / 800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_311 V_310
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_311 :
    ∀ t,
      (231025508973 / 800000000000 : ℝ) ≤ t →
        t ≤ (37041824992933 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_312 V_311
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_312 :
    ∀ t,
      (37041824992933 / 128000000000000 : ℝ) ≤ t →
        t ≤ (18559784275093 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_313 V_312
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_313 :
    ∀ t,
      (18559784275093 / 64000000000000 : ℝ) ≤ t →
        t ≤ (37197312107439 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_314 V_313
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_314 :
    ∀ t,
      (37197312107439 / 128000000000000 : ℝ) ≤ t →
        t ≤ (9318763916173 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_315 V_314
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_315 :
    ∀ t,
      (9318763916173 / 32000000000000 : ℝ) ≤ t →
        t ≤ (7470559844389 / 25600000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_316 V_315
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_316 :
    ∀ t,
      (7470559844389 / 25600000000000 : ℝ) ≤ t →
        t ≤ (18715271389599 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_317 V_316
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_317 :
    ∀ t,
      (18715271389599 / 64000000000000 : ℝ) ≤ t →
        t ≤ (37508286336451 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_318 V_317
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_318 :
    ∀ t,
      (37508286336451 / 128000000000000 : ℝ) ≤ t →
        t ≤ (4698253736713 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_319 V_318
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_319 :
    ∀ t,
      (4698253736713 / 16000000000000 : ℝ) ≤ t →
        t ≤ (37663773450957 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_320 V_319
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_320 :
    ∀ t,
      (37663773450957 / 128000000000000 : ℝ) ≤ t →
        t ≤ (3774151700821 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_321 V_320
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_321 :
    ∀ t,
      (3774151700821 / 12800000000000 : ℝ) ≤ t →
        t ≤ (37819260565463 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_322 V_321
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_322 :
    ∀ t,
      (37819260565463 / 128000000000000 : ℝ) ≤ t →
        t ≤ (9474251030679 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_323 V_322
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_323 :
    ∀ t,
      (9474251030679 / 32000000000000 : ℝ) ≤ t →
        t ≤ (37974747679969 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_324 V_323
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_324 :
    ∀ t,
      (37974747679969 / 128000000000000 : ℝ) ≤ t →
        t ≤ (19026245618611 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_325 V_324
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_325 :
    ∀ t,
      (19026245618611 / 64000000000000 : ℝ) ≤ t →
        t ≤ (1525209391779 / 5120000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_326 V_325
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_326 :
    ∀ t,
      (1525209391779 / 5120000000000 : ℝ) ≤ t →
        t ≤ (2387998646983 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_327 V_326
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_327 :
    ∀ t,
      (2387998646983 / 8000000000000 : ℝ) ≤ t →
        t ≤ (38285721908981 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_328 V_327
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_328 :
    ∀ t,
      (38285721908981 / 128000000000000 : ℝ) ≤ t →
        t ≤ (19181732733117 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_329 V_328
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_329 :
    ∀ t,
      (19181732733117 / 64000000000000 : ℝ) ≤ t →
        t ≤ (38441209023487 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_330 V_329
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_330 :
    ∀ t,
      (38441209023487 / 128000000000000 : ℝ) ≤ t →
        t ≤ (1925947629037 / 6400000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_331 V_330
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_331 :
    ∀ t,
      (1925947629037 / 6400000000000 : ℝ) ≤ t →
        t ≤ (19337219847623 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_332 V_331
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_332 :
    ∀ t,
      (19337219847623 / 64000000000000 : ℝ) ≤ t →
        t ≤ (4853740851219 / 16000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_333 V_332
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_333 :
    ∀ t,
      (4853740851219 / 16000000000000 : ℝ) ≤ t →
        t ≤ (19492706962129 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_334 V_333
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_334 :
    ∀ t,
      (19492706962129 / 64000000000000 : ℝ) ≤ t →
        t ≤ (9785225259691 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_335 V_334
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_335 :
    ∀ t,
      (9785225259691 / 32000000000000 : ℝ) ≤ t →
        t ≤ (3929638815327 / 12800000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_336 V_335
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_336 :
    ∀ t,
      (3929638815327 / 12800000000000 : ℝ) ≤ t →
        t ≤ (616435551059 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_337 V_336
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_337 :
    ∀ t,
      (616435551059 / 2000000000000 : ℝ) ≤ t →
        t ≤ (19803681191141 / 64000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_338 V_337
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_338 :
    ∀ t,
      (19803681191141 / 64000000000000 : ℝ) ≤ t →
        t ≤ (9940712374197 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_339 V_338
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_339 :
    ∀ t,
      (9940712374197 / 32000000000000 : ℝ) ≤ t →
        t ≤ (200369118629 / 640000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_340 V_339
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_340 :
    ∀ t,
      (200369118629 / 640000000000 : ℝ) ≤ t →
        t ≤ (10096199488703 / 32000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_341 V_340
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

lemma tc_341 :
    ∀ t,
      (10096199488703 / 32000000000000 : ℝ) ≤ t →
        t ≤ (2543485761489 / 8000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  check_right (by norm_num [bρ_1]) (by norm_num) U_342 V_341
    (by unfold M0; linarith only [Real.pi_gt_d20, Real.pi_lt_d20])

end Zeta5Irrational
