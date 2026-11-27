/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Modified in Lean Pool to separate the larger Schur update checks.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.PersistentSOS.MomentBlockFull0Data
public import LeanPool.PersistentSOS.PSD

import LeanPool.PersistentSOS.MomentBlockFull0UpdatesEarly
import LeanPool.PersistentSOS.MomentBlockFull0UpdatesLater

/-!
# Exact moment block certificate

The larger entrywise update checks compile in independent modules. The PSD
proofs here infer each pivot from its update theorem, then check positivity
and first-row symmetry. The auxiliary lemmas retain the original check types.
-/

@[expose] public section


namespace PersistentSOS


theorem momentBlockFull0Stage27_psd : IsPSD (fun i j => (momentBlockFull0Stage27 i j : ℝ)) := by
  intro x
  simp [quadraticForm, momentBlockFull0Stage27]

theorem momentBlockFull0Stage26_psd : IsPSD (fun i j => (momentBlockFull0Stage26 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage26 momentBlockFull0Stage27 (certificateInteger550)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage27_psd

theorem momentBlockFull0Stage25_psd : IsPSD (fun i j => (momentBlockFull0Stage25 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage25 momentBlockFull0Stage26 (certificateInteger540)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage26_psd

theorem momentBlockFull0Stage24_psd : IsPSD (fun i j => (momentBlockFull0Stage24 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage24 momentBlockFull0Stage25 (certificateInteger525)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage25_psd

theorem momentBlockFull0Stage23_psd : IsPSD (fun i j => (momentBlockFull0Stage23 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage23 momentBlockFull0Stage24 (certificateInteger504)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage24_psd

theorem momentBlockFull0Stage22_psd : IsPSD (fun i j => (momentBlockFull0Stage22 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage22 momentBlockFull0Stage23 (certificateInteger476)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage23_psd

theorem momentBlockFull0Stage21_psd : IsPSD (fun i j => (momentBlockFull0Stage21 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage21 momentBlockFull0Stage22 (certificateInteger440)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage22_psd

theorem momentBlockFull0Stage20_psd : IsPSD (fun i j => (momentBlockFull0Stage20 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage20 momentBlockFull0Stage21 (certificateInteger395)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage21_psd

theorem momentBlockFull0Stage19_psd : IsPSD (fun i j => (momentBlockFull0Stage19 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage19 momentBlockFull0Stage20 (certificateInteger340)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage20_psd

theorem momentBlockFull0Stage18_psd : IsPSD (fun i j => (momentBlockFull0Stage18 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage18 momentBlockFull0Stage19 (certificateInteger274)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage19_psd

theorem momentBlockFull0Stage17_psd : IsPSD (fun i j => (momentBlockFull0Stage17 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage17 momentBlockFull0Stage18 (certificateInteger196)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage18_psd

theorem momentBlockFull0Stage16_psd : IsPSD (fun i j => (momentBlockFull0Stage16 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage16 momentBlockFull0Stage17 (certificateInteger105)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage17_psd

theorem momentBlockFull0Stage15_psd : IsPSD (fun i j => (momentBlockFull0Stage15 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage15 momentBlockFull0Stage16 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage15_update)
    momentBlockFull0Stage16_psd
  all_goals decide

theorem momentBlockFull0Stage14_psd : IsPSD (fun i j => (momentBlockFull0Stage14 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage14 momentBlockFull0Stage15 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage14_update)
    momentBlockFull0Stage15_psd
  all_goals decide

theorem momentBlockFull0Stage13_psd : IsPSD (fun i j => (momentBlockFull0Stage13 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage13 momentBlockFull0Stage14 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage13_update)
    momentBlockFull0Stage14_psd
  all_goals decide

theorem momentBlockFull0Stage12_psd : IsPSD (fun i j => (momentBlockFull0Stage12 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage12 momentBlockFull0Stage13 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage12_update)
    momentBlockFull0Stage13_psd
  all_goals decide

theorem momentBlockFull0Stage11_psd : IsPSD (fun i j => (momentBlockFull0Stage11 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage11 momentBlockFull0Stage12 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage11_update)
    momentBlockFull0Stage12_psd
  all_goals decide

theorem momentBlockFull0Stage10_psd : IsPSD (fun i j => (momentBlockFull0Stage10 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage10 momentBlockFull0Stage11 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage10_update)
    momentBlockFull0Stage11_psd
  all_goals decide

theorem momentBlockFull0Stage9_psd : IsPSD (fun i j => (momentBlockFull0Stage9 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage9 momentBlockFull0Stage10 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage9_update)
    momentBlockFull0Stage10_psd
  all_goals decide

theorem momentBlockFull0Stage8_psd : IsPSD (fun i j => (momentBlockFull0Stage8 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage8 momentBlockFull0Stage9 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage8_update)
    momentBlockFull0Stage9_psd
  all_goals decide

theorem momentBlockFull0Stage7_psd : IsPSD (fun i j => (momentBlockFull0Stage7 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage7 momentBlockFull0Stage8 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage7_update)
    momentBlockFull0Stage8_psd
  all_goals decide

theorem momentBlockFull0Stage6_psd : IsPSD (fun i j => (momentBlockFull0Stage6 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage6 momentBlockFull0Stage7 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage6_update)
    momentBlockFull0Stage7_psd
  all_goals decide

theorem momentBlockFull0Stage5_psd : IsPSD (fun i j => (momentBlockFull0Stage5 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage5 momentBlockFull0Stage6 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage5_update)
    momentBlockFull0Stage6_psd
  all_goals decide

theorem momentBlockFull0Stage4_psd : IsPSD (fun i j => (momentBlockFull0Stage4 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage4 momentBlockFull0Stage5 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage4_update)
    momentBlockFull0Stage5_psd
  all_goals decide

theorem momentBlockFull0Stage3_psd : IsPSD (fun i j => (momentBlockFull0Stage3 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage3 momentBlockFull0Stage4 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage3_update)
    momentBlockFull0Stage4_psd
  all_goals decide

theorem momentBlockFull0Stage2_psd : IsPSD (fun i j => (momentBlockFull0Stage2 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage2 momentBlockFull0Stage3 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage2_update)
    momentBlockFull0Stage3_psd
  all_goals decide

theorem momentBlockFull0Stage1_psd : IsPSD (fun i j => (momentBlockFull0Stage1 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage1 momentBlockFull0Stage2 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage1_update)
    momentBlockFull0Stage2_psd
  all_goals decide

theorem momentBlockFull0Stage0_psd : IsPSD (fun i j => (momentBlockFull0Stage0 i j : ℝ)) := by
  refine integer_schur_step momentBlockFull0Stage0 momentBlockFull0Stage1 _
    ?_ ?_ (by decide +kernel) (by as_aux_lemma => exact momentBlockFull0Stage0_update)
    momentBlockFull0Stage1_psd
  all_goals decide

end PersistentSOS
