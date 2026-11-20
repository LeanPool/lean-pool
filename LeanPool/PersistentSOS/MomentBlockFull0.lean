/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
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

/-!
# Exact moment block certificate

The matrix data is compiled separately so each Schur step can check its
integer identities against already elaborated entries.
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
  apply integer_schur_step momentBlockFull0Stage15 momentBlockFull0Stage16 (certificateInteger0)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage16_psd

theorem momentBlockFull0Stage14_psd : IsPSD (fun i j => (momentBlockFull0Stage14 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage14 momentBlockFull0Stage15
    (241937662857451058764338007389609057488521077140633070297581497740643677390649179167977221)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage15_psd

theorem momentBlockFull0Stage13_psd : IsPSD (fun i j => (momentBlockFull0Stage13 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage13 momentBlockFull0Stage14
    (302282677391569003353895410009431779736279896258953094590784667407429716152511796424)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage14_psd

theorem momentBlockFull0Stage12_psd : IsPSD (fun i j => (momentBlockFull0Stage12 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage12 momentBlockFull0Stage13
    (755056374531704706639560641699264475888561252757247054018662644650894582588403)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage13_psd

theorem momentBlockFull0Stage11_psd : IsPSD (fun i j => (momentBlockFull0Stage11 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage11 momentBlockFull0Stage12
    (2527217969538333548343375792657934772317626846256498137010805719338681588)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage12_psd

theorem momentBlockFull0Stage10_psd : IsPSD (fun i j => (momentBlockFull0Stage10 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage10 momentBlockFull0Stage11
    (34561535069389069592098393609264156370712154364300862953273139676473)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage11_psd

theorem momentBlockFull0Stage9_psd : IsPSD (fun i j => (momentBlockFull0Stage9 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage9 momentBlockFull0Stage10
    (469013774677419966936811159834691249742394614482932476667660686)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage10_psd

theorem momentBlockFull0Stage8_psd : IsPSD (fun i j => (momentBlockFull0Stage8 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage8 momentBlockFull0Stage9
    (6257923582445758747145390762296215429555519566979662217587)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage9_psd

theorem momentBlockFull0Stage7_psd : IsPSD (fun i j => (momentBlockFull0Stage7 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage7 momentBlockFull0Stage8
    (7034453464707846749569596351075403408014983448443661)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage8_psd

theorem momentBlockFull0Stage6_psd : IsPSD (fun i j => (momentBlockFull0Stage6 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage6 momentBlockFull0Stage7
    (1923707158678150201899330964651535171639857294)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage7_psd

theorem momentBlockFull0Stage5_psd : IsPSD (fun i j => (momentBlockFull0Stage5 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage5 momentBlockFull0Stage6
    (446401646662782787320944432891295635868)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage6_psd

theorem momentBlockFull0Stage4_psd : IsPSD (fun i j => (momentBlockFull0Stage4 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage4 momentBlockFull0Stage5
    (37788621552805100777283433380138)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage5_psd

theorem momentBlockFull0Stage3_psd : IsPSD (fun i j => (momentBlockFull0Stage3 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage3 momentBlockFull0Stage4 (2203657213483261276564022)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage4_psd

theorem momentBlockFull0Stage2_psd : IsPSD (fun i j => (momentBlockFull0Stage2 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage2 momentBlockFull0Stage3 (119627585843864631)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage3_psd

theorem momentBlockFull0Stage1_psd : IsPSD (fun i j => (momentBlockFull0Stage1 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage1 momentBlockFull0Stage2 (1000000000)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage2_psd

theorem momentBlockFull0Stage0_psd : IsPSD (fun i j => (momentBlockFull0Stage0 i j : ℝ)) := by
  apply integer_schur_step momentBlockFull0Stage0 momentBlockFull0Stage1 (1)
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · exact momentBlockFull0Stage1_psd

end PersistentSOS
