/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Adapted in Lean Pool for independent Schur update checking.
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
# Fraction-free Schur updates for stages 4 through 15

These entrywise integer equalities depend only on the compiled matrix data.
They are checked together in this module so the two groups of large updates
can compile in parallel.
-/

public section

namespace PersistentSOS

theorem momentBlockFull0Stage4_update :
    IsIntegerSchurUpdate momentBlockFull0Stage4 momentBlockFull0Stage5
    (37788621552805100777283433380138) := by
  decide +kernel

theorem momentBlockFull0Stage5_update :
    IsIntegerSchurUpdate momentBlockFull0Stage5 momentBlockFull0Stage6
    (446401646662782787320944432891295635868) := by
  decide +kernel

theorem momentBlockFull0Stage6_update :
    IsIntegerSchurUpdate momentBlockFull0Stage6 momentBlockFull0Stage7
    (1923707158678150201899330964651535171639857294) := by
  decide +kernel

theorem momentBlockFull0Stage7_update :
    IsIntegerSchurUpdate momentBlockFull0Stage7 momentBlockFull0Stage8
    (7034453464707846749569596351075403408014983448443661) := by
  decide +kernel

theorem momentBlockFull0Stage8_update :
    IsIntegerSchurUpdate momentBlockFull0Stage8 momentBlockFull0Stage9
    (6257923582445758747145390762296215429555519566979662217587) := by
  decide +kernel

theorem momentBlockFull0Stage9_update :
    IsIntegerSchurUpdate momentBlockFull0Stage9 momentBlockFull0Stage10
    (469013774677419966936811159834691249742394614482932476667660686) := by
  decide +kernel

theorem momentBlockFull0Stage10_update :
    IsIntegerSchurUpdate momentBlockFull0Stage10 momentBlockFull0Stage11
    (34561535069389069592098393609264156370712154364300862953273139676473) := by
  decide +kernel

theorem momentBlockFull0Stage11_update :
    IsIntegerSchurUpdate momentBlockFull0Stage11 momentBlockFull0Stage12
    (2527217969538333548343375792657934772317626846256498137010805719338681588) := by
  decide +kernel

theorem momentBlockFull0Stage12_update :
    IsIntegerSchurUpdate momentBlockFull0Stage12 momentBlockFull0Stage13
    (755056374531704706639560641699264475888561252757247054018662644650894582588403) := by
  decide +kernel

theorem momentBlockFull0Stage13_update :
    IsIntegerSchurUpdate momentBlockFull0Stage13 momentBlockFull0Stage14
    (302282677391569003353895410009431779736279896258953094590784667407429716152511796424) := by
  decide +kernel

theorem momentBlockFull0Stage14_update :
    IsIntegerSchurUpdate momentBlockFull0Stage14 momentBlockFull0Stage15
    (241937662857451058764338007389609057488521077140633070297581497740643677390649179167977221) :=
  by decide +kernel

theorem momentBlockFull0Stage15_update :
    IsIntegerSchurUpdate momentBlockFull0Stage15 momentBlockFull0Stage16 (certificateInteger0) := by
  decide +kernel

end PersistentSOS
