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
# Fraction-free Schur updates for stages 0 through 3

These entrywise integer equalities depend only on the compiled matrix data.
They are checked together in this module so the two groups of large updates
can compile in parallel.
-/

public section

namespace PersistentSOS

theorem momentBlockFull0Stage0_update :
    IsIntegerSchurUpdate momentBlockFull0Stage0 momentBlockFull0Stage1 (1) := by
  decide +kernel

theorem momentBlockFull0Stage1_update :
    IsIntegerSchurUpdate momentBlockFull0Stage1 momentBlockFull0Stage2 (1000000000) := by
  decide +kernel

theorem momentBlockFull0Stage2_update :
    IsIntegerSchurUpdate momentBlockFull0Stage2 momentBlockFull0Stage3 (119627585843864631) := by
  decide +kernel

theorem momentBlockFull0Stage3_update :
    IsIntegerSchurUpdate momentBlockFull0Stage3 momentBlockFull0Stage4
    (2203657213483261276564022) := by
  decide +kernel

end PersistentSOS
