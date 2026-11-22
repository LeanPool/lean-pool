/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Defs.Setting
public import LeanPool.RigidDescent.Defs.Purity
public import LeanPool.RigidDescent.Defs.Tower
public import LeanPool.RigidDescent.Defs.Holim
public import LeanPool.RigidDescent.Defs.Descent
public import LeanPool.RigidDescent.Foundations.Compact
public import LeanPool.RigidDescent.Foundations.Telescope
public import LeanPool.RigidDescent.Foundations.CellularTower
public import LeanPool.RigidDescent.Foundations.Neeman
public import LeanPool.RigidDescent.Foundations.CompactsThick
public import LeanPool.RigidDescent.Foundations.Extension
public import LeanPool.RigidDescent.Foundations.Brown
public import LeanPool.RigidDescent.Foundations.ColimitFormula
public import LeanPool.RigidDescent.Foundations.TensorYoneda
public import LeanPool.RigidDescent.Towers.Basic
public import LeanPool.RigidDescent.Towers.AddCommGrp
public import LeanPool.RigidDescent.Towers.ProConstant
public import LeanPool.RigidDescent.Holim.Basic
public import LeanPool.RigidDescent.Paper.Sec2
public import LeanPool.RigidDescent.Paper.Sec3
public import LeanPool.RigidDescent.Paper.Sec4
public import LeanPool.RigidDescent.TheoremA

/-!
# Descent and effective descent in rigid categories

Source: url:https://github.com/Shamrock-Frost/rigid-descent-formal
Authors: Brendan Murphy
Status: verified
Main declarations: `RigidDescent.theoremA`, `RigidDescent.theoremA_of_splitMono`,
  `RigidDescent.brown_representability`
Tags: tensor-triangulated categories, descent, Brown representability, purity
MSC: 18G80, 18G25, 18D20
-/

/-
Upstream license notice for RigidDescent

MIT License

Copyright (c) 2026 Brendan Murphy

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
