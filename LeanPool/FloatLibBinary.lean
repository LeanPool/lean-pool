/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George, Will Adkisson, Anima Anandkumar, Nicolas Rouquette
-/

module

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Analysis.BFloat16
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Analysis.Error
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Analysis.Sterbenz
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction

/-!
# Verified binary floating-point arithmetic and error bounds

Source: arxiv:2609.19352, url:https://github.com/lean-dojo/FloatLib/tree/0d91825727839f597fd06b22fdd038ea21480f0c
Authors: Robert Joseph George, Will Adkisson, Anima Anandkumar, Nicolas Rouquette
Status: verified
Main declarations: `FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz`
Tags: floating-point, numerical-analysis, rounding, error-bounds, verified-arithmetic
MSC: 65G50, 68V15
-/
