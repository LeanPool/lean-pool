/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/CorrespondenceEndpoints.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceMatrixWeakClosure
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorInvariantUniqueness
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorUnrestrictedGamma
public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialDomain
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsGlobalCIR
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsHunt
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsAlmostSureStopping
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCurvatureNegativeTest
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAlgebraGenerator
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAlgebraQuadratic
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCollisionSupport
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryTensorGramSchmidt
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryEqualityAnalytic
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryPositiveWeightClosure
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryPositiveGeneratorMeasure
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryQuadraticNonPolynomial
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliarySlaterGroundState
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCapacitySpeed
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUESobolevAveraging
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEEndpoints
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEPaperH1

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceLogDistribution

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAlgebraCenterCovariance

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCurvatureComplexHessian

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryPositiveWeightUniform

public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialLipschitz

public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialNormalization

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberCompactCore

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberBochnerClosure

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberSquareRoot

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorFriedrichsSquareRoot

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberSpectrum

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberCfcRoot

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberTransfer

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberInverseRoot

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberShiftedRoot

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungInverse

public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneNinePointwiseGamma
public import LeanPool.GinibrePoincare.Endgame.CorrespondenceCurvatureCriterion
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeault
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLieb
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebWeak

/-! Public concrete endpoints added in response to the independent paper review.
Each imported result retains its own exact domain and hypotheses. This facade
does not turn compilation into an exhaustive paper-correspondence assertion. -/
