/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import LeanPool.EllipticPDE.BoundedInstances
public import LeanPool.EllipticPDE.Campanato.Converse
public import LeanPool.EllipticPDE.Embedding.DirichletSemilinear
public import LeanPool.EllipticPDE.Embedding.InteriorHolder
public import LeanPool.EllipticPDE.Embedding.MorreyOneDim
public import LeanPool.EllipticPDE.Embedding.SobolevEmbedding
public import LeanPool.EllipticPDE.Embedding.SobolevLadderCompactSupport
public import LeanPool.EllipticPDE.Embedding.SobolevSolution
public import LeanPool.EllipticPDE.Existence.AprioriBound
public import LeanPool.EllipticPDE.Existence.Existence
public import LeanPool.EllipticPDE.Existence.Harmonic
public import LeanPool.EllipticPDE.Existence.StrongMaximumCorollaries
public import LeanPool.EllipticPDE.Existence.WeakMaximumTransport
public import LeanPool.EllipticPDE.Extension.ShiftMollify
public import LeanPool.EllipticPDE.Form.Hneg
public import LeanPool.EllipticPDE.Regularity.CoeffLipWeakGrad
public import LeanPool.EllipticPDE.Regularity.InteriorHolderSolution
public import LeanPool.EllipticPDE.Regularity.Local.Classical
public import LeanPool.EllipticPDE.Regularity.Local.Evans
public import LeanPool.EllipticPDE.Regularity.Localise.CompactEllipticity
public import LeanPool.EllipticPDE.Regularity.OuterCutoffTower
public import LeanPool.EllipticPDE.Spectrum.BallDimension
public import LeanPool.EllipticPDE.Spectrum.PoincareBall

/-!
# Linear elliptic PDE: solvability, regularity and spectral theory

Source: arxiv:2609.32561, url:https://github.com/alejandro-soto-franco/EllipticPDE
Authors: Alejandro José Soto Franco, Kobe Marshall-Stevens
Status: verified
Main declarations: `EllipticPdes.Regularity.higher_interior_regularity`
Tags: elliptic-pde, sobolev-spaces, regularity, fredholm-theory, spectral-theory
MSC: 35J15, 35J25, 35B65, 46E35
-/

/-!
# EllipticPdes

Solvability and interior regularity for the linear second-order elliptic Dirichlet
problem in divergence form on a bounded domain, with bounded measurable coefficients
and a drift term, so the bilinear form is in general non-symmetric.

For zero drift and a nonnegative zeroth-order term, existence and uniqueness run from the
one-dimensional Poincaré inequality through the domain inequality, continuity and coercivity
of the form, and Lax-Milgram. The same
operator then supports the Gårding inequality, the Fredholm alternative with its index
and solvability clauses, the resolvent bound and spectral compactness, the interior
`H²` estimate with its higher-order and smooth refinements, and interior Hölder
continuity in dimensions one to three through Morrey's inequality and Campanato's
characterisation.

The imported closure contains completed results; boundary `H²` regularity is outside its scope.
-/

@[expose] public section
