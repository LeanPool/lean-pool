/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

/-
Adapted from chenson2018/finite-integral-ra at 5620a22cc48127b592bca85b1aaf013e55d4f6df.
The relation-algebra foundations are adapted from CSLib at 910210f7d155e22a2244591e394bd16fbb0ddbb3.
The upstream Rust generator supplies certificate data, and Lean checks that data in the kernel.
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms1.Symm0Nsymm0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms1.Total
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms2.Symm1Nsymm0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms2.Total
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms3.Symm0Nsymm1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms3.Symm2Nsymm0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms3.Total
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms4.Symm1Nsymm1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms4.Symm3Nsymm0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms4.Total
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.Symm0Nsymm2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.Symm2Nsymm1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.Symm4Nsymm0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.Total
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.Symm1Nsymm2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.Symm3Nsymm1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.Symm5Nsymm0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.Total
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.Symm0Nsymm3
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.Symm2Nsymm2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.Symm4Nsymm1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.Symm6Nsymm0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.Total

/-!
# Enumeration of finite integral relation algebras through seven atoms

Source: url:https://www1.chapman.edu/~jipsen/gap/ramaddux.html
Authors: Chris Henson
Status: verified
Main declarations:
  `FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.card_ofAtoms_one`,
  `FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.card_ofAtoms_two`,
  `FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.card_ofAtoms_three`,
  `FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.card_ofAtoms_four`,
  `FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.card_ofAtoms_five`,
  `FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.card_ofAtoms_six`,
  `FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.card_ofAtoms_seven`
Tags: relation-algebras, enumeration, isomorphism-classes, proof-certificates
MSC: 03G15, 05A15, 68V20
-/
