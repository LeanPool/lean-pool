/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/

module

public import LeanPool.QECCertificates.GF2.Basis
public import LeanPool.QECCertificates.GF2.HGPCleaningDual
public import LeanPool.QECCertificates.GF2.HGPKunneth
public import LeanPool.QECCertificates.GF2.LiftedProduct
public import LeanPool.QECCertificates.GF2.LowerBound
public import LeanPool.QECCertificates.GF2.RankEchelon
public import LeanPool.QECCertificates.Pauli.Expr
public import LeanPool.QECCertificates.Reflect.Distance

/-!
# Quantum code certificates and hypergraph-product theory

Source: arxiv:2610.03214, url:https://github.com/QCL-SUAT/QECCertificates
Authors: Shuoming An
Status: verified
Main declarations: `QECCertificates.hgp_kunneth`
Tags: quantum-error-correction, coding-theory, hypergraph-products, certificates
MSC: 81P45, 94B05, 03B35
-/

/-!
# Quantum error correction certificates and hypergraph-product code theory

Ported from QCL-SUAT/QECCertificates at
`1ced3ae0317725f80640d4a38b9c03eaba84a9c9`. The general theory, including every
GF(2) module, operator-expression translation, and abstract RUP/encoding proofs,
is preserved. Concrete instance certificate data and downstream measurement
protocols are outside this dependency closure.

QECCertificates, Copyright 2026 Shuoming An. Licensed under the Apache License,
Version 2.0. The Lean-QEC dependency carries its attribution in RowspaceKernel.
-/
