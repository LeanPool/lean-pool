/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ClassicalMatchingFactors.Factors.Tutte
public import LeanPool.ClassicalMatchingFactors.Matching.Certificates
public import LeanPool.ClassicalMatchingFactors.Matching.Petersen
public import LeanPool.ClassicalMatchingFactors.Order.ChainPartitions
public import LeanPool.ClassicalMatchingFactors.Regular.TwoFactors

/-!
# Classical matching and factor theorems in finite graphs

Source: doi:10.4153/CJM-1954-033-3, url:https://github.com/jtraverso/tutte-f-factor/tree/dc3bbce463c80c499d3e9fa072d13f9145d907d0
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `BergeMatching.exists_tutte_berge`, `FFactor.tutte_f_factor`
Tags: graph-theory, matchings, graph-factors, minimax-theorems, finite-orders
MSC: 05C70, 05C15, 06A07
-/
