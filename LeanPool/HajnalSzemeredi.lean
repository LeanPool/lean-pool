/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

module

public import LeanPool.HajnalSzemeredi.Defs
public import LeanPool.HajnalSzemeredi.Reach
public import LeanPool.HajnalSzemeredi.Shift
public import LeanPool.HajnalSzemeredi.Count
public import LeanPool.HajnalSzemeredi.Structure
public import LeanPool.HajnalSzemeredi.Cases
public import LeanPool.HajnalSzemeredi.Main
public import LeanPool.HajnalSzemeredi.Final

/-!
# The Hajnal–Szemerédi theorem on equitable vertex colourings

Source: doi:10.1017/S0963548307008619, url:https://github.com/jtraverso/hajnal-szemeredi/tree/ba34061e3cf12dfc8297610d5d7b3f0afac7ec54
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `HajnalSzemeredi.hajnalSzemeredi`, `HajnalSzemeredi.hajnalSzemeredi_exact`
Tags: graph-theory, equitable-colouring, extremal-combinatorics
MSC: 05C15, 05C35
-/

/-!
# Hajnal–Szemerédi equitable colourings

Ported to Lean Pool from jtraverso/hajnal-szemeredi, commit
`ba34061e3cf12dfc8297610d5d7b3f0afac7ec54`; import paths adapted.
-/
