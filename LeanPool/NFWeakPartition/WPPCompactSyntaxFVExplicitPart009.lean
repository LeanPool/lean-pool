/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart008

/-! NF weak partition development: WPPCompactSyntaxFVExplicitPart009. -/


public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/


theorem fv_syn_chnbaseresfn (F : Class) : (syn_chnbaseresfn F).fv = F.fv :=
  by
  ext u
  simp [syn_chnbaseresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn]

theorem fv_syn_chncodetrnfn (F : Class) : (syn_chncodetrnfn F).fv = F.fv :=
  by
  ext u
  simp [syn_chncodetrnfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnbaseresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen]

theorem fv_syn_cwppcardt4fn : (syn_cwppcardt4fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppcardt4fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt2fn]

theorem fv_syn_cwpppowsetfn : (syn_cwpppowsetfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwpppowsetfn]

theorem fv_syn_cwpphwcnsetfn : (syn_cwpphwcnsetfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwpphwcnsetfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowsetfn]

theorem fv_syn_cwpphwgendomfn : (syn_cwpphwgendomfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwpphwgendomfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwcnsetfn]

theorem fv_syn_cwpphwgencnvfn : (syn_cwpphwgencnvfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwpphwgencnvfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwgendomfn]

theorem fv_syn_cwpphwnisosetfn : (syn_cwpphwnisosetfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwpphwnisosetfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwcnsetfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwgencnvfn]

theorem fv_syn_cwpphnpairfn : (syn_cwpphnpairfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwpphnpairfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwcnsetfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwnisosetfn]

theorem fv_syn_cwpphninputfn : (syn_cwpphninputfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwpphninputfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphnpairfn]

theorem fv_syn_cwppqkrelkernel : (syn_cwppqkrelkernel).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppqkrelkernel]

theorem fv_syn_cwpplitphnordpointfn : (syn_cwpplitphnordpointfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwpplitphnordpointfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquofn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphninputfn]

theorem fv_syn_cwpppowset2fn : (syn_cwpppowset2fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwpppowset2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowsetfn]

theorem fv_syn_cwppfamilyrep2fn : (syn_cwppfamilyrep2fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppfamilyrep2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel]

theorem fv_syn_cwppdirecte2famfn : (syn_cwppdirecte2famfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppdirecte2famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfamilyrep2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowset2fn]

theorem fv_syn_cwppdirecth1famfn : (syn_cwppdirecth1famfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppdirecth1famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppdirecte2famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfamilyrep2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn]

theorem fv_syn_cwppdirecth2famfn : (syn_cwppdirecth2famfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppdirecth2famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppdirecth1famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfamilyrep2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn]

theorem fv_syn_cwppconcrete6codefn : (syn_cwppconcrete6codefn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppconcrete6codefn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppdirecth2famfn]

theorem fv_syn_cwppcardt6fn : (syn_cwppcardt6fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppcardt6fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt4fn]

theorem fv_syn_cwppconcrete6fn : (syn_cwppconcrete6fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppconcrete6fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6codefn]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
