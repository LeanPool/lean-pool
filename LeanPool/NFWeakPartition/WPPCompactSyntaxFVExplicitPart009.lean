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


theorem fv_syn_chnbaseresfn (F : Class) : (synChnbaseresfn F).fv = F.fv :=
  by
  ext u
  simp [synChnbaseresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn]

theorem fv_syn_chncodetrnfn (F : Class) : (synChncodetrnfn F).fv = F.fv :=
  by
  ext u
  simp [synChncodetrnfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnbaseresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen]

theorem fv_syn_cwppcardt4fn : (synCwppcardt4fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppcardt4fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt2fn]

theorem fv_syn_cwpppowsetfn : (synCwpppowsetfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwpppowsetfn]

theorem fv_syn_cwpphwcnsetfn : (synCwpphwcnsetfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwpphwcnsetfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowsetfn]

theorem fv_syn_cwpphwgendomfn : (synCwpphwgendomfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwpphwgendomfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwcnsetfn]

theorem fv_syn_cwpphwgencnvfn : (synCwpphwgencnvfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwpphwgencnvfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwgendomfn]

theorem fv_syn_cwpphwnisosetfn : (synCwpphwnisosetfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwpphwnisosetfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwcnsetfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwgencnvfn]

theorem fv_syn_cwpphnpairfn : (synCwpphnpairfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwpphnpairfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwcnsetfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphwnisosetfn]

theorem fv_syn_cwpphninputfn : (synCwpphninputfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwpphninputfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphnpairfn]

theorem fv_syn_cwppqkrelkernel : (synCwppqkrelkernel).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppqkrelkernel]

theorem fv_syn_cwpplitphnordpointfn : (synCwpplitphnordpointfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwpplitphnordpointfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquofn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphninputfn]

theorem fv_syn_cwpppowset2fn : (synCwpppowset2fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwpppowset2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowsetfn]

theorem fv_syn_cwppfamilyrep2fn : (synCwppfamilyrep2fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppfamilyrep2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel]

theorem fv_syn_cwppdirecte2famfn : (synCwppdirecte2famfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppdirecte2famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfamilyrep2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowset2fn]

theorem fv_syn_cwppdirecth1famfn : (synCwppdirecth1famfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppdirecth1famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppdirecte2famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfamilyrep2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn]

theorem fv_syn_cwppdirecth2famfn : (synCwppdirecth2famfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppdirecth2famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppdirecth1famfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfamilyrep2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn]

theorem fv_syn_cwppconcrete6codefn : (synCwppconcrete6codefn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppconcrete6codefn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppdirecth2famfn]

theorem fv_syn_cwppcardt6fn : (synCwppcardt6fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppcardt6fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt2fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt4fn]

theorem fv_syn_cwppconcrete6fn : (synCwppconcrete6fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppconcrete6fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6codefn]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
