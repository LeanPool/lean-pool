/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module  -- shake: keep-all --deprecated_module: ignore

-- Generated project imports; run `lake exe mk_all`.
public import LeanPool.MRiscX
public import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
public import LeanPool.MRiscX.AbstractSyntax.Instr
public import LeanPool.MRiscX.AbstractSyntax.MState
public import LeanPool.MRiscX.AbstractSyntax.Map
public import LeanPool.MRiscX.Basic
public import LeanPool.MRiscX.Delab.DelabCode
public import LeanPool.MRiscX.Delab.DelabHoare
public import LeanPool.MRiscX.Elab.CodeElaborator
public import LeanPool.MRiscX.Elab.HandleExpr
public import LeanPool.MRiscX.Elab.HandleNumOrIdent
public import LeanPool.MRiscX.Elab.HoareElaborator
public import LeanPool.MRiscX.Examples.Examples
public import LeanPool.MRiscX.Examples.OtpProof
public import LeanPool.MRiscX.Examples.SingleProofsOTP
public import LeanPool.MRiscX.Examples.SpecAutomation
public import LeanPool.MRiscX.Hoare.EvalLabelInHoare
public import LeanPool.MRiscX.Hoare.HoareAssignmentElab
public import LeanPool.MRiscX.Hoare.HoareCore
public import LeanPool.MRiscX.Hoare.HoareRules
public import LeanPool.MRiscX.Hoare.HoareTheory
public import LeanPool.MRiscX.Parser.AssemblySyntax
public import LeanPool.MRiscX.Parser.HoareSyntax
public import LeanPool.MRiscX.Semantics.MsTheory
public import LeanPool.MRiscX.Semantics.Run
public import LeanPool.MRiscX.Semantics.Specification
public import LeanPool.MRiscX.Tactics.ApplySpec
public import LeanPool.MRiscX.Tactics.CodeProofTactics
public import LeanPool.MRiscX.Tactics.GeneralCustomTactics
public import LeanPool.MRiscX.Tactics.HelpCodeProofTactics
public import LeanPool.MRiscX.Tactics.SpecificationTactics
public import LeanPool.MRiscX.Tactics.SplitLastSeq
public import LeanPool.MRiscX.Tactics.TacticUtil
public import LeanPool.MRiscX.Util.BasicTheorems
