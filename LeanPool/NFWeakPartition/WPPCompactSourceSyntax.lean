/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.CompactSourceSyntax

/-! NF weak partition development: WPPCompactSourceSyntax. -/


public section

namespace NFChoice.Compiler.CompactSourceSyntax

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport

/-! Compact constructors added by the repaired WPP endpoint. -/


/-- Compact nominal syntax for the upstream `wiso` operator. -/
@[expose]
def synWiso (H : Class) (R : Class) (S : Class) (A : Class) (B : Class) : Wff :=
  let x : Var := freshVar ((H).fv ∪ (R).fv ∪ (S).fv ∪ (A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((H).fv ∪ (R).fv ∪ (S).fv ∪ (A).fv ∪ (B).fv) 1
  (synWa (synWf1o H A B) (synWral x A (synWral y A (synWb (synWbr (.cv x) R (.cv y))
          (synWbr (synCfv H (.cv x)) S (synCfv H (.cv y)))))))

/-- Compact nominal syntax for the upstream `cpprod` operator. -/
@[expose]
def synCpprod (A : Class) (B : Class) : Class :=
  (synCtxp (synCcom A (synC1st)) (synCcom B (synC2nd)))

/-- Compact nominal syntax for the upstream `ccross` operator. -/
@[expose]
def synCcross : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (synCmpt2 x (synCvv) y (synCvv) (synCxp (.cv x) (.cv y)))

/-- Compact nominal syntax for the upstream `cdomfn` operator. -/
@[expose]
def synCdomfn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (synCmpt x (synCvv) (synCdm (.cv x)))

/-- Compact nominal syntax for the upstream `cranfn` operator. -/
@[expose]
def synCranfn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (synCmpt x (synCvv) (synCrn (.cv x)))

/-- Compact nominal syntax for the upstream `cmuc` operator. -/
@[expose]
def synCmuc : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let b : Var := freshVar ((∅ : Finset Var)) 1
  let g : Var := freshVar ((∅ : Finset Var)) 2
  let m : Var := freshVar ((∅ : Finset Var)) 3
  let n : Var := freshVar ((∅ : Finset Var)) 4
  (synCmpt2 m (synCncs) n (synCncs) (.cab a (synWrex b (.cv m)
        (synWrex g (.cv n) (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))))

/-- Compact nominal syntax for the upstream `cfrec` operator. -/
@[expose]
def synCfrec (F : Class) (I : Class) : Class :=
  let x : Var := freshVar ((F).fv ∪ (I).fv) 0
  (synCclos1 (synCsn (synCop (synC0c) I))
    (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F))

/-- Compact nominal syntax for the upstream `wwpp` operator. -/
@[expose]
def synWwpp : Wff :=
  let f : Var := freshVar ((∅ : Finset Var)) 0
  let g : Var := freshVar ((∅ : Finset Var)) 1
  let h : Var := freshVar ((∅ : Finset Var)) 2
  let x : Var := freshVar ((∅ : Finset Var)) 3
  let y : Var := freshVar ((∅ : Finset Var)) 4
  (.all x (.all y (.imp (synWa (synWex f (synWfo (.cv f) (.cv y) (.cv x)))
          (synWex g (synWf1 (.cv g) (.cv y) (.cv x))))
        (synWex h (synWf1 (.cv h) (.cv x) (.cv y))))))

/-- Compact nominal syntax for the upstream `cqkrel` operator. -/
@[expose]
def synCqkrel (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  let z : Var := freshVar ((A).fv) 2
  (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
          (.classMem (synCop (.cv x) (.cv y)) A)))))

/-- Compact nominal syntax for the upstream `cfdmem` operator. -/
@[expose]
def synCfdmem : Class :=
  (synCcnvk (synCsik (synCssetk)))

/-- Compact nominal syntax for the upstream `cfdprj0` operator. -/
@[expose]
def synCfdprj0 : Class :=
  (synCins3k (synCidk))

/-- Compact nominal syntax for the upstream `cfdprj1` operator. -/
@[expose]
def synCfdprj1 : Class :=
  (synCins2k (synCidk))

/-- Compact nominal syntax for the upstream `cfddom` operator. -/
@[expose]
def synCfddom (A : Class) (B : Class) : Class :=
  (synCxpk (synCpw1 A) (synCxpk B B))

/-- Compact nominal syntax for the upstream `cfde0` operator. -/
@[expose]
def synCfde0 (A : Class) (B : Class) : Class :=
  (synCin (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B))

/-- Compact nominal syntax for the upstream `cfde1` operator. -/
@[expose]
def synCfde1 (A : Class) (B : Class) : Class :=
  (synCin (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B))

/-- Compact nominal syntax for the upstream `cfdsep` operator. -/
@[expose]
def synCfdsep (A : Class) (B : Class) : Class :=
  (synCsymdif (synCfde0 A B) (synCfde1 A B))

/-- Compact nominal syntax for the upstream `cfdlift` operator. -/
@[expose]
def synCfdlift (R : Class) : Class :=
  (synCsik (synCqkrel R))

/-- Compact nominal syntax for the upstream `cfdnonmin` operator. -/
@[expose]
def synCfdnonmin (R : Class) (A : Class) (B : Class) : Class :=
  (synCcomk (synCfdsep A B) (synCcnvk (synCfdlift (synCdif R (synCid)))))

/-- Compact nominal syntax for the upstream `cfdminsep` operator. -/
@[expose]
def synCfdminsep (R : Class) (A : Class) (B : Class) : Class :=
  (synCdif (synCfdsep A B) (synCfdnonmin R A B))

/-- Compact nominal syntax for the upstream `csep2` operator. -/
@[expose]
def synCsep2 (A : Class) (B : Class) : Class :=
  let z : Var := freshVar ((A).fv ∪ (B).fv) 0
  (.cab z (synWo (synWa (.classMem A (.cv z)) (.neg (.classMem B (.cv z))))
      (synWa (.classMem B (.cv z)) (.neg (.classMem A (.cv z))))))

/-- Compact nominal syntax for the upstream `ckqrel` operator. -/
@[expose]
def synCkqrel (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (synCopab x y (.classMem (synCopk (.cv x) (.cv y)) A))

/-- Compact nominal syntax for the upstream `cfdminvalp` operator. -/
@[expose]
def synCfdminvalp (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)))

/-- Compact nominal syntax for the upstream `cfdminq` operator. -/
@[expose]
def synCfdminq (R : Class) (A : Class) (B : Class) : Class :=
  (synCkqrel (synCfdminsep R A B))

/-- Compact nominal syntax for the upstream `cfdpivmap2` operator. -/
@[expose]
def synCfdpivmap2 (R : Class) (A : Class) (B : Class) : Class :=
  let p : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0
  (synCmpt p (synCxpk B B) (synCfdminvalp R A B (.cv p)))

/-- Compact nominal syntax for the upstream `cfdpivrange2` operator. -/
@[expose]
def synCfdpivrange2 (R : Class) (A : Class) (B : Class) : Class :=
  (synCrn (synCfdpivmap2 R A B))

/-- Compact nominal syntax for the upstream `cfpiv` operator. -/
@[expose]
def synCfpiv (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let b : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  let c : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1
  (synCrab b A (synWa (.classMem (.cv b) (synCsep2 B C)) (synWral c A
        (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv b) R (.cv c))))))

/-- Compact nominal syntax for the upstream `cfdif` operator. -/
@[expose]
def synCfdif (R : Class) (A : Class) (B : Class) : Class :=
  let d : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0
  let x : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1
  let y : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2
  (synCrab d A
    (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))))

/-- Compact nominal syntax for the upstream `cfdrow` operator. -/
@[expose]
def synCfdrow (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let d : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  (synCrab d (synCfdif R A B) (.classMem C (.cv d)))

/-- Compact nominal syntax for the upstream `cfdcode` operator. -/
@[expose]
def synCfdcode (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let q : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  let x : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1
  (.cab q (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x)))))

/-- Compact nominal syntax for the upstream `cfdrowrel` operator. -/
@[expose]
def synCfdrowrel (R : Class) (A : Class) (B : Class) : Class :=
  (synCres (synCkqrel (synCfdmem)) (synCpw1 (synCfdif R A B)))

/-- Compact nominal syntax for the upstream `cfdrowfib` operator. -/
@[expose]
def synCfdrowfib (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let d : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  (.cab d (.classMem (synCop (synCsn (.cv d)) C) (synCfdrowrel R A B)))

/-- Compact nominal syntax for the upstream `cfdcodemap2` operator. -/
@[expose]
def synCfdcodemap2 (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let u : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  (synCmpt u (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u)))

/-- Compact nominal syntax for the upstream `cfdpointrel` operator. -/
@[expose]
def synCfdpointrel (A : Class) : Class :=
  (synCin (synCkqrel (synCfdmem)) (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A)))))

/-- Compact nominal syntax for the upstream `cfdglobalrowmap` operator. -/
@[expose]
def synCfdglobalrowmap (R : Class) (A : Class) (B : Class) : Class :=
  let u : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0
  (synCif (synWbr R (synCwe) A)
    (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u))) (synC0))

/-- Compact nominal syntax for the upstream `cfdcolcodemap` operator. -/
@[expose]
def synCfdcolcodemap (R : Class) (A : Class) (B : Class) : Class :=
  (synCres (synCcom (synCimage (synCfdglobalrowmap R A B)) (synCimage (synCfdpointrel A)))
    (synCpw1 (synCpw1 A)))

/-- Compact nominal syntax for the upstream `chwcodes` operator. -/
@[expose]
def synChwcodes (A : Class) : Class :=
  (synCin (synCwe) (synCxp (synCvv) (synCpw A)))

/-- Compact nominal syntax for the upstream `chwiso` operator. -/
@[expose]
def synChwiso (A : Class) : Class :=
  let h : Var := freshVar ((A).fv) 0
  let u : Var := freshVar ((A).fv) 1
  let v : Var := freshVar ((A).fv) 2
  (synCopab u v (synWa
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))))

/-- Compact nominal syntax for the upstream `chwrels` operator. -/
@[expose]
def synChwrels : Class :=
  (synCima (synCcnv
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))))
    (synCsset))

/-- Compact nominal syntax for the upstream `chwbij` operator. -/
@[expose]
def synChwbij : Class :=
  (synCin (synCfuns) (synCima (synCcnv (synCimage (synCswap))) (synCfuns)))

/-- Compact nominal syntax for the upstream `chwtrn` operator. -/
@[expose]
def synChwtrn : Class :=
  (synCcom (synCcompose) (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
      (synCcom (synCimage (synCswap)) (synC1st))))

/-- Compact nominal syntax for the upstream `chwgen` operator. -/
@[expose]
def synChwgen : Class :=
  (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
    (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))

/-- Compact nominal syntax for the upstream `chwcn` operator. -/
@[expose]
def synChwcn (A : Class) : Class :=
  (synCin (synChwcodes A) (synChwrels))

/-- Compact nominal syntax for the upstream `chwniso` operator. -/
@[expose]
def synChwniso (A : Class) : Class :=
  (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
    (synCxp (synChwcn A) (synChwcn A)))

/-- Compact nominal syntax for the upstream `chnord` operator. -/
@[expose]
def synChnord (A : Class) : Class :=
  (synCqs (synChwcn A) (synChwniso A))

/-- Compact nominal syntax for the upstream `chncard` operator. -/
@[expose]
def synChncard (A : Class) : Class :=
  (synCnc (synChnord A))

/-- Compact nominal syntax for the upstream `chwbases` operator. -/
@[expose]
def synChwbases (A : Class) : Class :=
  (synCima (synC2nd) (synChwcn A))

/-- Compact nominal syntax for the upstream `chwcards` operator. -/
@[expose]
def synChwcards (A : Class) : Class :=
  (synCqs (synChwbases A) (synCen))

/-- Compact nominal syntax for the upstream `chnwcutcode` operator. -/
@[expose]
def synChnwcutcode (R : Class) (D : Class) (C : Class) : Class :=
  (synCop (synCin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C)))))
    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn C))))

/-- Compact nominal syntax for the upstream `chnwcutmap` operator. -/
@[expose]
def synChnwcutmap (R : Class) (D : Class) : Class :=
  let p : Var := freshVar ((R).fv ∪ (D).fv) 0
  (synCmpt p (synCpw1 (synCpw1 D))
    (synCec (synChnwcutcode R D (synCuni (synCuni (.cv p)))) (synChwniso D)))

/-- Compact nominal syntax for the upstream `chnqmap1` operator. -/
@[expose]
def synChnqmap1 (A : Class) : Class :=
  (synCres (synCimage (synChwniso A)) (synCpw1 (synChwcn A)))

/-- Compact nominal syntax for the upstream `clntp` operator. -/
@[expose]
def synClntp : Class :=
  (synCin (synCin (synCref) (synCtrans)) (synCconnex))

/-- Compact nominal syntax for the upstream `clntpc` operator. -/
@[expose]
def synClntpc (A : Class) : Class :=
  (synCin (synCin (synClntp) (synChwrels)) (synCxp (synCvv) (synCsn A)))

/-- Compact nominal syntax for the upstream `clnker` operator. -/
@[expose]
def synClnker (R : Class) : Class :=
  (synCin R (synCcnv R))

/-- Compact nominal syntax for the upstream `clnquo` operator. -/
@[expose]
def synClnquo (R : Class) (A : Class) : Class :=
  (synCqs A (synClnker R))

/-- Compact nominal syntax for the upstream `cwpphit` operator. -/
@[expose]
def synCwpphit (F : Class) (I : Class) (C : Class) : Class :=
  (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C)))

/-- Compact nominal syntax for the upstream `chnwsegfn` operator. -/
@[expose]
def synChnwsegfn (R : Class) (D : Class) : Class :=
  (synCcom (synCimage (synCres (synCid) D)) (synCimage (synCcnv (synCdif R (synCid)))))

/-- Compact nominal syntax for the upstream `chnwcodefn` operator. -/
@[expose]
def synChnwcodefn (R : Class) : Class :=
  (synCtxp (synCcom (synCimage (synCres (synCid) R))
      (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid))

/-- Compact nominal syntax for the upstream `chnwcutfn` operator. -/
@[expose]
def synChnwcutfn (R : Class) (D : Class) : Class :=
  (synCcom (synChnwcodefn R) (synChnwsegfn R D))

/-- Compact nominal syntax for the upstream `chnwcutrel` operator. -/
@[expose]
def synChnwcutrel (R : Class) (D : Class) : Class :=
  (synCres (synChnwcutfn R D) (synCpw1 D))

/-- Compact nominal syntax for the upstream `clnqrel` operator. -/
@[expose]
def synClnqrel (R : Class) : Class :=
  let a : Var := freshVar ((R).fv) 0
  let b : Var := freshVar ((R).fv) 1
  let x : Var := freshVar ((R).fv) 2
  let y : Var := freshVar ((R).fv) 3
  (synCopab a b (synWrex x (.cv a) (synWrex y (.cv b) (synWbr (.cv x) R (.cv y)))))

/-- Compact nominal syntax for the upstream `clnqord` operator. -/
@[expose]
def synClnqord (R : Class) (C : Class) : Class :=
  (synCin (synClnqrel R) (synCxp (synClnquo R C) (synClnquo R C)))

/-- Compact nominal syntax for the upstream `clnpwc` operator. -/
@[expose]
def synClnpwc (A : Class) : Class :=
  let d : Var := freshVar ((A).fv) 0
  let r : Var := freshVar ((A).fv) 1
  (synCin (synClntpc A)
    (synCopab r d (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))

/-- Compact nominal syntax for the upstream `cfrecteq` operator. -/
@[expose]
def synCfrecteq (F : Class) (G : Class) (I : Class) : Class :=
  (synCuni1 (synCfix (synCcom (synCcnv (synCcom (synCtcfn) (synCsi (synCfrec F I))))
        (synCcom (synCfrec G (synCtc I)) (synCtcfn)))))

/-- Compact nominal syntax for the upstream `chnqinc` operator. -/
@[expose]
def synChnqinc (D : Class) (A : Class) : Class :=
  (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))

/-- Compact nominal syntax for the upstream `clndifop` operator. -/
@[expose]
def synClndifop : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (synCmpt2 x (synCvv) y (synCvv) (synCdif (.cv x) (.cv y)))

/-- Compact nominal syntax for the upstream `clnpwasymfn` operator. -/
@[expose]
def synClnpwasymfn : Class :=
  (synCcom (synClndifop) (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))))

/-- Compact nominal syntax for the upstream `cfdord` operator. -/
@[expose]
def synCfdord (R : Class) (A : Class) (B : Class) : Class :=
  (synCin R (synCxp (synCfdif R A B) (synCfdif R A B)))

/-- Compact nominal syntax for the upstream `ctcnn` operator. -/
@[expose]
def synCtcnn : Class :=
  (synCrn (synCres (synCtcfn) (synCpw1 (synCnnc))))

/-- Compact nominal syntax for the upstream `cpwpull` operator. -/
@[expose]
def synCpwpull (F : Class) (R : Class) : Class :=
  (synCcom (synCcom (synCcnv F) R) F)

/-- Compact nominal syntax for the upstream `clnpwkerfn` operator. -/
@[expose]
def synClnpwkerfn : Class :=
  (synCcom (synClndifop) (synCtxp (synC1st) (synClnpwasymfn)))

/-- Compact nominal syntax for the upstream `clninterop` operator. -/
@[expose]
def synClninterop : Class :=
  (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop)))

/-- Compact nominal syntax for the upstream `clnimagecrossfn` operator. -/
@[expose]
def synClnimagecrossfn : Class :=
  (synCcom (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))))

/-- Compact nominal syntax for the upstream `clnimageresfn` operator. -/
@[expose]
def synClnimageresfn : Class :=
  (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)))

/-- Compact nominal syntax for the upstream `clnimageop` operator. -/
@[expose]
def synClnimageop : Class :=
  (synCcom (synCranfn) (synClnimageresfn))

/-- Compact nominal syntax for the upstream `clnpwcnvkerfn` operator. -/
@[expose]
def synClnpwcnvkerfn : Class :=
  (synCcom (synCimage (synCswap)) (synClnpwkerfn))

/-- Compact nominal syntax for the upstream `clnpwclasspairfn` operator. -/
@[expose]
def synClnpwclasspairfn : Class :=
  (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd))

/-- Compact nominal syntax for the upstream `clnpwclassfn` operator. -/
@[expose]
def synClnpwclassfn : Class :=
  (synCcom (synClnimageop) (synClnpwclasspairfn))

/-- Compact nominal syntax for the upstream `clnpwpw1secondfn` operator. -/
@[expose]
def synClnpwpw1secondfn : Class :=
  (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd)))

/-- Compact nominal syntax for the upstream `clnpwquoinputfn` operator. -/
@[expose]
def synClnpwquoinputfn : Class :=
  (synCcom (synCcross) (synCtxp (synCid) (synClnpwpw1secondfn)))

/-- Compact nominal syntax for the upstream `clnpwquofn` operator. -/
@[expose]
def synClnpwquofn : Class :=
  (synCcom (synCimage (synClnpwclassfn)) (synClnpwquoinputfn))

/-- Compact nominal syntax for the upstream `clnpairraisefn` operator. -/
@[expose]
def synClnpairraisefn : Class :=
  (synCtxp (synCimage (synC1st)) (synCimage (synC2nd)))

/-- Compact nominal syntax for the upstream `clnsifn` operator. -/
@[expose]
def synClnsifn : Class :=
  (synCcom (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn)))

/-- Compact nominal syntax for the upstream `clnpwsirelfn` operator. -/
@[expose]
def synClnpwsirelfn : Class :=
  (synCcom (synClnsifn) (synCimage (synC1st)))

/-- Compact nominal syntax for the upstream `cwppreach` operator. -/
@[expose]
def synCwppreach (F : Class) (C : Class) : Class :=
  (synCuni (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))))

/-- Compact nominal syntax for the upstream `cwppcand` operator. -/
@[expose]
def synCwppcand (F : Class) (C : Class) : Class :=
  (synCin (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
    (synCwppreach F C))

/-- Compact nominal syntax for the upstream `cwpppredfam` operator. -/
@[expose]
def synCwpppredfam (F : Class) (C : Class) : Class :=
  (synCcom (synCimage (synCcnv
        (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)))) (synCimage (synCsset)))

/-- Compact nominal syntax for the upstream `cwpppostcomp` operator. -/
@[expose]
def synCwpppostcomp (F : Class) : Class :=
  (synCcom (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)))

/-- Compact nominal syntax for the upstream `cwppupperpreop` operator. -/
@[expose]
def synCwppupperpreop (C : Class) : Class :=
  (synCcom (synClnimageop) (synCtxp (synCimage (synCswap))
      (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))))

/-- Compact nominal syntax for the upstream `cwpppowlayerseq` operator. -/
@[expose]
def synCwpppowlayerseq (F : Class) (C : Class) : Class :=
  (synCcom (synCwppupperpreop C)
    (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))

/-- Compact nominal syntax for the upstream `cwpphitfam` operator. -/
@[expose]
def synCwpphitfam (F : Class) (C : Class) : Class :=
  (synCcom (synCimage (synCcnv (synCwpppowlayerseq F C))) (synCimage (synCsset)))

/-- Compact nominal syntax for the upstream `cwpppredmemrel` operator. -/
@[expose]
def synCwpppredmemrel (F : Class) (C : Class) : Class :=
  (synCcom (synCcnv (synCsset)) (synCwpppredfam F C))

/-- Compact nominal syntax for the upstream `cwpphitmemrel` operator. -/
@[expose]
def synCwpphitmemrel (F : Class) (C : Class) : Class :=
  (synCcom (synCcnv (synCsset)) (synCwpphitfam F C))

/-- Compact nominal syntax for the upstream `cwppreachincb` operator. -/
@[expose]
def synCwppreachincb (F : Class) (C : Class) : Class :=
  (synCuni1 (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
          (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
            (synCpw1 (synCpw1 (synCdm F))))))))

/-- Compact nominal syntax for the upstream `cwppimageat` operator. -/
@[expose]
def synCwppimageat (D : Class) : Class :=
  (synCcom (synClnimageop) (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))))

/-- Compact nominal syntax for the upstream `cwpppowateq` operator. -/
@[expose]
def synCwpppowateq (F : Class) (D : Class) : Class :=
  (synCuni1 (synCfix (synCcom (synCcnv (synCcom (synCwppimageat D)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
        (synCsi (synCfrec F D)))))

/-- Compact nominal syntax for the upstream `cwppprecomp` operator. -/
@[expose]
def synCwppprecomp (F : Class) : Class :=
  (synCcom (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F))))

/-- Compact nominal syntax for the upstream `cwpppowcommeq` operator. -/
@[expose]
def synCwpppowcommeq (F : Class) : Class :=
  (synCfix (synCcom
      (synCcnv (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
      (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))))

/-- Compact nominal syntax for the upstream `cwecutiso` operator. -/
@[expose]
def synCwecutiso (R : Class) (D : Class) (S : Class) (E : Class) : Class :=
  let f : Var := freshVar ((R).fv ∪ (D).fv ∪ (S).fv ∪ (E).fv) 0
  let u : Var := freshVar ((R).fv ∪ (D).fv ∪ (S).fv ∪ (E).fv) 1
  let x : Var := freshVar ((R).fv ∪ (D).fv ∪ (S).fv ∪ (E).fv) 2
  (.cab f (synWrex x D (synWrex u E (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))

/-- Compact nominal syntax for the upstream `cwecutisogen` operator. -/
@[expose]
def synCwecutisogen (R : Class) (D : Class) (S : Class) (E : Class) : Class :=
  (synCdm (synCin (synCxp (synChwbij) (synCvv)) (synCima (synCcnv (synChwgen))
        (synCxp (synCrn (synChnwcutrel R D)) (synCrn (synChnwcutrel S E))))))

/-- Compact nominal syntax for the upstream `cwecutcardfn` operator. -/
@[expose]
def synCwecutcardfn (R : Class) (D : Class) : Class :=
  let q : Var := freshVar ((R).fv ∪ (D).fv) 0
  (synCmpt q (synCpw1 (synCpw1 D)) (synCnc (synCin D
        (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv q))))))))

/-- Compact nominal syntax for the upstream `cwecutcardfactor` operator. -/
@[expose]
def synCwecutcardfactor (R : Class) (D : Class) : Class :=
  (synCcom (synCimage (synCen)) (synCsi (synCcom (synC2nd) (synChnwcutrel R D))))

/-- Compact nominal syntax for the upstream `cwppgamma` operator. -/
@[expose]
def synCwppgamma (F : Class) (C : Class) : Class :=
  let k : Var := freshVar ((F).fv ∪ (C).fv) 0
  let m : Var := freshVar ((F).fv ∪ (C).fv) 1
  (synCio m (synWa (.classMem (.cv m) (synCwppcand F C))
      (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))))

/-- Compact nominal syntax for the upstream `cwppcardtfn` operator. -/
@[expose]
def synCwppcardtfn : Class :=
  (synCres (synCtcfn) (synCpw1 (synCncs)))

/-- Compact nominal syntax for the upstream `cwppcardt2fn` operator. -/
@[expose]
def synCwppcardt2fn : Class :=
  (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn)))

/-- Compact nominal syntax for the upstream `chnbaseresfn` operator. -/
@[expose]
def synChnbaseresfn (F : Class) : Class :=
  (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv) (synCsn F)) (synC2nd)))

/-- Compact nominal syntax for the upstream `chncodetrnfn` operator. -/
@[expose]
def synChncodetrnfn (F : Class) : Class :=
  (synCcom (synC2nd) (synCcom (synChwgen) (synCtxp (synChnbaseresfn F) (synC1st))))

/-- Compact nominal syntax for the upstream `cwppcardt4fn` operator. -/
@[expose]
def synCwppcardt4fn : Class :=
  (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))))

/-- Compact nominal syntax for the upstream `cwpppowsetfn` operator. -/
@[expose]
def synCwpppowsetfn : Class :=
  (synCimage (synCcnv (synCsset)))

/-- Compact nominal syntax for the upstream `cwpphwcnsetfn` operator. -/
@[expose]
def synCwpphwcnsetfn : Class :=
  (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))))

/-- Compact nominal syntax for the upstream `cwpphwgendomfn` operator. -/
@[expose]
def synCwpphwgendomfn : Class :=
  (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
        (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
      (synCwpphwcnsetfn)))

/-- Compact nominal syntax for the upstream `cwpphwgencnvfn` operator. -/
@[expose]
def synCwpphwgencnvfn : Class :=
  (synCcom (synCimage (synCswap)) (synCwpphwgendomfn))

/-- Compact nominal syntax for the upstream `cwpphwnisosetfn` operator. -/
@[expose]
def synCwpphwnisosetfn : Class :=
  (synCcom (synCimage (synCswap))
    (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))))

/-- Compact nominal syntax for the upstream `cwpphnpairfn` operator. -/
@[expose]
def synCwpphnpairfn : Class :=
  (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn))

/-- Compact nominal syntax for the upstream `cwpphninputfn` operator. -/
@[expose]
def synCwpphninputfn : Class :=
  (synCsi (synCwpphnpairfn))

/-- Compact nominal syntax for the upstream `cwppqkrelkernel` operator. -/
@[expose]
def synCwppqkrelkernel : Class :=
  (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
        (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
              (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                          (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                      (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                  (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c))))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))

/-- Compact nominal syntax for the upstream `cwpplitphnordpointfn` operator. -/
@[expose]
def synCwpplitphnordpointfn : Class :=
  (synCcom (synClnpwquofn) (synCwpphninputfn))

/-- Compact nominal syntax for the upstream `cwpppowset2fn` operator. -/
@[expose]
def synCwpppowset2fn : Class :=
  (synCcom (synCwpppowsetfn) (synCsi (synCwpppowsetfn)))

/-- Compact nominal syntax for the upstream `cwppfamilyrep2fn` operator. -/
@[expose]
def synCwppfamilyrep2fn : Class :=
  (synCimage (synCfdpointrel (synCvv)))

/-- Compact nominal syntax for the upstream `cwppdirecte2famfn` operator. -/
@[expose]
def synCwppdirecte2famfn : Class :=
  (synCcom (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn))

/-- Compact nominal syntax for the upstream `cwppdirecth1famfn` operator. -/
@[expose]
def synCwppdirecth1famfn : Class :=
  (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
    (synCsi (synCsi (synCwppdirecte2famfn))))

/-- Compact nominal syntax for the upstream `cwppdirecth2famfn` operator. -/
@[expose]
def synCwppdirecth2famfn : Class :=
  (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
    (synCsi (synCsi (synCwppdirecth1famfn))))

/-- Compact nominal syntax for the upstream `cwppconcrete6codefn` operator. -/
@[expose]
def synCwppconcrete6codefn : Class :=
  (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))

/-- Compact nominal syntax for the upstream `cwppcardt6fn` operator. -/
@[expose]
def synCwppcardt6fn : Class :=
  (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))

/-- Compact nominal syntax for the upstream `cwppconcrete6fn` operator. -/
@[expose]
def synCwppconcrete6fn : Class :=
  (synCcom (synCwppconcrete6codefn) (synCcnv (synCwppcardt6fn)))

/-- Compact nominal syntax for the upstream `chnsicodeliftfn` operator. -/
@[expose]
def synChnsicodeliftfn : Class :=
  (synCtxp (synClnpwsirelfn) (synClnpwpw1secondfn))

/-- Compact nominal syntax for the upstream `chnsicodemap` operator. -/
@[expose]
def synChnsicodemap (A : Class) : Class :=
  (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A)))

/-- Compact nominal syntax for the upstream `chnsiquomap` operator. -/
@[expose]
def synChnsiquomap (A : Class) : Class :=
  (synCres (synCcom (synCimage (synChnsicodemap A)) (synCpw1fn)) (synCpw1 (synChnord A)))

/-- Compact nominal syntax for the upstream `chncodestrictfn` operator. -/
@[expose]
def synChncodestrictfn : Class :=
  (synCcom (synClndifop)
    (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid)))))

/-- Compact nominal syntax for the upstream `chncodepredfn` operator. -/
@[expose]
def synChncodepredfn : Class :=
  (synCcom (synClnimageop)
    (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))

/-- Compact nominal syntax for the upstream `chncodecarrierfn` operator. -/
@[expose]
def synChncodecarrierfn : Class :=
  (synCcom (synClninterop) (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))

/-- Compact nominal syntax for the upstream `chncodesquarefn` operator. -/
@[expose]
def synChncodesquarefn : Class :=
  (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))

/-- Compact nominal syntax for the upstream `chncoderelfn` operator. -/
@[expose]
def synChncoderelfn : Class :=
  (synCcom (synClninterop) (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))

/-- Compact nominal syntax for the upstream `chncodecutfn` operator. -/
@[expose]
def synChncodecutfn : Class :=
  (synCtxp (synChncoderelfn) (synChncodecarrierfn))

/-- Compact nominal syntax for the upstream `chncodecutpairfn` operator. -/
@[expose]
def synChncodecutpairfn : Class :=
  (synCtxp (synChncodecutfn) (synC1st))

/-- Compact nominal syntax for the upstream `chncodecutinputs` operator. -/
@[expose]
def synChncodecutinputs (A : Class) : Class :=
  (synCuni (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))

/-- Compact nominal syntax for the upstream `chncodecutrel` operator. -/
@[expose]
def synChncodecutrel (A : Class) : Class :=
  (synCima (synChncodecutpairfn) (synChncodecutinputs A))

/-- Compact nominal syntax for the upstream `chncodecmpset` operator. -/
@[expose]
def synChncodecmpset (A : Class) : Class :=
  (synCun (synChwniso A) (synCcom (synChncodecutrel A) (synChwniso A)))

/-- Compact nominal syntax for the upstream `chncodepredinputs` operator. -/
@[expose]
def synChncodepredinputs (A : Class) (X : Class) (v : Var) : Class :=
  (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
    (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))

/-- Compact nominal syntax for the upstream `chncodepredends` operator. -/
@[expose]
def synChncodepredends (A : Class) (X : Class) (v : Var) : Class :=
  (synCuni (synCima (synC2nd) (synChncodepredinputs A X v)))

/-- Compact nominal syntax for the upstream `cwppstopact` operator. -/
@[expose]
def synCwppstopact (F : Class) (C : Class) : Class :=
  (synCin (synCdm F)
    (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))

/-- Compact nominal syntax for the upstream `cwppstopstep` operator. -/
@[expose]
def synCwppstopstep (F : Class) (C : Class) : Class :=
  (synCun (synCres F (synCwppstopact F C))
    (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))

/-- Compact nominal syntax for the upstream `cwppfreceq` operator. -/
@[expose]
def synCwppfreceq (F : Class) (G : Class) (I : Class) : Class :=
  (synCfix (synCcom (synCcnv (synCfrec F I)) (synCfrec G I)))

/-- Compact nominal syntax for the upstream `cwppfrecprefixeq` operator. -/
@[expose]
def synCwppfrecprefixeq (F : Class) (G : Class) (I : Class) (k : Var) : Class :=
  (synCun (synCdif (synCnnc)
      (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))) (synCwppfreceq F G I))

end NFChoice.Compiler.CompactSourceSyntax
