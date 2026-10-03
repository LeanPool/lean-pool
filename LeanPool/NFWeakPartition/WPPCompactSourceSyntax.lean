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


@[expose]
def syn_wiso (H : Class) (R : Class) (S : Class) (A : Class) (B : Class) : Wff :=
  let x : Var := freshVar ((H).fv ∪ (R).fv ∪ (S).fv ∪ (A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((H).fv ∪ (R).fv ∪ (S).fv ∪ (A).fv ∪ (B).fv) 1
  (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y))
          (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))))

@[expose]
def syn_cpprod (A : Class) (B : Class) : Class :=
  (syn_ctxp (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd)))

@[expose]
def syn_ccross : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cxp (.cv x) (.cv y)))

@[expose]
def syn_cdomfn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (syn_cmpt x (syn_cvv) (syn_cdm (.cv x)))

@[expose]
def syn_cranfn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (syn_cmpt x (syn_cvv) (syn_crn (.cv x)))

@[expose]
def syn_cmuc : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let b : Var := freshVar ((∅ : Finset Var)) 1
  let g : Var := freshVar ((∅ : Finset Var)) 2
  let m : Var := freshVar ((∅ : Finset Var)) 3
  let n : Var := freshVar ((∅ : Finset Var)) 4
  (syn_cmpt2 m (syn_cncs) n (syn_cncs) (.cab a (syn_wrex b (.cv m)
        (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))))

@[expose]
def syn_cfrec (F : Class) (I : Class) : Class :=
  let x : Var := freshVar ((F).fv ∪ (I).fv) 0
  (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
    (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F))

@[expose]
def syn_wwpp : Wff :=
  let f : Var := freshVar ((∅ : Finset Var)) 0
  let g : Var := freshVar ((∅ : Finset Var)) 1
  let h : Var := freshVar ((∅ : Finset Var)) 2
  let x : Var := freshVar ((∅ : Finset Var)) 3
  let y : Var := freshVar ((∅ : Finset Var)) 4
  (.all x (.all y (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x)))
          (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x))))
        (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y))))))

@[expose]
def syn_cqkrel (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  let z : Var := freshVar ((A).fv) 2
  (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
          (.classMem (syn_cop (.cv x) (.cv y)) A)))))

@[expose]
def syn_cfdmem : Class :=
  (syn_ccnvk (syn_csik (syn_cssetk)))

@[expose]
def syn_cfdprj0 : Class :=
  (syn_cins3k (syn_cidk))

@[expose]
def syn_cfdprj1 : Class :=
  (syn_cins2k (syn_cidk))

@[expose]
def syn_cfddom (A : Class) (B : Class) : Class :=
  (syn_cxpk (syn_cpw1 A) (syn_cxpk B B))

@[expose]
def syn_cfde0 (A : Class) (B : Class) : Class :=
  (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B))

@[expose]
def syn_cfde1 (A : Class) (B : Class) : Class :=
  (syn_cin (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B))

@[expose]
def syn_cfdsep (A : Class) (B : Class) : Class :=
  (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B))

@[expose]
def syn_cfdlift (R : Class) : Class :=
  (syn_csik (syn_cqkrel R))

@[expose]
def syn_cfdnonmin (R : Class) (A : Class) (B : Class) : Class :=
  (syn_ccomk (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))))

@[expose]
def syn_cfdminsep (R : Class) (A : Class) (B : Class) : Class :=
  (syn_cdif (syn_cfdsep A B) (syn_cfdnonmin R A B))

@[expose]
def syn_csep2 (A : Class) (B : Class) : Class :=
  let z : Var := freshVar ((A).fv ∪ (B).fv) 0
  (.cab z (syn_wo (syn_wa (.classMem A (.cv z)) (.neg (.classMem B (.cv z))))
      (syn_wa (.classMem B (.cv z)) (.neg (.classMem A (.cv z))))))

@[expose]
def syn_ckqrel (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A))

@[expose]
def syn_cfdminvalp (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)))

@[expose]
def syn_cfdminq (R : Class) (A : Class) (B : Class) : Class :=
  (syn_ckqrel (syn_cfdminsep R A B))

@[expose]
def syn_cfdpivmap2 (R : Class) (A : Class) (B : Class) : Class :=
  let p : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0
  (syn_cmpt p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)))

@[expose]
def syn_cfdpivrange2 (R : Class) (A : Class) (B : Class) : Class :=
  (syn_crn (syn_cfdpivmap2 R A B))

@[expose]
def syn_cfpiv (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let b : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  let c : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1
  (syn_crab b A (syn_wa (.classMem (.cv b) (syn_csep2 B C)) (syn_wral c A
        (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv b) R (.cv c))))))

@[expose]
def syn_cfdif (R : Class) (A : Class) (B : Class) : Class :=
  let d : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0
  let x : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1
  let y : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2
  (syn_crab d A
    (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))))

@[expose]
def syn_cfdrow (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let d : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  (syn_crab d (syn_cfdif R A B) (.classMem C (.cv d)))

@[expose]
def syn_cfdcode (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let q : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  let x : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 1
  (.cab q (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))))

@[expose]
def syn_cfdrowrel (R : Class) (A : Class) (B : Class) : Class :=
  (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B)))

@[expose]
def syn_cfdrowfib (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let d : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  (.cab d (.classMem (syn_cop (syn_csn (.cv d)) C) (syn_cfdrowrel R A B)))

@[expose]
def syn_cfdcodemap2 (R : Class) (A : Class) (B : Class) (C : Class) : Class :=
  let u : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0
  (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u)))

@[expose]
def syn_cfdpointrel (A : Class) : Class :=
  (syn_cin (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))

@[expose]
def syn_cfdglobalrowmap (R : Class) (A : Class) (B : Class) : Class :=
  let u : Var := freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0
  (syn_cif (syn_wbr R (syn_cwe) A)
    (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0))

@[expose]
def syn_cfdcolcodemap (R : Class) (A : Class) (B : Class) : Class :=
  (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)))
    (syn_cpw1 (syn_cpw1 A)))

@[expose]
def syn_chwcodes (A : Class) : Class :=
  (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))

@[expose]
def syn_chwiso (A : Class) : Class :=
  let h : Var := freshVar ((A).fv) 0
  let u : Var := freshVar ((A).fv) 1
  let v : Var := freshVar ((A).fv) 2
  (syn_copab u v (syn_wa
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))))

@[expose]
def syn_chwrels : Class :=
  (syn_cima (syn_ccnv
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))))
    (syn_csset))

@[expose]
def syn_chwbij : Class :=
  (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))

@[expose]
def syn_chwtrn : Class :=
  (syn_ccom (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
      (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))

@[expose]
def syn_chwgen : Class :=
  (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
    (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))

@[expose]
def syn_chwcn (A : Class) : Class :=
  (syn_cin (syn_chwcodes A) (syn_chwrels))

@[expose]
def syn_chwniso (A : Class) : Class :=
  (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
    (syn_cxp (syn_chwcn A) (syn_chwcn A)))

@[expose]
def syn_chnord (A : Class) : Class :=
  (syn_cqs (syn_chwcn A) (syn_chwniso A))

@[expose]
def syn_chncard (A : Class) : Class :=
  (syn_cnc (syn_chnord A))

@[expose]
def syn_chwbases (A : Class) : Class :=
  (syn_cima (syn_c2nd) (syn_chwcn A))

@[expose]
def syn_chwcards (A : Class) : Class :=
  (syn_cqs (syn_chwbases A) (syn_cen))

@[expose]
def syn_chnwcutcode (R : Class) (D : Class) (C : Class) : Class :=
  (syn_cop (syn_cin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))
    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))

@[expose]
def syn_chnwcutmap (R : Class) (D : Class) : Class :=
  let p : Var := freshVar ((R).fv ∪ (D).fv) 0
  (syn_cmpt p (syn_cpw1 (syn_cpw1 D))
    (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D)))

@[expose]
def syn_chnqmap1 (A : Class) : Class :=
  (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A)))

@[expose]
def syn_clntp : Class :=
  (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex))

@[expose]
def syn_clntpc (A : Class) : Class :=
  (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn A)))

@[expose]
def syn_clnker (R : Class) : Class :=
  (syn_cin R (syn_ccnv R))

@[expose]
def syn_clnquo (R : Class) (A : Class) : Class :=
  (syn_cqs A (syn_clnker R))

@[expose]
def syn_cwpphit (F : Class) (I : Class) (C : Class) : Class :=
  (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)))

@[expose]
def syn_chnwsegfn (R : Class) (D : Class) : Class :=
  (syn_ccom (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))))

@[expose]
def syn_chnwcodefn (R : Class) : Class :=
  (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid))

@[expose]
def syn_chnwcutfn (R : Class) (D : Class) : Class :=
  (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D))

@[expose]
def syn_chnwcutrel (R : Class) (D : Class) : Class :=
  (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D))

@[expose]
def syn_clnqrel (R : Class) : Class :=
  let a : Var := freshVar ((R).fv) 0
  let b : Var := freshVar ((R).fv) 1
  let x : Var := freshVar ((R).fv) 2
  let y : Var := freshVar ((R).fv) 3
  (syn_copab a b (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wbr (.cv x) R (.cv y)))))

@[expose]
def syn_clnqord (R : Class) (C : Class) : Class :=
  (syn_cin (syn_clnqrel R) (syn_cxp (syn_clnquo R C) (syn_clnquo R C)))

@[expose]
def syn_clnpwc (A : Class) : Class :=
  let d : Var := freshVar ((A).fv) 0
  let r : Var := freshVar ((A).fv) 1
  (syn_cin (syn_clntpc A)
    (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))

@[expose]
def syn_cfrecteq (F : Class) (G : Class) (I : Class) : Class :=
  (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_ctcfn) (syn_csi (syn_cfrec F I))))
        (syn_ccom (syn_cfrec G (syn_ctc I)) (syn_ctcfn)))))

@[expose]
def syn_chnqinc (D : Class) (A : Class) : Class :=
  (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))

@[expose]
def syn_clndifop : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cdif (.cv x) (.cv y)))

@[expose]
def syn_clnpwasymfn : Class :=
  (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))

@[expose]
def syn_cfdord (R : Class) (A : Class) (B : Class) : Class :=
  (syn_cin R (syn_cxp (syn_cfdif R A B) (syn_cfdif R A B)))

@[expose]
def syn_ctcnn : Class :=
  (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))))

@[expose]
def syn_cpwpull (F : Class) (R : Class) : Class :=
  (syn_ccom (syn_ccom (syn_ccnv F) R) F)

@[expose]
def syn_clnpwkerfn : Class :=
  (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn)))

@[expose]
def syn_clninterop : Class :=
  (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)))

@[expose]
def syn_clnimagecrossfn : Class :=
  (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))))

@[expose]
def syn_clnimageresfn : Class :=
  (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)))

@[expose]
def syn_clnimageop : Class :=
  (syn_ccom (syn_cranfn) (syn_clnimageresfn))

@[expose]
def syn_clnpwcnvkerfn : Class :=
  (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn))

@[expose]
def syn_clnpwclasspairfn : Class :=
  (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd))

@[expose]
def syn_clnpwclassfn : Class :=
  (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn))

@[expose]
def syn_clnpwpw1secondfn : Class :=
  (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)))

@[expose]
def syn_clnpwquoinputfn : Class :=
  (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)))

@[expose]
def syn_clnpwquofn : Class :=
  (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn))

@[expose]
def syn_clnpairraisefn : Class :=
  (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))

@[expose]
def syn_clnsifn : Class :=
  (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn)))

@[expose]
def syn_clnpwsirelfn : Class :=
  (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st)))

@[expose]
def syn_cwppreach (F : Class) (C : Class) : Class :=
  (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))

@[expose]
def syn_cwppcand (F : Class) (C : Class) : Class :=
  (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
    (syn_cwppreach F C))

@[expose]
def syn_cwpppredfam (F : Class) (C : Class) : Class :=
  (syn_ccom (syn_cimage (syn_ccnv
        (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)))) (syn_cimage (syn_csset)))

@[expose]
def syn_cwpppostcomp (F : Class) : Class :=
  (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)))

@[expose]
def syn_cwppupperpreop (C : Class) : Class :=
  (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap))
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))))

@[expose]
def syn_cwpppowlayerseq (F : Class) (C : Class) : Class :=
  (syn_ccom (syn_cwppupperpreop C)
    (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))

@[expose]
def syn_cwpphitfam (F : Class) (C : Class) : Class :=
  (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset)))

@[expose]
def syn_cwpppredmemrel (F : Class) (C : Class) : Class :=
  (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpppredfam F C))

@[expose]
def syn_cwpphitmemrel (F : Class) (C : Class) : Class :=
  (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpphitfam F C))

@[expose]
def syn_cwppreachincb (F : Class) (C : Class) : Class :=
  (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
          (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
            (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))

@[expose]
def syn_cwppimageat (D : Class) : Class :=
  (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))))

@[expose]
def syn_cwpppowateq (F : Class) (D : Class) : Class :=
  (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
        (syn_csi (syn_cfrec F D)))))

@[expose]
def syn_cwppprecomp (F : Class) : Class :=
  (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))))

@[expose]
def syn_cwpppowcommeq (F : Class) : Class :=
  (syn_cfix (syn_ccom
      (syn_ccnv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))

@[expose]
def syn_cwecutiso (R : Class) (D : Class) (S : Class) (E : Class) : Class :=
  let f : Var := freshVar ((R).fv ∪ (D).fv ∪ (S).fv ∪ (E).fv) 0
  let u : Var := freshVar ((R).fv ∪ (D).fv ∪ (S).fv ∪ (E).fv) 1
  let x : Var := freshVar ((R).fv ∪ (D).fv ∪ (S).fv ∪ (E).fv) 2
  (.cab f (syn_wrex x D (syn_wrex u E (syn_wiso (.cv f) (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))))

@[expose]
def syn_cwecutisogen (R : Class) (D : Class) (S : Class) (E : Class) : Class :=
  (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen))
        (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))

@[expose]
def syn_cwecutcardfn (R : Class) (D : Class) : Class :=
  let q : Var := freshVar ((R).fv ∪ (D).fv) 0
  (syn_cmpt q (syn_cpw1 (syn_cpw1 D)) (syn_cnc (syn_cin D
        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))))

@[expose]
def syn_cwecutcardfactor (R : Class) (D : Class) : Class :=
  (syn_ccom (syn_cimage (syn_cen)) (syn_csi (syn_ccom (syn_c2nd) (syn_chnwcutrel R D))))

@[expose]
def syn_cwppgamma (F : Class) (C : Class) : Class :=
  let k : Var := freshVar ((F).fv ∪ (C).fv) 0
  let m : Var := freshVar ((F).fv ∪ (C).fv) 1
  (syn_cio m (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))

@[expose]
def syn_cwppcardtfn : Class :=
  (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs)))

@[expose]
def syn_cwppcardt2fn : Class :=
  (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)))

@[expose]
def syn_chnbaseresfn (F : Class) : Class :=
  (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)))

@[expose]
def syn_chncodetrnfn (F : Class) : Class :=
  (syn_ccom (syn_c2nd) (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))))

@[expose]
def syn_cwppcardt4fn : Class :=
  (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))

@[expose]
def syn_cwpppowsetfn : Class :=
  (syn_cimage (syn_ccnv (syn_csset)))

@[expose]
def syn_cwpphwcnsetfn : Class :=
  (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))))

@[expose]
def syn_cwpphwgendomfn : Class :=
  (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
        (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
      (syn_cwpphwcnsetfn)))

@[expose]
def syn_cwpphwgencnvfn : Class :=
  (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn))

@[expose]
def syn_cwpphwnisosetfn : Class :=
  (syn_ccom (syn_cimage (syn_cswap))
    (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))))

@[expose]
def syn_cwpphnpairfn : Class :=
  (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn))

@[expose]
def syn_cwpphninputfn : Class :=
  (syn_csi (syn_cwpphnpairfn))

@[expose]
def syn_cwppqkrelkernel : Class :=
  (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                          (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))

@[expose]
def syn_cwpplitphnordpointfn : Class :=
  (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn))

@[expose]
def syn_cwpppowset2fn : Class :=
  (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn)))

@[expose]
def syn_cwppfamilyrep2fn : Class :=
  (syn_cimage (syn_cfdpointrel (syn_cvv)))

@[expose]
def syn_cwppdirecte2famfn : Class :=
  (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn))

@[expose]
def syn_cwppdirecth1famfn : Class :=
  (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
    (syn_csi (syn_csi (syn_cwppdirecte2famfn))))

@[expose]
def syn_cwppdirecth2famfn : Class :=
  (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
    (syn_csi (syn_csi (syn_cwppdirecth1famfn))))

@[expose]
def syn_cwppconcrete6codefn : Class :=
  (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))

@[expose]
def syn_cwppcardt6fn : Class :=
  (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))

@[expose]
def syn_cwppconcrete6fn : Class :=
  (syn_ccom (syn_cwppconcrete6codefn) (syn_ccnv (syn_cwppcardt6fn)))

@[expose]
def syn_chnsicodeliftfn : Class :=
  (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn))

@[expose]
def syn_chnsicodemap (A : Class) : Class :=
  (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A)))

@[expose]
def syn_chnsiquomap (A : Class) : Class :=
  (syn_cres (syn_ccom (syn_cimage (syn_chnsicodemap A)) (syn_cpw1fn)) (syn_cpw1 (syn_chnord A)))

@[expose]
def syn_chncodestrictfn : Class :=
  (syn_ccom (syn_clndifop)
    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))))

@[expose]
def syn_chncodepredfn : Class :=
  (syn_ccom (syn_clnimageop)
    (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))

@[expose]
def syn_chncodecarrierfn : Class :=
  (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))

@[expose]
def syn_chncodesquarefn : Class :=
  (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))

@[expose]
def syn_chncoderelfn : Class :=
  (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))

@[expose]
def syn_chncodecutfn : Class :=
  (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn))

@[expose]
def syn_chncodecutpairfn : Class :=
  (syn_ctxp (syn_chncodecutfn) (syn_c1st))

@[expose]
def syn_chncodecutinputs (A : Class) : Class :=
  (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))

@[expose]
def syn_chncodecutrel (A : Class) : Class :=
  (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A))

@[expose]
def syn_chncodecmpset (A : Class) : Class :=
  (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)))

@[expose]
def syn_chncodepredinputs (A : Class) (X : Class) (v : Var) : Class :=
  (syn_cin (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
    (syn_cima (syn_ccnv (syn_chncodecutfn)) (syn_cima (syn_chwniso A) X)))

@[expose]
def syn_chncodepredends (A : Class) (X : Class) (v : Var) : Class :=
  (syn_cuni (syn_cima (syn_c2nd) (syn_chncodepredinputs A X v)))

@[expose]
def syn_cwppstopact (F : Class) (C : Class) : Class :=
  (syn_cin (syn_cdm F)
    (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))

@[expose]
def syn_cwppstopstep (F : Class) (C : Class) : Class :=
  (syn_cun (syn_cres F (syn_cwppstopact F C))
    (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))

@[expose]
def syn_cwppfreceq (F : Class) (G : Class) (I : Class) : Class :=
  (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I)))

@[expose]
def syn_cwppfrecprefixeq (F : Class) (G : Class) (I : Class) (k : Var) : Class :=
  (syn_cun (syn_cdif (syn_cnnc)
      (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I))

end NFChoice.Compiler.CompactSourceSyntax
