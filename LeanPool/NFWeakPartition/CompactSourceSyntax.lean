/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.Basic

/-! NF weak partition development: CompactSourceSyntax. -/


public section

namespace NFChoice.Compiler.CompactSourceSyntax

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport

/-! Definition-transparent compact interpretation of every source syntax head in
the exact `nchoice` closure.  Free-variable support, rather than nominal
`.vars`, is the correct semantic DV boundary because all generated dummies are
bound internally.
-/


@[expose]
def syn_wtru : Wff :=
  .imp .falsum .falsum

@[expose]
def syn_wb (ph : Wff) (ps : Wff) : Wff :=
  (.neg (.imp (.imp ph ps) (.neg (.imp ps ph))))

@[expose]
def syn_wo (ph : Wff) (ps : Wff) : Wff :=
  (.imp (.neg ph) ps)

@[expose]
def syn_wa (ph : Wff) (ps : Wff) : Wff :=
  (.neg (.imp ph (.neg ps)))

@[expose]
def syn_w3o (ph : Wff) (ps : Wff) (ch : Wff) : Wff :=
  (syn_wo (syn_wo ph ps) ch)

@[expose]
def syn_w3a (ph : Wff) (ps : Wff) (ch : Wff) : Wff :=
  (syn_wa (syn_wa ph ps) ch)

@[expose]
def syn_wnan (ph : Wff) (ps : Wff) : Wff :=
  (.neg (syn_wa ph ps))

@[expose]
def syn_wex (x : Var) (ph : Wff) : Wff :=
  (.neg (.all x (.neg ph)))

@[expose]
def syn_wnf (x : Var) (ph : Wff) : Wff :=
  (.all x (.imp ph (.all x ph)))

@[expose]
def syn_wsb (y : Var) (x : Var) (ph : Wff) : Wff :=
  (syn_wa (.imp (.objEq x y) ph) (syn_wex x (syn_wa (.objEq x y) ph)))

@[expose]
def syn_weu (x : Var) (ph : Wff) : Wff :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (ph).fv) 0
  (syn_wex y (.all x (syn_wb ph (.objEq x y))))

@[expose]
def syn_wmo (x : Var) (ph : Wff) : Wff :=
  (.imp (syn_wex x ph) (syn_weu x ph))

@[expose]
def syn_wnfc (x : Var) (A : Class) : Wff :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (A).fv) 0
  (.all y (syn_wnf x (.classMem (.cv y) A)))

@[expose]
def syn_wne (A : Class) (B : Class) : Wff :=
  (.neg (.classEq A B))

@[expose]
def syn_wral (x : Var) (A : Class) (ph : Wff) : Wff :=
  (.all x (.imp (.classMem (.cv x) A) ph))

@[expose]
def syn_wrex (x : Var) (A : Class) (ph : Wff) : Wff :=
  (syn_wex x (syn_wa (.classMem (.cv x) A) ph))

@[expose]
def syn_wreu (x : Var) (A : Class) (ph : Wff) : Wff :=
  (syn_weu x (syn_wa (.classMem (.cv x) A) ph))

@[expose]
def syn_wrmo (x : Var) (A : Class) (ph : Wff) : Wff :=
  (syn_wmo x (syn_wa (.classMem (.cv x) A) ph))

@[expose]
def syn_crab (x : Var) (A : Class) (ph : Wff) : Class :=
  (.cab x (syn_wa (.classMem (.cv x) A) ph))

@[expose]
def syn_cvv : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (.cab x (.objEq x x))

@[expose]
def syn_wsbc (A : Class) (x : Var) (ph : Wff) : Wff :=
  (.classMem A (.cab x ph))

@[expose]
def syn_csb (A : Class) (x : Var) (B : Class) : Class :=
  let y : Var := freshVar ((A).fv ∪ ({ x } : Finset Var) ∪ (B).fv) 0
  (.cab y (syn_wsbc A x (.classMem (.cv y) B)))

@[expose]
def syn_cnin (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  (.cab x (syn_wnan (.classMem (.cv x) A) (.classMem (.cv x) B)))

@[expose]
def syn_ccompl (A : Class) : Class :=
  (syn_cnin A A)

@[expose]
def syn_cin (A : Class) (B : Class) : Class :=
  (syn_ccompl (syn_cnin A B))

@[expose]
def syn_cun (A : Class) (B : Class) : Class :=
  (syn_cnin (syn_ccompl A) (syn_ccompl B))

@[expose]
def syn_cdif (A : Class) (B : Class) : Class :=
  (syn_cin A (syn_ccompl B))

@[expose]
def syn_csymdif (A : Class) (B : Class) : Class :=
  (syn_cun (syn_cdif A B) (syn_cdif B A))

@[expose]
def syn_wss (A : Class) (B : Class) : Wff :=
  (.classEq (syn_cin A B) A)

@[expose]
def syn_wpss (A : Class) (B : Class) : Wff :=
  (syn_wa (syn_wss A B) (syn_wne A B))

@[expose]
def syn_c0 : Class :=
  (syn_cdif (syn_cvv) (syn_cvv))

@[expose]
def syn_cif (ph : Wff) (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((ph).fv ∪ (A).fv ∪ (B).fv) 0
  (.cab x (syn_wo (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem (.cv x) B) (.neg ph))))

@[expose]
def syn_cpw (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (syn_wss (.cv x) A))

@[expose]
def syn_csn (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (.classEq (.cv x) A))

@[expose]
def syn_cpr (A : Class) (B : Class) : Class :=
  (syn_cun (syn_csn A) (syn_csn B))

@[expose]
def syn_ctp (A : Class) (B : Class) (C : Class) : Class :=
  (syn_cun (syn_cpr A B) (syn_csn C))

@[expose]
def syn_cuni (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (.cab x (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) A))))

@[expose]
def syn_cint (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (.cab x (.all y (.imp (.classMem (.cv y) A) (.objMem x y))))

@[expose]
def syn_ciun (x : Var) (A : Class) (B : Class) : Class :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0
  (.cab y (syn_wrex x A (.classMem (.cv y) B)))

@[expose]
def syn_copk (A : Class) (B : Class) : Class :=
  (syn_cpr (syn_csn A) (syn_cpr A B))

@[expose]
def syn_c1c : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (.cab x (syn_wex y (.classEq (.cv x) (syn_csn (.cv y)))))

@[expose]
def syn_cpw1 (A : Class) : Class :=
  (syn_cin (syn_cpw A) (syn_c1c))

@[expose]
def syn_cuni1 (A : Class) : Class :=
  (syn_cuni (syn_cin A (syn_c1c)))

@[expose]
def syn_cxpk (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  let z : Var := freshVar ((A).fv ∪ (B).fv) 2
  (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
          (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))))))

@[expose]
def syn_ccnvk (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  let z : Var := freshVar ((A).fv) 2
  (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
          (.classMem (syn_copk (.cv z) (.cv y)) A)))))

@[expose]
def syn_cins2k (A : Class) : Class :=
  let t : Var := freshVar ((A).fv) 0
  let u : Var := freshVar ((A).fv) 1
  let v : Var := freshVar ((A).fv) 2
  let x : Var := freshVar ((A).fv) 3
  let y : Var := freshVar ((A).fv) 4
  let z : Var := freshVar ((A).fv) 5
  (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex t
            (syn_wex u (syn_wex v (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
                  (.classEq (.cv z) (syn_copk (.cv u) (.cv v)))
                  (.classMem (syn_copk (.cv t) (.cv v)) A)))))))))

@[expose]
def syn_cins3k (A : Class) : Class :=
  let t : Var := freshVar ((A).fv) 0
  let u : Var := freshVar ((A).fv) 1
  let v : Var := freshVar ((A).fv) 2
  let x : Var := freshVar ((A).fv) 3
  let y : Var := freshVar ((A).fv) 4
  let z : Var := freshVar ((A).fv) 5
  (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex t
            (syn_wex u (syn_wex v (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
                  (.classEq (.cv z) (syn_copk (.cv u) (.cv v)))
                  (.classMem (syn_copk (.cv t) (.cv u)) A)))))))))

@[expose]
def syn_cimak (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  (.cab x (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A)))

@[expose]
def syn_ccomk (A : Class) (B : Class) : Class :=
  (syn_cimak (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv))

@[expose]
def syn_cp6 (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) A))

@[expose]
def syn_csik (A : Class) : Class :=
  let t : Var := freshVar ((A).fv) 0
  let u : Var := freshVar ((A).fv) 1
  let x : Var := freshVar ((A).fv) 2
  let y : Var := freshVar ((A).fv) 3
  let z : Var := freshVar ((A).fv) 4
  (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex t
            (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (.cv t)))
                (.classEq (.cv z) (syn_csn (.cv u)))
                (.classMem (syn_copk (.cv t) (.cv u)) A))))))))

@[expose]
def syn_cssetk : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
          (syn_wss (.cv y) (.cv z))))))

@[expose]
def syn_cimagek (A : Class) : Class :=
  (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
      (syn_cpw1 (syn_cpw1 (syn_c1c)))))

@[expose]
def syn_cidk : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (.cab x (syn_wex y
      (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.objEq y z)))))

@[expose]
def syn_cio (x : Var) (ph : Wff) : Class :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (ph).fv) 0
  (syn_cuni (.cab y (.classEq (.cab x ph) (syn_csn (.cv y)))))

@[expose]
def syn_c0c : Class :=
  (syn_csn (syn_c0))

@[expose]
def syn_cplc (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  let z : Var := freshVar ((A).fv ∪ (B).fv) 2
  (.cab x (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))))

@[expose]
def syn_cnnc : Class :=
  let b : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (syn_cint (.cab b (syn_wa (.classMem (syn_c0c) (.cv b))
        (syn_wral y (.cv b) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv b))))))

@[expose]
def syn_cfin : Class :=
  (syn_cuni (syn_cnnc))

@[expose]
def syn_clefin : Class :=
  let w : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  let z : Var := freshVar ((∅ : Finset Var)) 3
  (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
          (syn_wrex w (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv y) (.cv w))))))))

@[expose]
def syn_cltfin : Class :=
  let m : Var := freshVar ((∅ : Finset Var)) 0
  let n : Var := freshVar ((∅ : Finset Var)) 1
  let p : Var := freshVar ((∅ : Finset Var)) 2
  let x : Var := freshVar ((∅ : Finset Var)) 3
  (.cab x (syn_wex m (syn_wex n (syn_wa (.classEq (.cv x) (syn_copk (.cv m) (.cv n)))
          (syn_wa (syn_wne (.cv m) (syn_c0)) (syn_wrex p (syn_cnnc)
              (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c)))))))))

@[expose]
def syn_cncfin (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x))))

@[expose]
def syn_ctfin (M : Class) : Class :=
  let a : Var := freshVar ((M).fv) 0
  let n : Var := freshVar ((M).fv) 1
  (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc))
        (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))))

@[expose]
def syn_cevenfin : Class :=
  let n : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  (.cab x (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))))
      (syn_wne (.cv x) (syn_c0))))

@[expose]
def syn_coddfin : Class :=
  let n : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  (.cab x (syn_wa (syn_wrex n (syn_cnnc)
        (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (syn_wne (.cv x) (syn_c0))))

@[expose]
def syn_wsfin (M : Class) (N : Class) : Wff :=
  let a : Var := freshVar ((M).fv ∪ (N).fv) 0
  (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
    (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))))

@[expose]
def syn_cspfin : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
        (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))

@[expose]
def syn_cphi (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (.cab y (syn_wrex x A (.classEq (.cv y)
        (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)))))

@[expose]
def syn_cop (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x
      (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))

@[expose]
def syn_cproj1 (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (.classMem (syn_cphi (.cv x)) A))

@[expose]
def syn_cproj2 (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (.classMem (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) A))

@[expose]
def syn_copab (x : Var) (y : Var) (ph : Wff) : Class :=
  let z : Var := freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ (ph).fv) 0
  (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))))

@[expose]
def syn_wbr (A : Class) (R : Class) (B : Class) : Wff :=
  (.classMem (syn_cop A B) R)

@[expose]
def syn_c1st : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (syn_copab x y (syn_wex z (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))))

@[expose]
def syn_cswap : Class :=
  let w : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  let z : Var := freshVar ((∅ : Finset Var)) 3
  (syn_copab x y (syn_wex z (syn_wex w (syn_wa (.classEq (.cv x) (syn_cop (.cv z) (.cv w)))
          (.classEq (.cv y) (syn_cop (.cv w) (.cv z)))))))

@[expose]
def syn_csset : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (syn_copab x y (syn_wss (.cv x) (.cv y)))

@[expose]
def syn_ccom (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  let z : Var := freshVar ((A).fv ∪ (B).fv) 2
  (syn_copab x y (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))))

@[expose]
def syn_cima (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  (.cab x (syn_wrex y B (syn_wbr (.cv y) A (.cv x))))

@[expose]
def syn_csi (A : Class) : Class :=
  let w : Var := freshVar ((A).fv) 0
  let x : Var := freshVar ((A).fv) 1
  let y : Var := freshVar ((A).fv) 2
  let z : Var := freshVar ((A).fv) 3
  (syn_copab x y (syn_wex z (syn_wex w
        (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w)))
          (syn_wbr (.cv z) A (.cv w))))))

@[expose]
def syn_cid : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (syn_copab x y (.objEq x y))

@[expose]
def syn_cxp (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))

@[expose]
def syn_ccnv (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (syn_copab x y (syn_wbr (.cv y) A (.cv x)))

@[expose]
def syn_crn (A : Class) : Class :=
  (syn_cima A (syn_cvv))

@[expose]
def syn_cdm (A : Class) : Class :=
  (syn_crn (syn_ccnv A))

@[expose]
def syn_cres (A : Class) (B : Class) : Class :=
  (syn_cin A (syn_cxp B (syn_cvv)))

@[expose]
def syn_wfun (A : Class) : Wff :=
  (syn_wss (syn_ccom A (syn_ccnv A)) (syn_cid))

@[expose]
def syn_wfn (A : Class) (B : Class) : Wff :=
  (syn_wa (syn_wfun A) (.classEq (syn_cdm A) B))

@[expose]
def syn_wf (F : Class) (A : Class) (B : Class) : Wff :=
  (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B))

@[expose]
def syn_wf1 (F : Class) (A : Class) (B : Class) : Wff :=
  (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F)))

@[expose]
def syn_wfo (F : Class) (A : Class) (B : Class) : Wff :=
  (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))

@[expose]
def syn_wf1o (F : Class) (A : Class) (B : Class) : Wff :=
  (syn_wa (syn_wf1 F A B) (syn_wfo F A B))

@[expose]
def syn_cfv (F : Class) (A : Class) : Class :=
  let x : Var := freshVar ((F).fv ∪ (A).fv) 0
  (syn_cio x (syn_wbr A F (.cv x)))

@[expose]
def syn_c2nd : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (syn_copab x y (syn_wex z (.classEq (.cv x) (syn_cop (.cv z) (.cv y)))))

@[expose]
def syn_co (A : Class) (F : Class) (B : Class) : Class :=
  (syn_cfv F (syn_cop A B))

@[expose]
def syn_coprab (x : Var) (y : Var) (z : Var) (ph : Wff) : Class :=
  let w : Var :=
    freshVar
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ (ph).fv) 0
  (.cab w (syn_wex x (syn_wex y (syn_wex z
          (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))))

@[expose]
def syn_cmpt (x : Var) (A : Class) (B : Class) : Class :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0
  (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))

@[expose]
def syn_cmpt2 (x : Var) (A : Class) (y : Var) (B : Class) (C : Class) : Class :=
  let z : Var :=
    freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0
  (syn_coprab x y z
    (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv z) C)))

@[expose]
def syn_ctxp (A : Class) (B : Class) : Class :=
  (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c2nd)) B))

@[expose]
def syn_cfix (A : Class) : Class :=
  (syn_crn (syn_cin A (syn_cid)))

@[expose]
def syn_ccup : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cun (.cv x) (.cv y)))

@[expose]
def syn_cdisj : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (syn_copab x y (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))

@[expose]
def syn_caddcfn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cplc (.cv x) (.cv y)))

@[expose]
def syn_ccompose : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_ccom (.cv x) (.cv y)))

@[expose]
def syn_cins2 (A : Class) : Class :=
  (syn_ctxp (syn_cvv) A)

@[expose]
def syn_cins3 (A : Class) : Class :=
  (syn_ctxp A (syn_cvv))

@[expose]
def syn_cimage (A : Class) : Class :=
  (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c)))

@[expose]
def syn_cins4 (A : Class) : Class :=
  (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) A)

@[expose]
def syn_csi3 (A : Class) : Class :=
  (syn_cima (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
        (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_cpw1 A))

@[expose]
def syn_cfuns : Class :=
  let f : Var := freshVar ((∅ : Finset Var)) 0
  (.cab f (syn_wfun (.cv f)))

@[expose]
def syn_cfns : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let f : Var := freshVar ((∅ : Finset Var)) 1
  (syn_copab f a (syn_wfn (.cv f) (.cv a)))

@[expose]
def syn_cpw1fn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (syn_cmpt x (syn_c1c) (syn_cpw1 (syn_cuni (.cv x))))

@[expose]
def syn_cfullfun (F : Class) : Class :=
  (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp
      (syn_ccompl
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_csn (syn_c0))))

@[expose]
def syn_cclos1 (S : Class) (R : Class) : Class :=
  let a : Var := freshVar ((S).fv ∪ (R).fv) 0
  (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))

@[expose]
def syn_ctrans : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  let z : Var := freshVar ((∅ : Finset Var)) 4
  (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
            (syn_wbr (.cv x) (.cv r) (.cv z)))))))

@[expose]
def syn_cref : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  (syn_copab r a (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x))))

@[expose]
def syn_cantisym : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a)
        (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
          (.objEq x y)))))

@[expose]
def syn_cpartial : Class :=
  (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym))

@[expose]
def syn_cconnex : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a)
        (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))))

@[expose]
def syn_cstrict : Class :=
  (syn_cin (syn_cpartial) (syn_cconnex))

@[expose]
def syn_cfound : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  let z : Var := freshVar ((∅ : Finset Var)) 4
  (syn_copab r a (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
        (syn_wrex z (.cv x)
          (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))

@[expose]
def syn_cwe : Class :=
  (syn_cin (syn_cstrict) (syn_cfound))

@[expose]
def syn_csym : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a)
        (.imp (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))))

@[expose]
def syn_cer : Class :=
  (syn_cin (syn_csym) (syn_ctrans))

@[expose]
def syn_cec (A : Class) (R : Class) : Class :=
  (syn_cima R (syn_csn A))

@[expose]
def syn_cqs (A : Class) (R : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (R).fv) 0
  let y : Var := freshVar ((A).fv ∪ (R).fv) 1
  (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cec (.cv x) R))))

@[expose]
def syn_cmap : Class :=
  let f : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  (syn_cmpt2 x (syn_cvv) y (syn_cvv) (.cab f (syn_wf (.cv f) (.cv y) (.cv x))))

@[expose]
def syn_cen : Class :=
  let f : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  (syn_copab x y (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y))))

@[expose]
def syn_cncs : Class :=
  (syn_cqs (syn_cvv) (syn_cen))

@[expose]
def syn_clec : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let b : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  (syn_copab a b (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y)))))

@[expose]
def syn_cltc : Class :=
  (syn_cdif (syn_clec) (syn_cid))

@[expose]
def syn_cnc (A : Class) : Class :=
  (syn_cec A (syn_cen))

@[expose]
def syn_ctc (A : Class) : Class :=
  let b : Var := freshVar ((A).fv) 0
  let x : Var := freshVar ((A).fv) 1
  (syn_cio b (syn_wa (.classMem (.cv b) (syn_cncs))
      (syn_wrex x A (.classEq (.cv b) (syn_cnc (syn_cpw1 (.cv x)))))))

@[expose]
def syn_c2c : Class :=
  (syn_cnc (syn_cpr (syn_c0) (syn_cvv)))

@[expose]
def syn_c3c : Class :=
  (syn_cnc (syn_ctp (syn_c0) (syn_cvv) (syn_cdif (syn_cvv) (syn_csn (syn_c0)))))

@[expose]
def syn_cce : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let b : Var := freshVar ((∅ : Finset Var)) 1
  let g : Var := freshVar ((∅ : Finset Var)) 2
  let m : Var := freshVar ((∅ : Finset Var)) 3
  let n : Var := freshVar ((∅ : Finset Var)) 4
  (syn_cmpt2 n (syn_cncs) m (syn_cncs) (.cab g (syn_wex a (syn_wex b
          (syn_w3a (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv m))
            (syn_wbr (.cv g) (syn_cen) (syn_co (.cv a) (syn_cmap) (.cv b))))))))

@[expose]
def syn_ctcfn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (syn_cmpt x (syn_c1c) (syn_ctc (syn_cuni (.cv x))))

@[expose]
def syn_cspac : Class :=
  let m : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  (syn_cmpt m (syn_cncs) (syn_cclos1 (syn_csn (.cv m)) (syn_copab x y
        (syn_w3a (.classMem (.cv x) (syn_cncs)) (.classMem (.cv y) (syn_cncs))
          (.classEq (.cv y) (syn_co (syn_c2c) (syn_cce) (.cv x)))))))

/-! Small reduction checks for a no-dummy and a dummy-bearing definition. -/

example (p q : Wff) : syn_wb p q = Wff.biimp p q := by rfl

example (x : Var) (p : Wff) :
    let support : Finset Var := ({ x } : Finset Var) ∪ p.fv
    let y := freshVar support 0
    syn_weu x p = Wff.ex y (.all x (Wff.biimp p (.objEq x y))) :=
  by rfl

end NFChoice.Compiler.CompactSourceSyntax
