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


/-- Compact nominal syntax for the upstream `wtru` operator. -/
@[expose]
def synWtru : Wff :=
  .imp .falsum .falsum

/-- Compact nominal syntax for the upstream `wb` operator. -/
@[expose]
def synWb (ph : Wff) (ps : Wff) : Wff :=
  (.neg (.imp (.imp ph ps) (.neg (.imp ps ph))))

/-- Compact nominal syntax for the upstream `wo` operator. -/
@[expose]
def synWo (ph : Wff) (ps : Wff) : Wff :=
  (.imp (.neg ph) ps)

/-- Compact nominal syntax for the upstream `wa` operator. -/
@[expose]
def synWa (ph : Wff) (ps : Wff) : Wff :=
  (.neg (.imp ph (.neg ps)))

/-- Compact nominal syntax for the upstream `w3o` operator. -/
@[expose]
def synW3o (ph : Wff) (ps : Wff) (ch : Wff) : Wff :=
  (synWo (synWo ph ps) ch)

/-- Compact nominal syntax for the upstream `w3a` operator. -/
@[expose]
def synW3a (ph : Wff) (ps : Wff) (ch : Wff) : Wff :=
  (synWa (synWa ph ps) ch)

/-- Compact nominal syntax for the upstream `wnan` operator. -/
@[expose]
def synWnan (ph : Wff) (ps : Wff) : Wff :=
  (.neg (synWa ph ps))

/-- Compact nominal syntax for the upstream `wex` operator. -/
@[expose]
def synWex (x : Var) (ph : Wff) : Wff :=
  (.neg (.all x (.neg ph)))

/-- Compact nominal syntax for the upstream `wnf` operator. -/
@[expose]
def synWnf (x : Var) (ph : Wff) : Wff :=
  (.all x (.imp ph (.all x ph)))

/-- Compact nominal syntax for the upstream `wsb` operator. -/
@[expose]
def synWsb (y : Var) (x : Var) (ph : Wff) : Wff :=
  (synWa (.imp (.objEq x y) ph) (synWex x (synWa (.objEq x y) ph)))

/-- Compact nominal syntax for the upstream `weu` operator. -/
@[expose]
def synWeu (x : Var) (ph : Wff) : Wff :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (ph).fv) 0
  (synWex y (.all x (synWb ph (.objEq x y))))

/-- Compact nominal syntax for the upstream `wmo` operator. -/
@[expose]
def synWmo (x : Var) (ph : Wff) : Wff :=
  (.imp (synWex x ph) (synWeu x ph))

/-- Compact nominal syntax for the upstream `wnfc` operator. -/
@[expose]
def synWnfc (x : Var) (A : Class) : Wff :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (A).fv) 0
  (.all y (synWnf x (.classMem (.cv y) A)))

/-- Compact nominal syntax for the upstream `wne` operator. -/
@[expose]
def synWne (A : Class) (B : Class) : Wff :=
  (.neg (.classEq A B))

/-- Compact nominal syntax for the upstream `wral` operator. -/
@[expose]
def synWral (x : Var) (A : Class) (ph : Wff) : Wff :=
  (.all x (.imp (.classMem (.cv x) A) ph))

/-- Compact nominal syntax for the upstream `wrex` operator. -/
@[expose]
def synWrex (x : Var) (A : Class) (ph : Wff) : Wff :=
  (synWex x (synWa (.classMem (.cv x) A) ph))

/-- Compact nominal syntax for the upstream `wreu` operator. -/
@[expose]
def synWreu (x : Var) (A : Class) (ph : Wff) : Wff :=
  (synWeu x (synWa (.classMem (.cv x) A) ph))

/-- Compact nominal syntax for the upstream `wrmo` operator. -/
@[expose]
def synWrmo (x : Var) (A : Class) (ph : Wff) : Wff :=
  (synWmo x (synWa (.classMem (.cv x) A) ph))

/-- Compact nominal syntax for the upstream `crab` operator. -/
@[expose]
def synCrab (x : Var) (A : Class) (ph : Wff) : Class :=
  (.cab x (synWa (.classMem (.cv x) A) ph))

/-- Compact nominal syntax for the upstream `cvv` operator. -/
@[expose]
def synCvv : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (.cab x (.objEq x x))

/-- Compact nominal syntax for the upstream `wsbc` operator. -/
@[expose]
def synWsbc (A : Class) (x : Var) (ph : Wff) : Wff :=
  (.classMem A (.cab x ph))

/-- Compact nominal syntax for the upstream `csb` operator. -/
@[expose]
def synCsb (A : Class) (x : Var) (B : Class) : Class :=
  let y : Var := freshVar ((A).fv ∪ ({ x } : Finset Var) ∪ (B).fv) 0
  (.cab y (synWsbc A x (.classMem (.cv y) B)))

/-- Compact nominal syntax for the upstream `cnin` operator. -/
@[expose]
def synCnin (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  (.cab x (synWnan (.classMem (.cv x) A) (.classMem (.cv x) B)))

/-- Compact nominal syntax for the upstream `ccompl` operator. -/
@[expose]
def synCcompl (A : Class) : Class :=
  (synCnin A A)

/-- Compact nominal syntax for the upstream `cin` operator. -/
@[expose]
def synCin (A : Class) (B : Class) : Class :=
  (synCcompl (synCnin A B))

/-- Compact nominal syntax for the upstream `cun` operator. -/
@[expose]
def synCun (A : Class) (B : Class) : Class :=
  (synCnin (synCcompl A) (synCcompl B))

/-- Compact nominal syntax for the upstream `cdif` operator. -/
@[expose]
def synCdif (A : Class) (B : Class) : Class :=
  (synCin A (synCcompl B))

/-- Compact nominal syntax for the upstream `csymdif` operator. -/
@[expose]
def synCsymdif (A : Class) (B : Class) : Class :=
  (synCun (synCdif A B) (synCdif B A))

/-- Compact nominal syntax for the upstream `wss` operator. -/
@[expose]
def synWss (A : Class) (B : Class) : Wff :=
  (.classEq (synCin A B) A)

/-- Compact nominal syntax for the upstream `wpss` operator. -/
@[expose]
def synWpss (A : Class) (B : Class) : Wff :=
  (synWa (synWss A B) (synWne A B))

/-- Compact nominal syntax for the upstream `c0` operator. -/
@[expose]
def synC0 : Class :=
  (synCdif (synCvv) (synCvv))

/-- Compact nominal syntax for the upstream `cif` operator. -/
@[expose]
def synCif (ph : Wff) (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((ph).fv ∪ (A).fv ∪ (B).fv) 0
  (.cab x (synWo (synWa (.classMem (.cv x) A) ph) (synWa (.classMem (.cv x) B) (.neg ph))))

/-- Compact nominal syntax for the upstream `cpw` operator. -/
@[expose]
def synCpw (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (synWss (.cv x) A))

/-- Compact nominal syntax for the upstream `csn` operator. -/
@[expose]
def synCsn (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (.classEq (.cv x) A))

/-- Compact nominal syntax for the upstream `cpr` operator. -/
@[expose]
def synCpr (A : Class) (B : Class) : Class :=
  (synCun (synCsn A) (synCsn B))

/-- Compact nominal syntax for the upstream `ctp` operator. -/
@[expose]
def synCtp (A : Class) (B : Class) (C : Class) : Class :=
  (synCun (synCpr A B) (synCsn C))

/-- Compact nominal syntax for the upstream `cuni` operator. -/
@[expose]
def synCuni (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (.cab x (synWex y (synWa (.objMem x y) (.classMem (.cv y) A))))

/-- Compact nominal syntax for the upstream `cint` operator. -/
@[expose]
def synCint (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (.cab x (.all y (.imp (.classMem (.cv y) A) (.objMem x y))))

/-- Compact nominal syntax for the upstream `ciun` operator. -/
@[expose]
def synCiun (x : Var) (A : Class) (B : Class) : Class :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0
  (.cab y (synWrex x A (.classMem (.cv y) B)))

/-- Compact nominal syntax for the upstream `copk` operator. -/
@[expose]
def synCopk (A : Class) (B : Class) : Class :=
  (synCpr (synCsn A) (synCpr A B))

/-- Compact nominal syntax for the upstream `c1c` operator. -/
@[expose]
def synC1c : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (.cab x (synWex y (.classEq (.cv x) (synCsn (.cv y)))))

/-- Compact nominal syntax for the upstream `cpw1` operator. -/
@[expose]
def synCpw1 (A : Class) : Class :=
  (synCin (synCpw A) (synC1c))

/-- Compact nominal syntax for the upstream `cuni1` operator. -/
@[expose]
def synCuni1 (A : Class) : Class :=
  (synCuni (synCin A (synC1c)))

/-- Compact nominal syntax for the upstream `cxpk` operator. -/
@[expose]
def synCxpk (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  let z : Var := freshVar ((A).fv ∪ (B).fv) 2
  (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
          (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))))))

/-- Compact nominal syntax for the upstream `ccnvk` operator. -/
@[expose]
def synCcnvk (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  let z : Var := freshVar ((A).fv) 2
  (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
          (.classMem (synCopk (.cv z) (.cv y)) A)))))

/-- Compact nominal syntax for the upstream `cins2k` operator. -/
@[expose]
def synCins2k (A : Class) : Class :=
  let t : Var := freshVar ((A).fv) 0
  let u : Var := freshVar ((A).fv) 1
  let v : Var := freshVar ((A).fv) 2
  let x : Var := freshVar ((A).fv) 3
  let y : Var := freshVar ((A).fv) 4
  let z : Var := freshVar ((A).fv) 5
  (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex t
            (synWex u (synWex v (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv t))))
                  (.classEq (.cv z) (synCopk (.cv u) (.cv v)))
                  (.classMem (synCopk (.cv t) (.cv v)) A)))))))))

/-- Compact nominal syntax for the upstream `cins3k` operator. -/
@[expose]
def synCins3k (A : Class) : Class :=
  let t : Var := freshVar ((A).fv) 0
  let u : Var := freshVar ((A).fv) 1
  let v : Var := freshVar ((A).fv) 2
  let x : Var := freshVar ((A).fv) 3
  let y : Var := freshVar ((A).fv) 4
  let z : Var := freshVar ((A).fv) 5
  (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex t
            (synWex u (synWex v (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv t))))
                  (.classEq (.cv z) (synCopk (.cv u) (.cv v)))
                  (.classMem (synCopk (.cv t) (.cv u)) A)))))))))

/-- Compact nominal syntax for the upstream `cimak` operator. -/
@[expose]
def synCimak (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  (.cab x (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) A)))

/-- Compact nominal syntax for the upstream `ccomk` operator. -/
@[expose]
def synCcomk (A : Class) (B : Class) : Class :=
  (synCimak (synCin (synCins2k A) (synCins3k (synCcnvk B))) (synCvv))

/-- Compact nominal syntax for the upstream `cp6` operator. -/
@[expose]
def synCp6 (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (synWss (synCxpk (synCvv) (synCsn (synCsn (.cv x)))) A))

/-- Compact nominal syntax for the upstream `csik` operator. -/
@[expose]
def synCsik (A : Class) : Class :=
  let t : Var := freshVar ((A).fv) 0
  let u : Var := freshVar ((A).fv) 1
  let x : Var := freshVar ((A).fv) 2
  let y : Var := freshVar ((A).fv) 3
  let z : Var := freshVar ((A).fv) 4
  (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex t
            (synWex u (synW3a (.classEq (.cv y) (synCsn (.cv t)))
                (.classEq (.cv z) (synCsn (.cv u)))
                (.classMem (synCopk (.cv t) (.cv u)) A))))))))

/-- Compact nominal syntax for the upstream `cssetk` operator. -/
@[expose]
def synCssetk : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
          (synWss (.cv y) (.cv z))))))

/-- Compact nominal syntax for the upstream `cimagek` operator. -/
@[expose]
def synCimagek (A : Class) : Class :=
  (synCdif (synCxpk (synCvv) (synCvv)) (synCimak (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
      (synCpw1 (synCpw1 (synC1c)))))

/-- Compact nominal syntax for the upstream `cidk` operator. -/
@[expose]
def synCidk : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (.cab x (synWex y
      (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (.objEq y z)))))

/-- Compact nominal syntax for the upstream `cio` operator. -/
@[expose]
def synCio (x : Var) (ph : Wff) : Class :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (ph).fv) 0
  (synCuni (.cab y (.classEq (.cab x ph) (synCsn (.cv y)))))

/-- Compact nominal syntax for the upstream `c0c` operator. -/
@[expose]
def synC0c : Class :=
  (synCsn (synC0))

/-- Compact nominal syntax for the upstream `cplc` operator. -/
@[expose]
def synCplc (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  let z : Var := freshVar ((A).fv ∪ (B).fv) 2
  (.cab x (synWrex y A (synWrex z B (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
          (.classEq (.cv x) (synCun (.cv y) (.cv z)))))))

/-- Compact nominal syntax for the upstream `cnnc` operator. -/
@[expose]
def synCnnc : Class :=
  let b : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (synCint (.cab b (synWa (.classMem (synC0c) (.cv b))
        (synWral y (.cv b) (.classMem (synCplc (.cv y) (synC1c)) (.cv b))))))

/-- Compact nominal syntax for the upstream `cfin` operator. -/
@[expose]
def synCfin : Class :=
  (synCuni (synCnnc))

/-- Compact nominal syntax for the upstream `clefin` operator. -/
@[expose]
def synClefin : Class :=
  let w : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  let z : Var := freshVar ((∅ : Finset Var)) 3
  (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
          (synWrex w (synCnnc) (.classEq (.cv z) (synCplc (.cv y) (.cv w))))))))

/-- Compact nominal syntax for the upstream `cltfin` operator. -/
@[expose]
def synCltfin : Class :=
  let m : Var := freshVar ((∅ : Finset Var)) 0
  let n : Var := freshVar ((∅ : Finset Var)) 1
  let p : Var := freshVar ((∅ : Finset Var)) 2
  let x : Var := freshVar ((∅ : Finset Var)) 3
  (.cab x (synWex m (synWex n (synWa (.classEq (.cv x) (synCopk (.cv m) (.cv n)))
          (synWa (synWne (.cv m) (synC0)) (synWrex p (synCnnc)
              (.classEq (.cv n) (synCplc (synCplc (.cv m) (.cv p)) (synC1c)))))))))

/-- Compact nominal syntax for the upstream `cncfin` operator. -/
@[expose]
def synCncfin (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x))))

/-- Compact nominal syntax for the upstream `ctfin` operator. -/
@[expose]
def synCtfin (M : Class) : Class :=
  let a : Var := freshVar ((M).fv) 0
  let n : Var := freshVar ((M).fv) 1
  (synCif (.classEq M (synC0)) (synC0) (synCio n (synWa (.classMem (.cv n) (synCnnc))
        (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))))

/-- Compact nominal syntax for the upstream `cevenfin` operator. -/
@[expose]
def synCevenfin : Class :=
  let n : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  (.cab x (synWa (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
      (synWne (.cv x) (synC0))))

/-- Compact nominal syntax for the upstream `coddfin` operator. -/
@[expose]
def synCoddfin : Class :=
  let n : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  (.cab x (synWa (synWrex n (synCnnc)
        (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWne (.cv x) (synC0))))

/-- Compact nominal syntax for the upstream `wsfin` operator. -/
@[expose]
def synWsfin (M : Class) (N : Class) : Wff :=
  let a : Var := freshVar ((M).fv ∪ (N).fv) 0
  (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
    (synWex a (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))))

/-- Compact nominal syntax for the upstream `cspfin` operator. -/
@[expose]
def synCspfin : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (synCint (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a))
        (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))))

/-- Compact nominal syntax for the upstream `cphi` operator. -/
@[expose]
def synCphi (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (.cab y (synWrex x A (.classEq (.cv y)
        (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c)) (.cv x)))))

/-- Compact nominal syntax for the upstream `cop` operator. -/
@[expose]
def synCop (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  (synCun (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))) (.cab x
      (synWrex y B (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))

/-- Compact nominal syntax for the upstream `cproj1` operator. -/
@[expose]
def synCproj1 (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (.classMem (synCphi (.cv x)) A))

/-- Compact nominal syntax for the upstream `cproj2` operator. -/
@[expose]
def synCproj2 (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  (.cab x (.classMem (synCun (synCphi (.cv x)) (synCsn (synC0c))) A))

/-- Compact nominal syntax for the upstream `copab` operator. -/
@[expose]
def synCopab (x : Var) (y : Var) (ph : Wff) : Class :=
  let z : Var := freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ (ph).fv) 0
  (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))))

/-- Compact nominal syntax for the upstream `wbr` operator. -/
@[expose]
def synWbr (A : Class) (R : Class) (B : Class) : Wff :=
  (.classMem (synCop A B) R)

/-- Compact nominal syntax for the upstream `c1st` operator. -/
@[expose]
def synC1st : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (synCopab x y (synWex z (.classEq (.cv x) (synCop (.cv y) (.cv z)))))

/-- Compact nominal syntax for the upstream `cswap` operator. -/
@[expose]
def synCswap : Class :=
  let w : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  let z : Var := freshVar ((∅ : Finset Var)) 3
  (synCopab x y (synWex z (synWex w (synWa (.classEq (.cv x) (synCop (.cv z) (.cv w)))
          (.classEq (.cv y) (synCop (.cv w) (.cv z)))))))

/-- Compact nominal syntax for the upstream `csset` operator. -/
@[expose]
def synCsset : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (synCopab x y (synWss (.cv x) (.cv y)))

/-- Compact nominal syntax for the upstream `ccom` operator. -/
@[expose]
def synCcom (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  let z : Var := freshVar ((A).fv ∪ (B).fv) 2
  (synCopab x y (synWex z (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))))

/-- Compact nominal syntax for the upstream `cima` operator. -/
@[expose]
def synCima (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  (.cab x (synWrex y B (synWbr (.cv y) A (.cv x))))

/-- Compact nominal syntax for the upstream `csi` operator. -/
@[expose]
def synCsi (A : Class) : Class :=
  let w : Var := freshVar ((A).fv) 0
  let x : Var := freshVar ((A).fv) 1
  let y : Var := freshVar ((A).fv) 2
  let z : Var := freshVar ((A).fv) 3
  (synCopab x y (synWex z (synWex w
        (synW3a (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv y) (synCsn (.cv w)))
          (synWbr (.cv z) A (.cv w))))))

/-- Compact nominal syntax for the upstream `cid` operator. -/
@[expose]
def synCid : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (synCopab x y (.objEq x y))

/-- Compact nominal syntax for the upstream `cxp` operator. -/
@[expose]
def synCxp (A : Class) (B : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (B).fv) 0
  let y : Var := freshVar ((A).fv ∪ (B).fv) 1
  (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))

/-- Compact nominal syntax for the upstream `ccnv` operator. -/
@[expose]
def synCcnv (A : Class) : Class :=
  let x : Var := freshVar ((A).fv) 0
  let y : Var := freshVar ((A).fv) 1
  (synCopab x y (synWbr (.cv y) A (.cv x)))

/-- Compact nominal syntax for the upstream `crn` operator. -/
@[expose]
def synCrn (A : Class) : Class :=
  (synCima A (synCvv))

/-- Compact nominal syntax for the upstream `cdm` operator. -/
@[expose]
def synCdm (A : Class) : Class :=
  (synCrn (synCcnv A))

/-- Compact nominal syntax for the upstream `cres` operator. -/
@[expose]
def synCres (A : Class) (B : Class) : Class :=
  (synCin A (synCxp B (synCvv)))

/-- Compact nominal syntax for the upstream `wfun` operator. -/
@[expose]
def synWfun (A : Class) : Wff :=
  (synWss (synCcom A (synCcnv A)) (synCid))

/-- Compact nominal syntax for the upstream `wfn` operator. -/
@[expose]
def synWfn (A : Class) (B : Class) : Wff :=
  (synWa (synWfun A) (.classEq (synCdm A) B))

/-- Compact nominal syntax for the upstream `wf` operator. -/
@[expose]
def synWf (F : Class) (A : Class) (B : Class) : Wff :=
  (synWa (synWfn F A) (synWss (synCrn F) B))

/-- Compact nominal syntax for the upstream `wf1` operator. -/
@[expose]
def synWf1 (F : Class) (A : Class) (B : Class) : Wff :=
  (synWa (synWf F A B) (synWfun (synCcnv F)))

/-- Compact nominal syntax for the upstream `wfo` operator. -/
@[expose]
def synWfo (F : Class) (A : Class) (B : Class) : Wff :=
  (synWa (synWfn F A) (.classEq (synCrn F) B))

/-- Compact nominal syntax for the upstream `wf1o` operator. -/
@[expose]
def synWf1o (F : Class) (A : Class) (B : Class) : Wff :=
  (synWa (synWf1 F A B) (synWfo F A B))

/-- Compact nominal syntax for the upstream `cfv` operator. -/
@[expose]
def synCfv (F : Class) (A : Class) : Class :=
  let x : Var := freshVar ((F).fv ∪ (A).fv) 0
  (synCio x (synWbr A F (.cv x)))

/-- Compact nominal syntax for the upstream `c2nd` operator. -/
@[expose]
def synC2nd : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  let z : Var := freshVar ((∅ : Finset Var)) 2
  (synCopab x y (synWex z (.classEq (.cv x) (synCop (.cv z) (.cv y)))))

/-- Compact nominal syntax for the upstream `co` operator. -/
@[expose]
def synCo (A : Class) (F : Class) (B : Class) : Class :=
  (synCfv F (synCop A B))

/-- Compact nominal syntax for the upstream `coprab` operator. -/
@[expose]
def synCoprab (x : Var) (y : Var) (z : Var) (ph : Wff) : Class :=
  let w : Var :=
    freshVar
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ (ph).fv) 0
  (.cab w (synWex x (synWex y (synWex z
          (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph)))))

/-- Compact nominal syntax for the upstream `cmpt` operator. -/
@[expose]
def synCmpt (x : Var) (A : Class) (B : Class) : Class :=
  let y : Var := freshVar (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0
  (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)))

/-- Compact nominal syntax for the upstream `cmpt2` operator. -/
@[expose]
def synCmpt2 (x : Var) (A : Class) (y : Var) (B : Class) (C : Class) : Class :=
  let z : Var :=
    freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0
  (synCoprab x y z
    (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv z) C)))

/-- Compact nominal syntax for the upstream `ctxp` operator. -/
@[expose]
def synCtxp (A : Class) (B : Class) : Class :=
  (synCin (synCcom (synCcnv (synC1st)) A) (synCcom (synCcnv (synC2nd)) B))

/-- Compact nominal syntax for the upstream `cfix` operator. -/
@[expose]
def synCfix (A : Class) : Class :=
  (synCrn (synCin A (synCid)))

/-- Compact nominal syntax for the upstream `ccup` operator. -/
@[expose]
def synCcup : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (synCmpt2 x (synCvv) y (synCvv) (synCun (.cv x) (.cv y)))

/-- Compact nominal syntax for the upstream `cdisj` operator. -/
@[expose]
def synCdisj : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (synCopab x y (.classEq (synCin (.cv x) (.cv y)) (synC0)))

/-- Compact nominal syntax for the upstream `caddcfn` operator. -/
@[expose]
def synCaddcfn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (synCmpt2 x (synCvv) y (synCvv) (synCplc (.cv x) (.cv y)))

/-- Compact nominal syntax for the upstream `ccompose` operator. -/
@[expose]
def synCcompose : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  let y : Var := freshVar ((∅ : Finset Var)) 1
  (synCmpt2 x (synCvv) y (synCvv) (synCcom (.cv x) (.cv y)))

/-- Compact nominal syntax for the upstream `cins2` operator. -/
@[expose]
def synCins2 (A : Class) : Class :=
  (synCtxp (synCvv) A)

/-- Compact nominal syntax for the upstream `cins3` operator. -/
@[expose]
def synCins3 (A : Class) : Class :=
  (synCtxp A (synCvv))

/-- Compact nominal syntax for the upstream `cimage` operator. -/
@[expose]
def synCimage (A : Class) : Class :=
  (synCcompl (synCima (synCsymdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synC1c)))

/-- Compact nominal syntax for the upstream `cins4` operator. -/
@[expose]
def synCins4 (A : Class) : Class :=
  (synCima (synCcnv (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))))) A)

/-- Compact nominal syntax for the upstream `csi3` operator. -/
@[expose]
def synCsi3 (A : Class) : Class :=
  (synCima (synCtxp (synCsi (synC1st)) (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
        (synCsi (synCcom (synC2nd) (synC2nd))))) (synCpw1 A))

/-- Compact nominal syntax for the upstream `cfuns` operator. -/
@[expose]
def synCfuns : Class :=
  let f : Var := freshVar ((∅ : Finset Var)) 0
  (.cab f (synWfun (.cv f)))

/-- Compact nominal syntax for the upstream `cfns` operator. -/
@[expose]
def synCfns : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let f : Var := freshVar ((∅ : Finset Var)) 1
  (synCopab f a (synWfn (.cv f) (.cv a)))

/-- Compact nominal syntax for the upstream `cpw1fn` operator. -/
@[expose]
def synCpw1fn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (synCmpt x (synC1c) (synCpw1 (synCuni (.cv x))))

/-- Compact nominal syntax for the upstream `cfullfun` operator. -/
@[expose]
def synCfullfun (F : Class) : Class :=
  (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (synCxp
      (synCcompl
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synCsn (synC0))))

/-- Compact nominal syntax for the upstream `cclos1` operator. -/
@[expose]
def synCclos1 (S : Class) (R : Class) : Class :=
  let a : Var := freshVar ((S).fv ∪ (R).fv) 0
  (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))

/-- Compact nominal syntax for the upstream `ctrans` operator. -/
@[expose]
def synCtrans : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  let z : Var := freshVar ((∅ : Finset Var)) 4
  (synCopab r a (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
            (synWbr (.cv x) (.cv r) (.cv z)))))))

/-- Compact nominal syntax for the upstream `cref` operator. -/
@[expose]
def synCref : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  (synCopab r a (synWral x (.cv a) (synWbr (.cv x) (.cv r) (.cv x))))

/-- Compact nominal syntax for the upstream `cantisym` operator. -/
@[expose]
def synCantisym : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  (synCopab r a (synWral x (.cv a) (synWral y (.cv a)
        (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
          (.objEq x y)))))

/-- Compact nominal syntax for the upstream `cpartial` operator. -/
@[expose]
def synCpartial : Class :=
  (synCin (synCin (synCref) (synCtrans)) (synCantisym))

/-- Compact nominal syntax for the upstream `cconnex` operator. -/
@[expose]
def synCconnex : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  (synCopab r a (synWral x (.cv a) (synWral y (.cv a)
        (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))))))

/-- Compact nominal syntax for the upstream `cstrict` operator. -/
@[expose]
def synCstrict : Class :=
  (synCin (synCpartial) (synCconnex))

/-- Compact nominal syntax for the upstream `cfound` operator. -/
@[expose]
def synCfound : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  let z : Var := freshVar ((∅ : Finset Var)) 4
  (synCopab r a (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
        (synWrex z (.cv x)
          (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))

/-- Compact nominal syntax for the upstream `cwe` operator. -/
@[expose]
def synCwe : Class :=
  (synCin (synCstrict) (synCfound))

/-- Compact nominal syntax for the upstream `csym` operator. -/
@[expose]
def synCsym : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let r : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  (synCopab r a (synWral x (.cv a) (synWral y (.cv a)
        (.imp (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))))))

/-- Compact nominal syntax for the upstream `cer` operator. -/
@[expose]
def synCer : Class :=
  (synCin (synCsym) (synCtrans))

/-- Compact nominal syntax for the upstream `cec` operator. -/
@[expose]
def synCec (A : Class) (R : Class) : Class :=
  (synCima R (synCsn A))

/-- Compact nominal syntax for the upstream `cqs` operator. -/
@[expose]
def synCqs (A : Class) (R : Class) : Class :=
  let x : Var := freshVar ((A).fv ∪ (R).fv) 0
  let y : Var := freshVar ((A).fv ∪ (R).fv) 1
  (.cab y (synWrex x A (.classEq (.cv y) (synCec (.cv x) R))))

/-- Compact nominal syntax for the upstream `cmap` operator. -/
@[expose]
def synCmap : Class :=
  let f : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  (synCmpt2 x (synCvv) y (synCvv) (.cab f (synWf (.cv f) (.cv y) (.cv x))))

/-- Compact nominal syntax for the upstream `cen` operator. -/
@[expose]
def synCen : Class :=
  let f : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  (synCopab x y (synWex f (synWf1o (.cv f) (.cv x) (.cv y))))

/-- Compact nominal syntax for the upstream `cncs` operator. -/
@[expose]
def synCncs : Class :=
  (synCqs (synCvv) (synCen))

/-- Compact nominal syntax for the upstream `clec` operator. -/
@[expose]
def synClec : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let b : Var := freshVar ((∅ : Finset Var)) 1
  let x : Var := freshVar ((∅ : Finset Var)) 2
  let y : Var := freshVar ((∅ : Finset Var)) 3
  (synCopab a b (synWrex x (.cv a) (synWrex y (.cv b) (synWss (.cv x) (.cv y)))))

/-- Compact nominal syntax for the upstream `cltc` operator. -/
@[expose]
def synCltc : Class :=
  (synCdif (synClec) (synCid))

/-- Compact nominal syntax for the upstream `cnc` operator. -/
@[expose]
def synCnc (A : Class) : Class :=
  (synCec A (synCen))

/-- Compact nominal syntax for the upstream `ctc` operator. -/
@[expose]
def synCtc (A : Class) : Class :=
  let b : Var := freshVar ((A).fv) 0
  let x : Var := freshVar ((A).fv) 1
  (synCio b (synWa (.classMem (.cv b) (synCncs))
      (synWrex x A (.classEq (.cv b) (synCnc (synCpw1 (.cv x)))))))

/-- Compact nominal syntax for the upstream `c2c` operator. -/
@[expose]
def synC2c : Class :=
  (synCnc (synCpr (synC0) (synCvv)))

/-- Compact nominal syntax for the upstream `c3c` operator. -/
@[expose]
def synC3c : Class :=
  (synCnc (synCtp (synC0) (synCvv) (synCdif (synCvv) (synCsn (synC0)))))

/-- Compact nominal syntax for the upstream `cce` operator. -/
@[expose]
def synCce : Class :=
  let a : Var := freshVar ((∅ : Finset Var)) 0
  let b : Var := freshVar ((∅ : Finset Var)) 1
  let g : Var := freshVar ((∅ : Finset Var)) 2
  let m : Var := freshVar ((∅ : Finset Var)) 3
  let n : Var := freshVar ((∅ : Finset Var)) 4
  (synCmpt2 n (synCncs) m (synCncs) (.cab g (synWex a (synWex b
          (synW3a (.classMem (synCpw1 (.cv a)) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv m))
            (synWbr (.cv g) (synCen) (synCo (.cv a) (synCmap) (.cv b))))))))

/-- Compact nominal syntax for the upstream `ctcfn` operator. -/
@[expose]
def synCtcfn : Class :=
  let x : Var := freshVar ((∅ : Finset Var)) 0
  (synCmpt x (synC1c) (synCtc (synCuni (.cv x))))

/-- Compact nominal syntax for the upstream `cspac` operator. -/
@[expose]
def synCspac : Class :=
  let m : Var := freshVar ((∅ : Finset Var)) 0
  let x : Var := freshVar ((∅ : Finset Var)) 1
  let y : Var := freshVar ((∅ : Finset Var)) 2
  (synCmpt m (synCncs) (synCclos1 (synCsn (.cv m)) (synCopab x y
        (synW3a (.classMem (.cv x) (synCncs)) (.classMem (.cv y) (synCncs))
          (.classEq (.cv y) (synCo (synC2c) (synCce) (.cv x)))))))

/-! Small reduction checks for a no-dummy and a dummy-bearing definition. -/

example (p q : Wff) : synWb p q = Wff.biimp p q := by rfl

example (x : Var) (p : Wff) :
    let support : Finset Var := ({ x } : Finset Var) ∪ p.fv
    let y := freshVar support 0
    synWeu x p = Wff.ex y (.all x (Wff.biimp p (.objEq x y))) :=
  by rfl

end NFChoice.Compiler.CompactSourceSyntax
