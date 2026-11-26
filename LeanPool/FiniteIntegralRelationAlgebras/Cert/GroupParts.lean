/-
Copyright (c) 2026 Chris Henson and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson, Lean Pool contributors
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Orbit

/-! # Independent checks of a permutation group certificate

Each multiplication row is checked separately so its reduction cache can be released before
checking the next row.
-/

@[expose] public section

namespace RACert

/-- Verify that a generator's multiplication row agrees with composition of permutations. -/
noncomputable def checkMultiplicationRow (t : ℕ) (perms : List (List ℕ × List ℕ))
    (g : ℕ × List ℕ) : Bool :=
  allZip 0 (fun e c => Nat.blt c perms.length &&
    eqComp (pAt perms g.1) t (pAtB (blocks blockLen perms.length perms) c) e.1) perms g.2

/-- Verify that the inverse row agrees with the inverse permutations in the table. -/
noncomputable def checkInverseRow (t : ℕ) (perms : List (List ℕ × List ℕ))
    (inv : List ℕ) : Bool :=
  allZip 0 (fun e c => Nat.blt c perms.length &&
    eqOn t (pAtB (blocks blockLen perms.length perms) c) e.2) perms inv

/-- Assemble a group certificate from independently checked rows and structural conditions. -/
theorem checkBitGroup_of_parts {t : ℕ} {perms : List (List ℕ × List ℕ)}
    {gens : List (ℕ × List ℕ)} {inv : List ℕ}
    (hvalid : perms.all (fun e => checkBitPerm t e.1 e.2) = true)
    (hnonempty : Nat.blt 0 perms.length = true)
    (hidentity : (allRange t fun x => Nat.beq (nth 0 (pAt perms 0) x) x) = true)
    (horder : increasing (perms.map fun e => permCode t e.1) = true)
    (hrows : gens.all (checkMultiplicationRow t perms) = true)
    (hcoverage : Nat.beq (Nat.lor (maskOf (gens.flatMap fun g => childrenFrom 0 g.2)) 1)
      (Nat.sub (Nat.pow 2 perms.length) 1) = true)
    (hinverse : checkInverseRow t perms inv = true) : checkBitGroup t perms gens inv = true := by
  simp only [checkBitGroup, Bool.and_eq_true]
  exact ⟨hvalid, hnonempty, hidentity, horder, hrows, hcoverage, hinverse⟩

end RACert
