/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Model
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Prim

/-!
# Counting problems and their certificates

A `Problem` packages, for a fixed atom symmetry `σ` (given by its code list `perm`), the data
needed to count the lawful cycle sets invariant under `σ` as models of a Boolean formula:

* `cls` assigns to each triple of atom codes either a constant (`0`, `1`) or a variable (`j + 2`),
  the variables being the orbits of diversity triples under the Peircean transformations and `σ`;
* `reps` and `path` certify that these classes are exactly orbits;
* `quads` lists the quadruples whose associativity conditions make up the formula, and `wit`
  certifies that every other quadruple is equivalent to a listed one.

`Problem.check` verifies the certificate by computation, and `Problem.fixCountL_eq` is the
resulting identity between the number of invariant lawful cycle sets and a number of Boolean
assignments.
-/

@[expose] public section

namespace RACert

open FiniteIntegralRelationAlgebras.RelationAlgebra IntegralAtom

/-- The data of a counting problem; see the module docstring. -/
structure Problem where
  /-- The number of symmetric diversity atoms. -/
  s : ℕ
  /-- The number of pairs of nonsymmetric atoms. -/
  n : ℕ
  /-- The symmetry, as a list of codes. -/
  perm : List ℕ
  /-- The inverse of the symmetry. -/
  pinv : List ℕ
  /-- The number of variables. -/
  V : ℕ
  /-- The class of each triple: `0` (absent), `1` (present), or `j + 2` (variable `j`). -/
  cls : List (List (List ℕ))
  /-- The code of a representative triple of each variable. -/
  reps : List ℕ
  /-- For each triple, a word in the generators leading to the representative of its class. -/
  path : List (List (List ℕ))
  /-- Codes of the quadruples to be checked. -/
  quads : List ℕ
  /-- For each quadruple, a word in the generators leading into `quads`. -/
  wit : List (List (List (List ℕ)))

/-- The value of a class under an assignment of the variables. -/
def litB (v : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | 1 => true
  | j + 2 => v j

/-- The code of a triple. -/
def tcode (k a b c : ℕ) : ℕ := (a * k + b) * k + c

/-- The code of a quadruple. -/
def qcode (k r u t p : ℕ) : ℕ := ((r * k + u) * k + t) * k + p

theorem mul_add_div_mod {k x c : ℕ} (hc : c < k) : (x * k + c) / k = x ∧ (x * k + c) % k = c := by
  have hk : 0 < k := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem tcode_decode {k a b c : ℕ} (ha : a < k) (hb : b < k) (hc : c < k) :
    tcode k a b c / k / k % k = a ∧ tcode k a b c / k % k = b ∧ tcode k a b c % k = c := by
  unfold tcode
  rw [(mul_add_div_mod hc).1, (mul_add_div_mod hc).2, (mul_add_div_mod hb).1,
    (mul_add_div_mod hb).2, Nat.mod_eq_of_lt ha]
  exact ⟨rfl, rfl, rfl⟩

theorem qcode_decode {k r u t p : ℕ} (hr : r < k) (hu : u < k) (ht : t < k) (hp : p < k) :
    qcode k r u t p / k / k / k % k = r ∧ qcode k r u t p / k / k % k = u ∧
      qcode k r u t p / k % k = t ∧ qcode k r u t p % k = p := by
  unfold qcode
  rw [(mul_add_div_mod hp).1, (mul_add_div_mod hp).2, (mul_add_div_mod ht).1,
    (mul_add_div_mod ht).2, (mul_add_div_mod hu).1, (mul_add_div_mod hu).2, Nat.mod_eq_of_lt hr]
  exact ⟨rfl, rfl, rfl, rfl⟩

namespace Problem

variable (P : Problem)

/-- The number of atoms. -/
abbrev k : ℕ := numAtoms P.s P.n

/-- The symmetry on codes. -/
noncomputable def pm (c : ℕ) : ℕ := nth 0 P.perm c

/-- The inverse symmetry on codes. -/
noncomputable def pmi (c : ℕ) : ℕ := nth 0 P.pinv c

/-- The class of a triple. -/
noncomputable def clsAt (a b c : ℕ) : ℕ := nth 0 (nth [] (nth [] P.cls a) b) c

/-- The path word of a triple. -/
noncomputable def pathAt (a b c : ℕ) : ℕ := nth 0 (nth [] (nth [] P.path a) b) c

/-- The witness word of a quadruple. -/
noncomputable def witAt (r u t p : ℕ) : ℕ := nth 0 (nth [] (nth [] (nth [] P.wit r) u) t) p

/-- The Boolean table determined by an assignment of the variables. -/
noncomputable def tbl (v : ℕ → Bool) (a b c : ℕ) : Bool := litB v (P.clsAt a b c)

/-- Follow a word of generators (base `8` digits: `1` left, `2` right, `3` symmetry, otherwise
inverse symmetry) from a triple, returning the code of the final triple. -/
noncomputable def walk3 : (fuel w a b c : ℕ) → ℕ
  | 0, _, a, b, c => tcode P.k a b c
  | f + 1, w, a, b, c =>
    bif Nat.beq w 0 then tcode P.k a b c
    else bif Nat.beq (w % 8) 1 then walk3 f (w / 8) (cvN P.s a) c b
    else bif Nat.beq (w % 8) 2 then walk3 f (w / 8) c (cvN P.s b) a
    else bif Nat.beq (w % 8) 3 then walk3 f (w / 8) (P.pm a) (P.pm b) (P.pm c)
    else walk3 f (w / 8) (P.pmi a) (P.pmi b) (P.pmi c)

/-- Follow a word of generators (base `4` digits: `1` rotation, `2` reflection, otherwise symmetry)
from a quadruple, returning the code of the final quadruple. -/
noncomputable def walk4 : (fuel w r u t p : ℕ) → ℕ
  | 0, _, r, u, t, p => qcode P.k r u t p
  | f + 1, w, r, u, t, p =>
    bif Nat.beq w 0 then qcode P.k r u t p
    else bif Nat.beq (w % 4) 1 then walk4 f (w / 4) u t (cvN P.s p) (cvN P.s r)
    else bif Nat.beq (w % 4) 2 then
      walk4 f (w / 4) (cvN P.s t) (cvN P.s u) (cvN P.s r) (cvN P.s p)
    else walk4 f (w / 4) (P.pm r) (P.pm u) (P.pm t) (P.pm p)

/-- The maximal length of the words in a certificate. -/
def fuel : ℕ := 64

/-- The symmetry and its inverse are maps of codes, inverse to each other, commuting with
converse. -/
noncomputable def checkPerm : Bool :=
  allRange P.k fun c =>
    Nat.blt (P.pm c) P.k && (Nat.blt (P.pmi c) P.k && (Nat.beq (P.pm (P.pmi c)) c &&
      Nat.beq (P.pm (cvN P.s c)) (cvN P.s (P.pm c))))

/-- Triples containing the identity have the constant class forced by the identity laws. -/
noncomputable def checkId : Bool :=
  allRange P.k fun a => allRange P.k fun c =>
    Nat.beq (P.clsAt a 0 c) (bif Nat.beq c a then 1 else 0) &&
      (Nat.beq (P.clsAt 0 a c) (bif Nat.beq c a then 1 else 0) &&
        Nat.beq (P.clsAt a c 0) (bif Nat.beq c (cvN P.s a) then 1 else 0))

/-- Classes are invariant under the Peircean transformations and the symmetry. -/
noncomputable def checkInv : Bool :=
  allRange P.k fun a => allRange P.k fun b => allRange P.k fun c =>
    Nat.beq (P.clsAt (cvN P.s a) c b) (P.clsAt a b c) &&
      (Nat.beq (P.clsAt c (cvN P.s b) a) (P.clsAt a b c) &&
        Nat.beq (P.clsAt (P.pm a) (P.pm b) (P.pm c)) (P.clsAt a b c))

/-- Diversity triples are variables, connected to the representative of their class. -/
noncomputable def checkDiv : Bool :=
  allRange P.k fun a => allRange P.k fun b => allRange P.k fun c =>
    Nat.beq a 0 || (Nat.beq b 0 || (Nat.beq c 0 ||
      (Nat.ble 2 (P.clsAt a b c) && (Nat.blt (P.clsAt a b c) (P.V + 2) &&
        Nat.beq (P.walk3 fuel (P.pathAt a b c) a b c) (nth 0 P.reps (P.clsAt a b c - 2))))))

/-- The representative of variable `j` has class `j + 2`. -/
noncomputable def checkReps : Bool :=
  allRange P.V fun j =>
    Nat.beq (P.clsAt (nth 0 P.reps j / P.k / P.k % P.k) (nth 0 P.reps j / P.k % P.k)
      (nth 0 P.reps j % P.k)) (j + 2)

/-- Every quadruple of diversity atoms is equivalent to one in `quads`. -/
noncomputable def checkCover : Bool :=
  allRange P.k fun r => allRange P.k fun u => allRange P.k fun t => allRange P.k fun p =>
    Nat.beq r 0 || (Nat.beq u 0 || (Nat.beq t 0 || (Nat.beq p 0 ||
      Nat.testBit (maskOf P.quads) (P.walk4 fuel (P.witAt r u t p) r u t p))))

/-- The certificate check. -/
noncomputable def check : Bool :=
  P.checkPerm && (P.checkId && (P.checkInv && (P.checkDiv && (P.checkReps && P.checkCover))))

/-- Decode the first atom of a quadruple. -/
abbrev quadFirst (x : ℕ) : ℕ := x / P.k / P.k / P.k % P.k

/-- Decode the second atom of a quadruple. -/
abbrev quadSecond (x : ℕ) : ℕ := x / P.k / P.k % P.k

/-- Decode the third atom of a quadruple. -/
abbrev quadThird (x : ℕ) : ℕ := x / P.k % P.k

/-- Decode the fourth atom of a quadruple. -/
abbrev quadFourth (x : ℕ) : ℕ := x % P.k

/-- The associativity condition of the quadruple with code `x`. -/
noncomputable def quadAt (v : ℕ → Bool) (x : ℕ) : Bool :=
  quadB P.s P.k (P.tbl v) (x / P.k / P.k / P.k % P.k) (x / P.k / P.k % P.k) (x / P.k % P.k)
    (x % P.k)

/-- The formula: all listed quadruples satisfy their associativity condition. -/
noncomputable def phi (v : ℕ → Bool) : Bool := P.quads.all fun x => P.quadAt v x

end Problem

/-- Extend an assignment of the first `V` variables by `false`. -/
def extFin (V : ℕ) (v : Fin V → Bool) (j : ℕ) : Bool := if h : j < V then v ⟨j, h⟩ else false

theorem litB_beq (v : ℕ → Bool) (c a : ℕ) :
    litB v (bif Nat.beq c a then 1 else 0) = decide (c = a) := by
  by_cases h : c = a
  · subst h
    have hb : Nat.beq c c = true := by rw [Nat.beq_eq]
    rw [hb]
    simp [litB]
  · have hb : Nat.beq c a = false := by rw [Bool.eq_false_iff, Ne, Nat.beq_eq]; exact h
    simp [hb, litB, h]

namespace Problem

variable {P : Problem}

theorem checkPerm_spec (h : P.check = true) {c : ℕ} (hc : c < P.k) :
    P.pm c < P.k ∧ P.pmi c < P.k ∧ P.pm (P.pmi c) = c ∧ P.pm (cvN P.s c) = cvN P.s (P.pm c) := by
  simp only [check, Bool.and_eq_true] at h
  have h1 := allRange_iff.mp h.1 c hc
  simpa only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] using h1

theorem checkId_spec (h : P.check = true) {a c : ℕ} (ha : a < P.k) (hc : c < P.k) :
    P.clsAt a 0 c = (bif Nat.beq c a then 1 else 0) ∧
      P.clsAt 0 a c = (bif Nat.beq c a then 1 else 0) ∧
      P.clsAt a c 0 = (bif Nat.beq c (cvN P.s a) then 1 else 0) := by
  simp only [check, Bool.and_eq_true] at h
  have h1 := allRange_iff.mp (allRange_iff.mp h.2.1 a ha) c hc
  simpa only [Bool.and_eq_true, Nat.beq_eq] using h1

theorem checkInv_spec (h : P.check = true) {a b c : ℕ} (ha : a < P.k) (hb : b < P.k)
    (hc : c < P.k) :
    P.clsAt (cvN P.s a) c b = P.clsAt a b c ∧ P.clsAt c (cvN P.s b) a = P.clsAt a b c ∧
      P.clsAt (P.pm a) (P.pm b) (P.pm c) = P.clsAt a b c := by
  simp only [check, Bool.and_eq_true] at h
  have h1 := allRange_iff.mp (allRange_iff.mp (allRange_iff.mp h.2.2.1 a ha) b hb) c hc
  simpa only [Bool.and_eq_true, Nat.beq_eq] using h1

theorem checkDiv_spec (h : P.check = true) {a b c : ℕ} (ha : a < P.k) (hb : b < P.k)
    (hc : c < P.k) (h0 : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) :
    2 ≤ P.clsAt a b c ∧ P.clsAt a b c < P.V + 2 ∧
      P.walk3 fuel (P.pathAt a b c) a b c = nth 0 P.reps (P.clsAt a b c - 2) := by
  simp only [check, Bool.and_eq_true] at h
  have h1 := allRange_iff.mp (allRange_iff.mp (allRange_iff.mp h.2.2.2.1 a ha) b hb) c hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at h1
  rcases h1 with h1 | h1 | h1 | h1
  · exact absurd h1 h0.1
  · exact absurd h1 h0.2.1
  · exact absurd h1 h0.2.2
  · exact h1

theorem checkReps_spec (h : P.check = true) {j : ℕ} (hj : j < P.V) :
    P.clsAt (nth 0 P.reps j / P.k / P.k % P.k) (nth 0 P.reps j / P.k % P.k)
      (nth 0 P.reps j % P.k) = j + 2 := by
  simp only [check, Bool.and_eq_true] at h
  have h1 := allRange_iff.mp h.2.2.2.2.1 j hj
  simpa only [Nat.beq_eq] using h1

theorem checkCover_spec (h : P.check = true) {r u t p : ℕ} (hr : r < P.k) (hu : u < P.k)
    (ht : t < P.k) (hp : p < P.k) (h0 : r ≠ 0 ∧ u ≠ 0 ∧ t ≠ 0 ∧ p ≠ 0) :
    P.walk4 fuel (P.witAt r u t p) r u t p ∈ P.quads := by
  simp only [check, Bool.and_eq_true] at h
  have h1 := allRange_iff.mp (allRange_iff.mp (allRange_iff.mp
    (allRange_iff.mp h.2.2.2.2.2 r hr) u hu) t ht) p hp
  simp only [Bool.or_eq_true, Nat.beq_eq, testBit_maskOf, decide_eq_true_iff] at h1
  rcases h1 with h1 | h1 | h1 | h1 | h1
  · exact absurd h1 h0.1
  · exact absurd h1 h0.2.1
  · exact absurd h1 h0.2.2.1
  · exact absurd h1 h0.2.2.2
  · exact h1

/-- The table of any assignment satisfies the identity and Peircean conditions. -/
theorem peirceTbl_tbl (h : P.check = true) (v : ℕ → Bool) : PeirceTbl P.s P.n (P.tbl v) where
  id_right a ha c hc := by rw [tbl, (checkId_spec h ha hc).1, litB_beq]
  id_left a ha c hc := by rw [tbl, (checkId_spec h ha hc).2.1, litB_beq]
  id_out a ha b hb := by rw [tbl, (checkId_spec h ha hb).2.2, litB_beq]
  left a ha b hb c hc := by rw [tbl, tbl, (checkInv_spec h ha hb hc).1]
  right a ha b hb c hc := by rw [tbl, tbl, (checkInv_spec h ha hb hc).2.1]

/-- The table of any assignment is invariant under the symmetry. -/
theorem sigInv_tbl (h : P.check = true) (v : ℕ → Bool) : SigInv P.k (P.tbl v) P.pm P.pmi where
  lt a ha := (checkPerm_spec h ha).1
  inv_lt a ha := (checkPerm_spec h ha).2.1
  right_inv a ha := (checkPerm_spec h ha).2.2.1
  inv a ha b hb c hc := by rw [tbl, tbl, (checkInv_spec h ha hb hc).2.2]

theorem SigInv.inv' {k : ℕ} {X : ℕ → ℕ → ℕ → Bool} {f g : ℕ → ℕ} (h : SigInv k X f g) {a b c : ℕ}
    (ha : a < k) (hb : b < k) (hc : c < k) : X (g a) (g b) (g c) = X a b c := by
  have := h.inv _ (h.inv_lt a ha) _ (h.inv_lt b hb) _ (h.inv_lt c hc)
  rw [h.right_inv a ha, h.right_inv b hb, h.right_inv c hc] at this
  exact this.symm

/-- Walking along a word of generators does not change the value of an invariant table. -/
theorem walk3_spec {X : ℕ → ℕ → ℕ → Bool} (hX : PeirceTbl P.s P.n X)
    (hS : SigInv P.k X P.pm P.pmi) (fuel w : ℕ) {a b c : ℕ} (ha : a < P.k) (hb : b < P.k)
    (hc : c < P.k) :
    ∃ a' b' c', a' < P.k ∧ b' < P.k ∧ c' < P.k ∧ P.walk3 fuel w a b c = tcode P.k a' b' c' ∧
      X a' b' c' = X a b c := by
  induction fuel generalizing w a b c with
  | zero => exact ⟨a, b, c, ha, hb, hc, rfl, rfl⟩
  | succ f ih =>
    rw [walk3]
    cases h0 : Nat.beq w 0
    · cases h1 : Nat.beq (w % 8) 1
      · cases h2 : Nat.beq (w % 8) 2
        · cases h3 : Nat.beq (w % 8) 3
          · obtain ⟨a', b', c', ha', hb', hc', e1, e2⟩ :=
              ih (w / 8) (hS.inv_lt a ha) (hS.inv_lt b hb) (hS.inv_lt c hc)
            exact ⟨a', b', c', ha', hb', hc', e1, e2.trans (SigInv.inv' hS ha hb hc)⟩
          · obtain ⟨a', b', c', ha', hb', hc', e1, e2⟩ :=
              ih (w / 8) (hS.lt a ha) (hS.lt b hb) (hS.lt c hc)
            exact ⟨a', b', c', ha', hb', hc', e1, e2.trans (hS.inv a ha b hb c hc)⟩
        · obtain ⟨a', b', c', ha', hb', hc', e1, e2⟩ := ih (w / 8) hc (cvN_lt hb) ha
          exact ⟨a', b', c', ha', hb', hc', e1, e2.trans (hX.right a ha b hb c hc)⟩
      · obtain ⟨a', b', c', ha', hb', hc', e1, e2⟩ := ih (w / 8) (cvN_lt ha) hc hb
        exact ⟨a', b', c', ha', hb', hc', e1, e2.trans (hX.left a ha b hb c hc)⟩
    · exact ⟨a, b, c, ha, hb, hc, rfl, rfl⟩

/-- Walking along a word of generators does not change the associativity condition. -/
theorem walk4_spec {X : ℕ → ℕ → ℕ → Bool} (hX : PeirceTbl P.s P.n X)
    (hS : SigInv P.k X P.pm P.pmi) (hcv : ∀ a < P.k, P.pm (cvN P.s a) = cvN P.s (P.pm a))
    (fuel w : ℕ) {r u t p : ℕ} (hr : r < P.k) (hu : u < P.k) (ht : t < P.k) (hp : p < P.k) :
    ∃ r' u' t' p', r' < P.k ∧ u' < P.k ∧ t' < P.k ∧ p' < P.k ∧
      P.walk4 fuel w r u t p = qcode P.k r' u' t' p' ∧
      quadB P.s P.k X r' u' t' p' = quadB P.s P.k X r u t p := by
  induction fuel generalizing w r u t p with
  | zero => exact ⟨r, u, t, p, hr, hu, ht, hp, rfl, rfl⟩
  | succ f ih =>
    rw [walk4]
    cases h0 : Nat.beq w 0
    · cases h1 : Nat.beq (w % 4) 1
      · cases h2 : Nat.beq (w % 4) 2
        · obtain ⟨r', u', t', p', hr', hu', ht', hp', e1, e2⟩ :=
            ih (w / 4) (hS.lt r hr) (hS.lt u hu) (hS.lt t ht) (hS.lt p hp)
          exact ⟨r', u', t', p', hr', hu', ht', hp', e1,
            e2.trans (hS.quadB_map hcv hr hu ht hp)⟩
        · obtain ⟨r', u', t', p', hr', hu', ht', hp', e1, e2⟩ :=
            ih (w / 4) (cvN_lt ht) (cvN_lt hu) (cvN_lt hr) (cvN_lt hp)
          exact ⟨r', u', t', p', hr', hu', ht', hp', e1, e2.trans (hX.quadB_flip hr hu ht hp)⟩
      · obtain ⟨r', u', t', p', hr', hu', ht', hp', e1, e2⟩ :=
          ih (w / 4) hu ht (cvN_lt hp) (cvN_lt hr)
        exact ⟨r', u', t', p', hr', hu', ht', hp', e1, e2.trans (hX.quadB_rot hr hu ht hp)⟩
    · exact ⟨r, u, t, p, hr, hu, ht, hp, rfl, rfl⟩

/-- If the listed quadruples satisfy their associativity conditions, then all quadruples do. -/
theorem quadB_of_phi (h : P.check = true) {v : ℕ → Bool} (hv : P.phi v = true) {r u t p : ℕ}
    (hr : r < P.k) (hu : u < P.k) (ht : t < P.k) (hp : p < P.k) :
    quadB P.s P.k (P.tbl v) r u t p = true := by
  have hX := peirceTbl_tbl h v
  by_cases h0 : r = 0 ∨ u = 0 ∨ t = 0 ∨ p = 0
  · exact hX.quadB_of_zero hr hu ht hp h0
  · have h0' : r ≠ 0 ∧ u ≠ 0 ∧ t ≠ 0 ∧ p ≠ 0 := by tauto
    obtain ⟨r', u', t', p', hr', hu', ht', hp', e1, e2⟩ :=
      walk4_spec hX (sigInv_tbl h v) (fun a ha => (checkPerm_spec h ha).2.2.2) fuel
        (P.witAt r u t p) hr hu ht hp
    have hmem := checkCover_spec h hr hu ht hp h0'
    rw [e1] at hmem
    have hq := List.all_eq_true.mp hv _ hmem
    obtain ⟨d1, d2, d3, d4⟩ := qcode_decode hr' hu' ht' hp'
    rw [quadAt, d1, d2, d3, d4] at hq
    rw [← e2]
    exact hq

/-- The assignment read off from a table at the representatives. -/
noncomputable def assignOf (P : Problem) (X : ℕ → ℕ → ℕ → Bool) (j : ℕ) : Bool :=
  X (nth 0 P.reps j / P.k / P.k % P.k) (nth 0 P.reps j / P.k % P.k) (nth 0 P.reps j % P.k)

/-- The table of an assignment has the value of variable `j` at its representative. -/
theorem assignOf_tbl (h : P.check = true) (v : ℕ → Bool) {j : ℕ} (hj : j < P.V) :
    assignOf P (P.tbl v) j = v j := by
  rw [assignOf, tbl, checkReps_spec h hj]
  rfl

/-- An invariant table satisfying the identity and Peircean conditions is the table of the
assignment read off at the representatives. -/
theorem tbl_assignOf (h : P.check = true) {X : ℕ → ℕ → ℕ → Bool} (hX : PeirceTbl P.s P.n X)
    (hS : SigInv P.k X P.pm P.pmi) {a b c : ℕ} (ha : a < P.k) (hb : b < P.k) (hc : c < P.k) :
    P.tbl (assignOf P X) a b c = X a b c := by
  by_cases h0 : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0
  · obtain ⟨h2, -, hw⟩ := checkDiv_spec h ha hb hc h0
    obtain ⟨a', b', c', ha', hb', hc', e1, e2⟩ := walk3_spec hX hS fuel (P.pathAt a b c) ha hb hc
    obtain ⟨d1, d2, d3⟩ := tcode_decode ha' hb' hc'
    obtain ⟨m, hm⟩ : ∃ m, P.clsAt a b c = m + 2 := ⟨P.clsAt a b c - 2, by omega⟩
    rw [tbl, hm]
    change assignOf P X m = _
    rw [assignOf, show m = P.clsAt a b c - 2 by omega, ← hw, e1, d1, d2, d3, e2]
  · have hk := numAtoms_pos P.s P.n
    have h0' : a = 0 ∨ b = 0 ∨ c = 0 := by tauto
    rcases h0' with rfl | rfl | rfl
    · rw [tbl, (checkId_spec h hb hc).2.1, litB_beq, hX.id_left b hb c hc]
    · rw [tbl, (checkId_spec h ha hc).1, litB_beq, hX.id_right a ha c hc]
    · rw [tbl, (checkId_spec h ha hb).2.2, litB_beq, hX.id_out a ha b hb]

theorem enc_permFun (h : P.check = true) (a : IntegralAtom (Fin P.s) (Fin P.n)) :
    enc (permFun P.s P.n P.perm a) = P.pm (enc a) := by
  rw [permFun, ← nth_eq_getD, enc_dec]
  · rfl
  · exact (checkPerm_spec h (enc_lt a)).1

theorem permFun_dec (c : ℕ) (hc : c < P.k) :
    permFun P.s P.n P.perm (dec P.s P.n c) = dec P.s P.n (P.pm c) := by
  rw [permFun, ← nth_eq_getD, enc_dec hc]
  rfl

/-- The table of an invariant cycle set is invariant. -/
theorem sigInv_setTbl (h : P.check = true) {T : Set (Cycle (Fin P.s) (Fin P.n))}
    (hT : ∀ a b c, (permFun P.s P.n P.perm a, permFun P.s P.n P.perm b,
      permFun P.s P.n P.perm c) ∈ T ↔ (a, b, c) ∈ T) :
    SigInv P.k (setTbl T) P.pm P.pmi where
  lt a ha := (checkPerm_spec h ha).1
  inv_lt a ha := (checkPerm_spec h ha).2.1
  right_inv a ha := (checkPerm_spec h ha).2.2.1
  inv a ha b hb c hc := by
    rw [Bool.eq_iff_iff, setTbl_eq_true, setTbl_eq_true, ← permFun_dec a ha, ← permFun_dec b hb,
      ← permFun_dec c hc, hT]

/-- The set of lawful cycle sets invariant under the symmetry. -/
abbrev FixedSets (P : Problem) : Type :=
  {T : Set (Cycle (Fin P.s) (Fin P.n)) // IsLawfulCycles T ∧
    ∀ a b c, (permFun P.s P.n P.perm a, permFun P.s P.n P.perm b,
      permFun P.s P.n P.perm c) ∈ T ↔ (a, b, c) ∈ T}

/-- The set of models of the formula. -/
abbrev Models (P : Problem) : Type := {v : Fin P.V → Bool // P.phi (extFin P.V v) = true}

/-- The invariant lawful cycle set of a model. -/
noncomputable def modelSet (h : P.check = true) (v : Models P) : FixedSets P :=
  ⟨tblSet P.s P.n (P.tbl (extFin P.V v.val)),
    isLawfulCycles_tblSet (peirceTbl_tbl h _)
      (fun _ hr _ hu _ ht _ hp => quadB_of_phi h v.property hr hu ht hp),
    fun a b c => by
      rw [mem_tblSet, mem_tblSet, enc_permFun h, enc_permFun h, enc_permFun h,
        (sigInv_tbl h _).inv _ (enc_lt a) _ (enc_lt b) _ (enc_lt c)]⟩

theorem modelSet_injective (h : P.check = true) : Function.Injective (modelSet h) := by
  rintro ⟨v, hv⟩ ⟨v', hv'⟩ heq
  have heq' : tblSet P.s P.n (P.tbl (extFin P.V v)) = tblSet P.s P.n (P.tbl (extFin P.V v')) :=
    congrArg Subtype.val heq
  have key : ∀ a < P.k, ∀ b < P.k, ∀ c < P.k,
      P.tbl (extFin P.V v) a b c = P.tbl (extFin P.V v') a b c := by
    intro a ha b hb c hc
    have := Set.ext_iff.mp heq' (dec P.s P.n a, dec P.s P.n b, dec P.s P.n c)
    rw [mem_tblSet, mem_tblSet, enc_dec ha, enc_dec hb, enc_dec hc] at this
    exact Bool.eq_iff_iff.mpr this
  have hk := numAtoms_pos P.s P.n
  apply Subtype.ext
  funext ⟨j, hj⟩
  have e1 := assignOf_tbl h (extFin P.V v) hj
  have e2 := assignOf_tbl h (extFin P.V v') hj
  rw [assignOf, key _ (Nat.mod_lt _ hk) _ (Nat.mod_lt _ hk) _ (Nat.mod_lt _ hk)] at e1
  rw [assignOf] at e2
  have := e1.symm.trans e2
  simpa [extFin, hj] using this

theorem modelSet_surjective (h : P.check = true) : Function.Surjective (modelSet h) := by
  rintro ⟨T, hT, hfix⟩
  have hX := peirceTbl_setTbl hT
  have hS := sigInv_setTbl h hfix
  have key : ∀ a < P.k, ∀ b < P.k, ∀ c < P.k,
      P.tbl (extFin P.V fun j : Fin P.V => assignOf P (setTbl T) j) a b c = setTbl T a b c := by
    intro a ha b hb c hc
    rw [← tbl_assignOf h hX hS ha hb hc, tbl, tbl]
    by_cases h0 : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0
    · obtain ⟨h2, h3, -⟩ := checkDiv_spec h ha hb hc h0
      obtain ⟨m, hm⟩ : ∃ m, P.clsAt a b c = m + 2 := ⟨P.clsAt a b c - 2, by omega⟩
      have hmV : m < P.V := by omega
      rw [hm]
      simp [litB, extFin, hmV]
    · have h0' : a = 0 ∨ b = 0 ∨ c = 0 := by tauto
      rcases h0' with rfl | rfl | rfl
      · rw [(checkId_spec h hb hc).2.1, litB_beq, litB_beq]
      · rw [(checkId_spec h ha hc).1, litB_beq, litB_beq]
      · rw [(checkId_spec h ha hb).2.2, litB_beq, litB_beq]
  have hk := numAtoms_pos P.s P.n
  have hphi : P.phi (extFin P.V fun j : Fin P.V => assignOf P (setTbl T) j) = true := by
    rw [phi, List.all_eq_true]
    intro x _
    rw [quadAt, quadB_congr key (Nat.mod_lt _ hk) (Nat.mod_lt _ hk) (Nat.mod_lt _ hk)
      (Nat.mod_lt _ hk)]
    exact quadB_setTbl hT (Nat.mod_lt _ hk) (Nat.mod_lt _ hk) (Nat.mod_lt _ hk) (Nat.mod_lt _ hk)
  refine ⟨⟨_, hphi⟩, Subtype.ext ?_⟩
  change tblSet P.s P.n _ = T
  rw [tblSet_congr key, tblSet_setTbl]

/-- **The bridge.** For a checked certificate, the number of lawful cycle sets invariant under
the symmetry is the number of models of the formula. -/
theorem fixCountL_eq (h : P.check = true) :
    fixCountL P.s P.n P.perm = Fintype.card (Models P) := by
  rw [fixCountL, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨modelSet_injective h, modelSet_surjective h⟩)).symm

end Problem

end RACert
