/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Enc

/-!
# Boolean tables for cycle sets

A cycle set on `IntegralAtom (Fin s) (Fin n)` is represented by a Boolean table
`X : ℕ → ℕ → ℕ → Bool` on atom codes. This file expresses lawfulness of the cycle set through
Boolean conditions on the table: the identity and Peircean conditions (`PeirceTbl`) and the
associativity condition for each quadruple of atoms (`quadB`), together with the symmetries of the
latter which allow checking only one quadruple in each orbit.
-/

@[expose] public section

namespace RACert

open FiniteIntegralRelationAlgebras.RelationAlgebra IntegralAtom

variable {s n : ℕ}

/-- The cycle set of a Boolean table on codes. -/
def tblSet (s n : ℕ) (X : ℕ → ℕ → ℕ → Bool) : Set (Cycle (Fin s) (Fin n)) :=
  {c | X (enc c.1) (enc c.2.1) (enc c.2.2) = true}

@[simp]
theorem mem_tblSet {X : ℕ → ℕ → ℕ → Bool} {a b c : IntegralAtom (Fin s) (Fin n)} :
    (a, b, c) ∈ tblSet s n X ↔ X (enc a) (enc b) (enc c) = true := Iff.rfl

open Classical in
/-- The Boolean table of a cycle set. -/
noncomputable def setTbl (T : Set (Cycle (Fin s) (Fin n))) (a b c : ℕ) : Bool :=
  decide ((dec s n a, dec s n b, dec s n c) ∈ T)

@[simp]
theorem setTbl_eq_true {T : Set (Cycle (Fin s) (Fin n))} {a b c : ℕ} :
    setTbl T a b c = true ↔ (dec s n a, dec s n b, dec s n c) ∈ T := by
  simp [setTbl]

@[simp]
theorem tblSet_setTbl (T : Set (Cycle (Fin s) (Fin n))) : tblSet s n (setTbl T) = T := by
  ext ⟨a, b, c⟩
  simp

/-- Tables agreeing on all codes of atoms have the same cycle set. -/
theorem tblSet_congr {X Y : ℕ → ℕ → ℕ → Bool}
    (h : ∀ a < numAtoms s n, ∀ b < numAtoms s n, ∀ c < numAtoms s n, X a b c = Y a b c) :
    tblSet s n X = tblSet s n Y := by
  ext ⟨a, b, c⟩
  simp [h _ (enc_lt a) _ (enc_lt b) _ (enc_lt c)]

/-- The identity and Peircean conditions on a table. -/
structure PeirceTbl (s n : ℕ) (X : ℕ → ℕ → ℕ → Bool) : Prop where
  id_right : ∀ a < numAtoms s n, ∀ c < numAtoms s n, X a 0 c = decide (c = a)
  id_left : ∀ a < numAtoms s n, ∀ c < numAtoms s n, X 0 a c = decide (c = a)
  id_out : ∀ a < numAtoms s n, ∀ b < numAtoms s n, X a b 0 = decide (b = cvN s a)
  left : ∀ a < numAtoms s n, ∀ b < numAtoms s n, ∀ c < numAtoms s n, X (cvN s a) c b = X a b c
  right : ∀ a < numAtoms s n, ∀ b < numAtoms s n, ∀ c < numAtoms s n, X c (cvN s b) a = X a b c

theorem numAtoms_pos (s n : ℕ) : 0 < numAtoms s n := by
  simp only [numAtoms]; omega

theorem cvN_zero (s : ℕ) : cvN s 0 = 0 := cvN_of_le (Nat.zero_le s)

theorem PeirceTbl.conv {X : ℕ → ℕ → ℕ → Bool} (h : PeirceTbl s n X) {a b c : ℕ}
    (ha : a < numAtoms s n) (hb : b < numAtoms s n) (hc : c < numAtoms s n) :
    X (cvN s b) (cvN s a) (cvN s c) = X a b c := by
  rw [h.left b hb (cvN s c) (cvN_lt hc) (cvN s a) (cvN_lt ha),
    h.right (cvN s a) (cvN_lt ha) c hc b hb, h.left a ha b hb c hc]

/-- `∃ q, X a b q ∧ X c d q`: the products `a ; b` and `c ; d` meet. -/
def dotB (k : ℕ) (X : ℕ → ℕ → ℕ → Bool) (a b c d : ℕ) : Bool :=
  (List.range k).any fun q => X a b q && X c d q

theorem dotB_iff {k : ℕ} {X : ℕ → ℕ → ℕ → Bool} {a b c d : ℕ} :
    dotB k X a b c d = true ↔ ∃ q < k, X a b q = true ∧ X c d q = true := by
  simp [dotB]

theorem dotB_congr {k : ℕ} {X Y : ℕ → ℕ → ℕ → Bool} {a b c d : ℕ}
    (h1 : ∀ q < k, X a b q = Y a b q) (h2 : ∀ q < k, X c d q = Y c d q) :
    dotB k X a b c d = dotB k Y a b c d := by
  rw [Bool.eq_iff_iff, dotB_iff, dotB_iff]
  constructor <;> rintro ⟨q, hq, h⟩ <;> exact ⟨q, hq, by simpa [h1 q hq, h2 q hq] using h⟩

theorem dotB_symm {k : ℕ} {X : ℕ → ℕ → ℕ → Bool} (a b c d : ℕ) :
    dotB k X a b c d = dotB k X c d a b := by
  rw [Bool.eq_iff_iff, dotB_iff, dotB_iff]
  constructor <;> rintro ⟨q, hq, h1, h2⟩ <;> exact ⟨q, hq, h2, h1⟩

/-- The associativity condition for the quadruple `(r, u, t, p)`: `p ≤ r ; (u ; t)` iff
`p ≤ (r ; u) ; t`. -/
def quadB (s k : ℕ) (X : ℕ → ℕ → ℕ → Bool) (r u t p : ℕ) : Bool :=
  dotB k X (cvN s r) p u t == dotB k X r u p (cvN s t)

theorem quadB_congr {X Y : ℕ → ℕ → ℕ → Bool}
    (h : ∀ a < numAtoms s n, ∀ b < numAtoms s n, ∀ c < numAtoms s n, X a b c = Y a b c)
    {r u t p : ℕ} (hr : r < numAtoms s n) (hu : u < numAtoms s n) (ht : t < numAtoms s n)
    (hp : p < numAtoms s n) :
    quadB s (numAtoms s n) X r u t p = quadB s (numAtoms s n) Y r u t p := by
  unfold quadB
  rw [dotB_congr (fun q hq => h _ (cvN_lt hr) _ hp _ hq) (fun q hq => h _ hu _ ht _ hq),
    dotB_congr (fun q hq => h _ hr _ hu _ hq) (fun q hq => h _ hp _ (cvN_lt ht) _ hq)]

section Lawful

variable {X : ℕ → ℕ → ℕ → Bool}

/-- A table satisfying the identity, Peircean and all associativity conditions gives a lawful
cycle set. -/
theorem isLawfulCycles_tblSet (h : PeirceTbl s n X)
    (hq : ∀ r < numAtoms s n, ∀ u < numAtoms s n, ∀ t < numAtoms s n, ∀ p < numAtoms s n,
      quadB s (numAtoms s n) X r u t p = true) :
    IsLawfulCycles (tblSet s n X) := by
  rw [isLawfulCycles_iff]
  refine ⟨fun r p => ?_, fun r u t hc => ?_, fun r q p u t h₁ h₂ => ?_⟩
  · rw [mem_tblSet, enc_one, h.id_right _ (enc_lt r) _ (enc_lt p)]
    simp
  · rw [mem_tblSet] at hc ⊢
    rw [enc_conv, h.left _ (enc_lt r) _ (enc_lt u) _ (enc_lt t)]
    exact hc
  · rw [mem_tblSet] at h₁ h₂
    have hquad := hq _ (enc_lt r) _ (enc_lt u) _ (enc_lt t) _ (enc_lt p)
    rw [quadB, beq_iff_eq] at hquad
    have hL : dotB (numAtoms s n) X (cvN s (enc r)) (enc p) (enc u) (enc t) = true :=
      dotB_iff.mpr ⟨enc q, enc_lt q,
        by rw [h.left _ (enc_lt r) _ (enc_lt q) _ (enc_lt p)]; exact h₁, h₂⟩
    rw [hquad, dotB_iff] at hL
    obtain ⟨q', hq', h3, h4⟩ := hL
    refine ⟨dec s n q', ?_, ?_⟩
    · rw [mem_tblSet, enc_dec hq', ← h.right _ hq' _ (enc_lt t) _ (enc_lt p)]
      exact h4
    · rw [mem_tblSet, enc_dec hq']
      exact h3

variable {T : Set (Cycle (Fin s) (Fin n))}

/-- The table of a lawful cycle set satisfies the identity and Peircean conditions. -/
theorem peirceTbl_setTbl (h : IsLawfulCycles T) : PeirceTbl s n (setTbl T) where
  id_right a ha c hc := by
    rw [Bool.eq_iff_iff, setTbl_eq_true, dec_zero, h.one_right_iff, decide_eq_true_iff]
    exact ⟨fun h' => by rw [← enc_dec hc, ← enc_dec ha, h'], fun h' => by rw [h']⟩
  id_left a ha c hc := by
    rw [Bool.eq_iff_iff, setTbl_eq_true, dec_zero, h.one_left_iff, decide_eq_true_iff]
    exact ⟨fun h' => by rw [← enc_dec hc, ← enc_dec ha, h'], fun h' => by rw [h']⟩
  id_out a ha b hb := by
    rw [Bool.eq_iff_iff, setTbl_eq_true, dec_zero, h.one_out_iff, decide_eq_true_iff,
      ← dec_cvN ha]
    exact ⟨fun h' => by rw [← enc_dec hb, ← enc_dec (cvN_lt ha), h'], fun h' => by rw [h']⟩
  left a ha b hb c hc := by
    rw [Bool.eq_iff_iff, setTbl_eq_true, setTbl_eq_true, dec_cvN ha, h.left_mem_iff]
  right a ha b hb c hc := by
    rw [Bool.eq_iff_iff, setTbl_eq_true, setTbl_eq_true, dec_cvN hb, h.right_mem_iff]

/-- The table of a lawful cycle set satisfies every associativity condition. -/
theorem quadB_setTbl (h : IsLawfulCycles T) {r u t p : ℕ} (hr : r < numAtoms s n)
    (_hu : u < numAtoms s n) (ht : t < numAtoms s n) (hp : p < numAtoms s n) :
    quadB s (numAtoms s n) (setTbl T) r u t p = true := by
  have hP := peirceTbl_setTbl h
  have := h.lawfulAtomStructure
  rw [quadB, beq_iff_eq, Bool.eq_iff_iff, dotB_iff, dotB_iff]
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    rw [hP.left _ hr _ hq _ hp, setTbl_eq_true] at h1
    rw [setTbl_eq_true] at h2
    obtain ⟨q', h3, h4⟩ := h.assoc h1 h2
    refine ⟨enc q', enc_lt q', ?_, ?_⟩
    · rw [setTbl_eq_true, dec_enc]; exact h4
    · rw [hP.right _ (enc_lt q') _ ht _ hp, setTbl_eq_true, dec_enc]; exact h3
  · rintro ⟨q, hq, h1, h2⟩
    rw [hP.right _ hq _ ht _ hp, setTbl_eq_true] at h2
    rw [setTbl_eq_true] at h1
    obtain ⟨q', h3, h4⟩ := (structOf T).assoc_symm (r := dec s n r) (s := dec s n u) h2 h1
    refine ⟨enc q', enc_lt q', ?_, ?_⟩
    · rw [hP.left _ hr _ (enc_lt q') _ hp, setTbl_eq_true, dec_enc]; exact h3
    · rw [setTbl_eq_true, dec_enc]; exact h4

end Lawful

section Symmetry

variable {X : ℕ → ℕ → ℕ → Bool}

/-- `dotB` is invariant under converse. -/
theorem PeirceTbl.dotB_conv (h : PeirceTbl s n X) {a b c d : ℕ} (ha : a < numAtoms s n)
    (hb : b < numAtoms s n) (hc : c < numAtoms s n) (hd : d < numAtoms s n) :
    dotB (numAtoms s n) X (cvN s b) (cvN s a) (cvN s d) (cvN s c) =
      dotB (numAtoms s n) X a b c d := by
  rw [Bool.eq_iff_iff, dotB_iff, dotB_iff]
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    refine ⟨cvN s q, cvN_lt hq, ?_, ?_⟩
    · rw [← h.conv ha hb (cvN_lt hq), cvN_cvN hq]; exact h1
    · rw [← h.conv hc hd (cvN_lt hq), cvN_cvN hq]; exact h2
  · rintro ⟨q, hq, h1, h2⟩
    exact ⟨cvN s q, cvN_lt hq, by rw [h.conv ha hb hq]; exact h1,
      by rw [h.conv hc hd hq]; exact h2⟩

theorem PeirceTbl.dotB_conv' (h : PeirceTbl s n X) {r u t p : ℕ} (hr : r < numAtoms s n)
    (hu : u < numAtoms s n) (ht : t < numAtoms s n) (hp : p < numAtoms s n) :
    dotB (numAtoms s n) X (cvN s u) (cvN s r) t (cvN s p) =
      dotB (numAtoms s n) X r u p (cvN s t) := by
  have := h.dotB_conv hr hu hp (cvN_lt ht)
  rwa [cvN_cvN ht] at this

/-- Rotation of a quadruple. -/
theorem PeirceTbl.quadB_rot (h : PeirceTbl s n X) {r u t p : ℕ} (hr : r < numAtoms s n)
    (hu : u < numAtoms s n) (ht : t < numAtoms s n) (hp : p < numAtoms s n) :
    quadB s (numAtoms s n) X u t (cvN s p) (cvN s r) = quadB s (numAtoms s n) X r u t p := by
  unfold quadB
  rw [h.dotB_conv' hr hu ht hp, cvN_cvN hp, dotB_symm u t]
  exact Bool.beq_comm

/-- Reflection of a quadruple. -/
theorem PeirceTbl.quadB_flip (h : PeirceTbl s n X) {r u t p : ℕ} (hr : r < numAtoms s n)
    (hu : u < numAtoms s n) (ht : t < numAtoms s n) (hp : p < numAtoms s n) :
    quadB s (numAtoms s n) X (cvN s t) (cvN s u) (cvN s r) (cvN s p) =
      quadB s (numAtoms s n) X r u t p := by
  unfold quadB
  have e2 : dotB (numAtoms s n) X (cvN s t) (cvN s u) (cvN s p) (cvN s (cvN s r)) =
      dotB (numAtoms s n) X (cvN s r) p u t := by
    rw [h.dotB_conv hu ht (cvN_lt hr) hp, dotB_symm]
  rw [e2, cvN_cvN ht, dotB_symm t, h.dotB_conv' hr hu ht hp]
  exact Bool.beq_comm

/-- Invariance of a table under a map `f` of codes with a right inverse `g`. -/
structure SigInv (k : ℕ) (X : ℕ → ℕ → ℕ → Bool) (f g : ℕ → ℕ) : Prop where
  lt : ∀ a < k, f a < k
  inv_lt : ∀ a < k, g a < k
  right_inv : ∀ a < k, f (g a) = a
  inv : ∀ a < k, ∀ b < k, ∀ c < k, X (f a) (f b) (f c) = X a b c

theorem SigInv.dotB_map {k : ℕ} {f g : ℕ → ℕ} (h : SigInv k X f g) {a b c d : ℕ} (ha : a < k)
    (hb : b < k) (hc : c < k) (hd : d < k) :
    dotB k X (f a) (f b) (f c) (f d) = dotB k X a b c d := by
  rw [Bool.eq_iff_iff, dotB_iff, dotB_iff]
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    refine ⟨g q, h.inv_lt q hq, ?_, ?_⟩
    · rw [← h.inv a ha b hb _ (h.inv_lt q hq), h.right_inv q hq]; exact h1
    · rw [← h.inv c hc d hd _ (h.inv_lt q hq), h.right_inv q hq]; exact h2
  · rintro ⟨q, hq, h1, h2⟩
    exact ⟨f q, h.lt q hq, by rw [h.inv a ha b hb q hq]; exact h1,
      by rw [h.inv c hc d hd q hq]; exact h2⟩

/-- Invariance of the associativity condition under a symmetry commuting with converse. -/
theorem SigInv.quadB_map {f g : ℕ → ℕ} (h : SigInv (numAtoms s n) X f g)
    (hcv : ∀ a < numAtoms s n, f (cvN s a) = cvN s (f a)) {r u t p : ℕ}
    (hr : r < numAtoms s n) (hu : u < numAtoms s n) (ht : t < numAtoms s n)
    (hp : p < numAtoms s n) :
    quadB s (numAtoms s n) X (f r) (f u) (f t) (f p) = quadB s (numAtoms s n) X r u t p := by
  unfold quadB
  rw [← hcv r hr, ← hcv t ht, h.dotB_map (cvN_lt hr) hp hu ht, h.dotB_map hr hu hp (cvN_lt ht)]

theorem PeirceTbl.exists_id_left (h : PeirceTbl s n X) {p : ℕ} (hp : p < numAtoms s n)
    (F : ℕ → Prop) : (∃ q < numAtoms s n, X 0 p q = true ∧ F q) ↔ F p := by
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    rw [h.id_left p hp q hq, decide_eq_true_iff] at h1
    rwa [h1] at h2
  · exact fun hF => ⟨p, hp, by rw [h.id_left p hp p hp]; simp, hF⟩

theorem PeirceTbl.exists_id_left' (h : PeirceTbl s n X) {p : ℕ} (hp : p < numAtoms s n)
    (F : ℕ → Prop) : (∃ q < numAtoms s n, F q ∧ X 0 p q = true) ↔ F p := by
  rw [← h.exists_id_left hp F]
  exact exists_congr fun q => and_congr_right fun _ => and_comm

theorem PeirceTbl.exists_id_right (h : PeirceTbl s n X) {a : ℕ} (ha : a < numAtoms s n)
    (F : ℕ → Prop) : (∃ q < numAtoms s n, X a 0 q = true ∧ F q) ↔ F a := by
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    rw [h.id_right a ha q hq, decide_eq_true_iff] at h1
    rwa [h1] at h2
  · exact fun hF => ⟨a, ha, by rw [h.id_right a ha a ha]; simp, hF⟩

theorem PeirceTbl.exists_id_right' (h : PeirceTbl s n X) {a : ℕ} (ha : a < numAtoms s n)
    (F : ℕ → Prop) : (∃ q < numAtoms s n, F q ∧ X a 0 q = true) ↔ F a := by
  rw [← h.exists_id_right ha F]
  exact exists_congr fun q => and_congr_right fun _ => and_comm

/-- Quadruples containing the identity satisfy the associativity condition. -/
theorem PeirceTbl.quadB_of_zero (h : PeirceTbl s n X) {r u t p : ℕ} (hr : r < numAtoms s n)
    (hu : u < numAtoms s n) (ht : t < numAtoms s n) (hp : p < numAtoms s n)
    (h0 : r = 0 ∨ u = 0 ∨ t = 0 ∨ p = 0) : quadB s (numAtoms s n) X r u t p = true := by
  rw [quadB, beq_iff_eq, Bool.eq_iff_iff, dotB_iff, dotB_iff]
  rcases h0 with rfl | rfl | rfl | rfl
  · rw [cvN_zero, h.exists_id_left hp (fun q => X u t q = true),
      h.exists_id_left hu (fun q => X p (cvN s t) q = true), h.right u hu t ht p hp]
  · rw [h.exists_id_left' ht (fun q => X (cvN s r) p q = true),
      h.exists_id_right hr (fun q => X p (cvN s t) q = true), h.left r hr t ht p hp,
      h.right r hr t ht p hp]
  · rw [cvN_zero, h.exists_id_right' hu (fun q => X (cvN s r) p q = true),
      h.exists_id_right' hp (fun q => X r u q = true), h.left r hr u hu p hp]
  · have e : X u t (cvN s r) = X r u (cvN s t) := by
      rw [← h.left r hr u hu _ (cvN_lt ht), ← h.right _ (cvN_lt hr) _ (cvN_lt ht) u hu,
        cvN_cvN ht]
    rw [h.exists_id_right (cvN_lt hr) (fun q => X u t q = true),
      h.exists_id_left' (cvN_lt ht) (fun q => X r u q = true), e]

end Symmetry

end RACert
