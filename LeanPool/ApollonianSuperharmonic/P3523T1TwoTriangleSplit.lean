/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Linarith

public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Combination

-- [TABLET NODE: P3523T1TwoTriangleSplit]

/-!
# P3523T1TwoTriangleSplit

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TwoTriangleSplit

private theorem hu_nonneg (u : Real) (hu : 0 < u ∧ u < 1) : 0 ≤ u := by
  classical
  exact hu.1.le

private theorem h1u_nonneg (u : Real) (hu : 0 < u ∧ u < 1) : 0 ≤ 1-u := by
  classical
  linarith [hu.2]

private noncomputable def d (A : Real × Real) (B : Real × Real) (C : Real × Real) : Real := (B.1
    - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)

private theorem hd (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : (d A B C) ≠ 0 := by
  classical
  let d : Real := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)
  change (d ≠ 0)
  dsimp [d, P3381T1TriangleDeterminant] at hn ⊢
  simpa [Prod.fst_sub, Prod.snd_sub] using hn

private theorem distinctAB (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : A ≠ B := by
  classical
  let d : Real := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)
  have hd : d ≠ 0 := hd A B C hn
  intro h
  subst B
  apply hd
  dsimp [d]
  ring

private theorem distinctAC (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : A ≠ C := by
  classical
  let d : Real := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)
  have hd : d ≠ 0 := hd A B C hn
  intro h
  subst C
  apply hd
  dsimp [d]
  ring

private theorem distinctBC (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : B ≠ C := by
  classical
  let d : Real := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)
  have hd : d ≠ 0 := hd A B C hn
  intro h
  subst C
  apply hd
  dsimp [d]
  ring

private theorem hull3 (P Q R x : Real × Real) (hPQ : P ≠ Q) (hPR : P ≠ R)
      (hQR : Q ≠ R) :
      x ∈ convexHull Real ({P, Q, R} : Set (Real × Real)) ↔
        ∃ a b c : Real, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
          a • P + b • Q + c • R = x := by
  classical
  rw [show ({P, Q, R} : Set (Real × Real)) =
      ↑({P, Q, R} : Finset (Real × Real)) by ext y; simp]
  rw [Finset.mem_convexHull']
  constructor
  · rintro ⟨w, hpos, hsum, hvec⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, hPQ, hPR,
        or_self, not_false_eq_true, Finset.sum_insert, hQR, Finset.sum_singleton]
        at hpos hsum hvec
    rcases hpos with ⟨hP, hQ, hR⟩
    refine ⟨w P, w Q, w R, ?_, ?_, ?_, ?_, ?_⟩
    · exact hP
    · exact hQ
    · exact hR
    · nlinarith [hsum]
    · simpa [add_assoc] using hvec
  · rintro ⟨a, b, c, ha, hb, hc, hsum, hvec⟩
    refine ⟨(fun y => if P = y then a else if Q = y then b else c),
      ?_, ?_, ?_⟩
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hy | hy | hy
      · subst y; simpa using ha
      · subst y; simpa [hPQ] using hb
      · subst y; simpa [hPR, hQR] using hc
    · simp [Finset.sum_insert, hPQ, hPR, hQR]
      nlinarith [hsum]
    · simp [Finset.sum_insert, hPQ, hPR, hQR]
      simpa [add_assoc] using hvec

private theorem affineUnique (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) (a b c a' b' c' : Real)
      (hs : a + b + c = 1) (hs' : a' + b' + c' = 1)
      (he : a • A + b • B + c • C = a' • A + b' • B + c' • C) :
      a = a' ∧ b = b' ∧ c = c' := by
  classical
  let d : Real := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)
  have hd : d ≠ 0 := hd A B C hn
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at he1 he2
  have hsum : (b - b') + (c - c') = -(a - a') := by linarith
  have hsumdiff : (a - a') + (b - b') + (c - c') = 0 := by linarith
  have hx : (b - b') * (B.1 - A.1) + (c - c') * (C.1 - A.1) = 0 := by
    linear_combination he1 - A.1 * hsumdiff
  have hy : (b - b') * (B.2 - A.2) + (c - c') * (C.2 - A.2) = 0 := by
    linear_combination he2 - A.2 * hsumdiff
  have hb0 : d * (b - b') = 0 := by
    dsimp [d]
    linear_combination hx * (C.2 - A.2) - hy * (C.1 - A.1)
  have hc0 : d * (c - c') = 0 := by
    dsimp [d]
    linear_combination hy * (B.1 - A.1) - hx * (B.2 - A.2)
  have hb : b = b' := by
    have := (mul_eq_zero.mp hb0).resolve_left hd
    linarith
  have hc : c = c' := by
    have := (mul_eq_zero.mp hc0).resolve_left hd
    linarith
  have ha : a = a' := by linarith
  exact ⟨ha, hb, hc⟩

private theorem hDneA (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hu : 0 <
    u ∧ u < 1) (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : (1 - u) • A + u • B ≠ A := by
  classical
  have affineUnique (a b c a' b' c' : Real)
      (hs : a + b + c = 1) (hs' : a' + b' + c' = 1)
      (he : a • A + b • B + c • C = a' • A + b' • B + c' • C) :
      a = a' ∧ b = b' ∧ c = c' := affineUnique A B C hn a b c a' b' c' hs hs' he
  intro h
  have huniq := affineUnique (1-u) u (0:Real) 1 0 0 (by ring) (by norm_num)
    (by simpa using h)
  have : u = 0 := by linarith [huniq.2.1]
  exact (ne_of_gt hu.1) this

private theorem hDneB (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hu : 0 <
    u ∧ u < 1) (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : (1 - u) • A + u • B ≠ B := by
  classical
  have affineUnique (a b c a' b' c' : Real)
      (hs : a + b + c = 1) (hs' : a' + b' + c' = 1)
      (he : a • A + b • B + c • C = a' • A + b' • B + c' • C) :
      a = a' ∧ b = b' ∧ c = c' := affineUnique A B C hn a b c a' b' c' hs hs' he
  intro h
  have huniq := affineUnique (1-u) u (0:Real) 0 1 0 (by ring) (by norm_num)
    (by simpa using h)
  have : 1 - u = 0 := by linarith [huniq.1]
  linarith [hu.2]

private theorem hDneC (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : (1 - u) • A + u • B ≠ C := by
  classical
  have affineUnique (a b c a' b' c' : Real)
      (hs : a + b + c = 1) (hs' : a' + b' + c' = 1)
      (he : a • A + b • B + c • C = a' • A + b' • B + c' • C) :
      a = a' ∧ b = b' ∧ c = c' := affineUnique A B C hn a b c a' b' c' hs hs' he
  intro h
  have huniq := affineUnique (1-u) u (0:Real) (0:Real) (0:Real) (1:Real)
    (by ring) (by norm_num) (by simpa using h)
  linarith [huniq.2.1]

private theorem coeffSplit (u : Real) (hu : 0 < u ∧ u < 1) (a b c : Real) (ha : 0 ≤ a) (hb : 0 ≤
    b) (hc : 0 ≤ c)
      (hsum : a + b + c = 1) :
      (∃ l m t : Real, 0 ≤ l ∧ 0 ≤ m ∧ 0 ≤ t ∧ l + m + t = 1 ∧
        a = l + (1-u)*m ∧ b = u*m ∧ c = t) ∨
      (∃ m r t : Real, 0 ≤ m ∧ 0 ≤ r ∧ 0 ≤ t ∧ m + r + t = 1 ∧
        a = (1-u)*m ∧ b = u*m+r ∧ c = t) := by
  classical
  have hu0 : u ≠ 0 := ne_of_gt hu.1
  have hv : 0 < 1-u := by linarith [hu.2]
  have hv0 : 1-u ≠ 0 := ne_of_gt hv
  rcases le_total ((1-u)*b) (u*a) with h | h
  · left
    refine ⟨a-(1-u)*b/u, b/u, c, ?_, div_nonneg hb hu.1.le, hc, ?_, ?_, ?_, rfl⟩
    · apply sub_nonneg.mpr
      exact (div_le_iff₀ hu.1).2 (by nlinarith)
    · field_simp
      nlinarith [hsum]
    · field_simp
      ring
    · field_simp
  · right
    refine ⟨a/(1-u), b-u*a/(1-u), c, div_nonneg ha hv.le, ?_, hc, ?_, ?_, ?_, rfl⟩
    · apply sub_nonneg.mpr
      exact (div_le_iff₀ hv).2 (by nlinarith)
    · field_simp
      nlinarith [hsum]
    · field_simp
    · field_simp
      ring

private noncomputable def D (A : Real × Real) (B : Real × Real) (u : Real) : Real × Real := (1-u)
    • A + u • B

private theorem hcoverage (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hu :
    0 < u ∧ u < 1) (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : convexHull Real ({A, B,
    C} : Set (Real × Real)) =
      convexHull Real ({A, (D A B u), C} : Set (Real × Real)) ∪
        convexHull Real ({(D A B u), B, C} : Set (Real × Real)) := by
  classical
  have hu_nonneg : 0 ≤ u := hu_nonneg u hu
  have h1u_nonneg : 0 ≤ 1-u := h1u_nonneg u hu
  have distinctAB : A ≠ B := distinctAB A B C hn
  have distinctAC : A ≠ C := distinctAC A B C hn
  have distinctBC : B ≠ C := distinctBC A B C hn
  have hull3 (P Q R x : Real × Real) (hPQ : P ≠ Q) (hPR : P ≠ R)
      (hQR : Q ≠ R) :
      x ∈ convexHull Real ({P, Q, R} : Set (Real × Real)) ↔
        ∃ a b c : Real, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
          a • P + b • Q + c • R = x := hull3 P Q R x hPQ hPR hQR
  have hDneA : (1 - u) • A + u • B ≠ A := hDneA A B C u hu hn
  have hDneB : (1 - u) • A + u • B ≠ B := hDneB A B C u hu hn
  have hDneC : (1 - u) • A + u • B ≠ C := hDneC A B C u hn
  have hleftHull (x : Real × Real) := hull3 A ((1 - u) • A + u • B) C x
    (fun h => hDneA h.symm) distinctAC hDneC
  have hrightHull (x : Real × Real) := hull3 ((1 - u) • A + u • B) B C
    x hDneB hDneC distinctBC
  have holdHull (x : Real × Real) := hull3 A B C x distinctAB distinctAC distinctBC
  have coeffSplit (a b c : Real) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
      (hsum : a + b + c = 1) :
      (∃ l m t : Real, 0 ≤ l ∧ 0 ≤ m ∧ 0 ≤ t ∧ l + m + t = 1 ∧
        a = l + (1-u)*m ∧ b = u*m ∧ c = t) ∨
      (∃ m r t : Real, 0 ≤ m ∧ 0 ≤ r ∧ 0 ≤ t ∧ m + r + t = 1 ∧
        a = (1-u)*m ∧ b = u*m+r ∧ c = t) := coeffSplit u hu a b c ha hb hc hsum
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({A, B, C} : Set (Real × Real)) =
      convexHull Real ({A, D, C} : Set (Real × Real)) ∪
        convexHull Real ({D, B, C} : Set (Real × Real)))
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨a, b, c, ha, hb, hc, hsum, hvec⟩ := (holdHull x).1 hx
    rcases coeffSplit a b c ha hb hc hsum with hleft | hright
    · obtain ⟨l, m, t, hl, hm, ht, hst, hla, hmb, htc⟩ := hleft
      have hla' : a = l + m*(1-u) := by rw [hla]; ring
      have hmb' : b = m*u := by rw [hmb]; ring
      left
      apply (hleftHull x).2
      refine ⟨l, m, t, hl, hm, ht, hst, ?_⟩
      calc
        l • A + m • D + t • C = a • A + b • B + c • C := by
          simp only [D, smul_add, smul_smul]
          subst a
          subst b
          subst c
          module
        _ = x := hvec
    · obtain ⟨m, r, t, hm, hr, ht, hst, ham, hbr, htc⟩ := hright
      have ham' : a = m*(1-u) := by rw [ham]; ring
      have hbr' : b = m*u+r := by rw [hbr]; ring
      right
      apply (hrightHull x).2
      refine ⟨m, r, t, hm, hr, ht, hst, ?_⟩
      calc
        m • D + r • B + t • C = a • A + b • B + c • C := by
          simp only [D, smul_add, smul_smul]
          subst a
          subst b
          subst c
          module
        _ = x := hvec
  · rintro (hx | hx)
    · obtain ⟨l, m, t, hl, hm, ht, hst, hvec⟩ := (hleftHull x).1 hx
      apply (holdHull x).2
      refine ⟨l+(1-u)*m, u*m, t, ?_, ?_, ht, ?_, ?_⟩
      · exact add_nonneg hl (mul_nonneg h1u_nonneg hm)
      · exact mul_nonneg hu_nonneg hm
      · nlinarith [hst]
      · calc
          (l+(1-u)*m) • A + (u*m) • B + t • C = l • A + m • D + t • C := by
            simp only [D, smul_add, smul_smul]
            module
          _ = x := hvec
    · obtain ⟨m, r, t, hm, hr, ht, hst, hvec⟩ := (hrightHull x).1 hx
      apply (holdHull x).2
      refine ⟨(1-u)*m, u*m+r, t, ?_, ?_, ht, ?_, ?_⟩
      · exact mul_nonneg h1u_nonneg hm
      · exact add_nonneg (mul_nonneg hu_nonneg hm) hr
      · nlinarith [hst]
      · calc
          ((1-u)*m) • A + (u*m+r) • B + t • C = m • D + r • B + t • C := by
            simp only [D, smul_add, smul_smul]
            module
          _ = x := hvec

private theorem hdiag (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hu : 0 <
    u ∧ u < 1) (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) :
      convexHull Real ({A, (D A B u), C} : Set (Real × Real)) ∩
        convexHull Real ({(D A B u), B, C} : Set (Real × Real)) = segment Real (D A B u) C := by
  classical
  have hu_nonneg : 0 ≤ u := hu_nonneg u hu
  have h1u_nonneg : 0 ≤ 1-u := h1u_nonneg u hu
  have distinctAC : A ≠ C := distinctAC A B C hn
  have distinctBC : B ≠ C := distinctBC A B C hn
  have hull3 (P Q R x : Real × Real) (hPQ : P ≠ Q) (hPR : P ≠ R)
      (hQR : Q ≠ R) :
      x ∈ convexHull Real ({P, Q, R} : Set (Real × Real)) ↔
        ∃ a b c : Real, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
          a • P + b • Q + c • R = x := hull3 P Q R x hPQ hPR hQR
  have affineUnique (a b c a' b' c' : Real)
      (hs : a + b + c = 1) (hs' : a' + b' + c' = 1)
      (he : a • A + b • B + c • C = a' • A + b' • B + c' • C) :
      a = a' ∧ b = b' ∧ c = c' := affineUnique A B C hn a b c a' b' c' hs hs' he
  have hDneA : (1 - u) • A + u • B ≠ A := hDneA A B C u hu hn
  have hDneB : (1 - u) • A + u • B ≠ B := hDneB A B C u hu hn
  have hDneC : (1 - u) • A + u • B ≠ C := hDneC A B C u hn
  have hleftHull (x : Real × Real) := hull3 A ((1 - u) • A + u • B) C x
    (fun h => hDneA h.symm) distinctAC hDneC
  have hrightHull (x : Real × Real) := hull3 ((1 - u) • A + u • B) B C
    x hDneB hDneC distinctBC
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({A, D, C} : Set (Real × Real)) ∩
        convexHull Real ({D, B, C} : Set (Real × Real)) = segment Real D C)
  ext x
  constructor
  · rintro ⟨hxL, hxR⟩
    obtain ⟨l, m, t, hl, hm, ht, hsumL, hvecL⟩ := (hleftHull x).1 hxL
    obtain ⟨m', r, t', hm', hr, ht', hsumR, hvecR⟩ := (hrightHull x).1 hxR
    have hLold : (l+(1-u)*m) • A + (u*m) • B + t • C = x := by
      calc
        (l+(1-u)*m) • A + (u*m) • B + t • C = l • A + m • D + t • C := by
          simp only [D, smul_add, smul_smul]
          module
        _ = x := hvecL
    have hRold : ((1-u)*m') • A + (u*m'+r) • B + t' • C = x := by
      calc
        ((1-u)*m') • A + (u*m'+r) • B + t' • C = m' • D + r • B + t' • C := by
          simp only [D, smul_add, smul_smul]
          module
        _ = x := hvecR
    have huniq := affineUnique (l+(1-u)*m) (u*m) t ((1-u)*m') (u*m'+r) t'
      (by nlinarith [hsumL]) (by nlinarith [hsumR]) (hLold.trans hRold.symm)
    have hzero : u*l + (1-u)*r = 0 := by
      linear_combination u * huniq.1 - (1-u) * huniq.2.1
    have hl0 : l = 0 := by
      nlinarith [mul_nonneg hu_nonneg hl, mul_nonneg h1u_nonneg hr]
    have hr0 : r = 0 := by
      nlinarith [mul_nonneg hu_nonneg hl, mul_nonneg h1u_nonneg hr]
    have hmm : m = m' := by
      have hbEq := huniq.2.1
      rw [hr0] at hbEq
      nlinarith [hu.1]
    have hmt : m+t = 1 := by nlinarith [hsumL, hl0]
    refine ⟨m, t, hm, ht, hmt, ?_⟩
    calc
      m • D + t • C = ((1-u)*m) • A + (u*m) • B + t • C := by
        simp only [D, smul_add, smul_smul]
        module
      _ = x := by
        rw [← hLold, hl0]
        simp
  · rintro ⟨s, t, hs, ht, hst, hvec⟩
    constructor
    · apply (hleftHull x).2
      refine ⟨0, s, t, le_rfl, hs, ht, ?_, ?_⟩
      · simpa using hst
      · simpa only [zero_smul, zero_add, add_zero] using hvec
    · apply (hrightHull x).2
      refine ⟨s, 0, t, hs, le_rfl, ht, ?_, ?_⟩
      · simpa using hst
      · simpa only [zero_smul, zero_add, add_zero] using hvec

private theorem pairACsubL (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) :
    convexHull Real ({A, C} : Set (Real × Real)) ⊆
      convexHull Real ({A, (D A B u), C} : Set (Real × Real)) := by
  classical
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({A, C} : Set (Real × Real)) ⊆
      convexHull Real ({A, D, C} : Set (Real × Real)))
  apply convexHull_mono
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  rcases hz with hz | hz
  · subst z; simp
  · subst z; simp

private theorem pairBCsubR (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) :
    convexHull Real ({B, C} : Set (Real × Real)) ⊆
      convexHull Real ({(D A B u), B, C} : Set (Real × Real)) := by
  classical
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({B, C} : Set (Real × Real)) ⊆
      convexHull Real ({D, B, C} : Set (Real × Real)))
  apply convexHull_mono
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  rcases hz with hz | hz
  · subst z; simp
  · subst z; simp

private theorem hleftAC (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) :
      convexHull Real ({A, (D A B u), C} : Set (Real × Real)) ∩
        convexHull Real ({A, C} : Set (Real × Real)) =
      convexHull Real ({A, C} : Set (Real × Real)) := by
  classical
  let D : Real × Real := (1-u) • A + u • B
  have pairACsubL : convexHull Real ({A, C} : Set (Real × Real)) ⊆
      convexHull Real ({A, D, C} : Set (Real × Real)) := pairACsubL A B C u
  change (convexHull Real ({A, D, C} : Set (Real × Real)) ∩
        convexHull Real ({A, C} : Set (Real × Real)) =
      convexHull Real ({A, C} : Set (Real × Real)))
  ext z
  constructor
  · exact And.right
  · intro hz
    exact ⟨pairACsubL hz, hz⟩

private theorem hrightBC (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) :
      convexHull Real ({(D A B u), B, C} : Set (Real × Real)) ∩
        convexHull Real ({B, C} : Set (Real × Real)) =
      convexHull Real ({B, C} : Set (Real × Real)) := by
  classical
  let D : Real × Real := (1-u) • A + u • B
  have pairBCsubR : convexHull Real ({B, C} : Set (Real × Real)) ⊆
      convexHull Real ({D, B, C} : Set (Real × Real)) := pairBCsubR A B C u
  change (convexHull Real ({D, B, C} : Set (Real × Real)) ∩
        convexHull Real ({B, C} : Set (Real × Real)) =
      convexHull Real ({B, C} : Set (Real × Real)))
  ext z
  constructor
  · exact And.right
  · intro hz
    exact ⟨pairBCsubR hz, hz⟩

private theorem hrightAC (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hu : 0
    < u ∧ u < 1) (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) :
      convexHull Real ({(D A B u), B, C} : Set (Real × Real)) ∩
        convexHull Real ({A, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)) := by
  classical
  have hu_nonneg : 0 ≤ u := hu_nonneg u hu
  have distinctBC : B ≠ C := distinctBC A B C hn
  have hull3 (P Q R x : Real × Real) (hPQ : P ≠ Q) (hPR : P ≠ R)
      (hQR : Q ≠ R) :
      x ∈ convexHull Real ({P, Q, R} : Set (Real × Real)) ↔
        ∃ a b c : Real, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
          a • P + b • Q + c • R = x := hull3 P Q R x hPQ hPR hQR
  have affineUnique (a b c a' b' c' : Real)
      (hs : a + b + c = 1) (hs' : a' + b' + c' = 1)
      (he : a • A + b • B + c • C = a' • A + b' • B + c' • C) :
      a = a' ∧ b = b' ∧ c = c' := affineUnique A B C hn a b c a' b' c' hs hs' he
  have hDneB : (1 - u) • A + u • B ≠ B := hDneB A B C u hu hn
  have hDneC : (1 - u) • A + u • B ≠ C := hDneC A B C u hn
  have hrightHull (x : Real × Real) := hull3 ((1 - u) • A + u • B) B C
    x hDneB hDneC distinctBC
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({D, B, C} : Set (Real × Real)) ∩
        convexHull Real ({A, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)))
  ext x
  constructor
  · rintro ⟨hxR, hxAC⟩
    obtain ⟨m, r, t, hm, hr, ht, hsumR, hvecR⟩ := (hrightHull x).1 hxR
    rw [convexHull_pair] at hxAC
    obtain ⟨a, c, ha, hc, hsumAC, hvecAC⟩ := hxAC
    have hRold : ((1-u)*m) • A + (u*m+r) • B + t • C = x := by
      calc
        ((1-u)*m) • A + (u*m+r) • B + t • C = m • D + r • B + t • C := by
          simp only [D, smul_add, smul_smul]
          module
        _ = x := hvecR
    have hsumOld : (1-u)*m + (u*m+r) + t = 1 := by nlinarith [hsumR]
    have hpoint : ((1-u)*m) • A + (u*m+r) • B + t • C =
        a • A + (0:Real) • B + c • C := by
      calc
        ((1-u)*m) • A + (u*m+r) • B + t • C = x := hRold
        _ = a • A + (0:Real) • B + c • C := by simpa using hvecAC.symm
    have huniq := affineUnique ((1-u)*m) (u*m+r) t a 0 c hsumOld
      (by simpa using hsumAC) hpoint
    have hm0 : m = 0 := by
      nlinarith [huniq.2.1, mul_nonneg hu_nonneg hm]
    have hr0 : r = 0 := by nlinarith [huniq.2.1]
    have ht1 : t = 1 := by nlinarith [hsumR, hm0, hr0]
    have hxC : x = C := by
      rw [← hRold, hm0, hr0, ht1]
      simp
    simp [hxC]
  · intro hxC
    have hxEq : x = C := by simpa using hxC
    subst x
    constructor
    · exact subset_convexHull _ _ (by simp)
    · exact subset_convexHull _ _ (by simp)

private theorem hleftBC (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hu : 0
    < u ∧ u < 1) (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) :
      convexHull Real ({A, (D A B u), C} : Set (Real × Real)) ∩
        convexHull Real ({B, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)) := by
  classical
  have h1u_nonneg : 0 ≤ 1-u := h1u_nonneg u hu
  have distinctAC : A ≠ C := distinctAC A B C hn
  have hull3 (P Q R x : Real × Real) (hPQ : P ≠ Q) (hPR : P ≠ R)
      (hQR : Q ≠ R) :
      x ∈ convexHull Real ({P, Q, R} : Set (Real × Real)) ↔
        ∃ a b c : Real, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
          a • P + b • Q + c • R = x := hull3 P Q R x hPQ hPR hQR
  have affineUnique (a b c a' b' c' : Real)
      (hs : a + b + c = 1) (hs' : a' + b' + c' = 1)
      (he : a • A + b • B + c • C = a' • A + b' • B + c' • C) :
      a = a' ∧ b = b' ∧ c = c' := affineUnique A B C hn a b c a' b' c' hs hs' he
  have hDneA : (1 - u) • A + u • B ≠ A := hDneA A B C u hu hn
  have hDneC : (1 - u) • A + u • B ≠ C := hDneC A B C u hn
  have hleftHull (x : Real × Real) := hull3 A ((1 - u) • A + u • B) C x
    (fun h => hDneA h.symm) distinctAC hDneC
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({A, D, C} : Set (Real × Real)) ∩
        convexHull Real ({B, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)))
  ext x
  constructor
  · rintro ⟨hxL, hxBC⟩
    obtain ⟨l, m, t, hl, hm, ht, hsumL, hvecL⟩ := (hleftHull x).1 hxL
    rw [convexHull_pair] at hxBC
    obtain ⟨b, c, hb, hc, hsumBC, hvecBC⟩ := hxBC
    have hLold : (l+(1-u)*m) • A + (u*m) • B + t • C = x := by
      calc
        (l+(1-u)*m) • A + (u*m) • B + t • C = l • A + m • D + t • C := by
          simp only [D, smul_add, smul_smul]
          module
        _ = x := hvecL
    have hsumOld : l+(1-u)*m + u*m+t=1 := by nlinarith [hsumL]
    have hpoint : (l+(1-u)*m) • A + (u*m) • B + t • C =
        (0:Real) • A + b • B + c • C := by
      calc
        (l+(1-u)*m) • A + (u*m) • B + t • C = x := hLold
        _ = (0:Real) • A + b • B + c • C := by simpa using hvecBC.symm
    have huniq := affineUnique (l+(1-u)*m) (u*m) t 0 b c hsumOld
      (by simpa using hsumBC) hpoint
    have hm0 : m = 0 := by
      have hprod : 0 ≤ (1-u)*m := mul_nonneg h1u_nonneg hm
      nlinarith [huniq.1]
    have hl0 : l = 0 := by nlinarith [huniq.1, hm0]
    have ht1 : t = 1 := by nlinarith [hsumL, hl0, hm0]
    have hxC : x = C := by
      rw [← hLold, hl0, hm0, ht1]
      simp
    simp [hxC]
  · intro hxC
    have hxEq : x = C := by simpa using hxC
    subst x
    constructor
    · exact subset_convexHull _ _ (by simp)
    · exact subset_convexHull _ _ (by simp)

private theorem leftA (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) :
    convexHull Real ({A, (D A B u), C} : Set (Real × Real)) ∩
      convexHull Real ({A} : Set (Real × Real)) = convexHull Real ({A} : Set (Real × Real)) := by
  classical
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({A} : Set (Real × Real)) = convexHull Real ({A} : Set (Real × Real)))
  ext x
  constructor
  · exact And.right
  · intro hx
    have hxA : x = A := by simpa using hx
    subst x
    exact ⟨(subset_convexHull Real ({A,D,C} : Set (Real × Real))) (by simp), by simp⟩

private theorem rightA (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hu : 0 <
    u ∧ u < 1) (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : convexHull Real ({(D A B u),
    B, C} : Set (Real × Real)) ∩
      convexHull Real ({A} : Set (Real × Real)) = ∅ := by
  classical
  have distinctAC : A ≠ C := distinctAC A B C hn
  let D : Real × Real := (1-u) • A + u • B
  have hrightAC :
      convexHull Real ({D, B, C} : Set (Real × Real)) ∩
        convexHull Real ({A, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)) := hrightAC A B C u hu hn
  change (convexHull Real ({D, B, C} : Set (Real × Real)) ∩
      convexHull Real ({A} : Set (Real × Real)) = ∅)
  ext x
  constructor
  · rintro ⟨hxR, hxA⟩
    have hsub : convexHull Real ({A} : Set (Real × Real)) ⊆
        convexHull Real ({A, C} : Set (Real × Real)) := by
      apply convexHull_mono
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      simp
    have hC : x ∈ convexHull Real ({C} : Set (Real × Real)) := by
      have := hrightAC ▸ (show x ∈ convexHull Real ({D,B,C} : Set (Real × Real)) ∩
        convexHull Real ({A,C} : Set (Real × Real)) from ⟨hxR, hsub hxA⟩)
      exact this
    have hxEqC : x = C := by simpa using hC
    have hxEqA : x = A := by simpa using hxA
    exact False.elim (distinctAC (hxEqA.symm.trans hxEqC))
  · simp

private theorem leftB (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hu : 0 <
    u ∧ u < 1) (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : convexHull Real ({A, (D A B
    u), C} : Set (Real × Real)) ∩
      convexHull Real ({B} : Set (Real × Real)) = ∅ := by
  classical
  have distinctBC : B ≠ C := distinctBC A B C hn
  let D : Real × Real := (1-u) • A + u • B
  have hleftBC :
      convexHull Real ({A, D, C} : Set (Real × Real)) ∩
        convexHull Real ({B, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)) := hleftBC A B C u hu hn
  change (convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({B} : Set (Real × Real)) = ∅)
  ext x
  constructor
  · rintro ⟨hxL, hxB⟩
    have hsub : convexHull Real ({B} : Set (Real × Real)) ⊆
        convexHull Real ({B, C} : Set (Real × Real)) := by
      apply convexHull_mono
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      simp
    have hC : x ∈ convexHull Real ({C} : Set (Real × Real)) := by
      have := hleftBC ▸ (show x ∈ convexHull Real ({A,D,C} : Set (Real × Real)) ∩
        convexHull Real ({B,C} : Set (Real × Real)) from ⟨hxL, hsub hxB⟩)
      exact this
    have hxEqC : x = C := by simpa using hC
    have hxEqB : x = B := by simpa using hxB
    exact False.elim (distinctBC (hxEqB.symm.trans hxEqC))
  · simp

private theorem rightB (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) :
    convexHull Real ({(D A B u), B, C} : Set (Real × Real)) ∩
      convexHull Real ({B} : Set (Real × Real)) = convexHull Real ({B} : Set (Real × Real)) := by
  classical
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({D, B, C} : Set (Real × Real)) ∩
      convexHull Real ({B} : Set (Real × Real)) = convexHull Real ({B} : Set (Real × Real)))
  ext x
  constructor
  · exact And.right
  · intro hx
    have hxB : x = B := by simpa using hx
    subst x
    exact ⟨(subset_convexHull Real ({D,B,C} : Set (Real × Real))) (by simp), by simp⟩

private theorem leftC (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) :
    convexHull Real ({A, (D A B u), C} : Set (Real × Real)) ∩
      convexHull Real ({C} : Set (Real × Real)) = convexHull Real ({C} : Set (Real × Real)) := by
  classical
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({C} : Set (Real × Real)) = convexHull Real ({C} : Set (Real × Real)))
  ext x
  constructor
  · exact And.right
  · intro hx
    have hxC : x = C := by simpa using hx
    subst x
    exact ⟨(subset_convexHull Real ({A,D,C} : Set (Real × Real))) (by simp), by simp⟩

private theorem rightC (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) :
    convexHull Real ({(D A B u), B, C} : Set (Real × Real)) ∩
      convexHull Real ({C} : Set (Real × Real)) = convexHull Real ({C} : Set (Real × Real)) := by
  classical
  let D : Real × Real := (1-u) • A + u • B
  change (convexHull Real ({D, B, C} : Set (Real × Real)) ∩
      convexHull Real ({C} : Set (Real × Real)) = convexHull Real ({C} : Set (Real × Real)))
  ext x
  constructor
  · exact And.right
  · intro hx
    have hxC : x = C := by simpa using hx
    subst x
    exact ⟨(subset_convexHull Real ({D,B,C} : Set (Real × Real))) (by simp), by simp⟩

private theorem hACinterAC (A : Real × Real) (C : Real × Real) : ({A,C} : Set (Real × Real)) ∩
    {A,C} = {A,C} := by
  classical
  exact Set.inter_self _

private abbrev hBCinterBC := ApollonianSuperharmonic.TwoTriangleSplit.hACinterAC

private theorem hACinterBC (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : ({A,C} : Set (Real × Real)) ∩ {B,C} = {C} := by
  classical
  have distinctAB : A ≠ B := distinctAB A B C hn
  have distinctAC : A ≠ C := distinctAC A B C hn
  have distinctBC : B ≠ C := distinctBC A B C hn
  ext z
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzA | hzC, hzB | hzC'⟩
    · exact False.elim (distinctAB (hzA.symm.trans hzB))
    · exact False.elim (distinctAC (hzA.symm.trans hzC'))
    · exact False.elim (distinctBC (hzB.symm.trans hzC))
    · exact hzC
  · intro hz
    subst z
    exact ⟨Or.inr rfl, Or.inr rfl⟩

private theorem hBCinterAC (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : ({B,C} : Set (Real × Real)) ∩ {A,C} = {C} := by
  classical
  have distinctAB : A ≠ B := distinctAB A B C hn
  have distinctAC : A ≠ C := distinctAC A B C hn
  have distinctBC : B ≠ C := distinctBC A B C hn
  ext z
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzB | hzC, hzA | hzC'⟩
    · exact False.elim (distinctAB (hzA.symm.trans hzB))
    · exact False.elim (distinctBC (hzB.symm.trans hzC'))
    · exact False.elim (distinctAC (hzA.symm.trans hzC))
    · exact hzC
  · intro hz
    subst z
    exact ⟨Or.inr rfl, Or.inr rfl⟩

private theorem hAinterAC (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : ({A} : Set (Real × Real)) ∩ {A,C} = {A} := by
  classical
  have distinctAC : A ≠ C := distinctAC A B C hn
  ext z
  simp [distinctAC]

private theorem hAinterBC (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : ({A} : Set (Real × Real)) ∩ {B,C} = ∅ := by
  classical
  have distinctAB : A ≠ B := distinctAB A B C hn
  have distinctAC : A ≠ C := distinctAC A B C hn
  ext z
  simp [distinctAB, distinctAC]

private theorem hBinterAC (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : ({B} : Set (Real × Real)) ∩ {A,C} = ∅ := by
  classical
  have distinctAB : A ≠ B := distinctAB A B C hn
  have distinctBC : B ≠ C := distinctBC A B C hn
  ext z
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_insert_iff,
    Set.mem_empty_iff_false]
  constructor
  · rintro ⟨rfl, hzA | hzC⟩
    · exact False.elim (distinctAB hzA.symm)
    · exact False.elim (distinctBC hzC)
  · intro h
    exact False.elim h

private theorem hBinterBC (A : Real × Real) (B : Real × Real) (C : Real × Real) (hn :
    P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : ({B} : Set (Real × Real)) ∩ {B,C} = {B} := by
  classical
  have distinctBC : B ≠ C := distinctBC A B C hn
  ext z
  simp [distinctBC]

private theorem hCinterAC (A : Real × Real) (C : Real × Real) : ({C} : Set (Real × Real)) ∩ {A,C}
    = {C} := by
  classical
  ext z
  simp []

private abbrev hCinterBC := ApollonianSuperharmonic.TwoTriangleSplit.hCinterAC

private theorem hfaces (A : Real × Real) (B : Real × Real) (C : Real × Real) (u : Real) (hu : 0 <
    u ∧ u < 1) (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) : ∀ J : Set (Real × Real), J ⊆
    {A, B, C} →
      ¬(A ∈ J ∧ B ∈ J) →
      convexHull Real ({A, (D A B u), C} : Set (Real × Real)) ∩ convexHull Real J =
        convexHull Real (J ∩ {A, C}) ∧
      convexHull Real ({(D A B u), B, C} : Set (Real × Real)) ∩ convexHull Real J =
        convexHull Real (J ∩ {B, C}) := by
  classical
  let D : Real × Real := (1-u) • A + u • B
  have hleftAC :
      convexHull Real ({A, D, C} : Set (Real × Real)) ∩
        convexHull Real ({A, C} : Set (Real × Real)) =
      convexHull Real ({A, C} : Set (Real × Real)) := hleftAC A B C u
  have hrightBC :
      convexHull Real ({D, B, C} : Set (Real × Real)) ∩
        convexHull Real ({B, C} : Set (Real × Real)) =
      convexHull Real ({B, C} : Set (Real × Real)) := hrightBC A B C u
  have hrightAC :
      convexHull Real ({D, B, C} : Set (Real × Real)) ∩
        convexHull Real ({A, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)) := hrightAC A B C u hu hn
  have hleftBC :
      convexHull Real ({A, D, C} : Set (Real × Real)) ∩
        convexHull Real ({B, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)) := hleftBC A B C u hu hn
  have leftA : convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({A} : Set (Real × Real)) = convexHull Real ({A} : Set (Real × Real)) :=
          leftA A B C u
  have rightA : convexHull Real ({D, B, C} : Set (Real × Real)) ∩
      convexHull Real ({A} : Set (Real × Real)) = ∅ := rightA A B C u hu hn
  have leftB : convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({B} : Set (Real × Real)) = ∅ := leftB A B C u hu hn
  have rightB : convexHull Real ({D, B, C} : Set (Real × Real)) ∩
      convexHull Real ({B} : Set (Real × Real)) = convexHull Real ({B} : Set (Real × Real)) :=
          rightB A B C u
  have leftC : convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({C} : Set (Real × Real)) = convexHull Real ({C} : Set (Real × Real)) :=
          leftC A B C u
  have rightC : convexHull Real ({D, B, C} : Set (Real × Real)) ∩
      convexHull Real ({C} : Set (Real × Real)) = convexHull Real ({C} : Set (Real × Real)) :=
          rightC A B C u
  have hACinterAC : ({A,C} : Set (Real × Real)) ∩ {A,C} = {A,C} := hACinterAC A C
  have hBCinterBC : ({B,C} : Set (Real × Real)) ∩ {B,C} = {B,C} := hBCinterBC B C
  have hACinterBC : ({A,C} : Set (Real × Real)) ∩ {B,C} = {C} := hACinterBC A B C hn
  have hBCinterAC : ({B,C} : Set (Real × Real)) ∩ {A,C} = {C} := hBCinterAC A B C hn
  have hAinterAC : ({A} : Set (Real × Real)) ∩ {A,C} = {A} := hAinterAC A B C hn
  have hAinterBC : ({A} : Set (Real × Real)) ∩ {B,C} = ∅ := hAinterBC A B C hn
  have hBinterAC : ({B} : Set (Real × Real)) ∩ {A,C} = ∅ := hBinterAC A B C hn
  have hBinterBC : ({B} : Set (Real × Real)) ∩ {B,C} = {B} := hBinterBC A B C hn
  have hCinterAC : ({C} : Set (Real × Real)) ∩ {A,C} = {C} := hCinterAC A C
  have hCinterBC : ({C} : Set (Real × Real)) ∩ {B,C} = {C} := hCinterBC B C
  change (∀ J : Set (Real × Real), J ⊆ {A, B, C} →
      ¬(A ∈ J ∧ B ∈ J) →
      convexHull Real ({A, D, C} : Set (Real × Real)) ∩ convexHull Real J =
        convexHull Real (J ∩ {A, C}) ∧
      convexHull Real ({D, B, C} : Set (Real × Real)) ∩ convexHull Real J =
        convexHull Real (J ∩ {B, C}))
  intro J hJ hnot
  by_cases hA : A ∈ J
  · by_cases hB : B ∈ J
    · exact False.elim (hnot ⟨hA, hB⟩)
    · by_cases hC : C ∈ J
      · have hJAC : J = ({A, C} : Set (Real × Real)) := by
          ext z
          constructor
          · intro hz
            have hz' := hJ hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz' ⊢
            rcases hz' with hzA | hzB | hzC
            · exact Or.inl hzA
            · subst z; exact False.elim (hB hz)
            · exact Or.inr hzC
          · intro hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with hzA | hzC
            · subst z; exact hA
            · subst z; exact hC
        rw [hJAC]
        constructor
        · rw [hACinterAC]
          exact hleftAC
        · rw [hACinterBC]
          exact hrightAC
      · have hJA : J = ({A} : Set (Real × Real)) := by
          ext z
          constructor
          · intro hz
            have hz' := hJ hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz' ⊢
            rcases hz' with hzA | hzB | hzC
            · exact hzA
            · subst z; exact False.elim (hB hz)
            · subst z; exact False.elim (hC hz)
          · intro hz
            simp only [Set.mem_singleton_iff] at hz
            subst z; exact hA
        rw [hJA]
        constructor
        · rw [hAinterAC]
          exact leftA
        · rw [hAinterBC]
          simpa only [convexHull_empty] using rightA
  · by_cases hB : B ∈ J
    · by_cases hC : C ∈ J
      · have hJBC : J = ({B, C} : Set (Real × Real)) := by
          ext z
          constructor
          · intro hz
            have hz' := hJ hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz' ⊢
            rcases hz' with hzA | hzB | hzC
            · subst z; exact False.elim (hA hz)
            · exact Or.inl hzB
            · exact Or.inr hzC
          · intro hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with hzB | hzC
            · subst z; exact hB
            · subst z; exact hC
        rw [hJBC]
        constructor
        · rw [hBCinterAC]
          exact hleftBC
        · rw [hBCinterBC]
          exact hrightBC
      · have hJB : J = ({B} : Set (Real × Real)) := by
          ext z
          constructor
          · intro hz
            have hz' := hJ hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz' ⊢
            rcases hz' with hzA | hzB | hzC
            · subst z; exact False.elim (hA hz)
            · exact hzB
            · subst z; exact False.elim (hC hz)
          · intro hz
            simp only [Set.mem_singleton_iff] at hz
            subst z; exact hB
        rw [hJB]
        constructor
        · rw [hBinterAC]
          simpa only [convexHull_empty] using leftB
        · rw [hBinterBC]
          exact rightB
    · by_cases hC : C ∈ J
      · have hJC : J = ({C} : Set (Real × Real)) := by
          ext z
          constructor
          · intro hz
            have hz' := hJ hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz' ⊢
            rcases hz' with hzA | hzB | hzC
            · subst z; exact False.elim (hA hz)
            · subst z; exact False.elim (hB hz)
            · exact hzC
          · intro hz
            simp only [Set.mem_singleton_iff] at hz
            subst z; exact hC
        rw [hJC]
        constructor
        · rw [hCinterAC]
          exact leftC
        · rw [hCinterBC]
          exact rightC
      · have hJ0 : J = ∅ := by
          ext z
          constructor
          · intro hz
            have hz' := hJ hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
            rcases hz' with hzA | hzB | hzC
            · subst z; exact False.elim (hA hz)
            · subst z; exact False.elim (hB hz)
            · subst z; exact False.elim (hC hz)
          · simp
        rw [hJ0]
        simp

end TwoTriangleSplit

theorem P3523T1TwoTriangleSplit (A B C : Real × Real) (u : Real)
    (hu : 0 < u ∧ u < 1)
    (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) :
    let D := (1 - u) • A + u • B
    convexHull Real ({A, B, C} : Set (Real × Real)) =
      convexHull Real ({A, D, C} : Set (Real × Real)) ∪
      convexHull Real ({D, B, C} : Set (Real × Real)) ∧
    convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({D, B, C} : Set (Real × Real)) = segment Real D C ∧
    (∀ J : Set (Real × Real), J ⊆ {A, B, C} → ¬ (A ∈ J ∧ B ∈ J) →
      convexHull Real ({A, D, C} : Set (Real × Real)) ∩ convexHull Real J =
        convexHull Real (J ∩ {A, C}) ∧
      convexHull Real ({D, B, C} : Set (Real × Real)) ∩ convexHull Real J =
        convexHull Real (J ∩ {B, C})) := by
-- BODY
  classical
  have hu_nonneg : 0 ≤ u := TwoTriangleSplit.hu_nonneg u hu
  have h1u_nonneg : 0 ≤ 1-u := TwoTriangleSplit.h1u_nonneg u hu
  let d : Real := (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2)
  have hd : d ≠ 0 := TwoTriangleSplit.hd A B C hn
  have distinctAB : A ≠ B := TwoTriangleSplit.distinctAB A B C hn
  have distinctAC : A ≠ C := TwoTriangleSplit.distinctAC A B C hn
  have distinctBC : B ≠ C := TwoTriangleSplit.distinctBC A B C hn
  have hull3 (P Q R x : Real × Real) (hPQ : P ≠ Q) (hPR : P ≠ R)
      (hQR : Q ≠ R) :
      x ∈ convexHull Real ({P, Q, R} : Set (Real × Real)) ↔
        ∃ a b c : Real, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
          a • P + b • Q + c • R = x := TwoTriangleSplit.hull3 P Q R x hPQ hPR hQR
  have affineUnique (a b c a' b' c' : Real)
      (hs : a + b + c = 1) (hs' : a' + b' + c' = 1)
      (he : a • A + b • B + c • C = a' • A + b' • B + c' • C) :
      a = a' ∧ b = b' ∧ c = c' := TwoTriangleSplit.affineUnique A B C hn a b c a' b' c' hs hs' he
  have hDneA : (1 - u) • A + u • B ≠ A := TwoTriangleSplit.hDneA A B C u hu hn
  have hDneB : (1 - u) • A + u • B ≠ B := TwoTriangleSplit.hDneB A B C u hu hn
  have hDneC : (1 - u) • A + u • B ≠ C := TwoTriangleSplit.hDneC A B C u hn
  have hleftHull (x : Real × Real) := hull3 A ((1 - u) • A + u • B) C x
    (fun h => hDneA h.symm) distinctAC hDneC
  have hrightHull (x : Real × Real) := hull3 ((1 - u) • A + u • B) B C
    x hDneB hDneC distinctBC
  have holdHull (x : Real × Real) := hull3 A B C x distinctAB distinctAC distinctBC
  have coeffSplit (a b c : Real) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
      (hsum : a + b + c = 1) :
      (∃ l m t : Real, 0 ≤ l ∧ 0 ≤ m ∧ 0 ≤ t ∧ l + m + t = 1 ∧
        a = l + (1-u)*m ∧ b = u*m ∧ c = t) ∨
      (∃ m r t : Real, 0 ≤ m ∧ 0 ≤ r ∧ 0 ≤ t ∧ m + r + t = 1 ∧
        a = (1-u)*m ∧ b = u*m+r ∧ c = t) := TwoTriangleSplit.coeffSplit u hu a b c ha hb hc hsum
  let D : Real × Real := (1-u) • A + u • B
  have hcoverage : convexHull Real ({A, B, C} : Set (Real × Real)) =
      convexHull Real ({A, D, C} : Set (Real × Real)) ∪
        convexHull Real ({D, B, C} : Set (Real × Real)) := TwoTriangleSplit.hcoverage A B C u hu hn
  change (convexHull Real ({A, B, C} : Set (Real × Real)) =
      convexHull Real ({A, D, C} : Set (Real × Real)) ∪
        convexHull Real ({D, B, C} : Set (Real × Real))) ∧ _ ∧ _
  have hdiag :
      convexHull Real ({A, D, C} : Set (Real × Real)) ∩
        convexHull Real ({D, B, C} : Set (Real × Real)) = segment Real D C :=
            TwoTriangleSplit.hdiag A B C u hu hn
  have pairACsubL : convexHull Real ({A, C} : Set (Real × Real)) ⊆
      convexHull Real ({A, D, C} : Set (Real × Real)) := TwoTriangleSplit.pairACsubL A B C u
  have pairBCsubR : convexHull Real ({B, C} : Set (Real × Real)) ⊆
      convexHull Real ({D, B, C} : Set (Real × Real)) := TwoTriangleSplit.pairBCsubR A B C u
  have hleftAC :
      convexHull Real ({A, D, C} : Set (Real × Real)) ∩
        convexHull Real ({A, C} : Set (Real × Real)) =
      convexHull Real ({A, C} : Set (Real × Real)) := TwoTriangleSplit.hleftAC A B C u
  have hrightBC :
      convexHull Real ({D, B, C} : Set (Real × Real)) ∩
        convexHull Real ({B, C} : Set (Real × Real)) =
      convexHull Real ({B, C} : Set (Real × Real)) := TwoTriangleSplit.hrightBC A B C u
  have hrightAC :
      convexHull Real ({D, B, C} : Set (Real × Real)) ∩
        convexHull Real ({A, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)) := TwoTriangleSplit.hrightAC A B C u hu hn
  have hleftBC :
      convexHull Real ({A, D, C} : Set (Real × Real)) ∩
        convexHull Real ({B, C} : Set (Real × Real)) =
      convexHull Real ({C} : Set (Real × Real)) := TwoTriangleSplit.hleftBC A B C u hu hn
  have leftA : convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({A} : Set (Real × Real)) = convexHull Real ({A} : Set (Real × Real)) :=
          TwoTriangleSplit.leftA A B C u
  have rightA : convexHull Real ({D, B, C} : Set (Real × Real)) ∩
      convexHull Real ({A} : Set (Real × Real)) = ∅ := TwoTriangleSplit.rightA A B C u hu hn
  have leftB : convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({B} : Set (Real × Real)) = ∅ := TwoTriangleSplit.leftB A B C u hu hn
  have rightB : convexHull Real ({D, B, C} : Set (Real × Real)) ∩
      convexHull Real ({B} : Set (Real × Real)) = convexHull Real ({B} : Set (Real × Real)) :=
          TwoTriangleSplit.rightB A B C u
  have leftC : convexHull Real ({A, D, C} : Set (Real × Real)) ∩
      convexHull Real ({C} : Set (Real × Real)) = convexHull Real ({C} : Set (Real × Real)) :=
          TwoTriangleSplit.leftC A B C u
  have rightC : convexHull Real ({D, B, C} : Set (Real × Real)) ∩
      convexHull Real ({C} : Set (Real × Real)) = convexHull Real ({C} : Set (Real × Real)) :=
          TwoTriangleSplit.rightC A B C u
  have hACinterAC : ({A,C} : Set (Real × Real)) ∩ {A,C} = {A,C} := TwoTriangleSplit.hACinterAC A C
  have hBCinterBC : ({B,C} : Set (Real × Real)) ∩ {B,C} = {B,C} := TwoTriangleSplit.hBCinterBC B C
  have hACinterBC : ({A,C} : Set (Real × Real)) ∩ {B,C} = {C} := TwoTriangleSplit.hACinterBC A B
      C hn
  have hBCinterAC : ({B,C} : Set (Real × Real)) ∩ {A,C} = {C} := TwoTriangleSplit.hBCinterAC A B
      C hn
  have hAinterAC : ({A} : Set (Real × Real)) ∩ {A,C} = {A} := TwoTriangleSplit.hAinterAC A B C hn
  have hAinterBC : ({A} : Set (Real × Real)) ∩ {B,C} = ∅ := TwoTriangleSplit.hAinterBC A B C hn
  have hBinterAC : ({B} : Set (Real × Real)) ∩ {A,C} = ∅ := TwoTriangleSplit.hBinterAC A B C hn
  have hBinterBC : ({B} : Set (Real × Real)) ∩ {B,C} = {B} := TwoTriangleSplit.hBinterBC A B C hn
  have hCinterAC : ({C} : Set (Real × Real)) ∩ {A,C} = {C} := TwoTriangleSplit.hCinterAC A C
  have hCinterBC : ({C} : Set (Real × Real)) ∩ {B,C} = {C} := TwoTriangleSplit.hCinterBC B C
  have hfaces : ∀ J : Set (Real × Real), J ⊆ {A, B, C} →
      ¬(A ∈ J ∧ B ∈ J) →
      convexHull Real ({A, D, C} : Set (Real × Real)) ∩ convexHull Real J =
        convexHull Real (J ∩ {A, C}) ∧
      convexHull Real ({D, B, C} : Set (Real × Real)) ∩ convexHull Real J =
        convexHull Real (J ∩ {B, C}) := TwoTriangleSplit.hfaces A B C u hu hn
  exact ⟨hcoverage, hdiag, hfaces⟩

end ApollonianSuperharmonic

end
