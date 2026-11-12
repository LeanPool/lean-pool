/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3523T1OrderedInsertion

-- [TABLET NODE: P3523T1TargetBoundary]

/-!
# P3523T1TargetBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TargetBoundaryProof

private theorem htarget_edge :
    ∀ (r : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K), ∀ (i : Fin (r + (3 : ℕ))), t.target i ≠
        t.target (i + (1 : Fin (r + (3 : ℕ)))) := by
  classical
  intro r q X K t i h
  have hi : i = i + 1 := t.target_injective h
  have hv := congrArg Fin.val hi
  change i.val = (i.val + 1) % (r + 3) at hv
  by_cases hlt : i.val + 1 < r + 3
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = r + 3 := by omega
    rw [heq, Nat.mod_self] at hv
    have hi_lt := i.isLt
    omega

private theorem haffine_injective :
    ∀ (A : ℝ × ℝ), ∀ (B : ℝ × ℝ), A ≠ B → Function.Injective fun (u : ℝ) => ((1 : ℝ) - u) • A + u
        • B := by
  classical
  intro A B hAB u v h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change (1 - u) * A.1 + u * B.1 = (1 - v) * A.1 + v * B.1 at h1
  change (1 - u) * A.2 + u * B.2 = (1 - v) * A.2 + v * B.2 at h2
  have hprod1 : (u - v) * (B.1 - A.1) = 0 := by nlinarith
  have hprod2 : (u - v) * (B.2 - A.2) = 0 := by nlinarith
  by_cases hx : A.1 = B.1
  · have hy : B.2 - A.2 ≠ 0 := by
      intro he
      apply hAB
      exact Prod.ext hx (sub_eq_zero.mp he).symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod2).resolve_right hy)
  · have hy : B.1 - A.1 ≠ 0 := by
      intro he
      exact hx (sub_eq_zero.mp he).symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod1).resolve_right hy)

private theorem hQinj :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let Q := P3523T1InterpolatedTarget s t
    (∀ (j : Fin (n + 3)), Q j ∈ segment Real (t.target (s.edge j)) (t.target (s.edge j + 1))) →
        ((∀ (i : Fin (r + 3)), Function.Injective (fun u : Real => (1 - u) • t.target i + u •
        t.target (i + 1))) → ((∀ (j : Fin (n + 3)), Q j ≠ t.target (s.edge j + 1)) →
        (Function.Injective Q))) := by
  classical
  intro r n q p s X K t Q hparam_mem haffine_inj hparam_start i j hij
  have heqseg : Q i ∈ segment Real (t.target (s.edge i))
      (t.target (s.edge i + 1)) ∩
    segment Real (t.target (s.edge j)) (t.target (s.edge j + 1)) :=
    ⟨hparam_mem i, hij ▸ hparam_mem j⟩
  by_cases hed : s.edge i = s.edge j
  · have hparam : s.parameter i = s.parameter j := by
      apply haffine_inj (s.edge j)
      simpa [Q, P3523T1InterpolatedTarget, hed] using hij
    have hp : p.vertex i = p.vertex j := by
      rw [s.vertex_formula i, s.vertex_formula j, hed, hparam]
    exact p.injective hp
  · rw [t.target_edge_intersection _ _ hed] at heqseg
    rcases heqseg with ⟨hleft, hright⟩
    have hi_end : Q i ≠ t.target (s.edge i + 1) := hparam_start i
    have hj_end : Q j ≠ t.target (s.edge j + 1) := hparam_start j
    rcases hleft with hleft | hleft <;> rcases hright with hright | hright
    · have htargets : t.target (s.edge i) = t.target (s.edge j) := by
        exact hleft.symm.trans hright
      have : s.edge i = s.edge j := t.target_injective htargets
      exact (hed this).elim
    · exact (hj_end (hij.symm.trans hright)).elim
    · exact (hi_end hleft).elim
    · exact (hi_end hleft).elim

private theorem hfine_step :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let Q := P3523T1InterpolatedTarget s t
    let src (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • q.vertex e + u • q.vertex (e + 1)
    let tgt (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • t.target e + u • t.target (e + 1)
    ∀ (j : Fin (n + (3 : ℕ))), ∃ (b : ℝ), s.parameter j ≤ b ∧ b ≤ (1 : ℝ) ∧ p.vertex (j + (1 :
        Fin (n + (3 : ℕ)))) = src (s.edge j) b ∧ Q (j + (1 : Fin (n + (3 : ℕ)))) = tgt (s.edge j)
        b := by
  classical
  intro r n q p s X K t Q src tgt j
  rcases s.successor j with hs | hs
  · refine ⟨s.parameter (j + 1), ?_, ?_, ?_, ?_⟩
    · exact hs.2.le
    · exact (s.parameter_lt_one _).le
    · rw [s.vertex_formula (j + 1), hs.1]
    · simp [Q, tgt, P3523T1InterpolatedTarget, hs.1]
  · refine ⟨1, (s.parameter_lt_one j).le, le_rfl, ?_, ?_⟩
    · rw [s.vertex_formula (j + 1), hs.1, hs.2]
      simp [src]
    · simp [Q, tgt, P3523T1InterpolatedTarget, hs.1, hs.2]

private theorem hmix :
    ∀ (A : ℝ × ℝ), ∀ (B : ℝ × ℝ), ∀ (a : ℝ), ∀ (b : ℝ), ∀ (θ : ℝ), ((1 : ℝ) - θ) • (((1 : ℝ) - a)
        • A + a • B) + θ • (((1 : ℝ) - b) • A + b • B) = ((1 : ℝ) - (a + θ * (b - a))) • A + (a +
        θ * (b - a)) • B := by
  classical
  intro A B a b θ
  apply Prod.ext
  · change (1 - θ) * ((1 - a) * A.1 + a * B.1) +
      θ * ((1 - b) * A.1 + b * B.1) =
      (1 - (a + θ * (b - a))) * A.1 + (a + θ * (b - a)) * B.1
    ring
  · change (1 - θ) * ((1 - a) * A.2 + a * B.2) +
      θ * ((1 - b) * A.2 + b * B.2) =
      (1 - (a + θ * (b - a))) * A.2 + (a + θ * (b - a)) * B.2
    ring

private theorem hcoarse_inj_src :
    ∀ (r : Nat), ∀ (q : P3381T1PolygonBoundary r), (∀ (A : Real × Real), ∀ (B : Real × Real),
        (A ≠ B) → (Function.Injective (fun u : Real => (1 - u) • A + u • B))) → (
    let src (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • q.vertex e + u • q.vertex (e + 1)
    ∀ (e : Fin (r + (3 : ℕ))), Function.Injective (src e)) := by
  classical
  intro r q haffine_injective src e u v huv
  exact haffine_injective (q.vertex e) (q.vertex (e + 1))
    (by
      intro h
      have hi := q.injective h
      have hv := congrArg Fin.val hi
      change e.val = (e.val + 1) % (r + 3) at hv
      by_cases hlt : e.val + 1 < r + 3
      · rw [Nat.mod_eq_of_lt hlt] at hv
        omega
      · have heq : e.val + 1 = r + 3 := by omega
        rw [heq, Nat.mod_self] at hv
        omega) huv

private theorem hy_j :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p),
    let src (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • q.vertex e + u • q.vertex (e + 1)
    (∀ (A : Real × Real), ∀ (B : Real × Real), ∀ (a : Real), ∀ (b : Real), ∀ (θ : Real), (1 - θ)
        • ((1 - a) • A + a • B) + θ • ((1 - b) • A + b • B) = (1 - (a + θ * (b - a))) • A + (a +
        θ * (b - a)) • B) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))), ∀ (bi : ℝ), ∀
            (bj : ℝ), (p.vertex (j + (1 : Fin (n + (3 : ℕ)))) = src (s.edge j) bj) → (∀ (θ : ℝ),
            ∀ (φ : ℝ), (φ ∈ Set.Icc (0 : ℝ) (1 : ℝ)) → (
    let ci := s.parameter i + θ * (bi - s.parameter i)
    let cj := s.parameter j + φ * (bj - s.parameter j)
    (p.vertex j = src (s.edge j) (s.parameter j)) → ((s.edge i = s.edge j) → (
    let y := src (s.edge i) ci
    (ci = cj) → (y ∈ segment Real (p.vertex j) (p.vertex (j + 1)))))))) := by
  classical
  intro r n q p s src hmix i j bi bj hpj θ φ hφ ci cj hpj0 he y hparam_eq
  rw [segment_eq_image]
  refine ⟨φ, hφ, ?_⟩
  dsimp [y]
  rw [hpj0, hpj]
  have hm : (1 - φ) • src (s.edge j) (s.parameter j) +
        φ • src (s.edge j) bj = src (s.edge j) cj := by
    simpa [src, cj] using hmix (q.vertex (s.edge j))
      (q.vertex (s.edge j + 1)) (s.parameter j) bj φ
  calc (1 - φ) • src (s.edge j) (s.parameter j) +
        φ • src (s.edge j) bj = src (s.edge j) cj := hm
    _ = src (s.edge i) ci := by rw [← he, ← hparam_eq]

private theorem hx_i_endAt340 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let Q := P3523T1InterpolatedTarget s t
    let src (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • q.vertex e + u • q.vertex (e + 1)
    let tgt (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • t.target e + u • t.target (e + 1)
    (∀ (e : Fin (r + 3)), Function.Injective (src e)) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (x : ℝ ×
        ℝ), ∀ (bi : ℝ), (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) = src (s.edge i) bi) → ((Q (i +
        (1 : Fin (n + (3 : ℕ)))) = tgt (s.edge i) bi) → (∀ (θ : ℝ),
    let ci := s.parameter i + θ * (bi - s.parameter i)
    (Q i = tgt (s.edge i) (s.parameter i)) → ((p.vertex i = src (s.edge i) (s.parameter i)) → ((x
        = tgt (s.edge i) ci) → (
    let y := src (s.edge i) ci
    (y = p.vertex i ∨ y = p.vertex (i + (1 : Fin (n + (3 : ℕ))))) → (x = Q i ∨ x = Q (i +
        1)))))))) := by
  classical
  intro r n q p s X K t Q src tgt hcoarse_inj_src i x bi hpi hqi θ ci hqi0 hpi0 hx_i' y hi_end
  rcases hi_end with hi_end | hi_end
  · have hc : ci = s.parameter i := hcoarse_inj_src (s.edge i) (by
      calc src (s.edge i) ci = y := rfl
        _ = p.vertex i := hi_end
        _ = src (s.edge i) (s.parameter i) := hpi0)
    left
    calc x = tgt (s.edge i) ci := hx_i'
      _ = tgt (s.edge i) (s.parameter i) := congrArg _ hc
      _ = Q i := hqi0.symm
  · have hc : ci = bi := hcoarse_inj_src (s.edge i) (by
      calc src (s.edge i) ci = y := rfl
        _ = p.vertex (i + 1) := hi_end
        _ = src (s.edge i) bi := hpi)
    right
    calc x = tgt (s.edge i) ci := hx_i'
      _ = tgt (s.edge i) bi := congrArg _ hc
      _ = Q (i + 1) := hqi.symm

private theorem hx_j_endAt358 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let Q := P3523T1InterpolatedTarget s t
    let src (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • q.vertex e + u • q.vertex (e + 1)
    let tgt (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • t.target e + u • t.target (e + 1)
    (∀ (e : Fin (r + 3)), Function.Injective (src e)) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n
        + (3 : ℕ))), ∀ (x : ℝ × ℝ), ∀ (bi : ℝ), ∀ (bj : ℝ), (p.vertex (j + (1 : Fin (n + (3 :
        ℕ)))) = src (s.edge j) bj) → ((Q (j + (1 : Fin (n + (3 : ℕ)))) = tgt (s.edge j) bj) → (∀
            (θ : ℝ), ∀ (φ : ℝ),
    let ci := s.parameter i + θ * (bi - s.parameter i)
    let cj := s.parameter j + φ * (bj - s.parameter j)
    (Q j = tgt (s.edge j) (s.parameter j)) → ((p.vertex j = src (s.edge j) (s.parameter j)) → ((x
        = tgt (s.edge j) cj) → ((s.edge i = s.edge j) → (
    let y := src (s.edge i) ci
    (ci = cj) → ((y = p.vertex j ∨ y = p.vertex (j + (1 : Fin (n + (3 : ℕ))))) → (x = Q j ∨ x = Q
        (j + 1)))))))))) := by
  classical
  intro r n q p s X K t Q src tgt hcoarse_inj_src i j x bi bj hpj hqj θ φ ci cj hqj0 hpj0 hx_j'
      he y hparam_eq hj_end
  rcases hj_end with hj_end | hj_end
  · have hc : cj = s.parameter j := hcoarse_inj_src (s.edge i) (by
      calc src (s.edge i) cj = y := by simp [y, hparam_eq]
        _ = p.vertex j := hj_end
        _ = src (s.edge i) (s.parameter j) := by simpa [he] using hpj0)
    left
    calc x = tgt (s.edge j) cj := hx_j'
      _ = tgt (s.edge j) (s.parameter j) := congrArg _ hc
      _ = Q j := hqj0.symm
  · have hc : cj = bj := hcoarse_inj_src (s.edge i) (by
      calc src (s.edge i) cj = y := by simp [y, hparam_eq]
        _ = p.vertex (j + 1) := hj_end
        _ = src (s.edge i) bj := by simpa [he] using hpj)
    right
    calc x = tgt (s.edge j) cj := hx_j'
      _ = tgt (s.edge j) bj := congrArg _ hc
      _ = Q (j + 1) := hqj.symm

private theorem hx_i_endAt391 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let Q := P3523T1InterpolatedTarget s t
    let tgt (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • t.target e + u • t.target (e + 1)
    (∀ (e : Fin (r + 3)), Function.Injective (tgt e)) → (∀ (i : Fin (n + (3 : ℕ))), ∀ (x : ℝ ×
        ℝ), ∀ (bi : ℝ), (s.parameter i ≤ bi) → ((bi ≤ (1 : ℝ)) → ((Q (i + (1 : Fin (n + (3 :
        ℕ)))) = tgt (s.edge i) bi) → (∀ (θ : ℝ), (θ ∈ Set.Icc (0 : ℝ) (1 : ℝ)) → (
    let ci := s.parameter i + θ * (bi - s.parameter i)
    (Q i = tgt (s.edge i) (s.parameter i)) → ((x = tgt (s.edge i) ci) → ((x = t.target (s.edge i)
        ∨ x = t.target (s.edge i + (1 : Fin (r + (3 : ℕ))))) → (x = Q i ∨ x = Q (i + 1)))))))))
            := by
  classical
  intro r n q p s X K t Q tgt hcoarse_inj_tgt i x bi hai hbi hqi θ hθ ci hqi0 hx_i' hi_end
  rcases hi_end with hi_end | hi_end
  · have hc : ci = 0 := hcoarse_inj_tgt (s.edge i) (by
      calc tgt (s.edge i) ci = x := hx_i'.symm
        _ = t.target (s.edge i) := hi_end
        _ = tgt (s.edge i) 0 := by simp [tgt])
    have ha0 : s.parameter i = 0 := by
      dsimp [ci] at hc
      nlinarith [s.parameter_nonneg i, hθ.1, hθ.2, hai]
    left
    calc x = tgt (s.edge i) ci := hx_i'
      _ = tgt (s.edge i) (s.parameter i) := by rw [hc, ha0]
      _ = Q i := hqi0.symm
  · have hc : ci = 1 := hcoarse_inj_tgt (s.edge i) (by
      calc tgt (s.edge i) ci = x := hx_i'.symm
        _ = t.target (s.edge i + 1) := hi_end
        _ = tgt (s.edge i) 1 := by simp [tgt])
    have hb1 : bi = 1 := by
      dsimp [ci] at hc
      nlinarith [hai, hbi, hθ.1, hθ.2]
    right
    calc x = tgt (s.edge i) ci := hx_i'
      _ = tgt (s.edge i) bi := by rw [hc, hb1]
      _ = Q (i + 1) := hqi.symm

private theorem hx_j_endAt415 :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let Q := P3523T1InterpolatedTarget s t
    let tgt (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • t.target e + u • t.target (e + 1)
    (∀ (e : Fin (r + 3)), Function.Injective (tgt e)) → (∀ (j : Fin (n + (3 : ℕ))), ∀ (x : ℝ ×
        ℝ), ∀ (bj : ℝ), (s.parameter j ≤ bj) → ((bj ≤ (1 : ℝ)) → ((Q (j + (1 : Fin (n + (3 :
        ℕ)))) = tgt (s.edge j) bj) → (∀ (φ : ℝ), (φ ∈ Set.Icc (0 : ℝ) (1 : ℝ)) → (
    let cj := s.parameter j + φ * (bj - s.parameter j)
    (Q j = tgt (s.edge j) (s.parameter j)) → ((x = tgt (s.edge j) cj) → ((x = t.target (s.edge j)
        ∨ x = t.target (s.edge j + (1 : Fin (r + (3 : ℕ))))) → (x = Q j ∨ x = Q (j + 1)))))))))
            := by
  classical
  intro r n q p s X K t Q tgt hcoarse_inj_tgt j x bj haj hbj hqj φ hφ cj hqj0 hx_j' hj_end
  rcases hj_end with hj_end | hj_end
  · have hc : cj = 0 := hcoarse_inj_tgt (s.edge j) (by
      calc tgt (s.edge j) cj = x := hx_j'.symm
        _ = t.target (s.edge j) := hj_end
        _ = tgt (s.edge j) 0 := by simp [tgt])
    have ha0 : s.parameter j = 0 := by
      dsimp [cj] at hc
      nlinarith [s.parameter_nonneg j, hφ.1, hφ.2, haj]
    left
    calc x = tgt (s.edge j) cj := hx_j'
      _ = tgt (s.edge j) (s.parameter j) := by rw [hc, ha0]
      _ = Q j := hqj0.symm
  · have hc : cj = 1 := hcoarse_inj_tgt (s.edge j) (by
      calc tgt (s.edge j) cj = x := hx_j'.symm
        _ = t.target (s.edge j + 1) := hj_end
        _ = tgt (s.edge j) 1 := by simp [tgt])
    have hb1 : bj = 1 := by
      dsimp [cj] at hc
      nlinarith [haj, hbj, hφ.1, hφ.2]
    right
    calc x = tgt (s.edge j) cj := hx_j'
      _ = tgt (s.edge j) bj := by rw [hc, hb1]
      _ = Q (j + 1) := hqj.symm

private theorem hfine_subset :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let Q := P3523T1InterpolatedTarget s t
    let src (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • q.vertex e + u • q.vertex (e + 1)
    let tgt (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • t.target e + u • t.target (e + 1)
    (∀ (j : Fin (n + 3)), ∃ b : Real, s.parameter j ≤ b ∧ b ≤ 1 ∧ p.vertex (j + 1) = src (s.edge
        j) b ∧ Q (j + 1) = tgt (s.edge j) b) → ((∀ (e : Fin (r + 3)), ∀ (u : Real), (u ∈ Set.Icc
        (0 : Real) 1) → (tgt e u ∈ segment Real (t.target e) (t.target (e + 1)))) → ((⋃ j : Fin
        (n + 3), segment Real (Q j) (Q (j + 1))) ⊆ ⋃ e : Fin (r + 3), segment Real (t.target e)
        (t.target (e + 1)))) := by
  classical
  intro r n q p s X K t Q src tgt hfine_step htgt_mem x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hx⟩
  rcases hfine_step j with ⟨b, hab, hb, hp, hq⟩
  have hleft : Q j ∈ segment Real (t.target (s.edge j))
      (t.target (s.edge j + 1)) := by
    rw [show Q j = tgt (s.edge j) (s.parameter j) from rfl]
    exact htgt_mem _ _ ⟨s.parameter_nonneg j, (s.parameter_lt_one j).le⟩
  have hright : Q (j + 1) ∈ segment Real (t.target (s.edge j))
      (t.target (s.edge j + 1)) := by
    rw [hq]
    exact htgt_mem _ _ ⟨(s.parameter_nonneg j).trans hab, hb⟩
  refine Set.mem_iUnion.mpr ⟨s.edge j, ?_⟩
  exact (convex_segment _ _).segment_subset hleft hright hx

private theorem hcoarse_subset :
    ∀ (r : Nat), ∀ (n : Nat), ∀ (q : P3381T1PolygonBoundary r), ∀ (p : P3381T1PolygonBoundary
        n), ∀ (s : P3475T1BoundarySubdivision q p), ∀ (X : Set (Real × Real)), ∀ (K : Set (Real
        × Real)), ∀ (t : P3475T1TriangleTree q X K),
    let Q := P3523T1InterpolatedTarget s t
    let src (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • q.vertex e + u • q.vertex (e + 1)
    let tgt (e : Fin (r + 3)) (u : Real) :=
      (1 - u) • t.target e + u • t.target (e + 1)
    (∀ (j : Fin (n + 3)), ∃ b : Real, s.parameter j ≤ b ∧ b ≤ 1 ∧ p.vertex (j + 1) = src (s.edge
        j) b ∧ Q (j + 1) = tgt (s.edge j) b) → ((∀ (A : Real × Real), ∀ (B : Real × Real), ∀ (a :
            Real), ∀ (b : Real), ∀ (θ : Real), (1 - θ) • ((1 - a) • A + a • B) + θ • ((1 - b) • A
            + b
        • B) = (1 - (a + θ * (b - a))) • A + (a + θ * (b - a)) • B) → ((∀ {A : Real × Real}, ∀
            {B : Real × Real}, ∀ {x : Real × Real}, (x ∈ segment Real A B) → (∃ θ : Real, θ ∈
            Set.Icc
        (0 : Real) 1 ∧ x = (1 - θ) • A + θ • B)) → ((∀ (e : Fin (r + 3)), Function.Injective (src
        e)) → ((∀ (e : Fin (r + 3)), ∀ (u : Real), (u ∈ Set.Icc (0 : Real) 1) → (src e u ∈
        segment Real (q.vertex e) (q.vertex (e + 1)))) → ((⋃ e : Fin (r + 3), segment Real
        (t.target e) (t.target (e + 1))) ⊆ ⋃ j : Fin (n + 3), segment Real (Q j) (Q (j + 1)))))))
            := by
  classical
  intro r n q p s X K t Q src tgt hfine_step hmix hsegment_scalar hcoarse_inj_src hsrc_mem x hx
  rcases Set.mem_iUnion.mp hx with ⟨e, hx⟩
  rcases hsegment_scalar hx with ⟨v, hv, hxv⟩
  have hQstart (i : Fin (r + 3)) : Q (s.start i) = t.target i := by
    simp [Q, P3523T1InterpolatedTarget, s.edge_start, s.parameter_start]
  by_cases hvzero : v = 0
  · have hx0 : x = t.target e := by simpa [tgt, hvzero] using hxv
    refine Set.mem_iUnion.mpr ⟨s.start e, ?_⟩
    have hleft : t.target e ∈ segment Real (Q (s.start e))
        (Q (s.start e + 1)) := by
      rw [← hQstart e]
      exact left_mem_segment Real _ _
    exact hx0 ▸ hleft
  · by_cases hvone : v = 1
    · have hx1 : x = t.target (e + 1) := by simpa [tgt, hvone] using hxv
      refine Set.mem_iUnion.mpr ⟨s.start (e + 1), ?_⟩
      have hleft : t.target (e + 1) ∈ segment Real (Q (s.start (e + 1)))
          (Q (s.start (e + 1) + 1)) := by
        rw [← hQstart (e + 1)]
        exact left_mem_segment Real _ _
      exact hx1 ▸ hleft
    · have hvint : 0 < v ∧ v < 1 :=
        ⟨lt_of_le_of_ne hv.1 (Ne.symm hvzero), lt_of_le_of_ne hv.2 hvone⟩
      let y := src e v
      have hy_coarse : y ∈ ⋃ f : Fin (r + 3), segment Real (q.vertex f) (q.vertex (f + 1)) :=
        Set.mem_iUnion.mpr ⟨e, hsrc_mem e v hv⟩
      have hy_fine : y ∈ ⋃ j : Fin (n + 3), segment Real (p.vertex j) (p.vertex (j + 1)) := by
        simpa only [s.carrier_eq.symm] using hy_coarse
      rcases Set.mem_iUnion.mp hy_fine with ⟨j, hyseg⟩
      rcases hfine_step j with ⟨b, hab, hb, hp, hq⟩
      have hp0 : p.vertex j = src (s.edge j) (s.parameter j) := by
        simp [src, s.vertex_formula]
      have hp1 : p.vertex (j + 1) = src (s.edge j) b := hp
      have hsource_subset :
          segment Real (p.vertex j) (p.vertex (j + 1)) ⊆
            segment Real (q.vertex (s.edge j)) (q.vertex (s.edge j + 1)) := by
        apply (convex_segment _ _).segment_subset
        · rw [hp0]
          exact hsrc_mem _ _ ⟨s.parameter_nonneg j,
            (s.parameter_lt_one j).le⟩
        · rw [hp1]
          exact hsrc_mem _ _ ⟨(s.parameter_nonneg j).trans hab, hb⟩
      have hyboth : y ∈ segment Real (q.vertex e) (q.vertex (e + 1)) ∩
          segment Real (q.vertex (s.edge j)) (q.vertex (s.edge j + 1)) :=
        ⟨by simpa [y] using hsrc_mem e v hv, hsource_subset hyseg⟩
      have hedge_eq : e = s.edge j := by
        by_contra hne
        rw [q.edge_intersection e (s.edge j) hne] at hyboth
        rcases hyboth with ⟨hleft, _⟩
        rcases hleft with hleft | hleft
        · have hvzero' : v = 0 := hcoarse_inj_src e (by
            calc src e v = y := rfl
              _ = q.vertex e := hleft
              _ = src e 0 := by simp [src])
          exact hvzero (by linarith)
        · have hvone' : v = 1 := hcoarse_inj_src e (by
            calc src e v = y := rfl
              _ = q.vertex (e + 1) := hleft
              _ = src e 1 := by simp [src])
          exact hvone (by linarith)
      rcases hsegment_scalar hyseg with ⟨θ, hθ, hyθ⟩
      let c := s.parameter j + θ * (b - s.parameter j)
      have hp0' : p.vertex j = src e (s.parameter j) := by simpa [hedge_eq] using hp0
      have hp1' : p.vertex (j + 1) = src e b := by simpa [hedge_eq] using hp1
      have hy_eq : y = src e c := by
        rw [hyθ, hp0', hp1']
        simpa [c, src] using hmix (q.vertex e) (q.vertex (e + 1))
          (s.parameter j) b θ
      have hvc : v = c := hcoarse_inj_src e (by simpa [y] using hy_eq)
      have hxv' : x = tgt e v := by simpa [tgt] using hxv
      have htarget_mix : (1 - θ) • Q j + θ • Q (j + 1) = tgt e c := by
        calc (1 - θ) • Q j + θ • Q (j + 1) =
              (1 - θ) • tgt (s.edge j) (s.parameter j) +
                θ • tgt (s.edge j) b := by rw [show Q j =
                  tgt (s.edge j) (s.parameter j) from rfl, hq]
          _ = tgt e c := by
            simpa [c, tgt, hedge_eq] using hmix (t.target e)
              (t.target (e + 1)) (s.parameter j) b θ
      have hx_fine : x = (1 - θ) • Q j + θ • Q (j + 1) := by
        calc x = tgt e v := hxv'
          _ = tgt e c := congrArg (tgt e) hvc
          _ = (1 - θ) • Q j + θ • Q (j + 1) := htarget_mix.symm
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      rw [segment_eq_image]
      exact ⟨θ, hθ, hx_fine.symm⟩

end TargetBoundaryProof

theorem P3523T1TargetBoundary {r n : Nat}
    (q : P3381T1PolygonBoundary r) (p : P3381T1PolygonBoundary n)
    (s : P3475T1BoundarySubdivision q p)
    (X K : Set (Real × Real)) (t : P3475T1TriangleTree q X K) :
    let Q := P3523T1InterpolatedTarget s t
    Function.Injective Q ∧
    (∀ i j : Fin (n + 3), i ≠ j →
      segment Real (Q i) (Q (i + 1)) ∩ segment Real (Q j) (Q (j + 1)) =
        {x | (x = Q i ∨ x = Q (i + 1)) ∧
          (x = Q j ∨ x = Q (j + 1))}) ∧
    frontier K = ⋃ i, segment Real (Q i) (Q (i + 1)) := by
-- BODY
  classical
  dsimp only
  let Q := P3523T1InterpolatedTarget s t
  have htarget_edge (i : Fin (r + 3)) :
      t.target i ≠ t.target (i + 1) := TargetBoundaryProof.htarget_edge r q X K t i
  have hparam_mem (j : Fin (n + 3)) :
      Q j ∈ segment Real (t.target (s.edge j)) (t.target (s.edge j + 1)) := by
    rw [segment_eq_image]
    refine ⟨s.parameter j, ⟨s.parameter_nonneg j, (s.parameter_lt_one j).le⟩, ?_⟩
    simp [Q, P3523T1InterpolatedTarget]
  have haffine_injective (A B : Real × Real) (hAB : A ≠ B) :
      Function.Injective (fun u : Real => (1 - u) • A + u • B) :=
          TargetBoundaryProof.haffine_injective A B hAB
  have haffine_inj (i : Fin (r + 3)) :
      Function.Injective (fun u : Real =>
        (1 - u) • t.target i + u • t.target (i + 1)) := by
    intro u v huv
    exact haffine_injective (t.target i) (t.target (i + 1))
      (htarget_edge i) huv
  have hparam_start (j : Fin (n + 3)) :
      Q j ≠ t.target (s.edge j + 1) := by
    intro h
    have hu : s.parameter j = 1 := by
      apply haffine_injective (t.target (s.edge j))
        (t.target (s.edge j + 1)) (htarget_edge (s.edge j))
      simpa [Q, P3523T1InterpolatedTarget] using h
    linarith [s.parameter_lt_one j]
  have hQinj : Function.Injective Q := TargetBoundaryProof.hQinj r n q p s X K t hparam_mem
      haffine_inj hparam_start
  let src (e : Fin (r + 3)) (u : Real) :=
    (1 - u) • q.vertex e + u • q.vertex (e + 1)
  let tgt (e : Fin (r + 3)) (u : Real) :=
    (1 - u) • t.target e + u • t.target (e + 1)
  have hfine_step (j : Fin (n + 3)) :
      ∃ b : Real, s.parameter j ≤ b ∧ b ≤ 1 ∧
        p.vertex (j + 1) = src (s.edge j) b ∧
        Q (j + 1) = tgt (s.edge j) b := TargetBoundaryProof.hfine_step r n q p s X K t j
  have hmix (A B : Real × Real) (a b θ : Real) :
      (1 - θ) • ((1 - a) • A + a • B) +
        θ • ((1 - b) • A + b • B) =
      (1 - (a + θ * (b - a))) • A + (a + θ * (b - a)) • B := TargetBoundaryProof.hmix A B a b θ
  have hsegment_scalar {A B x : Real × Real}
      (hx : x ∈ segment Real A B) :
      ∃ θ : Real, θ ∈ Set.Icc (0 : Real) 1 ∧
        x = (1 - θ) • A + θ • B := by
    rw [segment_eq_image] at hx
    rcases hx with ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  have hcoarse_inj_src (e : Fin (r + 3)) :
      Function.Injective (src e) := TargetBoundaryProof.hcoarse_inj_src r q haffine_injective e
  have hcoarse_inj_tgt (e : Fin (r + 3)) :
      Function.Injective (tgt e) := haffine_inj e
  have hsrc_mem (e : Fin (r + 3)) (u : Real)
      (hu : u ∈ Set.Icc (0 : Real) 1) :
      src e u ∈ segment Real (q.vertex e) (q.vertex (e + 1)) := by
    rw [segment_eq_image]
    exact ⟨u, hu, rfl⟩
  have htgt_mem (e : Fin (r + 3)) (u : Real)
      (hu : u ∈ Set.Icc (0 : Real) 1) :
      tgt e u ∈ segment Real (t.target e) (t.target (e + 1)) := by
    rw [segment_eq_image]
    exact ⟨u, hu, rfl⟩
  refine ⟨hQinj, ?_, ?_⟩
  · intro i j hij
    apply Set.ext
    intro x
    constructor
    · intro hx
      rcases hx with ⟨hx_i, hx_j⟩
      rcases hfine_step i with ⟨bi, hai, hbi, hpi, hqi⟩
      rcases hfine_step j with ⟨bj, haj, hbj, hpj, hqj⟩
      rcases hsegment_scalar hx_i with ⟨θ, hθ, hxθ⟩
      rcases hsegment_scalar hx_j with ⟨φ, hφ, hxφ⟩
      let ci := s.parameter i + θ * (bi - s.parameter i)
      let cj := s.parameter j + φ * (bj - s.parameter j)
      have hqi0 : Q i = tgt (s.edge i) (s.parameter i) := rfl
      have hqj0 : Q j = tgt (s.edge j) (s.parameter j) := rfl
      have hpi0 : p.vertex i = src (s.edge i) (s.parameter i) := by
        simp [src, s.vertex_formula]
      have hpj0 : p.vertex j = src (s.edge j) (s.parameter j) := by
        simp [src, s.vertex_formula]
      have hx_i' : x = tgt (s.edge i) ci := by
        have hxθ' : x = (1 - θ) • Q i + θ • Q (i + 1) := by
          simpa [Q] using hxθ
        calc x = (1 - θ) • Q i + θ • Q (i + 1) := hxθ'
          _ = (1 - θ) • tgt (s.edge i) (s.parameter i) +
              θ • tgt (s.edge i) bi := by rw [hqi0, hqi]
          _ = tgt (s.edge i) ci := by
            simpa [ci, tgt] using hmix (t.target (s.edge i))
              (t.target (s.edge i + 1)) (s.parameter i) bi θ
      have hx_j' : x = tgt (s.edge j) cj := by
        have hxφ' : x = (1 - φ) • Q j + φ • Q (j + 1) := by
          simpa [Q] using hxφ
        calc x = (1 - φ) • Q j + φ • Q (j + 1) := hxφ'
          _ = (1 - φ) • tgt (s.edge j) (s.parameter j) +
              φ • tgt (s.edge j) bj := by rw [hqj0, hqj]
          _ = tgt (s.edge j) cj := by
            simpa [cj, tgt] using hmix (t.target (s.edge j))
              (t.target (s.edge j + 1)) (s.parameter j) bj φ
      have hci : ci ∈ Set.Icc (0 : Real) 1 := by
        constructor
        · dsimp [ci]
          nlinarith [s.parameter_nonneg i, hθ.1, hθ.2, hai]
        · dsimp [ci]
          nlinarith [s.parameter_nonneg i, s.parameter_lt_one i, hθ.1,
            hθ.2, hai, hbi]
      have hcj : cj ∈ Set.Icc (0 : Real) 1 := by
        constructor
        · dsimp [cj]
          nlinarith [s.parameter_nonneg j, hφ.1, hφ.2, haj]
        · dsimp [cj]
          nlinarith [s.parameter_nonneg j, s.parameter_lt_one j, hφ.1,
            hφ.2, haj, hbj]
      by_cases he : s.edge i = s.edge j
      · let y := src (s.edge i) ci
        have hparam_eq : ci = cj := by
          apply hcoarse_inj_tgt (s.edge i)
          calc tgt (s.edge i) ci = x := hx_i'.symm
            _ = tgt (s.edge j) cj := hx_j'
            _ = tgt (s.edge i) cj := by rw [he]
        have hy_i : y ∈ segment Real (p.vertex i) (p.vertex (i + 1)) := by
          rw [segment_eq_image]
          refine ⟨θ, hθ, ?_⟩
          dsimp [y]
          rw [hpi0, hpi]
          simpa [src] using hmix (q.vertex (s.edge i)) (q.vertex (s.edge i + 1))
            (s.parameter i) bi θ
        have hy_j : y ∈ segment Real (p.vertex j) (p.vertex (j + 1)) := TargetBoundaryProof.hy_j
            r n q p s hmix i j bi bj hpj θ φ hφ hpj0 he hparam_eq
        have hy : y ∈ segment Real (p.vertex i) (p.vertex (i + 1)) ∩
            segment Real (p.vertex j) (p.vertex (j + 1)) := ⟨hy_i, hy_j⟩
        rw [p.edge_intersection i j hij] at hy
        rcases hy with ⟨hi_end, hj_end⟩
        have hx_i_end : x = Q i ∨ x = Q (i + 1) := TargetBoundaryProof.hx_i_endAt340 r n q p s X
            K t hcoarse_inj_src i x bi hpi hqi θ hqi0 hpi0 hx_i' hi_end
        have hx_j_end : x = Q j ∨ x = Q (j + 1) := TargetBoundaryProof.hx_j_endAt358 r n q p s X
            K t hcoarse_inj_src i j x bi bj hpj hqj θ φ hqj0 hpj0 hx_j' he hparam_eq hj_end
        exact ⟨hx_i_end, hx_j_end⟩
      · have hx_coarse_i : x ∈ segment Real (t.target (s.edge i))
            (t.target (s.edge i + 1)) := by
          rw [hx_i']
          exact htgt_mem (s.edge i) ci hci
        have hx_coarse_j : x ∈ segment Real (t.target (s.edge j))
            (t.target (s.edge j + 1)) := by
          rw [hx_j']
          exact htgt_mem (s.edge j) cj hcj
        have hx_coarse : x ∈ segment Real (t.target (s.edge i))
            (t.target (s.edge i + 1)) ∩
            segment Real (t.target (s.edge j)) (t.target (s.edge j + 1)) :=
          ⟨hx_coarse_i, hx_coarse_j⟩
        rw [t.target_edge_intersection _ _ he] at hx_coarse
        rcases hx_coarse with ⟨hi_end, hj_end⟩
        have hx_i_end : x = Q i ∨ x = Q (i + 1) := TargetBoundaryProof.hx_i_endAt391 r n q p s X
            K t hcoarse_inj_tgt i x bi hai hbi hqi θ hθ hqi0 hx_i' hi_end
        have hx_j_end : x = Q j ∨ x = Q (j + 1) := TargetBoundaryProof.hx_j_endAt415 r n q p s X
            K t hcoarse_inj_tgt j x bj haj hbj hqj φ hφ hqj0 hx_j' hj_end
        exact ⟨hx_i_end, hx_j_end⟩
    · intro hx
      rcases hx with ⟨hxi, hxj⟩
      rcases hxi with hxi | hxi
      · rcases hxj with hxj | hxj
        · subst x
          exact ⟨left_mem_segment Real _ _, by rw [hxj]; exact left_mem_segment Real _ _⟩
        · subst x
          exact ⟨left_mem_segment Real _ _, by rw [hxj]; exact right_mem_segment Real _ _⟩
      · rcases hxj with hxj | hxj
        · subst x
          exact ⟨right_mem_segment Real _ _, by rw [hxj]; exact left_mem_segment Real _ _⟩
        · subst x
          exact ⟨right_mem_segment Real _ _, by rw [hxj]; exact right_mem_segment Real _ _⟩
  have hfine_subset :
      (⋃ j : Fin (n + 3), segment Real (Q j) (Q (j + 1))) ⊆
        ⋃ e : Fin (r + 3), segment Real (t.target e) (t.target (e + 1)) :=
            TargetBoundaryProof.hfine_subset r n q p s X K t hfine_step htgt_mem
  have hcoarse_subset :
      (⋃ e : Fin (r + 3), segment Real (t.target e) (t.target (e + 1))) ⊆
        ⋃ j : Fin (n + 3), segment Real (Q j) (Q (j + 1)) := TargetBoundaryProof.hcoarse_subset r
            n q p s X K t hfine_step hmix hsegment_scalar hcoarse_inj_src hsrc_mem
  have hcarrier : (⋃ j : Fin (n + 3), segment Real (Q j) (Q (j + 1))) =
      ⋃ e : Fin (r + 3), segment Real (t.target e) (t.target (e + 1)) :=
    Set.Subset.antisymm hfine_subset hcoarse_subset
  calc
    frontier K = ⋃ e : Fin (r + 3), segment Real (t.target e) (t.target (e + 1)) :=
        t.target_frontier
    _ = ⋃ j : Fin (n + 3), segment Real (Q j) (Q (j + 1)) := hcarrier.symm

end ApollonianSuperharmonic

end
