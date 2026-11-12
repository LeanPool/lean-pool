/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3934T1PolygonalSide
public import LeanPool.ApollonianSuperharmonic.P3934T1SectorContinuation
public import LeanPool.ApollonianSuperharmonic.P5667T1StraightFrontierLocalSides
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field

-- [TABLET NODE: P3934T1PolygonalSidePropagation]

/-!
# P3934T1PolygonalSidePropagation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PolygonSidePropagation

private theorem transfer :
    (by
      classical
      exact
        ∀ (W : Set (ℝ × ℝ)), ∀ (x : ℝ × ℝ), ∀ (r : ℝ), ∀ (C : Set (ℝ × ℝ)), ∀ (z : ℝ × ℝ), ∀ (w :
            ℝ × ℝ), ∀ (e : Bool), z ∈ Metric.ball x r → W ∩ Metric.ball x r = C →
            P3934T1LocalSide C z w e → P3934T1LocalSide W z w e ) := by
  classical
  intro W x r C z w e hz heq hside
  obtain ⟨δ, hδ, hside⟩ := hside
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z hz
  refine ⟨min δ ρ, lt_min hδ hρ, ?_⟩
  ext q
  have small (hq : q ∈ Metric.ball z (min δ ρ)) : q ∈ Metric.ball z δ :=
    Metric.ball_subset_ball (min_le_left δ ρ) hq
  have big (hq : q ∈ Metric.ball z (min δ ρ)) : q ∈ Metric.ball x r :=
    hsub (Metric.ball_subset_ball (min_le_right δ ρ) hq)
  constructor
  · rintro ⟨hqu, hqb⟩
    have hc : q ∈ C := heq ▸ ⟨hqu, big hqb⟩
    have hm : q ∈ C ∩ Metric.ball z δ := ⟨hc, small hqb⟩
    rw [hside] at hm
    exact ⟨hqb, hm.2⟩
  · rintro ⟨hqb, hqside⟩
    have hm : q ∈ C ∩ Metric.ball z δ := by
      rw [hside]
      exact ⟨small hqb, hqside⟩
    have hc := hm.1
    rw [← heq] at hc
    exact ⟨hc.1, hqb⟩

private theorem bend :
    (by
      classical
      exact
        ∀ (U : Set (Real × Real)), (IsOpen U) → ((frontier (closure U)ᶜ = frontier U) → ((∀ (W :
            Set (Real × Real)), ∀ (x : Real × Real), ∀ (r : Real), ∀ (C : Set (Real × Real)), ∀
            (z : Real × Real), ∀ (w : Real × Real), ∀ (e : Bool), (z ∈ Metric.ball x r) → ((W ∩
            Metric.ball x r = C) → ((P3934T1LocalSide C z w e) → (P3934T1LocalSide W z w
            e)))) → (∀ (x : ℝ × ℝ), ∀ (r : ℝ), ∀ (u : ℝ × ℝ), ∀ (v : ℝ × ℝ), (0 : ℝ) < r → ‖u‖ =
            (1 : ℝ) → ‖v‖ = (1 : ℝ) → u ≠ v → x ∈ frontier U → frontier U ∩ Metric.ball x r = ({p
            : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤ t ∧ p = x + t • u} ∪ {p : ℝ × ℝ | ∃ (t : ℝ), (0 : ℝ) ≤
            t ∧ p = x + t • v}) ∩ Metric.ball x r → ∃ (e : Bool), ∀ (t : ℝ), (0 : ℝ) < t → t < r
            → P3934T1LocalSide U (x + t • u) (-u) e ∧ P3934T1LocalSide U (x + t • v) v e ∧
            P3934T1LocalSide (closure U)ᶜ (x + t • u) (-u) !e ∧ P3934T1LocalSide (closure U)ᶜ
            (x + t • v) v !e))) ) := by
  classical
  intro U hU he transfer x r u v hr hu hv hne hx hchart
  obtain ⟨E⟩ := P3889T1TwoRaySectors x r u v hr hu hv hne
  have selected := P3934T1SectorSelection U x r u v E hr hU hx he hchart
  obtain ⟨e, hsides⟩ := P3934T1SectorContinuation x r u v hr hu hv hne E
  have in_ball (w : Real × Real) (hw : ‖w‖ = 1) (t : Real)
      (ht : 0 < t) (htr : t < r) : x + t • w ∈ Metric.ball x r := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, hw, mul_one] using htr
  rcases selected with h | h
  · refine ⟨e, ?_⟩
    intro t ht htr
    have sides := hsides t ht htr
    exact ⟨transfer U x r E.left _ _ e (in_ball u hu t ht htr) h.1 sides.1,
      transfer U x r E.left _ _ e (in_ball v hv t ht htr) h.1 sides.2.1,
      transfer (closure U)ᶜ x r E.right _ _ (!e) (in_ball u hu t ht htr) h.2 sides.2.2.1,
      transfer (closure U)ᶜ x r E.right _ _ (!e) (in_ball v hv t ht htr) h.2 sides.2.2.2⟩
  · refine ⟨!e, ?_⟩
    intro t ht htr
    have sides := hsides t ht htr
    refine ⟨transfer U x r E.right _ _ (!e) (in_ball u hu t ht htr) h.1 sides.2.2.1,
      transfer U x r E.right _ _ (!e) (in_ball v hv t ht htr) h.1 sides.2.2.2,
      ?_, ?_⟩
    · simpa using transfer (closure U)ᶜ x r E.left _ _ e
        (in_ball u hu t ht htr) h.2 sides.1
    · simpa using transfer (closure U)ᶜ x r E.left _ _ e
        (in_ball v hv t ht htr) h.2 sides.2.1

private theorem pieceData :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), (∀ (k : Fin (3 : ℕ)), Function.Injective
            (g k)) → (∀ (k : Fin (3 : ℕ)), ∀ (i : Fin (s k).count), ∃ (A : ℝ × ℝ) (B : ℝ × ℝ), B
            ≠ (0 : ℝ × ℝ) ∧ ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s k).time i.castSucc ≤
            (↑t : ℝ) → (↑t : ℝ) ≤ (s k).time i.succ → g k t = A + (↑t : ℝ) • B) ) := by
  classical
  intro g s hi k i
  obtain ⟨A, B, hline⟩ := (s k).affine_on i
  refine ⟨A, B, ?_, hline⟩
  intro hB
  have htime : (s k).time i.castSucc < (s k).time i.succ :=
    (s k).strict Fin.castSucc_lt_succ
  have hfirst : 0 ≤ (s k).time i.castSucc := by
    calc
      0 = (s k).time 0 := (s k).start.symm
      _ ≤ (s k).time i.castSucc := (s k).strict.monotone (Fin.zero_le _)
  have hlast : (s k).time i.succ ≤ 1 := by
    calc
      (s k).time i.succ ≤ (s k).time (Fin.last (s k).count) :=
        (s k).strict.monotone (Fin.le_last _)
      _ = 1 := (s k).finish
  let a : Set.Icc (0 : Real) 1 := ⟨(s k).time i.castSucc, ⟨hfirst, htime.le.trans hlast⟩⟩
  let b : Set.Icc (0 : Real) 1 := ⟨(s k).time i.succ, ⟨hfirst.trans htime.le, hlast⟩⟩
  have heq : g k a = g k b := by
    rw [hline a le_rfl htime.le, hline b htime.le le_rfl, hB]
    simp
  have hab : a = b := hi k heq
  have : (s k).time i.castSucc = (s k).time i.succ := congrArg Subtype.val hab
  exact (ne_of_lt htime) this

private theorem compactRange :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), (∀ (k : Fin (3 : ℕ)), Continuous (g
            k)) → (∀ (k : Fin (3 : ℕ)), IsCompact (Set.range (g k))) ) := by
  classical
  intro g hc k
  rw [← Set.image_univ]
  exact isCompact_univ.image (hc k)

private theorem avoidClosed :
    (by
      classical
      exact
        ∀ (K : Set (ℝ × ℝ)), IsClosed K → ∀ z ∉ K, ∃ (r : ℝ), (0 : ℝ) < r ∧ Disjoint (Metric.ball
            z r) K ) := by
  classical
  intro K hK z hz
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (hK.isOpen_compl.mem_nhds hz)
  refine ⟨r, hr, Set.disjoint_left.mpr ?_⟩
  intro q hqball hqK
  exact (hsub hqball) hqK

private theorem isolatePiece :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), (∀ (k : Fin (3 : ℕ)), Function.Injective
            (g k)) → ((∀ (k : Fin (3 : ℕ)), ∀ (l : Fin (3 : ℕ)), k ≠ l → Set.range (g k) ∩
            Set.range (g l) ⊆ {q : ℝ × ℝ | (q = g k ⟨(0 : ℝ),
            (by norm_num)⟩ ∨ q = g k ⟨(1 : ℝ),
            (by norm_num)⟩) ∧ (q = g l ⟨(0 : ℝ),
            (by norm_num)⟩ ∨ q = g l ⟨(1 : ℝ),
            (by norm_num)⟩)}) → ((∀ (k : Fin 3), IsCompact
            (Set.range (g k))) → ((∀ (k : Fin 3), ∀ (S : Set (Set.Icc (0 : Real) 1)), (IsClosed
            S) → (IsCompact (g k '' S))) → ((∀ (K : Set (Real × Real)), (IsClosed K) → (∀ (z :
            Real × Real), (z ∉ K) → (∃ r : Real, 0 < r ∧ Disjoint (Metric.ball z r) K))) → (∀ (k
            : Fin (3 : ℕ)), ∀ (i : Fin (s k).count), ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)),
            (s k).time i.castSucc < (↑t : ℝ) → (↑t : ℝ) < (s k).time i.succ → ∃ (r : ℝ), (0 : ℝ)
            < r ∧ ∀ (l : Fin (3 : ℕ)), ∀ (a : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), g l a ∈
            Metric.ball (g k t) r → l = k ∧ (s k).time i.castSucc < (↑a : ℝ) ∧ (↑a : ℝ) < (s
            k).time i.succ))))) ) := by
  classical
  intro g s hi hinter compactRange compactImage avoidClosed k i t htlo hthi
  let bad : Set (Set.Icc (0 : Real) 1) :=
    {a | (a : Real) ≤ (s k).time i.castSucc ∨
      (s k).time i.succ ≤ (a : Real)}
  have hbad : IsClosed bad := by
    have hEq : badᶜ = Subtype.val ⁻¹' Set.Ioo
        ((s k).time i.castSucc) ((s k).time i.succ) := by
      ext a
      simp [bad, Set.mem_Ioo, not_or, not_le]
    rw [← isOpen_compl_iff, hEq]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hbadpoint : g k t ∉ g k '' bad := by
    rintro ⟨a, ha, hga⟩
    have hat : a = t := hi k (by rw [hga])
    subst a
    change (t : Real) ≤ (s k).time i.castSucc ∨
      (s k).time i.succ ≤ (t : Real) at ha
    rcases ha with ha | ha
    · exact (not_le_of_gt htlo) ha
    · exact (not_le_of_gt hthi) ha
  let K : Set (Real × Real) :=
    ⋃ l : Fin 3, g l '' (if l = k then bad else Set.univ)
  have hKcompact : IsCompact K := by
    have hpieces : ∀ l : Fin 3, IsCompact
        (g l '' (if l = k then bad else Set.univ)) := by
      intro l
      by_cases hl : l = k
      · subst l
        simpa [bad] using compactImage k bad hbad
      · rw [ite_eq_right hl, Set.image_univ]
        exact compactRange l
    simpa [K] using (Set.toFinite (Set.univ : Set (Fin 3))).isCompact_biUnion
      (fun l _ => hpieces l)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hpoint : g k t ∉ K := by
    intro hz
    change g k t ∈ ⋃ l : Fin 3, g l '' (if l = k then bad else Set.univ) at hz
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hz
    by_cases hkl : l = k
    · subst l
      exact hbadpoint (by simpa using hl)
    · obtain ⟨a, ha, hga⟩ := hl
      have hq : g k t ∈ Set.range (g k) ∩ Set.range (g l) := by
        refine ⟨⟨t, rfl⟩, ?_⟩
        exact ⟨a, hga⟩
      obtain ⟨hendk, hendl⟩ := hinter k l (Ne.symm hkl) hq
      rcases hendk with hendk | hendk
      · have hteq : t = ⟨0, by norm_num⟩ := hi k (by simpa using hendk)
        have htpos : 0 < (t : Real) := lt_of_le_of_lt
          (by rw [← (s k).start]; exact (s k).strict.monotone (Fin.zero_le _)) htlo
        have htval : (t : Real) = 0 := congrArg Subtype.val hteq
        linarith
      · have hteq : t = ⟨1, by norm_num⟩ := hi k (by simpa using hendk)
        have htlt : (t : Real) < 1 := lt_of_lt_of_le hthi (by
          calc (s k).time i.succ ≤ (s k).time (Fin.last (s k).count) :=
                  (s k).strict.monotone (Fin.le_last _)
            _ = 1 := (s k).finish)
        have htval : (t : Real) = 1 := congrArg Subtype.val hteq
        linarith
  obtain ⟨r, hr, hdis⟩ := avoidClosed K hKclosed (g k t) hpoint
  refine ⟨r, hr, ?_⟩
  intro l a ha
  have hnotK : g l a ∉ K := by
    intro hm
    exact (Set.disjoint_left.mp hdis ha) hm
  by_cases hl : l = k
  · subst l
    refine ⟨rfl, ?_, ?_⟩
    · by_contra h
      have hmem : g k a ∈ K := by
        change g k a ∈ ⋃ l : Fin 3, g l '' (if l = k then bad else Set.univ)
        apply Set.mem_iUnion.mpr
        refine ⟨k, ?_⟩
        simp only []
        exact ⟨a, Set.mem_ofPred_eq.mpr (Or.inl (le_of_not_gt h)), rfl⟩
      exact hnotK hmem
    · by_contra h
      have hmem : g k a ∈ K := by
        change g k a ∈ ⋃ l : Fin 3, g l '' (if l = k then bad else Set.univ)
        apply Set.mem_iUnion.mpr
        refine ⟨k, ?_⟩
        simp only []
        exact ⟨a, Set.mem_ofPred_eq.mpr (Or.inr (le_of_not_gt h)), rfl⟩
      exact hnotK hmem
  · have hmem : g l a ∈ K := by
      change g l a ∈ ⋃ j : Fin 3, g j '' (if j = k then bad else Set.univ)
      apply Set.mem_iUnion.mpr
      refine ⟨l, ?_⟩
      rw [ite_eq_right hl, Set.image_univ]
      exact ⟨a, rfl⟩
    exact (hnotK hmem).elim


private theorem straightFrontierRays :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (U : Set (Real × Real)), (frontier U = ⋃
            (k : Fin (3 : ℕ)), Set.range (g k)) → ((∀ (k : Fin 3), ∀ (i : Fin (s k).count), ∀ (t
            : Set.Icc (0 : Real) 1), ((s k).time i.castSucc < (t : Real)) → (((t : Real) < (s
            k).time i.succ) → (∃ r : Real, 0 < r ∧ ∀ l, ∀ (a : Set.Icc (0 : Real) 1), g l a ∈
            Metric.ball (g k t) r → l = k ∧ (s k).time i.castSucc < (a : Real) ∧ (a : Real) < (s
            k).time i.succ))) → (∀ (k : Fin (3 : ℕ)), ∀ (i : Fin (s k).count), ∀ (A : ℝ × ℝ), ∀
            (B : ℝ × ℝ), B ≠ (0 : ℝ × ℝ) → (∀ (a : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s
            k).time i.castSucc ≤ (↑a : ℝ) → (↑a : ℝ) ≤ (s k).time i.succ → g k a = A + (↑a : ℝ) •
            B) → ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s k).time i.castSucc < (↑t : ℝ) →
            (↑t : ℝ) < (s k).time i.succ → ∃ (r : ℝ), (0 : ℝ) < r ∧ frontier U ∩ Metric.ball (g k
            t) r = ({q : ℝ × ℝ | ∃ (a : ℝ), (0 : ℝ) ≤ a ∧ q = g k t + a • ‖B‖⁻¹ • B} ∪ {q : ℝ × ℝ
            | ∃ (a : ℝ), (0 : ℝ) ≤ a ∧ q = g k t - a • ‖B‖⁻¹ • B}) ∩ Metric.ball (g k t) r)) ) := by
  classical
  intro g s U hf isolatePiece k i A B hB hline t htlo hthi
  obtain ⟨r, hr, hisolate⟩ := isolatePiece k i t htlo hthi
  let n : Real := ‖B‖
  have hn : 0 < n := by
    dsimp [n]
    exact norm_pos_iff.mpr hB
  let d : Real × Real := n⁻¹ • B
  have hBdecomp : B = n • d := by
    dsimp [d]
    rw [smul_smul]
    simp [n, hn.ne']
  have hd : ‖d‖ = 1 := by
    dsimp [d]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    change n⁻¹ * n = 1
    exact inv_mul_cancel₀ hn.ne'
  have hlineT := hline t (le_of_lt htlo) (le_of_lt hthi)
  have hfirst : 0 ≤ (s k).time i.castSucc := by
    calc
      0 = (s k).time 0 := (s k).start.symm
      _ ≤ (s k).time i.castSucc := (s k).strict.monotone (Fin.zero_le _)
  have hlast : (s k).time i.succ ≤ 1 := by
    calc
      (s k).time i.succ ≤ (s k).time (Fin.last (s k).count) :=
        (s k).strict.monotone (Fin.le_last _)
      _ = 1 := (s k).finish
  let R : Real := min r (min (((t : Real) - (s k).time i.castSucc) * n)
    (((s k).time i.succ - (t : Real)) * n))
  have hR : 0 < R := by
    dsimp [R]
    exact lt_min hr (lt_min (mul_pos (by linarith) hn)
      (mul_pos (by linarith) hn))
  have hRiso : R ≤ r := min_le_left _ _
  have hRleft : R ≤ ((t : Real) - (s k).time i.castSucc) * n :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hRright : R ≤ ((s k).time i.succ - (t : Real)) * n :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R, hR, ?_⟩
  ext q
  constructor
  · rintro ⟨hqfront, hqball⟩
    have hqball' : q ∈ Metric.ball (g k t) r :=
      Metric.ball_subset_ball hRiso hqball
    have hqRays : q ∈
        {q | ∃ a : Real, 0 ≤ a ∧ q = g k t + a • d} ∪
          {q | ∃ a : Real, 0 ≤ a ∧ q = g k t - a • d} := by
      rw [hf] at hqfront
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hqfront
      obtain ⟨a, hga⟩ := hl
      have hgaBall : g l a ∈ Metric.ball (g k t) r := by rw [hga]; exact hqball'
      obtain ⟨hlk, haLo, haHi⟩ := hisolate l a hgaBall
      have hgaK : g k a = q := by simpa [hlk] using hga
      have hlineA := hline a (le_of_lt haLo) (le_of_lt haHi)
      have hdiff : q = g k t + ((a : Real) - (t : Real)) • B := by
        rw [← hgaK, hlineA, hlineT]
        ext <;> simp [smul_eq_mul] <;> ring
      have hdiff' : q = g k t + (((a : Real) - (t : Real)) * n) • d := by
        rw [hdiff, hBdecomp, smul_smul]
      by_cases hc : 0 ≤ ((a : Real) - (t : Real)) * n
      · left
        exact ⟨_, hc, by simpa [n, d] using hdiff'⟩
      · right
        have hneg : ((a : Real) - (t : Real)) * n < 0 := lt_of_not_ge hc
        refine ⟨-(((a : Real) - (t : Real)) * n), neg_nonneg.mpr hneg.le, ?_⟩
        have hvec : -((-(((a : Real) - (t : Real)) * n)) • d) =
            (((a : Real) - (t : Real)) * n) • d := by
          ext <;> simp [d, Prod.smul_fst, Prod.smul_snd]
        calc
          q = g k t + (((a : Real) - (t : Real)) * n) • d := hdiff'
          _ = g k t - (-(((a : Real) - (t : Real)) * n)) • d := by
            rw [← hvec]
            simp [sub_eq_add_neg]
    exact ⟨hqRays, hqball⟩
  · rintro ⟨hqRays, hqball⟩
    refine ⟨?_, hqball⟩
    rcases hqRays with hplus | hminus
    · obtain ⟨a, ha, hqa⟩ := hplus
      have hsmall : a < R := by
        have hdist := Metric.mem_ball.mp hqball
        have hqa' : q = g k t + a • d := by simpa [n, d] using hqa
        rw [hqa', dist_eq_norm] at hdist
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ha, hd, mul_one] at hdist
        nlinarith [hdist]
      have hdelta : a / n < (s k).time i.succ - (t : Real) := by
        apply (div_lt_iff₀ hn).2
        exact lt_of_lt_of_le hsmall hRright
      have hparam : (t : Real) + a / n < (s k).time i.succ := by linarith
      have hparamlo : (s k).time i.castSucc ≤ (t : Real) + a / n := by
        have hdiv : 0 ≤ a / n := div_nonneg ha hn.le
        linarith [htlo, hdiv]
      have hparam0 : 0 ≤ (t : Real) + a / n := by
        have hdiv : 0 ≤ a / n := div_nonneg ha hn.le
        linarith [hfirst, htlo, hdiv]
      have hparam1 : (t : Real) + a / n ≤ 1 :=
        le_of_lt (hparam.trans_le hlast)
      let b : Set.Icc (0 : Real) 1 := ⟨(t : Real) + a / n, ⟨hparam0, hparam1⟩⟩
      have hlineB := hline b hparamlo (le_of_lt hparam)
      have hmove : (a / n) • B = a • d := by
        rw [hBdecomp, smul_smul]
        congr 1
        field_simp [hn.ne']
      have hgb : g k b = q := by
        calc
          g k b = A + ((t : Real) + a / n) • B := hlineB
          _ = (A + (t : Real) • B) + (a / n) • B := by
            ext <;> simp [smul_eq_mul] <;> ring
          _ = g k t + a • d := by rw [hlineT, hmove]
          _ = q := hqa.symm
      rw [hf]
      exact Set.mem_iUnion.mpr ⟨k, ⟨b, hgb⟩⟩
    · obtain ⟨a, ha, hqa⟩ := hminus
      have hsmall : a < R := by
        have hdist := Metric.mem_ball.mp hqball
        have hqa' : q = g k t - a • d := by simpa [n, d] using hqa
        rw [dist_eq_norm] at hdist
        have hdiff : q - g k t = -(a • d) := by rw [hqa']; simp
        rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ha, hd, mul_one] at hdist
        simpa only [mul_one] using hdist
      have hdelta : a / n < (t : Real) - (s k).time i.castSucc := by
        apply (div_lt_iff₀ hn).2
        exact lt_of_lt_of_le hsmall hRleft
      have hparam : (s k).time i.castSucc < (t : Real) - a / n := by linarith
      have hparamhi : (t : Real) - a / n ≤ (s k).time i.succ := by
        have hdiv : 0 ≤ a / n := div_nonneg ha hn.le
        linarith [hthi, hdiv]
      have hparam0 : 0 ≤ (t : Real) - a / n := by linarith [hfirst, hparam]
      have hparam1 : (t : Real) - a / n ≤ 1 := hparamhi.trans hlast
      let b : Set.Icc (0 : Real) 1 := ⟨(t : Real) - a / n, ⟨hparam0, hparam1⟩⟩
      have hlineB := hline b (le_of_lt hparam) hparamhi
      have hmove : (a / n) • B = a • d := by
        rw [hBdecomp, smul_smul]
        congr 1
        field_simp [hn.ne']
      have hgb : g k b = q := by
        calc
          g k b = A + ((t : Real) - a / n) • B := hlineB
          _ = (A + (t : Real) • B) - (a / n) • B := by
            ext <;> simp [smul_eq_mul, sub_eq_add_neg] <;> ring
          _ = g k t - a • d := by rw [hlineT, hmove]
          _ = q := hqa.symm
      rw [hf]
      exact Set.mem_iUnion.mpr ⟨k, ⟨b, hgb⟩⟩

private theorem straightSideAt :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (U : Set (Real × Real)), (IsOpen U) →
            ((frontier (closure U)ᶜ = frontier U) → ((∀ (k : Fin 3), ∀ (i : Fin (s k).count), ∀
            (A : Real × Real), ∀ (B : Real × Real), (B ≠ 0) → ((∀ a : Set.Icc (0 : Real) 1, (s
            k).time i.castSucc ≤ (a : Real) → (a : Real) ≤ (s k).time i.succ → g k a = A + (a :
            Real) • B) → (∀ (t : Set.Icc (0 : Real) 1), ((s k).time i.castSucc < (t : Real)) →
            (((t : Real) < (s k).time i.succ) → (∃ r : Real, 0 < r ∧ frontier U ∩ Metric.ball (g
            k t) r = ({q | ∃ a : Real, 0 ≤ a ∧ q = g k t + a • (‖B‖⁻¹ • B)} ∪ {q | ∃ a : Real, 0
            ≤ a ∧ q = g k t - a • (‖B‖⁻¹ • B)}) ∩ Metric.ball (g k t) r))))) → (∀ (k : Fin (3 :
            ℕ)), ∀ (i : Fin (s k).count), ∀ (A : ℝ × ℝ), ∀ (B : ℝ × ℝ), B ≠ (0 : ℝ × ℝ) → (∀ (a :
            (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s k).time i.castSucc ≤ (↑a : ℝ) → (↑a : ℝ) ≤
            (s k).time i.succ → g k a = A + (↑a : ℝ) • B) → ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) :
            Type)), (s k).time i.castSucc < (↑t : ℝ) → (↑t : ℝ) < (s k).time i.succ → ∃ (e :
            Bool), P3934T1LocalSide U (g k t) B e ∧ P3934T1LocalSide (closure U)ᶜ (g k t) B
            !e))) ) := by
  classical
  intro g s U hU he straightFrontierRays k i A B hB hline t htlo hthi
  obtain ⟨r, hr, hchart⟩ := straightFrontierRays k i A B hB hline t htlo hthi
  exact P5667T1StraightFrontierLocalSides U hU he (g k t) B hB r hr hchart

private theorem sideMove :
    (by
      classical
      exact
        ∀ (W : Set (ℝ × ℝ)), ∀ (z : ℝ × ℝ), ∀ (z' : ℝ × ℝ), ∀ (w : ℝ × ℝ), ∀ (e : Bool), (∃ (c :
            ℝ), z' = z + c • w) → ∀ (hside : P3934T1LocalSide W z w e), dist z' z <
            Classical.choose hside → P3934T1LocalSide W z' w e ) := by
  classical
  intro W z z' w e hshift hside hclose
  let r := Classical.choose hside
  have hspec := Classical.choose_spec hside
  obtain ⟨hr, heq⟩ := hspec
  have hdist : dist z' z < r := hclose
  let δ := r - dist z' z
  have hδ : 0 < δ := sub_pos.mpr hdist
  have hsmall (q : Real × Real) (hq : q ∈ Metric.ball z' δ) :
      q ∈ Metric.ball z r := by
    rw [Metric.mem_ball] at hq ⊢
    calc
      dist q z ≤ dist q z' + dist z' z := dist_triangle _ _ _
      _ < δ + dist z' z := add_lt_add_left hq _
      _ = r := by dsimp [δ]; ring
  have hdet (q : Real × Real) :
      w.1 * (q.2 - z'.2) - w.2 * (q.1 - z'.1) =
        w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1) := by
    obtain ⟨c, hc⟩ := hshift
    rw [hc]
    simp [Prod.smul_fst, Prod.smul_snd]
    ring
  refine ⟨δ, hδ, ?_⟩
  ext q
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hW, hq⟩
    have hmem : q ∈ W ∩ Metric.ball z r := ⟨hW, hsmall q hq⟩
    rw [heq] at hmem
    rcases hmem with ⟨_, hsign⟩
    refine ⟨hq, ?_⟩
    simpa only [hdet q] using hsign
  · rintro ⟨hq, hsign⟩
    have hsign' : (if e then
        0 < w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1) else
        w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1) < 0) := by
      simpa only [hdet q] using hsign
    have hmem : q ∈ Metric.ball z r ∧ (if e then
        0 < w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1) else
        w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1) < 0) :=
      ⟨hsmall q hq, hsign'⟩
    have hmem' : q ∈ W ∩ Metric.ball z r := heq.symm ▸ hmem
    exact ⟨hmem'.1, hq⟩

private theorem sideSignsDisjoint :
    (by
      classical
      exact
        ∀ (W : Set (ℝ × ℝ)), ∀ (z : ℝ × ℝ), ∀ (w : ℝ × ℝ), w ≠ (0 : ℝ × ℝ) → P3934T1LocalSide W
            z w true → P3934T1LocalSide W z w false → False ) := by
  classical
  intro W z w hw hpos hneg
  obtain ⟨r₁, hr₁, heq₁⟩ := hpos
  obtain ⟨r₂, hr₂, heq₂⟩ := hneg
  let j : Real × Real := (-w.2, w.1)
  have hnormj : ‖j‖ = ‖w‖ := by
    dsimp [j]
    simp [Prod.norm_def, Real.norm_eq_abs, max_comm]
  have hj : 0 < ‖j‖ := by
    rw [hnormj]
    exact norm_pos_iff.mpr hw
  have hsq : 0 < w.1 ^ 2 + w.2 ^ 2 := by
    rcases (show w.1 ≠ 0 ∨ w.2 ≠ 0 from by
      by_contra h
      push Not at h
      apply hw
      ext <;> simp [h.1, h.2]) with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)
  let m := min r₁ r₂
  let ε := m / (2 * ‖j‖)
  let q := z + ε • j
  have hm : 0 < m := lt_min hr₁ hr₂
  have hε : 0 < ε := div_pos hm (by positivity)
  have hdist : dist q z = ε * ‖j‖ := by
    rw [dist_eq_norm]
    have hdiff : q - z = ε • j := by simp [q]
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hdistHalf : ε * ‖j‖ = m / 2 := by
    dsimp [ε]
    field_simp [hj.ne']
  have hsmall₁ : dist q z < r₁ := by
    rw [hdist]
    rw [hdistHalf]
    have hm₁ : m ≤ r₁ := min_le_left _ _
    linarith [hm]
  have hsmall₂ : dist q z < r₂ := by
    rw [hdist]
    rw [hdistHalf]
    have hm₂ : m ≤ r₂ := min_le_right _ _
    linarith [hm]
  have hD : w.1 * (q.2 - z.2) - w.2 * (q.1 - z.1) > 0 := by
    dsimp [q, j]
    simp []
    nlinarith [hsq, hε]
  have hq₁ : q ∈ Metric.ball z r₁ := by rw [Metric.mem_ball]; exact hsmall₁
  have hq₂ : q ∈ Metric.ball z r₂ := by rw [Metric.mem_ball]; exact hsmall₂
  have hmem₁ : q ∈ W ∩ Metric.ball z r₁ := by
    rw [heq₁]
    simp only [Set.mem_ofPred_eq]
    exact ⟨hq₁, hD⟩
  have hmem₂ : q ∈ W ∩ Metric.ball z r₂ := ⟨hmem₁.1, hq₂⟩
  rw [heq₂] at hmem₂
  simp only [Set.mem_ofPred_eq] at hmem₂
  exact (not_lt_of_ge (le_of_lt hD)) hmem₂.2

private theorem pieceConstant :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (U : Set (Real × Real)), (∀ (k : Fin 3),
            ∀ (i : Fin (s k).count), ∀ (A : Real × Real), ∀ (B : Real × Real), (B ≠ 0) → ((∀ a :
            Set.Icc (0 : Real) 1, (s k).time i.castSucc ≤ (a : Real) → (a : Real) ≤ (s k).time
            i.succ → g k a = A + (a : Real) • B) → (∀ (t : Set.Icc (0 : Real) 1), ((s k).time
            i.castSucc < (t : Real)) → (((t : Real) < (s k).time i.succ) → (∃ e : Bool,
            P3934T1LocalSide U (g k t) B e ∧ P3934T1LocalSide (closure U)ᶜ (g k t) B
            (!e)))))) → ((∀ (W : Set (Real × Real)), ∀ (z : Real × Real), ∀ (z' : Real × Real), ∀
            (w : Real × Real), ∀ (e : Bool), (∃ c : Real, z' = z + c • w) → (∀ (hside :
            P3934T1LocalSide W z w e), (dist z' z < Classical.choose hside) →
            (P3934T1LocalSide W z' w e))) → ((∀ (W : Set (Real × Real)), ∀ (z : Real × Real), ∀
            (w : Real × Real), (w ≠ 0) → ((P3934T1LocalSide W z w true) → ((P3934T1LocalSide
            W z w false) → (False)))) → (∀ (k : Fin (3 : ℕ)), ∀ (i : Fin (s k).count), ∀ (A : ℝ ×
            ℝ), ∀ (B : ℝ × ℝ), B ≠ (0 : ℝ × ℝ) → (∀ (a : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s
            k).time i.castSucc ≤ (↑a : ℝ) → (↑a : ℝ) ≤ (s k).time i.succ → g k a = A + (↑a : ℝ) •
            B) → ∃ (e : Bool), ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s k).time i.castSucc
            < (↑t : ℝ) → (↑t : ℝ) < (s k).time i.succ → P3934T1LocalSide U (g k t) B e ∧
            P3934T1LocalSide (closure U)ᶜ (g k t) B !e))) ) := by
  classical
  intro g s U straightSideAt sideMove sideSignsDisjoint k i A B hB hline
  classical
  let a : Set.Icc (0 : Real) 1 := ⟨(s k).time i.castSucc, by
    constructor
    · have hzero : 0 ≤ (s k).time 0 := by rw [(s k).start]
      exact hzero.trans ((s k).strict.monotone (Fin.zero_le _))
    · calc (s k).time i.castSucc ≤ (s k).time (Fin.last (s k).count) :=
            (s k).strict.monotone (Fin.le_last _)
          _ = 1 := (s k).finish⟩
  let b : Set.Icc (0 : Real) 1 := ⟨(s k).time i.succ, by
    constructor
    · calc 0 ≤ (s k).time 0 := by rw [(s k).start]
          _ ≤ (s k).time i.succ := (s k).strict.monotone (Fin.zero_le _)
    · have hl : i.succ ≤ Fin.last (s k).count := Fin.le_last _
      calc (s k).time i.succ ≤ (s k).time (Fin.last (s k).count) := (s k).strict.monotone hl
          _ = 1 := (s k).finish⟩
  have hab : a < b := by
    change (s k).time i.castSucc < (s k).time i.succ
    exact (s k).strict Fin.castSucc_lt_succ
  let I := Set.Ioo a b
  let param (x : I) : Set.Icc (0 : Real) 1 := x.1
  let point (t : Set.Icc (0 : Real) 1)
      (htlo : (s k).time i.castSucc < (t : Real))
      (hthi : (t : Real) < (s k).time i.succ) : I :=
    ⟨t, by
      constructor
      · change (a : Real) < (t : Real)
        exact htlo
      · change (t : Real) < (b : Real)
        exact hthi⟩
  have paramBounds (x : I) :
      (s k).time i.castSucc < (param x : Real) ∧
        (param x : Real) < (s k).time i.succ := by
    constructor
    · change (a : Real) < (x.1 : Real)
      exact x.2.1
    · change (x.1 : Real) < (b : Real)
      exact x.2.2
  let pos : Set I := {x | P3934T1LocalSide U (g k (param x)) B true}
  let neg : Set I := {x | P3934T1LocalSide U (g k (param x)) B false}
  have hhn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hposOpen : IsOpen pos := by
    rw [Metric.isOpen_iff]
    intro x hx
    change P3934T1LocalSide U (g k (param x)) B true at hx
    let ρ := Classical.choose hx
    have hρ : 0 < ρ := (Classical.choose_spec hx).1
    let ε := ρ / (2 * ‖B‖)
    have hε : 0 < ε := div_pos hρ (by positivity)
    refine ⟨ε, hε, ?_⟩
    intro y hy
    change P3934T1LocalSide U (g k (param y)) B true
    have hyval : |(param y : Real) - (param x : Real)| < ε := by
      have hyreal : dist (param y : Real) (param x : Real) < ε := by
        exact_mod_cast hy
      simpa [Real.dist_eq] using hyreal
    have hshift : g k (param y) = g k (param x) +
        ((param y : Real) - (param x : Real)) • B := by
      have hly := hline (param y) (le_of_lt (paramBounds y).1) (le_of_lt (paramBounds y).2)
      have hlx := hline (param x) (le_of_lt (paramBounds x).1) (le_of_lt (paramBounds x).2)
      rw [hly, hlx]
      ext <;> simp [smul_eq_mul] <;> ring
    have hdist : dist (g k (param y)) (g k (param x)) < ρ := by
      rw [dist_eq_norm, hshift, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc
        |(param y : Real) - (param x : Real)| * ‖B‖ < ε * ‖B‖ :=
          mul_lt_mul_of_pos_right hyval hhn
        _ = ρ / 2 := by dsimp [ε]; field_simp
        _ < ρ := by linarith
    exact sideMove U (g k (param x)) (g k (param y)) B true ⟨_, hshift⟩ hx hdist
  have hnegOpen : IsOpen neg := by
    rw [Metric.isOpen_iff]
    intro x hx
    change P3934T1LocalSide U (g k (param x)) B false at hx
    let ρ := Classical.choose hx
    have hρ : 0 < ρ := (Classical.choose_spec hx).1
    let ε := ρ / (2 * ‖B‖)
    have hε : 0 < ε := div_pos hρ (by positivity)
    refine ⟨ε, hε, ?_⟩
    intro y hy
    change P3934T1LocalSide U (g k (param y)) B false
    have hyval : |(param y : Real) - (param x : Real)| < ε := by
      have hyreal : dist (param y : Real) (param x : Real) < ε := by
        exact_mod_cast hy
      simpa [Real.dist_eq] using hyreal
    have hshift : g k (param y) = g k (param x) +
        ((param y : Real) - (param x : Real)) • B := by
      have hly := hline (param y) (le_of_lt (paramBounds y).1) (le_of_lt (paramBounds y).2)
      have hlx := hline (param x) (le_of_lt (paramBounds x).1) (le_of_lt (paramBounds x).2)
      rw [hly, hlx]
      ext <;> simp [smul_eq_mul] <;> ring
    have hdist : dist (g k (param y)) (g k (param x)) < ρ := by
      rw [dist_eq_norm, hshift, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc
        |(param y : Real) - (param x : Real)| * ‖B‖ < ε * ‖B‖ :=
          mul_lt_mul_of_pos_right hyval hhn
        _ = ρ / 2 := by dsimp [ε]; field_simp
        _ < ρ := by linarith
    exact sideMove U (g k (param x)) (g k (param y)) B false ⟨_, hshift⟩ hx hdist
  have hdis : Disjoint pos neg := by
    apply Set.disjoint_left.mpr
    intro x hx hn
    change P3934T1LocalSide U (g k (param x)) B true at hx
    change P3934T1LocalSide U (g k (param x)) B false at hn
    exact sideSignsDisjoint U (g k (param x)) B hB hx hn
  have hcover : (Set.univ : Set I) ⊆ pos ∪ neg := by
    intro x _
    obtain ⟨e, hUside, hVside⟩ := straightSideAt k i A B hB hline
      (param x) (paramBounds x).1 (paramBounds x).2
    cases e <;> simp [pos, neg, param, hUside]
  let : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Ioo
  have hconn : IsPreconnected (Set.univ : Set I) := isPreconnected_univ
  by_cases hp : ((Set.univ : Set I) ∩ pos).Nonempty
  · have hconst : (Set.univ : Set I) ⊆ pos :=
      hconn.subset_left_of_subset_union hposOpen hnegOpen hdis hcover hp
    refine ⟨true, ?_⟩
    intro t htlo hthi
    let x := point t htlo hthi
    have hUside : P3934T1LocalSide U (g k t) B true := by
      have := hconst (Set.mem_univ x)
      simpa [pos, param, x, point] using this
    obtain ⟨e, hU', hV'⟩ := straightSideAt k i A B hB hline
      t htlo hthi
    cases e
    · exact False.elim (sideSignsDisjoint U (g k t) B hB hUside hU')
    · exact ⟨hUside, hV'⟩
  · have hconst : (Set.univ : Set I) ⊆ neg := by
      intro x _
      rcases hcover (Set.mem_univ x) with hp' | hn'
      · exact (hp ⟨x, Set.mem_univ x, hp'⟩).elim
      · exact hn'
    refine ⟨false, ?_⟩
    intro t htlo hthi
    let x := point t htlo hthi
    have hUside : P3934T1LocalSide U (g k t) B false := by
      have := hconst (Set.mem_univ x)
      simpa [neg, param, x, point] using this
    obtain ⟨e, hU', hV'⟩ := straightSideAt k i A B hB hline
      t htlo hthi
    cases e
    · exact ⟨hUside, hV'⟩
    · exact False.elim (sideSignsDisjoint U (g k t) B hB hU' hUside)

private theorem interiorIsolate :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), (∀ (k : Fin (3 : ℕ)), Function.Injective
            (g k)) → ((∀ (k : Fin (3 : ℕ)), ∀ (l : Fin (3 : ℕ)), k ≠
            l → Set.range (g k) ∩ Set.range (g l) ⊆ {q : ℝ × ℝ | (q = g k ⟨(0 : ℝ),
            (by norm_num)⟩ ∨ q = g k ⟨(1 : ℝ),
            (by norm_num)⟩) ∧ (q = g l ⟨(0 : ℝ),
            (by norm_num)⟩ ∨ q = g l ⟨(1 : ℝ),
            (by norm_num)⟩)}) → ((∀ (k : Fin 3), IsCompact (Set.range (g k))) → ((∀ (k : Fin 3),
                ∀ (S : Set (Set.Icc (0
            : Real) 1)), (IsClosed S) → (IsCompact (g k '' S))) → ((∀ (K : Set
            (Real × Real)), (IsClosed K) → (∀ (z : Real × Real), (z ∉ K) → (∃ r : Real, 0 < r ∧
            Disjoint (Metric.ball z r) K))) → (∀ (k : Fin 3), ∀ (i : Fin (s k).count), ∀ (hnxt :
                i.val + 1 < (s k).count), ∃ r : Real, 0 < r ∧ ∀ l, ∀ (a : Set.Icc (0 : Real) 1), g l
            a ∈ Metric.ball (g k ⟨(s k).time i.succ, by
              constructor
              · have hzero : 0 ≤ (s k).time 0 := by rw [(s k).start]
                exact hzero.trans ((s k).strict.monotone (Fin.zero_le _))
              · calc (s k).time i.succ ≤ (s k).time (Fin.last (s k).count) :=
                      (s k).strict.monotone (Fin.le_last _)
                    _ = 1 := (s k).finish⟩) r →
              l = k ∧ (s k).time i.castSucc < (a : Real) ∧
                (a : Real) < (s k).time
                  (⟨i.val + 2, by omega⟩ : Fin ((s k).count + 1)))))))) := by
  classical
  intro g s hi hinter compactRange compactImage avoidClosed k i hnxt
  classical
  let j : Fin (s k).count := ⟨i.val + 1, hnxt⟩
  have hjcast : j.castSucc = i.succ := by ext; rfl
  let p : Set.Icc (0 : Real) 1 := ⟨(s k).time i.succ, by
    constructor
    · have hzero : 0 ≤ (s k).time 0 := by rw [(s k).start]
      exact hzero.trans ((s k).strict.monotone (Fin.zero_le _))
    · calc (s k).time i.succ ≤ (s k).time (Fin.last (s k).count) :=
            (s k).strict.monotone (Fin.le_last _)
          _ = 1 := (s k).finish⟩
  have hlow : (s k).time i.castSucc < (p : Real) :=
    (s k).strict Fin.castSucc_lt_succ
  have hhigh : (p : Real) < (s k).time j.succ := by
    change (s k).time i.succ < (s k).time j.succ
    rw [← hjcast]
    exact (s k).strict Fin.castSucc_lt_succ
  let bad : Set (Set.Icc (0 : Real) 1) :=
    {a | (a : Real) ≤ (s k).time i.castSucc ∨
      (s k).time j.succ ≤ (a : Real)}
  have hbad : IsClosed bad := by
    have hEq : badᶜ = Subtype.val ⁻¹' Set.Ioo
        ((s k).time i.castSucc) ((s k).time j.succ) := by
      ext a
      simp [bad, Set.mem_Ioo, not_or, not_le]
    rw [← isOpen_compl_iff, hEq]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hbadpoint : g k p ∉ g k '' bad := by
    rintro ⟨a, ha, hga⟩
    have hEq : a = p := hi k (by rw [hga])
    subst a
    change (p : Real) ≤ (s k).time i.castSucc ∨
      (s k).time j.succ ≤ (p : Real) at ha
    rcases ha with ha | ha
    · exact (not_le_of_gt hlow) ha
    · exact (not_le_of_gt hhigh) ha
  let K : Set (Real × Real) :=
    ⋃ l : Fin 3, g l '' (if l = k then bad else Set.univ)
  have hKcompact : IsCompact K := by
    have hpieces : ∀ l : Fin 3, IsCompact
        (g l '' (if l = k then bad else Set.univ)) := by
      intro l
      by_cases hl : l = k
      · subst l
        simpa [bad] using compactImage k bad hbad
      · rw [ite_eq_right hl, Set.image_univ]
        exact compactRange l
    simpa [K] using (Set.toFinite (Set.univ : Set (Fin 3))).isCompact_biUnion
      (fun l _ => hpieces l)
  have hpoint : g k p ∉ K := by
    intro hz
    change g k p ∈ ⋃ l : Fin 3, g l '' (if l = k then bad else Set.univ) at hz
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hz
    by_cases hkl : l = k
    · subst l
      exact hbadpoint (by simpa using hl)
    · obtain ⟨a, ha, hga⟩ := hl
      have hq : g k p ∈ Set.range (g k) ∩ Set.range (g l) := by
        refine ⟨⟨p, rfl⟩, ?_⟩
        exact ⟨a, hga⟩
      obtain ⟨hendk, _⟩ := hinter k l (Ne.symm hkl) hq
      have hp0 : 0 < (p : Real) := lt_of_le_of_lt
        (by rw [← (s k).start]; exact (s k).strict.monotone (Fin.zero_le _)) hlow
      have hp1 : (p : Real) < 1 := lt_of_lt_of_le hhigh (by
        calc (s k).time j.succ ≤ (s k).time (Fin.last (s k).count) :=
                (s k).strict.monotone (Fin.le_last _)
          _ = 1 := (s k).finish)
      rcases hendk with hstart | hend
      · have hpEq : p = ⟨0, by norm_num⟩ := hi k (by simpa using hstart)
        have := congrArg Subtype.val hpEq
        change (p : Real) = 0 at this
        linarith
      · have hpEq : p = ⟨1, by norm_num⟩ := hi k (by simpa using hend)
        have := congrArg Subtype.val hpEq
        change (p : Real) = 1 at this
        linarith
  obtain ⟨r, hr, hdis⟩ := avoidClosed K hKcompact.isClosed (g k p) hpoint
  refine ⟨r, hr, ?_⟩
  intro l a ha
  have hnotK : g l a ∉ K := by
    intro hm
    exact (Set.disjoint_left.mp hdis ha) hm
  by_cases hl : l = k
  · subst l
    refine ⟨rfl, ?_, ?_⟩
    · by_contra h
      have hmem : g k a ∈ K := by
        change g k a ∈ ⋃ l : Fin 3, g l '' (if l = k then bad else Set.univ)
        apply Set.mem_iUnion.mpr
        refine ⟨k, ?_⟩
        simp only []
        exact ⟨a, Set.mem_ofPred_eq.mpr (Or.inl (le_of_not_gt h)), rfl⟩
      exact hnotK hmem
    · by_contra h
      have hmem : g k a ∈ K := by
        change g k a ∈ ⋃ l : Fin 3, g l '' (if l = k then bad else Set.univ)
        apply Set.mem_iUnion.mpr
        refine ⟨k, ?_⟩
        simp only []
        exact ⟨a, Set.mem_ofPred_eq.mpr (Or.inr (le_of_not_gt h)), rfl⟩
      exact hnotK hmem
  · have hmem : g l a ∈ K := by
      change g l a ∈ ⋃ q : Fin 3, g q '' (if q = k then bad else Set.univ)
      apply Set.mem_iUnion.mpr
      refine ⟨l, ?_⟩
      rw [ite_eq_right hl, Set.image_univ]
      exact ⟨a, rfl⟩
    exact (hnotK hmem).elim

private theorem sideBoolEq :
    (by
      classical
      exact
        (∀ (W : Set (Real × Real)), ∀ (z : Real × Real), ∀ (w : Real × Real), (w ≠ 0) →
            ((P3934T1LocalSide W z w true) → ((P3934T1LocalSide W z w false) → (False)))) →
            (∀ (W : Set (ℝ × ℝ)), ∀ (z : ℝ × ℝ), ∀ (w : ℝ × ℝ), w ≠ (0 : ℝ × ℝ) → ∀ (e : Bool), ∀
            (f : Bool), P3934T1LocalSide W z w e → P3934T1LocalSide W z w f → e = f) ) := by
  classical
  intro sideSignsDisjoint W z w hw e f he hf
  cases e <;> cases f
  · rfl
  · exact False.elim (sideSignsDisjoint W z w hw hf he)
  · exact False.elim (sideSignsDisjoint W z w hw he hf)
  · rfl

private theorem cornerAgree :
    (by
      classical
      exact
        ∀ (U : Set (Real × Real)), (∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v
            : Real × Real), (0 < r) → ((‖u‖ = 1) → ((‖v‖ = 1) → ((u ≠ v) → ((x ∈ frontier U) →
            ((frontier U ∩ Metric.ball x r = ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪ {p | ∃ t
            : Real, 0 ≤ t ∧ p = x + t • v}) ∩ Metric.ball x r) → (∃ e : Bool, ∀ t : Real, 0 < t →
            t < r → P3934T1LocalSide U (x + t • u) (-u) e ∧ P3934T1LocalSide U (x + t • v) v
            e ∧ P3934T1LocalSide (closure U)ᶜ (x + t • u) (-u) (!e) ∧ P3934T1LocalSide
            (closure U)ᶜ (x + t • v) v (!e)))))))) → ((∀ (W : Set (Real × Real)), ∀ (z : Real ×
            Real), ∀ (w : Real × Real), ∀ (c : Real), ∀ (e : Bool), (0 < c) →
            ((P3934T1LocalSide W z w e) → (P3934T1LocalSide W z (c • w) e))) → ((∀ (W : Set
            (Real × Real)), ∀ (z : Real × Real), ∀ (w : Real × Real), (w ≠ 0) → (∀ (e : Bool), ∀
            (f : Bool), (P3934T1LocalSide W z w e) → ((P3934T1LocalSide W z w f) → (e = f))))
            → (∀ (x : ℝ × ℝ), ∀ (B₁ : ℝ × ℝ), ∀ (B₂ : ℝ × ℝ), B₁ ≠ (0 : ℝ × ℝ) → B₂ ≠ (0 : ℝ × ℝ)
            → ∀ (a : ℝ), ∀ (b : ℝ), ∀ (R : ℝ), (0 : ℝ) < a → (0 : ℝ) < b → (0 : ℝ) < R → ∀ (e₁ :
            Bool), ∀ (e₂ : Bool), (∀ (t : ℝ), (0 : ℝ) ≤ t → t ≤ a → x - t • B₁ ∈ frontier U) → (∀
            (t : ℝ), (0 : ℝ) ≤ t → t ≤ b → x + t • B₂ ∈ frontier U) → (∀ (t : ℝ), (0 : ℝ) < t → t
            < a → P3934T1LocalSide U (x - t • B₁) B₁ e₁) → (∀ (t : ℝ), (0 : ℝ) < t → t < b →
            P3934T1LocalSide U (x + t • B₂) B₂ e₂) → (∀ (t₁ : ℝ), ∀ (t₂ : ℝ), (0 : ℝ) < t₁ → t₁
            < a → (0 : ℝ) < t₂ → t₂ < b → x - t₁ • B₁ ≠ x + t₂ • B₂) → (∀ q ∈ frontier U, q ∈
            Metric.ball x R → (∃ (t : ℝ), (0 : ℝ) ≤ t ∧ t ≤ a ∧ q = x - t • B₁) ∨ ∃ (t : ℝ), (0 :
            ℝ) ≤ t ∧ t ≤ b ∧ q = x + t • B₂) → e₁ = e₂))) ) := by
  classical
  intro U bend scaleLocalSide sideBoolEq x B₁ B₂ hB₁ hB₂ a b R ha hb hR e₁ e₂ back forward
      backSide forwardSide apart near
  let n₁ := ‖B₁‖
  let n₂ := ‖B₂‖
  have hn₁ : 0 < n₁ := norm_pos_iff.mpr hB₁
  have hn₂ : 0 < n₂ := norm_pos_iff.mpr hB₂
  let u := -(n₁⁻¹ • B₁)
  let v := n₂⁻¹ • B₂
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn₁)]
    exact inv_mul_cancel₀ hn₁.ne'
  have hv' : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn₂)]
    exact inv_mul_cancel₀ hn₂.ne'
  have move₁ (t : Real) : x + t • u = x - (t / n₁) • B₁ := by
    simp [u, div_eq_mul_inv, smul_smul, sub_eq_add_neg]
  have move₂ (t : Real) : x + t • v = x + (t / n₂) • B₂ := by
    simp [v, div_eq_mul_inv, smul_smul]
  have decomp₁ : n₁ • (-u) = B₁ := by
    simp [u, smul_smul, hn₁.ne']
  have decomp₂ : n₂ • v = B₂ := by
    simp [v, smul_smul, hn₂.ne']
  let r := min R (min (a * n₁) (b * n₂))
  have hr : 0 < r := lt_min hR (lt_min (mul_pos ha hn₁) (mul_pos hb hn₂))
  have hrR : r ≤ R := min_le_left _ _
  have hra : r ≤ a * n₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrb : r ≤ b * n₂ := (min_le_right _ _).trans (min_le_right _ _)
  have bounds₁ (t : Real) (ht : 0 < t) (htr : t < r) :
      0 < t / n₁ ∧ t / n₁ < a :=
    ⟨div_pos ht hn₁, (div_lt_iff₀ hn₁).2 (htr.trans_le hra)⟩
  have bounds₂ (t : Real) (ht : 0 < t) (htr : t < r) :
      0 < t / n₂ ∧ t / n₂ < b :=
    ⟨div_pos ht hn₂, (div_lt_iff₀ hn₂).2 (htr.trans_le hrb)⟩
  have hhalf : 0 < r / 2 ∧ r / 2 < r := ⟨by positivity, by linarith only [hr]⟩
  have huv : u ≠ v := by
    intro h
    have h₁ := bounds₁ (r / 2) hhalf.1 hhalf.2
    have h₂ := bounds₂ (r / 2) hhalf.1 hhalf.2
    apply apart (r / 2 / n₁) (r / 2 / n₂) h₁.1 h₁.2 h₂.1 h₂.2
    rw [← move₁, ← move₂, h]
  have chart : frontier U ∩ Metric.ball x r =
      ({q | ∃ t : Real, 0 ≤ t ∧ q = x + t • u} ∪
        {q | ∃ t : Real, 0 ≤ t ∧ q = x + t • v}) ∩ Metric.ball x r := by
    ext q
    constructor
    · rintro ⟨hq, hball⟩
      refine ⟨?_, hball⟩
      rcases near q hq (Metric.ball_subset_ball hrR hball) with
        ⟨t, ht, _, heq⟩ | ⟨t, ht, _, heq⟩
      · left
        refine ⟨t * n₁, mul_nonneg ht hn₁.le, ?_⟩
        rw [move₁, mul_div_cancel_right₀ t hn₁.ne']
        exact heq
      · right
        refine ⟨t * n₂, mul_nonneg ht hn₂.le, ?_⟩
        rw [move₂, mul_div_cancel_right₀ t hn₂.ne']
        exact heq
    · rintro ⟨(⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩), hball⟩
      · have htr : t < r := by
          simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg ht, hu, mul_one] using hball
        refine ⟨?_, hball⟩
        rw [move₁]
        exact back (t / n₁) (div_nonneg ht hn₁.le)
          ((div_lt_iff₀ hn₁).2 (htr.trans_le hra)).le
      · have htr : t < r := by
          simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg ht, hv', mul_one] using hball
        refine ⟨?_, hball⟩
        rw [move₂]
        exact forward (t / n₂) (div_nonneg ht hn₂.le)
          ((div_lt_iff₀ hn₂).2 (htr.trans_le hrb)).le
  have hx : x ∈ frontier U := by simpa using back 0 le_rfl ha.le
  obtain ⟨e, hs⟩ := bend x r u v hr hu hv' huv hx chart
  have hc := hs (r / 2) hhalf.1 hhalf.2
  have h₁ := bounds₁ (r / 2) hhalf.1 hhalf.2
  have h₂ := bounds₂ (r / 2) hhalf.1 hhalf.2
  have hp₁ : P3934T1LocalSide U (x + (r / 2) • u) B₁ e₁ := by
    rw [move₁]
    exact backSide _ h₁.1 h₁.2
  have hp₂ : P3934T1LocalSide U (x + (r / 2) • v) B₂ e₂ := by
    rw [move₂]
    exact forwardSide _ h₂.1 h₂.2
  have hc₁ := scaleLocalSide U (x + (r / 2) • u) (-u) n₁ e hn₁ hc.1
  have hc₂ := scaleLocalSide U (x + (r / 2) • v) v n₂ e hn₂ hc.2.1
  rw [decomp₁] at hc₁
  rw [decomp₂] at hc₂
  exact (sideBoolEq U _ B₁ hB₁ e₁ e hp₁ hc₁).trans
    (sideBoolEq U _ B₂ hB₂ e₂ e hp₂ hc₂).symm

private theorem pieceSide :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (U : Set (Real × Real)), (∀ (k : Fin 3),
            ∀ (i : Fin (s k).count), ∃ A B : Real × Real, B ≠ 0 ∧ ∀ t : Set.Icc (0 : Real) 1, (s
            k).time i.castSucc ≤ (t : Real) → (t : Real) ≤ (s k).time i.succ → g k t = A + (t :
            Real) • B) → ((∀ (k : Fin 3), ∀ (i : Fin (s k).count), ∀ (A : Real × Real), ∀ (B :
            Real × Real), (B ≠ 0) → ((∀ a : Set.Icc (0 : Real) 1, (s k).time i.castSucc ≤ (a :
            Real) → (a : Real) ≤ (s k).time i.succ → g k a = A + (a : Real) • B) → (∃ e : Bool, ∀
            t : Set.Icc (0 : Real) 1, (s k).time i.castSucc < (t : Real) → (t : Real) < (s
            k).time i.succ → P3934T1LocalSide U (g k t) B e ∧ P3934T1LocalSide (closure U)ᶜ
            (g k t) B (!e)))) → (∀ (k : Fin (3 : ℕ)), ∀ (i : Fin (s k).count), ∃ (d : (ℝ × ℝ) ×
            (ℝ × ℝ) × Bool), d.2.1 ≠ (0 : ℝ × ℝ) ∧ (∀ (a : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)),
            (s k).time i.castSucc ≤ (↑a : ℝ) → (↑a : ℝ) ≤ (s k).time i.succ → g k a = d.1 + (↑a :
            ℝ) • d.2.1) ∧ ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s k).time i.castSucc <
            (↑t : ℝ) → (↑t : ℝ) < (s k).time i.succ → P3934T1LocalSide U (g k t) d.2.1 d.2.2 ∧
            P3934T1LocalSide (closure U)ᶜ (g k t) d.2.1 !d.2.2)) ) := by
  classical
  intro g s U pieceData pieceConstant k i
  obtain ⟨A, B, hB, hline⟩ := pieceData k i
  obtain ⟨e, hs⟩ := pieceConstant k i A B hB hline
  exact ⟨(A, (B, e)), hB, hline, hs⟩

private theorem chosenSpec :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (U : Set (Real × Real)), ∀ (pieceSide :
            ∀ (k : Fin 3), ∀ (i : Fin (s k).count), ∃ d : (Real × Real) × ((Real × Real) × Bool),
            d.2.1 ≠ 0 ∧ (∀ a : Set.Icc (0 : Real) 1, (s k).time i.castSucc ≤ (a : Real) → (a :
            Real) ≤ (s k).time i.succ → g k a = d.1 + (a : Real) • d.2.1) ∧ (∀ t : Set.Icc (0 :
            Real) 1, (s k).time i.castSucc < (t : Real) → (t : Real) < (s k).time i.succ →
            P3934T1LocalSide U (g k t) d.2.1 d.2.2 ∧ P3934T1LocalSide (closure U)ᶜ (g k t)
            d.2.1 (!d.2.2))),
        let sideInfo (k : Fin 3) (i : Fin (s k).count) := Classical.choose (pieceSide k i)
        let chosenA (k : Fin 3) (i : Fin (s k).count) := (sideInfo k i).1
        let chosenAB (k : Fin 3) (i : Fin (s k).count) := (sideInfo k i).2.1
        let pieceSign (k : Fin 3) (i : Fin (s k).count) : Bool := (sideInfo k i).2.2
        ∀ (k : Fin (3 : ℕ)), ∀ (i : Fin (s k).count), chosenAB k i ≠ (0 : ℝ × ℝ) ∧ (∀ (a :
            (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s k).time i.castSucc ≤ (↑a : ℝ) → (↑a : ℝ) ≤
            (s k).time i.succ → g k a = chosenA k i + (↑a : ℝ) • chosenAB k i) ∧ ∀ (t :
            (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s k).time i.castSucc < (↑t : ℝ) → (↑t : ℝ) <
            (s k).time i.succ → P3934T1LocalSide U (g k t) (chosenAB k i) (pieceSign k i) ∧
            P3934T1LocalSide (closure U)ᶜ (g k t) (chosenAB k i) !pieceSign k i ) := by
  classical
  intro g s U pieceSide sideInfo chosenA chosenAB pieceSign k i
  exact Classical.choose_spec (pieceSide k i)

private theorem vertexLabels :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (U : Set (Real × Real)), (frontier U = ⋃
            (k : Fin (3 : ℕ)), Set.range (g k)) → ((∀ (x : Real × Real), ∀ (B₁ : Real × Real), ∀
            (B₂ : Real × Real), (B₁ ≠ 0) → ((B₂ ≠ 0) → (∀ (a : Real), ∀ (b : Real), ∀ (R : Real),
            (0 < a) → ((0 < b) → ((0 < R) → (∀ (e₁ : Bool), ∀ (e₂ : Bool), (∀ t : Real, 0 ≤ t → t
            ≤ a → x - t • B₁ ∈ frontier U) → ((∀ t : Real, 0 ≤ t → t ≤ b → x + t • B₂ ∈ frontier
            U) → ((∀ t : Real, 0 < t → t < a → P3934T1LocalSide U (x - t • B₁) B₁ e₁) → ((∀ t :
            Real, 0 < t → t < b → P3934T1LocalSide U (x + t • B₂) B₂ e₂) → ((∀ t₁ t₂ : Real, 0
            < t₁ → t₁ < a → 0 < t₂ → t₂ < b → x - t₁ • B₁ ≠ x + t₂ • B₂) → ((∀ q ∈ frontier U, q
            ∈ Metric.ball x R → (∃ t : Real, 0 ≤ t ∧ t ≤ a ∧ q = x - t • B₁) ∨ (∃ t : Real, 0 ≤ t
            ∧ t ≤ b ∧ q = x + t • B₂)) → (e₁ = e₂)))))))))))) → (∀ (pieceSide : ∀ (k : Fin 3), ∀
            (i : Fin (s k).count), ∃ d : (Real × Real) × ((Real × Real) × Bool), d.2.1 ≠ 0 ∧ (∀ a
            : Set.Icc (0 : Real) 1, (s k).time i.castSucc ≤ (a : Real) → (a : Real) ≤ (s k).time
            i.succ → g k a = d.1 + (a : Real) • d.2.1) ∧ (∀ t : Set.Icc (0 : Real) 1, (s k).time
            i.castSucc < (t : Real) → (t : Real) < (s k).time i.succ → P3934T1LocalSide U (g k
            t) d.2.1 d.2.2 ∧ P3934T1LocalSide (closure U)ᶜ (g k t) d.2.1 (!d.2.2))),
        let sideInfo (k : Fin 3) (i : Fin (s k).count) := Classical.choose (pieceSide k i)
        let chosenA (k : Fin 3) (i : Fin (s k).count) := (sideInfo k i).1
        let chosenAB (k : Fin 3) (i : Fin (s k).count) := (sideInfo k i).2.1
        let pieceSign (k : Fin 3) (i : Fin (s k).count) : Bool := (sideInfo k i).2.2
        (∀ (k : Fin 3), ∀ (i : Fin (s k).count), chosenAB k i ≠ 0 ∧ (∀ a : Set.Icc (0 : Real) 1,
            (s k).time i.castSucc ≤ (a : Real) → (a : Real) ≤ (s k).time i.succ → g k a = chosenA
            k i + (a : Real) • chosenAB k i) ∧ (∀ t : Set.Icc (0 : Real) 1, (s k).time i.castSucc
            < (t : Real) → (t : Real) < (s k).time i.succ → P3934T1LocalSide U (g k t)
            (chosenAB k i) (pieceSign k i) ∧ P3934T1LocalSide (closure U)ᶜ (g k t) (chosenAB k
            i) (!pieceSign k i))) → (∀ (k : Fin (3 : ℕ)), ∀ (l : Fin (3 : ℕ)), ∀ (i : Fin (s
            k).count), ∀ (j : Fin (s l).count), ∀ (p : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), ∀ (q
            : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s k).time i.succ = (↑p : ℝ) → (s l).time
            j.castSucc = (↑q : ℝ) → g k p = g l q → (∀ (t₁ : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) :
            Type)), ∀ (t₂ : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (s k).time i.castSucc < (↑t₁ :
            ℝ) → (↑t₁ : ℝ) < (↑p : ℝ) → (↑q : ℝ) < (↑t₂ : ℝ) → (↑t₂ : ℝ) < (s l).time j.succ → g
            k t₁ ≠ g l t₂) → ∀ (R : ℝ), (0 : ℝ) < R → (∀ (m : Fin (3 : ℕ)), ∀ (t : (↑(Set.Icc (0
            : ℝ) (1 : ℝ)) : Type)), g m t ∈ Metric.ball (g k p) R → m = k ∧ (s k).time i.castSucc
            ≤ (↑t : ℝ) ∧ (↑t : ℝ) ≤ (↑p : ℝ) ∨ m = l ∧ (↑q : ℝ) ≤ (↑t : ℝ) ∧ (↑t : ℝ) ≤ (s
            l).time j.succ) → pieceSign k i = pieceSign l j))) ) := by
  classical
  intro g s U hf cornerAgree pieceSide sideInfo chosenA chosenAB pieceSign chosenSpec k l i j p q
      hp hq hcenter apart R hR near
  let a := (p : Real) - (s k).time i.castSucc
  let b := (s l).time j.succ - (q : Real)
  have ha : 0 < a := sub_pos.mpr (by rw [← hp]; exact (s k).strict Fin.castSucc_lt_succ)
  have hb : 0 < b := sub_pos.mpr (by rw [← hq]; exact (s l).strict Fin.castSucc_lt_succ)
  have hlo : 0 ≤ (s k).time i.castSucc := by
    rw [← (s k).start]
    exact (s k).strict.monotone (Fin.zero_le _)
  have hhi : (s l).time j.succ ≤ 1 := by
    rw [← (s l).finish]
    exact (s l).strict.monotone (Fin.le_last _)
  let left (t : Real) (ht : 0 ≤ t) (hta : t ≤ a) : Set.Icc (0 : Real) 1 :=
    ⟨(p : Real) - t, by constructor <;> dsimp [a] at hta <;> linarith only [hta, ht, hlo, p.2.2]⟩
  let right (t : Real) (ht : 0 ≤ t) (htb : t ≤ b) : Set.Icc (0 : Real) 1 :=
    ⟨(q : Real) + t, by constructor <;> dsimp [b] at htb <;> linarith only [htb, ht, hhi, q.2.1]⟩
  have leftBounds (t : Real) (ht : 0 ≤ t) (hta : t ≤ a) :
      (s k).time i.castSucc ≤ (left t ht hta : Real) ∧
      (left t ht hta : Real) ≤ (p : Real) := by
    dsimp [left, a] at *
    constructor <;> linarith only [hta, ht]
  have rightBounds (t : Real) (ht : 0 ≤ t) (htb : t ≤ b) :
      (q : Real) ≤ (right t ht htb : Real) ∧
      (right t ht htb : Real) ≤ (s l).time j.succ := by
    dsimp [right, b] at *
    constructor <;> linarith only [htb, ht]
  have center₁ := (chosenSpec k i).2.1 p (by linarith only [ha]) (by rw [hp])
  have center₂ := (chosenSpec l j).2.1 q (by rw [hq]) (by linarith only [hb])
  have move₁ (t : Real) (ht : 0 ≤ t) (hta : t ≤ a) :
      g k (left t ht hta) = g k p - t • chosenAB k i := by
    rw [(chosenSpec k i).2.1 _ (leftBounds t ht hta).1
      (by rw [hp]; exact (leftBounds t ht hta).2), center₁]
    dsimp [left]
    module
  have move₂ (t : Real) (ht : 0 ≤ t) (htb : t ≤ b) :
      g l (right t ht htb) = g k p + t • chosenAB l j := by
    rw [(chosenSpec l j).2.1 _ (by rw [hq]; exact (rightBounds t ht htb).1)
      (rightBounds t ht htb).2, hcenter, center₂]
    dsimp [right]
    module
  apply cornerAgree (g k p) (chosenAB k i) (chosenAB l j)
    (chosenSpec k i).1 (chosenSpec l j).1 a b R ha hb hR
    (pieceSign k i) (pieceSign l j)
  · intro t ht hta
    rw [← move₁ t ht hta, hf]
    exact Set.mem_iUnion.mpr ⟨k, ⟨left t ht hta, rfl⟩⟩
  · intro t ht htb
    rw [← move₂ t ht htb, hf]
    exact Set.mem_iUnion.mpr ⟨l, ⟨right t ht htb, rfl⟩⟩
  · intro t ht hta
    rw [← move₁ t ht.le hta.le]
    apply ((chosenSpec k i).2.2 _ ?_ ?_).1
    · change (s k).time i.castSucc < (p : Real) - t
      dsimp [a] at hta
      linarith only [hta]
    · rw [hp]
      change (p : Real) - t < (p : Real)
      linarith only [ht]
  · intro t ht htb
    rw [← move₂ t ht.le htb.le]
    apply ((chosenSpec l j).2.2 _ ?_ ?_).1
    · rw [hq]
      change (q : Real) < (q : Real) + t
      linarith only [ht]
    · change (q : Real) + t < (s l).time j.succ
      dsimp [b] at htb
      linarith only [htb]
  · intro t₁ t₂ ht₁ ht₁a ht₂ ht₂b
    rw [← move₁ t₁ ht₁.le ht₁a.le, ← move₂ t₂ ht₂.le ht₂b.le]
    apply apart
    · change (s k).time i.castSucc < (p : Real) - t₁
      dsimp [a] at ht₁a
      linarith only [ht₁a]
    · change (p : Real) - t₁ < (p : Real)
      linarith only [ht₁]
    · change (q : Real) < (q : Real) + t₂
      linarith only [ht₂]
    · change (q : Real) + t₂ < (s l).time j.succ
      dsimp [b] at ht₂b
      linarith only [ht₂b]
  · intro z hz hzball
    rw [hf] at hz
    obtain ⟨m, t, hmt⟩ := Set.mem_iUnion.mp hz
    have hball : g m t ∈ Metric.ball (g k p) R := by rw [hmt]; exact hzball
    rcases near m t hball with ⟨hm, hlo, hhi⟩ | ⟨hm, hlo, hhi⟩
    · subst m
      left
      refine ⟨(p : Real) - (t : Real), sub_nonneg.mpr hhi, ?_, ?_⟩
      · dsimp [a]
        linarith only [hlo]
      · rw [← hmt, (chosenSpec k i).2.1 t hlo (by rw [hp]; exact hhi), center₁]
        module
    · subst m
      right
      refine ⟨(t : Real) - (q : Real), sub_nonneg.mpr hlo, ?_, ?_⟩
      · dsimp [b]
        linarith only [hhi]
      · rw [← hmt, (chosenSpec l j).2.1 t (by rw [hq]; exact hlo) hhi,
          hcenter, center₂]
        module

private theorem interiorSignAgree :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), (∀ (k : Fin (3 : ℕ)), Function.Injective
            (g k)) → (∀ (U : Set (Real × Real)), (∀ (k : Fin 3), ∀ (i : Fin (s
            k).count), ∀ (hnxt : i.val + 1 < (s k).count), ∃ r : Real, 0 < r ∧ ∀ l, ∀ (a :
                Set.Icc (0 : Real) 1), g l a ∈ Metric.ball (g k ⟨(s k).time i.succ, by
              constructor
              · have hzero : 0 ≤ (s k).time 0 := by rw [(s k).start]
                exact hzero.trans ((s k).strict.monotone (Fin.zero_le _))
              · calc (s k).time i.succ ≤ (s k).time (Fin.last (s k).count) :=
                      (s k).strict.monotone (Fin.le_last _)
                    _ = 1 := (s k).finish⟩) r →
              l = k ∧ (s k).time i.castSucc < (a : Real) ∧
                (a : Real) < (s k).time
                  (⟨i.val + 2, by omega⟩ : Fin ((s k).count + 1))) → (∀ (pieceSide : ∀ (k : Fin
                      3), ∀ (i : Fin (s k).count), ∃ d : (Real × Real) × ((Real × Real) × Bool),
                      d.2.1 ≠ 0 ∧ (∀ a : Set.Icc (0 : Real) 1, (s k).time i.castSucc ≤ (a : Real)
                      → (a : Real) ≤ (s k).time i.succ → g k a = d.1 + (a : Real) • d.2.1) ∧ (∀ t
                      : Set.Icc (0 : Real) 1, (s k).time i.castSucc < (t : Real) → (t : Real) <
                      (s k).time i.succ → P3934T1LocalSide U (g k t) d.2.1 d.2.2 ∧
                      P3934T1LocalSide (closure U)ᶜ (g k t) d.2.1 (!d.2.2))),
        let sideInfo (k : Fin 3) (i : Fin (s k).count) := Classical.choose (pieceSide k i)
        let pieceSign (k : Fin 3) (i : Fin (s k).count) : Bool := (sideInfo k i).2.2
        (∀ (k : Fin 3), ∀ (l : Fin 3), ∀ (i : Fin (s k).count), ∀ (j : Fin (s l).count), ∀ (p :
            Set.Icc (0 : Real) 1), ∀ (q : Set.Icc (0 : Real) 1), ((s k).time i.succ = (p : Real))
            → (((s l).time j.castSucc = (q : Real)) → ((g k p = g l q) → ((∀ t₁ t₂ : Set.Icc (0 :
            Real) 1, (s k).time i.castSucc < (t₁ : Real) → (t₁ : Real) < (p : Real) → (q : Real)
            < (t₂ : Real) → (t₂ : Real) < (s l).time j.succ → g k t₁ ≠ g l t₂) → (∀ (R : Real),
                (0 < R) → ((∀ m, ∀ (t : Set.Icc (0 : Real) 1), g m t ∈ Metric.ball (g k p) R → (m
                = k
            ∧ (s k).time i.castSucc ≤ (t : Real) ∧ (t : Real) ≤ (p : Real)) ∨ (m = l ∧ (q : Real)
            ≤ (t : Real) ∧ (t : Real) ≤ (s l).time j.succ)) → (pieceSign k i = pieceSign l
            j))))))) → (∀ (k : Fin (3 : ℕ)), ∀ (i : Fin (s k).count), ∀ (hnxt : (↑i : ℕ) + (1 :
            ℕ) < (s k).count), pieceSign k i = pieceSign k ⟨(↑i : ℕ) + (1 : ℕ), hnxt⟩)))) := by
  classical
  intro g s hi U interiorIsolate pieceSide sideInfo pieceSign vertexLabels k i hnxt
  let j : Fin (s k).count := ⟨i.val + 1, hnxt⟩
  have hj : j.castSucc = i.succ := by ext; rfl
  have hj₂ : j.succ = (⟨i.val + 2, by omega⟩ : Fin ((s k).count + 1)) := by
    ext
    change i.val + 1 + 1 = i.val + 2
    omega
  let p : Set.Icc (0 : Real) 1 := ⟨(s k).time i.succ, by
    constructor
    · rw [← (s k).start]
      exact (s k).strict.monotone (Fin.zero_le _)
    · rw [← (s k).finish]
      exact (s k).strict.monotone (Fin.le_last _)⟩
  obtain ⟨R, hR, hiso⟩ := interiorIsolate k i hnxt
  apply vertexLabels k k i j p p rfl (by rw [hj]) rfl ?_ R hR ?_
  · intro t₁ t₂ _ ht₁ ht₂ _ h
    have heq := congrArg Subtype.val (hi k h)
    linarith only [ht₁, ht₂, heq]
  · intro m t ht
    obtain ⟨rfl, hlo, hhi⟩ := hiso m t ht
    by_cases htp : (t : Real) ≤ (p : Real)
    · exact Or.inl ⟨rfl, hlo.le, htp⟩
    · exact Or.inr ⟨rfl, (le_of_not_ge htp), by simpa [hj₂] using hhi.le⟩

private theorem signChain :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (U : Set (Real × Real)), ∀ (pieceSide :
            ∀ (k : Fin 3), ∀ (i : Fin (s k).count), ∃ d : (Real × Real) × ((Real × Real) × Bool),
            d.2.1 ≠ 0 ∧ (∀ a : Set.Icc (0 : Real) 1, (s k).time i.castSucc ≤ (a : Real) → (a :
            Real) ≤ (s k).time i.succ → g k a = d.1 + (a : Real) • d.2.1) ∧ (∀ t : Set.Icc (0 :
            Real) 1, (s k).time i.castSucc < (t : Real) → (t : Real) < (s k).time i.succ →
            P3934T1LocalSide U (g k t) d.2.1 d.2.2 ∧ P3934T1LocalSide (closure U)ᶜ (g k t)
            d.2.1 (!d.2.2))),
        let sideInfo (k : Fin 3) (i : Fin (s k).count) := Classical.choose (pieceSide k i)
        let pieceSign (k : Fin 3) (i : Fin (s k).count) : Bool := (sideInfo k i).2.2
        (∀ (k : Fin 3), ∀ (i : Fin (s k).count), ∀ (hnxt : i.val + 1 < (s k).count), pieceSign k
            i = pieceSign k ⟨i.val + 1, hnxt⟩) → (∀ (k : Fin 3), ∀ n, ∀ (hn : n < (s k).count),
            pieceSign k ⟨n, hn⟩ = pieceSign k ⟨0, (s k).positive⟩) ) := by
  classical
  intro g s U pieceSide sideInfo pieceSign interiorSignAgree k n
  induction n with
  | zero =>
      intro _
      rfl
  | succ n ih =>
      intro hn
      have hn' : n < (s k).count := by omega
      let i : Fin (s k).count := ⟨n, hn'⟩
      let j : Fin (s k).count := ⟨n + 1, hn⟩
      have hij : i.val + 1 < (s k).count := by simpa [i] using hn
      have hji : j = ⟨i.val + 1, hij⟩ := by apply Fin.ext; rfl
      calc
        pieceSign k j = pieceSign k i := by
          rw [hji]
          exact (interiorSignAgree k i hij).symm
        _ = pieceSign k ⟨0, (s k).positive⟩ := ih hn'

private theorem isolateNeighborhood :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), (∀ (k : Fin 3), ∀ (S : Set (Set.Icc
            (0 : Real) 1)), (IsClosed S) → (IsCompact (g k '' S))) → ((∀ (K : Set (Real × Real)),
            (IsClosed K) → (∀ (z : Real × Real), (z ∉ K) → (∃ r : Real, 0 < r ∧ Disjoint
            (Metric.ball z r) K))) → (∀ (x : ℝ × ℝ), ∀ (O : Fin (3 : ℕ) → Set (↑(Set.Icc (0 : ℝ)
            (1 : ℝ)) : Type)), (∀ (k : Fin (3 : ℕ)), IsOpen (O k)) → (∀ (k : Fin (3 : ℕ)), ∀ (t :
            (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), g k t = x → t ∈ O k) → ∃ (R : ℝ), (0 : ℝ) < R ∧
            ∀ (k : Fin (3 : ℕ)), ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), g k t ∈ Metric.ball
            x R → t ∈ O k)) ) := by
  classical
  intro g compactImage avoidClosed x O hO hx
  let K := ⋃ k : Fin 3, g k '' (O k)ᶜ
  have hK : IsCompact K := by
    simpa [K] using (Set.toFinite (Set.univ : Set (Fin 3))).isCompact_biUnion
      (fun k _ => compactImage k (O k)ᶜ (hO k).isClosed_compl)
  have hxK : x ∉ K := by
    intro h
    obtain ⟨k, t, ht, hgt⟩ := Set.mem_iUnion.mp h
    exact ht (hx k t hgt)
  obtain ⟨R, hR, hdis⟩ := avoidClosed K hK.isClosed x hxK
  refine ⟨R, hR, ?_⟩
  intro k t ht
  by_contra h
  have hm : g k t ∈ K := Set.mem_iUnion.mpr ⟨k, ⟨t, h, rfl⟩⟩
  exact Set.disjoint_left.mp hdis ht hm

private theorem joinPreimage :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), (∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)) → ((∀ (k : Fin (3 : ℕ)), g k ⟨(1 : ℝ),
            (by norm_num)⟩ = g (k + (1 : Fin (3 : ℕ))) ⟨(0 : ℝ),
            (by norm_num)⟩) → ((Function.Injective fun (k : Fin
            (3 : ℕ)) => g k ⟨(0 : ℝ), (by norm_num)⟩) → ((∀ (k : Fin (3 : ℕ)), ∀ (l : Fin (3 :
                ℕ)), k ≠ l → Set.range (g k) ∩ Set.range (g l) ⊆
            {q : ℝ × ℝ | (q = g k ⟨(0 : ℝ), (by norm_num)⟩ ∨ q = g k
            ⟨(1 : ℝ), (by norm_num)⟩) ∧ (q = g l ⟨(0 : ℝ),
            (by norm_num)⟩ ∨ q = g l ⟨(1 : ℝ),
            (by norm_num)⟩)}) → (∀ (k : Fin 3), ∀ (l : Fin 3), ∀ (t : Set.Icc (0 : Real) 1), (g l
                t = g k ⟨1, by norm_num⟩) → ((l = k ∧ t = ⟨1,
            by norm_num⟩) ∨
          (l = k + 1 ∧ t = ⟨0, by norm_num⟩))))))) := by
  classical
  intro g hi hjoin hv hinter k l t ht
  by_cases hl : l = k
  · subst l
    exact Or.inl ⟨rfl, hi k ht⟩
  have hm : g k ⟨1, by norm_num⟩ ∈ Set.range (g k) ∩ Set.range (g l) :=
    ⟨⟨⟨1, by norm_num⟩, rfl⟩, ⟨t, ht⟩⟩
  obtain ⟨_, hend⟩ := hinter k l (Ne.symm hl) hm
  rcases hend with hstart | hfinish
  · have hindex : l = k + 1 := hv (hstart.symm.trans (hjoin k))
    exact Or.inr ⟨hindex, hi l (ht.trans hstart)⟩
  · have hindex : l + 1 = k + 1 :=
      hv ((hjoin l).symm.trans (hfinish.symm.trans (hjoin k)))
    exact False.elim (hl (add_right_cancel hindex))

private theorem joinSignAgree :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (hi : ∀ (k : Fin (3 : ℕ)),
            Function.Injective (g k)), ∀ (hjoin : ∀ (k : Fin (3 : ℕ)), g k ⟨(1 : ℝ),
            (by norm_num)⟩ = g (k + (1 : Fin (3 : ℕ))) ⟨(0 : ℝ),
            (by norm_num)⟩), ∀ (hinter : ∀ (k : Fin (3 : ℕ)), ∀ (l : Fin (3 : ℕ)), k ≠ l →
                Set.range (g k) ∩ Set.range (g l) ⊆ {q : ℝ × ℝ | (q = g k ⟨(0 :
            ℝ), (by norm_num)⟩ ∨ q = g k ⟨(1 : ℝ),
            (by norm_num)⟩) ∧ (q = g l ⟨(0 : ℝ),
            (by norm_num)⟩ ∨ q = g l ⟨(1 : ℝ),
            (by norm_num)⟩)}), ∀ (U : Set (Real × Real)), ∀ (pieceSide : ∀ (k : Fin 3), ∀ (i :
                Fin (s k).count), ∃ d : (Real × Real) × ((Real ×
            Real) × Bool), d.2.1 ≠ 0 ∧ (∀ a : Set.Icc (0 : Real) 1, (s k).time i.castSucc ≤ (a :
            Real) → (a : Real) ≤ (s k).time i.succ → g k a = d.1 + (a : Real) • d.2.1) ∧ (∀ t :
            Set.Icc (0 : Real) 1, (s k).time i.castSucc < (t : Real) → (t : Real) < (s k).time
            i.succ → P3934T1LocalSide U (g k t) d.2.1 d.2.2 ∧ P3934T1LocalSide (closure U)ᶜ
            (g k t) d.2.1 (!d.2.2))),
        let sideInfo (k : Fin 3) (i : Fin (s k).count) := Classical.choose (pieceSide k i)
        let pieceSign (k : Fin 3) (i : Fin (s k).count) : Bool := (sideInfo k i).2.2
        ∀ (vertexLabels : ∀ (k : Fin 3), ∀ (l : Fin 3), ∀ (i : Fin (s k).count), ∀ (j : Fin (s
            l).count), ∀ (p : Set.Icc (0 : Real) 1), ∀ (q : Set.Icc (0 : Real) 1), ((s k).time
            i.succ = (p : Real)) → (((s l).time j.castSucc = (q : Real)) → ((g k p = g l q) → ((∀
            t₁ t₂ : Set.Icc (0 : Real) 1, (s k).time i.castSucc < (t₁ : Real) → (t₁ : Real) < (p
            : Real) → (q : Real) < (t₂ : Real) → (t₂ : Real) < (s l).time j.succ → g k t₁ ≠ g l
            t₂) → (∀ (R : Real), (0 < R) → ((∀ m, ∀ (t : Set.Icc (0 : Real) 1), g m t ∈
            Metric.ball (g k p) R → (m = k ∧ (s k).time i.castSucc ≤ (t : Real) ∧ (t : Real) ≤ (p
            : Real)) ∨ (m = l ∧ (q : Real) ≤ (t : Real) ∧ (t : Real) ≤ (s l).time j.succ)) →
            (pieceSign k i = pieceSign l j))))))), ∀ (isolateNeighborhood : ∀ (x : Real × Real),
                ∀ (O : Fin 3 → Set (Set.Icc (0 : Real) 1)), (∀ k, IsOpen (O k)) → ((∀ k, ∀ t, g k
                t =
            x → t ∈ O k) → (∃ R : Real, 0 < R ∧ ∀ k, ∀ t, g k t ∈ Metric.ball x R → t ∈ O k))), ∀
                (next_ne : ∀ (k : Fin 3), k + 1 ≠ k), ∀ (joinPreimage : ∀ (k : Fin 3), ∀ (l : Fin
                3), ∀ (t : Set.Icc (0 : Real) 1), (g l t = g k ⟨1, by norm_num⟩) → ((l = k ∧ t = ⟨1,
            by norm_num⟩) ∨
          (l = k + 1 ∧ t = ⟨0, by norm_num⟩))),
        let first (k : Fin 3) : Fin (s k).count := ⟨0, (s k).positive⟩
        let last (k : Fin 3) : Fin (s k).count :=
          ⟨(s k).count - 1, by have := (s k).positive; omega⟩
        ∀ (k : Fin (3 : ℕ)), pieceSign k (last k) = pieceSign (k + (1 : Fin (3 : ℕ))) (first (k +
            (1 : Fin (3 : ℕ))))) := by
  classical
  intro g s hi hjoin hinter U pieceSide sideInfo pieceSign vertexLabels isolateNeighborhood
      next_ne joinPreimage first last k
  let i := last k
  let j := first (k + 1)
  have hiLast : i.succ = Fin.last (s k).count := by
    apply Fin.ext
    change (s k).count - 1 + 1 = (s k).count
    have := (s k).positive
    omega
  have hjZero : j.castSucc = (0 : Fin ((s (k + 1)).count + 1)) := rfl
  have hp : (s k).time i.succ = 1 := by rw [hiLast, (s k).finish]
  have hq : (s (k + 1)).time j.castSucc = 0 := by rw [hjZero, (s (k + 1)).start]
  have hgaplo : (s k).time i.castSucc < 1 := by
    rw [← hp]
    exact (s k).strict Fin.castSucc_lt_succ
  have hgaphigh : 0 < (s (k + 1)).time j.succ := by
    rw [← hq]
    exact (s (k + 1)).strict Fin.castSucc_lt_succ
  let O : Fin 3 → Set (Set.Icc (0 : Real) 1) := fun l =>
    if l = k then {t | (s k).time i.castSucc < (t : Real)}
    else if l = k + 1 then {t | (t : Real) < (s (k + 1)).time j.succ}
    else ∅
  have hO (l : Fin 3) : IsOpen (O l) := by
    dsimp [O]
    split_ifs
    · exact isOpen_Ioi.preimage continuous_subtype_val
    · exact isOpen_Iio.preimage continuous_subtype_val
    · exact isOpen_empty
  have hat (l : Fin 3) (t : Set.Icc (0 : Real) 1)
      (ht : g l t = g k ⟨1, by norm_num⟩) : t ∈ O l := by
    rcases joinPreimage k l t ht with ⟨hl, ht⟩ | ⟨hl, ht⟩
    · subst l
      subst t
      simpa only [O, ite_eq_left rfl, Set.mem_ofPred_eq] using hgaplo
    · subst l
      subst t
      simpa [O, next_ne k] using hgaphigh
  obtain ⟨R, hR, hiso⟩ := isolateNeighborhood (g k ⟨1, by norm_num⟩) O hO hat
  apply vertexLabels k (k + 1) i j ⟨1, by norm_num⟩ ⟨0, by norm_num⟩
    hp hq (hjoin k) ?_ R hR ?_
  · intro t₁ t₂ htlo hthi _ _ heq
    have hm : g k t₁ ∈ Set.range (g k) ∩ Set.range (g (k + 1)) :=
      ⟨⟨t₁, rfl⟩, ⟨t₂, heq.symm⟩⟩
    obtain ⟨hend, _⟩ := hinter k (k + 1) (Ne.symm (next_ne k)) hm
    have hlo : 0 ≤ (s k).time i.castSucc := by
      rw [← (s k).start]
      exact (s k).strict.monotone (Fin.zero_le _)
    rcases hend with hend | hend
    · have hval := congrArg Subtype.val (hi k hend)
      change (t₁ : Real) = 0 at hval
      linarith only [hlo, htlo, hval]
    · have hval := congrArg Subtype.val (hi k hend)
      change (t₁ : Real) = 1 at hval
      change (t₁ : Real) < 1 at hthi
      linarith only [hthi, hval]
  · intro m t ht
    have hmt := hiso m t ht
    by_cases hm : m = k
    · left
      refine ⟨hm, ?_, t.2.2⟩
      exact (show (s k).time i.castSucc < (t : Real) from
        by simpa only [O, ite_eq_left hm, Set.mem_ofPred_eq] using hmt).le
    · by_cases hm' : m = k + 1
      · right
        refine ⟨hm', t.2.1, ?_⟩
        exact (show (t : Real) < (s (k + 1)).time j.succ from
          by simpa only [O, ite_eq_right hm, ite_eq_left hm', Set.mem_ofPred_eq] using hmt).le
      · simp only [O, ite_eq_right hm, ite_eq_right hm', Set.mem_empty_iff_false] at hmt

private theorem arcAgree :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (U : Set (Real × Real)), ∀ (pieceSide :
            ∀ (k : Fin 3), ∀ (i : Fin (s k).count), ∃ d : (Real × Real) × ((Real × Real) × Bool),
            d.2.1 ≠ 0 ∧ (∀ a : Set.Icc (0 : Real) 1, (s k).time i.castSucc ≤ (a : Real) → (a :
            Real) ≤ (s k).time i.succ → g k a = d.1 + (a : Real) • d.2.1) ∧ (∀ t : Set.Icc (0 :
            Real) 1, (s k).time i.castSucc < (t : Real) → (t : Real) < (s k).time i.succ →
            P3934T1LocalSide U (g k t) d.2.1 d.2.2 ∧ P3934T1LocalSide (closure U)ᶜ (g k t)
            d.2.1 (!d.2.2))),
        let sideInfo (k : Fin 3) (i : Fin (s k).count) := Classical.choose (pieceSide k i)
        let pieceSign (k : Fin 3) (i : Fin (s k).count) : Bool := (sideInfo k i).2.2
        ∀ (signChain : ∀ (k : Fin 3), ∀ n, ∀ (hn : n < (s k).count), pieceSign k ⟨n, hn⟩ =
            pieceSign k ⟨0, (s k).positive⟩),
        let first (k : Fin 3) : Fin (s k).count := ⟨0, (s k).positive⟩
        let last (k : Fin 3) : Fin (s k).count :=
          ⟨(s k).count - 1, by have := (s k).positive; omega⟩
        (∀ (k : Fin 3), pieceSign k (last k) = pieceSign (k + 1) (first (k + 1))) → (∀ (k : Fin
            (3 : ℕ)), pieceSign k (first k) = pieceSign (k + (1 : Fin (3 : ℕ))) (first (k + (1 :
            Fin (3 : ℕ))))) ) := by
  classical
  intro g s U pieceSide sideInfo pieceSign signChain first last joinSignAgree k
  exact (signChain k (last k).val (last k).isLt).symm.trans (joinSignAgree k)

private theorem allArc :
    (by
      classical
      exact
        ∀ (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real), ∀ (s : ∀ k,
            P3723T1PolygonalParameterization (g k)), ∀ (U : Set (Real × Real)), ∀ (pieceSide :
            ∀ (k : Fin 3), ∀ (i : Fin (s k).count), ∃ d : (Real × Real) × ((Real × Real) × Bool),
            d.2.1 ≠ 0 ∧ (∀ a : Set.Icc (0 : Real) 1, (s k).time i.castSucc ≤ (a : Real) → (a :
            Real) ≤ (s k).time i.succ → g k a = d.1 + (a : Real) • d.2.1) ∧ (∀ t : Set.Icc (0 :
            Real) 1, (s k).time i.castSucc < (t : Real) → (t : Real) < (s k).time i.succ →
            P3934T1LocalSide U (g k t) d.2.1 d.2.2 ∧ P3934T1LocalSide (closure U)ᶜ (g k t)
            d.2.1 (!d.2.2))),
        let sideInfo (k : Fin 3) (i : Fin (s k).count) := Classical.choose (pieceSide k i)
        let pieceSign (k : Fin 3) (i : Fin (s k).count) : Bool := (sideInfo k i).2.2
        let first (k : Fin 3) : Fin (s k).count := ⟨0, (s k).positive⟩
        (∀ (k : Fin 3), pieceSign k (first k) = pieceSign (k + 1) (first (k + 1))) → (∀ (k : Fin
            (3 : ℕ)), pieceSign k (first k) = pieceSign (0 : Fin (3 : ℕ)) (first (0 : Fin (3 :
            ℕ)))) ) := by
  classical
  intro g s U pieceSide sideInfo pieceSign first arcAgree k
  fin_cases k
  · rfl
  · exact (arcAgree 0).symm
  · exact arcAgree 2

end PolygonSidePropagation

theorem P3934T1PolygonalSidePropagation
    (g : Fin 3 → Set.Icc (0 : Real) 1 → Real × Real)
    (s : ∀ k, P3723T1PolygonalParameterization (g k))
    (hc : ∀ k, Continuous (g k)) (hi : ∀ k, Function.Injective (g k))
    (hjoin : ∀ k, g k ⟨1, by norm_num⟩ = g (k + 1) ⟨0, by norm_num⟩)
    (hv : Function.Injective (fun k => g k ⟨0, by norm_num⟩))
    (hinter : ∀ k l, k ≠ l → Set.range (g k) ∩ Set.range (g l) ⊆
      {q | (q = g k ⟨0, by norm_num⟩ ∨ q = g k ⟨1, by norm_num⟩) ∧
        (q = g l ⟨0, by norm_num⟩ ∨ q = g l ⟨1, by norm_num⟩)})
    (U : Set (Real × Real)) (hU : IsOpen U)
    (hf : frontier U = ⋃ k, Set.range (g k))
    (he : frontier (closure U)ᶜ = frontier U) :
    ∃ e : Bool, ∀ k,
      P3934T1PolygonalSide U (g k) (s k) e ∧
      P3934T1PolygonalSide (closure U)ᶜ (g k) (s k) (!e) := by
-- BODY
  have transfer (W : Set (Real × Real)) (x : Real × Real) (r : Real) (C : Set (Real × Real))
      (z w : Real × Real) (e : Bool) (hz : z ∈ Metric.ball x r)
      (heq : W ∩ Metric.ball x r = C) (hside : P3934T1LocalSide C z w e) :=
          PolygonSidePropagation.transfer W x r C z w e hz heq hside
  have bend (x : Real × Real) (r : Real) (u v : Real × Real)
      (hr : 0 < r) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hne : u ≠ v)
      (hx : x ∈ frontier U)
      (hchart : frontier U ∩ Metric.ball x r =
        ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • u} ∪
          {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • v}) ∩ Metric.ball x r) :=
              PolygonSidePropagation.bend U hU he transfer x r u v hr hu hv hne hx hchart
  have pieceData (k : Fin 3) (i : Fin (s k).count) := PolygonSidePropagation.pieceData g s hi k i
  have compactRange (k : Fin 3) := PolygonSidePropagation.compactRange g hc k
  have compactImage (k : Fin 3) (S : Set (Set.Icc (0 : Real) 1))
      (hS : IsClosed S) : IsCompact (g k '' S) :=
    (isCompact_univ.of_isClosed_subset hS (Set.subset_univ _)).image (hc k)
  have avoidClosed (K : Set (Real × Real)) (hK : IsClosed K)
      (z : Real × Real) (hz : z ∉ K) := PolygonSidePropagation.avoidClosed K hK z hz
  have isolatePiece (k : Fin 3) (i : Fin (s k).count)
      (t : Set.Icc (0 : Real) 1)
      (htlo : (s k).time i.castSucc < (t : Real))
      (hthi : (t : Real) < (s k).time i.succ) := PolygonSidePropagation.isolatePiece g s hi
          hinter compactRange compactImage avoidClosed k i t htlo hthi
  have scaleLocalSide (W : Set (Real × Real)) (z w : Real × Real)
      (c : Real) (e : Bool) (hc : 0 < c)
      (hside : P3934T1LocalSide W z w e) := LocalSideScaling.positiveScale W z w c e hc
          hside
  have straightFrontierRays (k : Fin 3) (i : Fin (s k).count)
      (A B : Real × Real) (hB : B ≠ 0)
      (hline : ∀ a : Set.Icc (0 : Real) 1,
        (s k).time i.castSucc ≤ (a : Real) →
        (a : Real) ≤ (s k).time i.succ → g k a = A + (a : Real) • B)
      (t : Set.Icc (0 : Real) 1)
      (htlo : (s k).time i.castSucc < (t : Real))
      (hthi : (t : Real) < (s k).time i.succ) := PolygonSidePropagation.straightFrontierRays g s
          U hf isolatePiece k i A B hB hline t htlo hthi
  have straightSideAt (k : Fin 3) (i : Fin (s k).count)
      (A B : Real × Real) (hB : B ≠ 0)
      (hline : ∀ a : Set.Icc (0 : Real) 1,
        (s k).time i.castSucc ≤ (a : Real) →
        (a : Real) ≤ (s k).time i.succ → g k a = A + (a : Real) • B)
      (t : Set.Icc (0 : Real) 1)
      (htlo : (s k).time i.castSucc < (t : Real))
      (hthi : (t : Real) < (s k).time i.succ) := PolygonSidePropagation.straightSideAt g s U hU
          he straightFrontierRays k i A B hB hline t htlo hthi
  have sideMove (W : Set (Real × Real)) (z z' w : Real × Real) (e : Bool)
      (hshift : ∃ c : Real, z' = z + c • w)
      (hside : P3934T1LocalSide W z w e)
      (hclose : dist z' z < Classical.choose hside) := PolygonSidePropagation.sideMove W z z' w e
          hshift hside hclose
  have sideSignsDisjoint (W : Set (Real × Real)) (z w : Real × Real)
      (hw : w ≠ 0)
      (hpos : P3934T1LocalSide W z w true)
      (hneg : P3934T1LocalSide W z w false) := PolygonSidePropagation.sideSignsDisjoint W z w
          hw hpos hneg
  have pieceConstant (k : Fin 3) (i : Fin (s k).count)
      (A B : Real × Real) (hB : B ≠ 0)
      (hline : ∀ a : Set.Icc (0 : Real) 1,
        (s k).time i.castSucc ≤ (a : Real) →
        (a : Real) ≤ (s k).time i.succ → g k a = A + (a : Real) • B) :=
            PolygonSidePropagation.pieceConstant g s U straightSideAt sideMove sideSignsDisjoint
            k i A B hB hline
  have interiorIsolate (k : Fin 3) (i : Fin (s k).count)
      (hnxt : i.val + 1 < (s k).count) := PolygonSidePropagation.interiorIsolate g s hi hinter
          compactRange compactImage avoidClosed k i hnxt
  have sideBoolEq (W : Set (Real × Real)) (z w : Real × Real)
      (hw : w ≠ 0) (e f : Bool)
      (he : P3934T1LocalSide W z w e)
      (hf : P3934T1LocalSide W z w f) := PolygonSidePropagation.sideBoolEq sideSignsDisjoint W
          z w hw e f he hf
  have cornerAgree (x B₁ B₂ : Real × Real) (hB₁ : B₁ ≠ 0) (hB₂ : B₂ ≠ 0)
      (a b R : Real) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
      (e₁ e₂ : Bool)
      (back : ∀ t : Real, 0 ≤ t → t ≤ a → x - t • B₁ ∈ frontier U)
      (forward : ∀ t : Real, 0 ≤ t → t ≤ b → x + t • B₂ ∈ frontier U)
      (backSide : ∀ t : Real, 0 < t → t < a →
        P3934T1LocalSide U (x - t • B₁) B₁ e₁)
      (forwardSide : ∀ t : Real, 0 < t → t < b →
        P3934T1LocalSide U (x + t • B₂) B₂ e₂)
      (apart : ∀ t₁ t₂ : Real, 0 < t₁ → t₁ < a → 0 < t₂ → t₂ < b →
        x - t₁ • B₁ ≠ x + t₂ • B₂)
      (near : ∀ q ∈ frontier U, q ∈ Metric.ball x R →
        (∃ t : Real, 0 ≤ t ∧ t ≤ a ∧ q = x - t • B₁) ∨
        (∃ t : Real, 0 ≤ t ∧ t ≤ b ∧ q = x + t • B₂)) := PolygonSidePropagation.cornerAgree U
            bend scaleLocalSide sideBoolEq x B₁ B₂ hB₁ hB₂ a b R ha hb hR e₁ e₂ back forward
            backSide forwardSide apart near
  have pieceSide (k : Fin 3) (i : Fin (s k).count) := PolygonSidePropagation.pieceSide g s U
      pieceData pieceConstant k i
  let sideInfo (k : Fin 3) (i : Fin (s k).count) := Classical.choose (pieceSide k i)
  let chosenA (k : Fin 3) (i : Fin (s k).count) := (sideInfo k i).1
  let chosenAB (k : Fin 3) (i : Fin (s k).count) := (sideInfo k i).2.1
  let pieceSign (k : Fin 3) (i : Fin (s k).count) : Bool := (sideInfo k i).2.2
  have chosenSpec (k : Fin 3) (i : Fin (s k).count) :
      chosenAB k i ≠ 0 ∧
      (∀ a : Set.Icc (0 : Real) 1,
        (s k).time i.castSucc ≤ (a : Real) →
        (a : Real) ≤ (s k).time i.succ →
          g k a = chosenA k i + (a : Real) • chosenAB k i) ∧
      (∀ t : Set.Icc (0 : Real) 1,
        (s k).time i.castSucc < (t : Real) →
        (t : Real) < (s k).time i.succ →
          P3934T1LocalSide U (g k t) (chosenAB k i) (pieceSign k i) ∧
          P3934T1LocalSide (closure U)ᶜ (g k t) (chosenAB k i) (!pieceSign k i)) :=
              PolygonSidePropagation.chosenSpec g s U pieceSide k i
  have vertexLabels (k l : Fin 3) (i : Fin (s k).count) (j : Fin (s l).count)
      (p q : Set.Icc (0 : Real) 1)
      (hp : (s k).time i.succ = (p : Real))
      (hq : (s l).time j.castSucc = (q : Real))
      (hcenter : g k p = g l q)
      (apart : ∀ t₁ t₂ : Set.Icc (0 : Real) 1,
        (s k).time i.castSucc < (t₁ : Real) → (t₁ : Real) < (p : Real) →
        (q : Real) < (t₂ : Real) → (t₂ : Real) < (s l).time j.succ →
        g k t₁ ≠ g l t₂)
      (R : Real) (hR : 0 < R)
      (near : ∀ m (t : Set.Icc (0 : Real) 1),
        g m t ∈ Metric.ball (g k p) R →
        (m = k ∧ (s k).time i.castSucc ≤ (t : Real) ∧ (t : Real) ≤ (p : Real)) ∨
        (m = l ∧ (q : Real) ≤ (t : Real) ∧ (t : Real) ≤ (s l).time j.succ)) :=
            PolygonSidePropagation.vertexLabels g s U hf cornerAgree pieceSide chosenSpec k l i j
            p q hp hq hcenter apart R hR near
  have interiorSignAgree (k : Fin 3) (i : Fin (s k).count)
      (hnxt : i.val + 1 < (s k).count) := PolygonSidePropagation.interiorSignAgree g s hi U
          interiorIsolate pieceSide vertexLabels k i hnxt
  have signChain (k : Fin 3) := PolygonSidePropagation.signChain g s U pieceSide interiorSignAgree k
  have isolateNeighborhood (x : Real × Real)
      (O : Fin 3 → Set (Set.Icc (0 : Real) 1))
      (hO : ∀ k, IsOpen (O k))
      (hx : ∀ k t, g k t = x → t ∈ O k) := PolygonSidePropagation.isolateNeighborhood g
          compactImage avoidClosed x O hO hx
  have next_ne (k : Fin 3) : k + 1 ≠ k := by
    fin_cases k <;> decide
  have joinPreimage (k l : Fin 3) (t : Set.Icc (0 : Real) 1)
      (ht : g l t = g k ⟨1, by norm_num⟩) := PolygonSidePropagation.joinPreimage g hi hjoin hv
          hinter k l t ht
  let first (k : Fin 3) : Fin (s k).count := ⟨0, (s k).positive⟩
  let last (k : Fin 3) : Fin (s k).count :=
    ⟨(s k).count - 1, by have := (s k).positive; omega⟩
  have joinSignAgree (k : Fin 3) := PolygonSidePropagation.joinSignAgree g s hi hjoin hinter U
      pieceSide vertexLabels isolateNeighborhood next_ne joinPreimage k
  have arcAgree (k : Fin 3) := PolygonSidePropagation.arcAgree g s U pieceSide signChain
      joinSignAgree k
  have allArc (k : Fin 3) := PolygonSidePropagation.allArc g s U pieceSide arcAgree k
  have allPieces (k : Fin 3) (i : Fin (s k).count) :
      pieceSign k i = pieceSign 0 (first 0) :=
    (signChain k i.val i.isLt).trans (allArc k)
  refine ⟨pieceSign 0 (first 0), ?_⟩
  intro k
  constructor
  · intro i
    refine ⟨chosenA k i, chosenAB k i, (chosenSpec k i).1, (chosenSpec k i).2.1, ?_⟩
    intro t hlo hhi
    simpa only [allPieces k i] using ((chosenSpec k i).2.2 t hlo hhi).1
  · intro i
    refine ⟨chosenA k i, chosenAB k i, (chosenSpec k i).1, (chosenSpec k i).2.1, ?_⟩
    intro t hlo hhi
    simpa only [allPieces k i] using ((chosenSpec k i).2.2 t hlo hhi).2

end ApollonianSuperharmonic

end
