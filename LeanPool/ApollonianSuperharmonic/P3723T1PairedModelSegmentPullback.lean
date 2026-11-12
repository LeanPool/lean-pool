/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import LeanPool.ApollonianSuperharmonic.P3723T1PolygonalParameterization
public import LeanPool.ApollonianSuperharmonic.P3381T1PairedTriangulation
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Metrizable.Uniformity

-- [TABLET NODE: P3723T1PairedModelSegmentPullback]

/-!
# P3723T1PairedModelSegmentPullback

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SegmentPullbackProof

private theorem hgconst :
    (by
      classical
      exact
        ∀ (X : Set (Real × Real)), ∀ (K : Set (Real × Real)), ∀ (h : X ≃ₜ K), ∀ (a : K), ∀ (b :
            K), ∀ (g : Set.Icc (0 : Real) 1 → X), (∀ (s : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)),
            (↑((h : (↑X : Type) → (↑K : Type)) (g s)) : ℝ × ℝ) = ((1 : ℝ) - (↑s : ℝ)) • (↑a : ℝ ×
            ℝ) + (↑s : ℝ) • (↑b : ℝ × ℝ)) → ((a = b) → (∀ (s : Set.Icc (0 : Real) 1), g s = g ⟨0,
            by norm_num⟩))) := by
  classical
  intro X K h a b g hg hab s
  apply h.injective
  apply Subtype.ext
  have hs := hg s
  have h0 := hg ⟨0, by norm_num⟩
  rw [hab] at hs h0
  have hline : (1 - (s : Real)) • (b : Real × Real) +
      (s : Real) • (b : Real × Real) = b := by
    ext <;> simp [smul_eq_mul] <;> ring
  have hzero : (1 - (0 : Real)) • (b : Real × Real) +
      (0 : Real) • (b : Real × Real) = b := by simp
  exact (hs.trans hline).trans (h0.trans (by simp)).symm

private theorem hFbounds :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (a : K), ∀ (b : K),
        let L : Real → Real × Real :=
          AffineMap.lineMap (a : Real × Real) (b : Real × Real)
        let E : Fin t.count → Set (Real × Real) := fun k =>
          convexHull Real (Set.range (t.target ∘ t.face k))
        let I : Fin t.count → Set Real := fun k =>
          Set.Icc 0 1 ∩ L ⁻¹' E k
        ∀ (hIcompact : ∀ (k : Fin t.count), IsCompact (I k)),
        let lo : Fin t.count → Real := fun k =>
          if hk : (I k).Nonempty then Classical.choose ((hIcompact k).exists_isLeast hk) else 0
        let hi : Fin t.count → Real := fun k =>
          if hk : (I k).Nonempty then Classical.choose ((hIcompact k).exists_isGreatest hk) else 0
        let F : Finset Real := {0, 1} ∪ Finset.univ.biUnion (fun k =>
          if (I k).Nonempty then {lo k, hi k} else ∅)
        (∀ (k : Fin t.count), ((I k).Nonempty) → (lo k ∈ I k)) → ((∀ (k : Fin t.count), ((I
            k).Nonempty) → (hi k ∈ I k)) → (∀ x ∈ F, x ∈ Set.Icc (0 : ℝ) (1 : ℝ)))
    ) := by
  classical
  intro n p X K t a b L E I hIcompact lo hi F hlo_mem hhi_mem x hx
  simp only [F, Finset.mem_union] at hx
  rcases hx with hxpair | hxends
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
    rcases hxpair with rfl | rfl <;> norm_num
  · obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hxends
    by_cases hk : (I k).Nonempty
    · simp only [hk, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hxk
      rcases hxk with hxlo | hxhi
      · subst x
        have hm := hlo_mem k hk
        simpa [I] using hm.1
      · subst x
        have hm := hhi_mem k hk
        simpa [I] using hm.1
    · simp [hk] at hxk

private theorem hpart :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (a : K), ∀ (b : K),
        let L : Real → Real × Real :=
          AffineMap.lineMap (a : Real × Real) (b : Real × Real)
        let E : Fin t.count → Set (Real × Real) := fun k =>
          convexHull Real (Set.range (t.target ∘ t.face k))
        let I : Fin t.count → Set Real := fun k =>
          Set.Icc 0 1 ∩ L ⁻¹' E k
        ∀ (hIcompact : ∀ (k : Fin t.count), IsCompact (I k)), (∀ (k : Fin t.count), Convex Real
            (I k)) → ((Set.Icc (0 : Real) 1 ⊆ ⋃ k, I k) → (
        let lo : Fin t.count → Real := fun k =>
          if hk : (I k).Nonempty then Classical.choose ((hIcompact k).exists_isLeast hk) else 0
        let hi : Fin t.count → Real := fun k =>
          if hk : (I k).Nonempty then Classical.choose ((hIcompact k).exists_isGreatest hk) else 0
        (∀ (k : Fin t.count), ((I k).Nonempty) → (IsLeast (I k) (lo k))) → ((∀ (k : Fin t.count),
            ((I k).Nonempty) → (IsGreatest (I k) (hi k))) → (
        let F : Finset Real := {0, 1} ∪ Finset.univ.biUnion (fun k =>
          if (I k).Nonempty then {lo k, hi k} else ∅)
        (∀ (k : Fin t.count), ((I k).Nonempty) → (lo k ∈ F)) → ((∀ (k : Fin t.count), ((I
            k).Nonempty) → (hi k ∈ F)) → ((∀ (k : Fin t.count), ((I k).Nonempty) → (lo k ∈ I k))
            → ((∀ (k : Fin t.count), ((I k).Nonempty) → (hi k ∈ I k)) → ((∀ (x : Real), (x ∈ F) →
            (x ∈ Set.Icc 0 1)) → (∀ (hcount : F.card - 1 + 1 = F.card),
        let e : Fin F.card ↪o Real := F.orderEmbOfFin rfl
        let tm : Fin (F.card - 1 + 1) → Real := fun i => e (Fin.cast hcount i)
        (StrictMono tm) → (∀ (i : Fin (F.card - (1 : ℕ))), ∃ (k : Fin t.count), Set.Icc (tm
            i.castSucc) (tm i.succ) ⊆ I k))))))))))
    ) := by
  classical
  intro n p X K t a b L E I hIcompact hIconvex hIcover lo hi hlo hhi F hloF hhiF hlo_mem hhi_mem
      hFbounds hcount e tm htm_strict i
  let l := tm i.castSucc
  let r := tm i.succ
  have hir : i.castSucc < i.succ := by
    apply Fin.lt_def.mpr
    simp
  have hlr : l < r := by
    exact htm_strict hir
  have hlF : l ∈ F := by
    change e (Fin.cast hcount i.castSucc) ∈ F
    exact Finset.orderEmbOfFin_mem F rfl _
  have hrF : r ∈ F := by
    change e (Fin.cast hcount i.succ) ∈ F
    exact Finset.orderEmbOfFin_mem F rfl _
  let m := (l + r) / 2
  have hlm : l < m := by dsimp [m]; linarith
  have hmr : m < r := by dsimp [m]; linarith
  have hmIcc : m ∈ Set.Icc (0 : Real) 1 := by
    have hbl := (hFbounds l hlF).1
    have hbr := (hFbounds r hrF).2
    constructor <;> dsimp [m] <;> linarith
  obtain ⟨k, hkm⟩ := Set.mem_iUnion.mp (hIcover hmIcc)
  have hkn : (I k).Nonempty := ⟨m, hkm⟩
  have hno (x : Real) (hxF : x ∈ F) : ¬ (l < x ∧ x < r) := by
    rintro ⟨hlx, hxr⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin F.card, e j = x := by
      have hxrange : x ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin F rfl]
        exact hxF
      exact hxrange
    have hlj : Fin.cast hcount i.castSucc < j := by
      apply e.lt_iff_lt.mp
      change e (Fin.cast hcount i.castSucc) < e j
      simpa [l, tm, hj] using hlx
    have hjr : j < Fin.cast hcount i.succ := by
      apply e.lt_iff_lt.mp
      change e j < e (Fin.cast hcount i.succ)
      simpa [r, tm, hj] using hxr
    have hljv : i.val < j.val := by
      have h := hlj
      simp only [Fin.lt_def, Fin.val_cast, Fin.val_castSucc] at h
      exact h
    have hjrv : j.val < i.val + 1 := by
      have h := hjr
      simp only [Fin.lt_def, Fin.val_cast, Fin.val_succ] at h
      exact h
    omega
  have hlole : lo k ≤ l := by
    by_contra hn
    have hml := (hlo k hkn).2 hkm
    exact hno (lo k) (hloF k hkn) ⟨lt_of_not_ge hn, lt_of_le_of_lt hml hmr⟩
  have hler : r ≤ hi k := by
    by_contra hn
    have hml := (hhi k hkn).2 hkm
    exact hno (hi k) (hhiF k hkn) ⟨lt_of_lt_of_le hlm hml, lt_of_not_ge hn⟩
  have hlowhi : lo k ≤ hi k := le_trans hlole (le_trans hlr.le hler)
  have hseg := (hIconvex k).segment_subset (hlo_mem k hkn) (hhi_mem k hkn)
  rw [segment_eq_Icc hlowhi] at hseg
  refine ⟨k, ?_⟩
  intro s hs
  apply hseg
  exact ⟨le_trans hlole hs.1, le_trans hs.2 hler⟩

private theorem target_weights :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), ∀ (t : P3381T1PairedTriangulation p X K),
        let E : Fin t.count → Set (Real × Real) := fun k =>
          convexHull Real (Set.range (t.target ∘ t.face k))
        ∀ (k : Fin t.count), ∀ z ∈ E k, ∃ (w : Fin (3 : ℕ) → ℝ), ∑ j : Fin (3 : ℕ), w j = (1 : ℝ)
            ∧ (∀ (j : Fin (3 : ℕ)), (0 : ℝ) ≤ w j) ∧ z = ∑ j : Fin (3 : ℕ), w j • t.target
            (t.face k j)
    ) := by
  classical
  intro n p X K t E k z hz
  change z ∈ convexHull Real (Set.range (t.target ∘ t.face k)) at hz
  obtain ⟨ι, inst, w, y, hw0, hw1, hy, hzy⟩ :=
    mem_convexHull_iff_exists_fintype.mp hz
  let _ := inst
  choose c hc using hy
  simp only [Function.comp_apply] at hc
  let W : Fin 3 → Real := fun j => ∑ r, if c r = j then w r else 0
  have hW : (∑ j, W j) = 1 := by
    simpa [W, Finset.sum_comm] using hw1
  have hWnonneg : ∀ j, 0 ≤ W j := by
    intro j
    apply Finset.sum_nonneg
    intro r _
    split_ifs with h
    · exact hw0 r
    · exact le_rfl
  have sum_eq : ∀ f : Fin 3 → Real × Real,
      (∑ j, W j • f j) = ∑ r, w r • f (c r) := by
    intro f
    simp [W, Finset.sum_smul, Finset.sum_comm, ite_smul]
  refine ⟨W, hW, hWnonneg, ?_⟩
  calc
    z = ∑ r, w r • y r := hzy.symm
    _ = ∑ r, w r • t.target (t.face k (c r)) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← hc r]
    _ = ∑ j, W j • t.target (t.face k j) :=
      (sum_eq (t.target ∘ t.face k)).symm

private theorem piece :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (X : Set (Real × Real)), ∀ (K : Set
            (Real × Real)), ∀ (t : P3381T1PairedTriangulation p X K), ∀ (h : X ≃ₜ K), (∀ (k :
            Fin t.count), ∀ (x : (↑X : Type)), (↑x : ℝ × ℝ) ∈ (convexHull ℝ : Set (ℝ × ℝ) → Set
            (ℝ × ℝ)) (Set.range (p.vertex ∘ t.face k)) → ∀ (w : Fin (3 : ℕ) → ℝ), ∑ i : Fin (3 :
            ℕ), w i = (1 : ℝ) → (↑x : ℝ × ℝ) = ∑ i : Fin (3 : ℕ), w i • p.vertex (t.face k i) →
            (↑((h : (↑X : Type) → (↑K : Type)) x) : ℝ × ℝ) = ∑ i : Fin (3 : ℕ), w i • t.target
            (t.face k i)) → (∀ (a : K), ∀ (b : K), ∀ (g : Set.Icc (0 : Real) 1 → X), (∀ (s :
            (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (↑((h : (↑X : Type) → (↑K : Type)) (g s)) : ℝ ×
            ℝ) = ((1 : ℝ) - (↑s : ℝ)) • (↑a : ℝ × ℝ) + (↑s : ℝ) • (↑b : ℝ × ℝ)) → (
        let L : Real → Real × Real :=
          AffineMap.lineMap (a : Real × Real) (b : Real × Real)
        (∀ (s : Real), L s = (1 - s) • (a : Real × Real) + s • (b : Real × Real)) → (
        let E : Fin t.count → Set (Real × Real) := fun k =>
          convexHull Real (Set.range (t.target ∘ t.face k))
        let I : Fin t.count → Set Real := fun k =>
          Set.Icc 0 1 ∩ L ⁻¹' E k
        ∀ (hIcompact : ∀ (k : Fin t.count), IsCompact (I k)),
        let lo : Fin t.count → Real := fun k =>
          if hk : (I k).Nonempty then Classical.choose ((hIcompact k).exists_isLeast hk) else 0
        let hi : Fin t.count → Real := fun k =>
          if hk : (I k).Nonempty then Classical.choose ((hIcompact k).exists_isGreatest hk) else 0
        let F : Finset Real := {0, 1} ∪ Finset.univ.biUnion (fun k =>
          if (I k).Nonempty then {lo k, hi k} else ∅)
        ∀ (hcount : F.card - 1 + 1 = F.card),
        let e : Fin F.card ↪o Real := F.orderEmbOfFin rfl
        let tm : Fin (F.card - 1 + 1) → Real := fun i => e (Fin.cast hcount i)
        (StrictMono tm) → ((∀ (i : Fin (F.card - 1)), ∃ k, Set.Icc (tm i.castSucc) (tm i.succ) ⊆
            I k) → ((∀ (k : Fin t.count), ∀ (z : Real × Real), (z ∈ E k) → (∃ w : Fin 3 → Real,
            (∑ j, w j) = 1 ∧ (∀ j, 0 ≤ w j) ∧ z = ∑ j, w j • t.target (t.face k j))) → ((∀ (k :
            Fin t.count), ∀ (w : Fin 3 → Real), ((∑ j, w j) = 1) → ((∀ j, 0 ≤ w j) → ((∑ j, w j •
            p.vertex (t.face k j)) ∈ convexHull Real (Set.range (p.vertex ∘ t.face k))))) → (∀ (i
            : Fin (F.card - (1 : ℕ))), ∃ (A : ℝ × ℝ) (B : ℝ × ℝ), ∀ (s : (↑(Set.Icc (0 : ℝ) (1 :
            ℝ)) : Type)), tm i.castSucc ≤ (↑s : ℝ) → (↑s : ℝ) ≤ tm i.succ → (↑(g s) : ℝ × ℝ) = A
            + (↑s : ℝ) • B)))))))
    ) := by
  classical
  intro n p X K t h haffine a b g hg L hL E I hIcompact lo hi F hcount e tm htm_strict hpart
      target_weights source_hull i
  obtain ⟨k, hsub⟩ := hpart i
  let u := tm i.castSucc
  let v := tm i.succ
  have huv : u < v := htm_strict (by
    apply Fin.lt_def.mpr
    simp)
  have huI : u ∈ I k := hsub ⟨le_rfl, huv.le⟩
  have hvI : v ∈ I k := hsub ⟨huv.le, le_rfl⟩
  have huI' : u ∈ Set.Icc 0 1 ∧ L u ∈ E k := by simpa [I] using huI
  have hvI' : v ∈ Set.Icc 0 1 ∧ L v ∈ E k := by simpa [I] using hvI
  have huE : L u ∈ E k := huI'.2
  have hvE : L v ∈ E k := hvI'.2
  obtain ⟨w0, hw0sum, hw0nonneg, hw0target⟩ := target_weights k (L u) huE
  obtain ⟨w1, hw1sum, hw1nonneg, hw1target⟩ := target_weights k (L v) hvE
  let x0 : Real × Real := ∑ j, w0 j • p.vertex (t.face k j)
  let x1 : Real × Real := ∑ j, w1 j • p.vertex (t.face k j)
  have hx0src : x0 ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) := by
    exact source_hull k w0 hw0sum hw0nonneg
  have hx1src : x1 ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) := by
    exact source_hull k w1 hw1sum hw1nonneg
  have hx0X : x0 ∈ X := by
    rw [t.source_cover]
    exact Set.mem_iUnion.mpr ⟨k, hx0src⟩
  have hx1X : x1 ∈ X := by
    rw [t.source_cover]
    exact Set.mem_iUnion.mpr ⟨k, hx1src⟩
  let z0 : X := ⟨x0, hx0X⟩
  let z1 : X := ⟨x1, hx1X⟩
  have hz0map : (h z0 : Real × Real) = L u := by
    calc
      (h z0 : Real × Real) = ∑ j, w0 j • t.target (t.face k j) :=
        haffine k z0 hx0src w0 hw0sum rfl
      _ = L u := hw0target.symm
  have hz1map : (h z1 : Real × Real) = L v := by
    calc
      (h z1 : Real × Real) = ∑ j, w1 j • t.target (t.face k j) :=
        haffine k z1 hx1src w1 hw1sum rfl
      _ = L v := hw1target.symm
  let su : Set.Icc (0 : Real) 1 := ⟨u, huI'.1⟩
  let sv : Set.Icc (0 : Real) 1 := ⟨v, hvI'.1⟩
  have hg0 : g su = z0 := by
    apply h.injective
    apply Subtype.ext
    rw [hg su, ← hL u, hz0map]
  have hg1 : g sv = z1 := by
    apply h.injective
    apply Subtype.ext
    rw [hg sv, ← hL v, hz1map]
  let B : Real × Real := (v - u)⁻¹ • (x1 - x0)
  let A : Real × Real := x0 - u • B
  refine ⟨A, B, ?_⟩
  intro s hs₀ hs₁
  have hs : (s : Real) ∈ Set.Icc u v := ⟨hs₀, hs₁⟩
  let q : Real := ((s : Real) - u) / (v - u)
  have hden : 0 < v - u := sub_pos.mpr huv
  have hq : q ∈ Set.Icc 0 1 := by
    constructor
    · dsimp [q]
      exact div_nonneg (sub_nonneg.mpr hs.1) hden.le
    · dsimp [q]
      apply (div_le_iff₀ hden).2
      linarith
  have hparam : (1 - q) * u + q * v = (s : Real) := by
    dsimp [q]
    field_simp [ne_of_gt hden]
    ring
  let w : Fin 3 → Real := fun j => (1 - q) * w0 j + q * w1 j
  have hwSum : (∑ j, w j) = 1 := by
    simp [w, Finset.sum_add_distrib, ← Finset.mul_sum, hw0sum, hw1sum]
  have hwNonneg : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hq.2) (hw0nonneg j))
      (mul_nonneg hq.1 (hw1nonneg j))
  have hinterp (f : Fin 3 → Real × Real) :
      (∑ j, w j • f j) =
        (1 - q) • (∑ j, w0 j • f j) + q • (∑ j, w1 j • f j) := by
    ext <;> simp [w, Fin.sum_univ_three, smul_eq_mul] <;> ring
  have hsourceInterp :
      (∑ j, w j • p.vertex (t.face k j)) = (1 - q) • x0 + q • x1 := by
    simpa [x0, x1] using hinterp (p.vertex ∘ t.face k)
  have htargetInterp :
      (∑ j, w j • t.target (t.face k j)) = L (s : Real) := by
    calc
      (∑ j, w j • t.target (t.face k j)) =
          (1 - q) • (∑ j, w0 j • t.target (t.face k j)) +
            q • (∑ j, w1 j • t.target (t.face k j)) := by
              exact hinterp (t.target ∘ t.face k)
      _ = (1 - q) • L u + q • L v := by rw [← hw0target, ← hw1target]
      _ = L (s : Real) := by
        have hlin : (1 - q) • L u + q • L v =
            L ((1 - q) * u + q * v) := by
          rw [hL u, hL v, hL ((1 - q) * u + q * v)]
          ext <;> simp [smul_eq_mul] <;> ring
        rw [hlin, hparam]
  let xs : Real × Real := ∑ j, w j • p.vertex (t.face k j)
  have hxssrc : xs ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) :=
    source_hull k w hwSum hwNonneg
  have hxsX : xs ∈ X := by
    rw [t.source_cover]
    exact Set.mem_iUnion.mpr ⟨k, hxssrc⟩
  let zs : X := ⟨xs, hxsX⟩
  have hzsm : (h zs : Real × Real) = L (s : Real) := by
    calc
      (h zs : Real × Real) = ∑ j, w j • t.target (t.face k j) :=
        haffine k zs hxssrc w hwSum rfl
      _ = L (s : Real) := htargetInterp
  have hgs : g s = zs := by
    apply h.injective
    apply Subtype.ext
    calc
      (h (g s) : Real × Real) = (1 - (s : Real)) • (a : Real × Real) +
          (s : Real) • (b : Real × Real) := hg s
      _ = L (s : Real) := (hL (s : Real)).symm
      _ = (h zs : Real × Real) := hzsm.symm
  rw [hgs]
  change xs = A + (s : Real) • B
  change (∑ j, w j • p.vertex (t.face k j)) = A + (s : Real) • B
  rw [hsourceInterp]
  dsimp [A, B, q]
  ext <;> simp [smul_eq_mul] <;> field_simp [ne_of_gt hden] <;> ring

end SegmentPullbackProof

theorem P3723T1PairedModelSegmentPullback {n : Nat}
    (p : P3381T1PolygonBoundary n) (X K : Set (Real × Real))
    (t : P3381T1PairedTriangulation p X K) (h : X ≃ₜ K)
    (haffine : ∀ k (x : X),
      (x : Real × Real) ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) →
      ∀ w : Fin 3 → Real, (∑ i, w i) = 1 →
        (x : Real × Real) = ∑ i, w i • p.vertex (t.face k i) →
        (h x : Real × Real) = ∑ i, w i • t.target (t.face k i))
    (a b : K) (g : Set.Icc (0 : Real) 1 → X)
    (hg : ∀ s, (h (g s) : Real × Real) =
      (1 - (s : Real)) • (a : Real × Real) + (s : Real) • (b : Real × Real)) :
    Nonempty (P3723T1PolygonalParameterization
      (fun s => (g s : Real × Real))) := by
-- BODY
  classical
  by_cases hab : a = b
  · have hgconst (s : Set.Icc (0 : Real) 1) : g s = g ⟨0, by norm_num⟩ :=
      SegmentPullbackProof.hgconst X K h a b g hg hab s
    refine ⟨{ count := 1
              positive := by norm_num
              time := fun i => (i : Real)
              strict := ?_
              start := by simp
              finish := by simp
              affine_on := ?_ }⟩
    · intro i j hij
      have hij' : (i : Nat) < (j : Nat) := hij
      change (i : Real) < (j : Real)
      exact Nat.cast_lt.mpr hij'
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      refine ⟨(g ⟨0, by norm_num⟩ : Real × Real), 0, ?_⟩
      intro s _ _
      rw [hgconst s]
      simp
  · let L : Real → Real × Real :=
      AffineMap.lineMap (a : Real × Real) (b : Real × Real)
    have hL (s : Real) : L s =
        (1 - s) • (a : Real × Real) + s • (b : Real × Real) := by
      simp [L, AffineMap.lineMap_apply_module]
    have hLc : Continuous L := by
      dsimp [L]
      fun_prop
    let E : Fin t.count → Set (Real × Real) := fun k =>
      convexHull Real (Set.range (t.target ∘ t.face k))
    let I : Fin t.count → Set Real := fun k =>
      Set.Icc 0 1 ∩ L ⁻¹' E k
    have hEcompact (k : Fin t.count) : IsCompact (E k) := by
      exact (Set.finite_range (t.target ∘ t.face k)).isCompact_convexHull Real
    have hEconvex (k : Fin t.count) : Convex Real (E k) :=
      convex_convexHull Real _
    have hIcompact (k : Fin t.count) : IsCompact (I k) := by
      exact isCompact_Icc.inter_right ((hEcompact k).isClosed.preimage hLc)
    have hIconvex (k : Fin t.count) : Convex Real (I k) := by
      change Convex Real (Set.Icc 0 1 ∩ L ⁻¹' E k)
      exact Convex.inter (convex_Icc 0 1) (Convex.affine_preimage
        (AffineMap.lineMap (a : Real × Real) (b : Real × Real))
        (hEconvex k))
    have hIcover : Set.Icc (0 : Real) 1 ⊆ ⋃ k, I k := by
      intro s hs
      have hsline : L s ∈ segment Real (a : Real × Real) (b : Real × Real) := by
        rw [segment_eq_image]
        exact ⟨s, hs, (hL s).symm⟩
      have hsK : L s ∈ K := (t.target_convex.segment_subset a.property b.property) hsline
      rw [t.target_cover] at hsK
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hsK
      exact Set.mem_iUnion.mpr ⟨k, hs, hk⟩
    let lo : Fin t.count → Real := fun k =>
      if hk : (I k).Nonempty then Classical.choose ((hIcompact k).exists_isLeast hk) else 0
    let hi : Fin t.count → Real := fun k =>
      if hk : (I k).Nonempty then Classical.choose ((hIcompact k).exists_isGreatest hk) else 0
    have hlo (k : Fin t.count) (hk : (I k).Nonempty) : IsLeast (I k) (lo k) := by
      simp only [lo, dite_eq_left hk]
      exact Classical.choose_spec ((hIcompact k).exists_isLeast hk)
    have hhi (k : Fin t.count) (hk : (I k).Nonempty) : IsGreatest (I k) (hi k) := by
      simp only [hi, dite_eq_left hk]
      exact Classical.choose_spec ((hIcompact k).exists_isGreatest hk)
    let F : Finset Real := {0, 1} ∪ Finset.univ.biUnion (fun k =>
      if (I k).Nonempty then {lo k, hi k} else ∅)
    have hzeroF : (0 : Real) ∈ F := by simp [F]
    have honeF : (1 : Real) ∈ F := by simp [F]
    have hloF (k : Fin t.count) (hk : (I k).Nonempty) : lo k ∈ F := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      exact ⟨k, Finset.mem_univ _, by simp [hk]⟩
    have hhiF (k : Fin t.count) (hk : (I k).Nonempty) : hi k ∈ F := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      exact ⟨k, Finset.mem_univ _, by simp [hk]⟩
    have hlo_mem (k : Fin t.count) (hk : (I k).Nonempty) : lo k ∈ I k :=
      (hlo k hk).1
    have hhi_mem (k : Fin t.count) (hk : (I k).Nonempty) : hi k ∈ I k :=
      (hhi k hk).1
    have hFbounds (x : Real) (hx : x ∈ F) : x ∈ Set.Icc 0 1 := SegmentPullbackProof.hFbounds n p
        X K t a b hIcompact hlo_mem hhi_mem x hx
    have hFne : F.Nonempty := ⟨0, hzeroF⟩
    have hFcard : 1 < F.card := by
      apply Finset.one_lt_card.mpr
      exact ⟨0, hzeroF, 1, honeF, by norm_num⟩
    have hFmin : F.min' hFne = 0 := by
      apply (Finset.min'_eq_iff F hFne 0).2
      exact ⟨hzeroF, fun x hx => (hFbounds x hx).1⟩
    have hFmax : F.max' hFne = 1 := by
      apply (Finset.max'_eq_iff F hFne 1).2
      exact ⟨honeF, fun x hx => (hFbounds x hx).2⟩
    have hN : 0 < F.card := Nat.lt_trans Nat.zero_lt_one hFcard
    have hcount : F.card - 1 + 1 = F.card := by omega
    let e : Fin F.card ↪o Real := F.orderEmbOfFin rfl
    let tm : Fin (F.card - 1 + 1) → Real := fun i => e (Fin.cast hcount i)
    have htm_strict : StrictMono tm := by
      intro i j hij
      apply e.strictMono
      apply Fin.lt_def.mpr
      simpa using hij
    have htm_start : tm 0 = 0 := by
      change e (Fin.cast hcount 0) = 0
      have hcast : Fin.cast hcount 0 = ⟨0, hN⟩ := by
        apply Fin.ext
        rfl
      rw [hcast, Finset.orderEmbOfFin_zero rfl hN, hFmin]
    have htm_finish : tm (Fin.last (F.card - 1)) = 1 := by
      change e (Fin.cast hcount (Fin.last (F.card - 1))) = 1
      have hcast : Fin.cast hcount (Fin.last (F.card - 1)) =
          ⟨F.card - 1, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hcast, Finset.orderEmbOfFin_last rfl hN, hFmax]
    have hpart (i : Fin (F.card - 1)) :
        ∃ k, Set.Icc (tm i.castSucc) (tm i.succ) ⊆ I k := SegmentPullbackProof.hpart n p X K t a
            b hIcompact hIconvex hIcover hlo hhi hloF hhiF hlo_mem hhi_mem hFbounds hcount
            htm_strict i
    have target_weights (k : Fin t.count) (z : Real × Real)
        (hz : z ∈ E k) : ∃ w : Fin 3 → Real,
          (∑ j, w j) = 1 ∧ (∀ j, 0 ≤ w j) ∧
          z = ∑ j, w j • t.target (t.face k j) := SegmentPullbackProof.target_weights n p X K t k
              z hz
    have source_hull (k : Fin t.count) (w : Fin 3 → Real)
        (hw : (∑ j, w j) = 1) (hw0 : ∀ j, 0 ≤ w j) :
        (∑ j, w j • p.vertex (t.face k j)) ∈
          convexHull Real (Set.range (p.vertex ∘ t.face k)) := by
      apply mem_convexHull_of_exists_fintype w (p.vertex ∘ t.face k) hw0 hw
      · intro j
        exact Set.mem_range_self j
      · rfl
    have piece (i : Fin (F.card - 1)) : ∃ A B : Real × Real,
        ∀ s : Set.Icc (0 : Real) 1,
          tm i.castSucc ≤ (s : Real) → (s : Real) ≤ tm i.succ →
          (g s : Real × Real) = A + (s : Real) • B := SegmentPullbackProof.piece n p X K t h
              haffine a b g hg hL hIcompact hcount htm_strict hpart target_weights source_hull i
    refine ⟨{ count := F.card - 1
              positive := by omega
              time := tm
              strict := htm_strict
              start := htm_start
              finish := htm_finish
              affine_on := ?_ }⟩
    intro i
    exact piece i

end ApollonianSuperharmonic

end
