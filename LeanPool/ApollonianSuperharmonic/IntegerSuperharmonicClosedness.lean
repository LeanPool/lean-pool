/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Topology.Instances.Matrix
public import LeanPool.ApollonianSuperharmonic.IntegerPreservingNormalization
public import LeanPool.ApollonianSuperharmonic.PointwiseDiagonalCompactness
public import LeanPool.ApollonianSuperharmonic.TranslatedMinimumEnvelope

-- [TABLET NODE: IntegerSuperharmonicClosedness]

/-!
# IntegerSuperharmonicClosedness

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem IntegerSuperharmonicClosedness
    (Aseq : Nat -> Matrix (Fin 2) (Fin 2) Real)
    (A : Matrix (Fin 2) (Fin 2) Real)
    (hconv : forall i j,
      Filter.Tendsto (fun k => Aseq k i j) Filter.atTop (nhds (A i j)))
    (hreps : forall k, exists g : IntegerLatticeFunction,
      IntegerSuperharmonicRepresentative (Aseq k) g) :
    exists g : IntegerLatticeFunction,
      IntegerSuperharmonicRepresentative A g := by
-- BODY
  classical
  let B : Nat → Matrix (Fin 2) (Fin 2) Real := fun k =>
    Aseq k - (1 / (k + 1 : Real)) • (1 : Matrix (Fin 2) (Fin 2) Real)
  have hBconv : ∀ i j, Filter.Tendsto (fun k => B k i j) Filter.atTop (nhds (A i j)) := by
    intro i j
    let : ContinuousSub ℝ := by
      constructor
      rw [Metric.continuous_iff]
      intro c e he
      refine ⟨e / 2, by positivity, ?_⟩
      intro d hd
      rw [Real.dist_eq]
      simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff] at hd
      have h1 : |d.1 - c.1| < e / 2 := by simpa [abs_sub_comm] using hd.1
      have h2 : |d.2 - c.2| < e / 2 := by simpa [abs_sub_comm] using hd.2
      calc
        |(d.1 - d.2) - (c.1 - c.2)| = |(d.1 - c.1) - (d.2 - c.2)| := by ring_nf
        _ ≤ |d.1 - c.1| + |d.2 - c.2| := by
          simpa [abs_sub_comm] using (abs_sub_le (d.1 - c.1) (0 : ℝ) (d.2 - c.2))
        _ < e := by linarith
    have hc : Filter.Tendsto (fun k : Nat => (1 / (k + 1 : Real))) Filter.atTop (nhds 0) := by
      rw [Filter.tendsto_def]
      intro s hs
      rcases (mem_nhds_iff.mp hs) with ⟨t, hts, hto, hzero⟩
      obtain ⟨e, he, hsub⟩ := Metric.isOpen_iff.mp hto 0 hzero
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / e)
      apply Filter.eventually_atTop.mpr
      refine ⟨N, ?_⟩
      intro k hk
      apply hts
      apply hsub
      apply Metric.mem_ball.mpr
      rw [Real.dist_eq]
      dsimp
      simp only [sub_zero]
      rw [abs_of_pos (by positivity : (0 : Real) < 1 / (k + 1 : Real))]
      rw [div_lt_iff₀ (by positivity : (0 : Real) < k + 1)]
      have hkreal : (N : Real) ≤ k := by exact_mod_cast hk
      have hk' : (1 / e : Real) < k + 1 := by linarith
      have hrec : e * (1 / e : Real) = 1 := by field_simp
      nlinarith
    by_cases hij : i = j
    · subst j
      have hs : Filter.Tendsto (fun k : Nat =>
          Aseq k i i - (1 / (k + 1 : Real))) Filter.atTop (nhds (A i i - 0)) := by
        exact (hconv i i).sub hc
      simpa [B, Matrix.sub_apply, smul_eq_mul, Matrix.one_apply] using hs
    · simpa [B, Matrix.sub_apply, smul_eq_mul, Matrix.one_apply, hij] using hconv i j
  have hsymm : ∀ k, (Aseq k).IsSymm := by
    intro k
    obtain ⟨f, hf⟩ := hreps k
    exact hf.1
  have hBsymm : ∀ k, (B k).IsSymm := by
    intro k
    apply Matrix.IsSymm.sub
    · exact hsymm k
    · exact (Matrix.isSymm_one).smul _
  have hM : ∃ M : Real, 0 ≤ M ∧ ∀ k, 1 - Matrix.trace (B k) ≤ M := by
    let : ContinuousAdd ℝ := by
      constructor
      rw [Metric.continuous_iff]
      intro c e he
      refine ⟨e / 2, by positivity, ?_⟩
      intro d hd
      rw [Real.dist_eq]
      simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff] at hd
      calc
        |(d.1 + d.2) - (c.1 + c.2)| = |(d.1 - c.1) + (d.2 - c.2)| := by ring_nf
        _ ≤ |d.1 - c.1| + |d.2 - c.2| := abs_add_le _ _
        _ < e := by linarith [hd.1, hd.2]
    have ht : Filter.Tendsto (fun k => Matrix.trace (B k)) Filter.atTop
        (nhds (Matrix.trace A)) := by
      simpa only [Matrix.trace_fin_two] using (hBconv 0 0).add (hBconv 1 1)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (ht (Ioi_mem_nhds (by linarith : Matrix.trace A - 1 < Matrix.trace A)))
    let values := (Finset.range (N + 1)).image (fun k => 1 - Matrix.trace (B k))
    have values_ne : values.Nonempty := by
      refine ⟨1 - Matrix.trace (B 0), ?_⟩
      exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
    let M := max 0 (max (values.max' values_ne) (1 - (Matrix.trace A - 1)))
    refine ⟨M, le_max_left _ _, ?_⟩
    intro k
    by_cases hk : k ≤ N
    · have hm : 1 - Matrix.trace (B k) ∈ values :=
        Finset.mem_image.mpr ⟨k, by simp [hk], rfl⟩
      exact le_trans (Finset.le_max' values _ hm)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · have hlarge : N ≤ k := Nat.le_of_not_ge hk
      have hbound : 1 - Matrix.trace (B k) ≤ 1 - (Matrix.trace A - 1) := by
        have hkbound := hN k hlarge
        change Matrix.trace A - 1 < Matrix.trace (B k) at hkbound
        linarith
      exact le_trans hbound (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨M, hM0, htrace⟩ := hM
  have hnorm : ∀ k, ∃ b : Fin 2 → Real, ∃ u : IntegerLatticeFunction,
      (∀ i, abs (b i) ≤ 1) ∧ u 0 = 0 ∧
      (∀ x, FourNeighborLaplacian u x ≤ 1) ∧
      (∀ x, LatticeQuadraticForm (B k) x +
        dotProduct (b) ![(x.re : Real), (x.im : Real)] ≤ (u x : Real)) := by
    intro k
    obtain ⟨f, hf⟩ := hreps k
    obtain ⟨z, n, b, u, hbi, hb, hu, hu0, hlap, hlower⟩ :=
      IntegerPreservingNormalization (Aseq k) (B k) f hf
        (1 / (k + 1 : Real)) (by positivity) (by
          ext i j
          simp [B, Matrix.sub_apply, smul_eq_mul])
    exact ⟨b, u, hb, hu0, hlap, hlower⟩
  choose b u hb hu0 hulap hulower using hnorm
  obtain ⟨phi, hphi, bInf, v, hbconv, hv, hvlap, hvlower⟩ :=
    PointwiseDiagonalCompactness A B b u M hM0 hBconv hBsymm hb hu0 hulap hulower htrace
  obtain ⟨F, g, hF, hFlap, hmin, hgrowth, hg⟩ := TranslatedMinimumEnvelope A (by
    apply Matrix.IsSymm.eq
    ext i j
    have hji := hconv j i
    have hij : Filter.Tendsto (fun k => Aseq k j i) Filter.atTop (nhds (A i j)) := by
      convert hconv i j using 1
      funext k
      have hh := congrArg (fun z => z j) (congrFun (hsymm k).eq i)
      simpa using hh
    exact tendsto_nhds_unique hji hij) bInf v hvlap hvlower
  exact ⟨g, hg⟩

end ApollonianSuperharmonic

end
