/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Spectrum.BallSpectrum
public import LeanPool.EllipticPDE.Spectrum.Multiplicity
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition


/-!
# Infinite dimensionality of `H₀¹` of the unit ball

`EllipticPdes.Sobolev.exists_eigen_family` recurses on a vector of nonzero `L²` class
orthogonal to the family built so far, which is the infinite dimensionality of `H₀¹(Ω)`. This
file discharges it on the unit ball.

`n` bumps sit at the points `((2k+1)/(2n) - 1/2)eᵢ` of the first coordinate axis, each supported
in the ball of radius `1/(2n)` about its centre. The centres are `1/n` apart, so the supports are
disjoint, and each closed support sits inside the unit ball since `1/2 + 1/(2n) < 1`. Disjoint
supports make the `L²` classes orthogonal, and each is nonzero because a bump is one at its
centre.

Given `m` vectors, take `m + 1` of these bumps. A linear map from an `(m+1)`-dimensional space to
an `m`-dimensional one has a nonzero kernel, so some combination of the bumps is `L²`-orthogonal
to all `m` vectors, and orthogonality of the bumps makes that combination nonzero.

## Main declarations

* `EllipticPdes.Sobolev.ballBump`: a bump at a centre, with its support a ball of given radius.
* `EllipticPdes.Sobolev.orth_family_nonempty_ball`: the hypothesis of `exists_eigen_family`.
* `EllipticPdes.Sobolev.dirichlet_eigen_family_ball`: the Dirichlet eigenvalue sequence of the
  unit ball, with `2 < d` the only hypothesis.
* `EllipticPdes.Sobolev.dirichlet_eigenvalue_pos_ball`: every weak Dirichlet eigenvalue of the
  unit ball is positive.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.5.1, Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Bornology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Analysis EllipticPdes.Embedding

variable {d : ℕ}

/-! ### A bump at a centre -/

/-- A bump at `c`, one on `closedBall c (r/2)` and supported in `closedBall c r`. -/
def ballBump (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) : ContDiffBump c :=
  ⟨r / 2, r, by positivity, by linarith⟩

lemma tsupport_ballBump (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    tsupport (⇑(ballBump c hr)) = closedBall c r :=
  (ballBump c hr).tsupport_eq

lemma support_ballBump (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    Function.support (⇑(ballBump c hr)) = ball c r :=
  (ballBump c hr).support_eq

lemma ballBump_centre (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    (ballBump c hr) c = 1 :=
  (ballBump c hr).one_of_mem_closedBall (mem_closedBall_self (ballBump c hr).rIn_pos.le)

lemma isTestFn_ballBump {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ Ω) :
    IsTestFn Ω (⇑(ballBump c hr)) :=
  ⟨(ballBump c hr).contDiff, (ballBump c hr).hasCompactSupport,
    (tsupport_ballBump c hr).symm ▸ hsub⟩

/-- A bump has positive `Lᵖ` seminorm, being continuous and one at its centre. -/
lemma eLpNorm_ballBump_ne_zero (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) : eLpNorm (⇑(ballBump c hr)) p volume ≠ 0 := by
  rw [Ne, eLpNorm_eq_zero_iff hp0]
  intro hae
  have hzero : (⇑(ballBump c hr) : EuclideanSpace ℝ (Fin d) → ℝ) = 0 :=
    ((ballBump c hr).continuous.ae_eq_iff_eq volume continuous_const).mp hae
  have h1 := ballBump_centre c hr
  rw [hzero] at h1
  simp at h1

/-! ### The centres -/

/-- The coordinate of the `k`-th centre: `n` points spaced `1/n` apart inside `(-1/2, 1/2)`. -/
def bumpCoord (n : ℕ) (k : Fin n) : ℝ := (2 * (k : ℝ) + 1) / (2 * n) - 1 / 2

/-- The common radius: half the spacing, so the balls are disjoint. -/
def bumpRadius (n : ℕ) : ℝ := 1 / (2 * n)

/-- The `k`-th centre, on the `i`-th coordinate axis. -/
def bumpCentre (i : Fin d) (n : ℕ) (k : Fin n) : EuclideanSpace ℝ (Fin d) :=
  PiLp.single 2 i (bumpCoord n k)

lemma bumpRadius_pos {n : ℕ} (hn : 0 < n) : 0 < bumpRadius n := by
  have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [bumpRadius]
  positivity

lemma bumpRadius_le {n : ℕ} (hn : 0 < n) : bumpRadius n ≤ 1 / 2 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [bumpRadius]
  refine one_div_le_one_div_of_le (by norm_num) ?_
  linarith

lemma bumpCoord_abs_lt {n : ℕ} (k : Fin n) : |bumpCoord n k| < 1 / 2 := by
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := k.pos
    exact_mod_cast this
  have hk : (k : ℝ) + 1 ≤ (n : ℝ) := by
    have : (k : ℕ) + 1 ≤ n := k.isLt
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hlt : (2 * (k : ℝ) + 1) / (2 * n) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hpos : 0 < (2 * (k : ℝ) + 1) / (2 * n) := by positivity
  rw [bumpCoord, abs_lt]
  constructor <;> linarith

lemma bumpCoord_sub {n : ℕ} (j k : Fin n) :
    bumpCoord n j - bumpCoord n k = ((j : ℝ) - (k : ℝ)) / (n : ℝ) := by
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := j.pos
    exact_mod_cast this
  rw [bumpCoord, bumpCoord]
  field_simp
  ring

lemma one_le_abs_sub_of_ne {j k : ℕ} (h : j ≠ k) : (1 : ℝ) ≤ |(j : ℝ) - (k : ℝ)| := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlt
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hgt
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma bumpCoord_dist {n : ℕ} {j k : Fin n} (h : j ≠ k) :
    1 / (n : ℝ) ≤ |bumpCoord n j - bumpCoord n k| := by
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := j.pos
    exact_mod_cast this
  have hjk : (j : ℕ) ≠ (k : ℕ) := fun hc => h (Fin.ext hc)
  rw [bumpCoord_sub, abs_div, abs_of_pos hn, div_le_div_iff_of_pos_right hn]
  exact one_le_abs_sub_of_ne hjk

lemma dist_bumpCentre (i : Fin d) {n : ℕ} {j k : Fin n} (h : j ≠ k) :
    1 / (n : ℝ) ≤ dist (bumpCentre i n j) (bumpCentre i n k) := by
  have hd : dist (bumpCentre i n j) (bumpCentre i n k) = |bumpCoord n j - bumpCoord n k| := by
    rw [dist_eq_norm, bumpCentre, bumpCentre, ← PiLp.single_sub, PiLp.norm_single,
      Real.norm_eq_abs]
  rw [hd]
  exact bumpCoord_dist h

lemma closedBall_bumpCentre_subset (i : Fin d) {n : ℕ} (k : Fin n) :
    closedBall (bumpCentre i n k) (bumpRadius n) ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  have hn : 0 < n := k.pos
  intro x hx
  rw [mem_closedBall] at hx
  rw [mem_ball, dist_zero_right]
  have hc : ‖bumpCentre i n k‖ = |bumpCoord n k| := by
    rw [bumpCentre, PiLp.norm_single, Real.norm_eq_abs]
  have h1 : ‖x‖ ≤ ‖bumpCentre i n k‖ + bumpRadius n := by
    have := norm_sub_norm_le x (bumpCentre i n k)
    rw [← dist_eq_norm] at this
    linarith
  have h2 := bumpCoord_abs_lt (n := n) k
  have h3 := bumpRadius_le hn
  rw [hc] at h1
  linarith

lemma disjoint_support_ballBump (i : Fin d) {n : ℕ} {j k : Fin n} (h : j ≠ k) (x)
    (hj : (ballBump (bumpCentre i n j) (bumpRadius_pos j.pos)) x ≠ 0)
    (hk : (ballBump (bumpCentre i n k) (bumpRadius_pos k.pos)) x ≠ 0) : False := by
  have hxj : x ∈ ball (bumpCentre i n j) (bumpRadius n) := by
    rw [← support_ballBump]
    exact hj
  have hxk : x ∈ ball (bumpCentre i n k) (bumpRadius n) := by
    rw [← support_ballBump]
    exact hk
  rw [mem_ball] at hxj hxk
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := j.pos
    exact_mod_cast this
  have hsum : dist (bumpCentre i n j) (bumpCentre i n k) < bumpRadius n + bumpRadius n := by
    calc dist (bumpCentre i n j) (bumpCentre i n k)
        ≤ dist (bumpCentre i n j) x + dist x (bumpCentre i n k) := dist_triangle _ _ _
      _ < bumpRadius n + bumpRadius n := by
          rw [dist_comm (bumpCentre i n j) x]
          exact add_lt_add hxj hxk
  have hgap := dist_bumpCentre i h
  have heq : bumpRadius n + bumpRadius n = 1 / (n : ℝ) := by
    rw [bumpRadius]
    field_simp
    norm_num
  linarith

/-! ### The family in `H₀¹` of the unit ball -/

/-- The unit ball of `ℝ^d`. -/
local notation "B1" => ball (0 : EuclideanSpace ℝ (Fin d)) 1

/-- The `k`-th bump of a family of `n`, as a function. -/
def bumpFn (i : Fin d) (n : ℕ) (k : Fin n) : EuclideanSpace ℝ (Fin d) → ℝ :=
  ⇑(ballBump (bumpCentre i n k) (bumpRadius_pos k.pos))

lemma isTestFn_bumpFn (i : Fin d) {n : ℕ} (k : Fin n) : IsTestFn B1 (bumpFn i n k) :=
  isTestFn_ballBump _ _ (closedBall_bumpCentre_subset i k)

/-- Two bumps of the family never both survive at a point. -/
lemma bumpFn_eq_zero_or (i : Fin d) {n : ℕ} {j k : Fin n} (h : j ≠ k)
    (x : EuclideanSpace ℝ (Fin d)) : bumpFn i n j x = 0 ∨ bumpFn i n k x = 0 := by
  by_cases hj : bumpFn i n j x = 0
  · exact Or.inl hj
  by_cases hk : bumpFn i n k x = 0
  · exact Or.inr hk
  exact (disjoint_support_ballBump i h x hj hk).elim

/-- The `k`-th bump, as an element of `H₀¹` of the unit ball. -/
def bumpElt (i : Fin d) (n : ℕ) (k : Fin n) : H01 B1 :=
  ⟨(isTestFn_bumpFn i k).testGraph,
    (Submodule.le_topologicalClosure _)
      (Submodule.subset_span ⟨bumpFn i n k, isTestFn_bumpFn i k, rfl⟩)⟩

lemma coeFn_embL2_bumpElt (i : Fin d) {n : ℕ} (k : Fin n) :
    ⇑(embL2 B1 (bumpElt i n k)) =ᵐ[volume.restrict B1] bumpFn i n k := by
  rw [embL2_apply]
  change ⇑((isTestFn_bumpFn i k).testGraph 0) =ᵐ[volume.restrict B1] _
  rw [IsTestFn.testGraph_zero]
  exact (isTestFn_bumpFn i k).mem_lp.coeFn_toLp

/-- **Disjoint supports make the classes orthogonal.** -/
lemma inner_embL2_bumpElt (i : Fin d) {n : ℕ} {j k : Fin n} (h : j ≠ k) :
    ⟪embL2 B1 (bumpElt i n j), embL2 B1 (bumpElt i n k)⟫ = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [coeFn_embL2_bumpElt i j, coeFn_embL2_bumpElt i k] with x h1 h2
  rw [Pi.zero_apply, h1, h2]
  rcases bumpFn_eq_zero_or i h x with hz | hz
  · rw [hz, inner_zero_left]
  · rw [hz, inner_zero_right]

/-- **Each class is nonzero**, the bump being one at its centre. -/
lemma embL2_bumpElt_ne_zero (i : Fin d) {n : ℕ} (k : Fin n) :
    embL2 B1 (bumpElt i n k) ≠ 0 := by
  intro h0
  rw [embL2_apply] at h0
  have hz : eLpNorm (((isTestFn_bumpFn i k).testGraph 0 : L2D B1)) 2 (volume.restrict B1) = 0 := by
    rw [show ((isTestFn_bumpFn i k).testGraph 0 : L2D B1) = 0 from h0,
      eLpNorm_congr_ae (Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (volume.restrict B1))]
    exact eLpNorm_zero
  rw [eLpNorm_testGraph_zero_eq measurableSet_ball (isTestFn_bumpFn i k) 2] at hz
  exact eLpNorm_ballBump_ne_zero (bumpCentre i n k) (bumpRadius_pos k.pos)
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) hz

/-! ### The hypothesis of the eigenvalue recursion -/

/-- **`H₀¹` of the unit ball is infinite dimensional**, in the form the eigenvalue recursion
asks for: given `m` vectors there is one of nonzero `L²` class orthogonal to them all. Take
`m + 1` bumps with disjoint supports; a linear map from an `(m+1)`-dimensional space to an
`m`-dimensional one has a nonzero kernel, and the combination it names is nonzero because the
bumps are orthogonal. -/
theorem orth_family_nonempty_ball (hd : 2 < d) (m : ℕ) (v : Fin m → H01 B1) :
    ∃ U ∈ orthSubmodule v, embL2 B1 U ≠ 0 := by
  set i : Fin d := ⟨0, by omega⟩ with hi
  set u : Fin (m + 1) → H01 B1 := fun k => bumpElt i (m + 1) k with hu
  set e : Fin (m + 1) → L2D B1 := fun k => embL2 B1 (u k) with he
  have horth : ∀ j k, j ≠ k → ⟪e j, e k⟫ = 0 := fun j k h => inner_embL2_bumpElt i h
  have hne : ∀ k, e k ≠ 0 := fun k => embL2_bumpElt_ne_zero i k
  -- The pairing map, from one more dimension than there are constraints.
  set L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun c j => ∑ k, c k * ⟪e k, embL2 B1 (v j)⟫
      map_add' := by
        intro a b
        funext j
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      map_smul' := by
        intro t a
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring) } with hL
  have hnotinj : ¬ Function.Injective L := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective (f := L) hinj
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at hle
    omega
  have hker : LinearMap.ker L ≠ ⊥ := fun hb => hnotinj (LinearMap.ker_eq_bot.mp hb)
  obtain ⟨c, hcmem, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp hcne
  refine ⟨∑ k, c k • u k, ?_, ?_⟩
  · intro j
    have hsum : embL2 B1 (∑ k, c k • u k) = ∑ k, c k • e k := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [map_smul, he])
    rw [hsum, sum_inner]
    have hzero : (L c) j = 0 := by rw [LinearMap.mem_ker.mp hcmem]; rfl
    rw [hL] at hzero
    simp only [LinearMap.coe_mk, AddHom.coe_mk] at hzero
    rw [← hzero]
    exact Finset.sum_congr rfl (fun k _ => real_inner_smul_left _ _ _)
  · intro h0
    have hsum : embL2 B1 (∑ k, c k • u k) = ∑ k, c k • e k := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [map_smul, he])
    have hpair : ⟪embL2 B1 (∑ k, c k • u k), e k₀⟫ = c k₀ * ‖e k₀‖ ^ 2 := by
      rw [hsum, sum_inner, Finset.sum_eq_single k₀]
      · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      · intro k _ hk
        rw [real_inner_smul_left, horth k k₀ hk, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k₀) hk
    rw [h0, inner_zero_left] at hpair
    have hnorm : ‖e k₀‖ ≠ 0 := fun hz => hne k₀ (norm_eq_zero.mp hz)
    have : c k₀ * ‖e k₀‖ ^ 2 ≠ 0 := by
      refine mul_ne_zero hk₀ ?_
      exact pow_ne_zero 2 hnorm
    exact this hpair.symm

/-- **Dirichlet eigenvalue sequence of the unit ball**, with `2 < d` the only hypothesis: for
every `n` an `L²`-orthonormal family of `n` weak solutions of `-Δw = λw` with
`0 < λ₁ ≤ ⋯ ≤ λₙ`. Every side condition of the chapter is discharged here, boundedness by the
ball itself and the infinite dimensionality by `orth_family_nonempty_ball`. -/
theorem dirichlet_eigen_family_ball (hd : 2 < d) (n : ℕ) :
    ∃ (w : Fin n → H01 B1) (lam : Fin n → ℝ),
      (∀ i, ‖embL2 B1 (w i)‖ = 1) ∧
      (∀ i j, i ≠ j → ⟪embL2 B1 (w i), embL2 B1 (w j)⟫ = 0) ∧
      (∀ i, 0 < lam i) ∧
      (∀ i j, i ≤ j → lam i ≤ lam j) ∧
      (∀ i, ∀ V : H01 B1, laplaceBilin B1 (w i) V
        = lam i * ⟪embL2 B1 (w i), embL2 B1 V⟫) := by
  obtain ⟨p, rfl⟩ : ∃ p, d = p + 1 := ⟨d - 1, by omega⟩
  exact dirichlet_eigen_family_of_bounded _ measurableSet_ball isBounded_ball
    (fun k v => orth_family_nonempty_ball hd k v) n

/-- **Every weak Dirichlet eigenvalue of the unit ball is positive**, with `2 < d` the only
hypothesis beyond the eigenpair. -/
theorem dirichlet_eigenvalue_pos_ball (hd : 2 < d) {lam : ℝ} {U : H01 B1} (hU : U ≠ 0)
    (heig : ∀ V : H01 B1, laplaceBilin B1 U V = lam * ⟪embL2 B1 U, embL2 B1 V⟫) :
    0 < lam := by
  have hne := exists_embL2_ne_zero_ball hd
  obtain ⟨p, rfl⟩ : ∃ p, d = p + 1 := ⟨d - 1, by omega⟩
  exact dirichlet_eigenvalue_pos_of_bounded _ isBounded_ball hne hU heig

end EllipticPdes.Sobolev
