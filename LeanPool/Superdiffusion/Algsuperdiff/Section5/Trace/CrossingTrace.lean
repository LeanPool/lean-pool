/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.Minimizer
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.CubeTrace
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMetric

/-!
# CrossingTrace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Crossing extensions of pre-exit cube traces

A uniformly sampled trace whose times are strictly before an exit need not
itself contain a site outside the exited cube.  This file supplies the two
endpoint corrections that turn such a trace into a crossing of the annulus: at
most one lattice site is prepended and at most one is appended, and neither is
claimed to be visited.  A lower bound on the good vertices of every crossing
therefore transfers to the trace at a loss of at most `2 * d`, which is the
form the Section 5 argument consumes.
-/

open HCPolySupport
open scoped ENNReal NNReal

namespace Algsuperdiff.Section5.Trace

def cubeSiteRadius (k : ℕ) : ℕ := 3 ^ k / 2

def clampCoord (r : ℕ) (z : ℤ) : ℤ :=
  if z < -(r : ℤ) then -(r : ℤ) else if (r : ℤ) < z then (r : ℤ) else z

def clampSite {d : ℕ} (k : ℕ) (z : Section5.Percolation.Site d) :
    Section5.Percolation.Site d :=
  fun i => clampCoord (cubeSiteRadius k) (z i)

private theorem odd_three_pow (k : ℕ) : Odd (3 ^ k) :=
  (show Odd 3 by norm_num).pow

private theorem two_mul_cubeSiteRadius_add_one (k : ℕ) :
    2 * cubeSiteRadius k + 1 = 3 ^ k :=
  Nat.two_mul_div_two_add_one_of_odd (odd_three_pow k)

private theorem clampCoord_bounds (r : ℕ) (z : ℤ) :
    -(r : ℤ) ≤ clampCoord r z ∧ clampCoord r z ≤ (r : ℤ) := by
  unfold clampCoord
  split_ifs <;> omega

private theorem natAbs_clampCoord_le (r : ℕ) (z : ℤ) :
    (clampCoord r z).natAbs ≤ r := by
  have hbounds := clampCoord_bounds r z
  have habs : |clampCoord r z| ≤ (r : ℤ) := abs_le.mpr hbounds
  rw [← Int.natCast_natAbs] at habs
  exact_mod_cast habs

private theorem natAbs_clampCoord_sub_le_one (r : ℕ) (z : ℤ)
    (hz : z.natAbs ≤ r + 1) :
    (clampCoord r z - z).natAbs ≤ 1 := by
  have hzInt : |z| ≤ ((r + 1 : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hz
  unfold clampCoord
  split_ifs <;> omega

private theorem inCube_clampSite {d : ℕ} (k : ℕ)
    (z : Section5.Percolation.Site d) :
    Section5.Percolation.inCube k (clampSite k z) := by
  intro i
  have hi := natAbs_clampCoord_le (cubeSiteRadius k) (z i)
  have hodd := two_mul_cubeSiteRadius_add_one k
  change 2 * (clampCoord (cubeSiteRadius k) (z i)).natAbs < 3 ^ k
  omega

private theorem siteDist_clampSite_le_one {d : ℕ} (k : ℕ)
    (z : Section5.Percolation.Site d)
    (hz : ∀ i, (z i).natAbs ≤ cubeSiteRadius k + 1) :
    Section5.Percolation.siteDist (clampSite k z) z ≤ 1 := by
  apply Finset.sup_le
  intro i _hi
  exact natAbs_clampCoord_sub_le_one _ _ (hz i)

/-- A point of the closed centered cube at physical scale `n + k` has a
nearest scale-`n` site at lattice distance at most one from `inCube k`. -/
theorem exists_inCube_siteDist_nearestTriadicSite_le_one {d : ℕ}
    (n : ℤ) (k : ℕ) (x : Vec d)
    (hx : x ∈ Metric.closedBall (0 : Vec d)
      ((1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)))) :
    ∃ a : Section5.Percolation.Site d,
      Section5.Percolation.inCube k a ∧
      Section5.Percolation.siteDist a (nearestTriadicSite n x) ≤ 1 := by
  let z := nearestTriadicSite n x
  refine ⟨clampSite k z, inCube_clampSite k z, siteDist_clampSite_le_one k z ?_⟩
  intro i
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hpow : (3 : ℝ) ^ (n + (k : ℤ)) = (3 : ℝ) ^ n * (3 : ℝ) ^ k := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  have hxnorm : ‖x‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hxi : |x i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)) := by
    have hcoord := (dist_pi_le_iff (norm_nonneg x)).mp (by
      simpa only [dist_zero_right] using le_rfl : dist x (0 : Vec d) ≤ ‖x‖) i
    rw [Real.dist_eq, Pi.zero_apply, sub_zero] at hcoord
    exact hcoord.trans hxnorm
  let u : ℝ := x i / (3 : ℝ) ^ n
  have hu : |u| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
    change |x i / (3 : ℝ) ^ n| ≤ _
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    calc
      |x i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)) := hxi
      _ = (1 / 2 : ℝ) * (3 : ℝ) ^ k * (3 : ℝ) ^ n := by rw [hpow]; ring
  have hround := abs_le.mp (abs_sub_round u)
  have hu' := abs_le.mp hu
  have hodd := two_mul_cubeSiteRadius_add_one k
  have hoddR : (2 : ℝ) * cubeSiteRadius k + 1 = (3 : ℝ) ^ k := by
    exact_mod_cast hodd
  have hloR : (-((cubeSiteRadius k + 1 : ℕ) : ℝ)) ≤ ((round u : ℤ) : ℝ) := by
    push_cast
    linarith only [hu'.1, hround.2, hoddR]
  have hhiR : ((round u : ℤ) : ℝ) ≤ ((cubeSiteRadius k + 1 : ℕ) : ℝ) := by
    push_cast
    linarith only [hu'.2, hround.1, hoddR]
  have hloZ : (-((cubeSiteRadius k + 1 : ℕ) : ℤ)) ≤ round u := by
    exact_mod_cast hloR
  have hhiZ : round u ≤ ((cubeSiteRadius k + 1 : ℕ) : ℤ) := by
    exact_mod_cast hhiR
  have habsZ : |round u| ≤ ((cubeSiteRadius k + 1 : ℕ) : ℤ) :=
    abs_le.mpr ⟨hloZ, hhiZ⟩
  rw [← Int.natCast_natAbs] at habsZ
  exact_mod_cast habsZ

def outsideSite {d : ℕ} (k : ℕ) (z : Section5.Percolation.Site d)
    (i : Fin d) (positive : Bool) : Section5.Percolation.Site d :=
  Function.update z i
    (if positive then ((cubeSiteRadius k + 1 : ℕ) : ℤ)
      else -((cubeSiteRadius k + 1 : ℕ) : ℤ))

private theorem not_inCube_outsideSite {d : ℕ} (k : ℕ)
    (z : Section5.Percolation.Site d) (i : Fin d) (positive : Bool) :
    ¬Section5.Percolation.inCube k (outsideSite k z i positive) := by
  intro h
  have hi := h i
  have hodd := two_mul_cubeSiteRadius_add_one k
  simp only [outsideSite, Function.update_self] at hi
  split at hi <;> simp only [Int.natAbs_natCast, Int.natAbs_neg] at hi <;> omega

/-- A point strictly inside the centered cube and less than one scale-`n`
cell from a frontier point has a nearest site adjacent to an outside site. -/
theorem exists_not_inCube_siteDist_nearestTriadicSite_le_one_of_frontier
    {d : ℕ} (n : ℤ) (k : ℕ) {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n + (k : ℤ))))
    (hy : y ∈ frontier (openCubeSet (originCube d (n + (k : ℤ)))))
    (hxy : dist x y < (3 : ℝ) ^ n) :
    ∃ b : Section5.Percolation.Site d,
      ¬Section5.Percolation.inCube k b ∧
      Section5.Percolation.siteDist (nearestTriadicSite n x) b ≤ 1 := by
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hr : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)) := by positivity
  have hySphere : y ∈ Metric.sphere (0 : Vec d)
      ((1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ))) := by
    rw [← ball_cubeCenter_eq_openCubeSet (originCube d (n + (k : ℤ)))] at hy
    have hsub := Metric.frontier_ball_subset_sphere hy
    apply Metric.mem_sphere.mpr
    have hdist := Metric.mem_sphere.mp hsub
    have hcenter : cubeCenter (originCube d (n + (k : ℤ))) = (0 : Vec d) := by
      funext j
      simp only [cubeCenter, originCube, Pi.zero_apply, Int.cast_zero, zero_mul]
    rw [hcenter] at hdist
    simpa only [dist_zero_right, cubeRadius, cubeScaleFactor_originCube] using hdist
  have hyDist : dist y (0 : Vec d) =
      (1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)) := Metric.mem_sphere.mp hySphere
  obtain ⟨i, hi⟩ := (dist_pi_eq_iff hr).mp hyDist |>.1
  rw [Real.dist_eq, Pi.zero_apply, sub_zero] at hi
  have hpow : (3 : ℝ) ^ (n + (k : ℤ)) = (3 : ℝ) ^ n * (3 : ℝ) ^ k := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  have hxcoord := (mem_openCubeSet_originCube_iff.mp hx) i
  have hxycoord : |x i - y i| < (3 : ℝ) ^ n := by
    simpa only [Real.dist_eq] using (dist_pi_lt_iff hs).mp hxy i
  have hodd := two_mul_cubeSiteRadius_add_one k
  have hoddR : (2 : ℝ) * cubeSiteRadius k + 1 = (3 : ℝ) ^ k := by
    exact_mod_cast hodd
  have hRscale : (1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)) =
      (3 : ℝ) ^ n * ((cubeSiteRadius k : ℕ) + 1 / 2) := by
    rw [hpow, ← hoddR]
    ring
  rcases abs_cases (y i) with hypos | hyneg
  · have hyval : y i = (1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)) := by
      calc
        y i = |y i| := hypos.1.symm
        _ = (1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ)) := hi
    let b := outsideSite k (nearestTriadicSite n x) i true
    refine ⟨b, not_inCube_outsideSite k _ i true, ?_⟩
    apply Finset.sup_le
    intro j _hj
    by_cases hji : j = i
    · subst j
      have hround : round (x i / (3 : ℝ) ^ n) =
          ((cubeSiteRadius k : ℕ) : ℤ) := by
        let u : ℝ := x i / (3 : ℝ) ^ n
        have huUpper : u < (cubeSiteRadius k : ℕ) + 1 / 2 := by
          change x i / (3 : ℝ) ^ n < _
          rw [div_lt_iff₀ hs]
          calc
            x i < (3 : ℝ) ^ n * ((cubeSiteRadius k : ℕ) + 1 / 2) := by
              rw [← hRscale]
              exact hxcoord.2
            _ = ((cubeSiteRadius k : ℕ) + 1 / 2) * (3 : ℝ) ^ n := mul_comm _ _
        have huLower : (cubeSiteRadius k : ℕ) - 1 / 2 < u := by
          change _ < x i / (3 : ℝ) ^ n
          rw [lt_div_iff₀ hs]
          have hnear := (abs_lt.mp hxycoord).1
          rw [hyval, hRscale] at hnear
          nlinarith only [hnear]
        have hroundLo := sub_half_lt_round u
        have hroundHi := round_le_add_half u
        have hloR : ((cubeSiteRadius k : ℕ) : ℝ) - 1 < ((round u : ℤ) : ℝ) := by
          linarith only [huLower, hroundLo]
        have hhiR : ((round u : ℤ) : ℝ) < (cubeSiteRadius k : ℕ) + 1 := by
          linarith only [huUpper, hroundHi]
        have hloZ : ((cubeSiteRadius k : ℕ) : ℤ) - 1 < round u := by
          exact_mod_cast hloR
        have hhiZ : round u < ((cubeSiteRadius k : ℕ) : ℤ) + 1 := by
          exact_mod_cast hhiR
        change round u = ((cubeSiteRadius k : ℕ) : ℤ)
        omega
      change round (x i / (3 : ℝ) ^ n) = ((cubeSiteRadius k : ℕ) : ℤ) at hround
      dsimp [b, outsideSite, nearestTriadicSite]
      simp only [Function.update_self, hround]
      omega
    · dsimp [b, outsideSite]
      rw [Function.update_of_ne hji]
      rw [sub_self, Int.natAbs_zero]
      norm_num
  · have hyval : y i = -((1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ))) := by
      calc
        y i = -|y i| := by rw [hyneg.1]; ring
        _ = -((1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ))) := by rw [hi]
    let b := outsideSite k (nearestTriadicSite n x) i false
    refine ⟨b, not_inCube_outsideSite k _ i false, ?_⟩
    apply Finset.sup_le
    intro j _hj
    by_cases hji : j = i
    · subst j
      have hround : round (x i / (3 : ℝ) ^ n) =
          -((cubeSiteRadius k : ℕ) : ℤ) := by
        let u : ℝ := x i / (3 : ℝ) ^ n
        have huLower : -((cubeSiteRadius k : ℕ) : ℝ) - 1 / 2 < u := by
          change _ < x i / (3 : ℝ) ^ n
          rw [lt_div_iff₀ hs]
          calc
            (-((cubeSiteRadius k : ℕ) : ℝ) - 1 / 2) * (3 : ℝ) ^ n =
                -((1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ))) := by
              rw [hRscale]
              ring
            _ = (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (n + (k : ℤ)) := by ring
            _ < x i := hxcoord.1
        have huUpper : u < -((cubeSiteRadius k : ℕ) : ℝ) + 1 / 2 := by
          change x i / (3 : ℝ) ^ n < _
          rw [div_lt_iff₀ hs]
          have hnear := (abs_lt.mp hxycoord).2
          rw [hyval, hRscale] at hnear
          nlinarith only [hnear]
        have hroundLo := sub_half_lt_round u
        have hroundHi := round_le_add_half u
        have hloR : -((cubeSiteRadius k : ℕ) : ℝ) - 1 < ((round u : ℤ) : ℝ) := by
          linarith only [huLower, hroundLo]
        have hhiR : ((round u : ℤ) : ℝ) < -((cubeSiteRadius k : ℕ) : ℝ) + 1 := by
          linarith only [huUpper, hroundHi]
        have hloZ : -((cubeSiteRadius k : ℕ) : ℤ) - 1 < round u := by
          exact_mod_cast hloR
        have hhiZ : round u < -((cubeSiteRadius k : ℕ) : ℤ) + 1 := by
          exact_mod_cast hhiR
        change round u = -((cubeSiteRadius k : ℕ) : ℤ)
        omega
      change round (x i / (3 : ℝ) ^ n) = -((cubeSiteRadius k : ℕ) : ℤ) at hround
      dsimp [b, outsideSite, nearestTriadicSite]
      simp only [Function.update_self, hround]
      omega
    · dsimp [b, outsideSite]
      rw [Function.update_of_ne hji]
      rw [sub_self, Int.natAbs_zero]
      norm_num

private theorem isWeakPath_cons_append_singleton {d : ℕ}
    {Gamma : List (Section5.Percolation.Site d)} {a x y b : Section5.Percolation.Site d}
    (hGamma : Section5.Percolation.IsWeakPath Gamma)
    (hhead : Gamma.head? = some x) (hlast : Gamma.getLast? = some y)
    (ha : Section5.Percolation.siteDist a x ≤ 1)
    (hb : Section5.Percolation.siteDist y b ≤ 1) :
    Section5.Percolation.IsWeakPath (a :: Gamma ++ [b]) := by
  cases Gamma with
  | nil => simp at hhead
  | cons z zs =>
      have hzx : z = x := by
        simpa only [List.head?_cons, Option.some.injEq] using hhead
      subst z
      unfold Section5.Percolation.IsWeakPath at hGamma ⊢
      apply List.IsChain.cons
      · apply hGamma.append (List.isChain_singleton b)
        intro u hu v hv
        have huy : u = y := by
          have : y = u := by simpa only [hlast, Option.mem_some_iff] using hu
          exact this.symm
        have hvb : v = b := by
          have : b = v := by
            simpa only [List.head?_singleton, Option.mem_some_iff] using hv
          exact this.symm
        simpa only [huy, hvb] using hb
      · intro u hu
        have hux : u = x := by
          change u ∈ some x at hu
          exact (Option.mem_some_iff.mp hu).symm
        simpa only [hux] using ha

/-- Adding one endpoint correction on each side of a weak trace produces a
crossing path with the same vertices apart from those two corrections. -/
theorem exists_isPathFrom_extension {d k : ℕ}
    {Gamma : List (Section5.Percolation.Site d)} {a x y b : Section5.Percolation.Site d}
    (hGamma : Section5.Percolation.IsWeakPath Gamma)
    (hhead : Gamma.head? = some x) (hlast : Gamma.getLast? = some y)
    (ha : Section5.Percolation.siteDist a x ≤ 1)
    (hb : Section5.Percolation.siteDist y b ≤ 1)
    (hain : Section5.Percolation.inCube k a)
    (hbout : ¬Section5.Percolation.inCube (k + 1) b) :
    ∃ Delta : List (Section5.Percolation.Site d),
      Section5.Percolation.IsPathFrom k Delta ∧
      Delta.toFinset = insert a (insert b Gamma.toFinset) := by
  have hweak := isWeakPath_cons_append_singleton hGamma hhead hlast ha hb
  have hextHead : (a :: Gamma ++ [b]).head? = some a := by rfl
  have hextLast : (a :: Gamma ++ [b]).getLast? = some b := by
    rw [List.getLast?_append_of_ne_nil (a :: Gamma) (by simp)]
    rfl
  obtain ⟨Delta, hDelta, hvertices⟩ :=
    Section5.Percolation.exists_isPathFrom_of_isWeakPath
      hweak hextHead hextLast hain hbout
  refine ⟨Delta, hDelta, ?_⟩
  rw [hvertices]
  simp only [List.toFinset_cons, List.toFinset_append, List.toFinset_nil,
    Finset.insert_empty]
  ext z
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- If every crossing path has at least `L` good distinct vertices, removing
the two unclaimed endpoint corrections loses at most `2d` good vertices. -/
theorem good_toFinset_card_lower_bound_of_isPathFrom_extension {d k L : ℕ}
    (hd : 0 < d) (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good]
    {Gamma Delta : List (Section5.Percolation.Site d)} {a b : Section5.Percolation.Site d}
    (hDelta : Section5.Percolation.IsPathFrom k Delta)
    (hvertices : Delta.toFinset = insert a (insert b Gamma.toFinset))
    (hcross : ∀ Xi : List (Section5.Percolation.Site d),
      Section5.Percolation.IsPathFrom k Xi → L ≤ (Xi.toFinset.filter Good).card) :
    L - 2 * d ≤ (Gamma.toFinset.filter Good).card := by
  have hgood := hcross Delta hDelta
  rw [hvertices] at hgood
  have hfilter : (insert a (insert b Gamma.toFinset)).filter Good ⊆
      insert a (insert b (Gamma.toFinset.filter Good)) := by
    intro z hz
    have hzmem := (Finset.mem_filter.mp hz).1
    rw [Finset.mem_insert] at hzmem ⊢
    rcases hzmem with rfl | hzmem
    · exact Or.inl rfl
    · rw [Finset.mem_insert] at hzmem ⊢
      rcases hzmem with rfl | hzmem
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hzmem, (Finset.mem_filter.mp hz).2⟩))
  have hcardFilter :
      ((insert a (insert b Gamma.toFinset)).filter Good).card ≤
        (Gamma.toFinset.filter Good).card + 2 := by
    refine (Finset.card_le_card hfilter).trans ?_
    calc
      (insert a (insert b (Gamma.toFinset.filter Good))).card ≤
          (insert b (Gamma.toFinset.filter Good)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (Gamma.toFinset.filter Good).card + 1 + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = (Gamma.toFinset.filter Good).card + 2 := by omega
  omega

end Algsuperdiff.Section5.Trace
