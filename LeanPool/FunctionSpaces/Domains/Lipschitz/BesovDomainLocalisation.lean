/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.BesovDomains
public import LeanPool.FunctionSpaces.Domains.Sobolev.LipschitzDomainW1p
public import LeanPool.FunctionSpaces.Rd.Differences.PointwiseMultipliers
public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivativeChangeOfVariables

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Compactly supported functions on Besov domains

Let `Ω` be a Besov domain (`Rd.BesovDomain`) in a finite-dimensional real inner product space `V`
with Lebesgue measure, and `O = interior Ω`. Functions that vanish outside a ball `B(0, R)` are
described on the bounded convex pieces `D = O ∩ B(0, R')`, `R < R'`
(`Rd.BesovDomain.ballDomain`), which are bounded Lipschitz domains.

* `O` agrees with `Ω` up to a null set (`Rd.BesovDomain.interior_ae_eq`), since the frontier of a
  convex set is a null set.
* **Localisation** (`Rd.BesovDomain.modNormOn_lt_top_iff_ballDomain`): for such functions the
  intrinsic quasi-norm `N_Ω` is finite iff `N_D` is finite. One direction is the monotonicity in
  the set (`Rd.modNormOn_mono_set`); for the other, extend from `D`, multiply by a cutoff equal to
  `1` on `closedBall(0, R)` and supported in `B(0, R')`, and restrict to `Ω`. Multiplication by
  a smooth
  `χ` with compact support is bounded in the Besov quasi-norm by differences on `V`:
  `N(χ F) ≤ C N(F)` (`Rd.exists_mul_modNorm_le`).
* **`W^1_2 = B^1_{2,2}`** (`Rd.BesovDomain.exists_hasWeakLineDeriv_iff_modNormOn_lt_top`): such a
  function has a weak gradient on `O` with values in `L_2(O)` iff its intrinsic quasi-norm on `Ω`
  with `p = q = 2`, `s = 1` and moduli of any order `r ≥ 2` is finite: through
  `H^1(D) = W^1_2(D)` on the pieces in one direction, and through the extension property of `Ω`
  and `W^1_2(V) = B^1_{2,2}(V)` in the other.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set TopologicalSpace Module
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Bounded convex pieces of a Besov domain -/

namespace BesovDomain

variable (Ω : Set V) [BesovDomain Ω]

/-- **A Besov domain is its interior up to a null set**: the frontier of the convex set `Ω` is a
null set (Mathlib's `Convex.addHaar_frontier`, `interior_ae_eq_of_null_frontier`). -/
theorem interior_ae_eq : interior Ω =ᵐ[volume] Ω :=
  interior_ae_eq_of_null_frontier ((convex (Ω := Ω)).addHaar_frontier volume)

/-- Lebesgue measure restricted to the interior of a Besov domain is Lebesgue measure restricted
to the domain (`Rd.BesovDomain.interior_ae_eq`). -/
theorem restrict_interior : volume.restrict (interior Ω) = volume.restrict Ω :=
  Measure.restrict_congr_set (interior_ae_eq Ω)

/-- **The bounded convex piece** `O ∩ B(0, R)` of a Besov domain `Ω`, `O = interior Ω`, as a
bounded Lipschitz domain: it is open, bounded and convex
(`Rd.BoundedLipschitzDomain.ofConvex`). -/
noncomputable def ballDomain (R : ℝ) : BoundedLipschitzDomain V :=
  BoundedLipschitzDomain.ofConvex ((convex (Ω := Ω)).interior.inter (convex_ball 0 R))
    (isOpen_interior.inter isOpen_ball) (isBounded_ball.subset inter_subset_right)

/-- The carrier of the piece `Rd.BesovDomain.ballDomain Ω R` is `interior Ω ∩ B(0, R)`. -/
@[simp]
theorem carrier_ballDomain (R : ℝ) : (ballDomain Ω R).carrier = interior Ω ∩ ball 0 R :=
  rfl

/-- The piece `O ∩ B(0, R)` lies in `O = interior Ω`, as open sets. -/
theorem toOpens_ballDomain_le (R : ℝ) : (ballDomain Ω R).toOpens ≤ Opens.interior Ω :=
  fun _ hx => hx.1

/-- The piece `O ∩ B(0, R)` lies in `O = interior Ω`. -/
theorem ballDomain_subset_interior (R : ℝ) : (ballDomain Ω R).carrier ⊆ interior Ω :=
  fun _ hx => hx.1

/-- The piece `O ∩ B(0, R)` lies in `Ω`. -/
theorem ballDomain_subset (R : ℝ) : (ballDomain Ω R).carrier ⊆ Ω :=
  (ballDomain_subset_interior Ω R).trans interior_subset

/-! ### Localisation of the intrinsic quasi-norm -/

variable {Ω}

/-- **The cutoff identity**: let `g = 0` almost everywhere outside `B(0, R)`, `F = g` almost
everywhere on `D = O ∩ B(0, R')`, and let `χ` be `1` on `closedBall(0, R)` with closed support in
`B(0, R')`. Then `χ F = g` almost everywhere on `Ω`: on `D` because `χ g = g`, outside
`B(0, R')` because both sides vanish, and `Ω \ O` is a null set
(`Rd.BesovDomain.restrict_interior`). -/
theorem mul_ae_eq_of_ballDomain {p : ℝ≥0∞} {R R' : ℝ} (hR : R ≤ R')
    {g F : Lp ℂ p (volume : Measure V)} (hg : ∀ᵐ y ∂volume, y ∉ ball (0 : V) R → g y = 0)
    (hFg : (F : V → ℂ) =ᵐ[volume.restrict (ballDomain Ω R').carrier] g) {χ : V → ℝ}
    (hχU : tsupport χ ⊆ ball 0 R') (hχ1 : ∀ x ∈ Metric.closedBall (0 : V) R, χ x = 1) :
    (fun x => (χ x : ℂ) * F x) =ᵐ[volume.restrict Ω] g := by
  rw [← restrict_interior Ω]
  refine (ae_restrict_iff' measurableSet_interior).2 ?_
  have hF := (ae_restrict_iff' (ballDomain Ω R').measurableSet).1 hFg
  filter_upwards [hF, hg] with y h2 h3 hy
  by_cases hyR' : y ∈ ball (0 : V) R'
  · rw [h2 (by rw [carrier_ballDomain]; exact ⟨hy, hyR'⟩)]
    by_cases hyR : y ∈ ball (0 : V) R
    · rw [hχ1 y (ball_subset_closedBall hyR), Complex.ofReal_one, one_mul]
    · rw [h3 hyR, mul_zero]
  · have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hyR' (hχU h)
    rw [h0, Complex.ofReal_zero, zero_mul, h3 fun h => hyR' (ball_subset_ball hR h)]

/-- **From a bounded convex piece to the Besov domain**: for `1 ≤ p < ∞`, `0 < s < r`,
`1 ≤ q ≤ ∞`, `R < R'` and `g ∈ L_p(V)` vanishing almost everywhere outside `B(0, R)`, if the
intrinsic quasi-norm `N_D(g)` on the piece `D = O ∩ B(0, R')` is finite, so is `N_Ω(g)`. The piece
has the extension property (`Rd.BoundedLipschitzDomain.hasBesovExtension`), which gives `F` on `V`
with `F = g` on `D`; for a smooth cutoff `χ` equal to `1` on `closedBall(0, R)` with compact
support in
`B(0, R')` (`Rd.exists_contDiff_eventuallyEq_one`), `χ F` has finite quasi-norm on `V`
(`Rd.exists_mul_modNorm_le`) and agrees with `g` on `Ω` (`Rd.BesovDomain.mul_ae_eq_of_ballDomain`),
so `N_Ω(g)` is finite (`Rd.modNormOn_le_modNorm_of_indicatorLp`). -/
theorem modNormOn_lt_top_of_ballDomain {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {r : ℕ} {s : ℝ}
    (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) {R R' : ℝ} (hR : R < R')
    {g : Lp ℂ p (volume : Measure V)} (hg : ∀ᵐ y ∂volume, y ∉ ball (0 : V) R → g y = 0)
    (hD : modNormOn (ballDomain Ω R').measurableSet r s q g < ∞) :
    modNormOn (measurableSet Ω) r s q g < ∞ := by
  obtain ⟨C, hC, hext⟩ := (ballDomain Ω R').hasBesovExtension p hp r s hs hsr q hq
  obtain ⟨F, hFg, hFle⟩ := hext g hD
  obtain ⟨χ, hχ, hχc, hχU, -, hχ1⟩ := exists_contDiff_eventuallyEq_one
    (isCompact_closedBall (0 : V) R) isOpen_ball (closedBall_subset_ball hR)
  obtain ⟨C', hC', hmul⟩ := exists_mul_modNorm_le hp (Complex.ofRealCLM.contDiff.comp hχ)
    (hχc.comp_left Complex.ofReal_zero) hsr hq
  obtain ⟨G, hG, hGle⟩ := hmul F
  have hG' : (G : V → ℂ) =ᵐ[volume.restrict Ω] fun x => (χ x : ℂ) * F x :=
    ae_restrict_of_ae hG
  have hGg : indicatorLp (measurableSet Ω) G = indicatorLp (measurableSet Ω) g :=
    (indicatorLp_eq_iff_ae_eq_restrict _).2 (hG'.trans (mul_ae_eq_of_ballDomain hR.le hg
      ((indicatorLp_eq_iff_ae_eq_restrict _).1 hFg) hχU (Eventually.self_of_nhdsSet hχ1)))
  exact (modNormOn_le_modNorm_of_indicatorLp (measurableSet Ω) r s q hGg).trans_lt
    (hGle.trans_lt (ENNReal.mul_lt_top hC'.lt_top
      (hFle.trans_lt (ENNReal.mul_lt_top hC.lt_top hD))))

/-- **Localisation on Besov domains**: for `1 ≤ p < ∞`, `0 < s < r`, `1 ≤ q ≤ ∞`, `R < R'` and
every `g ∈ L_p(V)` vanishing almost everywhere outside `B(0, R)`, the intrinsic quasi-norm of `g`
on `Ω` is finite iff the one on the bounded convex piece `D = O ∩ B(0, R')` is finite:
`N_D(g) ≤ N_Ω(g)` (`Rd.modNormOn_mono_set`), and
`Rd.BesovDomain.modNormOn_lt_top_of_ballDomain`. -/
theorem modNormOn_lt_top_iff_ballDomain {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {r : ℕ} {s : ℝ}
    (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) {R R' : ℝ} (hR : R < R')
    {g : Lp ℂ p (volume : Measure V)} (hg : ∀ᵐ y ∂volume, y ∉ ball (0 : V) R → g y = 0) :
    modNormOn (measurableSet Ω) r s q g < ∞ ↔
      modNormOn (ballDomain Ω R').measurableSet r s q g < ∞ :=
  ⟨fun h => (modNormOn_mono_set _ _ (ballDomain_subset Ω R') r s q g).trans_lt h,
    modNormOn_lt_top_of_ballDomain hp hs hsr hq hR hg⟩

/-! ### The weak gradient on the interior -/

/-- **A finite intrinsic `B^1_{2,2}` quasi-norm gives a weak gradient**: if `g ∈ L_2(V)` has
`‖g‖_{L_2(Ω)} + ‖(2^k ω_r(g, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞` for an order `r ≥ 2`, then `g` has
weak derivatives `∂_{e_j} g ∈ L_2(O)` on `O = interior Ω` along the basis vectors
`e_j = Rd.gridBasis V j`. The extension property of `Ω` gives `F` on `V` with `F = g` on `Ω`
and finite `B^1_{2,2}(V)` quasi-norm, so `F ∈ W^1_2(V)` (`Rd.memSobolev_one_iff_modulus`); its
weak derivatives restrict to `O` (`Rd.HasWeakLineDeriv.mono`, `Rd.HasWeakLineDeriv.congr_ae`). -/
theorem exists_hasWeakLineDeriv_of_modNormOn_lt_top {r : ℕ} (hr : 2 ≤ r)
    {g : Lp ℂ 2 (volume : Measure V)} (hg : modNormOn (measurableSet Ω) r 1 2 g < ∞) :
    ∃ g' : Fin (finrank ℝ V) → Lp ℂ 2 (volume.restrict (interior Ω)),
      ∀ j, HasWeakLineDeriv (Opens.interior Ω) (fun _ : Fin 1 => gridBasis V j) g (g' j) := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hr
  obtain ⟨C, hC, hext⟩ := hasBesovExtension Ω 2 two_ne_top r 1 one_pos hr' 2 one_le_two
  obtain ⟨F, hFg, hFle⟩ := hext g hg
  have hF : MemSobolev 1 F := (memSobolev_one_iff_modulus hr F).2
    (hFle.trans_lt (ENNReal.mul_lt_top hC.lt_top hg))
  have hFg' : (F : V → ℂ) =ᵐ[volume.restrict (interior Ω)] g :=
    ae_mono (Measure.restrict_mono interior_subset le_rfl)
      ((indicatorLp_eq_iff_ae_eq_restrict _).1 hFg)
  choose G hG hFG using fun j : Fin (finrank ℝ V) => hF.2 1 le_rfl fun _ => gridBasis V j
  have hG' : ∀ j, MemLp (G j) 2 (volume.restrict (interior Ω)) := fun j =>
    (hG j).mono_measure (by rw [volume_restrict_top]; exact Measure.restrict_le_self)
  exact ⟨fun j => (hG' j).toLp _, fun j =>
    ((hFG j).mono le_top).congr_ae hFg' (hG' j).coeFn_toLp.symm⟩

/-- **A weak gradient gives a finite intrinsic `B^1_{2,2}` quasi-norm**: if `g ∈ L_2(V)` vanishes
almost everywhere outside `B(0, R)` and has weak derivatives `g'_j = ∂_{e_j} g ∈ L_2(O)` on
`O = interior Ω` along the basis vectors `e_j`, then
`‖g‖_{L_2(Ω)} + ‖(2^k ω_r(g, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞` for every order `r ≥ 2`. On the piece
`D = O ∩ B(0, R + 1)`, `g ∈ W^1_2(D) = H^1(D)` (`Rd.memWeakSobolev_one_of_forall_gridBasis`,
`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`), whose intrinsic quasi-norm is finite
(`Rd.BoundedLipschitzDomain.memSobolevOn_iff_modulusOn`); localisation passes to `Ω`
(`Rd.BesovDomain.modNormOn_lt_top_of_ballDomain`). -/
theorem modNormOn_lt_top_of_hasWeakLineDeriv {r : ℕ} (hr : 2 ≤ r) {R : ℝ}
    {g : Lp ℂ 2 (volume : Measure V)} (hg : ∀ᵐ y ∂volume, y ∉ ball (0 : V) R → g y = 0)
    {g' : Fin (finrank ℝ V) → Lp ℂ 2 (volume.restrict (interior Ω))}
    (h : ∀ j, HasWeakLineDeriv (Opens.interior Ω) (fun _ : Fin 1 => gridBasis V j) g (g' j)) :
    modNormOn (measurableSet Ω) r 1 2 g < ∞ := by
  have hW : MemWeakSobolev (ballDomain Ω (R + 1)).toOpens 1 2 g :=
    memWeakSobolev_one_of_forall_gridBasis one_le_two ((Lp.memLp g).restrict _)
      (fun j => (Lp.memLp (g' j)).mono_measure
        (Measure.restrict_mono (ballDomain_subset_interior Ω _) le_rfl))
      fun j => (h j).mono (toOpens_ballDomain_le Ω _)
  have hD := ((ballDomain Ω (R + 1)).memSobolevOn_iff_modulusOn hr g).1
    (((ballDomain Ω (R + 1)).memSobolevOn_iff_memWeakSobolev g).2 hW)
  exact modNormOn_lt_top_of_ballDomain (r := r) (s := 1) two_ne_top one_pos
    (by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hr) one_le_two (lt_add_one R) hg hD

/-- **`W^1_2 = B^1_{2,2}` for compactly supported functions on a Besov domain**: for every
`g ∈ L_2(V)` vanishing almost everywhere outside a ball `B(0, R)`, `g` has weak derivatives
`∂_{e_j} g ∈ L_2(O)` on `O = interior Ω` along the basis vectors `e_j = Rd.gridBasis V j` iff
`‖g‖_{L_2(Ω)} + ‖(2^k ω_r(g, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞`, for every order `r ≥ 2`
(`Rd.BesovDomain.modNormOn_lt_top_of_hasWeakLineDeriv`,
`Rd.BesovDomain.exists_hasWeakLineDeriv_of_modNormOn_lt_top`). -/
theorem exists_hasWeakLineDeriv_iff_modNormOn_lt_top {r : ℕ} (hr : 2 ≤ r) {R : ℝ}
    {g : Lp ℂ 2 (volume : Measure V)} (hg : ∀ᵐ y ∂volume, y ∉ ball (0 : V) R → g y = 0) :
    (∃ g' : Fin (finrank ℝ V) → Lp ℂ 2 (volume.restrict (interior Ω)),
      ∀ j, HasWeakLineDeriv (Opens.interior Ω) (fun _ : Fin 1 => gridBasis V j) g (g' j)) ↔
      modNormOn (measurableSet Ω) r 1 2 g < ∞ :=
  ⟨fun ⟨_, h⟩ => modNormOn_lt_top_of_hasWeakLineDeriv hr hg h,
    exists_hasWeakLineDeriv_of_modNormOn_lt_top hr⟩

end BesovDomain

end Rd
