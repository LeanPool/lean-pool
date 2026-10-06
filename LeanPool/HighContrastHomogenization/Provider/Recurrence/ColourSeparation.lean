/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCell

/-!
# High-contrast homogenization: Provider.Recurrence.ColourSeparation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Colour separation for adapted cells

The finite-range averaging lemma colours an aligned adapted cell
`3^j 𝐪 w + ⋄_j^𝐪` by the residue of its index `w = 3^{-j}𝐪^{-1}z` modulo three.
The purpose of the rounded-grid design is that two distinct cells of the same
colour are separated in `ℓ^∞`-distance by at least one, which is what makes the
unit-range assumption applicable to them.

Two quantitative facts carry that conclusion.  The first is that a rounded grid
is uniformly positive: the normalization `𝓛(m)` is at least the identity and
the rounding perturbs the quadratic form by at most `d 3^{-ℓ} ≤ 1/101`, so
`𝐪 ≥ (100/101) I`.  Consequently the grid map cannot contract the sup norm by
more than the factor `(100/101)/d`.  The second is that at any scale at or above
the alignment the cells are large: `3^j ≥ 3^{k_0(d)} ≥ 101 d`, this being the
content of the choice of `k_0(d)`.  Two same-colour indices differ by at least
three in some coordinate, so the corresponding points of the two cells differ by
more than `2 · 3^j` in that coordinate before the grid map is applied, and by at
least `200` after it.

The colour classes themselves need no new carrier: the residue map
`w ↦ (w i mod 3)_i` takes values in `(ZMod 3)^d`, so a finite family of aligned
indices splits into at most `3^d` same-colour classes, the count the printed
proof uses.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The rounded grid is uniformly positive -/

/-- **A rounded grid is at least `100/101` times the identity.**  The
normalization is at least the identity and the rounding error moves the
quadratic form by at most `d 3^{-ℓ}`, which `kZero_spec` bounds by `1/101`. -/
theorem dotProduct_mulVec_roundedGrid_ge {l : ℤ} (hl : (kZero d : ℤ) ≤ l) {m : Mat d}
    (hm : m.PosDef) (x : Vec d) :
    (100 / 101 : ℝ) * (∑ i, x i * x i) ≤ x ⬝ᵥ roundedGrid l m *ᵥ x := by
  set L : Mat d := Real.sqrt (specBound m⁻¹) • matSqrt m with hL
  set E : Mat d := roundedGrid l m - L with hEdef
  have hS : (0 : ℝ) ≤ ∑ i, x i * x i := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hdelta : (d : ℝ) * (3 : ℝ) ^ (-l) ≤ 1 / 101 := by
    have hmono : (3 : ℝ) ^ (-l) ≤ (3 : ℝ) ^ (-(kZero d : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact le_trans (mul_le_mul_of_nonneg_left hmono (by positivity)) (kZero_spec d)
  have hEentry : ∀ i k, |E i k| ≤ (3 : ℝ) ^ (-l) := by
    intro i k
    obtain ⟨h0, h1⟩ := roundedGrid_sub_normalized_matSqrt_mem l m i k
    have hE : E i k = roundedGrid l m i k - Real.sqrt (specBound m⁻¹) * matSqrt m i k := rfl
    rw [hE, abs_of_nonneg h0]
    exact h1
  have hone : x ⬝ᵥ (1 : Mat d) *ᵥ x ≤ x ⬝ᵥ L *ᵥ x := by
    have hPS : (L - 1).PosSemidef := Matrix.le_iff.mp (one_le_normalized_matSqrt hm)
    have hnn := hPS.dotProduct_mulVec_nonneg x
    rw [Matrix.sub_mulVec, dotProduct_sub] at hnn
    simpa using hnn
  have hsq : x ⬝ᵥ (1 : Mat d) *ᵥ x = ∑ i, x i * x i := by
    simp [Matrix.one_mulVec, dotProduct]
  have hEbound := neg_le_dotProduct_mulVec_of_abs_entry_le hEentry x
  have hsmall : (3 : ℝ) ^ (-l) * (d : ℝ) * (∑ i, x i * x i)
      ≤ 1 / 101 * (∑ i, x i * x i) :=
    mul_le_mul_of_nonneg_right (by linarith only [hdelta]) hS
  have hexp : x ⬝ᵥ roundedGrid l m *ᵥ x = x ⬝ᵥ L *ᵥ x + x ⬝ᵥ E *ᵥ x := by
    have hsplit : roundedGrid l m = L + E := by rw [hEdef]; abel
    rw [hsplit, Matrix.add_mulVec, dotProduct_add]
  rw [hexp]
  rw [hsq] at hone
  linarith only [hone, hEbound, hsmall]

/-- **A rounded adapted grid is at least `100/101` times the identity.** -/
theorem dotProduct_mulVec_ge_of_isRoundedGrid {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) (x : Vec d) :
    (100 / 101 : ℝ) * (∑ i, x i * x i) ≤ x ⬝ᵥ q *ᵥ x := by
  obtain ⟨hl, m, hm, rfl⟩ := hq
  exact dotProduct_mulVec_roundedGrid_ge hl hm x

/-! ## The grid map does not contract the sup norm -/

/-- The sup norm of a vector is dominated by its Euclidean length. -/
private theorem sq_pi_norm_le_sum_sq (x : Vec d) : ‖x‖ ^ 2 ≤ ∑ i, x i * x i := by
  have hS : (0 : ℝ) ≤ ∑ i, x i * x i := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 : ‖x‖ ≤ Real.sqrt (∑ i, x i * x i) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    have hi := Finset.single_le_sum (f := fun k : Fin d => x k * x k)
      (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ i)
    nlinarith only [hi]
  nlinarith only [h1, hS, Real.sq_sqrt hS, norm_nonneg x, Real.sqrt_nonneg (∑ i, x i * x i)]

/-- **The grid map of a rounded adapted grid does not contract the sup norm by
more than `d · 101/100`.**  This is the quantitative form of positivity that the
colour separation consumes. -/
theorem norm_matVecMul_ge_of_isRoundedGrid {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    (x : Vec d) : (100 / 101 : ℝ) * ‖x‖ ≤ (d : ℝ) * ‖matVecMul q x‖ := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hxpos
  · rw [← hx0, mul_zero]
    positivity
  · have hquad := dotProduct_mulVec_ge_of_isRoundedGrid hq x
    have hsq := sq_pi_norm_le_sum_sq x
    have hterm : ∀ i : Fin d, x i * matVecMul q x i ≤ ‖x‖ * ‖matVecMul q x‖ := by
      intro i
      calc x i * matVecMul q x i ≤ |x i * matVecMul q x i| := le_abs_self _
        _ = |x i| * |matVecMul q x i| := abs_mul _ _
        _ ≤ ‖x‖ * ‖matVecMul q x‖ :=
            mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i)
              (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (matVecMul q x) i)
              (abs_nonneg _) (norm_nonneg _)
    have hdot : x ⬝ᵥ q *ᵥ x = ∑ i, x i * matVecMul q x i := rfl
    have hsum : x ⬝ᵥ q *ᵥ x ≤ (d : ℝ) * (‖x‖ * ‖matVecMul q x‖) := by
      have hb := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin d))
        (fun i => x i * matVecMul q x i) (‖x‖ * ‖matVecMul q x‖) fun i _ => hterm i
      rw [hdot]
      simpa [Finset.card_univ, nsmul_eq_mul] using hb
    have h1 : (100 / 101 : ℝ) * ‖x‖ ^ 2 ≤ (100 / 101 : ℝ) * (∑ i, x i * x i) :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    have hchain : ‖x‖ * ((100 / 101 : ℝ) * ‖x‖) ≤ ‖x‖ * ((d : ℝ) * ‖matVecMul q x‖) := by
      nlinarith only [h1, hquad, hsum]
    exact le_of_mul_le_mul_left hchain hxpos

/-! ## The cells are large above the alignment -/

/-- **`3^j ≥ 101 d` at every scale at or above the alignment of a rounded
grid.**  This is the second use of `kZero_spec`, and it is what makes the
`ℓ^∞`-separation of same-colour cells at least one rather than merely
positive. -/
theorem mul_le_zpow_three_of_isRoundedGrid {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {j : ℤ} (hj : l ≤ j) : (101 : ℝ) * (d : ℝ) ≤ (3 : ℝ) ^ j := by
  have hkj : (kZero d : ℤ) ≤ j := le_trans hq.1 hj
  have hkpos : (0 : ℝ) < (3 : ℝ) ^ ((kZero d : ℤ)) := by positivity
  have hspec := kZero_spec d
  rw [zpow_neg] at hspec
  have hmul := mul_le_mul_of_nonneg_right hspec hkpos.le
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hkpos), mul_one] at hmul
  have hmono : (3 : ℝ) ^ ((kZero d : ℤ)) ≤ (3 : ℝ) ^ j :=
    zpow_le_zpow_right₀ (by norm_num) hkj
  linarith only [hmul, hmono]

/-! ## Same-colour cells are unit separated -/

/-- **Two aligned adapted cells whose indices differ by a nonzero multiple of
three in some coordinate are `ℓ^∞`-separated by at least one.**  In fact they
are separated by at least `200`; the printed statement asks only for one. -/
theorem unitSeparated_adaptedCellAt_of_dvd_sub {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) {w w' : Fin d → ℤ} {i₀ : Fin d}
    (hne : w i₀ ≠ w' i₀) (hdvd : (3 : ℤ) ∣ (w i₀ - w' i₀)) :
    UnitSeparated (adaptedCellAt q j w) (adaptedCellAt q j w') := by
  have hdpos : 0 < d := Fin.pos i₀
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hgrid := mul_le_zpow_three_of_isRoundedGrid hq hj
  have hstep : (3 : ℤ) ≤ |w i₀ - w' i₀| :=
    Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hne)) ((dvd_abs 3 _).mpr hdvd)
  intro x y hx hy
  rw [adaptedCellAt_eq_image] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rw [mem_standardCell_iff] at hs ht
  have hdiff : matVecMul q s - matVecMul q t = matVecMul q (s - t) := by
    funext i
    show (∑ k, q i k * s k) - (∑ k, q i k * t k) = ∑ k, q i k * (s k - t k)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hcoord : 2 * (3 : ℝ) ^ j < |(s - t) i₀| := by
    obtain ⟨h1, h2⟩ := hs i₀
    obtain ⟨h3, h4⟩ := ht i₀
    have hval : (s - t) i₀ = s i₀ - t i₀ := rfl
    rcases abs_cases (w i₀ - w' i₀) with ⟨habs, _⟩ | ⟨habs, _⟩
    · have hZ : (3 : ℤ) ≤ w i₀ - w' i₀ := by omega
      have hR : (3 : ℝ) ≤ (w i₀ : ℝ) - (w' i₀ : ℝ) := by exact_mod_cast hZ
      have hprod : (0 : ℝ) ≤ ((w i₀ : ℝ) - (w' i₀ : ℝ) - 3) * (3 : ℝ) ^ j :=
        mul_nonneg (by linarith only [hR]) h3j.le
      have hgap : 2 * (3 : ℝ) ^ j < s i₀ - t i₀ := by linarith only [h1, h4, hprod]
      rw [hval]
      exact lt_of_lt_of_le hgap (le_abs_self _)
    · have hZ : w i₀ - w' i₀ ≤ -3 := by omega
      have hR : (w i₀ : ℝ) - (w' i₀ : ℝ) ≤ -3 := by exact_mod_cast hZ
      have hprod : (0 : ℝ) ≤ (-3 - ((w i₀ : ℝ) - (w' i₀ : ℝ))) * (3 : ℝ) ^ j :=
        mul_nonneg (by linarith only [hR]) h3j.le
      have hgap : s i₀ - t i₀ < -(2 * (3 : ℝ) ^ j) := by linarith only [h2, h3, hprod]
      rw [hval]
      exact lt_of_lt_of_le (by linarith only [hgap]) (neg_le_abs _)
  have hnorm : 2 * (3 : ℝ) ^ j < ‖s - t‖ :=
    lt_of_lt_of_le hcoord (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (s - t) i₀)
  have hlow := norm_matVecMul_ge_of_isRoundedGrid hq (s - t)
  have hsup : Source.AKL.supDist (matVecMul q s) (matVecMul q t)
      = ‖matVecMul q (s - t)‖ := by
    rw [show Source.AKL.supDist (matVecMul q s) (matVecMul q t)
        = ‖matVecMul q s - matVecMul q t‖ from rfl, hdiff]
  rw [hsup]
  have h200 : (d : ℝ) * 200 < (d : ℝ) * ‖matVecMul q (s - t)‖ := by
    linarith only [hlow, hnorm, hgrid]
  have hfinal : (200 : ℝ) < ‖matVecMul q (s - t)‖ :=
    lt_of_mul_lt_mul_left h200 (by linarith only [hdR])
  linarith only [hfinal]

/-- **Distinct same-colour aligned adapted cells are `ℓ^∞`-separated by at least
one.**  The colour is the residue of the index modulo three, the index being
`3^{-j}𝐪^{-1}z` for the cell centred at `z`. -/
theorem unitSeparated_adaptedCellAt_of_intCast_eq {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) {w w' : Fin d → ℤ} (hne : w ≠ w')
    (hcol : (fun i => ((w i : ZMod 3))) = fun i => ((w' i : ZMod 3))) :
    UnitSeparated (adaptedCellAt q j w) (adaptedCellAt q j w') := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  refine unitSeparated_adaptedCellAt_of_dvd_sub hq hj hi₀ ?_
  have hres : ((w i₀ : ZMod 3)) = ((w' i₀ : ZMod 3)) := congrFun hcol i₀
  have hmod := (ZMod.intCast_eq_intCast_iff' (w i₀) (w' i₀) 3).mp hres
  omega

/-! ## The colour classes -/

/-- **A finite family of aligned indices meets at most `3^d` colours.**  This is
the bound `K ≤ 3^d` of the printed proof. -/
theorem card_image_intCast_le (Z : Finset (Fin d → ℤ)) :
    (Z.image fun w i => ((w i : ZMod 3))).card ≤ 3 ^ d := by
  classical
  have hcard : Fintype.card (Fin d → ZMod 3) = 3 ^ d := by simp
  exact le_trans (Finset.card_le_univ _) hcard.le

/-- **A finite family of aligned indices is the union of its colour classes.**
Together with the separation of same-colour cells this is the decomposition
`I = I_1 ⊍ ⋯ ⊍ I_K` of the printed proof. -/
theorem biUnion_filter_intCast_eq (Z : Finset (Fin d → ℤ)) :
    (Z.image fun w i => ((w i : ZMod 3))).biUnion
        (fun c => Z.filter fun w => (fun i => ((w i : ZMod 3))) = c) = Z := by
  classical
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨c, -, hw, -⟩
    exact hw
  · intro hw
    exact ⟨fun i => ((w i : ZMod 3)), ⟨w, hw, rfl⟩, hw, rfl⟩

/-- **The colour classes of a finite family of aligned indices are disjoint.**
Together with the previous two facts this is the printed partition
`I = I_1 ⊍ ⋯ ⊍ I_K`, in the form a sum over `I` is split by it. -/
theorem pairwiseDisjoint_filter_intCast (Z : Finset (Fin d → ℤ)) :
    Set.PairwiseDisjoint (↑(Z.image fun w i => ((w i : ZMod 3))) : Set (Fin d → ZMod 3))
      fun c => Z.filter fun w => (fun i => ((w i : ZMod 3))) = c := by
  intro c _ c' _ hcc
  simp only [Function.onFun]
  refine Finset.disjoint_left.mpr fun w hw hw' => ?_
  exact hcc (((Finset.mem_filter.mp hw).2).symm.trans (Finset.mem_filter.mp hw').2)

/-- **The cells of a same-colour family of distinct aligned indices are pairwise
`ℓ^∞`-separated by at least one.**  This is the hypothesis the joint
independence of a colour class is proved from. -/
theorem pairwise_unitSeparated_adaptedCellAt {ι : Type*} {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) {z : ι → Fin d → ℤ}
    (hinj : Function.Injective z)
    (hcol : ∀ n n' : ι, (fun i => ((z n i : ZMod 3))) = fun i => ((z n' i : ZMod 3))) :
    Pairwise fun n n' : ι =>
      UnitSeparated (adaptedCellAt q j (z n)) (adaptedCellAt q j (z n')) :=
  fun n n' hnn =>
    unitSeparated_adaptedCellAt_of_intCast_eq hq hj (fun h => hnn (hinj h)) (hcol n n')

/-- The members of one colour class of a finite family of aligned indices all
carry that colour. -/
theorem intCast_eq_of_mem_filter {Z : Finset (Fin d → ℤ)} {c : Fin d → ZMod 3}
    {w w' : Fin d → ℤ} (hw : w ∈ Z.filter fun v => (fun i => ((v i : ZMod 3))) = c)
    (hw' : w' ∈ Z.filter fun v => (fun i => ((v i : ZMod 3))) = c) :
    (fun i => ((w i : ZMod 3))) = fun i => ((w' i : ZMod 3)) :=
  ((Finset.mem_filter.mp hw).2).trans ((Finset.mem_filter.mp hw').2).symm

end

end Recurrence
end HighContrast
end HCPolySupport
