/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
import LeanPool.CCDN.Algebra.BinomialSectionBound
import LeanPool.CCDN.Algebra.GridPointInterpolation
import Mathlib.Data.Nat.Choose.Bounds

/-! A coordinate-grid bound for a proper complete intersection. The
constant depends only on the ambient dimension; the degree dependence
is quadratic. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If `f` is prime, `g` is not divisible by `f`, and both have total degree at most `d`, then the
number of distinct common zeros of `f` and `g` in the grid `Sⁿ⁺²` is at most `(n + 2) ^ n · d² · |S|
^ n`. -/
theorem proper_intersection_grid_card_le {K ι : Type*} [Field K]
    [Fintype ι] {n d : ℕ}
    (f g : MvPolynomial (Fin (n + 2)) K) (hf : Prime f) (hfg : ¬ f ∣ g)
    (hfd : f.totalDegree ≤ d) (hgd : g.totalDegree ≤ d)
    (S : Finset K) (z : ι → Fin (n + 2) → K) (hz : Function.Injective z)
    (hzS : ∀ i j, z i j ∈ S) (hzf : ∀ i, eval (z i) f = 0)
    (hzg : ∀ i, eval (z i) g = 0) :
    Fintype.card ι ≤ (n + 2) ^ n * d ^ 2 * S.card ^ n := by
  classical
  let L := S.card
  have hbox : Fintype.card ι ≤ L ^ (n + 2) := by
    let ψ : ι → (Fintype.piFinset (fun _ : Fin (n + 2) => S)) :=
      fun i => ⟨z i, Fintype.mem_piFinset.mpr (hzS i)⟩
    have hinj : Function.Injective ψ := by
      intro i j h
      exact hz (congrArg Subtype.val h)
    simpa only [Fintype.card_coe, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, L] using Fintype.card_le_of_injective ψ hinj
  by_cases hL : L = 0
  · have hz0 : Fintype.card ι = 0 :=
      Nat.eq_zero_of_le_zero (by simpa only [hL, pow_succ, mul_zero] using hbox)
    rw [hz0]
    exact Nat.zero_le _
  have hL1 : 1 ≤ L := by omega
  let N := (n + 2) * (L - 1)
  by_cases hN : f.totalDegree + g.totalDegree ≤ N
  · let I : Ideal (MvPolynomial (Fin (n + 2)) K) := Ideal.span {f, g}
    have hIf : f ∈ I := Ideal.subset_span (by simp)
    have hIg : g ∈ I := Ideal.subset_span (by simp)
    have hzI (i : ι) (q : MvPolynomial (Fin (n + 2)) K) (hq : q ∈ I) :
        eval (z i) q = 0 := by
      have hker : I ≤ RingHom.ker (eval (z i)) := by
        apply Ideal.span_le.mpr
        intro p hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp
        · exact hzf i
        · have hp' : p = g := Set.mem_singleton_iff.mp hp
          subst p
          exact hzg i
      exact hker hq
    have hlower : Fintype.card ι ≤ Module.finrank K (filteredCoordinateSpace I N) :=
      grid_points_filtered_lower I S z hz hzS hzI (by simp only [Fintype.card_fin]; rfl)
    have hupper := filteredCoordinateSpace_codim_two_bound hf hfg I hIf hIg hN
    have hchoose : (n + N).choose n ≤ ((n + 2) * L) ^ n := by
      calc
        _ ≤ (N + 1) ^ n := by
          simpa only [Nat.add_comm n N] using Nat.choose_add_le_add_one_pow N n
        _ ≤ _ := Nat.pow_le_pow_left (by
          have he : (n + 2) * (L - 1) + (n + 2) = (n + 2) * L := by
            rw [← Nat.mul_add_one, Nat.sub_add_cancel hL1]
          dsimp only [N]
          omega) n
    calc
      _ ≤ f.totalDegree * g.totalDegree * (n + N).choose n := hlower.trans hupper
      _ ≤ d * d * (((n + 2) * L) ^ n) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfd hgd) hchoose
      _ = _ := by simp only [mul_pow, L]; ring
  · have htwo : 2 * (L - 1) ≤ N := Nat.mul_le_mul_right (L - 1) (by omega)
    have hLd : L ≤ d := by omega
    have hconst : 1 ≤ (n + 2) ^ n :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    calc
      _ ≤ L ^ (n + 2) := hbox
      _ = L ^ 2 * L ^ n := by rw [pow_add]; ring
      _ ≤ d ^ 2 * L ^ n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hLd 2)
      _ ≤ (n + 2) ^ n * (d ^ 2 * L ^ n) := Nat.le_mul_of_pos_left _ hconst
      _ = _ := by rw [Nat.mul_assoc]

end
end CCDN
