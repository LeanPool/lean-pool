/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkin
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.ApproxSpaces

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Triebel–Lizorkin spaces on `V` and real interpolation

Let `1 ≤ p < ∞`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`.  The Triebel–Lizorkin quasi-norm of
`F^s_{p,q}` lies between the dyadic quasi-norms of `B^s_{p,max(p,q)}` and `B^s_{p,min(p,q)}`
(`Rd.approxNormDyadic_le_triebelLizorkinNorm`, `Rd.triebelLizorkinNorm_le_approxNormDyadic`),
so the sandwich principle gives, for `0 < s₀ < s₁` and `s = (1-η)s₀ + ηs₁`,

`(F^{s₀}_{p,q₀}, F^{s₁}_{p,q₁})_{η,q} = B^s_{p,q}` and `(L_p, F^{s₁}_{p,q₁})_{η,q} = B^{ηs₁}_{p,q}`

(`Rd.memKMethod_triebelLizorkinCouple_iff`, `Rd.memKMethod_lpTriebelLizorkinCouple_iff`), and the
same for every couple of quasi-norms equivalent to these
(`Rd.memKMethod_iff_memApprox_of_triebelLizorkin_equiv`,
`Rd.memKMethod_iff_memApprox_of_triebelLizorkin_equiv_left`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ η : ℝ}
  {q₀ q₁ q : ℝ≥0∞}

/-! ### Triebel–Lizorkin spaces -/

/-- The **couple `(F^{s₀}_{p,q₀}, F^{s₁}_{p,q₁})`** on `L_p(V)`: the two Triebel–Lizorkin
quasi-norms. -/
noncomputable def triebelLizorkinCouple (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ) (q₁ : ℝ≥0∞) :
    InterpCouple (Lp ℂ p (volume : Measure V)) :=
  ⟨triebelLizorkinNorm s₀ q₀, triebelLizorkinNorm s₁ q₁⟩

omit [Fact (1 ≤ p)] in
/-- The first norm of `(F^{s₀}_{p,q₀}, F^{s₁}_{p,q₁})` is the quasi-norm of `F^{s₀}_{p,q₀}`. -/
@[simp]
theorem triebelLizorkinCouple_norm0 (f : Lp ℂ p (volume : Measure V)) :
    (triebelLizorkinCouple s₀ q₀ s₁ q₁).norm0 f = triebelLizorkinNorm s₀ q₀ f := rfl

omit [Fact (1 ≤ p)] in
/-- The second norm of `(F^{s₀}_{p,q₀}, F^{s₁}_{p,q₁})` is the quasi-norm of `F^{s₁}_{p,q₁}`. -/
@[simp]
theorem triebelLizorkinCouple_norm1 (f : Lp ℂ p (volume : Measure V)) :
    (triebelLizorkinCouple s₀ q₀ s₁ q₁).norm1 f = triebelLizorkinNorm s₁ q₁ f := rfl

/-- The **couple `(L_p, F^{s₁}_{p,q₁})`** on `L_p(V)`: the `L_p` norm and the Triebel–Lizorkin
quasi-norm. -/
noncomputable def lpTriebelLizorkinCouple (s₁ : ℝ) (q₁ : ℝ≥0∞) :
    InterpCouple (Lp ℂ p (volume : Measure V)) :=
  ⟨fun f => ‖f‖ₑ, triebelLizorkinNorm s₁ q₁⟩

/-- The first norm of `(L_p, F^{s₁}_{p,q₁})` is the `L_p` norm. -/
@[simp]
theorem lpTriebelLizorkinCouple_norm0 (f : Lp ℂ p (volume : Measure V)) :
    (lpTriebelLizorkinCouple s₁ q₁).norm0 f = ‖f‖ₑ := rfl

/-- The second norm of `(L_p, F^{s₁}_{p,q₁})` is the quasi-norm of `F^{s₁}_{p,q₁}`. -/
@[simp]
theorem lpTriebelLizorkinCouple_norm1 (f : Lp ℂ p (volume : Measure V)) :
    (lpTriebelLizorkinCouple s₁ q₁).norm1 f = triebelLizorkinNorm s₁ q₁ f := rfl

/-- **Triebel–Lizorkin spaces interpolate to Besov spaces** (Triebel 1978,
Section 2.4): for `1 ≤ p < ∞`, `0 < s₀ < s₁`, `0 < η < 1` and
`1 ≤ q₀, q₁, q ≤ ∞`, `f ∈ L_p(V)` lies in the real interpolation space
`(F^{s₀}_{p,q₀}, F^{s₁}_{p,q₁})_{η,q}` iff `f` lies in the Besov space
`B^{(1-η)s₀+ηs₁}_{p,q}(V)`, the approximation space of the band-limited scheme.  The
Triebel–Lizorkin quasi-norms lie between two Besov quasi-norms of the same smoothness
(`ApproximationScheme.memKMethod_iff_memApprox_of_two_sandwiches`). -/
theorem memKMethod_triebelLizorkinCouple_iff (hp : p ≠ ∞) (hs₀ : 0 < s₀) (hs : s₀ < s₁)
    (hη : 0 < η) (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} :
    (triebelLizorkinCouple s₀ q₀ s₁ q₁).MemKMethod η q f ↔
      (bandScheme hp).MemApprox ((1 - η) * s₀ + η * s₁) q f :=
  ApproximationScheme.memKMethod_iff_memApprox_of_two_sandwiches
    (N₀ := triebelLizorkinNorm s₀ q₀) (N₁ := triebelLizorkinNorm s₁ q₁)
    (eight_mul_dyadicWeight_mul_eLpNorm_lpKernel_ne_top s₀)
    (ENNReal.two_mul_one_sub_two_rpow_neg_inv_ne_top hs₀)
    (eight_mul_dyadicWeight_mul_eLpNorm_lpKernel_ne_top s₁)
    (ENNReal.two_mul_one_sub_two_rpow_neg_inv_ne_top (hs₀.trans hs)) (le_min Fact.out hq₀)
    (le_max_of_le_right hq₀) (le_min Fact.out hq₁) (le_max_of_le_right hq₁) hs₀ hs hη hη' hq
    (triebelLizorkinNorm_le_approxNormDyadic hp hs₀.le hq₀)
    (approxNormDyadic_le_triebelLizorkinNorm hp hs₀ hq₀)
    (triebelLizorkinNorm_le_approxNormDyadic hp (hs₀.trans hs).le hq₁)
    (approxNormDyadic_le_triebelLizorkinNorm hp (hs₀.trans hs) hq₁)

/-- **`L_p` and a Triebel–Lizorkin space interpolate to Besov spaces**: for `1 ≤ p < ∞`,
`s₁ > 0`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, `f ∈ L_p(V)` lies in the real interpolation space
`(L_p, F^{s₁}_{p,q₁})_{η,q}` iff `f` lies in the Besov space `B^{ηs₁}_{p,q}(V)`
(`ApproximationScheme.memKMethod_iff_memApprox_of_sandwich`). -/
theorem memKMethod_lpTriebelLizorkinCouple_iff (hp : p ≠ ∞) (hs₁ : 0 < s₁) (hη : 0 < η)
    (hη' : η < 1) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} :
    (lpTriebelLizorkinCouple s₁ q₁).MemKMethod η q f ↔ (bandScheme hp).MemApprox (η * s₁) q f :=
  ApproximationScheme.memKMethod_iff_memApprox_of_sandwich (N₁ := triebelLizorkinNorm s₁ q₁)
    (eight_mul_dyadicWeight_mul_eLpNorm_lpKernel_ne_top s₁)
    (ENNReal.two_mul_one_sub_two_rpow_neg_inv_ne_top hs₁) (le_min Fact.out hq₁)
    (le_max_of_le_right hq₁) hs₁ hη hη' hq (triebelLizorkinNorm_le_approxNormDyadic hp hs₁.le hq₁)
    (approxNormDyadic_le_triebelLizorkinNorm hp hs₁ hq₁)

/-- **Couples equivalent to Triebel–Lizorkin couples interpolate to Besov spaces**: for
`1 ≤ p < ∞`, `0 < s₀ < s₁`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, if `N₀` is equivalent to the
quasi-norm of `F^{s₀}_{p,q₀}` and `N₁` to that of `F^{s₁}_{p,q₁}`, with finite constants, then
`f ∈ (N₀, N₁)_{η,q}` iff `f ∈ B^{(1-η)s₀+ηs₁}_{p,q}(V)` (`InterpCouple.memKMethod_congr`). -/
theorem memKMethod_iff_memApprox_of_triebelLizorkin_equiv (hp : p ≠ ∞)
    {N₀ N₁ : Lp ℂ p (volume : Measure V) → ℝ≥0∞} {c₀ c₀' c₁ c₁' : ℝ≥0∞} (hc₀ : c₀ ≠ ∞)
    (hc₀' : c₀' ≠ ∞) (hc₁ : c₁ ≠ ∞) (hc₁' : c₁' ≠ ∞) (hs₀ : 0 < s₀) (hs : s₀ < s₁)
    (hη : 0 < η) (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (h₀ : ∀ f, N₀ f ≤ c₀ * triebelLizorkinNorm s₀ q₀ f)
    (h₀' : ∀ f, triebelLizorkinNorm s₀ q₀ f ≤ c₀' * N₀ f)
    (h₁ : ∀ f, N₁ f ≤ c₁ * triebelLizorkinNorm s₁ q₁ f)
    (h₁' : ∀ f, triebelLizorkinNorm s₁ q₁ f ≤ c₁' * N₁ f) {f : Lp ℂ p (volume : Measure V)} :
    (⟨N₀, N₁⟩ : InterpCouple (Lp ℂ p (volume : Measure V))).MemKMethod η q f ↔
      (bandScheme hp).MemApprox ((1 - η) * s₀ + η * s₁) q f :=
  (InterpCouple.memKMethod_congr (A := ⟨N₀, N₁⟩) (B := triebelLizorkinCouple s₀ q₀ s₁ q₁)
    hc₀' hc₁' hc₀ hc₁ h₀' h₁' h₀ h₁).trans
    (memKMethod_triebelLizorkinCouple_iff hp hs₀ hs hη hη' hq₀ hq₁ hq)

/-- **Couples of `L_p` and a quasi-norm equivalent to a Triebel–Lizorkin quasi-norm interpolate to
Besov spaces**: for `1 ≤ p < ∞`, `s₁ > 0`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, if `N₁` is
equivalent to the quasi-norm of `F^{s₁}_{p,q₁}` with finite constants, then
`f ∈ (L_p, N₁)_{η,q}` iff `f ∈ B^{ηs₁}_{p,q}(V)`. -/
theorem memKMethod_iff_memApprox_of_triebelLizorkin_equiv_left (hp : p ≠ ∞)
    {N₁ : Lp ℂ p (volume : Measure V) → ℝ≥0∞} {c₁ c₁' : ℝ≥0∞} (hc₁ : c₁ ≠ ∞) (hc₁' : c₁' ≠ ∞)
    (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (h₁ : ∀ f, N₁ f ≤ c₁ * triebelLizorkinNorm s₁ q₁ f)
    (h₁' : ∀ f, triebelLizorkinNorm s₁ q₁ f ≤ c₁' * N₁ f) {f : Lp ℂ p (volume : Measure V)} :
    (⟨fun f => ‖f‖ₑ, N₁⟩ : InterpCouple (Lp ℂ p (volume : Measure V))).MemKMethod η q f ↔
      (bandScheme hp).MemApprox (η * s₁) q f :=
  (InterpCouple.memKMethod_congr (A := ⟨fun f => ‖f‖ₑ, N₁⟩)
    (B := lpTriebelLizorkinCouple s₁ q₁) ENNReal.one_ne_top hc₁' ENNReal.one_ne_top hc₁
    (fun a => (one_mul ‖a‖ₑ).ge) h₁' (fun a => (one_mul ‖a‖ₑ).ge) h₁).trans
    (memKMethod_lpTriebelLizorkinCouple_iff hp hs₁ hη hη' hq₁ hq)

end Rd
