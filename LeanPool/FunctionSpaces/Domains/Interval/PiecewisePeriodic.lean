/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.PiecewiseInverse
public import LeanPool.FunctionSpaces.Domains.Interval.Periodic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Piecewise polynomials on the circle

On the circle `𝕋 = ℝ/ℤ`, identified with `[0, 1)` through the periodic extension
`fTilde(x) = f(x - ⌊x⌋)`, the dyadic piecewise polynomials are the same functions as on `[0, 1)`,
so their scheme is `Interval.ppScheme` in `L_p[0, 1] = L_p(𝕋)`. Only the modulus changes: the
periodic modulus `ω_r^per(f, t)_p` of `FunctionSpaces.Domains.Interval.Periodic` also sees the knot
`0 = 1` of the circle.

* **Jackson's inequality** `E_{2^k}(f)_p ≤ C ω_r^per(f, 2^(-k))_p` at every level follows from
  the one on `[0, 1]`, since the periodic modulus is the larger one
  (`Interval.exists_approxError_ppScheme_le_per`).
* **The inverse inequality** `ω_r^per(a, 2^(-k))_p ≤ C_B 2^(-(k-j)/p) ‖a‖_p` for `a ∈ V_j`
  (`Interval.exists_inverse_ppScheme_per`) is the local inverse estimate for the periodic
  extension, which is a piecewise polynomial on `[0, ∞)` (`Interval.isPiecewisePoly_perExt_ppFun`)
  whose `2^j` consecutive pieces always make up one period
  (`Interval.sum_localMass_perExt_le`).

Hence for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 ≤ s < 1/p`,
`f ∈ A^s_q ↔ ‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
(`Interval.memApprox_ppScheme_iff_per`): the approximation space is the Besov space
`B^s_{p,q}(𝕋)` for `0 < s < 1/p`. Comparing with `Interval.memApprox_ppScheme_iff`, the Besov
spaces `B^s_{p,q}[0, 1]` and `B^s_{p,q}(𝕋)` contain the same functions for `0 < s < 1/p`
(`Interval.lqNorm_modulus_lt_top_iff_perModulus`): below smoothness `1/p` a jump between the
ends of the interval does not count.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **pieces of the periodic extension** of a piecewise polynomial of level `k`: on `I_{k,m}`
with `m = m' + 2^k c`, `m' < 2^k`, the piece `Q_{m'}` shifted by `c`, `Q_{m'}(x - c)`. -/
noncomputable def perPieces (k : ℕ) (Q : ℕ → ℂ[X]) (m : ℕ) : ℂ[X] :=
  (Q (m % 2 ^ k)).comp (X - C ((((m / 2 ^ k : ℕ) : ℝ) : ℝ) : ℂ))

/-- The pieces of the periodic extension in a given decomposition `m = m' + 2^k c`, `m' < 2^k`. -/
theorem perPieces_eq (k : ℕ) (Q : ℕ → ℂ[X]) {m' : ℕ} (hm' : m' < 2 ^ k) (c : ℕ) :
    perPieces k Q (m' + 2 ^ k * c) = (Q m').comp (X - C (((c : ℝ) : ℝ) : ℂ)) := by
  have hpos : 0 < 2 ^ k := by positivity
  rw [perPieces, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hm', zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm']

/-- The pieces of the periodic extension have degree `< r`. -/
theorem perPieces_mem {r : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r) (k m : ℕ) :
    perPieces k Q m ∈ degreeLT ℂ r := by
  have h : (X - C ((((m / 2 ^ k : ℕ) : ℝ) : ℝ) : ℂ) : ℂ[X]) =
      C (-((((m / 2 ^ k : ℕ) : ℝ) : ℝ) : ℂ)) + C 1 * X := by
    rw [C_neg, C_1, one_mul]; ring
  rw [perPieces, h]
  exact comp_affine_mem_degreeLT (hQ _) _ _

/-- **The periodic extension of a piecewise polynomial** of level `k` is the piece
`Interval.perPieces k Q m` on every `I_{k,m}`, `m ∈ ℕ`. -/
theorem perExt_ppFun_eq (k : ℕ) (Q : ℕ → ℂ[X]) {m : ℕ} {x : ℝ} (hx : x ∈ dyadicIco k m) :
    perExt (ppFun k Q) x = polyFun (perPieces k Q m) x := by
  obtain ⟨c, m', hm', rfl⟩ : ∃ c m' : ℕ, m' < 2 ^ k ∧ m = m' + 2 ^ k * c :=
    ⟨m / 2 ^ k, m % 2 ^ k, Nat.mod_lt _ (by positivity), (Nat.mod_add_div m (2 ^ k)).symm⟩
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hm'R : (m' : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast hm'
  have hm'0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
  rw [mem_dyadicIco] at hx
  push_cast at hx
  have hfl : ⌊x⌋ = (c : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · nlinarith
    · nlinarith
  have hfract : Int.fract x = x - c := by
    rw [← Int.self_sub_floor, hfl]
    push_cast
    ring
  have hmem : x - c ∈ dyadicIco k m' := by
    rw [mem_dyadicIco]
    constructor <;> nlinarith
  rw [perExt, hfract, ppFun_eq_of_mem Q hm' hmem, perPieces_eq k Q hm' c]
  simp only [polyFun, eval_comp, eval_sub, eval_X, eval_C]
  push_cast
  ring_nf

/-- **The periodic extension of a piecewise polynomial** of level `k` is a piecewise polynomial
of level `k` on `[0, ∞)`, with the pieces `Interval.perPieces k Q`. -/
theorem isPiecewisePoly_perExt_ppFun {r : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r)
    (k : ℕ) : IsPiecewisePoly r k (perExt (ppFun k Q)) := fun m =>
  ⟨perPieces k Q m, perPieces_mem hQ k m, fun _ hx => perExt_ppFun_eq k Q hx⟩

/-- **The local masses of a periodic extension**: `2^k` consecutive pieces of the periodic
extension `uTilde` make up one period, so `∑_{n < 2^k} ∫_{I_{k,n+l}} |uTilde|^p ≤ ‖u‖_p^p`. -/
theorem sum_localMass_perExt_le {u : ℝ → ℂ} (hu : Measurable u) (hp : p ≠ ∞) (k l : ℕ) :
    ∑ n ∈ Finset.range (2 ^ k), localMass p k (perExt u) (n + l) ≤
      eLpNorm u p unitVol ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hsum := sum_le_lintegral_Icc (G := fun x => ‖perExt u x‖ₑ ^ p.toReal) ((l : ℝ) / 2 ^ k)
    (by positivity : (0 : ℝ) ≤ 1 / 2 ^ k) (2 ^ k)
  have h1 : (l : ℝ) / 2 ^ k + ((2 ^ k : ℕ) : ℝ) * (1 / 2 ^ k) = l / 2 ^ k + 1 := by
    push_cast
    field_simp
  rw [h1, lintegral_Icc_periodic (G := fun x => ‖perExt u x‖ₑ ^ p.toReal)
    (fun x => by simp only [perExt_periodic u x])] at hsum
  have hpieces : ∀ n : ℕ, localMass p k (perExt u) (n + l) =
      ∫⁻ x in Icc ((l : ℝ) / 2 ^ k + n * (1 / 2 ^ k)) ((l : ℝ) / 2 ^ k + (n + 1) * (1 / 2 ^ k)),
        ‖perExt u x‖ₑ ^ p.toReal := fun n => by
    rw [localMass, ← setLIntegral_congr Ico_ae_eq_Icc, dyadicIco]
    congr 2
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun n _ => hpieces n]
  refine hsum.trans (le_of_eq ?_)
  rw [eLpNorm_rpow_eq hu.aestronglyMeasurable hp0 hp, ← setLIntegral_congr Ico_ae_eq_Icc]
  rw [show (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂unitVol) = ∫⁻ x in Icc (0 : ℝ) 1, ‖u x‖ₑ ^ p.toReal from rfl,
    ← setLIntegral_congr Ico_ae_eq_Icc]
  exact setLIntegral_congr_fun measurableSet_Ico fun x hx => by rw [perExt_of_mem u hx]

/-- **Bounded overlap on the circle**: `∑_{n < 2^k} ∑_{l ≤ r} ∫_{I_{k,n+l}} |uTilde|^p ≤ (r + 1)
‖u‖_p^p`
for the periodic extension `uTilde`. -/
theorem sum_sum_localMass_perExt_le {u : ℝ → ℂ} (hu : Measurable u) (hp : p ≠ ∞) (k r : ℕ) :
    ∑ n ∈ Finset.range (2 ^ k), ∑ l ∈ Finset.range (r + 1), localMass p k (perExt u) (n + l) ≤
      (r + 1) * eLpNorm u p unitVol ^ p.toReal := by
  rw [Finset.sum_comm]
  calc ∑ l ∈ Finset.range (r + 1), ∑ n ∈ Finset.range (2 ^ k), localMass p k (perExt u) (n + l)
      ≤ ∑ _l ∈ Finset.range (r + 1), eLpNorm u p unitVol ^ p.toReal :=
        Finset.sum_le_sum fun l _ => sum_localMass_perExt_le hu hp k l
    _ = (r + 1) * eLpNorm u p unitVol ^ p.toReal := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

variable (p) in
/-- The periodic modulus of an element of `L_p[0, 1] = L_p(𝕋)` at the dyadic scale `2^(-k)`,
`ω_r^per(f, 2^(-k))_p`. -/
noncomputable def lpPerModulus (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) : ℝ≥0∞ :=
  perModulus r p (f : ℝ → ℂ) (1 / 2 ^ k)

/-- The periodic modulus of elements of `L_p[0, 1]` is subadditive. -/
theorem lpPerModulus_add_le (r : ℕ) (f g : Lp ℂ p unitVol) (k : ℕ) :
    lpPerModulus p r (f + g) k ≤ lpPerModulus p r f k + lpPerModulus p r g k := by
  rw [lpPerModulus, perModulus_congr_ae (Lp.coeFn_add f g)]
  exact perModulus_add_le Fact.out r _ _ _

/-- `ω_r^per(f, t)_p ≤ 2^r ‖f‖_p` in `L_p[0, 1]`. -/
theorem lpPerModulus_le (hp : p ≠ ∞) (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) :
    lpPerModulus p r f k ≤ 2 ^ r * ‖f‖ₑ := by
  rw [Lp.eNorm_def]
  exact perModulus_le (Lp.stronglyMeasurable f).measurable Fact.out hp r _

omit [Fact (1 ≤ p)] in
/-- The modulus on `[0, 1]` is at most the periodic modulus. -/
theorem lpModulus_le_lpPerModulus (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) :
    lpModulus p r f k ≤ lpPerModulus p r f k :=
  modulus_le_perModulus r p _ _

/-- **Jackson's inequality on the circle**: for `1 ≤ p < ∞` and `r ≥ 1` there is `C_J < ∞` with
`E_{2^k}(f)_p ≤ C_J ω_r^per(f, 2^(-k))_p` for all `f` and all `k ≥ 0`, since the periodic modulus
dominates the modulus on `[0, 1]`. -/
theorem exists_approxError_ppScheme_le_per {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p unitVol) (k : ℕ),
      (ppScheme p r).approxError f (2 ^ k) ≤ CJ * lpPerModulus p r f k := by
  obtain ⟨CJ, hCJ, h⟩ := exists_approxError_ppScheme_le (p := p) hr hp
  exact ⟨CJ, hCJ, fun f k => (h f k).trans (mul_le_mul' le_rfl (lpModulus_le_lpPerModulus r f k))⟩

/-- **The inverse inequality on the circle**, of order `1/p`: there is `C_B < ∞` with
`ω_r^per(a, 2^(-k))_p ≤ C_B 2^(-(k-j)/p) ‖a‖_p` for every piecewise polynomial `a` of level `j`
(and `k - j` truncated at `0`). -/
theorem exists_inverse_ppScheme_per {r : ℕ} (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ ppScheme p r (2 ^ j),
      lpPerModulus p r a k ≤ CB * dyadicWeight (-(1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  refine ⟨ppInverseConst p r K, ppInverseConst_ne_top r hK, fun j k a ha => ?_⟩
  obtain ⟨Q, hQ, hae⟩ := mem_ppScheme_two_pow.1 ha
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (lpPerModulus_le hp r a k).trans (by gcongr; exact two_pow_le_ppInverseConst r K)
  · have hnorm : ‖a‖ₑ = eLpNorm (ppFun j Q) p unitVol := by
      rw [Lp.eNorm_def]
      exact eLpNorm_congr_ae hae
    rw [lpPerModulus, perModulus_congr_ae hae, hnorm]
    refine iSup₂_le fun h hh => ?_
    have hhj : h ≤ 1 / 2 ^ j := hh.2.trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hjk))
    exact (eLpNorm_higherDiff_le_of_isPiecewisePoly (isPiecewisePoly_perExt_ppFun hQ j)
      (measurable_perExt (measurable_ppFun j Q)) hKb hp hh.1 hhj
      (sum_sum_localMass_perExt_le (measurable_ppFun j Q) hp j r)).trans
      (le_ppInverseConst_mul hjk K hh.2 _)

/-- The periodic modulus `ω_r^per(f, 2^(-k))_p` is compatible with the scheme of dyadic piecewise
polynomials of degree `< r`, with inverse order `θ = 1/p`. -/
noncomputable def ppPerModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (ppScheme p r) (1 / p.toReal) :=
  .ofExists (lpPerModulus p r) (lpPerModulus_add_le r) (2 ^ r) (by simp) (lpPerModulus_le hp r) 0
    ((exists_approxError_ppScheme_le_per hr hp).imp fun _ h => ⟨h.1, fun f k _ => h.2 f k⟩)
    (exists_inverse_ppScheme_per hp)

/-- **Approximation by piecewise polynomials on the circle.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`r ≥ 1` and `0 ≤ s < 1/p`, an `f ∈ L_p(𝕋) = L_p[0, 1]` lies in the approximation space `A^s_q`
of the dyadic piecewise polynomials of degree `< r` iff its periodic Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q}` is finite. -/
theorem memApprox_ppScheme_iff_per {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hs : 0 ≤ s) (hsp : s < 1 / p.toReal) (f : Lp ℂ p unitVol) :
    (ppScheme p r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpPerModulus p r f k) < ∞ :=
  (ppPerModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs hsp f

/-- **Besov spaces on the interval and on the circle agree below smoothness `1/p`**: for
`1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 ≤ s < 1/p`, the Besov quasi-norm of `f ∈ L_p[0, 1]`
defined by the modulus on `[0, 1]` is finite iff the one defined by the periodic modulus is.
Both conditions describe the same approximation space. -/
theorem lqNorm_modulus_lt_top_iff_perModulus {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 ≤ s) (hsp : s < 1 / p.toReal) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpPerModulus p r f k) < ∞ :=
  (memApprox_ppScheme_iff hr hp hq hs hsp f).symm.trans
    (memApprox_ppScheme_iff_per hr hp hq hs hsp f)

end Interval
