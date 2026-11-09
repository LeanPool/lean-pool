/-
Copyright (c) 2026 Stefanos Lappas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefanos Lappas
-/
module

public import LeanPool.MirekThiele.Contraction
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Part 4 of the development: the contraction step and Theorem 1.4 from Theorem 1.3, the
global/local reduction and Theorem 1.11, the atom estimate, and the proof of Theorem 1.3
(section `T1Theorem`), ending with the unconditional statements `localT1`, `localTb_all`,
`globalTb_all`. -/

@[expose] public section

open MeasureTheory

namespace MirekThiele

variable {d : ℕ}

section Bridge


variable {n k : ℕ}


/-! ### The contraction step, the main estimate and Theorem 1.4 -/

/-- **The contraction step, literally** (the main estimate of §2.2–2.8 in the form `A ≤ A θ + C`,
p. 43), for `n ≥ 2` and **every** family of testing functions: `θ = θu`, `C₁ = C₁u` for the
constant `B²` depend only on `d`, `n`, `B` and the exponents. For an instance `(σ', 𝐐, g)` of the
testing condition for the restricted family: if `k + 1 = n` there is no extension and the
restricted family vanishes, if `‖g‖_q = 0` or `F = 0` the form vanishes, and otherwise the
stopping data `Bridge.Instance.data` — on the tree `𝒟_N(Q)` with `N` at least the resolutions of
`g` and of the finitely many testing functions of the chain `𝐐`, and with leaf scale at most the
resolution of the form, so that the coarsened testing functions of the subchains may be used —
give the bound with `θ, C` of the data, which are at most `θu`, `C₁u`. [PROVED] -/
theorem contractionStep (hd : d ≠ 0) (hn : 2 ≤ n) (p : HolderTuple n) :
    ContractionStep d n k p := by
  intro B hB
  refine ⟨Bridge.θu (d := d) p (B * B), Bridge.C₁u (d := d) p (B * B), Bridge.θu_nonneg p _,
    Bridge.θu_lt_one p _, Bridge.C₁u_nonneg p _, ?_⟩
  intro T C hC b hb A hA htest σ₀ hσ₀ Q hQ g hg f hf hl hs
  have hprod0 : 0 ≤ (A * Bridge.θu (d := d) p (B * B) + Bridge.C₁u (d := d) p (B * B)) *
      prodNorm p f :=
    mul_nonneg (add_nonneg (mul_nonneg hA (Bridge.θu_nonneg p _)) (Bridge.C₁u_nonneg p _))
      (prodNorm_nonneg p f)
  have hzero : ∀ j : Fin n, lpNorm (f j : (Fin d → ℝ) → ℝ) (p.p j) = 0 →
      |T.form f| ≤ (A * Bridge.θu (d := d) p (B * B) + Bridge.C₁u (d := d) p (B * B)) *
        prodNorm p f := by
    intro j hj
    rw [T.form_eq_zero_of_lpNorm_eq_zero f j (by linarith [p.one_lt j]) hj, abs_zero]
    exact hprod0
  by_cases hk : k + 1 < n
  · obtain ⟨σ, hσ, hσσ₀⟩ := hC.extension (k + 1) hk σ₀ hσ₀
    obtain ⟨s, hsK⟩ := Bridge.exists_kernelScale T p
    obtain ⟨Ng, hNg⟩ := Bridge.exists_resolution g (Q (σ₀ (Fin.last k)))
    have hQσ : IPath.Nested σ Q := hQ.of_restrict hσσ₀
    choose Nb hNb using fun l : Fin (k + 1) =>
      Bridge.exists_resolution ⟨b σ Q l, hb.testFun _ hσ _ hQσ _⟩ (Q (σ₀ (Fin.last k)))
    obtain ⟨N, hN⟩ : ∃ N : ℕ,
        N = max (max Ng ((Q (σ₀ (Fin.last k))).m - s).toNat) (Finset.univ.sup Nb) := ⟨_, rfl⟩
    have hN1 : (((Q (σ₀ (Fin.last k))).m - s).toNat : ℤ) ≤ N := by
      rw [hN]
      exact Nat.cast_le.mpr ((le_max_right _ _).trans (le_max_left _ _))
    have hN2 := Int.self_le_toNat ((Q (σ₀ (Fin.last k))).m - s)
    let I : Bridge.Instance T p C b B :=
      { hd := hd, hC := hC, hk := hk, hb := hb, hB := hB, σ₀ := σ₀, hσ₀ := hσ₀, σ := σ, hσ := hσ,
        hσσ₀ := hσσ₀, Q := Q, hQ := hQ, G := g, hG := hg, A := A, hA := hA, htest := htest,
        N := N,
        hgres := fun l => Bridge.constOn_leaves_mono
          (by rw [hN]; exact (Finset.le_sup (Finset.mem_univ l)).trans (le_max_right _ _)) (hNb l),
        hGres := Bridge.constOn_leaves_mono
          (by rw [hN]; exact (le_max_left _ _).trans (le_max_left _ _)) hNg,
        s := s, hs := hsK, hNs := by omega }
    by_cases hG0 : lpNorm (g : (Fin d → ℝ) → ℝ) (p.p (σ₀ (Fin.last k))) = 0
    · exact hzero _ (by rw [hf]; exact hG0)
    by_cases hF0 : ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
        lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j) = 0
    · obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp hF0
      rw [Finset.mem_erase, Finset.mem_erase] at hj
      refine hzero j ?_
      rw [I.eq_tup f hf hl hs, I.tup_of_ne _ _ _ hj.2.1 hj.1, I.truncateₗ_frozen]
      exact hj0
    have hF : 0 < ∏ j ∈ (Finset.univ.erase I.a).erase I.b₀,
        lpNorm (I.frozen j : (Fin d → ℝ) → ℝ) (p.p j) :=
      lt_of_le_of_ne (Finset.prod_nonneg fun _ _ => lpNorm_nonneg _ _) (Ne.symm hF0)
    have hG0' : 0 < lpNorm (I.G : (Fin d → ℝ) → ℝ) (p.p I.b₀) :=
      lt_of_le_of_ne (lpNorm_nonneg _ _) (Ne.symm hG0)
    have hrq : 1 / p.p I.a + 1 / p.p I.b₀ ≤ 1 := Bridge.holder_pair_le_one p I.hab
    have h := I.abs_form_le hF hG0' hrq f hf hl hs
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (prodNorm_nonneg p f))
    have h1 := Bridge.θc_le_θu (I.data hF hG0') rfl rfl rfl
    have h2 := Bridge.Cstep_le_C₁u (I.data hF hG0') hrq rfl rfl rfl
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hA) h2
  · have hkn : k + 1 ≤ n := by simpa using Fintype.card_le_of_embedding σ₀
    have hno : ¬ ∃ τ ∈ C (k + 2), τ.restrict = σ₀ := by
      rintro ⟨τ, -, -⟩
      have := Fintype.card_le_of_embedding τ
      simp only [Fintype.card_fin] at this
      omega
    have hk0 : 0 < k := by omega
    have hl0 := hl ⟨0, hk0⟩
    simp only [restrictFamily, hno, ↓reduceDIte] at hl0
    refine hzero (σ₀ (⟨0, hk0⟩ : Fin k).castSucc) ?_
    rw [hl0, Bridge.truncate_zero, Bridge.lpNorm_zero']

/-- **The main estimate `RestrictedTesting`, literally**, for `n ≥ 2`: by iteration of the
contraction step. [PROVED] -/
theorem restrictedTesting (hd : d ≠ 0) (hn : 2 ≤ n) (p : HolderTuple n) :
    RestrictedTesting d n k p :=
  restrictedTesting_of_contractionStep (contractionStep hd hn p)

/-- **Theorem 1.4, literally, from Theorem 1.3**: the local `T(b)` theorem `LocalTb` for paths of
every length `1 ≤ k ≤ n`, `n ≥ 2`, for every family of testing functions satisfying (1.5)–(1.9),
with the literal main estimate supplying the inductive step. [PROVED] -/
theorem localTb (hn : 2 ≤ n) (p : HolderTuple n) (h13 : LocalT1 d n p) :
    ∀ k, 1 ≤ k → k ≤ n → LocalTb d n k p := by
  intro k hk1 hkn hd hk1' hkn' B hB
  exact localTb_of_localT1 hn p h13 (fun _ _ => restrictedTesting (by omega) hn p)
    k hk1 hkn hd hk1' hkn' B hB

/-! ## Theorem 1.11 from Theorem 1.4: the global/local reduction (p. 38, following [1])

Given `b_1, …, b_n` with (1.12)–(1.15), the testing functions `b_{σ,𝐐,σ(l)} = [b_j]_{Q_j}^{-1} b_j
𝟙_{Q_j}`
(`j = σ(l)`) satisfy the hypotheses (1.5)–(1.9) of Theorem 1.4 for paths of full length `n`
(`globalFamily`): (1.5)–(1.8) are immediate, and the testing condition (1.9) at `(σ, 𝐐)` with the
free function `g` in the slot `k = σ(n)` and the cube `Q = Q_k` reduces to the **local bound**
`|Λ(b_1 𝟙_Q, …, g, …, b_n 𝟙_Q)| ≤ C |Q|^{1-1/p_k} ‖g‖_{p_k}` (`abs_form_tupQ_le`), since
`‖b_j 𝟙_Q‖_{p_j} ≥ |Q|^{1/p_j}` by pseudo-accretivity. The local bound is the reduction of [1]:
write
`g = g₀ + [g]_Q 𝟙_Q` with `g₀` of mean zero on `Q`; by perfect smoothness the truncations `b_j 𝟙_Q`
may be replaced by `b_j` against a mean-zero entry (`form_update_truncate_eq`), so the BMO
condition (1.15) bounds the `g₀`-term by `B ‖g₀‖_{H¹}`; for the `𝟙_Q`-term write
`𝟙_Q = h + [b_k]_Q^{-1} b_k 𝟙_Q` with `h` of mean zero, use (1.15) again and the weak boundedness
(1.14). What remains is the **atom estimate** `‖h‖_{H¹} ≤ C |Q|^{1-1/p} ‖h‖_p` for mean-zero `h`
supported on `Q` (`AtomBound`): for `p ≥ 2` it follows from the martingale Pythagoras identity and
Hölder's inequality, for `1 < p < 2` it is the `L^p` bound of the dyadic square function
(Burkholder's inequality), which the paper does not discuss; both are proved below (`atomBound`),
here it is taken as a hypothesis. Theorem 1.4 in the form `localTb` then applies. -/

section GlobalReduction

variable {n : ℕ}

/-- **The atom estimate** for the dyadic Hardy norm with exponent `p`: for a mean-zero `h`
supported on a dyadic cube `Q`, `‖h‖_{H¹} ≤ C |Q|^{1-1/p} ‖h‖_p`. -/
def AtomBound (d : ℕ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (h : TestFun d), SupportedOn (h : (Fin d → ℝ) → ℝ) Q →
    MeanZero (h : (Fin d → ℝ) → ℝ) →
    hardyNorm (h : (Fin d → ℝ) → ℝ) ≤ C * Q.vol ^ (1 - 1 / p) * lpNorm (h : (Fin d → ℝ) → ℝ) p

/-- `‖f 𝟙_Q‖_p ≤ ‖f‖_∞ |Q|^{1/p}` for a bounded `f`. [PROVED] -/
theorem lpNorm_truncate_le_supNorm_mul (Q : DyadicCube d) (f : (Fin d → ℝ) → ℝ) {p : ℝ}
    (hp : 0 < p) (hf : MemLp f ⊤ volume) :
    lpNorm (truncate Q f) p ≤ supNorm f * Q.vol ^ (1 / p) := by
  unfold lpNorm supNorm
  have h1 : eLpNorm (truncate Q f) (ENNReal.ofReal p) volume ≤
      eLpNorm f ⊤ volume * ENNReal.ofReal Q.vol ^ (1 / p) := by
    rw [truncate, eLpNorm_indicator_eq_eLpNorm_restrict Q.measurableSet_toSet.nullMeasurableSet]
    calc eLpNorm f (ENNReal.ofReal p) (volume.restrict Q.toSet)
        ≤ eLpNorm f ⊤ (volume.restrict Q.toSet) * (volume.restrict Q.toSet Set.univ) ^
            (1 / (ENNReal.ofReal p).toReal - 1 / (⊤ : ENNReal).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ le_top hf.aestronglyMeasurable.restrict
      _ ≤ eLpNorm f ⊤ volume * ENNReal.ofReal Q.vol ^ (1 / p) := by
          rw [Measure.restrict_apply_univ, Q.volume_toSet, ENNReal.toReal_ofReal hp.le,
            ENNReal.toReal_top, div_zero, sub_zero]
          exact mul_le_mul' (eLpNorm_mono_measure f Measure.restrict_le_self) le_rfl
  have h2 : eLpNorm f ⊤ volume * ENNReal.ofReal Q.vol ^ (1 / p) ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  calc (eLpNorm (truncate Q f) (ENNReal.ofReal p) volume).toReal
      ≤ (eLpNorm f ⊤ volume * ENNReal.ofReal Q.vol ^ (1 / p)).toReal := ENNReal.toReal_mono h2 h1
    _ = (eLpNorm f ⊤ volume).toReal * Q.vol ^ (1 / p) := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal Q.vol_pos.le]

theorem TestFun.lpNorm_truncateₗ_le_supNorm_mul (Q : DyadicCube d) (f : TestFun d) {p : ℝ}
    (hp : 0 < p) :
    lpNorm ((TestFun.truncateₗ Q f : TestFun d) : (Fin d → ℝ) → ℝ) p ≤
      supNorm (f : (Fin d → ℝ) → ℝ) * Q.vol ^ (1 / p) :=
  lpNorm_truncate_le_supNorm_mul Q f hp (TestFun.memLp f.2 ⊤)

/-- `𝟙_P (c f 𝟙_R) = c f 𝟙_P` for `P ⊆ R`. [PROVED] -/
theorem truncate_smul_truncate_of_subset {P R : DyadicCube d} (h : P.toSet ⊆ R.toSet) (c : ℝ)
    (f : (Fin d → ℝ) → ℝ) : truncate P (c • truncate R f) = c • truncate P f := by
  funext x
  by_cases hx : x ∈ P.toSet
  · simp only [truncate, Pi.smul_apply, Set.indicator_of_mem hx, Set.indicator_of_mem (h hx)]
  · simp only [truncate, Pi.smul_apply, Set.indicator_of_notMem hx, smul_zero]

/-- **Against a mean-zero entry, truncations may be removed** (perfect smoothness (1.2)): if
`G` is supported on `Q` with mean zero, `Λ(…, F_j 𝟙_Q, …, G, …) = Λ(…, F_j, …, G, …)`. [PROVED] -/
theorem form_update_truncate_eq (T : PerfectCZForm d n) (Q : DyadicCube d)
    (F : Fin n → TestFun d) (k : Fin n) (G : TestFun d) (hG : SupportedOn (G : (Fin d → ℝ) → ℝ) Q)
    (hG0 : MeanZero (G : (Fin d → ℝ) → ℝ)) :
    T.form (Function.update (fun j => TestFun.truncateₗ Q (F j)) k G) =
      T.form (Function.update F k G) := by
  have key : ∀ s : Finset (Fin n), k ∉ s →
      T.form (Function.update (fun j => if j ∈ s then TestFun.truncateₗ Q (F j) else F j) k G) =
        T.form (Function.update F k G) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert j s hj ih =>
      intro hk
      have hjk : j ≠ k := fun h => hk (h ▸ Finset.mem_insert_self j s)
      have hk' : k ∉ s := fun h => hk (Finset.mem_insert_of_mem h)
      rw [← ih hk']
      set u := Function.update (fun i => if i ∈ s then TestFun.truncateₗ Q (F i) else F i) k G
        with hu
      have e1 : Function.update (fun i => if i ∈ insert j s then TestFun.truncateₗ Q (F i) else F i)
          k G = Function.update u j (TestFun.truncateₗ Q (F j)) := by
        funext i
        by_cases hik : i = k
        · subst hik
          rw [Function.update_self, Function.update_of_ne hjk.symm, hu, Function.update_self]
        · rw [Function.update_of_ne hik]
          by_cases hij : i = j
          · subst hij
            rw [Function.update_self]
            simp
          · rw [Function.update_of_ne hij, hu, Function.update_of_ne hik]
            simp [Finset.mem_insert, hij]
      have e2 : u = Function.update u j (F j) := by
        funext i
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self, hu, Function.update_of_ne hjk]
          simp [hj]
        · rw [Function.update_of_ne hij]
      have hsub := MultilinearMap.map_update_sub T.form u j (TestFun.truncateₗ Q (F j)) (F j)
      have hzero : T.form (Function.update u j (TestFun.truncateₗ Q (F j) - F j)) = 0 := by
        apply T.smooth Q _ k j hjk.symm
        · rw [Function.update_of_ne hjk.symm, hu, Function.update_self]
          exact hG
        · rw [Function.update_of_ne hjk.symm, hu, Function.update_self]
          exact hG0
        · rw [Function.update_self]
          intro x hx
          rw [Submodule.coe_sub, Pi.sub_apply, TestFun.coe_truncateₗ, truncate,
            Set.indicator_of_mem hx, sub_self]
      rw [e1]
      conv_rhs => rw [e2]
      exact sub_eq_zero.mp (hsub.symm.trans hzero)
  have := key (Finset.univ.erase k) (Finset.notMem_erase k _)
  convert this using 2
  funext i
  by_cases hik : i = k
  · subst hik
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hik, Function.update_of_ne hik]
    simp [Finset.mem_erase, hik]

/-! #### The dyadic cubes of side `2^M` at the origin -/

/-- The `2^d` dyadic cubes of side length `2^M` at the origin: `∏_i [0, 2^M)` or `[-2^M, 0)`
according to `κ_i`. -/
def quad (M : ℕ) (κ : Fin d → Bool) : DyadicCube d := ⟨M, fun i => if κ i then 0 else -1⟩

theorem quad_vol (M : ℕ) (κ : Fin d → Bool) : (quad M κ).vol = 2 ^ (M * d) := by
  change (2 : ℝ) ^ ((M : ℤ) * (d : ℤ)) = 2 ^ (M * d)
  have h := zpow_natCast (2 : ℝ) (M * d)
  push_cast at h
  exact h

theorem quad_injective (M : ℕ) : Function.Injective (quad (d := d) M) := by
  intro κ κ' h
  funext i
  have h1 := congrArg (fun Q : DyadicCube d => Q.l i) h
  simp only [quad] at h1
  revert h1
  cases κ i <;> cases κ' i <;> simp

theorem quad_disjoint {M : ℕ} {κ κ' : Fin d → Bool} (h : κ ≠ κ') :
    Disjoint (quad M κ).toSet (quad M κ').toSet :=
  (DyadicCube.eq_or_disjoint_of_m_eq (quad M κ) (quad M κ') rfl).resolve_left
    fun e => h (quad_injective M e)

theorem mem_quad_iff (M : ℕ) (κ : Fin d → Bool) (x : Fin d → ℝ) :
    x ∈ (quad M κ).toSet ↔
      ∀ i, if κ i then 0 ≤ x i ∧ x i < 2 ^ M else -(2 : ℝ) ^ M ≤ x i ∧ x i < 0 := by
  change (∀ i, (2 : ℝ) ^ (M : ℤ) * ((if κ i then 0 else -1 : ℤ) : ℝ) ≤ x i ∧
    x i < (2 : ℝ) ^ (M : ℤ) * (((if κ i then 0 else -1 : ℤ) : ℝ) + 1)) ↔ _
  refine forall_congr' fun i => ?_
  rw [zpow_natCast]
  cases κ i <;> simp

theorem exists_mem_quad {M : ℕ} {x : Fin d → ℝ} (hx : ∀ i, |x i| < 2 ^ M) :
    ∃ κ, x ∈ (quad M κ).toSet := by
  refine ⟨fun i => decide (0 ≤ x i), ?_⟩
  rw [mem_quad_iff]
  intro i
  have h := abs_lt.mp (hx i)
  by_cases h0 : 0 ≤ x i
  · simp [h0, h.2]
  · simp [h0, h.1.le, not_le.mp h0]

/-- A test function supported in `(-2^M, 2^M)^d` is the sum of its truncations to the cubes
at the origin. [PROVED] -/
theorem sum_truncateₗ_quad {M : ℕ} (f : TestFun d)
    (hf : ∀ x, (f : (Fin d → ℝ) → ℝ) x ≠ 0 → ∀ i, |x i| < 2 ^ M) :
    ∑ κ : Fin d → Bool, TestFun.truncateₗ (quad M κ) f = f := by
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply, TestFun.coe_truncateₗ, truncate]
  by_cases hfx : (f : (Fin d → ℝ) → ℝ) x = 0
  · rw [hfx]
    exact Finset.sum_eq_zero fun κ _ => Set.indicator_apply_eq_zero.mpr fun _ => hfx
  · obtain ⟨κ₀, hκ₀⟩ := exists_mem_quad (hf x hfx)
    rw [Finset.sum_eq_single κ₀ (fun κ _ hne =>
      Set.indicator_of_notMem (Set.disjoint_right.mp (quad_disjoint hne) hκ₀) _)
      (fun h => absurd (Finset.mem_univ κ₀) h), Set.indicator_of_mem hκ₀]

/-- Every dyadic test function is supported in some box `(-2^M, 2^M)^d`. [PROVED] -/
theorem TestFun.exists_abs_lt_pow (f : TestFun d) :
    ∃ M : ℕ, ∀ x, (f : (Fin d → ℝ) → ℝ) x ≠ 0 → ∀ i, |x i| < 2 ^ M := by
  suffices h : ∃ ρ : ℝ, ∀ x, (f : (Fin d → ℝ) → ℝ) x ≠ 0 → ∀ i, |x i| ≤ ρ by
    obtain ⟨ρ, hρ⟩ := h
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt ρ (by norm_num : (1 : ℝ) < 2)
    exact ⟨M, fun x hx i => (hρ x hx i).trans_lt hM⟩
  have hf : (f : (Fin d → ℝ) → ℝ) ∈
      Submodule.span ℝ (Set.range (DyadicCube.indicator (d := d))) := f.2
  refine Submodule.span_induction (p := fun g _ => ∃ ρ : ℝ, ∀ x, g x ≠ 0 → ∀ i, |x i| ≤ ρ)
    ?_ ?_ ?_ ?_ hf
  · rintro g ⟨P, rfl⟩
    refine ⟨(2 : ℝ) ^ P.m * ∑ i, (|(P.l i : ℝ)| + 1), fun x hx i => ?_⟩
    have hxP : x ∈ P.toSet := by
      by_contra h
      exact hx (Set.indicator_of_notMem h _)
    obtain ⟨h1, h2⟩ := hxP i
    have hpos : (0 : ℝ) < 2 ^ P.m := zpow_pos (by norm_num) _
    have hi : |(P.l i : ℝ)| + 1 ≤ ∑ i, (|(P.l i : ℝ)| + 1) :=
      Finset.single_le_sum (f := fun i => |(P.l i : ℝ)| + 1) (fun i _ => by positivity)
        (Finset.mem_univ i)
    have e2 := mul_le_mul_of_nonneg_left hi hpos.le
    rw [abs_le]
    constructor
    · have e1 := mul_le_mul_of_nonneg_left (neg_abs_le (P.l i : ℝ)) hpos.le
      linarith
    · have e3 := mul_le_mul_of_nonneg_left
        (show (P.l i : ℝ) + 1 ≤ |(P.l i : ℝ)| + 1 by linarith [le_abs_self (P.l i : ℝ)]) hpos.le
      linarith
  · exact ⟨0, fun x hx => absurd rfl hx⟩
  · rintro g h _ _ ⟨ρ₁, h₁⟩ ⟨ρ₂, h₂⟩
    refine ⟨max ρ₁ ρ₂, fun x hx i => ?_⟩
    by_cases hg : g x = 0
    · have hh : h x ≠ 0 := fun hh => hx (by simp [hg, hh])
      exact (h₂ x hh i).trans (le_max_right _ _)
    · exact (h₁ x hg i).trans (le_max_left _ _)
  · rintro c g _ ⟨ρ, hρ⟩
    exact ⟨ρ, fun x hx i => hρ x (fun hg => hx (by simp [hg])) i⟩

/-! #### Locally dyadic test functions and the kernel of the form

The functions `b_j` of Theorem 1.11 are locally dyadic test functions (`LocTestFun`), for example
`b_j = 1`; only their truncations `b_j 𝟙_Q` are dyadic test functions. In the BMO condition (1.15)
the value `Λ(b_1, …, h, …, b_n)` is the kernel integral `∫ K(x) ∏_j f_j(x_j) dx`. Since the kernel
has bounded support (`TestFunProd.exists_abs_lt_pow`), this integral equals `Λ` applied to the
truncations of the `b_j` to a large box (`form_update_box_eq_integral`), and against a mean-zero
`h` supported on `Q` perfect smoothness reduces the box to `Q`
(`form_update_trunc_eq_integral`). -/

/-- The truncation `b 𝟙_Q` of a locally dyadic test function, as a dyadic test function. -/
noncomputable def LocTestFun.trunc {b : (Fin d → ℝ) → ℝ} (hb : b ∈ LocTestFun d)
    (Q : DyadicCube d) : TestFun d :=
  ⟨truncate Q b, hb Q⟩

@[simp] theorem LocTestFun.coe_trunc {b : (Fin d → ℝ) → ℝ} (hb : b ∈ LocTestFun d)
    (Q : DyadicCube d) : ((LocTestFun.trunc hb Q : TestFun d) : (Fin d → ℝ) → ℝ) = truncate Q b :=
  rfl

/-- The truncation of a locally dyadic test function to the box `[-2^M, 2^M)^d`, the union of the
`2^d` cubes `quad M κ`, as a dyadic test function. -/
noncomputable def LocTestFun.box {b : (Fin d → ℝ) → ℝ} (hb : b ∈ LocTestFun d) (M : ℕ) :
    TestFun d :=
  ∑ κ : Fin d → Bool, LocTestFun.trunc hb (quad M κ)

/-- The box truncation agrees with `b` inside `(-2^M, 2^M)^d`. [PROVED] -/
theorem LocTestFun.box_apply {b : (Fin d → ℝ) → ℝ} (hb : b ∈ LocTestFun d) {M : ℕ}
    {y : Fin d → ℝ} (hy : ∀ i, |y i| < 2 ^ M) :
    (LocTestFun.box hb M : (Fin d → ℝ) → ℝ) y = b y := by
  obtain ⟨κ₀, hκ₀⟩ := exists_mem_quad hy
  simp only [LocTestFun.box, Submodule.coe_sum, Finset.sum_apply, LocTestFun.coe_trunc, truncate]
  rw [Finset.sum_eq_single κ₀ (fun κ _ hne =>
      Set.indicator_of_notMem (Set.disjoint_right.mp (quad_disjoint hne) hκ₀) _)
      (fun h => absurd (Finset.mem_univ κ₀) h), Set.indicator_of_mem hκ₀]

/-- Every dyadic test function on `ℝ^{dn}` is supported in some box `(-2^M, 2^M)^{dn}`.
[PROVED] -/
theorem TestFunProd.exists_abs_lt_pow {K : (Fin n → Fin d → ℝ) → ℝ} (hK : K ∈ TestFunProd d n) :
    ∃ M : ℕ, ∀ x, K x ≠ 0 → ∀ j i, |x j i| < 2 ^ M := by
  refine Submodule.span_induction
    (p := fun g _ => ∃ M : ℕ, ∀ x, g x ≠ 0 → ∀ j i, |x j i| < 2 ^ M) ?_ ?_ ?_ ?_ hK
  · rintro g ⟨P, -, rfl⟩
    choose Mj hMj using fun j => TestFun.exists_abs_lt_pow (TestFun.ind (P j))
    refine ⟨∑ j, Mj j, fun x hx j i => ?_⟩
    have hxP : x ∈ DyadicCube.prodSet P := by
      by_contra h
      exact hx (Set.indicator_of_notMem h _)
    have hxj : x j ∈ (P j).toSet := hxP j
    have h1 : ((TestFun.ind (P j) : TestFun d) : (Fin d → ℝ) → ℝ) (x j) ≠ 0 := by
      rw [TestFun.coe_ind, Set.indicator_of_mem hxj]
      exact one_ne_zero
    exact (hMj j (x j) h1 i).trans_le (pow_le_pow_right₀ one_le_two
      (Finset.single_le_sum (f := Mj) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)))
  · exact ⟨0, fun x hx => absurd rfl hx⟩
  · rintro g h _ _ ⟨M₁, h₁⟩ ⟨M₂, h₂⟩
    refine ⟨max M₁ M₂, fun x hx j i => ?_⟩
    by_cases hg : g x = 0
    · have hh : h x ≠ 0 := fun hh => hx (by simp [hg, hh])
      exact (h₂ x hh j i).trans_le (pow_le_pow_right₀ one_le_two (le_max_right _ _))
    · exact (h₁ x hg j i).trans_le (pow_le_pow_right₀ one_le_two (le_max_left _ _))
  · rintro c g _ ⟨M, hM⟩
    exact ⟨M, fun x hx j i => hM x (fun hg => hx (by simp [hg])) j i⟩

/-- **`Λ(b_1, …, h, …, b_n)` through a kernel equals `Λ` on box truncations**: for a kernel `K` of
`Λ` supported in the box of size `2^M` in every variable. [PROVED] -/
theorem form_update_box_eq_integral (T : PerfectCZForm d n) {b : Fin n → (Fin d → ℝ) → ℝ}
    (hb : ∀ j, b j ∈ LocTestFun d) {K : (Fin n → Fin d → ℝ) → ℝ}
    (hrep : ∀ f : Fin n → TestFun d, T.form f = ∫ x, K x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j))
    {M : ℕ} (hM : ∀ x, K x ≠ 0 → ∀ j i, |x j i| < 2 ^ M) (k : Fin n) (h : TestFun d) :
    T.form (Function.update (fun j => LocTestFun.box (hb j) M) k h) =
      ∫ x, K x * ∏ j, (Function.update b k (h : (Fin d → ℝ) → ℝ)) j (x j) := by
  rw [hrep]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  by_cases hK0 : K x = 0
  · rw [hK0, zero_mul, zero_mul]
  · congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hjk : j = k
    · subst hjk
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
      exact LocTestFun.box_apply (hb j) (hM x hK0 j)

/-- **Against a mean-zero entry, `Λ(b_1, …, h, …, b_n) = Λ(b_1 𝟙_Q, …, h, …, b_n 𝟙_Q)`**: for `h`
supported on `Q` with mean zero, the kernel integral with the locally dyadic test functions `b_j`
equals `Λ` applied to their truncations to `Q` (perfect smoothness, `form_update_truncate_eq`).
[PROVED] -/
theorem form_update_trunc_eq_integral (T : PerfectCZForm d n) {b : Fin n → (Fin d → ℝ) → ℝ}
    (hb : ∀ j, b j ∈ LocTestFun d) {K : (Fin n → Fin d → ℝ) → ℝ} (hK : K ∈ TestFunProd d n)
    (hrep : ∀ f : Fin n → TestFun d, T.form f = ∫ x, K x * ∏ j, (f j : (Fin d → ℝ) → ℝ) (x j))
    (Q : DyadicCube d) (k : Fin n) (h : TestFun d) (hs : SupportedOn (h : (Fin d → ℝ) → ℝ) Q)
    (h0 : MeanZero (h : (Fin d → ℝ) → ℝ)) :
    T.form (Function.update (fun j => LocTestFun.trunc (hb j) Q) k h) =
      ∫ x, K x * ∏ j, (Function.update b k (h : (Fin d → ℝ) → ℝ)) j (x j) := by
  obtain ⟨M₁, hM₁⟩ := TestFunProd.exists_abs_lt_pow hK
  obtain ⟨M₂, hM₂⟩ := TestFun.exists_abs_lt_pow (TestFun.ind Q)
  have hQbox : ∀ y ∈ Q.toSet, ∀ i, |y i| < 2 ^ (M₁ + M₂) := fun y hy i => by
    have h1 : ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) y ≠ 0 := by
      rw [TestFun.coe_ind, Set.indicator_of_mem hy]
      exact one_ne_zero
    exact (hM₂ y h1 i).trans_le (pow_le_pow_right₀ one_le_two (Nat.le_add_left _ _))
  have hKbox : ∀ x, K x ≠ 0 → ∀ j i, |x j i| < 2 ^ (M₁ + M₂) := fun x hx j i =>
    (hM₁ x hx j i).trans_le (pow_le_pow_right₀ one_le_two (Nat.le_add_right _ _))
  have htr : ∀ j, TestFun.truncateₗ Q (LocTestFun.box (hb j) (M₁ + M₂)) =
      LocTestFun.trunc (hb j) Q := by
    intro j
    apply Subtype.ext
    funext y
    rw [TestFun.coe_truncateₗ, LocTestFun.coe_trunc]
    by_cases hy : y ∈ Q.toSet
    · rw [truncate, truncate, Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      exact LocTestFun.box_apply (hb j) (hQbox y hy)
    · rw [truncate, truncate, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have e : (fun j => LocTestFun.trunc (hb j) Q) =
      fun j => TestFun.truncateₗ Q (LocTestFun.box (hb j) (M₁ + M₂)) :=
    funext fun j => (htr j).symm
  rw [e]
  exact (form_update_truncate_eq T Q (fun j => LocTestFun.box (hb j) (M₁ + M₂)) k h hs h0).trans
    (form_update_box_eq_integral T hb hrep hKbox k h)

/-- `‖b_j 𝟙_Q‖_p ≤ B |Q|^{1/p}` under the norm bound (1.13). [PROVED] -/
theorem GlobalTbHypotheses.lpNorm_trunc_le {T : PerfectCZForm d n}
    {b : Fin n → (Fin d → ℝ) → ℝ} {B : ℝ} (hb : GlobalTbHypotheses T b B) (hB : 0 ≤ B)
    (Q : DyadicCube d) (j : Fin n) {p : ℝ} (hp : 0 < p) :
    lpNorm ((LocTestFun.trunc (hb.loc j) Q : TestFun d) : (Fin d → ℝ) → ℝ) p ≤
      B * Q.vol ^ (1 / p) := by
  have hmem : MemLp (truncate Q (b j)) ⊤ volume := TestFun.memLp (LocTestFun.trunc (hb.loc j) Q).2 ⊤
  have h1 := lpNorm_truncate_le_supNorm_mul Q (truncate Q (b j)) hp hmem
  have htt : truncate Q (truncate Q (b j)) = truncate Q (b j) := by
    funext x
    by_cases hx : x ∈ Q.toSet
    · rw [truncate, truncate, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [truncate, truncate, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [htt] at h1
  have hle : eLpNorm (truncate Q (b j)) ⊤ volume ≤ ENNReal.ofReal B := by
    rw [truncate]
    exact (eLpNorm_indicator_le (b j) Q.measurableSet_toSet.nullMeasurableSet).trans
      (hb.bound j)
  have h2 : supNorm (truncate Q (b j)) ≤ B := by
    unfold supNorm
    calc (eLpNorm (truncate Q (b j)) ⊤ volume).toReal ≤ (ENNReal.ofReal B).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = B := ENNReal.toReal_ofReal hB
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg Q.vol_pos.le _))

/-- The tuple `(b_j 𝟙_Q)_{j ≠ k}` with `x` in the slot `k`. -/
noncomputable def tupQ {b : Fin n → (Fin d → ℝ) → ℝ} (hb : ∀ j, b j ∈ LocTestFun d)
    (Q : DyadicCube d) (k : Fin n) (x : TestFun d) : Fin n → TestFun d :=
  Function.update (fun j => LocTestFun.trunc (hb j) Q) k x

theorem form_tupQ_add (T : PerfectCZForm d n) {b : Fin n → (Fin d → ℝ) → ℝ}
    (hb : ∀ j, b j ∈ LocTestFun d) (Q : DyadicCube d) (k : Fin n) (x y : TestFun d) :
    T.form (tupQ hb Q k (x + y)) = T.form (tupQ hb Q k x) + T.form (tupQ hb Q k y) :=
  MultilinearMap.map_update_add _ _ _ _ _

theorem form_tupQ_smul (T : PerfectCZForm d n) {b : Fin n → (Fin d → ℝ) → ℝ}
    (hb : ∀ j, b j ∈ LocTestFun d) (Q : DyadicCube d) (k : Fin n) (c : ℝ) (x : TestFun d) :
    T.form (tupQ hb Q k (c • x)) = c * T.form (tupQ hb Q k x) := by
  unfold tupQ
  rw [MultilinearMap.map_update_smul, smul_eq_mul]

/-- **The local bound of the global/local reduction** (p. 38, [1]): for `g` supported on `Q`,
`|Λ(b_1 𝟙_Q, …, g, …, b_n 𝟙_Q)| ≤ B (3 C_a + 1 + C_a B) |Q|^{1-1/p} ‖g‖_p`, where `C_a` is the
constant of the atom estimate for the exponent `p`. [PROVED] -/
theorem GlobalTbHypotheses.abs_form_tupQ_le {T : PerfectCZForm d n} {b : Fin n → (Fin d → ℝ) → ℝ}
    {B : ℝ} (hb : GlobalTbHypotheses T b B) (hB : 1 ≤ B) {Ca : ℝ} (hCa : 0 ≤ Ca) {p : ℝ}
    (hp : 1 < p)
    (hatom : ∀ (Q : DyadicCube d) (h : TestFun d), SupportedOn (h : (Fin d → ℝ) → ℝ) Q →
      MeanZero (h : (Fin d → ℝ) → ℝ) →
      hardyNorm (h : (Fin d → ℝ) → ℝ) ≤ Ca * Q.vol ^ (1 - 1 / p) * lpNorm (h : (Fin d → ℝ) → ℝ) p)
    (hsq : ∀ (Q : DyadicCube d) (h : TestFun d), SupportedOn (h : (Fin d → ℝ) → ℝ) Q →
      MeanZero (h : (Fin d → ℝ) → ℝ) → Integrable (dyadicSquareFun (h : (Fin d → ℝ) → ℝ)))
    (Q : DyadicCube d) (k : Fin n) (g : TestFun d) (hg : SupportedOn (g : (Fin d → ℝ) → ℝ) Q) :
    |T.form (tupQ hb.loc Q k g)| ≤
      B * (3 * Ca + 1 + Ca * B) * Q.vol ^ (1 - 1 / p) * lpNorm (g : (Fin d → ℝ) → ℝ) p := by
  have hV := Q.vol_pos
  have hp0 : 0 < p := by linarith
  have hB0 : 0 < B := by linarith
  have hgn := lpNorm_nonneg (g : (Fin d → ℝ) → ℝ) p
  set V1 := Q.vol ^ (1 - 1 / p) with hV1
  set Vp := Q.vol ^ (1 / p) with hVp
  set Vm := Q.vol ^ (-(1 / p)) with hVm
  have hV1p : V1 * Vp = Q.vol := by
    rw [hV1, hVp, ← Real.rpow_add hV, sub_add_cancel, Real.rpow_one]
  have hVmp : Vm * Vp = 1 := by
    rw [hVm, hVp, ← Real.rpow_add hV, neg_add_cancel, Real.rpow_zero]
  have hVmQ : Vm * Q.vol = V1 := by
    rw [← hV1p]
    linear_combination V1 * hVmp
  have hV10 : 0 ≤ V1 := Real.rpow_nonneg hV.le _
  have hVp0 : 0 ≤ Vp := Real.rpow_nonneg hV.le _
  -- mean-zero entries: (1.15) and the atom estimate
  have hmz : ∀ h : TestFun d, SupportedOn (h : (Fin d → ℝ) → ℝ) Q →
      MeanZero (h : (Fin d → ℝ) → ℝ) →
      |T.form (tupQ hb.loc Q k h)| ≤ B * Ca * V1 * lpNorm (h : (Fin d → ℝ) → ℝ) p := by
    intro h hs h0
    obtain ⟨K, hK, hrep⟩ := T.truncation
    rw [tupQ, form_update_trunc_eq_integral T hb.loc hK hrep Q k h hs h0]
    calc |∫ x, K x * ∏ j, (Function.update b k (h : (Fin d → ℝ) → ℝ)) j (x j)|
        ≤ B * hardyNorm (h : (Fin d → ℝ) → ℝ) := hb.bmo K hK hrep k h (hsq Q h hs h0)
      _ ≤ B * (Ca * V1 * lpNorm (h : (Fin d → ℝ) → ℝ) p) :=
          mul_le_mul_of_nonneg_left (hatom Q h hs h0) hB0.le
      _ = _ := by ring
  -- the decomposition `g = g₀ + [g]_Q 𝟙_Q`
  set c := avg Q (g : (Fin d → ℝ) → ℝ)
  set g₀ : TestFun d := g - c • TestFun.ind Q with hg₀
  have hg₀s : SupportedOn (g₀ : (Fin d → ℝ) → ℝ) Q := by
    intro x hx
    rw [hg₀, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, TestFun.coe_ind,
      Set.indicator_of_notMem hx, hg x hx, smul_zero, sub_zero]
  have hintg : ∫ x, (g : (Fin d → ℝ) → ℝ) x = c * Q.vol := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hg x hx), ← avg_mul_vol]
  have hintQ : ∫ x, ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x = Q.vol := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => TestFun.ind_supportedOn Q x hx),
      StoppingData.TestFun.setIntegral_ind_of_subset (subset_refl _)]
  have hg₀0 : MeanZero (g₀ : (Fin d → ℝ) → ℝ) := by
    change TestFun.integralₗ g₀ = 0
    rw [hg₀, map_sub, map_smul, smul_eq_mul, TestFun.integralₗ_apply, TestFun.integralₗ_apply,
      hintg, hintQ, sub_self]
  have hc' : |c| ≤ Vm * lpNorm (g : (Fin d → ℝ) → ℝ) p := abs_avg_le Q g hp.le
  have hcabs : |c| * Vp ≤ lpNorm (g : (Fin d → ℝ) → ℝ) p := by
    calc |c| * Vp ≤ Vm * lpNorm (g : (Fin d → ℝ) → ℝ) p * Vp :=
          mul_le_mul_of_nonneg_right hc' hVp0
      _ = lpNorm (g : (Fin d → ℝ) → ℝ) p * (Vm * Vp) := by ring
      _ = lpNorm (g : (Fin d → ℝ) → ℝ) p := by rw [hVmp, mul_one]
  have hg₀n : lpNorm (g₀ : (Fin d → ℝ) → ℝ) p ≤ 2 * lpNorm (g : (Fin d → ℝ) → ℝ) p := by
    calc lpNorm (g₀ : (Fin d → ℝ) → ℝ) p
        ≤ lpNorm (g : (Fin d → ℝ) → ℝ) p +
            lpNorm ((c • TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) p :=
          TestFun.lpNorm_sub_le g _ hp.le
      _ = lpNorm (g : (Fin d → ℝ) → ℝ) p + |c| * Vp := by
          rw [TestFun.lpNorm_smul, TestFun.lpNorm_ind Q hp0]
      _ ≤ lpNorm (g : (Fin d → ℝ) → ℝ) p + lpNorm (g : (Fin d → ℝ) → ℝ) p := add_le_add le_rfl hcabs
      _ = _ := by ring
  -- the indicator entry: `𝟙_Q = h₁ + [b_k]_Q^{-1} b_k 𝟙_Q`
  set ck := (avg Q (b k : (Fin d → ℝ) → ℝ))⁻¹ with hck
  have hacc := hb.accretive Q k
  have havg0 : avg Q (b k : (Fin d → ℝ) → ℝ) ≠ 0 := fun h => by
    rw [h, abs_zero] at hacc
    linarith
  have hck1 : |ck| ≤ 1 := by
    rw [hck, abs_inv]
    exact inv_le_one_of_one_le₀ hacc
  set h₁ : TestFun d := TestFun.ind Q - ck • LocTestFun.trunc (hb.loc k) Q with hh₁
  have hh₁s : SupportedOn (h₁ : (Fin d → ℝ) → ℝ) Q := by
    intro x hx
    rw [hh₁, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, TestFun.coe_ind,
      LocTestFun.coe_trunc, Set.indicator_of_notMem hx, truncate, Set.indicator_of_notMem hx,
      smul_zero, sub_zero]
  have hintb : ∫ x, ((LocTestFun.trunc (hb.loc k) Q : TestFun d) : (Fin d → ℝ) → ℝ) x =
      avg Q (b k : (Fin d → ℝ) → ℝ) * Q.vol := by
    rw [LocTestFun.coe_trunc, truncate, integral_indicator Q.measurableSet_toSet, avg_mul_vol]
  have hh₁0 : MeanZero (h₁ : (Fin d → ℝ) → ℝ) := by
    change TestFun.integralₗ h₁ = 0
    rw [hh₁, map_sub, map_smul, smul_eq_mul, TestFun.integralₗ_apply, TestFun.integralₗ_apply,
      hintQ, hintb, hck, ← mul_assoc, inv_mul_cancel₀ havg0, one_mul, sub_self]
  have hbk : lpNorm ((LocTestFun.trunc (hb.loc k) Q : TestFun d) : (Fin d → ℝ) → ℝ) p ≤ B * Vp :=
    hb.lpNorm_trunc_le hB0.le Q k hp0
  have hh₁n : lpNorm (h₁ : (Fin d → ℝ) → ℝ) p ≤ (1 + B) * Vp := by
    calc lpNorm (h₁ : (Fin d → ℝ) → ℝ) p
        ≤ lpNorm ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) p +
            lpNorm ((ck • LocTestFun.trunc (hb.loc k) Q : TestFun d) : (Fin d → ℝ) → ℝ) p :=
          TestFun.lpNorm_sub_le _ _ hp.le
      _ = Vp + |ck| * lpNorm ((LocTestFun.trunc (hb.loc k) Q : TestFun d) : (Fin d → ℝ) → ℝ) p := by
          rw [TestFun.lpNorm_ind Q hp0, TestFun.lpNorm_smul]
      _ ≤ Vp + 1 * (B * Vp) :=
          add_le_add le_rfl (mul_le_mul hck1 hbk (lpNorm_nonneg _ _) zero_le_one)
      _ = _ := by ring
  have hweak : |T.form (tupQ hb.loc Q k (LocTestFun.trunc (hb.loc k) Q))| ≤ B * Q.vol := by
    have e : tupQ hb.loc Q k (LocTestFun.trunc (hb.loc k) Q) =
        fun j => LocTestFun.trunc (hb.loc j) Q :=
      Function.update_eq_self k _
    rw [e]
    exact hb.weak Q _ fun _ => rfl
  have hind : |T.form (tupQ hb.loc Q k (TestFun.ind Q))| ≤ B * (Ca * (1 + B) + 1) * Q.vol := by
    have e : TestFun.ind Q = h₁ + ck • LocTestFun.trunc (hb.loc k) Q := by rw [hh₁, sub_add_cancel]
    rw [e, form_tupQ_add, form_tupQ_smul]
    have h1 := hmz h₁ hh₁s hh₁0
    calc |T.form (tupQ hb.loc Q k h₁) + ck * T.form (tupQ hb.loc Q k (LocTestFun.trunc (hb.loc k)
      Q))|
        ≤ |T.form (tupQ hb.loc Q k h₁)| + |ck| * |T.form (tupQ hb.loc Q k (LocTestFun.trunc (hb.loc
          k) Q))| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ B * Ca * V1 * ((1 + B) * Vp) + 1 * (B * Q.vol) :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left hh₁n (by positivity)))
            (mul_le_mul hck1 hweak (abs_nonneg _) zero_le_one)
      _ = B * (Ca * (1 + B) + 1) * Q.vol := by
          rw [show B * Ca * V1 * ((1 + B) * Vp) = B * Ca * (1 + B) * (V1 * Vp) by ring, hV1p]
          ring
  -- assembly
  have e : g = g₀ + c • TestFun.ind Q := by rw [hg₀, sub_add_cancel]
  have h0 := hmz g₀ hg₀s hg₀0
  calc |T.form (tupQ hb.loc Q k g)|
      = |T.form (tupQ hb.loc Q k g₀) + c * T.form (tupQ hb.loc Q k (TestFun.ind Q))| := by
        rw [← form_tupQ_smul, ← form_tupQ_add, ← e]
    _ ≤ |T.form (tupQ hb.loc Q k g₀)| + |c| * |T.form (tupQ hb.loc Q k (TestFun.ind Q))| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ B * Ca * V1 * (2 * lpNorm (g : (Fin d → ℝ) → ℝ) p) +
          (Vm * lpNorm (g : (Fin d → ℝ) → ℝ) p) * (B * (Ca * (1 + B) + 1) * Q.vol) :=
        add_le_add (h0.trans (mul_le_mul_of_nonneg_left hg₀n (by positivity)))
          (mul_le_mul hc' hind (abs_nonneg _) (by positivity))
    _ = B * (3 * Ca + 1 + Ca * B) * V1 * lpNorm (g : (Fin d → ℝ) → ℝ) p := by
        rw [show (Vm * lpNorm (g : (Fin d → ℝ) → ℝ) p) * (B * (Ca * (1 + B) + 1) * Q.vol) =
          B * (Ca * (1 + B) + 1) * lpNorm (g : (Fin d → ℝ) → ℝ) p * (Vm * Q.vol) by ring, hVmQ]
        ring

/-- **The testing family of the global/local reduction**: `b_{σ,𝐐,σ(l)} = [b_j]_{Q_j}^{-1} b_j
𝟙_{Q_j}`
for `j = σ(l)` (p. 38). -/
noncomputable def globalFamily (b : Fin n → (Fin d → ℝ) → ℝ) (m : ℕ) : TestingFamily d n m :=
  fun σ Q l => (avg (Q (σ l.castSucc)) (b (σ l.castSucc) : (Fin d → ℝ) → ℝ))⁻¹ •
    truncate (Q (σ l.castSucc)) (b (σ l.castSucc))

theorem globalFamily_eq {b : Fin n → (Fin d → ℝ) → ℝ} (hb : ∀ j, b j ∈ LocTestFun d) (m : ℕ)
    (σ : IPath n (m + 1)) (Q : Fin n → DyadicCube d) (l : Fin m) :
    globalFamily b m σ Q l = (((avg (Q (σ l.castSucc)) (b (σ l.castSucc) : (Fin d → ℝ) → ℝ))⁻¹ •
      LocTestFun.trunc (hb (σ l.castSucc)) (Q (σ l.castSucc)) : TestFun d) : (Fin d → ℝ) → ℝ) :=
  rfl

/-- **The testing condition (1.9) for the family of the reduction**, with the constant
`B₁ = 1 + ∑_j B^{p_j} + B (3 C_a + 1 + C_a B)`: at `(σ, 𝐐)` with `σ` of full length, the tuple of
(1.9) is `(c_j b_j 𝟙_Q)_{j ≠ k}` with `g` in the slot `k = σ(n)`, `Q = Q_k`; the local bound and
`‖b_j 𝟙_Q‖_{p_j} ≥ |Q|^{1/p_j}` give the bound. [PROVED] -/
theorem GlobalTbHypotheses.testing_globalFamily {T : PerfectCZForm d n} {b : Fin n → (Fin d → ℝ) →
  ℝ}
    {B : ℝ} (hb : GlobalTbHypotheses T b B) (hB : 1 ≤ B) (p : HolderTuple n) {m : ℕ}
    (hm : m + 1 = n) (C : IPath.Collection n) {Ca : ℝ} (hCa : 0 ≤ Ca)
    (hatom : ∀ (k : Fin n) (Q : DyadicCube d) (h : TestFun d), SupportedOn (h : (Fin d → ℝ) → ℝ) Q →
      MeanZero (h : (Fin d → ℝ) → ℝ) → hardyNorm (h : (Fin d → ℝ) → ℝ) ≤
        Ca * Q.vol ^ (1 - 1 / p.p k) * lpNorm (h : (Fin d → ℝ) → ℝ) (p.p k))
    (hsq : ∀ (Q : DyadicCube d) (h : TestFun d), SupportedOn (h : (Fin d → ℝ) → ℝ) Q →
      MeanZero (h : (Fin d → ℝ) → ℝ) → Integrable (dyadicSquareFun (h : (Fin d → ℝ) → ℝ))) :
    TestingCondition T p C (globalFamily b m) (1 + (∑ j, B ^ p.p j) + B * (3 * Ca + 1 + Ca * B)) :=
      by
  intro σ _ Q hQ g hg f hf hl _
  have hsurj : Function.Surjective σ :=
    ((Fintype.bijective_iff_injective_and_card σ).mpr ⟨σ.injective, by simp [hm]⟩).2
  set k := σ (Fin.last m) with hk
  set Q₀ := Q k
  set cf : Fin n → ℝ := fun j => if j = k then 1 else (avg (Q j) (b j : (Fin d → ℝ) → ℝ))⁻¹ with hcf
  have hf_eq : f = fun j => cf j • tupQ hb.loc Q₀ k g j := by
    funext j
    obtain ⟨i, rfl⟩ := hsurj j
    induction i using Fin.lastCases with
    | last =>
      simp only [hk, hcf, tupQ, ↓reduceIte, one_smul, Function.update_self]
      exact hf
    | cast i =>
      have hne : σ i.castSucc ≠ k := fun h => (Fin.castSucc_lt_last i).ne (σ.injective h)
      have hsub : Q₀.toSet ⊆ (Q (σ i.castSucc)).toSet := hQ.mono _ _ (Fin.castSucc_lt_last i)
      apply Subtype.ext
      rw [hl i, globalFamily_eq hb.loc]
      simp only [hcf, hne, ↓reduceIte, tupQ, Function.update_of_ne hne, Submodule.coe_smul,
        LocTestFun.coe_trunc]
      exact truncate_smul_truncate_of_subset hsub _ _
  have hform : T.form f = (∏ j, cf j) * T.form (tupQ hb.loc Q₀ k g) := by
    rw [hf_eq, MultilinearMap.map_smul_univ, smul_eq_mul]
  have hprod : prodNorm p f = (∏ j, |cf j|) * prodNorm p (tupQ hb.loc Q₀ k g) := by
    rw [hf_eq]
    unfold prodNorm
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => TestFun.lpNorm_smul _ _ _
  -- the lower bound `∏_j ‖(tupQ g)_j‖ ≥ |Q|^{1-1/p_k} ‖g‖_{p_k}`
  have hV := Q₀.vol_pos
  have hlow : Q₀.vol ^ (1 - 1 / p.p k) * lpNorm (g : (Fin d → ℝ) → ℝ) (p.p k) ≤
      prodNorm p (tupQ hb.loc Q₀ k g) := by
    rw [tupQ, Bridge.prodNorm_update]
    have hsum : ∑ j ∈ Finset.univ.erase k, 1 / p.p j = 1 - 1 / p.p k := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ k)]
      simp only [one_div]
      rw [p.sum_inv]
    have hterm : ∀ j ∈ Finset.univ.erase k, Q₀.vol ^ (1 / p.p j) ≤
        lpNorm ((LocTestFun.trunc (hb.loc j) Q₀ : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j) := by
      intro j _
      have hacc := hb.accretive Q₀ j
      have h := abs_avg_le Q₀ (LocTestFun.trunc (hb.loc j) Q₀) (p.one_lt j).le
      rw [LocTestFun.coe_trunc, avg_truncate_of_subset (subset_refl _)] at h
      have hVmp : Q₀.vol ^ (-(1 / p.p j)) * Q₀.vol ^ (1 / p.p j) = 1 := by
        rw [← Real.rpow_add hV, neg_add_cancel, Real.rpow_zero]
      calc Q₀.vol ^ (1 / p.p j) = 1 * Q₀.vol ^ (1 / p.p j) := (one_mul _).symm
        _ ≤ (Q₀.vol ^ (-(1 / p.p j)) *
              lpNorm ((LocTestFun.trunc (hb.loc j) Q₀ : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j)) *
              Q₀.vol ^ (1 / p.p j) :=
            mul_le_mul_of_nonneg_right (hacc.trans h) (Real.rpow_nonneg hV.le _)
        _ = lpNorm ((LocTestFun.trunc (hb.loc j) Q₀ : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j) *
              (Q₀.vol ^ (-(1 / p.p j)) * Q₀.vol ^ (1 / p.p j)) := by ring
        _ = _ := by rw [hVmp, mul_one]
    calc Q₀.vol ^ (1 - 1 / p.p k) * lpNorm (g : (Fin d → ℝ) → ℝ) (p.p k)
        = lpNorm (g : (Fin d → ℝ) → ℝ) (p.p k) * ∏ j ∈ Finset.univ.erase k, Q₀.vol ^ (1 / p.p j) :=
          by
          rw [← hsum, Real.rpow_sum_of_pos hV]
          ring
      _ ≤ lpNorm (g : (Fin d → ℝ) → ℝ) (p.p k) * ∏ j ∈ Finset.univ.erase k,
            lpNorm ((LocTestFun.trunc (hb.loc j) Q₀ : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j) :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg hV.le _) hterm)
            (lpNorm_nonneg _ _)
  -- the local bound and the assembly
  have hloc := hb.abs_form_tupQ_le hB hCa (p.one_lt k) (hatom k) hsq Q₀ k g hg
  have hcf0 : 0 ≤ ∏ j, |cf j| := Finset.prod_nonneg fun j _ => abs_nonneg _
  have hC0 : 0 ≤ B * (3 * Ca + 1 + Ca * B) := by positivity
  have hS0 : 0 ≤ ∑ j, B ^ p.p j := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (by linarith) _
  have hpn := prodNorm_nonneg p (tupQ hb.loc Q₀ k g)
  rw [hform, hprod, abs_mul, Finset.abs_prod]
  calc (∏ j, |cf j|) * |T.form (tupQ hb.loc Q₀ k g)|
      ≤ (∏ j, |cf j|) * (B * (3 * Ca + 1 + Ca * B) *
          (Q₀.vol ^ (1 - 1 / p.p k) * lpNorm (g : (Fin d → ℝ) → ℝ) (p.p k))) :=
        mul_le_mul_of_nonneg_left (by rw [← mul_assoc]; exact hloc) hcf0
    _ ≤ (∏ j, |cf j|) * (B * (3 * Ca + 1 + Ca * B) * prodNorm p (tupQ hb.loc Q₀ k g)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow hC0) hcf0
    _ = B * (3 * Ca + 1 + Ca * B) * ((∏ j, |cf j|) * prodNorm p (tupQ hb.loc Q₀ k g)) := by ring
    _ ≤ (1 + (∑ j, B ^ p.p j) + B * (3 * Ca + 1 + Ca * B)) *
          ((∏ j, |cf j|) * prodNorm p (tupQ hb.loc Q₀ k g)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hcf0 hpn)

/-- **The hypotheses (1.5)–(1.9) of Theorem 1.4 for the family of the reduction**, for paths of
full length `n` and any collection, with the constant `B₁ = 1 + ∑_j B^{p_j} + B (3 C_a + 1 + C_a
B)`.
[PROVED] -/
theorem GlobalTbHypotheses.localTbHypotheses {T : PerfectCZForm d n} {b : Fin n → (Fin d → ℝ) → ℝ}
    {B : ℝ} (hb : GlobalTbHypotheses T b B) (hB : 1 ≤ B) (p : HolderTuple n) {m : ℕ}
    (hm : m + 1 = n) (C : IPath.Collection n) {Ca : ℝ} (hCa : 0 ≤ Ca)
    (hatom : ∀ (k : Fin n) (Q : DyadicCube d) (h : TestFun d), SupportedOn (h : (Fin d → ℝ) → ℝ) Q →
      MeanZero (h : (Fin d → ℝ) → ℝ) → hardyNorm (h : (Fin d → ℝ) → ℝ) ≤
        Ca * Q.vol ^ (1 - 1 / p.p k) * lpNorm (h : (Fin d → ℝ) → ℝ) (p.p k))
    (hsq : ∀ (Q : DyadicCube d) (h : TestFun d), SupportedOn (h : (Fin d → ℝ) → ℝ) Q →
      MeanZero (h : (Fin d → ℝ) → ℝ) → Integrable (dyadicSquareFun (h : (Fin d → ℝ) → ℝ))) :
    LocalTbHypotheses T p C (globalFamily b m)
      (1 + (∑ j, B ^ p.p j) + B * (3 * Ca + 1 + Ca * B)) where
  support := fun _ _ _ _ _ x hx => by
    simp only [globalFamily, Pi.smul_apply, truncate, Set.indicator_of_notMem hx, smul_zero]
  testFun := fun σ _ Q _ l =>
    ((avg (Q (σ l.castSucc)) (b (σ l.castSucc) : (Fin d → ℝ) → ℝ))⁻¹ •
      LocTestFun.trunc (hb.loc (σ l.castSucc)) (Q (σ l.castSucc))).2
  mean := fun σ _ Q _ l => by
    have hacc := hb.accretive (Q (σ l.castSucc)) (σ l.castSucc)
    have h0 : avg (Q (σ l.castSucc)) (b (σ l.castSucc) : (Fin d → ℝ) → ℝ) ≠ 0 := fun h => by
      rw [h, abs_zero] at hacc
      linarith
    simp only [globalFamily, Pi.smul_apply]
    rw [integral_smul, truncate, integral_indicator (Q _).measurableSet_toSet, ← avg_mul_vol,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
  norm := fun σ _ Q _ l => by
    have hp0 : 0 < p.p (σ l.castSucc) := by linarith [p.one_lt (σ l.castSucc)]
    have hacc := hb.accretive (Q (σ l.castSucc)) (σ l.castSucc)
    have hck1 : |(avg (Q (σ l.castSucc)) (b (σ l.castSucc) : (Fin d → ℝ) → ℝ))⁻¹| ≤ 1 := by
      rw [abs_inv]
      exact inv_le_one_of_one_le₀ hacc
    have hB0 : 0 < B := by linarith
    have hbk := hb.lpNorm_trunc_le hB0.le (Q (σ l.castSucc)) (σ l.castSucc) hp0
    have hV := (Q (σ l.castSucc)).vol_pos
    have hVp0 : 0 ≤ (Q (σ l.castSucc)).vol ^ (1 / p.p (σ l.castSucc)) := Real.rpow_nonneg hV.le _
    have hn : lpNorm (globalFamily b m σ Q l) (p.p (σ l.castSucc)) ≤
        B * (Q (σ l.castSucc)).vol ^ (1 / p.p (σ l.castSucc)) := by
      rw [globalFamily_eq hb.loc, TestFun.lpNorm_smul]
      calc _ ≤ 1 * (B * (Q (σ l.castSucc)).vol ^ (1 / p.p (σ l.castSucc))) :=
            mul_le_mul hck1 hbk (lpNorm_nonneg _ _) zero_le_one
        _ = _ := one_mul _
    have hint : ∫ x, |globalFamily b m σ Q l x| ^ p.p (σ l.castSucc) =
        lpNorm (globalFamily b m σ Q l) (p.p (σ l.castSucc)) ^ p.p (σ l.castSucc) :=
      (lpNorm_rpow_eq_integral hp0 (by
        rw [globalFamily_eq hb.loc]
        exact TestFun.memLp ((avg (Q (σ l.castSucc)) (b (σ l.castSucc) : (Fin d → ℝ) → ℝ))⁻¹ •
          LocTestFun.trunc (hb.loc (σ l.castSucc)) (Q (σ l.castSucc))).2 _)).symm
    rw [hint]
    calc lpNorm (globalFamily b m σ Q l) (p.p (σ l.castSucc)) ^ p.p (σ l.castSucc)
        ≤ (B * (Q (σ l.castSucc)).vol ^ (1 / p.p (σ l.castSucc))) ^ p.p (σ l.castSucc) :=
          Real.rpow_le_rpow (lpNorm_nonneg _ _) hn hp0.le
      _ = B ^ p.p (σ l.castSucc) * (Q (σ l.castSucc)).vol := by
          rw [Real.mul_rpow hB0.le hVp0, ← Real.rpow_mul hV.le, one_div_mul_cancel hp0.ne',
            Real.rpow_one]
      _ ≤ (1 + (∑ i, B ^ p.p i) + B * (3 * Ca + 1 + Ca * B)) * (Q (σ l.castSucc)).vol := by
          refine mul_le_mul_of_nonneg_right ?_ hV.le
          have h1 : B ^ p.p (σ l.castSucc) ≤ ∑ i, B ^ p.p i :=
            Finset.single_le_sum (f := fun i => B ^ p.p i)
              (fun i _ => Real.rpow_nonneg hB0.le _) (Finset.mem_univ _)
          have h2 : 0 ≤ B * (3 * Ca + 1 + Ca * B) := by positivity
          linarith
  interdep := fun σ _ σ' _ Q Q' _ _ l h => by
    obtain ⟨h1, h2⟩ := h l le_rfl
    simp only [globalFamily]
    rw [h2, h1]
  testing := hb.testing_globalFamily hB p hm C hCa hatom hsq

/-- **Theorem 1.11 from Theorem 1.3** (the global/local reduction of [1], p. 38), for `n ≥ 2`,
given the atom estimate for the dyadic Hardy norm with the exponents of the Hölder tuple: the
family `globalFamily` satisfies the hypotheses of Theorem 1.4 for paths of full length `n`, and
Theorem 1.4 (`localTb`) gives the bound (1.16). [PROVED] -/
theorem globalTb_of_localT1 (hn : 2 ≤ n) (p : HolderTuple n) (h13 : LocalT1 d n p)
    (hatom : ∀ j, AtomBound d (p.p j))
    (hsq : ∀ (Q : DyadicCube d) (h : TestFun d), SupportedOn (h : (Fin d → ℝ) → ℝ) Q →
      MeanZero (h : (Fin d → ℝ) → ℝ) → Integrable (dyadicSquareFun (h : (Fin d → ℝ) → ℝ))) :
    GlobalTb d n p := by
  intro hd _ B hB
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  choose Cat hCat0 hCat using hatom
  have hCa0 : 0 ≤ ∑ j, Cat j := Finset.sum_nonneg fun j _ => hCat0 j
  have hatom' : ∀ (k : Fin (m + 1)) (Q : DyadicCube d) (h : TestFun d),
      SupportedOn (h : (Fin d → ℝ) → ℝ) Q → MeanZero (h : (Fin d → ℝ) → ℝ) →
      hardyNorm (h : (Fin d → ℝ) → ℝ) ≤
        (∑ j, Cat j) * Q.vol ^ (1 - 1 / p.p k) * lpNorm (h : (Fin d → ℝ) → ℝ) (p.p k) :=
    fun k Q h hs h0 => (hCat k Q h hs h0).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := Cat) (fun j _ => hCat0 j) (Finset.mem_univ k))
        (Real.rpow_nonneg Q.vol_pos.le _)) (lpNorm_nonneg _ _))
  have hB₁ : 1 ≤ 1 + (∑ j, B ^ p.p j) + B * (3 * (∑ j, Cat j) + 1 + (∑ j, Cat j) * B) := by
    have : 0 ≤ ∑ j, B ^ p.p j := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (by linarith) _
    have : 0 ≤ B * (3 * (∑ j, Cat j) + 1 + (∑ j, Cat j) * B) := by positivity
    linarith
  obtain ⟨C, hC⟩ := localTb hn p h13 (m + 1) (by omega) le_rfl hd (by omega) le_rfl _ hB₁
  refine ⟨C, fun T b hb f => ?_⟩
  exact hC T (IPath.exampleCollection (m + 1)) (IPath.exampleCollection_admissible _)
    (globalFamily b m) (hb.localTbHypotheses hB p rfl _ hCa0 hatom' hsq) f

/-- The zero form, a perfect Calderón–Zygmund form with kernel `0`. -/
noncomputable def PerfectCZForm.zero (d n : ℕ) : PerfectCZForm d n where
  form := 0
  decay := fun p _ f _ _ => by
    rw [zero_apply, abs_zero]
    exact prodNorm_nonneg p f
  smooth := fun _ _ _ _ _ _ _ _ => zero_apply _
  truncation := ⟨0, Submodule.zero_mem _, fun f => by simp⟩

/-- **The hypotheses of Theorem 1.11 are satisfiable, with `b_j = 1`**: for every `B ≥ 1` the zero
form satisfies (1.12)–(1.15) with the constant functions `b_1 = ⋯ = b_n = 1`, which are locally
dyadic test functions without bounded support. In particular Theorem 1.11 is not vacuous, and with
`b_j = 1` its hypotheses are those of a global `T(1)` theorem. [PROVED] -/
theorem globalTbHypotheses_one {n : ℕ} {B : ℝ} (hB : 1 ≤ B) :
    ∃ T : PerfectCZForm d n, GlobalTbHypotheses T (fun _ _ => (1 : ℝ)) B := by
  refine ⟨PerfectCZForm.zero d n, ?_⟩
  have hloc : ∀ _ : Fin n, (fun _ : Fin d → ℝ => (1 : ℝ)) ∈ LocTestFun d := fun _ Q =>
    indicator_mem_testFun Q
  refine ⟨hloc, fun Q _ => ?_, fun _ => ?_, fun Q f _ => ?_, fun K hK hrep j₀ g _ => ?_⟩
  · have h1 : avg Q (fun _ : Fin d → ℝ => (1 : ℝ)) = 1 := by
      rw [avg, setIntegral_const, measureReal_def, Q.volume_toSet,
        ENNReal.toReal_ofReal Q.vol_pos.le, smul_eq_mul, mul_one, div_self Q.vol_pos.ne']
    rw [h1, abs_one]
  · rw [eLpNorm_exponent_top]
    · calc eLpNormEssSup (fun _ : Fin d → ℝ => (1 : ℝ)) volume ≤ ENNReal.ofReal 1 :=
            eLpNormEssSup_le_of_ae_bound (ae_of_all _ fun x => by simp)
        _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hB
    · exact aestronglyMeasurable_const
  · change |(0 : MultilinearMap ℝ (fun _ : Fin n => TestFun d) ℝ) f| ≤ B * Q.vol
    rw [zero_apply, abs_zero]
    exact mul_nonneg (by linarith) Q.vol_pos.le
  · obtain ⟨M, hM⟩ := TestFunProd.exists_abs_lt_pow hK
    rw [← form_update_box_eq_integral (PerfectCZForm.zero d n) hloc hrep hM j₀ g]
    change |(0 : MultilinearMap ℝ (fun _ : Fin n => TestFun d) ℝ) _| ≤ _
    rw [zero_apply, abs_zero]
    exact mul_nonneg (by linarith) (integral_nonneg fun _ => Real.sqrt_nonneg _)

end GlobalReduction

/-! ### The atom estimate for `p ≥ 2`

For a mean-zero `h` supported on `Q`, the square-function series of `hardyNorm h` has only
finitely many nonzero terms: the cubes `P ⊄ Q` contribute nothing (the averages of `h` over `P`
and its children vanish), and so do the cubes below the resolution of `h` (on which `h` is
constant). The remaining cubes `P ⊆ Q` with `Q.m − N < P.m` form the finite family
`StoppingData.nonleaf N Q`, on which the integrand is the dyadic test function
`G = ∑_P ∑_ε ([h]_{P_ε} − [h]_P)² 𝟙_{P_ε}` (`sqFun`). Then `∫ G = ∑_P dsq P h ≤ V_Q h = ‖h‖₂²` by
the
Bessel inequality `sum_dsq_le_var` (the martingale Pythagoras identity), the Cauchy–Schwarz
inequality on `Q` gives `‖h‖_{H¹} = ∫_Q √G ≤ |Q|^{1/2} ‖√G‖₂ ≤ |Q|^{1/2} ‖h‖₂`, and Hölder's
inequality gives `‖h‖₂ ≤ |Q|^{1/2 − 1/p} ‖h‖_p` for `p ≥ 2`. -/

section AtomEstimate

/-- `childAt P x = P_ε` for `x ∈ P_ε`. [PROVED] -/
theorem childAt_eq_of_mem (P : DyadicCube d) {ε : Fin d → Bool} {x : Fin d → ℝ}
    (hx : x ∈ (P.child ε).toSet) : P.childAt x = P.child ε := by
  rcases DyadicCube.eq_or_disjoint_of_m_eq (P.childAt x) (P.child ε) rfl with h | h
  · exact h
  · exact absurd hx (Set.disjoint_left.mp h (P.mem_childAt (P.child_subset ε hx)))

/-- The average of a function constant on `P`. [PROVED] -/
theorem avg_eq_of_constOn {f : (Fin d → ℝ) → ℝ} {P : DyadicCube d} (hf : ConstOn f P)
    {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ P.toSet) : avg P f = f x₀ := by
  rw [avg, setIntegral_congr_fun P.measurableSet_toSet (g := fun _ => f x₀)
    (fun x hx => hf x hx x₀ hx₀), setIntegral_const, measureReal_def, P.volume_toSet,
    ENNReal.toReal_ofReal P.vol_pos.le, smul_eq_mul, mul_comm, mul_div_assoc,
    div_self P.vol_pos.ne', mul_one]

/-- The average over a cube disjoint from the support vanishes. [PROVED] -/
theorem avg_eq_zero_of_disjoint {h : (Fin d → ℝ) → ℝ} {Q P : DyadicCube d}
    (hs : SupportedOn h Q) (hdis : Disjoint P.toSet Q.toSet) : avg P h = 0 := by
  rw [avg, setIntegral_congr_fun P.measurableSet_toSet (g := fun _ => (0 : ℝ))
    (fun x hx => hs x (Set.disjoint_left.mp hdis hx)), integral_zero, zero_div]

/-- The average of a mean-zero function over a cube containing its support vanishes. [PROVED] -/
theorem avg_eq_zero_of_subset_supp {h : (Fin d → ℝ) → ℝ} {Q P : DyadicCube d}
    (hs : SupportedOn h Q) (h0 : MeanZero h) (hQP : Q.toSet ⊆ P.toSet) : avg P h = 0 := by
  have h0' : ∫ x, h x = 0 := h0
  rw [avg, setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hs x fun hxQ => hx (hQP hxQ)), h0', zero_div]

/-- The square-function term of a cube `P ⊄ Q` vanishes identically for a mean-zero `h`
supported on `Q`. [PROVED] -/
theorem sqTerm_eq_zero_of_not_subset (hd : d ≠ 0) {h : (Fin d → ℝ) → ℝ} {Q : DyadicCube d}
    (hs : SupportedOn h Q) (h0 : MeanZero h) {P : DyadicCube d} (hP : ¬ P.toSet ⊆ Q.toSet)
    (x : Fin d → ℝ) :
    P.toSet.indicator (fun y => (avg (P.childAt y) h - avg P h) ^ 2) x = 0 := by
  by_cases hx : x ∈ P.toSet
  · rw [Set.indicator_of_mem hx]
    have hsub : (P.childAt x).toSet ⊆ P.toSet := P.child_subset _
    have hdis : Disjoint P.toSet Q.toSet → (avg (P.childAt x) h - avg P h) ^ 2 = 0 := fun hdis => by
      rw [avg_eq_zero_of_disjoint hs hdis,
        avg_eq_zero_of_disjoint hs (Set.disjoint_of_subset_left hsub hdis), sub_self,
        zero_pow two_ne_zero]
    rcases le_or_gt P.m Q.m with hm | hm
    · rcases DyadicCube.subset_or_disjoint P Q hm with hPQ | hPQ
      · exact absurd hPQ hP
      · exact hdis hPQ
    · rcases DyadicCube.subset_or_disjoint Q P hm.le with hQP | hQP
      · have hne : Q ≠ P := fun e => by
          subst e
          exact hP (subset_refl _)
        obtain ⟨ε₀, hε₀⟩ := DyadicCube.exists_child_of_ssubset hd hQP hne
        rw [avg_eq_zero_of_subset_supp hs h0 hQP]
        rcases DyadicCube.eq_or_disjoint_of_m_eq (P.childAt x) (P.child ε₀) rfl with heq | hdis'
        · rw [heq, avg_eq_zero_of_subset_supp hs h0 hε₀, sub_self, zero_pow two_ne_zero]
        · rw [avg_eq_zero_of_disjoint hs (Set.disjoint_of_subset_right hε₀ hdis'), sub_self,
            zero_pow two_ne_zero]
      · exact hdis hQP.symm
  · exact Set.indicator_of_notMem hx _

/-- The square-function term of a cube on which `h` is constant vanishes. [PROVED] -/
theorem sqTerm_eq_zero_of_const {h : (Fin d → ℝ) → ℝ} {P : DyadicCube d} (hc : ConstOn h P)
    (x : Fin d → ℝ) :
    P.toSet.indicator (fun y => (avg (P.childAt y) h - avg P h) ^ 2) x = 0 := by
  by_cases hx : x ∈ P.toSet
  · have hsub : (P.childAt x).toSet ⊆ P.toSet := P.child_subset _
    rw [Set.indicator_of_mem hx, avg_eq_of_constOn hc hx,
      avg_eq_of_constOn (Bridge.constOn_of_subset hsub hc) (P.mem_childAt hx),
      sub_self, zero_pow two_ne_zero]
  · exact Set.indicator_of_notMem hx _

/-- On `P`, the square-function term is the sum over the children:
`𝟙_P ([h]_{child} − [h]_P)² = ∑_ε ([h]_{P_ε} − [h]_P)² 𝟙_{P_ε}`. [PROVED] -/
theorem sqTerm_eq_sum_children (P : DyadicCube d) (h : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    P.toSet.indicator (fun y => (avg (P.childAt y) h - avg P h) ^ 2) x =
      ∑ ε : Fin d → Bool, (avg (P.child ε) h - avg P h) ^ 2 *
        (P.child ε).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x := by
  by_cases hx : x ∈ P.toSet
  · rw [Set.indicator_of_mem hx]
    obtain ⟨ε₀, hε₀⟩ : ∃ ε₀, x ∈ (P.child ε₀).toSet := ⟨_, P.mem_childAt hx⟩
    rw [Finset.sum_eq_single ε₀]
    · rw [Set.indicator_of_mem hε₀, Pi.one_apply, mul_one, childAt_eq_of_mem P hε₀]
    · intro ε _ hne
      have hx' : x ∉ (P.child ε).toSet := by
        intro hx'
        rcases DyadicCube.eq_or_disjoint_of_m_eq (P.child ε) (P.child ε₀) rfl with heq | hdis
        · exact hne (P.child_injective heq)
        · exact Set.disjoint_left.mp hdis hx' hε₀
      rw [Set.indicator_of_notMem hx', mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [Set.indicator_of_notMem hx]
    symm
    exact Finset.sum_eq_zero fun ε _ => by
      rw [Set.indicator_of_notMem (fun hx' => hx (P.child_subset ε hx')), mul_zero]

/-- The square-function integrand of `h` at resolution `N` relative to `Q`, as a dyadic test
function: `G = ∑_{P ∈ nonleaf N Q} ∑_ε ([h]_{P_ε} − [h]_P)² 𝟙_{P_ε}`. -/
noncomputable def sqFun (Q : DyadicCube d) (N : ℕ) (h : TestFun d) : TestFun d :=
  ∑ P ∈ StoppingData.nonleaf N Q, ∑ ε : Fin d → Bool,
    ((avg (P.child ε) h - avg P h) ^ 2) • TestFun.ind (P.child ε)

theorem sqFun_apply (Q : DyadicCube d) (N : ℕ) (h : TestFun d) (x : Fin d → ℝ) :
    (sqFun Q N h : (Fin d → ℝ) → ℝ) x = ∑ P ∈ StoppingData.nonleaf N Q, ∑ ε : Fin d → Bool,
      (avg (P.child ε) h - avg P h) ^ 2 * (P.child ε).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x := by
  simp only [sqFun, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, TestFun.coe_ind]

theorem sqFun_nonneg (Q : DyadicCube d) (N : ℕ) (h : TestFun d) (x : Fin d → ℝ) :
    0 ≤ (sqFun Q N h : (Fin d → ℝ) → ℝ) x := by
  rw [sqFun_apply]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem sqFun_eq_zero (hd : d ≠ 0) {Q : DyadicCube d} {N : ℕ} {h : TestFun d} {x : Fin d → ℝ}
    (hx : x ∉ Q.toSet) : (sqFun Q N h : (Fin d → ℝ) → ℝ) x = 0 := by
  rw [sqFun_apply]
  refine Finset.sum_eq_zero fun P hP => Finset.sum_eq_zero fun ε _ => ?_
  rw [Set.indicator_of_notMem (fun hx' => hx (((StoppingData.mem_nonleaf_iff hd).mp hP).1
    (P.child_subset ε hx'))), mul_zero]

/-- **The square-function series is the finite sum `sqFun`** for a mean-zero `h` supported on
`Q` with resolution `N`. [PROVED] -/
theorem tsum_sqTerm_eq (hd : d ≠ 0) {Q : DyadicCube d} {N : ℕ} {h : TestFun d}
    (hs : SupportedOn (h : (Fin d → ℝ) → ℝ) Q) (h0 : MeanZero (h : (Fin d → ℝ) → ℝ))
    (hres : ∀ T : DyadicCube d, T.toSet ⊆ Q.toSet → T.m = Q.m - N →
      ConstOn (h : (Fin d → ℝ) → ℝ) T) (x : Fin d → ℝ) :
    ∑' P : DyadicCube d, P.toSet.indicator (fun y => (avg (P.childAt y) h - avg P h) ^ 2) x =
      (sqFun Q N h : (Fin d → ℝ) → ℝ) x := by
  have hzero : ∀ P ∉ StoppingData.nonleaf N Q,
      P.toSet.indicator (fun y => (avg (P.childAt y) h - avg P h) ^ 2) x = 0 := by
    intro P hP
    rw [StoppingData.mem_nonleaf_iff hd] at hP
    by_cases hPQ : P.toSet ⊆ Q.toSet
    · have hm : P.m ≤ Q.m - N := not_lt.mp fun hlt => hP ⟨hPQ, hlt⟩
      obtain ⟨T', hPT', hm', hT'Q⟩ := Bridge.exists_superset_of_le hPQ hm (by omega)
      exact sqTerm_eq_zero_of_const (Bridge.constOn_of_subset hPT' (hres T' hT'Q hm')) x
    · exact sqTerm_eq_zero_of_not_subset hd hs h0 hPQ x
  rw [sqFun_apply, tsum_eq_sum hzero]
  exact Finset.sum_congr rfl fun P _ => sqTerm_eq_sum_children P h x

/-- `∫ G = ∑_{P ∈ nonleaf N Q} dsq P h`. [PROVED] -/
theorem integral_sqFun (Q : DyadicCube d) (N : ℕ) (h : TestFun d) :
    ∫ x, (sqFun Q N h : (Fin d → ℝ) → ℝ) x = ∑ P ∈ StoppingData.nonleaf N Q, dsq P h := by
  rw [← TestFun.integralₗ_apply, sqFun, map_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [map_smul, smul_eq_mul, TestFun.integralₗ_apply,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => TestFun.ind_supportedOn (P.child ε) x hx),
    StoppingData.TestFun.setIntegral_ind_of_subset (subset_refl _)]

/-- **Bessel's inequality for the finite family**: `∑_{P ∈ nonleaf N Q} dsq P h ≤ V_Q h`. [PROVED]
-/
theorem sum_dsq_nonleaf_le_var (hd : d ≠ 0) (Q : DyadicCube d) (N : ℕ) (h : TestFun d) :
    ∑ P ∈ StoppingData.nonleaf N Q, dsq P h ≤ var Q h := by
  classical
  have hf : ∀ P : DyadicCube d, IntegrableOn (h : (Fin d → ℝ) → ℝ) P.toSet volume :=
    fun _ => (TestFun.integrable h.2).integrableOn
  have hsq : Integrable (fun x => (h : (Fin d → ℝ) → ℝ) x ^ 2) volume :=
    ((TestFun.memLp h.2 2).integrable_mul (TestFun.memLp h.2 2)).congr
      (ae_of_all _ fun x => (sq ((h : (Fin d → ℝ) → ℝ) x)).symm)
  have hf2 : ∀ P : DyadicCube d, IntegrableOn (fun x => (h : (Fin d → ℝ) → ℝ) x ^ 2) P.toSet volume
    :=
    fun _ => hsq.integrableOn
  have := sum_dsq_le_var hd hf hf2 (StoppingData.nonleaf N Q) N Q
    (fun P hP _ => ((StoppingData.mem_nonleaf_iff hd).mp hP).2.le)
  rwa [Finset.filter_true_of_mem (fun P hP => ((StoppingData.mem_nonleaf_iff hd).mp hP).1)] at this

/-- `V_Q h = ‖h‖₂²` for a mean-zero `h` supported on `Q`. [PROVED] -/
theorem var_eq_lpNorm_sq {Q : DyadicCube d} {h : TestFun d} (hs : SupportedOn (h : (Fin d → ℝ) → ℝ)
  Q)
    (h0 : MeanZero (h : (Fin d → ℝ) → ℝ)) : var Q h = lpNorm (h : (Fin d → ℝ) → ℝ) 2 ^ 2 := by
  have h2 : lpNorm (h : (Fin d → ℝ) → ℝ) 2 ^ 2 = ∫ x, (h : (Fin d → ℝ) → ℝ) x ^ 2 := by
    have := lpNorm_rpow_eq_integral two_pos (TestFun.memLp h.2 (ENNReal.ofReal 2))
    simp only [Real.rpow_two] at this
    rw [this]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [sq_abs])
  rw [var, avg_eq_zero_of_subset_supp hs h0 (subset_refl _), zero_pow two_ne_zero, zero_mul,
    sub_zero, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hs x hx, zero_pow two_ne_zero]), h2]

/-- Hölder: `‖h‖₂ ≤ ‖h‖_p |Q|^{1/2 − 1/p}` for `p ≥ 2` and `h` supported on `Q`. [PROVED] -/
theorem lpNorm_two_le_lpNorm {Q : DyadicCube d} {h : TestFun d}
    (hs : SupportedOn (h : (Fin d → ℝ) → ℝ) Q) {p : ℝ} (hp : 2 ≤ p) :
    lpNorm (h : (Fin d → ℝ) → ℝ) 2 ≤ lpNorm (h : (Fin d → ℝ) → ℝ) p * Q.vol ^ (1 / 2 - 1 / p) := by
  have hp0 : 0 < p := by linarith
  have hexp : (0 : ℝ) ≤ 1 / 2 - 1 / p := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le two_pos hp
  have e : Q.toSet.indicator (h : (Fin d → ℝ) → ℝ) = h :=
    congrArg Subtype.val (TestFun.truncateₗ_of_supportedOn hs)
  have key : ∀ r : ℝ, eLpNorm (h : (Fin d → ℝ) → ℝ) (ENNReal.ofReal r) (volume.restrict Q.toSet) =
      eLpNorm (h : (Fin d → ℝ) → ℝ) (ENNReal.ofReal r) volume := fun r => by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict Q.measurableSet_toSet.nullMeasurableSet, e]
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict Q.toSet)
    (ENNReal.ofReal_le_ofReal hp)
    (TestFun.memLp h.2 (ENNReal.ofReal 2)).aestronglyMeasurable.restrict
  rw [key, key, Measure.restrict_apply_univ, Q.volume_toSet, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal hp0.le] at h1
  have hfin : eLpNorm (h : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) volume *
      ENNReal.ofReal Q.vol ^ (1 / 2 - 1 / p) ≠ ⊤ :=
    ENNReal.mul_ne_top (TestFun.memLp h.2 _).eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexp ENNReal.ofReal_ne_top)
  unfold lpNorm
  calc (eLpNorm (h : (Fin d → ℝ) → ℝ) (ENNReal.ofReal 2) volume).toReal
      ≤ (eLpNorm (h : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) volume *
          ENNReal.ofReal Q.vol ^ (1 / 2 - 1 / p)).toReal := ENNReal.toReal_mono hfin h1
    _ = _ := by rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal Q.vol_pos.le]

/-- **The atom estimate for `p ≥ 2`**, with constant `1`: for a mean-zero `h` supported on `Q`,
`‖h‖_{H¹} ≤ |Q|^{1−1/p} ‖h‖_p`. [PROVED] -/
theorem atomBound_of_two_le (hd : d ≠ 0) {p : ℝ} (hp : 2 ≤ p) : AtomBound d p := by
  refine ⟨1, zero_le_one, fun Q h hs h0 => ?_⟩
  obtain ⟨N, hres⟩ := Bridge.exists_resolution h Q
  have hG0 : ∀ x, 0 ≤ (sqFun Q N h : (Fin d → ℝ) → ℝ) x := sqFun_nonneg Q N h
  have hV := Q.vol_pos
  -- the integrand of the Hardy norm is `√G`
  have hint : hardyNorm (h : (Fin d → ℝ) → ℝ) =
      ∫ x, Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) := by
    unfold hardyNorm dyadicSquareFun
    exact integral_congr_ae (ae_of_all _ fun x => congrArg Real.sqrt (tsum_sqTerm_eq hd hs h0 hres
      x))
  -- `√G` is in `L²` and supported on `Q`
  have hmeas : AEStronglyMeasurable (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x))
      volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (TestFun.memLp (sqFun Q N h).2 1).aestronglyMeasurable
  have hsq : Integrable (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) ^ 2) volume :=
    (TestFun.integrable (sqFun Q N h).2).congr (ae_of_all _ fun x => (Real.sq_sqrt (hG0 x)).symm)
  have hmem : MemLp (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x))
      (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hmeas).mpr hsq
  have hsupp : ∫ x, Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) =
      ∫ x in Q.toSet, Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [sqFun_eq_zero hd hx, Real.sqrt_zero]).symm
  -- Cauchy–Schwarz on `Q`
  have hCS := abs_setIntegral_le_rpow_mul_lpNorm (p := 2) one_le_two hmem Q.measurableSet_toSet
    (by rw [Q.volume_toSet]; exact ENNReal.ofReal_ne_top)
  rw [Q.volume_toSet, ENNReal.toReal_ofReal hV.le] at hCS
  -- `‖√G‖₂² = ∫ G = ∑ dsq ≤ V_Q h = ‖h‖₂²`
  have hL2 : lpNorm (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)) 2 ^ 2 ≤
      lpNorm (h : (Fin d → ℝ) → ℝ) 2 ^ 2 := by
    have e1 := lpNorm_rpow_eq_integral two_pos hmem
    simp only [Real.rpow_two] at e1
    rw [e1]
    calc ∫ x, |Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)| ^ 2
        = ∫ x, (sqFun Q N h : (Fin d → ℝ) → ℝ) x :=
          integral_congr_ae (ae_of_all _ fun x => by
            simp only [sq_abs, Real.sq_sqrt (hG0 x)])
      _ = ∑ P ∈ StoppingData.nonleaf N Q, dsq P h := integral_sqFun Q N h
      _ ≤ var Q h := sum_dsq_nonleaf_le_var hd Q N h
      _ = lpNorm (h : (Fin d → ℝ) → ℝ) 2 ^ 2 := var_eq_lpNorm_sq hs h0
  have hL2' : lpNorm (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)) 2 ≤
      lpNorm (h : (Fin d → ℝ) → ℝ) 2 :=
    (pow_le_pow_iff_left₀ (lpNorm_nonneg _ _) (lpNorm_nonneg _ _) two_ne_zero).mp hL2
  have hH := lpNorm_two_le_lpNorm hs hp
  have hexp : Q.vol ^ ((1 : ℝ) - 1 / 2) * Q.vol ^ (1 / 2 - 1 / p) = Q.vol ^ (1 - 1 / p) := by
    rw [← Real.rpow_add hV]
    congr 1
    ring
  calc hardyNorm (h : (Fin d → ℝ) → ℝ)
      = ∫ x in Q.toSet, Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) := by rw [hint, hsupp]
    _ ≤ |∫ x in Q.toSet, Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)| := le_abs_self _
    _ ≤ Q.vol ^ ((1 : ℝ) - 1 / 2) *
          lpNorm (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)) 2 := hCS
    _ ≤ Q.vol ^ ((1 : ℝ) - 1 / 2) * (lpNorm (h : (Fin d → ℝ) → ℝ) p * Q.vol ^ (1 / 2 - 1 / p)) :=
        mul_le_mul_of_nonneg_left (hL2'.trans hH) (Real.rpow_nonneg hV.le _)
    _ = 1 * Q.vol ^ (1 - 1 / p) * lpNorm (h : (Fin d → ℝ) → ℝ) p := by
        rw [← hexp]
        ring

end AtomEstimate

/-! ### The dyadic square function on a finite family: weak type `(1,1)` and strong type `(2,2)`

Towards the atom estimate for `1 < p < 2` (Burkholder's inequality). For a finite family `S` of
cubes, `G_S f = ∑_{P ∈ S} ∑_ε ([f]_{P_ε} − [f]_P)² 𝟙_{P_ε}` (`sqFunS`) is the square of the dyadic
square function restricted to `S`, and `√(G_S f)` is sublinear in `f` (Minkowski's inequality).
For `S = nonleaf N Q`, the Calderón–Zygmund cubes `𝓕` at height `λ` for `|f|` give the weak-type
estimate `|{√(G f) > λ}| ≤ (4·2^d + 1) ‖f‖₁/λ`: the good part (the cubes outside `𝒢`) has
`∫ G_good ≤ 2^d λ ‖f‖₁` by a sharpened form of the stopped Bessel inequality (the bound
`‖g‖₂² ≤ ‖g‖_∞ ‖g‖₁` for the good function, without forming `g`), and Markov's inequality applies;
the bad part is supported in `⋃ 𝓕`, whose measure is at most `‖f‖₁/λ`. The strong type `(2,2)`
is the Bessel inequality `∫ G f ≤ ‖f‖₂²`. -/

section SquareFunctionWeakType


variable {f : (Fin d → ℝ) → ℝ}

/-- `[f]_{T_ε}² |T_ε| ≤ 2^d λ ∫_{T_ε} |f|` for the children of `T ∉ 𝒢`. [PROVED] -/
theorem energy_child_le_integral (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) {T : DyadicCube d} (hT : T ∉ badTrees (fun x => |f x|) lam)
    (ε : Fin d → Bool) :
    avg (T.child ε) f ^ 2 * (T.child ε).vol ≤ 2 ^ d * lam * ∫ x in (T.child ε).toSet, |f x| := by
  have h1 : |avg (T.child ε) f| ≤ avg (T.child ε) (fun x => |f x|) := abs_avg_le_avg_abs _ f
  have h2 := avg_abs_child_le hd hf hlam hT ε
  have hV := (T.child ε).vol_pos
  calc avg (T.child ε) f ^ 2 * (T.child ε).vol
      = |avg (T.child ε) f| ^ 2 * (T.child ε).vol := by rw [sq_abs]
    _ ≤ 2 ^ d * lam * avg (T.child ε) (fun x => |f x|) * (T.child ε).vol := by
        refine mul_le_mul_of_nonneg_right ?_ hV.le
        rw [sq]
        exact mul_le_mul (h1.trans h2) h1 (abs_nonneg _) (by positivity)
    _ = 2 ^ d * lam * ∫ x in (T.child ε).toSet, |f x| := by rw [mul_assoc, avg_mul_vol]

/-- `∑_ε ∫_{T_ε} |f| = ∫_T |f|`. [PROVED] -/
theorem sum_setIntegral_abs_children (T : DyadicCube d) (hf : Integrable f volume) :
    ∑ ε : Fin d → Bool, ∫ x in (T.child ε).toSet, |f x| = ∫ x in T.toSet, |f x| :=
  (T.integral_children hf.abs.integrableOn).symm

open Classical in
/-- **The sharpened stopped Bessel inequality**: for `T ∉ 𝒢` and a finite family `F` of cubes of
bounded depth below `T`, `∑_{Q ∈ F, Q ⊆ T, Q ∉ 𝒢} ‖Δ_Q f‖² |Q| ≤ 2^d λ ∫_T |f| − [f]_T² |T|` (the
bound `‖g‖₂² ≤ ‖g‖_∞ ‖g‖₁ ≤ 2^d λ ‖f‖₁` for the good function of the Calderón–Zygmund
decomposition, without forming `g`). Induction on the depth. [PROVED] -/
theorem sum_dsq_stopped_le_integral (hd : d ≠ 0) (hf : Integrable f volume) {lam : ℝ}
    (hlam : 0 < lam) (F : Finset (DyadicCube d)) (n : ℕ) :
    ∀ T : DyadicCube d, T ∉ badTrees (fun x => |f x|) lam →
      (∀ Q ∈ F, Q.toSet ⊆ T.toSet → T.m - (n : ℤ) ≤ Q.m) →
      ∑ Q ∈ F.filter (fun Q => Q.toSet ⊆ T.toSet ∧ Q ∉ badTrees (fun x => |f x|) lam),
          dsq Q f ≤
        2 ^ d * lam * (∫ x in T.toSet, |f x|) - avg T f ^ 2 * T.vol := by
  classical
  intro T hT hdepth
  convert sum_dsq_stopped_le_of_child_energy hd hf
    (fun Q => Q ∉ badTrees (fun x => |f x|) lam) ?_
    (fun T => 2 ^ d * lam * ∫ x in T.toSet, |f x|) ?_
    (fun T hT ε => energy_child_le_integral hd hf hlam hT ε) F n T hT hdepth using 1
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext Q
    simp only [Finset.mem_filter]
  · intro Q R hQR hQ hR
    obtain ⟨P, hP, hRP⟩ := hR
    exact hQ ⟨P, hP, hQR.trans hRP⟩
  · intro T
    rw [← Finset.mul_sum, sum_setIntegral_abs_children T hf]

/-- The square-function integrand on a finite family `S` of cubes:
`G_S h = ∑_{P ∈ S} ∑_ε ([h]_{P_ε} − [h]_P)² 𝟙_{P_ε}`. -/
noncomputable def sqFunS (S : Finset (DyadicCube d)) (h : TestFun d) : TestFun d :=
  ∑ P ∈ S, ∑ ε : Fin d → Bool, ((avg (P.child ε) h - avg P h) ^ 2) • TestFun.ind (P.child ε)

theorem sqFun_eq_sqFunS (Q : DyadicCube d) (N : ℕ) (h : TestFun d) :
    sqFun Q N h = sqFunS (StoppingData.nonleaf N Q) h := rfl

theorem sqFunS_apply (S : Finset (DyadicCube d)) (h : TestFun d) (x : Fin d → ℝ) :
    (sqFunS S h : (Fin d → ℝ) → ℝ) x = ∑ P ∈ S, ∑ ε : Fin d → Bool,
      (avg (P.child ε) h - avg P h) ^ 2 * (P.child ε).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x := by
  simp only [sqFunS, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, TestFun.coe_ind]

theorem sqFunS_nonneg (S : Finset (DyadicCube d)) (h : TestFun d) (x : Fin d → ℝ) :
    0 ≤ (sqFunS S h : (Fin d → ℝ) → ℝ) x := by
  rw [sqFunS_apply]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- `∫ G_S h = ∑_{P ∈ S} dsq P h`. [PROVED] -/
theorem integral_sqFunS (S : Finset (DyadicCube d)) (h : TestFun d) :
    ∫ x, (sqFunS S h : (Fin d → ℝ) → ℝ) x = ∑ P ∈ S, dsq P h := by
  rw [← TestFun.integralₗ_apply, sqFunS, map_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [map_smul, smul_eq_mul, TestFun.integralₗ_apply,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => TestFun.ind_supportedOn (P.child ε) x hx),
    StoppingData.TestFun.setIntegral_ind_of_subset (subset_refl _)]

/-- Splitting the family: `G_S = G_{S ∩ p} + G_{S ∖ p}`. [PROVED] -/
theorem sqFunS_filter_add (S : Finset (DyadicCube d)) (p : DyadicCube d → Prop)
    [DecidablePred p] (h : TestFun d) :
    sqFunS S h = sqFunS (S.filter p) h + sqFunS (S.filter (fun P => ¬ p P)) h := by
  unfold sqFunS
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- `√(a + b) ≤ √a + √b`. [PROVED] -/
theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
  apply Real.sqrt_le_sqrt
  rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- Minkowski's inequality for finite sums (the unweighted case of `sqrt_sum_sq_add_le`):
`√(∑ (a_i + b_i)²) ≤ √(∑ a_i²) + √(∑ b_i²)`. [PROVED] -/
theorem sqrt_sum_sq_add_le_univ {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    Real.sqrt (∑ i, (a i + b i) ^ 2) ≤ Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2) := by
  have := sqrt_sum_sq_add_le (Finset.univ : Finset ι) a b (fun _ => 1) (fun _ => zero_le_one)
  simpa only [mul_one] using this

theorem avg_add_coe (P : DyadicCube d) (f g : TestFun d) :
    avg P ((f + g : TestFun d) : (Fin d → ℝ) → ℝ) =
      avg P (f : (Fin d → ℝ) → ℝ) + avg P (g : (Fin d → ℝ) → ℝ) := by
  rw [Submodule.coe_add]
  exact avg_add P (TestFun.integrable f.2).integrableOn (TestFun.integrable g.2).integrableOn

/-- **Sublinearity of the square function**: `√(G_S (f + g)) ≤ √(G_S f) + √(G_S g)` pointwise.
[PROVED] -/
theorem sqrt_sqFunS_add_le (S : Finset (DyadicCube d)) (f g : TestFun d) (x : Fin d → ℝ) :
    Real.sqrt ((sqFunS S (f + g) : (Fin d → ℝ) → ℝ) x) ≤
      Real.sqrt ((sqFunS S f : (Fin d → ℝ) → ℝ) x) +
        Real.sqrt ((sqFunS S g : (Fin d → ℝ) → ℝ) x) := by
  have hind : ∀ (P : DyadicCube d) (ε : Fin d → Bool),
      ((P.child ε).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x) ^ 2 =
        (P.child ε).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x := by
    intro P ε
    by_cases hx : x ∈ (P.child ε).toSet <;> simp [hx]
  have e : ∀ h : TestFun d, (sqFunS S h : (Fin d → ℝ) → ℝ) x =
      ∑ i : ↥S × (Fin d → Bool), ((avg ((i.1 : DyadicCube d).child i.2) h -
        avg (i.1 : DyadicCube d) h) *
          ((i.1 : DyadicCube d).child i.2).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x) ^ 2 := by
    intro h
    rw [sqFunS_apply, Fintype.sum_prod_type, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun ε _ => ?_
    rw [mul_pow, hind]
  have key := sqrt_sum_sq_add_le_univ (ι := ↥S × (Fin d → Bool))
    (fun i => (avg ((i.1 : DyadicCube d).child i.2) f - avg (i.1 : DyadicCube d) f) *
      ((i.1 : DyadicCube d).child i.2).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x)
    (fun i => (avg ((i.1 : DyadicCube d).child i.2) g - avg (i.1 : DyadicCube d) g) *
      ((i.1 : DyadicCube d).child i.2).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x)
  rw [e f, e g, e (f + g)]
  refine le_of_eq_of_le ?_ key
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [avg_add_coe, avg_add_coe]
  ring

/-- **Weak type `(1,1)` of the square function on `nonleaf N Q`**:
`|{√(G f) > λ}| ≤ (4·2^d + 1) ‖f‖₁ / λ`, by the Calderón–Zygmund decomposition at height `λ`.
[PROVED] -/
theorem volume_sqrt_sqFun_gt_le (hd : d ≠ 0) (Q : DyadicCube d) (N : ℕ) (f : TestFun d)
    {lam : ℝ} (hlam : 0 < lam) :
    volume {x | lam < Real.sqrt ((sqFun Q N f : (Fin d → ℝ) → ℝ) x)} ≤
      ENNReal.ofReal ((4 * 2 ^ d + 1) * (∫ x, |(f : (Fin d → ℝ) → ℝ) x|) / lam) := by
  classical
  have hfi : Integrable (f : (Fin d → ℝ) → ℝ) volume := TestFun.integrable f.2
  have hI0 : 0 ≤ ∫ x, |(f : (Fin d → ℝ) → ℝ) x| := integral_nonneg fun x => abs_nonneg _
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hC : (1 : ℝ) ≤ 4 * 2 ^ d + 1 := by linarith
  have hsubQ : {x | lam < Real.sqrt ((sqFun Q N f : (Fin d → ℝ) → ℝ) x)} ⊆ Q.toSet := by
    intro x hx
    by_contra hxQ
    have h0 : (sqFun Q N f : (Fin d → ℝ) → ℝ) x = 0 := sqFun_eq_zero hd hxQ
    have hx' : lam < Real.sqrt ((sqFun Q N f : (Fin d → ℝ) → ℝ) x) := hx
    rw [h0, Real.sqrt_zero] at hx'
    linarith
  by_cases hQ : Q ∈ badTrees (fun x => |(f : (Fin d → ℝ) → ℝ) x|) lam
  · obtain ⟨R, hR, hQR⟩ := hQ
    have hvol := vol_lt_of_mem_badCubes hfi.abs hlam hR.1
    simp only [abs_abs] at hvol
    calc volume {x | lam < Real.sqrt ((sqFun Q N f : (Fin d → ℝ) → ℝ) x)}
        ≤ volume Q.toSet := measure_mono hsubQ
      _ ≤ volume R.toSet := measure_mono hQR
      _ = ENNReal.ofReal R.vol := R.volume_toSet
      _ ≤ ENNReal.ofReal ((∫ x, |(f : (Fin d → ℝ) → ℝ) x|) / lam) :=
          ENNReal.ofReal_le_ofReal hvol.le
      _ ≤ _ := ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_mul_of_one_le_left hI0 hC) hlam.le)
  · -- `Q ∉ 𝒢`: the good and the bad cubes of `nonleaf N Q`
    set F := StoppingData.nonleaf N Q
    set good := F.filter (fun P => P.toSet ⊆ Q.toSet ∧
      P ∉ badTrees (fun x => |(f : (Fin d → ℝ) → ℝ) x|) lam)
    set bad := F.filter (fun P => ¬ (P.toSet ⊆ Q.toSet ∧
      P ∉ badTrees (fun x => |(f : (Fin d → ℝ) → ℝ) x|) lam)) with hbad
    have hsplit : sqFun Q N f = sqFunS good f + sqFunS bad f := sqFunS_filter_add F _ f
    -- the good part: `∫ G_good ≤ 2^d λ ‖f‖₁`, then Markov
    have hgood_int : ∫ x, (sqFunS good f : (Fin d → ℝ) → ℝ) x ≤
        2 ^ d * lam * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| := by
      rw [integral_sqFunS]
      have h1 := sum_dsq_stopped_le_integral hd hfi hlam F N Q hQ
        (fun P hP _ => ((StoppingData.mem_nonleaf_iff hd).mp hP).2.le)
      have h2 : ∫ x in Q.toSet, |(f : (Fin d → ℝ) → ℝ) x| ≤ ∫ x, |(f : (Fin d → ℝ) → ℝ) x| :=
        setIntegral_le_integral hfi.abs (ae_of_all _ fun x => abs_nonneg _)
      have h3 : 0 ≤ avg Q (f : (Fin d → ℝ) → ℝ) ^ 2 * Q.vol :=
        mul_nonneg (sq_nonneg _) Q.vol_pos.le
      have h4 : (0 : ℝ) ≤ 2 ^ d * lam := by positivity
      calc ∑ P ∈ good, dsq P f
          ≤ 2 ^ d * lam * (∫ x in Q.toSet, |(f : (Fin d → ℝ) → ℝ) x|) -
              avg Q (f : (Fin d → ℝ) → ℝ) ^ 2 * Q.vol := h1
        _ ≤ 2 ^ d * lam * ∫ x, |(f : (Fin d → ℝ) → ℝ) x| := by
            linarith [mul_le_mul_of_nonneg_left h2 h4]
    have hG0 : ∀ x, 0 ≤ (sqFunS good f : (Fin d → ℝ) → ℝ) x := sqFunS_nonneg good f
    have hmarkov : volume {x | lam / 2 < Real.sqrt ((sqFunS good f : (Fin d → ℝ) → ℝ) x)} ≤
        ENNReal.ofReal (4 * 2 ^ d * (∫ x, |(f : (Fin d → ℝ) → ℝ) x|) / lam) := by
      have hsub : {x | lam / 2 < Real.sqrt ((sqFunS good f : (Fin d → ℝ) → ℝ) x)} ⊆
          {x | ENNReal.ofReal ((lam / 2) ^ 2) ≤
            ENNReal.ofReal ((sqFunS good f : (Fin d → ℝ) → ℝ) x)} := by
        intro x hx
        have hx' : lam / 2 < Real.sqrt ((sqFunS good f : (Fin d → ℝ) → ℝ) x) := hx
        exact ENNReal.ofReal_le_ofReal ((Real.lt_sqrt (by positivity)).mp hx').le
      have hmeas : AEMeasurable (fun x => ENNReal.ofReal ((sqFunS good f : (Fin d → ℝ) → ℝ) x))
          volume :=
        ENNReal.measurable_ofReal.comp_aemeasurable
          (TestFun.memLp (sqFunS good f).2 1).aestronglyMeasurable.aemeasurable
      have hM := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal ((lam / 2) ^ 2))
      rw [← ofReal_integral_eq_lintegral_ofReal (TestFun.integrable (sqFunS good f).2)
        (ae_of_all _ hG0)] at hM
      have hε : ENNReal.ofReal ((lam / 2) ^ 2) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        positivity
      calc volume {x | lam / 2 < Real.sqrt ((sqFunS good f : (Fin d → ℝ) → ℝ) x)}
          ≤ volume {x | ENNReal.ofReal ((lam / 2) ^ 2) ≤
              ENNReal.ofReal ((sqFunS good f : (Fin d → ℝ) → ℝ) x)} := measure_mono hsub
        _ ≤ ENNReal.ofReal (∫ x, (sqFunS good f : (Fin d → ℝ) → ℝ) x) /
              ENNReal.ofReal ((lam / 2) ^ 2) := by
            rw [ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
            exact hM
        _ = ENNReal.ofReal ((∫ x, (sqFunS good f : (Fin d → ℝ) → ℝ) x) / (lam / 2) ^ 2) :=
            (ENNReal.ofReal_div_of_pos (by positivity)).symm
        _ ≤ ENNReal.ofReal (4 * 2 ^ d * (∫ x, |(f : (Fin d → ℝ) → ℝ) x|) / lam) := by
            apply ENNReal.ofReal_le_ofReal
            rw [div_le_div_iff₀ (by positivity) hlam]
            linarith [mul_le_mul_of_nonneg_right hgood_int hlam.le]
    -- the bad part is supported in the union of the maximal bad cubes
    have hbad_supp : ∀ x, (sqFunS bad f : (Fin d → ℝ) → ℝ) x ≠ 0 → ∃ P ∈ bad, x ∈ P.toSet := by
      intro x hx
      rw [sqFunS_apply] at hx
      obtain ⟨P, hP, hPx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨ε, -, hεx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hPx
      refine ⟨P, hP, ?_⟩
      by_contra hxP
      exact hεx (by rw [Set.indicator_of_notMem (fun h => hxP (P.child_subset ε h)), mul_zero])
    have hbadR : ∀ P ∈ bad, ∃ R ∈ maxBadCubes (fun x => |(f : (Fin d → ℝ) → ℝ) x|) lam,
        P.toSet ⊆ R.toSet := by
      intro P hP
      rw [hbad, Finset.mem_filter] at hP
      have hPQ := ((StoppingData.mem_nonleaf_iff hd).mp hP.1).1
      have : P ∈ badTrees (fun x => |(f : (Fin d → ℝ) → ℝ) x|) lam := by
        by_contra h
        exact hP.2 ⟨hPQ, h⟩
      exact this
    choose! R hRmax hPR using hbadR
    set s := bad.image R with hs
    have hbad_set : {x | lam / 2 < Real.sqrt ((sqFunS bad f : (Fin d → ℝ) → ℝ) x)} ⊆
        ⋃ R' ∈ s, R'.toSet := by
      intro x hx
      have hx0 : (sqFunS bad f : (Fin d → ℝ) → ℝ) x ≠ 0 := by
        intro h0
        have hx' : lam / 2 < Real.sqrt ((sqFunS bad f : (Fin d → ℝ) → ℝ) x) := hx
        rw [h0, Real.sqrt_zero] at hx'
        linarith
      obtain ⟨P, hP, hxP⟩ := hbad_supp x hx0
      exact Set.mem_biUnion (Finset.mem_image_of_mem R hP) (hPR P hP hxP)
    have hvol_s : ∑ R' ∈ s, R'.vol ≤ (∫ x, |(f : (Fin d → ℝ) → ℝ) x|) / lam := by
      have := sum_vol_le_of_lt_abs_avg s (fun R' => R') ?_ hfi.abs hlam ?_
      · simpa [abs_abs] using this
      · intro R₁ hR₁ R₂ hR₂ hne
        rw [Finset.mem_coe, hs, Finset.mem_image] at hR₁ hR₂
        obtain ⟨P₁, hP₁, rfl⟩ := hR₁
        obtain ⟨P₂, hP₂, rfl⟩ := hR₂
        exact maxBad_disjoint (hRmax P₁ hP₁) (hRmax P₂ hP₂) hne
      · intro R' hR'
        rw [hs, Finset.mem_image] at hR'
        obtain ⟨P, hP, rfl⟩ := hR'
        exact (hRmax P hP).1
    have hvol_bad : volume (⋃ R' ∈ s, R'.toSet) ≤
        ENNReal.ofReal ((∫ x, |(f : (Fin d → ℝ) → ℝ) x|) / lam) := by
      calc volume (⋃ R' ∈ s, R'.toSet) ≤ ∑ R' ∈ s, volume R'.toSet := measure_biUnion_finset_le s _
        _ = ENNReal.ofReal (∑ R' ∈ s, R'.vol) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun R' _ => R'.vol_pos.le)]
            exact Finset.sum_congr rfl fun R' _ => R'.volume_toSet
        _ ≤ _ := ENNReal.ofReal_le_ofReal hvol_s
    -- combine
    have hsub2 : {x | lam < Real.sqrt ((sqFun Q N f : (Fin d → ℝ) → ℝ) x)} ⊆
        {x | lam / 2 < Real.sqrt ((sqFunS good f : (Fin d → ℝ) → ℝ) x)} ∪
          {x | lam / 2 < Real.sqrt ((sqFunS bad f : (Fin d → ℝ) → ℝ) x)} := by
      intro x hx
      have hx' : lam < Real.sqrt ((sqFun Q N f : (Fin d → ℝ) → ℝ) x) := hx
      have hle : Real.sqrt ((sqFun Q N f : (Fin d → ℝ) → ℝ) x) ≤
          Real.sqrt ((sqFunS good f : (Fin d → ℝ) → ℝ) x) +
            Real.sqrt ((sqFunS bad f : (Fin d → ℝ) → ℝ) x) := by
        rw [hsplit, Submodule.coe_add, Pi.add_apply]
        exact sqrt_add_le' (sqFunS_nonneg _ _ _) (sqFunS_nonneg _ _ _)
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
      linarith [hcon.1, hcon.2]
    calc volume {x | lam < Real.sqrt ((sqFun Q N f : (Fin d → ℝ) → ℝ) x)}
        ≤ volume ({x | lam / 2 < Real.sqrt ((sqFunS good f : (Fin d → ℝ) → ℝ) x)} ∪
            {x | lam / 2 < Real.sqrt ((sqFunS bad f : (Fin d → ℝ) → ℝ) x)}) := measure_mono hsub2
      _ ≤ volume {x | lam / 2 < Real.sqrt ((sqFunS good f : (Fin d → ℝ) → ℝ) x)} +
            volume {x | lam / 2 < Real.sqrt ((sqFunS bad f : (Fin d → ℝ) → ℝ) x)} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (4 * 2 ^ d * (∫ x, |(f : (Fin d → ℝ) → ℝ) x|) / lam) +
            ENNReal.ofReal ((∫ x, |(f : (Fin d → ℝ) → ℝ) x|) / lam) :=
          add_le_add hmarkov ((measure_mono hbad_set).trans hvol_bad)
      _ = ENNReal.ofReal ((4 * 2 ^ d + 1) * (∫ x, |(f : (Fin d → ℝ) → ℝ) x|) / lam) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

/-- **Strong type `(2,2)`**: `∫ G f = ∑_P dsq P f ≤ ‖f‖₂²`. [PROVED] -/
theorem integral_sqFun_le (hd : d ≠ 0) (Q : DyadicCube d) (N : ℕ) (f : TestFun d) :
    ∫ x, (sqFun Q N f : (Fin d → ℝ) → ℝ) x ≤ ∫ x, (f : (Fin d → ℝ) → ℝ) x ^ 2 := by
  rw [integral_sqFun]
  have hsq : Integrable (fun x => (f : (Fin d → ℝ) → ℝ) x ^ 2) volume :=
    ((TestFun.memLp f.2 2).integrable_mul (TestFun.memLp f.2 2)).congr
      (ae_of_all _ fun x => (sq ((f : (Fin d → ℝ) → ℝ) x)).symm)
  calc ∑ P ∈ StoppingData.nonleaf N Q, dsq P f ≤ var Q f := sum_dsq_nonleaf_le_var hd Q N f
    _ ≤ ∫ x in Q.toSet, (f : (Fin d → ℝ) → ℝ) x ^ 2 := by
        rw [var]
        linarith [mul_nonneg (sq_nonneg (avg Q (f : (Fin d → ℝ) → ℝ))) Q.vol_pos.le]
    _ ≤ ∫ x, (f : (Fin d → ℝ) → ℝ) x ^ 2 :=
        setIntegral_le_integral hsq (ae_of_all _ fun x => sq_nonneg _)

end SquareFunctionWeakType

/-! ### The `L^p` bound for the square function, `1 < p < 2`, and the atom estimate

Marcinkiewicz interpolation between the weak type `(1,1)` and the strong type `(2,2)` of the
restricted square function `S f = √(G f)`, `G = sqFun Q N`, on dyadic test functions `f`
supported on `Q` with resolution `N`. The class of such functions is closed under the truncations
`f 𝟙_{|f| > t}`, `f 𝟙_{|f| ≤ t}`: every function constant on the leaves `𝒟_N(Q)` of the tree is the
leaf sum `∑_{L ∈ 𝒟_N(Q)} g(x_L) 𝟙_L` (`leafSum`), a dyadic test function. For `t > 0`, by
sublinearity `|{S f > t}| ≤ |{S f_t > t/2}| + |{S f^t > t/2}|` with `f_t = f 𝟙_{|f| > t}`,
`f^t = f 𝟙_{|f| ≤ t}`; the weak type `(1,1)` bounds the first term by `2A ‖f_t‖₁/t` and Markov's
inequality with the strong type `(2,2)` the second by `4 ‖f^t‖₂²/t²`. The layer-cake formula
`∫ (S f)^p = p ∫_0^∞ t^{p-1} |{S f > t}| dt` and Tonelli's theorem then give
`∫ (S f)^p ≤ p (2A/(p-1) + 4/(2-p)) ∫ |f|^p`. Since `S f` is itself constant on the leaves, Hölder's
inequality on `Q` gives the atom estimate `‖h‖_{H¹} = ∫_Q S h ≤ |Q|^{1-1/p} ‖S h‖_p ≤
C_p |Q|^{1-1/p} ‖h‖_p` for `1 < p < 2`, and with the case `p ≥ 2` the atom estimate holds for all
`p > 1`, so that Theorem 1.11 follows from Theorem 1.3 without further hypotheses. -/

section SquareFunctionLp


/-- Dyadic test functions are measurable. [PROVED] -/
theorem TestFun.measurable (f : TestFun d) : Measurable (f : (Fin d → ℝ) → ℝ) := by
  have hf : (f : (Fin d → ℝ) → ℝ) ∈
      Submodule.span ℝ (Set.range (DyadicCube.indicator (d := d))) := f.2
  refine Submodule.span_induction (p := fun g _ => Measurable g) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨P, rfl⟩
    exact measurable_const.indicator P.measurableSet_toSet
  · exact measurable_const
  · intro g₁ g₂ _ _ h₁ h₂
    exact h₁.add h₂
  · intro c g _ h
    exact h.const_smul c

/-- The leaf sum `∑_{L ∈ 𝒟_N(Q)} g(x_L) 𝟙_L` of a function `g`, where `x_L` is the corner of `L`:
for `g` constant on the leaves this is `g 𝟙_Q`. -/
noncomputable def leafSum (Q : DyadicCube d) (N : ℕ) (g : (Fin d → ℝ) → ℝ) : TestFun d :=
  ∑ L ∈ StoppingData.level N Q, g (fun i => (2 : ℝ) ^ L.m * L.l i) • TestFun.ind L

/-- `leafSum Q N g = g 𝟙_Q` for `g` constant on the leaves of `𝒟_N(Q)`. [PROVED] -/
theorem leafSum_apply (Q : DyadicCube d) (N : ℕ) {g : (Fin d → ℝ) → ℝ}
    (hg : ∀ L ∈ StoppingData.level N Q, ConstOn g L) (x : Fin d → ℝ) :
    (leafSum Q N g : (Fin d → ℝ) → ℝ) x = Q.toSet.indicator g x := by
  simp only [leafSum, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, TestFun.coe_ind]
  by_cases hx : x ∈ Q.toSet
  · obtain ⟨L₀, hL₀, hxL₀⟩ := StoppingData.exists_mem_level N hx
    rw [Set.indicator_of_mem hx, Finset.sum_eq_single L₀]
    · rw [Set.indicator_of_mem hxL₀, Pi.one_apply, mul_one]
      exact hg L₀ hL₀ _ L₀.corner_mem x hxL₀
    · intro L hL hne
      rcases StoppingData.level_eq_or_disjoint hL hL₀ with h | h
      · exact absurd h hne
      · rw [Set.indicator_of_notMem (Set.disjoint_right.mp h hxL₀), mul_zero]
    · intro h
      exact absurd hL₀ h
  · rw [Set.indicator_of_notMem hx]
    refine Finset.sum_eq_zero fun L hL => ?_
    rw [Set.indicator_of_notMem (fun h => hx (StoppingData.subset_of_mem_level hL h)), mul_zero]

/-- `leafSum Q N g = g` for `g` supported on `Q` and constant on the leaves. [PROVED] -/
theorem coe_leafSum (Q : DyadicCube d) (N : ℕ) {g : (Fin d → ℝ) → ℝ}
    (hg : ∀ L ∈ StoppingData.level N Q, ConstOn g L) (hs : SupportedOn g Q) :
    (leafSum Q N g : (Fin d → ℝ) → ℝ) = g := by
  funext x
  rw [leafSum_apply Q N hg x]
  by_cases hx : x ∈ Q.toSet
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hs x hx]

/-- The resolution hypothesis gives constancy on the leaves. [PROVED] -/
theorem constOn_level_of_res {Q : DyadicCube d} {N : ℕ} {g : (Fin d → ℝ) → ℝ}
    (hres : ∀ T : DyadicCube d, T.toSet ⊆ Q.toSet → T.m = Q.m - N → ConstOn g T) :
    ∀ L ∈ StoppingData.level N Q, ConstOn g L := fun L hL =>
  hres L (StoppingData.mem_level_iff.mp hL).1 (StoppingData.mem_level_iff.mp hL).2

/-- `g 𝟙_{P(g)}` is constant on `L` when `g` is. [PROVED] -/
theorem constOn_indicator_pred {g : (Fin d → ℝ) → ℝ} {L : DyadicCube d} (hg : ConstOn g L)
    (P : ℝ → Prop) : ConstOn ({x | P (g x)}.indicator g) L := fun x hx y hy => by
  classical
  have := hg x hx y hy
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, this]

/-- `g 𝟙_{P(g)}ᶜ` is constant on `L` when `g` is. [PROVED] -/
theorem constOn_indicator_pred_compl {g : (Fin d → ℝ) → ℝ} {L : DyadicCube d} (hg : ConstOn g L)
    (P : ℝ → Prop) : ConstOn ({x | P (g x)}ᶜ.indicator g) L := fun x hx y hy => by
  classical
  have := hg x hx y hy
  simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_ofPred_eq, this]

/-- **The truncations are dyadic test functions**: for `h` supported on `Q` with resolution `N`
and `t ∈ ℝ`, `h 𝟙_{|h| > t}` and `h 𝟙_{|h| ≤ t}` are dyadic test functions summing to `h`.
[PROVED] -/
theorem exists_trunc_abs_gt {Q : DyadicCube d} {N : ℕ} {h : TestFun d}
    (hs : SupportedOn (h : (Fin d → ℝ) → ℝ) Q)
    (hres : ∀ T : DyadicCube d, T.toSet ⊆ Q.toSet → T.m = Q.m - N →
      ConstOn (h : (Fin d → ℝ) → ℝ) T) (t : ℝ) :
    ∃ b s : TestFun d,
      (b : (Fin d → ℝ) → ℝ) = {x | t < |(h : (Fin d → ℝ) → ℝ) x|}.indicator h ∧
      (s : (Fin d → ℝ) → ℝ) = {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator h ∧
      h = b + s := by
  have hL := constOn_level_of_res hres
  have hs' : ∀ S : Set (Fin d → ℝ), SupportedOn (S.indicator (h : (Fin d → ℝ) → ℝ)) Q :=
    fun S x hx => Set.indicator_apply_eq_zero.mpr fun _ => hs x hx
  have hb := coe_leafSum Q N (fun L hL' => constOn_indicator_pred (hL L hL') (fun r => t < |r|))
    (hs' _)
  have hsm := coe_leafSum Q N
    (fun L hL' => constOn_indicator_pred_compl (hL L hL') (fun r => t < |r|)) (hs' _)
  refine ⟨_, _, hb, hsm, ?_⟩
  apply Subtype.ext
  rw [Submodule.coe_add, hb, hsm, Set.indicator_self_add_compl]

/-- **The superlevel sets of `S h` via the truncations**: for `t > 0`,
`|{S h > t}| ≤ (2A/t) ∫_{|h|>t} |h| + (4/t²) ∫_{|h|≤t} |h|²`, `A = 4·2^d + 1`, by sublinearity, the
weak type `(1,1)` for `h 𝟙_{|h|>t}` and Markov's inequality with the strong type `(2,2)` for
`h 𝟙_{|h|≤t}`. [PROVED] -/
theorem volume_sqrt_sqFun_gt_le_trunc (hd : d ≠ 0) {Q : DyadicCube d} {N : ℕ} {h : TestFun d}
    (hs : SupportedOn (h : (Fin d → ℝ) → ℝ) Q)
    (hres : ∀ T : DyadicCube d, T.toSet ⊆ Q.toSet → T.m = Q.m - N →
      ConstOn (h : (Fin d → ℝ) → ℝ) T) {t : ℝ} (ht : 0 < t) :
    volume {x | t < Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)} ≤
      ENNReal.ofReal (2 * (4 * 2 ^ d + 1) / t) *
          (∫⁻ x, {x | t < |(h : (Fin d → ℝ) → ℝ) x|}.indicator
            (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ) x) +
        ENNReal.ofReal (4 / t ^ 2) *
          ∫⁻ x, {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator
            (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) x := by
  obtain ⟨big, small, hbig, hsmall, hsum⟩ := exists_trunc_abs_gt hs hres t
  have ht2 : 0 < t / 2 := by positivity
  have hsub : {x | t < Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)} ⊆
      {x | t / 2 < Real.sqrt ((sqFun Q N big : (Fin d → ℝ) → ℝ) x)} ∪
        {x | t / 2 < Real.sqrt ((sqFun Q N small : (Fin d → ℝ) → ℝ) x)} := by
    intro x hx
    have hx' : t < Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) := hx
    have hle : Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) ≤
        Real.sqrt ((sqFun Q N big : (Fin d → ℝ) → ℝ) x) +
          Real.sqrt ((sqFun Q N small : (Fin d → ℝ) → ℝ) x) := by
      rw [hsum]
      simp only [sqFun_eq_sqFunS]
      exact sqrt_sqFunS_add_le _ big small x
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    linarith [hcon.1, hcon.2]
  -- the big part: weak type `(1,1)`
  have hbig_int : Integrable (big : (Fin d → ℝ) → ℝ) volume := TestFun.integrable big.2
  have h1 : volume {x | t / 2 < Real.sqrt ((sqFun Q N big : (Fin d → ℝ) → ℝ) x)} ≤
      ENNReal.ofReal (2 * (4 * 2 ^ d + 1) / t) *
        ∫⁻ x, {x | t < |(h : (Fin d → ℝ) → ℝ) x|}.indicator
          (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ) x := by
    refine (volume_sqrt_sqFun_gt_le hd Q N big ht2).trans (le_of_eq ?_)
    have e1 : ENNReal.ofReal (∫ x, |(big : (Fin d → ℝ) → ℝ) x|) =
        ∫⁻ x, ‖(big : (Fin d → ℝ) → ℝ) x‖ₑ := by
      have := ofReal_integral_norm_eq_lintegral_enorm hbig_int
      simpa only [Real.norm_eq_abs] using this
    rw [show (4 * 2 ^ d + 1) * (∫ x, |(big : (Fin d → ℝ) → ℝ) x|) / (t / 2) =
        (2 * (4 * 2 ^ d + 1) / t) * ∫ x, |(big : (Fin d → ℝ) → ℝ) x| by
          rw [div_div_eq_mul_div]; ring,
      ENNReal.ofReal_mul (by positivity), e1]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [hbig]
    exact enorm_indicator_eq_indicator_enorm _ x
  -- the small part: Markov and the strong type `(2,2)`
  have hsm_int : Integrable (fun x => (small : (Fin d → ℝ) → ℝ) x ^ 2) volume :=
    ((TestFun.memLp small.2 2).integrable_mul (TestFun.memLp small.2 2)).congr
      (ae_of_all _ fun x => (sq ((small : (Fin d → ℝ) → ℝ) x)).symm)
  have hG0 : ∀ x, 0 ≤ (sqFun Q N small : (Fin d → ℝ) → ℝ) x := sqFun_nonneg Q N small
  have h2 : volume {x | t / 2 < Real.sqrt ((sqFun Q N small : (Fin d → ℝ) → ℝ) x)} ≤
      ENNReal.ofReal (4 / t ^ 2) *
        ∫⁻ x, {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator
          (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) x := by
    have hsub2 : {x | t / 2 < Real.sqrt ((sqFun Q N small : (Fin d → ℝ) → ℝ) x)} ⊆
        {x | ENNReal.ofReal ((t / 2) ^ 2) ≤
          ENNReal.ofReal ((sqFun Q N small : (Fin d → ℝ) → ℝ) x)} := by
      intro x hx
      have hx' : t / 2 < Real.sqrt ((sqFun Q N small : (Fin d → ℝ) → ℝ) x) := hx
      exact ENNReal.ofReal_le_ofReal ((Real.lt_sqrt ht2.le).mp hx').le
    have hmeas : AEMeasurable (fun x => ENNReal.ofReal ((sqFun Q N small : (Fin d → ℝ) → ℝ) x))
        volume :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (TestFun.memLp (sqFun Q N small).2 1).aestronglyMeasurable.aemeasurable
    have hM := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal ((t / 2) ^ 2))
    rw [← ofReal_integral_eq_lintegral_ofReal (TestFun.integrable (sqFun Q N small).2)
      (ae_of_all _ hG0)] at hM
    have hε : ENNReal.ofReal ((t / 2) ^ 2) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hI : ENNReal.ofReal (∫ x, (sqFun Q N small : (Fin d → ℝ) → ℝ) x) ≤
        ∫⁻ x, {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator
          (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) x := by
      calc ENNReal.ofReal (∫ x, (sqFun Q N small : (Fin d → ℝ) → ℝ) x)
          ≤ ENNReal.ofReal (∫ x, (small : (Fin d → ℝ) → ℝ) x ^ 2) :=
            ENNReal.ofReal_le_ofReal (integral_sqFun_le hd Q N small)
        _ = ∫⁻ x, ENNReal.ofReal ((small : (Fin d → ℝ) → ℝ) x ^ 2) :=
            ofReal_integral_eq_lintegral_ofReal hsm_int (ae_of_all _ fun x => sq_nonneg _)
        _ = _ := by
            refine lintegral_congr fun x => ?_
            rw [hsmall]
            by_cases hx : x ∈ {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ
            · simp only [Set.indicator_of_mem hx]
              rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
            · simp only [Set.indicator_of_notMem hx]
              simp
    calc volume {x | t / 2 < Real.sqrt ((sqFun Q N small : (Fin d → ℝ) → ℝ) x)}
        ≤ volume {x | ENNReal.ofReal ((t / 2) ^ 2) ≤
            ENNReal.ofReal ((sqFun Q N small : (Fin d → ℝ) → ℝ) x)} := measure_mono hsub2
      _ ≤ ENNReal.ofReal (∫ x, (sqFun Q N small : (Fin d → ℝ) → ℝ) x) /
            ENNReal.ofReal ((t / 2) ^ 2) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
          exact hM
      _ ≤ (∫⁻ x, {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator
            (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) x) / ENNReal.ofReal ((t / 2) ^ 2) := by
          gcongr
      _ = _ := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos (by positivity)]
          congr 2
          rw [div_pow, inv_div]
          norm_num
  calc volume {x | t < Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)}
      ≤ volume ({x | t / 2 < Real.sqrt ((sqFun Q N big : (Fin d → ℝ) → ℝ) x)} ∪
          {x | t / 2 < Real.sqrt ((sqFun Q N small : (Fin d → ℝ) → ℝ) x)}) := measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- The `p`-th power `C_p^p = p (2A/(p-1) + 4/(2-p))`, `A = 4·2^d + 1`, of the constant of the
`L^p` bound for the square function. -/
noncomputable def sqConst (d : ℕ) (p : ℝ) : ℝ :=
  p * (2 * (4 * 2 ^ d + 1) / (p - 1) + 4 / (2 - p))

theorem sqConst_nonneg {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : 0 ≤ sqConst d p := by
  unfold sqConst
  have h1 : (0 : ℝ) ≤ 2 * (4 * 2 ^ d + 1) / (p - 1) := div_nonneg (by positivity) (by linarith)
  have h2 : (0 : ℝ) ≤ 4 / (2 - p) := div_nonneg (by norm_num) (by linarith)
  exact mul_nonneg (by linarith) (add_nonneg h1 h2)

/-- The weighted tail integral used in the square-function interpolation estimate. -/
private theorem lintegral_weighted_tail (h : (Fin d → ℝ) → ℝ) (hhm : Measurable h)
    {p A : ℝ} (hp1 : 1 < p) (hA : 0 ≤ A) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * A * t ^ (p - 2)) *
        ∫⁻ x, {x | t < |h x|}.indicator (fun x => ‖h x‖ₑ) x =
      ENNReal.ofReal (2 * A / (p - 1)) * ∫⁻ x, ‖h x‖ₑ ^ p := by
  classical
  have hp0 : 0 < p := zero_lt_one.trans hp1
  have hp1' : 0 < p - 1 := sub_pos.mpr hp1
  let I₁ : ℝ → ENNReal := fun t =>
    ∫⁻ x, {x | t < |h x|}.indicator (fun x => ‖h x‖ₑ) x
  have hI₁ : I₁ = fun t => ∫⁻ x,
      {x | t < |h x|}.indicator (fun x => ‖h x‖ₑ) x := rfl
  calc ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * A * t ^ (p - 2)) * I₁ t
      = ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x, ENNReal.ofReal (2 * A * t ^ (p - 2)) *
          {x | t < |(h : (Fin d → ℝ) → ℝ) x|}.indicator
            (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ) x := by
        rw [hI₁]
        exact lintegral_congr fun t => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ x, ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * A * t ^ (p - 2)) *
          {x | t < |(h : (Fin d → ℝ) → ℝ) x|}.indicator
            (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ) x := by
        apply lintegral_lintegral_swap
        refine Measurable.aemeasurable ?_
        have hset : MeasurableSet {q : ℝ × (Fin d → ℝ) | q.1 < |(h : (Fin d → ℝ) → ℝ) q.2|} := by
          have := measurableSet_lt measurable_fst (hhm.comp measurable_snd).norm
          simpa only [Real.norm_eq_abs, Function.comp] using this
        have h1 : Measurable fun q : ℝ × (Fin d → ℝ) =>
            ENNReal.ofReal (2 * A * q.1 ^ (p - 2)) :=
          ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const (p - 2)))
        have h2 : Measurable fun q : ℝ × (Fin d → ℝ) =>
            {x | q.1 < |(h : (Fin d → ℝ) → ℝ) x|}.indicator
              (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ) q.2 := by
          simp only [Set.indicator_apply, Set.mem_ofPred_eq]
          exact Measurable.ite hset (hhm.comp measurable_snd).enorm measurable_const
        exact h1.mul h2
    _ = ∫⁻ x, ENNReal.ofReal (2 * A / (p - 1)) * ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ p := by
        refine lintegral_congr fun x => ?_
        set b : ℝ := |(h : (Fin d → ℝ) → ℝ) x| with hb_def
        have hb : 0 ≤ b := abs_nonneg _
        have hind : ∀ t : ℝ, {x | t < |(h : (Fin d → ℝ) → ℝ) x|}.indicator
            (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ) x =
              (Set.Iio b).indicator (fun _ => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ) t := by
          intro t
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iio, hb_def]
        simp_rw [hind]
        have hfun : (fun t => ENNReal.ofReal (2 * A * t ^ (p - 2)) *
            (Set.Iio b).indicator (fun _ => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ) t) =
            (Set.Iio b).indicator fun t => ENNReal.ofReal (2 * A * t ^ (p - 2)) *
              ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ := by
          funext t
          by_cases ht : t ∈ Set.Iio b
          · simp [Set.indicator_of_mem ht]
          · simp [Set.indicator_of_notMem ht]
        rw [hfun, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict
          measurableSet_Iio,
          show Set.Iio b ∩ Set.Ioi 0 = Set.Ioo 0 b by
            ext t
            simp [and_comm],
          lintegral_mul_const' _ _ enorm_ne_top]
        have hint : IntegrableOn (fun t : ℝ => 2 * A * t ^ (p - 2)) (Set.Ioo 0 b) volume := by
          have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
            (by linarith : (-1 : ℝ) < p - 2)).const_mul (2 * A)
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb] at this
          exact this.mono_set Set.Ioo_subset_Ioc_self
        have hK1 : 0 ≤ 2 * A * (b ^ (p - 2 + 1) / (p - 2 + 1)) :=
          mul_nonneg (mul_nonneg (by norm_num) hA)
            (div_nonneg (Real.rpow_nonneg hb _) (by linarith))
        have hK2 : 0 ≤ 2 * A / (p - 1) := div_nonneg (mul_nonneg (by norm_num) hA) hp1'.le
        rw [← ofReal_integral_eq_lintegral_ofReal hint
            (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => by
              have : 0 < t := ht.1
              positivity),
          ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb,
          intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
          Real.zero_rpow (by linarith), sub_zero, Real.enorm_eq_ofReal_abs, ← hb_def,
          ← ENNReal.ofReal_mul hK1, ENNReal.ofReal_rpow_of_nonneg hb hp0.le,
          ← ENNReal.ofReal_mul hK2]
        congr 1
        have hfp : b ^ p = b ^ (p - 1) * b := by
          rw [← Real.rpow_add_one' hb (y := p - 1) (by linarith)]
          congr 1
          ring
        rw [show p - 2 + 1 = p - 1 by ring, hfp]
        ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The `L^p` bound for the square function, `1 < p < 2`** (Burkholder's inequality for the
restricted dyadic square function), for test functions supported on `Q` with resolution `N`:
`∫ (S h)^p ≤ C_p^p ∫ |h|^p`, by the layer-cake formula, the bound for the superlevel sets via the
truncations, and Tonelli's theorem. [PROVED] -/
theorem lintegral_sqrt_sqFun_rpow_le (hd : d ≠ 0) {Q : DyadicCube d} {N : ℕ} {h : TestFun d}
    (hs : SupportedOn (h : (Fin d → ℝ) → ℝ) Q)
    (hres : ∀ T : DyadicCube d, T.toSet ⊆ Q.toSet → T.m = Q.m - N →
      ConstOn (h : (Fin d → ℝ) → ℝ) T) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∫⁻ x, ENNReal.ofReal (Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) ^ p) ≤
      ENNReal.ofReal (sqConst d p) * ∫⁻ x, ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ p := by
  obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = 4 * 2 ^ d + 1 := ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [hA_def]; positivity
  have hp0 : 0 < p := by linarith
  have hp1' : 0 < p - 1 := by linarith
  have hp2' : 0 < 2 - p := by linarith
  have hhm : Measurable (h : (Fin d → ℝ) → ℝ) := TestFun.measurable h
  have hSm : AEMeasurable (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)) volume :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (TestFun.memLp (sqFun Q N h).2 1).aestronglyMeasurable).aemeasurable
  -- the two slice integrals, monotone in `t` and hence measurable
  obtain ⟨I₁, hI₁⟩ : ∃ I₁ : ℝ → ENNReal, I₁ = fun t => ∫⁻ x,
      {x | t < |(h : (Fin d → ℝ) → ℝ) x|}.indicator (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ) x :=
    ⟨_, rfl⟩
  obtain ⟨I₂, hI₂⟩ : ∃ I₂ : ℝ → ENNReal, I₂ = fun t => ∫⁻ x,
      {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator
        (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) x :=
    ⟨_, rfl⟩
  have hmI₁ : Measurable I₁ := by
    rw [hI₁]
    refine Antitone.measurable fun s t hst => lintegral_mono fun x => ?_
    exact Set.indicator_le_indicator_of_subset (fun x hx => lt_of_le_of_lt hst hx)
      (fun _ => bot_le) x
  have hmI₂ : Measurable I₂ := by
    rw [hI₂]
    refine Monotone.measurable fun s t hst => lintegral_mono fun x => ?_
    refine Set.indicator_le_indicator_of_subset (fun x hx => ?_) (fun _ => bot_le) x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hx ⊢
    exact hx.trans hst
  -- the pointwise bound on the superlevel measure
  have key : ∀ t : ℝ, 0 < t →
      volume {a | t < Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) a)} *
          ENNReal.ofReal (t ^ (p - 1)) ≤
        ENNReal.ofReal (2 * A * t ^ (p - 2)) * I₁ t + ENNReal.ofReal (4 * t ^ (p - 3)) * I₂ t := by
    intro t ht
    have e1 : 2 * A / t * t ^ (p - 1) = 2 * A * t ^ (p - 2) := by
      have : t ^ (p - 2) = t ^ (p - 1) / t := by
        rw [← Real.rpow_sub_one ht.ne']
        congr 1
        ring
      rw [this]
      ring
    have e2 : 4 / t ^ 2 * t ^ (p - 1) = 4 * t ^ (p - 3) := by
      have : t ^ (p - 3) = t ^ (p - 1) / t ^ (2 : ℝ) := by
        rw [← Real.rpow_sub ht]
        congr 1
        ring
      rw [this, Real.rpow_two]
      ring
    calc volume {a | t < Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) a)} *
          ENNReal.ofReal (t ^ (p - 1))
        ≤ (ENNReal.ofReal (2 * A / t) * I₁ t + ENNReal.ofReal (4 / t ^ 2) * I₂ t) *
            ENNReal.ofReal (t ^ (p - 1)) := by
          gcongr
          simp only [hI₁, hI₂, hA_def]
          exact volume_sqrt_sqFun_gt_le_trunc hd hs hres ht
      _ = _ := by
          rw [add_mul, mul_right_comm (ENNReal.ofReal (2 * A / t)),
            mul_right_comm (ENNReal.ofReal (4 / t ^ 2)), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), e1, e2]
  have hm1 : Measurable fun t : ℝ => ENNReal.ofReal (2 * A * t ^ (p - 2)) * I₁ t :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))).mul hmI₁
  -- the first slice integral: `∫_0^∞ 2A t^{p-2} ∫_{|h|>t} |h| dt = (2A/(p-1)) ∫ |h|^p`
  have hJ₁ : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * A * t ^ (p - 2)) * I₁ t =
      ENNReal.ofReal (2 * A / (p - 1)) * ∫⁻ x, ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ p := by
    rw [hI₁]
    exact lintegral_weighted_tail (h : (Fin d → ℝ) → ℝ) hhm hp1 hA
  -- the second slice integral: `∫_0^∞ 4 t^{p-3} ∫_{|h|≤t} |h|² dt = (4/(2-p)) ∫ |h|^p`
  have hJ₂ : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (4 * t ^ (p - 3)) * I₂ t =
      ENNReal.ofReal (4 / (2 - p)) * ∫⁻ x, ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ p := by
    calc ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (4 * t ^ (p - 3)) * I₂ t
        = ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x, ENNReal.ofReal (4 * t ^ (p - 3)) *
            {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator
              (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) x := by
          rw [hI₂]
          exact lintegral_congr fun t => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ x, ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (4 * t ^ (p - 3)) *
            {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator
              (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) x := by
          apply lintegral_lintegral_swap
          refine Measurable.aemeasurable ?_
          have hset : MeasurableSet {q : ℝ × (Fin d → ℝ) | |(h : (Fin d → ℝ) → ℝ) q.2| ≤ q.1} := by
            have := measurableSet_le (hhm.comp measurable_snd).norm measurable_fst
            simpa only [Real.norm_eq_abs, Function.comp] using this
          have h1 : Measurable fun q : ℝ × (Fin d → ℝ) =>
              ENNReal.ofReal (4 * q.1 ^ (p - 3)) :=
            ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const (p - 3)))
          have h2 : Measurable fun q : ℝ × (Fin d → ℝ) =>
              {x | q.1 < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator
                (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) q.2 := by
            simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
            exact Measurable.ite hset ((hhm.comp measurable_snd).enorm.pow_const 2)
              measurable_const
          exact h1.mul h2
      _ = ∫⁻ x, ENNReal.ofReal (4 / (2 - p)) * ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ p := by
          refine lintegral_congr fun x => ?_
          set b : ℝ := |(h : (Fin d → ℝ) → ℝ) x| with hb_def
          have hb : 0 ≤ b := abs_nonneg _
          have hind : ∀ t : ℝ, {x | t < |(h : (Fin d → ℝ) → ℝ) x|}ᶜ.indicator
              (fun x => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) x =
                (Set.Ici b).indicator (fun _ => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) t := by
            intro t
            simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_Ici,
              not_lt, hb_def]
          simp_rw [hind]
          have hfun : (fun t => ENNReal.ofReal (4 * t ^ (p - 3)) *
              (Set.Ici b).indicator (fun _ => ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2) t) =
              (Set.Ici b).indicator fun t => ENNReal.ofReal (4 * t ^ (p - 3)) *
                ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ 2 := by
            funext t
            by_cases ht : t ∈ Set.Ici b
            · simp [Set.indicator_of_mem ht]
            · simp [Set.indicator_of_notMem ht]
          rw [hfun, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict
            measurableSet_Ici,
            lintegral_mul_const' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
          by_cases hb0 : b = 0
          · have hx0 : ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ = 0 := by
              rw [Real.enorm_eq_ofReal_abs, ← hb_def, hb0, ENNReal.ofReal_zero]
            rw [hx0, zero_pow two_ne_zero, mul_zero, ENNReal.zero_rpow_of_pos hp0, mul_zero]
          · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
            rw [Set.inter_eq_left.mpr (Set.Ici_subset_Ioi.mpr hbpos),
              ← Measure.restrict_congr_set Ioi_ae_eq_Ici]
            have hint : IntegrableOn (fun t : ℝ => 4 * t ^ (p - 3)) (Set.Ioi b) volume :=
              (integrableOn_Ioi_rpow_of_lt (by linarith) hbpos).const_mul 4
            have e : -b ^ (p - 3 + 1) / (p - 3 + 1) = b ^ (p - 2) / (2 - p) := by
              rw [show p - 3 + 1 = p - 2 by ring, neg_div, ← div_neg, neg_sub]
            have hK1 : 0 ≤ 4 * (b ^ (p - 2) / (2 - p)) :=
              mul_nonneg (by norm_num) (div_nonneg (Real.rpow_nonneg hb _) hp2'.le)
            have hK2 : (0 : ℝ) ≤ 4 / (2 - p) := div_nonneg (by norm_num) hp2'.le
            rw [← ofReal_integral_eq_lintegral_ofReal hint
                (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
                  have : 0 < t := hbpos.trans ht
                  positivity),
              integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hbpos, e,
              Real.enorm_eq_ofReal_abs, ← hb_def, ← ENNReal.ofReal_pow hb,
              ENNReal.ofReal_rpow_of_nonneg hb hp0.le, ← ENNReal.ofReal_mul hK1,
              ← ENNReal.ofReal_mul hK2]
            congr 1
            have hfp : b ^ p = b ^ (p - 2) * b ^ 2 := by
              rw [← Real.rpow_two, ← Real.rpow_add hbpos]
              congr 1
              ring
            rw [hfp]
            ring
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- the layer-cake formula
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume (ae_of_all _ fun x => Real.sqrt_nonneg _)
    hSm hp0]
  calc ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ),
        volume {a | t < Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) a)} *
          ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ),
          (ENNReal.ofReal (2 * A * t ^ (p - 2)) * I₁ t +
            ENNReal.ofReal (4 * t ^ (p - 3)) * I₂ t) := by
        refine mul_le_mul' le_rfl ?_
        exact setLIntegral_mono' measurableSet_Ioi fun t ht => key t ht
    _ = ENNReal.ofReal p * ((∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * A * t ^ (p - 2)) * I₁ t) +
          ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (4 * t ^ (p - 3)) * I₂ t) := by
        rw [lintegral_add_left hm1]
    _ = ENNReal.ofReal p * ((ENNReal.ofReal (2 * A / (p - 1)) *
          ∫⁻ x, ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ p) +
          ENNReal.ofReal (4 / (2 - p)) * ∫⁻ x, ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ p) := by
        rw [hJ₁, hJ₂]
    _ = _ := by
        rw [← add_mul, ← mul_assoc,
          ← ENNReal.ofReal_add (div_nonneg (by positivity) hp1'.le)
            (div_nonneg (by norm_num) hp2'.le),
          ← ENNReal.ofReal_mul hp0.le, sqConst, hA_def]

/-- `G = sqFun Q N h` is constant on the leaves of `𝒟_N(Q)`: each cube `P_ε`, `P ∈ nonleaf N Q`,
contains or is disjoint from each leaf. [PROVED] -/
theorem constOn_sqFun_level (hd : d ≠ 0) (Q : DyadicCube d) (N : ℕ) (h : TestFun d) :
    ∀ L ∈ StoppingData.level N Q, ConstOn (sqFun Q N h : (Fin d → ℝ) → ℝ) L := by
  intro L hL
  have hLm := StoppingData.m_of_mem_level hL
  unfold sqFun
  refine StoppingData.constOn_sum fun P hP => StoppingData.constOn_sum fun ε _ =>
    StoppingData.constOn_smul _ (constOn_ind ?_)
  have hPm := ((StoppingData.mem_nonleaf_iff hd).mp hP).2
  apply DyadicCube.subset_or_disjoint
  change L.m ≤ P.m - 1
  omega

/-- **The atom estimate for `1 < p < 2`**, with constant `C_p = (C_p^p)^{1/p}`: for a mean-zero
`h` supported on `Q`, `‖h‖_{H¹} = ∫_Q S h ≤ |Q|^{1−1/p} ‖S h‖_p ≤ C_p |Q|^{1−1/p} ‖h‖_p`, by
Hölder's inequality on `Q` and the `L^p` bound for the square function; `S h` is itself a dyadic
test function (constant on the leaves) so that the `L^p` norms are those of test functions.
[PROVED] -/
theorem atomBound_of_lt_two (hd : d ≠ 0) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : AtomBound d p := by
  refine ⟨sqConst d p ^ (1 / p), Real.rpow_nonneg (sqConst_nonneg hp1 hp2) _,
    fun Q h hs h0 => ?_⟩
  obtain ⟨N, hres⟩ := Bridge.exists_resolution h Q
  have hp0 : 0 < p := by linarith
  have hV := Q.vol_pos
  -- `S h = √G` is a dyadic test function
  obtain ⟨S, hS_def⟩ : ∃ S : TestFun d,
      S = leafSum Q N (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)) := ⟨_, rfl⟩
  have hS : (S : (Fin d → ℝ) → ℝ) = fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) := by
    rw [hS_def]
    refine coe_leafSum Q N (fun L hL x hx y hy => ?_) (fun x hx => ?_)
    · exact congrArg Real.sqrt (constOn_sqFun_level hd Q N h L hL x hx y hy)
    · simp only [sqFun_eq_zero hd hx, Real.sqrt_zero]
  -- the Hardy norm is `∫_Q S h`
  have hint : hardyNorm (h : (Fin d → ℝ) → ℝ) = ∫ x, (S : (Fin d → ℝ) → ℝ) x := by
    unfold hardyNorm dyadicSquareFun
    rw [hS]
    exact integral_congr_ae (ae_of_all _ fun x =>
      congrArg Real.sqrt (tsum_sqTerm_eq hd hs h0 hres x))
  have hsupp : ∫ x, (S : (Fin d → ℝ) → ℝ) x = ∫ x in Q.toSet, (S : (Fin d → ℝ) → ℝ) x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hS]
      simp only [sqFun_eq_zero hd hx, Real.sqrt_zero]).symm
  -- Hölder's inequality on `Q`
  have hH := abs_setIntegral_le_rpow_mul_lpNorm hp1.le (TestFun.memLp S.2 (ENNReal.ofReal p))
    Q.measurableSet_toSet (by rw [Q.volume_toSet]; exact ENNReal.ofReal_ne_top)
  rw [Q.volume_toSet, ENNReal.toReal_ofReal hV.le] at hH
  -- the `L^p` bound `‖S h‖_p ≤ C_p ‖h‖_p`
  have hLp : lpNorm (S : (Fin d → ℝ) → ℝ) p ≤
      sqConst d p ^ (1 / p) * lpNorm (h : (Fin d → ℝ) → ℝ) p := by
    have hint1 : ∫ x, |(S : (Fin d → ℝ) → ℝ) x| ^ p ≤
        sqConst d p * lpNorm (h : (Fin d → ℝ) → ℝ) p ^ p := by
      have hhp : lpNorm (h : (Fin d → ℝ) → ℝ) p ^ p = ∫ x, |(h : (Fin d → ℝ) → ℝ) x| ^ p :=
        lpNorm_rpow_eq_integral hp0 (TestFun.memLp h.2 _)
      have hnn : 0 ≤ sqConst d p * ∫ x, |(h : (Fin d → ℝ) → ℝ) x| ^ p :=
        mul_nonneg (sqConst_nonneg hp1 hp2) (integral_nonneg fun x => by positivity)
      rw [hhp, ← ENNReal.ofReal_le_ofReal_iff hnn,
        ofReal_integral_eq_lintegral_ofReal (TestFun.integrable_abs_rpow S hp0)
          (ae_of_all _ fun x => by positivity),
        ENNReal.ofReal_mul (sqConst_nonneg hp1 hp2),
        ofReal_integral_eq_lintegral_ofReal (TestFun.integrable_abs_rpow h hp0)
          (ae_of_all _ fun x => by positivity)]
      have e1 : ∀ x, ENNReal.ofReal (|(S : (Fin d → ℝ) → ℝ) x| ^ p) =
          ENNReal.ofReal (Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) ^ p) := by
        intro x
        rw [hS]
        simp only [abs_of_nonneg (Real.sqrt_nonneg _)]
      have e2 : ∀ x, ENNReal.ofReal (|(h : (Fin d → ℝ) → ℝ) x| ^ p) =
          ‖(h : (Fin d → ℝ) → ℝ) x‖ₑ ^ p := by
        intro x
        rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
      simp only [e1, e2]
      exact lintegral_sqrt_sqFun_rpow_le hd hs hres hp1 hp2
    have := TestFun.lpNorm_le_rpow_of_integral_le S hp0 hint1
    rwa [Real.mul_rpow (sqConst_nonneg hp1 hp2) (Real.rpow_nonneg (lpNorm_nonneg _ _) _), one_div,
      Real.rpow_rpow_inv (lpNorm_nonneg _ _) hp0.ne', ← one_div] at this
  calc hardyNorm (h : (Fin d → ℝ) → ℝ)
      = ∫ x in Q.toSet, (S : (Fin d → ℝ) → ℝ) x := by rw [hint, hsupp]
    _ ≤ |∫ x in Q.toSet, (S : (Fin d → ℝ) → ℝ) x| := le_abs_self _
    _ ≤ Q.vol ^ (1 - 1 / p) * lpNorm (S : (Fin d → ℝ) → ℝ) p := hH
    _ ≤ Q.vol ^ (1 - 1 / p) * (sqConst d p ^ (1 / p) * lpNorm (h : (Fin d → ℝ) → ℝ) p) :=
        mul_le_mul_of_nonneg_left hLp (Real.rpow_nonneg hV.le _)
    _ = sqConst d p ^ (1 / p) * Q.vol ^ (1 - 1 / p) * lpNorm (h : (Fin d → ℝ) → ℝ) p := by ring

/-- **The atom estimate for every `p > 1`.** [PROVED] -/
theorem atomBound (hd : d ≠ 0) {p : ℝ} (hp : 1 < p) : AtomBound d p := by
  by_cases h2 : 2 ≤ p
  · exact atomBound_of_two_le hd h2
  · exact atomBound_of_lt_two hd hp (not_le.mp h2)

/-- **The square function of an atom is integrable**: for a mean-zero `h` supported on `Q`, the
square function `S h` is the dyadic test function `√G` (`tsum_sqTerm_eq`), so `‖h‖_{H¹} < ∞` and
the BMO condition (1.15) applies to `h`. [PROVED] -/
theorem integrable_dyadicSquareFun (hd : d ≠ 0) {Q : DyadicCube d} {h : TestFun d}
    (hs : SupportedOn (h : (Fin d → ℝ) → ℝ) Q) (h0 : MeanZero (h : (Fin d → ℝ) → ℝ)) :
    Integrable (dyadicSquareFun (h : (Fin d → ℝ) → ℝ)) := by
  obtain ⟨N, hres⟩ := Bridge.exists_resolution h Q
  have hS : (leafSum Q N (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x)) :
      (Fin d → ℝ) → ℝ) = fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x) := by
    refine coe_leafSum Q N (fun L hL x hx y hy => ?_) (fun x hx => ?_)
    · exact congrArg Real.sqrt (constOn_sqFun_level hd Q N h L hL x hx y hy)
    · simp only [sqFun_eq_zero hd hx, Real.sqrt_zero]
  refine (TestFun.integrable
    (leafSum Q N (fun x => Real.sqrt ((sqFun Q N h : (Fin d → ℝ) → ℝ) x))).2).congr
    (ae_of_all _ fun x => ?_)
  rw [hS, dyadicSquareFun, tsum_sqTerm_eq hd hs h0 hres x]

/-- **Theorem 1.11 from Theorem 1.3**, for every Hölder tuple and `n ≥ 2`: the atom estimate holds
for all exponents, so Theorem 1.11 (in the scale-invariant form `GlobalTb`) follows from
Theorem 1.3 without further hypotheses. [PROVED] -/
theorem globalTb (hn : 2 ≤ n) (p : HolderTuple n) (h13 : LocalT1 d n p) : GlobalTb d n p := by
  intro hd hn' B hB
  exact globalTb_of_localT1 hn p h13 (fun j => atomBound (by omega) (p.one_lt j))
    (fun _ _ hs h0 => integrable_dyadicSquareFun (by omega) hs h0) hd hn' B hB

end SquareFunctionLp

/-! ## Towards Theorem 1.3: the perfect multilinear local T(1) theorem

The paper gives no proof of Theorem 1.3 (`LocalT1`) and cites it as folklore. The plan of the
proof formalized here (in progress) is the dyadic paraproduct argument:

1. **Finite martingale expansion of the form.** For `f_j` supported on a common cube `R` of scale
   `M`, `Λ(f) = Λ(E_s f)` by the resolution `s` of the form (`KernelScale`), and
   `E_s f_j = [f_j]_R 𝟙_R + ∑_{Q ∈ 𝒟_{M−s}(R)} Δ_Q f_j` with the martingale differences
   `Δ_Q f = ∑_ε [f]_{Q_ε} 𝟙_{Q_ε} − [f]_Q 𝟙_Q` (`mdiff`, `coarsen_eq_sum_mdiff`). Expanding
   scale by scale, `Λ(E_m f) − Λ(E_{m+1} f) = ∑_{Q: ℓ(Q) = 2^{m+1}} ∑_{∅ ≠ S ⊆ [n]}
   ∏_{j ∉ S} [f_j]_Q · Λ(Δ_Q f_j (j ∈ S), 𝟙_Q (j ∉ S))`: the products of differences at distinct
   cubes of the same scale vanish and the entries `E_{m+1} f_j` outside `S` may be replaced by
   `[f_j]_Q 𝟙_Q`, both by perfect smoothness (`form_update_truncate_eq`).
2. **The building blocks.** For a tuple supported on `Q` and constant on the children of `Q`,
   `|Λ(f)| ≤ B 2^{dn} ∏ ‖f_j‖_{p_j}` (`abs_form_le_of_constOn_children`): expand into the
   children, use the dyadic decay (1.1) off the diagonal and the weak boundedness `|Λ(𝟙_P, …, 𝟙_P)|
   ≤ B |P|` (a case of `T1Testing`) on the diagonal.
3. **Two or more differences** (`|S| ≥ 2`): the sum over `Q` of
   `|Q| ∏_{j∈S} |Δ_Q f_j| ∏_{j∉S} |[f_j]_Q|` is bounded by `∏ ‖f_j‖_{p_j}` through the outer
   measure Hölder inequalities and the Carleson embedding (`carlesonEmbedding`,
   `outerLpNorm_mul_le`, `tsum_enorm_mul_vol_le`), as in Lemma 2.72.
4. **The paraproducts** (`|S| = 1`): `∑_Q ∏_{i≠j} [f_i]_Q Λ(𝟙_Q, …, Δ_Q f_j, …, 𝟙_Q)`; the
   coefficients `Λ(𝟙_Q, …, h_Q^ε, …, 𝟙_Q)` are intrinsic by perfect smoothness and satisfy a
   Carleson condition by the testing condition in the slot `j`; for `p_j > 2` this is the dyadic
   John–Nirenberg inequality for the symbol of the paraproduct.
5. **The cubes at infinity.** `Λ(f) = ∑_{κ} Λ(f_1 𝟙_{R_{κ_1}}, …, f_n 𝟙_{R_{κ_n}})` over the `2^d`
   dyadic cubes `R_κ` of scale `M` at the origin; the off-diagonal terms are
   `∏ [f_j]_{R_{κ_j}} Λ(𝟙_{R_{κ_1}}, …)` (all other terms vanish by perfect smoothness) and
   are `O(2^{-Md(n-1)})`, so `M → ∞` removes them.

Steps 1 (the finite martingale expansion `coarsen_eq_sum_mdiff` and the scale-by-scale
expansion `form_coarsen_succ_sub`, via the localization lemma `form_eq_of_vanishesOn`), 2
(`abs_form_le_of_constOn_children`) and 3 (`sum_block_le`, via `abs_form_blockTuple_le`, the
multi-factor Hölder inequality `outerLpNorm_prod_sizeInf_le` in `L^·(S_∞)` and the comparison
`superlevel_sizeInf_le_sizeP` of the `S_∞`- and `S_p`-superlevel measures) are done below.
Step 4 is done for all exponents (`sum_para_le`): the coefficients `coefChild`, their
fluctuations `coefV`, the Carleson sequence `carl T j Q = |Q|⁻¹ √(2^d ∑_ε (coefV)²)`, the
intrinsic property `form_oneTuple_eq_of_subset`, the testing bound `abs_form_oneTuple_le`, the
symbol `paraSymbol = ∑_Q ψ_Q` with `ψ_Q = |Q|⁻¹ ∑_ε coefV_Q^ε 𝟙_{Q_ε}`, which represents the
paraproduct (`form_oneTuple_eq_integral_paraSymbol : Λ(𝟙_Q, …, φ, …, 𝟙_Q) = 2^d ∫ ψ φ`), and the
Carleson condition `sum_carl_sq_le' : ∑_{Q ∈ nonleaf N P} carl² |Q| ≤ C_d B² |P|` with the
constant `C_d = 128 + (8 + 2^d)²` for all exponents (for `p_j ≤ 2` it would follow directly from
the orthogonality of the `ψ_Q` and Hölder's inequality `‖ψ‖_{p_j} ≤ ‖ψ‖₂ |P|^{1/p_j − 1/2}`; the
general case is the John–Nirenberg argument): the testing hypothesis gives the
dual `L^1`-BMO condition `|∫ ψ φ| ≤ 2^{-d} B ‖φ‖_∞ |Q|` for mean-zero `φ` on `Q ⊆ P`
(`paraSymbol_jnDual`), and the **dyadic John–Nirenberg inequality** `dyadic_john_nirenberg`
(stopping-time bootstrap `jn_step` on the maximal cubes with `|[ψ]_Q − [ψ]_P| > 8K`, which cover
at most a quarter of `P`) turns it into the `L²` bound `∫_P |ψ − [ψ]_P|² ≤ C_d K² |P|`, that is,
the Carleson condition. Hence `‖carl‖_{L^∞(S₂)} ≤ √C_d B` (`outerLinfNorm_carl_le`), and per cube
`|Λ(𝟙_Q, …, Δ_Q f_j, …, 𝟙_Q)| ≤ |Q| Δ_Q f_j · carl T j Q` by Cauchy–Schwarz
(`abs_form_blockTuple_single_le`). Step 5 is done as well: `form_coarsen_eq` (`Λ(f) = Λ(E_N f)`
in all slots), the telescoping `form_coarsen_eq_sum`, the local bound
`abs_form_le_of_supported` for tuples supported in a common cube (with the constant
`B 2^{dn} + ∑_{S ≠ ∅} C_S`, uniform in the form), the cubes `quad M κ` at the origin with
`sum_truncateₗ_quad`, the bounded support `TestFun.exists_abs_lt_pow`, the off-diagonal
factorization `form_eq_prod_avg_mul` (from one slot of perfect smoothness,
`form_eq_avg_mul_of_vanishes`), the term bound `abs_form_quad_le` and the limit `M → ∞` in
`localT1_core`. **Theorem 1.3 is `localT1`**, and Theorems 1.4 and 1.11 follow unconditionally
(`localTb_unconditional`, `globalTb_unconditional`). -/

section T1Theorem

open Bridge

variable {n : ℕ}

theorem level_one (Q : DyadicCube d) : StoppingData.level 1 Q = StoppingData.children Q := by
  rw [StoppingData.level_succ, StoppingData.level_zero, Finset.singleton_biUnion]

theorem coarsen_zero (Q : DyadicCube d) (f : TestFun d) :
    coarsen Q 0 f = avg Q (f : (Fin d → ℝ) → ℝ) • TestFun.ind Q := by
  rw [coarsen, StoppingData.level_zero, Finset.sum_singleton]

/-- The martingale difference `Δ_Q f = E_1 f − E_0 f = ∑_ε [f]_{Q_ε} 𝟙_{Q_ε} − [f]_Q 𝟙_Q` at `Q`. -/
noncomputable def mdiff (Q : DyadicCube d) (f : TestFun d) : TestFun d :=
  coarsen Q 1 f - coarsen Q 0 f

theorem mdiff_eq (Q : DyadicCube d) (f : TestFun d) :
    mdiff Q f = ∑ ε : Fin d → Bool, avg (Q.child ε) (f : (Fin d → ℝ) → ℝ) • TestFun.ind (Q.child ε)
      -
      avg Q (f : (Fin d → ℝ) → ℝ) • TestFun.ind Q := by
  rw [mdiff, coarsen_zero, coarsen, level_one, StoppingData.children,
    Finset.sum_image fun ε _ ε' _ h => Q.child_injective h]

theorem mdiff_supportedOn (Q : DyadicCube d) (f : TestFun d) :
    SupportedOn (mdiff Q f : (Fin d → ℝ) → ℝ) Q := by
  intro x hx
  rw [mdiff, Submodule.coe_sub, Pi.sub_apply, coarsen_supportedOn Q 1 f x hx,
    coarsen_supportedOn Q 0 f x hx, sub_zero]

/-- `∫ Δ_Q f = 0`. [PROVED] -/
theorem mdiff_meanZero (Q : DyadicCube d) (f : TestFun d) :
    MeanZero (mdiff Q f : (Fin d → ℝ) → ℝ) := by
  change ∫ x, (mdiff Q f : (Fin d → ℝ) → ℝ) x = 0
  rw [mdiff, Submodule.coe_sub]
  simp only [Pi.sub_apply]
  rw [integral_sub (TestFun.integrable (coarsen Q 1 f).2) (TestFun.integrable (coarsen Q 0 f).2),
    coarsen_integral', coarsen_integral', sub_self]

/-- `Δ_Q f` is constant on the children of `Q`. [PROVED] -/
theorem mdiff_constOn_child (Q : DyadicCube d) (f : TestFun d) (ε : Fin d → Bool) :
    ConstOn (mdiff Q f : (Fin d → ℝ) → ℝ) (Q.child ε) := by
  rw [mdiff]
  refine StoppingData.constOn_sub (coarsen_constOn Q 1 f ?_) (coarsen_constOn Q 0 f ?_)
  · change Q.m - 1 ≤ Q.m - ((1 : ℕ) : ℤ)
    omega
  · change Q.m - 1 ≤ Q.m - ((0 : ℕ) : ℤ)
    omega

/-- `E_{N+1} f = E_N f + ∑_{Q ∈ level N P} Δ_Q f`. [PROVED] -/
theorem coarsen_succ (P : DyadicCube d) (N : ℕ) (f : TestFun d) :
    coarsen P (N + 1) f = coarsen P N f + ∑ Q ∈ StoppingData.level N P, mdiff Q f := by
  have h1 : coarsen P (N + 1) f = ∑ Q ∈ StoppingData.level N P, coarsen Q 1 f := by
    rw [coarsen, StoppingData.sum_level_succ]
    exact Finset.sum_congr rfl fun Q _ => by rw [coarsen, level_one]
  have h2 : coarsen P N f = ∑ Q ∈ StoppingData.level N P, coarsen Q 0 f := by
    rw [coarsen]
    exact Finset.sum_congr rfl fun Q _ => by rw [coarsen_zero]
  rw [h1, h2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun Q _ => by rw [mdiff, add_sub_cancel]

/-- **The finite martingale expansion** `E_N f = [f]_P 𝟙_P + ∑_{Q ∈ nonleaf N P} Δ_Q f`. [PROVED] -/
theorem coarsen_eq_sum_mdiff (P : DyadicCube d) (N : ℕ) (f : TestFun d) :
    coarsen P N f = avg P (f : (Fin d → ℝ) → ℝ) • TestFun.ind P +
      ∑ Q ∈ StoppingData.nonleaf N P, mdiff Q f := by
  induction N with
  | zero => rw [coarsen_zero, StoppingData.nonleaf_zero, Finset.sum_empty, add_zero]
  | succ N ih => rw [coarsen_succ, ih, StoppingData.sum_nonleaf_succ, add_assoc]

/-- `E_N f = f` for `f` supported on `P` and constant on the leaves of `𝒟_N(P)`. [PROVED] -/
theorem coarsen_eq_self {P : DyadicCube d} {N : ℕ} {f : TestFun d}
    (hf : SupportedOn (f : (Fin d → ℝ) → ℝ) P)
    (hconst : ∀ L ∈ StoppingData.level N P, ConstOn (f : (Fin d → ℝ) → ℝ) L) :
    coarsen P N f = f := by
  apply Subtype.ext
  have e : coarsen P N f = leafSum P N f := by
    unfold coarsen leafSum
    exact Finset.sum_congr rfl fun L hL => by rw [avg_eq_of_constOn (hconst L hL) L.corner_mem]
  rw [e]
  exact coe_leafSum P N hconst hf

/-- A function supported on `Q` and constant on its children is `∑_ε [f]_{Q_ε} 𝟙_{Q_ε}`. [PROVED] -/
theorem eq_sum_children_of_constOn {Q : DyadicCube d} {f : TestFun d}
    (hf : SupportedOn (f : (Fin d → ℝ) → ℝ) Q)
    (hconst : ∀ ε, ConstOn (f : (Fin d → ℝ) → ℝ) (Q.child ε)) :
    f = ∑ ε : Fin d → Bool, avg (Q.child ε) (f : (Fin d → ℝ) → ℝ) • TestFun.ind (Q.child ε) := by
  have h := coarsen_eq_self (N := 1) hf fun L hL => by
    rw [level_one] at hL
    obtain ⟨ε, rfl⟩ := StoppingData.mem_children.mp hL
    exact hconst ε
  conv_lhs => rw [← h]
  rw [coarsen, level_one, StoppingData.children,
    Finset.sum_image fun ε _ ε' _ h => Q.child_injective h]

/-- `∑_j 1/p_j = 1` for a Hölder tuple, and `n ≥ 1`. [PROVED] -/
theorem HolderTuple.sum_one_div (p : HolderTuple n) : ∑ j, 1 / p.p j = 1 := by
  simp only [one_div]
  exact p.sum_inv

theorem HolderTuple.pos (p : HolderTuple n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exfalso
    have := p.sum_inv
    subst h
    simp at this
  · exact h

/-- **The building-block bound**: for a tuple of functions supported on `Q` and constant on the
children of `Q`, `|Λ(f)| ≤ B 2^{dn} ∏_j ‖f_j‖_{p_j}`. Expanding each entry into the children,
`Λ(f) = ∑_{ε} ∏_j [f_j]_{Q_{ε_j}} Λ(𝟙_{Q_{ε_1}}, …, 𝟙_{Q_{ε_n}})`; off the diagonal the dyadic
decay
(1.1) gives `|Λ(𝟙_{Q_{ε}})| ≤ |Q_ε|`, on the diagonal the weak boundedness `≤ B |Q_ε|` (a case of
the testing condition); and `|[f_j]_{Q_ε}| ≤ |Q_ε|^{-1/p_j} ‖f_j‖_{p_j}` by Hölder. [PROVED] -/
theorem abs_form_le_of_constOn_children {T : PerfectCZForm d n} {p : HolderTuple n} {B : ℝ}
    (hT : T1Testing T p B) (hB : 1 ≤ B) (Q : DyadicCube d) (f : Fin n → TestFun d)
    (hsupp : ∀ j, SupportedOn (f j : (Fin d → ℝ) → ℝ) Q)
    (hconst : ∀ j ε, ConstOn (f j : (Fin d → ℝ) → ℝ) (Q.child ε)) :
    |T.form f| ≤ B * 2 ^ (d * n) * prodNorm p f := by
  have hn0 : 0 < n := p.pos
  have hB0 : (0 : ℝ) ≤ B := by linarith
  -- the common volume of the children
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = Q.vol / 2 ^ d := ⟨_, rfl⟩
  have hVpos : 0 < V := by rw [hV]; exact div_pos Q.vol_pos (by positivity)
  have hVε : ∀ ε : Fin d → Bool, (Q.child ε).vol = V := fun ε => by
    rw [hV, eq_div_iff (by positivity)]
    exact Q.vol_child ε
  -- the expansion into the children
  have hf : f = fun j => ∑ ε : Fin d → Bool,
      avg (Q.child ε) (f j : (Fin d → ℝ) → ℝ) • TestFun.ind (Q.child ε) :=
    funext fun j => eq_sum_children_of_constOn (hsupp j) (hconst j)
  have hexp : T.form f = ∑ r : Fin n → (Fin d → Bool),
      (∏ j, avg (Q.child (r j)) (f j : (Fin d → ℝ) → ℝ)) *
        T.form (fun j => TestFun.ind (Q.child (r j))) := by
    conv_lhs => rw [hf]
    rw [MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  -- the volume of the indicator tuple
  have hprodV : ∀ r : Fin n → (Fin d → Bool),
      prodNorm p (fun j => TestFun.ind (Q.child (r j))) = V := by
    intro r
    unfold prodNorm
    have : ∀ j, lpNorm ((TestFun.ind (Q.child (r j)) : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j) =
        V ^ (1 / p.p j) := fun j => by
      rw [TestFun.lpNorm_ind _ (by linarith [p.one_lt j]), hVε]
    rw [Finset.prod_congr rfl fun j _ => this j, ← Real.rpow_sum_of_pos hVpos, p.sum_one_div,
      Real.rpow_one]
  -- the building blocks: `|Λ(𝟙_{Q_{ε}})| ≤ B |Q_ε|`
  have hblock : ∀ r : Fin n → (Fin d → Bool),
      |T.form (fun j => TestFun.ind (Q.child (r j)))| ≤ B * V := by
    intro r
    have hsub : ∀ j, SupportedOn ((TestFun.ind (Q.child (r j)) : TestFun d) : (Fin d → ℝ) → ℝ) Q :=
      fun j x hx => Set.indicator_of_notMem (fun h => hx (Q.child_subset _ h)) _
    by_cases hr : ∀ j, r j = r ⟨0, hn0⟩
    · have h := hT (Q.child (r ⟨0, hn0⟩)) ⟨0, hn0⟩ (fun j => TestFun.ind (Q.child (r j)))
        (fun j _ => by rw [hr j]; rfl) (TestFun.ind_supportedOn _)
      rwa [hprodV] at h
    · obtain ⟨j, hj⟩ := not_forall.mp hr
      have h := T.decay p Q (fun j => TestFun.ind (Q.child (r j))) hsub
        ⟨j, ⟨0, hn0⟩, fun h => hj (by rw [h]), r j, r ⟨0, hn0⟩, hj,
          TestFun.ind_supportedOn _, TestFun.ind_supportedOn _⟩
      rw [hprodV] at h
      exact h.trans (le_mul_of_one_le_left hVpos.le hB)
  -- Hölder: `|[f_j]_{Q_ε}| ≤ V^{-1/p_j} ‖f_j‖_{p_j}`
  have hc : ∀ (j : Fin n) (ε : Fin d → Bool), |avg (Q.child ε) (f j : (Fin d → ℝ) → ℝ)| ≤
      V ^ (-(1 / p.p j)) * lpNorm (f j : (Fin d → ℝ) → ℝ) (p.p j) := by
    intro j ε
    have h1 := abs_integral_indicator_le (p.one_lt j).le (TestFun.memLp (f j).2 _) (Q.child ε)
    rw [integral_indicator (Q.child ε).measurableSet_toSet, hVε] at h1
    rw [avg, hVε, abs_div, abs_of_pos hVpos, div_le_iff₀ hVpos]
    refine h1.trans (le_of_eq ?_)
    rw [mul_right_comm, ← Real.rpow_add_one hVpos.ne']
    congr 2
    ring
  have hsum : ∀ j : Fin n, ∑ ε : Fin d → Bool, |avg (Q.child ε) (f j : (Fin d → ℝ) → ℝ)| ≤
      2 ^ d * (V ^ (-(1 / p.p j)) * lpNorm (f j : (Fin d → ℝ) → ℝ) (p.p j)) := by
    intro j
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun ε : Fin d → Bool => |avg (Q.child ε) (f j : (Fin d → ℝ) → ℝ)|) _ (fun ε _ => hc j ε)
    rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat] at this
  have hVne : V ≠ 0 := hVpos.ne'
  have hsumneg : ∑ j, -(1 / p.p j) = (-1 : ℝ) := by
    rw [Finset.sum_neg_distrib, p.sum_one_div]
  calc |T.form f|
      = |∑ r : Fin n → (Fin d → Bool), (∏ j, avg (Q.child (r j)) (f j : (Fin d → ℝ) → ℝ)) *
          T.form (fun j => TestFun.ind (Q.child (r j)))| := by rw [hexp]
    _ ≤ ∑ r : Fin n → (Fin d → Bool), |(∏ j, avg (Q.child (r j)) (f j : (Fin d → ℝ) → ℝ)) *
          T.form (fun j => TestFun.ind (Q.child (r j)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin n → (Fin d → Bool),
          (∏ j, |avg (Q.child (r j)) (f j : (Fin d → ℝ) → ℝ)|) * (B * V) :=
        Finset.sum_le_sum fun r _ => by
          rw [abs_mul, Finset.abs_prod]
          exact mul_le_mul_of_nonneg_left (hblock r) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    _ = (B * V) * ∏ j, ∑ ε : Fin d → Bool, |avg (Q.child ε) (f j : (Fin d → ℝ) → ℝ)| := by
        rw [← Finset.sum_mul, mul_comm,
          Fintype.prod_sum fun (j : Fin n) (ε : Fin d → Bool) =>
            |avg (Q.child ε) (f j : (Fin d → ℝ) → ℝ)|]
    _ ≤ (B * V) * ∏ j, (2 ^ d * (V ^ (-(1 / p.p j)) * lpNorm (f j : (Fin d → ℝ) → ℝ) (p.p j))) :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            fun j _ => hsum j) (by positivity)
    _ = B * 2 ^ (d * n) * prodNorm p f := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← Real.rpow_sum_of_pos hVpos, hsumneg, Real.rpow_neg_one, prodNorm,
          ← pow_mul]
        field_simp

/-! #### The scale-by-scale expansion of the form

`Λ(E_{N+1} f) − Λ(E_N f) = ∑_{Q ∈ level N R} ∑_{∅ ≠ S ⊆ [n]} ∏_{j ∉ S} [f_j]_Q · Λ(Δ_Q f_j (j ∈ S),
𝟙_Q (j ∉ S))`.
The multilinear expansion of `Λ(E_N f + ∑_Q Δ_Q f)` over the subsets `S` of slots carrying a
difference, then in one slot `j₀ ∈ S` the sum over `Q`; for fixed `Q` the slot `j₀` carries
`Δ_Q f_{j₀}`, supported on `Q` with mean zero, so by perfect smoothness every other entry may be
changed by a function vanishing on `Q` (`form_eq_of_vanishesOn`): in the slots of `S` the
differences at the other cubes of the level are dropped, and outside `S` the coarsening `E_N f_j`,
which equals `[f_j]_Q` on `Q`, is replaced by `[f_j]_Q 𝟙_Q`. -/

/-- **Localization by perfect smoothness**: if the slot `j₀` carries a mean-zero function
supported on `Q`, the form does not change when every other entry is modified by a function
vanishing on `Q`. [PROVED] -/
theorem form_eq_of_vanishesOn (T : PerfectCZForm d n) {m m' : Fin n → TestFun d} {j₀ : Fin n}
    {Q : DyadicCube d} (h0 : SupportedOn (m j₀ : (Fin d → ℝ) → ℝ) Q)
    (hmean : MeanZero (m j₀ : (Fin d → ℝ) → ℝ)) (hj₀ : m' j₀ = m j₀)
    (h : ∀ j, j ≠ j₀ → VanishesOn ((m j - m' j : TestFun d) : (Fin d → ℝ) → ℝ) Q) :
    T.form m = T.form m' := by
  have key : ∀ s : Finset (Fin n), j₀ ∉ s → T.form (s.piecewise m' m) = T.form m := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.piecewise_empty]
    | @insert j s hj ih =>
      intro hj₀s
      have hj₀ : j₀ ∉ s := fun h => hj₀s (Finset.mem_insert_of_mem h)
      have hjne : j ≠ j₀ := fun h => hj₀s (h ▸ Finset.mem_insert_self j s)
      rw [Finset.piecewise_insert, ← ih hj₀]
      have hsub := MultilinearMap.map_update_sub T.form (s.piecewise m' m) j
        ((s.piecewise m' m) j) (m' j)
      rw [Function.update_eq_self] at hsub
      have hzero : T.form (Function.update (s.piecewise m' m) j ((s.piecewise m' m) j - m' j)) = 0
        := by
        refine T.smooth Q _ j₀ j hjne.symm ?_ ?_ ?_
        · rw [Function.update_of_ne hjne.symm, Finset.piecewise_eq_of_notMem _ _ _ hj₀]
          exact h0
        · rw [Function.update_of_ne hjne.symm, Finset.piecewise_eq_of_notMem _ _ _ hj₀]
          exact hmean
        · rw [Function.update_self, Finset.piecewise_eq_of_notMem _ _ _ hj]
          exact h j hjne
      linarith [hsub, hzero]
  have hfull : (Finset.univ.erase j₀).piecewise m' m = m' := by
    funext j
    by_cases hj : j = j₀
    · subst hj
      rw [Finset.piecewise_eq_of_notMem _ _ _ (Finset.notMem_erase j _), hj₀]
    · rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)]
  rw [← hfull, key _ (Finset.notMem_erase j₀ _)]

/-- The value of `E_N f` on a cube `Q` of `level N R` is the average `[f]_Q`. [PROVED] -/
theorem coarsen_apply_of_mem {R Q : DyadicCube d} {N : ℕ} (hQ : Q ∈ StoppingData.level N R)
    (f : TestFun d) {x : Fin d → ℝ} (hx : x ∈ Q.toSet) :
    (coarsen R N f : (Fin d → ℝ) → ℝ) x = avg Q (f : (Fin d → ℝ) → ℝ) := by
  rw [coarsen_apply, Finset.sum_eq_single Q]
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
  · intro L hL hne
    rcases StoppingData.level_eq_or_disjoint hL hQ with h | h
    · exact absurd h hne
    · rw [Set.indicator_of_notMem (Set.disjoint_right.mp h hx), mul_zero]
  · intro h
    exact absurd hQ h

/-- `∏_j (if j ∈ S then 1 else c j) = ∏_{j ∉ S} c j`. [PROVED] -/
theorem prod_ite_one_mem (S : Finset (Fin n)) (c : Fin n → ℝ) :
    ∏ j, (if j ∈ S then (1 : ℝ) else c j) = ∏ j ∈ Sᶜ, c j := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
  congr 1
  ext j
  simp

/-- The tuple with `Δ_Q f_j` in the slots of `S` and `𝟙_Q` elsewhere. -/
noncomputable def blockTuple (Q : DyadicCube d) (f : Fin n → TestFun d) (S : Finset (Fin n)) :
    Fin n → TestFun d :=
  fun j => if j ∈ S then mdiff Q (f j) else TestFun.ind Q

/-- **The term of the expansion at `Q` and `S`**: with `Δ_Q f_{j₀}` in the slot `j₀ ∈ S`, the
sums of differences in the other slots of `S` and the coarsenings outside `S`, the form equals
`∏_{j ∉ S} [f_j]_Q · Λ(Δ_Q f_j (j ∈ S), 𝟙_Q (j ∉ S))`. [PROVED] -/
theorem form_update_mdiff_eq (T : PerfectCZForm d n) (R Q : DyadicCube d) (N : ℕ)
    (hQ : Q ∈ StoppingData.level N R) (f : Fin n → TestFun d) (S : Finset (Fin n)) {j₀ : Fin n}
    (hj₀ : j₀ ∈ S) :
    T.form (Function.update (S.piecewise (fun j => ∑ Q' ∈ StoppingData.level N R, mdiff Q' (f j))
        (fun j => coarsen R N (f j))) j₀ (mdiff Q (f j₀))) =
      (∏ j ∈ Sᶜ, avg Q (f j : (Fin d → ℝ) → ℝ)) * T.form (blockTuple Q f S) := by
  set b : Fin n → TestFun d := fun j => ∑ Q' ∈ StoppingData.level N R, mdiff Q' (f j) with hb
  set a : Fin n → TestFun d := fun j => coarsen R N (f j) with ha
  set m' : Fin n → TestFun d :=
    fun j => if j ∈ S then mdiff Q (f j) else avg Q (f j : (Fin d → ℝ) → ℝ) • TestFun.ind Q with hm'
  have h1 : T.form (Function.update (S.piecewise b a) j₀ (mdiff Q (f j₀))) = T.form m' := by
    refine form_eq_of_vanishesOn T (j₀ := j₀) (Q := Q) ?_ ?_ ?_ ?_
    · rw [Function.update_self]
      exact mdiff_supportedOn Q (f j₀)
    · rw [Function.update_self]
      exact mdiff_meanZero Q (f j₀)
    · rw [Function.update_self]
      simp only [hm', hj₀, ↓reduceIte]
    · intro j hj x hx
      rw [Function.update_of_ne hj]
      by_cases hjS : j ∈ S
      · rw [Finset.piecewise_eq_of_mem _ _ _ hjS]
        simp only [hm', hjS, ↓reduceIte, hb]
        rw [← Finset.sum_erase_eq_sub hQ, Submodule.coe_sum, Finset.sum_apply]
        refine Finset.sum_eq_zero fun Q' hQ' => ?_
        rw [Finset.mem_erase] at hQ'
        rcases StoppingData.level_eq_or_disjoint hQ'.2 hQ with h | h
        · exact absurd h hQ'.1
        · exact mdiff_supportedOn Q' (f j) x (Set.disjoint_right.mp h hx)
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hjS]
        simp only [hm', hjS, ↓reduceIte, ha]
        rw [Submodule.coe_sub, Pi.sub_apply, coarsen_apply_of_mem hQ (f j) hx, Submodule.coe_smul,
          Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_mem hx, Pi.one_apply, smul_eq_mul,
          mul_one, sub_self]
  have h2 : m' = fun j => (if j ∈ S then (1 : ℝ) else avg Q (f j : (Fin d → ℝ) → ℝ)) •
      blockTuple Q f S j := by
    funext j
    by_cases hjS : j ∈ S <;> simp [hm', blockTuple, hjS]
  rw [h1, h2, MultilinearMap.map_smul_univ, smul_eq_mul, prod_ite_one_mem]

/-- **The scale-by-scale expansion**:
`Λ(E_{N+1} f) − Λ(E_N f) = ∑_{Q ∈ level N R} ∑_{∅ ≠ S} ∏_{j ∉ S} [f_j]_Q · Λ(Δ_Q f_j (j ∈ S), 𝟙_Q (j
∉ S))`.
[PROVED] -/
theorem form_coarsen_succ_sub (T : PerfectCZForm d n) (R : DyadicCube d) (N : ℕ)
    (f : Fin n → TestFun d) :
    T.form (fun j => coarsen R (N + 1) (f j)) - T.form (fun j => coarsen R N (f j)) =
      ∑ Q ∈ StoppingData.level N R, ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
        (∏ j ∈ Sᶜ, avg Q (f j : (Fin d → ℝ) → ℝ)) * T.form (blockTuple Q f S) := by
  set b : Fin n → TestFun d := fun j => ∑ Q' ∈ StoppingData.level N R, mdiff Q' (f j) with hb
  set a : Fin n → TestFun d := fun j => coarsen R N (f j) with ha
  have hsplit : (fun j => coarsen R (N + 1) (f j)) = b + a := by
    funext j
    rw [Pi.add_apply, ha, hb]
    exact (coarsen_succ R N (f j)).trans (add_comm _ _)
  rw [hsplit, MultilinearMap.map_add_univ, ← Finset.add_sum_erase _ _ (Finset.mem_univ ∅),
    Finset.piecewise_empty, add_sub_cancel_left, Finset.sum_comm]
  refine Finset.sum_congr rfl fun S hS => ?_
  obtain ⟨j₀, hj₀⟩ : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hS)
  have e : Function.update (S.piecewise b a) j₀ (∑ Q ∈ StoppingData.level N R, mdiff Q (f j₀)) =
      S.piecewise b a := by
    rw [show (∑ Q ∈ StoppingData.level N R, mdiff Q (f j₀)) = S.piecewise b a j₀ from
      (Finset.piecewise_eq_of_mem S b a hj₀).symm, Function.update_eq_self]
  rw [← e, MultilinearMap.map_update_sum]
  exact Finset.sum_congr rfl fun Q hQ => form_update_mdiff_eq T R Q N hQ f S hj₀

/-! #### The terms with two or more differences

For `|S| ≥ 2` the sum over the cubes of the tree of
`∏_{j ∉ S} |[f_j]_Q| · |Λ(Δ_Q f_j (j ∈ S), 𝟙_Q (j ∉ S))|` is bounded by `C ∏_j ‖f_j‖_{p_j}`:
the building-block bound gives `|Λ(…)| ≤ B 4^{dn} |Q| ∏_{j ∈ S} Δ_Q f_j` with the martingale
differences `Δ_Q f = (|Q|⁻¹ ∑_ε |[f]_{Q_ε} − [f]_Q|² |Q_ε|)^{1/2}` of §2.9, the sum is then
`∑_Q |Q| F(Q)` with `F = Δ f_{i₁} Δ f_{i₂} ∏_{j ∈ S ∖ {i₁,i₂}} Δ f_j ∏_{j ∉ S} E f_j`, bounded by
Proposition 3.6 of Do–Thiele through `‖F‖_{L¹(S₁)}`, and the outer Hölder inequalities with the
Carleson embedding give `‖F‖_{L¹(S₁)} ≤ C ∏ ‖f_j‖_{p_j}`: `S₁(Δ f_{i₁} Δ f_{i₂} · H) ≤
S₂(Δ f_{i₁}) S₂(Δ f_{i₂}) S_∞(H)`, the remaining factors `Δ f_j`, `E f_j` of `H` are in
`L^{p_j}(S_∞)` (for `Δ f_j` because a size dominates its top cube, so the `S_∞`-superlevel
measure is at most the `S₂` one), and `S_∞` is submultiplicative. -/

/-- A size dominates the value at the top cube: `|F(T)| ≤ S_p(F)(T)`. [PROVED] -/
theorem enorm_le_sizeP {p : ℝ} (hp : 0 < p) (F : DyadicCube d → ℝ) (T : DyadicCube d) :
    ‖F T‖ₑ ≤ sizeP p F T := by
  have hT : T ∈ T.tree := fun x hx => hx
  calc ‖F T‖ₑ = (‖F T‖ₑ ^ p) ^ (1 / p) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal T.vol⁻¹ *
          ∑' Q : T.tree, ‖F Q‖ₑ ^ p * ENNReal.ofReal (Q : DyadicCube d).vol) ^ (1 / p) := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        calc ‖F T‖ₑ ^ p = ENNReal.ofReal T.vol⁻¹ * (‖F T‖ₑ ^ p * ENNReal.ofReal T.vol) := by
              rw [mul_comm (‖F T‖ₑ ^ p), ← mul_assoc,
                ← ENNReal.ofReal_mul (inv_nonneg.mpr T.vol_pos.le), inv_mul_cancel₀ T.vol_pos.ne',
                ENNReal.ofReal_one, one_mul]
          _ ≤ _ := mul_le_mul' le_rfl
              (ENNReal.le_tsum (f := fun Q : T.tree => ‖F Q‖ₑ ^ p * ENNReal.ofReal (Q : DyadicCube
                d).vol)
                (⟨T, hT⟩ : T.tree))

/-- **The `S_∞`-superlevel measure is at most the `S_p` one**: an exceptional set for `S_p` is one
for `S_∞`, since `S_p(F 𝟙_{𝒢ᶜ})(Q) ≥ |F(Q)|` for `Q ∉ 𝒢`. [PROVED] -/
theorem superlevel_sizeInf_le_sizeP {p : ℝ} (hp : 0 < p) (F : DyadicCube d → ℝ) (lam : ℝ) :
    superlevel sizeInf F lam ≤ superlevel (sizeP p) F lam := by
  unfold superlevel
  apply le_iInf₂
  intro G hG
  apply iInf₂_le G
  intro T
  change (⨆ Q : T.tree, ‖(Gᶜ.indicator F) Q‖ₑ) ≤ ENNReal.ofReal lam
  apply iSup_le
  intro Q
  exact (enorm_le_sizeP hp (Gᶜ.indicator F) Q).trans (hG Q)

/-- `‖F‖_{L^q(S_∞)} ≤ ‖F‖_{L^q(S_p)}`. [PROVED] -/
theorem outerLpNorm_sizeInf_le_sizeP {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (F : DyadicCube d → ℝ) :
    outerLpNorm sizeInf q F ≤ outerLpNorm (sizeP p) q F := by
  unfold outerLpNorm
  refine ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (lintegral_mono fun lam => ?_)) (by positivity)
  exact mul_le_mul' le_rfl (superlevel_sizeInf_le_sizeP hp F lam)

/-- `S_∞(FG) ≤ S_∞(F) S_∞(G)`. [PROVED] -/
theorem sizeInf_mul_le (F G : DyadicCube d → ℝ) (T : DyadicCube d) :
    sizeInf (F * G) T ≤ sizeInf F T * sizeInf G T := by
  refine iSup_le fun Q => ?_
  rw [Pi.mul_apply, enorm_mul]
  exact mul_le_mul' (le_iSup (fun Q : T.tree => ‖F Q‖ₑ) Q) (le_iSup (fun Q : T.tree => ‖G Q‖ₑ) Q)

/-- **Hölder's inequality in `L^·(S_∞)` for finitely many factors**: if
`‖G_j‖_{L^{p_j}(S_∞)} ≤ K_j < ∞` and `∑_{j ∈ J} 1/p_j ≤ 1`, then
`‖∏_{j ∈ J} G_j‖_{L^{r}(S_∞)} ≤ 2^{|J|} ∏_{j ∈ J} K_j` with `1/r = ∑_{j ∈ J} 1/p_j`. [PROVED] -/
theorem outerLpNorm_prod_sizeInf_le (p : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (G : Fin n → DyadicCube d → ℝ) (K : Fin n → ENNReal) (hK : ∀ j, K j ≠ ⊤)
    (hG : ∀ j, outerLpNorm sizeInf (p j) (G j) ≤ K j) :
    ∀ (J : Finset (Fin n)), J.Nonempty → ∑ j ∈ J, 1 / p j ≤ 1 →
      outerLpNorm sizeInf (∑ j ∈ J, 1 / p j)⁻¹ (∏ j ∈ J, G j) ≤
        (2 : ENNReal) ^ J.card * ∏ j ∈ J, K j := by
  intro J hJ
  induction hJ using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro _
    rw [Finset.sum_singleton, Finset.prod_singleton, Finset.prod_singleton, Finset.card_singleton,
      pow_one, one_div, inv_inv]
    exact (hG a).trans (le_mul_of_one_le_left bot_le one_le_two)
  | cons a s ha hs ih =>
    intro hsum
    rw [Finset.sum_cons] at hsum ⊢
    rw [Finset.prod_cons, Finset.prod_cons, Finset.card_cons, pow_succ]
    have hpos : ∀ j, 0 < 1 / p j := fun j => by have := hp j; positivity
    have hs0 : 0 < ∑ j ∈ s, 1 / p j := Finset.sum_pos (fun j _ => hpos j) hs
    have hs1 : ∑ j ∈ s, 1 / p j ≤ 1 := le_trans (le_add_of_nonneg_left (hpos a).le) hsum
    have ih' := ih hs1
    have hfinG : outerLpNorm sizeInf (∑ j ∈ s, 1 / p j)⁻¹ (∏ j ∈ s, G j) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
        (ENNReal.prod_ne_top fun j _ => hK j)) ih'
    have hfinF : outerLpNorm sizeInf (p a) (G a) ≠ ⊤ := ne_top_of_le_ne_top (hK a) (hG a)
    have hmul := outerLpNorm_mul_le sizeInf sizeInf sizeInf (fun F G T h => sizeInf_mono h T)
      (fun F G T h => sizeInf_mono h T) sizeInf_mul_le (hp a) (inv_pos.mpr hs0)
      (inv_pos.mpr (add_pos (hpos a) hs0))
      (by simp only [one_div, inv_inv]) (G a) (∏ j ∈ s, G j) hfinF hfinG
    refine hmul.trans ?_
    have h2 : (2 : ENNReal) ^ (1 / (1 / p a + ∑ j ∈ s, 1 / p j)⁻¹) ≤ 2 := by
      calc (2 : ENNReal) ^ (1 / (1 / p a + ∑ j ∈ s, 1 / p j)⁻¹) ≤ (2 : ENNReal) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le one_le_two (by rw [one_div, inv_inv]; exact hsum)
        _ = 2 := ENNReal.rpow_one 2
    calc (2 : ENNReal) ^ (1 / (1 / p a + ∑ j ∈ s, 1 / p j)⁻¹) *
          (outerLpNorm sizeInf (p a) (G a) *
            outerLpNorm sizeInf (∑ j ∈ s, 1 / p j)⁻¹ (∏ j ∈ s, G j))
        ≤ 2 * (K a * ((2 : ENNReal) ^ s.card * ∏ j ∈ s, K j)) :=
          mul_le_mul' h2 (mul_le_mul' (hG a) ih')
      _ = (2 : ENNReal) ^ s.card * 2 * (K a * ∏ j ∈ s, K j) := by ring

/-- `Δ_Q f = ((2^d)⁻¹ ∑_ε |[f]_{Q_ε} − [f]_Q|²)^{1/2}`: the children have volume `2^{-d} |Q|`.
[PROVED] -/
theorem martDiff_eq_sqrt (Q : DyadicCube d) (f : (Fin d → ℝ) → ℝ) :
    martDiff Q f = Real.sqrt ((2 ^ d)⁻¹ * ∑ ε : Fin d → Bool, |avg (Q.child ε) f - avg Q f| ^ 2) :=
      by
  unfold martDiff
  congr 1
  have h : ∀ ε : Fin d → Bool, (Q.child ε).vol = Q.vol / 2 ^ d := fun ε => by
    rw [eq_div_iff (by positivity)]
    exact Q.vol_child ε
  simp only [h]
  rw [← Finset.sum_mul]
  calc Q.vol⁻¹ * ((∑ ε : Fin d → Bool, |avg (Q.child ε) f - avg Q f| ^ 2) * (Q.vol / 2 ^ d))
      = (Q.vol⁻¹ * Q.vol) * ((2 ^ d)⁻¹ * ∑ ε : Fin d → Bool, |avg (Q.child ε) f - avg Q f| ^ 2) :=
        by
        ring
    _ = _ := by rw [inv_mul_cancel₀ Q.vol_pos.ne', one_mul]

/-- **The martingale difference is bounded by `2^{d/2} Δ_Q f`**: `|Δ_Q f(x)| ≤ √(2^d) Δ_Q f`.
[PROVED] -/
theorem abs_mdiff_le (Q : DyadicCube d) (f : TestFun d) (x : Fin d → ℝ) :
    |(mdiff Q f : (Fin d → ℝ) → ℝ) x| ≤
      Real.sqrt (2 ^ d) * martDiff Q (f : (Fin d → ℝ) → ℝ) := by
  have hpos : 0 ≤ Real.sqrt (2 ^ d) * martDiff Q (f : (Fin d → ℝ) → ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (martDiff_nonneg _ _)
  by_cases hx : x ∈ Q.toSet
  · obtain ⟨L, hL, hxL⟩ := StoppingData.exists_mem_level 1 hx
    rw [level_one] at hL
    obtain ⟨ε₀, rfl⟩ := StoppingData.mem_children.mp hL
    have hval : (mdiff Q f : (Fin d → ℝ) → ℝ) x =
        avg (Q.child ε₀) (f : (Fin d → ℝ) → ℝ) - avg Q (f : (Fin d → ℝ) → ℝ) := by
      rw [mdiff_eq, Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_mem hx, Pi.one_apply,
        smul_eq_mul, mul_one, Finset.sum_eq_single ε₀]
      · rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind, Set.indicator_of_mem hxL,
          Pi.one_apply, smul_eq_mul, mul_one]
      · intro ε _ hne
        rw [Submodule.coe_smul, Pi.smul_apply, TestFun.coe_ind,
          Set.indicator_of_notMem (Set.disjoint_right.mp (Q.child_disjoint hne) hxL), smul_zero]
      · intro h
        exact absurd (Finset.mem_univ ε₀) h
    rw [hval, martDiff_eq_sqrt, ← Real.sqrt_mul (by positivity), ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]
    refine Real.abs_le_sqrt ?_
    rw [← sq_abs]
    exact Finset.single_le_sum (f := fun ε => |avg (Q.child ε) (f : (Fin d → ℝ) → ℝ) -
      avg Q (f : (Fin d → ℝ) → ℝ)| ^ 2) (fun _ _ => by positivity) (Finset.mem_univ ε₀)
  · rw [mdiff_supportedOn Q f x hx, abs_zero]
    exact hpos

/-- `‖Δ_Q f‖_r ≤ √(2^d) Δ_Q f |Q|^{1/r}`. [PROVED] -/
theorem lpNorm_mdiff_le (Q : DyadicCube d) (f : TestFun d) {r : ℝ} (hr : 0 < r) :
    lpNorm (mdiff Q f : (Fin d → ℝ) → ℝ) r ≤
      Real.sqrt (2 ^ d) * martDiff Q (f : (Fin d → ℝ) → ℝ) * Q.vol ^ (1 / r) :=
  TestFun.lpNorm_le_of_abs_le (mdiff Q f) (mdiff_supportedOn Q f)
    (mul_nonneg (Real.sqrt_nonneg _) (martDiff_nonneg _ _)) (abs_mdiff_le Q f) hr

/-- **The block bound in terms of the martingale differences**:
`|Λ(Δ_Q f_j (j ∈ S), 𝟙_Q (j ∉ S))| ≤ B 2^{dn} 2^{dn} |Q| ∏_{j ∈ S} Δ_Q f_j`. [PROVED] -/
theorem abs_form_blockTuple_le {T : PerfectCZForm d n} {p : HolderTuple n} {B : ℝ}
    (hT : T1Testing T p B) (hB : 1 ≤ B) (Q : DyadicCube d) (f : Fin n → TestFun d)
    (S : Finset (Fin n)) :
    |T.form (blockTuple Q f S)| ≤
      B * 2 ^ (d * n) * 2 ^ (d * n) * Q.vol * ∏ j ∈ S, martDiff Q (f j : (Fin d → ℝ) → ℝ) := by
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hV := Q.vol_pos
  have h1 : |T.form (blockTuple Q f S)| ≤ B * 2 ^ (d * n) * prodNorm p (blockTuple Q f S) := by
    refine abs_form_le_of_constOn_children hT hB Q _ (fun j => ?_) (fun j ε => ?_)
    · unfold blockTuple
      split_ifs
      · exact mdiff_supportedOn Q _
      · exact TestFun.ind_supportedOn Q
    · unfold blockTuple
      split_ifs
      · exact mdiff_constOn_child Q _ ε
      · exact constOn_ind (Or.inl (Q.child_subset ε))
  -- the product of the norms
  have hsq : Real.sqrt (2 ^ d) ≤ 2 ^ d := by
    calc Real.sqrt (2 ^ d) ≤ Real.sqrt ((2 ^ d) ^ 2) :=
          Real.sqrt_le_sqrt (le_self_pow₀ (one_le_pow₀ one_le_two) two_ne_zero)
      _ = 2 ^ d := Real.sqrt_sq (by positivity)
  have h2 : prodNorm p (blockTuple Q f S) ≤
      (∏ j ∈ S, (Real.sqrt (2 ^ d) * martDiff Q (f j : (Fin d → ℝ) → ℝ))) * Q.vol := by
    unfold prodNorm
    have e : ∀ j, (if j ∈ S then Real.sqrt (2 ^ d) * martDiff Q (f j : (Fin d → ℝ) → ℝ) else 1) *
        Q.vol ^ (1 / p.p j) =
        if j ∈ S then Real.sqrt (2 ^ d) * martDiff Q (f j : (Fin d → ℝ) → ℝ) * Q.vol ^ (1 / p.p j)
        else Q.vol ^ (1 / p.p j) := by
      intro j
      split_ifs <;> ring
    calc ∏ j, lpNorm ((blockTuple Q f S j : TestFun d) : (Fin d → ℝ) → ℝ) (p.p j)
        ≤ ∏ j, (if j ∈ S then Real.sqrt (2 ^ d) * martDiff Q (f j : (Fin d → ℝ) → ℝ) else 1) *
            Q.vol ^ (1 / p.p j) := by
          refine Finset.prod_le_prod₀ (fun j _ => lpNorm_nonneg _ _) fun j _ => ?_
          rw [e]
          unfold blockTuple
          split_ifs
          · exact lpNorm_mdiff_le Q (f j) (by linarith [p.one_lt j])
          · exact le_of_eq (TestFun.lpNorm_ind Q (by linarith [p.one_lt j]))
      _ = (∏ j ∈ S, (Real.sqrt (2 ^ d) * martDiff Q (f j : (Fin d → ℝ) → ℝ))) * Q.vol := by
          rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter,
            ← Real.rpow_sum_of_pos hV, p.sum_one_div, Real.rpow_one]
  have h3 : ∏ j ∈ S, (Real.sqrt (2 ^ d) * martDiff Q (f j : (Fin d → ℝ) → ℝ)) ≤
      2 ^ (d * n) * ∏ j ∈ S, martDiff Q (f j : (Fin d → ℝ) → ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => martDiff_nonneg _ _)
    calc Real.sqrt (2 ^ d) ^ S.card ≤ (2 ^ d) ^ S.card :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq _
      _ ≤ (2 ^ d) ^ n := pow_le_pow_right₀ (one_le_pow₀ one_le_two)
          ((Finset.card_le_univ S).trans (le_of_eq (Fintype.card_fin n)))
      _ = 2 ^ (d * n) := (pow_mul 2 d n).symm
  calc |T.form (blockTuple Q f S)|
      ≤ B * 2 ^ (d * n) * prodNorm p (blockTuple Q f S) := h1
    _ ≤ B * 2 ^ (d * n) *
        ((∏ j ∈ S, (Real.sqrt (2 ^ d) * martDiff Q (f j : (Fin d → ℝ) → ℝ))) * Q.vol) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ B * 2 ^ (d * n) *
        ((2 ^ (d * n) * ∏ j ∈ S, martDiff Q (f j : (Fin d → ℝ) → ℝ)) * Q.vol) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hV.le) (by positivity)
    _ = _ := by ring

/-- Splitting a product over `S` and `Sᶜ` at two elements `i₁ ≠ i₂` of `S`:
`∏_{j ∈ S} a_j ∏_{j ∉ S} b_j = a_{i₁} a_{i₂} ∏_{j ≠ i₁, i₂} (if j ∈ S then a_j else b_j)`. [PROVED]
-/
theorem prod_split_two {S : Finset (Fin n)} {i₁ i₂ : Fin n} (hi₁ : i₁ ∈ S) (hi₂ : i₂ ∈ S)
    (hne : i₁ ≠ i₂) (a b : Fin n → ℝ) :
    (∏ j ∈ S, a j) * ∏ j ∈ Sᶜ, b j =
      a i₁ * a i₂ * ∏ j ∈ (Finset.univ.erase i₁).erase i₂, (if j ∈ S then a j else b j) := by
  have hi₂' : i₂ ∈ S.erase i₁ := Finset.mem_erase.mpr ⟨hne.symm, hi₂⟩
  have e1 : ((Finset.univ.erase i₁).erase i₂).filter (fun j => j ∈ S) = (S.erase i₁).erase i₂ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  have e2 : ((Finset.univ.erase i₁).erase i₂).filter (fun j => ¬ j ∈ S) = Sᶜ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_compl]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨fun e => h (e ▸ hi₂), fun e => h (e ▸ hi₁)⟩, h⟩
  rw [Finset.prod_ite, e1, e2, ← Finset.mul_prod_erase S a hi₁,
    ← Finset.mul_prod_erase (S.erase i₁) a hi₂']
  ring

/-- Outer Hölder controls two martingale-difference factors and any remaining average factors. -/
theorem outerLpNorm_two_differences_product_le (p : HolderTuple n)
    (i₁ i₂ : Fin n) (hne : i₁ ≠ i₂) (Δ G : Fin n → DyadicCube d → ℝ)
    (K : Fin n → ENNReal) (hKfin : ∀ j, K j ≠ ⊤)
    (hΔK : ∀ j, outerLpNorm (sizeP 2) (p.p j) (Δ j) ≤ K j)
    (hGK : ∀ j, outerLpNorm sizeInf (p.p j) (G j) ≤ K j) :
    outerLpNorm (sizeP 1) 1
        (Δ i₁ * Δ i₂ * ∏ j ∈ (Finset.univ.erase i₁).erase i₂, G j) ≤
      2 * (2 * (K i₁ * K i₂)) *
        ((2 : ENNReal) ^ ((Finset.univ.erase i₁).erase i₂).card *
          ∏ j ∈ (Finset.univ.erase i₁).erase i₂, K j) := by
  classical
  let F : DyadicCube d → ℝ := Δ i₁ * Δ i₂ * ∏ j ∈ (Finset.univ.erase i₁).erase i₂, G j
  have hF : F = Δ i₁ * Δ i₂ * ∏ j ∈ (Finset.univ.erase i₁).erase i₂, G j := rfl
  change outerLpNorm (sizeP 1) 1 F ≤ _
  have hp : ∀ j, 0 < p.p j := fun j => zero_lt_one.trans (p.one_lt j)
  have hpos : ∀ j, 0 < 1 / p.p j := fun j => one_div_pos.mpr (hp j)
  have hi₂' : i₂ ∈ Finset.univ.erase i₁ := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i₂⟩
  have hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 2 F T ≤ sizeP 2 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 1 F T ≤ sizeP 1 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hSinf : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeInf F T ≤ sizeInf G T :=
    fun F G T h => sizeInf_mono h T
  have hΔfin : ∀ j, outerLpNorm (sizeP 2) (p.p j) (Δ j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (hKfin j) (hΔK j)
  have hp12 : 0 < 1 / p.p i₁ + 1 / p.p i₂ := add_pos (hpos i₁) (hpos i₂)
  have hsum_univ : 1 / p.p i₁ + (1 / p.p i₂ + ∑ j ∈ (Finset.univ.erase i₁).erase i₂, 1 / p.p j) = 1
    := by
    have h1 : 1 / p.p i₂ + ∑ j ∈ (Finset.univ.erase i₁).erase i₂, 1 / p.p j =
        ∑ j ∈ Finset.univ.erase i₁, 1 / p.p j :=
      Finset.add_sum_erase (Finset.univ.erase i₁) (fun j => 1 / p.p j) hi₂'
    have h2 : 1 / p.p i₁ + ∑ j ∈ Finset.univ.erase i₁, 1 / p.p j = ∑ j, 1 / p.p j :=
      Finset.add_sum_erase Finset.univ (fun j => 1 / p.p j) (Finset.mem_univ i₁)
    rw [h1, h2]
    exact p.sum_one_div
  by_cases hJ : ((Finset.univ.erase i₁).erase i₂).Nonempty
  · -- `n ≥ 3`: the remaining factors are in `L^·(S_∞)`
    have hJpos : 0 < ∑ j ∈ (Finset.univ.erase i₁).erase i₂, 1 / p.p j :=
      Finset.sum_pos (fun j _ => hpos j) hJ
    have hs0 : 0 < (1 / p.p i₁ + 1 / p.p i₂)⁻¹ := inv_pos.mpr hp12
    have hs'0 : 0 < (∑ j ∈ (Finset.univ.erase i₁).erase i₂, 1 / p.p j)⁻¹ := inv_pos.mpr hJpos
    have hlt1 : 1 / p.p i₁ + 1 / p.p i₂ < 1 := by linarith
    have hlt2 : ∑ j ∈ (Finset.univ.erase i₁).erase i₂, 1 / p.p j < 1 := by linarith
    have hs1 : 1 < (1 / p.p i₁ + 1 / p.p i₂)⁻¹ := by
      rw [lt_inv_comm₀ one_pos hp12, inv_one]
      exact hlt1
    have hs'1 : 1 < (∑ j ∈ (Finset.univ.erase i₁).erase i₂, 1 / p.p j)⁻¹ := by
      rw [lt_inv_comm₀ one_pos hJpos, inv_one]
      exact hlt2
    have hss' : 1 / (1 / p.p i₁ + 1 / p.p i₂)⁻¹ +
        1 / (∑ j ∈ (Finset.univ.erase i₁).erase i₂, 1 / p.p j)⁻¹ = 1 := by
      simp only [one_div, inv_inv]
      simp only [one_div] at hsum_univ
      rw [add_assoc]
      exact hsum_univ
    have h2Δ := outerLpNorm_mul_le (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂
      sizeP_one_mul_le_sizeP_two (hp i₁) (hp i₂) hs0 (by simp only [one_div, inv_inv]) (Δ i₁)
      (Δ i₂) (hΔfin i₁) (hΔfin i₂)
    have h2s : (2 : ENNReal) ^ (1 / (1 / p.p i₁ + 1 / p.p i₂)⁻¹) ≤ 2 := by
      calc (2 : ENNReal) ^ (1 / (1 / p.p i₁ + 1 / p.p i₂)⁻¹) ≤ (2 : ENNReal) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le one_le_two (by
              simp only [one_div, inv_inv]
              simpa only [one_div] using hlt1.le)
        _ = 2 := ENNReal.rpow_one 2
    have hA : outerLpNorm (sizeP 1) (1 / p.p i₁ + 1 / p.p i₂)⁻¹ (Δ i₁ * Δ i₂) ≤
        2 * (K i₁ * K i₂) :=
      h2Δ.trans (mul_le_mul' h2s (mul_le_mul' (hΔK i₁) (hΔK i₂)))
    have hBnd := outerLpNorm_prod_sizeInf_le p.p hp G K hKfin hGK _ hJ hlt2.le
    have hAfin : outerLpNorm (sizeP 1) (1 / p.p i₁ + 1 / p.p i₂)⁻¹ (Δ i₁ * Δ i₂) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.mul_ne_top (hKfin i₁) (hKfin i₂))) hA
    have hBfin : outerLpNorm sizeInf (∑ j ∈ (Finset.univ.erase i₁).erase i₂, 1 / p.p j)⁻¹
        (∏ j ∈ (Finset.univ.erase i₁).erase i₂, G j) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
        (ENNReal.prod_ne_top fun j _ => hKfin j)) hBnd
    have h3 := outerL1Norm_mul_le (sizeP 1) (sizeP 1) sizeInf hS₁ hSinf
      sizeP_one_mul_le_sizeInf' hs1 hs'1 hss' (Δ i₁ * Δ i₂)
      (∏ j ∈ (Finset.univ.erase i₁).erase i₂, G j) hAfin hBfin
    refine h3.trans ?_
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (mul_le_mul' hA hBnd)
  · -- `n = 2`: only the two differences
    rw [Finset.not_nonempty_iff_eq_empty] at hJ
    have hJsum0 : ∑ j ∈ (Finset.univ.erase i₁).erase i₂, 1 / p.p j = 0 := by
      rw [hJ, Finset.sum_empty]
    have h12 : 1 / p.p i₁ + 1 / p.p i₂ = 1 / 1 := by
      rw [div_one]
      rw [hJsum0, add_zero] at hsum_univ
      exact hsum_univ
    have h2Δ := outerLpNorm_mul_le (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂
      sizeP_one_mul_le_sizeP_two (hp i₁) (hp i₂) one_pos h12 (Δ i₁) (Δ i₂) (hΔfin i₁) (hΔfin i₂)
    have hF' : F = Δ i₁ * Δ i₂ := by
      simp only [hF, hJ, Finset.prod_empty, mul_one]
    simp only [hJ, Finset.prod_empty, Finset.card_empty, pow_zero, mul_one]
    rw [hF']
    refine h2Δ.trans ?_
    rw [div_one, ENNReal.rpow_one]
    calc 2 * (outerLpNorm (sizeP 2) (p.p i₁) (Δ i₁) * outerLpNorm (sizeP 2) (p.p i₂) (Δ i₂))
        ≤ 2 * (K i₁ * K i₂) := mul_le_mul' le_rfl (mul_le_mul' (hΔK i₁) (hΔK i₂))
      _ ≤ 2 * (2 * (K i₁ * K i₂)) := mul_le_mul' le_rfl (le_mul_of_one_le_left bot_le one_le_two)

/-- **The terms with two or more differences**: for `|S| ≥ 2` there is `C` (depending only on
`d`, `n`, `B`, the exponents and `S`) such that for every cube `R`, depth `N` and tuple `f`,
`∑_{Q ∈ nonleaf N R} ∏_{j ∉ S} |[f_j]_Q| · |Λ(Δ_Q f_j (j ∈ S), 𝟙_Q (j ∉ S))| ≤ C ∏_j ‖f_j‖_{p_j}`.
[PROVED] -/
theorem sum_block_le (hd : d ≠ 0) {p : HolderTuple n} {B : ℝ}
    (hB : 1 ≤ B) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : PerfectCZForm d n), T1Testing T p B →
      ∀ (R : DyadicCube d) (N : ℕ) (f : Fin n → TestFun d),
      ∑ Q ∈ StoppingData.nonleaf N R,
        (∏ j ∈ Sᶜ, |avg Q (f j : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f S)| ≤
      C * prodNorm p f := by
  obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  choose Cc hCc0 hCc using fun j => carlesonEmbedding hd (p.p j) (p.one_lt j)
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hCprod : 0 ≤ ∏ j, Cc j := Finset.prod_nonneg fun j _ => hCc0 j
  have hK₁ : (0 : ℝ) ≤ B * 2 ^ (d * n) * 2 ^ (d * n) := by positivity
  refine ⟨B * 2 ^ (d * n) * 2 ^ (d * n) * (4 * 2 * 2 * 2 ^ n) * ∏ j, Cc j, by positivity, ?_⟩
  intro T hT R N f
  have hp : ∀ j, 0 < p.p j := fun j => by linarith [p.one_lt j]
  have hi₂' : i₂ ∈ Finset.univ.erase i₁ := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i₂⟩
  -- the functions on cubes
  set Δ : Fin n → DyadicCube d → ℝ := fun j Q => martDiff Q (f j : (Fin d → ℝ) → ℝ) with hΔ
  set E : Fin n → DyadicCube d → ℝ := fun j Q => martAvg Q (f j : (Fin d → ℝ) → ℝ) with hE
  set G : Fin n → DyadicCube d → ℝ := fun j Q => if j ∈ S then Δ j Q else E j Q with hG
  set F : DyadicCube d → ℝ := Δ i₁ * Δ i₂ * ∏ j ∈ (Finset.univ.erase i₁).erase i₂, G j with hF
  set K : Fin n → ENNReal := fun j =>
    ENNReal.ofReal (Cc j) * eLpNorm (f j : (Fin d → ℝ) → ℝ) (ENNReal.ofReal (p.p j)) with hK
  have hΔnn : ∀ j Q, 0 ≤ Δ j Q := fun _ _ => martDiff_nonneg _ _
  have hEnn : ∀ j Q, 0 ≤ E j Q := fun _ _ => martAvg_nonneg _ _
  have hGnn : ∀ j Q, 0 ≤ G j Q := fun j Q => by
    simp only [hG]
    split_ifs
    · exact hΔnn j Q
    · exact hEnn j Q
  have hFnn : ∀ Q, 0 ≤ F Q := fun Q => by
    simp only [hF, Pi.mul_apply, Finset.prod_apply]
    exact mul_nonneg (mul_nonneg (hΔnn _ _) (hΔnn _ _)) (Finset.prod_nonneg fun j _ => hGnn j Q)
  -- the pointwise bound
  have hpt : ∀ Q, (∏ j ∈ Sᶜ, |avg Q (f j : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f S)| ≤
      B * 2 ^ (d * n) * 2 ^ (d * n) * Q.vol * F Q := by
    intro Q
    have h1 := abs_form_blockTuple_le hT hB Q f S
    have h2 : (∏ j ∈ S, Δ j Q) * ∏ j ∈ Sᶜ, E j Q = F Q := by
      rw [prod_split_two hi₁ hi₂ hne (fun j => Δ j Q) (fun j => E j Q)]
      simp only [hF, Pi.mul_apply, Finset.prod_apply, hG]
    calc (∏ j ∈ Sᶜ, |avg Q (f j : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f S)|
        ≤ (∏ j ∈ Sᶜ, E j Q) *
            (B * 2 ^ (d * n) * 2 ^ (d * n) * Q.vol * ∏ j ∈ S, Δ j Q) :=
          mul_le_mul_of_nonneg_left h1 (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      _ = B * 2 ^ (d * n) * 2 ^ (d * n) * Q.vol * F Q := by
          rw [← h2]
          ring
  -- the sum in `ℝ≥0∞` and Proposition 3.6
  have hsum : ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R,
      (∏ j ∈ Sᶜ, |avg Q (f j : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f S)|) ≤
      ENNReal.ofReal (B * 2 ^ (d * n) * 2 ^ (d * n)) * (4 * outerLpNorm (sizeP 1) 1 F) := by
    calc ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R,
          (∏ j ∈ Sᶜ, |avg Q (f j : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f S)|)
        ≤ ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R,
            B * 2 ^ (d * n) * 2 ^ (d * n) * Q.vol * F Q) :=
          ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun Q _ => hpt Q)
      _ = ∑ Q ∈ StoppingData.nonleaf N R,
            ENNReal.ofReal (B * 2 ^ (d * n) * 2 ^ (d * n)) * (‖F Q‖ₑ * ENNReal.ofReal Q.vol) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun Q _ =>
            mul_nonneg (mul_nonneg hK₁ Q.vol_pos.le) (hFnn Q)]
          refine Finset.sum_congr rfl fun Q _ => ?_
          rw [mul_assoc, ENNReal.ofReal_mul hK₁, mul_comm Q.vol, ENNReal.ofReal_mul (hFnn Q),
            Real.enorm_eq_ofReal_abs, abs_of_nonneg (hFnn Q)]
      _ ≤ ENNReal.ofReal (B * 2 ^ (d * n) * 2 ^ (d * n)) *
            ∑' Q : DyadicCube d, ‖F Q‖ₑ * ENNReal.ofReal Q.vol := by
          rw [← Finset.mul_sum]
          exact mul_le_mul' le_rfl (ENNReal.sum_le_tsum _)
      _ ≤ _ := mul_le_mul' le_rfl (tsum_enorm_mul_vol_le F)
  -- monotonicity of the sizes and the Carleson bounds
  have hKfin : ∀ j, K j ≠ ⊤ := fun j =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (TestFun.memLp (f j).2 _).eLpNorm_ne_top
  have hΔK : ∀ j, outerLpNorm (sizeP 2) (p.p j) (Δ j) ≤ K j := fun j =>
    (hCc j _ (TestFun.memLp (f j).2 _)).2
  have hEK : ∀ j, outerLpNorm sizeInf (p.p j) (E j) ≤ K j := fun j =>
    (hCc j _ (TestFun.memLp (f j).2 _)).1
  have hGK : ∀ j, outerLpNorm sizeInf (p.p j) (G j) ≤ K j := by
    intro j
    by_cases hj : j ∈ S
    · have e : G j = Δ j := funext fun Q => by simp only [hG, hj, ↓reduceIte]
      rw [e]
      exact (outerLpNorm_sizeInf_le_sizeP two_pos (hp j) _).trans (hΔK j)
    · have e : G j = E j := funext fun Q => by simp only [hG, hj, ↓reduceIte]
      rw [e]
      exact hEK j
  have hprodK : K i₁ * (K i₂ * ∏ j ∈ (Finset.univ.erase i₁).erase i₂, K j) = ∏ j, K j := by
    rw [Finset.mul_prod_erase _ _ hi₂', Finset.mul_prod_erase _ _ (Finset.mem_univ i₁)]
  -- the outer Hölder inequalities
  have hhold :=
    outerLpNorm_two_differences_product_le p i₁ i₂ hne Δ G K hKfin hΔK hGK
  -- the product of the Carleson constants and the norms
  have hKprod : ∏ j, K j = ENNReal.ofReal ((∏ j, Cc j) * prodNorm p f) := by
    have e : ∀ j, eLpNorm (f j : (Fin d → ℝ) → ℝ) (ENNReal.ofReal (p.p j)) =
        ENNReal.ofReal (lpNorm (f j : (Fin d → ℝ) → ℝ) (p.p j)) := fun j =>
      (ENNReal.ofReal_toReal (TestFun.memLp (f j).2 _).eLpNorm_ne_top).symm
    simp only [hK, e]
    rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg fun j _ => hCc0 j,
      ← ENNReal.ofReal_prod_of_nonneg fun j _ => lpNorm_nonneg _ _, ← ENNReal.ofReal_mul hCprod,
      prodNorm]
  have hcard : ((Finset.univ.erase i₁).erase i₂).card ≤ n :=
    (Finset.card_le_univ _).trans (le_of_eq (Fintype.card_fin n))
  have hc : (4 * 2 * 2 * 2 ^ n : ENNReal) = ENNReal.ofReal (4 * 2 * 2 * 2 ^ n) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_ofNat]
  have hfinal : ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R,
      (∏ j ∈ Sᶜ, |avg Q (f j : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f S)|) ≤
      ENNReal.ofReal (B * 2 ^ (d * n) * 2 ^ (d * n) * (4 * 2 * 2 * 2 ^ n) * (∏ j, Cc j) *
        prodNorm p f) := by
    calc ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R,
          (∏ j ∈ Sᶜ, |avg Q (f j : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f S)|)
        ≤ ENNReal.ofReal (B * 2 ^ (d * n) * 2 ^ (d * n)) * (4 * outerLpNorm (sizeP 1) 1 F) := hsum
      _ ≤ ENNReal.ofReal (B * 2 ^ (d * n) * 2 ^ (d * n)) * (4 * (2 * (2 * (K i₁ * K i₂)) *
            ((2 : ENNReal) ^ ((Finset.univ.erase i₁).erase i₂).card *
              ∏ j ∈ (Finset.univ.erase i₁).erase i₂, K j))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hhold)
      _ = ENNReal.ofReal (B * 2 ^ (d * n) * 2 ^ (d * n)) *
            (4 * 2 * 2 * (2 : ENNReal) ^ ((Finset.univ.erase i₁).erase i₂).card) * ∏ j, K j := by
          rw [← hprodK]
          ring
      _ ≤ ENNReal.ofReal (B * 2 ^ (d * n) * 2 ^ (d * n)) * (4 * 2 * 2 * (2 : ENNReal) ^ n) *
            ∏ j, K j :=
          mul_le_mul' (mul_le_mul' le_rfl (mul_le_mul' le_rfl (pow_le_pow_right₀ one_le_two hcard)))
            le_rfl
      _ = _ := by
          rw [hKprod, hc, ← ENNReal.ofReal_mul hK₁, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  rw [← ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (by positivity) hCprod) (prodNorm_nonneg p f))]
  exact hfinal

/-! #### The paraproduct terms (exponents at most `2`)

For `S = {j}` the term at `Q` is `∏_{i ≠ j} [f_i]_Q · Λ(𝟙_Q, …, Δ_Q f_j, …, 𝟙_Q)`. Writing
`Δ_Q f_j = ∑_ε c_ε 𝟙_{Q_ε}` with `∑_ε c_ε = 0`, the form is `∑_ε c_ε g_Q(ε)` with the coefficients
`g_Q(ε) = Λ(𝟙_Q, …, 𝟙_{Q_ε}, …, 𝟙_Q)` (`coefChild`), equivalently `∑_ε c_ε v_Q(ε)` with the
centered coefficients `v_Q = g_Q − [g_Q]` (`coefV`), so that by Cauchy–Schwarz it is at most
`|Q| Δ_Q f_j β_Q` with the **Carleson sequence** `β_Q = √(2^d) ‖v_Q‖ / |Q|` (`carl`). The Carleson
condition `∑_{Q ⊆ P} β_Q² |Q| ≤ B² |P|` follows from the testing condition in the slot `j`
applied to the test function `φ = ∑_{Q ⊆ P} ψ_Q`, `ψ_Q = |Q|⁻¹ ∑_ε v_Q(ε) 𝟙_{Q_ε}` (`psi`): by
perfect smoothness the coefficients are intrinsic, `Λ(𝟙_P, …, ψ_Q, …, 𝟙_P) = Λ(𝟙_Q, …, ψ_Q, …, 𝟙_Q)
= |Q|⁻¹ ‖v_Q‖²`, so `Λ(𝟙_P, …, φ, …, 𝟙_P) = ∑_Q |Q|⁻¹ ‖v_Q‖² =: Σ`; the blocks `ψ_Q` are orthogonal
(Pythagoras), `‖φ‖₂² = 2^{-d} Σ`; and for `p_j ≤ 2` Hölder on `P` gives
`Σ ≤ B |P|^{1-1/p_j} ‖φ‖_{p_j} ≤ B |P|^{1/2} ‖φ‖₂`, hence `Σ ≤ 2^{-d} B² |P|`. Below the resolution
of the form the coefficients `g_Q(ε)` do not depend on `ε` and `β_Q = 0`, so the condition on the
finite trees gives `‖β‖_{L^∞(S₂)} ≤ B`. The paraproduct sum is then bounded like the terms with
two differences, with `β` in the role of the second difference. -/

/-- The tuple with `φ` in the slot `j` and `𝟙_Q` elsewhere. -/
noncomputable def oneTuple (Q : DyadicCube d) (j : Fin n) (φ : TestFun d) : Fin n → TestFun d :=
  Function.update (fun _ => TestFun.ind Q) j φ

theorem blockTuple_singleton (Q : DyadicCube d) (f : Fin n → TestFun d) (j : Fin n) :
    blockTuple Q f {j} = oneTuple Q j (mdiff Q (f j)) := by
  funext i
  unfold blockTuple oneTuple
  by_cases h : i = j
  · subst h
    simp
  · rw [Function.update_of_ne h]
    simp [h]

/-- The coefficients `g_Q(ε) = Λ(𝟙_Q, …, 𝟙_{Q_ε}, …, 𝟙_Q)` (slot `j`). -/
noncomputable def coefChild (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d)
    (ε : Fin d → Bool) : ℝ :=
  T.form (oneTuple Q j (TestFun.ind (Q.child ε)))

/-- The mean `[g_Q] = 2^{-d} ∑_ε g_Q(ε)`. -/
noncomputable def coefMean (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d) : ℝ :=
  (2 ^ d)⁻¹ * ∑ ε : Fin d → Bool, coefChild T j Q ε

/-- The centered coefficients `v_Q(ε) = g_Q(ε) − [g_Q]`. -/
noncomputable def coefV (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d)
    (ε : Fin d → Bool) : ℝ :=
  coefChild T j Q ε - coefMean T j Q

/-- The Carleson sequence `β_Q = √(2^d) ‖v_Q‖ / |Q|`. -/
noncomputable def carl (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d) : ℝ :=
  Real.sqrt (2 ^ d) * Real.sqrt (∑ ε : Fin d → Bool, coefV T j Q ε ^ 2) / Q.vol

/-- The test function `ψ_Q = |Q|⁻¹ ∑_ε v_Q(ε) 𝟙_{Q_ε}`. -/
noncomputable def psi (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d) : TestFun d :=
  ∑ ε : Fin d → Bool, (Q.vol⁻¹ * coefV T j Q ε) • TestFun.ind (Q.child ε)

theorem card_children : (Finset.univ : Finset (Fin d → Bool)).card = 2 ^ d := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem sum_coefV (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d) :
    ∑ ε : Fin d → Bool, coefV T j Q ε = 0 := by
  unfold coefV coefMean
  rw [Finset.sum_sub_distrib, Finset.sum_const, card_children, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, sub_self]

theorem vol_child_eq (Q : DyadicCube d) (ε : Fin d → Bool) : (Q.child ε).vol = Q.vol / 2 ^ d := by
  rw [eq_div_iff (by positivity)]
  exact Q.vol_child ε

theorem psi_supportedOn (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d) :
    SupportedOn (psi T j Q : (Fin d → ℝ) → ℝ) Q := by
  intro x hx
  simp only [psi, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    TestFun.coe_ind, smul_eq_mul]
  exact Finset.sum_eq_zero fun ε _ => by
    rw [Set.indicator_of_notMem (fun h => hx (Q.child_subset ε h)), mul_zero]

theorem psi_meanZero (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d) :
    MeanZero (psi T j Q : (Fin d → ℝ) → ℝ) := by
  change ∫ x, (psi T j Q : (Fin d → ℝ) → ℝ) x = 0
  rw [← TestFun.integralₗ_apply, psi, map_sum]
  have e : ∀ ε : Fin d → Bool,
      TestFun.integralₗ ((Q.vol⁻¹ * coefV T j Q ε) • TestFun.ind (Q.child ε)) =
        (Q.vol⁻¹ * (Q.vol / 2 ^ d)) * coefV T j Q ε := fun ε => by
    rw [map_smul, smul_eq_mul, TestFun.integralₗ_apply, TestFun.integral_ind, vol_child_eq]
    ring
  rw [Finset.sum_congr rfl fun ε _ => e ε, ← Finset.mul_sum, sum_coefV, mul_zero]

theorem psi_constOn_child (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d)
    (ε : Fin d → Bool) : ConstOn (psi T j Q : (Fin d → ℝ) → ℝ) (Q.child ε) := by
  unfold psi
  refine StoppingData.constOn_sum fun ε' _ => StoppingData.constOn_smul _ (constOn_ind ?_)
  exact DyadicCube.subset_or_disjoint _ _ le_rfl

/-- Linearity of the form in the slot `j` on sums of children indicators. [PROVED] -/
theorem form_oneTuple_smul_sum (T : PerfectCZForm d n) (Q : DyadicCube d) (j : Fin n)
    (a : (Fin d → Bool) → ℝ) :
    T.form (oneTuple Q j (∑ ε : Fin d → Bool, a ε • TestFun.ind (Q.child ε))) =
      ∑ ε : Fin d → Bool, a ε * coefChild T j Q ε := by
  unfold coefChild oneTuple
  rw [MultilinearMap.map_update_sum]
  exact Finset.sum_congr rfl fun ε _ => by rw [MultilinearMap.map_update_smul, smul_eq_mul]

/-- **The coefficients are intrinsic**: `Λ(𝟙_P, …, φ, …, 𝟙_P) = Λ(𝟙_Q, …, φ, …, 𝟙_Q)` for `Q ⊆ P`
and
`φ` supported on `Q` with mean zero (perfect smoothness). [PROVED] -/
theorem form_oneTuple_eq_of_subset (T : PerfectCZForm d n) (j : Fin n) {Q P : DyadicCube d}
    (hQP : Q.toSet ⊆ P.toSet) {φ : TestFun d} (hφs : SupportedOn (φ : (Fin d → ℝ) → ℝ) Q)
    (hφ0 : MeanZero (φ : (Fin d → ℝ) → ℝ)) :
    T.form (oneTuple P j φ) = T.form (oneTuple Q j φ) := by
  symm
  refine form_eq_of_vanishesOn T (j₀ := j) (Q := Q) ?_ ?_ ?_ ?_
  · simp only [oneTuple, Function.update_self]
    exact hφs
  · simp only [oneTuple, Function.update_self]
    exact hφ0
  · simp only [oneTuple, Function.update_self]
  · intro i hi
    change ∀ x ∈ Q.toSet,
      ((oneTuple Q j φ i - oneTuple P j φ i : TestFun d) : (Fin d → ℝ) → ℝ) x = 0
    intro x hx
    rw [oneTuple, oneTuple, Function.update_of_ne hi, Function.update_of_ne hi]
    change ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x -
      ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) x = 0
    rw [TestFun.coe_ind, TestFun.coe_ind, Set.indicator_of_mem hx, Set.indicator_of_mem (hQP hx),
      sub_self]

/-- **The testing condition in the slot `j`**: `|Λ(𝟙_P, …, φ, …, 𝟙_P)| ≤ B |P|^{1-1/p_j} ‖φ‖_{p_j}`
for `φ` supported on `P`. [PROVED] -/
theorem abs_form_oneTuple_le {T : PerfectCZForm d n} {p : HolderTuple n} {B : ℝ}
    (hT : T1Testing T p B) (j : Fin n) (P : DyadicCube d) (φ : TestFun d)
    (hφ : SupportedOn (φ : (Fin d → ℝ) → ℝ) P) :
    |T.form (oneTuple P j φ)| ≤ B * P.vol ^ (1 - 1 / p.p j) * lpNorm (φ : (Fin d → ℝ) → ℝ) (p.p j)
      := by
  have h := hT P j (oneTuple P j φ)
    (fun i hi => by
      simp only [oneTuple, Function.update_of_ne hi]
      rfl)
    (by
      simp only [oneTuple, Function.update_self]
      exact hφ)
  rw [oneTuple, prodNorm_update] at h
  have hsum : ∑ i ∈ Finset.univ.erase j, 1 / p.p i = 1 - 1 / p.p j := by
    have := Finset.add_sum_erase Finset.univ (fun i => 1 / p.p i) (Finset.mem_univ j)
    rw [p.sum_one_div] at this
    linarith
  have hprod : ∏ i ∈ Finset.univ.erase j,
      lpNorm ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) (p.p i) = P.vol ^ (1 - 1 / p.p j) := by
    rw [Finset.prod_congr rfl fun i _ => TestFun.lpNorm_ind P (by linarith [p.one_lt i]),
      ← Real.rpow_sum_of_pos P.vol_pos, hsum]
  rw [hprod] at h
  calc |T.form (oneTuple P j φ)|
      ≤ B * (lpNorm (φ : (Fin d → ℝ) → ℝ) (p.p j) * P.vol ^ (1 - 1 / p.p j)) := h
    _ = _ := by ring

/-- **Orthogonality**: two blocks at distinct cubes, each supported on its cube with mean zero
and constant on the children of its cube, are orthogonal. [PROVED] -/
theorem integral_mul_eq_zero_of_ne {Q Q' : DyadicCube d} (hne : Q ≠ Q') {ψ ψ' : TestFun d}
    (hs : SupportedOn (ψ : (Fin d → ℝ) → ℝ) Q) (hs' : SupportedOn (ψ' : (Fin d → ℝ) → ℝ) Q')
    (h0 : MeanZero (ψ : (Fin d → ℝ) → ℝ)) (h0' : MeanZero (ψ' : (Fin d → ℝ) → ℝ))
    (hc : ∀ ε, ConstOn (ψ : (Fin d → ℝ) → ℝ) (Q.child ε))
    (hc' : ∀ ε, ConstOn (ψ' : (Fin d → ℝ) → ℝ) (Q'.child ε)) :
    ∫ x, (ψ : (Fin d → ℝ) → ℝ) x * (ψ' : (Fin d → ℝ) → ℝ) x = 0 := by
  -- the nested case: `Q' ⊊ Q`
  have key : ∀ {Q Q' : DyadicCube d} {ψ ψ' : TestFun d}, Q' ≠ Q → Q'.toSet ⊆ Q.toSet →
      Q'.m ≤ Q.m → SupportedOn (ψ' : (Fin d → ℝ) → ℝ) Q' → MeanZero (ψ' : (Fin d → ℝ) → ℝ) →
      (∀ ε, ConstOn (ψ : (Fin d → ℝ) → ℝ) (Q.child ε)) →
      ∫ x, (ψ : (Fin d → ℝ) → ℝ) x * (ψ' : (Fin d → ℝ) → ℝ) x = 0 := by
    intro Q Q' ψ ψ' hne hsub hm hs' h0' hc
    have hlt : Q'.m < Q.m :=
      lt_of_le_of_ne hm fun h => hne (DyadicCube.eq_of_subset_of_m_eq hsub h)
    have hx0 : (fun i => (2 : ℝ) ^ Q'.m * Q'.l i) ∈ Q.toSet := hsub Q'.corner_mem
    obtain ⟨ε₀, hε₀⟩ : ∃ ε₀, Q'.toSet ⊆ (Q.child ε₀).toSet := by
      obtain ⟨L, hL, hxL⟩ := StoppingData.exists_mem_level 1 hx0
      rw [level_one] at hL
      obtain ⟨ε₀, rfl⟩ := StoppingData.mem_children.mp hL
      refine ⟨ε₀, ?_⟩
      rcases DyadicCube.subset_or_disjoint Q' (Q.child ε₀)
        (by change Q'.m ≤ Q.m - 1; omega) with h | h
      · exact h
      · exact absurd hxL (Set.disjoint_left.mp h Q'.corner_mem)
    have hconst : ConstOn (ψ : (Fin d → ℝ) → ℝ) Q' := Bridge.constOn_of_subset hε₀ (hc ε₀)
    have hx0' := Q'.corner_mem
    calc ∫ x, (ψ : (Fin d → ℝ) → ℝ) x * (ψ' : (Fin d → ℝ) → ℝ) x
        = ∫ x in Q'.toSet, (ψ : (Fin d → ℝ) → ℝ) x * (ψ' : (Fin d → ℝ) → ℝ) x :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            rw [hs' x hx, mul_zero]).symm
      _ = ∫ x in Q'.toSet, (ψ : (Fin d → ℝ) → ℝ) (fun i => (2 : ℝ) ^ Q'.m * Q'.l i) *
            (ψ' : (Fin d → ℝ) → ℝ) x :=
          setIntegral_congr_fun Q'.measurableSet_toSet fun x hx => by rw [hconst x hx _ hx0']
      _ = (ψ : (Fin d → ℝ) → ℝ) (fun i => (2 : ℝ) ^ Q'.m * Q'.l i) *
            ∫ x in Q'.toSet, (ψ' : (Fin d → ℝ) → ℝ) x := integral_const_mul _ _
      _ = 0 := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hs' x hx, h0', mul_zero]
  have hdisj : Disjoint Q.toSet Q'.toSet →
      ∫ x, (ψ : (Fin d → ℝ) → ℝ) x * (ψ' : (Fin d → ℝ) → ℝ) x = 0 := by
    intro hdis
    have hz : (fun x => (ψ : (Fin d → ℝ) → ℝ) x * (ψ' : (Fin d → ℝ) → ℝ) x) = fun _ => (0 : ℝ) :=
      funext fun x => by
        by_cases hx : x ∈ Q.toSet
        · rw [hs' x (Set.disjoint_left.mp hdis hx), mul_zero]
        · rw [hs x hx, zero_mul]
    rw [hz, integral_zero]
  rcases le_total Q'.m Q.m with hm | hm
  · rcases DyadicCube.subset_or_disjoint Q' Q hm with hsub | hdis
    · exact key hne.symm hsub hm hs' h0' hc
    · exact hdisj hdis.symm
  · rcases DyadicCube.subset_or_disjoint Q Q' hm with hsub | hdis
    · rw [← key hne hsub hm hs h0 hc']
      exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    · exact hdisj hdis

/-- **Pythagoras**: `∫ (∑_Q ψ_Q)² = ∑_Q ∫ ψ_Q²` for orthogonal blocks. [PROVED] -/
theorem integral_sq_sum_eq_sum {F : Finset (DyadicCube d)} (ψ : DyadicCube d → TestFun d)
    (hs : ∀ Q ∈ F, SupportedOn (ψ Q : (Fin d → ℝ) → ℝ) Q)
    (h0 : ∀ Q ∈ F, MeanZero (ψ Q : (Fin d → ℝ) → ℝ))
    (hc : ∀ Q ∈ F, ∀ ε, ConstOn (ψ Q : (Fin d → ℝ) → ℝ) (Q.child ε)) :
    ∫ x, ((∑ Q ∈ F, ψ Q : TestFun d) : (Fin d → ℝ) → ℝ) x ^ 2 =
      ∑ Q ∈ F, ∫ x, (ψ Q : (Fin d → ℝ) → ℝ) x ^ 2 := by
  have hint : ∀ Q Q' : DyadicCube d,
      Integrable (fun x => (ψ Q : (Fin d → ℝ) → ℝ) x * (ψ Q' : (Fin d → ℝ) → ℝ) x) volume :=
    fun Q Q' => (TestFun.memLp (ψ Q).2 2).integrable_mul (TestFun.memLp (ψ Q').2 2)
  have e : ∀ x, ((∑ Q ∈ F, ψ Q : TestFun d) : (Fin d → ℝ) → ℝ) x ^ 2 =
      ∑ Q ∈ F, ∑ Q' ∈ F, (ψ Q : (Fin d → ℝ) → ℝ) x * (ψ Q' : (Fin d → ℝ) → ℝ) x := by
    intro x
    rw [Submodule.coe_sum, Finset.sum_apply, sq, Finset.sum_mul_sum]
  rw [integral_congr_ae (ae_of_all _ e),
    integral_finsetSum _ fun Q _ => integrable_finsetSum _ fun Q' _ => hint Q Q']
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [integral_finsetSum _ fun Q' _ => hint Q Q', Finset.sum_eq_single Q]
  · exact integral_congr_ae (ae_of_all _ fun x => (sq _).symm)
  · intro Q' hQ' hne
    exact integral_mul_eq_zero_of_ne (Ne.symm hne) (hs Q hQ) (hs Q' hQ') (h0 Q hQ) (h0 Q' hQ')
      (hc Q hQ) (hc Q' hQ')
  · intro h
    exact absurd hQ h

/-- `∫ ψ_Q² = 2^{-d} |Q|⁻¹ ‖v_Q‖²`. [PROVED] -/
theorem integral_sq_psi (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d) :
    ∫ x, (psi T j Q : (Fin d → ℝ) → ℝ) x ^ 2 =
      (2 ^ d)⁻¹ * Q.vol⁻¹ * ∑ ε : Fin d → Bool, coefV T j Q ε ^ 2 := by
  have hpt : ∀ x, (psi T j Q : (Fin d → ℝ) → ℝ) x ^ 2 =
      ((∑ ε : Fin d → Bool, (Q.vol⁻¹ * coefV T j Q ε) ^ 2 • TestFun.ind (Q.child ε) : TestFun d) :
        (Fin d → ℝ) → ℝ) x := by
    intro x
    simp only [psi, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, TestFun.coe_ind]
    by_cases hx : x ∈ Q.toSet
    · obtain ⟨L, hL, hxL⟩ := StoppingData.exists_mem_level 1 hx
      rw [level_one] at hL
      obtain ⟨ε₀, rfl⟩ := StoppingData.mem_children.mp hL
      have hother : ∀ ε, ε ≠ ε₀ → (Q.child ε).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x = 0 :=
        fun ε hne => Set.indicator_of_notMem (Set.disjoint_right.mp (Q.child_disjoint hne) hxL) _
      rw [Finset.sum_eq_single ε₀ (fun ε _ hne => by rw [hother ε hne, mul_zero])
          (fun h => absurd (Finset.mem_univ ε₀) h),
        Finset.sum_eq_single ε₀ (fun ε _ hne => by rw [hother ε hne, mul_zero])
          (fun h => absurd (Finset.mem_univ ε₀) h),
        Set.indicator_of_mem hxL, Pi.one_apply, mul_one, mul_one]
    · have hall : ∀ ε : Fin d → Bool, (Q.child ε).toSet.indicator (1 : (Fin d → ℝ) → ℝ) x = 0 :=
        fun ε => Set.indicator_of_notMem (fun h => hx (Q.child_subset ε h)) _
      rw [Finset.sum_eq_zero (fun ε _ => by rw [hall ε, mul_zero]),
        Finset.sum_eq_zero (fun ε _ => by rw [hall ε, mul_zero]), zero_pow two_ne_zero]
  rw [integral_congr_ae (ae_of_all _ hpt), ← TestFun.integralₗ_apply, map_sum]
  have hV0 := Q.vol_pos.ne'
  have e : ∀ ε : Fin d → Bool,
      TestFun.integralₗ ((Q.vol⁻¹ * coefV T j Q ε) ^ 2 • TestFun.ind (Q.child ε)) =
        (2 ^ d)⁻¹ * Q.vol⁻¹ * coefV T j Q ε ^ 2 := fun ε => by
    rw [map_smul, smul_eq_mul, TestFun.integralₗ_apply, TestFun.integral_ind, vol_child_eq]
    calc (Q.vol⁻¹ * coefV T j Q ε) ^ 2 * (Q.vol / 2 ^ d)
        = (Q.vol⁻¹ * Q.vol) * ((2 ^ d)⁻¹ * Q.vol⁻¹ * coefV T j Q ε ^ 2) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hV0, one_mul]
  rw [Finset.sum_congr rfl fun ε _ => e ε, ← Finset.mul_sum]

theorem subset_of_mem_nonleaf {N : ℕ} {P Q : DyadicCube d} (hQ : Q ∈ StoppingData.nonleaf N P) :
    Q.toSet ⊆ P.toSet := by
  rw [StoppingData.nonleaf, Finset.mem_biUnion] at hQ
  obtain ⟨L, -, hL⟩ := hQ
  exact StoppingData.subset_of_mem_level hL

/-- **Below the resolution of the form the Carleson sequence vanishes**: for `ℓ(Q) ≤ 2^s` the
coefficients `g_Q(ε)` do not depend on `ε`. [PROVED] -/
theorem carl_eq_zero_of_le {T : PerfectCZForm d n} {s : ℤ} (hs : KernelScale T s) (j : Fin n)
    {Q : DyadicCube d} (hQ : Q.m ≤ s) : carl T j Q = 0 := by
  have hV0 := Q.vol_pos.ne'
  have hconst : ∀ ε, coefChild T j Q ε = (2 ^ d)⁻¹ * T.form (oneTuple Q j (TestFun.ind Q)) := by
    intro ε
    unfold coefChild oneTuple
    rw [hs (fun _ => TestFun.ind Q) j Q hQ (TestFun.ind (Q.child ε))
      (fun x hx => Set.indicator_of_notMem (fun h => hx (Q.child_subset ε h)) _)]
    congr 1
    rw [avg, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => TestFun.ind_supportedOn (Q.child ε) x (fun h => hx (Q.child_subset ε h))),
      TestFun.integral_ind, div_eq_iff hV0, ← Q.vol_child ε, mul_comm (Q.child ε).vol,
      ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hmean : coefMean T j Q = (2 ^ d)⁻¹ * T.form (oneTuple Q j (TestFun.ind Q)) := by
    unfold coefMean
    rw [Finset.sum_congr rfl fun ε _ => hconst ε, Finset.sum_const, card_children, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hv : ∀ ε, coefV T j Q ε = 0 := fun ε => by rw [coefV, hconst, hmean, sub_self]
  unfold carl
  simp only [hv, zero_pow two_ne_zero, Finset.sum_const_zero, Real.sqrt_zero, mul_zero, zero_div]

/-- `∑_ε [f]_{Q_ε} = 2^d [f]_Q`. [PROVED] -/
theorem sum_avg_children (Q : DyadicCube d) (f : TestFun d) :
    ∑ ε : Fin d → Bool, avg (Q.child ε) (f : (Fin d → ℝ) → ℝ) = 2 ^ d * avg Q (f : (Fin d → ℝ) → ℝ)
      := by
  have h := Q.integral_children (TestFun.integrable f.2).integrableOn
  have e : ∀ ε : Fin d → Bool, avg (Q.child ε) (f : (Fin d → ℝ) → ℝ) =
      2 ^ d * (∫ x in (Q.child ε).toSet, (f : (Fin d → ℝ) → ℝ) x) / Q.vol := fun ε => by
    rw [avg, vol_child_eq, div_div_eq_mul_div]
    ring
  rw [Finset.sum_congr rfl fun ε _ => e ε, ← Finset.sum_div, ← Finset.mul_sum, ← h, avg,
    mul_div_assoc]

/-- `Δ_Q f = ∑_ε ([f]_{Q_ε} − [f]_Q) 𝟙_{Q_ε}`. [PROVED] -/
theorem mdiff_eq_sum_children (Q : DyadicCube d) (f : TestFun d) :
    mdiff Q f = ∑ ε : Fin d → Bool,
      (avg (Q.child ε) (f : (Fin d → ℝ) → ℝ) - avg Q (f : (Fin d → ℝ) → ℝ)) • TestFun.ind (Q.child
        ε) := by
  rw [mdiff_eq]
  have hind : TestFun.ind Q = ∑ ε : Fin d → Bool, TestFun.ind (Q.child ε) := by
    have h := eq_sum_children_of_constOn (TestFun.ind_supportedOn Q)
      (fun ε => constOn_ind (Or.inl (Q.child_subset ε)))
    rw [Finset.sum_congr rfl fun ε _ => by
      rw [StoppingData.avg_ind_of_subset (Q.child_subset ε), one_smul]] at h
    exact h
  rw [hind, Finset.smul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ε _ => (sub_smul _ _ _).symm

/-- **The per-cube Cauchy–Schwarz bound**: `|Λ(𝟙_Q, …, Δ_Q f_j, …, 𝟙_Q)| ≤ |Q| Δ_Q f_j β_Q`.
[PROVED] -/
theorem abs_form_blockTuple_single_le (T : PerfectCZForm d n) (Q : DyadicCube d)
    (f : Fin n → TestFun d) (j : Fin n) :
    |T.form (blockTuple Q f {j})| ≤ Q.vol * martDiff Q (f j : (Fin d → ℝ) → ℝ) * carl T j Q := by
  have hV0 := Q.vol_pos.ne'
  rw [blockTuple_singleton, mdiff_eq_sum_children, form_oneTuple_smul_sum]
  obtain ⟨c, hc⟩ : ∃ c : (Fin d → Bool) → ℝ, c = fun ε =>
      avg (Q.child ε) (f j : (Fin d → ℝ) → ℝ) - avg Q (f j : (Fin d → ℝ) → ℝ) := ⟨_, rfl⟩
  have hc' : ∀ ε, avg (Q.child ε) (f j : (Fin d → ℝ) → ℝ) - avg Q (f j : (Fin d → ℝ) → ℝ) = c ε :=
    fun ε => by rw [hc]
  simp only [hc']
  have hc0 : ∑ ε, c ε = 0 := by
    simp only [hc]
    rw [Finset.sum_sub_distrib, sum_avg_children, Finset.sum_const, card_children, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, sub_self]
  have e : ∑ ε, c ε * coefChild T j Q ε = ∑ ε, c ε * coefV T j Q ε := by
    have h : ∀ ε, c ε * coefChild T j Q ε = c ε * coefV T j Q ε + coefMean T j Q * c ε := by
      intro ε
      unfold coefV
      ring
    rw [Finset.sum_congr rfl fun ε _ => h ε, Finset.sum_add_distrib, ← Finset.mul_sum, hc0,
      mul_zero, add_zero]
  rw [e]
  have hCS : (∑ ε, c ε * coefV T j Q ε) ^ 2 ≤
      (∑ ε, c ε ^ 2) * ∑ ε, coefV T j Q ε ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsumc : ∑ ε, c ε ^ 2 = 2 ^ d * martDiff Q (f j : (Fin d → ℝ) → ℝ) ^ 2 := by
    rw [martDiff_eq_sqrt, Real.sq_sqrt (by positivity), ← mul_assoc, mul_inv_cancel₀ (by
      positivity),
      one_mul]
    exact Finset.sum_congr rfl fun ε _ => by simp only [hc, sq_abs]
  calc |∑ ε, c ε * coefV T j Q ε|
      ≤ Real.sqrt ((∑ ε, c ε ^ 2) * ∑ ε, coefV T j Q ε ^ 2) := Real.abs_le_sqrt hCS
    _ = Q.vol * martDiff Q (f j : (Fin d → ℝ) → ℝ) * carl T j Q := by
        rw [hsumc, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (martDiff_nonneg _ _), carl, mul_div_assoc', eq_div_iff hV0]
        ring

theorem carl_nonneg (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d) : 0 ≤ carl T j Q :=
  div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) Q.vol_pos.le

/-! ### The dyadic John–Nirenberg inequality

For exponents `p_j > 2` the testing condition only gives the dual `L^{p_j'}`-BMO condition on the
symbol `ψ = ∑_Q ψ_Q` of the paraproduct (`p_j' < 2`), while the Carleson condition is its
`L²`-BMO condition. The two are equivalent by the dyadic John–Nirenberg inequality, which we prove
by a stopping-time bootstrap: for a test function `b` constant below the scale `m₀` and satisfying
the dual `L^1`-BMO condition `|∫ b φ| ≤ K M |Q|` for all admissible `φ` with `|φ| ≤ M`, the maximal
cubes `Q ⊆ P` with `|[b]_Q − [b]_P| > 8K` cover at most a quarter of `P`, their averages satisfy
`|[b]_Q − [b]_P| ≤ (8 + 2^d) K`, and the inductive bound on the stopping cubes gives
`∫_P |b − [b]_P|² ≤ (128 + (8 + 2^d)²) K² |P|`. -/

/-- `∫ g 𝟙_Q = ∫_Q g`. [PROVED] -/
theorem integral_mul_ind (g : (Fin d → ℝ) → ℝ) (Q : DyadicCube d) :
    ∫ x, g x * ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x = ∫ x in Q.toSet, g x := by
  rw [← integral_indicator Q.measurableSet_toSet]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change g x * ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x = Q.toSet.indicator g x
  rw [TestFun.coe_ind]
  by_cases hx : x ∈ Q.toSet
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

/-- `(f − c)²` is integrable on every cube for a dyadic test function `f`. [PROVED] -/
theorem TestFun.integrableOn_sq_sub {f : (Fin d → ℝ) → ℝ} (hf : f ∈ TestFun d) (c : ℝ)
    (Q : DyadicCube d) : IntegrableOn (fun x => (f x - c) ^ 2) Q.toSet volume := by
  have e : (fun x => (f x - c) ^ 2) = fun x => (f x ^ 2 - (2 * c) * f x) + c ^ 2 := by
    funext x
    ring
  rw [e]
  refine IntegrableOn.add (IntegrableOn.sub ?_ ?_) ?_
  · exact (TestFun.memLp hf 2).integrable_sq.integrableOn
  · exact ((TestFun.integrable hf).const_mul _).integrableOn
  · exact integrableOn_const (by rw [Q.volume_toSet]; exact ENNReal.ofReal_ne_top)

/-- `∫_P (f − [f]_P)² = 0` for `f` constant on `P`. [PROVED] -/
theorem setIntegral_sq_sub_avg_eq_zero {f : (Fin d → ℝ) → ℝ} {P : DyadicCube d}
    (hf : ConstOn f P) : ∫ x in P.toSet, (f x - avg P f) ^ 2 = 0 := by
  rw [setIntegral_congr_fun P.measurableSet_toSet (g := fun _ => (0 : ℝ))
    (fun x hx => by rw [avg_eq_of_constOn hf hx, sub_self, zero_pow two_ne_zero])]
  simp

/-- `|∑_Q c_Q 𝟙_Q(x)| ≤ 1` for pairwise disjoint cubes and `|c_Q| ≤ 1`. [PROVED] -/
theorem abs_sum_mul_ind_apply_le {S : Finset (DyadicCube d)}
    (hdisj : ∀ Q ∈ S, ∀ R ∈ S, Q ≠ R → Disjoint Q.toSet R.toSet) {c : DyadicCube d → ℝ}
    (hc : ∀ Q ∈ S, |c Q| ≤ 1) (x : Fin d → ℝ) :
    |∑ Q ∈ S, c Q * ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x| ≤ 1 := by
  by_cases hx : ∃ Q ∈ S, x ∈ Q.toSet
  · obtain ⟨Q₀, hQ₀, hxQ₀⟩ := hx
    rw [Finset.sum_eq_single Q₀]
    · rw [TestFun.coe_ind, Set.indicator_of_mem hxQ₀, Pi.one_apply, mul_one]
      exact hc Q₀ hQ₀
    · intro Q hQ hne
      rw [TestFun.coe_ind, Set.indicator_of_notMem (Set.disjoint_right.mp (hdisj Q hQ Q₀ hQ₀ hne)
        hxQ₀),
        mul_zero]
    · intro h
      exact absurd hQ₀ h
  · rw [Finset.sum_eq_zero fun Q hQ => by
      rw [TestFun.coe_ind, Set.indicator_of_notMem fun h => hx ⟨Q, hQ, h⟩, mul_zero], abs_zero]
    exact zero_le_one

/-- Pairwise disjoint subcubes of `P` have total measure at most `|P|`. [PROVED] -/
theorem sum_vol_le_of_disjoint {S : Finset (DyadicCube d)} {P : DyadicCube d}
    (hsub : ∀ Q ∈ S, Q.toSet ⊆ P.toSet)
    (hdisj : ∀ Q ∈ S, ∀ R ∈ S, Q ≠ R → Disjoint Q.toSet R.toSet) :
    ∑ Q ∈ S, Q.vol ≤ P.vol := by
  have e : ∑ Q ∈ S, Q.vol = ∫ x, ((∑ Q ∈ S, TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x := by
    rw [← TestFun.integralₗ_apply, map_sum]
    exact Finset.sum_congr rfl fun Q _ => (TestFun.integral_ind Q).symm
  rw [e, ← TestFun.integral_ind P]
  refine integral_mono (TestFun.integrable (∑ Q ∈ S, TestFun.ind Q : TestFun d).2)
    (TestFun.integrable (TestFun.ind P).2) fun x => ?_
  simp only [Submodule.coe_sum, Finset.sum_apply]
  by_cases hxP : x ∈ P.toSet
  · rw [TestFun.coe_ind P, Set.indicator_of_mem hxP, Pi.one_apply]
    have := abs_sum_mul_ind_apply_le hdisj (c := fun _ => 1) (fun Q _ => by simp) x
    simp only [one_mul] at this
    exact (le_abs_self _).trans this
  · rw [TestFun.coe_ind P, Set.indicator_of_notMem hxP]
    exact le_of_eq (Finset.sum_eq_zero fun Q hQ => by
      rw [TestFun.coe_ind, Set.indicator_of_notMem fun h => hxP (hsub Q hQ h)])

/-- **The dual `L^1`-BMO condition** on `P` at the resolution `m₀`: `|∫ b φ| ≤ K M |Q|` for every
cube `Q ⊆ P` of scale `≥ m₀` and every test function `φ` supported on `Q` with mean zero, constant
on the cubes of scale `≤ m₀` and bounded by `M`. -/
def JNDual (b : (Fin d → ℝ) → ℝ) (m₀ : ℤ) (K : ℝ) (P : DyadicCube d) : Prop :=
  ∀ Q : DyadicCube d, Q.toSet ⊆ P.toSet → m₀ ≤ Q.m → ∀ φ : TestFun d,
    SupportedOn (φ : (Fin d → ℝ) → ℝ) Q → MeanZero (φ : (Fin d → ℝ) → ℝ) →
    (∀ L : DyadicCube d, L.m ≤ m₀ → ConstOn (φ : (Fin d → ℝ) → ℝ) L) →
    ∀ M : ℝ, 0 ≤ M → (∀ x, |(φ : (Fin d → ℝ) → ℝ) x| ≤ M) →
    |∫ x, b x * (φ : (Fin d → ℝ) → ℝ) x| ≤ K * M * Q.vol

theorem JNDual.mono {b : (Fin d → ℝ) → ℝ} {m₀ : ℤ} {K : ℝ} {P Q : DyadicCube d}
    (h : JNDual b m₀ K P) (hQP : Q.toSet ⊆ P.toSet) : JNDual b m₀ K Q :=
  fun R hR hm => h R (hR.trans hQP) hm

/-- The John–Nirenberg constant `128 + (8 + 2^d)²`. -/
noncomputable def jnC (d : ℕ) : ℝ := 128 + (8 + 2 ^ d) ^ 2

theorem jnC_pos (d : ℕ) : 0 < jnC d := by
  unfold jnC
  positivity

/-- **One step of the stopping time**: `|[b]_Q − [b]_{Q̂}| ≤ 2^d K` under the dual condition,
tested against `φ = 𝟙_Q − 2^{-d} 𝟙_{Q̂}`. [PROVED] -/
theorem abs_avg_sub_avg_parent_le {b : (Fin d → ℝ) → ℝ} (hb : b ∈ TestFun d) {m₀ : ℤ} {K : ℝ}
    {P Q : DyadicCube d} (hdual : JNDual b m₀ K P) (hQP : Q.parent.toSet ⊆ P.toSet)
    (hm : m₀ ≤ Q.m) : |avg Q b - avg Q.parent b| ≤ 2 ^ d * K := by
  have hV := Q.vol_pos
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  obtain ⟨φ, hφ⟩ : ∃ φ : TestFun d,
      φ = TestFun.ind Q - ((2 : ℝ) ^ d)⁻¹ • TestFun.ind Q.parent := ⟨_, rfl⟩
  have hφx : ∀ x, (φ : (Fin d → ℝ) → ℝ) x =
      Q.toSet.indicator 1 x - (2 ^ d)⁻¹ * Q.parent.toSet.indicator 1 x := by
    intro x
    simp only [hφ, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
      TestFun.coe_ind, smul_eq_mul]
  have hsupp : SupportedOn (φ : (Fin d → ℝ) → ℝ) Q.parent := by
    intro x hx
    rw [hφx, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (Q.subset_parent h)),
      mul_zero, sub_zero]
  have hmean : MeanZero (φ : (Fin d → ℝ) → ℝ) := by
    change ∫ x, (φ : (Fin d → ℝ) → ℝ) x = 0
    rw [← TestFun.integralₗ_apply, hφ, map_sub, map_smul, TestFun.integralₗ_apply,
      TestFun.integralₗ_apply, TestFun.integral_ind, TestFun.integral_ind, smul_eq_mul,
        Q.vol_parent,
      ← mul_assoc, inv_mul_cancel₀ h2d.ne', one_mul, sub_self]
  have hconst : ∀ L : DyadicCube d, L.m ≤ m₀ → ConstOn (φ : (Fin d → ℝ) → ℝ) L := by
    intro L hL
    rw [hφ]
    refine StoppingData.constOn_sub (constOn_ind ?_) (StoppingData.constOn_smul _ (constOn_ind ?_))
    · exact DyadicCube.subset_or_disjoint L Q (by omega)
    · exact DyadicCube.subset_or_disjoint L Q.parent (by rw [DyadicCube.parent_m]; omega)
  have hbound : ∀ x, |(φ : (Fin d → ℝ) → ℝ) x| ≤ 1 := by
    intro x
    rw [hφx]
    have h2 : (0 : ℝ) < (2 ^ d)⁻¹ := by positivity
    have h2' : ((2 : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    by_cases hxQ : x ∈ Q.toSet
    · rw [Set.indicator_of_mem hxQ, Set.indicator_of_mem (Q.subset_parent hxQ), Pi.one_apply,
        mul_one, abs_le]
      constructor <;> linarith
    · rw [Set.indicator_of_notMem hxQ, zero_sub, abs_neg]
      by_cases hxP : x ∈ Q.parent.toSet
      · rw [Set.indicator_of_mem hxP, Pi.one_apply, mul_one, abs_of_pos h2]
        exact h2'
      · rw [Set.indicator_of_notMem hxP, mul_zero, abs_zero]
        exact zero_le_one
  have hint : ∫ x, b x * (φ : (Fin d → ℝ) → ℝ) x = Q.vol * (avg Q b - avg Q.parent b) := by
    have e : ∀ x, b x * (φ : (Fin d → ℝ) → ℝ) x =
        b x * ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x -
          (2 ^ d)⁻¹ * (b x * ((TestFun.ind Q.parent : TestFun d) : (Fin d → ℝ) → ℝ) x) := by
      intro x
      rw [hφx, TestFun.coe_ind, TestFun.coe_ind]
      ring
    have hint : ∀ R : DyadicCube d,
        Integrable (fun x => b x * ((TestFun.ind R : TestFun d) : (Fin d → ℝ) → ℝ) x) volume :=
      fun R => (TestFun.memLp hb 2).integrable_mul (TestFun.memLp (TestFun.ind R).2 2)
    rw [integral_congr_ae (ae_of_all _ e), integral_sub (hint Q) ((hint Q.parent).const_mul _),
      integral_const_mul, integral_mul_ind, integral_mul_ind, ← avg_mul_vol, ← avg_mul_vol,
      Q.vol_parent]
    calc avg Q b * Q.vol - (2 ^ d)⁻¹ * (avg Q.parent b * (2 ^ d * Q.vol))
        = avg Q b * Q.vol - ((2 ^ d)⁻¹ * 2 ^ d) * (avg Q.parent b * Q.vol) := by ring
      _ = Q.vol * (avg Q b - avg Q.parent b) := by
        rw [inv_mul_cancel₀ h2d.ne', one_mul]
        ring
  have h := hdual Q.parent hQP (by rw [DyadicCube.parent_m]; omega) φ hsupp hmean hconst 1
    zero_le_one hbound
  rw [hint, abs_mul, abs_of_pos hV, mul_one, Q.vol_parent] at h
  have h' : Q.vol * |avg Q b - avg Q.parent b| ≤ Q.vol * (2 ^ d * K) := by linarith
  exact le_of_mul_le_mul_left h' hV

/-- Maximal bad cubes occupy at most one quarter of their parent under the dual BMO bound. -/
private theorem jn_stopping_volume {b : (Fin d → ℝ) → ℝ} (hb : b ∈ TestFun d)
    {m₀ : ℤ} {K : ℝ} (hK : 0 < K) {P : DyadicCube d} (hPm : m₀ < P.m)
    (hdual : JNDual b m₀ K P) (stop : Finset (DyadicCube d))
    (stop_sub : ∀ Q ∈ stop, Q.toSet ⊆ P.toSet)
    (stop_disj : ∀ Q ∈ stop, ∀ R ∈ stop, Q ≠ R → Disjoint Q.toSet R.toSet)
    (stop_m : ∀ Q ∈ stop, m₀ ≤ Q.m) {lam : ℝ} (hlam : lam = 8 * K)
    (stop_bad : ∀ Q ∈ stop, lam < |avg Q b - avg P b|) :
    ∑ Q ∈ stop, Q.vol ≤ P.vol / 4 := by
  have hV := P.vol_pos
  have stop_vol_le := sum_vol_le_of_disjoint stop_sub stop_disj
  obtain ⟨c, hc⟩ : ∃ c : DyadicCube d → ℝ, c = fun Q =>
    if 0 ≤ (∫ x in Q.toSet, b x) - avg P b * Q.vol then 1 else -1 := ⟨_, rfl⟩
  have hc1 : ∀ Q, |c Q| ≤ 1 := by
    intro Q
    rw [hc]
    dsimp only
    split_ifs <;> simp
  have hcI : ∀ Q, c Q * ((∫ x in Q.toSet, b x) - avg P b * Q.vol) =
      |(∫ x in Q.toSet, b x) - avg P b * Q.vol| := by
    intro Q
    rw [hc]
    dsimp only
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (not_le.mp h)]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (∑ Q ∈ stop, c Q * Q.vol) / P.vol := ⟨_, rfl⟩
  have hs1 : |s| ≤ 1 := by
    rw [hs, abs_div, abs_of_pos hV, div_le_one hV]
    calc |∑ Q ∈ stop, c Q * Q.vol| ≤ ∑ Q ∈ stop, |c Q * Q.vol| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ Q ∈ stop, Q.vol := Finset.sum_le_sum fun Q _ => by
          rw [abs_mul, abs_of_pos Q.vol_pos]
          exact mul_le_of_le_one_left Q.vol_pos.le (hc1 Q)
      _ ≤ P.vol := stop_vol_le
  obtain ⟨φ, hφ⟩ : ∃ φ : TestFun d,
      φ = (∑ Q ∈ stop, c Q • TestFun.ind Q) - s • TestFun.ind P := ⟨_, rfl⟩
  have hφx : ∀ x, (φ : (Fin d → ℝ) → ℝ) x =
      (∑ Q ∈ stop, c Q * ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x) -
        s * ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) x := by
    intro x
    simp only [hφ, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsupp : SupportedOn (φ : (Fin d → ℝ) → ℝ) P := by
    intro x hx
    rw [hφx, TestFun.coe_ind P, Set.indicator_of_notMem hx, mul_zero, sub_zero]
    exact Finset.sum_eq_zero fun Q hQ => by
      rw [TestFun.coe_ind, Set.indicator_of_notMem fun h => hx (stop_sub Q hQ h), mul_zero]
  have hmean : MeanZero (φ : (Fin d → ℝ) → ℝ) := by
    change ∫ x, (φ : (Fin d → ℝ) → ℝ) x = 0
    rw [← TestFun.integralₗ_apply, hφ, map_sub, map_sum, map_smul, TestFun.integralₗ_apply,
      TestFun.integral_ind, smul_eq_mul]
    have e : ∀ Q ∈ stop, TestFun.integralₗ (c Q • TestFun.ind Q) = c Q * Q.vol := fun Q _ => by
      rw [map_smul, smul_eq_mul, TestFun.integralₗ_apply, TestFun.integral_ind]
    rw [Finset.sum_congr rfl e, hs, div_mul_cancel₀ _ hV.ne', sub_self]
  have hconst' : ∀ L : DyadicCube d, L.m ≤ m₀ → ConstOn (φ : (Fin d → ℝ) → ℝ) L := by
    intro L hL
    rw [hφ]
    refine StoppingData.constOn_sub
      (StoppingData.constOn_sum fun Q hQ => StoppingData.constOn_smul _ (constOn_ind ?_))
      (StoppingData.constOn_smul _ (constOn_ind ?_))
    · exact DyadicCube.subset_or_disjoint L Q (by have := stop_m Q hQ; omega)
    · exact DyadicCube.subset_or_disjoint L P (by omega)
  have hbound : ∀ x, |(φ : (Fin d → ℝ) → ℝ) x| ≤ 2 := by
    intro x
    rw [hφx]
    have h1 := abs_sum_mul_ind_apply_le stop_disj (fun Q _ => hc1 Q) x
    have h2 : |s * ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) x| ≤ 1 := by
      rw [abs_mul, TestFun.coe_ind]
      by_cases hx : x ∈ P.toSet
      · rw [Set.indicator_of_mem hx, Pi.one_apply, abs_one, mul_one]
        exact hs1
      · rw [Set.indicator_of_notMem hx, abs_zero, mul_zero]
        exact zero_le_one
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- the pairing with `φ` is `∑_Q |∫_Q (b − [b]_P)|`
  have hpair : ∫ x, b x * (φ : (Fin d → ℝ) → ℝ) x =
      ∑ Q ∈ stop, |(∫ x in Q.toSet, b x) - avg P b * Q.vol| := by
    have e : ∀ x, b x * (φ : (Fin d → ℝ) → ℝ) x =
        (∑ Q ∈ stop, c Q * (b x * ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x)) -
          s * (b x * ((TestFun.ind P : TestFun d) : (Fin d → ℝ) → ℝ) x) := by
      intro x
      rw [hφx, mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun Q _ => by ring
      · ring
    have hint : ∀ Q : DyadicCube d,
        Integrable (fun x => b x * ((TestFun.ind Q : TestFun d) : (Fin d → ℝ) → ℝ) x) volume :=
      fun Q => (TestFun.memLp hb 2).integrable_mul (TestFun.memLp (TestFun.ind Q).2 2)
    rw [integral_congr_ae (ae_of_all _ e),
      integral_sub (integrable_finsetSum _ fun Q _ => (hint Q).const_mul _) ((hint P).const_mul _),
      integral_finsetSum _ fun Q _ => (hint Q).const_mul _]
    simp only [integral_const_mul, integral_mul_ind]
    rw [← avg_mul_vol P b]
    have e2 : s * (avg P b * P.vol) = ∑ Q ∈ stop, c Q * (avg P b * Q.vol) := by
      calc s * (avg P b * P.vol)
          = (∑ Q ∈ stop, c Q * Q.vol) * avg P b * (P.vol / P.vol) := by rw [hs]; ring
        _ = ∑ Q ∈ stop, c Q * (avg P b * Q.vol) := by
          rw [div_self hV.ne', mul_one, Finset.sum_mul]
          exact Finset.sum_congr rfl fun Q _ => by ring
    rw [e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun Q _ => by rw [← mul_sub, hcI]
  have hdualφ := hdual P subset_rfl hPm.le φ hsupp hmean hconst' 2 (by norm_num) hbound
  rw [hpair] at hdualφ
  have hlow : lam * ∑ Q ∈ stop, Q.vol ≤ ∑ Q ∈ stop, |(∫ x in Q.toSet, b x) - avg P b * Q.vol| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun Q hQ => ?_
    have hbadQ := stop_bad Q hQ
    have hVQ := Q.vol_pos
    have e : avg Q b - avg P b = ((∫ x in Q.toSet, b x) - avg P b * Q.vol) / Q.vol := by
      simp only [avg]
      rw [sub_div, mul_div_cancel_right₀ _ hVQ.ne']
    rw [e, abs_div, abs_of_pos hVQ, lt_div_iff₀ hVQ] at hbadQ
    exact hbadQ.le
  have h4 : lam * ∑ Q ∈ stop, Q.vol ≤ K * 2 * P.vol :=
    hlow.trans ((le_abs_self _).trans hdualφ)
  rw [hlam] at h4
  have h5 : 8 * K * ∑ Q ∈ stop, Q.vol ≤ 8 * K * (P.vol / 4) := by linarith
  exact le_of_mul_le_mul_left h5 (by positivity)

/-- **The stopping-time step of John–Nirenberg**: if the bound holds on all proper subcubes of
`P`, it holds on `P`. [PROVED] -/
theorem jn_step (hd : d ≠ 0) {b : (Fin d → ℝ) → ℝ} (hb : b ∈ TestFun d) {m₀ : ℤ}
    (hconst : ∀ L : DyadicCube d, L.m ≤ m₀ → ConstOn b L) {K : ℝ} (hK : 0 < K)
    {P : DyadicCube d} (hPm : m₀ < P.m) (hdual : JNDual b m₀ K P)
    (ih : ∀ Q : DyadicCube d, Q.toSet ⊆ P.toSet → Q ≠ P →
      ∫ x in Q.toSet, (b x - avg Q b) ^ 2 ≤ jnC d * K ^ 2 * Q.vol) :
    ∫ x in P.toSet, (b x - avg P b) ^ 2 ≤ jnC d * K ^ 2 * P.vol := by
  classical
  have hV := P.vol_pos
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 8 * K := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = lam + 2 ^ d * K := ⟨_, rfl⟩
  -- the candidate cubes: the subcubes of `P` of scale `≥ m₀`
  obtain ⟨N', hN'⟩ : ∃ N' : ℕ, N' = (P.m - m₀).toNat := ⟨_, rfl⟩
  have hN'm : P.m - N' = m₀ := by omega
  obtain ⟨cand, hcand⟩ : ∃ C : Finset (DyadicCube d), C = StoppingData.nonleaf (N' + 1) P :=
    ⟨_, rfl⟩
  have mem_cand : ∀ Q : DyadicCube d, Q ∈ cand ↔ Q.toSet ⊆ P.toSet ∧ m₀ ≤ Q.m := by
    intro Q
    rw [hcand, StoppingData.mem_nonleaf_iff hd]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by push_cast at h2; omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by push_cast; omega⟩
  -- the stopping cubes: the maximal candidates with `|[b]_Q − [b]_P| > λ`
  obtain ⟨stop, hstop⟩ : ∃ S : Finset (DyadicCube d), S = cand.filter
      (fun Q => lam < |avg Q b - avg P b| ∧
        ∀ R ∈ cand, Q.toSet ⊆ R.toSet → lam < |avg R b - avg P b| → R = Q) := ⟨_, rfl⟩
  have mem_stop : ∀ Q : DyadicCube d, Q ∈ stop ↔ Q ∈ cand ∧ lam < |avg Q b - avg P b| ∧
      ∀ R ∈ cand, Q.toSet ⊆ R.toSet → lam < |avg R b - avg P b| → R = Q := by
    intro Q
    rw [hstop, Finset.mem_filter]
  have exists_stop : ∀ L ∈ cand, lam < |avg L b - avg P b| → ∃ Q ∈ stop, L.toSet ⊆ Q.toSet := by
    intro L hL hbadL
    obtain ⟨Q, hQ, hmax⟩ := Finset.exists_max_image
      (cand.filter fun R => L.toSet ⊆ R.toSet ∧ lam < |avg R b - avg P b|) (fun R => R.m)
      ⟨L, Finset.mem_filter.mpr ⟨hL, subset_rfl, hbadL⟩⟩
    rw [Finset.mem_filter] at hQ
    refine ⟨Q, (mem_stop Q).mpr ⟨hQ.1, hQ.2.2, fun R hR hQR hbadR => ?_⟩, hQ.2.1⟩
    have h1 := hmax R (Finset.mem_filter.mpr ⟨hR, hQ.2.1.trans hQR, hbadR⟩)
    exact (DyadicCube.eq_of_subset_of_m_eq hQR
      (le_antisymm (DyadicCube.m_le_of_subset hd hQR) h1)).symm
  have stop_sub : ∀ Q ∈ stop, Q.toSet ⊆ P.toSet :=
    fun Q hQ => ((mem_cand Q).mp ((mem_stop Q).mp hQ).1).1
  have stop_m : ∀ Q ∈ stop, m₀ ≤ Q.m := fun Q hQ => ((mem_cand Q).mp ((mem_stop Q).mp hQ).1).2
  have stop_bad : ∀ Q ∈ stop, lam < |avg Q b - avg P b| := fun Q hQ => ((mem_stop Q).mp hQ).2.1
  have stop_ne : ∀ Q ∈ stop, Q ≠ P := by
    intro Q hQ hQP
    have h := stop_bad Q hQ
    rw [hQP, sub_self, abs_zero] at h
    exact absurd h (not_lt.mpr hlam0.le)
  have stop_disj : ∀ Q ∈ stop, ∀ R ∈ stop, Q ≠ R → Disjoint Q.toSet R.toSet := by
    intro Q hQ R hR hne
    have hQ' := (mem_stop Q).mp hQ
    have hR' := (mem_stop R).mp hR
    rcases le_total Q.m R.m with h | h
    · rcases DyadicCube.subset_or_disjoint Q R h with hsub | hdis
      · exact absurd (hQ'.2.2 R hR'.1 hsub hR'.2.1) (Ne.symm hne)
      · exact hdis
    · rcases DyadicCube.subset_or_disjoint R Q h with hsub | hdis
      · exact absurd (hR'.2.2 Q hQ'.1 hsub hQ'.2.1) hne
      · exact hdis.symm
  -- the parent of a stopping cube is a good cube in `P`
  have stop_parent : ∀ Q ∈ stop, Q.parent.toSet ⊆ P.toSet ∧ |avg Q.parent b - avg P b| ≤ lam := by
    intro Q hQ
    have hQ' := (mem_stop Q).mp hQ
    have hsub : Q.parent.toSet ⊆ P.toSet :=
      DyadicCube.parent_subset_of_ssubset hd (stop_sub Q hQ) (stop_ne Q hQ)
    refine ⟨hsub, not_lt.mp fun hbadp => ?_⟩
    have hpc : Q.parent ∈ cand :=
      (mem_cand _).mpr ⟨hsub, by rw [DyadicCube.parent_m]; have := stop_m Q hQ; omega⟩
    have h := hQ'.2.2 Q.parent hpc Q.subset_parent hbadp
    have hm := congrArg DyadicCube.m h
    rw [DyadicCube.parent_m] at hm
    omega
  -- `|[b]_Q − [b]_P| ≤ μ` on the stopping cubes
  have stop_avg : ∀ Q ∈ stop, |avg Q b - avg P b| ≤ μ := by
    intro Q hQ
    obtain ⟨hsub, hgood⟩ := stop_parent Q hQ
    have h1 := abs_avg_sub_avg_parent_le hb hdual hsub (stop_m Q hQ)
    calc |avg Q b - avg P b|
        ≤ |avg Q b - avg Q.parent b| + |avg Q.parent b - avg P b| := abs_sub_le _ _ _
      _ ≤ 2 ^ d * K + lam := add_le_add h1 hgood
      _ = μ := by rw [hμ]; ring
  -- the stopping cubes cover at most a quarter of `P`
  have stop_vol :=
    jn_stopping_volume hb hK hPm hdual stop stop_sub stop_disj stop_m hlam stop_bad
  -- the pointwise bound on `P`
  have hpt : ∀ x ∈ P.toSet, (b x - avg P b) ^ 2 ≤ lam ^ 2 +
      ∑ Q ∈ stop, Q.toSet.indicator (fun y => 2 * (b y - avg Q b) ^ 2 + 2 * μ ^ 2) x := by
    intro x hx
    have hnn : ∀ Q ∈ stop,
        0 ≤ Q.toSet.indicator (fun y => 2 * (b y - avg Q b) ^ 2 + 2 * μ ^ 2) x :=
      fun Q _ => Set.indicator_nonneg (fun y _ => by positivity) x
    by_cases hxs : ∃ Q ∈ stop, x ∈ Q.toSet
    · obtain ⟨Q, hQ, hxQ⟩ := hxs
      have h1 := Finset.single_le_sum
        (f := fun Q => Q.toSet.indicator (fun y => 2 * (b y - avg Q b) ^ 2 + 2 * μ ^ 2) x) hnn hQ
      rw [Set.indicator_of_mem hxQ] at h1
      have h2 : (avg Q b - avg P b) ^ 2 ≤ μ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (stop_avg Q hQ) 2
      have h3 : (b x - avg P b) ^ 2 ≤ 2 * (b x - avg Q b) ^ 2 + 2 * (avg Q b - avg P b) ^ 2 := by
        nlinarith [sq_nonneg ((b x - avg Q b) - (avg Q b - avg P b))]
      linarith [h1, h2, h3, sq_nonneg lam]
    · have hgood : |b x - avg P b| ≤ lam := by
        obtain ⟨L, hL, hxL⟩ := StoppingData.exists_mem_level N' hx
        have hLm : L.m = m₀ := by rw [StoppingData.m_of_mem_level hL]; omega
        have hLc : L ∈ cand := (mem_cand L).mpr ⟨StoppingData.subset_of_mem_level hL, hLm.ge⟩
        have hbx : b x = avg L b := (avg_eq_of_constOn (hconst L hLm.le) hxL).symm
        rw [hbx]
        by_contra hbad
        obtain ⟨Q, hQ, hLQ⟩ := exists_stop L hLc (not_le.mp hbad)
        exact hxs ⟨Q, hQ, hLQ hxL⟩
      have h1 : (b x - avg P b) ^ 2 ≤ lam ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hgood 2
      linarith [Finset.sum_nonneg hnn]
  -- integrate the pointwise bound
  have hint1 : IntegrableOn (fun x => (b x - avg P b) ^ 2) P.toSet volume :=
    TestFun.integrableOn_sq_sub hb _ P
  have hintQ : ∀ Q : DyadicCube d,
      IntegrableOn (fun y => 2 * (b y - avg Q b) ^ 2 + 2 * μ ^ 2) Q.toSet volume := fun Q =>
    ((TestFun.integrableOn_sq_sub hb _ Q).const_mul 2).add
      (integrableOn_const (by rw [Q.volume_toSet]; exact ENNReal.ofReal_ne_top))
  have hint0 : Integrable (fun _ : Fin d → ℝ => lam ^ 2) (volume.restrict P.toSet) :=
    integrableOn_const (by rw [P.volume_toSet]; exact ENNReal.ofReal_ne_top)
  have hint3 : Integrable (fun x => ∑ Q ∈ stop,
      Q.toSet.indicator (fun y => 2 * (b y - avg Q b) ^ 2 + 2 * μ ^ 2) x) (volume.restrict P.toSet)
        :=
    integrable_finsetSum _ fun Q _ =>
      ((hintQ Q).integrable_indicator Q.measurableSet_toSet).integrableOn
  have hint2 : IntegrableOn (fun x => lam ^ 2 + ∑ Q ∈ stop,
      Q.toSet.indicator (fun y => 2 * (b y - avg Q b) ^ 2 + 2 * μ ^ 2) x) P.toSet volume :=
    hint0.add hint3
  have hI := setIntegral_mono_on hint1 hint2 P.measurableSet_toSet hpt
  rw [integral_add hint0 hint3, setIntegral_const,
    integral_finsetSum _ fun Q _ => ((hintQ Q).integrable_indicator
      Q.measurableSet_toSet).integrableOn,
    measureReal_def, P.volume_toSet, ENNReal.toReal_ofReal hV.le, smul_eq_mul] at hI
  have hterm : ∀ Q ∈ stop,
      ∫ x in P.toSet, Q.toSet.indicator (fun y => 2 * (b y - avg Q b) ^ 2 + 2 * μ ^ 2) x ≤
        (2 * (jnC d * K ^ 2) + 2 * μ ^ 2) * Q.vol := by
    intro Q hQ
    rw [setIntegral_indicator Q.measurableSet_toSet, Set.inter_eq_right.mpr (stop_sub Q hQ),
      integral_add ((TestFun.integrableOn_sq_sub hb _ Q).const_mul 2)
        (integrableOn_const (C := 2 * μ ^ 2) (by rw [Q.volume_toSet]; exact ENNReal.ofReal_ne_top)),
      integral_const_mul, setIntegral_const, measureReal_def, Q.volume_toSet,
      ENNReal.toReal_ofReal Q.vol_pos.le, smul_eq_mul]
    have := ih Q (stop_sub Q hQ) (stop_ne Q hQ)
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hμ2 : (0 : ℝ) ≤ 2 * (jnC d * K ^ 2) + 2 * μ ^ 2 :=
    add_nonneg (mul_nonneg two_pos.le (mul_nonneg (jnC_pos d).le (sq_nonneg _))) (by positivity)
  calc ∫ x in P.toSet, (b x - avg P b) ^ 2
      ≤ P.vol * lam ^ 2 + ∑ Q ∈ stop,
          ∫ x in P.toSet, Q.toSet.indicator (fun y => 2 * (b y - avg Q b) ^ 2 + 2 * μ ^ 2) x := hI
    _ ≤ P.vol * lam ^ 2 + (2 * (jnC d * K ^ 2) + 2 * μ ^ 2) * (P.vol / 4) :=
        add_le_add le_rfl (hsum.trans (mul_le_mul_of_nonneg_left stop_vol hμ2))
    _ = jnC d * K ^ 2 * P.vol := by
        rw [hμ, hlam, jnC]
        ring

/-- **The dyadic John–Nirenberg inequality** (induction on the depth). [PROVED] -/
theorem jn_core (hd : d ≠ 0) {b : (Fin d → ℝ) → ℝ} (hb : b ∈ TestFun d) {m₀ : ℤ}
    (hconst : ∀ L : DyadicCube d, L.m ≤ m₀ → ConstOn b L) {K : ℝ} (hK : 0 < K) :
    ∀ N : ℕ, ∀ P : DyadicCube d, P.m ≤ m₀ + N → JNDual b m₀ K P →
      ∫ x in P.toSet, (b x - avg P b) ^ 2 ≤ jnC d * K ^ 2 * P.vol := by
  intro N
  induction N with
  | zero =>
    intro P hP _
    rw [setIntegral_sq_sub_avg_eq_zero (hconst P (by simpa using hP))]
    exact mul_nonneg (mul_nonneg (jnC_pos d).le (sq_nonneg _)) P.vol_pos.le
  | succ N ih =>
    intro P hP hdual
    by_cases hPm : P.m ≤ m₀
    · rw [setIntegral_sq_sub_avg_eq_zero (hconst P hPm)]
      exact mul_nonneg (mul_nonneg (jnC_pos d).le (sq_nonneg _)) P.vol_pos.le
    · refine jn_step hd hb hconst hK (not_le.mp hPm) hdual fun Q hQP hne => ?_
      have hm : Q.m < P.m := lt_of_le_of_ne (DyadicCube.m_le_of_subset hd hQP)
        fun h => hne (DyadicCube.eq_of_subset_of_m_eq hQP h)
      exact ih Q (by push_cast at hP; omega) (hdual.mono hQP)

/-- **The dyadic John–Nirenberg inequality**: a test function `b` constant below the scale `m₀`
satisfying the dual `L^1`-BMO condition `JNDual b m₀ K P` has `∫_P |b − [b]_P|² ≤ C_d K² |P|`.
[PROVED] -/
theorem dyadic_john_nirenberg (hd : d ≠ 0) {b : (Fin d → ℝ) → ℝ} (hb : b ∈ TestFun d) {m₀ : ℤ}
    (hconst : ∀ L : DyadicCube d, L.m ≤ m₀ → ConstOn b L) {K : ℝ} (hK : 0 < K) (P : DyadicCube d)
    (hdual : JNDual b m₀ K P) :
    ∫ x in P.toSet, (b x - avg P b) ^ 2 ≤ jnC d * K ^ 2 * P.vol :=
  jn_core hd hb hconst hK (P.m - m₀).toNat P (by omega) hdual

/-! ### The Carleson condition for all exponents -/

/-- The symbol `ψ = ∑_{Q ∈ nonleaf N P₀} ψ_Q` of the paraproduct in the slot `j` on `P₀`. -/
noncomputable def paraSymbol (T : PerfectCZForm d n) (j : Fin n) (P₀ : DyadicCube d) (N : ℕ) :
    TestFun d :=
  ∑ Q ∈ StoppingData.nonleaf N P₀, psi T j Q

/-- The symbol is constant on the cubes of scale `≤ ℓ(P₀) 2^{-N}`. [PROVED] -/
theorem paraSymbol_constOn (hd : d ≠ 0) (T : PerfectCZForm d n) (j : Fin n) (P₀ : DyadicCube d)
    (N : ℕ) : ∀ L : DyadicCube d, L.m ≤ P₀.m - N →
      ConstOn (paraSymbol T j P₀ N : (Fin d → ℝ) → ℝ) L := by
  intro L hL
  unfold paraSymbol
  refine StoppingData.constOn_sum fun Q hQ => ?_
  have hQm := ((StoppingData.mem_nonleaf_iff hd).mp hQ).2
  unfold psi
  refine StoppingData.constOn_sum fun ε _ => StoppingData.constOn_smul _ (constOn_ind ?_)
  exact DyadicCube.subset_or_disjoint L (Q.child ε) (show L.m ≤ Q.m - 1 by omega)

/-- `∫ ψ_Q φ = 2^{-d} ∑_ε v_Q(ε) ([φ]_{Q_ε} − [φ]_Q)`. [PROVED] -/
theorem integral_psi_mul (T : PerfectCZForm d n) (j : Fin n) (Q : DyadicCube d) (φ : TestFun d) :
    ∫ x, (psi T j Q : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x =
      (2 ^ d)⁻¹ * ∑ ε : Fin d → Bool, coefV T j Q ε *
        (avg (Q.child ε) (φ : (Fin d → ℝ) → ℝ) - avg Q (φ : (Fin d → ℝ) → ℝ)) := by
  have hV0 := Q.vol_pos.ne'
  have e : ∀ x, (psi T j Q : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x =
      ∑ ε : Fin d → Bool, (Q.vol⁻¹ * coefV T j Q ε) *
        ((φ : (Fin d → ℝ) → ℝ) x * ((TestFun.ind (Q.child ε) : TestFun d) : (Fin d → ℝ) → ℝ) x) :=
          by
    intro x
    simp only [psi, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ε _ => by ring
  have hint : ∀ ε : Fin d → Bool, Integrable (fun x => (φ : (Fin d → ℝ) → ℝ) x *
      ((TestFun.ind (Q.child ε) : TestFun d) : (Fin d → ℝ) → ℝ) x) volume :=
    fun ε => (TestFun.memLp φ.2 2).integrable_mul (TestFun.memLp (TestFun.ind _).2 2)
  rw [integral_congr_ae (ae_of_all _ e), integral_finsetSum _ fun ε _ => (hint ε).const_mul _]
  simp only [integral_const_mul, integral_mul_ind]
  have e2 : ∀ ε : Fin d → Bool, Q.vol⁻¹ * coefV T j Q ε *
      ∫ x in (Q.child ε).toSet, (φ : (Fin d → ℝ) → ℝ) x =
      (2 ^ d)⁻¹ * (coefV T j Q ε * avg (Q.child ε) (φ : (Fin d → ℝ) → ℝ)) := by
    intro ε
    rw [← avg_mul_vol, vol_child_eq]
    calc Q.vol⁻¹ * coefV T j Q ε * (avg (Q.child ε) (φ : (Fin d → ℝ) → ℝ) * (Q.vol / 2 ^ d))
        = (Q.vol⁻¹ * Q.vol) * ((2 ^ d)⁻¹ * (coefV T j Q ε * avg (Q.child ε) (φ : (Fin d → ℝ) → ℝ)))
          := by
          ring
      _ = _ := by rw [inv_mul_cancel₀ hV0, one_mul]
  rw [Finset.sum_congr rfl fun ε _ => e2 ε, ← Finset.mul_sum]
  congr 1
  have h0 : ∑ ε : Fin d → Bool, coefV T j Q ε * avg Q (φ : (Fin d → ℝ) → ℝ) = 0 := by
    rw [← Finset.sum_mul, sum_coefV, zero_mul]
  rw [Finset.sum_congr rfl fun ε _ => mul_sub (coefV T j Q ε) _ _, Finset.sum_sub_distrib, h0,
    sub_zero]

/-- `∫ ψ_{Q''} φ = 0` for `φ` supported on `Q` with mean zero and `Q'' ⊄ Q`. [PROVED] -/
theorem integral_psi_mul_eq_zero (hd : d ≠ 0) (T : PerfectCZForm d n) (j : Fin n)
    {Q'' Q : DyadicCube d} (hn : ¬ Q''.toSet ⊆ Q.toSet) {φ : TestFun d}
    (hφs : SupportedOn (φ : (Fin d → ℝ) → ℝ) Q) (hφ0 : MeanZero (φ : (Fin d → ℝ) → ℝ)) :
    ∫ x, (psi T j Q'' : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x = 0 := by
  have hdis : Disjoint Q''.toSet Q.toSet →
      ∫ x, (psi T j Q'' : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x = 0 := by
    intro hdis
    have hz : ∀ x, (psi T j Q'' : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x = 0 := by
      intro x
      by_cases hx : x ∈ Q.toSet
      · rw [psi_supportedOn T j Q'' x (Set.disjoint_right.mp hdis hx), zero_mul]
      · rw [hφs x hx, mul_zero]
    rw [integral_congr_ae (ae_of_all _ hz)]
    simp
  by_cases h : Q''.m ≤ Q.m
  · rcases DyadicCube.subset_or_disjoint Q'' Q h with hsub | hd'
    · exact absurd hsub hn
    · exact hdis hd'
  · rcases DyadicCube.subset_or_disjoint Q Q'' (not_le.mp h).le with hsub | hd'
    · have hne : Q ≠ Q'' := fun e => h (le_of_eq (by rw [e]))
      obtain ⟨ε, hε⟩ := DyadicCube.exists_child_of_ssubset hd hsub hne
      have hc : ConstOn (psi T j Q'' : (Fin d → ℝ) → ℝ) Q :=
        constOn_of_subset hε (psi_constOn_child T j Q'' ε)
      have hz : ∀ x, (psi T j Q'' : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x =
          (psi T j Q'' : (Fin d → ℝ) → ℝ) (fun i => (2 : ℝ) ^ Q.m * Q.l i) *
            (φ : (Fin d → ℝ) → ℝ) x := by
        intro x
        by_cases hx : x ∈ Q.toSet
        · rw [hc x hx _ Q.corner_mem]
        · rw [hφs x hx, mul_zero, mul_zero]
      have h0' : ∫ x, (φ : (Fin d → ℝ) → ℝ) x = 0 := hφ0
      rw [integral_congr_ae (ae_of_all _ hz), integral_const_mul, h0', mul_zero]
    · exact hdis hd'.symm

/-- **The symbol represents the paraproduct**: `Λ(𝟙_Q, …, φ, …, 𝟙_Q) = 2^d ∫ ψ φ` for `Q ⊆ P₀` of
scale `≥ ℓ(P₀) 2^{-N}` and `φ` supported on `Q`, with mean zero and constant on the cubes of scale
`≤ ℓ(P₀) 2^{-N}`. [PROVED] -/
theorem form_oneTuple_eq_integral_paraSymbol (hd : d ≠ 0) (T : PerfectCZForm d n) (j : Fin n)
    {P₀ : DyadicCube d} {N : ℕ} {Q : DyadicCube d} (hQP : Q.toSet ⊆ P₀.toSet)
    (hQm : P₀.m - N ≤ Q.m) {φ : TestFun d} (hφs : SupportedOn (φ : (Fin d → ℝ) → ℝ) Q)
    (hφ0 : MeanZero (φ : (Fin d → ℝ) → ℝ))
    (hφc : ∀ L : DyadicCube d, L.m ≤ P₀.m - N → ConstOn (φ : (Fin d → ℝ) → ℝ) L) :
    T.form (oneTuple Q j φ) =
      2 ^ d * ∫ x, (paraSymbol T j P₀ N : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x := by
  classical
  obtain ⟨NQ, hNQ⟩ : ∃ NQ : ℕ, NQ = (Q.m - (P₀.m - N)).toNat := ⟨_, rfl⟩
  have hNQm : Q.m - NQ = P₀.m - N := by omega
  -- `φ = ∑_{Q' ∈ nonleaf NQ Q} Δ_{Q'} φ`
  have hφeq : φ = ∑ Q' ∈ StoppingData.nonleaf NQ Q, mdiff Q' φ := by
    have h1 := coarsen_eq_self hφs (N := NQ) fun L hL =>
      hφc L (le_of_eq (by rw [StoppingData.m_of_mem_level hL, hNQm]))
    have h2 := coarsen_eq_sum_mdiff Q NQ φ
    rw [h1, avg_eq_zero_of_subset_supp hφs hφ0 subset_rfl, zero_smul, zero_add] at h2
    exact h2
  -- the cubes of `nonleaf N P₀` inside `Q` are the cubes of `nonleaf NQ Q`
  have hfilter : (StoppingData.nonleaf N P₀).filter (fun Q'' => Q''.toSet ⊆ Q.toSet) =
      StoppingData.nonleaf NQ Q := by
    ext Q''
    rw [Finset.mem_filter, StoppingData.mem_nonleaf_iff hd, StoppingData.mem_nonleaf_iff hd]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h3, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.trans hQP, by omega⟩, h1⟩
  -- the left side
  have hL : T.form (oneTuple Q j φ) = ∑ Q' ∈ StoppingData.nonleaf NQ Q, ∑ ε : Fin d → Bool,
      (avg (Q'.child ε) (φ : (Fin d → ℝ) → ℝ) - avg Q' (φ : (Fin d → ℝ) → ℝ)) *
        coefChild T j Q' ε := by
    conv_lhs => rw [hφeq]
    rw [oneTuple, MultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun Q' hQ' => ?_
    have hQ'Q : Q'.toSet ⊆ Q.toSet := subset_of_mem_nonleaf hQ'
    rw [show T.form (Function.update (fun _ : Fin n => TestFun.ind Q) j (mdiff Q' φ)) =
        T.form (oneTuple Q' j (mdiff Q' φ)) from
        form_oneTuple_eq_of_subset T j hQ'Q (mdiff_supportedOn Q' φ) (mdiff_meanZero Q' φ),
      mdiff_eq_sum_children, form_oneTuple_smul_sum]
  -- the right side
  have hR : ∫ x, (paraSymbol T j P₀ N : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x =
      ∑ Q' ∈ StoppingData.nonleaf NQ Q, (2 ^ d)⁻¹ * ∑ ε : Fin d → Bool, coefV T j Q' ε *
        (avg (Q'.child ε) (φ : (Fin d → ℝ) → ℝ) - avg Q' (φ : (Fin d → ℝ) → ℝ)) := by
    have e : ∀ x, (paraSymbol T j P₀ N : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x =
        ∑ Q'' ∈ StoppingData.nonleaf N P₀,
          (psi T j Q'' : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x := by
      intro x
      simp only [paraSymbol, Submodule.coe_sum, Finset.sum_apply, Finset.sum_mul]
    have hzero : ∑ Q'' ∈ (StoppingData.nonleaf N P₀).filter (fun Q'' => ¬ Q''.toSet ⊆ Q.toSet),
        ∫ x, (psi T j Q'' : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x = 0 :=
      Finset.sum_eq_zero fun Q'' hQ'' =>
        integral_psi_mul_eq_zero hd T j (Finset.mem_filter.mp hQ'').2 hφs hφ0
    have hint : ∀ Q'' : DyadicCube d, Integrable
        (fun x => (psi T j Q'' : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x) volume :=
      fun Q'' => (TestFun.memLp (psi T j Q'').2 2).integrable_mul (TestFun.memLp φ.2 2)
    rw [integral_congr_ae (ae_of_all _ e), integral_finsetSum _ fun Q'' _ => hint Q'',
      ← Finset.sum_filter_add_sum_filter_not (StoppingData.nonleaf N P₀)
        (fun Q'' => Q''.toSet ⊆ Q.toSet), hzero, add_zero, hfilter]
    exact Finset.sum_congr rfl fun Q' _ => integral_psi_mul T j Q' φ
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q' _ => ?_
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ d ≠ 0), one_mul]
  have hc0 : ∑ ε : Fin d → Bool,
      (avg (Q'.child ε) (φ : (Fin d → ℝ) → ℝ) - avg Q' (φ : (Fin d → ℝ) → ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_avg_children, Finset.sum_const, card_children, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, sub_self]
  have h : ∀ ε : Fin d → Bool,
      (avg (Q'.child ε) (φ : (Fin d → ℝ) → ℝ) - avg Q' (φ : (Fin d → ℝ) → ℝ)) * coefChild T j Q' ε =
        coefV T j Q' ε * (avg (Q'.child ε) (φ : (Fin d → ℝ) → ℝ) - avg Q' (φ : (Fin d → ℝ) → ℝ)) +
          coefMean T j Q' *
            (avg (Q'.child ε) (φ : (Fin d → ℝ) → ℝ) - avg Q' (φ : (Fin d → ℝ) → ℝ)) := by
    intro ε
    unfold coefV
    ring
  rw [Finset.sum_congr rfl fun ε _ => h ε, Finset.sum_add_distrib, ← Finset.mul_sum, hc0, mul_zero,
    add_zero]

/-- **The dual BMO condition for the symbol** follows from the testing condition in the slot `j`,
with `K = 2^{-d} B`. [PROVED] -/
theorem paraSymbol_jnDual (hd : d ≠ 0) {T : PerfectCZForm d n} {p : HolderTuple n} {B : ℝ}
    (hT : T1Testing T p B) (hB : 1 ≤ B) (j : Fin n) (P₀ : DyadicCube d) (N : ℕ) :
    JNDual (paraSymbol T j P₀ N : (Fin d → ℝ) → ℝ) (P₀.m - N) ((2 ^ d)⁻¹ * B) P₀ := by
  intro Q hQP hQm φ hφs hφ0 hφc M hM0 hM
  have hpj : 0 < p.p j := by linarith [p.one_lt j]
  have hV := Q.vol_pos
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have h1 := abs_form_oneTuple_le hT j Q φ hφs
  rw [form_oneTuple_eq_integral_paraSymbol hd T j hQP hQm hφs hφ0 hφc,
    abs_mul, abs_of_pos h2d] at h1
  have h2 := TestFun.lpNorm_le_of_abs_le φ hφs hM0 hM hpj
  have h3 : Q.vol ^ (1 - 1 / p.p j) * Q.vol ^ (1 / p.p j) = Q.vol := by
    rw [← Real.rpow_add hV, sub_add_cancel, Real.rpow_one]
  calc |∫ x, (paraSymbol T j P₀ N : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x|
      = (2 ^ d)⁻¹ * (2 ^ d *
          |∫ x, (paraSymbol T j P₀ N : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x|) := by
        rw [← mul_assoc, inv_mul_cancel₀ h2d.ne', one_mul]
    _ ≤ (2 ^ d)⁻¹ * (B * Q.vol ^ (1 - 1 / p.p j) * (M * Q.vol ^ (1 / p.p j))) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2
          (mul_nonneg hB0 (Real.rpow_nonneg hV.le _)))) (by positivity)
    _ = (2 ^ d)⁻¹ * B * M * (Q.vol ^ (1 - 1 / p.p j) * Q.vol ^ (1 / p.p j)) := by ring
    _ = (2 ^ d)⁻¹ * B * M * Q.vol := by rw [h3]

/-- **The Carleson condition for all exponents**: `∑_{Q ∈ nonleaf N P} β_Q² |Q| ≤ C_d B² |P|`, by
the dyadic John–Nirenberg inequality applied to the symbol `ψ = ∑_Q ψ_Q`. [PROVED] -/
theorem sum_carl_sq_le' (hd : d ≠ 0) {T : PerfectCZForm d n} {p : HolderTuple n} {B : ℝ}
    (hT : T1Testing T p B) (hB : 1 ≤ B) (j : Fin n) (P : DyadicCube d) (N : ℕ) :
    ∑ Q ∈ StoppingData.nonleaf N P, carl T j Q ^ 2 * Q.vol ≤ jnC d * B ^ 2 * P.vol := by
  have hV := P.vol_pos
  have hB0 : (0 : ℝ) < B := by linarith
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  -- `β_Q² |Q| = 2^d |Q|⁻¹ ‖v_Q‖²`
  have hcarl : ∀ Q : DyadicCube d, carl T j Q ^ 2 * Q.vol =
      2 ^ d * (Q.vol⁻¹ * ∑ ε : Fin d → Bool, coefV T j Q ε ^ 2) := by
    intro Q
    have hV0 := Q.vol_pos.ne'
    unfold carl
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    calc 2 ^ d * (∑ ε : Fin d → Bool, coefV T j Q ε ^ 2) / Q.vol ^ 2 * Q.vol
        = 2 ^ d * (Q.vol⁻¹ * ∑ ε : Fin d → Bool, coefV T j Q ε ^ 2) * (Q.vol⁻¹ * Q.vol) := by
          ring
      _ = _ := by rw [inv_mul_cancel₀ hV0, mul_one]
  -- Pythagoras: `∫ ψ² = 2^{-d} Σ`
  have hψ2 : ∫ x, (paraSymbol T j P N : (Fin d → ℝ) → ℝ) x ^ 2 =
      (2 ^ d)⁻¹ * ∑ Q ∈ StoppingData.nonleaf N P, Q.vol⁻¹ * ∑ ε : Fin d → Bool, coefV T j Q ε ^ 2 :=
        by
    rw [paraSymbol, integral_sq_sum_eq_sum (psi T j) (fun Q _ => psi_supportedOn T j Q)
      (fun Q _ => psi_meanZero T j Q) (fun Q _ ε => psi_constOn_child T j Q ε), Finset.mul_sum]
    exact Finset.sum_congr rfl fun Q _ => by rw [integral_sq_psi, mul_assoc]
  have hsupp : SupportedOn (paraSymbol T j P N : (Fin d → ℝ) → ℝ) P := by
    intro x hx
    simp only [paraSymbol, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun Q hQ =>
      psi_supportedOn T j Q x fun h => hx (subset_of_mem_nonleaf hQ h)
  have hmean : MeanZero (paraSymbol T j P N : (Fin d → ℝ) → ℝ) := by
    change ∫ x, (paraSymbol T j P N : (Fin d → ℝ) → ℝ) x = 0
    rw [← TestFun.integralₗ_apply, paraSymbol, map_sum]
    exact Finset.sum_eq_zero fun Q _ => psi_meanZero T j Q
  -- John–Nirenberg
  have hjn := dyadic_john_nirenberg hd (paraSymbol T j P N).2 (paraSymbol_constOn hd T j P N)
    (by positivity : (0 : ℝ) < (2 ^ d)⁻¹ * B) P (paraSymbol_jnDual hd hT hB j P N)
  rw [avg_eq_zero_of_subset_supp hsupp hmean subset_rfl] at hjn
  simp only [sub_zero] at hjn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [hsupp x hx, zero_pow two_ne_zero]), hψ2] at hjn
  -- conclude
  rw [Finset.sum_congr rfl fun Q _ => hcarl Q, ← Finset.mul_sum]
  calc 2 ^ d * ∑ Q ∈ StoppingData.nonleaf N P, Q.vol⁻¹ * ∑ ε : Fin d → Bool, coefV T j Q ε ^ 2
      = (2 ^ d) ^ 2 * ((2 ^ d)⁻¹ *
          ∑ Q ∈ StoppingData.nonleaf N P, Q.vol⁻¹ * ∑ ε : Fin d → Bool, coefV T j Q ε ^ 2) := by
        rw [show ((2 : ℝ) ^ d) ^ 2 * ((2 ^ d)⁻¹ *
            ∑ Q ∈ StoppingData.nonleaf N P, Q.vol⁻¹ * ∑ ε : Fin d → Bool, coefV T j Q ε ^ 2) =
            (2 ^ d * (2 ^ d)⁻¹) *
              (2 ^ d * ∑ Q ∈ StoppingData.nonleaf N P, Q.vol⁻¹ *
                ∑ ε : Fin d → Bool, coefV T j Q ε ^ 2) by ring,
          mul_inv_cancel₀ h2d.ne', one_mul]
    _ ≤ (2 ^ d) ^ 2 * (jnC d * ((2 ^ d)⁻¹ * B) ^ 2 * P.vol) :=
        mul_le_mul_of_nonneg_left hjn (by positivity)
    _ = jnC d * B ^ 2 * P.vol := by
        rw [show ((2 : ℝ) ^ d) ^ 2 * (jnC d * ((2 ^ d)⁻¹ * B) ^ 2 * P.vol) =
            (2 ^ d * (2 ^ d)⁻¹) ^ 2 * (jnC d * B ^ 2 * P.vol) by ring,
          mul_inv_cancel₀ h2d.ne', one_pow, one_mul]

/-- **`‖β‖_{L^∞(S₂)} ≤ √C_d B`** for all exponents: on every tree the Carleson sum lives on the
finitely many cubes above the resolution of the form, where it is at most `C_d B² |P|`. [PROVED] -/
theorem outerLinfNorm_carl_le (hd : d ≠ 0) {T : PerfectCZForm d n} {p : HolderTuple n} {B : ℝ}
    (hT : T1Testing T p B) (hB : 1 ≤ B) {s : ℤ} (hs : KernelScale T s) (j : Fin n) :
    outerLinfNorm (sizeP 2) (carl T j) ≤ ENNReal.ofReal (Real.sqrt (jnC d) * B) := by
  have hB0 : (0 : ℝ) ≤ B := by linarith
  refine iSup_le fun P => ?_
  have hV := P.vol_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (P.m - s).toNat := ⟨_, rfl⟩
  have hsupp : ∀ Q : DyadicCube d, Q ∉ StoppingData.nonleaf N P →
      P.tree.indicator (fun Q => ‖carl T j Q‖ₑ ^ (2 : ℝ) * ENNReal.ofReal Q.vol) Q = 0 := by
    intro Q hQ
    by_cases hQP : Q ∈ P.tree
    · rw [Set.indicator_of_mem hQP]
      have hQle : Q.m ≤ P.m := DyadicCube.m_le_of_subset hd hQP
      have hQm : Q.m ≤ s := by
        by_contra hlt
        have hlt' : s < Q.m := not_le.mp hlt
        exact hQ ((StoppingData.mem_nonleaf_iff hd).mpr ⟨hQP, by omega⟩)
      rw [carl_eq_zero_of_le hs j hQm, enorm_zero, ENNReal.zero_rpow_of_pos two_pos, zero_mul]
    · rw [Set.indicator_of_notMem hQP]
  have hsum : ∑' Q : P.tree, ‖carl T j Q‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Q : DyadicCube d).vol ≤
      ENNReal.ofReal (jnC d * B ^ 2 * P.vol) := by
    rw [tsum_subtype P.tree (fun Q => ‖carl T j Q‖ₑ ^ (2 : ℝ) * ENNReal.ofReal Q.vol),
      tsum_eq_sum hsupp]
    calc ∑ Q ∈ StoppingData.nonleaf N P,
          P.tree.indicator (fun Q => ‖carl T j Q‖ₑ ^ (2 : ℝ) * ENNReal.ofReal Q.vol) Q
        = ∑ Q ∈ StoppingData.nonleaf N P, ENNReal.ofReal (carl T j Q ^ 2 * Q.vol) := by
          refine Finset.sum_congr rfl fun Q hQ => ?_
          rw [Set.indicator_of_mem (subset_of_mem_nonleaf hQ : Q ∈ P.tree),
            Real.enorm_eq_ofReal_abs, abs_of_nonneg (carl_nonneg T j Q),
            ENNReal.ofReal_rpow_of_nonneg (carl_nonneg T j Q) two_pos.le, Real.rpow_two,
            ← ENNReal.ofReal_mul (sq_nonneg _)]
      _ = ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N P, carl T j Q ^ 2 * Q.vol) :=
          (ENNReal.ofReal_sum_of_nonneg fun Q _ => mul_nonneg (sq_nonneg _) Q.vol_pos.le).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (sum_carl_sq_le' hd hT hB j P N)
  change sizeP 2 (carl T j) P ≤ ENNReal.ofReal (Real.sqrt (jnC d) * B)
  unfold sizeP
  calc (ENNReal.ofReal P.vol⁻¹ *
        ∑' Q : P.tree, ‖carl T j Q‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (Q : DyadicCube d).vol) ^ (1 / (2 :
          ℝ))
      ≤ (ENNReal.ofReal P.vol⁻¹ * ENNReal.ofReal (jnC d * B ^ 2 * P.vol)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hsum) (by positivity)
    _ = ENNReal.ofReal (Real.sqrt (jnC d) * B) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hV.le),
          show P.vol⁻¹ * (jnC d * B ^ 2 * P.vol) = (Real.sqrt (jnC d) * B) ^ 2 by
            rw [mul_comm (jnC d * B ^ 2), ← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul, mul_pow,
              Real.sq_sqrt (jnC_pos d).le],
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by positivity), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hB0)]

/-- **The paraproduct terms** (all exponents): there is `C` (depending only on `d`, `n`, `B`, the
exponents and `j`) such that for every cube `R`, depth `N` and tuple `f`,
`∑_{Q ∈ nonleaf N R} ∏_{i ≠ j} |[f_i]_Q| · |Λ(𝟙_Q, …, Δ_Q f_j, …, 𝟙_Q)| ≤ C ∏_i ‖f_i‖_{p_i}`.
[PROVED] -/
theorem sum_para_le (hd : d ≠ 0) {p : HolderTuple n} {B : ℝ} (hB : 1 ≤ B) (j : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : PerfectCZForm d n), T1Testing T p B →
      ∀ (R : DyadicCube d) (N : ℕ) (f : Fin n → TestFun d),
      ∑ Q ∈ StoppingData.nonleaf N R,
        (∏ i ∈ ({j} : Finset (Fin n))ᶜ, |avg Q (f i : (Fin d → ℝ) → ℝ)|) *
          |T.form (blockTuple Q f {j})| ≤ C * prodNorm p f := by
  choose Cc hCc0 hCc using fun i => carlesonEmbedding hd (p.p i) (p.one_lt i)
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hsB : (0 : ℝ) ≤ Real.sqrt (jnC d) * B := mul_nonneg (Real.sqrt_nonneg _) hB0
  have hCprod : 0 ≤ ∏ i, Cc i := Finset.prod_nonneg fun i _ => hCc0 i
  refine ⟨Real.sqrt (jnC d) * B * (4 * 2 * 2 ^ n) * ∏ i, Cc i, by positivity, ?_⟩
  intro T hT R N f
  obtain ⟨s, hs⟩ := Bridge.exists_kernelScale T p
  have hp : ∀ i, 0 < p.p i := fun i => by linarith [p.one_lt i]
  have hpos : ∀ i, 0 < 1 / p.p i := fun i => by have := hp i; positivity
  set E : Fin n → DyadicCube d → ℝ := fun i Q => martAvg Q (f i : (Fin d → ℝ) → ℝ) with hE
  set Δj : DyadicCube d → ℝ := fun Q => martDiff Q (f j : (Fin d → ℝ) → ℝ) with hΔ
  set F : DyadicCube d → ℝ := (∏ i ∈ Finset.univ.erase j, E i) * (Δj * carl T j) with hF
  set K : Fin n → ENNReal := fun i =>
    ENNReal.ofReal (Cc i) * eLpNorm (f i : (Fin d → ℝ) → ℝ) (ENNReal.ofReal (p.p i)) with hK
  have hcompl : ({j} : Finset (Fin n))ᶜ = Finset.univ.erase j := by
    ext i
    simp [eq_comm]
  have hFnn : ∀ Q, 0 ≤ F Q := fun Q => by
    simp only [hF, Pi.mul_apply, Finset.prod_apply]
    exact mul_nonneg (Finset.prod_nonneg fun i _ => martAvg_nonneg _ _)
      (mul_nonneg (martDiff_nonneg _ _) (carl_nonneg T j Q))
  -- the pointwise bound
  have hpt : ∀ Q, (∏ i ∈ ({j} : Finset (Fin n))ᶜ, |avg Q (f i : (Fin d → ℝ) → ℝ)|) *
      |T.form (blockTuple Q f {j})| ≤ Q.vol * F Q := by
    intro Q
    rw [hcompl]
    calc (∏ i ∈ Finset.univ.erase j, |avg Q (f i : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f
      {j})|
        ≤ (∏ i ∈ Finset.univ.erase j, E i Q) *
            (Q.vol * martDiff Q (f j : (Fin d → ℝ) → ℝ) * carl T j Q) :=
          mul_le_mul_of_nonneg_left (abs_form_blockTuple_single_le T Q f j)
            (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      _ = Q.vol * F Q := by
          simp only [hF, Pi.mul_apply, Finset.prod_apply, hΔ]
          ring
  -- the sum in `ℝ≥0∞` and Proposition 3.6
  have hsum : ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R,
      (∏ i ∈ ({j} : Finset (Fin n))ᶜ, |avg Q (f i : (Fin d → ℝ) → ℝ)|) *
        |T.form (blockTuple Q f {j})|) ≤ 4 * outerLpNorm (sizeP 1) 1 F := by
    calc ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R,
          (∏ i ∈ ({j} : Finset (Fin n))ᶜ, |avg Q (f i : (Fin d → ℝ) → ℝ)|) *
            |T.form (blockTuple Q f {j})|)
        ≤ ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R, Q.vol * F Q) :=
          ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun Q _ => hpt Q)
      _ = ∑ Q ∈ StoppingData.nonleaf N R, ‖F Q‖ₑ * ENNReal.ofReal Q.vol := by
          rw [ENNReal.ofReal_sum_of_nonneg fun Q _ => mul_nonneg Q.vol_pos.le (hFnn Q)]
          refine Finset.sum_congr rfl fun Q _ => ?_
          rw [mul_comm, ENNReal.ofReal_mul (hFnn Q), Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (hFnn Q)]
      _ ≤ ∑' Q : DyadicCube d, ‖F Q‖ₑ * ENNReal.ofReal Q.vol := ENNReal.sum_le_tsum _
      _ ≤ _ := tsum_enorm_mul_vol_le F
  -- monotonicity of the sizes and the Carleson bounds
  have hS₂ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 2 F T ≤ sizeP 2 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hS₁ : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeP 1 F T ≤ sizeP 1 G T :=
    fun F G T h => sizeP_mono (by norm_num) h T
  have hSinf : ∀ F G : DyadicCube d → ℝ, ∀ T, (∀ Q, ‖F Q‖ₑ ≤ ‖G Q‖ₑ) → sizeInf F T ≤ sizeInf G T :=
    fun F G T h => sizeInf_mono h T
  have hKfin : ∀ i, K i ≠ ⊤ := fun i =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (TestFun.memLp (f i).2 _).eLpNorm_ne_top
  have hEK : ∀ i, outerLpNorm sizeInf (p.p i) (E i) ≤ K i := fun i =>
    (hCc i _ (TestFun.memLp (f i).2 _)).1
  have hΔK : outerLpNorm (sizeP 2) (p.p j) Δj ≤ K j := (hCc j _ (TestFun.memLp (f j).2 _)).2
  have hcarlK : outerLinfNorm (sizeP 2) (carl T j) ≤ ENNReal.ofReal (Real.sqrt (jnC d) * B) :=
    outerLinfNorm_carl_le hd hT hB hs j
  -- the exponents: `∑_{i ≠ j} 1/p_i = 1 − 1/p_j ∈ (0, 1)`
  have hsumJ : ∑ i ∈ Finset.univ.erase j, 1 / p.p i = 1 - 1 / p.p j := by
    have := Finset.add_sum_erase Finset.univ (fun i => 1 / p.p i) (Finset.mem_univ j)
    rw [p.sum_one_div] at this
    linarith
  have hJpos : 0 < ∑ i ∈ Finset.univ.erase j, 1 / p.p i := by
    rw [hsumJ, sub_pos, div_lt_one (hp j)]
    exact p.one_lt j
  have hJne : (Finset.univ.erase j).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hJpos
    exact lt_irrefl _ hJpos
  have hJlt : ∑ i ∈ Finset.univ.erase j, 1 / p.p i < 1 := by
    rw [hsumJ]
    linarith [hpos j]
  -- Hölder for `∏_{i ≠ j} E_i` in `L^·(S_∞)`
  have hBnd := outerLpNorm_prod_sizeInf_le p.p hp E K hKfin hEK _ hJne hJlt.le
  -- Hölder with the `L^∞(S₂)` factor `β`
  have hcarlfin : outerLinfNorm (sizeP 2) (carl T j) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcarlK
  have hA := outerLpNorm_mul_le_Linf (sizeP 1) (sizeP 2) (sizeP 2) hS₂ hS₂
    sizeP_one_mul_le_sizeP_two (hp j) Δj (carl T j) hcarlfin
  -- Hölder with target exponent `1`
  have hr1 : 1 < (∑ i ∈ Finset.univ.erase j, 1 / p.p i)⁻¹ := by
    rw [lt_inv_comm₀ one_pos hJpos, inv_one]
    exact hJlt
  have hrr : 1 / (∑ i ∈ Finset.univ.erase j, 1 / p.p i)⁻¹ + 1 / p.p j = 1 := by
    simp only [one_div, inv_inv]
    simp only [one_div] at hsumJ
    linarith
  have hAfin : outerLpNorm sizeInf (∑ i ∈ Finset.univ.erase j, 1 / p.p i)⁻¹
      (∏ i ∈ Finset.univ.erase j, E i) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (ENNReal.prod_ne_top fun i _ => hKfin i)) hBnd
  have hBfin : outerLpNorm (sizeP 1) (p.p j) (Δj * carl T j) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ne_top_of_le_ne_top (hKfin j) hΔK) hcarlfin) hA
  have h3 := outerL1Norm_mul_le (sizeP 1) sizeInf (sizeP 1) hSinf hS₁ sizeP_one_mul_le_sizeInf
    hr1 (p.one_lt j) hrr (∏ i ∈ Finset.univ.erase j, E i) (Δj * carl T j) hAfin hBfin
  have hhold : outerLpNorm (sizeP 1) 1 F ≤
      2 * (((2 : ENNReal) ^ (Finset.univ.erase j).card * ∏ i ∈ Finset.univ.erase j, K i) *
        (K j * ENNReal.ofReal (Real.sqrt (jnC d) * B))) :=
    h3.trans (mul_le_mul' le_rfl (mul_le_mul' hBnd (hA.trans (mul_le_mul' hΔK hcarlK))))
  have hprodK : K j * ∏ i ∈ Finset.univ.erase j, K i = ∏ i, K i :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ j)
  have hcard : (Finset.univ.erase j).card ≤ n :=
    (Finset.card_le_univ _).trans (le_of_eq (Fintype.card_fin n))
  have hKprod : ∏ i, K i = ENNReal.ofReal ((∏ i, Cc i) * prodNorm p f) := by
    have e : ∀ i, eLpNorm (f i : (Fin d → ℝ) → ℝ) (ENNReal.ofReal (p.p i)) =
        ENNReal.ofReal (lpNorm (f i : (Fin d → ℝ) → ℝ) (p.p i)) := fun i =>
      (ENNReal.ofReal_toReal (TestFun.memLp (f i).2 _).eLpNorm_ne_top).symm
    simp only [hK, e]
    rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg fun i _ => hCc0 i,
      ← ENNReal.ofReal_prod_of_nonneg fun i _ => lpNorm_nonneg _ _, ← ENNReal.ofReal_mul hCprod,
      prodNorm]
  have hc : (4 * 2 * 2 ^ n : ENNReal) = ENNReal.ofReal (4 * 2 * 2 ^ n) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  have hfinal : ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R,
      (∏ i ∈ ({j} : Finset (Fin n))ᶜ, |avg Q (f i : (Fin d → ℝ) → ℝ)|) *
        |T.form (blockTuple Q f {j})|) ≤
      ENNReal.ofReal (Real.sqrt (jnC d) * B * (4 * 2 * 2 ^ n) * (∏ i, Cc i) * prodNorm p f) := by
    calc ENNReal.ofReal (∑ Q ∈ StoppingData.nonleaf N R,
          (∏ i ∈ ({j} : Finset (Fin n))ᶜ, |avg Q (f i : (Fin d → ℝ) → ℝ)|) *
            |T.form (blockTuple Q f {j})|)
        ≤ 4 * outerLpNorm (sizeP 1) 1 F := hsum
      _ ≤ 4 * (2 * (((2 : ENNReal) ^ (Finset.univ.erase j).card * ∏ i ∈ Finset.univ.erase j, K i) *
            (K j * ENNReal.ofReal (Real.sqrt (jnC d) * B)))) := mul_le_mul' le_rfl hhold
      _ = 4 * 2 * (2 : ENNReal) ^ (Finset.univ.erase j).card *
            ENNReal.ofReal (Real.sqrt (jnC d) * B) * ∏ i, K i := by
          rw [← hprodK]
          ring
      _ ≤ 4 * 2 * (2 : ENNReal) ^ n * ENNReal.ofReal (Real.sqrt (jnC d) * B) * ∏ i, K i :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_right₀ one_le_two hcard)) le_rfl)
            le_rfl
      _ = _ := by
          rw [hKprod, hc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * 2 * 2 ^ n),
            ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hsB)]
          congr 1
          ring
  rw [← ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (by positivity) hCprod) (prodNorm_nonneg p f))]
  exact hfinal

/-! ### The bound for tuples supported in a common cube -/

/-- Jensen: `‖E_N f‖_q ≤ ‖f‖_q` for `q ≥ 1`. [PROVED] -/
theorem lpNorm_coarsen_le (P : DyadicCube d) (N : ℕ) (f : TestFun d) {q : ℝ} (hq : 1 ≤ q) :
    lpNorm (coarsen P N f : (Fin d → ℝ) → ℝ) q ≤ lpNorm (f : (Fin d → ℝ) → ℝ) q := by
  have hq0 : 0 < q := by linarith
  refine (Real.rpow_le_rpow_iff (lpNorm_nonneg _ _) (lpNorm_nonneg _ _) hq0).mp ?_
  rw [lpNorm_rpow_eq_integral hq0 (TestFun.memLp (coarsen P N f).2 _),
    lpNorm_rpow_eq_integral hq0 (TestFun.memLp f.2 _)]
  exact coarsen_norm_le P N f hq

/-- `Λ(f) = Λ(E_N f)` for `f` supported on `P` and `ℓ(P) 2^{-N} ≤ 2^s`, `s` the resolution of
the form (all slots at once). [PROVED] -/
theorem form_coarsen_eq {T : PerfectCZForm d n} {s : ℤ} (hs : KernelScale T s)
    (f : Fin n → TestFun d) {P : DyadicCube d} {N : ℕ} (hPN : P.m - N ≤ s)
    (hf : ∀ j, SupportedOn (f j : (Fin d → ℝ) → ℝ) P) :
    T.form (fun j => coarsen P N (f j)) = T.form f := by
  have key : ∀ S : Finset (Fin n),
      T.form (fun j => if j ∈ S then coarsen P N (f j) else f j) = T.form f := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      rw [← ih]
      have e : (fun j => if j ∈ insert a S then coarsen P N (f j) else f j) =
          Function.update (fun j => if j ∈ S then coarsen P N (f j) else f j) a
            (coarsen P N ((fun j => if j ∈ S then coarsen P N (f j) else f j) a)) := by
        funext j
        by_cases hj : j = a
        · subst hj
          simp [ha]
        · simp [hj]
      rw [e, form_update_coarsen hs _ a hPN]
      simpa [ha] using hf a
  simpa using key Finset.univ

/-- **The telescoping expansion**: `Λ(E_N f) = Λ(E_0 f) + ∑_{Q ∈ nonleaf N R} ∑_{S ≠ ∅}
∏_{j ∉ S} [f_j]_Q · Λ(Δ_Q f_j (j ∈ S), 𝟙_Q (j ∉ S))`. [PROVED] -/
theorem form_coarsen_eq_sum (T : PerfectCZForm d n) (R : DyadicCube d) (f : Fin n → TestFun d) :
    ∀ N : ℕ, T.form (fun j => coarsen R N (f j)) = T.form (fun j => coarsen R 0 (f j)) +
      ∑ Q ∈ StoppingData.nonleaf N R, ∑ S ∈ Finset.univ.erase ∅,
        (∏ j ∈ Sᶜ, avg Q (f j : (Fin d → ℝ) → ℝ)) * T.form (blockTuple Q f S) := by
  intro N
  induction N with
  | zero => simp [StoppingData.nonleaf_zero]
  | succ N ih =>
    rw [StoppingData.sum_nonleaf_succ, ← add_assoc, ← ih, ← form_coarsen_succ_sub T R N f]
    ring

/-- **The local bound**: there is `C`, depending only on `d`, `n`, `B` and the exponents, such
that `|Λ(f)| ≤ C ∏ ‖f_j‖_{p_j}` for every form satisfying the testing condition and every tuple
supported in a common dyadic cube. [PROVED] -/
theorem abs_form_le_of_supported (hd : d ≠ 0) {p : HolderTuple n} {B : ℝ} (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : PerfectCZForm d n), T1Testing T p B →
      ∀ (R : DyadicCube d) (f : Fin n → TestFun d), (∀ j, SupportedOn (f j : (Fin d → ℝ) → ℝ) R) →
        |T.form f| ≤ C * prodNorm p f := by
  have hB0 : (0 : ℝ) ≤ B := by linarith
  -- the constants for the blocks `S ≠ ∅`
  have hS : ∀ S : Finset (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : PerfectCZForm d n), T1Testing T p B →
      ∀ (R : DyadicCube d) (N : ℕ) (f : Fin n → TestFun d), S.Nonempty →
        ∑ Q ∈ StoppingData.nonleaf N R,
          (∏ j ∈ Sᶜ, |avg Q (f j : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f S)| ≤
        C * prodNorm p f := by
    intro S
    by_cases hS2 : 2 ≤ S.card
    · obtain ⟨C, hC0, hC⟩ := sum_block_le hd hB S hS2
      exact ⟨C, hC0, fun T hT R N f _ => hC T hT R N f⟩
    · by_cases hS1 : S.card = 1
      · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hS1
        obtain ⟨C, hC0, hC⟩ := sum_para_le hd hB j
        refine ⟨C, hC0, fun T hT R N f _ => ?_⟩
        rw [hj]
        exact hC T hT R N f
      · refine ⟨0, le_rfl, fun T hT R N f hne => ?_⟩
        exfalso
        have := hne.card_pos
        omega
  choose CS hCS0 hCS using hS
  refine ⟨B * 2 ^ (d * n) + ∑ S ∈ Finset.univ.erase ∅, CS S,
    add_nonneg (by positivity) (Finset.sum_nonneg fun S _ => hCS0 S), ?_⟩
  intro T hT R f hsupp
  obtain ⟨s, hs⟩ := Bridge.exists_kernelScale T p
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (R.m - s).toNat := ⟨_, rfl⟩
  have hRN : R.m - N ≤ s := by omega
  have hp : ∀ j, 0 < p.p j := fun j => by linarith [p.one_lt j]
  -- the term at the top scale
  have h0 : |T.form (fun j => coarsen R 0 (f j))| ≤ B * 2 ^ (d * n) * prodNorm p f := by
    have hb := abs_form_le_of_constOn_children hT hB R (fun j => coarsen R 0 (f j))
      (fun j => coarsen_supportedOn R 0 (f j))
      (fun j ε => coarsen_constOn R 0 (f j) (by change R.m - 1 ≤ R.m - (0 : ℕ); simp))
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Finset.prod_le_prod₀ (fun j _ => lpNorm_nonneg _ _) fun j _ =>
      lpNorm_coarsen_le R 0 (f j) (p.one_lt j).le
  rw [← form_coarsen_eq hs f hRN hsupp, form_coarsen_eq_sum T R f N]
  calc |T.form (fun j => coarsen R 0 (f j)) + ∑ Q ∈ StoppingData.nonleaf N R,
          ∑ S ∈ Finset.univ.erase ∅,
            (∏ j ∈ Sᶜ, avg Q (f j : (Fin d → ℝ) → ℝ)) * T.form (blockTuple Q f S)|
      ≤ |T.form (fun j => coarsen R 0 (f j))| + |∑ Q ∈ StoppingData.nonleaf N R,
          ∑ S ∈ Finset.univ.erase ∅,
            (∏ j ∈ Sᶜ, avg Q (f j : (Fin d → ℝ) → ℝ)) * T.form (blockTuple Q f S)| :=
        abs_add_le _ _
    _ ≤ B * 2 ^ (d * n) * prodNorm p f + ∑ S ∈ Finset.univ.erase ∅,
          ∑ Q ∈ StoppingData.nonleaf N R,
            (∏ j ∈ Sᶜ, |avg Q (f j : (Fin d → ℝ) → ℝ)|) * |T.form (blockTuple Q f S)| := by
        refine add_le_add h0 ?_
        rw [Finset.sum_comm]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun Q _ => ?_)
        rw [abs_mul, Finset.abs_prod]
    _ ≤ B * 2 ^ (d * n) * prodNorm p f + ∑ S ∈ Finset.univ.erase ∅, CS S * prodNorm p f :=
        add_le_add le_rfl (Finset.sum_le_sum fun S hS => hCS S T hT R N f
          (Finset.nonempty_of_ne_empty (Finset.ne_of_mem_erase hS)))
    _ = (B * 2 ^ (d * n) + ∑ S ∈ Finset.univ.erase ∅, CS S) * prodNorm p f := by
        rw [add_mul, Finset.sum_mul]

/-! ### The cubes at infinity -/

/-- **One slot of perfect smoothness**: if `m_i` is supported on `P` and `m_{i'}` vanishes on `P`,
then `Λ(m) = [m_i]_P Λ(m with 𝟙_P in the slot i)`. [PROVED] -/
theorem form_eq_avg_mul_of_vanishes (T : PerfectCZForm d n) (m : Fin n → TestFun d)
    (i i' : Fin n) (hii' : i ≠ i') (P : DyadicCube d)
    (hs : SupportedOn (m i : (Fin d → ℝ) → ℝ) P) (hv : VanishesOn (m i' : (Fin d → ℝ) → ℝ) P) :
    T.form m = avg P (m i : (Fin d → ℝ) → ℝ) * T.form (Function.update m i (TestFun.ind P)) := by
  have hsplit : m = Function.update m i
      ((m i - avg P (m i : (Fin d → ℝ) → ℝ) • TestFun.ind P) +
        avg P (m i : (Fin d → ℝ) → ℝ) • TestFun.ind P) := by
    rw [sub_add_cancel, Function.update_eq_self]
  have h0 : T.form (Function.update m i
      (m i - avg P (m i : (Fin d → ℝ) → ℝ) • TestFun.ind P)) = 0 := by
    refine T.smooth P _ i i' hii' ?_ ?_ ?_
    · rw [Function.update_self]
      intro x hx
      simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        TestFun.coe_ind, hs x hx, Set.indicator_of_notMem hx, mul_zero, sub_zero]
    · rw [Function.update_self]
      change ∫ x, ((m i - avg P (m i : (Fin d → ℝ) → ℝ) • TestFun.ind P : TestFun d) :
        (Fin d → ℝ) → ℝ) x = 0
      rw [← TestFun.integralₗ_apply, map_sub, map_smul, TestFun.integralₗ_apply,
        TestFun.integralₗ_apply, TestFun.integral_ind, smul_eq_mul,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hs x hx), ← avg_mul_vol,
        sub_self]
    · rw [Function.update_of_ne hii'.symm]
      exact hv
  conv_lhs => rw [hsplit]
  rw [MultilinearMap.map_update_add, MultilinearMap.map_update_smul, smul_eq_mul, h0, zero_add]

/-- **The off-diagonal factorization**: if every slot `j` has a slot `j'` whose cube `R_{j'}` is
disjoint from `R_j`, then `Λ(g) = ∏_j [g_j]_{R_j} · Λ(𝟙_{R_1}, …, 𝟙_{R_n})` for `g_j` supported on
`R_j`. [PROVED] -/
theorem form_eq_prod_avg_mul (T : PerfectCZForm d n) (g : Fin n → TestFun d)
    (R : Fin n → DyadicCube d) (hs : ∀ j, SupportedOn (g j : (Fin d → ℝ) → ℝ) (R j))
    (hoff : ∀ j, ∃ j', j' ≠ j ∧ Disjoint (R j').toSet (R j).toSet) :
    T.form g = (∏ j, avg (R j) (g j : (Fin d → ℝ) → ℝ)) * T.form (fun j => TestFun.ind (R j)) := by
  have key : ∀ S : Finset (Fin n), T.form g = (∏ j ∈ S, avg (R j) (g j : (Fin d → ℝ) → ℝ)) *
      T.form (fun j => if j ∈ S then TestFun.ind (R j) else g j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      obtain ⟨a', ha', hdis⟩ := hoff a
      have h := form_eq_avg_mul_of_vanishes T (fun j => if j ∈ S then TestFun.ind (R j) else g j)
        a a' (Ne.symm ha') (R a) (by simpa [ha] using hs a) (by
          intro x hx
          have hx' : x ∉ (R a').toSet := Set.disjoint_right.mp hdis hx
          split_ifs with h'
          · rw [TestFun.coe_ind]
            exact Set.indicator_of_notMem hx' _
          · exact hs a' x hx')
      have e1 : (if a ∈ S then TestFun.ind (R a) else g a) = g a := by simp [ha]
      have e2 : Function.update (fun j => if j ∈ S then TestFun.ind (R j) else g j) a
          (TestFun.ind (R a)) = fun j => if j ∈ insert a S then TestFun.ind (R j) else g j := by
        funext j
        by_cases hj : j = a
        · subst hj
          simp
        · simp [hj]
      rw [ih, h, e1, e2, Finset.prod_insert ha]
      ring
  simpa using key Finset.univ

/-- `(2^{Md})^{-n} 2^{Md} = (2^{-d(n-1)})^M`. [PROVED] -/
theorem two_pow_inv_pow_mul (hn : 1 ≤ n) (M : ℕ) :
    ((2 : ℝ) ^ (M * d))⁻¹ ^ n * 2 ^ (M * d) = (((2 : ℝ) ^ (d * (n - 1)))⁻¹) ^ M := by
  have h1 : ((2 : ℝ) ^ (M * d)) ^ n = ((2 : ℝ) ^ (d * (n - 1))) ^ M * 2 ^ (M * d) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [inv_pow, h1, mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one, inv_pow]

/-- **The bound for one term of the quadrant decomposition**: `C₁ ∏ ‖f_j‖_{p_j}` on the diagonal
(all cubes equal), `A₀ ∏ ‖f_j‖₁ 2^{-Md(n-1)}` off the diagonal. [PROVED] -/
theorem abs_form_quad_le (hn : 2 ≤ n) {T : PerfectCZForm d n} {p : HolderTuple n} {C₁ A : ℝ}
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ (R : DyadicCube d) (f : Fin n → TestFun d),
      (∀ j, SupportedOn (f j : (Fin d → ℝ) → ℝ) R) → |T.form f| ≤ C₁ * prodNorm p f)
    (hA0 : 0 ≤ A) (hA : ∀ f : Fin n → TestFun d, |T.form f| ≤ A * prodNorm p f) (M : ℕ)
    (r : Fin n → (Fin d → Bool)) (f : Fin n → TestFun d) :
    |T.form (fun j => TestFun.truncateₗ (quad M (r j)) (f j))| ≤
      C₁ * prodNorm p f +
        A * (∏ j, lpNorm (f j : (Fin d → ℝ) → ℝ) 1) * (((2 : ℝ) ^ (d * (n - 1)))⁻¹) ^ M := by
  have hp : ∀ j, 0 < p.p j := fun j => by linarith [p.one_lt j]
  have hL1 : 0 ≤ ∏ j, lpNorm (f j : (Fin d → ℝ) → ℝ) 1 :=
    Finset.prod_nonneg fun j _ => lpNorm_nonneg _ _
  have hnn : 0 ≤ A * (∏ j, lpNorm (f j : (Fin d → ℝ) → ℝ) 1) *
      (((2 : ℝ) ^ (d * (n - 1)))⁻¹) ^ M := by positivity
  have hV : ∀ κ, (quad M κ).vol = 2 ^ (M * d) := quad_vol M
  have hprod : prodNorm p (fun j => TestFun.truncateₗ (quad M (r j)) (f j)) ≤ prodNorm p f :=
    Finset.prod_le_prod₀ (fun j _ => lpNorm_nonneg _ _) fun j _ =>
      TestFun.lpNorm_truncateₗ_le _ _ (hp j)
  let j₀ : Fin n := ⟨0, by omega⟩
  by_cases hconst : ∀ j, r j = r j₀
  · -- the diagonal: all truncations live on the cube `quad M (r j₀)`
    have hsupp : ∀ j, SupportedOn ((TestFun.truncateₗ (quad M (r j)) (f j) : TestFun d) :
        (Fin d → ℝ) → ℝ) (quad M (r j₀)) := fun j => by
      rw [← hconst j]
      exact TestFun.truncateₗ_supportedOn _ _
    have h := hC₁ _ _ hsupp
    linarith [mul_le_mul_of_nonneg_left hprod hC₁0]
  · -- off the diagonal: the factorization and the a priori bound
    obtain ⟨j₁, hj₁⟩ := not_forall.mp hconst
    have hoff : ∀ j, ∃ j', j' ≠ j ∧ Disjoint (quad M (r j')).toSet (quad M (r j)).toSet := by
      intro j
      by_cases hj : r j = r j₀
      · exact ⟨j₁, fun e => hj₁ (by rw [e, hj]), quad_disjoint (by rw [hj]; exact hj₁)⟩
      · exact ⟨j₀, fun e => hj (by rw [e]), quad_disjoint (Ne.symm hj)⟩
    rw [form_eq_prod_avg_mul T _ (fun j => quad M (r j))
      (fun j => TestFun.truncateₗ_supportedOn _ _) hoff, abs_mul, Finset.abs_prod]
    have hind : prodNorm p (fun j => TestFun.ind (quad M (r j))) = 2 ^ (M * d) := by
      unfold prodNorm
      simp only [TestFun.lpNorm_ind _ (hp _), hV]
      rw [← Real.rpow_sum_of_pos (by positivity), p.sum_one_div, Real.rpow_one]
    have havg : ∀ j, |avg (quad M (r j))
        ((TestFun.truncateₗ (quad M (r j)) (f j) : TestFun d) : (Fin d → ℝ) → ℝ)| ≤
        ((2 : ℝ) ^ (M * d))⁻¹ * lpNorm (f j : (Fin d → ℝ) → ℝ) 1 := fun j => by
      have h := abs_avg_le (quad M (r j)) (TestFun.truncateₗ (quad M (r j)) (f j)) le_rfl
      rw [one_div_one, Real.rpow_neg_one, hV] at h
      exact h.trans (mul_le_mul_of_nonneg_left (TestFun.lpNorm_truncateₗ_le _ _ zero_lt_one)
        (by positivity))
    have hρ := two_pow_inv_pow_mul (d := d) (by omega : 1 ≤ n) M
    calc (∏ j, |avg (quad M (r j))
            ((TestFun.truncateₗ (quad M (r j)) (f j) : TestFun d) : (Fin d → ℝ) → ℝ)|) *
          |T.form (fun j => TestFun.ind (quad M (r j)))|
        ≤ (∏ j, ((2 : ℝ) ^ (M * d))⁻¹ * lpNorm (f j : (Fin d → ℝ) → ℝ) 1) *
            (A * prodNorm p (fun j => TestFun.ind (quad M (r j)))) :=
          mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => havg j) (hA _)
            (abs_nonneg _)
            (Finset.prod_nonneg fun _ _ => mul_nonneg (by positivity) (lpNorm_nonneg _ _))
      _ = A * (∏ j, lpNorm (f j : (Fin d → ℝ) → ℝ) 1) * (((2 : ℝ) ^ (d * (n - 1)))⁻¹) ^ M := by
          rw [hind, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← hρ]
          ring
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hC₁0 (prodNorm_nonneg p f))

/-- **Theorem 1.3** (perfect multilinear local `T(1)` theorem), with explicit hypotheses:
`|Λ(f)| ≤ C ∏ ‖f_j‖_{p_j}` with `C` depending only on `d`, `n`, `B` and the exponents. The tuple
is decomposed over the `2^d` cubes of side `2^M` at the origin; the diagonal terms are bounded by
the local bound, the off-diagonal terms are `O(2^{-Md(n-1)})` by the a priori bound of the form,
and `M → ∞`. [PROVED] -/
theorem localT1_core (hd : d ≠ 0) (hn : 2 ≤ n) (p : HolderTuple n) {B : ℝ} (hB : 1 ≤ B) :
    ∃ C : ℝ, ∀ T : PerfectCZForm d n, T1Testing T p B →
      ∀ f : Fin n → TestFun d, |T.form f| ≤ C * prodNorm p f := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := abs_form_le_of_supported hd hB
  refine ⟨((2 : ℝ) ^ d) ^ n * C₁, fun T hT f => ?_⟩
  -- the box containing the supports
  choose Mf hMf using fun j => TestFun.exists_abs_lt_pow (f j)
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, ∀ j, Mf j ≤ M₀ :=
    ⟨∑ j, Mf j, fun j => Finset.single_le_sum (f := Mf) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)⟩
  have hbox : ∀ M, M₀ ≤ M → ∀ j x, (f j : (Fin d → ℝ) → ℝ) x ≠ 0 → ∀ i, |x i| < 2 ^ M :=
    fun M hM j x hx i =>
      (hMf j x hx i).trans_le (pow_le_pow_right₀ one_le_two ((hM₀ j).trans hM))
  -- the a priori bound of the form
  obtain ⟨A, hA0, hA⟩ := T.exists_bound p
  -- the decomposition over the cubes at the origin
  have hdecomp : ∀ M, M₀ ≤ M → T.form f = ∑ r : Fin n → (Fin d → Bool),
      T.form (fun j => TestFun.truncateₗ (quad M (r j)) (f j)) := by
    intro M hM
    conv_lhs => rw [show f = fun j => ∑ κ : Fin d → Bool, TestFun.truncateₗ (quad M κ) (f j) from
      funext fun j => (sum_truncateₗ_quad (f j) (hbox M hM j)).symm]
    exact MultilinearMap.map_sum T.form (fun j κ => TestFun.truncateₗ (quad M κ) (f j))
  have hbound : ∀ M, M₀ ≤ M → |T.form f| ≤ ((2 : ℝ) ^ d) ^ n * C₁ * prodNorm p f +
      ((2 : ℝ) ^ d) ^ n * (A * ∏ j, lpNorm (f j : (Fin d → ℝ) → ℝ) 1) *
        (((2 : ℝ) ^ (d * (n - 1)))⁻¹) ^ M := by
    intro M hM
    rw [hdecomp M hM]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun r _ => abs_form_quad_le hn hC₁0 (hC₁ T hT) hA0 hA M r f).trans
      (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  -- let `M → ∞`
  have hρ0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (d * (n - 1)))⁻¹ := by positivity
  have hρ1 : ((2 : ℝ) ^ (d * (n - 1)))⁻¹ < 1 := by
    refine inv_lt_one_of_one_lt₀ (one_lt_pow₀ one_lt_two ?_)
    have : 0 < d * (n - 1) := Nat.mul_pos (Nat.pos_of_ne_zero hd) (by omega)
    omega
  have hlim : Filter.Tendsto (fun M : ℕ => ((2 : ℝ) ^ d) ^ n * C₁ * prodNorm p f +
      ((2 : ℝ) ^ d) ^ n * (A * ∏ j, lpNorm (f j : (Fin d → ℝ) → ℝ) 1) *
        (((2 : ℝ) ^ (d * (n - 1)))⁻¹) ^ M) Filter.atTop
      (nhds (((2 : ℝ) ^ d) ^ n * C₁ * prodNorm p f +
        ((2 : ℝ) ^ d) ^ n * (A * ∏ j, lpNorm (f j : (Fin d → ℝ) → ℝ) 1) * 0)) :=
    tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨M₀, hbound⟩)

/-- **Theorem 1.3** (perfect multilinear local `T(1)` theorem). [PROVED] -/
theorem localT1 (p : HolderTuple n) : LocalT1 d n p :=
  fun hd hn _ hB => localT1_core (by omega) hn p hB

/-- **Theorem 1.4**, unconditionally: the local `T(b)` theorem for paths of every length
`1 ≤ k ≤ n`, `n ≥ 2`. [PROVED] -/
theorem localTb_unconditional (hn : 2 ≤ n) (p : HolderTuple n) :
    ∀ k, 1 ≤ k → k ≤ n → LocalTb d n k p :=
  localTb hn p (localT1 p)

/-- **The global `T(b)` variant**, unconditionally, with the hypotheses of `GlobalTb`. -/
theorem globalTb_unconditional (hn : 2 ≤ n) (p : HolderTuple n) : GlobalTb d n p :=
  globalTb hn p (localT1 p)

/-- A Hölder tuple of finite exponents has at least two entries: for `n = 1` the conditions
`1 < p₁` and `1/p₁ = 1` are incompatible. Hence the case `n = 1` of Theorem 1.4 (allowed by the
paper's `n ≥ min(k, 2)` for `k = 1`) is void. [PROVED] -/
theorem HolderTuple.two_le (p : HolderTuple n) : 2 ≤ n := by
  by_contra h
  have h1 : n = 1 := by
    have := p.pos
    omega
  subst h1
  have hs := p.sum_inv
  rw [Fin.sum_univ_one, inv_eq_one] at hs
  exact absurd hs (p.one_lt 0).ne'

/-- **Theorem 1.4 in the paper's full range**: `LocalTb d n k p` for all `n`, `k` and every
Hölder tuple `p`. For `k = 0` or `k > n` the statement is vacuous (the hypotheses `1 ≤ k ≤ n` are
part of `LocalTb`), and `n ≥ 2` holds automatically (`HolderTuple.two_le`), so this covers the
paper's range `k ≥ 1`, `n ≥ min(k, 2)`. [PROVED] -/
theorem localTb_all (p : HolderTuple n) (k : ℕ) : LocalTb d n k p := by
  intro hd hk1 hkn
  exact localTb_unconditional p.two_le p k hk1 hkn hd hk1 hkn

/-- **The global `T(b)` variant**: `GlobalTb d n p` for every Hölder tuple `p`, with locally
dyadic testing functions, scale-normalized weak boundedness, and finite-Hardy-norm BMO tests. -/
theorem globalTb_all (p : HolderTuple n) : GlobalTb d n p :=
  globalTb_unconditional p.two_le p

end T1Theorem

end Bridge

end MirekThiele
