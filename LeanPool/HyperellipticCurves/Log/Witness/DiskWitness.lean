/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Ftau.TauGeneric
public import LeanPool.HyperellipticCurves.Log.Witness.DiskPencil

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial

/-!
# The per-disk witness (`lem:global-generic`, per-disk half)

The per-disk configuration of `lem:global-generic` is the three-block pipeline
`[P₀ + ι Q] + τ + [Q + ι P₀]`, with `P₀ = (a, b)` the disk centre and `Q = (x_Q, y_Q)` an
auxiliary point. Both of its reduction steps are conditional
(`ChabautyColeman.isPipelineCenterCerts_of_pair_blocks`), and this file discharges every
remaining condition by choosing `Q` on the pencil of
`LeanPool.HyperellipticCurves.Log.Witness.DiskPencil`.

The two ends of the pipeline are the *same* interpolating curve:

* stage 1 composes to the pencil member `V_t`
  (`ChabautyColeman.cantorCompose_pencil`), whose residual with `Q` removed is the
  Cantor cofactor (`ChabautyColeman.mul_cantorCofactor_pencil`);
* stage 3 composes to `-V_t` (`ChabautyColeman.cantorCompose_pencil_three`), so the second
  step's degree condition *is* the first one, and the pipeline returns `τ`.

What remains are three conditions on the residual, all supplied by
`ChabautyColeman.exists_pencil_param`: it must not vanish at `a` or (to first order) at
`x_Q` — transversality of `y = V_t(x)` at `P₀` and at `ι Q`, which frees the second Bézout
certificate — and it must miss the Weierstrass points. The result is
`ChabautyColeman.exists_isPipelineCerts_disk`: over an algebraically closed field every
nonsingular disk centre — `b ≠ 0`, or `a` a simple root of `f` — off the support of `τ`
admits an auxiliary point making the configuration generic and avoiding
(`ChabautyColeman.IsPipelineAvoid` constrains only the *reduced* data, which at a
Weierstrass centre the order cancellation at `a` keeps Weierstrass-free), with the CRT
coprimality of the reduced stage-2 `u`-part with the pair block, for every choice of the
interpolating `v`-part of the two pair blocks.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Pair

variable {R : Type*} [CommRing R]

theorem monic_pairU (a xQ : R) : ((X - C a) * (X - C xQ)).Monic :=
  (monic_X_sub_C a).mul (monic_X_sub_C xQ)

theorem natDegree_pairU [Nontrivial R] (a xQ : R) : ((X - C a) * (X - C xQ)).natDegree = 2 := by
  compute_degree!

end Pair

section DiskWitness

variable {K : Type*} [Field K] {f uτ vτ v₁ : K[X]} {a b t xQ : K} {g : ℕ}

/-- The **per-disk residue configuration** `[P₀ + ι Q] + τ + [Q + ι P₀]` over a field: the
two pair blocks around the disk centre `a` and the auxiliary point `xQ`, with the `τ`-block
between them. It is the reduction of `ChabautyColeman.phiConfig`, and its two outer blocks
carry inverse classes. -/
@[simps] noncomputable def pencilConfig (a xQ : K) (v₁ uτ vτ : K[X]) : PipelineData K :=
  ⟨(X - C a) * (X - C xQ), v₁, uτ, vτ, (X - C xQ) * (X - C a), -v₁⟩

/-- The `u`-part of the per-disk stage-1 composite divides the curve relation of the pencil
member — the composite is `[P₀ + ι Q] + τ`, whose square root the member is. -/
theorem pair_mul_dvd_pencilV_sq_sub (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0) :
    (X - C a) * (X - C xQ) * uτ ∣ pencilV uτ vτ a b t ^ 2 - f :=
  ⟨pencilW f uτ vτ a b t /ₘ (X - C xQ), by
    rw [pencilW_spec hu hne hd hb, pencilU]
    linear_combination (uτ * (X - C a)) * (mul_divByMonic_eq_iff_isRoot.mpr hxW).symm⟩

/-- **The residual of the per-disk configuration is the pencil residual with `Q` removed**:
composing the pair block at `P₀` and `ι Q` with `τ` gives the pencil member, whose residual
already contains `Q`. -/
theorem mul_cantorCofactor_pencil (hu : uτ.Monic) (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f)
    (hb : b ^ 2 = f.eval a) (hxW : (pencilW f uτ vτ a b t).eval xQ = 0) :
    (X - C xQ) * cantorCofactor f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)
      = pencilW f uτ vτ a b t := by
  have hfac : (X - C xQ) * (pencilW f uτ vτ a b t /ₘ (X - C xQ)) = pencilW f uτ vτ a b t :=
    mul_divByMonic_eq_iff_isRoot.mpr hxW
  have hspec : pencilV uτ vτ a b t ^ 2 - f
      = (X - C a) * (X - C xQ) * uτ * (pencilW f uτ vτ a b t /ₘ (X - C xQ)) := by
    rw [pencilW_spec hu hne hd hb, pencilU]
    linear_combination (uτ * (X - C a)) * hfac.symm
  rwa [cantorCofactor, hspec, mul_divByMonic_cancel_left _ ((monic_pairU a xQ).mul hu)]

/-- The pair block is a Mumford datum: any polynomial agreeing with the pencil member at
`P₀` and at `ι Q` is a square root of `f` modulo the pair. -/
theorem pair_dvd_sq_sub (hu : uτ.Monic) (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f)
    (hb : b ^ 2 = f.eval a) (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (hv₁ : (X - C a) * (X - C xQ) ∣ pencilV uτ vτ a b t - v₁) :
    (X - C a) * (X - C xQ) ∣ v₁ ^ 2 - f := by
  obtain ⟨c, hc⟩ := hv₁
  obtain ⟨e, he⟩ := pair_mul_dvd_pencilV_sq_sub hu hne hd hb hxW
  exact ⟨uτ * e - c * (pencilV uτ vτ a b t + v₁), by
    linear_combination he - (pencilV uτ vτ a b t + v₁) * hc⟩

theorem eval_cantorCofactor_pencil_left (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (haW : (pencilW f uτ vτ a b t).eval a ≠ 0) :
    (cantorCofactor f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).eval a ≠ 0 :=
  fun h0 ↦ haW (by
    have := congrArg (eval a) (mul_cantorCofactor_pencil hu hne hd hb hxW)
    simpa [h0] using this.symm)

theorem eval_cantorCofactor_pencil_right (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (hxW' : (pencilW f uτ vτ a b t).derivative.eval xQ ≠ 0) :
    (cantorCofactor f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).eval xQ ≠ 0 :=
  fun h0 ↦ hxW' (by
    have := congrArg (fun p ↦ p.derivative.eval xQ)
      (mul_cantorCofactor_pencil hu hne hd hb hxW)
    simpa [h0] using this.symm)

/-- **Stage 1 of the per-disk pipeline is the pencil member**: composing the pair block at
`P₀` and `ι Q` with `τ` gives `([P₀ + ι Q] + τ, V_t)`. -/
theorem cantorCompose_pencil {s₁ s₂ s₃ : K[X]} (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a) (hv : vτ.degree < uτ.degree)
    (ht0 : t ≠ 0) (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (hcop : IsCoprime ((X - C a) * (X - C xQ)) uτ)
    (hbez : s₁ * ((X - C a) * (X - C xQ)) + s₂ * uτ + s₃ * (v₁ + vτ) = 1)
    (hv₁ : (X - C a) * (X - C xQ) ∣ pencilV uτ vτ a b t - v₁) :
    cantorCompose f ((X - C a) * (X - C xQ)) v₁ uτ vτ s₁ s₂ s₃
      = ((X - C a) * (X - C xQ) * uτ, pencilV uτ vτ a b t) :=
  Prod.ext rfl (eq_cantorCompose_snd (monic_pairU a xQ) hu hcop hbez
    (cantorCofactor_spec f (monic_pairU a xQ) (pair_dvd_sq_sub hu hne hd hb hxW hv₁))
    (cantorCofactor_spec f hu hd) hv₁ dvd_pencilV_sub
    (degree_lt_degree (by rw [(monic_pairU a xQ).natDegree_mul hu, natDegree_pairU,
      natDegree_pencilV ht0 hu hv]; lia))).symm

theorem cantorCofactor_pencil_ne_zero (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (haW : (pencilW f uτ vτ a b t).eval a ≠ 0) :
    cantorCofactor f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t) ≠ 0 :=
  fun h0 ↦ eval_cantorCofactor_pencil_left hu hne hd hb hxW haW (by rw [h0, eval_zero])

/-- The reduced stage-2 datum is the normalized cofactor, so its values are those of the
cofactor up to a unit. -/
theorem isCoprime_reduceCanon_pencil_iff {q : K[X]} (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (haW : (pencilW f uτ vτ a b t).eval a ≠ 0) :
    IsCoprime (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1 q
      ↔ IsCoprime (cantorCofactor f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)) q := by
  rw [reduceCanon_fst]
  exact isCoprime_mul_unit_left_left (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (inv_ne_zero (leadingCoeff_ne_zero.mpr (cantorCofactor_pencil_ne_zero hu hne hd hb hxW haW)))))
    _ _

/-- **The reduced stage-2 datum of the pencil misses the Weierstrass points.** Away from the
centre this is the curve-avoidance clause `hfW` of the pencil member; at the centre itself
the residual is nonzero by transversality (`haW` — at a Weierstrass centre the orders of
`V² - f` and of the configuration's `u`-part at `a` cancel). -/
theorem isCoprime_cantorCofactor_pencil [IsAlgClosed K] (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a) (hf0 : f ≠ 0)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (haW : (pencilW f uτ vτ a b t).eval a ≠ 0)
    (hfW : ∀ r, f.eval r = 0 → r ≠ a → (pencilV uτ vτ a b t).eval r ≠ 0) :
    IsCoprime (cantorCofactor f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)) f := by
  refine isCoprime_of_forall_eval_ne_zero hf0 fun x hx hfx ↦ ?_
  rcases eq_or_ne x a with rfl | hxa
  · exact eval_cantorCofactor_pencil_left hu hne hd hb hxW haW hx
  · refine hfW x hfx hxa ?_
    have hspec := congrArg (eval x) (cantorCofactor_spec f ((monic_pairU a xQ).mul hu)
      (pair_mul_dvd_pencilV_sq_sub hu hne hd hb hxW))
    simp only [eval_sub, eval_mul, eval_pow] at hspec
    rw [hx, mul_zero, hfx] at hspec
    exact (pow_eq_zero_iff two_ne_zero).mp (by linear_combination hspec)

/-- **The first per-disk reduction step is generic**: the composite
`[P₀ + ι Q] + τ` reduces without a degree drop exactly because the pencil member has top
degree. -/
theorem reduceGeneric_pencil (hu : uτ.Monic) (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f)
    (hb : b ^ 2 = f.eval a) (hv : vτ.degree < uτ.degree) (ht0 : t ≠ 0)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    ReduceGeneric f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t) := by
  have hdeg : ((X - C a) * (X - C xQ) * uτ).natDegree = 2 + uτ.natDegree := by
    rw [(monic_pairU a xQ).natDegree_mul hu, natDegree_pairU]
  rw [reduceGeneric_iff ((monic_pairU a xQ).mul hu)
      (pair_mul_dvd_pencilV_sq_sub hu hne hd hb hxW)
      (degree_lt_degree (by rw [hdeg, natDegree_pencilV ht0 hu hv]; lia))
      (by rw [hfdeg]; exact ⟨uτ.natDegree, by lia⟩) (by rw [hfdeg, hdeg]; lia),
    natDegree_pencilV ht0 hu hv, hdeg]
  lia

/-- The reduced stage-2 datum has the degree of `τ`: the pipeline is back to a reduced
divisor of full degree after one step. -/
theorem natDegree_reduceCanon_pencil (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a) (hv : vτ.degree < uτ.degree) (ht0 : t ≠ 0)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1.natDegree
      = uτ.natDegree := by
  rw [(reduceGeneric_pencil hu hne hd hb hv ht0 hxW hfdeg).reduceCanon_natDegree,
    (monic_pairU a xQ).natDegree_mul hu, natDegree_pairU, hfdeg, genericDeg_pair_compose]

/-- **Stage 3 of the per-disk pipeline is the negated pencil member**: the reduced stage-2
datum and the block `[Q + ι P₀]` are cut out by the same interpolating curve, so the second
reduction step is generic for the same reason as the first — and the pipeline returns `τ`. -/
theorem cantorCompose_pencil_three {t₁ t₂ t₃ : K[X]} (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a) (hv : vτ.degree < uτ.degree) (ht0 : t ≠ 0)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hcop : IsCoprime (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
      ((X - C a) * (X - C xQ)))
    (hbez : t₁ * (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
        + t₂ * ((X - C a) * (X - C xQ))
        + t₃ * ((reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).2 + -v₁)
      = 1)
    (hv₁ : (X - C a) * (X - C xQ) ∣ pencilV uτ vτ a b t - v₁) :
    cantorCompose f (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
        (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).2
        ((X - C a) * (X - C xQ)) (-v₁) t₁ t₂ t₃
      = ((reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
          * ((X - C a) * (X - C xQ)), -(pencilV uτ vτ a b t)) := by
  have hgen := reduceGeneric_pencil hu hne hd hb hv ht0 hxW hfdeg
  obtain ⟨hmon, hdvd⟩ := hgen.reduceCanon_monic_dvd ((monic_pairU a xQ).mul hu)
    (pair_mul_dvd_pencilV_sq_sub hu hne hd hb hxW)
  have hdeg := natDegree_reduceCanon_pencil hu hne hd hb hv ht0 hxW hfdeg
  refine Prod.ext rfl (eq_cantorCompose_snd hmon (monic_pairU a xQ) hcop hbez
    (cantorCofactor_spec f hmon hdvd)
    (cantorCofactor_spec f (monic_pairU a xQ) (by
          rw [neg_pow, even_two.neg_one_pow, one_mul]
          exact pair_dvd_sq_sub hu hne hd hb hxW hv₁))
    (dvd_sub_comm.mp (dvd_modByMonic_sub _ _)) ?_ ?_).symm
  · rw [neg_sub_neg]
    exact dvd_sub_comm.mp hv₁
  · exact degree_lt_degree (by
      rw [hmon.natDegree_mul (monic_pairU a xQ), hdeg, natDegree_pairU, natDegree_neg,
        natDegree_pencilV ht0 hu hv]
      lia)

/-- **The second per-disk reduction step is generic**, for the same
reason as the first: its composed square root is again the pencil member, negated. -/
theorem reduceGeneric_pencil_three {t₁ t₂ t₃ : K[X]} (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a) (hv : vτ.degree < uτ.degree) (ht0 : t ≠ 0)
    (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hcop : IsCoprime (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
      ((X - C a) * (X - C xQ)))
    (hbez : t₁ * (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
        + t₂ * ((X - C a) * (X - C xQ))
        + t₃ * ((reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).2 + -v₁)
      = 1)
    (hv₁ : (X - C a) * (X - C xQ) ∣ pencilV uτ vτ a b t - v₁) :
    ReduceGeneric f ((reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
      * ((X - C a) * (X - C xQ))) (-(pencilV uτ vτ a b t)) := by
  obtain ⟨hmon, hdvd⟩ := (reduceGeneric_pencil hu hne hd hb hv ht0 hxW hfdeg).reduceCanon_monic_dvd
    ((monic_pairU a xQ).mul hu) (pair_mul_dvd_pencilV_sq_sub hu hne hd hb hxW)
  have hd₃ : (X - C a) * (X - C xQ) ∣ (-v₁) ^ 2 - f := by
    rw [neg_pow, even_two.neg_one_pow, one_mul]
    exact pair_dvd_sq_sub hu hne hd hb hxW hv₁
  have hdeg : ((reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
      * ((X - C a) * (X - C xQ))).natDegree = uτ.natDegree + 2 := by
    rw [hmon.natDegree_mul (monic_pairU a xQ),
      natDegree_reduceCanon_pencil hu hne hd hb hv ht0 hxW hfdeg, natDegree_pairU]
  have hdvd₃ : (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
      * ((X - C a) * (X - C xQ)) ∣ (-(pencilV uτ vτ a b t)) ^ 2 - f := by
    have h := cantorCompose_dvd f hbez hdvd hd₃
    rwa [cantorCompose_pencil_three hu hne hd hb hv ht0 hxW hfdeg hcop hbez hv₁] at h
  rw [reduceGeneric_iff (hmon.mul (monic_pairU a xQ)) hdvd₃
      (degree_lt_degree (by rw [hdeg, natDegree_neg, natDegree_pencilV ht0 hu hv]; lia))
      (by rw [hfdeg]; exact ⟨uτ.natDegree, by lia⟩) (by rw [hfdeg, hdeg]; lia),
    natDegree_neg, natDegree_pencilV ht0 hu hv, hdeg]
  lia

/-- **The per-disk certificate pack at a good pencil parameter** (`lem:global-generic`, the
per-disk half): the configuration `[P₀ + ι Q] + τ + [Q + ι P₀]` cut out by the pencil member
at a good parameter carries a full certificate pack, Weierstrass avoidance at both
reduced data, and the CRT input — the reduced stage-2 `u`-part is coprime to the pair
block. Only the curve-avoidance of the composed cofactor depends on whether the centre is
generic or a Weierstrass point, and it enters as `hWf`. -/
theorem exists_isPipelineCerts_pencil_of_isCoprime [IsAlgClosed K] [NeZero (2 : K)]
    [Fact (Odd f.natDegree)] [Fact (Squarefree f)] (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a)
    (hv : vτ.degree < uτ.degree) (hgp : IsCoprime uτ f)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1) (ht0 : t ≠ 0)
    (hxU : (pencilU uτ a).eval xQ ≠ 0) (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (haW : (pencilW f uτ vτ a b t).eval a ≠ 0)
    (hxW' : (pencilW f uτ vτ a b t).derivative.eval xQ ≠ 0)
    (hWf : IsCoprime (cantorCofactor f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)) f)
    (hv₁ : (X - C a) * (X - C xQ) ∣ pencilV uτ vτ a b t - v₁) :
    ∃ d : CantorCertData K,
      IsPipelineCenterCerts f (pencilConfig a xQ v₁ uτ vτ)
          d uτ.natDegree
        ∧ IsPipelineAvoid f (pencilConfig a xQ v₁ uτ vτ) d
        ∧ IsCoprime (cantorStage₂ f (pencilConfig a xQ v₁ uτ vτ) d).1
          ((X - C a) * (X - C xQ)) := by
  simp only [pencilConfig]
  rw [mul_comm (X - C xQ) (X - C a)]
  set D₀ : PipelineData K :=
    ⟨(X - C a) * (X - C xQ), v₁, uτ, vτ, (X - C a) * (X - C xQ), -v₁⟩
  have h2 : IsUnit (2 : K[X]) := Polynomial.isUnit_two (NeZero.ne (2 : K)).isUnit
  have huxQ : uτ.eval xQ ≠ 0 := fun h0 ↦ hxU (by rw [eval_pencilU, h0, zero_mul])
  have hd₁ := pair_dvd_sq_sub hu hne hd hb hxW hv₁
  have hd₃ : (X - C a) * (X - C xQ) ∣ (-v₁) ^ 2 - f := by
    rwa [neg_pow, even_two.neg_one_pow, one_mul]
  have hdvdc := pair_mul_dvd_pencilV_sq_sub hu hne hd hb hxW
  have hgen₁ := reduceGeneric_pencil hu hne hd hb hv ht0 hxW hfdeg
  -- the two Bézout certificates come from coprimality of the `u`-parts
  obtain ⟨s₁, s₂, hs⟩ : IsCoprime ((X - C a) * (X - C xQ)) uτ :=
    ((isCoprime_X_sub_C_of_eval_ne_zero hne).mul_right
      (isCoprime_X_sub_C_of_eval_ne_zero huxQ)).symm
  have hbez₁ : s₁ * ((X - C a) * (X - C xQ)) + s₂ * uτ + 0 * (v₁ + vτ) = 1 := by
    linear_combination hs
  have hcof₂ : IsCoprime (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
      ((X - C a) * (X - C xQ)) :=
    (isCoprime_reduceCanon_pencil_iff hu hne hd hb hxW haW).mpr
      ((isCoprime_X_sub_C_of_eval_ne_zero
          (eval_cantorCofactor_pencil_left hu hne hd hb hxW haW)).mul_right
        (isCoprime_X_sub_C_of_eval_ne_zero
          (eval_cantorCofactor_pencil_right hu hne hd hb hxW hxW')))
  obtain ⟨t₁, t₂, htb⟩ := hcof₂
  have hbez₂ : t₁ * (reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).1
      + t₂ * ((X - C a) * (X - C xQ))
      + 0 * ((reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t)).2 + -v₁)
      = 1 := by linear_combination htb
  have hS₁ := cantorCompose_pencil hu hne hd hb hv ht0 hxW ⟨s₁, s₂, hs⟩ hbez₁ hv₁
  have hS₃ := cantorCompose_pencil_three hu hne hd hb hv ht0 hxW hfdeg ⟨t₁, t₂, htb⟩ hbez₂ hv₁
  have hgen₂ := reduceGeneric_pencil_three hu hne hd hb hv ht0 hxW hfdeg ⟨t₁, t₂, htb⟩ hbez₂ hv₁
  have hcopf : ReduceCoprimeCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t) := by
    rw [reduceCoprimeCanon_iff h2 ((monic_pairU a xQ).mul hu) hdvdc
        (cantorCofactor_pencil_ne_zero hu hne hd hb hxW haW),
      isCoprime_reduceCanon_pencil_iff hu hne hd hb hxW haW]
    exact hWf
  have hcerts := isPipelineCenterCerts_of_pair_blocks (D := D₀) (g := uτ.natDegree) hfdeg
    (monic_pairU a xQ) hu (monic_pairU a xQ) (natDegree_pairU a xQ) rfl (natDegree_pairU a xQ)
    hd₁ hd hS₁ rfl hS₃ hbez₁ hgen₁ hbez₂ hgen₂
  refine ⟨_, hcerts, isPipelineAvoid_of_pair_blocks (D := D₀) hfdeg (monic_pairU a xQ) hu
    (monic_pairU a xQ) rfl hd₁ hd hd₃ hS₁ rfl hS₃ hcerts
    (mk0_mumfordIdeal_mul_neg f (monic_pairU a xQ) hd₁) hv h2 hgp hcopf, ?_⟩
  have h2eq : cantorStage₂ f D₀ (pipelineCanonData f D₀ s₁ s₂ 0 t₁ t₂ 0)
      = reduceCanon f ((X - C a) * (X - C xQ) * uτ) (pencilV uτ vτ a b t) := by
    rw [cantorStage₂_pipelineCanonData, hS₁]
  rw [h2eq]
  exact ⟨t₁, t₂, htb⟩

/-- **The per-disk certificate pack at a good pencil parameter**: the pack, the avoidance
and the CRT input of `ChabautyColeman.exists_isPipelineCerts_pencil_of_isCoprime`, with the
composed cofactor kept off the curve by `hfW` away from the centre and by transversality
(`haW`) at the centre. -/
theorem exists_isPipelineCerts_pencil [IsAlgClosed K] [NeZero (2 : K)] [Fact (Odd f.natDegree)]
    [Fact (Squarefree f)] (hf : f.Monic) (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a) (hv : vτ.degree < uτ.degree)
    (hgp : IsCoprime uτ f) (hfdeg : f.natDegree = 2 * uτ.natDegree + 1) (ht0 : t ≠ 0)
    (hxU : (pencilU uτ a).eval xQ ≠ 0) (hxW : (pencilW f uτ vτ a b t).eval xQ = 0)
    (haW : (pencilW f uτ vτ a b t).eval a ≠ 0)
    (hxW' : (pencilW f uτ vτ a b t).derivative.eval xQ ≠ 0)
    (hfW : ∀ r, f.eval r = 0 → r ≠ a → (pencilV uτ vτ a b t).eval r ≠ 0)
    (hv₁ : (X - C a) * (X - C xQ) ∣ pencilV uτ vτ a b t - v₁) :
    ∃ d : CantorCertData K,
      IsPipelineCenterCerts f (pencilConfig a xQ v₁ uτ vτ) d uτ.natDegree
        ∧ IsPipelineAvoid f (pencilConfig a xQ v₁ uτ vτ) d
        ∧ IsCoprime (cantorStage₂ f (pencilConfig a xQ v₁ uτ vτ) d).1
          ((X - C a) * (X - C xQ)) :=
  exists_isPipelineCerts_pencil_of_isCoprime hu hne hd hb hv hgp hfdeg ht0 hxU hxW haW hxW'
    (isCoprime_cantorCofactor_pencil hu hne hd hb hf.ne_zero hxW haW hfW) hv₁

/-- **The per-disk witness** (`lem:global-generic`, the per-disk half): over an algebraically
closed field, for every nonsingular disk centre `P₀ = (a, b)` — `b ≠ 0`, or `a` a simple
root of `f` — off the support of `τ`, there is an auxiliary point `Q = (x_Q, y_Q)` for which
the configuration `[P₀ + ι Q] + τ + [Q + ι P₀]` carries a full certificate pack, Weierstrass
avoidance at both reduced data (`ChabautyColeman.IsPipelineAvoid` constrains only the
*reduced* data, which at a Weierstrass centre the order cancellation at `a` keeps
Weierstrass-free), and the CRT coprimality of the reduced stage-2 `u`-part with the pair
block — for *every* choice of the interpolating `v`-part of the two pair blocks. -/
theorem exists_isPipelineCerts_disk [IsAlgClosed K] [NeZero (2 : K)] [Fact (Odd f.natDegree)]
    [Fact (Squarefree f)] (hf : f.Monic) (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a) (hns : b ≠ 0 ∨ f.derivative.eval a ≠ 0)
    (hv : vτ.degree < uτ.degree) (hgp : IsCoprime uτ f)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    ∃ xQ yQ : K, yQ ^ 2 = f.eval xQ ∧ yQ ≠ 0 ∧ a ≠ xQ ∧ uτ.eval xQ ≠ 0
      ∧ ∀ v₁ : K[X], v₁.eval a = b → v₁.eval xQ = -yQ → ∃ d : CantorCertData K,
        IsPipelineCenterCerts f (pencilConfig a xQ v₁ uτ vτ) d uτ.natDegree
          ∧ IsPipelineAvoid f (pencilConfig a xQ v₁ uτ vτ) d
          ∧ IsCoprime (cantorStage₂ f (pencilConfig a xQ v₁ uτ vτ) d).1
            ((X - C a) * (X - C xQ)) := by
  obtain ⟨t, xQ, ht0, hxU, hxW, haW, hxW', hfW⟩ :=
    exists_pencil_param hf hu hne hd hb hns hv hgp hfdeg rfl
  rw [eval_pencilU] at hxU
  have haxQ : a ≠ xQ := fun h0 ↦ hxU (by rw [h0, sub_self, mul_zero])
  have huxQ : uτ.eval xQ ≠ 0 := fun h0 ↦ hxU (by rw [h0, zero_mul])
  have hsq := eval_pencilV_sq hu hne hd hb hxW
  refine ⟨xQ, -(pencilV uτ vτ a b t).eval xQ, by rwa [neg_pow_two],
    fun h0 ↦ hfW xQ ?_ haxQ.symm (neg_eq_zero.mp h0), haxQ, huxQ, fun v₁ h₁ h₂ ↦ ?_⟩
  · rw [← hsq, neg_eq_zero.mp h0]
    ring
  · exact exists_isPipelineCerts_pencil hf hu hne hd hb hv hgp hfdeg ht0
      (by rwa [eval_pencilU]) hxW haW hxW' hfW
      (pair_dvd_of_eval haxQ (by
        rw [eval_sub, eval_pencilV_base hne, h₁, sub_self])
        (by rw [eval_sub, h₂]; ring))

end DiskWitness

end ChabautyColeman

end
