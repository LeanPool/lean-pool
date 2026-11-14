/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Cantor.CenterGenericity
public import LeanPool.HyperellipticCurves.Log.Trace.TracePipeline

/-!
# The canonical reduction step over a field

Over a field, a valid reduction certificate is forced to be the inverse of the cofactor's
leading coefficient, so a Cantor reduction step is canonical (`ChabautyColeman.reduceCanon`)
and its genericity is the certificate-free condition `ChabautyColeman.ReduceGeneric` — the
cofactor attains its generic degree; Weierstrass avoidance at the reduced datum is
`ChabautyColeman.ReduceCoprimeCanon`.

The assembly is carried out for the **generic three-block pipeline**
(`ChabautyColeman.pipelineCanonData`, whose reduction certificates are the canonical ones): one
canonical pack carries both the validity pack `ChabautyColeman.IsPipelineCenterCerts` and
the Weierstrass avoidance `ChabautyColeman.IsPipelineAvoid`
(`ChabautyColeman.isPipelineCenterCerts_pipelineCanonData`,
`ChabautyColeman.isPipelineAvoid_pipelineCanonData`), so a single witness configuration
settles both.  When the outer blocks are **pair data**, one reduction step per chain returns
to degree `g` for every genus (`ChabautyColeman.isPipelineCenterCerts_of_pair_blocks`,
`ChabautyColeman.isPipelineAvoid_of_pair_blocks`) — this is the form the per-disk pencil of
`LeanPool.HyperellipticCurves.Log.Witness.DiskWitness` consumes (blueprint `lem:global-generic`,
condition
(3)).

Blueprint `lem:tau-generic` is proved by the centre-fold witness of
`LeanPool.HyperellipticCurves.Log.Fold.CenterFold`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {K : Type*} [Field K] {f u v w : K[X]}

section CanonicalStep

variable (f)

/-- The canonical Cantor reduction step over a field: the inverse of the cofactor's leading
coefficient is the certificate. -/
noncomputable def reduceCanon (u v : K[X]) : K[X] × K[X] :=
  cantorReduce f u v (cantorCofactor f u v).leadingCoeff⁻¹

/-- The canonical reduction step normalizes the cofactor. -/
theorem reduceCanon_fst (u v : K[X]) :
    (reduceCanon f u v).1 = C (cantorCofactor f u v).leadingCoeff⁻¹ * cantorCofactor f u v := rfl

/-- **The canonical genericity condition of a reduction step** over a field: the cofactor
attains the generic degree exactly. This is certificate-free — over a field, a valid reduction
certificate is forced to be the inverse of the cofactor's leading coefficient — and it is a
single top-coefficient nonvanishing condition on the datum. -/
def ReduceGeneric (u v : K[X]) : Prop :=
  (cantorCofactor f u v).degree
    = ((max (2 * (u.natDegree - 1)) f.natDegree - u.natDegree : ℕ) : WithBot ℕ)

variable {f}

/-- **The conditional reduction step, as a degree condition on the square root**: when the
square dominates the curve degree, the canonical step is generic exactly when the square root
has exact top degree. This is the form in which a witness checks the condition — for the
per-disk configuration (`ChabautyColeman.isPipelineCenterCerts_of_pair_blocks`) it is the
whole degree content. -/
theorem reduceGeneric_iff (hu : u.Monic) (hd : u ∣ v ^ 2 - f) (hv : v.degree < u.degree)
    (hodd : Odd f.natDegree) (hgt : f.natDegree < 2 * (u.natDegree - 1)) :
    ReduceGeneric f u v ↔ v.natDegree = u.natDegree - 1 := by
  rw [ReduceGeneric, max_eq_left hgt.le,
    degree_eq_iff_natDegree_eq (cantorCofactor_ne_zero hu hd hodd),
    natDegree_cantorCofactor_eq_iff hu hd hv hodd hgt]

theorem ReduceGeneric.cantorCofactor_ne_zero (hgen : ReduceGeneric f u v) :
    cantorCofactor f u v ≠ 0 := fun h0 ↦ by
  rw [ReduceGeneric, h0, degree_zero] at hgen
  exact WithBot.bot_ne_coe hgen

/-- The canonical certificate of a generic step is a valid reduction certificate. -/
theorem ReduceGeneric.reduceCert (hgen : ReduceGeneric f u v) :
    (cantorCofactor f u v).leadingCoeff⁻¹ * (cantorCofactor f u v).leadingCoeff = 1 :=
  inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hgen.cantorCofactor_ne_zero)

/-- A generic step attains the full cofactor degree. -/
theorem ReduceGeneric.fullDeg (hgen : ReduceGeneric f u v) :
    (cantorCofactor f u v).natDegree = max (2 * (u.natDegree - 1)) f.natDegree - u.natDegree :=
  natDegree_eq_of_degree_eq_some hgen

/-- The canonical reduction of a Mumford datum is again a Mumford datum. -/
theorem ReduceGeneric.reduceCanon_monic_dvd (hgen : ReduceGeneric f u v) (hu : u.Monic)
    (hdvd : u ∣ v ^ 2 - f) :
    (reduceCanon f u v).1.Monic ∧ (reduceCanon f u v).1 ∣ (reduceCanon f u v).2 ^ 2 - f :=
  ⟨cantorReduce_monic f hgen.reduceCert, cantorReduce_dvd f hu hdvd hgen.reduceCert⟩

/-- The canonical reduction attains the generic degree. -/
theorem ReduceGeneric.reduceCanon_natDegree (hgen : ReduceGeneric f u v) :
    (reduceCanon f u v).1.natDegree = max (2 * (u.natDegree - 1)) f.natDegree - u.natDegree :=
  natDegree_cantorReduce_of_fullDeg f hgen.reduceCert hgen.fullDeg

variable (f) in
/-- **Weierstrass avoidance at the canonical reduced datum**: the certificate-free counterpart
of the conditions of `ChabautyColeman.IsPipelineAvoid`. By
`ChabautyColeman.isCoprime_two_mul_iff` it says that the reduced `u`-part is coprime to `f`,
i.e. that the reduced divisor misses the Weierstrass points. -/
def ReduceCoprimeCanon (u v : K[X]) : Prop :=
  IsCoprime (reduceCanon f u v).1 (2 * (reduceCanon f u v).2)

/-- **The canonical avoidance condition is coprimality with the curve**: the reduced datum
misses the Weierstrass points. -/
theorem reduceCoprimeCanon_iff (h2 : IsUnit (2 : K[X])) (hu : u.Monic) (hdvd : u ∣ v ^ 2 - f)
    (hne : cantorCofactor f u v ≠ 0) :
    ReduceCoprimeCanon f u v ↔ IsCoprime (reduceCanon f u v).1 f :=
  isCoprime_two_mul_iff h2 (cantorReduce_dvd f hu hdvd
    (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hne)))

end CanonicalStep

section GenericPack

variable {s₁ s₂ s₃ t₁ t₂ t₃ : K[X]} {D : PipelineData K}

variable (f) in
/-- **The canonical certificate pack of the generic three-block pipeline**: the two Bézout
certificates supplied by the caller, and the two canonical reduction certificates. Both the
validity pack (`ChabautyColeman.IsPipelineCenterCerts`) and the Weierstrass avoidance
(`ChabautyColeman.IsPipelineAvoid`) are statements about *this* pack, which is what lets the
two be established for one and the same configuration. -/
noncomputable def pipelineCanonData (D : PipelineData K) (s₁ s₂ s₃ t₁ t₂ t₃ : K[X]) :
    CantorCertData K :=
  let S₁ := cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ s₁ s₂ s₃
  let S₂ := reduceCanon f S₁.1 S₁.2
  ⟨s₁, s₂, s₃, (cantorCofactor f S₁.1 S₁.2).leadingCoeff⁻¹, t₁, t₂, t₃,
    (cantorCofactor f (cantorCompose f S₂.1 S₂.2 D.u₃ D.v₃ t₁ t₂ t₃).1
      (cantorCompose f S₂.1 S₂.2 D.u₃ D.v₃ t₁ t₂ t₃).2).leadingCoeff⁻¹⟩

/-- The second stage of the canonical pack is the canonical reduction of the composed
first stage. -/
theorem cantorStage₂_pipelineCanonData (D : PipelineData K) (s₁ s₂ s₃ t₁ t₂ t₃ : K[X]) :
    cantorStage₂ f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃)
      = reduceCanon f (cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ s₁ s₂ s₃).1
        (cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ s₁ s₂ s₃).2 :=
  rfl

/-- **Field-direct assembly of the pipeline certificate pack**: over a field the reduction
certificates are forced, so a valid and fully generic pack follows from the two Bézout
certificates, the certificate-free canonical conditions at the two reduction steps
(`ChabautyColeman.ReduceGeneric`), and the degree bookkeeping. The three intermediate data
are named by hypotheses, so a caller that knows them in closed form can state the conditions
in that form. -/
theorem isPipelineCenterCerts_pipelineCanonData {S₁ S₂ S₃ : K[X] × K[X]} {n : ℕ}
    (hS₁ : cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ s₁ s₂ s₃ = S₁) (hS₂ : reduceCanon f S₁.1 S₁.2 = S₂)
    (hS₃ : cantorCompose f S₂.1 S₂.2 D.u₃ D.v₃ t₁ t₂ t₃ = S₃)
    (hbez₁ : s₁ * D.u₁ + s₂ * D.u₂ + s₃ * (D.v₁ + D.v₂) = 1) (hgen₁ : ReduceGeneric f S₁.1 S₁.2)
    (hbez₂ : t₁ * S₂.1 + t₂ * D.u₃ + t₃ * (S₂.2 + D.v₃) = 1) (hgen₂ : ReduceGeneric f S₃.1 S₃.2)
    (hn : max (2 * (S₃.1.natDegree - 1)) f.natDegree - S₃.1.natDegree = n) :
    IsPipelineCenterCerts f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃) n := by
  subst hS₁ hS₂ hS₃
  exact ⟨⟨hbez₁, hgen₁.reduceCert, hbez₂, hgen₂.reduceCert, hn ▸ hgen₂.reduceCanon_natDegree⟩,
    hgen₁.fullDeg, hgen₂.fullDeg⟩

/-- **Weierstrass avoidance of the pipeline, on the same canonical pack**: the two
certificate-free conditions are exactly the two fields of `ChabautyColeman.IsPipelineAvoid` for
`ChabautyColeman.pipelineCanonData`. -/
theorem isPipelineAvoid_pipelineCanonData {S₁ S₂ S₃ : K[X] × K[X]}
    (hS₁ : cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ s₁ s₂ s₃ = S₁) (hS₂ : reduceCanon f S₁.1 S₁.2 = S₂)
    (hS₃ : cantorCompose f S₂.1 S₂.2 D.u₃ D.v₃ t₁ t₂ t₃ = S₃)
    (hcop₁ : ReduceCoprimeCanon f S₁.1 S₁.2) (hcop₂ : ReduceCoprimeCanon f S₃.1 S₃.2) :
    IsPipelineAvoid f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃) := by
  subst hS₁ hS₂ hS₃
  exact ⟨hcop₁, hcop₂⟩

/-- **Second-step avoidance is free once the pipeline returns its middle datum**: the `v`-part
of that datum is invertible modulo its `u`-part exactly when the `u`-part is coprime to the
curve — for the per-disk configuration, the good position of `τ`. So only the first step
carries an avoidance condition. -/
theorem isPipelineAvoid_of_pipeline_eq_middle {S₁ S₂ S₃ : K[X] × K[X]}
    (hS₁ : cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ s₁ s₂ s₃ = S₁) (hS₂ : reduceCanon f S₁.1 S₁.2 = S₂)
    (hS₃ : cantorCompose f S₂.1 S₂.2 D.u₃ D.v₃ t₁ t₂ t₃ = S₃)
    (hmid : cantorPipeline f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃) = (D.u₂, D.v₂))
    (h2 : IsUnit (2 : K[X])) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hcop : IsCoprime D.u₂ f)
    (hcop₁ : ReduceCoprimeCanon f S₁.1 S₁.2) :
    IsPipelineAvoid f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃) := by
  refine isPipelineAvoid_pipelineCanonData hS₁ hS₂ hS₃ hcop₁ ?_
  subst hS₁ hS₂ hS₃
  change IsCoprime (cantorPipeline f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃)).1
    (2 * (cantorPipeline f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃)).2)
  rw [hmid]
  exact (isCoprime_two_mul_iff h2 hd₂).mpr hcop

/-- **The per-disk pipeline avoids the Weierstrass points as soon as its first reduced datum
does**: with pair blocks whose classes cancel (`ChabautyColeman.cantorPipeline_eq_middle`), the
pipeline returns the middle datum `τ`, and `τ` misses the Weierstrass points by good
position. -/
theorem isPipelineAvoid_of_pair_blocks [NeZero (2 : K)] [Fact (Odd f.natDegree)]
    [Fact (Squarefree f)] {S₁ S₂ S₃ : K[X] × K[X]} {g : ℕ}
    (hf : f.natDegree = 2 * g + 1) (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic) (hu₃ : D.u₃.Monic)
    (hn₂ : D.u₂.natDegree = g) (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f)
    (hd₃ : D.u₃ ∣ D.v₃ ^ 2 - f) (hS₁ : cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ s₁ s₂ s₃ = S₁)
    (hS₂ : reduceCanon f S₁.1 S₁.2 = S₂) (hS₃ : cantorCompose f S₂.1 S₂.2 D.u₃ D.v₃ t₁ t₂ t₃ = S₃)
    (hcerts : IsPipelineCenterCerts f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃) g)
    (hcancel : ClassGroup.mk0 ⟨mumfordIdeal f D.u₁ D.v₁,
          mumfordIdeal_mem_nonZeroDivisors f hu₁.ne_zero D.v₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f D.u₃ D.v₃,
          mumfordIdeal_mem_nonZeroDivisors f hu₃.ne_zero D.v₃⟩ = 1)
    (hv₂ : D.v₂.degree < D.u₂.degree) (h2 : IsUnit (2 : K[X])) (hcop : IsCoprime D.u₂ f)
    (hcop₁ : ReduceCoprimeCanon f S₁.1 S₁.2) :
    IsPipelineAvoid f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃) :=
  isPipelineAvoid_of_pipeline_eq_middle hS₁ hS₂ hS₃
    (cantorPipeline_eq_middle hu₁ hd₁ hu₂ hd₂ hu₃ hd₃ hcerts.toIsPipelineCerts hcancel hv₂
      (by rw [hn₂, hf]; lia) (by rw [hf]; lia)) h2 hd₂ hcop hcop₁

/-- The generic degree after composing a degree-`2` datum with a degree-`g` one and reducing
once: back to `g`. -/
theorem genericDeg_pair_compose (g : ℕ) : max (2 * (2 + g - 1)) (2 * g + 1) - (2 + g) = g := by
  rw [max_eq_left (by lia)]
  lia

/-- **A pipeline with pair blocks has exactly one conditional reduction step per chain**, for
every genus: composing a degree-`2` datum with the degree-`g` datum `τ` gives degree `g + 2`,
and one canonical reduction step brings it back to `g`; the same for the second chain. This is
the shape of the per-disk configuration `[P₀ + ι Q] + τ + [Q + ι P₀]`, so — unlike the
configuration `τ + τ - τ`, whose stage-1 datum has degree `2g` — its genericity is four conditions
independently of `g`. -/
theorem isPipelineCenterCerts_of_pair_blocks {S₁ S₂ S₃ : K[X] × K[X]} {g : ℕ}
    (hf : f.natDegree = 2 * g + 1) (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic) (hu₃ : D.u₃.Monic)
    (hn₁ : D.u₁.natDegree = 2) (hn₂ : D.u₂.natDegree = g) (hn₃ : D.u₃.natDegree = 2)
    (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f)
    (hS₁ : cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ s₁ s₂ s₃ = S₁) (hS₂ : reduceCanon f S₁.1 S₁.2 = S₂)
    (hS₃ : cantorCompose f S₂.1 S₂.2 D.u₃ D.v₃ t₁ t₂ t₃ = S₃)
    (hbez₁ : s₁ * D.u₁ + s₂ * D.u₂ + s₃ * (D.v₁ + D.v₂) = 1) (hgen₁ : ReduceGeneric f S₁.1 S₁.2)
    (hbez₂ : t₁ * S₂.1 + t₂ * D.u₃ + t₃ * (S₂.2 + D.v₃) = 1)
    (hgen₂ : ReduceGeneric f S₃.1 S₃.2) :
    IsPipelineCenterCerts f D (pipelineCanonData f D s₁ s₂ s₃ t₁ t₂ t₃) g := by
  refine isPipelineCenterCerts_pipelineCanonData hS₁ hS₂ hS₃ hbez₁ hgen₁ hbez₂ hgen₂ ?_
  have hS₂m : S₂.1.Monic := by
    rw [← hS₂]; exact (hgen₁.reduceCanon_monic_dvd (hS₁ ▸ cantorCompose_monic f hu₁ hu₂)
      (hS₁ ▸ cantorCompose_dvd f hbez₁ hd₁ hd₂)).1
  have hS₂deg : S₂.1.natDegree = g := by
    rw [← hS₂, hgen₁.reduceCanon_natDegree, ← hS₁, cantorCompose_natDegree f hu₁ hu₂, hn₁, hn₂, hf,
      genericDeg_pair_compose]
  rw [← hS₃, cantorCompose_natDegree f hS₂m hu₃, hS₂deg, hn₃, hf, add_comm, genericDeg_pair_compose]

end GenericPack

end ChabautyColeman

end
