/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCOriginTrace

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
/-!
# A fixed finite cover of the unit spatial ball

A single finite cover, transported by translation and dilation, supplies
the spatial covers used to move the Gaussian center.
-/

public section


open Set CKN CKN.Foundation.Parabolic
attribute [local instance] Classical.propDecidable

noncomputable section

namespace ESS

/-- The closed unit ball admits a finite cover by explicit Euclidean balls
of radius one half, with centers in the closed unit ball. -/
theorem uc_unit_ball_finite_half_cover :
    ∃ F : Finset Vec3,
      (∀ c ∈ F, c ∈ closure (vec3Ball 0 1)) ∧
      ∀ y ∈ closure (vec3Ball 0 1),
        ∃ c ∈ F, y ∈ vec3Ball c (1 / 2) := by
  let K : Set Vec3 := closure (vec3Ball 0 1)
  have hK : IsCompact K := isCompact_closure_vec3Ball (by norm_num)
  have hcover (y : Vec3) (hy : y ∈ K) :
      y ∈ ⋃ c : K, vec3Ball c.1 (1 / 2) := by
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, by
      simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using
        (by norm_num : (0 : ℝ) < 1 / 2)⟩
  obtain ⟨G, hG⟩ := hK.elim_finite_subcover
    (fun c : K => vec3Ball c.1 (1 / 2))
    (fun c => isOpen_vec3Ball _ _) hcover
  let F : Finset Vec3 := G.image Subtype.val
  refine ⟨F, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    exact d.2
  · intro y hy
    obtain ⟨d, hd, hyball⟩ := mem_iUnion₂.mp (hG hy)
    exact ⟨d.1, Finset.mem_image.mpr ⟨d, hd, rfl⟩, hyball⟩

/-- A fixed unit-ball cover scales to every positive spatial radius. -/
theorem uc_finite_half_cover_scaled
    (F : Finset Vec3)
    (hF : ∀ y ∈ closure (vec3Ball 0 1),
      ∃ c ∈ F, y ∈ vec3Ball c (1 / 2))
    (x : Vec3) (r : ℝ) (hr : 0 < r)
    (y : Vec3) (hy : y ∈ closure (vec3Ball x r)) :
    ∃ c ∈ F, y ∈ vec3Ball (x + r • c) (r / 2) := by
  have hybound : vec3EuclideanNorm (y - x) ≤ r := by
    rw [closure_vec3Ball hr] at hy
    exact hy
  let u : Vec3 := r⁻¹ • (y - x)
  have hunorm : vec3EuclideanNorm u ≤ 1 := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
    change r⁻¹ * vec3EuclideanNorm (y - x) ≤ 1
    exact (inv_mul_le_one₀ hr).mpr hybound
  have hu : u ∈ closure (vec3Ball 0 1) := by
    rw [closure_vec3Ball (by norm_num)]
    simpa only [Set.mem_ofPred_eq, sub_zero] using hunorm
  obtain ⟨c, hc, huc⟩ := hF u hu
  refine ⟨c, hc, ?_⟩
  have hscaled : r • u = y - x := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hdiff : y - (x + r • c) = r • (u - c) := by
    rw [smul_sub, hscaled]
    abel
  rw [mem_vec3Ball, hdiff, vec3EuclideanNorm_smul,
    abs_of_pos hr]
  have hsmall : vec3EuclideanNorm (u - c) < 1 / 2 :=
    (mem_vec3Ball).mp huc
  exact (mul_lt_mul_of_pos_left hsmall hr).trans_eq (by ring)

/-- Centers obtained by repeatedly halving a spatial-ball cover. -/
@[expose] def ucBallCoverCenters (F : Finset Vec3) (x : Vec3) (r : ℝ) :
    ℕ → Finset Vec3
  | 0 => {x}
  | n + 1 => (ucBallCoverCenters F x r n).biUnion fun c =>
      F.image fun d => c + (r / (2 : ℝ) ^ n) • d

/-- Every ball is covered by the iterated half-radius balls. -/
theorem uc_ball_cover_centers_cover
    (F : Finset Vec3)
    (hF : ∀ y ∈ closure (vec3Ball 0 1),
      ∃ c ∈ F, y ∈ vec3Ball c (1 / 2))
    (x : Vec3) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∀ y ∈ vec3Ball x r,
      ∃ c ∈ ucBallCoverCenters F x r n,
        y ∈ vec3Ball c (r / (2 : ℝ) ^ n) := by
  induction n with
  | zero =>
      intro y hy
      exact ⟨x, by simp [ucBallCoverCenters], by simpa using hy⟩
  | succ n ih =>
      intro y hy
      obtain ⟨c, hc, hyc⟩ := ih y hy
      let s : ℝ := r / (2 : ℝ) ^ n
      have hs : 0 < s := by dsimp [s]; positivity
      have hyclosure : y ∈ closure (vec3Ball c s) :=
        subset_closure (by simpa only [s] using hyc)
      obtain ⟨d, hd, hyd⟩ :=
        uc_finite_half_cover_scaled F hF c s hs y hyclosure
      refine ⟨c + s • d, ?_, ?_⟩
      · simp only [ucBallCoverCenters, Finset.mem_biUnion]
        exact ⟨c, hc, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
      · have hrad : s / 2 = r / (2 : ℝ) ^ (n + 1) := by
          dsimp [s]
          rw [pow_succ]
          ring
        simpa only [hrad] using hyd

/-- The number of iterated cover centers grows at most geometrically. -/
theorem uc_ball_cover_centers_card_le
    (F : Finset Vec3) (x : Vec3) (r : ℝ) (n : ℕ) :
    (ucBallCoverCenters F x r n).card ≤ F.card ^ n := by
  induction n with
  | zero => simp [ucBallCoverCenters]
  | succ n ih =>
      calc
        (ucBallCoverCenters F x r (n + 1)).card ≤
            (ucBallCoverCenters F x r n).card * F.card := by
          simpa only [ucBallCoverCenters] using
            Finset.card_biUnion_le_card_mul
              (ucBallCoverCenters F x r n)
              (fun c => F.image fun d => c + (r / (2 : ℝ) ^ n) • d)
              F.card (fun c hc => Finset.card_image_le)
        _ ≤ F.card ^ n * F.card := Nat.mul_le_mul_right F.card ih
        _ = F.card ^ (n + 1) := (pow_succ _ _).symm

/-- Retain only cover balls meeting the original ball. Their centers stay
within twice its radius. -/
theorem uc_ball_cover_near_centers
    (F : Finset Vec3)
    (hF : ∀ y ∈ closure (vec3Ball 0 1),
      ∃ c ∈ F, y ∈ vec3Ball c (1 / 2))
    (x : Vec3) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∃ G : Finset Vec3,
      G.card ≤ F.card ^ n ∧
      (∀ c ∈ G, c ∈ vec3Ball x (2 * r)) ∧
      ∀ y ∈ vec3Ball x r,
        ∃ c ∈ G, y ∈ vec3Ball c (r / (2 : ℝ) ^ n) := by
  let s : ℝ := r / (2 : ℝ) ^ n
  have hs : 0 < s := by dsimp [s]; positivity
  have hsle : s ≤ r := by
    have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
      (by nlinarith only [hpow, hr])
  let H := ucBallCoverCenters F x r n
  let G := H.filter fun c =>
    ∃ y ∈ vec3Ball x r, y ∈ vec3Ball c s
  refine ⟨G, (Finset.card_filter_le _ _).trans
    (uc_ball_cover_centers_card_le F x r n), ?_, ?_⟩
  · intro c hc
    obtain ⟨y, hyx, hyc⟩ := (Finset.mem_filter.mp hc).2
    have hcx : vec3EuclideanNorm (c - x) ≤
        vec3EuclideanNorm (c - y) + vec3EuclideanNorm (y - x) := by
      have h := vec3EuclideanNorm_add_le (c - y) (y - x)
      simpa only [sub_add_sub_cancel] using h
    have hcy : vec3EuclideanNorm (c - y) < s := by
      have h := (mem_vec3Ball).mp hyc
      rw [← vec3EuclideanNorm_neg (y - c), neg_sub] at h
      exact h
    have hyx' : vec3EuclideanNorm (y - x) < r := (mem_vec3Ball).mp hyx
    apply (mem_vec3Ball).mpr
    linarith only [hcx, hcy, hyx', hsle]
  · intro y hy
    obtain ⟨c, hc, hyc⟩ := uc_ball_cover_centers_cover F hF x r hr n y hy
    refine ⟨c, Finset.mem_filter.mpr ⟨hc, ⟨y, hy, ?_⟩⟩, hyc⟩
    simpa only [s] using hyc

end ESS
