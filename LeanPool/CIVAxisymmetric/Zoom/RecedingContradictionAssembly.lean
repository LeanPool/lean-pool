/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.EndpointFiniteAxis
public import LeanPool.CIVAxisymmetric.Zoom.EndpointReceding
public import LeanPool.CIVAxisymmetric.Zoom.RecedingSelectionIdentity

/-!
# The receding-axis contradiction

`eq:aniso:zoom:receding:quotient`: the final contradiction of the receding-axis case.
In the recentred variables `eq:aniso:zoom:receding:variables` the selected point is the
origin of `ℝ × ℝ` and the axis sits at `R = -A_n`, so the meridional fields live on the
whole plane. The limiting divergence identity of `eq:aniso:zoom:receding:div` is
`∂_R V + ∂_Z W = 0` with no radial quotient, the term `V_n / (A_n + R)` vanishing
uniformly on compact sets because `A_n → ∞` while `V_n` stays bounded. Endpoint vanishing
is therefore `CIV.endpoint_vanishing_rec`, which holds at every point of the plane and
needs no continuity statement at a boundary; and the radial quotient at the selected point
is bounded by `M / A_n`. All three summands of `eq:aniso:zoom:selected` thus tend to `0`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- Uniform convergence on a set to a constant implies pointwise convergence to that constant
at every point of the set. -/
theorem tendsto_at_of_tendstoUniformlyOn_const
    (S : Set (ℝ × ℝ)) (F : ℕ → ℝ × ℝ → ℝ) (c : ℝ)
    (hF : TendstoUniformlyOn F (fun _ => c) atTop S) {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ S) :
    Tendsto (fun n => F n x₀) atTop (nhds c) := by
  have := hF.tendsto_at hx₀
  simpa using this

/-- `eq:aniso:zoom:receding:endpoint` in pointwise form: a divergence-free meridional pair
`(V, W)` on `ℝ × ℝ` with `∂_R W = 0` and `V` bounded has `∂_R V` and `∂_Z W` vanishing at
every point, in particular at the origin, which is the selected point in the variables
`eq:aniso:zoom:receding:variables`. The divergence hypothesis is the quotient-free identity
of `eq:aniso:zoom:receding:div`. -/
theorem dVaxis_dWaxis_eq_zero_rec
    (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, DV p (1, 0) + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, DW p (1, 0) = 0)
    (p : ℝ × ℝ) :
    DV p (1, 0) = 0 ∧ DW p (0, 1) = 0 := by
  obtain ⟨hDVzero, hDWzero⟩ := endpoint_vanishing_rec V W DV DW M hV hW hbdd hdiv hWr
  exact ⟨hDVzero p, hDWzero p⟩

/-- The final contradiction of the receding-axis zoom. On a set `S` containing the selected
point — the origin of the variables `eq:aniso:zoom:receding:variables` — the recentred
derivatives converge uniformly to the endpoint derivatives, which vanish identically by
`eq:aniso:zoom:receding:endpoint`; the radial quotient at the selected point is at most
`M / A_n` with `A_n → ∞`, which is `eq:aniso:zoom:receding:quotient`. The three summands of
`eq:aniso:zoom:selected` therefore tend to `0`, and `ge_of_tendsto'` forces `c₀ ≤ 0`,
contradicting `hc₀`. -/
theorem false_of_receding_contradiction_data
    {c₀ M : ℝ} (hc₀ : 0 < c₀)
    (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hV : ∀ p : ℝ × ℝ, HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, DV p (1, 0) + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, DW p (1, 0) = 0)
    (DVn DWn : ℕ → ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (Vn : ℕ → ℝ × ℝ → ℝ)
    (S : Set (ℝ × ℝ)) (hS : ((0 : ℝ), (0 : ℝ)) ∈ S)
    (hDVconv : TendstoUniformlyOn DVn DV atTop S)
    (hDWconv : TendstoUniformlyOn DWn DW atTop S)
    {Anseq : ℕ → ℝ} (hAtop : Tendsto Anseq atTop atTop)
    (hApos : ∀ n, 0 < Anseq n)
    (hVnbdd : ∀ n, |Vn n (0, 0)| ≤ M)
    (hlower : ∀ n, c₀ ≤ |DVn n (0, 0) (1, 0)| + |Vn n (0, 0)| / Anseq n + |DWn n (0, 0) (0, 1)|) :
    False := by
  -- The endpoint derivatives vanish at every point of the plane, hence on `S`.
  have hDVseg : ∀ p ∈ S, DV p (1, 0) = 0 := fun p _ =>
    (dVaxis_dWaxis_eq_zero_rec V W DV DW M hV hW hbdd hdiv hWr p).1
  have hDWseg : ∀ p ∈ S, DW p (0, 1) = 0 := fun p _ =>
    (dVaxis_dWaxis_eq_zero_rec V W DV DW M hV hW hbdd hdiv hWr p).2
  -- Uniform convergence of the linear maps to a limit that annihilates `(1,0)` gives
  -- uniform convergence of the values at `(1,0)` to `0`.
  have hDVn_tendsto : TendstoUniformlyOn (fun n p => DVn n p (1, 0)) (fun _ => (0 : ℝ)) atTop S :=
    tendstoUniformlyOn_clm_apply_zero S DVn DV (1, 0) hDVconv hDVseg
  have hDWn_tendsto : TendstoUniformlyOn (fun n p => DWn n p (0, 1)) (fun _ => (0 : ℝ)) atTop S :=
    tendstoUniformlyOn_clm_apply_zero S DWn DW (0, 1) hDWconv hDWseg
  -- Pointwise convergence at the selected point.
  have hDVpt : Tendsto (fun n : ℕ => DVn n (0, 0) (1, 0)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_at_of_tendstoUniformlyOn_const S (fun n p => DVn n p (1, 0)) 0 hDVn_tendsto hS
  have hDWpt : Tendsto (fun n : ℕ => DWn n (0, 0) (0, 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_at_of_tendstoUniformlyOn_const S (fun n p => DWn n p (0, 1)) 0 hDWn_tendsto hS
  -- Absolute values tend to 0.
  have hDVabs : Tendsto (fun n : ℕ => |DVn n (0, 0) (1, 0)|) atTop (𝓝 0) := by
    simpa [abs_zero] using hDVpt.abs
  have hDWabs : Tendsto (fun n : ℕ => |DWn n (0, 0) (0, 1)|) atTop (𝓝 0) := by
    simpa [abs_zero] using hDWpt.abs
  -- The middle term: `|Vn n (0,0)| / Anseq n` tends to 0.
  have hmid : Tendsto (fun n : ℕ => |Vn n (0, 0)| / Anseq n) atTop (𝓝 0) := by
    have h_bound : ∀ n, |Vn n (0, 0)| / Anseq n ≤ M / Anseq n := by
      intro n
      exact div_le_div_of_nonneg_right (hVnbdd n) (hApos n).le
    have h_tendsto : Tendsto (fun n : ℕ => M / Anseq n) atTop (𝓝 0) := by
      simpa [div_zero] using Filter.Tendsto.const_div_atTop hAtop M
    have h_nonneg : ∀ n, 0 ≤ |Vn n (0, 0)| / Anseq n := by
      intro n
      exact div_nonneg (abs_nonneg _) (hApos n).le
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_tendsto h_nonneg h_bound
  -- Sum the three vanishing sequences.
  have hsum : Tendsto (fun n : ℕ => |DVn n (0, 0) (1, 0)| + |Vn n (0, 0)| / Anseq n
      + |DWn n (0, 0) (0, 1)|) atTop (𝓝 0) := by
    have h12 : Tendsto (fun n : ℕ => |DVn n (0, 0) (1, 0)| + |Vn n (0, 0)| / Anseq n) atTop (𝓝
      0) := by
      simpa [add_zero] using hDVabs.add hmid
    simpa [add_zero] using h12.add hDWabs
  -- `ge_of_tendsto'` yields `c₀ ≤ 0`.
  have hle : c₀ ≤ (0 : ℝ) :=
    ge_of_tendsto' hsum (fun n => hlower n)
  linarith only [hc₀, hle]

end CIV
