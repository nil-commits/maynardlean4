import RHDirect.Stage5ZetaZeroFree
import RHDirect.Stage4ExplicitFormula
import RHDirect.Stage3RealAnalyticLandau
import RHDirect.Stage2DirichletAP
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# RHDirect.Stage6EffectivePNT

**UNCONDITIONAL EFFECTIVE PRIME NUMBER THEOREM** (0 assumptions, 0 `sorry`, 0 custom `axiom`s)
directly on Mathlib's actual `Chebyshev.psi`, `Chebyshev.theta`, and `Nat.primeCounting`, in pure
Mathlib `v4.33.1`.

## Main Contents
1. **Quantitative Log-Derivative Bounds Inside the de la Vallée Poussin Zero-Free Region**:
   - Holomorphic regularization `zetaReg z = (z - 1) ζ(z)` on `Re(z) > 0` via the Euler–Maclaurin
     continuation (`Stage5ZetaZeroFree.riemannZeta_sub_pole_eq_eulerMaclaurin`), with `zetaReg 1 = 1`
     and `negLogDerivZetaReg z = (-ζ'/ζ)(z) - 1/(z - 1)` holomorphic on the entire zero-free region.
   - `negLogDerivZeta_zeroFree_bound`: unconditionally via `riemannZeta_deLaValleePoussin_zeroFree` +
     `exists_holomorphic_log_ball` + `borelCaratheodory_deriv_le`,
     `∃ c₁ > 0, ∃ C₁ > 0, ∀ s, 1 - c₁ / log(|s.im| + 2) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖(-ζ'/ζ)(s)‖ ≤ C₁ (log(|s.im| + 2))²`.
   - `negLogDerivZeta_sub_pole_bounded_near_one`: unconditionally near `s = 1`,
     `∃ c₂ > 0, ∃ C₂ > 0, ∀ s, 1 - c₂ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 → s ≠ 1 → ‖(-ζ'/ζ)(s) - 1/(s - 1)‖ ≤ C₂`.
2. **Exact Zero-Free Perron Contour Shift for `ψ₁(x) = ∑_{n ≤ x} Λ(n) (x - n)`**:
   - Exact rectangle residue integral `∮_{∂R} (s - 1)⁻¹ ds = 2 π i` via explicit `log`/`arctan`
     antiderivatives and `Real.arctan_inv_of_pos`.
   - Exact Cauchy contour shift from `Re(s) = c = 1 + 1 / (2 log x)` to `Re(s) = σ_T = 1 - c_* / log(T + 2)`
     via `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` + `dslope` pole extraction,
     yielding residue `x² / 2`.
   - Optimization `T = exp(√(c_* / 2 · log x))` giving **unconditionally**:
     `effective_pnt_psi1`: `∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |psi1 x - x² / 2| ≤ C x² exp(-c √(log x))`.
3. **Unconditional Effective Prime Number Theorem for `Chebyshev.psi`, `Chebyshev.theta`, & `Nat.primeCounting`**:
   - Purely algebraic monotone finite-difference de-smoothing of `psi1`:
     - `effective_pnt_psi`: `∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C x exp(-c √(log x))`.
     - `effective_pnt_theta`: `∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ C x exp(-c √(log x))`.
     - `pnt_psi_asymp`: `Tendsto (fun x => Chebyshev.psi x / x) atTop (nhds 1)`.
     - `pnt_theta_asymp`: `Tendsto (fun x => Chebyshev.theta x / x) atTop (nhds 1)`.
     - `pnt_primeCounting_asymp`: `Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / (n / Real.log n)) atTop (nhds 1)`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage6EffectivePNT

/-! ## Section 1: Quantitative Log-Derivative Bounds in the de la Vallée Poussin Zero-Free Region -/

/-- Holomorphic regularization of `(z - 1) * riemannZeta z` on the right half-plane `Re(z) > 0`,
built directly from the Euler–Maclaurin continuation `Stage5ZetaZeroFree.riemannZeta_sub_pole_eq_eulerMaclaurin`. -/
def zetaReg (z : ℂ) : ℂ :=
  1 + (z - 1) *
    (1 - z * ∫ t in Ioi (1 : ℝ),
      ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1))

/-- Regularized negative logarithmic derivative `-zetaReg'(z) / zetaReg(z)`, which equals
`(-ζ'(z) / ζ(z)) - 1 / (z - 1)` on `Re(z) > 0`, `z ≠ 1`, `ζ(z) ≠ 0`, and extends holomorphically
across `z = 1`. -/
def negLogDerivZetaReg (z : ℂ) : ℂ :=
  -deriv zetaReg z / zetaReg z

theorem zetaReg_one : zetaReg 1 = 1 := by
  simp [zetaReg]

theorem zetaReg_eq_mul_riemannZeta {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    zetaReg z = (z - 1) * riemannZeta z := by
  unfold zetaReg
  rw [← Stage5ZetaZeroFree.riemannZeta_sub_pole_eq_eulerMaclaurin hz hz1]
  have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp [hne]
  ring

theorem differentiableOn_zetaReg : DifferentiableOn ℂ zetaReg {z : ℂ | 0 < z.re} := by
  have hE_meas : Measurable (fun t : ℝ => -((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp Stage5ZetaZeroFree.measurable_fractNat).neg
  have hE_bd : ∀ t : ℝ, 1 ≤ t →
      ‖-((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)‖ ≤ 1 * t ^ (0 : ℝ) := by
    intro t ht
    rw [norm_neg, Real.rpow_zero, mul_one]
    exact Stage5ZetaZeroFree.norm_fractNat_le_one (zero_le_one.trans ht)
  have hH_an := Stage3RealAnalyticLandau.analyticOnNhd_mellin_of_rpow_bound hE_meas zero_le_one hE_bd
  have hEq : (fun z : ℂ => 1 + z * ∫ t in Ioi (1 : ℝ),
        (-((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
      fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ),
        ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    funext z
    have hneg : (fun t : ℝ => (-((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
        fun t : ℝ => -(((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
      funext t; ring
    rw [hneg, integral_neg]; ring
  rw [hEq] at hH_an
  have hH_diff : DifferentiableOn ℂ
      (fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ),
        ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) {z : ℂ | 0 < z.re} :=
    hH_an.differentiableOn
  unfold zetaReg
  exact (differentiableOn_const 1).add ((differentiableOn_id.sub (differentiableOn_const 1)).mul hH_diff)

theorem negLogDerivZetaReg_eq_sub_pole {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1)
    (hnz : riemannZeta z ≠ 0) :
    negLogDerivZetaReg z = (-deriv riemannZeta z / riemannZeta z) - 1 / (z - 1) := by
  have hopen : IsOpen ({w : ℂ | 0 < w.re} \ {(1 : ℂ)}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hev : zetaReg =ᶠ[𝓝 z] fun w : ℂ => (w - 1) * riemannZeta w := by
    filter_upwards [hopen.mem_nhds ⟨hz, hz1⟩] with w hw
    exact zetaReg_eq_mul_riemannZeta hw.1 hw.2
  have hdz : HasDerivAt (fun w : ℂ => (w - 1) * riemannZeta w)
      (1 * riemannZeta z + (z - 1) * deriv riemannZeta z) z :=
    ((hasDerivAt_id z).sub_const 1).mul (differentiableAt_riemannZeta hz1).hasDerivAt
  have hderiv_eq : deriv zetaReg z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
    rw [hev.deriv_eq, hdz.deriv, one_mul]
  unfold negLogDerivZetaReg
  rw [hderiv_eq, zetaReg_eq_mul_riemannZeta hz hz1]
  have hsub_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp [hsub_ne, hnz]
  ring

theorem isOpen_re_pos_zetaReg_ne_zero :
    IsOpen {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcont : ContinuousOn zetaReg {z : ℂ | 0 < z.re} := differentiableOn_zetaReg.continuousOn
  have hset : {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} =
      {z : ℂ | 0 < z.re} ∩ zetaReg ⁻¹' ({(0 : ℂ)}ᶜ) := by
    ext z; simp
  rw [hset]
  exact hcont.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl

theorem differentiableOn_negLogDerivZetaReg :
    DifferentiableOn ℂ negLogDerivZetaReg {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
  have hU := isOpen_re_pos_zetaReg_ne_zero
  have hsub : {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} ⊆ {z : ℂ | 0 < z.re} := fun _ hz => hz.1
  have hdiff : DifferentiableOn ℂ zetaReg {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} :=
    differentiableOn_zetaReg.mono hsub
  unfold negLogDerivZetaReg
  exact (hdiff.deriv hU).neg.div hdiff fun _ hz => hz.2

/-- **Unconditional Quantitative Log-Derivative Bound Inside the de la Vallée Poussin Zero-Free Region**:
there exist explicit constants `c₁ > 0` and `C₁ > 0` such that for all `s : ℂ` with `1 ≤ |s.im|`
and `1 - c₁ / log(|s.im| + 2) ≤ s.re ≤ 2`,
`‖-deriv riemannZeta s / riemannZeta s‖ ≤ C₁ * (Real.log (|s.im| + 2)) ^ 2`. -/
theorem negLogDerivZeta_zeroFree_bound :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ s : ℂ, 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
        ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C₁ * (Real.log (|s.im| + 2)) ^ 2 := by
  obtain ⟨c₀, hc₀_pos, hzf₀⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  set c : ℝ := min c₀ (1 / 4) with hc_def
  have hc_pos : 0 < c := lt_min hc₀_pos (by norm_num)
  have hc_le_c₀ : c ≤ c₀ := min_le_left _ _
  have hc_le_qtr : c ≤ 1 / 4 := min_le_right _ _
  set c₁ : ℝ := c / 16 with hc₁_def
  have hc₁_pos : 0 < c₁ := by positivity
  set C_right : ℝ := 1 / c₁ + 1
  set C_left : ℝ := (16 / c) * (Real.log (112 / c) + 2)
  have h112_gt1 : (1 : ℝ) < 112 / c := by
    rw [one_lt_div hc_pos]; linarith
  have hC_left_pos : 0 < C_left := by
    have hlog_pos : 0 < Real.log (112 / c) := Real.log_pos h112_gt1
    positivity
  set C₁ : ℝ := max C_right C_left
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le hC_left_pos (le_max_right _ _)
  refine ⟨c₁, hc₁_pos, C₁, hC₁_pos, fun s hre_lo hre_hi him => ?_⟩
  set t : ℝ := s.im
  set L : ℝ := Real.log (|t| + 2) with hL_def
  have ht2_ge3 : (3 : ℝ) ≤ |t| + 2 := by linarith
  have ht2_pos : 0 < |t| + 2 := by linarith
  have hL_gt1 : 1 < L := by
    have h3 : Real.exp 1 < |t| + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h3)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  by_cases hright : 1 + c₁ / L ≤ s.re
  · -- Case 1: `s.re ≥ 1 + c₁ / L` — direct from `Stage5ZetaZeroFree.norm_negLogDerivZeta_of_one_lt_re`
    have hs_re_gt1 : 1 < s.re := by
      have : 0 < c₁ / L := div_pos hc₁_pos hL_pos
      linarith
    have hs_eq : s = (s.re : ℂ) + I * (t : ℂ) := by
      apply Complex.ext <;> simp [t]
    have hbd := Stage5ZetaZeroFree.norm_negLogDerivZeta_of_one_lt_re hs_re_gt1 t
    have hnorm_le : ‖-deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + 1 := by
      have h1 := hbd.1.trans hbd.2
      unfold Stage3ZeroFreeRegion.negLogDerivZeta at h1
      rwa [← hs_eq] at h1
    have hinv_le : 1 / (s.re - 1) ≤ L / c₁ := by
      rw [div_le_div_iff₀ (by linarith) hc₁_pos, one_mul]
      have h1 : c₁ / L ≤ s.re - 1 := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hL_pos.le
      rw [div_mul_cancel₀ _ hL_pos.ne'] at h2
      linarith
    have hL_le_L2 : L ≤ L ^ 2 := by nlinarith
    have h1_le_L2 : 1 ≤ L ^ 2 := by nlinarith
    have hC_right_le : C_right ≤ C₁ := le_max_left _ _
    calc ‖-deriv riemannZeta s / riemannZeta s‖
        ≤ 1 / (s.re - 1) + 1 := hnorm_le
      _ ≤ (1 / c₁) * L + 1 := by linarith [show L / c₁ = (1 / c₁) * L by ring]
      _ ≤ (1 / c₁) * L ^ 2 + 1 * L ^ 2 := by
          have h1 : (1 / c₁) * L ≤ (1 / c₁) * L ^ 2 :=
            mul_le_mul_of_nonneg_left hL_le_L2 (by positivity)
          linarith
      _ = C_right * L ^ 2 := by dsimp only [C_right]; ring
      _ ≤ C₁ * L ^ 2 := mul_le_mul_of_nonneg_right hC_right_le (sq_nonneg L)
  · -- Case 2: `1 - c₁ / L ≤ s.re < 1 + c₁ / L` — Borel–Carathéodory on a zero-free disk
    push Not at hright
    set η : ℝ := c / (8 * L) with hη_def
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 32 := by
      dsimp only [η]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    set R_open : ℝ := 5 * η
    set R : ℝ := 4 * η
    set r : ℝ := 2 * η
    have hR_open_pos : 0 < R_open := by positivity
    have hR_pos : 0 < R := by positivity
    have hrR : r < R := by dsimp only [r, R]; linarith
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (t : ℂ) with hs₀_def
    have hs₀_re : s₀.re = 1 + η := by simp [s₀]
    have hs₀_im : s₀.im = t := by simp [s₀]
    -- Every `z ∈ ball s₀ R_open` avoids `1` and lies inside the de la Vallée Poussin zero-free region
    have hball_ne1 : ∀ z ∈ Metric.ball s₀ R_open, z ≠ 1 := by
      intro z hz h1
      subst h1
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have him_diff := (Complex.abs_im_le_norm ((1 : ℂ) - s₀)).trans_lt hz
      rw [Complex.sub_im, Complex.one_im, hs₀_im, zero_sub, abs_neg] at him_diff
      have hR_lt : R_open < 1 := by dsimp only [R_open]; linarith
      linarith
    have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, riemannZeta z ≠ 0 := by
      intro z hz
      have hz1 : z ≠ 1 := hball_ne1 z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz.le)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hz_im_le : |z.im| ≤ |t| + 1 / 2 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        have hR_le_half : R_open ≤ 1 / 2 := by dsimp only [R_open]; linarith
        linarith [abs_le.mpr him_diff]
      have hlog_le : Real.log (|z.im| + 2) ≤ 2 * L := by
        have hsq : |z.im| + 2 ≤ (|t| + 2) ^ 2 := by nlinarith
        have h1 := Real.log_le_log (by linarith [abs_nonneg z.im]) hsq
        rw [Real.log_pow] at h1
        simpa [L] using h1
      have hlogz_pos : 0 < Real.log (|z.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg z.im])
      have hdiv_ge : c / (2 * L) ≤ c₀ / Real.log (|z.im| + 2) := by
        calc c / (2 * L) ≤ c / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_left hc_pos.le hlogz_pos hlog_le
          _ ≤ c₀ / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_right hc_le_c₀ hlogz_pos.le
      have h4η : 4 * η = c / (2 * L) := by dsimp only [η]; ring
      have hz_re_ge : 1 - c₀ / Real.log (|z.im| + 2) ≤ z.re := by
        dsimp only [R_open] at hre_diff
        linarith
      exact hzf₀ z hz_re_ge hz1
    have hball_diff : DifferentiableOn ℂ riemannZeta (Metric.ball s₀ R_open) := fun z hz =>
      (differentiableAt_riemannZeta (hball_ne1 z hz)).differentiableWithinAt
    -- Holomorphic logarithm `Log` of `riemannZeta z / riemannZeta s₀` on `ball s₀ R_open`
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
      (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
    -- Upper bound `(Log z).re ≤ M` on `closedBall s₀ R`
    set M : ℝ := (Real.log (112 / c) + 2) * L with hM_def
    have hLog_re_le : ∀ z ∈ Metric.closedBall s₀ R, (Log z).re ≤ M := by
      intro z hz
      have hz_ball : z ∈ Metric.ball s₀ R_open := hcb_sub hz
      have hz1 : z ≠ 1 := hball_ne1 z hz_ball
      have hznz : riemannZeta z ≠ 0 := hball_nz z hz_ball
      have hs₀_nz : riemannZeta s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hR_le_8 : R ≤ 1 / 8 := by dsimp only [R]; linarith
      have hz_re_lo : 1 / 2 ≤ z.re := by linarith
      have hz_re_hi : z.re ≤ 2 := by linarith
      have hz_im_lo : 1 / 2 ≤ |z.im| := by
        have htri : |t| ≤ |z.im| + |z.im - t| := by
          have := abs_sub_le t z.im 0
          linarith [abs_sub_comm t z.im, show |t - 0| = |t| by simp, show |z.im - 0| = |z.im| by simp]
        linarith [abs_le.mpr him_diff]
      have hz_im_hi : |z.im| ≤ |t| + 1 / 8 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        linarith [abs_le.mpr him_diff]
      have hz_bd : ‖riemannZeta z‖ ≤ 7 * (|t| + 2) := by
        have h1 := Stage5ZetaZeroFree.norm_riemannZeta_le_of_re_pos (by linarith : 0 < z.re) hz1
        have hsub_ge : 1 / 2 ≤ ‖z - 1‖ := by
          have := Complex.abs_im_le_norm (z - 1)
          simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
          linarith
        have hinv_le : 1 / ‖z - 1‖ ≤ 2 := by
          rw [div_le_iff₀ (by linarith : 0 < ‖z - 1‖)]; linarith
        have hnorm_z : ‖z‖ ≤ 2 * (|t| + 2) := by
          have := Complex.norm_le_abs_re_add_abs_im z
          rw [abs_of_pos (by linarith : 0 < z.re)] at this
          linarith
        have hdiv_le : ‖z‖ / z.re ≤ 4 * (|t| + 2) := by
          rw [div_le_iff₀ (by linarith : 0 < z.re)]
          nlinarith
        linarith
      have hinv_s₀ : ‖1 / riemannZeta s₀‖ ≤ 16 * L / c := by
        have h := Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re (by linarith : 1 < 1 + η) t
        have h1 := h.2.1.trans h.2.2
        have hsub : (1 + η) - 1 = η := by ring
        rw [hsub] at h1
        have hs₀_eq' : ((1 + η : ℝ) : ℂ) + I * (t : ℂ) = s₀ := rfl
        rw [hs₀_eq'] at h1
        have h2 : (1 + η) / η ≤ 2 / η := div_le_div_of_nonneg_right (by linarith) hη_pos.le
        have h3 : 2 / η = 16 * L / c := by dsimp only [η]; field_simp [hc_pos.ne', hL_pos.ne']; ring
        linarith
      have hratio_le : ‖riemannZeta z / riemannZeta s₀‖ ≤ (112 / c) * (|t| + 2) ^ 2 := by
        have hL_le_t2 : L ≤ |t| + 2 :=
          (Real.log_le_sub_one_of_pos ht2_pos).trans (by linarith)
        rw [show riemannZeta z / riemannZeta s₀ = riemannZeta z * (1 / riemannZeta s₀) by ring,
          norm_mul]
        calc ‖riemannZeta z‖ * ‖1 / riemannZeta s₀‖
            ≤ (7 * (|t| + 2)) * (16 * L / c) :=
              mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ = (112 / c) * ((|t| + 2) * L) := by ring
          _ ≤ (112 / c) * ((|t| + 2) * (|t| + 2)) := by
              gcongr
          _ = (112 / c) * (|t| + 2) ^ 2 := by ring
      have hre_eq : (Log z).re = Real.log ‖riemannZeta z / riemannZeta s₀‖ := by
        have hexp : Real.exp (Log z).re = ‖riemannZeta z / riemannZeta s₀‖ := by
          rw [← Complex.norm_exp, hLog_exp z hz_ball]
        rw [← hexp, Real.log_exp]
      have hratio_pos : 0 < ‖riemannZeta z / riemannZeta s₀‖ :=
        norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)
      rw [hre_eq]
      calc Real.log ‖riemannZeta z / riemannZeta s₀‖
          ≤ Real.log ((112 / c) * (|t| + 2) ^ 2) := Real.log_le_log hratio_pos hratio_le
        _ = Real.log (112 / c) + Real.log ((|t| + 2) ^ 2) :=
            Real.log_mul (by positivity) (by positivity)
        _ = Real.log (112 / c) + 2 * L := by rw [Real.log_pow]; push_cast; rfl
        _ ≤ (Real.log (112 / c) + 2) * L := by
            nlinarith [Real.log_pos h112_gt1]
    -- Check `‖s - s₀‖ ≤ r` and apply `borelCaratheodory_deriv_le`!
    have hs_dist : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - (1 + η) : ℝ) : ℂ)) :=
        Complex.ext (by simp [s₀]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hc₁_eq : c₁ / L = η / 2 := by dsimp only [c₁, η]; ring
      dsimp only [r]
      constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_dist
    have hs_ball : s ∈ Metric.ball s₀ R_open :=
      hcb_sub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hs_dist.trans hrR.le))
    rw [(hLog_d s hs_ball).deriv, hLog0, Complex.zero_re, sub_zero] at hbc
    have hcoeff : 2 * R / (R - r) ^ 2 = 16 * L / c := by
      dsimp only [R, r, η]
      field_simp [hc_pos.ne', hL_pos.ne']
      ring
    rw [hcoeff] at hbc
    have hneg_norm : ‖-deriv riemannZeta s / riemannZeta s‖ = ‖deriv riemannZeta s / riemannZeta s‖ := by
      rw [neg_div, norm_neg]
    rw [hneg_norm]
    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ (16 * L / c) * M := hbc
      _ = C_left * L ^ 2 := by dsimp only [C_left, M]; ring
      _ ≤ C₁ * L ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg L)

/-- **Unconditional Boundedness of `(-ζ'/ζ)(s) - 1/(s - 1)` Near `s = 1`**:
there exist `c₂ > 0` and `C₂ > 0` such that `negLogDerivZetaReg` is bounded by `C₂` on the
rectangle `[1 - c₂, 2] × [-1, 1]`, and hence
`‖(-deriv riemannZeta s / riemannZeta s) - 1 / (s - 1)‖ ≤ C₂` for all `s ≠ 1` in that rectangle. -/
theorem negLogDerivZeta_sub_pole_bounded_near_one :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ s : ℂ, 1 - c₂ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 →
        zetaReg s ≠ 0 ∧ ‖negLogDerivZetaReg s‖ ≤ C₂) ∧
      (∀ s : ℂ, 1 - c₂ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 → s ≠ 1 →
        ‖(-deriv riemannZeta s / riemannZeta s) - 1 / (s - 1)‖ ≤ C₂) := by
  obtain ⟨c₀, hc₀_pos, hzf₀⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set c₂ : ℝ := min (1 / 4) (c₀ / (2 * Real.log 3)) with hc₂_def
  have hc₂_pos : 0 < c₂ := lt_min (by norm_num) (by positivity)
  have hc₂_le_qtr : c₂ ≤ 1 / 4 := min_le_left _ _
  have hc₂_le_log : c₂ ≤ c₀ / (2 * Real.log 3) := min_le_right _ _
  set K : Set ℂ := {z : ℂ | 1 - c₂ ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1}
  have hK_comp : IsCompact K := by
    have hsub : K = Complex.equivRealProdCLM.symm '' (Set.Icc (1 - c₂) 2 ×ˢ Set.Icc (-1 : ℝ) 1) := by
      ext z
      simp only [K, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, Complex.ext (by simp) (by simp)⟩
      · rintro ⟨⟨x, y⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
    rw [hsub]
    exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hK_sub : K ⊆ {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
    intro z hz
    have hz_re : 0 < z.re := by linarith [hz.1]
    refine ⟨hz_re, ?_⟩
    by_cases hz1 : z = 1
    · subst hz1; rw [zetaReg_one]; exact one_ne_zero
    · rw [zetaReg_eq_mul_riemannZeta hz_re hz1]
      refine mul_ne_zero (sub_ne_zero.mpr hz1) ?_
      have hlog_le : Real.log (|z.im| + 2) ≤ Real.log 3 :=
        Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith [hz.2.2])
      have hlog_pos : 0 < Real.log (|z.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg z.im])
      have hdiv : c₂ ≤ c₀ / Real.log (|z.im| + 2) := by
        calc c₂ ≤ c₀ / (2 * Real.log 3) := hc₂_le_log
          _ ≤ c₀ / Real.log 3 := div_le_div_of_nonneg_left hc₀_pos.le hlog3_pos (by linarith)
          _ ≤ c₀ / Real.log (|z.im| + 2) := div_le_div_of_nonneg_left hc₀_pos.le hlog_pos hlog_le
      exact hzf₀ z (by linarith [hz.1]) hz1
  have hcont_K : ContinuousOn negLogDerivZetaReg K :=
    (differentiableOn_negLogDerivZetaReg.mono hK_sub).continuousOn
  obtain ⟨M, hM⟩ := hK_comp.exists_bound_of_continuousOn hcont_K
  set C₂ : ℝ := max M 1
  have hC₂_pos : 0 < C₂ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨c₂, hc₂_pos, C₂, hC₂_pos, ?_, ?_⟩
  · intro s hlo hhi him
    have hsK : s ∈ K := ⟨hlo, hhi, him⟩
    exact ⟨(hK_sub hsK).2, (hM s hsK).trans (le_max_left _ _)⟩
  · intro s hlo hhi him hs1
    have hsK : s ∈ K := ⟨hlo, hhi, him⟩
    have hs_re : 0 < s.re := (hK_sub hsK).1
    have hsnz : riemannZeta s ≠ 0 := by
      have hreg := (hK_sub hsK).2
      rw [zetaReg_eq_mul_riemannZeta hs_re hs1] at hreg
      exact (mul_ne_zero_iff.mp hreg).2
    rw [← negLogDerivZetaReg_eq_sub_pole hs_re hs1 hsnz]
    exact (hM s hsK).trans (le_max_left _ _)

/-! ## Section 2: Exact Zero-Free Perron Contour Shift for `ψ₁(x)` -/

/-- Integrated (Cesàro-1) Chebyshev sum `ψ₁(x) = ∑_{n ≤ x} Λ(n) * (x - n)`. -/
def psi1 (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * max (x - (n : ℝ)) 0

theorem psi1_nonneg (x : ℝ) : 0 ≤ psi1 x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right _ _)

theorem psi1_eq_psi1Char_one (x : ℝ) :
    (psi1 x : ℂ) = Stage4ExplicitFormula.psi1Char (1 : DirichletCharacter ℂ 1) x := by
  unfold psi1 Stage4ExplicitFormula.psi1Char
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Stage2DirichletAP.principal_char_apply_nat (q := 1) n]
  simp

lemma negLogDerivL_one_eq_negLogDerivZeta (s : ℂ) :
    Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ 1) s =
      Stage3ZeroFreeRegion.negLogDerivZeta s := by
  unfold Stage3ZeroFreeRegion.negLogDerivL Stage3ZeroFreeRegion.negLogDerivZeta
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  rw [hL]

/-- Exact rectangle boundary integral of `(s - 1)⁻¹` around `[σ, c] × [-T, T]` for `σ < 1 < c`
and `0 < T` equals `2 * π * I`, proved directly via elementary `log`/`arctan` antiderivatives. -/
theorem integral_boundary_rect_inv_sub_one {σ c T : ℝ} (hσ : σ < 1) (hc : 1 < c) (hT : 0 < T) :
    ((∫ u in σ..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) -
      (∫ u in σ..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹)) +
      I • (∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) -
      I • (∫ t in (-T)..T, ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹) =
      2 * Real.pi * I := by
  set a : ℝ := c - 1
  set b : ℝ := 1 - σ
  have ha : 0 < a := by dsimp only [a]; linarith
  have hb : 0 < b := by dsimp only [b]; linarith
  -- 1. Right vertical edge: `I * ∫_{-T}^T ((a : ℂ) + t * I)⁻¹ dt = 2 * I * arctan(T / a)`
  have hright : I • (∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) =
      2 * I * (Real.arctan (T / a) : ℂ) := by
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    set F_r : ℝ → ℂ := fun t =>
      ((Real.log (a ^ 2 + t ^ 2) / 2 : ℝ) : ℂ) + I * (Real.arctan (t / a) : ℂ)
    have hderiv : ∀ t ∈ Set.uIcc (-T) T,
        HasDerivAt F_r (I * ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) t := by
      intro t _
      have hden_pos : 0 < a ^ 2 + t ^ 2 := by positivity
      have h1 : HasDerivAt (fun u : ℝ => Real.log (a ^ 2 + u ^ 2) / 2) (t / (a ^ 2 + t ^ 2)) t := by
        have hsq : HasDerivAt (fun u : ℝ => a ^ 2 + u ^ 2) (2 * t) t := by
          simpa using (hasDerivAt_const t (a ^ 2)).fun_add (hasDerivAt_pow 2 t)
        refine ((hsq.log hden_pos.ne').div_const 2).congr_deriv ?_
        ring
      have h2 : HasDerivAt (fun u : ℝ => Real.arctan (u / a)) (a / (a ^ 2 + t ^ 2)) t := by
        have hlin : HasDerivAt (fun u : ℝ => u / a) (1 / a) t := by
          simpa using (hasDerivAt_id t).div_const a
        refine (hlin.arctan).congr_deriv ?_
        field_simp [ha.ne', hden_pos.ne']
      have h3 := h1.ofReal_comp.add (h2.ofReal_comp.const_mul I)
      refine h3.congr_deriv ?_
      have hca : (c : ℂ) + (t : ℂ) * I - 1 = (a : ℂ) + (t : ℂ) * I := by
        dsimp only [a]; push_cast; ring
      rw [hca]
      have hne1 : (a : ℂ) + (t : ℂ) * I ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hdenC : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden_pos.ne'
      push_cast
      rw [← div_eq_mul_inv, eq_div_iff hne1, ← mul_div_assoc, ← add_div, div_mul_eq_mul_div,
        div_eq_iff hdenC]
      linear_combination ((t : ℂ) * (a : ℂ)) * Complex.I_sq
    have hcont : ContinuousOn (fun t : ℝ => I * ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) (Set.uIcc (-T) T) := by
      refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun t _ h0 => ?_)
      have := congrArg Complex.re h0; simp at this; linarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    dsimp only [F_r]
    have hneg_sq : (-T) ^ 2 = T ^ 2 := by ring
    have hneg_div : -T / a = -(T / a) := neg_div a T
    rw [hneg_sq, hneg_div, Real.arctan_neg]
    push_cast; ring
  -- 2. Left vertical edge: `I * ∫_{-T}^T ((-b : ℂ) + t * I)⁻¹ dt = -2 * I * arctan(T / b)`
  have hleft : I • (∫ t in (-T)..T, ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹) =
      -(2 * I * (Real.arctan (T / b) : ℂ)) := by
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    set F_l : ℝ → ℂ := fun t =>
      ((Real.log (b ^ 2 + t ^ 2) / 2 : ℝ) : ℂ) - I * (Real.arctan (t / b) : ℂ)
    have hderiv : ∀ t ∈ Set.uIcc (-T) T,
        HasDerivAt F_l (I * ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹) t := by
      intro t _
      have hden_pos : 0 < b ^ 2 + t ^ 2 := by positivity
      have h1 : HasDerivAt (fun u : ℝ => Real.log (b ^ 2 + u ^ 2) / 2) (t / (b ^ 2 + t ^ 2)) t := by
        have hsq : HasDerivAt (fun u : ℝ => b ^ 2 + u ^ 2) (2 * t) t := by
          simpa using (hasDerivAt_const t (b ^ 2)).fun_add (hasDerivAt_pow 2 t)
        refine ((hsq.log hden_pos.ne').div_const 2).congr_deriv ?_
        ring
      have h2 : HasDerivAt (fun u : ℝ => Real.arctan (u / b)) (b / (b ^ 2 + t ^ 2)) t := by
        have hlin : HasDerivAt (fun u : ℝ => u / b) (1 / b) t := by
          simpa using (hasDerivAt_id t).div_const b
        refine (hlin.arctan).congr_deriv ?_
        field_simp [hb.ne', hden_pos.ne']
      have h3 := h1.ofReal_comp.sub (h2.ofReal_comp.const_mul I)
      refine h3.congr_deriv ?_
      have hσb : (σ : ℂ) + (t : ℂ) * I - 1 = -(b : ℂ) + (t : ℂ) * I := by
        dsimp only [b]; push_cast; ring
      rw [hσb]
      have hne1 : -(b : ℂ) + (t : ℂ) * I ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hdenC : (b : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden_pos.ne'
      push_cast
      rw [← div_eq_mul_inv, eq_div_iff hne1, ← mul_div_assoc, ← sub_div, div_mul_eq_mul_div,
        div_eq_iff hdenC]
      linear_combination (-(t : ℂ) * (b : ℂ)) * Complex.I_sq
    have hcont : ContinuousOn (fun t : ℝ => I * ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹) (Set.uIcc (-T) T) := by
      refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun t _ h0 => ?_)
      have := congrArg Complex.re h0; simp at this; linarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    dsimp only [F_l]
    have hneg_sq : (-T) ^ 2 = T ^ 2 := by ring
    have hneg_div : -T / b = -(T / b) := neg_div b T
    rw [hneg_sq, hneg_div, Real.arctan_neg]
    push_cast; ring
  -- 3. Bottom minus top horizontal edges: `2 * I * (arctan(a / T) + arctan(b / T))`
  have hhoriz : (∫ u in σ..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) -
      (∫ u in σ..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) =
      2 * I * ((Real.arctan (a / T) : ℂ) + (Real.arctan (b / T) : ℂ)) := by
    have hcont_bot : ContinuousOn (fun u : ℝ => ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) (Set.uIcc σ c) :=
      ContinuousOn.inv₀ (by fun_prop) fun u _ h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
    have hcont_top : ContinuousOn (fun u : ℝ => ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) (Set.uIcc σ c) :=
      ContinuousOn.inv₀ (by fun_prop) fun u _ h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
    rw [← intervalIntegral.integral_sub hcont_bot.intervalIntegrable hcont_top.intervalIntegrable]
    set F_h : ℝ → ℂ := fun u => 2 * I * (Real.arctan ((u - 1) / T) : ℂ)
    have hderiv : ∀ u ∈ Set.uIcc σ c,
        HasDerivAt F_h (((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹ - ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) u := by
      intro u _
      have hden_pos : 0 < (u - 1) ^ 2 + T ^ 2 := by positivity
      have h1 : HasDerivAt (fun x : ℝ => Real.arctan ((x - 1) / T))
          (T / ((u - 1) ^ 2 + T ^ 2)) u := by
        have hlin : HasDerivAt (fun x : ℝ => (x - 1) / T) (1 / T) u := by
          simpa using ((hasDerivAt_id u).sub_const 1).div_const T
        refine (hlin.arctan).congr_deriv ?_
        field_simp [hT.ne', hden_pos.ne']
        ring
      refine (h1.ofReal_comp.const_mul (2 * I)).congr_deriv ?_
      have hne1 : (u : ℂ) + ((-T : ℝ) : ℂ) * I - 1 ≠ 0 := fun h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
      have hne2 : (u : ℂ) + (T : ℂ) * I - 1 ≠ 0 := fun h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
      have hprod : ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1) * ((u : ℂ) + (T : ℂ) * I - 1) =
          ((u : ℂ) - 1) ^ 2 + (T : ℂ) ^ 2 := by
        push_cast
        linear_combination -((T : ℂ) ^ 2) * Complex.I_sq
      rw [inv_sub_inv hne1 hne2, hprod]
      push_cast
      rw [← mul_div_assoc]
      congr 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont_bot.sub hcont_top).intervalIntegrable]
    dsimp only [F_h]
    have hσ1 : (σ - 1) / T = -(b / T) := by dsimp only [b]; ring
    have hc1 : (c - 1) / T = a / T := rfl
    rw [hc1, hσ1, Real.arctan_neg]
    push_cast; ring
  -- 4. Sum all four edges using `Real.arctan_inv_of_pos`: `arctan(y) + arctan(1/y) = π/2`!
  rw [hhoriz, hright, hleft]
  have hpi_a : Real.arctan (T / a) + Real.arctan (a / T) = Real.pi / 2 := by
    have h := Real.arctan_inv_of_pos (div_pos hT ha)
    rw [inv_div] at h
    linarith
  have hpi_b : Real.arctan (T / b) + Real.arctan (b / T) = Real.pi / 2 := by
    have h := Real.arctan_inv_of_pos (div_pos hT hb)
    rw [inv_div] at h
    linarith
  have hpiC : ((Real.arctan (T / a) : ℂ) + (Real.arctan (a / T) : ℂ)) +
      ((Real.arctan (T / b) : ℂ) + (Real.arctan (b / T) : ℂ)) = (Real.pi : ℂ) := by
    norm_cast
    linarith
  calc 2 * I * ((Real.arctan (a / T) : ℂ) + (Real.arctan (b / T) : ℂ)) +
          2 * I * (Real.arctan (T / a) : ℂ) - -(2 * I * (Real.arctan (T / b) : ℂ))
      = 2 * I * (((Real.arctan (T / a) : ℂ) + (Real.arctan (a / T) : ℂ)) +
          ((Real.arctan (T / b) : ℂ) + (Real.arctan (b / T) : ℂ))) := by ring
    _ = 2 * I * (Real.pi : ℂ) := by rw [hpiC]
    _ = 2 * Real.pi * I := by ring

/-- **Exact Zero-Free Perron Contour Shift Identity for `truncatedPerronPsi1`**:
whenever `0 < x`, `0 < σ < 1 < c`, `0 < T`, and `riemannZeta` has no zeros on the closed rectangle
`[σ, c] × [-T, T]` (away from `s = 1`), shifting the vertical integral at `Re(s) = c` to `Re(s) = σ`
extracts the exact pole residue `(x : ℂ) ^ 2 / 2`! -/
theorem perron_contour_shift_psi1 {x σ c T : ℝ} (hx : 0 < x)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hc1 : 1 < c) (hT : 0 < T)
    (hzf : ∀ z : ℂ, σ ≤ z.re → z.re ≤ c → |z.im| ≤ T → z ≠ 1 → riemannZeta z ≠ 0) :
    let F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivZeta s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T -
        ((x : ℂ) ^ 2 / 2) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
      ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
      ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
  intro F
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set W : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1))
  have hW_one : W 1 = (x : ℂ) ^ 2 / 2 := by
    dsimp only [W]
    rw [show (1 : ℂ) + 1 = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    ring
  have hW_diff : DifferentiableOn ℂ W {s : ℂ | 0 < s.re} := by
    intro s hs
    have hs_re : 0 < s.re := hs
    have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (z + 1)) s := by
      have hEq : (fun z : ℂ => (x : ℂ) ^ (z + 1)) =
          fun z : ℂ => cexp (Complex.log (x : ℂ) * (z + 1)) :=
        funext fun z => Complex.cpow_def_of_ne_zero hxC _
      rw [hEq]; fun_prop
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_re; exact lt_irrefl 0 hs_re
    have hs1 : s + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact (hpow.div (differentiableAt_id.mul (differentiableAt_id.add (differentiableAt_const 1)))
      (mul_ne_zero hs0 hs1)).differentiableWithinAt
  set H₁ : ℂ → ℂ := fun s => negLogDerivZetaReg s * W s + dslope W 1 s
  -- `H₁` is holomorphic on `U = {s | 0 < s.re ∧ zetaReg s ≠ 0}` which contains `[σ, c] × [-T, T]`
  set U : Set ℂ := {s : ℂ | 0 < s.re ∧ zetaReg s ≠ 0}
  have hrect_sub : Set.uIcc σ c ×ℂ Set.uIcc (-T) T ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith : σ ≤ c),
      Set.uIcc_of_le (by linarith : -T ≤ T)] at hz
    have hz_re : 0 < z.re := lt_of_lt_of_le hσ0 hz.1.1
    refine ⟨hz_re, ?_⟩
    by_cases hz1 : z = 1
    · subst hz1; rw [zetaReg_one]; exact one_ne_zero
    · rw [zetaReg_eq_mul_riemannZeta hz_re hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1)
        (hzf z hz.1.1 hz.1.2 (abs_le.mpr hz.2) hz1)
  have hH₁_diff : DifferentiableOn ℂ H₁ (Set.uIcc σ c ×ℂ Set.uIcc (-T) T) := by
    have hds_diff : DifferentiableOn ℂ (dslope W 1) {s : ℂ | 0 < s.re} :=
      (Complex.differentiableOn_dslope
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (0 : ℝ) < (1 : ℂ).re))).mpr hW_diff
    have h1 : DifferentiableOn ℂ H₁ U :=
      (differentiableOn_negLogDerivZetaReg.mul (hW_diff.mono fun _ h => h.1)).add
        (hds_diff.mono fun _ h => h.1)
    exact h1.mono hrect_sub
  -- Apply Cauchy's rectangle theorem to `H₁`!
  set z₀ : ℂ := (σ : ℂ) + ((-T : ℝ) : ℂ) * I
  set w₀ : ℂ := (c : ℂ) + (T : ℂ) * I
  have hz₀_re : z₀.re = σ := by simp [z₀]
  have hz₀_im : z₀.im = -T := by simp [z₀]
  have hw₀_re : w₀.re = c := by simp [w₀]
  have hw₀_im : w₀.im = T := by simp [w₀]
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H₁ z₀ w₀
    (by simpa [hz₀_re, hz₀_im, hw₀_re, hw₀_im] using hH₁_diff)
  simp only [hz₀_re, hz₀_im, hw₀_re, hw₀_im] at hcauchy
  -- Pointwise decomposition `F s = H₁ s + (x^2 / 2) * (s - 1)⁻¹` for `s ∈ U \ {1}`
  have hdecomp : ∀ s ∈ U, s ≠ 1 → F s = H₁ s + ((x : ℂ) ^ 2 / 2) * (s - 1)⁻¹ := by
    intro s hs hs1
    have hsnz : riemannZeta s ≠ 0 := by
      have hreg := hs.2
      rw [zetaReg_eq_mul_riemannZeta hs.1 hs1] at hreg
      exact (mul_ne_zero_iff.mp hreg).2
    have hreg_eq := negLogDerivZetaReg_eq_sub_pole hs.1 hs1 hsnz
    dsimp only [F, H₁, Stage3ZeroFreeRegion.negLogDerivZeta]
    rw [hreg_eq, dslope_of_ne W hs1, slope_def_field, hW_one]
    have hsub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    dsimp only [W]
    field_simp [hsub_ne]
    ring
  -- Integrability helpers on all 4 edges
  have hH₁_cont : ContinuousOn H₁ (Set.uIcc σ c ×ℂ Set.uIcc (-T) T) := hH₁_diff.continuousOn
  have hbot_H₁ : IntervalIntegrable (fun u : ℝ => H₁ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) volume σ c := by
    refine (hH₁_cont.comp (by fun_prop) fun u hu => ?_).intervalIntegrable
    rw [Complex.mem_reProdIm]; simp [hu, Set.left_mem_uIcc]
  have htop_H₁ : IntervalIntegrable (fun u : ℝ => H₁ ((u : ℂ) + (T : ℂ) * I)) volume σ c := by
    refine (hH₁_cont.comp (by fun_prop) fun u hu => ?_).intervalIntegrable
    rw [Complex.mem_reProdIm]; simp [hu, Set.right_mem_uIcc]
  have hright_H₁ : IntervalIntegrable (fun t : ℝ => H₁ ((c : ℂ) + (t : ℂ) * I)) volume (-T) T := by
    refine (hH₁_cont.comp (by fun_prop) fun t ht => ?_).intervalIntegrable
    rw [Complex.mem_reProdIm]; simp [ht, Set.right_mem_uIcc]
  have hleft_H₁ : IntervalIntegrable (fun t : ℝ => H₁ ((σ : ℂ) + (t : ℂ) * I)) volume (-T) T := by
    refine (hH₁_cont.comp (by fun_prop) fun t ht => ?_).intervalIntegrable
    rw [Complex.mem_reProdIm]; simp [ht, Set.left_mem_uIcc]
  have hbot_inv : IntervalIntegrable (fun u : ℝ => ((x : ℂ) ^ 2 / 2) * ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹)
      volume σ c :=
    (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun u _ h0 => by
      have := congrArg Complex.im h0; simp at this; linarith)).intervalIntegrable
  have htop_inv : IntervalIntegrable (fun u : ℝ => ((x : ℂ) ^ 2 / 2) * ((u : ℂ) + (T : ℂ) * I - 1)⁻¹)
      volume σ c :=
    (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun u _ h0 => by
      have := congrArg Complex.im h0; simp at this; linarith)).intervalIntegrable
  have hright_inv : IntervalIntegrable (fun t : ℝ => ((x : ℂ) ^ 2 / 2) * ((c : ℂ) + (t : ℂ) * I - 1)⁻¹)
      volume (-T) T :=
    (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun t _ h0 => by
      have := congrArg Complex.re h0; simp at this; linarith)).intervalIntegrable
  have hleft_inv : IntervalIntegrable (fun t : ℝ => ((x : ℂ) ^ 2 / 2) * ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹)
      volume (-T) T :=
    (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun t _ h0 => by
      have := congrArg Complex.re h0; simp at this; linarith)).intervalIntegrable
  -- Rewrite each of the 4 edge integrals of `F` using `hdecomp`
  have hbot_F : ∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I) =
      (∫ u in σ..c, H₁ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) +
      ((x : ℂ) ^ 2 / 2) * ∫ u in σ..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hbot_H₁ hbot_inv]
    refine intervalIntegral.integral_congr fun u hu => hdecomp _ (hrect_sub ?_) fun h1 => ?_
    · rw [Complex.mem_reProdIm]; simp [hu, Set.left_mem_uIcc]
    · have := congrArg Complex.im h1; simp at this; linarith
  have htop_F : ∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I) =
      (∫ u in σ..c, H₁ ((u : ℂ) + (T : ℂ) * I)) +
      ((x : ℂ) ^ 2 / 2) * ∫ u in σ..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add htop_H₁ htop_inv]
    refine intervalIntegral.integral_congr fun u hu => hdecomp _ (hrect_sub ?_) fun h1 => ?_
    · rw [Complex.mem_reProdIm]; simp [hu, Set.right_mem_uIcc]
    · have := congrArg Complex.im h1; simp at this; linarith
  have hright_F : ∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I) =
      (∫ t in (-T)..T, H₁ ((c : ℂ) + (t : ℂ) * I)) +
      ((x : ℂ) ^ 2 / 2) * ∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hright_H₁ hright_inv]
    refine intervalIntegral.integral_congr fun t ht => hdecomp _ (hrect_sub ?_) fun h1 => ?_
    · rw [Complex.mem_reProdIm]; simp [ht, Set.right_mem_uIcc]
    · have := congrArg Complex.re h1; simp at this; linarith
  have hleft_F : ∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I) =
      (∫ t in (-T)..T, H₁ ((σ : ℂ) + (t : ℂ) * I)) +
      ((x : ℂ) ^ 2 / 2) * ∫ t in (-T)..T, ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hleft_H₁ hleft_inv]
    refine intervalIntegral.integral_congr fun t ht => hdecomp _ (hrect_sub ?_) fun h1 => ?_
    · rw [Complex.mem_reProdIm]; simp [ht, Set.left_mem_uIcc]
    · have := congrArg Complex.re h1; simp at this; linarith
  -- Combine `hcauchy` and `integral_boundary_rect_inv_sub_one`!
  have hres := integral_boundary_rect_inv_sub_one hσ1 hc1 hT
  have hrect_F :
      ((∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) -
        (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I))) +
      I * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) -
      I * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) =
      (2 * Real.pi * I) * ((x : ℂ) ^ 2 / 2) := by
    rw [hbot_F, htop_F, hright_F, hleft_F]
    simp only [smul_eq_mul] at hcauchy hres
    linear_combination hcauchy + ((x : ℂ) ^ 2 / 2) * hres
  -- Match `truncatedPerronPsi1 1 x c T` with `(2π)⁻¹ * ∫_{-T}^T F (c + t * I) dt`
  have htrunc_eq :
      Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I) := by
    unfold Stage4ExplicitFormula.truncatedPerronPsi1
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp only [F]
    rw [negLogDerivL_one_eq_negLogDerivZeta, mul_comm I (t : ℂ)]
    have hadd : (c : ℂ) + 1 + (t : ℂ) * I = (c : ℂ) + (t : ℂ) * I + 1 := by ring
    rw [hadd]
  rw [htrunc_eq]
  have h2pi_ne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  have hI_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2piI_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (2 * Real.pi * I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]
    exact mul_ne_zero h2pi_ne hI_ne
  -- Multiply both sides by `2 * π * I` to reduce to `hrect_F`
  apply mul_left_cancel₀ h2piI_ne
  have h2pi_cast : (2 * Real.pi * I : ℂ) * ((2 * Real.pi : ℝ) : ℂ)⁻¹ = I := by
    have : (2 * Real.pi * I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, mul_comm _ I, mul_assoc, mul_inv_cancel₀ h2pi_ne, mul_one]
  calc (2 * Real.pi * I : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) - (x : ℂ) ^ 2 / 2)
      = I * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) - (2 * Real.pi * I : ℂ) * ((x : ℂ) ^ 2 / 2) := by
        rw [mul_sub, ← mul_assoc, h2pi_cast]
    _ = I * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
        (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
        (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
        linear_combination hrect_F
    _ = (2 * Real.pi * I : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
          (2 * Real.pi * I : ℂ)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
          (2 * Real.pi * I : ℂ)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I))) := by
        rw [mul_sub, mul_add, ← mul_assoc, h2pi_cast, ← mul_assoc, ← mul_assoc,
          mul_inv_cancel₀ h2piI_ne, one_mul, one_mul]

/-- Elementary exponential decay inequality: `u * exp(-u) ≤ 1` for all `u : ℝ`. -/
private lemma mul_exp_neg_le_one (u : ℝ) : u * Real.exp (-u) ≤ 1 := by
  have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos u)).mpr h1

/-- Elementary quadratic-exponential decay inequality: `u² * exp(-2 u) ≤ 1` for all `u ≥ 0`. -/
private lemma sq_mul_exp_neg_two_le_one {u : ℝ} (hu : 0 ≤ u) : u ^ 2 * Real.exp (-2 * u) ≤ 1 := by
  have h1 := mul_exp_neg_le_one u
  have h2 : u ^ 2 * Real.exp (-2 * u) = (u * Real.exp (-u)) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [h2]
  nlinarith [mul_nonneg hu (Real.exp_pos (-u)).le]

/-- **UNCONDITIONAL EFFECTIVE PRIME NUMBER THEOREM FOR `ψ₁(x)` (0 ASSUMPTIONS!)**:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |psi1 x - x ^ 2 / 2| ≤ C * x ^ 2 * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem effective_pnt_psi1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |psi1 x - x ^ 2 / 2| ≤ C * x ^ 2 * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := negLogDerivZeta_zeroFree_bound
  obtain ⟨c₂, hc₂, C₂, hC₂, hbd₂, hbd₂'⟩ := negLogDerivZeta_sub_pole_bounded_near_one
  obtain ⟨c₀, hc₀, hzf₀⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Unified zero-free width constant `c_*`
  set c_star : ℝ := min (min c₀ c₁) (min (c₂ * Real.log 2) (1 / 4)) with hc_star_def
  have hc_star_pos : 0 < c_star := by positivity
  have hc_star_le_c₀ : c_star ≤ c₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hc_star_le_c₁ : c_star ≤ c₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hc_star_le_c₂ : c_star ≤ c₂ * Real.log 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc_star_le_qtr : c_star ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  -- Optimal height exponent `α = √(c_star / 2)`, final decay exponent `c_fin = α / 2`
  set α : ℝ := Real.sqrt (c_star / 2) with hα_def
  have hα_pos : 0 < α := Real.sqrt_pos.mpr (by positivity)
  have hα_sq : α ^ 2 = c_star / 2 := Real.sq_sqrt (by positivity)
  set c_fin : ℝ := α / 2 with hc_fin_def
  have hc_fin_pos : 0 < c_fin := by positivity
  -- Threshold `x₀` so that `α * √(log x) ≥ 1` (hence `T ≥ e > 2`) for all `x ≥ x₀`
  set x₀ : ℝ := max 2 (Real.exp (1 / α ^ 2)) with hx₀_def
  have hx₀_ge2 : 2 ≤ x₀ := le_max_left _ _
  -- Constant `K_large` for `x ≥ x₀`
  set K_left : ℝ := C₁ + 2 * (C₂ + 1 / c_star)
  have hK_left_pos : 0 < K_left := by positivity
  set K_large : ℝ :=
    (48 / Real.pi + (K_left / Real.pi + 2 * C₁ / Real.pi) * (4 * α ^ 2)) * (16 / α ^ 2)
  have hK_large_pos : 0 < K_large := by positivity
  -- Step 1: Prove the bound for all `x ≥ x₀`
  have hlarge : ∀ x : ℝ, x₀ ≤ x →
      |psi1 x - x ^ 2 / 2| ≤ K_large * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
    intro x hx
    have hx2 : 2 ≤ x := hx₀_ge2.trans hx
    have hx0 : 0 < x := by linarith
    set Lx : ℝ := Real.log x with hLx_def
    have hLx_ge_log2 : Real.log 2 ≤ Lx := Real.log_le_log (by norm_num) hx2
    have hLx_pos : 0 < Lx := hlog2_pos.trans_le hLx_ge_log2
    have hLx_ge_inv : 1 / α ^ 2 ≤ Lx := by
      have hexp : Real.exp (1 / α ^ 2) ≤ x := (le_max_right _ _).trans hx
      exact (Real.log_exp (1 / α ^ 2)).symm.trans_le (Real.log_le_log (Real.exp_pos _) hexp)
    have hα_sqrt_ge1 : 1 ≤ α * Real.sqrt Lx := by
      have hsq : 1 ^ 2 ≤ (α * Real.sqrt Lx) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hLx_pos.le, one_pow]
        have h := mul_le_mul_of_nonneg_left hLx_ge_inv (sq_nonneg α)
        rwa [mul_one_div_cancel (sq_pos_of_pos hα_pos).ne'] at h
      nlinarith [mul_nonneg hα_pos.le (Real.sqrt_nonneg Lx)]
    set T : ℝ := Real.exp (α * Real.sqrt Lx) with hT_def
    have hT_pos : 0 < T := Real.exp_pos _
    have hT_ge_e : Real.exp 1 ≤ T := Real.exp_le_exp.mpr hα_sqrt_ge1
    have hT_ge2 : 2 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlogT : Real.log T = α * Real.sqrt Lx := Real.log_exp _
    set LT : ℝ := Real.log (T + 2) with hLT_def
    have hLT_ge1 : 1 ≤ LT := by
      have h : Real.exp 1 ≤ T + 2 := by linarith
      exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) h)
    have hLT_pos : 0 < LT := zero_lt_one.trans_le hLT_ge1
    have hLT_le : LT ≤ 2 * (α * Real.sqrt Lx) := by
      have hle2T : T + 2 ≤ 2 * T := by linarith
      have h1 : LT ≤ Real.log (2 * T) := Real.log_le_log (by linarith) hle2T
      rw [Real.log_mul (by norm_num) hT_pos.ne', hlogT] at h1
      have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
    -- Contour parameters `c` and `σ_T`
    set c : ℝ := 1 + 1 / (2 * Lx) with hc_def
    have hc_gt1 : 1 < c := by dsimp only [c]; linarith [div_pos one_pos (by linarith : 0 < 2 * Lx)]
    have hc_le2 : c ≤ 2 := by
      have h2Lx : 1 ≤ 2 * Lx := by linarith [Real.log_two_gt_d9]
      have : 1 / (2 * Lx) ≤ 1 := (div_le_one (by linarith)).mpr h2Lx
      dsimp only [c]; linarith
    have hx_pow_c : x ^ (c + 1) ≤ 2 * x ^ 2 := by
      have h1 : x ^ (c + 1) = x ^ 2 * x ^ (1 / (2 * Lx)) := by
        rw [show c + 1 = (2 : ℝ) + 1 / (2 * Lx) by dsimp only [c]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (1 / (2 * Lx)) = Real.exp (1 / 2) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]
        congr 1; field_simp [hLx_pos.ne']
      have h3 : Real.exp (1 / 2) ≤ 2 := by
        have hsq : (Real.exp (1 / 2)) ^ 2 ≤ 2 ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num
          linarith [Real.exp_one_lt_d9]
        nlinarith [Real.exp_pos (1 / 2)]
      rw [h1, h2]
      nlinarith [sq_nonneg x]
    set σ_T : ℝ := 1 - c_star / LT with hσ_def
    have hσ_lt1 : σ_T < 1 := by dsimp only [σ_T]; linarith [div_pos hc_star_pos hLT_pos]
    have hσ_ge_half : 1 / 2 ≤ σ_T := by
      have h1 : c_star / LT ≤ 1 / 4 := by
        calc c_star / LT ≤ c_star / 1 := div_le_div_of_nonneg_left hc_star_pos.le zero_lt_one hLT_ge1
          _ = c_star := div_one _
          _ ≤ 1 / 4 := hc_star_le_qtr
      dsimp only [σ_T]; linarith
    have hσ_pos : 0 < σ_T := by linarith
    have hσ_ge_c₂ : 1 - c₂ ≤ σ_T := by
      have hlog2_le_LT : Real.log 2 ≤ LT := Real.log_le_log (by norm_num) (by linarith)
      have h1 : c_star / LT ≤ c₂ := by
        rw [div_le_iff₀ hLT_pos]
        exact hc_star_le_c₂.trans (mul_le_mul_of_nonneg_left hlog2_le_LT hc₂.le)
      dsimp only [σ_T]; linarith
    -- Zero-freeness on `[σ_T, c] × [-T, T]`
    have hzf_rect : ∀ z : ℂ, σ_T ≤ z.re → z.re ≤ c → |z.im| ≤ T → z ≠ 1 → riemannZeta z ≠ 0 := by
      intro z hlo _ him hz1
      have hlog_le : Real.log (|z.im| + 2) ≤ LT :=
        Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
      have hlog_pos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
      have h1 : c_star / LT ≤ c₀ / Real.log (|z.im| + 2) := by
        calc c_star / LT ≤ c_star / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_left hc_star_pos.le hlog_pos hlog_le
          _ ≤ c₀ / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_right hc_star_le_c₀ hlog_pos.le
      exact hzf₀ z (by linarith) hz1
    -- Define integrand `F`
    set F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivZeta s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    -- (A) Truncation error from `Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le`
    have htrunc_err :
        ‖(psi1 x : ℂ) - Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T‖ ≤
          (48 / Real.pi) * x ^ 2 * Lx / T := by
      rw [psi1_eq_psi1Char_one]
      have h0 := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le
        (1 : DirichletCharacter ℂ 1) hx0 hc_gt1 hT_pos
      have hc_sub : c - 1 = 1 / (2 * Lx) := by dsimp only [c]; ring
      rw [hc_sub] at h0
      calc ‖Stage4ExplicitFormula.psi1Char (1 : DirichletCharacter ℂ 1) x -
              Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T‖
          ≤ (6 * c / Real.pi) * x ^ (c + 1) / (1 / (2 * Lx) * T) := h0
        _ ≤ (6 * 2 / Real.pi) * (2 * x ^ 2) / (1 / (2 * Lx) * T) := by
            gcongr
        _ = (48 / Real.pi) * x ^ 2 * Lx / T := by
            field_simp [Real.pi_ne_zero, hLx_pos.ne', hT_pos.ne']; ring
    -- (B) Exact contour shift identity
    have hshift := perron_contour_shift_psi1 hx0 hσ_pos hσ_lt1 hc_gt1 hT_pos hzf_rect
    -- (C) Horizontal segment bounds (`t = ±T`, `u ∈ [σ_T, c]`)
    have hhoriz_bd : ∀ sgn : ℝ, |sgn| = 1 →
        ‖∫ u in σ_T..c, F ((u : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
          2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by
      intro sgn hsgn
      have hle : σ_T ≤ c := by linarith
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2) fun u hu => ?_).trans ?_
      · rw [Set.uIoc_of_le hle] at hu
        set z : ℂ := (u : ℂ) + ((sgn * T : ℝ) : ℂ) * I
        have hz_re : z.re = u := by simp [z]
        have hz_im : z.im = sgn * T := by simp [z]
        have hz_abs_im : |z.im| = T := by
          rw [hz_im, abs_mul, hsgn, one_mul, abs_of_pos hT_pos]
        have hz_re_lo : 1 - c₁ / Real.log (|z.im| + 2) ≤ z.re := by
          rw [hz_re, hz_abs_im]
          have : c_star / LT ≤ c₁ / LT := div_le_div_of_nonneg_right hc_star_le_c₁ hLT_pos.le
          dsimp only [σ_T] at hu; linarith [hu.1]
        have hz_re_hi : z.re ≤ 2 := by rw [hz_re]; linarith [hu.2]
        have hnd := hbd₁ z hz_re_lo hz_re_hi (by rw [hz_abs_im]; linarith)
        rw [hz_abs_im] at hnd
        have hpow_norm : ‖(x : ℂ) ^ (z + 1)‖ ≤ x ^ (c + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre1 : (z + 1).re = u + 1 := by simp [hz_re]
          rw [hre1]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hu.2])
        have hden_ge : T ^ 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : T ≤ ‖z‖ := by rw [← hz_abs_im]; exact Complex.abs_im_le_norm z
          have h2 : T ≤ ‖z + 1‖ := by
            have := Complex.abs_im_le_norm (z + 1)
            simpa [hz_abs_im] using this
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivZeta]
        rw [norm_div, norm_mul]
        calc ‖-deriv riemannZeta z / riemannZeta z‖ * ‖(x : ℂ) ^ (z + 1)‖ / ‖z * (z + 1)‖
            ≤ (C₁ * LT ^ 2) * x ^ (c + 1) / T ^ 2 := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul hnd hpow_norm (norm_nonneg _) (by positivity))
                (sq_pos_of_pos hT_pos) hden_ge
          _ = C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by ring
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        have hlen : c - σ_T ≤ 2 := by linarith
        calc C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 * (c - σ_T)
            ≤ C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 * 2 :=
              mul_le_mul_of_nonneg_left hlen (by positivity)
          _ = 2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by ring
    have htop_bd : ‖∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by
      simpa using hhoriz_bd 1 (by norm_num)
    have hbot_bd : ‖∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by
      simpa using hhoriz_bd (-1) (by norm_num)
    -- (D) Left vertical segment bound (`s = σ_T + t * I`, `t ∈ [-T, T]`)
    have hleft_cont : ContinuousOn (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
      have hopen := isOpen_re_pos_zetaReg_ne_zero
      have hmap : Continuous (fun t : ℝ => (σ_T : ℂ) + (t : ℂ) * I) := by fun_prop
      have hmem : ∀ t ∈ Set.Icc (-T) T, (σ_T : ℂ) + (t : ℂ) * I ∈ {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
        intro t ht
        refine ⟨by simp [hσ_pos], ?_⟩
        have hne1 : (σ_T : ℂ) + (t : ℂ) * I ≠ 1 := fun h1 => by
          have := congrArg Complex.re h1; simp at this; linarith
        rw [zetaReg_eq_mul_riemannZeta (by simp [hσ_pos]) hne1]
        exact mul_ne_zero (sub_ne_zero.mpr hne1)
          (hzf_rect _ (by simp) (by simp; linarith) (by simp [abs_le, ht.1, ht.2]) hne1)
      have hnd_cont : ContinuousOn (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivZeta ((σ_T : ℂ) + (t : ℂ) * I))
          (Set.Icc (-T) T) := by
        have hreg_cont : ContinuousOn (fun t : ℝ => negLogDerivZetaReg ((σ_T : ℂ) + (t : ℂ) * I) +
            1 / ((σ_T : ℂ) + (t : ℂ) * I - 1)) (Set.Icc (-T) T) := by
          refine (differentiableOn_negLogDerivZetaReg.continuousOn.comp hmap.continuousOn hmem).add ?_
          refine continuousOn_const.div (by fun_prop) fun t _ h0 => ?_
          have := congrArg Complex.re h0; simp at this; linarith
        refine hreg_cont.congr fun t ht => ?_
        have hne1 : (σ_T : ℂ) + (t : ℂ) * I ≠ 1 := fun h1 => by
          have := congrArg Complex.re h1; simp at this; linarith
        have hnz : riemannZeta ((σ_T : ℂ) + (t : ℂ) * I) ≠ 0 :=
          hzf_rect _ (by simp) (by simp; linarith) (by simp [abs_le, ht.1, ht.2]) hne1
        dsimp only [Stage3ZeroFreeRegion.negLogDerivZeta]
        rw [negLogDerivZetaReg_eq_sub_pole (by simp [hσ_pos]) hne1 hnz]
        ring
      have hpow_cont : Continuous (fun t : ℝ => (x : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) := by
        have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
        have hEq : (fun t : ℝ => (x : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) =
            fun t : ℝ => cexp (Complex.log (x : ℂ) * (((σ_T : ℂ) + (t : ℂ) * I) + 1)) :=
          funext fun t => Complex.cpow_def_of_ne_zero hxC _
        rw [hEq]; fun_prop
      refine (hnd_cont.mul hpow_cont.continuousOn).div (by fun_prop) fun t _ => mul_ne_zero ?_ ?_
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hint_seg : ∀ a b : ℝ, -T ≤ a → a ≤ b → b ≤ T →
        IntervalIntegrable (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) volume a b := by
      intro a b ha hab hb
      refine (hleft_cont.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab]
      exact fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
    -- Split `[-T, T] = [-T, -1] ∪ [-1, 1] ∪ [1, T]`
    have hsplit_left :
        ∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I) =
          (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith))
        (hint_seg (-1) 1 (by linarith) (by norm_num) (by linarith))
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hint_seg (-T) 1 le_rfl (by linarith) (by linarith))
        (hint_seg 1 T (by linarith) (by linarith) le_rfl)
      rw [h1, h2]
    -- Piece 1: `t ∈ [1, T]` (and identically `t ∈ [-T, -1]`)
    have hleft_tail_pt : ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
        ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * LT ^ 2 * x ^ (σ_T + 1) / t ^ 2 := by
      intro t ht1 htT
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have hz_im : z.im = t := by simp [z]
      have hlog_le : Real.log (|t| + 2) ≤ LT := Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
      have hlog_pos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
      have hz_re_lo : 1 - c₁ / Real.log (|z.im| + 2) ≤ z.re := by
        rw [hz_re, hz_im]
        have h1 : c_star / LT ≤ c₁ / Real.log (|t| + 2) := by
          calc c_star / LT ≤ c_star / Real.log (|t| + 2) :=
                div_le_div_of_nonneg_left hc_star_pos.le hlog_pos hlog_le
            _ ≤ c₁ / Real.log (|t| + 2) :=
                div_le_div_of_nonneg_right hc_star_le_c₁ hlog_pos.le
        dsimp only [σ_T]; linarith
      have hnd := hbd₁ z hz_re_lo (by rw [hz_re]; linarith) (by rw [hz_im]; exact ht1)
      have hnd' : ‖-deriv riemannZeta z / riemannZeta z‖ ≤ C₁ * LT ^ 2 := by
        rw [hz_im] at hnd
        exact hnd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog_pos.le hlog_le 2) hC₁.le)
      have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp [hz_re]
      have hden : t ^ 2 ≤ ‖z * (z + 1)‖ := by
        rw [norm_mul]
        have h1 : |t| ≤ ‖z‖ := by rw [← hz_im]; exact Complex.abs_im_le_norm z
        have h2 : |t| ≤ ‖z + 1‖ := by
          have := Complex.abs_im_le_norm (z + 1); simpa [hz_im] using this
        have hsq : t ^ 2 = |t| * |t| := by rw [← sq_abs, sq]
        rw [hsq]
        exact mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg z)
      have ht2_pos : 0 < t ^ 2 := by
        have : t ≠ 0 := fun h => by rw [h, abs_zero] at ht1; linarith
        positivity
      dsimp only [F, Stage3ZeroFreeRegion.negLogDerivZeta]
      rw [norm_div, norm_mul, hpow]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hx0.le _))
        ht2_pos hden
    have hinv_sq_1T : ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun u : ℝ => -(u⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        exact ((hasDerivAt_inv ht0).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (1 : ℝ) T) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.1])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      have : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_pos.le
      linarith
    have hinv_sq_neg : ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (-T) (-1 : ℝ), HasDerivAt (fun u : ℝ => -(u⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        have ht0 : t ≠ 0 := by linarith [ht.2]
        exact ((hasDerivAt_inv ht0).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (-T) (-1 : ℝ)) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.2])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      have : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_pos.le
      simp only [inv_neg, neg_neg, inv_one]
      linarith
    have hleft_pos_bd : ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C₁ * LT ^ 2 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (1 : ℝ) T := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact pow_ne_zero 2 (by linarith [ht.1])
      calc ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (1 : ℝ)..T, ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (1 : ℝ)..T, C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg 1 T (by linarith) (by linarith) le_rfl).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1)
              (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.2)
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) * ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 2 * x ^ (σ_T + 1) * 1 :=
            mul_le_mul_of_nonneg_left hinv_sq_1T (by positivity)
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) := mul_one _
    have hleft_neg_bd : ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C₁ * LT ^ 2 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (-T) (-1 : ℝ) := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact pow_ne_zero 2 (by linarith [ht.2])
      calc ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (-T)..(-1 : ℝ), ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (-T)..(-1 : ℝ), C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith)).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
              (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) * ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 2 * x ^ (σ_T + 1) * 1 :=
            mul_le_mul_of_nonneg_left hinv_sq_neg (by positivity)
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) := mul_one _
    -- Piece 2: `t ∈ [-1, 1]`
    have hleft_mid_bd : ‖∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        4 * (C₂ + 1 / c_star) * LT ^ 2 * x ^ (σ_T + 1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 2 * (C₂ + 1 / c_star) * LT ^ 2 * x ^ (σ_T + 1)) fun t ht => ?_).trans ?_
      · rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
        have hz_re : z.re = σ_T := by simp [z]
        have hz_im : z.im = t := by simp [z]
        have hz1 : z ≠ 1 := fun h => by have := congrArg Complex.re h; rw [hz_re] at this; simp at this; linarith
        have hreg := hbd₂' z (by rw [hz_re]; exact hσ_ge_c₂) (by rw [hz_re]; linarith)
          (by rw [hz_im, abs_le]; exact ⟨ht.1.le, ht.2⟩) hz1
        have hpole_bd : ‖(1 : ℂ) / (z - 1)‖ ≤ LT / c_star := by
          rw [norm_div, norm_one]
          have hre_sub : c_star / LT ≤ ‖z - 1‖ := by
            have := Complex.abs_re_le_norm (z - 1)
            rw [Complex.sub_re, hz_re, Complex.one_re, show σ_T - 1 = -(c_star / LT) by dsimp only [σ_T]; ring,
              abs_neg, abs_of_pos (div_pos hc_star_pos hLT_pos)] at this
            exact this
          have h1 : 1 / ‖z - 1‖ ≤ 1 / (c_star / LT) :=
            div_le_div_of_nonneg_left zero_le_one (div_pos hc_star_pos hLT_pos) hre_sub
          simpa [one_div_div] using h1
        have hnd_bd : ‖-deriv riemannZeta z / riemannZeta z‖ ≤ (C₂ + 1 / c_star) * LT ^ 2 := by
          have htri : ‖-deriv riemannZeta z / riemannZeta z‖ ≤
              ‖(-deriv riemannZeta z / riemannZeta z) - 1 / (z - 1)‖ + ‖(1 : ℂ) / (z - 1)‖ := by
            simpa [sub_add_cancel] using
              norm_add_le ((-deriv riemannZeta z / riemannZeta z) - 1 / (z - 1)) (1 / (z - 1))
          have hLT_le_sq : LT ≤ LT ^ 2 := by nlinarith
          have h1_le_sq : 1 ≤ LT ^ 2 := by nlinarith
          calc ‖-deriv riemannZeta z / riemannZeta z‖
              ≤ C₂ + LT / c_star := by linarith
            _ = C₂ * 1 + (1 / c_star) * LT := by ring
            _ ≤ C₂ * LT ^ 2 + (1 / c_star) * LT ^ 2 := by
                have h1 : C₂ * 1 ≤ C₂ * LT ^ 2 := mul_le_mul_of_nonneg_left h1_le_sq hC₂.le
                have h2 : (1 / c_star) * LT ≤ (1 / c_star) * LT ^ 2 :=
                  mul_le_mul_of_nonneg_left hLT_le_sq (by positivity)
                linarith
            _ = (C₂ + 1 / c_star) * LT ^ 2 := by ring
        have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [hz_re]
        have hden : 1 / 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : 1 / 2 ≤ ‖z‖ := by
            have := Complex.abs_re_le_norm z; rw [hz_re, abs_of_pos hσ_pos] at this; linarith
          have h2 : 1 ≤ ‖z + 1‖ := by
            have := Complex.abs_re_le_norm (z + 1)
            have hre1 : (z + 1).re = σ_T + 1 := by simp [hz_re]
            rw [hre1, abs_of_pos (by linarith)] at this; linarith
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivZeta]
        rw [norm_div, norm_mul, hpow]
        calc ‖-deriv riemannZeta z / riemannZeta z‖ * x ^ (σ_T + 1) / ‖z * (z + 1)‖
            ≤ ((C₂ + 1 / c_star) * LT ^ 2) * x ^ (σ_T + 1) / (1 / 2) := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_right hnd_bd (Real.rpow_nonneg hx0.le _)) (by norm_num) hden
          _ = 2 * (C₂ + 1 / c_star) * LT ^ 2 * x ^ (σ_T + 1) := by ring
      · norm_num
        linarith
    have hleft_bd : ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        2 * K_left * LT ^ 2 * x ^ (σ_T + 1) := by
      rw [hsplit_left]
      have htri1 := norm_add_le
        ((∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)))
        (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I))
      have htri2 := norm_add_le
        (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I))
        (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I))
      dsimp only [K_left]
      linarith
    -- (E) Combine truncation error + contour shift bounds!
    have hshift_bd :
        ‖Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T - ((x : ℂ) ^ 2 / 2)‖ ≤
          (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) +
          (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by
      rw [hshift]
      have hnorm_2pi : ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hnorm_2piI : ‖((2 * Real.pi * I : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
      have htri :
          ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)) -
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤
          (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
        have h1 := norm_sub_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)))
        have h2 := norm_add_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)))
        simp only [norm_mul, hnorm_2pi, hnorm_2piI] at h1 h2
        linarith
      have hterm_left : (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
          (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) := by
        calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
            ≤ (2 * Real.pi)⁻¹ * (2 * K_left * LT ^ 2 * x ^ (σ_T + 1)) :=
              mul_le_mul_of_nonneg_left hleft_bd (by positivity)
          _ = (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) := by field_simp [Real.pi_ne_zero]
      have hterm_horiz : ∀ Ival : ℂ, ‖Ival‖ ≤ 2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 →
          (2 * Real.pi)⁻¹ * ‖Ival‖ ≤ (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by
        intro Ival hIval
        have hxc_div : x ^ (c + 1) / T ^ 2 ≤ x ^ 2 / T := by
          have h1 : x ^ (c + 1) / T ^ 2 ≤ (2 * x ^ 2) / T ^ 2 :=
            div_le_div_of_nonneg_right hx_pow_c (sq_nonneg T)
          have h2 : 2 * x ^ 2 / T ^ 2 ≤ x ^ 2 / T := by
            rw [div_le_div_iff₀ (sq_pos_of_pos hT_pos) hT_pos]
            have hT2 : 2 * T ≤ T ^ 2 := by nlinarith
            nlinarith [sq_nonneg x]
          linarith
        calc (2 * Real.pi)⁻¹ * ‖Ival‖
            ≤ (2 * Real.pi)⁻¹ * (2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2) :=
              mul_le_mul_of_nonneg_left hIval (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 2 * (x ^ (c + 1) / T ^ 2) := by
              field_simp [Real.pi_ne_zero, hT_pos.ne']
          _ ≤ (C₁ / Real.pi) * LT ^ 2 * (x ^ 2 / T) :=
              mul_le_mul_of_nonneg_left hxc_div (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by ring
      have htop_h := hterm_horiz _ htop_bd
      have hbot_h := hterm_horiz _ hbot_bd
      change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)) -
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤ _
      have hsum2 : (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T + (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T =
          (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by ring
      linarith
    -- (F) Combine all errors and substitute `T = exp(α √Lx)`!
    have htotal : |psi1 x - x ^ 2 / 2| ≤
        (48 / Real.pi) * x ^ 2 * Lx / T +
        (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) +
        (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by
      have hcast : |psi1 x - x ^ 2 / 2| = ‖(psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2)‖ := by
        have h : (psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2) = (((psi1 x - x ^ 2 / 2 : ℝ) : ℂ)) := by
          push_cast; ring
        rw [h, Complex.norm_real, Real.norm_eq_abs]
      rw [hcast]
      have htri : ‖(psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2)‖ ≤
          ‖(psi1 x : ℂ) - Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T‖ +
          ‖Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T - ((x : ℂ) ^ 2 / 2)‖ := by
        have h1 := norm_add_le
          ((psi1 x : ℂ) - Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T)
          (Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T - ((x : ℂ) ^ 2 / 2))
        rwa [sub_add_sub_cancel] at h1
      linarith
    -- Match the two exponential factors: `x^(σ_T + 1) ≤ x^2 * exp(-α √Lx)` and `1 / T = exp(-α √Lx)`
    have hx_left_exp : x ^ (σ_T + 1) ≤ x ^ 2 * Real.exp (-α * Real.sqrt Lx) := by
      have h1 : x ^ (σ_T + 1) = x ^ 2 * x ^ (-(c_star / LT)) := by
        rw [show σ_T + 1 = (2 : ℝ) + (-(c_star / LT)) by dsimp only [σ_T]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (-(c_star / LT)) = Real.exp (-(c_star * Lx / LT)) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]; congr 1; ring
      have hexp_le : -(c_star * Lx / LT) ≤ -α * Real.sqrt Lx := by
        have hsqrt_pos : 0 < Real.sqrt Lx := Real.sqrt_pos.mpr hLx_pos
        have hdiv : α * Real.sqrt Lx ≤ c_star * Lx / LT := by
          rw [le_div_iff₀ hLT_pos]
          calc α * Real.sqrt Lx * LT
              ≤ α * Real.sqrt Lx * (2 * (α * Real.sqrt Lx)) :=
                mul_le_mul_of_nonneg_left hLT_le (by positivity)
            _ = 2 * α ^ 2 * (Real.sqrt Lx) ^ 2 := by ring
            _ = 2 * (c_star / 2) * Lx := by rw [hα_sq, Real.sq_sqrt hLx_pos.le]
            _ = c_star * Lx := by ring
        linarith
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (sq_nonneg x)
    have hinvT : (1 : ℝ) / T = Real.exp (-α * Real.sqrt Lx) := by
      rw [hT_def, one_div, ← Real.exp_neg]; congr 1; ring
    have hLT_sq : LT ^ 2 ≤ (4 * α ^ 2) * Lx := by
      have h1 := pow_le_pow_left₀ hLT_pos.le hLT_le 2
      have h2 : (2 * (α * Real.sqrt Lx)) ^ 2 = (4 * α ^ 2) * Lx := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hLx_pos.le]; ring
      linarith
    -- Absorb `Lx` into `exp(-(α / 2) * √Lx)`: `Lx * exp(-(α / 2) * √Lx) ≤ 16 / α ^ 2`
    have habsorb : Lx * Real.exp (-α * Real.sqrt Lx) ≤ (16 / α ^ 2) * Real.exp (-c_fin * Real.sqrt Lx) := by
      have hsplit : Real.exp (-α * Real.sqrt Lx) =
          Real.exp (-2 * ((α / 4) * Real.sqrt Lx)) * Real.exp (-c_fin * Real.sqrt Lx) := by
        rw [← Real.exp_add]; congr 1; dsimp only [c_fin]; ring
      rw [hsplit, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hu_nn : 0 ≤ (α / 4) * Real.sqrt Lx := by positivity
      have hsq_id : Lx * Real.exp (-2 * ((α / 4) * Real.sqrt Lx)) =
          (16 / α ^ 2) * (((α / 4) * Real.sqrt Lx) ^ 2 * Real.exp (-2 * ((α / 4) * Real.sqrt Lx))) := by
        have h1 : Lx = (16 / α ^ 2) * ((α / 4) * Real.sqrt Lx) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hLx_pos.le]
          field_simp [hα_pos.ne']; ring
        have h2 := congrArg (· * Real.exp (-2 * ((α / 4) * Real.sqrt Lx))) h1
        simpa only [mul_assoc] using h2
      calc Lx * Real.exp (-2 * ((α / 4) * Real.sqrt Lx))
          = (16 / α ^ 2) * (((α / 4) * Real.sqrt Lx) ^ 2 * Real.exp (-2 * ((α / 4) * Real.sqrt Lx))) := hsq_id
        _ ≤ (16 / α ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left (sq_mul_exp_neg_two_le_one hu_nn) (by positivity)
        _ = 16 / α ^ 2 := mul_one _
    -- Put the three terms together!
    have hterm1 : (48 / Real.pi) * x ^ 2 * Lx / T =
        (48 / Real.pi) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]; ring
    have hterm2 : (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) ≤
        ((K_left / Real.pi) * (4 * α ^ 2)) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by
      calc (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1)
          ≤ (K_left / Real.pi) * ((4 * α ^ 2) * Lx) * (x ^ 2 * Real.exp (-α * Real.sqrt Lx)) := by
            gcongr
        _ = ((K_left / Real.pi) * (4 * α ^ 2)) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by ring
    have hterm3 : (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T ≤
        ((2 * C₁ / Real.pi) * (4 * α ^ 2)) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]
      calc (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 * Real.exp (-α * Real.sqrt Lx)
          ≤ (2 * C₁ / Real.pi) * ((4 * α ^ 2) * Lx) * x ^ 2 * Real.exp (-α * Real.sqrt Lx) := by
            gcongr
        _ = ((2 * C₁ / Real.pi) * (4 * α ^ 2)) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by ring
    calc |psi1 x - x ^ 2 / 2|
        ≤ (48 / Real.pi + (K_left / Real.pi + 2 * C₁ / Real.pi) * (4 * α ^ 2)) *
            x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by linarith
      _ ≤ (48 / Real.pi + (K_left / Real.pi + 2 * C₁ / Real.pi) * (4 * α ^ 2)) *
            x ^ 2 * ((16 / α ^ 2) * Real.exp (-c_fin * Real.sqrt Lx)) := by
          gcongr
      _ = K_large * x ^ 2 * Real.exp (-c_fin * Real.sqrt Lx) := by dsimp only [K_large]; ring
  -- Step 2: Cover `2 ≤ x ≤ x₀` with a constant bump
  set C_small : ℝ := (13 / 2) * Real.exp (c_fin * Real.sqrt (Real.log x₀))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  by_cases hge : x₀ ≤ x
  · exact (hlarge x hge).trans (by gcongr; exact le_max_left _ _)
  · push Not at hge
    have hpsi1_le : psi1 x ≤ 6 * x ^ 2 := by
      have h1 : psi1 x ≤ x * RHDirect.chebyshevPsi x := by
        unfold psi1 RHDirect.chebyshevPsi
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n _ => ?_
        have hmax : max (x - (n : ℝ)) 0 ≤ x := max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
        nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
      have h2 := Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith : 1 ≤ x)
      nlinarith
    have habs_le : |psi1 x - x ^ 2 / 2| ≤ (13 / 2) * x ^ 2 := by
      rw [abs_le]
      constructor <;> linarith [psi1_nonneg x]
    have hexp_ge : Real.exp (-c_fin * Real.sqrt (Real.log x₀)) ≤ Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log x ≤ Real.log x₀ := Real.log_le_log (by linarith) hge.le
      have hsqrt : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log x₀) := Real.sqrt_le_sqrt hlog
      nlinarith
    have hcancel : C_small * Real.exp (-c_fin * Real.sqrt (Real.log x₀)) = 13 / 2 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : c_fin * Real.sqrt (Real.log x₀) + -c_fin * Real.sqrt (Real.log x₀) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc |psi1 x - x ^ 2 / 2|
        ≤ (13 / 2) * x ^ 2 := habs_le
      _ = C_small * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x₀)) := by
          rw [← hcancel]; ring
      _ ≤ C_small * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
          gcongr
      _ ≤ C_fin * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
          gcongr; exact le_max_right _ _

/-! ## Section 3: Unconditional Effective PNT for `Chebyshev.psi`, `Chebyshev.theta`, & `Nat.primeCounting` -/

/-- Purely algebraic monotone finite-difference sandwich relating `psi1` to `Chebyshev.psi`:
for all `0 ≤ x` and `0 ≤ h`,
`h * Chebyshev.psi x ≤ psi1 (x + h) - psi1 x ≤ h * Chebyshev.psi (x + h)`. -/
theorem psi1_diff_sandwich {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    h * Chebyshev.psi x ≤ psi1 (x + h) - psi1 x ∧
    psi1 (x + h) - psi1 x ≤ h * Chebyshev.psi (x + h) := by
  have hpsi_eq : ∀ y : ℝ, Chebyshev.psi y = RHDirect.chebyshevPsi y := fun y =>
    (Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi y).symm
  rw [hpsi_eq x, hpsi_eq (x + h)]
  have hfl_le : ⌊x⌋₊ + 1 ≤ ⌊x + h⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_mono (by linarith)) 1
  have hsub : Finset.range (⌊x⌋₊ + 1) ⊆ Finset.range (⌊x + h⌋₊ + 1) := Finset.range_mono hfl_le
  -- Extend the sum for `psi1 x` to `Finset.range (⌊x + h⌋₊ + 1)` since extra terms vanish
  have hpsi1_ext : psi1 x = ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), Λ n * max (x - (n : ℝ)) 0 := by
    unfold psi1
    refine Finset.sum_subset hsub fun n _ hn => ?_
    have hgt : ⌊x⌋₊ + 1 ≤ n := by simpa [Finset.mem_range] using hn
    have hnx : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hgt)
    rw [max_eq_right (by linarith), mul_zero]
  have hdiff : psi1 (x + h) - psi1 x =
      ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), Λ n * (max (x + h - (n : ℝ)) 0 - max (x - (n : ℝ)) 0) := by
    rw [hpsi1_ext]
    unfold psi1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [hdiff]
  constructor
  · -- Lower bound: drop terms with `n > ⌊x⌋₊`
    unfold RHDirect.chebyshevPsi
    rw [Finset.mul_sum]
    calc ∑ n ∈ Finset.range (⌊x⌋₊ + 1), h * Λ n
        = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * (max (x + h - (n : ℝ)) 0 - max (x - (n : ℝ)) 0) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have hn_le : (n : ℝ) ≤ x := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
            (Nat.floor_le hx)
          rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
      _ ≤ ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), Λ n * (max (x + h - (n : ℝ)) 0 - max (x - (n : ℝ)) 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
          refine mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ?_
          rw [sub_nonneg]
          exact max_le_max (by linarith) le_rfl
  · -- Upper bound: `max (x + h - n) 0 - max (x - n) 0 ≤ h` for every `n`
    unfold RHDirect.chebyshevPsi
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hstep : max (x + h - (n : ℝ)) 0 - max (x - (n : ℝ)) 0 ≤ h := by
      rcases le_or_gt (n : ℝ) x with hle | hgt
      · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
      · rw [max_eq_right (by linarith : x - (n : ℝ) ≤ 0), sub_zero]
        exact max_le (by linarith) hh
    have h1 := mul_le_mul_of_nonneg_left hstep (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    linarith

/-- **UNCONDITIONAL EFFECTIVE PRIME NUMBER THEOREM FOR `Chebyshev.psi` (0 ASSUMPTIONS!)**:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem effective_pnt_psi :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, C, hC, hpsi1⟩ := effective_pnt_psi1
  set c' : ℝ := c / 4 with hc'_def
  have hc'_pos : 0 < c' := by positivity
  set K_large : ℝ := 1 / 4 + 20 * C
  have hK_large_pos : 0 < K_large := by positivity
  -- Step 1: De-smoothing for all `x ≥ 4`
  have hge4 : ∀ x : ℝ, 4 ≤ x →
      |Chebyshev.psi x - x| ≤ K_large * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
    intro x hx4
    have hx2 : 2 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    set Lx : ℝ := Real.log x with hLx_def
    have hLx_pos : 0 < Lx := Real.log_pos (by linarith)
    set E_val : ℝ := Real.exp (-c' * Real.sqrt Lx) with hE_def
    have hE_pos : 0 < E_val := Real.exp_pos _
    have hE_le1 : E_val ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg Lx])
    set h : ℝ := (x / 2) * E_val with hh_def
    have hh_pos : 0 < h := by positivity
    have hh_le_half : h ≤ x / 2 := by nlinarith
    have hxh_ge2 : 2 ≤ x - h := by linarith
    have hxh_le : x - h ≤ x := by linarith
    have hxph_ge2 : 2 ≤ x + h := by linarith
    have hxph_le2x : x + h ≤ 2 * x := by linarith
    -- Decay comparison: `Real.exp (-c * √(log (x - h))) ≤ E_val ^ 2`
    have hexp_half : Real.exp (-c * Real.sqrt (Real.log (x - h))) ≤ E_val ^ 2 := by
      have hlog_ge : Lx / 2 ≤ Real.log (x - h) := by
        have h1 : x / 2 ≤ x - h := by linarith
        have h2 : Real.log (x / 2) ≤ Real.log (x - h) := Real.log_le_log (by linarith) h1
        rw [Real.log_div hx0.ne' two_ne_zero] at h2
        have hlog4 : 2 * Real.log 2 ≤ Lx := by
          have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx4
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at this
          simpa [Lx] using this
        linarith
      have hsqrt_ge : Real.sqrt Lx / 2 ≤ Real.sqrt (Real.log (x - h)) := by
        have hsq : (Real.sqrt Lx / 2) ^ 2 ≤ Real.log (x - h) := by
          rw [div_pow, Real.sq_sqrt hLx_pos.le]; norm_num; linarith
        exact Real.le_sqrt_of_sq_le hsq
      have hE2 : E_val ^ 2 = Real.exp (-(c / 2) * Real.sqrt Lx) := by
        rw [hE_def, ← Real.exp_nat_mul]; congr 1; dsimp only [c']; push_cast; ring
      rw [hE2]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hexp_x : Real.exp (-c * Real.sqrt Lx) ≤ E_val ^ 2 := by
      have hE2 : E_val ^ 2 = Real.exp (-(c / 2) * Real.sqrt Lx) := by
        rw [hE_def, ← Real.exp_nat_mul]; congr 1; dsimp only [c']; push_cast; ring
      rw [hE2]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.sqrt_nonneg Lx]
    have hexp_plus : Real.exp (-c * Real.sqrt (Real.log (x + h))) ≤ E_val ^ 2 := by
      have hlog_ge : Lx ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
      have h1 : Real.exp (-c * Real.sqrt (Real.log (x + h))) ≤ Real.exp (-c * Real.sqrt Lx) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.sqrt_le_sqrt hlog_ge]
      exact h1.trans hexp_x
    have hE_sub : |psi1 (x - h) - (x - h) ^ 2 / 2| ≤ C * x ^ 2 * E_val ^ 2 := by
      calc |psi1 (x - h) - (x - h) ^ 2 / 2|
          ≤ C * (x - h) ^ 2 * Real.exp (-c * Real.sqrt (Real.log (x - h))) := hpsi1 (x - h) hxh_ge2
        _ ≤ C * x ^ 2 * E_val ^ 2 := by
            have hsq : (x - h) ^ 2 ≤ x ^ 2 := by nlinarith
            gcongr
    have hE_cur : |psi1 x - x ^ 2 / 2| ≤ C * x ^ 2 * E_val ^ 2 := by
      calc |psi1 x - x ^ 2 / 2|
          ≤ C * x ^ 2 * Real.exp (-c * Real.sqrt Lx) := hpsi1 x hx2
        _ ≤ C * x ^ 2 * E_val ^ 2 := by gcongr
    have hE_add : |psi1 (x + h) - (x + h) ^ 2 / 2| ≤ 4 * C * x ^ 2 * E_val ^ 2 := by
      calc |psi1 (x + h) - (x + h) ^ 2 / 2|
          ≤ C * (x + h) ^ 2 * Real.exp (-c * Real.sqrt (Real.log (x + h))) := hpsi1 (x + h) hxph_ge2
        _ ≤ C * (2 * x) ^ 2 * E_val ^ 2 := by
            have hsq : (x + h) ^ 2 ≤ (2 * x) ^ 2 := by nlinarith
            gcongr
        _ = 4 * C * x ^ 2 * E_val ^ 2 := by ring
    -- Apply two-sided sandwich!
    have hup_sand := (psi1_diff_sandwich hx0.le hh_pos.le).1
    have hlo_sand := (psi1_diff_sandwich (by linarith : 0 ≤ x - h) hh_pos.le).2
    rw [sub_add_cancel] at hlo_sand
    rw [abs_le]
    constructor
    · -- Lower bound on `Chebyshev.psi x - x`
      have h1 : h * Chebyshev.psi x ≥ h * x - h ^ 2 / 2 +
          (psi1 x - x ^ 2 / 2) - (psi1 (x - h) - (x - h) ^ 2 / 2) := by
        linarith [show x ^ 2 / 2 - (x - h) ^ 2 / 2 = h * x - h ^ 2 / 2 by ring]
      have h2 : -(2 * C * x ^ 2 * E_val ^ 2) ≤
          (psi1 x - x ^ 2 / 2) - (psi1 (x - h) - (x - h) ^ 2 / 2) := by
        linarith [(abs_le.mp hE_cur).1, (abs_le.mp hE_sub).2]
      have h3 : h * (Chebyshev.psi x - x) ≥ -h ^ 2 / 2 - 2 * C * x ^ 2 * E_val ^ 2 := by linarith
      have h4 : -((1 / 4 + 4 * C) * x * E_val) ≤ Chebyshev.psi x - x := by
        have hrhs : h * (-((1 / 4 + 4 * C) * x * E_val)) = -h ^ 2 / 2 - 2 * C * x ^ 2 * E_val ^ 2 := by
          dsimp only [h]; ring
        have : h * (-((1 / 4 + 4 * C) * x * E_val)) ≤ h * (Chebyshev.psi x - x) := by linarith
        exact le_of_mul_le_mul_left this hh_pos
      have hC_nn : 0 ≤ C * x * E_val := by positivity
      dsimp only [K_large]
      linarith
    · -- Upper bound on `Chebyshev.psi x - x`
      have h1 : h * Chebyshev.psi x ≤ h * x + h ^ 2 / 2 +
          (psi1 (x + h) - (x + h) ^ 2 / 2) - (psi1 x - x ^ 2 / 2) := by
        linarith [show (x + h) ^ 2 / 2 - x ^ 2 / 2 = h * x + h ^ 2 / 2 by ring]
      have h2 : (psi1 (x + h) - (x + h) ^ 2 / 2) - (psi1 x - x ^ 2 / 2) ≤
          5 * C * x ^ 2 * E_val ^ 2 := by
        linarith [(abs_le.mp hE_add).2, (abs_le.mp hE_cur).1]
      have h3 : h * (Chebyshev.psi x - x) ≤ h ^ 2 / 2 + 5 * C * x ^ 2 * E_val ^ 2 := by linarith
      have h4 : Chebyshev.psi x - x ≤ (1 / 4 + 10 * C) * x * E_val := by
        have hrhs : h * ((1 / 4 + 10 * C) * x * E_val) = h ^ 2 / 2 + 5 * C * x ^ 2 * E_val ^ 2 := by
          dsimp only [h]; ring
        have : h * (Chebyshev.psi x - x) ≤ h * ((1 / 4 + 10 * C) * x * E_val) := by linarith
        exact le_of_mul_le_mul_left this hh_pos
      have hC_nn : 0 ≤ C * x * E_val := by positivity
      dsimp only [K_large]
      linarith
  -- Step 2: Cover `2 ≤ x ≤ 4`
  set C_small : ℝ := 7 * Real.exp (c' * Real.sqrt (Real.log 4))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨c', hc'_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  by_cases hx4 : 4 ≤ x
  · exact (hge4 x hx4).trans (by gcongr; exact le_max_left _ _)
  · push Not at hx4
    have hpsi_le : Chebyshev.psi x ≤ 6 * x := by
      rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
      exact Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith)
    have hpsi_nn : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
    have habs : |Chebyshev.psi x - x| ≤ 7 * x := by
      rw [abs_le]; constructor <;> linarith
    have hexp_ge : Real.exp (-c' * Real.sqrt (Real.log 4)) ≤ Real.exp (-c' * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hsqrt := Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hx4.le)
      nlinarith
    have hcancel : C_small * Real.exp (-c' * Real.sqrt (Real.log 4)) = 7 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : c' * Real.sqrt (Real.log 4) + -c' * Real.sqrt (Real.log 4) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc |Chebyshev.psi x - x|
        ≤ 7 * x := habs
      _ = C_small * x * Real.exp (-c' * Real.sqrt (Real.log 4)) := by rw [← hcancel]; ring
      _ ≤ C_small * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by gcongr
      _ ≤ C_fin * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by gcongr; exact le_max_right _ _

/-- Equivalent formulation on `RHDirect.chebyshevPsi`. -/
theorem effective_pnt_chebyshevPsi :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |RHDirect.chebyshevPsi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_pnt_psi
  refine ⟨c, hc, C, hC, fun x hx => ?_⟩
  rw [Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
  exact hbd x hx

/-- **UNCONDITIONAL EFFECTIVE PRIME NUMBER THEOREM FOR `Chebyshev.theta` (0 ASSUMPTIONS!)**:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem effective_pnt_theta :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |Chebyshev.theta x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, C, hC, hpsi⟩ := effective_pnt_psi
  set c' : ℝ := min c (1 / 4) with hc'_def
  have hc'_pos : 0 < c' := lt_min hc (by norm_num)
  have hc'_le_c : c' ≤ c := min_le_left _ _
  have hc'_le_qtr : c' ≤ 1 / 4 := min_le_right _ _
  refine ⟨c', hc'_pos, C + 8, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set Lx : ℝ := Real.log x with hLx_def
  have hLx_pos : 0 < Lx := Real.log_pos (by linarith)
  have hdiff : |Chebyshev.theta x - Chebyshev.psi x| ≤ 2 * Real.sqrt x * Lx := by
    have h1 := Chebyshev.theta_le_psi x
    have h2 := Chebyshev.psi_sub_theta_le (by linarith : 1 ≤ x)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1)]
    exact h2
  -- Show `2 * √x * Lx ≤ 8 * x * exp(-c' * √Lx)`
  have hsqrt_bd : 2 * Real.sqrt x * Lx ≤ 8 * x * Real.exp (-c' * Real.sqrt Lx) := by
    have hsqrt_eq : Real.sqrt x = x * Real.exp (-(1 / 2) * Lx) := by
      have h1 : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
      have h2 : x ^ (1 / 2 : ℝ) = x * x ^ (-(1 / 2 : ℝ)) := by
        calc x ^ (1 / 2 : ℝ) = x ^ ((1 : ℝ) + -(1 / 2 : ℝ)) := by norm_num
          _ = x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ)) := Real.rpow_add hx0 _ _
          _ = x * x ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      rw [h1, h2, Real.rpow_def_of_pos hx0, ← hLx_def]
      congr 2; ring
    rw [hsqrt_eq]
    -- Need `2 * Lx * exp(-(1/2) * Lx) ≤ 8 * exp(-c' * √Lx)`, i.e. `Lx * exp(c' * √Lx - (1/2) * Lx) ≤ 4`
    have hkey : Lx * Real.exp (-(1 / 2) * Lx) ≤ 4 * Real.exp (-c' * Real.sqrt Lx) := by
      by_cases hL1 : 1 ≤ Lx
      · have hsqrt_le : Real.sqrt Lx ≤ Lx := by
          have : Lx ≤ Lx ^ 2 := by nlinarith
          exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hLx_pos.le)
        have hexp_le : -(1 / 2) * Lx ≤ -(Lx / 4) + (-c' * Real.sqrt Lx) := by nlinarith
        have h1 : Real.exp (-(1 / 2) * Lx) ≤ Real.exp (-(Lx / 4)) * Real.exp (-c' * Real.sqrt Lx) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hexp_le
        have h2 : (Lx / 4) * Real.exp (-(Lx / 4)) ≤ 1 := mul_exp_neg_le_one (Lx / 4)
        calc Lx * Real.exp (-(1 / 2) * Lx)
            ≤ Lx * (Real.exp (-(Lx / 4)) * Real.exp (-c' * Real.sqrt Lx)) :=
              mul_le_mul_of_nonneg_left h1 hLx_pos.le
          _ = 4 * ((Lx / 4) * Real.exp (-(Lx / 4))) * Real.exp (-c' * Real.sqrt Lx) := by ring
          _ ≤ 4 * 1 * Real.exp (-c' * Real.sqrt Lx) := by gcongr
          _ = 4 * Real.exp (-c' * Real.sqrt Lx) := by ring
      · push Not at hL1
        have hsqrt_le1 : Real.sqrt Lx ≤ 1 := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL1.le
        have h1 : Real.exp (-(1 / 2) * Lx) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have h2 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-c' * Real.sqrt Lx) := by
          apply Real.exp_le_exp.mpr; nlinarith [Real.sqrt_nonneg Lx]
        have h3 : (1 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by
          have := Real.add_one_le_exp (-(1 / 4 : ℝ)); linarith
        calc Lx * Real.exp (-(1 / 2) * Lx) ≤ 1 * 1 := mul_le_mul hL1.le h1 (Real.exp_pos _).le zero_le_one
          _ = 4 * (1 / 4) := by norm_num
          _ ≤ 4 * Real.exp (-c' * Real.sqrt Lx) := by linarith
    have := mul_le_mul_of_nonneg_left hkey (show 0 ≤ 2 * x by linarith)
    linarith
  have hpsi_c' : |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c' * Real.sqrt Lx) := by
    refine (hpsi x hx).trans ?_
    gcongr
  have htri : |Chebyshev.theta x - x| ≤ |Chebyshev.theta x - Chebyshev.psi x| + |Chebyshev.psi x - x| := by
    simpa [sub_add_sub_cancel] using abs_add_le (Chebyshev.theta x - Chebyshev.psi x) (Chebyshev.psi x - x)
  linarith

/-- Helper: `Real.exp (-c * Real.sqrt (Real.log x)) → 0` as `x → ∞` for any `c > 0`. -/
private lemma tendsto_exp_neg_mul_sqrt_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x)) atTop atTop :=
    Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp Real.tendsto_log_atTop
      |>.congr fun x => (Real.sqrt_eq_rpow (Real.log x)).symm)
  have h2 : Tendsto (fun x : ℝ => -(c * Real.sqrt (Real.log x))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  exact (Real.tendsto_exp_atBot.comp h2).congr fun x => by dsimp only [Function.comp_apply]; congr 1; ring

/-- **CLASSICAL PRIME NUMBER THEOREM (`ψ(x) ~ x`, 0 ASSUMPTIONS!)**:
`Tendsto (fun x => Chebyshev.psi x / x) atTop (nhds 1)`. -/
theorem pnt_psi_asymp :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_pnt_psi
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (a := fun x : ℝ => C * Real.exp (-c * Real.sqrt (Real.log x))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    rw [Real.norm_eq_abs, show Chebyshev.psi x / x - 1 = (Chebyshev.psi x - x) / x by field_simp [hx0.ne'],
      abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    linarith [hbd x hx]
  · simpa using (tendsto_exp_neg_mul_sqrt_log hc).const_mul C

/-- **CLASSICAL PRIME NUMBER THEOREM (`ϑ(x) ~ x`, 0 ASSUMPTIONS!)**:
`Tendsto (fun x => Chebyshev.theta x / x) atTop (nhds 1)`. -/
theorem pnt_theta_asymp :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_pnt_theta
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (a := fun x : ℝ => C * Real.exp (-c * Real.sqrt (Real.log x))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    rw [Real.norm_eq_abs, show Chebyshev.theta x / x - 1 = (Chebyshev.theta x - x) / x by field_simp [hx0.ne'],
      abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    linarith [hbd x hx]
  · simpa using (tendsto_exp_neg_mul_sqrt_log hc).const_mul C

/-- **CLASSICAL PRIME NUMBER THEOREM (`π(x) ~ x / log x`, real variable, 0 ASSUMPTIONS!)**:
`Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (nhds 1)`. -/
theorem pnt_primeCounting_real_asymp :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) := by
  -- Use `Stage3RealAnalyticLandau.primeCounting_eq_abel_theta`:
  -- `π(x) / (x / log x) = θ(x) / x + (log x / x) * ∫_2^x θ(t) / (t (log t)^2) dt`
  set R : ℝ → ℝ := fun x =>
    (Real.log x / x) * ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2)
  have hR_tendsto : Tendsto R atTop (𝓝 0) := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set B : ℝ → ℝ := fun x => 6 * Real.log x / ((Real.log 2) ^ 2 * Real.sqrt x) + 24 / Real.log x
    have hB_tendsto : Tendsto B atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
        have h := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
        exact h.tendsto_div_nhds_zero.congr fun x => by rw [Real.sqrt_eq_rpow]
      have h1' : Tendsto (fun x : ℝ => 6 * Real.log x / ((Real.log 2) ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
        have := h1.const_mul (6 / (Real.log 2) ^ 2)
        rw [mul_zero] at this
        exact this.congr fun x => by ring
      have h2 : Tendsto (fun x : ℝ => 24 / Real.log x) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul 24
        rw [mul_zero] at this
        exact this.congr fun x => by dsimp only [Function.comp_apply]; ring
      simpa using h1'.add h2
    refine squeeze_zero_norm' (a := B) ?_ hB_tendsto
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx4
    have hx0 : 0 < x := by linarith
    have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hsq_ge2 : 2 ≤ Real.sqrt x :=
      Real.le_sqrt_of_sq_le (by linarith : (2 : ℝ) ^ 2 ≤ x)
    have hsq_le : Real.sqrt x ≤ x := by
      have : x ≤ x ^ 2 := by nlinarith
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hx0.le)
    have hint_th : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
        IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * (Real.log t) ^ 2)) volume a b := by
      intro a b ha hab
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr ?_
      refine Integrable.mono'
        (integrableOn_const (C := 6 / (Real.log 2) ^ 2) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
      · have hm : Measurable Chebyshev.theta := by
          have h : Chebyshev.theta =
              (fun k : ℕ => ∑ p ∈ (Finset.Ioc 0 k).filter Nat.Prime, Real.log (p : ℝ)) ∘ Nat.floor := rfl
          rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
        exact (hm.div (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
        have ht2 : 2 ≤ t := ha.trans ht.1.le
        have ht0 : 0 < t := by linarith
        have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
        have hth_nn : 0 ≤ Chebyshev.theta t := Chebyshev.theta_nonneg t
        have hth_le : Chebyshev.theta t ≤ 6 * t := by
          have h1 := Chebyshev.theta_le_psi t
          rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi] at h1
          exact h1.trans (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith))
        rw [Real.norm_of_nonneg (div_nonneg hth_nn (by positivity))]
        calc Chebyshev.theta t / (t * (Real.log t) ^ 2)
            ≤ (6 * t) / (t * (Real.log 2) ^ 2) := by
              refine div_le_div₀ (by positivity) hth_le (by positivity) ?_
              gcongr
          _ = 6 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']
    have hint_nn : 0 ≤ ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2) :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        div_nonneg (Chebyshev.theta_nonneg t) (mul_nonneg (by linarith [ht.1]) (sq_nonneg _))
    have hR_nn : 0 ≤ R x := mul_nonneg (div_nonneg hLx_pos.le hx0.le) hint_nn
    rw [Real.norm_of_nonneg hR_nn]
    have hsplit : ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2) =
        (∫ t in (2 : ℝ)..(Real.sqrt x), Chebyshev.theta t / (t * (Real.log t) ^ 2)) +
        (∫ t in (Real.sqrt x)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2)) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hint_th 2 (Real.sqrt x) le_rfl hsq_ge2)
        (hint_th (Real.sqrt x) x hsq_ge2 hsq_le)).symm
    have hpart1 : ∫ t in (2 : ℝ)..(Real.sqrt x), Chebyshev.theta t / (t * (Real.log t) ^ 2) ≤
        6 * Real.sqrt x / (Real.log 2) ^ 2 := by
      have h1 : ∫ t in (2 : ℝ)..(Real.sqrt x), Chebyshev.theta t / (t * (Real.log t) ^ 2) ≤
          ∫ _t in (2 : ℝ)..(Real.sqrt x), (6 / (Real.log 2) ^ 2) := by
        refine intervalIntegral.integral_mono_on hsq_ge2 (hint_th 2 (Real.sqrt x) le_rfl hsq_ge2)
          intervalIntegrable_const fun t ht => ?_
        have ht0 : 0 < t := by linarith [ht.1]
        have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
        have hth_le : Chebyshev.theta t ≤ 6 * t := by
          have h := Chebyshev.theta_le_psi t
          rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi] at h
          exact h.trans (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith [ht.1]))
        calc Chebyshev.theta t / (t * (Real.log t) ^ 2)
            ≤ (6 * t) / (t * (Real.log 2) ^ 2) := by
              refine div_le_div₀ (by positivity) hth_le (by positivity) ?_; gcongr
          _ = 6 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      have hlen : Real.sqrt x - 2 ≤ Real.sqrt x := by linarith
      calc ∫ t in (2 : ℝ)..(Real.sqrt x), Chebyshev.theta t / (t * (Real.log t) ^ 2)
          ≤ (Real.sqrt x - 2) * (6 / (Real.log 2) ^ 2) := h1
        _ ≤ Real.sqrt x * (6 / (Real.log 2) ^ 2) :=
            mul_le_mul_of_nonneg_right hlen (by positivity)
        _ = 6 * Real.sqrt x / (Real.log 2) ^ 2 := by ring
    have hpart2 : ∫ t in (Real.sqrt x)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2) ≤
        24 * x / (Real.log x) ^ 2 := by
      have h1 : ∫ t in (Real.sqrt x)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2) ≤
          ∫ _t in (Real.sqrt x)..x, (24 / (Real.log x) ^ 2) := by
        refine intervalIntegral.integral_mono_on hsq_le (hint_th (Real.sqrt x) x hsq_ge2 hsq_le)
          intervalIntegrable_const fun t ht => ?_
        have ht0 : 0 < t := by linarith [ht.1]
        have hlt_ge : Real.log x / 2 ≤ Real.log t := by
          have h := Real.log_le_log (by linarith) ht.1
          rwa [Real.log_sqrt hx0.le] at h
        have hth_le : Chebyshev.theta t ≤ 6 * t := by
          have h := Chebyshev.theta_le_psi t
          rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi] at h
          exact h.trans (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith [ht.1]))
        calc Chebyshev.theta t / (t * (Real.log t) ^ 2)
            ≤ (6 * t) / (t * (Real.log x / 2) ^ 2) := by
              refine div_le_div₀ (by positivity) hth_le (by positivity) ?_; gcongr
          _ = 24 / (Real.log x) ^ 2 := by field_simp [ht0.ne', hLx_pos.ne']; ring
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      have hlen : x - Real.sqrt x ≤ x := by linarith [Real.sqrt_nonneg x]
      calc ∫ t in (Real.sqrt x)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2)
          ≤ (x - Real.sqrt x) * (24 / (Real.log x) ^ 2) := h1
        _ ≤ x * (24 / (Real.log x) ^ 2) := mul_le_mul_of_nonneg_right hlen (by positivity)
        _ = 24 * x / (Real.log x) ^ 2 := by ring
    dsimp only [R, B]
    rw [hsplit]
    have hcomb : (Real.log x / x) * (6 * Real.sqrt x / (Real.log 2) ^ 2 + 24 * x / (Real.log x) ^ 2) =
        6 * Real.log x / ((Real.log 2) ^ 2 * Real.sqrt x) + 24 / Real.log x := by
      have hsq_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have h1 : (Real.log x / x) * (6 * Real.sqrt x / (Real.log 2) ^ 2) =
          6 * Real.log x / ((Real.log 2) ^ 2 * Real.sqrt x) := by
        have hdiv : Real.sqrt x / x = (Real.sqrt x)⁻¹ := by
          rw [div_eq_iff hx0.ne', eq_comm, inv_mul_eq_iff_eq_mul₀ hsq_pos.ne', Real.mul_self_sqrt hx0.le]
        calc (Real.log x / x) * (6 * Real.sqrt x / (Real.log 2) ^ 2)
            = 6 * Real.log x / (Real.log 2) ^ 2 * (Real.sqrt x / x) := by ring
          _ = 6 * Real.log x / (Real.log 2) ^ 2 * (Real.sqrt x)⁻¹ := by rw [hdiv]
          _ = 6 * Real.log x / ((Real.log 2) ^ 2 * Real.sqrt x) := by
              field_simp [hsq_pos.ne', hlog2_pos.ne']
      have h2 : (Real.log x / x) * (24 * x / (Real.log x) ^ 2) = 24 / Real.log x := by
        field_simp [hx0.ne', hLx_pos.ne']
      rw [mul_add, h1, h2]
    calc (Real.log x / x) *
            ((∫ t in (2 : ℝ)..(Real.sqrt x), Chebyshev.theta t / (t * (Real.log t) ^ 2)) +
             (∫ t in (Real.sqrt x)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2)))
        ≤ (Real.log x / x) * (6 * Real.sqrt x / (Real.log 2) ^ 2 + 24 * x / (Real.log x) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hpart1 hpart2) (by positivity)
      _ = 6 * Real.log x / ((Real.log 2) ^ 2 * Real.sqrt x) + 24 / Real.log x := hcomb
  -- Conclude `π(x) / (x / log x) = θ(x) / x + R(x) → 1 + 0 = 1`!
  have hsum : Tendsto (fun x : ℝ => Chebyshev.theta x / x + R x) atTop (𝓝 1) := by
    simpa using pnt_theta_asymp.add hR_tendsto
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx2
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Stage3RealAnalyticLandau.primeCounting_eq_abel_theta hx2]
  dsimp only [R]
  field_simp [hx0.ne', hLx_pos.ne']

/-- **THE CLASSICAL PRIME NUMBER THEOREM FOR `Nat.primeCounting` (0 ASSUMPTIONS!)**:
`Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds 1)`. -/
theorem pnt_primeCounting_asymp :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 1) := by
  have h := pnt_primeCounting_real_asymp.comp tendsto_natCast_atTop_atTop
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Nat.floor_natCast]

end RHDirect.Stage6EffectivePNT
