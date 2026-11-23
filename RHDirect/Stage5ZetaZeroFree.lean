import RHDirect.Interfaces
import RHDirect.ElementaryEquiv
import RHDirect.Stage3ZeroFreeRegion
import RHDirect.Stage3RealAnalyticLandau
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# RHDirect.Stage5ZetaZeroFree

Concrete, 0-assumption analytic estimates and unconditional classical zero-free regions directly
on Mathlib's actual `riemannZeta` and `DirichletCharacter.LFunction`, in pure Mathlib `v4.33.1`.

## Main Contents
1. **Borel–Carathéodory Lemma & Sharp Derivative Bounds**:
   - Arbitrary-center Borel–Carathéodory bounds (`borelCaratheodory_sub_center`,
     `borelCaratheodory_general`),
   - Center derivative bound `‖deriv f z₀‖ ≤ (2 / R) * (M - (f z₀).re)`,
   - Exact sharp Cauchy-integral derivative bound
     `‖deriv f z‖ ≤ (2 * R / (R - r)^2) * (M - (f z₀).re)` on `‖z - z₀‖ ≤ r < R`.
2. **Finite Blaschke Factorization & Landau's Local Log-Derivative Carathéodory Bound**:
   - Elementary `dslope` + Maximum-Modulus finite Blaschke factorization on `closedBall s₀ R`,
   - Radial-primitive holomorphic logarithm on open balls,
   - Landau's local log-derivative upper bound `-Re(g'/g(s₀)) ≤ (2 / r) * log M - ∑ Re(B_ρ'/B_ρ(s₀))`
     with zero-free, single-zero, and finite-subset-of-zeros corollaries.
3. **Exact First-Order & Truncated Euler–Maclaurin Continuation and Concrete Bounds on `riemannZeta`
   and `DirichletCharacter.LFunction`**:
   - `riemannZeta s - 1 / (s - 1) = 1 - s ∫_1^∞ (t - ⌊t⌋) t^{-s-1} dt` on `Re(s) > 0`, `s ≠ 1`,
   - Truncated Euler–Maclaurin formula `∑_{n=1}^N n^{-s} + N^{1-s}/(s-1) - s ∫_N^∞ {t} t^{-s-1} dt`,
   - Concrete vertical-strip polynomial & sharp near-1 logarithmic growth bounds,
   - Concrete `σ > 1` bounds on `‖ζ(σ+it)‖`, `‖1/ζ(σ+it)‖`, `‖-ζ'/ζ(σ+it)‖ ≤ 1/(σ-1) + 1`,
   - Concrete `Re(s) > 0` polynomial bounds and `σ > 1` reciprocal/log-derivative bounds for
     non-principal `DirichletCharacter.LFunction χ`.
4. **Unconditional Classical de la Vallée Poussin Zero-Free Region (0 Assumptions!)**:
   - Directly on Mathlib's `riemannZeta`:
     `∃ c > 0, ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0`
     (with explicit constant `c = 1 / 14000` on `|s.im| ≥ 4`),
   - Directly on Mathlib's `DirichletCharacter.LFunction χ` for every complex character `χ ^ 2 ≠ 1`
     with an explicit uniform constant across all moduli `q` and all `s : ℂ`!

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage5ZetaZeroFree

/-! ## Section 1: Borel–Carathéodory Lemma & Sharp Derivative Bounds -/

/-- Shifted Borel–Carathéodory bound centered at an arbitrary `z₀ : ℂ`:
if `f` is holomorphic on `ball z₀ R` (`0 < R`) with `(f w).re ≤ M` on `ball z₀ R`, then for every
`z ∈ ball z₀ R` with `‖z - z₀‖ ≤ r < R`,
`‖f z - f z₀‖ ≤ (2 * r / (R - r)) * (M - (f z₀).re)`. -/
theorem borelCaratheodory_sub_center {f : ℂ → ℂ} {z₀ z : ℂ} {M R r : ℝ}
    (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M)
    (hz : ‖z - z₀‖ ≤ r) :
    ‖f z - f z₀‖ ≤ (2 * r / (R - r)) * (M - (f z₀).re) := by
  have hz_ball : z - z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hrR
  have hz₀_mem : z₀ ∈ Metric.ball z₀ R := Metric.mem_ball_self hR
  have hA_nonneg : 0 ≤ M - (f z₀).re := sub_nonneg.mpr (hre z₀ hz₀_mem)
  set g : ℂ → ℂ := fun w => f (z₀ + w) - f z₀
  have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) := by
    refine (hf.comp (differentiableOn_const z₀ |>.fun_add differentiableOn_id) ?_).sub
      (differentiableOn_const (f z₀))
    intro w hw
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hg0 : g 0 = 0 := by simp [g]
  -- Apply Mathlib's `Complex.borelCaratheodory_zero` with `M' = (M - (f z₀).re) + ε > 0`
  have hε : ∀ ε : ℝ, 0 < ε →
      ‖f z - f z₀‖ ≤ (2 * r / (R - r)) * (M - (f z₀).re + ε) := by
    intro ε hε0
    have hM' : 0 < M - (f z₀).re + ε := by linarith
    have hmaps : Set.MapsTo g (Metric.ball (0 : ℂ) R) {w : ℂ | w.re ≤ M - (f z₀).re + ε} := by
      intro w hw
      have hw' : z₀ + w ∈ Metric.ball z₀ R := by
        rw [Metric.mem_ball, dist_zero_right] at hw
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact hw
      show (f (z₀ + w) - f z₀).re ≤ M - (f z₀).re + ε
      rw [Complex.sub_re]
      linarith [hre (z₀ + w) hw']
    have hbc := Complex.borelCaratheodory_zero hM' hg_diff hmaps hR hz_ball hg0
    have hgz : g (z - z₀) = f z - f z₀ := by simp [g]
    rw [hgz] at hbc
    have hmono : 2 * (M - (f z₀).re + ε) * ‖z - z₀‖ / (R - ‖z - z₀‖) ≤
        (2 * r / (R - r)) * (M - (f z₀).re + ε) := by
      have hden1 : 0 < R - ‖z - z₀‖ := by linarith
      have hden2 : 0 < R - r := by linarith
      have h1 : ‖z - z₀‖ / (R - ‖z - z₀‖) ≤ r / (R - r) := by
        rw [div_le_div_iff₀ hden1 hden2]
        nlinarith [norm_nonneg (z - z₀)]
      have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 2 * (M - (f z₀).re + ε))
      linarith [show 2 * (M - (f z₀).re + ε) * (‖z - z₀‖ / (R - ‖z - z₀‖)) =
          2 * (M - (f z₀).re + ε) * ‖z - z₀‖ / (R - ‖z - z₀‖) by ring,
        show 2 * (M - (f z₀).re + ε) * (r / (R - r)) =
          (2 * r / (R - r)) * (M - (f z₀).re + ε) by ring]
    exact hbc.trans hmono
  -- Let ε → 0⁺
  by_contra hlt
  push Not at hlt
  set gap : ℝ := ‖f z - f z₀‖ - (2 * r / (R - r)) * (M - (f z₀).re)
  have hgap : 0 < gap := sub_pos.mpr hlt
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg (z - z₀)) hz
  have hcoeff_nonneg : 0 ≤ 2 * r / (R - r) := div_nonneg (by linarith) (by linarith)
  set ε : ℝ := gap / (2 * (2 * r / (R - r) + 1))
  have hε0 : 0 < ε := by positivity
  have hbd := hε ε hε0
  have hmul : (2 * r / (R - r)) * ε ≤ gap / 2 := by
    dsimp only [ε]
    have hden : 0 < 2 * (2 * r / (R - r) + 1) := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hden two_pos]
    nlinarith
  linarith [show (2 * r / (R - r)) * (M - (f z₀).re + ε) =
      (2 * r / (R - r)) * (M - (f z₀).re) + (2 * r / (R - r)) * ε by ring]

/-- **General Borel–Carathéodory Lemma** at arbitrary center `z₀ : ℂ`:
if `f` is holomorphic on `ball z₀ R` (`0 < R`) with `(f w).re ≤ M` on `ball z₀ R`, then for every
`z` with `‖z - z₀‖ ≤ r < R`:
`‖f z‖ ≤ (2 * r / (R - r)) * M + ((R + r) / (R - r)) * ‖f z₀‖`. -/
theorem borelCaratheodory_general {f : ℂ → ℂ} {z₀ z : ℂ} {M R r : ℝ}
    (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M)
    (hz : ‖z - z₀‖ ≤ r) :
    ‖f z‖ ≤ (2 * r / (R - r)) * M + ((R + r) / (R - r)) * ‖f z₀‖ := by
  have hsub := borelCaratheodory_sub_center hR hrR hf hre hz
  have htri : ‖f z‖ ≤ ‖f z - f z₀‖ + ‖f z₀‖ := by
    simpa [sub_add_cancel] using norm_add_le (f z - f z₀) (f z₀)
  have hneg_re : -(f z₀).re ≤ ‖f z₀‖ := by
    have := Complex.abs_re_le_norm (f z₀)
    exact (neg_le_abs _).trans this
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg (z - z₀)) hz
  have hden : 0 < R - r := by linarith
  have hcoeff : 0 ≤ 2 * r / (R - r) := div_nonneg (by linarith) hden.le
  have h1 : (2 * r / (R - r)) * (M - (f z₀).re) + ‖f z₀‖ ≤
      (2 * r / (R - r)) * M + ((R + r) / (R - r)) * ‖f z₀‖ := by
    have hid : (2 * r / (R - r)) * ‖f z₀‖ + ‖f z₀‖ = ((R + r) / (R - r)) * ‖f z₀‖ := by
      field_simp [hden.ne']; ring
    have hmul : (2 * r / (R - r)) * (-(f z₀).re) ≤ (2 * r / (R - r)) * ‖f z₀‖ :=
      mul_le_mul_of_nonneg_left hneg_re hcoeff
    linarith [show (2 * r / (R - r)) * (M - (f z₀).re) =
        (2 * r / (R - r)) * M + (2 * r / (R - r)) * (-(f z₀).re) by ring]
  linarith

/-- **Borel–Carathéodory Derivative Bound at the Center**:
if `f` is holomorphic on `ball z₀ R` (`0 < R`) with `(f w).re ≤ M` on `ball z₀ R`, then
`‖deriv f z₀‖ ≤ (2 / R) * (M - (f z₀).re)`. -/
theorem borelCaratheodory_deriv_at_center {f : ℂ → ℂ} {z₀ : ℂ} {M R : ℝ}
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) :
    ‖deriv f z₀‖ ≤ (2 / R) * (M - (f z₀).re) := by
  have hd : HasDerivAt f (deriv f z₀) z₀ :=
    (hf.differentiableAt (Metric.ball_mem_nhds z₀ hR)).hasDerivAt
  have hlim : Tendsto (fun t : ℝ => ‖(f (z₀ + (t : ℂ)) - f z₀) / (t : ℂ)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖deriv f z₀‖) := by
    have h1 : Tendsto (fun w : ℂ => (f (z₀ + w) - f z₀) / w) (𝓝[≠] (0 : ℂ)) (𝓝 (deriv f z₀)) := by
      have hs := hd.tendsto_slope_zero
      refine hs.congr' (Eventually.of_forall fun w => ?_)
      simp [div_eq_inv_mul]
    have h2 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    exact (h1.comp h2).norm
  have hlim_rhs : Tendsto (fun t : ℝ => (2 / (R - t)) * (M - (f z₀).re))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 / R) * (M - (f z₀).re))) := by
    have hcont : ContinuousAt (fun t : ℝ => (2 / (R - t)) * (M - (f z₀).re)) 0 := by
      have hsub : ContinuousAt (fun t : ℝ => R - t) 0 := continuousAt_const.sub continuousAt_id
      have hne : R - (0 : ℝ) ≠ 0 := by simpa using hR.ne'
      exact ((continuousAt_const.div hsub hne).mul continuousAt_const)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hlim hlim_rhs ?_
  filter_upwards [Ioo_mem_nhdsGT hR] with t ht
  have ht0 : 0 < t := ht.1
  have htR : t < R := ht.2
  have hbc := borelCaratheodory_sub_center hR htR hf hre
    (z := z₀ + (t : ℂ)) (r := t) (by simp [Real.norm_of_nonneg ht0.le])
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht0.le, div_le_iff₀ ht0]
  have hmul : (2 / (R - t)) * (M - (f z₀).re) * t = (2 * t / (R - t)) * (M - (f z₀).re) := by
    ring
  linarith

/-- Helper: Cauchy integral formula for `deriv f w` at any interior point `w ∈ ball c R`
via `dslope`. -/
private lemma circleIntegral_sub_sq_inv_mul_eq_deriv {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hw : w ∈ Metric.ball c R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) :
    ∮ z in C(c, R), (z - w)⁻¹ ^ 2 * f z = (2 * Real.pi * I) * deriv f w := by
  have hmem_nhds : Metric.closedBall c R ∈ 𝓝 w :=
    Filter.mem_of_superset (Metric.ball_mem_nhds w (sub_pos.mpr (Metric.mem_ball.mp hw)))
      (fun x hx => by
        rw [Metric.mem_closedBall]
        exact le_of_lt (lt_of_le_of_lt (dist_triangle x w c) (by
          rw [Metric.mem_ball] at hx
          linarith)))
  have hds_diff : DifferentiableOn ℂ (dslope f w) (Metric.closedBall c R) :=
    (Complex.differentiableOn_dslope hmem_nhds).mpr hf
  have hds_dc : DiffContOnCl ℂ (dslope f w) (Metric.ball c R) := by
    refine ⟨hds_diff.mono Metric.ball_subset_closedBall, ?_⟩
    rw [closure_ball c hR.ne']
    exact hds_diff.continuousOn
  have hcauchy := hds_dc.circleIntegral_sub_inv_smul hw
  rw [dslope_same] at hcauchy
  -- Also `∮ (z - w)⁻¹ ^ 2 * f w = 0` by FTC on the closed circle `θ ↦ -(circleMap c R θ - w)⁻¹ * f w`
  have hzero : ∮ z in C(c, R), (z - w)⁻¹ ^ 2 * f w = 0 := by
    unfold circleIntegral
    have hcm_ne : ∀ θ : ℝ, circleMap c R θ - w ≠ 0 := by
      intro θ h0
      have heq : circleMap c R θ = w := sub_eq_zero.mp h0
      have hdist : dist w c = R := by
        rw [← heq]
        exact Metric.mem_sphere.mp (circleMap_mem_sphere c hR.le θ)
      exact (Metric.mem_ball.mp hw).ne hdist
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt (fun t : ℝ => -(circleMap c R t - w)⁻¹ * f w)
          (deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ ^ 2 * f w)) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t : ℝ => circleMap c R t - w) (deriv (circleMap c R) θ) θ := by
        rw [deriv_circleMap]
        exact (hasDerivAt_circleMap c R θ).sub_const w
      have h2 := (h1.inv (hcm_ne θ)).neg.mul_const (f w)
      refine h2.congr_deriv ?_
      rw [smul_eq_mul]
      field_simp [hcm_ne θ]
    have hcont : ContinuousOn (fun θ : ℝ =>
        deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ ^ 2 * f w))
        (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
      have hEq : (fun θ : ℝ => deriv (circleMap c R) θ) = fun θ => circleMap 0 R θ * I := by
        funext θ; exact deriv_circleMap c R θ
      have h1 : ContinuousOn (fun θ : ℝ => deriv (circleMap c R) θ) (Set.uIcc 0 (2 * Real.pi)) := by
        rw [hEq]; exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn
      have h2 : ContinuousOn (fun θ : ℝ => (circleMap c R θ - w)⁻¹ ^ 2 * f w)
          (Set.uIcc 0 (2 * Real.pi)) :=
        ((ContinuousOn.inv₀ ((continuous_circleMap c R).continuousOn.sub continuousOn_const)
          (fun θ _ => hcm_ne θ)).pow 2).mul continuousOn_const
      exact h1.smul h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    have h2pi : circleMap c R (2 * Real.pi) = circleMap c R 0 := by
      simp [circleMap, Complex.exp_two_pi_mul_I]
    rw [h2pi, sub_self]
  have hcongr : EqOn (fun z : ℂ => (z - w)⁻¹ • dslope f w z)
      (fun z : ℂ => (z - w)⁻¹ ^ 2 * f z - (z - w)⁻¹ ^ 2 * f w) (Metric.sphere c R) := by
    intro z hz
    rw [Metric.mem_sphere] at hz
    have hzw : z ≠ w := by
      intro h; subst h; exact (Metric.mem_ball.mp hw).ne hz
    dsimp only
    rw [dslope_of_ne f hzw, slope_def_field, smul_eq_mul]
    field_simp [sub_ne_zero.mpr hzw]
  have hint1 : CircleIntegrable (fun z : ℂ => (z - w)⁻¹ ^ 2 * f z) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine ((ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => ?_).pow 2).mul
      (hf.continuousOn.mono Metric.sphere_subset_closedBall)
    rw [Metric.mem_sphere] at hz
    intro h; have heq : z = w := sub_eq_zero.mp h; subst heq; exact (Metric.mem_ball.mp hw).ne hz
  have hint2 : CircleIntegrable (fun z : ℂ => (z - w)⁻¹ ^ 2 * f w) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine ((ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => ?_).pow 2).mul
      continuousOn_const
    rw [Metric.mem_sphere] at hz
    intro h; have heq : z = w := sub_eq_zero.mp h; subst heq; exact (Metric.mem_ball.mp hw).ne hz
  have hsub := circleIntegral.integral_sub hint1 hint2
  rw [hzero, sub_zero] at hsub
  rw [← hsub, ← circleIntegral.integral_congr hR.le hcongr]
  simpa [smul_eq_mul] using hcauchy

/-- **Exact Sharp Borel–Carathéodory Derivative Bound**:
if `f` is holomorphic on `closedBall z₀ R` (`0 < R`) with `(f ζ).re ≤ M` on `closedBall z₀ R`,
then for every `r` with `0 ≤ r < R` and every `z` with `‖z - z₀‖ ≤ r`:
`‖deriv f z‖ ≤ (2 * R / (R - r) ^ 2) * (M - (f z₀).re)`. -/
theorem borelCaratheodory_deriv_le {f : ℂ → ℂ} {z₀ z : ℂ} {M R r : ℝ}
    (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ R))
    (hre : ∀ ζ ∈ Metric.closedBall z₀ R, (f ζ).re ≤ M)
    (hz : ‖z - z₀‖ ≤ r) :
    ‖deriv f z‖ ≤ (2 * R / (R - r) ^ 2) * (M - (f z₀).re) := by
  have hz_ball : z ∈ Metric.ball z₀ R := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hz hrR
  set w : ℂ := z - z₀ with hw_def
  have hw_norm : ‖w‖ ≤ r := hz
  have hw_lt : ‖w‖ < R := lt_of_le_of_lt hz hrR
  -- Step 1: Rewrite Cauchy derivative formula as a `θ ∈ [0, 2π]` integral
  have hcauchy := circleIntegral_sub_sq_inv_mul_eq_deriv hR hz_ball hf
  -- Step 2: Vanishing of the conjugate kernel integral by Cauchy's theorem on `closedBall z₀ R`:
  -- `∮ f(ζ) * R² * (R² - conj w * (ζ - z₀))⁻² dζ = 0`, since `‖conj w * (ζ - z₀)‖ ≤ r * R < R²`.
  have hden_ne : ∀ ζ ∈ Metric.closedBall z₀ R,
      (R : ℂ) ^ 2 - starRingEnd ℂ w * (ζ - z₀) ≠ 0 := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    intro h0
    have heq : (R : ℂ) ^ 2 = starRingEnd ℂ w * (ζ - z₀) := sub_eq_zero.mp h0
    have hn := congrArg norm heq
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul, Complex.norm_conj] at hn
    have hlt : ‖w‖ * ‖ζ - z₀‖ < R ^ 2 := by nlinarith [norm_nonneg w, norm_nonneg (ζ - z₀)]
    linarith
  have hconj_zero :
      ∮ ζ in C(z₀, R), f ζ * (R : ℂ) ^ 2 * ((R : ℂ) ^ 2 - starRingEnd ℂ w * (ζ - z₀))⁻¹ ^ 2 = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      Set.countable_empty ?_ ?_
    · refine (hf.continuousOn.mul continuousOn_const).mul ?_
      refine (ContinuousOn.inv₀ (continuousOn_const.sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
        (fun ζ hζ => hden_ne ζ hζ)).pow 2
    · intro ζ hζ
      have hζ_ball : ζ ∈ Metric.ball z₀ R := hζ.1
      have hζ_cb : ζ ∈ Metric.closedBall z₀ R := Metric.ball_subset_closedBall hζ_ball
      have hf_at : DifferentiableAt ℂ f ζ :=
        (hf.mono Metric.ball_subset_closedBall).differentiableAt (Metric.isOpen_ball.mem_nhds hζ_ball)
      have hden_at : DifferentiableAt ℂ
          (fun u : ℂ => (R : ℂ) ^ 2 - starRingEnd ℂ w * (u - z₀)) ζ :=
        (differentiableAt_const _).sub
          ((differentiableAt_const _).mul ((differentiableAt_id).sub (differentiableAt_const _)))
      exact (hf_at.mul (differentiableAt_const _)).mul ((hden_at.inv (hden_ne ζ hζ_cb)).pow 2)
  -- Step 3: Vanishing of constant-kernel integral `∮ (ζ - z)⁻¹ ^ 2 * (2 * M : ℂ) = 0`
  have hM_zero : ∮ ζ in C(z₀, R), (ζ - z)⁻¹ ^ 2 * ((2 * M : ℝ) : ℂ) = 0 := by
    have hconst := circleIntegral_sub_sq_inv_mul_eq_deriv (f := fun _ => ((2 * M : ℝ) : ℂ))
      hR hz_ball (differentiableOn_const _)
    simpa [deriv_const] using hconst
  -- Step 4: Mean value property at center `z₀`
  have hmean := Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
    hR Set.countable_empty hf.continuousOn
    (fun ζ hζ => (hf.mono Metric.ball_subset_closedBall).differentiableAt
      (Metric.isOpen_ball.mem_nhds hζ.1))
  -- Now unfold all four `circleIntegral`s into `∫ θ in 0..(2π)`!
  unfold circleIntegral at hcauchy hconj_zero hM_zero hmean
  -- Helper identity on the circle `ζ = circleMap z₀ R θ = z₀ + R * exp(θ * I)`:
  have hkern_conj : ∀ θ : ℝ,
      starRingEnd ℂ (deriv (circleMap z₀ R) θ *
        (f (circleMap z₀ R θ) * (R : ℂ) ^ 2 *
          ((R : ℂ) ^ 2 - starRingEnd ℂ w * (circleMap z₀ R θ - z₀))⁻¹ ^ 2)) =
      -(deriv (circleMap z₀ R) θ *
        ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ)))) := by
    intro θ
    set e : ℂ := cexp ((θ : ℂ) * I) with he_def
    have he_ne : e ≠ 0 := Complex.exp_ne_zero _
    have he_conj : starRingEnd ℂ e = e⁻¹ := by
      rw [he_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
        Complex.exp_neg]
    have hcm : circleMap z₀ R θ - z₀ = (R : ℂ) * e := by simp [circleMap, he_def]
    have hcm_z : circleMap z₀ R θ - z = (R : ℂ) * e - w := by
      rw [hw_def]; simp [circleMap, he_def]; ring
    have hdcm : deriv (circleMap z₀ R) θ = (R : ℂ) * e * I := by
      rw [deriv_circleMap, circleMap, zero_add, he_def]
    have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    have hsub_ne : (R : ℂ) * e - w ≠ 0 := by
      intro h0
      have h1 : (R : ℂ) * e = w := sub_eq_zero.mp h0
      have hn := congrArg norm h1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le, he_def,
        Complex.norm_exp_ofReal_mul_I, mul_one] at hn
      linarith
    rw [hcm, hcm_z, hdcm, map_mul, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow,
      map_inv₀, map_sub, map_pow, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I,
      he_conj, Complex.conj_conj]
    have hfac : (R : ℂ) ^ 2 - w * ((R : ℂ) * e⁻¹) = (R : ℂ) * e⁻¹ * ((R : ℂ) * e - w) := by
      field_simp [he_ne]
    rw [hfac]
    field_simp [hRne, he_ne, hsub_ne]
  -- Take conjugate of `hconj_zero`
  have hconj_int :
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap z₀ R) θ *
          ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ))) = 0 := by
    have hint_conj : IntervalIntegrable (fun θ : ℝ =>
        deriv (circleMap z₀ R) θ *
          (f (circleMap z₀ R θ) * (R : ℂ) ^ 2 *
            ((R : ℂ) ^ 2 - starRingEnd ℂ w * (circleMap z₀ R θ - z₀))⁻¹ ^ 2))
        volume 0 (2 * Real.pi) := by
      have h1 : ContinuousOn (fun θ : ℝ => deriv (circleMap z₀ R) θ) (Set.uIcc 0 (2 * Real.pi)) := by
        have hEq : (fun θ : ℝ => deriv (circleMap z₀ R) θ) = fun θ => circleMap 0 R θ * I := by
          funext θ; exact deriv_circleMap z₀ R θ
        rw [hEq]; exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn
      have h2 : ContinuousOn (fun θ : ℝ => f (circleMap z₀ R θ) * (R : ℂ) ^ 2)
          (Set.uIcc 0 (2 * Real.pi)) :=
        (hf.continuousOn.comp (continuous_circleMap z₀ R).continuousOn
          (fun θ _ => Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hR.le θ))).mul
          continuousOn_const
      have h3 : ContinuousOn (fun θ : ℝ =>
          ((R : ℂ) ^ 2 - starRingEnd ℂ w * (circleMap z₀ R θ - z₀))⁻¹ ^ 2)
          (Set.uIcc 0 (2 * Real.pi)) := by
        refine (ContinuousOn.inv₀ (continuousOn_const.sub (continuousOn_const.mul
          ((continuous_circleMap z₀ R).continuousOn.sub continuousOn_const))) fun θ _ => ?_).pow 2
        exact hden_ne _ (Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hR.le θ))
      exact (h1.mul (h2.mul h3)).intervalIntegrable
    have h1 : starRingEnd ℂ (∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap z₀ R) θ *
          (f (circleMap z₀ R θ) * (R : ℂ) ^ 2 *
            ((R : ℂ) ^ 2 - starRingEnd ℂ w * (circleMap z₀ R θ - z₀))⁻¹ ^ 2)) = 0 := by
      simpa [smul_eq_mul] using congrArg (starRingEnd ℂ) hconj_zero
    rw [← Complex.conjCLE_apply, ← ContinuousLinearEquiv.coe_coe,
      ← Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint_conj] at h1
    have h2 : ∫ θ in (0 : ℝ)..(2 * Real.pi),
        -(deriv (circleMap z₀ R) θ *
          ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ)))) = 0 := by
      refine Eq.trans ?_ h1
      refine intervalIntegral.integral_congr fun θ _ => (hkern_conj θ).symm
    rw [intervalIntegral.integral_neg] at h2
    exact neg_eq_zero.mp h2
  -- Combine `hcauchy + hconj_int - hM_zero`!
  have hcont_f : ContinuousOn (fun θ : ℝ => f (circleMap z₀ R θ)) (Set.uIcc 0 (2 * Real.pi)) :=
    hf.continuousOn.comp (continuous_circleMap z₀ R).continuousOn
      (fun θ _ => Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hR.le θ))
  have hcont_kern : ContinuousOn (fun θ : ℝ =>
      deriv (circleMap z₀ R) θ * (circleMap z₀ R θ - z)⁻¹ ^ 2) (Set.uIcc 0 (2 * Real.pi)) := by
    refine ContinuousOn.mul ?_ ?_
    · show ContinuousOn (fun θ : ℝ => deriv (circleMap z₀ R) θ) (Set.uIcc 0 (2 * Real.pi))
      have hEq : (fun θ : ℝ => deriv (circleMap z₀ R) θ) = fun θ => circleMap 0 R θ * I := by
        funext θ; exact deriv_circleMap z₀ R θ
      rw [hEq]
      exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn
    · refine (ContinuousOn.inv₀ ((continuous_circleMap z₀ R).continuousOn.sub continuousOn_const)
        fun θ _ => ?_).pow 2
      intro h0
      have h1 : circleMap z₀ R θ = z := sub_eq_zero.mp h0
      have h2 : dist z z₀ = R := by
        rw [← h1]
        exact Metric.mem_sphere.mp (circleMap_mem_sphere z₀ hR.le θ)
      rw [Metric.mem_ball] at hz_ball
      linarith
  have hint_f : IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * f (circleMap z₀ R θ)))
      volume 0 (2 * Real.pi) := by
    have h := (hcont_kern.mul hcont_f).intervalIntegrable (μ := volume)
    refine h.congr fun θ _ => ?_
    dsimp [Pi.mul_apply]; ring
  have hint_fc : IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ))))
      volume 0 (2 * Real.pi) := by
    have h := (hcont_kern.mul (Complex.continuous_conj.comp_continuousOn hcont_f)).intervalIntegrable (μ := volume)
    refine h.congr fun θ _ => ?_
    dsimp [Pi.mul_apply, Function.comp]; ring
  have hint_M : IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * ((2 * M : ℝ) : ℂ)))
      volume 0 (2 * Real.pi) := by
    have h := (hcont_kern.mul (continuousOn_const (c := ((2 * M : ℝ) : ℂ)))).intervalIntegrable (μ := volume)
    refine h.congr fun θ _ => ?_
    dsimp [Pi.mul_apply]; ring
  have hcomb : (2 * Real.pi * I) * deriv f z =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap z₀ R) θ * (circleMap z₀ R θ - z)⁻¹ ^ 2 *
          (((2 * ((f (circleMap z₀ R θ)).re - M) : ℝ) : ℂ)) := by
    have h1 : (2 * Real.pi * I) * deriv f z =
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * f (circleMap z₀ R θ))) +
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ)))) -
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * ((2 * M : ℝ) : ℂ))) := by
      simp only [smul_eq_mul] at hcauchy hM_zero
      rw [hcauchy, hconj_int, hM_zero]
      ring
    rw [h1, ← intervalIntegral.integral_add hint_f hint_fc,
      ← intervalIntegral.integral_sub (hint_f.add hint_fc) hint_M]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hre_sum : f (circleMap z₀ R θ) + starRingEnd ℂ (f (circleMap z₀ R θ)) =
        (((2 * (f (circleMap z₀ R θ)).re : ℝ) : ℂ)) := by
      simpa using Complex.add_conj (f (circleMap z₀ R θ))
    calc deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * f (circleMap z₀ R θ)) +
            deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ))) -
            deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * ((2 * M : ℝ) : ℂ))
        = deriv (circleMap z₀ R) θ * (circleMap z₀ R θ - z)⁻¹ ^ 2 *
            (f (circleMap z₀ R θ) + starRingEnd ℂ (f (circleMap z₀ R θ)) - ((2 * M : ℝ) : ℂ)) := by
          ring
      _ = deriv (circleMap z₀ R) θ * (circleMap z₀ R θ - z)⁻¹ ^ 2 *
            (((2 * ((f (circleMap z₀ R θ)).re - M) : ℝ) : ℂ)) := by
          rw [hre_sum]; push_cast; ring
  -- Mean value property for `Re f`: `∫_0^{2π} (M - Re(f(circleMap z₀ R θ))) dθ = 2π * (M - Re(f z₀))`
  have hmean_re :
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (M - (f (circleMap z₀ R θ)).re) =
        2 * Real.pi * (M - (f z₀).re) := by
    have hsimpl : ∀ θ : ℝ,
        deriv (circleMap z₀ R) θ • ((circleMap z₀ R θ - z₀)⁻¹ • f (circleMap z₀ R θ)) =
          I * f (circleMap z₀ R θ) := by
      intro θ
      rw [deriv_circleMap, smul_eq_mul, smul_eq_mul]
      have h1 : circleMap z₀ R θ - z₀ = circleMap 0 R θ := by simp [circleMap]
      have hne : circleMap 0 R θ ≠ 0 := by
        simp [circleMap, hR.ne', Complex.exp_ne_zero]
      rw [h1]
      field_simp [hne]
    have hmean2 : I * ∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap z₀ R θ) =
        (2 * Real.pi * I) * f z₀ := by
      rw [← intervalIntegral.integral_const_mul]
      have hEq : ∫ θ in (0 : ℝ)..(2 * Real.pi), I * f (circleMap z₀ R θ) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            deriv (circleMap z₀ R) θ • ((circleMap z₀ R θ - z₀)⁻¹ • f (circleMap z₀ R θ)) :=
        intervalIntegral.integral_congr fun θ _ => (hsimpl θ).symm
      rw [hEq]
      simpa [smul_eq_mul] using hmean
    have hmean3 : ∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap z₀ R θ) =
        ((2 * Real.pi : ℝ) : ℂ) * f z₀ := by
      have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
      apply mul_left_cancel₀ hI
      rw [hmean2]; push_cast; ring
    have hre_int : ∫ θ in (0 : ℝ)..(2 * Real.pi), (f (circleMap z₀ R θ)).re =
        2 * Real.pi * (f z₀).re := by
      have h1 := congrArg Complex.re hmean3
      rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hcont_f.intervalIntegrable] at h1
      simpa [Complex.reCLM_apply] using h1
    have hint_re : IntervalIntegrable (fun θ : ℝ => (f (circleMap z₀ R θ)).re)
        volume 0 (2 * Real.pi) :=
      (Complex.continuous_re.comp_continuousOn hcont_f).intervalIntegrable
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint_re,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, hre_int]
    ring
  -- Step 5: Take norms of `hcomb`!
  have hnorm_lhs : ‖(2 * Real.pi * I) * deriv f z‖ = (2 * Real.pi) * ‖deriv f z‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hRr_pos : 0 < R - r := by linarith
  have hnorm_bound :
      (2 * Real.pi) * ‖deriv f z‖ ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (2 * R / (R - r) ^ 2) * (M - (f (circleMap z₀ R θ)).re) := by
    rw [← hnorm_lhs, hcomb]
    refine (intervalIntegral.norm_integral_le_integral_norm h2pi_pos.le).trans ?_
    refine intervalIntegral.integral_mono_on h2pi_pos.le ?_ ?_ fun θ _ => ?_
    · exact ((hcont_kern.mul (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul ((Complex.continuous_re.comp_continuousOn hcont_f).sub
          continuousOn_const)))).norm).intervalIntegrable
    · exact (continuousOn_const.mul (continuousOn_const.sub
        (Complex.continuous_re.comp_continuousOn hcont_f))).intervalIntegrable
    · have hmem : circleMap z₀ R θ ∈ Metric.closedBall z₀ R :=
        Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hR.le θ)
      have hMge : 0 ≤ M - (f (circleMap z₀ R θ)).re := sub_nonneg.mpr (hre _ hmem)
      have hdist : R - r ≤ ‖circleMap z₀ R θ - z‖ := by
        have htri : ‖circleMap z₀ R θ - z₀‖ ≤ ‖circleMap z₀ R θ - z‖ + ‖z - z₀‖ := by
          simpa [sub_add_sub_cancel] using norm_add_le (circleMap z₀ R θ - z) (z - z₀)
        have hnormR : ‖circleMap z₀ R θ - z₀‖ = R := by
          simpa [dist_eq_norm] using Metric.mem_sphere.mp (circleMap_mem_sphere z₀ hR.le θ)
        linarith
      have hd_norm : ‖deriv (circleMap z₀ R) θ‖ = R := by
        rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one]
        simpa [dist_eq_norm] using Metric.mem_sphere.mp (circleMap_mem_sphere (0 : ℂ) hR.le θ)
      rw [norm_mul, norm_mul, norm_pow, norm_inv, hd_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_of_pos two_pos, abs_sub_comm, abs_of_nonneg hMge]
      have hinv_le : (‖circleMap z₀ R θ - z‖)⁻¹ ^ 2 ≤ ((R - r) ^ 2)⁻¹ := by
        rw [← inv_pow]
        simpa [inv_pow] using inv_anti₀ (sq_pos_of_pos hRr_pos) (pow_le_pow_left₀ hRr_pos.le hdist 2)
      calc R * (‖circleMap z₀ R θ - z‖)⁻¹ ^ 2 * (2 * (M - (f (circleMap z₀ R θ)).re))
          ≤ R * ((R - r) ^ 2)⁻¹ * (2 * (M - (f (circleMap z₀ R θ)).re)) := by
            gcongr
        _ = 2 * R / (R - r) ^ 2 * (M - (f (circleMap z₀ R θ)).re) := by ring
  rw [intervalIntegral.integral_const_mul, hmean_re] at hnorm_bound
  have hfinal : (2 * Real.pi) * ‖deriv f z‖ ≤
      (2 * Real.pi) * ((2 * R / (R - r) ^ 2) * (M - (f z₀).re)) := by
    linarith
  exact le_of_mul_le_mul_left hfinal h2pi_pos

/-! ## Section 2: Finite Blaschke Factorization & Landau's Local Log-Derivative Bound -/

/-- Blaschke factor on the disk `B(s₀, R)` vanishing at `ρ`:
`B(s₀, R, ρ, z) = R (z - ρ) / (R² - conj(ρ - s₀) (z - s₀))`. -/
def blaschkeFactor (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ :=
  (R : ℂ) * (z - ρ) / ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))

lemma blaschkeFactor_denom_ne_zero {s₀ ρ z : ℂ} {R : ℝ}
    (hR : 0 < R) (hρ : ‖ρ - s₀‖ < R) (hz : ‖z - s₀‖ ≤ R) :
    (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀) ≠ 0 := by
  intro h0
  have heq : (R : ℂ) ^ 2 = starRingEnd ℂ (ρ - s₀) * (z - s₀) := sub_eq_zero.mp h0
  have hn := congrArg norm heq
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul, Complex.norm_conj] at hn
  have hlt : ‖ρ - s₀‖ * ‖z - s₀‖ < R ^ 2 := by nlinarith [norm_nonneg (ρ - s₀), norm_nonneg (z - s₀)]
  linarith

/-- On the boundary sphere `‖z - s₀‖ = R`, every Blaschke factor with `‖ρ - s₀‖ < R` has unit
modulus `‖B(s₀, R, ρ, z)‖ = 1`. -/
theorem blaschkeFactor_norm_eq_one_on_sphere {s₀ ρ z : ℂ} {R : ℝ}
    (hR : 0 < R) (hρ : ‖ρ - s₀‖ < R) (hz : z ∈ Metric.sphere s₀ R) :
    ‖blaschkeFactor s₀ R ρ z‖ = 1 := by
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  have hden := blaschkeFactor_denom_ne_zero hR hρ hz.le
  unfold blaschkeFactor
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)]
  -- Compare `‖R (z - ρ)‖²` and `‖R² - conj(ρ - s₀)(z - s₀)‖²` via `Complex.normSq`
  have hsq : ‖(R : ℂ) * (z - ρ)‖ ^ 2 = ‖(R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    set a : ℂ := ρ - s₀
    set w : ℂ := z - s₀
    have hzr : z - ρ = w - a := by simp [a, w]
    have hw_sq : Complex.normSq w = R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hz]
    rw [hzr, map_mul, Complex.normSq_ofReal]
    have h1 : Complex.normSq (w - a) = Complex.normSq w - 2 * (w * starRingEnd ℂ a).re + Complex.normSq a := by
      rw [Complex.normSq_sub, Complex.normSq_apply, Complex.normSq_apply]
      simp [Complex.mul_re]; ring
    have h2 : Complex.normSq ((R : ℂ) ^ 2 - starRingEnd ℂ a * w) =
        R ^ 4 - 2 * R ^ 2 * (w * starRingEnd ℂ a).re + Complex.normSq a * Complex.normSq w := by
      rw [Complex.normSq_sub, map_pow, Complex.normSq_ofReal, map_mul, Complex.normSq_conj]
      have hre : ((R : ℂ) ^ 2 * starRingEnd ℂ (starRingEnd ℂ a * w)).re =
          R ^ 2 * (w * starRingEnd ℂ a).re := by
        rw [map_mul, Complex.conj_conj]
        have hR2 : ((R : ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) := by push_cast; rfl
        rw [hR2, Complex.re_ofReal_mul]
        have hconj : (a * starRingEnd ℂ w).re = (w * starRingEnd ℂ a).re := by
          have := Complex.conj_re (a * starRingEnd ℂ w)
          rw [map_mul, Complex.conj_conj, mul_comm] at this
          exact this.symm
        rw [hconj]
      rw [hre]; ring
    rw [h1, h2, hw_sq]; ring
  nlinarith [norm_nonneg ((R : ℂ) * (z - ρ)),
    norm_nonneg ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))]

theorem blaschkeFactor_eval_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) :
    blaschkeFactor s₀ R ρ s₀ = -(ρ - s₀) / (R : ℂ) := by
  unfold blaschkeFactor
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  simp only [sub_self, mul_zero, sub_zero]
  field_simp [hRne]
  ring

theorem blaschkeFactor_norm_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) :
    ‖blaschkeFactor s₀ R ρ s₀‖ = ‖ρ - s₀‖ / R := by
  rw [blaschkeFactor_eval_center hR, norm_div, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg hR.le]

theorem blaschkeFactor_hasDerivAt_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) :
    HasDerivAt (blaschkeFactor s₀ R ρ)
      (1 / (R : ℂ) - (ρ - s₀) * starRingEnd ℂ (ρ - s₀) / (R : ℂ) ^ 3) s₀ := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hnum : HasDerivAt (fun z : ℂ => (R : ℂ) * (z - ρ)) (R : ℂ) s₀ := by
    simpa using ((hasDerivAt_id s₀).sub_const ρ).const_mul (R : ℂ)
  have hden : HasDerivAt (fun z : ℂ => (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))
      (-(starRingEnd ℂ (ρ - s₀))) s₀ := by
    have h1 := ((hasDerivAt_id s₀).sub_const s₀).const_mul (starRingEnd ℂ (ρ - s₀))
    simpa using (hasDerivAt_const s₀ ((R : ℂ) ^ 2)).fun_sub h1
  have hden_ne : (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (s₀ - s₀) ≠ 0 := by
    simp [pow_ne_zero 2 hRne]
  refine (hnum.div hden hden_ne).congr_deriv ?_
  simp only [sub_self, mul_zero, sub_zero]
  field_simp [hRne]
  ring

/-- Exact logarithmic derivative of a Blaschke factor at the center `s₀`:
`B_ρ'(s₀) / B_ρ(s₀) = 1 / (s₀ - ρ) - conj(s₀ - ρ) / R²`. -/
theorem blaschkeFactor_logDeriv_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) (hne : ρ ≠ s₀) :
    deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀ =
      1 / (s₀ - ρ) - starRingEnd ℂ (s₀ - ρ) / (R : ℂ) ^ 2 := by
  rw [(blaschkeFactor_hasDerivAt_center hR).deriv, blaschkeFactor_eval_center hR]
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hsub : s₀ - ρ ≠ 0 := sub_ne_zero.mpr hne.symm
  have hsub' : ρ - s₀ ≠ 0 := sub_ne_zero.mpr hne
  have hneg : starRingEnd ℂ (ρ - s₀) = -starRingEnd ℂ (s₀ - ρ) := by
    rw [← map_neg]; congr 1; ring
  rw [hneg]
  field_simp [hRne, hsub, hsub']
  ring

/-- Exact real part of the Blaschke log-derivative at `s₀`:
`Re(B_ρ'(s₀) / B_ρ(s₀)) = Re(s₀ - ρ) * (1 / ‖s₀ - ρ‖² - 1 / R²)`. -/
theorem blaschkeFactor_logDeriv_center_re {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) (hne : ρ ≠ s₀) :
    (deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀).re =
      (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2) := by
  rw [blaschkeFactor_logDeriv_center hR hne, Complex.sub_re, one_div, Complex.inv_re,
    Complex.normSq_eq_norm_sq]
  have hR2 : ((R : ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hR2, Complex.div_ofReal_re, Complex.conj_re]
  ring

lemma blaschkeFactor_logDeriv_center_re_nonneg {s₀ ρ : ℂ} {R : ℝ}
    (hR : 0 < R) (hne : ρ ≠ s₀) (hρR : ‖ρ - s₀‖ < R) (hre : ρ.re ≤ s₀.re) :
    0 ≤ (deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀).re := by
  rw [blaschkeFactor_logDeriv_center_re hR hne]
  have hpos : 0 < ‖s₀ - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hnorm_lt : ‖s₀ - ρ‖ < R := by rwa [norm_sub_rev]
  have h1 : 1 / R ^ 2 ≤ 1 / ‖s₀ - ρ‖ ^ 2 := by
    rw [one_div, one_div]
    exact inv_anti₀ (sq_pos_of_pos hpos) (pow_le_pow_left₀ hpos.le hnorm_lt.le 2)
  exact mul_nonneg (by simp [hre]) (sub_nonneg.mpr h1)

/-- Elementary `dslope` + Maximum Modulus finite Blaschke factorization:
for any `g` analytic on `closedBall s₀ R` (`0 < r < R`) with `g s₀ ≠ 0`, there exist a finite
list `L : List ℂ` of zeros of `g` in `closedBall s₀ r` and a function `h` analytic on
`closedBall s₀ R`, nonvanishing on `closedBall s₀ r`, such that
`g z = h z * (L.map (blaschkeFactor s₀ R · z)).prod` on `closedBall s₀ R` and
`∀ z ∈ closedBall s₀ R, ‖h z‖ ≤ M₀` whenever `‖g z‖ ≤ M₀` on `sphere s₀ R`. -/
theorem exists_blaschke_factorization {g : ℂ → ℂ} {s₀ : ℂ} {R r M₀ : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hM₀ : ∀ z ∈ Metric.sphere s₀ R, ‖g z‖ ≤ M₀) :
    ∃ (L : List ℂ) (h : ℂ → ℂ),
      (∀ ρ ∈ L, ρ ∈ Metric.closedBall s₀ r ∧ ρ ≠ s₀ ∧ g ρ = 0) ∧
      (∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ ∈ L) ∧
      AnalyticOnNhd ℂ h (Metric.closedBall s₀ R) ∧
      (∀ z ∈ Metric.closedBall s₀ r, h z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall s₀ R,
        g z = h z * (L.map (fun ρ => blaschkeFactor s₀ R ρ z)).prod) ∧
      (∀ z ∈ Metric.closedBall s₀ R, ‖h z‖ ≤ M₀) := by
  have hR : 0 < R := lt_trans hr hrR
  set q : ℝ := R / r with hq_def
  have hq1 : 1 < q := (one_lt_div hr).mpr hrR
  have hg0_pos : 0 < ‖g s₀‖ := norm_pos_iff.mpr hg0
  -- Choose fuel `N` such that `M₀ < ‖g s₀‖ * q ^ N`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M₀ < ‖g s₀‖ * q ^ N := by
    have hev := (tendsto_pow_atTop_atTop_of_one_lt hq1).eventually
      (Filter.eventually_gt_atTop (M₀ / ‖g s₀‖))
    obtain ⟨N, hN⟩ := hev.exists
    exact ⟨N, by have := (div_lt_iff₀ hg0_pos).mp hN; linarith⟩
  have hfr_sub : frontier (Metric.ball s₀ R) ⊆ Metric.sphere s₀ R := by
    intro z hz
    rw [Metric.mem_sphere]
    have hcl : z ∈ Metric.closedBall s₀ R := by
      rw [← closure_ball s₀ hR.ne']
      exact hz.1
    have hnot : z ∉ Metric.ball s₀ R := by
      rw [← interior_eq_iff_isOpen.mpr Metric.isOpen_ball]
      exact hz.2
    rw [Metric.mem_closedBall] at hcl
    rw [Metric.mem_ball, not_lt] at hnot
    exact le_antisymm hcl hnot
  -- Core inductive peeling lemma
  have hpeel : ∀ (n : ℕ) (f : ℂ → ℂ),
      AnalyticOnNhd ℂ f (Metric.closedBall s₀ R) →
      f s₀ ≠ 0 →
      (∀ z ∈ Metric.sphere s₀ R, ‖f z‖ ≤ M₀) →
      M₀ < ‖f s₀‖ * q ^ n →
      ∃ (L : List ℂ) (h : ℂ → ℂ),
        (∀ ρ ∈ L, ρ ∈ Metric.closedBall s₀ r ∧ ρ ≠ s₀) ∧
        AnalyticOnNhd ℂ h (Metric.closedBall s₀ R) ∧
        (∀ z ∈ Metric.closedBall s₀ r, h z ≠ 0) ∧
        (∀ z ∈ Metric.closedBall s₀ R,
          f z = h z * (L.map (fun ρ => blaschkeFactor s₀ R ρ z)).prod) ∧
        (∀ z ∈ Metric.closedBall s₀ R, ‖h z‖ ≤ M₀) := by
    intro n
    induction n with
    | zero =>
      intro f hf _ hfM hlt
      simp only [pow_zero, mul_one] at hlt
      -- Contradicts Maximum Modulus Principle!
      have hdc : DiffContOnCl ℂ f (Metric.ball s₀ R) := by
        refine ⟨(hf.mono Metric.ball_subset_closedBall).differentiableOn, ?_⟩
        rw [closure_ball s₀ hR.ne']
        exact hf.continuousOn
      have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc
        (fun z hz => hfM z (hfr_sub hz))
        (by rw [closure_ball s₀ hR.ne']; exact Metric.mem_closedBall_self hR.le)
      linarith
    | succ k ih =>
      intro f hf hf0 hfM hlt
      by_cases hnz : ∀ z ∈ Metric.closedBall s₀ r, f z ≠ 0
      · -- Already zero-free on `closedBall s₀ r`!
        have hdc : DiffContOnCl ℂ f (Metric.ball s₀ R) := by
          refine ⟨(hf.mono Metric.ball_subset_closedBall).differentiableOn, ?_⟩
          rw [closure_ball s₀ hR.ne']
          exact hf.continuousOn
        have hmax : ∀ z ∈ Metric.closedBall s₀ R, ‖f z‖ ≤ M₀ := fun z hz =>
          Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc
            (fun w hw => hfM w (hfr_sub hw))
            (by rwa [closure_ball s₀ hR.ne'])
        exact ⟨[], f, by simp, hf, hnz, fun z _ => by simp, hmax⟩
      · -- Peel off one Blaschke factor at a zero `ρ ∈ closedBall s₀ r`!
        push Not at hnz
        obtain ⟨ρ, hρ_mem, hρ_zero⟩ := hnz
        have hρ_ne : ρ ≠ s₀ := fun h => hf0 (h ▸ hρ_zero)
        have hρ_norm : ‖ρ - s₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem
        have hρ_lt : ‖ρ - s₀‖ < R := lt_of_le_of_lt hρ_norm hrR
        set f₁ : ℂ → ℂ := fun z =>
          (((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)) / (R : ℂ)) * dslope f ρ z
        have hf₁_an : AnalyticOnNhd ℂ f₁ (Metric.closedBall s₀ R) := by
          -- Find an open neighborhood `U` of `closedBall s₀ R` where `f` is differentiable
          have hopen_ex : ∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall s₀ R ⊆ U ∧
              DifferentiableOn ℂ f U := by
            refine ⟨{z | AnalyticAt ℂ f z}, isOpen_analyticAt ℂ f, fun z hz => hf z hz,
              fun z hz => hz.differentiableAt.differentiableWithinAt⟩
          obtain ⟨U, hU_open, hU_sub, hfU⟩ := hopen_ex
          have hρU : U ∈ 𝓝 ρ :=
            hU_open.mem_nhds (hU_sub (Metric.closedBall_subset_closedBall hrR.le hρ_mem))
          have hdsU : DifferentiableOn ℂ (dslope f ρ) U :=
            (Complex.differentiableOn_dslope hρU).mpr hfU
          have hds_an : AnalyticOnNhd ℂ (dslope f ρ) (Metric.closedBall s₀ R) :=
            (hdsU.analyticOnNhd hU_open).mono hU_sub
          have hlin_an : AnalyticOnNhd ℂ
              (fun z : ℂ => ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)) / (R : ℂ))
              (Metric.closedBall s₀ R) := by
            refine (((analyticOnNhd_const.sub
              (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))).div
              analyticOnNhd_const) fun z _ => Complex.ofReal_ne_zero.mpr hR.ne')
          exact hlin_an.mul hds_an
        have hfac : ∀ z ∈ Metric.closedBall s₀ R, f z = f₁ z * blaschkeFactor s₀ R ρ z := by
          intro z hz
          have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
          have hden := blaschkeFactor_denom_ne_zero hR hρ_lt
            (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
          have hds_eq : (z - ρ) * dslope f ρ z = f z := by
            have := sub_smul_dslope f ρ z
            rw [hρ_zero, sub_zero, smul_eq_mul] at this
            exact this
          dsimp only [f₁, blaschkeFactor]
          calc f z = (z - ρ) * dslope f ρ z := hds_eq.symm
            _ = (((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)) / (R : ℂ) * dslope f ρ z) *
                ((R : ℂ) * (z - ρ) / ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))) := by
                field_simp [hRne, hden]
        have hf₁0 : f₁ s₀ ≠ 0 := by
          intro h0
          have := hfac s₀ (Metric.mem_closedBall_self hR.le)
          rw [h0, zero_mul] at this
          exact hf0 this
        have hf₁M : ∀ z ∈ Metric.sphere s₀ R, ‖f₁ z‖ ≤ M₀ := by
          intro z hz
          have h1 := congrArg norm (hfac z (Metric.sphere_subset_closedBall hz))
          rw [norm_mul, blaschkeFactor_norm_eq_one_on_sphere hR hρ_lt hz, mul_one] at h1
          rw [← h1]
          exact hfM z hz
        have hgrowth : ‖f s₀‖ * q ≤ ‖f₁ s₀‖ := by
          have h1 := congrArg norm (hfac s₀ (Metric.mem_closedBall_self hR.le))
          rw [norm_mul, blaschkeFactor_norm_center hR] at h1
          have hpos_ρ : 0 < ‖ρ - s₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρ_ne)
          have hle : ‖ρ - s₀‖ / R ≤ r / R := div_le_div_of_nonneg_right hρ_norm hR.le
          have h2 : ‖f s₀‖ ≤ ‖f₁ s₀‖ * (r / R) := by
            rw [h1]
            exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
          rw [hq_def, mul_div_assoc', div_le_iff₀ hr]
          have h3 := mul_le_mul_of_nonneg_right h2 hR.le
          have h4 : ‖f₁ s₀‖ * (r / R) * R = ‖f₁ s₀‖ * r := by field_simp [hR.ne']
          linarith
        have hlt₁ : M₀ < ‖f₁ s₀‖ * q ^ k := by
          have hq_pow_nonneg : 0 ≤ q ^ k := pow_nonneg (by positivity) k
          calc M₀ < ‖f s₀‖ * q ^ (k + 1) := hlt
            _ = (‖f s₀‖ * q) * q ^ k := by rw [pow_succ']; ring
            _ ≤ ‖f₁ s₀‖ * q ^ k := mul_le_mul_of_nonneg_right hgrowth hq_pow_nonneg
        obtain ⟨L₁, h, hL₁, hh_an, hh_nz, hh_eq, hh_M⟩ := ih f₁ hf₁_an hf₁0 hf₁M hlt₁
        refine ⟨ρ :: L₁, h, ?_, hh_an, hh_nz, ?_, hh_M⟩
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact ⟨hρ_mem, hρ_ne⟩
          · exact hL₁ w hw'
        · intro z hz
          rw [hfac z hz, hh_eq z hz, List.map_cons, List.prod_cons]
          ring
  obtain ⟨L, h, hL, hh_an, hh_nz, hh_eq, hh_M⟩ := hpeel N g hg hg0 hM₀ hN
  refine ⟨L, h, ?_, ?_, hh_an, hh_nz, hh_eq, hh_M⟩
  · intro ρ hρ
    obtain ⟨hρ_mem, hρ_ne⟩ := hL ρ hρ
    refine ⟨hρ_mem, hρ_ne, ?_⟩
    rw [hh_eq ρ (Metric.closedBall_subset_closedBall hrR.le hρ_mem)]
    have hzero_fac : blaschkeFactor s₀ R ρ ρ = 0 := by simp [blaschkeFactor]
    have hprod_zero : (L.map (fun w => blaschkeFactor s₀ R w ρ)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.mpr ⟨ρ, hρ, hzero_fac⟩)
    rw [hprod_zero, mul_zero]
  · intro ρ hρ_mem hρ_zero
    have hprod := hh_eq ρ (Metric.closedBall_subset_closedBall hrR.le hρ_mem)
    rw [hρ_zero] at hprod
    have h0 : (L.map (fun w => blaschkeFactor s₀ R w ρ)).prod = 0 :=
      (mul_eq_zero.mp hprod.symm).resolve_left (hh_nz ρ hρ_mem)
    obtain ⟨w, hwL, hBw⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    have hden := blaschkeFactor_denom_ne_zero hR
      (lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_eq_norm] using (hL w hwL).1) hrR)
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using
        Metric.closedBall_subset_closedBall hrR.le hρ_mem)
    unfold blaschkeFactor at hBw
    have hnum : (R : ℂ) * (ρ - w) = 0 := (div_eq_zero_iff.mp hBw).resolve_right hden
    have hρw : ρ = w := sub_eq_zero.mp ((mul_eq_zero.mp hnum).resolve_left
      (Complex.ofReal_ne_zero.mpr hR.ne'))
    exact hρw ▸ hwL

/-- **Radial Holomorphic Primitive on an Open Ball**:
any holomorphic function `H` on `ball s₀ r` (`0 < r`) has the explicit holomorphic primitive
`P(z) = ∫ u in 0..1, (z - s₀) * H (s₀ + u * (z - s₀))` satisfying `HasDerivAt P (H z) z`
for every `z ∈ ball s₀ r` and `P s₀ = 0`. -/
theorem hasDerivAt_radial_primitive_ball {H : ℂ → ℂ} {s₀ z : ℂ} {r : ℝ}
    (hH : DifferentiableOn ℂ H (Metric.ball s₀ r)) (hz : z ∈ Metric.ball s₀ r) :
    HasDerivAt (fun w : ℂ => ∫ u in (0 : ℝ)..1, (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀))) (H z) z := by
  have hH_an : AnalyticOnNhd ℂ H (Metric.ball s₀ r) := hH.analyticOnNhd Metric.isOpen_ball
  have hH_cont : ContinuousOn H (Metric.ball s₀ r) := hH_an.continuousOn
  have hH'_an : AnalyticOnNhd ℂ (deriv H) (Metric.ball s₀ r) := fun w hw => (hH_an w hw).deriv
  have hH'_cont : ContinuousOn (deriv H) (Metric.ball s₀ r) := hH'_an.continuousOn
  set δ : ℝ := (r - ‖z - s₀‖) / 2 with hδ_def
  have hδ0 : 0 < δ := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    linarith
  have hmem_ball : ∀ w ∈ Metric.closedBall z δ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      s₀ + (u : ℂ) * (w - s₀) ∈ Metric.ball s₀ r := by
    intro w hw u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hu.1]
    have hws : ‖w - s₀‖ ≤ ‖z - s₀‖ + δ := by
      have htri := norm_add_le (w - z) (z - s₀)
      rw [sub_add_sub_cancel] at htri
      linarith
    have hlt : ‖z - s₀‖ + δ < r := by
      rw [Metric.mem_ball, dist_eq_norm] at hz; linarith
    calc u * ‖w - s₀‖ ≤ 1 * ‖w - s₀‖ := mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _)
      _ = ‖w - s₀‖ := one_mul _
      _ ≤ ‖z - s₀‖ + δ := hws
      _ < r := hlt
  set Φ : ℂ × ℝ → ℂ := fun p => s₀ + (p.2 : ℂ) * (p.1 - s₀)
  have hΦ_cont : Continuous Φ := by fun_prop
  set K : Set ℂ := Φ '' (Metric.closedBall z δ ×ˢ Set.Icc (0 : ℝ) 1)
  have hK_comp : IsCompact K := ((isCompact_closedBall z δ).prod isCompact_Icc).image hΦ_cont
  have hK_sub : K ⊆ Metric.ball s₀ r := by
    rintro _ ⟨⟨w, u⟩, ⟨hw, hu⟩, rfl⟩
    exact hmem_ball w hw u hu
  obtain ⟨M₁, hM₁⟩ := hK_comp.exists_bound_of_continuousOn (hH_cont.mono hK_sub)
  obtain ⟨M₂, hM₂⟩ := hK_comp.exists_bound_of_continuousOn (hH'_cont.mono hK_sub)
  set B : ℝ := |M₁| + (‖z - s₀‖ + δ) * |M₂|
  have hstep : HasDerivAt
      (fun w : ℂ => ∫ u in (0 : ℝ)..1, (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀)))
      (∫ u in (0 : ℝ)..1,
        (H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀))))) z := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w u => (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀)))
      (F' := fun w u => H (s₀ + (u : ℂ) * (w - s₀)) +
        (w - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (w - s₀))))
      (bound := fun _ : ℝ => B)
      (Metric.ball_mem_nhds z hδ0) ?_ ?_ ?_ ?_ (intervalIntegrable_const (c := B)) ?_).2
    · filter_upwards [Metric.ball_mem_nhds z hδ0] with w hw
      have hcw : ContinuousOn (fun u : ℝ => (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        refine continuousOn_const.mul (hH_cont.comp ?_ fun u hu =>
          hmem_ball w (Metric.ball_subset_closedBall hw) u hu)
        exact continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
      exact (hcw.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · have hcz : ContinuousOn (fun u : ℝ => (z - s₀) * H (s₀ + (u : ℂ) * (z - s₀))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        refine continuousOn_const.mul (hH_cont.comp ?_ fun u hu =>
          hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu)
        exact continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
      exact hcz.intervalIntegrable
    · have hcz' : ContinuousOn (fun u : ℝ =>
          H (s₀ + (u : ℂ) * (z - s₀)) +
            (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀)))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        have hcomp : ContinuousOn (fun u : ℝ => s₀ + (u : ℂ) * (z - s₀)) (Set.Icc 0 1) :=
          continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
        exact (hH_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu).add
          (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul
            (hH'_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu)))
      exact (hcz'.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · refine Eventually.of_forall fun u hu w hw => ?_
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu_cc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
      have hw_cb : w ∈ Metric.closedBall z δ := Metric.ball_subset_closedBall hw
      have hKmem : s₀ + (u : ℂ) * (w - s₀) ∈ K :=
        ⟨(w, u), ⟨hw_cb, hu_cc⟩, rfl⟩
      have h1 : ‖H (s₀ + (u : ℂ) * (w - s₀))‖ ≤ |M₁| :=
        (hM₁ _ hKmem).trans (le_abs_self M₁)
      have h2 : ‖deriv H (s₀ + (u : ℂ) * (w - s₀))‖ ≤ |M₂| :=
        (hM₂ _ hKmem).trans (le_abs_self M₂)
      have hws : ‖w - s₀‖ ≤ ‖z - s₀‖ + δ := by
        have htri := norm_add_le (w - z) (z - s₀)
        rw [sub_add_sub_cancel] at htri
        rw [Metric.mem_closedBall, dist_eq_norm] at hw_cb
        linarith
      have huM2 : u * ‖deriv H (s₀ + (u : ℂ) * (w - s₀))‖ ≤ 1 * |M₂| :=
        mul_le_mul hu_cc.2 h2 (norm_nonneg _) zero_le_one
      calc ‖H (s₀ + (u : ℂ) * (w - s₀)) +
              (w - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (w - s₀)))‖
          ≤ ‖H (s₀ + (u : ℂ) * (w - s₀))‖ +
            ‖w - s₀‖ * (u * ‖deriv H (s₀ + (u : ℂ) * (w - s₀))‖) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu_cc.1]
        _ ≤ |M₁| + (‖z - s₀‖ + δ) * (1 * |M₂|) := by
            gcongr
            exact mul_nonneg hu_cc.1 (norm_nonneg _)
        _ = B := by dsimp only [B]; ring
    · refine Eventually.of_forall fun u hu w hw => ?_
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu_cc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
      have hmem := hmem_ball w (Metric.ball_subset_closedBall hw) u hu_cc
      have hH_at : HasDerivAt H (deriv H (s₀ + (u : ℂ) * (w - s₀))) (s₀ + (u : ℂ) * (w - s₀)) :=
        (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).hasDerivAt
      have hlin : HasDerivAt (fun x : ℂ => s₀ + (u : ℂ) * (x - s₀)) (u : ℂ) w := by
        simpa using (hasDerivAt_const w s₀).fun_add (((hasDerivAt_id w).sub_const s₀).const_mul (u : ℂ))
      have hcomp := hH_at.comp w hlin
      have hmul := ((hasDerivAt_id w).sub_const s₀).fun_mul hcomp
      refine hmul.congr_deriv ?_
      dsimp [Function.comp]
      ring
  -- Evaluate the integral of the total derivative `d/du (u * H(s₀ + u * (z - s₀)))` by FTC!
  have hftc : ∫ u in (0 : ℝ)..1,
      (H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀)))) =
      H z := by
    have hderiv_u : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (t : ℂ) * H (s₀ + (t : ℂ) * (z - s₀)))
          (H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀)))) u := by
      intro u hu
      rw [Set.uIcc_of_le zero_le_one] at hu
      have hmem := hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu
      have hH_at : HasDerivAt H (deriv H (s₀ + (u : ℂ) * (z - s₀))) (s₀ + (u : ℂ) * (z - s₀)) :=
        (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).hasDerivAt
      have hlin : HasDerivAt (fun t : ℝ => s₀ + (t : ℂ) * (z - s₀)) (z - s₀) u := by
        have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
        simpa using (hasDerivAt_const u s₀).fun_add (hof.mul_const (z - s₀))
      have hcomp : HasDerivAt (fun t : ℝ => H (s₀ + (t : ℂ) * (z - s₀)))
          (deriv H (s₀ + (u : ℂ) * (z - s₀)) * (z - s₀)) u :=
        HasDerivAt.comp u hH_at hlin
      have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
      refine (hof.fun_mul hcomp).congr_deriv ?_
      ring
    have hcont_u : ContinuousOn (fun u : ℝ =>
        H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀))))
        (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le zero_le_one]
      have hcomp : ContinuousOn (fun u : ℝ => s₀ + (u : ℂ) * (z - s₀)) (Set.Icc 0 1) :=
        continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
      exact (hH_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu).add
        (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul
          (hH'_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu)))
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_u hcont_u.intervalIntegrable
    simpa using h
  rwa [hftc] at hstep

/-- **Holomorphic Logarithm on a Ball**:
if `h` is holomorphic and nonvanishing on `ball s₀ r` (`0 < r`), then there exists `L : ℂ → ℂ`
holomorphic on `ball s₀ r` with `L s₀ = 0`, `HasDerivAt L (deriv h z / h z) z`, and
`cexp (L z) = h z / h s₀` for every `z ∈ ball s₀ r`. -/
theorem exists_holomorphic_log_ball {h : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (Metric.ball s₀ r))
    (hnz : ∀ z ∈ Metric.ball s₀ r, h z ≠ 0) :
    ∃ L : ℂ → ℂ, L s₀ = 0 ∧
      (∀ z ∈ Metric.ball s₀ r, HasDerivAt L (deriv h z / h z) z) ∧
      (∀ z ∈ Metric.ball s₀ r, cexp (L z) = h z / h s₀) := by
  set H : ℂ → ℂ := fun z => deriv h z / h z
  have hH_diff : DifferentiableOn ℂ H (Metric.ball s₀ r) :=
    (hh.deriv Metric.isOpen_ball).div hh hnz
  set L : ℂ → ℂ := fun w => ∫ u in (0 : ℝ)..1, (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀))
  have hL0 : L s₀ = 0 := by simp [L]
  have hL_deriv : ∀ z ∈ Metric.ball s₀ r, HasDerivAt L (H z) z :=
    fun z hz => hasDerivAt_radial_primitive_ball hH_diff hz
  refine ⟨L, hL0, hL_deriv, fun z hz => ?_⟩
  -- `q(w) = h(w) * exp(-L(w))` has derivative `0` on the convex open ball `ball s₀ r`
  set q : ℂ → ℂ := fun w => h w * cexp (-L w)
  have hq_deriv : ∀ w ∈ Metric.ball s₀ r, HasDerivAt q 0 w := by
    intro w hw
    have hh_at : HasDerivAt h (deriv h w) w :=
      (hh.differentiableAt (Metric.isOpen_ball.mem_nhds hw)).hasDerivAt
    have hL_at : HasDerivAt L (deriv h w / h w) w := hL_deriv w hw
    have hexp : HasDerivAt (fun x => cexp (-L x)) (cexp (-L w) * -(deriv h w / h w)) w :=
      hL_at.neg.cexp
    refine (hh_at.mul hexp).congr_deriv ?_
    have hne := hnz w hw
    field_simp [hne]
    ring
  have hq_const : q z = q s₀ := by
    have hconv : Convex ℝ (Metric.ball s₀ r) := convex_ball s₀ r
    refine hconv.is_const_of_fderivWithin_eq_zero
      (fun w hw => ((hq_deriv w hw).hasFDerivAt.restrictScalars ℝ).differentiableAt.differentiableWithinAt) ?_
      hz (Metric.mem_ball_self hr)
    intro w hw
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hw,
      ((hq_deriv w hw).hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  have hqs₀ : q s₀ = h s₀ := by simp [q, hL0]
  have hhz₀ : h s₀ ≠ 0 := hnz s₀ (Metric.mem_ball_self hr)
  rw [hqs₀] at hq_const
  dsimp only [q] at hq_const
  have hmul : h z = h s₀ * cexp (L z) := by
    calc h z = (h z * cexp (-L z)) * cexp (L z) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = h s₀ * cexp (L z) := by rw [hq_const]
  rw [hmul, mul_div_cancel_left₀ _ hhz₀]

/-- Logarithmic derivative of a product with a finite list of functions (at a point where all
factors are nonzero). -/
private lemma hasDerivAt_logDeriv_list_prod {s₀ : ℂ} {L : List ℂ} {F : ℂ → ℂ → ℂ} {F' : ℂ → ℂ}
    (hd : ∀ ρ ∈ L, HasDerivAt (F ρ) (F' ρ) s₀)
    (hnz : ∀ ρ ∈ L, F ρ s₀ ≠ 0) :
    HasDerivAt (fun z => (L.map (fun ρ => F ρ z)).prod)
      ((L.map (fun ρ => F ρ s₀)).prod * (L.map (fun ρ => F' ρ / F ρ s₀)).sum) s₀ := by
  induction L with
  | nil => simp [hasDerivAt_const]
  | cons a t ih =>
    have ha_d : HasDerivAt (F a) (F' a) s₀ := hd a (List.mem_cons_self ..)
    have ha_nz : F a s₀ ≠ 0 := hnz a (List.mem_cons_self ..)
    have ht_ih := ih (fun ρ hρ => hd ρ (List.mem_cons_of_mem a hρ))
      (fun ρ hρ => hnz ρ (List.mem_cons_of_mem a hρ))
    have hfun : (fun z => ((a :: t).map (fun ρ => F ρ z)).prod) =
        fun z => F a z * (t.map (fun ρ => F ρ z)).prod := by
      funext z; simp
    rw [hfun]
    refine (ha_d.fun_mul ht_ih).congr_deriv ?_
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    field_simp [ha_nz]

/-- **Landau's Local Log-Derivative Carathéodory Bound (Full Blaschke-Sum Form)**:
if `g` is analytic on `closedBall s₀ R` (`0 < r < R`), `g s₀ ≠ 0`, `1 ≤ M`, and
`∀ z ∈ closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖`, then there exists a finite list `L` of zeros of `g`
in `closedBall s₀ r` (containing EVERY zero of `g` in `closedBall s₀ r`) such that:
`(-deriv g s₀ / g s₀).re ≤ (2 / r) * Real.log M - (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖^2 - 1 / R^2))).sum`. -/
theorem landau_negLogDeriv_full {g : ℂ → ℂ} {s₀ : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖) :
    ∃ L : List ℂ,
      (∀ ρ ∈ L, ρ ∈ Metric.closedBall s₀ r ∧ ρ ≠ s₀ ∧ g ρ = 0) ∧
      (∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ ∈ L) ∧
      (-deriv g s₀ / g s₀).re ≤
        (2 / r) * Real.log M -
          (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
  have hR : 0 < R := lt_trans hr hrR
  obtain ⟨L, h, hL, hL_cov, hh_an, hh_nz, hh_eq, hh_M⟩ :=
    exists_blaschke_factorization hr hrR hg hg0
      (fun z hz => hbd z (Metric.sphere_subset_closedBall hz))
  -- Lower bound `‖h s₀‖ ≥ ‖g s₀‖` because `‖B_ρ(s₀)‖ = ‖ρ - s₀‖ / R ≤ r / R < 1`
  have hprod_le_one : ‖(L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod‖ ≤ 1 := by
    have haux : ∀ (l : List ℂ), (∀ ρ ∈ l, ‖ρ - s₀‖ ≤ R) →
        ‖(l.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod‖ ≤ 1 := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a t ih =>
        intro hl
        simp only [List.map_cons, List.prod_cons, norm_mul]
        have ha : ‖blaschkeFactor s₀ R a s₀‖ ≤ 1 := by
          rw [blaschkeFactor_norm_center hR]
          exact (div_le_one hR).mpr (hl a (List.mem_cons_self ..))
        have ht := ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ))
        nlinarith [norm_nonneg (blaschkeFactor s₀ R a s₀),
          norm_nonneg (t.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod]
    refine haux L fun ρ hρ => ?_
    have h1 : ‖ρ - s₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using (hL ρ hρ).1
    exact h1.trans hrR.le
  have hh0_ge : ‖g s₀‖ ≤ ‖h s₀‖ := by
    have h1 := congrArg norm (hh_eq s₀ (Metric.mem_closedBall_self hR.le))
    rw [norm_mul] at h1
    rw [h1]
    exact mul_le_of_le_one_right (norm_nonneg _) hprod_le_one
  have hh0_ne : h s₀ ≠ 0 := hh_nz s₀ (Metric.mem_closedBall_self hr.le)
  have hh0_pos : 0 < ‖h s₀‖ := norm_pos_iff.mpr hh0_ne
  -- Holomorphic logarithm `Log` of `h / h s₀` on `ball s₀ r`
  have hh_diff : DifferentiableOn ℂ h (Metric.ball s₀ r) :=
    (hh_an.mono (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hrR.le))).differentiableOn
  obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
    exists_holomorphic_log_ball hr hh_diff (fun z hz => hh_nz z (Metric.ball_subset_closedBall hz))
  have hLog_diff : DifferentiableOn ℂ Log (Metric.ball s₀ r) :=
    fun z hz => (hLog_d z hz).differentiableAt.differentiableWithinAt
  have hLog_re : ∀ z ∈ Metric.ball s₀ r, (Log z).re ≤ Real.log M := by
    intro z hz
    have h1 : Real.exp (Log z).re = ‖h z / h s₀‖ := by
      rw [← Complex.norm_exp, hLog_exp z hz]
    have h2 : ‖h z / h s₀‖ ≤ M := by
      rw [norm_div, div_le_iff₀ hh0_pos]
      have hhz : ‖h z‖ ≤ M * ‖g s₀‖ :=
        hh_M z (Metric.closedBall_subset_closedBall hrR.le (Metric.ball_subset_closedBall hz))
      have hM0 : 0 ≤ M := by linarith
      exact hhz.trans (mul_le_mul_of_nonneg_left hh0_ge hM0)
    have h3 : (Log z).re = Real.log ‖h z / h s₀‖ := by
      rw [← h1, Real.log_exp]
    rw [h3]
    have hpos : 0 < ‖h z / h s₀‖ := by
      rw [norm_div]
      exact div_pos (norm_pos_iff.mpr (hh_nz z (Metric.ball_subset_closedBall hz))) hh0_pos
    exact Real.log_le_log hpos h2
  have hbc_h : ‖deriv h s₀ / h s₀‖ ≤ (2 / r) * Real.log M := by
    have h1 := borelCaratheodory_deriv_at_center hr hLog_diff hLog_re
    rw [(hLog_d s₀ (Metric.mem_ball_self hr)).deriv, hLog0, Complex.zero_re, sub_zero] at h1
    exact h1
  -- Log-derivative identity for `g = h * ∏ B_ρ` at `s₀`
  have hB_nz : ∀ ρ ∈ L, blaschkeFactor s₀ R ρ s₀ ≠ 0 := by
    intro ρ hρ
    rw [blaschkeFactor_eval_center hR]
    exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (hL ρ hρ).2.1))
      (Complex.ofReal_ne_zero.mpr hR.ne')
  have hP_d := hasDerivAt_logDeriv_list_prod (s₀ := s₀) (L := L)
    (F := fun ρ z => blaschkeFactor s₀ R ρ z)
    (F' := fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀)
    (fun ρ _ => (blaschkeFactor_hasDerivAt_center hR).congr_deriv
      (blaschkeFactor_hasDerivAt_center hR).deriv.symm)
    hB_nz
  have hh_at : HasDerivAt h (deriv h s₀) s₀ :=
    (hh_an s₀ (Metric.mem_closedBall_self hR.le)).differentiableAt.hasDerivAt
  have hmul_d := hh_at.fun_mul hP_d
  have hEq_nhds : g =ᶠ[𝓝 s₀] fun z => h z * (L.map (fun ρ => blaschkeFactor s₀ R ρ z)).prod := by
    filter_upwards [Metric.closedBall_mem_nhds s₀ hR] with z hz
    exact hh_eq z hz
  have hg_d : deriv g s₀ =
      deriv h s₀ * (L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod +
      h s₀ * ((L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod *
        (L.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum) := by
    rw [hEq_nhds.deriv_eq, hmul_d.deriv]
  have hP_ne : (L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod ≠ 0 :=
    List.prod_ne_zero (by
      intro hmem
      obtain ⟨ρ, hρL, h0⟩ := List.mem_map.mp hmem
      exact hB_nz ρ hρL h0)
  have hlogd : deriv g s₀ / g s₀ =
      deriv h s₀ / h s₀ +
        (L.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum := by
    rw [hg_d, hh_eq s₀ (Metric.mem_closedBall_self hR.le)]
    field_simp [hh0_ne, hP_ne]
  have hre_sum :
      ((L.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum).re =
      (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
    have hmap_re : ∀ (l : List ℂ), (∀ ρ ∈ l, ρ ≠ s₀) →
        ((l.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum).re =
        (l.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a t ih =>
        intro hl
        simp only [List.map_cons, List.sum_cons, Complex.add_re]
        rw [blaschkeFactor_logDeriv_center_re hR (hl a (List.mem_cons_self ..)),
          ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ))]
    exact hmap_re L (fun ρ hρ => (hL ρ hρ).2.1)
  have hneg_le : (-(deriv h s₀ / h s₀)).re ≤ (2 / r) * Real.log M := by
    rw [Complex.neg_re]
    have h1 := (abs_le.mp (Complex.abs_re_le_norm (deriv h s₀ / h s₀))).1
    linarith
  refine ⟨L, hL, hL_cov, ?_⟩
  have hneg_eq : -deriv g s₀ / g s₀ = -(deriv g s₀ / g s₀) := by ring
  rw [hneg_eq, hlogd, neg_add, Complex.add_re, Complex.neg_re, Complex.neg_re, hre_sum]
  rw [Complex.neg_re] at hneg_le
  linarith

/-- **Landau's Local Log-Derivative Bound (No-Zero Form)**:
under the hypotheses of `landau_negLogDeriv_full`, if every zero `ρ` of `g` in `closedBall s₀ r`
satisfies `ρ.re ≤ s₀.re`, then `(-deriv g s₀ / g s₀).re ≤ (2 / r) * Real.log M`. -/
theorem landau_negLogDeriv_le {g : ℂ → ℂ} {s₀ : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖)
    (hzeros : ∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ.re ≤ s₀.re) :
    (-deriv g s₀ / g s₀).re ≤ (2 / r) * Real.log M := by
  have hR : 0 < R := lt_trans hr hrR
  obtain ⟨L, hL, _, hle⟩ := landau_negLogDeriv_full hr hrR hM hg hg0 hbd
  have hsum_nonneg :
      0 ≤ (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
    refine List.sum_nonneg ?_
    intro x hx
    obtain ⟨ρ, hρL, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hρ_mem, hρ_ne, hρ_zero⟩ := hL ρ hρL
    have hρR : ‖ρ - s₀‖ < R := lt_of_le_of_lt
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem) hrR
    rw [← blaschkeFactor_logDeriv_center_re hR hρ_ne]
    exact blaschkeFactor_logDeriv_center_re_nonneg hR hρ_ne hρR (hzeros ρ hρ_mem hρ_zero)
  linarith

/-- **Landau's Local Log-Derivative Bound (Single Distinguished Zero Form)**:
under the same hypotheses, for any zero `ρ₀ ∈ closedBall s₀ r` of `g`:
`(-deriv g s₀ / g s₀).re ≤ (2 / r) * Real.log M + (s₀ - ρ₀).re / R^2 - (1 / (s₀ - ρ₀)).re`. -/
theorem landau_negLogDeriv_le_one_zero {g : ℂ → ℂ} {s₀ ρ₀ : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖)
    (hzeros : ∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ.re ≤ s₀.re)
    (hρ₀_mem : ρ₀ ∈ Metric.closedBall s₀ r) (hρ₀_zero : g ρ₀ = 0) :
    (-deriv g s₀ / g s₀).re ≤
      (2 / r) * Real.log M + (s₀ - ρ₀).re / R ^ 2 - (1 / (s₀ - ρ₀)).re := by
  have hR : 0 < R := lt_trans hr hrR
  obtain ⟨L, hL, hL_cov, hle⟩ := landau_negLogDeriv_full hr hrR hM hg hg0 hbd
  have hρ₀L : ρ₀ ∈ L := hL_cov ρ₀ hρ₀_mem hρ₀_zero
  set φ : ℂ → ℝ := fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2)
  have hφ_nonneg : ∀ ρ ∈ L, 0 ≤ φ ρ := by
    intro ρ hρL
    obtain ⟨hρ_mem, hρ_ne, hρ_zero⟩ := hL ρ hρL
    have hρR : ‖ρ - s₀‖ < R := lt_of_le_of_lt
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem) hrR
    dsimp only [φ]
    rw [← blaschkeFactor_logDeriv_center_re hR hρ_ne]
    exact blaschkeFactor_logDeriv_center_re_nonneg hR hρ_ne hρR (hzeros ρ hρ_mem hρ_zero)
  have hterm_le : φ ρ₀ ≤ (L.map φ).sum := by
    have haux : ∀ (l : List ℂ), (∀ ρ ∈ l, 0 ≤ φ ρ) → ρ₀ ∈ l → φ ρ₀ ≤ (l.map φ).sum := by
      intro l
      induction l with
      | nil => intro _ h; simp at h
      | cons a t ih =>
        intro hl hmem
        simp only [List.map_cons, List.sum_cons]
        rcases List.mem_cons.mp hmem with rfl | ht
        · have ht_nn : 0 ≤ (t.map φ).sum := List.sum_nonneg fun x hx => by
            obtain ⟨ρ, hρt, rfl⟩ := List.mem_map.mp hx
            exact hl ρ (List.mem_cons_of_mem _ hρt)
          linarith
        · have ha_nn : 0 ≤ φ a := hl a (List.mem_cons_self ..)
          have hih := ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ)) ht
          linarith
    exact haux L hφ_nonneg hρ₀L
  have hφ_eq : φ ρ₀ = (1 / (s₀ - ρ₀)).re - (s₀ - ρ₀).re / R ^ 2 := by
    dsimp only [φ]
    have hre1 : (1 / (s₀ - ρ₀)).re = (s₀ - ρ₀).re / ‖s₀ - ρ₀‖ ^ 2 := by
      rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    rw [hre1]
    ring
  linarith

/-- **Landau's Local Log-Derivative Bound (Half-Radius Finite Zero-Subset Form)**:
for `r = R / 2` and any finite set `S : Finset ℂ` of zeros of `g` in `closedBall s₀ (R / 2)`:
`(-deriv g s₀ / g s₀).re ≤ (4 / R) * Real.log M - (3 / 4) * ∑ ρ ∈ S, (1 / (s₀ - ρ)).re`. -/
theorem landau_negLogDeriv_le_finset_zeros {g : ℂ → ℂ} {s₀ : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖)
    (hzeros : ∀ ρ ∈ Metric.closedBall s₀ (R / 2), g ρ = 0 → ρ.re ≤ s₀.re)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ Metric.closedBall s₀ (R / 2) ∧ g ρ = 0) :
    (-deriv g s₀ / g s₀).re ≤
      (4 / R) * Real.log M - (3 / 4) * ∑ ρ ∈ S, (1 / (s₀ - ρ)).re := by
  have hr : 0 < R / 2 := half_pos hR
  have hrR : R / 2 < R := half_lt_self hR
  obtain ⟨L, hL, hL_cov, hle⟩ := landau_negLogDeriv_full hr hrR hM hg hg0 hbd
  set φ : ℂ → ℝ := fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2)
  have hφ_nonneg : ∀ ρ ∈ L, 0 ≤ φ ρ := by
    intro ρ hρL
    obtain ⟨hρ_mem, hρ_ne, hρ_zero⟩ := hL ρ hρL
    have hρR : ‖ρ - s₀‖ < R := lt_of_le_of_lt
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem) hrR
    dsimp only [φ]
    rw [← blaschkeFactor_logDeriv_center_re hR hρ_ne]
    exact blaschkeFactor_logDeriv_center_re_nonneg hR hρ_ne hρR (hzeros ρ hρ_mem hρ_zero)
  -- `∑ ρ ∈ S, φ ρ ≤ (L.map φ).sum` since `S ⊆ L.toFinset` and `φ ≥ 0` on `L`
  have hsum_ge : ∑ ρ ∈ S, φ ρ ≤ (L.map φ).sum := by
    have hdedup : ∑ ρ ∈ L.toFinset, φ ρ ≤ (L.map φ).sum := by
      have haux : ∀ (l : List ℂ), (∀ ρ ∈ l, 0 ≤ φ ρ) →
          ∑ ρ ∈ l.toFinset, φ ρ ≤ (l.map φ).sum := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons a t ih =>
          intro hl
          simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
          have hih := ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ))
          have ha_nn : 0 ≤ φ a := hl a (List.mem_cons_self ..)
          by_cases ha : a ∈ t.toFinset
          · rw [Finset.insert_eq_of_mem ha]; linarith
          · rw [Finset.sum_insert ha]; linarith
      exact haux L hφ_nonneg
    have hsub : S ⊆ L.toFinset := fun ρ hρ =>
      List.mem_toFinset.mpr (hL_cov ρ (hS ρ hρ).1 (hS ρ hρ).2)
    have hle_sub : ∑ ρ ∈ S, φ ρ ≤ ∑ ρ ∈ L.toFinset, φ ρ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun ρ hρ _ =>
        hφ_nonneg ρ (List.mem_toFinset.mp hρ)
    exact hle_sub.trans hdedup
  -- Pointwise lower bound `φ ρ ≥ (3 / 4) * (1 / (s₀ - ρ)).re` for `‖ρ - s₀‖ ≤ R / 2`
  have hpw : (3 / 4) * ∑ ρ ∈ S, (1 / (s₀ - ρ)).re ≤ ∑ ρ ∈ S, φ ρ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    obtain ⟨hρ_mem, hρ_zero⟩ := hS ρ hρ
    have hρ_ne : ρ ≠ s₀ := fun h => hg0 (h ▸ hρ_zero)
    have hnorm : ‖s₀ - ρ‖ ≤ R / 2 := by
      rw [norm_sub_rev]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem
    have hpos : 0 < ‖s₀ - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρ_ne.symm)
    have hsq : 4 * ‖s₀ - ρ‖ ^ 2 ≤ R ^ 2 := by nlinarith
    have h1 : 3 / 4 * (1 / ‖s₀ - ρ‖ ^ 2) ≤ 1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2 := by
      have hinv : 1 / R ^ 2 ≤ 1 / (4 * ‖s₀ - ρ‖ ^ 2) := by
        rw [one_div, one_div]
        exact inv_anti₀ (by positivity) hsq
      have h4 : 1 / (4 * ‖s₀ - ρ‖ ^ 2) = 1 / 4 * (1 / ‖s₀ - ρ‖ ^ 2) := by ring
      linarith
    have hre_nn : 0 ≤ (s₀ - ρ).re := by simp [hzeros ρ hρ_mem hρ_zero]
    have h2 := mul_le_mul_of_nonneg_left h1 hre_nn
    dsimp only [φ]
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    linarith [show (s₀ - ρ).re * (3 / 4 * (1 / ‖s₀ - ρ‖ ^ 2)) =
        3 / 4 * ((s₀ - ρ).re / ‖s₀ - ρ‖ ^ 2) by ring]
  have h4R : 2 / (R / 2) = 4 / R := by ring
  rw [h4R] at hle
  linarith

/-! ## Section 3: Exact Euler–Maclaurin Continuation & Concrete Bounds on `riemannZeta` and `LFunction` -/

/-- Natural fractional part `{t} = t - ⌊t⌋₊` on `ℝ` (lies in `[0, 1)` for `t ≥ 0`). -/
def fractNat (t : ℝ) : ℝ := t - (⌊t⌋₊ : ℝ)

lemma fractNat_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ fractNat t :=
  sub_nonneg.mpr (Nat.floor_le ht)

lemma fractNat_lt_one (t : ℝ) : fractNat t < 1 := by
  unfold fractNat
  linarith [Nat.lt_floor_add_one t]

lemma norm_fractNat_le_one {t : ℝ} (ht : 0 ≤ t) : ‖((fractNat t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (fractNat_nonneg ht)]
  exact (fractNat_lt_one t).le

lemma measurable_fractNat : Measurable fractNat :=
  measurable_id.sub (measurable_from_top.comp Nat.measurable_floor)

private lemma stepSum_const_one (t : ℝ) :
    Stage3RealAnalyticLandau.stepSum (fun _ : ℕ => (1 : ℂ)) t = (⌊t⌋₊ : ℂ) := by
  unfold Stage3RealAnalyticLandau.stepSum
  simp

private lemma isPreconnected_re_pos_sdiff_one :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) := by
  -- Show path-connectedness by joining every point in `U` to `(2 : ℂ)` inside `U`.
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {(1 : ℂ)}
  have h2U : (2 : ℂ) ∈ U := by
    refine ⟨by norm_num, ?_⟩
    intro h; have := congrArg Complex.re h; norm_num at this
  have hseg : ∀ a b : ℂ, a ∈ U → b ∈ U →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - (t : ℂ)) * a + (t : ℂ) * b ∈ U) →
      JoinedIn U a b := by
    intro a b ha hb hmem
    refine ⟨{
      toFun := fun t => (1 - ((t : ℝ) : ℂ)) * a + ((t : ℝ) : ℂ) * b
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp
    }, fun t => hmem t t.2⟩
  have hjoin2 : ∀ z ∈ U, JoinedIn U z (2 : ℂ) := by
    intro z hz
    have hz_re : 0 < z.re := hz.1
    have hz_ne : z ≠ 1 := hz.2
    by_cases him : z.im = 0
    · by_cases hgt : 1 < z.re
      · refine hseg z 2 hz h2U fun t ht => ?_
        have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re = (1 - t) * z.re + 2 * t := by
          simp [Complex.mul_re]; ring
        refine ⟨show 0 < ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re by rw [hre]; nlinarith [ht.1, ht.2], ?_⟩
        intro h1
        have h1' : ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re = 1 := by
          rw [Set.mem_singleton_iff] at h1; rw [h1, Complex.one_re]
        rw [hre] at h1'
        have hnn : 0 ≤ (1 - t) * (z.re - 1) := mul_nonneg (by linarith [ht.2]) (by linarith)
        rcases eq_or_lt_of_le ht.1 with rfl | ht0
        · linarith
        · nlinarith
      · -- `0 < z.re < 1` and `z.im = 0`: go `z → z + I → 2 + I → 2`
        have hlt : z.re < 1 := lt_of_le_of_ne (le_of_not_gt hgt) fun heq =>
          hz_ne (Complex.ext heq (by simpa using him))
        have hzI : z + I ∈ U := by
          refine ⟨by simpa using hz_re, ?_⟩
          intro h1; have := congrArg Complex.im h1; simp [him] at this
        have h2I : (2 : ℂ) + I ∈ U := by
          refine ⟨by norm_num, ?_⟩
          intro h1; have := congrArg Complex.im h1; simp at this
        have h1 : JoinedIn U z (z + I) := hseg z (z + I) hz hzI fun t ht => by
          have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * (z + I)).re = z.re := by
            simp [Complex.mul_re]; ring
          refine ⟨show 0 < ((1 - (t : ℂ)) * z + (t : ℂ) * (z + I)).re by rw [hre]; exact hz_re, ?_⟩
          intro h1; rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; linarith
        have h2 : JoinedIn U (z + I) (2 + I) := hseg (z + I) (2 + I) hzI h2I fun t ht => by
          have hre : ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).re = (1 - t) * z.re + 2 * t := by
            simp [Complex.mul_re]; ring
          have him' : ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).im = 1 := by
            simp [Complex.mul_im, him]
          refine ⟨show 0 < ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).re by
            rw [hre]; nlinarith [ht.1, ht.2], ?_⟩
          intro h1; rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.im h1; rw [him', Complex.one_im] at this; norm_num at this
        have h3 : JoinedIn U (2 + I) 2 := hseg (2 + I) 2 h2I h2U fun t ht => by
          have hre : ((1 - (t : ℂ)) * (2 + I) + (t : ℂ) * 2).re = 2 := by
            simp [Complex.mul_re]; ring
          refine ⟨show 0 < ((1 - (t : ℂ)) * (2 + I) + (t : ℂ) * 2).re by rw [hre]; norm_num, ?_⟩
          intro h1; rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; norm_num at this
        exact (h1.trans h2).trans h3
    · -- `z.im ≠ 0`: go `z → 2 + I * z.im → 2`
      set w : ℂ := (2 : ℂ) + I * (z.im : ℂ)
      have hw : w ∈ U := by
        refine ⟨by simp [w], ?_⟩
        intro h1; have := congrArg Complex.re h1; simp [w] at this
      have h1 : JoinedIn U z w := hseg z w hz hw fun t ht => by
        have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * w).re = (1 - t) * z.re + 2 * t := by
          simp [w, Complex.mul_re]; ring
        have him' : ((1 - (t : ℂ)) * z + (t : ℂ) * w).im = z.im := by
          simp [w, Complex.mul_im]; ring
        refine ⟨show 0 < ((1 - (t : ℂ)) * z + (t : ℂ) * w).re by
          rw [hre]; rcases eq_or_lt_of_le ht.1 with rfl | ht0 <;> nlinarith [ht.1, ht.2], ?_⟩
        intro h1; rw [Set.mem_singleton_iff] at h1
        have := congrArg Complex.im h1; rw [him', Complex.one_im] at this; exact him this
      have h2 : JoinedIn U w 2 := hseg w 2 hw h2U fun t ht => by
        have hre : ((1 - (t : ℂ)) * w + (t : ℂ) * 2).re = 2 := by
          simp [w, Complex.mul_re]; ring
        refine ⟨show 0 < ((1 - (t : ℂ)) * w + (t : ℂ) * 2).re by rw [hre]; norm_num, ?_⟩
        intro h1; rw [Set.mem_singleton_iff] at h1
        have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; norm_num at this
      exact h1.trans h2
  have hpc : IsPathConnected U := ⟨2, h2U, fun z hz => (hjoin2 z hz).symm⟩
  exact hpc.isConnected.isPreconnected

/-- **Exact First-Order Euler–Maclaurin Formula for Mathlib's `riemannZeta`** on `Re(s) > 0`, `s ≠ 1`:
`riemannZeta s - 1 / (s - 1) = 1 - s * ∫_1^∞ (t - ⌊t⌋₊) * t ^ (-s - 1) dt`. -/
theorem riemannZeta_sub_pole_eq_eulerMaclaurin {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s - 1 / (s - 1) =
      1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} \ {(1 : ℂ)}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hLHS_an : AnalyticOnNhd ℂ (fun z : ℂ => riemannZeta z - 1 / (z - 1)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    have hz1 : z ≠ 1 := hz.2
    exact ((differentiableAt_riemannZeta hz1).sub
      ((differentiableAt_const (1 : ℂ)).div ((differentiableAt_id).sub (differentiableAt_const 1))
        (sub_ne_zero.mpr hz1))).differentiableWithinAt
  have hE_meas : Measurable (fun t : ℝ => -((fractNat t : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp measurable_fractNat).neg
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖-((fractNat t : ℝ) : ℂ)‖ ≤ 1 * t ^ (0 : ℝ) := by
    intro t ht
    rw [norm_neg, Real.rpow_zero, mul_one]
    exact norm_fractNat_le_one (zero_le_one.trans ht)
  have hRHS_an : AnalyticOnNhd ℂ
      (fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) U := by
    have h1 := Stage3RealAnalyticLandau.analyticOnNhd_mellin_of_rpow_bound hE_meas zero_le_one hE_bd
    have hEq : (fun z : ℂ => 1 + z * ∫ t in Ioi (1 : ℝ), (-((fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
        fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
      funext z
      have hneg : (fun t : ℝ => (-((fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
          fun t : ℝ => -(((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by funext t; ring
      rw [hneg, integral_neg]
      ring
    rw [hEq] at h1
    exact h1.mono (fun z hz => hz.1)
  have hEq_gt1 : ∀ z : ℂ, 1 < z.re →
      riemannZeta z - 1 / (z - 1) =
        1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    intro z hz
    have hL_eq : LSeries (fun _ : ℕ => (1 : ℂ)) z = riemannZeta z := by
      have h1 := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz
      rw [ArithmeticFunction.LSeries_zeta_eq] at h1
      exact h1
    have hsum : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) z := by
      have h1 := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hz
      refine h1.congr fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term]
      · simp [LSeries.term, hn, ArithmeticFunction.zeta_apply]
    have hbd_step : ∀ t : ℝ, 1 ≤ t → ‖Stage3RealAnalyticLandau.stepSum (fun _ : ℕ => (1 : ℂ)) t‖ ≤ 1 * t := by
      intro t ht
      rw [stepSum_const_one, one_mul, Complex.norm_natCast]
      exact Nat.floor_le (zero_le_one.trans ht)
    have hmel := Stage3RealAnalyticLandau.LSeries_sub_pole_eq_mellin_error hbd_step hz hsum
    rw [hL_eq] at hmel
    rw [hmel]
    have hpt : (fun t : ℝ => (Stage3RealAnalyticLandau.stepSum (fun _ : ℕ => (1 : ℂ)) t - (t : ℂ)) *
          (t : ℂ) ^ (-z - 1)) =
        fun t : ℝ => -(((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
      funext t
      rw [stepSum_const_one]
      unfold fractNat
      push_cast
      ring
    rw [hpt, integral_neg]
    ring
  have hEv : (fun z : ℂ => riemannZeta z - 1 / (z - 1)) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact hEq_gt1 z hz
  have h2U : (2 : ℂ) ∈ U := ⟨by norm_num, fun h => by
    have := congrArg Complex.re h; norm_num at this⟩
  exact hLHS_an.eqOn_of_preconnected_of_eventuallyEq hRHS_an isPreconnected_re_pos_sdiff_one
    h2U hEv ⟨hs, hs1⟩

/-- **Exact Truncated Euler–Maclaurin Formula for Mathlib's `riemannZeta`** on `Re(s) > 0`, `s ≠ 1`:
for every `N : ℕ` with `1 ≤ N`,
`riemannZeta s = ∑_{n=1}^N n ^ (-s) + N ^ (1 - s) / (s - 1) - s * ∫_N^∞ (t - ⌊t⌋₊) * t ^ (-s - 1) dt`. -/
theorem riemannZeta_eq_eulerMaclaurin_trunc {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) -
        s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  have hN0 : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hN1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs hs1
  -- Split `∫_{Ioi 1}` into `∫_1^N + ∫_{Ioi N}`
  have hint_full : IntegrableOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
    Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
      (Complex.measurable_ofReal.comp measurable_fractNat)
      (fun t ht => by simpa [Real.rpow_zero] using norm_fractNat_le_one (zero_le_one.trans ht)) hs
  have hint_N : IntegrableOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) :=
    hint_full.mono_set (Ioi_subset_Ioi hN1)
  have hint_Ioc : IntegrableOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      (Ioc (1 : ℝ) (N : ℝ)) :=
    hint_full.mono_set Ioc_subset_Ioi_self
  have hsplit_set : Ioi (1 : ℝ) = Ioc (1 : ℝ) (N : ℝ) ∪ Ioi (N : ℝ) :=
    (Ioc_union_Ioi_eq_Ioi hN1).symm
  have hdisj : Disjoint (Ioc (1 : ℝ) (N : ℝ)) (Ioi (N : ℝ)) := Ioc_disjoint_Ioi_same
  have hsplit_int :
      ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) =
        (∫ t in (1 : ℝ)..(N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) +
        (∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) := by
    rw [hsplit_set, setIntegral_union hdisj measurableSet_Ioi hint_Ioc hint_N,
      intervalIntegral.integral_of_le hN1]
  -- Evaluate `∑_{n=1}^N n^(-s)` via `abel_summation_dirichlet`
  have hab := Stage3RealAnalyticLandau.abel_summation_dirichlet (fun _ : ℕ => (1 : ℂ)) hN1 s
  simp only [Nat.floor_natCast, one_mul, stepSum_const_one] at hab
  -- Evaluate `∫_1^N t * t^(-s-1) dt = ∫_1^N t^(-s) dt = (N^(1-s) - 1) / (1 - s)`
  have hpow_int : ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) * (t : ℂ) ^ (-s - 1) =
      ((N : ℂ) ^ (1 - s) - 1) / (1 - s) := by
    have h1s_ne : 1 - s ≠ 0 := fun h => hs1 (sub_eq_zero.mp h).symm
    have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) (N : ℝ),
        HasDerivAt (fun u : ℝ => (u : ℂ) ^ (1 - s) / (1 - s)) ((t : ℂ) * (t : ℂ) ^ (-s - 1)) t := by
      intro t ht
      rw [Set.uIcc_of_le hN1] at ht
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht.1
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have hfun : (fun u : ℝ => (u : ℂ) ^ (1 - s)) =ᶠ[𝓝 t]
          fun u : ℝ => cexp ((Real.log u : ℂ) * (1 - s)) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht0] with u hu
        have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
        rw [Complex.cpow_def_of_ne_zero huC, Complex.ofReal_log hu.le]
      have h1 : HasDerivAt (fun u : ℝ => cexp ((Real.log u : ℂ) * (1 - s)))
          (cexp ((Real.log t : ℂ) * (1 - s)) * (((t⁻¹ : ℝ) : ℂ) * (1 - s))) t :=
        (((Real.hasDerivAt_log ht0.ne').ofReal_comp).mul_const (1 - s)).cexp
      have h2 := ((h1.congr_of_eventuallyEq hfun).div_const (1 - s))
      refine h2.congr_deriv ?_
      have hcp : cexp ((Real.log t : ℂ) * (1 - s)) = (t : ℂ) ^ (1 - s) := by
        rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
      rw [hcp]
      have hpow1 : (t : ℂ) ^ (1 - s) = (t : ℂ) * (t : ℂ) ^ (-s) := by
        rw [show (1 - s : ℂ) = 1 + (-s) by ring, Complex.cpow_add _ _ htC, Complex.cpow_one]
      have hpow2 : (t : ℂ) ^ (-s - 1) = (t : ℂ) ^ (-s) / (t : ℂ) := by
        rw [Complex.cpow_sub _ _ htC, Complex.cpow_one]
      rw [hpow1, hpow2]
      push_cast; field_simp [htC, h1s_ne]
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.uIcc (1 : ℝ) (N : ℝ)) := by
      rw [Set.uIcc_of_le hN1]
      refine Complex.continuous_ofReal.continuousOn.mul ?_
      have hce : ContinuousOn (fun t : ℝ => cexp ((Real.log t : ℂ) * (-s - 1))) (Set.Icc (1 : ℝ) (N : ℝ)) :=
        ContinuousOn.cexp ((Complex.continuous_ofReal.comp_continuousOn
          (Real.continuousOn_log.mono fun t ht => (zero_lt_one.trans_le ht.1).ne')).mul continuousOn_const)
      refine hce.congr fun t ht => ?_
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht.1
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      dsimp only
      rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht0.le]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    simp only [Complex.ofReal_natCast, Complex.ofReal_one, Complex.one_cpow] at h
    rw [h]; ring
  have hint_t : IntervalIntegrable (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) := by
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1)) (Set.uIcc (1 : ℝ) (N : ℝ)) := by
      rw [Set.uIcc_of_le hN1]
      refine Complex.continuous_ofReal.continuousOn.mul ?_
      have hce : ContinuousOn (fun t : ℝ => cexp ((Real.log t : ℂ) * (-s - 1))) (Set.Icc (1 : ℝ) (N : ℝ)) :=
        ContinuousOn.cexp ((Complex.continuous_ofReal.comp_continuousOn
          (Real.continuousOn_log.mono fun t ht => (zero_lt_one.trans_le ht.1).ne')).mul continuousOn_const)
      refine hce.congr fun t ht => ?_
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht.1
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      dsimp only
      rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht0.le]
    exact hcont.intervalIntegrable
  have hint_fr_iv : IntervalIntegrable (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
      volume (1 : ℝ) (N : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hN1).mpr hint_Ioc
  have hfloor_int :
      ∫ t in (1 : ℝ)..(N : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-s - 1) =
        ((N : ℂ) ^ (1 - s) - 1) / (1 - s) -
          ∫ t in (1 : ℝ)..(N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    have hpt : (fun t : ℝ => (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-s - 1)) =
        fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1) - ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
      funext t; unfold fractNat; push_cast; ring
    rw [hpt, intervalIntegral.integral_sub hint_t hint_fr_iv, hpow_int]
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNpow : (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 - s) := by
    rw [show (1 - s : ℂ) = 1 + (-s) by ring, Complex.cpow_add _ _ hNC, Complex.cpow_one]
  have h1s_ne : 1 - s ≠ 0 := fun h => hs1 (sub_eq_zero.mp h).symm
  rw [Complex.ofReal_natCast, hfloor_int, hNpow] at hab
  rw [hsplit_int] at hem
  -- Now combine `hem` and `hab` purely algebraically!
  have halg : (N : ℂ) ^ (1 - s) + s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) =
      1 + 1 / (s - 1) - (N : ℂ) ^ (1 - s) / (s - 1) := by
    field_simp [hs1', h1s_ne]
    ring
  calc riemannZeta s
      = 1 / (s - 1) + 1 - s * ((∫ t in (1 : ℝ)..(N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) +
          (∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))) := by
        linear_combination hem
    _ = ((N : ℂ) ^ (1 - s) + s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) -
          s * ∫ t in (1 : ℝ)..(N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) +
          (N : ℂ) ^ (1 - s) / (s - 1) -
          s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
        rw [halg]; ring
    _ = (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) -
          s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
        rw [hab]; ring

/-- Bound on the Euler–Maclaurin tail integral `‖∫_a^∞ {t} t^(-s-1) dt‖ ≤ a^(-s.re) / s.re`
for all `a ≥ 1` and `s.re > 0`. -/
lemma norm_eulerMaclaurin_tail_le {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Ioi a, ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re) / s.re := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hre : -s.re - 1 < -1 := by linarith
  have hint_dom : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt hre ha0
  have hint_val : ∫ t in Ioi a, t ^ (-s.re - 1) = a ^ (-s.re) / s.re := by
    rw [integral_Ioi_rpow_of_lt hre ha0]
    have h1 : -s.re - 1 + 1 = -s.re := by ring
    rw [h1]; field_simp [hs.ne']
  calc ‖∫ t in Ioi a, ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖
      ≤ ∫ t in Ioi a, ‖((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi a, t ^ (-s.re - 1) := by
        refine setIntegral_mono_on ?_ hint_dom measurableSet_Ioi fun t ht => ?_
        · have hint_full : IntegrableOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
            Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
              (Complex.measurable_ofReal.comp measurable_fractNat)
              (fun u hu => by simpa [Real.rpow_zero] using norm_fractNat_le_one (zero_le_one.trans hu)) hs
          exact (hint_full.mono_set (Ioi_subset_Ioi ha)).norm
        · have ht0 : 0 < t := ha0.trans ht
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          have hre' : (-s - 1).re = -s.re - 1 := by simp
          rw [hre']
          exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (norm_fractNat_le_one ht0.le)
    _ = a ^ (-s.re) / s.re := hint_val

/-- **Unconditional Pointwise Growth Bound for `riemannZeta` on `Re(s) > 0`**:
for every `s : ℂ` with `0 < s.re` and `s ≠ 1`,
`‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re`. -/
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re := by
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs hs1
  have hzeta : riemannZeta s =
      1 / (s - 1) + 1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    linear_combination hem
  have htail := norm_eulerMaclaurin_tail_le le_rfl hs
  rw [Real.one_rpow] at htail
  rw [hzeta]
  calc ‖1 / (s - 1) + 1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖1 / (s - 1) + 1‖ + ‖s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ :=
        norm_sub_le _ _
    _ ≤ (‖1 / (s - 1)‖ + ‖(1 : ℂ)‖) + ‖s‖ * ‖∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ := by
        rw [norm_mul]; gcongr; exact norm_add_le _ _
    _ ≤ (1 / ‖s - 1‖ + 1) + ‖s‖ * (1 / s.re) := by
        rw [norm_div, norm_one]; gcongr
    _ = 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re := by ring

/-- **Unconditional Concrete Vertical-Strip Polynomial Bound on Mathlib's `riemannZeta`**:
for every `s : ℂ` with `1 / 2 ≤ s.re ≤ 2` and `1 ≤ |s.im|`,
`‖riemannZeta s‖ ≤ 3 * (|s.im| + 2)`. -/
theorem norm_riemannZeta_strip_le {s : ℂ} (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 2)
    (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 3 * (|s.im| + 2) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h, Complex.one_im, abs_zero] at him; linarith
  have hbd := norm_riemannZeta_le_of_re_pos hs0 hs1
  have hsub_ge : 1 ≤ ‖s - 1‖ := by
    have h1 := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h1
    linarith
  have hinv_le : 1 / ‖s - 1‖ ≤ 1 := (div_le_one (by linarith)).mpr hsub_ge
  have hnorm_s : ‖s‖ ≤ |s.im| + 2 := by
    have h1 := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at h1
    linarith
  have hdiv_le : ‖s‖ / s.re ≤ 2 * (|s.im| + 2) := by
    rw [div_le_iff₀ hs0]
    nlinarith [abs_nonneg s.im]
  linarith

/-- Elementary harmonic partial sum bound `∑_{n=1}^N (n : ℝ)⁻¹ ≤ 1 + Real.log N` for `1 ≤ N`. -/
private lemma harmonic_sum_le_one_add_log {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹) ≤ 1 + Real.log (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp : m + 1 ∉ Finset.Icc 1 m)]
    have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    -- `1 / (m + 1) ≤ log((m + 1) / m) = log(m + 1) - log m`
    -- Since `log(1 - 1/(m+1)) ≤ -1/(m+1)` i.e. `log(m / (m+1)) ≤ -1/(m+1)`!
    have hstep : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      have h1 : Real.log ((m : ℝ) / ((m : ℝ) + 1)) ≤ (m : ℝ) / ((m : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hm0 hm1)
      rw [Real.log_div hm0.ne' hm1.ne'] at h1
      have h2 : (m : ℝ) / ((m : ℝ) + 1) - 1 = -((m : ℝ) + 1)⁻¹ := by
        field_simp [hm1.ne']; ring
      rw [h2] at h1
      push_cast
      linarith
    linarith

/-- **Sharp Truncated Euler–Maclaurin Bound in the Critical Strip**:
for `2 ≤ |t|` and `1 / 4 ≤ σ ≤ 1`,
`‖riemannZeta (σ + I * t)‖ ≤ 12 * (|t| + 2) ^ (1 - σ) * Real.log (|t| + 2)`. -/
theorem norm_riemannZeta_critical_strip_sharp {σ t : ℝ} (hlo : 1 / 4 ≤ σ) (hhi : σ ≤ 1)
    (ht : 2 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ 12 * (|t| + 2) ^ (1 - σ) * Real.log (|t| + 2) := by
  set s : ℂ := (σ : ℂ) + I * (t : ℂ)
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hs_im, Complex.one_im] at this
    rw [this, abs_zero] at ht; linarith
  set N : ℕ := ⌊|t| + 2⌋₊
  have hN_ge4 : 4 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hN1 : 1 ≤ N := by omega
  have hN_le : (N : ℝ) ≤ |t| + 2 := Nat.floor_le (by linarith [abs_nonneg t])
  have hN_gt : |t| + 1 < (N : ℝ) := by linarith [Nat.lt_floor_add_one (|t| + 2)]
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith [abs_nonneg t]
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
  have h1σ : 0 ≤ 1 - σ := by linarith
  have ht2_pos : 0 < |t| + 2 := by linarith [abs_nonneg t]
  have hlog_ge1 : (1 : ℝ) ≤ Real.log (|t| + 2) := by
    have h4 : Real.exp 1 ≤ |t| + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) h4)
  have hem := riemannZeta_eq_eulerMaclaurin_trunc hN1 hs0 hs1
  -- Term 1: `‖∑_{n=1}^N n^(-s)‖ ≤ 2 (|t|+2)^(1-σ) log(|t|+2)`
  have hterm1 : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤
      2 * (|t| + 2) ^ (1 - σ) * Real.log (|t| + 2) := by
    have h1 : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤
        ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [Complex.norm_natCast_cpow_of_pos hn1, Complex.neg_re, hs_re]
    have h2 : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) ≤
        (|t| + 2) ^ (1 - σ) * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
      have hn_le : (n : ℝ) ≤ |t| + 2 := le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) hN_le
      have hpow : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (1 - σ) * (n : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]; congr 1; ring
      rw [hpow]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn0.le hn_le h1σ) (inv_nonneg.mpr hn0.le)
    have hharm := harmonic_sum_le_one_add_log hN1
    have hlogN : Real.log (N : ℝ) ≤ Real.log (|t| + 2) := Real.log_le_log hN0 hN_le
    have h3 : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (|t| + 2) := by linarith
    calc ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖
        ≤ (|t| + 2) ^ (1 - σ) * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹) := h1.trans h2
      _ ≤ (|t| + 2) ^ (1 - σ) * (2 * Real.log (|t| + 2)) :=
          mul_le_mul_of_nonneg_left (hharm.trans h3) (Real.rpow_nonneg ht2_pos.le _)
      _ = 2 * (|t| + 2) ^ (1 - σ) * Real.log (|t| + 2) := by ring
  -- Term 2: `‖N^(1-s) / (s - 1)‖ ≤ (|t| + 2)^(1-σ)`
  have hterm2 : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ (|t| + 2) ^ (1 - σ) := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hN1]
    have hre1 : (1 - s).re = 1 - σ := by simp [hs_re]
    rw [hre1]
    have hden : 2 ≤ ‖s - 1‖ := by
      have h1 := Complex.abs_im_le_norm (s - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero, hs_im] at h1
      linarith
    have hnum : (N : ℝ) ^ (1 - σ) ≤ (|t| + 2) ^ (1 - σ) :=
      Real.rpow_le_rpow hN0.le hN_le h1σ
    have h1 : (N : ℝ) ^ (1 - σ) / ‖s - 1‖ ≤ (N : ℝ) ^ (1 - σ) / 1 :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) zero_lt_one (by linarith)
    rw [div_one] at h1
    exact h1.trans hnum
  -- Term 3: `‖s * ∫_N^∞ {t} t^(-s-1) dt‖ ≤ ‖s‖ * N^(-σ) / σ ≤ 4 * (|t| + 2)^(1-σ)`
  have hterm3 : ‖s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
      4 * (|t| + 2) ^ (1 - σ) := by
    rw [norm_mul]
    have htail := norm_eulerMaclaurin_tail_le hN1R hs0
    rw [hs_re] at htail
    have hnorm_s : ‖s‖ ≤ |t| + 1 := by
      have h1 := Complex.norm_le_abs_re_add_abs_im s
      rw [hs_re, hs_im, abs_of_pos (by linarith : 0 < σ)] at h1
      linarith
    have hNpow : (N : ℝ) ^ (-σ) = (N : ℝ) ^ (1 - σ) / (N : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN0]; congr 1; ring
    have hfrac : ‖s‖ / (N : ℝ) ≤ 1 := (div_le_one hN0).mpr (by linarith)
    have hNle : (N : ℝ) ^ (1 - σ) ≤ (|t| + 2) ^ (1 - σ) :=
      Real.rpow_le_rpow hN0.le hN_le h1σ
    calc ‖s‖ * ‖∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * ((N : ℝ) ^ (-σ) / σ) := mul_le_mul_of_nonneg_left htail (norm_nonneg s)
      _ = (‖s‖ / (N : ℝ)) * ((N : ℝ) ^ (1 - σ) / σ) := by rw [hNpow]; ring
      _ ≤ 1 * ((|t| + 2) ^ (1 - σ) / (1 / 4)) := by
          refine mul_le_mul hfrac ?_ (by positivity) zero_le_one
          exact div_le_div₀ (Real.rpow_nonneg ht2_pos.le _) hNle (by positivity) hlo
      _ = 4 * (|t| + 2) ^ (1 - σ) := by ring
  -- Combine all 3 terms
  rw [hem]
  have htri : ‖(∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) -
      s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
      ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ + ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ +
        ‖s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ :=
    (norm_sub_le ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1))
      (s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))).trans
      (by linarith [norm_add_le (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) ((N : ℂ) ^ (1 - s) / (s - 1))])
  have hrpow_nn : 0 ≤ (|t| + 2) ^ (1 - σ) := Real.rpow_nonneg ht2_pos.le _
  have h5 : 5 * (|t| + 2) ^ (1 - σ) ≤ 5 * (|t| + 2) ^ (1 - σ) * Real.log (|t| + 2) := by
    nlinarith
  linarith

/-- **Sharp Logarithmic Bound near the 1-Line** (`1 - 1 / log(|t| + 2) ≤ σ ≤ 2`, `|t| ≥ 2`):
`‖riemannZeta (σ + I * t)‖ ≤ 36 * Real.log (|t| + 2)`. -/
theorem norm_riemannZeta_near_one_le {σ t : ℝ} (hlo : 1 - 1 / Real.log (|t| + 2) ≤ σ)
    (hhi : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ 36 * Real.log (|t| + 2) := by
  have ht2_pos : 0 < |t| + 2 := by linarith [abs_nonneg t]
  have hlog_ge1 : (1 : ℝ) ≤ Real.log (|t| + 2) := by
    have h4 : Real.exp 1 ≤ |t| + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) h4)
  by_cases hσ1 : σ ≤ 1
  · have hqtr : 1 / 4 ≤ σ := by
      have h4 : (4 : ℝ) ≤ |t| + 2 := by linarith
      have hlog4 : Real.log 4 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) h4
      have h2 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; ring
      have hlog_gt : 4 / 3 < Real.log (|t| + 2) := by linarith [Real.log_two_gt_d9]
      have hinv : 1 / Real.log (|t| + 2) < 3 / 4 := by
        rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
        linarith
      linarith
    have hsharp := norm_riemannZeta_critical_strip_sharp hqtr hσ1 ht
    have hrpow : (|t| + 2) ^ (1 - σ) ≤ 3 := by
      have hexp_le : 1 - σ ≤ 1 / Real.log (|t| + 2) := by linarith
      have h1 : (|t| + 2) ^ (1 - σ) ≤ (|t| + 2) ^ (1 / Real.log (|t| + 2)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hexp_le
      have h2 : (|t| + 2) ^ (1 / Real.log (|t| + 2)) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos ht2_pos, mul_one_div_cancel (by linarith : Real.log (|t| + 2) ≠ 0)]
      rw [h2] at h1
      linarith [Real.exp_one_lt_d9]
    nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ |t| + 2)]
  · -- `1 < σ ≤ 2`: use truncated Euler–Maclaurin with `N = ⌊|t| + 2⌋₊`
    push Not at hσ1
    set s : ℂ := (σ : ℂ) + I * (t : ℂ)
    have hs_re : s.re = σ := by simp [s]
    have hs_im : s.im = t := by simp [s]
    have hs0 : 0 < s.re := by linarith
    have hs1 : s ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hs_re, Complex.one_re] at this; linarith
    set N : ℕ := ⌊|t| + 2⌋₊
    have hN_ge4 : 4 ≤ N := Nat.le_floor (by push_cast; linarith)
    have hN1 : 1 ≤ N := by omega
    have hN_le : (N : ℝ) ≤ |t| + 2 := Nat.floor_le (by linarith [abs_nonneg t])
    have hN_gt : |t| + 1 < (N : ℝ) := by linarith [Nat.lt_floor_add_one (|t| + 2)]
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith [abs_nonneg t]
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
    have hem := riemannZeta_eq_eulerMaclaurin_trunc hN1 hs0 hs1
    have hterm1 : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ 2 * Real.log (|t| + 2) := by
      have h1 : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤
          ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
        rw [Complex.norm_natCast_cpow_of_pos hn1, Complex.neg_re, hs_re, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
      have hharm := harmonic_sum_le_one_add_log hN1
      have hlogN : Real.log (N : ℝ) ≤ Real.log (|t| + 2) := Real.log_le_log hN0 hN_le
      linarith
    have hterm2 : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast_cpow_of_pos hN1]
      have hre1 : (1 - s).re = 1 - σ := by simp [hs_re]
      rw [hre1]
      have hnum : (N : ℝ) ^ (1 - σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1R (by linarith)
      have hden : 2 ≤ ‖s - 1‖ := by
        have h1 := Complex.abs_im_le_norm (s - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero, hs_im] at h1
        linarith
      exact (div_le_one (by linarith)).mpr (by linarith)
    have hterm3 : ‖s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤ 2 := by
      rw [norm_mul]
      have htail := norm_eulerMaclaurin_tail_le hN1R hs0
      rw [hs_re] at htail
      have hnorm_s : ‖s‖ ≤ |t| + 2 := by
        have h1 := Complex.norm_le_abs_re_add_abs_im s
        rw [hs_re, hs_im, abs_of_pos (by linarith : 0 < σ)] at h1
        linarith
      have hNpow : (N : ℝ) ^ (-σ) ≤ (N : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
      have hfrac : ‖s‖ / (N : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hN0]; linarith
      calc ‖s‖ * ‖∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖
          ≤ ‖s‖ * ((N : ℝ) ^ (-σ) / σ) := mul_le_mul_of_nonneg_left htail (norm_nonneg s)
        _ ≤ ‖s‖ * ((N : ℝ)⁻¹ / 1) := by
            gcongr
        _ = ‖s‖ / (N : ℝ) := by ring
        _ ≤ 2 := hfrac
    rw [hem]
    have htri : ‖(∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) -
        s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
        ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ + ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ +
          ‖s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ :=
      (norm_sub_le ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1))
        (s * ∫ t in Ioi (N : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))).trans
        (by linarith [norm_add_le (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) ((N : ℂ) ^ (1 - s) / (s - 1))])
    linarith

/-- Real-axis Euler–Maclaurin sandwich on `σ > 1`:
`riemannZeta (σ : ℂ)` is real and satisfies `1 / (σ - 1) ≤ (riemannZeta σ).re ≤ σ / (σ - 1)`. -/
theorem riemannZeta_real_bounds {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).im = 0 ∧
    1 / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re ∧
    (riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) := by
  have hs0 : 0 < (σ : ℂ).re := by simp; linarith
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs0 hs1
  have hreal_int : ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) =
      (((∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ)) := by
    have hpt : EqOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
        (fun t : ℝ => (((fractNat t * t ^ (-σ - 1) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, ← Complex.ofReal_cpow ht0.le, Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    exact Complex.ofRealCLM.integral_comp_comm (by
      have hre : -σ - 1 < -1 := by linarith
      refine (integrableOn_Ioi_rpow_of_lt hre zero_lt_one).mono'
        ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      change ‖fractNat t * t ^ (-σ - 1)‖ ≤ t ^ (-σ - 1)
      rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le)
  have hzeta_real : riemannZeta (σ : ℂ) =
      (((1 / (σ - 1) + 1 - σ * ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ)) := by
    have h1 : riemannZeta (σ : ℂ) =
        1 / ((σ : ℂ) - 1) + 1 - (σ : ℂ) * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) := by
      linear_combination hem
    rw [h1, hreal_int]
    push_cast; rfl
  have hint_nn : 0 ≤ ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    exact mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _)
  have hint_le : ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) ≤ 1 / σ := by
    have hre : -σ - 1 < -1 := by linarith
    have hint_dom : IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt hre zero_lt_one
    have hint_f : IntegrableOn (fun t : ℝ => fractNat t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
      refine hint_dom.mono' ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      change ‖fractNat t * t ^ (-σ - 1)‖ ≤ t ^ (-σ - 1)
      rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
    have hval : ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) = 1 / σ := by
      rw [integral_Ioi_rpow_of_lt hre zero_lt_one, Real.one_rpow]
      have h1 : -σ - 1 + 1 = -σ := by ring
      rw [h1]; field_simp [(by linarith : σ ≠ 0)]
    rw [← hval]
    refine setIntegral_mono_on hint_f hint_dom measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
  rw [hzeta_real, Complex.ofReal_im, Complex.ofReal_re]
  have hσ_pos : 0 < σ := by linarith
  have hσ1_ne : σ - 1 ≠ 0 := by linarith
  have hupper : 1 / (σ - 1) + 1 = σ / (σ - 1) := by field_simp [hσ1_ne]; ring
  have hmul_le : σ * ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hint_le hσ_pos.le
    rw [mul_one_div_cancel hσ_pos.ne'] at h1
    exact h1
  refine ⟨rfl, ?_, ?_⟩
  · linarith
  · linarith [mul_nonneg hσ_pos.le hint_nn]

/-- Helper: `‖LSeries f (σ + I * t)‖ ≤ (riemannZeta σ).re` whenever `‖f n‖ ≤ 1` for all `n` and `σ > 1`. -/
private lemma norm_LSeries_le_riemannZeta_real {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖LSeries f ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hsσ : 1 < (σ : ℂ).re := by simp [hσ]
  have hsum_z : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
    have h1 := (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hsσ).norm
    refine h1.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, ArithmeticFunction.zeta_apply, if_neg hn, Nat.cast_one,
        norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.ofReal_re, if_neg hn, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  have hsum_f : Summable (fun n : ℕ => ‖LSeries.term f ((σ : ℂ) + I * (t : ℂ)) n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum_z
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + I * (t : ℂ)).re = σ by simp, if_neg hn,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) σ)) (hf n)
  have hzeta_re : (riemannZeta (σ : ℂ)).re = ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsσ]
    unfold LSeries
    have hsumZ := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hsσ
    rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hsumZ]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      simp only [LSeries.term, hn, ↓reduceIte, ArithmeticFunction.zeta_apply, Nat.cast_one,
        Complex.reCLM_apply]
      have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
      rw [hcpow, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re, one_div,
        Real.rpow_neg hn0.le]
  rw [hzeta_re]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsum_f).trans ?_
  refine hsum_f.tsum_le_tsum (fun n => ?_) hsum_z
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      show ((σ : ℂ) + I * (t : ℂ)).re = σ by simp, if_neg hn,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) σ)) (hf n)

private lemma norm_moebius_le_one (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [norm_pow, norm_neg, norm_one, one_pow]
  · simp [ArithmeticFunction.moebius, h]

/-- **Concrete `σ > 1` Bounds on `riemannZeta` and `1 / riemannZeta`**:
for every `σ > 1` and `t : ℝ`:
1. `‖riemannZeta (σ + I * t)‖ ≤ (riemannZeta σ).re ≤ σ / (σ - 1)`,
2. `‖1 / riemannZeta (σ + I * t)‖ ≤ (riemannZeta σ).re ≤ σ / (σ - 1)`. -/
theorem norm_riemannZeta_and_inv_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re ∧
    ‖1 / riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re ∧
    (riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have h1 : ‖riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    refine norm_LSeries_le_riemannZeta_real (fun n => ?_) hσ t
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [ArithmeticFunction.zeta_apply, hn]
  have h2 : ‖1 / riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re := by
    have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hmul
    have hinv : 1 / riemannZeta ((σ : ℂ) + I * (t : ℂ)) =
        LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + I * (t : ℂ)) := by
      have hne : riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re hs.le
      rw [div_eq_iff hne, mul_comm, hmul]
    rw [hinv]
    exact norm_LSeries_le_riemannZeta_real norm_moebius_le_one hσ t
  exact ⟨h1, h2, (riemannZeta_real_bounds hσ).2.2⟩

/-- **Unconditional Real-Axis Pole Bound for `-ζ'(σ) / ζ(σ)` on ALL `σ > 1`**:
`0 ≤ (negLogDerivZeta σ).re ≤ 1 / (σ - 1) + 1` (proved directly by differentiating Euler–Maclaurin
at `σ > 1` and dividing by `ζ(σ) ≥ 1 / (σ - 1)`!). -/
theorem negLogDerivZeta_real_le {σ : ℝ} (hσ : 1 < σ) :
    (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
  have hs0 : 0 < (σ : ℂ).re := by simp; linarith
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hE_meas : Measurable (fun t : ℝ => ((fractNat t : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp measurable_fractNat
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖((fractNat t : ℝ) : ℂ)‖ ≤ 1 * t ^ (0 : ℝ) := by
    intro t ht; simpa [Real.rpow_zero] using norm_fractNat_le_one (zero_le_one.trans ht)
  -- Derivative of Euler–Maclaurin `ζ(s) = 1/(s-1) + 1 - s * I(s)` at `s = σ`
  have hI_d := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound hE_meas zero_le_one hE_bd hs0
  have hEq : riemannZeta =ᶠ[𝓝 (σ : ℂ)] fun z : ℂ =>
      1 / (z - 1) + 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    have hopen : IsOpen ({z : ℂ | 0 < z.re} \ {(1 : ℂ)}) :=
      (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    filter_upwards [hopen.mem_nhds ⟨hs0, hs1⟩] with z hz
    linear_combination riemannZeta_sub_pole_eq_eulerMaclaurin hz.1 hz.2
  have hpole_d : HasDerivAt (fun z : ℂ => 1 / (z - 1)) (-1 / ((σ : ℂ) - 1) ^ 2) (σ : ℂ) := by
    have h1 := ((hasDerivAt_id' (σ : ℂ)).sub_const 1).inv (sub_ne_zero.mpr hs1)
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun z => by simp [one_div])).congr_deriv ?_
    ring
  have hzeta_d : deriv riemannZeta (σ : ℂ) =
      -1 / ((σ : ℂ) - 1) ^ 2 -
        (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)) -
        (σ : ℂ) * (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) *
          (-(Real.log t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))) := by
    rw [hEq.deriv_eq]
    have h1 := (hpole_d.add_const (1 : ℂ)).fun_sub ((hasDerivAt_id' (σ : ℂ)).fun_mul hI_d)
    rw [h1.deriv]
    ring
  -- Take real part of `-deriv riemannZeta σ`
  have hint_real1 : IntegrableOn (fun t : ℝ => fractNat t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
    have hre : -σ - 1 < -1 := by linarith
    refine (integrableOn_Ioi_rpow_of_lt hre zero_lt_one).mono'
      ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
  have hreal1 : (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)).re =
      ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) := by
    have hpt : EqOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
        (fun t : ℝ => (((fractNat t * t ^ (-σ - 1) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, ← Complex.ofReal_cpow ht0.le, Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    have hcomm := Complex.ofRealCLM.integral_comp_comm hint_real1
    simpa [Complex.ofRealCLM_apply] using congrArg Complex.re hcomm
  have hint_real2 : IntegrableOn (fun t : ℝ => -(fractNat t * Real.log t * t ^ (-σ - 1))) (Ioi (1 : ℝ)) := by
    set e : ℝ := (σ - 1) / 2
    have he0 : 0 < e := by dsimp only [e]; linarith
    have hre : e - σ - 1 < -1 := by dsimp only [e]; linarith
    refine ((integrableOn_Ioi_rpow_of_lt hre zero_lt_one).const_mul e⁻¹).mono'
      (((measurable_fractNat.mul Real.measurable_log).mul (measurable_id.pow_const _)).neg.aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    rw [norm_neg, Real.norm_of_nonneg (mul_nonneg (mul_nonneg (fractNat_nonneg ht0.le)
      (Real.log_nonneg ht1.le)) (Real.rpow_nonneg ht0.le _))]
    have hlog : Real.log t ≤ e⁻¹ * t ^ e := by
      have := Real.log_le_rpow_div ht0.le he0
      linarith [show t ^ e / e = e⁻¹ * t ^ e by ring]
    have hcomb : t ^ e * t ^ (-σ - 1) = t ^ (e - σ - 1) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have h1 : fractNat t * Real.log t ≤ 1 * (e⁻¹ * t ^ e) :=
      mul_le_mul (fractNat_lt_one t).le hlog (Real.log_nonneg ht1.le) zero_le_one
    calc fractNat t * Real.log t * t ^ (-σ - 1)
        ≤ (1 * (e⁻¹ * t ^ e)) * t ^ (-σ - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0.le _)
      _ = e⁻¹ * (t ^ e * t ^ (-σ - 1)) := by ring
      _ = e⁻¹ * t ^ (e - σ - 1) := by rw [hcomb]
  have hreal2 : (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) *
        (-(Real.log t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))).re =
      -(∫ t in Ioi (1 : ℝ), fractNat t * Real.log t * t ^ (-σ - 1)) := by
    have hpt : EqOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) *
          (-(Real.log t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)))
        (fun t : ℝ => (((-(fractNat t * Real.log t * t ^ (-σ - 1)) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, ← Complex.ofReal_cpow ht0.le]
      push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    have hcomm := Complex.ofRealCLM.integral_comp_comm hint_real2
    simpa [Complex.ofRealCLM_apply, integral_neg] using congrArg Complex.re hcomm
  have hneg_deriv_re : (-deriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) ^ 2 + 1 / σ := by
    have h1 : (-deriv riemannZeta (σ : ℂ)).re =
        1 / (σ - 1) ^ 2 +
          (∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1)) -
          σ * (∫ t in Ioi (1 : ℝ), fractNat t * Real.log t * t ^ (-σ - 1)) := by
      rw [hzeta_d]
      have hp : (1 / ((σ : ℂ) - 1) ^ 2).re = 1 / (σ - 1) ^ 2 := by
        have hcast : ((σ : ℂ) - 1) ^ 2 = ((((σ - 1) ^ 2 : ℝ) : ℂ)) := by push_cast; ring
        rw [hcast, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      simp only [neg_sub, Complex.sub_re, Complex.re_ofReal_mul, hreal1, hreal2]
      have hp' : (-1 / ((σ : ℂ) - 1) ^ 2).re = -(1 / (σ - 1) ^ 2) := by
        rw [neg_div, Complex.neg_re, hp]
      rw [hp']
      ring
    rw [h1]
    have hint1_le : ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) ≤ 1 / σ := by
      have hre : -σ - 1 < -1 := by linarith
      have hint_dom : IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi (1 : ℝ)) :=
        integrableOn_Ioi_rpow_of_lt hre zero_lt_one
      have hint_f : IntegrableOn (fun t : ℝ => fractNat t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
        refine hint_dom.mono' ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := zero_lt_one.trans ht
        change ‖fractNat t * t ^ (-σ - 1)‖ ≤ t ^ (-σ - 1)
        rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
        exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
      have hval : ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) = 1 / σ := by
        rw [integral_Ioi_rpow_of_lt hre zero_lt_one, Real.one_rpow]
        have h2 : -σ - 1 + 1 = -σ := by ring
        rw [h2]; field_simp [(by linarith : σ ≠ 0)]
      rw [← hval]
      refine setIntegral_mono_on hint_f hint_dom measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
    have hint2_nn : 0 ≤ ∫ t in Ioi (1 : ℝ), fractNat t * Real.log t * t ^ (-σ - 1) := by
      refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
      have ht1 : 1 < t := ht
      have ht0 : 0 < t := zero_lt_one.trans ht1
      exact mul_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.log_nonneg ht1.le))
        (Real.rpow_nonneg ht0.le _)
    nlinarith
  -- Divide by `riemannZeta σ` (which is real and `≥ 1 / (σ - 1) > 0`!)
  obtain ⟨hz_im, hz_ge, _⟩ := riemannZeta_real_bounds hσ
  have hz_pos : 0 < (riemannZeta (σ : ℂ)).re := lt_of_lt_of_le (by positivity) hz_ge
  have hz_eq : riemannZeta (σ : ℂ) = (((riemannZeta (σ : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hz_im])
  unfold Stage3ZeroFreeRegion.negLogDerivZeta
  rw [hz_eq, Complex.div_ofReal_re]
  have hσ1_pos : 0 < σ - 1 := by linarith
  have hσ_pos : 0 < σ := by linarith
  calc (-deriv riemannZeta (σ : ℂ)).re / (riemannZeta (σ : ℂ)).re
      ≤ (1 / (σ - 1) ^ 2 + 1 / σ) / (1 / (σ - 1)) := by
        refine div_le_div₀ (by positivity) hneg_deriv_re (by positivity) hz_ge
    _ = 1 / (σ - 1) + (σ - 1) / σ := by
        field_simp [hσ1_pos.ne', hσ_pos.ne']
    _ ≤ 1 / (σ - 1) + 1 := by
        have hfrac : (σ - 1) / σ ≤ 1 := (div_le_one hσ_pos).mpr (by linarith)
        linarith

/-- **Unconditional `σ > 1` Log-Derivative Bound on `riemannZeta`**:
`‖-ζ'(σ + it) / ζ(σ + it)‖ ≤ (-ζ'(σ) / ζ(σ)).re ≤ 1 / (σ - 1) + 1`. -/
theorem norm_negLogDerivZeta_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤
      (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ∧
    (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hsσ : 1 < (σ : ℂ).re := by simp [hσ]
  refine ⟨?_, negLogDerivZeta_real_le hσ⟩
  rw [Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hs,
    Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hsσ]
  have hsumσ := ArithmeticFunction.LSeriesSummable_vonMangoldt hsσ
  have hsumt := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  unfold LSeries
  rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hsumσ]
  refine (norm_tsum_le_tsum_norm hsumt.norm).trans ?_
  refine hsumt.norm.tsum_le_tsum (fun n => ?_) (Complex.reCLM.summable hsumσ)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp only [LSeries.term, hn, ↓reduceIte, Complex.reCLM_apply, norm_div, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero]
    have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
    rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re]

/-- **Concrete `σ > 1` Bounds on Mathlib's `DirichletCharacter.LFunction χ`**:
for EVERY modulus `q ≥ 1`, character `χ : DirichletCharacter ℂ q`, `σ > 1`, and `t : ℝ`:
1. `‖L(χ, σ + it)‖ ≤ σ / (σ - 1)`,
2. `‖1 / L(χ, σ + it)‖ ≤ σ / (σ - 1)`,
3. `‖-L'(χ, σ + it) / L(χ, σ + it)‖ ≤ 1 / (σ - 1) + 1`. -/
theorem norm_LFunction_and_inv_and_logDeriv_of_one_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) ∧
    ‖1 / DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) ∧
    ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ 1 / (σ - 1) + 1 := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hsσ : 1 < (σ : ℂ).re := by simp [hσ]
  have hζ_le := (riemannZeta_real_bounds hσ).2.2
  have h1 : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact (norm_LSeries_le_riemannZeta_real (fun n => χ.norm_le_one _) hσ t).trans hζ_le
  have h2 : ‖1 / DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) := by
    have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hs] at hmul
    have hne : DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ)) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr (by
        intro h; have := congrArg Complex.re h; simp at this; linarith)) hs.le
    have hinv : 1 / DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ)) =
        LSeries ((fun n : ℕ => χ (n : ZMod q)) * fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
          ((σ : ℂ) + I * (t : ℂ)) := by
      rw [div_eq_iff hne, mul_comm, hmul]
    rw [hinv]
    refine (norm_LSeries_le_riemannZeta_real (fun n => ?_) hσ t).trans hζ_le
    dsimp [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_one₀ (χ.norm_le_one _) (norm_nonneg _) (norm_moebius_le_one n)
  have h3 : ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ 1 / (σ - 1) + 1 := by
    refine le_trans ?_ (negLogDerivZeta_real_le hσ)
    rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs,
      Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hsσ]
    have hsumσ := ArithmeticFunction.LSeriesSummable_vonMangoldt hsσ
    have hsumt := χ.LSeriesSummable_twist_vonMangoldt hs
    unfold LSeries
    rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hsumσ]
    refine (norm_tsum_le_tsum_norm hsumt.norm).trans ?_
    refine hsumt.norm.tsum_le_tsum (fun n => ?_) (Complex.reCLM.summable hsumσ)
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.reCLM_apply,
        norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + I * (t : ℂ)).re = σ by simp]
      have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
      rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re]
      gcongr
      dsimp [Pi.mul_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
  exact ⟨h1, h2, h3⟩

/-- Bounded partial character sums for any non-principal Dirichlet character `χ ≠ 1 mod q`:
`‖∑_{1 ≤ n ≤ ⌊t⌋₊} χ(n)‖ ≤ q` for all `t : ℝ`. -/
theorem norm_stepSum_dirichletChar_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) := by
  unfold Stage3RealAnalyticLandau.stepSum
  have hq0 : 0 < q := NeZero.pos q
  have hblock : ∀ k : ℕ, ∑ n ∈ Finset.Icc 1 (k * q), χ (n : ZMod q) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      have hmq : (m + 1) * q = m * q + q := by ring
      have hsplit : Finset.Icc 1 ((m + 1) * q) =
          Finset.Icc 1 (m * q) ∪ Finset.Icc (m * q + 1) ((m + 1) * q) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 (m * q)) (Finset.Icc (m * q + 1) ((m + 1) * q)) := by
        rw [Finset.disjoint_left]; intro n hn1 hn2
        simp only [Finset.mem_Icc] at hn1 hn2; omega
      rw [hsplit, Finset.sum_union hdisj, ih, zero_add]
      have hfull : ∑ n ∈ Finset.Icc (m * q + 1) ((m + 1) * q), χ (n : ZMod q) =
          ∑ a : ZMod q, χ a := by
        refine Finset.sum_bij (fun n _ => (n : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
        · intro n₁ hn₁ n₂ hn₂ heq
          simp only [Finset.mem_Icc] at hn₁ hn₂
          have hdvd : (q : ℤ) ∣ ((n₁ : ℤ) - (n₂ : ℤ)) := by
            have h0 : (((n₁ : ℤ) - (n₂ : ℤ) : ℤ) : ZMod q) = 0 := by
              push_cast; exact sub_eq_zero.mpr heq
            exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h0
          obtain ⟨c, hc⟩ := hdvd
          have hlt1 : (n₁ : ℤ) - (n₂ : ℤ) < (q : ℤ) := by omega
          have hgt1 : -(q : ℤ) < (n₁ : ℤ) - (n₂ : ℤ) := by omega
          have hc0 : c = 0 := by nlinarith
          have hsub0 : (n₁ : ℤ) - (n₂ : ℤ) = 0 := by rw [hc, hc0, mul_zero]
          omega
        · intro a _
          set r : ℕ := a.val with hr_def
          have hr : r < q := a.val_lt
          by_cases hr0 : r = 0
          · refine ⟨(m + 1) * q, ?_, ?_⟩
            · simp only [Finset.mem_Icc]; omega
            · have ha0 : a = 0 := by
                have := ZMod.natCast_zmod_val a
                rw [← this, ← hr_def, hr0, Nat.cast_zero]
              rw [ha0]; push_cast; simp
          · refine ⟨m * q + r, ?_, ?_⟩
            · simp only [Finset.mem_Icc]; omega
            · push_cast; simp [hr_def]
        · intro _ _; rfl
      rw [hfull]
      exact MulChar.sum_eq_zero_of_ne_one hχ
  set N : ℕ := ⌊t⌋₊
  set k : ℕ := N / q
  set r : ℕ := N % q
  have hdiv : N = k * q + r := by
    rw [mul_comm]; exact (Nat.div_add_mod N q).symm
  have hr_lt : r < q := Nat.mod_lt N hq0
  have hsplit : Finset.Icc 1 N = Finset.Icc 1 (k * q) ∪ Finset.Icc (k * q + 1) N := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 (k * q)) (Finset.Icc (k * q + 1) N) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2; omega
  rw [hsplit, Finset.sum_union hdisj, hblock k, zero_add]
  calc ‖∑ n ∈ Finset.Icc (k * q + 1) N, χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Icc (k * q + 1) N, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc (k * q + 1) N, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => χ.norm_le_one _
    _ = ((Finset.Icc (k * q + 1) N).card : ℝ) := by simp
    _ ≤ (q : ℝ) := by
        rw [Nat.card_Icc]
        have hle : N + 1 - (k * q + 1) ≤ q := by omega
        exact_mod_cast hle

/-- **Exact Mellin–Abelian Representation & Polynomial Strip Bound for Non-Principal `L(χ, s)`**:
for every non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`) and `0 < s.re`:
`L(χ, s) = s * ∫_1^∞ A_χ(t) * t^(-s-1) dt` and `‖L(χ, s)‖ ≤ q * ‖s‖ / s.re`. -/
theorem LFunction_eq_mellin_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s =
      s * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpc : IsPreconnected {z : ℂ | 0 < z.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have hLHS_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => ?_) hopen
    exact (DirichletCharacter.differentiableAt_LFunction χ z (.inr hχ)).differentiableWithinAt
  have hE_meas : Measurable (Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q))) :=
    Stage3RealAnalyticLandau.measurable_stepSum _
  have hE_bd : ∀ t : ℝ, 1 ≤ t →
      ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _; simpa [Real.rpow_zero] using norm_stepSum_dirichletChar_le hχ t
  have hRHS_an : AnalyticOnNhd ℂ
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1))
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
    have hd := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound hE_meas (Nat.cast_nonneg q)
      hE_bd hz
    exact (differentiableAt_id.mul hd.differentiableAt).differentiableWithinAt
  have hEv : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1)) := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
    have hsum : LSeriesSummable (fun n => χ (n : ZMod q)) z := by
      have h1 := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hz
      refine (h1.norm).of_norm_bounded fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term]
      · simp only [LSeries.term, hn, ↓reduceIte, ArithmeticFunction.zeta_apply, Nat.cast_one,
          norm_div, norm_one]
        gcongr
        exact χ.norm_le_one _
    exact Stage3RealAnalyticLandau.LSeries_eq_mul_mellin_stepSum hE_bd (by linarith) hsum
  exact hLHS_an.eqOn_of_preconnected_of_eventuallyEq hRHS_an hpc (by norm_num : (0 : ℝ) < (2 : ℂ).re)
    hEv hs

theorem norm_LFunction_le_of_re_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  rw [LFunction_eq_mellin_of_ne_one hχ hs, norm_mul]
  have hre : -s.re - 1 < -1 := by linarith
  have hint_dom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt hre zero_lt_one).const_mul (q : ℝ)
  have hint_val : ∫ t in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hre zero_lt_one, Real.one_rpow]
    have h1 : -s.re - 1 + 1 = -s.re := by ring
    rw [h1]; field_simp [hs.ne']
  have hint_f : IntegrableOn (fun t : ℝ =>
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
    Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
      (Stage3RealAnalyticLandau.measurable_stepSum _)
      (fun t _ => by simpa [Real.rpow_zero] using norm_stepSum_dirichletChar_le hχ t) hs
  have hint_le : ‖∫ t in Ioi (1 : ℝ),
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
      (q : ℝ) / s.re := by
    rw [← hint_val]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on hint_f.norm hint_dom measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre' : (-s - 1).re = -s.re - 1 := by simp
    rw [hre']
    exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le hχ t) (Real.rpow_nonneg ht0.le _)
  calc ‖s‖ * ‖∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖s‖ * ((q : ℝ) / s.re) := mul_le_mul_of_nonneg_left hint_le (norm_nonneg s)
    _ = (q : ℝ) * ‖s‖ / s.re := by ring

theorem norm_LFunction_strip_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 2 * (q : ℝ) * (|s.im| + 2) := by
  have hs0 : 0 < s.re := by linarith
  have hbd := norm_LFunction_le_of_re_pos hχ hs0
  have hnorm_s : ‖s‖ ≤ |s.im| + 2 := by
    have h1 := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at h1
    linarith
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  calc ‖DirichletCharacter.LFunction χ s‖
      ≤ (q : ℝ) * ‖s‖ / s.re := hbd
    _ ≤ (q : ℝ) * (|s.im| + 2) / (1 / 2) := by
        refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnorm_s hq0) (by positivity) hlo
    _ = 2 * (q : ℝ) * (|s.im| + 2) := by ring

/-! ## Section 4: Unconditional Concrete de la Vallée Poussin Zero-Free Regions (0 Assumptions!) -/

/-- Auxiliary numerical inequality: `87 + 40 * Real.log 48000 < 1000`. -/
private lemma numerical_dlvp_closing : 87 + 40 * Real.log (48000 : ℝ) < 1000 := by
  have hpow : (48000 : ℝ) ≤ (2 : ℝ) ^ (16 : ℕ) := by norm_num
  have hlog : Real.log (48000 : ℝ) ≤ 16 * Real.log 2 := by
    have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 48000) hpow
    rw [Real.log_pow] at h1
    simpa using h1
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  linarith

/-- **Unconditional Concrete de la Vallée Poussin Zero-Free Region for `riemannZeta` (`|s.im| ≥ 4`)**
with explicit rational constant `1 / 14000` and **ZERO assumptions**:
for every `s : ℂ` with `4 ≤ |s.im|` and `1 - 1 / (14000 * Real.log (|s.im| + 2)) ≤ s.re`,
`riemannZeta s ≠ 0`. -/
theorem riemannZeta_zeroFree_large_im {s : ℂ} (him : 4 ≤ |s.im|)
    (hre : 1 - 1 / (14000 * Real.log (|s.im| + 2)) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  -- By Mathlib's `riemannZeta_ne_zero_of_one_le_re`, `s.re < 1`.
  have hlt1 : s.re < 1 := by
    by_contra hge
    push Not at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hz
  set γ : ℝ := s.im
  set β : ℝ := s.re
  set L : ℝ := Real.log (|γ| + 2)
  have hL_gt1 : 1 < L := by
    have h6 : Real.exp 1 < |γ| + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h6)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  set δ : ℝ := 1 / (2000 * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 8 := by
    dsimp only [δ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hβ_gt : 7 / 8 < β := by
    have h1 : 1 / (14000 * L) < 1 / 8 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hσ_le : σ ≤ 5 / 4 := by linarith
  -- Apply Landau's local bound on `closedBall s₁ (1/2)` centered at `s₁ = σ + I * γ`
  set s₁ : ℂ := (σ : ℂ) + I * (γ : ℂ)
  have hs₁_re : s₁.re = σ := by simp [s₁]
  have hs₁_im : s₁.im = γ := by simp [s₁]
  have hs₁_an : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₁ (1 / 2)) := by
    refine (DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (isOpen_compl_singleton (x := (1 : ℂ)))).mono ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    intro h1
    rw [h1] at hz
    have him_diff := Complex.abs_im_le_norm (1 - s₁)
    rw [Complex.sub_im, Complex.one_im, hs₁_im] at him_diff
    have hge4 : 4 ≤ |0 - γ| := by simpa [abs_neg] using him
    linarith
  have hs₁_nz : riemannZeta s₁ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hs₁_re]; linarith)
  set M₁ : ℝ := 12 * (|γ| + 2) / δ
  have hM₁_ge1 : 1 ≤ M₁ := by
    dsimp only [M₁]
    rw [le_div_iff₀ hδ_pos]
    linarith [abs_nonneg γ]
  have hs₁_bd : ∀ z ∈ Metric.closedBall s₁ (1 / 2), ‖riemannZeta z‖ ≤ M₁ * ‖riemannZeta s₁‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm (z - s₁)).trans hz))
    have him_diff := (abs_le.mp ((Complex.abs_im_le_norm (z - s₁)).trans hz))
    rw [Complex.sub_re, hs₁_re] at hre_diff
    rw [Complex.sub_im, hs₁_im] at him_diff
    have hz_re_lo : 1 / 2 ≤ z.re := by linarith
    have hz_re_hi : z.re ≤ 2 := by linarith
    have hz_im_lo : 1 ≤ |z.im| := by
      have : |γ| - 1 / 2 ≤ |z.im| := by
        have htri : |γ| ≤ |z.im| + |z.im - γ| := by
          have := abs_sub_le γ z.im 0
          linarith [abs_sub_comm γ z.im, show |γ - 0| = |γ| by simp, show |z.im - 0| = |z.im| by simp]
        linarith [(abs_le.mpr him_diff)]
      linarith
    have hz_im_hi : |z.im| ≤ |γ| + 1 / 2 := by
      have htri : |z.im| ≤ |γ| + |z.im - γ| := by
        simpa [add_sub_cancel] using abs_add_le γ (z.im - γ)
      linarith [(abs_le.mpr him_diff)]
    have hz_strip : ‖riemannZeta z‖ ≤ 6 * (|γ| + 2) := by
      have h := norm_riemannZeta_strip_le hz_re_lo hz_re_hi hz_im_lo
      linarith
    have hinv_s₁ : ‖1 / riemannZeta s₁‖ ≤ 2 / δ := by
      have h := norm_riemannZeta_and_inv_of_one_lt_re hσ1 γ
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      have hle : σ / δ ≤ 2 / δ := div_le_div_of_nonneg_right (by linarith) hδ_pos.le
      exact (h.2.1.trans h.2.2).trans hle
    have h1 : ‖riemannZeta z‖ / ‖riemannZeta s₁‖ ≤ M₁ := by
      rw [← norm_div, show riemannZeta z / riemannZeta s₁ = riemannZeta z * (1 / riemannZeta s₁) by ring,
        norm_mul]
      calc ‖riemannZeta z‖ * ‖1 / riemannZeta s₁‖
          ≤ (6 * (|γ| + 2)) * (2 / δ) :=
            mul_le_mul hz_strip hinv_s₁ (norm_nonneg _) (by positivity)
        _ = M₁ := by dsimp only [M₁]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hs₁_nz)).mp h1
  have hs₁_zeros : ∀ ρ ∈ Metric.closedBall s₁ (1 / 4), riemannZeta ρ = 0 → ρ.re ≤ s₁.re := by
    intro ρ _ hρ0
    by_contra hgt; push Not at hgt
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hs₁_re] at hgt; linarith) hρ0
  have hs_mem : s ∈ Metric.closedBall s₁ (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : s - s₁ = (((β - σ : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hlandau₁ := landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM₁_ge1 hs₁_an hs₁_nz hs₁_bd hs₁_zeros hs_mem hz
  have hs₁_sub_s : s₁ - s = (((σ - β : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
  have hre_inv : (1 / (s₁ - s)).re = 1 / (σ - β) := by
    rw [hs₁_sub_s, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre_err : (s₁ - s).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
    rw [hs₁_sub_s, Complex.ofReal_re, show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
    have hle : σ - β ≤ 1 / 4 := by dsimp only [σ]; linarith
    linarith
  have hbound₁ : (Stage3ZeroFreeRegion.negLogDerivZeta s₁).re ≤
      8 * Real.log M₁ + 1 - 1 / (σ - β) := by
    unfold Stage3ZeroFreeRegion.negLogDerivZeta
    rw [hre_inv] at hlandau₁
    have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8] at hlandau₁
    linarith
  -- Apply Landau's local bound on `closedBall s₂ (1/2)` centered at `s₂ = σ + 2 I * γ` (no distinguished zero)
  set s₂ : ℂ := (σ : ℂ) + I * ((2 * γ : ℝ) : ℂ)
  have hs₂_re : s₂.re = σ := by simp [s₂]
  have hs₂_im : s₂.im = 2 * γ := by simp [s₂]
  have hs₂_an : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₂ (1 / 2)) := by
    refine (DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (isOpen_compl_singleton (x := (1 : ℂ)))).mono ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    intro h1
    rw [h1] at hz
    have him_diff := Complex.abs_im_le_norm (1 - s₂)
    rw [Complex.sub_im, Complex.one_im, hs₂_im] at him_diff
    have hge8 : 8 ≤ |0 - 2 * γ| := by
      rw [zero_sub, abs_neg, abs_mul, abs_of_pos two_pos]; linarith
    linarith
  have hs₂_nz : riemannZeta s₂ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hs₂_re]; linarith)
  set M₂ : ℝ := 24 * (|γ| + 2) / δ
  have hM₂_ge1 : 1 ≤ M₂ := by
    dsimp only [M₂]
    rw [le_div_iff₀ hδ_pos]
    linarith [abs_nonneg γ]
  have hs₂_bd : ∀ z ∈ Metric.closedBall s₂ (1 / 2), ‖riemannZeta z‖ ≤ M₂ * ‖riemannZeta s₂‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm (z - s₂)).trans hz))
    have him_diff := (abs_le.mp ((Complex.abs_im_le_norm (z - s₂)).trans hz))
    rw [Complex.sub_re, hs₂_re] at hre_diff
    rw [Complex.sub_im, hs₂_im] at him_diff
    have hz_re_lo : 1 / 2 ≤ z.re := by linarith
    have hz_re_hi : z.re ≤ 2 := by linarith
    have h2γ : |2 * γ| = 2 * |γ| := by rw [abs_mul, abs_of_pos two_pos]
    have hz_im_lo : 1 ≤ |z.im| := by
      have htri : |2 * γ| ≤ |z.im| + |z.im - 2 * γ| := by
        have := abs_sub_le (2 * γ) z.im 0
        linarith [abs_sub_comm (2 * γ) z.im, show |2 * γ - 0| = |2 * γ| by simp,
          show |z.im - 0| = |z.im| by simp]
      linarith [(abs_le.mpr him_diff)]
    have hz_im_hi : |z.im| ≤ 2 * |γ| + 1 / 2 := by
      have htri : |z.im| ≤ |2 * γ| + |z.im - 2 * γ| := by
        simpa [add_sub_cancel] using abs_add_le (2 * γ) (z.im - 2 * γ)
      linarith [(abs_le.mpr him_diff)]
    have hz_strip : ‖riemannZeta z‖ ≤ 12 * (|γ| + 2) := by
      have h := norm_riemannZeta_strip_le hz_re_lo hz_re_hi hz_im_lo
      linarith
    have hinv_s₂ : ‖1 / riemannZeta s₂‖ ≤ 2 / δ := by
      have h := norm_riemannZeta_and_inv_of_one_lt_re hσ1 (2 * γ)
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      have hle : σ / δ ≤ 2 / δ := div_le_div_of_nonneg_right (by linarith) hδ_pos.le
      exact (h.2.1.trans h.2.2).trans hle
    have h1 : ‖riemannZeta z‖ / ‖riemannZeta s₂‖ ≤ M₂ := by
      rw [← norm_div, show riemannZeta z / riemannZeta s₂ = riemannZeta z * (1 / riemannZeta s₂) by ring,
        norm_mul]
      calc ‖riemannZeta z‖ * ‖1 / riemannZeta s₂‖
          ≤ (12 * (|γ| + 2)) * (2 / δ) :=
            mul_le_mul hz_strip hinv_s₂ (norm_nonneg _) (by positivity)
        _ = M₂ := by dsimp only [M₂]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hs₂_nz)).mp h1
  have hs₂_zeros : ∀ ρ ∈ Metric.closedBall s₂ (1 / 4), riemannZeta ρ = 0 → ρ.re ≤ s₂.re := by
    intro ρ _ hρ0
    by_contra hgt; push Not at hgt
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hs₂_re] at hgt; linarith) hρ0
  have hbound₂ : (Stage3ZeroFreeRegion.negLogDerivZeta s₂).re ≤ 8 * Real.log M₂ := by
    have h := landau_negLogDeriv_le (r := 1 / 4) (R := 1 / 2)
      (by norm_num) (by norm_num) hM₂_ge1 hs₂_an hs₂_nz hs₂_bd hs₂_zeros
    unfold Stage3ZeroFreeRegion.negLogDerivZeta
    have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8] at h
    exact h
  -- Real-axis bound at `σ`
  have hbound₀ : (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / δ + 1 := by
    have h := negLogDerivZeta_real_le hσ1
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rwa [hσ_sub] at h
  -- Combine via `Stage3ZeroFreeRegion.three_four_one_zeta_re_nonneg`!
  have h341 := Stage3ZeroFreeRegion.three_four_one_zeta_re_nonneg hσ1 γ
  have h2it : (σ : ℂ) + 2 * I * (γ : ℂ) = s₂ := by dsimp only [s₂]; push_cast; ring
  rw [h2it] at h341
  -- Bound `log M₁ ≤ log M₂ ≤ log 48000 + 2 * L`
  have hM₁_le_M₂ : M₁ ≤ M₂ := by
    dsimp only [M₁, M₂]
    exact div_le_div_of_nonneg_right (by linarith [abs_nonneg γ]) hδ_pos.le
  have hlogM₁ : Real.log M₁ ≤ Real.log M₂ := Real.log_le_log (by linarith) hM₁_le_M₂
  have hlogM₂ : Real.log M₂ ≤ Real.log (48000 : ℝ) + 2 * L := by
    have hL_le : L ≤ |γ| + 2 := (Real.log_le_sub_one_of_pos (by linarith [abs_nonneg γ])).trans (by linarith)
    have hM₂_le : M₂ ≤ 48000 * (|γ| + 2) ^ 2 := by
      have hM₂_eq : M₂ = 48000 * (|γ| + 2) * L := by
        dsimp only [M₂, δ]; field_simp [hL_pos.ne']; ring
      rw [hM₂_eq]
      nlinarith [abs_nonneg γ]
    calc Real.log M₂ ≤ Real.log (48000 * (|γ| + 2) ^ 2) := Real.log_le_log (by linarith) hM₂_le
      _ = Real.log (48000 : ℝ) + Real.log ((|γ| + 2) ^ 2) :=
          Real.log_mul (by norm_num) (by positivity)
      _ = Real.log (48000 : ℝ) + 2 * L := by rw [Real.log_pow]; push_cast; rfl
  -- Strict error bound `7 + 32 log M₁ + 8 log M₂ < 1000 L = 1 / (2 δ)`
  have herr_strict : 7 + 32 * Real.log M₁ + 8 * Real.log M₂ < 1 / (2 * δ) := by
    have h1000 : 1000 * L = 1 / (2 * δ) := by
      dsimp only [δ]; field_simp [hL_pos.ne']; ring
    have hcomb : 7 + 32 * Real.log M₁ + 8 * Real.log M₂ ≤ (87 + 40 * Real.log (48000 : ℝ)) * L := by
      nlinarith [hlogM₁, hlogM₂, hL_gt1, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 48000)]
    have h2 : (87 + 40 * Real.log (48000 : ℝ)) * L < 1000 * L :=
      mul_lt_mul_of_pos_right numerical_dlvp_closing hL_pos
    linarith
  have hineq_strict : 4 / (σ - β) < 7 / (2 * δ) := by
    have h1 : 4 / (σ - β) < 3 / δ + 1 / (2 * δ) := by
      have h4 : 4 * (1 / (σ - β)) = 4 / (σ - β) := by ring
      have h3 : 3 * (1 / δ) = 3 / δ := by ring
      linarith
    have h2 : 3 / δ + 1 / (2 * δ) = 7 / (2 * δ) := by field_simp [hδ_pos.ne']; ring
    linarith
  have hσβ_pos : 0 < σ - β := by linarith
  have hmul_strict : 8 * δ < 7 * (σ - β) := by
    have h := (div_lt_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 2 * δ)).mp hineq_strict
    linarith
  have hβ_strict : β < 1 - δ / 7 := by dsimp only [σ] at hmul_strict; linarith
  have hδ7 : δ / 7 = 1 / (14000 * L) := by
    dsimp only [δ]; field_simp [hL_pos.ne']; ring
  linarith

/-- **Unconditional Zero-Free Strip on Bounded Height (`|s.im| ≤ 4`)**:
directly from Mathlib's `IsCompact.inter_riemannZetaZeros_finite` and
`riemannZeta_ne_zero_of_one_le_re`. -/
theorem riemannZeta_zeroFree_bounded_im :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ s : ℂ, |s.im| ≤ 4 → 1 - ε₀ ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  set K : Set ℂ := {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ 4}
  have hK_comp : IsCompact K := by
    have hsub : K = Complex.equivRealProdCLM.symm '' (Set.Icc (1 / 2 : ℝ) 1 ×ˢ Set.Icc (-4 : ℝ) 4) := by
      ext z
      simp only [K, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, by
          apply Complex.ext <;> simp⟩
      · rintro ⟨⟨x, y⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
    rw [hsub]
    exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hfin : (K ∩ riemannZetaZeros).Finite := hK_comp.inter_riemannZetaZeros_finite
  set F : Finset ℂ := hfin.toFinset
  -- Minimum distance `1 - z.re > 0` over the finite set `F`
  have hall_pos : ∀ z ∈ F, 0 < 1 - z.re := by
    intro z hz
    have hmem : z ∈ K ∩ riemannZetaZeros := hfin.mem_toFinset.mp hz
    have hz0 : riemannZeta z = 0 := mem_riemannZetaZeros.mp hmem.2
    have hlt : z.re < 1 := by
      by_contra hge; push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hz0
    linarith
  by_cases hF : F.Nonempty
  · set m : ℝ := F.inf' hF (fun z => 1 - z.re)
    have hm_pos : 0 < m := (Finset.lt_inf'_iff hF).mpr hall_pos
    refine ⟨min (1 / 4) (m / 2), by positivity, fun s him hre _ hz => ?_⟩
    have hlt1 : s.re < 1 := by
      by_contra hge; push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hz
    have hsK : s ∈ K := ⟨by linarith [min_le_left (1 / 4 : ℝ) (m / 2)], hlt1.le, him⟩
    have hsF : s ∈ F := hfin.mem_toFinset.mpr ⟨hsK, mem_riemannZetaZeros.mpr hz⟩
    have hm_le : m ≤ 1 - s.re := Finset.inf'_le (fun z => 1 - z.re) hsF
    linarith [min_le_right (1 / 4 : ℝ) (m / 2)]
  · refine ⟨1 / 4, by norm_num, fun s him hre _ hz => ?_⟩
    have hlt1 : s.re < 1 := by
      by_contra hge; push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hz
    have hsK : s ∈ K := ⟨by linarith, hlt1.le, him⟩
    have hsF : s ∈ F := hfin.mem_toFinset.mpr ⟨hsK, mem_riemannZetaZeros.mpr hz⟩
    exact hF ⟨s, hsF⟩

/-- **UNCONDITIONAL CLASSIC DE LA VALLÉE POUSSIN ZERO-FREE REGION DIRECTLY ON MATHLIB'S `riemannZeta` (0 ASSUMPTIONS!)**:
`∃ c > 0, ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0`. -/
theorem riemannZeta_deLaValleePoussin_zeroFree :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨ε₀, hε₀, hbdd⟩ := riemannZeta_zeroFree_bounded_im
  set c : ℝ := min (1 / 14000) (ε₀ * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, fun s hre hs1 => ?_⟩
  have hlog_ge : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlog_pos : 0 < Real.log (|s.im| + 2) := lt_of_lt_of_le hlog2 hlog_ge
  by_cases him : 4 ≤ |s.im|
  · refine riemannZeta_zeroFree_large_im him ?_
    have hc1 : c ≤ 1 / 14000 := min_le_left _ _
    have hdiv : c / Real.log (|s.im| + 2) ≤ 1 / (14000 * Real.log (|s.im| + 2)) := by
      have h1 := div_le_div_of_nonneg_right hc1 hlog_pos.le
      linarith [show (1 / 14000 : ℝ) / Real.log (|s.im| + 2) =
          1 / (14000 * Real.log (|s.im| + 2)) by ring]
    linarith
  · push Not at him
    refine hbdd s him.le ?_ hs1
    have hc2 : c ≤ ε₀ * Real.log 2 := min_le_right _ _
    have hdiv : c / Real.log (|s.im| + 2) ≤ ε₀ := by
      rw [div_le_iff₀ hlog_pos]
      exact hc2.trans (mul_le_mul_of_nonneg_left hlog_ge hε₀.le)
    linarith

/-- Corollary (exponent-9 form):
`∃ c > 0, ∀ s : ℂ, 1 - c / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0`. -/
theorem riemannZeta_zeroFree_log_pow_nine :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨c, hc, hzf⟩ := riemannZeta_deLaValleePoussin_zeroFree
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨c / 256, by positivity, fun s hre hs1 => ?_⟩
  have hlog_ge : (1 / 2 : ℝ) < Real.log (|s.im| + 2) :=
    hlog2.trans_le (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im]))
  have hlog_pos : 0 < Real.log (|s.im| + 2) := by linarith
  have hpow : (1 / 256 : ℝ) ≤ (Real.log (|s.im| + 2)) ^ 8 := by
    have h1 : ((1 / 2 : ℝ) ^ 8) ≤ (Real.log (|s.im| + 2)) ^ 8 :=
      pow_le_pow_left₀ (by norm_num) hlog_ge.le 8
    norm_num at h1
    exact h1
  have hdiv : (c / 256) / (Real.log (|s.im| + 2)) ^ 9 ≤ c / Real.log (|s.im| + 2) := by
    rw [div_le_div_iff₀ (pow_pos hlog_pos 9) hlog_pos]
    have h9 : (Real.log (|s.im| + 2)) ^ 9 = (Real.log (|s.im| + 2)) ^ 8 * Real.log (|s.im| + 2) := by
      ring
    rw [h9]
    have hmul : (c / 256) * Real.log (|s.im| + 2) ≤ c * ((Real.log (|s.im| + 2)) ^ 8 * Real.log (|s.im| + 2)) := by
      have h2 : c / 256 ≤ c * (Real.log (|s.im| + 2)) ^ 8 := by
        have := mul_le_mul_of_nonneg_left hpow hc.le
        linarith [show c * (1 / 256 : ℝ) = c / 256 by ring]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h2 hlog_pos.le
    exact hmul
  exact hzf s (by linarith) hs1

/-- **UNCONDITIONAL CONCRETE DE LA VALLÉE POUSSIN ZERO-FREE REGION FOR COMPLEX DIRICHLET CHARACTERS (`χ ^ 2 ≠ 1`)**
with explicit uniform rational constant `1 / 14000` across ALL moduli `q` and ALL `s : ℂ` (ZERO assumptions!):
for every `q ≥ 1`, `χ : DirichletCharacter ℂ q` with `χ ^ 2 ≠ 1`, and EVERY `s : ℂ`,
`1 - 1 / (14000 * Real.log (q * (|s.im| + 2))) ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0`. -/
theorem LFunction_complex_char_deLaValleePoussin_zeroFree {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 ≠ 1) {s : ℂ}
    (hre : 1 - 1 / (14000 * Real.log ((q : ℝ) * (|s.im| + 2))) ≤ s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hz
  have hχ1 : χ ≠ 1 := fun h => hχ2 (by rw [h, one_pow])
  -- Any `χ` with `χ ^ 2 ≠ 1` must have modulus `q ≥ 3` (since `(ZMod 1)ˣ` and `(ZMod 2)ˣ` are trivial)
  have hq3 : 3 ≤ q := by
    by_contra hlt
    push Not at hlt
    have hq_pos : 0 < q := NeZero.pos q
    have hcases : q = 1 ∨ q = 2 := by omega
    rcases hcases with rfl | rfl
    · exact hχ1 (DirichletCharacter.level_one χ)
    · apply hχ1
      ext u
      have hu1 : (u : ZMod 2) = 1 := by
        have hval : (u : ZMod 2).val < 2 := (u : ZMod 2).val_lt
        have hne0 : (u : ZMod 2) ≠ 0 := Units.ne_zero u
        have hval1 : (u : ZMod 2).val = 1 := by
          by_contra h
          have hv0 : (u : ZMod 2).val = 0 := by omega
          apply hne0
          have := ZMod.natCast_zmod_val (u : ZMod 2)
          rw [← this, hv0, Nat.cast_zero]
        have := ZMod.natCast_zmod_val (u : ZMod 2)
        rw [← this, hval1, Nat.cast_one]
      rw [hu1, map_one, map_one]
  have hlt1 : s.re < 1 := by
    by_contra hge; push Not at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) hge hz
  set γ : ℝ := s.im
  set β : ℝ := s.re
  have hqR3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  set Q : ℝ := (q : ℝ) * (|γ| + 2)
  have hQ_ge6 : (6 : ℝ) ≤ Q := by dsimp only [Q]; nlinarith [abs_nonneg γ]
  set L : ℝ := Real.log Q
  have hL_gt1 : 1 < L := by
    have h6 : Real.exp 1 < Q := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h6)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  set δ : ℝ := 1 / (2000 * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 8 := by
    dsimp only [δ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hβ_gt : 7 / 8 < β := by
    have h1 : 1 / (14000 * L) < 1 / 8 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hσ_le : σ ≤ 5 / 4 := by linarith
  -- Landau bound for `L(χ, ·)` on `closedBall s₁ (1/2)`
  set s₁ : ℂ := (σ : ℂ) + I * (γ : ℂ)
  have hs₁_re : s₁.re = σ := by simp [s₁]
  have hs₁_im : s₁.im = γ := by simp [s₁]
  have hs₁_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall s₁ (1 / 2)) := by
    refine (DifferentiableOn.analyticOnNhd (fun z _ =>
      (DirichletCharacter.differentiableAt_LFunction χ z (.inr hχ1)).differentiableWithinAt)
      isOpen_univ).mono (Set.subset_univ _)
  have hs₁_nz : DirichletCharacter.LFunction χ s₁ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by rw [hs₁_re]; linarith)
  set M₁ : ℝ := 12 * Q / δ
  have hM₁_ge1 : 1 ≤ M₁ := by
    dsimp only [M₁]; rw [le_div_iff₀ hδ_pos]; linarith
  have hs₁_bd : ∀ z ∈ Metric.closedBall s₁ (1 / 2),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M₁ * ‖DirichletCharacter.LFunction χ s₁‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm (z - s₁)).trans hz))
    have him_diff := (abs_le.mp ((Complex.abs_im_le_norm (z - s₁)).trans hz))
    rw [Complex.sub_re, hs₁_re] at hre_diff
    rw [Complex.sub_im, hs₁_im] at him_diff
    have hz_im_hi : |z.im| ≤ |γ| + 1 / 2 := by
      have htri : |z.im| ≤ |γ| + |z.im - γ| := by
        simpa [add_sub_cancel] using abs_add_le γ (z.im - γ)
      linarith [(abs_le.mpr him_diff)]
    have hz_strip : ‖DirichletCharacter.LFunction χ z‖ ≤ 6 * Q := by
      have h := norm_LFunction_strip_le hχ1 (by linarith : 1 / 2 ≤ z.re) (by linarith : z.re ≤ 2)
      dsimp only [Q]; nlinarith [abs_nonneg γ]
    have hinv_s₁ : ‖1 / DirichletCharacter.LFunction χ s₁‖ ≤ 2 / δ := by
      have h := (norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hσ1 γ).2.1
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      exact h.trans (div_le_div_of_nonneg_right (by linarith) hδ_pos.le)
    have h1 : ‖DirichletCharacter.LFunction χ z‖ / ‖DirichletCharacter.LFunction χ s₁‖ ≤ M₁ := by
      rw [← norm_div, show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₁ =
          DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₁) by ring, norm_mul]
      calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₁‖
          ≤ (6 * Q) * (2 / δ) := mul_le_mul hz_strip hinv_s₁ (norm_nonneg _) (by positivity)
        _ = M₁ := by dsimp only [M₁]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hs₁_nz)).mp h1
  have hs₁_zeros : ∀ ρ ∈ Metric.closedBall s₁ (1 / 4),
      DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ s₁.re := by
    intro ρ _ hρ0
    by_contra hgt; push Not at hgt
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by rw [hs₁_re] at hgt; linarith) hρ0
  have hs_mem : s ∈ Metric.closedBall s₁ (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : s - s₁ = (((β - σ : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hlandau₁ := landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM₁_ge1 hs₁_an hs₁_nz hs₁_bd hs₁_zeros hs_mem hz
  have hs₁_sub_s : s₁ - s = (((σ - β : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
  have hre_inv : (1 / (s₁ - s)).re = 1 / (σ - β) := by
    rw [hs₁_sub_s, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre_err : (s₁ - s).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
    rw [hs₁_sub_s, Complex.ofReal_re, show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
    have hle : σ - β ≤ 1 / 4 := by dsimp only [σ]; linarith
    linarith
  have hbound₁ : (Stage3ZeroFreeRegion.negLogDerivL χ s₁).re ≤
      8 * Real.log M₁ + 1 - 1 / (σ - β) := by
    unfold Stage3ZeroFreeRegion.negLogDerivL
    rw [hre_inv] at hlandau₁
    have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8] at hlandau₁
    linarith
  -- Landau bound for `L(χ^2, ·)` on `closedBall s₂ (1/2)` (entire since `χ ^ 2 ≠ 1`!)
  set s₂ : ℂ := (σ : ℂ) + I * ((2 * γ : ℝ) : ℂ)
  have hs₂_re : s₂.re = σ := by simp [s₂]
  have hs₂_im : s₂.im = 2 * γ := by simp [s₂]
  have hs₂_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction (χ ^ 2)) (Metric.closedBall s₂ (1 / 2)) := by
    refine (DifferentiableOn.analyticOnNhd (fun z _ =>
      (DirichletCharacter.differentiableAt_LFunction (χ ^ 2) z (.inr hχ2)).differentiableWithinAt)
      isOpen_univ).mono (Set.subset_univ _)
  have hs₂_nz : DirichletCharacter.LFunction (χ ^ 2) s₂ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ ^ 2) (.inl hχ2) (by rw [hs₂_re]; linarith)
  set M₂ : ℝ := 24 * Q / δ
  have hM₂_ge1 : 1 ≤ M₂ := by
    dsimp only [M₂]; rw [le_div_iff₀ hδ_pos]; linarith
  have hs₂_bd : ∀ z ∈ Metric.closedBall s₂ (1 / 2),
      ‖DirichletCharacter.LFunction (χ ^ 2) z‖ ≤ M₂ * ‖DirichletCharacter.LFunction (χ ^ 2) s₂‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm (z - s₂)).trans hz))
    have him_diff := (abs_le.mp ((Complex.abs_im_le_norm (z - s₂)).trans hz))
    rw [Complex.sub_re, hs₂_re] at hre_diff
    rw [Complex.sub_im, hs₂_im] at him_diff
    have h2γ : |2 * γ| = 2 * |γ| := by rw [abs_mul, abs_of_pos two_pos]
    have hz_im_hi : |z.im| ≤ 2 * |γ| + 1 / 2 := by
      have htri : |z.im| ≤ |2 * γ| + |z.im - 2 * γ| := by
        simpa [add_sub_cancel] using abs_add_le (2 * γ) (z.im - 2 * γ)
      linarith [(abs_le.mpr him_diff)]
    have hz_strip : ‖DirichletCharacter.LFunction (χ ^ 2) z‖ ≤ 12 * Q := by
      have h := norm_LFunction_strip_le hχ2 (by linarith : 1 / 2 ≤ z.re) (by linarith : z.re ≤ 2)
      dsimp only [Q]; nlinarith [abs_nonneg γ]
    have hinv_s₂ : ‖1 / DirichletCharacter.LFunction (χ ^ 2) s₂‖ ≤ 2 / δ := by
      have h := (norm_LFunction_and_inv_and_logDeriv_of_one_lt_re (χ ^ 2) hσ1 (2 * γ)).2.1
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      exact h.trans (div_le_div_of_nonneg_right (by linarith) hδ_pos.le)
    have h1 : ‖DirichletCharacter.LFunction (χ ^ 2) z‖ /
        ‖DirichletCharacter.LFunction (χ ^ 2) s₂‖ ≤ M₂ := by
      rw [← norm_div, show DirichletCharacter.LFunction (χ ^ 2) z / DirichletCharacter.LFunction (χ ^ 2) s₂ =
          DirichletCharacter.LFunction (χ ^ 2) z * (1 / DirichletCharacter.LFunction (χ ^ 2) s₂) by ring,
        norm_mul]
      calc ‖DirichletCharacter.LFunction (χ ^ 2) z‖ * ‖1 / DirichletCharacter.LFunction (χ ^ 2) s₂‖
          ≤ (12 * Q) * (2 / δ) := mul_le_mul hz_strip hinv_s₂ (norm_nonneg _) (by positivity)
        _ = M₂ := by dsimp only [M₂]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hs₂_nz)).mp h1
  have hs₂_zeros : ∀ ρ ∈ Metric.closedBall s₂ (1 / 4),
      DirichletCharacter.LFunction (χ ^ 2) ρ = 0 → ρ.re ≤ s₂.re := by
    intro ρ _ hρ0
    by_contra hgt; push Not at hgt
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ ^ 2) (.inl hχ2)
      (by rw [hs₂_re] at hgt; linarith) hρ0
  have hbound₂ : (Stage3ZeroFreeRegion.negLogDerivL (χ ^ 2) s₂).re ≤ 8 * Real.log M₂ := by
    have h := landau_negLogDeriv_le (r := 1 / 4) (R := 1 / 2)
      (by norm_num) (by norm_num) hM₂_ge1 hs₂_an hs₂_nz hs₂_bd hs₂_zeros
    unfold Stage3ZeroFreeRegion.negLogDerivL
    have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8] at h
    exact h
  -- Real-axis bound at `σ`
  have hbound₀ : (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / δ + 1 := by
    have h := negLogDerivZeta_real_le hσ1
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rwa [hσ_sub] at h
  -- Combine via `Stage3ZeroFreeRegion.three_four_one_zeta_negLogDerivL_re_nonneg`!
  have h341 := Stage3ZeroFreeRegion.three_four_one_zeta_negLogDerivL_re_nonneg χ hσ1 γ
  have h2it : (σ : ℂ) + 2 * I * (γ : ℂ) = s₂ := by dsimp only [s₂]; push_cast; ring
  rw [h2it] at h341
  have hlogM₁ : Real.log M₁ ≤ Real.log M₂ :=
    Real.log_le_log (by linarith) (div_le_div_of_nonneg_right (by linarith) hδ_pos.le)
  have hlogM₂ : Real.log M₂ ≤ Real.log (48000 : ℝ) + 2 * L := by
    have hL_le : L ≤ Q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hM₂_le : M₂ ≤ 48000 * Q ^ 2 := by
      have hM₂_eq : M₂ = 48000 * Q * L := by
        dsimp only [M₂, δ]; field_simp [hL_pos.ne']; ring
      rw [hM₂_eq]; nlinarith
    calc Real.log M₂ ≤ Real.log (48000 * Q ^ 2) := Real.log_le_log (by linarith) hM₂_le
      _ = Real.log (48000 : ℝ) + Real.log (Q ^ 2) := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log (48000 : ℝ) + 2 * L := by rw [Real.log_pow]; push_cast; rfl
  have herr_strict : 7 + 32 * Real.log M₁ + 8 * Real.log M₂ < 1 / (2 * δ) := by
    have h1000 : 1000 * L = 1 / (2 * δ) := by
      dsimp only [δ]; field_simp [hL_pos.ne']; ring
    have hcomb : 7 + 32 * Real.log M₁ + 8 * Real.log M₂ ≤ (87 + 40 * Real.log (48000 : ℝ)) * L := by
      nlinarith [hlogM₁, hlogM₂, hL_gt1, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 48000)]
    have h2 : (87 + 40 * Real.log (48000 : ℝ)) * L < 1000 * L :=
      mul_lt_mul_of_pos_right numerical_dlvp_closing hL_pos
    linarith
  have hineq_strict : 4 / (σ - β) < 7 / (2 * δ) := by
    have h1 : 4 / (σ - β) < 3 / δ + 1 / (2 * δ) := by
      have h4 : 4 * (1 / (σ - β)) = 4 / (σ - β) := by ring
      have h3 : 3 * (1 / δ) = 3 / δ := by ring
      linarith
    have h2 : 3 / δ + 1 / (2 * δ) = 7 / (2 * δ) := by field_simp [hδ_pos.ne']; ring
    linarith
  have hσβ_pos : 0 < σ - β := by linarith
  have hmul_strict : 8 * δ < 7 * (σ - β) := by
    have h := (div_lt_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 2 * δ)).mp hineq_strict
    linarith
  have hβ_strict : β < 1 - δ / 7 := by dsimp only [σ] at hmul_strict; linarith
  have hδ7 : δ / 7 = 1 / (14000 * L) := by
    dsimp only [δ]; field_simp [hL_pos.ne']; ring
  linarith

end RHDirect.Stage5ZetaZeroFree


