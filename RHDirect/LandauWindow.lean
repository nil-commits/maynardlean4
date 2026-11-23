import RHDirect.Interfaces
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.Floor

/-!
# RHDirect.LandauWindow

A compact, self-contained, 0-`sorry`, 0-`axiom` Lean 4 proof of the windowed Landau nonvanishing
theorem and its application to arbitrary positively-weighted finite families of Dirichlet
`L`-functions (`RHDirect.CharFamily`):

1. **Abstract Windowed Landau Theorem (`landau_window`)**:
   Given `PoleData g Φ Z` (a real measurable function `g` with `|g(u)| ≤ C e^{2u}`, whose Laplace
   transform `Φ(s) = ∫₀^∞ g(u) e^{-su} du` extends meromorphically to `Re(s) > 0` with isolated
   simple poles at `Z` having positive real residue at real poles) and a windowed upper bound
   `WindowHypU g θ δ` on arbitrarily large windows `[U, (1 + δ) U]`, every pole `ρ ∈ Z` satisfies
   `Re(ρ) ≤ θ`.
2. **Mellin / Laplace Continuation for Dirichlet Character Families (`poleData`)**:
   Constructs `PoleData (CharFamily.gm F) Φ (CharFamily.zeroSet F)` directly from Mathlib's
   `DirichletCharacter.LFunction` and `riemannZeta`.
3. **Windowed Nonvanishing for `CharFamily` (`zeroFree_of_rpow_window`)**:
   If `HasRpowWindow F.Gm θ δ C` holds (`0 < θ < 1`, `δ > 0`), then `F.ZeroFree θ`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace RHDirect

/-! ## Part 1: Abstract Windowed Landau Nonvanishing Theorem -/

/-- Laplace / meromorphic pole data for the abstract windowed Landau theorem. -/
structure PoleData (g : ℝ → ℝ) (Φ : ℂ → ℂ) (Z : Set ℂ) : Prop where
  meas : Measurable g
  growth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)
  laplace : ∀ s : ℂ, 2 < s.re → Φ s = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-s * u)
  pos : ∀ ρ ∈ Z, 0 < ρ.re
  diff : DifferentiableOn ℂ Φ ({s : ℂ | 0 < s.re} \ Z)
  iso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z
  pole : ∀ ρ ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s

/-- Exponentially-weighted upper majorant on arbitrarily large additive windows `[U, (1 + δ) U]`. -/
def WindowHypU (g : ℝ → ℝ) (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ R : ℝ → ℝ,
    IntegrableOn (fun u => R u * Real.exp (-θ * u)) (Icc U ((1 + δ) * U)) ∧
    (∀ u ∈ Icc U ((1 + δ) * U), 0 ≤ R u ∧ g u ≤ R u) ∧
    ∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u) ≤ Real.exp (η * U)

private lemma kernel_max (k : ℕ) {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) ≤ 1 / a ^ k := by
  have h := Real.pow_div_factorial_le_exp (a * u) (mul_nonneg ha.le hu) k
  rw [le_div_iff₀ (pow_pos ha k)]
  calc u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) * a ^ k
      = (a * u) ^ k / (k.factorial : ℝ) * Real.exp (-(a * u)) := by rw [mul_pow, neg_mul]; ring
    _ ≤ Real.exp (a * u) * Real.exp (-(a * u)) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

private lemma kernel_integral (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) = (a ^ (k + 1))⁻¹ := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi hk ha
  have e : ∀ u : ℝ, u ^ k * Real.exp (-a * u) = u ^ (((k : ℝ) + 1) - 1) * Real.exp (-(a * u)) :=
    fun u => by rw [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
  rw [MeasureTheory.integral_div]
  simp_rw [e]
  rw [key, Real.Gamma_nat_eq_factorial]
  have h2 : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [h2, Real.rpow_natCast, one_div, inv_pow, mul_div_assoc, div_self hf, mul_one]

private lemma integrable_kernel (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-b * u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := b)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hb
  exact h.congr_fun (fun u _ => by simp only [Real.rpow_natCast, Real.rpow_one]) measurableSet_Ioi

private lemma iteratedDeriv_laplace (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (s : ℂ) (hs : 2 < s.re) :
    iteratedDeriv k (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) s =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-s * u) := by
  have hmeas : ∀ j (z : ℂ),
      AEStronglyMeasurable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-z * u))
        (volume.restrict (Ioi (0 : ℝ))) :=
    fun j z => (by fun_prop : Measurable _).aestronglyMeasurable
  have hbound : ∀ j b (z : ℂ), 2 + b ≤ z.re → ∀ u : ℝ, 0 < u →
      ‖(g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-z * u)‖ ≤ C * (u ^ j * Real.exp (-b * u)) := by
    intro j b z hz u hu
    have h1 : ‖(g u : ℂ)‖ ≤ C * Real.exp (2 * u) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hgC u hu.le
    have h2 : ‖((-u : ℝ) : ℂ) ^ j‖ = u ^ j := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu]
    have h3 : ‖cexp (-z * u)‖ ≤ Real.exp (-(2 + b) * u) := by
      rw [Complex.norm_exp]; simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.neg_im, mul_zero, sub_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [norm_mul, norm_mul, h2]
    calc ‖(g u : ℂ)‖ * u ^ j * ‖cexp (-z * u)‖
        ≤ C * Real.exp (2 * u) * u ^ j * Real.exp (-(2 + b) * u) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 (norm_nonneg _)
            (mul_nonneg ((norm_nonneg _).trans h1) (by positivity))
      _ = C * (u ^ j * (Real.exp (2 * u) * Real.exp (-(2 + b) * u))) := by ring
      _ = C * (u ^ j * Real.exp (-b * u)) := by
          rw [← Real.exp_add, show 2 * u + -(2 + b) * u = -b * u by ring]
  have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  suffices ∀ j : ℕ, ∀ z : ℂ, 2 < z.re →
      iteratedDeriv j (fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-w * u)) z =
        ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-z * u) from this k s hs
  intro j
  induction j with
  | zero => intro z _; simp
  | succ j ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-w * u))
        =ᶠ[𝓝 z] fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-w * u) :=
      Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => ih w hw
    rw [hev.deriv_eq]
    set δ := (z.re - 2) / 2 with hδ_def
    have hδpos : 0 < δ := by rw [hδ_def]; linarith
    have hre : ∀ w ∈ Metric.ball z δ, 2 + δ ≤ w.re := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm (w - z)).trans hw.le)).1
      rw [Complex.sub_re] at h1; rw [hδ_def] at *; linarith
    have hint : Integrable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-z * u))
        (volume.restrict (Ioi 0)) := by
      refine Integrable.mono' ((integrable_kernel j δ hδpos).const_mul C) (hmeas j z) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
      exact hbound j δ z (hre z (Metric.mem_ball_self hδpos)) u hu
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-w * u))
      (F' := fun w u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (j + 1) * cexp (-w * u))
      (Metric.ball_mem_nhds z hδpos)
      (Eventually.of_forall fun w => hmeas j w) hint (hmeas (j + 1) z) ?_
      ((integrable_kernel (j + 1) δ hδpos).const_mul C) ?_).2.deriv
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu w hw => ?_)
      exact hbound (j + 1) δ w (hre w hw) u hu
    · refine Eventually.of_forall fun u w _ => ?_
      have h1 : HasDerivAt (fun v : ℂ => -v * (u : ℂ)) (-(u : ℂ)) w := by
        simpa using (hasDerivAt_id' w).neg.mul_const (u : ℂ)
      exact (h1.cexp.const_mul ((g u : ℂ) * ((-u : ℝ) : ℂ) ^ j)).congr_deriv (by push_cast; ring)

private lemma landau_coeff {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) (k : ℕ)
    {s : ℂ} (hs : 2 < s.re) :
    (-1) ^ k * iteratedDeriv k Φ s / (k.factorial : ℂ) =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by
  obtain ⟨C, hC⟩ := hP.growth
  have hev : Φ =ᶠ[𝓝 s] (fun z => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact hP.laplace z hz
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_laplace g hP.meas C hC k s hs, ← integral_const_mul,
    ← integral_div]
  congr 1; funext u; push_cast
  have e : ((-1 : ℂ)) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by rw [← mul_pow]; ring
  calc (-1 : ℂ) ^ k * ((g u : ℂ) * (-(u : ℂ)) ^ k * cexp (-s * u)) / (k.factorial : ℂ)
      = (g u : ℂ) * ((-1 : ℂ) ^ k * (-(u : ℂ)) ^ k) * cexp (-s * u) / (k.factorial : ℂ) := by ring
    _ = (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by rw [e]

private lemma landau_tails {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧
      ∫ u in Ioi (0 : ℝ) \ Icc U ((1 + δ) * U), u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ)
        ≤ C / σ ^ k := by
  have hint : ∀ (k : ℕ) (a : ℝ), 0 < a →
      IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)) (Ioi 0) :=
    fun k a ha => (integrable_kernel k a ha).div_const _
  have hchernoff : ∀ (k : ℕ) {s l U V : ℝ}, 0 ≤ l → l < s →
      ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp (-s * u) / (k.factorial : ℝ) ≤
        Real.exp (-(l * V)) * ((s - l) ^ (k + 1))⁻¹ + Real.exp (l * U) * ((s + l) ^ (k + 1))⁻¹ := by
    intro k s l U V hl hs
    have ha : 0 < s - l := by linarith
    have hb : 0 < s + l := by linarith
    have i1 := (hint k (s - l) ha).const_mul (Real.exp (-(l * V)))
    have i2 := (hint k (s + l) hb).const_mul (Real.exp (l * U))
    have i3 := i1.add i2
    rw [← kernel_integral k ha, ← kernel_integral k hb, ← integral_const_mul, ← integral_const_mul,
      ← integral_add i1 i2]
    refine le_trans (setIntegral_mono_on (IntegrableOn.mono_set (hint k s (by linarith)) sdiff_subset)
      (IntegrableOn.mono_set i3 sdiff_subset) (measurableSet_Ioi.diff measurableSet_Icc) ?_)
      (setIntegral_mono_set i3 ?_ sdiff_subset.eventuallyLE)
    · intro u hu
      have hu0 : 0 < u := hu.1
      have e1 : Real.exp (-(l * V)) * Real.exp (-(s - l) * u) = Real.exp (-s * u + l * (u - V)) := by
        rw [← Real.exp_add]; congr 1; ring
      have e2 : Real.exp (l * U) * Real.exp (-(s + l) * u) = Real.exp (-s * u + l * (U - u)) := by
        rw [← Real.exp_add]; congr 1; ring
      have key : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V)) + Real.exp (-s * u + l * (U - u)) := by
        have hn := hu.2
        rw [mem_Icc, not_and_or, not_le, not_le] at hn
        rcases hn with h | h
        · linarith [Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)] :
            -s * u ≤ -s * u + l * (U - u)), Real.exp_pos (-s * u + l * (u - V))]
        · linarith [Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)] :
            -s * u ≤ -s * u + l * (u - V)), Real.exp_pos (-s * u + l * (U - u))]
      rw [← e1, ← e2] at key
      have hp : 0 ≤ u ^ k / (k.factorial : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left key hp
      calc _ = u ^ k / (k.factorial : ℝ) * Real.exp (-s * u) := by ring
        _ ≤ _ := this
        _ = Real.exp (-(l * V)) * (u ^ k * Real.exp (-(s - l) * u) / (k.factorial : ℝ)) +
            Real.exp (l * U) * (u ^ k * Real.exp (-(s + l) * u) / (k.factorial : ℝ)) := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      change 0 ≤ Real.exp (-(l * V)) * (u ^ k * Real.exp (-(s - l) * u) / (k.factorial : ℝ)) +
        Real.exp (l * U) * (u ^ k * Real.exp (-(s + l) * u) / (k.factorial : ℝ))
      positivity
  have hpow : ∀ (k : ℕ) {σ a x c : ℝ}, 0 < σ → 0 < a → x + k * ((σ - a) / a) ≤ c →
      Real.exp x * (a ^ (k + 1))⁻¹ ≤ Real.exp c / a / σ ^ k := by
    intro k σ a x c hσ ha h
    have h1 : σ / a ≤ Real.exp ((σ - a) / a) := by
      have := Real.add_one_le_exp ((σ - a) / a)
      have e : (σ - a) / a + 1 = σ / a := by field_simp; ring
      linarith
    have h2 : (σ / a) ^ k ≤ Real.exp (k * ((σ - a) / a)) := by
      rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) h1 k
    have h3 : Real.exp x * (σ / a) ^ k ≤ Real.exp c :=
      (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le).trans
        (by rw [← Real.exp_add]; exact Real.exp_le_exp.2 h)
    calc _ = Real.exp x * (σ / a) ^ k / a / σ ^ k := by rw [div_pow, pow_succ]; field_simp
      _ ≤ _ := by gcongr
  set l : ℝ := 2 + 6 / δ with hl_def
  have hl2 : 2 < l := by
    have : 0 < 6 / δ := by positivity
    rw [hl_def]; linarith
  have hl : l * δ = 6 + 2 * δ := by rw [hl_def]; field_simp; ring
  set M : ℝ := l * (1 + δ) with hM_def
  have hMl : l < M := by rw [hM_def]; nlinarith
  set σ : ℝ := M * (2 + l) with hσ_def
  have hσ1 : l * (2 + l) < σ := by rw [hσ_def]; gcongr
  have hs : l < σ - 2 := by nlinarith
  have ha : 0 < σ - 2 - l := by linarith
  have hb : 0 < σ - 2 + l := by linarith
  have hσ0 : 0 < σ := by linarith
  refine ⟨σ, by linarith, Real.exp 1 / (σ - 2 - l) + Real.exp 0 / (σ - 2 + l), fun U hU => ?_⟩
  have hx : 0 ≤ (1 + δ / 2) * σ * U := by positivity
  set k := ⌈(1 + δ / 2) * σ * U⌉₊
  have hk1 : (1 + δ / 2) * σ * U ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) ≤ (1 + δ / 2) * σ * U + 1 := (Nat.ceil_lt_add_one hx).le
  refine ⟨k, by nlinarith [mul_nonneg hδ.le (by positivity : 0 ≤ σ * U)], ?_⟩
  rw [show (2 - σ) = -(σ - 2) by ring, add_div]
  refine (hchernoff k (by linarith) hs).trans (add_le_add ?_ ?_)
  · apply hpow k hσ0 ha
    have e1 : (σ - (σ - 2 - l)) / (σ - 2 - l) = 1 / (M - 1) := by
      have : 0 < M - 1 := by linarith
      rw [div_eq_div_iff ha.ne' this.ne', hσ_def]; ring
    have e2 : (1 + δ / 2) * σ = M * (M - 1) := by
      have : (1 + δ / 2) * (2 + l) = M - 1 := by rw [hM_def]; nlinarith
      rw [hσ_def]; nlinarith
    have e3 : (k : ℝ) * (1 / (M - 1)) ≤ M * U + 1 := by
      rw [mul_one_div, div_le_iff₀ (by linarith : 0 < M - 1)]
      rw [e2] at hk2; nlinarith
    have e4 : l * ((1 + δ) * U) = M * U := by rw [hM_def]; ring
    rw [e1, e4]; linarith
  · apply hpow k hσ0 hb
    have e1 : (k : ℝ) * ((σ - (σ - 2 + l)) / (σ - 2 + l)) = -((k : ℝ) * (l - 2) / (σ - 2 + l)) := by
      ring
    have e2 : (1 + δ / 2) * (l - 2) = l + 1 := by nlinarith
    have e3 : l * U ≤ (k : ℝ) * (l - 2) / (σ - 2 + l) := by
      rw [le_div_iff₀ hb]
      have h1 : (1 + δ / 2) * σ * U * (l - 2) ≤ k * (l - 2) :=
        mul_le_mul_of_nonneg_right hk1 (by linarith)
      have h2 : (1 + δ / 2) * σ * U * (l - 2) = (l + 1) * σ * U := by rw [← e2]; ring
      have h3 : l * (σ - 2 + l) ≤ (l + 1) * σ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h3 (by linarith : 0 ≤ U)]
    rw [e1]; linarith

private lemma landau_window_ineq {g R : ℝ → ℝ} (hg : Measurable g) {C₀ : ℝ}
    (hC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C₀ * Real.exp (2 * u)) {σ θ U V : ℝ}
    (hσ : 2 < σ) (hθ : θ < σ) (hU : 0 < U)
    (hR : IntegrableOn (fun u => R u * Real.exp (-θ * u)) (Icc U V))
    (hR' : ∀ u ∈ Icc U V, 0 ≤ R u ∧ g u ≤ R u) (k : ℕ) (γ : ℝ) :
    ‖∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) / (k.factorial : ℂ)‖ ≤
      2 * (1 / (σ - θ) ^ k) * (∫ u in Icc U V, R u * Real.exp (-θ * u)) -
        (∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)).re +
        2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) := by
  set w : ℝ → ℝ := fun u => u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ)
  set h : ℝ → ℝ := fun u => u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ)
  have hhi : IntegrableOn h (Ioi 0) :=
    IntegrableOn.congr_fun ((integrable_kernel k (σ - 2) (by linarith)).div_const (k.factorial : ℝ))
      (fun u _ => by simp only [h]; rw [show -(σ - 2) * u = (2 - σ) * u by ring]) measurableSet_Ioi
  have hw0 : ∀ u, 0 ≤ u → 0 ≤ w u := fun u hu => by simp only [w]; positivity
  have hwm : Measurable w := by simp only [w]; fun_prop
  have hb : ∀ u, 0 ≤ u → |g u| * w u ≤ C₀ * h u := fun u hu => by
    have e : C₀ * h u = C₀ * Real.exp (2 * u) * w u := by
      simp only [w, h]; rw [show (2 - σ) * u = 2 * u + -σ * u by ring, Real.exp_add]; ring
    rw [e]; exact mul_le_mul_of_nonneg_right (hC u hu) (hw0 u hu)
  have hI1 : IntegrableOn (fun u => |g u| * w u) (Ioi 0) := by
    refine Integrable.mono' (hhi.const_mul C₀) ((continuous_abs.measurable.comp hg).mul hwm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 ≤ u := le_of_lt hu
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hw0 u hu0))]; exact hb u hu0
  have hI2 : IntegrableOn (fun u => g u * w u) (Ioi 0) := by
    refine Integrable.mono' (hhi.const_mul C₀) (hg.mul hwm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 ≤ u := le_of_lt hu
    rw [norm_mul, Real.norm_of_nonneg (hw0 u hu0), Real.norm_eq_abs]; exact hb u hu0
  have hL : ‖∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) / (k.factorial : ℂ)‖
      ≤ ∫ u in Ioi (0 : ℝ), |g u| * w u := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 ≤ u := le_of_lt hu
    have hre : (-((σ : ℂ) + γ * I) * u).re = -σ * u := by simp
    simp only [w, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, hre,
      Complex.norm_natCast, Real.norm_eq_abs, abs_of_nonneg hu0]
    ring
  have hM : (∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)).re
      = ∫ u in Ioi (0 : ℝ), g u * w u := by
    have : (fun u : ℝ => (g u : ℂ) * (u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ))
        = fun u : ℝ => ((g u * w u : ℝ) : ℂ) := by
      funext u; simp only [w]; push_cast; ring
    rw [this, integral_complex_ofReal, Complex.ofReal_re]
  have hI3 : IntegrableOn (fun u => |g u| * w u + g u * w u) (Ioi 0) := hI1.add hI2
  have hsub : Icc U V ⊆ Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le hU hu.1
  have hsplit := integral_inter_add_sdiff (μ := volume) (s := Ioi (0 : ℝ)) (t := Icc U V)
    measurableSet_Icc hI3
  rw [inter_eq_right.2 hsub, integral_add hI1 hI2] at hsplit
  have hA : ∫ u in Icc U V, (|g u| * w u + g u * w u)
      ≤ 2 * (1 / (σ - θ) ^ k) * (∫ u in Icc U V, R u * Real.exp (-θ * u)) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (IntegrableOn.mono_set hI3 hsub) (hR.const_mul _) measurableSet_Icc fun u hu => ?_
    have hu0 : 0 ≤ u := le_of_lt (hsub hu)
    obtain ⟨h1, h2⟩ := hR' u hu
    have h3 : |g u| + g u ≤ 2 * R u := by rcases abs_cases (g u) with h | h <;> linarith [h.1]
    have h4 : w u ≤ 1 / (σ - θ) ^ k * Real.exp (-θ * u) := by
      have h5 := kernel_max k (sub_pos.2 hθ) hu0
      have h6 : w u = (u ^ k * Real.exp (-(σ - θ) * u) / (k.factorial : ℝ)) * Real.exp (-θ * u) := by
        simp only [w]; rw [show -σ * u = -(σ - θ) * u + -θ * u by ring, Real.exp_add]; ring
      rw [h6]; exact mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    calc |g u| * w u + g u * w u = (|g u| + g u) * w u := by ring
      _ ≤ (2 * R u) * w u := mul_le_mul_of_nonneg_right h3 (hw0 u hu0)
      _ ≤ (2 * R u) * (1 / (σ - θ) ^ k * Real.exp (-θ * u)) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
      _ = _ := by ring
  have hB : ∫ u in Ioi (0 : ℝ) \ Icc U V, (|g u| * w u + g u * w u)
      ≤ 2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, h u := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (IntegrableOn.mono_set hI3 sdiff_subset)
      ((IntegrableOn.mono_set hhi sdiff_subset).const_mul _)
      (measurableSet_Ioi.diff measurableSet_Icc) fun u hu => ?_
    have hu0 : 0 ≤ u := le_of_lt hu.1
    have h1 := hb u hu0
    have h2 : g u * w u ≤ |g u| * w u := mul_le_mul_of_nonneg_right (le_abs_self _) (hw0 u hu0)
    linarith
  rw [hM]; linarith

private lemma landau_cauchy {Φ : ℂ → ℂ} {z : ℂ} {r r' : ℝ}
    (hd : DifferentiableOn ℂ Φ (Metric.ball z r)) (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k Φ z / (k.factorial : ℂ)‖ ≤ M / r' ^ k := by
  set R : NNReal := ⟨r', h0.le⟩
  refine ⟨(2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖Φ (circleMap z r' θ)‖, fun k => ?_⟩
  have hp := (hd.mono (Metric.closedBall_subset_ball h1)).hasFPowerSeriesOnBall (show (0 : NNReal) < R from h0)
  have key := hp.factorial_smul (1 : ℂ) k
  have hderiv : iteratedDeriv k Φ z / (k.factorial : ℂ) = cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← key, nsmul_eq_mul]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [hderiv]
  calc ‖cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1)‖
      ≤ ‖cauchyPowerSeries Φ z (R : ℝ) k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries Φ z (R : ℝ) k‖ := by simp
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖Φ (circleMap z (R : ℝ) θ)‖) * |(R : ℝ)|⁻¹ ^ k :=
        norm_cauchyPowerSeries_le _ _ _ _
    _ = _ := by show _ = _ / r' ^ k; rw [show (R : ℝ) = r' from rfl, abs_of_pos h0, inv_pow, div_eq_mul_inv]

private lemma landau_pole_asym {Φ : ℂ → ℂ} {z ρ c : ℂ} {r r' : ℝ}
    (_hρ : ρ ∈ Metric.ball z r) (hne : ρ ≠ z) (hd : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}))
    (hp : ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s)
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ,
      ‖(-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ) - c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨hfun, han, hev⟩ := hp
  have hopen : IsOpen (Metric.ball z r \ {ρ}) := Metric.isOpen_ball.sdiff isClosed_singleton
  set G : ℂ → ℂ := fun s => if s = ρ then hfun ρ else Φ s - c / (s - ρ)
  have hGeq : G =ᶠ[𝓝 ρ] hfun := by
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]; simp [G]
    · simp only [G, if_neg hsρ]; rw [hs (Set.mem_compl_singleton_iff.mpr hsρ)]; ring
  have hGd : DifferentiableOn ℂ G (Metric.ball z r) := by
    intro s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]; exact ((hGeq.differentiableAt_iff).mpr han.differentiableAt).differentiableWithinAt
    · have hmem : s ∈ Metric.ball z r \ {ρ} := ⟨hs, hsρ⟩
      have hΦ : DifferentiableAt ℂ Φ s := (hd s hmem).differentiableAt (hopen.mem_nhds hmem)
      have hloc : G =ᶠ[𝓝 s] fun t => Φ t - c / (t - ρ) := by
        filter_upwards [hopen.mem_nhds hmem] with t ht
        have htρ : t ≠ ρ := ht.2
        simp only [G, if_neg htρ]
      have hd' : DifferentiableAt ℂ (fun t => Φ t - c / (t - ρ)) s :=
        hΦ.sub ((differentiableAt_const c).div
          (differentiableAt_id.sub (differentiableAt_const ρ)) (sub_ne_zero.mpr hsρ))
      exact ((hloc.differentiableAt_iff).mpr hd').differentiableWithinAt
  obtain ⟨M, hM⟩ := landau_cauchy hGd h0 h1
  refine ⟨M, fun k => ?_⟩
  have hzρ : z ≠ ρ := Ne.symm hne
  have hr : 0 < r := lt_trans h0 h1
  have hloc : Φ =ᶠ[𝓝 z] G + fun s => c * (s - ρ)⁻¹ := by
    filter_upwards [hopen.mem_nhds ⟨Metric.mem_ball_self hr, hzρ⟩] with t ht
    have htρ : t ≠ ρ := ht.2
    simp only [Pi.add_apply, G, if_neg htρ, div_eq_mul_inv]; ring
  have hGc : ContDiffAt ℂ k G z :=
    (hGd.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hPc : ContDiffAt ℂ k (fun s => c * (s - ρ)⁻¹) z :=
    contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hzρ))
  have hderiv : iteratedDeriv k (fun s : ℂ => c * (s - ρ)⁻¹) z =
      c * ((-1) ^ k * (k.factorial : ℂ) * ((z - ρ) ^ (k + 1))⁻¹) := by
    rw [iteratedDeriv_const_mul_field]; congr 1
    have e := congrFun (iteratedDeriv_comp_sub_const k (fun t : ℂ => t⁻¹) ρ) z
    rw [e, iteratedDeriv_eq_iterate, show (fun t : ℂ => t⁻¹) = Inv.inv from rfl, iter_deriv_inv,
      show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [hloc.iteratedDeriv_eq, iteratedDeriv_add hGc hPc, hderiv]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpow : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  set iG := iteratedDeriv k G z
  set X := (z - ρ) ^ (k + 1)
  have e : (-1) ^ k * (iG + c * ((-1) ^ k * (k.factorial : ℂ) * X⁻¹)) / (k.factorial : ℂ) - c / X
      = (-1) ^ k * (iG / k.factorial) := by
    calc _ = (-1) ^ k * (iG / k.factorial) + ((-1) ^ k * (-1) ^ k) * c *
          ((k.factorial : ℂ) / k.factorial) * X⁻¹ - c / X := by ring
      _ = _ := by rw [hpow, div_self hfac, div_eq_mul_inv c]; ring
  rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hM k

private lemma landau_pole_re_le {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) :
    ∀ ρ ∈ Z, ρ.re ≤ 2 := by
  intro ρ hρ
  by_contra hlt
  have hlt : 2 < ρ.re := not_le.mp hlt
  obtain ⟨C, hC⟩ := hP.growth
  set σ := (2 + ρ.re) / 2 with hσ_def
  have hσ : 2 < σ := by rw [hσ_def]; linarith
  have hM : ∀ s : ℂ, σ ≤ s.re → ‖Φ s‖ ≤ ∫ u in Ioi (0 : ℝ), C * Real.exp (-(σ - 2) * u) := by
    intro s hs
    rw [hP.laplace s (lt_of_lt_of_le hσ hs)]
    refine norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hσ)).const_mul C) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have h1 := hC u hu0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      show (-s * (u : ℂ)).re = -s.re * u by simp]
    calc |g u| * Real.exp (-s.re * u) ≤ (C * Real.exp (2 * u)) * Real.exp (-σ * u) :=
          mul_le_mul h1 (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le ((abs_nonneg _).trans h1)
      _ = C * Real.exp (-(σ - 2) * u) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  obtain ⟨c, hc, -, h, hh, hev⟩ := hP.pole ρ hρ
  have h0 : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)) := tendsto_id.sub_const ρ
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ s in 𝓝[≠] ρ, ‖Φ s‖ ≤ ∫ u in Ioi (0 : ℝ), C * Real.exp (-(σ - 2) * u) := by
    have hσlt : σ < ρ.re := by rw [hσ_def]; linarith
    have := Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hσlt)
    filter_upwards [this.filter_mono nhdsWithin_le_nhds] with s hs using hM s hs.le
  have h1 : Tendsto (fun s : ℂ => (s - ρ) * Φ s) (𝓝[≠] ρ) (𝓝 0) :=
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded h0 ⟨_, eventually_map.mpr hb⟩
  have h2 : Tendsto (fun s : ℂ => c + (s - ρ) * h s) (𝓝[≠] ρ) (𝓝 (c + 0 * h ρ)) :=
    (h0.mul (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).const_add c
  have h3 : (fun s : ℂ => (s - ρ) * Φ s) =ᶠ[𝓝[≠] ρ] fun s : ℂ => c + (s - ρ) * h s := by
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hne
    have : s - ρ ≠ 0 := sub_ne_zero.mpr hne; rw [hs]; field_simp
  exact hc (by simpa using (tendsto_nhds_unique (h1.congr' h3) h2).symm)

private lemma landau_finite {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    {z : ℂ} {r : ℝ} (hr : r < z.re) : (Z ∩ Metric.closedBall z r).Finite := by
  have hpos : ∀ w ∈ Metric.closedBall z r, 0 < w.re := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by simpa [dist_eq_norm] using hw
    have h3 := (abs_le.mp ((Complex.abs_re_le_norm _).trans h1)).1
    simp only [Complex.sub_re] at h3; linarith
  obtain ⟨t, -, ht⟩ := (isCompact_closedBall z r).elim_nhds_subcover
    (fun w => {v | v ∈ ({w}ᶜ : Set ℂ) → v ∉ Z})
    (fun w hw => eventually_nhdsWithin_iff.mp (hiso w (hpos w hw)))
  refine t.finite_toSet.subset ?_
  rintro v ⟨hvZ, hvK⟩
  obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.mp (ht hvK)
  by_cases h : v = w
  · exact h ▸ hw
  · exact absurd hvZ (hvw h)

private lemma landau_dichotomy {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    {σ θ : ℝ} (hθ : 0 < θ) {ρ₀ : ℂ} (h₀ : ρ₀ ∈ Z) (hρ₀ : θ < ρ₀.re) :
    (∃ D : ℝ, D ≤ σ - θ ∧ (∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) D) ∧ ∃ ρ₁ ∈ Z, σ - ρ₁.re < D) ∨
    (∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ ∃ r : ℝ, σ - β < r ∧ r ≤ σ - θ ∧
      ∀ w ∈ Z, w ∈ Metric.ball (σ : ℂ) r → w = β) := by
  have hfin : (Z ∩ Metric.closedBall (σ : ℂ) (σ - θ)).Finite :=
    landau_finite hiso (by rw [Complex.ofReal_re]; linarith)
  set F := Z ∩ Metric.closedBall (σ : ℂ) (σ - θ)
  rcases F.eq_empty_or_nonempty with hF | hF
  · left; refine ⟨σ - θ, le_rfl, ?_, ρ₀, h₀, by linarith⟩
    intro w hw hb; have : w ∈ F := ⟨hw, Metric.ball_subset_closedBall hb⟩; rwa [hF] at this
  · obtain ⟨ρs, hρsF, hmin⟩ := Set.exists_min_image F (fun w => dist w (σ : ℂ)) hfin hF
    have hdle : dist ρs (σ : ℂ) ≤ σ - θ := Metric.mem_closedBall.mp hρsF.2
    have hball : ∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) (dist ρs (σ : ℂ)) := by
      intro w hw hb; rw [Metric.mem_ball] at hb
      have := hmin w ⟨hw, Metric.mem_closedBall.mpr (by linarith)⟩; linarith
    by_cases hex : ∃ ρ₁ ∈ Z, σ - ρ₁.re < dist ρs (σ : ℂ)
    · exact Or.inl ⟨dist ρs (σ : ℂ), hdle, hball, hex⟩
    · right; push Not at hex
      set d := dist ρs (σ : ℂ)
      have hreal : ∀ w ∈ F, dist w (σ : ℂ) = d → w = ((σ - d : ℝ) : ℂ) := by
        intro w hw he
        have h1 : dist w (σ : ℂ) ≤ d := he.le
        have h2 : d ≤ σ - w.re := hex w hw.1
        have hD0 : 0 ≤ d := dist_nonneg.trans h1
        rw [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im] at h1
        have hq : (w.re - σ) ^ 2 + (w.im - 0) ^ 2 ≤ d ^ 2 := by
          have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (w.re - σ) ^ 2 + (w.im - 0) ^ 2)
          have h0 := Real.sqrt_nonneg ((w.re - σ) ^ 2 + (w.im - 0) ^ 2); nlinarith
        apply Complex.ext
        · rw [Complex.ofReal_re]; nlinarith [sq_nonneg w.im]
        · rw [Complex.ofReal_im]; nlinarith [sq_nonneg w.im]
      have hρs := hreal ρs hρsF rfl
      have hdlt : d < σ - θ := lt_of_le_of_ne hdle fun h => by linarith [hex ρ₀ h₀]
      refine ⟨σ - d, hρs ▸ hρsF.1, by linarith, ?_⟩
      have hT : ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, d < dist t (σ : ℂ) := fun t ht =>
        lt_of_le_of_ne (hmin t ht.1) fun h => ht.2 (hreal t ht.1 h.symm)
      obtain ⟨r, hr, hrT⟩ : ∃ r, d < r ∧ ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, r ≤ dist t (σ : ℂ) := by
        rcases (F \ {((σ - d : ℝ) : ℂ)}).eq_empty_or_nonempty with hTe | hTne
        · exact ⟨d + 1, by linarith, fun t ht => by rw [hTe] at ht; exact absurd ht (Set.notMem_empty t)⟩
        · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {((σ - d : ℝ) : ℂ)})
            (fun w => dist w (σ : ℂ)) (hfin.subset Set.sdiff_subset) hTne
          exact ⟨dist t₀ (σ : ℂ), hT t₀ ht₀, htmin⟩
      refine ⟨min r (σ - θ), by rw [sub_sub_cancel]; exact lt_min hr hdlt, min_le_right _ _, ?_⟩
      intro w hw hb; rw [Metric.mem_ball] at hb
      have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr (le_trans hb.le (min_le_right _ _))⟩
      by_contra hne
      linarith [hrT w ⟨hwF, hne⟩, min_le_left r (σ - θ)]

private lemma landau_nearest {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    {σ D : ℝ} (hle : ∀ ρ ∈ Z, ρ.re < σ) (hD : D < σ) {ρ₁ : ℂ} (h₁ : ρ₁ ∈ Z) (hρ₁ : σ - ρ₁.re < D) :
    ∃ γ : ℝ, ∃ ρ ∈ Z, ∃ r : ℝ, ‖(σ : ℂ) + γ * I - ρ‖ < r ∧ r ≤ D ∧
      ∀ w ∈ Z, w ∈ Metric.ball ((σ : ℂ) + γ * I) r → w = ρ := by
  set ε : ℝ := min (D - (σ - ρ₁.re)) (σ - D) / 2 with hε_def
  have hε0 : 0 < ε := by
    rw [hε_def]; have := lt_min (show 0 < D - (σ - ρ₁.re) by linarith) (show 0 < σ - D by linarith); linarith
  have hε1 : ε ≤ (D - (σ - ρ₁.re)) / 2 := by
    rw [hε_def]; have := min_le_left (D - (σ - ρ₁.re)) (σ - D); linarith
  have hε2 : ε ≤ (σ - D) / 2 := by
    rw [hε_def]; have := min_le_right (D - (σ - ρ₁.re)) (σ - D); linarith
  set c₀ : ℂ := (σ : ℂ) + ρ₁.im * I
  have hF : (Z ∩ Metric.closedBall c₀ (D + ε)).Finite :=
    landau_finite hiso (by simp only [c₀, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_zero, add_zero]; linarith)
  set F := Z ∩ Metric.closedBall c₀ (D + ε)
  set B : Set ℝ := (fun p : ℂ × ℂ =>
      ((σ - p.1.re) ^ 2 + p.1.im ^ 2 - (σ - p.2.re) ^ 2 - p.2.im ^ 2) / (2 * (p.1.im - p.2.im))) ''
      (F ×ˢ F)
  have hBfin : B.Finite := (hF.prod hF).image _
  obtain ⟨γ, hγI, hγB⟩ := ((Set.Ioo_infinite (show ρ₁.im - ε < ρ₁.im + ε by linarith)).sdiff hBfin).nonempty
  set c : ℂ := (σ : ℂ) + γ * I
  have hγε : |γ - ρ₁.im| < ε := abs_sub_lt_iff.mpr ⟨by linarith [hγI.2], by linarith [hγI.1]⟩
  have hcc₀ : ‖c - c₀‖ = |γ - ρ₁.im| := by
    have e : c - c₀ = ((γ - ρ₁.im : ℝ) : ℂ) * I := by simp only [c, c₀]; push_cast; ring
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hc₀ρ₁ : ‖c₀ - ρ₁‖ = σ - ρ₁.re := by
    have e : c₀ - ρ₁ = ((σ - ρ₁.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [c₀]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (hle ρ₁ h₁))]
  have hρ₁F : ρ₁ ∈ F := ⟨h₁, by rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, hc₀ρ₁]; linarith⟩
  obtain ⟨ρ, hρF, hmin⟩ := Set.exists_min_image F (fun w => ‖c - w‖) hF ⟨ρ₁, hρ₁F⟩
  have hρ₁c : ‖c - ρ₁‖ < D := by
    have := norm_add_le (c - c₀) (c₀ - ρ₁); rw [sub_add_sub_cancel, hcc₀, hc₀ρ₁] at this; linarith
  have hm : ‖c - ρ‖ ≤ ‖c - ρ₁‖ := hmin ρ₁ hρ₁F
  have hT : ∀ w ∈ F \ {ρ}, ‖c - ρ‖ < ‖c - w‖ := by
    intro w hw
    refine lt_of_le_of_ne (hmin w hw.1) fun heq => hw.2 ?_
    have h2 : ‖c - w‖ ^ 2 = ‖c - ρ‖ ^ 2 := by rw [heq]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
    simp only [c, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at h2
    have him : w.im = ρ.im := by
      by_contra hne
      apply hγB
      refine ⟨(w, ρ), ⟨hw.1, hρF⟩, ?_⟩
      have hne' : 2 * (w.im - ρ.im) ≠ 0 := by have := sub_ne_zero.mpr hne; positivity
      exact ((eq_div_iff hne').mpr (by linear_combination -h2)).symm
    have hsq : (ρ.re - w.re) * ((σ - w.re) + (σ - ρ.re)) = 0 := by rw [him] at h2; linear_combination h2
    rcases mul_eq_zero.mp hsq with h3 | h3
    · exact Complex.ext (by linarith) him
    · exfalso; linarith [hle w hw.1.1, hle ρ hρF.1]
  obtain ⟨r, hr, hrT⟩ : ∃ r, ‖c - ρ‖ < r ∧ ∀ t ∈ F \ {ρ}, r ≤ ‖c - t‖ := by
    rcases (F \ {ρ}).eq_empty_or_nonempty with hTe | hTne
    · exact ⟨‖c - ρ‖ + 1, by linarith, fun t ht => by rw [hTe] at ht; exact absurd ht (Set.notMem_empty t)⟩
    · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {ρ}) (fun w => ‖c - w‖)
        (hF.subset Set.sdiff_subset) hTne
      exact ⟨‖c - t₀‖, hT t₀ ht₀, htmin⟩
  refine ⟨γ, ρ, hρF.1, min r D, lt_min hr (by linarith), min_le_right _ _, ?_⟩
  intro w hw hb
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hb
  have hwF : w ∈ F := ⟨hw, by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have := norm_add_le (w - c) (c - c₀)
    rw [sub_add_sub_cancel, norm_sub_rev w c, hcc₀] at this
    linarith [min_le_right r D]⟩
  by_contra hne
  linarith [hrT w ⟨hwF, hne⟩, min_le_left r D]

private lemma landau_window_contra {c d e E M C : ℝ} (hc : 0 < c) (hd : 0 < d) (hde : d < e)
    (heE : e ≤ E)
    (H : ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ k : ℕ, U ≤ k ∧
      c / d ^ k ≤ M / e ^ k + C * Real.exp (η * U) / E ^ k) : False := by
  have he : 0 < e := hd.trans hde
  have hL : 0 < Real.log (e / d) := Real.log_pos ((one_lt_div hd).mpr hde)
  set L := Real.log (e / d)
  set C' := |M| + |C|
  obtain ⟨U, hU, k, hk, hle⟩ := H (L / 2) (by positivity) (max (2 * |C'| / (c * L)) 0)
  have hU0 : 0 ≤ U := (le_max_right _ _).trans hU
  have hU1 : 2 * |C'| / (c * L) ≤ U := (le_max_left _ _).trans hU
  have hdk : 0 < d ^ k := pow_pos hd k
  have hek : 0 < e ^ k := pow_pos he k
  have hexp : 1 ≤ Real.exp (L / 2 * U) := Real.one_le_exp (by positivity)
  have h1 : C' * Real.exp (L / 2 * U) / e ^ k < c / d ^ k := by
    have hpow : e ^ k = d ^ k * Real.exp (k * L) := by
      rw [Real.exp_nat_mul, Real.exp_log (div_pos he hd), div_pow, mul_div_cancel₀ _ hdk.ne']
    rw [div_lt_div_iff₀ hek hdk, hpow]
    set X := Real.exp (L / 2 * U)
    have hXpos : 0 < X := Real.exp_pos _
    rw [div_le_iff₀ (mul_pos hc hL)] at hU1
    have hX : |C'| < c * X := by nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (L / 2 * U)) hc.le]
    have hY : X * X ≤ Real.exp (k * L) := by
      simp only [X]; rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hk hL.le])
    have hCX : C' * X * d ^ k ≤ |C'| * X * d ^ k := by nlinarith [le_abs_self C', mul_pos hXpos hdk]
    calc C' * X * d ^ k ≤ |C'| * X * d ^ k := hCX
      _ < c * Real.exp (k * L) * d ^ k :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le (by nlinarith) (mul_le_mul_of_nonneg_left hY hc.le)) hdk
      _ = c * (d ^ k * Real.exp (k * L)) := by ring
  have h2 : M / e ^ k ≤ |M| * Real.exp (L / 2 * U) / e ^ k :=
    div_le_div_of_nonneg_right ((le_abs_self M).trans (le_mul_of_one_le_right (abs_nonneg M) hexp)) hek.le
  have h3 : C * Real.exp (L / 2 * U) / E ^ k ≤ |C| * Real.exp (L / 2 * U) / e ^ k :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
      hek (pow_le_pow_left₀ he.le heE k)
  have h4 : C' * Real.exp (L / 2 * U) / e ^ k =
      |M| * Real.exp (L / 2 * U) / e ^ k + |C| * Real.exp (L / 2 * U) / e ^ k := by simp only [C']; ring
  linarith

/-- **Windowed Landau Nonvanishing Theorem**: if `g` has meromorphic Laplace transform `Φ` with
poles `Z` (positive real residue at real poles) and satisfies a windowed upper bound `WindowHypU g θ δ`,
then no pole `ρ ∈ Z` has `Re(ρ) > θ`. -/
theorem landau_window {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hW : WindowHypU g θ δ) : ∀ ρ ∈ Z, ρ.re ≤ θ := by
  have hre_pos : ∀ {z w : ℂ} {r : ℝ}, r ≤ z.re → w ∈ Metric.ball z r → 0 < w.re := by
    intro z w r hr hw
    have h1 : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
    have h3 := (abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt h1)).1
    simp only [Complex.sub_re] at h3; linarith
  have hkey : ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ k : ℕ, U ≤ k ∧
      ∀ γ : ℝ, ‖(-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + γ * I) / (k.factorial : ℂ)‖ +
        ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)).re ≤
        C * Real.exp (η * U) / (σ - θ) ^ k := by
    obtain ⟨σ, hσ, C, hC⟩ := landau_tails hδ
    obtain ⟨C₀, hC₀⟩ := hP.growth
    have hC₀0 : 0 ≤ C₀ := by
      have := hC₀ 0 le_rfl; simp only [mul_zero, Real.exp_zero, mul_one] at this
      exact (abs_nonneg _).trans this
    refine ⟨σ, hσ, 2 + 2 * C₀ * |C|, fun η hη U₀ => ?_⟩
    obtain ⟨U, hU, R, hR1, hR2, hR3⟩ := hW η hη (max U₀ 1)
    have hU1 : 1 ≤ U := (le_max_right _ _).trans hU
    obtain ⟨k, hk, hk'⟩ := hC U hU1
    refine ⟨U, (le_max_left _ _).trans hU, k, hk, fun γ => ?_⟩
    have h := landau_window_ineq hP.meas hC₀ hσ (by linarith : θ < σ) (by linarith : 0 < U) hR1 hR2 k γ
    rw [landau_coeff hP k (s := (σ : ℂ) + γ * I) (by simpa using hσ),
      landau_coeff hP k (s := (σ : ℂ)) (by simpa using hσ)]
    have hst : 0 < σ - θ := by linarith
    have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
    have h1 : 2 * (1 / (σ - θ) ^ k) * (∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u))
        ≤ 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U) := mul_le_mul_of_nonneg_left hR3 (by positivity)
    have h2 : C / σ ^ k ≤ |C| * Real.exp (η * U) / (σ - θ) ^ k :=
      div_le_div₀ (by positivity) ((le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hexp))
        (pow_pos hst k) (pow_le_pow_left₀ hst.le (by linarith) k)
    have h3 := mul_le_mul_of_nonneg_left (hk'.trans h2) (by positivity : 0 ≤ 2 * C₀)
    have h4 : (2 + 2 * C₀ * |C|) * Real.exp (η * U) / (σ - θ) ^ k
        = 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U)
          + 2 * C₀ * (|C| * Real.exp (η * U) / (σ - θ) ^ k) := by ring
    linarith
  intro ρ₀ h₀
  by_contra hρ₀
  rw [not_le] at hρ₀
  obtain ⟨σ, hσ, C, hkey⟩ := hkey
  have hle : ∀ ρ ∈ Z, ρ.re < σ := fun ρ hρ => (landau_pole_re_le hP ρ hρ).trans_lt hσ
  rcases landau_dichotomy hP.iso hθ h₀ hρ₀ with
    ⟨D, hD, hfree, ρ₁, h₁, hρ₁⟩ | ⟨β, hβZ, hβ, r, hr1, hr2, huniq⟩
  · obtain ⟨γ, ρ, hρ, r, hr1, hr2, huniq⟩ := landau_nearest hP.iso hle (by linarith : D < σ) h₁ hρ₁
    obtain ⟨c, hc, -, hp⟩ := hP.pole ρ hρ
    set z : ℂ := (σ : ℂ) + γ * I
    have hzre : z.re = σ := by simp [z]
    have hne : ρ ≠ z := fun h => lt_irrefl _ (by have := hle ρ hρ; rwa [h, hzre] at this)
    set d := ‖z - ρ‖
    have hd : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
    have hball : ρ ∈ Metric.ball z r := by rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hr1
    have hdiff : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}) :=
      hP.diff.mono fun w ⟨hw, hw'⟩ => ⟨hre_pos (by rw [hzre]; linarith) hw, fun hZ => hw' (huniq w hZ hw)⟩
    have hdiff' : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) D) :=
      hP.diff.mono fun w hw => ⟨hre_pos (by rw [Complex.ofReal_re]; linarith) hw, fun hZ => hfree w hZ hw⟩
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (d + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
    obtain ⟨M', hM'⟩ := landau_cauchy (r' := (d + r) / 2) hdiff' (by linarith) (by linarith)
    refine landau_window_contra (c := ‖c‖ / d) (d := d) (e := (d + r) / 2) (E := σ - θ)
      (M := M + M') (C := C) (div_pos (norm_pos_iff.2 hc) hd) hd (by linarith) (by linarith)
      fun η hη U₀ => ?_
    obtain ⟨U, hU, k, hk, hb⟩ := hkey η hη U₀
    refine ⟨U, hU, k, hk, ?_⟩
    have h1 := hb γ; have h2 := hM k; have h3 := hM' k
    have h4 : ‖c / (z - ρ) ^ (k + 1)‖ = ‖c‖ / d / d ^ k := by
      rw [norm_div, norm_pow, pow_succ', div_div]
    have h5 : ‖(-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖
        = ‖iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖ := by
      rw [mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h6 := (abs_le.mp (Complex.abs_re_le_norm
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)))).1
    have h7 := norm_sub_norm_le (c / (z - ρ) ^ (k + 1))
      ((-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ))
    rw [norm_sub_rev] at h7; rw [add_div]; linarith
  · obtain ⟨c, -, hc, hp⟩ := hP.pole β hβZ
    obtain ⟨hc1, -⟩ := hc (Complex.ofReal_im β)
    have hd : 0 < σ - β := by have := hle β hβZ; rw [Complex.ofReal_re] at this; linarith
    have hne : (β : ℂ) ≠ (σ : ℂ) := fun h => by
      have : β = σ := by exact_mod_cast h
      linarith
    have hball : (β : ℂ) ∈ Metric.ball (σ : ℂ) r := by
      rw [Metric.mem_ball, dist_comm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hd]; exact hr1
    have hdiff : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) r \ {(β : ℂ)}) :=
      hP.diff.mono fun w ⟨hw, hw'⟩ =>
        ⟨hre_pos (by rw [Complex.ofReal_re]; linarith) hw, fun hZ => hw' (huniq w hZ hw)⟩
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (σ - β + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
    refine landau_window_contra (c := c.re / (σ - β)) (d := σ - β) (e := (σ - β + r) / 2)
      (E := σ - θ) (M := M) (C := C) (div_pos hc1 hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_
    obtain ⟨U, hU, k, hk, hb⟩ := hkey η hη U₀
    refine ⟨U, hU, k, hk, ?_⟩
    have h1 := hb 0; have h2 := hM k
    have h4 : (c / ((σ : ℂ) - β) ^ (k + 1)).re = c.re / (σ - β) / (σ - β) ^ k := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.div_ofReal_re, pow_succ', div_div]
    have h6 := (abs_le.mp (Complex.abs_re_le_norm
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ) - c / ((σ : ℂ) - β) ^ (k + 1)))).1
    rw [Complex.sub_re, h4] at h6
    have h7 := norm_nonneg ((-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + (0 : ℝ) * I) / (k.factorial : ℂ))
    linarith

/-! ## Part 2: `CharFamily` Mellin Continuation & `PoleData` -/

/-- Additive-variable Cesàro sum `gm F u = F.Gm (exp u)`. -/
def CharFamily.gm (F : CharFamily) (u : ℝ) : ℝ := F.Gm (Real.exp u)

/-- Right-half-plane zero set of `F` and its conjugates. -/
def CharFamily.zeroSet (F : CharFamily) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ∃ i, DirichletCharacter.LFunction (F.χ i) ρ = 0 ∨
    DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) ρ) = 0}

private lemma charFamily_LFunction_ne_zero_of_one_le_re (F : CharFamily) (i : F.ι) (s : ℂ)
    (hs : 1 ≤ s.re) : DirichletCharacter.LFunction (F.χ i) s ≠ 0 := by
  rcases F.adm i with h | h
  · have key : ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), M = 1 →
        DirichletCharacter.LFunction ψ s ≠ 0 := by
      intro M _ ψ hM; subst hM; rw [DirichletCharacter.LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re hs
    exact key _ (F.χ i) h
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl h) hs

private lemma measurable_floor_app (g : ℕ → ℝ → ℂ) (hg : ∀ k, Measurable (g k)) :
    Measurable (fun y : ℝ => g ⌊y⌋₊ y) := by
  have h : Measurable fun p : ℝ × ℕ => g p.2 p.1 :=
    measurable_from_prod_countable_left fun k => hg k
  exact h.comp (measurable_id.prodMk Nat.measurable_floor)

private lemma measurable_Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Measurable (Gchi χ) := by
  have hramp : ∀ f : ℕ → ℂ, Measurable (ramp f) := by
    intro f
    unfold ramp
    refine measurable_floor_app
      (fun k y => ∑ n ∈ Finset.range (k + 1),
        (Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)) fun k =>
      Finset.measurable_sum _ fun n _ =>
        measurable_const.mul (Complex.measurable_ofReal.comp
          (((measurable_id.div_const (n : ℝ)).sub measurable_const).max measurable_const))
  unfold Gchi
  split_ifs
  · exact ((hramp _).sub (Complex.measurable_ofReal.comp (measurable_id.mul Real.measurable_log))).add
      (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id))
  · exact (hramp _).add (Complex.measurable_ofReal.mul measurable_const)

private lemma Gchi_growth {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → ‖Gchi χ y‖ ≤ C * y ^ 2 := by
  have hramp : ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ {y : ℝ}, 1 ≤ y → ‖ramp f y‖ ≤ 2 * y ^ 2 := by
    intro f hf y hy
    have key : ∀ n ∈ Finset.range (⌊y⌋₊ + 1),
        ‖(Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)‖ ≤ y := by
      intro n _
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using (by linarith : (0 : ℝ) ≤ y)
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Real.norm_of_nonneg (le_max_right _ _)]
      calc _ ≤ (n : ℝ) * 1 * (y / n) := by
            gcongr
            · exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn'.le)
            · exact hf n
            · exact max_le (by linarith) (by positivity)
        _ = y := by field_simp
    have h := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ key)
    rw [Finset.card_range, nsmul_eq_mul] at h
    unfold ramp; refine h.trans ?_; push_cast; nlinarith [Nat.floor_le (by linarith : 0 ≤ y)]
  by_cases h : χ = 1
  · refine ⟨2 + 1 + |1 + Real.eulerMascheroniConstant|, fun y hy => ?_⟩
    have hr := hramp (fun n => χ n) (fun n => χ.norm_le_one _) hy
    have hy0 : 0 ≤ y := by linarith
    have hl : Real.log y ≤ y := Real.log_le_self hy0
    have hyy : y ≤ y ^ 2 := by nlinarith
    unfold Gchi; rw [if_pos h]
    refine (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans ?_)
    rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hy0 (Real.log_nonneg hy)),
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hy0]
    have h1 : y * Real.log y ≤ y ^ 2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left hyy (abs_nonneg (1 + Real.eulerMascheroniConstant))
    linarith
  · refine ⟨2 + ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖,
      fun y hy => ?_⟩
    have hr := hramp (fun n => χ n) (fun n => χ.norm_le_one _) hy
    have hy0 : 0 ≤ y := by linarith
    have hyy : y ≤ y ^ 2 := by nlinarith
    unfold Gchi; rw [if_neg h]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0]
    have h2 := mul_le_mul_of_nonneg_left hyy
      (norm_nonneg (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1))
    linarith

private lemma LFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by
  have hcpow : ∀ {x : ℝ}, 0 ≤ x → ∀ z : ℂ, (x : ℂ) ^ ((starRingEnd ℂ) z) = (starRingEnd ℂ) ((x : ℂ) ^ z) := by
    intro x hx z
    have h := Complex.conj_cpow (x : ℂ) ((starRingEnd ℂ) z)
      (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_pos.ne)
    rwa [Complex.conj_ofReal, Complex.conj_conj] at h
  have hGamma : ∀ z : ℂ, Gammaℝ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Gammaℝ z) := fun z => by
    rw [Gammaℝ, Gammaℝ, show -(starRingEnd ℂ) z / 2 = (starRingEnd ℂ) (-z / 2) by rw [map_div₀, map_neg, map_ofNat],
      show (starRingEnd ℂ) z / 2 = (starRingEnd ℂ) (z / 2) by rw [map_div₀, map_ofNat],
      hcpow Real.pi_pos.le, Complex.Gamma_conj, map_mul]
  have hpole : ∀ z : ℂ, 1 / ((starRingEnd ℂ) z - 1) / Gammaℝ ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (1 / (z - 1) / Gammaℝ z) := fun z => by rw [hGamma]; simp [map_div₀]
  have hhurw : ∀ (a : UnitAddCircle) (z : ℂ),
      HurwitzZeta.hurwitzZeta a ((starRingEnd ℂ) z) = (starRingEnd ℂ) (HurwitzZeta.hurwitzZeta a z) := by
    intro a z
    induction a using QuotientAddGroup.induction_on with
    | H b =>
      have hb : ((b : ℝ) : UnitAddCircle) = ((Int.fract b : ℝ) : UnitAddCircle) := by
        rw [QuotientAddGroup.eq]; exact ⟨-⌊b⌋, by simp only [Int.fract, zsmul_eq_mul, mul_one, Int.cast_neg]; ring⟩
      rw [hb]
      set a₀ : ℝ := Int.fract b
      have ha : a₀ ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩
      set reg : ℂ → ℂ := fun w => HurwitzZeta.hurwitzZeta (a₀ : UnitAddCircle) w - 1 / (w - 1) / Gammaℝ w
      have hdreg : Differentiable ℂ reg := fun w => by
        rcases eq_or_ne w 1 with rfl | hw
        · exact HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div _
        · have e : reg = fun t => HurwitzZeta.hurwitzZeta (a₀ : UnitAddCircle) t - (t - 1)⁻¹ * (Gammaℝ t)⁻¹ := by
            funext t; simp only [reg]; rw [one_div, div_eq_mul_inv]
          rw [e]
          exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hw).sub
            (((differentiableAt_id.sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hw)).mul (differentiable_Gammaℝ_inv w))
      have hreg : ∀ w : ℂ, 1 < w.re → (starRingEnd ℂ) (reg ((starRingEnd ℂ) w)) = reg w := by
        intro w hw
        have h1 : HurwitzZeta.hurwitzZeta (a₀ : UnitAddCircle) ((starRingEnd ℂ) w) =
            (starRingEnd ℂ) (HurwitzZeta.hurwitzZeta (a₀ : UnitAddCircle) w) := by
          have hw' : 1 < ((starRingEnd ℂ) w).re := by rwa [Complex.conj_re]
          rw [← (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ha hw').tsum_eq,
            ← (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ha hw).tsum_eq, Complex.conj_tsum]
          refine tsum_congr fun n => ?_
          rw [map_div₀, map_one, show ((n : ℂ) + (a₀ : ℂ)) = (((n : ℝ) + a₀ : ℝ) : ℂ) by push_cast; rfl,
            hcpow (add_nonneg (Nat.cast_nonneg n) ha.1)]
        have h2 := hpole w
        rw [show reg ((starRingEnd ℂ) w) = _ from rfl, map_sub, h1, h2, Complex.conj_conj, Complex.conj_conj]
      have hF : Differentiable ℂ (fun w => (starRingEnd ℂ) (reg ((starRingEnd ℂ) w))) :=
        fun w => differentiableAt_conj_conj_iff.mpr (hdreg _)
      have heq : (fun w => (starRingEnd ℂ) (reg ((starRingEnd ℂ) w))) = reg :=
        AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (hF.differentiableOn.analyticOnNhd isOpen_univ)
          (hdreg.differentiableOn.analyticOnNhd isOpen_univ)
          (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hreg)
      have h3 : (starRingEnd ℂ) (reg z) = reg ((starRingEnd ℂ) z) := by
        have := congrFun heq ((starRingEnd ℂ) z); rwa [Complex.conj_conj] at this
      have e : ∀ w, HurwitzZeta.hurwitzZeta (a₀ : UnitAddCircle) w = reg w + 1 / (w - 1) / Gammaℝ w :=
        fun w => by simp only [reg, sub_add_cancel]
      rw [e ((starRingEnd ℂ) z), e z, map_add, ← h3, hpole]
  simp only [DirichletCharacter.LFunction, ZMod.LFunction, map_mul, map_sum]
  congr 1
  · simpa using hcpow (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (-s)
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hhurw, ← MulChar.star_apply']; rfl

private lemma Gchi_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (starRingEnd ℂ) (Gchi χ y) = Gchi χ⁻¹ y := by
  have hramp : (starRingEnd ℂ) (ramp (fun n => χ n) y) = ramp (fun n => χ⁻¹ n) y := by
    unfold ramp; rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]; congr 2
    exact MulChar.star_apply' χ (n : ZMod N)
  by_cases h1 : χ = 1
  · subst h1; simp only [Gchi, inv_one, if_true]
    rw [map_add, map_sub, hramp, inv_one, Complex.conj_ofReal, Complex.conj_ofReal]
  · have h2 : χ⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.mp h)
    simp only [Gchi, h1, h2, if_false]
    have hL : DirichletCharacter.LFunction χ⁻¹ =
        (starRingEnd ℂ) ∘ DirichletCharacter.LFunction χ ∘ (starRingEnd ℂ) := by
      funext s; have h := LFunction_conj χ ((starRingEnd ℂ) s); rwa [Complex.conj_conj] at h
    have hderiv : deriv ((starRingEnd ℂ) ∘ DirichletCharacter.LFunction χ ∘ (starRingEnd ℂ)) 1 =
        (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1) := by
      have hd := (DirichletCharacter.differentiable_LFunction h1 1).hasDerivAt.conj_conj.deriv
      simp only [map_one] at hd
      exact hd
    rw [map_add, map_mul, map_div₀, hramp, Complex.conj_ofReal, hL, hderiv]
    simp

private lemma mellin_ramp (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) =
      (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by
    have : s = 1 := by linear_combination h
    rw [this] at hs; simp at hs
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioi (n : ℝ)) measurableSet_Ioi
    (Ioi_subset_Ioi hn1)]
  swap
  · intro y hy
    have hy' : y ≤ n := by simpa using hy.2
    simp [max_eq_right (show y / n - 1 ≤ 0 by rw [sub_nonpos, div_le_one hn0]; exact hy')]
  have hpt : ∀ y ∈ Ioi (n : ℝ), ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
      = (n : ℂ)⁻¹ * (y : ℂ) ^ (-s) - (y : ℂ) ^ (-s - 1) := by
    intro y hy
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast (lt_trans hn0 hy).ne'
    have hm : y / n - 1 ≥ 0 := by rw [ge_iff_le, sub_nonneg, le_div_iff₀ hn0]; linarith [show (n : ℝ) < y from hy]
    rw [max_eq_left hm, cpow_sub _ _ hyC, cpow_one]; push_cast; field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have ha1 : (-s).re < -1 := by simp; linarith
  have ha2 : (-s - 1).re < -1 := by simp; linarith
  rw [integral_sub ((integrableOn_Ioi_cpow_of_lt ha1 hn0).const_mul _)
    (integrableOn_Ioi_cpow_of_lt ha2 hn0), integral_const_mul,
    integral_Ioi_cpow_of_lt ha1 hn0, integral_Ioi_cpow_of_lt ha2 hn0]
  have hcast : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; rfl
  rw [hcast, cpow_add _ _ hnC, cpow_one, sub_add_cancel]
  have h1s : -s + 1 ≠ 0 := fun h => hs1 (by linear_combination -h)
  field_simp; ring

private lemma mellin_ramp_sum (f : ℕ → ℂ) (s : ℂ) (hs : 1 < s.re)
    (hf : LSeriesSummable (fun n => f n * (Λ n : ℂ)) s) (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 1)) :
    ∫ y in Ioi (1 : ℝ), (ramp f y * (y : ℂ) ^ (-s - 1) + g y) =
      LSeries (fun n => f n * (Λ n : ℂ)) s / (s * (s - 1)) + ∫ y in Ioi (1 : ℝ), g y := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by rw [sub_eq_zero.mp h] at hs; simp at hs
  set a : ℕ → ℂ := fun n => f n * (Λ n : ℂ)
  let F : ℕ → ℝ → ℂ := fun n y => match n with
    | 0 => g y
    | m + 1 => a (m + 1) * (((max (y / ((m + 1 : ℕ) : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
  have hint_n : ∀ (n : ℕ), 1 ≤ n → IntegrableOn (fun y : ℝ =>
      ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := fun n hn => by
    apply Integrable.of_integral_ne_zero
    rw [mellin_ramp n hn s hs]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    exact div_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hnC)) (mul_ne_zero hs0 hs1)
  have hnorm_n : ∀ (n : ℕ), 1 ≤ n → ∫ y in Ioi (1 : ℝ),
      ‖((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)‖ =
      (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := fun n hn => by
    have h := mellin_ramp n hn (s.re : ℂ) (by simpa using hs)
    apply ofReal_injective
    rw [← integral_complex_ofReal, ofReal_div, ofReal_cpow (Nat.cast_nonneg n)]; push_cast; rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real, Real.norm_of_nonneg (le_max_right _ _)]
    change (((max (y / n - 1) 0 * y ^ (-s - 1).re : ℝ)) : ℂ) = _
    rw [ofReal_mul, ofReal_cpow hy0.le]; simp
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 1)) := by
    rintro (_ | m); exact hg; exact (hint_n (m + 1) (by omega)).const_mul _
  have hsum : Summable fun n => ∫ y in Ioi (1 : ℝ), ‖F n y‖ := by
    rw [← summable_nat_add_iff 1]
    refine (((summable_nat_add_iff 1).mpr hf.norm).div_const (s.re * (s.re - 1))).congr fun m => ?_
    simp only [F]; simp_rw [norm_mul (a (m + 1))]
    rw [integral_const_mul, hnorm_n (m + 1) (by omega), LSeries.norm_term_eq, if_neg (by omega),
      Real.rpow_neg (Nat.cast_nonneg _)]; ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hF : ∀ y, ∑' n, F n y = ramp f y * (y : ℂ) ^ (-s - 1) + g y := by
    intro y
    have hhs : HasSum (fun n : ℕ => (Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)) (ramp f y) := by
      unfold ramp; apply hasSum_sum_of_ne_finset_zero; intro n hn
      have hn' : ⌊y⌋₊ + 1 ≤ n := by simpa using hn
      have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlt : y < n := by
        have h1 := Nat.lt_floor_add_one y
        have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
        push_cast at h2; linarith
      rw [max_eq_right (by linarith [(div_lt_one hpos).mpr hlt])]; simp
    have h1 := (hasSum_nat_add_iff' 1).mpr (hhs.mul_right ((y : ℂ) ^ (-s - 1)))
    have h2 : HasSum (fun n => F (n + 1) y) (ramp f y * (y : ℂ) ^ (-s - 1)) := by
      convert h1 using 1
      · rfl
      · ext m; simp only [F, a]; ring
      · simp
    simpa [F] using ((hasSum_nat_add_iff (f := fun n => F n y) 1).mp h2).tsum_eq
  simp_rw [hF] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr (hf.hasSum.div_const (s * (s - 1)))
  have h2 : HasSum (fun n => ∫ y in Ioi (1 : ℝ), F (n + 1) y) (LSeries a s / (s * (s - 1))) := by
    convert h1 using 1
    · rfl
    · ext m; simp only [F]
      rw [integral_const_mul, mellin_ramp (m + 1) (by omega) s hs, LSeries.term_of_ne_zero (by omega), cpow_neg]; ring
    · simp [LSeries]
  simpa [F] using h.unique ((hasSum_nat_add_iff (f := fun n => ∫ y in Ioi (1 : ℝ), F n y) 1).mp h2)

private lemma mellin_Gchi_modOne (χ : DirichletCharacter ℂ 1) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1 -
          (1 + Real.eulerMascheroniConstant) * s) / (s * (s - 1)) := by
  have h1 : χ = 1 := DirichletCharacter.level_one χ
  have h2 : ∀ n : ℕ, χ n = 1 := fun n => by rw [h1]; exact MulChar.one_apply (isUnit_of_subsingleton _)
  have ha : (-s).re < -1 := by simp; linarith
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by rw [sub_eq_zero.mp h] at hs; simp at hs
  set e : ℝ := (s.re - 1) / 2 with he_def
  have he0 : 0 < e := by rw [he_def]; linarith
  have hlogkey : ∀ (c : ℂ) (y : ℝ), 1 < y →
      ‖((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ c‖ ≤ y ^ (e + c.re) / e := fun c y hy => by
    have hy0 : (0 : ℝ) < y := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hy.le),
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, Real.rpow_add hy0]
    calc _ ≤ y ^ e / e * y ^ c.re := by gcongr; exact Real.log_le_rpow_div hy0.le he0
      _ = _ := by ring
  have hlog_int : IntegrableOn (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) := by
    have hc : e + (-s).re < -1 := by simp; rw [he_def]; linarith
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hc zero_lt_one).div_const e) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable).mul
        (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).1
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => hlogkey _ y hy
  have hlog_val : ∫ y in Ioi (1 : ℝ), ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s) = 1 / (s - 1) ^ 2 := by
    have hs1' : -s + 1 ≠ 0 := fun h => hs1 (by linear_combination -h)
    have ht : Tendsto (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1)) atTop (𝓝 0) := by
      have hc : 0 < -(e + (-s + 1).re) := by simp; rw [he_def]; linarith
      have h := (tendsto_rpow_neg_atTop hc).div_const e
      rw [neg_neg, zero_div] at h
      exact squeeze_zero_norm' (by filter_upwards [eventually_gt_atTop 1] with y hy using hlogkey _ y hy) h
    have hd : ∀ y ∈ Ici (1 : ℝ), HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1))
        ((-s + 1) * (((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) + (y : ℂ) ^ (-s)) y := fun y hy => by
      have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
      have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
      refine ((Real.hasDerivAt_log hy0).ofReal_comp.mul (hasDerivAt_ofReal_cpow_const hy0 hs1')).congr_deriv ?_
      rw [add_sub_cancel_right, cpow_add _ _ hyC, cpow_one]; push_cast; field_simp; ring
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
      ((hlog_int.const_mul _).add (integrableOn_Ioi_cpow_of_lt ha zero_lt_one)) ht
    rw [integral_add (hlog_int.const_mul _) (integrableOn_Ioi_cpow_of_lt ha zero_lt_one),
      integral_const_mul, integral_Ioi_cpow_of_lt ha zero_lt_one] at h
    simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_mul, sub_zero] at h
    rw [show (s - 1) ^ 2 = (-s + 1) ^ 2 by ring]; field_simp at h ⊢; linear_combination h
  have hi2 := integrableOn_Ioi_cpow_of_lt ha zero_lt_one
  have hf : LSeriesSummable (fun n => (1 : ℂ) * (Λ n : ℂ)) s := by
    simpa using ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hmain := mellin_ramp_sum (fun _ => 1) s hs hf
    (fun y => (1 + Real.eulerMascheroniConstant) * (y : ℂ) ^ (-s) - ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s))
    ((hi2.const_mul _).sub hlog_int)
  have hcongr : EqOn (fun y : ℝ => Gchi χ y * (y : ℂ) ^ (-s - 1))
      (fun y => ramp (fun _ => 1) y * (y : ℂ) ^ (-s - 1) +
        ((1 + Real.eulerMascheroniConstant) * (y : ℂ) ^ (-s) - ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)))
      (Ioi 1) := fun y hy => by
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hy).ne'
    have h3 : (y : ℂ) ^ (-s) = y * (y : ℂ) ^ (-s - 1) := by rw [cpow_sub _ _ hyC, cpow_one]; field_simp
    simp only [Gchi, if_pos h1, h2, h3]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hmain,
    integral_sub (hi2.const_mul _) hlog_int, integral_const_mul,
    integral_Ioi_cpow_of_lt ha zero_lt_one, hlog_val]
  have h4 : LSeries (fun n => (1 : ℂ) * (Λ n : ℂ)) s = -deriv riemannZeta s / riemannZeta s := by
    simpa using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [h4, neg_div (riemannZeta s), show -s + 1 = -(s - 1) by ring]
  generalize deriv riemannZeta s / riemannZeta s = D
  simp only [ofReal_one, one_cpow]; field_simp; ring

private lemma mellin_Gchi_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          s * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) /
        (s * (s - 1)) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by rw [sub_eq_zero.mp h] at hs; simp at hs
  set c := deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1
  have ha : (-s).re < -1 := by simp; linarith
  have h := mellin_ramp_sum (fun n => χ n) s hs (χ.LSeriesSummable_twist_vonMangoldt hs)
    (fun y => c * (y : ℂ) ^ (-s)) ((integrableOn_Ioi_cpow_of_lt ha one_pos).const_mul c)
  have hL : LSeries (fun n : ℕ => χ n * (Λ n : ℂ)) s = _ := χ.LSeries_twist_vonMangoldt_eq hs
  rw [hL, ← χ.LFunction_eq_LSeries hs, ← χ.deriv_LFunction_eq_deriv_LSeries hs, integral_const_mul,
    integral_Ioi_cpow_of_lt ha one_pos] at h
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y : ℝ =>
    ramp (fun n => χ n) y * (y : ℂ) ^ (-s - 1) + c * (y : ℂ) ^ (-s)), h]
  · rw [show -s + 1 = -(s - 1) by ring, neg_div (DirichletCharacter.LFunction χ s)]
    generalize deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s = d
    simp only [ofReal_one, one_cpow]; field_simp; ring
  · intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos hy).ne'
    simp only [Gchi, if_neg hχ, c]; rw [cpow_sub _ _ hy0, cpow_one]; field_simp

private lemma poleData_abstract (g : ℂ → ℂ) (hg : Differentiable ℂ g) (h1 : g 1 ≠ 0) (k : ℂ) :
    ∃ Φ : ℂ → ℂ,
      (∀ s, s ≠ 1 → Φ s =
        -(deriv g s / g s - s * (deriv g 1 / g 1) + k * (1 - s)) / (s * (s - 1))) ∧
      (∀ ρ, ρ ≠ 0 → g ρ ≠ 0 → AnalyticAt ℂ Φ ρ) ∧
      (∀ ρ, ρ ≠ 0 → ∃ m : ℕ, (m = 0 ↔ g ρ ≠ 0) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, Φ s = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h s) ∧
      (∀ z, ∀ᶠ w in 𝓝[≠] z, g w ≠ 0) := by
  have hA : ∀ z, AnalyticAt ℂ g z := fun z => hg.analyticAt z
  have hnz : ∀ z, ¬ ∀ᶠ w in 𝓝 z, g w = 0 := fun z hz => by
    have hon : AnalyticOnNhd ℂ g Set.univ := fun w _ => hA w
    exact h1 (hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) hz (Set.mem_univ 1))
  set c : ℂ := deriv g 1 / g 1
  set N : ℂ → ℂ := fun s => deriv g s / g s - s * c + k * (1 - s)
  have hN1 : N 1 = 0 := by simp only [N, c]; ring
  have hUo : IsOpen {s | g s ≠ 0} := isOpen_ne_fun hg.continuous continuous_const
  have hNd : DifferentiableOn ℂ N {s | g s ≠ 0} := fun s hs =>
    ((((hA s).deriv.differentiableAt.div (hA s).differentiableAt hs).sub
      (differentiableAt_id.mul (differentiableAt_const c))).add
      ((differentiableAt_const k).mul ((differentiableAt_const 1).sub differentiableAt_id))).differentiableWithinAt
  have hDd : DifferentiableOn ℂ (dslope N 1) {s | g s ≠ 0} :=
    (differentiableOn_dslope (hUo.mem_nhds h1)).mpr hNd
  have hPhi : ∀ s, s ≠ 1 → -(dslope N 1 s) / s =
      -(deriv g s / g s - s * (deriv g 1 / g 1) + k * (1 - s)) / (s * (s - 1)) := fun s hs => by
    rw [dslope_of_ne _ hs, slope_def_field, hN1]; simp only [N, c, div_eq_mul_inv, mul_inv]; ring
  have hPan : ∀ ρ, ρ ≠ 0 → g ρ ≠ 0 → AnalyticAt ℂ (fun s => -(dslope N 1 s) / s) ρ :=
    fun ρ hρ hgρ => (hDd.analyticAt (hUo.mem_nhds hgρ)).neg.div analyticAt_id hρ
  refine ⟨fun s => -(dslope N 1 s) / s, hPhi, hPan, ?_, fun z =>
    (hA z).eventually_eq_zero_or_eventually_ne_zero.resolve_left (hnz z)⟩
  intro ρ hρ
  by_cases hgρ : g ρ = 0
  · have hρ1 : ρ ≠ 1 := fun h => h1 (h ▸ hgρ)
    have htop : analyticOrderAt g ρ ≠ ⊤ := fun h => hnz ρ (analyticOrderAt_eq_top.mp h)
    obtain ⟨g₀, hg₀, hg₀0, hfg⟩ := (hA ρ).analyticOrderAt_ne_top.mp htop
    set m := analyticOrderNatAt g ρ
    have hm0 : m = 0 ↔ g ρ ≠ 0 := by
      rw [← (hA ρ).analyticOrderAt_eq_zero, ← Nat.cast_analyticOrderNatAt htop]; exact Nat.cast_eq_zero.symm
    have hlog : ∀ᶠ s in 𝓝[≠] ρ, deriv g s / g s = (m : ℂ) / (s - ρ) + deriv g₀ s / g₀ s := by
      have hev : ∀ᶠ s in 𝓝 ρ, (∀ᶠ z in 𝓝 s, g z = (z - ρ) ^ m • g₀ z) ∧ g₀ s ≠ 0 ∧ AnalyticAt ℂ g₀ s :=
        (Filter.Eventually.eventually_nhds hfg).and ((hg₀.continuousAt.eventually_ne hg₀0).and hg₀.eventually_analyticAt)
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s ⟨hs1, hs2, hs3⟩ hsne
      have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hsne
      have hd : HasDerivAt (fun z => (z - ρ) ^ m * g₀ z)
          (↑m * (s - ρ) ^ (m - 1) * 1 * g₀ s + (s - ρ) ^ m * deriv g₀ s) s :=
        (((hasDerivAt_id' s).sub_const ρ).pow m).mul hs3.differentiableAt.hasDerivAt
      have e1 : deriv g s = deriv (fun z => (z - ρ) ^ m * g₀ z) s :=
        Filter.EventuallyEq.deriv_eq (by filter_upwards [hs1] with z hz; rw [hz, smul_eq_mul])
      have e2 : g s = (s - ρ) ^ m * g₀ s := by simpa only [smul_eq_mul] using hs1.self_of_nhds
      rw [e1, hd.deriv, e2]
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        rw [hj, Nat.add_sub_cancel, pow_succ]; field_simp
    have hr : AnalyticAt ℂ (fun s : ℂ => 1 / (s * (s - 1))) ρ :=
      analyticAt_const.div (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
        (mul_ne_zero hρ (sub_ne_zero.mpr hρ1))
    have hq : AnalyticAt ℂ (dslope (fun s : ℂ => 1 / (s * (s - 1))) ρ) ρ := by
      obtain ⟨p, hp⟩ := hr; exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
    refine ⟨m, hm0, fun s => -((m : ℂ) * dslope (fun s : ℂ => 1 / (s * (s - 1))) ρ s)
        - (deriv g₀ s / g₀ s - s * c + k * (1 - s)) * (1 / (s * (s - 1))), ?_, ?_⟩
    · exact ((analyticAt_const.mul hq).neg).sub
        ((((hg₀.deriv.div hg₀ hg₀0).sub (analyticAt_id.mul analyticAt_const)).add
          (analyticAt_const.mul (analyticAt_const.sub analyticAt_id))).mul hr)
    · filter_upwards [hlog, nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ),
        nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ1), self_mem_nhdsWithin] with s hs hs0 hs1 hsρ
      rw [hPhi s hs1, hs, dslope_of_ne _ hsρ, slope_def_field]
      simp only [c, div_eq_mul_inv, mul_inv]; ring
  · exact ⟨0, by simp [hgρ], fun s => -(dslope N 1 s) / s, hPan ρ hρ hgρ,
      Filter.Eventually.of_forall fun s => by simp⟩

/-- **PoleData construction for any admissible `CharFamily`**, directly from Mathlib's
`DirichletCharacter.LFunction` and `riemannZeta`. -/
theorem poleData (F : CharFamily) : ∃ Φ : ℂ → ℂ, PoleData F.gm Φ F.zeroSet := by
  classical
  have hchange : ∀ (G : ℝ → ℂ) (s : ℂ),
      ∫ u in Ioi (0 : ℝ), G (Real.exp u) * cexp (-s * u) =
        ∫ y in Ioi (1 : ℝ), G y * (y : ℂ) ^ (-s - 1) := by
    intro G s
    have himg : Real.exp '' Ioi 0 = Ioi 1 := by
      ext y; constructor
      · rintro ⟨u, hu, rfl⟩; show (1 : ℝ) < Real.exp u; rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 hu
      · intro hy; exact ⟨Real.log y, Real.log_pos hy, Real.exp_log (by linarith [show (1 : ℝ) < y from hy])⟩
    rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [abs_of_pos (Real.exp_pos u), Complex.real_smul,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, Complex.ofReal_exp,
      mul_left_comm, ← Complex.exp_add]
    congr 2; ring
  have hchar : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), (N = 1 ∨ χ ≠ 1) →
      ∃ Φ : ℂ → ℂ,
        (∀ s : ℂ, 2 < s.re → Φ s = ∫ u in Ioi (0 : ℝ), Gchi χ (Real.exp u) * cexp (-s * u)) ∧
        (∀ ρ, ρ ≠ 0 → DirichletCharacter.LFunction χ ρ ≠ 0 → AnalyticAt ℂ Φ ρ) ∧
        (∀ ρ, ρ ≠ 0 → ∃ m : ℕ, (m = 0 ↔ DirichletCharacter.LFunction χ ρ ≠ 0) ∧
          ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
          ∀ᶠ s in 𝓝[≠] ρ, Φ s = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h s) ∧
        (∀ z, ∀ᶠ w in 𝓝[≠] z, DirichletCharacter.LFunction χ w ≠ 0) := by
    intro N _ χ adm
    by_cases hχ : χ = 1
    · have hN : N = 1 := adm.resolve_right (fun h => h hχ)
      subst hN; simp only [DirichletCharacter.LFunction_modOne_eq]
      set g : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
      have hg_ne : ∀ w : ℂ, w ≠ 1 → g w = (w - 1) * riemannZeta w := fun w hw => by
        simp [g, hw]
      have hg1 : g 1 = 1 := by simp [g]
      have hg : Differentiable ℂ g := by
        rw [← differentiableOn_univ,
          ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
        refine ⟨fun z hz => ?_, by simpa only [g, continuousAt_update_same] using riemannZeta_residue_one⟩
        have hz1 : z ≠ 1 := by simpa using hz
        have hev : g =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw using hg_ne w hw
        exact ((DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hz1)).congr_of_eventuallyEq
          hev).differentiableWithinAt
      have hderiv1 : deriv g 1 = Real.eulerMascheroniConstant := by
        have hd := hasDerivAt_iff_tendsto_slope.mp (hg 1).hasDerivAt
        refine tendsto_nhds_unique hd (tendsto_riemannZeta_sub_one_div.congr' ?_)
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
        rw [slope_def_field, hg_ne s hs, hg1]; field_simp
      have hderiv : ∀ s : ℂ, s ≠ 1 → deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s := fun s hs1 => by
        have hev : g =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with w hw using hg_ne w hw
        have h3 : HasDerivAt (fun t : ℂ => (t - 1) * riemannZeta t)
            (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
          ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs1).hasDerivAt
        rw [hev.deriv_eq, h3.deriv]; ring
      have hgz : ∀ w : ℂ, g w ≠ 0 ↔ riemannZeta w ≠ 0 := fun w => by
        by_cases hw : w = 1
        · subst hw; rw [hg1]; exact ⟨fun _ => riemannZeta_one_ne_zero, fun _ => one_ne_zero⟩
        · rw [hg_ne w hw]; exact ⟨fun h hz => h (by rw [hz, mul_zero]), mul_ne_zero (sub_ne_zero.mpr hw)⟩
      obtain ⟨Φ, h1, h2, h3, h4⟩ := poleData_abstract g hg (by rw [hg1]; exact one_ne_zero) 1
      refine ⟨Φ, fun s hs => ?_, fun ρ hρ hL => h2 ρ hρ ((hgz ρ).mpr hL),
        fun ρ hρ => by obtain ⟨m, hm, rest⟩ := h3 ρ hρ; exact ⟨m, hm.trans (hgz ρ), rest⟩,
        fun z => by filter_upwards [h4 z] with w hw using (hgz w).mp hw⟩
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
      have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
      rw [h1 s hs1, hchange, mellin_Gchi_modOne χ s (by linarith), hderiv s hs1, hg_ne s hs1, hderiv1, hg1]
      congr 1; field_simp; ring
    · obtain ⟨Φ, h1, h2, h3, h4⟩ := poleData_abstract (DirichletCharacter.LFunction χ)
        (DirichletCharacter.differentiable_LFunction hχ)
        (DirichletCharacter.LFunction_apply_one_ne_zero hχ) 0
      refine ⟨Φ, fun s hs => ?_, h2, h3, h4⟩
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
      rw [h1 s hs1, hchange, mellin_Gchi_of_ne_one χ hχ s (by linarith), zero_mul, add_zero]
  have hint : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 2 < s.re →
      IntegrableOn (fun u : ℝ => Gchi χ (Real.exp u) * cexp (-s * u)) (Ioi 0) := by
    intro N _ χ s hs
    obtain ⟨C, hC⟩ := Gchi_growth χ
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < s.re - 2)).const_mul (max C 0))
      (((measurable_Gchi χ).comp Real.measurable_exp).mul (by fun_prop : Measurable fun u : ℝ => cexp (-s * u))).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 ≤ u := le_of_lt hu
    rw [norm_mul, Complex.norm_exp, show (-s * (u : ℂ)).re = -s.re * u by simp]
    calc ‖Gchi χ (Real.exp u)‖ * Real.exp (-s.re * u)
        ≤ (max C 0 * Real.exp u ^ 2) * Real.exp (-s.re * u) := by
          gcongr; exact (hC (Real.exp u) (Real.one_le_exp hu0)).trans (by gcongr; exact le_max_left _ _)
      _ = max C 0 * Real.exp (-(s.re - 2) * u) := by
          rw [mul_assoc, sq, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have adm' : ∀ i, F.N i = 1 ∨ (F.χ i)⁻¹ ≠ 1 := fun i => (F.adm i).imp id (fun h => inv_ne_one.mpr h)
  choose Φ1 hΦ1int hΦ1an hΦ1pol hΦ1iso using fun i => hchar (F.χ i) (F.adm i)
  choose Φ2 hΦ2int hΦ2an hΦ2pol hΦ2iso using fun i => hchar (F.χ i)⁻¹ (adm' i)
  choose C hC using fun i => Gchi_growth (F.χ i)
  have hconj : ∀ i (w : ℂ), DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) w) = 0 ↔
      DirichletCharacter.LFunction (F.χ i)⁻¹ w = 0 := fun i w => by
    have := LFunction_conj (F.χ i) ((starRingEnd ℂ) w); rw [Complex.conj_conj] at this
    rw [this, map_eq_zero]
  refine ⟨fun s => ∑ i, (F.a i : ℂ) / 2 * (Φ1 i s + Φ2 i s), ?_⟩
  refine PoleData.mk ?_ ?_ ?_ (fun ρ hρ => hρ.1) ?_ ?_ ?_
  · exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      (Complex.measurable_re.comp ((measurable_Gchi (F.χ i)).comp Real.measurable_exp))
  · refine ⟨∑ i, F.a i * C i, fun u hu => ?_⟩
    have hy : 1 ≤ Real.exp u := Real.one_le_exp hu
    have he : Real.exp u ^ 2 = Real.exp (2 * u) := by rw [sq, ← Real.exp_add, two_mul]
    calc |∑ i, F.a i * (Gchi (F.χ i) (Real.exp u)).re|
        ≤ ∑ i, |F.a i * (Gchi (F.χ i) (Real.exp u)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, F.a i * (C i * Real.exp (2 * u)) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_pos (F.a_pos i)]
          exact mul_le_mul_of_nonneg_left
            ((Complex.abs_re_le_norm _).trans ((hC i _ hy).trans_eq (by rw [he]))) (F.a_pos i).le
      _ = (∑ i, F.a i * C i) * Real.exp (2 * u) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  · intro s hs
    have hpt : ∀ u : ℝ, ((F.gm u : ℝ) : ℂ) * cexp (-s * u) = ∑ i, (F.a i : ℂ) / 2 *
        (Gchi (F.χ i) (Real.exp u) * cexp (-s * u) + Gchi (F.χ i)⁻¹ (Real.exp u) * cexp (-s * u)) := by
      intro u; simp only [CharFamily.gm, CharFamily.Gm]; push_cast; rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_; rw [Complex.re_eq_add_conj, Gchi_conj]; ring
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_add (hint _ s hs) (hint _ s hs), hΦ1int i s hs, hΦ2int i s hs]
    · intro i _
      exact ((hint _ s hs).add (hint _ s hs)).const_mul _
  · intro s ⟨hsre, hsZ⟩
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
    have hL : ∀ i, DirichletCharacter.LFunction (F.χ i) s ≠ 0 ∧
        DirichletCharacter.LFunction (F.χ i)⁻¹ s ≠ 0 := fun i =>
      ⟨fun h => hsZ ⟨hsre, i, Or.inl h⟩, fun h => hsZ ⟨hsre, i, Or.inr ((hconj i s).2 h)⟩⟩
    exact (Finset.analyticAt_fun_sum _ fun i _ =>
      analyticAt_const.mul ((hΦ1an i s hs0 (hL i).1).add (hΦ2an i s hs0 (hL i).2))).differentiableAt.differentiableWithinAt
  · intro z _
    have hall : ∀ᶠ w in 𝓝[≠] z, ∀ i, DirichletCharacter.LFunction (F.χ i) w ≠ 0 ∧
        DirichletCharacter.LFunction (F.χ i)⁻¹ w ≠ 0 :=
      Filter.eventually_all.mpr fun i => (hΦ1iso i z).and (hΦ2iso i z)
    filter_upwards [hall] with w hw ⟨_, i, hi⟩
    rcases hi with hi | hi
    · exact (hw i).1 hi
    · exact (hw i).2 ((hconj i w).1 hi)
  · intro ρ ⟨hρre, i0, hi0⟩
    have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρre; simp at hρre
    have hρ1 : ρ ≠ 1 := fun h => by
      rcases hi0 with h' | h'
      · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 ρ (by rw [h]; simp) h'
      · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 _ (by rw [h]; simp) h'
    choose m1 hm1 h1 hh1an hh1ev using fun i => hΦ1pol i ρ hρ0
    choose m2 hm2 h2 hh2an hh2ev using fun i => hΦ2pol i ρ hρ0
    set S : ℝ := ∑ i, F.a i / 2 * ((m1 i : ℝ) + m2 i)
    have hS0 : 0 < S := by
      have hpos : 0 < F.a i0 / 2 * ((m1 i0 : ℝ) + m2 i0) := by
        apply mul_pos (by linarith [F.a_pos i0])
        have hm1n : (0 : ℝ) ≤ m1 i0 := Nat.cast_nonneg _
        have hm2n : (0 : ℝ) ≤ m2 i0 := Nat.cast_nonneg _
        rcases hi0 with h | h
        · have : (1 : ℝ) ≤ m1 i0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun hm => ((hm1 i0).1 hm) h
          linarith
        · have : (1 : ℝ) ≤ m2 i0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun hm => ((hm2 i0).1 hm) ((hconj i0 ρ).1 h)
          linarith
      exact hpos.trans_le (Finset.single_le_sum (f := fun i => F.a i / 2 * ((m1 i : ℝ) + m2 i))
        (fun i _ => by have := F.a_pos i; positivity) (Finset.mem_univ i0))
    refine ⟨(S : ℂ) * (-1 / (ρ * (ρ - 1))),
      mul_ne_zero (by exact_mod_cast hS0.ne') (div_ne_zero (by norm_num) (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1))),
      fun him => ?_, fun s => ∑ i, (F.a i : ℂ) / 2 * (h1 i s + h2 i s),
      Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul ((hh1an i).add (hh2an i)), ?_⟩
    · have hρx : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
      have hlt : ρ.re < 1 := by
        by_contra hge; push Not at hge
        rcases hi0 with h' | h'
        · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 ρ hge h'
        · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 _ (by simpa using hge) h'
      have hc : (S : ℂ) * (-1 / (ρ * (ρ - 1))) = ((S * (-1 / (ρ.re * (ρ.re - 1))) : ℝ) : ℂ) := by
        push_cast; rw [← hρx]
      rw [hc, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨mul_pos hS0 (div_pos_of_neg_of_neg (by norm_num) (mul_neg_of_pos_of_neg hρre (by linarith))), rfl⟩
    · have hev := Filter.eventually_all.mpr fun i => (hh1ev i).and (hh2ev i)
      filter_upwards [hev] with s hs
      simp only [S]; push_cast; rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [(hs i).1, (hs i).2]; ring

/-! ## Part 3: Multiplicative-Window Nonvanishing (`zeroFree_of_rpow_window`) -/

/-- **Main Windowed Nonvanishing Theorem for `CharFamily`**:
If `HasRpowWindow F.Gm θ δ C` holds (`0 < θ < 1`, `δ > 0`), then `L(F.χ i, s) ≠ 0` for all `i`
and all `s` with `θ < Re(s)`. -/
theorem zeroFree_of_rpow_window (F : CharFamily) {θ δ C : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (h : HasRpowWindow F.Gm θ δ C) :
    F.ZeroFree θ := by
  have hWU : WindowHypU F.gm θ δ := by
    intro η hη U₀
    have hη2 : 0 < η / 2 := by positivity
    obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1
      (((tendsto_rpow_atTop hη2).eventually_ge_atTop ((|C| * δ) / (η / 2))).and (eventually_ge_atTop (1 : ℝ)))
    obtain ⟨Y, hY, hb⟩ := h (max (Real.exp U₀) Y₁)
    obtain ⟨ha, h1⟩ := hY₁ Y ((le_max_right _ _).trans hY)
    have hYpos : 0 < Y := by linarith
    have hK : |C| * δ * Real.log Y ≤ Y ^ η := by
      have he : Y ^ η = Y ^ (η / 2) * Y ^ (η / 2) := by rw [← Real.rpow_add hYpos]; congr 1; ring
      calc |C| * δ * Real.log Y ≤ |C| * δ * (Y ^ (η / 2) / (η / 2)) :=
            mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hYpos.le hη2) (by positivity)
        _ = |C| * δ / (η / 2) * Y ^ (η / 2) := by ring
        _ ≤ Y ^ (η / 2) * Y ^ (η / 2) := mul_le_mul_of_nonneg_right ha (by positivity)
        _ = Y ^ η := he.symm
    set U := Real.log Y
    have hU : U₀ ≤ U := by
      rw [← Real.exp_le_exp, Real.exp_log hYpos]; exact (le_max_left _ _).trans hY
    have hle : U ≤ (1 + δ) * U := by
      have hU0 : 0 ≤ U := Real.log_nonneg h1; nlinarith
    have heq : EqOn (fun u => |C| * (Real.exp u) ^ θ * Real.exp (-θ * u)) (fun _ => |C|) (Icc U ((1 + δ) * U)) := by
      intro u _
      dsimp only
      rw [← Real.exp_mul, mul_assoc, ← Real.exp_add]
      simp [mul_comm]
    refine ⟨U, hU, fun u => |C| * (Real.exp u) ^ θ,
      (integrableOn_congr_fun heq measurableSet_Icc).2 continuousOn_const.integrableOn_Icc, ?_, ?_⟩
    · intro u ⟨hu1, hu2⟩
      have hy : Real.exp u ∈ Icc Y (Y ^ (1 + δ)) := by
        refine ⟨by rw [← Real.exp_log hYpos]; exact Real.exp_le_exp.2 hu1, ?_⟩
        rw [Real.rpow_def_of_pos hYpos, mul_comm]; exact Real.exp_le_exp.2 hu2
      exact ⟨by positivity, (hb _ hy).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))⟩
    · rw [setIntegral_congr_fun measurableSet_Icc heq, setIntegral_const, smul_eq_mul,
        Real.volume_real_Icc_of_le hle]
      calc ((1 + δ) * U - U) * |C| = |C| * δ * Real.log Y := by simp only [U]; ring
        _ ≤ Y ^ η := hK
        _ = Real.exp (η * U) := by rw [Real.rpow_def_of_pos hYpos, mul_comm]
  intro i s hs hzero
  obtain ⟨Φ, hP⟩ := poleData F
  have hZ := landau_window hP hθ hθ1 hδ hWU
  by_cases h1 : 1 ≤ s.re
  · exact charFamily_LFunction_ne_zero_of_one_le_re F i s h1 hzero
  · have := hZ s ⟨by linarith, i, Or.inl hzero⟩
    linarith

end RHDirect
