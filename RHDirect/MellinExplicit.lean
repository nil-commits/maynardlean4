import RHDirect.Interfaces
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# RHDirect.MellinExplicit

Compact, self-contained, 0-`sorry`, 0-`axiom` rebuild of the Cesàro-1 ramp kernel,
Mellin transform identities, Dirichlet-series integral convergence & holomorphicity on
`Re(s) > 1`, Mertens/growth bounds, and Landau windowed tail estimates against
`RHDirect.Interfaces` and Mathlib `v4.33.1`.

## Main Contents
1. **Cesàro Ramp Kernel (`cesaroKernel`, `ramp`)**:
   Non-negativity, exact support `[x, ∞)`, monotonicity in `t`, antitonicity in `x`,
   continuity, measurability, finite-support series representation `ramp_eq_tsum_hasSum`,
   positivity/monotonicity of the unsigned ramp `ramp (fun _ => 1)`, and character
   conjugation `ramp_conj`.
2. **Exact Mellin Transforms**:
   - `mellin_cesaroKernel`: `∫ t in Ioi 1, ((max (t / x - 1) 0 : ℝ) : ℂ) * t ^ (-s - 1) = x ^ (-s) / (s * (s - 1))`
     for all `1 ≤ x` and `1 < Re(s)`.
   - `mellin_ramp_div`: exact Mellin transform of the scaled Cesàro ramp `ramp f (t / x)` on `Ioi 1`,
     giving `(x : ℂ) ^ (-s) * LSeries (fun n => f n * (Λ n : ℂ)) s / (s * (s - 1))`.
   - `mellin_log`: `∫ y in Ioi 1, (Real.log y : ℂ) * y ^ (-s) = 1 / (s - 1) ^ 2`.
   - `mellin_Gchi_modOne`, `mellin_Gz`, `mellin_Gchi_of_ne_one`, and `mellin_Gm_eq_sum`:
     exact Mellin transforms of `Gchi`, `Gz`, and `CharFamily.Gm` on `Re(s) > 1`.
3. **Mertens Bound, Growth Estimates, Convergence & Holomorphicity on `Re(s) > 1`**:
   - `mertens_upper`: `∑ n ≤ ⌊y⌋₊, Λ(n) / n ≤ log y + 2` for `y ≥ 1`.
   - Sharp `O(y (log y + 1))` and `O(y²)` bounds for `ramp`, `Gchi`, `Gz`, `CharFamily.Gm`.
   - Absolute integrability, complex differentiability (`DifferentiableOn ℂ`), and
     analyticity (`AnalyticOnNhd ℂ`) of the Mellin transforms of `Gchi`, `Gz`, and
     `CharFamily.Gm` on the full half-plane `{s : ℂ | 1 < s.re}`.
   - Mellin–Laplace change of variables `y = exp u` (`mellin_eq_laplace`, `mellin_Gm_eq_laplace`).
4. **Landau Kernel, Iterated Laplace Derivatives & Windowed Tail Estimates**:
   - `kernel_integral`, `iteratedDeriv_laplace`, `landau_tails` (Chernoff tail bound),
     and `windowHyp_of_hasRpowWindow` (`HasRpowWindow F.Gm θ δ C → F.WindowHyp θ δ`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.MellinExplicit

/-! ## 1. Elementary Cesàro Ramp Kernel & `ramp` Properties -/

/-- Elementary Cesàro-1 ramp weight `(t / x - 1)_+`. -/
def cesaroKernel (x t : ℝ) : ℝ := max (t / x - 1) 0

theorem cesaroKernel_nonneg (x t : ℝ) : 0 ≤ cesaroKernel x t :=
  le_max_right _ _

theorem cesaroKernel_eq_zero_of_le {x t : ℝ} (hx : 0 < x) (ht : t ≤ x) :
    cesaroKernel x t = 0 := by
  unfold cesaroKernel
  rw [max_eq_right]
  rw [sub_nonpos, div_le_one hx]
  exact ht

theorem cesaroKernel_eq_sub_of_ge {x t : ℝ} (hx : 0 < x) (ht : x ≤ t) :
    cesaroKernel x t = t / x - 1 := by
  unfold cesaroKernel
  rw [max_eq_left]
  rw [sub_nonneg, one_le_div hx]
  exact ht

theorem cesaroKernel_pos_of_lt {x t : ℝ} (hx : 0 < x) (ht : x < t) :
    0 < cesaroKernel x t := by
  rw [cesaroKernel_eq_sub_of_ge hx ht.le, sub_pos, one_lt_div hx]
  exact ht

theorem cesaroKernel_mono_right {x : ℝ} (hx : 0 < x) : Monotone (cesaroKernel x) := by
  intro t₁ t₂ h
  unfold cesaroKernel
  exact max_le_max_right 0 (sub_le_sub_right (div_le_div_of_nonneg_right h hx.le) 1)

theorem cesaroKernel_antitone_left {t : ℝ} (ht : 0 ≤ t) :
    AntitoneOn (fun x => cesaroKernel x t) (Ioi 0) := by
  intro x₁ hx₁ x₂ hx₂ h
  unfold cesaroKernel
  exact max_le_max_right 0 (sub_le_sub_right (div_le_div_of_nonneg_left ht hx₁ h) 1)

theorem cesaroKernel_le_div {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    cesaroKernel x t ≤ t / x :=
  max_le (by linarith) (div_nonneg ht hx.le)

theorem cesaroKernel_continuous_right (x : ℝ) : Continuous (cesaroKernel x) := by
  unfold cesaroKernel
  fun_prop

theorem cesaroKernel_div_eq {x y t : ℝ} :
    cesaroKernel y (t / x) = cesaroKernel (x * y) t := by
  simp only [cesaroKernel, div_div]

theorem ramp_eq_sum_cesaroKernel (f : ℕ → ℂ) (y : ℝ) :
    ramp f y = ∑ n ∈ Finset.range (⌊y⌋₊ + 1), (Λ n : ℂ) * f n * ((cesaroKernel n y : ℝ) : ℂ) :=
  rfl

theorem ramp_term_eq_zero_of_not_mem (f : ℕ → ℂ) (y : ℝ) {n : ℕ}
    (hn : n ∉ Finset.range (⌊y⌋₊ + 1)) :
    (Λ n : ℂ) * f n * ((cesaroKernel n y : ℝ) : ℂ) = 0 := by
  have hn' : ⌊y⌋₊ + 1 ≤ n := by simpa using hn
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlt : y < n := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at h2
    linarith
  rw [cesaroKernel_eq_zero_of_le hnpos hlt.le]
  simp

theorem ramp_eq_tsum_hasSum (f : ℕ → ℂ) (y : ℝ) :
    HasSum (fun n : ℕ => (Λ n : ℂ) * f n * ((cesaroKernel n y : ℝ) : ℂ)) (ramp f y) := by
  unfold ramp
  exact hasSum_sum_of_ne_finset_zero fun n hn => ramp_term_eq_zero_of_not_mem f y hn

theorem ramp_eq_sum_of_le (f : ℕ → ℂ) {y : ℝ} {M : ℕ} (hM : ⌊y⌋₊ ≤ M) :
    ramp f y = ∑ n ∈ Finset.range (M + 1), (Λ n : ℂ) * f n * ((cesaroKernel n y : ℝ) : ℂ) := by
  have hsub : Finset.range (⌊y⌋₊ + 1) ⊆ Finset.range (M + 1) :=
    Finset.range_mono (Nat.succ_le_succ hM)
  rw [ramp_eq_sum_cesaroKernel]
  exact Finset.sum_subset hsub fun n _ hn => ramp_term_eq_zero_of_not_mem f y hn

theorem ramp_eq_zero_of_le_two (f : ℕ → ℂ) {y : ℝ} (hy : y ≤ 2) : ramp f y = 0 := by
  unfold ramp
  refine Finset.sum_eq_zero fun n _ => ?_
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  rcases eq_or_ne n 1 with rfl | h1
  · simp
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have hzero : max (y / n - 1) 0 = 0 := cesaroKernel_eq_zero_of_le hnpos (hy.trans hn2)
  rw [hzero]
  simp

theorem ramp_eq_zero_of_le_one (f : ℕ → ℂ) {y : ℝ} (hy : y ≤ 1) : ramp f y = 0 :=
  ramp_eq_zero_of_le_two f (by linarith)

theorem ramp_one_eq_ofReal (y : ℝ) :
    ramp (fun _ => 1) y =
      ((∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * cesaroKernel n y : ℝ) : ℂ) := by
  unfold ramp cesaroKernel
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem ramp_one_re_eq (y : ℝ) :
    (ramp (fun _ => 1) y).re = ∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * cesaroKernel n y := by
  rw [ramp_one_eq_ofReal, Complex.ofReal_re]

theorem ramp_one_im_eq_zero (y : ℝ) : (ramp (fun _ => 1) y).im = 0 := by
  rw [ramp_one_eq_ofReal, Complex.ofReal_im]

theorem ramp_one_re_nonneg (y : ℝ) : 0 ≤ (ramp (fun _ => 1) y).re := by
  rw [ramp_one_re_eq]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (cesaroKernel_nonneg n y)

theorem ramp_one_re_mono : Monotone (fun y => (ramp (fun _ => 1) y).re) := by
  intro y₁ y₂ h
  have hM : ⌊y₁⌋₊ ≤ ⌊y₂⌋₊ := Nat.floor_mono h
  have h1 : (ramp (fun _ => 1) y₁).re =
      ∑ n ∈ Finset.range (⌊y₂⌋₊ + 1), Λ n * cesaroKernel n y₁ := by
    rw [ramp_eq_sum_of_le (fun _ => 1) hM]
    simp only [mul_one, Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  dsimp only
  rw [h1, ramp_one_re_eq]
  refine Finset.sum_le_sum fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact mul_le_mul_of_nonneg_left (cesaroKernel_mono_right (by exact_mod_cast hn) h)
      ArithmeticFunction.vonMangoldt_nonneg

theorem ramp_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (starRingEnd ℂ) (ramp (fun n => χ n) y) = ramp (fun n => χ⁻¹ n) y := by
  unfold ramp
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  congr 2
  exact MulChar.star_apply' χ (n : ZMod N)

private theorem measurable_floor_family (g : ℕ → ℝ → ℂ) (hg : ∀ k, Measurable (g k)) :
    Measurable (fun y : ℝ => g ⌊y⌋₊ y) := by
  have h : Measurable fun p : ℝ × ℕ => g p.2 p.1 :=
    measurable_from_prod_countable_left fun k => hg k
  exact h.comp (measurable_id.prodMk Nat.measurable_floor)

theorem measurable_ramp (f : ℕ → ℂ) : Measurable (ramp f) := by
  unfold ramp
  refine measurable_floor_family
    (fun k y => ∑ n ∈ Finset.range (k + 1), (Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)) ?_
  intro k
  refine Finset.measurable_sum _ fun n _ => ?_
  fun_prop

theorem measurable_Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Measurable (Gchi χ) := by
  unfold Gchi
  split_ifs
  · exact ((measurable_ramp _).sub (by fun_prop)).add (by fun_prop)
  · exact (measurable_ramp _).add (by fun_prop)

theorem measurable_Gz : Measurable Gz := by
  unfold Gz
  exact (((Complex.measurable_re.comp (measurable_ramp _)).sub (by fun_prop)).add (by fun_prop))

theorem measurable_Gm (F : CharFamily) : Measurable F.Gm := by
  unfold CharFamily.Gm
  refine Finset.measurable_sum _ fun i _ => ?_
  exact measurable_const.mul (Complex.measurable_re.comp (measurable_Gchi (F.χ i)))

theorem Gchi_level_one_eq_Gz (χ : DirichletCharacter ℂ 1) (y : ℝ) :
    Gchi χ y = (Gz y : ℂ) := by
  have h1 : χ = 1 := DirichletCharacter.level_one χ
  have h2 : ∀ n : ℕ, χ n = 1 := fun n => by
    rw [h1]; exact MulChar.one_apply (isUnit_of_subsingleton _)
  simp only [Gchi, if_pos h1, Gz]
  have hfun : (fun n : ℕ => χ (n : ZMod 1)) = fun _ => (1 : ℂ) := funext h2
  rw [hfun]
  apply Complex.ext
  · simp
  · simp [ramp_one_im_eq_zero]

/-! ## 2. Exact Mellin Transform Integrals -/

theorem integrableOn_cesaroKernel_mul_cpow {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((cesaroKernel x t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have ha : (-s).re < -1 := by simp; linarith
  have hb : (-s - 1).re < -1 := by simp; linarith
  refine Integrable.mono' ((integrableOn_Ioi_norm_cpow_of_lt ha zero_lt_one).const_mul (x⁻¹)) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (integrableOn_Ioi_cpow_of_lt hb zero_lt_one).1
    exact (Complex.continuous_ofReal.comp (cesaroKernel_continuous_right x)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hle : cesaroKernel x t ≤ t / x := cesaroKernel_le_div hx ht0.le
    rw [norm_mul, cpow_sub _ _ htC, cpow_one, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (cesaroKernel_nonneg x t), Real.norm_of_nonneg ht0.le]
    calc cesaroKernel x t * (‖(t : ℂ) ^ (-s)‖ / t)
        ≤ (t / x) * (‖(t : ℂ) ^ (-s)‖ / t) := by gcongr
      _ = x⁻¹ * ‖(t : ℂ) ^ (-s)‖ := by field_simp

/-- Exact Mellin transform of the elementary Cesàro-1 ramp kernel `(t / x - 1)_+`. -/
theorem mellin_cesaroKernel {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (1 : ℝ), ((cesaroKernel x t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) =
      (x : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans_le hx
  have hs0 : s ≠ 0 := by
    rintro rfl; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioi x) measurableSet_Ioi
    (Ioi_subset_Ioi hx)]
  swap
  · intro t ht
    have ht' : t ≤ x := by simpa using ht.2
    rw [cesaroKernel_eq_zero_of_le hx0 ht']
    simp
  have hpt : ∀ t ∈ Ioi x, ((cesaroKernel x t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)
      = (x : ℂ)⁻¹ * (t : ℂ) ^ (-s) - (t : ℂ) ^ (-s - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hx0 ht
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    rw [cesaroKernel_eq_sub_of_ge hx0 ht.le, cpow_sub _ _ htC, cpow_one]
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have ha1 : (-s).re < -1 := by simp; linarith
  have ha2 : (-s - 1).re < -1 := by simp; linarith
  rw [integral_sub ((integrableOn_Ioi_cpow_of_lt ha1 hx0).const_mul _)
    (integrableOn_Ioi_cpow_of_lt ha2 hx0), integral_const_mul,
    integral_Ioi_cpow_of_lt ha1 hx0, integral_Ioi_cpow_of_lt ha2 hx0]
  rw [cpow_add _ _ hxC, cpow_one, sub_add_cancel]
  have h1s : -s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  field_simp
  ring

theorem mellin_cesaroKernel_nat (n : ℕ) (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (1 : ℝ), ((cesaroKernel n t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) =
      (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have h := mellin_cesaroKernel (x := (n : ℝ)) (by exact_mod_cast hn) hs
  simpa using h

private theorem mellin_cesaroKernel_norm {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (1 : ℝ), ‖((cesaroKernel x t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ =
      x ^ (-s.re) / (s.re * (s.re - 1)) := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans_le hx
  have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have h := mellin_cesaroKernel hx hσ
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hcongr : EqOn (fun t : ℝ => (‖((cesaroKernel x t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ : ℂ))
      (fun t : ℝ => ((cesaroKernel x t : ℝ) : ℂ) * (t : ℂ) ^ (-(s.re : ℂ) - 1)) (Ioi 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cesaroKernel_nonneg x t),
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hpow : (t : ℂ) ^ (-(s.re : ℂ) - 1) = ((t ^ (-s - 1).re : ℝ) : ℂ) := by
      rw [ofReal_cpow ht0.le]
      simp
    rw [hpow, ← Complex.ofReal_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, h]
  have hxpow : ((x ^ (-s.re) : ℝ) : ℂ) = (x : ℂ) ^ (-(s.re : ℂ)) := by
    rw [ofReal_cpow hx0.le]
    simp
  push_cast
  rw [hxpow]

/-- Exact Mellin transform of the scaled Dirichlet Cesàro ramp `t ↦ ramp f (t / x)` for `x ≥ 1`
and `1 < Re(s)`, yielding the elementary rational Mellin factor `1 / (s * (s - 1))` times
`x ^ (-s) * LSeries (fun n => f n * (Λ n : ℂ)) s`. -/
theorem mellin_ramp_div (f : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re)
    (hf : LSeriesSummable (fun n => f n * (Λ n : ℂ)) s) :
    ∫ t in Ioi (1 : ℝ), ramp f (t / x) * (t : ℂ) ^ (-s - 1) =
      (x : ℂ) ^ (-s) * LSeries (fun n => f n * (Λ n : ℂ)) s / (s * (s - 1)) := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans_le hx
  set a : ℕ → ℂ := fun n => f n * (Λ n : ℂ) with ha
  let F : ℕ → ℝ → ℂ := fun m t =>
    a (m + 1) * (((cesaroKernel (x * (m + 1 : ℕ)) t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
  have hint : ∀ m, Integrable (F m) (volume.restrict (Ioi 1)) := fun m => by
    have hxm : 0 < x * ((m + 1 : ℕ) : ℝ) := by positivity
    exact (integrableOn_cesaroKernel_mul_cpow hxm hs).const_mul _
  have hsum : Summable fun m => ∫ t in Ioi (1 : ℝ), ‖F m t‖ := by
    have h1 := (((summable_nat_add_iff 1).mpr hf.norm).mul_left (x ^ (-s.re))).div_const
      (s.re * (s.re - 1))
    refine h1.congr fun m => ?_
    simp only [F]
    have hxm : 1 ≤ x * ((m + 1 : ℕ) : ℝ) := by
      have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
      nlinarith
    simp_rw [norm_mul (a (m + 1))]
    rw [integral_const_mul, mellin_cesaroKernel_norm hxm hs,
      Real.mul_rpow hx0.le (Nat.cast_nonneg _), LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero m),
      Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hF : ∀ t, ∑' m, F m t = ramp f (t / x) * (t : ℂ) ^ (-s - 1) := by
    intro t
    have h1 := (hasSum_nat_add_iff' 1).mpr
      ((ramp_eq_tsum_hasSum f (t / x)).mul_right ((t : ℂ) ^ (-s - 1)))
    simp only [Finset.sum_range_one, ArithmeticFunction.map_zero, ofReal_zero, zero_mul,
      sub_zero] at h1
    have h2 : HasSum (fun m => F m t) (ramp f (t / x) * (t : ℂ) ^ (-s - 1)) := by
      refine h1.congr_fun fun m => ?_
      simp only [F, ha, cesaroKernel_div_eq]
      ring
    exact h2.tsum_eq
  simp_rw [hF] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr
    ((hf.hasSum.mul_left ((x : ℂ) ^ (-s))).div_const (s * (s - 1)))
  simp only [Finset.sum_range_one, LSeries.term_zero, mul_zero, zero_div, sub_zero] at h1
  have h2 : HasSum (fun m => ∫ t in Ioi (1 : ℝ), F m t)
      ((x : ℂ) ^ (-s) * LSeries a s / (s * (s - 1))) := by
    refine h1.congr_fun fun m => ?_
    simp only [F]
    have hxm : 1 ≤ x * ((m + 1 : ℕ) : ℝ) := by
      have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
      nlinarith
    rw [integral_const_mul, mellin_cesaroKernel hxm hs,
      LSeries.term_of_ne_zero (Nat.succ_ne_zero m)]
    have hcpow : ((x * ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ (-s) =
        (x : ℂ) ^ (-s) * ((m + 1 : ℕ) : ℂ) ^ (-s) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx0.le (Nat.cast_nonneg _)]
      simp
    rw [hcpow, cpow_neg, cpow_neg]
    ring
  exact h.unique h2

/-- Unscaled specialization (`x = 1`) of `mellin_ramp_div`. -/
theorem mellin_ramp (f : ℕ → ℂ) {s : ℂ} (hs : 1 < s.re)
    (hf : LSeriesSummable (fun n => f n * (Λ n : ℂ)) s) :
    ∫ t in Ioi (1 : ℝ), ramp f t * (t : ℂ) ^ (-s - 1) =
      LSeries (fun n => f n * (Λ n : ℂ)) s / (s * (s - 1)) := by
  have h := mellin_ramp_div f (x := 1) le_rfl hs hf
  simpa using h

theorem mellin_log_integrable_and_tendsto {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) ∧
    Tendsto (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1)) atTop (𝓝 0) := by
  have ha : (-s).re < -1 := by simp; linarith
  set e : ℝ := (s.re - 1) / 2 with he
  have he0 : 0 < e := by linarith
  have key : ∀ (c : ℂ) (y : ℝ), 1 < y →
      ‖((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ c‖ ≤ y ^ (e + c.re) / e := by
    intro c y hy
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hy.le),
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, Real.rpow_add hy0]
    calc Real.log y * y ^ c.re ≤ (y ^ e / e) * y ^ c.re := by
          gcongr
          exact Real.log_le_rpow_div hy0.le he0
      _ = y ^ e * y ^ c.re / e := by ring
  constructor
  · have hc : e + (-s).re < -1 := by simp; linarith
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hc zero_lt_one).div_const e) ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).1
      exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => key _ y hy
  · have hc : 0 < -(e + (-s + 1).re) := by simp; linarith
    have h := (tendsto_rpow_neg_atTop hc).div_const e
    rw [neg_neg, zero_div] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_gt_atTop 1] with y hy using key _ y hy

theorem mellin_log {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s) = 1 / (s - 1) ^ 2 := by
  have ha : (-s).re < -1 := by simp; linarith
  have hs1 : -s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨hi, ht⟩ := mellin_log_integrable_and_tendsto hs
  have hd : ∀ y ∈ Ici (1 : ℝ), HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1))
      ((-s + 1) * (((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) + (y : ℂ) ^ (-s)) y := by
    intro y hy
    have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
    refine ((Real.hasDerivAt_log hy0).ofReal_comp.mul
      (hasDerivAt_ofReal_cpow_const hy0 hs1)).congr_deriv ?_
    rw [add_sub_cancel_right, cpow_add _ _ hyC, cpow_one]
    push_cast
    field_simp
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((hi.const_mul _).add (integrableOn_Ioi_cpow_of_lt ha zero_lt_one)) ht
  rw [integral_add (hi.const_mul _) (integrableOn_Ioi_cpow_of_lt ha zero_lt_one),
    integral_const_mul, integral_Ioi_cpow_of_lt ha zero_lt_one] at h
  simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_mul, sub_zero] at h
  have e2 : (s - 1) ^ 2 = (-s + 1) ^ 2 := by ring
  rw [e2]
  field_simp at h ⊢
  linear_combination h

/-! ## 3. Mertens Upper Bound, Growth Bounds & Holomorphicity on `Re(s) > 1` -/

private theorem sum_log_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ N * Real.log N - N + 1 + Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : Real.log ((N : ℝ) / (N + 1)) ≤ (N : ℝ) / (N + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hN'.ne' (by positivity)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ N + 1 by positivity)
    have h3 : ((N : ℝ) + 1) * ((N : ℝ) / (N + 1) - 1) = -1 := by field_simp; ring
    rw [h3] at h2
    push_cast
    nlinarith

private theorem log_le_log_add_div (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c + x / c - 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / c by positivity)
  rw [Real.log_div hx.ne' hc.ne'] at h
  linarith

private theorem psi_add_log_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, Λ n + 1 + Real.log N ≤ 3 * N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  by_cases h25 : 25 ≤ N
  · have hp := Chebyshev.psi_le hN'
    rw [Chebyshev.psi, Nat.floor_natCast] at hp
    have h25' : (25 : ℝ) ≤ N := by exact_mod_cast h25
    have hs : 5 ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by linarith)
    have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
    have hL : Real.log N = 2 * Real.log (Real.sqrt N) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have hl := log_le_log_add_div (Real.sqrt N) 4 (by linarith) (by norm_num)
    set s := Real.sqrt N
    have hl' : Real.log N ≤ 0.78 + s / 2 := by linarith
    have h5 : 2 * s * Real.log N ≤ 2 * s * (0.78 + s / 2) :=
      mul_le_mul_of_nonneg_left hl' (by linarith)
    have h6 : Real.log 4 * N ≤ 1.39 * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  · have h1 : ∑ n ∈ Finset.Ioc 0 N, Λ n ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log n :=
      Finset.sum_le_sum fun n _ => ArithmeticFunction.vonMangoldt_le_log
    have h2 := sum_log_le N hN
    have h24 : (N : ℝ) ≤ 24 := by exact_mod_cast (by omega : N ≤ 24)
    by_cases h3 : 3 ≤ N
    · have h3' : (3 : ℝ) ≤ N := by exact_mod_cast h3
      have hl := log_le_log_add_div N 16 (by linarith) (by norm_num)
      have hl' : Real.log N ≤ 1.78 + N / 16 := by linarith
      have h5 : ((N : ℝ) + 2) * Real.log N ≤ (N + 2) * (1.78 + N / 16) :=
        mul_le_mul_of_nonneg_left hl' (by linarith)
      nlinarith
    · have h2' : (N : ℝ) ≤ 2 := by exact_mod_cast (by omega : N ≤ 2)
      have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)
      have h5 : ((N : ℝ) + 2) * Real.log N ≤ (N + 2) * (N - 1) :=
        mul_le_mul_of_nonneg_left hl (by linarith)
      nlinarith

theorem mertens_upper_nat (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, Λ n / (n : ℝ) ≤ Real.log N + 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hid := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt N
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at hid
  simp only [ArithmeticFunction.log_apply] at hid
  have h1 := sum_log_le N hN
  have h2 := psi_add_log_le N hN
  have h3 : N * ∑ n ∈ Finset.Ioc 0 N, Λ n / (n : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) + ∑ n ∈ Finset.Ioc 0 N, Λ n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn']
      have : N ≤ (N / n + 1) * n := by
        have := Nat.lt_div_mul_add (a := N) hn0
        nlinarith
      exact_mod_cast this
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    calc (N : ℝ) * (Λ n / n) = Λ n * ((N : ℝ) / n) := by ring
      _ ≤ Λ n * (((N / n : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left hlt hΛ
      _ = _ := by ring
  rw [← hid] at h3
  refine le_of_mul_le_mul_left ?_ hN'
  nlinarith

/-- Mertens upper bound `∑_{n ≤ y} Λ(n) / n ≤ log y + 2` for `y ≥ 1`. -/
theorem mertens_upper {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n / (n : ℝ) ≤ Real.log y + 2 := by
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have h := mertens_upper_nat ⌊y⌋₊ hN
  have hN' : (0 : ℝ) < (⌊y⌋₊ : ℕ) := by exact_mod_cast hN
  have hl : Real.log (⌊y⌋₊ : ℕ) ≤ Real.log y :=
    Real.log_le_log hN' (Nat.floor_le (by linarith))
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp only [Nat.cast_zero, div_zero, zero_add]
  linarith

/-- Sharp `O(y (log y + 2))` upper bound on `‖ramp f y‖` for any bounded arithmetic function `f`. -/
theorem ramp_norm_le_mul_log (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    ‖ramp f y‖ ≤ y * (Real.log y + 2) := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  unfold ramp
  calc ‖∑ n ∈ Finset.range (⌊y⌋₊ + 1), (Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)‖
      ≤ ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
          ‖(Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (⌊y⌋₊ + 1), y * (Λ n / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
          have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
          have h2 : max (y / n - 1) 0 ≤ y / n := cesaroKernel_le_div hn' hy0
          have h3 : 0 ≤ max (y / n - 1) 0 := le_max_right _ _
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg h0, Real.norm_of_nonneg h3]
          calc Λ n * ‖f n‖ * max (y / n - 1) 0
              ≤ Λ n * 1 * (y / n) := by gcongr; exact hf n
            _ = y * (Λ n / n) := by ring
    _ = y * ∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n / (n : ℝ) := (Finset.mul_sum ..).symm
    _ ≤ y * (Real.log y + 2) := mul_le_mul_of_nonneg_left (mertens_upper hy) hy0

/-- Quadratic envelope `‖ramp f y‖ ≤ 2 y²` for `y ≥ 1`. -/
theorem ramp_norm_le_sq (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    ‖ramp f y‖ ≤ 2 * y ^ 2 := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hlog : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hy)
  calc ‖ramp f y‖ ≤ y * (Real.log y + 2) := ramp_norm_le_mul_log f hf hy
    _ ≤ y * (y + 1) := by nlinarith
    _ ≤ 2 * y ^ 2 := by nlinarith

/-- Sharp `O(y (log y + 1))` growth bound for `Gchi χ y` on `y ≥ 1`. -/
theorem Gchi_growth_log {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → ‖Gchi χ y‖ ≤ C * y * (Real.log y + 1) := by
  by_cases h : χ = 1
  · refine ⟨3 + |1 + Real.eulerMascheroniConstant|, by positivity, fun y hy => ?_⟩
    have hr := ramp_norm_le_mul_log (fun n => χ n) (fun n => χ.norm_le_one _) hy
    have hy0 : 0 ≤ y := zero_le_one.trans hy
    have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy
    unfold Gchi
    rw [if_pos h]
    refine (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans ?_)
    rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hy0 hl0),
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hy0]
    have h1 : |1 + Real.eulerMascheroniConstant| * y ≤
        |1 + Real.eulerMascheroniConstant| * y * (Real.log y + 1) := by
      nlinarith [mul_nonneg (abs_nonneg (1 + Real.eulerMascheroniConstant)) hy0]
    nlinarith
  · set c := ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ with hc_def
    refine ⟨2 + c, by positivity, fun y hy => ?_⟩
    have hr := ramp_norm_le_mul_log (fun n => χ n) (fun n => χ.norm_le_one _) hy
    have hy0 : 0 ≤ y := zero_le_one.trans hy
    have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy
    unfold Gchi
    rw [if_neg h]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0, ← hc_def]
    have hc : 0 ≤ c := norm_nonneg _
    have hcy : c * y ≤ c * y * (Real.log y + 1) := by
      nlinarith [mul_nonneg hc hy0]
    nlinarith

/-- Quadratic growth bound `‖Gchi χ y‖ ≤ C y²` for `y ≥ 1`. -/
theorem Gchi_growth_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → ‖Gchi χ y‖ ≤ C * y ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := Gchi_growth_log χ
  refine ⟨C, hC, fun y hy => ?_⟩
  have hlog : Real.log y + 1 ≤ y := by
    linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hy)]
  have hCy : 0 ≤ C * y := mul_nonneg hC (zero_le_one.trans hy)
  calc ‖Gchi χ y‖ ≤ C * y * (Real.log y + 1) := hbound y hy
    _ ≤ C * y * y := mul_le_mul_of_nonneg_left hlog hCy
    _ = C * y ^ 2 := by ring

theorem Gz_growth_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |Gz y| ≤ C * y * (Real.log y + 1) := by
  obtain ⟨C, hC, hbound⟩ := Gchi_growth_log (1 : DirichletCharacter ℂ 1)
  refine ⟨C, hC, fun y hy => ?_⟩
  have h := hbound y hy
  rw [Gchi_level_one_eq_Gz, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem Gm_growth_log (F : CharFamily) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |F.Gm y| ≤ C * y * (Real.log y + 1) := by
  have hex : ∀ i : F.ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → ‖Gchi (F.χ i) y‖ ≤ C * y * (Real.log y + 1) :=
    fun i => Gchi_growth_log (F.χ i)
  choose C hC hbound using hex
  refine ⟨∑ i, F.a i * C i, Finset.sum_nonneg fun i _ => mul_nonneg (F.a_pos i).le (hC i),
    fun y hy => ?_⟩
  unfold CharFamily.Gm
  calc |∑ i, F.a i * (Gchi (F.χ i) y).re|
      ≤ ∑ i, |F.a i * (Gchi (F.χ i) y).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (F.a i * C i) * y * (Real.log y + 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_pos (F.a_pos i)]
        calc F.a i * |(Gchi (F.χ i) y).re|
            ≤ F.a i * ‖Gchi (F.χ i) y‖ :=
              mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (F.a_pos i).le
          _ ≤ F.a i * (C i * y * (Real.log y + 1)) :=
              mul_le_mul_of_nonneg_left (hbound i y hy) (F.a_pos i).le
          _ = (F.a i * C i) * y * (Real.log y + 1) := by ring
    _ = (∑ i, F.a i * C i) * y * (Real.log y + 1) := by
        rw [Finset.sum_mul, Finset.sum_mul]

theorem Gm_growth_sq (F : CharFamily) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |F.Gm y| ≤ C * y ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := Gm_growth_log F
  refine ⟨C, hC, fun y hy => ?_⟩
  have hlog : Real.log y + 1 ≤ y := by
    linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hy)]
  have hCy : 0 ≤ C * y := mul_nonneg hC (zero_le_one.trans hy)
  calc |F.Gm y| ≤ C * y * (Real.log y + 1) := hbound y hy
    _ ≤ C * y * y := mul_le_mul_of_nonneg_left hlog hCy
    _ = C * y ^ 2 := by ring

/-- Any measurable `g : ℝ → ℂ` with `‖g y‖ ≤ C * y * (log y + 1)` on `y ≥ 1` has an
absolutely convergent Mellin transform on the entire half-plane `Re(s) > 1`. -/
theorem integrableOn_mellin_of_log_growth {g : ℝ → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y * (Real.log y + 1)) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => g y * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  set e : ℝ := (s.re - 1) / 2 with he
  have he0 : 0 < e := by linarith
  have hc : e - s.re < -1 := by linarith
  refine Integrable.mono'
    ((integrableOn_Ioi_rpow_of_lt hc zero_lt_one).const_mul (C * (e⁻¹ + 1))) ?_ ?_
  · have ha : (-s - 1).re < -1 := by simp; linarith
    exact hg.aestronglyMeasurable.mul (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).1
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy
    have hlog : Real.log y ≤ y ^ e / e := Real.log_le_rpow_div hy0.le he0
    have h1ye : (1 : ℝ) ≤ y ^ e := Real.one_le_rpow hy.le he0.le
    have hlog1 : Real.log y + 1 ≤ (e⁻¹ + 1) * y ^ e := by
      have : y ^ e / e = e⁻¹ * y ^ e := by ring
      linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    have hpow1 : y * y ^ (-s.re - 1) = y ^ (-s.re) := by
      calc y * y ^ (-s.re - 1) = y ^ (1 : ℝ) * y ^ (-s.re - 1) := by rw [Real.rpow_one]
        _ = y ^ (1 + (-s.re - 1)) := (Real.rpow_add hy0 _ _).symm
        _ = y ^ (-s.re) := by congr 1; ring
    have hpow2 : y ^ e * y ^ (-s.re) = y ^ (e - s.re) := by
      rw [← Real.rpow_add hy0, sub_eq_add_neg]
    calc ‖g y‖ * y ^ (-s.re - 1)
        ≤ (C * y * (Real.log y + 1)) * y ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (hbound y hy.le) (Real.rpow_nonneg hy0.le _)
      _ = C * (Real.log y + 1) * (y * y ^ (-s.re - 1)) := by ring
      _ = C * (Real.log y + 1) * y ^ (-s.re) := by rw [hpow1]
      _ ≤ C * ((e⁻¹ + 1) * y ^ e) * y ^ (-s.re) := by
          gcongr
      _ = C * (e⁻¹ + 1) * (y ^ e * y ^ (-s.re)) := by ring
      _ = C * (e⁻¹ + 1) * y ^ (e - s.re) := by rw [hpow2]

/-- Complex differentiability (with explicit derivative formula) of the Mellin transform on
`Re(s) > 1` under `O(y (log y + 1))` growth. -/
theorem hasDerivAt_mellin_of_log_growth {g : ℝ → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y * (Real.log y + 1)) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (fun z : ℂ => ∫ y in Ioi (1 : ℝ), g y * (y : ℂ) ^ (-z - 1))
      (∫ y in Ioi (1 : ℝ), g y * (-(Real.log y : ℂ) * (y : ℂ) ^ (-s - 1))) s := by
  set δ : ℝ := (s.re - 1) / 2 with hδ
  have hδ0 : 0 < δ := by linarith
  set e : ℝ := δ / 4 with he
  have he0 : 0 < e := by linarith
  have hre : ∀ z ∈ Metric.ball s δ, 1 + δ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - s)
    rw [Complex.sub_re] at h1
    have h2 := (abs_le.mp (h1.trans hz.le)).1
    linarith
  have hmeasF : ∀ z : ℂ, AEStronglyMeasurable (fun y : ℝ => g y * (y : ℂ) ^ (-z - 1))
      (volume.restrict (Ioi 1)) := fun z => by
    have hpow : Measurable (fun y : ℝ => (y : ℂ) ^ (-z - 1)) :=
      Complex.measurable_ofReal.pow_const (-z - 1)
    exact (hg.mul hpow).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable
      (fun y : ℝ => g y * (-(Real.log y : ℂ) * (y : ℂ) ^ (-s - 1)))
      (volume.restrict (Ioi 1)) := by
    have h1 : Measurable (fun y : ℝ => -(Real.log y : ℂ)) :=
      (Complex.measurable_ofReal.comp Real.measurable_log).neg
    have h2 : Measurable (fun y : ℝ => (y : ℂ) ^ (-s - 1)) :=
      Complex.measurable_ofReal.pow_const (-s - 1)
    exact (hg.mul (h1.mul h2)).aestronglyMeasurable
  have hint : Integrable (fun y : ℝ => g y * (y : ℂ) ^ (-s - 1)) (volume.restrict (Ioi 1)) :=
    integrableOn_mellin_of_log_growth hg hC hbound hs
  have hdom_int : Integrable (fun y : ℝ => C * (e⁻¹ + 1) * e⁻¹ * y ^ (-1 - δ / 2))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - δ / 2 < -1) zero_lt_one).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y => g y * (y : ℂ) ^ (-z - 1))
    (F' := fun z y => g y * (-(Real.log y : ℂ) * (y : ℂ) ^ (-z - 1)))
    (Metric.ball_mem_nhds s hδ0)
    (Eventually.of_forall hmeasF) hint hmeasF' ?_ hdom_int ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy z hz => ?_)
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy1
    have hzr : 1 + δ ≤ z.re := hre z hz
    have hlog : Real.log y ≤ e⁻¹ * y ^ e := by
      have := Real.log_le_rpow_div hy0.le he0
      linarith [show y ^ e / e = e⁻¹ * y ^ e by ring]
    have h1ye : (1 : ℝ) ≤ y ^ e := Real.one_le_rpow hy1.le he0.le
    have hlog1 : Real.log y + 1 ≤ (e⁻¹ + 1) * y ^ e := by linarith
    have hlog_nn : 0 ≤ Real.log y := Real.log_nonneg hy1.le
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hlog_nn,
      Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre_z : (-z - 1).re = -z.re - 1 := by simp
    rw [hre_z]
    have hz_pow : y ^ (-z.re - 1) ≤ y ^ (-(1 + δ) - 1) :=
      Real.rpow_le_rpow_of_exponent_le hy1.le (by linarith)
    have hpow_comb : y * (y ^ e * (y ^ e * y ^ (-(1 + δ) - 1))) = y ^ (-1 - δ / 2) := by
      calc y * (y ^ e * (y ^ e * y ^ (-(1 + δ) - 1)))
          = y ^ (1 : ℝ) * (y ^ e * (y ^ e * y ^ (-(1 + δ) - 1))) := by rw [Real.rpow_one]
        _ = y ^ (1 + (e + (e + (-(1 + δ) - 1)))) := by
            rw [← Real.rpow_add hy0, ← Real.rpow_add hy0, ← Real.rpow_add hy0]
        _ = y ^ (-1 - δ / 2) := by congr 1; linarith
    calc ‖g y‖ * (Real.log y * y ^ (-z.re - 1))
        ≤ (C * y * (Real.log y + 1)) * (Real.log y * y ^ (-(1 + δ) - 1)) := by
          gcongr
          exact hbound y hy1.le
      _ ≤ (C * y * ((e⁻¹ + 1) * y ^ e)) * ((e⁻¹ * y ^ e) * y ^ (-(1 + δ) - 1)) := by
          gcongr
      _ = C * (e⁻¹ + 1) * e⁻¹ * (y * (y ^ e * (y ^ e * y ^ (-(1 + δ) - 1)))) := by ring
      _ = C * (e⁻¹ + 1) * e⁻¹ * y ^ (-1 - δ / 2) := by rw [hpow_comb]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy z _ => ?_)
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have hfun : (fun w : ℂ => g y * (y : ℂ) ^ (-w - 1)) =
        fun w : ℂ => g y * cexp ((Real.log y : ℂ) * (-w - 1)) := by
      funext w
      rw [Complex.cpow_def_of_ne_zero hyC, Complex.ofReal_log hy0.le]
    rw [hfun]
    have h1 : HasDerivAt (fun w : ℂ => (Real.log y : ℂ) * (-w - 1)) (-(Real.log y : ℂ)) z := by
      have h0 : HasDerivAt (fun w : ℂ => -w - 1) (-1 : ℂ) z := by
        simpa using (hasDerivAt_id' z).neg.sub_const (1 : ℂ)
      simpa using h0.const_mul (Real.log y : ℂ)
    have h2 := h1.cexp.const_mul (g y)
    refine h2.congr_deriv ?_
    rw [Complex.cpow_def_of_ne_zero hyC, Complex.ofReal_log hy0.le]
    ring

/-- Holomorphicity (`DifferentiableOn ℂ`) of the Mellin transform on `Re(s) > 1`. -/
theorem differentiableOn_mellin_of_log_growth {g : ℝ → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y * (Real.log y + 1)) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ y in Ioi (1 : ℝ), g y * (y : ℂ) ^ (-s - 1))
      {s : ℂ | 1 < s.re} :=
  fun _ hs => (hasDerivAt_mellin_of_log_growth hg hC hbound hs).differentiableAt.differentiableWithinAt

/-- Analyticity (`AnalyticOnNhd ℂ`) of the Mellin transform on `{s : ℂ | 1 < s.re}`. -/
theorem analyticOnNhd_mellin_of_log_growth {g : ℝ → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y * (Real.log y + 1)) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ y in Ioi (1 : ℝ), g y * (y : ℂ) ^ (-s - 1))
      {s : ℂ | 1 < s.re} :=
  (differentiableOn_mellin_of_log_growth hg hC hbound).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

theorem integrableOn_Gchi_mellin {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Gchi χ y * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  obtain ⟨C, hC, hbound⟩ := Gchi_growth_log χ
  exact integrableOn_mellin_of_log_growth (measurable_Gchi χ) hC hbound hs

theorem integrableOn_Gm_mellin (F : CharFamily) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => (F.Gm y : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  obtain ⟨C, hC, hbound⟩ := Gm_growth_log F
  refine integrableOn_mellin_of_log_growth (Complex.measurable_ofReal.comp (measurable_Gm F))
    hC (fun y hy => ?_) hs
  dsimp only [Function.comp_apply]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hbound y hy

theorem differentiableOn_mellin_Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1))
      {s : ℂ | 1 < s.re} := by
  obtain ⟨C, hC, hbound⟩ := Gchi_growth_log χ
  exact differentiableOn_mellin_of_log_growth (measurable_Gchi χ) hC hbound

theorem analyticOnNhd_mellin_Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1))
      {s : ℂ | 1 < s.re} := by
  obtain ⟨C, hC, hbound⟩ := Gchi_growth_log χ
  exact analyticOnNhd_mellin_of_log_growth (measurable_Gchi χ) hC hbound

theorem differentiableOn_mellin_Gm (F : CharFamily) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ y in Ioi (1 : ℝ), (F.Gm y : ℂ) * (y : ℂ) ^ (-s - 1))
      {s : ℂ | 1 < s.re} := by
  obtain ⟨C, hC, hbound⟩ := Gm_growth_log F
  refine differentiableOn_mellin_of_log_growth
    (Complex.measurable_ofReal.comp (measurable_Gm F)) hC fun y hy => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hbound y hy

theorem analyticOnNhd_mellin_Gm (F : CharFamily) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ y in Ioi (1 : ℝ), (F.Gm y : ℂ) * (y : ℂ) ^ (-s - 1))
      {s : ℂ | 1 < s.re} := by
  obtain ⟨C, hC, hbound⟩ := Gm_growth_log F
  refine analyticOnNhd_mellin_of_log_growth
    (Complex.measurable_ofReal.comp (measurable_Gm F)) hC fun y hy => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hbound y hy

/-! ## 4. Exact Mellin Transforms of `Gchi`, `Gz`, Conjugation & `CharFamily.Gm` -/

/-- Exact Mellin transform of `Gchi χ` for the level-1 trivial character `χ` on `Re(s) > 1`. -/
theorem mellin_Gchi_modOne (χ : DirichletCharacter ℂ 1) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1 -
          (1 + Real.eulerMascheroniConstant) * s) / (s * (s - 1)) := by
  have h1 : χ = 1 := DirichletCharacter.level_one χ
  have h2 : ∀ n : ℕ, χ n = 1 := fun n => by
    rw [h1]; exact MulChar.one_apply (isUnit_of_subsingleton _)
  have ha : (-s).re < -1 := by simp; linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hi_log := (mellin_log_integrable_and_tendsto hs).1
  have hi_pow := integrableOn_Ioi_cpow_of_lt ha zero_lt_one
  have hi_ramp : IntegrableOn (fun y : ℝ => ramp (fun _ => 1) y * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
    refine integrableOn_mellin_of_log_growth (measurable_ramp _) (by norm_num : (0 : ℝ) ≤ 2)
      (fun y hy => ?_) hs
    have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy
    calc ‖ramp (fun _ => 1) y‖ ≤ y * (Real.log y + 2) :=
          ramp_norm_le_mul_log (fun _ => 1) (fun _ => by simp) hy
      _ ≤ 2 * y * (Real.log y + 1) := by nlinarith
  have hc : EqOn (fun y : ℝ => Gchi χ y * (y : ℂ) ^ (-s - 1))
      (fun y : ℝ => ramp (fun _ => 1) y * (y : ℂ) ^ (-s - 1) -
        ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s) +
        ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have h3 : (y : ℂ) ^ (-s) = y * (y : ℂ) ^ (-s - 1) := by
      rw [cpow_sub _ _ hyC, cpow_one]
      field_simp
    have hfun : (fun n : ℕ => χ (n : ZMod 1)) = fun _ => (1 : ℂ) := funext h2
    simp only [Gchi, if_pos h1, hfun]
    rw [h3]
    push_cast
    ring
  have hi_sub : IntegrableOn
      (fun y : ℝ => ramp (fun _ => 1) y * (y : ℂ) ^ (-s - 1) -
        ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) := hi_ramp.sub hi_log
  rw [setIntegral_congr_fun measurableSet_Ioi hc,
    integral_add hi_sub (hi_pow.const_mul _),
    integral_sub hi_ramp hi_log, integral_const_mul,
    integral_Ioi_cpow_of_lt ha zero_lt_one, mellin_log hs]
  have hsum_vM : LSeriesSummable (fun n => (1 : ℂ) * (Λ n : ℂ)) s := by
    simpa using ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [mellin_ramp (fun _ => 1) hs hsum_vM]
  have h4 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hL : LSeries (fun n => (1 : ℂ) * (Λ n : ℂ)) s = -deriv riemannZeta s / riemannZeta s := by
    simpa [one_mul] using h4
  rw [hL, neg_div (riemannZeta s)]
  have e2 : -s + 1 = -(s - 1) := by ring
  rw [e2]
  generalize deriv riemannZeta s / riemannZeta s = D
  simp only [ofReal_one, one_cpow]
  push_cast
  field_simp
  ring

/-- Exact Mellin transform of `Gz` on `Re(s) > 1`. -/
theorem mellin_Gz {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), (Gz y : ℂ) * (y : ℂ) ^ (-s - 1) =
      -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1 -
          (1 + Real.eulerMascheroniConstant) * s) / (s * (s - 1)) := by
  have h := mellin_Gchi_modOne (1 : DirichletCharacter ℂ 1) hs
  simpa [Gchi_level_one_eq_Gz] using h

/-- Exact Mellin transform of `Gchi χ` for any non-trivial character `χ ≠ 1` on `Re(s) > 1`. -/
theorem mellin_Gchi_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          s * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) /
        (s * (s - 1)) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  set c := deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 with hc
  have ha : (-s).re < -1 := by simp; linarith
  have hi_pow := (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).const_mul c
  have hi_ramp : IntegrableOn (fun y : ℝ => ramp (fun n => χ n) y * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
    refine integrableOn_mellin_of_log_growth (measurable_ramp _) (by norm_num : (0 : ℝ) ≤ 2)
      (fun y hy => ?_) hs
    have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy
    calc ‖ramp (fun n => χ n) y‖ ≤ y * (Real.log y + 2) :=
          ramp_norm_le_mul_log (fun n => χ n) (fun n => χ.norm_le_one _) hy
      _ ≤ 2 * y * (Real.log y + 1) := by nlinarith
  have hcongr : EqOn (fun y : ℝ => Gchi χ y * (y : ℂ) ^ (-s - 1))
      (fun y : ℝ => ramp (fun n => χ n) y * (y : ℂ) ^ (-s - 1) + c * (y : ℂ) ^ (-s)) (Ioi 1) := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hy).ne'
    simp only [Gchi, if_neg hχ, ← hc]
    rw [cpow_sub _ _ hy0, cpow_one]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_add hi_ramp hi_pow,
    mellin_ramp (fun n => χ n) hs (χ.LSeriesSummable_twist_vonMangoldt hs),
    integral_const_mul, integral_Ioi_cpow_of_lt ha zero_lt_one]
  have hL : LSeries (fun n => χ n * (Λ n : ℂ)) s =
      -deriv (LSeries fun n => χ n) s / LSeries (fun n => χ n) s :=
    χ.LSeries_twist_vonMangoldt_eq hs
  rw [hL, ← χ.LFunction_eq_LSeries hs, ← χ.deriv_LFunction_eq_deriv_LSeries hs]
  have e2 : -s + 1 = -(s - 1) := by ring
  rw [e2, neg_div (DirichletCharacter.LFunction χ s)]
  generalize deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s = d
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

private lemma ofReal_cpow_conj {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    (x : ℂ) ^ ((starRingEnd ℂ) s) = (starRingEnd ℂ) ((x : ℂ) ^ s) := by
  have h := Complex.conj_cpow (x : ℂ) ((starRingEnd ℂ) s)
    (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_pos.ne)
  rwa [Complex.conj_ofReal, Complex.conj_conj] at h

private lemma Gammaℝ_conj (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  have h1 : -(starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (-s / 2) := by
    rw [map_div₀, map_neg, map_ofNat]
  have h2 : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, map_ofNat]
  rw [Gammaℝ, Gammaℝ, h1, h2, ofReal_cpow_conj Real.pi_pos.le, Complex.Gamma_conj, map_mul]

private lemma hurwitz_conj_of_re {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.hurwitzZeta a ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (HurwitzZeta.hurwitzZeta a s) := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  rw [← (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ha hs').tsum_eq,
    ← (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ha hs).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) + a := add_nonneg (Nat.cast_nonneg n) ha.1
  have hc : ((n : ℂ) + (a : ℂ)) = (((n : ℝ) + a : ℝ) : ℂ) := by push_cast; rfl
  rw [map_div₀, map_one, hc, ofReal_cpow_conj hn]

private lemma hurwitz_conj (a : UnitAddCircle) (s : ℂ) :
    HurwitzZeta.hurwitzZeta a ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (HurwitzZeta.hurwitzZeta a s) := by
  let reg : UnitAddCircle → ℂ → ℂ := fun b z =>
    HurwitzZeta.hurwitzZeta b z - 1 / (z - 1) / Gammaℝ z
  have hdiff : ∀ b : UnitAddCircle, Differentiable ℂ (reg b) := fun b z => by
    rcases eq_or_ne z 1 with rfl | hz
    · exact HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div b
    · have e : reg b = fun w => HurwitzZeta.hurwitzZeta b w - (w - 1)⁻¹ * (Gammaℝ w)⁻¹ := by
        funext w; simp [reg, div_eq_mul_inv]
      rw [e]
      exact (HurwitzZeta.differentiableAt_hurwitzZeta b hz).sub
        (((differentiableAt_id.sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hz)).mul
          (differentiable_Gammaℝ_inv z))
  have hpole : ∀ z : ℂ, 1 / ((starRingEnd ℂ) z - 1) / Gammaℝ ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (1 / (z - 1) / Gammaℝ z) := fun z => by
    rw [Gammaℝ_conj]; simp [map_div₀]
  induction a using QuotientAddGroup.induction_on with
  | H b =>
    have hb : ((b : ℝ) : UnitAddCircle) = ((Int.fract b : ℝ) : UnitAddCircle) := by
      rw [QuotientAddGroup.eq]
      exact ⟨-⌊b⌋, by simp only [Int.fract, zsmul_eq_mul, mul_one, Int.cast_neg]; ring⟩
    rw [hb]
    set a₀ : UnitAddCircle := ((Int.fract b : ℝ) : UnitAddCircle)
    have ha : Int.fract b ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩
    have hreg : ∀ z : ℂ, 1 < z.re →
        (starRingEnd ℂ) (reg a₀ ((starRingEnd ℂ) z)) = reg a₀ z := by
      intro z hz
      have h1 := hurwitz_conj_of_re ha (s := (starRingEnd ℂ) z) (by rwa [Complex.conj_re])
      have h2 := hpole ((starRingEnd ℂ) z)
      rw [Complex.conj_conj] at h1 h2
      simp only [reg, a₀, map_sub, h1, h2]
    have hF : Differentiable ℂ (fun z => (starRingEnd ℂ) (reg a₀ ((starRingEnd ℂ) z))) :=
      fun z => differentiableAt_conj_conj_iff.mpr (hdiff a₀ _)
    have heq : (fun z => (starRingEnd ℂ) (reg a₀ ((starRingEnd ℂ) z))) = reg a₀ :=
      AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (hF.differentiableOn.analyticOnNhd isOpen_univ)
        ((hdiff a₀).differentiableOn.analyticOnNhd isOpen_univ)
        (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hreg)
    have h3 := congrFun heq ((starRingEnd ℂ) s)
    rw [Complex.conj_conj] at h3
    have e : ∀ w, HurwitzZeta.hurwitzZeta a₀ w = reg a₀ w + 1 / (w - 1) / Gammaℝ w :=
      fun w => by simp [reg]
    change HurwitzZeta.hurwitzZeta a₀ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (HurwitzZeta.hurwitzZeta a₀ s)
    rw [e ((starRingEnd ℂ) s), e s, map_add, ← h3, hpole]

/-- Conjugation symmetry `L(χ⁻¹, s̄) = conj(L(χ, s))` for all `s : ℂ`. -/
theorem LFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by
  simp only [DirichletCharacter.LFunction, ZMod.LFunction, map_mul, map_sum]
  congr 1
  · have h := ofReal_cpow_conj (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (-s)
    simpa using h
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hurwitz_conj, ← MulChar.star_apply']
    rfl

private theorem deriv_conj_comp_conj (f : ℂ → ℂ) (x : ℂ) :
    deriv ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) x) =
      (starRingEnd ℂ) (deriv f x) := by
  by_cases hf : DifferentiableAt ℂ f x
  · exact hf.hasDerivAt.conj_conj.deriv
  · have hg : ¬ DifferentiableAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) x) := by
      rw [differentiableAt_conj_conj_iff, Complex.conj_conj]
      exact hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hg, map_zero]

/-- Conjugation symmetry `conj (Gchi χ y) = Gchi χ⁻¹ y`. -/
theorem Gchi_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (starRingEnd ℂ) (Gchi χ y) = Gchi χ⁻¹ y := by
  by_cases h1 : χ = 1
  · subst h1
    simp only [Gchi, inv_one, if_true]
    rw [map_add, map_sub, ramp_conj, inv_one, Complex.conj_ofReal, Complex.conj_ofReal]
  · have h2 : χ⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.mp h)
    simp only [Gchi, h1, h2, if_false]
    have hL : DirichletCharacter.LFunction χ⁻¹ =
        (starRingEnd ℂ) ∘ DirichletCharacter.LFunction χ ∘ (starRingEnd ℂ) := by
      funext s
      have h := LFunction_conj χ ((starRingEnd ℂ) s)
      rw [Complex.conj_conj] at h
      exact h
    have h1c : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
    rw [map_add, map_mul, map_div₀, ramp_conj, Complex.conj_ofReal, hL]
    congr 2
    rw [← h1c, deriv_conj_comp_conj, h1c]
    simp only [Function.comp_apply, h1c]

open Classical in
/-- Closed-form meromorphic Mellin transform value for an admissible character `χ`. -/
def mellinTerm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  if χ = 1 then
    -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1 -
        (1 + Real.eulerMascheroniConstant) * s) / (s * (s - 1))
  else
    -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        s * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) /
      (s * (s - 1))

theorem mellin_Gchi_eq_mellinTerm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hadm : N = 1 ∨ χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) = mellinTerm χ s := by
  by_cases h1 : χ = 1
  · rcases hadm with rfl | hne
    · simp only [mellinTerm, if_pos h1]
      exact mellin_Gchi_modOne χ hs
    · exact absurd h1 hne
  · simp only [mellinTerm, if_neg h1]
    exact mellin_Gchi_of_ne_one χ h1 hs

/-- Explicit Mellin transform identity for any `CharFamily.Gm` on `Re(s) > 1`. -/
theorem mellin_Gm_eq_sum (F : CharFamily) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), (F.Gm y : ℂ) * (y : ℂ) ^ (-s - 1) =
      ∑ i, ((F.a i : ℂ) / 2) * (mellinTerm (F.χ i) s + mellinTerm (F.χ i)⁻¹ s) := by
  have hfun : (fun y : ℝ => (F.Gm y : ℂ) * (y : ℂ) ^ (-s - 1)) =
      fun y : ℝ => ∑ i, ((F.a i : ℂ) / 2) *
        (Gchi (F.χ i) y * (y : ℂ) ^ (-s - 1) + Gchi (F.χ i)⁻¹ y * (y : ℂ) ^ (-s - 1)) := by
    funext y
    unfold CharFamily.Gm
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hre : ((Gchi (F.χ i) y).re : ℂ) = (Gchi (F.χ i) y + Gchi (F.χ i)⁻¹ y) / 2 := by
      rw [← Gchi_conj (F.χ i) y, Complex.add_conj]
      push_cast
      ring
    rw [hre]
    ring
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi1 := integrableOn_Gchi_mellin (F.χ i) hs
    have hi2 := integrableOn_Gchi_mellin (F.χ i)⁻¹ hs
    rw [integral_const_mul, integral_add hi1 hi2]
    have hadm_inv : F.N i = 1 ∨ (F.χ i)⁻¹ ≠ 1 := by
      rcases F.adm i with hN | hne
      · exact Or.inl hN
      · exact Or.inr fun h => hne (inv_eq_one.mp h)
    rw [mellin_Gchi_eq_mellinTerm (F.χ i) (F.adm i) hs,
      mellin_Gchi_eq_mellinTerm (F.χ i)⁻¹ hadm_inv hs]
  · intro i _
    exact ((integrableOn_Gchi_mellin (F.χ i) hs).add
      (integrableOn_Gchi_mellin (F.χ i)⁻¹ hs)).const_mul _

/-! ## 5. Mellin–Laplace Equivalence, Iterated Derivatives & Windowed Landau Tails -/

/-- Change of variables `y = exp u` identifying Laplace transforms on `(0, ∞)` with
Mellin transforms on `(1, ∞)`. -/
theorem mellin_eq_laplace (g : ℝ → ℂ) (s : ℂ) :
    ∫ u in Ioi (0 : ℝ), g (Real.exp u) * cexp (-s * u) =
      ∫ y in Ioi (1 : ℝ), g y * (y : ℂ) ^ (-s - 1) := by
  have himg : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.one_lt_exp_iff.2 hu
    · intro hy
      exact ⟨Real.log y, Real.log_pos hy, Real.exp_log (zero_lt_one.trans hy)⟩
  have hd : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt Real.exp (Real.exp u) (Ioi 0) u :=
    fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt
  have e := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd Real.exp_injective.injOn
    (fun y => g y * (y : ℂ) ^ (-s - 1))
  rw [himg] at e
  rw [e]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul]
  have hpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hne : ((Real.exp u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hpos.le, Real.log_exp,
    Complex.ofReal_exp]
  rw [← mul_assoc, mul_comm (cexp (u : ℂ)) (g (Real.exp u)), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem mellin_Gm_eq_laplace (F : CharFamily) (s : ℂ) :
    ∫ u in Ioi (0 : ℝ), (F.Gm (Real.exp u) : ℂ) * cexp (-s * u) =
      ∫ y in Ioi (1 : ℝ), (F.Gm y : ℂ) * (y : ℂ) ^ (-s - 1) :=
  mellin_eq_laplace (fun y => (F.Gm y : ℂ)) s

/-- Exact Gamma/factorial Laplace kernel integral `∫₀^∞ u^k e^{-au} / k! du = a^{-(k+1)}`. -/
theorem kernel_integral (k : ℕ) {a : ℝ} (ha : 0 < a) :
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

private theorem integrableOn_u_pow_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-b * u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := b)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hb
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

private theorem laplace_deriv_bound (g : ℝ → ℝ) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (b : ℝ) (z : ℂ)
    (hz : 2 + b ≤ z.re) (u : ℝ) (hu : 0 < u) :
    ‖(g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u)‖ ≤ C * (u ^ k * Real.exp (-b * u)) := by
  have h1 : ‖(g u : ℂ)‖ ≤ C * Real.exp (2 * u) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgC u hu.le
  have h2 : ‖((-u : ℝ) : ℂ) ^ k‖ = u ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu]
  have h3 : ‖cexp (-z * u)‖ ≤ Real.exp (-(2 + b) * u) := by
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hC : 0 ≤ C * Real.exp (2 * u) := le_trans (norm_nonneg _) h1
  rw [norm_mul, norm_mul, h2]
  calc ‖(g u : ℂ)‖ * u ^ k * ‖cexp (-z * u)‖
      ≤ C * Real.exp (2 * u) * u ^ k * Real.exp (-(2 + b) * u) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 (norm_nonneg _)
          (mul_nonneg hC (by positivity))
    _ = C * (u ^ k * (Real.exp (2 * u) * Real.exp (-(2 + b) * u))) := by ring
    _ = C * (u ^ k * Real.exp (-b * u)) := by rw [← Real.exp_add]; ring_nf

/-- Iterated differentiation under the Laplace integral for `Re(s) > 2`. -/
theorem iteratedDeriv_laplace (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u))
    (k : ℕ) {s : ℂ} (hs : 2 < s.re) :
    iteratedDeriv k (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) s =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-s * u) := by
  have hstep : ∀ (j : ℕ) (w : ℂ), 2 < w.re →
      HasDerivAt (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-z * u))
        (∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (j + 1) * cexp (-w * u)) w := by
    intro j w hw
    set δ := (w.re - 2) / 2 with hδ
    have hδpos : 0 < δ := by linarith
    have hre : ∀ z ∈ Metric.ball w δ, 2 + δ ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h1 := Complex.abs_re_le_norm (z - w)
      rw [Complex.sub_re] at h1
      have h2 := (abs_le.mp (h1.trans hz.le)).1
      linarith
    have hmeas : ∀ (m : ℕ) (z : ℂ),
        AEStronglyMeasurable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ m * cexp (-z * u))
          (volume.restrict (Ioi 0)) := fun m z =>
      Measurable.aestronglyMeasurable (by fun_prop)
    have hint : Integrable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-w * u))
        (volume.restrict (Ioi 0)) := by
      refine Integrable.mono' ((integrableOn_u_pow_exp j hδpos).const_mul C) (hmeas j w) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
      exact laplace_deriv_bound g C hgC j δ w (hre w (Metric.mem_ball_self hδpos)) u hu
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-z * u))
      (F' := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (j + 1) * cexp (-z * u))
      (Metric.ball_mem_nhds w hδpos)
      (Eventually.of_forall fun z => hmeas j z) hint (hmeas (j + 1) w) ?_
      ((integrableOn_u_pow_exp (j + 1) hδpos).const_mul C) ?_).2
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu z hz => ?_)
      exact laplace_deriv_bound g C hgC (j + 1) δ z (hre z hz) u hu
    · refine Eventually.of_forall fun u z _ => ?_
      have h1 : HasDerivAt (fun x : ℂ => -x * (u : ℂ)) (-(u : ℂ)) z := by
        simpa using (hasDerivAt_id' z).neg.mul_const (u : ℂ)
      have h2 := h1.cexp.const_mul ((g u : ℂ) * ((-u : ℝ) : ℂ) ^ j)
      refine h2.congr_deriv ?_
      push_cast
      ring
  have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : EqOn (iteratedDeriv k fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u))
        (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
        {z : ℂ | 2 < z.re} := fun z hz => ih hz
    rw [(eventuallyEq_of_mem (hopen.mem_nhds hs) heq).deriv_eq]
    exact (hstep k s hs).deriv

private lemma landau_tails_integrable (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)) (Ioi 0) :=
  (integrableOn_u_pow_exp k ha).div_const _

private lemma landau_tails_chernoff (k : ℕ) {s l U V : ℝ} (hl : 0 ≤ l) (hs : l < s) :
    ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp (-s * u) / (k.factorial : ℝ) ≤
      Real.exp (-(l * V)) * ((s - l) ^ (k + 1))⁻¹ +
        Real.exp (l * U) * ((s + l) ^ (k + 1))⁻¹ := by
  have ha : 0 < s - l := by linarith
  have hb : 0 < s + l := by linarith
  have hs0 : 0 < s := by linarith
  have i1 := (landau_tails_integrable k ha).const_mul (Real.exp (-(l * V)))
  have i2 := (landau_tails_integrable k hb).const_mul (Real.exp (l * U))
  have i0 := landau_tails_integrable k hs0
  have i3 := i1.add i2
  rw [← kernel_integral k ha, ← kernel_integral k hb, ← integral_const_mul, ← integral_const_mul,
    ← integral_add i1 i2]
  have hm : MeasurableSet (Ioi (0 : ℝ) \ Icc U V) := measurableSet_Ioi.diff measurableSet_Icc
  refine le_trans (setIntegral_mono_on (IntegrableOn.mono_set i0 sdiff_subset)
    (IntegrableOn.mono_set i3 sdiff_subset) hm ?_)
    (setIntegral_mono_set i3 ?_ sdiff_subset.eventuallyLE)
  · intro u hu
    have hu0 : 0 < u := hu.1
    have hp : 0 ≤ u ^ k / (k.factorial : ℝ) := by positivity
    have e1 : Real.exp (-(l * V)) * Real.exp (-(s - l) * u) = Real.exp (-s * u + l * (u - V)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (l * U) * Real.exp (-(s + l) * u) = Real.exp (-s * u + l * (U - u)) := by
      rw [← Real.exp_add]; congr 1; ring
    have key : Real.exp (-s * u) ≤
        Real.exp (-s * u + l * (u - V)) + Real.exp (-s * u + l * (U - u)) := by
      have hn := hu.2
      rw [mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h
      · have : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (U - u)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])
        linarith [Real.exp_pos (-s * u + l * (u - V))]
      · have : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])
        linarith [Real.exp_pos (-s * u + l * (U - u))]
    rw [← e1, ← e2] at key
    have := mul_le_mul_of_nonneg_left key hp
    simp only [Pi.add_apply]
    calc u ^ k * Real.exp (-s * u) / (k.factorial : ℝ)
        = u ^ k / (k.factorial : ℝ) * Real.exp (-s * u) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    simp only [Pi.add_apply, Pi.zero_apply]
    positivity

private lemma landau_tails_pow (k : ℕ) {σ a x c : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (h : x + k * ((σ - a) / a) ≤ c) :
    Real.exp x * (a ^ (k + 1))⁻¹ ≤ Real.exp c / a / σ ^ k := by
  have h1 : σ / a ≤ Real.exp ((σ - a) / a) := by
    have := Real.add_one_le_exp ((σ - a) / a)
    have e : (σ - a) / a + 1 = σ / a := by field_simp; ring
    linarith
  have h2 : (σ / a) ^ k ≤ Real.exp (k * ((σ - a) / a)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h1 k
  have h3 : Real.exp x * (σ / a) ^ k ≤ Real.exp c := by
    calc Real.exp x * (σ / a) ^ k ≤ Real.exp x * Real.exp (k * ((σ - a) / a)) := by gcongr
      _ = Real.exp (x + k * ((σ - a) / a)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp c := Real.exp_le_exp.2 h
  calc Real.exp x * (a ^ (k + 1))⁻¹ = Real.exp x * (σ / a) ^ k / a / σ ^ k := by
        rw [div_pow, pow_succ]; field_simp
    _ ≤ Real.exp c / a / σ ^ k := by gcongr

/-- Chernoff tail bound for the Landau derivative kernel outside a multiplicative window
`[U, (1 + δ) U]` (with growth exponent `2`). -/
theorem landau_tails {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧
      ∫ u in Ioi (0 : ℝ) \ Icc U ((1 + δ) * U),
        u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) ≤ C / σ ^ k := by
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℝ, 2 < l ∧ l * δ = 6 + 2 * δ := by
    refine ⟨2 + 6 / δ, ?_, by field_simp; ring⟩
    have : 0 < 6 / δ := by positivity
    linarith
  set M : ℝ := l * (1 + δ) with hM
  have hMl : l < M := by nlinarith
  set σ : ℝ := M * (2 + l) with hσ
  have hσ1 : l * (2 + l) < σ := by rw [hσ]; gcongr
  have hs : l < σ - 2 := by nlinarith
  have ha : 0 < σ - 2 - l := by linarith
  have hb : 0 < σ - 2 + l := by linarith
  have hσ0 : 0 < σ := by linarith
  refine ⟨σ, by linarith, Real.exp 1 / (σ - 2 - l) + Real.exp 0 / (σ - 2 + l), fun U hU => ?_⟩
  have hx : 0 ≤ (1 + δ / 2) * σ * U := by positivity
  have hk1 := Nat.le_ceil ((1 + δ / 2) * σ * U)
  have hk2 := (Nat.ceil_lt_add_one hx).le
  set k := ⌈(1 + δ / 2) * σ * U⌉₊
  have hσU : 0 ≤ σ * U := by positivity
  refine ⟨k, ?_, ?_⟩
  · nlinarith [mul_nonneg hδ.le hσU]
  · have e : (2 - σ) = -(σ - 2) := by ring
    rw [e, add_div]
    refine (landau_tails_chernoff k (by linarith : 0 ≤ l) hs).trans (add_le_add ?_ ?_)
    · apply landau_tails_pow k hσ0 ha
      have e1 : (σ - (σ - 2 - l)) / (σ - 2 - l) = 1 / (M - 1) := by
        have : 0 < M - 1 := by linarith
        rw [div_eq_div_iff ha.ne' this.ne']; dsimp only [σ]; ring
      have e2 : (1 + δ / 2) * σ = M * (M - 1) := by
        have : (1 + δ / 2) * (2 + l) = M - 1 := by dsimp only [M]; nlinarith
        dsimp only [σ]; rw [← this]; ring
      have e3 : (k : ℝ) * (1 / (M - 1)) ≤ M * U + 1 := by
        rw [mul_one_div, div_le_iff₀ (by linarith : 0 < M - 1)]
        rw [e2] at hk2
        nlinarith
      have e4 : l * ((1 + δ) * U) = M * U := by dsimp only [M]; ring
      rw [e1, e4]; linarith
    · apply landau_tails_pow k hσ0 hb
      have e1 : (k : ℝ) * ((σ - (σ - 2 + l)) / (σ - 2 + l)) = -((k : ℝ) * (l - 2) / (σ - 2 + l)) := by
        ring
      have e2 : (1 + δ / 2) * (l - 2) = l + 1 := by nlinarith
      have e3 : l * U ≤ (k : ℝ) * (l - 2) / (σ - 2 + l) := by
        rw [le_div_iff₀ hb]
        have h1 : (1 + δ / 2) * σ * U * (l - 2) ≤ k * (l - 2) :=
          mul_le_mul_of_nonneg_right hk1 (by linarith)
        have h2 : (1 + δ / 2) * σ * U * (l - 2) = (l + 1) * σ * U := by rw [← e2]; ring
        have h3 : l * (σ - 2 + l) ≤ (l + 1) * σ := by nlinarith
        have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : 0 ≤ U)
        nlinarith
      rw [e1]; linarith

private lemma rpow_dominates_log (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y → 1 ≤ Y ∧ K * Real.log Y ≤ Y ^ η := by
  have he : 0 < η / 2 := half_pos hη
  have h1 : Tendsto (fun Y : ℝ => Y ^ (η / 2)) atTop atTop := tendsto_rpow_atTop he
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 (h1.eventually_ge_atTop (K / (η / 2)))
  refine ⟨max Y₀ 1, fun Y hY => ⟨le_trans (le_max_right _ _) hY, ?_⟩⟩
  have hY1 : 1 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hl : Real.log Y ≤ Y ^ (η / 2) / (η / 2) := Real.log_le_rpow_div hY0.le he
  have ha : K / (η / 2) ≤ Y ^ (η / 2) := hY₀ Y (le_trans (le_max_left _ _) hY)
  have hp : 0 ≤ Y ^ (η / 2) := by positivity
  have heq : Y ^ η = Y ^ (η / 2) * Y ^ (η / 2) := by
    rw [← Real.rpow_add hY0]; congr 1; ring
  calc K * Real.log Y ≤ K * (Y ^ (η / 2) / (η / 2)) := mul_le_mul_of_nonneg_left hl hK
    _ = K / (η / 2) * Y ^ (η / 2) := by ring
    _ ≤ Y ^ (η / 2) * Y ^ (η / 2) := mul_le_mul_of_nonneg_right ha hp
    _ = Y ^ η := heq.symm

/-- Bridge from a pointwise power-window bound `HasRpowWindow F.Gm θ δ C` to the integral
`CharFamily.WindowHyp F θ δ` consumed by the windowed Landau nonvanishing theorem. -/
theorem windowHyp_of_hasRpowWindow (F : CharFamily) {θ δ C : ℝ} (hδ : 0 < δ)
    (h : HasRpowWindow F.Gm θ δ C) : F.WindowHyp θ δ := by
  intro η hη Y₀
  obtain ⟨Y₁, hY₁⟩ := rpow_dominates_log (|C| * δ) η (by positivity) hη
  obtain ⟨Y, hY, hb⟩ := h (max Y₀ Y₁)
  obtain ⟨h1, hK⟩ := hY₁ Y (le_trans (le_max_right _ _) hY)
  have hY0 : 0 < Y := zero_lt_one.trans_le h1
  have hle : Y ≤ Y ^ (1 + δ) := by
    calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
      _ ≤ Y ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have heq : EqOn (fun y : ℝ => |C| * y ^ θ * y ^ (-θ - 1)) (fun y : ℝ => |C| * y⁻¹)
      (Icc Y (Y ^ (1 + δ))) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
    simp only
    rw [mul_assoc, ← Real.rpow_add hy0, show θ + (-θ - 1) = -1 by ring, Real.rpow_neg_one]
  refine ⟨Y, le_trans (le_max_left _ _) hY, fun y => |C| * y ^ θ, ?_, ?_, ?_⟩
  · refine (integrableOn_congr_fun heq measurableSet_Icc).2 ?_
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.mul (continuousOn_id.inv₀ fun y hy => (lt_of_lt_of_le hY0 hy.1).ne')
  · intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
    have hp : 0 ≤ y ^ θ := by positivity
    exact ⟨by positivity, (hb y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)⟩
  · rw [setIntegral_congr_fun measurableSet_Icc heq, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hY0 (lt_of_lt_of_le hY0 hle),
      Real.log_div (lt_of_lt_of_le hY0 hle).ne' hY0.ne', Real.log_rpow hY0]
    calc |C| * ((1 + δ) * Real.log Y - Real.log Y) = |C| * δ * Real.log Y := by ring
      _ ≤ Y ^ η := hK

end RHDirect.MellinExplicit

end
