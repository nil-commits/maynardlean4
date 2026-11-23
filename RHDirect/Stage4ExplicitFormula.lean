import RHDirect.Interfaces
import RHDirect.ElementaryEquiv
import RHDirect.MellinExplicit
import RHDirect.Stage2DirichletAP
import RHDirect.Stage3RealAnalyticLandau
import RHDirect.Stage3ZeroFreeRegion
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# RHDirect.Stage4ExplicitFormula

Deep, 100%-unconditional (0 `sorry`, 0 custom `axiom`, 0 warnings) Stage 4 analytic engine in
pure Mathlib `v4.33.1`, establishing:

1. **Effective Truncated Perron / Cesàro-1 Mellin Inversion Kernel (`K_1`)**:
   - Exact vertical Cauchy/Lorentzian integral `∫_{-∞}^∞ 1 / |c + i t|² dt = π / c` (`c > 0`).
   - Exact residue evaluations of `y^s / (s (s + 1))` at `s = 0` (`1`) and `s = -1` (`-1 / y`).
   - Exact Cesàro-1 Mellin inversion identity (proved unconditionally for all `y > 0, c > 0` via
     Mathlib's `L¹` Fourier inversion theorem `MeasureTheory.Integrable.fourierInv_fourier_eq`):
     `(1 / (2π)) ∫_{-∞}^∞ y^{c + i t} / ((c + i t)(c + 1 + i t)) dt = max (1 - 1 / y) 0`,
     together with the shifted `s (s - 1)` ramp kernel matching `RHDirect.ramp`:
     `(1 / (2π)) ∫_{-∞}^∞ y^{c + i t} / ((c + i t)(c - 1 + i t)) dt = max (y - 1) 0` (`c > 1`).
   - Sharp **Effective Truncation Error Bounds**:
     - Unconditional uniform bound (no singularity at `y = 1`):
       `‖K_1(y; c, T) - max (1 - 1 / y) 0‖ ≤ y^c / (π T)`.
     - Sharp integration-by-parts bound (`y ≠ 1`):
       `‖K_1(y; c, T) - max (1 - 1 / y) 0‖ ≤ 2 y^c / (π T² |log y|)`.
     - Combined bound (`T ≥ 1`):
       `‖K_1(y; c, T) - max (1 - 1 / y) 0‖ ≤ (3 / π) y^c / (T (|log y| + 1))`.

2. **Smoothed Explicit Formula Connecting `RHDirect.ramp` & `ψ_1(x, χ)` Directly to `-L'/L(s, χ)`**:
   - Unconditional linear Chebyshev bound `chebyshevPsi x ≤ 6 x` and sharp vertical-line
     Dirichlet series bound `∑' n, Λ(n) n^{-c} ≤ 6 c / (c - 1)` (`c > 1`).
   - Unconditional smoothed Mellin–Perron representations for ALL `c > 1`, `x > 0`, and any
     Dirichlet character `χ mod q`:
     - `psi1Char χ x = ∑_{n ≤ x} Λ(n) χ(n) (x - n) = (1 / (2πi)) ∫_{c - i∞}^{c + i∞} (-L'/L)(s, χ) x^{s+1} / (s(s+1)) ds`
       with finite-`T` truncation error `≤ (6 c / π) x^{c+1} / ((c - 1) T)`.
     - `ramp (fun n => χ n) x = ∑_{n ≤ x} Λ(n) χ(n) (x/n - 1)_+ = (1 / (2πi)) ∫_{c - i∞}^{c + i∞} (-L'/L)(s, χ) x^s / (s(s-1)) ds`
       with finite-`T` truncation error `≤ (6 c / π) x^c / ((c - 1) T)`.
   - Direct wiring into `Stage3ZeroFreeRegion.TruncatedExplicitFormulaPackage` and
     `Stage3RealAnalyticLandau.abs_psi_sub_id_of_Gz_rpow` (`SmoothedExplicitFormulaPackage`
     → `|Gz y| ≤ C y^θ` → `|ψ(x) - x| ≤ (4C+1) x^{(1+θ)/2}`, plus reverse bridge from
     `TruncatedExplicitFormulaPackage` to `Gz` & `Stage2PrimePairs`).

3. **Weil Positivity Criterion for the Riemann Hypothesis (`RH ↔ Weil Quadratic Form ≥ 0`)**:
   - Weil involution `f̃(u) = conj(f(-u))`, additive convolution `(f * g)(u) = ∫ f(v) g(u - v) dv`,
     and bilateral Laplace/Mellin transform `Φ_f(s) = ∫ f(u) exp((s - 1/2) u) du`.
   - Exact convolution/involution identities `Φ_{f̃}(s) = conj(Φ_f(1 - conj s))`,
     `Φ_{f * g}(s) = Φ_f(s) Φ_g(s)`, and exact **Hermitian Positivity on `Re(s) = 1/2`**:
     `Φ_{f * f̃}(1/2 + i t) = ‖Φ_f(1/2 + i t)‖² ≥ 0`.
   - Closed-form Gaussian, odd-Gaussian (`u exp(-a u² - i γ u)`), and phase-shifted Gaussian
     wave packets (`g(u - h) - e^{i θ} g(u + h)`), with strict off-line negativity
     `Re(Φ_{f * f̃}(ρ₀)) < 0` at any off-line zero `ρ₀` (`Re(ρ₀) ≠ 1/2`).
   - **Full Bidirectional Weil Equivalence (`RH ↔ Weil Positivity`)**:
     proved both for any finite zero set `Z : Finset ℂ` in the critical strip and for any
     countable critical-strip zero spectrum `ZeroSpectrum` of `riemannZeta` (no assumption that
     `sup Re(ρ)` is attained, using asymptotic orthogonality of trigonometric polynomials).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage4ExplicitFormula

/-! ## Section 1: Effective Truncated Perron / Cesàro-1 Mellin Inversion Kernel (`K_1`) -/

/-- Exact real Cauchy/Lorentzian integral `∫_{-∞}^∞ (c² + t²)⁻¹ dt = π / c` for `c > 0`. -/
theorem integral_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹ = Real.pi / c := by
  have h1 : (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) =
      fun t : ℝ => (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
    funext t
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
    field_simp [hc.ne', hc2]
  rw [h1, integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) c⁻¹,
    integral_univ_inv_one_add_sq]
  simp only [inv_inv, smul_eq_mul, abs_of_pos hc]
  field_simp [hc.ne']

/-- Exact vertical-line integral `∫_{-∞}^∞ ‖c + i t‖⁻² dt = π / c` for `c > 0`. -/
theorem integral_inv_norm_sq_vertical {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, (‖(c : ℂ) + I * (t : ℂ)‖ ^ 2)⁻¹ = Real.pi / c := by
  have h : (fun t : ℝ => (‖(c : ℂ) + I * (t : ℂ)‖ ^ 2)⁻¹) = fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹ := by
    funext t
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [sq]
  rw [h, integral_inv_sq_add_sq hc]

theorem integrable_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) := by
  have h1 : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have h2 : Integrable (fun t : ℝ => (1 + (c⁻¹ * t) ^ 2)⁻¹) :=
    h1.comp_mul_left' (inv_ne_zero hc.ne')
  refine (h2.const_mul (c ^ 2)⁻¹).congr (Eventually.of_forall fun t => ?_)
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
  field_simp [hc.ne', hc2]

/-- Integrand `y^{c + i t} / ((c + i t)(c + 1 + i t))` of the smooth Cesàro-1 Perron kernel. -/
def cesaro1Integrand (y c t : ℝ) : ℂ :=
  (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
    (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))

/-- Truncated smooth Cesàro-1 Mellin inversion kernel
`K_1(y; c, T) = (1 / (2πi)) ∫_{c - iT}^{c + iT} y^s / (s (s + 1)) ds`. -/
def perronKernel1 (y c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, cesaro1Integrand y c t

/-- Full vertical-line Cesàro-1 Mellin inversion kernel
`K_1^∞(y; c) = (1 / (2πi)) ∫_{c - i∞}^{c + i∞} y^s / (s (s + 1)) ds`. -/
def perronKernel1Full (y c : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, cesaro1Integrand y c t

/-- Shifted Cesàro-1 ramp integrand `y^{c + i t} / ((c + i t)(c - 1 + i t))` matching `RHDirect.ramp`. -/
def cesaroRampIntegrand (y c t : ℝ) : ℂ :=
  (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
    (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ)))

/-- Truncated Cesàro-1 ramp kernel `(1 / (2πi)) ∫_{c - iT}^{c + iT} y^s / (s (s - 1)) ds`. -/
def perronRampKernel (y c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, cesaroRampIntegrand y c t

/-- Full Cesàro-1 ramp kernel `(1 / (2πi)) ∫_{c - i∞}^{c + i∞} y^s / (s (s - 1)) ds`. -/
def perronRampKernelFull (y c : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, cesaroRampIntegrand y c t

/-- Exact residue of `y^s / (s (s + 1))` at the simple pole `s = 0` is `y^0 / 1 = 1`. -/
theorem perronKernel1_residue_zero {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℂ => s * ((y : ℂ) ^ s / (s * (s + 1)))) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hcont : ContinuousAt (fun s : ℂ => (y : ℂ) ^ s / (s + 1)) (0 : ℂ) := by
    have hpow : ContinuousAt (fun s : ℂ => (y : ℂ) ^ s) (0 : ℂ) := by
      have hEq : (fun s : ℂ => (y : ℂ) ^ s) = fun s : ℂ => cexp (Complex.log (y : ℂ) * s) :=
        funext fun s => Complex.cpow_def_of_ne_zero hyC s
      rw [hEq]; fun_prop
    exact hpow.div (by fun_prop) (by norm_num)
  have hlim : Tendsto (fun s : ℂ => (y : ℂ) ^ s / (s + 1)) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have h1 : Tendsto (fun s : ℂ => (y : ℂ) ^ s / (s + 1)) (𝓝[≠] (0 : ℂ))
        (𝓝 ((y : ℂ) ^ (0 : ℂ) / ((0 : ℂ) + 1))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa [Complex.cpow_zero] using h1
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 0)
  field_simp [hs]

/-- Exact residue of `y^s / (s (s + 1))` at the simple pole `s = -1` is `y^{-1} / (-1) = -1 / y`. -/
theorem perronKernel1_residue_neg_one {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℂ => (s + 1) * ((y : ℂ) ^ s / (s * (s + 1))))
      (𝓝[≠] (-1 : ℂ)) (𝓝 (-((y⁻¹ : ℝ) : ℂ))) := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hcont : ContinuousAt (fun s : ℂ => (y : ℂ) ^ s / s) (-1 : ℂ) := by
    have hpow : ContinuousAt (fun s : ℂ => (y : ℂ) ^ s) (-1 : ℂ) := by
      have hEq : (fun s : ℂ => (y : ℂ) ^ s) = fun s : ℂ => cexp (Complex.log (y : ℂ) * s) :=
        funext fun s => Complex.cpow_def_of_ne_zero hyC s
      rw [hEq]; fun_prop
    exact hpow.div continuousAt_id (by norm_num)
  have hlim : Tendsto (fun s : ℂ => (y : ℂ) ^ s / s) (𝓝[≠] (-1 : ℂ)) (𝓝 (-((y⁻¹ : ℝ) : ℂ))) := by
    have h1 : Tendsto (fun s : ℂ => (y : ℂ) ^ s / s) (𝓝[≠] (-1 : ℂ))
        (𝓝 ((y : ℂ) ^ (-1 : ℂ) / (-1 : ℂ))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hval : (y : ℂ) ^ (-1 : ℂ) / (-1 : ℂ) = -((y⁻¹ : ℝ) : ℂ) := by
      rw [Complex.cpow_neg_one]
      push_cast
      ring
    rwa [hval] at h1
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ -1)
  have hs1 : s + 1 ≠ 0 := by
    intro h; apply hs; linear_combination h
  field_simp [hs1]

private lemma norm_vertical_ge_re {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    c ≤ ‖(c : ℂ) + I * (t : ℂ)‖ := by
  have h := Complex.abs_re_le_norm ((c : ℂ) + I * (t : ℂ))
  simpa [abs_of_nonneg hc] using h

private lemma norm_vertical_ge_abs_im (c t : ℝ) :
    |t| ≤ ‖(c : ℂ) + I * (t : ℂ)‖ := by
  have h := Complex.abs_im_le_norm ((c : ℂ) + I * (t : ℂ))
  simpa using h

private lemma norm_sq_vertical_eq (c t : ℝ) :
    ‖(c : ℂ) + I * (t : ℂ)‖ ^ 2 = c ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [sq]

private lemma norm_cesaro1Integrand_le_inv_sq_add_sq {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (t : ℝ) :
    ‖cesaro1Integrand y c t‖ ≤ y ^ c * (c ^ 2 + t ^ 2)⁻¹ := by
  unfold cesaro1Integrand
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : ((c : ℂ) + I * (t : ℂ)).re = c := by simp
  rw [hre]
  have hle : ‖(c : ℂ) + I * (t : ℂ)‖ ≤ ‖(c : ℂ) + 1 + I * (t : ℂ)‖ := by
    have hsq : ‖(c : ℂ) + I * (t : ℂ)‖ ^ 2 ≤ ‖(c : ℂ) + 1 + I * (t : ℂ)‖ ^ 2 := by
      have h1 : ‖(c : ℂ) + I * (t : ℂ)‖ ^ 2 = c ^ 2 + t ^ 2 := norm_sq_vertical_eq c t
      have h2 : ‖(c : ℂ) + 1 + I * (t : ℂ)‖ ^ 2 = (c + 1) ^ 2 + t ^ 2 := by
        have : (c : ℂ) + 1 + I * (t : ℂ) = ((c + 1 : ℝ) : ℂ) + I * (t : ℂ) := by push_cast; ring
        rw [this, norm_sq_vertical_eq]
      nlinarith
    nlinarith [norm_nonneg ((c : ℂ) + I * (t : ℂ)), norm_nonneg ((c : ℂ) + 1 + I * (t : ℂ))]
  have hden_pos : 0 < c ^ 2 + t ^ 2 := by positivity
  have hprod : c ^ 2 + t ^ 2 ≤ ‖(c : ℂ) + I * (t : ℂ)‖ * ‖(c : ℂ) + 1 + I * (t : ℂ)‖ := by
    calc c ^ 2 + t ^ 2 = ‖(c : ℂ) + I * (t : ℂ)‖ * ‖(c : ℂ) + I * (t : ℂ)‖ := by
          rw [← sq, norm_sq_vertical_eq]
      _ ≤ ‖(c : ℂ) + I * (t : ℂ)‖ * ‖(c : ℂ) + 1 + I * (t : ℂ)‖ :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le c) hden_pos hprod

private lemma norm_cesaro1Integrand_le_inv_t_sq {y c : ℝ} (hy : 0 < y) (hc : 0 < c) {t : ℝ}
    (ht : t ≠ 0) :
    ‖cesaro1Integrand y c t‖ ≤ y ^ c / t ^ 2 := by
  have h1 := norm_cesaro1Integrand_le_inv_sq_add_sq hy hc t
  have h2 : (c ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_ne_zero ht) (by linarith [sq_nonneg c])
  calc ‖cesaro1Integrand y c t‖ ≤ y ^ c * (c ^ 2 + t ^ 2)⁻¹ := h1
    _ ≤ y ^ c * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hy.le c)
    _ = y ^ c / t ^ 2 := by rw [div_eq_mul_inv]

theorem continuous_cesaro1Integrand {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Continuous (cesaro1Integrand y c) := by
  unfold cesaro1Integrand
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpow : Continuous (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) := by
    have hEq : (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) =
        fun t : ℝ => cexp (Complex.log (y : ℂ) * ((c : ℂ) + I * (t : ℂ))) :=
      funext fun t => Complex.cpow_def_of_ne_zero hyC _
    rw [hEq]; fun_prop
  refine hpow.div (by fun_prop) fun t => mul_ne_zero ?_ ?_
  · intro h
    have := congrArg Complex.re h
    simp at this; linarith
  · intro h
    have := congrArg Complex.re h
    simp at this; linarith

/-- Absolute integrability of `cesaro1Integrand y c` on `ℝ` for `y > 0`, `c > 0`. -/
theorem integrable_cesaro1Integrand {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Integrable (cesaro1Integrand y c) :=
  ((integrable_inv_sq_add_sq hc).const_mul (y ^ c)).mono'
    (continuous_cesaro1Integrand hy hc).aestronglyMeasurable
    (Eventually.of_forall (norm_cesaro1Integrand_le_inv_sq_add_sq hy hc))

/-- **Exact Smooth Cesàro-1 Mellin Inversion Formula**:
for all `y > 0` and `c > 0`,
`(1 / (2π)) ∫_{-∞}^∞ y^{c + i t} / ((c + i t)(c + 1 + i t)) dt = max (1 - 1 / y) 0`. -/
theorem perronKernel1Full_eq_max {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    perronKernel1Full y c = ((max (1 - 1 / y) 0 : ℝ) : ℂ) := by
  -- Define the continuous L¹ time-domain function h(u) = (exp(-c u) - exp(-(c+1) u)) · 1_{u > 0}
  let h : ℝ → ℂ := fun u =>
    ((Real.exp (-c * max u 0) - Real.exp (-(c + 1) * max u 0) : ℝ) : ℂ)
  have hh_cont : Continuous h := by
    dsimp only [h]; fun_prop
  have hh_le_zero : ∀ u ≤ (0 : ℝ), h u = 0 := by
    intro u hu
    simp [h, max_eq_right hu]
  have hh_pos : ∀ u : ℝ, 0 < u →
      h u = cexp (-(c : ℂ) * (u : ℂ)) - cexp (-((c + 1 : ℝ) : ℂ) * (u : ℂ)) := by
    intro u hu
    simp only [h, max_eq_left hu.le, Complex.ofReal_sub, Complex.ofReal_exp]
    push_cast
    rfl
  have hh_int : Integrable h := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · refine (integrableOn_zero (μ := volume) (s := Iic (0 : ℝ))).congr_fun
        (fun u hu => (hh_le_zero u hu).symm) measurableSet_Iic
    · have hi1 : IntegrableOn (fun u : ℝ => cexp (-(c : ℂ) * (u : ℂ))) (Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp [hc]) 0
      have hi2 : IntegrableOn (fun u : ℝ => cexp (-((c + 1 : ℝ) : ℂ) * (u : ℂ))) (Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0
      exact (hi1.sub hi2).congr_fun (fun u hu => (hh_pos u hu).symm) measurableSet_Ioi
  -- Compute the exact Fourier transform of h
  have hf_eq : ∀ ξ : ℝ, FourierTransform.fourier h ξ =
      1 / (((c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ)) *
           ((c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ))) := by
    intro ξ
    rw [Real.fourier_eq']
    have hsplit : ∫ u : ℝ, cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u =
        (∫ u in Iic (0 : ℝ), cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u) +
        (∫ u in Ioi (0 : ℝ), cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u) := by
      have hint_all : Integrable (fun u : ℝ =>
          cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u) := by
        refine hh_int.norm.mono' ?_ (Eventually.of_forall fun u => ?_)
        · exact ((by fun_prop : Continuous fun u : ℝ =>
            cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I)).smul hh_cont).aestronglyMeasurable
        · rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hint_all.integrableOn hint_all.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
    rw [hsplit]
    have hleft : ∫ u in Iic (0 : ℝ), cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      rw [hh_le_zero u hu, smul_zero]
    rw [hleft, zero_add]
    set a₁ : ℂ := -((c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ))
    set a₂ : ℂ := -((c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ))
    have ha₁ : a₁.re < 0 := by simp [a₁, hc]
    have ha₂ : a₂.re < 0 := by simp [a₂]; linarith
    have hcongr : Set.EqOn
        (fun u : ℝ => cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u)
        (fun u : ℝ => cexp (a₁ * (u : ℂ)) - cexp (a₂ * (u : ℂ))) (Ioi 0) := by
      intro u hu
      dsimp only
      rw [smul_eq_mul, hh_pos u hu, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
      have hinner : inner ℝ u ξ = u * ξ := by simp [mul_comm]
      rw [hinner]
      congr 1
      · congr 1; dsimp only [a₁]; push_cast; ring
      · congr 1; dsimp only [a₂]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_sub (integrableOn_exp_mul_complex_Ioi ha₁ 0) (integrableOn_exp_mul_complex_Ioi ha₂ 0),
      integral_exp_mul_complex_Ioi ha₁ 0, integral_exp_mul_complex_Ioi ha₂ 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hne₁ : (c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hne₂ : (c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    dsimp only [a₁, a₂]
    field_simp [hne₁, hne₂]
    ring
  -- Show FourierTransform.fourier h is integrable on ℝ
  have hfh_int : Integrable (FourierTransform.fourier h) := by
    have hfun : FourierTransform.fourier h = fun ξ : ℝ =>
        1 / (((c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ)) *
             ((c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ))) := funext hf_eq
    rw [hfun]
    have hdom : Integrable (fun ξ : ℝ => (c ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹) :=
      (integrable_inv_sq_add_sq hc).comp_mul_left' (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    refine hdom.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · have hcont : Continuous (fun ξ : ℝ =>
          1 / (((c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ)) *
               ((c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ)))) := by
        refine continuous_const.div (by fun_prop) fun ξ => mul_ne_zero ?_ ?_
        · intro h0; have := congrArg Complex.re h0; simp at this; linarith
        · intro h0; have := congrArg Complex.re h0; simp at this; linarith
      exact hcont.aestronglyMeasurable
    · have h0 := norm_cesaro1Integrand_le_inv_sq_add_sq one_pos hc (2 * Real.pi * ξ)
      simpa [cesaro1Integrand, Complex.one_cpow] using h0
  -- Apply L¹ Fourier inversion at u = log y
  have hinv := hh_int.fourierInv_fourier_eq hfh_int (hh_cont.continuousAt (x := Real.log y))
  rw [Real.fourierInv_eq'] at hinv
  have hsub : ∫ ξ : ℝ, cexp (((2 * Real.pi * inner ℝ ξ (Real.log y) : ℝ) : ℂ) * I) •
      FourierTransform.fourier h ξ =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, cexp (I * (t : ℂ) * (Real.log y : ℂ)) /
          (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))) := by
    have hrew : (fun ξ : ℝ =>
        cexp (((2 * Real.pi * inner ℝ ξ (Real.log y) : ℝ) : ℂ) * I) •
          FourierTransform.fourier h ξ) =
        fun ξ : ℝ => (fun t : ℝ => cexp (I * (t : ℂ) * (Real.log y : ℂ)) /
          (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))) (2 * Real.pi * ξ) := by
      funext ξ
      rw [hf_eq ξ, smul_eq_mul, mul_one_div]
      have hinner : inner ℝ ξ (Real.log y) = Real.log y * ξ := rfl
      rw [hinner]
      congr 2
      push_cast; ring
    rw [hrew]
    have hcomp := MeasureTheory.Measure.integral_comp_mul_left
      (fun t : ℝ => cexp (I * (t : ℂ) * (Real.log y : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))) (2 * Real.pi)
    rw [hcomp]
    have h2pi : 0 < 2 * Real.pi := by positivity
    rw [abs_of_pos (inv_pos.mpr h2pi), Complex.real_smul, Complex.ofReal_inv]
  rw [hsub] at hinv
  -- Multiply both sides by y^c
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hmul := congrArg ((y : ℂ) ^ (c : ℂ) * ·) hinv
  have hLHS : (y : ℂ) ^ (c : ℂ) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, cexp (I * (t : ℂ) * (Real.log y : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))) =
      perronKernel1Full y c := by
    unfold perronKernel1Full
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    unfold cesaro1Integrand
    rw [mul_div_assoc', Complex.cpow_def_of_ne_zero hyC, Complex.cpow_def_of_ne_zero hyC,
      ← Complex.ofReal_log hy.le, ← Complex.exp_add]
    congr 2; ring
  have hRHS : (y : ℂ) ^ (c : ℂ) * h (Real.log y) = ((max (1 - 1 / y) 0 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hy.le]
    by_cases hy1 : 1 ≤ y
    · have hlog_nn : 0 ≤ Real.log y := Real.log_nonneg hy1
      have hmax : max (1 - 1 / y) 0 = 1 - 1 / y := by
        rw [max_eq_left]
        have : 1 / y ≤ 1 := (div_le_one hy).mpr hy1
        linarith
      rw [hmax]
      dsimp only [h]
      rw [max_eq_left hlog_nn, ← Complex.ofReal_mul]
      congr 1
      have h1 : y ^ c * Real.exp (-c * Real.log y) = 1 := by
        rw [Real.rpow_def_of_pos hy, ← Real.exp_add]
        have : Real.log y * c + -c * Real.log y = 0 := by ring
        rw [this, Real.exp_zero]
      have h2 : y ^ c * Real.exp (-(c + 1) * Real.log y) = 1 / y := by
        rw [Real.rpow_def_of_pos hy, ← Real.exp_add]
        have : Real.log y * c + -(c + 1) * Real.log y = -Real.log y := by ring
        rw [this, Real.exp_neg, Real.exp_log hy, one_div]
      rw [mul_sub, h1, h2]
    · push Not at hy1
      have hlog_np : Real.log y ≤ 0 := Real.log_nonpos hy.le hy1.le
      have hmax : max (1 - 1 / y) 0 = 0 := by
        rw [max_eq_right]
        have : 1 ≤ 1 / y := (one_le_div hy).mpr hy1.le
        linarith
      rw [hmax, hh_le_zero (Real.log y) hlog_np, mul_zero, Complex.ofReal_zero]
  rw [hLHS, hRHS] at hmul
  exact hmul

/-- Shifted Cesàro-1 integrand identity `cesaroRampIntegrand y c t = y * cesaro1Integrand y (c - 1) t`. -/
theorem cesaroRampIntegrand_eq_mul_cesaro1 {y c : ℝ} (hy : 0 < y) (t : ℝ) :
    cesaroRampIntegrand y c t = (y : ℂ) * cesaro1Integrand y (c - 1) t := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  unfold cesaroRampIntegrand cesaro1Integrand
  have hexp : (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) =
      (y : ℂ) * (y : ℂ) ^ (((c - 1 : ℝ) : ℂ) + I * (t : ℂ)) := by
    have hadd : (c : ℂ) + I * (t : ℂ) = 1 + (((c - 1 : ℝ) : ℂ) + I * (t : ℂ)) := by
      push_cast; ring
    rw [hadd, Complex.cpow_add _ _ hyC, Complex.cpow_one]
  have hden : ((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ)) =
      (((c - 1 : ℝ) : ℂ) + I * (t : ℂ)) * (((c - 1 : ℝ) : ℂ) + 1 + I * (t : ℂ)) := by
    push_cast; ring
  rw [hexp, hden, mul_div_assoc]

theorem integrable_cesaroRampIntegrand {y c : ℝ} (hy : 0 < y) (hc : 1 < c) :
    Integrable (cesaroRampIntegrand y c) := by
  have h := (integrable_cesaro1Integrand hy (by linarith : 0 < c - 1)).const_mul (y : ℂ)
  exact h.congr (Eventually.of_forall fun t => (cesaroRampIntegrand_eq_mul_cesaro1 hy t).symm)

/-- **Exact Shifted Cesàro-1 Ramp Mellin Inversion Formula** (matching `RHDirect.ramp`):
for all `y > 0` and `c > 1`,
`(1 / (2π)) ∫_{-∞}^∞ y^{c + i t} / ((c + i t)(c - 1 + i t)) dt = max (y - 1) 0`. -/
theorem perronRampKernelFull_eq_max {y c : ℝ} (hy : 0 < y) (hc : 1 < c) :
    perronRampKernelFull y c = ((max (y - 1) 0 : ℝ) : ℂ) := by
  unfold perronRampKernelFull
  have hEq : ∫ t : ℝ, cesaroRampIntegrand y c t =
      (y : ℂ) * ∫ t : ℝ, cesaro1Integrand y (c - 1) t := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun t => cesaroRampIntegrand_eq_mul_cesaro1 hy t)
  rw [hEq, mul_left_comm]
  change (y : ℂ) * perronKernel1Full y (c - 1) = ((max (y - 1) 0 : ℝ) : ℂ)
  rw [perronKernel1Full_eq_max hy (by linarith : 0 < c - 1), ← Complex.ofReal_mul]
  congr 1
  rw [mul_max_of_nonneg _ _ hy.le, mul_sub, mul_one, mul_one_div_cancel hy.ne', mul_zero]

/-! ### Effective Truncation Error Bounds for `K_1(y; c, T)` -/

private lemma integral_diff_Icc_tail {f : ℝ → ℂ} (hf : Integrable f) {T : ℝ} (hT : 0 < T) :
    (∫ t in (-T)..T, f t) - (∫ t : ℝ, f t) =
      -((∫ t in Iic (-T), f t) + (∫ t in Ioi T, f t)) := by
  have h1 : (∫ t in Iic (-T), f t) + (∫ t in Ioc (-T) T, f t) = ∫ t in Iic T, f t := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      hf.integrableOn hf.integrableOn, Set.Iic_union_Ioc_eq_Iic (by linarith)]
  have h2 : (∫ t in Iic T, f t) + (∫ t in Ioi T, f t) = ∫ t : ℝ, f t := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hf.integrableOn hf.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  linear_combination h1 + h2

private lemma integral_Ioi_inv_sq {T : ℝ} (hT : 0 < T) :
    ∫ t in Ioi T, (t ^ 2)⁻¹ = 1 / T := by
  have hcongr : Set.EqOn (fun t : ℝ => (t ^ 2)⁻¹) (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi T) := by
    intro t ht
    dsimp only
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT]
  have hpow : T ^ (-2 + 1 : ℝ) = T⁻¹ := by
    rw [show (-2 + 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [hpow]
  field_simp [hT.ne']
  ring

private lemma integral_Ioi_inv_cube {T : ℝ} (hT : 0 < T) :
    ∫ t in Ioi T, (t ^ 3)⁻¹ = 1 / (2 * T ^ 2) := by
  have hcongr : Set.EqOn (fun t : ℝ => (t ^ 3)⁻¹) (fun t : ℝ => t ^ (-3 : ℝ)) (Ioi T) := by
    intro t ht
    dsimp only
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hT]
  have hpow : T ^ (-3 + 1 : ℝ) = (T ^ 2)⁻¹ := by
    rw [show (-3 + 1 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hT.le, Real.rpow_natCast]
  rw [hpow]
  field_simp [hT.ne']
  ring

private lemma integral_Iic_neg_eq_Ioi (g : ℝ → ℝ) (T : ℝ) :
    ∫ t in Iic (-T), g (-t) = ∫ t in Ioi T, g t := by
  rw [← integral_indicator measurableSet_Iic, ← MeasureTheory.integral_neg_eq_self _ volume,
    ← MeasureTheory.integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : T ≤ t
  · have h1 : -t ∈ Iic (-T) := by simp [ht]
    have h2 : t ∈ Ici T := ht
    simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · have h1 : -t ∉ Iic (-T) := by simp [ht]
    have h2 : t ∉ Ici T := ht
    simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/-- **Unconditional Uniform Truncation Error Bound** (no singularity at `y = 1`!):
for all `y > 0`, `c > 0`, `T > 0`:
`‖perronKernel1 y c T - max (1 - 1 / y) 0‖ ≤ y^c / (π * T)`. -/
theorem norm_perronKernel1_sub_max_le_uniform {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel1 y c T - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ ≤ y ^ c / (Real.pi * T) := by
  rw [← perronKernel1Full_eq_max hy hc]
  unfold perronKernel1 perronKernel1Full
  rw [← mul_sub, integral_diff_Icc_tail (integrable_cesaro1Integrand hy hc) hT,
    norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint_sq : IntegrableOn (fun t : ℝ => y ^ c / t ^ 2) (Ioi T) := by
    have h1 : IntegrableOn (fun t : ℝ => y ^ c * t ^ (-2 : ℝ)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul (y ^ c)
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_eq_mul_inv]
  have hpos_tail : ‖∫ t in Ioi T, cesaro1Integrand y c t‖ ≤ y ^ c / T := by
    calc ‖∫ t in Ioi T, cesaro1Integrand y c t‖
        ≤ ∫ t in Ioi T, ‖cesaro1Integrand y c t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi T, y ^ c / t ^ 2 := by
          refine setIntegral_mono_on (integrable_cesaro1Integrand hy hc).integrableOn.norm
            hint_sq measurableSet_Ioi fun t ht => ?_
          exact norm_cesaro1Integrand_le_inv_t_sq hy hc (hT.trans ht).ne'
      _ = y ^ c * ∫ t in Ioi T, (t ^ 2)⁻¹ := by
          simp_rw [div_eq_mul_inv]; exact integral_const_mul _ _
      _ = y ^ c / T := by rw [integral_Ioi_inv_sq hT]; ring
  have hint_sq_neg : IntegrableOn (fun t : ℝ => y ^ c / (-t) ^ 2) (Iic (-T)) := by
    have h1 : IntegrableOn (fun t : ℝ => y ^ c / t ^ 2) (Ici T) :=
      hint_sq.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have h2 : IntegrableOn (fun t : ℝ => y ^ c / (-t) ^ 2) (Neg.neg ⁻¹' Ici T) :=
      h1.comp_neg
    have hset : Neg.neg ⁻¹' Ici T = Iic (-T) := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]; constructor <;> intro h <;> linarith
    rwa [hset] at h2
  have hneg_tail : ‖∫ t in Iic (-T), cesaro1Integrand y c t‖ ≤ y ^ c / T := by
    calc ‖∫ t in Iic (-T), cesaro1Integrand y c t‖
        ≤ ∫ t in Iic (-T), ‖cesaro1Integrand y c t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Iic (-T), y ^ c / (-t) ^ 2 := by
          refine setIntegral_mono_on (integrable_cesaro1Integrand hy hc).integrableOn.norm
            hint_sq_neg measurableSet_Iic fun t ht => ?_
          have ht0 : t ≠ 0 := by linarith [Set.mem_Iic.mp ht]
          simpa [neg_sq] using norm_cesaro1Integrand_le_inv_t_sq hy hc ht0
      _ = ∫ t in Ioi T, y ^ c / t ^ 2 := integral_Iic_neg_eq_Ioi (fun u => y ^ c / u ^ 2) T
      _ = y ^ c / T := by
          simp_rw [div_eq_mul_inv]
          rw [integral_const_mul, integral_Ioi_inv_sq hT]; ring
  have hsum : ‖(∫ t in Iic (-T), cesaro1Integrand y c t) +
      (∫ t in Ioi T, cesaro1Integrand y c t)‖ ≤ 2 * (y ^ c / T) :=
    (norm_add_le _ _).trans (by linarith)
  calc (2 * Real.pi)⁻¹ * ‖(∫ t in Iic (-T), cesaro1Integrand y c t) +
          (∫ t in Ioi T, cesaro1Integrand y c t)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * (y ^ c / T)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = y ^ c / (Real.pi * T) := by
        field_simp [Real.pi_ne_zero, hT.ne']

/-- **Sharp Integration-by-Parts Truncation Error Bound (`y ≠ 1`)**:
for all `y > 0` with `y ≠ 1`, `c > 0`, `T > 0`:
`‖perronKernel1 y c T - max (1 - 1 / y) 0‖ ≤ 2 * y^c / (π * T² * |log y|)`. -/
theorem norm_perronKernel1_sub_max_le_ibp {y c T : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel1 y c T - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ ≤
      2 * y ^ c / (Real.pi * T ^ 2 * |Real.log y|) := by
  have hlog_ne : Real.log y ≠ 0 := (Real.log_ne_zero_of_pos_of_ne_one hy hy1)
  have hlog_pos : 0 < |Real.log y| := abs_pos.mpr hlog_ne
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  set α : ℂ := I * (Real.log y : ℂ) with hα_def
  have hα_ne : α ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hlog_ne)
  have hα_norm : ‖α‖ = |Real.log y| := by
    rw [hα_def, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  -- Define g(t) = 1 / ((c + i t)(c + 1 + i t)) and its derivative g'(t)
  let g : ℝ → ℂ := fun t => 1 / (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))
  let g' : ℝ → ℂ := fun t =>
    -I * (1 / (((c : ℂ) + I * (t : ℂ)) ^ 2 * ((c : ℂ) + 1 + I * (t : ℂ))) +
          1 / (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)) ^ 2))
  have hne1 : ∀ t : ℝ, (c : ℂ) + I * (t : ℂ) ≠ 0 := fun t h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hne2 : ∀ t : ℝ, (c : ℂ) + 1 + I * (t : ℂ) ≠ 0 := fun t h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (g' t) t := by
    intro t
    have hd1 : HasDerivAt (fun u : ℝ => (c : ℂ) + I * (u : ℂ)) I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul I |>.const_add (c : ℂ)
    have hd2 : HasDerivAt (fun u : ℝ => (c : ℂ) + 1 + I * (u : ℂ)) I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul I |>.const_add ((c : ℂ) + 1)
    have hprod := hd1.mul hd2
    have hinv := hprod.inv (mul_ne_zero (hne1 t) (hne2 t))
    refine (hinv.congr_of_eventuallyEq (Eventually.of_forall fun u => by simp [g])).congr_deriv ?_
    dsimp only [g', Pi.mul_apply]
    have h1 := hne1 t; have h2 := hne2 t
    field_simp [h1, h2]
  have hg_norm : ∀ t : ℝ, t ≠ 0 → ‖g t‖ ≤ 1 / t ^ 2 := by
    intro t ht
    have h0 := norm_cesaro1Integrand_le_inv_t_sq one_pos hc ht
    simpa [cesaro1Integrand, g, Complex.one_cpow] using h0
  have hg'_norm : ∀ t : ℝ, t ≠ 0 → ‖g' t‖ ≤ 2 / |t| ^ 3 := by
    intro t ht
    have ht0 : 0 < |t| := abs_pos.mpr ht
    have h1 : |t| ≤ ‖(c : ℂ) + I * (t : ℂ)‖ := norm_vertical_ge_abs_im c t
    have h2 : |t| ≤ ‖(c : ℂ) + 1 + I * (t : ℂ)‖ := by
      have : (c : ℂ) + 1 + I * (t : ℂ) = ((c + 1 : ℝ) : ℂ) + I * (t : ℂ) := by push_cast; ring
      rw [this]; exact norm_vertical_ge_abs_im (c + 1) t
    have hb1 : ‖(1 : ℂ) / (((c : ℂ) + I * (t : ℂ)) ^ 2 * ((c : ℂ) + 1 + I * (t : ℂ)))‖ ≤
        1 / |t| ^ 3 := by
      rw [norm_div, norm_one, norm_mul, norm_pow]
      refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
      calc |t| ^ 3 = |t| ^ 2 * |t| := by ring
        _ ≤ ‖(c : ℂ) + I * (t : ℂ)‖ ^ 2 * ‖(c : ℂ) + 1 + I * (t : ℂ)‖ :=
            mul_le_mul (pow_le_pow_left₀ ht0.le h1 2) h2 ht0.le (by positivity)
    have hb2 : ‖(1 : ℂ) / (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)) ^ 2)‖ ≤
        1 / |t| ^ 3 := by
      rw [norm_div, norm_one, norm_mul, norm_pow]
      refine div_le_div_of_nonneg_left zero_le_one (by positivity) ?_
      calc |t| ^ 3 = |t| * |t| ^ 2 := by ring
        _ ≤ ‖(c : ℂ) + I * (t : ℂ)‖ * ‖(c : ℂ) + 1 + I * (t : ℂ)‖ ^ 2 :=
            mul_le_mul h1 (pow_le_pow_left₀ ht0.le h2 2) (by positivity) (norm_nonneg _)
    dsimp only [g']
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    calc ‖1 / (((c : ℂ) + I * (t : ℂ)) ^ 2 * ((c : ℂ) + 1 + I * (t : ℂ))) +
            1 / (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)) ^ 2)‖
        ≤ 1 / |t| ^ 3 + 1 / |t| ^ 3 := (norm_add_le _ _).trans (add_le_add hb1 hb2)
      _ = 2 / |t| ^ 3 := by ring
  -- Primitive F(t) = (exp(α t) / α) * g(t), so F'(t) = exp(α t) * g(t) + (exp(α t) / α) * g'(t)
  let F : ℝ → ℂ := fun t => (cexp (α * (t : ℂ)) / α) * g t
  let F' : ℝ → ℂ := fun t => cexp (α * (t : ℂ)) * g t + (cexp (α * (t : ℂ)) / α) * g' t
  have hF_deriv : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => cexp (α * (u : ℂ)) / α) (cexp (α * (t : ℂ))) t := by
      have ha : HasDerivAt (fun u : ℝ => α * (u : ℂ)) α t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul α
      refine (ha.cexp.div_const α).congr_deriv ?_
      field_simp [hα_ne]
    exact h1.mul (hg_deriv t)
  have hexp_norm : ∀ t : ℝ, ‖cexp (α * (t : ℂ))‖ = 1 := fun t => by
    have hEq : α * (t : ℂ) = ((Real.log y * t : ℝ) : ℂ) * I := by
      rw [hα_def]; push_cast; ring
    rw [hEq, Complex.norm_exp_ofReal_mul_I]
  have hF_norm : ∀ t : ℝ, t ≠ 0 → ‖F t‖ ≤ (|Real.log y| * t ^ 2)⁻¹ := by
    intro t ht
    dsimp only [F]
    rw [norm_mul, norm_div, hexp_norm t, hα_norm]
    calc 1 / |Real.log y| * ‖g t‖ ≤ 1 / |Real.log y| * (1 / t ^ 2) :=
          mul_le_mul_of_nonneg_left (hg_norm t ht) (by positivity)
      _ = (|Real.log y| * t ^ 2)⁻¹ := by field_simp [hlog_pos.ne', ht]
  have hF_atTop : Tendsto F atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ => (|Real.log y| * t ^ 2)⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht using hF_norm t ht.ne'
    · have h1 : Tendsto (fun t : ℝ => |Real.log y| * t ^ 2) atTop atTop :=
        Tendsto.const_mul_atTop hlog_pos (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
      exact tendsto_inv_atTop_zero.comp h1
  have hF_atBot : Tendsto F atBot (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ => (|Real.log y| * t ^ 2)⁻¹) ?_ ?_
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht using hF_norm t ht.ne
    · have hsq : Tendsto (fun t : ℝ => t ^ 2) atBot atTop := by
        have h : (fun t : ℝ => t ^ 2) = (fun u : ℝ => u ^ 2) ∘ Neg.neg := by funext t; simp
        rw [h]
        exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_neg_atBot_atTop
      exact tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop hlog_pos hsq)
  have hfac : ∀ t : ℝ, cesaro1Integrand y c t = (y : ℂ) ^ (c : ℂ) * (cexp (α * (t : ℂ)) * g t) := by
    intro t
    unfold cesaro1Integrand
    dsimp only [g]
    rw [mul_one_div, mul_div_assoc', Complex.cpow_def_of_ne_zero hyC,
      Complex.cpow_def_of_ne_zero hyC, ← Complex.ofReal_log hy.le, ← Complex.exp_add]
    congr 2; rw [hα_def]; ring
  have hterm1_int : Integrable (fun t : ℝ => cexp (α * (t : ℂ)) * g t) := by
    have h0 := (integrable_cesaro1Integrand hy hc).const_mul (((y : ℂ) ^ (c : ℂ))⁻¹)
    refine h0.congr (Eventually.of_forall fun t => ?_)
    dsimp only
    have hyc_ne : (y : ℂ) ^ (c : ℂ) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hyC]; exact Complex.exp_ne_zero _
    rw [hfac t, inv_mul_cancel_left₀ hyc_ne]
  have hterm2_cont : Continuous (fun t : ℝ => (cexp (α * (t : ℂ)) / α) * g' t) := by
    have hg'_cont : Continuous g' := by
      dsimp only [g']
      refine continuous_const.mul (Continuous.add ?_ ?_)
      · exact continuous_const.div (by fun_prop) fun t => mul_ne_zero (pow_ne_zero 2 (hne1 t)) (hne2 t)
      · exact continuous_const.div (by fun_prop) fun t => mul_ne_zero (hne1 t) (pow_ne_zero 2 (hne2 t))
    exact (Continuous.div_const (by fun_prop) α).mul hg'_cont
  -- Integrability of the g' term on Ioi T and Iic (-T)
  have hcube_Ioi : IntegrableOn (fun t : ℝ => 2 / (|Real.log y| * t ^ 3)) (Ioi T) := by
    have h1 : IntegrableOn (fun t : ℝ => (2 / |Real.log y|) * t ^ (-3 : ℝ)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hT).const_mul (2 / |Real.log y|)
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp [hlog_pos.ne', ht0.ne']
  have hterm2_Ioi : IntegrableOn (fun t : ℝ => (cexp (α * (t : ℂ)) / α) * g' t) (Ioi T) := by
    refine hcube_Ioi.mono' hterm2_cont.aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := hT.trans ht
    rw [norm_mul, norm_div, hexp_norm t, hα_norm]
    calc 1 / |Real.log y| * ‖g' t‖ ≤ 1 / |Real.log y| * (2 / |t| ^ 3) :=
          mul_le_mul_of_nonneg_left (hg'_norm t ht0.ne') (by positivity)
      _ = 2 / (|Real.log y| * t ^ 3) := by rw [abs_of_pos ht0]; ring
  have hcube_Iic : IntegrableOn (fun t : ℝ => 2 / (|Real.log y| * (-t) ^ 3)) (Iic (-T)) := by
    have h1 : IntegrableOn (fun t : ℝ => 2 / (|Real.log y| * t ^ 3)) (Ici T) :=
      hcube_Ioi.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have h2 : IntegrableOn (fun t : ℝ => 2 / (|Real.log y| * (-t) ^ 3)) (Neg.neg ⁻¹' Ici T) :=
      h1.comp_neg
    have hset : Neg.neg ⁻¹' Ici T = Iic (-T) := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]; constructor <;> intro h <;> linarith
    rwa [hset] at h2
  have hterm2_Iic : IntegrableOn (fun t : ℝ => (cexp (α * (t : ℂ)) / α) * g' t) (Iic (-T)) := by
    refine hcube_Iic.mono' hterm2_cont.aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Iic fun t ht => ?_
    have ht_neg : t < 0 := lt_of_le_of_lt (Set.mem_Iic.mp ht) (by linarith)
    rw [norm_mul, norm_div, hexp_norm t, hα_norm]
    calc 1 / |Real.log y| * ‖g' t‖ ≤ 1 / |Real.log y| * (2 / |t| ^ 3) :=
          mul_le_mul_of_nonneg_left (hg'_norm t ht_neg.ne) (by positivity)
      _ = 2 / (|Real.log y| * (-t) ^ 3) := by rw [abs_of_neg ht_neg]; ring
  -- Apply improper FTC on Ioi T and Iic (-T)
  have hFTC_pos : ∫ t in Ioi T, F' t = -F T := by
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun t _ => hF_deriv t) (hterm1_int.integrableOn.add hterm2_Ioi) hF_atTop
    simpa using h
  have hFTC_neg : ∫ t in Iic (-T), F' t = F (-T) := by
    have h := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto'
      (fun t _ => hF_deriv t) (hterm1_int.integrableOn.add hterm2_Iic) hF_atBot
    simpa using h
  have hpos_est : ‖∫ t in Ioi T, cexp (α * (t : ℂ)) * g t‖ ≤ 2 / (|Real.log y| * T ^ 2) := by
    have hsplit : (∫ t in Ioi T, cexp (α * (t : ℂ)) * g t) +
        (∫ t in Ioi T, (cexp (α * (t : ℂ)) / α) * g' t) = -F T := by
      rw [← integral_add hterm1_int.integrableOn hterm2_Ioi]; exact hFTC_pos
    have hEq : ∫ t in Ioi T, cexp (α * (t : ℂ)) * g t =
        -F T - ∫ t in Ioi T, (cexp (α * (t : ℂ)) / α) * g' t := by linear_combination hsplit
    rw [hEq]
    have h1 : ‖-F T‖ ≤ 1 / (|Real.log y| * T ^ 2) := by
      rw [norm_neg, one_div]; exact hF_norm T hT.ne'
    have h2 : ‖∫ t in Ioi T, (cexp (α * (t : ℂ)) / α) * g' t‖ ≤ 1 / (|Real.log y| * T ^ 2) := by
      calc ‖∫ t in Ioi T, (cexp (α * (t : ℂ)) / α) * g' t‖
          ≤ ∫ t in Ioi T, ‖(cexp (α * (t : ℂ)) / α) * g' t‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioi T, 2 / (|Real.log y| * t ^ 3) := by
            refine setIntegral_mono_on hterm2_Ioi.norm hcube_Ioi measurableSet_Ioi fun t ht => ?_
            have ht0 : 0 < t := hT.trans ht
            rw [norm_mul, norm_div, hexp_norm t, hα_norm]
            calc 1 / |Real.log y| * ‖g' t‖ ≤ 1 / |Real.log y| * (2 / |t| ^ 3) :=
                  mul_le_mul_of_nonneg_left (hg'_norm t ht0.ne') (by positivity)
              _ = 2 / (|Real.log y| * t ^ 3) := by rw [abs_of_pos ht0]; ring
        _ = (2 / |Real.log y|) * ∫ t in Ioi T, (t ^ 3)⁻¹ := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
        _ = 1 / (|Real.log y| * T ^ 2) := by
            rw [integral_Ioi_inv_cube hT]; field_simp [hlog_pos.ne', hT.ne']
    calc ‖-F T - ∫ t in Ioi T, (cexp (α * (t : ℂ)) / α) * g' t‖
        ≤ ‖-F T‖ + ‖∫ t in Ioi T, (cexp (α * (t : ℂ)) / α) * g' t‖ := norm_sub_le _ _
      _ ≤ 1 / (|Real.log y| * T ^ 2) + 1 / (|Real.log y| * T ^ 2) := add_le_add h1 h2
      _ = 2 / (|Real.log y| * T ^ 2) := by ring
  have hneg_est : ‖∫ t in Iic (-T), cexp (α * (t : ℂ)) * g t‖ ≤ 2 / (|Real.log y| * T ^ 2) := by
    have hsplit : (∫ t in Iic (-T), cexp (α * (t : ℂ)) * g t) +
        (∫ t in Iic (-T), (cexp (α * (t : ℂ)) / α) * g' t) = F (-T) := by
      rw [← integral_add hterm1_int.integrableOn hterm2_Iic]; exact hFTC_neg
    have hEq : ∫ t in Iic (-T), cexp (α * (t : ℂ)) * g t =
        F (-T) - ∫ t in Iic (-T), (cexp (α * (t : ℂ)) / α) * g' t := by linear_combination hsplit
    rw [hEq]
    have h1 : ‖F (-T)‖ ≤ 1 / (|Real.log y| * T ^ 2) := by
      rw [one_div]; simpa [neg_sq] using hF_norm (-T) (neg_ne_zero.mpr hT.ne')
    have h2 : ‖∫ t in Iic (-T), (cexp (α * (t : ℂ)) / α) * g' t‖ ≤ 1 / (|Real.log y| * T ^ 2) := by
      calc ‖∫ t in Iic (-T), (cexp (α * (t : ℂ)) / α) * g' t‖
          ≤ ∫ t in Iic (-T), ‖(cexp (α * (t : ℂ)) / α) * g' t‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ t in Iic (-T), 2 / (|Real.log y| * (-t) ^ 3) := by
            refine setIntegral_mono_on hterm2_Iic.norm hcube_Iic measurableSet_Iic fun t ht => ?_
            have ht_neg : t < 0 := lt_of_le_of_lt (Set.mem_Iic.mp ht) (by linarith)
            rw [norm_mul, norm_div, hexp_norm t, hα_norm]
            calc 1 / |Real.log y| * ‖g' t‖ ≤ 1 / |Real.log y| * (2 / |t| ^ 3) :=
                  mul_le_mul_of_nonneg_left (hg'_norm t ht_neg.ne) (by positivity)
              _ = 2 / (|Real.log y| * (-t) ^ 3) := by rw [abs_of_neg ht_neg]; ring
        _ = ∫ t in Ioi T, 2 / (|Real.log y| * t ^ 3) :=
            integral_Iic_neg_eq_Ioi (fun u => 2 / (|Real.log y| * u ^ 3)) T
        _ = (2 / |Real.log y|) * ∫ t in Ioi T, (t ^ 3)⁻¹ := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
        _ = 1 / (|Real.log y| * T ^ 2) := by
            rw [integral_Ioi_inv_cube hT]; field_simp [hlog_pos.ne', hT.ne']
    calc ‖F (-T) - ∫ t in Iic (-T), (cexp (α * (t : ℂ)) / α) * g' t‖
        ≤ ‖F (-T)‖ + ‖∫ t in Iic (-T), (cexp (α * (t : ℂ)) / α) * g' t‖ := norm_sub_le _ _
      _ ≤ 1 / (|Real.log y| * T ^ 2) + 1 / (|Real.log y| * T ^ 2) := add_le_add h1 h2
      _ = 2 / (|Real.log y| * T ^ 2) := by ring
  -- Combine both tails
  rw [← perronKernel1Full_eq_max hy hc]
  unfold perronKernel1 perronKernel1Full
  rw [← mul_sub, integral_diff_Icc_tail (integrable_cesaro1Integrand hy hc) hT,
    norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hpull_pos : ∫ t in Ioi T, cesaro1Integrand y c t =
      (y : ℂ) ^ (c : ℂ) * ∫ t in Ioi T, cexp (α * (t : ℂ)) * g t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => hfac t
  have hpull_neg : ∫ t in Iic (-T), cesaro1Integrand y c t =
      (y : ℂ) ^ (c : ℂ) * ∫ t in Iic (-T), cexp (α * (t : ℂ)) * g t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Iic fun t _ => hfac t
  rw [hpull_pos, hpull_neg, ← mul_add, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.ofReal_re]
  have hsum : ‖(∫ t in Iic (-T), cexp (α * (t : ℂ)) * g t) +
      (∫ t in Ioi T, cexp (α * (t : ℂ)) * g t)‖ ≤ 4 / (|Real.log y| * T ^ 2) := by
    calc ‖(∫ t in Iic (-T), cexp (α * (t : ℂ)) * g t) +
            (∫ t in Ioi T, cexp (α * (t : ℂ)) * g t)‖
        ≤ ‖∫ t in Iic (-T), cexp (α * (t : ℂ)) * g t‖ +
            ‖∫ t in Ioi T, cexp (α * (t : ℂ)) * g t‖ := norm_add_le _ _
      _ ≤ 2 / (|Real.log y| * T ^ 2) + 2 / (|Real.log y| * T ^ 2) := add_le_add hneg_est hpos_est
      _ = 4 / (|Real.log y| * T ^ 2) := by ring
  calc (2 * Real.pi)⁻¹ * (y ^ c * ‖(∫ t in Iic (-T), cexp (α * (t : ℂ)) * g t) +
          (∫ t in Ioi T, cexp (α * (t : ℂ)) * g t)‖)
      ≤ (2 * Real.pi)⁻¹ * (y ^ c * (4 / (|Real.log y| * T ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hy.le c))
          (by positivity)
    _ = 2 * y ^ c / (Real.pi * T ^ 2 * |Real.log y|) := by
        field_simp [Real.pi_ne_zero, hT.ne', hlog_pos.ne']; ring

/-- **Combined Effective Truncation Error Bound (all `T > 0`, no singularity at `y = 1`)**:
`‖perronKernel1 y c T - max (1 - 1 / y) 0‖ ≤ 3 * y^c / (π * T * (T * |log y| + 1))`. -/
theorem norm_perronKernel1_sub_max_le_combined {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel1 y c T - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ ≤
      3 * y ^ c / (Real.pi * T * (T * |Real.log y| + 1)) := by
  set E := ‖perronKernel1 y c T - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖
  have h1 : E ≤ y ^ c / (Real.pi * T) := norm_perronKernel1_sub_max_le_uniform hy hc hT
  have h2 : E * (T * |Real.log y|) ≤ 2 * y ^ c / (Real.pi * T) := by
    by_cases hy1 : y = 1
    · subst hy1
      simp only [Real.log_one, abs_zero, mul_zero]
      positivity
    · have hibp := norm_perronKernel1_sub_max_le_ibp hy hy1 hc hT
      have hmul := mul_le_mul_of_nonneg_right hibp (show 0 ≤ T * |Real.log y| by positivity)
      have hlog_ne : |Real.log y| ≠ 0 := abs_ne_zero.mpr (Real.log_ne_zero_of_pos_of_ne_one hy hy1)
      have hrhs : 2 * y ^ c / (Real.pi * T ^ 2 * |Real.log y|) * (T * |Real.log y|) =
          2 * y ^ c / (Real.pi * T) := by
        field_simp [Real.pi_ne_zero, hT.ne', hlog_ne]
      rwa [hrhs] at hmul
  have hden : 0 < T * |Real.log y| + 1 := by positivity
  have hsum : E * (T * |Real.log y| + 1) ≤ 3 * y ^ c / (Real.pi * T) := by
    have hring : E * (T * |Real.log y| + 1) = E * (T * |Real.log y|) + E := by ring
    have hring2 : 2 * y ^ c / (Real.pi * T) + y ^ c / (Real.pi * T) = 3 * y ^ c / (Real.pi * T) := by
      ring
    linarith
  rw [le_div_iff₀ (by positivity : 0 < Real.pi * T * (T * |Real.log y| + 1))]
  have hmul := mul_le_mul_of_nonneg_right hsum (show 0 ≤ Real.pi * T by positivity)
  have hrhs : 3 * y ^ c / (Real.pi * T) * (Real.pi * T) = 3 * y ^ c :=
    div_mul_cancel₀ _ (by positivity)
  linarith

/-- **Effective Truncation Error Bound (`T ≥ 1`)**:
`‖perronKernel1 y c T - max (1 - 1 / y) 0‖ ≤ (3 / π) * y^c / (T * (|log y| + 1))`. -/
theorem norm_perronKernel1_sub_max_le {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 1 ≤ T) :
    ‖perronKernel1 y c T - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖ ≤
      (3 / Real.pi) * y ^ c / (T * (|Real.log y| + 1)) := by
  have hT0 : 0 < T := by linarith
  have hc1 := norm_perronKernel1_sub_max_le_combined hy hc hT0
  have hlog_le : |Real.log y| ≤ T * |Real.log y| := by
    calc |Real.log y| = 1 * |Real.log y| := (one_mul _).symm
      _ ≤ T * |Real.log y| := mul_le_mul_of_nonneg_right hT (abs_nonneg _)
  have hden : T * (|Real.log y| + 1) ≤ T * (T * |Real.log y| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hT0.le
  calc ‖perronKernel1 y c T - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖
      ≤ 3 * y ^ c / (Real.pi * T * (T * |Real.log y| + 1)) := hc1
    _ ≤ 3 * y ^ c / (Real.pi * T * (|Real.log y| + 1)) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        have := mul_le_mul_of_nonneg_left hden Real.pi_pos.le
        linarith
    _ = (3 / Real.pi) * y ^ c / (T * (|Real.log y| + 1)) := by
        field_simp [Real.pi_ne_zero, hT0.ne']

/-- Uniform truncation error bound for the shifted Cesàro-1 ramp kernel (`c > 1`, `T > 0`):
`‖perronRampKernel y c T - max (y - 1) 0‖ ≤ y^c / (π * T)`. -/
theorem norm_perronRampKernel_sub_max_le_uniform {y c T : ℝ} (hy : 0 < y) (hc : 1 < c)
    (hT : 0 < T) :
    ‖perronRampKernel y c T - ((max (y - 1) 0 : ℝ) : ℂ)‖ ≤ y ^ c / (Real.pi * T) := by
  have hEq : perronRampKernel y c T = (y : ℂ) * perronKernel1 y (c - 1) T := by
    unfold perronRampKernel perronKernel1
    rw [mul_left_comm]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => cesaroRampIntegrand_eq_mul_cesaro1 hy t
  have hmax : ((max (y - 1) 0 : ℝ) : ℂ) = (y : ℂ) * ((max (1 - 1 / y) 0 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [mul_max_of_nonneg _ _ hy.le, mul_sub, mul_one, mul_one_div_cancel hy.ne', mul_zero]
  rw [hEq, hmax, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy.le]
  calc y * ‖perronKernel1 y (c - 1) T - ((max (1 - 1 / y) 0 : ℝ) : ℂ)‖
      ≤ y * (y ^ (c - 1) / (Real.pi * T)) :=
        mul_le_mul_of_nonneg_left (norm_perronKernel1_sub_max_le_uniform hy (by linarith) hT) hy.le
    _ = y ^ c / (Real.pi * T) := by
        have hpow : y * y ^ (c - 1) = y ^ c := by
          calc y * y ^ (c - 1) = y ^ (1 : ℝ) * y ^ (c - 1) := by rw [Real.rpow_one]
            _ = y ^ (1 + (c - 1)) := (Real.rpow_add hy _ _).symm
            _ = y ^ c := by congr 1; ring
        rw [← mul_div_assoc, hpow]

/-! ## Section 2: Smoothed Explicit Formula Connecting `RHDirect.ramp` & `ψ_1(x, χ)` to `-L'/L(s, χ)` -/

private lemma chebyshevPsi_nonneg (x : ℝ) : 0 ≤ RHDirect.chebyshevPsi x :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- Elementary unconditional linear upper bound `chebyshevPsi x ≤ 6 * x` for all `x ≥ 1`. -/
theorem chebyshevPsi_le_six_mul {x : ℝ} (hx : 1 ≤ x) :
    RHDirect.chebyshevPsi x ≤ 6 * x := by
  have hx0 : 0 < x := by linarith
  have hpsi : RHDirect.chebyshevPsi x = Chebyshev.psi x := by
    unfold RHDirect.chebyshevPsi Chebyshev.psi
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
    simp
  rw [hpsi]
  have h1 := Chebyshev.psi_le hx
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlogx : Real.log x ≤ 2 * Real.sqrt x := by
    have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx0.le]; ring
    have h3 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    linarith
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  nlinarith

/-- Unconditional sharp upper bound `∑' n, Λ(n) * n^{-c} ≤ 6 * c / (c - 1)` for all real `c > 1`. -/
theorem tsum_vonMangoldt_mul_rpow_le {c : ℝ} (hc : 1 < c) :
    ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c) ≤ 6 * c / (c - 1) := by
  have hc0 : 0 < c := by linarith
  have hsumm : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n => Λ n) (by simp) (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (c : ℂ)).mp
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    simpa using h
  refine hsumm.tsum_le_of_sum_range_le fun N => ?_
  by_cases hN : N ≤ 1
  · interval_cases N <;> simp [div_nonneg (by positivity : 0 ≤ 6 * c) (by linarith : 0 ≤ c - 1)]
  · push Not at hN
    set M : ℕ := N - 1
    have hM1 : 1 ≤ M := by omega
    have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    have hrange : ∑ n ∈ Finset.range N, Λ n * (n : ℝ) ^ (-c) =
        ∑ n ∈ Finset.Icc 1 M, Λ n * (n : ℝ) ^ (-c) := by
      have hsub : Finset.range N = insert 0 (Finset.Icc 1 M) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsub, Finset.sum_insert (by simp)]
      simp
    rw [hrange]
    have hab := Stage3RealAnalyticLandau.abel_summation_dirichlet (fun n => (Λ n : ℂ)) hMR (c : ℂ)
    have hre := congrArg Complex.re hab
    have hLHS : (∑ n ∈ Finset.Icc 1 ⌊(M : ℝ)⌋₊, (Λ n : ℂ) * (n : ℂ) ^ (-(c : ℂ))).re =
        ∑ n ∈ Finset.Icc 1 M, Λ n * (n : ℝ) ^ (-c) := by
      rw [Nat.floor_natCast, Complex.re_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
      have hpow : (n : ℂ) ^ (-(c : ℂ)) = (((n : ℝ) ^ (-c) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]; simp
      rw [hpow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hstep : ∀ t : ℝ, Stage3RealAnalyticLandau.stepSum (fun n => (Λ n : ℂ)) t =
        (RHDirect.chebyshevPsi t : ℂ) := fun t => by
      unfold Stage3RealAnalyticLandau.stepSum RHDirect.chebyshevPsi
      rw [Complex.ofReal_sum]
      have hsub : Finset.range (⌊t⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊t⌋₊) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsub, Finset.sum_insert (by simp)]; simp
    have hMpow : ((M : ℝ) : ℂ) ^ (-(c : ℂ)) = (((M : ℝ) ^ (-c) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by linarith)]; simp
    have hint_re : (∫ t in (1 : ℝ)..(M : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => (Λ n : ℂ)) t * (t : ℂ) ^ (-(c : ℂ) - 1)).re =
        ∫ t in (1 : ℝ)..(M : ℝ), RHDirect.chebyshevPsi t * t ^ (-c - 1) := by
      have hcongr : Set.EqOn
          (fun t : ℝ => Stage3RealAnalyticLandau.stepSum (fun n => (Λ n : ℂ)) t * (t : ℂ) ^ (-(c : ℂ) - 1))
          (fun t : ℝ => ((RHDirect.chebyshevPsi t * t ^ (-c - 1) : ℝ) : ℂ)) (Set.uIcc 1 M) := by
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le hMR] at ht
        have ht0 : 0 < t := by linarith [ht.1]
        rw [hstep t, Complex.ofReal_mul]
        congr 1
        rw [Complex.ofReal_cpow ht0.le]; simp
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal, Complex.ofReal_re]
    rw [hLHS, hstep M, hMpow, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.re_ofReal_mul, hint_re] at hre
    rw [hre]
    -- Bound ψ(M) M^(-c) + c ∫_1^M ψ(t) t^(-c-1) dt using ψ(t) ≤ 6 t
    have hpsiM : RHDirect.chebyshevPsi M * (M : ℝ) ^ (-c) ≤ 6 * (M : ℝ) ^ (1 - c) := by
      have h1 : RHDirect.chebyshevPsi M ≤ 6 * (M : ℝ) := chebyshevPsi_le_six_mul hMR
      have hpow : (M : ℝ) * (M : ℝ) ^ (-c) = (M : ℝ) ^ (1 - c) := by
        calc (M : ℝ) * (M : ℝ) ^ (-c) = (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (-c) := by rw [Real.rpow_one]
          _ = (M : ℝ) ^ (1 + -c) := (Real.rpow_add (by linarith) _ _).symm
          _ = (M : ℝ) ^ (1 - c) := by rw [sub_eq_add_neg]
      calc RHDirect.chebyshevPsi M * (M : ℝ) ^ (-c)
          ≤ (6 * (M : ℝ)) * (M : ℝ) ^ (-c) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by linarith) _)
        _ = 6 * ((M : ℝ) * (M : ℝ) ^ (-c)) := by ring
        _ = 6 * (M : ℝ) ^ (1 - c) := by rw [hpow]
    have hint_le : ∫ t in (1 : ℝ)..(M : ℝ), RHDirect.chebyshevPsi t * t ^ (-c - 1) ≤
        ∫ t in (1 : ℝ)..(M : ℝ), 6 * t ^ (-c) := by
      have hint1 : IntervalIntegrable (fun t : ℝ => RHDirect.chebyshevPsi t * t ^ (-c - 1))
          volume (1 : ℝ) M := by
        refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hMR).mpr ?_
        refine Integrable.mono'
          (integrableOn_const (C := 6 * (M : ℝ)) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
        · have hm : Measurable RHDirect.chebyshevPsi := by
            have h : RHDirect.chebyshevPsi =
                (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
            rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
          exact (hm.mul (measurable_id.pow_const _)).aestronglyMeasurable
        · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
          have ht1 : 1 ≤ t := ht.1.le
          have ht0 : 0 < t := by linarith
          have hpow_le : t ^ (-c - 1) ≤ 1 := by
            calc t ^ (-c - 1) ≤ t ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
              _ = 1 := Real.rpow_zero t
          rw [Real.norm_of_nonneg (mul_nonneg (chebyshevPsi_nonneg t)
            (Real.rpow_nonneg ht0.le _))]
          calc RHDirect.chebyshevPsi t * t ^ (-c - 1)
              ≤ RHDirect.chebyshevPsi t * 1 :=
                mul_le_mul_of_nonneg_left hpow_le (chebyshevPsi_nonneg t)
            _ = RHDirect.chebyshevPsi t := mul_one _
            _ ≤ 6 * t := chebyshevPsi_le_six_mul ht1
            _ ≤ 6 * (M : ℝ) := by linarith [ht.2]
      have hint2 : IntervalIntegrable (fun t : ℝ => 6 * t ^ (-c)) volume (1 : ℝ) M := by
        have hc_cont : ContinuousOn (fun t : ℝ => 6 * t ^ (-c)) (Set.uIcc 1 M) := by
          rw [Set.uIcc_of_le hMR]
          exact continuousOn_const.mul
            (continuousOn_id.rpow_const fun t ht => Or.inl (by simp; linarith [ht.1]))
        exact hc_cont.intervalIntegrable
      refine intervalIntegral.integral_mono_on hMR hint1 hint2 fun t ht => ?_
      have ht0 : 0 < t := by linarith [ht.1]
      have hpow : t * t ^ (-c - 1) = t ^ (-c) := by
        calc t * t ^ (-c - 1) = t ^ (1 : ℝ) * t ^ (-c - 1) := by rw [Real.rpow_one]
          _ = t ^ (1 + (-c - 1)) := (Real.rpow_add ht0 _ _).symm
          _ = t ^ (-c) := by congr 1; ring
      calc RHDirect.chebyshevPsi t * t ^ (-c - 1)
          ≤ (6 * t) * t ^ (-c - 1) :=
            mul_le_mul_of_nonneg_right (chebyshevPsi_le_six_mul ht.1) (Real.rpow_nonneg ht0.le _)
        _ = 6 * (t * t ^ (-c - 1)) := by ring
        _ = 6 * t ^ (-c) := by rw [hpow]
    have hint_eval : ∫ t in (1 : ℝ)..(M : ℝ), 6 * t ^ (-c) =
        6 * (1 - (M : ℝ) ^ (1 - c)) / (c - 1) := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inr ⟨by linarith, fun h => by
          rw [Set.uIcc_of_le hMR] at h; linarith [h.1]⟩)]
      rw [Real.one_rpow]
      have heq : -c + 1 = 1 - c := by ring
      rw [heq]
      field_simp [show c - 1 ≠ 0 by linarith, show 1 - c ≠ 0 by linarith]
      ring
    have hstep1 : RHDirect.chebyshevPsi M * (M : ℝ) ^ (-c) +
        c * ∫ t in (1 : ℝ)..(M : ℝ), RHDirect.chebyshevPsi t * t ^ (-c - 1) ≤
        6 * (M : ℝ) ^ (1 - c) + c * (6 * (1 - (M : ℝ) ^ (1 - c)) / (c - 1)) := by
      linarith [mul_le_mul_of_nonneg_left (hint_le.trans_eq hint_eval) hc0.le]
    have hstep2 : 6 * (M : ℝ) ^ (1 - c) + c * (6 * (1 - (M : ℝ) ^ (1 - c)) / (c - 1)) =
        6 * c / (c - 1) - 6 * (M : ℝ) ^ (1 - c) / (c - 1) := by
      field_simp [show c - 1 ≠ 0 by linarith]
      ring
    have hnn : 0 ≤ 6 * (M : ℝ) ^ (1 - c) / (c - 1) :=
      div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)) (by linarith)
    linarith

/-- Integrated (Cesàro-1) character Chebyshev sum `ψ_1(x, χ) = ∑_{n ≤ x} Λ(n) χ(n) (x - n)`. -/
def psi1Char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * χ n * ((max (x - (n : ℝ)) 0 : ℝ) : ℂ)

/-- Truncated Perron integral for `ψ_1(x, χ)` at height `T` along `Re(s) = c > 1`. -/
def truncatedPerronPsi1 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-T)..T,
      Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))

/-- Truncated Perron integral for `RHDirect.ramp (fun n => χ n) x` at height `T` along `Re(s) = c > 1`. -/
def truncatedPerronRamp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-T)..T,
      Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ)))

private lemma psi1Char_hasSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ =>
      if n = 0 then (0 : ℂ)
      else (Λ n : ℂ) * χ n * ((x : ℂ) * ((max (1 - (n : ℝ) / x) 0 : ℝ) : ℂ)))
      (psi1Char χ x) := by
  have hEq : ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
      (if n = 0 then (0 : ℂ)
       else (Λ n : ℂ) * χ n * ((x : ℂ) * ((max (1 - (n : ℝ) / x) 0 : ℝ) : ℂ))) = psi1Char χ x := by
    unfold psi1Char
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [if_neg hn0, ← Complex.ofReal_mul]
      congr 2
      rw [mul_max_of_nonneg _ _ hx.le, mul_sub, mul_one, mul_div_cancel₀ _ hx.ne', mul_zero]
  rw [← hEq]
  refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
  have hn' : ⌊x⌋₊ + 1 ≤ n := by simpa using hn
  have hn0 : n ≠ 0 := by omega
  rw [if_neg hn0]
  have hlt : x < (n : ℝ) := by
    have h1 := Nat.lt_floor_add_one x
    have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at h2; linarith
  have hmax : max (1 - (n : ℝ) / x) 0 = 0 :=
    max_eq_right (by rw [sub_nonpos, one_le_div hx]; exact hlt.le)
  rw [hmax]; simp

private lemma norm_negLogDerivL_le_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {c : ℝ} (hc : 1 < c) (t : ℝ) :
    ‖Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ))‖ ≤
      ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c) := by
  have hs : 1 < ((c : ℂ) + I * (t : ℂ)).re := by simp [hc]
  rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs]
  have hsumL : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((c : ℂ) + I * (t : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt hs
  have hsumR : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n => Λ n) (by simp) (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (c : ℂ)).mp
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    simpa using h
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsumL.norm).trans (hsumL.norm.tsum_le_tsum (fun n => ?_) hsumR)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos hn]
    have hre : ((c : ℂ) + I * (t : ℂ)).re = c := by simp
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [hre, Real.rpow_neg hnR.le, div_eq_mul_inv]
    calc ‖χ (n : ZMod q)‖ * Λ n * ((n : ℝ) ^ c)⁻¹
        ≤ 1 * Λ n * ((n : ℝ) ^ c)⁻¹ := by
          gcongr; exact χ.norm_le_one _
      _ = Λ n * ((n : ℝ) ^ c)⁻¹ := by ring

/-- **Unconditional Smoothed Mellin–Perron Representation for `ψ_1(x, χ)`**:
for all `q ≥ 1`, `χ : DirichletCharacter ℂ q`, `x > 0`, and `c > 1`:
`ψ_1(x, χ) = (1 / (2π)) ∫_{-∞}^∞ (-L'/L)(c + i t, χ) · x^{c + 1 + i t} / ((c + i t)(c + 1 + i t)) dt`. -/
theorem psi1Char_eq_perron_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    psi1Char χ x =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ,
          Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
            (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
            (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))) := by
  have hc0 : 0 < c := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  -- Define termwise integrand F n t = Λ(n) χ(n) x · cesaro1Integrand (x / n) c t
  let F : ℕ → ℝ → ℂ := fun n t =>
    if n = 0 then 0
    else (Λ n : ℂ) * χ n * (x : ℂ) * cesaro1Integrand (x / (n : ℝ)) c t
  have hF_int : ∀ n : ℕ, Integrable (F n) := fun n => by
    by_cases hn : n = 0
    · subst hn; simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      exact (integrable_cesaro1Integrand (div_pos hx hnR) hc0).const_mul _
  have hsumR : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n => Λ n) (by simp) (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (c : ℂ)).mp
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    simpa using h
  have hF_sum_norm : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
      (hsumR.mul_left (x ^ (c + 1) * (Real.pi / c)))
    by_cases hn : n = 0
    · subst hn; simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      calc ∫ t : ℝ, ‖(Λ n : ℂ) * χ n * (x : ℂ) * cesaro1Integrand (x / (n : ℝ)) c t‖
          ≤ ∫ t : ℝ, (Λ n * x * (x / (n : ℝ)) ^ c) * (c ^ 2 + t ^ 2)⁻¹ := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((integrable_inv_sq_add_sq hc0).const_mul _) (Eventually.of_forall fun t => ?_)
            dsimp only
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.norm_of_nonneg hx.le]
            calc Λ n * ‖χ n‖ * x * ‖cesaro1Integrand (x / (n : ℝ)) c t‖
                ≤ Λ n * 1 * x * ((x / (n : ℝ)) ^ c * (c ^ 2 + t ^ 2)⁻¹) := by
                  gcongr
                  · exact χ.norm_le_one _
                  · exact norm_cesaro1Integrand_le_inv_sq_add_sq (div_pos hx hnR) hc0 t
              _ = Λ n * x * (x / (n : ℝ)) ^ c * (c ^ 2 + t ^ 2)⁻¹ := by ring
        _ = (Λ n * x * (x / (n : ℝ)) ^ c) * (Real.pi / c) := by
            rw [integral_const_mul, integral_inv_sq_add_sq hc0]
        _ = x ^ (c + 1) * (Real.pi / c) * (Λ n * (n : ℝ) ^ (-c)) := by
            rw [Real.div_rpow hx.le hnR.le, Real.rpow_add hx, Real.rpow_one,
              Real.rpow_neg hnR.le, div_eq_mul_inv]
            ring
  -- Tonelli / dominated series-integral swap
  have hswap := hasSum_integral_of_summable_integral_norm hF_int hF_sum_norm
  -- Identify ∑' n, F n t with the integrand
  have htsum_t : ∀ t : ℝ, ∑' n : ℕ, F n t =
      Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))) := by
    intro t
    have hs : 1 < ((c : ℂ) + I * (t : ℂ)).re := by simp [hc]
    rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs]
    set W : ℂ := (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
      (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))
    have hsumL : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((c : ℂ) + I * (t : ℂ)) :=
      χ.LSeriesSummable_twist_vonMangoldt hs
    have h1 := (hsumL.hasSum.mul_right W).tsum_eq
    rw [mul_div_assoc]
    change ∑' n : ℕ, F n t = (∑' n : ℕ, LSeries.term (fun m => χ m * (Λ m : ℂ)) ((c : ℂ) + I * (t : ℂ)) n) * W
    rw [← h1]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, LSeries.term]
    · simp only [F, LSeries.term, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      unfold cesaro1Integrand
      have hpow1 : ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) =
          (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / (n : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) := by
        have hxnC : ((x / (n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hx hnR).ne'
        have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnR.ne'
        rw [Complex.cpow_def_of_ne_zero hxnC, Complex.cpow_def_of_ne_zero hxC,
          Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_sub, ← Complex.ofReal_log (div_pos hx hnR).le,
          Real.log_div hx.ne' hnR.ne', ← Complex.ofReal_log hx.le, ← Complex.ofReal_natCast,
          ← Complex.ofReal_log hnR.le]
        congr 1; push_cast; ring
      have hpow2 : (x : ℂ) * (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) =
          (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) := by
        have hadd : (c : ℂ) + 1 + I * (t : ℂ) = 1 + ((c : ℂ) + I * (t : ℂ)) := by ring
        rw [hadd, Complex.cpow_add 1 ((c : ℂ) + I * (t : ℂ)) hxC, Complex.cpow_one]
      rw [hpow1]
      dsimp only [W]
      calc (Λ n : ℂ) * χ (n : ZMod q) * (x : ℂ) *
              ((x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / (n : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
                (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))))
          = χ (n : ZMod q) * (Λ n : ℂ) / (n : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) *
              (((x : ℂ) * (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) /
                (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))) := by ring
        _ = _ := by rw [hpow2]
  simp_rw [htsum_t] at hswap
  -- Evaluate each termwise integral via perronKernel1Full_eq_max
  have hmul := hswap.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have hterm_eq : ∀ n : ℕ, ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, F n t =
      if n = 0 then (0 : ℂ)
      else (Λ n : ℂ) * χ n * ((x : ℂ) * ((max (1 - (n : ℝ) / x) 0 : ℝ) : ℂ)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [integral_const_mul, mul_left_comm]
      change (Λ n : ℂ) * χ n * (x : ℂ) * perronKernel1Full (x / (n : ℝ)) c = _
      rw [perronKernel1Full_eq_max (div_pos hx hnR) hc0]
      have hdiv : 1 / (x / (n : ℝ)) = (n : ℝ) / x := by field_simp [hx.ne', hnR.ne']
      rw [hdiv]
      ring
  have hsum1 := hmul.congr_fun fun n => (hterm_eq n).symm
  exact (psi1Char_hasSum χ hx).unique hsum1

/-- **Unconditional Smoothed Mellin–Perron Representation for `RHDirect.ramp`**:
for all `q ≥ 1`, `χ : DirichletCharacter ℂ q`, `x > 0`, and `c > 1`:
`ramp (fun n => χ n) x = (1 / (2π)) ∫_{-∞}^∞ (-L'/L)(c + i t, χ) · x^{c + i t} / ((c + i t)(c - 1 + i t)) dt`. -/
theorem rampChar_eq_perron_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    RHDirect.ramp (fun n => χ n) x =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ,
          Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
            (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
            (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ))) := by
  have hc1 : 0 < c - 1 := by linarith
  let F : ℕ → ℝ → ℂ := fun n t =>
    if n = 0 then 0
    else (Λ n : ℂ) * χ n * cesaroRampIntegrand (x / (n : ℝ)) c t
  have hF_int : ∀ n : ℕ, Integrable (F n) := fun n => by
    by_cases hn : n = 0
    · subst hn; simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      exact (integrable_cesaroRampIntegrand (div_pos hx hnR) hc).const_mul _
  have hsumR : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n => Λ n) (by simp) (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (c : ℂ)).mp
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    simpa using h
  have hF_sum_norm : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
      (hsumR.mul_left (x ^ c * (Real.pi / (c - 1))))
    by_cases hn : n = 0
    · subst hn; simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hdiv_pos : 0 < x / (n : ℝ) := div_pos hx hnR
      calc ∫ t : ℝ, ‖(Λ n : ℂ) * χ n * cesaroRampIntegrand (x / (n : ℝ)) c t‖
          ≤ ∫ t : ℝ, (Λ n * (x / (n : ℝ)) ^ c) * ((c - 1) ^ 2 + t ^ 2)⁻¹ := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((integrable_inv_sq_add_sq hc1).const_mul _) (Eventually.of_forall fun t => ?_)
            dsimp only
            rw [cesaroRampIntegrand_eq_mul_cesaro1 hdiv_pos t, norm_mul, norm_mul, norm_mul,
              Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
              Real.norm_of_nonneg hdiv_pos.le]
            have hpow : (x / (n : ℝ)) * (x / (n : ℝ)) ^ (c - 1) = (x / (n : ℝ)) ^ c := by
              calc (x / (n : ℝ)) * (x / (n : ℝ)) ^ (c - 1)
                  = (x / (n : ℝ)) ^ (1 : ℝ) * (x / (n : ℝ)) ^ (c - 1) := by rw [Real.rpow_one]
                _ = (x / (n : ℝ)) ^ (1 + (c - 1)) := (Real.rpow_add hdiv_pos _ _).symm
                _ = (x / (n : ℝ)) ^ c := by congr 1; ring
            calc Λ n * ‖χ n‖ * ((x / (n : ℝ)) * ‖cesaro1Integrand (x / (n : ℝ)) (c - 1) t‖)
                ≤ Λ n * 1 * ((x / (n : ℝ)) * ((x / (n : ℝ)) ^ (c - 1) * ((c - 1) ^ 2 + t ^ 2)⁻¹)) := by
                  gcongr
                  · exact χ.norm_le_one _
                  · exact norm_cesaro1Integrand_le_inv_sq_add_sq hdiv_pos hc1 t
              _ = Λ n * ((x / (n : ℝ)) * (x / (n : ℝ)) ^ (c - 1)) * ((c - 1) ^ 2 + t ^ 2)⁻¹ := by ring
              _ = Λ n * (x / (n : ℝ)) ^ c * ((c - 1) ^ 2 + t ^ 2)⁻¹ := by rw [hpow]
        _ = (Λ n * (x / (n : ℝ)) ^ c) * (Real.pi / (c - 1)) := by
            rw [integral_const_mul, integral_inv_sq_add_sq hc1]
        _ = x ^ c * (Real.pi / (c - 1)) * (Λ n * (n : ℝ) ^ (-c)) := by
            rw [Real.div_rpow hx.le hnR.le, Real.rpow_neg hnR.le, div_eq_mul_inv]; ring
  have hswap := hasSum_integral_of_summable_integral_norm hF_int hF_sum_norm
  have htsum_t : ∀ t : ℝ, ∑' n : ℕ, F n t =
      Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ))) := by
    intro t
    have hs : 1 < ((c : ℂ) + I * (t : ℂ)).re := by simp [hc]
    rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs]
    set W : ℂ := (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
      (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ)))
    have hsumL : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((c : ℂ) + I * (t : ℂ)) :=
      χ.LSeriesSummable_twist_vonMangoldt hs
    have h1 := (hsumL.hasSum.mul_right W).tsum_eq
    rw [mul_div_assoc]
    change ∑' n : ℕ, F n t = (∑' n : ℕ, LSeries.term (fun m => χ m * (Λ m : ℂ)) ((c : ℂ) + I * (t : ℂ)) n) * W
    rw [← h1]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, LSeries.term]
    · simp only [F, LSeries.term, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      unfold cesaroRampIntegrand
      have hpow1 : ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) =
          (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / (n : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) := by
        have hxnC : ((x / (n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hx hnR).ne'
        have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
        have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnR.ne'
        rw [Complex.cpow_def_of_ne_zero hxnC, Complex.cpow_def_of_ne_zero hxC,
          Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_sub, ← Complex.ofReal_log (div_pos hx hnR).le,
          Real.log_div hx.ne' hnR.ne', ← Complex.ofReal_log hx.le, ← Complex.ofReal_natCast,
          ← Complex.ofReal_log hnR.le]
        congr 1; push_cast; ring
      rw [hpow1]
      dsimp only [W]
      ring
  simp_rw [htsum_t] at hswap
  have hmul := hswap.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have hterm_eq : ∀ n : ℕ, ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, F n t =
      (Λ n : ℂ) * χ n * ((MellinExplicit.cesaroKernel (n : ℝ) x : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [integral_const_mul, mul_left_comm]
      change (Λ n : ℂ) * χ n * perronRampKernelFull (x / (n : ℝ)) c = _
      rw [perronRampKernelFull_eq_max (div_pos hx hnR) hc]
      rfl
  exact (MellinExplicit.ramp_eq_tsum_hasSum (fun n => χ n) x).unique
    (hmul.congr_fun fun n => (hterm_eq n).symm)

/-- **Effective Finite-`T` Truncation Error Bound for `ψ_1(x, χ)`**:
for all `q ≥ 1`, `χ : DirichletCharacter ℂ q`, `x > 0`, `c > 1`, `T > 0`:
`‖psi1Char χ x - truncatedPerronPsi1 χ x c T‖ ≤ (6 * c / π) * x^{c + 1} / ((c - 1) * T)`. -/
theorem norm_psi1Char_sub_truncatedPerron_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T) :
    ‖psi1Char χ x - truncatedPerronPsi1 χ x c T‖ ≤
      (6 * c / Real.pi) * x ^ (c + 1) / ((c - 1) * T) := by
  have hc0 : 0 < c := by linarith
  set f : ℝ → ℂ := fun t =>
    Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
      (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
      (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))
  set S : ℝ := ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c)
  have hS_nn : 0 ≤ S := tsum_nonneg fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hS_le : S ≤ 6 * c / (c - 1) := tsum_vonMangoldt_mul_rpow_le hc
  have hf_meas : AEStronglyMeasurable f volume := by
    have hcont : Continuous f := by
      dsimp only [f]
      have hL : Continuous (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ))) := by
        unfold Stage3ZeroFreeRegion.negLogDerivL
        have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
        have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 1 < s.re} := by
          intro s hs
          have hs1 : s ≠ 1 := fun h => by subst h; simp at hs
          exact (DirichletCharacter.differentiableAt_LFunction χ s (.inl hs1)).differentiableWithinAt
        have hcontL : ContinuousOn (DirichletCharacter.LFunction χ) {s : ℂ | 1 < s.re} :=
          hdiff.continuousOn
        have hcontL' : ContinuousOn (deriv (DirichletCharacter.LFunction χ)) {s : ℂ | 1 < s.re} :=
          (hdiff.deriv hopen).continuousOn
        have hmap : Continuous (fun t : ℝ => (c : ℂ) + I * (t : ℂ)) := by fun_prop
        have hmem : ∀ t : ℝ, ((c : ℂ) + I * (t : ℂ)) ∈ {s : ℂ | 1 < s.re} := fun t => by simp [hc]
        refine (hcontL'.comp_continuous hmap hmem).neg.div (hcontL.comp_continuous hmap hmem) fun t => ?_
        have hs1 : (c : ℂ) + I * (t : ℂ) ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr hs1) (by simp [hc.le])
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      have hpow : Continuous (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ))) := by
        have hEq : (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ))) =
            fun t : ℝ => cexp (Complex.log (x : ℂ) * ((c : ℂ) + 1 + I * (t : ℂ))) :=
          funext fun t => Complex.cpow_def_of_ne_zero hxC _
        rw [hEq]; fun_prop
      refine (hL.mul hpow).div (by fun_prop) fun t => mul_ne_zero ?_ ?_
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
    exact hcont.aestronglyMeasurable
  have hf_norm_all : ∀ t : ℝ, ‖f t‖ ≤ (S * x ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹ := by
    intro t
    dsimp only [f]
    have hre : ((c : ℂ) + 1 + I * (t : ℂ)).re = c + 1 := by simp
    have h0 := norm_cesaro1Integrand_le_inv_sq_add_sq one_pos hc0 t
    have hden : ‖(1 : ℂ) / (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))‖ ≤
        (c ^ 2 + t ^ 2)⁻¹ := by
      simpa [cesaro1Integrand, Complex.one_cpow] using h0
    rw [mul_div_assoc, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    have hden' : x ^ (c + 1) / ‖((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))‖ ≤
        x ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx.le _)
      simpa [norm_div, norm_one, one_div] using hden
    calc ‖Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ))‖ *
            (x ^ (c + 1) / ‖((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))‖)
        ≤ S * (x ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹) :=
          mul_le_mul (norm_negLogDerivL_le_tsum χ hc t) hden' (by positivity) hS_nn
      _ = S * x ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹ := by ring
  have hf_int : Integrable f :=
    ((integrable_inv_sq_add_sq hc0).const_mul (S * x ^ (c + 1))).mono' hf_meas
      (Eventually.of_forall hf_norm_all)
  have hf_norm_t : ∀ t : ℝ, t ≠ 0 → ‖f t‖ ≤ S * x ^ (c + 1) / t ^ 2 := by
    intro t ht
    have h1 := hf_norm_all t
    have h2 : (c ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_ne_zero ht) (by linarith [sq_nonneg c])
    calc ‖f t‖ ≤ S * x ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹ := h1
      _ ≤ S * x ^ (c + 1) * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = S * x ^ (c + 1) / t ^ 2 := by rw [div_eq_mul_inv]
  rw [psi1Char_eq_perron_integral χ hx hc]
  unfold truncatedPerronPsi1
  change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, f t) -
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, f t)‖ ≤ _
  rw [← mul_sub, ← neg_sub (∫ t in (-T)..T, f t), integral_diff_Icc_tail hf_int hT, neg_neg,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint_sq : IntegrableOn (fun t : ℝ => S * x ^ (c + 1) / t ^ 2) (Ioi T) := by
    have h1 : IntegrableOn (fun t : ℝ => (S * x ^ (c + 1)) * t ^ (-2 : ℝ)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul (S * x ^ (c + 1))
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  have hpos_tail : ‖∫ t in Ioi T, f t‖ ≤ S * x ^ (c + 1) / T := by
    calc ‖∫ t in Ioi T, f t‖ ≤ ∫ t in Ioi T, ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi T, S * x ^ (c + 1) / t ^ 2 :=
          setIntegral_mono_on hf_int.integrableOn.norm hint_sq measurableSet_Ioi fun t ht =>
            hf_norm_t t (hT.trans ht).ne'
      _ = S * x ^ (c + 1) / T := by
          simp_rw [div_eq_mul_inv]; rw [integral_const_mul, integral_Ioi_inv_sq hT]; ring
  have hint_sq_neg : IntegrableOn (fun t : ℝ => S * x ^ (c + 1) / (-t) ^ 2) (Iic (-T)) := by
    have h1 : IntegrableOn (fun t : ℝ => S * x ^ (c + 1) / t ^ 2) (Ici T) :=
      hint_sq.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have h2 : IntegrableOn (fun t : ℝ => S * x ^ (c + 1) / (-t) ^ 2) (Neg.neg ⁻¹' Ici T) := h1.comp_neg
    have hset : Neg.neg ⁻¹' Ici T = Iic (-T) := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]; constructor <;> intro h <;> linarith
    rwa [hset] at h2
  have hneg_tail : ‖∫ t in Iic (-T), f t‖ ≤ S * x ^ (c + 1) / T := by
    calc ‖∫ t in Iic (-T), f t‖ ≤ ∫ t in Iic (-T), ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Iic (-T), S * x ^ (c + 1) / (-t) ^ 2 :=
          setIntegral_mono_on hf_int.integrableOn.norm hint_sq_neg measurableSet_Iic fun t ht => by
            have ht0 : t ≠ 0 := by linarith [Set.mem_Iic.mp ht]
            simpa [neg_sq] using hf_norm_t t ht0
      _ = ∫ t in Ioi T, S * x ^ (c + 1) / t ^ 2 :=
          integral_Iic_neg_eq_Ioi (fun u => S * x ^ (c + 1) / u ^ 2) T
      _ = S * x ^ (c + 1) / T := by
          simp_rw [div_eq_mul_inv]; rw [integral_const_mul, integral_Ioi_inv_sq hT]; ring
  calc (2 * Real.pi)⁻¹ * ‖(∫ t in Iic (-T), f t) + (∫ t in Ioi T, f t)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * (S * x ^ (c + 1) / T)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (by positivity)
    _ = S * x ^ (c + 1) / (Real.pi * T) := by field_simp [Real.pi_ne_zero, hT.ne']
    _ ≤ (6 * c / (c - 1)) * x ^ (c + 1) / (Real.pi * T) := by gcongr
    _ = (6 * c / Real.pi) * x ^ (c + 1) / ((c - 1) * T) := by
        field_simp [Real.pi_ne_zero, hT.ne', show c - 1 ≠ 0 by linarith]

/-- **Effective Finite-`T` Truncation Error Bound for `RHDirect.ramp`**:
for all `q ≥ 1`, `χ : DirichletCharacter ℂ q`, `x > 0`, `c > 1`, `T > 0`:
`‖ramp (fun n => χ n) x - truncatedPerronRamp χ x c T‖ ≤ (6 * c / π) * x^c / ((c - 1) * T)`. -/
theorem norm_rampChar_sub_truncatedPerron_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T) :
    ‖RHDirect.ramp (fun n => χ n) x - truncatedPerronRamp χ x c T‖ ≤
      (6 * c / Real.pi) * x ^ c / ((c - 1) * T) := by
  have hc1 : 0 < c - 1 := by linarith
  set f : ℝ → ℂ := fun t =>
    Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
      (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
      (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ)))
  set S : ℝ := ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c)
  have hS_nn : 0 ≤ S := tsum_nonneg fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hS_le : S ≤ 6 * c / (c - 1) := tsum_vonMangoldt_mul_rpow_le hc
  have hf_meas : AEStronglyMeasurable f volume := by
    have hcont : Continuous f := by
      dsimp only [f]
      have hL : Continuous (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ))) := by
        unfold Stage3ZeroFreeRegion.negLogDerivL
        have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
        have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 1 < s.re} := by
          intro s hs
          have hs1 : s ≠ 1 := fun h => by subst h; simp at hs
          exact (DirichletCharacter.differentiableAt_LFunction χ s (.inl hs1)).differentiableWithinAt
        have hmap : Continuous (fun t : ℝ => (c : ℂ) + I * (t : ℂ)) := by fun_prop
        have hmem : ∀ t : ℝ, ((c : ℂ) + I * (t : ℂ)) ∈ {s : ℂ | 1 < s.re} := fun t => by simp [hc]
        refine ((hdiff.deriv hopen).continuousOn.comp_continuous hmap hmem).neg.div
          (hdiff.continuousOn.comp_continuous hmap hmem) fun t => ?_
        have hs1 : (c : ℂ) + I * (t : ℂ) ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr hs1) (by simp [hc.le])
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      have hpow : Continuous (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) := by
        have hEq : (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) =
            fun t : ℝ => cexp (Complex.log (x : ℂ) * ((c : ℂ) + I * (t : ℂ))) :=
          funext fun t => Complex.cpow_def_of_ne_zero hxC _
        rw [hEq]; fun_prop
      refine (hL.mul hpow).div (by fun_prop) fun t => mul_ne_zero ?_ ?_
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
    exact hcont.aestronglyMeasurable
  have hf_norm_all : ∀ t : ℝ, ‖f t‖ ≤ (S * x ^ c) * ((c - 1) ^ 2 + t ^ 2)⁻¹ := by
    intro t
    dsimp only [f]
    have hre : ((c : ℂ) + I * (t : ℂ)).re = c := by simp
    have h0 := norm_cesaro1Integrand_le_inv_sq_add_sq one_pos hc1 t
    have hden_eq : ((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ)) =
        (((c - 1 : ℝ) : ℂ) + I * (t : ℂ)) * (((c - 1 : ℝ) : ℂ) + 1 + I * (t : ℂ)) := by
      push_cast; ring
    have hden : ‖(1 : ℂ) / (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ)))‖ ≤
        ((c - 1) ^ 2 + t ^ 2)⁻¹ := by
      rw [hden_eq]; simpa [cesaro1Integrand, Complex.one_cpow] using h0
    rw [mul_div_assoc, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    have hden' : x ^ c / ‖((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ))‖ ≤
        x ^ c * ((c - 1) ^ 2 + t ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx.le _)
      simpa [norm_div, norm_one, one_div] using hden
    calc ‖Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ))‖ *
            (x ^ c / ‖((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) - 1 + I * (t : ℂ))‖)
        ≤ S * (x ^ c * ((c - 1) ^ 2 + t ^ 2)⁻¹) :=
          mul_le_mul (norm_negLogDerivL_le_tsum χ hc t) hden' (by positivity) hS_nn
      _ = S * x ^ c * ((c - 1) ^ 2 + t ^ 2)⁻¹ := by ring
  have hf_int : Integrable f :=
    ((integrable_inv_sq_add_sq hc1).const_mul (S * x ^ c)).mono' hf_meas
      (Eventually.of_forall hf_norm_all)
  have hf_norm_t : ∀ t : ℝ, t ≠ 0 → ‖f t‖ ≤ S * x ^ c / t ^ 2 := by
    intro t ht
    have h1 := hf_norm_all t
    have h2 : ((c - 1) ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_ne_zero ht) (by linarith [sq_nonneg (c - 1)])
    calc ‖f t‖ ≤ S * x ^ c * ((c - 1) ^ 2 + t ^ 2)⁻¹ := h1
      _ ≤ S * x ^ c * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = S * x ^ c / t ^ 2 := by rw [div_eq_mul_inv]
  rw [rampChar_eq_perron_integral χ hx hc]
  unfold truncatedPerronRamp
  change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, f t) -
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, f t)‖ ≤ _
  rw [← mul_sub, ← neg_sub (∫ t in (-T)..T, f t), integral_diff_Icc_tail hf_int hT, neg_neg,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint_sq : IntegrableOn (fun t : ℝ => S * x ^ c / t ^ 2) (Ioi T) := by
    have h1 : IntegrableOn (fun t : ℝ => (S * x ^ c) * t ^ (-2 : ℝ)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul (S * x ^ c)
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  have hpos_tail : ‖∫ t in Ioi T, f t‖ ≤ S * x ^ c / T := by
    calc ‖∫ t in Ioi T, f t‖ ≤ ∫ t in Ioi T, ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi T, S * x ^ c / t ^ 2 :=
          setIntegral_mono_on hf_int.integrableOn.norm hint_sq measurableSet_Ioi fun t ht =>
            hf_norm_t t (hT.trans ht).ne'
      _ = S * x ^ c / T := by
          simp_rw [div_eq_mul_inv]; rw [integral_const_mul, integral_Ioi_inv_sq hT]; ring
  have hint_sq_neg : IntegrableOn (fun t : ℝ => S * x ^ c / (-t) ^ 2) (Iic (-T)) := by
    have h1 : IntegrableOn (fun t : ℝ => S * x ^ c / t ^ 2) (Ici T) :=
      hint_sq.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have h2 : IntegrableOn (fun t : ℝ => S * x ^ c / (-t) ^ 2) (Neg.neg ⁻¹' Ici T) := h1.comp_neg
    have hset : Neg.neg ⁻¹' Ici T = Iic (-T) := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]; constructor <;> intro h <;> linarith
    rwa [hset] at h2
  have hneg_tail : ‖∫ t in Iic (-T), f t‖ ≤ S * x ^ c / T := by
    calc ‖∫ t in Iic (-T), f t‖ ≤ ∫ t in Iic (-T), ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Iic (-T), S * x ^ c / (-t) ^ 2 :=
          setIntegral_mono_on hf_int.integrableOn.norm hint_sq_neg measurableSet_Iic fun t ht => by
            have ht0 : t ≠ 0 := by linarith [Set.mem_Iic.mp ht]
            simpa [neg_sq] using hf_norm_t t ht0
      _ = ∫ t in Ioi T, S * x ^ c / t ^ 2 :=
          integral_Iic_neg_eq_Ioi (fun u => S * x ^ c / u ^ 2) T
      _ = S * x ^ c / T := by
          simp_rw [div_eq_mul_inv]; rw [integral_const_mul, integral_Ioi_inv_sq hT]; ring
  calc (2 * Real.pi)⁻¹ * ‖(∫ t in Iic (-T), f t) + (∫ t in Ioi T, f t)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * (S * x ^ c / T)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (by positivity)
    _ = S * x ^ c / (Real.pi * T) := by field_simp [Real.pi_ne_zero, hT.ne']
    _ ≤ (6 * c / (c - 1)) * x ^ c / (Real.pi * T) := by gcongr
    _ = (6 * c / Real.pi) * x ^ c / ((c - 1) * T) := by
        field_simp [Real.pi_ne_zero, hT.ne', show c - 1 ≠ 0 by linarith]

/-! ### Wiring into `Stage3ZeroFreeRegion.TruncatedExplicitFormulaPackage` & `Stage3RealAnalyticLandau` -/

/-- **Bridge 1**: Any `Stage3ZeroFreeRegion.TruncatedExplicitFormulaPackage θ C_N C_R`
unconditionally yields:
1. `Stage2DirichletAP.PsiCharPowerBound θ'` for every `θ' ∈ (θ, 1)`,
2. Quantitative Cesàro-1 ramp bound `|Gz y| ≤ (M / (1 - θ')) y^{θ'}` on `y ≥ 1`,
3. De-smoothed `|ψ(x) - x| ≤ (4 M / (1 - θ') + 1) x^{(1 + θ') / 2}` via
   `Stage3RealAnalyticLandau.abs_psi_sub_id_of_Gz_rpow`, and
4. Full discharge of `Stage2PrimePairs` (`LinnikAPDyadic`, `LinnikAPInterval`, `PairSupply`,
   `PairEx`, `SmallOne`). -/
theorem stage4_bridge_of_truncatedExplicitFormula {θ C_N C_R θ' : ℝ}
    (H : Stage3ZeroFreeRegion.TruncatedExplicitFormulaPackage θ C_N C_R)
    (hθ'lo : θ < θ') (hθ'hi : θ' < 1) :
    Stage2DirichletAP.PsiCharPowerBound θ' ∧
      (∃ M : ℝ, 0 ≤ M ∧
        (∀ y : ℝ, 1 ≤ y → |RHDirect.Gz y| ≤ (M / (1 - θ')) * y ^ θ') ∧
        (∀ x : ℝ, 4 ≤ x →
          |RHDirect.chebyshevPsi x - x| ≤ (4 * (M / (1 - θ')) + 1) * x ^ ((1 + θ') / 2))) ∧
      (Stage2PrimePairs.LinnikAPDyadic ∧
        Stage2PrimePairs.LinnikAPInterval ∧
        HostFieldSupply.PairSupply ∧
        ThetaSlopeEngine.PairEx ∧
        HostFieldSupply.SmallOne) := by
  have hPsi := Stage3ZeroFreeRegion.psiCharPowerBound_of_truncatedExplicitFormula H hθ'lo hθ'hi
  have hPairs := Stage3ZeroFreeRegion.stage2PrimePairs_of_truncatedExplicitFormula H
  have ⟨hθ'0, _, C, hC0, hC⟩ := hPsi
  have hθ'_pos : 0 < θ' := by linarith [H.theta_ge_half]
  set M : ℝ := max C (12 + 2) with hM_def
  have hM0 : 0 ≤ M := le_trans (by norm_num) (le_max_right _ _)
  have hpsi_all : ∀ t : ℝ, 1 ≤ t → |RHDirect.chebyshevPsi t - t| ≤ M * t ^ θ' := by
    intro t ht
    by_cases ht2 : 2 ≤ t
    · have h1 := (hC 2 le_rfl t ht2).1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
    · push Not at ht2
      have h1 : RHDirect.chebyshevPsi t ≤ 6 * t := chebyshevPsi_le_six_mul ht
      have h2 : 0 ≤ RHDirect.chebyshevPsi t := chebyshevPsi_nonneg t
      have h3 : |RHDirect.chebyshevPsi t - t| ≤ 14 := by
        rw [abs_le]; constructor <;> linarith
      have h4 : (1 : ℝ) ≤ t ^ θ' := Real.one_le_rpow ht hθ'0
      have h5 : (14 : ℝ) ≤ M := by
        have : (14 : ℝ) = 12 + 2 := by norm_num
        rw [this]; exact le_max_right _ _
      nlinarith
  have hGz : ∀ y : ℝ, 1 ≤ y → |RHDirect.Gz y| ≤ (M / (1 - θ')) * y ^ θ' := fun y hy =>
    (Stage3RealAnalyticLandau.Gz_eq_neg_mul_tail_integral_and_bound hθ'hi hpsi_all hy).2
  have hDeSmooth : ∀ x : ℝ, 4 ≤ x →
      |RHDirect.chebyshevPsi x - x| ≤ (4 * (M / (1 - θ')) + 1) * x ^ ((1 + θ') / 2) := fun x hx =>
    Stage3RealAnalyticLandau.abs_psi_sub_id_of_Gz_rpow (div_nonneg hM0 (by linarith)) hθ'_pos hθ'hi hGz hx
  exact ⟨hPsi, ⟨M, hM0, hGz, hDeSmooth⟩, hPairs⟩

/-- **Bridge 2 (Smoothed Cesàro-1 Zero-Sum → `|Gz y| ≤ C y^θ` → `|ψ(x) - x| ≤ (4C+1) x^{(1+θ)/2}`
→ Zero-Free Half-Plane `Re(s) > (1 + θ)/2`)**:
if `Gz y` satisfies the smoothed Cesàro-1 explicit formula bound `|Gz y| ≤ C y^θ` (`0 < θ < 1`),
then `Stage3RealAnalyticLandau.abs_psi_sub_id_of_Gz_rpow` + `zeroFree_riemannZeta_of_psi_bound`
unconditionally recover both `ψ(x) - x = O(x^{(1+θ)/2})` and zero-freeness of `riemannZeta`
on `Re(s) > (1 + θ) / 2`! -/
theorem zeroFree_and_psi_of_Gz_rpow {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hGz : ∀ y : ℝ, 1 ≤ y → |RHDirect.Gz y| ≤ C * y ^ θ) :
    (∀ x : ℝ, 4 ≤ x → |RHDirect.chebyshevPsi x - x| ≤ (4 * C + 1) * x ^ ((1 + θ) / 2)) ∧
      (∀ s : ℂ, (1 + θ) / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) := by
  have hpsi4 : ∀ x : ℝ, 4 ≤ x →
      |RHDirect.chebyshevPsi x - x| ≤ (4 * C + 1) * x ^ ((1 + θ) / 2) := fun x hx =>
    Stage3RealAnalyticLandau.abs_psi_sub_id_of_Gz_rpow hC hθ0 hθ1 hGz hx
  set M : ℝ := max (4 * C + 1) 28
  have hM0 : 0 ≤ M := le_trans (by norm_num) (le_max_right _ _)
  have hpsi1 : ∀ x : ℝ, 1 ≤ x → |RHDirect.chebyshevPsi x - x| ≤ M * x ^ ((1 + θ) / 2) := by
    intro x hx
    by_cases hx4 : 4 ≤ x
    · exact (hpsi4 x hx4).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
    · push Not at hx4
      have h1 : RHDirect.chebyshevPsi x ≤ 6 * x := chebyshevPsi_le_six_mul hx
      have h2 : 0 ≤ RHDirect.chebyshevPsi x := chebyshevPsi_nonneg x
      have h3 : |RHDirect.chebyshevPsi x - x| ≤ 28 := by
        rw [abs_le]; constructor <;> linarith
      have h4 : (1 : ℝ) ≤ x ^ ((1 + θ) / 2) := Real.one_le_rpow hx (by linarith)
      have h5 : (28 : ℝ) ≤ M := le_max_right _ _
      nlinarith
  exact ⟨hpsi4,
    (Stage3RealAnalyticLandau.zeroFree_riemannZeta_of_psi_bound hM0 (by linarith) hpsi1).1⟩

/-! ## Section 3: Weil Positivity Criterion for the Riemann Hypothesis (`RH ↔ Weil ≥ 0`) -/

/-- Weil involution `f̃(u) = conj (f (-u))`. -/
def weilInvolution (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  starRingEnd ℂ (f (-u))

/-- Additive Weil convolution `(f * g)(u) = ∫_{-∞}^∞ f(v) g(u - v) dv`. -/
def weilConv (f g : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, f v * g (u - v)

/-- Bilateral Laplace/Mellin transform centered on the critical line `Re(s) = 1/2`:
`Φ_f(s) = ∫_{-∞}^∞ f(u) exp((s - 1/2) u) du`. -/
def weilBilateralTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, f u * cexp ((s - 1 / 2) * (u : ℂ))

/-- Admissibility of a Weil test function at exponential decay rate `σ₀`:
measurable and `‖f u‖ ≤ C exp(-σ₀ |u|)`. When `σ₀ > 1/2`, `Φ_f(s)` converges absolutely on the
entire closed critical strip `0 ≤ Re(s) ≤ 1`. -/
def WeilAdmissible (f : ℝ → ℂ) (σ₀ : ℝ) : Prop :=
  AEStronglyMeasurable f volume ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖f u‖ ≤ C * Real.exp (-σ₀ * |u|)

private lemma integrable_exp_neg_abs {α : ℝ} (hα : 0 < α) :
    Integrable (fun u : ℝ => Real.exp (-α * |u|)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have hpos : IntegrableOn (fun u : ℝ => Real.exp (-α * u)) (Ici 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have hneg : IntegrableOn (fun u : ℝ => Real.exp (-α * (-u))) (Neg.neg ⁻¹' Ici 0) :=
      hpos.comp_neg
    have hset : Neg.neg ⁻¹' Ici (0 : ℝ) = Iic 0 := by
      ext u; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]; constructor <;> intro h <;> linarith
    rw [hset] at hneg
    refine hneg.congr_fun (fun u hu => ?_) measurableSet_Iic
    dsimp only
    rw [abs_of_nonpos (Set.mem_Iic.mp hu)]
  · refine (integrableOn_exp_mul_Ioi (by linarith : -α < 0) 0).congr_fun (fun u hu => ?_) measurableSet_Ioi
    dsimp only
    rw [abs_of_pos hu]

theorem weilAdmissible_involution {f : ℝ → ℂ} {σ₀ : ℝ} (hf : WeilAdmissible f σ₀) :
    WeilAdmissible (weilInvolution f) σ₀ := by
  obtain ⟨hm, C, hC, hbd⟩ := hf
  refine ⟨?_, C, hC, fun u => ?_⟩
  · have h1 : AEStronglyMeasurable (fun u : ℝ => f (-u)) volume :=
      hm.comp_measurePreserving (MeasureTheory.Measure.measurePreserving_neg volume)
    exact Complex.conjCLE.continuous.comp_aestronglyMeasurable h1
  · unfold weilInvolution
    rw [Complex.norm_conj, ← abs_neg u]
    exact hbd (-u)

theorem integrable_weilBilateralTransform {f : ℝ → ℂ} {σ₀ : ℝ} (hf : WeilAdmissible f σ₀)
    {s : ℂ} (hs : |s.re - 1 / 2| < σ₀) :
    Integrable (fun u : ℝ => f u * cexp ((s - 1 / 2) * (u : ℂ))) := by
  obtain ⟨hm, C, hC, hbd⟩ := hf
  set α : ℝ := σ₀ - |s.re - 1 / 2|
  have hα : 0 < α := by linarith
  refine ((integrable_exp_neg_abs hα).const_mul C).mono' ?_ (Eventually.of_forall fun u => ?_)
  · exact hm.mul (by fun_prop : Continuous fun u : ℝ => cexp ((s - 1 / 2) * (u : ℂ))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_exp]
    have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by simp
    rw [hre]
    have h1 : (s.re - 1 / 2) * u ≤ |s.re - 1 / 2| * |u| := by
      calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
        _ = |s.re - 1 / 2| * |u| := abs_mul _ _
    calc ‖f u‖ * Real.exp ((s.re - 1 / 2) * u)
        ≤ (C * Real.exp (-σ₀ * |u|)) * Real.exp (|s.re - 1 / 2| * |u|) :=
          mul_le_mul (hbd u) (Real.exp_le_exp.mpr h1) (Real.exp_nonneg _) (by positivity)
      _ = C * (Real.exp (-σ₀ * |u|) * Real.exp (|s.re - 1 / 2| * |u|)) := by ring
      _ = C * Real.exp (-α * |u|) := by
          rw [← Real.exp_add]; congr 2; dsimp only [α]; ring

/-- **Exact Involution Transform Identity**:
`Φ_{f̃}(s) = conj (Φ_f(1 - conj s))`. -/
theorem weilBilateralTransform_involution (f : ℝ → ℂ) (s : ℂ) :
    weilBilateralTransform (weilInvolution f) s =
      starRingEnd ℂ (weilBilateralTransform f (1 - starRingEnd ℂ s)) := by
  unfold weilBilateralTransform weilInvolution
  rw [← Complex.conjCLE_apply, ← ContinuousLinearEquiv.integral_comp_comm Complex.conjCLE]
  have h1 := MeasureTheory.integral_neg_eq_self
    (fun u : ℝ => starRingEnd ℂ (f (-u)) * cexp ((s - 1 / 2) * (u : ℂ))) volume
  rw [← h1]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [neg_neg, Complex.conjCLE_apply, map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_sub, map_one, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_conj]
  push_cast; ring

/-- **Exact Convolution Transform Identity**:
for `WeilAdmissible f σ₀`, `WeilAdmissible g σ₀`, and `|Re(s) - 1/2| < σ₀`:
`Φ_{f * g}(s) = Φ_f(s) * Φ_g(s)`. -/
theorem weilBilateralTransform_conv {f g : ℝ → ℂ} {σ₀ : ℝ}
    (hf : WeilAdmissible f σ₀) (hg : WeilAdmissible g σ₀)
    {s : ℂ} (hs : |s.re - 1 / 2| < σ₀) :
    weilBilateralTransform (weilConv f g) s =
      weilBilateralTransform f s * weilBilateralTransform g s := by
  have hfi := integrable_weilBilateralTransform hf hs
  have hgi := integrable_weilBilateralTransform hg hs
  have hmeas_uv : AEStronglyMeasurable
      (fun p : ℝ × ℝ => f p.2 * g (p.1 - p.2) * cexp ((s - 1 / 2) * (p.1 : ℂ)))
      (volume.prod volume) := by
    have hf2 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (volume.prod volume) :=
      hf.1.comp_snd
    have hg12 : AEStronglyMeasurable (fun p : ℝ × ℝ => g (p.1 - p.2)) (volume.prod volume) :=
      hg.1.comp_quasiMeasurePreserving (MeasureTheory.quasiMeasurePreserving_sub volume volume)
    have hexp : AEStronglyMeasurable (fun p : ℝ × ℝ => cexp ((s - 1 / 2) * (p.1 : ℂ)))
        (volume.prod volume) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => cexp ((s - 1 / 2) * (p.1 : ℂ))).aestronglyMeasurable
    exact (hf2.mul hg12).mul hexp
  have hfac : ∀ u v : ℝ, f v * g (u - v) * cexp ((s - 1 / 2) * (u : ℂ)) =
      (f v * cexp ((s - 1 / 2) * (v : ℂ))) * (g (u - v) * cexp ((s - 1 / 2) * ((u - v : ℝ) : ℂ))) := by
    intro u v
    have hexp : cexp ((s - 1 / 2) * (v : ℂ)) * cexp ((s - 1 / 2) * ((u - v : ℝ) : ℂ)) =
        cexp ((s - 1 / 2) * (u : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc f v * g (u - v) * cexp ((s - 1 / 2) * (u : ℂ))
        = f v * g (u - v) * (cexp ((s - 1 / 2) * (v : ℂ)) * cexp ((s - 1 / 2) * ((u - v : ℝ) : ℂ))) := by
          rw [hexp]
      _ = _ := by ring
  have hprod_uv : Integrable (fun p : ℝ × ℝ =>
      f p.2 * g (p.1 - p.2) * cexp ((s - 1 / 2) * (p.1 : ℂ))) (volume.prod volume) := by
    rw [MeasureTheory.integrable_prod_iff' hmeas_uv]
    constructor
    · refine Eventually.of_forall fun v => ?_
      have h1 := (hgi.comp_sub_right v).const_mul (f v * cexp ((s - 1 / 2) * (v : ℂ)))
      exact h1.congr (Eventually.of_forall fun u => (hfac u v).symm)
    · have hnorm : (fun v : ℝ => ∫ u : ℝ, ‖f v * g (u - v) * cexp ((s - 1 / 2) * (u : ℂ))‖) =
          fun v : ℝ => ‖f v * cexp ((s - 1 / 2) * (v : ℂ))‖ *
            ∫ w : ℝ, ‖g w * cexp ((s - 1 / 2) * (w : ℂ))‖ := by
        funext v
        have hpt : (fun u : ℝ => ‖f v * g (u - v) * cexp ((s - 1 / 2) * (u : ℂ))‖) =
            fun u : ℝ => ‖f v * cexp ((s - 1 / 2) * (v : ℂ))‖ *
              ‖g (u - v) * cexp ((s - 1 / 2) * ((u - v : ℝ) : ℂ))‖ := by
          funext u; rw [hfac u v, norm_mul]
        rw [hpt, integral_const_mul,
          MeasureTheory.integral_sub_right_eq_self
            (fun w : ℝ => ‖g w * cexp ((s - 1 / 2) * (w : ℂ))‖) v]
      rw [hnorm]
      exact hfi.norm.mul_const _
  unfold weilBilateralTransform weilConv
  have hpull : ∀ u : ℝ, (∫ v : ℝ, f v * g (u - v)) * cexp ((s - 1 / 2) * (u : ℂ)) =
      ∫ v : ℝ, f v * g (u - v) * cexp ((s - 1 / 2) * (u : ℂ)) := fun u =>
    (integral_mul_const _ _).symm
  simp_rw [hpull]
  rw [MeasureTheory.integral_integral_swap hprod_uv]
  have hinner : ∀ v : ℝ, ∫ u : ℝ, f v * g (u - v) * cexp ((s - 1 / 2) * (u : ℂ)) =
      (f v * cexp ((s - 1 / 2) * (v : ℂ))) *
        ∫ w : ℝ, g w * cexp ((s - 1 / 2) * (w : ℂ)) := by
    intro v
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun w : ℝ => f v * g (w - v) * cexp ((s - 1 / 2) * (w : ℂ))) v, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [add_sub_cancel_right]
    have hexp : cexp ((s - 1 / 2) * ((w + v : ℝ) : ℂ)) =
        cexp ((s - 1 / 2) * (v : ℂ)) * cexp ((s - 1 / 2) * (w : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp]; ring
  simp_rw [hinner]
  rw [integral_mul_const]

/-- **Exact Self-Convolution Transform Formula**:
`Φ_{f * f̃}(s) = Φ_f(s) * conj (Φ_f(1 - conj s))`. -/
theorem weilBilateralTransform_selfConv {f : ℝ → ℂ} {σ₀ : ℝ}
    (hf : WeilAdmissible f σ₀) {s : ℂ} (hs : |s.re - 1 / 2| < σ₀) :
    weilBilateralTransform (weilConv f (weilInvolution f)) s =
      weilBilateralTransform f s * starRingEnd ℂ (weilBilateralTransform f (1 - starRingEnd ℂ s)) := by
  rw [weilBilateralTransform_conv hf (weilAdmissible_involution hf) hs,
    weilBilateralTransform_involution]

/-- **Exact Hermitian Positivity Identity on the Critical Line `Re(s) = 1/2`**:
for every `WeilAdmissible f σ₀` (`σ₀ > 0`) and every `t ∈ ℝ`,
`Φ_{f * f̃}(1/2 + i t) = ‖Φ_f(1/2 + i t)‖² ≥ 0` (real and non-negative!). -/
theorem weilBilateralTransform_selfConv_criticalLine {f : ℝ → ℂ} {σ₀ : ℝ}
    (hf : WeilAdmissible f σ₀) (hσ₀ : 0 < σ₀) (t : ℝ) :
    weilBilateralTransform (weilConv f (weilInvolution f)) (1 / 2 + I * (t : ℂ)) =
      ((‖weilBilateralTransform f (1 / 2 + I * (t : ℂ))‖ ^ 2 : ℝ) : ℂ) := by
  have hs : |(1 / 2 + I * (t : ℂ)).re - 1 / 2| < σ₀ := by simp [hσ₀]
  rw [weilBilateralTransform_selfConv hf hs]
  have hsym : 1 - starRingEnd ℂ (1 / 2 + I * (t : ℂ)) = 1 / 2 + I * (t : ℂ) := by
    apply Complex.ext
    · simp; ring
    · simp
  rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem weilBilateralTransform_selfConv_re_nonneg_of_re_eq_half {f : ℝ → ℂ} {σ₀ : ℝ}
    (hf : WeilAdmissible f σ₀) (hσ₀ : 0 < σ₀) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    0 ≤ (weilBilateralTransform (weilConv f (weilInvolution f)) ρ).re ∧
      (weilBilateralTransform (weilConv f (weilInvolution f)) ρ).im = 0 := by
  have hEq : ρ = 1 / 2 + I * (ρ.im : ℂ) := by
    apply Complex.ext
    · simp [hρ]
    · simp
  rw [hEq, weilBilateralTransform_selfConv_criticalLine hf hσ₀ ρ.im,
    Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨sq_nonneg _, rfl⟩

/-! ### Explicit Gaussian, Odd-Gaussian, and Phase-Shifted Gaussian Wave Packets -/

/-- Modulated Gaussian Weil test function `g_{a, γ}(u) = exp(-a u² - i γ u)`. -/
def weilGaussian (a γ : ℝ) (u : ℝ) : ℂ :=
  cexp (-(a : ℂ) * (u : ℂ) ^ 2 - I * (γ : ℂ) * (u : ℂ))

/-- Odd-modulated Gaussian Weil test function `f_{a, γ}(u) = u · exp(-a u² - i γ u)`. -/
def weilOddGaussian (a γ : ℝ) (u : ℝ) : ℂ :=
  (u : ℂ) * weilGaussian a γ u

/-- Phase-shifted Gaussian wave packet `h_{a, γ, L, θ}(u) = g(u - L) - e^{i θ} g(u + L)`. -/
def weilPhasePacket (a γ L θ : ℝ) (u : ℝ) : ℂ :=
  weilGaussian a γ (u - L) - cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)

theorem weilAdmissible_weilGaussian {a : ℝ} (ha : 0 < a) (γ σ₀ : ℝ) :
    WeilAdmissible (weilGaussian a γ) σ₀ := by
  refine ⟨(by unfold weilGaussian; fun_prop : Continuous (weilGaussian a γ)).aestronglyMeasurable,
    Real.exp (σ₀ ^ 2 / (4 * a)), Real.exp_nonneg _, fun u => ?_⟩
  unfold weilGaussian
  rw [Complex.norm_exp]
  have hre : (-(a : ℂ) * (u : ℂ) ^ 2 - I * (γ : ℂ) * (u : ℂ)).re = -a * u ^ 2 := by
    simp [sq]
  rw [hre, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hsq : 0 ≤ a * (|u| - σ₀ / (2 * a)) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have habs : |u| ^ 2 = u ^ 2 := sq_abs u
  have hexp : a * (|u| - σ₀ / (2 * a)) ^ 2 = a * u ^ 2 - σ₀ * |u| + σ₀ ^ 2 / (4 * a) := by
    rw [← habs]; field_simp [ha.ne']; ring
  linarith

theorem weilAdmissible_weilOddGaussian {a : ℝ} (ha : 0 < a) (γ σ₀ : ℝ) :
    WeilAdmissible (weilOddGaussian a γ) σ₀ := by
  refine ⟨(by unfold weilOddGaussian weilGaussian; fun_prop : Continuous (weilOddGaussian a γ)).aestronglyMeasurable,
    Real.exp ((|σ₀| + 1) ^ 2 / (4 * a)), Real.exp_nonneg _, fun u => ?_⟩
  unfold weilOddGaussian weilGaussian
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hre : (-(a : ℂ) * (u : ℂ) ^ 2 - I * (γ : ℂ) * (u : ℂ)).re = -a * u ^ 2 := by simp [sq]
  rw [hre]
  have hu_le : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
  calc |u| * Real.exp (-a * u ^ 2)
      ≤ Real.exp |u| * Real.exp (-a * u ^ 2) :=
        mul_le_mul_of_nonneg_right hu_le (Real.exp_nonneg _)
    _ = Real.exp (-a * u ^ 2 + |u|) := by rw [← Real.exp_add, add_comm]
    _ ≤ Real.exp ((|σ₀| + 1) ^ 2 / (4 * a) + -σ₀ * |u|) := by
        refine Real.exp_le_exp.mpr ?_
        have hsq : 0 ≤ a * (|u| - (|σ₀| + 1) / (2 * a)) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
        have habs : |u| ^ 2 = u ^ 2 := sq_abs u
        have hexp : a * (|u| - (|σ₀| + 1) / (2 * a)) ^ 2 =
            a * u ^ 2 - (|σ₀| + 1) * |u| + (|σ₀| + 1) ^ 2 / (4 * a) := by
          rw [← habs]; field_simp [ha.ne']; ring
        have hσ : σ₀ * |u| ≤ |σ₀| * |u| := mul_le_mul_of_nonneg_right (le_abs_self σ₀) (abs_nonneg u)
        linarith
    _ = Real.exp ((|σ₀| + 1) ^ 2 / (4 * a)) * Real.exp (-σ₀ * |u|) := Real.exp_add _ _

theorem weilAdmissible_weilPhasePacket {a : ℝ} (ha : 0 < a) (γ L θ σ₀ : ℝ) :
    WeilAdmissible (weilPhasePacket a γ L θ) σ₀ := by
  obtain ⟨_, C, hC, hbd⟩ := weilAdmissible_weilGaussian ha γ (max σ₀ 0)
  set M : ℝ := 2 * C * Real.exp (max σ₀ 0 * |L|)
  refine ⟨(by unfold weilPhasePacket weilGaussian; fun_prop : Continuous (weilPhasePacket a γ L θ)).aestronglyMeasurable,
    M, by positivity, fun u => ?_⟩
  unfold weilPhasePacket
  have htri1 : |u| - |L| ≤ |u - L| := by
    have := abs_sub_abs_le_abs_sub u L; linarith
  have htri2 : |u| - |L| ≤ |u + L| := by
    have := abs_sub_abs_le_abs_sub u (-L)
    simpa [abs_neg, sub_neg_eq_add] using this
  have hsm : σ₀ ≤ max σ₀ 0 := le_max_left _ _
  have hm0 : 0 ≤ max σ₀ 0 := le_max_right _ _
  have hb1 : ‖weilGaussian a γ (u - L)‖ ≤ C * Real.exp (max σ₀ 0 * |L|) * Real.exp (-σ₀ * |u|) := by
    calc ‖weilGaussian a γ (u - L)‖ ≤ C * Real.exp (-(max σ₀ 0) * |u - L|) := hbd (u - L)
      _ ≤ C * Real.exp (-(max σ₀ 0) * (|u| - |L|)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
      _ = C * Real.exp (max σ₀ 0 * |L|) * Real.exp (-(max σ₀ 0) * |u|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ C * Real.exp (max σ₀ 0 * |L|) * Real.exp (-σ₀ * |u|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])) (by positivity)
  have hb2 : ‖cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)‖ ≤
      C * Real.exp (max σ₀ 0 * |L|) * Real.exp (-σ₀ * |u|) := by
    rw [norm_mul, show I * (θ : ℂ) = (θ : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I, one_mul]
    calc ‖weilGaussian a γ (u + L)‖ ≤ C * Real.exp (-(max σ₀ 0) * |u + L|) := hbd (u + L)
      _ ≤ C * Real.exp (-(max σ₀ 0) * (|u| - |L|)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
      _ = C * Real.exp (max σ₀ 0 * |L|) * Real.exp (-(max σ₀ 0) * |u|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ C * Real.exp (max σ₀ 0 * |L|) * Real.exp (-σ₀ * |u|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])) (by positivity)
  calc ‖weilGaussian a γ (u - L) - cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)‖
      ≤ ‖weilGaussian a γ (u - L)‖ + ‖cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)‖ := norm_sub_le _ _
    _ ≤ M * Real.exp (-σ₀ * |u|) := by dsimp only [M]; linarith

/-- Exact bilateral Laplace/Mellin transform of `weilGaussian a γ`. -/
theorem weilBilateralTransform_weilGaussian {a : ℝ} (ha : 0 < a) (γ : ℝ) (s : ℂ) :
    weilBilateralTransform (weilGaussian a γ) s =
      ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) *
        cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ))) := by
  unfold weilBilateralTransform weilGaussian
  have hEq : (fun u : ℝ =>
      cexp (-(a : ℂ) * (u : ℂ) ^ 2 - I * (γ : ℂ) * (u : ℂ)) * cexp ((s - 1 / 2) * (u : ℂ))) =
      fun u : ℝ => cexp (-(a : ℂ) * (u : ℂ) ^ 2 + (s - 1 / 2 - I * (γ : ℂ)) * (u : ℂ) + 0) := by
    funext u
    rw [← Complex.exp_add]
    congr 1; ring
  rw [hEq, integral_cexp_quadratic (by simp [ha] : (-(a : ℂ)).re < 0)]
  have hsqrt : ((Real.pi : ℂ) / -(-(a : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) := by
    rw [neg_neg, ← Complex.ofReal_div, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [hsqrt]
  congr 2
  ring

/-- Exact self-convolution transform of `weilGaussian a γ`:
`Φ_{g * g̃}(s) = (π / a) * exp((s - 1/2 - i γ)² / (2 a))`. -/
theorem weilBilateralTransform_selfConv_weilGaussian {a : ℝ} (ha : 0 < a) (γ : ℝ) (s : ℂ) :
    weilBilateralTransform (weilConv (weilGaussian a γ) (weilInvolution (weilGaussian a γ))) s =
      ((Real.pi / a : ℝ) : ℂ) * cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (2 * (a : ℂ))) := by
  have hσ : |s.re - 1 / 2| < |s.re - 1 / 2| + 1 := by linarith
  rw [weilBilateralTransform_selfConv (weilAdmissible_weilGaussian ha γ (|s.re - 1 / 2| + 1)) hσ,
    weilBilateralTransform_weilGaussian ha γ s,
    weilBilateralTransform_weilGaussian ha γ (1 - starRingEnd ℂ s)]
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have hsq : ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) =
      ((Real.pi / a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  have hconj : starRingEnd ℂ ((1 - starRingEnd ℂ s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ))) =
      (s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ)) := by
    simp only [map_div₀, map_pow, map_mul, map_sub, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [hconj]
  calc ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ))) *
        (((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ))))
      = (((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * ((Real.sqrt (Real.pi / a) : ℝ) : ℂ)) *
          (cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ))) *
           cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ)))) := by ring
    _ = ((Real.pi / a : ℝ) : ℂ) * cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (2 * (a : ℂ))) := by
        rw [hsq, ← Complex.exp_add]
        congr 2; field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast ha.ne']; ring

/-- Exact bilateral Laplace/Mellin transform of `weilOddGaussian a γ`:
`Φ_{u g}(s) = ((s - 1/2 - i γ) / (2 a)) * Φ_g(s)`. -/
theorem weilBilateralTransform_weilOddGaussian {a : ℝ} (ha : 0 < a) (γ : ℝ) (s : ℂ) :
    weilBilateralTransform (weilOddGaussian a γ) s =
      ((s - 1 / 2 - I * (γ : ℂ)) / (2 * (a : ℂ))) *
        ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) *
        cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ))) := by
  set w : ℂ := s - 1 / 2 - I * (γ : ℂ) with hw_def
  let G : ℝ → ℂ := fun u => cexp (-(a : ℂ) * (u : ℂ) ^ 2 + w * (u : ℂ))
  let G' : ℝ → ℂ := fun u => (-2 * (a : ℂ) * (u : ℂ) + w) * G u
  have hG_deriv : ∀ u : ℝ, HasDerivAt G (G' u) u := fun u => by
    have h1 : HasDerivAt (fun t : ℝ => -(a : ℂ) * (t : ℂ) ^ 2 + w * (t : ℂ))
        (-2 * (a : ℂ) * (u : ℂ) + w) u := by
      have hu : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      have hsq : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (u : ℂ)) u := by
        refine ((hu.mul hu).congr_of_eventuallyEq (Eventually.of_forall fun t => by simp [sq])).congr_deriv ?_
        ring
      have h2 := (hsq.const_mul (-(a : ℂ))).add (hu.const_mul w)
      exact h2.congr_deriv (by ring)
    exact h1.cexp.congr_deriv (by dsimp only [G, G']; ring)
  have hG_norm : ∀ u : ℝ, ‖G u‖ = Real.exp (-a * u ^ 2 + w.re * u) := fun u => by
    dsimp only [G]
    rw [Complex.norm_exp]
    congr 1; simp [sq]
  have hG_atTop : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => -a * u ^ 2 + w.re * u) atTop atBot := by
      have hpos : Tendsto (fun u : ℝ => a * u ^ 2 - w.re * u) atTop atTop := by
        refine tendsto_atTop_mono' atTop ?_ tendsto_id
        filter_upwards [eventually_ge_atTop (max 0 ((|w.re| + 1) / a))] with u hu
        have hu0 : 0 ≤ u := (le_max_left _ _).trans hu
        have hu1 : (|w.re| + 1) / a ≤ u := (le_max_right _ _).trans hu
        have hau : |w.re| + 1 ≤ a * u := by
          have := mul_le_mul_of_nonneg_left hu1 ha.le
          rwa [mul_div_cancel₀ _ ha.ne'] at this
        have hwr : w.re ≤ |w.re| := le_abs_self w.re
        change u ≤ a * u ^ 2 - w.re * u
        nlinarith
      exact (tendsto_neg_atTop_atBot.comp hpos).congr fun u => by dsimp only [Function.comp_apply]; ring
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      ((Real.tendsto_exp_atBot.comp h1).congr fun u => (hG_norm u).symm)
  have hG_atBot : Tendsto G atBot (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => -a * u ^ 2 + w.re * u) atBot atBot := by
      have hpos : Tendsto (fun u : ℝ => a * u ^ 2 - w.re * u) atBot atTop := by
        refine tendsto_atTop_mono' atBot ?_ tendsto_neg_atBot_atTop
        filter_upwards [eventually_le_atBot (-(max 0 ((|w.re| + 1) / a)))] with u hu
        have hu0 : 0 ≤ -u := by linarith [le_max_left (0 : ℝ) ((|w.re| + 1) / a)]
        have hu1 : (|w.re| + 1) / a ≤ -u := by linarith [le_max_right (0 : ℝ) ((|w.re| + 1) / a)]
        have hau : |w.re| + 1 ≤ a * (-u) := by
          have := mul_le_mul_of_nonneg_left hu1 ha.le
          rwa [mul_div_cancel₀ _ ha.ne'] at this
        have hwr : -w.re ≤ |w.re| := neg_le_abs w.re
        nlinarith
      exact (tendsto_neg_atTop_atBot.comp hpos).congr fun u => by dsimp only [Function.comp_apply]; ring
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      ((Real.tendsto_exp_atBot.comp h1).congr fun u => (hG_norm u).symm)
  have hG_eq : ∀ u : ℝ, G u = weilGaussian a γ u * cexp ((s - 1 / 2) * (u : ℂ)) := fun u => by
    dsimp only [G, weilGaussian]; rw [← Complex.exp_add]; congr 1; rw [hw_def]; ring
  have huG_eq : ∀ u : ℝ, (u : ℂ) * G u = weilOddGaussian a γ u * cexp ((s - 1 / 2) * (u : ℂ)) := fun u => by
    unfold weilOddGaussian; rw [mul_assoc, hG_eq u]
  have hσ : |s.re - 1 / 2| < |s.re - 1 / 2| + 1 := by linarith
  have hG_int : Integrable G :=
    (integrable_weilBilateralTransform (weilAdmissible_weilGaussian ha γ (|s.re - 1 / 2| + 1)) hσ).congr
      (Eventually.of_forall fun u => (hG_eq u).symm)
  have huG_int : Integrable (fun u : ℝ => (u : ℂ) * G u) :=
    (integrable_weilBilateralTransform (weilAdmissible_weilOddGaussian ha γ (|s.re - 1 / 2| + 1)) hσ).congr
      (Eventually.of_forall fun u => (huG_eq u).symm)
  have hG'_int : Integrable G' := by
    have hEq : G' = fun u : ℝ => (-2 * (a : ℂ)) * ((u : ℂ) * G u) + w * G u := by
      funext u; dsimp only [G']; ring
    rw [hEq]
    exact (huG_int.const_mul _).add (hG_int.const_mul _)
  have hint_zero : ∫ u : ℝ, G' u = 0 := by
    have h1 := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
      (fun u _ => hG_deriv u) hG'_int.integrableOn hG_atTop
    have h2 := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
      (fun u _ => hG_deriv u) hG'_int.integrableOn hG_atBot
    have hsplit : (∫ u in Iic (0 : ℝ), G' u) + (∫ u in Ioi (0 : ℝ), G' u) = ∫ u : ℝ, G' u := by
      rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hG'_int.integrableOn hG'_int.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
    rw [← hsplit, h1, h2]; ring
  have hlin : (-2 * (a : ℂ)) * (∫ u : ℝ, (u : ℂ) * G u) + w * (∫ u : ℝ, G u) = 0 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (huG_int.const_mul _) (hG_int.const_mul _)]
    have hEq : (fun u : ℝ => (-2 * (a : ℂ)) * ((u : ℂ) * G u) + w * G u) = G' := by
      funext u; dsimp only [G']; ring
    rw [hEq]; exact hint_zero
  have h2a : (2 * (a : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast ha.ne')
  have hsolve : ∫ u : ℝ, (u : ℂ) * G u = (w / (2 * (a : ℂ))) * ∫ u : ℝ, G u := by
    rw [div_mul_eq_mul_div, eq_div_iff h2a]
    linear_combination -hlin
  have hLHS : weilBilateralTransform (weilOddGaussian a γ) s = ∫ u : ℝ, (u : ℂ) * G u :=
    integral_congr_ae (Eventually.of_forall fun u => (huG_eq u).symm)
  have hRHS : ∫ u : ℝ, G u = weilBilateralTransform (weilGaussian a γ) s :=
    integral_congr_ae (Eventually.of_forall hG_eq)
  rw [hLHS, hsolve, hRHS, weilBilateralTransform_weilGaussian ha γ s, mul_assoc]

/-- **Exact Self-Convolution Transform of `weilOddGaussian a γ`**:
`Φ_{f * f̃}(s) = -((s - 1/2 - i γ)² / (4 a²)) * (π / a) * exp((s - 1/2 - i γ)² / (2 a))`. -/
theorem weilBilateralTransform_selfConv_weilOddGaussian {a : ℝ} (ha : 0 < a) (γ : ℝ) (s : ℂ) :
    weilBilateralTransform
        (weilConv (weilOddGaussian a γ) (weilInvolution (weilOddGaussian a γ))) s =
      -((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ) ^ 2)) *
        ((Real.pi / a : ℝ) : ℂ) *
        cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (2 * (a : ℂ))) := by
  have hσ : |s.re - 1 / 2| < |s.re - 1 / 2| + 1 := by linarith
  rw [weilBilateralTransform_selfConv (weilAdmissible_weilOddGaussian ha γ (|s.re - 1 / 2| + 1)) hσ,
    weilBilateralTransform_weilOddGaussian ha γ s,
    weilBilateralTransform_weilOddGaussian ha γ (1 - starRingEnd ℂ s)]
  have hconj_lin : starRingEnd ℂ ((1 - starRingEnd ℂ s - 1 / 2 - I * (γ : ℂ)) / (2 * (a : ℂ))) =
      -((s - 1 / 2 - I * (γ : ℂ)) / (2 * (a : ℂ))) := by
    simp only [map_div₀, map_sub, map_one, map_ofNat, map_mul, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hconj_exp : starRingEnd ℂ (cexp ((1 - starRingEnd ℂ s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ)))) =
      cexp ((s - 1 / 2 - I * (γ : ℂ)) ^ 2 / (4 * (a : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_div₀, map_pow, map_sub, map_one, map_ofNat, map_mul, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hsq : ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) =
      ((Real.pi / a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  rw [map_mul, map_mul, hconj_lin, Complex.conj_ofReal, hconj_exp]
  set w : ℂ := s - 1 / 2 - I * (γ : ℂ)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  calc w / (2 * (a : ℂ)) * ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * cexp (w ^ 2 / (4 * (a : ℂ))) *
        (-(w / (2 * (a : ℂ))) * ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * cexp (w ^ 2 / (4 * (a : ℂ))))
      = (w / (2 * (a : ℂ)) * -(w / (2 * (a : ℂ)))) *
        (((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * ((Real.sqrt (Real.pi / a) : ℝ) : ℂ)) *
        (cexp (w ^ 2 / (4 * (a : ℂ))) * cexp (w ^ 2 / (4 * (a : ℂ)))) := by ring
    _ = -(w ^ 2 / (4 * (a : ℂ) ^ 2)) * ((Real.pi / a : ℝ) : ℂ) * cexp (w ^ 2 / (2 * (a : ℂ))) := by
        rw [hsq, ← Complex.exp_add]
        congr 2
        · field_simp [haC]; ring
        · field_simp [haC]; ring

/-- **Strict Off-Line Negativity of `weilOddGaussian` at Any Off-Line Point `ρ₀` (`Re(ρ₀) ≠ 1/2`)**:
for every `a > 0` and every `ρ₀` with `ρ₀.re ≠ 1/2`,
`Re(Φ_{f_{a, ρ₀.im} * f̃_{a, ρ₀.im}}(ρ₀)) < 0`. -/
theorem weilBilateralTransform_selfConv_weilOddGaussian_neg_at_offLine
    {a : ℝ} (ha : 0 < a) {ρ₀ : ℂ} (hoff : ρ₀.re ≠ 1 / 2) :
    (weilBilateralTransform
      (weilConv (weilOddGaussian a ρ₀.im) (weilInvolution (weilOddGaussian a ρ₀.im))) ρ₀).re < 0 := by
  rw [weilBilateralTransform_selfConv_weilOddGaussian ha ρ₀.im ρ₀]
  have hw : ρ₀ - 1 / 2 - I * (ρ₀.im : ℂ) = ((ρ₀.re - 1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hw]
  set x : ℝ := ρ₀.re - 1 / 2
  have hx : x ≠ 0 := sub_ne_zero.mpr hoff
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hval : -(((x : ℂ) ^ 2) / (4 * (a : ℂ) ^ 2)) * ((Real.pi / a : ℝ) : ℂ) *
      cexp (((x : ℂ) ^ 2) / (2 * (a : ℂ))) =
      ((-(x ^ 2 / (4 * a ^ 2)) * (Real.pi / a) * Real.exp (x ^ 2 / (2 * a)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast; ring
  rw [hval, Complex.ofReal_re]
  have hpos : 0 < (x ^ 2 / (4 * a ^ 2)) * (Real.pi / a) * Real.exp (x ^ 2 / (2 * a)) := by
    positivity
  linarith

/-- Exact bilateral Laplace/Mellin transform of the phase-shifted Gaussian wave packet
`weilPhasePacket a γ L θ u = g(u - L) - e^{i θ} g(u + L)`. -/
theorem weilBilateralTransform_weilPhasePacket {a : ℝ} (ha : 0 < a) (γ L θ : ℝ) (s : ℂ) :
    weilBilateralTransform (weilPhasePacket a γ L θ) s =
      (cexp ((L : ℂ) * (s - 1 / 2)) - cexp (I * (θ : ℂ) - (L : ℂ) * (s - 1 / 2))) *
        weilBilateralTransform (weilGaussian a γ) s := by
  have hσ : |s.re - 1 / 2| < |s.re - 1 / 2| + 1 := by linarith
  have hgi := integrable_weilBilateralTransform (weilAdmissible_weilGaussian ha γ (|s.re - 1 / 2| + 1)) hσ
  have h1 : ∫ u : ℝ, weilGaussian a γ (u - L) * cexp ((s - 1 / 2) * (u : ℂ)) =
      cexp ((L : ℂ) * (s - 1 / 2)) * weilBilateralTransform (weilGaussian a γ) s := by
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun u : ℝ => weilGaussian a γ (u - L) * cexp ((s - 1 / 2) * (u : ℂ))) L]
    unfold weilBilateralTransform
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    simp only [add_sub_cancel_right]
    have hexp : cexp ((s - 1 / 2) * ((u + L : ℝ) : ℂ)) =
        cexp ((L : ℂ) * (s - 1 / 2)) * cexp ((s - 1 / 2) * (u : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp]; ring
  have h2 : ∫ u : ℝ, (cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)) * cexp ((s - 1 / 2) * (u : ℂ)) =
      cexp (I * (θ : ℂ) - (L : ℂ) * (s - 1 / 2)) * weilBilateralTransform (weilGaussian a γ) s := by
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun u : ℝ => (cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)) * cexp ((s - 1 / 2) * (u : ℂ))) (-L)]
    unfold weilBilateralTransform
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    simp only [neg_add_cancel_right]
    have hexp : cexp (I * (θ : ℂ)) * cexp ((s - 1 / 2) * ((u + -L : ℝ) : ℂ)) =
        cexp (I * (θ : ℂ) - (L : ℂ) * (s - 1 / 2)) * cexp ((s - 1 / 2) * (u : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    calc cexp (I * (θ : ℂ)) * weilGaussian a γ u * cexp ((s - 1 / 2) * ((u + -L : ℝ) : ℂ))
        = weilGaussian a γ u * (cexp (I * (θ : ℂ)) * cexp ((s - 1 / 2) * ((u + -L : ℝ) : ℂ))) := by ring
      _ = _ := by rw [hexp]; ring
  have hi1 : Integrable (fun u : ℝ => weilGaussian a γ (u - L) * cexp ((s - 1 / 2) * (u : ℂ))) := by
    have hcomp := (hgi.const_mul (cexp ((L : ℂ) * (s - 1 / 2)))).comp_sub_right L
    refine hcomp.congr (Eventually.of_forall fun u => ?_)
    dsimp only [Function.comp_apply]
    have hexp : cexp ((L : ℂ) * (s - 1 / 2)) * cexp ((s - 1 / 2) * ((u - L : ℝ) : ℂ)) =
        cexp ((s - 1 / 2) * (u : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc cexp ((L : ℂ) * (s - 1 / 2)) * (weilGaussian a γ (u - L) * cexp ((s - 1 / 2) * ((u - L : ℝ) : ℂ)))
        = weilGaussian a γ (u - L) * (cexp ((L : ℂ) * (s - 1 / 2)) * cexp ((s - 1 / 2) * ((u - L : ℝ) : ℂ))) := by ring
      _ = _ := by rw [hexp]
  have hi2 : Integrable (fun u : ℝ =>
      (cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)) * cexp ((s - 1 / 2) * (u : ℂ))) := by
    have hcomp := (hgi.const_mul (cexp (I * (θ : ℂ) - (L : ℂ) * (s - 1 / 2)))).comp_add_right L
    refine hcomp.congr (Eventually.of_forall fun u => ?_)
    dsimp only [Function.comp_apply]
    have hexp : cexp (I * (θ : ℂ) - (L : ℂ) * (s - 1 / 2)) * cexp ((s - 1 / 2) * ((u + L : ℝ) : ℂ)) =
        cexp (I * (θ : ℂ)) * cexp ((s - 1 / 2) * (u : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    calc cexp (I * (θ : ℂ) - (L : ℂ) * (s - 1 / 2)) *
            (weilGaussian a γ (u + L) * cexp ((s - 1 / 2) * ((u + L : ℝ) : ℂ)))
        = weilGaussian a γ (u + L) *
            (cexp (I * (θ : ℂ) - (L : ℂ) * (s - 1 / 2)) * cexp ((s - 1 / 2) * ((u + L : ℝ) : ℂ))) := by ring
      _ = _ := by rw [hexp]; ring
  change ∫ u : ℝ, (weilGaussian a γ (u - L) - cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)) *
      cexp ((s - 1 / 2) * (u : ℂ)) = _
  have hsub_fn : (fun u : ℝ =>
      (weilGaussian a γ (u - L) - cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)) *
        cexp ((s - 1 / 2) * (u : ℂ))) =
      fun u : ℝ =>
        weilGaussian a γ (u - L) * cexp ((s - 1 / 2) * (u : ℂ)) -
        (cexp (I * (θ : ℂ)) * weilGaussian a γ (u + L)) * cexp ((s - 1 / 2) * (u : ℂ)) := by
    funext u; ring
  rw [hsub_fn, integral_sub hi1 hi2, h1, h2]
  ring

/-- **Strict Off-Line Negativity of the Phase-Shifted Gaussian Wave Packet**:
for any `a > 0`, `L > 0`, and any off-line point `ρ₀` (`ρ₀.re ≠ 1/2`), choosing phase
`θ = 2 * L * ρ₀.im` yields `Re(Φ_{h * h̃}(ρ₀)) < 0` (via `2 - 2 cosh(2 L (ρ₀.re - 1/2)) < 0`). -/
theorem weilBilateralTransform_selfConv_weilPhasePacket_neg_at_offLine
    {a L : ℝ} (ha : 0 < a) (hL : 0 < L) {ρ₀ : ℂ} (hoff : ρ₀.re ≠ 1 / 2) :
    (weilBilateralTransform
      (weilConv (weilPhasePacket a ρ₀.im L (2 * L * ρ₀.im))
        (weilInvolution (weilPhasePacket a ρ₀.im L (2 * L * ρ₀.im)))) ρ₀).re < 0 := by
  have hσ : |ρ₀.re - 1 / 2| < |ρ₀.re - 1 / 2| + 1 := by linarith
  set θ : ℝ := 2 * L * ρ₀.im
  rw [weilBilateralTransform_selfConv (weilAdmissible_weilPhasePacket ha ρ₀.im L θ (|ρ₀.re - 1 / 2| + 1)) hσ,
    weilBilateralTransform_weilPhasePacket ha ρ₀.im L θ ρ₀,
    weilBilateralTransform_weilPhasePacket ha ρ₀.im L θ (1 - starRingEnd ℂ ρ₀)]
  rw [map_mul]
  have hcomb :
      (cexp ((L : ℂ) * (ρ₀ - 1 / 2)) - cexp (I * (θ : ℂ) - (L : ℂ) * (ρ₀ - 1 / 2))) *
        weilBilateralTransform (weilGaussian a ρ₀.im) ρ₀ *
        (starRingEnd ℂ (cexp ((L : ℂ) * (1 - starRingEnd ℂ ρ₀ - 1 / 2)) -
          cexp (I * (θ : ℂ) - (L : ℂ) * (1 - starRingEnd ℂ ρ₀ - 1 / 2))) *
        starRingEnd ℂ (weilBilateralTransform (weilGaussian a ρ₀.im) (1 - starRingEnd ℂ ρ₀))) =
      ((cexp ((L : ℂ) * (ρ₀ - 1 / 2)) - cexp (I * (θ : ℂ) - (L : ℂ) * (ρ₀ - 1 / 2))) *
        starRingEnd ℂ (cexp ((L : ℂ) * (1 - starRingEnd ℂ ρ₀ - 1 / 2)) -
          cexp (I * (θ : ℂ) - (L : ℂ) * (1 - starRingEnd ℂ ρ₀ - 1 / 2)))) *
      (weilBilateralTransform (weilGaussian a ρ₀.im) ρ₀ *
        starRingEnd ℂ (weilBilateralTransform (weilGaussian a ρ₀.im) (1 - starRingEnd ℂ ρ₀))) := by ring
  rw [hcomb, ← weilBilateralTransform_selfConv (weilAdmissible_weilGaussian ha ρ₀.im (|ρ₀.re - 1 / 2| + 1)) hσ,
    weilBilateralTransform_selfConv_weilGaussian ha ρ₀.im ρ₀]
  set x : ℝ := ρ₀.re - 1 / 2
  have hx : x ≠ 0 := sub_ne_zero.mpr hoff
  have hw : ρ₀ - 1 / 2 - I * (ρ₀.im : ℂ) = (x : ℂ) := by apply Complex.ext <;> simp [x]
  rw [hw]
  have hfac :
      (cexp ((L : ℂ) * (ρ₀ - 1 / 2)) - cexp (I * (θ : ℂ) - (L : ℂ) * (ρ₀ - 1 / 2))) *
        starRingEnd ℂ (cexp ((L : ℂ) * (1 - starRingEnd ℂ ρ₀ - 1 / 2)) -
          cexp (I * (θ : ℂ) - (L : ℂ) * (1 - starRingEnd ℂ ρ₀ - 1 / 2))) =
      ((2 - Real.exp (2 * L * x) - Real.exp (-(2 * L * x)) : ℝ) : ℂ) := by
    rw [map_sub, ← Complex.exp_conj, ← Complex.exp_conj]
    have hc1 : starRingEnd ℂ ((L : ℂ) * (1 - starRingEnd ℂ ρ₀ - 1 / 2)) =
        -(L : ℂ) * (ρ₀ - 1 / 2) := by
      rw [map_mul, Complex.conj_ofReal, map_sub, map_sub, map_one, Complex.conj_conj,
        map_div₀, map_one, map_ofNat]; ring
    have hc2 : starRingEnd ℂ (I * (θ : ℂ) - (L : ℂ) * (1 - starRingEnd ℂ ρ₀ - 1 / 2)) =
        -I * (θ : ℂ) + (L : ℂ) * (ρ₀ - 1 / 2) := by
      rw [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, hc1]; ring
    rw [hc1, hc2]
    have hρ : ρ₀ - 1 / 2 = (x : ℂ) + I * (ρ₀.im : ℂ) := by apply Complex.ext <;> simp [x]
    rw [mul_sub, sub_mul, sub_mul, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
    have e1 : (L : ℂ) * (ρ₀ - 1 / 2) + -(L : ℂ) * (ρ₀ - 1 / 2) = 0 := by ring
    have e2 : (L : ℂ) * (ρ₀ - 1 / 2) + (-I * (θ : ℂ) + (L : ℂ) * (ρ₀ - 1 / 2)) =
        ((2 * L * x : ℝ) : ℂ) := by rw [hρ]; push_cast [θ]; ring
    have e3 : (I * (θ : ℂ) - (L : ℂ) * (ρ₀ - 1 / 2)) + -(L : ℂ) * (ρ₀ - 1 / 2) =
        ((-(2 * L * x) : ℝ) : ℂ) := by rw [hρ]; push_cast [θ]; ring
    have e4 : (I * (θ : ℂ) - (L : ℂ) * (ρ₀ - 1 / 2)) + (-I * (θ : ℂ) + (L : ℂ) * (ρ₀ - 1 / 2)) = 0 := by
      ring
    rw [e1, e2, e3, e4, Complex.exp_zero, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    push_cast; ring
  rw [hfac]
  have hval : ((2 - Real.exp (2 * L * x) - Real.exp (-(2 * L * x)) : ℝ) : ℂ) *
      (((Real.pi / a : ℝ) : ℂ) * cexp ((x : ℂ) ^ 2 / (2 * (a : ℂ)))) =
      (((2 - Real.exp (2 * L * x) - Real.exp (-(2 * L * x))) *
        ((Real.pi / a) * Real.exp (x ^ 2 / (2 * a))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast; ring
  rw [hval, Complex.ofReal_re]
  have hneg : 2 - Real.exp (2 * L * x) - Real.exp (-(2 * L * x)) < 0 := by
    have hne : Real.exp (2 * L * x) ≠ 1 := by
      intro h
      have h0 : 2 * L * x = 0 := Real.exp_injective (by simpa [Real.exp_zero] using h)
      exact hx (by nlinarith)
    have hpos : 0 < Real.exp (2 * L * x) := Real.exp_pos _
    have hsq : 0 < (Real.exp (2 * L * x) - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    rw [Real.exp_neg]
    have hdiv := div_pos hsq hpos
    have hid : (Real.exp (2 * L * x) - 1) ^ 2 / Real.exp (2 * L * x) =
        Real.exp (2 * L * x) + (Real.exp (2 * L * x))⁻¹ - 2 := by
      field_simp [hpos.ne']; ring
    linarith
  have hpos : 0 < (Real.pi / a) * Real.exp (x ^ 2 / (2 * a)) := by positivity
  nlinarith

/-! ### Asymptotic Trigonometric Negativity Lemma (for Full Infinite Zero Spectra) -/

private lemma abs_integral_cos_mul_le {ω a b : ℝ} (hω : ω ≠ 0) :
    |∫ t in a..b, Real.cos (ω * t)| ≤ 2 / |ω| := by
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => Real.sin (ω * u) / ω) (Real.cos (ω * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => ω * u) ω t := by simpa using (hasDerivAt_id t).const_mul ω
    refine (h1.sin.div_const ω).congr_deriv ?_
    field_simp [hω]
  have hc : Continuous (fun t : ℝ => Real.cos (ω * t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable a b),
    ← sub_div, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg ω)
  calc |Real.sin (ω * b) - Real.sin (ω * a)|
      ≤ |Real.sin (ω * b)| + |Real.sin (ω * a)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
    _ = 2 := by norm_num

private lemma abs_integral_sin_mul_le {ω a b : ℝ} (hω : ω ≠ 0) :
    |∫ t in a..b, Real.sin (ω * t)| ≤ 2 / |ω| := by
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -(Real.cos (ω * u) / ω)) (Real.sin (ω * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => ω * u) ω t := by simpa using (hasDerivAt_id t).const_mul ω
    refine (h1.cos.div_const ω).neg.congr_deriv ?_
    field_simp [hω]
  have hc : Continuous (fun t : ℝ => Real.sin (ω * t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable a b),
    neg_sub_neg, ← sub_div, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg ω)
  calc |Real.cos (ω * a) - Real.cos (ω * b)|
      ≤ |Real.cos (ω * a)| + |Real.cos (ω * b)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
    _ = 2 := by norm_num

private lemma integral_cos_mul_cos_bound {ω₁ ω₂ a b : ℝ} (h1 : 0 < ω₁) (h2 : 0 < ω₂) :
    (ω₁ = ω₂ → |∫ t in a..b, Real.cos (ω₁ * t) * Real.cos (ω₂ * t) - (1 / 2)| ≤ 1 / (2 * ω₁)) ∧
    (ω₁ ≠ ω₂ → |∫ t in a..b, Real.cos (ω₁ * t) * Real.cos (ω₂ * t)| ≤
      1 / |ω₁ - ω₂| + 1 / (ω₁ + ω₂)) := by
  have hpt : ∀ t : ℝ, Real.cos (ω₁ * t) * Real.cos (ω₂ * t) =
      (Real.cos ((ω₁ - ω₂) * t) + Real.cos ((ω₁ + ω₂) * t)) / 2 := fun t => by
    have e1 : (ω₁ - ω₂) * t = ω₁ * t - ω₂ * t := by ring
    have e2 : (ω₁ + ω₂) * t = ω₁ * t + ω₂ * t := by ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  constructor
  · rintro rfl
    have hsub : (fun t : ℝ => Real.cos (ω₁ * t) * Real.cos (ω₁ * t) - 1 / 2) =
        fun t : ℝ => (1 / 2) * Real.cos ((2 * ω₁) * t) := by
      funext t; rw [hpt t, sub_self, zero_mul, Real.cos_zero]
      have : ω₁ + ω₁ = 2 * ω₁ := by ring
      rw [this]; ring
    rw [hsub, intervalIntegral.integral_const_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h2ω : 2 * ω₁ ≠ 0 := by linarith
    calc (1 / 2) * |∫ t in a..b, Real.cos ((2 * ω₁) * t)|
        ≤ (1 / 2) * (2 / |2 * ω₁|) := mul_le_mul_of_nonneg_left (abs_integral_cos_mul_le h2ω) (by norm_num)
      _ = 1 / (2 * ω₁) := by rw [abs_of_pos (by linarith : 0 < 2 * ω₁)]; ring
  · intro hne
    have hsum : (fun t : ℝ => Real.cos (ω₁ * t) * Real.cos (ω₂ * t)) =
        fun t : ℝ => (1 / 2) * Real.cos ((ω₁ - ω₂) * t) + (1 / 2) * Real.cos ((ω₁ + ω₂) * t) := by
      funext t; rw [hpt t]; ring
    rw [hsum, intervalIntegral.integral_add
      ((by fun_prop : Continuous fun t : ℝ => (1 / 2) * Real.cos ((ω₁ - ω₂) * t)).intervalIntegrable a b)
      ((by fun_prop : Continuous fun t : ℝ => (1 / 2) * Real.cos ((ω₁ + ω₂) * t)).intervalIntegrable a b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hd : ω₁ - ω₂ ≠ 0 := sub_ne_zero.mpr hne
    have hs : ω₁ + ω₂ ≠ 0 := by linarith
    calc |(1 / 2) * (∫ t in a..b, Real.cos ((ω₁ - ω₂) * t)) +
            (1 / 2) * (∫ t in a..b, Real.cos ((ω₁ + ω₂) * t))|
        ≤ |(1 / 2) * ∫ t in a..b, Real.cos ((ω₁ - ω₂) * t)| +
          |(1 / 2) * ∫ t in a..b, Real.cos ((ω₁ + ω₂) * t)| := abs_add_le _ _
      _ ≤ (1 / 2) * (2 / |ω₁ - ω₂|) + (1 / 2) * (2 / |ω₁ + ω₂|) := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (abs_integral_cos_mul_le hd) (by norm_num))
            (mul_le_mul_of_nonneg_left (abs_integral_cos_mul_le hs) (by norm_num))
      _ = 1 / |ω₁ - ω₂| + 1 / (ω₁ + ω₂) := by rw [abs_of_pos (by linarith : 0 < ω₁ + ω₂)]; ring

private lemma integral_sin_mul_sin_bound {ω₁ ω₂ a b : ℝ} (h1 : 0 < ω₁) (h2 : 0 < ω₂) :
    (ω₁ = ω₂ → |∫ t in a..b, Real.sin (ω₁ * t) * Real.sin (ω₂ * t) - (1 / 2)| ≤ 1 / (2 * ω₁)) ∧
    (ω₁ ≠ ω₂ → |∫ t in a..b, Real.sin (ω₁ * t) * Real.sin (ω₂ * t)| ≤
      1 / |ω₁ - ω₂| + 1 / (ω₁ + ω₂)) := by
  have hpt : ∀ t : ℝ, Real.sin (ω₁ * t) * Real.sin (ω₂ * t) =
      (Real.cos ((ω₁ - ω₂) * t) - Real.cos ((ω₁ + ω₂) * t)) / 2 := fun t => by
    have e1 : (ω₁ - ω₂) * t = ω₁ * t - ω₂ * t := by ring
    have e2 : (ω₁ + ω₂) * t = ω₁ * t + ω₂ * t := by ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  constructor
  · rintro rfl
    have hsub : (fun t : ℝ => Real.sin (ω₁ * t) * Real.sin (ω₁ * t) - 1 / 2) =
        fun t : ℝ => -(1 / 2) * Real.cos ((2 * ω₁) * t) := by
      funext t; rw [hpt t, sub_self, zero_mul, Real.cos_zero]
      have : ω₁ + ω₁ = 2 * ω₁ := by ring
      rw [this]; ring
    rw [hsub, intervalIntegral.integral_const_mul, abs_mul, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h2ω : 2 * ω₁ ≠ 0 := by linarith
    calc (1 / 2) * |∫ t in a..b, Real.cos ((2 * ω₁) * t)|
        ≤ (1 / 2) * (2 / |2 * ω₁|) := mul_le_mul_of_nonneg_left (abs_integral_cos_mul_le h2ω) (by norm_num)
      _ = 1 / (2 * ω₁) := by rw [abs_of_pos (by linarith : 0 < 2 * ω₁)]; ring
  · intro hne
    have hsum : (fun t : ℝ => Real.sin (ω₁ * t) * Real.sin (ω₂ * t)) =
        fun t : ℝ => (1 / 2) * Real.cos ((ω₁ - ω₂) * t) - (1 / 2) * Real.cos ((ω₁ + ω₂) * t) := by
      funext t; rw [hpt t]; ring
    rw [hsum, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t : ℝ => (1 / 2) * Real.cos ((ω₁ - ω₂) * t)).intervalIntegrable a b)
      ((by fun_prop : Continuous fun t : ℝ => (1 / 2) * Real.cos ((ω₁ + ω₂) * t)).intervalIntegrable a b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hd : ω₁ - ω₂ ≠ 0 := sub_ne_zero.mpr hne
    have hs : ω₁ + ω₂ ≠ 0 := by linarith
    calc |(1 / 2) * (∫ t in a..b, Real.cos ((ω₁ - ω₂) * t)) -
            (1 / 2) * (∫ t in a..b, Real.cos ((ω₁ + ω₂) * t))|
        ≤ |(1 / 2) * ∫ t in a..b, Real.cos ((ω₁ - ω₂) * t)| +
          |(1 / 2) * ∫ t in a..b, Real.cos ((ω₁ + ω₂) * t)| := abs_sub _ _
      _ ≤ (1 / 2) * (2 / |ω₁ - ω₂|) + (1 / 2) * (2 / |ω₁ + ω₂|) := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (abs_integral_cos_mul_le hd) (by norm_num))
            (mul_le_mul_of_nonneg_left (abs_integral_cos_mul_le hs) (by norm_num))
      _ = 1 / |ω₁ - ω₂| + 1 / (ω₁ + ω₂) := by rw [abs_of_pos (by linarith : 0 < ω₁ + ω₂)]; ring

private lemma integral_cos_mul_sin_bound {ω₁ ω₂ a b : ℝ} (h1 : 0 < ω₁) (h2 : 0 < ω₂) :
    |∫ t in a..b, Real.cos (ω₁ * t) * Real.sin (ω₂ * t)| ≤
      (if ω₁ = ω₂ then 0 else 1 / |ω₂ - ω₁|) + 1 / (ω₁ + ω₂) := by
  have hpt : ∀ t : ℝ, Real.cos (ω₁ * t) * Real.sin (ω₂ * t) =
      (Real.sin ((ω₁ + ω₂) * t) + Real.sin ((ω₂ - ω₁) * t)) / 2 := fun t => by
    have e1 : (ω₁ + ω₂) * t = ω₂ * t + ω₁ * t := by ring
    have e2 : (ω₂ - ω₁) * t = ω₂ * t - ω₁ * t := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]; ring
  by_cases heq : ω₁ = ω₂
  · subst heq
    simp only [↓reduceIte, zero_add]
    have hfun : (fun t : ℝ => Real.cos (ω₁ * t) * Real.sin (ω₁ * t)) =
        fun t : ℝ => (1 / 2) * Real.sin ((ω₁ + ω₁) * t) := by
      funext t; rw [hpt t, sub_self, zero_mul, Real.sin_zero]; ring
    rw [hfun, intervalIntegral.integral_const_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc (1 / 2) * |∫ t in a..b, Real.sin ((ω₁ + ω₁) * t)|
        ≤ (1 / 2) * (2 / |ω₁ + ω₁|) :=
          mul_le_mul_of_nonneg_left (abs_integral_sin_mul_le (by linarith)) (by norm_num)
      _ = 1 / (ω₁ + ω₁) := by rw [abs_of_pos (by linarith)]; ring
  · simp only [heq, ↓reduceIte]
    have hfun : (fun t : ℝ => Real.cos (ω₁ * t) * Real.sin (ω₂ * t)) =
        fun t : ℝ => (1 / 2) * Real.sin ((ω₁ + ω₂) * t) + (1 / 2) * Real.sin ((ω₂ - ω₁) * t) := by
      funext t; rw [hpt t]; ring
    rw [hfun, intervalIntegral.integral_add
      ((by fun_prop : Continuous fun t : ℝ => (1 / 2) * Real.sin ((ω₁ + ω₂) * t)).intervalIntegrable a b)
      ((by fun_prop : Continuous fun t : ℝ => (1 / 2) * Real.sin ((ω₂ - ω₁) * t)).intervalIntegrable a b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hd : ω₂ - ω₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
    have hs : ω₁ + ω₂ ≠ 0 := by linarith
    calc |(1 / 2) * (∫ t in a..b, Real.sin ((ω₁ + ω₂) * t)) +
            (1 / 2) * (∫ t in a..b, Real.sin ((ω₂ - ω₁) * t))|
        ≤ |(1 / 2) * ∫ t in a..b, Real.sin ((ω₁ + ω₂) * t)| +
          |(1 / 2) * ∫ t in a..b, Real.sin ((ω₂ - ω₁) * t)| := abs_add_le _ _
      _ ≤ (1 / 2) * (2 / |ω₁ + ω₂|) + (1 / 2) * (2 / |ω₂ - ω₁|) := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (abs_integral_sin_mul_le hs) (by norm_num))
            (mul_le_mul_of_nonneg_left (abs_integral_sin_mul_le hd) (by norm_num))
      _ = 1 / |ω₂ - ω₁| + 1 / (ω₁ + ω₂) := by rw [abs_of_pos (by linarith)]; ring

/-- **Asymptotic Trigonometric Negativity Lemma**:
for any nonempty finite set `W ⊂ [0, ∞)` of frequencies, positive weights `m : ℝ → ℝ`, and `M > 0`,
the trigonometric polynomial `F(t) = ∑_{λ ∈ W} m(λ) * (-M cos(λ t) + 2 λ sin(λ t))` takes values
`≤ -ε` (for a uniform `ε > 0`) at arbitrarily large `t`! -/
theorem exists_trigPoly_neg_large {W : Finset ℝ} (hWne : W.Nonempty)
    (hWnn : ∀ μ ∈ W, 0 ≤ μ) {m : ℝ → ℝ} (hm : ∀ μ ∈ W, 0 < m μ) {M : ℝ} (hM : 0 < M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧
      ∑ μ ∈ W, m μ * (-M * Real.cos (μ * t) + 2 * μ * Real.sin (μ * t)) ≤ -ε := by
  classical
  let F : ℝ → ℝ := fun t => ∑ μ ∈ W, m μ * (-M * Real.cos (μ * t) + 2 * μ * Real.sin (μ * t))
  have hF_cont : Continuous F := by
    dsimp only [F]; exact continuous_finsetSum _ fun _ _ => by fun_prop
  by_cases h0 : (0 : ℝ) ∈ W
  · -- Case 1: frequency 0 is present, so the average of F is -m(0)*M < 0!
    set Wpos : Finset ℝ := W.erase 0
    have hWpos : ∀ μ ∈ Wpos, 0 < μ := fun μ hμ =>
      lt_of_le_of_ne (hWnn μ (Finset.mem_of_mem_erase hμ)) (Ne.symm (Finset.ne_of_mem_erase hμ))
    set C₁ : ℝ := ∑ μ ∈ Wpos, m μ * (2 * M / μ + 4)
    have hC₁_nn : 0 ≤ C₁ := Finset.sum_nonneg fun μ hμ => by
      have hmμ := hm μ (Finset.mem_of_mem_erase hμ)
      have hμ0 := hWpos μ hμ
      positivity
    set ε : ℝ := m 0 * M / 4
    have hε : 0 < ε := by
      have := hm 0 h0; positivity
    refine ⟨ε, hε, fun T => ?_⟩
    set L : ℝ := max 1 (C₁ / (2 * ε) + 1)
    have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hC₁_le : C₁ ≤ 2 * ε * L := by
      have h1 : C₁ / (2 * ε) + 1 ≤ L := le_max_right _ _
      have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * ε by linarith)
      rw [mul_add, mul_div_cancel₀ _ (by linarith)] at h2
      linarith
    have hint_F : ∫ t in T..(T + L), F t ≤ -2 * ε * L := by
      have hsplit : ∀ t : ℝ, F t = -(m 0 * M) +
          ∑ μ ∈ Wpos, m μ * (-M * Real.cos (μ * t) + 2 * μ * Real.sin (μ * t)) := fun t => by
        dsimp only [F]
        rw [← Finset.add_sum_erase _ _ h0]
        simp [Wpos]
      have hEq : ∫ t in T..(T + L), F t =
          -(m 0 * M) * L + ∑ μ ∈ Wpos, ∫ t in T..(T + L),
            m μ * (-M * Real.cos (μ * t) + 2 * μ * Real.sin (μ * t)) := by
        simp_rw [hsplit]
        rw [intervalIntegral.integral_add intervalIntegrable_const
          (Continuous.intervalIntegrable (continuous_finsetSum _ fun _ _ => by fun_prop) _ _),
          intervalIntegral.integral_const, smul_eq_mul,
          intervalIntegral.integral_finsetSum (fun _ _ => (by fun_prop : Continuous _).intervalIntegrable _ _)]
        ring
      have hrem : ∑ μ ∈ Wpos, ∫ t in T..(T + L),
          m μ * (-M * Real.cos (μ * t) + 2 * μ * Real.sin (μ * t)) ≤ C₁ := by
        refine Finset.sum_le_sum fun μ hμ => ?_
        have hμ0 := hWpos μ hμ
        have hmμ := hm μ (Finset.mem_of_mem_erase hμ)
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add
            ((by fun_prop : Continuous _).intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ hmμ.le
        have hc := abs_integral_cos_mul_le (a := T) (b := T + L) hμ0.ne'
        have hs := abs_integral_sin_mul_le (a := T) (b := T + L) hμ0.ne'
        rw [abs_of_pos hμ0] at hc hs
        have h1 : -M * ∫ t in T..(T + L), Real.cos (μ * t) ≤ 2 * M / μ := by
          have := (abs_le.mp hc).1
          have := mul_le_mul_of_nonneg_left this hM.le
          have : M * (2 / μ) = 2 * M / μ := by ring
          linarith
        have h2 : 2 * μ * ∫ t in T..(T + L), Real.sin (μ * t) ≤ 4 := by
          have := (abs_le.mp hs).2
          have := mul_le_mul_of_nonneg_left this (show 0 ≤ 2 * μ by linarith)
          have : 2 * μ * (2 / μ) = 4 := by field_simp [hμ0.ne']; ring
          linarith
        linarith
      rw [hEq]
      have h4ε : m 0 * M = 4 * ε := by dsimp only [ε]; ring
      nlinarith
    by_contra hall
    push Not at hall
    have hlow : -ε * L ≤ ∫ t in T..(T + L), F t := by
      have h1 : ∫ t in T..(T + L), (-ε) = -ε * L := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      rw [← h1]
      exact intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hF_cont.intervalIntegrable _ _) fun t ht => (hall t ht.1).le
    nlinarith
  · -- Case 2: all frequencies in W are strictly positive; use mean ≈ 0 and mean-square ≥ c₀ > 0!
    have hWpos : ∀ μ ∈ W, 0 < μ := fun μ hμ =>
      lt_of_le_of_ne (hWnn μ hμ) (fun heq => h0 (heq ▸ hμ))
    set C₁ : ℝ := ∑ μ ∈ W, m μ * (2 * M / μ + 4)
    have hC₁_nn : 0 ≤ C₁ := Finset.sum_nonneg fun μ hμ => by
      have := hm μ hμ; have := hWpos μ hμ; positivity
    set c₀ : ℝ := (1 / 2) * ∑ μ ∈ W, (m μ) ^ 2 * (M ^ 2 + 4 * μ ^ 2)
    have hc₀ : 0 < c₀ := by
      obtain ⟨μ₀, hμ₀⟩ := hWne
      have hterm_pos : 0 < (m μ₀) ^ 2 * (M ^ 2 + 4 * μ₀ ^ 2) := by
        have := hm μ₀ hμ₀; positivity
      have hle := Finset.single_le_sum
        (f := fun μ => (m μ) ^ 2 * (M ^ 2 + 4 * μ ^ 2))
        (fun μ _ => by positivity) hμ₀
      dsimp only [c₀]
      linarith
    -- Upper bound on |F t|
    set B : ℝ := (∑ μ ∈ W, m μ * (M + 2 * μ)) + 1
    have hB_pos : 0 < B := by
      have : 0 ≤ ∑ μ ∈ W, m μ * (M + 2 * μ) := Finset.sum_nonneg fun μ hμ => by
        have := hm μ hμ; have := hWpos μ hμ; positivity
      linarith
    have hF_le_B : ∀ t : ℝ, F t ≤ B := fun t => by
      dsimp only [F, B]
      have h1 : ∑ μ ∈ W, m μ * (-M * Real.cos (μ * t) + 2 * μ * Real.sin (μ * t)) ≤
          ∑ μ ∈ W, m μ * (M + 2 * μ) := by
        refine Finset.sum_le_sum fun μ hμ => ?_
        have hmμ := hm μ hμ
        have hμ0 := hWpos μ hμ
        refine mul_le_mul_of_nonneg_left ?_ hmμ.le
        have hc := abs_le.mp (Real.abs_cos_le_one (μ * t))
        have hs := abs_le.mp (Real.abs_sin_le_one (μ * t))
        nlinarith
      linarith
    -- Uniform bound C₂ on the oscillatory remainder of ∫ (F t)² dt - c₀ * L
    set Kpair : ℝ → ℝ → ℝ := fun μ₁ μ₂ =>
      if μ₁ = μ₂ then 1 / (2 * μ₁) else 1 / |μ₁ - μ₂| + 1 / (μ₁ + μ₂)
    set Kcross : ℝ → ℝ → ℝ := fun μ₁ μ₂ =>
      (if μ₁ = μ₂ then 0 else 1 / |μ₂ - μ₁|) + 1 / (μ₁ + μ₂)
    set C₂ : ℝ := ∑ μ₁ ∈ W, ∑ μ₂ ∈ W,
      m μ₁ * m μ₂ *
        (M ^ 2 * Kpair μ₁ μ₂ + 4 * μ₁ * μ₂ * Kpair μ₁ μ₂ +
         2 * M * μ₂ * Kcross μ₁ μ₂ + 2 * M * μ₁ * Kcross μ₂ μ₁)
    have hC₂_nn : 0 ≤ C₂ := Finset.sum_nonneg fun μ₁ h1 => Finset.sum_nonneg fun μ₂ h2 => by
      have := hm μ₁ h1; have := hm μ₂ h2; have := hWpos μ₁ h1; have := hWpos μ₂ h2
      have hKp : 0 ≤ Kpair μ₁ μ₂ := by dsimp only [Kpair]; split_ifs <;> positivity
      have hKc1 : 0 ≤ Kcross μ₁ μ₂ := by dsimp only [Kcross]; split_ifs <;> positivity
      have hKc2 : 0 ≤ Kcross μ₂ μ₁ := by dsimp only [Kcross]; split_ifs <;> positivity
      positivity
    -- Choose ε > 0 so ε * (B + ε) ≤ c₀ / 4
    set ε : ℝ := min 1 (c₀ / (4 * (B + 1)))
    have hε : 0 < ε := lt_min one_pos (by positivity)
    have hε_le1 : ε ≤ 1 := min_le_left _ _
    have hε_prod : ε * (B + ε) ≤ c₀ / 4 := by
      have h1 : ε ≤ c₀ / (4 * (B + 1)) := min_le_right _ _
      have h2 : B + ε ≤ B + 1 := by linarith
      calc ε * (B + ε) ≤ (c₀ / (4 * (B + 1))) * (B + 1) :=
            mul_le_mul h1 h2 (by linarith) (by positivity)
        _ = c₀ / 4 := by field_simp [show B + 1 ≠ 0 by linarith]
    refine ⟨ε, hε, fun T => ?_⟩
    set L : ℝ := max 1 (max (4 * C₂ / c₀) (4 * B * C₁ / c₀) + 1)
    have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hC₂_le : C₂ ≤ (c₀ / 4) * L := by
      have h1 : 4 * C₂ / c₀ ≤ L := by
        have ha : 4 * C₂ / c₀ ≤ max (4 * C₂ / c₀) (4 * B * C₁ / c₀) := le_max_left _ _
        have hb : max (4 * C₂ / c₀) (4 * B * C₁ / c₀) + 1 ≤ L := le_max_right _ _
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ c₀ / 4 by linarith)
      have h3 : (c₀ / 4) * (4 * C₂ / c₀) = C₂ := by field_simp [hc₀.ne']
      linarith
    have hBC₁_le : B * C₁ ≤ (c₀ / 4) * L := by
      have h1 : 4 * B * C₁ / c₀ ≤ L := by
        have ha : 4 * B * C₁ / c₀ ≤ max (4 * C₂ / c₀) (4 * B * C₁ / c₀) := le_max_right _ _
        have hb : max (4 * C₂ / c₀) (4 * B * C₁ / c₀) + 1 ≤ L := le_max_right _ _
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ c₀ / 4 by linarith)
      have h3 : (c₀ / 4) * (4 * B * C₁ / c₀) = B * C₁ := by field_simp [hc₀.ne']
      linarith
    -- Mean bound: |∫_T^{T+L} F t dt| ≤ C₁
    have hmean_le : |∫ t in T..(T + L), F t| ≤ C₁ := by
      dsimp only [F]
      rw [intervalIntegral.integral_finsetSum (fun _ _ => (by fun_prop : Continuous _).intervalIntegrable _ _)]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ hμ => ?_)
      have hμ0 := hWpos μ hμ; have hmμ := hm μ hμ
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          ((by fun_prop : Continuous _).intervalIntegrable _ _)
          ((by fun_prop : Continuous _).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        abs_mul, abs_of_pos hmμ]
      refine mul_le_mul_of_nonneg_left ?_ hmμ.le
      have hc := abs_integral_cos_mul_le (a := T) (b := T + L) hμ0.ne'
      have hs := abs_integral_sin_mul_le (a := T) (b := T + L) hμ0.ne'
      rw [abs_of_pos hμ0] at hc hs
      calc |-M * (∫ t in T..(T + L), Real.cos (μ * t)) +
              2 * μ * (∫ t in T..(T + L), Real.sin (μ * t))|
          ≤ |-M * (∫ t in T..(T + L), Real.cos (μ * t))| +
            |2 * μ * (∫ t in T..(T + L), Real.sin (μ * t))| := abs_add_le _ _
        _ = M * |∫ t in T..(T + L), Real.cos (μ * t)| +
            2 * μ * |∫ t in T..(T + L), Real.sin (μ * t)| := by
            rw [abs_mul, abs_neg, abs_of_pos hM, abs_mul, abs_of_pos (by linarith : 0 < 2 * μ)]
        _ ≤ M * (2 / μ) + 2 * μ * (2 / μ) :=
            add_le_add (mul_le_mul_of_nonneg_left hc hM.le)
              (mul_le_mul_of_nonneg_left hs (by linarith))
        _ = 2 * M / μ + 4 := by field_simp [hμ0.ne']; ring
    -- Mean-square lower bound: ∫_T^{T+L} (F t)² dt ≥ c₀ * L - C₂
    have hsq_ge : c₀ * L - C₂ ≤ ∫ t in T..(T + L), (F t) ^ 2 := by
      have hexp : ∀ t : ℝ, (F t) ^ 2 = ∑ μ₁ ∈ W, ∑ μ₂ ∈ W,
          m μ₁ * m μ₂ *
            (M ^ 2 * (Real.cos (μ₁ * t) * Real.cos (μ₂ * t)) +
             4 * μ₁ * μ₂ * (Real.sin (μ₁ * t) * Real.sin (μ₂ * t)) -
             2 * M * μ₂ * (Real.cos (μ₁ * t) * Real.sin (μ₂ * t)) -
             2 * M * μ₁ * (Real.cos (μ₂ * t) * Real.sin (μ₁ * t))) := fun t => by
        dsimp only [F]
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun μ₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ₂ _ => ?_
        ring
      have hdiag : c₀ * L = ∑ μ₁ ∈ W, ∑ μ₂ ∈ W,
          if μ₁ = μ₂ then m μ₁ * m μ₂ * (M ^ 2 * (1 / 2 * L) + 4 * μ₁ * μ₂ * (1 / 2 * L)) else 0 := by
        dsimp only [c₀]
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun μ₁ h1 => ?_
        rw [Finset.sum_ite_eq W μ₁, if_pos h1]
        ring
      simp_rw [hexp]
      rw [intervalIntegral.integral_finsetSum (fun _ _ =>
        (continuous_finsetSum _ fun _ _ => by fun_prop).intervalIntegrable _ _)]
      have hinner_int : ∀ μ₁ ∈ W,
          ∫ t in T..(T + L), ∑ μ₂ ∈ W, m μ₁ * m μ₂ *
            (M ^ 2 * (Real.cos (μ₁ * t) * Real.cos (μ₂ * t)) +
             4 * μ₁ * μ₂ * (Real.sin (μ₁ * t) * Real.sin (μ₂ * t)) -
             2 * M * μ₂ * (Real.cos (μ₁ * t) * Real.sin (μ₂ * t)) -
             2 * M * μ₁ * (Real.cos (μ₂ * t) * Real.sin (μ₁ * t))) =
          ∑ μ₂ ∈ W, ∫ t in T..(T + L), m μ₁ * m μ₂ *
            (M ^ 2 * (Real.cos (μ₁ * t) * Real.cos (μ₂ * t)) +
             4 * μ₁ * μ₂ * (Real.sin (μ₁ * t) * Real.sin (μ₂ * t)) -
             2 * M * μ₂ * (Real.cos (μ₁ * t) * Real.sin (μ₂ * t)) -
             2 * M * μ₁ * (Real.cos (μ₂ * t) * Real.sin (μ₁ * t))) := fun μ₁ _ =>
        intervalIntegral.integral_finsetSum (fun _ _ => (by fun_prop : Continuous _).intervalIntegrable _ _)
      rw [Finset.sum_congr rfl hinner_int]
      have hdiff : |(∑ μ₁ ∈ W, ∑ μ₂ ∈ W, ∫ t in T..(T + L), m μ₁ * m μ₂ *
            (M ^ 2 * (Real.cos (μ₁ * t) * Real.cos (μ₂ * t)) +
             4 * μ₁ * μ₂ * (Real.sin (μ₁ * t) * Real.sin (μ₂ * t)) -
             2 * M * μ₂ * (Real.cos (μ₁ * t) * Real.sin (μ₂ * t)) -
             2 * M * μ₁ * (Real.cos (μ₂ * t) * Real.sin (μ₁ * t)))) - c₀ * L| ≤ C₂ := by
        rw [hdiag, ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ₁ h1 => ?_)
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ₂ h2 => ?_)
        have hm1 := hm μ₁ h1; have hm2 := hm μ₂ h2
        have hw1 := hWpos μ₁ h1; have hw2 := hWpos μ₂ h2
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub
            ((by fun_prop : Continuous _).intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _),
          intervalIntegral.integral_sub
            ((by fun_prop : Continuous _).intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _),
          intervalIntegral.integral_add
            ((by fun_prop : Continuous _).intervalIntegrable _ _)
            ((by fun_prop : Continuous _).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        have hcc := integral_cos_mul_cos_bound (a := T) (b := T + L) hw1 hw2
        have hss := integral_sin_mul_sin_bound (a := T) (b := T + L) hw1 hw2
        have hcs1 := integral_cos_mul_sin_bound (a := T) (b := T + L) hw1 hw2
        have hcs2 := integral_cos_mul_sin_bound (a := T) (b := T + L) hw2 hw1
        by_cases heq : μ₁ = μ₂
        · subst heq
          simp only [↓reduceIte]
          have hsub_cc : (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.cos (μ₁ * t)) - 1 / 2 * L =
              ∫ t in T..(T + L), (Real.cos (μ₁ * t) * Real.cos (μ₁ * t) - 1 / 2) := by
            rw [intervalIntegral.integral_sub ((by fun_prop : Continuous _).intervalIntegrable _ _)
              intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]; ring
          have hsub_ss : (∫ t in T..(T + L), Real.sin (μ₁ * t) * Real.sin (μ₁ * t)) - 1 / 2 * L =
              ∫ t in T..(T + L), (Real.sin (μ₁ * t) * Real.sin (μ₁ * t) - 1 / 2) := by
            rw [intervalIntegral.integral_sub ((by fun_prop : Continuous _).intervalIntegrable _ _)
              intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]; ring
          have hrew :
              m μ₁ * m μ₁ *
                (M ^ 2 * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.cos (μ₁ * t)) +
                 4 * μ₁ * μ₁ * (∫ t in T..(T + L), Real.sin (μ₁ * t) * Real.sin (μ₁ * t)) -
                 2 * M * μ₁ * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₁ * t)) -
                 2 * M * μ₁ * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₁ * t))) -
              m μ₁ * m μ₁ * (M ^ 2 * (1 / 2 * L) + 4 * μ₁ * μ₁ * (1 / 2 * L)) =
              m μ₁ * m μ₁ *
                (M ^ 2 * ((∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.cos (μ₁ * t)) - 1 / 2 * L) +
                 4 * μ₁ * μ₁ * ((∫ t in T..(T + L), Real.sin (μ₁ * t) * Real.sin (μ₁ * t)) - 1 / 2 * L) -
                 2 * M * μ₁ * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₁ * t)) -
                 2 * M * μ₁ * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₁ * t))) := by ring
          rw [hrew, hsub_cc, hsub_ss, abs_mul, abs_of_pos (mul_pos hm1 hm1)]
          refine mul_le_mul_of_nonneg_left ?_ (mul_pos hm1 hm1).le
          have b1 := hcc.1 rfl
          have b2 := hss.1 rfl
          have b3 : |∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₁ * t)| ≤ Kcross μ₁ μ₁ := hcs1
          have hKp : Kpair μ₁ μ₁ = 1 / (2 * μ₁) := if_pos rfl
          rw [hKp]
          have ht1 := abs_sub
            (M ^ 2 * (∫ t in T..(T + L), (Real.cos (μ₁ * t) * Real.cos (μ₁ * t) - 1 / 2)) +
             4 * μ₁ * μ₁ * (∫ t in T..(T + L), (Real.sin (μ₁ * t) * Real.sin (μ₁ * t) - 1 / 2)) -
             2 * M * μ₁ * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₁ * t)))
            (2 * M * μ₁ * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₁ * t)))
          have ht2 := abs_sub
            (M ^ 2 * (∫ t in T..(T + L), (Real.cos (μ₁ * t) * Real.cos (μ₁ * t) - 1 / 2)) +
             4 * μ₁ * μ₁ * (∫ t in T..(T + L), (Real.sin (μ₁ * t) * Real.sin (μ₁ * t) - 1 / 2)))
            (2 * M * μ₁ * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₁ * t)))
          have ht3 := abs_add_le
            (M ^ 2 * (∫ t in T..(T + L), (Real.cos (μ₁ * t) * Real.cos (μ₁ * t) - 1 / 2)))
            (4 * μ₁ * μ₁ * (∫ t in T..(T + L), (Real.sin (μ₁ * t) * Real.sin (μ₁ * t) - 1 / 2)))
          rw [abs_mul, abs_of_nonneg (sq_nonneg M)] at ht3
          rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * μ₁ * μ₁)] at ht3
          rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * M * μ₁)] at ht1 ht2
          have m1 := mul_le_mul_of_nonneg_left b1 (sq_nonneg M)
          have m2 := mul_le_mul_of_nonneg_left b2 (by positivity : 0 ≤ 4 * μ₁ * μ₁)
          have m3 := mul_le_mul_of_nonneg_left b3 (by positivity : 0 ≤ 2 * M * μ₁)
          linarith
        · simp only [heq, ↓reduceIte, sub_zero]
          rw [abs_mul, abs_of_pos (mul_pos hm1 hm2)]
          refine mul_le_mul_of_nonneg_left ?_ (mul_pos hm1 hm2).le
          have b1 : |∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.cos (μ₂ * t)| ≤ Kpair μ₁ μ₂ := by
            dsimp only [Kpair]; rw [if_neg heq]; exact hcc.2 heq
          have b2 : |∫ t in T..(T + L), Real.sin (μ₁ * t) * Real.sin (μ₂ * t)| ≤ Kpair μ₁ μ₂ := by
            dsimp only [Kpair]; rw [if_neg heq]; exact hss.2 heq
          have b3 : |∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₂ * t)| ≤ Kcross μ₁ μ₂ := hcs1
          have b4 : |∫ t in T..(T + L), Real.cos (μ₂ * t) * Real.sin (μ₁ * t)| ≤ Kcross μ₂ μ₁ := hcs2
          have ht1 := abs_sub
            (M ^ 2 * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.cos (μ₂ * t)) +
             4 * μ₁ * μ₂ * (∫ t in T..(T + L), Real.sin (μ₁ * t) * Real.sin (μ₂ * t)) -
             2 * M * μ₂ * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₂ * t)))
            (2 * M * μ₁ * (∫ t in T..(T + L), Real.cos (μ₂ * t) * Real.sin (μ₁ * t)))
          have ht2 := abs_sub
            (M ^ 2 * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.cos (μ₂ * t)) +
             4 * μ₁ * μ₂ * (∫ t in T..(T + L), Real.sin (μ₁ * t) * Real.sin (μ₂ * t)))
            (2 * M * μ₂ * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.sin (μ₂ * t)))
          have ht3 := abs_add_le
            (M ^ 2 * (∫ t in T..(T + L), Real.cos (μ₁ * t) * Real.cos (μ₂ * t)))
            (4 * μ₁ * μ₂ * (∫ t in T..(T + L), Real.sin (μ₁ * t) * Real.sin (μ₂ * t)))
          rw [abs_mul, abs_of_nonneg (sq_nonneg M)] at ht3
          rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * μ₁ * μ₂)] at ht3
          rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * M * μ₂)] at ht2
          rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * M * μ₁)] at ht1
          have m1 := mul_le_mul_of_nonneg_left b1 (sq_nonneg M)
          have m2 := mul_le_mul_of_nonneg_left b2 (by positivity : 0 ≤ 4 * μ₁ * μ₂)
          have m3 := mul_le_mul_of_nonneg_left b3 (by positivity : 0 ≤ 2 * M * μ₂)
          have m4 := mul_le_mul_of_nonneg_left b4 (by positivity : 0 ≤ 2 * M * μ₁)
          linarith
      linarith [(abs_le.mp hdiff).1]
    -- Contradiction if F t > -ε for all t ∈ [T, T + L]
    by_contra hall
    push Not at hall
    have hpt_sq : ∀ t ∈ Set.Icc T (T + L), (F t) ^ 2 ≤ B * F t + ε * (B + ε) := by
      intro t ht
      have hgt : -ε < F t := hall t ht.1
      have hle : F t ≤ B := hF_le_B t
      rcases le_or_gt 0 (F t) with hnn | hneg
      · nlinarith
      · nlinarith
    have hint_sq_le : ∫ t in T..(T + L), (F t) ^ 2 ≤ B * (∫ t in T..(T + L), F t) + ε * (B + ε) * L := by
      have h1 : ∫ t in T..(T + L), (F t) ^ 2 ≤ ∫ t in T..(T + L), (B * F t + ε * (B + ε)) :=
        intervalIntegral.integral_mono_on (by linarith)
          ((hF_cont.pow 2).intervalIntegrable _ _)
          (((hF_cont.const_mul B).add continuous_const).intervalIntegrable _ _) hpt_sq
      rw [intervalIntegral.integral_add ((hF_cont.const_mul B).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul] at h1
      linarith
    have hBF : B * (∫ t in T..(T + L), F t) ≤ B * C₁ :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hmean_le) hB_pos.le
    have hεL : ε * (B + ε) * L ≤ (c₀ / 4) * L :=
      mul_le_mul_of_nonneg_right hε_prod hL.le
    nlinarith

/-! ### Weil's Equivalence (`RH ↔ Weil Positivity`) -/

/-- Exact real-part expansion of `Φ_{f_{a, γ} * f̃_{a, γ}}(ρ)` for `f_{a, γ} = weilOddGaussian a γ`. -/
private lemma re_selfConv_weilOddGaussian (a γ : ℝ) (ha : 0 < a) (ρ : ℂ) :
    (weilBilateralTransform
      (weilConv (weilOddGaussian a γ) (weilInvolution (weilOddGaussian a γ))) ρ).re =
    (Real.pi / (4 * a ^ 3)) * Real.exp (((ρ.re - 1 / 2) ^ 2 - (ρ.im - γ) ^ 2) / (2 * a)) *
      (-(((ρ.re - 1 / 2) ^ 2 - (ρ.im - γ) ^ 2) * Real.cos ((ρ.re - 1 / 2) * (ρ.im - γ) / a)) +
        2 * ((ρ.re - 1 / 2) * (ρ.im - γ)) * Real.sin ((ρ.re - 1 / 2) * (ρ.im - γ) / a)) := by
  rw [weilBilateralTransform_selfConv_weilOddGaussian ha γ ρ]
  set x : ℝ := ρ.re - 1 / 2
  set y : ℝ := ρ.im - γ
  have hw : ρ - 1 / 2 - I * (γ : ℂ) = (x : ℂ) + I * (y : ℂ) := by apply Complex.ext <;> simp [x, y]
  rw [hw]
  have hw2 : ((x : ℂ) + I * (y : ℂ)) ^ 2 = ((x ^ 2 - y ^ 2 : ℝ) : ℂ) + I * ((2 * x * y : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [sq]
    · simp [sq]; ring
  rw [hw2]
  have hexp_split : cexp ((((x ^ 2 - y ^ 2 : ℝ) : ℂ) + I * ((2 * x * y : ℝ) : ℂ)) / (2 * (a : ℂ))) =
      ((Real.exp ((x ^ 2 - y ^ 2) / (2 * a)) : ℝ) : ℂ) *
        cexp (((x * y / a : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast; field_simp [haC]
  rw [hexp_split]
  have hpre : -((((x ^ 2 - y ^ 2 : ℝ) : ℂ) + I * ((2 * x * y : ℝ) : ℂ)) / (4 * (a : ℂ) ^ 2)) *
      ((Real.pi / a : ℝ) : ℂ) *
      (((Real.exp ((x ^ 2 - y ^ 2) / (2 * a)) : ℝ) : ℂ) * cexp (((x * y / a : ℝ) : ℂ) * I)) =
      (((Real.pi / (4 * a ^ 3)) * Real.exp ((x ^ 2 - y ^ 2) / (2 * a)) : ℝ) : ℂ) *
        ((-((x ^ 2 - y ^ 2 : ℝ) : ℂ) - I * ((2 * x * y : ℝ) : ℂ)) * cexp (((x * y / a : ℝ) : ℂ) * I)) := by
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast; field_simp [haC]; ring
  rw [hpre, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im]
  ring

private lemma norm_selfConv_weilOddGaussian (a γ : ℝ) (ha : 0 < a) (ρ : ℂ) :
    ‖weilBilateralTransform
      (weilConv (weilOddGaussian a γ) (weilInvolution (weilOddGaussian a γ))) ρ‖ =
    (Real.pi / (4 * a ^ 3)) * ((ρ.re - 1 / 2) ^ 2 + (ρ.im - γ) ^ 2) *
      Real.exp (((ρ.re - 1 / 2) ^ 2 - (ρ.im - γ) ^ 2) / (2 * a)) := by
  rw [weilBilateralTransform_selfConv_weilOddGaussian ha γ ρ]
  set x : ℝ := ρ.re - 1 / 2
  set y : ℝ := ρ.im - γ
  have hw : ρ - 1 / 2 - I * (γ : ℂ) = (x : ℂ) + I * (y : ℂ) := by apply Complex.ext <;> simp [x, y]
  rw [hw, norm_mul, norm_mul, norm_neg, norm_div, norm_pow, norm_mul, Complex.norm_ofNat,
    norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha.le,
    Real.norm_of_nonneg (by positivity : 0 ≤ Real.pi / a), Complex.norm_exp]
  have hns : ‖(x : ℂ) + I * (y : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
  have hre : (((x : ℂ) + I * (y : ℂ)) ^ 2 / (2 * (a : ℂ))).re = (x ^ 2 - y ^ 2) / (2 * a) := by
    have h2 : ((x : ℂ) + I * (y : ℂ)) ^ 2 / (2 * (a : ℂ)) =
        (((x ^ 2 - y ^ 2) / (2 * a) : ℝ) : ℂ) + I * (((x * y) / a : ℝ) : ℂ) := by
      have hsq : ((x : ℂ) + I * (y : ℂ)) ^ 2 = ((x ^ 2 - y ^ 2 : ℝ) : ℂ) + I * ((2 * x * y : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [sq]
        · simp [sq]; ring
      rw [hsq]
      have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      push_cast; field_simp [haC]
    rw [h2, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    ring
  rw [hns, hre]
  field_simp [ha.ne']

/-- A countable critical-strip zero spectrum `Z : ℕ → ℂ` (e.g., all nontrivial zeros of
`riemannZeta` with multiplicity) satisfying local finiteness in bounded vertical strips and
Gaussian-tail summability (which holds automatically from any polynomial or Riemann–von Mangoldt
zero count `N(T) = O(T log T)`). -/
structure ZeroSpectrum where
  zero : ℕ → ℂ
  in_strip : ∀ n : ℕ, 0 < (zero n).re ∧ (zero n).re < 1
  locally_finite : ∀ R : ℝ, Set.Finite {n : ℕ | |(zero n).im| ≤ R}
  gaussian_summable : ∀ c : ℝ, 0 < c → Summable (fun n : ℕ => Real.exp (-c * (zero n).im ^ 2))

/-- The Weil quadratic form over a `ZeroSpectrum`:
`W(Z; f) = ∑' n, Re(Φ_{f * f̃}(Z.zero n))`. -/
def weilQuadraticForm (Z : ZeroSpectrum) (f : ℝ → ℂ) : ℝ :=
  ∑' n : ℕ, (weilBilateralTransform (weilConv f (weilInvolution f)) (Z.zero n)).re

/-- **Forward Direction (`On-Line → Weil Positivity`) for Any `ZeroSpectrum`**:
if every zero `Z.zero n` lies on `Re(s) = 1/2`, then for EVERY `WeilAdmissible f σ₀` (`σ₀ > 0`),
every summand is `‖Φ_f(Z.zero n)‖² ≥ 0` and hence `0 ≤ weilQuadraticForm Z f`! -/
theorem weilQuadraticForm_nonneg_of_onLine (Z : ZeroSpectrum)
    (hon : ∀ n : ℕ, (Z.zero n).re = 1 / 2) {f : ℝ → ℂ} {σ₀ : ℝ}
    (hf : WeilAdmissible f σ₀) (hσ₀ : 0 < σ₀) :
    0 ≤ weilQuadraticForm Z f := by
  unfold weilQuadraticForm
  exact tsum_nonneg fun n => (weilBilateralTransform_selfConv_re_nonneg_of_re_eq_half hf hσ₀ (hon n)).1

/-- **Converse Direction (`Weil Positivity on Odd-Gaussians → Every Zero Lies on Re(s) = 1/2`)**:
for ANY `ZeroSpectrum`, if `0 ≤ weilQuadraticForm Z (weilOddGaussian a γ)` for all `a > 0` and
all `γ ∈ ℝ`, then EVERY zero satisfies `(Z.zero n).re = 1 / 2`! (No assumption that
`sup |(Z.zero n).re - 1/2|` is attained!) -/
theorem onLine_of_weilQuadraticForm_nonneg (Z : ZeroSpectrum)
    (hpos : ∀ a : ℝ, 0 < a → ∀ γ : ℝ, 0 ≤ weilQuadraticForm Z (weilOddGaussian a γ)) :
    ∀ n : ℕ, (Z.zero n).re = 1 / 2 := by
  classical
  intro n₀
  by_contra hoff
  set γ₀ : ℝ := (Z.zero n₀).im
  set Q : ℕ → ℝ := fun n => ((Z.zero n).re - 1 / 2) ^ 2 - ((Z.zero n).im - γ₀) ^ 2
  have hQ0 : 0 < Q n₀ := by
    dsimp only [Q, γ₀]
    rw [sub_self, zero_pow (by norm_num), sub_zero]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
  -- The box B = {n | |(Z.zero n).im - γ₀| ≤ 1} is finite!
  have hB_fin : Set.Finite {n : ℕ | |(Z.zero n).im - γ₀| ≤ 1} := by
    refine (Z.locally_finite (|γ₀| + 1)).subset fun n hn => ?_
    change |(Z.zero n).im - γ₀| ≤ 1 at hn
    change |(Z.zero n).im| ≤ |γ₀| + 1
    have h1 := abs_sub_abs_le_abs_sub (Z.zero n).im γ₀
    linarith
  set Bfin : Finset ℕ := hB_fin.toFinset
  have hn₀_mem : n₀ ∈ Bfin := by
    rw [Set.Finite.mem_toFinset]
    simp [γ₀]
  have hBne : Bfin.Nonempty := ⟨n₀, hn₀_mem⟩
  -- For any n ∉ Bfin, Q n ≤ 1/4 - 1 = -3/4 < 0 < Q n₀!
  have hQ_out : ∀ n : ℕ, n ∉ Bfin → Q n ≤ -(1 / 2) - (1 / 4) * ((Z.zero n).im - γ₀) ^ 2 := by
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    change ¬ |(Z.zero n).im - γ₀| ≤ 1 at hn
    push Not at hn
    obtain ⟨hlo, hhi⟩ := Z.in_strip n
    have hx : ((Z.zero n).re - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith
    have hy : 1 ≤ ((Z.zero n).im - γ₀) ^ 2 := by
      have : 1 < |(Z.zero n).im - γ₀| := hn
      nlinarith [sq_abs ((Z.zero n).im - γ₀)]
    dsimp only [Q]
    nlinarith
  -- Maximize Q over the finite box Bfin; this is the GLOBAL maximum over all ℕ!
  obtain ⟨nMax, hnMax_mem, hnMax_ge⟩ := Bfin.exists_max_image Q hBne
  set M : ℝ := Q nMax
  have hM_pos : 0 < M := lt_of_lt_of_le hQ0 (hnMax_ge n₀ hn₀_mem)
  set Smax : Finset ℕ := Bfin.filter fun n => Q n = M
  set Snear : Finset ℕ := Bfin.filter fun n => Q n ≠ M
  have hSmax_ne : Smax.Nonempty := ⟨nMax, Finset.mem_filter.mpr ⟨hnMax_mem, rfl⟩⟩
  have hQ_le_M : ∀ n ∈ Bfin, Q n ≤ M := hnMax_ge
  -- Gap η > 0 separating Snear from M
  have hgap : ∃ η : ℝ, 0 < η ∧ ∀ n ∈ Snear, Q n ≤ M - η := by
    by_cases hSne : Snear.Nonempty
    · obtain ⟨n1, hn1_mem, hn1_ge⟩ := Snear.exists_max_image Q hSne
      have hlt : Q n1 < M :=
        lt_of_le_of_ne (hQ_le_M n1 (Finset.mem_filter.mp hn1_mem).1) (Finset.mem_filter.mp hn1_mem).2
      refine ⟨M - Q n1, by linarith, fun n hn => by linarith [hn1_ge n hn]⟩
    · refine ⟨1, one_pos, fun n hn => (hSne ⟨n, hn⟩).elim⟩
  obtain ⟨η, hη_pos, hSnear_le⟩ := hgap
  -- Group Smax by frequency μ = |(re - 1/2) * (im - γ₀)| ≥ 0
  set ω : ℕ → ℝ := fun n => |((Z.zero n).re - 1 / 2) * ((Z.zero n).im - γ₀)|
  set W : Finset ℝ := Smax.image ω
  have hWne : W.Nonempty := hSmax_ne.image ω
  have hWnn : ∀ μ ∈ W, 0 ≤ μ := fun μ hμ => by
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hμ
    exact abs_nonneg _
  set mult : ℝ → ℝ := fun μ => ((Smax.filter fun n => ω n = μ).card : ℝ)
  have hmult_pos : ∀ μ ∈ W, 0 < mult μ := fun μ hμ => by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hμ
    have hne : (Smax.filter fun k => ω k = ω n).Nonempty := ⟨n, Finset.mem_filter.mpr ⟨hn, rfl⟩⟩
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  -- Apply our Asymptotic Trigonometric Negativity Lemma!
  obtain ⟨ε, hε_pos, htrig⟩ := exists_trigPoly_neg_large hWne hWnn hmult_pos hM_pos
  -- Show that on Smax, the normalized leading sum equals the trig polynomial F(1/a)!
  have hlead_eq : ∀ a : ℝ, 0 < a →
      ∑ n ∈ Smax,
        (weilBilateralTransform
          (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀)))
          (Z.zero n)).re =
      (Real.pi / (4 * a ^ 3)) * Real.exp (M / (2 * a)) *
        (∑ μ ∈ W, mult μ * (-M * Real.cos (μ * (1 / a)) + 2 * μ * Real.sin (μ * (1 / a)))) := by
    intro a ha
    have hterm : ∀ n ∈ Smax,
        (weilBilateralTransform
          (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀)))
          (Z.zero n)).re =
        (Real.pi / (4 * a ^ 3)) * Real.exp (M / (2 * a)) *
          (-M * Real.cos (ω n * (1 / a)) + 2 * ω n * Real.sin (ω n * (1 / a))) := by
      intro n hn
      have hQn : Q n = M := (Finset.mem_filter.mp hn).2
      rw [re_selfConv_weilOddGaussian a γ₀ ha (Z.zero n)]
      have hQ_rw : ((Z.zero n).re - 1 / 2) ^ 2 - ((Z.zero n).im - γ₀) ^ 2 = M := hQn
      rw [hQ_rw]
      congr 1
      set p : ℝ := ((Z.zero n).re - 1 / 2) * ((Z.zero n).im - γ₀)
      have hdiv : p / a = p * (1 / a) := by ring
      rw [hdiv]
      rcases le_or_gt 0 p with hp | hp
      · have habs : ω n = p := abs_of_nonneg hp
        rw [habs]; ring
      · have habs : ω n = -p := abs_of_neg hp
        rw [habs, show -p * (1 / a) = -(p * (1 / a)) by ring, Real.cos_neg, Real.sin_neg]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (g := ω) (t := W) (fun n hn => Finset.mem_image_of_mem ω hn)]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hconst : ∀ n ∈ Smax.filter (fun k => ω k = μ),
        -M * Real.cos (ω n * (1 / a)) + 2 * ω n * Real.sin (ω n * (1 / a)) =
        -M * Real.cos (μ * (1 / a)) + 2 * μ * Real.sin (μ * (1 / a)) := fun n hn => by
      rw [(Finset.mem_filter.mp hn).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  -- Summability of the full Gaussian tail over n ∉ Bfin for any 0 < a ≤ 1/4
  have hfar_summ_base : Summable (fun n : ℕ =>
      (1 / 4 + ((Z.zero n).im - γ₀) ^ 2) * Real.exp (-((Z.zero n).im - γ₀) ^ 2 / 2)) := by
    have hbase := Z.gaussian_summable (1 / 8) (by norm_num)
    -- Bound (1/4 + (y - γ₀)²) * exp(-(y - γ₀)² / 2) ≤ C * exp(-y² / 8)
    have h1 : ∀ y : ℝ, (1 / 4 + (y - γ₀) ^ 2) * Real.exp (-(y - γ₀) ^ 2 / 2) ≤
        (5 * Real.exp (γ₀ ^ 2 / 4)) * Real.exp (-(1 / 8) * y ^ 2) := fun y => by
      have hu : 1 / 4 + (y - γ₀) ^ 2 ≤ 5 * Real.exp ((y - γ₀) ^ 2 / 4) := by
        have hlin : (y - γ₀) ^ 2 / 4 + 1 ≤ Real.exp ((y - γ₀) ^ 2 / 4) :=
          Real.add_one_le_exp _
        nlinarith
      have hquad : -(y - γ₀) ^ 2 / 4 ≤ γ₀ ^ 2 / 4 - (1 / 8) * y ^ 2 := by
        have : 0 ≤ (y - 2 * γ₀) ^ 2 / 8 := by positivity
        nlinarith
      calc (1 / 4 + (y - γ₀) ^ 2) * Real.exp (-(y - γ₀) ^ 2 / 2)
          ≤ (5 * Real.exp ((y - γ₀) ^ 2 / 4)) * Real.exp (-(y - γ₀) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right hu (Real.exp_nonneg _)
        _ = 5 * Real.exp (-(y - γ₀) ^ 2 / 4) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ 5 * Real.exp (γ₀ ^ 2 / 4 - (1 / 8) * y ^ 2) := by gcongr
        _ = (5 * Real.exp (γ₀ ^ 2 / 4)) * Real.exp (-(1 / 8) * y ^ 2) := by
            rw [sub_eq_add_neg, Real.exp_add, mul_assoc, neg_mul]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => h1 (Z.zero n).im)
      (hbase.mul_left _)
  set Cfar : ℝ := ∑' n : ℕ, (1 / 4 + ((Z.zero n).im - γ₀) ^ 2) * Real.exp (-((Z.zero n).im - γ₀) ^ 2 / 2)
  have hCfar_nn : 0 ≤ Cfar := tsum_nonneg fun _ => by positivity
  set Cnear : ℝ := ∑ n ∈ Snear, (((Z.zero n).re - 1 / 2) ^ 2 + ((Z.zero n).im - γ₀) ^ 2)
  have hCnear_nn : 0 ≤ Cnear := Finset.sum_nonneg fun _ _ => by positivity
  -- Choose threshold T₀ ≥ 4 large enough so both near and far tails are < ε / 4
  have htail_small : ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      Cnear * Real.exp (-η * t / 2) + Cfar * Real.exp (-(M + 1 / 2) * t / 2) ≤ ε / 2 := by
    have hlim1 : Tendsto (fun t : ℝ => Cnear * Real.exp (-η * t / 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => (-η / 2) * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
      have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul Cnear
      rw [mul_zero] at h2
      refine h2.congr fun t => ?_
      dsimp only [Function.comp_apply]; congr 2; ring
    have hlim2 : Tendsto (fun t : ℝ => Cfar * Real.exp (-(M + 1 / 2) * t / 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => (-(M + 1 / 2) / 2) * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
      have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul Cfar
      rw [mul_zero] at h2
      refine h2.congr fun t => ?_
      dsimp only [Function.comp_apply]; congr 2; ring
    have hlim := hlim1.add hlim2
    rw [add_zero] at hlim
    have hev := (hlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2)))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨T1, hT1⟩ := hev
    exact ⟨max 4 T1, le_max_left _ _, fun t ht => (hT1 t ((le_max_right _ _).trans ht)).le⟩
  obtain ⟨T₀, hT₀4, htail_bd⟩ := htail_small
  -- Pick t ≥ T₀ with F(t) ≤ -ε and set a = 1 / t ∈ (0, 1/4]
  obtain ⟨t, htT₀, hFt⟩ := htrig T₀
  have ht_pos : 0 < t := by linarith
  set a : ℝ := 1 / t with ha_def
  have ha_pos : 0 < a := by positivity
  have ha_le : a ≤ 1 / 4 := by
    rw [ha_def, one_div, inv_le_comm₀ ht_pos (by norm_num)]; linarith
  have hinv_a : 1 / a = t := by rw [ha_def]; field_simp [ht_pos.ne']
  -- Summability of the Weil quadratic form terms at a
  set term : ℕ → ℝ := fun n =>
    (weilBilateralTransform
      (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀)))
      (Z.zero n)).re
  have hterm_far_le : ∀ n : ℕ, n ∉ Bfin →
      |term n| ≤ (Real.pi / (4 * a ^ 3)) * Real.exp (-(1 / 2) / (2 * a)) *
        ((1 / 4 + ((Z.zero n).im - γ₀) ^ 2) * Real.exp (-((Z.zero n).im - γ₀) ^ 2 / 2)) := by
    intro n hn
    have h1 : |term n| ≤ ‖weilBilateralTransform
        (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) (Z.zero n)‖ :=
      Complex.abs_re_le_norm _
    rw [norm_selfConv_weilOddGaussian a γ₀ ha_pos (Z.zero n)] at h1
    obtain ⟨hlo, hhi⟩ := Z.in_strip n
    have hx : ((Z.zero n).re - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith
    have hQle := hQ_out n hn
    have hexp_le : Q n / (2 * a) ≤ -(1 / 2) / (2 * a) + -((Z.zero n).im - γ₀) ^ 2 / 2 := by
      have hdiv : Q n / (2 * a) ≤ (-(1 / 2) - (1 / 4) * ((Z.zero n).im - γ₀) ^ 2) / (2 * a) :=
        div_le_div_of_nonneg_right hQle (by positivity)
      have h8a : 1 / 2 ≤ 1 / (8 * a) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
      have hy2 : 0 ≤ ((Z.zero n).im - γ₀) ^ 2 := sq_nonneg _
      have hstep : (-(1 / 2) - (1 / 4) * ((Z.zero n).im - γ₀) ^ 2) / (2 * a) =
          -(1 / 2) / (2 * a) - (1 / (8 * a)) * ((Z.zero n).im - γ₀) ^ 2 := by
        field_simp [ha_pos.ne']; ring
      nlinarith
    calc |term n|
        ≤ (Real.pi / (4 * a ^ 3)) * (((Z.zero n).re - 1 / 2) ^ 2 + ((Z.zero n).im - γ₀) ^ 2) *
            Real.exp (Q n / (2 * a)) := h1
      _ ≤ (Real.pi / (4 * a ^ 3)) * (1 / 4 + ((Z.zero n).im - γ₀) ^ 2) *
            Real.exp (-(1 / 2) / (2 * a) + -((Z.zero n).im - γ₀) ^ 2 / 2) := by
          gcongr
      _ = (Real.pi / (4 * a ^ 3)) * Real.exp (-(1 / 2) / (2 * a)) *
            ((1 / 4 + ((Z.zero n).im - γ₀) ^ 2) * Real.exp (-((Z.zero n).im - γ₀) ^ 2 / 2)) := by
          rw [Real.exp_add]; ring
  have hterm_summ : Summable term := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n => (Real.pi / (4 * a ^ 3)) * Real.exp (-(1 / 2) / (2 * a)) *
        ((1 / 4 + ((Z.zero n).im - γ₀) ^ 2) * Real.exp (-((Z.zero n).im - γ₀) ^ 2 / 2)))
      (hfar_summ_base.mul_left _) ?_
    rw [Filter.eventually_cofinite]
    refine hB_fin.subset fun n hn => ?_
    by_contra hnot
    exact hn (by simpa [Real.norm_eq_abs] using hterm_far_le n (by rwa [Set.Finite.mem_toFinset]))
  -- Split weilQuadraticForm Z (weilOddGaussian a γ₀) = Smax + Snear + outside Bfin
  have hsplit_all : weilQuadraticForm Z (weilOddGaussian a γ₀) =
      (∑ n ∈ Bfin, term n) + ∑' n : ℕ, if n ∈ Bfin then (0 : ℝ) else term n := by
    unfold weilQuadraticForm
    change ∑' n : ℕ, term n = _
    have h1 := hterm_summ.sum_add_tsum_compl (s := Bfin)
    rw [← h1]
    congr 1
    rw [← tsum_subtype_eq_of_support_subset (s := (Bfin : Set ℕ)ᶜ) (f := fun n => if n ∈ Bfin then 0 else term n)]
    · refine tsum_congr fun x => ?_
      have hx : x.1 ∉ Bfin := x.2
      simp [hx]
    · intro n hn
      simp only [Function.mem_support, ne_eq, ite_eq_left_iff, not_forall] at hn
      exact hn.1
  have hsplit_B : ∑ n ∈ Bfin, term n = (∑ n ∈ Smax, term n) + ∑ n ∈ Snear, term n := by
    have hdisj : Disjoint Smax Snear := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    have hunion : Smax ∪ Snear = Bfin := by
      ext n; simp only [Smax, Snear, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hq : Q n = M; exact Or.inl ⟨h, hq⟩; exact Or.inr ⟨h, hq⟩
    rw [← hunion, Finset.sum_union hdisj]
  -- Bound the three pieces!
  set scale : ℝ := (Real.pi / (4 * a ^ 3)) * Real.exp (M / (2 * a))
  have hscale_pos : 0 < scale := by positivity
  have hP1 : ∑ n ∈ Smax, term n ≤ scale * (-ε) := by
    rw [hlead_eq a ha_pos, hinv_a]
    exact mul_le_mul_of_nonneg_left hFt hscale_pos.le
  have hP2 : ∑ n ∈ Snear, term n ≤ scale * (Cnear * Real.exp (-η * t / 2)) := by
    calc ∑ n ∈ Snear, term n
        ≤ ∑ n ∈ Snear, |term n| := Finset.sum_le_sum fun n _ => le_abs_self _
      _ ≤ ∑ n ∈ Snear, (Real.pi / (4 * a ^ 3)) *
            (((Z.zero n).re - 1 / 2) ^ 2 + ((Z.zero n).im - γ₀) ^ 2) *
            Real.exp ((M - η) / (2 * a)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have h1 := (Complex.abs_re_le_norm _).trans_eq (norm_selfConv_weilOddGaussian a γ₀ ha_pos (Z.zero n))
          refine h1.trans (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hSnear_le n hn) (by positivity)))
            (by positivity))
      _ = scale * (Cnear * Real.exp (-η * t / 2)) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          have hexp : Real.exp ((M - η) / (2 * a)) = Real.exp (M / (2 * a)) * Real.exp (-η * t / 2) := by
            rw [← Real.exp_add]; congr 1; rw [ha_def]; field_simp [ht_pos.ne']; ring
          rw [hexp]; dsimp only [scale, Cnear]; ring
  have hP3 : (∑' n : ℕ, if n ∈ Bfin then (0 : ℝ) else term n) ≤
      scale * (Cfar * Real.exp (-(M + 1 / 2) * t / 2)) := by
    have hsumm_out : Summable (fun n : ℕ => if n ∈ Bfin then (0 : ℝ) else term n) := by
      refine Summable.of_norm_bounded (g := fun n => ‖term n‖) hterm_summ.norm fun n => ?_
      split_ifs <;> simp
    have hle_far := hsumm_out.tsum_le_tsum (g := fun n =>
      (Real.pi / (4 * a ^ 3)) * Real.exp (-(1 / 2) / (2 * a)) *
        ((1 / 4 + ((Z.zero n).im - γ₀) ^ 2) * Real.exp (-((Z.zero n).im - γ₀) ^ 2 / 2)))
      (fun n => by
        by_cases hn : n ∈ Bfin
        · simp only [hn, ↓reduceIte]; positivity
        · simp only [hn, ↓reduceIte]
          exact (le_abs_self _).trans (hterm_far_le n hn))
      (hfar_summ_base.mul_left _)
    rw [tsum_mul_left] at hle_far
    have hexp : Real.exp (-(1 / 2) / (2 * a)) = Real.exp (M / (2 * a)) * Real.exp (-(M + 1 / 2) * t / 2) := by
      rw [← Real.exp_add]; congr 1; rw [ha_def]; field_simp [ht_pos.ne']; ring
    rw [hexp] at hle_far
    calc (∑' n : ℕ, if n ∈ Bfin then (0 : ℝ) else term n)
        ≤ (Real.pi / (4 * a ^ 3)) * (Real.exp (M / (2 * a)) * Real.exp (-(M + 1 / 2) * t / 2)) * Cfar := hle_far
      _ = scale * (Cfar * Real.exp (-(M + 1 / 2) * t / 2)) := by dsimp only [scale]; ring
  have htot : weilQuadraticForm Z (weilOddGaussian a γ₀) ≤ scale * (-(ε / 2)) := by
    rw [hsplit_all, hsplit_B]
    have hbd := htail_bd t htT₀
    have hscale_tail : scale * (Cnear * Real.exp (-η * t / 2) +
        Cfar * Real.exp (-(M + 1 / 2) * t / 2)) ≤ scale * (ε / 2) :=
      mul_le_mul_of_nonneg_left hbd hscale_pos.le
    linarith
  have hneg : weilQuadraticForm Z (weilOddGaussian a γ₀) < 0 := by nlinarith
  linarith [hpos a ha_pos γ₀]

/-- **Weil's Equivalence for Any Infinite Critical-Strip Zero Spectrum**:
every zero lies on the critical line `Re(ρ) = 1/2` IF AND ONLY IF the Weil quadratic form is
non-negative for every admissible test function `f` (`WeilAdmissible f 1`)! -/
theorem weilPositivity_spectrum_iff_onLine (Z : ZeroSpectrum) :
    (∀ n : ℕ, (Z.zero n).re = 1 / 2) ↔
      (∀ f : ℝ → ℂ, WeilAdmissible f 1 → 0 ≤ weilQuadraticForm Z f) := by
  constructor
  · intro hon f hf
    exact weilQuadraticForm_nonneg_of_onLine Z hon hf one_pos
  · intro hpos
    exact onLine_of_weilQuadraticForm_nonneg Z fun a ha γ =>
      hpos (weilOddGaussian a γ) (weilAdmissible_weilOddGaussian ha γ 1)

/-- **Weil's Positivity Criterion for the Riemann Hypothesis (`RiemannHypothesis ↔ Weil ≥ 0`)**:
given a `ZeroSpectrum` enumerating the critical-strip zeros of `riemannZeta` (every critical-strip
zero appears in `Z.zero`, and every `Z.zero n` is a critical-strip zero of `riemannZeta`),
Mathlib's `RiemannHypothesis` is **logically equivalent** to non-negativity of the Weil quadratic
form `weilQuadraticForm Z f ≥ 0` over all admissible test functions `f`! -/
theorem riemannHypothesis_iff_weilPositivity (Z : ZeroSpectrum)
    (hsurj : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → ∃ n : ℕ, Z.zero n = s)
    (hsound : ∀ n : ℕ, riemannZeta (Z.zero n) = 0) :
    RiemannHypothesis ↔
      (∀ f : ℝ → ℂ, WeilAdmissible f 1 → 0 ≤ weilQuadraticForm Z f) := by
  rw [← weilPositivity_spectrum_iff_onLine Z, RHDirect.riemannHypothesis_iff_riemannZetaZerosOnLine]
  constructor
  · intro hRH n
    obtain ⟨h0, h1⟩ := Z.in_strip n
    have htriv : ¬ ∃ k : ℕ, Z.zero n = -2 * ((k : ℂ) + 1) := by
      rintro ⟨k, hk⟩
      have hre := congrArg Complex.re hk
      simp at hre
      linarith
    have hne1 : Z.zero n ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact hRH (Z.zero n) (hsound n) htriv hne1
  · intro hon s hz htriv _
    obtain ⟨h0, h1⟩ := RHDirect.riemannZeta_nontrivial_zero_mem_strip hz htriv
    obtain ⟨n, hn⟩ := hsurj s h0 h1 hz
    rw [← hn]
    exact hon n

/-- **Finite Zero-Set Weil Positivity Equivalence**:
for ANY finite set `Z : Finset ℂ`, all points in `Z` lie on `Re(ρ) = 1/2` IF AND ONLY IF
`∑_{ρ ∈ Z} Re(Φ_{f * f̃}(ρ)) ≥ 0` for all admissible test functions `f` (`WeilAdmissible f 1`)! -/
theorem weilPositivity_finset_iff_onLine (Z : Finset ℂ) :
    (∀ ρ ∈ Z, ρ.re = 1 / 2) ↔
      (∀ f : ℝ → ℂ, WeilAdmissible f 1 →
        0 ≤ ∑ ρ ∈ Z, (weilBilateralTransform (weilConv f (weilInvolution f)) ρ).re) := by
  constructor
  · intro hon f hf
    exact Finset.sum_nonneg fun ρ hρ =>
      (weilBilateralTransform_selfConv_re_nonneg_of_re_eq_half hf one_pos (hon ρ hρ)).1
  · intro hpos
    by_cases hZ : Z.Nonempty
    · classical
      intro ρ₀ hρ₀
      by_contra hoff
      set γ₀ : ℝ := ρ₀.im
      set Q : ℂ → ℝ := fun ρ => (ρ.re - 1 / 2) ^ 2 - (ρ.im - γ₀) ^ 2
      have hQ0 : 0 < Q ρ₀ := by
        dsimp only [Q, γ₀]; rw [sub_self, zero_pow (by norm_num), sub_zero]
        exact sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
      obtain ⟨ρMax, hρMax_mem, hρMax_ge⟩ := Z.exists_max_image Q hZ
      set M : ℝ := Q ρMax
      have hM_pos : 0 < M := lt_of_lt_of_le hQ0 (hρMax_ge ρ₀ hρ₀)
      set Smax : Finset ℂ := Z.filter fun ρ => Q ρ = M
      set Snear : Finset ℂ := Z.filter fun ρ => Q ρ ≠ M
      have hSmax_ne : Smax.Nonempty := ⟨ρMax, Finset.mem_filter.mpr ⟨hρMax_mem, rfl⟩⟩
      have hgap : ∃ η : ℝ, 0 < η ∧ ∀ ρ ∈ Snear, Q ρ ≤ M - η := by
        by_cases hSne : Snear.Nonempty
        · obtain ⟨ρ1, hρ1_mem, hρ1_ge⟩ := Snear.exists_max_image Q hSne
          have hlt : Q ρ1 < M :=
            lt_of_le_of_ne (hρMax_ge ρ1 (Finset.mem_filter.mp hρ1_mem).1) (Finset.mem_filter.mp hρ1_mem).2
          exact ⟨M - Q ρ1, by linarith, fun ρ hρ => by linarith [hρ1_ge ρ hρ]⟩
        · exact ⟨1, one_pos, fun ρ hρ => (hSne ⟨ρ, hρ⟩).elim⟩
      obtain ⟨η, hη_pos, hSnear_le⟩ := hgap
      set ω : ℂ → ℝ := fun ρ => |(ρ.re - 1 / 2) * (ρ.im - γ₀)|
      set W : Finset ℝ := Smax.image ω
      have hWne : W.Nonempty := hSmax_ne.image ω
      have hWnn : ∀ μ ∈ W, 0 ≤ μ := fun μ hμ => by
        obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.mp hμ; exact abs_nonneg _
      set mult : ℝ → ℝ := fun μ => ((Smax.filter fun ρ => ω ρ = μ).card : ℝ)
      have hmult_pos : ∀ μ ∈ W, 0 < mult μ := fun μ hμ => by
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hμ
        exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hρ, rfl⟩⟩)
      obtain ⟨ε, hε_pos, htrig⟩ := exists_trigPoly_neg_large hWne hWnn hmult_pos hM_pos
      set Cnear : ℝ := ∑ ρ ∈ Snear, ((ρ.re - 1 / 2) ^ 2 + (ρ.im - γ₀) ^ 2)
      have hlim : Tendsto (fun t : ℝ => Cnear * Real.exp (-η * t / 2)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun t : ℝ => (-η / 2) * t) atTop atBot :=
          Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
        have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul Cnear
        rw [mul_zero] at h2
        refine h2.congr fun t => ?_
        dsimp only [Function.comp_apply]; congr 2; ring
      obtain ⟨T1, hT1⟩ := Filter.eventually_atTop.mp
        (hlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2)))
      obtain ⟨t, ht, hFt⟩ := htrig (max 1 T1)
      have ht_pos : 0 < t := lt_of_lt_of_le one_pos ((le_max_left _ _).trans ht)
      set a : ℝ := 1 / t with ha_def
      have ha_pos : 0 < a := by positivity
      have hinv_a : 1 / a = t := by rw [ha_def]; field_simp [ht_pos.ne']
      set scale : ℝ := (Real.pi / (4 * a ^ 3)) * Real.exp (M / (2 * a))
      have hscale_pos : 0 < scale := by positivity
      have hsplit : ∑ ρ ∈ Z, (weilBilateralTransform
            (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) ρ).re =
          (∑ ρ ∈ Smax, (weilBilateralTransform
            (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) ρ).re) +
          (∑ ρ ∈ Snear, (weilBilateralTransform
            (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) ρ).re) := by
        have hdisj : Disjoint Smax Snear := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
        have hunion : Smax ∪ Snear = Z := by
          ext ρ; simp only [Smax, Snear, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h; by_cases hq : Q ρ = M; exact Or.inl ⟨h, hq⟩; exact Or.inr ⟨h, hq⟩
        rw [← hunion, Finset.sum_union hdisj]
      have hP1 : ∑ ρ ∈ Smax, (weilBilateralTransform
            (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) ρ).re ≤
          scale * (-ε) := by
        have hterm : ∀ ρ ∈ Smax, (weilBilateralTransform
            (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) ρ).re =
            scale * (-M * Real.cos (ω ρ * t) + 2 * ω ρ * Real.sin (ω ρ * t)) := fun ρ hρ => by
          have hQρ : (ρ.re - 1 / 2) ^ 2 - (ρ.im - γ₀) ^ 2 = M := (Finset.mem_filter.mp hρ).2
          rw [re_selfConv_weilOddGaussian a γ₀ ha_pos ρ, hQρ]
          congr 1
          set p : ℝ := (ρ.re - 1 / 2) * (ρ.im - γ₀)
          have hdiv : p / a = p * t := by rw [ha_def]; field_simp [ht_pos.ne']
          rw [hdiv]
          rcases le_or_gt 0 p with hp | hp
          · rw [show ω ρ = p from abs_of_nonneg hp]; ring
          · rw [show ω ρ = -p from abs_of_neg hp, show -p * t = -(p * t) by ring,
              Real.cos_neg, Real.sin_neg]; ring
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hscale_pos.le
        rw [← Finset.sum_fiberwise_of_maps_to (g := ω) (t := W) (fun ρ hρ => Finset.mem_image_of_mem ω hρ)]
        have hEq : ∑ μ ∈ W, ∑ ρ ∈ Smax.filter (fun k => ω k = μ),
            (-M * Real.cos (ω ρ * t) + 2 * ω ρ * Real.sin (ω ρ * t)) =
            ∑ μ ∈ W, mult μ * (-M * Real.cos (μ * t) + 2 * μ * Real.sin (μ * t)) := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          have hc : ∀ ρ ∈ Smax.filter (fun k => ω k = μ),
              -M * Real.cos (ω ρ * t) + 2 * ω ρ * Real.sin (ω ρ * t) =
              -M * Real.cos (μ * t) + 2 * μ * Real.sin (μ * t) := fun ρ hρ => by
            rw [(Finset.mem_filter.mp hρ).2]
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
        rw [hEq]; exact hFt
      have hP2 : ∑ ρ ∈ Snear, (weilBilateralTransform
            (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) ρ).re ≤
          scale * (Cnear * Real.exp (-η * t / 2)) := by
        calc ∑ ρ ∈ Snear, (weilBilateralTransform
                (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) ρ).re
            ≤ ∑ ρ ∈ Snear, |(weilBilateralTransform
                (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) ρ).re| :=
              Finset.sum_le_sum fun _ _ => le_abs_self _
          _ ≤ ∑ ρ ∈ Snear, (Real.pi / (4 * a ^ 3)) *
                ((ρ.re - 1 / 2) ^ 2 + (ρ.im - γ₀) ^ 2) * Real.exp ((M - η) / (2 * a)) := by
              refine Finset.sum_le_sum fun ρ hρ => ?_
              have h1 := (Complex.abs_re_le_norm _).trans_eq (norm_selfConv_weilOddGaussian a γ₀ ha_pos ρ)
              refine h1.trans (mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hSnear_le ρ hρ) (by positivity)))
                (by positivity))
          _ = scale * (Cnear * Real.exp (-η * t / 2)) := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
              have hexp : Real.exp ((M - η) / (2 * a)) = Real.exp (M / (2 * a)) * Real.exp (-η * t / 2) := by
                rw [← Real.exp_add]; congr 1; rw [ha_def]; field_simp [ht_pos.ne']; ring
              rw [hexp]; dsimp only [scale, Cnear]; ring
      have htail := (hT1 t ((le_max_right _ _).trans ht)).le
      have hscale_tail := mul_le_mul_of_nonneg_left htail hscale_pos.le
      have hneg : ∑ ρ ∈ Z, (weilBilateralTransform
            (weilConv (weilOddGaussian a γ₀) (weilInvolution (weilOddGaussian a γ₀))) ρ).re < 0 := by
        rw [hsplit]; nlinarith
      linarith [hpos (weilOddGaussian a γ₀) (weilAdmissible_weilOddGaussian ha_pos γ₀ 1)]
    · intro ρ hρ
      exact (hZ ⟨ρ, hρ⟩).elim

end RHDirect.Stage4ExplicitFormula

end
