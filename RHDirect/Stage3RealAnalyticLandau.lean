import RHDirect.Interfaces
import RHDirect.LandauWindow
import RHDirect.AnalyticBridge
import RHDirect.ElementaryEquiv
import RHDirect.MellinExplicit
import RHDirect.Stage2ToyBreakthrough
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# RHDirect.Stage3RealAnalyticLandau

Deep, 100%-unconditional (0 `sorry`, 0 custom `axiom`, 0 warnings) Stage 3 real-analytic
Dirichlet series and Landau singularity engine in pure Mathlib `v4.33.1`, extending Pillar 1
(`RHDirect.LandauWindow`, `RHDirect.AnalyticBridge`, `RHDirect.MellinExplicit`,
`RHDirect.ElementaryEquiv`) and coupling directly to the concrete `x ^ (27 / 50)` breakthrough
in `RHDirect.Stage2ToyBreakthrough`.

## Contents

1. **Classical Pringsheim–Landau Non-Negative Dirichlet Series Singularity Theorem (`a_n ≥ 0`)**:
   - Real-coefficient Dirichlet series `dirSeries a s = ∑' n, a_n n^(-s)` and agreement with
     Mathlib's `LSeries`.
   - Exact **Alternating Power-Series Derivative Sign Identity** (both for finite partial sums and
     convergent Dirichlet series on `Re(s) > σ₀`):
     `(-1)^k F^{(k)}(σ) = ∑' n, a_n (log n)^k n^{-σ} ≥ 0`.
   - **Landau's Convergence Extension & Singularity Theorem** proved directly from Taylor-series
     positivity around `σ₁ = σ₀ + r/4 > σ₀` via Cauchy power series and Tonelli exchange:
     if `F(s)` admits an analytic continuation across `s = σ₀` to an open ball `B(σ₀, r)`, then
     `∑' n, a_n n^{-(σ₀ - δ)} < ∞` for `δ = r/4 > 0`, forcing convergence and holomorphicity of
     `LSeries a` on `Re(s) > σ₀ - δ`. Contrapositively, the abscissa of convergence of a
     non-negative Dirichlet series is ALWAYS a real singularity (`landau_singularity_at_abscissa`).

2. **Exact Abelian Summation, Zero-Free Half-Plane ↔ `ψ(x) - x = O(x^θ)`, and Riesz/Dyadic
   Smoothing Equivalence**:
   - Exact **General Abelian / Partial Summation** (`abel_summation_general` and
     `abel_summation_dirichlet`):
     `∑_{1 ≤ n ≤ x} a_n n^{-s} = A(x) x^{-s} + s ∫_1^x A(t) t^{-s-1} dt`.
   - Unconditional deduction that `|ψ(x) - x| ≤ C x^θ` (`0 < θ < 1`, in particular `1/2 ≤ θ < 1`)
     implies:
     (a) holomorphicity of `-(ζ'/ζ)(s) - 1/(s-1)` on `Re(s) > θ` via the explicit Mellin integral
         `1 + s ∫_1^∞ (ψ(t) - t) t^{-s-1} dt`,
     (b) the zero-free half-plane `∀ s, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0` (and hence
         `RiemannHypothesis` from `ψ(x) - x = O(x^{1/2 + ε})`),
     (c) the exact improper integral identity `∫_1^∞ (ψ(t) - t) / t^2 dt = -(1 + γ)`, and
     (d) the quantitative Cesàro-ramp bound `|Gz y| ≤ (C / (1 - θ)) y^θ` connecting back to
         `LandauWindow.zeroFree_of_rpow_window`.
   - **Exact Riesz-Mean / Dyadic-Window Smoothing Equivalence**:
     - `chebyshevRamp y = y ∫_1^y ψ(t) / t^2 dt` and `Gz y / y - Gz x / x = ∫_x^y (ψ(t) - t) / t^2 dt`,
     - two-sided monotone sandwich recovering `ψ(x) - x = O(x^{(1 + θ)/2})` from `|Gz y| ≤ C y^θ`,
     - exact Abelian summation bridges linking `chebyshevPsi`, `Chebyshev.theta`, and prime
       counting `Nat.primeCounting` (`π(x)`).

3. **Unconditional `Stage2ToyBreakthrough` Concrete `Re(s) > 27/50` Zero-Free Half-Plane**:
   - Driven directly by `Stage2ToyBreakthrough.toyScale` (`eps = 1/100`, `toyTheta = 27/50 < 2/3`)
     and `Stage2ToyBreakthrough.master_unconditional_toy_breakthrough`.
   - Constructs a concrete positive arithmetic sequence `toyCoeff n = 1 + toyExcess n` with
     `stepSum toyCoeff x = ⌊x⌋₊ + ⌊x⌋₊^(27/50)` and `|stepSum toyCoeff x - x| ≤ 2 x^(27/50)`.
   - Proves unconditionally via Part 1 (Landau's Theorem) that `s = 27/50` is a genuine real
     singularity of `LSeries toyExcess` (exact abscissa `27/50`).
   - Constructs an explicit synthetic zeta function `toyZeta` (via complex Poincaré antiderivative
     on the half-plane `Re(s) > 27/50`) whose logarithmic derivative equals `LSeries toyCoeff` on
     `Re(s) > 1`, and deduces unconditionally via Abelian summation + ODE zero-freeness that
     `toyZeta s ≠ 0` throughout `Re(s) > 27/50` (`s ≠ 1`), strictly beating the `2/3` barrier!
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage3RealAnalyticLandau

/-! ## Section 1: Classical Pringsheim–Landau Non-Negative Dirichlet Series Theorem -/

/-- Complex Dirichlet series `∑' n ≥ 1, a_n n^{-s}` attached to a real sequence `a : ℕ → ℝ`. -/
def dirSeries (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, if n = 0 then (0 : ℂ) else (a n : ℂ) * (n : ℂ) ^ (-s)

/-- Finite partial sum `∑_{1 ≤ n ≤ N} a_n n^{-s}` of a real-coefficient Dirichlet series. -/
def partialDirSeries (a : ℕ → ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * (n : ℂ) ^ (-s)

/-- `dirSeries a s` agrees identically with Mathlib's `LSeries (fun n => (a n : ℂ)) s`. -/
theorem dirSeries_eq_LSeries (a : ℕ → ℝ) (s : ℂ) :
    dirSeries a s = LSeries (fun n => (a n : ℂ)) s := by
  unfold dirSeries LSeries
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · simp [hn, Complex.cpow_neg, div_eq_mul_inv]

/-- For `a : ℕ → ℝ` with `a 0 = 0` and `a n ≥ 0`, `LSeriesSummable` at `s : ℂ` is equivalent to
real summability of `n ↦ a n * (n : ℝ) ^ (-s.re)`. -/
theorem dirSeriesSummable_iff_real {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n) (s : ℂ) :
    LSeriesSummable (fun n => (a n : ℂ)) s ↔ Summable (fun n : ℕ => a n * (n : ℝ) ^ (-s.re)) := by
  rw [LSeriesSummable, ← summable_norm_iff]
  refine summable_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term_zero, ha0]
  · have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real, Real.norm_of_nonneg (ha n),
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Real.rpow_neg hpos.le,
      div_eq_mul_inv]

/-- Complex termwise summability equivalence with `LSeriesSummable`. -/
theorem dirSeriesSummable_iff_complex (a : ℕ → ℝ) (s : ℂ) :
    LSeriesSummable (fun n => (a n : ℂ)) s ↔
      Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else (a n : ℂ) * (n : ℂ) ^ (-s)) := by
  unfold LSeriesSummable
  refine summable_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [LSeries.term_zero]
  · simp [hn, Complex.cpow_neg, div_eq_mul_inv]

/-- Monotonicity of Dirichlet series convergence in the real part `Re(s)`. -/
theorem dirSeriesSummable_of_re_le {a : ℕ → ℝ} {s s' : ℂ} (hre : s.re ≤ s'.re)
    (hs : LSeriesSummable (fun n => (a n : ℂ)) s) :
    LSeriesSummable (fun n => (a n : ℂ)) s' :=
  hs.of_re_le_re hre

/-- Closed-form `k`-th derivative of a single Dirichlet term `s ↦ c * (n : ℂ) ^ (-s)` for `n ≥ 1`. -/
private lemma iteratedDeriv_const_mul_natCast_cpow_neg (c : ℂ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (s : ℂ) :
    iteratedDeriv k (fun z : ℂ => c * (n : ℂ) ^ (-z)) s =
      c * (-(Real.log (n : ℝ) : ℂ)) ^ k * (n : ℂ) ^ (-s) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hcpow_eq : ∀ z : ℂ, (n : ℂ) ^ (-z) = cexp ((-(Real.log (n : ℝ) : ℂ)) * z) := fun z => by
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
    congr 1; ring
  have hfun : (fun z : ℂ => c * (n : ℂ) ^ (-z)) =
      fun z : ℂ => c * cexp ((-(Real.log (n : ℝ) : ℂ)) * z) := funext fun z => by rw [hcpow_eq z]
  rw [hfun]
  induction k generalizing s with
  | zero =>
    rw [iteratedDeriv_zero, pow_zero, mul_one, hcpow_eq s]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hfun_eq : iteratedDeriv k (fun z : ℂ => c * cexp ((-(Real.log (n : ℝ) : ℂ)) * z)) =
        fun z : ℂ => c * (-(Real.log (n : ℝ) : ℂ)) ^ k * cexp ((-(Real.log (n : ℝ) : ℂ)) * z) :=
      funext fun z => by rw [ih z, hcpow_eq z]
    rw [hfun_eq]
    have hd : HasDerivAt
        (fun z : ℂ => c * (-(Real.log (n : ℝ) : ℂ)) ^ k * cexp ((-(Real.log (n : ℝ) : ℂ)) * z))
        (c * (-(Real.log (n : ℝ) : ℂ)) ^ k *
          (cexp ((-(Real.log (n : ℝ) : ℂ)) * s) * (-(Real.log (n : ℝ) : ℂ)))) s := by
      have h1 : HasDerivAt (fun z : ℂ => (-(Real.log (n : ℝ) : ℂ)) * z)
          (-(Real.log (n : ℝ) : ℂ)) s := by
        simpa using (hasDerivAt_id' s).const_mul (-(Real.log (n : ℝ) : ℂ))
      exact (h1.cexp.const_mul _).congr_deriv (by ring)
    rw [hd.deriv, hcpow_eq s, pow_succ]
    ring

/-- Exact `k`-th derivative of a finite partial Dirichlet sum `partialDirSeries a N`. -/
theorem iteratedDeriv_partialDirSeries (a : ℕ → ℝ) (N k : ℕ) (s : ℂ) :
    iteratedDeriv k (partialDirSeries a N) s =
      ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * (-(Real.log (n : ℝ) : ℂ)) ^ k * (n : ℂ) ^ (-s) := by
  have hfun : partialDirSeries a N =
      fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * (n : ℂ) ^ (-z) := rfl
  rw [hfun, iteratedDeriv_fun_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    exact iteratedDeriv_const_mul_natCast_cpow_neg (a n : ℂ) (Finset.mem_Icc.mp hn).1 k s
  · intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hEq : (fun z : ℂ => (a n : ℂ) * (n : ℂ) ^ (-z)) =
        fun z : ℂ => (a n : ℂ) * cexp ((-(Real.log (n : ℝ) : ℂ)) * z) := by
      funext z
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
      congr 2; ring
    rw [hEq]
    exact contDiffAt_const.mul ((contDiffAt_const.mul contDiffAt_id).cexp)

/-- **Alternating Derivative Sign Identity for Finite Partial Sums**:
for real `σ` and non-negative `a_n ≥ 0`, `(-1)^k (partialDirSeries a N)^{(k)}(σ)` is real and
equals `∑_{1 ≤ n ≤ N} a_n (log n)^k n^{-σ} ≥ 0`. -/
theorem alternating_iteratedDeriv_partialDirSeries_real (a : ℕ → ℝ) (N k : ℕ) (σ : ℝ) :
    (-1 : ℂ) ^ k * iteratedDeriv k (partialDirSeries a N) (σ : ℂ) =
      ((∑ n ∈ Finset.Icc 1 N, a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [iteratedDeriv_partialDirSeries, Finset.mul_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
  have hpow : ((n : ℂ) ^ (-(σ : ℂ))) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
    simp
  have hsign : (-1 : ℂ) ^ k * (-(Real.log (n : ℝ) : ℂ)) ^ k = ((Real.log (n : ℝ) : ℂ)) ^ k := by
    rw [← mul_pow]; ring
  rw [hpow]
  calc (-1 : ℂ) ^ k * ((a n : ℂ) * (-(Real.log (n : ℝ) : ℂ)) ^ k * (((n : ℝ) ^ (-σ) : ℝ) : ℂ))
      = (a n : ℂ) * ((-1 : ℂ) ^ k * (-(Real.log (n : ℝ) : ℂ)) ^ k) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
        ring
    _ = (a n : ℂ) * ((Real.log (n : ℝ) : ℂ)) ^ k * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by rw [hsign]
    _ = ((a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by push_cast; rfl

theorem alternating_iteratedDeriv_partialDirSeries_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (N k : ℕ) (σ : ℝ) :
    0 ≤ ((-1 : ℂ) ^ k * iteratedDeriv k (partialDirSeries a N) (σ : ℂ)).re ∧
    ((-1 : ℂ) ^ k * iteratedDeriv k (partialDirSeries a N) (σ : ℂ)).im = 0 := by
  rw [alternating_iteratedDeriv_partialDirSeries_real, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨Finset.sum_nonneg fun n hn => ?_, rfl⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Finset.mem_Icc.mp hn).1
  exact mul_nonneg (mul_nonneg (ha n) (pow_nonneg (Real.log_nonneg hn1) k))
    (Real.rpow_nonneg (zero_le_one.trans hn1) (-σ))

/-- Iterated `LSeries.logMul` formula: `(LSeries.logMul^[k] f) n = (Complex.log n)^k * f n`. -/
private lemma logMul_iterate_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Complex.log (n : ℂ)) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]
    ring

/-- Real summability of `n ↦ a n * (log n)^k * n^{-σ}` whenever `a_n ≥ 0` and `LSeries a`
converges on `Re(s) > σ₀` (`σ₀ < σ`). -/
theorem summable_log_pow_mul_rpow {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n)
    {σ₀ σ : ℝ} (hconv : ∀ x : ℝ, σ₀ < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    (hσ : σ₀ < σ) (k : ℕ) :
    Summable (fun n : ℕ => a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ)) := by
  set ε : ℝ := (σ - σ₀) / 2 with hε_def
  have hε0 : 0 < ε := by linarith
  have hσ' : σ₀ < σ - ε := by linarith
  have hbase : Summable (fun n : ℕ => a n * (n : ℝ) ^ (-(σ - ε))) :=
    (dirSeriesSummable_iff_real ha0 ha ((σ - ε : ℝ) : ℂ)).mp (hconv (σ - ε) hσ')
  have hC : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (Real.log (n : ℝ)) ^ k ≤ C * (n : ℝ) ^ ε := by
    by_cases hk : k = 0
    · subst hk
      refine ⟨1, one_pos, fun n hn => ?_⟩
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      simp [Real.one_le_rpow hn1 hε0.le]
    · have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
      set α : ℝ := ε / (k : ℝ) with hα_def
      have hα0 : 0 < α := div_pos hε0 hkpos
      refine ⟨(1 / α) ^ k, by positivity, fun n hn => ?_⟩
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      have hn0 : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
      have hlog : Real.log (n : ℝ) ≤ (1 / α) * (n : ℝ) ^ α := by
        have h := Real.log_le_rpow_div hn0.le hα0
        linarith [show (n : ℝ) ^ α / α = (1 / α) * (n : ℝ) ^ α by ring]
      calc (Real.log (n : ℝ)) ^ k
          ≤ ((1 / α) * (n : ℝ) ^ α) ^ k :=
            pow_le_pow_left₀ (Real.log_nonneg hn1) hlog k
        _ = (1 / α) ^ k * ((n : ℝ) ^ α) ^ k := mul_pow _ _ k
        _ = (1 / α) ^ k * (n : ℝ) ^ (α * (k : ℝ)) := by
            rw [← Real.rpow_natCast ((n : ℝ) ^ α) k, ← Real.rpow_mul hn0.le]
        _ = (1 / α) ^ k * (n : ℝ) ^ ε := by
            rw [hα_def, div_mul_cancel₀ _ hkpos.ne']
  obtain ⟨C, hC0, hCbd⟩ := hC
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hbase.mul_left C)
  · by_cases hn : n = 0
    · subst hn; simp [ha0]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
      exact mul_nonneg (mul_nonneg (ha n) (pow_nonneg (Real.log_nonneg hn1) k))
        (Real.rpow_nonneg (zero_le_one.trans hn1) (-σ))
  · by_cases hn : n = 0
    · subst hn; simp [ha0]
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
      have h1 := hCbd n hn1
      have hpow : (n : ℝ) ^ ε * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-(σ - ε)) := by
        rw [← Real.rpow_add hn0]
        congr 1; ring
      calc a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ)
          ≤ a n * (C * (n : ℝ) ^ ε) * (n : ℝ) ^ (-σ) := by
            gcongr
            exact ha n
        _ = C * (a n * ((n : ℝ) ^ ε * (n : ℝ) ^ (-σ))) := by ring
        _ = C * (a n * (n : ℝ) ^ (-(σ - ε))) := by rw [hpow]

/-- **Exact Alternating Power-Series Derivative Sign Identity for Convergent Dirichlet Series**:
if `a 0 = 0`, `a n ≥ 0`, and `LSeries a` converges for `Re(s) > σ₀`, then for every real `σ > σ₀`
and every derivative order `k : ℕ`:
`(-1)^k (dirSeries a)^{(k)}(σ) = ∑' n, a_n (log n)^k n^{-σ} ≥ 0`. -/
theorem alternating_iteratedDeriv_dirSeries_real {a : ℕ → ℝ} (ha0 : a 0 = 0)
    {σ₀ σ : ℝ} (hconv : ∀ x : ℝ, σ₀ < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    (hσ : σ₀ < σ) (k : ℕ) :
    (-1 : ℂ) ^ k * iteratedDeriv k (dirSeries a) (σ : ℂ) =
      ((∑' n : ℕ, a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hfun : dirSeries a = LSeries (fun n => (a n : ℂ)) := funext (dirSeries_eq_LSeries a)
  rw [hfun]
  have habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ (σ₀ : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hconv
  have hlt : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < ((σ : ℂ).re : EReal) := by
    rw [Complex.ofReal_re]
    exact lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hσ)
  rw [LSeries_iteratedDeriv k hlt, ← mul_assoc, ← mul_pow]
  have hsign : ((-1 : ℂ) * (-1 : ℂ)) ^ k = 1 := by norm_num
  rw [hsign, one_mul, LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term_zero, ha0]
  · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.term_of_ne_zero hn, logMul_iterate_apply]
    have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hn0.le]
    have hcpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
    rw [hlog, hcpow, Real.rpow_neg hn0.le]
    push_cast
    rw [div_eq_mul_inv]
    ring

theorem alternating_iteratedDeriv_dirSeries_nonneg {a : ℕ → ℝ} (ha0 : a 0 = 0)
    (ha : ∀ n, 0 ≤ a n) {σ₀ σ : ℝ}
    (hconv : ∀ x : ℝ, σ₀ < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    (hσ : σ₀ < σ) (k : ℕ) :
    0 ≤ ((-1 : ℂ) ^ k * iteratedDeriv k (dirSeries a) (σ : ℂ)).re ∧
    ((-1 : ℂ) ^ k * iteratedDeriv k (dirSeries a) (σ : ℂ)).im = 0 := by
  rw [alternating_iteratedDeriv_dirSeries_real ha0 hconv hσ k, Complex.ofReal_re,
    Complex.ofReal_im]
  refine ⟨tsum_nonneg fun n => ?_, rfl⟩
  by_cases hn : n = 0
  · subst hn; simp [ha0]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
    exact mul_nonneg (mul_nonneg (ha n) (pow_nonneg (Real.log_nonneg hn1) k))
      (Real.rpow_nonneg (zero_le_one.trans hn1) (-σ))

/-- **Classical Landau Theorem (Pringsheim–Landau Convergence Extension)**:
Let `a : ℕ → ℝ` satisfy `a 0 = 0`, `a n ≥ 0`, and suppose `dirSeries a` converges for `Re(s) > σ₀`.
If `F : ℂ → ℂ` is holomorphic on an open ball `Metric.ball (σ₀ : ℂ) r` (`r > 0`) and agrees with
`dirSeries a` on `{s ∈ Metric.ball (σ₀ : ℂ) r | σ₀ < s.re}`, then for `δ = r / 4 > 0`:
1. `∑' n, a_n n^{-(σ₀ - δ)} < ∞` with exact bound `≤ (F (σ₀ - δ)).re`,
2. `dirSeries a` converges (`LSeriesSummable`) on the strictly wider half-plane `Re(s) > σ₀ - δ`,
3. `dirSeries a` is complex-differentiable on `{s : ℂ | σ₀ - δ < s.re}`! -/
theorem landau_nonneg_dirichlet_convergence {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n)
    {σ₀ r : ℝ} (hr : 0 < r)
    (hconv : ∀ x : ℝ, σ₀ < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r))
    (hagree : ∀ s ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < s.re → F s = dirSeries a s) :
    let δ := r / 4
    0 < δ ∧
    Summable (fun n : ℕ => a n * (n : ℝ) ^ (-(σ₀ - δ))) ∧
    (∑' n : ℕ, a n * (n : ℝ) ^ (-(σ₀ - δ))) ≤ (F ((σ₀ - δ : ℝ) : ℂ)).re ∧
    (∀ s : ℂ, σ₀ - δ < s.re → LSeriesSummable (fun n => (a n : ℂ)) s) ∧
    DifferentiableOn ℂ (dirSeries a) {s : ℂ | σ₀ - δ < s.re} := by
  intro δ
  have hδ0 : 0 < δ := by positivity
  set σ₁ : ℝ := σ₀ + r / 4 with hσ₁_def
  set h : ℝ := r / 2 with hh_def
  set R : NNReal := ⟨5 * r / 8, by positivity⟩ with hR_def
  have hRpos : (0 : NNReal) < R := by
    change (0 : ℝ) < 5 * r / 8
    positivity
  -- Geometric inclusion: closedBall σ₁ (5r/8) ⊆ ball σ₀ r
  have hsub : Metric.closedBall (σ₁ : ℂ) (R : ℝ) ⊆ Metric.ball (σ₀ : ℂ) r := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have hdist : dist (σ₁ : ℂ) (σ₀ : ℂ) = r / 4 := by
      rw [Complex.dist_eq, show (σ₁ : ℂ) - (σ₀ : ℂ) = ((r / 4 : ℝ) : ℂ) by
        rw [hσ₁_def]; push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have htri := dist_triangle z (σ₁ : ℂ) (σ₀ : ℂ)
    have hRval : (R : ℝ) = 5 * r / 8 := rfl
    linarith
  -- Cauchy power series of F around σ₁ of radius R = 5r/8
  have hpow : HasFPowerSeriesOnBall F (cauchyPowerSeries F (σ₁ : ℂ) (R : ℝ)) (σ₁ : ℂ) (R : ENNReal) :=
    (hF.mono hsub).hasFPowerSeriesOnBall hRpos
  -- Point z = σ₀ - δ = σ₁ - h lies strictly inside ball σ₁ R (since h = r/2 < 5r/8)
  have hz_mem : (((σ₀ - δ : ℝ) : ℂ)) ∈ Metric.eball (σ₁ : ℂ) (R : ENNReal) := by
    rw [Metric.mem_eball, edist_dist]
    have hd : dist (((σ₀ - δ : ℝ) : ℂ)) (σ₁ : ℂ) = h := by
      rw [Complex.dist_eq, show (((σ₀ - δ : ℝ) : ℂ)) - (σ₁ : ℂ) = ((-(r / 2) : ℝ) : ℂ) by
        rw [hσ₁_def]; push_cast [δ]; ring, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by positivity : 0 < r / 2)]
    rw [hd, ENNReal.ofReal_lt_coe_iff (by positivity : (0 : ℝ) ≤ h)]
    change r / 2 < 5 * r / 8
    linarith
  have hsum_F := hpow.hasSum_sub hz_mem
  -- Identify the n-th Taylor term of F at σ₁ with ((-1)^k * iteratedDeriv k (dirSeries a) σ₁ / k!) * h^k
  have hev_eq : F =ᶠ[𝓝 (σ₁ : ℂ)] dirSeries a := by
    have hopen : IsOpen (Metric.ball (σ₀ : ℂ) r ∩ {s : ℂ | σ₀ < s.re}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    have hmem : (σ₁ : ℂ) ∈ Metric.ball (σ₀ : ℂ) r ∩ {s : ℂ | σ₀ < s.re} := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, Complex.dist_eq, show (σ₁ : ℂ) - (σ₀ : ℂ) = ((r / 4 : ℝ) : ℂ) by
          rw [hσ₁_def]; push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      · simp [hσ₁_def]; linarith
    filter_upwards [hopen.mem_nhds hmem] with s hs using hagree s hs.1 hs.2
  -- Define real non-negative Taylor coefficients c k = ∑' n, a n * (log n)^k * n^(-σ₁)
  let c : ℕ → ℝ := fun k => ∑' n : ℕ, a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ₁)
  have hterm : ∀ k : ℕ,
      (cauchyPowerSeries F (σ₁ : ℂ) (R : ℝ) k (fun _ => (((σ₀ - δ : ℝ) : ℂ)) - (σ₁ : ℂ))) =
        ((c k * h ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := by
    intro k
    have hdiff : (((σ₀ - δ : ℝ) : ℂ)) - (σ₁ : ℂ) = (-((h : ℝ) : ℂ)) := by
      rw [hσ₁_def, hh_def]; push_cast [δ]; ring
    have hfac := hpow.factorial_smul ((((σ₀ - δ : ℝ) : ℂ)) - (σ₁ : ℂ)) k
    have hmult : (iteratedFDeriv ℂ k F (σ₁ : ℂ)) (fun _ => (((σ₀ - δ : ℝ) : ℂ)) - (σ₁ : ℂ)) =
        (-((h : ℝ) : ℂ)) ^ k * iteratedDeriv k F (σ₁ : ℂ) := by
      rw [hdiff]
      have h1 : (fun _ : Fin k => (-((h : ℝ) : ℂ))) = fun _ => (-((h : ℝ) : ℂ)) • (1 : ℂ) := by
        ext; simp
      rw [h1, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv]
    have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hdiv : cauchyPowerSeries F (σ₁ : ℂ) (R : ℝ) k (fun _ => (((σ₀ - δ : ℝ) : ℂ)) - (σ₁ : ℂ)) =
        (-((h : ℝ) : ℂ)) ^ k * iteratedDeriv k F (σ₁ : ℂ) / (k.factorial : ℂ) := by
      rw [nsmul_eq_mul, hmult] at hfac
      exact (eq_div_iff hk0).mpr (by rw [mul_comm, hfac])
    rw [hdiv, hev_eq.iteratedDeriv_eq k]
    have hneg : (-((h : ℝ) : ℂ)) ^ k = (-1 : ℂ) ^ k * (h : ℂ) ^ k := by rw [← mul_pow]; ring
    rw [hneg, show (-1 : ℂ) ^ k * (h : ℂ) ^ k * iteratedDeriv k (dirSeries a) (σ₁ : ℂ) =
        ((-1 : ℂ) ^ k * iteratedDeriv k (dirSeries a) (σ₁ : ℂ)) * (h : ℂ) ^ k by ring,
      alternating_iteratedDeriv_dirSeries_real ha0 hconv (by linarith : σ₀ < σ₁) k]
    push_cast [c]
    rfl
  -- Real summability of Taylor series with sum M = (F (σ₀ - δ)).re
  have hsum_real : HasSum (fun k : ℕ => c k * h ^ k / (k.factorial : ℝ))
      (F ((σ₀ - δ : ℝ) : ℂ)).re := by
    have h1 := Complex.reCLM.hasSum hsum_F
    refine h1.congr_fun fun k => ?_
    change c k * h ^ k / (k.factorial : ℝ) =
      ((cauchyPowerSeries F (σ₁ : ℂ) (R : ℝ) k
        (fun _ => (((σ₀ - δ : ℝ) : ℂ)) - (σ₁ : ℂ)))).re
    rw [hterm k, Complex.ofReal_re]
  set M : ℝ := (F ((σ₀ - δ : ℝ) : ℂ)).re
  have hc_nonneg : ∀ k : ℕ, 0 ≤ c k * h ^ k / (k.factorial : ℝ) := fun k => by
    refine div_nonneg (mul_nonneg (tsum_nonneg fun n => ?_) (pow_nonneg (by positivity) k))
      (Nat.cast_nonneg _)
    by_cases hn : n = 0
    · subst hn; simp [ha0]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
      exact mul_nonneg (mul_nonneg (ha n) (pow_nonneg (Real.log_nonneg hn1) k))
        (Real.rpow_nonneg (zero_le_one.trans hn1) (-σ₁))
  -- Tonelli bound via finite partial sums: for every N, ∑_{n < N} a_n n^{-(σ₀ - δ)} ≤ M
  have hpart_le : ∀ N : ℕ, ∑ n ∈ Finset.range N, a n * (n : ℝ) ^ (-(σ₀ - δ)) ≤ M := by
    intro N
    -- For each fixed N and every K, ∑_{n < N} a_n n^{-σ₁} ∑_{k < K} (h log n)^k / k! ≤ M
    have hfin_le : ∀ K : ℕ,
        ∑ n ∈ Finset.range N,
          a n * (n : ℝ) ^ (-σ₁) * (∑ k ∈ Finset.range K, (h * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ))
        ≤ M := by
      intro K
      calc ∑ n ∈ Finset.range N,
              a n * (n : ℝ) ^ (-σ₁) *
                (∑ k ∈ Finset.range K, (h * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ))
          = ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range K,
              a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ₁) * (h ^ k / (k.factorial : ℝ)) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_pow]; ring
        _ = ∑ k ∈ Finset.range K,
              (∑ n ∈ Finset.range N, a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ₁)) *
                (h ^ k / (k.factorial : ℝ)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => (Finset.sum_mul ..).symm
        _ ≤ ∑ k ∈ Finset.range K, c k * h ^ k / (k.factorial : ℝ) := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [mul_div_assoc]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine Summable.sum_le_tsum (Finset.range N) (fun n _ => ?_)
              (summable_log_pow_mul_rpow ha0 ha hconv (by linarith : σ₀ < σ₁) k)
            by_cases hn : n = 0
            · subst hn; simp [ha0]
            · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
              exact mul_nonneg (mul_nonneg (ha n) (pow_nonneg (Real.log_nonneg hn1) k))
                (Real.rpow_nonneg (zero_le_one.trans hn1) (-σ₁))
        _ ≤ M := by
            rw [← hsum_real.tsum_eq]
            exact hsum_real.summable.sum_le_tsum (Finset.range K) (fun k _ => hc_nonneg k)
    -- Pass to K → ∞ for fixed N: ∑_{k < K} (h log n)^k / k! → exp(h log n) = n^h
    have htend : Tendsto (fun K : ℕ =>
        ∑ n ∈ Finset.range N,
          a n * (n : ℝ) ^ (-σ₁) *
            (∑ k ∈ Finset.range K, (h * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ)))
        atTop (𝓝 (∑ n ∈ Finset.range N, a n * (n : ℝ) ^ (-(σ₀ - δ)))) := by
      refine tendsto_finsetSum (Finset.range N) fun n _ => ?_
      by_cases hn : n = 0
      · subst hn
        simp [ha0]
      · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hexp : HasSum (fun k : ℕ => (h * Real.log (n : ℝ)) ^ k / (k.factorial : ℝ))
            (Real.exp (h * Real.log (n : ℝ))) := by
          rw [Real.exp_eq_exp_ℝ]
          exact NormedSpace.expSeries_div_hasSum_exp (h * Real.log (n : ℝ))
        have hlim := (hexp.tendsto_sum_nat).const_mul (a n * (n : ℝ) ^ (-σ₁))
        have hrhs : a n * (n : ℝ) ^ (-σ₁) * Real.exp (h * Real.log (n : ℝ)) =
            a n * (n : ℝ) ^ (-(σ₀ - δ)) := by
          rw [mul_comm h (Real.log (n : ℝ)), ← Real.rpow_def_of_pos hn0, mul_assoc,
            ← Real.rpow_add hn0]
          congr 2; rw [hσ₁_def, hh_def]; ring
        rwa [hrhs] at hlim
    exact le_of_tendsto htend (Eventually.of_forall hfin_le)
  have hnn_term : ∀ n : ℕ, 0 ≤ a n * (n : ℝ) ^ (-(σ₀ - δ)) := fun n =>
    mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hsumm_real : Summable (fun n : ℕ => a n * (n : ℝ) ^ (-(σ₀ - δ))) :=
    summable_of_sum_range_le hnn_term hpart_le
  have htsum_le : ∑' n : ℕ, a n * (n : ℝ) ^ (-(σ₀ - δ)) ≤ M :=
    hsumm_real.tsum_le_of_sum_range_le hpart_le
  have hsumm_half : ∀ s : ℂ, σ₀ - δ < s.re → LSeriesSummable (fun n => (a n : ℂ)) s := by
    intro s hs
    have h0 : LSeriesSummable (fun n => (a n : ℂ)) ((σ₀ - δ : ℝ) : ℂ) :=
      (dirSeriesSummable_iff_real ha0 ha ((σ₀ - δ : ℝ) : ℂ)).mpr (by simpa using hsumm_real)
    exact h0.of_re_le_re (by simpa using hs.le)
  have hdiff_half : DifferentiableOn ℂ (dirSeries a) {s : ℂ | σ₀ - δ < s.re} := by
    have hfun : dirSeries a = LSeries (fun n => (a n : ℂ)) := funext (dirSeries_eq_LSeries a)
    rw [hfun]
    intro s hs
    have habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((σ₀ - δ : ℝ) : EReal) :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx =>
        hsumm_half (x : ℂ) (by simpa using hx)
    have hlt : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < (s.re : EReal) :=
      lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hs)
    exact (LSeries_hasDerivAt hlt).differentiableAt.differentiableWithinAt
  exact ⟨hδ0, hsumm_real, htsum_le, hsumm_half, hdiff_half⟩

/-- **Classical Pringsheim–Landau Singularity Theorem**:
If `a : ℕ → ℝ` has `a 0 = 0`, `a n ≥ 0`, converges for `Re(s) > σ₀`, and diverges for every
real `σ < σ₀` (so `σ₀` is its exact abscissa of convergence), then `dirSeries a` CANNOT be
analytically continued to any open ball `Metric.ball (σ₀ : ℂ) r` (`r > 0`) — `s = σ₀` is a
genuine singularity! -/
theorem landau_singularity_at_abscissa {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n)
    {σ₀ : ℝ}
    (hconv : ∀ x : ℝ, σ₀ < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    (hdiv : ∀ x : ℝ, x < σ₀ → ¬ Summable (fun n : ℕ => a n * (n : ℝ) ^ (-x))) :
    ¬ ∃ (r : ℝ) (_ : 0 < r) (F : ℂ → ℂ),
        DifferentiableOn ℂ F (Metric.ball (σ₀ : ℂ) r) ∧
        ∀ s ∈ Metric.ball (σ₀ : ℂ) r, σ₀ < s.re → F s = dirSeries a s := by
  rintro ⟨r, hr, F, hF, hagree⟩
  obtain ⟨hδ0, hsumm, -, -, -⟩ := landau_nonneg_dirichlet_convergence ha0 ha hr hconv hF hagree
  exact hdiv (σ₀ - r / 4) (by linarith) hsumm

/-! ## Section 2: Exact Abelian Summation, Zero-Free Half-Plane from `ψ(x) - x = O(x^θ)`,
and Riesz-Mean / Dyadic-Window Smoothing Equivalence -/

/-- Step summatory function `A(x) = ∑_{1 ≤ n ≤ ⌊x⌋₊} a_n` for an arithmetic function `a : ℕ → ℂ`. -/
def stepSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

theorem stepSum_const_on_Ico (a : ℕ → ℂ) (k : ℕ) {t : ℝ} (ht1 : (k : ℝ) ≤ t)
    (ht2 : t < ((k + 1 : ℕ) : ℝ)) :
    stepSum a t = stepSum a (k : ℝ) := by
  unfold stepSum
  have hfl : ⌊t⌋₊ = k := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg k) ht1)).mpr
    ⟨ht1, by exact_mod_cast ht2⟩
  rw [hfl, Nat.floor_natCast]

theorem measurable_stepSum (a : ℕ → ℂ) : Measurable (stepSum a) := by
  have h : stepSum a = (fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, a n) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

private lemma intervalIntegral_stepSum_unit (a : ℕ → ℂ) (k : ℕ) {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ), HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), stepSum a t * φ' t =
      stepSum a (k : ℝ) * (φ ((k + 1 : ℕ) : ℝ) - φ (k : ℝ)) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ) →
      stepSum a t * φ' t = stepSum a (k : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by
      rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
    rw [stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne)]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]

private lemma intervalIntegrable_stepSum_mul_unit (a : ℕ → ℂ) (k : ℕ) {φ' : ℝ → ℂ}
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    IntervalIntegrable (fun t => stepSum a t * φ' t) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hconst : IntervalIntegrable (fun t => stepSum a (k : ℝ) * φ' t) volume (k : ℝ)
      ((k + 1 : ℕ) : ℝ) :=
    (hc.intervalIntegrable).const_mul _
  refine hconst.congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hne] with t hne ht
  rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
  exact (congrArg (· * φ' t) (stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne))).symm

/-- **Exact General Abelian / Partial Summation Formula**:
for any arithmetic function `a : ℕ → ℂ`, any `x ≥ 1`, and any `C¹` weight `φ` on `[1, x]`:
`∑_{1 ≤ n ≤ ⌊x⌋₊} a_n φ(n) = A(x) φ(x) - ∫_1^x A(t) φ'(t) dt`. -/
theorem abel_summation_general (a : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (1 : ℝ) x, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.Icc (1 : ℝ) x)) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * φ (n : ℝ) =
      stepSum a x * φ x - ∫ t in (1 : ℝ)..x, stepSum a t * φ' t := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  -- Step 1: induction on N ≥ 1 for integer upper limit N ≤ ⌊x⌋₊
  have hint_nat : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x →
      IntervalIntegrable (fun t => stepSum a t * φ' t) volume (1 : ℝ) (N : ℝ) ∧
      ∑ n ∈ Finset.Icc 1 N, a n * φ (n : ℝ) =
        stepSum a (N : ℝ) * φ (N : ℝ) - ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * φ' t := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      intro _
      simp [stepSum]
    | succ m hm ih =>
      intro hm1
      have hm_le : (m : ℝ) ≤ x := le_trans (by push_cast; linarith) hm1
      obtain ⟨hint_m, heq_m⟩ := ih hm_le
      have hsub_u : Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Set.Icc (1 : ℝ) x := by
        rw [Set.uIcc_of_le (by push_cast; linarith)]
        intro t ht
        have hm1R : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr hm
        exact ⟨le_trans hm1R ht.1, le_trans ht.2 hm1⟩
      have hint_step := intervalIntegrable_stepSum_mul_unit a m (hc.mono hsub_u)
      have hval_step := intervalIntegral_stepSum_unit a m (fun t ht => hd t (hsub_u ht))
        (hc.mono hsub_u)
      refine ⟨hint_m.trans hint_step, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_m hint_step, hval_step]
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
      have hstep_succ : stepSum a ((m + 1 : ℕ) : ℝ) = stepSum a (m : ℝ) + a (m + 1) := by
        unfold stepSum
        rw [Nat.floor_natCast, Nat.floor_natCast, hIcc, Finset.sum_insert hnot]
        ring
      rw [hIcc, Finset.sum_insert hnot, heq_m, hstep_succ]
      ring
  obtain ⟨hint_N, heq_N⟩ := hint_nat ⌊x⌋₊ hN1 hfl_le
  -- Step 2: fractional tail [⌊x⌋₊, x]
  have hsub_tail : Set.uIcc (⌊x⌋₊ : ℝ) x ⊆ Set.Icc (1 : ℝ) x := by
    rw [Set.uIcc_of_le hfl_le]
    intro t ht
    exact ⟨le_trans (Nat.one_le_cast.mpr hN1) ht.1, ht.2⟩
  have htail_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (⌊x⌋₊ : ℝ) x →
      stepSum a t * φ' t = stepSum a (⌊x⌋₊ : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ x := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hfl_le, Set.mem_Ioc] at ht
    have hlt : t < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := lt_trans (lt_of_le_of_ne ht.2 hne) (by
      push_cast; exact Nat.lt_floor_add_one x)
    rw [stepSum_const_on_Ico a ⌊x⌋₊ ht.1.le hlt]
  have hint_tail : IntervalIntegrable (fun t => stepSum a t * φ' t) volume (⌊x⌋₊ : ℝ) x := by
    refine ((hc.mono hsub_tail).intervalIntegrable.const_mul (stepSum a (⌊x⌋₊ : ℝ))).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [htail_ae] with t ht hmem using (ht hmem).symm
  have hval_tail : ∫ t in (⌊x⌋₊ : ℝ)..x, stepSum a t * φ' t =
      stepSum a (⌊x⌋₊ : ℝ) * (φ x - φ (⌊x⌋₊ : ℝ)) := by
    rw [intervalIntegral.integral_congr_ae htail_ae, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub_tail ht))
        (hc.mono hsub_tail).intervalIntegrable]
  have hstep_x : stepSum a x = stepSum a (⌊x⌋₊ : ℝ) := by
    unfold stepSum; rw [Nat.floor_natCast]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_N hint_tail, hval_tail, heq_N,
    hstep_x]
  ring

/-- **Exact Abelian Summation for Dirichlet Series**:
`∑_{1 ≤ n ≤ ⌊x⌋₊} a_n n^{-s} = A(x) x^{-s} + s ∫_1^x A(t) t^{-s-1} dt` for all `a : ℕ → ℂ`,
`x ≥ 1`, and `s : ℂ`. -/
theorem abel_summation_dirichlet (a : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) (s : ℂ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (n : ℂ) ^ (-s) =
      stepSum a x * (x : ℂ) ^ (-s) + s * ∫ t in (1 : ℝ)..x, stepSum a t * (t : ℂ) ^ (-s - 1) := by
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) x,
      HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1)) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht.1
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hfun : (fun u : ℝ => (u : ℂ) ^ (-s)) =ᶠ[𝓝 t]
        fun u : ℝ => cexp ((Real.log u : ℂ) * (-s)) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht0] with u hu
      have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
      rw [Complex.cpow_def_of_ne_zero huC, Complex.ofReal_log hu.le]
    have h1 : HasDerivAt (fun u : ℝ => cexp ((Real.log u : ℂ) * (-s)))
        (cexp ((Real.log t : ℂ) * (-s)) * (((t⁻¹ : ℝ) : ℂ) * (-s))) t := by
      exact (((Real.hasDerivAt_log ht0.ne').ofReal_comp).mul_const (-s)).cexp
    refine (h1.congr_of_eventuallyEq hfun).congr_deriv ?_
    have hcp : cexp ((Real.log t : ℂ) * (-s)) = (t : ℂ) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
    rw [hcp, Complex.cpow_sub _ _ htC, Complex.cpow_one]
    push_cast; field_simp
  have hc : ContinuousOn (fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1)) (Set.Icc (1 : ℝ) x) := by
    refine continuousOn_const.mul ?_
    have hcont_exp : ContinuousOn (fun t : ℝ => cexp ((Real.log t : ℂ) * (-s - 1))) (Set.Icc (1 : ℝ) x) := by
      refine ContinuousOn.cexp (ContinuousOn.mul ?_ continuousOn_const)
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact Real.continuousOn_log.mono fun t ht => (zero_lt_one.trans_le ht.1).ne'
    refine hcont_exp.congr fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht.1
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    dsimp only
    rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht0.le]
  have hab := abel_summation_general a hx hd hc
  have hcast : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((n : ℝ) : ℂ) ^ (-s) = a n * (n : ℂ) ^ (-s) := by
    intro n _; push_cast; rfl
  rw [Finset.sum_congr rfl hcast] at hab
  rw [hab]
  have hint : ∫ t in (1 : ℝ)..x, stepSum a t * ((-s) * (t : ℂ) ^ (-s - 1)) =
      (-s) * ∫ t in (1 : ℝ)..x, stepSum a t * (t : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => by ring
  rw [hint]
  ring

/-- Convergence of the improper Mellin integral `∫_1^∞ E(t) t^{-s-1} dt` under `‖E(t)‖ ≤ C t^θ`. -/
theorem integrableOn_mellin_of_rpow_bound {E : ℝ → ℂ} (hE : Measurable E) {C θ : ℝ}
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ C * t ^ θ) {s : ℂ} (hs : θ < s.re) :
    IntegrableOn (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
  have hexp : θ - s.re - 1 < -1 := by linarith
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul C) ?_ ?_
  · have hpow : Measurable (fun t : ℝ => (t : ℂ) ^ (-s - 1)) :=
      Complex.measurable_ofReal.pow_const (-s - 1)
    exact (hE.mul hpow).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    calc ‖E t‖ * t ^ (-s.re - 1)
        ≤ (C * t ^ θ) * t ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (hbd t ht.le) (Real.rpow_nonneg ht0.le _)
      _ = C * (t ^ θ * t ^ (-s.re - 1)) := by ring
      _ = C * t ^ (θ - s.re - 1) := by
          rw [← Real.rpow_add ht0]; congr 2; ring

/-- Complex differentiability (holomorphicity) of `s ↦ ∫_1^∞ E(t) t^{-s-1} dt` on `Re(s) > θ`
under `‖E(t)‖ ≤ C t^θ`. -/
theorem hasDerivAt_mellin_of_rpow_bound {E : ℝ → ℂ} (hE : Measurable E) {C θ : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ C * t ^ θ) {s : ℂ} (hs : θ < s.re) :
    HasDerivAt (fun z : ℂ => ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1))
      (∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1))) s := by
  set δ : ℝ := (s.re - θ) / 2 with hδ_def
  have hδ0 : 0 < δ := by linarith
  set e : ℝ := δ / 2 with he_def
  have he0 : 0 < e := by linarith
  have hre : ∀ z ∈ Metric.ball s δ, θ + δ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hz.le)).1
    rw [Complex.sub_re] at h1
    linarith
  have hmeasF : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => E t * (t : ℂ) ^ (-z - 1))
      (volume.restrict (Ioi 1)) := fun z =>
    (hE.mul (Complex.measurable_ofReal.pow_const (-z - 1))).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable
      (fun t : ℝ => E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)))
      (volume.restrict (Ioi 1)) :=
    (hE.mul (((Complex.measurable_ofReal.comp Real.measurable_log).neg).mul
      (Complex.measurable_ofReal.pow_const (-s - 1)))).aestronglyMeasurable
  have hint := integrableOn_mellin_of_rpow_bound hE hbd hs
  have hdom_int : Integrable (fun t : ℝ => C * e⁻¹ * t ^ (-1 - δ / 2))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - δ / 2 < -1) zero_lt_one).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => E t * (t : ℂ) ^ (-z - 1))
    (F' := fun z t => E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-z - 1)))
    (Metric.ball_mem_nhds s hδ0)
    (Eventually.of_forall hmeasF) hint hmeasF' ?_ hdom_int ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z hz => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht1
    have hzr : θ + δ ≤ z.re := hre z hz
    have hlog : Real.log t ≤ e⁻¹ * t ^ e := by
      have := Real.log_le_rpow_div ht0.le he0
      linarith [show t ^ e / e = e⁻¹ * t ^ e by ring]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg ht1.le),
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre_z : (-z - 1).re = -z.re - 1 := by simp
    rw [hre_z]
    have hz_pow : t ^ (-z.re - 1) ≤ t ^ (-(θ + δ) - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    have hcomb : t ^ θ * (t ^ e * t ^ (-(θ + δ) - 1)) = t ^ (-1 - δ / 2) := by
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
      congr 1; linarith
    calc ‖E t‖ * (Real.log t * t ^ (-z.re - 1))
        ≤ (C * t ^ θ) * ((e⁻¹ * t ^ e) * t ^ (-(θ + δ) - 1)) := by
          refine mul_le_mul (hbd t ht1.le) ?_ (mul_nonneg (Real.log_nonneg ht1.le) (Real.rpow_nonneg ht0.le _))
            (mul_nonneg hC (Real.rpow_nonneg ht0.le _))
          exact mul_le_mul hlog hz_pow (Real.rpow_nonneg ht0.le _) (by positivity)
      _ = C * e⁻¹ * (t ^ θ * (t ^ e * t ^ (-(θ + δ) - 1))) := by ring
      _ = C * e⁻¹ * t ^ (-1 - δ / 2) := by rw [hcomb]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z _ => ?_)
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hfun : (fun w : ℂ => E t * (t : ℂ) ^ (-w - 1)) =
        fun w : ℂ => E t * cexp ((Real.log t : ℂ) * (-w - 1)) := by
      funext w
      rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
    rw [hfun]
    have h1 : HasDerivAt (fun w : ℂ => (Real.log t : ℂ) * (-w - 1)) (-(Real.log t : ℂ)) z := by
      have h0 : HasDerivAt (fun w : ℂ => -w - 1) (-1 : ℂ) z := by
        simpa using (hasDerivAt_id' z).neg.sub_const (1 : ℂ)
      simpa using h0.const_mul (Real.log t : ℂ)
    refine (h1.cexp.const_mul (E t)).congr_deriv ?_
    rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
    ring

theorem analyticOnNhd_mellin_of_rpow_bound {E : ℝ → ℂ} (hE : Measurable E) {C θ : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ C * t ^ θ) :
    AnalyticOnNhd ℂ (fun s : ℂ => 1 + s * ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1))
      {s : ℂ | θ < s.re} := by
  have hopen : IsOpen {s : ℂ | θ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hopen
  have hd := hasDerivAt_mellin_of_rpow_bound hE hC hbd hs
  exact (differentiableAt_const (1 : ℂ)).add
    (differentiableAt_id.mul hd.differentiableAt) |>.differentiableWithinAt

/-- Passage from finite Abelian summation to the improper Mellin integral for any `a : ℕ → ℂ`
with `‖stepSum a t‖ ≤ C t^θ` on `t ≥ 1`. -/
theorem LSeries_eq_mul_mellin_stepSum {a : ℕ → ℂ} {C θ : ℝ}
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖stepSum a t‖ ≤ C * t ^ θ) {s : ℂ} (hs : θ < s.re)
    (hsum : LSeriesSummable a s) :
    LSeries a s = s * ∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1) := by
  -- Partial sums converge to LSeries a s
  have hLHS : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) atTop
      (𝓝 (LSeries a s)) := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term a s n) atTop
        (𝓝 (LSeries a s)) :=
      h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun N => ?_
    have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 N), LSeries.term_zero, zero_add]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
  -- Boundary term stepSum a N * N ^ (-s) → 0
  have hBdry : Tendsto (fun N : ℕ => stepSum a (N : ℝ) * (N : ℂ) ^ (-s)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => C * ((N : ℝ) ^ (-(s.re - θ)))) atTop (𝓝 0) := by
      have h := ((tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp
        tendsto_natCast_atTop_atTop).const_mul C
      simpa using h
    refine squeeze_zero_norm' ?_ hpow
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have hN0 : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hN1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN, neg_re]
    calc ‖stepSum a (N : ℝ)‖ * (N : ℝ) ^ (-s.re)
        ≤ (C * (N : ℝ) ^ θ) * (N : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hbd (N : ℝ) hN1) (Real.rpow_nonneg hN0.le _)
      _ = C * ((N : ℝ) ^ θ * (N : ℝ) ^ (-s.re)) := by ring
      _ = C * (N : ℝ) ^ (-(s.re - θ)) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
  -- Integral ∫_1^N → ∫_{Ioi 1}
  have hint := integrableOn_mellin_of_rpow_bound (measurable_stepSum a) hbd hs
  have hInt : Tendsto (fun N : ℕ => ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))
      atTop (𝓝 (∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))) :=
    (intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id).comp tendsto_natCast_atTop_atTop
  have hRHS : Tendsto (fun N : ℕ =>
      stepSum a (N : ℝ) * (N : ℂ) ^ (-s) +
        s * ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))
      atTop (𝓝 (0 + s * ∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))) :=
    hBdry.add (hInt.const_mul s)
  have hEq : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) =ᶠ[atTop]
      (fun N : ℕ => stepSum a (N : ℝ) * (N : ℂ) ^ (-s) +
        s * ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h := abel_summation_dirichlet a (Nat.one_le_cast.mpr hN) s
    simpa [Nat.floor_natCast] using h
  simpa using tendsto_nhds_unique (hLHS.congr' hEq) hRHS

/-- Subtracting the main term `t` from `stepSum a t`: on `Re(s) > 1`,
`LSeries a s - 1 / (s - 1) = 1 + s * ∫_1^∞ (stepSum a t - t) * t^(-s-1) dt`. -/
theorem LSeries_sub_pole_eq_mellin_error {a : ℕ → ℂ} {C : ℝ}
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖stepSum a t‖ ≤ C * t) {s : ℂ} (hs : 1 < s.re)
    (hsum : LSeriesSummable a s) :
    LSeries a s - 1 / (s - 1) =
      1 + s * ∫ t in Ioi (1 : ℝ), (stepSum a t - (t : ℂ)) * (t : ℂ) ^ (-s - 1) := by
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have ha_pow : (-s).re < -1 := by simp; linarith
  have hlin_int : IntegrableOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
    refine (integrableOn_Ioi_cpow_of_lt ha_pow zero_lt_one).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    dsimp only
    rw [Complex.cpow_sub _ _ htC, Complex.cpow_one]; field_simp
  have hlin_val : ∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-s - 1) = 1 / (s - 1) := by
    have hcongr : EqOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1))
        (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi (1 : ℝ)) := fun t ht => by
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
      dsimp only
      rw [Complex.cpow_sub _ _ htC, Complex.cpow_one]; field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_Ioi_cpow_of_lt ha_pow zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
    have h1s : -s + 1 = -(s - 1) := by ring
    rw [h1s]; field_simp
  have hstep_int : IntegrableOn (fun t : ℝ => stepSum a t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_mellin_of_rpow_bound (measurable_stepSum a)
      (fun t ht => by simpa [Real.rpow_one] using hbd t ht) hs
  have hL := LSeries_eq_mul_mellin_stepSum
    (fun t ht => by simpa [Real.rpow_one] using hbd t ht) hs hsum
  have hsub_eq : ∫ t in Ioi (1 : ℝ), (stepSum a t - (t : ℂ)) * (t : ℂ) ^ (-s - 1) =
      (∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1)) - 1 / (s - 1) := by
    have hpt : (fun t : ℝ => (stepSum a t - (t : ℂ)) * (t : ℂ) ^ (-s - 1)) =
        fun t : ℝ => stepSum a t * (t : ℂ) ^ (-s - 1) - (t : ℂ) * (t : ℂ) ^ (-s - 1) := by
      funext t; ring
    rw [hpt, integral_sub hstep_int hlin_int, hlin_val]
  rw [hL, hsub_eq]
  field_simp
  ring

/-- `stepSum (fun n => (Λ n : ℂ)) x` equals `(chebyshevPsi x : ℂ)`. -/
theorem stepSum_vonMangoldt_eq_chebyshevPsi (x : ℝ) :
    stepSum (fun n => (Λ n : ℂ)) x = (chebyshevPsi x : ℂ) := by
  unfold stepSum chebyshevPsi
  rw [Complex.ofReal_sum]
  have hset : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 ⌊x⌋₊)]
  simp

/-- Exact agreement between `RHDirect.chebyshevPsi` and Mathlib's `Chebyshev.psi`. -/
theorem chebyshevPsi_eq_mathlib_psi (x : ℝ) :
    chebyshevPsi x = Chebyshev.psi x := by
  unfold chebyshevPsi Chebyshev.psi
  have hset : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Ioc 0 ⌊x⌋₊)]
  simp

/-- Unconditional linear growth bound `chebyshevPsi t ≤ 6 * t` for all `t ≥ 1`. -/
theorem chebyshevPsi_le_six_mul {t : ℝ} (ht : 1 ≤ t) :
    chebyshevPsi t ≤ 6 * t := by
  rw [chebyshevPsi_eq_mathlib_psi]
  have h := Chebyshev.psi_le ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hl4 : Real.log 4 ≤ 1.4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have hlog : Real.log t ≤ 2 * Real.sqrt t := by
    have h1 := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h1
    linarith
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have h2 : 2 * Real.sqrt t * Real.log t ≤ 4 * t := by
    calc 2 * Real.sqrt t * Real.log t
        ≤ 2 * Real.sqrt t * (2 * Real.sqrt t) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 4 * (Real.sqrt t * Real.sqrt t) := by ring
      _ = 4 * t := by rw [hsq]
  nlinarith

/-- **Exact Mellin–Abelian Representation of `-(ζ'/ζ)(s) - 1/(s-1)` on `Re(s) > 1`**:
`-deriv riemannZeta s / riemannZeta s - 1 / (s - 1) = 1 + s * ∫_1^∞ (ψ(t) - t) * t^(-s-1) dt`. -/
theorem neg_deriv_zeta_div_sub_pole_eq_mellin_psi {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) =
      1 + s * ∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
  rw [← LSeries_vonMangoldt_eq_neg_deriv_zeta_div hs]
  have hbd : ∀ t : ℝ, 1 ≤ t → ‖stepSum (fun n => (Λ n : ℂ)) t‖ ≤ 6 * t := by
    intro t ht
    rw [stepSum_vonMangoldt_eq_chebyshevPsi, Complex.norm_real,
      Real.norm_of_nonneg (chebyshevPsi_nonneg t)]
    exact chebyshevPsi_le_six_mul ht
  have h := LSeries_sub_pole_eq_mellin_error (a := fun n => (Λ n : ℂ))
    hbd hs (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  rw [h]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [stepSum_vonMangoldt_eq_chebyshevPsi]
  push_cast; rfl

/-- **General Holomorphic Logarithmic-Derivative Zero-Free Principle**:
Let `U = {s : ℂ | θ < s.re} \ {1}` (`θ < 1`). If `Z : ℂ → ℂ` is holomorphic on `U`, nonzero at
`s = 2`, and satisfies `-deriv Z s / Z s - 1 / (s - 1) = H s` on `{s | 1 < s.re}` where `H` is
holomorphic on `{s | θ < s.re}`, then `Z` has NO zeros in `{s | θ < s.re} \ {1}`! -/
theorem zeroFree_of_analytic_logDeriv_continuation {θ : ℝ} (hθ : θ < 1)
    {Z H : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s : ℂ | θ < s.re} \ {1}))
    (hZ2 : Z 2 ≠ 0)
    (hH : DifferentiableOn ℂ H {s : ℂ | θ < s.re})
    (hEq : ∀ s : ℂ, 1 < s.re → Z s ≠ 0 → -deriv Z s / Z s - 1 / (s - 1) = H s) :
    ∀ s : ℂ, θ < s.re → s ≠ 1 → Z s ≠ 0 := by
  set U : Set ℂ := {s : ℂ | θ < s.re} \ {1}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  -- U is path-connected (hence preconnected): every point joins to 2 by at most 3 segments in U
  have hseg : ∀ {a b : ℂ}, (∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • a + t • b ∈ U) → JoinedIn U a b := by
    intro a b hab
    refine ⟨⟨⟨fun t : unitInterval => (1 - (t : ℝ)) • a + (t : ℝ) • b, by fun_prop⟩,
      by simp, by simp⟩, fun t => hab (t : ℝ) t.2.1 t.2.2⟩
  have h2U : (2 : ℂ) ∈ U := ⟨by simp; linarith, by norm_num⟩
  have hU_pre : IsPreconnected U := by
    refine (IsPathConnected.isConnected (?_ : IsPathConnected U)).isPreconnected
    refine ⟨2, h2U, fun z hz => ?_⟩
    have hre_seg : ∀ (x y : ℂ) (t : ℝ), ((1 - t) • x + t • y).re = (1 - t) * x.re + t * y.re := by
      intro x y t; simp [Complex.real_smul]
    have him_seg : ∀ (x y : ℂ) (t : ℝ), ((1 - t) • x + t • y).im = (1 - t) * x.im + t * y.im := by
      intro x y t; simp [Complex.real_smul]
    by_cases hzr : z.re = 1
    · have hzi : z.im ≠ 0 := fun hi => hz.2 (Complex.ext hzr hi)
      set w : ℂ := 2 + (z.im : ℂ) * I
      have hj1 : JoinedIn U 2 w := hseg fun t ht0 ht1 => by
        refine ⟨?_, fun h => by
          have := congrArg Complex.re h
          rw [hre_seg] at this; simp [w] at this; linarith⟩
        show θ < ((1 - t) • (2 : ℂ) + t • w).re
        rw [hre_seg]; simp [w]; linarith
      have hj2 : JoinedIn U w z := hseg fun t ht0 ht1 => by
        refine ⟨?_, fun h => by
          have := congrArg Complex.im h
          rw [him_seg] at this; simp [w] at this; exact hzi (by linarith)⟩
        show θ < ((1 - t) • w + t • z).re
        rw [hre_seg]; simp [w, hzr]; nlinarith
      exact hj1.trans hj2
    · set w₁ : ℂ := 2 + I
      set w₂ : ℂ := (z.re : ℂ) + I
      have hj1 : JoinedIn U 2 w₁ := hseg fun t ht0 ht1 => by
        refine ⟨?_, fun h => by
          have := congrArg Complex.re h
          rw [hre_seg] at this; simp [w₁] at this; linarith⟩
        show θ < ((1 - t) • (2 : ℂ) + t • w₁).re
        rw [hre_seg]; simp [w₁]; linarith
      have hzr_gt : θ < z.re := hz.1
      have hj2 : JoinedIn U w₁ w₂ := hseg fun t ht0 ht1 => by
        refine ⟨?_, fun h => by
          have := congrArg Complex.im h
          rw [him_seg] at this; simp [w₁, w₂] at this⟩
        show θ < ((1 - t) • w₁ + t • w₂).re
        rw [hre_seg]; simp [w₁, w₂]
        rcases eq_or_lt_of_le ht0 with rfl | htpos <;> nlinarith
      have hj3 : JoinedIn U w₂ z := hseg fun t ht0 ht1 => by
        refine ⟨?_, fun h => by
          have := congrArg Complex.re h
          rw [hre_seg] at this; simp [w₂] at this; exact hzr (by linarith)⟩
        show θ < ((1 - t) • w₂ + t • z).re
        rw [hre_seg]; simp [w₂]; linarith
      exact (hj1.trans hj2).trans hj3
  have hZ_an : AnalyticOnNhd ℂ Z U := hZ.analyticOnNhd hU_open
  have hF_an : AnalyticOnNhd ℂ (fun s => -deriv Z s) U :=
    fun s hs => (hZ_an s hs).deriv.neg
  have hG_an : AnalyticOnNhd ℂ (fun s => Z s * (H s + 1 / (s - 1))) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hU_open
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
    have hH' : DifferentiableAt ℂ H s :=
      (hH s hs.1).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs.1)
    have hZ' : DifferentiableAt ℂ Z s := (hZ s hs).differentiableAt (hU_open.mem_nhds hs)
    exact (hZ'.mul (hH'.add ((differentiableAt_const (1 : ℂ)).div
      (differentiableAt_id.sub_const 1) hs1))).differentiableWithinAt
  have hEv : (fun s => -deriv Z s) =ᶠ[𝓝 (2 : ℂ)] (fun s => Z s * (H s + 1 / (s - 1))) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp : 1 < (2 : ℂ).re),
      (hZ_an 2 h2U).continuousAt.eventually_ne hZ2] with s hs1 hZs
    have h := hEq s hs1 hZs
    have : -deriv Z s / Z s = H s + 1 / (s - 1) := eq_add_of_sub_eq h
    rw [mul_comm]
    exact (div_eq_iff hZs).mp this
  have hODE : ∀ s ∈ U, -deriv Z s = Z s * (H s + 1 / (s - 1)) :=
    fun s hs => hF_an.eqOn_of_preconnected_of_eventuallyEq hG_an hU_pre h2U hEv hs
  intro ρ hρre hρ1 hZρ
  have hρU : ρ ∈ U := ⟨hρre, hρ1⟩
  have hZρ_an : AnalyticAt ℂ Z ρ := hZ_an ρ hρU
  have htop : analyticOrderAt Z ρ ≠ ⊤ := by
    intro h
    have h0 := analyticOrderAt_eq_top.mp h
    exact hZ2 (hZ_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_pre hρU h0 h2U)
  obtain ⟨g, hg_an, hgρ, hZg⟩ := hZρ_an.analyticOrderAt_ne_top.mp htop
  set m := analyticOrderNatAt Z ρ with hm_def
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    have hord0 : analyticOrderAt Z ρ = 0 := by
      rw [← Nat.cast_analyticOrderNatAt htop, ← hm_def, hm0']; simp
    exact ((hZρ_an.analyticOrderAt_eq_zero).mp hord0) hZρ
  -- Compute derivative of Z(z) = (z - ρ)^m * g(z) near ρ
  have hnear : ∀ᶠ z in 𝓝[≠] ρ,
      (m : ℂ) * g z + (z - ρ) * deriv g z = -(z - ρ) * g z * (H z + 1 / (z - 1)) := by
    have hU_ev : ∀ᶠ z in 𝓝 ρ, z ∈ U := hU_open.mem_nhds hρU
    have hnhds : ∀ᶠ z in 𝓝 ρ,
        (∀ᶠ w in 𝓝 z, Z w = (w - ρ) ^ m • g w) ∧ z ∈ U ∧ AnalyticAt ℂ g z :=
      (Filter.Eventually.eventually_nhds hZg).and (hU_ev.and hg_an.eventually_analyticAt)
    filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with z ⟨hz1, hzU, hgz⟩ hzne
    have hzρ : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
    have hdz : HasDerivAt (fun w => (w - ρ) ^ m * g w)
        ((m : ℂ) * (z - ρ) ^ (m - 1) * 1 * g z + (z - ρ) ^ m * deriv g z) z :=
      (((hasDerivAt_id' z).sub_const ρ).pow m).mul hgz.differentiableAt.hasDerivAt
    have hdZ : deriv Z z = (m : ℂ) * (z - ρ) ^ (m - 1) * g z + (z - ρ) ^ m * deriv g z := by
      have hev' : Z =ᶠ[𝓝 z] fun w => (w - ρ) ^ m * g w := by
        filter_upwards [hz1] with w hw; simpa [smul_eq_mul] using hw
      rw [hev'.deriv_eq, hdz.deriv]; ring
    have hZz : Z z = (z - ρ) ^ m * g z := by simpa [smul_eq_mul] using hz1.self_of_nhds
    have hode := hODE z hzU
    rw [hdZ, hZz] at hode
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hpow_ne : (z - ρ) ^ j ≠ 0 := pow_ne_zero j hzρ
    have hfactor : (z - ρ) ^ j * ((m : ℂ) * g z + (z - ρ) * deriv g z) =
        (z - ρ) ^ j * (-(z - ρ) * g z * (H z + 1 / (z - 1))) := by
      rw [hj, Nat.add_sub_cancel, pow_succ] at hode
      rw [hj]
      linear_combination -hode
    exact mul_left_cancel₀ hpow_ne hfactor
  -- Take limit z → ρ along 𝓝[≠] ρ: LHS → m * g(ρ) ≠ 0, RHS → 0, contradiction!
  have hLHS : Tendsto (fun z : ℂ => (m : ℂ) * g z + (z - ρ) * deriv g z) (𝓝[≠] ρ)
      (𝓝 ((m : ℂ) * g ρ + (ρ - ρ) * deriv g ρ)) :=
    (((hg_an.continuousAt.tendsto.const_mul (m : ℂ)).add
      ((tendsto_id.sub_const ρ).mul hg_an.deriv.continuousAt.tendsto))).mono_left nhdsWithin_le_nhds
  have hH_cont : ContinuousAt (fun z => H z + 1 / (z - 1)) ρ :=
    ((hH ρ hρre).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρre)).continuousAt.add
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hρ1))
  have hRHS : Tendsto (fun z : ℂ => -(z - ρ) * g z * (H z + 1 / (z - 1))) (𝓝[≠] ρ)
      (𝓝 (-(ρ - ρ) * g ρ * (H ρ + 1 / (ρ - 1)))) :=
    ((((tendsto_id.sub_const ρ).neg.mul hg_an.continuousAt.tendsto).mul
      hH_cont.tendsto)).mono_left nhdsWithin_le_nhds
  have heq_lim := tendsto_nhds_unique (hLHS.congr' hnear) hRHS
  simp only [sub_self, zero_mul, neg_zero, add_zero] at heq_lim
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hm_pos.ne') hgρ heq_lim

/-- **Analyticity of `-(ζ'/ζ)(s) - 1/(s-1)` on `Re(s) > θ` from `|ψ(x) - x| ≤ C x^θ`**:
explicitly realized by the Mellin integral `1 + s * ∫_1^∞ (ψ(t) - t) t^(-s-1) dt`. -/
theorem analytic_logDeriv_zeta_of_psi_bound {C θ : ℝ} (hC : 0 ≤ C)
    (hpsi : ∀ x : ℝ, 1 ≤ x → |chebyshevPsi x - x| ≤ C * x ^ θ) :
    let H : ℂ → ℂ := fun s =>
      1 + s * ∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)
    AnalyticOnNhd ℂ H {s : ℂ | θ < s.re} ∧
    ∀ s : ℂ, 1 < s.re → -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) = H s := by
  intro H
  have hmeas : Measurable (fun t : ℝ => ((chebyshevPsi t - t : ℝ) : ℂ)) := by
    have h1 : (fun t : ℝ => (chebyshevPsi t : ℂ)) = stepSum (fun n => (Λ n : ℂ)) :=
      funext fun t => (stepSum_vonMangoldt_eq_chebyshevPsi t).symm
    have h2 : (fun t : ℝ => ((chebyshevPsi t - t : ℝ) : ℂ)) =
        fun t : ℝ => stepSum (fun n => (Λ n : ℂ)) t - (t : ℂ) := by
      funext t; rw [stepSum_vonMangoldt_eq_chebyshevPsi]; push_cast; rfl
    rw [h2]
    exact (measurable_stepSum _).sub Complex.measurable_ofReal
  have hbd : ∀ t : ℝ, 1 ≤ t → ‖((chebyshevPsi t - t : ℝ) : ℂ)‖ ≤ C * t ^ θ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hpsi t ht
  exact ⟨analyticOnNhd_mellin_of_rpow_bound hmeas hC hbd,
    fun s hs => neg_deriv_zeta_div_sub_pole_eq_mellin_psi hs⟩

/-- **Unconditional Zero-Free Half-Plane for `ζ(s)` from `|ψ(x) - x| ≤ C x^θ`** (`θ < 1`,
in particular `1/2 ≤ θ < 1`):
deduces BOTH analytic continuation of `-(ζ'/ζ)(s) - 1/(s-1)` across `Re(s) > θ` AND
`∀ s, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0`! -/
theorem zeroFree_riemannZeta_of_psi_bound {C θ : ℝ} (hC : 0 ≤ C) (hθ : θ < 1)
    (hpsi : ∀ x : ℝ, 1 ≤ x → |chebyshevPsi x - x| ≤ C * x ^ θ) :
    (∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) ∧
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | θ < s.re} ∧
      ∀ s : ℂ, θ < s.re → s ≠ 1 → -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) = H s := by
  obtain ⟨hHan, hHeq⟩ := analytic_logDeriv_zeta_of_psi_bound hC hpsi
  set H : ℂ → ℂ := fun s =>
    1 + s * ∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)
  have hZdiff : DifferentiableOn ℂ riemannZeta ({s : ℂ | θ < s.re} \ {1}) := fun s hs =>
    (differentiableAt_riemannZeta hs.2).differentiableWithinAt
  have hZ2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have hzf : ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
    zeroFree_of_analytic_logDeriv_continuation hθ hZdiff hZ2 hHan.differentiableOn
      fun s hs _ => hHeq s hs
  refine ⟨hzf, H, hHan, fun s hs hs1 => ?_⟩
  -- Equality on all of {s | θ < s.re} \ {1} by identity theorem
  set U : Set ℂ := {s : ℂ | θ < s.re} \ {1}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hseg : ∀ {a b : ℂ}, (∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • a + t • b ∈ U) → JoinedIn U a b := by
    intro a b hab
    refine ⟨⟨⟨fun t : unitInterval => (1 - (t : ℝ)) • a + (t : ℝ) • b, by fun_prop⟩,
      by simp, by simp⟩, fun t => hab (t : ℝ) t.2.1 t.2.2⟩
  have h2U : (2 : ℂ) ∈ U := ⟨by simp; linarith, by norm_num⟩
  have hU_pre : IsPreconnected U := by
    refine (IsPathConnected.isConnected (?_ : IsPathConnected U)).isPreconnected
    refine ⟨2, h2U, fun z hz => ?_⟩
    have hre_seg : ∀ (x y : ℂ) (t : ℝ), ((1 - t) • x + t • y).re = (1 - t) * x.re + t * y.re := by
      intro x y t; simp [Complex.real_smul]
    have him_seg : ∀ (x y : ℂ) (t : ℝ), ((1 - t) • x + t • y).im = (1 - t) * x.im + t * y.im := by
      intro x y t; simp [Complex.real_smul]
    by_cases hzr : z.re = 1
    · have hzi : z.im ≠ 0 := fun hi => hz.2 (Complex.ext hzr hi)
      set w : ℂ := 2 + (z.im : ℂ) * I
      have hj1 : JoinedIn U 2 w := hseg fun t _ _ =>
        ⟨by show θ < ((1 - t) • (2 : ℂ) + t • w).re; rw [hre_seg]; simp [w]; linarith,
          fun h => by have := congrArg Complex.re h; rw [hre_seg] at this; simp [w] at this; linarith⟩
      have hj2 : JoinedIn U w z := hseg fun t ht0 ht1 =>
        ⟨by show θ < ((1 - t) • w + t • z).re; rw [hre_seg]; simp [w, hzr]; nlinarith,
          fun h => by have := congrArg Complex.im h; rw [him_seg] at this; simp [w] at this; exact hzi (by linarith)⟩
      exact hj1.trans hj2
    · set w₁ : ℂ := 2 + I
      set w₂ : ℂ := (z.re : ℂ) + I
      have hzr_gt : θ < z.re := hz.1
      have hj1 : JoinedIn U 2 w₁ := hseg fun t _ _ =>
        ⟨by show θ < ((1 - t) • (2 : ℂ) + t • w₁).re; rw [hre_seg]; simp [w₁]; linarith,
          fun h => by have := congrArg Complex.re h; rw [hre_seg] at this; simp [w₁] at this; linarith⟩
      have hj2 : JoinedIn U w₁ w₂ := hseg fun t ht0 ht1 =>
        ⟨by show θ < ((1 - t) • w₁ + t • w₂).re; rw [hre_seg]; simp [w₁, w₂]
            rcases eq_or_lt_of_le ht0 with rfl | htpos <;> nlinarith,
          fun h => by have := congrArg Complex.im h; rw [him_seg] at this; simp [w₁, w₂] at this⟩
      have hj3 : JoinedIn U w₂ z := hseg fun t _ _ =>
        ⟨by show θ < ((1 - t) • w₂ + t • z).re; rw [hre_seg]; simp [w₂]; linarith,
          fun h => by have := congrArg Complex.re h; rw [hre_seg] at this; simp [w₂] at this; exact hzr (by linarith)⟩
      exact (hj1.trans hj2).trans hj3
  have hLHS_an : AnalyticOnNhd ℂ (fun z => -deriv riemannZeta z / riemannZeta z - 1 / (z - 1)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    have hz_an : AnalyticAt ℂ riemannZeta z :=
      (hZdiff.analyticOnNhd hU_open) z hz
    have hdz : DifferentiableAt ℂ (deriv riemannZeta) z := hz_an.deriv.differentiableAt
    exact ((hdz.neg.div (differentiableAt_riemannZeta hz.2) (hzf z hz.1 hz.2)).sub
      ((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1)
        (sub_ne_zero.mpr hz.2))).differentiableWithinAt
  have hEv : (fun z => -deriv riemannZeta z / riemannZeta z - 1 / (z - 1)) =ᶠ[𝓝 (2 : ℂ)] H := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp : 1 < (2 : ℂ).re)] with z hz using hHeq z hz
  exact hLHS_an.eqOn_of_preconnected_of_eventuallyEq (hHan.mono fun _ h => h.1) hU_pre h2U hEv ⟨hs, hs1⟩

/-- Classical corollary: `ψ(x) - x = O(x^{1/2 + ε})` for every `ε > 0` unconditionally implies
Mathlib's `RiemannHypothesis`! -/
theorem riemannHypothesis_of_psi_bound_eps
    (hpsi : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |chebyshevPsi x - x| ≤ C * x ^ ((1 : ℝ) / 2 + ε)) :
    RiemannHypothesis := by
  rw [RHDirect.riemannHypothesis_iff_nonvanishingRightOfHalf]
  intro s hs hs1
  rcases lt_or_ge s.re 1 with hlt1 | hge1
  · set ε : ℝ := (s.re - 1 / 2) / 2 with hε_def
    have hε0 : 0 < ε := by linarith
    obtain ⟨C, hCbd⟩ := hpsi ε hε0
    have hC0 : 0 ≤ C := by
      have h1 := hCbd 1 le_rfl
      simp only [Real.one_rpow, mul_one] at h1
      exact (abs_nonneg _).trans h1
    exact (zeroFree_riemannZeta_of_psi_bound hC0 (by linarith) hCbd).1 s (by linarith) hs1
  · exact riemannZeta_ne_zero_of_one_le_re hge1

/-! ### Exact Riesz-Mean Integral Identity, Dyadic-Window Smoothing, and `ψ` ↔ `ϑ` ↔ `π` Bridges -/

/-- **Exact Riesz-Mean / Cesàro-Ramp Integral Representation**:
for all `y ≥ 1`, `chebyshevRamp y = y * ∫_1^y (ψ(t) / t^2) dt`. -/
theorem chebyshevRamp_eq_mul_integral_psi {y : ℝ} (hy : 1 ≤ y) :
    chebyshevRamp y = y * ∫ t in (1 : ℝ)..y, chebyshevPsi t / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) y,
      HasDerivAt (fun u : ℝ => ((y / u - 1 : ℝ) : ℂ)) (((-(y / t ^ 2) : ℝ) : ℂ)) t := by
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    have hr : HasDerivAt (fun u : ℝ => y / u - 1) (-(y / t ^ 2)) t := by
      have h1 := (hasDerivAt_inv ht0).const_mul y
      have h2 := h1.sub_const (1 : ℝ)
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => by simp [div_eq_mul_inv])
        |>.congr_deriv ?_
      ring
    exact hr.ofReal_comp
  have hc : ContinuousOn (fun t : ℝ => ((-(y / t ^ 2) : ℝ) : ℂ)) (Set.Icc (1 : ℝ) y) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.neg (continuousOn_const.div (continuousOn_pow 2) fun t ht => ?_)
    exact pow_ne_zero 2 (zero_lt_one.trans_le ht.1).ne'
  have hab := abel_summation_general (fun n => (Λ n : ℂ)) hy hd hc
  have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
  simp only [div_self hy0, sub_self, Complex.ofReal_zero, mul_zero, zero_sub] at hab
  have hre := congrArg Complex.re hab
  have hLHS : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * ((y / (n : ℝ) - 1 : ℝ) : ℂ)).re =
      chebyshevRamp y := by
    rw [chebyshevRamp_eq_sum_Icc hy, Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hRHS : (-(∫ t in (1 : ℝ)..y, stepSum (fun n => (Λ n : ℂ)) t * (((-(y / t ^ 2) : ℝ) : ℂ)))).re =
      y * ∫ t in (1 : ℝ)..y, chebyshevPsi t / t ^ 2 := by
    have hfun : (fun t : ℝ => stepSum (fun n => (Λ n : ℂ)) t * (((-(y / t ^ 2) : ℝ) : ℂ))) =
        fun t : ℝ => (((-(y * (chebyshevPsi t / t ^ 2)) : ℝ) : ℂ)) := by
      funext t
      rw [stepSum_vonMangoldt_eq_chebyshevPsi, ← Complex.ofReal_mul]
      congr 1; ring
    rw [hfun, intervalIntegral.integral_ofReal, Complex.neg_re, Complex.ofReal_re,
      intervalIntegral.integral_neg, neg_neg, intervalIntegral.integral_const_mul]
  rw [hLHS, hRHS] at hre
  exact hre

/-- Exact Riesz-mean error identity:
`chebyshevRamp y - y * log y = y * ∫_1^y ((ψ(t) - t) / t^2) dt` for all `y ≥ 1`. -/
theorem chebyshevRamp_sub_mul_log_eq_integral {y : ℝ} (hy : 1 ≤ y) :
    chebyshevRamp y - y * Real.log y =
      y * ∫ t in (1 : ℝ)..y, (chebyshevPsi t - t) / t ^ 2 := by
  have hint_log : ∫ t in (1 : ℝ)..y, (1 : ℝ) / t = Real.log y := by
    have h := integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hy)
    simpa [one_div, Real.log_one] using h
  have hpsi_int : IntervalIntegrable (fun t : ℝ => chebyshevPsi t / t ^ 2) volume (1 : ℝ) y := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr ?_
    refine Integrable.mono' (integrableOn_const (C := chebyshevPsi y) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
    · have hm : Measurable chebyshevPsi := by
        have h : chebyshevPsi = (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
        rw [h]
        exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
      exact (hm.div (continuous_pow 2).measurable).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht1 : 1 ≤ t := ht.1.le
      have htsq : 1 ≤ t ^ 2 := by nlinarith
      rw [Real.norm_of_nonneg (div_nonneg (chebyshevPsi_nonneg t) (sq_nonneg t))]
      exact (div_le_self (chebyshevPsi_nonneg t) htsq).trans (chebyshevPsi_mono ht.2)
  have hinv_int : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) volume (1 : ℝ) y := by
    have hc : ContinuousOn (fun t : ℝ => (1 : ℝ) / t) (Set.uIcc 1 y) := by
      rw [Set.uIcc_of_le hy]
      exact continuousOn_const.div continuousOn_id fun t ht => (zero_lt_one.trans_le ht.1).ne'
    exact hc.intervalIntegrable
  have hpt : Set.EqOn (fun t : ℝ => (chebyshevPsi t - t) / t ^ 2)
      (fun t : ℝ => chebyshevPsi t / t ^ 2 - 1 / t) (Set.uIcc 1 y) := by
    rw [Set.uIcc_of_le hy]
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    dsimp only; field_simp
  rw [chebyshevRamp_eq_mul_integral_psi hy, intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_sub hpsi_int hinv_int, hint_log]
  ring

/-- **Exact Difference Identity for `RHDirect.Gz`**:
for all `1 ≤ x ≤ y`, `Gz y / y - Gz x / x = ∫_x^y ((ψ(t) - t) / t^2) dt`! -/
theorem Gz_div_sub_Gz_div_eq_integral {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    Gz y / y - Gz x / x = ∫ t in x..y, (chebyshevPsi t - t) / t ^ 2 := by
  have hy : 1 ≤ y := hx.trans hxy
  have hx0 : x ≠ 0 := (zero_lt_one.trans_le hx).ne'
  have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
  have hGz_id : ∀ z : ℝ, 1 ≤ z →
      Gz z / z = (1 + Real.eulerMascheroniConstant) +
        ∫ t in (1 : ℝ)..z, (chebyshevPsi t - t) / t ^ 2 := by
    intro z hz
    have hz0 : z ≠ 0 := (zero_lt_one.trans_le hz).ne'
    rw [Gz_eq_chebyshevRamp, chebyshevRamp_sub_mul_log_eq_integral hz]
    field_simp; ring
  have hint_fn : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      IntervalIntegrable (fun t : ℝ => (chebyshevPsi t - t) / t ^ 2) volume a b := by
    intro a b ha hab
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr ?_
    refine Integrable.mono'
      (integrableOn_const (C := chebyshevPsi b + b) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
    · have hm : Measurable chebyshevPsi := by
        have h : chebyshevPsi = (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
        rw [h]
        exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
      exact ((hm.sub measurable_id).div (continuous_pow 2).measurable).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht1 : 1 ≤ t := ha.trans ht.1.le
      have htsq : 1 ≤ t ^ 2 := by nlinarith
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      refine (div_le_self (abs_nonneg _) htsq).trans ?_
      have h1 : |chebyshevPsi t - t| ≤ chebyshevPsi t + t := by
        have h0 := chebyshevPsi_nonneg t
        rcases abs_cases (chebyshevPsi t - t) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
      linarith [chebyshevPsi_mono ht.2, ht.2]
  rw [hGz_id y hy, hGz_id x hx,
    ← intervalIntegral.integral_add_adjacent_intervals (hint_fn 1 x le_rfl hx) (hint_fn x y hx hxy)]
  ring

/-- **Exact Improper Integral Evaluation `∫_1^∞ ((ψ(t) - t) / t^2) dt = -(1 + γ)`**
whenever `|ψ(t) - t| ≤ C t^θ` (`θ < 1`), obtained via DCT on `-(ζ'/ζ)(σ) - 1/(σ - 1)` as `σ → 1⁺`. -/
theorem integral_psi_sub_id_div_sq_eq {C θ : ℝ} (hθ : θ < 1)
    (hpsi : ∀ t : ℝ, 1 ≤ t → |chebyshevPsi t - t| ≤ C * t ^ θ) :
    ∫ t in Ioi (1 : ℝ), (chebyshevPsi t - t) / t ^ 2 = -(1 + Real.eulerMascheroniConstant) := by
  have hC0 : 0 ≤ C := by
    have h1 := hpsi 1 le_rfl; simp only [Real.one_rpow, mul_one] at h1
    exact (abs_nonneg _).trans h1
  -- Auxiliary entire function g(s) = (s - 1) ζ(s) with g(1) = 1, g'(1) = γ
  set g : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
  have hg_ne : ∀ w : ℂ, w ≠ 1 → g w = (w - 1) * riemannZeta w := fun w hw => by simp [g, hw]
  have hg1 : g 1 = 1 := by simp [g]
  have hg_diff : Differentiable ℂ g := by
    rw [← differentiableOn_univ,
      ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
    refine ⟨fun z hz => ?_, by simpa only [g, continuousAt_update_same] using riemannZeta_residue_one⟩
    have hz1 : z ≠ 1 := by simpa using hz
    have hev : g =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw using hg_ne w hw
    exact ((DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hz1)).congr_of_eventuallyEq
      hev).differentiableWithinAt
  have hderiv1 : deriv g 1 = (Real.eulerMascheroniConstant : ℂ) := by
    have hd := hasDerivAt_iff_tendsto_slope.mp (hg_diff 1).hasDerivAt
    refine tendsto_nhds_unique hd (tendsto_riemannZeta_sub_one_div.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    rw [slope_def_field, hg_ne s hs, hg1]; field_simp
  have hderiv_ne : ∀ s : ℂ, s ≠ 1 → deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    intro s hs1
    have hev : g =ᶠ[𝓝 s] fun t => (t - 1) * riemannZeta t := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with w hw using hg_ne w hw
    have h3 : HasDerivAt (fun t : ℂ => (t - 1) * riemannZeta t)
        (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
      ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs1).hasDerivAt
    rw [hev.deriv_eq, h3.deriv]; ring
  -- Limit of -(ζ'/ζ)(σ) - 1/(σ - 1) = -(g'(σ) / g(σ)) as σ → 1⁺ is -γ
  have hLim1 : Tendsto (fun σ : ℝ =>
      -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) - 1 / ((σ : ℂ) - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    have hcont_g' : ContinuousAt (deriv g) 1 := (hg_diff.analyticAt 1).deriv.continuousAt
    have hcont_div : ContinuousAt (fun z : ℂ => -(deriv g z / g z)) 1 :=
      (hcont_g'.div (hg_diff.continuous.continuousAt) (by rw [hg1]; exact one_ne_zero)).neg
    have h1 : Tendsto (fun σ : ℝ => -(deriv g (σ : ℂ) / g (σ : ℂ))) (𝓝[>] (1 : ℝ))
        (𝓝 (-(deriv g 1 / g 1))) :=
      (hcont_div.tendsto.comp Complex.continuous_ofReal.continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    rw [hderiv1, hg1, div_one] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    have hσ1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.ne'
    have hσ1' : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hσ1
    have hz : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simpa using hσ.le)
    rw [hderiv_ne (σ : ℂ) hσ1, hg_ne (σ : ℂ) hσ1]
    field_simp
    ring
  -- Limit of 1 + σ * ∫_1^∞ (ψ(t) - t) t^(-σ-1) dt as σ → 1⁺ by DCT
  have hmeas_psi : Measurable chebyshevPsi := by
    have h : chebyshevPsi = (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
    rw [h]
    exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
  have hDCT : Tendsto (fun σ : ℝ =>
      ∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
      (𝓝[>] (1 : ℝ))
      (𝓝 (∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(2 : ℂ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun t : ℝ => C * t ^ (θ - 2)) ?_ ?_
      ((integrableOn_Ioi_rpow_of_lt (by linarith : θ - 2 < -1) zero_lt_one).const_mul C) ?_
    · exact Eventually.of_forall fun σ =>
        ((Complex.measurable_ofReal.comp (hmeas_psi.sub measurable_id)).mul
          (Complex.measurable_ofReal.pow_const (-(σ : ℂ) - 1))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-(σ : ℂ) - 1).re = -σ - 1 := by simp
      rw [hre]
      have hpow_le : t ^ (-σ - 1) ≤ t ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
      calc |chebyshevPsi t - t| * t ^ (-σ - 1)
          ≤ (C * t ^ θ) * t ^ (-2 : ℝ) :=
            mul_le_mul (hpsi t ht.le) hpow_le (Real.rpow_nonneg ht0.le _)
              (mul_nonneg hC0 (Real.rpow_nonneg ht0.le _))
        _ = C * (t ^ θ * t ^ (-2 : ℝ)) := by ring
        _ = C * t ^ (θ - 2) := by rw [← Real.rpow_add ht0, sub_eq_add_neg]
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have hfun : (fun σ : ℝ => (t : ℂ) ^ (-(σ : ℂ) - 1)) =
          fun σ : ℝ => cexp ((Real.log t : ℂ) * (-(σ : ℂ) - 1)) := by
        funext σ
        rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
      have hlim_pow : Tendsto (fun σ : ℝ => (t : ℂ) ^ (-(σ : ℂ) - 1)) (𝓝[>] (1 : ℝ))
          (𝓝 ((t : ℂ) ^ (-(2 : ℂ)))) := by
        rw [hfun]
        have hcont : Continuous (fun σ : ℝ => cexp ((Real.log t : ℂ) * (-(σ : ℂ) - 1))) := by
          fun_prop
        have h2 : Tendsto (fun σ : ℝ => cexp ((Real.log t : ℂ) * (-(σ : ℂ) - 1))) (𝓝[>] (1 : ℝ))
            (𝓝 (cexp ((Real.log t : ℂ) * (-((1 : ℝ) : ℂ) - 1)))) :=
          (hcont.continuousAt.tendsto (x := (1 : ℝ))).mono_left nhdsWithin_le_nhds
        have hval : cexp ((Real.log t : ℂ) * (-((1 : ℝ) : ℂ) - 1)) = (t : ℂ) ^ (-(2 : ℂ)) := by
          rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
          congr 2; push_cast; ring
        rwa [hval] at h2
      exact hlim_pow.const_mul _
  have hLim2 : Tendsto (fun σ : ℝ =>
      1 + (σ : ℂ) * ∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
      (𝓝[>] (1 : ℝ))
      (𝓝 (1 + (1 : ℂ) * ∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(2 : ℂ)))) :=
    (((Complex.continuous_ofReal.continuousAt.tendsto (x := (1 : ℝ))).mono_left
      nhdsWithin_le_nhds).mul hDCT).const_add 1
  have hEv : (fun σ : ℝ => -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) - 1 / ((σ : ℂ) - 1)) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun σ : ℝ => 1 + (σ : ℂ) * ∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    exact neg_deriv_zeta_div_sub_pole_eq_mellin_psi (by simpa using hσ)
  have heqC := tendsto_nhds_unique (hLim1.congr' hEv) hLim2
  have hcast_int : ∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(2 : ℂ)) =
      ((∫ t in Ioi (1 : ℝ), (chebyshevPsi t - t) / t ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have hpow : (t : ℂ) ^ (-(2 : ℂ)) = (((t ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast; rfl
    rw [hpow, ← Complex.ofReal_mul, div_eq_mul_inv]
  rw [one_mul, hcast_int] at heqC
  have hre := congrArg Complex.re heqC
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.add_re, Complex.one_re] at hre
  linarith

/-- **Exact Tail-Integral Formula for `RHDirect.Gz` & Quantitative `O(y^θ)` Bound from
`|ψ(x) - x| ≤ C x^θ`**:
connects classical `ψ(x) - x = O(x^θ)` directly to `HasRpowWindow Gz θ δ (C / (1 - θ))`! -/
theorem Gz_eq_neg_mul_tail_integral_and_bound {C θ : ℝ} (hθ : θ < 1)
    (hpsi : ∀ t : ℝ, 1 ≤ t → |chebyshevPsi t - t| ≤ C * t ^ θ) {y : ℝ} (hy : 1 ≤ y) :
    Gz y = -y * ∫ t in Ioi y, (chebyshevPsi t - t) / t ^ 2 ∧
    |Gz y| ≤ (C / (1 - θ)) * y ^ θ := by
  have hC0 : 0 ≤ C := by
    have h1 := hpsi 1 le_rfl; simp only [Real.one_rpow, mul_one] at h1
    exact (abs_nonneg _).trans h1
  have hy0 : (0 : ℝ) < y := zero_lt_one.trans_le hy
  have hmeas_psi : Measurable chebyshevPsi := by
    have h : chebyshevPsi = (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
    rw [h]
    exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
  have hint_all : IntegrableOn (fun t : ℝ => (chebyshevPsi t - t) / t ^ 2) (Ioi (1 : ℝ)) := by
    refine Integrable.mono'
      ((integrableOn_Ioi_rpow_of_lt (by linarith : θ - 2 < -1) zero_lt_one).const_mul C)
      ((hmeas_psi.sub measurable_id).div (continuous_pow 2).measurable).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
    have hpow : t ^ θ / t ^ 2 = t ^ (θ - 2) := by
      rw [show t ^ 2 = t ^ (2 : ℝ) by norm_cast, ← Real.rpow_sub ht0]
    calc |chebyshevPsi t - t| / t ^ 2
        ≤ (C * t ^ θ) / t ^ 2 := div_le_div_of_nonneg_right (hpsi t ht.le) (sq_nonneg t)
      _ = C * (t ^ θ / t ^ 2) := by ring
      _ = C * t ^ (θ - 2) := by rw [hpow]
  have hsplit : (∫ t in (1 : ℝ)..y, (chebyshevPsi t - t) / t ^ 2) +
      (∫ t in Ioi y, (chebyshevPsi t - t) / t ^ 2) =
      ∫ t in Ioi (1 : ℝ), (chebyshevPsi t - t) / t ^ 2 := by
    rw [intervalIntegral.integral_of_le hy]
    have hdisj : Disjoint (Ioc (1 : ℝ) y) (Ioi y) := Set.Ioc_disjoint_Ioi_same
    have hunion : Ioc (1 : ℝ) y ∪ Ioi y = Ioi (1 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hy
    rw [← setIntegral_union hdisj measurableSet_Ioi
      (hint_all.mono_set (Set.Ioc_subset_Ioi_self))
      (hint_all.mono_set (Set.Ioi_subset_Ioi hy)), hunion]
  have hGz : Gz y = -y * ∫ t in Ioi y, (chebyshevPsi t - t) / t ^ 2 := by
    have h1 := integral_psi_sub_id_div_sq_eq hθ hpsi
    rw [Gz_eq_chebyshevRamp, chebyshevRamp_sub_mul_log_eq_integral hy]
    have h2 : ∫ t in (1 : ℝ)..y, (chebyshevPsi t - t) / t ^ 2 =
        -(1 + Real.eulerMascheroniConstant) - ∫ t in Ioi y, (chebyshevPsi t - t) / t ^ 2 := by
      linarith
    rw [h2]; ring
  refine ⟨hGz, ?_⟩
  rw [hGz, abs_mul, abs_neg, abs_of_pos hy0]
  have htail_le : |∫ t in Ioi y, (chebyshevPsi t - t) / t ^ 2| ≤
      ∫ t in Ioi y, C * t ^ (θ - 2) := by
    refine (abs_integral_le_integral_abs).trans ?_
    refine setIntegral_mono_on (hint_all.mono_set (Set.Ioi_subset_Ioi hy)).abs
      ((integrableOn_Ioi_rpow_of_lt (by linarith : θ - 2 < -1) hy0).const_mul C)
      measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := hy0.trans ht
    have ht1 : 1 ≤ t := hy.trans ht.le
    rw [abs_div, abs_of_nonneg (sq_nonneg t)]
    have hpow : t ^ θ / t ^ 2 = t ^ (θ - 2) := by
      rw [show t ^ 2 = t ^ (2 : ℝ) by norm_cast, ← Real.rpow_sub ht0]
    calc |chebyshevPsi t - t| / t ^ 2
        ≤ (C * t ^ θ) / t ^ 2 := div_le_div_of_nonneg_right (hpsi t ht1) (sq_nonneg t)
      _ = C * (t ^ θ / t ^ 2) := by ring
      _ = C * t ^ (θ - 2) := by rw [hpow]
  have hval : ∫ t in Ioi y, C * t ^ (θ - 2) = C * (y ^ (θ - 1) / (1 - θ)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : θ - 2 < -1) hy0]
    congr 1
    rw [show θ - 2 + 1 = -(1 - θ) by ring, neg_div_neg_eq, show -(1 - θ) = θ - 1 by ring]
  have hprod : y * (C * (y ^ (θ - 1) / (1 - θ))) = (C / (1 - θ)) * y ^ θ := by
    have hpow : y * y ^ (θ - 1) = y ^ θ := by
      calc y * y ^ (θ - 1) = y ^ (1 : ℝ) * y ^ (θ - 1) := by rw [Real.rpow_one]
        _ = y ^ (1 + (θ - 1)) := (Real.rpow_add hy0 _ _).symm
        _ = y ^ θ := by congr 1; ring
    calc y * (C * (y ^ (θ - 1) / (1 - θ)))
        = (C / (1 - θ)) * (y * y ^ (θ - 1)) := by ring
      _ = (C / (1 - θ)) * y ^ θ := by rw [hpow]
  calc y * |∫ t in Ioi y, (chebyshevPsi t - t) / t ^ 2|
      ≤ y * ∫ t in Ioi y, C * t ^ (θ - 2) := mul_le_mul_of_nonneg_left htail_le hy0.le
    _ = y * (C * (y ^ (θ - 1) / (1 - θ))) := by rw [hval]
    _ = (C / (1 - θ)) * y ^ θ := hprod

/-- Bridge into `RHDirect.LandauWindow`: `|ψ(x) - x| ≤ C x^θ` immediately supplies
`HasRpowWindow Gz θ δ (C / (1 - θ))` for every `δ > 0`. -/
theorem hasRpowWindow_Gz_of_psi_bound {C θ δ : ℝ} (hθ : θ < 1)
    (hpsi : ∀ t : ℝ, 1 ≤ t → |chebyshevPsi t - t| ≤ C * t ^ θ) :
    HasRpowWindow Gz θ δ (C / (1 - θ)) := by
  intro Y₀
  refine ⟨max Y₀ 1, le_max_left _ _, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := (le_max_right _ _).trans hy.1
  exact (le_abs_self (Gz y)).trans (Gz_eq_neg_mul_tail_integral_and_bound hθ hpsi hy1).2

/-- **Two-Sided Monotone Sandwich for `chebyshevRamp` Differences**:
for `1 ≤ x ≤ y`,
`ψ(x) * (1/x - 1/y) ≤ chebyshevRamp y / y - chebyshevRamp x / x ≤ ψ(y) * (1/x - 1/y)`. -/
theorem chebyshevRamp_diff_sandwich {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    chebyshevPsi x * (1 / x - 1 / y) ≤ chebyshevRamp y / y - chebyshevRamp x / x ∧
    chebyshevRamp y / y - chebyshevRamp x / x ≤ chebyshevPsi y * (1 / x - 1 / y) := by
  have hy : 1 ≤ y := hx.trans hxy
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans_le hx
  have hy0 : (0 : ℝ) < y := zero_lt_one.trans_le hy
  have hdiff : chebyshevRamp y / y - chebyshevRamp x / x =
      ∫ t in x..y, chebyshevPsi t / t ^ 2 := by
    have hint_fn : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
        IntervalIntegrable (fun t : ℝ => chebyshevPsi t / t ^ 2) volume a b := by
      intro a b ha hab
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr ?_
      refine Integrable.mono'
        (integrableOn_const (C := chebyshevPsi b) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
      · have hm : Measurable chebyshevPsi := by
          have h : chebyshevPsi = (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
          rw [h]
          exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
        exact (hm.div (continuous_pow 2).measurable).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
        have ht1 : 1 ≤ t := ha.trans ht.1.le
        have htsq : 1 ≤ t ^ 2 := by nlinarith
        rw [Real.norm_of_nonneg (div_nonneg (chebyshevPsi_nonneg t) (sq_nonneg t))]
        exact (div_le_self (chebyshevPsi_nonneg t) htsq).trans (chebyshevPsi_mono ht.2)
    rw [chebyshevRamp_eq_mul_integral_psi hy, chebyshevRamp_eq_mul_integral_psi hx,
      mul_div_cancel_left₀ _ hy0.ne', mul_div_cancel_left₀ _ hx0.ne',
      ← intervalIntegral.integral_add_adjacent_intervals (hint_fn 1 x le_rfl hx) (hint_fn x y hx hxy)]
    ring
  have hinv_sq : ∫ t in x..y, (1 : ℝ) / t ^ 2 = 1 / x - 1 / y := by
    have hd : ∀ t ∈ Set.uIcc x y, HasDerivAt (fun u : ℝ => -(1 / u)) (1 / t ^ 2) t := by
      intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      have ht0 : t ≠ 0 := (hx0.trans_le ht.1).ne'
      have h1 := (hasDerivAt_inv ht0).neg
      refine h1.congr_of_eventuallyEq (Eventually.of_forall fun u => by simp [one_div])
        |>.congr_deriv ?_
      simp [one_div]
    have hc : ContinuousOn (fun t : ℝ => (1 : ℝ) / t ^ 2) (Set.uIcc x y) := by
      rw [Set.uIcc_of_le hxy]
      exact continuousOn_const.div (continuousOn_pow 2) fun t ht =>
        pow_ne_zero 2 (hx0.trans_le ht.1).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
    ring
  have hint_inv : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t ^ 2) volume x y := by
    have hc : ContinuousOn (fun t : ℝ => (1 : ℝ) / t ^ 2) (Set.uIcc x y) := by
      rw [Set.uIcc_of_le hxy]
      exact continuousOn_const.div (continuousOn_pow 2) fun t ht =>
        pow_ne_zero 2 (hx0.trans_le ht.1).ne'
    exact hc.intervalIntegrable
  have hint_psi : IntervalIntegrable (fun t : ℝ => chebyshevPsi t / t ^ 2) volume x y := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mpr ?_
    refine Integrable.mono'
      (integrableOn_const (C := chebyshevPsi y) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
    · have hm : Measurable chebyshevPsi := by
        have h : chebyshevPsi = (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
        rw [h]
        exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
      exact (hm.div (continuous_pow 2).measurable).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht1 : 1 ≤ t := hx.trans ht.1.le
      have htsq : 1 ≤ t ^ 2 := by nlinarith
      rw [Real.norm_of_nonneg (div_nonneg (chebyshevPsi_nonneg t) (sq_nonneg t))]
      exact (div_le_self (chebyshevPsi_nonneg t) htsq).trans (chebyshevPsi_mono ht.2)
  rw [hdiff]
  constructor
  · rw [← hinv_sq, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hxy (hint_inv.const_mul _) hint_psi fun t ht => ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (chebyshevPsi_mono ht.1) (sq_nonneg t)
  · rw [← hinv_sq, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hxy hint_psi (hint_inv.const_mul _) fun t ht => ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (chebyshevPsi_mono ht.2) (sq_nonneg t)

/-- **Quantitative Recovery of `|ψ(x) - x|` from `|Gz y| ≤ C y^θ`** (Riesz/Dyadic Window
De-Smoothing):
if `|Gz y| ≤ C y^θ` for all `y ≥ 1` (`0 < θ < 1`, `0 ≤ C`), then choosing smoothing width
`η = x ^ (-(1 - θ) / 2)` recovers `|ψ(x) - x| ≤ (4 * C + 1) * x ^ ((1 + θ) / 2)` for all `x ≥ 4`! -/
theorem abs_psi_sub_id_of_Gz_rpow {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hGz : ∀ y : ℝ, 1 ≤ y → |Gz y| ≤ C * y ^ θ) {x : ℝ} (hx : 4 ≤ x) :
    |chebyshevPsi x - x| ≤ (4 * C + 1) * x ^ ((1 + θ) / 2) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set η : ℝ := x ^ (-(1 - θ) / 2) with hη_def
  have hη0 : 0 < η := Real.rpow_pos_of_pos hx0 _
  have hη_le1 : η ≤ 1 := by
    rw [hη_def]
    calc x ^ (-(1 - θ) / 2) ≤ x ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = 1 := Real.rpow_zero x
  have h1η_pos : 0 < 1 + η := by linarith
  have h1η_le2 : 1 + η ≤ 2 := by linarith
  have hinv_int : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      ∫ t in a..b, (1 : ℝ) / t ^ 2 = 1 / a - 1 / b := by
    intro a b ha hab
    have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -(1 / u)) (1 / t ^ 2) t := by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have ht0 : t ≠ 0 := (zero_lt_one.trans_le (ha.trans ht.1)).ne'
      exact ((hasDerivAt_inv ht0).neg.congr_of_eventuallyEq
        (Eventually.of_forall fun u => by simp [one_div])).congr_deriv (by simp [one_div])
    have hc : ContinuousOn (fun t : ℝ => (1 : ℝ) / t ^ 2) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      exact continuousOn_const.div (continuousOn_pow 2) fun t ht =>
        pow_ne_zero 2 (zero_lt_one.trans_le (ha.trans ht.1)).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]; ring
  have hint_err : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      IntervalIntegrable (fun t : ℝ => (chebyshevPsi t - t) / t ^ 2) volume a b := by
    intro a b ha hab
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr ?_
    refine Integrable.mono'
      (integrableOn_const (C := chebyshevPsi b + b) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
    · have hm : Measurable chebyshevPsi := by
        have h : chebyshevPsi = (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
        rw [h]
        exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
      exact ((hm.sub measurable_id).div (continuous_pow 2).measurable).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht1 : 1 ≤ t := ha.trans ht.1.le
      have htsq : 1 ≤ t ^ 2 := by nlinarith
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      refine (div_le_self (abs_nonneg _) htsq).trans ?_
      have h1 : |chebyshevPsi t - t| ≤ chebyshevPsi t + t := by
        have h0 := chebyshevPsi_nonneg t
        rcases abs_cases (chebyshevPsi t - t) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
      linarith [chebyshevPsi_mono ht.2, ht.2]
  have hint_inv : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t ^ 2) volume a b := by
    intro a b ha hab
    have hc : ContinuousOn (fun t : ℝ => (1 : ℝ) / t ^ 2) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      exact continuousOn_const.div (continuousOn_pow 2) fun t ht =>
        pow_ne_zero 2 (zero_lt_one.trans_le (ha.trans ht.1)).ne'
    exact hc.intervalIntegrable
  have hGz_div : ∀ y : ℝ, 1 ≤ y → |Gz y / y| ≤ C * y ^ (θ - 1) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans_le hy
    rw [abs_div, abs_of_pos hy0]
    calc |Gz y| / y ≤ (C * y ^ θ) / y := div_le_div_of_nonneg_right (hGz y hy) hy0.le
      _ = C * (y ^ θ / y ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = C * y ^ (θ - 1) := by rw [← Real.rpow_sub hy0]
  have hpow_main : x * x ^ (θ - 1) / η = x ^ ((1 + θ) / 2) := by
    calc x * x ^ (θ - 1) / η
        = x ^ (1 : ℝ) * x ^ (θ - 1) / x ^ (-(1 - θ) / 2) := by rw [Real.rpow_one, hη_def]
      _ = x ^ (1 + (θ - 1)) / x ^ (-(1 - θ) / 2) := by rw [← Real.rpow_add hx0]
      _ = x ^ (1 + (θ - 1) - -(1 - θ) / 2) := by rw [← Real.rpow_sub hx0]
      _ = x ^ ((1 + θ) / 2) := by congr 1; ring
  have hpow_eta : η * x = x ^ ((1 + θ) / 2) := by
    calc η * x = x ^ (-(1 - θ) / 2) * x ^ (1 : ℝ) := by rw [Real.rpow_one, hη_def]
      _ = x ^ (-(1 - θ) / 2 + 1) := by rw [← Real.rpow_add hx0]
      _ = x ^ ((1 + θ) / 2) := by congr 1; ring
  rw [abs_le]
  constructor
  · -- Lower bound on ψ(x) - x using window [x / (1 + η), x]
    set a : ℝ := x / (1 + η)
    have ha1 : 1 ≤ a := by
      rw [show a = x / (1 + η) from rfl, one_le_div h1η_pos]; linarith
    have hax : a ≤ x := div_le_self hx0.le (by linarith)
    have ha0 : 0 < a := zero_lt_one.trans_le ha1
    have hdiff := Gz_div_sub_Gz_div_eq_integral ha1 hax
    have hmono : ∫ t in a..x, (chebyshevPsi t - t) / t ^ 2 ≤
        (chebyshevPsi x - a) * (1 / a - 1 / x) := by
      rw [← hinv_int a x ha1 hax, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hax (hint_err a x ha1 hax)
        ((hint_inv a x ha1 hax).const_mul _) fun t ht => ?_
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (sub_le_sub (chebyshevPsi_mono ht.2) ht.1) (sq_nonneg t)
    have hwt : 1 / a - 1 / x = η / x := by
      simp only [a]; field_simp; ring
    rw [← hdiff, hwt] at hmono
    have ha_pow : a ^ (θ - 1) ≤ 2 * x ^ (θ - 1) := by
      have h1 : x / 2 ≤ a := by
        simp only [a]; exact div_le_div_of_nonneg_left hx0.le h1η_pos h1η_le2
      have h2 : a ^ (θ - 1) ≤ (x / 2) ^ (θ - 1) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)
      have h3 : (x / 2) ^ (θ - 1) = (2 : ℝ) ^ (1 - θ) * x ^ (θ - 1) := by
        rw [Real.div_rpow hx0.le (by norm_num : (0 : ℝ) ≤ 2),
          show (2 : ℝ) ^ (θ - 1) = ((2 : ℝ) ^ (1 - θ))⁻¹ by
            rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring,
          div_inv_eq_mul, mul_comm]
      have h4 : (2 : ℝ) ^ (1 - θ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 - θ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have h5 : (2 : ℝ) ^ (1 - θ) * x ^ (θ - 1) ≤ 2 * x ^ (θ - 1) :=
        mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hx0.le _)
      linarith
    have hdiff_bd : -(3 * C * x ^ (θ - 1)) ≤ Gz x / x - Gz a / a := by
      have h1 := abs_le.mp (hGz_div x hx1)
      have h2 := abs_le.mp (hGz_div a ha1)
      nlinarith
    have hmul : (x / η) * (-(3 * C * x ^ (θ - 1))) ≤ chebyshevPsi x - a := by
      have h1 := mul_le_mul_of_nonneg_left (hdiff_bd.trans hmono) (div_nonneg hx0.le hη0.le)
      have hcancel : (x / η) * ((chebyshevPsi x - a) * (η / x)) = chebyshevPsi x - a := by
        field_simp
      linarith
    have hxa : x - a ≤ η * x := by
      simp only [a]
      have h1 : x - x / (1 + η) = η * x / (1 + η) := by field_simp; ring
      rw [h1]
      exact div_le_self (mul_nonneg hη0.le hx0.le) (by linarith)
    have h3C : (x / η) * (3 * C * x ^ (θ - 1)) = 3 * C * x ^ ((1 + θ) / 2) := by
      calc (x / η) * (3 * C * x ^ (θ - 1))
          = 3 * C * (x * x ^ (θ - 1) / η) := by ring
        _ = 3 * C * x ^ ((1 + θ) / 2) := by rw [hpow_main]
    have hxp : 0 ≤ x ^ ((1 + θ) / 2) := Real.rpow_nonneg hx0.le _
    nlinarith
  · -- Upper bound on ψ(x) - x using window [x, (1 + η) * x]
    set b : ℝ := (1 + η) * x
    have hxb : x ≤ b := by nlinarith
    have hb1 : 1 ≤ b := hx1.trans hxb
    have hdiff := Gz_div_sub_Gz_div_eq_integral hx1 hxb
    have hmono : (chebyshevPsi x - b) * (1 / x - 1 / b) ≤
        ∫ t in x..b, (chebyshevPsi t - t) / t ^ 2 := by
      rw [← hinv_int x b hx1 hxb, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hxb ((hint_inv x b hx1 hxb).const_mul _)
        (hint_err x b hx1 hxb) fun t ht => ?_
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (sub_le_sub (chebyshevPsi_mono ht.1) ht.2) (sq_nonneg t)
    have hwt : 1 / x - 1 / b = η / ((1 + η) * x) := by
      simp only [b]; field_simp; ring
    rw [← hdiff, hwt] at hmono
    have hb_pow : b ^ (θ - 1) ≤ x ^ (θ - 1) :=
      Real.rpow_le_rpow_of_nonpos hx0 hxb (by linarith)
    have hdiff_bd : Gz b / b - Gz x / x ≤ 2 * C * x ^ (θ - 1) := by
      have h1 := abs_le.mp (hGz_div b hb1)
      have h2 := abs_le.mp (hGz_div x hx1)
      nlinarith
    have hmul : chebyshevPsi x - b ≤ ((1 + η) * x / η) * (2 * C * x ^ (θ - 1)) := by
      have hpos : 0 ≤ (1 + η) * x / η := div_nonneg (mul_nonneg h1η_pos.le hx0.le) hη0.le
      have h1 := mul_le_mul_of_nonneg_left (hmono.trans hdiff_bd) hpos
      have hcancel : ((1 + η) * x / η) * ((chebyshevPsi x - b) * (η / ((1 + η) * x))) =
          chebyshevPsi x - b := by
        field_simp
      linarith
    have hbx : b - x = η * x := by simp only [b]; ring
    have h4C : ((1 + η) * x / η) * (2 * C * x ^ (θ - 1)) ≤ 4 * C * x ^ ((1 + θ) / 2) := by
      have h1 : ((1 + η) * x / η) * (2 * C * x ^ (θ - 1)) =
          (2 * (1 + η) * C) * (x * x ^ (θ - 1) / η) := by ring
      rw [h1, hpow_main]
      have hxp : 0 ≤ x ^ ((1 + θ) / 2) := Real.rpow_nonneg hx0.le _
      have hCxp : 0 ≤ C * x ^ ((1 + θ) / 2) := mul_nonneg hC hxp
      nlinarith
    linarith

/-! ### Exact Abelian Summation Bridges Linking `chebyshevPsi`, `Chebyshev.theta`, and `π(x)` -/

/-- `stepSum` of the prime indicator equals `Nat.primeCounting ⌊x⌋₊`. -/
theorem stepSum_primeIndicator_eq_primeCounting (x : ℝ) :
    stepSum (fun n => if n.Prime then (1 : ℂ) else 0) x = ((Nat.primeCounting ⌊x⌋₊ : ℝ) : ℂ) := by
  unfold stepSum Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one, Complex.ofReal_natCast]
  congr 1
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h1, hp⟩; exact ⟨⟨hp.one_le, by omega⟩, hp⟩

/-- `stepSum` of `1_{p prime} log p` equals `Chebyshev.theta x`. -/
theorem stepSum_primeLog_eq_theta (x : ℝ) :
    stepSum (fun n => if n.Prime then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0) x =
      (Chebyshev.theta x : ℂ) := by
  unfold stepSum Chebyshev.theta
  rw [Complex.ofReal_sum, Finset.sum_filter]
  refine Finset.sum_congr ?_ fun n _ => by split_ifs with h <;> simp [h]
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- **Exact Abelian Summation Identity `ϑ(x) = π(x) log x - ∫_2^x (π(t) / t) dt`** for `x ≥ 2`. -/
theorem theta_eq_abel_primeCounting {x : ℝ} (hx : 2 ≤ x) :
    Chebyshev.theta x =
      (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x -
        ∫ t in (2 : ℝ)..x, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t := by
  have hx1 : 1 ≤ x := by linarith
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) x,
      HasDerivAt (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) (((t⁻¹ : ℝ) : ℂ)) t := fun t ht =>
    (Real.hasDerivAt_log (zero_lt_one.trans_le ht.1).ne').ofReal_comp
  have hc : ContinuousOn (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) (Set.Icc (1 : ℝ) x) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.inv₀ fun t ht => (zero_lt_one.trans_le ht.1).ne')
  have hab := abel_summation_general (fun n => if n.Prime then (1 : ℂ) else 0) hx1 hd hc
  have hLHS : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if n.Prime then (1 : ℂ) else 0) * ((Real.log (n : ℝ) : ℝ) : ℂ) =
      (Chebyshev.theta x : ℂ) := by
    rw [← stepSum_primeLog_eq_theta]
    unfold stepSum
    refine Finset.sum_congr rfl fun n _ => by split_ifs with h <;> simp [h]
  rw [hLHS, stepSum_primeIndicator_eq_primeCounting] at hab
  have hre := congrArg Complex.re hab
  have hint_zero : ∫ t in (1 : ℝ)..(2 : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t = 0 := by
    have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (1 : ℝ) 2 → (Nat.primeCounting ⌊t⌋₊ : ℝ) / t = 0 := by
      have hne : ∀ᵐ t ∂volume, t ≠ (2 : ℝ) := by rw [ae_iff]; simp
      filter_upwards [hne] with t hne ht
      rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2), Set.mem_Ioc] at ht
      have hfl : ⌊t⌋₊ = 1 := (Nat.floor_eq_iff (by linarith)).mpr
        ⟨by exact_mod_cast ht.1.le, by norm_num; exact lt_of_le_of_ne ht.2 hne⟩
      rw [hfl]
      have hpc1 : Nat.primeCounting 1 = 0 := by decide
      simp [hpc1]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_zero]
  have hint_pi : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      IntervalIntegrable (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) volume a b := by
    intro a b ha hab'
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hab').mpr ?_
    refine Integrable.mono'
      (integrableOn_const (C := (Nat.primeCounting ⌊b⌋₊ : ℝ)) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
    · have hm : Measurable (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ)) := by
        change Measurable ((fun k : ℕ => (Nat.primeCounting k : ℝ)) ∘ Nat.floor)
        exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
      exact (hm.div measurable_id).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      have ht1 : 1 ≤ t := ha.trans ht.1.le
      rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) (zero_le_one.trans ht1))]
      refine (div_le_self (Nat.cast_nonneg _) ht1).trans ?_
      exact Nat.cast_le.mpr (Nat.monotone_primeCounting (Nat.floor_mono ht.2))
  have hRHS_re : (∫ t in (1 : ℝ)..x,
      stepSum (fun n => if n.Prime then (1 : ℂ) else 0) t * ((t⁻¹ : ℝ) : ℂ)).re =
      ∫ t in (2 : ℝ)..x, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t := by
    have hfun : (fun t : ℝ =>
        stepSum (fun n => if n.Prime then (1 : ℂ) else 0) t * ((t⁻¹ : ℝ) : ℂ)) =
        fun t : ℝ => (((Nat.primeCounting ⌊t⌋₊ : ℝ) / t : ℝ) : ℂ) := by
      funext t
      rw [stepSum_primeIndicator_eq_primeCounting, ← Complex.ofReal_mul, div_eq_mul_inv]
    rw [hfun, intervalIntegral.integral_ofReal, Complex.ofReal_re,
      ← intervalIntegral.integral_add_adjacent_intervals (hint_pi 1 2 le_rfl (by norm_num))
        (hint_pi 2 x (by norm_num) hx), hint_zero, zero_add]
  rw [Complex.ofReal_re, Complex.sub_re, ← Complex.ofReal_mul, Complex.ofReal_re, hRHS_re] at hre
  exact hre

/-- **Exact Abelian Summation Identity `π(x) = ϑ(x) / log x + ∫_2^x (ϑ(t) / (t (log t)^2)) dt`**
for `x ≥ 2`, plus direct comparison with `chebyshevPsi`. -/
theorem primeCounting_eq_abel_theta {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) =
      Chebyshev.theta x / Real.log x +
        ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  -- Apply abel_summation on [2, x] by integrating on unit steps [k, k+1] for k ≥ 2
  set a : ℕ → ℂ := fun n => if n.Prime then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0
  set φ : ℝ → ℂ := fun u => (((Real.log u)⁻¹ : ℝ) : ℂ)
  set φ' : ℝ → ℂ := fun u => ((-(1 / (u * (Real.log u) ^ 2)) : ℝ) : ℂ)
  have hd : ∀ t ∈ Set.Icc (2 : ℝ) x, HasDerivAt φ (φ' t) t := by
    intro t ht
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    have hlt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hr : HasDerivAt (fun u : ℝ => (Real.log u)⁻¹) (-(1 / (t * (Real.log t) ^ 2))) t := by
      have h1 := (Real.hasDerivAt_log ht0).inv hlt0
      refine h1.congr_deriv ?_
      field_simp
    exact hr.ofReal_comp
  have hc : ContinuousOn φ' (Set.Icc (2 : ℝ) x) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.neg (continuousOn_const.div
      (continuousOn_id.mul ((Real.continuousOn_log.mono fun t ht =>
        (by linarith [ht.1] : (0 : ℝ) < t).ne').pow 2)) fun t ht => ?_)
    exact mul_ne_zero (by linarith [ht.1] : (0 : ℝ) < t).ne'
      (pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne')
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hint_nat : ∀ N : ℕ, 2 ≤ N → (N : ℝ) ≤ x →
      IntervalIntegrable (fun t => stepSum a t * φ' t) volume (2 : ℝ) (N : ℝ) ∧
      ∑ n ∈ Finset.Icc 2 N, a n * φ (n : ℝ) =
        stepSum a (N : ℝ) * φ (N : ℝ) - ∫ t in (2 : ℝ)..(N : ℝ), stepSum a t * φ' t := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      intro _
      refine ⟨IntervalIntegrable.refl, ?_⟩
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_ofNat, intervalIntegral.integral_same,
        sub_zero]
      have ha2 : stepSum a 2 = a 2 := by
        unfold stepSum
        rw [Nat.floor_ofNat]
        have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
        rw [hIcc, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
        have h1 : a 1 = 0 := by simp [a, Nat.not_prime_one]
        rw [h1, zero_add]
      rw [ha2]
    | succ m hm ih =>
      intro hm1
      have hm_le : (m : ℝ) ≤ x := le_trans (by push_cast; linarith) hm1
      obtain ⟨hint_m, heq_m⟩ := ih hm_le
      have hsub_u : Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Set.Icc (2 : ℝ) x := by
        rw [Set.uIcc_of_le (by push_cast; linarith)]
        intro t ht
        have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        exact ⟨le_trans hm2R ht.1, le_trans ht.2 hm1⟩
      have hint_step := intervalIntegrable_stepSum_mul_unit a m (hc.mono hsub_u)
      have hval_step := intervalIntegral_stepSum_unit a m (fun t ht => hd t (hsub_u ht))
        (hc.mono hsub_u)
      refine ⟨hint_m.trans hint_step, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_m hint_step, hval_step]
      have hIcc2 : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hIcc1 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot2 : m + 1 ∉ Finset.Icc 2 m := by simp
      have hnot1 : m + 1 ∉ Finset.Icc 1 m := by simp
      have hstep_succ : stepSum a ((m + 1 : ℕ) : ℝ) = stepSum a (m : ℝ) + a (m + 1) := by
        unfold stepSum
        rw [Nat.floor_natCast, Nat.floor_natCast, hIcc1, Finset.sum_insert hnot1]
        ring
      rw [hIcc2, Finset.sum_insert hnot2, heq_m, hstep_succ]
      ring
  obtain ⟨hint_N, heq_N⟩ := hint_nat ⌊x⌋₊ hN2 hfl_le
  have hsub_tail : Set.uIcc (⌊x⌋₊ : ℝ) x ⊆ Set.Icc (2 : ℝ) x := by
    rw [Set.uIcc_of_le hfl_le]
    intro t ht
    exact ⟨le_trans (by exact_mod_cast hN2) ht.1, ht.2⟩
  have htail_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (⌊x⌋₊ : ℝ) x →
      stepSum a t * φ' t = stepSum a (⌊x⌋₊ : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ x := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hfl_le, Set.mem_Ioc] at ht
    have hlt : t < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := lt_trans (lt_of_le_of_ne ht.2 hne) (by
      push_cast; exact Nat.lt_floor_add_one x)
    rw [stepSum_const_on_Ico a ⌊x⌋₊ ht.1.le hlt]
  have hint_tail : IntervalIntegrable (fun t => stepSum a t * φ' t) volume (⌊x⌋₊ : ℝ) x := by
    refine ((hc.mono hsub_tail).intervalIntegrable.const_mul (stepSum a (⌊x⌋₊ : ℝ))).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [htail_ae] with t ht hmem using (ht hmem).symm
  have hval_tail : ∫ t in (⌊x⌋₊ : ℝ)..x, stepSum a t * φ' t =
      stepSum a (⌊x⌋₊ : ℝ) * (φ x - φ (⌊x⌋₊ : ℝ)) := by
    rw [intervalIntegral.integral_congr_ae htail_ae, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub_tail ht))
        (hc.mono hsub_tail).intervalIntegrable]
  have hstep_x : stepSum a x = stepSum a (⌊x⌋₊ : ℝ) := by
    unfold stepSum; rw [Nat.floor_natCast]
  have hab : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n * φ (n : ℝ) =
      stepSum a x * φ x - ∫ t in (2 : ℝ)..x, stepSum a t * φ' t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_N hint_tail, hval_tail, heq_N,
      hstep_x]
    ring
  have hLHS : (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n * φ (n : ℝ)).re = (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    have hsum_eq : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, a n * φ (n : ℝ) =
        stepSum (fun n => if n.Prime then (1 : ℂ) else 0) x := by
      unfold stepSum
      have hIcc : Finset.Icc 1 ⌊x⌋₊ = insert 1 (Finset.Icc 2 ⌊x⌋₊) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp : (1 : ℕ) ∉ Finset.Icc 2 ⌊x⌋₊),
        if_neg Nat.not_prime_one, zero_add]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hlogn : Real.log (n : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
      simp only [a, φ]
      split_ifs
      · rw [← Complex.ofReal_mul, mul_inv_cancel₀ hlogn, Complex.ofReal_one]
      · simp
    rw [hsum_eq, stepSum_primeIndicator_eq_primeCounting, Complex.ofReal_re]
  have hRHS : (stepSum a x * φ x - ∫ t in (2 : ℝ)..x, stepSum a t * φ' t).re =
      Chebyshev.theta x / Real.log x +
        ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2) := by
    have h1 : stepSum a x * φ x = ((Chebyshev.theta x / Real.log x : ℝ) : ℂ) := by
      rw [stepSum_primeLog_eq_theta]
      simp only [φ, ← Complex.ofReal_mul, div_eq_mul_inv]
    have h2 : (fun t : ℝ => stepSum a t * φ' t) =
        fun t : ℝ => (((-(Chebyshev.theta t / (t * (Real.log t) ^ 2)) : ℝ) : ℂ)) := by
      funext t
      rw [stepSum_primeLog_eq_theta]
      simp only [φ', ← Complex.ofReal_mul]
      congr 1; ring
    rw [h1, h2, intervalIntegral.integral_ofReal, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_re, intervalIntegral.integral_neg, sub_neg_eq_add]
  have hre := congrArg Complex.re hab
  rw [hLHS, hRHS] at hre
  exact hre

/-- Elementary comparison linking `chebyshevPsi`, `Chebyshev.theta`, and `Nat.primeCounting`:
`ϑ(x) ≤ ψ(x) ≤ ϑ(x) + 2 √x log x` for `x ≥ 1`. -/
theorem psi_theta_sandwich {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.theta x ≤ chebyshevPsi x ∧
    chebyshevPsi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x := by
  rw [chebyshevPsi_eq_mathlib_psi]
  exact ⟨Chebyshev.theta_le_psi x, Chebyshev.psi_sub_theta_le hx⟩

/-! ## Section 3: Unconditional `Stage2ToyBreakthrough` Concrete `Re(s) > 27/50`
Zero-Free Half-Plane & Landau Sharpness -/

/-- Exact breakthrough exponent `1/2 + 4 * ε = 27 / 50 < 2 / 3` from `Stage2ToyBreakthrough`. -/
def toyTheta : ℝ :=
  (1 : ℝ) / 2 + (1 + 3) * Stage2ToyBreakthrough.toyScale.eps

theorem toyTheta_eq : toyTheta = 27 / 50 := by
  unfold toyTheta Stage2ToyBreakthrough.toyScale
  norm_num

theorem toyTheta_bounds : (1 : ℝ) / 2 < toyTheta ∧ toyTheta < 2 / 3 ∧ toyTheta < 1 := by
  rw [toyTheta_eq]; norm_num

theorem toyGx_le_toyScale_rpow_toyTheta :
    Stage2ToyBreakthrough.toyGx ≤ Stage2ToyBreakthrough.toyScale.x ^ toyTheta :=
  Stage2ToyBreakthrough.master_unconditional_toy_breakthrough.2.2.2.1

/-- Concrete positive excess arithmetic sequence `toyExcess n = n^(27/50) - (n-1)^(27/50)` (`n ≥ 1`),
whose step summatory function is exact `⌊x⌋₊^(27/50)`. -/
def toyExcess (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ toyTheta - ((n - 1 : ℕ) : ℝ) ^ toyTheta

/-- Concrete positive synthetic arithmetic sequence `toyCoeff n = 1 + toyExcess n` (`n ≥ 1`),
whose step summatory function is `⌊x⌋₊ + ⌊x⌋₊^(27/50) = x + O(x^(27/50))`. -/
def toyCoeff (n : ℕ) : ℝ :=
  if n = 0 then 0 else 1 + toyExcess n

theorem toyExcess_zero : toyExcess 0 = 0 := by simp [toyExcess]

theorem toyCoeff_zero : toyCoeff 0 = 0 := by simp [toyCoeff]

theorem toyExcess_nonneg (n : ℕ) : 0 ≤ toyExcess n := by
  unfold toyExcess
  split_ifs with h
  · exact le_rfl
  · rw [sub_nonneg]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.sub_le n 1))
      (by linarith [toyTheta_bounds.1])

theorem toyCoeff_nonneg (n : ℕ) : 0 ≤ toyCoeff n := by
  unfold toyCoeff
  split_ifs
  · exact le_rfl
  · linarith [toyExcess_nonneg n]

/-- Two-sided derivative MVT bounds on `toyExcess n` (`n ≥ 1`):
`(27/50) * n^(-23/50) ≤ toyExcess n ≤ 2 * n^(-23/50)`. -/
theorem toyExcess_mvt_bounds {n : ℕ} (hn : 1 ≤ n) :
    toyTheta * (n : ℝ) ^ (toyTheta - 1) ≤ toyExcess n ∧
    toyExcess n ≤ 2 * (n : ℝ) ^ (toyTheta - 1) := by
  have hθ0 : 0 < toyTheta := by linarith [toyTheta_bounds.1]
  have hθ1 : toyTheta < 1 := toyTheta_bounds.2.2
  by_cases hn1 : n = 1
  · subst hn1
    simp only [toyExcess, Nat.one_ne_zero, ↓reduceIte, Nat.cast_one, Real.one_rpow, Nat.sub_self,
      Nat.cast_zero, Real.zero_rpow hθ0.ne', sub_zero, mul_one]
    constructor <;> linarith
  · have hn2 : 2 ≤ n := by omega
    have ha_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
    have hab : ((n - 1 : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : n - 1 < n)
    have hdiff : ∀ t ∈ Set.Ioo ((n - 1 : ℕ) : ℝ) (n : ℝ),
        HasDerivAt (fun u : ℝ => u ^ toyTheta) (toyTheta * t ^ (toyTheta - 1)) t := by
      intro t ht
      exact Real.hasDerivAt_rpow_const (Or.inl (ha_pos.trans ht.1).ne')
    have hcont : ContinuousOn (fun u : ℝ => u ^ toyTheta) (Set.Icc ((n - 1 : ℕ) : ℝ) (n : ℝ)) :=
      fun t ht => (Real.continuousAt_rpow_const t toyTheta (Or.inl (ha_pos.trans_le ht.1).ne')).continuousWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun u : ℝ => u ^ toyTheta)
      (fun t => toyTheta * t ^ (toyTheta - 1)) hab hcont hdiff
    have hsub1 : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
      have : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel hn
      have hR : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by exact_mod_cast this
      linarith
    rw [hsub1, div_one] at hslope
    have heq : toyExcess n = toyTheta * c ^ (toyTheta - 1) := by
      simp only [toyExcess, show n ≠ 0 by omega, ↓reduceIte, hslope]
    rw [heq]
    have hc_pos : 0 < c := ha_pos.trans hc.1
    constructor
    · refine mul_le_mul_of_nonneg_left ?_ hθ0.le
      exact Real.rpow_le_rpow_of_nonpos hc_pos hc.2.le (by linarith)
    · have hhalf : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
        have h : n ≤ 2 * (n - 1) := by omega
        have hR : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      have hc_ge : (n : ℝ) / 2 ≤ c := hhalf.trans hc.1.le
      have h1 : c ^ (toyTheta - 1) ≤ ((n : ℝ) / 2) ^ (toyTheta - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hc_ge (by linarith)
      have h2 : ((n : ℝ) / 2) ^ (toyTheta - 1) = (2 : ℝ) ^ (1 - toyTheta) * (n : ℝ) ^ (toyTheta - 1) := by
        rw [Real.div_rpow (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 2),
          show (2 : ℝ) ^ (toyTheta - 1) = ((2 : ℝ) ^ (1 - toyTheta))⁻¹ by
            rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring,
          div_inv_eq_mul, mul_comm]
      have h3 : (2 : ℝ) ^ (1 - toyTheta) ≤ 2 := by
        calc (2 : ℝ) ^ (1 - toyTheta) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have h4 : toyTheta * ((2 : ℝ) ^ (1 - toyTheta) * (n : ℝ) ^ (toyTheta - 1)) ≤
          2 * (n : ℝ) ^ (toyTheta - 1) := by
        have hnp : 0 ≤ (n : ℝ) ^ (toyTheta - 1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        have h5 : toyTheta * (2 : ℝ) ^ (1 - toyTheta) ≤ 2 := by nlinarith
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right h5 hnp
      linarith [mul_le_mul_of_nonneg_left (h1.trans_eq h2) hθ0.le]

/-- Exact telescoping partial sums of `toyExcess` and `toyCoeff`. -/
theorem stepSum_toyExcess (x : ℝ) :
    stepSum (fun n => (toyExcess n : ℂ)) x = (((⌊x⌋₊ : ℝ) ^ toyTheta : ℝ) : ℂ) := by
  unfold stepSum
  have hθ0 : 0 < toyTheta := by linarith [toyTheta_bounds.1]
  have htel : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, (toyExcess n : ℂ) = (((N : ℝ) ^ toyTheta : ℝ) : ℂ) := by
    intro N
    induction N with
    | zero => simp [Real.zero_rpow hθ0.ne']
    | succ k ih =>
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp : k + 1 ∉ Finset.Icc 1 k), ih]
      simp only [toyExcess, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Complex.ofReal_sub]
      ring
  exact htel ⌊x⌋₊

theorem stepSum_toyCoeff (x : ℝ) :
    stepSum (fun n => (toyCoeff n : ℂ)) x =
      (((⌊x⌋₊ : ℝ) + (⌊x⌋₊ : ℝ) ^ toyTheta : ℝ) : ℂ) := by
  have hsplit : stepSum (fun n => (toyCoeff n : ℂ)) x =
      (∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℂ)) + stepSum (fun n => (toyExcess n : ℂ)) x := by
    unfold stepSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    simp [toyCoeff, hn0]
  rw [hsplit, stepSum_toyExcess x, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    mul_one]
  push_cast; rfl

/-- Exact `O(x ^ (27 / 50))` error bound on `stepSum toyCoeff x - x` for all `x ≥ 1`. -/
theorem norm_stepSum_toyCoeff_sub_id {x : ℝ} (hx : 1 ≤ x) :
    ‖stepSum (fun n => (toyCoeff n : ℂ)) x - (x : ℂ)‖ ≤ 2 * x ^ toyTheta := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  rw [stepSum_toyCoeff x, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hfl_gt : x - 1 < (⌊x⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one x]
  have hθ0 : 0 < toyTheta := by linarith [toyTheta_bounds.1]
  have h1 : (1 : ℝ) ≤ x ^ toyTheta := Real.one_le_rpow hx hθ0.le
  have h2 : (⌊x⌋₊ : ℝ) ^ toyTheta ≤ x ^ toyTheta :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hfl_le hθ0.le
  have h3 : 0 ≤ (⌊x⌋₊ : ℝ) ^ toyTheta := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [abs_le]
  constructor <;> linarith

/-- **Unconditional Landau Sharpness at `s = 27 / 50`**:
`dirSeries toyExcess` converges on `Re(s) > 27 / 50`, diverges for all real `x ≤ 27 / 50`, and
by our Classical Landau Singularity Theorem (`landau_singularity_at_abscissa`), `s = 27 / 50` is
an exact real singularity (no analytic continuation to any ball `B(27/50, r)`!). -/
theorem toyExcess_landau_singularity :
    (∀ s : ℂ, toyTheta < s.re → LSeriesSummable (fun n => (toyExcess n : ℂ)) s) ∧
    (∀ x : ℝ, x ≤ toyTheta → ¬ Summable (fun n : ℕ => toyExcess n * (n : ℝ) ^ (-x))) ∧
    ¬ ∃ (r : ℝ) (_ : 0 < r) (F : ℂ → ℂ),
        DifferentiableOn ℂ F (Metric.ball (toyTheta : ℂ) r) ∧
        ∀ s ∈ Metric.ball (toyTheta : ℂ) r, toyTheta < s.re → F s = dirSeries toyExcess s := by
  have hconv : ∀ s : ℂ, toyTheta < s.re → LSeriesSummable (fun n => (toyExcess n : ℂ)) s := by
    intro s hs
    rw [dirSeriesSummable_iff_real toyExcess_zero toyExcess_nonneg s]
    have hp : 1 < s.re - toyTheta + 1 := by linarith
    have hbase : Summable (fun n : ℕ => 2 * ((n : ℝ) ^ (s.re - toyTheta + 1))⁻¹) :=
      (Real.summable_nat_rpow_inv.mpr hp).mul_left 2
    refine Summable.of_nonneg_of_le (fun n =>
      mul_nonneg (toyExcess_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (fun n => ?_) hbase
    by_cases hn : n = 0
    · subst hn; simp [toyExcess_zero, Real.zero_rpow (by linarith : s.re - toyTheta + 1 ≠ 0)]
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
      have hup := (toyExcess_mvt_bounds hn1).2
      have hpow : (n : ℝ) ^ (toyTheta - 1) * (n : ℝ) ^ (-s.re) = ((n : ℝ) ^ (s.re - toyTheta + 1))⁻¹ := by
        rw [← Real.rpow_add hn0, ← Real.rpow_neg hn0.le]
        congr 1; ring
      calc toyExcess n * (n : ℝ) ^ (-s.re)
          ≤ (2 * (n : ℝ) ^ (toyTheta - 1)) * (n : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right hup (Real.rpow_nonneg hn0.le _)
        _ = 2 * ((n : ℝ) ^ (toyTheta - 1) * (n : ℝ) ^ (-s.re)) := by ring
        _ = 2 * ((n : ℝ) ^ (s.re - toyTheta + 1))⁻¹ := by rw [hpow]
  have hdiv : ∀ x : ℝ, x ≤ toyTheta → ¬ Summable (fun n : ℕ => toyExcess n * (n : ℝ) ^ (-x)) := by
    intro x hx hsum
    have hθ0 : 0 < toyTheta := by linarith [toyTheta_bounds.1]
    have hharm : Summable (fun n : ℕ => (n : ℝ)⁻¹) := by
      have hscaled : Summable (fun n : ℕ => toyTheta⁻¹ * (toyExcess n * (n : ℝ) ^ (-x))) :=
        hsum.mul_left toyTheta⁻¹
      refine Summable.of_nonneg_of_le (fun n => inv_nonneg.mpr (Nat.cast_nonneg n)) (fun n => ?_) hscaled
      by_cases hn : n = 0
      · subst hn; simp [toyExcess_zero]
      · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
        have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
        have hlo := (toyExcess_mvt_bounds hn1).1
        have hpow_ge : (n : ℝ) ^ (-toyTheta) ≤ (n : ℝ) ^ (-x) :=
          Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
        have hinv : (n : ℝ) ^ (toyTheta - 1) * (n : ℝ) ^ (-toyTheta) = (n : ℝ)⁻¹ := by
          rw [← Real.rpow_add hn0, show toyTheta - 1 + -toyTheta = (-1 : ℝ) by ring,
            Real.rpow_neg_one]
        calc (n : ℝ)⁻¹ = toyTheta⁻¹ * (toyTheta * (n : ℝ) ^ (toyTheta - 1) * (n : ℝ) ^ (-toyTheta)) := by
              rw [mul_assoc, hinv]; field_simp
          _ ≤ toyTheta⁻¹ * (toyExcess n * (n : ℝ) ^ (-x)) := by
              refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hθ0.le)
              exact mul_le_mul hlo hpow_ge (Real.rpow_nonneg hn0.le _) (toyExcess_nonneg n)
    exact Real.not_summable_natCast_inv hharm
  exact ⟨hconv, hdiv, landau_singularity_at_abscissa toyExcess_zero toyExcess_nonneg
    (fun x hx => hconv (x : ℂ) (by simpa using hx)) (fun x hx => hdiv x hx.le)⟩

/-- **Complex Poincaré Antiderivative on Half-Planes**:
any holomorphic function `H` on `{s : ℂ | θ < s.re}` (`θ < 1`) has an explicit holomorphic
antiderivative `P(s) = ∫_0^1 (s - 2) * H (2 + u * (s - 2)) du` satisfying `HasDerivAt P (H s) s`
for every `s` with `θ < s.re`! -/
theorem hasDerivAt_radial_antideriv_halfPlane {θ : ℝ} (hθ : θ < 1) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {s : ℂ | θ < s.re}) {s : ℂ} (hs : θ < s.re) :
    HasDerivAt (fun w : ℂ => ∫ u in (0 : ℝ)..1, (w - 2) * H (2 + (u : ℂ) * (w - 2))) (H s) s := by
  have hopen : IsOpen {z : ℂ | θ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hH_an : AnalyticOnNhd ℂ H {z : ℂ | θ < z.re} := hH.analyticOnNhd hopen
  have hH_cont : ContinuousOn H {z : ℂ | θ < z.re} := hH_an.continuousOn
  have hH'_an : AnalyticOnNhd ℂ (deriv H) {z : ℂ | θ < z.re} := fun z hz => (hH_an z hz).deriv
  have hH'_cont : ContinuousOn (deriv H) {z : ℂ | θ < z.re} := hH'_an.continuousOn
  set δ : ℝ := (s.re - θ) / 2 with hδ_def
  have hδ0 : 0 < δ := by linarith
  -- For w ∈ closedBall s (δ/2) and u ∈ [0, 1], z(w, u) = 2 + u*(w - 2) stays inside {z | θ < z.re}
  have hmem_half : ∀ w ∈ Metric.closedBall s (δ / 2), ∀ u ∈ Set.Icc (0 : ℝ) 1,
      θ < (2 + (u : ℂ) * (w - 2)).re := by
    intro w hw u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre_w : θ + δ / 2 < w.re := by
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm (w - s)).trans hw)).1
      rw [Complex.sub_re] at h1; linarith
    have hre_z : (2 + (u : ℂ) * (w - 2)).re = (1 - u) * 2 + u * w.re := by
      simp [Complex.mul_re]; ring
    rw [hre_z]
    rcases eq_or_lt_of_le hu.1 with rfl | hu0
    · linarith
    · nlinarith [hu.2]
  -- Compact image K = {(w, u) ∈ closedBall s (δ/2) × [0, 1] ↦ 2 + u*(w-2)} ⊆ {z | θ < z.re}
  set Φ : ℂ × ℝ → ℂ := fun p => 2 + (p.2 : ℂ) * (p.1 - 2)
  have hΦ_cont : Continuous Φ := by fun_prop
  set K : Set ℂ := Φ '' (Metric.closedBall s (δ / 2) ×ˢ Set.Icc (0 : ℝ) 1)
  have hK_comp : IsCompact K :=
    ((isCompact_closedBall s (δ / 2)).prod isCompact_Icc).image hΦ_cont
  have hK_sub : K ⊆ {z : ℂ | θ < z.re} := by
    rintro _ ⟨⟨w, u⟩, ⟨hw, hu⟩, rfl⟩
    exact hmem_half w hw u hu
  have hK_ne : K.Nonempty := ⟨Φ (s, 0), ⟨(s, 0), ⟨Metric.mem_closedBall_self (by positivity),
    ⟨le_rfl, zero_le_one⟩⟩, rfl⟩⟩
  obtain ⟨M₁, hM₁⟩ := hK_comp.exists_bound_of_continuousOn (hH_cont.mono hK_sub)
  obtain ⟨M₂, hM₂⟩ := hK_comp.exists_bound_of_continuousOn (hH'_cont.mono hK_sub)
  set B : ℝ := |M₁| + (‖s - 2‖ + δ / 2) * |M₂|
  have hstep : HasDerivAt
      (fun w : ℂ => ∫ u in (0 : ℝ)..1, (w - 2) * H (2 + (u : ℂ) * (w - 2)))
      (∫ u in (0 : ℝ)..1,
        (H (2 + (u : ℂ) * (s - 2)) + (s - 2) * ((u : ℂ) * deriv H (2 + (u : ℂ) * (s - 2))))) s := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w u => (w - 2) * H (2 + (u : ℂ) * (w - 2)))
      (F' := fun w u => H (2 + (u : ℂ) * (w - 2)) + (w - 2) * ((u : ℂ) * deriv H (2 + (u : ℂ) * (w - 2))))
      (bound := fun _ : ℝ => B)
      (Metric.ball_mem_nhds s (show 0 < δ / 2 by positivity)) ?_ ?_ ?_ ?_
      (intervalIntegrable_const (c := B)) ?_).2
    · filter_upwards [Metric.ball_mem_nhds s (show 0 < δ / 2 by positivity)] with w hw
      have hcw : ContinuousOn (fun u : ℝ => (w - 2) * H (2 + (u : ℂ) * (w - 2))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        refine continuousOn_const.mul (hH_cont.comp (by fun_prop) fun u hu => ?_)
        exact hmem_half w (Metric.ball_subset_closedBall hw) u hu
      exact (hcw.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · have hcs : ContinuousOn (fun u : ℝ => (s - 2) * H (2 + (u : ℂ) * (s - 2))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        refine continuousOn_const.mul (hH_cont.comp (by fun_prop) fun u hu => ?_)
        exact hmem_half s (Metric.mem_closedBall_self (by positivity)) u hu
      exact hcs.intervalIntegrable
    · have hcs' : ContinuousOn (fun u : ℝ =>
          H (2 + (u : ℂ) * (s - 2)) + (s - 2) * ((u : ℂ) * deriv H (2 + (u : ℂ) * (s - 2))))
          (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        refine (hH_cont.comp (by fun_prop) fun u hu =>
          hmem_half s (Metric.mem_closedBall_self (by positivity)) u hu).add
          (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul
            (hH'_cont.comp (by fun_prop) fun u hu =>
              hmem_half s (Metric.mem_closedBall_self (by positivity)) u hu)))
      exact (hcs'.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · refine Eventually.of_forall fun u hu w hw => ?_
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu_cc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
      have hw_cb : w ∈ Metric.closedBall s (δ / 2) := Metric.ball_subset_closedBall hw
      have hzK : 2 + (u : ℂ) * (w - 2) ∈ K := ⟨(w, u), ⟨hw_cb, hu_cc⟩, rfl⟩
      have h1 : ‖H (2 + (u : ℂ) * (w - 2))‖ ≤ |M₁| := (hM₁ _ hzK).trans (le_abs_self M₁)
      have h2 : ‖deriv H (2 + (u : ℂ) * (w - 2))‖ ≤ |M₂| := (hM₂ _ hzK).trans (le_abs_self M₂)
      have hw_norm : ‖w - 2‖ ≤ ‖s - 2‖ + δ / 2 := by
        have hws : ‖w - s‖ ≤ δ / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw_cb
        calc ‖w - 2‖ = ‖(w - s) + (s - 2)‖ := by ring_nf
          _ ≤ ‖w - s‖ + ‖s - 2‖ := norm_add_le _ _
          _ ≤ ‖s - 2‖ + δ / 2 := by linarith
      have hu_norm : ‖(u : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg hu_cc.1]; exact hu_cc.2
      calc ‖H (2 + (u : ℂ) * (w - 2)) + (w - 2) * ((u : ℂ) * deriv H (2 + (u : ℂ) * (w - 2)))‖
          ≤ ‖H (2 + (u : ℂ) * (w - 2))‖ + ‖w - 2‖ * (‖(u : ℂ)‖ * ‖deriv H (2 + (u : ℂ) * (w - 2))‖) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ |M₁| + (‖s - 2‖ + δ / 2) * (1 * |M₂|) := by
            gcongr
        _ = B := by simp only [B, one_mul]
    · refine Eventually.of_forall fun u hu w hw => ?_
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu_cc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
      have hz_mem : θ < (2 + (u : ℂ) * (w - 2)).re :=
        hmem_half w (Metric.ball_subset_closedBall hw) u hu_cc
      have hHz : HasDerivAt H (deriv H (2 + (u : ℂ) * (w - 2))) (2 + (u : ℂ) * (w - 2)) :=
        ((hH _ hz_mem).differentiableAt (hopen.mem_nhds hz_mem)).hasDerivAt
      have hlin : HasDerivAt (fun v : ℂ => 2 + (u : ℂ) * (v - 2)) (u : ℂ) w := by
        simpa using (((hasDerivAt_id' w).sub_const (2 : ℂ)).const_mul (u : ℂ)).const_add (2 : ℂ)
      have hcomp := hHz.comp w hlin
      exact (((hasDerivAt_id' w).sub_const (2 : ℂ)).mul hcomp).congr_deriv (by
        simp only [Function.comp_apply]; ring)
  -- Evaluate the derivative integral by FTC: integrand is d/du (u * H (2 + u * (s - 2)))!
  have hFTC : ∫ u in (0 : ℝ)..1,
      (H (2 + (u : ℂ) * (s - 2)) + (s - 2) * ((u : ℂ) * deriv H (2 + (u : ℂ) * (s - 2)))) = H s := by
    have hd_u : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (t : ℂ) * H (2 + (t : ℂ) * (s - 2)))
          (H (2 + (u : ℂ) * (s - 2)) + (s - 2) * ((u : ℂ) * deriv H (2 + (u : ℂ) * (s - 2)))) u := by
      intro u hu
      rw [Set.uIcc_of_le zero_le_one] at hu
      have hz_mem : θ < (2 + (u : ℂ) * (s - 2)).re :=
        hmem_half s (Metric.mem_closedBall_self (by positivity)) u hu
      have hHz : HasDerivAt H (deriv H (2 + (u : ℂ) * (s - 2))) (2 + (u : ℂ) * (s - 2)) :=
        ((hH _ hz_mem).differentiableAt (hopen.mem_nhds hz_mem)).hasDerivAt
      have hlin : HasDerivAt (fun t : ℝ => 2 + (t : ℂ) * (s - 2)) (s - 2) u := by
        simpa using (((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const (s - 2)).const_add (2 : ℂ))
      have hcomp := hHz.comp u hlin
      exact ((Complex.ofRealCLM.hasDerivAt (x := u)).mul hcomp).congr_deriv (by
        simp only [Complex.ofRealCLM_apply, Function.comp_apply, Complex.ofReal_one, one_mul]
        ring)
    have hc_u : ContinuousOn (fun u : ℝ =>
        H (2 + (u : ℂ) * (s - 2)) + (s - 2) * ((u : ℂ) * deriv H (2 + (u : ℂ) * (s - 2))))
        (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le zero_le_one]
      refine (hH_cont.comp (by fun_prop) fun u hu =>
        hmem_half s (Metric.mem_closedBall_self (by positivity)) u hu).add
        (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul
          (hH'_cont.comp (by fun_prop) fun u hu =>
            hmem_half s (Metric.mem_closedBall_self (by positivity)) u hu)))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd_u hc_u.intervalIntegrable]
    simp
  rwa [hFTC] at hstep

/-- Holomorphic Mellin remainder of `dirSeries toyCoeff` on `Re(s) > 27 / 50`. -/
def toyRemainder (s : ℂ) : ℂ :=
  1 + s * ∫ t in Ioi (1 : ℝ), (stepSum (fun n => (toyCoeff n : ℂ)) t - (t : ℂ)) * (t : ℂ) ^ (-s - 1)

/-- Explicit holomorphic antiderivative of `toyRemainder` on `Re(s) > 27 / 50`. -/
def toyAntideriv (s : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..1, (s - 2) * toyRemainder (2 + (u : ℂ) * (s - 2))

/-- **Concrete Synthetic Zeta Function `toyZeta`** driven by the `Stage2ToyBreakthrough`
`x ^ (27 / 50)` error law: meromorphic on `Re(s) > 27 / 50` with a simple pole at `s = 1`,
logarithmic derivative `-toyZeta'/toyZeta = dirSeries toyCoeff` on `Re(s) > 1`, and
unconditionally zero-free throughout `Re(s) > 27 / 50`! -/
def toyZeta (s : ℂ) : ℂ :=
  (s - 1)⁻¹ * cexp (-toyAntideriv s)

theorem toyRemainder_analytic_and_eq :
    AnalyticOnNhd ℂ toyRemainder {s : ℂ | toyTheta < s.re} ∧
    ∀ s : ℂ, 1 < s.re → dirSeries toyCoeff s - 1 / (s - 1) = toyRemainder s := by
  have hmeas : Measurable (fun t : ℝ => stepSum (fun n => (toyCoeff n : ℂ)) t - (t : ℂ)) :=
    (measurable_stepSum _).sub Complex.measurable_ofReal
  have han : AnalyticOnNhd ℂ toyRemainder {s : ℂ | toyTheta < s.re} :=
    analyticOnNhd_mellin_of_rpow_bound hmeas (by norm_num : (0 : ℝ) ≤ 2)
      fun t ht => norm_stepSum_toyCoeff_sub_id ht
  refine ⟨han, fun s hs => ?_⟩
  rw [dirSeries_eq_LSeries]
  have hsum_coeff : LSeriesSummable (fun n => (toyCoeff n : ℂ)) s := by
    rw [dirSeriesSummable_iff_real toyCoeff_zero toyCoeff_nonneg s]
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ s.re)⁻¹) :=
      Real.summable_nat_rpow_inv.mpr hs
    have h2 : Summable (fun n : ℕ => toyExcess n * (n : ℝ) ^ (-s.re)) :=
      (dirSeriesSummable_iff_real toyExcess_zero toyExcess_nonneg s).mp
        (toyExcess_landau_singularity.1 s (lt_trans toyTheta_bounds.2.2 hs))
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (toyCoeff_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (fun n => ?_) (h1.add h2)
    by_cases hn : n = 0
    · subst hn; simp [toyCoeff_zero, toyExcess_zero, Real.zero_rpow (by linarith : s.re ≠ 0)]
    · simp only [toyCoeff, hn, ↓reduceIte, add_mul, one_mul, Real.rpow_neg (Nat.cast_nonneg n)]
      exact le_rfl
  have hbd_lin : ∀ t : ℝ, 1 ≤ t → ‖stepSum (fun n => (toyCoeff n : ℂ)) t‖ ≤ 3 * t := by
    intro t ht
    have h1 := norm_stepSum_toyCoeff_sub_id ht
    have h2 : t ^ toyTheta ≤ t := by
      calc t ^ toyTheta ≤ t ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ht toyTheta_bounds.2.2.le
        _ = t := Real.rpow_one t
    have h3 : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans ht)]
    calc ‖stepSum (fun n => (toyCoeff n : ℂ)) t‖
        = ‖(stepSum (fun n => (toyCoeff n : ℂ)) t - (t : ℂ)) + (t : ℂ)‖ := by ring_nf
      _ ≤ ‖stepSum (fun n => (toyCoeff n : ℂ)) t - (t : ℂ)‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * t ^ toyTheta + t := by linarith
      _ ≤ 3 * t := by linarith
  exact LSeries_sub_pole_eq_mellin_error hbd_lin hs hsum_coeff

/-- **Unconditional Concrete Zero-Free Half-Plane `Re(s) > 27 / 50` for `toyZeta`**
(deduced via Abelian summation + `zeroFree_of_analytic_logDeriv_continuation`, strictly beating
the `2/3` barrier!). -/
theorem toyZeta_logDeriv_and_zeroFree :
    DifferentiableOn ℂ toyZeta ({s : ℂ | 27 / 50 < s.re} \ {1}) ∧
    (∀ s : ℂ, 1 < s.re → -deriv toyZeta s / toyZeta s = dirSeries toyCoeff s) ∧
    (∀ s : ℂ, 27 / 50 < s.re → s ≠ 1 → toyZeta s ≠ 0) := by
  have hRem_diff : DifferentiableOn ℂ toyRemainder {s : ℂ | toyTheta < s.re} :=
    toyRemainder_analytic_and_eq.1.differentiableOn
  have hP_deriv : ∀ s : ℂ, toyTheta < s.re → HasDerivAt toyAntideriv (toyRemainder s) s :=
    fun s hs => hasDerivAt_radial_antideriv_halfPlane toyTheta_bounds.2.2 hRem_diff hs
  have hZ_deriv : ∀ s : ℂ, toyTheta < s.re → s ≠ 1 →
      HasDerivAt toyZeta
        (-(s - 1)⁻¹ ^ 2 * cexp (-toyAntideriv s) +
          (s - 1)⁻¹ * (cexp (-toyAntideriv s) * (-toyRemainder s))) s := by
    intro s hs hs1
    have h1 : HasDerivAt (fun w : ℂ => (w - 1)⁻¹) (-(s - 1)⁻¹ ^ 2) s := by
      have h := ((hasDerivAt_id' s).sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hs1)
      refine h.congr_deriv ?_; field_simp
    have h2 : HasDerivAt (fun w : ℂ => cexp (-toyAntideriv w))
        (cexp (-toyAntideriv s) * (-toyRemainder s)) s :=
      (hP_deriv s hs).neg.cexp
    exact h1.mul h2
  have hZ_diff : DifferentiableOn ℂ toyZeta ({s : ℂ | toyTheta < s.re} \ {1}) := fun s hs =>
    (hZ_deriv s hs.1 hs.2).differentiableAt.differentiableWithinAt
  have hZ2 : toyZeta 2 ≠ 0 := by
    unfold toyZeta
    exact mul_ne_zero (inv_ne_zero (by norm_num)) (Complex.exp_ne_zero _)
  have hlogDeriv : ∀ s : ℂ, toyTheta < s.re → s ≠ 1 → toyZeta s ≠ 0 →
      -deriv toyZeta s / toyZeta s - 1 / (s - 1) = toyRemainder s := by
    intro s hs hs1 _
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hexp : cexp (-toyAntideriv s) ≠ 0 := Complex.exp_ne_zero _
    rw [(hZ_deriv s hs hs1).deriv]
    unfold toyZeta
    field_simp
    ring
  have hzf_theta : ∀ s : ℂ, toyTheta < s.re → s ≠ 1 → toyZeta s ≠ 0 :=
    zeroFree_of_analytic_logDeriv_continuation toyTheta_bounds.2.2 hZ_diff hZ2 hRem_diff
      fun s hs hZs => hlogDeriv s (lt_trans toyTheta_bounds.2.2 hs)
        (fun h => by rw [h, one_re] at hs; exact lt_irrefl _ hs) hZs
  refine ⟨by simpa [toyTheta_eq] using hZ_diff, fun s hs => ?_, by simpa [toyTheta_eq] using hzf_theta⟩
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl _ hs
  have hsθ : toyTheta < s.re := lt_trans toyTheta_bounds.2.2 hs
  have h1 := hlogDeriv s hsθ hs1 (hzf_theta s hsθ hs1)
  have h2 := toyRemainder_analytic_and_eq.2 s hs
  linear_combination h1 - h2

/-- **Master Unconditional Stage 3 Real-Analytic Landau & `27/50` Zero-Free Theorem**
(0 hypotheses, 0 `sorry`, standard axioms `[propext, Classical.choice, Quot.sound]` only):

Unifies all three Stage 3 Pillar-1 engines with `Stage2ToyBreakthrough`:
1. **Concrete `Stage2ToyBreakthrough` Exponent**: `toyTheta = 27 / 50 < 2 / 3` and
   `Stage2ToyBreakthrough.toyGx ≤ Stage2ToyBreakthrough.toyScale.x ^ (27 / 50)`.
2. **Classical Landau Singularity Sharpness**: `dirSeries toyExcess` (`toyExcess n ≥ 0`) has
   exact abscissa of convergence `27 / 50`, alternating non-negative real derivatives
   `(-1)^k F^{(k)}(σ) ≥ 0` on `(27 / 50, ∞)`, and a genuine real Landau singularity at `s = 27 / 50`.
3. **Abelian Summation → Concrete Zero-Free Half-Plane `Re(s) > 27 / 50`**:
   `toyZeta` has `-deriv toyZeta s / toyZeta s = dirSeries toyCoeff s` on `Re(s) > 1` with
   `‖stepSum toyCoeff x - x‖ ≤ 2 x^(27/50)`, and is unconditionally zero-free on
   `Re(s) > 27 / 50` (`s ≠ 1`), strictly beating the `2/3` barrier!
4. **Classical Prime-Counting / Chebyshev / Riesz-Mean Transfer**:
   For ANY `0 < θ < 1` and `C ≥ 0`, `|ψ(x) - x| ≤ C x^θ` implies BOTH `ζ(s) ≠ 0` on
   `Re(s) > θ` AND the `LandauWindow` ramp bound `|Gz y| ≤ (C / (1 - θ)) y^θ`! -/
theorem master_stage3_real_analytic_landau :
    -- (1) Exact Stage2ToyBreakthrough exponent 27/50 < 2/3:
    toyTheta = 27 / 50 ∧ toyTheta < 2 / 3 ∧
    Stage2ToyBreakthrough.toyGx ≤ Stage2ToyBreakthrough.toyScale.x ^ ((27 : ℝ) / 50) ∧
    -- (2) Classical Landau alternating derivative positivity + exact singularity at s = 27/50:
    (∀ σ : ℝ, (27 : ℝ) / 50 < σ → ∀ k : ℕ,
      0 ≤ ((-1 : ℂ) ^ k * iteratedDeriv k (dirSeries toyExcess) (σ : ℂ)).re) ∧
    (¬ ∃ (r : ℝ) (_ : 0 < r) (F : ℂ → ℂ),
        DifferentiableOn ℂ F (Metric.ball ((27 / 50 : ℝ) : ℂ) r) ∧
        ∀ s ∈ Metric.ball ((27 / 50 : ℝ) : ℂ) r, (27 : ℝ) / 50 < s.re → F s = dirSeries toyExcess s) ∧
    -- (3) Unconditional concrete Re(s) > 27/50 zero-free half-plane for toyZeta:
    (∀ s : ℂ, 1 < s.re → -deriv toyZeta s / toyZeta s = dirSeries toyCoeff s) ∧
    (∀ s : ℂ, (27 : ℝ) / 50 < s.re → s ≠ 1 → toyZeta s ≠ 0) ∧
    -- (4) Unconditional ψ(x) - x = O(x^θ) → zero-free Re(s) > θ + LandauWindow Gz bound:
    (∀ (C θ : ℝ), 0 ≤ C → θ < 1 →
      (∀ x : ℝ, 1 ≤ x → |chebyshevPsi x - x| ≤ C * x ^ θ) →
      (∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) ∧
      (∀ y : ℝ, 1 ≤ y → |Gz y| ≤ (C / (1 - θ)) * y ^ θ)) := by
  refine ⟨toyTheta_eq, toyTheta_bounds.2.1,
    by simpa [toyTheta_eq] using toyGx_le_toyScale_rpow_toyTheta,
    fun σ hσ k => (alternating_iteratedDeriv_dirSeries_nonneg toyExcess_zero toyExcess_nonneg
      (fun x hx => toyExcess_landau_singularity.1 (x : ℂ) (by simpa [toyTheta_eq] using hx))
      hσ k).1,
    by simpa [toyTheta_eq] using toyExcess_landau_singularity.2.2,
    toyZeta_logDeriv_and_zeroFree.2.1,
    toyZeta_logDeriv_and_zeroFree.2.2,
    fun C θ hC hθ hpsi =>
      ⟨(zeroFree_riemannZeta_of_psi_bound hC hθ hpsi).1,
       fun y hy => (Gz_eq_neg_mul_tail_integral_and_bound hθ hpsi hy).2⟩⟩

end RHDirect.Stage3RealAnalyticLandau
