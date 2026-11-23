import RHDirect.Stage2DirichletAP
import RHDirect.Stage3BombieriVinogradov
import RHDirect.Stage4ClassFieldTheory
import RHDirect.Stage5DirichletLZeroFree
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# RHDirect.Stage6ClassNumberFormula

Unconditional (0 `sorry`, 0 custom `axiom`, 0 warnings, 0 info) formalization of
**Dirichlet's Analytic Class Number Formula Core** in pure Mathlib `v4.33.1`:

1. **Conditional Convergence of `L(1, χ)` & Abel Limit Theorem for Fourier Logarithm Series**:
   - Exact rate `‖LFunction χ 1 - ∑_{n=1}^N χ(n) / n‖ ≤ 2 q / N` from
     `Stage5DirichletLZeroFree.LFunction_eq_partialSum_add_tail`, giving
     `∑_{n=1}^N χ(n) / n → LFunction χ 1` for every non-principal `χ ≠ 1`.
   - Elementary Abel/Dirichlet radial-approximation proof of the convergent Fourier logarithm
     series `∑_{n=1}^N e(n θ) / n → -Complex.log (1 - e θ)` whenever `0 < distZ θ`.
2. **Exact Finite-Sum Evaluation of `DirichletCharacter.LFunction χ 1` via Gauss Sums**:
   - Gauss-sum conjugation & inversion `τ(χ) * τ(χ⁻¹) = χ(-1) * q`,
     `(τ(χ⁻¹))⁻¹ = χ(-1) * τ(χ) / q` built on `Stage3BombieriVinogradov.norm_sq_gaussSum_eq`.
   - Exact branch evaluation `Complex.log (1 - e x) = Real.log (2 sin(π x)) + i π (x - 1/2)`
     for `x ∈ (0, 1)`.
   - Exact finite Dirichlet `L(1, χ)` formulas for every primitive `χ ≠ 1` mod `q`:
     - General: `LFunction χ 1 = -(τ(χ⁻¹))⁻¹ * ∑_{a=1}^{q-1} χ⁻¹(a) * Complex.log (1 - e(a / q))`
       and `= -(χ(-1) * τ(χ) / q) * ∑_{a=1}^{q-1} χ⁻¹(a) * Complex.log (1 - e(a / q))`.
     - Even primitive `χ`: `LFunction χ 1 = -(τ(χ) / q) * ∑_{a=1}^{q-1} χ⁻¹(a) * log(2 sin(π a / q))`.
     - Odd primitive `χ`: `LFunction χ 1 = (i π τ(χ) / q²) * ∑_{a=1}^{q-1} a * χ⁻¹(a)` and
       `‖LFunction χ 1‖ = (π / (q √q)) * ‖∑_{a=1}^{q-1} a * χ⁻¹(a)‖`.
3. **Unconditional Strict Positivity `L(1, χ) > 0` for Every Real Non-Principal `χ ≠ 1`**:
   - Real-valuedness `(LFunction χ σ).im = 0` for all real `σ > 0` (via Abelian Mellin integral).
   - Strict positivity `0 < (LFunction χ σ).re` for all `σ > 1` (via the convergent Euler product
     and `LFunction_ne_zero_of_one_le_re_bridge`).
   - Unconditional `0 < (LFunction χ 1).re ∧ (LFunction χ 1).im = 0` via continuity at `s = 1`
     and `Stage2DirichletAP.LFunction_apply_one_ne_zero_bridge`.
4. **Gauss's Exact Quadratic Gauss Sum & Unconditional Dirichlet Non-Vanishing Sign Theorem**:
   - Exact quadratic Gauss sum `∑_{r=0}^{q-1} e(r² / q) = ((1 + I) * (1 + (-I)^q) / 2) * √q` for
     every `q ≥ 1` via `Complex.tsum_exp_neg_quadratic` / `Complex.tsum_exp_neg_mul_int_sq`.
   - Full CRT + prime-power + quadratic-reciprocity evaluation of the quadratic Gauss sum
     `gaussSum χ ZMod.stdAddChar = (if χ.Even then 1 else I) * √q` for EVERY real primitive
     character `χ : DirichletCharacter ℂ q` (arbitrary prime OR composite modulus `q`!).
   - Unconditional exact finite formula
     `(LFunction χ 1).re = -(π / (q * √q)) * ∑_{a=1}^{q-1} a * (χ a).re` and **Dirichlet's
     Non-Vanishing Sign Theorem** `∑_{a=1}^{q-1} a * (χ a).re < 0` for EVERY odd real primitive
     character `χ mod q`, plus **Dirichlet's Quadratic Residue Excess Theorem**
     `0 < ∑_{a=1}^{(p-1)/2} (χ a).re` for every prime `p ≡ 3 [MOD 4]` and the even log-sine
     sign theorem `∑_{a=1}^{q-1} (χ a).re * log(2 sin(π a / q)) < 0`.
5. **Exact Cyclotomic Dedekind Zeta Residue Formulas at `s = 1`**:
   - Exact residue of `∏_{χ mod m} LFunction χ s` (`(∏_{p ∣ m} (1 - p⁻¹)) * ∏_{χ ≠ 1} L(1, χ) ≠ 0`),
     of `riemannZeta s * ∏_{χ ≠ 1} LFunction χ s` (`∏_{χ ≠ 1} L(1, χ) ≠ 0`), and of the full
     primitive cyclotomic Dedekind zeta product `∏_{χ mod m} LFunction χ.primitiveCharacter s`
     (`∏_{χ ≠ 1} L(1, χ*) ≠ 0`).
-/

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology
open RHDirect.Stage3BombieriVinogradov RHDirect.Stage4ClassFieldTheory RHDirect.Stage5DirichletLZeroFree
open scoped BigOperators

namespace RHDirect.Stage6ClassNumberFormula

/-! ## Section 1: Conditional Convergence of `L(1, χ)` & Fourier Logarithm Series -/

/-- Explicit error rate for partial sums of `L(1, χ)` for any non-principal `χ ≠ 1` mod `q`:
for every `N ≥ 1`, `‖LFunction χ 1 - ∑_{n=1}^N χ(n) / n‖ ≤ 2 q / N`. -/
theorem norm_LFunction_one_sub_partialSum_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖LFunction χ 1 - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ)‖ ≤
      2 * (q : ℝ) / (N : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hs : (0 : ℝ) < (1 : ℂ).re := by simp
  have hsplit := LFunction_eq_partialSum_add_tail hχ hN hs
  have hsum_eq :
      ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) =
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.cpow_neg_one, div_eq_mul_inv]
  rw [hsplit, hsum_eq]
  have hdiff :
      ((∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ)) -
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-(1 : ℂ)) +
        (1 : ℂ) * ∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (t : ℂ) ^ (-(1 : ℂ) - 1)) -
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ) =
      -(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-(1 : ℂ))) +
        ∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (t : ℂ) ^ (-(1 : ℂ) - 1) := by
    ring
  rw [hdiff]
  have hT1 :
      ‖-(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
          (N : ℂ) ^ (-(1 : ℂ)))‖ ≤ (q : ℝ) / (N : ℝ) := by
    rw [norm_neg, norm_mul, Complex.cpow_neg_one, norm_inv, Complex.norm_natCast,
      ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ (N : ℝ)) hN_pos.le
  have hT2 :
      ‖∫ t in Ioi (N : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
          (t : ℂ) ^ (-(1 : ℂ) - 1)‖ ≤ (q : ℝ) / (N : ℝ) := by
    have hdom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-2 : ℝ)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hN_pos).const_mul (q : ℝ)
    have h1 :
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (t : ℂ) ^ (-(1 : ℂ) - 1)‖ ≤
        ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-2 : ℝ) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := hN_pos.trans ht
      dsimp only
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-(1 : ℂ) - 1).re = (-2 : ℝ) := by norm_num
      rw [hre]
      exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ t)
        (Real.rpow_nonneg ht0.le _)
    have heval : ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-2 : ℝ) = (q : ℝ) / (N : ℝ) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hN_pos]
      have hexp : (-2 : ℝ) + 1 = -1 := by norm_num
      rw [hexp, Real.rpow_neg_one]
      field_simp [hN_pos.ne']
    exact h1.trans_eq heval
  calc ‖-(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
            (N : ℂ) ^ (-(1 : ℂ))) +
          ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (t : ℂ) ^ (-(1 : ℂ) - 1)‖
      ≤ ‖-(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
            (N : ℂ) ^ (-(1 : ℂ)))‖ +
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (t : ℂ) ^ (-(1 : ℂ) - 1)‖ := norm_add_le _ _
    _ ≤ (q : ℝ) / (N : ℝ) + (q : ℝ) / (N : ℝ) := add_le_add hT1 hT2
    _ = 2 * (q : ℝ) / (N : ℝ) := by ring

/-- **Conditional Convergence of the Dirichlet Series `L(1, χ)`** (`Icc 1 N` partial sums):
for every non-principal `χ ≠ 1`, `∑_{n=1}^N χ(n) / n → LFunction χ 1` as `N → ∞`. -/
theorem tendsto_partialSum_LFunction_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ))
      atTop (nhds (LFunction χ 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hzero : Tendsto (fun N : ℕ => 2 * (q : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 * (q : ℝ))
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
  exact norm_LFunction_one_sub_partialSum_le hχ hN

/-- Conditional convergence of `L(1, χ)` with `Finset.range` partial sums. -/
theorem tendsto_range_LFunction_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, χ (n : ZMod q) / (n : ℂ))
      atTop (nhds (LFunction χ 1)) := by
  have hshift :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), χ (n : ZMod q) / (n : ℂ))
        atTop (nhds (LFunction χ 1)) := by
    refine (tendsto_partialSum_LFunction_one hχ).congr fun N => ?_
    have h0 : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [h0, Finset.sum_insert (by simp)]
    simp
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-- Elementary Bernoulli-type bound: `1 - r ^ n ≤ n * (1 - r)` for `0 ≤ r ≤ 1`. -/
private lemma one_sub_pow_le_mul_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    1 - r ^ n ≤ (n : ℝ) * (1 - r) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hpow : r ^ k ≤ 1 := pow_le_one₀ hr0 hr1
    push_cast
    rw [pow_succ]
    nlinarith

/-- For any `θ : ℝ` with `0 < distZ θ`, `1 - e θ` lies in the open right half-plane
(and hence in `Complex.slitPlane`). -/
theorem one_sub_e_mem_slitPlane {θ : ℝ} (hθ : 0 < distZ θ) :
    1 - e θ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hne : e θ ≠ 1 := by
    intro h1
    have h4 := four_mul_distZ_le_norm_e_sub_one θ
    rw [h1, sub_self, norm_zero] at h4
    linarith
  have hnorm : ‖e θ‖ = 1 := norm_e θ
  have hsq : (e θ).re ^ 2 + (e θ).im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq (e θ)
    rw [hnorm, one_pow, Complex.normSq_apply] at h
    nlinarith
  have hlt : (e θ).re < 1 := by
    by_contra hge
    push Not at hge
    have hre1 : (e θ).re = 1 := by nlinarith
    have him0 : (e θ).im = 0 := by nlinarith
    apply hne
    exact Complex.ext (by simpa using hre1) (by simpa using him0)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- Uniform-in-`r` tail bound for `∑_{n > N} (r * e θ)^n / n` by summation by parts:
for `0 < r < 1`, `N ≥ 1`, and `0 < distZ θ`,
`‖(-Complex.log (1 - (r : ℂ) * e θ)) - ∑ n ∈ Finset.Icc 1 N, ((r : ℂ) * e θ) ^ n / n‖ ≤ (2 * distZ θ)⁻¹ * 2 / N`. -/
private lemma norm_taylor_neg_log_sub_partialSum_le {θ : ℝ} (hθ : 0 < distZ θ)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖-Complex.log (1 - (r : ℂ) * e θ) -
        ∑ n ∈ Finset.Icc 1 N, ((r : ℂ) * e θ) ^ n / (n : ℂ)‖ ≤
      2 * (2 * distZ θ)⁻¹ / (N : ℝ) := by
  set w : ℂ := e θ
  set C : ℝ := (2 * distZ θ)⁻¹
  have hC_pos : 0 < C := inv_pos.mpr (by positivity)
  have hrw_norm : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, norm_e, mul_one]
    exact hr1
  have hhasSum := Complex.hasSum_taylorSeries_neg_log hrw_norm
  -- Partial sums of `w^k` (`k = 1..n`) are bounded uniformly by `C`
  let P : ℕ → ℂ := fun n => ∑ k ∈ Finset.Icc 1 n, w ^ k
  have hP_bd : ∀ n : ℕ, ‖P n‖ ≤ C := by
    intro n
    have hIcc : ∑ k ∈ Finset.Icc 1 n, w ^ k =
        ∑ k ∈ Finset.Ico (1 : ℤ) ((1 : ℤ) + (n : ℤ)), e ((k : ℝ) * θ) := by
      refine Finset.sum_bij (fun k _ => (k : ℤ)) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_Ico]; omega
      · intro k₁ _ k₂ _ h; omega
      · intro k hk; simp only [Finset.mem_Ico] at hk
        exact ⟨k.toNat, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k _
        simp only [w]
        unfold e
        rw [← Complex.exp_nat_mul]
        congr 1; push_cast; ring
    show ‖∑ k ∈ Finset.Icc 1 n, w ^ k‖ ≤ C
    rw [hIcc]
    exact norm_geom_sum_e_Ico_le 1 n hθ
  have hP_diff : ∀ n : ℕ, 1 ≤ n → w ^ n = P n - P (n - 1) := by
    intro n hn
    dsimp only [P]
    have hsplit : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : n ∉ Finset.Icc 1 (n - 1) := by simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hnot]
    ring
  -- Finite summation-by-parts bound on `Icc (N + 1) M` for any `M ≥ N + 1`
  let c : ℕ → ℝ := fun n => r ^ n / (n : ℝ)
  have hc_nonneg : ∀ n : ℕ, 0 ≤ c n := fun n => by dsimp only [c]; positivity
  have hc_anti : ∀ n : ℕ, 1 ≤ n → c (n + 1) ≤ c n := by
    intro n hn
    dsimp only [c]
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hpow : r ^ (n + 1) ≤ r ^ n := by
      rw [pow_succ]; nlinarith [pow_nonneg hr0.le n]
    have hden : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    calc r ^ (n + 1) / ((n + 1 : ℕ) : ℝ)
        ≤ r ^ n / ((n + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ r ^ n / (n : ℝ) := div_le_div_of_nonneg_left (pow_nonneg hr0.le n) hn_pos hden
  have hfinite_tail : ∀ M : ℕ, N + 1 ≤ M →
      ‖∑ n ∈ Finset.Icc (N + 1) M, ((r : ℂ) * w) ^ n / (n : ℂ)‖ ≤
        2 * C * c (N + 1) := by
    intro M hNM
    -- Abel summation identity on `Icc (N + 1) M`
    have habel :
        ∑ n ∈ Finset.Icc (N + 1) M, (P n - P (n - 1)) * (c n : ℂ) =
          P M * (c M : ℂ) - P N * (c (N + 1) : ℂ) +
            ∑ n ∈ Finset.Ico (N + 1) M, P n * ((c n - c (n + 1) : ℝ) : ℂ) := by
      induction M, hNM using Nat.le_induction with
      | base =>
        have hIcc : Finset.Icc (N + 1) (N + 1) = {N + 1} := by simp
        have hIco : Finset.Ico (N + 1) (N + 1) = ∅ := by simp
        rw [hIcc, hIco, Finset.sum_singleton, Finset.sum_empty, add_zero]
        have hsub : N + 1 - 1 = N := by omega
        rw [hsub]; ring
      | succ k hk ih =>
        have hIcc : Finset.Icc (N + 1) (k + 1) = insert (k + 1) (Finset.Icc (N + 1) k) := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hIco : Finset.Ico (N + 1) (k + 1) = insert k (Finset.Ico (N + 1) k) := by
          ext n; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        have hnot1 : k + 1 ∉ Finset.Icc (N + 1) k := by simp only [Finset.mem_Icc]; omega
        have hnot2 : k ∉ Finset.Ico (N + 1) k := by simp only [Finset.mem_Ico]; omega
        rw [hIcc, Finset.sum_insert hnot1, ih, hIco, Finset.sum_insert hnot2]
        have hsub : k + 1 - 1 = k := by omega
        rw [hsub]
        push_cast
        ring
    have htele :
        ∑ n ∈ Finset.Ico (N + 1) M, (c n - c (n + 1)) = c (N + 1) - c M := by
      clear habel
      induction M, hNM using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        have hIco : Finset.Ico (N + 1) (k + 1) = insert k (Finset.Ico (N + 1) k) := by
          ext n; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        have hnot : k ∉ Finset.Ico (N + 1) k := by simp only [Finset.mem_Ico]; omega
        rw [hIco, Finset.sum_insert hnot, ih]
        ring
    have hterm : ∀ n ∈ Finset.Icc (N + 1) M,
        ((r : ℂ) * w) ^ n / (n : ℂ) = (P n - P (n - 1)) * (c n : ℂ) := by
      intro n hn
      have hn1 : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
      rw [mul_pow, ← hP_diff n hn1]
      dsimp only [c]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, habel]
    have hsum_bd :
        ‖∑ n ∈ Finset.Ico (N + 1) M, P n * ((c n - c (n + 1) : ℝ) : ℂ)‖ ≤
          C * (c (N + 1) - c M) := by
      calc ‖∑ n ∈ Finset.Ico (N + 1) M, P n * ((c n - c (n + 1) : ℝ) : ℂ)‖
          ≤ ∑ n ∈ Finset.Ico (N + 1) M, ‖P n * ((c n - c (n + 1) : ℝ) : ℂ)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Ico (N + 1) M, C * (c n - c (n + 1)) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn1 : 1 ≤ n := by have := (Finset.mem_Ico.mp hn).1; omega
            have hdiff_nn : 0 ≤ c n - c (n + 1) := sub_nonneg.mpr (hc_anti n hn1)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdiff_nn]
            exact mul_le_mul_of_nonneg_right (hP_bd n) hdiff_nn
        _ = C * ∑ n ∈ Finset.Ico (N + 1) M, (c n - c (n + 1)) := (Finset.mul_sum _ _ _).symm
        _ = C * (c (N + 1) - c M) := by rw [htele]
    have hPM : ‖P M * (c M : ℂ)‖ ≤ C * c M := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc_nonneg M)]
      exact mul_le_mul_of_nonneg_right (hP_bd M) (hc_nonneg M)
    have hPN : ‖P N * (c (N + 1) : ℂ)‖ ≤ C * c (N + 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc_nonneg (N + 1))]
      exact mul_le_mul_of_nonneg_right (hP_bd N) (hc_nonneg (N + 1))
    calc ‖P M * (c M : ℂ) - P N * (c (N + 1) : ℂ) +
            ∑ n ∈ Finset.Ico (N + 1) M, P n * ((c n - c (n + 1) : ℝ) : ℂ)‖
        ≤ ‖P M * (c M : ℂ) - P N * (c (N + 1) : ℂ)‖ +
          ‖∑ n ∈ Finset.Ico (N + 1) M, P n * ((c n - c (n + 1) : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖P M * (c M : ℂ)‖ + ‖P N * (c (N + 1) : ℂ)‖) +
          ‖∑ n ∈ Finset.Ico (N + 1) M, P n * ((c n - c (n + 1) : ℝ) : ℂ)‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ (C * c M + C * c (N + 1)) + C * (c (N + 1) - c M) := by linarith
      _ = 2 * C * c (N + 1) := by ring
  -- Pass `M → ∞` using `HasSum.tendsto_sum_nat`
  have htend_full :
      Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), ((r : ℂ) * w) ^ n / (n : ℂ))
        atTop (nhds (-Complex.log (1 - (r : ℂ) * w))) :=
    (hhasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have htend_diff :
      Tendsto (fun M : ℕ =>
          ∑ n ∈ Finset.Icc (N + 1) M, ((r : ℂ) * w) ^ n / (n : ℂ))
        atTop (nhds (-Complex.log (1 - (r : ℂ) * w) -
          ∑ n ∈ Finset.Icc 1 N, ((r : ℂ) * w) ^ n / (n : ℂ))) := by
    have hsub_tend := htend_full.sub_const (∑ n ∈ Finset.Icc 1 N, ((r : ℂ) * w) ^ n / (n : ℂ))
    refine hsub_tend.congr' ?_
    filter_upwards [eventually_ge_atTop (N + 1)] with M hM
    have hpart :
        Finset.range (M + 1) = insert 0 (Finset.Icc 1 N ∪ Finset.Icc (N + 1) M) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_union, Finset.mem_Icc]; omega
    have hnot0 : 0 ∉ Finset.Icc 1 N ∪ Finset.Icc (N + 1) M := by
      simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) M) := by
      rw [Finset.disjoint_left]
      intro n h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    rw [hpart, Finset.sum_insert hnot0, Finset.sum_union hdisj]
    simp
  have hnorm_le :
      ‖-Complex.log (1 - (r : ℂ) * w) -
          ∑ n ∈ Finset.Icc 1 N, ((r : ℂ) * w) ^ n / (n : ℂ)‖ ≤ 2 * C * c (N + 1) := by
    refine le_of_tendsto (htend_diff.norm) ?_
    filter_upwards [eventually_ge_atTop (N + 1)] with M hM
    exact hfinite_tail M hM
  refine hnorm_le.trans ?_
  have hcN1 : c (N + 1) ≤ (N : ℝ)⁻¹ := by
    dsimp only [c]
    have hpow : r ^ (N + 1) ≤ 1 := pow_le_one₀ hr0.le hr1.le
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
    calc r ^ (N + 1) / ((N + 1 : ℕ) : ℝ)
        ≤ 1 / ((N + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ 1 / (N : ℝ) := div_le_div_of_nonneg_left zero_le_one hN_pos hNle
      _ = (N : ℝ)⁻¹ := one_div _
  calc 2 * C * c (N + 1)
      ≤ 2 * C * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hcN1 (by positivity)
    _ = 2 * C / (N : ℝ) := by rw [div_eq_mul_inv]

/-- **Abel's Limit Theorem for the Convergent Fourier Logarithm Series**:
for every `θ : ℝ` with `0 < distZ θ` (equivalently `e θ ≠ 1`),
`∑_{n=1}^N e(n θ) / n → -Complex.log (1 - e θ)` as `N → ∞`. -/
theorem tendsto_fourier_log_series {θ : ℝ} (hθ : 0 < distZ θ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, e ((n : ℝ) * θ) / (n : ℂ))
      atTop (nhds (-Complex.log (1 - e θ))) := by
  set w : ℂ := e θ
  set C : ℝ := (2 * distZ θ)⁻¹
  have hC_pos : 0 < C := inv_pos.mpr (by positivity)
  -- Express `e(n * θ)` as `w ^ n`
  have hpow_eq : ∀ n : ℕ, e ((n : ℝ) * θ) = w ^ n := fun n => by
    dsimp only [w]
    unfold e
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [hpow_eq]
  -- Radial sequence `r N = 1 - 1 / N^2` (`N ≥ 2`)
  let r : ℕ → ℝ := fun N => 1 - ((N : ℝ) ^ 2)⁻¹
  have hr_tend : Tendsto r atTop (nhds 1) := by
    have hsq : Tendsto (fun N : ℕ => ((N : ℝ) ^ 2)⁻¹) atTop (nhds 0) := by
      have h1 : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [mul_zero, sq, mul_inv] using h1.mul h1
    simpa only [sub_zero] using tendsto_const_nhds.sub hsq
  have hlog_tend :
      Tendsto (fun N : ℕ => -Complex.log (1 - (r N : ℂ) * w))
        atTop (nhds (-Complex.log (1 - w))) := by
    have hcont : ContinuousAt (fun z : ℂ => -Complex.log z) (1 - w) :=
      (Complex.hasDerivAt_log (one_sub_e_mem_slitPlane hθ)).continuousAt.neg
    have harg : Tendsto (fun N : ℕ => 1 - (r N : ℂ) * w) atTop (nhds (1 - w)) := by
      simpa only [Complex.ofReal_one, one_mul, Function.comp_def] using
        tendsto_const_nhds.sub ((Complex.continuous_ofReal.continuousAt.tendsto.comp hr_tend).mul_const w)
    exact hcont.tendsto.comp harg
  -- Show `‖S N - (-log(1 - r N * w))‖ ≤ (1 + 2 C) / N → 0`
  have hdiff_tend :
      Tendsto (fun N : ℕ =>
          (∑ n ∈ Finset.Icc 1 N, w ^ n / (n : ℂ)) - (-Complex.log (1 - (r N : ℂ) * w)))
        atTop (nhds 0) := by
    have hdom : Tendsto (fun N : ℕ => (1 + 2 * C) / (N : ℝ)) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (1 + 2 * C)
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN1 : 1 ≤ N := by omega
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
    have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    have hsq_ge : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hinv_pos : 0 < ((N : ℝ) ^ 2)⁻¹ := inv_pos.mpr (by positivity)
    have hinv_lt1 : ((N : ℝ) ^ 2)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; linarith
    have hr0 : 0 < r N := by dsimp only [r]; linarith
    have hr1 : r N < 1 := by dsimp only [r]; linarith
    have hsplit :
        (∑ n ∈ Finset.Icc 1 N, w ^ n / (n : ℂ)) - (-Complex.log (1 - (r N : ℂ) * w)) =
          (∑ n ∈ Finset.Icc 1 N, (1 - ((r N : ℂ) ^ n)) * w ^ n / (n : ℂ)) -
            ((-Complex.log (1 - (r N : ℂ) * w)) -
              ∑ n ∈ Finset.Icc 1 N, ((r N : ℂ) * w) ^ n / (n : ℂ)) := by
      have hsub :
          (∑ n ∈ Finset.Icc 1 N, w ^ n / (n : ℂ)) -
            ∑ n ∈ Finset.Icc 1 N, ((r N : ℂ) * w) ^ n / (n : ℂ) =
          ∑ n ∈ Finset.Icc 1 N, (1 - (r N : ℂ) ^ n) * w ^ n / (n : ℂ) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [mul_pow]; ring
      linear_combination hsub
    rw [hsplit]
    have hhead :
        ‖∑ n ∈ Finset.Icc 1 N, (1 - (r N : ℂ) ^ n) * w ^ n / (n : ℂ)‖ ≤ 1 / (N : ℝ) := by
      calc ‖∑ n ∈ Finset.Icc 1 N, (1 - (r N : ℂ) ^ n) * w ^ n / (n : ℂ)‖
          ≤ ∑ n ∈ Finset.Icc 1 N, ‖(1 - (r N : ℂ) ^ n) * w ^ n / (n : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.Icc 1 N, ((N : ℝ) ^ 2)⁻¹ := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
            have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
            have h1sub : (1 - (r N : ℂ) ^ n) = (((1 - r N ^ n : ℝ)) : ℂ) := by push_cast; rfl
            rw [norm_div, norm_mul, h1sub, Complex.norm_real, Real.norm_eq_abs,
              norm_pow, norm_e, one_pow, mul_one, Complex.norm_natCast]
            have hnn : 0 ≤ 1 - r N ^ n := sub_nonneg.mpr (pow_le_one₀ hr0.le hr1.le)
            rw [abs_of_nonneg hnn]
            have hber := one_sub_pow_le_mul_one_sub hr0.le hr1.le n
            have h1r : 1 - r N = ((N : ℝ) ^ 2)⁻¹ := by dsimp only [r]; ring
            rw [h1r] at hber
            rw [div_le_iff₀ hn_pos]
            linarith
        _ = (N : ℝ) * ((N : ℝ) ^ 2)⁻¹ := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
        _ = 1 / (N : ℝ) := by field_simp [hN_pos.ne']
    have htail := norm_taylor_neg_log_sub_partialSum_le hθ hr0 hr1 hN1
    calc ‖(∑ n ∈ Finset.Icc 1 N, (1 - (r N : ℂ) ^ n) * w ^ n / (n : ℂ)) -
            ((-Complex.log (1 - (r N : ℂ) * w)) -
              ∑ n ∈ Finset.Icc 1 N, ((r N : ℂ) * w) ^ n / (n : ℂ))‖
        ≤ ‖∑ n ∈ Finset.Icc 1 N, (1 - (r N : ℂ) ^ n) * w ^ n / (n : ℂ)‖ +
          ‖(-Complex.log (1 - (r N : ℂ) * w)) -
            ∑ n ∈ Finset.Icc 1 N, ((r N : ℂ) * w) ^ n / (n : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 / (N : ℝ) + 2 * C / (N : ℝ) := add_le_add hhead htail
      _ = (1 + 2 * C) / (N : ℝ) := by ring
  simpa only [sub_add_cancel, zero_add] using hdiff_tend.add hlog_tend

/-! ## Section 2: Exact Finite-Sum Evaluation of `DirichletCharacter.LFunction χ 1` via Gauss Sums -/

/-- Exact complex conjugation of the standard Gauss sum:
`conj(τ(χ)) = χ(-1) * τ(χ⁻¹)`. -/
theorem conj_gaussSum_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    starRingEnd ℂ (gaussSum χ ZMod.stdAddChar) =
      χ (-1 : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have h1 : starRingEnd ℂ (gaussSum χ ZMod.stdAddChar) =
      ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (-a) := by
    unfold gaussSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, conj_stdAddChar]
    congr 1
    simpa [RCLike.star_def] using MulChar.star_apply' χ a
  rw [h1]
  have hinv_neg : χ⁻¹ (-1 : ZMod q) = χ (-1 : ZMod q) := by
    rw [MulChar.inv_apply_eq_inv']
    have hsq : χ (-1 : ZMod q) * χ (-1 : ZMod q) = 1 := by
      rw [← map_mul, neg_mul_neg, one_mul, map_one]
    exact eq_inv_of_mul_eq_one_left hsq |>.symm
  rw [← hinv_neg, gaussSum, Finset.mul_sum]
  calc ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (-a)
      = ∑ b : ZMod q, χ⁻¹ (-b) * ZMod.stdAddChar b :=
        Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ fun a => by simp
    _ = ∑ b : ZMod q, χ⁻¹ (-1 : ZMod q) * (χ⁻¹ b * ZMod.stdAddChar b) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [show (-b : ZMod q) = (-1 : ZMod q) * b by ring, map_mul, mul_assoc]

/-- Exact product of conjugate Gauss sums for every primitive `χ mod q`:
`τ(χ) * τ(χ⁻¹) = χ(-1) * q`. -/
theorem gaussSum_mul_gaussSum_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar =
      χ (-1 : ZMod q) * (q : ℂ) := by
  have hsq_sign : χ (-1 : ZMod q) * χ (-1 : ZMod q) = 1 := by
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  have hnorm : gaussSum χ ZMod.stdAddChar * starRingEnd ℂ (gaussSum χ ZMod.stdAddChar) = (q : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_sq_gaussSum_eq hprim]
    exact Complex.ofReal_natCast q
  rw [conj_gaussSum_eq χ] at hnorm
  calc gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar
      = χ (-1 : ZMod q) * (gaussSum χ ZMod.stdAddChar *
          (χ (-1 : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar)) := by
        linear_combination -(gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar) * hsq_sign
    _ = χ (-1 : ZMod q) * (q : ℂ) := by rw [hnorm]

/-- Every primitive Dirichlet character has nonzero Gauss sum `τ(χ) ≠ 0`. -/
theorem gaussSum_ne_zero_of_isPrimitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) : gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro h0
  have hq := norm_sq_gaussSum_eq hprim
  rw [h0, norm_zero, zero_pow (by norm_num)] at hq
  exact (Nat.cast_pos (α := ℝ).mpr (NeZero.pos q)).ne hq

/-- Exact inverse of `τ(χ⁻¹)` for primitive `χ`: `(τ(χ⁻¹))⁻¹ = χ(-1) * τ(χ) / q`. -/
theorem inv_gaussSum_inv_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) :
    (gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ =
      χ (-1 : ZMod q) * gaussSum χ ZMod.stdAddChar / (q : ℂ) := by
  have hprim_inv : χ⁻¹.IsPrimitive := by
    show χ⁻¹.conductor = q
    rw [DirichletCharacter.conductor_inv, hprim]
  have hne : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := gaussSum_ne_zero_of_isPrimitive hprim_inv
  have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hsq_sign : χ (-1 : ZMod q) * χ (-1 : ZMod q) = 1 := by
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  refine inv_eq_of_mul_eq_one_right ?_
  calc gaussSum χ⁻¹ ZMod.stdAddChar * (χ (-1 : ZMod q) * gaussSum χ ZMod.stdAddChar / (q : ℂ))
      = χ (-1 : ZMod q) * (gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar) / (q : ℂ) := by
        ring
    _ = χ (-1 : ZMod q) * (χ (-1 : ZMod q) * (q : ℂ)) / (q : ℂ) := by
        rw [gaussSum_mul_gaussSum_inv hprim]
    _ = (χ (-1 : ZMod q) * χ (-1 : ZMod q)) * ((q : ℂ) / (q : ℂ)) := by ring
    _ = 1 := by rw [hsq_sign, div_self hq_ne, mul_one]

/-- Exact polar factorization of `1 - e(x)`:
`1 - e(x) = (2 * sin(π x)) * exp(i * π * (x - 1/2))`. -/
theorem one_sub_e_eq_polar (x : ℝ) :
    1 - e x =
      ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((Real.pi * (x - 1 / 2) : ℝ) : ℂ)) := by
  have hexp_half :
      Complex.exp (Complex.I * ((Real.pi * (x - 1 / 2) : ℝ) : ℂ)) =
        (-Complex.I) * Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    have harg :
        Complex.I * ((Real.pi * (x - 1 / 2) : ℝ) : ℂ) =
          -(Real.pi : ℂ) / 2 * Complex.I + ((Real.pi * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
  rw [hexp_half]
  have hsin :
      ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) * (-Complex.I) =
        Complex.exp (-(((Real.pi * x : ℝ) : ℂ) * Complex.I)) -
          Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, show -(((Real.pi * x : ℝ) : ℂ) * Complex.I) =
      (((-(Real.pi * x) : ℝ) : ℂ) * Complex.I) by push_cast; ring, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  calc 1 - e x
      = Complex.exp 0 - Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
        rw [Complex.exp_zero]; rfl
    _ = (Complex.exp (-(((Real.pi * x : ℝ) : ℂ) * Complex.I)) -
          Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I) := by
        rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add]
        congr 2
        · ring
        · push_cast; ring
    _ = ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) *
          ((-Complex.I) * Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
        rw [← mul_assoc, hsin]

/-- Exact principal-branch logarithm evaluation of `1 - e(x)` for `0 < x < 1`:
`Complex.log (1 - e x) = Real.log (2 * sin(π x)) + I * π * (x - 1/2)`. -/
theorem clog_one_sub_e_eq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Complex.log (1 - e x) =
      (Real.log (2 * Real.sin (Real.pi * x)) : ℂ) +
        Complex.I * ((Real.pi * (x - 1 / 2) : ℝ) : ℂ) := by
  have hsin_pos : 0 < 2 * Real.sin (Real.pi * x) := by
    have h1 : 0 < Real.pi * x := mul_pos Real.pi_pos hx0
    have h2 : Real.pi * x < Real.pi := by nlinarith [Real.pi_pos]
    exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  set z : ℂ :=
    (Real.log (2 * Real.sin (Real.pi * x)) : ℂ) +
      Complex.I * ((Real.pi * (x - 1 / 2) : ℝ) : ℂ)
  have hexp_eq : Complex.exp z = 1 - e x := by
    dsimp only [z]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hsin_pos, one_sub_e_eq_polar]
  have him_eq : z.im = Real.pi * (x - 1 / 2) := by
    dsimp only [z]; simp
  have him_gt : -Real.pi < z.im := by
    rw [him_eq]; nlinarith [Real.pi_pos]
  have him_le : z.im ≤ Real.pi := by
    rw [him_eq]; nlinarith [Real.pi_pos]
  rw [← hexp_eq, Complex.log_exp him_gt him_le]

/-- **Exact Finite-Sum Dirichlet `L(1, χ)` Formula (Gauss-Sum Product Form)**:
for every primitive non-principal character `χ ≠ 1` mod `q`,
`τ(χ⁻¹) * L(1, χ) = -∑_{a=1}^{q-1} χ⁻¹(a) * Complex.log (1 - e(a / q))`. -/
theorem gaussSum_inv_mul_LFunction_one_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    gaussSum χ⁻¹ ZMod.stdAddChar * LFunction χ 1 =
      -∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) * Complex.log (1 - e ((a : ℝ) / (q : ℝ))) := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hq_pos : 0 < q := by omega
  -- Rewrite finite identity `gaussSum_mul_char_sum_eq` over `Finset.Ico 1 q`
  have hfinite : ∀ N : ℕ,
      gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ) =
        ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Icc 1 N, e ((n : ℝ) * ((a : ℝ) / (q : ℝ))) / (n : ℂ) := by
    intro N
    have hg := gaussSum_mul_char_sum_eq hprim (Finset.Icc 1 N) (fun n => ((n : ℂ))⁻¹)
    have hL :
        ∑ n ∈ Finset.Icc 1 N, ((n : ℂ))⁻¹ * χ (n : ZMod q) =
          ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ) :=
      Finset.sum_congr rfl fun n _ => by rw [div_eq_mul_inv, mul_comm]
    rw [hL] at hg
    rw [hg]
    have hR :
        ∀ a : (ZMod q)ˣ,
          ∑ n ∈ Finset.Icc 1 N, ((n : ℂ))⁻¹ *
            e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) =
          ∑ n ∈ Finset.Icc 1 N,
            e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) / (n : ℂ) := fun a =>
      Finset.sum_congr rfl fun n _ => by ring
    simp_rw [hR]
    -- Convert sum over `(ZMod q)ˣ` to sum over `Finset.Ico 1 q`
    have hfilt :
        ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) *
            ∑ n ∈ Finset.Icc 1 N, e ((n : ℝ) * ((a : ℝ) / (q : ℝ))) / (n : ℂ) =
          ∑ a ∈ (Finset.Ico 1 q).filter (fun a => Nat.Coprime a q), χ⁻¹ (a : ZMod q) *
            ∑ n ∈ Finset.Icc 1 N, e ((n : ℝ) * ((a : ℝ) / (q : ℝ))) / (n : ℂ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hcop : Nat.Coprime a q
      · rw [if_pos hcop]
      · rw [if_neg hcop]
        have hnu : ¬ IsUnit (a : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime a q).mp hu)
        rw [MulChar.map_nonunit χ⁻¹ hnu, zero_mul]
    rw [hfilt]
    refine Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val) ?_ ?_ ?_ ?_
    · intro u _
      have hu_lt : (u : ZMod q).val < q := ZMod.val_lt _
      have hu_pos : 1 ≤ (u : ZMod q).val := by
        by_contra h0
        have hv0 : (u : ZMod q).val = 0 := by omega
        have hu0 : (u : ZMod q) = 0 := by
          rw [← ZMod.natCast_zmod_val (u : ZMod q), hv0]; simp
        have hnt : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
        exact not_isUnit_zero (hu0 ▸ u.isUnit)
      have hcop : Nat.Coprime (u : ZMod q).val q := by
        have hu : IsUnit (((u : ZMod q).val : ℕ) : ZMod q) := by
          rw [ZMod.natCast_zmod_val]; exact u.isUnit
        exact (ZMod.isUnit_iff_coprime _ q).mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hu_pos, hu_lt⟩, hcop⟩
    · intro u₁ _ u₂ _ h
      exact Units.ext (by
        rw [← ZMod.natCast_zmod_val (u₁ : ZMod q), ← ZMod.natCast_zmod_val (u₂ : ZMod q), h])
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Ico] at ha
      have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha.2
      refine ⟨hu.unit, Finset.mem_univ _, ?_⟩
      simp only [IsUnit.unit_spec, ZMod.val_natCast, Nat.mod_eq_of_lt ha.1.2]
    · intro u _
      simp only [ZMod.natCast_zmod_val]
  -- Pass `N → ∞` on both sides
  have hLHS :
      Tendsto (fun N : ℕ =>
          gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ))
        atTop (nhds (gaussSum χ⁻¹ ZMod.stdAddChar * LFunction χ 1)) :=
    (tendsto_partialSum_LFunction_one hχ).const_mul _
  have hRHS :
      Tendsto (fun N : ℕ =>
          ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) *
            ∑ n ∈ Finset.Icc 1 N, e ((n : ℝ) * ((a : ℝ) / (q : ℝ))) / (n : ℂ))
        atTop (nhds (-∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) *
          Complex.log (1 - e ((a : ℝ) / (q : ℝ))))) := by
    have hsum := tendsto_finsetSum (Finset.Ico 1 q) fun a ha => by
      have ha' := Finset.mem_Ico.mp ha
      exact (tendsto_fourier_log_series (distZ_div_pos ha'.1 ha'.2)).const_mul (χ⁻¹ (a : ZMod q))
    have hlim :
        ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) * -Complex.log (1 - e ((a : ℝ) / (q : ℝ))) =
          -∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) * Complex.log (1 - e ((a : ℝ) / (q : ℝ))) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => by ring
    rwa [hlim] at hsum
  have heq_fun :
      (fun N : ℕ =>
          gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ)) =
        (fun N : ℕ =>
          ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) *
            ∑ n ∈ Finset.Icc 1 N, e ((n : ℝ) * ((a : ℝ) / (q : ℝ))) / (n : ℂ)) :=
    funext hfinite
  rw [heq_fun] at hLHS
  exact tendsto_nhds_unique hLHS hRHS

/-- **Exact Finite-Sum Dirichlet `L(1, χ)` Formula (General Primitive Character)**:
`LFunction χ 1 = -(χ(-1) * τ(χ) / q) * ∑_{a=1}^{q-1} χ⁻¹(a) * Complex.log (1 - e(a / q))`. -/
theorem LFunction_one_eq_neg_sign_gaussSum_div_q_mul_sum_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    LFunction χ 1 =
      -(χ (-1 : ZMod q) * gaussSum χ ZMod.stdAddChar / (q : ℂ)) *
        ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) * Complex.log (1 - e ((a : ℝ) / (q : ℝ))) := by
  have hprim_inv : χ⁻¹.IsPrimitive := by
    show χ⁻¹.conductor = q
    rw [DirichletCharacter.conductor_inv, hprim]
  have hne : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := gaussSum_ne_zero_of_isPrimitive hprim_inv
  have h := congrArg ((gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ * ·)
    (gaussSum_inv_mul_LFunction_one_eq hprim hχ)
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul, inv_gaussSum_inv_eq hprim] at h
  rw [h]; ring

/-- Equivalent inverse-Gauss-sum form:
`LFunction χ 1 = -(τ(χ⁻¹))⁻¹ * ∑_{a=1}^{q-1} χ⁻¹(a) * Complex.log (1 - e(a / q))`. -/
theorem LFunction_one_eq_neg_inv_gaussSum_mul_sum_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    LFunction χ 1 =
      -(gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
        ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) * Complex.log (1 - e ((a : ℝ) / (q : ℝ))) := by
  rw [LFunction_one_eq_neg_sign_gaussSum_div_q_mul_sum_log hprim hχ, ← inv_gaussSum_inv_eq hprim]

/-- Helper: reflection `a ↦ q - a` on `Finset.Ico 1 q` transforms `χ⁻¹ (q - a) = χ(-1) * χ⁻¹ a`. -/
private lemma char_inv_sub_eq {q a : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ha : a ≤ q) :
    χ⁻¹ ((q - a : ℕ) : ZMod q) = χ (-1 : ZMod q) * χ⁻¹ (a : ZMod q) := by
  have hcast : ((q - a : ℕ) : ZMod q) = (-1 : ZMod q) * (a : ZMod q) := by
    rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub, neg_one_mul]
  have hinv_neg : χ⁻¹ (-1 : ZMod q) = χ (-1 : ZMod q) := by
    rw [MulChar.inv_apply_eq_inv']
    have hsq : χ (-1 : ZMod q) * χ (-1 : ZMod q) = 1 := by
      rw [← map_mul, neg_mul_neg, one_mul, map_one]
    exact (eq_inv_of_mul_eq_one_left hsq).symm
  rw [hcast, map_mul, hinv_neg]

/-- **Exact Finite-Sum Dirichlet `L(1, χ)` Formula for EVEN Primitive Characters (`χ(-1) = 1`)**:
`LFunction χ 1 = -(τ(χ) / q) * ∑_{a=1}^{q-1} χ⁻¹(a) * Real.log (2 * Real.sin (π * a / q))`. -/
theorem LFunction_one_eq_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even) :
    LFunction χ 1 =
      -(gaussSum χ ZMod.stdAddChar / (q : ℂ)) *
        ∑ a ∈ Finset.Ico 1 q,
          χ⁻¹ (a : ZMod q) * (Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) : ℂ) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  rw [LFunction_one_eq_neg_sign_gaussSum_div_q_mul_sum_log hprim hχ, heven, one_mul]
  congr 1
  -- Split `Complex.log (1 - e(a/q))` into real log + odd imaginary part
  have hsplit :
      ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) * Complex.log (1 - e ((a : ℝ) / (q : ℝ))) =
        (∑ a ∈ Finset.Ico 1 q,
          χ⁻¹ (a : ZMod q) * (Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) : ℂ)) +
        (∑ a ∈ Finset.Ico 1 q,
          χ⁻¹ (a : ZMod q) * (Complex.I * ((Real.pi * ((a : ℝ) / (q : ℝ) - 1 / 2) : ℝ) : ℂ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_Ico.mp ha
    have hx0 : 0 < (a : ℝ) / (q : ℝ) := div_pos (Nat.cast_pos.mpr ha'.1) hq_pos
    have hx1 : (a : ℝ) / (q : ℝ) < 1 := (div_lt_one hq_pos).mpr (by exact_mod_cast ha'.2)
    rw [clog_one_sub_e_eq hx0 hx1, mul_add, mul_div_assoc]
  rw [hsplit]
  -- Show the odd imaginary part sums to `0` by `a ↦ q - a`
  set S_im : ℂ := ∑ a ∈ Finset.Ico 1 q,
    χ⁻¹ (a : ZMod q) * (Complex.I * ((Real.pi * ((a : ℝ) / (q : ℝ) - 1 / 2) : ℝ) : ℂ))
  have hSim : S_im = -S_im := by
    dsimp only [S_im]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
    · intro a₁ ha₁ a₂ ha₂ h; simp only [Finset.mem_Ico] at ha₁ ha₂; omega
    · intro b hb; simp only [Finset.mem_Ico] at hb
      exact ⟨q - b, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro a ha
      have ha' := Finset.mem_Ico.mp ha
      rw [char_inv_sub_eq χ ha'.2.le, heven, one_mul]
      have harg :
          ((q - a : ℕ) : ℝ) / (q : ℝ) - 1 / 2 = -((a : ℝ) / (q : ℝ) - 1 / 2) := by
        rw [Nat.cast_sub ha'.2.le]
        field_simp [hq_pos.ne']
        ring
      rw [harg]
      push_cast
      ring
  have hSim0 : S_im = 0 := by
    have h2 : (2 : ℂ) * S_im = 0 := by linear_combination hSim
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [hSim0, add_zero]

/-- **Exact Finite-Sum Dirichlet `L(1, χ)` Formula for ODD Primitive Characters (`χ(-1) = -1`)**:
`LFunction χ 1 = (I * π * τ(χ) / q²) * ∑_{a=1}^{q-1} a * χ⁻¹(a)`. -/
theorem LFunction_one_eq_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hodd : χ.Odd) :
    LFunction χ 1 =
      (Complex.I * (Real.pi : ℂ) * gaussSum χ ZMod.stdAddChar / ((q : ℂ) ^ 2)) *
        ∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ⁻¹ (a : ZMod q) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hqC_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [LFunction_one_eq_neg_sign_gaussSum_div_q_mul_sum_log hprim hχ, hodd]
  have hsplit :
      ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) * Complex.log (1 - e ((a : ℝ) / (q : ℝ))) =
        (∑ a ∈ Finset.Ico 1 q,
          χ⁻¹ (a : ZMod q) * (Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) : ℂ)) +
        (∑ a ∈ Finset.Ico 1 q,
          χ⁻¹ (a : ZMod q) * (Complex.I * ((Real.pi * ((a : ℝ) / (q : ℝ) - 1 / 2) : ℝ) : ℂ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_Ico.mp ha
    have hx0 : 0 < (a : ℝ) / (q : ℝ) := div_pos (Nat.cast_pos.mpr ha'.1) hq_pos
    have hx1 : (a : ℝ) / (q : ℝ) < 1 := (div_lt_one hq_pos).mpr (by exact_mod_cast ha'.2)
    rw [clog_one_sub_e_eq hx0 hx1, mul_add, mul_div_assoc]
  rw [hsplit]
  -- Show the even log part sums to `0` by `a ↦ q - a`
  set S_re : ℂ := ∑ a ∈ Finset.Ico 1 q,
    χ⁻¹ (a : ZMod q) * (Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) : ℂ)
  have hSre : S_re = -S_re := by
    dsimp only [S_re]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
    · intro a₁ ha₁ a₂ ha₂ h; simp only [Finset.mem_Ico] at ha₁ ha₂; omega
    · intro b hb; simp only [Finset.mem_Ico] at hb
      exact ⟨q - b, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro a ha
      have ha' := Finset.mem_Ico.mp ha
      rw [char_inv_sub_eq χ ha'.2.le, hodd]
      have hsin_eq :
          Real.sin (Real.pi * ((q - a : ℕ) : ℝ) / (q : ℝ)) =
            Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
        have harg : Real.pi * ((q - a : ℕ) : ℝ) / (q : ℝ) =
            Real.pi - Real.pi * (a : ℝ) / (q : ℝ) := by
          rw [Nat.cast_sub ha'.2.le]
          field_simp [hq_pos.ne']
        rw [harg, Real.sin_pi_sub]
      rw [hsin_eq]; ring
  have hSre0 : S_re = 0 := by
    have h2 : (2 : ℂ) * S_re = 0 := by linear_combination hSre
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [hSre0, zero_add]
  -- Simplify the linear term using `∑_{a=1}^{q-1} χ⁻¹(a) = 0`
  have hχinv_ne : χ⁻¹ ≠ 1 := fun h1 => hχ (by simpa using congrArg Inv.inv h1)
  have hsum_zero : ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) = 0 := by
    have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
    have h0 : χ⁻¹ (0 : ZMod q) = 0 := χ⁻¹.map_zero' (by omega)
    have hrange : Finset.range q = insert 0 (Finset.Ico 1 q) := by
      ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    have hfull : ∑ a ∈ Finset.range q, χ⁻¹ (a : ZMod q) = ∑ a : ZMod q, χ⁻¹ a := by
      refine Finset.sum_bij (fun a _ => (a : ZMod q)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a₁ ha₁ a₂ ha₂ h
        simp only [Finset.mem_range] at ha₁ ha₂
        have hv := congrArg ZMod.val h
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha₁, Nat.mod_eq_of_lt ha₂] at hv
      · intro x _; exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
      · intro _ _; rfl
    have htot := sum_dirichletChar_zmod_eq_zero hχinv_ne
    rw [← hfull, hrange, Finset.sum_insert (by simp), Nat.cast_zero, h0, zero_add] at htot
    exact htot
  have hlin :
      ∑ a ∈ Finset.Ico 1 q,
          χ⁻¹ (a : ZMod q) * (Complex.I * ((Real.pi * ((a : ℝ) / (q : ℝ) - 1 / 2) : ℝ) : ℂ)) =
        (Complex.I * (Real.pi : ℂ) / (q : ℂ)) *
          ∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ⁻¹ (a : ZMod q) := by
    have hexp :
        ∑ a ∈ Finset.Ico 1 q,
            χ⁻¹ (a : ZMod q) * (Complex.I * ((Real.pi * ((a : ℝ) / (q : ℝ) - 1 / 2) : ℝ) : ℂ)) =
          (Complex.I * (Real.pi : ℂ) / (q : ℂ)) *
              (∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ⁻¹ (a : ZMod q)) -
            (Complex.I * (Real.pi : ℂ) / 2) * ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast; ring
    rw [hexp, hsum_zero, mul_zero, sub_zero]
  rw [hlin]
  field_simp [hqC_ne]

/-- **Exact Modulus Formula for Odd Primitive `L(1, χ)`**:
`‖LFunction χ 1‖ = (π / (q * √q)) * ‖∑_{a=1}^{q-1} a * χ⁻¹(a)‖`. -/
theorem norm_LFunction_one_eq_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hodd : χ.Odd) :
    ‖LFunction χ 1‖ =
      (Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ))) *
        ‖∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ⁻¹ (a : ZMod q)‖ := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  rw [LFunction_one_eq_odd hprim hχ hodd, norm_mul, norm_div, norm_mul, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    norm_gaussSum_eq_sqrt hprim, norm_pow, Complex.norm_natCast]
  congr 1
  have hsq : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := Real.mul_self_sqrt hq_pos.le
  field_simp [hq_pos.ne', hsqrt_pos.ne']
  nlinarith

/-- For a real Dirichlet character (`∀ a, (χ a).im = 0`), `χ⁻¹ = χ`. -/
theorem dirichletChar_inv_eq_self_of_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ⁻¹ = χ := by
  ext a
  have hstar : starRingEnd ℂ (χ a) = χ a := Complex.conj_eq_iff_im.mpr (hreal a)
  have hinv : χ⁻¹ a = starRingEnd ℂ (χ a) := by
    simpa [RCLike.star_def] using (MulChar.star_apply' χ a).symm
  rw [hinv, hstar]

/-- Real-part exact evaluation for odd real primitive `χ` whenever `τ(χ) = I * √q`:
`(LFunction χ 1).re = -(π / (q * √q)) * ∑_{a=1}^{q-1} a * (χ a).re`. -/
theorem re_LFunction_one_eq_odd_real_of_gaussSum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hodd : χ.Odd)
    (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hgauss : gaussSum χ ZMod.stdAddChar = Complex.I * (Real.sqrt (q : ℝ) : ℂ)) :
    (LFunction χ 1).re =
      -(Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ))) *
        ∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  have hqC_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hL := LFunction_one_eq_odd hprim hχ hodd
  rw [hgauss, dirichletChar_inv_eq_self_of_real hreal] at hL
  have hsum_real :
      ∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ (a : ZMod q) =
        ((∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha : χ (a : ZMod q) = ((χ (a : ZMod q)).re : ℂ) :=
      Complex.ext (by simp) (by simpa using hreal _)
    rw [ha]; push_cast; rfl
  have hcoeff :
      Complex.I * (Real.pi : ℂ) * (Complex.I * (Real.sqrt (q : ℝ) : ℂ)) / ((q : ℂ) ^ 2) =
        ((-(Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ))) : ℝ) : ℂ) := by
    have hsq : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := Real.mul_self_sqrt hq_pos.le
    have hsqC : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
      rw [sq]; exact_mod_cast hsq
    have hsqrtC_ne : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqrt_pos.ne'
    push_cast
    field_simp [hqC_ne, hsqrtC_ne]
    rw [Complex.I_sq, hsqC]
    ring
  rw [hL, hcoeff, hsum_real, ← Complex.ofReal_mul, Complex.ofReal_re]

/-! ## Section 3: Unconditional Strict Positivity `L(1, χ) > 0` for Every Real `χ ≠ 1` -/

/-- For every real non-principal character `χ ≠ 1` and every real `σ > 0`,
`LFunction χ (σ : ℂ)` is real-valued (`(LFunction χ σ).im = 0`). -/
theorem LFunction_im_eq_zero_of_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : ∀ a : ZMod q, (χ a).im = 0) {σ : ℝ} (hσ : 0 < σ) :
    (LFunction χ (σ : ℂ)).im = 0 := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  rw [LFunction_eq_mul_mellin_of_ne_one hχ hs]
  have hstep_real : ∀ t : ℝ,
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t =
        ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (χ (n : ZMod q)).re : ℝ) : ℂ) := by
    intro t
    unfold Stage3RealAnalyticLandau.stepSum
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact Complex.ext (by simp) (by simpa using hreal _)
  have hint_eq :
      ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-(σ : ℂ) - 1) =
      ((∫ t in Ioi (1 : ℝ),
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (χ (n : ZMod q)).re) * t ^ (-σ - 1) : ℝ) : ℂ) := by
    have hof :
        ∫ t in Ioi (1 : ℝ),
          (((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (χ (n : ZMod q)).re) * t ^ (-σ - 1) : ℝ) : ℂ) =
        ((∫ t in Ioi (1 : ℝ),
          (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (χ (n : ZMod q)).re) * t ^ (-σ - 1) : ℝ) : ℂ) :=
      integral_ofReal
    rw [← hof]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [hstep_real t, Complex.ofReal_mul, show -(σ : ℂ) - 1 = ((-σ - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow ht0.le]
  rw [hint_eq, ← Complex.ofReal_mul, Complex.ofReal_im]

/-- For every real character `χ` and every real `σ > 1`, `0 < (LFunction χ σ).re`. -/
theorem LFunction_re_pos_of_real_of_one_lt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) {σ : ℝ} (hσ : 1 < σ) :
    0 < (LFunction χ (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have heuler := DirichletCharacter.LSeries_eulerProduct χ hs
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hs] at heuler
  -- Every finite Euler product is strictly positive real
  have hfin_pos : ∀ N : ℕ,
      (∏ p ∈ N.primesBelow, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(σ : ℂ)))⁻¹).im = 0 ∧
      0 < (∏ p ∈ N.primesBelow, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(σ : ℂ)))⁻¹).re := by
    intro N
    have hprod_real :
        ∏ p ∈ N.primesBelow, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(σ : ℂ)))⁻¹ =
          ((∏ p ∈ N.primesBelow, (1 - (χ (p : ZMod q)).re * (p : ℝ) ^ (-σ))⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primesBelow hp).pos
      have hχp : χ (p : ZMod q) = ((χ (p : ZMod q)).re : ℂ) :=
        Complex.ext (by simp) (by simpa using hreal _)
      have hpow : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, show -(σ : ℂ) = ((-σ : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_cpow hp_pos.le]
      rw [hχp, hpow]
      push_cast; rfl
    rw [hprod_real, Complex.ofReal_im, Complex.ofReal_re]
    refine ⟨rfl, Finset.prod_pos fun p hp => inv_pos.mpr ?_⟩
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hpow_lt1 : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
    have hre_le1 : (χ (p : ZMod q)).re ≤ 1 := by
      have h1 : |(χ (p : ZMod q)).re| ≤ ‖χ (p : ZMod q)‖ := Complex.abs_re_le_norm _
      have h2 : ‖χ (p : ZMod q)‖ ≤ 1 := χ.norm_le_one _
      linarith [(le_abs_self _).trans (h1.trans h2)]
    have hmul_lt1 : (χ (p : ZMod q)).re * (p : ℝ) ^ (-σ) < 1 := by
      have hpow_pos : 0 < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp_pos _
      calc (χ (p : ZMod q)).re * (p : ℝ) ^ (-σ)
          ≤ 1 * (p : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right hre_le1 hpow_pos.le
        _ = (p : ℝ) ^ (-σ) := one_mul _
        _ < 1 := hpow_lt1
    linarith
  have hre_ge : 0 ≤ (LFunction χ (σ : ℂ)).re :=
    ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp heuler)
      (Eventually.of_forall fun N => (hfin_pos N).2.le)
  have him_zero : (LFunction χ (σ : ℂ)).im = 0 :=
    tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp heuler)
      (tendsto_const_nhds.congr fun N => (hfin_pos N).1.symm)
  have hne : LFunction χ (σ : ℂ) ≠ 0 :=
    Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ
      (Or.inr (by intro h1; have := congrArg Complex.re h1; simp at this; linarith))
      (by simpa using hσ.le)
  have hre_ne : (LFunction χ (σ : ℂ)).re ≠ 0 := fun h0 =>
    hne (Complex.ext (by simpa using h0) (by simpa using him_zero))
  exact lt_of_le_of_ne hre_ge hre_ne.symm

/-- **UNCONDITIONAL STRICT POSITIVITY `L(1, χ) > 0` FOR EVERY REAL NON-PRINCIPAL CHARACTER `χ ≠ 1`**:
for every modulus `q ≥ 1` and every real non-principal `χ : DirichletCharacter ℂ q`,
`0 < (LFunction χ 1).re ∧ (LFunction χ 1).im = 0`. -/
theorem LFunction_one_pos_of_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    0 < (DirichletCharacter.LFunction χ 1).re ∧ (DirichletCharacter.LFunction χ 1).im = 0 := by
  have him : (DirichletCharacter.LFunction χ 1).im = 0 := by
    simpa only [Complex.ofReal_one] using LFunction_im_eq_zero_of_real hχ hreal zero_lt_one
  have hcont : Continuous (fun σ : ℝ => (DirichletCharacter.LFunction χ (σ : ℂ)).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hseq_tend : Tendsto (fun n : ℕ => (1 : ℝ) + ((n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 1) := by
    have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp (tendsto_add_atTop_nat 1)
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  have hre_ge : 0 ≤ (DirichletCharacter.LFunction χ 1).re := by
    have ht := (hcont.tendsto 1).comp hseq_tend
    simp only [Complex.ofReal_one] at ht
    refine ge_of_tendsto ht (Eventually.of_forall fun n => ?_)
    have hgt : (1 : ℝ) < 1 + ((n + 1 : ℕ) : ℝ)⁻¹ := by
      have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)⁻¹ := inv_pos.mpr (by positivity)
      linarith
    exact (LFunction_re_pos_of_real_of_one_lt hreal hgt).le
  have hne : DirichletCharacter.LFunction χ 1 ≠ 0 :=
    Stage2DirichletAP.LFunction_apply_one_ne_zero_bridge hχ
  have hre_ne : (DirichletCharacter.LFunction χ 1).re ≠ 0 := fun h0 =>
    hne (Complex.ext (by simpa using h0) (by simpa using him))
  exact ⟨lt_of_le_of_ne hre_ge hre_ne.symm, him⟩

/-- Conditional-on-Gauss-sum form of Dirichlet's Sign Theorem (unconditionally discharged for
ALL real primitive characters in Section 4 below): if `χ` is odd real primitive and
`τ(χ) = I * √q`, then `∑_{a=1}^{q-1} a * (χ a).re < 0`. -/
theorem sum_mul_odd_real_char_neg_of_gaussSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hodd : χ.Odd)
    (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hgauss : gaussSum χ ZMod.stdAddChar = Complex.I * (Real.sqrt (q : ℝ) : ℂ)) :
    ∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re < 0 := by
  have hpos := (LFunction_one_pos_of_real χ hχ hreal).1
  rw [re_LFunction_one_eq_odd_real_of_gaussSum hprim hχ hodd hreal hgauss] at hpos
  have hc_pos : 0 < Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
    exact div_pos Real.pi_pos (mul_pos hq_pos (Real.sqrt_pos.mpr hq_pos))
  nlinarith

/-! ## Section 4: Exact Quadratic Gauss Sum & Unconditional Dirichlet Non-Vanishing Sign Theorem -/

/-- Helper: positive real scalar pulls out of complex power:
for `r > 0` and `z ≠ 0`, `((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w`. -/
private lemma cpow_ofReal_mul_of_pos {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hrC hz),
    Complex.cpow_def_of_ne_zero hrC, Complex.cpow_def_of_ne_zero hz,
    ← Complex.exp_add, ← add_mul, Complex.log_ofReal_mul hr hz,
    ← Complex.ofReal_log hr.le]

/-- Helper: shifted Gaussian Poisson summation identity:
for `0 < c.re` and `α : ℝ`,
`∑' m : ℤ, cexp (-π * c * (m + α)^2) = (1 / c^(1/2)) * ∑' k : ℤ, cexp (-π / c * k^2 - 2πi α k)`. -/
private lemma tsum_cexp_neg_pi_mul_add_sq {c : ℂ} (hc : 0 < c.re) (α : ℝ) :
    (∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * c * ((m : ℂ) + (α : ℂ)) ^ 2)) =
      1 / c ^ (1 / 2 : ℂ) *
        ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) / c * (k : ℂ) ^ 2 -
          2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (k : ℂ)) := by
  have hc_ne : c ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hc; exact lt_irrefl _ hc
  have hcinv_re : 0 < (c⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hc (Complex.normSq_pos.mpr hc_ne)
  have hpois := Complex.tsum_exp_neg_quadratic hcinv_re (-Complex.I * (α : ℂ))
  have hL :
      ∀ k : ℤ,
        Complex.exp (-(Real.pi : ℂ) * c⁻¹ * (k : ℂ) ^ 2 +
            2 * (Real.pi : ℂ) * (-Complex.I * (α : ℂ)) * (k : ℂ)) =
          Complex.exp (-(Real.pi : ℂ) / c * (k : ℂ) ^ 2 -
            2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (k : ℂ)) := fun k => by
    congr 1; ring
  have hR :
      ∀ m : ℤ,
        Complex.exp (-(Real.pi : ℂ) / c⁻¹ * ((m : ℂ) + Complex.I * (-Complex.I * (α : ℂ))) ^ 2) =
          Complex.exp (-(Real.pi : ℂ) * c * ((m : ℂ) + (α : ℂ)) ^ 2) := fun m => by
    congr 1
    rw [div_inv_eq_mul]
    have hII : Complex.I * (-Complex.I * (α : ℂ)) = (α : ℂ) := by
      calc Complex.I * (-Complex.I * (α : ℂ))
          = -(Complex.I * Complex.I) * (α : ℂ) := by ring
        _ = -(-1) * (α : ℂ) := by rw [Complex.I_mul_I]
        _ = (α : ℂ) := by ring
    rw [hII]
  simp_rw [hL, hR] at hpois
  have harg : c.arg ≠ Real.pi := by
    intro hpi
    have hlt := (Complex.arg_eq_pi_iff.mp hpi).1
    linarith
  rw [Complex.inv_cpow c (1 / 2 : ℂ) harg, one_div, inv_inv] at hpois
  have hcpow_ne : c ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hc_ne]
    exact Complex.exp_ne_zero _
  have hmul := congrArg ((c ^ (1 / 2 : ℂ))⁻¹ * ·) hpois
  rw [← mul_assoc, inv_mul_cancel₀ hcpow_ne, one_mul] at hmul
  rw [one_div]
  exact hmul.symm

/-- Helper: summability of `k ↦ cexp (-π / c * k^2 - 2πi α k)` for `0 < c.re` and its exact tail bound
`‖(∑' k : ℤ, ...) - 1‖ ≤ 2 * exp (-π * (c⁻¹).re) / (1 - exp (-π * (c⁻¹).re))`. -/
private lemma norm_tsum_dual_gaussian_sub_one_le {c : ℂ} (hc : 0 < c.re) (α : ℝ) :
    ‖(∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) / c * (k : ℂ) ^ 2 -
        2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (k : ℂ))) - 1‖ ≤
      2 * Real.exp (-Real.pi * (c⁻¹).re) / (1 - Real.exp (-Real.pi * (c⁻¹).re)) := by
  have hc_ne : c ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hc; exact lt_irrefl _ hc
  have hcinv_re : 0 < (c⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hc (Complex.normSq_pos.mpr hc_ne)
  set ρ : ℝ := Real.exp (-Real.pi * (c⁻¹).re)
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  let g : ℤ → ℂ := fun k =>
    Complex.exp (-(Real.pi : ℂ) / c * (k : ℂ) ^ 2 -
      2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (k : ℂ))
  have hg_norm : ∀ k : ℤ, ‖g k‖ ≤ ρ ^ k.natAbs := by
    intro k
    dsimp only [g, ρ]
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hre :
        (-(Real.pi : ℂ) / c * (k : ℂ) ^ 2 -
            2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (k : ℂ)).re =
          -Real.pi * (c⁻¹).re * (k : ℝ) ^ 2 := by
      rw [div_eq_mul_inv]
      have h1 : (-(Real.pi : ℂ) * c⁻¹ * (k : ℂ) ^ 2).re = -Real.pi * (c⁻¹).re * (k : ℝ) ^ 2 := by
        have hcast : (k : ℂ) ^ 2 = (((k : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast, show -(Real.pi : ℂ) * c⁻¹ * (((k : ℝ) ^ 2 : ℝ) : ℂ) =
          (((-Real.pi * (k : ℝ) ^ 2 : ℝ) : ℂ)) * c⁻¹ by push_cast; ring, Complex.re_ofReal_mul]
        ring
      have h2 : (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (k : ℂ)).re = 0 := by
        rw [show 2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (k : ℂ) =
          (((2 * Real.pi * α * (k : ℝ) : ℝ) : ℂ)) * Complex.I by push_cast; ring]
        simp
      rw [Complex.sub_re, h1, h2, sub_zero]
    rw [hre]
    have hle : (k.natAbs : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hk_sq : (k : ℝ) ^ 2 = (k.natAbs : ℝ) ^ 2 := by
        rw [← Int.cast_natCast, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]
      rw [hk_sq]
      rcases Nat.eq_zero_or_pos k.natAbs with h0 | hpos
      · simp [h0]
      · have h1 : (1 : ℝ) ≤ (k.natAbs : ℝ) := Nat.one_le_cast.mpr hpos
        nlinarith
    have hfac : 0 < Real.pi * (c⁻¹).re := mul_pos Real.pi_pos hcinv_re
    nlinarith
  have hsum_pos : Summable (fun m : ℕ => g ((m + 1 : ℕ) : ℤ)) := by
    refine Summable.of_norm_bounded (g := fun m : ℕ => ρ ^ (m + 1)) ?_ fun m => ?_
    · exact (summable_geometric_of_lt_one hρ0.le hρ1).comp_injective Nat.succ_injective
    · simpa only [Int.natAbs_natCast] using hg_norm ((m + 1 : ℕ) : ℤ)
  have hsum_neg : Summable (fun m : ℕ => g (-((m + 1 : ℕ) : ℤ))) := by
    refine Summable.of_norm_bounded (g := fun m : ℕ => ρ ^ (m + 1)) ?_ fun m => ?_
    · exact (summable_geometric_of_lt_one hρ0.le hρ1).comp_injective Nat.succ_injective
    · simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hg_norm (-((m + 1 : ℕ) : ℤ))
  have hsum_nat : Summable (fun m : ℕ => g (m : ℤ)) :=
    (summable_nat_add_iff 1).mp hsum_pos
  have hsplit :
      ∑' k : ℤ, g k =
        g 0 + (∑' m : ℕ, g ((m + 1 : ℕ) : ℤ)) + ∑' m : ℕ, g (-((m + 1 : ℕ) : ℤ)) := by
    have hneg' : Summable (fun n : ℕ => g (-((n : ℤ) + 1))) := by
      refine hsum_neg.congr fun n => ?_; congr 1
    have hz := tsum_of_nat_of_neg_add_one hsum_nat hneg'
    have h0 := hsum_nat.tsum_eq_zero_add
    rw [hz, h0]
    have hneg_eq : (∑' n : ℕ, g (-((n : ℤ) + 1))) = ∑' m : ℕ, g (-((m + 1 : ℕ) : ℤ)) :=
      tsum_congr fun m => by congr 1
    rw [hneg_eq, Nat.cast_zero]
  have hg0 : g 0 = 1 := by simp [g]
  have hgeom_val : ∑' m : ℕ, ρ ^ (m + 1) = ρ / (1 - ρ) := by
    have h1 : (fun m : ℕ => ρ ^ (m + 1)) = fun m : ℕ => ρ * ρ ^ m := by
      funext m; rw [pow_succ']
    rw [h1, tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1, div_eq_mul_inv]
  have hbd_pos : ‖∑' m : ℕ, g ((m + 1 : ℕ) : ℤ)‖ ≤ ρ / (1 - ρ) := by
    rw [← hgeom_val]
    refine (norm_tsum_le_tsum_norm hsum_pos.norm).trans ?_
    exact Summable.tsum_le_tsum (fun m => by simpa only [Int.natAbs_natCast] using hg_norm ((m + 1 : ℕ) : ℤ))
      hsum_pos.norm ((summable_geometric_of_lt_one hρ0.le hρ1).comp_injective Nat.succ_injective)
  have hbd_neg : ‖∑' m : ℕ, g (-((m + 1 : ℕ) : ℤ))‖ ≤ ρ / (1 - ρ) := by
    rw [← hgeom_val]
    refine (norm_tsum_le_tsum_norm hsum_neg.norm).trans ?_
    exact Summable.tsum_le_tsum (fun m => by simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hg_norm (-((m + 1 : ℕ) : ℤ)))
      hsum_neg.norm ((summable_geometric_of_lt_one hρ0.le hρ1).comp_injective Nat.succ_injective)
  change ‖(∑' k : ℤ, g k) - 1‖ ≤ 2 * ρ / (1 - ρ)
  rw [hsplit, hg0]
  have hsub :
      1 + (∑' m : ℕ, g ((m + 1 : ℕ) : ℤ)) + (∑' m : ℕ, g (-((m + 1 : ℕ) : ℤ))) - 1 =
        (∑' m : ℕ, g ((m + 1 : ℕ) : ℤ)) + ∑' m : ℕ, g (-((m + 1 : ℕ) : ℤ)) := by ring
  rw [hsub]
  calc ‖(∑' m : ℕ, g ((m + 1 : ℕ) : ℤ)) + ∑' m : ℕ, g (-((m + 1 : ℕ) : ℤ))‖
      ≤ ‖∑' m : ℕ, g ((m + 1 : ℕ) : ℤ)‖ + ‖∑' m : ℕ, g (-((m + 1 : ℕ) : ℤ))‖ := norm_add_le _ _
    _ ≤ ρ / (1 - ρ) + ρ / (1 - ρ) := add_le_add hbd_pos hbd_neg
    _ = 2 * ρ / (1 - ρ) := by ring

/-- Master shifted-Gaussian limit: if `0 < (c n).re` and `((c n)⁻¹).re → +∞`, then for any `α : ℝ`,
`(c n)^(1/2) * ∑' m : ℤ, cexp (-π * c n * (m + α)^2) → 1`. -/
private lemma tendsto_tsum_cexp_shift_one {c : ℕ → ℂ} {α : ℝ}
    (hc_re : ∀ n, 0 < (c n).re)
    (hc_inv_re : Tendsto (fun n => ((c n)⁻¹).re) atTop atTop) :
    Tendsto
      (fun n =>
        (c n) ^ (1 / 2 : ℂ) *
          ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * c n * ((m : ℂ) + (α : ℂ)) ^ 2))
      atTop (nhds 1) := by
  have heq :
      ∀ n : ℕ,
        (c n) ^ (1 / 2 : ℂ) *
            ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * c n * ((m : ℂ) + (α : ℂ)) ^ 2) =
          ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) / c n * (k : ℂ) ^ 2 -
            2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (k : ℂ)) := by
    intro n
    have hc_ne : c n ≠ 0 := fun h0 => by have := hc_re n; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this
    have hcpow_ne : (c n) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hc_ne]; exact Complex.exp_ne_zero _
    rw [tsum_cexp_neg_pi_mul_add_sq (hc_re n) α, ← mul_assoc, mul_one_div_cancel hcpow_ne, one_mul]
  simp_rw [heq]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hρ_tend : Tendsto (fun n => Real.exp (-Real.pi * ((c n)⁻¹).re)) atTop (nhds 0) := by
    have hneg : Tendsto (fun n => -Real.pi * ((c n)⁻¹).re) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos) hc_inv_re
    exact Real.tendsto_exp_atBot.comp hneg
  have hdom :
      Tendsto (fun n => 2 * Real.exp (-Real.pi * ((c n)⁻¹).re) /
        (1 - Real.exp (-Real.pi * ((c n)⁻¹).re))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => 2 * Real.exp (-Real.pi * ((c n)⁻¹).re)) atTop (nhds (2 * 0)) :=
      hρ_tend.const_mul 2
    have h2 : Tendsto (fun n => 1 - Real.exp (-Real.pi * ((c n)⁻¹).re)) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hρ_tend
    have hdiv := h1.div h2 (by norm_num)
    rw [mul_zero, sub_zero, zero_div] at hdiv
    exact hdiv.congr fun _ => rfl
  refine squeeze_zero_norm' ?_ hdom
  exact Eventually.of_forall fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_tsum_dual_gaussian_sub_one_le (hc_re n) α

/-- Exact square root `(-2 * I / q) ^ (1 / 2 : ℂ) = (1 - I) / √q` for `q > 0`. -/
private lemma neg_two_mul_I_div_cpow_half {q : ℕ} (hq : 0 < q) :
    (-(2 : ℂ) * Complex.I / (q : ℂ)) ^ (1 / 2 : ℂ) =
      (1 - Complex.I) / (Real.sqrt (q : ℝ) : ℂ) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  have hsqrtC_ne : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsqrt_pos.ne'
  have h2q_pos : (0 : ℝ) < 2 / (q : ℝ) := div_pos (by norm_num) hq_pos
  have hrew : -(2 : ℂ) * Complex.I / (q : ℂ) = ((2 / (q : ℝ) : ℝ) : ℂ) * (-Complex.I) := by
    push_cast; ring
  have hnegI_ne : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  rw [hrew, cpow_ofReal_mul_of_pos h2q_pos hnegI_ne]
  have hreal_pow : ((2 / (q : ℝ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt 2 / Real.sqrt (q : ℝ) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow h2q_pos.le, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]
  have hnegI_pow : (-Complex.I : ℂ) ^ (1 / 2 : ℂ) = (1 - Complex.I) / (Real.sqrt 2 : ℂ) := by
    have hexp : (-Complex.I : ℂ) = Complex.exp (-(Real.pi : ℂ) / 2 * Complex.I) :=
      Complex.exp_neg_pi_div_two_mul_I.symm
    have hlog : Complex.log (-Complex.I) = -(Real.pi : ℂ) / 2 * Complex.I := by
      rw [hexp, Complex.log_exp]
      · simp
        linarith [Real.pi_pos]
      · simp
        linarith [Real.pi_pos]
    rw [Complex.cpow_def_of_ne_zero hnegI_ne, hlog]
    have harg :
        -(Real.pi : ℂ) / 2 * Complex.I * (1 / 2 : ℂ) =
          ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have hsq2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsq2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    push_cast
    field_simp [hsq2_ne]
    rw [show (Real.sqrt 2 : ℂ) ^ 2 = 2 by rw [sq]; exact hsq2]
    ring
  rw [hreal_pow, hnegI_pow]
  have hsq2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  push_cast
  field_simp [hsq2_ne, hsqrtC_ne]

/-- Helper: summability of `k ↦ cexp (-π * z * k^2)` over `ℤ` whenever `0 < z.re`. -/
private lemma summable_int_cexp_neg_pi_mul_sq {z : ℂ} (hz : 0 < z.re) :
    Summable (fun k : ℤ => Complex.exp (-(Real.pi : ℂ) * z * (k : ℂ) ^ 2)) := by
  set ρ : ℝ := Real.exp (-Real.pi * z.re)
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hbd : ∀ k : ℤ, ‖Complex.exp (-(Real.pi : ℂ) * z * (k : ℂ) ^ 2)‖ ≤ ρ ^ k.natAbs := by
    intro k
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hre : (-(Real.pi : ℂ) * z * (k : ℂ) ^ 2).re = -Real.pi * z.re * (k : ℝ) ^ 2 := by
      have hcast : (k : ℂ) ^ 2 = (((k : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, show -(Real.pi : ℂ) * z * (((k : ℝ) ^ 2 : ℝ) : ℂ) =
        (((-Real.pi * (k : ℝ) ^ 2 : ℝ) : ℂ)) * z by push_cast; ring, Complex.re_ofReal_mul]
      ring
    rw [hre]
    have hle : (k.natAbs : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hk_sq : (k : ℝ) ^ 2 = (k.natAbs : ℝ) ^ 2 := by
        rw [← Int.cast_natCast, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]
      rw [hk_sq]
      rcases Nat.eq_zero_or_pos k.natAbs with h0 | hpos
      · simp [h0]
      · have h1 : (1 : ℝ) ≤ (k.natAbs : ℝ) := Nat.one_le_cast.mpr hpos
        nlinarith
    have hfac : 0 < Real.pi * z.re := mul_pos Real.pi_pos hz
    nlinarith
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · exact Summable.of_norm_bounded (summable_geometric_of_lt_one hρ0.le hρ1) fun m => by
      simpa only [Int.natAbs_natCast] using hbd (m : ℤ)
  · exact Summable.of_norm_bounded (summable_geometric_of_lt_one hρ0.le hρ1) fun m => by
      have hm := hbd (-(m : ℤ))
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hm

/-- **Gauss's Exact Quadratic Gauss Sum Formula** (for EVERY positive integer `q ≥ 1`):
`∑_{r=0}^{q-1} e(r² / q) = ((1 + I) * (1 + (-I)^q) / 2) * √q`. -/
theorem quadratic_gaussSum_eq {q : ℕ} (hq : 0 < q) :
    ∑ r ∈ Finset.range q, e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ)) =
      ((1 + Complex.I) * (1 + (-Complex.I) ^ q) / 2) * (Real.sqrt (q : ℝ) : ℂ) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hqC_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  let ε : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  have hε_pos : ∀ n, 0 < ε n := fun n => inv_pos.mpr (by positivity)
  have hε_tend : Tendsto ε atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).comp (tendsto_add_atTop_nat 1)
  let a : ℕ → ℂ := fun n => (ε n : ℂ) - 2 * Complex.I / (q : ℂ)
  have ha_re : ∀ n, 0 < (a n).re := fun n => by
    dsimp only [a]
    have hre : (2 * Complex.I / (q : ℂ)).re = 0 := by
      rw [show (2 * Complex.I / (q : ℂ)) = (((2 / (q : ℝ) : ℝ) : ℂ)) * Complex.I by push_cast; ring]
      simp
    rw [Complex.sub_re, Complex.ofReal_re, hre, sub_zero]
    exact hε_pos n
  have ha_ne : ∀ n, a n ≠ 0 := fun n h0 => by
    have := ha_re n; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this
  -- Sequence `F n := √(ε n) * ∑' k : ℤ, cexp (-π * a n * k^2)`
  let F : ℕ → ℂ := fun n =>
    (Real.sqrt (ε n) : ℂ) * ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * a n * (k : ℂ) ^ 2)
  -- Step 1: Limit of `F n` directly by partitioning `k = q * m + r` (`0 ≤ r < q`)
  have hLHS_tend :
      Tendsto F atTop (nhds ((1 / (q : ℂ)) * ∑ r ∈ Finset.range q, e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ)))) := by
    -- Express `F n` as a finite sum over `r ∈ Finset.range q`
    have hF_eq : ∀ n : ℕ,
        F n =
          (1 / (q : ℂ)) * ∑ r ∈ Finset.range q,
            e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ)) *
              (((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
                ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) *
                  ((m : ℂ) + (((r : ℝ) / (q : ℝ) : ℝ) : ℂ)) ^ 2)) := by
      intro n
      have hterm_eq : ∀ (r : ℕ) (m : ℤ),
          Complex.exp (-(Real.pi : ℂ) * a n * (((q : ℤ) * m + (r : ℤ) : ℤ) : ℂ) ^ 2) =
            e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ)) *
              Complex.exp (-(Real.pi : ℂ) * ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) *
                ((m : ℂ) + (((r : ℝ) / (q : ℝ) : ℝ) : ℂ)) ^ 2) := by
        intro r m
        have hosc :
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ) *
                (((q : ℤ) * m + (r : ℤ) : ℤ) : ℂ) ^ 2) =
              e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ)) := by
          have hexp_split :
              2 * (Real.pi : ℂ) * Complex.I / (q : ℂ) * (((q : ℤ) * m + (r : ℤ) : ℤ) : ℂ) ^ 2 =
                ((q : ℤ) * m ^ 2 + 2 * m * (r : ℤ) : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) +
                  2 * (Real.pi : ℂ) * Complex.I * ((((r ^ 2 : ℕ) : ℝ) / (q : ℝ) : ℝ) : ℂ) := by
            push_cast
            field_simp [hqC_ne]
            ring
          rw [hexp_split, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
          rfl
        have hfull :
            -(Real.pi : ℂ) * a n * (((q : ℤ) * m + (r : ℤ) : ℤ) : ℂ) ^ 2 =
              2 * (Real.pi : ℂ) * Complex.I / (q : ℂ) * (((q : ℤ) * m + (r : ℤ) : ℤ) : ℂ) ^ 2 +
                (-(Real.pi : ℂ) * ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) *
                  ((m : ℂ) + (((r : ℝ) / (q : ℝ) : ℝ) : ℂ)) ^ 2) := by
          dsimp only [a]
          push_cast
          field_simp [hqC_ne]
          ring
        rw [hfull, Complex.exp_add, hosc]
      have hsumm_all : Summable (fun k : ℤ => Complex.exp (-(Real.pi : ℂ) * a n * (k : ℂ) ^ 2)) :=
        summable_int_cexp_neg_pi_mul_sq (ha_re n)
      -- Bijection `ℤ ≃ Fin q × ℤ` via Euclidean division by `q`
      let eDiv : ℤ ≃ Fin q × ℤ :=
        { toFun := fun k => (⟨(k % (q : ℤ)).toNat, by
            have hqZ : (0 : ℤ) < (q : ℤ) := Int.natCast_pos.mpr hq
            have h1 := Int.emod_nonneg k hqZ.ne'
            have h2 := Int.emod_lt_of_pos k hqZ
            omega⟩, k / (q : ℤ))
          invFun := fun p => (q : ℤ) * p.2 + (p.1.1 : ℤ)
          left_inv := fun k => by
            have hqZ : (0 : ℤ) < (q : ℤ) := Int.natCast_pos.mpr hq
            have h1 := Int.emod_nonneg k hqZ.ne'
            have h2 : ((k % (q : ℤ)).toNat : ℤ) = k % (q : ℤ) := Int.toNat_of_nonneg h1
            dsimp only
            rw [h2, Int.mul_ediv_add_emod]
          right_inv := fun p => by
            have hqZ : (0 : ℤ) < (q : ℤ) := Int.natCast_pos.mpr hq
            have hp1 : (0 : ℤ) ≤ (p.1.1 : ℤ) := Int.natCast_nonneg _
            have hp2 : (p.1.1 : ℤ) < (q : ℤ) := Int.ofNat_lt.mpr p.1.2
            ext
            · dsimp only
              rw [Int.mul_add_emod_self_left, Int.emod_eq_of_lt hp1 hp2]
              omega
            · dsimp only
              rw [Int.mul_add_ediv_left _ _ hqZ.ne', Int.ediv_eq_zero_of_lt hp1 hp2, add_zero] }
      have htsum_part :
          ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * a n * (k : ℂ) ^ 2) =
            ∑ r : Fin q, ∑' m : ℤ,
              Complex.exp (-(Real.pi : ℂ) * a n * (((q : ℤ) * m + (r.1 : ℤ) : ℤ) : ℂ) ^ 2) := by
        rw [← eDiv.symm.tsum_eq]
        have hsumm_prod :
            Summable (fun p : Fin q × ℤ =>
              Complex.exp (-(Real.pi : ℂ) * a n * (((q : ℤ) * p.2 + (p.1.1 : ℤ) : ℤ) : ℂ) ^ 2)) :=
          hsumm_all.comp_injective eDiv.symm.injective
        change ∑' p : Fin q × ℤ,
          Complex.exp (-(Real.pi : ℂ) * a n * (((q : ℤ) * p.2 + (p.1.1 : ℤ) : ℤ) : ℂ) ^ 2) = _
        rw [Summable.tsum_prod hsumm_prod, tsum_fintype]
      have hcpow_eq :
          ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (ε n) : ℂ) * (q : ℂ) := by
        have hnn : 0 ≤ ε n * (q : ℝ) ^ 2 := by positivity
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cpow hnn, ← Real.sqrt_eq_rpow,
          Real.sqrt_mul (hε_pos n).le, Real.sqrt_sq hq_pos.le]
        push_cast; rfl
      dsimp only [F]
      rw [htsum_part, Finset.sum_fin_eq_sum_range]
      have hrange :
          ∑ r ∈ Finset.range q,
              (if h : r < q then
                ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * a n * (((q : ℤ) * m + (r : ℤ) : ℤ) : ℂ) ^ 2)
              else 0) =
            ∑ r ∈ Finset.range q,
              e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ)) *
                ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) *
                  ((m : ℂ) + (((r : ℝ) / (q : ℝ) : ℝ) : ℂ)) ^ 2) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [dif_pos (Finset.mem_range.mp hr)]
        simp_rw [hterm_eq r, tsum_mul_left]
      rw [hrange, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hcpow_eq]
      field_simp [hqC_ne]
    have hF_fun : F = fun n : ℕ =>
        (1 / (q : ℂ)) * ∑ r ∈ Finset.range q,
          e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ)) *
            (((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) *
                ((m : ℂ) + (((r : ℝ) / (q : ℝ) : ℝ) : ℂ)) ^ 2)) := funext hF_eq
    rw [hF_fun]
    have hsum_tend :
        Tendsto
          (fun n : ℕ =>
            ∑ r ∈ Finset.range q,
              e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ)) *
                (((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
                  ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) *
                    ((m : ℂ) + (((r : ℝ) / (q : ℝ) : ℝ) : ℂ)) ^ 2)))
          atTop
          (nhds (∑ r ∈ Finset.range q, e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ)) * 1)) := by
      refine tendsto_finsetSum (Finset.range q) fun r _ => ?_
      refine Tendsto.const_mul (e (((r ^ 2 : ℕ) : ℝ) / (q : ℝ))) ?_
      refine tendsto_tsum_cexp_shift_one
        (c := fun n => ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ))
        (α := (r : ℝ) / (q : ℝ))
        (fun n => by simp only [Complex.ofReal_re]; positivity) ?_
      have hinv :
          (fun n : ℕ => ((((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ))⁻¹).re) =
            fun n : ℕ => ((q : ℝ) ^ 2)⁻¹ * ((n + 1 : ℕ) : ℝ) := by
        funext n
        rw [← Complex.ofReal_inv, Complex.ofReal_re]
        dsimp only [ε]
        field_simp [hq_pos.ne']
      rw [hinv]
      exact Tendsto.const_mul_atTop (inv_pos.mpr (sq_pos_of_pos hq_pos))
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    simp only [mul_one] at hsum_tend
    exact hsum_tend.const_mul (1 / (q : ℂ))
  -- Step 2: Limit of `F n` via `Complex.tsum_exp_neg_mul_int_sq` and splitting `k = 2m, 2m+1`
  have hRHS_tend :
      Tendsto F atTop
        (nhds (((1 + Complex.I) / (2 * (Real.sqrt (q : ℝ) : ℂ))) * (1 + (-Complex.I) ^ q))) := by
    let b : ℕ → ℂ := fun n => (-2 * Complex.I * (q : ℂ) * (ε n : ℂ)) / a n
    let u : ℕ → ℂ := fun n => (1 + Complex.I * (q : ℂ) * (ε n : ℂ) / 2)⁻¹
    have hu_den_ne : ∀ n, 1 + Complex.I * (q : ℂ) * (ε n : ℂ) / 2 ≠ 0 := by
      intro n h0
      have hre := congrArg Complex.re h0
      have him_part : (Complex.I * (q : ℂ) * (ε n : ℂ) / 2).re = 0 := by
        rw [show Complex.I * (q : ℂ) * (ε n : ℂ) / 2 =
          ((((q : ℝ) * ε n / 2 : ℝ) : ℂ)) * Complex.I by push_cast; ring]
        simp
      rw [Complex.add_re, Complex.one_re, him_part, add_zero, Complex.zero_re] at hre
      norm_num at hre
    have hu_ne : ∀ n, u n ≠ 0 := fun n => inv_ne_zero (hu_den_ne n)
    have hb_eq_u : ∀ n, b n = ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ) * u n := by
      intro n
      dsimp only [b, u]
      have hden : 1 + Complex.I * (q : ℂ) * (ε n : ℂ) / 2 ≠ 0 := hu_den_ne n
      have han : a n ≠ 0 := ha_ne n
      rw [div_eq_iff han, eq_comm, mul_right_comm ((ε n * (q : ℝ) ^ 2 : ℝ) : ℂ),
        mul_inv_eq_iff_eq_mul₀ hden]
      dsimp only [a]
      push_cast
      field_simp [hqC_ne]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hb_inv : ∀ n, (b n)⁻¹ = (((ε n * (q : ℝ) ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) + Complex.I / (2 * (q : ℂ)) := by
      intro n
      rw [hb_eq_u n, mul_inv]
      dsimp only [u]
      rw [inv_inv]
      have hεC_ne : (ε n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hε_pos n).ne'
      push_cast
      field_simp [hqC_ne, hεC_ne]
    have hb_inv_re : ∀ n, ((b n)⁻¹).re = ((q : ℝ) ^ 2)⁻¹ * ((n + 1 : ℕ) : ℝ) := by
      intro n
      rw [hb_inv n]
      have h0 : (Complex.I / (2 * (q : ℂ))).re = 0 := by
        rw [show Complex.I / (2 * (q : ℂ)) = (((1 / (2 * (q : ℝ)) : ℝ) : ℂ)) * Complex.I by push_cast; ring]
        simp
      rw [Complex.add_re, Complex.ofReal_re, h0, add_zero]
      dsimp only [ε]
      field_simp [hq_pos.ne']
    have hb_re : ∀ n, 0 < (b n).re := by
      intro n
      have hbinv_pos : 0 < ((b n)⁻¹).re := by rw [hb_inv_re n]; positivity
      have hb_ne : b n ≠ 0 := by
        rw [hb_eq_u n]
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (hu_ne n)
      have h1 : (b n).re = ((b n)⁻¹).re * Complex.normSq (b n) := by
        rw [Complex.inv_re, div_mul_cancel₀ _ (Complex.normSq_pos.mpr hb_ne).ne']
      rw [h1]
      exact mul_pos hbinv_pos (Complex.normSq_pos.mpr hb_ne)
    have h4_div_a : ∀ n, 4 / a n = b n + 2 * Complex.I * (q : ℂ) := by
      intro n
      have han : a n ≠ 0 := ha_ne n
      rw [div_eq_iff han]
      dsimp only [b]
      rw [add_mul, div_mul_cancel₀ _ han]
      dsimp only [a]
      field_simp [hqC_ne]
      ring_nf
      rw [Complex.I_sq]
      ring
    -- Express `F n` in terms of `a n`, `u n`, and the two shifted sums for `b n`
    have hF_rhs : ∀ n : ℕ,
        F n =
          (1 / ((a n) ^ (1 / 2 : ℂ) * (q : ℂ) * (u n) ^ (1 / 2 : ℂ))) *
            (((b n) ^ (1 / 2 : ℂ) *
                ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((0 : ℝ) : ℂ)) ^ 2)) +
              (-Complex.I) ^ q *
                ((b n) ^ (1 / 2 : ℂ) *
                  ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((1 / 2 : ℝ) : ℂ)) ^ 2))) := by
      intro n
      dsimp only [F]
      rw [Complex.tsum_exp_neg_mul_int_sq (ha_re n)]
      -- Split `∑' k : ℤ, cexp (-π / a n * k^2)` into even `2m` and odd `2m + 1`
      have hsumm_dual : Summable (fun k : ℤ => Complex.exp (-(Real.pi : ℂ) / a n * (k : ℂ) ^ 2)) := by
        have hre_pos : 0 < ((a n)⁻¹).re := by
          rw [Complex.inv_re]; exact div_pos (ha_re n) (Complex.normSq_pos.mpr (ha_ne n))
        have hs := summable_int_cexp_neg_pi_mul_sq hre_pos
        exact hs.congr fun k => by rw [div_eq_mul_inv]
      let ePar : ℤ ≃ Bool × ℤ :=
        { toFun := fun k => (decide (k % 2 = 1), k / 2)
          invFun := fun p => if p.1 then 2 * p.2 + 1 else 2 * p.2
          left_inv := fun k => by
            dsimp only
            by_cases h1 : k % 2 = 1
            · rw [decide_eq_true h1, if_pos rfl]; omega
            · rw [decide_eq_false h1, if_neg Bool.false_ne_true]; omega
          right_inv := fun p => by
            rcases p with ⟨b, m⟩
            cases b <;> ext <;> dsimp only
            · simp
            · omega
            · simp
            · omega }
      have hpar_split :
          ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) / a n * (k : ℂ) ^ 2) =
            (∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) / a n * ((2 * m : ℤ) : ℂ) ^ 2)) +
              ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) / a n * ((2 * m + 1 : ℤ) : ℂ) ^ 2) := by
        rw [← ePar.symm.tsum_eq]
        have hsp : Summable (fun p : Bool × ℤ =>
            Complex.exp (-(Real.pi : ℂ) / a n * ((ePar.symm p : ℤ) : ℂ) ^ 2)) :=
          hsumm_dual.comp_injective ePar.symm.injective
        rw [Summable.tsum_prod hsp, tsum_fintype]
        simp [ePar, add_comm]
      have heven_term : ∀ m : ℤ,
          Complex.exp (-(Real.pi : ℂ) / a n * ((2 * m : ℤ) : ℂ) ^ 2) =
            Complex.exp (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((0 : ℝ) : ℂ)) ^ 2) := by
        intro m
        have h1 :
            -(Real.pi : ℂ) / a n * ((2 * m : ℤ) : ℂ) ^ 2 =
              ((-(q : ℤ) * m ^ 2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
                (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((0 : ℝ) : ℂ)) ^ 2) := by
          have h4 := h4_div_a n
          push_cast
          calc -(Real.pi : ℂ) / a n * (2 * (m : ℂ)) ^ 2
              = -(Real.pi : ℂ) * (4 / a n) * (m : ℂ) ^ 2 := by ring
            _ = -(Real.pi : ℂ) * (b n + 2 * Complex.I * (q : ℂ)) * (m : ℂ) ^ 2 := by rw [h4]
            _ = -(q : ℂ) * (m : ℂ) ^ 2 * (2 * (Real.pi : ℂ) * Complex.I) +
                -(Real.pi : ℂ) * b n * ((m : ℂ) + 0) ^ 2 := by ring
        rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
      have hodd_term : ∀ m : ℤ,
          Complex.exp (-(Real.pi : ℂ) / a n * ((2 * m + 1 : ℤ) : ℂ) ^ 2) =
            (-Complex.I) ^ q *
              Complex.exp (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((1 / 2 : ℝ) : ℂ)) ^ 2) := by
        intro m
        have h1 :
            -(Real.pi : ℂ) / a n * ((2 * m + 1 : ℤ) : ℂ) ^ 2 =
              ((-(q : ℤ) * (m ^ 2 + m) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
                (q : ℂ) * (-(Real.pi : ℂ) / 2 * Complex.I) +
                (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((1 / 2 : ℝ) : ℂ)) ^ 2) := by
          have h4 := h4_div_a n
          push_cast
          calc -(Real.pi : ℂ) / a n * (2 * (m : ℂ) + 1) ^ 2
              = -(Real.pi : ℂ) * (4 / a n) * ((m : ℂ) + 1 / 2) ^ 2 := by ring
            _ = -(Real.pi : ℂ) * (b n + 2 * Complex.I * (q : ℂ)) * ((m : ℂ) + 1 / 2) ^ 2 := by rw [h4]
            _ = -(q : ℂ) * ((m : ℂ) ^ 2 + (m : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) +
                (q : ℂ) * (-(Real.pi : ℂ) / 2 * Complex.I) +
                -(Real.pi : ℂ) * b n * ((m : ℂ) + 1 / 2) ^ 2 := by ring
        rw [h1, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
          Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]
      rw [hpar_split]
      simp_rw [heven_term, hodd_term, tsum_mul_left]
      have hb_pow :
          (b n) ^ (1 / 2 : ℂ) = (Real.sqrt (ε n) : ℂ) * (q : ℂ) * (u n) ^ (1 / 2 : ℂ) := by
        rw [hb_eq_u n, cpow_ofReal_mul_of_pos (by positivity) (hu_ne n)]
        congr 1
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow,
          Real.sqrt_mul (hε_pos n).le, Real.sqrt_sq hq_pos.le]
        push_cast; rfl
      have hsqrt_ε_ne : (Real.sqrt (ε n) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hε_pos n)).ne'
      have ha_pow_ne : (a n) ^ (1 / 2 : ℂ) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (ha_ne n)]; exact Complex.exp_ne_zero _
      have hu_pow_ne : (u n) ^ (1 / 2 : ℂ) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (hu_ne n)]; exact Complex.exp_ne_zero _
      rw [hb_pow]
      field_simp [hqC_ne, hsqrt_ε_ne, ha_pow_ne, hu_pow_ne]
    have hF_fun2 : F = fun n : ℕ =>
        (1 / ((a n) ^ (1 / 2 : ℂ) * (q : ℂ) * (u n) ^ (1 / 2 : ℂ))) *
          (((b n) ^ (1 / 2 : ℂ) *
              ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((0 : ℝ) : ℂ)) ^ 2)) +
            (-Complex.I) ^ q *
              ((b n) ^ (1 / 2 : ℂ) *
                ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((1 / 2 : ℝ) : ℂ)) ^ 2))) :=
      funext hF_rhs
    rw [hF_fun2]
    have hbinv_tend : Tendsto (fun n => ((b n)⁻¹).re) atTop atTop := by
      simp_rw [hb_inv_re]
      exact Tendsto.const_mul_atTop (inv_pos.mpr (sq_pos_of_pos hq_pos))
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    have hsum0 := tendsto_tsum_cexp_shift_one (α := 0) hb_re hbinv_tend
    have hsum1 := tendsto_tsum_cexp_shift_one (α := 1 / 2) hb_re hbinv_tend
    have hbrack :
        Tendsto
          (fun n =>
            ((b n) ^ (1 / 2 : ℂ) *
                ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((0 : ℝ) : ℂ)) ^ 2)) +
              (-Complex.I) ^ q *
                ((b n) ^ (1 / 2 : ℂ) *
                  ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) * b n * ((m : ℂ) + ((1 / 2 : ℝ) : ℂ)) ^ 2)))
          atTop (nhds (1 + (-Complex.I) ^ q)) := by
      simpa only [mul_one] using hsum0.add (hsum1.const_mul ((-Complex.I) ^ q))
    -- Limits of `a n ^ (1/2)` and `u n ^ (1/2)`
    have ha_tend : Tendsto a atTop (nhds (-(2 : ℂ) * Complex.I / (q : ℂ))) := by
      have h1 : Tendsto (fun n => (ε n : ℂ)) atTop (nhds 0) := by
        simpa only [Complex.ofReal_zero, Function.comp_def] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp hε_tend
      have h2 := h1.sub_const (2 * Complex.I / (q : ℂ))
      simpa only [a, zero_sub, neg_div, neg_mul] using h2
    have ha_slit : -(2 : ℂ) * Complex.I / (q : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      have him : (-(2 : ℂ) * Complex.I / (q : ℂ)).im = -(2 / (q : ℝ)) := by
        rw [show -(2 : ℂ) * Complex.I / (q : ℂ) = (((-(2 / (q : ℝ)) : ℝ) : ℂ)) * Complex.I by push_cast; ring]
        simp
      rw [him]
      exact (neg_lt_zero.mpr (div_pos (by norm_num) hq_pos)).ne
    have ha_pow_tend :
        Tendsto (fun n => (a n) ^ (1 / 2 : ℂ)) atTop
          (nhds ((1 - Complex.I) / (Real.sqrt (q : ℝ) : ℂ))) := by
      rw [← neg_two_mul_I_div_cpow_half hq]
      exact (continuousAt_cpow_const ha_slit).tendsto.comp ha_tend
    have hu_tend : Tendsto u atTop (nhds 1) := by
      have hεC : Tendsto (fun n => (ε n : ℂ)) atTop (nhds 0) := by
        simpa only [Complex.ofReal_zero, Function.comp_def] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp hε_tend
      have hden : Tendsto (fun n => 1 + Complex.I * (q : ℂ) * (ε n : ℂ) / 2) atTop (nhds 1) := by
        have hmul := (hεC.const_mul (Complex.I * (q : ℂ) / 2)).const_add (1 : ℂ)
        simpa only [mul_zero, add_zero] using hmul.congr fun n => by ring
      simpa only [inv_one] using hden.inv₀ one_ne_zero
    have hu_pow_tend : Tendsto (fun n => (u n) ^ (1 / 2 : ℂ)) atTop (nhds 1) := by
      have h1slit : (1 : ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
      simpa only [Complex.one_cpow, Function.comp_def] using
        (continuousAt_cpow_const h1slit).tendsto.comp hu_tend
    have hdenom_tend :
        Tendsto (fun n => (a n) ^ (1 / 2 : ℂ) * (q : ℂ) * (u n) ^ (1 / 2 : ℂ)) atTop
          (nhds (((1 - Complex.I) / (Real.sqrt (q : ℝ) : ℂ)) * (q : ℂ) * 1)) :=
      (ha_pow_tend.mul_const (q : ℂ)).mul hu_pow_tend
    have hdenom_ne : ((1 - Complex.I) / (Real.sqrt (q : ℝ) : ℂ)) * (q : ℂ) * 1 ≠ 0 := by
      have h1mI : (1 - Complex.I : ℂ) ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0; simp at this
      have hsqrtC_ne : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsqrt_pos.ne'
      exact mul_ne_zero (mul_ne_zero (div_ne_zero h1mI hsqrtC_ne) hqC_ne) one_ne_zero
    have hpref_tend :
        Tendsto (fun n => 1 / ((a n) ^ (1 / 2 : ℂ) * (q : ℂ) * (u n) ^ (1 / 2 : ℂ))) atTop
          (nhds ((1 + Complex.I) / (2 * (Real.sqrt (q : ℝ) : ℂ)))) := by
      have h1 := (tendsto_const_nhds (x := (1 : ℂ))).div hdenom_tend hdenom_ne
      have hval :
          1 / (((1 - Complex.I) / (Real.sqrt (q : ℝ) : ℂ)) * (q : ℂ) * 1) =
            (1 + Complex.I) / (2 * (Real.sqrt (q : ℝ) : ℂ)) := by
        have hsqrtC_ne : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsqrt_pos.ne'
        have h1mI : (1 - Complex.I : ℂ) ≠ 0 := fun h0 => by
          have := congrArg Complex.re h0; simp at this
        have hsqC : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
          rw [sq]; exact_mod_cast Real.mul_self_sqrt hq_pos.le
        field_simp [hqC_ne, hsqrtC_ne, h1mI]
        calc (Real.sqrt (q : ℝ) : ℂ) ^ 2 * 2
            = (q : ℂ) * 2 := by rw [hsqC]
          _ = (q : ℂ) * ((1 - Complex.I) * (1 + Complex.I)) := by
              rw [show (1 - Complex.I) * (1 + Complex.I) = (1 - Complex.I ^ 2 : ℂ) by ring,
                Complex.I_sq]; ring
          _ = (1 - Complex.I) * (q : ℂ) * (1 + Complex.I) := by ring
      rw [hval] at h1
      exact h1.congr fun _ => rfl
    exact hpref_tend.mul hbrack
  -- Equate the two limits of `F n`
  have heq := tendsto_nhds_unique hLHS_tend hRHS_tend
  have hmul := congrArg ((q : ℂ) * ·) heq
  rw [← mul_assoc, mul_one_div_cancel hqC_ne, one_mul] at hmul
  rw [hmul]
  have hsqrtC_ne : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsqrt_pos.ne'
  have hsqC : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    rw [sq]; exact_mod_cast Real.mul_self_sqrt hq_pos.le
  field_simp [hsqrtC_ne]
  rw [← hsqC]
  ring

/-- For an odd prime `p` and any real non-principal character `χ : DirichletCharacter ℂ p`,
the Gauss sum equals the quadratic exponential sum `∑_{x=0}^{p-1} e(x² / p)`. -/
theorem gaussSum_eq_quadratic_sum_of_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (hreal : ∀ a : ZMod p, (χ a).im = 0) :
    gaussSum χ ZMod.stdAddChar =
      ∑ r ∈ Finset.range p, e (((r ^ 2 : ℕ) : ℝ) / (p : ℝ)) := by
  have hp_prime : p.Prime := Fact.out
  have hp_pos : 0 < p := hp_prime.pos
  -- On `(ZMod p)ˣ`, `χ` takes values in `{1, -1}`
  have hχ_sq : ∀ u : (ZMod p)ˣ, χ (u : ZMod p) = 1 ∨ χ (u : ZMod p) = -1 := by
    intro u
    have hnorm : ‖χ (u : ZMod p)‖ = 1 :=
      (Stage2BehrendSieve.dirichlet_norm_eq_one_and_conj χ u.isUnit).1
    have him : (χ (u : ZMod p)).im = 0 := hreal _
    have hsq : (χ (u : ZMod p)).re ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq (χ (u : ZMod p))
      rw [hnorm, one_pow, Complex.normSq_apply, him] at h
      nlinarith
    rcases sq_eq_one_iff.mp hsq with h1 | hm1
    · left; exact Complex.ext (by simpa using h1) (by simpa using him)
    · right; exact Complex.ext (by simpa using hm1) (by simpa using him)
  -- For every `a : ZMod p`, `#{x : ZMod p | x^2 = a} = 1 + χ(a)`
  have hfib_card : ∀ a : ZMod p,
      ((Finset.univ.filter fun x : ZMod p => x ^ 2 = a).card : ℂ) = 1 + χ a := by
    intro a
    by_cases ha0 : a = 0
    · subst ha0
      have hfilt : Finset.univ.filter (fun x : ZMod p => x ^ 2 = (0 : ZMod p)) = {0} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          sq_eq_zero_iff]
      rw [hfilt, Finset.card_singleton, Nat.cast_one, χ.map_zero' hp_prime.ne_one, add_zero]
    · have ha_unit : IsUnit a := isUnit_iff_ne_zero.mpr ha0
      -- Show `a` is a nonzero square iff `χ a = 1`
      -- Compare cardinalities of `ker(χ|_units)` and `im(sq|_units)`:
      let sqHom : (ZMod p)ˣ →* (ZMod p)ˣ :=
        { toFun := fun u => u ^ 2
          map_one' := one_pow 2
          map_mul' := fun u v => mul_pow u v 2 }
      let χHom : (ZMod p)ˣ →* ℂˣ :=
        { toFun := fun u => Units.mk0 (χ (u : ZMod p)) (by
            rcases hχ_sq u with h1 | hm1
            · simp [h1]
            · simp [hm1])
          map_one' := Units.ext (by simp)
          map_mul' := fun u v => Units.ext (by simp [map_mul]) }
      have hsub : sqHom.range ≤ χHom.ker := by
        rintro _ ⟨u, rfl⟩
        rw [MonoidHom.mem_ker]
        apply Units.ext
        change χ ((u : ZMod p) ^ 2) = 1
        rw [map_pow]
        rcases hχ_sq u with h1 | hm1
        · simp [h1]
        · simp [hm1]
      have hker_sq_card : Fintype.card sqHom.ker = 2 := by
        have hker_eq : (Finset.univ.filter fun u : (ZMod p)ˣ => u ^ 2 = 1) = {1, -1} := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · intro h
            have hv : (u : ZMod p) ^ 2 = 1 := by simpa using congrArg Units.val h
            rcases sq_eq_one_iff.mp hv with h1 | hm1
            · left; exact Units.ext h1
            · right; exact Units.ext hm1
          · rintro (rfl | rfl) <;> simp
        have h1ne : (1 : (ZMod p)ˣ) ≠ -1 := by
          intro h
          have hv : (1 : ZMod p) = -1 := congrArg Units.val h
          have h20 : (2 : ZMod p) = 0 := by linear_combination hv
          have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
          exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp_prime.two_le)
        calc Fintype.card sqHom.ker
            = (Finset.univ.filter fun u : (ZMod p)ˣ => u ^ 2 = 1).card := by
              rw [← Fintype.card_coe]
              refine Fintype.card_congr
                { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
                  invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
                  left_inv := fun _ => rfl
                  right_inv := fun _ => rfl }
          _ = ({(1 : (ZMod p)ˣ), -1} : Finset (ZMod p)ˣ).card := by rw [hker_eq]
          _ = 2 := Finset.card_pair h1ne
      have hrange_sq_card : Fintype.card sqHom.range * 2 = Fintype.card (ZMod p)ˣ := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup sqHom.ker
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          hker_sq_card] at h
        have hq := Fintype.card_congr (QuotientGroup.quotientKerEquivRange sqHom).toEquiv
        rw [← hq, ← h]
      have hker_χ_ne_top : χHom.ker ≠ ⊤ := by
        intro htop
        apply hχ
        ext u
        have hmem : u ∈ χHom.ker := by rw [htop]; trivial
        have hv := congrArg Units.val hmem
        simpa [χHom, MulChar.one_apply u.isUnit] using hv
      have hker_χ_card : Fintype.card χHom.ker < Fintype.card (ZMod p)ˣ := by
        by_contra hge
        push Not at hge
        apply hker_χ_ne_top
        rw [eq_top_iff]
        intro u _
        have hcard_eq : (Finset.univ.filter fun v : (ZMod p)ˣ => v ∈ χHom.ker).card =
            (Finset.univ : Finset (ZMod p)ˣ).card := by
          have h1 : (Finset.univ.filter fun v : (ZMod p)ˣ => v ∈ χHom.ker).card =
              Fintype.card χHom.ker := by
            rw [← Fintype.card_coe]
            exact (Fintype.card_congr
              { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
                invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl }).symm
          have hle := Finset.card_le_card (Finset.filter_subset (fun v : (ZMod p)ˣ => v ∈ χHom.ker) Finset.univ)
          rw [Finset.card_univ] at hle ⊢
          omega
        have hall := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcard_eq.ge
        have hu_mem : u ∈ Finset.univ.filter (fun v : (ZMod p)ˣ => v ∈ χHom.ker) := by
          rw [hall]; exact Finset.mem_univ u
        exact (Finset.mem_filter.mp hu_mem).2
      have hrange_eq_ker : sqHom.range = χHom.ker := by
        have hdvd1 : Fintype.card sqHom.range ∣ Fintype.card χHom.ker := by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
          exact Subgroup.card_dvd_of_le hsub
        have hdvd2 : Fintype.card χHom.ker ∣ Fintype.card (ZMod p)ˣ := by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
          exact Subgroup.card_subgroup_dvd_card χHom.ker
        obtain ⟨k, hk⟩ := hdvd1
        obtain ⟨m, hm⟩ := hdvd2
        have hprod : Fintype.card sqHom.range * (k * m) = Fintype.card sqHom.range * 2 := by
          calc Fintype.card sqHom.range * (k * m)
              = (Fintype.card sqHom.range * k) * m := by ring
            _ = Fintype.card χHom.ker * m := by rw [← hk]
            _ = Fintype.card (ZMod p)ˣ := hm.symm
            _ = Fintype.card sqHom.range * 2 := hrange_sq_card.symm
        have hpos_r : 0 < Fintype.card sqHom.range := Fintype.card_pos
        have hkm : k * m = 2 := Nat.eq_of_mul_eq_mul_left hpos_r hprod
        have hm_ne1 : m ≠ 1 := by
          intro hm1; rw [hm1, mul_one] at hm; omega
        have hk1 : k = 1 := by
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp ⟨m, hkm.symm⟩ with rfl | rfl
          · rfl
          · exfalso; exact hm_ne1 (by omega)
        have hcard_eq : Fintype.card sqHom.range = Fintype.card χHom.ker := by
          rw [hk, hk1, mul_one]
        exact Subgroup.eq_of_le_of_card_ge hsub (by
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; exact hcard_eq.ge)
      -- Now evaluate both sides for `a = ha_unit.unit`
      rcases hχ_sq ha_unit.unit with h1 | hm1
      · have hmem : ha_unit.unit ∈ sqHom.range := by
          rw [hrange_eq_ker, MonoidHom.mem_ker]
          apply Units.ext
          simpa [χHom] using h1
        obtain ⟨u0, hu0⟩ := hmem
        have hu0_sq : (u0 : ZMod p) ^ 2 = a := by
          have := congrArg Units.val hu0
          simpa [sqHom] using this
        have hfilt : Finset.univ.filter (fun x : ZMod p => x ^ 2 = a) = {(u0 : ZMod p), -(u0 : ZMod p)} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          rw [← hu0_sq, sq_eq_sq_iff_eq_or_eq_neg]
        have hne : (u0 : ZMod p) ≠ -(u0 : ZMod p) := by
          intro heq
          have h2u : (2 : ZMod p) * (u0 : ZMod p) = 0 := by linear_combination heq
          have h20 : (2 : ZMod p) = 0 := (mul_eq_zero.mp h2u).resolve_right u0.ne_zero
          have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
          exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp_prime.two_le)
        rw [hfilt, Finset.card_pair hne, Nat.cast_ofNat]
        have ha1 : χ a = 1 := by simpa using h1
        rw [ha1]; norm_num
      · have hnotmem : ha_unit.unit ∉ sqHom.range := by
          rw [hrange_eq_ker, MonoidHom.mem_ker]
          intro hker
          have hv := congrArg Units.val hker
          have h1 : χ a = 1 := by simpa [χHom] using hv
          have hm1' : χ a = -1 := by simpa using hm1
          rw [h1] at hm1'
          norm_num at hm1'
        have hfilt : Finset.univ.filter (fun x : ZMod p => x ^ 2 = a) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x _ hx
          have hx_ne : x ≠ 0 := fun h0 => ha0 (by rw [← hx, h0]; simp)
          have hx_unit : IsUnit x := isUnit_iff_ne_zero.mpr hx_ne
          apply hnotmem
          refine ⟨hx_unit.unit, Units.ext ?_⟩
          simpa [sqHom] using hx
        rw [hfilt, Finset.card_empty, Nat.cast_zero]
        have ham1 : χ a = -1 := by simpa using hm1
        rw [ham1]; ring
  -- Sum `(1 + χ a) * stdAddChar a` over `a : ZMod p`
  have hsum_sq :
      ∑ x : ZMod p, ZMod.stdAddChar (x ^ 2) = gaussSum χ ZMod.stdAddChar := by
    have hfib :
        ∑ x : ZMod p, ZMod.stdAddChar (x ^ 2) =
          ∑ a : ZMod p, ((Finset.univ.filter fun x : ZMod p => x ^ 2 = a).card : ℂ) *
            ZMod.stdAddChar a := by
      have h1 := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (ZMod p)))
        (t := (Finset.univ : Finset (ZMod p))) (g := fun x : ZMod p => x ^ 2)
        (f := fun x : ZMod p => ZMod.stdAddChar (x ^ 2)) (fun _ _ => Finset.mem_univ _)
      rw [← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hcongr :
          ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = a), ZMod.stdAddChar (x ^ 2) =
            ∑ _x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = a), ZMod.stdAddChar a :=
        Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]
      rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    rw [hfib]
    simp_rw [hfib_card, add_mul, one_mul, Finset.sum_add_distrib]
    have h0 : ∑ a : ZMod p, ZMod.stdAddChar a = 0 := by
      have h := sum_stdAddChar_mul (q := p) (1 : ZMod p)
      have h1ne : (1 : ZMod p) ≠ 0 := one_ne_zero
      simpa only [mul_one, if_neg h1ne] using h
    rw [h0, zero_add]
    rfl
  rw [← hsum_sq]
  refine Finset.sum_bij (fun (a : ZMod p) _ => a.val) ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a₁ _ a₂ _ h
    rw [← ZMod.natCast_zmod_val a₁, ← ZMod.natCast_zmod_val a₂, h]
  · intro r hr
    exact ⟨(r : ZMod p), Finset.mem_univ _, by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]⟩
  · intro a _
    have hcast : a ^ 2 = ((a.val ^ 2 : ℕ) : ZMod p) := by
      rw [Nat.cast_pow, ZMod.natCast_zmod_val]
    rw [hcast, stdAddChar_natCast_eq_e]

/-- **Exact Gauss Sum of the Quadratic Character mod an Odd Prime `p`**:
- `p % 4 = 1`: `τ(χ) = +√p`,
- `p % 4 = 3`: `τ(χ) = +I * √p`. -/
theorem gaussSum_prime_real_char {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (hreal : ∀ a : ZMod p, (χ a).im = 0) :
    gaussSum χ ZMod.stdAddChar =
      (if p % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt (p : ℝ) : ℂ) := by
  have hp_prime : p.Prime := Fact.out
  obtain ⟨k_odd, hk_odd⟩ := hp_prime.odd_of_ne_two hp2
  have hp_odd : p % 2 = 1 := by omega
  rw [gaussSum_eq_quadratic_sum_of_prime hp2 hχ hreal, quadratic_gaussSum_eq hp_prime.pos]
  congr 1
  have hpow4 : (-Complex.I : ℂ) ^ 4 = 1 := by
    calc (-Complex.I : ℂ) ^ 4 = ((-Complex.I) ^ 2) ^ 2 := by ring
      _ = (-1 : ℂ) ^ 2 := by rw [neg_sq, Complex.I_sq]
      _ = 1 := by norm_num
  have hpow_mod : (-Complex.I : ℂ) ^ p = (-Complex.I) ^ (p % 4) := by
    conv_lhs => rw [← Nat.div_add_mod p 4]
    rw [pow_add, pow_mul, hpow4, one_pow, one_mul]
  rw [hpow_mod]
  have hcases : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases hcases with h1 | h3
  · rw [if_pos h1, h1, pow_one]
    have h12 : (1 + Complex.I) * (1 + -Complex.I) = 2 := by
      calc (1 + Complex.I) * (1 + -Complex.I) = 1 - Complex.I ^ 2 := by ring
        _ = 1 - (-1) := by rw [Complex.I_sq]
        _ = 2 := by norm_num
    rw [h12, div_self (by norm_num : (2 : ℂ) ≠ 0)]
  · rw [if_neg (by omega), h3]
    have hnegI3 : (-Complex.I : ℂ) ^ 3 = Complex.I := by
      calc (-Complex.I : ℂ) ^ 3 = (-Complex.I) ^ 2 * (-Complex.I) := by ring
        _ = (-1) * (-Complex.I) := by rw [neg_sq, Complex.I_sq]
        _ = Complex.I := by ring
    rw [hnegI3]
    have h12 : (1 + Complex.I) * (1 + Complex.I) = 2 * Complex.I := by
      calc (1 + Complex.I) * (1 + Complex.I) = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
        _ = 1 + 2 * Complex.I + (-1) := by rw [Complex.I_sq]
        _ = 2 * Complex.I := by ring
    rw [h12]
    ring

/-- Any non-principal character of prime modulus `p` is automatically primitive. -/
theorem isPrimitive_of_prime_of_ne_one {p : ℕ} [Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) : χ.IsPrimitive := by
  have hp_prime : p.Prime := Fact.out
  show χ.conductor = p
  have hdvd : χ.conductor ∣ p := χ.conductor_dvd_level
  rcases (Nat.dvd_prime hp_prime).mp hdvd with h1 | hp
  · exfalso; exact hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h1)
  · exact hp

/-- **UNCONDITIONAL DIRICHLET NON-VANISHING SIGN THEOREM FOR PRIMES `p ≡ 3 [MOD 4]`**:
for EVERY prime `p ≡ 3 [MOD 4]` and the real non-principal (quadratic) character `χ mod p`:
1. `χ` is odd (`χ.Odd`) and primitive (`χ.IsPrimitive`), with `τ(χ) = I * √p`,
2. `(LFunction χ 1).re = -(π / (p * √p)) * ∑_{a=1}^{p-1} a * (χ a).re`,
3. **`∑_{a=1}^{p-1} a * (χ a).re < 0`**,
4. **Dirichlet's Quadratic Residue Excess Theorem**:
   **`0 < ∑_{a=1}^{(p-1)/2} (χ a).re`** (strictly more quadratic residues than non-residues
   in `(0, p / 2)`!)! -/
theorem dirichlet_sign_theorem_prime_three_mod_four {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3)
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (hreal : ∀ a : ZMod p, (χ a).im = 0) :
    χ.Odd ∧
      gaussSum χ ZMod.stdAddChar = Complex.I * (Real.sqrt (p : ℝ) : ℂ) ∧
      ∑ a ∈ Finset.Ico 1 p, (a : ℝ) * (χ (a : ZMod p)).re < 0 ∧
      0 < ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), (χ (a : ZMod p)).re := by
  have hp_prime : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hprim : χ.IsPrimitive := isPrimitive_of_prime_of_ne_one hχ
  have hgauss : gaussSum χ ZMod.stdAddChar = Complex.I * (Real.sqrt (p : ℝ) : ℂ) := by
    have h := gaussSum_prime_real_char hp2 hχ hreal
    rwa [if_neg (by omega)] at h
  have hodd : χ.Odd := by
    show χ (-1 : ZMod p) = -1
    have hconj := conj_gaussSum_eq χ
    rw [dirichletChar_inv_eq_self_of_real hreal, hgauss] at hconj
    have hstar : starRingEnd ℂ (Complex.I * (Real.sqrt (p : ℝ) : ℂ)) =
        (-1 : ℂ) * (Complex.I * (Real.sqrt (p : ℝ) : ℂ)) := by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [hstar] at hconj
    have hne : Complex.I * (Real.sqrt (p : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp_prime.pos)).ne')
    exact mul_right_cancel₀ hne hconj.symm
  have hneg : ∑ a ∈ Finset.Ico 1 p, (a : ℝ) * (χ (a : ZMod p)).re < 0 :=
    sum_mul_odd_real_char_neg_of_gaussSum hprim hχ hodd hreal hgauss
  -- Deduce `0 < ∑_{a=1}^{(p-1)/2} (χ a).re` via the exact identity
  -- `(2 - (χ 2).re) * (-∑_{a=1}^{p-1} a * (χ a).re) = p * ∑_{a=1}^{(p-1)/2} (χ a).re`
  have hhalf_pos : 0 < ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), (χ (a : ZMod p)).re := by
    set m : ℕ := (p - 1) / 2
    have hp_eq : p = 2 * m + 1 := by omega
    have h2_unit : IsUnit (2 : ZMod p) :=
      (ZMod.isUnit_iff_coprime 2 p).mpr ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by omega))
    have hχ2_sq : (χ (2 : ZMod p)).re ^ 2 = 1 := by
      have hnorm := (Stage2BehrendSieve.dirichlet_norm_eq_one_and_conj χ h2_unit).1
      have h := Complex.normSq_eq_norm_sq (χ (2 : ZMod p))
      rw [hnorm, one_pow, Complex.normSq_apply, hreal _] at h
      nlinarith
    have hχ2_le : (χ (2 : ZMod p)).re ≤ 1 := by nlinarith
    have h2sub_pos : 0 < 2 - (χ (2 : ZMod p)).re := by linarith
    have hχ_real_mul : ∀ a b : ZMod p, (χ (a * b)).re = (χ a).re * (χ b).re := by
      intro a b
      rw [map_mul, Complex.mul_re, hreal a, hreal b, mul_zero, sub_zero]
    -- Bijection `a ↦ (2 * a) % p` on `Ico 1 p`
    have hbij :
        ∑ a ∈ Finset.Ico 1 p, (((2 * a) % p : ℕ) : ℝ) * (χ (((2 * a) % p : ℕ) : ZMod p)).re =
          ∑ b ∈ Finset.Ico 1 p, (b : ℝ) * (χ (b : ZMod p)).re := by
      refine Finset.sum_bij (fun a _ => (2 * a) % p) ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_Ico] at ha ⊢
        refine ⟨?_, Nat.mod_lt _ hp_prime.pos⟩
        by_contra h0
        have hmod0 : (2 * a) % p = 0 := by omega
        have hdvd : p ∣ 2 * a := Nat.dvd_of_mod_eq_zero hmod0
        have hdvd_a : p ∣ a := (hp_prime.dvd_mul.mp hdvd).resolve_left (fun h => hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) hp_prime.two_le))
        have hle := Nat.le_of_dvd (by omega) hdvd_a
        omega
      · intro a₁ ha₁ a₂ ha₂ h
        simp only [Finset.mem_Ico] at ha₁ ha₂
        have hcast : ((2 * a₁ : ℕ) : ZMod p) = ((2 * a₂ : ℕ) : ZMod p) :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
        rw [Nat.cast_mul, Nat.cast_mul] at hcast
        have h2ne : (2 : ZMod p) ≠ 0 := h2_unit.ne_zero
        have heq : (a₁ : ZMod p) = (a₂ : ZMod p) := mul_left_cancel₀ h2ne hcast
        have hv := congrArg ZMod.val heq
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha₁.2, Nat.mod_eq_of_lt ha₂.2] at hv
      · intro b hb
        simp only [Finset.mem_Ico] at hb
        by_cases hpar : b % 2 = 0
        · refine ⟨b / 2, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
          have h2a : 2 * (b / 2) = b := by omega
          rw [h2a, Nat.mod_eq_of_lt hb.2]
        · refine ⟨(b + p) / 2, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
          have h2a : 2 * ((b + p) / 2) = b + p := by omega
          rw [h2a, Nat.add_mod_right, Nat.mod_eq_of_lt hb.2]
      · intro _ _; rfl
    -- Split `Ico 1 p = Icc 1 m ∪ Ioo m p`
    have hsplit : Finset.Ico 1 p = Finset.Icc 1 m ∪ Finset.Ioo m p := by
      ext a; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioo]; omega
    have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Ioo m p) := by
      rw [Finset.disjoint_left]
      intro a h1 h2; simp only [Finset.mem_Icc, Finset.mem_Ioo] at h1 h2; omega
    have hmod_left :
        ∑ a ∈ Finset.Icc 1 m, (((2 * a) % p : ℕ) : ℝ) * (χ (((2 * a) % p : ℕ) : ZMod p)).re =
          (χ (2 : ZMod p)).re * ∑ a ∈ Finset.Icc 1 m, (2 * (a : ℝ)) * (χ (a : ZMod p)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' := Finset.mem_Icc.mp ha
      have hmod : (2 * a) % p = 2 * a := Nat.mod_eq_of_lt (by omega)
      rw [hmod, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat, hχ_real_mul]
      ring
    have hmod_right :
        ∑ a ∈ Finset.Ioo m p, (((2 * a) % p : ℕ) : ℝ) * (χ (((2 * a) % p : ℕ) : ZMod p)).re =
          (χ (2 : ZMod p)).re * ∑ a ∈ Finset.Ioo m p, (2 * (a : ℝ) - (p : ℝ)) * (χ (a : ZMod p)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' := Finset.mem_Ioo.mp ha
      have hmod : (2 * a) % p = 2 * a - p := by
        have h1 : 2 * a = (2 * a - p) + p := by omega
        conv_lhs => rw [h1]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hcast_mod : (((2 * a - p : ℕ) : ZMod p)) = (2 : ZMod p) * (a : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, sub_zero, Nat.cast_mul, Nat.cast_ofNat]
      rw [hmod, hcast_mod, hχ_real_mul, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hsum_top_eq_neg_bot :
        ∑ a ∈ Finset.Ioo m p, (χ (a : ZMod p)).re = -∑ a ∈ Finset.Icc 1 m, (χ (a : ZMod p)).re := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_bij (fun a _ => p - a) ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_Ioo] at ha; simp only [Finset.mem_Icc]; omega
      · intro a₁ ha₁ a₂ ha₂ h; simp only [Finset.mem_Ioo] at ha₁ ha₂; omega
      · intro b hb; simp only [Finset.mem_Icc] at hb
        exact ⟨p - b, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro a ha
        have ha' := Finset.mem_Ioo.mp ha
        have hcast : ((p - a : ℕ) : ZMod p) = (-1 : ZMod p) * (a : ZMod p) := by
          rw [Nat.cast_sub ha'.2.le, ZMod.natCast_self, zero_sub, neg_one_mul]
        rw [hcast, hχ_real_mul, show (χ (-1 : ZMod p)).re = -1 by rw [hodd]; simp]
        ring
    have hcomb :
        ∑ b ∈ Finset.Ico 1 p, (b : ℝ) * (χ (b : ZMod p)).re =
          (χ (2 : ZMod p)).re *
            (2 * (∑ a ∈ Finset.Ico 1 p, (a : ℝ) * (χ (a : ZMod p)).re) +
              (p : ℝ) * ∑ a ∈ Finset.Icc 1 m, (χ (a : ZMod p)).re) := by
      conv_lhs => rw [← hbij, hsplit, Finset.sum_union hdisj, hmod_left, hmod_right, ← mul_add]
      congr 1
      rw [hsplit, Finset.sum_union hdisj]
      have hL1 : ∑ a ∈ Finset.Icc 1 m, (2 * (a : ℝ)) * (χ (a : ZMod p)).re =
          2 * ∑ a ∈ Finset.Icc 1 m, (a : ℝ) * (χ (a : ZMod p)).re := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
      have hR1 :
          ∑ a ∈ Finset.Ioo m p, (2 * (a : ℝ) - (p : ℝ)) * (χ (a : ZMod p)).re =
            2 * (∑ a ∈ Finset.Ioo m p, (a : ℝ) * (χ (a : ZMod p)).re) -
              (p : ℝ) * ∑ a ∈ Finset.Ioo m p, (χ (a : ZMod p)).re := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => by ring
      rw [hL1, hR1, hsum_top_eq_neg_bot]
      ring
    -- Multiply `hcomb` by `(χ 2).re` (whose square is `1`)
    have hfinal :
        (2 - (χ (2 : ZMod p)).re) * (-(∑ a ∈ Finset.Ico 1 p, (a : ℝ) * (χ (a : ZMod p)).re)) =
          (p : ℝ) * ∑ a ∈ Finset.Icc 1 m, (χ (a : ZMod p)).re := by
      have hm := congrArg ((χ (2 : ZMod p)).re * ·) hcomb
      rw [← mul_assoc, ← sq, hχ2_sq, one_mul] at hm
      linarith
    have hp_posR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
    nlinarith
  exact ⟨hodd, hgauss, hneg, hhalf_pos⟩

/-! ### Section 4B: Full Gauss-Sum Sign Theorem & Dirichlet Sign Theorem for ALL Real Primitive `χ mod q` -/

/-- Helper: for any real Dirichlet character `χ` and unit `u : (ZMod q)ˣ`, `χ u = 1 ∨ χ u = -1`. -/
private lemma real_char_unit_eq_one_or_neg_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (u : (ZMod q)ˣ) :
    χ (u : ZMod q) = 1 ∨ χ (u : ZMod q) = -1 := by
  have hnorm : ‖χ (u : ZMod q)‖ = 1 :=
    (Stage2BehrendSieve.dirichlet_norm_eq_one_and_conj χ u.isUnit).1
  have him : (χ (u : ZMod q)).im = 0 := hreal _
  have hsq : (χ (u : ZMod q)).re ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq (χ (u : ZMod q))
    rw [hnorm, one_pow, Complex.normSq_apply, him] at h
    nlinarith
  rcases sq_eq_one_iff.mp hsq with h1 | hm1
  · left; exact Complex.ext (by simpa using h1) (by simpa using him)
  · right; exact Complex.ext (by simpa using hm1) (by simpa using him)

/-- **CRT Decomposition of Dirichlet Characters & Gauss Sums**:
for coprime `m, n ≥ 1` and any `χ : DirichletCharacter ℂ (m * n)`, there exist
`χ₁ : DirichletCharacter ℂ m` and `χ₂ : DirichletCharacter ℂ n` such that:
- `χ x = χ₁ (ZMod.cast x) * χ₂ (ZMod.cast x)` for all `x : ZMod (m * n)`,
- `χ` real ⟹ `χ₁, χ₂` real,
- `χ` primitive ⟹ `χ₁, χ₂` primitive,
- `τ(χ) = χ₁(n) * χ₂(m) * τ(χ₁) * τ(χ₂)`. -/
theorem exists_crt_decomposition_gaussSum {m n : ℕ} [NeZero m] [NeZero n]
    (hcop : Nat.Coprime m n) (χ : DirichletCharacter ℂ (m * n)) :
    ∃ (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n),
      (∀ x : ZMod (m * n),
        χ x = χ₁ (ZMod.castHom (dvd_mul_right m n) (ZMod m) x) *
              χ₂ (ZMod.castHom (dvd_mul_left n m) (ZMod n) x)) ∧
      ((∀ a : ZMod (m * n), (χ a).im = 0) →
        (∀ a : ZMod m, (χ₁ a).im = 0) ∧ (∀ b : ZMod n, (χ₂ b).im = 0)) ∧
      (χ.IsPrimitive → χ₁.IsPrimitive ∧ χ₂.IsPrimitive) ∧
      gaussSum χ ZMod.stdAddChar =
        χ₁ (n : ZMod m) * χ₂ (m : ZMod n) *
          gaussSum χ₁ ZMod.stdAddChar * gaussSum χ₂ ZMod.stdAddChar := by
  have : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  let eCRT : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hcop
  let eU : (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
    (Units.mapEquiv eCRT.toMulEquiv).trans MulEquiv.prodUnits
  let inl : (ZMod m)ˣ →* (ZMod (m * n))ˣ :=
    { toFun := fun u => eU.symm (u, 1)
      map_one' := by simp
      map_mul' := fun u v => by rw [← map_mul]; simp }
  let inr : (ZMod n)ˣ →* (ZMod (m * n))ˣ :=
    { toFun := fun v => eU.symm (1, v)
      map_one' := by simp
      map_mul' := fun u v => by rw [← map_mul]; simp }
  let χ₁ : DirichletCharacter ℂ m := MulChar.ofUnitHom (χ.toUnitHom.comp inl)
  let χ₂ : DirichletCharacter ℂ n := MulChar.ofUnitHom (χ.toUnitHom.comp inr)
  have hcast_eq : ∀ x : ZMod (m * n),
      eCRT x = (ZMod.castHom (dvd_mul_right m n) (ZMod m) x,
                ZMod.castHom (dvd_mul_left n m) (ZMod n) x) := fun x => by
    rw [← ZMod.natCast_zmod_val x, map_natCast, map_natCast, map_natCast]
    rfl
  have hfact : ∀ x : ZMod (m * n),
      χ x = χ₁ (ZMod.castHom (dvd_mul_right m n) (ZMod m) x) *
            χ₂ (ZMod.castHom (dvd_mul_left n m) (ZMod n) x) := by
    intro x
    by_cases hx : IsUnit x
    · obtain ⟨u, rfl⟩ := hx
      have heu : eU u = (Units.map (ZMod.castHom (dvd_mul_right m n) (ZMod m)).toMonoidHom u,
                         Units.map (ZMod.castHom (dvd_mul_left n m) (ZMod n)).toMonoidHom u) := by
        apply Prod.ext
        · apply Units.ext
          exact congrArg Prod.fst (hcast_eq (u : ZMod (m * n)))
        · apply Units.ext
          exact congrArg Prod.snd (hcast_eq (u : ZMod (m * n)))
      have hdecomp : u = inl (eU u).1 * inr (eU u).2 := by
        apply eU.injective
        simp [inl, inr]
      have hu1 : ((eU u).1 : ZMod m) = ZMod.castHom (dvd_mul_right m n) (ZMod m) (u : ZMod (m * n)) := by
        rw [heu]; rfl
      have hu2 : ((eU u).2 : ZMod n) = ZMod.castHom (dvd_mul_left n m) (ZMod n) (u : ZMod (m * n)) := by
        rw [heu]; rfl
      rw [← hu1, ← hu2]
      calc χ (u : ZMod (m * n))
          = χ ((inl (eU u).1 * inr (eU u).2 : (ZMod (m * n))ˣ) : ZMod (m * n)) := by
            conv_lhs => rw [hdecomp]
        _ = χ (inl (eU u).1 : ZMod (m * n)) * χ (inr (eU u).2 : ZMod (m * n)) := by
            rw [Units.val_mul, map_mul]
        _ = χ₁ ((eU u).1 : ZMod m) * χ₂ ((eU u).2 : ZMod n) := by
            simp [χ₁, χ₂]
    · have hnotboth : ¬ (IsUnit (ZMod.castHom (dvd_mul_right m n) (ZMod m) x) ∧
                         IsUnit (ZMod.castHom (dvd_mul_left n m) (ZMod n) x)) := by
        rintro ⟨hu1, hu2⟩
        apply hx
        have hpair : IsUnit (eCRT x) := by
          rw [hcast_eq x, Prod.isUnit_iff]
          exact ⟨hu1, hu2⟩
        simpa using hpair.map eCRT.symm.toMonoidHom
      rw [MulChar.map_nonunit χ hx]
      by_cases h1 : IsUnit (ZMod.castHom (dvd_mul_right m n) (ZMod m) x)
      · have h2 : ¬ IsUnit (ZMod.castHom (dvd_mul_left n m) (ZMod n) x) := fun h2 => hnotboth ⟨h1, h2⟩
        rw [MulChar.map_nonunit χ₂ h2, mul_zero]
      · rw [MulChar.map_nonunit χ₁ h1, zero_mul]
  have hreal_imp :
      (∀ a : ZMod (m * n), (χ a).im = 0) →
        (∀ a : ZMod m, (χ₁ a).im = 0) ∧ (∀ b : ZMod n, (χ₂ b).im = 0) := by
    intro hreal
    constructor
    · intro a
      by_cases ha : IsUnit a
      · obtain ⟨u, rfl⟩ := ha
        have h : χ₁ (u : ZMod m) = χ (inl u : ZMod (m * n)) := by
          simp [χ₁]
        rw [h]; exact hreal _
      · rw [MulChar.map_nonunit χ₁ ha]; simp
    · intro b
      by_cases hb : IsUnit b
      · obtain ⟨v, rfl⟩ := hb
        have h : χ₂ (v : ZMod n) = χ (inr v : ZMod (m * n)) := by
          simp [χ₂]
        rw [h]; exact hreal _
      · rw [MulChar.map_nonunit χ₂ hb]; simp
  have hprim_imp : χ.IsPrimitive → χ₁.IsPrimitive ∧ χ₂.IsPrimitive := by
    intro hprim
    have hchange :
        χ = DirichletCharacter.changeLevel (dvd_mul_right m n) χ₁ *
            DirichletCharacter.changeLevel (dvd_mul_left n m) χ₂ := by
      ext u
      have hu := hfact (u : ZMod (m * n))
      simpa [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe,
        MulChar.coe_toUnitHom, ZMod.unitsMap_def] using hu
    constructor
    · show χ₁.conductor = m
      apply Nat.dvd_antisymm χ₁.conductor_dvd_level
      have hfac1 := χ₁.factorsThrough_conductor
      obtain ⟨hd1, ψ₁, hψ₁⟩ := hfac1
      have : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
      have hdvd_tot : χ₁.conductor * n ∣ m * n := mul_dvd_mul_right hd1 n
      have : NeZero (χ₁.conductor * n) := ⟨Nat.mul_ne_zero χ₁.conductor_ne_zero (NeZero.ne n)⟩
      have hχ_fac : χ.FactorsThrough (χ₁.conductor * n) := by
        refine ⟨hdvd_tot,
          DirichletCharacter.changeLevel (dvd_mul_right χ₁.conductor n) ψ₁ *
          DirichletCharacter.changeLevel (dvd_mul_left n χ₁.conductor) χ₂, ?_⟩
        rw [map_mul, ← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
        have h1eq : DirichletCharacter.changeLevel (dvd_trans hd1 (dvd_mul_right m n)) ψ₁ =
            DirichletCharacter.changeLevel (dvd_mul_right m n) χ₁ := by
          conv_rhs => rw [hψ₁]
          rw [DirichletCharacter.changeLevel_trans]
        rw [h1eq, hchange]
      have hcond_dvd : χ.conductor ∣ χ₁.conductor * n :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hdvd_tot).mp hχ_fac
      rw [hprim] at hcond_dvd
      exact (mul_dvd_mul_iff_right (NeZero.ne n)).mp hcond_dvd
    · show χ₂.conductor = n
      apply Nat.dvd_antisymm χ₂.conductor_dvd_level
      have hfac2 := χ₂.factorsThrough_conductor
      obtain ⟨hd2, ψ₂, hψ₂⟩ := hfac2
      have : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
      have hdvd_tot : m * χ₂.conductor ∣ m * n := mul_dvd_mul_left m hd2
      have : NeZero (m * χ₂.conductor) := ⟨Nat.mul_ne_zero (NeZero.ne m) χ₂.conductor_ne_zero⟩
      have hχ_fac : χ.FactorsThrough (m * χ₂.conductor) := by
        refine ⟨hdvd_tot,
          DirichletCharacter.changeLevel (dvd_mul_right m χ₂.conductor) χ₁ *
          DirichletCharacter.changeLevel (dvd_mul_left χ₂.conductor m) ψ₂, ?_⟩
        rw [map_mul, ← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
        have h2eq : DirichletCharacter.changeLevel (dvd_trans hd2 (dvd_mul_left n m)) ψ₂ =
            DirichletCharacter.changeLevel (dvd_mul_left n m) χ₂ := by
          conv_rhs => rw [hψ₂]
          rw [DirichletCharacter.changeLevel_trans]
        rw [h2eq, hchange]
      have hcond_dvd : χ.conductor ∣ m * χ₂.conductor :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hdvd_tot).mp hχ_fac
      rw [hprim] at hcond_dvd
      exact (mul_dvd_mul_iff_left (NeZero.ne m)).mp hcond_dvd
  -- Gauss sum CRT factorization via `(a, b) ↦ n * a.val + m * b.val`
  have hgauss_crt :
      gaussSum χ ZMod.stdAddChar =
        χ₁ (n : ZMod m) * χ₂ (m : ZMod n) *
          gaussSum χ₁ ZMod.stdAddChar * gaussSum χ₂ ZMod.stdAddChar := by
    let φ : ZMod m × ZMod n → ZMod (m * n) := fun p =>
      (n : ZMod (m * n)) * (p.1.val : ZMod (m * n)) +
        (m : ZMod (m * n)) * (p.2.val : ZMod (m * n))
    have hφ_cast1 : ∀ p : ZMod m × ZMod n,
        ZMod.castHom (dvd_mul_right m n) (ZMod m) (φ p) = (n : ZMod m) * p.1 := by
      intro p
      dsimp only [φ]
      rw [map_add, map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero]
    have hφ_cast2 : ∀ p : ZMod m × ZMod n,
        ZMod.castHom (dvd_mul_left n m) (ZMod n) (φ p) = (m : ZMod n) * p.2 := by
      intro p
      dsimp only [φ]
      rw [map_add, map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, zero_add]
    have hφ_inj : Function.Injective φ := by
      intro p₁ p₂ h
      have h1 := congrArg (ZMod.castHom (dvd_mul_right m n) (ZMod m)) h
      have h2 := congrArg (ZMod.castHom (dvd_mul_left n m) (ZMod n)) h
      rw [hφ_cast1, hφ_cast1] at h1
      rw [hφ_cast2, hφ_cast2] at h2
      have hn_u : IsUnit (n : ZMod m) := (ZMod.isUnit_iff_coprime n m).mpr hcop.symm
      have hm_u : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr hcop
      exact Prod.ext (hn_u.mul_left_cancel h1) (hm_u.mul_left_cancel h2)
    have hφ_bij : Function.Bijective φ := by
      refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, ?_⟩
      simp [ZMod.card]
    have hφ_add : ∀ p : ZMod m × ZMod n,
        ZMod.stdAddChar (φ p) = ZMod.stdAddChar p.1 * ZMod.stdAddChar p.2 := by
      intro p
      have hcast : φ p = ((n * p.1.val + m * p.2.val : ℕ) : ZMod (m * n)) := by
        dsimp only [φ]; push_cast; rfl
      rw [hcast, stdAddChar_natCast_eq_e, stdAddChar_eq_e, stdAddChar_eq_e, ← e_add]
      congr 1
      have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      push_cast
      field_simp [hm_ne, hn_ne]
    unfold gaussSum
    rw [← Equiv.sum_comp (Equiv.ofBijective φ hφ_bij)]
    simp only [Equiv.ofBijective_apply]
    have hterm : ∀ p : ZMod m × ZMod n,
        χ (φ p) * ZMod.stdAddChar (φ p) =
          (χ₁ (n : ZMod m) * χ₂ (m : ZMod n)) *
            ((χ₁ p.1 * ZMod.stdAddChar p.1) * (χ₂ p.2 * ZMod.stdAddChar p.2)) := by
      intro p
      rw [hfact (φ p), hφ_cast1, hφ_cast2, map_mul, map_mul, hφ_add]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    have hprod_sum :
        ∑ a : ZMod m, ∑ b : ZMod n,
            (χ₁ a * ZMod.stdAddChar a) * (χ₂ b * ZMod.stdAddChar b) =
          (∑ a : ZMod m, χ₁ a * ZMod.stdAddChar a) *
            ∑ b : ZMod n, χ₂ b * ZMod.stdAddChar b := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    rw [hprod_sum]
    ring
  exact ⟨χ₁, χ₂, hfact, hreal_imp, hprim_imp, hgauss_crt⟩

/-- Transport wrapper for `exists_crt_decomposition_gaussSum` when `q = m * n` via an equality `hq`,
avoiding dependent `subst` issues in callers. -/
private theorem exists_crt_decomposition_of_eq {q m n : ℕ} [NeZero q] [NeZero m] [NeZero n]
    (hq : q = m * n) (hcop : Nat.Coprime m n) (χ : DirichletCharacter ℂ q) :
    ∃ (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n),
      (∀ a : ℕ, χ (a : ZMod q) = χ₁ (a : ZMod m) * χ₂ (a : ZMod n)) ∧
      (χ (-1 : ZMod q) = χ₁ (-1 : ZMod m) * χ₂ (-1 : ZMod n)) ∧
      ((∀ a : ZMod q, (χ a).im = 0) →
        (∀ a : ZMod m, (χ₁ a).im = 0) ∧ (∀ b : ZMod n, (χ₂ b).im = 0)) ∧
      (χ.IsPrimitive → χ₁.IsPrimitive ∧ χ₂.IsPrimitive) ∧
      gaussSum χ ZMod.stdAddChar =
        χ₁ (n : ZMod m) * χ₂ (m : ZMod n) *
          gaussSum χ₁ ZMod.stdAddChar * gaussSum χ₂ ZMod.stdAddChar := by
  subst hq
  obtain ⟨χ₁, χ₂, hfact, hreal12, hprim12, hgauss⟩ := exists_crt_decomposition_gaussSum hcop χ
  refine ⟨χ₁, χ₂, ?_, ?_, hreal12, hprim12, hgauss⟩
  · intro a
    have h := hfact (a : ZMod (m * n))
    simpa only [map_natCast] using h
  · have h := hfact (-1 : ZMod (m * n))
    simpa only [map_neg, map_one] using h

/-- Transport wrapper across an equality of moduli `h : m₁ = m₂`, avoiding dependent `subst` issues. -/
private lemma exists_char_eq_of_level_eq {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] (h : m₁ = m₂)
    (χ : DirichletCharacter ℂ m₁) :
    ∃ χ' : DirichletCharacter ℂ m₂,
      (∀ a : ℕ, χ' (a : ZMod m₂) = χ (a : ZMod m₁)) ∧
      χ' (-1 : ZMod m₂) = χ (-1 : ZMod m₁) ∧
      (χ'.Even ↔ χ.Even) ∧
      (χ'.IsPrimitive ↔ χ.IsPrimitive) ∧
      (χ' ≠ 1 ↔ χ ≠ 1) ∧
      ((∀ a : ZMod m₁, (χ a).im = 0) → ∀ a : ZMod m₂, (χ' a).im = 0) ∧
      gaussSum χ' ZMod.stdAddChar = gaussSum χ ZMod.stdAddChar := by
  subst h
  exact ⟨χ, fun _ => rfl, rfl, Iff.rfl, Iff.rfl, Iff.rfl, id, rfl⟩

/-- Helper: for odd prime `p` and `j ≥ 0`, `p ^ (j + 1) ∣ (1 + p * t) ^ (p ^ j) - 1`
(modulo `p ^ (j + 1)`, every `1 + p * t` has `p ^ j`-th power equal to `1`). -/
private lemma one_add_prime_mul_pow_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (t : ℕ) :
    ∀ j : ℕ, (1 + p * t) ^ (p ^ j) ≡ 1 [MOD p ^ (j + 1)] := by
  intro j
  induction j with
  | zero =>
    rw [pow_zero, pow_one, pow_one, Nat.ModEq, Nat.add_mul_mod_self_left]
  | succ k ih =>
    have hge1 : 1 ≤ (1 + p * t) ^ (p ^ k) := Nat.one_le_pow _ _ (by omega)
    obtain ⟨y, hy⟩ := (Nat.modEq_iff_dvd' hge1).mp ih.symm
    have hx : (1 + p * t) ^ (p ^ k) = 1 + p ^ (k + 1) * y := by omega
    conv_lhs => rw [pow_succ, pow_mul, hx]
    -- Show `(1 + p^(k+1) * y)^p ≡ 1 [MOD p^(k+2)]` via `add_pow`
    rw [Nat.ModEq, add_comm 1, add_pow]
    have hsum_dvd :
        p ^ (k + 2) ∣
          ∑ i ∈ Finset.Icc 1 p, (p ^ (k + 1) * y) ^ i * p.choose i := by
      refine Finset.dvd_sum fun i hi => ?_
      have hi' := Finset.mem_Icc.mp hi
      rcases eq_or_lt_of_le hi'.2 with hip | hilt
      · rw [hip]
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hexp : k + 2 ≤ (k + 1) * p := by nlinarith
        rw [mul_pow, ← pow_mul]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hexp) _) _
      · have hch : p ∣ p.choose i := hp.dvd_choose_self (by omega) hilt
        have hpow_i : p ^ (k + 1) ∣ (p ^ (k + 1) * y) ^ i := by
          rw [mul_pow, ← pow_mul]
          exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p (by nlinarith)) _
        have hmul : p ^ (k + 1) * p ∣ (p ^ (k + 1) * y) ^ i * p.choose i :=
          mul_dvd_mul hpow_i hch
        rwa [← pow_succ] at hmul
    have hrange_split : Finset.range (p + 1) = insert 0 (Finset.Icc 1 p) := by
      ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange_split, Finset.sum_insert (by simp)]
    simp only [pow_zero, one_pow, Nat.choose_zero_right, mul_one, Nat.cast_id]
    obtain ⟨m, hm⟩ := hsum_dvd
    rw [hm, add_comm 1, Nat.mul_add_mod]

/-- **Odd Prime-Power Classification**: every real primitive Dirichlet character of odd prime-power
modulus `p ^ k` (`k ≥ 1`) must have `k = 1`! -/
theorem odd_prime_pow_exp_eq_one_of_real_primitive {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 1 ≤ k) {χ : DirichletCharacter ℂ (p ^ k)}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod (p ^ k), (χ a).im = 0) :
    k = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hfac : χ.FactorsThrough p := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (dvd_pow_self p (by omega))]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    -- `u ≡ 1 [MOD p]` implies `u ^ (p ^ (k - 1)) = 1` in `(ZMod (p^k))ˣ`
    have hu1 : ((u : ZMod (p ^ k)).val : ZMod p) = 1 := by
      have hv := congrArg Units.val hu
      simpa [ZMod.unitsMap_def] using hv
    have hdvd : p ∣ (u : ZMod (p ^ k)).val - 1 := by
      have hval_pos : 1 ≤ (u : ZMod (p ^ k)).val := by
        by_contra h0
        have hv0 : (u : ZMod (p ^ k)).val = 0 := by omega
        rw [hv0, Nat.cast_zero] at hu1
        have : Fact p.Prime := ⟨hp⟩
        exact zero_ne_one hu1
      have hmod : (u : ZMod (p ^ k)).val ≡ 1 [MOD p] := by
        rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]; exact hu1
      exact (Nat.modEq_iff_dvd' hval_pos).mp hmod.symm
    obtain ⟨t, ht⟩ := hdvd
    have huval : (u : ZMod (p ^ k)).val = 1 + p * t := by
      have hval_pos : 1 ≤ (u : ZMod (p ^ k)).val := by
        by_contra h0
        have hv0 : (u : ZMod (p ^ k)).val = 0 := by omega
        rw [hv0, Nat.cast_zero] at hu1
        have : Fact p.Prime := ⟨hp⟩
        exact zero_ne_one hu1
      omega
    have hpow_mod := one_add_prime_mul_pow_prime_pow hp hp2 t (k - 1)
    have hsub1 : k - 1 + 1 = k := by omega
    rw [hsub1, ← huval] at hpow_mod
    have hpow_u : u ^ (p ^ (k - 1)) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, ← ZMod.natCast_zmod_val (u : ZMod (p ^ k)),
        ← Nat.cast_pow]
      simpa only [Nat.cast_one] using
        (ZMod.natCast_eq_natCast_iff ((u : ZMod (p ^ k)).val ^ p ^ (k - 1)) 1 (p ^ k)).mpr hpow_mod
    have hχ_pow_odd : χ (u : ZMod (p ^ k)) ^ (p ^ (k - 1)) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hpow_u, Units.val_one, map_one]
    apply Units.ext
    rw [Units.val_one, MulChar.coe_toUnitHom]
    rcases real_char_unit_eq_one_or_neg_one hreal u with h1 | hm1
    · exact h1
    · exfalso
      rw [hm1] at hχ_pow_odd
      have hodd : Odd (p ^ (k - 1)) := (hp.odd_of_ne_two hp2).pow
      rw [hodd.neg_one_pow] at hχ_pow_odd
      norm_num at hχ_pow_odd
  have hle : p ^ k ≤ p := by
    have hdvd : χ.conductor ∣ p := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ
      (dvd_pow_self p (by omega))).mp hfac
    rw [hprim] at hdvd
    exact Nat.le_of_dvd hp.pos hdvd
  by_contra hk1
  have hk2 : 2 ≤ k := by omega
  have hgt : p < p ^ k := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

/-- Helper: `n % (d * 2) = n % d + d * ((n / d) % 2)` for any `d > 0`. -/
private lemma nat_mod_mul_two {d : ℕ} (hd : 0 < d) (n : ℕ) :
    n % (d * 2) = n % d + d * ((n / d) % 2) := by
  have hlt : n % d + d * ((n / d) % 2) < d * 2 := by
    have h1 : n % d < d := Nat.mod_lt n hd
    have h2 : (n / d) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    nlinarith
  have heq : n = (d * 2) * (n / d / 2) + (n % d + d * ((n / d) % 2)) := by
    have h1 := (Nat.div_add_mod n d).symm
    have h2 := (Nat.div_add_mod (n / d) 2).symm
    calc n = d * (n / d) + n % d := h1
      _ = d * (2 * (n / d / 2) + (n / d) % 2) + n % d := by rw [← h2]
      _ = (d * 2) * (n / d / 2) + (n % d + d * ((n / d) % 2)) := by ring
  conv_lhs => rw [heq]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- Helper: every natural number `a ≡ 1 [MOD 8]` is a square modulo `2 ^ k` for all `k ≥ 3`. -/
private lemma exists_sq_mod_two_pow {a : ℕ} (ha8 : a % 8 = 1) :
    ∀ k : ℕ, 3 ≤ k → ∃ x : ℕ, x ^ 2 ≡ a [MOD 2 ^ k] := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨1, ?_⟩
    rw [Nat.ModEq, one_pow, show 2 ^ 3 = 8 by norm_num, ha8]
    norm_num
  | succ j hj ih =>
    obtain ⟨x, hx⟩ := ih
    have hx_odd : x % 2 = 1 := by
      have hmod2 : x ^ 2 % 2 = a % 2 := hx.of_dvd (dvd_pow_self 2 (by omega))
      have ha2 : a % 2 = 1 := by omega
      rw [ha2, sq, Nat.mul_mod] at hmod2
      rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
      · rw [h0] at hmod2; norm_num at hmod2
      · exact h1
    by_cases hnext : x ^ 2 ≡ a [MOD 2 ^ (j + 1)]
    · exact ⟨x, hnext⟩
    · refine ⟨x + 2 ^ (j - 1), ?_⟩
      have hsq_exp :
          (x + 2 ^ (j - 1)) ^ 2 = x ^ 2 + 2 ^ j * x + 2 ^ (2 * j - 2) := by
        have h2mul : 2 * 2 ^ (j - 1) = 2 ^ j := by
          rw [mul_comm, ← pow_succ, show j - 1 + 1 = j by omega]
        have h2sq : (2 ^ (j - 1)) ^ 2 = 2 ^ (2 * j - 2) := by
          rw [← pow_mul]; congr 1; omega
        calc (x + 2 ^ (j - 1)) ^ 2
            = x ^ 2 + (2 * 2 ^ (j - 1)) * x + (2 ^ (j - 1)) ^ 2 := by ring
          _ = x ^ 2 + 2 ^ j * x + 2 ^ (2 * j - 2) := by rw [h2mul, h2sq]
      have h2j_le : j + 1 ≤ 2 * j - 2 := by omega
      have hpow_dvd : 2 ^ (j + 1) ∣ 2 ^ (2 * j - 2) := Nat.pow_dvd_pow 2 h2j_le
      have hdiff_mod : (x ^ 2 + 2 ^ j * x) % 2 ^ (j + 1) = a % 2 ^ (j + 1) := by
        have h2j_pos : 0 < 2 ^ j := pow_pos (by norm_num) j
        have hq_eq : x ^ 2 % 2 ^ j = a % 2 ^ j := hx
        have hpow_s : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
        rw [Nat.ModEq] at hnext
        have hpar : (x ^ 2 / 2 ^ j) % 2 ≠ (a / 2 ^ j) % 2 := by
          intro heq
          apply hnext
          rw [hpow_s, nat_mod_mul_two h2j_pos, nat_mod_mul_two h2j_pos, hq_eq, heq]
        rw [hpow_s, nat_mod_mul_two h2j_pos, nat_mod_mul_two h2j_pos]
        have hadd_mod : (x ^ 2 + 2 ^ j * x) % 2 ^ j = a % 2 ^ j := by
          rw [Nat.add_mul_mod_self_left, hq_eq]
        have hadd_div : (x ^ 2 + 2 ^ j * x) / 2 ^ j = x ^ 2 / 2 ^ j + x := by
          rw [Nat.add_mul_div_left _ _ h2j_pos]
        rw [hadd_mod, hadd_div]
        congr 2
        omega
      rw [Nat.ModEq, hsq_exp]
      obtain ⟨c, hc⟩ := hpow_dvd
      rw [hc, Nat.add_mul_mod_self_left, hdiff_mod]

/-- **2-Power Classification**: every real primitive Dirichlet character of `2`-power modulus
`2 ^ k` must have `k = 0`, `k = 2`, or `k = 3`! -/
theorem two_pow_exp_mem_of_real_primitive {k : ℕ} {χ : DirichletCharacter ℂ (2 ^ k)}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod (2 ^ k), (χ a).im = 0) :
    k = 0 ∨ k = 2 ∨ k = 3 := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  by_cases hk0 : k = 0
  · exact Or.inl hk0
  by_cases hk1 : k = 1
  · exfalso
    subst hk1
    have h1 : χ = 1 := by
      ext u
      have hu : u = 1 := by
        apply Units.ext
        have hlt : (u : ZMod (2 ^ 1)).val < 2 := by simpa using ZMod.val_lt (u : ZMod (2 ^ 1))
        have hcop : Nat.Coprime (u : ZMod (2 ^ 1)).val 2 := by
          have hu' : IsUnit (((u : ZMod (2 ^ 1)).val : ℕ) : ZMod (2 ^ 1)) := by
            rw [ZMod.natCast_zmod_val]; exact u.isUnit
          simpa using (ZMod.isUnit_iff_coprime _ (2 ^ 1)).mp hu'
        have hv1 : (u : ZMod (2 ^ 1)).val = 1 := by
          have h01 : (u : ZMod (2 ^ 1)).val = 0 ∨ (u : ZMod (2 ^ 1)).val = 1 := by omega
          rcases h01 with h0 | h1
          · rw [h0] at hcop; norm_num at hcop
          · exact h1
        rw [← ZMod.natCast_zmod_val (u : ZMod (2 ^ 1)), hv1]; rfl
      rw [hu, Units.val_one, map_one, map_one]
    have hcond : χ.conductor = 1 := by rw [h1]; exact DirichletCharacter.conductor_one
    rw [hprim] at hcond
    norm_num at hcond
  by_cases hk2 : k = 2
  · exact Or.inr (Or.inl hk2)
  by_cases hk3 : k = 3
  · exact Or.inr (Or.inr hk3)
  -- For `k ≥ 4`, show `χ` factors through `8 = 2^3`, contradicting `χ.conductor = 2^k`
  exfalso
  have hk4 : 4 ≤ k := by omega
  have hdvd8 : 8 ∣ 2 ^ k := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
  have hfac8 : χ.FactorsThrough 8 := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd8]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have hu8 : (u : ZMod (2 ^ k)).val % 8 = 1 := by
      have hv := congrArg Units.val hu
      have hcast : ((u : ZMod (2 ^ k)).val : ZMod 8) = 1 := by
        simpa [ZMod.unitsMap_def] using hv
      have hmod := (ZMod.natCast_eq_natCast_iff (u : ZMod (2 ^ k)).val 1 8).mp (by simpa using hcast)
      simpa [Nat.ModEq] using hmod
    obtain ⟨x, hx⟩ := exists_sq_mod_two_pow hu8 k (by omega)
    have hx_cop : Nat.Coprime x (2 ^ k) := by
      have hx_odd : x % 2 = 1 := by
        have hmod2 : x ^ 2 % 2 = (u : ZMod (2 ^ k)).val % 2 := hx.of_dvd (dvd_pow_self 2 (by omega))
        have hu2 : (u : ZMod (2 ^ k)).val % 2 = 1 := by omega
        rw [hu2, sq, Nat.mul_mod] at hmod2
        rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
        · rw [h0] at hmod2; norm_num at hmod2
        · exact h1
      exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega)).symm.pow_right k
    let v : (ZMod (2 ^ k))ˣ := ZMod.unitOfCoprime x hx_cop
    have hv_sq : v ^ 2 = u := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow,
        ← ZMod.natCast_zmod_val (u : ZMod (2 ^ k))]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hx
    apply Units.ext
    rw [Units.val_one, MulChar.coe_toUnitHom, ← hv_sq, Units.val_pow_eq_pow_val, map_pow]
    rcases real_char_unit_eq_one_or_neg_one hreal v with h1 | hm1
    · rw [h1, one_pow]
    · rw [hm1]; norm_num
  have hle : 2 ^ k ≤ 8 := by
    have hdvd : χ.conductor ∣ 8 := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hdvd8).mp hfac8
    rw [hprim] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hgt : 8 < 2 ^ k := by
    calc 8 = 2 ^ 3 := by norm_num
      _ < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- Exact evaluation of `χ mod p` as the Jacobi symbol `(a / p)` for any odd prime `p`
and any real non-principal character `χ : DirichletCharacter ℂ p`. -/
theorem prime_real_char_eq_jacobiSym {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (hreal : ∀ a : ZMod p, (χ a).im = 0) (a : ℕ) :
    χ (a : ZMod p) = (jacobiSym (a : ℤ) p : ℂ) := by
  have hp_prime : p.Prime := Fact.out
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  by_cases ha0 : (a : ZMod p) = 0
  · rw [ha0, χ.map_zero' hp_prime.ne_one]
    have hleg : legendreSym p (a : ℤ) = 0 := by
      rw [legendreSym.eq_zero_iff]; exact_mod_cast ha0
    rw [hleg]; simp
  · have ha_u : IsUnit (a : ZMod p) := isUnit_iff_ne_zero.mpr ha0
    -- Use `sqHom.range = χHom.ker` on `(ZMod p)ˣ` as in `gaussSum_eq_quadratic_sum_of_prime`
    let sqHom : (ZMod p)ˣ →* (ZMod p)ˣ :=
      { toFun := fun u => u ^ 2
        map_one' := one_pow 2
        map_mul' := fun u v => mul_pow u v 2 }
    let χHom : (ZMod p)ˣ →* ℂˣ :=
      { toFun := fun u => Units.mk0 (χ (u : ZMod p)) (by
          rcases real_char_unit_eq_one_or_neg_one hreal u with h1 | hm1
          · simp [h1]
          · simp [hm1])
        map_one' := Units.ext (by simp)
        map_mul' := fun u v => Units.ext (by simp [map_mul]) }
    have hsub : sqHom.range ≤ χHom.ker := by
      rintro _ ⟨u, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Units.ext
      change χ ((u : ZMod p) ^ 2) = 1
      rw [map_pow]
      rcases real_char_unit_eq_one_or_neg_one hreal u with h1 | hm1
      · simp [h1]
      · simp [hm1]
    have hker_sq_card : Fintype.card sqHom.ker = 2 := by
      have hker_eq : (Finset.univ.filter fun u : (ZMod p)ˣ => u ^ 2 = 1) = {1, -1} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro h
          have hv : (u : ZMod p) ^ 2 = 1 := by simpa using congrArg Units.val h
          rcases sq_eq_one_iff.mp hv with h1 | hm1
          · left; exact Units.ext h1
          · right; exact Units.ext hm1
        · rintro (rfl | rfl) <;> simp
      have h1ne : (1 : (ZMod p)ˣ) ≠ -1 := by
        intro h
        have hv : (1 : ZMod p) = -1 := congrArg Units.val h
        have h20 : (2 : ZMod p) = 0 := by linear_combination hv
        have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
        exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp_prime.two_le)
      calc Fintype.card sqHom.ker
          = (Finset.univ.filter fun u : (ZMod p)ˣ => u ^ 2 = 1).card := by
            rw [← Fintype.card_coe]
            refine Fintype.card_congr
              { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
                invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl }
        _ = ({(1 : (ZMod p)ˣ), -1} : Finset (ZMod p)ˣ).card := by rw [hker_eq]
        _ = 2 := Finset.card_pair h1ne
    have hrange_sq_card : Fintype.card sqHom.range * 2 = Fintype.card (ZMod p)ˣ := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup sqHom.ker
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        hker_sq_card] at h
      have hq := Fintype.card_congr (QuotientGroup.quotientKerEquivRange sqHom).toEquiv
      rw [← hq, ← h]
    have hker_χ_card : Fintype.card χHom.ker < Fintype.card (ZMod p)ˣ := by
      by_contra hge
      push Not at hge
      have htop : χHom.ker = ⊤ := by
        rw [eq_top_iff]
        intro u _
        have hcard_eq : (Finset.univ.filter fun v : (ZMod p)ˣ => v ∈ χHom.ker).card =
            (Finset.univ : Finset (ZMod p)ˣ).card := by
          have h1 : (Finset.univ.filter fun v : (ZMod p)ˣ => v ∈ χHom.ker).card =
              Fintype.card χHom.ker := by
            rw [← Fintype.card_coe]
            exact (Fintype.card_congr
              { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
                invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl }).symm
          have hle := Finset.card_le_card (Finset.filter_subset (fun v : (ZMod p)ˣ => v ∈ χHom.ker) Finset.univ)
          rw [Finset.card_univ] at hle ⊢
          omega
        have hall := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcard_eq.ge
        have hu_mem : u ∈ Finset.univ.filter (fun v : (ZMod p)ˣ => v ∈ χHom.ker) := by
          rw [hall]; exact Finset.mem_univ u
        exact (Finset.mem_filter.mp hu_mem).2
      apply hχ
      ext u
      have hmem : u ∈ χHom.ker := by rw [htop]; trivial
      have hv := congrArg Units.val hmem
      simpa [χHom, MulChar.one_apply u.isUnit] using hv
    have hrange_eq_ker : sqHom.range = χHom.ker := by
      have hdvd1 : Fintype.card sqHom.range ∣ Fintype.card χHom.ker := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact Subgroup.card_dvd_of_le hsub
      have hdvd2 : Fintype.card χHom.ker ∣ Fintype.card (ZMod p)ˣ := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact Subgroup.card_subgroup_dvd_card χHom.ker
      obtain ⟨k, hk⟩ := hdvd1
      obtain ⟨m, hm⟩ := hdvd2
      have hprod : Fintype.card sqHom.range * (k * m) = Fintype.card sqHom.range * 2 := by
        calc Fintype.card sqHom.range * (k * m)
            = (Fintype.card sqHom.range * k) * m := by ring
          _ = Fintype.card χHom.ker * m := by rw [← hk]
          _ = Fintype.card (ZMod p)ˣ := hm.symm
          _ = Fintype.card sqHom.range * 2 := hrange_sq_card.symm
      have hkm : k * m = 2 := Nat.eq_of_mul_eq_mul_left Fintype.card_pos hprod
      have hm_ne1 : m ≠ 1 := fun hm1 => by rw [hm1, mul_one] at hm; omega
      have hk1 : k = 1 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp ⟨m, hkm.symm⟩ with rfl | rfl
        · rfl
        · exfalso; exact hm_ne1 (by omega)
      have hcard_eq : Fintype.card sqHom.range = Fintype.card χHom.ker := by rw [hk, hk1, mul_one]
      exact Subgroup.eq_of_le_of_card_ge hsub (by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; exact hcard_eq.ge)
    have hisSq_iff : IsSquare (a : ZMod p) ↔ ha_u.unit ∈ sqHom.range := by
      constructor
      · rintro ⟨x, hx⟩
        have hx_ne : x ≠ 0 := fun h0 => ha0 (by rw [hx, h0, mul_zero])
        refine ⟨(isUnit_iff_ne_zero.mpr hx_ne).unit, Units.ext ?_⟩
        simpa [sqHom, sq] using hx.symm
      · rintro ⟨u, hu⟩
        refine ⟨(u : ZMod p), ?_⟩
        have := congrArg Units.val hu
        simpa [sqHom, sq] using this.symm
    rcases real_char_unit_eq_one_or_neg_one hreal ha_u.unit with h1 | hm1
    · have ha1 : χ (a : ZMod p) = 1 := by simpa using h1
      have hsq : IsSquare (a : ZMod p) := by
        rw [hisSq_iff, hrange_eq_ker, MonoidHom.mem_ker]
        apply Units.ext; simpa [χHom] using h1
      have hleg : legendreSym p (a : ℤ) = 1 :=
        (legendreSym.eq_one_iff p (by exact_mod_cast ha0)).mpr (by exact_mod_cast hsq)
      rw [ha1, hleg]; simp
    · have ham1 : χ (a : ZMod p) = -1 := by simpa using hm1
      have hnsq : ¬ IsSquare (a : ZMod p) := by
        rw [hisSq_iff, hrange_eq_ker, MonoidHom.mem_ker]
        intro hker
        have hv := congrArg Units.val hker
        have h1 : χ (a : ZMod p) = 1 := by simpa [χHom] using hv
        rw [h1] at ham1; norm_num at ham1
      have hleg : legendreSym p (a : ℤ) = -1 :=
        (legendreSym.eq_neg_one_iff p).mpr (by exact_mod_cast hnsq)
      rw [ham1, hleg]; simp

/-- **Odd-Modulus Classification & Exact Gauss Sum**:
for EVERY odd modulus `m ≥ 1` and EVERY real primitive character `χ : DirichletCharacter ℂ m`:
1. `χ (a : ZMod m) = (jacobiSym (a : ℤ) m : ℂ)` for all `a : ℕ`,
2. `χ.Even ↔ m % 4 = 1`,
3. `gaussSum χ ZMod.stdAddChar = (if m % 4 = 1 then (1 : ℂ) else Complex.I) * √m`. -/
theorem odd_real_primitive_jacobi_and_gaussSum :
    ∀ m : ℕ, [NeZero m] → Odd m →
      ∀ (χ : DirichletCharacter ℂ m), χ.IsPrimitive → (∀ a : ZMod m, (χ a).im = 0) →
        (∀ a : ℕ, χ (a : ZMod m) = (jacobiSym (a : ℤ) m : ℂ)) ∧
        (χ.Even ↔ m % 4 = 1) ∧
        gaussSum χ ZMod.stdAddChar =
          (if m % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt (m : ℝ) : ℂ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm_ne hm_odd χ hprim hreal
    by_cases hm1 : m = 1
    · subst hm1
      have hχ1 : χ = 1 := DirichletCharacter.level_one χ
      subst hχ1
      refine ⟨fun a => ?_, ?_, ?_⟩
      · simp [MulChar.one_apply (isUnit_of_subsingleton _)]
      · simp [DirichletCharacter.Even, MulChar.one_apply (isUnit_of_subsingleton _)]
      · simp [gaussSum, -Finset.univ_unique, ← Finset.singleton_eq_univ (0 : ZMod 1),
          MulChar.one_apply (isUnit_of_subsingleton _)]
    · have hm_gt1 : 1 < m := by have := NeZero.pos m; omega
      set p : ℕ := m.minFac
      have hp_prime : p.Prime := Nat.minFac_prime hm1
      have : Fact p.Prime := ⟨hp_prime⟩
      have hp_dvd : p ∣ m := Nat.minFac_dvd m
      have hp2 : p ≠ 2 := by
        intro hp2'
        have h2dvd : 2 ∣ m := hp2' ▸ hp_dvd
        obtain ⟨r, hr⟩ := hm_odd
        omega
      set k : ℕ := m.factorization p
      have hk_pos : 1 ≤ k := by
        have hne : m.factorization p ≠ 0 :=
          (Nat.Prime.dvd_iff_one_le_factorization hp_prime (NeZero.ne m)).mp hp_dvd |> Nat.pos_iff_ne_zero.mp
        omega
      have hpk_dvd : p ^ k ∣ m := Nat.ordProj_dvd m p
      set m' : ℕ := m / p ^ k
      have hm_eq : m = p ^ k * m' := (Nat.mul_div_cancel' hpk_dvd).symm
      have hcop : Nat.Coprime (p ^ k) m' := (Nat.coprime_ordCompl hp_prime (NeZero.ne m)).pow_left k
      have : NeZero (p ^ k) := ⟨pow_ne_zero k hp_prime.ne_zero⟩
      have hm'_pos : 0 < m' := Nat.div_pos (Nat.le_of_dvd (NeZero.pos m) hpk_dvd) (pow_pos hp_prime.pos k)
      have : NeZero m' := ⟨hm'_pos.ne'⟩
      have hm'_odd : Odd m' := by
        rcases Nat.even_or_odd m' with ⟨r, hr⟩ | hodd
        · exfalso
          have h2dvd : 2 ∣ m := ⟨p ^ k * r, by rw [hm_eq, hr]; ring⟩
          obtain ⟨s, hs⟩ := hm_odd
          omega
        · exact hodd
      have hm'_lt : m' < m := by
        have hpk_gt1 : 1 < p ^ k := by
          calc 1 < p := hp_prime.one_lt
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ k := Nat.pow_le_pow_right hp_prime.pos hk_pos
        nlinarith
      -- Apply CRT decomposition via `exists_crt_decomposition_of_eq` (no dependent `subst`!)
      obtain ⟨χ₁, χ₂, hfact_nat, hfact_neg1, hreal12, hprim12, hgauss_crt⟩ :=
        exists_crt_decomposition_of_eq hm_eq hcop χ
      obtain ⟨hreal₁, hreal₂⟩ := hreal12 hreal
      obtain ⟨hprim₁, hprim₂⟩ := hprim12 hprim
      have hk1 : k = 1 := odd_prime_pow_exp_eq_one_of_real_primitive hp_prime hp2 hk_pos hprim₁ hreal₁
      have hpk_eq_p : p ^ k = p := by rw [hk1, pow_one]
      have hm_eq_pm' : m = p * m' := by rw [hm_eq, hpk_eq_p]
      have hχ₁_ne1 : χ₁ ≠ 1 := by
        intro h1
        have hcond : χ₁.conductor = 1 := by rw [h1]; exact DirichletCharacter.conductor_one
        rw [hprim₁, hpk_eq_p] at hcond
        exact hp_prime.ne_one hcond
      obtain ⟨χ₁', hχ₁'_val, _, _, _, hχ₁'_ne1_iff, hχ₁'_real_imp, hgauss₁_eq⟩ :=
        exists_char_eq_of_level_eq hpk_eq_p χ₁
      have hχ₁'_ne1 : χ₁' ≠ 1 := hχ₁'_ne1_iff.mpr hχ₁_ne1
      have hχ₁'_real : ∀ a : ZMod p, (χ₁' a).im = 0 := hχ₁'_real_imp hreal₁
      have hχ₁_jac : ∀ a : ℕ, χ₁ (a : ZMod (p ^ k)) = (jacobiSym (a : ℤ) p : ℂ) := fun a => by
        rw [← hχ₁'_val a, prime_real_char_eq_jacobiSym hp2 hχ₁'_ne1 hχ₁'_real a]
      have hgauss₁ :
          gaussSum χ₁ ZMod.stdAddChar =
            (if p % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt (p : ℝ) : ℂ) := by
        rw [← hgauss₁_eq, gaussSum_prime_real_char hp2 hχ₁'_ne1 hχ₁'_real]
      -- Induction hypothesis on `m' < m`
      obtain ⟨hχ₂_jac, hχ₂_even, hgauss₂⟩ := ih m' hm'_lt hm'_odd χ₂ hprim₂ hreal₂
      -- 1. Jacobi symbol identity for `χ`
      have hχ_jac : ∀ a : ℕ, χ (a : ZMod m) = (jacobiSym (a : ℤ) m : ℂ) := by
        intro a
        rw [hfact_nat a, hχ₁_jac a, hχ₂_jac a, hm_eq_pm', jacobiSym.mul_right (a : ℤ) p m',
          Int.cast_mul]
      -- 2. Parity `χ.Even ↔ m % 4 = 1`
      have hp_odd : p % 2 = 1 := by obtain ⟨t, ht⟩ := hp_prime.odd_of_ne_two hp2; omega
      have hm'_odd_mod : m' % 2 = 1 := by obtain ⟨t, ht⟩ := hm'_odd; omega
      have hχ_neg1 : χ (-1 : ZMod m) = if m % 4 = 1 then 1 else -1 := by
        have hneg_cast : (-1 : ZMod m) = ((m - 1 : ℕ) : ZMod m) := by
          rw [Nat.cast_sub (by have := NeZero.pos m; omega), ZMod.natCast_self, zero_sub, Nat.cast_one]
        rw [hneg_cast, hχ_jac]
        have hmod_neg : ((m - 1 : ℕ) : ℤ) ≡ (-1 : ℤ) [ZMOD (m : ℕ)] := by
          rw [Int.modEq_iff_dvd]
          refine ⟨-1, ?_⟩
          have hpos : 1 ≤ m := NeZero.pos m
          omega
        rw [jacobiSym.mod_left' hmod_neg, jacobiSym.at_neg_one hm_odd]
        have hodd_m : m % 2 = 1 := by obtain ⟨t, ht⟩ := hm_odd; omega
        have hcases : m % 4 = 1 ∨ m % 4 = 3 := by omega
        rcases hcases with h1 | h3
        · rw [if_pos h1]
          have h4 : ((m : ℕ) : ZMod 4) = 1 := by
            rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact h1
          have hχ4_1 : ZMod.χ₄ (1 : ZMod 4) = 1 := by decide
          rw [h4, hχ4_1]; norm_num
        · rw [if_neg (by omega)]
          have h4 : ((m : ℕ) : ZMod 4) = 3 := by
            rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact h3
          have hχ4_3 : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
          rw [h4, hχ4_3]; norm_num
      have hχ_even : χ.Even ↔ m % 4 = 1 := by
        show χ (-1 : ZMod m) = 1 ↔ m % 4 = 1
        rw [hχ_neg1]
        split_ifs with h
        · simp [h]
        · constructor
          · intro h0; norm_num at h0
          · intro h1; exact absurd h1 h
      -- 3. Gauss sum identity via Quadratic Reciprocity!
      have hgauss_all :
          gaussSum χ ZMod.stdAddChar =
            (if m % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt (m : ℝ) : ℂ) := by
        rw [hgauss_crt, hχ₁_jac m', hχ₂_jac (p ^ k), hgauss₁, hgauss₂]
        rw [show (jacobiSym ((p ^ k : ℕ) : ℤ) m' : ℂ) = (jacobiSym (p : ℤ) m' : ℂ) by rw [hpk_eq_p]]
        have hsqrt_mul :
            (Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt (m' : ℝ) : ℂ) = (Real.sqrt (m : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Real.sqrt_mul (Nat.cast_nonneg p), ← Nat.cast_mul, ← hm_eq_pm']
        have hcop_pm' : Nat.Coprime p m' := by rwa [hpk_eq_p] at hcop
        have hjac_sq : (jacobiSym (p : ℤ) m' : ℂ) * (jacobiSym (p : ℤ) m' : ℂ) = 1 := by
          have hne0 : jacobiSym (p : ℤ) m' ≠ 0 := by
            intro h0
            have hgcd : Int.gcd (p : ℤ) m' ≠ 1 := ((jacobiSym.eq_zero_iff).mp h0).2
            exact hgcd (by simpa using hcop_pm')
          rcases jacobiSym.trichotomy (p : ℤ) m' with h0 | h1 | hm1
          · exact absurd h0 hne0
          · rw [h1]; norm_num
          · rw [hm1]; norm_num
        have hqr :
            (jacobiSym (m' : ℤ) p : ℂ) * (jacobiSym (p : ℤ) m' : ℂ) =
              if p % 4 = 3 ∧ m' % 4 = 3 then -1 else 1 := by
          have hp_cases : p % 4 = 1 ∨ p % 4 = 3 := by omega
          have hm'_cases : m' % 4 = 1 ∨ m' % 4 = 3 := by omega
          rcases hp_cases with hp1 | hp3
          · rw [if_neg (by omega), jacobiSym.quadratic_reciprocity_one_mod_four' hm'_odd hp1,
              hjac_sq]
          · rcases hm'_cases with hm1' | hm3'
            · rw [if_neg (by omega), jacobiSym.quadratic_reciprocity_one_mod_four hm1'
                (hp_prime.odd_of_ne_two hp2), hjac_sq]
            · rw [if_pos ⟨hp3, hm3'⟩, jacobiSym.quadratic_reciprocity_three_mod_four hm3' hp3,
                Int.cast_neg, neg_mul, hjac_sq]
        have hrearr :
            (jacobiSym (m' : ℤ) p : ℂ) * (jacobiSym (p : ℤ) m' : ℂ) *
                ((if p % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt (p : ℝ) : ℂ)) *
                ((if m' % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt (m' : ℝ) : ℂ)) =
              ((jacobiSym (m' : ℤ) p : ℂ) * (jacobiSym (p : ℤ) m' : ℂ) *
                (if p % 4 = 1 then (1 : ℂ) else Complex.I) *
                (if m' % 4 = 1 then (1 : ℂ) else Complex.I)) *
                ((Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt (m' : ℝ) : ℂ)) := by ring
        rw [hrearr, hsqrt_mul, hqr]
        congr 1
        have hmod_prod : m % 4 = (p % 4 * (m' % 4)) % 4 := by rw [hm_eq_pm', Nat.mul_mod]
        have hp_cases : p % 4 = 1 ∨ p % 4 = 3 := by omega
        have hm'_cases : m' % 4 = 1 ∨ m' % 4 = 3 := by omega
        rcases hp_cases with hp1 | hp3 <;> rcases hm'_cases with hm1' | hm3'
        · rw [hp1, hm1'] at hmod_prod
          rw [if_neg (by omega), if_pos hp1, if_pos hm1', if_pos (by omega)]; ring
        · rw [hp1, hm3'] at hmod_prod
          rw [if_neg (by omega), if_pos hp1, if_neg (by omega), if_neg (by omega)]; ring
        · rw [hp3, hm1'] at hmod_prod
          rw [if_neg (by omega), if_neg (by omega), if_pos hm1', if_neg (by omega)]; ring
        · rw [hp3, hm3'] at hmod_prod
          rw [if_pos ⟨hp3, hm3'⟩, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          calc (-1 : ℂ) * Complex.I * Complex.I = -(Complex.I * Complex.I) := by ring
            _ = -(-1) := by rw [Complex.I_mul_I]
            _ = 1 := by ring
      exact ⟨hχ_jac, hχ_even, hgauss_all⟩

/-- Explicit Gauss sum for the unique real primitive character mod `4`: `τ(χ₄) = 2 * I = I * √4`. -/
private lemma gaussSum_mod4_real_primitive {χ : DirichletCharacter ℂ 4}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod 4, (χ a).im = 0) :
    χ.Odd ∧
      (∀ m : ℕ, Odd m → χ (m : ZMod 4) = if m % 4 = 1 then 1 else -1) ∧
      gaussSum χ ZMod.stdAddChar = Complex.I * (Real.sqrt (4 : ℝ) : ℂ) := by
  have hχ_ne1 : χ ≠ 1 := by
    intro h1
    have hcond : χ.conductor = 1 := by rw [h1]; exact DirichletCharacter.conductor_one
    rw [hprim] at hcond; norm_num at hcond
  have hχ3 : χ (3 : ZMod 4) = -1 := by
    have h3u : IsUnit (3 : ZMod 4) := (ZMod.isUnit_iff_coprime 3 4).mpr (by decide)
    rcases real_char_unit_eq_one_or_neg_one hreal h3u.unit with h1 | hm1
    · exfalso
      apply hχ_ne1
      ext u
      have hu : u = 1 ∨ u = h3u.unit := by
        have hval : (u : ZMod 4) = 1 ∨ (u : ZMod 4) = 3 := by
          fin_cases u <;> decide
        rcases hval with h | h
        · left; exact Units.ext h
        · right; exact Units.ext h
      rcases hu with rfl | rfl
      · simp
      · simpa [MulChar.one_apply h3u] using h1
    · simpa using hm1
  have hodd : χ.Odd := by
    show χ (-1 : ZMod 4) = -1
    have hneg1 : (-1 : ZMod 4) = 3 := by decide
    rw [hneg1, hχ3]
  have hval_odd : ∀ m : ℕ, Odd m → χ (m : ZMod 4) = if m % 4 = 1 then 1 else -1 := by
    intro m hm
    obtain ⟨t, ht⟩ := hm
    have hcases : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hcases with h1 | h3
    · rw [if_pos h1]
      have hm1 : (m : ZMod 4) = 1 := by rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact h1
      rw [hm1, map_one]
    · rw [if_neg (by omega)]
      have hm3 : (m : ZMod 4) = 3 := by rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact h3
      rw [hm3, hχ3]
  have hgauss : gaussSum χ ZMod.stdAddChar = Complex.I * (Real.sqrt (4 : ℝ) : ℂ) := by
    have hsum : gaussSum χ ZMod.stdAddChar =
        χ (0 : ZMod 4) * ZMod.stdAddChar (0 : ZMod 4) +
        χ (1 : ZMod 4) * ZMod.stdAddChar (1 : ZMod 4) +
        χ (2 : ZMod 4) * ZMod.stdAddChar (2 : ZMod 4) +
        χ (3 : ZMod 4) * ZMod.stdAddChar (3 : ZMod 4) := by
      unfold gaussSum
      have huniv : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
      rw [huniv]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
        show (0 : ZMod 4) ≠ 1 by decide, show (0 : ZMod 4) ≠ 2 by decide,
        show (0 : ZMod 4) ≠ 3 by decide, show (1 : ZMod 4) ≠ 2 by decide,
        show (1 : ZMod 4) ≠ 3 by decide, show (2 : ZMod 4) ≠ 3 by decide,
        or_self, not_false_eq_true]
      ring
    have h0 : χ (0 : ZMod 4) = 0 := χ.map_zero' (by norm_num)
    have h2 : χ (2 : ZMod 4) = 0 :=
      MulChar.map_nonunit χ (fun hu => by
        have := (ZMod.isUnit_iff_coprime 2 4).mp hu; norm_num at this)
    have he1 : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
      rw [show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by rfl, stdAddChar_natCast_eq_e]
      unfold e
      have harg : 2 * (Real.pi : ℂ) * Complex.I * ((((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) : ℝ) : ℂ) =
          (Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_pi_div_two_mul_I]
    have he3 : ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
      rw [show (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) by rfl, stdAddChar_natCast_eq_e]
      unfold e
      have harg : 2 * (Real.pi : ℂ) * Complex.I * ((((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) : ℝ) : ℂ) =
          (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) + -(Real.pi : ℂ) / 2 * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
        Complex.exp_neg_pi_div_two_mul_I]
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsum, h0, h2, map_one, hχ3, he1, he3, hsqrt4]
    push_cast; ring
  exact ⟨hodd, hval_odd, hgauss⟩

open Classical in
/-- Explicit Gauss sums for the two real primitive characters mod `8`:
- Even (`χ(3) = -1, χ(5) = -1, χ(7) = 1`): `χ(m) = χ₈(m)` and `τ(χ) = √8`.
- Odd (`χ(3) = 1, χ(5) = -1, χ(7) = -1`): `χ(m) = χ₄(m) * χ₈(m)` and `τ(χ) = I * √8`. -/
private lemma gaussSum_mod8_real_primitive {χ : DirichletCharacter ℂ 8}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod 8, (χ a).im = 0) :
    (∀ m : ℕ, Odd m →
        χ (m : ZMod 8) = (if χ.Even then (1 : ℂ) else (if m % 4 = 1 then 1 else -1)) *
          (jacobiSym 2 m : ℂ)) ∧
      gaussSum χ ZMod.stdAddChar =
        (if χ.Even then (1 : ℂ) else Complex.I) * (Real.sqrt (8 : ℝ) : ℂ) := by
  have h5u : IsUnit (5 : ZMod 8) := (ZMod.isUnit_iff_coprime 5 8).mpr (by decide)
  have h7u : IsUnit (7 : ZMod 8) := (ZMod.isUnit_iff_coprime 7 8).mpr (by decide)
  -- `χ 5 = -1` because `χ` does NOT factor through `4`
  have hχ5 : χ (5 : ZMod 8) = -1 := by
    rcases real_char_unit_eq_one_or_neg_one hreal h5u.unit with h1 | hm1
    · exfalso
      have hfac4 : χ.FactorsThrough 4 := by
        rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (by norm_num : 4 ∣ 8)]
        intro u hu
        rw [MonoidHom.mem_ker] at hu ⊢
        have hu15 : u = 1 ∨ u = h5u.unit := by
          have hv := congrArg Units.val hu
          have hmod : (u : ZMod 8).val % 4 = 1 := by
            have hcast : ((u : ZMod 8).val : ZMod 4) = 1 := by
              have h1 : ZMod.cast (u : ZMod 8) = (1 : ZMod 4) := by
                simpa [ZMod.unitsMap_def] using hv
              rwa [ZMod.cast_eq_val] at h1
            have hm := (ZMod.natCast_eq_natCast_iff (u : ZMod 8).val 1 4).mp (by simpa using hcast)
            simpa [Nat.ModEq] using hm
          have hlt : (u : ZMod 8).val < 8 := ZMod.val_lt _
          have h15 : (u : ZMod 8).val = 1 ∨ (u : ZMod 8).val = 5 := by omega
          rcases h15 with h | h
          · left; apply Units.ext; rw [← ZMod.natCast_zmod_val (u : ZMod 8), h]; rfl
          · right; apply Units.ext; rw [← ZMod.natCast_zmod_val (u : ZMod 8), h]; rfl
        rcases hu15 with rfl | rfl
        · simp
        · apply Units.ext; simpa [MulChar.coe_toUnitHom] using h1
      have hdvd : χ.conductor ∣ 4 :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ (by norm_num : 4 ∣ 8)).mp hfac4
      rw [hprim] at hdvd; norm_num at hdvd
    · simpa using hm1
  have hχ7_cases : χ (7 : ZMod 8) = 1 ∨ χ (7 : ZMod 8) = -1 := by
    simpa using real_char_unit_eq_one_or_neg_one hreal h7u.unit
  have hneg1_eq7 : (-1 : ZMod 8) = 7 := by decide
  have h3_eq : (3 : ZMod 8) = 5 * 7 := by decide
  have hχ3 : χ (3 : ZMod 8) = -χ (7 : ZMod 8) := by
    rw [h3_eq, map_mul, hχ5]; ring
  -- Evaluate `e(1/8), e(3/8), e(5/8), e(7/8)`
  have he1 : ZMod.stdAddChar (1 : ZMod 8) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
    rw [show (1 : ZMod 8) = ((1 : ℕ) : ZMod 8) by rfl, stdAddChar_natCast_eq_e]
    unfold e
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) : ℝ) : ℂ) =
      (((Real.pi / 4 : ℝ) : ℂ)) * Complex.I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring
  have he3 : ZMod.stdAddChar (3 : ZMod 8) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (-1 + Complex.I) := by
    rw [show (3 : ZMod 8) = ((3 : ℕ) : ZMod 8) by rfl, stdAddChar_natCast_eq_e]
    unfold e
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((((3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) : ℝ) : ℂ) =
      (Real.pi : ℂ) / 2 * Complex.I + (((Real.pi / 4 : ℝ) : ℂ)) * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_div_two_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    calc Complex.I * (↑(Real.sqrt 2) / 2 + ↑(Real.sqrt 2) / 2 * Complex.I)
        = ↑(Real.sqrt 2) / 2 * Complex.I + ↑(Real.sqrt 2) / 2 * (Complex.I * Complex.I) := by ring
      _ = ↑(Real.sqrt 2) / 2 * Complex.I + ↑(Real.sqrt 2) / 2 * (-1) := by rw [Complex.I_mul_I]
      _ = ↑(Real.sqrt 2) / 2 * (-1 + Complex.I) := by ring
  have he5 : ZMod.stdAddChar (5 : ZMod 8) = -ZMod.stdAddChar (1 : ZMod 8) := by
    have h51 : (5 : ZMod 8) = 4 + 1 := by decide
    rw [h51, AddChar.map_add_eq_mul]
    have he4 : ZMod.stdAddChar (4 : ZMod 8) = -1 := by
      rw [show (4 : ZMod 8) = ((4 : ℕ) : ZMod 8) by rfl, stdAddChar_natCast_eq_e]
      unfold e
      rw [show 2 * (Real.pi : ℂ) * Complex.I * ((((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) : ℝ) : ℂ) =
        (Real.pi : ℂ) * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
    rw [he4]; ring
  have he7 : ZMod.stdAddChar (7 : ZMod 8) = -ZMod.stdAddChar (3 : ZMod 8) := by
    have h73 : (7 : ZMod 8) = 4 + 3 := by decide
    rw [h73, AddChar.map_add_eq_mul]
    have he4 : ZMod.stdAddChar (4 : ZMod 8) = -1 := by
      rw [show (4 : ZMod 8) = ((4 : ℕ) : ZMod 8) by rfl, stdAddChar_natCast_eq_e]
      unfold e
      rw [show 2 * (Real.pi : ℂ) * Complex.I * ((((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) : ℝ) : ℂ) =
        (Real.pi : ℂ) * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
    rw [he4]; ring
  have hsum8 : gaussSum χ ZMod.stdAddChar =
      ZMod.stdAddChar (1 : ZMod 8) + χ (3 : ZMod 8) * ZMod.stdAddChar (3 : ZMod 8) +
      χ (5 : ZMod 8) * ZMod.stdAddChar (5 : ZMod 8) + χ (7 : ZMod 8) * ZMod.stdAddChar (7 : ZMod 8) := by
    unfold gaussSum
    have h8 : ∑ x : ZMod 8, χ x * ZMod.stdAddChar x =
        χ (0 : ZMod 8) * ZMod.stdAddChar (0 : ZMod 8) + χ (1 : ZMod 8) * ZMod.stdAddChar (1 : ZMod 8) +
        χ (2 : ZMod 8) * ZMod.stdAddChar (2 : ZMod 8) + χ (3 : ZMod 8) * ZMod.stdAddChar (3 : ZMod 8) +
        χ (4 : ZMod 8) * ZMod.stdAddChar (4 : ZMod 8) + χ (5 : ZMod 8) * ZMod.stdAddChar (5 : ZMod 8) +
        χ (6 : ZMod 8) * ZMod.stdAddChar (6 : ZMod 8) + χ (7 : ZMod 8) * ZMod.stdAddChar (7 : ZMod 8) := by
      have huniv : (Finset.univ : Finset (ZMod 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide
      rw [huniv]
      have h0 : (0 : ZMod 8) ∉ ({1, 2, 3, 4, 5, 6, 7} : Finset (ZMod 8)) := by decide
      have h1 : (1 : ZMod 8) ∉ ({2, 3, 4, 5, 6, 7} : Finset (ZMod 8)) := by decide
      have h2 : (2 : ZMod 8) ∉ ({3, 4, 5, 6, 7} : Finset (ZMod 8)) := by decide
      have h3 : (3 : ZMod 8) ∉ ({4, 5, 6, 7} : Finset (ZMod 8)) := by decide
      have h4 : (4 : ZMod 8) ∉ ({5, 6, 7} : Finset (ZMod 8)) := by decide
      have h5 : (5 : ZMod 8) ∉ ({6, 7} : Finset (ZMod 8)) := by decide
      have h6 : (6 : ZMod 8) ∉ ({7} : Finset (ZMod 8)) := by decide
      rw [Finset.sum_insert h0, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
        Finset.sum_insert h4, Finset.sum_insert h5, Finset.sum_insert h6, Finset.sum_singleton]
      ring
    have h0 : χ (0 : ZMod 8) = 0 := χ.map_zero' (by norm_num)
    have h2 : χ (2 : ZMod 8) = 0 := MulChar.map_nonunit χ (fun hu => by have := (ZMod.isUnit_iff_coprime 2 8).mp hu; norm_num at this)
    have h4 : χ (4 : ZMod 8) = 0 := MulChar.map_nonunit χ (fun hu => by have := (ZMod.isUnit_iff_coprime 4 8).mp hu; norm_num at this)
    have h6 : χ (6 : ZMod 8) = 0 := MulChar.map_nonunit χ (fun hu => by have := (ZMod.isUnit_iff_coprime 6 8).mp hu; norm_num at this)
    rw [h8, h0, h2, h4, h6, map_one]; ring
  have hsqrt8 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hχ8_1 : ZMod.χ₈ (1 : ZMod 8) = 1 := by decide
  have hχ8_3 : ZMod.χ₈ (3 : ZMod 8) = -1 := by decide
  have hχ8_5 : ZMod.χ₈ (5 : ZMod 8) = -1 := by decide
  have hχ8_7 : ZMod.χ₈ (7 : ZMod 8) = 1 := by decide
  constructor
  · intro m hm
    obtain ⟨t, ht⟩ := hm
    rw [jacobiSym.at_two ⟨t, ht⟩]
    have hmod8 : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
    rcases hχ7_cases with h7 | h7
    · have heven : χ.Even := by show χ (-1 : ZMod 8) = 1; rw [hneg1_eq7, h7]
      rw [if_pos heven, one_mul]
      rcases hmod8 with h | h | h | h
      · have hm8 : (m : ZMod 8) = 1 := by rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact h
        rw [hm8, map_one, hχ8_1]; norm_num
      · have hm8 : (m : ZMod 8) = 3 := by rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact h
        rw [hm8, hχ3, h7, hχ8_3]; norm_num
      · have hm8 : (m : ZMod 8) = 5 := by rw [← Nat.cast_ofNat (n := 5), ZMod.natCast_eq_natCast_iff]; exact h
        rw [hm8, hχ5, hχ8_5]; norm_num
      · have hm8 : (m : ZMod 8) = 7 := by rw [← Nat.cast_ofNat (n := 7), ZMod.natCast_eq_natCast_iff]; exact h
        rw [hm8, h7, hχ8_7]; norm_num
    · have hneven : ¬ χ.Even := by
        intro he; have : χ (-1 : ZMod 8) = 1 := he; rw [hneg1_eq7, h7] at this; norm_num at this
      rw [if_neg hneven]
      rcases hmod8 with h | h | h | h
      · have hm8 : (m : ZMod 8) = 1 := by rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact h
        rw [hm8, map_one, if_pos (by omega), hχ8_1]; norm_num
      · have hm8 : (m : ZMod 8) = 3 := by rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; exact h
        rw [hm8, hχ3, h7, if_neg (by omega), hχ8_3]; norm_num
      · have hm8 : (m : ZMod 8) = 5 := by rw [← Nat.cast_ofNat (n := 5), ZMod.natCast_eq_natCast_iff]; exact h
        rw [hm8, hχ5, if_pos (by omega), hχ8_5]; norm_num
      · have hm8 : (m : ZMod 8) = 7 := by rw [← Nat.cast_ofNat (n := 7), ZMod.natCast_eq_natCast_iff]; exact h
        rw [hm8, h7, if_neg (by omega), hχ8_7]; norm_num
  · rcases hχ7_cases with h7 | h7
    · have heven : χ.Even := by show χ (-1 : ZMod 8) = 1; rw [hneg1_eq7, h7]
      rw [if_pos heven, one_mul, hsum8, hχ3, hχ5, h7, he5, he7, he1, he3, hsqrt8]
      push_cast; ring
    · have hneven : ¬ χ.Even := by
        intro he; have : χ (-1 : ZMod 8) = 1 := he; rw [hneg1_eq7, h7] at this; norm_num at this
      rw [if_neg hneven, hsum8, hχ3, hχ5, h7, he5, he7, he1, he3, hsqrt8]
      push_cast; ring

open Classical in
/-- **GAUSS'S FULL QUADRATIC GAUSS-SUM SIGN THEOREM (ALL MODULI `q ≥ 1`)**:
for EVERY modulus `q ≥ 1` (prime OR composite!) and EVERY real primitive character
`χ : DirichletCharacter ℂ q`:
- if `χ` is even: `τ(χ) = +√q`,
- if `χ` is odd: `τ(χ) = +I * √q`. -/
theorem gaussSum_real_primitive_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    gaussSum χ ZMod.stdAddChar =
      (if χ.Even then (1 : ℂ) else Complex.I) * (Real.sqrt (q : ℝ) : ℂ) := by
  set k : ℕ := q.factorization 2
  have h2k_dvd : 2 ^ k ∣ q := Nat.ordProj_dvd q 2
  set m : ℕ := q / 2 ^ k
  have hq_eq : q = 2 ^ k * m := (Nat.mul_div_cancel' h2k_dvd).symm
  have hcop : Nat.Coprime (2 ^ k) m :=
    (Nat.coprime_ordCompl (by norm_num : Nat.Prime 2) (NeZero.ne q)).pow_left k
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) h2k_dvd) (pow_pos (by norm_num) k)
  have : NeZero m := ⟨hm_pos.ne'⟩
  have hm_odd : Odd m := by
    have hcop2 : Nat.Coprime 2 m :=
      Nat.coprime_ordCompl (by norm_num : Nat.Prime 2) (NeZero.ne q)
    have hnot2 : ¬ 2 ∣ m := (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mp hcop2
    exact Nat.odd_iff.mpr (by omega)
  obtain ⟨χ₁, χ₂, _, hneg1, hreal12, hprim12, hgauss_crt⟩ :=
    exists_crt_decomposition_of_eq hq_eq hcop χ
  obtain ⟨hreal₁, hreal₂⟩ := hreal12 hreal
  obtain ⟨hprim₁, hprim₂⟩ := hprim12 hprim
  obtain ⟨hχ₂_jac, hχ₂_even, hgauss₂⟩ := odd_real_primitive_jacobi_and_gaussSum m hm_odd χ₂ hprim₂ hreal₂
  have hsqrt_mul :
      (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) * (Real.sqrt (m : ℝ) : ℂ) = (Real.sqrt (q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, ← hq_eq]
  rcases two_pow_exp_mem_of_real_primitive hprim₁ hreal₁ with hk0 | hk2 | hk3
  · -- `k = 0`: `2 ^ 0 = 1`, pure odd modulus `m`
    have h2k_eq1 : 2 ^ k = 1 := by rw [hk0, pow_zero]
    have hq_eq_m : q = m := by rw [hq_eq, h2k_eq1, one_mul]
    have hsub1 : Subsingleton (ZMod (2 ^ k)) := by rw [h2k_eq1]; infer_instance
    have hχ₁_1 : ∀ x : ZMod (2 ^ k), χ₁ x = 1 := fun x => by
      have : x = 1 := Subsingleton.elim x 1
      rw [this, map_one]
    have hg1 : gaussSum χ₁ ZMod.stdAddChar = 1 := by
      unfold gaussSum
      have huniv : (Finset.univ : Finset (ZMod (2 ^ k))) = {0} := by
        ext x; simp [Subsingleton.elim x 0]
      rw [huniv, Finset.sum_singleton, hχ₁_1 0, AddChar.map_zero_eq_one, mul_one]
    have hχ₂_1 : χ₂ ((2 ^ k : ℕ) : ZMod m) = 1 := by rw [h2k_eq1, Nat.cast_one, map_one]
    have heven_iff : χ.Even ↔ m % 4 = 1 := by
      rw [← hχ₂_even]
      show χ (-1 : ZMod q) = 1 ↔ χ₂ (-1 : ZMod m) = 1
      rw [hneg1, hχ₁_1 (-1), one_mul]
    rw [hgauss_crt, hχ₁_1 m, hχ₂_1, hg1, hgauss₂,
      show (Real.sqrt (q : ℝ) : ℂ) = (Real.sqrt (m : ℝ) : ℂ) by rw [hq_eq_m]]
    have hiff : (if χ.Even then (1 : ℂ) else Complex.I) =
        if m % 4 = 1 then (1 : ℂ) else Complex.I := by
      by_cases h : m % 4 = 1
      · rw [if_pos (heven_iff.mpr h), if_pos h]
      · rw [if_neg (mt heven_iff.mp h), if_neg h]
    rw [hiff]
    ring
  · -- `k = 2`: `2 ^ 2 = 4`
    have h2k_eq4 : 2 ^ k = 4 := by rw [hk2]; norm_num
    obtain ⟨χ₁', hχ₁'_val, hχ₁'_neg1, _, hχ₁'_prim_iff, _, hχ₁'_real_imp, hgauss₁_eq⟩ :=
      exists_char_eq_of_level_eq h2k_eq4 χ₁
    obtain ⟨hodd₁', hval₁', hgauss₁'⟩ :=
      gaussSum_mod4_real_primitive (hχ₁'_prim_iff.mpr hprim₁) (hχ₁'_real_imp hreal₁)
    have hodd₁ : χ₁ (-1 : ZMod (2 ^ k)) = -1 := by rw [← hχ₁'_neg1]; exact hodd₁'
    have hgauss₁ : gaussSum χ₁ ZMod.stdAddChar = Complex.I * (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) := by
      rw [← hgauss₁_eq, hgauss₁', h2k_eq4]; norm_num
    have hχ₂_4 : χ₂ ((2 ^ k : ℕ) : ZMod m) = 1 := by
      rw [h2k_eq4]
      have h2u : IsUnit (2 : ZMod m) :=
        (ZMod.isUnit_iff_coprime 2 m).mpr (by
          obtain ⟨t, ht⟩ := hm_odd
          exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega))
      rw [show ((4 : ℕ) : ZMod m) = (2 : ZMod m) ^ 2 by norm_num, map_pow]
      rcases real_char_unit_eq_one_or_neg_one hreal₂ h2u.unit with h1 | hm1
      · have : χ₂ (2 : ZMod m) = 1 := by simpa using h1
        rw [this, one_pow]
      · have : χ₂ (2 : ZMod m) = -1 := by simpa using hm1
        rw [this]; norm_num
    rw [hgauss_crt, ← hχ₁'_val m, hval₁' m hm_odd, hχ₂_4, hgauss₁, hgauss₂]
    have hrearr :
        (if m % 4 = 1 then (1 : ℂ) else -1) * 1 * (Complex.I * (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ)) *
            ((if m % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt (m : ℝ) : ℂ)) =
          ((if m % 4 = 1 then (1 : ℂ) else -1) * Complex.I *
            (if m % 4 = 1 then (1 : ℂ) else Complex.I)) *
            ((Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) * (Real.sqrt (m : ℝ) : ℂ)) := by ring
    rw [hrearr, hsqrt_mul]
    congr 1
    by_cases hm4 : m % 4 = 1
    · have hχ₂_e : χ₂ (-1 : ZMod m) = 1 := hχ₂_even.mpr hm4
      have hne : ¬ χ.Even := by
        intro he
        have : χ (-1 : ZMod q) = 1 := he
        rw [hneg1, hodd₁, hχ₂_e] at this; norm_num at this
      simp only [hm4, hne, ite_true, ite_false]; ring
    · have hχ₂_o : χ₂ (-1 : ZMod m) = -1 := by
        rcases χ₂.even_or_odd with he | ho
        · exfalso; exact hm4 (hχ₂_even.mp he)
        · exact ho
      have he : χ.Even := by
        show χ (-1 : ZMod q) = 1
        rw [hneg1, hodd₁, hχ₂_o]; ring
      simp only [hm4, he, ite_true, ite_false]
      calc (-1 : ℂ) * Complex.I * Complex.I = -(Complex.I * Complex.I) := by ring
        _ = -(-1) := by rw [Complex.I_mul_I]
        _ = 1 := by ring
  · -- `k = 3`: `2 ^ 3 = 8`
    have h2k_eq8 : 2 ^ k = 8 := by rw [hk3]; norm_num
    obtain ⟨χ₁', hχ₁'_val, hχ₁'_neg1, _, hχ₁'_prim_iff, _, hχ₁'_real_imp, hgauss₁_eq⟩ :=
      exists_char_eq_of_level_eq h2k_eq8 χ₁
    obtain ⟨hval₁', hgauss₁'⟩ :=
      gaussSum_mod8_real_primitive (hχ₁'_prim_iff.mpr hprim₁) (hχ₁'_real_imp hreal₁)
    have hneg1_1 : χ₁ (-1 : ZMod (2 ^ k)) = χ₁' (-1 : ZMod 8) := hχ₁'_neg1.symm
    have hgauss₁ :
        gaussSum χ₁ ZMod.stdAddChar =
          (if χ₁'.Even then (1 : ℂ) else Complex.I) * (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) := by
      rw [← hgauss₁_eq, hgauss₁', h2k_eq8]; norm_num
    have hχ₂_8 : χ₂ ((2 ^ k : ℕ) : ZMod m) = (jacobiSym 2 m : ℂ) := by
      rw [h2k_eq8]
      have h2u : IsUnit (2 : ZMod m) :=
        (ZMod.isUnit_iff_coprime 2 m).mpr (by
          obtain ⟨t, ht⟩ := hm_odd
          exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega))
      have hsq : χ₂ (2 : ZMod m) ^ 2 = 1 := by
        rcases real_char_unit_eq_one_or_neg_one hreal₂ h2u.unit with h1 | hm1
        · have : χ₂ (2 : ZMod m) = 1 := by simpa using h1
          rw [this, one_pow]
        · have : χ₂ (2 : ZMod m) = -1 := by simpa using hm1
          rw [this]; norm_num
      have h8 : ((8 : ℕ) : ZMod m) = (2 : ZMod m) ^ 2 * (2 : ZMod m) := by norm_num
      rw [h8, map_mul, map_pow, hsq, one_mul]
      simpa using hχ₂_jac 2
    have hjac2_sq : (jacobiSym 2 m : ℂ) * (jacobiSym 2 m : ℂ) = 1 := by
      have hne0 : jacobiSym 2 m ≠ 0 := by
        intro h0
        have hgcd := ((jacobiSym.eq_zero_iff).mp h0).2
        obtain ⟨t, ht⟩ := hm_odd
        have hcop2 : Nat.Coprime 2 m :=
          (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by omega)
        exact hgcd (by exact_mod_cast hcop2.gcd_eq_one)
      rcases jacobiSym.trichotomy 2 m with h0 | h1 | hm1
      · exact absurd h0 hne0
      · rw [h1]; norm_num
      · rw [hm1]; norm_num
    rw [hgauss_crt, ← hχ₁'_val m, hval₁' m hm_odd, hχ₂_8, hgauss₁, hgauss₂]
    have hrearr :
        (if χ₁'.Even then (1 : ℂ) else if m % 4 = 1 then 1 else -1) * (jacobiSym 2 m : ℂ) *
            (jacobiSym 2 m : ℂ) *
            ((if χ₁'.Even then (1 : ℂ) else Complex.I) * (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ)) *
            ((if m % 4 = 1 then (1 : ℂ) else Complex.I) * (Real.sqrt (m : ℝ) : ℂ)) =
          ((if χ₁'.Even then (1 : ℂ) else if m % 4 = 1 then 1 else -1) *
            ((jacobiSym 2 m : ℂ) * (jacobiSym 2 m : ℂ)) *
            (if χ₁'.Even then (1 : ℂ) else Complex.I) *
            (if m % 4 = 1 then (1 : ℂ) else Complex.I)) *
            ((Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) * (Real.sqrt (m : ℝ) : ℂ)) := by ring
    rw [hrearr, hjac2_sq, hsqrt_mul]
    congr 1
    by_cases h1e : χ₁'.Even
    · by_cases hm4 : m % 4 = 1
      · have hχ₂_e : χ₂ (-1 : ZMod m) = 1 := hχ₂_even.mpr hm4
        have he : χ.Even := by
          show χ (-1 : ZMod q) = 1
          rw [hneg1, hneg1_1, h1e, hχ₂_e, one_mul]
        simp only [h1e, hm4, he, ite_true]; ring
      · have hχ₂_o : χ₂ (-1 : ZMod m) = -1 := by
          rcases χ₂.even_or_odd with he | ho
          · exfalso; exact hm4 (hχ₂_even.mp he)
          · exact ho
        have hne : ¬ χ.Even := by
          intro he
          have : χ (-1 : ZMod q) = 1 := he
          rw [hneg1, hneg1_1, h1e, hχ₂_o] at this; norm_num at this
        simp only [h1e, hm4, hne, ite_true, ite_false]; ring
    · have h1o : χ₁' (-1 : ZMod 8) = -1 := χ₁'.even_or_odd.resolve_left h1e
      by_cases hm4 : m % 4 = 1
      · have hχ₂_e : χ₂ (-1 : ZMod m) = 1 := hχ₂_even.mpr hm4
        have hne : ¬ χ.Even := by
          intro he
          have : χ (-1 : ZMod q) = 1 := he
          rw [hneg1, hneg1_1, h1o, hχ₂_e] at this; norm_num at this
        simp only [h1e, hm4, hne, ite_true, ite_false]; ring
      · have hχ₂_o : χ₂ (-1 : ZMod m) = -1 := by
          rcases χ₂.even_or_odd with he | ho
          · exfalso; exact hm4 (hχ₂_even.mp he)
          · exact ho
        have he : χ.Even := by
          show χ (-1 : ZMod q) = 1
          rw [hneg1, hneg1_1, h1o, hχ₂_o]; ring
        simp only [h1e, hm4, he, ite_true, ite_false]
        calc (-1 : ℂ) * 1 * Complex.I * Complex.I = -(Complex.I * Complex.I) := by ring
          _ = -(-1) := by rw [Complex.I_mul_I]
          _ = 1 := by ring

/-- **EXACT FINITE `L(1, χ)` FORMULA FOR EVERY ODD REAL PRIMITIVE CHARACTER `χ mod q`**
(0 extra assumptions — Gauss-sum sign proved unconditionally!):
`(LFunction χ 1).re = -(π / (q * √q)) * ∑_{a=1}^{q-1} a * (χ a).re`. -/
theorem re_LFunction_one_eq_odd_real_primitive {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    (DirichletCharacter.LFunction χ 1).re =
      -(Real.pi / ((q : ℝ) * Real.sqrt (q : ℝ))) *
        ∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re := by
  have hχ : χ ≠ 1 := by
    intro h1
    have : χ (-1 : ZMod q) = 1 := by rw [h1]; exact MulChar.one_apply isUnit_one.neg
    have ho : χ (-1 : ZMod q) = -1 := hodd
    rw [this] at ho; norm_num at ho
  have hgauss : gaussSum χ ZMod.stdAddChar = Complex.I * (Real.sqrt (q : ℝ) : ℂ) := by
    have h := gaussSum_real_primitive_eq hprim hreal
    rwa [if_neg hodd.not_even] at h
  exact re_LFunction_one_eq_odd_real_of_gaussSum hprim hχ hodd hreal hgauss

/-- **UNCONDITIONAL DIRICHLET NON-VANISHING SIGN THEOREM FOR EVERY ODD REAL PRIMITIVE `χ mod q`**
(arbitrary prime or composite modulus `q`, 0 assumptions!):
`∑_{a=1}^{q-1} a * (χ a).re < 0`. -/
theorem dirichlet_sign_theorem_odd_real_primitive {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hodd : χ.Odd)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    ∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re < 0 := by
  have hχ : χ ≠ 1 := by
    intro h1
    have : χ (-1 : ZMod q) = 1 := by rw [h1]; exact MulChar.one_apply isUnit_one.neg
    have ho : χ (-1 : ZMod q) = -1 := hodd
    rw [this] at ho; norm_num at ho
  have hgauss : gaussSum χ ZMod.stdAddChar = Complex.I * (Real.sqrt (q : ℝ) : ℂ) := by
    have h := gaussSum_real_primitive_eq hprim hreal
    rwa [if_neg hodd.not_even] at h
  exact sum_mul_odd_real_char_neg_of_gaussSum hprim hχ hodd hreal hgauss

/-- **UNCONDITIONAL LOG-SINE SIGN THEOREM FOR EVERY EVEN REAL PRIMITIVE `χ ≠ 1` mod `q`**:
`∑_{a=1}^{q-1} (χ a).re * Real.log (2 * Real.sin (π * a / q)) < 0`. -/
theorem dirichlet_log_sin_neg_even_real_primitive {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    ∑ a ∈ Finset.Ico 1 q,
        (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) < 0 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hsqrt_pos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq_pos
  have hL := LFunction_one_eq_even hprim hχ heven
  have hgauss : gaussSum χ ZMod.stdAddChar = (Real.sqrt (q : ℝ) : ℂ) := by
    have h := gaussSum_real_primitive_eq hprim hreal
    rwa [if_pos heven, one_mul] at h
  rw [hgauss, dirichletChar_inv_eq_self_of_real hreal] at hL
  have hsum_real :
      ∑ a ∈ Finset.Ico 1 q,
          χ (a : ZMod q) * (Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) : ℂ) =
        ((∑ a ∈ Finset.Ico 1 q,
          (χ (a : ZMod q)).re * Real.log (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha : χ (a : ZMod q) = ((χ (a : ZMod q)).re : ℂ) :=
      Complex.ext (by simp) (by simpa using hreal _)
    rw [ha]; push_cast; rfl
  have hre := congrArg Complex.re hL
  rw [hsum_real, show -((Real.sqrt (q : ℝ) : ℂ) / (q : ℂ)) =
    ((-(Real.sqrt (q : ℝ) / (q : ℝ)) : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hre
  have hpos := (LFunction_one_pos_of_real χ hχ hreal).1
  rw [hre] at hpos
  have hc_pos : 0 < Real.sqrt (q : ℝ) / (q : ℝ) := div_pos hsqrt_pos hq_pos
  nlinarith

/-! ## Section 5: Exact Cyclotomic Dedekind Zeta Residue Formulas at `s = 1` -/

/-- The `L`-function of the primitive character `χ*` inducing `χ : DirichletCharacter ℂ m`. -/
def primitiveLFunction {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (s : ℂ) : ℂ :=
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  DirichletCharacter.LFunction χ.primitiveCharacter s

private lemma primitiveCharacter_ne_one_of_ne_one {m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  intro h1
  apply hχ
  have hcond : χ.conductor = 1 := by
    have hp : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
    have hcond1 : (1 : DirichletCharacter ℂ χ.conductor).conductor = 1 :=
      DirichletCharacter.conductor_one
    have hself : χ.primitiveCharacter.conductor = χ.conductor := hp
    rw [h1, hcond1] at hself
    exact hself.symm
  exact (DirichletCharacter.eq_one_iff_conductor_eq_one).mpr hcond

open Classical in
/-- Nonvanishing of the product of non-principal Dirichlet `L`-values at `s = 1`:
`∏_{χ ≠ 1} L(1, χ) ≠ 0` for every modulus `m ≥ 1`. -/
theorem prod_LFunction_one_erase_one_ne_zero (m : ℕ) [NeZero m] :
    ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), DirichletCharacter.LFunction χ 1 ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun χ hχ => ?_
  exact Stage2DirichletAP.LFunction_apply_one_ne_zero_bridge (Finset.ne_of_mem_erase hχ)

open Classical in
/-- Nonvanishing of the product of primitive non-principal Dirichlet `L`-values at `s = 1`:
`∏_{χ ≠ 1} L(1, χ*) ≠ 0` for every modulus `m ≥ 1`. -/
theorem prod_primitiveLFunction_one_erase_one_ne_zero (m : ℕ) [NeZero m] :
    ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), primitiveLFunction χ 1 ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun χ hχ => ?_
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact Stage2DirichletAP.LFunction_apply_one_ne_zero_bridge
    (primitiveCharacter_ne_one_of_ne_one (Finset.ne_of_mem_erase hχ))

/-- Nonvanishing of the principal-character Euler factor correction `∏_{p ∣ m} (1 - p⁻¹)` at `s = 1`. -/
theorem prod_primeFactors_one_sub_inv_ne_zero (m : ℕ) :
    ∏ p ∈ m.primeFactors, (1 - ((p : ℂ))⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  intro h0
  have hinv : ((p : ℂ))⁻¹ = 1 := (sub_eq_zero.mp h0).symm
  have hp1 : (p : ℂ) = 1 := by simpa using congrArg Inv.inv hinv
  have : p = 1 := Nat.cast_eq_one.mp hp1
  omega

open Classical in
/-- **Exact Cyclotomic Dedekind Zeta Residue Formula (`riemannZeta`-normalized product)**:
`(s - 1) * (riemannZeta s * ∏_{χ ≠ 1} LFunction χ s) → ∏_{χ ≠ 1} LFunction χ 1 ≠ 0` as `s → 1` (`s ≠ 1`). -/
theorem riemannZeta_mul_prod_nonprincipal_LFunction_residue_one (m : ℕ) [NeZero m] :
    Tendsto
      (fun s : ℂ =>
        (s - 1) * (riemannZeta s *
          ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), DirichletCharacter.LFunction χ s))
      (𝓝[≠] (1 : ℂ))
      (nhds (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m),
        DirichletCharacter.LFunction χ 1)) ∧
    ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m),
      DirichletCharacter.LFunction χ 1 ≠ 0 := by
  refine ⟨?_, prod_LFunction_one_erase_one_ne_zero m⟩
  have hprod_cont :
      Tendsto
        (fun s : ℂ =>
          ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), DirichletCharacter.LFunction χ s)
        (𝓝[≠] (1 : ℂ))
        (nhds (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m),
          DirichletCharacter.LFunction χ 1)) := by
    refine tendsto_finsetProd _ fun χ hχ => ?_
    exact tendsto_nhdsWithin_of_tendsto_nhds
      ((DirichletCharacter.differentiable_LFunction (Finset.ne_of_mem_erase hχ)).continuous.tendsto 1)
  have hmul := riemannZeta_residue_one.mul hprod_cont
  rw [one_mul] at hmul
  exact hmul.congr fun s => by ring

open Classical in
/-- **Exact Cyclotomic Dedekind Zeta Residue Formula (Full Primitive Character Product)**:
`ζ_{ℚ(ζ_m)}(s) = ∏_{χ mod m} L(s, χ*)` has a simple pole at `s = 1` with exact nonzero residue
`∏_{χ ≠ 1} L(1, χ*) ≠ 0`! -/
theorem cyclotomic_dedekind_primitive_residue_one (m : ℕ) [NeZero m] :
    Tendsto
      (fun s : ℂ => (s - 1) * ∏ χ : DirichletCharacter ℂ m, primitiveLFunction χ s)
      (𝓝[≠] (1 : ℂ))
      (nhds (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), primitiveLFunction χ 1)) ∧
    ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), primitiveLFunction χ 1 ≠ 0 := by
  refine ⟨?_, prod_primitiveLFunction_one_erase_one_ne_zero m⟩
  have hsplit :
      (fun s : ℂ => (s - 1) * ∏ χ : DirichletCharacter ℂ m, primitiveLFunction χ s) =ᶠ[𝓝[≠] (1 : ℂ)]
        fun s : ℂ =>
          ((s - 1) * riemannZeta s) *
            ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), primitiveLFunction χ s := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ m))]
    have h1 : primitiveLFunction (1 : DirichletCharacter ℂ m) s = riemannZeta s := by
      unfold primitiveLFunction
      have : NeZero (1 : DirichletCharacter ℂ m).conductor :=
        ⟨DirichletCharacter.conductor_ne_zero _⟩
      rw [DirichletCharacter.primitiveCharacter_one]
      have htriv := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
        (N := (1 : DirichletCharacter ℂ m).conductor) hs
      have hcond1 : (1 : DirichletCharacter ℂ m).conductor = 1 := DirichletCharacter.conductor_one
      change LFunctionTrivChar (1 : DirichletCharacter ℂ m).conductor s = riemannZeta s
      rw [htriv, hcond1, Nat.primeFactors_one, Finset.prod_empty, one_mul]
    rw [h1]; ring
  rw [tendsto_congr' hsplit]
  have hprod_cont :
      Tendsto
        (fun s : ℂ =>
          ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), primitiveLFunction χ s)
        (𝓝[≠] (1 : ℂ))
        (nhds (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), primitiveLFunction χ 1)) := by
    refine tendsto_finsetProd _ fun χ hχ => ?_
    unfold primitiveLFunction
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    exact tendsto_nhdsWithin_of_tendsto_nhds
      ((DirichletCharacter.differentiable_LFunction
        (primitiveCharacter_ne_one_of_ne_one (Finset.ne_of_mem_erase hχ))).continuous.tendsto 1)
  simpa only [one_mul] using riemannZeta_residue_one.mul hprod_cont

open Classical in
/-- **Exact Residue of the Unramified-Mod-`m` Product `∏_{χ mod m} LFunction χ s` at `s = 1`**
(matching `Stage4ClassFieldTheory.prod_dirichletLFunction_eulerProduct_tendsto`):
`(s - 1) * ∏_{χ mod m} LFunction χ s → (∏_{p ∣ m} (1 - p⁻¹)) * ∏_{χ ≠ 1} LFunction χ 1 ≠ 0`. -/
theorem prod_dirichletLFunction_residue_one (m : ℕ) [NeZero m] :
    Tendsto
      (fun s : ℂ =>
        (s - 1) * ∏ χ : DirichletCharacter ℂ m, DirichletCharacter.LFunction χ s)
      (𝓝[≠] (1 : ℂ))
      (nhds ((∏ p ∈ m.primeFactors, (1 - ((p : ℂ))⁻¹)) *
        ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m),
          DirichletCharacter.LFunction χ 1)) ∧
    (∏ p ∈ m.primeFactors, (1 - ((p : ℂ))⁻¹)) *
      ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m),
        DirichletCharacter.LFunction χ 1 ≠ 0 := by
  refine ⟨?_, mul_ne_zero (prod_primeFactors_one_sub_inv_ne_zero m)
    (prod_LFunction_one_erase_one_ne_zero m)⟩
  have hsplit :
      ∀ s : ℂ,
        (s - 1) * ∏ χ : DirichletCharacter ℂ m, DirichletCharacter.LFunction χ s =
          ((s - 1) * LFunctionTrivChar m s) *
            ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m),
              DirichletCharacter.LFunction χ s := by
    intro s
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ m))]
    dsimp only [LFunctionTrivChar]
    ring
  simp_rw [hsplit]
  have hprod_cont :
      Tendsto
        (fun s : ℂ =>
          ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), DirichletCharacter.LFunction χ s)
        (𝓝[≠] (1 : ℂ))
        (nhds (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m),
          DirichletCharacter.LFunction χ 1)) := by
    refine tendsto_finsetProd _ fun χ hχ => ?_
    exact tendsto_nhdsWithin_of_tendsto_nhds
      ((DirichletCharacter.differentiable_LFunction (Finset.ne_of_mem_erase hχ)).continuous.tendsto 1)
  exact (DirichletCharacter.LFunctionTrivChar_residue_one (N := m)).mul hprod_cont

open Classical in
/-- **Master Unconditional Stage 6 Theorem (Dirichlet's Analytic Class Number Formula Core)**:
simultaneously packaging all three unconditional pillars with zero external assumptions:
1. Exact finite Gauss-sum evaluation of `L(1, χ)` for every primitive `χ ≠ 1` (general, even, odd).
2. Strict real positivity `0 < (LFunction χ 1).re ∧ (LFunction χ 1).im = 0` for every real
   non-principal `χ ≠ 1`, together with Gauss's exact quadratic Gauss sum
   `τ(χ) = (if χ.Even then 1 else I) * √q` and Dirichlet's Sign Theorem
   `∑_{a=1}^{q-1} a * (χ a).re < 0` for every odd real primitive `χ`.
3. Exact nonzero cyclotomic Dedekind zeta residue at `s = 1` for every modulus `m ≥ 1`
   (both full primitive product `∏_χ L(s, χ*)` and `riemannZeta s * ∏_{χ ≠ 1} L(s, χ)`). -/
theorem stage6_classNumberFormula_unconditional :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      DirichletCharacter.LFunction χ 1 =
        -(χ (-1 : ZMod q) * gaussSum χ ZMod.stdAddChar / (q : ℂ)) *
          ∑ a ∈ Finset.Ico 1 q, χ⁻¹ (a : ZMod q) * Complex.log (1 - e ((a : ℝ) / (q : ℝ)))) ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
      0 < (DirichletCharacter.LFunction χ 1).re ∧ (DirichletCharacter.LFunction χ 1).im = 0) ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ.Odd → (∀ a : ZMod q, (χ a).im = 0) →
      ∑ a ∈ Finset.Ico 1 q, (a : ℝ) * (χ (a : ZMod q)).re < 0) ∧
    (∀ (m : ℕ) [NeZero m],
      Tendsto (fun s : ℂ => (s - 1) * ∏ χ : DirichletCharacter ℂ m, primitiveLFunction χ s)
        (𝓝[≠] (1 : ℂ))
        (nhds (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), primitiveLFunction χ 1)) ∧
      ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ m), primitiveLFunction χ 1 ≠ 0) :=
  ⟨fun _ _ _ hprim hχ => LFunction_one_eq_neg_sign_gaussSum_div_q_mul_sum_log hprim hχ,
   fun _ _ χ hχ hreal => LFunction_one_pos_of_real χ hχ hreal,
   fun _ _ _ hprim hodd hreal => dirichlet_sign_theorem_odd_real_primitive hprim hodd hreal,
   fun m _ => cyclotomic_dedekind_primitive_residue_one m⟩

end RHDirect.Stage6ClassNumberFormula
