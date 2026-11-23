import RHDirect.Stage9LandauSiegel
import RHDirect.Stage8UniformAP
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# RHDirect.Stage10SiegelWalfiszFull

**UNCONDITIONAL FULL SIEGEL–WALFISZ THEOREM (1936) FOR ALL `q ≤ (log x)^A` WITH ZERO
EXCEPTIONAL MODULUS `q₁`**, together with **FULL ZERO-EXCEPTION `θ(x; q, a)` & `π(x; q, a)`**
and **FULL ZERO-EXCEPTION UNIFORM SHORT-INTERVAL PRIMES IN ARITHMETIC PROGRESSIONS**, proved
directly on Mathlib's `DirichletCharacter.LFunction`, `Stage2DirichletAP.chebyshevPsiAP`,
`Stage2DirichletAP.chebyshevThetaAP`, and `Stage2DirichletAP.primeCountAP` in pure Mathlib
`v4.33.1` (`0` assumptions, `0` `sorry`, `0` custom `axiom`s, `0` errors, `0` warnings, `0` info).

## Main Contents

1. **Unconditional Full Siegel–Walfisz Zero-Free Region & Log-Derivative Bound (`0` Exceptions!)**:
   - `siegel_walfisz_zeroFree_region_eps` & **`siegel_walfisz_zeroFree_region`**:
     combines `Stage9LandauSiegel.siegel_real_zero_exclusion` (for real points via primitive
     character reduction `PChar.of χ`), `Stage8UniformAP.LFunction_real_char_nonreal_zeroFree`
     (for non-real points of real characters), and
     `Stage5ZetaZeroFree.LFunction_complex_char_deLaValleePoussin_zeroFree` (for complex characters)
     to establish for EVERY `A > 0` a zero-free region
     `1 - min (c_A / Q ^ (1 / (2 * A))) (1 / (60000 * Real.log (Q * (|s.im| + 2)))) ≤ s.re`
     across ALL `Q ≥ 2`, ALL `q ≤ Q`, ALL non-principal `χ : DirichletCharacter ℂ q` with **ZERO**
     exceptional modulus `q₁`!
   - `siegel_walfisz_zeroFree_two_scale`, `negLogDerivL_bound_of_zeroFree_log`, and
     **`siegel_walfisz_negLogDerivL_bound`**:
     uniform Borel–Carathéodory log-derivative bound with **absolute** constants `c' > 0, C' > 0`
     independent of `A`, valid for ALL `q ≤ (Real.log x) ^ A` and ALL non-principal `χ mod q`
     with **ZERO** exception!

2. **Unconditional Zero-Exception Uniform Character-Sum Decay (`ψ₁(y, χ)` & `ψ(x, χ)`)**:
   - `psi1Char_bound_of_negLogDerivL_bound` & `siegel_walfisz_psi1Char_uniform`:
     uniform pole-free Perron contour shift with absolute exponent `c > 0` independent of `A`.
   - **`siegel_walfisz_character_psi_uniform`**:
     `∃ c > 0, ∀ A > 0, ∃ C > 0, ∀ x ≥ 4, ∀ q ≤ (log x)^A, ∀ χ ≠ 1, ‖chebyshevPsiChar χ x‖ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`.

3. **Unconditional Full Siegel–Walfisz Theorem (1936) for `ψ`, `θ`, and `π` (`0` Exceptions!)**:
   - **`siegel_walfisz_psi`**:
     `∃ c > 0, ∀ A > 0, ∃ C > 0, ∀ x ≥ 4, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A → ∀ a, Nat.Coprime a q → |chebyshevPsiAP q a x - x / q.totient| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`.
   - **`siegel_walfisz_theta`**:
     same unconditional zero-exception bound for `chebyshevThetaAP q a x`.
   - `primeCountAP_eq_abel_thetaAP` & `integral_inv_log_eq`:
     exact Abelian summation identity for `π(x; q, a)` and exact FTC identity for `li(x)`.
   - **`siegel_walfisz_pi`** & `siegel_walfisz_pi_real`:
     `∃ c > 0, ∀ A > 0, ∃ C > 0, ∀ x ≥ 4, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A → ∀ a, Nat.Coprime a q → |(primeCountAP q a ⌊x⌋₊ : ℝ) - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / q.totient| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`.

4. **Unconditional Zero-Exception Uniform Short-Interval Primes in Arithmetic Progressions**:
   - **`exists_prime_in_AP_uniform_siegel_walfisz`**:
     `∃ c > 0, ∀ A > 0, ∃ X_A ≥ 4, ∀ x ≥ X_A, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A → ∀ a, Nat.Coprime a q → ∃ p, p.Prime ∧ p ≡ a [MOD q] ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + x * Real.exp (-c * Real.sqrt (Real.log x))`.
   - **`stage10_siegel_walfisz_master`**: unified master theorem packaging all main results.
-/

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology RHDirect
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage10SiegelWalfiszFull

/-! ## Section 1: Unconditional Full Siegel–Walfisz Zero-Free Region & Log-Derivative Bound (`0` Exceptions!) -/

/-- Primitive character induced by a non-principal real character is non-principal and real. -/
private lemma primitiveChar_ne_one_and_sq_eq_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    (PChar.of χ).χ ≠ 1 ∧ (PChar.of χ).χ ^ 2 = 1 := by
  have hdvd : χ.conductor ∣ q := χ.conductor_dvd_level
  have hchg : DirichletCharacter.changeLevel hdvd χ.primitiveCharacter = χ :=
    χ.changeLevel_primitiveCharacter
  constructor
  · intro h1
    apply hχ1
    have h1' : χ.primitiveCharacter = 1 := h1
    rw [← hchg, h1', map_one]
  · have hprim2 : χ.primitiveCharacter ^ 2 = 1 :=
      DirichletCharacter.changeLevel_injective hdvd (by rw [map_pow, hchg, hχ2, map_one])
    exact hprim2

/-- **UNCONDITIONAL FULL SIEGEL–WALFISZ ZERO-FREE REGION (GENERAL `ε > 0`, `0` EXCEPTIONS!)**:
for EVERY `ε > 0`, there exists `c_ε > 0` such that for ALL `Q ≥ 2`, ALL `q ≤ Q` (`[NeZero q]`),
ALL non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`), and ALL `s : ℂ` with
`1 - min (c_ε / Q ^ ε) (1 / (60000 * Real.log (Q * (|s.im| + 2)))) ≤ s.re`:
`DirichletCharacter.LFunction χ s ≠ 0` (with **ZERO** exceptional modulus!). -/
theorem siegel_walfisz_zeroFree_region_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ c_ε : ℝ, 0 < c_ε ∧
      ∀ Q : ℝ, 2 ≤ Q →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q →
          ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
            ∀ s : ℂ,
              1 - min (c_ε / Q ^ ε) (1 / (60000 * Real.log (Q * (|s.im| + 2)))) ≤ s.re →
              DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨C_ε, hC_ε, hsiegel⟩ := Stage9LandauSiegel.siegel_real_zero_exclusion ε hε
  set c_ε : ℝ := min C_ε (1 / 2) with hc_def
  have hc_pos : 0 < c_ε := lt_min hC_ε (by norm_num)
  have hc_le_C : c_ε ≤ C_ε := min_le_left _ _
  have hc_le_half : c_ε ≤ 1 / 2 := min_le_right _ _
  refine ⟨c_ε, hc_pos, fun Q hQ q _ hqQ χ hχ s hs => ?_⟩
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hQ_pos : 0 < Q := by linarith
  have hlogq_pos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg s.im])
  have hlogQ_ge : Real.log ((q : ℝ) * (|s.im| + 2)) ≤ Real.log (Q * (|s.im| + 2)) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hqQ (by linarith [abs_nonneg s.im]))
  have hlogQ_pos : 0 < Real.log (Q * (|s.im| + 2)) := hlogq_pos.trans_le hlogQ_ge
  have hs_dlvp : 1 - 1 / (60000 * Real.log (Q * (|s.im| + 2))) ≤ s.re := by
    have := min_le_right (c_ε / Q ^ ε) (1 / (60000 * Real.log (Q * (|s.im| + 2))))
    linarith
  have hs_siegel : 1 - c_ε / Q ^ ε ≤ s.re := by
    have := min_le_left (c_ε / Q ^ ε) (1 / (60000 * Real.log (Q * (|s.im| + 2))))
    linarith
  by_cases hχ2 : χ ^ 2 ≠ 1
  · -- Complex character `χ ^ 2 ≠ 1`: de la Vallée Poussin zero-free region
    refine Stage5ZetaZeroFree.LFunction_complex_char_deLaValleePoussin_zeroFree χ hχ2 ?_
    have h1 : 1 / (60000 * Real.log (Q * (|s.im| + 2))) ≤
        1 / (14000 * Real.log ((q : ℝ) * (|s.im| + 2))) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      nlinarith
    linarith
  · push Not at hχ2
    by_cases him : s.im ≠ 0
    · -- Real character, non-real point: uniform de la Vallée Poussin zero-free region
      refine Stage8UniformAP.LFunction_real_char_nonreal_zeroFree hχ hχ2 him ?_
      have h1 : 1 / (60000 * Real.log (Q * (|s.im| + 2))) ≤
          1 / (60000 * Real.log ((q : ℝ) * (|s.im| + 2))) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    · -- Real character, real point: full unconditional Siegel real-zero exclusion (`0` exceptions!)
      push Not at him
      have hs_eq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
      have hQpow_ge1 : (1 : ℝ) ≤ Q ^ ε := Real.one_le_rpow (by linarith) hε.le
      have hc_div_le : c_ε / Q ^ ε ≤ 1 / 2 := by
        calc c_ε / Q ^ ε ≤ (1 / 2) / 1 := div_le_div₀ (by norm_num) hc_le_half zero_lt_one hQpow_ge1
          _ = 1 / 2 := div_one _
      have hs_re_pos : 0 < s.re := by linarith
      set ψ : PChar := PChar.of χ
      obtain ⟨hψ1, hψ2⟩ := primitiveChar_ne_one_and_sq_eq_one hχ hχ2
      have hψN_le_q : ψ.N ≤ q := Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
      have hψN_le_Q : (ψ.N : ℝ) ≤ Q := (by exact_mod_cast hψN_le_q : (ψ.N : ℝ) ≤ (q : ℝ)).trans hqQ
      have hψN_pos : (0 : ℝ) < (ψ.N : ℝ) := Nat.cast_pos.mpr (NeZero.pos ψ.N)
      have hpow_le : (ψ.N : ℝ) ^ ε ≤ Q ^ ε := Real.rpow_le_rpow hψN_pos.le hψN_le_Q hε.le
      have hβ_ge : 1 - C_ε / (ψ.N : ℝ) ^ ε ≤ s.re := by
        have h1 : c_ε / Q ^ ε ≤ C_ε / (ψ.N : ℝ) ^ ε := by
          calc c_ε / Q ^ ε ≤ C_ε / Q ^ ε :=
                div_le_div_of_nonneg_right hc_le_C (Real.rpow_nonneg hQ_pos.le ε)
            _ ≤ C_ε / (ψ.N : ℝ) ^ ε :=
                div_le_div_of_nonneg_left hC_ε.le (Real.rpow_pos_of_pos hψN_pos ε) hpow_le
        linarith
      have hnz_prim : DirichletCharacter.LFunction ψ.χ (s.re : ℂ) ≠ 0 :=
        hsiegel ψ.N ψ.χ ψ.prim hψ2 hψ1 s.re hβ_ge
      rw [hs_eq]
      intro hz
      exact hnz_prim ((RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ
        (by simpa using hs_re_pos) (.inl hχ)).mp hz)

/-- **UNCONDITIONAL FULL SIEGEL–WALFISZ ZERO-FREE REGION (`ε = 1 / (2 * A)`, `0` EXCEPTIONS!)**:
for EVERY `A > 0`, there exists `c_A > 0` such that for ALL `Q ≥ 2`, ALL `q ≤ Q` (`[NeZero q]`),
ALL non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`), and ALL `s : ℂ` with
`1 - min (c_A / Q ^ (1 / (2 * A))) (1 / (60000 * Real.log (Q * (|s.im| + 2)))) ≤ s.re`:
`DirichletCharacter.LFunction χ s ≠ 0` (with **ZERO** exceptional modulus `q₁`!). -/
theorem siegel_walfisz_zeroFree_region {A : ℝ} (hA : 0 < A) :
    ∃ c_A : ℝ, 0 < c_A ∧
      ∀ Q : ℝ, 2 ≤ Q →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q →
          ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
            ∀ s : ℂ,
              1 - min (c_A / Q ^ (1 / (2 * A))) (1 / (60000 * Real.log (Q * (|s.im| + 2)))) ≤ s.re →
              DirichletCharacter.LFunction χ s ≠ 0 :=
  siegel_walfisz_zeroFree_region_eps (by positivity : (0 : ℝ) < 1 / (2 * A))

/-- **Two-Scale Zero-Exception Zero-Free Region**: if `2 ≤ Q_s ≤ Q_b` and
`1 / (60000 * Real.log (2 * Q_b)) ≤ c_ε / Q_s ^ ε`, then every non-principal `χ mod q` with
`q ≤ Q_s` satisfies the pure de la Vallée Poussin zero-free region
`1 - 1 / (60000 * Real.log (Q_b * (|s.im| + 2))) ≤ s.re → LFunction χ s ≠ 0` with ZERO exception! -/
theorem siegel_walfisz_zeroFree_two_scale {ε : ℝ} (hε : 0 < ε) :
    ∃ c_ε : ℝ, 0 < c_ε ∧
      ∀ Q_s Q_b : ℝ, 2 ≤ Q_s → Q_s ≤ Q_b →
        1 / (60000 * Real.log (2 * Q_b)) ≤ c_ε / Q_s ^ ε →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q_s →
          ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
            ∀ s : ℂ, 1 - 1 / (60000 * Real.log (Q_b * (|s.im| + 2))) ≤ s.re →
              DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨c_ε, hc_ε, hzf⟩ := siegel_walfisz_zeroFree_region_eps hε
  refine ⟨c_ε, hc_ε, fun Q_s Q_b hQs hQsb hcmp q _ hqQs χ hχ s hs => ?_⟩
  refine hzf Q_s hQs q hqQs χ hχ s ?_
  have hQs_pos : 0 < Q_s := by linarith
  have hQb_pos : 0 < Q_b := by linarith
  have hlog2Qb_pos : 0 < Real.log (2 * Q_b) := Real.log_pos (by linarith)
  have hlogQs_pos : 0 < Real.log (Q_s * (|s.im| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg s.im])
  have h1 : 1 / (60000 * Real.log (Q_b * (|s.im| + 2))) ≤ c_ε / Q_s ^ ε := by
    have hlog_ge : Real.log (2 * Q_b) ≤ Real.log (Q_b * (|s.im| + 2)) :=
      Real.log_le_log (by positivity) (by nlinarith [abs_nonneg s.im])
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans hcmp
  have h2 : 1 / (60000 * Real.log (Q_b * (|s.im| + 2))) ≤
      1 / (60000 * Real.log (Q_s * (|s.im| + 2))) := by
    have hlog_ge : Real.log (Q_s * (|s.im| + 2)) ≤ Real.log (Q_b * (|s.im| + 2)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hQsb (by linarith [abs_nonneg s.im]))
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hmin : 1 / (60000 * Real.log (Q_b * (|s.im| + 2))) ≤
      min (c_ε / Q_s ^ ε) (1 / (60000 * Real.log (Q_s * (|s.im| + 2)))) :=
    le_min h1 h2
  linarith

/-- **Modular Borel–Carathéodory Log-Derivative Bound from Any Uniform Log Zero-Free Region**:
for ANY `c_zf > 0`, `Q ≥ 2`, `q ≤ Q`, non-principal `χ mod q`, if `LFunction χ s ≠ 0` whenever
`1 - c_zf / log (Q * (|s.im| + 2)) ≤ s.re`, then with explicit constants depending ONLY on `c_zf`:
`c := min c_zf (1 / 4)`, `c' := c / 32`, `C' := max (1 / c' + 1) ((32 / c) * (log (128 / c) + 2))`,
we have `LFunction χ s ≠ 0` and `‖(-L'/L)(s, χ)‖ ≤ C' * (log (Q * (|s.im| + 2))) ^ 2` for all
`1 - c' / log (Q * (|s.im| + 2)) ≤ s.re ≤ 2`. -/
theorem negLogDerivL_bound_of_zeroFree_log {c_zf Q : ℝ} (hc_zf : 0 < c_zf) (hQ : 2 ≤ Q)
    {q : ℕ} [NeZero q] (hqQ : (q : ℝ) ≤ Q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hzf : ∀ s : ℂ, 1 - c_zf / Real.log (Q * (|s.im| + 2)) ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0) :
    let c : ℝ := min c_zf (1 / 4)
    let c' : ℝ := c / 32
    let C' : ℝ := max (1 / c' + 1) ((32 / c) * (Real.log (128 / c) + 2))
    ∀ s : ℂ, 1 - c' / Real.log (Q * (|s.im| + 2)) ≤ s.re → s.re ≤ 2 →
      DirichletCharacter.LFunction χ s ≠ 0 ∧
      ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
        C' * (Real.log (Q * (|s.im| + 2))) ^ 2 := by
  intro c c' C' s hre_lo hre_hi
  have hc_pos : 0 < c := lt_min hc_zf (by norm_num)
  have hc_le_zf : c ≤ c_zf := min_le_left _ _
  have hc_le_qtr : c ≤ 1 / 4 := min_le_right _ _
  have hc'_pos : 0 < c' := by positivity
  set C_right : ℝ := 1 / c' + 1
  have h128_gt1 : (1 : ℝ) < 128 / c := by rw [one_lt_div hc_pos]; linarith
  have hlog128_pos : 0 < Real.log (128 / c) := Real.log_pos h128_gt1
  set A_M : ℝ := Real.log (128 / c) + 2
  have hAM_pos : 0 < A_M := by positivity
  set C_left : ℝ := (32 / c) * A_M
  set t : ℝ := s.im
  set L : ℝ := Real.log (Q * (|t| + 2)) with hL_def
  have hQt_ge4 : (4 : ℝ) ≤ Q * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hL_gt1 : 1 < L := by
    have : Real.exp 1 < Q * (|t| + 2) := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  have hsnz : DirichletCharacter.LFunction χ s ≠ 0 := by
    refine hzf s ?_
    have : c' / L ≤ c_zf / L :=
      div_le_div_of_nonneg_right (by dsimp only [c']; linarith) hL_pos.le
    linarith
  refine ⟨hsnz, ?_⟩
  by_cases hright : 1 + c' / L ≤ s.re
  · -- Case 1: `s.re ≥ 1 + c' / L`
    have hs_re_gt1 : 1 < s.re := by linarith [div_pos hc'_pos hL_pos]
    have hs_eq : (s.re : ℂ) + I * (t : ℂ) = s := by
      have := Complex.re_add_im s
      simpa only [t, mul_comm I] using this
    have hbd := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hs_re_gt1 t).2.2
    unfold Stage3ZeroFreeRegion.negLogDerivL at hbd
    rw [hs_eq] at hbd
    have hinv_le : 1 / (s.re - 1) ≤ L / c' := by
      rw [div_le_div_iff₀ (by linarith) hc'_pos, one_mul]
      have h1 : c' / L ≤ s.re - 1 := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hL_pos.le
      rw [div_mul_cancel₀ _ hL_pos.ne'] at h2
      linarith
    have hL_le_L2 : L ≤ L ^ 2 := by nlinarith
    have h1_le_L2 : 1 ≤ L ^ 2 := by nlinarith
    calc ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
        ≤ 1 / (s.re - 1) + 1 := hbd
      _ ≤ (1 / c') * L + 1 := by linarith [show L / c' = (1 / c') * L by ring]
      _ ≤ (1 / c') * L ^ 2 + 1 * L ^ 2 := by
          have := mul_le_mul_of_nonneg_left hL_le_L2 (by positivity : 0 ≤ 1 / c')
          linarith
      _ = C_right * L ^ 2 := by dsimp only [C_right]; ring
      _ ≤ C' * L ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg L)
  · -- Case 2: `1 - c' / L ≤ s.re < 1 + c' / L` — Borel–Carathéodory on a zero-free disk
    push Not at hright
    set η : ℝ := c / (16 * L) with hη_def
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 64 := by
      have h1 : c / L ≤ 1 / 4 := by
        calc c / L ≤ (1 / 4) / 1 := div_le_div₀ (by norm_num) hc_le_qtr zero_lt_one hL_gt1.le
          _ = 1 / 4 := div_one _
      have hEq : η = (c / L) / 16 := by dsimp only [η]; ring
      rw [hEq]; linarith
    set R_open : ℝ := 5 * η
    set R : ℝ := 4 * η
    set r : ℝ := 2 * η
    have hR_open_pos : 0 < R_open := by positivity
    have hR_pos : 0 < R := by positivity
    have hrR : r < R := by dsimp only [r, R]; linarith
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (t : ℂ) with hs₀_def
    have hs₀_re : s₀.re = 1 + η := by simp [s₀]
    have hs₀_im : s₀.im = t := by simp [s₀]
    have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz.le)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hz_im_le : |z.im| ≤ |t| + 1 / 2 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        have hR_le : R_open ≤ 1 / 2 := by dsimp only [R_open]; linarith
        linarith [abs_le.mpr him_diff]
      have hlog_le : Real.log (Q * (|z.im| + 2)) ≤ 2 * L := by
        have hsq : Q * (|z.im| + 2) ≤ (Q * (|t| + 2)) ^ 2 := by
          have ht2 : 2 ≤ |t| + 2 := by linarith [abs_nonneg t]
          nlinarith
        have h1 := Real.log_le_log (by positivity) hsq
        rw [Real.log_pow] at h1
        simpa [L] using h1
      have hlogz_pos : 0 < Real.log (Q * (|z.im| + 2)) :=
        Real.log_pos (by nlinarith [abs_nonneg z.im])
      have hdiv_ge : c / (2 * L) ≤ c_zf / Real.log (Q * (|z.im| + 2)) := by
        calc c / (2 * L) ≤ c / Real.log (Q * (|z.im| + 2)) :=
              div_le_div_of_nonneg_left hc_pos.le hlogz_pos hlog_le
          _ ≤ c_zf / Real.log (Q * (|z.im| + 2)) :=
              div_le_div_of_nonneg_right hc_le_zf hlogz_pos.le
      have h4η : 4 * η ≤ c / (2 * L) := by
        have hEq : 4 * η = (c / (2 * L)) / 2 := by dsimp only [η]; ring
        have hnn : 0 ≤ c / (2 * L) := by positivity
        linarith
      exact hzf z (by dsimp only [R_open] at hre_diff; linarith)
    have hball_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball s₀ R_open) :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
      (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
    set M : ℝ := A_M * L with hM_def
    have hLog_re_le : ∀ z ∈ Metric.closedBall s₀ R, (Log z).re ≤ M := by
      intro z hz
      have hz_ball : z ∈ Metric.ball s₀ R_open := hcb_sub hz
      have hznz : DirichletCharacter.LFunction χ z ≠ 0 := hball_nz z hz_ball
      have hs₀_nz : DirichletCharacter.LFunction χ s₀ ≠ 0 :=
        hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hR_le : R ≤ 1 / 16 := by dsimp only [R]; linarith
      have hz_re_lo : 1 / 2 ≤ z.re := by linarith
      have hz_im_hi : |z.im| ≤ |t| + 1 / 2 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        linarith [abs_le.mpr him_diff]
      have hz_bd : ‖DirichletCharacter.LFunction χ z‖ ≤ 4 * Q * (|t| + 2) := by
        have h1 := Stage5DirichletLZeroFree.norm_LFunction_le_of_stepSum_bound hχ (Nat.cast_nonneg q)
          (fun u _ => Stage5DirichletLZeroFree.norm_stepSum_dirichletChar_le_modulus hχ u)
          (by linarith : 0 < z.re)
        calc ‖DirichletCharacter.LFunction χ z‖
            ≤ (q : ℝ) * (z.re + |z.im|) / z.re := h1
          _ ≤ Q * (2 + (|t| + 1 / 2)) / (1 / 2) := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul hqQ (by linarith) (by linarith [abs_nonneg z.im]) (by linarith))
                (by norm_num) hz_re_lo
          _ ≤ 4 * Q * (|t| + 2) := by nlinarith [abs_nonneg t]
      have hinv_s₀ : ‖1 / DirichletCharacter.LFunction χ s₀‖ ≤ 32 * L / c := by
        have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ
          (by linarith : 1 < 1 + η) t).2.1
        have hsub : (1 + η) - 1 = η := by ring
        rw [hsub] at h
        have hs₀_eq' : ((1 + η : ℝ) : ℂ) + I * (t : ℂ) = s₀ := rfl
        rw [hs₀_eq'] at h
        have h2 : (1 + η) / η ≤ 2 / η := div_le_div_of_nonneg_right (by linarith) hη_pos.le
        have h3 : 2 / η = 32 * L / c := by
          dsimp only [η]; field_simp [hc_pos.ne', hL_pos.ne']; ring
        linarith
      have hratio_le :
          ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ ≤
            (128 / c) * (Q * (|t| + 2)) * L := by
        rw [show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀ =
              DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₀) by ring,
          norm_mul]
        calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₀‖
            ≤ (4 * Q * (|t| + 2)) * (32 * L / c) :=
              mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ = (128 / c) * (Q * (|t| + 2)) * L := by ring
      have hre_eq : (Log z).re =
          Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
        have hexp : Real.exp (Log z).re =
            ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
          rw [← Complex.norm_exp, hLog_exp z hz_ball]
        rw [← hexp, Real.log_exp]
      have hratio_pos : 0 < ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ :=
        norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)
      have hlogL_le : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL_pos).trans (by linarith)
      rw [hre_eq]
      calc Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖
          ≤ Real.log ((128 / c) * (Q * (|t| + 2)) * L) := Real.log_le_log hratio_pos hratio_le
        _ = Real.log ((128 / c) * (Q * (|t| + 2))) + Real.log L :=
            Real.log_mul (by positivity) hL_pos.ne'
        _ = Real.log (128 / c) + L + Real.log L := by
            rw [Real.log_mul (by positivity) (by positivity), ← hL_def]
        _ ≤ Real.log (128 / c) * L + L + L := by nlinarith
        _ = M := by dsimp only [M, A_M]; ring
    have hs_dist : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - (1 + η) : ℝ) : ℂ)) :=
        Complex.ext (by simp [s₀]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hc'_eq : c' / L = η / 2 := by dsimp only [c', η]; ring
      dsimp only [r]
      constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_dist
    have hs_ball : s ∈ Metric.ball s₀ R_open :=
      hcb_sub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hs_dist.trans hrR.le))
    rw [(hLog_d s hs_ball).deriv, hLog0, Complex.zero_re, sub_zero] at hbc
    have hcoeff : 2 * R / (R - r) ^ 2 = 32 * L / c := by
      dsimp only [R, r, η]
      field_simp [hc_pos.ne', hL_pos.ne']
      ring
    rw [hcoeff] at hbc
    have hneg_norm :
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
          ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ := by
      rw [neg_div, norm_neg]
    rw [hneg_norm]
    calc ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
        ≤ (32 * L / c) * M := hbc
      _ = C_left * L ^ 2 := by dsimp only [C_left, M]; ring
      _ ≤ C' * L ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg L)

/-- Asymptotic threshold helper: for any `A > 0`, `α > 0`, `c_ε > 0`, eventually for all `y ≥ X`:
1. `2 ≤ (Real.log y) ^ A`,
2. `(Real.log y) ^ A ≤ Real.exp (α * Real.sqrt (Real.log y))`,
3. `1 / (60000 * Real.log (2 * Real.exp (α * Real.sqrt (Real.log y)))) ≤ c_ε / ((Real.log y) ^ A) ^ (1 / (4 * A))`. -/
private lemma eventually_siegel_two_scale_conditions {A α c_ε : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hc : 0 < c_ε) :
    ∃ X : ℝ, 4 ≤ X ∧
      ∀ y : ℝ, X ≤ y →
        2 ≤ (Real.log y) ^ A ∧
        (Real.log y) ^ A ≤ Real.exp (α * Real.sqrt (Real.log y)) ∧
        1 / (60000 * Real.log (2 * Real.exp (α * Real.sqrt (Real.log y)))) ≤
          c_ε / ((Real.log y) ^ A) ^ (1 / (4 * A)) := by
  have hlog_div_sqrt : Tendsto (fun u : ℝ => Real.log u / Real.sqrt u) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    exact h.congr fun u => by rw [Real.sqrt_eq_rpow]
  have h1 : ∀ᶠ y : ℝ in atTop, Real.log (Real.log y) / Real.sqrt (Real.log y) < α / A :=
    (hlog_div_sqrt.comp Real.tendsto_log_atTop).eventually (Iio_mem_nhds (div_pos hα hA))
  have h2 : ∀ᶠ y : ℝ in atTop, 2 ≤ (Real.log y) ^ A :=
    ((tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop (2 : ℝ))
  have h3 : ∀ᶠ y : ℝ in atTop, 1 / (60000 * α * c_ε) ≤ (Real.log y) ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (1 / (60000 * α * c_ε)))
  have h4 : ∀ᶠ y : ℝ in atTop, 4 ≤ y := eventually_ge_atTop (4 : ℝ)
  have hall : ∀ᶠ y : ℝ in atTop,
      4 ≤ y ∧
      2 ≤ (Real.log y) ^ A ∧
      (Real.log y) ^ A ≤ Real.exp (α * Real.sqrt (Real.log y)) ∧
      1 / (60000 * Real.log (2 * Real.exp (α * Real.sqrt (Real.log y)))) ≤
        c_ε / ((Real.log y) ^ A) ^ (1 / (4 * A)) := by
    filter_upwards [h1, h2, h3, h4] with y hy1 hy2 hy3 hy4
    have hLy_pos : 0 < Real.log y := Real.log_pos (by linarith)
    have hsq_pos : 0 < Real.sqrt (Real.log y) := Real.sqrt_pos.mpr hLy_pos
    refine ⟨hy4, hy2, ?_, ?_⟩
    · -- `(log y)^A ≤ exp(α * √(log y))`
      have hmul : A * Real.log (Real.log y) ≤ α * Real.sqrt (Real.log y) := by
        have hlt := (div_lt_iff₀ hsq_pos).mp hy1
        have hlt2 := mul_lt_mul_of_pos_left hlt hA
        have heq : A * (α / A * Real.sqrt (Real.log y)) = α * Real.sqrt (Real.log y) := by
          field_simp [hA.ne']
        linarith
      rw [Real.rpow_def_of_pos hLy_pos]
      exact Real.exp_le_exp.mpr (by linarith)
    · -- `1 / (60000 * log(2 * exp(α √(log y)))) ≤ c_ε / ((log y)^A)^(1/(4A))`
      have hpow_eq : ((Real.log y) ^ A) ^ (1 / (4 * A)) = (Real.log y) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_mul hLy_pos.le]
        congr 1; field_simp [hA.ne']
      rw [hpow_eq]
      have hlog_ge : α * Real.sqrt (Real.log y) ≤ Real.log (2 * Real.exp (α * Real.sqrt (Real.log y))) := by
        rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
        linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
      have hsq_eq : Real.sqrt (Real.log y) = (Real.log y) ^ (1 / 4 : ℝ) * (Real.log y) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hLy_pos]; norm_num
      have hq_pos : 0 < (Real.log y) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hLy_pos _
      calc 1 / (60000 * Real.log (2 * Real.exp (α * Real.sqrt (Real.log y))))
          ≤ 1 / (60000 * (α * Real.sqrt (Real.log y))) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
        _ ≤ c_ε / (Real.log y) ^ (1 / 4 : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) hq_pos, one_mul, hsq_eq]
            have hstep := mul_le_mul_of_nonneg_left hy3 (show 0 ≤ 60000 * α * c_ε * (Real.log y) ^ (1 / 4 : ℝ) by positivity)
            have hlhs : 60000 * α * c_ε * (Real.log y) ^ (1 / 4 : ℝ) * (1 / (60000 * α * c_ε)) =
                (Real.log y) ^ (1 / 4 : ℝ) := by
              field_simp [hα.ne', hc.ne']
            linarith
  rw [Filter.eventually_atTop] at hall
  obtain ⟨X₀, hX₀⟩ := hall
  refine ⟨max 4 X₀, le_max_left _ _, fun y hy => ?_⟩
  have h := hX₀ y ((le_max_right _ _).trans hy)
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-- **Absolute Borel–Carathéodory constants at `c_zf = 1 / 60000`** (independent of `A, q, χ, s`). -/
private def sw_c1 : ℝ := (1 / 60000 : ℝ) / 32
private def sw_C1 : ℝ :=
  max (1 / sw_c1 + 1) ((32 / (1 / 60000 : ℝ)) * (Real.log (128 / (1 / 60000 : ℝ)) + 2))

private lemma sw_c1_pos : 0 < sw_c1 := by unfold sw_c1; norm_num
private lemma sw_C1_pos : 0 < sw_C1 := by
  unfold sw_C1
  exact lt_of_lt_of_le (by have := sw_c1_pos; positivity : (0 : ℝ) < 1 / sw_c1 + 1) (le_max_left _ _)

/-- **Parameterized Zero-Exception Log-Derivative Bound at Scale `Q_b = exp(α √(log x))`**:
for EVERY scale `α > 0` and EVERY `A > 0`, there exists `X_A ≥ 4` such that for ALL `x ≥ X_A`,
ALL `q ≤ (Real.log x) ^ A` (`[NeZero q]`), ALL non-principal `χ : DirichletCharacter ℂ q`,
and ALL `s : ℂ` with `1 - sw_c1 / (α * √(log x) + log(|s.im| + 2)) ≤ s.re ≤ 2`:
`LFunction χ s ≠ 0` and
`‖(-L'/L)(s, χ)‖ ≤ sw_C1 * (α * √(log x) + log(|s.im| + 2)) ^ 2`. -/
theorem siegel_walfisz_negLogDerivL_bound_at_scale {α : ℝ} (hα : 0 < α) {A : ℝ} (hA : 0 < A) :
    ∃ X_A : ℝ, 4 ≤ X_A ∧
      ∀ x : ℝ, X_A ≤ x →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
          ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
            ∀ s : ℂ,
              1 - sw_c1 / (α * Real.sqrt (Real.log x) + Real.log (|s.im| + 2)) ≤ s.re →
              s.re ≤ 2 →
              DirichletCharacter.LFunction χ s ≠ 0 ∧
              ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
                sw_C1 * (α * Real.sqrt (Real.log x) + Real.log (|s.im| + 2)) ^ 2 := by
  obtain ⟨c_ε, hc_ε, htwo⟩ := siegel_walfisz_zeroFree_two_scale (ε := 1 / (4 * A)) (by positivity)
  obtain ⟨X_A, hXA4, hcond⟩ := eventually_siegel_two_scale_conditions hA hα hc_ε
  refine ⟨X_A, hXA4, fun x hx q _ hq χ hχ s hs_lo hs_hi => ?_⟩
  obtain ⟨hQs2, hQsb, hcmp⟩ := hcond x hx
  set Q_s : ℝ := (Real.log x) ^ A
  set Q_b : ℝ := Real.exp (α * Real.sqrt (Real.log x))
  have hQb2 : 2 ≤ Q_b := hQs2.trans hQsb
  have hqQb : (q : ℝ) ≤ Q_b := hq.trans hQsb
  have hzf : ∀ z : ℂ, 1 - (1 / 60000 : ℝ) / Real.log (Q_b * (|z.im| + 2)) ≤ z.re →
      DirichletCharacter.LFunction χ z ≠ 0 := by
    intro z hz
    refine htwo Q_s Q_b hQs2 hQsb hcmp q hq χ hχ z ?_
    have hrew : (1 / 60000 : ℝ) / Real.log (Q_b * (|z.im| + 2)) =
        1 / (60000 * Real.log (Q_b * (|z.im| + 2))) := by ring
    rwa [← hrew]
  have hlog_eq : Real.log (Q_b * (|s.im| + 2)) =
      α * Real.sqrt (Real.log x) + Real.log (|s.im| + 2) := by
    dsimp only [Q_b]
    rw [Real.log_mul (Real.exp_pos _).ne' (by linarith [abs_nonneg s.im]), Real.log_exp]
  have hmin_eq : min (1 / 60000 : ℝ) (1 / 4) = 1 / 60000 := min_eq_left (by norm_num)
  have hbc := negLogDerivL_bound_of_zeroFree_log (c_zf := 1 / 60000) (by norm_num) hQb2 hqQb hχ hzf s
  simp only [hmin_eq, hlog_eq] at hbc
  exact hbc hs_lo hs_hi

/-- **UNCONDITIONAL FULL SIEGEL–WALFISZ LOG-DERIVATIVE BOUND (`0` EXCEPTIONS, ABSOLUTE `c', C'`)**:
there exist ABSOLUTE constants `c' > 0` and `C' > 0` (independent of `A`) such that for EVERY
`A > 0`, there exists `X_A ≥ 4` such that for ALL `x ≥ X_A`, ALL `q ≤ (Real.log x) ^ A`
(`[NeZero q]`), ALL non-principal `χ : DirichletCharacter ℂ q`, and ALL `s : ℂ` with
`1 - c' / (Real.sqrt (Real.log x) + Real.log (|s.im| + 2)) ≤ s.re ≤ 2`:
`LFunction χ s ≠ 0` and
`‖(-L'/L)(s, χ)‖ ≤ C' * (Real.sqrt (Real.log x) + Real.log (|s.im| + 2)) ^ 2`
with **ZERO** exceptional modulus `q₁`! -/
theorem siegel_walfisz_negLogDerivL_bound :
    ∃ c' : ℝ, 0 < c' ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ A : ℝ, 0 < A →
        ∃ X_A : ℝ, 4 ≤ X_A ∧
          ∀ x : ℝ, X_A ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
                ∀ s : ℂ,
                  1 - c' / (Real.sqrt (Real.log x) + Real.log (|s.im| + 2)) ≤ s.re → s.re ≤ 2 →
                  DirichletCharacter.LFunction χ s ≠ 0 ∧
                  ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
                    C' * (Real.sqrt (Real.log x) + Real.log (|s.im| + 2)) ^ 2 := by
  refine ⟨sw_c1, sw_c1_pos, sw_C1, sw_C1_pos, fun A hA => ?_⟩
  obtain ⟨X_A, hXA4, hbd⟩ := siegel_walfisz_negLogDerivL_bound_at_scale (α := 1) one_pos hA
  refine ⟨X_A, hXA4, fun x hx q _ hq χ hχ s hs_lo hs_hi => ?_⟩
  have h := hbd x hx q hq χ hχ s (by simpa [one_mul] using hs_lo) hs_hi
  simpa [one_mul] using h

/-! ## Section 2: Unconditional Zero-Exception Uniform Character-Sum Decay (`ψ₁(y, χ)` & `ψ(x, χ)`) -/

/-- Elementary exponential decay inequality `u ^ 2 * exp (-2 * u) ≤ 1` for `u ≥ 0`. -/
private lemma sq_mul_exp_neg_two_le_one {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-2 * u) ≤ 1 := by
  have h1 : u * Real.exp (-u) ≤ 1 := by
    have h := Real.add_one_le_exp u
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos u)).mpr (by linarith)
  have h2 : u ^ 2 * Real.exp (-2 * u) = (u * Real.exp (-u)) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [h2]
  exact pow_le_one₀ (mul_nonneg hu (Real.exp_pos (-u)).le) h1

/-- **Modular Pole-Free Perron Contour Shift for `psi1Char χ y`**:
given any `c₁, C₁ > 0`, `Q ≥ 2`, `y ≥ max 2 (exp((2 / α)^2))` where
`α = √(min c₁ (1 / 4) / 6)`, `Q ≤ exp(α √(log y))`, and a log-derivative bound
`‖(-L'/L)(z, χ)‖ ≤ C₁ * (log(Q * (|z.im| + 2)))^2` on `1 - c₁ / log(Q * (|z.im| + 2)) ≤ z.re ≤ 2`,
we obtain `‖psi1Char χ y‖ ≤ K_large * y ^ 2 * Real.exp (-(α / 2) * Real.sqrt (Real.log y))`. -/
theorem psi1Char_bound_of_negLogDerivL_bound {c₁ C₁ Q y : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
    (hQ : 2 ≤ Q)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hbd : ∀ s : ℂ, 1 - c₁ / Real.log (Q * (|s.im| + 2)) ≤ s.re → s.re ≤ 2 →
      DirichletCharacter.LFunction χ s ≠ 0 ∧
      ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
        C₁ * (Real.log (Q * (|s.im| + 2))) ^ 2)
    (hy_ge : max 2 (Real.exp ((2 / Real.sqrt (min c₁ (1 / 4) / 6)) ^ 2)) ≤ y)
    (hQy : Q ≤ Real.exp (Real.sqrt (min c₁ (1 / 4) / 6) * Real.sqrt (Real.log y))) :
    let α : ℝ := Real.sqrt (min c₁ (1 / 4) / 6)
    let K_large : ℝ :=
      (48 / Real.pi + (27 * C₁ * α ^ 2 / Real.pi) + (18 * C₁ * α ^ 2 / Real.pi)) * (4 / α) ^ 2
    ‖Stage4ExplicitFormula.psi1Char χ y‖ ≤
      K_large * y ^ 2 * Real.exp (-(α / 2) * Real.sqrt (Real.log y)) := by
  intro α K_large
  set c_star : ℝ := min c₁ (1 / 4) with hc_star_def
  have hc_star_pos : 0 < c_star := lt_min hc₁ (by norm_num)
  have hc_star_le_c₁ : c_star ≤ c₁ := min_le_left _ _
  have hc_star_le_qtr : c_star ≤ 1 / 4 := min_le_right _ _
  have hα_pos : 0 < α := Real.sqrt_pos.mpr (by positivity)
  have h6α2 : 6 * α ^ 2 = c_star := by
    dsimp only [α]; rw [Real.sq_sqrt (by positivity)]; ring
  set c_fin : ℝ := α / 2 with hc_fin_def
  have hy2 : 2 ≤ y := (le_max_left _ _).trans hy_ge
  have hy0 : 0 < y := by linarith
  set Ly : ℝ := Real.log y with hLy_def
  have hLy_ge_log2 : Real.log 2 ≤ Ly := Real.log_le_log (by norm_num) hy2
  have hLy_pos : 0 < Ly := (Real.log_pos (by norm_num)).trans_le hLy_ge_log2
  set u : ℝ := Real.sqrt Ly with hu_def
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hLy_pos
  have hu_sq : u ^ 2 = Ly := Real.sq_sqrt hLy_pos.le
  have hLy_ge_inv : (2 / α) ^ 2 ≤ Ly := by
    have hexp : Real.exp ((2 / α) ^ 2) ≤ y := (le_max_right _ _).trans hy_ge
    exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hexp)
  have hαu_ge2 : 2 ≤ α * u := by
    have h1 : 2 / α ≤ u := Real.le_sqrt_of_sq_le hLy_ge_inv
    have h2 := mul_le_mul_of_nonneg_left h1 hα_pos.le
    rwa [mul_div_cancel₀ _ hα_pos.ne'] at h2
  set T : ℝ := Real.exp (α * u) with hT_def
  have hT_pos : 0 < T := Real.exp_pos _
  have hT_ge2 : 2 ≤ T := by
    have h1 : Real.exp 1 ≤ T := Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_one_gt_d9]
  have hlogT : Real.log T = α * u := Real.log_exp _
  set L_QT : ℝ := Real.log (Q * (T + 2)) with hLQT_def
  have hLQT_gt1 : 1 < L_QT := by
    have : Real.exp 1 < Q * (T + 2) := by nlinarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLQT_pos : 0 < L_QT := zero_lt_one.trans hLQT_gt1
  have hLQT_le : L_QT ≤ 3 * α * u := by
    have hle : Q * (T + 2) ≤ Real.exp (α * u) * (2 * T) := by
      have hT2 : T + 2 ≤ 2 * T := by linarith
      exact mul_le_mul hQy hT2 (by positivity) (Real.exp_pos _).le
    have h1 : L_QT ≤ Real.log (Real.exp (α * u) * (2 * T)) :=
      Real.log_le_log (by positivity) hle
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
      Real.log_mul (by norm_num) hT_pos.ne', hlogT] at h1
    have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  set c_r : ℝ := 1 + 1 / (2 * Ly) with hcr_def
  have hcr_gt1 : 1 < c_r := by dsimp only [c_r]; linarith [div_pos one_pos (by linarith : 0 < 2 * Ly)]
  have hcr_le2 : c_r ≤ 2 := by
    have h2Ly : 1 ≤ 2 * Ly := by linarith [Real.log_two_gt_d9]
    have : 1 / (2 * Ly) ≤ 1 := (div_le_one (by linarith)).mpr h2Ly
    dsimp only [c_r]; linarith
  have hy_pow_cr : y ^ (c_r + 1) ≤ 2 * y ^ 2 := by
    have h1 : y ^ (c_r + 1) = y ^ 2 * y ^ (1 / (2 * Ly)) := by
      rw [show c_r + 1 = (2 : ℝ) + 1 / (2 * Ly) by dsimp only [c_r]; ring,
        Real.rpow_add hy0, show y ^ (2 : ℝ) = y ^ (2 : ℕ) by norm_cast]
    have h2 : y ^ (1 / (2 * Ly)) = Real.exp (1 / 2) := by
      rw [Real.rpow_def_of_pos hy0, ← hLy_def]
      congr 1; field_simp [hLy_pos.ne']
    have h3 : Real.exp (1 / 2) ≤ 2 := by
      have hsq : (Real.exp (1 / 2)) ^ 2 ≤ 2 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num; linarith [Real.exp_one_lt_d9]
      nlinarith [Real.exp_pos (1 / 2)]
    rw [h1, h2]; nlinarith [sq_nonneg y]
  set σ_T : ℝ := 1 - c_star / L_QT with hσ_def
  have hσ_lt1 : σ_T < 1 := by dsimp only [σ_T]; linarith [div_pos hc_star_pos hLQT_pos]
  have hσ_ge_half : 1 / 2 ≤ σ_T := by
    have h1 : c_star / L_QT ≤ 1 / 4 := by
      calc c_star / L_QT ≤ c_star / 1 := div_le_div_of_nonneg_left hc_star_pos.le zero_lt_one hLQT_gt1.le
        _ = c_star := div_one _
        _ ≤ 1 / 4 := hc_star_le_qtr
    dsimp only [σ_T]; linarith
  have hσ_pos : 0 < σ_T := by linarith
  have hrect_bd : ∀ z : ℂ, σ_T ≤ z.re → z.re ≤ c_r → |z.im| ≤ T →
      DirichletCharacter.LFunction χ z ≠ 0 ∧
      ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ ≤
        C₁ * L_QT ^ 2 := by
    intro z hlo hhi him
    have hlog_le : Real.log (Q * (|z.im| + 2)) ≤ L_QT :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    have hlog_pos : 0 < Real.log (Q * (|z.im| + 2)) :=
      Real.log_pos (by nlinarith [abs_nonneg z.im])
    have h1 : c_star / L_QT ≤ c₁ / Real.log (Q * (|z.im| + 2)) := by
      calc c_star / L_QT ≤ c_star / Real.log (Q * (|z.im| + 2)) :=
            div_le_div_of_nonneg_left hc_star_pos.le hlog_pos hlog_le
        _ ≤ c₁ / Real.log (Q * (|z.im| + 2)) :=
            div_le_div_of_nonneg_right hc_star_le_c₁ hlog_pos.le
    obtain ⟨hnz, hnd⟩ := hbd z (by linarith) (by linarith)
    refine ⟨hnz, hnd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog_pos.le hlog_le 2) hC₁.le)⟩
  have hzf_rect : ∀ z : ℂ, σ_T ≤ z.re → z.re ≤ c_r → |z.im| ≤ T →
      DirichletCharacter.LFunction χ z ≠ 0 :=
    fun z hlo hhi him => (hrect_bd z hlo hhi him).1
  set F : ℂ → ℂ := fun s =>
    Stage3ZeroFreeRegion.negLogDerivL χ s * (y : ℂ) ^ (s + 1) / (s * (s + 1))
  -- (A) Truncation error
  have htrunc_err :
      ‖Stage4ExplicitFormula.psi1Char χ y - Stage4ExplicitFormula.truncatedPerronPsi1 χ y c_r T‖ ≤
        (48 / Real.pi) * y ^ 2 * Ly / T := by
    have h0 := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le χ hy0 hcr_gt1 hT_pos
    have hc_sub : c_r - 1 = 1 / (2 * Ly) := by dsimp only [c_r]; ring
    rw [hc_sub] at h0
    calc ‖Stage4ExplicitFormula.psi1Char χ y - Stage4ExplicitFormula.truncatedPerronPsi1 χ y c_r T‖
        ≤ (6 * c_r / Real.pi) * y ^ (c_r + 1) / (1 / (2 * Ly) * T) := h0
      _ ≤ (6 * 2 / Real.pi) * (2 * y ^ 2) / (1 / (2 * Ly) * T) := by gcongr
      _ = (48 / Real.pi) * y ^ 2 * Ly / T := by
          field_simp [Real.pi_ne_zero, hLy_pos.ne', hT_pos.ne']; ring
  -- (B) Exact pole-free Perron contour shift
  have hshift := Stage7PNTInAP.perron_contour_shift_psi1Char hχ hy0 hσ_pos (by linarith) hT_pos hzf_rect
  -- (C) Horizontal edges `t = ±T`
  have hhoriz_bd : ∀ sgn : ℝ, |sgn| = 1 →
      ‖∫ v in σ_T..c_r, F ((v : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
        2 * C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2 := by
    intro sgn hsgn
    have hle : σ_T ≤ c_r := by linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2) fun v hv => ?_).trans ?_
    · rw [Set.uIoc_of_le hle] at hv
      set z : ℂ := (v : ℂ) + ((sgn * T : ℝ) : ℂ) * I
      have hz_re : z.re = v := by simp [z]
      have hz_im : z.im = sgn * T := by simp [z]
      have hz_abs_im : |z.im| = T := by
        rw [hz_im, abs_mul, hsgn, one_mul, abs_of_pos hT_pos]
      have hnd := (hrect_bd z (by rw [hz_re]; exact hv.1.le) (by rw [hz_re]; exact hv.2)
        (by rw [hz_abs_im])).2
      have hpow_norm : ‖(y : ℂ) ^ (z + 1)‖ ≤ y ^ (c_r + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
        have hre1 : (z + 1).re = v + 1 := by simp [hz_re]
        rw [hre1]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hv.2])
      have hden_ge : T ^ 2 ≤ ‖z * (z + 1)‖ := by
        rw [norm_mul]
        have h1 : T ≤ ‖z‖ := by rw [← hz_abs_im]; exact Complex.abs_im_le_norm z
        have h2 : T ≤ ‖z + 1‖ := by
          have := Complex.abs_im_le_norm (z + 1); simpa [hz_abs_im] using this
        nlinarith
      dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
      rw [norm_div, norm_mul]
      calc ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ *
              ‖(y : ℂ) ^ (z + 1)‖ / ‖z * (z + 1)‖
          ≤ (C₁ * L_QT ^ 2) * y ^ (c_r + 1) / T ^ 2 :=
            div_le_div₀ (by positivity)
              (mul_le_mul hnd hpow_norm (norm_nonneg _) (by positivity))
              (sq_pos_of_pos hT_pos) hden_ge
        _ = C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2 := by ring
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      have hlen : c_r - σ_T ≤ 2 := by linarith
      calc C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2 * (c_r - σ_T)
          ≤ C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2 * 2 :=
            mul_le_mul_of_nonneg_left hlen (by positivity)
        _ = 2 * C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2 := by ring
  have htop_bd : ‖∫ v in σ_T..c_r, F ((v : ℂ) + (T : ℂ) * I)‖ ≤
      2 * C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2 := by simpa using hhoriz_bd 1 (by norm_num)
  have hbot_bd : ‖∫ v in σ_T..c_r, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
      2 * C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2 := by simpa using hhoriz_bd (-1) (by norm_num)
  -- (D) Left vertical edge `Re(s) = σ_T`, `t ∈ [-T, T]`
  have hleft_cont : ContinuousOn (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
    have hL_cont : Continuous (DirichletCharacter.LFunction χ) :=
      (DirichletCharacter.differentiable_LFunction hχ).continuous
    have hL'_cont : Continuous (deriv (DirichletCharacter.LFunction χ)) :=
      continuousOn_univ.mp
        ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.deriv isOpen_univ).continuousOn
    have hmap : Continuous (fun t : ℝ => (σ_T : ℂ) + (t : ℂ) * I) := by fun_prop
    have hnd_cont : ContinuousOn
        (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ ((σ_T : ℂ) + (t : ℂ) * I))
        (Set.Icc (-T) T) := by
      unfold Stage3ZeroFreeRegion.negLogDerivL
      refine (hL'_cont.comp hmap).neg.continuousOn.div (hL_cont.comp hmap).continuousOn fun t ht => ?_
      exact hzf_rect _ (by simp) (by simp; linarith) (by simp [abs_le, ht.1, ht.2])
    have hpow_cont : Continuous (fun t : ℝ => (y : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) := by
      have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
      have hEq : (fun t : ℝ => (y : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) =
          fun t : ℝ => cexp (Complex.log (y : ℂ) * (((σ_T : ℂ) + (t : ℂ) * I) + 1)) :=
        funext fun t => Complex.cpow_def_of_ne_zero hyC _
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
  have hleft_tail_pt : ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
      ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * L_QT ^ 2 * y ^ (σ_T + 1) / t ^ 2 := by
    intro t ht1 htT
    set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
    have hz_re : z.re = σ_T := by simp [z]
    have hz_im : z.im = t := by simp [z]
    have hnd' := (hrect_bd z (by simp [z]) (by simp [z]; linarith) (by simp [z, htT])).2
    have hpow : ‖(y : ℂ) ^ (z + 1)‖ = y ^ (σ_T + 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]; simp [hz_re]
    have hden : t ^ 2 ≤ ‖z * (z + 1)‖ := by
      rw [norm_mul]
      have h1 : |t| ≤ ‖z‖ := by rw [← hz_im]; exact Complex.abs_im_le_norm z
      have h2 : |t| ≤ ‖z + 1‖ := by
        have := Complex.abs_im_le_norm (z + 1); simpa [hz_im] using this
      have hsq : t ^ 2 = |t| * |t| := by rw [← sq_abs, sq]
      rw [hsq]; exact mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg z)
    have ht2_pos : 0 < t ^ 2 := by
      have : t ≠ 0 := fun h => by rw [h, abs_zero] at ht1; linarith
      positivity
    dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
    rw [norm_div, norm_mul, hpow]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hy0.le _)) ht2_pos hden
  have hinv_sq_1T : ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ ≤ 1 := by
    have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun w : ℝ => -(w⁻¹)) (t ^ 2)⁻¹ t := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact ((hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).neg).congr_deriv (by ring)
    have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (1 : ℝ) T) := by
      rw [Set.uIcc_of_le (by linarith)]
      exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
    linarith [inv_nonneg.mpr hT_pos.le]
  have hinv_sq_neg : ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ ≤ 1 := by
    have hd : ∀ t ∈ Set.uIcc (-T) (-1 : ℝ), HasDerivAt (fun w : ℝ => -(w⁻¹)) (t ^ 2)⁻¹ t := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact ((hasDerivAt_inv (by linarith [ht.2] : t ≠ 0)).neg).congr_deriv (by ring)
    have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (-T) (-1 : ℝ)) := by
      rw [Set.uIcc_of_le (by linarith)]
      exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.2])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
    simp only [inv_neg, neg_neg, inv_one]
    linarith [inv_nonneg.mpr hT_pos.le]
  have hleft_pos_bd : ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
      C₁ * L_QT ^ 2 * y ^ (σ_T + 1) := by
    have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * L_QT ^ 2 * y ^ (σ_T + 1) * (t ^ 2)⁻¹)
        volume (1 : ℝ) T := by
      refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)] at ht; exact pow_ne_zero 2 (by linarith [ht.1])
    calc ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t in (1 : ℝ)..T, ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ t in (1 : ℝ)..T, C₁ * L_QT ^ 2 * y ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hint_seg 1 T (by linarith) (by linarith) le_rfl).norm hint_dom fun t ht => ?_
          rw [← div_eq_mul_inv]
          exact hleft_tail_pt t (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1)
            (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.2)
      _ = C₁ * L_QT ^ 2 * y ^ (σ_T + 1) * ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ C₁ * L_QT ^ 2 * y ^ (σ_T + 1) * 1 :=
          mul_le_mul_of_nonneg_left hinv_sq_1T (by positivity)
      _ = C₁ * L_QT ^ 2 * y ^ (σ_T + 1) := mul_one _
  have hleft_neg_bd : ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
      C₁ * L_QT ^ 2 * y ^ (σ_T + 1) := by
    have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * L_QT ^ 2 * y ^ (σ_T + 1) * (t ^ 2)⁻¹)
        volume (-T) (-1 : ℝ) := by
      refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)] at ht; exact pow_ne_zero 2 (by linarith [ht.2])
    calc ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t in (-T)..(-1 : ℝ), ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ t in (-T)..(-1 : ℝ), C₁ * L_QT ^ 2 * y ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith)).norm hint_dom fun t ht => ?_
          rw [← div_eq_mul_inv]
          exact hleft_tail_pt t (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
            (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
      _ = C₁ * L_QT ^ 2 * y ^ (σ_T + 1) * ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ C₁ * L_QT ^ 2 * y ^ (σ_T + 1) * 1 :=
          mul_le_mul_of_nonneg_left hinv_sq_neg (by positivity)
      _ = C₁ * L_QT ^ 2 * y ^ (σ_T + 1) := mul_one _
  have hleft_mid_bd : ‖∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
      4 * C₁ * L_QT ^ 2 * y ^ (σ_T + 1) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 2 * C₁ * L_QT ^ 2 * y ^ (σ_T + 1)) fun t ht => ?_).trans ?_
    · rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have htT : |t| ≤ T := by
        have : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩; linarith
      have hnd' := (hrect_bd z (by simp [z]) (by simp [z]; linarith) (by simp [z, htT])).2
      have hpow : ‖(y : ℂ) ^ (z + 1)‖ = y ^ (σ_T + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]; simp [hz_re]
      have hden : 1 / 2 ≤ ‖z * (z + 1)‖ := by
        rw [norm_mul]
        have h1 : 1 / 2 ≤ ‖z‖ := by
          have := Complex.abs_re_le_norm z; rw [hz_re, abs_of_pos hσ_pos] at this; linarith
        have h2 : 1 ≤ ‖z + 1‖ := by
          have := Complex.abs_re_le_norm (z + 1)
          have hre1 : (z + 1).re = σ_T + 1 := by simp [hz_re]
          rw [hre1, abs_of_pos (by linarith)] at this; linarith
        nlinarith
      dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
      rw [norm_div, norm_mul, hpow]
      calc ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ *
              y ^ (σ_T + 1) / ‖z * (z + 1)‖
          ≤ (C₁ * L_QT ^ 2) * y ^ (σ_T + 1) / (1 / 2) :=
            div_le_div₀ (by positivity)
              (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hy0.le _)) (by norm_num) hden
        _ = 2 * C₁ * L_QT ^ 2 * y ^ (σ_T + 1) := by ring
    · norm_num; linarith
  have hleft_bd : ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
      6 * C₁ * L_QT ^ 2 * y ^ (σ_T + 1) := by
    rw [hsplit_left]
    have htri1 := norm_add_le
      ((∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
        (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)))
      (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I))
    have htri2 := norm_add_le
      (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I))
      (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I))
    linarith
  -- (E) Combine all contour pieces
  have hshift_bd :
      ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ y c_r T‖ ≤
        (3 * C₁ / Real.pi) * L_QT ^ 2 * y ^ (σ_T + 1) +
        (2 * C₁ / Real.pi) * L_QT ^ 2 * y ^ 2 / T := by
    rw [hshift]
    have hnorm_2pi : ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hnorm_2piI : ‖((2 * Real.pi * I : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
    have htri :
        ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c_r, F ((v : ℂ) + (T : ℂ) * I)) -
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c_r, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤
        (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ +
        (2 * Real.pi)⁻¹ * ‖∫ v in σ_T..c_r, F ((v : ℂ) + (T : ℂ) * I)‖ +
        (2 * Real.pi)⁻¹ * ‖∫ v in σ_T..c_r, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
      have h1 := norm_sub_le
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c_r, F ((v : ℂ) + (T : ℂ) * I)))
        (((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c_r, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)))
      have h2 := norm_add_le
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)))
        (((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c_r, F ((v : ℂ) + (T : ℂ) * I)))
      simp only [norm_mul, hnorm_2pi, hnorm_2piI] at h1 h2
      linarith
    have hterm_left : (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        (3 * C₁ / Real.pi) * L_QT ^ 2 * y ^ (σ_T + 1) := by
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ (2 * Real.pi)⁻¹ * (6 * C₁ * L_QT ^ 2 * y ^ (σ_T + 1)) :=
            mul_le_mul_of_nonneg_left hleft_bd (by positivity)
        _ = (3 * C₁ / Real.pi) * L_QT ^ 2 * y ^ (σ_T + 1) := by field_simp [Real.pi_ne_zero]; ring
    have hterm_horiz : ∀ Ival : ℂ, ‖Ival‖ ≤ 2 * C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2 →
        (2 * Real.pi)⁻¹ * ‖Ival‖ ≤ (C₁ / Real.pi) * L_QT ^ 2 * y ^ 2 / T := by
      intro Ival hIval
      have hyc_div : y ^ (c_r + 1) / T ^ 2 ≤ y ^ 2 / T := by
        have h1 : y ^ (c_r + 1) / T ^ 2 ≤ (2 * y ^ 2) / T ^ 2 :=
          div_le_div_of_nonneg_right hy_pow_cr (sq_nonneg T)
        have h2 : 2 * y ^ 2 / T ^ 2 ≤ y ^ 2 / T := by
          rw [div_le_div_iff₀ (sq_pos_of_pos hT_pos) hT_pos]
          have hT2 : 2 * T ≤ T ^ 2 := by nlinarith
          nlinarith [sq_nonneg y]
        linarith
      calc (2 * Real.pi)⁻¹ * ‖Ival‖
          ≤ (2 * Real.pi)⁻¹ * (2 * C₁ * L_QT ^ 2 * y ^ (c_r + 1) / T ^ 2) :=
            mul_le_mul_of_nonneg_left hIval (by positivity)
        _ = (C₁ / Real.pi) * L_QT ^ 2 * (y ^ (c_r + 1) / T ^ 2) := by
            field_simp [Real.pi_ne_zero, hT_pos.ne']
        _ ≤ (C₁ / Real.pi) * L_QT ^ 2 * (y ^ 2 / T) :=
            mul_le_mul_of_nonneg_left hyc_div (by positivity)
        _ = (C₁ / Real.pi) * L_QT ^ 2 * y ^ 2 / T := by ring
    have htop_h := hterm_horiz _ htop_bd
    have hbot_h := hterm_horiz _ hbot_bd
    change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
        ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c_r, F ((v : ℂ) + (T : ℂ) * I)) -
        ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c_r, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤ _
    have hsum2 : (C₁ / Real.pi) * L_QT ^ 2 * y ^ 2 / T + (C₁ / Real.pi) * L_QT ^ 2 * y ^ 2 / T =
        (2 * C₁ / Real.pi) * L_QT ^ 2 * y ^ 2 / T := by ring
    linarith
  have htotal : ‖Stage4ExplicitFormula.psi1Char χ y‖ ≤
      (48 / Real.pi) * y ^ 2 * Ly / T +
      (3 * C₁ / Real.pi) * L_QT ^ 2 * y ^ (σ_T + 1) +
      (2 * C₁ / Real.pi) * L_QT ^ 2 * y ^ 2 / T := by
    have htri : ‖Stage4ExplicitFormula.psi1Char χ y‖ ≤
        ‖Stage4ExplicitFormula.psi1Char χ y - Stage4ExplicitFormula.truncatedPerronPsi1 χ y c_r T‖ +
        ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ y c_r T‖ := by
      simpa [sub_add_cancel] using norm_add_le
        (Stage4ExplicitFormula.psi1Char χ y - Stage4ExplicitFormula.truncatedPerronPsi1 χ y c_r T)
        (Stage4ExplicitFormula.truncatedPerronPsi1 χ y c_r T)
    linarith
  have hLQT_sq : L_QT ^ 2 ≤ 9 * α ^ 2 * Ly := by
    have h1 := pow_le_pow_left₀ hLQT_pos.le hLQT_le 2
    have h2 : (3 * α * u) ^ 2 = 9 * α ^ 2 * Ly := by rw [← hu_sq]; ring
    linarith
  have hy_left_exp : y ^ (σ_T + 1) ≤ y ^ 2 * Real.exp (-α * u) := by
    have h1 : y ^ (σ_T + 1) = y ^ 2 * y ^ (-(c_star / L_QT)) := by
      rw [show σ_T + 1 = (2 : ℝ) + (-(c_star / L_QT)) by dsimp only [σ_T]; ring,
        Real.rpow_add hy0, show y ^ (2 : ℝ) = y ^ (2 : ℕ) by norm_cast]
    have h2 : y ^ (-(c_star / L_QT)) = Real.exp (-(c_star * Ly / L_QT)) := by
      rw [Real.rpow_def_of_pos hy0, ← hLy_def]; congr 1; ring
    have hexp_le : -(c_star * Ly / L_QT) ≤ -α * u := by
      have hdiv : α * u ≤ c_star * Ly / L_QT := by
        rw [le_div_iff₀ hLQT_pos]
        calc α * u * L_QT ≤ α * u * (3 * α * u) :=
              mul_le_mul_of_nonneg_left hLQT_le (by positivity)
          _ = 3 * α ^ 2 * u ^ 2 := by ring
          _ = (1 / 2) * (6 * α ^ 2) * Ly := by rw [hu_sq]; ring
          _ = (1 / 2) * (c_star * Ly) := by rw [h6α2]; ring
          _ ≤ c_star * Ly := by nlinarith
      linarith
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (sq_nonneg y)
  have hinvT : (1 : ℝ) / T = Real.exp (-α * u) := by
    rw [hT_def, one_div, ← Real.exp_neg]; congr 1; ring
  have habsorb : Ly * Real.exp (-α * u) ≤ (4 / α) ^ 2 * Real.exp (-c_fin * u) := by
    have hsplit : Real.exp (-α * u) = Real.exp (-2 * ((α / 4) * u)) * Real.exp (-c_fin * u) := by
      rw [← Real.exp_add]; congr 1; dsimp only [c_fin]; ring
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hid : Ly * Real.exp (-2 * ((α / 4) * u)) =
        (4 / α) ^ 2 * (((α / 4) * u) ^ 2 * Real.exp (-2 * ((α / 4) * u))) := by
      have h1 : Ly = (4 / α) ^ 2 * ((α / 4) * u) ^ 2 := by
        rw [← mul_pow, show (4 / α) * ((α / 4) * u) = u by field_simp [hα_pos.ne'], hu_sq]
      have h2 := congrArg (· * Real.exp (-2 * ((α / 4) * u))) h1
      simpa only [mul_assoc] using h2
    calc Ly * Real.exp (-2 * ((α / 4) * u))
        = (4 / α) ^ 2 * (((α / 4) * u) ^ 2 * Real.exp (-2 * ((α / 4) * u))) := hid
      _ ≤ (4 / α) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (sq_mul_exp_neg_two_le_one (by positivity)) (by positivity)
      _ = (4 / α) ^ 2 := mul_one _
  have hterm1 : (48 / Real.pi) * y ^ 2 * Ly / T =
      (48 / Real.pi) * y ^ 2 * (Ly * Real.exp (-α * u)) := by
    rw [div_eq_mul_inv, ← one_div, hinvT]; ring
  have hterm2 : (3 * C₁ / Real.pi) * L_QT ^ 2 * y ^ (σ_T + 1) ≤
      (27 * C₁ * α ^ 2 / Real.pi) * y ^ 2 * (Ly * Real.exp (-α * u)) := by
    calc (3 * C₁ / Real.pi) * L_QT ^ 2 * y ^ (σ_T + 1)
        ≤ (3 * C₁ / Real.pi) * (9 * α ^ 2 * Ly) * (y ^ 2 * Real.exp (-α * u)) := by gcongr
      _ = (27 * C₁ * α ^ 2 / Real.pi) * y ^ 2 * (Ly * Real.exp (-α * u)) := by ring
  have hterm3 : (2 * C₁ / Real.pi) * L_QT ^ 2 * y ^ 2 / T ≤
      (18 * C₁ * α ^ 2 / Real.pi) * y ^ 2 * (Ly * Real.exp (-α * u)) := by
    rw [div_eq_mul_inv, ← one_div, hinvT]
    calc (2 * C₁ / Real.pi) * L_QT ^ 2 * y ^ 2 * Real.exp (-α * u)
        ≤ (2 * C₁ / Real.pi) * (9 * α ^ 2 * Ly) * y ^ 2 * Real.exp (-α * u) := by gcongr
      _ = (18 * C₁ * α ^ 2 / Real.pi) * y ^ 2 * (Ly * Real.exp (-α * u)) := by ring
  calc ‖Stage4ExplicitFormula.psi1Char χ y‖
      ≤ (48 / Real.pi + (27 * C₁ * α ^ 2 / Real.pi) + (18 * C₁ * α ^ 2 / Real.pi)) *
          y ^ 2 * (Ly * Real.exp (-α * u)) := by linarith
    _ ≤ (48 / Real.pi + (27 * C₁ * α ^ 2 / Real.pi) + (18 * C₁ * α ^ 2 / Real.pi)) *
          y ^ 2 * ((4 / α) ^ 2 * Real.exp (-c_fin * u)) := by gcongr
    _ = K_large * y ^ 2 * Real.exp (-c_fin * u) := by dsimp only [K_large]; ring

/-- **UNCONDITIONAL ZERO-EXCEPTION UNIFORM `ψ₁(y, χ)` BOUND (`c > 0` INDEPENDENT OF `A`!)**:
`∃ c > 0, ∀ A > 0, ∃ C > 0, ∀ y ≥ 4, ∀ q ≤ (log y)^A, ∀ χ ≠ 1, ‖psi1Char χ y‖ ≤ C * y^2 * exp(-c √(log y))`. -/
theorem siegel_walfisz_psi1Char_uniform :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ y : ℝ, 4 ≤ y →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log y) ^ A →
              ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
                ‖Stage4ExplicitFormula.psi1Char χ y‖ ≤
                  C * y ^ 2 * Real.exp (-c * Real.sqrt (Real.log y)) := by
  set α : ℝ := Real.sqrt (min sw_c1 (1 / 4) / 6) with hα_def
  have hα_pos : 0 < α := Real.sqrt_pos.mpr (by have := sw_c1_pos; positivity)
  set c_fin : ℝ := α / 2 with hc_fin_def
  have hc_fin_pos : 0 < c_fin := by positivity
  set y₀ : ℝ := max 2 (Real.exp ((2 / α) ^ 2)) with hy₀_def
  set K_large : ℝ :=
    (48 / Real.pi + (27 * sw_C1 * α ^ 2 / Real.pi) + (18 * sw_C1 * α ^ 2 / Real.pi)) * (4 / α) ^ 2
  have hK_large_pos : 0 < K_large := by have := sw_C1_pos; positivity
  refine ⟨c_fin, hc_fin_pos, fun A hA => ?_⟩
  obtain ⟨X_A, hXA4, hbdA⟩ := siegel_walfisz_negLogDerivL_bound_at_scale hα_pos hA
  set X_cut : ℝ := max X_A y₀ with hXcut_def
  have hXcut_ge4 : 4 ≤ X_cut := hXA4.trans (le_max_left _ _)
  set C_small : ℝ := 6 * Real.exp (c_fin * Real.sqrt (Real.log X_cut))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨C_fin, hC_fin_pos, fun y hy4 q _ hq χ hχ => ?_⟩
  by_cases hge : X_cut ≤ y
  · have hyXA : X_A ≤ y := (le_max_left _ _).trans hge
    have hyy₀ : y₀ ≤ y := (le_max_right _ _).trans hge
    set Q_b : ℝ := Real.exp (α * Real.sqrt (Real.log y))
    have hQb_ge2 : 2 ≤ Q_b := by
      have hLy_ge : (2 / α) ^ 2 ≤ Real.log y := by
        have hexp : Real.exp ((2 / α) ^ 2) ≤ y := (le_max_right _ _).trans hyy₀
        exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hexp)
      have hαu : 2 ≤ α * Real.sqrt (Real.log y) := by
        have h1 : 2 / α ≤ Real.sqrt (Real.log y) := Real.le_sqrt_of_sq_le hLy_ge
        have h2 := mul_le_mul_of_nonneg_left h1 hα_pos.le
        rwa [mul_div_cancel₀ _ hα_pos.ne'] at h2
      have h1 : Real.exp 1 ≤ Q_b := Real.exp_le_exp.mpr (by linarith)
      linarith [Real.exp_one_gt_d9]
    have hbd_Q : ∀ s : ℂ, 1 - sw_c1 / Real.log (Q_b * (|s.im| + 2)) ≤ s.re → s.re ≤ 2 →
        DirichletCharacter.LFunction χ s ≠ 0 ∧
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
          sw_C1 * (Real.log (Q_b * (|s.im| + 2))) ^ 2 := by
      intro s hs_lo hs_hi
      have hlog_eq : Real.log (Q_b * (|s.im| + 2)) =
          α * Real.sqrt (Real.log y) + Real.log (|s.im| + 2) := by
        dsimp only [Q_b]
        rw [Real.log_mul (Real.exp_pos _).ne' (by linarith [abs_nonneg s.im]), Real.log_exp]
      rw [hlog_eq] at hs_lo ⊢
      exact hbdA y hyXA q hq χ hχ s hs_lo hs_hi
    have hperr := psi1Char_bound_of_negLogDerivL_bound sw_c1_pos sw_C1_pos hQb_ge2 hχ hbd_Q hyy₀ le_rfl
    exact hperr.trans (by gcongr; exact le_max_left _ _)
  · push Not at hge
    have hpsi1_le : ‖Stage4ExplicitFormula.psi1Char χ y‖ ≤ 6 * y ^ 2 := by
      have h1 : ‖Stage4ExplicitFormula.psi1Char χ y‖ ≤ y * RHDirect.chebyshevPsi y := by
        unfold Stage4ExplicitFormula.psi1Char RHDirect.chebyshevPsi
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.norm_of_nonneg (le_max_right _ _)]
        have hmax : max (y - (n : ℝ)) 0 ≤ y :=
          max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
        have hchi : ‖χ n‖ ≤ 1 := χ.norm_le_one _
        calc Λ n * ‖χ n‖ * max (y - (n : ℝ)) 0
            ≤ Λ n * 1 * y :=
              mul_le_mul (mul_le_mul_of_nonneg_left hchi ArithmeticFunction.vonMangoldt_nonneg)
                hmax (le_max_right _ _) (by linarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)])
          _ = y * Λ n := by ring
      have h2 := Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith : 1 ≤ y)
      nlinarith
    have hexp_ge :
        Real.exp (-c_fin * Real.sqrt (Real.log X_cut)) ≤ Real.exp (-c_fin * Real.sqrt (Real.log y)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log y ≤ Real.log X_cut := Real.log_le_log (by linarith) hge.le
      nlinarith [Real.sqrt_le_sqrt hlog]
    have hcancel : C_small * Real.exp (-c_fin * Real.sqrt (Real.log X_cut)) = 6 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : c_fin * Real.sqrt (Real.log X_cut) + -c_fin * Real.sqrt (Real.log X_cut) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc ‖Stage4ExplicitFormula.psi1Char χ y‖
        ≤ 6 * y ^ 2 := hpsi1_le
      _ = C_small * y ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log X_cut)) := by rw [← hcancel]; ring
      _ ≤ C_small * y ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log y)) := by gcongr
      _ ≤ C_fin * y ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log y)) := by
          gcongr; exact le_max_right _ _

/-- **UNCONDITIONAL FULL SIEGEL–WALFISZ UNIFORM CHARACTER-SUM DECAY (`0` EXCEPTIONS!)**:
there exists an ABSOLUTE constant `c > 0` such that for EVERY `A > 0`, there exists `C > 0` such
that for ALL `x ≥ 4`, ALL `q ≤ (Real.log x) ^ A` (`[NeZero q]`), and ALL non-principal
`χ : DirichletCharacter ℂ q` (`χ ≠ 1`):
`‖chebyshevPsiChar χ x‖ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem siegel_walfisz_character_psi_uniform :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
                ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
                  C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c₁, hc₁, hpsi1_all⟩ := siegel_walfisz_psi1Char_uniform
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  set c_fin : ℝ := min (c₁ / 2) c_ψ with hc_fin_def
  have hc_fin_pos : 0 < c_fin := lt_min (by positivity) hc_ψ
  have hc_fin_le1 : c_fin ≤ c₁ / 2 := min_le_left _ _
  have hc_fin_le_ψ : c_fin ≤ c_ψ := min_le_right _ _
  refine ⟨c_fin, hc_fin_pos, fun A hA => ?_⟩
  obtain ⟨C₁, hC₁, hpsi1⟩ := hpsi1_all A hA
  set C_fin : ℝ := 5 * C₁ + 1 + 3 * C_ψ
  have hC_fin_pos : 0 < C_fin := by positivity
  refine ⟨C_fin, hC_fin_pos, fun x hx4 q _ hq χ hχ => ?_⟩
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  set u : ℝ := Real.sqrt (Real.log x) with hu_def
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hLx_pos
  set E : ℝ := Real.exp (-c_fin * u) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_le1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  set h : ℝ := x * E with hh_def
  have hh_pos : 0 < h := by positivity
  have hh_le_x : h ≤ x := by nlinarith
  have hxph_ge4 : 4 ≤ x + h := by linarith
  have hxph_le2x : x + h ≤ 2 * x := by linarith
  have hlog_le : Real.log x ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
  have hsqrt_le : u ≤ Real.sqrt (Real.log (x + h)) := Real.sqrt_le_sqrt hlog_le
  have hq_xh : (q : ℝ) ≤ (Real.log (x + h)) ^ A :=
    hq.trans (Real.rpow_le_rpow hLx_pos.le hlog_le hA.le)
  have hexp_E2 : Real.exp (-c₁ * u) ≤ E ^ 2 := by
    rw [hE_def, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr; push_cast; nlinarith
  have hexp_xh : Real.exp (-c₁ * Real.sqrt (Real.log (x + h))) ≤ E ^ 2 :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans hexp_E2
  have hexp_psi : Real.exp (-c_ψ * u) ≤ E :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexp_psi_xh : Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤ E :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans hexp_psi
  have hdiff := Stage7PNTInAP.norm_psi1Char_diff_sub_mul_chebyshevPsiChar_le χ hx0.le hh_pos.le
  have hnorm_mul : h * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
      ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖ + ‖Stage4ExplicitFormula.psi1Char χ x‖ +
        h * (RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x) := by
    have h1 : ‖(h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x‖ +
        ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
      have htri := norm_sub_le
        (Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x)
        (Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x)
      simpa [sub_sub_cancel] using htri
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh_pos.le] at h1
    linarith [norm_sub_le (Stage4ExplicitFormula.psi1Char χ (x + h)) (Stage4ExplicitFormula.psi1Char χ x)]
  have hbd_xh : ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖ ≤ 4 * C₁ * x ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖
        ≤ C₁ * (x + h) ^ 2 * Real.exp (-c₁ * Real.sqrt (Real.log (x + h))) :=
          hpsi1 (x + h) hxph_ge4 q hq_xh χ hχ
      _ ≤ C₁ * (2 * x) ^ 2 * E ^ 2 := by
          have hsq : (x + h) ^ 2 ≤ (2 * x) ^ 2 := by nlinarith
          gcongr
      _ = 4 * C₁ * x ^ 2 * E ^ 2 := by ring
  have hbd_x : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ C₁ * x ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ C₁ * x ^ 2 * Real.exp (-c₁ * u) := hpsi1 x hx4 q hq χ hχ
      _ ≤ C₁ * x ^ 2 * E ^ 2 := by gcongr
  have hpsi_diff_le :
      RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x ≤ (1 + 3 * C_ψ) * x * E := by
    have h1 := (abs_le.mp (hpsi (x + h) (by linarith))).2
    have h2 := (abs_le.mp (hpsi x (by linarith))).1
    have h3 : C_ψ * (x + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤ 2 * C_ψ * x * E := by
      calc C_ψ * (x + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (x + h)))
          ≤ C_ψ * (2 * x) * E := by gcongr
        _ = 2 * C_ψ * x * E := by ring
    have h4 : C_ψ * x * Real.exp (-c_ψ * u) ≤ C_ψ * x * E := by gcongr
    dsimp only [h] at h1 h2 h3 ⊢
    linarith
  have hcomb : h * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ h * (C_fin * x * E) := by
    have hrhs1 : 5 * C₁ * x ^ 2 * E ^ 2 = h * (5 * C₁ * x * E) := by dsimp only [h]; ring
    have hmul_psi := mul_le_mul_of_nonneg_left hpsi_diff_le hh_pos.le
    have hrhs2 : h * (5 * C₁ * x * E) + h * ((1 + 3 * C_ψ) * x * E) = h * (C_fin * x * E) := by
      dsimp only [C_fin]; ring
    linarith
  exact le_of_mul_le_mul_left hcomb hh_pos

/-! ## Section 3: Unconditional Full Siegel–Walfisz Theorem (1936) for `ψ`, `θ`, and `π` (`0` Exceptions!) -/

/-- Helper: `(log x) ^ 2 ≤ 16 * x * exp (-c * √(log x))` for `0 < c ≤ 1 / 2` and `x ≥ 4`. -/
private lemma log_sq_le_16_mul_x_exp_neg_sqrt {c x : ℝ} (hc_le : c ≤ 1 / 2) (hx4 : 4 ≤ x) :
    (Real.log x) ^ 2 ≤ 16 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  have hu_le_Lx : Real.sqrt (Real.log x) ≤ Real.log x := by
    have hsq : (Real.sqrt (Real.log x)) ^ 2 = Real.log x := Real.sq_sqrt hLx_pos.le
    nlinarith [Real.sqrt_nonneg (Real.log x)]
  have hexp1 : Real.exp (-(1 / 2) * Real.log x) ≤ Real.exp (-c * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg (Real.log x)])
  have hx_exp : x * Real.exp (-(1 / 2) * Real.log x) = Real.exp ((1 / 2) * Real.log x) := by
    conv_lhs => lhs; rw [← Real.exp_log hx0]
    rw [← Real.exp_add]; congr 1; ring
  have hsq_exp : (Real.log x) ^ 2 * Real.exp (-(1 / 2) * Real.log x) ≤ 16 := by
    have h := sq_mul_exp_neg_two_le_one (u := Real.log x / 4) (by positivity)
    have hEq : (Real.log x) ^ 2 * Real.exp (-(1 / 2) * Real.log x) =
        16 * ((Real.log x / 4) ^ 2 * Real.exp (-2 * (Real.log x / 4))) := by
      rw [show -(1 / 2 : ℝ) * Real.log x = -2 * (Real.log x / 4) by ring]; ring
    rw [hEq]; linarith
  have hLx2_half : (Real.log x) ^ 2 ≤ 16 * Real.exp ((1 / 2) * Real.log x) := by
    have hmul := mul_le_mul_of_nonneg_right hsq_exp (Real.exp_pos ((1 / 2) * Real.log x)).le
    have hcancel : Real.exp (-(1 / 2) * Real.log x) * Real.exp ((1 / 2) * Real.log x) = 1 := by
      rw [← Real.exp_add]; simp
    rw [mul_assoc, hcancel, mul_one] at hmul
    exact hmul
  calc (Real.log x) ^ 2 ≤ 16 * Real.exp ((1 / 2) * Real.log x) := hLx2_half
    _ = 16 * (x * Real.exp (-(1 / 2) * Real.log x)) := by rw [hx_exp]
    _ ≤ 16 * (x * Real.exp (-c * Real.sqrt (Real.log x))) := by gcongr
    _ = 16 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring

/-- Helper: `√x * log x ≤ 4 * x * exp (-c * √(log x))` for `0 < c ≤ 1 / 4` and `x ≥ 4`. -/
private lemma sqrt_mul_log_le_4_mul_x_exp_neg_sqrt {c x : ℝ} (hc_le : c ≤ 1 / 4) (hx4 : 4 ≤ x) :
    Real.sqrt x * Real.log x ≤ 4 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  set Lx : ℝ := Real.log x with hLx_def
  have hLx_gt1 : 1 < Lx := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Lx := zero_lt_one.trans hLx_gt1
  have hsqrt_eq : Real.sqrt x = x * Real.exp (-(1 / 2) * Lx) := by
    rw [Real.sqrt_eq_rpow]
    have h2 : x ^ (1 / 2 : ℝ) = x * x ^ (-(1 / 2 : ℝ)) := by
      calc x ^ (1 / 2 : ℝ) = x ^ ((1 : ℝ) + -(1 / 2 : ℝ)) := by norm_num
        _ = x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ)) := Real.rpow_add hx0 _ _
        _ = x * x ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
    rw [h2, Real.rpow_def_of_pos hx0, ← hLx_def]; congr 2; ring
  have hsqrt_le : Real.sqrt Lx ≤ Lx := by
    have : Lx ≤ Lx ^ 2 := by nlinarith
    exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hLx_pos.le)
  have hexp_le : Real.exp (-(1 / 2) * Lx) ≤ Real.exp (-(Lx / 4)) * Real.exp (-c * Real.sqrt Lx) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg Lx])
  have h1 : (Lx / 4) * Real.exp (-(Lx / 4)) ≤ 1 := by
    have h := Real.add_one_le_exp (Lx / 4)
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos _)).mpr (by linarith)
  have hkey : Lx * Real.exp (-(1 / 2) * Lx) ≤ 4 * Real.exp (-c * Real.sqrt Lx) := by
    calc Lx * Real.exp (-(1 / 2) * Lx)
        ≤ Lx * (Real.exp (-(Lx / 4)) * Real.exp (-c * Real.sqrt Lx)) :=
          mul_le_mul_of_nonneg_left hexp_le hLx_pos.le
      _ = 4 * ((Lx / 4) * Real.exp (-(Lx / 4))) * Real.exp (-c * Real.sqrt Lx) := by ring
      _ ≤ 4 * 1 * Real.exp (-c * Real.sqrt Lx) := by gcongr
      _ = 4 * Real.exp (-c * Real.sqrt Lx) := by ring
  rw [hsqrt_eq]
  calc x * Real.exp (-(1 / 2) * Lx) * Lx = x * (Lx * Real.exp (-(1 / 2) * Lx)) := by ring
    _ ≤ x * (4 * Real.exp (-c * Real.sqrt Lx)) := mul_le_mul_of_nonneg_left hkey hx0.le
    _ = 4 * x * Real.exp (-c * Real.sqrt Lx) := by ring

/-- **UNCONDITIONAL FULL SIEGEL–WALFISZ THEOREM (1936) FOR `ψ(x; q, a)` (`0` EXCEPTIONS!)**:
there exists an ABSOLUTE constant `c > 0` such that for EVERY `A > 0`, there exists `C > 0` such
that for ALL `x ≥ 4`, ALL `q ≤ (Real.log x) ^ A` (`[NeZero q]`), and ALL `a` with `Nat.Coprime a q`:
`|chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem siegel_walfisz_psi :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ a : ℕ, Nat.Coprime a q →
                |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
                  C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c_ch, hc_ch, hchar_all⟩ := siegel_walfisz_character_psi_uniform
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  set c : ℝ := min c_ch (min c_ψ (1 / 2)) with hc_def
  have hc_pos : 0 < c := by positivity
  have hc_le_ch : c ≤ c_ch := min_le_left _ _
  have hc_le_ψ : c ≤ c_ψ := (min_le_right _ _).trans (min_le_left _ _)
  have hc_le_half : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc_pos, fun A hA => ?_⟩
  obtain ⟨C_ch, hC_ch, hchar⟩ := hchar_all A hA
  set C : ℝ := C_ψ + 32 * A + C_ch with hC_def
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, fun x hx4 q _ hq a hcop => ?_⟩
  have hLx_gt1 : 1 < Real.log x := by
    have : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  set u : ℝ := Real.sqrt (Real.log x) with hu_def
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hLx_pos
  have hE1 : |RHDirect.chebyshevPsi x - x| ≤ C_ψ * x * Real.exp (-c * u) := by
    calc |RHDirect.chebyshevPsi x - x|
        ≤ C_ψ * x * Real.exp (-c_ψ * u) := hpsi x (by linarith)
      _ ≤ C_ψ * x * Real.exp (-c * u) := by gcongr
  have hE2 : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C_ch * x * Real.exp (-c * u) := by
    intro χ hχ
    calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
        ≤ C_ch * x * Real.exp (-c_ch * u) := hchar x hx4 q hq χ hχ
      _ ≤ C_ch * x * Real.exp (-c * u) := by gcongr
  have htri := Stage2DirichletAP.abs_chebyshevPsiAP_sub_le_of_uniform_char_bound hcop (by linarith)
    (by positivity : 0 ≤ C_ch * x * Real.exp (-c * u)) hE1 hE2
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hω_le : (q.primeFactors.card : ℝ) * Real.log x ≤ 32 * A * x * Real.exp (-c * u) := by
    have h1 := Stage2DirichletAP.card_primeFactors_le_log_div_log_two (NeZero.pos q)
    have hlogq_le : Real.log (q : ℝ) ≤ A * Real.log x := by
      have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
      calc Real.log (q : ℝ) ≤ Real.log ((Real.log x) ^ A) := Real.log_le_log hq_pos hq
        _ = A * Real.log (Real.log x) := Real.log_rpow hLx_pos A
        _ ≤ A * Real.log x :=
            mul_le_mul_of_nonneg_left ((Real.log_le_sub_one_of_pos hLx_pos).trans (by linarith)) hA.le
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hcard_le : (q.primeFactors.card : ℝ) ≤ 2 * A * Real.log x := by
      calc (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := h1
        _ ≤ (A * Real.log x) / (1 / 2) :=
            div_le_div₀ (by positivity) hlogq_le (by norm_num) hlog2_gt.le
        _ = 2 * A * Real.log x := by ring
    have hLx2_le := log_sq_le_16_mul_x_exp_neg_sqrt hc_le_half hx4
    calc (q.primeFactors.card : ℝ) * Real.log x
        ≤ (2 * A * Real.log x) * Real.log x := mul_le_mul_of_nonneg_right hcard_le hLx_pos.le
      _ = 2 * A * (Real.log x) ^ 2 := by ring
      _ ≤ 2 * A * (16 * x * Real.exp (-c * u)) := mul_le_mul_of_nonneg_left hLx2_le (by positivity)
      _ = 32 * A * x * Real.exp (-c * u) := by ring
  have hdiv_le :
      (C_ψ * x * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) ≤
        (C_ψ + 32 * A) * x * Real.exp (-c * u) := by
    calc (C_ψ * x * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ)
        ≤ (C_ψ * x * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log x) / 1 :=
          div_le_div_of_nonneg_left (by positivity) zero_lt_one hphi_ge1
      _ = C_ψ * x * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log x := div_one _
      _ ≤ (C_ψ + 32 * A) * x * Real.exp (-c * u) := by linarith
  calc |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)|
      ≤ (C_ψ * x * Real.exp (-c * u) + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) +
          C_ch * x * Real.exp (-c * u) := htri
    _ ≤ (C_ψ + 32 * A) * x * Real.exp (-c * u) + C_ch * x * Real.exp (-c * u) := by linarith
    _ = C * x * Real.exp (-c * u) := by dsimp only [C]; ring

/-- **UNCONDITIONAL FULL SIEGEL–WALFISZ THEOREM (1936) FOR `θ(x; q, a)` (`0` EXCEPTIONS!)**:
there exists an ABSOLUTE constant `c > 0` such that for EVERY `A > 0`, there exists `C > 0` such
that for ALL `x ≥ 4`, ALL `q ≤ (Real.log x) ^ A` (`[NeZero q]`), and ALL `a` with `Nat.Coprime a q`:
`|chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem siegel_walfisz_theta :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ a : ℕ, Nat.Coprime a q →
                |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
                  C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hpsi_all⟩ := siegel_walfisz_psi
  set c' : ℝ := min c (1 / 4) with hc'_def
  have hc'_pos : 0 < c' := lt_min hc (by norm_num)
  have hc'_le_c : c' ≤ c := min_le_left _ _
  have hc'_le_qtr : c' ≤ 1 / 4 := min_le_right _ _
  refine ⟨c', hc'_pos, fun A hA => ?_⟩
  obtain ⟨C, hC, hpsi⟩ := hpsi_all A hA
  refine ⟨C + 4, by positivity, fun x hx4 q _ hq a hcop => ?_⟩
  have hdiff : |Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x| ≤
      Real.sqrt x * Real.log x := by
    have h1 := Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a x
    have h2 := Stage2DirichletAP.chebyshevPsiAP_sub_chebyshevThetaAP_le q a (x := x) (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1)]
    exact h2
  have hsqrt := sqrt_mul_log_le_4_mul_x_exp_neg_sqrt hc'_le_qtr hx4
  have hpsi' : |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
      C * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
    refine (hpsi x hx4 q hq a hcop).trans ?_
    gcongr
  have htri : |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
      |Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x| +
      |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| := by
    simpa [sub_add_sub_cancel] using abs_add_le
      (Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x)
      (Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ))
  linarith

/-- Bridge: `stepSum` of the AP prime-log indicator equals `chebyshevThetaAP`. -/
private lemma stepSum_primeLogAP_eq_thetaAP (q a : ℕ) (x : ℝ) :
    Stage3RealAnalyticLandau.stepSum
        (fun n => if n.Prime ∧ n ≡ a [MOD q] then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0) x =
      (Stage2DirichletAP.chebyshevThetaAP q a x : ℂ) := by
  unfold Stage3RealAnalyticLandau.stepSum Stage2DirichletAP.chebyshevThetaAP
  rw [Complex.ofReal_sum]
  have hrange : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hrange, Finset.sum_insert (by simp)]
  simp only [Nat.not_prime_zero, false_and, ↓reduceIte, Complex.ofReal_zero, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- Unit-interval integration of `stepSum a t * φ' t` on `[k, k + 1]`. -/
private lemma intervalIntegral_stepSum_unit (a : ℕ → ℂ) (k : ℕ) {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ), HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), Stage3RealAnalyticLandau.stepSum a t * φ' t =
      Stage3RealAnalyticLandau.stepSum a (k : ℝ) * (φ ((k + 1 : ℕ) : ℝ) - φ (k : ℝ)) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ) →
      Stage3RealAnalyticLandau.stepSum a t * φ' t =
        Stage3RealAnalyticLandau.stepSum a (k : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
    rw [Stage3RealAnalyticLandau.stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne)]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]

/-- Unit-interval integrability of `stepSum a t * φ' t` on `[k, k + 1]`. -/
private lemma intervalIntegrable_stepSum_mul_unit (a : ℕ → ℂ) (k : ℕ) {φ' : ℝ → ℂ}
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    IntervalIntegrable (fun t => Stage3RealAnalyticLandau.stepSum a t * φ' t) volume
      (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hconst : IntervalIntegrable (fun t => Stage3RealAnalyticLandau.stepSum a (k : ℝ) * φ' t)
      volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    hc.intervalIntegrable.const_mul _
  refine hconst.congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hne] with t hne ht
  rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
  rw [Stage3RealAnalyticLandau.stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne)]

/-- **Exact Abelian Summation Identity for `π(x; q, a)`**:
for every `q a : ℕ` and every `x ≥ 2`:
`(primeCountAP q a x : ℝ) = chebyshevThetaAP q a x / Real.log x + ∫ t in (2 : ℝ)..x, chebyshevThetaAP q a t / (t * (Real.log t) ^ 2)`. -/
theorem primeCountAP_eq_abel_thetaAP (q a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    (Stage2DirichletAP.primeCountAP q a x : ℝ) =
      Stage2DirichletAP.chebyshevThetaAP q a x / Real.log x +
        ∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a t / (t * (Real.log t) ^ 2) := by
  set f : ℕ → ℂ := fun n => if n.Prime ∧ n ≡ a [MOD q] then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0
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
      IntervalIntegrable (fun t => Stage3RealAnalyticLandau.stepSum f t * φ' t) volume (2 : ℝ) (N : ℝ) ∧
      ∑ n ∈ Finset.Icc 2 N, f n * φ (n : ℝ) =
        Stage3RealAnalyticLandau.stepSum f (N : ℝ) * φ (N : ℝ) -
          ∫ t in (2 : ℝ)..(N : ℝ), Stage3RealAnalyticLandau.stepSum f t * φ' t := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      intro _
      refine ⟨IntervalIntegrable.refl, ?_⟩
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_ofNat, intervalIntegral.integral_same,
        sub_zero]
      have hf2 : Stage3RealAnalyticLandau.stepSum f 2 = f 2 := by
        unfold Stage3RealAnalyticLandau.stepSum
        rw [Nat.floor_ofNat]
        have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
        rw [hIcc, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
        have h1 : f 1 = 0 := by simp [f, Nat.not_prime_one]
        rw [h1, zero_add]
      rw [hf2]
    | succ m hm ih =>
      intro hm1
      have hm_le : (m : ℝ) ≤ x := le_trans (by push_cast; linarith) hm1
      obtain ⟨hint_m, heq_m⟩ := ih hm_le
      have hsub_u : Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Set.Icc (2 : ℝ) x := by
        rw [Set.uIcc_of_le (by push_cast; linarith)]
        intro t ht
        have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        exact ⟨le_trans hm2R ht.1, le_trans ht.2 hm1⟩
      have hint_step := intervalIntegrable_stepSum_mul_unit f m (hc.mono hsub_u)
      have hval_step := intervalIntegral_stepSum_unit f m
        (fun t ht => hd t (hsub_u ht)) (hc.mono hsub_u)
      refine ⟨hint_m.trans hint_step, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_m hint_step, hval_step]
      have hIcc2 : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hIcc1 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hstep_succ : Stage3RealAnalyticLandau.stepSum f ((m + 1 : ℕ) : ℝ) =
          Stage3RealAnalyticLandau.stepSum f (m : ℝ) + f (m + 1) := by
        unfold Stage3RealAnalyticLandau.stepSum
        rw [Nat.floor_natCast, Nat.floor_natCast, hIcc1, Finset.sum_insert (by simp)]
        ring
      rw [hIcc2, Finset.sum_insert (by simp), heq_m, hstep_succ]
      ring
  obtain ⟨hint_N, heq_N⟩ := hint_nat ⌊x⌋₊ hN2 hfl_le
  have hsub_tail : Set.uIcc (⌊x⌋₊ : ℝ) x ⊆ Set.Icc (2 : ℝ) x := by
    rw [Set.uIcc_of_le hfl_le]
    intro t ht
    exact ⟨le_trans (by exact_mod_cast hN2) ht.1, ht.2⟩
  have htail_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (⌊x⌋₊ : ℝ) x →
      Stage3RealAnalyticLandau.stepSum f t * φ' t =
        Stage3RealAnalyticLandau.stepSum f (⌊x⌋₊ : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ x := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hfl_le, Set.mem_Ioc] at ht
    have hlt : t < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := lt_trans (lt_of_le_of_ne ht.2 hne) (by
      push_cast; exact Nat.lt_floor_add_one x)
    rw [Stage3RealAnalyticLandau.stepSum_const_on_Ico f ⌊x⌋₊ ht.1.le hlt]
  have hint_tail :
      IntervalIntegrable (fun t => Stage3RealAnalyticLandau.stepSum f t * φ' t) volume (⌊x⌋₊ : ℝ) x := by
    refine ((hc.mono hsub_tail).intervalIntegrable.const_mul
      (Stage3RealAnalyticLandau.stepSum f (⌊x⌋₊ : ℝ))).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [htail_ae] with t ht hmem using (ht hmem).symm
  have hval_tail : ∫ t in (⌊x⌋₊ : ℝ)..x, Stage3RealAnalyticLandau.stepSum f t * φ' t =
      Stage3RealAnalyticLandau.stepSum f (⌊x⌋₊ : ℝ) * (φ x - φ (⌊x⌋₊ : ℝ)) := by
    rw [intervalIntegral.integral_congr_ae htail_ae, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub_tail ht))
        (hc.mono hsub_tail).intervalIntegrable]
  have hstep_x : Stage3RealAnalyticLandau.stepSum f x = Stage3RealAnalyticLandau.stepSum f (⌊x⌋₊ : ℝ) := by
    unfold Stage3RealAnalyticLandau.stepSum; rw [Nat.floor_natCast]
  have hab : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, f n * φ (n : ℝ) =
      Stage3RealAnalyticLandau.stepSum f x * φ x -
        ∫ t in (2 : ℝ)..x, Stage3RealAnalyticLandau.stepSum f t * φ' t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_N hint_tail, hval_tail, heq_N, hstep_x]
    ring
  have hLHS : (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, f n * φ (n : ℝ)).re = (Stage2DirichletAP.primeCountAP q a x : ℝ) := by
    have hsum_eq : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, f n * φ (n : ℝ) =
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n.Prime ∧ n ≡ a [MOD q] then (1 : ℂ) else 0 := by
      have hrange : Finset.range (⌊x⌋₊ + 1) = insert 0 (insert 1 (Finset.Icc 2 ⌊x⌋₊)) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hrange, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      simp only [Nat.not_prime_zero, Nat.not_prime_one, false_and, ↓reduceIte, zero_add]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hlogn : Real.log (n : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
      simp only [f, φ]
      split_ifs
      · rw [← Complex.ofReal_mul, mul_inv_cancel₀ hlogn, Complex.ofReal_one]
      · simp
    rw [hsum_eq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp [Stage2DirichletAP.primeCountAP]
  have hRHS : (Stage3RealAnalyticLandau.stepSum f x * φ x -
        ∫ t in (2 : ℝ)..x, Stage3RealAnalyticLandau.stepSum f t * φ' t).re =
      Stage2DirichletAP.chebyshevThetaAP q a x / Real.log x +
        ∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a t / (t * (Real.log t) ^ 2) := by
    have h1 : Stage3RealAnalyticLandau.stepSum f x * φ x =
        ((Stage2DirichletAP.chebyshevThetaAP q a x / Real.log x : ℝ) : ℂ) := by
      rw [stepSum_primeLogAP_eq_thetaAP]
      simp only [φ, ← Complex.ofReal_mul, div_eq_mul_inv]
    have h2 : (fun t : ℝ => Stage3RealAnalyticLandau.stepSum f t * φ' t) =
        fun t : ℝ => (((-(Stage2DirichletAP.chebyshevThetaAP q a t / (t * (Real.log t) ^ 2)) : ℝ) : ℂ)) := by
      funext t
      rw [stepSum_primeLogAP_eq_thetaAP]
      simp only [φ', ← Complex.ofReal_mul]
      congr 1; ring
    rw [h1, h2, intervalIntegral.integral_ofReal, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_re, intervalIntegral.integral_neg, sub_neg_eq_add]
  have hre := congrArg Complex.re hab
  rw [hLHS, hRHS] at hre
  exact hre

/-- **Exact FTC Integration-by-Parts Identity for the Logarithmic Integral `li(x)`**:
for all `x ≥ 2`,
`∫ t in (2 : ℝ)..x, 1 / Real.log t = x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2`. -/
theorem integral_inv_log_eq {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.log t =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 := by
  have hcont1 : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
    · intro t ht; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact (Real.log_pos (by linarith [ht.1])).ne'
  have hcont2 : ContinuousOn (fun t : ℝ => 1 / (Real.log t) ^ 2) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => u / Real.log u)
        (1 / Real.log t - 1 / (Real.log t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hd := (hasDerivAt_id' t).fun_div (Real.hasDerivAt_log ht0.ne') hlt0.ne'
    refine hd.congr_deriv ?_
    field_simp [ht0.ne', hlt0.ne']
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont1.sub hcont2).intervalIntegrable
  rw [intervalIntegral.integral_sub hcont1.intervalIntegrable hcont2.intervalIntegrable] at hftc
  linarith

/-- Helper: `chebyshevThetaAP q a` is measurable (factors through `Nat.floor`). -/
private lemma measurable_chebyshevThetaAP (q a : ℕ) :
    Measurable (Stage2DirichletAP.chebyshevThetaAP q a) := by
  have h : Stage2DirichletAP.chebyshevThetaAP q a =
      (fun k : ℕ => ∑ n ∈ Finset.range (k + 1),
        if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

/-- **UNCONDITIONAL FULL SIEGEL–WALFISZ THEOREM (1936) FOR `π(x; q, a)` (REAL ARGUMENT, `0` EXCEPTIONS!)**:
there exists an ABSOLUTE constant `c > 0` such that for EVERY `A > 0`, there exists `C > 0` such
that for ALL `x ≥ 4`, ALL `q ≤ (Real.log x) ^ A` (`[NeZero q]`), and ALL `a` with `Nat.Coprime a q`:
`|(primeCountAP q a x : ℝ) - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ)| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem siegel_walfisz_pi_real :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ a : ℕ, Nat.Coprime a q →
                |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
                    (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ)| ≤
                  C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c_θ, hc_θ, hth_all⟩ := siegel_walfisz_theta
  set c : ℝ := min (c_θ / 2) (1 / 4) with hc_def
  have hc_pos : 0 < c := lt_min (by positivity) (by norm_num)
  have hc_le_half_θ : c ≤ c_θ / 2 := min_le_left _ _
  have hc_le_qtr : c ≤ 1 / 4 := min_le_right _ _
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c, hc_pos, fun A hA => ?_⟩
  obtain ⟨C_A, hCA, hthA⟩ := hth_all A hA
  obtain ⟨C_A1, hCA1, hthA1⟩ := hth_all (A + 1) (by linarith)
  set X_A : ℝ := max 16 (Real.exp (2 * (2 : ℝ) ^ A)) with hXA_def
  have hXA_ge16 : 16 ≤ X_A := le_max_left _ _
  set K_large : ℝ :=
    C_A / Real.log 2 + 8 / Real.log 2 + 28 / (Real.log 2) ^ 2 + C_A1 / (Real.log 2) ^ 2
  have hK_large_pos : 0 < K_large := by positivity
  set C_small : ℝ := (2 + 1 / Real.log 2) * Real.exp (c * Real.sqrt (Real.log X_A))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨C_fin, hC_fin_pos, fun x hx4 q _ hq a hcop => ?_⟩
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by linarith
  by_cases hge : X_A ≤ x
  · -- Large `x ≥ X_A`: exact Abel summation + split integral at `√x`!
    have hx16 : 16 ≤ x := hXA_ge16.trans hge
    have hsq_ge4 : 4 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith : (4 : ℝ) ^ 2 ≤ x)
    have hsq_ge2 : 2 ≤ Real.sqrt x := by linarith
    have hsq_le : Real.sqrt x ≤ x := by
      have : x ≤ x ^ 2 := by nlinarith
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hx0.le)
    have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hLx_ge_2A : 2 * (2 : ℝ) ^ A ≤ Real.log x := by
      have hexp : Real.exp (2 * (2 : ℝ) ^ A) ≤ x := (le_max_right _ _).trans hge
      exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hexp)
    -- Integrability of `(θ(t; q, a) - t / φ(q)) / (t (log t)^2)` and `1 / (log t)^2` on subintervals `[u, v] ⊆ [2, x]`
    have hint_inv2 : ∀ u v : ℝ, 2 ≤ u → u ≤ v →
        IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ 2) volume u v := by
      intro u v hu huv
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le huv]
      refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2) ?_
      · intro t ht; exact ne_of_gt (by linarith [hu, ht.1])
      · intro t ht; exact pow_ne_zero 2 (Real.log_pos (by linarith [hu, ht.1])).ne'
    have hth_triv : ∀ t : ℝ, 2 ≤ t →
        |Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)| ≤ 7 * t := by
      intro t ht2
      have h1 : Stage2DirichletAP.chebyshevThetaAP q a t ≤ 6 * t := by
        have ha1 := Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a t
        have ha2 : Stage2DirichletAP.chebyshevPsiAP q a t ≤ RHDirect.chebyshevPsi t := by
          unfold Stage2DirichletAP.chebyshevPsiAP RHDirect.chebyshevPsi
          refine Finset.sum_le_sum fun n _ => ?_
          split_ifs
          · exact le_rfl
          · exact ArithmeticFunction.vonMangoldt_nonneg
        exact (ha1.trans ha2).trans (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith))
      have h2 : 0 ≤ Stage2DirichletAP.chebyshevThetaAP q a t :=
        Stage2DirichletAP.chebyshevThetaAP_nonneg q a t
      have h3 : t / (q.totient : ℝ) ≤ t := by
        calc t / (q.totient : ℝ) ≤ t / 1 := div_le_div_of_nonneg_left (by linarith) zero_lt_one hphi_ge1
          _ = t := div_one t
      have h4 : 0 ≤ t / (q.totient : ℝ) := div_nonneg (by linarith) hphi_pos.le
      rw [abs_le]; constructor <;> linarith
    have hint_err : ∀ u v : ℝ, 2 ≤ u → u ≤ v →
        IntervalIntegrable
          (fun t : ℝ => (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
            (t * (Real.log t) ^ 2)) volume u v := by
      intro u v hu huv
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr ?_
      refine Integrable.mono'
        (integrableOn_const (C := 7 / (Real.log 2) ^ 2) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
      · exact (((measurable_chebyshevThetaAP q a).sub (measurable_id.div_const _)).div
          (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
        have ht2 : 2 ≤ t := hu.trans ht.1.le
        have ht0 : 0 < t := by linarith
        have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
        have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlt_pos))]
        calc |Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)| / (t * (Real.log t) ^ 2)
            ≤ (7 * t) / (t * (Real.log 2) ^ 2) := by
              refine div_le_div₀ (by positivity) (hth_triv t ht2) (by positivity) ?_
              gcongr
          _ = 7 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']
    -- Exact decomposition of `π(x; q, a) - li(x) / φ(q)`
    have hsplit_int :
        ∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a t / (t * (Real.log t) ^ 2) =
          (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) / (q.totient : ℝ) +
          ∫ t in (2 : ℝ)..x,
            (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
              (t * (Real.log t) ^ 2) := by
      have hconst : (∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2) / (q.totient : ℝ) =
          ∫ t in (2 : ℝ)..x, (1 / (q.totient : ℝ)) * (1 / (Real.log t) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]; ring
      rw [hconst, ← intervalIntegral.integral_add ((hint_inv2 2 x le_rfl hx2).const_mul _)
        (hint_err 2 x le_rfl hx2)]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx2] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hlt0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      field_simp [ht0.ne', hlt0.ne', hphi_pos.ne']
      ring
    have hdecomp :
        (Stage2DirichletAP.primeCountAP q a x : ℝ) -
            (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ) =
          (Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x +
            (2 / Real.log 2) / (q.totient : ℝ) +
            (∫ t in (2 : ℝ)..(Real.sqrt x),
              (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
                (t * (Real.log t) ^ 2)) +
            (∫ t in (Real.sqrt x)..x,
              (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
                (t * (Real.log t) ^ 2)) := by
      rw [primeCountAP_eq_abel_thetaAP q a hx2, integral_inv_log_eq hx2, hsplit_int,
        ← intervalIntegral.integral_add_adjacent_intervals
          (hint_err 2 (Real.sqrt x) le_rfl hsq_ge2)
          (hint_err (Real.sqrt x) x hsq_ge2 hsq_le)]
      ring
    rw [hdecomp]
    -- Helper: `√x ≤ 4 * x * exp(-c √(log x))`
    have hsqrt_le_exp : Real.sqrt x ≤ 4 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      have hLx_ge1 : 1 ≤ Real.log x := by
        have : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
        exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) this)
      calc Real.sqrt x ≤ Real.sqrt x * Real.log x := by nlinarith [Real.sqrt_nonneg x]
        _ ≤ 4 * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
            sqrt_mul_log_le_4_mul_x_exp_neg_sqrt hc_le_qtr hx4
    -- Piece 1: boundary term `(θ(x; q, a) - x / φ(q)) / log x`
    have hb1 : |(Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x| ≤
        (C_A / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      rw [abs_div, abs_of_pos hLx_pos]
      have hLx_ge : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
      have h1 := hthA x hx4 q hq a hcop
      have hexp : Real.exp (-c_θ * Real.sqrt (Real.log x)) ≤
          Real.exp (-c * Real.sqrt (Real.log x)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg (Real.log x)])
      calc |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| / Real.log x
          ≤ (C_A * x * Real.exp (-c * Real.sqrt (Real.log x))) / Real.log 2 :=
            div_le_div₀ (by positivity) (h1.trans (by gcongr)) hlog2_pos hLx_ge
        _ = (C_A / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring
    -- Piece 2: constant term `(2 / log 2) / φ(q)`
    have hb2 : |(2 / Real.log 2) / (q.totient : ℝ)| ≤
        (8 / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      rw [abs_of_pos (by positivity)]
      calc (2 / Real.log 2) / (q.totient : ℝ)
          ≤ (2 / Real.log 2) / 1 := div_le_div_of_nonneg_left (by positivity) zero_lt_one hphi_ge1
        _ = 2 / Real.log 2 := div_one _
        _ ≤ (2 / Real.log 2) * Real.sqrt x := by nlinarith [hsq_ge2, div_pos (by norm_num : (0 : ℝ) < 2) hlog2_pos]
        _ ≤ (2 / Real.log 2) * (4 * x * Real.exp (-c * Real.sqrt (Real.log x))) :=
            mul_le_mul_of_nonneg_left hsqrt_le_exp (by positivity)
        _ = (8 / Real.log 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring
    -- Piece 3: low integral `[2, √x]`
    have hb3 : |∫ t in (2 : ℝ)..(Real.sqrt x),
          (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
            (t * (Real.log t) ^ 2)| ≤
        (28 / (Real.log 2) ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      have hnorm : |∫ t in (2 : ℝ)..(Real.sqrt x),
            (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
              (t * (Real.log t) ^ 2)| ≤
          (7 / (Real.log 2) ^ 2) * |Real.sqrt x - 2| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_of_norm_le_const
            (f := fun t : ℝ =>
              (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
                (t * (Real.log t) ^ 2))
            (C := 7 / (Real.log 2) ^ 2)
            fun t ht => by
              rw [Set.uIoc_of_le hsq_ge2] at ht
              have ht2 : 2 ≤ t := ht.1.le
              have ht0 : 0 < t := by linarith
              have hlt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
              have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge
              rw [Real.norm_eq_abs, abs_div,
                abs_of_pos (a := t * (Real.log t) ^ 2) (mul_pos ht0 (sq_pos_of_pos hlt_pos))]
              calc |Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)| /
                      (t * (Real.log t) ^ 2)
                  ≤ (7 * t) / (t * (Real.log 2) ^ 2) := by
                    refine div_le_div₀ (by positivity) (hth_triv t ht2) (by positivity) ?_
                    gcongr
                _ = 7 / (Real.log 2) ^ 2 := by field_simp [ht0.ne']
      rw [abs_of_nonneg (sub_nonneg.mpr hsq_ge2)] at hnorm
      calc |∫ t in (2 : ℝ)..(Real.sqrt x),
              (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
                (t * (Real.log t) ^ 2)|
          ≤ (7 / (Real.log 2) ^ 2) * (Real.sqrt x - 2) := hnorm
        _ ≤ (7 / (Real.log 2) ^ 2) * Real.sqrt x :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ (7 / (Real.log 2) ^ 2) * (4 * x * Real.exp (-c * Real.sqrt (Real.log x))) :=
            mul_le_mul_of_nonneg_left hsqrt_le_exp (by positivity)
        _ = (28 / (Real.log 2) ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring
    -- Piece 4: high integral `[√x, x]` via `siegel_walfisz_theta` at exponent `A + 1`!
    have hb4 : |∫ t in (Real.sqrt x)..x,
          (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
            (t * (Real.log t) ^ 2)| ≤
        (C_A1 / (Real.log 2) ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      have hnorm : |∫ t in (Real.sqrt x)..x,
            (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
              (t * (Real.log t) ^ 2)| ≤
          ((C_A1 / (Real.log 2) ^ 2) * Real.exp (-c * Real.sqrt (Real.log x))) * |x - Real.sqrt x| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_of_norm_le_const
            (f := fun t : ℝ =>
              (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
                (t * (Real.log t) ^ 2))
            (C := (C_A1 / (Real.log 2) ^ 2) * Real.exp (-c * Real.sqrt (Real.log x)))
            fun t ht => by
              rw [Set.uIoc_of_le hsq_le] at ht
              have ht4 : 4 ≤ t := hsq_ge4.trans ht.1.le
              have ht0 : 0 < t := by linarith
              have hlt_ge_half : Real.log x / 2 ≤ Real.log t := by
                have h := Real.log_le_log (by linarith) ht.1.le
                rwa [Real.log_sqrt hx0.le] at h
              have hlt_ge2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
              have hlt_pos : 0 < Real.log t := hlog2_pos.trans_le hlt_ge2
              have h2A_le_lt : (2 : ℝ) ^ A ≤ Real.log t := by linarith
              have hq_t : (q : ℝ) ≤ (Real.log t) ^ (A + 1) := by
                calc (q : ℝ) ≤ (Real.log x) ^ A := hq
                  _ = (2 * (Real.log x / 2)) ^ A := by congr 1; ring
                  _ = (2 : ℝ) ^ A * (Real.log x / 2) ^ A :=
                      Real.mul_rpow (by norm_num) (by positivity)
                  _ ≤ Real.log t * (Real.log t) ^ A :=
                      mul_le_mul h2A_le_lt (Real.rpow_le_rpow (by positivity) hlt_ge_half hA.le)
                        (Real.rpow_nonneg (by positivity) A) hlt_pos.le
                  _ = (Real.log t) ^ (A + 1) := by
                      rw [Real.rpow_add hlt_pos, Real.rpow_one, mul_comm]
              have hsqrt_t : Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log t) := by
                refine Real.le_sqrt_of_sq_le ?_
                rw [div_pow, Real.sq_sqrt hLx_pos.le]; norm_num; linarith
              have hexp_t : Real.exp (-c_θ * Real.sqrt (Real.log t)) ≤
                  Real.exp (-c * Real.sqrt (Real.log x)) :=
                Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg (Real.log x)])
              have hth_t := hthA1 t ht4 q hq_t a hcop
              rw [Real.norm_eq_abs, abs_div,
                abs_of_pos (a := t * (Real.log t) ^ 2) (mul_pos ht0 (sq_pos_of_pos hlt_pos))]
              calc |Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)| /
                      (t * (Real.log t) ^ 2)
                  ≤ (C_A1 * t * Real.exp (-c * Real.sqrt (Real.log x))) / (t * (Real.log 2) ^ 2) := by
                    refine div_le_div₀ (by positivity) (hth_t.trans (by gcongr)) (by positivity) ?_
                    gcongr
                _ = (C_A1 / (Real.log 2) ^ 2) * Real.exp (-c * Real.sqrt (Real.log x)) := by
                    field_simp [ht0.ne']
      rw [abs_of_nonneg (sub_nonneg.mpr hsq_le)] at hnorm
      calc |∫ t in (Real.sqrt x)..x,
              (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) /
                (t * (Real.log t) ^ 2)|
          ≤ ((C_A1 / (Real.log 2) ^ 2) * Real.exp (-c * Real.sqrt (Real.log x))) * (x - Real.sqrt x) := hnorm
        _ ≤ ((C_A1 / (Real.log 2) ^ 2) * Real.exp (-c * Real.sqrt (Real.log x))) * x :=
            mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg x]) (by positivity)
        _ = (C_A1 / (Real.log 2) ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring
    -- Combine all four pieces
    have htri1 := abs_add_le
      ((Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x +
        (2 / Real.log 2) / (q.totient : ℝ) +
        (∫ t in (2 : ℝ)..(Real.sqrt x),
          (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) / (t * (Real.log t) ^ 2)))
      (∫ t in (Real.sqrt x)..x,
        (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) / (t * (Real.log t) ^ 2))
    have htri2 := abs_add_le
      ((Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x +
        (2 / Real.log 2) / (q.totient : ℝ))
      (∫ t in (2 : ℝ)..(Real.sqrt x),
        (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) / (t * (Real.log t) ^ 2))
    have htri3 := abs_add_le
      ((Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x)
      ((2 / Real.log 2) / (q.totient : ℝ))
    have hsum_le :
        |(Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / Real.log x +
          (2 / Real.log 2) / (q.totient : ℝ) +
          (∫ t in (2 : ℝ)..(Real.sqrt x),
            (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) / (t * (Real.log t) ^ 2)) +
          (∫ t in (Real.sqrt x)..x,
            (Stage2DirichletAP.chebyshevThetaAP q a t - t / (q.totient : ℝ)) / (t * (Real.log t) ^ 2))| ≤
          K_large * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      dsimp only [K_large]; linarith
    exact hsum_le.trans (by gcongr; exact le_max_left _ _)
  · -- Small `4 ≤ x < X_A`: trivial bound `|π(x; q, a) - li(x) / φ(q)| ≤ (2 + 1 / log 2) * x`
    push Not at hge
    have hpi_le : (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤ 2 * x := by
      have hcard : Stage2DirichletAP.primeCountAP q a x ≤ ⌊x⌋₊ + 1 := by
        unfold Stage2DirichletAP.primeCountAP
        exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
      have hcardR : (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
      linarith [Nat.floor_le (by linarith : 0 ≤ x)]
    have hpi_nn : (0 : ℝ) ≤ (Stage2DirichletAP.primeCountAP q a x : ℝ) := Nat.cast_nonneg _
    have hli_nn : 0 ≤ ∫ t in (2 : ℝ)..x, 1 / Real.log t :=
      intervalIntegral.integral_nonneg hx2 fun t ht =>
        div_nonneg zero_le_one (Real.log_nonneg (by linarith [ht.1]))
    have hli_le : ∫ t in (2 : ℝ)..x, 1 / Real.log t ≤ (1 / Real.log 2) * x := by
      have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc 2 x) := by
        rw [Set.uIcc_of_le hx2]
        refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
        · intro t ht; exact ne_of_gt (by linarith [ht.1])
        · intro t ht; exact (Real.log_pos (by linarith [ht.1])).ne'
      have h1 : ∫ t in (2 : ℝ)..x, 1 / Real.log t ≤ ∫ _t in (2 : ℝ)..x, 1 / Real.log 2 := by
        refine intervalIntegral.integral_mono_on hx2 hcont.intervalIntegrable intervalIntegrable_const
          fun t ht => one_div_le_one_div_of_le hlog2_pos (Real.log_le_log (by norm_num) ht.1)
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      calc ∫ t in (2 : ℝ)..x, 1 / Real.log t ≤ (x - 2) * (1 / Real.log 2) := h1
        _ ≤ x * (1 / Real.log 2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (1 / Real.log 2) * x := by ring
    have hli_div_le : (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ) ≤ (1 / Real.log 2) * x := by
      calc (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ)
          ≤ (∫ t in (2 : ℝ)..x, 1 / Real.log t) / 1 :=
            div_le_div_of_nonneg_left hli_nn zero_lt_one hphi_ge1
        _ = ∫ t in (2 : ℝ)..x, 1 / Real.log t := div_one _
        _ ≤ (1 / Real.log 2) * x := hli_le
    have hli_div_nn : 0 ≤ (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ) :=
      div_nonneg hli_nn hphi_pos.le
    have habs : |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
          (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ)| ≤ (2 + 1 / Real.log 2) * x := by
      rw [abs_le]; constructor <;> linarith
    have hexp_ge :
        Real.exp (-c * Real.sqrt (Real.log X_A)) ≤ Real.exp (-c * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log x ≤ Real.log X_A := Real.log_le_log hx0 hge.le
      nlinarith [Real.sqrt_le_sqrt hlog]
    have hcancel : C_small * Real.exp (-c * Real.sqrt (Real.log X_A)) = 2 + 1 / Real.log 2 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : c * Real.sqrt (Real.log X_A) + -c * Real.sqrt (Real.log X_A) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc |(Stage2DirichletAP.primeCountAP q a x : ℝ) -
            (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ)|
        ≤ (2 + 1 / Real.log 2) * x := habs
      _ = C_small * x * Real.exp (-c * Real.sqrt (Real.log X_A)) := by rw [← hcancel]; ring
      _ ≤ C_small * x * Real.exp (-c * Real.sqrt (Real.log x)) := by gcongr
      _ ≤ C_fin * x * Real.exp (-c * Real.sqrt (Real.log x)) := by gcongr; exact le_max_right _ _

/-- **UNCONDITIONAL FULL SIEGEL–WALFISZ THEOREM (1936) FOR `π(x; q, a)` (`⌊x⌋₊` FORM, `0` EXCEPTIONS!)**:
there exists an ABSOLUTE constant `c > 0` such that for EVERY `A > 0`, there exists `C > 0` such
that for ALL `x ≥ 4`, ALL `q ≤ (Real.log x) ^ A` (`[NeZero q]`), and ALL `a` with `Nat.Coprime a q`:
`|(primeCountAP q a ⌊x⌋₊ : ℝ) - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ)| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem siegel_walfisz_pi :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ a : ℕ, Nat.Coprime a q →
                |(Stage2DirichletAP.primeCountAP q a ⌊x⌋₊ : ℝ) -
                    (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ)| ≤
                  C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hpi⟩ := siegel_walfisz_pi_real
  refine ⟨c, hc, fun A hA => ?_⟩
  obtain ⟨C, hC, hbd⟩ := hpi A hA
  refine ⟨C, hC, fun x hx4 q _ hq a hcop => ?_⟩
  have heq : Stage2DirichletAP.primeCountAP q a (⌊x⌋₊ : ℝ) = Stage2DirichletAP.primeCountAP q a x := by
    simp [Stage2DirichletAP.primeCountAP]
  rw [heq]
  exact hbd x hx4 q hq a hcop

/-! ## Section 4: Unconditional Zero-Exception Uniform Short-Interval Primes in AP & Master Packaging -/

/-- If `chebyshevThetaAP q a x < chebyshevThetaAP q a y` for `0 ≤ x ≤ y`, there is a prime
`p ≡ a [MOD q]` in `(x, y]`. -/
private lemma exists_prime_in_AP_Ioc_of_thetaAP_lt (q a : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hlt : Stage2DirichletAP.chebyshevThetaAP q a x < Stage2DirichletAP.chebyshevThetaAP q a y) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  by_contra hno
  push Not at hno
  set Sx : Finset ℕ := (Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ a [MOD q]
  set Sy : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ a [MOD q]
  have hsub : Sy ⊆ Sx := by
    intro p hp
    simp only [Sx, Sy, Finset.mem_filter, Finset.mem_range] at hp ⊢
    refine ⟨?_, hp.2⟩
    have hpy : (p : ℝ) ≤ y := le_trans (by exact_mod_cast (by omega : p ≤ ⌊y⌋₊)) (Nat.floor_le (by linarith))
    have hpx : (p : ℝ) ≤ x := by
      by_contra hgt; push Not at hgt
      exact (not_le_of_gt (hno p hp.2.1 hp.2.2 hgt)) hpy
    have hle : p ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx).mpr hpx
    omega
  have hsub' : Sx ⊆ Sy := Finset.filter_subset_filter _
    (Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hxy) 1))
  have heq : Stage2DirichletAP.chebyshevThetaAP q a x = Stage2DirichletAP.chebyshevThetaAP q a y := by
    unfold Stage2DirichletAP.chebyshevThetaAP
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    exact Finset.Subset.antisymm hsub' hsub
  linarith

/-- Helper: `(Real.log x) ^ A * Real.exp (-c * Real.sqrt (Real.log x)) → 0` as `x → ∞`. -/
private lemma tendsto_log_rpow_mul_exp_neg_sqrt_log {c A : ℝ} (hc : 0 < c) (hA : 0 < A) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A * Real.exp (-c * Real.sqrt (Real.log x)))
      atTop (𝓝 0) := by
  have hratio : Tendsto (fun u : ℝ => Real.log u / Real.sqrt u) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    exact h.congr fun u => by rw [Real.sqrt_eq_rpow]
  have hcomp : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.sqrt (Real.log x)) atTop (𝓝 0) :=
    hratio.comp Real.tendsto_log_atTop
  have hev := hcomp.eventually (Iio_mem_nhds (div_pos (half_pos hc) hA))
  have hdecay : Tendsto (fun x : ℝ => Real.exp (-(c / 2) * Real.sqrt (Real.log x))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (c / 2) * Real.sqrt (Real.log x)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity)
        (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp Real.tendsto_log_atTop).congr
          fun x => (Real.sqrt_eq_rpow (Real.log x)).symm)
    exact (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).congr fun x => by
      dsimp only [Function.comp_apply]; congr 1; ring
  refine squeeze_zero_norm' (a := fun x : ℝ => Real.exp (-(c / 2) * Real.sqrt (Real.log x))) ?_ hdecay
  filter_upwards [hev, eventually_gt_atTop (Real.exp 1)] with x hx hx_e
  have hLx_gt1 : 1 < Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hx_e
  have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
  have hsq_pos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLx_pos
  have hlt : A * Real.log (Real.log x) < (c / 2) * Real.sqrt (Real.log x) := by
    have h1 := (div_lt_iff₀ hsq_pos).mp hx
    have h2 := mul_lt_mul_of_pos_left h1 hA
    have h3 : A * (c / 2 / A * Real.sqrt (Real.log x)) = (c / 2) * Real.sqrt (Real.log x) := by
      field_simp [hA.ne']
    linarith
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hLx_pos.le A) (Real.exp_pos _).le),
    Real.rpow_def_of_pos hLx_pos, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **UNCONDITIONAL ZERO-EXCEPTION UNIFORM SHORT-INTERVAL PRIMES IN ARITHMETIC PROGRESSIONS**:
there exists an ABSOLUTE constant `c > 0` such that for EVERY `A > 0`, there exists `X_A ≥ 4`
such that for ALL `x ≥ X_A`, EVERY modulus `1 ≤ q ≤ (Real.log x) ^ A` (`[NeZero q]`, NO
EXCEPTIONS!), and EVERY `a` with `Nat.Coprime a q`, there exists a prime `p ≡ a [MOD q]` in
`(x, x + x * Real.exp (-c * Real.sqrt (Real.log x))]`! -/
theorem exists_prime_in_AP_uniform_siegel_walfisz :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ X_A : ℝ, 4 ≤ X_A ∧
          ∀ x : ℝ, X_A ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ a : ℕ, Nat.Coprime a q →
                ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ x < (p : ℝ) ∧
                  (p : ℝ) ≤ x + x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c_θ, hc_θ, hth_all⟩ := siegel_walfisz_theta
  set c : ℝ := c_θ / 2 with hc_def
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, fun A hA => ?_⟩
  obtain ⟨C, hC, hth⟩ := hth_all A hA
  have hev := (tendsto_log_rpow_mul_exp_neg_sqrt_log hc_pos hA).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / (4 * C) by positivity))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨max 4 X₁, le_max_left _ _, fun x hx q _ hq a hcop => ?_⟩
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  set δ : ℝ := Real.exp (-c * Real.sqrt (Real.log x)) with hδ_def
  have hδ_pos : 0 < δ := Real.exp_pos _
  have hδ_le1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg (Real.log x)])
  have hδ_small : (Real.log x) ^ A * δ < 1 / (4 * C) := hX₁ x hx1
  set y : ℝ := x + x * δ with hy_def
  have hxy : x ≤ y := by nlinarith
  have hy4 : 4 ≤ y := by linarith
  have hy_le2x : y ≤ 2 * x := by nlinarith
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hq_y : (q : ℝ) ≤ (Real.log y) ^ A :=
    hq.trans (Real.rpow_le_rpow hLx_pos.le hlog_le hA.le)
  have hE_x : Real.exp (-c_θ * Real.sqrt (Real.log x)) = δ ^ 2 := by
    rw [hδ_def, ← Real.exp_nat_mul]; congr 1; push_cast; dsimp only [c]; ring
  have hE_y : Real.exp (-c_θ * Real.sqrt (Real.log y)) ≤ δ ^ 2 := by
    rw [← hE_x]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_le_sqrt hlog_le]
  have hth_x := (abs_le.mp (hth x hx4 q hq a hcop)).2
  have hth_y := (abs_le.mp (hth y hy4 q hq_y a hcop)).1
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hphi_le : (q.totient : ℝ) ≤ (Real.log x) ^ A :=
    (by exact_mod_cast Nat.totient_le q : (q.totient : ℝ) ≤ (q : ℝ)).trans hq
  have h3C_lt : 3 * C * δ < 1 / (q.totient : ℝ) := by
    have hmul : 4 * C * ((Real.log x) ^ A * δ) < 1 := by
      have := mul_lt_mul_of_pos_left hδ_small (show (0 : ℝ) < 4 * C by positivity)
      rwa [mul_one_div_cancel (by positivity : (4 * C) ≠ 0)] at this
    have hle1 : (q.totient : ℝ) * (3 * C * δ) < 1 := by
      have h1 : (q.totient : ℝ) * (3 * C * δ) ≤ (Real.log x) ^ A * (3 * C * δ) :=
        mul_le_mul_of_nonneg_right hphi_le (by positivity)
      have h2 : (Real.log x) ^ A * (3 * C * δ) < (Real.log x) ^ A * (4 * C * δ) := by
        have hpos : 0 < (Real.log x) ^ A * C * δ := by positivity
        linarith
      linarith
    rwa [lt_div_iff₀ hphi_pos, mul_comm]
  have hth_diff : Stage2DirichletAP.chebyshevThetaAP q a x < Stage2DirichletAP.chebyshevThetaAP q a y := by
    have h1 : C * y * Real.exp (-c_θ * Real.sqrt (Real.log y)) ≤ 2 * C * x * δ ^ 2 := by
      calc C * y * Real.exp (-c_θ * Real.sqrt (Real.log y))
          ≤ C * (2 * x) * δ ^ 2 := by gcongr
        _ = 2 * C * x * δ ^ 2 := by ring
    have h2 : C * x * Real.exp (-c_θ * Real.sqrt (Real.log x)) = C * x * δ ^ 2 := by rw [hE_x]
    have h3 : 3 * C * x * δ ^ 2 < (x * δ) / (q.totient : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left h3C_lt (show 0 < x * δ by positivity)
      have hlhs : x * δ * (3 * C * δ) = 3 * C * x * δ ^ 2 := by ring
      have hrhs : x * δ * (1 / (q.totient : ℝ)) = (x * δ) / (q.totient : ℝ) := by ring
      linarith
    have hmain : y / (q.totient : ℝ) - x / (q.totient : ℝ) = (x * δ) / (q.totient : ℝ) := by
      dsimp only [y]; ring
    linarith
  exact exists_prime_in_AP_Ioc_of_thetaAP_lt q a hx0.le hxy hth_diff

/-- **MASTER UNCONDITIONAL STAGE 10 SIEGEL–WALFISZ THEOREM (1936, `0` EXCEPTIONS, `0` ASSUMPTIONS!)**:
simultaneously packages:
1. Full zero-exception Siegel–Walfisz zero-free region across all `q ≤ Q`,
2. Full zero-exception uniform character-sum decay `‖ψ(x, χ)‖ ≤ C x exp(-c √(log x))`,
3. Full unconditional Siegel–Walfisz theorem for `ψ(x; q, a)`, `θ(x; q, a)`, and `π(x; q, a)` (with
   exact logarithmic integral `li(x) / φ(q)`),
4. Full zero-exception uniform short-interval prime existence in every coprime AP `q ≤ (log x)^A`! -/
theorem stage10_siegel_walfisz_master :
    (∀ A : ℝ, 0 < A →
      ∃ c_A : ℝ, 0 < c_A ∧
        ∀ Q : ℝ, 2 ≤ Q →
          ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q →
            ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
              ∀ s : ℂ,
                1 - min (c_A / Q ^ (1 / (2 * A))) (1 / (60000 * Real.log (Q * (|s.im| + 2)))) ≤ s.re →
                DirichletCharacter.LFunction χ s ≠ 0) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
                ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
                  C * x * Real.exp (-c * Real.sqrt (Real.log x))) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ a : ℕ, Nat.Coprime a q →
                |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
                  C * x * Real.exp (-c * Real.sqrt (Real.log x))) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ a : ℕ, Nat.Coprime a q →
                |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
                  C * x * Real.exp (-c * Real.sqrt (Real.log x))) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 4 ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ a : ℕ, Nat.Coprime a q →
                |(Stage2DirichletAP.primeCountAP q a ⌊x⌋₊ : ℝ) -
                    (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (q.totient : ℝ)| ≤
                  C * x * Real.exp (-c * Real.sqrt (Real.log x))) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 0 < A →
        ∃ X_A : ℝ, 4 ≤ X_A ∧
          ∀ x : ℝ, X_A ≤ x →
            ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x) ^ A →
              ∀ a : ℕ, Nat.Coprime a q →
                ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ x < (p : ℝ) ∧
                  (p : ℝ) ≤ x + x * Real.exp (-c * Real.sqrt (Real.log x))) :=
  ⟨fun _ hA => siegel_walfisz_zeroFree_region hA,
   siegel_walfisz_character_psi_uniform,
   siegel_walfisz_psi,
   siegel_walfisz_theta,
   siegel_walfisz_pi,
   exists_prime_in_AP_uniform_siegel_walfisz⟩

end RHDirect.Stage10SiegelWalfiszFull
