import RHDirect.Stage6EffectivePNT
import RHDirect.Stage5DirichletLZeroFree
import RHDirect.Stage5ZetaZeroFree
import RHDirect.Stage4ExplicitFormula
import RHDirect.Stage2DirichletAP

/-!
# RHDirect.Stage7PNTInAP

**UNCONDITIONAL EFFECTIVE PRIME NUMBER THEOREM IN ARITHMETIC PROGRESSIONS**
(0 assumptions, 0 `sorry`, 0 custom `axiom`s) directly on Mathlib's actual
`DirichletCharacter.LFunction`, `Stage2DirichletAP.chebyshevPsiAP`,
`Stage2DirichletAP.chebyshevThetaAP`, and `Stage2DirichletAP.primeCountAP`, in pure
Mathlib `v4.33.1`.

## Main Contents
1. **Unconditional Fixed-Modulus Zero-Free Region & Log-Derivative Bounds for Every Non-Principal `χ`**:
   - `LFunction_zeroFreeRegion_fixed_char`: combines `Stage5DirichletLZeroFree.LFunction_ne_zero_in_zeroFreeRegion`
     (for `|s.im| ≥ 1`) with compactness on `{1} × [-1, 1]` + `Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge`
     + the horizontal MVT bound `Stage5DirichletLZeroFree.norm_LFunction_sub_le_of_strip` to prove
     unconditionally for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY non-principal `χ ≠ 1`:
     `∃ c_χ > 0, ∀ s : ℂ, 1 - c_χ / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re → LFunction χ s ≠ 0`.
   - `negLogDerivL_zeroFree_bound_pow10` and `negLogDerivL_zeroFree_bound`: via
     `Stage5ZetaZeroFree.exists_holomorphic_log_ball`, `Stage5ZetaZeroFree.borelCaratheodory_deriv_le`,
     and `Stage5DirichletLZeroFree.norm_LFunction_le_of_stepSum_bound`, proves unconditionally:
     `∃ c' > 0, ∃ C' > 0, ∀ s : ℂ, 1 - c' / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re → s.re ≤ 2 → ‖-deriv (LFunction χ) s / LFunction χ s‖ ≤ C' * (Real.log (|s.im| + 2)) ^ 18`.
2. **Pole-Free Perron Contour Shift for Non-Principal `ψ₁(x, χ)` & Effective Character-Sum Decay**:
   - `perron_contour_shift_psi1Char`: exact rectangular Cauchy shift
     (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) of
     `Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T` to `Re(s) = σ` with ZERO poles inside.
   - `effective_psi1Char_bound`: optimizing `T = exp(α (log x)^{1/10})` yields
     `‖psi1Char χ x‖ ≤ C * x ^ 2 * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ))`.
   - `effective_chebyshevPsiChar_bound` & `chebyshevPsiChar_div_tendsto_zero`: complex finite-difference
     de-smoothing against `Stage6EffectivePNT.effective_pnt_chebyshevPsi` yields
     `‖chebyshevPsiChar χ x‖ ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))` and
     `chebyshevPsiChar χ x / x → 0`.
3. **Unconditional Effective Prime Number Theorem in Arithmetic Progressions (0 Assumptions!)**:
   For EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a` with `Nat.Coprime a q`:
   - `effective_pnt_psiAP`: `|ψ(x; q, a) - x / φ(q)| ≤ C * x * exp(-c * (log x)^{1/20})`.
   - `effective_pnt_thetaAP`: `|θ(x; q, a) - x / φ(q)| ≤ C * x * exp(-c * (log x)^{1/20})`.
   - `pnt_psiAP_asymp`, `pnt_thetaAP_asymp`, `pnt_primeCountAP_real_asymp`, and `pnt_primeCountAP_asymp`:
     `π(n; q, a) / (n / (φ(q) * log n)) → 1`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex DirichletCharacter MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage7PNTInAP

/-! ## Section 1: Fixed-Modulus Unconditional Zero-Free Region & Log-Derivative Bounds -/

/-- Elementary comparison `Real.log (q * (|t| + 2)) ≤ (2 * Real.log q + 1) * Real.log (|t| + 2)`
for `q ≥ 2` and all `t : ℝ`. -/
private lemma log_q_mul_le_const_mul_log {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    Real.log ((q : ℝ) * (|t| + 2)) ≤ (2 * Real.log (q : ℝ) + 1) * Real.log (|t| + 2) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have ht2_ge2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have ht2_pos : (0 : ℝ) < |t| + 2 := by linarith
  rw [Real.log_mul hq_pos.ne' ht2_pos.ne']
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_t_ge : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) :=
    hlog2_gt.le.trans (Real.log_le_log (by norm_num) ht2_ge2)
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  nlinarith

/-- **Unconditional Fixed-Modulus Zero-Free Region for EVERY Non-Principal Dirichlet Character**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`),
there exists `c_χ > 0` such that `LFunction χ s ≠ 0` whenever
`1 - c_χ / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re`. -/
theorem LFunction_zeroFreeRegion_fixed_char {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c_χ : ℝ, 0 < c_χ ∧
      ∀ s : ℂ, 1 - c_χ / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Part 1: Compactness on `{1} × [-1, 1]` + MVT gives a uniform strip `1 - δ_χ ≤ s.re` for `|s.im| ≤ 1`
  have hcont_seg : ContinuousOn (fun t : ℝ => ‖DirichletCharacter.LFunction χ (1 + I * (t : ℂ))‖)
      (Set.Icc (-1 : ℝ) 1) := by
    have hL_cont : Continuous (DirichletCharacter.LFunction χ) :=
      (DirichletCharacter.differentiable_LFunction hχ).continuous
    have hmap : Continuous (fun t : ℝ => (1 : ℂ) + I * (t : ℂ)) := by fun_prop
    exact (hL_cont.comp hmap).norm.continuousOn
  have hne_Icc : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, by norm_num, by norm_num⟩
  obtain ⟨t₀, ht₀_mem, ht₀_min⟩ := isCompact_Icc.exists_isMinOn hne_Icc hcont_seg
  set m : ℝ := ‖DirichletCharacter.LFunction χ (1 + I * (t₀ : ℂ))‖ with hm_def
  have hm_pos : 0 < m := by
    refine norm_pos_iff.mpr ?_
    exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (Or.inl hχ) (by simp)
  set L3q : ℝ := Real.log ((q : ℝ) * 3) with hL3q_def
  have hL3q_pos : 0 < L3q := Real.log_pos (by linarith)
  set δ_χ : ℝ := min L3q⁻¹ (m / (2 * (288 * L3q ^ 2))) with hδ_def
  have hδ_pos : 0 < δ_χ := lt_min (inv_pos.mpr hL3q_pos) (by positivity)
  have hδ_le_inv : δ_χ ≤ L3q⁻¹ := min_le_left _ _
  have hδ_le_m : δ_χ ≤ m / (2 * (288 * L3q ^ 2)) := min_le_right _ _
  -- Part 2: Combine with `Stage5DirichletLZeroFree.LFunction_ne_zero_in_zeroFreeRegion` for `|s.im| ≥ 1`
  set A_q : ℝ := 2 * Real.log (q : ℝ) + 1 with hAq_def
  have hAq_pos : 0 < A_q := by
    have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
    linarith
  set c_high : ℝ := Stage5DirichletLZeroFree.zeroFreeConst / A_q ^ 9 with hc_high_def
  have hc_high_pos : 0 < c_high :=
    div_pos Stage5DirichletLZeroFree.zeroFreeConst_pos (pow_pos hAq_pos 9)
  set c_χ : ℝ := min c_high (δ_χ * (Real.log 2) ^ 9) with hc_def
  have hc_pos : 0 < c_χ := lt_min hc_high_pos (by positivity)
  refine ⟨c_χ, hc_pos, fun s hs => ?_⟩
  by_cases hre1 : 1 ≤ s.re
  · exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (Or.inl hχ) hre1
  · push Not at hre1
    have hlog_t_ge : Real.log 2 ≤ Real.log (|s.im| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
    have hlog_t_pos : 0 < Real.log (|s.im| + 2) := hlog2_pos.trans_le hlog_t_ge
    by_cases him1 : 1 ≤ |s.im|
    · -- High `|s.im| ≥ 1`: apply `Stage5DirichletLZeroFree.LFunction_ne_zero_in_zeroFreeRegion`
      have hlog_cmp := log_q_mul_le_const_mul_log hq2 s.im
      have hlogq_pos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
        Real.log_pos (by nlinarith [abs_nonneg s.im])
      have hpow9 : (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 ≤
          A_q ^ 9 * (Real.log (|s.im| + 2)) ^ 9 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hlogq_pos.le hlog_cmp 9
      have hdiv : c_χ / (Real.log (|s.im| + 2)) ^ 9 ≤
          Stage5DirichletLZeroFree.zeroFreeConst / (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 := by
        calc c_χ / (Real.log (|s.im| + 2)) ^ 9
            ≤ c_high / (Real.log (|s.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_right (min_le_left _ _) (pow_nonneg hlog_t_pos.le 9)
          _ = Stage5DirichletLZeroFree.zeroFreeConst / (A_q ^ 9 * (Real.log (|s.im| + 2)) ^ 9) := by
              dsimp only [c_high]; rw [div_div]
          _ ≤ Stage5DirichletLZeroFree.zeroFreeConst / (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 :=
              div_le_div_of_nonneg_left Stage5DirichletLZeroFree.zeroFreeConst_pos.le
                (pow_pos hlogq_pos 9) hpow9
      exact Stage5DirichletLZeroFree.LFunction_ne_zero_in_zeroFreeRegion hχ (Or.inr him1)
        (by linarith)
    · -- Low `|s.im| < 1`: apply compactness minimum `m` + horizontal MVT
      push Not at him1
      have hdiv_le_δ : c_χ / (Real.log (|s.im| + 2)) ^ 9 ≤ δ_χ := by
        have hpow_ge : (Real.log 2) ^ 9 ≤ (Real.log (|s.im| + 2)) ^ 9 :=
          pow_le_pow_left₀ hlog2_pos.le hlog_t_ge 9
        calc c_χ / (Real.log (|s.im| + 2)) ^ 9
            ≤ (δ_χ * (Real.log 2) ^ 9) / (Real.log (|s.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_right (min_le_right _ _) (pow_nonneg hlog_t_pos.le 9)
          _ ≤ (δ_χ * (Real.log 2) ^ 9) / (Real.log 2) ^ 9 :=
              div_le_div_of_nonneg_left (by positivity) (pow_pos hlog2_pos 9) hpow_ge
          _ = δ_χ := mul_div_cancel_right₀ _ (pow_pos hlog2_pos 9).ne'
      have hs_re_ge : 1 - δ_χ ≤ s.re := by linarith
      set Lq : ℝ := Real.log ((q : ℝ) * (|s.im| + 2)) with hLq_def
      have hLq_pos : 0 < Lq := Real.log_pos (by nlinarith [abs_nonneg s.im])
      have hLq_le : Lq ≤ L3q := Real.log_le_log (by nlinarith [abs_nonneg s.im]) (by nlinarith)
      have hinv_le : L3q⁻¹ ≤ Lq⁻¹ := inv_anti₀ hLq_pos hLq_le
      have hmvt := Stage5DirichletLZeroFree.norm_LFunction_sub_le_of_strip hχ
        (σ₁ := s.re) (σ₂ := 1) (t := s.im) (by linarith) hre1.le (by norm_num)
      have hs_eq : (s.re : ℂ) + I * (s.im : ℂ) = s := by
        have := Complex.re_add_im s
        simpa only [mul_comm I] using this
      have h1_eq : ((1 : ℝ) : ℂ) + I * (s.im : ℂ) = 1 + I * (s.im : ℂ) := by simp
      rw [hs_eq, h1_eq] at hmvt
      have hmin_le : m ≤ ‖DirichletCharacter.LFunction χ (1 + I * (s.im : ℂ))‖ :=
        ht₀_min (abs_le.mp him1.le)
      have hdiff_lt : (1 - s.re) * (288 * Lq ^ 2) < m := by
        have h1s : 1 - s.re ≤ δ_χ := by linarith
        have hsq : Lq ^ 2 ≤ L3q ^ 2 := pow_le_pow_left₀ hLq_pos.le hLq_le 2
        have h1 : (1 - s.re) * (288 * Lq ^ 2) ≤ δ_χ * (288 * L3q ^ 2) :=
          mul_le_mul h1s (by linarith) (by positivity) hδ_pos.le
        have h2 : δ_χ * (288 * L3q ^ 2) ≤ m / 2 := by
          have := mul_le_mul_of_nonneg_right hδ_le_m (show 0 ≤ 288 * L3q ^ 2 by positivity)
          have hcancel : m / (2 * (288 * L3q ^ 2)) * (288 * L3q ^ 2) = m / 2 := by
            field_simp [hL3q_pos.ne']
          linarith
        linarith
      intro hzero
      rw [hzero, sub_zero] at hmvt
      linarith

/-- **Unconditional Quantitative Log-Derivative Bound Inside the Fixed-Modulus Zero-Free Region**
(sharp `(log(|s.im| + 2)) ^ 10` form, valid for ALL `s.im : ℝ` since `LFunction χ` is entire!):
for every non-principal `χ ≠ 1` mod `q`, there exist `c' > 0` and `C' > 0` such that
`‖-deriv (LFunction χ) s / LFunction χ s‖ ≤ C' * (Real.log (|s.im| + 2)) ^ 10`
whenever `1 - c' / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re ≤ 2`. -/
theorem negLogDerivL_zeroFree_bound_pow10 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ s : ℂ, 1 - c' / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re → s.re ≤ 2 →
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
          C' * (Real.log (|s.im| + 2)) ^ 10 := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c_zf, hc_zf_pos, hzf⟩ := LFunction_zeroFreeRegion_fixed_char hχ
  -- Choose `c ≤ min c_zf ((log 2)^9 / 4)` so `c / L^9 ≤ 1/4` for ALL `t : ℝ`
  set c : ℝ := min c_zf ((Real.log 2) ^ 9 / 4) with hc_def
  have hc_pos : 0 < c := lt_min hc_zf_pos (by positivity)
  have hc_le_zf : c ≤ c_zf := min_le_left _ _
  have hc_le_qtr : c ≤ (Real.log 2) ^ 9 / 4 := min_le_right _ _
  have hc_le_one : c ≤ 1 := by
    have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have hpow_le1 : (Real.log 2) ^ 9 ≤ 1 := pow_le_one₀ hlog2_pos.le hlog2_lt1.le
    linarith
  set P29 : ℝ := (2 : ℝ) ^ (9 : ℕ) with hP29_def
  have hP29_pos : 0 < P29 := by positivity
  set c' : ℝ := c / (16 * P29) with hc'_def
  have hc'_pos : 0 < c' := by positivity
  -- Constants for Case 1 (`s.re ≥ 1 + c'/L^9`) and Case 2 (`s.re < 1 + c'/L^9`)
  set C_right : ℝ := (1 / c') / Real.log 2 + 1 / (Real.log 2) ^ 10 with hC_right_def
  have hC_right_pos : 0 < C_right := by positivity
  set K_arg : ℝ := 64 * P29 * (q : ℝ) / c with hK_arg_def
  have hK_arg_gt1 : 1 < K_arg := by
    dsimp only [K_arg, P29]
    rw [one_lt_div hc_pos]
    nlinarith
  have hlogK_pos : 0 < Real.log K_arg := Real.log_pos hK_arg_gt1
  set A_M : ℝ := Real.log K_arg / Real.log 2 + 10 with hAM_def
  have hAM_pos : 0 < A_M := by positivity
  set C_left : ℝ := (16 * P29 / c) * A_M with hC_left_def
  have hC_left_pos : 0 < C_left := by positivity
  set C' : ℝ := max C_right C_left with hC'_def
  have hC'_pos : 0 < C' := lt_of_lt_of_le hC_left_pos (le_max_right _ _)
  refine ⟨c', hc'_pos, C', hC'_pos, fun s hre_lo hre_hi => ?_⟩
  set t : ℝ := s.im
  set L : ℝ := Real.log (|t| + 2) with hL_def
  have ht2_ge2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have ht2_pos : 0 < |t| + 2 := by linarith
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) ht2_ge2
  have hL_pos : 0 < L := hlog2_pos.trans_le hL_ge
  have hL9_pos : 0 < L ^ 9 := pow_pos hL_pos 9
  have hL10_pos : 0 < L ^ 10 := pow_pos hL_pos 10
  by_cases hright : 1 + c' / L ^ 9 ≤ s.re
  · -- Case 1: `s.re ≥ 1 + c' / L^9`, direct from `Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re`
    have hs_re_gt1 : 1 < s.re := by
      have : 0 < c' / L ^ 9 := div_pos hc'_pos hL9_pos
      linarith
    have hs_eq : (s.re : ℂ) + I * (t : ℂ) = s := by
      have := Complex.re_add_im s
      simpa only [t, mul_comm I] using this
    have hbd := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hs_re_gt1 t).2.2
    unfold Stage3ZeroFreeRegion.negLogDerivL at hbd
    rw [hs_eq] at hbd
    have hinv_le : 1 / (s.re - 1) ≤ L ^ 9 / c' := by
      rw [div_le_div_iff₀ (by linarith) hc'_pos, one_mul]
      have h1 : c' / L ^ 9 ≤ s.re - 1 := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hL9_pos.le
      rw [div_mul_cancel₀ _ hL9_pos.ne'] at h2
      linarith
    have h1_le_L : 1 ≤ L / Real.log 2 := (one_le_div hlog2_pos).mpr hL_ge
    have h1_le_L10 : 1 ≤ L ^ 10 / (Real.log 2) ^ 10 :=
      (one_le_div (pow_pos hlog2_pos 10)).mpr (pow_le_pow_left₀ hlog2_pos.le hL_ge 10)
    have hterm1 : L ^ 9 / c' ≤ ((1 / c') / Real.log 2) * L ^ 10 := by
      have h := mul_le_mul_of_nonneg_left h1_le_L (show 0 ≤ L ^ 9 / c' by positivity)
      have hrhs : (L ^ 9 / c') * (L / Real.log 2) = ((1 / c') / Real.log 2) * L ^ 10 := by
        field_simp [hc'_pos.ne', hlog2_pos.ne']
      linarith
    have hterm2 : (1 : ℝ) ≤ (1 / (Real.log 2) ^ 10) * L ^ 10 := by
      have : (1 / (Real.log 2) ^ 10) * L ^ 10 = L ^ 10 / (Real.log 2) ^ 10 := by ring
      linarith
    calc ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
        ≤ 1 / (s.re - 1) + 1 := hbd
      _ ≤ L ^ 9 / c' + 1 := by linarith
      _ ≤ ((1 / c') / Real.log 2) * L ^ 10 + (1 / (Real.log 2) ^ 10) * L ^ 10 := by linarith
      _ = C_right * L ^ 10 := by dsimp only [C_right]; ring
      _ ≤ C' * L ^ 10 := mul_le_mul_of_nonneg_right (le_max_left _ _) hL10_pos.le
  · -- Case 2: `1 - c' / L^9 ≤ s.re < 1 + c' / L^9`, Borel–Carathéodory on a zero-free disk
    push Not at hright
    set η : ℝ := c / (8 * P29 * L ^ 9) with hη_def
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 32 := by
      have hpow_ge : (Real.log 2) ^ 9 ≤ L ^ 9 := pow_le_pow_left₀ hlog2_pos.le hL_ge 9
      have h1 : c / L ^ 9 ≤ 1 / 4 := by
        calc c / L ^ 9 ≤ ((Real.log 2) ^ 9 / 4) / L ^ 9 :=
              div_le_div_of_nonneg_right hc_le_qtr hL9_pos.le
          _ ≤ ((Real.log 2) ^ 9 / 4) / (Real.log 2) ^ 9 :=
              div_le_div_of_nonneg_left (by positivity) (pow_pos hlog2_pos 9) hpow_ge
          _ = 1 / 4 := by field_simp [(pow_pos hlog2_pos 9).ne']
      have hP29_ge1 : (1 : ℝ) ≤ P29 := by dsimp only [P29]; norm_num
      have hη_eq : η = (c / L ^ 9) / (8 * P29) := by dsimp only [η]; ring
      rw [hη_eq]
      calc (c / L ^ 9) / (8 * P29) ≤ (1 / 4) / (8 * 1) :=
            div_le_div₀ (by norm_num) h1 (by norm_num) (by linarith)
        _ = 1 / 32 := by norm_num
    set R_open : ℝ := 5 * η
    set R : ℝ := 4 * η
    set r : ℝ := 2 * η
    have hR_open_pos : 0 < R_open := by positivity
    have hR_pos : 0 < R := by positivity
    have hrR : r < R := by dsimp only [r, R]; linarith
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (t : ℂ) with hs₀_def
    have hs₀_re : s₀.re = 1 + η := by simp [s₀]
    have hs₀_im : s₀.im = t := by simp [s₀]
    -- Every `z ∈ ball s₀ R_open` lies in the zero-free region of `LFunction χ`
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
        have hR_le_half : R_open ≤ 1 / 2 := by dsimp only [R_open]; linarith
        linarith [abs_le.mpr him_diff]
      have hlog_le : Real.log (|z.im| + 2) ≤ 2 * L := by
        have hsq : |z.im| + 2 ≤ (|t| + 2) ^ 2 := by nlinarith [abs_nonneg t]
        have h1 := Real.log_le_log (by linarith [abs_nonneg z.im]) hsq
        rw [Real.log_pow] at h1
        simpa [L] using h1
      have hlogz_pos : 0 < Real.log (|z.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg z.im])
      have hpow9_le : (Real.log (|z.im| + 2)) ^ 9 ≤ P29 * L ^ 9 := by
        have h1 := pow_le_pow_left₀ hlogz_pos.le hlog_le 9
        rwa [mul_pow] at h1
      have hdiv_ge : c / (P29 * L ^ 9) ≤ c_zf / (Real.log (|z.im| + 2)) ^ 9 := by
        calc c / (P29 * L ^ 9) ≤ c / (Real.log (|z.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_left hc_pos.le (pow_pos hlogz_pos 9) hpow9_le
          _ ≤ c_zf / (Real.log (|z.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_right hc_le_zf (pow_nonneg hlogz_pos.le 9)
      have h4η : 4 * η ≤ c / (P29 * L ^ 9) := by
        have hEq : 4 * η = (c / (P29 * L ^ 9)) / 2 := by dsimp only [η]; ring
        have hnn : 0 ≤ c / (P29 * L ^ 9) := by positivity
        linarith
      have hz_re_ge : 1 - c_zf / (Real.log (|z.im| + 2)) ^ 9 ≤ z.re := by
        dsimp only [R_open] at hre_diff
        linarith
      exact hzf z hz_re_ge
    have hball_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball s₀ R_open) :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
      (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
    -- Upper bound `(Log z).re ≤ M := A_M * L` on `closedBall s₀ R`
    set M : ℝ := A_M * L with hM_def
    have hLog_re_le : ∀ z ∈ Metric.closedBall s₀ R, (Log z).re ≤ M := by
      intro z hz
      have hz_ball : z ∈ Metric.ball s₀ R_open := hcb_sub hz
      have hznz : DirichletCharacter.LFunction χ z ≠ 0 := hball_nz z hz_ball
      have hs₀_nz : DirichletCharacter.LFunction χ s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hR_le_8 : R ≤ 1 / 8 := by dsimp only [R]; linarith
      have hz_re_lo : 1 / 2 ≤ z.re := by linarith
      have hz_re_hi : z.re ≤ 2 := by linarith
      have hz_im_hi : |z.im| ≤ |t| + 1 / 2 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        linarith [abs_le.mpr him_diff]
      have hz_bd : ‖DirichletCharacter.LFunction χ z‖ ≤ 4 * (q : ℝ) * (|t| + 2) := by
        have h1 := Stage5DirichletLZeroFree.norm_LFunction_le_of_stepSum_bound hχ (Nat.cast_nonneg q)
          (fun u _ => Stage5DirichletLZeroFree.norm_stepSum_dirichletChar_le_modulus hχ u)
          (by linarith : 0 < z.re)
        calc ‖DirichletCharacter.LFunction χ z‖
            ≤ (q : ℝ) * (z.re + |z.im|) / z.re := h1
          _ ≤ (q : ℝ) * (2 + (|t| + 1 / 2)) / (1 / 2) := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_left (by linarith) hq_pos.le) (by norm_num) hz_re_lo
          _ ≤ 4 * (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
      have hinv_s₀ : ‖1 / DirichletCharacter.LFunction χ s₀‖ ≤ 16 * P29 * L ^ 9 / c := by
        have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ
          (by linarith : 1 < 1 + η) t).2.1
        have hsub : (1 + η) - 1 = η := by ring
        rw [hsub] at h
        have hs₀_eq' : ((1 + η : ℝ) : ℂ) + I * (t : ℂ) = s₀ := rfl
        rw [hs₀_eq'] at h
        have h2 : (1 + η) / η ≤ 2 / η := div_le_div_of_nonneg_right (by linarith) hη_pos.le
        have h3 : 2 / η = 16 * P29 * L ^ 9 / c := by
          dsimp only [η]; field_simp [hc_pos.ne', hP29_pos.ne', hL9_pos.ne']; ring
        linarith
      have hratio_le :
          ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ ≤
            K_arg * (|t| + 2) * L ^ 9 := by
        rw [show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀ =
              DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₀) by ring,
          norm_mul]
        calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₀‖
            ≤ (4 * (q : ℝ) * (|t| + 2)) * (16 * P29 * L ^ 9 / c) :=
              mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ = K_arg * (|t| + 2) * L ^ 9 := by dsimp only [K_arg]; ring
      have hre_eq : (Log z).re =
          Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
        have hexp : Real.exp (Log z).re =
            ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
          rw [← Complex.norm_exp, hLog_exp z hz_ball]
        rw [← hexp, Real.log_exp]
      have hratio_pos : 0 < ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ :=
        norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)
      have hlogL_le : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL_pos).trans (by linarith)
      have h1_le_L : 1 ≤ L / Real.log 2 := (one_le_div hlog2_pos).mpr hL_ge
      rw [hre_eq]
      calc Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖
          ≤ Real.log (K_arg * (|t| + 2) * L ^ 9) := Real.log_le_log hratio_pos hratio_le
        _ = Real.log (K_arg * (|t| + 2)) + Real.log (L ^ 9) :=
            Real.log_mul (by positivity) (by positivity)
        _ = Real.log K_arg + Real.log (|t| + 2) + 9 * Real.log L := by
            rw [Real.log_mul (by positivity) ht2_pos.ne', Real.log_pow]; push_cast; ring
        _ ≤ Real.log K_arg * (L / Real.log 2) + L + 9 * L := by
            have h1 : Real.log K_arg ≤ Real.log K_arg * (L / Real.log 2) := by
              nlinarith
            linarith
        _ = M := by dsimp only [M, A_M]; ring
    -- Apply `borelCaratheodory_deriv_le` at `s` with `‖s - s₀‖ ≤ r`
    have hs_dist : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - (1 + η) : ℝ) : ℂ)) :=
        Complex.ext (by simp [s₀]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hc'_eq : c' / L ^ 9 = η / 2 := by dsimp only [c', η]; ring
      dsimp only [r]
      constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_dist
    have hs_ball : s ∈ Metric.ball s₀ R_open :=
      hcb_sub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hs_dist.trans hrR.le))
    rw [(hLog_d s hs_ball).deriv, hLog0, Complex.zero_re, sub_zero] at hbc
    have hcoeff : 2 * R / (R - r) ^ 2 = 16 * P29 * L ^ 9 / c := by
      dsimp only [R, r, η]
      field_simp [hc_pos.ne', hP29_pos.ne', hL9_pos.ne']
      ring
    rw [hcoeff] at hbc
    have hneg_norm :
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
          ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ := by
      rw [neg_div, norm_neg]
    rw [hneg_norm]
    calc ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
        ≤ (16 * P29 * L ^ 9 / c) * M := hbc
      _ = C_left * L ^ 10 := by dsimp only [C_left, M]; ring
      _ ≤ C' * L ^ 10 := mul_le_mul_of_nonneg_right (le_max_right _ _) hL10_pos.le

/-- **Unconditional Quantitative Log-Derivative Bound Inside the Fixed-Modulus Zero-Free Region**
(`(Real.log (|s.im| + 2)) ^ 18` form): for every non-principal `χ ≠ 1` mod `q`, there exist
`c' > 0` and `C' > 0` such that for all `s : ℂ` with `1 - c' / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re ≤ 2`,
`‖-deriv (LFunction χ) s / LFunction χ s‖ ≤ C' * (Real.log (|s.im| + 2)) ^ 18`. -/
theorem negLogDerivL_zeroFree_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ s : ℂ, 1 - c' / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re → s.re ≤ 2 →
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
          C' * (Real.log (|s.im| + 2)) ^ 18 := by
  obtain ⟨c', hc', C', hC', hbd⟩ := negLogDerivL_zeroFree_bound_pow10 hχ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c', hc', C' / (Real.log 2) ^ 8, by positivity, fun s hlo hhi => ?_⟩
  have hL_ge : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hpow8 : (Real.log 2) ^ 8 ≤ (Real.log (|s.im| + 2)) ^ 8 :=
    pow_le_pow_left₀ hlog2_pos.le hL_ge 8
  have h1 : (1 : ℝ) ≤ (Real.log (|s.im| + 2)) ^ 8 / (Real.log 2) ^ 8 :=
    (one_le_div (pow_pos hlog2_pos 8)).mpr hpow8
  calc ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      ≤ C' * (Real.log (|s.im| + 2)) ^ 10 := hbd s hlo hhi
    _ ≤ C' * (Real.log (|s.im| + 2)) ^ 10 * ((Real.log (|s.im| + 2)) ^ 8 / (Real.log 2) ^ 8) := by
        have hnn : 0 ≤ C' * (Real.log (|s.im| + 2)) ^ 10 := by positivity
        nlinarith
    _ = (C' / (Real.log 2) ^ 8) * (Real.log (|s.im| + 2)) ^ 18 := by ring

/-! ## Section 2: Pole-Free Perron Contour Shift for `ψ₁(x, χ)` & Character-Sum Decay -/

/-- **Exact Pole-Free Perron Contour Shift Identity for Non-Principal `χ ≠ 1`**:
whenever `χ ≠ 1`, `0 < x`, `0 < σ < c`, `0 < T`, and `LFunction χ` has no zeros on the closed
rectangle `[σ, c] × [-T, T]`, shifting `truncatedPerronPsi1 χ x c T` to `Re(s) = σ` produces ZERO
pole residues! -/
theorem perron_contour_shift_psi1Char {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {x σ c T : ℝ} (hx : 0 < x)
    (hσ0 : 0 < σ) (hσc : σ < c) (hT : 0 < T)
    (hzf : ∀ z : ℂ, σ ≤ z.re → z.re ≤ c → |z.im| ≤ T → DirichletCharacter.LFunction χ z ≠ 0) :
    let F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivL χ s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
      ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
      ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
  intro F
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set U : Set ℂ := {z : ℂ | 0 < z.re ∧ DirichletCharacter.LFunction χ z ≠ 0}
  have hU_open : IsOpen U := by
    have hL_cont : Continuous (DirichletCharacter.LFunction χ) :=
      (DirichletCharacter.differentiable_LFunction hχ).continuous
    have hset : U = {z : ℂ | 0 < z.re} ∩ (DirichletCharacter.LFunction χ) ⁻¹' ({(0 : ℂ)}ᶜ) := by
      ext z; simp [U]
    rw [hset]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isClosed_singleton.isOpen_compl.preimage hL_cont)
  have hrect_sub : Set.uIcc σ c ×ℂ Set.uIcc (-T) T ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hσc.le,
      Set.uIcc_of_le (by linarith : -T ≤ T)] at hz
    exact ⟨lt_of_lt_of_le hσ0 hz.1.1, hzf z hz.1.1 hz.1.2 (abs_le.mpr hz.2)⟩
  have hF_diff_U : DifferentiableOn ℂ F U := by
    have hL_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    have hnd_diff : DifferentiableOn ℂ (Stage3ZeroFreeRegion.negLogDerivL χ) U := by
      unfold Stage3ZeroFreeRegion.negLogDerivL
      exact (hL_diff.deriv hU_open).neg.div hL_diff fun _ hz => hz.2
    have hW_diff : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ (s + 1) / (s * (s + 1))) U := by
      intro s hs
      have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (z + 1)) s := by
        have hEq : (fun z : ℂ => (x : ℂ) ^ (z + 1)) =
            fun z : ℂ => cexp (Complex.log (x : ℂ) * (z + 1)) :=
          funext fun z => Complex.cpow_def_of_ne_zero hxC _
        rw [hEq]; fun_prop
      have hs0 : s ≠ 0 := fun h => by have := hs.1; rw [h, Complex.zero_re] at this; exact lt_irrefl 0 this
      have hs1 : s + 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith [hs.1]
      exact (hpow.div (differentiableAt_id.mul (differentiableAt_id.add (differentiableAt_const 1)))
        (mul_ne_zero hs0 hs1)).differentiableWithinAt
    have hF_eq : F = fun s => Stage3ZeroFreeRegion.negLogDerivL χ s *
        ((x : ℂ) ^ (s + 1) / (s * (s + 1))) := funext fun s => by dsimp only [F]; ring
    rw [hF_eq]
    exact hnd_diff.mul hW_diff
  -- Apply Cauchy's rectangle theorem directly to `F` on `[σ, c] × [-T, T]`!
  set z₀ : ℂ := (σ : ℂ) + ((-T : ℝ) : ℂ) * I
  set w₀ : ℂ := (c : ℂ) + (T : ℂ) * I
  have hz₀_re : z₀.re = σ := by simp [z₀]
  have hz₀_im : z₀.im = -T := by simp [z₀]
  have hw₀_re : w₀.re = c := by simp [w₀]
  have hw₀_im : w₀.im = T := by simp [w₀]
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z₀ w₀
    (by simpa [hz₀_re, hz₀_im, hw₀_re, hw₀_im] using hF_diff_U.mono hrect_sub)
  simp only [hz₀_re, hz₀_im, hw₀_re, hw₀_im, smul_eq_mul] at hcauchy
  have hright_eq : Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) := by
    unfold Stage4ExplicitFormula.truncatedPerronPsi1
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp only [F]
    have harg : (c : ℂ) + I * (t : ℂ) = (c : ℂ) + (t : ℂ) * I := by ring
    have harg1 : (c : ℂ) + 1 + I * (t : ℂ) = ((c : ℂ) + (t : ℂ) * I) + 1 := by ring
    rw [harg, harg1]
  rw [hright_eq]
  have h2piI_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have h2pi_cast : (2 * Real.pi * I : ℂ) * (((2 * Real.pi : ℝ) : ℂ)⁻¹) = I := by
    have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    push_cast
    field_simp [Real.pi_ne_zero]
  apply mul_left_cancel₀ h2piI_ne
  calc (2 * Real.pi * I : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)))
      = I * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) := by
        rw [← mul_assoc, h2pi_cast]
    _ = I * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
        (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
        (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
        linear_combination hcauchy
    _ = (2 * Real.pi * I : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I))) := by
        rw [mul_sub, mul_add, ← mul_assoc, h2pi_cast, ← mul_assoc, ← mul_assoc,
          mul_inv_cancel₀ h2piI_ne, one_mul, one_mul]

/-- Elementary exponential decay inequality: `u ^ k * exp (-(k : ℝ) * u) ≤ 1` for `k : ℕ`, `u ≥ 0`. -/
private lemma pow_mul_exp_neg_le_one (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * Real.exp (-(k : ℝ) * u) ≤ 1 := by
  have h1 : u * Real.exp (-u) ≤ 1 := by
    have h := Real.add_one_le_exp u
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos u)).mpr (by linarith)
  have h2 : u ^ k * Real.exp (-(k : ℝ) * u) = (u * Real.exp (-u)) ^ k := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2; ring
  rw [h2]
  exact pow_le_one₀ (mul_nonneg hu (Real.exp_pos (-u)).le) h1

/-- Elementary exponent comparison: for `0 < p ≤ q`, `c > 0`, and `x ≥ 2`,
`Real.exp (-c * (Real.log x) ^ q) ≤ Real.exp c * Real.exp (-c * (Real.log x) ^ p)`. -/
private lemma exp_neg_rpow_le_of_le {p q c x : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hc : 0 < c) (hx : 2 ≤ x) :
    Real.exp (-c * (Real.log x) ^ q) ≤
      Real.exp c * Real.exp (-c * (Real.log x) ^ p) := by
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hL1 : 1 ≤ Real.log x
  · have hpow : (Real.log x) ^ p ≤ (Real.log x) ^ q :=
      Real.rpow_le_rpow_of_exponent_le hL1 hpq
    have hexp1 : Real.exp (-c * (Real.log x) ^ q) ≤ Real.exp (-c * (Real.log x) ^ p) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h1 : (1 : ℝ) ≤ Real.exp c := Real.one_le_exp hc.le
    nlinarith [Real.exp_pos (-c * (Real.log x) ^ p)]
  · push Not at hL1
    have hpow_le1 : (Real.log x) ^ p ≤ 1 :=
      Real.rpow_le_one hLx_pos.le hL1.le hp.le
    have hpow_nn : 0 ≤ (Real.log x) ^ q := Real.rpow_nonneg hLx_pos.le q
    have h1 : Real.exp (-c * (Real.log x) ^ q) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : Real.exp (-c) ≤ Real.exp (-c * (Real.log x) ^ p) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hcancel : Real.exp c * Real.exp (-c) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : 1 ≤ Real.exp c * Real.exp (-c * (Real.log x) ^ p) := by
      rw [← hcancel]
      exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos c).le
    linarith

/-- **UNCONDITIONAL EFFECTIVE DECAY FOR NON-PRINCIPAL `ψ₁(x, χ)` (0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`),
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, ‖psi1Char χ x‖ ≤ C * x ^ 2 * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ))`. -/
theorem effective_psi1Char_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
          C * x ^ 2 * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)) := by
  obtain ⟨c_zf, hc_zf, hzf⟩ := LFunction_zeroFreeRegion_fixed_char hχ
  obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := negLogDerivL_zeroFree_bound_pow10 hχ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c_star : ℝ := min (min c_zf c₁) (1 / 4) with hc_star_def
  have hc_star_pos : 0 < c_star := by positivity
  have hc_star_le_zf : c_star ≤ c_zf := (min_le_left _ _).trans (min_le_left _ _)
  have hc_star_le_c₁ : c_star ≤ c₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hc_star_le_qtr : c_star ≤ 1 / 4 := min_le_right _ _
  -- Optimal height parameter `α = c_star ^ (1/10) / 2` so `(2 * α) ^ 10 = c_star`
  set α : ℝ := c_star ^ (1 / 10 : ℝ) / 2 with hα_def
  have hα_pos : 0 < α := by positivity
  have h2α_pow10 : (2 * α) ^ (10 : ℕ) = c_star := by
    have h1 : 2 * α = c_star ^ (1 / 10 : ℝ) := by dsimp only [α]; ring
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hc_star_pos.le]
    norm_num
  set c_fin : ℝ := α / 2 with hc_fin_def
  have hc_fin_pos : 0 < c_fin := by positivity
  -- Threshold `x₀` so that `α * (log x)^{1/10} ≥ 1` (hence `T ≥ e > 2`) for all `x ≥ x₀`
  set x₀ : ℝ := max 2 (Real.exp ((1 / α) ^ (10 : ℕ))) with hx₀_def
  have hx₀_ge2 : 2 ≤ x₀ := le_max_left _ _
  set K_large : ℝ :=
    (48 / Real.pi + (3 * C₁ / Real.pi + 2 * C₁ / Real.pi) * c_star) * (20 / α) ^ (10 : ℕ)
  have hK_large_pos : 0 < K_large := by positivity
  -- Step 1: Prove the bound for all `x ≥ x₀`
  have hlarge : ∀ x : ℝ, x₀ ≤ x →
      ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
        K_large * x ^ 2 * Real.exp (-c_fin * (Real.log x) ^ (1 / 10 : ℝ)) := by
    intro x hx
    have hx2 : 2 ≤ x := hx₀_ge2.trans hx
    have hx0 : 0 < x := by linarith
    set Lx : ℝ := Real.log x with hLx_def
    have hLx_ge_log2 : Real.log 2 ≤ Lx := Real.log_le_log (by norm_num) hx2
    have hLx_pos : 0 < Lx := hlog2_pos.trans_le hLx_ge_log2
    set u : ℝ := Lx ^ (1 / 10 : ℝ) with hu_def
    have hu_pos : 0 < u := Real.rpow_pos_of_pos hLx_pos _
    have hu_pow10 : u ^ (10 : ℕ) = Lx := by
      dsimp only [u]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLx_pos.le]
      norm_num
    have hLx_ge_inv : (1 / α) ^ (10 : ℕ) ≤ Lx := by
      have hexp : Real.exp ((1 / α) ^ (10 : ℕ)) ≤ x := (le_max_right _ _).trans hx
      exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hexp)
    have hαu_ge1 : 1 ≤ α * u := by
      have hpow : (1 : ℝ) ^ (10 : ℕ) ≤ (α * u) ^ (10 : ℕ) := by
        rw [one_pow, mul_pow, hu_pow10]
        have h := mul_le_mul_of_nonneg_left hLx_ge_inv (pow_nonneg hα_pos.le 10)
        rw [← mul_pow, mul_one_div_cancel hα_pos.ne', one_pow] at h
        exact h
      by_contra hlt
      push Not at hlt
      have : (α * u) ^ (10 : ℕ) < 1 ^ (10 : ℕ) :=
        pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      linarith
    set T : ℝ := Real.exp (α * u) with hT_def
    have hT_pos : 0 < T := Real.exp_pos _
    have hT_ge_e : Real.exp 1 ≤ T := Real.exp_le_exp.mpr hαu_ge1
    have hT_ge2 : 2 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlogT : Real.log T = α * u := Real.log_exp _
    set LT : ℝ := Real.log (T + 2) with hLT_def
    have hLT_ge1 : 1 ≤ LT := by
      have h : Real.exp 1 ≤ T + 2 := by linarith
      exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) h)
    have hLT_pos : 0 < LT := zero_lt_one.trans_le hLT_ge1
    have hLT_le : LT ≤ 2 * (α * u) := by
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
    set σ_T : ℝ := 1 - c_star / LT ^ 9 with hσ_def
    have hσ_lt1 : σ_T < 1 := by dsimp only [σ_T]; linarith [div_pos hc_star_pos (pow_pos hLT_pos 9)]
    have hσ_ge_half : 1 / 2 ≤ σ_T := by
      have hLT9_ge1 : (1 : ℝ) ≤ LT ^ 9 := one_le_pow₀ hLT_ge1
      have h1 : c_star / LT ^ 9 ≤ 1 / 4 := by
        calc c_star / LT ^ 9 ≤ c_star / 1 :=
              div_le_div_of_nonneg_left hc_star_pos.le zero_lt_one hLT9_ge1
          _ = c_star := div_one _
          _ ≤ 1 / 4 := hc_star_le_qtr
      dsimp only [σ_T]; linarith
    have hσ_pos : 0 < σ_T := by linarith
    -- Zero-freeness on `[σ_T, c] × [-T, T]`
    have hzf_rect : ∀ z : ℂ, σ_T ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hlo _ him
      have hlog_le : Real.log (|z.im| + 2) ≤ LT :=
        Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
      have hlog_pos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
      have hpow9 : (Real.log (|z.im| + 2)) ^ 9 ≤ LT ^ 9 :=
        pow_le_pow_left₀ hlog_pos.le hlog_le 9
      have h1 : c_star / LT ^ 9 ≤ c_zf / (Real.log (|z.im| + 2)) ^ 9 := by
        calc c_star / LT ^ 9 ≤ c_star / (Real.log (|z.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_left hc_star_pos.le (pow_pos hlog_pos 9) hpow9
          _ ≤ c_zf / (Real.log (|z.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_right hc_star_le_zf (pow_nonneg hlog_pos.le 9)
      exact hzf z (by linarith)
    set F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivL χ s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    -- (A) Truncation error from `Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le`
    have htrunc_err :
        ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ ≤
          (48 / Real.pi) * x ^ 2 * Lx / T := by
      have h0 := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le χ hx0 hc_gt1 hT_pos
      have hc_sub : c - 1 = 1 / (2 * Lx) := by dsimp only [c]; ring
      rw [hc_sub] at h0
      calc ‖Stage4ExplicitFormula.psi1Char χ x -
              Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖
          ≤ (6 * c / Real.pi) * x ^ (c + 1) / (1 / (2 * Lx) * T) := h0
        _ ≤ (6 * 2 / Real.pi) * (2 * x ^ 2) / (1 / (2 * Lx) * T) := by gcongr
        _ = (48 / Real.pi) * x ^ 2 * Lx / T := by
            field_simp [Real.pi_ne_zero, hLx_pos.ne', hT_pos.ne']; ring
    -- (B) Exact pole-free contour shift identity
    have hshift := perron_contour_shift_psi1Char hχ hx0 hσ_pos (by linarith : σ_T < c) hT_pos hzf_rect
    -- (C) Horizontal segment bounds (`t = ±T`, `u ∈ [σ_T, c]`)
    have hhoriz_bd : ∀ sgn : ℝ, |sgn| = 1 →
        ‖∫ v in σ_T..c, F ((v : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
          2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by
      intro sgn hsgn
      have hle : σ_T ≤ c := by linarith
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2) fun v hv => ?_).trans ?_
      · rw [Set.uIoc_of_le hle] at hv
        set z : ℂ := (v : ℂ) + ((sgn * T : ℝ) : ℂ) * I
        have hz_re : z.re = v := by simp [z]
        have hz_im : z.im = sgn * T := by simp [z]
        have hz_abs_im : |z.im| = T := by
          rw [hz_im, abs_mul, hsgn, one_mul, abs_of_pos hT_pos]
        have hz_re_lo : 1 - c₁ / (Real.log (|z.im| + 2)) ^ 9 ≤ z.re := by
          rw [hz_re, hz_abs_im]
          have : c_star / LT ^ 9 ≤ c₁ / LT ^ 9 :=
            div_le_div_of_nonneg_right hc_star_le_c₁ (pow_nonneg hLT_pos.le 9)
          dsimp only [σ_T] at hv; linarith [hv.1]
        have hz_re_hi : z.re ≤ 2 := by rw [hz_re]; linarith [hv.2]
        have hnd := hbd₁ z hz_re_lo hz_re_hi
        rw [hz_abs_im] at hnd
        have hpow_norm : ‖(x : ℂ) ^ (z + 1)‖ ≤ x ^ (c + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre1 : (z + 1).re = v + 1 := by simp [hz_re]
          rw [hre1]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hv.2])
        have hden_ge : T ^ 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : T ≤ ‖z‖ := by rw [← hz_abs_im]; exact Complex.abs_im_le_norm z
          have h2 : T ≤ ‖z + 1‖ := by
            have := Complex.abs_im_le_norm (z + 1)
            simpa [hz_abs_im] using this
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
        rw [norm_div, norm_mul]
        calc ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ *
                ‖(x : ℂ) ^ (z + 1)‖ / ‖z * (z + 1)‖
            ≤ (C₁ * LT ^ 10) * x ^ (c + 1) / T ^ 2 := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul hnd hpow_norm (norm_nonneg _) (by positivity))
                (sq_pos_of_pos hT_pos) hden_ge
          _ = C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by ring
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        have hlen : c - σ_T ≤ 2 := by linarith
        calc C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 * (c - σ_T)
            ≤ C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 * 2 :=
              mul_le_mul_of_nonneg_left hlen (by positivity)
          _ = 2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by ring
    have htop_bd : ‖∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by
      simpa using hhoriz_bd 1 (by norm_num)
    have hbot_bd : ‖∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by
      simpa using hhoriz_bd (-1) (by norm_num)
    -- (D) Left vertical segment bound (`s = σ_T + t * I`, `t ∈ [-T, T]`)
    have hleft_cont : ContinuousOn (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
      have hL_cont : Continuous (DirichletCharacter.LFunction χ) :=
        (DirichletCharacter.differentiable_LFunction hχ).continuous
      have hL'_cont : Continuous (deriv (DirichletCharacter.LFunction χ)) :=
        continuousOn_univ.mp
          ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.deriv isOpen_univ).continuousOn
      have hmap : Continuous (fun t : ℝ => (σ_T : ℂ) + (t : ℂ) * I) := by fun_prop
      have hnd_cont : ContinuousOn (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ ((σ_T : ℂ) + (t : ℂ) * I))
          (Set.Icc (-T) T) := by
        unfold Stage3ZeroFreeRegion.negLogDerivL
        refine (hL'_cont.comp hmap).neg.continuousOn.div (hL_cont.comp hmap).continuousOn fun t ht => ?_
        exact hzf_rect _ (by simp) (by simp; linarith) (by simp [abs_le, ht.1, ht.2])
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
    -- Pointwise log-deriv bound on the entire left edge `σ_T + t * I`, `|t| ≤ T`
    have hleft_nd : ∀ t : ℝ, |t| ≤ T →
        ‖-deriv (DirichletCharacter.LFunction χ) ((σ_T : ℂ) + (t : ℂ) * I) /
          DirichletCharacter.LFunction χ ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * LT ^ 10 := by
      intro t htT
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have hz_im : z.im = t := by simp [z]
      have hlog_le : Real.log (|t| + 2) ≤ LT := Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
      have hlog_pos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
      have hpow9 : (Real.log (|t| + 2)) ^ 9 ≤ LT ^ 9 := pow_le_pow_left₀ hlog_pos.le hlog_le 9
      have hz_re_lo : 1 - c₁ / (Real.log (|z.im| + 2)) ^ 9 ≤ z.re := by
        rw [hz_re, hz_im]
        have h1 : c_star / LT ^ 9 ≤ c₁ / (Real.log (|t| + 2)) ^ 9 := by
          calc c_star / LT ^ 9 ≤ c_star / (Real.log (|t| + 2)) ^ 9 :=
                div_le_div_of_nonneg_left hc_star_pos.le (pow_pos hlog_pos 9) hpow9
            _ ≤ c₁ / (Real.log (|t| + 2)) ^ 9 :=
                div_le_div_of_nonneg_right hc_star_le_c₁ (pow_nonneg hlog_pos.le 9)
        dsimp only [σ_T]; linarith
      have hnd := hbd₁ z hz_re_lo (by rw [hz_re]; linarith)
      rw [hz_im] at hnd
      exact hnd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog_pos.le hlog_le 10) hC₁.le)
    -- Piece 1: `1 ≤ |t| ≤ T`
    have hleft_tail_pt : ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
        ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * LT ^ 10 * x ^ (σ_T + 1) / t ^ 2 := by
      intro t ht1 htT
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have hz_im : z.im = t := by simp [z]
      have hnd' := hleft_nd t htT
      have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [hz_re]
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
      dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
      rw [norm_div, norm_mul, hpow]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hx0.le _))
        ht2_pos hden
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
        C₁ * LT ^ 10 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 10 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (1 : ℝ) T := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact pow_ne_zero 2 (by linarith [ht.1])
      calc ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (1 : ℝ)..T, ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (1 : ℝ)..T, C₁ * LT ^ 10 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg 1 T (by linarith) (by linarith) le_rfl).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1)
              (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.2)
        _ = C₁ * LT ^ 10 * x ^ (σ_T + 1) * ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 10 * x ^ (σ_T + 1) * 1 :=
            mul_le_mul_of_nonneg_left hinv_sq_1T (by positivity)
        _ = C₁ * LT ^ 10 * x ^ (σ_T + 1) := mul_one _
    have hleft_neg_bd : ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C₁ * LT ^ 10 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 10 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (-T) (-1 : ℝ) := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact pow_ne_zero 2 (by linarith [ht.2])
      calc ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (-T)..(-1 : ℝ), ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (-T)..(-1 : ℝ), C₁ * LT ^ 10 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith)).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
              (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
        _ = C₁ * LT ^ 10 * x ^ (σ_T + 1) * ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 10 * x ^ (σ_T + 1) * 1 :=
            mul_le_mul_of_nonneg_left hinv_sq_neg (by positivity)
        _ = C₁ * LT ^ 10 * x ^ (σ_T + 1) := mul_one _
    -- Piece 2: `t ∈ [-1, 1]` (NO POLE!)
    have hleft_mid_bd : ‖∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        4 * C₁ * LT ^ 10 * x ^ (σ_T + 1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 2 * C₁ * LT ^ 10 * x ^ (σ_T + 1)) fun t ht => ?_).trans ?_
      · rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
        have hz_re : z.re = σ_T := by simp [z]
        have htT : |t| ≤ T := by
          have : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
          linarith
        have hnd' := hleft_nd t htT
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
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
        rw [norm_div, norm_mul, hpow]
        calc ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ *
                x ^ (σ_T + 1) / ‖z * (z + 1)‖
            ≤ (C₁ * LT ^ 10) * x ^ (σ_T + 1) / (1 / 2) := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hx0.le _)) (by norm_num) hden
          _ = 2 * C₁ * LT ^ 10 * x ^ (σ_T + 1) := by ring
      · norm_num
        linarith
    have hleft_bd : ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        6 * C₁ * LT ^ 10 * x ^ (σ_T + 1) := by
      rw [hsplit_left]
      have htri1 := norm_add_le
        ((∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)))
        (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I))
      have htri2 := norm_add_le
        (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I))
        (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I))
      linarith
    -- (E) Combine truncation error + contour shift bounds!
    have hshift_bd :
        ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ ≤
          (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) +
          (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by
      rw [hshift]
      have hnorm_2pi : ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hnorm_2piI : ‖((2 * Real.pi * I : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
      have htri :
          ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)) -
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤
          (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
        have h1 := norm_sub_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)))
        have h2 := norm_add_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)))
        simp only [norm_mul, hnorm_2pi, hnorm_2piI] at h1 h2
        linarith
      have hterm_left : (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
          (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) := by
        calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
            ≤ (2 * Real.pi)⁻¹ * (6 * C₁ * LT ^ 10 * x ^ (σ_T + 1)) :=
              mul_le_mul_of_nonneg_left hleft_bd (by positivity)
          _ = (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) := by field_simp [Real.pi_ne_zero]; ring
      have hterm_horiz : ∀ Ival : ℂ, ‖Ival‖ ≤ 2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 →
          (2 * Real.pi)⁻¹ * ‖Ival‖ ≤ (C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by
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
            ≤ (2 * Real.pi)⁻¹ * (2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2) :=
              mul_le_mul_of_nonneg_left hIval (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 10 * (x ^ (c + 1) / T ^ 2) := by
              field_simp [Real.pi_ne_zero, hT_pos.ne']
          _ ≤ (C₁ / Real.pi) * LT ^ 10 * (x ^ 2 / T) :=
              mul_le_mul_of_nonneg_left hxc_div (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by ring
      have htop_h := hterm_horiz _ htop_bd
      have hbot_h := hterm_horiz _ hbot_bd
      change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)) -
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤ _
      have hsum2 : (C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T + (C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T =
          (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by ring
      linarith
    -- (F) Combine all errors and substitute `T = exp(α * u)`!
    have htotal : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
        (48 / Real.pi) * x ^ 2 * Lx / T +
        (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) +
        (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by
      have htri : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
          ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ +
          ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ := by
        simpa [sub_add_cancel] using norm_add_le
          (Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T)
          (Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T)
      linarith
    have hLT_pow10 : LT ^ 10 ≤ c_star * Lx := by
      have h1 := pow_le_pow_left₀ hLT_pos.le hLT_le 10
      have h2 : (2 * (α * u)) ^ (10 : ℕ) = c_star * Lx := by
        rw [show 2 * (α * u) = (2 * α) * u by ring, mul_pow, h2α_pow10, hu_pow10]
      linarith
    have hx_left_exp : x ^ (σ_T + 1) ≤ x ^ 2 * Real.exp (-α * u) := by
      have h1 : x ^ (σ_T + 1) = x ^ 2 * x ^ (-(c_star / LT ^ 9)) := by
        rw [show σ_T + 1 = (2 : ℝ) + (-(c_star / LT ^ 9)) by dsimp only [σ_T]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (-(c_star / LT ^ 9)) = Real.exp (-(c_star * Lx / LT ^ 9)) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]; congr 1; ring
      have hexp_le : -(c_star * Lx / LT ^ 9) ≤ -α * u := by
        have hdiv : α * u ≤ c_star * Lx / LT ^ 9 := by
          rw [le_div_iff₀ (pow_pos hLT_pos 9)]
          calc α * u * LT ^ 9
              ≤ α * u * (2 * (α * u)) ^ 9 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLT_pos.le hLT_le 9) (by positivity)
            _ = (1 / 2) * ((2 * α) ^ (10 : ℕ) * u ^ (10 : ℕ)) := by ring
            _ = (1 / 2) * (c_star * Lx) := by rw [h2α_pow10, hu_pow10]
            _ ≤ c_star * Lx := by nlinarith
        linarith
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (sq_nonneg x)
    have hinvT : (1 : ℝ) / T = Real.exp (-α * u) := by
      rw [hT_def, one_div, ← Real.exp_neg]; congr 1; ring
    -- Absorb `Lx = u ^ 10` into `exp(-(α / 2) * u)` via `pow_mul_exp_neg_le_one 10`
    have habsorb : Lx * Real.exp (-α * u) ≤ (20 / α) ^ (10 : ℕ) * Real.exp (-c_fin * u) := by
      have hsplit : Real.exp (-α * u) =
          Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u)) * Real.exp (-c_fin * u) := by
        rw [← Real.exp_add]; congr 1; dsimp only [c_fin]; push_cast; ring
      rw [hsplit, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hv_nn : 0 ≤ (α / 20) * u := by positivity
      have hid : Lx * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u)) =
          (20 / α) ^ (10 : ℕ) * (((α / 20) * u) ^ (10 : ℕ) * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u))) := by
        have h1 : Lx = (20 / α) ^ (10 : ℕ) * ((α / 20) * u) ^ (10 : ℕ) := by
          rw [← mul_pow, show (20 / α) * ((α / 20) * u) = u by field_simp [hα_pos.ne'], hu_pow10]
        have h2 := congrArg (· * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u))) h1
        simpa only [mul_assoc] using h2
      calc Lx * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u))
          = (20 / α) ^ (10 : ℕ) *
              (((α / 20) * u) ^ (10 : ℕ) * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u))) := hid
        _ ≤ (20 / α) ^ (10 : ℕ) * 1 :=
            mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_one 10 hv_nn) (by positivity)
        _ = (20 / α) ^ (10 : ℕ) := mul_one _
    have hterm1 : (48 / Real.pi) * x ^ 2 * Lx / T =
        (48 / Real.pi) * x ^ 2 * (Lx * Real.exp (-α * u)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]; ring
    have hterm2 : (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) ≤
        ((3 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by
      calc (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1)
          ≤ (3 * C₁ / Real.pi) * (c_star * Lx) * (x ^ 2 * Real.exp (-α * u)) := by gcongr
        _ = ((3 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by ring
    have hterm3 : (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T ≤
        ((2 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]
      calc (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 * Real.exp (-α * u)
          ≤ (2 * C₁ / Real.pi) * (c_star * Lx) * x ^ 2 * Real.exp (-α * u) := by gcongr
        _ = ((2 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by ring
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ (48 / Real.pi + (3 * C₁ / Real.pi + 2 * C₁ / Real.pi) * c_star) *
            x ^ 2 * (Lx * Real.exp (-α * u)) := by linarith
      _ ≤ (48 / Real.pi + (3 * C₁ / Real.pi + 2 * C₁ / Real.pi) * c_star) *
            x ^ 2 * ((20 / α) ^ (10 : ℕ) * Real.exp (-c_fin * u)) := by gcongr
      _ = K_large * x ^ 2 * Real.exp (-c_fin * u) := by dsimp only [K_large]; ring
  -- Step 2: Cover `2 ≤ x < x₀`
  set C_small : ℝ := 6 * Real.exp (c_fin * (Real.log x₀) ^ (1 / 10 : ℝ))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  by_cases hge : x₀ ≤ x
  · exact (hlarge x hge).trans (by gcongr; exact le_max_left _ _)
  · push Not at hge
    have hpsi1_le : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ 6 * x ^ 2 := by
      have h1 : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ x * RHDirect.chebyshevPsi x := by
        unfold Stage4ExplicitFormula.psi1Char RHDirect.chebyshevPsi
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.norm_of_nonneg (le_max_right _ _)]
        have hmax : max (x - (n : ℝ)) 0 ≤ x :=
          max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
        have hchi : ‖χ n‖ ≤ 1 := χ.norm_le_one _
        calc Λ n * ‖χ n‖ * max (x - (n : ℝ)) 0
            ≤ Λ n * 1 * x := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hchi ArithmeticFunction.vonMangoldt_nonneg)
                hmax (le_max_right _ _) (by linarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)])
          _ = x * Λ n := by ring
      have h2 := Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith : 1 ≤ x)
      nlinarith
    have hexp_ge :
        Real.exp (-c_fin * (Real.log x₀) ^ (1 / 10 : ℝ)) ≤
          Real.exp (-c_fin * (Real.log x) ^ (1 / 10 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log x ≤ Real.log x₀ := Real.log_le_log (by linarith) hge.le
      have hrpow : (Real.log x) ^ (1 / 10 : ℝ) ≤ (Real.log x₀) ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog (by norm_num)
      nlinarith
    have hcancel : C_small * Real.exp (-c_fin * (Real.log x₀) ^ (1 / 10 : ℝ)) = 6 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : c_fin * (Real.log x₀) ^ (1 / 10 : ℝ) + -c_fin * (Real.log x₀) ^ (1 / 10 : ℝ) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ 6 * x ^ 2 := hpsi1_le
      _ = C_small * x ^ 2 * Real.exp (-c_fin * (Real.log x₀) ^ (1 / 10 : ℝ)) := by
          rw [← hcancel]; ring
      _ ≤ C_small * x ^ 2 * Real.exp (-c_fin * (Real.log x) ^ (1 / 10 : ℝ)) := by gcongr
      _ ≤ C_fin * x ^ 2 * Real.exp (-c_fin * (Real.log x) ^ (1 / 10 : ℝ)) := by
          gcongr; exact le_max_right _ _

/-- **Purely Algebraic Complex Finite-Difference De-Smoothing Identity**:
for any `χ : DirichletCharacter ℂ q` and any `0 ≤ x`, `0 ≤ h`:
`‖psi1Char χ (x + h) - psi1Char χ x - h * chebyshevPsiChar χ x‖ ≤ h * (chebyshevPsi (x + h) - chebyshevPsi x)`. -/
theorem norm_psi1Char_diff_sub_mul_chebyshevPsiChar_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
        (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
      h * (RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x) := by
  have hfl_le : ⌊x⌋₊ + 1 ≤ ⌊x + h⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_mono (by linarith)) 1
  have hsub : Finset.range (⌊x⌋₊ + 1) ⊆ Finset.range (⌊x + h⌋₊ + 1) := Finset.range_mono hfl_le
  -- Extend `psi1Char χ x` to `range (⌊x + h⌋₊ + 1)`
  have hpsi1_ext : Stage4ExplicitFormula.psi1Char χ x =
      ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), (Λ n : ℂ) * χ n * ((max (x - (n : ℝ)) 0 : ℝ) : ℂ) := by
    unfold Stage4ExplicitFormula.psi1Char
    refine Finset.sum_subset hsub fun n _ hn => ?_
    have hgt : ⌊x⌋₊ + 1 ≤ n := by simpa [Finset.mem_range] using hn
    have hnx : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hgt)
    rw [max_eq_right (by linarith), Complex.ofReal_zero, mul_zero]
  have hchar_ext : (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * χ n * (h : ℂ) := by
    unfold Stage2DirichletAP.chebyshevPsiChar
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hdiff_eq :
      Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x =
        ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1) \ Finset.range (⌊x⌋₊ + 1),
          (Λ n : ℂ) * χ n * ((max (x + h - (n : ℝ)) 0 : ℝ) : ℂ) := by
    rw [hpsi1_ext, hchar_ext]
    unfold Stage4ExplicitFormula.psi1Char
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sdiff hsub]
    have hinner :
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
            ((Λ n : ℂ) * χ n * ((max (x + h - (n : ℝ)) 0 : ℝ) : ℂ) -
             (Λ n : ℂ) * χ n * ((max (x - (n : ℝ)) 0 : ℝ) : ℂ)) =
          ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * χ n * (h : ℂ) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn_le : (n : ℝ) ≤ x :=
        le_trans (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) (Nat.floor_le hx)
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      push_cast; ring
    rw [hinner, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnot : n ∉ Finset.range (⌊x⌋₊ + 1) := (Finset.mem_sdiff.mp hn).2
    have hgt : ⌊x⌋₊ + 1 ≤ n := by simpa [Finset.mem_range] using hnot
    have hnx : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hgt)
    have hm0 : max (x - (n : ℝ)) 0 = 0 := max_eq_right (by linarith)
    rw [hm0, Complex.ofReal_zero, mul_zero, sub_zero]
  have hpsi_diff :
      RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x =
        ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1) \ Finset.range (⌊x⌋₊ + 1), Λ n := by
    unfold RHDirect.chebyshevPsi
    exact (eq_sub_of_add_eq (Finset.sum_sdiff hsub)).symm
  rw [hdiff_eq, hpsi_diff, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hnot : n ∉ Finset.range (⌊x⌋₊ + 1) := (Finset.mem_sdiff.mp hn).2
  have hgt : ⌊x⌋₊ + 1 ≤ n := by simpa [Finset.mem_range] using hnot
  have hnx : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hgt)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    Real.norm_of_nonneg (le_max_right _ _)]
  have hmax_le : max (x + h - (n : ℝ)) 0 ≤ h := max_le (by linarith) hh
  have hchi : ‖χ n‖ ≤ 1 := χ.norm_le_one _
  calc Λ n * ‖χ n‖ * max (x + h - (n : ℝ)) 0
      ≤ Λ n * 1 * h := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hchi ArithmeticFunction.vonMangoldt_nonneg)
          hmax_le (le_max_right _ _) (by linarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)])
    _ = h * Λ n := by ring

/-- **Unconditional Effective Character-Sum Decay (`(log x)^(1/10)` form)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY non-principal `χ ≠ 1` mod `q`:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, ‖chebyshevPsiChar χ x‖ ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ))`. -/
theorem effective_chebyshevPsiChar_bound_one_tenth {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hpsi1⟩ := effective_psi1Char_bound hχ
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  set c_fin : ℝ := min (c₁ / 2) c_ψ with hc_fin_def
  have hc_fin_pos : 0 < c_fin := lt_min (by positivity) hc_ψ
  have hc_fin_le1 : c_fin ≤ c₁ / 2 := min_le_left _ _
  have hc_fin_le_ψ : c_fin ≤ c_ψ := min_le_right _ _
  set C_fin : ℝ := 5 * C₁ + 1 + 3 * C_ψ * Real.exp c_fin
  have hC_fin_pos : 0 < C_fin := by positivity
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  set u : ℝ := (Real.log x) ^ (1 / 10 : ℝ) with hu_def
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hLx_pos _
  set E : ℝ := Real.exp (-c_fin * u) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_le1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  set h : ℝ := x * E with hh_def
  have hh_pos : 0 < h := by positivity
  have hh_le_x : h ≤ x := by nlinarith
  have hxph_ge2 : 2 ≤ x + h := by linarith
  have hxph_le2x : x + h ≤ 2 * x := by linarith
  -- Compare `exp (-c₁ * u)` with `E ^ 2`
  have hexp_E2 : Real.exp (-c₁ * u) ≤ E ^ 2 := by
    rw [hE_def, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast; nlinarith
  have hexp_xh : Real.exp (-c₁ * (Real.log (x + h)) ^ (1 / 10 : ℝ)) ≤ E ^ 2 := by
    have hlog : Real.log x ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
    have hrpow : u ≤ (Real.log (x + h)) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow hLx_pos.le hlog (by norm_num)
    have h1 : Real.exp (-c₁ * (Real.log (x + h)) ^ (1 / 10 : ℝ)) ≤ Real.exp (-c₁ * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact h1.trans hexp_E2
  -- Compare `exp (-c_ψ * √(log x))` with `exp c_fin * E`
  have hexp_psi : Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤ Real.exp c_fin * E := by
    have h1 : Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤ Real.exp (-c_fin * (Real.log x) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.rpow_nonneg hLx_pos.le (1 / 2 : ℝ)]
    exact h1.trans (exp_neg_rpow_le_of_le (by norm_num) (by norm_num) hc_fin_pos hx2)
  have hexp_psi_xh : Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤ Real.exp c_fin * E := by
    have hlog : Real.log x ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
    have h1 : Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤ Real.exp (-c_ψ * Real.sqrt (Real.log x)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_le_sqrt hlog])
    exact h1.trans hexp_psi
  -- Apply the complex finite-difference de-smoothing inequality
  have hdiff := norm_psi1Char_diff_sub_mul_chebyshevPsiChar_le χ hx0.le hh_pos.le
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
        ≤ C₁ * (x + h) ^ 2 * Real.exp (-c₁ * (Real.log (x + h)) ^ (1 / 10 : ℝ)) := hpsi1 (x + h) hxph_ge2
      _ ≤ C₁ * (2 * x) ^ 2 * E ^ 2 := by
          have hsq : (x + h) ^ 2 ≤ (2 * x) ^ 2 := by nlinarith
          gcongr
      _ = 4 * C₁ * x ^ 2 * E ^ 2 := by ring
  have hbd_x : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ C₁ * x ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ C₁ * x ^ 2 * Real.exp (-c₁ * u) := hpsi1 x hx2
      _ ≤ C₁ * x ^ 2 * E ^ 2 := by gcongr
  have hpsi_diff_le :
      RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x ≤
        (1 + 3 * C_ψ * Real.exp c_fin) * x * E := by
    have h1 := (abs_le.mp (hpsi (x + h) hxph_ge2)).2
    have h2 := (abs_le.mp (hpsi x hx2)).1
    have h3 : C_ψ * (x + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤
        2 * C_ψ * Real.exp c_fin * x * E := by
      calc C_ψ * (x + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (x + h)))
          ≤ C_ψ * (2 * x) * (Real.exp c_fin * E) := by gcongr
        _ = 2 * C_ψ * Real.exp c_fin * x * E := by ring
    have h4 : C_ψ * x * Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤
        C_ψ * Real.exp c_fin * x * E := by
      calc C_ψ * x * Real.exp (-c_ψ * Real.sqrt (Real.log x))
          ≤ C_ψ * x * (Real.exp c_fin * E) := by gcongr
        _ = C_ψ * Real.exp c_fin * x * E := by ring
    dsimp only [h] at h1 h2 h3 ⊢
    linarith
  have hcomb : h * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ h * (C_fin * x * E) := by
    have hrhs1 : 5 * C₁ * x ^ 2 * E ^ 2 = h * (5 * C₁ * x * E) := by dsimp only [h]; ring
    have hmul_psi := mul_le_mul_of_nonneg_left hpsi_diff_le hh_pos.le
    have hrhs2 : h * (5 * C₁ * x * E) + h * ((1 + 3 * C_ψ * Real.exp c_fin) * x * E) =
        h * (C_fin * x * E) := by dsimp only [C_fin]; ring
    linarith
  exact le_of_mul_le_mul_left hcomb hh_pos

/-- **UNCONDITIONAL EFFECTIVE CHARACTER-SUM DECAY (`(log x)^(1/20)` form, 0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY non-principal `χ ≠ 1` mod `q`:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, ‖chebyshevPsiChar χ x‖ ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))`. -/
theorem effective_chebyshevPsiChar_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_chebyshevPsiChar_bound_one_tenth hχ
  refine ⟨c, hc, C * Real.exp c, by positivity, fun x hx => ?_⟩
  have hcmp := exp_neg_rpow_le_of_le (p := (1 / 20 : ℝ)) (q := (1 / 10 : ℝ))
    (by norm_num) (by norm_num) hc hx
  calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
      ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)) := hbd x hx
    _ ≤ C * x * (Real.exp c * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))) := by gcongr
    _ = (C * Real.exp c) * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by ring

/-- Helper: `Real.exp (-c * (Real.log x) ^ p) → 0` as `x → ∞` for any `c > 0`, `p > 0`. -/
private lemma tendsto_exp_neg_mul_rpow_log {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ p)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => c * (Real.log x) ^ p) atTop atTop :=
    Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop hp).comp Real.tendsto_log_atTop)
  have h2 : Tendsto (fun x : ℝ => -(c * (Real.log x) ^ p)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  exact (Real.tendsto_exp_atBot.comp h2).congr fun x => by dsimp only [Function.comp_apply]; congr 1; ring

/-- **Unconditional Cancellation `ψ(x, χ) / x → 0`** for every non-principal `χ ≠ 1` mod `q`. -/
theorem chebyshevPsiChar_div_tendsto_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    Tendsto (fun x : ℝ => Stage2DirichletAP.chebyshevPsiChar χ x / (x : ℂ)) atTop (𝓝 0) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_chebyshevPsiChar_bound hχ
  refine squeeze_zero_norm' (a := fun x : ℝ => C * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le, div_le_iff₀ hx0]
    linarith [hbd x hx]
  · simpa using (tendsto_exp_neg_mul_rpow_log hc (by norm_num : (0 : ℝ) < 1 / 20)).const_mul C

/-! ## Section 3: Unconditional Effective Prime Number Theorem in Arithmetic Progressions -/

/-- Uniform bound over any finite set of non-principal characters mod `q`. -/
private lemma exists_uniform_nonprincipal_char_bound {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ χ ∈ S, ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1, zero_lt_one, 1, zero_lt_one, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert χ S' hnot ih =>
    have hχ : χ ≠ 1 := hS χ (Finset.mem_insert_self χ S')
    obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := effective_chebyshevPsiChar_bound hχ
    obtain ⟨c₂, hc₂, C₂, hC₂, hbd₂⟩ := ih (fun ψ hψ => hS ψ (Finset.mem_insert_of_mem hψ))
    refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _),
      fun ψ hψ x hx => ?_⟩
    have hLx_nn : 0 ≤ (Real.log x) ^ (1 / 20 : ℝ) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    rcases Finset.mem_insert.mp hψ with hEq | hmem
    · rw [hEq]
      have hexp : Real.exp (-c₁ * (Real.log x) ^ (1 / 20 : ℝ)) ≤
          Real.exp (-min c₁ c₂ * (Real.log x) ^ (1 / 20 : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [min_le_left c₁ c₂])
      calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
          ≤ C₁ * x * Real.exp (-c₁ * (Real.log x) ^ (1 / 20 : ℝ)) := hbd₁ x hx
        _ ≤ max C₁ C₂ * x * Real.exp (-min c₁ c₂ * (Real.log x) ^ (1 / 20 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
              hexp (Real.exp_pos _).le (by positivity)
    · have hexp : Real.exp (-c₂ * (Real.log x) ^ (1 / 20 : ℝ)) ≤
          Real.exp (-min c₁ c₂ * (Real.log x) ^ (1 / 20 : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [min_le_right c₁ c₂])
      calc ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖
          ≤ C₂ * x * Real.exp (-c₂ * (Real.log x) ^ (1 / 20 : ℝ)) := hbd₂ ψ hmem x hx
        _ ≤ max C₁ C₂ * x * Real.exp (-min c₁ c₂ * (Real.log x) ^ (1 / 20 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
              hexp (Real.exp_pos _).le (by positivity)

/-- Elementary bound `Real.sqrt x * Real.log x ≤ 4 * Real.exp c * x * Real.exp (-c * (Real.log x) ^ p)`
for `0 < c ≤ 1 / 4`, `0 < p ≤ 1 / 2`, and `x ≥ 2`. -/
private lemma sqrt_mul_log_le_mul_exp_neg_rpow {c p x : ℝ} (hc : 0 < c) (hc_le : c ≤ 1 / 4)
    (hp : 0 < p) (hp_le : p ≤ 1 / 2) (hx : 2 ≤ x) :
    Real.sqrt x * Real.log x ≤ 4 * Real.exp c * x * Real.exp (-c * (Real.log x) ^ p) := by
  have hx0 : 0 < x := by linarith
  set Lx : ℝ := Real.log x with hLx_def
  have hLx_pos : 0 < Lx := Real.log_pos (by linarith)
  have hsqrt_eq : Real.sqrt x = x * Real.exp (-(1 / 2) * Lx) := by
    have h1 : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have h2 : x ^ (1 / 2 : ℝ) = x * x ^ (-(1 / 2 : ℝ)) := by
      calc x ^ (1 / 2 : ℝ) = x ^ ((1 : ℝ) + -(1 / 2 : ℝ)) := by norm_num
        _ = x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ)) := Real.rpow_add hx0 _ _
        _ = x * x ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
    rw [h1, h2, Real.rpow_def_of_pos hx0, ← hLx_def]
    congr 2; ring
  have hkey : Lx * Real.exp (-(1 / 2) * Lx) ≤ 4 * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by
    have h1_mul : (Lx / 4) * Real.exp (-(Lx / 4)) ≤ 1 := by
      have h := pow_mul_exp_neg_le_one 1 (show 0 ≤ Lx / 4 by positivity)
      simpa using h
    by_cases hL1 : 1 ≤ Lx
    · have hpow_le : Lx ^ (1 / 2 : ℝ) ≤ Lx := by
        calc Lx ^ (1 / 2 : ℝ) ≤ Lx ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
          _ = Lx := Real.rpow_one Lx
      have hexp_le : Real.exp (-(1 / 2) * Lx) ≤ Real.exp (-(Lx / 4)) * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      calc Lx * Real.exp (-(1 / 2) * Lx)
          ≤ Lx * (Real.exp (-(Lx / 4)) * Real.exp (-c * Lx ^ (1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hexp_le hLx_pos.le
        _ = 4 * ((Lx / 4) * Real.exp (-(Lx / 4))) * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by ring
        _ ≤ 4 * 1 * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by gcongr
        _ = 4 * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by ring
    · push Not at hL1
      have hpow_le1 : Lx ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hLx_pos.le hL1.le (by norm_num)
      have h1 : Real.exp (-(1 / 2) * Lx) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h2 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-c * Lx ^ (1 / 2 : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg hLx_pos.le (1 / 2 : ℝ)])
      have h3 : (1 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 4 : ℝ))]
      calc Lx * Real.exp (-(1 / 2) * Lx)
          ≤ 1 * 1 := mul_le_mul hL1.le h1 (Real.exp_pos _).le zero_le_one
        _ = 4 * (1 / 4) := by norm_num
        _ ≤ 4 * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by linarith
  have hcmp := exp_neg_rpow_le_of_le hp hp_le hc hx
  rw [hsqrt_eq]
  calc x * Real.exp (-(1 / 2) * Lx) * Lx
      = x * (Lx * Real.exp (-(1 / 2) * Lx)) := by ring
    _ ≤ x * (4 * Real.exp (-c * Lx ^ (1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hkey hx0.le
    _ ≤ x * (4 * (Real.exp c * Real.exp (-c * Lx ^ p))) := by gcongr
    _ = 4 * Real.exp c * x * Real.exp (-c * Lx ^ p) := by ring

/-- **UNCONDITIONAL EFFECTIVE PRIME NUMBER THEOREM IN ARITHMETIC PROGRESSIONS FOR `ψ(x; q, a)` (0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a : ℕ` with `Nat.Coprime a q`:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))`. -/
theorem effective_pnt_psiAP {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  classical
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  obtain ⟨c_χ, hc_χ, C_χ, hC_χ, hchar⟩ :=
    exists_uniform_nonprincipal_char_bound (Finset.univ.erase (1 : DirichletCharacter ℂ q))
      (fun χ hχ => (Finset.mem_erase.mp hχ).1)
  set c_fin : ℝ := min (min c_ψ c_χ) (1 / 4) with hc_fin_def
  have hc_fin_pos : 0 < c_fin := by positivity
  have hc_fin_le_ψ : c_fin ≤ c_ψ := (min_le_left _ _).trans (min_le_left _ _)
  have hc_fin_le_χ : c_fin ≤ c_χ := (min_le_left _ _).trans (min_le_right _ _)
  have hc_fin_le_qtr : c_fin ≤ 1 / 4 := min_le_right _ _
  set ω : ℝ := (q.primeFactors.card : ℝ)
  set C_fin : ℝ := C_ψ * Real.exp c_fin + 4 * ω * Real.exp c_fin + C_χ
  have hC_fin_pos : 0 < C_fin := by positivity
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  set E : ℝ := Real.exp (-c_fin * (Real.log x) ^ (1 / 20 : ℝ)) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  -- Bound `|chebyshevPsi x - x| ≤ C_ψ * exp c_fin * x * E`
  have hpsi_bd : |RHDirect.chebyshevPsi x - x| ≤ (C_ψ * Real.exp c_fin) * x * E := by
    have h1 : Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤
        Real.exp (-c_fin * (Real.log x) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.rpow_nonneg hLx_pos.le (1 / 2 : ℝ)]
    have h2 := h1.trans (exp_neg_rpow_le_of_le (p := (1 / 20 : ℝ)) (q := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) hc_fin_pos hx2)
    calc |RHDirect.chebyshevPsi x - x|
        ≤ C_ψ * x * Real.exp (-c_ψ * Real.sqrt (Real.log x)) := hpsi x hx2
      _ ≤ C_ψ * x * (Real.exp c_fin * E) := by gcongr
      _ = (C_ψ * Real.exp c_fin) * x * E := by ring
  -- Bound `ω * log x ≤ (4 * ω * exp c_fin) * x * E`
  have hlog_bd : ω * Real.log x ≤ (4 * ω * Real.exp c_fin) * x * E := by
    have hsq_ge1 : (1 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    have h1 : Real.log x ≤ Real.sqrt x * Real.log x := by nlinarith
    have h2 := h1.trans (sqrt_mul_log_le_mul_exp_neg_rpow hc_fin_pos hc_fin_le_qtr
      (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num : (1 / 20 : ℝ) ≤ 1 / 2) hx2)
    have hω_nn : 0 ≤ ω := Nat.cast_nonneg _
    calc ω * Real.log x ≤ ω * (4 * Real.exp c_fin * x * E) := mul_le_mul_of_nonneg_left h2 hω_nn
      _ = (4 * ω * Real.exp c_fin) * x * E := by ring
  -- Bound each non-principal character sum uniformly by `C_χ * x * E`
  have hchar_bd : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C_χ * x * E := by
    intro χ hχ
    have hmem : χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q) :=
      Finset.mem_erase.mpr ⟨hχ, Finset.mem_univ _⟩
    calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
        ≤ C_χ * x * Real.exp (-c_χ * (Real.log x) ^ (1 / 20 : ℝ)) := hchar χ hmem x hx2
      _ ≤ C_χ * x * E := by
          dsimp only [E]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [Real.rpow_nonneg hLx_pos.le (1 / 20 : ℝ)]
  have htri := Stage2DirichletAP.abs_chebyshevPsiAP_sub_le_of_uniform_char_bound hcop
    (by linarith : 1 ≤ x) (by positivity : 0 ≤ C_χ * x * E) hpsi_bd hchar_bd
  have hdiv_le : ((C_ψ * Real.exp c_fin) * x * E + ω * Real.log x) / (q.totient : ℝ) ≤
      (C_ψ * Real.exp c_fin + 4 * ω * Real.exp c_fin) * x * E := by
    calc ((C_ψ * Real.exp c_fin) * x * E + ω * Real.log x) / (q.totient : ℝ)
        ≤ ((C_ψ * Real.exp c_fin) * x * E + (4 * ω * Real.exp c_fin) * x * E) / 1 := by
          refine div_le_div₀ (by positivity) (by linarith) zero_lt_one hphi_ge1
      _ = (C_ψ * Real.exp c_fin + 4 * ω * Real.exp c_fin) * x * E := by ring
  dsimp only [C_fin]
  linarith

/-- **UNCONDITIONAL EFFECTIVE PRIME NUMBER THEOREM IN ARITHMETIC PROGRESSIONS FOR `θ(x; q, a)` (0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a : ℕ` with `Nat.Coprime a q`:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))`. -/
theorem effective_pnt_thetaAP {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  obtain ⟨c, hc, C, hC, hpsi⟩ := effective_pnt_psiAP hcop
  set c' : ℝ := min c (1 / 4) with hc'_def
  have hc'_pos : 0 < c' := lt_min hc (by norm_num)
  have hc'_le_c : c' ≤ c := min_le_left _ _
  have hc'_le_qtr : c' ≤ 1 / 4 := min_le_right _ _
  refine ⟨c', hc'_pos, C + 4 * Real.exp c', by positivity, fun x hx => ?_⟩
  have hdiff : |Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x| ≤
      Real.sqrt x * Real.log x := by
    have h1 := Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a x
    have h2 := Stage2DirichletAP.chebyshevPsiAP_sub_chebyshevThetaAP_le q a (by linarith : 1 ≤ x)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1)]
    exact h2
  have hsqrt := sqrt_mul_log_le_mul_exp_neg_rpow hc'_pos hc'_le_qtr
    (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num : (1 / 20 : ℝ) ≤ 1 / 2) hx
  have hpsi' : |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
      C * x * Real.exp (-c' * (Real.log x) ^ (1 / 20 : ℝ)) := by
    have hLx_nn : 0 ≤ (Real.log x) ^ (1 / 20 : ℝ) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    refine (hpsi x hx).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have htri : |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
      |Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x| +
      |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| := by
    simpa [sub_add_sub_cancel] using abs_add_le
      (Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x)
      (Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ))
  linarith

/-- **PRIME NUMBER THEOREM IN ARITHMETIC PROGRESSIONS (`ψ(x; q, a) ~ x / φ(q)`, 0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a` with `Nat.Coprime a q`:
`Tendsto (fun x : ℝ => chebyshevPsiAP q a x / (x / (q.totient : ℝ))) atTop (𝓝 1)`. -/
theorem pnt_psiAP_asymp {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    Tendsto (fun x : ℝ => Stage2DirichletAP.chebyshevPsiAP q a x / (x / (q.totient : ℝ)))
      atTop (𝓝 1) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_pnt_psiAP hcop
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm'
    (a := fun x : ℝ => (q.totient : ℝ) * C * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hden_pos : 0 < x / (q.totient : ℝ) := div_pos hx0 hphi_pos
    rw [Real.norm_eq_abs,
      show Stage2DirichletAP.chebyshevPsiAP q a x / (x / (q.totient : ℝ)) - 1 =
        (Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)) / (x / (q.totient : ℝ)) by
        field_simp [hden_pos.ne'],
      abs_div, abs_of_pos hden_pos, div_le_iff₀ hden_pos]
    have hmul : (q.totient : ℝ) * C * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) *
        (x / (q.totient : ℝ)) = C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
      field_simp [hphi_pos.ne']
    linarith [hbd x hx]
  · simpa using (tendsto_exp_neg_mul_rpow_log hc (by norm_num : (0 : ℝ) < 1 / 20)).const_mul
      ((q.totient : ℝ) * C)

/-- **PRIME NUMBER THEOREM IN ARITHMETIC PROGRESSIONS (`θ(x; q, a) ~ x / φ(q)`, 0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a` with `Nat.Coprime a q`:
`Tendsto (fun x : ℝ => chebyshevThetaAP q a x / (x / (q.totient : ℝ))) atTop (𝓝 1)`. -/
theorem pnt_thetaAP_asymp {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    Tendsto (fun x : ℝ => Stage2DirichletAP.chebyshevThetaAP q a x / (x / (q.totient : ℝ)))
      atTop (𝓝 1) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_pnt_thetaAP hcop
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm'
    (a := fun x : ℝ => (q.totient : ℝ) * C * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hden_pos : 0 < x / (q.totient : ℝ) := div_pos hx0 hphi_pos
    rw [Real.norm_eq_abs,
      show Stage2DirichletAP.chebyshevThetaAP q a x / (x / (q.totient : ℝ)) - 1 =
        (Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)) / (x / (q.totient : ℝ)) by
        field_simp [hden_pos.ne'],
      abs_div, abs_of_pos hden_pos, div_le_iff₀ hden_pos]
    have hmul : (q.totient : ℝ) * C * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) *
        (x / (q.totient : ℝ)) = C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
      field_simp [hphi_pos.ne']
    linarith [hbd x hx]
  · simpa using (tendsto_exp_neg_mul_rpow_log hc (by norm_num : (0 : ℝ) < 1 / 20)).const_mul
      ((q.totient : ℝ) * C)

/-- **Elementary Lower Bound `θ(x; q, a) ≤ π(x; q, a) * log x`** for `x ≥ 1`. -/
private lemma chebyshevThetaAP_le_primeCountAP_mul_log (q a : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Stage2DirichletAP.chebyshevThetaAP q a x ≤
      (Stage2DirichletAP.primeCountAP q a x : ℝ) * Real.log x := by
  unfold Stage2DirichletAP.chebyshevThetaAP Stage2DirichletAP.primeCountAP
  rw [← Finset.sum_filter]
  calc ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), Real.log (n : ℝ)
      ≤ ∑ _n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), Real.log x := by
        refine Finset.sum_le_sum fun n hn => ?_
        simp only [Finset.mem_filter, Finset.mem_range] at hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.2.1.pos
        have hn_le : (n : ℝ) ≤ x :=
          le_trans (by exact_mod_cast (by omega : n ≤ ⌊x⌋₊)) (Nat.floor_le (by linarith))
        exact Real.log_le_log hn_pos hn_le
    _ = (((Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ) * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Elementary Upper Bound `π(x; q, a) ≤ (y + 1) + θ(x; q, a) / log y`** for `1 < y ≤ x`. -/
private lemma primeCountAP_le_add_chebyshevThetaAP_div_log (q a : ℕ) {x y : ℝ}
    (hy : 1 < y) (hyx : y ≤ x) :
    (Stage2DirichletAP.primeCountAP q a x : ℝ) ≤
      (y + 1) + Stage2DirichletAP.chebyshevThetaAP q a x / Real.log y := by
  have hlogy_pos : 0 < Real.log y := Real.log_pos hy
  set Sx : Finset ℕ := (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])
  set Sy : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])
  have hsub : Sy ⊆ Sx := Finset.filter_subset_filter _
    (Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hyx) 1))
  have hcard_split : (Sx.card : ℝ) = (Sy.card : ℝ) + ((Sx \ Sy).card : ℝ) := by
    have hnat : Sx.card = Sy.card + (Sx \ Sy).card := by
      have := Finset.card_sdiff_add_card_eq_card hsub
      omega
    exact_mod_cast hnat
  have hSy_le : (Sy.card : ℝ) ≤ y + 1 := by
    have h1 : Sy.card ≤ ⌊y⌋₊ + 1 := by
      calc Sy.card ≤ (Finset.range (⌊y⌋₊ + 1)).card := Finset.card_filter_le _ _
        _ = ⌊y⌋₊ + 1 := Finset.card_range _
    have h2 : (Sy.card : ℝ) ≤ (⌊y⌋₊ : ℝ) + 1 := by exact_mod_cast h1
    linarith [Nat.floor_le (by linarith : 0 ≤ y)]
  have htail_le : ((Sx \ Sy).card : ℝ) * Real.log y ≤ Stage2DirichletAP.chebyshevThetaAP q a x := by
    unfold Stage2DirichletAP.chebyshevThetaAP
    rw [← Finset.sum_filter]
    calc ((Sx \ Sy).card : ℝ) * Real.log y
        = ∑ _n ∈ Sx \ Sy, Real.log y := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Sx \ Sy, Real.log (n : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Finset.mem_sdiff] at hn
          have hmem_x := Finset.mem_filter.mp hn.1
          have hnot_y : n ∉ Finset.range (⌊y⌋₊ + 1) := fun h =>
            hn.2 (Finset.mem_filter.mpr ⟨h, hmem_x.2⟩)
          have hgt : ⌊y⌋₊ + 1 ≤ n := by simpa [Finset.mem_range] using hnot_y
          have hny : y < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one y) (by exact_mod_cast hgt)
          exact Real.log_le_log (by linarith) hny.le
      _ ≤ ∑ n ∈ Sx, Real.log (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun n _ _ =>
            Real.log_natCast_nonneg n
  have htail_div : ((Sx \ Sy).card : ℝ) ≤ Stage2DirichletAP.chebyshevThetaAP q a x / Real.log y :=
    (le_div_iff₀ hlogy_pos).mpr htail_le
  change (Sx.card : ℝ) ≤ _
  linarith

/-- **PRIME NUMBER THEOREM IN ARITHMETIC PROGRESSIONS (`π(x; q, a) ~ x / (φ(q) log x)`, real variable, 0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a` with `Nat.Coprime a q`:
`Tendsto (fun x : ℝ => (primeCountAP q a x : ℝ) / (x / ((q.totient : ℝ) * Real.log x))) atTop (𝓝 1)`. -/
theorem pnt_primeCountAP_real_asymp {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    Tendsto
      (fun x : ℝ =>
        (Stage2DirichletAP.primeCountAP q a x : ℝ) / (x / ((q.totient : ℝ) * Real.log x)))
      atTop (𝓝 1) := by
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  set y : ℝ → ℝ := fun x => x / (Real.log x) ^ 2
  -- Auxiliary limits: `log x / x → 0`, `log (log x) / log x → 0`, and `log (y x) / log x → 1`
  have hlog_div_x : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    exact h.congr' (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _; rw [Real.rpow_one])
  have hloglog_div : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
    hlog_div_x.comp Real.tendsto_log_atTop
  have hlogy_div : Tendsto (fun x : ℝ => Real.log (y x) / Real.log x) atTop (𝓝 1) := by
    have h1 : Tendsto (fun x : ℝ => 1 - 2 * (Real.log (Real.log x) / Real.log x)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (hloglog_div.const_mul 2)
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
    have hLx_gt1 : 1 < Real.log x := by
      rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hx
    have hLx0 : 0 < Real.log x := zero_lt_one.trans hLx_gt1
    dsimp only [y]
    rw [Real.log_div hx0.ne' (pow_ne_zero 2 hLx0.ne'), Real.log_pow]
    push_cast
    field_simp [hLx0.ne']
  have hlog_div_logy : Tendsto (fun x : ℝ => Real.log x / Real.log (y x)) atTop (𝓝 1) := by
    have h := hlogy_div.inv₀ one_ne_zero
    rw [inv_one] at h
    exact h.congr fun x => by rw [inv_div]
  have hy_atTop : Tendsto y atTop atTop := by
    have hinv : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (𝓝 0) := by
      have hsq : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
        (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
      have h2 := hsq.mul hsq
      rw [mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hmul : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
        rw [← Real.rpow_add hx]; norm_num
      rw [div_mul_div_comm, ← sq, hmul]
    have hinv_pos : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hinv ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_pos (sq_pos_of_pos (Real.log_pos hx)) (by linarith)
    exact (tendsto_inv_nhdsGT_zero.comp hinv_pos).congr fun x => by
      dsimp only [Function.comp_apply, y]; rw [inv_div]
  -- Upper envelope `U x → 1`
  set U : ℝ → ℝ := fun x =>
    (q.totient : ℝ) * (1 / Real.log x + Real.log x / x) +
      (Stage2DirichletAP.chebyshevThetaAP q a x / (x / (q.totient : ℝ))) *
        (Real.log x / Real.log (y x))
  have hU_tendsto : Tendsto U atTop (𝓝 1) := by
    have hinv_log : Tendsto (fun x : ℝ => (1 : ℝ) / Real.log x) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).congr fun x => by
        dsimp only [Function.comp_apply]; rw [one_div]
    have hpart1 : Tendsto (fun x : ℝ => (q.totient : ℝ) * (1 / Real.log x + Real.log x / x))
        atTop (𝓝 0) := by
      have h := (hinv_log.add hlog_div_x).const_mul (q.totient : ℝ)
      rwa [add_zero, mul_zero] at h
    have hpart2 : Tendsto
        (fun x : ℝ => (Stage2DirichletAP.chebyshevThetaAP q a x / (x / (q.totient : ℝ))) *
          (Real.log x / Real.log (y x))) atTop (𝓝 1) := by
      have h := (pnt_thetaAP_asymp hcop).mul hlog_div_logy
      rwa [mul_one] at h
    have hsum := hpart1.add hpart2
    rwa [zero_add] at hsum
  -- Squeeze `π(x; q, a) / (x / (φ(q) log x))` between `θ(x; q, a) / (x / φ(q))` and `U x`!
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (pnt_thetaAP_asymp hcop) hU_tendsto ?_ ?_
  · -- Lower bound: eventually `θ(x; q, a) / (x / φ(q)) ≤ π(x; q, a) / (x / (φ(q) log x))`
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx2
    have hx0 : 0 < x := by linarith
    have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have h1 := chebyshevThetaAP_le_primeCountAP_mul_log q a (by linarith : 1 ≤ x)
    have hden1 : 0 < x / (q.totient : ℝ) := div_pos hx0 hphi_pos
    have hden2 : 0 < x / ((q.totient : ℝ) * Real.log x) := div_pos hx0 (mul_pos hphi_pos hLx_pos)
    rw [div_le_div_iff₀ hden1 hden2]
    have hlhs : Stage2DirichletAP.chebyshevThetaAP q a x * (x / ((q.totient : ℝ) * Real.log x)) =
        Stage2DirichletAP.chebyshevThetaAP q a x * (x / (q.totient : ℝ)) / Real.log x := by ring
    rw [hlhs, div_le_iff₀ hLx_pos]
    nlinarith
  · -- Upper bound: eventually `π(x; q, a) / (x / (φ(q) log x)) ≤ U x`
    filter_upwards [eventually_gt_atTop (Real.exp 1), hy_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
      with x hx hy1
    have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
    have hLx_gt1 : 1 < Real.log x := by
      rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hx
    have hLx_pos : 0 < Real.log x := zero_lt_one.trans hLx_gt1
    have hyx : y x ≤ x := by
      dsimp only [y]
      exact div_le_self hx0.le (by nlinarith)
    have hlogy_pos : 0 < Real.log (y x) := Real.log_pos hy1
    have hup := primeCountAP_le_add_chebyshevThetaAP_div_log q a hy1 hyx
    have hden : 0 < x / ((q.totient : ℝ) * Real.log x) := div_pos hx0 (mul_pos hphi_pos hLx_pos)
    rw [div_le_iff₀ hden]
    refine hup.trans_eq ?_
    dsimp only [U, y]
    field_simp [hx0.ne', hphi_pos.ne', hLx_pos.ne', hlogy_pos.ne']

/-- **UNCONDITIONAL PRIME NUMBER THEOREM IN ARITHMETIC PROGRESSIONS FOR `primeCountAP` (0 ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY `a : ℕ` with `Nat.Coprime a q`:
`Tendsto (fun n : ℕ => (primeCountAP q a n : ℝ) / ((n : ℝ) / ((q.totient : ℝ) * Real.log (n : ℝ)))) atTop (𝓝 1)`. -/
theorem pnt_primeCountAP_asymp {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    Tendsto
      (fun n : ℕ =>
        (Stage2DirichletAP.primeCountAP q a n : ℝ) /
          ((n : ℝ) / ((q.totient : ℝ) * Real.log (n : ℝ))))
      atTop (𝓝 1) :=
  (pnt_primeCountAP_real_asymp hcop).comp tendsto_natCast_atTop_atTop

end RHDirect.Stage7PNTInAP
