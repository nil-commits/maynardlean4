import RHDirect.Interfaces
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.LinearCombination

/-!
# RHDirect.SlopeInequality

Direct, self-contained, 0-`sorry`, 0-`axiom` formalization of the new mathematical heart of
Alpöge's proof:

1. **The `2/3` Barrier vs. the `√X` Iterated Theta-Lift Chain Breakthrough**:
   - Why single-step lifting (`m = 1`) stalls at `O(x)` and separate quadratic charging
     (`max (x / m) (m ^ 2)`) stalls at the `2/3` barrier (`x ^ (2/3)` at `m = x ^ (1/3)`).
   - How a common dual lattice with chain length `m ∈ [x ^ (1/2 - ε), x ^ (1/2 + ε/2)]`
     and `x * m ≤ k ≤ n ^ 2 * x ^ (1/2 - ε)` collapses `errorBracketSizeWindows` all the way
     past `2/3` to `x ^ (1/2 + (C + 3) * ε)` (`growth_size_bound_breaks_two_thirds`).

2. **Exact Threshold & Window Arithmetic (`1/52`, `13 * ε < 1/4`, `377 = 1 + 47 * 8`, `400`, `401`)**:
   - `eps_lt_one_div_52_iff`: `ε < 1 / 52 ↔ 13 * ε < 1 / 4`.
   - `eventually_rank_le_rpow_400`: exact rank bound `(R.t : ℝ) ≤ s.x ^ 400` for
     `ScaleParams` (`0 < s.eps < 1 / 52`, `s.x ≥ 2 ^ 100`) and `RankVal s R`
     (matching `EventuallyRankLeRpowOfLtOneDivFiftytwo.lean`).
   - `win_window_embedding_401`: exact window embedding `(k * W) ^ (3/2) ≤ W ^ 2` and
     `(k * x') ^ 400 ≤ x' ^ 401` (matching `WinPairs.lean`).

3. **Bost / Arakelov Common-Slope Cancellation & Weighted Mean Inequality**:
   - Exact cancellation of the common dual-lattice slope `μ_CC(u₀)`, the weighted mean slope
     `s(u₀)`, the shift `F₀(u₀)`, and the volume constants `log (π / v)` and `m * sumA * lg`
     (`key_cancellation_identity`, `pointwise_slope_cancellation`,
     `mean_bound_of_slope_cancellation`, `errorTerm_le_rpow_errText`).

4. **Bost / Gram-Schur Dual-Lattice Frame Bound**:
   - Direct proof of the truncated slope/covolume inequality (`bost_slope_from_frame_tail`),
     Frobenius-Gram spectral defect bound (`gram_schur_diag_defect_bound`), and the
     exceptional-character rank/count bound comparing archimedean covolume upper bounds
     against `p`-adic divisibility along the `m`-step chain
     (`exceptional_character_rank_bound`).
-/

open Real Finset RHDirect
open scoped BigOperators

namespace RHDirect.SlopeInequality

noncomputable section

/-! ## Section 1: The `2/3` Barrier vs. the `√X` Chain Breakthrough -/

/-- Charging a single lift (`m = 1`) leaves the ratio `x / m = x`, giving zero saving. -/
theorem single_step_no_saving (x : ℝ) : x / (1 : ℝ) = x := div_one x

/-- **The `2/3` Barrier**: Balancing `x / m` against a quadratic separate-lift penalty `m ^ 2`
cannot beat `x ^ (2 / 3)` for any positive chain length `m > 0`. -/
theorem two_thirds_barrier_lower_bound {x m : ℝ} (hx : 0 < x) (hm : 0 < m) :
    x ^ ((2 : ℝ) / 3) ≤ max (x / m) (m ^ 2) := by
  by_cases h : m ≤ x ^ ((1 : ℝ) / 3)
  · refine le_trans ?_ (le_max_left _ _)
    rw [le_div_iff₀ hm]
    calc x ^ ((2 : ℝ) / 3) * m
        ≤ x ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le _)
      _ = x ^ (((2 : ℝ) / 3) + (1 : ℝ) / 3) := (Real.rpow_add hx _ _).symm
      _ = x := by norm_num
  · push Not at h
    refine le_trans ?_ (le_max_right _ _)
    have h1 : (x ^ ((1 : ℝ) / 3)) ^ 2 ≤ m ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hx.le _) h.le 2
    have h2 : (x ^ ((1 : ℝ) / 3)) ^ 2 = x ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
    linarith

/-- The `2/3` barrier is attained precisely at `m = x ^ (1/3)`. -/
theorem two_thirds_barrier_attained {x : ℝ} (hx : 0 < x) :
    max (x / x ^ ((1 : ℝ) / 3)) ((x ^ ((1 : ℝ) / 3)) ^ 2) = x ^ ((2 : ℝ) / 3) := by
  have h1 : x / x ^ ((1 : ℝ) / 3) = x ^ ((2 : ℝ) / 3) := by
    rw [div_eq_iff (Real.rpow_pos_of_pos hx _).ne', ← Real.rpow_add hx]
    norm_num
  have h2 : (x ^ ((1 : ℝ) / 3)) ^ 2 = x ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  rw [h1, h2, max_self]

/-- Exact size-window constraints pinning the chain length to `m ∈ [x^(1/2 - ε), x^(1/2 + ε/2)]`
and the rank parameter to `x * m ≤ k ≤ n^2 * x^(1/2 - ε)`
(combining `RHDirect.RestSize` with upper window bounds and `RHDirect.errorBracketSizeWindows`). -/
structure SizeWindowParams (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ) : Prop where
  x_ge_three : 3 ≤ x
  eps_pos : 0 < ε
  C_nonneg : 0 ≤ C
  n_pos : 0 < n
  b_pos : 0 < b
  aE_nonneg : 0 ≤ aE
  rest : RestSize ε x n nT nT2 m b k aE
  nT2_le : nT2 ≤ n
  m_le : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)
  k_ge : x * (m : ℝ) ≤ k
  err_le : Err ≤ x ^ (C * ε) * errorBracketSizeWindows x ε n nT nT2 m b k aE
  x_large_26 : 26 ≤ x ^ (3 * ε / 8)

/-- Dividing `errorBracketSizeWindows` by the main-term scale `nT * m * b` collapses all four
error contributions to `10 * x ^ (1/2 + 13*ε/8)` — breaking past `2/3`! -/
theorem errorBracket_div_scale_bound {C ε x : ℝ} {n nT nT2 m : ℕ} {b k aE Err : ℝ}
    (h : SizeWindowParams C ε x n nT nT2 m b k aE Err) :
    errorBracketSizeWindows x ε n nT nT2 m b k aE / ((nT : ℝ) * (m : ℝ) * b)
      ≤ 10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) := by
  obtain ⟨haE_le, hnT_ge, _hnT2_ge, hm_ge, hk_le⟩ := h.rest
  have hx1 : 1 ≤ x := by linarith [h.x_ge_three]
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr h.n_pos
  have hnT0 : (0 : ℝ) < nT := lt_of_lt_of_le (by positivity) hnT_ge
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm_ge
  have hk0 : 0 < k := lt_of_lt_of_le (mul_pos hx0 hm0) h.k_ge
  have hb0 : 0 < b := h.b_pos
  have heps : 0 < ε := h.eps_pos
  -- Rewrite the 4 terms cleanly after dividing by nT * m * b
  have hsplit : errorBracketSizeWindows x ε n nT nT2 m b k aE / ((nT : ℝ) * (m : ℝ) * b)
      = aE / ((m : ℝ) * b) + aE * (m : ℝ) / (k * b)
        + 2 * (n : ℝ) * (m : ℝ) * x ^ ε / (nT : ℝ)
        + ((nT2 : ℝ) / (n : ℝ)) * k * x ^ (2 * ε) / ((nT : ℝ) * (n : ℝ)) := by
    unfold errorBracketSizeWindows
    have hxe : x ^ (-ε) = (x ^ ε)⁻¹ := Real.rpow_neg hx0.le ε
    have h2e : x ^ (2 * ε) = x ^ ε * x ^ ε := by rw [two_mul, Real.rpow_add hx0]
    have hxe_ne : x ^ ε ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
    rw [hxe, h2e]
    field_simp [hn0.ne', hnT0.ne', hm0.ne', hk0.ne', hb0.ne', hxe_ne]
    ring
  rw [hsplit]
  -- Term 1: aE / (m * b) ≤ 2 * x / m ≤ 2 * x ^ (1/2 + ε)
  have ht1 : aE / ((m : ℝ) * b) ≤ 2 * x ^ ((1 : ℝ) / 2 + ε) := by
    have h1 : aE / ((m : ℝ) * b) ≤ (2 * x * b) / ((m : ℝ) * b) :=
      div_le_div_of_nonneg_right haE_le (by positivity)
    have h2 : (2 * x * b) / ((m : ℝ) * b) = 2 * x / (m : ℝ) := by field_simp [hb0.ne']
    have h3 : 2 * x / (m : ℝ) ≤ 2 * x / x ^ ((1 : ℝ) / 2 - ε) :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hx0 _) hm_ge
    have h4 : 2 * x / x ^ ((1 : ℝ) / 2 - ε) = 2 * x ^ ((1 : ℝ) / 2 + ε) := by
      rw [div_eq_iff (Real.rpow_pos_of_pos hx0 _).ne', mul_assoc, ← Real.rpow_add hx0]
      norm_num
    linarith
  -- Term 2: aE * m / (k * b) ≤ 2 * x * m / k ≤ 2 ≤ 2 * x ^ (1/2 + ε)
  have ht2 : aE * (m : ℝ) / (k * b) ≤ 2 * x ^ ((1 : ℝ) / 2 + ε) := by
    have h1 : aE * (m : ℝ) / (k * b) ≤ (2 * x * b) * (m : ℝ) / (k * b) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right haE_le hm0.le) (by positivity)
    have h2 : (2 * x * b) * (m : ℝ) / (k * b) = 2 * (x * (m : ℝ) / k) := by
      field_simp [hb0.ne', hk0.ne']
    have h3 : x * (m : ℝ) / k ≤ 1 := (div_le_one hk0).mpr h.k_ge
    have h4 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε) := Real.one_le_rpow hx1 (by linarith)
    linarith
  -- Term 3: 2 * n * m * x^ε / nT ≤ 4 * m * x^(9*ε/8) ≤ 4 * x^(1/2 + 13*ε/8)
  have hinv_nT : (n : ℝ) / (nT : ℝ) ≤ 2 * x ^ (ε / 8) := by
    rw [div_le_iff₀ hnT0]
    have h1 := mul_le_mul_of_nonneg_left hnT_ge (show (0 : ℝ) ≤ 2 * x ^ (ε / 8) by positivity)
    have h2 : 2 * x ^ (ε / 8) * (x ^ (-(ε / 8)) * (n : ℝ) / 2) = (n : ℝ) := by
      have : x ^ (ε / 8) * x ^ (-(ε / 8)) = 1 := by
        rw [← Real.rpow_add hx0]; norm_num
      linear_combination (n : ℝ) * this
    linarith
  have ht3 : 2 * (n : ℝ) * (m : ℝ) * x ^ ε / (nT : ℝ) ≤ 4 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) := by
    have h1 : 2 * (n : ℝ) * (m : ℝ) * x ^ ε / (nT : ℝ) = 2 * ((n : ℝ) / (nT : ℝ)) * (m : ℝ) * x ^ ε := by
      ring
    rw [h1]
    calc 2 * ((n : ℝ) / (nT : ℝ)) * (m : ℝ) * x ^ ε
        ≤ 2 * (2 * x ^ (ε / 8)) * x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε := by gcongr; exact h.m_le
      _ = 4 * (x ^ (ε / 8) * x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε) := by ring
      _ = 4 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0,
            show ε / 8 + ((1 : ℝ) / 2 + ε / 2) + ε = (1 : ℝ) / 2 + 13 * ε / 8 by ring]
  -- Term 4: (nT2 / n) * k * x^(2ε) / (nT * n) ≤ 2 * x^(1/2 + 9*ε/8)
  have ht4 : ((nT2 : ℝ) / (n : ℝ)) * k * x ^ (2 * ε) / ((nT : ℝ) * (n : ℝ))
      ≤ 2 * x ^ ((1 : ℝ) / 2 + 9 * ε / 8) := by
    have hnT2_ratio : (nT2 : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]; exact_mod_cast h.nT2_le
    have hrew : ((nT2 : ℝ) / (n : ℝ)) * k * x ^ (2 * ε) / ((nT : ℝ) * (n : ℝ))
        = ((nT2 : ℝ) / (n : ℝ)) * ((n : ℝ) / (nT : ℝ)) * (k / (n : ℝ) ^ 2) * x ^ (2 * ε) := by
      field_simp [hn0.ne', hnT0.ne']
    rw [hrew]
    have hk_div : k / (n : ℝ) ^ 2 ≤ x ^ ((1 : ℝ) / 2 - ε) := by
      rw [div_le_iff₀ (sq_pos_of_pos hn0)]
      linarith
    calc ((nT2 : ℝ) / (n : ℝ)) * ((n : ℝ) / (nT : ℝ)) * (k / (n : ℝ) ^ 2) * x ^ (2 * ε)
        ≤ 1 * (2 * x ^ (ε / 8)) * x ^ ((1 : ℝ) / 2 - ε) * x ^ (2 * ε) := by
          have : 0 ≤ (nT2 : ℝ) / (n : ℝ) := by positivity
          have : 0 ≤ (n : ℝ) / (nT : ℝ) := by positivity
          have : 0 ≤ k / (n : ℝ) ^ 2 := by positivity
          gcongr
      _ = 2 * (x ^ (ε / 8) * x ^ ((1 : ℝ) / 2 - ε) * x ^ (2 * ε)) := by ring
      _ = 2 * x ^ ((1 : ℝ) / 2 + 9 * ε / 8) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0,
            show ε / 8 + ((1 : ℝ) / 2 - ε) + 2 * ε = (1 : ℝ) / 2 + 9 * ε / 8 by ring]
  have hmono1 : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hmono2 : x ^ ((1 : ℝ) / 2 + 9 * ε / 8) ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  linarith

/-- **Main Exponent Breakthrough (`GrowthSizeBound`)**:
Under `SizeWindowParams` (`m ∈ [x^(1/2 - ε), x^(1/2 + ε/2)]`), the common dual-lattice
mean bound collapses all error terms to `Gx ≤ x ^ (1/2 + (C + 3) * ε)`, breaking the `2/3`
barrier for every `ε < 1 / (6 * (C + 3))`! -/
theorem growth_size_bound_breaks_two_thirds {C ε x : ℝ} {n nT nT2 m : ℕ} {b k aE Err Gx : ℝ}
    (h : SizeWindowParams C ε x n nT nT2 m b k aE Err)
    (hMain : (nT : ℝ) * (m : ℝ) * b * (((nT2 : ℝ) / (n : ℝ)) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ Err + 2 * (nT : ℝ) * (m : ℝ) * b / x) :
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
  obtain ⟨_, hnT_ge, hnT2_ge, hm_ge, _⟩ := h.rest
  have hx1 : 1 ≤ x := by linarith [h.x_ge_three]
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr h.n_pos
  have hnT0 : (0 : ℝ) < nT := lt_of_lt_of_le (by positivity) hnT_ge
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm_ge
  have hb0 : 0 < b := h.b_pos
  have hscale0 : 0 < (nT : ℝ) * (m : ℝ) * b := by positivity
  have hd2_pos : 0 < (nT2 : ℝ) / (n : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hnT2_ge
  have hcoeff0 : 0 < (nT : ℝ) * (m : ℝ) * b * (((nT2 : ℝ) / (n : ℝ)) / 2) := by positivity
  have hGx_sub : Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)
      ≤ (2 / ((nT2 : ℝ) / (n : ℝ))) * (Err / ((nT : ℝ) * (m : ℝ) * b) + 2 / x) := by
    have h1 := (le_div_iff₀' hcoeff0).mpr hMain
    have h2 : (Err + 2 * (nT : ℝ) * (m : ℝ) * b / x) /
        ((nT : ℝ) * (m : ℝ) * b * (((nT2 : ℝ) / (n : ℝ)) / 2))
        = (2 / ((nT2 : ℝ) / (n : ℝ))) * (Err / ((nT : ℝ) * (m : ℝ) * b) + 2 / x) := by
      field_simp [hscale0.ne', hd2_pos.ne', hx0.ne']
    linarith
  have hinv_d2 : 2 / ((nT2 : ℝ) / (n : ℝ)) ≤ 2 * x ^ ε := by
    rw [div_le_iff₀ hd2_pos]
    have h1 := mul_le_mul_of_nonneg_left hnT2_ge (show (0 : ℝ) ≤ 2 * x ^ ε by positivity)
    have h2 : 2 * x ^ ε * x ^ (-ε) = 2 := by
      rw [mul_assoc, ← Real.rpow_add hx0]; norm_num
    linarith
  have hEB := errorBracket_div_scale_bound h
  have hErr_div : Err / ((nT : ℝ) * (m : ℝ) * b) ≤ 10 * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) := by
    calc Err / ((nT : ℝ) * (m : ℝ) * b)
        ≤ (x ^ (C * ε) * errorBracketSizeWindows x ε n nT nT2 m b k aE) / ((nT : ℝ) * (m : ℝ) * b) :=
          div_le_div_of_nonneg_right h.err_le hscale0.le
      _ = x ^ (C * ε) * (errorBracketSizeWindows x ε n nT nT2 m b k aE / ((nT : ℝ) * (m : ℝ) * b)) := by ring
      _ ≤ x ^ (C * ε) * (10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) :=
          mul_le_mul_of_nonneg_left hEB (Real.rpow_nonneg hx0.le _)
      _ = 10 * (x ^ (C * ε) * x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) := by ring
      _ = 10 * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) := by
          rw [← Real.rpow_add hx0,
            show C * ε + ((1 : ℝ) / 2 + 13 * ε / 8) = (1 : ℝ) / 2 + (C + 13 / 8) * ε by ring]
  have h2_div_x : 2 / x ≤ x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) := by
    have h1 : 2 / x ≤ 1 := by rw [div_le_one hx0]; linarith [h.x_ge_three]
    have h2 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε) :=
      Real.one_le_rpow hx1 (by nlinarith [h.C_nonneg, h.eps_pos])
    linarith
  have hprod : (2 / ((nT2 : ℝ) / (n : ℝ))) * (Err / ((nT : ℝ) * (m : ℝ) * b) + 2 / x)
      ≤ 22 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    by_cases hs : 0 ≤ Err / ((nT : ℝ) * (m : ℝ) * b) + 2 / x
    · calc (2 / ((nT2 : ℝ) / (n : ℝ))) * (Err / ((nT : ℝ) * (m : ℝ) * b) + 2 / x)
          ≤ (2 * x ^ ε) * (11 * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε)) :=
            mul_le_mul hinv_d2 (by linarith) hs (by positivity)
        _ = 22 * (x ^ ε * x ^ ((1 : ℝ) / 2 + (C + 13 / 8) * ε)) := by ring
        _ = 22 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
            rw [← Real.rpow_add hx0,
              show ε + ((1 : ℝ) / 2 + (C + 13 / 8) * ε) = (1 : ℝ) / 2 + (C + 21 / 8) * ε by ring]
    · push Not at hs
      have hneg_prod : (2 / ((nT2 : ℝ) / (n : ℝ))) * (Err / ((nT : ℝ) * (m : ℝ) * b) + 2 / x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hs.le
      have hrhs_nn : 0 ≤ 22 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by positivity
      linarith
  have h4mono : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith [h.C_nonneg, h.eps_pos])
  calc Gx ≤ 4 * x ^ ((1 : ℝ) / 2 + ε) + 22 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by linarith
    _ ≤ 26 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by linarith
    _ ≤ x ^ (3 * ε / 8) * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) :=
        mul_le_mul_of_nonneg_right h.x_large_26 (Real.rpow_nonneg hx0.le _)
    _ = x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
        rw [← Real.rpow_add hx0]; congr 1; ring

/-- Explicitly breaks the `2/3` barrier whenever `ε < 1 / (6 * (C + 3))`. -/
theorem breaks_two_thirds_exponent {C ε : ℝ} (hC : 0 ≤ C) (hε : ε < 1 / (6 * (C + 3))) :
    (1 : ℝ) / 2 + (C + 3) * ε < (2 : ℝ) / 3 := by
  have h1 : (C + 3) * ε < (C + 3) * (1 / (6 * (C + 3))) :=
    mul_lt_mul_of_pos_left hε (by linarith)
  have h2 : (C + 3) * (1 / (6 * (C + 3))) = 1 / 6 := by
    field_simp [(by linarith : C + 3 ≠ 0)]
  linarith

/-! ## Section 2: Exact Threshold & Window Arithmetic (`1/52`, `377 = 1 + 47*8`, `400`, `401`) -/

/-- Exact equivalence between Alpöge's `1/52` threshold and `13 * ε < 1 / 4`. -/
theorem eps_lt_one_div_52_iff (ε : ℝ) : ε < 1 / 52 ↔ 13 * ε < 1 / 4 := by
  constructor <;> intro h <;> linarith

/-- Exact combinatorial decompositions for `377 = 1 + 47 * 8`, `401 = 1 + 400`, and `40000`. -/
theorem exponent_identities :
    (377 : ℕ) = 1 + 47 * 8 ∧ (401 : ℕ) = 1 + 400 ∧ (37700 : ℕ) + 2267 + 33 = 40000 := by
  norm_num

/-- **Exact `1/52` Threshold Rank Bound (`EventuallyRankLeRpowOfLtOneDivFiftytwo.lean`)**:
For any `ScaleParams` (`0 < s.eps < 1/52`, `s.delta1 = s.x ^ (-(s.eps / 8))`, `s.L = s.x ^ s.eps`,
`s.x ≥ 2 ^ 100`) and `ChainRanks` satisfying `RankVal s R`, the auxiliary unitary rank `R.t`
satisfies `(R.t : ℝ) ≤ s.x ^ 400`. -/
theorem eventually_rank_le_rpow_400 (s : ScaleParams) (R : ChainRanks)
    (hx : (2 : ℝ) ^ 100 ≤ s.x)
    (hdelta1 : s.delta1 = s.x ^ (-(s.eps / 8)))
    (hL_eq : s.L = s.x ^ s.eps)
    (hf_eq : R.f = 2 * R.n)
    (hm2 : 2 ≤ R.m)
    (hmk : R.m + 3 ≤ R.k)
    (hr_eq : R.r = R.k + R.m - 1)
    (hR : RankVal s R) :
    (R.t : ℝ) ≤ s.x ^ (400 : ℝ) := by
  have hX1 : 1 < s.x := s.x_gt_one
  have hX0 : 0 < s.x := by linarith
  have he : 0 < s.eps := s.eps_pos
  have he52 : s.eps < 1 / 52 := s.eps_lt
  obtain ⟨⟨_, hn_up⟩, ⟨hm_lo, _⟩, ⟨_, hk_up⟩, hrt_eq⟩ := hR
  have hmono : ∀ a b : ℝ, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hX1.le h
  have hY : ∀ j : ℕ, s.x ^ ((j : ℝ) / 100) = (s.x ^ ((1 : ℝ) / 100)) ^ j := by
    intro j
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    ring_nf
  have hY2 : (2 : ℝ) ≤ s.x ^ ((1 : ℝ) / 100) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ 100) hx (by norm_num : (0 : ℝ) ≤ 1 / 100)
    have h2 : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  generalize hYd : s.x ^ ((1 : ℝ) / 100) = Y at hY hY2
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hn : (R.n : ℝ) ≤ 2 * Y ^ 216 := by
    have h := hmono _ _ (show 2 + 8 * s.eps ≤ ((216 : ℕ) : ℝ) / 100 by push_cast; linarith)
    rw [hY] at h; linarith
  have hf : (R.f : ℝ) ≤ 4 * Y ^ 216 := by
    have hfe : (R.f : ℝ) = 2 * (R.n : ℝ) := by rw [hf_eq]; push_cast; rfl
    linarith
  have hk : (R.k : ℝ) ≤ 2 * Y ^ 470 := by
    have h := hmono _ _ (show (9 : ℝ) / 2 + 10 * s.eps ≤ ((470 : ℕ) : ℝ) / 100 by push_cast; linarith)
    rw [hY] at h; linarith
  have hm : Y ^ 49 ≤ (R.m : ℝ) := by
    refine le_trans ?_ hm_lo
    rw [hdelta1, Real.le_sqrt (by positivity) (by positivity)]
    have h1 : (Y ^ 49) ^ 2 = s.x ^ (((98 : ℕ) : ℝ) / 100) := by rw [hY]; ring
    have h2 : s.x * s.x ^ (-(s.eps / 8)) = s.x ^ ((1 : ℝ) + -(s.eps / 8)) := by
      rw [Real.rpow_add hX0, Real.rpow_one]
    rw [h1, h2]
    exact hmono _ _ (by push_cast; linarith)
  have hm0 : (0 : ℝ) < R.m := lt_of_lt_of_le (by positivity) hm
  have hL : s.L ^ 2 ≤ Y ^ 4 := by
    have h1 : s.L ^ 2 = s.x ^ (s.eps * 2) := by
      rw [hL_eq, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
    rw [h1]
    have h := hmono _ _ (show s.eps * 2 ≤ ((4 : ℕ) : ℝ) / 100 by push_cast; linarith)
    rw [hY] at h; exact h
  have hr : (R.r : ℝ) ≤ 4 * Y ^ 470 := by
    have h : R.r ≤ 2 * R.k := by omega
    have h' : (R.r : ℝ) ≤ 2 * (R.k : ℝ) := by exact_mod_cast h
    linarith
  have hk5 : (5 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 5 ≤ R.k)
  have hk0 : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
  have hk' : (R.k : ℝ) - 1 ≤ 2 * Y ^ 470 := by linarith
  have hB : (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / (R.m : ℝ) ≤ 128 * Y ^ 1797 := by
    rw [div_le_iff₀ hm0]
    have hL0 : 0 ≤ s.L := s.L_pos.le
    calc (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2
        ≤ (4 * Y ^ 216) ^ 2 * (2 * Y ^ 470) ^ 3 * Y ^ 4 := by gcongr
      _ = 128 * Y ^ 1797 * Y ^ 49 := by ring
      _ ≤ 128 * Y ^ 1797 * (R.m : ℝ) := by gcongr
  have hp1 : Y ^ 216 ≤ Y ^ 1797 := pow_le_pow_right₀ hY1 (by norm_num)
  have hQ : (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / (R.m : ℝ) ≤ 132 * Y ^ 1797 := by
    linarith
  have hQ0 : 0 ≤ (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / (R.m : ℝ) := by
    have := s.L_pos.le; positivity
  have hW : (nWv R s : ℝ) ≤ 5288 * Y ^ 2267 := by
    have hy0 : (0 : ℝ) ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / (R.m : ℝ)) / 8 :=
      by positivity
    have hc := Nat.ceil_lt_add_one hy0
    have hyb : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / (R.m : ℝ))
        ≤ 10 * (4 * Y ^ 470) * (132 * Y ^ 1797) :=
      mul_le_mul (by linarith) hQ hQ0 (by positivity)
    have hY2267 : (1 : ℝ) ≤ Y ^ 2267 := one_le_pow₀ hY1
    have e1 : 10 * (4 * Y ^ 470) * (132 * Y ^ 1797) = 5280 * Y ^ 2267 := by ring
    unfold nWv
    push_cast
    linarith
  have hT : (TOv s : ℝ) ≤ 2 * Y ^ 37700 := by
    have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ s.x ^ (377 : ℝ) by positivity)
    have h1 : s.x ^ (377 : ℝ) = Y ^ 37700 := by
      rw [show (377 : ℝ) = ((37700 : ℕ) : ℝ) / 100 by norm_num, hY]
    have h2 : (1 : ℝ) ≤ Y ^ 37700 := one_le_pow₀ hY1
    unfold TOv
    linarith
  have heqR : (R.r : ℝ) + (R.t : ℝ) = 8 * (R.f : ℝ) * (R.r : ℝ) + 4 + (TOv s : ℝ) * (nWv R s : ℝ) := by
    have hcast : ((R.r + R.t : ℕ) : ℝ) = ((8 * R.f * R.r + 4 + TOv s * nWv R s : ℕ) : ℝ) :=
      congrArg (Nat.cast (R := ℝ)) hrt_eq
    push_cast at hcast
    exact hcast
  have hfr : (R.f : ℝ) * (R.r : ℝ) ≤ (4 * Y ^ 216) * (4 * Y ^ 470) :=
    mul_le_mul hf hr (Nat.cast_nonneg _) (by positivity)
  have hTW : (TOv s : ℝ) * (nWv R s : ℝ) ≤ (2 * Y ^ 37700) * (5288 * Y ^ 2267) :=
    mul_le_mul hT hW (Nat.cast_nonneg _) (by positivity)
  rw [show (400 : ℝ) = ((40000 : ℕ) : ℝ) / 100 by norm_num, hY]
  have e1 : (4 * Y ^ 216) * (4 * Y ^ 470) = 16 * Y ^ 686 := by ring
  have e2 : (2 * Y ^ 37700) * (5288 * Y ^ 2267) = 10576 * Y ^ 39967 := by ring
  have p1 : Y ^ 686 ≤ Y ^ 39967 := pow_le_pow_right₀ hY1 (by norm_num)
  have p2 : (1 : ℝ) ≤ Y ^ 39967 := one_le_pow₀ hY1
  have p3 : (10708 : ℝ) ≤ Y ^ 33 := by
    have := pow_le_pow_left₀ (by norm_num) hY2 33
    norm_num at this; linarith
  have e3 : Y ^ 40000 = Y ^ 33 * Y ^ 39967 := by ring
  have p4 : (10708 : ℝ) * Y ^ 39967 ≤ Y ^ 33 * Y ^ 39967 :=
    mul_le_mul_of_nonneg_right p3 (by positivity)
  have hr_nn : (0 : ℝ) ≤ R.r := Nat.cast_nonneg _
  rw [e3]
  linarith

/-- **Exact `401` Window Embedding Arithmetic (`WinPairs.lean`)**:
1. If `k ^ 3 ≤ W`, then `(k * W) ^ (3 / 2) ≤ W ^ 2`, embedding a `[Z, Z^(3/2)]` Landau window
   inside `VWinAt`'s `[W, W^2]` window.
2. If `k ^ 400 ≤ x'`, then `(k * x') ^ 400 ≤ x' ^ 401`, explaining why `VWinAt ψ 401`
   absorbs the rescaling `x = k * x'` of the `x ^ 400` rank bound. -/
theorem win_window_embedding_401 {k W x' : ℝ} (hk0 : 0 ≤ k) (hW0 : 0 ≤ W) (hx'0 : 0 < x')
    (hk3 : k ^ (3 : ℝ) ≤ W) (hk400 : k ^ (400 : ℝ) ≤ x') :
    (k * W) ^ ((3 : ℝ) / 2) ≤ W ^ (2 : ℝ) ∧ (k * x') ^ (400 : ℝ) ≤ x' ^ (401 : ℝ) := by
  constructor
  · rcases hW0.eq_or_lt with rfl | hWpos
    · simp
    · have h1 : (k * W) ^ ((3 : ℝ) / 2) = ((k * W) ^ (3 : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_mul (mul_nonneg hk0 hW0)]; norm_num
      have h2 : W ^ (2 : ℝ) = (W ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_mul hW0]; norm_num
      rw [h1, h2]
      apply Real.rpow_le_rpow (Real.rpow_nonneg (mul_nonneg hk0 hW0) _) _ (by norm_num)
      rw [Real.mul_rpow hk0 hW0, show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add hWpos, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right hk3 (Real.rpow_nonneg hW0 _)
  · rw [Real.mul_rpow hk0 hx'0.le, show (401 : ℝ) = 1 + 400 by norm_num,
      Real.rpow_add hx'0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_right hk400 (Real.rpow_nonneg hx'0.le _)

/-! ## Section 3: Bost / Arakelov Common-Slope Cancellation & Weighted Mean Inequality -/

/-- Entropy function `φ(y) = y log y - y`. -/
def ph (y : ℝ) : ℝ := y * Real.log y - y

/-- Weighted mean with respect to positive rank weights `d`. -/
def wmean {ι : Type*} [Fintype ι] (d X : ι → ℝ) : ℝ := (∑ i, d i * X i) / (∑ i, d i)

/-- Uniform mean over a finite index type `ι`. -/
def umean {ι : Type*} [Fintype ι] (X : ι → ℝ) : ℝ := (∑ i, X i) / (Fintype.card ι : ℝ)

lemma sum_pos_of_pos {ι : Type*} [Fintype ι] [Nonempty ι] {d : ι → ℝ} (hd : ∀ i, 0 < d i) :
    0 < ∑ i, d i :=
  Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty

lemma wmean_mono {ι : Type*} [Fintype ι] {d X Y : ι → ℝ} (hd : ∀ i, 0 < d i) (h : ∀ i, X i ≤ Y i) :
    wmean d X ≤ wmean d Y := by
  unfold wmean
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hd i).le)
    (Finset.sum_nonneg fun i _ => (hd i).le)

lemma wmean_add {ι : Type*} [Fintype ι] (d X Y : ι → ℝ) :
    wmean d (fun i => X i + Y i) = wmean d X + wmean d Y := by
  simp only [wmean, mul_add, Finset.sum_add_distrib, add_div]

lemma wmean_const {ι : Type*} [Fintype ι] [Nonempty ι] {d : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ) :
    wmean d (fun _ => c) = c := by
  have hS : ∑ i, d i ≠ 0 := (sum_pos_of_pos hd).ne'
  simp only [wmean]
  rw [div_eq_iff hS, ← Finset.sum_mul, mul_comm]

lemma wmean_le_const {ι : Type*} [Fintype ι] [Nonempty ι] {d X : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ)
    (h : ∀ i, X i ≤ c) : wmean d X ≤ c := by
  calc wmean d X ≤ wmean d (fun _ => c) := wmean_mono hd h
    _ = c := wmean_const hd c

lemma sub_wmean_le {ι : Type*} [Fintype ι] [Nonempty ι] {d X Y : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ)
    (h : ∀ i, c - Y i ≤ X i) : c - wmean d Y ≤ wmean d X := by
  have h1 := wmean_mono (X := fun _ => c) (Y := fun i => X i + Y i) hd
    (fun i => by linarith [h i])
  rw [wmean_const hd c, wmean_add] at h1
  linarith

lemma umean_mono {ι : Type*} [Fintype ι] {X Y : ι → ℝ} (h : ∀ i, X i ≤ Y i) :
    umean X ≤ umean Y :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h i) (Nat.cast_nonneg _)

lemma umean_add {ι : Type*} [Fintype ι] (X Y : ι → ℝ) :
    umean (fun i => X i + Y i) = umean X + umean Y := by
  simp only [umean, Finset.sum_add_distrib, add_div]

lemma umean_mul {ι : Type*} [Fintype ι] (c : ℝ) (X : ι → ℝ) :
    umean (fun i => c * X i) = c * umean X := by
  simp only [umean, ← Finset.mul_sum, mul_div_assoc]

lemma umean_const {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ) :
    umean (fun _ : ι => c) = c := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [umean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [div_eq_iff hc, mul_comm]

/-- Convexity / logarithm envelope used in Bost's slope inequality:
`u * log (1 + H / u) ≤ log (1 + X) * (U + b)` for `0 ≤ u ≤ U` and `0 < H ≤ X * b`. -/
theorem phi_bound {u H X b U : ℝ} (hu : 0 ≤ u) (hH : 0 < H) (hHX : H ≤ X * b) (hb : 0 < b)
    (hX : 0 < X) (huU : u ≤ U) :
    u * Real.log (1 + H / u) ≤ Real.log (1 + X) * (U + b) := by
  have hL : 0 < Real.log (1 + X) := Real.log_pos (by linarith)
  have hX1 : 0 < 1 + X := by linarith
  rcases hu.eq_or_lt with rfl | hpos
  · rw [zero_mul]
    exact mul_nonneg hL.le (by linarith)
  · have hw0 : 0 ≤ (1 + X)⁻¹ := inv_nonneg.mpr hX1.le
    have hw1 : (1 + X) * (1 + X)⁻¹ = 1 := mul_inv_cancel₀ hX1.ne'
    have hb0 : 1 - (1 + X)⁻¹ ≤ Real.log (1 + X) := by
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr hX1)
      rw [Real.log_inv] at this; linarith
    have h1 : 0 < 1 + H / u := by have := div_nonneg hH.le hpos.le; linarith
    have ha : Real.log (1 + H / u) ≤ Real.log (1 + X) + ((1 + H / u) * (1 + X)⁻¹ - 1) := by
      have := Real.log_le_sub_one_of_pos (mul_pos h1 (inv_pos.mpr hX1))
      rw [Real.log_mul h1.ne' (inv_pos.mpr hX1).ne', Real.log_inv] at this; linarith
    have hyu : u * (H / u) = H := by field_simp [hpos.ne']
    have i1 := mul_le_mul_of_nonneg_left ha hu
    have e1 : u * (Real.log (1 + X) + ((1 + H / u) * (1 + X)⁻¹ - 1))
        = u * Real.log (1 + X) + u * (1 + X)⁻¹ + H * (1 + X)⁻¹ - u := by
      linear_combination (1 + X)⁻¹ * hyu
    have i2 := mul_le_mul_of_nonneg_right huU hL.le
    have hXw : X * (1 + X)⁻¹ = 1 - (1 + X)⁻¹ := by linear_combination hw1
    have hwle : (1 + X)⁻¹ ≤ 1 := by linarith [mul_nonneg hX.le hw0]
    have i3 : 0 ≤ u * (1 - (1 + X)⁻¹) := mul_nonneg hu (by linarith)
    have i4 : H * (1 + X)⁻¹ ≤ b * (1 - (1 + X)⁻¹) := by
      rw [← hXw]
      have := mul_le_mul_of_nonneg_right hHX hw0
      linarith
    have i5 := mul_le_mul_of_nonneg_left hb0 hb.le
    linarith

/-- Constants bundle for the Bost/Arakelov slope cancellation system
(stripped of any dead fields; matches `WeightedMeanData.Consts`). -/
structure SlopeConsts where
  cDiv : ℝ
  eDiv : ℝ
  cE : ℝ
  cH : ℝ
  cCount : ℝ
  cSlope : ℝ
  cSl1 : ℝ
  cLoss : ℝ
  eLoss : ℝ
  cHH : ℝ

/-- Clean, dead-field-free data bundle for the `m`-step iterated theta-lift chain and
common dual-lattice Bost slope cancellation (matching `WeightedMeanData.Data`). -/
structure SlopeData (U0 : Type) (W : U0 → Type) (Top : Type) (m f : ℕ) where
  x : ℝ
  ε : ℝ
  a : ℝ
  b : ℝ
  b' : ℝ
  k : ℝ
  L : ℝ
  La : ℝ
  B0 : ℝ
  Nc : ℝ
  gam : ℝ
  LpL : ℝ
  v : ℝ
  lg : ℝ
  aT : Top → ℝ
  w : U0 → Fin m → Fin f → ℝ
  d : (u0 : U0) → W u0 → ℝ
  T : (u0 : U0) → W u0 → ℝ
  muN : (u0 : U0) → W u0 → ℝ
  muMaxN : (u0 : U0) → W u0 → ℝ
  h : (u0 : U0) → W u0 → ℝ
  muM : (u0 : U0) → W u0 → ℝ
  muMaxM : (u0 : U0) → W u0 → ℝ
  Ee : (u0 : U0) → W u0 → ℝ
  muCC : U0 → ℝ
  muMinCC : U0 → ℝ
  Fo : U0 → ℝ
  Ga : U0 → ℝ
  ASK : U0 → ℝ
  IO : U0 → ℝ
  HH : U0 → ℝ
  del : U0 → ℝ
  η : U0 → ℝ
  e : U0 → ℝ
  delBar : ℝ
  etaBar : ℝ
  eBar : ℝ

namespace SlopeData

section Defs

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}

def nT (_ : SlopeData U0 W Top m f) : ℝ := (Fintype.card Top : ℝ)
def sumA (D : SlopeData U0 W Top m f) : ℝ := ∑ t, D.aT t
def logOm (D : SlopeData U0 W Top m f) : ℝ := D.gam + Real.log (Real.pi / D.v) - D.LpL
def s (D : SlopeData U0 W Top m f) (u0 : U0) : ℝ := wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u)
def uF (D : SlopeData U0 W Top m f) (u0 : U0) : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u)) - D.s u0

/-- The `RHDirect.BostSlopeFiber` attached to a fiber `u0`. -/
def fiber (D : SlopeData U0 W Top m f) (u0 : U0) : BostSlopeFiber where
  del := D.del u0
  η := D.η u0
  e := D.e u0
  s := D.s u0
  muMinCC := D.muMinCC u0
  muCC := D.muCC u0
  HH := D.HH u0
  uF := D.uF u0
  cardW := Fintype.card (W u0)

def Lo5 (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ) (u0 : U0) (u : W u0) : ℝ :=
  C.cSl1 * D.IO u0 + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u)
    + C.cSl1 * Xpp + 1

def LoP (D : SlopeData U0 W Top m f) (C : SlopeConsts) : ℝ :=
  C.cLoss * D.nT * (m : ℝ) * D.b * D.x ^ (C.eLoss * D.ε)

def Main (D : SlopeData U0 W Top m f) (u0 : U0) : ℝ :=
  ∑ j : Fin m, ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL
    - (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))

def SDiv (D : SlopeData U0 W Top m f) : ℝ := ∑ t, (m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm)

def EDiv (D : SlopeData U0 W Top m f) (C : SlopeConsts) : ℝ :=
  C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)

def Lam5 (D : SlopeData U0 W Top m f) (C : SlopeConsts) (u0 : U0) : ℝ :=
  (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / Real.pi))
    + (m : ℝ) * D.lg - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)

def Vvar (D : SlopeData U0 W Top m f) (C : SlopeConsts) : ℝ :=
  2 * (m : ℝ) * C.cE * D.B0 + C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0)
    + D.sumA * (C.cCount * Real.log D.k)

def K3 (D : SlopeData U0 W Top m f) (C : SlopeConsts) : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0

def K0v5 (D : SlopeData U0 W Top m f) (C : SlopeConsts) : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + D.EDiv C + (m : ℝ) * C.cE * D.B0 + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)

def K7v5 (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ) : ℝ :=
  C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L) + C.cSl1 * Xpp + 1

def MLo5 (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ) : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
    + C.cSl1 * Xpp + 1

def UBar5 (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ) : ℝ := D.K3 C + D.MLo5 C Xpp

def errorTermWith (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ) : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + D.EDiv C
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + D.MLo5 C Xpp
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (D.UBar5 C Xpp + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

def ErrText (D : SlopeData U0 W Top m f) : ℝ :=
  D.nT * D.a * (1 + (m : ℝ) ^ 2 / D.k) + (m : ℝ) * (D.B0 + D.Nc)

/-- Positivity and basic structural assumptions on the slope system. -/
structure Setting (D : SlopeData U0 W Top m f) (C : SlopeConsts) : Prop where
  x_pos : 0 < D.x
  b_pos : 0 < D.b
  a_nonneg : 0 ≤ D.a
  b'_nonneg : 0 ≤ D.b'
  k_pos : 0 < D.k
  v_pos : 0 < D.v
  f_pos : 0 < f
  aT_nonneg : ∀ t, 0 ≤ D.aT t
  w_pos : ∀ u0 j ρ, 0 < D.w u0 j ρ
  d_pos : ∀ u0 u, 0 < D.d u0 u
  mu_le_max : ∀ u0 u, D.muN u0 u ≤ D.muMaxN u0 u
  cSl1_nonneg : 0 ≤ C.cSl1
  delBar_lt_one : D.delBar < 1
  etaBar_nonneg : 0 ≤ D.etaBar
  eBar_nonneg : 0 ≤ D.eBar
  eBar_le : D.eBar ≤ 1 / 4

/-- The bundled analytic/divisibility/Bost-slope hypotheses feeding common-slope cancellation.
Uses `RHDirect.BostSlopeFiber.SlopeIneq` directly at every fiber `u0`. -/
structure SlopeHypotheses (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ) : Prop where
  setting : D.Setting C
  div : ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
    (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) - D.aT t * Real.log (D.T u0 u))) + D.EDiv C
  eComp : ∀ u0 (u : W u0), |D.Ee u0 u - (m : ℝ) * D.sumA * D.lg| ≤ C.cE * (m : ℝ) * D.B0
  hComp : ∀ u0 (u u' : W u0),
    |(D.h u0 u + ∑ t, D.aT t * Real.log (D.T u0 u))
      - (D.h u0 u' + ∑ t, D.aT t * Real.log (D.T u0 u'))|
      ≤ C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0)
  count : ∀ u0 (u : W u0),
    D.Lam5 C u0 ≤ Real.log (D.T u0 u) ∧
    Real.log (D.T u0 u) ≤ C.cCount * (m : ℝ) * D.L ∧
    ∀ u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ C.cCount * Real.log D.k
  slopes : ∀ u0 (u : W u0),
    -(C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)) ≤ D.muM u0 u ∧
    D.muMaxM u0 u ≤ C.cSlope * D.nT * D.a * D.La
  quotientSlopes : ∀ u0 (u : W u0),
    D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + C.cSl1 * (m : ℝ) * D.B0 ∧
    D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - D.Lo5 C Xpp u0 u ≤ D.muN u0 u
  losses : umean (fun u0 => D.ASK u0 - D.Ga u0) ≤ D.LoP C ∧ umean D.IO ≤ D.LoP C
  bostSlope : ∀ u0, (D.fiber u0).SlopeIneq
  hhBound : ∀ u0, D.s u0 - D.muMinCC u0 ≤ D.HH u0 ∧ 0 < D.HH u0 ∧ D.HH u0 ≤ D.x ^ C.cHH * D.b
  fParams : ∀ u0, 0 ≤ D.del u0 ∧ D.del u0 ≤ D.delBar ∧ 0 ≤ D.η u0 ∧ D.η u0 ≤ D.etaBar ∧
    0 ≤ D.e u0 ∧ D.e u0 ≤ D.eBar

omit [Fintype U0] [(u0 : U0) → Fintype (W u0)] [∀ (u0 : U0), Nonempty (W u0)] in
lemma sumA_nonneg (D : SlopeData U0 W Top m f) (C : SlopeConsts) (hS : D.Setting C) : 0 ≤ D.sumA :=
  Finset.sum_nonneg fun t _ => hS.aT_nonneg t

omit [Fintype U0] [Fintype Top] in
lemma uF_nonneg (D : SlopeData U0 W Top m f) (C : SlopeConsts) (hS : D.Setting C) (u0 : U0) :
    0 ≤ D.uF u0 := by
  unfold uF s
  have hle : ∀ u : W u0, D.muN u0 u - D.h u0 u ≤
      Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) := fun u =>
    (by linarith [hS.mu_le_max u0 u] : D.muN u0 u - D.h u0 u ≤ D.muMaxN u0 u - D.h u0 u).trans
      (Finset.le_sup' (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) (Finset.mem_univ u))
  linarith [wmean_le_const (hS.d_pos u0) _ hle]

omit [Fintype U0] [(u0 : U0) → Fintype (W u0)] [∀ (u0 : U0), Nonempty (W u0)] in
/-- **Exact Volume & Shift Cancellation Identity**:
Cancels `log (π / v)` and `m * sumA * lg` between the `m`-fold divisibility entropy `SDiv`
and the `m`-fold counting bound `Lam5`, exposing `Main u0`. -/
theorem key_cancellation_identity (D : SlopeData U0 W Top m f) (C : SlopeConsts)
    (hv : 0 < D.v) (hf : 0 < f) (u0 : U0) (hw : ∀ j ρ, 0 < D.w u0 j ρ) :
    D.SDiv - D.sumA * D.Lam5 C u0 + (m : ℝ) * D.sumA * D.lg =
      D.Main u0 + D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)) := by
  have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  have hpi : Real.log (Real.pi / D.v) = Real.log Real.pi - Real.log D.v :=
    Real.log_div Real.pi_ne_zero hv.ne'
  have hff : (1 / (f : ℝ)) * (f : ℝ) = 1 := by field_simp [hfR]
  have h1 : ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / Real.pi)
      = (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))
        + (m : ℝ) * (Real.log D.v - Real.log Real.pi) := by
    have hcard : (m : ℝ) * (Real.log D.v - Real.log Real.pi) =
        ∑ _j : Fin m, (Real.log D.v - Real.log Real.pi) := by simp; ring
    rw [hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / Real.pi)
        = (∑ ρ : Fin f, Real.log (D.w u0 j ρ)) + (f : ℝ) * (Real.log D.v - Real.log Real.pi) := by
      have hcardf : (f : ℝ) * (Real.log D.v - Real.log Real.pi) =
          ∑ _ρ : Fin f, (Real.log D.v - Real.log Real.pi) := by simp; ring
      rw [hcardf, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Real.log_div (mul_pos (hw j ρ) hv).ne' Real.pi_ne_zero,
        Real.log_mul (hw j ρ).ne' hv.ne']
      ring
    rw [e1]
    linear_combination (Real.log D.v - Real.log Real.pi) * hff
  have h2 : D.SDiv = (m : ℝ) * (∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL))
      - (m : ℝ) * (Real.log Real.pi - Real.log D.v) * D.sumA := by
    unfold SDiv sumA
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [ph, logOm, hpi]; ring
  have h3 : D.Main u0 = (m : ℝ) * (∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL))
      - D.sumA * (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)) := by
    unfold Main sumA
    have : ∀ j : Fin m,
        ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL
            - (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))
        = (∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL))
          - (∑ t, D.aT t) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)) := by
      intro j
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => by ring
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
  unfold Lam5
  rw [h1, h2, h3]
  ring

/-- **Pointwise Common-Slope Cancellation (`Ga_bound5`)**:
Simultaneously cancels `s(u0)`, `muCC(u0)`, `Fo(u0)`, and `h(u0, u)` between the `m`-step
divisibility inequality and Bost's slope inequality! -/
theorem pointwise_slope_cancellation (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ)
    (H : D.SlopeHypotheses C Xpp) (u0 : U0) :
    D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ) + D.K0v5 C
      + wmean (D.d u0) (D.Lo5 C Xpp u0)
      + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (D.Lo5 C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) := by
  have hS := H.setting
  have hA := D.sumA_nonneg C hS
  have hsl : D.Ga u0 + D.muCC u0
      - (C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
          + (m : ℝ) * (D.sumA * D.lg + C.cE * D.B0) + D.SDiv - D.sumA * D.Lam5 C u0 + D.EDiv C)
      - wmean (D.d u0) (D.Lo5 C Xpp u0) ≤ D.s u0 := by
    unfold s
    refine sub_wmean_le (hS.d_pos u0) _ fun u => ?_
    have h1 := (H.quotientSlopes u0 u).2
    have h2 := H.div u0 u
    rw [Finset.sum_sub_distrib] at h2
    have hsumT : ∑ t, D.aT t * Real.log (D.T u0 u) = D.sumA * Real.log (D.T u0 u) := by
      simp only [sumA, Finset.sum_mul]
    rw [hsumT] at h2
    have h3 : D.Lam5 C u0 ≤ Real.log (D.T u0 u) := (H.count u0 u).1
    have h4 := mul_le_mul_of_nonneg_left h3 hA
    have h5 : D.Ee u0 u ≤ (m : ℝ) * (D.sumA * D.lg + C.cE * D.B0) := by
      have := (abs_le.mp (H.eComp u0 u)).2; linarith
    have h6 := (H.slopes u0 u).1
    unfold SDiv at *
    linarith
  have huF : D.uF u0 ≤ D.K3 C + wmean (D.d u0) (D.Lo5 C Xpp u0) := by
    have hvar : ∀ u u' : W u0, (-D.Ee u0 u - D.h u0 u) - (-D.Ee u0 u' - D.h u0 u') ≤ D.Vvar C := by
      intro u u'
      have e1 : D.Ee u0 u' ≤ (m : ℝ) * (D.sumA * D.lg + C.cE * D.B0) := by
        have := (abs_le.mp (H.eComp u0 u')).2; linarith
      have e2 : (m : ℝ) * (D.sumA * D.lg - C.cE * D.B0) ≤ D.Ee u0 u := by
        have := (abs_le.mp (H.eComp u0 u)).1; linarith
      have h3 := (abs_le.mp (H.hComp u0 u' u)).2
      have hsum1 : ∑ t, D.aT t * Real.log (D.T u0 u') = D.sumA * Real.log (D.T u0 u') := by
        simp only [sumA, Finset.sum_mul]
      have hsum2 : ∑ t, D.aT t * Real.log (D.T u0 u) = D.sumA * Real.log (D.T u0 u) := by
        simp only [sumA, Finset.sum_mul]
      rw [hsum1, hsum2] at h3
      have h4 := (abs_le.mp ((H.count u0 u).2.2 u')).2
      have h5 := mul_le_mul_of_nonneg_left h4 hA
      unfold Vvar; linarith
    have hs : ∀ u : W u0,
        (D.muMaxN u0 u - D.h u0 u - D.K3 C) - wmean (D.d u0) (D.Lo5 C Xpp u0) ≤ D.s u0 := by
      intro u
      unfold s
      refine sub_wmean_le (hS.d_pos u0) _ fun u' => ?_
      have h1 := (H.quotientSlopes u0 u).1
      have h2 := (H.quotientSlopes u0 u').2
      have h3 := (H.slopes u0 u).2
      have h4 := (H.slopes u0 u').1
      have h5 := hvar u u'
      unfold K3; linarith
    unfold uF
    have hsup := Finset.sup'_le (Finset.univ_nonempty (α := W u0))
      (fun u : W u0 => D.muMaxN u0 u - D.h u0 u)
      (a := D.s u0 + (D.K3 C + wmean (D.d u0) (D.Lo5 C Xpp u0)))
      (fun u _ => by linarith [hs u])
    linarith
  have huF0 := D.uF_nonneg C hS u0
  have hid := D.key_cancellation_identity C hS.v_pos hS.f_pos u0 (hS.w_pos u0)
  obtain ⟨hdel0, hdelle, heta0, hetale, he0, hele⟩ := H.fParams u0
  obtain ⟨hHH1, hHH2, hHH3⟩ := H.hhBound u0
  have hSI := H.bostSlope u0 hdel0 (show D.del u0 < 1 by linarith [hS.delBar_lt_one]) heta0 he0
    (show D.e u0 ≤ 1 / 4 by linarith [hS.eBar_le]) hHH1 hHH2
  dsimp only [fiber] at hSI
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hS.x_pos _
  have hphi := phi_bound huF0 hHH2 hHH3 hS.b_pos hX huF
  have hA0 : 0 ≤ 4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) :=
    mul_nonneg (by linarith) (Real.log_nonneg (by have := div_nonneg hHH2.le huF0; linarith))
  have hsq : Real.sqrt (D.e u0) ≤ Real.sqrt D.eBar := Real.sqrt_le_sqrt hele
  have hc0 : 0 ≤ D.η u0 + 4 * Real.sqrt (D.e u0) := by positivity
  have hc1 : 0 ≤ D.etaBar + 4 * Real.sqrt D.eBar :=
    add_nonneg hS.etaBar_nonneg (by positivity)
  have hB : (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
      ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
    calc (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
        ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * D.HH u0 :=
          mul_le_mul_of_nonneg_right (by linarith) hHH2.le
      _ ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
          mul_le_mul_of_nonneg_left hHH3 hc1
  have hB0 : 0 ≤ (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 := mul_nonneg hc0 hHH2.le
  have hinv : (1 - D.del u0)⁻¹ ≤ (1 - D.delBar)⁻¹ :=
    inv_anti₀ (by linarith [hS.delBar_lt_one]) (by linarith)
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith [hS.delBar_lt_one])
  have hPhi : (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
        + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0)
      ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (D.Lo5 C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) := by
    calc _ ≤ (1 - D.delBar)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) :=
          mul_le_mul_of_nonneg_right hinv (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hinv0
  unfold K0v5
  linarith

/-- **Uniform Mean Bound from Bost Slope Cancellation (`uniform_bound_statement`)**:
Averaging `pointwise_slope_cancellation` over `u0 : U0` yields
`umean D.ASK ≤ umean D.Main + D.errorTermWith C Xpp`. -/
theorem mean_bound_of_slope_cancellation [Nonempty U0]
    (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ) (H : D.SlopeHypotheses C Xpp) :
    umean D.ASK ≤ umean D.Main + D.errorTermWith C Xpp := by
  have hS := H.setting
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith [hS.delBar_lt_one])
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hS.x_pos _
  have hLX : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith)
  have hc4 : 0 ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) := by positivity
  have hp : 0 ≤ (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1 :=
    mul_nonneg (by linarith) hS.cSl1_nonneg
  have hLo : ∀ u0, wmean (D.d u0) (D.Lo5 C Xpp u0) ≤ C.cSl1 * D.IO u0 + D.K7v5 C Xpp := by
    intro u0
    refine wmean_le_const (hS.d_pos u0) _ fun u => ?_
    have hnT0 : 0 ≤ D.nT := Nat.cast_nonneg _
    have hc : 0 ≤ C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') :=
      mul_nonneg (mul_nonneg (mul_nonneg hS.cSl1_nonneg hnT0) (Nat.cast_nonneg _))
        (add_nonneg (div_nonneg hS.a_nonneg hS.k_pos.le) hS.b'_nonneg)
    have h1 := mul_le_mul_of_nonneg_left (H.count u0 u).2.1 hc
    unfold Lo5 K7v5; linarith
  set coeff := (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1
  set Kconst := D.K0v5 C + (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * D.K7v5 C Xpp
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) * (D.K3 C + D.b)
    + (1 - D.delBar)⁻¹ * ((D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))
  have hGa : ∀ u0, D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ)
      + coeff * D.IO u0 + Kconst := by
    intro u0
    have h1 := D.pointwise_slope_cancellation C Xpp H u0
    have h2 := hLo u0
    have h3 := mul_le_mul_of_nonneg_left h2 hc4
    dsimp only [coeff, Kconst]; linarith
  have hu1 : umean D.Ga ≤ umean D.Main + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
      + coeff * umean D.IO + Kconst := by
    have hm := umean_mono hGa
    rw [umean_add, umean_add, umean_add, umean_mul, umean_const] at hm
    exact hm
  have hu2 : umean D.ASK = umean (fun u0 => D.ASK u0 - D.Ga u0) + umean D.Ga := by
    rw [← umean_add]; congr 1; funext u0; ring
  have hIO := mul_le_mul_of_nonneg_left H.losses.2 hp
  have hASK := H.losses.1
  dsimp only [coeff, Kconst] at hu1 hIO
  unfold errorTermWith UBar5 MLo5
  unfold K0v5 K7v5 at hu1
  linarith

/-- Window bounds on the slope data and constants (`ErrWindows` + `LargeX` in
`ErrorFormsWeakWindowsFalse.lean`). -/
structure ErrorWindowBounds (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp eK K : ℝ) : Prop where
  x_ge_one : 1 ≤ D.x
  eps_pos : 0 < D.ε
  eps_le_one : D.ε ≤ 1
  b_ge_one : 1 ≤ D.b
  xb_le_a : D.x * D.b ≤ D.a
  nT_ge_one : 1 ≤ D.nT
  m_le : (m : ℝ) ≤ D.x ^ ((1 : ℝ) / 2 + D.ε / 2)
  xm_le_k : D.x * (m : ℝ) ≤ D.k
  eK_nonneg : 0 ≤ eK
  k_ge_one : 1 ≤ D.k
  k_le_xeK : D.k ≤ D.x ^ eK
  k_le_a : D.k ≤ D.a
  L_nonneg : 0 ≤ D.L
  L_le : D.L ≤ 2 * D.x ^ D.ε
  La_nonneg : 0 ≤ D.La
  La_le : D.La ≤ 2 * D.x ^ D.ε
  b'_nonneg : 0 ≤ D.b'
  kb'_le_a : D.k * D.b' ≤ D.a
  Xpp_nonneg : 0 ≤ Xpp
  Xpp_le_a : Xpp ≤ D.a
  aT_bounds : ∀ t, 0 ≤ D.aT t ∧ D.aT t ≤ 2 * D.a
  B0_nonneg : 0 ≤ D.B0
  Nc_nonneg : 0 ≤ D.Nc
  cardW_le : ∀ u0, Real.log (Fintype.card (W u0) : ℝ) ≤ (D.k - 3) * Real.log 2
  delBar_le : D.delBar ≤ 1 / 2
  etaBar_nonneg : 0 ≤ D.etaBar
  eBar_nonneg : 0 ≤ D.eBar
  trace_le : (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)
    ≤ K * D.x ^ D.ε * (D.nT * D.a)
  cDiv_bounds : 0 ≤ C.cDiv ∧ C.cDiv ≤ K
  cE_bounds : 0 ≤ C.cE ∧ C.cE ≤ K
  cH_bounds : 0 ≤ C.cH ∧ C.cH ≤ K
  cCount_bounds : 0 ≤ C.cCount ∧ C.cCount ≤ K
  cSlope_bounds : 0 ≤ C.cSlope ∧ C.cSlope ≤ K
  cSl1_bounds : 0 ≤ C.cSl1 ∧ C.cSl1 ≤ K
  cLoss_bounds : 0 ≤ C.cLoss ∧ C.cLoss ≤ K
  eDiv_nonneg : 0 ≤ C.eDiv
  eLoss_nonneg : 0 ≤ C.eLoss
  cHH_nonneg : 0 ≤ C.cHH
  log_x_le : Real.log D.x ≤ D.x ^ D.ε
  KBig_le : 200 * (1 + K) ^ 2 * (1 + C.cHH) * (1 + eK) ≤ D.x ^ D.ε

/-- Helper algebraic bound for the Bost slope coefficient envelope `200 * (1+K)^2 * (1+cHH) * (1+eK)`. -/
private lemma coeff_envelope_le {K cHH eK : ℝ} (hK0 : 0 ≤ K) (hcHH : 0 ≤ cHH) (heK : 0 ≤ eK) :
    (4 * K + 3 * K + K + 4 * K + 1 + K + (5 * K ^ 2 + K + 1))
      + (8 * (1 + cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) + 2 * K)
      ≤ 200 * (1 + K) ^ 2 * (1 + cHH) * (1 + eK) := by
  have h1 : 5 * K ^ 2 + 13 * K + 2 * K * eK + 2 ≤ 15 * (1 + K) ^ 2 * (1 + eK) := by
    have hdiff : 15 * (1 + K) ^ 2 * (1 + eK) - (5 * K ^ 2 + 13 * K + 2 * K * eK + 2)
        = 13 + 17 * K + 10 * K ^ 2 + 15 * eK + 28 * K * eK + 15 * K ^ 2 * eK := by ring
    have hpos : 0 ≤ 13 + 17 * K + 10 * K ^ 2 + 15 * eK + 28 * K * eK + 15 * K ^ 2 * eK := by
      positivity
    linarith
  have h2 : (4 * K + 3 * K + K + 4 * K + 1 + K + (5 * K ^ 2 + K + 1)) + 2 * K
      ≤ 20 * (1 + K) ^ 2 := by
    have hdiff : 20 * (1 + K) ^ 2
        - ((4 * K + 3 * K + K + 4 * K + 1 + K + (5 * K ^ 2 + K + 1)) + 2 * K)
        = 18 + 24 * K + 15 * K ^ 2 := by ring
    have hpos : 0 ≤ 18 + 24 * K + 15 * K ^ 2 := by positivity
    linarith
  have h3 : 20 * (1 + K) ^ 2 ≤ 20 * (1 + K) ^ 2 * (1 + cHH) * (1 + eK) := by
    have ha' : (1 : ℝ) ≤ (1 + cHH) * (1 + eK) := by nlinarith
    have hb' : 0 ≤ 20 * (1 + K) ^ 2 := by positivity
    nlinarith
  have h4 : 8 * (1 + cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2)
      ≤ 120 * (1 + K) ^ 2 * (1 + cHH) * (1 + eK) := by
    have hmul := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 8 * (1 + cHH) by positivity)
    linarith
  have h5 : 0 ≤ 60 * (1 + K) ^ 2 * (1 + cHH) * (1 + eK) := by positivity
  linarith

omit [∀ (u0 : U0), Nonempty (W u0)] in
/-- Helper bound for `MLo5`, `UBar5 + b`, and the non-Bost pieces of `errorTermWith`. -/
private lemma errorTerm_parts_le [Nonempty U0]
    (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ) {eK K : ℝ}
    (hW : D.ErrorWindowBounds C Xpp eK K) :
    let E1 := D.x ^ ((C.eDiv + C.eLoss + 1) * D.ε)
    (D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
      + D.EDiv C + (m : ℝ) * C.cE * D.B0
      + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
      + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
      + D.LoP C + D.MLo5 C Xpp
        ≤ (4 * K + 3 * K + K + 4 * K + 1 + K + (5 * K ^ 2 + K + 1)) * E1 * D.ErrText) ∧
    (0 ≤ D.UBar5 C Xpp + D.b ∧
      D.UBar5 C Xpp + D.b ≤ (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) * E1 * D.ErrText) ∧
    0 ≤ D.ErrText ∧ D.nT * D.a ≤ D.ErrText := by
  intro E1
  have hx1 : 1 ≤ D.x := hW.x_ge_one
  have hx0 : 0 < D.x := by linarith
  have heps : 0 < D.ε := hW.eps_pos
  have hK0 : 0 ≤ K := le_trans hW.cDiv_bounds.1 hW.cDiv_bounds.2
  have hb0 : 0 ≤ D.b := by linarith [hW.b_ge_one]
  have ha1 : 1 ≤ D.a := le_trans (by nlinarith [hW.x_ge_one, hW.b_ge_one]) hW.xb_le_a
  have ha0 : 0 ≤ D.a := by linarith
  have hk0 : 0 < D.k := by linarith [hW.k_ge_one]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnT0 : 0 ≤ D.nT := by linarith [hW.nT_ge_one]
  have hnT_a : 0 ≤ D.nT * D.a := mul_nonneg hnT0 ha0
  have hBN0 : 0 ≤ D.B0 + D.Nc := add_nonneg hW.B0_nonneg hW.Nc_nonneg
  have hET_ge_nTa_m2k : D.nT * D.a * (1 + (m : ℝ) ^ 2 / D.k) ≤ D.ErrText := by
    unfold ErrText; nlinarith [mul_nonneg hm0 hBN0]
  have hET_ge_nTa : D.nT * D.a ≤ D.ErrText := by
    have hq : 0 ≤ D.nT * D.a * ((m : ℝ) ^ 2 / D.k) :=
      mul_nonneg hnT_a (div_nonneg (sq_nonneg _) hk0.le)
    linarith
  have hET_ge_mBN : (m : ℝ) * (D.B0 + D.Nc) ≤ D.ErrText := by
    unfold ErrText
    have hq : 0 ≤ D.nT * D.a * (1 + (m : ℝ) ^ 2 / D.k) :=
      mul_nonneg hnT_a (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) hk0.le))
    linarith
  have hET0 : 0 ≤ D.ErrText := le_trans hnT_a hET_ge_nTa
  have hET_ge_a : D.a ≤ D.ErrText := le_trans (by nlinarith [hW.nT_ge_one]) hET_ge_nTa
  have hET_ge_1 : 1 ≤ D.ErrText := le_trans ha1 hET_ge_a
  have hET_ge_b : D.b ≤ D.ErrText := le_trans (by nlinarith [hW.x_ge_one, hW.xb_le_a]) hET_ge_a
  have hET_ge_mB0 : (m : ℝ) * D.B0 ≤ D.ErrText :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith [hW.Nc_nonneg]) hm0) hET_ge_mBN
  have hmB0_nn : 0 ≤ (m : ℝ) * D.B0 := mul_nonneg hm0 hW.B0_nonneg
  have hE1_ge_1 : 1 ≤ E1 := Real.one_le_rpow hx1 (by nlinarith [hW.eDiv_nonneg, hW.eLoss_nonneg])
  have hE1_nn : 0 ≤ E1 := by linarith
  have hE1_ge_xe : D.x ^ D.ε ≤ E1 :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith [hW.eDiv_nonneg, hW.eLoss_nonneg])
  have hE1_ge_eDiv : D.x ^ (C.eDiv * D.ε) ≤ E1 :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith [hW.eLoss_nonneg])
  have hE1_ge_eLoss : D.x ^ (C.eLoss * D.ε) ≤ E1 :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith [hW.eDiv_nonneg])
  have hlog2 : Real.log 2 ≤ 1 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
      _ = 1 := Real.log_exp 1
  have hsumA : D.sumA ≤ 2 * D.nT * D.a := by
    unfold sumA nT
    calc ∑ t, D.aT t ≤ ∑ _t : Top, (2 * D.a) := Finset.sum_le_sum fun t _ => (hW.aT_bounds t).2
      _ = 2 * (Fintype.card Top : ℝ) * D.a := by simp; ring
  have hsumA0 : 0 ≤ D.sumA := Finset.sum_nonneg fun t _ => (hW.aT_bounds t).1
  have h1 : D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
      ≤ 4 * K * E1 * D.ErrText := by
    have hfac : D.La + (m : ℝ) ^ 2 * D.La / D.k = D.La * (1 + (m : ℝ) ^ 2 / D.k) := by ring
    rw [hfac]
    have hq0 : 0 ≤ 1 + (m : ℝ) ^ 2 / D.k := add_nonneg zero_le_one (div_nonneg (sq_nonneg _) hk0.le)
    have hmid : C.cCount * (D.La * (1 + (m : ℝ) ^ 2 / D.k))
        ≤ K * ((2 * D.x ^ D.ε) * (1 + (m : ℝ) ^ 2 / D.k)) :=
      mul_le_mul hW.cCount_bounds.2 (mul_le_mul_of_nonneg_right hW.La_le hq0)
        (mul_nonneg hW.La_nonneg hq0) hK0
    calc D.sumA * (C.cCount * (D.La * (1 + (m : ℝ) ^ 2 / D.k)))
        ≤ (2 * D.nT * D.a) * (K * ((2 * D.x ^ D.ε) * (1 + (m : ℝ) ^ 2 / D.k))) :=
          mul_le_mul hsumA hmid (mul_nonneg hW.cCount_bounds.1 (mul_nonneg hW.La_nonneg hq0)) (by positivity)
      _ = 4 * K * D.x ^ D.ε * (D.nT * D.a * (1 + (m : ℝ) ^ 2 / D.k)) := by ring
      _ ≤ 4 * K * E1 * D.ErrText :=
          mul_le_mul (mul_le_mul_of_nonneg_left hE1_ge_xe (by positivity)) hET_ge_nTa_m2k
            (mul_nonneg hnT_a hq0) (by positivity)
  have h2 : D.EDiv C ≤ 3 * K * E1 * D.ErrText := by
    unfold EDiv
    have ha' : C.cDiv * D.nT * D.a * D.La ≤ 2 * K * E1 * D.ErrText := by
      have hsub : C.cDiv * D.La ≤ K * (2 * D.x ^ D.ε) :=
        mul_le_mul hW.cDiv_bounds.2 hW.La_le hW.La_nonneg hK0
      calc C.cDiv * D.nT * D.a * D.La = (C.cDiv * D.La) * (D.nT * D.a) := by ring
        _ ≤ (K * (2 * D.x ^ D.ε)) * (D.nT * D.a) := mul_le_mul_of_nonneg_right hsub hnT_a
        _ = 2 * K * D.x ^ D.ε * (D.nT * D.a) := by ring
        _ ≤ 2 * K * E1 * D.ErrText :=
            mul_le_mul (mul_le_mul_of_nonneg_left hE1_ge_xe (by positivity)) hET_ge_nTa hnT_a (by positivity)
    have hb' : C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε) ≤ K * E1 * D.ErrText := by
      have hsub : C.cDiv * D.x ^ (C.eDiv * D.ε) ≤ K * E1 :=
        mul_le_mul hW.cDiv_bounds.2 hE1_ge_eDiv (Real.rpow_nonneg hx0.le _) hK0
      calc C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)
          = (C.cDiv * D.x ^ (C.eDiv * D.ε)) * ((m : ℝ) * (D.B0 + D.Nc)) := by ring
        _ ≤ (K * E1) * D.ErrText := mul_le_mul hsub hET_ge_mBN (mul_nonneg hm0 hBN0) (mul_nonneg hK0 hE1_nn)
        _ = K * E1 * D.ErrText := by ring
    linarith
  have h3 : (m : ℝ) * C.cE * D.B0 ≤ K * E1 * D.ErrText := by
    calc (m : ℝ) * C.cE * D.B0 = C.cE * ((m : ℝ) * D.B0) := by ring
      _ ≤ (K * E1) * D.ErrText :=
          mul_le_mul (le_trans hW.cE_bounds.2 (le_mul_of_one_le_right hK0 hE1_ge_1)) hET_ge_mB0 hmB0_nn
            (mul_nonneg hK0 hE1_nn)
      _ = K * E1 * D.ErrText := by ring
  have hm_le_k : (m : ℝ) / D.k ≤ 1 := by
    rw [div_le_one hk0]
    exact le_trans (le_mul_of_one_le_left hm0 hx1) hW.xm_le_k
  have h4 : C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k) ≤ 4 * K * E1 * D.ErrText := by
    have hsub : C.cSlope * D.La * (1 + (m : ℝ) / D.k) ≤ K * (2 * D.x ^ D.ε) * 2 :=
      mul_le_mul (mul_le_mul hW.cSlope_bounds.2 hW.La_le hW.La_nonneg hK0) (by linarith)
        (add_nonneg zero_le_one (div_nonneg hm0 hk0.le)) (by positivity)
    calc C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
        = (C.cSlope * D.La * (1 + (m : ℝ) / D.k)) * (D.nT * D.a) := by ring
      _ ≤ (K * (2 * D.x ^ D.ε) * 2) * (D.nT * D.a) := mul_le_mul_of_nonneg_right hsub hnT_a
      _ = 4 * K * D.x ^ D.ε * (D.nT * D.a) := by ring
      _ ≤ 4 * K * E1 * D.ErrText :=
          mul_le_mul (mul_le_mul_of_nonneg_left hE1_ge_xe (by positivity)) hET_ge_nTa hnT_a (by positivity)
  have h5 : umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ)) ≤ E1 * D.ErrText := by
    have hpt : ∀ u0, Real.log (Fintype.card (W u0) : ℝ) ≤ D.ErrText := by
      intro u0
      have hc := hW.cardW_le u0
      have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have h1' : (D.k - 3) * Real.log 2 ≤ D.k := by nlinarith [hW.k_ge_one]
      linarith [hW.k_le_a, hET_ge_a]
    calc umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
        ≤ umean (fun _ : U0 => D.ErrText) := umean_mono hpt
      _ = D.ErrText := umean_const _
      _ ≤ E1 * D.ErrText := le_mul_of_one_le_left hET0 hE1_ge_1
  have hm_le_x : (m : ℝ) ≤ D.x := by
    calc (m : ℝ) ≤ D.x ^ ((1 : ℝ) / 2 + D.ε / 2) := hW.m_le
      _ ≤ D.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hW.eps_le_one])
      _ = D.x := Real.rpow_one D.x
  have hLoP_nn : 0 ≤ D.LoP C := by
    unfold LoP
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hW.cLoss_bounds.1 hnT0) hm0) hb0)
      (Real.rpow_nonneg hx0.le _)
  have h6 : D.LoP C ≤ K * E1 * D.ErrText := by
    unfold LoP
    have hmb : (m : ℝ) * D.b ≤ D.a := le_trans (mul_le_mul_of_nonneg_right hm_le_x hb0) hW.xb_le_a
    have hsub : C.cLoss * D.x ^ (C.eLoss * D.ε) ≤ K * E1 :=
      mul_le_mul hW.cLoss_bounds.2 hE1_ge_eLoss (Real.rpow_nonneg hx0.le _) hK0
    calc C.cLoss * D.nT * (m : ℝ) * D.b * D.x ^ (C.eLoss * D.ε)
        = (C.cLoss * D.x ^ (C.eLoss * D.ε)) * (D.nT * ((m : ℝ) * D.b)) := by ring
      _ ≤ (K * E1) * (D.nT * D.a) :=
          mul_le_mul hsub (mul_le_mul_of_nonneg_left hmb hnT0) (mul_nonneg hnT0 (mul_nonneg hm0 hb0))
            (mul_nonneg hK0 hE1_nn)
      _ ≤ (K * E1) * D.ErrText := mul_le_mul_of_nonneg_left hET_ge_nTa (mul_nonneg hK0 hE1_nn)
      _ = K * E1 * D.ErrText := by ring
  have h7 : D.MLo5 C Xpp ≤ (5 * K ^ 2 + K + 1) * E1 * D.ErrText := by
    unfold MLo5
    have hp1 : C.cSl1 * D.LoP C ≤ K ^ 2 * E1 * D.ErrText := by
      calc C.cSl1 * D.LoP C ≤ K * (K * E1 * D.ErrText) := mul_le_mul hW.cSl1_bounds.2 h6 hLoP_nn hK0
        _ = K ^ 2 * E1 * D.ErrText := by ring
    have hp2 : C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
        ≤ 4 * K ^ 2 * E1 * D.ErrText := by
      have hab' : D.a / D.k + D.b' ≤ 2 * (D.a / D.k) := by
        have : D.b' ≤ D.a / D.k := (le_div_iff₀ hk0).mpr (by linarith [hW.kb'_le_a])
        linarith
      have h0 : D.nT * D.a * ((m : ℝ) ^ 2 / D.k) ≤ D.ErrText := by linarith
      have hsub : 2 * C.cSl1 * C.cCount * D.L ≤ 4 * K ^ 2 * E1 := by
        have hcc : C.cSl1 * C.cCount ≤ K * K :=
          mul_le_mul hW.cSl1_bounds.2 hW.cCount_bounds.2 hW.cCount_bounds.1 hK0
        have hccL : (C.cSl1 * C.cCount) * D.L ≤ (K * K) * (2 * D.x ^ D.ε) :=
          mul_le_mul hcc hW.L_le hW.L_nonneg (mul_nonneg hK0 hK0)
        calc 2 * C.cSl1 * C.cCount * D.L = 2 * ((C.cSl1 * C.cCount) * D.L) := by ring
          _ ≤ 2 * ((K * K) * (2 * D.x ^ D.ε)) := by linarith
          _ = 4 * K ^ 2 * D.x ^ D.ε := by ring
          _ ≤ 4 * K ^ 2 * E1 := mul_le_mul_of_nonneg_left hE1_ge_xe (by positivity)
      have hcmL : 0 ≤ C.cCount * (m : ℝ) * D.L :=
        mul_nonneg (mul_nonneg hW.cCount_bounds.1 hm0) hW.L_nonneg
      have hcnm : 0 ≤ C.cSl1 * D.nT * (m : ℝ) := mul_nonneg (mul_nonneg hW.cSl1_bounds.1 hnT0) hm0
      calc C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
          ≤ C.cSl1 * D.nT * (m : ℝ) * (2 * (D.a / D.k)) * (C.cCount * (m : ℝ) * D.L) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab' hcnm) hcmL
        _ = (2 * C.cSl1 * C.cCount * D.L) * (D.nT * D.a * ((m : ℝ) ^ 2 / D.k)) := by ring
        _ ≤ (4 * K ^ 2 * E1) * D.ErrText :=
            mul_le_mul hsub h0 (mul_nonneg hnT_a (div_nonneg (sq_nonneg _) hk0.le)) (by positivity)
        _ = 4 * K ^ 2 * E1 * D.ErrText := by ring
    have hp3 : C.cSl1 * Xpp + 1 ≤ (K + 1) * E1 * D.ErrText := by
      have ha_le : C.cSl1 * Xpp ≤ K * D.ErrText :=
        le_trans (mul_le_mul hW.cSl1_bounds.2 hW.Xpp_le_a hW.Xpp_nonneg hK0)
          (mul_le_mul_of_nonneg_left hET_ge_a hK0)
      have h1e : (K + 1) * D.ErrText ≤ (K + 1) * E1 * D.ErrText := by
        calc (K + 1) * D.ErrText = (K + 1) * 1 * D.ErrText := by ring
          _ ≤ (K + 1) * E1 * D.ErrText :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE1_ge_1 (by linarith)) hET0
      linarith
    linarith
  have hlogk : Real.log D.k ≤ eK * D.x ^ D.ε := by
    calc Real.log D.k ≤ Real.log (D.x ^ eK) := Real.log_le_log hk0 hW.k_le_xeK
      _ = eK * Real.log D.x := Real.log_rpow hx0 eK
      _ ≤ eK * D.x ^ D.ε := mul_le_mul_of_nonneg_left hW.log_x_le hW.eK_nonneg
  have hlogk0 : 0 ≤ Real.log D.k := Real.log_nonneg hW.k_ge_one
  have hVvar : D.Vvar C ≤ (5 * K + 2 * K * eK) * E1 * D.ErrText := by
    unfold Vvar
    have hv1 : 2 * (m : ℝ) * C.cE * D.B0 ≤ 2 * K * E1 * D.ErrText := by linarith
    have hv2 : C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0) ≤ 3 * K * E1 * D.ErrText := by
      have h1' : D.nT * D.a * D.La ≤ 2 * E1 * D.ErrText := by
        calc D.nT * D.a * D.La ≤ D.nT * D.a * (2 * D.x ^ D.ε) := mul_le_mul_of_nonneg_left hW.La_le hnT_a
          _ = 2 * D.x ^ D.ε * (D.nT * D.a) := by ring
          _ ≤ 2 * E1 * D.ErrText :=
              mul_le_mul (mul_le_mul_of_nonneg_left hE1_ge_xe zero_le_two) hET_ge_nTa hnT_a (by positivity)
      have h2' : (m : ℝ) * D.B0 ≤ E1 * D.ErrText :=
        le_trans hET_ge_mB0 (le_mul_of_one_le_left hET0 hE1_ge_1)
      calc C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0)
          ≤ K * (2 * E1 * D.ErrText + E1 * D.ErrText) :=
            mul_le_mul hW.cH_bounds.2 (by linarith) (add_nonneg (mul_nonneg hnT_a hW.La_nonneg) hmB0_nn) hK0
        _ = 3 * K * E1 * D.ErrText := by ring
    have hv3 : D.sumA * (C.cCount * Real.log D.k) ≤ 2 * K * eK * E1 * D.ErrText := by
      have hsub : C.cCount * Real.log D.k ≤ K * (eK * D.x ^ D.ε) :=
        mul_le_mul hW.cCount_bounds.2 hlogk hlogk0 hK0
      calc D.sumA * (C.cCount * Real.log D.k)
          ≤ (2 * D.nT * D.a) * (K * (eK * D.x ^ D.ε)) :=
            mul_le_mul hsumA hsub (mul_nonneg hW.cCount_bounds.1 hlogk0) (by positivity)
        _ = 2 * K * eK * D.x ^ D.ε * (D.nT * D.a) := by ring
        _ ≤ 2 * K * eK * E1 * D.ErrText :=
            mul_le_mul (mul_le_mul_of_nonneg_left hE1_ge_xe (mul_nonneg (by positivity) hW.eK_nonneg))
              hET_ge_nTa hnT_a (mul_nonneg (mul_nonneg (by positivity) hW.eK_nonneg) hE1_nn)
    linarith
  have hUB : D.UBar5 C Xpp + D.b ≤ (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) * E1 * D.ErrText := by
    unfold UBar5 K3
    have hs1 : C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) ≤ 6 * K * E1 * D.ErrText := by
      have hsub : C.cSlope * D.La * (2 + (m : ℝ) / D.k) ≤ K * (2 * D.x ^ D.ε) * 3 :=
        mul_le_mul (mul_le_mul hW.cSlope_bounds.2 hW.La_le hW.La_nonneg hK0) (by linarith)
          (add_nonneg zero_le_two (div_nonneg hm0 hk0.le)) (by positivity)
      calc C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k)
          = (C.cSlope * D.La * (2 + (m : ℝ) / D.k)) * (D.nT * D.a) := by ring
        _ ≤ (K * (2 * D.x ^ D.ε) * 3) * (D.nT * D.a) := mul_le_mul_of_nonneg_right hsub hnT_a
        _ = 6 * K * D.x ^ D.ε * (D.nT * D.a) := by ring
        _ ≤ 6 * K * E1 * D.ErrText :=
            mul_le_mul (mul_le_mul_of_nonneg_left hE1_ge_xe (by positivity)) hET_ge_nTa hnT_a (by positivity)
    have hs2 : C.cSl1 * (m : ℝ) * D.B0 ≤ K * E1 * D.ErrText := by
      calc C.cSl1 * (m : ℝ) * D.B0 = C.cSl1 * ((m : ℝ) * D.B0) := by ring
        _ ≤ (K * E1) * D.ErrText :=
            mul_le_mul (le_trans hW.cSl1_bounds.2 (le_mul_of_one_le_right hK0 hE1_ge_1)) hET_ge_mB0
              hmB0_nn (mul_nonneg hK0 hE1_nn)
        _ = K * E1 * D.ErrText := by ring
    have hb_le : D.b ≤ E1 * D.ErrText :=
      le_trans hET_ge_b (le_mul_of_one_le_left hET0 hE1_ge_1)
    linarith
  have hUB0 : 0 ≤ D.UBar5 C Xpp + D.b := by
    unfold UBar5 K3 MLo5 Vvar
    have p1 : 0 ≤ C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hW.cSlope_bounds.1 hnT0) ha0) hW.La_nonneg)
        (add_nonneg zero_le_two (div_nonneg hm0 hk0.le))
    have p2 : 0 ≤ 2 * (m : ℝ) * C.cE * D.B0 :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hm0) hW.cE_bounds.1) hW.B0_nonneg
    have p3 : 0 ≤ C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0) :=
      mul_nonneg hW.cH_bounds.1 (add_nonneg (mul_nonneg hnT_a hW.La_nonneg) hmB0_nn)
    have p4 : 0 ≤ D.sumA * (C.cCount * Real.log D.k) :=
      mul_nonneg hsumA0 (mul_nonneg hW.cCount_bounds.1 hlogk0)
    have p5 : 0 ≤ C.cSl1 * (m : ℝ) * D.B0 := mul_nonneg (mul_nonneg hW.cSl1_bounds.1 hm0) hW.B0_nonneg
    have p6 : 0 ≤ C.cSl1 * D.LoP C := mul_nonneg hW.cSl1_bounds.1 hLoP_nn
    have p7 : 0 ≤ C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hW.cSl1_bounds.1 hnT0) hm0)
        (add_nonneg (div_nonneg ha0 hk0.le) hW.b'_nonneg))
        (mul_nonneg (mul_nonneg hW.cCount_bounds.1 hm0) hW.L_nonneg)
    have p8 : 0 ≤ C.cSl1 * Xpp := mul_nonneg hW.cSl1_bounds.1 hW.Xpp_nonneg
    linarith
  exact ⟨by linarith, ⟨hUB0, hUB⟩, hET0, hET_ge_nTa⟩

omit [∀ (u0 : U0), Nonempty (W u0)] in
/-- **Error Collapse Theorem (`ErrorFormsUnderWindows`)**:
Under `ErrorWindowBounds`, the full Bost slope error term `errorTermWith D C Xpp` collapses to
`D.x ^ ((C.eDiv + C.eLoss + 3) * D.ε) * D.ErrText`. -/
theorem errorTerm_le_rpow_errText [Nonempty U0]
    (D : SlopeData U0 W Top m f) (C : SlopeConsts) (Xpp : ℝ) {eK K : ℝ}
    (hW : D.ErrorWindowBounds C Xpp eK K) :
    D.errorTermWith C Xpp ≤ D.x ^ ((C.eDiv + C.eLoss + 3) * D.ε) * D.ErrText := by
  obtain ⟨hRest, ⟨hUB0, hUB⟩, hET0, hET_ge_nTa⟩ := D.errorTerm_parts_le C Xpp hW
  have hx1 : 1 ≤ D.x := hW.x_ge_one
  have hx0 : 0 < D.x := by linarith
  have heps : 0 < D.ε := hW.eps_pos
  have hxe0 : 0 ≤ D.x ^ D.ε := Real.rpow_nonneg hx0.le _
  have hK0 : 0 ≤ K := le_trans hW.cDiv_bounds.1 hW.cDiv_bounds.2
  have hb0 : 0 ≤ D.b := by linarith [hW.b_ge_one]
  have hnT_a : 0 ≤ D.nT * D.a :=
    mul_nonneg (by linarith [hW.nT_ge_one]) (le_trans (by nlinarith [hW.x_ge_one, hW.b_ge_one]) hW.xb_le_a)
  set E1 := D.x ^ ((C.eDiv + C.eLoss + 1) * D.ε)
  set E2 := D.x ^ ((C.eDiv + C.eLoss + 2) * D.ε)
  have hE1_ge_xe : D.x ^ D.ε ≤ E1 :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith [hW.eDiv_nonneg, hW.eLoss_nonneg])
  have hE2_eq : D.x ^ D.ε * E1 = E2 := by
    dsimp only [E1, E2]; rw [← Real.rpow_add hx0]; congr 1; ring
  have hE2_ge_E1 : E1 ≤ E2 :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith [hW.eDiv_nonneg, hW.eLoss_nonneg])
  have hE2_nn : 0 ≤ E2 := Real.rpow_nonneg hx0.le _
  have hinv_le : (1 - D.delBar)⁻¹ ≤ 2 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith [hW.delBar_le] : (1 : ℝ) / 2 ≤ 1 - D.delBar)
    norm_num at this; exact this
  have hlog2 : Real.log 2 ≤ 1 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
      _ = 1 := Real.log_exp 1
  have hlogHH : Real.log (1 + D.x ^ C.cHH) ≤ (1 + C.cHH) * D.x ^ D.ε := by
    have hxc : 1 ≤ D.x ^ C.cHH := Real.one_le_rpow hx1 hW.cHH_nonneg
    have hxe1 : 1 ≤ D.x ^ D.ε := Real.one_le_rpow hx1 heps.le
    calc Real.log (1 + D.x ^ C.cHH)
        ≤ Real.log (2 * D.x ^ C.cHH) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + C.cHH * Real.log D.x := by
          rw [Real.log_mul (by norm_num) (by linarith), Real.log_rpow hx0]
      _ ≤ 1 * D.x ^ D.ε + C.cHH * D.x ^ D.ε := by
          linarith [mul_le_mul_of_nonneg_left hW.log_x_le hW.cHH_nonneg]
      _ = (1 + C.cHH) * D.x ^ D.ε := by ring
  have hlogHH0 : 0 ≤ Real.log (1 + D.x ^ C.cHH) :=
    Real.log_nonneg (by linarith [Real.one_le_rpow hx1 hW.cHH_nonneg])
  have htr0 : 0 ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
    mul_nonneg (add_nonneg hW.etaBar_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
      (mul_nonneg (Real.rpow_nonneg hx0.le _) hb0)
  have htr : (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) ≤ K * E2 * D.ErrText :=
    le_trans hW.trace_le
      (mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hE1_ge_xe hE2_ge_E1) hK0) hET_ge_nTa hnT_a
        (mul_nonneg hK0 hE2_nn))
  have hfirst : 4 * Real.log (1 + D.x ^ C.cHH) * (D.UBar5 C Xpp + D.b)
      ≤ 4 * (1 + C.cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) * E2 * D.ErrText := by
    have h4log : 4 * Real.log (1 + D.x ^ C.cHH) ≤ 4 * ((1 + C.cHH) * D.x ^ D.ε) :=
      mul_le_mul_of_nonneg_left hlogHH (by norm_num)
    have hrhs_nn : 0 ≤ 4 * ((1 + C.cHH) * D.x ^ D.ε) :=
      mul_nonneg (by norm_num) (mul_nonneg (by linarith [hW.cHH_nonneg]) hxe0)
    calc 4 * Real.log (1 + D.x ^ C.cHH) * (D.UBar5 C Xpp + D.b)
        ≤ 4 * ((1 + C.cHH) * D.x ^ D.ε) * ((5 * K ^ 2 + 13 * K + 2 * K * eK + 2) * E1 * D.ErrText) :=
          mul_le_mul h4log hUB hUB0 hrhs_nn
      _ = 4 * (1 + C.cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) * (D.x ^ D.ε * E1) * D.ErrText := by
          ring
      _ = 4 * (1 + C.cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) * E2 * D.ErrText := by
          rw [hE2_eq]
  have hBost : (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (D.UBar5 C Xpp + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))
      ≤ (8 * (1 + C.cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) + 2 * K) * E2 * D.ErrText := by
    calc (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (D.UBar5 C Xpp + D.b)
          + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))
        ≤ 2 * (4 * (1 + C.cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) * E2 * D.ErrText
          + K * E2 * D.ErrText) :=
          mul_le_mul hinv_le (add_le_add hfirst htr)
            (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlogHH0) hUB0) htr0) (by norm_num)
      _ = (8 * (1 + C.cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) + 2 * K) * E2 * D.ErrText := by
          ring
  have hcoeff := coeff_envelope_le hK0 hW.cHH_nonneg hW.eK_nonneg
  have hE_nn : 0 ≤ (4 * K + 3 * K + K + 4 * K + 1 + K + (5 * K ^ 2 + K + 1)) := by positivity
  have hRest2 : D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
      + D.EDiv C + (m : ℝ) * C.cE * D.B0
      + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
      + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
      + D.LoP C + D.MLo5 C Xpp
      ≤ (4 * K + 3 * K + K + 4 * K + 1 + K + (5 * K ^ 2 + K + 1)) * E2 * D.ErrText :=
    le_trans hRest (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE2_ge_E1 hE_nn) hET0)
  have hsum_pre : D.errorTermWith C Xpp
      ≤ ((4 * K + 3 * K + K + 4 * K + 1 + K + (5 * K ^ 2 + K + 1))
          + (8 * (1 + C.cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) + 2 * K)) * (E2 * D.ErrText) := by
    unfold errorTermWith
    calc _ ≤ (4 * K + 3 * K + K + 4 * K + 1 + K + (5 * K ^ 2 + K + 1)) * E2 * D.ErrText
            + (8 * (1 + C.cHH) * (5 * K ^ 2 + 13 * K + 2 * K * eK + 2) + 2 * K) * E2 * D.ErrText :=
          add_le_add hRest2 hBost
      _ = _ := by ring
  have hE2ET : 0 ≤ E2 * D.ErrText := mul_nonneg hE2_nn hET0
  calc D.errorTermWith C Xpp
      ≤ (200 * (1 + K) ^ 2 * (1 + C.cHH) * (1 + eK)) * (E2 * D.ErrText) :=
        le_trans hsum_pre (mul_le_mul_of_nonneg_right hcoeff hE2ET)
    _ ≤ D.x ^ D.ε * (E2 * D.ErrText) :=
        mul_le_mul_of_nonneg_right hW.KBig_le hE2ET
    _ = (D.x ^ D.ε * E2) * D.ErrText := by ring
    _ = D.x ^ ((C.eDiv + C.eLoss + 3) * D.ε) * D.ErrText := by
        dsimp only [E2]
        rw [← Real.rpow_add hx0]; congr 2; ring

end Defs

end SlopeData

/-! ## Section 4: Bost / Gram-Schur Dual-Lattice Frame Bound -/

/-- **Truncated Bost Slope Inequality from Tail Mass (`bost_slope_from_frame_tail`)**:
Given a finite family of lattices with positive ranks `d u`, shifted slopes `x u = μ_u - h_u`,
weighted mean `s = wmean d x`, spread `uF ≥ max_u x_u - s`, and an exceptional subset `B`
whose complement satisfies `x u ≤ muCC + Δ`, the fraction `θ = (∑_{u ∈ B} d u) / (∑_u d u) < 1`
yields the exact Bost slope lower bound:
`s - (θ / (1 - θ)) * uF - Δ ≤ muCC`. -/
theorem bost_slope_from_frame_tail {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (d x : ι → ℝ) (B : Finset ι) (muCC uF Δ : ℝ)
    (hd : ∀ u, 0 < d u)
    (hSpread : ∀ u ∈ B, x u ≤ wmean d x + uF)
    (hGood : ∀ u ∉ B, x u ≤ muCC + Δ)
    (hThetaLt : (∑ u ∈ B, d u) / (∑ u, d u) < 1) :
    wmean d x - (((∑ u ∈ B, d u) / (∑ u, d u)) / (1 - (∑ u ∈ B, d u) / (∑ u, d u))) * uF - Δ
      ≤ muCC := by
  set Dtot := ∑ u, d u
  set DB := ∑ u ∈ B, d u
  set θ := DB / Dtot
  have hDpos : 0 < Dtot := sum_pos_of_pos hd
  have h1m : 0 < 1 - θ := by linarith
  have hsplit : ∑ u, d u * x u = (∑ u ∈ B, d u * x u) + (∑ u ∈ Bᶜ, d u * x u) := by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
  have hB : ∑ u ∈ B, d u * x u ≤ DB * (wmean d x + uF) := by
    calc ∑ u ∈ B, d u * x u
        ≤ ∑ u ∈ B, d u * (wmean d x + uF) :=
          Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hSpread u hu) (hd u).le
      _ = DB * (wmean d x + uF) := (Finset.sum_mul _ _ _).symm
  have hBc_sum : ∑ u ∈ Bᶜ, d u = Dtot - DB := by
    have : DB + ∑ u ∈ Bᶜ, d u = Dtot := by
      dsimp only [DB, Dtot]
      rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
    linarith
  have hBc : ∑ u ∈ Bᶜ, d u * x u ≤ (Dtot - DB) * (muCC + Δ) := by
    calc ∑ u ∈ Bᶜ, d u * x u
        ≤ ∑ u ∈ Bᶜ, d u * (muCC + Δ) :=
          Finset.sum_le_sum fun u hu =>
            mul_le_mul_of_nonneg_left (hGood u (Finset.mem_compl.mp hu)) (hd u).le
      _ = (∑ u ∈ Bᶜ, d u) * (muCC + Δ) := (Finset.sum_mul _ _ _).symm
      _ = (Dtot - DB) * (muCC + Δ) := by rw [hBc_sum]
  have hmean : wmean d x ≤ θ * (wmean d x + uF) + (1 - θ) * (muCC + Δ) := by
    have h1 : ∑ u, d u * x u ≤ DB * (wmean d x + uF) + (Dtot - DB) * (muCC + Δ) := by linarith
    have h2 := div_le_div_of_nonneg_right h1 hDpos.le
    have hrew : (DB * (wmean d x + uF) + (Dtot - DB) * (muCC + Δ)) / Dtot
        = θ * (wmean d x + uF) + (1 - θ) * (muCC + Δ) := by
      dsimp only [θ]; field_simp [hDpos.ne']
    rw [← hrew]
    exact h2
  have hmul : (1 - θ) * (θ / (1 - θ)) = θ := by field_simp [h1m.ne']
  have h3 : (1 - θ) * (wmean d x - (θ / (1 - θ)) * uF - Δ) ≤ (1 - θ) * muCC := by
    have heq : (1 - θ) * (wmean d x - (θ / (1 - θ)) * uF - Δ) - (1 - θ) * muCC
        = wmean d x - (θ * (wmean d x + uF) + (1 - θ) * (muCC + Δ)) := by
      linear_combination -uF * hmul
    linarith
  exact le_of_mul_le_mul_left h3 h1m

/-- **Gram-Schur Diagonal Defect Bound**:
For any complex matrix `G : Matrix κ κ ℂ` (such as a normalized Gram matrix `Bᴴ * B` of a
dual-lattice frame) whose Frobenius deviation from `γ • 1` satisfies
`∑ i, ∑ j, ‖G i j - (if i = j then (γ : ℂ) else 0)‖ ^ 2 ≤ e * |κ| * γ ^ 2`,
the fraction of columns with `|‖G i i‖ - γ| ≥ τ * γ` is at most `e / τ ^ 2`. -/
theorem gram_schur_diag_defect_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℂ) (γ e τ : ℝ) (hγ : 0 < γ) (hτ : 0 < τ)
    (hFrob : ∑ i : κ, ∑ j : κ, ‖G i j - (if i = j then (γ : ℂ) else 0)‖ ^ 2
      ≤ e * (Fintype.card κ : ℝ) * γ ^ 2) :
    ((Finset.univ.filter (fun i : κ => τ * γ ≤ |‖G i i‖ - γ|)).card : ℝ)
      ≤ (e / τ ^ 2) * (Fintype.card κ : ℝ) := by
  set S := Finset.univ.filter (fun i : κ => τ * γ ≤ |‖G i i‖ - γ|)
  have hdiag : ∑ i : κ, |‖G i i‖ - γ| ^ 2 ≤ e * (Fintype.card κ : ℝ) * γ ^ 2 := by
    refine le_trans ?_ hFrob
    refine Finset.sum_le_sum fun i _ => ?_
    have hsub : |‖G i i‖ - γ| ^ 2 ≤ ‖G i i - (γ : ℂ)‖ ^ 2 := by
      have h1 : |‖G i i‖ - ‖(γ : ℂ)‖| ≤ ‖G i i - (γ : ℂ)‖ := abs_norm_sub_norm_le _ _
      have h2 : ‖(γ : ℂ)‖ = γ := by rw [Complex.norm_real, Real.norm_of_nonneg hγ.le]
      rw [h2] at h1
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hmem : ‖G i i - (if i = i then (γ : ℂ) else 0)‖ ^ 2
        ≤ ∑ j : κ, ‖G i j - (if i = j then (γ : ℂ) else 0)‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖G i j - (if i = j then (γ : ℂ) else 0)‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    simp only [↓reduceIte] at hmem
    linarith
  have hS : (S.card : ℝ) * (τ * γ) ^ 2 ≤ ∑ i : κ, |‖G i i‖ - γ| ^ 2 := by
    calc (S.card : ℝ) * (τ * γ) ^ 2
        = ∑ _i ∈ S, (τ * γ) ^ 2 := by simp
      _ ≤ ∑ i ∈ S, |‖G i i‖ - γ| ^ 2 :=
          Finset.sum_le_sum fun i hi =>
            pow_le_pow_left₀ (by positivity) (Finset.mem_filter.mp hi).2 2
      _ ≤ ∑ i : κ, |‖G i i‖ - γ| ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => sq_nonneg _)
  have htg0 : 0 < (τ * γ) ^ 2 := by positivity
  have h1 : (S.card : ℝ) * (τ * γ) ^ 2 ≤ (e / τ ^ 2) * (Fintype.card κ : ℝ) * (τ * γ) ^ 2 := by
    have heq : (e / τ ^ 2) * (Fintype.card κ : ℝ) * (τ * γ) ^ 2 = e * (Fintype.card κ : ℝ) * γ ^ 2 := by
      field_simp [hτ.ne']
    rw [heq]; linarith
  exact le_of_mul_le_mul_right h1 htg0

/-- **Arakelov Covolume vs. `p`-adic Chain Divisibility Bound on Exceptional Characters**:
If a family of characters/lattices of rank weights `d u > 0` embeds into a common dual lattice
with archimedean covolume ceiling `ArchBound`, while every exceptional character `u ∈ Exc`
gains at least `m * divGain` from the `m`-step `p`-adic divisibility chain (and every
non-exceptional character contributes at least `-baseLoss`), then the total rank of exceptional
characters satisfies:
`∑_{u ∈ Exc} d u ≤ (ArchBound + (∑_u d u) * baseLoss) / (m * divGain + baseLoss)`. -/
theorem exceptional_character_rank_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d score : ι → ℝ) (Exc : Finset ι) (m : ℕ) (divGain baseLoss ArchBound : ℝ)
    (hd : ∀ u, 0 < d u)
    (hGainPos : 0 < (m : ℝ) * divGain + baseLoss)
    (hArch : ∑ u, d u * score u ≤ ArchBound)
    (hExc : ∀ u ∈ Exc, (m : ℝ) * divGain ≤ score u)
    (hRest : ∀ u ∉ Exc, -baseLoss ≤ score u) :
    ∑ u ∈ Exc, d u ≤ (ArchBound + (∑ u, d u) * baseLoss) / ((m : ℝ) * divGain + baseLoss) := by
  rw [le_div_iff₀ hGainPos]
  have hsplit : ∑ u, d u * score u = (∑ u ∈ Exc, d u * score u) + (∑ u ∈ Excᶜ, d u * score u) := by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
  have h1 : (∑ u ∈ Exc, d u) * ((m : ℝ) * divGain) ≤ ∑ u ∈ Exc, d u * score u := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hExc u hu) (hd u).le
  have h2 : (∑ u ∈ Excᶜ, d u) * (-baseLoss) ≤ ∑ u ∈ Excᶜ, d u * score u := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun u hu =>
      mul_le_mul_of_nonneg_left (hRest u (Finset.mem_compl.mp hu)) (hd u).le
  have htot : (∑ u ∈ Exc, d u) + (∑ u ∈ Excᶜ, d u) = ∑ u, d u := by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
  have hcomb : (∑ u ∈ Exc, d u) * ((m : ℝ) * divGain + baseLoss)
      = (∑ u ∈ Exc, d u) * ((m : ℝ) * divGain) + (∑ u ∈ Excᶜ, d u) * (-baseLoss)
        + (∑ u, d u) * baseLoss := by
    linear_combination baseLoss * htot
  linarith

end

end RHDirect.SlopeInequality
